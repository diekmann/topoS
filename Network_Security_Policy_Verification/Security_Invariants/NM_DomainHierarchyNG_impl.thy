theory NM_DomainHierarchyNG_impl
imports NM_DomainHierarchyNG "../NetworkModel_Lists_Impl_Interface"
begin


code_identifier code_module NM_DomainHierarchyNG_impl => (Scala) NM_DomainHierarchyNG

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (s, r) \<in> set (edgesL G). (nP r) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s))"


fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> set (nodesL G). 
    case (nP v) of Unassigned \<Rightarrow> True | DN (level, trust) \<Rightarrow> valid_hierarchy_pos tree level
   )"




definition DomainHierarchyNG_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> ('v \<times> 'v) list list" where
  "DomainHierarchyNG_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (s,r) \<Rightarrow> \<not> (nP r) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s) ] ])"



lemma "DomainHierarchyNG.node_props P = 
  (\<lambda>i. case node_properties P i of None \<Rightarrow> NM_DomainHierarchyNG.default_node_properties | Some property \<Rightarrow> property)"
by(fact NetworkModel.node_props.simps[OF NetworkModel_DomainHierarchyNG, of "P"])

definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_DomainHierarchyNG.default_node_properties))"
(*lemma[code_unfold]: "NetworkModel.node_props NM_DomainHierarchy.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done*)

(*TODO does this work?*)
lemma[code_unfold]: "DomainHierarchyNG.node_props P = NetModel_node_props P"
by(simp add: NetModel_node_props_def)

definition "DomainHierarchyNG_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_DomainHierarchyNG.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_DomainHierarchyNG.default_node_properties P))"


interpretation DomainHierarchyNG_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_DomainHierarchyNG.default_node_properties
  and eval_model_spec=NM_DomainHierarchyNG.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_DomainHierarchyNG.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_DomainHierarchyNG.target_focus
  and offending_flows_impl=DomainHierarchyNG_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=DomainHierarchyNG_eval
 apply(unfold NetworkModel_List_Impl_def)
 apply(rule conjI)
  apply(simp add: NetworkModel_DomainHierarchyNG list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def DomainHierarchyNG_offending_set DomainHierarchyNG_offending_set_def DomainHierarchyNG_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis DomainHierarchyNG.node_props.simps DomainHierarchyNG.node_props_eq_node_props_formaldef)
 apply(simp only: DomainHierarchyNG_eval_def)
 apply(intro allI)
 apply(rule NetworkModel_eval_impl_proofrule[OF NetworkModel_DomainHierarchyNG])
 apply(simp_all add: list_graph_to_graph_def)
done


section {* DomainHierarchyNG packing *}
  definition NM_LIB_DomainHierarchyNG :: "('v::vertex, domainNameTrust, domainTree) NetworkModel_packed" where
    "NM_LIB_DomainHierarchyNG \<equiv> 
    \<lparr> nm_name = ''DomainHierarchyNG'', 
      nm_target_focus = NM_DomainHierarchyNG.target_focus,
      nm_default = NM_DomainHierarchyNG.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = DomainHierarchyNG_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = DomainHierarchyNG_eval
      \<rparr>"
  interpretation NM_LIB_DomainHierarchyNG_interpretation: NetworkModel_modelLibrary NM_LIB_DomainHierarchyNG 
      NM_DomainHierarchyNG.eval_model NM_DomainHierarchyNG.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_DomainHierarchyNG_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)






text {*Examples:*}
definition example_TUM_net :: "vString list_graph" where
  "example_TUM_net \<equiv> \<lparr> nodesL=[NetworkModel_Vertices.V ''Gateway'', NetworkModel_Vertices.V ''LowerSVR'', NetworkModel_Vertices.V ''UpperSRV''], 
        edgesL=[
          (NetworkModel_Vertices.V ''Gateway'',NetworkModel_Vertices.V ''LowerSVR''), (NetworkModel_Vertices.V ''Gateway'',NetworkModel_Vertices.V ''UpperSRV''), 
          (NetworkModel_Vertices.V ''LowerSVR'', NetworkModel_Vertices.V ''Gateway''),
          (NetworkModel_Vertices.V ''UpperSRV'', NetworkModel_Vertices.V ''Gateway'')
        ] \<rparr>"
value[code] "valid_list_graph example_TUM_net"

definition example_TUM_config :: "vString \<Rightarrow> domainNameTrust" where
  "example_TUM_config \<equiv> ((\<lambda> e. default_node_properties)
        (NetworkModel_Vertices.V ''Gateway'':= DN (''ACD''--''AISD''--Leaf, 1),
         NetworkModel_Vertices.V ''LowerSVR'':= DN (''ACD''--''AISD''--Leaf, 0),
         NetworkModel_Vertices.V ''UpperSRV'':= DN (''ACD''--Leaf, 0)
       ))"

definition example_TUM_hierarchy :: "domainTree" where
"example_TUM_hierarchy \<equiv> (Department ''ACD'' [
           Department ''AISD'' []
       ])"

value[code] "verify_globals example_TUM_net example_TUM_config example_TUM_hierarchy"
value[code] "eval_model     example_TUM_net example_TUM_config"

definition example_TUM_net_invalid where
"example_TUM_net_invalid \<equiv> example_TUM_net\<lparr>edgesL :=  
    (NetworkModel_Vertices.V ''LowerSRV'', NetworkModel_Vertices.V ''UpperSRV'')#(edgesL example_TUM_net)\<rparr>"

value[code] "verify_globals example_TUM_net_invalid example_TUM_config example_TUM_hierarchy"
value[code] "eval_model     example_TUM_net_invalid example_TUM_config"
value[code] "DomainHierarchyNG_offending_list example_TUM_net_invalid example_TUM_config"


hide_const (open) NetModel_node_props

hide_const (open) eval_model verify_globals 

end
