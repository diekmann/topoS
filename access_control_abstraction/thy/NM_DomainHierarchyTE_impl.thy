theory NM_DomainHierarchyTE_impl
imports NM_DomainHierarchyTE NetworkModel_Lists_Impl_Interface FiniteListGraph_Impl
begin

end (*DEPRECATED use NM_DomainHierarchyNG*)

code_identifier code_module NM_DomainHierarchyTE_impl => (Scala) NM_DomainHierarchyTE

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). let c1=(nP e1) in 
    (level (nP e2)) \<le> domainNameChop (level c1) (trust c1))"

text {* Assigning unassigned a trust level is syntactically invalid, thus, case can be ignored *}
fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> set (nodesL G). 
    valid_hierarchy_pos tree (level (nP v)) \<and> 
    (level (nP v) = Unassigned \<longrightarrow> trust (nP v) = 0)
   )"




definition DomainHierarchyTE_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "DomainHierarchyTE_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> let c1=(nP e1) in 
    \<not> (level (nP e2)) \<le> domainNameChop (level c1) (trust c1)] ])"



lemma "DomainHierarchyTE.node_props P = 
  (\<lambda>i. case node_properties P i of None \<Rightarrow> NM_DomainHierarchyTE.default_node_properties | Some property \<Rightarrow> property)"
by(fact NetworkModel.node_props.simps[OF DomainHierarchyTE_NetworkModel, of "P"])

definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_DomainHierarchyTE.default_node_properties))"
(*lemma[code_unfold]: "NetworkModel.node_props NM_DomainHierarchy.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done*)

(*TODO does this work?*)
lemma[code_unfold]: "DomainHierarchyTE.node_props P = NetModel_node_props P"
by(simp add: NetModel_node_props_def)

definition "DomainHierarchyTE_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_DomainHierarchyTE.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_DomainHierarchyTE.default_node_properties P))"


interpretation DomainHierarchyTE_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_DomainHierarchyTE.default_node_properties
  and eval_model_spec=NM_DomainHierarchyTE.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_DomainHierarchyTE.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_DomainHierarchyTE.target_focus
  and offending_flows_impl=DomainHierarchyTE_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=DomainHierarchyTE_eval
apply(unfold_locales)
     apply(simp add: list_graph_to_graph_def)
    apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def DomainHierarchyTE_offending_set DomainHierarchyTE_offending_set_def DomainHierarchyTE_offending_list_def)
  apply(simp only: NetModel_node_props_def)
 apply(metis DomainHierarchyTE.node_props.simps DomainHierarchyTE.node_props_eq_node_props_formaldef)
apply(simp only: DomainHierarchyTE_eval_def)
apply(rule_tac target_focus=NM_DomainHierarchyTE.target_focus in NetworkModel_eval_impl_proofrule)
   apply(unfold_locales) (*instance *)
apply(simp_all add: list_graph_to_graph_def)
done



section {* DomainHierarchyTE packing *}
  definition NM_LIB_DomainHierarchyTE :: "('v::vertex, node_config, domainTree) NetworkModel_packed" where
    "NM_LIB_DomainHierarchyTE \<equiv> 
    \<lparr> nm_name = ''DomainHierarchyTE'', 
      nm_target_focus = NM_DomainHierarchyTE.target_focus,
      nm_default = NM_DomainHierarchyTE.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = DomainHierarchyTE_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = DomainHierarchyTE_eval
      \<rparr>"
  interpretation NM_LIB_DomainHierarchyTE_interpretation: NetworkModel_modelLibrary NM_LIB_DomainHierarchyTE 
      NM_DomainHierarchyTE.eval_model NM_DomainHierarchyTE.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_DomainHierarchyTE_def)
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

definition example_TUM_config :: "vString \<Rightarrow> node_config" where
  "example_TUM_config \<equiv> ((\<lambda> e. default_node_properties)
        (NetworkModel_Vertices.V ''Gateway'':= \<lparr> level = ''ACD''--''AISD''--Leaf, trust = 1 \<rparr>,
         NetworkModel_Vertices.V ''LowerSVR'':= \<lparr> level = ''ACD''--''AISD''--Leaf, trust = 0 \<rparr>,
         NetworkModel_Vertices.V ''UpperSRV'':= \<lparr> level = ''ACD''--Leaf, trust = 0 \<rparr>
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
value[code] "DomainHierarchyTE_offending_list example_TUM_net_invalid example_TUM_config"


hide_const (open) NetModel_node_props

hide_const (open) eval_model verify_globals 

end
