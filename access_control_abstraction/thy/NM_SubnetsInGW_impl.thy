theory NM_SubnetsInGW_impl
imports NM_SubnetsInGW NetworkModel_Lists_Impl_Interface
begin

code_identifier code_module NM_SubnetsInGW_impl => (Scala) NM_SubnetsInGW

section {* NetworkModel SubnetsInGw List Implementation *}

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). NM_SubnetsInGW.allowed_subnet_flow (nP e1) (nP e2))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition SubnetsInGW_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) list list" where
  "SubnetsInGW_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_SubnetsInGW.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_SubnetsInGW.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "SubnetsInGW_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_SubnetsInGW.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_SubnetsInGW.default_node_properties P))"


interpretation SubnetsInGW_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_SubnetsInGW.default_node_properties
  and eval_model_spec=NM_SubnetsInGW.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_SubnetsInGW.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_SubnetsInGW.target_focus
  and offending_flows_impl=SubnetsInGW_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=SubnetsInGW_eval
apply(unfold_locales)
 apply(simp add: list_graph_to_graph_def)
 apply(simp add: list_graph_to_graph_def)
 apply(simp add: list_graph_to_graph_def SubnetsInGW_offending_set SubnetsInGW_offending_set_def SubnetsInGW_offending_list_def)
apply(simp only: NetModel_node_props_def)
 apply(metis SubnetsInGW.node_props.simps SubnetsInGW.node_props_eq_node_props_formaldef)
apply(simp only: SubnetsInGW_eval_def)
apply(rule_tac target_focus=NM_SubnetsInGW.target_focus in NetworkModel_eval_impl_proofrule)
 apply(unfold_locales) (*instance*)
apply(simp_all add: list_graph_to_graph_def)
done



section {* SubnetsInGW packing *}
  definition NM_LIB_SubnetsInGW :: "('v::vertex, subnets, unit) NetworkModel_packed" where
    "NM_LIB_SubnetsInGW \<equiv> 
    \<lparr> nm_name = ''SubnetsInGW'', 
      nm_target_focus = NM_SubnetsInGW.target_focus,
      nm_default = NM_SubnetsInGW.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = SubnetsInGW_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = SubnetsInGW_eval
      \<rparr>"
  interpretation NM_LIB_SubnetsInGW_interpretation: NetworkModel_modelLibrary NM_LIB_SubnetsInGW
      NM_SubnetsInGW.eval_model NM_SubnetsInGW.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_SubnetsInGW_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text {* Examples*}

definition example_net_sub :: "nat list_graph" where
"example_net_sub \<equiv> \<lparr> nodesL = [1::nat,2,3,4, 8, 11,12,42], 
  edgesL = [(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1),(3,2),(3,4),(4,1),(4,2),(4,3), 
  (8,1),(8,2),
  (8,11),
  (11,8), (12,8),
  (11,42), (12,42), (8,42)] \<rparr>"
value[code] "valid_list_graph example_net_sub"

definition example_conf_sub where
"example_conf_sub \<equiv> ((\<lambda>e. NM_SubnetsInGW.default_node_properties)
  (1 := Member, 2:= Member, 3:= Member, 4:=Member,
   8:=InboundGateway))" 

value[code] "eval_model example_net_sub example_conf_sub"


definition example_net_sub_invalid where
"example_net_sub_invalid \<equiv> example_net_sub\<lparr>edgesL := (42,4)#(edgesL example_net_sub)\<rparr>"

value[code] "eval_model example_net_sub_invalid example_conf_sub"
value[code] "SubnetsInGW_offending_list example_net_sub_invalid example_conf_sub"



hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
