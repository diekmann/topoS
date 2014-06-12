theory NM_CommunicationPartners_impl
imports NM_CommunicationPartners NetworkModel_Lists_Impl_Interface
begin

code_identifier code_module NM_CommunicationPartners_impl => (Scala) NM_CommunicationPartners


section {* NetworkModel CommunicationPartners List Implementation *}


fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (s,r) \<in> set (edgesL G). s \<noteq> r \<longrightarrow> NM_CommunicationPartners.allowed_flow (nP s) s (nP r) r)"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"



definition CommunicationPartners_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "CommunicationPartners_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_flow (nP e1) e1 (nP e2) e2] ])"


thm NM_CommunicationPartners.CommunicationPartners.node_props.simps
definition "NetModel_node_props (P::('v::vertex, 'v node_config, 'b) NetworkModel_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_CommunicationPartners.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_CommunicationPartners.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "CommunicationPartners_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_CommunicationPartners.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_CommunicationPartners.default_node_properties P))"


interpretation CommunicationPartners_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_CommunicationPartners.default_node_properties
  and eval_model_spec=NM_CommunicationPartners.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_CommunicationPartners.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_CommunicationPartners.target_focus
  and offending_flows_impl=CommunicationPartners_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=CommunicationPartners_eval
apply(unfold_locales)
 apply(simp add: list_graph_to_graph_def)
 apply(simp add: list_graph_to_graph_def)
 apply(simp add: list_graph_to_graph_def CommunicationPartners_offending_set CommunicationPartners_offending_set_def CommunicationPartners_offending_list_def)
apply(simp only: NetModel_node_props_def)
 apply(metis CommunicationPartners.node_props.simps CommunicationPartners.node_props_eq_node_props_formaldef)
apply(simp only: CommunicationPartners_eval_def)
apply(rule_tac target_focus=NM_CommunicationPartners.target_focus in NetworkModel_eval_impl_proofrule)
 apply(unfold_locales) (*instance*)
apply(simp_all add: list_graph_to_graph_def)
done


section {* CommunicationPartners packing *}
  definition NM_LIB_CommunicationPartners :: "('v::vertex, 'v NM_CommunicationPartners.node_config, unit) NetworkModel_packed" where
    "NM_LIB_CommunicationPartners \<equiv> 
    \<lparr> nm_name = ''CommunicationPartners'', 
      nm_target_focus = NM_CommunicationPartners.target_focus,
      nm_default = NM_CommunicationPartners.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = CommunicationPartners_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = CommunicationPartners_eval
      \<rparr>"
  interpretation NM_LIB_CommunicationPartners_interpretation: NetworkModel_modelLibrary NM_LIB_CommunicationPartners
      NM_CommunicationPartners.eval_model NM_CommunicationPartners.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_CommunicationPartners_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {* Examples*}



hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
