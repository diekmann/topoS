theory NM_ACLnotCommunicateWith_impl
imports NM_ACLnotCommunicateWith "../TopoS_Lists_Impl_Interface"
begin

code_identifier code_module NM_ACLnotCommunicateWith_impl => (Scala) NM_ACLnotCommunicateWith


section {* NetworkModel ACLnotCommunicateWith List Implementation *}


fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v set) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> v \<in> set (nodesL G). \<forall> a \<in> set (succ_tran G v). a \<notin> (nP v))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v set) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition "NetModel_node_props (P::('v::vertex, 'v set, 'b) TopoS_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_ACLnotCommunicateWith.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_ACLnotCommunicateWith.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "ACLnotCommunicateWith_offending_list = Generic_offending_list sinvar"

definition "ACLnotCommunicateWith_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_ACLnotCommunicateWith.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (NetworkModel.node_props NM_ACLnotCommunicateWith.default_node_properties P))"


lemma sinvar_correct: "valid_list_graph G \<Longrightarrow> NM_ACLnotCommunicateWith.sinvar (list_graph_to_graph G) nP = sinvar G nP"
by (metis NM_ACLnotCommunicateWith.sinvar.simps NM_ACLnotCommunicateWith_impl.sinvar.simps graph.select_convs(1) list_graph_to_graph_def succ_tran_correct)


interpretation ACLnotCommunicateWith_impl:TopoS_List_Impl 
  where default_node_properties=NM_ACLnotCommunicateWith.default_node_properties
  and sinvar_spec=NM_ACLnotCommunicateWith.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=NM_ACLnotCommunicateWith.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_ACLnotCommunicateWith.target_focus
  and offending_flows_impl=ACLnotCommunicateWith_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=ACLnotCommunicateWith_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_ACLnotCommunicateWith)
  apply(rule conjI)
   apply(intro allI impI)
   apply(fact sinvar_correct)
  apply(simp)
 apply(rule conjI)
  apply(unfold ACLnotCommunicateWith_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(intro allI impI)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis ACLnotCommunicateWith.node_props.simps ACLnotCommunicateWith.node_props_eq_node_props_formaldef)
 apply(simp only: ACLnotCommunicateWith_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_ACLnotCommunicateWith])
  apply(simp only: sinvar_correct)
 apply(simp)
done

section {* packing *}
  definition NM_LIB_ACLnotCommunicateWith:: "('v::vertex, 'v set, unit) TopoS_packed" where
    "NM_LIB_ACLnotCommunicateWith \<equiv> 
    \<lparr> nm_name = ''ACLnotCommunicateWith'', 
      nm_target_focus = NM_ACLnotCommunicateWith.target_focus,
      nm_default = NM_ACLnotCommunicateWith.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = ACLnotCommunicateWith_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = ACLnotCommunicateWith_eval
      \<rparr>"
  interpretation NM_LIB_ACLnotCommunicateWith_interpretation: TopoS_modelLibrary NM_LIB_ACLnotCommunicateWith
      NM_ACLnotCommunicateWith.sinvar NM_ACLnotCommunicateWith.verify_globals
    apply(unfold TopoS_modelLibrary_def NM_LIB_ACLnotCommunicateWith_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {* Examples*}



hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
