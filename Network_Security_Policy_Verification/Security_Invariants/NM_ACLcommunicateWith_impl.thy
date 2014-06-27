theory NM_ACLcommunicateWith_impl
imports NM_ACLcommunicateWith "../TopoS_Lists_Impl_Interface"
begin

code_identifier code_module NM_ACLcommunicateWith_impl => (Scala) NM_ACLcommunicateWith


section {* List Implementation *}

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v access_list) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> v \<in> set (nodesL G). accesses_okay (nP v) (set (succ_tran G v)))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v access_list) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition "NetModel_node_props (P::('v::vertex, 'v access_list, 'b) TopoS_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_ACLcommunicateWith.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_ACLcommunicateWith.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "ACLcommunicateWith_offending_list = Generic_offending_list eval_model"

definition "ACLcommunicateWith_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_ACLcommunicateWith.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_ACLcommunicateWith.default_node_properties P))"


lemma eval_model_correct: "valid_list_graph G \<Longrightarrow> NM_ACLcommunicateWith.eval_model (list_graph_to_graph G) nP = eval_model G nP"
by (metis NM_ACLcommunicateWith.eval_model.simps NM_ACLcommunicateWith_impl.eval_model.simps graph.select_convs(1) list_graph_to_graph_def succ_tran_correct)


interpretation NM_ACLcommunicateWith_impl:TopoS_List_Impl 
  where default_node_properties=NM_ACLcommunicateWith.default_node_properties
  and eval_model_spec=NM_ACLcommunicateWith.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_ACLcommunicateWith.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_ACLcommunicateWith.target_focus
  and offending_flows_impl=ACLcommunicateWith_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=ACLcommunicateWith_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_ACLcommunicateWith)
  apply(rule conjI)
   apply(intro allI impI)
   apply(fact eval_model_correct)
  apply(simp)
 apply(rule conjI)
  apply(unfold ACLcommunicateWith_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(intro allI impI)
  apply(simp only: eval_model_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis ACLcommunicateWith.node_props.simps ACLcommunicateWith.node_props_eq_node_props_formaldef)
 apply(simp only: ACLcommunicateWith_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_ACLcommunicateWith])
  apply(simp only: eval_model_correct)
 apply(simp)
done


section {* packing *}
  definition NM_LIB_ACLcommunicateWith:: "('v::vertex, 'v access_list, unit) TopoS_packed" where
    "NM_LIB_ACLcommunicateWith \<equiv> 
    \<lparr> nm_name = ''ACLcommunicateWith'', 
      nm_target_focus = NM_ACLcommunicateWith.target_focus,
      nm_default = NM_ACLcommunicateWith.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = ACLcommunicateWith_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = ACLcommunicateWith_eval
      \<rparr>"
  interpretation NM_LIB_ACLcommunicateWith_interpretation: TopoS_modelLibrary NM_LIB_ACLcommunicateWith
      NM_ACLcommunicateWith.eval_model NM_ACLcommunicateWith.verify_globals
    apply(unfold TopoS_modelLibrary_def NM_LIB_ACLcommunicateWith_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {* Examples*}
  text{*
    1 can acceess 2 and 3
    2 can access 3
  *}
  definition exampleG :: "nat list_graph" where
    "exampleG \<equiv> \<lparr> nodesL = [1, 2, 3],
                    edgesL = [(1,2), (2,3)]\<rparr>"

  definition examplenP :: "nat \<Rightarrow> nat access_list" where
    "examplenP \<equiv> ((\<lambda>v. NM_ACLcommunicateWith.default_node_properties)
                    (1 := AccessList [2,3]))
                    (2 := AccessList [3])"

  lemma "eval_model exampleG examplenP" by eval
  value[code] "ACLcommunicateWith_offending_list exampleG examplenP"

  hide_const exampleG examplenP



hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
