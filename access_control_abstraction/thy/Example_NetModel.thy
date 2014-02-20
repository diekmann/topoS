theory Example_NetModel
imports NetworkModel_Interface NetworkModel_Helper
begin

text{* A toy example that defines a valid network security requirement model *}

definition default_node_properties :: "bool"
  where  "default_node_properties \<equiv> False"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> (edges G). (nP e1) \<and> (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

(* we will not define target_focus!! Works for both! *)


lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
  apply(simp only: NetworkModel_withOffendingFlows.eval_model_mono_def)
  apply(clarify)
  by auto

 
-- "The preliminaries: mostly, eval_model is monotonic"
interpretation NetworkModel_preliminaries
where eval_model = eval_model
and verify_globals = verify_globals
  apply unfold_locales
  apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
  apply(erule_tac exE)
  apply(rename_tac list_edges)
  apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
  apply(auto)[6]
  apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops)[2]
  apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
done


-- "With generic target focus"
interpretation Example_NetModel: NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus (*yep, that's a variable*)
  unfolding default_node_properties_def
  apply unfold_locales

  -- "Secure bydefault"
  apply(simp)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:delete_edges_simp2 graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
    apply blast

 -- "Uniqueness"
 apply(simp add:default_node_properties_def)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:delete_edges_simp2 graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  -- "proof by counter example: assume False is not the unique default parameter"
  apply(rule_tac x="\<lparr> nodes={vertex_1}, edges = {(vertex_1,vertex_1)} \<rparr>" in exI, simp)
  apply(rule conjI)
  apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := False)" in exI, simp add:default_node_properties_def)
  apply(case_tac target_focus)
    apply(simp_all)
    apply(rule_tac x="{(vertex_1,vertex_1)}" in exI, simp)+
done


text{*And we end up with a totally useless network security requirement model. I hope this was instructive.*}

end
