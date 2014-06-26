theory NM_NoRefl
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel hosts are not allowed to communicate with themselves *}

text {* This can be used to effectively lift hosts to roles.
        Just list all roles that are allowed to communicate with themselves.
        Otherwise, communication between hosts of the same role (group) is prohibited. 
        Usefull in conjunction with the security gateway *}

datatype node_config = NoRefl | Refl 

definition default_node_properties :: "node_config"
  where  "default_node_properties = NoRefl"


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (s, r) \<in> edges G. s = r \<longrightarrow> nP s = Refl)"


fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus = False"



subsubsection {*Preliminaries*}
  lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
    apply(simp only: NetworkModel_withOffendingFlows.eval_model_mono_def)
    apply(clarify)
    by auto
  
  interpretation NetworkModel_preliminaries
  where eval_model = eval_model
  and verify_globals = verify_globals
    apply unfold_locales
      apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
          apply(auto)[6]
     apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops)[1]
    apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
   done

 lemma NoRfl_ENRsr: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_sr eval_model (\<lambda> nP\<^sub>s s nP\<^sub>r r. s = r \<longrightarrow> nP\<^sub>s = Refl)"
    by(simp add: NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_sr_def)

  definition NoRefl_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "NoRefl_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 = e2 \<and> nP e1 = NoRefl} })"

 thm NetworkModel_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr]

  lemma NoRefl_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = NoRefl_offending_set"
    apply(simp only: fun_eq_iff NoRefl_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(simp only: NetworkModel_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr])
    apply(case_tac "eval_model G nP")
    apply(simp)
    apply(simp)
    apply(rule)
    apply(rule)
     apply(clarsimp)
     using node_config.exhaust apply blast
    apply(rule)
    apply(rule)
    apply(clarsimp)
   done


interpretation NoRefl: NetworkModel_ACS
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = NoRefl_offending_set"
  unfolding default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply(frule NM_NoRefl.offending_notevalD)
    apply(simp only: NetworkModel_withOffendingFlows.ENFsr_offending_set[OF NoRfl_ENRsr])
    apply fastforce
   apply(erule default_uniqueness_by_counterexample_ACS)
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(rule_tac x="\<lparr> nodes={vertex_1}, edges = {(vertex_1,vertex_1)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(case_tac otherbot, simp_all)
   apply(rule_tac x="(\<lambda> x. NoRefl)(vertex_1 := NoRefl, vertex_2 := NoRefl)" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_1)}" in exI, simp)
  apply(fact NoRefl_offending_set)
  done




  lemma NetworkModel_NoRefl: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales  

hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties


end
