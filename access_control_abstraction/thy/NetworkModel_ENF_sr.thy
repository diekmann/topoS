theory NetworkModel_ENF_sr
imports Main NetworkModel_Interface NetworkModel_Util NetworkModel_withOffendingFlows_lemmata
begin



section {* edges normal form ENF with sender and receiver names *}
  definition (in NetworkModel_withOffendingFlows) eval_model_all_edges_normal_form_sr :: "('a \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
    "eval_model_all_edges_normal_form_sr P \<equiv> \<forall> G nP. eval_model G nP = (\<forall> (s, r)\<in> edges G. P (nP s) s (nP r) r)"
  

  lemma (in NetworkModel_withOffendingFlows) ENFsr_monotonicity_eval_model_mono: "\<lbrakk> eval_model_all_edges_normal_form_sr P \<rbrakk> \<Longrightarrow>
    eval_model_mono"
    apply(simp add: eval_model_all_edges_normal_form_sr_def eval_model_mono_def)
    by blast

section {* offending flows:*}
  
  theorem (in NetworkModel_withOffendingFlows) ENFsr_offending_set:
    assumes ENFsr: "eval_model_all_edges_normal_form_sr P"
    shows "set_offending_flows G nP = (if eval_model G nP then
      {}
     else 
      { {(s,r). (s, r) \<in> edges G \<and> \<not> P (nP s) s (nP r) r} })" (is "?A = ?B")
  proof(cases "eval_model G nP")
  case True thus "?A = ?B" 
    by(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def)
  next
  case False
   from ENFsr have ENFsr_offending_imp_not_P: "\<And> F s r. F \<in> set_offending_flows G nP \<Longrightarrow> (s, r) \<in> F  \<Longrightarrow> \<not> P (nP s) s (nP r) r"
     unfolding eval_model_all_edges_normal_form_sr_def
     apply(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
     apply clarify
     by fastforce
   from ENFsr have  ENFsr_offending_set_P_representation: 
    "\<And> F. F \<in> set_offending_flows G nP  \<Longrightarrow> F = {(s,r). (s, r) \<in> edges G \<and> \<not> P (nP s) s (nP r) r}"
      apply -
      apply rule
       apply rule
       apply clarify
       apply(rename_tac a b)
       apply rule
        apply(auto simp add:set_offending_flows_def)[1]
       apply(simp add: ENFsr_offending_imp_not_P)
      unfolding eval_model_all_edges_normal_form_sr_def
      apply(simp add:set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
      apply clarify
      apply(rename_tac a b a1 b1)
      apply(blast)
    done
  

    from ENFsr False have ENFsr_offending_flows_exist: "set_offending_flows G nP \<noteq> {}"
      apply(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def eval_model_all_edges_normal_form_sr_def
            delete_edges_def add_edge_def)
      apply(clarify)
      apply(rename_tac s r)
      apply(rule_tac x="{(s,r). (s,r) \<in> (edges G) \<and> \<not>P (nP s) s (nP r) r}" in exI)
      apply(simp)
      by blast

    from ENFsr have ENFsr_offenindg_not_empty_imp_ENF_offending_subseteq_rhs:
      "set_offending_flows G nP \<noteq> {}  \<Longrightarrow>
      { {(s,r). (s, r) \<in> edges G \<and> \<not> P (nP s) s (nP r) r} } \<subseteq> set_offending_flows G nP"
      apply -
      apply rule
      using ENFsr_offending_set_P_representation
      by blast

    from ENFsr have ENFsr_offending_subseteq_lhs:
      "(set_offending_flows G nP) \<subseteq> { {(s,r). (s, r) \<in> edges G \<and> \<not> P (nP s) s (nP r) r} }"
      apply -
      apply rule
      by(simp add: ENFsr_offending_set_P_representation)

    from False ENFsr_offenindg_not_empty_imp_ENF_offending_subseteq_rhs[OF ENFsr_offending_flows_exist] ENFsr_offending_subseteq_lhs show "?A = ?B"
      by force
  qed
  
  

end
