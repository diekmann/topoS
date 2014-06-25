theory NetworkModel_ENFnrSR
imports NetworkModel_ENF_sr
begin

section {* edges normal form not refl ENFnrSR *}
  definition (in NetworkModel_withOffendingFlows) eval_model_all_edges_normal_form_not_refl_SR :: "('a \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
    "eval_model_all_edges_normal_form_not_refl_SR P \<equiv> 
    \<forall> G nP. eval_model G nP = (\<forall> (s, r) \<in> edges G. s \<noteq> r \<longrightarrow> P (nP s) s (nP r) r)"



  text{* we derive everything from the ENFnrSR form *}
  lemma (in NetworkModel_withOffendingFlows) ENFnrSR_to_ENFsr: 
    "eval_model_all_edges_normal_form_not_refl_SR P \<Longrightarrow> eval_model_all_edges_normal_form_sr (\<lambda> p1 v1 p2 v2. v1 \<noteq> v2 \<longrightarrow> P p1 v1 p2 v2)"
    by(simp add: eval_model_all_edges_normal_form_sr_def eval_model_all_edges_normal_form_not_refl_SR_def)
    


section {*offending flows*}
   theorem (in NetworkModel_withOffendingFlows) ENFnrSR_offending_set:
    "\<lbrakk> eval_model_all_edges_normal_form_not_refl_SR P \<rbrakk> \<Longrightarrow>
    set_offending_flows G nP = (if eval_model G nP then
      {}
     else 
      { {(e1,e2). (e1, e2) \<in> edges G \<and> e1 \<noteq> e2 \<and> \<not> P (nP e1) e1 (nP e2) e2} })"
    by(auto dest: ENFnrSR_to_ENFsr simp: ENFsr_offending_set)


section {* Instance helper*}

  (* fsts version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnrSR_fsts_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf: "eval_model_all_edges_normal_form_not_refl_SR P"
    and   a_weakrefl: "\<forall> s r. P \<bottom> s \<bottom> r"
    and   a_botdefault: "\<forall> s r. (nP r) \<noteq> \<bottom> \<longrightarrow> \<not> P (nP s) s (nP r) r \<longrightarrow> \<not> P \<bottom> s (nP r) r"
    and   a_alltobot: "\<forall> s r. P (nP s) s \<bottom> r"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_fsts: "i \<in> fst` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from a_offending have a_not_eval: "\<not> eval_model G nP" by (metis ex_in_conv validmodel_imp_no_offending)
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .
    from a_enf have a_enf': "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2)\<in> (edges G). e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)" 
      using eval_model_all_edges_normal_form_not_refl_SR_def by simp
  
    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending have a_f_3_in_f: "\<And> e1 e2. (e1, e2)\<in>f \<Longrightarrow> \<not> P (nP e1) e1 (nP e2) e2" by(simp)
    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending have a_f_3_neq: "\<And> e1 e2. (e1, e2)\<in>f \<Longrightarrow> e1 \<noteq> e2" by simp
  
    let ?nP' = "(nP(i := \<bottom>))"

    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending a_i_fsts
      obtain e1 e2 where e1e2cond: "(e1, e2) \<in> f \<and> e1 = i" by fastforce

    from conjunct1[OF e1e2cond] a_offending have "(e1, e2) \<in> edges G"
      by (metis (lifting, no_types) NetworkModel_withOffendingFlows.set_offending_flows_def mem_Collect_eq set_rev_mp)
  
    from conjunct1[OF e1e2cond] a_f_3_in_f have e1e2notP: "\<not> P (nP e1) e1 (nP e2) e2" by simp
    from e1e2notP a_weakrefl have e1ore2neqbot: "(nP e1) \<noteq> \<bottom> \<or> (nP e2) \<noteq> \<bottom>" by fastforce
    from e1e2notP a_alltobot have "(nP e2) \<noteq> \<bottom>" by fastforce
    from this e1e2notP a_botdefault have "\<not> P \<bottom> e1 (nP e2) e2" by simp
    from this e1e2notP have e1e2subgoal1: "\<not> P (?nP' e1) e1 (nP e2) e2" by auto

    from a_f_3_neq e1e2cond have "e2 \<noteq> e1" by blast
  
    from e1e2subgoal1 have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) e1 (?nP' e2) e2"
      apply simp
      apply(rule conjI)
       apply blast
      apply(insert e1e2cond)
      by simp
    from this `e2 \<noteq> e1` have "\<not> P (?nP' e1) e1 (?nP' e2) e2" by simp
  
    from this `e2 \<noteq> e1` ENFnrSR_offending_set[OF a_enf] a_offending `(e1, e2) \<in> edges G` have 
      "\<exists> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<and> \<not> P (?nP' e1) e1 (?nP' e2) e2" by blast
    hence "\<not> (\<forall> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<longrightarrow> P ((nP(i := \<bottom>)) e1) e1 ((nP(i := \<bottom>)) e2) e2)" by fast
    from this a_enf' show "\<not> eval_model G (nP(i := \<bottom>))" by fast
  qed



  (* snds version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnrSR_snds_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf: "eval_model_all_edges_normal_form_not_refl_SR P"
    and   a_weakrefl: "\<forall> s r. P \<bottom> s \<bottom> r"
    and   a_botdefault: "\<forall> s r. (nP s) \<noteq> \<bottom> \<longrightarrow> \<not> P (nP s) s (nP r) r \<longrightarrow> \<not> P (nP s) s \<bottom> r"
    and   a_bottoall: "\<forall> s r. P \<bottom> s (nP r) r"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_snds: "i \<in> snd` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from a_offending have a_not_eval: "\<not> eval_model G nP" by (metis equals0D validmodel_imp_no_offending)
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .
    from a_enf have a_enf': "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2)\<in>(edges G). e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)" 
      using eval_model_all_edges_normal_form_not_refl_SR_def by simp
  
    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending have a_f_3_in_f: "\<And> s r. (s, r)\<in>f \<Longrightarrow> \<not> P (nP s) s (nP r) r" by simp
    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending have a_f_3_neq: "\<And> s r. (s, r)\<in>f \<Longrightarrow> s \<noteq> r" by simp
  
    let ?nP' = "(nP(i := \<bottom>))"

    from ENFnrSR_offending_set[OF a_enf] a_not_eval a_offending a_i_snds
      obtain e1 e2 where e1e2cond: "(e1, e2)\<in>f \<and> e2 = i" by fastforce

    from conjunct1[OF e1e2cond] a_offending have "(e1, e2) \<in> edges G"
      by (metis (lifting, no_types) NetworkModel_withOffendingFlows.set_offending_flows_def mem_Collect_eq set_rev_mp)
  
    from conjunct1[OF e1e2cond] a_f_3_in_f have e1e2notP: "\<not> P (nP e1) e1 (nP e2) e2" by simp
    from e1e2notP a_weakrefl have e1ore2neqbot: "(nP e1) \<noteq> \<bottom> \<or> (nP e2) \<noteq> \<bottom>" by fastforce
    from e1e2notP a_bottoall have x1: "(nP e1) \<noteq> \<bottom>" by fastforce
    from this e1e2notP a_botdefault have x2: "\<not> P (nP e1) e1 \<bottom> e2" by fast
    from this e1e2notP have e1e2subgoal1: "\<not> P (nP e1) e1 (?nP' e2) e2" by auto

    from a_f_3_neq e1e2cond have "e2 \<noteq> e1" by blast
  
    from e1e2subgoal1 have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) e1 (?nP' e2) e2" by(simp add: e1e2cond)
  
    from this `e2 \<noteq> e1` ENFnrSR_offending_set[OF a_enf] a_offending `(e1, e2) \<in> edges G` have 
      "\<exists> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<and> \<not> P (?nP' e1) e1 (?nP' e2) e2" by fastforce
    hence "\<not> (\<forall> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<longrightarrow> P ((nP(i := \<bottom>)) e1) e1 ((nP(i := \<bottom>)) e2) e2)" by fast
    from this a_enf' show "\<not> eval_model G (nP(i := \<bottom>))" by fast
  qed



end
