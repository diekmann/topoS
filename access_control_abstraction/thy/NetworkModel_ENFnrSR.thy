theory NetworkModel_ENFnrSR
imports Main NetworkModel_Interface NetworkModel_Util
begin



section {* edges normal form not refl ENFnrSR *}
  definition (in NetworkModel_withOffendingFlows) eval_model_all_edges_normal_form_not_refl_SR :: "('a \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
    "eval_model_all_edges_normal_form_not_refl_SR P \<equiv> 
    \<forall> G nP. eval_model G nP = (\<forall> (s, r) \<in> edges G. s \<noteq> r \<longrightarrow> P (nP s) s (nP r) r)"


section {*offending flows*}
  lemma (in NetworkModel_withOffendingFlows)  ENFnrSR_offending_members:
    assumes a_not_eval: "\<not> eval_model G nP"
    and   a_enf: "eval_model_all_edges_normal_form_not_refl_SR P"
    and   a_offending: "f \<in> set_offending_flows G nP"
    shows
          "f \<subseteq> edges G \<and> (\<forall> (e1, e2) \<in> f. \<not> P (nP e1) e1 (nP e2) e2 \<and> e1 \<noteq> e2)"
  proof -
    from a_enf have a_enf': "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2) \<in> (edges G). e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)" 
      using eval_model_all_edges_normal_form_not_refl_SR_def by simp
  
    from a_offending have a_offending': "f \<subseteq> edges G \<and>
        (\<forall>(e1, e2)\<in>(edges G) - f. e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2) \<and> 
        (\<forall>(e1, e2)\<in>f. \<not> (\<forall>(e1, e2)\<in>(edges G) - f \<union> {(e1, e2)}. e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2))"
      apply(simp add: set_offending_flows_def)
      unfolding is_offending_flows_min_set_def
      unfolding is_offending_flows_def
      apply(simp only: a_not_eval)
      apply simp
      apply(simp only:a_enf')
      apply(simp add:graph_ops)
      by force
  
    from a_offending' have a_f_1: "f \<subseteq> edges G" by simp
    from a_offending' have a_f_2: "\<forall>(e1, e2) \<in> edges G - f. e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2" by simp
    from a_offending' have a_f_3: "\<forall>(e1, e2) \<in> f. \<not> (\<forall>(e1', e2') \<in> edges G - f \<union> {(e1, e2)}. e1' \<noteq> e2' \<longrightarrow> P (nP e1') e1' (nP e2') e2' )" by fastforce
    from this a_offending' have a_f_3_in_f': "\<forall>(e1, e2) \<in> f. \<not> (\<forall>(e1', e2') \<in> edges G - f \<union> {(e1, e2)}. e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)"
    by auto
    from a_f_3_in_f' have x1: "\<And> e1 e2. (e1, e2) \<in> f \<Longrightarrow> \<not> P (nP e1) e1 (nP e2) e2" by fast
    from a_f_3_in_f' have x2: "\<And> e1 e2. (e1, e2) \<in> f \<Longrightarrow> e1 \<noteq> e2" by fast
    from a_f_1 x1 x2 show ?thesis by force
  qed

  lemma (in NetworkModel_withOffendingFlows) ENFnrSR_offending_flows_structure:
    "\<lbrakk> \<not> eval_model G nP; eval_model_all_edges_normal_form_not_refl_SR P; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
      f = {(e1, e2). (e1, e2)\<in> edges G \<and> \<not> P (nP e1) e1 (nP e2) e2 \<and> e1 \<noteq> e2}"
    apply(frule ENFnrSR_offending_members, simp, simp)
    apply(clarify)
    apply rule
     apply fastforce
    apply(simp add:set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def eval_model_all_edges_normal_form_not_refl_SR_def graph_ops)
    apply clarsimp
    done
  
  lemma (in NetworkModel_withOffendingFlows) ENFnrSR_notevalmodel_imp_offending_not_empty:
  "eval_model_all_edges_normal_form_not_refl_SR P \<Longrightarrow> 
    \<not> eval_model G nP \<Longrightarrow>
    set_offending_flows G nP \<noteq> {}"
    apply(simp add: set_offending_flows_def eval_model_all_edges_normal_form_not_refl_SR_def)
    apply(simp only:is_offending_flows_min_set_def is_offending_flows_def)
    apply(simp only: graph_ops)
    apply simp
    apply(rule_tac x="{e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not>P (nP e1) e1 (nP e2) e2}" in exI)
    apply(rule conjI)
      apply fastforce+
   done

  lemma (in NetworkModel_withOffendingFlows) ENFnrSR_offending_case1:
    "\<lbrakk> eval_model_all_edges_normal_form_not_refl_SR P;  \<not> eval_model G nP \<rbrakk> \<Longrightarrow>
    { {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (nP e1) e1 (nP e2) e2 \<and> e1 \<noteq> e2} } =
    set_offending_flows G nP"
    apply(insert ENFnrSR_offending_flows_structure[of G nP P])
    apply(simp only:HOL.not_False_eq_True)
    apply rule
    apply(insert ENFnrSR_notevalmodel_imp_offending_not_empty[of P G nP], simp)
     apply blast+
    done
  
  lemma (in NetworkModel_withOffendingFlows) ENFnrSR_offending_case2:
    "\<lbrakk> eval_model_all_edges_normal_form_not_refl_SR P; eval_model G nP \<rbrakk> \<Longrightarrow>
    {} = set_offending_flows G nP"
    apply(drule validmodel_imp_no_offending[of G nP])
    apply simp
  done


   theorem (in NetworkModel_withOffendingFlows) ENFnrSR_offending_set:
    "\<lbrakk> eval_model_all_edges_normal_form_not_refl_SR P \<rbrakk> \<Longrightarrow>
    set_offending_flows G nP = (if eval_model G nP then
      {}
     else 
      { {(e1,e2). (e1, e2) \<in> edges G \<and> e1 \<noteq> e2 \<and> \<not> P (nP e1) e1 (nP e2) e2} })"
  apply(cases "eval_model G nP")
  apply(drule ENFnrSR_offending_case2, simp)
   apply simp
  apply(drule ENFnrSR_offending_case1, simp)
  apply(simp)
  by blast


section {* Instance helper*}


  (* fsts version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnrSR_fsts_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_not_eval: "\<not> eval_model G nP"
    and   a_enf: "eval_model_all_edges_normal_form_not_refl_SR P"
    and   a_weakrefl: "\<forall> s r. P \<bottom> s \<bottom> r"
    and   a_botdefault: "\<forall> s r. (nP r) \<noteq> \<bottom> \<longrightarrow> \<not> P (nP s) s (nP r) r \<longrightarrow> \<not> P \<bottom> s (nP r) r"
    and   a_alltobot: "\<forall> s r. P (nP s) s \<bottom> r"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_fsts: "i \<in> fst` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .
    from a_enf have a_enf': "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2)\<in> (edges G). e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)" 
      using eval_model_all_edges_normal_form_not_refl_SR_def by simp
  
    from ENFnrSR_offending_members[OF a_not_eval a_enf a_offending] have a_f_3_in_f: "\<And> e1 e2. (e1, e2)\<in>f \<Longrightarrow> \<not> P (nP e1) e1 (nP e2) e2" by fast
    from ENFnrSR_offending_members[OF a_not_eval a_enf a_offending]  have a_f_3_neq: "\<And> e1 e2. (e1, e2)\<in>f \<Longrightarrow> e1 \<noteq> e2" by fast
  
    let ?nP' = "(nP(i := \<bottom>))"

    from offending_not_empty[OF a_offending] ENFnrSR_offending_members[OF a_not_eval a_enf a_offending] a_i_fsts hd_in_set
      obtain e1 e2 where e1e2cond: "(e1, e2)\<in>f \<and> e1 = i" by force
  
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
  
    from this e1e2cond conjunct1[OF ENFnrSR_offending_members[OF a_not_eval a_enf a_offending]] conjunct1[OF e1e2cond] `e2 \<noteq> e1` have 
      "\<exists> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<and> \<not> P (?nP' e1) e1 (?nP' e2) e2" by fastforce
    hence "\<not> (\<forall> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<longrightarrow> P ((nP(i := \<bottom>)) e1) e1 ((nP(i := \<bottom>)) e2) e2)" by fast
    from this a_enf' show "\<not> eval_model G (nP(i := \<bottom>))" by fast
  qed



  (* snds version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnrSR_snds_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_not_eval: "\<not> eval_model G nP"
    and   a_enf: "eval_model_all_edges_normal_form_not_refl_SR P"
    and   a_weakrefl: "\<forall> s r. P \<bottom> s \<bottom> r"
    and   a_botdefault: "\<forall> s r. (nP s) \<noteq> \<bottom> \<longrightarrow> \<not> P (nP s) s (nP r) r \<longrightarrow> \<not> P (nP s) s \<bottom> r"
    and   a_bottoall: "\<forall> s r. P \<bottom> s (nP r) r"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_snds: "i \<in> snd` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .
    from a_enf have a_enf': "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2)\<in>(edges G). e1 \<noteq> e2 \<longrightarrow> P (nP e1) e1 (nP e2) e2)" 
      using eval_model_all_edges_normal_form_not_refl_SR_def by simp
  
    from ENFnrSR_offending_members[OF a_not_eval a_enf a_offending] have a_f_3_in_f: "\<And> s r. (s, r)\<in>f \<Longrightarrow> \<not> P (nP s) s (nP r) r" by fast
    from ENFnrSR_offending_members[OF a_not_eval a_enf a_offending]  have a_f_3_neq: "\<And> s r. (s, r)\<in>f \<Longrightarrow> s \<noteq> r" by fast
  
    let ?nP' = "(nP(i := \<bottom>))"

    from offending_not_empty[OF a_offending] ENFnrSR_offending_members[OF a_not_eval a_enf a_offending] a_i_snds hd_in_set
      obtain e1 e2 where e1e2cond: "(e1, e2)\<in>f \<and> e2 = i" by force
  
    from conjunct1[OF e1e2cond] a_f_3_in_f have e1e2notP: "\<not> P (nP e1) e1 (nP e2) e2" by simp
    from e1e2notP a_weakrefl have e1ore2neqbot: "(nP e1) \<noteq> \<bottom> \<or> (nP e2) \<noteq> \<bottom>" by fastforce
    from e1e2notP a_bottoall have x1: "(nP e1) \<noteq> \<bottom>" by fastforce
    from this e1e2notP a_botdefault have x2: "\<not> P (nP e1) e1 \<bottom> e2" by fast
    from this e1e2notP have e1e2subgoal1: "\<not> P (nP e1) e1 (?nP' e2) e2" by auto

    from a_f_3_neq e1e2cond have "e2 \<noteq> e1" by blast
  
    from e1e2subgoal1 have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) e1 (?nP' e2) e2" by(simp add: e1e2cond)
  
    from this e1e2cond conjunct1[OF ENFnrSR_offending_members[OF a_not_eval a_enf a_offending]] conjunct1[OF e1e2cond] `e2 \<noteq> e1` have 
      "\<exists> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<and> \<not> P (?nP' e1) e1 (?nP' e2) e2" by fastforce
    hence "\<not> (\<forall> (e1, e2)\<in>(edges G). e2 \<noteq> e1 \<longrightarrow> P ((nP(i := \<bottom>)) e1) e1 ((nP(i := \<bottom>)) e2) e2)" by fast
    from this a_enf' show "\<not> eval_model G (nP(i := \<bottom>))" by fast
  qed



end
