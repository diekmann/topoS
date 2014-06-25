theory NetworkModel_ENF
imports Main NetworkModel_Interface NetworkModel_Util NetworkModel_withOffendingFlows_lemmata
begin



section {* NetworkModel theory: Often the @{term "eval_model"} function has a common structure.
  We call this the ll edges normal form (ENF). This file provides some theory for 
  @{term "eval_model"} functions in ENF. Helps instantiation of new models in ENF.*}


(*TODO most could be inherited from ENF_sr*)




section {* edges normal form ENF *}
  definition (in NetworkModel_withOffendingFlows) eval_model_all_edges_normal_form :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
    "eval_model_all_edges_normal_form P \<equiv> \<forall> G nP. eval_model G nP = (\<forall> (e1, e2)\<in> edges G. P (nP e1) (nP e2))"
  

  (* reflexivity is needed for convenience. If a network security model is not refexive, that means that all nodes with the default
    parameter \<bottom> are not allowed to communicate with each other *)
  definition (in NetworkModel_withOffendingFlows)  ENF_refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
    "ENF_refl P \<equiv> eval_model_all_edges_normal_form P \<and> (\<forall> p1. P p1 p1)"

    
  lemma (in NetworkModel_withOffendingFlows) monotonicity_eval_model_mono: "\<lbrakk> eval_model_all_edges_normal_form P \<rbrakk> \<Longrightarrow>
    eval_model_mono"
    apply(simp add: eval_model_all_edges_normal_form_def eval_model_mono_def)
    by blast

section {* offending flows:*}
  
  lemma (in NetworkModel_withOffendingFlows) ENF_is_offending_flow_ex_not_P:
    "\<lbrakk> eval_model_all_edges_normal_form P;
    is_offending_flows f G nP \<rbrakk>
    \<Longrightarrow> (\<exists> (e1, e2) \<in> edges G. \<not> P (nP e1) (nP e2))"
    unfolding eval_model_all_edges_normal_form_def
    unfolding is_offending_flows_def
    apply blast
    done
  lemma (in NetworkModel_withOffendingFlows) "eval_model_all_edges_normal_form P \<Longrightarrow>
    (f \<in> set_offending_flows G nP) \<and> f \<noteq> {} 
    \<Longrightarrow> (\<exists> (e1, e2) \<in> f.  \<not> P (nP e1) (nP e2))"
    unfolding eval_model_all_edges_normal_form_def
    apply(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
    apply clarify
    apply(blast)
  done
  
  
  lemma (in NetworkModel_withOffendingFlows) ENF_offending_imp_not_P: "eval_model_all_edges_normal_form P \<Longrightarrow>
    f \<in> set_offending_flows G nP \<Longrightarrow> (e1, e2) \<in> f 
    \<Longrightarrow> \<not> P (nP e1) (nP e2)"
    unfolding eval_model_all_edges_normal_form_def
    apply(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
    apply clarify
    by fastforce
  
  
  lemma (in NetworkModel_withOffendingFlows) ENF_offending_set_P_representation: 
    "eval_model_all_edges_normal_form P \<Longrightarrow> 
    f \<in> set_offending_flows G nP
    \<Longrightarrow> f = {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (nP e1) (nP e2)}"
    apply rule
     apply rule
     apply clarify
     apply(rename_tac a b)
     apply rule
      apply(auto simp add:set_offending_flows_def)[1]
     apply(simp add: ENF_offending_imp_not_P[of P f G nP])
    unfolding eval_model_all_edges_normal_form_def
    apply(simp add:set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
    apply clarify
    apply(rename_tac a b a1 b1)
    apply(blast)
  done
  
  
  (* We can show an overapproximation already: *)
  lemma (in NetworkModel_withOffendingFlows) ENF_offending_subseteq_lhs:
    "eval_model_all_edges_normal_form P \<Longrightarrow> 
    (set_offending_flows G nP) \<subseteq>
    { {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (nP e1) (nP e2)} }"
    apply rule
    by(simp add: ENF_offending_set_P_representation[of P _ G nP])
  
  
  (* if offending flows not empty, we have the other direction *)
  lemma (in NetworkModel_withOffendingFlows) ENF_offenindg_not_empty_imp_ENF_offending_subseteq_rhs:
    "eval_model_all_edges_normal_form P \<Longrightarrow> 
    set_offending_flows G nP \<noteq> {}  \<Longrightarrow>
    { {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (nP e1) (nP e2)} } \<subseteq> set_offending_flows G nP"
    apply rule
    apply(insert ENF_offending_set_P_representation[of P _ G nP],simp)[1]
    apply blast
   done
  
  
  
  
  lemma (in NetworkModel_withOffendingFlows) ENF_notevalmodel_offending_imp_ex_offending_min:
   "eval_model_all_edges_normal_form P \<Longrightarrow> 
   is_offending_flows f G nP \<Longrightarrow> f \<subseteq> edges G 
   \<Longrightarrow> \<exists>f'. f' \<subseteq> edges G \<and> is_offending_flows_min_set f' G nP"
    unfolding eval_model_all_edges_normal_form_def
    apply(simp only:is_offending_flows_def is_offending_flows_min_set_def)
    apply(simp only:graph_ops)
    apply simp
    (* select f' as the list of all edges of f which violate P *)
    apply(rule_tac x="{(e1,e2). (e1,e2) \<in> (edges G) \<and> \<not>P (nP e1) (nP e2)}" in exI) (* f better than edges G but proof harder *)
    apply simp
    apply force
  done
  
  lemma (in NetworkModel_withOffendingFlows) ENF_notevalmodel_imp_ex_offending:
  "\<lbrakk> eval_model_all_edges_normal_form P;
    \<not> eval_model G nP \<rbrakk> \<Longrightarrow>
    \<exists>f. f \<subseteq> (edges G) \<and> is_offending_flows f G nP"
    unfolding eval_model_all_edges_normal_form_def
    apply(simp add: Set.Ball_def)
    apply(simp only:is_offending_flows_def)
    apply(simp only:graph_ops)
    apply simp
    apply(rule_tac x="{(e1,e2). (e1,e2) \<in> (edges G) \<and> \<not>P (nP e1) (nP e2)}" in exI)
    apply(rule conjI)
     apply blast
    apply blast
  done
  
  lemma (in NetworkModel_withOffendingFlows) ENF_notevalmodel_imp_ex_offending_min:
  "\<lbrakk> eval_model_all_edges_normal_form P;
    \<not> eval_model G nP \<rbrakk> \<Longrightarrow>
    \<exists>f. f \<subseteq> edges G \<and> is_offending_flows_min_set f G nP"
    apply(frule ENF_notevalmodel_imp_ex_offending[of P G nP], simp)
    apply(erule exE)
    using ENF_notevalmodel_offending_imp_ex_offending_min[of P _ G nP] by fast
  
  lemma (in NetworkModel_withOffendingFlows) ENF_notevalmodel_imp_offending_not_empty:
  "eval_model_all_edges_normal_form P \<Longrightarrow> 
    \<not> eval_model G nP \<Longrightarrow>
    set_offending_flows G nP \<noteq> {}"
    apply(drule ENF_notevalmodel_imp_ex_offending_min[of P G nP], simp)
    apply(simp add: set_offending_flows_def)
   done
  
  lemma (in NetworkModel_withOffendingFlows) ENF_offending_case1:
    "\<lbrakk> eval_model_all_edges_normal_form P;  \<not> eval_model G nP \<rbrakk> \<Longrightarrow>
    { {(e1,e2). (e1, e2) \<in> (edges G) \<and> \<not> P (nP e1) (nP e2)} } = set_offending_flows G nP"
    apply(rule)
     apply(frule ENF_notevalmodel_imp_offending_not_empty, simp)
     apply(rule ENF_offenindg_not_empty_imp_ENF_offending_subseteq_rhs, simp)
     apply simp
    apply(rule ENF_offending_subseteq_lhs)
    apply simp
  done
  
  lemma (in NetworkModel_withOffendingFlows) ENF_offending_case2:
    "\<lbrakk> eval_model_all_edges_normal_form P; eval_model G nP \<rbrakk> \<Longrightarrow>
    {} = set_offending_flows G nP"
    apply(drule validmodel_imp_no_offending[of G nP])
    apply simp
  done
  
  
  theorem (in NetworkModel_withOffendingFlows) ENF_offending_set:
    "\<lbrakk> eval_model_all_edges_normal_form P \<rbrakk> \<Longrightarrow>
    set_offending_flows G nP = (if eval_model G nP then
      {}
     else 
      { {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (nP e1) (nP e2)} })"
  by(simp add: ENF_offending_case1 ENF_offending_case2)


section {* lemata *}

  lemma (in NetworkModel_withOffendingFlows)  ENF_offending_members:
    "\<lbrakk> \<not> eval_model G nP; eval_model_all_edges_normal_form P; f \<in> set_offending_flows G nP\<rbrakk> \<Longrightarrow> 
    f \<subseteq> (edges G) \<and> (\<forall> (e1, e2)\<in> f. \<not> P (nP e1) (nP e2))"
  by(auto simp add: ENF_offending_set)
 


section {* instance helper *}
  
  lemma (in NetworkModel_withOffendingFlows) ENF_refl_not_offedning:
        "\<lbrakk> \<not> eval_model G nP; f \<in> set_offending_flows G nP; 
          ENF_refl P\<rbrakk> \<Longrightarrow>
          \<forall>(e1,e2) \<in> f. e1 \<noteq> e2"
  proof -
  assume a_not_eval: "\<not> eval_model G nP"
    and   a_enf_refl: "ENF_refl P"
    and   a_offedning: "f \<in> set_offending_flows G nP"
  
    from a_enf_refl have a_enf: "eval_model_all_edges_normal_form P" using ENF_refl_def by simp
    hence a_ENF: "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2) \<in> edges G. P (nP e1) (nP e2))" using eval_model_all_edges_normal_form_def by simp
    
    from a_enf_refl ENF_refl_def have a_refl: "\<forall> (e1,e1) \<in> f. P (nP e1) (nP e1)" by simp
    from ENF_offending_members[OF a_not_eval a_enf a_offedning] have "\<forall> (e1, e2) \<in> f. \<not> P (nP e1) (nP e2)" by fast
    from this a_refl show "\<forall>(e1,e2) \<in> f. e1 \<noteq> e2" by fast
  qed
  
  (* declare	[[show_types]] *)
  lemma (in NetworkModel_withOffendingFlows) ENF_default_update_fst: 
  fixes "default_node_properties" :: "'a" ("\<bottom>")
  assumes modelInv: "\<not> eval_model G nP"
    and   ENFdef: "eval_model_all_edges_normal_form P"
    and   secdef: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P \<bottom> (nP e2))"
  shows
    "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) (nP e2))"
  proof -
    from ENFdef have ENF: "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2)\<in> edges G. P (nP e1) (nP e2))" 
      using eval_model_all_edges_normal_form_def by simp
    from modelInv ENF have modelInv': "\<not> (\<forall> (e1, e2)\<in> edges G. P (nP e1) (nP e2))" by simp
    from this secdef have modelInv'': "\<not> (\<forall> (e1, e2)\<in> edges G. P \<bottom> (nP e2))" by blast
      have simpUpdateI: "\<And> e1 e2. \<not> P (nP e1) (nP e2) \<Longrightarrow> \<not> P \<bottom> (nP e2) \<Longrightarrow> \<not> P ((nP(i := \<bottom>)) e1) (nP e2)" by simp
      hence "\<And> X. \<exists>(e1,e2) \<in> X. \<not> P (nP e1) (nP e2) \<Longrightarrow> \<exists>(e1,e2) \<in> X.\<not> P \<bottom> (nP e2) \<Longrightarrow> \<exists>(e1,e2) \<in> X.\<not> P ((nP(i := \<bottom>)) e1) (nP e2)" 
        using secdef by blast
    from this modelInv' modelInv'' show "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) (nP e2))" by blast
  qed

  
  lemma (in NetworkModel_withOffendingFlows) 
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    shows "\<not> eval_model G nP \<Longrightarrow> eval_model_all_edges_normal_form P \<Longrightarrow>
    (\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow>  \<not> (P \<bottom> (nP e2))) \<Longrightarrow>
    (\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P (nP e1) \<bottom>)) \<Longrightarrow>
    (\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> P \<bottom> \<bottom>)
    \<Longrightarrow> \<not> eval_model G (nP(i := \<bottom>))"
  proof -
    assume a1: "\<not> eval_model G nP"
    and   a2d: "eval_model_all_edges_normal_form P"
    and    a3: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P \<bottom> (nP e2))"
    and    a4: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P (nP e1) \<bottom>)"
    and    a5: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> P \<bottom> \<bottom>"
  
    from a2d have a2: "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2) \<in> edges G. P (nP e1) (nP e2))" 
      using eval_model_all_edges_normal_form_def by simp
  
    from ENF_default_update_fst[OF a1 a2d] a3 have subgoal1: "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) (nP e2))" by blast
    (*next asm*)
    
    let ?nP' = "(nP(i := \<bottom>))"
  
    from subgoal1 have "\<exists> (e1, e2) \<in> edges G. \<not> P (?nP' e1) (nP e2)" by blast
    from this obtain e11 e21 where s1cond: "(e11, e21) \<in> edges G \<and> \<not> P (?nP' e11) (nP e21)" by blast
  
    from s1cond have "i \<noteq> e11 \<Longrightarrow> \<not> P (nP e11) (nP e21)" by simp
    from s1cond have "e11 \<noteq> e21 \<Longrightarrow> \<not> P (?nP' e11) (?nP' e21)"
      apply simp
      apply(rule conjI)
       apply blast
      apply(insert a4)
      by force
    from s1cond a4 fun_upd_apply have ex1: "e11 \<noteq> e21 \<Longrightarrow> \<not> P (?nP' e11) (?nP' e21)" by metis
    from s1cond a5 have ex2: "e11 = e21 \<Longrightarrow> \<not> P (?nP' e11) (?nP' e21)" by auto
  
    from ex1 ex2 s1cond have "\<exists> (e1, e2) \<in> edges G. \<not> P (?nP' e1) (?nP' e2)" by blast
    hence "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) ((nP(i := \<bottom>)) e2))" by fast
    from this a2 show "\<not> eval_model G (nP(i := \<bottom>))" by presburger
  qed
  
  (* fsts version *)
  lemma (in NetworkModel_withOffendingFlows)  ENF_fsts_refl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf_refl: "ENF_refl P"
    and   a3: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P \<bottom> (nP e2))" (*changed \<And> to \<forall>*)
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_fsts: "i \<in> fst ` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from a_offending have a_not_eval: "\<not> eval_model G nP" by (metis equals0D validmodel_imp_no_offending)
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .

    from a_enf_refl have a_enf: "eval_model_all_edges_normal_form P" using ENF_refl_def by simp
    hence a2: "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2) \<in> edges G. P (nP e1) (nP e2))" using eval_model_all_edges_normal_form_def by simp
  
    from ENF_offending_members[OF a_not_eval a_enf a_offending] have a_f_3_in_f: "\<And> e1 e2. (e1, e2) \<in> f \<Longrightarrow> \<not> P (nP e1) (nP e2)" by fast
  
    let ?nP' = "(nP(i := \<bottom>))"
  
    (* obain from f *)
    from offending_not_empty[OF a_offending] ENF_offending_members[OF a_not_eval a_enf a_offending] a_i_fsts hd_in_set
      obtain e1 e2 where e1e2cond: "(e1, e2) \<in> f \<and> e1 = i" by force
  
    from conjunct1[OF e1e2cond] a_f_3_in_f have e1e2notP: "\<not> P (nP e1) (nP e2)" by simp
    from this a3 have "\<not> P \<bottom> (nP e2)" by simp
    from this e1e2notP have e1e2subgoal1: "\<not> P (?nP' e1) (nP e2)" by simp
  
    from ENF_refl_not_offedning[OF a_not_eval a_offending a_enf_refl] conjunct1[OF e1e2cond] have ENF_refl: "e1 \<noteq> e2" by fast
  
    from e1e2subgoal1 have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) (?nP' e2)"
      apply simp
      apply(rule conjI)
       apply blast
      apply(insert conjunct2[OF e1e2cond])
      by simp
  
    from this ENF_refl ENF_offending_members[OF a_not_eval a_enf a_offending]  conjunct1[OF e1e2cond] have 
      "\<exists> (e1, e2) \<in> edges G. \<not> P (?nP' e1) (?nP' e2)" by blast
    hence "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) ((nP(i := \<bottom>)) e2))" by fast
    from this a2 show "\<not> eval_model G (nP(i := \<bottom>))" by presburger
  qed

  (* snds version *)
  lemma (in NetworkModel_withOffendingFlows)  ENF_snds_refl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf_refl: "ENF_refl P"
    and   a3: "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P (nP e1) \<bottom>)"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_snds: "i \<in> snd ` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from a_offending have a_not_eval: "\<not> eval_model G nP" by (metis equals0D validmodel_imp_no_offending)
    from valid_without_offending_flows[OF a_offending] have a_offending_rm: "eval_model (delete_edges G f) nP" .
    from a_enf_refl have a_enf: "eval_model_all_edges_normal_form P" using ENF_refl_def by simp
    hence a2: "\<And> G nP. eval_model G nP  = (\<forall> (e1, e2) \<in> edges G. P (nP e1) (nP e2))" using eval_model_all_edges_normal_form_def by simp
  
    from ENF_offending_members[OF a_not_eval a_enf a_offending] have a_f_3_in_f: "\<And> e1 e2. (e1, e2) \<in> f \<Longrightarrow> \<not> P (nP e1) (nP e2)" by fast
  
    let ?nP' = "(nP(i := \<bottom>))"
  
    (* obain from f *)
    from offending_not_empty[OF a_offending] ENF_offending_members[OF a_not_eval a_enf a_offending] a_i_snds hd_in_set
      obtain e1 e2 where e1e2cond: "(e1, e2) \<in> f \<and> e2 = i" by force
  
    from conjunct1[OF e1e2cond] a_f_3_in_f have e1e2notP: "\<not> P (nP e1) (nP e2)" by simp
    from this a3 have "\<not> P (nP e1) \<bottom>" by auto
    from this e1e2notP have e1e2subgoal1: "\<not> P (nP e1) (?nP' e2)" by simp
  
    from ENF_refl_not_offedning[OF a_not_eval a_offending a_enf_refl] e1e2cond have ENF_refl: "e1 \<noteq> e2" by fast
  
    from e1e2subgoal1 have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) (?nP' e2)"
      apply simp
      apply(rule conjI)
       apply(insert conjunct2[OF e1e2cond])
       by simp_all
  
    from this ENF_refl e1e2cond ENF_offending_members[OF a_not_eval a_enf a_offending]  conjunct1[OF e1e2cond] have 
      "\<exists> (e1, e2) \<in> edges G. \<not> P (?nP' e1) (?nP' e2)" by blast
    hence "\<not> (\<forall> (e1, e2) \<in> edges G. P ((nP(i := \<bottom>)) e1) ((nP(i := \<bottom>)) e2))" by fast
    from this a2 show "\<not> eval_model G (nP(i := \<bottom>))" by presburger
  qed



end
