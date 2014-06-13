theory NetworkModel_ENFnr
imports NetworkModel_ENFnrSR
begin


section {* edges normal form not refl ENFnr *}
  definition (in NetworkModel_withOffendingFlows) eval_model_all_edges_normal_form_not_refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
    "eval_model_all_edges_normal_form_not_refl P \<equiv> \<forall> G nP. eval_model G nP = (\<forall> (e1, e2) \<in> edges G. e1 \<noteq> e2 \<longrightarrow> P (nP e1) (nP e2))"
  

  text{* we derive everything from the ENFnrSR form *}
  lemma (in NetworkModel_withOffendingFlows) ENFnr_to_ENFnrSR: 
    "eval_model_all_edges_normal_form_not_refl P \<Longrightarrow> eval_model_all_edges_normal_form_not_refl_SR (\<lambda> v1 _ v2 _. P v1 v2)"
    by(simp add: eval_model_all_edges_normal_form_not_refl_def eval_model_all_edges_normal_form_not_refl_SR_def)

  (*TODO: most of results should be implied from previous lemma*)

section {*offending flows*}
   theorem (in NetworkModel_withOffendingFlows) ENFnr_offending_set:
    "\<lbrakk> eval_model_all_edges_normal_form_not_refl P \<rbrakk> \<Longrightarrow>
    set_offending_flows G nP = (if eval_model G nP then
      {}
     else 
      { {(e1,e2). (e1, e2) \<in> edges G \<and> e1 \<noteq> e2 \<and> \<not> P (nP e1) (nP e2)} })"
    apply(drule ENFnr_to_ENFnrSR)
    by(drule(1) ENFnrSR_offending_set)


section {* Instance helper*}
  (* fsts version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnr_fsts_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf: "eval_model_all_edges_normal_form_not_refl P"
    and   a_botdefault: "\<forall> e1 e2. e2 \<noteq> \<bottom> \<longrightarrow> \<not> P e1 e2 \<longrightarrow> \<not> P \<bottom> e2"
    and   a_alltobot: "\<forall> e1. P e1 \<bottom>"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_fsts: "i \<in> fst` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from assms show ?thesis
    apply -
    apply(drule ENFnr_to_ENFnrSR)
    apply(drule ENFnrSR_fsts_weakrefl_instance)
         by auto
  qed
  
  (* snds version *)
  lemma (in NetworkModel_withOffendingFlows)  ENFnr_snds_weakrefl_instance:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_enf: "eval_model_all_edges_normal_form_not_refl P"
    and   a_botdefault: "\<forall> e1 e2. \<not> P e1 e2 \<longrightarrow> \<not> P e1 \<bottom>"
    and   a_bottoall: "\<forall> e2. P \<bottom> e2"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_i_snds: "i \<in> snd` f"
    shows
          "\<not> eval_model G (nP(i := \<bottom>))"
  proof -
    from assms show ?thesis
    apply -
    apply(drule ENFnr_to_ENFnrSR)
    apply(drule ENFnrSR_snds_weakrefl_instance)
         by auto
  qed
 



  (* snds version DRAFT*)
  lemma (in NetworkModel_withOffendingFlows)  ENF_weakrefl_instance_FALSE:
    fixes "default_node_properties" :: "'a" ("\<bottom>")
    assumes a_validG: "valid_graph G"
    and   a_not_eval: "\<not> eval_model G nP"
    and   a_enf: "eval_model_all_edges_normal_form P"
    and   a_weakrefl: "P \<bottom> \<bottom>"
    and   a_botisolated: "\<And> e2. e2 \<noteq> \<bottom> \<Longrightarrow> \<not> P \<bottom> e2"
    and   a_botdefault: "\<And> e1 e2. e1 \<noteq> \<bottom> \<Longrightarrow> \<not> P e1 e2 \<Longrightarrow> \<not> P e1 \<bottom>"
    and   a_offending: "f \<in> set_offending_flows G nP"
    and   a_offending_rm: "eval_model (delete_edges G f) nP"
    and   a_i_fsts: "i \<in> snd` f"
    and   a_not_eval_upd: "\<not> eval_model G (nP(i := \<bottom>))"
    shows "False"
oops



end
