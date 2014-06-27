theory NM_BLPbasic
imports "../NetworkModel_Helper"
begin

section {* Basic Bell LePadula NetworkModel *}

type_synonym privacy_level = nat

definition default_node_properties :: "privacy_level"
  where  "default_node_properties \<equiv> 0"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. (nP e1) \<le> (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus \<equiv> True"


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


lemma BLP_def_unique: "otherbot \<noteq> 0 \<Longrightarrow>
    \<exists>G p i f. valid_graph G \<and> \<not> eval_model G p \<and> f \<in> (NetworkModel_withOffendingFlows.set_offending_flows eval_model G p) \<and>
       eval_model (delete_edges G f) p \<and>
        i \<in> snd ` f \<and> eval_model G (p(i := otherbot)) "
  apply(simp)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. 0)(vertex_1 := 1, vertex_2 := 0)" in exI, simp)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
  done


(*Test instantiation without any fancy lemmata*)
(*
interpretation NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus
  unfolding default_node_properties_def
  unfolding target_focus_def
  apply unfold_locales
  
  apply(simp)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(auto intro!:bexI)[1]
   (*apply (smt image_iff offending_in_edges pair_collapse)*)
  apply(blast intro: BLP_def_unique)
done
*)
 

section {*ENF*}
  lemma zero_default_candidate: "\<And> nP e1 e2. \<not> (op \<le>::privacy_level \<Rightarrow> privacy_level \<Rightarrow> bool) (nP e1) (nP e2) \<Longrightarrow> \<not> (op \<le>) (nP e1) 0"
    by simp_all
  lemma zero_default_candidate_rule: "\<And> (nP::('v \<Rightarrow> privacy_level)) e1 e2. \<not> (nP e1) \<le> (nP e2) \<Longrightarrow> \<not> (nP e1) \<le> 0"
    by simp_all
  lemma privacylevel_refl: "(op \<le>::privacy_level \<Rightarrow> privacy_level \<Rightarrow> bool) e e"
    by(simp_all)
  lemma BLP_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model (op \<le>)"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    by simp
  lemma BLP_ENF_refl: "NetworkModel_withOffendingFlows.ENF_refl eval_model (op \<le>)"
    unfolding NetworkModel_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
    apply(simp add: privacylevel_refl)
  done

  definition BLP_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> ('v \<times> 'v) set set" where
  "BLP_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)} })"
  lemma BLP_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = BLP_offending_set"
    apply(simp only: fun_eq_iff NetworkModel_withOffendingFlows.ENF_offending_set[OF BLP_ENF] BLP_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done
   

  interpretation BLPbasic: NetworkModel_IFS eval_model verify_globals default_node_properties
  where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = BLP_offending_set"
    unfolding target_focus_def
    unfolding default_node_properties_def
    apply(unfold_locales)
      apply(rule ballI)
      apply(rule NetworkModel_withOffendingFlows.ENF_snds_refl_instance[OF BLP_ENF_refl])
         apply(simp_all add: BLP_ENF BLP_ENF_refl)[3]
     apply(erule default_uniqueness_by_counterexample_IFS)
     apply(fact BLP_def_unique)
    apply(fact BLP_offending_set)
   done


  lemma NetworkModel_BLPBasic: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales
   
hide_fact (open) eval_model_mono   

hide_const (open) eval_model verify_globals target_focus default_node_properties

end
