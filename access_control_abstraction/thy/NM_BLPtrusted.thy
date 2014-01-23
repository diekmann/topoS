theory NM_BLPtrusted
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* Basic Bell LePadula NetworkModel with trusted entities *}

type_synonym privacy_level = nat

record node_config = 
    privacy_level::privacy_level
    trusted::bool

definition default_node_properties :: "node_config"
  where  "default_node_properties \<equiv> \<lparr> privacy_level = 0, trusted = False \<rparr>"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow>  bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. (if trusted (nP e2) then True else privacy_level (nP e1) \<le> privacy_level (nP e2) ))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus \<equiv> True"


lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
  apply(simp only: NetworkModel_withOffendingFlows.eval_model_mono_def)
  apply(clarify)
  apply(simp split: split_split split_split_asm)
  by auto


interpretation NetworkModel_preliminaries
where eval_model = eval_model
and verify_globals = verify_globals
  apply unfold_locales
  apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
  apply(erule_tac exE)
  apply(rename_tac list_edges)
  apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
   apply(auto split: split_split split_split_asm)[6]
  apply(simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops split: split_split split_split_asm)[1]
   apply (metis prod.inject)
  apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
done

lemma BLP_def_unique: "otherbot \<noteq> default_node_properties \<Longrightarrow>
    \<exists>G p i f. valid_graph G \<and> \<not> eval_model G p \<and> f \<in> (NetworkModel_withOffendingFlows.set_offending_flows eval_model G p) \<and>
       eval_model (delete_edges G f) p \<and> 
        (\<not> True \<longrightarrow> i \<in> fst ` f \<and> eval_model G (p(i := otherbot))) \<and>
        (True \<longrightarrow> i \<in> snd ` f \<and> eval_model G (p(i := otherbot))) "
  apply(simp add:default_node_properties_def)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes={vertex_1, vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
  apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := \<lparr>privacy_level = 1, trusted = False \<rparr>, vertex_2 := \<lparr>privacy_level = 0, trusted = False \<rparr>)" in exI, simp add:default_node_properties_def)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(case_tac otherbot)
  apply simp
  apply(erule disjE)
   apply force
   apply fast
  done



section {*ENF*}
  definition BLP_P where "BLP_P \<equiv> (\<lambda>n1 n2.(if trusted n2 then True else privacy_level n1 \<le> privacy_level n2 ))"
  lemma zero_default_candidate: "\<forall>nP e1 e2. \<not> BLP_P (nP e1) (nP e2) \<longrightarrow> \<not> BLP_P (nP e1) default_node_properties"
    apply(rule allI)+
    apply(case_tac "nP e1")
    apply(case_tac "nP e2")
    apply(rename_tac privacy2 trusted2 more2)
    apply (simp add: BLP_P_def default_node_properties_def)
    done
  lemma privacylevel_refl: "BLP_P e e"
    by(simp_all add: BLP_P_def)
  lemma BLP_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model BLP_P"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    unfolding BLP_P_def
    by simp
  lemma BLP_ENF_refl: "NetworkModel_withOffendingFlows.ENF_refl eval_model BLP_P"
    unfolding NetworkModel_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
     apply(simp add: privacylevel_refl)
  done


  definition BLP_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "BLP_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> BLP_P (nP e1) (nP e2)} })"
  lemma BLP_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = BLP_offending_set"
    apply(simp only: fun_eq_iff NetworkModel_withOffendingFlows.ENF_offending_set[OF BLP_ENF] BLP_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done
   

interpretation BLPtrusted: NetworkModel
  where default_node_properties = default_node_properties
  and eval_model = eval_model
  and verify_globals = verify_globals
  and target_focus = target_focus
  where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = BLP_offending_set"
    unfolding target_focus_def
    apply unfold_locales
    (* only remove target_focus: *)
    apply(rule conjI) prefer 1 apply(simp) apply(simp only:HOL.not_False_eq_True HOL.simp_thms(15)) apply(rule impI)
     apply (drule NetworkModel_withOffendingFlows.ENF_snds_refl_instance[OF _ BLP_ENF_refl zero_default_candidate],simp_all)[1]

    apply(unfold default_node_properties_def)
     apply(blast intro: BLP_def_unique[simplified default_node_properties_def])

     apply(fact BLP_offending_set)
    done

   
 
hide_type (open) node_config
hide_const (open) eval_model_mono
hide_const (open) BLP_P
hide_const (open) eval_model verify_globals target_focus default_node_properties

end
