theory NM_Dependability
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel *}


type_synonym dependability_level = nat

definition default_node_properties :: "dependability_level"
  where  "default_node_properties \<equiv> 0"

text {* Less-equal other nodes depend on the output of a node than its dependability level. *}
fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. (num_reachable G e1) \<le> (nP e1))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where 
  "target_focus \<equiv> False"


text{* It does not matter whether we iterate over all edges or all nodes. We chose all edges because it is in line with the other models.  *}
  fun eval_model_nodes :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
    "eval_model_nodes G nP = (\<forall> v \<in> nodes G. (num_reachable G v) \<le> (nP v))"
  
  theorem eval_model_edges_nodes_iff: "valid_graph G \<Longrightarrow> 
    eval_model_nodes G nP = eval_model G nP"
  proof(unfold eval_model_nodes.simps eval_model.simps, rule iffI)
    assume a1: "valid_graph G"
      and  a2: "\<forall>v\<in>nodes G. num_reachable G v \<le> nP v"

      from a1[simplified valid_graph_def] have f1: "fst ` edges G \<subseteq> nodes G" by simp
      from f1 a2 have "\<forall>v \<in> (fst ` edges G). num_reachable G v \<le> nP v" by auto

      thus "\<forall>(e1, _) \<in> edges G. num_reachable G e1 \<le> nP e1" by auto
    next
    assume a1: "valid_graph G"
      and  a2: "\<forall>(e1, _)\<in>edges G. num_reachable G e1 \<le> nP e1"

      from a2 have g1: "\<forall> v \<in> (fst ` edges G). num_reachable G v \<le> nP v" by auto

      from succ_tran_empty[OF a1] num_reachable_zero_iff[OF a1, symmetric]
      have g2: "\<forall> v. v \<notin> (fst ` edges G) \<longrightarrow> num_reachable G v \<le> nP v" by auto

      from g1 g2 show "\<forall>v\<in>nodes G. num_reachable G v \<le> nP v" by metis
  qed




  lemma num_reachable_le_nodes: "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow> num_reachable G v \<le> card (nodes G)"
    apply(simp add: num_reachable_def)
    using succ_tran_subseteq_nodes card_seteq  nat_le_linear valid_graph.finiteV by metis


  text{* nP is valid if all dependability level are greater equal the total number of nodes in the graph *}
  lemma "\<lbrakk> valid_graph G; \<forall>v \<in> nodes G. nP v \<ge> card (nodes G) \<rbrakk> \<Longrightarrow> eval_model G nP"
    apply(subst eval_model_edges_nodes_iff[symmetric], simp)
    apply(simp add:)
    using num_reachable_le_nodes by (metis le_trans)



  text{* Generate a valid configuration to start from: *}
   text{* Takes arbitrary configuration, returns a valid one *}
   fun fix_nP :: "'v graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<Rightarrow> dependability_level)" where
      "fix_nP G nP = (\<lambda>v. if num_reachable G v \<le> (nP v) then (nP v) else num_reachable G v)"
  
   text{* @{term fix_nP} always gives you a valid solution *}
   lemma fix_nP_valid: "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow> eval_model G (fix_nP G nP)"
      by(subst eval_model_edges_nodes_iff[symmetric], simp_all)
  
   text{* furthermore, it gives you a minimal solution, i.e. if someone supplies a configuration with a value lower than
          calculated by fix_nP, this is invalid! *}
   lemma fix_nP_minimal_solution: "\<lbrakk> valid_graph G; \<exists> v \<in> nodes G. (nP v) < (fix_nP G (\<lambda>_. 0)) v \<rbrakk> \<Longrightarrow> \<not> eval_model G nP"
      apply(subst eval_model_edges_nodes_iff[symmetric], simp)
      apply(simp)
      apply(clarify)
      apply(rule_tac x="v" in bexI)
       apply(simp_all)
      done




lemma unique_default_example: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
apply (simp add: succ_tran_def)
by (metis (lifting, no_types) Collect_cong Range.intros Range_empty Range_insert mem_Collect_eq singleton_conv singleton_iff trancl.r_into_trancl trancl_range)
lemma unique_default_example_simp1: "{(e1, e2). e1 = vertex_1 \<and> e2 = vertex_2 \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> vertex_2)} = {}" by blast
lemma unique_default_example_simp2: "{(vertex_1, vertex_2)}\<^sup>+ = {(vertex_1, vertex_2)}"
  apply(rule)
   apply(rule)
   apply(clarify)
   apply(rule_tac P="\<lambda> a b. a = vertex_1 \<and> b = vertex_2" in trancl.induct)
     apply auto
 done


(*
lemma card_less_equal_trancl: "finite A \<Longrightarrow> card {e2. (aa, e2) \<in> (A - X)\<^sup>+} \<le> card {e2. (aa, e2) \<in> (A)\<^sup>+}"
apply(subgoal_tac "{e2. (aa, e2) \<in> (A - X)\<^sup>+} \<subseteq> {e2. (aa, e2) \<in> (A)\<^sup>+}")
apply(rule card_mono)
defer
apply(simp)
apply (metis (lifting) Collect_mono Diff_subset trancl_mono)
by (metis (lifting) Range_iff finite_Range mem_Collect_eq rev_finite_subset subsetI trancl_range)
*)


lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
  apply(rule_tac NetworkModel_withOffendingFlows.eval_model_mono_I_proofrule)
   apply(auto)
  apply(rename_tac nP e1 e2 N E' e1' e2' E)
  apply(drule_tac E'="E'" and v="e1'" in num_reachable_mono)
   apply simp
  apply(subgoal_tac "(e1', e2') \<in> E")
   apply(force)
  apply(blast)
 done
  

interpretation NetworkModel_preliminaries
where eval_model = eval_model
and verify_globals = verify_globals
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
        apply(auto)[5]
   apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops)[1]
  apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_eval_model_mono[OF eval_model_mono])
 apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
done


interpretation Dependability: NetworkModel_ACS
where default_node_properties = NM_Dependability.default_node_properties
and eval_model = NM_Dependability.eval_model
and verify_globals = verify_globals
  unfolding target_focus_def
  unfolding NM_Dependability.default_node_properties_def
  apply unfold_locales
   apply simp
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
    NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
    NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply (simp add:graph_ops)
   apply(clarify)
   apply (metis gr0I le0)
  apply(erule default_uniqueness_by_counterexample_ACS)
  apply(simp)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. 0)(vertex_1 := 0, vertex_2 := 0)" in exI, simp)
  apply(rule conjI)
   apply(simp add: unique_default_example num_reachable_def)
  apply(rule_tac x="vertex_1" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(simp add: unique_default_example num_reachable_def)
  apply(simp add: succ_tran_def unique_default_example_simp1 unique_default_example_simp2)
  done

  lemma NetworkModel_Dependability: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales  

hide_const (open) eval_model verify_globals target_focus default_node_properties

end
