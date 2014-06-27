theory NM_ACLnotCommunicateWith
imports "../NetworkModel_Helper"
begin

section {* NetworkModel *}
text{*An access control list strategy that says that hosts must not transitively access each other*}

text{* node properties: a set of hosts this host must no access *}

definition default_node_properties :: "'v set"
  where  "default_node_properties \<equiv> UNIV"


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v set) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> v \<in> nodes G. \<forall> a \<in> (succ_tran G v). a \<notin> (nP v))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v set) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where 
  "target_focus \<equiv> False"


lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
  apply(simp only: NetworkModel_withOffendingFlows.eval_model_mono_def)
  apply(rule)+
  apply(clarify)
  proof -
    fix nP::"('v \<Rightarrow> 'v set)" and N E' E
    assume a1: "valid_graph \<lparr>nodes = N, edges = E\<rparr>"
    and    a2: "E' \<subseteq> E"
    and    a3: "eval_model \<lparr>nodes = N, edges = E\<rparr> nP"

    from a3 have "\<And>v a. v \<in> N \<Longrightarrow>  a \<in> (succ_tran \<lparr>nodes = N, edges = E\<rparr> v) \<Longrightarrow> a \<notin> (nP v)" by fastforce
    from this a2 have g1: "\<And>v a. v \<in> N \<Longrightarrow> a \<in> (succ_tran \<lparr>nodes = N, edges = E'\<rparr> v) \<Longrightarrow> a \<notin> (nP v)" 
      using succ_tran_mono[OF a1] by blast

    thus "eval_model \<lparr>nodes = N, edges = E'\<rparr> nP"
      by(clarsimp)
qed
  

lemma False_set: "{(e1, e2). False} = {}" by blast
lemma succ_tran_empty: "(succ_tran \<lparr>nodes = nodes G, edges = {}\<rparr> v) = {}"
  by(simp add: succ_tran_def)

interpretation NetworkModel_preliminaries
where eval_model = eval_model
and verify_globals = verify_globals
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
        apply(auto)[5]
    apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops False_set succ_tran_empty)[1]
   apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_eval_model_mono[OF eval_model_mono])
  apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
 done


lemma unique_default_example: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_2 = {}"
apply (simp add: succ_tran_def)
by (metis Domain.DomainI Domain_empty Domain_insert distince_vertices12 singleton_iff trancl_domain)

interpretation ACLnotCommunicateWith: NetworkModel_ACS
where default_node_properties = NM_ACLnotCommunicateWith.default_node_properties
and eval_model = NM_ACLnotCommunicateWith.eval_model
and verify_globals = verify_globals
  unfolding NM_ACLnotCommunicateWith.default_node_properties_def
  apply unfold_locales
 
   apply simp
   apply(subst(asm) NetworkModel_withOffendingFlows.set_offending_flows_simp, simp)
   apply(clarsimp)
   apply (metis)

  apply(erule default_uniqueness_by_counterexample_ACS)
  apply(simp)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(case_tac "otherbot = {}")

   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(rule_tac x="(\<lambda> x. UNIV)(vertex_1 := {vertex_2}, vertex_2 := {})" in exI, simp)
   apply(simp add: example_simps)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(simp add: example_simps)

  apply(subgoal_tac "\<exists>canAccess. canAccess \<in> UNIV \<and> canAccess \<notin> otherbot")
   prefer 2
   apply blast
  apply(erule exE)
  apply(rename_tac canAccessThis)
  apply(case_tac "vertex_1 \<noteq> canAccessThis")

   apply(rule_tac x="\<lparr> nodes={vertex_1,canAccessThis}, edges = {(vertex_1,canAccessThis)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(rule_tac x="(\<lambda> x. UNIV)(vertex_1 := UNIV, canAccessThis := {})" in exI, simp)
   apply(simp add: example_simps)
   apply(rule_tac x="{(vertex_1,canAccessThis)}" in exI, simp)
   apply(simp add: example_simps)

  apply(rule_tac x="\<lparr> nodes={canAccessThis,vertex_2}, edges = {(vertex_2,canAccessThis)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. UNIV)(vertex_2 := UNIV, canAccessThis := {})" in exI, simp)
  apply(simp add: example_simps)
  apply(rule_tac x="{(vertex_2,canAccessThis)}" in exI, simp)
  apply(simp add: example_simps)
 done

  lemma NetworkModel_ACLnotCommunicateWith: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales  

hide_const (open) eval_model verify_globals target_focus default_node_properties

end
