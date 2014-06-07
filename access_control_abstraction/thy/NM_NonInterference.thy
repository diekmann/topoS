theory NM_NonInterference
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel NonInterference *}

datatype node_config = Interfering | Unrelated

definition default_node_properties :: "node_config"
  where  "default_node_properties = Interfering"

definition undirected_reachable :: "'v graph \<Rightarrow> 'v => 'v set" where
  "undirected_reachable G v = (succ_tran (undirected G) v) - {v}"


lemma undirected_reachable_mono:
  "\<lbrakk>E' \<subseteq> E \<rbrakk> \<Longrightarrow>
    (undirected_reachable \<lparr>nodes = N, edges = E'\<rparr> n) \<subseteq> (undirected_reachable \<lparr>nodes = N, edges = E\<rparr> n)"
  proof(simp add: undirected_reachable_def undirected_def succ_tran_def)
  assume m: "E' \<subseteq> E"
  have subsetminusmono: "\<And> A B D. A \<subseteq> B \<Longrightarrow> A - D \<subseteq> B - D" by fast
  have set2subseteq: "\<And> A B. A \<subseteq> B \<Longrightarrow> {e2. (n, e2) \<in> A} \<subseteq> {e2. (n, e2) \<in> B}" by fast
  have trancl_mono: "\<And> A B. A \<subseteq> B \<Longrightarrow> A^+ \<subseteq> B^+" by (metis subsetI trancl_mono)  

  show "{e2. (n, e2) \<in> (E' \<union> {(b, a). (a, b) \<in> E'})\<^sup>+} - {n} \<subseteq> {e2. (n, e2) \<in> (E \<union> {(b, a). (a, b) \<in> E})\<^sup>+} - {n}"
   apply(rule subsetminusmono)
   apply(rule set2subseteq)
   apply(rule trancl_mono)
   apply(rule Set.Un_mono)
    apply(fact m)
   using m apply(blast)
   done
  qed
  

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> n \<in> (nodes G). (nP n) = Interfering \<longrightarrow> (nP ` (undirected_reachable G n)) \<subseteq> {Unrelated})"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where 
  "target_focus = True"


text{*simplifications for sets we need in the uniqueness proof*}
  lemma tmp1: "{(b, a). a = vertex_1 \<and> b = vertex_2} = {(vertex_2, vertex_1)}" by auto
  lemma tmp6: "{(vertex_1, vertex_2), (vertex_2, vertex_1)}\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(rule)
     apply(rule)
     apply(case_tac x, simp)
     apply(erule_tac r="{(vertex_1, vertex_2), (vertex_2, vertex_1)}" in trancl_induct)
      apply(auto)
     apply (metis (mono_tags) insertCI r_r_into_trancl)+
  done
  lemma tmp2: "(insert (vertex_1, vertex_2) {(b, a). a = vertex_1 \<and> b = vertex_2})\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(subst tmp1)
    apply(fact tmp6)
    done
  lemma tmp3: "{(b, a). False} = {}" by simp
  lemma tmp4: "{(e1, e2). e1 = vertex_1 \<and> e2 = vertex_2 \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> vertex_2)} = {}" by blast
  lemma tmp5: "{(b, a). a = vertex_1 \<and> b = vertex_2 \<or> a = vertex_1 \<and> b = vertex_2 \<and> (a = vertex_1 \<longrightarrow> b \<noteq> vertex_2)} = 
    {(vertex_2, vertex_1)}" by fastforce
  lemma unique_default_example: "undirected_reachable \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
    by(auto simp add: undirected_def undirected_reachable_def succ_tran_def tmp2)
  lemma unique_default_example_hlp1: "delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)} = 
    \<lparr>nodes = {vertex_1, vertex_2}, edges = {}\<rparr>"
    by(simp add: delete_edges_def)
  lemma unique_default_example_2: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_1 = {}"
    apply(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
    apply(subst tmp3)
    by auto
  lemma unique_default_example_3: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_2 = {}"
    apply(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
    apply(subst tmp3)
    by auto
  lemma unique_default_example_4: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_1) = {vertex_2}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force
  lemma unique_default_example_5: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_2) = {vertex_1}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force


  lemma empty_undirected_reachable_false: "xb \<in> undirected_reachable \<lparr>nodes = nodes G, edges = {(e1, e2). False}\<rparr> na \<longleftrightarrow> False"
    apply(simp add: undirected_reachable_def succ_tran_def undirected_def)
    apply(subst tmp3)
    by fastforce

section{*monotonic and preliminaries*}
  lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
    apply(simp add: NetworkModel_withOffendingFlows.eval_model_mono_def)
    apply(clarsimp)
    apply(rename_tac nP N E' n E xa)
    apply(erule_tac x=n in ballE)
     prefer 2
     apply simp
    apply(simp)
    apply(drule_tac N=N and n=n in undirected_reachable_mono)
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
      apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops empty_undirected_reachable_false)[1]
     apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_eval_model_mono[OF eval_model_mono])
    apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
  done


interpretation NonInterference: NetworkModel
where default_node_properties = NM_NonInterference.default_node_properties
and eval_model = NM_NonInterference.eval_model
and verify_globals = verify_globals
and target_focus = NM_NonInterference.target_focus
  unfolding target_focus_def
  unfolding NM_NonInterference.default_node_properties_def
  apply unfold_locales

    (* only remove target_focus: *)
    apply(rule conjI) prefer 1 apply(simp) apply(simp only:HOL.not_False_eq_True HOL.simp_thms(15)) apply(rule impI)

    apply simp
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
    NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
    NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply(simp add: undirected_reachable_def succ_tran_def undirected_def graph_ops)
   apply clarify
   apply simp_all
   apply(rename_tac xa)
   apply(case_tac "nP xa")
    (*case Interfering*)
    apply simp

  (*apply(erule_tac x=n and A="nodes G" in ballE)
  prefer 2
  apply fast
  apply(simp)
  apply(erule_tac x=n and A="nodes G" in ballE)
  prefer 2
  apply fast
  sledgehammer (*now finds something*)
  (*apply (smt DiffI fun_upd_image fun_upd_triv insert_subset mem_Collect_eq node_config.distinct(1) singleton_iff)*)
  (*apply (smt DiffI fun_upd_image fun_upd_triv insert_subset mem_Collect_eq node_config.distinct(1) singleton_iff)*)
  *)

  (*wow, sledgehammer can find it no more!!*)
  (*reproduce: using DiffI empty_iff fun_upd_image fun_upd_triv insert_iff insert_subset mem_Collect_eq node_config.simps(1)
  sledgehammer[provers=z3,verbose=true]*)
  (*isabelle 2013: using DiffI empty_iff fun_upd_image fun_upd_triv insert_iff insert_subset mem_Collect_eq node_config.simps(1)
  using singleton_conv2 sledgehammer[provers=z3,verbose=true,isar_proofs,timeout=60]
  apply (smt singleton_conv2)*)
   (*isabelle 2012: apply (smt Diff_iff empty_iff fun_upd_image fun_upd_triv insert_iff insert_subset mem_Collect_eq node_config.simps(1))*)
   (*isabelle 2013: apply (smt DiffI empty_iff fun_upd_image fun_upd_triv insert_iff insert_subset mem_Collect_eq node_config.simps(1))*)
    apply (smt DiffI empty_iff fun_upd_image fun_upd_triv insert_iff insert_subset mem_Collect_eq node_config.simps(1))
(*case Unrelated*)
   apply simp

  (*unique: *)
  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:delete_edges_set_nodes)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := Interfering, vertex_2 := Interfering)" in exI, simp)
  apply(rule conjI)
   apply(simp add: unique_default_example)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(simp add: unique_default_example)
  apply(simp add: unique_default_example_2)
  apply(simp add: unique_default_example_3)
  apply(simp add: unique_default_example_4)
  apply(simp add: unique_default_example_5)
  apply(case_tac otherbot)
   apply simp
  apply(simp add:graph_ops)
  done


  lemma "NetworkModel eval_model default_node_properties target_focus"
  by unfold_locales
   

hide_const (open) eval_model verify_globals target_focus default_node_properties

end
