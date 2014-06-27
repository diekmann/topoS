theory NM_NonInterference
imports "../NetworkModel_Helper"
begin

section {* NetworkModel NonInterference *}

datatype node_config = Interfering | Unrelated

definition default_node_properties :: "node_config"
  where  "default_node_properties = Interfering"

definition undirected_reachable :: "'v graph \<Rightarrow> 'v => 'v set" where
  "undirected_reachable G v = (succ_tran (undirected G) v) - {v}"


lemma undirected_reachable_mono:
  "E' \<subseteq> E \<Longrightarrow> undirected_reachable \<lparr>nodes = N, edges = E'\<rparr> n \<subseteq> undirected_reachable \<lparr>nodes = N, edges = E\<rparr> n"
unfolding undirected_reachable_def undirected_def succ_tran_def
by (fastforce intro: trancl_mono)

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
  unfolding NetworkModel_withOffendingFlows.eval_model_mono_def
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


interpretation NonInterference: NetworkModel_IFS
where default_node_properties = NM_NonInterference.default_node_properties
and eval_model = NM_NonInterference.eval_model
and verify_globals = verify_globals
  unfolding NM_NonInterference.default_node_properties_def
  apply unfold_locales
   apply(rule ballI)
   apply(drule NM_NonInterference.offending_notevalD)
   apply(simp)
   apply clarify
   apply(rename_tac xa)
   apply(case_tac "nP xa")
    (*case Interfering*)
    apply simp
    apply(erule_tac x=n and A="nodes G" in ballE)
     prefer 2
     apply fast
    apply(simp)
    apply(thin_tac "valid_graph G")
    apply(thin_tac "(a,b) \<in> f")
    apply(thin_tac "n \<in> nodes G")
    apply(thin_tac "nP n = Interfering")
    apply(erule disjE)
     apply (metis fun_upd_other fun_upd_same imageI node_config.distinct(1) set_rev_mp singleton_iff)
    apply (metis fun_upd_other fun_upd_same imageI node_config.distinct(1) set_rev_mp singleton_iff)
   (*case Unrelated*)
   apply simp
  (*unique: *)
  apply(erule default_uniqueness_by_counterexample_IFS)
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


  lemma NetworkModel_NonInterference: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales
   

hide_const (open) eval_model verify_globals target_focus default_node_properties

hide_fact tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 unique_default_example 
          unique_default_example_2 unique_default_example_3 unique_default_example_4
          unique_default_example_5 empty_undirected_reachable_false

end
