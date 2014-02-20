theory Scratch
imports Main
"../thy_lib/FiniteGraph"
"../thy_lib/isabelle_afp/Graph_Theory/Pair_Digraph"
begin


definition graph_to_afp_graph :: "'v graph \<Rightarrow> 'v pair_pre_digraph" where
  "graph_to_afp_graph G \<equiv> \<lparr> pverts = nodes G, parcs = edges G \<rparr>"

lemma "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow> pair_wf_digraph (graph_to_afp_graph G)"
  apply(unfold_locales)
  by(auto simp add: valid_graph_def graph_to_afp_graph_def)

lemma "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow> pair_fin_digraph (graph_to_afp_graph G)"
  apply(unfold_locales)
  by(auto simp add: valid_graph_def graph_to_afp_graph_def)

lemma "with_proj (graph_to_afp_graph G) =  \<lparr> verts = nodes G, arcs = edges G, tail = fst, head = snd \<rparr>"
  by(simp add: graph_to_afp_graph_def)

definition "has_directed_cycle" :: "'v graph \<Rightarrow> ('v \<times> 'v) awalk \<Rightarrow> bool" where
  "has_directed_cycle G p \<equiv> pre_digraph.cycle (with_proj (graph_to_afp_graph G)) p"

lemma fixes G::"'v graph" and Gafp::"('v, 'v \<times> 'v) pre_digraph"
  assumes transl: "Gafp = with_proj (graph_to_afp_graph G)"
  shows "has_directed_cycle G p = (\<exists>u. pre_digraph.awalk Gafp u p u \<and> distinct (tl (pre_digraph.awalk_verts Gafp u p)) \<and> p \<noteq> [])"
  by(simp add: has_directed_cycle_def pre_digraph.cycle_def transl)


definition acyclic :: "('v, 'v \<times> 'v) pre_digraph \<Rightarrow> bool" where
  "acyclic G \<equiv> \<forall> u p v. pre_digraph.awalk G u p v \<longrightarrow> \<not> pre_digraph.cycle G p"

lemma acyclic_alt: "wf_digraph G \<Longrightarrow> acyclic G = (\<forall> u \<in> verts G. \<forall> v \<in> verts G. \<forall> p. pre_digraph.awalk G u p v \<longrightarrow> \<not> pre_digraph.cycle G p)"
  apply(simp add: acyclic_def wf_digraph_def)
  by (metis (full_types) pre_digraph.awalk_def pre_digraph.cycle_def)

lemma "\<not> acyclic \<lparr> pverts = {1::nat}, parcs = {(1,1)} \<rparr>"
  apply(simp add: acyclic_def with_proj_def)
  apply(rule_tac x="1" in exI)
  apply(rule_tac x="[(1,1)]" in exI)
  apply(rule conjI)
  apply(rule_tac x="1" in exI)
  apply(simp add: pre_digraph.awalk_def)
  apply(simp add: pre_digraph.cas.simps)
  apply(simp add: pre_digraph.cycle_def)
  apply(simp add: pre_digraph.awalk_def)
  apply(simp add: pre_digraph.cas.simps)
  apply(simp add: pre_digraph.awalk_verts.simps)
  done
lemma "\<not> acyclic \<lparr> pverts = {1::nat,2,3}, parcs = {(1,2),(2,3),(3,1)} \<rparr>"
  apply(simp add: acyclic_def with_proj_def)
  apply(rule_tac x="1" in exI)
  apply(rule_tac x="[(1,2),(2,3),(3,1)]" in exI)
  apply(rule conjI)
  apply(rule_tac x="1" in exI)
  apply(simp add: pre_digraph.awalk_def)
  apply(simp add: pre_digraph.cas.simps)
  apply(simp add: pre_digraph.cycle_def)
  apply(simp add: pre_digraph.awalk_def)
  apply(simp add: pre_digraph.cas.simps)
  apply(simp add: pre_digraph.awalk_verts.simps)
  done
lemma "acyclic \<lparr> pverts = {1::nat,2,3}, parcs = {(1,2),(2,3),(1,3)} \<rparr>"
  apply(subgoal_tac "wf_digraph \<lparr> pverts = {1::nat,2,3}, parcs = {(1,2),(2,3),(1,3)} \<rparr>")
  apply(unfold_locales, auto)
  apply(simp add: acyclic_alt with_proj_def)
  apply(thin_tac "wf_digraph ?x")
  apply(auto)
  oops (*need a methot to calculate awalks*)


section{*TEST TEST TES TEST of UNIO*}
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = {2,3,4}" by eval
  lemma "(\<Union>n\<in>{1::nat, 2, 3}. {n + 1}) = {2, 3, 4}" by eval
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = set (map (\<lambda>n. n+1) [1,2,3])" by eval

(*
  locale X =
    fixes N1 N2
    assumes well_n1: "wellformed_network N1"
    assumes well_n2: "wellformed_network N2"
  begin
  end

  sublocale X \<subseteq> n1!: wellformed_network N1
    by (rule well_n1)
  sublocale X \<subseteq> n2!: wellformed_network N2
    by (rule well_n2)
  
    context X
    begin
      
    end
*)



end
