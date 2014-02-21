theory Scratch
imports Main
"../thy_lib/FiniteGraph"
"../thy_lib/isabelle_afp/Graph_Theory/Pair_Digraph"
"../thy_lib/Collections/Refine_Dflt"
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

hide_const(open) succ (*my succ in my graph*)

definition cycles_dfs_rec :: "('a \<Rightarrow>'a set) \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "cycles_dfs_rec succ v0 \<equiv> REC (\<lambda>D (V,v). 
    if v \<in> V then RETURN True 
    else do {
      let V=insert v V;
      FOREACH (succ v) (\<lambda>v' _. D (V,v')) False }
  ) ({},v0)"

(*TODO only acyclic in reachable from v0*)

lemma cycles_dfs_rec_sound:
  fixes succ and G
  defines "E \<equiv> {(v,v'). v'\<in>succ v}"
  assumes F: "finite {v. (v0,v)\<in>E\<^sup>*}"
  and wf_G: "wf_digraph G" and "arcs G = E"
  shows "cycles_dfs_rec succ v0 \<le> SPEC (\<lambda>r. r \<longrightarrow> acyclic G)"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  
  from F show ?thesis
    unfolding cycles_dfs_rec_def S acyclic_alt[OF wf_G]
    apply(refine_rcg refine_vcg impI REC_rule[where 
        \<Phi>="\<lambda>(V,v). V \<subseteq> verts G \<and> (\<forall>x\<in>V. \<forall>y\<in>V. \<forall>p. pre_digraph.awalk G x p y \<longrightarrow> \<not> pre_digraph.cycle G p)"]
        FOREACH_rule[where I="\<lambda>_ r. r \<longrightarrow> acyclic G"])
    apply(auto)
    apply(auto simp add: acyclic_alt[OF wf_G])
    (*apply (refine_rcg refine_vcg impI
      RECT_rule[where 
        \<Phi>="\<lambda>(V,v). (v0,v)\<in>E\<^sup>* \<and> V\<subseteq>{v. (v0,v)\<in>E\<^sup>*}" and
        V="finite_psupset ({v. (v0,v)\<in>E\<^sup>*}) <*lex*> {}"]
      FOREACHc_rule[where I="\<lambda>_ r. r \<longrightarrow> (v0, vd) \<in> E\<^sup>*"]
    )*)
    apply(auto)
    oops




section{*cycles*}
(*An undirected graph has a cycle if and only if a depth-first search (DFS) 
  finds an edge that points to an already-visited vertex (a back edge) [wikipedia] *)


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
