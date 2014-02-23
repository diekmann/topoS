theory Scratch
imports Main
"../thy_lib/FiniteGraph"
"../thy_lib/isabelle_afp/Graph_Theory/Pair_Digraph"
"../thy_lib/Collections/Refine_Dflt"
"../thy_lib/Collections/Examples/Autoref/Nested_DFS"
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

(*hmm, for my purposes, this almost looks executable enough! \<dots>*)
definition pcycle :: "'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> bool" where
  "pcycle V E v0 \<equiv> \<exists>v\<in>V. (v0,v)\<in>E\<^sup>* \<and> (v,v)\<in>E\<^sup>+"
(*for my purpose, it might be enough:
  (x,x) \<notin> view^+ but this does not find undirected cycles! *)
(*is basic routing loop detection*)


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


(*An undirected graph has a cycle if and only if a depth-first search (DFS) 
  finds an edge that points to an already-visited vertex (a back edge) [wikipedia] *)
(*need to trace edges!!*)

(*http://www.geeksforgeeks.org/detect-cycle-undirected-graph/*)

fun neighbors :: "('v \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> 'v list" where
  "neighbors E v = map (\<lambda> (_,y). y) (filter (\<lambda>(x,y). x=v) E)"

declare neighbors.simps[simp del]

lemma set_neighbors: "set (neighbors E v) = {y. (v,y) \<in> set E}"
by (auto simp add: neighbors.simps)

(* v0 \<Rightarrow> visited \<Rightarrow> parent \<Rightarrow> neighbors *)
function x_cycle :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> (('v \<times> 'v) list) \<Rightarrow> bool" where
  "x_cycle v visited parent E = ((neighbors E v \<noteq> []) \<and> (\<forall> nxt \<in> set (neighbors E v). (if nxt \<notin> set visited
    then
      x_cycle nxt (v#visited) v E
    else
      nxt \<noteq> parent)))"
apply pat_completeness
by auto

(*how do I termination?*)
termination x_cycle
apply (relation "measure (\<lambda>(v,vis,p,E). Suc(length E) - length vis)")
apply(simp)
apply(simp only: set_neighbors)
oops

value "x_cycle (1::nat) [] 1 [(1,2), (2,3), (3,1)]"
value "x_cycle (1::nat) [] 1 [(1,2), (2,3), (1,3)]"



(*Tets with DFS AFP*)

(*E should be a DAG, finds cycles in the underlying undirected graph
*)
(* E worklist visited*)
function y_cycle :: "(('v \<times> 'v) list) \<Rightarrow> 'v list \<Rightarrow> 'v set \<Rightarrow> bool" where
  "y_cycle E [] vis = False" |
  "y_cycle E (w#ws) vis = (if w \<in> vis then True 
                        else y_cycle E (neighbors E w@ws) (insert w vis))"
by pat_completeness auto

termination (*I HAVE NO IDEA how to do termination proofs ... Where is this documented?*)
apply (relation "inv_image (finite_psubset <*lex*> less_than)  
                   (\<lambda>(E,w,vis). ((fst ` set E \<union> snd ` set E) - vis, size w))")
apply auto[1]
apply (simp_all add: finite_psubset_def)
apply(case_tac "w \<in> (fst ` set E \<union> snd ` set E)")
apply(auto simp add: neighbors.simps)
by (metis (lifting, mono_tags) filter_False imageI split_beta)


value "y_cycle [(1,2), (2,3), (3,1)] [1::nat] {}"
value "(1,1) \<in> {(1::nat,2::nat), (2,3), (3,1)}^+"
value "y_cycle [(1,2), (2,3), (1,3)] [1::nat] {}"
value "{(1::nat,2::nat), (2,3), (1,3)}^+"
value "y_cycle [(1,2), (2,3), (3,4)] [1::nat] {}"
value "y_cycle [(1,2), (2,1)] [1::nat] {}" (*not a DAG*)
value "(1,1) \<in> {(1::nat,2::nat), (2,1)}^+"
value "y_cycle [(1,1)] [1::nat] {}"
value "y_cycle [(1,2), (1,3), (3,4), (1,5), (5,6), (2,4)] [1::nat] {}"



(*
How do I formalize that the underlying undirected graph is acyclic?
Digraph.symmetric
*)
definition "underlying_undirected_cycle \<equiv> 
\<exists>p u. awalk u p u \<and> distinct (tl (awalk_verts u p)) \<and> length p \<ge> 3"












(*Collections&Refinement tests*)


(*does this really detetc cycles?*)
(*V=worklist, (vertex, parent)*)
definition cycles_dfs_imp :: "('a \<Rightarrow>'a set) \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "cycles_dfs_imp succ v0 \<equiv>  do {
      (_,_,cycle) \<leftarrow> WHILE (\<lambda> (V,Discovered,cycle). V \<noteq> {} \<and> \<not> cycle) (\<lambda> (V,Discovered,cycle). do {
        (v,vparent) \<leftarrow> SPEC (\<lambda>v. v\<in>V );
        let succs = (succ v) - {vparent};
        if succs \<inter> fst ` Discovered  \<noteq> {} then RETURN (V,Discovered,True) else do {
          let V = V - {(v,vparent)};
          let Discovered = insert (v,vparent) Discovered;
          let V = V \<union> ((succ v) \<times> {v});
          RETURN (V,Discovered,cycle)
        }
      }) ({(v0,v0)},{},False);
      RETURN cycle
  }"

(*everything reachable from V'*)
lemma "{y. \<exists>x \<in> V'. (x,y) \<in> E\<^sup>*} = E\<^sup>*``V'" by blast

definition cycles_dfs_imp_WHILE_invar :: "('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> ('v\<times>'v) set \<times> ('v\<times>'v) set \<times> bool \<Rightarrow> bool" where
  "cycles_dfs_imp_WHILE_invar E v0 \<sigma> \<equiv> let (V',Discovered,cycle) = \<sigma> in
        V' \<subseteq> insert (v0,v0) E \<and> Discovered \<subseteq> insert (v0,v0) E \<and> 
        E\<^sup>*``(fst ` V') \<union> fst ` Discovered = E\<^sup>*``{v0} \<and> 
        ( Discovered \<inter> V' = {})"
        (*{(a,b) \<in> E. a \<in> Discovered \<and> b \<in> Discovered} = E*)
        (*need condition: no cycle so far!*)

lemma cycles_dfs_imp_WHILE_invar_step1:
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 (V',Discovered,cycle)"
      "V' \<noteq> {}" "\<not> cycle" "x \<in> V'" "x \<in> Discovered"
  shows "cycles_dfs_imp_WHILE_invar V E v0 (V', Discovered, True)"
  using assms apply(simp add: cycles_dfs_imp_WHILE_invar_def) by blast

lemma cycles_dfs_imp_WHILE_invar_step2:
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 (V', Discovered, cycle)"
       "V' \<noteq> {}" "\<not> cycle" "x \<in> V'" "x \<notin> Discovered"
  shows "cycles_dfs_imp_WHILE_invar V E v0 (V' - {x} \<union> E `` {x}, insert x Discovered, cycle)"
  using assms apply(simp add: cycles_dfs_imp_WHILE_invar_def)
  apply(rule conjI)
  apply blast
  thm it_step_insert_iff
oops

lemma cycles_dfs_imp_WHILE_invar_goal_c1: 
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 ({},Discovered,cycle)"
  shows "\<not> cycle \<longleftrightarrow> (\<forall>x\<in>V. (v0, x) \<in> E\<^sup>* \<longrightarrow> (x, x) \<notin> E\<^sup>+)"
  using assms by(auto simp add: cycles_dfs_imp_WHILE_invar_def)

lemma cycles_dfs_imp_sound:
  fixes succ and v0
  defines "E \<equiv> {(v,v'). v'\<in>succ v}"
  defines "V \<equiv> {v. (v0,v)\<in>E\<^sup>*}"
  assumes F: "finite V"
  shows "cycles_dfs_imp succ v0 \<le> SPEC (\<lambda>r. \<not> r \<longleftrightarrow> (\<forall>x\<in>V. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+))"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  have V: "V = E\<^sup>*``{v0}"
    by (auto simp: V_def)
  
  from F show ?thesis
    unfolding cycles_dfs_imp_def S
    apply(intro WHILE_rule[where I="cycles_dfs_imp_WHILE_invar E v0"] refine_vcg)
    apply(auto simp add: V_def cycles_dfs_imp_WHILE_invar_def)[1]
    apply(clarify)
    apply(drule(5) cycles_dfs_imp_WHILE_invar_step1[OF V])
    apply(clarify)
    prefer 2
    apply(simp add: cycles_dfs_imp_WHILE_invar_goal_c1)
    apply(auto simp add: V_def cycles_dfs_imp_WHILE_invar_def)[1]
    oops



(**The old version***)
definition cycles_dfs_imp_WHILE_invar :: "'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> 'v set \<times> 'v set \<times> bool \<Rightarrow> bool" where
  "cycles_dfs_imp_WHILE_invar V E v0 \<sigma> \<equiv> let (V',Discovered,cycle) = \<sigma> in
        V' \<subseteq> V \<and> Discovered \<subseteq> V \<and> 
        (*E\<^sup>*``V' = V - Discovered *) (*Discovered = V - E\<^sup>*``V'*) E\<^sup>*``V' \<union> Discovered = V \<and> 
        ( Discovered \<inter> V' = {}) \<and>
        ( \<not>cycle \<longleftrightarrow> (\<forall>x\<in>Discovered. (v0, x) \<in> E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+))"
        (*{(a,b) \<in> E. a \<in> Discovered \<and> b \<in> Discovered} = E*)
        (*need condition: no cycle so far!*)

lemma cycles_dfs_imp_WHILE_invar_step1:
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 (V',Discovered,cycle)"
      "V' \<noteq> {}" "\<not> cycle" "x \<in> V'" "x \<in> Discovered"
  shows "cycles_dfs_imp_WHILE_invar V E v0 (V', Discovered, True)"
  using assms apply(simp add: cycles_dfs_imp_WHILE_invar_def) by blast

lemma cycles_dfs_imp_WHILE_invar_step2:
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 (V', Discovered, cycle)"
       "V' \<noteq> {}" "\<not> cycle" "x \<in> V'" "x \<notin> Discovered"
  shows "cycles_dfs_imp_WHILE_invar V E v0 (V' - {x} \<union> E `` {x}, insert x Discovered, cycle)"
  using assms apply(simp add: cycles_dfs_imp_WHILE_invar_def)
  apply(rule conjI)
  apply blast
  apply(rule conjI)oops
apply (metis Image_singleton_iff rtrancl.rtrancl_into_rtrancl subsetD subsetI)
  apply(rule conjI)
  apply blast
  apply(rule conjI)
apply (metis Un_insert_left insert_Diff_single insert_subset rtrancl_apply_insert subsetI subset_antisym)
  apply(rule conjI)defer 
  apply(rule conjI)
  oops
  apply(rule conjI)
  thm it_step_insert_iff
oops

lemma cycles_dfs_imp_WHILE_invar_goal_c1: 
  assumes "V = E\<^sup>*``{v0}" and "cycles_dfs_imp_WHILE_invar V E v0 ({},Discovered,cycle)"
  shows "\<not> cycle \<longleftrightarrow> (\<forall>x\<in>V. (v0, x) \<in> E\<^sup>* \<longrightarrow> (x, x) \<notin> E\<^sup>+)"
  using assms by(auto simp add: cycles_dfs_imp_WHILE_invar_def)

lemma cycles_dfs_imp_sound:
  fixes succ and v0
  defines "E \<equiv> {(v,v'). v'\<in>succ v}"
  defines "V \<equiv> {v. (v0,v)\<in>E\<^sup>*}"
  assumes F: "finite V"
  shows "cycles_dfs_imp succ v0 \<le> SPEC (\<lambda>r. \<not> r \<longleftrightarrow> (\<forall>x\<in>V. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+))"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  have V: "V = E\<^sup>*``{v0}"
    by (auto simp: V_def)
  
  from F show ?thesis
    unfolding cycles_dfs_imp_def S
    apply(intro WHILE_rule[where I="cycles_dfs_imp_WHILE_invar V E v0"] refine_vcg)
    apply(auto simp add: V_def cycles_dfs_imp_WHILE_invar_def)[1]
    apply(clarify)
    apply(drule(5) cycles_dfs_imp_WHILE_invar_step1[OF V])
    apply(clarify)
    prefer 2
    apply(simp add: cycles_dfs_imp_WHILE_invar_goal_c1)
    apply(auto simp add: V_def cycles_dfs_imp_WHILE_invar_def)[1]
    oops




(*no idea what's wrong here*)
definition cycles_dfs_rec :: "('a \<Rightarrow>'a set) \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "cycles_dfs_rec succ v0 \<equiv> REC (\<lambda>D (V,v). 
    if v \<in> V then RETURN True 
    else do {
      let V=insert v V;
      FOREACH (succ v) (\<lambda>v' _. D (V,v')) False }
  ) ({},v0)"
lemma cycles_dfs_rec_sound:
  fixes succ and v0
  defines "E \<equiv> {(v,v'). v'\<in>succ v}"
  defines "V \<equiv> {v. (v0,v)\<in>E\<^sup>*}"
  assumes F: "finite V"
  shows "cycles_dfs_rec succ v0 \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<forall>x\<in>V. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+))"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  
  from F show ?thesis
    unfolding cycles_dfs_rec_def S
    apply(intro REC_rule[where \<Phi>="\<lambda>(V',v'). (v0,v')\<in>E\<^sup>* \<and> V'\<subseteq>V \<and> (\<forall>x\<in>V'. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+)"] 
        FOREACH_rule[where I="\<lambda>Succs r. XXX"] refine_vcg) (*r \<longrightarrow> (\<forall>v\<in>V. (v0,v)\<in>E\<^sup>* \<longrightarrow> (v,v)\<notin>E\<^sup>+)*)
    apply(refine_mono) (*REC is somehow undocumented*)
    apply(simp)
    apply(simp_all)
    apply(rename_tac V' v')
    apply(intro FOREACH_rule[where I="\<lambda>_ r. r \<longrightarrow> (\<forall>v\<in>V. (v0,v)\<in>E\<^sup>* \<longrightarrow> (v,v)\<notin>E\<^sup>+)"] refine_vcg)
    apply(refine_rcg)
    apply(auto)
    apply(refine_rcg refine_vcg impI REC_rule[where 
        \<Phi>="\<lambda>(V,v). (v0,v)\<in>E\<^sup>* \<and> V\<subseteq>{v. (v0,v)\<in>E\<^sup>*} \<and> \<not>(\<exists>v\<in>V. (v0,v)\<in>E\<^sup>* \<and> (v,v)\<in>E\<^sup>+)"]
        FOREACH_rule[where I="\<lambda>_ r. r \<longrightarrow> (\<forall>v\<in>V. (v0,v)\<in>E\<^sup>* \<longrightarrow> (v,v)\<notin>E\<^sup>+)"])
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

(*TODO only acyclic in reachable from v0*)




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
