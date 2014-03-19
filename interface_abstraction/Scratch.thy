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
  \<forall> reachable v0 x. (x,x) \<notin> view^+ but this does not find undirected cycles! *)
(*is basic routing loop detection*)


hide_const(open) succ (*my succ in my graph*)

definition nodes_of :: "('v \<times> 'v) set \<Rightarrow> 'v set" where "nodes_of E \<equiv> (fst ` E \<union> snd ` E)"


(*Collections&Refinement tests*)


(*requires: no loops (x,x) \<in> E*)
(*V=worklist, (vertex, parent)*)
definition cycles_dfs_imp :: "('a \<times>'a) set \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "cycles_dfs_imp E v0 \<equiv>  do {
      (_,_,cycle) \<leftarrow> WHILE (\<lambda> (W,Discovered,cycle). W \<noteq> {} \<and> \<not> cycle) (\<lambda> (W,Discovered,cycle). do {
        (vparent,v) \<leftarrow> SPEC (\<lambda>v. v\<in>W);
        if v \<in> snd ` Discovered (* \<or> v \<in> fst ` Discovered evtl auch fst`?? test in python first!*)
        then
          RETURN (W,Discovered,True)
        else do {
          let succs = {v'. (v,v')\<in>E \<or> (v',v)\<in>E} - {vparent,v}; (*exclude self-loops*)
          let W = W - {(vparent,v)};
          let Discovered = insert (vparent,v) Discovered;
          let W = W \<union> ({v} \<times> succs);
          RETURN (W,Discovered,cycle)
        }
      }) ({(v0,v0 (*probably: succs v0????*))},{},False);
      RETURN cycle
  }"



lemma pcas_append: "pcas a p b \<Longrightarrow> pcas a (p @ [(b, c)]) c"
  by(induction a p b rule: pcas.induct, simp_all)

lemma pcas_iff_trancl: assumes "x \<noteq> y" shows "(\<exists> p. set p \<subseteq> D \<and> pcas x p y) \<longleftrightarrow> (x,y) \<in> D\<^sup>+"
proof
  assume "\<exists>p. set p \<subseteq> D \<and> pcas x p y"
  from this obtain p where pset: "set p \<subseteq> D" and pcas: "pcas x p y" by auto
  have "x \<noteq> y \<longrightarrow> set p \<subseteq> D \<longrightarrow> pcas x p y \<longrightarrow> (x, y) \<in> D\<^sup>+"
    apply(induction p arbitrary: x y)
    apply(simp)
    apply(clarify)
    apply(simp)
    using trancl_into_trancl2 by (metis r_into_trancl')
  from this assms pset pcas
  show "(x, y) \<in> D\<^sup>+" by simp
next
  show "(x,y) \<in> D\<^sup>+ \<Longrightarrow> (\<exists> p. set p \<subseteq> D \<and> pcas x p y)"
  apply(induction rule: trancl_induct)
  apply(rule_tac x="[(x,y)]" in exI)
  apply(simp)
  apply(erule exE)
  apply(rule_tac x="p@[(y,z)]" in exI)
  apply(simp add: pcas_append)
  done
qed

lemma pcas_start_in_pawalkvert: "pcas a p b \<Longrightarrow> a \<in> set (pawalk_verts a p)"
  by(induction p, simp_all)
lemma pcas_end_in_pawalkvert: "pcas a p b \<Longrightarrow> b \<in> set (pawalk_verts a p)"
  by(induction p arbitrary: a, simp_all)
lemma pcas_distinct_len: "pcas a p b \<Longrightarrow>  a \<noteq> b \<Longrightarrow> length p \<ge> 1"
  by(induction a p b rule:pcas.induct, simp_all)
lemma pawalk_verts_length: "length (pawalk_verts a p) = Suc (length p)"
  by(induction p arbitrary: a, simp_all)

value "dropWhile (\<lambda>x. x \<noteq> (1::nat)) [2,3,4,1,2,3]"

lemma "pcas x p y \<Longrightarrow> \<exists>p'. pcas x p' y \<and> set (pawalk_verts x p') \<subseteq> set (pawalk_verts x p) \<and> distinct (tl (pawalk_verts x p'))"
  apply(induction x p y rule: pcas.induct)
  apply(simp)
  apply(rule_tac x="[]" in exI)
  apply(simp)
  apply(simp)
  apply(erule_tac exE)
  apply(clarsimp)
  apply(case_tac "a = b")
  apply(rule_tac x="p'" in exI)
  apply(simp)
  using pcas_start_in_pawalkvert apply fast
  apply(case_tac "b \<notin> (set (pawalk_verts b p'))")
  apply(rule_tac x="(a,b)#p'" in exI)
  apply(simp)
  apply (metis pcas_start_in_pawalkvert)
  apply(rule_tac x="dropWhile (\<lambda>(x1,x2). x1 \<noteq> b) p'" in exI) (*TODO need to cut out circle ....*)
  apply(simp)
  nitpick
sorry (*TODOTODO*)

(*everything reachable from V'*)
lemma "{y. \<exists>x \<in> V'. (x,y) \<in> E\<^sup>*} = E\<^sup>*``V'" by blast

definition restrict_to :: "('v \<times> 'v) set \<Rightarrow> 'v set \<Rightarrow> ('v \<times> 'v) set" where
  "restrict_to E V \<equiv> {(a,b)\<in>E. a\<in>V \<and> b\<in>V}"

definition bi :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" where
  "bi E = E \<union> backflows E"

lemma bi_insert: "bi (insert (x,y) X) = {(x,y), (y,x)} \<union> bi X"
  by(auto simp add: bi_def backflows_def)
lemma bi_sym: "sym (bi X)"
  by(simp add: sym_def bi_def backflows_def)
lemma bi_union: "bi A \<union> bi B = bi (A \<union> B)"
  by(auto simp add: sym_def bi_def backflows_def)

definition uni_restrict_to :: "('v \<times> 'v) set \<Rightarrow> 'v set \<Rightarrow> ('v \<times> 'v) set" where
  "uni_restrict_to E V \<equiv> restrict_to (bi E) V"

lemma uni_restrict_to_mono: "D' \<subseteq> D \<Longrightarrow> uni_restrict_to E D' \<subseteq> uni_restrict_to E D"
  by(simp add: uni_restrict_to_def restrict_to_def, fast)



definition has_undirected_cycle_in :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "has_undirected_cycle_in E \<equiv> 
  \<exists> u \<in> nodes_of E. \<exists> p. set p \<subseteq> bi E \<and> pcas u p u \<and> distinct (tl (Pair_Digraph.pawalk_verts u p)) \<and> length p \<ge> 3"


definition cycles_dfs_imp_WHILE_invar :: "('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> ('v\<times>'v) set \<times> ('v\<times>'v) set \<times> bool \<Rightarrow> bool" where
  "cycles_dfs_imp_WHILE_invar E v0 \<sigma> \<equiv> let (W,D,cycle) = \<sigma> in
        W \<subseteq> bi E \<and> D \<subseteq> bi E
        \<and> (\<forall> (a,_) \<in> W. \<exists> (_,d) \<in> D. (d,a) \<in> D)
        \<and> W \<inter> D = {}
        \<and> (\<forall> x\<in>snd`D. \<forall> y\<in>snd`D. x \<noteq> y \<longrightarrow> (x,y) \<in> (bi D)\<^sup>+)
        \<and> (cycle \<longrightarrow> has_undirected_cycle_in (D \<union> W)) 
        (*\<and> (\<forall> x\<in>Discovered. \<forall> y\<in>Discovered. x \<noteq> y \<longrightarrow> 
            (\<exists> p. set p \<subseteq> uni_restrict_to E (Discovered) \<and> pcas x p y \<and> distinct (Pair_Digraph.pawalk_verts x p)))*)
        (*E\<^sup>*``(fst ` V') \<union> fst ` Discovered = E\<^sup>*``{v0} \<and> *)"


lemma "(\<forall> x\<in>snd`(bi D). \<forall> y\<in>snd`D. x \<noteq> y \<longrightarrow> (x,y) \<in> (bi D)\<^sup>+) \<Longrightarrow> (\<forall> x\<in>fst`D. \<forall> y\<in>snd`D. x \<noteq> y \<longrightarrow> (x,y) \<in> (bi D)\<^sup>+)"
  apply(clarsimp)
  apply(rename_tac a b x y)
  apply(erule_tac x="(b,a)" in ballE)
  apply(erule_tac x="(x,y)" in ballE)
  apply(simp_all)
  by(simp add: bi_def backflows_def)

lemma distinct_xyz_length: "distinct [x,y,z] \<Longrightarrow> x \<in> set X \<Longrightarrow> y \<in> set X \<Longrightarrow> z \<in> set X \<Longrightarrow> length X \<ge> 3"
by (smt distinct_length_2_or_more length_pos_if_in_set list.size(4) list_decomp_2 list_tail_coinc set_ConsD)

lemma assumes D_path: "(\<forall> x\<in>nodes_of D. \<forall> y\<in>snd`D. x \<noteq> y \<longrightarrow> (x,y) \<in> (bi D)\<^sup>+)" (*replace snd with nodes_of*)
    and ad2W: "(a, d2) \<in> W" and d1d2D: "(d1, d2) \<in> D"
    and WD_edge: "(\<forall> (a,_) \<in> W. \<exists> (_,d) \<in> D. (d,a) \<in> D)"
    and nreflW: "\<forall> (x,y) \<in> W. x \<noteq> y"
    (*and nreflD: "\<forall> (x,y) \<in> D. x \<noteq> y"*)
    and disjunct: "bi W \<inter> bi D = {}"
   shows "has_undirected_cycle_in (D \<union> {(a,d2)})"
   proof(unfold has_undirected_cycle_in_def)
    from ad2W WD_edge have "\<exists> (x,y) \<in> D. (y, a) \<in> D" by fast
    from this obtain y where yD: "(y, a) \<in> D" by blast (*maybe add y to the path to prolong it?*)
    have "a \<noteq> d2" using ad2W nreflW by blast
    have "y \<noteq> a" sorry
    from `y \<noteq> a` `a \<noteq> d2` disjunct ad2W yD have "y \<noteq> d2" by(simp add: bi_def backflows_def, blast)
    (* d2 \<longrightarrow> y \<longrightarrow> (y,a) \<longrightarrow> a,d2 <-- in W*) (*need d2 \<noteq> y*)
    (*from yD have "set [(y,a)] \<subseteq> bi D \<and> pcas y [(y,a)] a" by (auto simp: bi_def)*)
    from yD d1d2D D_path have "y \<noteq> d2 \<longrightarrow> (y, d2) \<in> (bi D)\<^sup>+"
      by(simp add: nodes_of_def, force)
    from this `y \<noteq> d2` have "(d2, y) \<in> (bi D)\<^sup>+" using bi_sym by (metis symD sym_trancl)
    from this pcas_iff_trancl[symmetric] `y \<noteq> d2` have "\<exists>p. set p \<subseteq> (bi D) \<and> pcas d2 p y" by metis
    from this obtain p where p: "set p \<subseteq> (bi D) \<and> pcas d2 p y" and pdist: "distinct (pawalk_verts d2 p)" sorry
    from pcas_distinct_len p `y \<noteq> d2` have plength: "length p \<ge> 1" by metis
    let ?pa = "p@[(y,a)]"
    from p yD have pa: "set ?pa \<subseteq> (bi D) \<and> pcas d2 ?pa a" by(simp add: bi_def pcas_append)
    have "pcas d2 p y \<Longrightarrow> pawalk_verts d2 (p @ [(y, a)]) = (pawalk_verts d2 p)@[a]"
      by(induction p arbitrary: d2, simp_all)
    from this p have pawalk_verts_simp: "pawalk_verts d2 (p @ [(y, a)]) = (pawalk_verts d2 p)@[a]" by simp
    have a_in_path_length: "a \<in> set (pawalk_verts d2 p) \<Longrightarrow> length p \<ge> 2"
    proof -
      assume 0: "a \<in> set (pawalk_verts d2 p)"
      from `y \<noteq> a` `a \<noteq> d2` `y \<noteq> d2` have 1: "distinct [d2, y, a]" by auto
      from p have 2: "d2 \<in> set (pawalk_verts d2 p)" by (metis pcas_start_in_pawalkvert)
      from p have 3: "y \<in> set (pawalk_verts d2 p)" using pcas_end_in_pawalkvert by metis
      from distinct_xyz_length 0 1 2 3 have "length (pawalk_verts d2 p) \<ge> 3" by fast
      from this pawalk_verts_length show "length p \<ge> 2" by (metis le_numeral_Suc pred_numeral_simps(3))
    qed
    from pdist have padist: "a \<notin> set (pawalk_verts d2 p) \<Longrightarrow> distinct (pawalk_verts d2 ?pa)"
      by(simp add: pawalk_verts_simp)
    (*if a in pa: let ?pa = p*)
    from plength have palength: "length ?pa \<ge> 2" by simp
    from ad2W have ad2biW: "(d2,a) \<in> bi W" by(simp add: bi_def backflows_def)
    hence "set [(a, d2)] \<subseteq> bi {(a,d2)} \<and> pcas a [(a, d2)] d2" by (simp add: bi_def)
    from this pa have 1: "set ((a, d2)#?pa) \<subseteq> bi {(a,d2)} \<union> bi D \<and> pcas a ((a, d2)#?pa) a" by auto
    from padist have 2: "distinct (tl (pawalk_verts a ((a, d2)#?pa)))" by simp
   
   show "\<exists>u\<in>nodes_of (D \<union> {(a, d2)}). \<exists>p. set p \<subseteq> bi (D \<union> {(a, d2)}) \<and> pcas u p u \<and> distinct (tl (pawalk_verts u p)) \<and> 3 \<le> length p"
    apply(case_tac "a \<notin> set (pawalk_verts d2 p)")
    apply(rule_tac x=a in bexI)
    apply(rule_tac x="(a, d2)#?pa" in exI)
    apply(rule conjI)
    using bi_union 1 apply blast
    apply(rule conjI)
    using 1 apply blast
    apply(rule conjI)
    using padist apply simp
    apply(simp add: plength[simplified])
    apply(simp add: nodes_of_def)
oops

lemma cycles_dfs_imp_WHILE_invar_step1:
  assumes "cycles_dfs_imp_WHILE_invar E v0 (W, Discovered, cycle)"
       "(a, snd (d1, d2)) \<in> W" "(d1, d2) \<in> Discovered" "W \<noteq> {}" "\<not> cycle" 
  shows "cycles_dfs_imp_WHILE_invar E v0 (W, Discovered, True)"
  using assms unfolding cycles_dfs_imp_WHILE_invar_def
  apply(simp)
  (*a is snd`discovered \<longrightarrow> (d2,a) \<in> D^+ \<longrightarrow> need W disjunct D \<longrightarrow> path: d2,a + (a,d2)*)
  (*TODO*)
  apply(simp add: has_undirected_cycle_in_def)
  proof -
  show "\<exists>u\<in>nodes_of (Discovered \<union> W). \<exists>p. set p \<subseteq> bi (Discovered \<union> W) \<and> pcas u p u \<and> distinct (tl (pawalk_verts u p)) \<and> 3 \<le> length p"
oops

lemma nodes_of_backflows_snd: "nodes_of E = snd ` E \<union> snd ` (backflows E)"
    apply(simp add: nodes_of_def backflows_alt_fstsnd) by force
lemma nodes_of_subset_backflows_b: "v0 \<in> nodes_of E \<Longrightarrow> V \<subseteq> insert (v0,v0) (E \<union> backflows E) \<Longrightarrow> (a, b) \<in> V \<Longrightarrow> b \<in> nodes_of E"
    apply(simp add: nodes_of_backflows_snd) by force

lemma "y \<in> snd ` (V - {(a, b)} \<union> {b} \<times> ({v'. (b, v') \<in> E \<or> (v', b) \<in> E} - {a, b})) \<Longrightarrow>
         b \<noteq> y \<Longrightarrow>  y \<notin> snd ` V \<Longrightarrow> False" oops

lemma cycles_dfs_imp_WHILE_invar_step2:
  assumes "v0 \<in> nodes_of E" and "cycles_dfs_imp_WHILE_invar E v0 (W, Discovered, False)"
       "(w1, w2) \<in> W"
       "w2 \<notin> snd ` Discovered"
       "W \<noteq> {}"
       "\<not> cycle"
  shows "cycles_dfs_imp_WHILE_invar E v0 (W - {(w1, w2)} \<union> {w2} \<times> ({v'. (w2, v') \<in> E \<or> (v', w2) \<in> E} - {w1, w2}), insert (w1, w2) Discovered, False)" 
  using assms unfolding cycles_dfs_imp_WHILE_invar_def
  apply(simp)
  apply(rule conjI)
  apply(auto)[1]
  apply(rule conjI)
  apply(auto simp add: bi_def backflows_def)[1]
  apply(rule conjI)
  apply(auto simp add: bi_def backflows_def)[1]
  apply(rule conjI)
  apply blast
  apply(rule conjI)
  nitpick (*dis*)
  apply(simp add: bi_insert)[1]
  apply(clarsimp)
  apply(erule_tac x="(w1,w2)" in ballE, simp)
  prefer 2 apply simp
  apply(erule bexE)
  apply(clarify)
  (*holds but needs proof ...*)
    using nodes_of_subset_backflows_b
oops

lemma cycles_dfs_imp_sound:
  fixes succ and v0
  assumes F: "finite E"
  shows "cycles_dfs_imp E v0 \<le> SPEC (\<lambda>r. r \<longleftrightarrow> has_undirected_cycle_in (uni_restrict_to E (E\<^sup>*``{v0})))"
proof -
  
  from F show ?thesis
    unfolding cycles_dfs_imp_def
    apply(intro WHILE_rule[where I="cycles_dfs_imp_WHILE_invar E v0"] refine_vcg)
    apply(auto simp add: cycles_dfs_imp_WHILE_invar_def restrict_to_def has_undirected_cycle_in_def nodes_of_def)[1]
    apply(clarify, rename_tac A W C V Discovered cycle I J a L d1 d2)
    apply(simp add: cycles_dfs_imp_WHILE_invar_step1)
    apply(clarsimp)
    apply(rename_tac W Discovered cycle w1 w2)
    apply(auto simp add: cycles_dfs_imp_WHILE_invar_def)[1]
    apply(simp add: cycles_dfs_imp_WHILE_invar_def)[1]
    apply(rule conjI)
    apply(auto)[1]
    apply(rule conjI)
    apply(auto)[1]
    apply(rule conjI)
    apply(auto)[1]
    apply clarify
    using v0 try0
    oops





(*no idea what's wrong here*)
definition cycles_dfs_recX :: "('a \<Rightarrow>'a set) \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "cycles_dfs_recX succ v0 \<equiv> REC (\<lambda>D (V,v). 
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
  shows "cycles_dfs_recX succ v0 \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<forall>x\<in>V. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+))"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  
  from F show ?thesis
    unfolding cycles_dfs_recX_def S
    apply(intro REC_rule[where \<Phi>="\<lambda>(V',v'). (v0,v')\<in>E\<^sup>* \<and> V'\<subseteq>V \<and> (\<forall>x\<in>V'. (v0,x)\<in>E\<^sup>* \<longrightarrow> (x,x)\<notin>E\<^sup>+)"] 
        FOREACH_rule[where I="\<lambda>Succs r. XXX"] refine_vcg) (*r \<longrightarrow> (\<forall>v\<in>V. (v0,v)\<in>E\<^sup>* \<longrightarrow> (v,v)\<notin>E\<^sup>+)*)
    apply(refine_mono) (*REC is somehow undocumented*)
    apply(simp)
    apply(simp_all)
    apply(rename_tac V' v')
    oops










fun fibdef :: "nat \<Rightarrow> nat" where
  "fibdef 0 = 1" |
  "fibdef (Suc 0) = 1" |
  "fibdef (Suc (Suc n)) = fibdef (Suc n) + fibdef n"
value "fibdef 4"

definition fibref :: "nat \<Rightarrow> nat nres" 
  where
  "fibref n \<equiv> REC (\<lambda>D (n). 
    if n = 0 then RETURN 1
    else if n = 1 then RETURN 1
    else do { 
      x \<leftarrow> (D (n - 1));
      y \<leftarrow> (D (n - 2));
      RETURN (x + y)
      }
    ) (n)"

lemma fibref:
  shows "fibref n \<le> SPEC (\<lambda>r. r = fibdef n)"
proof -
  show ?thesis
    unfolding fibref_def
    apply (refine_rcg refine_vcg REC_rule[where \<Phi>="\<lambda>n. n \<ge> 0"])
    apply(simp_all)[3]
    apply(simp add: RETURN_def)
    apply(auto)
    oops




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
