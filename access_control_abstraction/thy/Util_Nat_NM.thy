theory Util_Nat_NM
imports Main FiniteGraph
begin

(*old lemma, unused. *)

lemma exists_x1x2_x1notoffending_natLeq: 
  fixes 
    G::"'v graph" and
    f and
    p::"'v \<Rightarrow> nat"
  assumes
    "valid_graph G"
    "\<exists>(e1, e2)\<in>(edges G). \<not> (p e1 \<le> p e2)" and
    "f \<subseteq> edges G \<and> (\<forall>(e1, e2)\<in>f. \<not> p e1 \<le> p e2)" and
    "\<forall>(e1, e2)\<in>(edges G) - f. p e1 \<le> p e2"
  shows "\<exists> x1 x2. (x1,x2)\<in>(edges G) \<and> (x1,x2)\<in> f \<and> x1 \<in> fst ` f \<and> x1 \<notin> snd ` f \<and> ((p x1) = Max (p`fst` f))"
proof -
   from assms have a2: "\<exists>x\<in>(edges G). \<not> (case x of (e1, e2) \<Rightarrow> p e1 \<le> p e2)" by auto
   from assms have a3: "f \<subseteq>(edges G) \<and> (\<forall>(e1, e2)\<in>f. \<not> p e1 \<le> p e2)" by simp
   from assms have a4: "\<forall>(e1, e2)\<in>(edges G) - f. p e1 \<le> p e2" by simp
   from assms(1) have finiteE: "finite (edges G)" using valid_graph.finiteE by fast
   from finiteE conjunct1[OF a3] have  finiteF: "finite f" by (metis rev_finite_subset)

   -- "Find a suitable x1, it is the Max of the firsts"
   from finiteF have x12: "\<forall> x \<in> f. Max (p`fst` f) \<ge> p (fst x)" by (metis Max_ge finite_imageI image_eqI)
   from a2 a4 have x14: "\<exists> x1. (p x1) \<in> p`fst` f \<and> x1 \<in> fst` f" by fast
   from finiteF have "(p`fst` f) \<noteq> {} \<Longrightarrow> Max (p`fst` f) \<in> (p`fst` f)" by simp
   hence x15: "Max (p`fst` f) \<in> (p`fst` f)" using x14 by fastforce
   hence "\<exists> x1. ((p x1) = Max (p`fst` f)) \<and> x1 \<in> fst` f" by force
   from this x14 obtain x1 where x1Cond: "((p x1) = Max (p`fst` f)) \<and> x1 \<in> fst` f" by blast
   
   -- "Thus x1 is not in the seconds, not offending"
   from x1Cond x15 have x1ImportantProp3: "(p x1) \<in> p`fst` f" by presburger
   from x1Cond conjunct2[OF a3] x12 have "\<forall>(e1, e2) \<in> f. p x1 > p e2" by fastforce

   from x1Cond this a2 a3 a4 have x1ImportantProp1: "(p x1) \<notin> p`snd` f" by force
   hence x1ImportantProp2: "x1 \<notin> snd` f" by blast

   -- "Obtain x2"
   from x1ImportantProp3 x1Cond have x1ImportantProp4: "x1 \<in> fst` f" by presburger
   from this x1ImportantProp2 have  "\<exists> x1 x2. (x1,x2) \<in> f \<and> x1 \<notin> snd` f" by fastforce
   from this x1Cond x1ImportantProp2 obtain x2 where x2Cond:"(x1,x2) \<in> f \<and> x1 \<notin> snd` f" by force
   
   from a3 have "\<And> x. x \<in> f \<Longrightarrow> x \<in> (edges G)" by blast
   from this x2Cond have x1x2Cond: "(x1,x2) \<in> (edges G)" by blast

   from x1x2Cond x2Cond x1Cond show ?thesis by auto
qed


lemma exCasePairSimp: "(\<exists>x. x \<in> A \<and> (case x of (e1, e2) \<Rightarrow> P e1 e2)) = (\<exists>(e1, e2) \<in> A. (P e1 e2))"
  thm Pair_eq splitE splitI2
  by auto

lemma exCasePairNotSimp: "(\<exists>x. x \<in> A \<and> \<not> (case x of (e1, e2) \<Rightarrow> P e1 e2)) = (\<exists>(e1, e2) \<in> A. \<not> (P e1 e2))"
  by auto



end
