header {* \isaheader{Machine Words} *}
theory WordRefine
imports "../Refine" "~~/src/HOL/Word/Word"
begin

text {* This theory provides a simple example to show refinement of natural
  numbers to machine words. The setup is not yet very elaborated, but shows 
  the direction to go.
*}

subsection {* Setup *}
definition [simp]: "word_nat_rel \<equiv> build_rel (unat) (\<lambda>_. True)"
lemma word_nat_RELEATES[refine_dref_RELATES]: 
  "RELATES word_nat_rel" by (simp add: RELATES_def)

lemma [simp]: "single_valued word_nat_rel" unfolding word_nat_rel_def
  by blast

lemma [simp]: "single_valuedP (\<lambda>c a. a = unat c)" 
  by (rule single_valuedI) blast

lemma [simp]: "single_valued (converse word_nat_rel)" 
  unfolding word_nat_rel_def
  apply (auto simp del: build_rel_def)
  by (metis injI order_antisym order_eq_refl word_le_nat_alt)

lemmas [refine_hsimp] = 
  word_less_nat_alt word_le_nat_alt unat_sub iffD1[OF unat_add_lem]

subsection {* Example *}
type_synonym word32 = "32 word"

definition test :: "nat \<Rightarrow> nat \<Rightarrow> nat set nres" where "test x0 y0 \<equiv> do {
  let S={};
  (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
    let S=S\<union>{y};
    let x=x - 1;
    ASSERT (y<x0+y0);
    let y=y + 1;
    RETURN (S,x,y)
  }) (S,x0,y0);
  RETURN S
}"

lemma "y0>0 \<Longrightarrow> test x0 y0 \<le> SPEC (\<lambda>S. S={y0 .. y0 + x0 - 1})"
  -- "Choosen pre-condition to get least trouble when proving"
  unfolding test_def
  apply (intro WHILE_rule[where I="\<lambda>(S,x,y). 
    x+y=x0+y0 \<and> x\<le>x0 \<and>
    S={y0 .. y0 + (x0-x) - 1}"] 
    refine_vcg)
  by auto

definition test_impl :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 set nres" where 
  "test_impl x y \<equiv> do {
    let S={};
    (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
      let S=S\<union>{y}; 
      let x=x - 1;
      let y=y + 1;
      RETURN (S,x,y)
    }) (S,x,y);
    RETURN S
  }"

lemma test_impl_refine: 
  assumes "x'+y'<2^len_of TYPE(32)"
  assumes "(x,x')\<in>word_nat_rel" 
  assumes "(y,y')\<in>word_nat_rel" 
  shows "test_impl x y \<le> \<Down>(map_set_rel word_nat_rel) (test x' y')"
proof -
  from assms show ?thesis
    unfolding test_impl_def test_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (auto simp: refine_hsimp)
  done
qed

end