theory NetworkModel_Util
imports Main FiniteGraph
begin

(*Utility lemmata go gere*)


lemma finite_ne_subset_induct [case_names singleton insert, consumes 2]:
  assumes "finite F" and "F \<noteq> {}" and "F \<subseteq> A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> P {x}"
    and "\<And>x F. finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
using assms
proof induct
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by cases auto
qed

end
