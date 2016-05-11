theory Analysis_Tainting
imports SINVAR_Tainting SINVAR_BLPbasic
begin

term SINVAR_Tainting.sinvar
term SINVAR_BLPbasic.sinvar


lemma "\<forall>ts v. nP v = ts \<longrightarrow> finite ts \<Longrightarrow>
  SINVAR_Tainting.sinvar G nP \<Longrightarrow> SINVAR_BLPbasic.sinvar G (card \<circ> nP)"
apply(simp add: SINVAR_Tainting.sinvar_def)
apply(clarify, rename_tac a b)
apply(erule_tac x="(a,b)" in ballE)
 apply(simp_all)
using card_mono by blast


(*Stronger version*)
lemma "\<forall>b \<in> snd ` edges G. finite (nP b) \<Longrightarrow>
  SINVAR_Tainting.sinvar G nP \<Longrightarrow> SINVAR_BLPbasic.sinvar G (card \<circ> nP)"
apply(simp add: SINVAR_Tainting.sinvar_def)
apply(clarify, rename_tac a b)
apply(erule_tac x="(a,b)" in ballE)
 apply(simp_all)
apply(case_tac "finite (nP a)")
 apply(case_tac [!] "finite (nP b)")
   using card_mono apply blast
  apply(simp_all)
done





end