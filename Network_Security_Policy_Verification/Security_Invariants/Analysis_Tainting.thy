theory Analysis_Tainting
imports SINVAR_Tainting SINVAR_BLPbasic
        SINVAR_TaintingTrusted SINVAR_BLPtrusted
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




text{*
  Translated to the Bell LaPadula model with trust:
  security clearance is the number of tainted minus the untainted things
  We set the Trusted flag if a machine untaints things.
*}
lemma "\<forall>ts v. nP v = ts \<longrightarrow> finite (taints ts) \<Longrightarrow>
  SINVAR_TaintingTrusted.sinvar G nP \<Longrightarrow>
    SINVAR_BLPtrusted.sinvar G ((\<lambda> ts. \<lparr>privacy_level = card (taints ts - untaints ts), trusted = (untaints ts \<noteq> {})\<rparr> ) \<circ> nP)"
apply(simp add: SINVAR_TaintingTrusted.sinvar_def)
apply(clarify, rename_tac a b)
apply(erule_tac x="(a,b)" in ballE)
 apply(simp_all)
apply(subgoal_tac "finite (taints (nP a) - untaints (nP a))")
 prefer 2 subgoal by blast
apply(rule card_mono)
 by blast+

end