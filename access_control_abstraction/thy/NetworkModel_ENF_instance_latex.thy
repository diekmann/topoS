theory NetworkModel_ENF_instance_latex
imports "~~/src/HOL/Library/LaTeXsugar" Main FiniteGraph NetworkModel_Interface NetworkModel_Util NetworkModel_ENF
begin

(*DEPRECATED! uses lists! TODO: fix for set interface*)

(* for proof in the thesis *)
lemma (in NetworkModel_withOffendingFlows)  ENF_snds_refl_insatnce_documentedIsar:
  assumes a_not_eval: "\<not> eval_model G nP g"
  and   a_enf_refl: "ENF_refl P"
  and   a_bot_default_candidate:
    "\<forall> (nP::'v \<Rightarrow> 'a) e1 e2. \<not> (P (nP e1) (nP e2)) \<longrightarrow> \<not> (P (nP e1) \<bottom>)"
  and   a_offending: "f \<in> set (list_offending_flows G nP g)"
  and   a_offending_rm: "eval_model (delete_edges G f) nP g"
  and   a_i_snds: "i \<in> snds f"
  shows
        "\<not> eval_model G (nP(i := \<bottom>)) g"
proof -
  -- "Unfolding the ENF definition"
  from a_enf_refl have a_enf: "eval_model_all_edges_normal_form P"
    using ENF_refl_def by simp
  hence enf: 
    "\<forall> G nP gP. eval_model G nP gP  = 
    (\<forall> (e1, e2)\<in> set (edges G). P (nP e1) (nP e2))"
    using eval_model_all_edges_normal_form_def by simp

  -- {*All members in the set of offending flows violate @{term "P"}*}
  from ENF_offending_members[OF a_not_eval a_enf a_offending] 
  have offending_condition: 
    "\<forall> e1 e2. (e1, e2)\<in>set f \<longrightarrow> \<not> P (nP e1) (nP e2)" by fast
 
  -- {*We notate the updated node configuration of our goal with @{text "?nP'"}*}
  let ?nP' = "(nP(i := \<bottom>))"

  -- {*Obtain concrete flow in @{term "f"} where the target equals @{term "i"}*}
  from offending_not_empty[OF a_not_eval a_offending a_offending_rm] 
    ENF_offending_members[OF a_not_eval a_enf a_offending] a_i_snds hd_in_set
    obtain e1 e2 where "(e1, e2)\<in> set f \<and> e2 = i" by force
  hence "(e1, e2)\<in> set f" and "e2 = i" by blast+

  -- {*As @{term "e1"} and @{term "e2"} are in @{term "f"}, @{term "P"} does not hold for them*}
  from `(e1, e2)\<in> set f` offending_condition 
  have e1e2notP: "\<not> P (nP e1) (nP e2)" by simp

  -- {*Subgoal: From @{text "\<not> P (nP e1) (nP e2)"} show @{text "\<not> P (?nP' e1) (?nP' e2)"}*}

  -- "Second part of subgoal holds by assumption"
  from this a_bot_default_candidate have "\<not> P (nP e1) \<bottom>" by blast
  from this e1e2notP have e1e2subgoal1: "\<not> P (nP e1) (?nP' e2)" by simp

  -- {*As the model is reflexive, which means  @{term "P (nP e1) (nP e1)"} always holds, *}
  -- {*and  @{term "e1"} and @{term "e2"} are from @{term "f"}, @{term "e1"} and @{term "e2"} are different*}
  from ENF_refl_not_offedning[OF a_not_eval a_offending a_enf_refl] 
    `(e1, e2)\<in> set f` 
  have "e1 \<noteq> e2" by fast
  
  -- {*As @{term "e2=i"}, and if @{term "e1 \<noteq> i"}, *}
  -- {*we can always make a case distinction on @{term "e1 = i"}, as this case is always false*}
  from e1e2subgoal1 `e2 = i` 
  have "e1 \<noteq> e2 \<Longrightarrow> \<not> P (if e1 = i then \<bottom> else nP e1) (?nP' e2)" by simp
  hence "e1 \<noteq> e2 \<Longrightarrow> \<not> P (?nP' e1) (?nP' e2)" by simp
  from this `e1 \<noteq> e2` have e1e2subgoal2: "\<not> P (?nP' e1) (?nP' e2)" by simp

  -- {*We obtained @{term "e1"} and @{term "e2"} from  @{term "f"}, *}
  -- {*thus some nodes  @{term "e1"} and @{term "e2"} exist in @{term "f"} *}
  -- {*with the properties of our @{term "e1"} @{term "e2"}.*}
  -- {*All nodes listed in @{term "f"} are also in @{term "G"}.*}
  from e1e2subgoal2 
    offending_in_edges[OF conjunct1[OF 
        ENF_offending_members[OF a_not_eval a_enf a_offending]] 
    `(e1, e2)\<in> set f`] 
 have 
    "\<exists> (e1, e2)\<in> set (edges G). \<not> P (?nP' e1) (?nP' e2)" by blast
  hence 
    "\<not> (\<forall> (e1, e2)\<in> set (edges G). P ((nP(i := \<bottom>)) e1) ((nP(i := \<bottom>)) e2))"
    by fast

  -- {* Inserting the definition yields the final goal *}
  thus "\<not> eval_model G (nP(i := \<bottom>)) g" using enf by presburger
qed



end
