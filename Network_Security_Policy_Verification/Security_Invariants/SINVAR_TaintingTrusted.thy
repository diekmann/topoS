theory SINVAR_TaintingTrusted
imports "../TopoS_Helper" (*SINVAR_BLPtrusted*)
begin

subsection {* SecurityInvariant Tainting for IFS  *}

context
begin
  qualified datatype taints = TaintsUntaints (taints: "string set") (untaints: "string set")

  text{*The things in the first set are tainted, those in the second set are untainted.
    For example, a machine produces @{term "''foo''"}:
      @{term "TaintsUntaints {''foo''} {}"}

    For example, a machine consumes @{term "''foo''"} and @{term "''bar''"}, combines them in a 
    way that they are no longer critical and outputs @{term "''baz''"}:
      @{term "TaintsUntaints {''foo'', ''bar'', ''baz''} {''foo'', ''bar''}"}
      *}
    (*TODO: abbreviated: @{term "TaintsUntaints {''baz''} {''foo'', ''bar''}"}*)

  qualified definition default_node_properties :: "taints"
    where  "default_node_properties \<equiv> TaintsUntaints {} {}"
  
  qualified definition sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> bool" where
    "sinvar G nP \<equiv> \<forall> (v1,v2) \<in> edges G.
        taints (nP v1) - untaints (nP v1) \<subseteq> taints (nP v2)"
  
  text{*Information Flow Security*}
  qualified definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"
  
  
  private lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
    apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def sinvar_def)
    apply(clarify)
    by blast
  interpretation SecurityInvariant_preliminaries
  where sinvar = sinvar
  proof(unfold_locales, goal_cases)
    case (1 G nP)
      from 1 show ?case
      apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
          apply(auto simp add: sinvar_def)
       apply(auto simp add: sinvar_def SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
      (*by (metis (no_types, lifting) "1"(2) DiffD1 DiffD2 SecurityInvariant_withOffendingFlows.is_offending_flows_def delete_edges_simp2 graph.select_convs(2) sinvar_def)+*)
      done
    next
    case (2 N E E' nP) thus ?case by(simp add: sinvar_def) blast
    next
    case 3 thus ?case by(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
  qed
  
  
  
  text{*Needs the well-formedness condition that @{term "untaints otherbot \<subseteq> taints otherbot"}*}
  private lemma Taints_def_unique: "untaints otherbot \<subseteq> taints otherbot \<Longrightarrow>
      otherbot \<noteq> default_node_properties \<Longrightarrow>
      \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
         sinvar (delete_edges G f) p \<and>
          i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
    apply(simp add: default_node_properties_def)
    apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_def)
    apply (simp add:graph_ops)
    apply (simp split: prod.split_asm prod.split)
    apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
    apply(rule conjI)
     apply(simp add: wf_graph_def; fail)
    apply(case_tac otherbot, rename_tac tnts untnts)
    apply(subgoal_tac "\<exists>foo. foo \<in> tnts")
     prefer 2
     subgoal for tnts untnts (*TODO simplify*)
     apply(simp)
     apply(subgoal_tac "tnts \<noteq> {}")
      prefer 2 subgoal by blast
     by blast
    apply(elim exE, rename_tac foo)
    apply(rule_tac x="(\<lambda> x. default_node_properties)
            (vertex_1 := TaintsUntaints tnts {}, vertex_2 := default_node_properties)" in exI)
    apply(simp add: default_node_properties_def)
    apply(rule conjI)
     apply(simp add: sinvar_def, blast)
    apply(rule_tac x="vertex_2" in exI)
    apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
    apply(simp add: sinvar_def, blast)
    done
  
  
  
  subsubsection {*ENF*}
    private lemma Taints_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form
        sinvar (\<lambda>c1 c2.
          case (c1, c2) of (TaintsUntaints tnts1 untnts1, TaintsUntaints tnts2 untnts2)
          \<Rightarrow> tnts1 - untnts1 \<subseteq> tnts2)"
      unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def sinvar_def
      apply(intro allI)
      apply(rule iffI)
       apply(intro ballI, rename_tac e)
       apply(case_tac e, simp, rename_tac e1 e2)
       apply(case_tac "nP e1", simp)
       apply(case_tac "nP e2", simp)
       apply(erule_tac x=e in ballE, simp_all)
      apply(intro ballI, rename_tac e)
      apply(case_tac e, simp, rename_tac e1 e2)
      apply(case_tac "nP e1", simp)
      apply(case_tac "nP e2", simp)
      apply(erule_tac x=e in ballE, simp_all)
      done
    private lemma Taints_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (\<lambda>c1 c2.
          case (c1, c2) of (TaintsUntaints tnts1 untnts1, TaintsUntaints tnts2 untnts2)
          \<Rightarrow> tnts1 - untnts1 \<subseteq> tnts2)"
      unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def sinvar_def
      apply(intro conjI)
       subgoal using Taints_ENF by simp
      apply(intro allI)
      apply(rename_tac e)
      apply(case_tac e, simp, rename_tac e1 e2)
      by auto
       
  
    qualified definition Taints_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> ('v \<times> 'v) set set" where
    "Taints_offending_set G nP = (if sinvar G nP then
        {}
       else 
        { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> taints (nP e1) - untaints (nP e1) \<subseteq> taints (nP e2)} })"
    lemma Taints_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      apply(simp add: fun_eq_iff
                        SecurityInvariant_withOffendingFlows.ENF_offending_set[OF Taints_ENF]
                        Taints_offending_set_def)
      apply safe
       apply(rename_tac G nP a b)
       apply(case_tac "nP a", case_tac "nP b")
       apply(simp)
      apply(rename_tac G nP a b x)
      apply(case_tac "nP a", case_tac "nP b")
      apply(simp)
      by blast 
     
(*  
    interpretation Taints: SecurityInvariant_IFS sinvar default_node_properties
    rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      unfolding receiver_violation_def
      unfolding default_node_properties_def
      proof(unfold_locales, goal_cases)
      case (1 G f nP)
        from 1(2) show ?case
        apply(intro ballI)
        apply(rule SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF Taints_ENF_refl])
          apply(intro allI)
          apply(rename_tac e1 e2)
          apply(case_tac "nPa e1", case_tac "nPa e2")
          apply(simp_all)
        by blast
      next
      case 2 thus ?case
        apply(elim default_uniqueness_by_counterexample_IFS)
        apply(rule Taints_def_unique)
        apply(simp_all add: default_node_properties_def)
        (*the well-formedness constraint remains*)
        oops
      next
      case 3 show "set_offending_flows = Taints_offending_set" by(fact Taints_offending_set)
     qed
  
  
    lemma TopoS_Tainting: "SecurityInvariant sinvar default_node_properties receiver_violation"
    unfolding receiver_violation_def by unfold_locales
*)
end

end
