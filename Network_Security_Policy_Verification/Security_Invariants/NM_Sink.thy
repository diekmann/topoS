theory NM_Sink
imports "../NetworkModel_Helper"
begin

section {* NetworkModel Sink (IFS)*}

datatype node_config = Sink | SinkPool | Unassigned

definition default_node_properties :: "node_config"
  where  "default_node_properties = Unassigned"

fun allowed_sink_flow :: "node_config \<Rightarrow> node_config \<Rightarrow> bool" where
  "allowed_sink_flow Sink _ = False" |
  "allowed_sink_flow SinkPool SinkPool = True" |
  "allowed_sink_flow SinkPool Sink = True" |
  "allowed_sink_flow SinkPool _ = False" |
  "allowed_sink_flow Unassigned _ = True"


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. e1 \<noteq> e2 \<longrightarrow> allowed_sink_flow (nP e1) (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus = True" (*this is odd. 
  philosophical: default is less restrictive rule. 
  thus, responsibility is in the one who accepts and not the one who initiates. two entities are needed for a connection! *)


subsubsection {*Preliminaries*}
  lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
    apply(simp only: NetworkModel_withOffendingFlows.eval_model_mono_def)
    apply(clarify)
    by auto
  
  interpretation NetworkModel_preliminaries
  where eval_model = eval_model
  and verify_globals = verify_globals
    apply unfold_locales
      apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
          apply(auto)[6]
     apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops)[1]
    apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
   done

section{*ENF*}
  lemma Sink_ENFnr: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl eval_model allowed_sink_flow"
    by(simp add: NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl_def)
  lemma Unassigned_to_All: "\<forall> e2. allowed_sink_flow Unassigned e2"
    by (rule allI, case_tac e2, simp_all)
  lemma Unassigned_default_candidate: "\<forall> e1 e2. \<not> allowed_sink_flow e1 e2 \<longrightarrow> \<not> allowed_sink_flow e1 Unassigned"
    apply(rule allI)+
    apply(case_tac "e2")
      apply simp_all
     apply(case_tac "e1")
       apply simp_all
    apply(case_tac "e1")
      apply simp_all
    done

  definition Sink_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "Sink_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_sink_flow (nP e1) (nP e2)} })"
  lemma Sink_offending_set: 
  "NetworkModel_withOffendingFlows.set_offending_flows eval_model = Sink_offending_set"
    apply(simp only: fun_eq_iff ENFnr_offending_set[OF Sink_ENFnr] Sink_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation Sink: NetworkModel_IFS
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = Sink_offending_set"
  unfolding default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply (rule NetworkModel_withOffendingFlows.ENFnr_snds_weakrefl_instance[OF Sink_ENFnr Unassigned_default_candidate Unassigned_to_All])
     apply(simp_all)[2]

   apply(erule default_uniqueness_by_counterexample_IFS)
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
    apply(case_tac otherbot, simp_all)
    apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := SinkPool, vertex_2 := Unassigned)" in exI, simp)
    apply(rule_tac x="vertex_2" in exI, simp)
    apply(rule_tac x="{(vertex_1, vertex_2)}" in exI, simp)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := SinkPool, vertex_2 := Unassigned)" in exI, simp)
   apply(rule_tac x="vertex_2" in exI, simp)
   apply(rule_tac x="{(vertex_1, vertex_2)}" in exI, simp)

  apply(fact Sink_offending_set)
  done


  lemma NetworkModel_Sink: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales

hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties

end
