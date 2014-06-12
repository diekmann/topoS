theory NM_SubnetsInGW
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel *}

datatype subnets = Member | InboundGateway | Unassigned

definition default_node_properties :: "subnets"
  where  "default_node_properties \<equiv> Unassigned"

fun allowed_subnet_flow :: "subnets \<Rightarrow> subnets \<Rightarrow> bool" where
  "allowed_subnet_flow Member _ = True" |
  "allowed_subnet_flow InboundGateway _ = True" |
  "allowed_subnet_flow Unassigned Unassigned = True" |
  "allowed_subnet_flow Unassigned InboundGateway = True"|
  "allowed_subnet_flow Unassigned Member = False"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets)  \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. allowed_subnet_flow (nP e1) (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus = False"


subsubsection {*Preleminaries*}
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
  lemma Unassigned_not_to_Member: "\<not> allowed_subnet_flow Unassigned Member"
    by(simp)
  lemma All_to_Unassigned: "allowed_subnet_flow e1 Unassigned"
    by (case_tac e1, simp_all)
  lemma Member_to_All: "allowed_subnet_flow Member e2"
    by (case_tac e2, simp_all)
  lemma Unassigned_default_candidate: "\<forall> nP e1 e2. \<not> allowed_subnet_flow (nP e1) (nP e2) \<longrightarrow> \<not> allowed_subnet_flow Unassigned (nP e2)"
    apply(rule allI)+
    apply(case_tac "nP e2")
      apply simp
     apply(case_tac "nP e1")
       apply(simp_all)[3]
    by(simp add: All_to_Unassigned)
  lemma allowed_subnet_flow_refl: "allowed_subnet_flow e e"
    by(case_tac e, simp_all)
  lemma SubnetsInGW_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model allowed_subnet_flow"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    by simp
  lemma SubnetsInGW_ENF_refl: "NetworkModel_withOffendingFlows.ENF_refl eval_model allowed_subnet_flow"
    unfolding NetworkModel_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: SubnetsInGW_ENF)
    apply(simp add: allowed_subnet_flow_refl)
  done

  definition SubnetsInGW_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) set set" where
  "SubnetsInGW_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)} })"
  lemma SubnetsInGW_offending_set: 
  "NetworkModel_withOffendingFlows.set_offending_flows eval_model = SubnetsInGW_offending_set"
    apply(simp only: fun_eq_iff ENF_offending_set[OF SubnetsInGW_ENF] SubnetsInGW_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done

interpretation SubnetsInGW: NetworkModel_ACS
where default_node_properties = NM_SubnetsInGW.default_node_properties
and eval_model = NM_SubnetsInGW.eval_model
and verify_globals = verify_globals
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = SubnetsInGW_offending_set"
  unfolding NM_SubnetsInGW.default_node_properties_def
  apply unfold_locales

    apply(rule ballI)
    thm NetworkModel_withOffendingFlows.ENF_fsts_refl_instance[OF SubnetsInGW_ENF_refl Unassigned_default_candidate]
    apply(rule NetworkModel_withOffendingFlows.ENF_fsts_refl_instance[OF SubnetsInGW_ENF_refl Unassigned_default_candidate])
      apply(simp_all)[2]

   apply(erule default_uniqueness_by_counterexample_ACS)
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(case_tac otherbot, simp_all)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := Member)" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := Member)" in exI, simp)
   apply(rule_tac x="vertex_1" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  
  apply(fact SubnetsInGW_offending_set)
  done



  lemma NetworkModel_SubnetsInGW: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales

 
hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties

end
