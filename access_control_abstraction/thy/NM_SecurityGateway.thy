theory NM_SecurityGateway
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel SecurityGateway *}

datatype secgw_member = SecurityGateway | DomainMember | Unassigned

definition default_node_properties :: "secgw_member"
  where  "default_node_properties = Unassigned"

fun allowed_secgw_flow :: "secgw_member \<Rightarrow> secgw_member \<Rightarrow> bool" where
  "allowed_secgw_flow SecurityGateway _ = True" |
  "allowed_secgw_flow DomainMember SecurityGateway = True" |
  "allowed_secgw_flow DomainMember DomainMember = False" |
  "allowed_secgw_flow DomainMember Unassigned = True" |
  "allowed_secgw_flow Unassigned Unassigned = True" |
  "allowed_secgw_flow Unassigned _ = False"


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> secgw_member) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. e1 \<noteq> e2 \<longrightarrow> allowed_secgw_flow (nP e1) (nP e2))"


(*Idea: only one secgw? *)
fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> secgw_member) \<Rightarrow> 'b \<Rightarrow> bool" where
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


subsection {*ENRnr*}
  lemma SecurityGateway_ENRnr: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl eval_model allowed_secgw_flow"
    by(simp add: NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl_def)
  lemma Unassigned_botdefault: "\<forall> e1 e2. e2 \<noteq> Unassigned \<longrightarrow> \<not> allowed_secgw_flow e1 e2 \<longrightarrow> \<not> allowed_secgw_flow Unassigned e2"
    apply(rule allI)+
    apply(case_tac e2)
    apply(simp_all)
    done
  lemma Unassigned_only_to_Unassigned: "allowed_secgw_flow Unassigned e2 \<longleftrightarrow> e2 = Unassigned"
    by(case_tac e2, simp_all)
  lemma All_to_Unassigned: "\<forall> e1. allowed_secgw_flow e1 Unassigned"
    by (rule allI, case_tac e1, simp_all)
  lemma Unassigned_default_candidate: "\<forall>e1 e2. \<not> allowed_secgw_flow e1 e2 \<longrightarrow> \<not> allowed_secgw_flow Unassigned e2"
    apply(rule allI)+
    apply(case_tac "e1")
     apply simp
    apply simp
    apply(case_tac "e2")
     apply simp_all[3] defer
     apply simp
    done
  
  definition SecurityGateway_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> secgw_member) \<Rightarrow> ('v \<times> 'v) set set" where
  "SecurityGateway_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_secgw_flow (nP e1) (nP e2)} })"
  lemma SecurityGateway_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = SecurityGateway_offending_set"
    apply(simp only: fun_eq_iff ENFnr_offending_set[OF SecurityGateway_ENRnr] SecurityGateway_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation SecurityGateway: NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = SecurityGateway_offending_set"
  unfolding target_focus_def
  unfolding default_node_properties_def
  apply unfold_locales

  (* only remove target_focus: *)
  apply(rule conjI) prefer 2 apply(simp) apply(simp only:HOL.not_False_eq_True HOL.simp_thms(15)) apply(rule impI)
  
  apply (rule NetworkModel_withOffendingFlows.ENFnr_fsts_weakrefl_instance[OF _ SecurityGateway_ENRnr Unassigned_botdefault All_to_Unassigned])
  apply(auto)[3]

 apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(case_tac otherbot, simp_all)
  apply(rename_tac secgwcase)
  apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := secgwcase)" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(rename_tac membercase)
  apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := SecurityGateway)" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

  apply(fact SecurityGateway_offending_set)
  done




hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties


end
