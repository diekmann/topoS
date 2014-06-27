theory NM_Subnets
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel Subnets *}

datatype subnets = Subnet nat | BorderRouter nat | Unassigned

definition default_node_properties :: "subnets"
  where  "default_node_properties \<equiv> Unassigned"

fun allowed_subnet_flow :: "subnets \<Rightarrow> subnets \<Rightarrow> bool" where
  "allowed_subnet_flow (Subnet s1) (Subnet s2) = (s1 = s2)" | 
  "allowed_subnet_flow (Subnet s1) (BorderRouter s2) = (s1 = s2)" |
  "allowed_subnet_flow (Subnet s1) Unassigned = True" | 
  "allowed_subnet_flow (BorderRouter s1) (Subnet s2) = False" |
  "allowed_subnet_flow (BorderRouter s1) Unassigned = True" | 
  "allowed_subnet_flow (BorderRouter s1) (BorderRouter s2) = True" |
  "allowed_subnet_flow Unassigned Unassigned  = True" |
  "allowed_subnet_flow Unassigned _  = False"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
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
  lemma Unassigned_only_to_Unassigned: "allowed_subnet_flow Unassigned e2 \<longleftrightarrow> e2 = Unassigned"
    by(case_tac e2, simp_all)
  lemma All_to_Unassigned: "\<forall> e1. allowed_subnet_flow e1 Unassigned"
    by (rule allI, case_tac e1, simp_all)
  lemma Unassigned_default_candidate: "\<forall> nP e1 e2. \<not> allowed_subnet_flow (nP e1) (nP e2) \<longrightarrow> \<not> allowed_subnet_flow Unassigned (nP e2)"
    apply(rule allI)+
    apply(case_tac "nP e2")
    apply simp
    apply simp
    by(simp add: All_to_Unassigned)
  lemma allowed_subnet_flow_refl: "\<forall> e. allowed_subnet_flow e e"
    by(rule allI, case_tac e, simp_all)
  lemma Subnets_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model allowed_subnet_flow"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    by simp
  lemma Subnets_ENF_refl: "NetworkModel_withOffendingFlows.ENF_refl eval_model allowed_subnet_flow"
    unfolding NetworkModel_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: Subnets_ENF)
     apply(simp add: allowed_subnet_flow_refl)
  done


  definition Subnets_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) set set" where
  "Subnets_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)} })"
  lemma Subnets_offending_set: 
  "NetworkModel_withOffendingFlows.set_offending_flows eval_model = Subnets_offending_set"
    apply(simp only: fun_eq_iff ENF_offending_set[OF Subnets_ENF] Subnets_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation Subnets: NetworkModel_ACS
where default_node_properties = NM_Subnets.default_node_properties
and eval_model = NM_Subnets.eval_model
and verify_globals = verify_globals
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = Subnets_offending_set"
  unfolding NM_Subnets.default_node_properties_def
  apply unfold_locales
    apply(rule ballI)
    apply (rule NetworkModel_withOffendingFlows.ENF_fsts_refl_instance[OF Subnets_ENF_refl Unassigned_default_candidate])[1]
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
    apply(rename_tac mysubnetcase)
    apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter mysubnetcase)" in exI, simp)
      apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
    apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := BorderRouter whatever)" in exI, simp)
      apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

   apply(fact Subnets_offending_set)
  done


  lemma NetworkModel_Subnets: "NetworkModel eval_model default_node_properties target_focus"
  unfolding target_focus_def by unfold_locales

subsection {* Analysis *}

lemma violating_configurations: "\<not> eval_model G nP \<Longrightarrow> 
    \<exists> (e1, e2) \<in> edges G. nP e1 = Unassigned \<or> (\<exists> s1. nP e1 = Subnet s1) \<or> (\<exists> s1. nP e1 = BorderRouter s1)"
  apply simp
  apply clarify
  apply(rename_tac a b)
  apply(case_tac "nP b", simp_all)
  apply(case_tac "nP a", simp_all)
  apply blast
  apply blast
  apply blast
  apply(case_tac "nP a", simp_all)
  apply blast
  apply blast
  apply(simp add: All_to_Unassigned)
done

lemma violating_configurations_exhaust_Unassigned: "\<And>n1 n2. (n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = Unassigned \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
    \<exists> (e1, e2) \<in> (edges G).  nP e1 = Unassigned \<and> nP e2 \<noteq> Unassigned "
  apply simp
  apply(case_tac "nP n2", simp_all)
  apply force
  apply force
done
lemma violating_configurations_exhaust_Subnet: "\<And>n1 n2. (n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = Subnet s1' \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
  \<exists> (e1, e2) \<in> (edges G). \<exists> s1 s2. nP e1 = Subnet s1 \<and> s1 \<noteq> s2 \<and> (nP e2 = Subnet s2 \<or> nP e2 = BorderRouter s2)"
  apply simp
  apply(case_tac "nP n2", simp_all)
  apply blast
  apply blast
done
lemma violating_configurations_exhaust_BorderRouter: "\<And>n1 n2. (n1, n2) \<in> (edges G) \<Longrightarrow> nP n1 = BorderRouter s1' \<Longrightarrow> \<not> allowed_subnet_flow (nP n1) (nP n2) \<Longrightarrow>
  \<exists> (e1, e2) \<in> (edges G). \<exists> s1 s2. nP e1 = BorderRouter s1 \<and> nP e2 = Subnet s2"
  apply simp
  apply(case_tac "nP n2")
  apply simp_all
  apply blast
done

text {* All cases where the model can become invalid: *}
theorem violating_configurations_exhaust: "\<not> eval_model G nP \<Longrightarrow> 
    \<exists> (e1, e2) \<in> (edges G). 
      nP e1 = Unassigned \<and> nP e2 \<noteq> Unassigned \<or> 
      (\<exists> s1 s2. nP e1 = Subnet s1 \<and> s1 \<noteq> s2 \<and> (nP e2 = Subnet s2 \<or> nP e2 = BorderRouter s2)) \<or> 
      (\<exists> s1 s2. nP e1 = BorderRouter s1 \<and> nP e2 = Subnet s2)"
  apply simp
  apply clarify
  apply(rename_tac n1 n2)
  apply(case_tac "nP n1", simp_all)
  apply(rename_tac s1)
  apply(drule_tac nP="nP" and s1'="s1" in violating_configurations_exhaust_Subnet, simp_all)
  apply blast
  apply(rename_tac s1)
  apply(drule_tac nP="nP" and s1'="s1" in violating_configurations_exhaust_BorderRouter, simp_all)
  apply blast
  apply(drule_tac nP="nP" in violating_configurations_exhaust_Unassigned, simp_all)
  apply blast
done


hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties

end
