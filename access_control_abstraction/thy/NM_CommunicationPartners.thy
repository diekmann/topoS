theory NM_CommunicationPartners
imports NetworkModel_Interface NetworkModel_Helper
begin

section {* NetworkModel CommunicationPartners *}


text{*
Idea of this security requirement model:
  Only some nodes can communicate with Master nodes.
    It constraints who may access master nodes, Master nodes cann access the world (except other prohibited master nodes).
  A node configured as Master has a list of nodes that can access it.
  Also, in order to be able to access a Master node, the sender must be denoted as a node we Care about.
  By default, all nodes are set to DonTCare, thus they can no access Master nodes. But they can access 
  all other DontCare nodes and Care nodes.

  TL;DR: An access control list determines who can access a master node.
*}
datatype 'v node_config = DontCare | Care | Master "'v list"

definition default_node_properties :: "'v node_config"
  where  "default_node_properties = DontCare"

text{* Unrestricted accesses among DontCare nodes! *}

fun allowed_flow :: "'v node_config \<Rightarrow> 'v \<Rightarrow> 'v node_config \<Rightarrow> 'v \<Rightarrow> bool" where
  "allowed_flow DontCare s DontCare r = True" |
  "allowed_flow DontCare s Care r = True" |
  "allowed_flow DontCare s (Master _) r = False" |
  "allowed_flow Care s Care r = True" |
  "allowed_flow Care s DontCare r = True" |
  "allowed_flow Care s (Master M) r = (s \<in> set M)" |
  "allowed_flow (Master _) s (Master M) r = (s \<in> set M)" |
  "allowed_flow (Master _) s Care r = True" |
  "allowed_flow (Master _) s DontCare r = True" 


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (s,r) \<in> edges G. s \<noteq> r \<longrightarrow> allowed_flow (nP s) s (nP r) r)"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition target_focus :: "bool" where "target_focus = False"



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


subsection {*ENRnr*}
  lemma CommunicationPartners_ENRnrSR: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl_SR eval_model allowed_flow"
    by(simp add: NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_not_refl_SR_def)
  lemma Unassigned_weakrefl: "\<forall> s r. allowed_flow DontCare s DontCare r"
    by(simp)
  lemma Unassigned_botdefault: "\<forall> s r. (nP r) \<noteq> DontCare \<longrightarrow> \<not> allowed_flow (nP s) s (nP r) r \<longrightarrow> \<not> allowed_flow DontCare s (nP r) r"
    apply(rule allI)+
    apply(case_tac "nP r")
      apply(simp_all)
    apply(case_tac "nP s")
      apply(simp_all)
    done
  lemma  "\<not> allowed_flow DontCare s (Master M) r" by(simp)
    
  lemma All_to_Unassigned: "\<forall> s r. allowed_flow (nP s) s DontCare r"
    by (rule allI, rule allI, case_tac "nP s", simp_all)
  lemma Unassigned_default_candidate: "\<forall> s r. \<not> allowed_flow (nP s) s (nP r) r \<longrightarrow> \<not> allowed_flow DontCare s (nP r) r"
    apply(rule allI)+
    apply(case_tac "nP s")
      apply(simp_all)
     apply(case_tac "nP r")
       apply(simp_all)
    apply(case_tac "nP r")
      apply(simp_all)
    done
  
  definition CommunicationPartners_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "CommunicationPartners_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_flow (nP e1) e1 (nP e2) e2} })"
  lemma CommunicationPartners_offending_set: 
  "NetworkModel_withOffendingFlows.set_offending_flows eval_model = CommunicationPartners_offending_set"
    apply(simp only: fun_eq_iff ENFnrSR_offending_set[OF CommunicationPartners_ENRnrSR] CommunicationPartners_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done


interpretation CommunicationPartners: NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = CommunicationPartners_offending_set"
  unfolding target_focus_def
  unfolding default_node_properties_def
  apply unfold_locales

    apply(frule NetworkModel_withOffendingFlows.ENFnrSR_offending_case1[OF CommunicationPartners_ENRnrSR])

  (* only remove target_focus: *)
    apply(rule conjI) prefer 2 apply(simp) apply(simp only:HOL.not_False_eq_True HOL.simp_thms(15)) apply(rule impI)
  
    apply (rule_tac f="f" in NetworkModel_withOffendingFlows.ENFnrSR_fsts_weakrefl_instance[OF _ CommunicationPartners_ENRnrSR Unassigned_weakrefl Unassigned_botdefault All_to_Unassigned])
      apply(simp)
     apply(simp)
    apply(simp)

   (*unique*)
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
   apply (simp add:graph_ops)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
   apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(case_tac otherbot, simp_all)
    apply(rule_tac x="(\<lambda> x. DontCare)(vertex_1 := DontCare, vertex_2 := Master [vertex_1])" in exI, simp)
    apply(rule_tac x="vertex_1" in exI, simp)
    apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
   apply(rename_tac M) (*case Master M*)
   apply(rule_tac x="(\<lambda> x. DontCare)(vertex_1 := DontCare, vertex_2 := (Master (vertex_1#M')))" in exI, simp)
   apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

  apply(fact CommunicationPartners_offending_set)
  done




hide_fact (open) eval_model_mono   
hide_const (open) eval_model verify_globals target_focus default_node_properties


end
