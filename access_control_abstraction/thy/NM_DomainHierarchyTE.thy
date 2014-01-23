theory NM_DomainHierarchyTE
imports NetworkModel_Interface NetworkModel_Helper datatype_DomainHierarchy
begin


fun domainNameChopOne :: "domainName \<Rightarrow> domainName" where
  "domainNameChopOne Unassigned = Leaf" | (* yes, lift bot to top *)
  "domainNameChopOne Leaf = Leaf" |
  "domainNameChopOne (name--Leaf) = Leaf" |
  "domainNameChopOne (name--dpt) = name--(domainNameChopOne dpt)"

value[code] "domainNameChopOne (''i8''--''CoffeeMachine''--Leaf)"
value[code] "domainNameChopOne (''i8''--''CoffeeMachine''--''CoffeeSlave''--Leaf)"
value[code] "domainNameChopOne (''i8''--''CoffeeMachine''--Unassigned)"
value[code] "domainNameChopOne (''i8''--Leaf)"
value[code] "domainNameChopOne (Leaf)"

theorem chopOne_increase: "dn \<le> domainNameChopOne dn"
  apply(induction dn)
  apply(rename_tac name dpt)
  apply(drule_tac x="name" in prepend_domain)
    apply(case_tac dpt)
     apply simp
     apply simp
     apply simp
   apply simp
   apply simp
done

lemma chopOneContinue: "dpt \<noteq> Leaf \<Longrightarrow> domainNameChopOne (name -- dpt) = name -- domainNameChopOne (dpt)"
apply(case_tac dpt)
by simp_all

fun domainNameChop :: "domainName \<Rightarrow> nat \<Rightarrow> domainName" where
  "domainNameChop Unassigned 0 = Unassigned" |
  "domainNameChop Unassigned _ = Leaf" | (* lift bot to top *)
  "domainNameChop Leaf _ = Leaf" |
  "domainNameChop namedpt 0 = namedpt" |
  "domainNameChop namedpt (Suc n) = domainNameChop (domainNameChopOne namedpt) n"

value "domainNameChop (''i8''--''CoffeeMachine''--Leaf) 2"
value "domainNameChop (''i8''--''CoffeeMachine''--''CoffeeSlave''--Leaf) 2"
value "domainNameChop (''i8''--''CoffeeMachine''--Unassigned) 2"
value "domainNameChop (''i8''--Leaf) 0"
value "domainNameChop (Leaf) 8"


lemma chop0[simp]: "domainNameChop dn 0 = dn"
  apply(case_tac dn)
by simp_all


value [code]"(domainNameChopOne^^2) (''d1''--''d2''--''d3''--Leaf)"

text {* domainNameChop is equal to applying n times chop one *}
lemma domainNameChopFunApply: "domainNameChop dn n = (domainNameChopOne^^n) dn"
  apply(induction dn)
  defer
  apply simp
   apply(induction n) apply simp apply simp
   apply(induction n)
    apply simp
    apply simp
    apply (metis chop0 domainNameChop.simps(2) domainNameChopOne.simps(1) domainNameChopOne.simps(2) nat.exhaust)
  apply(induction n)
   apply simp
  apply simp
  apply (metis chopOneContinue domainName.exhaust domainNameChop.simps(2) domainNameChop.simps(3) domainNameChop.simps(5) domainNameChopOne.simps(1) 
    domainNameChopOne.simps(2) domainNameChopOne.simps(3) funpow_swap1)
done

lemma domainNameChopRotateSuc: "domainNameChop dn (Suc n) = domainNameChopOne (domainNameChop dn n)"
by(simp add: domainNameChopFunApply)

lemma domainNameChopRotate: "domainNameChop (domainNameChopOne dn) n = domainNameChopOne (domainNameChop dn n)"
  apply(subgoal_tac "domainNameChop (domainNameChopOne dn) n = domainNameChop dn (Suc n)")
  apply simp
  apply(simp add: domainNameChopFunApply)
  apply(case_tac dn)
by(simp_all)


theorem chop_increase_hierarchy: "dn \<le> domainNameChop dn n"
  apply(induction n)
  apply(simp)
  apply(case_tac dn)
  apply(rename_tac name dpt)
  apply (simp)
  apply(simp add:domainNameChopRotate)
   apply (metis chopOne_increase less_eq_refl)
   apply simp
   apply simp
done

corollary [simp]: "dn \<le> domainNameChopOne ((domainNameChopOne ^^ n) (dn))"
by (metis chop_increase_hierarchy domainNameChopFunApply domainNameChopRotateSuc)
  


record node_config = 
    level::domainName
    trust::nat

definition default_node_properties :: "node_config"
  where  "default_node_properties = \<lparr> level = Unassigned, trust = 0 \<rparr>"

fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. let c1=(nP e1) in 
    (level (nP e2)) \<le> domainNameChop (level c1) (trust c1))"

text {* Assigning unassigned a trust level is syntactically invalid, thus, case can be ignored *}
fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> nodes G. 
    valid_hierarchy_pos tree (level (nP v)) \<and> 
    (level (nP v) = Unassigned \<longrightarrow> trust (nP v) = 0)
   )"


(* Unassigned with a trustlevel other than 0 is syntactically invalid *)
lemma "verify_globals \<lparr> nodes=set [1,2,3], edges=set [] \<rparr> (\<lambda>n. default_node_properties) (Department ''TUM'' [])"
  by (simp add: default_node_properties_def)
lemma "trustlevel \<noteq> 0 \<Longrightarrow> verify_globals \<lparr> nodes=set [1,2,3], edges=set [] \<rparr> ((\<lambda>n. default_node_properties)(2 := \<lparr> level = Unassigned, trust = trustlevel \<rparr> )) (Department ''TUM'' []) 
  \<Longrightarrow> False"
  by (simp add: default_node_properties_def)

text {* We show that verify globals is false if some Unassigned node has trust other than 0 *}
theorem "\<exists>n \<in> (nodes G). level (nP n) = Unassigned \<and> trust (nP n) \<noteq> 0 \<Longrightarrow> \<not> verify_globals G nP tree"
apply(simp add: Bex_def)
apply(erule exE) apply(rename_tac x)
apply(rule_tac x=x in exI)
apply simp
done

definition target_focus :: "bool" where "target_focus = False"


lemma eval_model_nolet: "eval_model G nP = ((\<forall>(e1, e2) \<in> edges G. level (nP e2) \<le> domainNameChop (level (nP e1)) (trust (nP e1))) )"
apply simp
by (metis (full_types))




lemma eval_model_mono: "NetworkModel_withOffendingFlows.eval_model_mono eval_model"
  apply(rule_tac NetworkModel_withOffendingFlows.eval_model_mono_I_proofrule)
   apply(auto)
  apply(rename_tac nP e1 e2 N E' e1' e2' E)
 apply(blast)
 done


interpretation NetworkModel_preliminaries
where eval_model = eval_model
and verify_globals = verify_globals
  apply unfold_locales
     apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
     apply(erule_tac exE)
     apply(rename_tac list_edges)
          apply(rule_tac ff="list_edges" in NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono])
     apply(auto)[5]
    apply(auto simp add: NetworkModel_withOffendingFlows.is_offending_flows_def graph_ops)[1]
   apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_eval_model_mono[OF eval_model_mono])
  apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
done


section {*ENF*}
  lemma DomainHierarchyTE_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model (\<lambda> e1 e2. (level e2) \<le> domainNameChop (level e1) (trust e1))"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    apply(simp only: eval_model_nolet)
    by simp

  definition DomainHierarchyTE_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) set set" where
  "DomainHierarchyTE_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> let c1=(nP e1) in \<not> (level (nP e2)) \<le> domainNameChop (level c1) (trust c1)} })"
  lemma DomainHierarchyTE_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = DomainHierarchyTE_offending_set"
    apply(simp only: fun_eq_iff NetworkModel_withOffendingFlows.ENF_offending_set[OF DomainHierarchyTE_ENF] DomainHierarchyTE_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto split:split_split_asm split_split simp add: Let_def)
  done


interpretation DomainHierarchyTE: NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus
where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = DomainHierarchyTE_offending_set"
  unfolding target_focus_def
  unfolding default_node_properties_def
  apply unfold_locales

  apply(simp only: eval_model.simps)
  apply(simp add: Set.Ball_def)
  apply clarify
  apply (simp only: NetworkModel_withOffendingFlows.set_offending_flows_def)
  apply (simp only: NetworkModel_withOffendingFlows.is_offending_flows_min_set_def)
  apply(simp add: Set.Ball_def)
  apply (simp only: NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply(simp add: Set.Ball_def)
  apply (simp add:graph_ops)
  apply (auto simp add:Unassigned_bot Unassigned_bot_Unique Leaf_Top Let_def)
   using Unassigned_bot chop_increase_hierarchy apply (metis Unassigned_bot_Unique set_mp)


  apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(case_tac otherbot)
  apply(rename_tac dn trustlevel)
  apply(simp add:domainNameChopFunApply)

 apply(case_tac trustlevel)
 --"copy of proof from domain hierarchy"
 apply simp
 apply(frule_tac Unassigned_bot_step)
  apply(erule_tac P="\<lambda>x. x -- Unassigned \<le> dn" in exE)
  apply(rule_tac x="(\<lambda> x. \<lparr> level = Unassigned, trust= 0 \<rparr>)(vertex_1 := \<lparr> level = Unassigned, trust= 0 \<rparr>, vertex_2 := \<lparr> level = x--Unassigned, trust= 0 \<rparr>)" in exI, simp)
  --"Only Unassigned fulfills Unassigned \<le> x--Unassigned; for any other value for vertex_1 the model becoms true as vertex_1' \<ge> x--Unassigned"
  apply(rule_tac x="vertex_1" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
 --"end copy"


 apply simp
apply(case_tac dn)
apply(rename_tac name dpt)
  apply(rule_tac x="(\<lambda> x. \<lparr> level = Unassigned, trust= 0 \<rparr>)(vertex_1 := \<lparr> level = Unassigned, trust= 0 \<rparr>, vertex_2 := \<lparr> level = name--dpt, trust= 0 \<rparr>)" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

  apply(rule_tac x="(\<lambda> x. \<lparr> level = Unassigned, trust= 0 \<rparr>)(vertex_1 := \<lparr> level = Unassigned, trust= 0 \<rparr>, vertex_2 := \<lparr> level = Leaf, trust= 0 \<rparr>)" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

  apply simp
  (* problem: not unique for unassigned, thus we lift it with chop to Leaf *)
  apply(rule_tac x="(\<lambda> x. \<lparr> level = Unassigned, trust= 0 \<rparr>)(vertex_1 := \<lparr> level = Unassigned, trust= 0 \<rparr>, vertex_2 := \<lparr> level = Leaf, trust= 0 \<rparr>)" in exI, simp)
  apply(rule_tac x="vertex_1" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply (metis domainNameChop.simps(2) domainNameChopFunApply domainNameChopRotateSuc order_eq_iff)


  apply(fact DomainHierarchyTE_offending_set)
done




lemma DomainHierarchyTE_NetworkModel: "NetworkModel eval_model default_node_properties target_focus"
  by(unfold_locales)



hide_const (open) eval_model verify_globals target_focus

end
