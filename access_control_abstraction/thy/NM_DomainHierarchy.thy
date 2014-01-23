theory NM_DomainHierarchy
imports NetworkModel_Interface NetworkModel_Helper datatype_DomainHierarchy
begin

(*deprecated*)
end

definition default_node_properties :: "domainName"
  where  "default_node_properties = Unassigned"


fun eval_model :: "'v graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> edges G. (nP e2) \<le> (nP e1)) "

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> nodes G. valid_hierarchy_pos tree (nP v))"

definition target_focus :: "bool" where "target_focus = False"



section{*preliminaries*}
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
  lemma DomainHierarchy_ENF: "NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form eval_model (\<lambda> e1 e2. e2 \<le> e1)"
    unfolding NetworkModel_withOffendingFlows.eval_model_all_edges_normal_form_def
    by simp
  lemma DomainHierarchy_ENF_refl: "NetworkModel_withOffendingFlows.ENF_refl eval_model (\<lambda> e1 e2. e2 \<le> e1)"
    unfolding NetworkModel_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: DomainHierarchy_ENF)
     apply(simp)
  done

  definition DomainHierarchy_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> ('v \<times> 'v) set set" where
  "DomainHierarchy_offending_set G nP = (if eval_model G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> (nP e2) \<le> (nP e1)} })"
  lemma DomainHierarchy_offending_set: "NetworkModel_withOffendingFlows.set_offending_flows eval_model = DomainHierarchy_offending_set"
    apply(simp only: fun_eq_iff NetworkModel_withOffendingFlows.ENF_offending_set[OF DomainHierarchy_ENF] DomainHierarchy_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto split:split_split_asm split_split)
  done

interpretation DomainHierarchy: NetworkModel
where default_node_properties = default_node_properties
and eval_model = eval_model
and verify_globals = verify_globals
and target_focus = target_focus
  where "NetworkModel_withOffendingFlows.set_offending_flows eval_model = DomainHierarchy_offending_set"
  unfolding target_focus_def
  apply unfold_locales
     apply(rule conjI) prefer 2 apply(simp) apply(simp only:HOL.not_False_eq_True HOL.simp_thms(15)) apply(rule impI)
         apply(rename_tac G nP f i)
         thm ENF_fsts_refl_instance[OF _ DomainHierarchy_ENF_refl]
         apply(rule_tac G=G and nP=nP and f=f in ENF_fsts_refl_instance[OF _ DomainHierarchy_ENF_refl])
        apply(simp)
       apply(metis Unassigned_bot Unassigned_bot_Unique default_node_properties_def)
      apply(simp)
     apply(simp)
    apply(simp)

  (*unique default*)
   apply (simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
      NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
      NetworkModel_withOffendingFlows.is_offending_flows_def
      default_node_properties_def)
   apply (simp add:graph_ops)
   apply (simp split: split_split_asm split_split add:prod_case_beta)
   apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
     apply(rule conjI)
    apply(simp add: valid_graph_def)
   apply(frule_tac Unassigned_bot_step)
   apply(erule_tac P="\<lambda>x. x -- Unassigned \<le> otherbot" in exE)
   apply(rule_tac x="(\<lambda> x. Unassigned)(vertex_1 := Unassigned, vertex_2 := x--Unassigned)" in exI, simp)
   --"Only Unassigned fulfills Unassigned \<le> x--Unassigned; for any other value for vertex_1 the model becoms true as vertex_1' \<ge> x--Unassigned"
   apply(rule_tac x="vertex_1" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)

 apply(fact DomainHierarchy_offending_set)
done


lemma DomainHierarchy_NetworkModel: "NetworkModel eval_model default_node_properties target_focus"
  by(unfold_locales)

(*
text {* Both Leaf and a foreign Department can be defaults under cirtain circumstances! *}
lemma KindOf_unique_default:
  "otherbot = ''LMU''--Leaf \<Longrightarrow> 
    \<exists> G p g i f. valid_graph (G::nat graph) \<and> \<not> eval_model G p g \<and> f \<in> set (DomainHierarchy.list_offending_flows G p g) \<and> 
     eval_model (delete_edges G f) p g \<and> i \<in> fsts f \<and> eval_model G (p(i := otherbot)) g
     "
  unfolding default_node_properties_def
  apply(simp)
  apply (simp add: 
      DomainHierarchy.is_offending_flows_min_set_def
      DomainHierarchy.is_offending_flows_def)
  apply (simp add:delete_edges_set_edges)
  apply (simp split: split_split_asm split_split add:prod_case_beta)
  apply(rule_tac x="\<lparr> nodes=[1,2], edges = [(1,2)] \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_record_impl)
  apply(rule_tac x="(\<lambda> x. Unassigned)(1 := Unassigned, 2 := ''LMU''--Leaf)" in exI, simp)
  apply(rule_tac x="1" in exI, simp)
   apply(rule_tac x="[(1,2)]" in exI, simp)
  done
*)



hide_const (open) eval_model_mono
hide_const (open) eval_model verify_globals target_focus default_node_properties

end
