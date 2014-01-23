theory NM_Dependability_impl
imports NM_Dependability NetworkModel_Lists_Impl_Interface FiniteListGraph_Impl
begin


code_identifier code_module NM_Dependability_impl => (Scala) NM_Dependability


section {* NetworkModel Dependability implementation *}


text {* Less-equal other nodes depend on the output of a node than its dependability level. *}
fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (num_reachable G e1) \<le> (nP e1))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


value "eval_model 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 3)"
value "eval_model 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 2)"





text{* Generate a valid configuration to start from: *}
   fun fix_nP :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<Rightarrow> dependability_level)" where
      "fix_nP G nP = (\<lambda>v. let nr = num_reachable G v in (if nr \<le> (nP v) then (nP v) else nr))"

   theorem fix_nP_impl_correct: "valid_list_graph G \<Longrightarrow> fix_nP G nP  = NM_Dependability.fix_nP (list_graph_to_graph G) nP"
   by(simp add: num_reachable_correct fun_eq_iff)

   value[code] "let G = \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,1), (2,1), (3,1), (4,1), (1,2), (1,3)] \<rparr> in (let nP = fix_nP G (\<lambda>e. 0) in map (\<lambda>v. nP v) (nodesL G))"


   value[code] "let G = \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,1)] \<rparr> in (let nP = fix_nP G (\<lambda>e. 0) in map (\<lambda>v. nP v) (nodesL G))"



definition Dependability_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "Dependability_offending_list = Generic_offending_list eval_model"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_Dependability.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_Dependability.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Dependability_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_Dependability.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_Dependability.default_node_properties P))"



lemma eval_model_correct: "valid_list_graph G \<Longrightarrow> NM_Dependability.eval_model (list_graph_to_graph G) nP = eval_model G nP"
   apply(simp)
   apply(rule all_edges_list_I)
   apply(simp add: fun_eq_iff)
   apply(clarify)
   apply(rename_tac x)
   apply(drule_tac v="x" in  num_reachable_correct)
  apply presburger
done



interpretation Dependability_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_Dependability.default_node_properties
  and eval_model_spec=NM_Dependability.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_Dependability.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_Dependability.target_focus
  and offending_flows_impl=Dependability_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Dependability_eval
 apply(unfold_locales)
      apply(fact eval_model_correct)
     apply(simp add: list_graph_to_graph_def)
     apply(unfold Dependability_offending_list_def)
      apply(rule Generic_offending_list_correct)
     apply(simp)
     apply(clarify)
     apply(simp)
     apply(simp add: FiniteListGraph.num_reachable_correct)
    apply(simp add: list_graph_to_graph_def)
    apply(simp only: NetModel_node_props_def)
   apply(metis Dependability.node_props.simps Dependability.node_props_eq_node_props_formaldef)
   apply(simp only: Dependability_eval_def)
   apply(rule_tac target_focus=NM_Dependability.target_focus in NetworkModel_eval_impl_proofrule)
    apply(unfold_locales) (*instance*)
   apply(fact eval_model_correct)
  apply(simp)
done

section {* Dependability packing *}
  definition NM_LIB_Dependability :: "('v::vertex, NM_Dependability.dependability_level, unit) NetworkModel_packed" where
    "NM_LIB_Dependability \<equiv> 
    \<lparr> nm_name = ''Dependability'', 
      nm_target_focus = NM_Dependability.target_focus,
      nm_default = NM_Dependability.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = Dependability_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Dependability_eval
      \<rparr>"
  interpretation NM_LIB_Dependability_interpretation: NetworkModel_modelLibrary NM_LIB_Dependability
      NM_Dependability.eval_model NM_Dependability.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_Dependability_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text {*Example: *}
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in eval_model G  ((\<lambda> n. NM_Dependability.default_node_properties)(1:=3, 2:=2, 3:=1, 4:=0, 8:=2, 9:=2, 10:=0))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in eval_model G  ((\<lambda> n. NM_Dependability.default_node_properties)(1:=10, 2:=10, 3:=10, 4:=10, 8:=10, 9:=10, 10:=10))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in eval_model G  ((\<lambda> n. 2))"
  
  value "let G = \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      in Dependability_eval G  \<lparr>node_properties=[1\<mapsto>3, 2\<mapsto>2, 3\<mapsto>1, 4\<mapsto>0, 8\<mapsto>2, 9\<mapsto>2, 10\<mapsto>0], model_global_properties=() \<rparr>"
  
  value "Dependability_offending_list \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> (\<lambda> n. 2)"

hide_fact (open) eval_model_correct
hide_const (open) eval_model verify_globals NetModel_node_props

end
