theory NM_NonInterference_impl
imports NM_NonInterference "../TopoS_Lists_Impl_Interface"
begin


code_identifier code_module NM_NonInterference_impl => (Scala) NM_NonInterference


section {* NetworkModel NonInterference Implementation*}

definition undirected_reachable :: "'v list_graph \<Rightarrow> 'v => 'v list" where
  "undirected_reachable G v = removeAll v (succ_tran (undirected G) v)"

lemma undirected_reachable_set: "set (undirected_reachable G v) = {e2. (v,e2) \<in> (set (edgesL (undirected G)))\<^sup>+} - {v}"
  by(simp add: undirected_succ_tran_set undirected_nodes_set undirected_reachable_def)

fun eval_model_set :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model_set G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"

(* equal: lemma eval_model_list_eq_set*)
fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> (let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]))"

lemma "P = Q \<Longrightarrow> (\<forall> x. P x) = (\<forall> x. Q x)"
  by(erule arg_cong)


lemma eval_model_eq_help1: "nP ` set (undirected_reachable G n) = set (map nP (undirected_reachable G n))"
  by auto
lemma eval_model_eq_help2: "set l = {Unrelated} \<Longrightarrow> remdups l = [Unrelated]"
 apply(induction l)
  apply simp
 apply(simp)
  apply (metis empty_iff insertI1 set_empty2 subset_singletonD)
 done
lemma eval_model_eq_help3: "(let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]) = (set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"
  apply simp
  apply(rule iffI)
  apply(erule disjE)
    apply simp
  apply (metis List.set.simps(2) empty_set set_eq_subset set_map set_remdups)
  apply(case_tac " nP ` set (undirected_reachable G n) = {}")
   apply fast
  apply(case_tac " nP ` set (undirected_reachable G n) = {Unrelated}")
  defer
  apply(subgoal_tac "nP ` set (undirected_reachable G n) \<subseteq> {Unrelated} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {Unrelated} \<Longrightarrow> False")
   apply fast
   apply (metis subset_singletonD)
  apply simp
  apply(rule disjI2)
  apply(simp only: eval_model_eq_help1)
   apply(simp add:eval_model_eq_help2)
  done

lemma eval_model_list_eq_set: "eval_model = eval_model_set"
  apply(insert eval_model_eq_help3)
  apply(simp add: fun_eq_iff)
  apply(rule allI)+
  apply fastforce
  done

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"



value[code] "eval_model 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. NM_NonInterference.default_node_properties)"
value[code] "eval_model 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4)] \<rparr>
    ((\<lambda>e. NM_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value[code] "eval_model 
    \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9),(9,8)] \<rparr>
    ((\<lambda>e. NM_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value[code] "eval_model 
    \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr>
    ((\<lambda>e. NM_NonInterference.default_node_properties)(1:= Interfering))"

value[code] "(undirected_reachable \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr> 1) = []" 
  (* apply(simp add: removeAll_def remdups_def undirected_reachable_def succ_tran_def trancl_list_impl_def trancl_impl_def) *)





definition NonInterference_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "NonInterference_offending_list = Generic_offending_list eval_model"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_NonInterference.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_NonInterference.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "NonInterference_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_NonInterference.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_NonInterference.default_node_properties P))"



lemma eval_model_correct: "valid_list_graph G \<Longrightarrow> NM_NonInterference.eval_model (list_graph_to_graph G) nP = eval_model G nP"
   apply(simp add: eval_model_list_eq_set)
   apply(rule all_nodes_list_I)
   apply(simp add: fun_eq_iff)
   apply(clarify)
   apply(rename_tac x)
   proof -
    fix x :: 'a
    have f1: "\<And>e_x1 e_x2. - insert (e_x1\<Colon>'a) (List.coset e_x2) = set e_x2 - {e_x1}"
      by (metis compl_coset insert_code(2) set_removeAll)
    hence f2: "\<And>e_x1 e_x e_x2. e_x1 ` (- insert (e_x\<Colon>'a) (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x2) e_x))) = set (map e_x1 (removeAll e_x (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x2) e_x))\<Colon>node_config list)"
      by (metis NM_NonInterference_impl.undirected_reachable_def eval_model_eq_help1 set_removeAll)
    have f3: "\<And>e_x2 e_x1. - insert (e_x2\<Colon>'a) (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x1) e_x2)) = NM_NonInterference.undirected_reachable (list_graph_to_graph e_x1) e_x2"
      using f1 by (metis NM_NonInterference.undirected_reachable_def succ_tran_correct undirected_correct)
    have "\<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> \<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<or> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      by metis
    moreover
    { assume "nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      hence "(nP x = Interfering \<longrightarrow> nP ` NM_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (NM_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
        using f2 f3 by (metis NM_NonInterference_impl.undirected_reachable_def image_set) }
    moreover
    { assume "\<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> \<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      hence "(nP x = Interfering \<longrightarrow> nP ` NM_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (NM_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
        using f2 f3 by (metis NM_NonInterference_impl.undirected_reachable_def image_set) }
    ultimately show "(nP x = Interfering \<longrightarrow> nP ` NM_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (NM_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
      by metis
  qed



interpretation NonInterference_impl:TopoS_List_Impl 
  where default_node_properties=NM_NonInterference.default_node_properties
  and eval_model_spec=NM_NonInterference.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_NonInterference.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_NonInterference.target_focus
  and offending_flows_impl=NonInterference_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=NonInterference_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_NonInterference)
  apply(rule conjI)
   apply(intro allI impI)
   apply(fact eval_model_correct)
  apply(simp)
 apply(rule conjI)
  apply(unfold NonInterference_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(intro allI impI)
  apply(simp only: eval_model_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis NonInterference.node_props.simps NonInterference.node_props_eq_node_props_formaldef)
 apply(simp only: NonInterference_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_NonInterference])
  apply(simp only: eval_model_correct)
 apply(simp)
done

section {* NonInterference packing *}
  definition NM_LIB_NonInterference :: "('v::vertex, node_config, unit) TopoS_packed" where
    "NM_LIB_NonInterference \<equiv> 
    \<lparr> nm_name = ''NonInterference'', 
      nm_target_focus = NM_NonInterference.target_focus,
      nm_default = NM_NonInterference.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = NonInterference_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = NonInterference_eval
      \<rparr>"
  interpretation NM_LIB_NonInterference_interpretation: TopoS_modelLibrary NM_LIB_NonInterference
      NM_NonInterference.eval_model NM_NonInterference.verify_globals
    apply(unfold TopoS_modelLibrary_def NM_LIB_NonInterference_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)




text {*Example: *}

  definition "example_graph  = \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9),(9,8)] \<rparr>"
  definition"example_conf = ((\<lambda>e. NM_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated, 8:= Unrelated, 9:= Unrelated))"
  
  value[code] "eval_model example_graph example_conf"
  value[code] "NonInterference_offending_list example_graph example_conf"



hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
