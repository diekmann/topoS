theory NetworkModel_Helper
imports Main NetworkModel_Interface NetworkModel_Util 
  NetworkModel_ENF
  NetworkModel_withOffendingFlows_lemmata
  vertex_example_simps
begin

text {*Imports a lot of usefull NetworkModelling lemmata.*}



lemma (in NetworkModel_preliminaries) eval_model_valid_remove_flattened_offending_flows:
  "valid_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr> \<Longrightarrow> eval_model \<lparr>nodes = nodesG, edges = edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
  proof -
  assume a1: "valid_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr>"
  from remove_offending_flows_imp_model_valid have 1:
    "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. eval_model \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      apply(simp add: graph_ops)
      by (metis NetworkModel_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
  have 2: "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. f \<subseteq> ( \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP))"
    by blast
  from 2 have 3: "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. 
    edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<subseteq> edgesG - f" by blast

   from mono_eval_model[OF a1] 1 3 show ?thesis 
   by (metis (lifting, no_types) Diff_subset a1 defined_offending delete_edges_simp2 delete_edges_valid ex_in_conv graph.select_convs(1) graph.select_convs(2) mono_eval_model)
  qed

end
