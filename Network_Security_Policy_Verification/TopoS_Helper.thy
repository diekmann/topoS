theory TopoS_Helper
imports Main TopoS_Interface TopoS_Util 
  TopoS_ENF
  vertex_example_simps
begin

text {*Imports a lot of usefull NetworkModelling lemmata.*}



lemma (in SecurityInvariant_preliminaries) sinvar_valid_remove_flattened_offending_flows:
  "valid_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr> \<Longrightarrow> sinvar \<lparr>nodes = nodesG, edges = edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
  proof -
  assume a1: "valid_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr>"
  from removing_offending_flows_makes_invariant_hold have 1:
    "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. sinvar \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      apply(simp add: graph_ops)
      by (metis SecurityInvariant_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
  have 2: "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. f \<subseteq> ( \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP))"
    by blast
  from 2 have 3: "\<forall>f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP. 
    edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<subseteq> edgesG - f" by blast

   from mono_sinvar[OF a1] 1 3 show ?thesis 
   by (metis (lifting, no_types) Diff_subset a1 defined_offending delete_edges_simp2 delete_edges_valid ex_in_conv graph.select_convs(1) graph.select_convs(2) mono_sinvar)
  qed

end
