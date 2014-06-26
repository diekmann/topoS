theory FiniteListGraph
imports 
  FiniteGraph
  "$AFP/Transitive-Closure/Transitive_Closure_List_Impl"
begin

section {*Specification of a finite graph, implemented by lists*}

text{* A graph G=(V,E) consits of a list of vertices V, also called nodes, 
       and a list of edges E. The edges are tuples of vertices.
       Using lists instead of sets, code can be easily created. *}

  record 'v list_graph =
    nodesL :: "'v list"
    edgesL :: "('v \<times>'v) list"

text{*Correspondence the FiniteGraph*}
  definition list_graph_to_graph :: "'v list_graph \<Rightarrow> 'v graph" where 
    "list_graph_to_graph G = \<lparr> nodes = set (nodesL G), edges = set (edgesL G) \<rparr>"


  definition valid_list_graph_axioms :: "'v list_graph \<Rightarrow> bool" where
    "valid_list_graph_axioms G \<longleftrightarrow> fst` set (edgesL G) \<subseteq> set (nodesL G) \<and> snd` set (edgesL G) \<subseteq> set (nodesL G)"


  lemma valid_list_graph_iff_valid_graph: "valid_graph (list_graph_to_graph G) \<longleftrightarrow> valid_list_graph_axioms G"
  by(simp add: list_graph_to_graph_def valid_graph_def valid_list_graph_axioms_def)


  text{*We say a list_graph is valid if it fulfills the graph axioms and its lists are distinct*}
  definition valid_list_graph::"('v) list_graph \<Rightarrow> bool" where
   "valid_list_graph G = (distinct (nodesL G) \<and> distinct (edgesL G) \<and> valid_list_graph_axioms G)"


section{*FiniteListGraph operations*}

  text {* Adds a node to a graph. *}
  definition add_node :: "'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "add_node v G = \<lparr> nodesL = (if v \<in> set (nodesL G) then nodesL G else v#nodesL G), edgesL=edgesL G \<rparr>"

  text {* Adds an edge to a graph. *}
  definition add_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "add_edge v v' G = (add_node v (add_node v' G)) \<lparr>edgesL := (if (v, v') \<in> set (edgesL G) then edgesL G else (v, v')#edgesL G) \<rparr>"

  text {* Deletes a node from a graph. Also deletes all adjacent edges. *}
  definition delete_node :: "'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
  "delete_node v G = \<lparr> 
    nodesL = remove1 v (nodesL G), edgesL = [(e1,e2) \<leftarrow> (edgesL G). e1 \<noteq> v \<and> e2 \<noteq> v]
    \<rparr>"

  text {* Deletes an edge from a graph. *}
  definition delete_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list_graph \<Rightarrow> 'v list_graph" where 
    "delete_edge v v' G = \<lparr>nodesL = nodesL G, edgesL = [(e1,e2) \<leftarrow> edgesL G. e1 \<noteq> v \<or> e2 \<noteq> v'] \<rparr>"

  
  fun delete_edges::"'v list_graph \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v list_graph" where 
    "delete_edges G [] = G"|
    "delete_edges G ((v,v')#es) = delete_edges (delete_edge v v' G) es"



text {* extended graph operations *}
   text {* Reflexive transitive successors of a node. Or: All reachable nodes for v including v. *}
    definition succ_rtran :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> 'v list" where
      "succ_rtran G v = rtrancl_list_impl (edgesL G) [v]"

   text {* Transitive successors of a node. Or: All reachable nodes for v. *}
    definition succ_tran :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> 'v list" where
      "succ_tran G v = trancl_list_impl (edgesL G) [v]"
  
   text {* The number of reachable nodes from v *}
    definition num_reachable :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> nat" where
      "num_reachable G v = length (succ_tran G v)"


    definition num_reachable_norefl :: "'v list_graph \<Rightarrow> 'v \<Rightarrow> nat" where
      "num_reachable_norefl G v = length ([ x \<leftarrow> succ_tran G v. x \<noteq> v])"


subsection{*undirected graph simulation*}
  text {* Create undirected graph from directed graph by adding backward links *}
  fun backlinks :: "('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
    "backlinks [] = []" |
    "backlinks ((e1, e2)#es) = (e2, e1)#(backlinks es)"

  definition undirected :: "'v list_graph \<Rightarrow> 'v list_graph"
    where "undirected G \<equiv> \<lparr> nodesL = nodesL G, edgesL = remdups (edgesL G @ backlinks (edgesL G)) \<rparr>"

section{*Correctness lemmata*}

  -- "add node"
  lemma add_node_valid: "valid_list_graph G \<Longrightarrow> valid_list_graph (add_node v G)"
    by(auto simp add: valid_list_graph_def valid_list_graph_axioms_def add_node_def)
  lemma add_node_set_nodes: "set (nodesL (add_node v G)) = set (nodesL G) \<union> {v}"
    by(auto simp add:add_node_def)
  lemma add_node_set_edges: "set (edgesL (add_node v G)) = set (edgesL G)"
     by(auto simp add:add_node_def)
  lemma add_node_correct: "FiniteGraph.add_node v (list_graph_to_graph G) = list_graph_to_graph (add_node v G)"
    by(simp add:FiniteGraph.add_node_def list_graph_to_graph_def add_node_set_edges add_node_set_nodes)
  lemma add_node_valid2: "valid_graph (list_graph_to_graph G) \<Longrightarrow> valid_graph (list_graph_to_graph (add_node v G))"
  by(simp add: add_node_correct[symmetric])

  -- "add edge"
  lemma add_edge_valid: "valid_list_graph G \<Longrightarrow> valid_list_graph (add_edge v v' G)"
    by(auto simp add: valid_list_graph_def add_edge_def add_node_def valid_list_graph_axioms_def)
  lemma add_edge_set_nodes: "set (nodesL (add_edge v v' G)) = set (nodesL G) \<union> {v,v'}"
    by(auto simp add: add_edge_def add_node_def)
  lemma add_edge_set_edges: "set (edgesL (add_edge v v' G)) = set (edgesL G) \<union> {(v,v')}"
    by(auto simp add: add_edge_def add_node_def)
  lemma add_edge_correct: "FiniteGraph.add_edge v v' (list_graph_to_graph G) = list_graph_to_graph (add_edge v v' G)"
    by(auto simp add:FiniteGraph.add_edge_def add_edge_def list_graph_to_graph_def add_node_set_nodes)
  lemma add_edge_valid2: "valid_graph (list_graph_to_graph G) \<Longrightarrow> valid_graph (list_graph_to_graph (add_edge v v' G))"
  by(simp add: add_edge_correct[symmetric])

  -- "delete node"
  lemma delete_node_valid:
  "valid_list_graph G \<Longrightarrow> valid_list_graph (delete_node v G)"
    by(auto simp add: valid_list_graph_def delete_node_def valid_list_graph_axioms_def)
  lemma delete_node_set_edges: "set (edgesL (delete_node v G)) = {(a,b). (a, b) \<in> set (edgesL G) \<and> a \<noteq> v \<and> b \<noteq> v}"
    by(auto simp add: delete_node_def)
  lemma delete_node_correct: "valid_list_graph G \<Longrightarrow> FiniteGraph.delete_node v (list_graph_to_graph G) = list_graph_to_graph (delete_node v G)"
    by(auto simp add:FiniteGraph.delete_node_def delete_node_def list_graph_to_graph_def valid_list_graph_def)


  -- "delte edge"
  lemma delete_edge_set_nodes: "set (nodesL (delete_edge v v' G)) = set (nodesL G)"
    by(simp add:delete_edge_def)
  lemma delete_edge_set_edges: "set (edgesL (delete_edge v v' G)) = {(a,b). (a,b) \<in> set (edgesL G) \<and> (a,b) \<noteq> (v,v')}"
    apply(simp add: delete_edge_def)
    by fastforce
  lemma delete_edge_set_edges2: "set (edgesL (delete_edge v v' G)) = set (edgesL G) - {(v,v')}"
    apply(simp add:delete_edge_set_edges)
    by fastforce
  lemma delete_edge_valid: "valid_list_graph G \<Longrightarrow> valid_list_graph (delete_edge v v' G)"
    apply(simp add: valid_list_graph_def delete_edge_def valid_list_graph_axioms_def)
    by blast
  lemma delete_edge_length: "length (edgesL (delete_edge v v' G)) \<le> length (edgesL G)"
    by (simp add:delete_edge_def)
  lemma delete_edge_commute: "delete_edge a1 a2 (delete_edge b1 b2 G) = delete_edge b1 b2 (delete_edge a1 a2 G)"
    apply(simp add: delete_edge_def)
    by metis
  lemma delete_edge_correct: "FiniteGraph.delete_edge v v' (list_graph_to_graph G) = list_graph_to_graph (delete_edge v v' G)"
    apply(simp add:FiniteGraph.delete_edge_def delete_edge_def list_graph_to_graph_def)
    by fastforce
  lemma delete_edge_valid2: "valid_graph (list_graph_to_graph G) \<Longrightarrow> valid_graph (list_graph_to_graph (delete_edge v v' G))"
  by(simp add: delete_edge_correct[symmetric])


  -- "delete edges"
  lemma delete_edges_valid: "valid_list_graph G \<Longrightarrow> valid_list_graph (delete_edges G E)"
    apply(induction E arbitrary: G) by(auto simp add:delete_edge_valid)
  lemma delete_edges_set_nodes: "set (nodesL (delete_edges G E)) = set (nodesL G)"
    apply(induction E arbitrary: G)
    apply simp
    apply(clarify)
    by(simp add: delete_edge_def delete_edge_set_nodes)
  lemma delete_edges_nodes: "nodesL (delete_edges G es) = nodesL G"
    apply(induction es arbitrary: G)
     apply simp
    apply(clarify)
    by(simp add: delete_edge_def)
  lemma delete_edges_set_edges: "set (edgesL (delete_edges G E)) = set (edgesL G) - set E"
    apply(induction E arbitrary: G)
    apply(simp)
    apply(clarify)
    apply(simp add: delete_edge_def delete_edge_set_nodes)
    by fastforce
  lemma delete_edges_set_edges2: "set (edgesL (delete_edges G E)) = {(a,b). (a,b) \<in> set (edgesL G) \<and> (a,b) \<notin> set E}"
    apply(simp add:delete_edges_set_edges)
    by fastforce
  lemma delete_edges_length: "length (edgesL (delete_edges G f)) \<le> length (edgesL G)"
    apply(induction f arbitrary:G)
    apply(simp)
    apply(auto)
    apply(metis delete_edge_length le_trans)
  done
  lemma delete_edges_chain: "delete_edges G (as @ bs) = delete_edges (delete_edges G as) bs"
   apply(induction as arbitrary: bs G)
    apply(simp)
   apply(simp)
   apply(rename_tac a as bs G)
   apply(case_tac a)
   apply(rename_tac a1 a2)
  by(simp)
  lemma delete_edges_delete_edge_commute: "delete_edges (delete_edge a1 a2 G) as = delete_edge a1 a2 (delete_edges G as)"
   apply(induction as arbitrary: G a1 a2)
    apply(simp)
   apply(case_tac a)
   apply(rename_tac a' as G a1' a2')
   apply(simp)
  by(simp add: delete_edge_commute)
  lemma delete_edges_commute: "delete_edges (delete_edges G as) bs = delete_edges (delete_edges G bs) as"
   apply(induction as arbitrary: bs G)
    apply(simp)
   apply(rename_tac a as bs G)
   apply(case_tac a)
   apply(rename_tac a1 a2)
   apply(simp)
  by(simp add:delete_edges_delete_edge_commute)
  lemma delete_edges_as_filter: "delete_edges G l = \<lparr> nodesL = nodesL G,  edgesL = [x \<leftarrow> edgesL G. x \<notin> set l] \<rparr>"
   apply(induction l)
    apply(simp)
   apply(clarsimp)
   apply(simp add: delete_edges_delete_edge_commute)
   apply(simp add: delete_edge_def)
  by (metis (lifting, full_types) prod.exhaust splitI split_conv)
  declare delete_edges.simps[simp del] (*do not automatically expand definition*)
  lemma delete_edges_correct: "FiniteGraph.delete_edges (list_graph_to_graph G) (set E) = list_graph_to_graph (delete_edges G E)"
   apply(simp add: delete_edges_as_filter list_graph_to_graph_def FiniteGraph.delete_edges_def)
  by fastforce
  lemma delete_edges_valid2: "valid_graph (list_graph_to_graph G) \<Longrightarrow> valid_graph (list_graph_to_graph (delete_edges G E))"
  by(simp add: delete_edges_correct[symmetric])


  -- "helper about reflexive transitive closure impl"
  lemma distinct_relpow_impl: "distinct L \<Longrightarrow> distinct new \<Longrightarrow> distinct have \<Longrightarrow> distinct (new@have) \<Longrightarrow> 
  distinct (relpow_impl (\<lambda>as. remdups (map snd [(a, b)\<leftarrow>L . a \<in> set as])) (\<lambda>xs ys. [x\<leftarrow>xs . x \<notin> set ys] @ ys) (\<lambda>x xs. x \<in> set xs) new have M)"
    apply(induction M arbitrary: "new" "have")
     apply(simp, fastforce)
    apply(simp)
    apply(clarify)
    apply(subgoal_tac "distinct ([n\<leftarrow>remdups (map snd [(a, b)\<leftarrow>L . a \<in> set new]) . (n \<in> set new \<longrightarrow> n \<in> set have) \<and> n \<notin> set have])")
    apply(subgoal_tac "distinct ([x\<leftarrow>new . x \<notin> set have] @ have)")
    apply(subgoal_tac "set ([n\<leftarrow>remdups (map snd [(a, b)\<leftarrow>L . a \<in> set new]) . (n \<in> set new \<longrightarrow> n \<in> set have) \<and> n \<notin> set have])
      \<inter> set ([x\<leftarrow>new . x \<notin> set have] @ have) = {}")
     apply blast
    apply (auto)
  done
  lemma distinct_rtrancl_list_impl: "distinct L \<Longrightarrow> distinct ls \<Longrightarrow> distinct (rtrancl_list_impl L ls)"
    apply(simp add:rtrancl_list_impl_def rtrancl_impl_def)
    apply(simp add:distinct_relpow_impl)
  done
  lemma distinct_trancl_list_impl: "distinct L \<Longrightarrow> distinct ls \<Longrightarrow> distinct (trancl_list_impl L ls)"
    apply(simp add:trancl_list_impl_def trancl_impl_def)
    apply(simp add:distinct_relpow_impl)
  done


  -- "succ rtran"
  value "succ_rtran \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> 1"
  lemma succ_rtran_correct: "FiniteGraph.succ_rtran (list_graph_to_graph G) v = set (succ_rtran G v)"
    by(simp add:rtrancl_list_impl FiniteGraph.succ_rtran_def succ_rtran_def list_graph_to_graph_def)
  lemma distinct_succ_rtran: "valid_list_graph G \<Longrightarrow> distinct (succ_rtran G v)"
    apply(simp add:succ_rtran_def)
    apply(rule distinct_rtrancl_list_impl)
    by(simp_all add:valid_list_graph_def)

  -- "succ tran"
  lemma distinct_succ_tran: "valid_list_graph G \<Longrightarrow> distinct (succ_tran G v)"
    apply(simp add:succ_tran_def)
    apply(rule distinct_trancl_list_impl)
    by(simp_all add:valid_list_graph_def)
  lemma succ_tran_set: "set (succ_tran G v) = {e2. (v,e2) \<in> (set (edgesL G))\<^sup>+}"
    by(simp add: succ_tran_def trancl_list_impl)
  value "succ_tran \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr> 1"
  lemma succ_tran_correct: "FiniteGraph.succ_tran (list_graph_to_graph G) v = set (succ_tran G v)"
    by(simp add:trancl_list_impl FiniteGraph.succ_tran_def succ_tran_def list_graph_to_graph_def)
  

  --"num_reachable"
  lemma num_reachable_correct: "valid_list_graph G \<Longrightarrow> 
    FiniteGraph.num_reachable (list_graph_to_graph G) v = num_reachable G v"
   apply(simp add: num_reachable_def FiniteGraph.num_reachable_def succ_tran_correct)
   apply(rule List.distinct_card)
   by(fact distinct_succ_tran)
  --"num_reachable_norefl"
  lemma num_reachable_norefl_correct: "valid_list_graph G \<Longrightarrow> 
    FiniteGraph.num_reachable_norefl (list_graph_to_graph G) v = num_reachable_norefl G v"
   apply(simp add: num_reachable_norefl_def FiniteGraph.num_reachable_norefl_def succ_tran_correct)
   using List.distinct_card by (metis (full_types) distinct_filter distinct_succ_tran set_minus_filter_out)


  -- "backlinks, i.e. backflows in formal def"
  lemma backlinks_alt: "backlinks E = [(snd e, fst e). e \<leftarrow> E]"
    by(induction E,fastforce+)
  lemma backlinks_set: "set (backlinks E) = {(e2, e1). (e1, e2) \<in> set E}"
    by(induction E,fastforce+)
  lemma undirected_nodes_set: "set (edgesL (undirected G)) = set (edgesL G) \<union> {(e2, e1). (e1, e2) \<in> set (edgesL G)}"
    by(simp add: undirected_def backlinks_set)
  lemma undirected_succ_tran_set: "set (succ_tran (undirected G) v) = {e2. (v,e2) \<in> (set (edgesL (undirected G)))\<^sup>+}"
    by(simp add: succ_tran_set)
  lemma backlinks_in_nodes_G: "\<lbrakk> fst ` set (edgesL G) \<subseteq> set (nodesL G); snd ` set (edgesL G) \<subseteq> set (nodesL G) \<rbrakk> \<Longrightarrow> 
    fst` set (edgesL (undirected G)) \<subseteq> set (nodesL (undirected G)) \<and> snd` set (edgesL (undirected G)) \<subseteq> set (nodesL (undirected G))"
    by(auto simp add:undirected_def backlinks_set)
  lemma backlinks_distinct: "distinct E \<Longrightarrow> distinct (backlinks E)"
    apply(induction E)
    by(simp_all add: backlinks_alt, force)
  lemma backlinks_subset: "set (backlinks X) \<subseteq> set (backlinks Y) <-> set X \<subseteq> set Y"
    by(auto simp add: backlinks_set)
  lemma backlinks_correct: 
    "FiniteGraph.backflows (set E) = set (backlinks E)"
    by(simp add: backflows_def backlinks_set)
  -- "undirected"
  lemma undirected_valid: "valid_list_graph G \<Longrightarrow> valid_list_graph (undirected G)"
    apply(simp add:valid_list_graph_def valid_list_graph_axioms_def)
    apply(simp add:backlinks_in_nodes_G)
    by(simp add:undirected_def)
  lemma undirected_correct: 
    "FiniteGraph.undirected (list_graph_to_graph G) = list_graph_to_graph (undirected G)"
    by(simp add: FiniteGraph.undirected_def undirected_def list_graph_to_graph_def backlinks_set)
      

lemmas valid_list_graph_valid = add_node_valid
  add_edge_valid
  delete_node_valid
  delete_edge_valid
  delete_edges_valid
  undirected_valid
thm valid_list_graph_valid


lemmas list_graph_correct = add_node_correct
  add_edge_correct
  delete_node_correct
  delete_edge_correct
  delete_edges_correct
  succ_rtran_correct
  succ_tran_correct
  num_reachable_correct
  undirected_correct
thm list_graph_correct


end
