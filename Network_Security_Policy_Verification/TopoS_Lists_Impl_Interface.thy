theory TopoS_Lists_Impl_Interface
imports "Lib/FiniteGraph" "Lib/FiniteListGraph" TopoS_Interface TopoS_Helper
begin

  section {*Correspondence List implementation and set Speficiation*}
  
  subsection{*Abstraction from list implementation to set specification*}
  locale TopoS_List_Impl = 
    fixes default_node_properties :: "'a" ("\<bottom>") 
    and eval_model_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and eval_model_impl::"('v::vertex) list_graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and verify_globals_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    and verify_globals_impl::"('v::vertex) list_graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    and target_focus :: "bool"
    and offending_flows_impl::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    and node_props_impl::"('v::vertex, 'a, 'b) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)"
    and eval_impl::"('v::vertex) list_graph \<Rightarrow> ('v, 'a, 'b)TopoS_Params \<Rightarrow> bool"
    assumes
      spec: "NetworkModel eval_model_spec default_node_properties target_focus" --"specification is valid"
    and
      eval_model_spec_impl: "valid_list_graph G \<Longrightarrow> 
        (eval_model_spec (list_graph_to_graph G) nP) = (eval_model_impl G nP)"
    and
      verify_globals_spec_impl: "valid_list_graph G \<Longrightarrow> 
        (verify_globals_spec (list_graph_to_graph G) nP gP) = (verify_globals_impl G nP gP)"
    and
      offending_flows_spec_impl: "valid_list_graph G \<Longrightarrow> 
      (TopoS_withOffendingFlows.set_offending_flows eval_model_spec (list_graph_to_graph G) nP) = 
      set`set (offending_flows_impl G nP)"
    and 
      node_props_spec_impl: 
     "NetworkModel.node_props_formaldef default_node_properties P = node_props_impl P"
    and
      eval_spec_impl:
     "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> 
     NetworkModel.eval eval_model_spec verify_globals_spec default_node_properties (list_graph_to_graph G) P ) = 
     (eval_impl G P)"
    begin
    end
    print_locale! TopoS_List_Impl
    term TopoS_List_Impl


  text {* Models packed. *}

  section {* many network models together form a library *}
  record ('v::vertex, 'a, 'b) TopoS_packed =
    nm_name :: "string"
    nm_target_focus :: "bool"
    nm_default :: "'a"
    nm_eval_model::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool"
    nm_verify_globals::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    nm_offending_flows::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    nm_node_props::"('v::vertex, 'a, 'b) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)" 
    nm_eval::"('v::vertex) list_graph \<Rightarrow> ('v, 'a, 'b)TopoS_Params \<Rightarrow> bool"
    


   text{*This must be shown to prove that some packed model m complies with the formal definition!*}
   locale TopoS_modelLibrary =
    fixes m :: "('v::vertex, 'a, 'b) TopoS_packed" -- "concrete model implementation"
    and eval_model_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool" --"specification"
    and verify_globals_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool" --"specification"
    assumes
       name_not_empty: "length (nm_name m) > 0"
     and
       impl_spec: "TopoS_List_Impl 
        (nm_default m)
        eval_model_spec
        (nm_eval_model m)
        verify_globals_spec
        (nm_verify_globals m)
        (nm_target_focus m)
        (nm_offending_flows m)
        (nm_node_props m)
        (nm_eval m)"
   begin
   end
   print_locale! TopoS_modelLibrary



subsection{*Helpfull lemmata*}
  
  lemma distinct_rm: "P G = Q G \<Longrightarrow> (distinct (nodesL G) \<and> distinct (edgesL G) \<and> P G) = (distinct (nodesL G) \<and> distinct (edgesL G) \<and> Q G)"
  by simp
  
  lemma valid_list_graph_axioms_rm: "P G = Q G \<Longrightarrow> (valid_list_graph_axioms G \<and> P G) = (valid_list_graph_axioms G \<and> Q G)"
  by simp
  
  (*show that eval complies*)
  lemma TopoS_eval_impl_proofrule: 
    "\<lbrakk>NetworkModel eval_model_spec default_node_properties target_focus;
    (\<And> nP. valid_list_graph G \<Longrightarrow> eval_model_spec (list_graph_to_graph G) nP = eval_model_impl G nP); 
    (\<And> nP gP. valid_list_graph G \<Longrightarrow> verify_globals_spec (list_graph_to_graph G) nP gP = verify_globals_impl G nP gP) \<rbrakk> \<Longrightarrow>
      (distinct (nodesL G) \<and> distinct (edgesL G) \<and> NetworkModel.eval eval_model_spec verify_globals_spec default_node_properties (list_graph_to_graph G) P) =
      (valid_list_graph G \<and> verify_globals_impl G (NetworkModel.node_props default_node_properties P) (model_global_properties P) \<and>
       eval_model_impl G (NetworkModel.node_props default_node_properties P))"
    proof -
    assume inst: "NetworkModel eval_model_spec default_node_properties target_focus"
    assume ev: "\<And> nP. valid_list_graph G \<Longrightarrow> eval_model_spec (list_graph_to_graph G) nP = eval_model_impl G nP"
    assume ver: "\<And> nP gP. valid_list_graph G \<Longrightarrow> verify_globals_spec (list_graph_to_graph G) nP gP = verify_globals_impl G nP gP"
  
    have case_valid: "valid_list_graph G \<Longrightarrow> (verify_globals_spec (list_graph_to_graph G) (NetworkModel.node_props default_node_properties P) (model_global_properties P) \<and>
       eval_model_spec (list_graph_to_graph G) (NetworkModel.node_props default_node_properties P)) =
      (verify_globals_impl G (NetworkModel.node_props default_node_properties P) (model_global_properties P) \<and>
       eval_model_impl G (NetworkModel.node_props default_node_properties P))" using
       ev[of "(NetworkModel.node_props default_node_properties P)"]
       ver[of "(NetworkModel.node_props default_node_properties P)" "(model_global_properties P)"] by blast

    show "?thesis"
      proof(cases "valid_list_graph G")
      case True
        from inst case_valid[OF True] show ?thesis
        apply(simp add: valid_list_graph_def)
        apply(rule distinct_rm)
        apply(unfold NetworkModel.eval_def)
        apply(simp only: valid_list_graph_iff_valid_graph)
        done
      next
      case False
        from False valid_list_graph_def have "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> valid_list_graph_axioms G) = False" by blast
        from this NetworkModel.eval_def[OF inst, of verify_globals_spec "(list_graph_to_graph G)"] 
        valid_list_graph_iff_valid_graph  have "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> 
          NetworkModel.eval eval_model_spec verify_globals_spec default_node_properties (list_graph_to_graph G) P) = False" by blast
        from False this show ?thesis by blast
      qed
    qed
  


section {*Helper lemmata*}

  text{* Provide @{term eval_model} function and get back a function that computes the list of offending flows
  
  Exponential time!!
  *}
  definition Generic_offending_list:: "('v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool )\<Rightarrow> 'v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list" where
    "Generic_offending_list eval_model G nP = [f \<leftarrow> (sublists (edgesL G)). 
    (\<not> eval_model G nP \<and> eval_model (FiniteListGraph.delete_edges G f) nP) \<and> 
      (\<forall>(e1, e2)\<in>set f. \<not> eval_model (add_edge e1 e2 (FiniteListGraph.delete_edges G f)) nP)]"
  
  
  (*proof rule: if eval_model is correct, Generic_offending_list is correct *)
  lemma Generic_offending_list_correct: 
    "\<lbrakk> valid_list_graph G;
      \<forall> G nP. valid_list_graph G \<longrightarrow> (eval_model_spec (list_graph_to_graph G) nP) = (eval_model_impl G nP) \<rbrakk> \<Longrightarrow>
    TopoS_withOffendingFlows.set_offending_flows eval_model_spec (list_graph_to_graph G) nP = 
      set`set( Generic_offending_list eval_model_impl G nP )"
  proof(unfold TopoS_withOffendingFlows.set_offending_flows_def 
      TopoS_withOffendingFlows.is_offending_flows_min_set_def 
      TopoS_withOffendingFlows.is_offending_flows_def
      Generic_offending_list_def)
    assume valid: "valid_list_graph G"
    and spec_impl: "\<forall>G nP. valid_list_graph G \<longrightarrow> eval_model_spec (list_graph_to_graph G) nP = eval_model_impl G nP"
      hence spec_impl1: "\<And> G nP. valid_list_graph G \<Longrightarrow> eval_model_spec (list_graph_to_graph G) nP = eval_model_impl G nP" by simp
    
    have set_reinziehen: "\<And> P G. set ` {x \<in> set (sublists (edgesL G)). P G (set x)} = {x \<in> set ` set (sublists (edgesL G)). P G (x)}"
      by fastforce
    have subset_sublists_filter: "\<And> G P. {f. f \<subseteq> edges (list_graph_to_graph G) \<and> P G f} 
    = set ` set [f\<leftarrow>sublists (edgesL G) . P G (set f)]"
      by(simp add: list_graph_to_graph_def set_reinziehen sublists_powset)
  
  
    from valid delete_edges_valid have valid_delete: "\<forall>f. valid_list_graph(FiniteListGraph.delete_edges G f)" by fast
    from spec_impl1[symmetric] valid_delete FiniteListGraph.delete_edges_correct[of "G"] have impl_spec_delete:
      "\<forall>f. eval_model_impl (FiniteListGraph.delete_edges G f) nP = 
          eval_model_spec (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)) nP" by simp
  
    from spec_impl1[OF valid, symmetric] have impl_spec_not:
      "(\<not> eval_model_impl G nP) = (\<not> eval_model_spec (list_graph_to_graph G) nP)" by auto
  
    from spec_impl1[symmetric, OF FiniteListGraph.add_edge_valid[OF FiniteListGraph.delete_edges_valid[OF valid]]] have impl_spec_allE:
    "\<forall> e1 e2 E. eval_model_impl (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E)) nP =
    eval_model_spec (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E))) nP" by simp
  
  
    have substListGraph: "\<And> e1 e2 G f. (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G f))) = 
      (FiniteGraph.add_edge e1 e2 (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)))"
    by(simp add: FiniteListGraph.add_edge_correct FiniteListGraph.delete_edges_correct)
    
    show "{f. f \<subseteq> edges (list_graph_to_graph G) \<and>
            (\<not> eval_model_spec (list_graph_to_graph G) nP \<and> eval_model_spec (FiniteGraph.delete_edges (list_graph_to_graph G) f) nP) \<and>
            (\<forall>(e1, e2)\<in>f. \<not> eval_model_spec (FiniteGraph.add_edge e1 e2 (FiniteGraph.delete_edges (list_graph_to_graph G) f)) nP)} =
        set ` set [f\<leftarrow>sublists (edgesL G) .
                   (\<not> eval_model_impl G nP \<and> eval_model_impl (FiniteListGraph.delete_edges G f) nP) \<and>
                   (\<forall>(e1, e2)\<in>set f. \<not> eval_model_impl (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G f)) nP)]"
        apply(subst impl_spec_delete)
        apply(subst impl_spec_not)
        apply(subst impl_spec_allE)
        apply(subst substListGraph)
        apply(rule subset_sublists_filter)
        done
  qed
  
  
  
  
  lemma all_edges_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>(e1, e2)\<in> (edges (list_graph_to_graph G)). P (list_graph_to_graph G) e1 e2) = (\<forall>(e1, e2)\<in>set (edgesL G). Pl G e1 e2)"
   by(simp add:list_graph_to_graph_def)

  
  lemma all_nodes_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>n \<in> (nodes (list_graph_to_graph G)). P (list_graph_to_graph G) n) = (\<forall> n \<in>set (nodesL G). Pl G n)"
   by(simp add:list_graph_to_graph_def)

end
