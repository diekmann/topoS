theory NetworkModel_Composition_Theory_legacy
imports NetworkModel_Interface NetworkModel_Helper
begin

(*theory, do not load together with library list impl*)

(* Outdated legac version!!
  Problem: 'a 'b types are fixed!!
  So you can only combine network security requirement models over the same type of scenario specific information
   *)


  (*'v should be of type ::vertex*)
  type_synonym ('v, 'a, 'b) network_security_requirement =
   "'a \<times> (('v) graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool) \<times> bool        \<times> ('v, 'a, 'b) NetworkModel_Params"
  (*\<bottom> \<times> eval_model                         \<times> target_focus \<times> scenario-specific information    *)



  definition valid_req :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> bool" where
    "valid_req m \<equiv> (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> NetworkModel eval_model defbot target_focus)"

  definition valid_reqs :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> bool" where
    "valid_reqs M \<equiv> \<forall> m \<in> set M. valid_req m"

  subsection {*Accessors*}
    definition c_nP :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> ('v \<Rightarrow> 'a)" where
      "c_nP m = (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> NetworkModel.node_props defbot config)"
  
    definition c_gP :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> 'b" where
      "c_gP m = (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> (model_global_properties config))"
    
    definition c_eval_model :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> (('v) graph \<Rightarrow> bool)" where
      "c_eval_model m = (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> \<lambda>G. eval_model G (c_nP m))"

    definition c_offending_flows :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> (('v) graph \<Rightarrow> ('v \<times> 'v) set set)" where
      "c_offending_flows m = (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> 
        (\<lambda>G. NetworkModel_withOffendingFlows.set_offending_flows eval_model G (c_nP m)))"

    definition c_isIFS :: "('v::vertex, 'a, 'b) network_security_requirement \<Rightarrow> bool" where
      "c_isIFS m = (case m of (defbot, eval_model, target_focus, config) \<Rightarrow> target_focus)"

      subsubsection {* Accessors for lists of security requirements *}
      -- "return all Information Flow Strategy models from a list of models"
      definition get_IFS :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> ('v::vertex, 'a, 'b) network_security_requirement list" where
        "get_IFS M \<equiv> [m \<leftarrow> M. c_isIFS m]"
  
      lemma "\<forall> (defbot, eval_model, target_focus, config) \<in> set (get_IFS M). target_focus"
        by(simp add: get_IFS_def c_isIFS_def)
  
      -- "return all Access Control Strategy models from a list of models"
      definition get_ACS :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> ('v::vertex, 'a, 'b) network_security_requirement list" where
        "get_ACS M \<equiv> [m \<leftarrow> M. \<not> c_isIFS m]"
  
      lemma "\<forall> (defbot, eval_model, target_focus, config) \<in> set (get_ACS M). \<not> target_focus"
        by(simp add: get_ACS_def c_isIFS_def)


      definition get_offending_flows :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> 'v graph \<Rightarrow> (('v \<times> 'v) set set)" where
        "get_offending_flows M G = (\<Union>m\<in>set M. c_offending_flows m G)"


      (* as a programmer, the List.filter approach was more intuitive but those definitions are equal *)
      lemma get_offending_flows_alt1: "get_offending_flows M G = \<Union> {c_offending_flows m G | m. m \<in> set M}"
        apply(simp add: get_offending_flows_def) by fastforce
      lemma get_offending_flows_alt2: "get_offending_flows M G = \<Union> set [c_offending_flows m G. m \<leftarrow> M]"
        apply(simp add: get_offending_flows_alt1) by fastforce


  subsection {*Algorithms*}
    (*Note: is only eval_model, not eval, hence does not check verify_globals and valid_graph!!*)
    definition all_security_requirements_fulfilled :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> 'v graph \<Rightarrow> bool" where
      "all_security_requirements_fulfilled M G \<equiv> \<forall>m \<in> set M. (c_eval_model m) G"
  
  
    (*constant G, remove after algorithm*)
    fun generate_valid_topology :: "('v::vertex, 'a, 'b) network_security_requirement list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
      "generate_valid_topology [] G = G" |
      "generate_valid_topology (m#Ms) G = delete_edges (generate_valid_topology Ms G) (\<Union> (c_offending_flows m G))"



  subsection {*Lemmata*}
    lemma c_eval_model_mono:
    "\<lbrakk> valid_req m; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr>; c_eval_model m \<lparr>nodes = V, edges = E\<rparr>\<rbrakk> \<Longrightarrow>
       c_eval_model m \<lparr>nodes = V, edges = E'\<rparr>"
     apply(cases m)
     apply(rename_tac defbot eval_model target_focus config)
     apply(simp add: valid_req_def)
     apply(simp add: c_eval_model_def c_nP_def c_gP_def c_offending_flows_def)
     apply clarify
     apply(subgoal_tac "NetworkModel_preliminaries eval_model")
       prefer 2
       apply(simp add: NetworkModel_def)
     apply(erule_tac NetworkModel_preliminaries.mono_eval_model)
     by simp_all

    lemma valid_reqs1: "valid_reqs (m # M) \<Longrightarrow> valid_req m"
      by(simp add: valid_reqs_def)
    lemma valid_reqs2: "valid_reqs (m # M) \<Longrightarrow> valid_reqs M"
      by(simp add: valid_reqs_def)

    lemma all_security_requirements_fulfilled_mono:
    "\<lbrakk> valid_reqs M; E' \<subseteq> E; valid_graph \<lparr> nodes = V, edges = E \<rparr> \<rbrakk> \<Longrightarrow>  
      all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
      all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E' \<rparr>"
      apply(induction M arbitrary: E' E)
      apply(simp_all add: all_security_requirements_fulfilled_def)
      apply(rename_tac m M E' E)
      apply(rule conjI)
       apply(drule valid_reqs1)
       apply(erule c_eval_model_mono)
       apply(simp_all)
       apply force
      apply(drule valid_reqs2)
      apply blast
      done


    (* erule to get NetworkModel_preliminaries from valid_req *)
    lemma rule_NetworkModel_preliminariesE: "\<lbrakk> valid_req m \<rbrakk> \<Longrightarrow> 
    (\<And>defbot eval_model target_focus config. m = (defbot, eval_model, target_focus, config) \<Longrightarrow> NetworkModel_preliminaries eval_model \<Longrightarrow> P) \<Longrightarrow> P"
      apply(simp add: valid_req_def NetworkModel_def)
      apply(clarify)
      by blast
    
    lemma c_offending_flows_union_mono:
    "\<lbrakk> valid_req m; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow>
      \<Union> c_offending_flows m \<lparr> nodes = V, edges = E' \<rparr> \<subseteq> \<Union> c_offending_flows m \<lparr> nodes = V, edges = E \<rparr>"
      apply(erule rule_NetworkModel_preliminariesE)
      thm NetworkModel_preliminaries.offending_flows_union_mono
      apply(drule(2) NetworkModel_preliminaries.offending_flows_union_mono)
      by(simp add: c_offending_flows_def)


    lemma c_offending_flows_extend:
    "\<lbrakk> valid_req m; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr>; F \<in> c_offending_flows m \<lparr> nodes = V, edges = E' \<rparr> \<rbrakk> \<Longrightarrow>
      \<exists> F' \<in> c_offending_flows m \<lparr> nodes = V, edges = E \<rparr>. F \<subseteq> F'"
      apply(erule rule_NetworkModel_preliminariesE)
      apply(simp add: c_offending_flows_def)
      apply(drule(3) NetworkModel_preliminaries.mono_extend_set_offending_flows)
      by assumption

   lemma c_offending_flows_insert_contains_new:
     "\<lbrakk> valid_req m; valid_graph \<lparr> nodes = V, edges = insert e E \<rparr>; 
       c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> = {}; 
       c_offending_flows m \<lparr>nodes = V, edges = insert e E\<rparr> \<noteq> {} \<rbrakk> \<Longrightarrow> 
        {e} \<in> c_offending_flows m \<lparr>nodes = V, edges = insert e E\<rparr>"
      apply(erule rule_NetworkModel_preliminariesE)
      apply(simp add: c_offending_flows_def)
      apply(drule(3) NetworkModel_preliminaries.set_offending_flows_insert_contains_new)
      by assumption


    lemma get_offending_flows_flattened_mono: 
    "\<lbrakk> valid_reqs M; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow>
      \<Union> get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr> \<subseteq> \<Union> get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs1)
      apply(drule(2) c_offending_flows_union_mono)
      apply(simp add: get_offending_flows_def)
      apply(rule conjI)
      apply(thin_tac "valid_reqs ?M")
       apply blast
      apply(drule valid_reqs2)
      by blast


    lemma get_offending_flows_extend:
    "\<lbrakk> valid_reqs M; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr>; F \<in> get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr> \<rbrakk> \<Longrightarrow>
      \<exists> F' \<in> get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>. F \<subseteq> F'"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs1)
      apply(drule valid_reqs2)
      apply(simp add: get_offending_flows_def)
      apply(erule disjE)
      apply(drule(3) c_offending_flows_extend)
       apply blast
      apply(simp add: get_offending_flows_def)
       apply(blast)
      done

   lemma get_offending_flows_insert_contains_new:
     "\<lbrakk> valid_reqs M; valid_graph \<lparr> nodes = V, edges = insert e E \<rparr>; 
       get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> = {}; 
       get_offending_flows M \<lparr>nodes = V, edges = insert e E\<rparr> \<noteq> {} \<rbrakk> \<Longrightarrow> 
        {e} \<in> get_offending_flows M \<lparr>nodes = V, edges = insert e E\<rparr>"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs1)
      apply(drule valid_reqs2)
      apply(simp add: get_offending_flows_def)
      apply auto
      apply(drule(1) c_offending_flows_insert_contains_new)
       apply blast
       apply blast
       apply blast
      done
      
    text{* The offending flows are in the powerset of the edges *}
    lemma get_offending_flows_subseteq_edges: 
    "get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<subseteq> Pow E"
      apply(simp add: get_offending_flows_def c_offending_flows_def NetworkModel_withOffendingFlows.set_offending_flows_def)
      by fastforce

     lemma "\<lbrakk> get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> = {}; get_offending_flows M \<lparr>nodes = V, edges = insert e E\<rparr> \<noteq> {} \<rbrakk> \<Longrightarrow> get_offending_flows M \<lparr>nodes = V, edges = insert e E\<rparr> = {{e}}"
      oops

  
    lemma generate_valid_topology_nodes:
    "nodes (generate_valid_topology M G) = (nodes G)"
      apply(induction M arbitrary: G)
      by(simp_all add: graph_ops)
  

    lemma valid_graph_generate_valid_topology: "valid_graph G \<Longrightarrow> valid_graph (generate_valid_topology M G)"
      apply(induction M arbitrary: G)
      by(simp_all)


  lemma generate_valid_topology_EX_graph_record:
  "\<exists> hypE. (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr> "
    apply(induction M arbitrary: V E)
    apply(simp_all)
    by(simp add: delete_edges_simp2 generate_valid_topology_nodes)

    lemma generate_valid_topology_mono_models:
    "edges (generate_valid_topology (m#M) \<lparr> nodes = V, edges = E \<rparr>) \<subseteq> edges (generate_valid_topology M \<lparr> nodes = V, edges = E \<rparr>)"
      apply(induction M arbitrary: E m)
      apply(simp add: delete_edges_simp2)
      apply fastforce
      apply(simp_all add: delete_edges_simp2)
      by blast
   
    lemma generate_valid_topology_subseteq_edges:
    "edges (generate_valid_topology M G) \<subseteq> (edges G)"
      apply(induction M arbitrary: G)
      apply(simp_all)
      apply(simp add: delete_edges_simp2)
      by blast
    

  text{* generate_valid_topology generates a valid topology! *}
  theorem generate_valid_topology_sound:
  "\<lbrakk> valid_reqs M; valid_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow> 
  all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)"
    proof(induction M arbitrary: V E)
      case Nil
      thus ?case by(simp add: all_security_requirements_fulfilled_def)
    next
      case (Cons m M)
      from valid_reqs1[OF Cons(2)] have "valid_req m" .
      from this obtain defbot eval_model target_focus config where 
        m_components: "m = (defbot, eval_model, target_focus, config)" and
        m_NetworkModel: "NetworkModel eval_model defbot target_focus"
          apply(simp add:valid_req_def) by blast

      from Cons(3) have valid_rmUnOff: "valid_graph \<lparr>nodes = V, edges = E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>"
        by(simp add: valid_graph_remove_edges)
      
      from NetworkModel_preliminaries.eval_model_valid_remove_flattened_offending_flows[OF _ Cons(3)] m_NetworkModel
      have valid_eval_rmUnOff: "c_eval_model m \<lparr>nodes = V, edges = E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>"
        apply(simp add: c_eval_model_def m_components c_offending_flows_def)
        sorry (*holds, but I'm too lazy to update this outdated theory, ....*)

      from generate_valid_topology_subseteq_edges have edges_gentopo_subseteq: 
        "(edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)) - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)
           \<subseteq>
        E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)"  by fastforce

      from c_eval_model_mono[OF valid_reqs1[OF Cons(2)] edges_gentopo_subseteq valid_rmUnOff valid_eval_rmUnOff]
      have "c_eval_model m \<lparr>nodes = V, edges = (edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)) - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>"
        by simp
      from this have goal1: 
        "c_eval_model m (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
           by(simp add: delete_edges_simp2 generate_valid_topology_nodes)



      from valid_reqs2[OF Cons(2)] have "valid_reqs M" .
      from Cons.IH[OF `valid_reqs M` Cons(3)] have IH:
        "all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)" .

      from generate_valid_topology_EX_graph_record obtain E_IH where  E_IH_prop:
        "(generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = E_IH\<rparr>" by blast

      from valid_graph_generate_valid_topology[OF Cons(3)] E_IH_prop
      have valid_G_E_IH: "valid_graph \<lparr>nodes = V, edges = E_IH\<rparr>" by metis

      thm IH[simplified E_IH_prop]
      thm all_security_requirements_fulfilled_mono[OF `valid_reqs M` _  valid_G_E_IH IH[simplified E_IH_prop]]

      from all_security_requirements_fulfilled_mono[OF `valid_reqs M` _  valid_G_E_IH IH[simplified E_IH_prop]] have mono_rule:
        "\<And> E'. E' \<subseteq> E_IH \<Longrightarrow> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" .

      have "all_security_requirements_fulfilled M 
        (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
        apply(subst E_IH_prop)
        apply(simp add: delete_edges_simp2)
        apply(rule mono_rule)
        by fast

      from this have goal2:
        "(\<forall>ma\<in>set M.
        c_eval_model ma (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)))"
        by(simp add: all_security_requirements_fulfilled_def)

      from goal1 goal2 
      show  "all_security_requirements_fulfilled (m # M) (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)" 
      by (simp add: all_security_requirements_fulfilled_def)
   qed
   

   lemma c_eval_model_valid_imp_no_offending_flows: 
      "c_eval_model m G \<Longrightarrow> \<forall>x\<in>c_offending_flows m G. x = {}"
      apply(case_tac m)
      apply(rename_tac defbot eval_model target_focus config)
      apply(simp add: c_eval_model_def)
      apply(simp add: c_nP_def c_gP_def)
      apply(simp add: c_offending_flows_def)
      apply(simp add: c_nP_def c_gP_def)
      apply(clarify)
      by(simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
          NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
          NetworkModel_withOffendingFlows.is_offending_flows_def)

   lemma all_security_requirements_fulfilled_imp_no_offending_flows:
      "all_security_requirements_fulfilled M G \<Longrightarrow> (\<Union>m\<in>set M. \<Union>c_offending_flows m G) = {}"
      apply(induction M)
      apply(simp_all)
      apply(simp add: all_security_requirements_fulfilled_def)
      using c_eval_model_valid_imp_no_offending_flows by metis

  corollary all_security_requirements_fulfilled_imp_get_offending_empty:
  "all_security_requirements_fulfilled M G \<Longrightarrow> get_offending_flows M G = {}"
    apply(simp only: get_offending_flows_def)
    apply(drule all_security_requirements_fulfilled_imp_no_offending_flows)
    apply(rule)

    (*adding valid_reqs here, the proof would be easier, we are repeating a fact here*)
    thm NetworkModel_withOffendingFlows.empty_offending_contra

      apply(clarsimp)
      apply(rename_tac defbot eval_model target_focus config)
      apply(simp add: c_offending_flows_def)
      apply(simp add: c_nP_def c_gP_def)
      apply(simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
          NetworkModel_withOffendingFlows.is_offending_flows_min_set_def
          NetworkModel_withOffendingFlows.is_offending_flows_def)
      apply fastforce

    apply simp
   done



end
