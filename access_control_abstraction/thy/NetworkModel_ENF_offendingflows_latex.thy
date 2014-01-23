theory NetworkModel_ENF_offendingflows_latex
imports Main FiniteGraph NetworkModel_Interface NetworkModel_Util NetworkModel_ENF
begin


lemma (in NetworkModel_withOffendingFlows)  ENF_offending_members_documentedIsar:
  assumes a_not_eval: "\<not> eval_model G nP gP"
  and   a_enf: "eval_model_all_edges_normal_form P"
  and   a_offending: "F \<in> set_offending_flows G nP gP"
  shows
        "set F = {(e1,e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}"
proof
  -- {* Unfolding the edges normal form definition *}
  from a_enf have enf: 
    "\<forall> G nP gP. eval_model G nP gP =
      (\<forall> (e1, e2)\<in> set (edges G). P (nP e1) (nP e2))" 
    unfolding eval_model_all_edges_normal_form_def by simp

  -- {* Unfolding the offending flows definition *}
  from set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def
    have "set_offending_flows G nP gP = 
    {f \<in> set (sublists (edges G)). 
      \<not> eval_model G nP gP \<and> 
      eval_model (delete_edges G f) nP gP \<and> 
      (\<forall>(e1, e2)\<in>set f. 
        \<not> eval_model (add_edge e1 e2 (delete_edges G f)) nP gP)
    }" by simp

  -- {*The sublists of a list correspond to the powerset in set notation. *}
  -- {*@{thm sublists_powset [no_vars]}*}
  -- {* @{text "set ` set"} lifts a list of lists to a set of sets. *}

  -- {* Inserting edges normal form definition and using that the model is invalid *}
  from this a_not_eval enf have "set_offending_flows G nP gP = 
    {f \<in> set (sublists (edges G)). 
      (\<forall>(e1, e2)\<in>set (edges (delete_edges G f)). P (nP e1) (nP e2)) \<and> 
      (\<forall>(e1, e2)\<in>set f. 
        \<not> (\<forall>(e1', e2')\<in>set (edges (add_edge e1 e2 (delete_edges G f))). 
            P (nP e1') (nP e2')))
    }" by simp

  -- {* Lifting graph operations to their set theoretic equivalent *}
  from this have offending_set: "set_offending_flows G nP gP = 
    {f \<in> set (sublists (edges G)). 
      (\<forall>(e1, e2)\<in>set (edges G) - set f. P (nP e1) (nP e2)) \<and> 
      (\<forall>(e1, e2)\<in>set f. 
        \<not> (\<forall>(e1', e2')\<in>set (edges G) - set f \<union> {(e1, e2)}. 
            P (nP e1') (nP e2')))
    }" by (simp add:delete_edges_set_edges add_delete_edges_set_edges)


    -- {* First condition in the set of offending flows applied to @{text "F"}*}
    from offending_set a_offending have 
      F1: "F \<in> set (sublists (edges G))" by simp
  
    -- {* Second condition in the set of offending flows applied to @{text "F"}*}
    from offending_set a_offending have 
      F2: "\<forall>(e1, e2)\<in>set (edges G) - set F. P (nP e1) (nP e2)" by simp
  
    -- {* Third condition in the set of offending flows applied to @{text "F"}*}
    from offending_set a_offending have "\<forall>(e1, e2)\<in>set F. 
      \<not> (\<forall>(e1', e2')\<in>set (edges G) - set F \<union> {(e1, e2)}. P (nP e1') (nP e2'))"
      by fastforce
    -- {* Restating this fact *}
    hence 
      F3: "\<forall>(e1, e2)\<in>set F. 
        \<exists>(e1', e2')\<in>set (edges G) - set F \<union> {(e1, e2)}. \<not> P (nP e1') (nP e2')"
      by blast

  show "set F \<subseteq> {(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}"
  proof -
     -- {* First part of goal follows from first offending set condition.*}
    from F1 offending_in_edges have goal1: 
      "\<forall> (e1, e2)\<in> set F. (e1, e2) \<in> set (edges G)" by fast

    -- {* From @{text "F2"} and @{text "F3"} we see: *}
        -- {*  @{text "P"} holds for all edges in @{text "G"} without @{text "F"}.*}
        -- {*  If you add one edge from @{text "F"} to this set,*}
        -- {*  there exists an edge where @{text "P"} does not hold.*}
        -- {*  This edge must be taken from @{text "F"}.*}
    from F2 F3  have goal2: "\<forall>(e1, e2)\<in>set F. \<not> P (nP e1) (nP e2)" by blast

    from goal1 goal2 show 
    "set F \<subseteq> {(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}"
    by blast
  qed
  
  show "{(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)} \<subseteq> set F"
  proof(rule, clarify)
    -- {*We assume that an arbitrary @{text "(e1, e2)"} is in the left hand side set*}
    -- {*and show that it is also in the right hand side set. *}
    fix e1 e2
    assume a1: "(e1, e2) \<in> set (edges G)"
    assume a2: "\<not> P (nP e1) (nP e2)"
    
    -- {* @{text "F2"} statet that the model is valid without @{text "F"}.*}
    -- {* Hence, @{text "(e1, e2)"} cannot be in this valid part of @{text "G"}*}
    from a2 F2 have "(e1, e2) \<notin> (set (edges G) - set F)" by blast
    from this a1 show "(e1, e2) \<in> set F" by simp
  qed
qed


theorem (in NetworkModel_withOffendingFlows) ENF_offending_set_documentedIsar:
  assumes assm_enf: "eval_model_all_edges_normal_form P"
  shows
  "set ` set_offending_flows G nP gP = (if eval_model G nP gP then
    {}
   else 
    { {(e1,e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)} })"
proof(cases "eval_model G nP gP")
  -- {*Case 1: model is valid*}
  assume assm_eval: "eval_model G nP gP"
  
  -- {*By definition, the set of offending flows is empty for a valid model*}
  from set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def
    have "eval_model G nP gP \<Longrightarrow> set_offending_flows G nP gP = {}" by simp
  from this assm_eval have "set_offending_flows G nP gP = {}" by simp
  from this set_list_offending_flows have 
    "set ` set_offending_flows G nP gP = {}" by simp
  thus ?thesis using assm_eval by simp
next
  -- {*Case 2: model is invalid*}
  assume assm_not_eval: "\<not> eval_model G nP gP"
  from assm_enf have enf:
    "\<forall>G nP gP. eval_model G nP gP = 
      (\<forall>(e1, e2)\<in>set (edges G). P (nP e1) (nP e2))"
    unfolding eval_model_all_edges_normal_form_def by simp
  
  -- {* By assumption, there is a flow in @{text "G"} which violates @{text "P"} *}
  from assm_not_eval enf have "\<not> (\<forall>(e1, e2)\<in>set (edges G). P (nP e1) (nP e2))"
    by simp
  hence "\<exists>(e1, e2)\<in>set (edges G). \<not> P (nP e1) (nP e2)" by blast
  
  -- {* Thus, the set of offending flows is not empty. *}
  -- {* Note: The full formal proof for this fact available in *}
  -- {* lemma @{text "ENF_notevalmodel_imp_ex_offending_min"}.*}
  -- {* The intuition is as follows: *}
    --{*    The model is invalid and all validity decisions are decided locally.*}
    --{*    Thus, there must be at least one flow to violate the model's validity.*}
  hence offending_not_empty: "set_offending_flows G nP gP  \<noteq> {}"
    using ENF_notevalmodel_imp_ex_offending_min assm_enf 
    assm_not_eval set_offending_flows_def by simp
 
  -- {* From our previous lemma @{text "ENF_offending_members_documentedIsar"} *}
  -- {* we conclude *}
  from ENF_offending_members_documentedIsar[OF assm_not_eval assm_enf]
  have offending_prop: 
    "\<forall> f \<in> set_offending_flows G nP gP. 
      set f = {(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}"
    by simp

  -- {* Adding an outer set to meet the formulation of the main goal *}
  have "set ` set_offending_flows G nP gP = 
    {{(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}}"
  proof
    from offending_prop
    show "set ` set_offending_flows G nP gP \<subseteq> 
      {{(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}}" by blast
  next
    -- {* For the other direction, we need that the set of offending flows is not empty. *}
    show "{{(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)}} \<subseteq> 
      set ` set_offending_flows G nP gP"
    proof(clarify)
      from offending_prop offending_not_empty
      show "{(e1, e2). (e1, e2) \<in> set (edges G) \<and> \<not> P (nP e1) (nP e2)} \<in> 
        set ` set_offending_flows G nP gP" by blast
    qed
  qed
  from this assm_not_eval show ?thesis by simp
qed



end
