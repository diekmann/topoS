theory NetworkModel_Interface
imports Main "../../thy_lib/FiniteGraph" NetworkModel_Vertices NetworkModel_Util
begin



section {* NetworkModel definition: *}
  (* 'v is a graph's node type
     'a are the model specific node configuration options
     'b are additional configuration options for this model *)
  record ('v::vertex, 'a, 'b) NetworkModel_Params =
    node_properties :: "'v::vertex \<Rightarrow> 'a option"
    model_global_properties :: "'b"


text {* A NetworkModel where the offending flows (flows that invalidate the network graph) can be defined and calculated:*}  
  locale NetworkModel_withOffendingFlows = 
    fixes eval_model::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool" (*Network Graph (V,E) => V to node_properties => bool*)
    fixes verify_globals::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool" (*Network Graph (V,E) => V to node_properties => model_global_properties => bool*)
   begin
    -- "Offending Flows definitions:"
    definition is_offending_flows::"('v \<times> 'v) set \<Rightarrow> 'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool" where
      "is_offending_flows f G nP \<equiv> \<not> eval_model G nP \<and> eval_model (delete_edges G f) nP"
    
    -- "Above definition is not minimal: "
    definition is_offending_flows_min_set::"('v \<times> 'v) set \<Rightarrow> 'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool" where
      "is_offending_flows_min_set f G nP \<equiv> is_offending_flows f G nP \<and> 
        (\<forall> (e1, e2) \<in> f. \<not> eval_model (add_edge e1 e2 (delete_edges G f)) nP)"
    
    -- "The set of all offending flows."
    definition set_offending_flows::"'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) set set" where
      "set_offending_flows G  nP = {f. f \<subseteq> (edges G) \<and> is_offending_flows_min_set f G nP}"
  

    -- "Properties of this offending flows definition"
    lemma removing_offendingFlows_evalTrue: 
      "\<lbrakk> \<not> eval_model G  nP \<rbrakk> \<Longrightarrow> \<forall> f \<in> set_offending_flows G nP. eval_model (delete_edges G f) nP"
    by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
    lemma offending_not_empty: "\<lbrakk> f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow> f \<noteq> {}"
     by(auto simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma empty_offending_contra:
       "\<lbrakk> f \<in> set_offending_flows G nP; f = {}\<rbrakk> \<Longrightarrow> False"
     by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma "f \<in> set_offending_flows G nP \<Longrightarrow> \<not> eval_model G nP"
     by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma validmodel_imp_no_offending: 
      "eval_model G nP \<Longrightarrow> set_offending_flows G nP = {}"
     by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    theorem remove_offending_flows_imp_model_valid:
      "\<forall>f \<in> set_offending_flows G nP. eval_model (delete_edges G f) nP"
      apply(cases "\<not> eval_model G nP")
       apply (metis removing_offendingFlows_evalTrue)
      apply (metis empty_iff validmodel_imp_no_offending)
    done
  corollary valid_without_offending_flows:
  "\<lbrakk> f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow> eval_model (delete_edges G f) nP"
    by(simp add: remove_offending_flows_imp_model_valid)

  lemma set_offending_flows_simp: 
    "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow>
      set_offending_flows G nP = {F. F \<subseteq> edges G \<and>
        (\<not> eval_model G nP \<and> eval_model \<lparr>nodes = nodes G, edges = edges G - F\<rparr> nP) \<and>
        (\<forall>(e1, e2)\<in>F. \<not> eval_model \<lparr>nodes = nodes G, edges = {(e1, e2)} \<union> (edges G - F)\<rparr> nP)}"
    apply(simp only: set_offending_flows_def is_offending_flows_min_set_def 
      is_offending_flows_def delete_edges_simp2 add_edge_def graph.select_convs)
    apply(subgoal_tac "\<And>F e1 e2. F \<subseteq> edges G \<Longrightarrow> (e1, e2) \<in> F \<Longrightarrow> nodes G \<union> {e1, e2} = nodes G")
     apply fastforce
    apply(simp add: valid_graph_def)
    by (metis fst_conv imageI in_mono insert_absorb snd_conv)

   end



print_locale! NetworkModel_withOffendingFlows



text {* The offending flows can be empty even for an invalid model!*}
  lemma "NetworkModel_withOffendingFlows.set_offending_flows (\<lambda>_ _. False) 
    \<lparr> nodes = set [V ''v1''], edges=set [] \<rparr> id = set []"
  by(simp add: NetworkModel_withOffendingFlows.set_offending_flows_def 
    NetworkModel_withOffendingFlows.is_offending_flows_min_set_def NetworkModel_withOffendingFlows.is_offending_flows_def)
  lemma "NetworkModel_withOffendingFlows.set_offending_flows (\<lambda>_ _. False) 
    \<lparr> nodes = set [V ''v1'', V ''v2''], edges= set [(V ''v1'', V ''v2'')] \<rparr> id = set []"
  by(simp add: NetworkModel_withOffendingFlows.set_offending_flows_def 
    NetworkModel_withOffendingFlows.is_offending_flows_min_set_def NetworkModel_withOffendingFlows.is_offending_flows_def)

text {*There exists an eval_model such that the model is invalid and no offending flows exits.*}
  lemma "\<exists>eval_model. \<not> eval_model G nP \<and> NetworkModel_withOffendingFlows.set_offending_flows eval_model G nP = {}"
  apply(simp add: NetworkModel_withOffendingFlows.set_offending_flows_def
    NetworkModel_withOffendingFlows.is_offending_flows_min_set_def NetworkModel_withOffendingFlows.is_offending_flows_def)
  apply(rule_tac x="(\<lambda>_ _. False)" in exI)
  apply(simp)
  done


text{*Thus, we introduce a usefullness property that prohibits such useless models.*}

  text{*Usefullness properties*}
  locale NetworkModel_preliminaries = NetworkModel_withOffendingFlows eval_model verify_globals
    for eval_model::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and verify_globals::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    +
    assumes 
      defined_offending:
      "\<lbrakk> valid_graph G; \<not> eval_model G nP \<rbrakk> \<Longrightarrow> set_offending_flows G nP \<noteq> {}"
    and
      mono_eval_model:
      "\<lbrakk> valid_graph \<lparr> nodes = N, edges = E \<rparr>; E' \<subseteq> E; eval_model \<lparr> nodes = N, edges = E \<rparr> nP \<rbrakk> \<Longrightarrow> 
        eval_model \<lparr> nodes = N, edges = E' \<rparr> nP"
    and mono_offending:
      "\<lbrakk> valid_graph G; is_offending_flows ff G nP \<rbrakk> \<Longrightarrow> is_offending_flows (ff \<union> f') G nP"
  begin

  text {*
  For instance proofs:
    Have a look at NetworkModel_withOffendingFlows_lemmata.thy
    There is a definition of eval_model_mono. It impplies mono_eval_model and mono_offending
    apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_eval_model_mono[OF eval_model_mono])
    apply(fact NetworkModel_withOffendingFlows.eval_model_mono_imp_is_offending_flows_mono[OF eval_model_mono])
  
    In addition, NetworkModel_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF eval_model_mono] gives a nice proof rule for
    defined_offending
  
    Basically, eval_model_mono. implies almost all assumptions here and is equal to mono_eval_model.
  *}

  lemma offending_notevalD: "f \<in> set_offending_flows G nP \<Longrightarrow> \<not> eval_model G nP"
    by (metis NetworkModel_withOffendingFlows.validmodel_imp_no_offending empty_iff)
  end


  text {* The base network model: default-node-properties is a secure default value.*}
  text {* Some notes about the notation:
          @{text "fst ` f"} means to apply the function @{text "fst"} to the set @{text "f"} elementwise.
          In the context of network graphs: If @{text "f"} is a set of directed edges 
          @{text "f = {(s,r) \<in> edges G. s=senders, r=receivers}"}, then @{text "fst ` f"}
          is the set of senders and @{text "snd ` f"} the set of receivers.*}

  locale NetworkModel = NetworkModel_preliminaries eval_model verify_globals
    for eval_model::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and verify_globals::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    +
    fixes default_node_properties :: "'a" ("\<bottom>") 
    and target_focus :: "bool"
    assumes 
      -- "default value can never turn an invalid model to valid."
      -- {*Idea: Giving an offending host the default configuration value does not change the validity of the model. 
        I.e this reconfiguration does not remove information, thus preserves all security critical information.
        Thought experiment preliminaries: Can a default configuration ever solve an existing security violation? NO!
        Thought experiment 1: admin forgot to configure host, hence it is handled by default configuration value ..
        Thought experiment 2: new node (attacker) is added to the network. What is its default configuration value ..*}
      default_secure:
      "\<lbrakk> valid_graph G; \<not> eval_model G nP; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
        (\<not> target_focus \<longrightarrow> i \<in> fst ` f \<longrightarrow> \<not> eval_model G (nP(i := \<bottom>))) \<and>
        (target_focus \<longrightarrow> i \<in> snd ` f \<longrightarrow> \<not> eval_model G (nP(i := \<bottom>)))"
      and
      default_unique:
      "otherbot \<noteq> \<bottom> \<Longrightarrow> 
        \<exists> G nP i f. valid_graph (G::('v::vertex) graph) \<and> \<not> eval_model G nP \<and> f \<in> set_offending_flows G nP \<and> 
         eval_model (delete_edges G f) nP \<and>
         (\<not> target_focus \<longrightarrow> i \<in> fst ` f \<and> eval_model G (nP(i := otherbot))) \<and>
         (target_focus \<longrightarrow> i \<in> snd ` f \<and> eval_model G (nP(i := otherbot))) "
      (*and
      --{*verify_globals does not depend on graph topology, i.e. semantics is in eval_model*}
      verify_globals_sound:
      "verify_globals G nP gP \<Longrightarrow> 
        (\<forall> v. verify_globals (add_node v G) nP gP) \<and> 
        (\<forall> v \<in> nodes G. verify_globals (delete_node v G) nP gP) \<and> 
        (\<forall> v\<^sub>1 v\<^sub>2. verify_globals (add_edge v\<^sub>1 v\<^sub>2 G) nP gP) \<and> 
        (\<forall> (v\<^sub>1, v\<^sub>2) \<in> edges G. verify_globals (delete_edge v\<^sub>1 v\<^sub>2 G) nP gP)"*)
   begin
    -- "Removes option type, replaces with default node property"
    fun node_props :: "('v, 'a, 'b) NetworkModel_Params \<Rightarrow> ('v \<Rightarrow> 'a)" where
    "node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> \<bottom>))"

    definition node_props_formaldef :: "('v, 'a, 'b) NetworkModel_Params \<Rightarrow> ('v \<Rightarrow> 'a)" where
    "node_props_formaldef P \<equiv>
    (\<lambda> i. (if i \<in> dom (node_properties P) then the (node_properties P i) else \<bottom>))"

    lemma node_props_eq_node_props_formaldef: "node_props_formaldef = node_props"
     apply(simp add: fun_eq_iff node_props_formaldef_def)
     apply(rule allI)+
     by (metis (lifting, mono_tags) domD domIff option.simps(4) option.simps(5) the.simps)


    definition eval::"'v graph \<Rightarrow> ('v, 'a, 'b)NetworkModel_Params \<Rightarrow> bool" where
    "eval G P \<equiv> valid_graph G \<and> verify_globals G (node_props P) (model_global_properties P) \<and> 
          eval_model G (node_props P)"


    -- "Unbound variables are implicitly all-quantified by mathematical rules. Thus, we require default-secure for all possible graphs, configurations, ..."
    lemma "\<forall> G nP f i. (valid_graph G \<and> \<not> eval_model G nP \<and> f \<in> set_offending_flows G nP \<and> eval_model (delete_edges G f) nP) \<longrightarrow>
        (\<not> target_focus \<longrightarrow> i \<in> fst ` f \<longrightarrow> \<not> eval_model G (nP(i := \<bottom>))) \<and>
        (target_focus \<longrightarrow> i \<in> snd ` f \<longrightarrow>\<not> eval_model G (nP(i := \<bottom>)))"
    by(blast dest:default_secure)

    (* declare[[show_types]] *)
    lemma unique_common_math_notation:
    assumes a: "\<forall>G nP i f. valid_graph (G::('v::vertex) graph) \<and> \<not> eval_model G nP \<and> f \<in> set_offending_flows G nP \<and> 
         eval_model (delete_edges G f) nP \<and> 
         (\<not> target_focus \<longrightarrow> i \<in> fst ` f \<longrightarrow> \<not> eval_model G (nP(i := otherbot))) \<and>
         (target_focus \<longrightarrow> i \<in> snd ` f \<longrightarrow> \<not> eval_model G (nP(i := otherbot)))"
    shows "otherbot = \<bottom>"
    proof -
      have or_imp_eq: "\<And>P Q. \<not> target_focus \<and> P \<or> target_focus \<and> Q \<longleftrightarrow> (\<not>target_focus \<longrightarrow> P) \<and> (target_focus \<longrightarrow> Q)" by blast
      from default_unique have "\<not> ( \<exists>G nP i f.
           valid_graph G \<and>
           \<not> eval_model G nP \<and>
           f \<in> set_offending_flows G nP \<and>
           eval_model (delete_edges G f) nP \<and>
           (\<not> target_focus \<longrightarrow> i \<in> fst ` f \<and> eval_model G (nP(i := otherbot))) \<and> (target_focus \<longrightarrow> i \<in> snd ` f \<and> eval_model G (nP(i := otherbot))))
      \<Longrightarrow> otherbot = \<bottom>" by blast
      from this a have "(\<not> ( \<exists>G nP i f.(
           (\<not> target_focus \<longrightarrow> i \<in> fst` f \<and> eval_model G (nP(i := otherbot))) \<and> (target_focus \<longrightarrow> i \<in> snd` f \<and> eval_model G (nP(i := otherbot))))))
      \<longrightarrow> otherbot = \<bottom>"
      by blast
      hence "(\<forall>G nP i f. (
           (\<not> target_focus \<longrightarrow> i \<in> fst` f \<longrightarrow> \<not> eval_model G (nP(i := otherbot))) \<and> (target_focus \<longrightarrow> i \<in> snd` f \<longrightarrow> \<not> eval_model G (nP(i := otherbot)))))
      \<longrightarrow> otherbot = \<bottom>"
      apply(simp only: HOL.not_ex)
      by(simp add:or_imp_eq)
      from this a show ?thesis by blast
      qed
   end

print_locale! NetworkModel



section{*Information flow Security and Access Control*}
text{*target_focus defines the offending host. Thus, it defines when the violation happens. 

If the violation happes when the sender sends, we have an access control model. I.e. 
the sender does not have the appropriate rights ro initiate the connection.

If the violation happens at the receiver, we have an information flow security model. I.e. 
the reciever lacks the appropiate security clearance to retrieve the (confidential) information. 
The violations happens only when the receiver reads the data.


We refine our definitions
*}

subsection {*Information flow security*}
  locale NetworkModel_IFS = NetworkModel_preliminaries eval_model verify_globals
      for eval_model::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
      and verify_globals::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
      +
      fixes default_node_properties :: "'a" ("\<bottom>") 
      assumes  default_secure_IFS:
        "\<lbrakk> valid_graph G; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
          \<forall>i \<in> snd` f. \<not> eval_model G (nP(i := \<bottom>))"
      and
      --{* If some otherbot fulfills default_secure, it must be \<bottom> 
             Hence, \<bottom> is uniquely defined *}
      default_unique_IFS:
      "(\<forall>G f nP i. valid_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> snd` f 
                \<longrightarrow> \<not> eval_model G (nP(i := otherbot))) \<Longrightarrow> otherbot = \<bottom>"
      begin
        lemma default_unique_EX_notation: "otherbot \<noteq> \<bottom> \<Longrightarrow> 
          \<exists> G nP i f. valid_graph G \<and> \<not> eval_model G nP \<and> f \<in> set_offending_flows G nP \<and> 
           eval_model (delete_edges G f) nP \<and>
           (i \<in> snd` f \<and> eval_model G (nP(i := otherbot)))"
          apply(erule contrapos_pp)
          apply(simp)
          using default_unique_IFS NetworkModel_withOffendingFlows.valid_without_offending_flows offending_notevalD
          by metis
      end
  
  sublocale NetworkModel_IFS \<subseteq> NetworkModel where target_focus=True
  apply(unfold_locales)
   apply(simp add: default_secure_IFS)
  apply(simp only: HOL.simp_thms)
  apply(drule default_unique_EX_notation)
  apply(assumption)
  done

  (*other direction*)
  locale NetworkModel_IFS_otherDirectrion = NetworkModel where target_focus=True
  sublocale NetworkModel_IFS_otherDirectrion \<subseteq> NetworkModel_IFS
  apply(unfold_locales)
   apply (metis default_secure offending_notevalD)
  apply(erule contrapos_pp)
  apply(simp)
  apply(drule default_unique)
  apply(simp)
  apply(blast)
  done
  


subsection {*Access Control Strategy*}
  locale NetworkModel_ACS = NetworkModel_preliminaries eval_model verify_globals
      for eval_model::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
      and verify_globals::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
      +
      fixes default_node_properties :: "'a" ("\<bottom>") 
      assumes  default_secure_ACS:
        "\<lbrakk> valid_graph G; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
          \<forall>i \<in> fst` f. \<not> eval_model G (nP(i := \<bottom>))"
      and
      default_unique_ACS:
      "(\<forall>G f nP i. valid_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> fst` f 
                \<longrightarrow> \<not> eval_model G (nP(i := otherbot))) \<Longrightarrow> otherbot = \<bottom>"
      begin
        lemma default_unique_EX_notation: "otherbot \<noteq> \<bottom> \<Longrightarrow> 
          \<exists> G nP i f. valid_graph G \<and> \<not> eval_model G nP \<and> f \<in> set_offending_flows G nP \<and> 
           eval_model (delete_edges G f) nP \<and>
           (i \<in> fst` f \<and> eval_model G (nP(i := otherbot)))"
          apply(erule contrapos_pp)
          apply(simp)
          using default_unique_ACS NetworkModel_withOffendingFlows.valid_without_offending_flows offending_notevalD
          by metis
      end
  
  sublocale NetworkModel_ACS \<subseteq> NetworkModel where target_focus=False
  apply(unfold_locales)
   apply(simp add: default_secure_ACS)
  apply(simp only: HOL.simp_thms)
  apply(drule default_unique_EX_notation)
  apply(assumption)
  done


  (*other direction*)
  locale NetworkModel_ACS_otherDirectrion = NetworkModel where target_focus=False
  sublocale NetworkModel_ACS_otherDirectrion \<subseteq> NetworkModel_ACS
  apply(unfold_locales)
   apply (metis default_secure offending_notevalD)
  apply(erule contrapos_pp)
  apply(simp)
  apply(drule default_unique)
  apply(simp)
  apply(blast)
  done


text{* The sublocale relation ship tells that the simplified NetworkModel_ACL and NetworkModel_IFS 
  assumptions suffice to do tho whole NetworkModel thing. The other direction is just for completeness.  *}

end
