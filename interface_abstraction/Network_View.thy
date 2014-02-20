theory Network_View
imports Network
begin

text{*the view for a fixed packet header*}


section{*The view of a fixed packet*}
  text{*For a fixed packet with a fixed header, its global network view is defined. 
        For any start interface the packet is set out, the interfaces the packet can go next is recoreded.
        
        Essentially, view is a relation or the edges of a graph. This graph describes how the packet can move. 
          The forwarding (and transfer) function is removed, the packet can directly move along the edges!

        It is the view a packet has from the network.
        *}
  definition view :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
    "view N hdr = {(src, dst). src \<in> interfaces N \<and> dst \<in> traverse N hdr src}"

  text{*Alternative definition of view: For all interfaces in the network, collect the next hops. *}
  lemma view_alt: "view N hdr = (\<Union>src \<in> interfaces N. {src} \<times> traverse N hdr src)"
    apply(simp add: view_def)
    apply(rule)
    apply blast
    apply(rule)
    by(clarify)



 lemma view_subseteq_interfaces_x_interfaces: assumes wf_N: "wellformed_network N"
    shows "view N hdr \<subseteq> interfaces N \<times> interfaces N"
    apply(simp add: view_alt)
    using traverse_subseteq_interfaces[OF wf_N] by blast

  lemma view_finite: assumes wf_N: "wellformed_network N"
    shows "finite (view N hdr)"
    apply(simp add: view_alt)
    apply(subst finite_UN[OF wellformed_network.finite_interfaces[OF wf_N]])
    apply(clarify)
    apply(rule finite_cartesian_product)
    apply simp
    using traverse_finite[OF wf_N] by simp
  lemma finite_view_trancl: assumes wf_N: "wellformed_network N" shows "finite ((view N hdr)\<^sup>+)"
    using view_finite[OF wf_N] finite_trancl by simp

  text{*The (bounded) reflexive transitive closure*}
  (*In isabelle, saying only ^* would be transitive closure plus all reflexive elementes of type 'v interface. We only want all (interface N). 
    For infinite types, ^* is infinite as it contains ALL {(a,a) | a of tpye}*)
  definition view_rtrancl :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
    "view_rtrancl N hdr \<equiv> {(src,dst). src \<in> interfaces N \<and> dst \<in> interfaces N \<and> (src, dst) \<in> (view N hdr)\<^sup>*}"

  lemma assumes wf_N: "wellformed_network N" shows "finite (view_rtrancl N hdr)"
    proof -
      have "{(src,dst). src \<in> interfaces N \<and> dst \<in> interfaces N \<and> (src, dst) \<in> (view N hdr)\<^sup>*} \<subseteq> interfaces N \<times> interfaces N" by blast
      thus ?thesis using wellformed_network.finite_interfaces[OF wf_N] unfolding view_rtrancl_def by (metis (lifting, no_types) finite_SigmaI rev_finite_subset)
    qed

  lemma view_rtrancl_alt: 
    assumes wf_N: "wellformed_network N" shows "view_rtrancl N hdr = (view N hdr)\<^sup>+ \<union> {(a,a) | a . a \<in> interfaces N}"
    unfolding view_rtrancl_def
    apply(rule equalityI)
    apply(clarify)
    apply (metis rtranclD)
    (* r to l*)
    apply(clarify)
    apply(rule)
    apply(erule Set.UnE)
    using view_subseteq_interfaces_x_interfaces[OF wf_N] apply (metis SigmaE2 converse_tranclE trancl_mono)
    apply fastforce
    apply(rule)
    apply(erule Set.UnE)
    using view_subseteq_interfaces_x_interfaces[OF wf_N] apply (metis mem_Sigma_iff r_into_trancl' subsetI subset_antisym trancl_mono trancl_subset_Sigma)
    apply fastforce
    apply(erule Set.UnE)
    apply(simp)
    apply(simp)
    done


  lemma start_view_rtrancl:
    assumes wf_N: "wellformed_network N"
    shows "{dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>*} = (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view N hdr)\<^sup>+}) \<union> (succ N start)" (is "?LHS = ?RHS")
    proof -
      have view_interfaces: "(view N hdr) `` (interfaces N) \<subseteq> (interfaces N)"
        using view_subseteq_interfaces_x_interfaces[OF wf_N] by blast
      have "?LHS \<subseteq> interfaces N"
        apply(auto)
        using succ_subseteq_interfaces[OF wf_N] Image_closed_trancl[OF view_interfaces] by auto
      have "?LHS = {dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> view_rtrancl N hdr}"
        apply(simp add: view_rtrancl_def)
        apply(rule Set.Collect_cong)
        apply(rule iffI)
        apply(erule bexE)
        apply(rule_tac x="first_hop" in bexI)
        apply(rule)
        using succ_subseteq_interfaces[OF wf_N] apply blast
        apply(rule)
        using `?LHS \<subseteq> interfaces N` apply blast
        apply(simp_all)
        apply(erule bexE)
        apply(rule_tac x="first_hop" in bexI)
        by(simp_all)
      also have "\<dots> = {dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>+} \<union> (succ N start)"
        apply(subst view_rtrancl_alt[OF wf_N])
        apply(rule)
        apply fastforce
        apply(rule)
        apply(simp)
        apply(erule disjE)
        apply(erule bexE)
        apply(rule_tac x="first_hop" in bexI)
        apply(simp_all)
        apply(rule_tac x="x" in bexI)
        apply(simp_all)
        using succ_subseteq_interfaces[OF wf_N] by blast
      also have "\<dots> = (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view N hdr)\<^sup>+}) \<union> (succ N start)"
        by(simp add: Complete_Lattices.Collect_bex_eq)
     finally show "?LHS = ?RHS" .
   qed
  (*lemma star_view_rtrancl:
    assumes wf_N: "wellformed_network N"
    and     start_iface: "start \<in> interfaces N"
    shows "{dst. (start, dst) \<in> (view N hdr)\<^sup>*} = {dst. (start, dst) \<in> (view N hdr)\<^sup>+} \<union> {start}" (is "?LHS = ?RHS")
    proof -
      have "?LHS = {dst. (start, dst) \<in> view_rtrancl N hdr}"
        unfolding view_rtrancl_def
        apply(simp)
        apply(auto simp add: start_iface)
        using view_subseteq_interfaces_x_interfaces[OF wf_N] by (metis Image_closed_trancl Image_subset rev_ImageI start_iface)
      also have "{dst. (start, dst) \<in> view_rtrancl N hdr} = ?RHS"
       apply(subst view_rtrancl_alt[OF wf_N])
       apply(rule)
       apply fastforce
       apply(rule)
       apply(simp)
       using start_iface apply fastforce
       done
     finally show "?LHS = ?RHS" .
   qed*)
     

section{*Reachable and view*}
  text{*intuitive reachable definition and defining reachability by the rtrancl over the view relation is equal. *}
  theorem reachable_eq_rtrancl_view:
      assumes wf_N: "wellformed_network N"
      shows "reachable N hdr start = {dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>*}"
    proof(rule equalityI)
      show "reachable N hdr start \<subseteq> {dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>*}"
        proof(rule, simp)
          fix x show "x \<in> reachable N hdr start \<Longrightarrow> \<exists>first_hop\<in>succ N start. (first_hop, x) \<in> (view N hdr)\<^sup>*"
            proof(induction x rule:reachable_induct)
              case(Start first_hop)
                hence "first_hop\<in>succ N start \<and> (first_hop, first_hop) \<in> (view N hdr)\<^sup>*" by(simp add: view_def)
                thus ?case by blast
            next
              case(Step hop next_hop)
                from reachable_subseteq_interfaces[OF wf_N] Step(1) have "hop \<in> interfaces N" by blast
                hence  "(hop, next_hop) \<in> {(src, dst). src \<in> interfaces N \<and> dst \<in> traverse N hdr src}"
                  by(simp add: Step(2))
                hence  next_rtran: "(hop, next_hop) \<in> view N hdr"
                  by(simp add: view_def)
                from Step(3) obtain first_hop where "first_hop\<in>succ N start" and first_rtran: "(first_hop, hop) \<in> (view N hdr)\<^sup>*" by blast
                from `first_hop\<in>succ N start` rtrancl.rtrancl_into_rtrancl[OF first_rtran next_rtran]
                show ?case by blast
            qed
       qed
    next
    show "{dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>*} \<subseteq> reachable N hdr start"   
      proof(rule, clarify)
        fix x first_hop
        assume "first_hop \<in> succ N start"
        show "(first_hop, x) \<in> (view N hdr)\<^sup>* \<Longrightarrow> x \<in> reachable N hdr start"
          proof(induction rule: rtrancl_induct)
            case base
              thus ?case using reachable.intros(1) `first_hop \<in> succ N start` .
            case(step y z)
              thus ?case by(auto intro: reachable.intros(2) simp add: view_def)
            qed
          qed
   qed
  text{*reachability is exactly:
    the first hop plus everything that can be transitively reached via the first hop. *}
  corollary reachable_eq_rtrancl_view2:
   "\<lbrakk> wellformed_network N \<rbrakk> \<Longrightarrow> reachable N hdr start = (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view N hdr)\<^sup>+}) \<union> (succ N start)"
   by(simp add: reachable_eq_rtrancl_view start_view_rtrancl)



subsection{*About reachability*}
  text{*With the view, a property of reachability can be shown*}
  lemma reachable_subset_start_iff:
    assumes wf_N: "wellformed_network N"
    shows "reachable N hdr start \<subseteq> succ N start \<longleftrightarrow> (\<forall>first_hop \<in> succ N start. traverse N hdr first_hop \<subseteq> succ N start)"
    proof
      assume only_reach_succ: "reachable N hdr start \<subseteq> succ N start"
      show "\<forall>first_hop\<in>succ N start. traverse N hdr first_hop \<subseteq> succ N start"
        proof 
        fix first_hop
        assume f: "first_hop \<in> succ N start"
        from only_reach_succ have reach_eq_succ: "reachable N hdr start = succ N start" 
          using Network.succ_subseteq_reachable by fast

        have view_dst_simp: "\<And> first_hop. {dst. first_hop \<in> interfaces N \<and> dst \<in> traverse N hdr first_hop} = 
          {dst \<in> (\<Union>p\<in>forward N hdr first_hop. succ N \<lparr>entity = entity first_hop, port = p\<rparr>). first_hop \<in> interfaces N}"
          by(simp only: traverse_def, blast)
        
        have "{dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>*} = 
            (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view N hdr)\<^sup>*})" by blast

        from this reach_eq_succ f have "{dst. (first_hop, dst) \<in> (view N hdr)\<^sup>*} \<subseteq> succ N start"
          using reachable_eq_rtrancl_view[OF wf_N] by auto
        
        hence "{dst. (first_hop, dst) \<in> (view N hdr)} \<subseteq> succ N start" using f  by blast
        hence "(\<Union>p\<in>forward N hdr first_hop. succ N \<lparr>entity = entity first_hop, port = p\<rparr>) \<subseteq> succ N start" using f
          apply(simp add: view_def)                                          
          apply(simp only: view_dst_simp)
          by (metis reach_eq_succ reachable.simps subsetI traverse_def)
        thus "traverse N hdr first_hop \<subseteq> succ N start"
          by(simp add: traverse_def)
        qed
      next
      assume only_traverse_succ: "\<forall>first_hop \<in> succ N start. traverse N hdr first_hop \<subseteq> succ N start"
      {
        fix x
        have "x \<in> reachable N hdr start \<Longrightarrow> x \<in> succ N start"
        proof(induction rule: reachable_induct)
          case Start thus ?case by simp
          next
          case Step thus ?case using only_traverse_succ by fast
        qed
      }
      thus "reachable N hdr start \<subseteq> succ N start" by blast
    qed






end
