theory Network
imports Entity
begin

(*examples and code equations are in Network_ex*)

section{*A network consisting of entities*}
  text{*packet header*}
  type_synonym 'v hdr="('v entity \<times> 'v entity)" -- "packet header: (src address, dst address)"


  text{*fwd is an entity's packet forward function: 
      A packet arriving at port with a header (src, dst) is outputted to a set of ports.
      Example: flooding switch with 3 ports. If packet arrives at port 1, output at ports {2,3}.*}
  type_synonym 'v fwd_fun="port \<Rightarrow> 'v hdr \<Rightarrow> port set"

  
  text{* A network consists of
          A set of interfaces (ports at entities where packets are moved between)
          A forwarding behaviour per entity
          Links betweend interfaces (edges in a graph or cables in real world)*}
  record 'v network = interfaces :: "'v interface set"
                      forwarding :: "'v entity \<Rightarrow> 'v fwd_fun"
                      links      :: "(('v interface) \<times> ('v interface)) set"

  text{*here is an abbreviatin for forwarding in network N the packet with hdr at input interface hop:
          get forwarding function for hop, apply input port and hdr to it, get result*}
  abbreviation forward :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> port set" where
    "forward N hdr hop \<equiv> ((forwarding N) (entity hop)) (port hop) hdr"

  text{*wellformed network.
        Links must be subset of interfaces, think of it as a graph. 
        names_disjunct verifies that no confusion arises if there is a switch ''x'' and a host ''x''.*}
  locale wellformed_network =
    fixes N :: "'v network"
    assumes fst_links: "fst ` links N \<subseteq> interfaces N"
    and     snd_links: "snd ` links N \<subseteq> interfaces N"
    and     finite_interfaces: "finite (interfaces N)"
    and     names_disjunct: "{host. Host host \<in> entity ` interfaces N} \<inter> {box. NetworkBox box \<in> entity ` interfaces N} = {}"
    begin
      lemma finite_links: "finite (links N)"
      proof - 
        have "\<And> X. X \<subseteq> fst ` X \<times> snd ` X" by force
        hence "links N \<subseteq> fst ` links N \<times> snd ` links N" by blast
        from this rev_finite_subset[OF finite_interfaces fst_links] rev_finite_subset[OF finite_interfaces snd_links] show ?thesis
          by (metis finite_cartesian_product rev_finite_subset)
      qed

      lemma finite_entity_interfaces: "finite (entity ` interfaces N)" by(simp add: finite_interfaces)
      lemma finite_entity_name_entity_interfaces: "finite (entity_name ` entity ` interfaces N)" by(simp add: finite_entity_interfaces)
      
      lemma names_disjunct_2: "\<forall>x\<in>interfaces N. \<forall>y\<in>interfaces N. entity_name (entity x) = entity_name (entity y) \<longrightarrow> entity x = entity y"
        apply(clarify)
        apply(case_tac x, rename_tac entity_x port_x, case_tac y, rename_tac entity_y port_y, clarsimp)
        apply(case_tac entity_x, case_tac entity_y)
        apply(simp add: entity_name_def)
        apply(simp add: entity_name_def)
        using names_disjunct apply force
        apply(clarsimp)
        apply(case_tac entity_y)
        apply(simp add: entity_name_def)
        using names_disjunct apply force
        apply(simp add: entity_name_def)
        done
      lemma "card (entity ` interfaces N) = card (entity_name ` entity ` interfaces N)"
        thm Set_Interval.BIJ
        apply(subst Set_Interval.BIJ[OF finite_entity_interfaces finite_entity_name_entity_interfaces, symmetric])
        apply(rule_tac x="entity_name" in exI)
        apply(simp add: bij_betw_def inj_on_def)
        apply(fact names_disjunct_2)
        done
    end

   subsection{*Selecting hosts and NetworkBoxes*}
    text{*select all hosts in an interface set*}
    definition hosts :: "'v interface set \<Rightarrow> 'v interface set" where
      "hosts ifaces \<equiv> {e \<in> ifaces. \<exists> x. entity e = Host x}"
    (*hosts only contains hosts*)
    lemma "entity ` hosts ifaces = Host ` entity_name ` entity ` hosts ifaces"
      apply(simp add: hosts_def image_def)
      apply(rule Set.Collect_cong)
      apply(simp add: entity_name_def)
      by fastforce

    definition networkboxes :: "'v interface set \<Rightarrow> 'v interface set" where
      "networkboxes ifaces \<equiv> {e \<in> ifaces. \<exists> x. entity e = NetworkBox x}"

    subsection{*Moving packets*}
      text{*The following simple model is used. A packet is moved from input interface to input interface.
            Therefore, two steps are necessary. 
            1) the entity forwarding function outputs the packet at output interfaces. 
            2) the packet traverses the link and thus arrives at the next input interface. *}

      text{*succ moves packet along links. It is step 2*}
      definition succ :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "succ N out_iface \<equiv> {in_iface. (out_iface, in_iface) \<in> links N}"

      lemma succ_subseteq_interfaces: assumes wf_N: "wellformed_network N" shows "succ N x \<subseteq> interfaces N"
        apply(simp add: succ_def)
        using wellformed_network.snd_links[OF wf_N] by force
      lemma succ_subset_networkboxes: "succ N start \<subseteq> networkboxes (succ N start) \<Longrightarrow> succ N start = networkboxes (succ N start)"
        by(simp add: networkboxes_def, blast)
  
      text{*A packet traverses a hop. It performs steps 1 and 2.*}
      (*recall: (forward N hdr hop) return the ports where the packet leaves the entity*)
      definition traverse :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "traverse N hdr hop \<equiv> \<Union> p \<in> (forward N hdr hop). succ N \<lparr>entity = entity hop, port = p\<rparr>"

      (*traverse jumps over routers, it is not in the links. the forwarding function moves packets in routeres, there is no corresponding link IN an entity for it. *)
      lemma traverse_subseteq_interfaces: "wellformed_network N \<Longrightarrow> traverse N hdr hop \<subseteq> interfaces N"
        apply(simp add: traverse_def succ_def)
        apply(drule wellformed_network.snd_links)
        by force
      corollary traverse_finite: assumes wf_N: "wellformed_network N"
        shows "finite (traverse N hdr hop)"
        using traverse_subseteq_interfaces[OF wf_N] wellformed_network.finite_interfaces[OF wf_N] by (metis rev_finite_subset)

 

    subsection {*Reachable interfaces*}
      text{* Traverese performs one step to move a packet. The reachable set defines all reachable entities for a given start node of a packet. *}
      (* we can allow spoofing by allowing an arbitrary packet header.*)
      text{*reachable(1): a packet starts at a start node. All directly reachable nodes are reachable.
            reachable(2): if a hop is reachables, then the next hop is also reachable. *}
      inductive_set reachable :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set"
      for N::"'v network" and "pkt_hdr"::"'v hdr" and "start"::"'v interface"
      where
        "first_hop \<in> succ N start \<Longrightarrow> first_hop \<in> reachable N pkt_hdr start" |
        "hop \<in> reachable N pkt_hdr start \<Longrightarrow> next_hop \<in> (traverse N pkt_hdr hop) \<Longrightarrow> next_hop \<in> reachable N pkt_hdr start"

      (*tuned induction rule*)
      lemmas reachable_induct = reachable.induct[case_names Start Step]
      thm reachable_induct

      lemma reachable_subseteq_interfaces:
        assumes wf_N: "wellformed_network N"
        shows "reachable N pkt_hdr start \<subseteq> interfaces N"
        proof
          fix x
          show "x \<in> reachable N pkt_hdr start \<Longrightarrow> x \<in> interfaces N"
            apply(induction x rule: reachable_induct)
            using succ_subseteq_interfaces[OF wf_N] apply blast
            using traverse_subseteq_interfaces[OF wf_N] by fast
        qed

    lemma "succ N start \<subseteq> reachable N hdr start"
      by(auto intro: reachable.intros)

    subsection{*The view of a packet*}
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
        also have "{dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> view_rtrancl N hdr} = {dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>+} \<union> (succ N start)"
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
        also have "{dst. \<exists>first_hop \<in> succ N start. (first_hop, dst) \<in> (view N hdr)\<^sup>+} \<union> (succ N start) = (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view N hdr)\<^sup>+}) \<union> (succ N start)"
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



  section{*Sending packets to hosts*}
    text{*a packet from start is sent to dst. Which hosts gets the packet?*}
    definition send_to :: "'v network \<Rightarrow> 'v interface \<Rightarrow> 'v entity \<Rightarrow> 'v interface set" where
      "send_to N start dst \<equiv> hosts (reachable N (entity start, dst) start)"


  section{*Can hosts spoof?*}
    definition host_cannot_spoof :: "'v network \<Rightarrow> 'v interface \<Rightarrow> bool" where
      "host_cannot_spoof N start \<equiv> \<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> reachable N (spoofed, dst) start \<subseteq> networkboxes (succ N start)"


    (*if spoofed adresses exist ...*)
    lemma "\<lbrakk> wellformed_network N \<rbrakk> \<Longrightarrow> \<exists> spoofed. spoofed \<noteq> entity start \<Longrightarrow> host_cannot_spoof N start \<Longrightarrow> succ N start = networkboxes (succ N start)"
      apply(rule succ_subset_networkboxes)
      apply(simp add: host_cannot_spoof_def reachable_eq_rtrancl_view2)
      apply(erule exE)
      by presburger

    (*if the adress space is so small that there is only one adress, a host cannot spoof (oviously)*)
    lemma "\<not> (\<exists> spoofed. spoofed \<noteq> entity start) \<Longrightarrow> host_cannot_spoof N start"
      by(simp add: host_cannot_spoof_def)
      

    text{*if all networkboxes connected to start block spoofing, start cannot spoof*}
    lemma 
      assumes connected_to_networkboxes: "succ N start = networkboxes (succ N start)" 
        and   no_fwd_spoofed: "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {})"
      shows "host_cannot_spoof N start"
      proof -
        {
        have "\<forall> spoofed dst. spoofed \<noteq> entity start \<longrightarrow> (\<forall> first_hop \<in> succ N start. (forward N (spoofed, dst) first_hop) = {}) \<Longrightarrow>
                  host_cannot_spoof N start"
        apply(simp add: host_cannot_spoof_def)
        apply(clarify)
        apply(erule reachable_induct)
        apply(simp)
        using connected_to_networkboxes apply fast
        apply(simp add: traverse_def)
        using connected_to_networkboxes apply blast
        done
        }
        from this no_fwd_spoofed show ?thesis by simp
      qed






section{*TEST TEST TES TEST of UNIO*}
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = {2,3,4}" by eval
  lemma "(\<Union>n\<in>{1::nat, 2, 3}. {n + 1}) = {2, 3, 4}" by eval
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = set (map (\<lambda>n. n+1) [1,2,3])" by eval

(*
  locale X =
    fixes N1 N2
    assumes well_n1: "wellformed_network N1"
    assumes well_n2: "wellformed_network N2"
  begin
  end

  sublocale X \<subseteq> n1!: wellformed_network N1
    by (rule well_n1)
  sublocale X \<subseteq> n2!: wellformed_network N2
    by (rule well_n2)
  
    context X
    begin
      
    end
*)


end
