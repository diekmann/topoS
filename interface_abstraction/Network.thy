theory Network
imports Entity
begin

(*TODO split into view and props
  spoofing
  treepath
  policycompliance
  *)

(*examples and code equations are in Network_ex*)

section{*A network consisting of entities*}
  text{*packet header*}

  (*TODO make generic hdr
  datatype 'v srcdsthdr = SrcDstHdr "'v entity \<times> 'v entity"
  value "SrcDstHdr (Host ''Alice'', Host ''Bob'') :: string srcdsthdr"
  *)
  (*record 'v hdr = src_addr :: "'v entity"
                  dst_addr :: "'v entity"
                  proto :: nat
                   src_port :: nat
                   dst_port ::nat*)
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
  lemma start_notininterfaces_succ_empty: assumes wf_N: "wellformed_network N" shows "start \<notin> interfaces N \<Longrightarrow> succ N start = {}"
    apply(simp add: succ_def)
    using wellformed_network.fst_links[OF wf_N] by fastforce

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

  lemma start_notininterfaces_reachableempty: assumes wf_N: "wellformed_network N" shows "start \<notin> interfaces N \<Longrightarrow> reachable N hdr start = {}"
    apply(drule start_notininterfaces_succ_empty[OF wf_N])
    apply(rule, rule)
    apply(erule reachable_induct)
    by(auto)
  lemma succ_subseteq_reachable: "succ N start \<subseteq> reachable N hdr start"
    by(auto intro: reachable.intros)





section{*Sending packets to hosts*}
  text{*a packet from start is sent to dst. Which hosts gets the packet?*}
  definition send_to :: "'v network \<Rightarrow> 'v interface \<Rightarrow> 'v entity \<Rightarrow> 'v interface set" where
    "send_to N start dst \<equiv> hosts (reachable N (entity start, dst) start)"



section{*Compliance with a Security Policy*}
    (*policy is a graph ... cannot spoof .... *)




end
