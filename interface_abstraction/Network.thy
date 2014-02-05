theory Network
imports Entity
begin

section{*A network consisting of entities*}
  text{*packet header*}
  type_synonym 'v hdr="('v entity \<times> 'v entity)" -- "packet header: (src address, dst address)"


  text{*fwd is an entity's packet forward function: 
      A packet arriving at port with a header (src, dst) is outputted to a set of ports*}
  type_synonym 'v fwd_fun="port \<Rightarrow> 'v hdr \<Rightarrow> port set"

  
  text{* A network consists of
          A set of interfaces (ports at entities where packets are moved between)
          A forwarding behaviour per entity
          Links betweend interfaces (edges in a graph or cables in real world)*}
  record 'v network = interfaces :: "'v interface set"
                      forwarding :: "'v entity \<Rightarrow> 'v fwd_fun"
                      links      :: "(('v interface) \<times> ('v interface)) set"


  text{*wellformed network. links must be subset of interfaces, think of it as a graph.*}
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

  text{*Example*}
    (*
      Alice   1
              /\
               |
               |
               \/
                1                   2         -->  1 Bob
                   ThreePortSwitch           /
                           3  <-------------/
                                             `---> 1 Carl
    *)
    definition "example_network = \<lparr> interfaces = {\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>,
                           \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 2 \<rparr>,
                           \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>,
                           \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>,
                           \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
                           \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>},
             forwarding = (\<lambda> e. 
                if e = NetworkBox ''threePortSwitch'' then 
                  (\<lambda> p (src,dst). if p = Port 1 then Port ` {2,3} else if p = Port 2 then Port ` {1,3} else if p = Port 3 then Port ` {1,2} else {})
                else
                  (\<lambda> p (src,dst). if e = src then {Port 1} else {})), (*Hosts (not necessarily) send out their own packets and drop the rest*)
             links = {
              (\<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>),
              (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>, \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>),
  
              (\<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>),
              (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>, \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>),
  
              (\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>),
              (\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>, \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>)
              }\<rparr>"

    interpretation example!: wellformed_network example_network
      by(unfold_locales, auto simp add: example_network_def)
    lemma wellformed_network_example_network: "wellformed_network example_network" by(unfold_locales)


    subsection{*A packet traverses a hop*}

      text{*transmitting a packet. A packet is ready to be send at output port out. It is send to all ports that are connected. *}


      text{*A packet leaving an interface (outgoing) and traversing a link and arriving at an incoming interface. *}
      text{*succ moves packet along links. *}
      definition succ :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "succ N out_iface \<equiv> {in_iface. (out_iface, in_iface) \<in> links N}"
        
      definition succ_code :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "succ_code N out_iface \<equiv> {in_iface \<in> interfaces N. (out_iface, in_iface) \<in> links N}"
      lemma succ_code_correct: "wellformed_network N \<Longrightarrow> succ_code N = succ N"
        apply(simp add: fun_eq_iff succ_def succ_code_def)
        apply(drule wellformed_network.snd_links)
        by force

      text{*Example*}
        lemma "succ_code example_network \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr> = 
          {\<lparr>entity = Host ''Bob'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval

      text{*A packet in network N with header hdr traverses hop hop. The output is the set of input interface at the nex hops*}
      definition traverse :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "traverse N hdr hop \<equiv> UNION (((forwarding N) (entity hop)) (port hop) hdr) (\<lambda>p. succ N \<lparr>entity = entity hop, port = p\<rparr>)"

      (*traverse jumps over routers, it is not in the links*)
      lemma traverse_subseteq_interfaces: "wellformed_network N \<Longrightarrow> traverse N hdr hop \<subseteq> interfaces N"
        apply(simp add: traverse_def succ_def)
        apply(drule wellformed_network.snd_links)
        by force

      definition traverse_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "traverse_code N hdr hop \<equiv> UNION (((forwarding N) (entity hop)) (port hop) hdr) (\<lambda>p. succ_code N \<lparr>entity = entity hop, port = p\<rparr>)"
      lemma traverse_code_correct: "wellformed_network N \<Longrightarrow> traverse_code N = traverse N"
        apply(simp add: fun_eq_iff traverse_code_def traverse_def)
        by(drule succ_code_correct, simp)


      text{*Example*}
        text{*Example: alice sends out packet, it arrives at switch*}
        lemma example_network_ex1:"traverse_code example_network (Host ''Alice'', Host ''Bob'') \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>  = {\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}" by eval
        text{*Example cont.: Switch forwards packet to Bob and Carl*}
        lemma example_network_ex2: "traverse_code example_network (Host ''Alice'', Host ''Bob'')  \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr> = {\<lparr>entity = Host ''Carl'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>}" by eval
        text{*Example cont.: Carl accepts packet (or drops it, he does not forward it)*}
        lemma example_network_ex3: "traverse_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Bob'', port = Port 1\<rparr> = {}" by eval
        lemma example_network_ex4: "traverse_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Carl'', port = Port 1\<rparr> = {}" by eval


    subsection {*Reachable interfaces*}
      text{*
        sending out a packet:
          the source address in the header must match
          the packet is send out according to the traverse function
        transmitting a packet:
          traverse it through the net
      *}
      (* we can allow spoofing by allowing an arbitrary packet header. UNION over all start points should give reachable_spoofing? *)
      inductive_set reachable :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set"
      for N::"'v network" and "pkt_hdr"::"'v hdr" and "start"::"'v interface"
      where
        "start \<in> (interfaces N) \<Longrightarrow> start \<in> reachable N pkt_hdr start" |
        "hop \<in> reachable N pkt_hdr start \<Longrightarrow> next_hop \<in> (traverse N pkt_hdr hop) \<Longrightarrow> next_hop \<in> reachable N pkt_hdr start"

      lemma reachable_subseteq_interfaces:
        assumes wf_N: "wellformed_network N"
        shows "x \<in> reachable N pkt_hdr start \<Longrightarrow> x \<in> interfaces N"
        apply(induction x rule: reachable.induct)
        apply(simp)
        using traverse_subseteq_interfaces[OF wf_N] by fast

      text{*Example*}
        lemma "\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr> \<in> reachable example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"
          apply(rule reachable.intros(2))
          apply(rule reachable.intros(2))
          apply(rule reachable.intros(1))
          (*apply(rule HOL.sym[of _ "entity \<lparr>entity = Host ''Alice'', port = Port (Suc 0)\<rparr>"]) (*need to select manually*)*)
          apply(simp add: example_network_def)
          apply(subst traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(simp, subst example_network_ex1[simplified])
          apply(simp)
          apply(subst traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(simp, subst example_network_ex2[simplified])
          apply(simp)
          done
        lemma "\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr> \<in> reachable example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"
          apply(rule reachable.intros(2))
          apply(rule reachable.intros(1))
          apply(simp add: example_network_def)
          apply(subst traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(simp, subst example_network_ex1[simplified], simp)
          done
        lemma "x \<in> reachable example_network (Host ''Alice'', Host ''Bob'')  \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> \<Longrightarrow> 
          x \<in> {\<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>,
               \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>,
               \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
               \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}"
          apply(induction rule: reachable.induct)
          apply(simp)
          (*step*)
          apply(case_tac "hop = \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>", simp)
          apply(subst(asm) traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(subst(asm) example_network_ex2[simplified])
          apply(fast)
          apply(case_tac "hop = \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>", simp)
          apply(subst(asm) traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(subst(asm) example_network_ex3[simplified])
          apply(fast)
          apply(case_tac "hop = \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>", simp)
          apply(subst(asm) traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(subst(asm) example_network_ex4[simplified])
          apply(fast)
          apply(simp)
          apply(subst(asm) traverse_code_correct[symmetric, OF wellformed_network_example_network])
          apply(subst(asm) example_network_ex1[simplified])
          by simp

    subsection{*The view of a packet*}
      definition view :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
        "view N hdr = {(src, dst). src \<in> interfaces N \<and> dst \<in> traverse N hdr src}"


      definition view_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
        "view_code N hdr = { src_dst \<in> interfaces N \<times> interfaces N. case src_dst of (src, dst) \<Rightarrow> dst \<in> traverse_code N hdr src}"
      lemma view_code_correct: "wellformed_network N \<Longrightarrow> view_code N = view N"
        apply(simp add: view_code_def view_def fun_eq_iff traverse_code_correct)
        apply(clarify)
        apply(rule equalityI)
        apply blast
        using traverse_subseteq_interfaces by fast

      lemma traverse_code_subseteq_interfaces: "src \<in> interfaces N \<Longrightarrow> dst \<in> traverse_code N hdr src \<Longrightarrow> dst \<in> interfaces N"
        by(simp add: traverse_code_def succ_code_def)
      (*more efficient, I guess. Only iterate over the interfaces*)
      lemma[code_unfold]: "view_code N hdr = UNION (interfaces N) (\<lambda> src. {src} \<times> traverse_code N hdr src)"
        apply(simp add: view_code_def)
        apply(rule)
        apply blast
        apply(rule)
        apply(clarify)
        apply(fact traverse_code_subseteq_interfaces)
        done

        
    (*
      the view jumps over routers. It essentially removes the traverse function. For example, if a packet arrives at switch port 1, it can continue to Bob and Carl directly. The fact that this happens via port 3 is hidden

      Alice   1 <-------------------.
        /\     |                    |
         |     |                    |
         |     |          ----------------------.
         |     \/        |          |           \/
         |      1 ------\<acute>          2 ----------> 1 Bob
         |      |  ThreePortSwitch  |       
         `------|--------- 3        |
                |                    `-------->  
                 `----------------------------> 1 Carl
    *)
        lemma "view_code example_network (Host ''Alice'', Host ''Bob'') = {
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>),
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>),
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>),
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>),
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>),
          (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 3\<rparr>, \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>),
          (\<lparr>entity = Host ''Alice'', port = Port 1\<rparr>, \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>)}" by eval

    (*the view transforms the graph into a new graph without the traverse function! *)

  
    theorem reachable_eq_rtrancl_view:
        assumes wf_N: "wellformed_network N"
        and     start_iface: "start \<in> interfaces N"
        shows "reachable N hdr start = {dst. (start, dst) \<in> (view N hdr)\<^sup>*}"
      apply(rule equalityI)
      apply(rule)
      apply(simp)
      apply(erule reachable.induct)
      apply(simp add: view_def)
      apply(simp add: view_def)
      apply(subgoal_tac "(hop, next_hop) \<in> {(src, dst). src \<in> interfaces N \<and> dst \<in> traverse N hdr src}")
      apply (metis (lifting, no_types) rtrancl.rtrancl_into_rtrancl)
      apply(simp)
      using reachable_subseteq_interfaces[OF wf_N] apply fast
      (*next, right to left subset*)
      apply(rule)
      apply(simp)
      apply(erule rtrancl_induct)
      apply(simp)
      apply(simp add: start_iface reachable.intros(1))
      apply(simp)
      apply(simp add: view_def)
      apply (metis (full_types) reachable.intros(2))
      done

section{*TEST of UNIO*}
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = {2,3,4}" by eval
  lemma "UNION {1::nat,2,3} (\<lambda>n. {n+1}) = set (map (\<lambda>n. n+1) [1,2,3])" by eval


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


  


  hide_const "example_network"
  hide_fact example_network_ex1 example_network_ex2 example_network_ex3 example_network_ex4 wellformed_network_example_network 

end
