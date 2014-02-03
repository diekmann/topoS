theory Network
imports Entity
begin

section{*A network consisting of entities*}
  text{*fwd is an entity's packet forward function: 
      A packet arriving at port with a header (src, dst) is outputted to a set of ports*}
  type_synonym 'v fwd_fun="port \<Rightarrow> ('v \<times> 'v) \<Rightarrow> port set"

  
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

      text{*transmitting a packet. A packet is ready to be send at output port out. It is send to all ports that are connected. *}
      definition link_from :: "'v interface \<Rightarrow> ('v interface) set" where
        "link_from out \<equiv> {inI. (out, inI) \<in> links N}"
    
      lemma link_from_bounded[code_unfold]: "link_from out = {inI \<in> interfaces N. (out, inI) \<in> links N}"
      proof -
        have "{inI. (out, inI) \<in> links N} = {inI \<in> snd ` links N. (out, inI) \<in> links N}" by force
        also have "{inI \<in> snd ` links N. (out, inI) \<in> links N} = {inI \<in> interfaces N. (out, inI) \<in> links N}" using snd_links by force
        finally show ?thesis using link_from_def by simp
      qed
    end

    text{*the same link_from but conveniently executable*}
    definition link_from_code :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
      "link_from_code N out \<equiv> {inI \<in> interfaces N. (out, inI) \<in> links N}"

    lemma "wellformed_network N \<Longrightarrow> wellformed_network.link_from N out = link_from_code N out"
      by(simp add: wellformed_network.link_from_bounded link_from_code_def)

  text{*Example*}
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
                  (\<lambda> p (src,dst). if e = Host src then {Port 1} else {})), (*Hosts send out their own packets and drop the rest*)
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

    value[code] "example.link_from \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>"

    lemma "link_from_code example_network \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr> = {\<lparr>entity = Host ''Bob'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval


    subsection{*A packet traverses a hop*}
      text{*A packet leaving an interface (outgoing) and traversing a link and arriving at an incoming interface. *}
      definition succ :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "succ N out_iface \<equiv> {in_iface. (out_iface, in_iface) \<in> links N}"
        
      definition succ_code :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "succ_code N out_iface \<equiv> {in_iface \<in> interfaces N. (out_iface, in_iface) \<in> links N}"
      lemma traverse_code_correct: "wellformed_network N \<Longrightarrow> succ N = succ_code N"
        apply(simp add: fun_eq_iff succ_def succ_code_def)
        apply(drule wellformed_network.snd_links)
        by force

      text{*Example*}
        lemma "succ_code example_network \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr> = {\<lparr>entity = Host ''Bob'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval

      type_synonym 'v hdr="('v \<times> 'v)" -- "packet header: (src address, dst address)"
      text{*A packet in network N with header hdr traverses hop hop. The output is the set of input interface at the nex hops*}
      definition traverse :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "traverse N hdr hop \<equiv> UNION (((forwarding N) (entity hop)) (port hop) hdr) (\<lambda>p. succ N \<lparr>entity = entity hop, port = p\<rparr>)"


      definition traverse_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
        "traverse_code N hdr hop \<equiv> UNION (((forwarding N) (entity hop)) (port hop) hdr) (\<lambda>p. succ_code N \<lparr>entity = entity hop, port = p\<rparr>)"
      lemma "wellformed_network N \<Longrightarrow> traverse N = traverse_code N"
        apply(simp add: fun_eq_iff traverse_code_def traverse_def)
        by(drule traverse_code_correct, simp)


      text{*Example*}
        text{*Example: alice sends out packet, it arrives at switch*}
        lemma "traverse_code example_network (''Alice'', ''Bob'') \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>  = {\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}" by eval
        text{*Example cont.: Switch forwards packet to Bob and Carl*}
        lemma "traverse_code example_network (''Alice'', ''Bob'')  \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr> = {\<lparr>entity = Host ''Carl'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>}" by eval
        text{*Example cont.: Carl accepts packet (or drops it, he does not forward it)*}
        lemma "traverse_code example_network (''Alice'', ''Bob'') \<lparr>entity = Host ''Bob'', port = Port 1\<rparr> = {}" by eval



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
      thm n1.link_from_def
    end

  locale added_wellformed_network = wellformed_network
  sublocale added_wellformed_network \<subseteq> added!: wellformed_network "add_iface a"
    by (fact add_wf)

  context added_wellformed_network
  begin
    thm finite_links
    thm added.finite_links
  end

  


  hide_const "example_network"

end
