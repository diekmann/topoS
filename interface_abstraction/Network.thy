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
    begin
      lemma finite_links: "finite (links N)"
      proof - 
        have "\<And> X. X \<subseteq> fst ` X \<times> snd ` X" by force
        hence "links N \<subseteq> fst ` links N \<times> snd ` links N" by blast
        from this rev_finite_subset[OF finite_interfaces fst_links] rev_finite_subset[OF finite_interfaces snd_links] show ?thesis
          by (metis finite_cartesian_product rev_finite_subset)
      qed


      text{*transmitting a packet. A packet is ready to be send at output port out. It is send to all ports that are connected. *}
      definition link_from :: "'v interface \<Rightarrow> ('v interface) set" where
        "link_from out \<equiv> {inI. (out, inI) \<in> links N}"
    
      lemma link_from_bounded[code_unfold]: "link_from out = {inI \<in> interfaces N. (out, inI) \<in> links N}"
      proof -
        have "{inI. (out, inI) \<in> links N} = {inI \<in> snd ` links N. (out, inI) \<in> links N}" by force
        also have "{inI \<in> snd ` links N. (out, inI) \<in> links N} = {inI \<in> interfaces N. (out, inI) \<in> links N}" using snd_links by force
        finally show ?thesis using link_from_def by simp
      qed

      definition "add_iface i = N\<lparr> interfaces := interfaces N \<union> {i} \<rparr>"
    
      lemma add_wf: "wellformed_network (add_iface i)"
        sorry
    end

    text{*the same link_from but conveniently executable*}
    definition link_from :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
      "link_from N out \<equiv> {inI \<in> interfaces N. (out, inI) \<in> links N}"

    lemma "wellformed_network N \<Longrightarrow> wellformed_network.link_from N out = link_from N out"
      by(simp add: wellformed_network.link_from_bounded link_from_def)


  text{*Example*}
    definition "example_network = \<lparr> interfaces = {\<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 1 \<rparr>,
                           \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 2 \<rparr>,
                           \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr>,
                           \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>,
                           \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
                           \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>},
             forwarding = (\<lambda> e. \<lambda> p (srd,dst). {}),
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
      
  
    lemma "wellformed_network example_network"
      by(unfold_locales, auto simp add: example_network_def)

    lemma "link_from example_network \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr> = {\<lparr>entity = Host ''Bob'', port = Port (Suc 0)\<rparr>, \<lparr>entity = Host ''Carl'', port = Port (Suc 0)\<rparr>}" by eval

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
