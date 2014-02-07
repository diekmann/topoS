theory Network_ex
imports Network
begin

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
              (\<lambda> p (src,dst). {})), (*do not forward*)
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


subsection{*succ*}
  definition succ_code :: "'v network \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
    "succ_code N out_iface \<equiv> {in_iface \<in> interfaces N. (out_iface, in_iface) \<in> links N}"
  lemma succ_code_correct: "wellformed_network N \<Longrightarrow> succ_code N = succ N"
    apply(simp add: fun_eq_iff succ_def succ_code_def)
    apply(drule wellformed_network.snd_links)
    by force

  text{*Example*}
    lemma "succ_code example_network \<lparr> entity = NetworkBox ''threePortSwitch'', port = Port 3 \<rparr> = 
      {\<lparr>entity = Host ''Bob'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval

subsection{*traverse*}
  definition traverse_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
    "traverse_code N hdr hop \<equiv> UNION (((forwarding N) (entity hop)) (port hop) hdr) (\<lambda>p. succ_code N \<lparr>entity = entity hop, port = p\<rparr>)"
  lemma traverse_code_correct: "wellformed_network N \<Longrightarrow> traverse_code N = traverse N"
    apply(simp add: fun_eq_iff traverse_code_def traverse_def)
    by(drule succ_code_correct, simp)


  text{*Example*}
    text{*Example: alice sends out packet, it arrives at switch*}
    lemma "succ_code example_network \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr> = {\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}" by eval
    text{*Example cont.: Switch forwards packet to Bob and Carl*}
    lemma example_network_ex2: "traverse_code example_network (Host ''Alice'', Host ''Bob'')  \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr> = {\<lparr>entity = Host ''Carl'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>}" by eval
    text{*Example cont.: Carl accepts packet (or drops it, he does not forward it)*}
    lemma example_network_ex3: "traverse_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Bob'', port = Port 1\<rparr> = {}" by eval
    lemma example_network_ex4: "traverse_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Carl'', port = Port 1\<rparr> = {}" by eval

subsection{*reachable*}
  text{*Example*}
    lemma "\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr> \<in> reachable example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"
      apply(rule reachable.intros(2))
      apply(rule reachable.intros(1))
      (*apply(rule HOL.sym[of _ "entity \<lparr>entity = Host ''Alice'', port = Port (Suc 0)\<rparr>"]) (*need to select manually*)*)
      apply(simp add: example_network_def)
      apply(simp add: example_network_def succ_def)
      apply(subst traverse_code_correct[symmetric, OF wellformed_network_example_network])
      apply(subst example_network_ex2[simplified])
      by(simp)
    lemma "\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr> \<in> reachable example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"
      apply(rule reachable.intros(1))
      apply(simp add: example_network_def)
      by(simp add: example_network_def succ_def)
    lemma "x \<in> reachable example_network (Host ''Alice'', Host ''Bob'')  \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> \<Longrightarrow> 
      x \<in> {\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>,
           \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
           \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}"
      apply(induction rule: reachable.induct)
      apply(simp)
      apply(simp add: example_network_def succ_def)
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
      by(simp)


subsection{*view*}
  definition view_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
    "view_code N hdr = UNION (interfaces N) (\<lambda> src. {src} \<times> traverse_code N hdr src)"
  lemma view_code_correct: "wellformed_network N \<Longrightarrow> view_code N = view N"
    by(simp add: view_code_def view_alt fun_eq_iff traverse_code_correct)
  
  lemma traverse_code_subseteq_interfaces: "src \<in> interfaces N \<Longrightarrow> dst \<in> traverse_code N hdr src \<Longrightarrow> dst \<in> interfaces N"
    by(simp add: traverse_code_def succ_code_def)
        
  (*
    the view jumps over routers. It essentially removes the traverse function. For example, if a packet arrives at switch port 1, it can continue to Bob and Carl directly. The fact that this happens via port 3 is hidden

    Alice   1 <-------------------.
      /\                          |
       |                          |
       |                ----------------------.
       |               |          |           \/
       |      1 ------\<acute>          2 ----------> 1 Bob
       |      |  ThreePortSwitch  |       
       `------|--------- 3        |
              |                    `-------->  
               `----------------------------> 1 Carl
  *)
  value "view_code example_network (Host ''Alice'', Host ''Bob'')"
  lemma "view_code example_network (Host ''Alice'', Host ''Bob'') = {
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 3\<rparr>, \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>),
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>),
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>),
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 2\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>),
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>),
    (\<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>)}" by eval

    (*the view transforms the graph into a new graph without the traverse function! *)

  thm reachable_eq_rtrancl_view2
  definition reachable_code :: "'v network \<Rightarrow> 'v hdr \<Rightarrow> 'v interface \<Rightarrow> ('v interface) set" where
    "reachable_code N hdr start \<equiv> (\<Union> first_hop \<in> succ N start. {dst. (first_hop, dst) \<in> (view_code N hdr)\<^sup>+}) \<union> (succ_code N start)"
  lemma reachable_code_correct: "wellformed_network N \<Longrightarrow> start \<in> interfaces N \<Longrightarrow> 
    reachable_code N hdr start = reachable N hdr start"
    by(simp add: reachable_code_def succ_code_correct view_code_correct reachable_eq_rtrancl_view2)


  value[code] "(view_code example_network (Host ''Alice'', Host ''Bob''))\<^sup>+"

  lemma[code_unfold]: "{dst. (start, dst) \<in> X} = snd ` (Set.filter (\<lambda>(src,dst). src = start) X)" by force


  lemma "reachable_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> = {
    \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>,
    \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>,
    \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 1\<rparr>}" by eval

  text{*A packet emitted at switch port 3 is send directly to Bob and Carl, the switching function is not called.*}
  lemma "reachable_code example_network (NetworkBox ''threePortSwitch'', Host ''Bob'') \<lparr>entity = NetworkBox ''threePortSwitch'', port = Port 3\<rparr> = 
    {\<lparr>entity = Host ''Bob'', port = Port 1\<rparr>, \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval

  subsection{*Modelling Spoofing*}
    text{*the switch does not care about packet headers. We can send out arbitrary spoofed packets.*}
    lemma "reachable_code example_network (Host ''Alice_Spoofing'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> = reachable_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>" by eval
    lemma "reachable_code example_network (Host ''Bob'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> = reachable_code example_network (Host ''Alice'', Host ''Bob'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>" by eval
  
section{*Another example*}
  text{*forwarding by name*}
  definition "example_network2 = \<lparr> interfaces = {
                       \<lparr> entity = NetworkBox ''sw1'', port = Port 1 \<rparr>,
                       \<lparr> entity = NetworkBox ''sw1'', port = Port 2 \<rparr>,
                       \<lparr> entity = NetworkBox ''sw1'', port = Port 3 \<rparr>,
                       \<lparr> entity = NetworkBox ''sw2'', port = Port 1 \<rparr>,
                       \<lparr> entity = NetworkBox ''sw2'', port = Port 2 \<rparr>,
                       \<lparr> entity = NetworkBox ''sw2'', port = Port 3 \<rparr>,
                       \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>,
                       \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>,
                       \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>,
                       \<lparr> entity = Host ''Dan'', port = Port 1 \<rparr>},
         forwarding = (\<lambda> e. 
            if e = NetworkBox ''sw1'' then 
              (\<lambda> p (src,dst). if dst = Host ''Alice'' then {Port 1} else if dst = Host ''Bob'' then {Port 3} else if dst = Host ''Carl'' then {Port 3} else {})
            else if e = NetworkBox ''sw2'' then 
              (\<lambda> p (src,dst). if dst = Host ''Alice'' then {Port 3} else if dst = Host ''Bob'' then {Port 1}  else if dst = Host ''Carl'' then {Port 2}  else {})
            else
              (\<lambda> p (src,dst). {})), (*do not forward*)
         links = {
          (\<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''sw1'', port = Port 1 \<rparr>),
          (\<lparr> entity = NetworkBox ''sw1'', port = Port 1 \<rparr>, \<lparr> entity = Host ''Alice'', port = Port 1 \<rparr>),


          (\<lparr> entity = NetworkBox ''sw1'', port = Port 3 \<rparr>, \<lparr> entity = NetworkBox ''sw2'', port = Port 3 \<rparr>),
          (\<lparr> entity = NetworkBox ''sw2'', port = Port 3 \<rparr>, \<lparr> entity = NetworkBox ''sw1'', port = Port 3 \<rparr>),

          (\<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''sw2'', port = Port 1 \<rparr>),
          (\<lparr> entity = NetworkBox ''sw2'', port = Port 1 \<rparr>, \<lparr> entity = Host ''Bob'', port = Port 1 \<rparr>),

          (\<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>, \<lparr> entity = NetworkBox ''sw2'', port = Port 2 \<rparr>),
          (\<lparr> entity = NetworkBox ''sw2'', port = Port 2 \<rparr>, \<lparr> entity = Host ''Carl'', port = Port 1 \<rparr>)
          }\<rparr>"

  interpretation example2!: wellformed_network example_network2
  by(unfold_locales, auto simp add: example_network2_def)
  lemma "wellformed_network example_network2" by(unfold_locales)

  text{*Alice sends spoofed packet to carl*}
  value "reachable_code example_network2 (Host ''Alice_Spoofing'', Host ''Carl'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"

  text{*unknown desination is not forwarded*}
  value "reachable_code example_network2 (Host ''Alice_Spoofing'', Host ''nobody'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"

  text{*packet comes back*}
  value "reachable_code example_network2 (Host ''Carl'', Host ''Alice'') \<lparr>entity = Host ''Alice'', port = Port 1\<rparr>"

  text{*Carl to Alice*}
  value "reachable_code example_network2 (Host ''Carl'', Host ''Alice'') \<lparr>entity = Host ''Carl'', port = Port 1\<rparr>"

  section{*send_to*}
    definition send_to_code :: "'v network \<Rightarrow> 'v interface \<Rightarrow> 'v entity \<Rightarrow> 'v interface set" where
      "send_to_code N start dst \<equiv> Set.filter (\<lambda>e. case entity e of Host _ \<Rightarrow> True | _ \<Rightarrow> False) (reachable_code N (entity start, dst) start)"
  lemma send_to_code_correct: "wellformed_network N \<Longrightarrow> start \<in> interfaces N \<Longrightarrow> 
    send_to_code N start dst = send_to N start dst"
    apply(simp add: send_to_code_def send_to_def reachable_code_correct Set.filter_def)
    apply(rule Set.Collect_cong)
    apply(rule)
    apply(simp)
    apply(case_tac "entity a")
    apply(simp)
    apply(simp)
    apply(simp)
    apply(clarify)
    by auto

    text{*in network one, carl and bob are at the same port, our packet arrives at both*}
    lemma "send_to_code example_network \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> (Host ''Carl'') = {\<lparr>entity = Host ''Carl'', port = Port 1\<rparr>, \<lparr>entity = Host ''Bob'', port = Port 1\<rparr>}" by eval
    text{*network two makes sure that the packet only arrives at carl*}
    lemma "send_to_code example_network2 \<lparr>entity = Host ''Alice'', port = Port 1\<rparr> (Host ''Carl'') = {\<lparr>entity = Host ''Carl'', port = Port 1\<rparr>}" by eval


section{*cleanup namespace*}
  hide_const "example_network" "example_network2"
  hide_fact example_network_ex2 example_network_ex3 example_network_ex4 wellformed_network_example_network

end
