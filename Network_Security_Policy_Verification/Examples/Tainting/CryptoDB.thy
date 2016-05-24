theory CryptoDB
imports "../../TopoS_Impl"
begin

abbreviation "V\<equiv>TopoS_Vertices.V"


ML{*
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
*}

definition policy :: "vString list_graph" where
  "policy \<equiv> \<lparr> nodesL = [
                        V ''A'', V ''A_encrypter'', V ''A_channel'',
                        V ''B'', V ''B_encrypter'', V ''B_channel'',
                        V ''C'', V ''C_encrypter'', V ''C_channel_in'', V ''C_channel_out'', V ''C_decrypter'',
                        V ''Adversary'',
                        V ''CryptoDB''],
              edgesL = [
              (V ''A'', V ''A_encrypter''), (V ''A_encrypter'', V ''A_channel''), (V ''A_channel'', V ''CryptoDB''),
              (V ''B'', V ''B_encrypter''), (V ''B_encrypter'', V ''B_channel''), (V ''B_channel'', V ''CryptoDB''),
              (V ''C'', V ''C_encrypter''), (V ''C_encrypter'', V ''C_channel_out''), (V ''C_channel_out'', V ''CryptoDB''),
              (V ''CryptoDB'', V ''C_channel_in''), (V ''C_channel_in'', V ''C_decrypter''), (V ''C_decrypter'', V ''C'')
              ] \<rparr>"

context begin
  private definition "tainiting_host_attributes \<equiv> [
                           V ''A'' \<mapsto> TaintsUntaints {''A''} {},
                           V ''A_encrypter'' \<mapsto> TaintsUntaints {} {''A''},
                           V ''A_channel'' \<mapsto> TaintsUntaints {} {},
                           V ''B'' \<mapsto> TaintsUntaints {''B''} {},
                           V ''B_encrypter'' \<mapsto> TaintsUntaints {} {''B''},
                           V ''B_channel'' \<mapsto> TaintsUntaints {} {},
                           V ''C'' \<mapsto> TaintsUntaints {''C''} {},
                           V ''C_encrypter'' \<mapsto> TaintsUntaints {} {''C''},
                           V ''C_decrypter'' \<mapsto> TaintsUntaints {''C''} {},
                           V ''C_channel_out'' \<mapsto> TaintsUntaints {} {},
                           V ''C_channel_in'' \<mapsto> TaintsUntaints {} {},
                           V ''Adversary'' \<mapsto> TaintsUntaints {} {}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)" by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr>"
end
lemma "wf_list_graph policy" by eval

ML_val{*
visualize_graph @{context} @{term "[]::vString SecurityInvariant list"} @{term "policy"};
*}


context begin
  private definition "A_host_attributes \<equiv>
                [V ''A'' \<mapsto> Member,
                 V ''A_encrypter'' \<mapsto> Member,
                 V ''A_channel'' \<mapsto> Member
                 ]"
  private lemma "dom A_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: A_host_attributes_def policy_def)
  definition "SystemA_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = A_host_attributes \<rparr>"
end

context begin
  private definition "B_host_attributes \<equiv>
                [V ''B'' \<mapsto> Member,
                 V ''B_encrypter'' \<mapsto> Member,
                 V ''B_channel'' \<mapsto> Member
                 ]"
  private lemma "dom B_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: B_host_attributes_def policy_def)
  definition "SystemB_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = B_host_attributes \<rparr>"
end



context begin
  private definition "C_host_attributes \<equiv>
                [V ''C_channel_in'' \<mapsto> InboundGateway,
                 V ''C_decrypter'' \<mapsto> Member,
                 V ''C'' \<mapsto> Member,
                 V ''C_encrypter'' \<mapsto> Member,
                 V ''C_channel_out'' \<mapsto> Member
                 ]"
  private lemma "dom C_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: C_host_attributes_def policy_def)
  definition "SystemC_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = C_host_attributes \<rparr>"
end

definition "invariants \<equiv> [Tainting_m, SystemA_m, SystemB_m, SystemC_m]"

lemma "all_security_requirements_fulfilled invariants policy" by eval
ML{*
visualize_graph @{context} @{term "invariants"} @{term "policy"};
*}


value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := edgesL policy\<rparr>)"
ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := edgesL policy\<rparr>)"};
*}


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

ML_val{*
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     ((e1,e2) \<notin> set (edgesL policy)) \<and> ((e1,e2) \<notin> set( edgesL (make_policy invariants (nodesL policy)))) \<and> (e2 = V ''Adversary'') \<and> (e1 \<noteq> V ''Adversary'')]"})] "";
*}


ML_val{*
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL policy)]"})] "";
*}


end
