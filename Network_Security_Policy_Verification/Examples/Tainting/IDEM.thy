theory IDEM
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
                        V ''Sensor_Controller'',
                        V ''P4S_in'',
                        V ''P4S_filter_A'',
                        V ''P4S_filter_B'',
                        V ''P4S_filter_C'',
                        V ''P4S_aggregator_C'',
                        V ''P4S_encrypt_A'',
                        V ''P4S_encrypt_B'',
                        V ''P4S_encrypt_C'',
                        V ''P4S_encrypt_C_low'',
                        V ''P4S_DB'',
                        V ''P4S_out_A'',
                        V ''P4S_out_B'',
                        V ''P4S_out_C'',
                        V ''P4S_out_C_low'',
                        V ''A_decrypt'',
                        V ''B_decrypt'',
                        V ''C_decrypt'',
                        V ''C_low_decrypt'',
                        V ''A'',
                        V ''B'',
                        V ''C'',
                        V ''C_low'',
                        V ''Adversary''],
              edgesL = [
              (V ''Sensor_Controller'', V ''P4S_in''),
              (V ''P4S_in'',       V ''P4S_filter_A''),
              (V ''P4S_in'',       V ''P4S_filter_B''),
              (V ''P4S_in'',       V ''P4S_filter_C''),

              (V ''P4S_filter_A''    , V ''P4S_encrypt_A''),
              (V ''P4S_filter_B''    , V ''P4S_encrypt_B''),
              (V ''P4S_filter_C''    , V ''P4S_encrypt_C''),
              (V ''P4S_filter_C''    , V ''P4S_aggregator_C''),
              (V ''P4S_aggregator_C'', V ''P4S_encrypt_C_low''),

              (V ''P4S_encrypt_A''    , V ''P4S_DB''),
              (V ''P4S_encrypt_B''    , V ''P4S_DB''),
              (V ''P4S_encrypt_C''    , V ''P4S_DB''),
              (V ''P4S_encrypt_C_low''    , V ''P4S_DB''),

              (V ''P4S_DB'', V ''P4S_out_A''),
              (V ''P4S_DB'', V ''P4S_out_B''),
              (V ''P4S_DB'', V ''P4S_out_C''),
              (V ''P4S_DB'', V ''P4S_out_C_low''),
              (V ''P4S_out_A'', V ''A_decrypt''),
              (V ''P4S_out_B'', V ''B_decrypt''),
              (V ''P4S_out_C'', V ''C_decrypt''),
              (V ''P4S_out_C_low'', V ''C_low_decrypt''),
              (V ''A_decrypt'',     V ''A''),
              (V ''B_decrypt'',     V ''B''),
              (V ''C_decrypt'',     V ''C''),
              (V ''C_low_decrypt'', V ''C_low''),
              (V ''P4S_DB'', V ''Adversary''),
              (V ''Adversary'', V ''P4S_DB'')
              ] \<rparr>"

context begin
  private definition "tainiting_host_attributes \<equiv> [
                           V ''Sensor_Controller'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           V ''P4S_in'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           V ''P4S_filter_A'' \<mapsto> TaintsUntaints {''A''} {''A'',''B'',''C'',''D''},
                           V ''P4S_filter_B'' \<mapsto> TaintsUntaints {''B''} {''A'',''B'',''C'',''D''},
                           V ''P4S_filter_C'' \<mapsto> TaintsUntaints {''C''} {''A'',''B'',''C'',''D''},
                           V ''P4S_aggregator_C'' \<mapsto> TaintsUntaints {''C_low''} {''C''},
                           V ''P4S_encrypt_A'' \<mapsto> TaintsUntaints {} {''A''},
                           V ''P4S_encrypt_B'' \<mapsto> TaintsUntaints {} {''B''},
                           V ''P4S_encrypt_C'' \<mapsto> TaintsUntaints {} {''C''},
                           V ''P4S_encrypt_C_low'' \<mapsto> TaintsUntaints {}{''C_low''},
                           V ''A_decrypt'' \<mapsto> TaintsUntaints {''A''}{},
                           V ''B_decrypt'' \<mapsto> TaintsUntaints {''B''}{},
                           V ''C_decrypt'' \<mapsto> TaintsUntaints {''C''}{},
                           V ''C_low_decrypt'' \<mapsto> TaintsUntaints {''C_low''}{},
                           V ''A'' \<mapsto> TaintsUntaints {''A''}{},
                           V ''B'' \<mapsto> TaintsUntaints {''B''}{},
                           V ''C'' \<mapsto> TaintsUntaints {''C''}{},
                           V ''C_low'' \<mapsto> TaintsUntaints {''C_low''}{}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)" by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr>"
end
lemma "wf_list_graph policy" by eval

ML_val{*
visualize_graph @{context} @{term "[]::vString SecurityInvariant list"} @{term "policy"};
*}

(*



context begin
  private definition "BLP_host_attributes \<equiv>
                          [V ''CryptoDB'' \<mapsto> \<lparr> privacy_level = 3, trusted = False \<rparr>
                           ]"
  private lemma "dom (BLP_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: BLP_host_attributes_def policy_def)
  definition "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr>
        node_properties = BLP_host_attributes \<rparr>"
end
*)

definition "invariants \<equiv> [Tainting_m]"

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
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL policy)]"})] "";
*}


end
