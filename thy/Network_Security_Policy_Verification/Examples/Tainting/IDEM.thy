section\<open>IDEM\<close>
theory IDEM
imports "../../TopoS_Impl"
begin

ML{*
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
*}

definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [
                        ''Sensor_Controller'',
                        ''P4S_in'',
                        ''P4S_filter_A'',
                        ''P4S_filter_B'',
                        ''P4S_filter_C'',
                        ''P4S_aggregator_C'',
                        ''P4S_encrypt_A'',
                        ''P4S_encrypt_B'',
                        ''P4S_encrypt_C'',
                        ''P4S_encrypt_C_low'',
                        ''P4S_DB'',
                        ''P4S_out_A'',
                        ''P4S_out_B'',
                        ''P4S_out_C'',
                        ''P4S_out_C_low'',
                        ''A_decrypt'',
                        ''B_decrypt'',
                        ''C_decrypt'',
                        ''C_low_decrypt'',
                        ''A'',
                        ''B'',
                        ''C'',
                        ''C_low''],
              edgesL = [
              (''Sensor_Controller'', ''P4S_in''),
              (''P4S_in'',       ''P4S_filter_A''),
              (''P4S_in'',       ''P4S_filter_B''),
              (''P4S_in'',       ''P4S_filter_C''),

              (''P4S_filter_A''    , ''P4S_encrypt_A''),
              (''P4S_filter_B''    , ''P4S_encrypt_B''),
              (''P4S_filter_C''    , ''P4S_encrypt_C''),
              (''P4S_filter_C''    , ''P4S_aggregator_C''),
              (''P4S_aggregator_C'', ''P4S_encrypt_C_low''),

              (''P4S_encrypt_A''    , ''P4S_DB''),
              (''P4S_encrypt_B''    , ''P4S_DB''),
              (''P4S_encrypt_C''    , ''P4S_DB''),
              (''P4S_encrypt_C_low''    , ''P4S_DB''),

              (''P4S_DB'', ''P4S_out_A''),
              (''P4S_DB'', ''P4S_out_B''),
              (''P4S_DB'', ''P4S_out_C''),
              (''P4S_DB'', ''P4S_out_C_low''),
              (''P4S_out_A'', ''A_decrypt''),
              (''P4S_out_B'', ''B_decrypt''),
              (''P4S_out_C'', ''C_decrypt''),
              (''P4S_out_C_low'', ''C_low_decrypt''),
              (''A_decrypt'',     ''A''),
              (''B_decrypt'',     ''B''),
              (''C_decrypt'',     ''C''),
              (''C_low_decrypt'', ''C_low'')
              ] \<rparr>"

context begin
  definition "tainiting_host_attributes \<equiv> [
                           ''Sensor_Controller'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           ''P4S_in'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           ''P4S_filter_A'' \<mapsto> TaintsUntaints {''A''} {''B'',''C'',''D''},
                           ''P4S_filter_B'' \<mapsto> TaintsUntaints {''B''} {''A'',''C'',''D''},
                           ''P4S_filter_C'' \<mapsto> TaintsUntaints {''C''} {''A'',''B'',''D''},
                           ''P4S_aggregator_C'' \<mapsto> TaintsUntaints {''C_low''} {''C''},
                           ''P4S_encrypt_A'' \<mapsto> TaintsUntaints {} {''A''},
                           ''P4S_encrypt_B'' \<mapsto> TaintsUntaints {} {''B''},
                           ''P4S_encrypt_C'' \<mapsto> TaintsUntaints {} {''C''},
                           ''P4S_encrypt_C_low'' \<mapsto> TaintsUntaints {}{''C_low''},
                           ''A_decrypt'' \<mapsto> TaintsUntaints {''A''}{},
                           ''B_decrypt'' \<mapsto> TaintsUntaints {''B''}{},
                           ''C_decrypt'' \<mapsto> TaintsUntaints {''C''}{},
                           ''C_low_decrypt'' \<mapsto> TaintsUntaints {''C_low''}{},
                           ''A'' \<mapsto> TaintsUntaints {''A''}{},
                           ''B'' \<mapsto> TaintsUntaints {''B''}{},
                           ''C'' \<mapsto> TaintsUntaints {''C''}{},
                           ''C_low'' \<mapsto> TaintsUntaints {''C_low''}{}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)" by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr> ''String'' "
end
lemma "wf_list_graph policy" by eval

ML_val{*
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
*}

(*



context begin
  private definition "BLP_host_attributes \<equiv>
                          [''CryptoDB'' \<mapsto> \<lparr> privacy_level = 3, trusted = False \<rparr>
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
(*ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := edgesL policy\<rparr>)"};
*}*)
ML{*
visualize_graph_header @{context} @{term "invariants"} @{term "policy"} @{term tainiting_host_attributes};
*}


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

ML_val{*
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     ((e1,e2) \<notin> set (edgesL policy)) \<and> ((e1,e2) \<notin> set( edgesL (make_policy invariants (nodesL policy)))) \<and> (e2 = ''Adversary'') \<and> (e1 \<noteq> ''Adversary'')]"})] "";
*}


end
