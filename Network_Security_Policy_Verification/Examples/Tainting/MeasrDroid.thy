theory MeasrDroid
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
                        V ''Sensors_A'',
                        V ''Encryption_A'',
                        V ''Client_A_out'',

                        V ''Sensors_B'',
                        V ''Encryption_B'',
                        V ''Client_B_out'',

                        V ''Sensors_C'',
                        V ''Encryption_C'',
                        V ''Client_C_out'',

                        V ''UploadDroid'',
                        V ''C3PO_in'',
                        V ''C3PO_Dec_A'',
                        V ''C3PO_Dec_B'',
                        V ''C3PO_Dec_C'',

                        V ''C3PO_Storage'',

                        V ''Adversary''],
              edgesL = [
              (V ''Sensors_A'',    V ''Encryption_A''),
              (V ''Encryption_A'', V ''Client_A_out''),
              (V ''Client_A_out'', V ''UploadDroid''),

              (V ''Sensors_B'',    V ''Encryption_B''),
              (V ''Encryption_B'', V ''Client_B_out''),
              (V ''Client_B_out'', V ''UploadDroid''),

              (V ''Sensors_C'',    V ''Encryption_C''),
              (V ''Encryption_C'', V ''Client_C_out''),
              (V ''Client_C_out'', V ''UploadDroid''),

              (V ''UploadDroid'', V ''C3PO_in''),

              (V ''C3PO_in'', V ''C3PO_Dec_A''),
              (V ''C3PO_in'', V ''C3PO_Dec_B''),
              (V ''C3PO_in'', V ''C3PO_Dec_C''),

              (V ''C3PO_Dec_A'', V ''C3PO_Storage''),
              (V ''C3PO_Dec_B'', V ''C3PO_Storage''),
              (V ''C3PO_Dec_C'', V ''C3PO_Storage'')

              ] \<rparr>"

context begin
  private definition "tainiting_host_attributes \<equiv> [
                           V ''Sensors_A'' \<mapsto> TaintsUntaints {''A''} {},
                           V ''Sensors_B'' \<mapsto> TaintsUntaints {''B''} {},
                           V ''Sensors_C'' \<mapsto> TaintsUntaints {''C''} {},

                           V ''Encryption_A'' \<mapsto> TaintsUntaints {} {''A''} ,
                           V ''Encryption_B'' \<mapsto> TaintsUntaints {} {''B''} ,
                           V ''Encryption_C'' \<mapsto> TaintsUntaints {} {''C''} ,

                           V ''C3PO_Dec_A'' \<mapsto> TaintsUntaints {''A''} {},
                           V ''C3PO_Dec_B'' \<mapsto> TaintsUntaints {''B''} {},
                           V ''C3PO_Dec_C'' \<mapsto> TaintsUntaints {''C''} {} ,

                           V ''C3PO_Storage'' \<mapsto> TaintsUntaints {''A'',''B'',''C''} {}

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
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     ((e1,e2) \<notin> set (edgesL policy)) \<and> ((e1,e2) \<notin> set( edgesL (make_policy invariants (nodesL policy)))) \<and> (e2 = V ''Adversary'') \<and> (e1 \<noteq> V ''Adversary'')]"})] "";
*}


end
