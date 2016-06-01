theory MeasrDroid
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
                         ''Sensors_A'',
                         ''Encryption_A'',
                         ''Client_A_out'',
                         ''Sensors_B'',
                         ''Encryption_B'',
                         ''Client_B_out'',

                         ''Sensors_C'',
                         ''Encryption_C'',
                         ''Client_C_out'',
                         ''UploadDroid'',
                         ''C3PO_in'',
                         ''C3PO_Dec_A'',
                         ''C3PO_Dec_B'',
                         ''C3PO_Dec_C'',

                         ''C3PO_Storage'',

                         ''Adversary''],
              edgesL = [
              (''Sensors_A'',    ''Encryption_A''),
              (''Encryption_A'', ''Client_A_out''),
              (''Client_A_out'', ''UploadDroid''),

              (''Sensors_B'',    ''Encryption_B''),
              (''Encryption_B'', ''Client_B_out''),
              (''Client_B_out'', ''UploadDroid''),

              (''Sensors_C'',    ''Encryption_C''),
              (''Encryption_C'', ''Client_C_out''),
              (''Client_C_out'', ''UploadDroid''),

              (*(''UploadDroid'', ''C3PO_in''),*)
              (''C3PO_in'', ''UploadDroid''),

              (''C3PO_in'', ''C3PO_Dec_A''),
              (''C3PO_in'', ''C3PO_Dec_B''),
              (''C3PO_in'', ''C3PO_Dec_C''),

              (''C3PO_Dec_A'', ''C3PO_Storage''),
              (''C3PO_Dec_B'', ''C3PO_Storage''),
              (''C3PO_Dec_C'', ''C3PO_Storage'')

              ] \<rparr>"

context begin
  private definition "tainiting_host_attributes \<equiv> [
                           ''Sensors_A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''Sensors_B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''Sensors_C'' \<mapsto> TaintsUntaints {''C''} {},

                           ''Encryption_A'' \<mapsto> TaintsUntaints {} {''A''} ,
                           ''Encryption_B'' \<mapsto> TaintsUntaints {} {''B''} ,
                           ''Encryption_C'' \<mapsto> TaintsUntaints {} {''C''} ,

                           ''C3PO_Dec_A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''C3PO_Dec_B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''C3PO_Dec_C'' \<mapsto> TaintsUntaints {''C''} {} ,

                           ''C3PO_Storage'' \<mapsto> TaintsUntaints {''A'',''B'',''C''} {}

                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)" by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr> ''dd''"
end
lemma "wf_list_graph policy" by eval

ML_val{*
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
*}


context begin
  private definition "A_host_attributes \<equiv>
                [(''Client_A_out'' ,  SystemBoundaryOutput),
                 (''Sensors_A'' ,  SystemComponent),
                 (''Encryption_A'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of A_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: A_host_attributes_def policy_def)
  definition "SystemA_m \<equiv> new_meta_system_boundary A_host_attributes ''hh''"
end

context begin
  private definition "B_host_attributes \<equiv>
                [(''Client_B_out'' ,  SystemBoundaryOutput),
                 (''Sensors_B'' ,  SystemComponent),
                 (''Encryption_B'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of B_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: B_host_attributes_def policy_def)
  definition "SystemB_m \<equiv> new_meta_system_boundary B_host_attributes ''kk''"
end

context begin
  private definition "C_host_attributes \<equiv>
                [(''Client_C_out'' ,  SystemBoundaryOutput),
                 (''Sensors_C'' ,  SystemComponent),
                 (''Encryption_C'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of C_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: C_host_attributes_def policy_def)
  definition "SystemC_m \<equiv> new_meta_system_boundary C_host_attributes ''uu''"
end

context begin
  private definition "M_host_attributes \<equiv>
                [(''C3PO_in'' ,  SystemBoundaryOutput),
                 (''C3PO_Dec_A'' ,  SystemComponent),
                 (''C3PO_Dec_C'' ,  SystemComponent),
                 (''C3PO_Storage'' ,  SystemComponent),
                 (''C3PO_Dec_B'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of M_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: M_host_attributes_def policy_def)
  definition "SystemM_m \<equiv> new_meta_system_boundary M_host_attributes ''rr''"
end

definition "invariants \<equiv> [Tainting_m] @ SystemA_m @ SystemB_m @ SystemC_m @ SystemM_m"

lemma "all_security_requirements_fulfilled invariants policy" by eval
ML{*
visualize_graph @{context} @{term "invariants"} @{term "policy"};
*}


value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := edgesL policy\<rparr>)"
ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := (''Adversary'', ''C3PO_Storage'')#edgesL policy\<rparr>)"};
*}


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"


lemma "set (edgesL policy) \<subseteq> set (edgesL (make_policy invariants (nodesL policy)))" by eval
ML_val{*
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     ((e1,e2) \<notin> set (edgesL policy)) \<and> ((e1,e2) \<notin> set( edgesL (make_policy [Tainting_m] (nodesL policy)))) \<and> (e2 = ''Adversary'') \<and> (e1 \<noteq> ''Adversary'')]"})] "";
*}


definition "stateful_policy = generate_valid_stateful_policy_IFSACS policy invariants"
ML_val{*
visualize_edges @{context} @{term "flows_fixL stateful_policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] "";
*}

end
