theory Tainting_Tests
imports "../TopoS_Impl"
begin


(*Instead of opening a lot of pdfs now, ask whether to open them first.
  If not clicked yes/no, it will wait 3 seconds until it continues.
  Don't change other settings!
  DoNothing must remain DoNothing for batch build.
  Changing this reference will change the behavior of all other theories! Careful with this one ;-)*)
ML{*
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
*}




definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [''A'',
                        ''B'',
                        ''C'',
                        ''CryptoDB''],
              edgesL = [(''A'', ''CryptoDB'')] \<rparr>"

lemma "wf_list_graph policy" by eval

ML_val{*
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
*}


context begin
  private definition "tainiting_host_attributes \<equiv> [''A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''C'' \<mapsto> TaintsUntaints {''C''} {},
                           ''CryptoDB'' \<mapsto> TaintsUntaints {} {''A'', ''B'', ''C''}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr> 
        node_properties = tainiting_host_attributes \<rparr> ''A tained''"
end


context begin
  private definition "BLP_host_attributes \<equiv>
                          [''CryptoDB'' \<mapsto> \<lparr> privacy_level = 3, trusted = False \<rparr>
                           ]"
  private lemma "dom (BLP_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: BLP_host_attributes_def policy_def)
  definition "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
        node_properties = BLP_host_attributes \<rparr> ''some usefull descriprion''"
end



definition "invariants \<equiv> [Tainting_m, BLP_m]"


lemma "all_security_requirements_fulfilled invariants policy" by eval
ML{*
visualize_graph @{context} @{term "invariants"} @{term "policy"};
*}



value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := (''B'', ''C'')#edgesL policy\<rparr>)"
ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := (''B'', ''C'')#edgesL policy\<rparr>)"};
*}


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

text{*
We visualize this comparison below. 
The solid edges correspond to the manually-specified policy. 
The dotted edges correspond to the flow which would be additionally permitted by the computed policy. *}
ML_val{*
visualize_edges @{context} @{term "edgesL policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL policy)]"})] "";
*}


end