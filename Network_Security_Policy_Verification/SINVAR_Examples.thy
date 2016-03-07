theory SINVAR_Examples
imports
  TopoS_Interface
  TopoS_Interface_impl
  TopoS_Library
  TopoS_Composition_Theory
  TopoS_Stateful_Policy
  TopoS_Composition_Theory_impl
  TopoS_Stateful_Policy_Algorithm
  TopoS_Stateful_Policy_impl
  TopoS_Impl
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

definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars V \<equiv> generate_valid_topology sinvars \<lparr>nodesL = V, edgesL = List.product V V \<rparr>"


abbreviation "V\<equiv>TopoS_Vertices.V"



context begin
  private definition "SINK_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [V ''Bot1'' \<mapsto> Sink,
                             V ''Bot2'' \<mapsto> Sink,
                             V ''MissionControl1'' \<mapsto> SinkPool,
                             V ''MissionControl2'' \<mapsto> SinkPool
                             ]
          \<rparr>"
  value[code] "make_policy [SINK_m] [V ''INET'', V ''Supervisor'', V ''Bot1'', V ''Bot2'', V ''MissionControl1'', V ''MissionControl2'']"
  ML_val{*
  visualize_graph_header @{context} @{term "[SINK_m]"}
    @{term "make_policy [SINK_m] [V ''INET'', V ''Supervisor'', V ''Bot1'', V ''Bot2'', V ''MissionControl1'', V ''MissionControl2'']"}
    @{term "[V ''Bot1'' \<mapsto> Sink,
             V ''Bot2'' \<mapsto> Sink,
             V ''MissionControl1'' \<mapsto> SinkPool,
             V ''MissionControl2'' \<mapsto> SinkPool
             ]"};
  *}
end






context begin
  private definition "ACL_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''db1'' \<mapsto> Master [V ''h1'', V ''h2''],
                             V ''db2'' \<mapsto> Master [V ''db1''],
                             V ''h1'' \<mapsto> Care,
                             V ''h2'' \<mapsto> Care
                             ]
          \<rparr>" 
  value[code] "make_policy [ACL_m] [V ''db1'', V ''db2'', V ''h1'', V ''h2'', V ''h3'']"
  ML_val{*
  visualize_graph_header @{context} @{term "[ACL_m]"}
    @{term "make_policy [ACL_m] [V ''db1'', V ''db2'', V ''h1'', V ''h2'', V ''h3'']"}
    @{term "[V ''db1'' \<mapsto> Master [V ''h1'', V ''h2''],
             V ''db2'' \<mapsto> Master [V ''db1''],
             V ''h1'' \<mapsto> Care,
             V ''h2'' \<mapsto> Care
             ]"};
  *}
end




definition CommWith_m::"(nat SecurityInvariant)" where
    "CommWith_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1 \<mapsto> [2,3],
                  2 \<mapsto> [3]]
          \<rparr>"


text{*Experimental: the config (only one) can be added to the end.*}
ML_val{*
visualize_graph_header @{context} @{term "[CommWith_m]"}
       @{term "\<lparr> nodesL = [1::nat, 2, 3],
                edgesL = [(1,2), (2,3)]\<rparr>"} @{term "[
                  (1::nat) \<mapsto> [2::nat,3],
                  2 \<mapsto> [3]]"};
*}


value[code] "make_policy [CommWith_m] [1,2,3]"
value[code] "implc_offending_flows CommWith_m \<lparr>nodesL = [1,2,3,4], edgesL = List.product [1,2,3,4] [1,2,3,4] \<rparr>"
value[code] "make_policy [CommWith_m] [1,2,3,4]"


ML_val{*
visualize_graph @{context} @{term "[ new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr>]"} @{term "\<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr>"};
*}


lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr>) \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr> =
        [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(3, 4)]]" by eval



context begin
  private definition G_dep :: "nat list_graph" where
    "G_dep \<equiv> \<lparr>nodesL = [1::nat,2,3,4,5,6,7], edgesL = [(1,2), (2,1), (2,3),
                                                       (4,5), (5,6), (6,7)] \<rparr>"
  private lemma "wf_list_graph G_dep" by eval

  private definition "DEP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)
          \<rparr>"
  ML_val{* 
  visualize_graph_header @{context} @{term "[DEP_m]"}
    @{term "G_dep"}
    @{term "Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)"};
  *}

  text{*Connecting @{term "(3,4)"}. This causes only one offedning flow at @{term "(3,4)"}.*}
  ML_val{*
  visualize_graph_header @{context} @{term "[DEP_m]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)"};
  *}
  text{*We try to increase the dependability level at @{term 3}. Suddenly, offending flows everywhere.*}
  ML_val{*
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))
          \<rparr>]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))"};
  *}
  lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
                          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))
                          \<rparr>)
             (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) = 
           [[(3, 4)], [(1, 2), (2, 1), (5, 6)], [(1, 2), (4, 5)], [(2, 1), (4, 5)], [(2, 3), (4, 5)], [(2, 3), (5, 6)]]"
           by eval

  text{*If we recompute the dependability levels for the changed graph, we see that suddenly, 
        The level at @{term 1} and @{term 2} increased, though we only added the edge @{term "(3,4)"}.
        This hints that we connected the graph. If an attacker can now compromise @{term 1}, she 
        may be able to peek much deeper into the network.*}
  ML_val{*
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0)
          \<rparr>]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0)"};
  *}

  text{*Dependability is reflexive, a host can depend on itself.*}
  ML_val{*
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP \<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr> (\<lambda>_. 0)
          \<rparr>]"}
    @{term "\<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr>"}
    @{term "Some \<circ> dependability_fix_nP \<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr> (\<lambda>_. 0)"};
  *}
  ML_val{*
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability_norefl \<lparr> 
          node_properties = (\<lambda>_::nat. Some 0)
          \<rparr>]"}
    @{term "\<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr>"}
    @{term "(\<lambda>_::nat. Some (0::nat))"};
  *}

end



context begin
  private definition G_noninter :: "nat list_graph" where
    "G_noninter \<equiv> \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr>"
  private lemma "wf_list_graph G_noninter" by eval

  private definition "NonI_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_NonInterference \<lparr> 
          node_properties = [
                  1::nat \<mapsto> Interfering,
                  2 \<mapsto> Unrelated, 
                  3 \<mapsto> Unrelated, 
                  4 \<mapsto> Interfering]
          \<rparr>"
  ML_val{*
  visualize_graph @{context} @{term "[ NonI_m ]"} @{term "G_noninter"};
  *}

  (*The same as the CommWith example*)
  lemma "implc_offending_flows NonI_m G_noninter = [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(3, 4)]]"
           by eval


  ML_val{*
  visualize_graph @{context} @{term "[ NonI_m ]"} @{term "\<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr>"};
  *}

  lemma "implc_offending_flows NonI_m \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr> =
    [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(4, 3)]]"
           by eval

  text{*In comparison, @{const SINVAR_LIB_ACLcommunicateWith} is less strict. 
        Changing the direction of the edge @{term "(3,4)"} removes the access from @{term 1} to @{term 4}
        and the invariant holds. *}
  lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr>) \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr> = []" by eval
end



context begin
  private definition "subnets_host_attributes \<equiv> [
                             V ''v11'' \<mapsto> Subnet 1,
                             V ''v12'' \<mapsto> Subnet 1,
                             V ''v13'' \<mapsto> Subnet 1,
                             V ''v1b'' \<mapsto> BorderRouter 1,
                             V ''v21'' \<mapsto> Subnet 2,
                             V ''v22'' \<mapsto> Subnet 2,
                             V ''v23'' \<mapsto> Subnet 2,
                             V ''v2b'' \<mapsto> BorderRouter 2,
                             V ''v3b'' \<mapsto> BorderRouter 3
                             ]"
  private definition "Subnets_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Subnets \<lparr> 
          node_properties = subnets_host_attributes
          \<rparr>"
  private definition "subnet_hosts \<equiv> [V ''v11'', V ''v12'', V ''v13'', V ''v1b'',
                                      V ''v21'', V ''v22'', V ''v23'', V ''v2b'',
                                      V ''v3b'', V ''vo'']"

  private lemma "dom (subnets_host_attributes) \<subseteq> set (subnet_hosts)"
    by(simp add: subnet_hosts_def subnets_host_attributes_def)
  value[code] "make_policy [Subnets_m] subnet_hosts"
  ML_val{*
  visualize_graph_header @{context} @{term "[Subnets_m]"}
    @{term "make_policy [Subnets_m] subnet_hosts"}
    @{term "subnets_host_attributes"};
  *}


  text{*Emulating the same but with accessible members with SubnetsInGW and ACLs*}
  private definition "SubnetsInGW_ACL_ms \<equiv> [new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''v11'' \<mapsto> Member, V ''v12'' \<mapsto> Member, V ''v13'' \<mapsto> Member, V ''v1b'' \<mapsto> InboundGateway]
          \<rparr>,
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''v1b'' \<mapsto> Master [V ''v11'', V ''v12'', V ''v13'', V ''v2b'', V ''v3b''],
                             V ''v11'' \<mapsto> Care,
                             V ''v12'' \<mapsto> Care,
                             V ''v13'' \<mapsto> Care,
                             V ''v2b'' \<mapsto> Care,
                             V ''v3b'' \<mapsto> Care
                             ]
          \<rparr>,
          new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''v21'' \<mapsto> Member, V ''v22'' \<mapsto> Member, V ''v23'' \<mapsto> Member, V ''v2b'' \<mapsto> InboundGateway]
          \<rparr>,
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''v2b'' \<mapsto> Master [V ''v21'', V ''v22'', V ''v23'', V ''v1b'', V ''v3b''],
                             V ''v21'' \<mapsto> Care,
                             V ''v22'' \<mapsto> Care,
                             V ''v23'' \<mapsto> Care,
                             V ''v1b'' \<mapsto> Care,
                             V ''v3b'' \<mapsto> Care
                             ]
          \<rparr>,
          (*new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''v3b'' \<mapsto> InboundGateway]
          \<rparr>,*)
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''v3b'' \<mapsto> Master [V ''v1b'', V ''v2b''],
                             V ''v1b'' \<mapsto> Care,
                             V ''v2b'' \<mapsto> Care
                             ]
          \<rparr>]"
  value[code] "make_policy SubnetsInGW_ACL_ms subnet_hosts"
  lemma "set (edgesL (make_policy [Subnets_m] subnet_hosts)) \<subseteq> set (edgesL (make_policy SubnetsInGW_ACL_ms subnet_hosts))" by eval
  lemma "[e <- edgesL (make_policy SubnetsInGW_ACL_ms subnet_hosts). e \<notin> set (edgesL (make_policy [Subnets_m] subnet_hosts))] =
   [(V ''v1b'', V ''v11''), (V ''v1b'', V ''v12''), (V ''v1b'', V ''v13''), (V ''v2b'', V ''v21''), (V ''v2b'', V ''v22''), (V ''v2b'', V ''v23'')]" by eval
  ML_val{*
  visualize_graph @{context} @{term "SubnetsInGW_ACL_ms"}
    @{term "make_policy SubnetsInGW_ACL_ms subnet_hosts"};
  *}
end




context begin
  private definition "secgwext_host_attributes \<equiv> [
                             V ''hypervisor'' \<mapsto> SecurityGateway,
                             V ''securevm1'' \<mapsto> DomainMember,
                             V ''securevm2'' \<mapsto> DomainMember,
                             V ''publicvm1'' \<mapsto> AccessibleMember,
                             V ''publicvm2'' \<mapsto> AccessibleMember
                             ]"
  private definition "SecGwExt_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SecurityGatewayExtended \<lparr> 
          node_properties = secgwext_host_attributes
          \<rparr>"
  private definition "secgwext_hosts \<equiv> [V ''hypervisor'', V ''securevm1'', V ''securevm2'',
                                      V ''publicvm1'', V ''publicvm2'',
                                      V ''INET'']"

  private lemma "dom (secgwext_host_attributes) \<subseteq> set (secgwext_hosts)"
    by(simp add: secgwext_hosts_def secgwext_host_attributes_def)
  value[code] "make_policy [SecGwExt_m] secgwext_hosts"
  ML_val{*
  visualize_graph_header @{context} @{term "[SecGwExt_m]"}
    @{term "make_policy [SecGwExt_m] secgwext_hosts"}
    @{term "secgwext_host_attributes"};
  *}
end


end
