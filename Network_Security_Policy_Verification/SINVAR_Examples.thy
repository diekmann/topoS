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
  

end
