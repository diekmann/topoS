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
  private definition "ACL_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''db1'' \<mapsto> Master [V ''h1'', V ''h2''],
                             V ''db2'' \<mapsto> Master [V ''db1''],
                             V ''h1'' \<mapsto> Care,
                             V ''h2'' \<mapsto> Care
                             ], 
          model_global_properties = () 
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
                  2 \<mapsto> [3]], 
          model_global_properties = () 
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
                  4 \<mapsto> [1,2,3,4]],
          model_global_properties = () 
          \<rparr>]"} @{term "\<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr>"};
*}



context begin
  private definition G_dep :: "nat list_graph" where
    "G_dep \<equiv> \<lparr>nodesL = [1::nat,2,3,4,5,6,7], edgesL = [(1,2), (2,1), (2,3),
                                                       (4,5), (5,6), (6,7)] \<rparr>"
  private lemma "wf_list_graph G_dep" by eval

  private definition "DEP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0),
          model_global_properties = () 
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
          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2)),
          model_global_properties = () 
          \<rparr>]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))"};
  *}
  lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
                          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2)),
                          model_global_properties = () 
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
          node_properties = Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0),
          model_global_properties = () 
          \<rparr>]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0)"};
  *}

end


