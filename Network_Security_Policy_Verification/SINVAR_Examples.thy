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


definition exampleG :: "nat list_graph" where
  "exampleG \<equiv> \<lparr> nodesL = [1, 2, 3],
                edgesL = [(1,2), (2,3)]\<rparr>"

definition CommWith_m::"(nat SecurityInvariant)" where
    "CommWith_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1 \<mapsto> [2,3],
                  2 \<mapsto> [3]], 
          model_global_properties = () 
          \<rparr>"


text{*Experimental: the config (only one) can be added to the end.*}
ML_val{*
visualize_graph_header @{context} @{term "[CommWith_m]"} @{term "exampleG"} @{term "[
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