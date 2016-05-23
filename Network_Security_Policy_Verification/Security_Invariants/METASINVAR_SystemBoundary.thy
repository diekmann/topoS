theory METASINVAR_SystemBoundary
imports SINVAR_BLPtrusted_impl
        SINVAR_SubnetsInGW_impl
        "../TopoS_Composition_Theory_impl"
        "../TopoS_Impl" (*TODO: delete, only for visualization*)
begin


subsubsection {* Meta SecurityInvariant: System Boundaries *}


datatype system_components = SystemComponent
                           | SystemBoundaryInput
                           | SystemBoundaryOutput
                           | SystemBoundaryInputOutput


fun system_components_to_subnets :: "system_components \<Rightarrow> subnets" where
  "system_components_to_subnets SystemComponent = Member" |
  "system_components_to_subnets SystemBoundaryInput = InboundGateway" |
  "system_components_to_subnets SystemBoundaryOutput = Member" |
  "system_components_to_subnets SystemBoundaryInputOutput = InboundGateway"

fun system_components_to_blp :: "system_components \<Rightarrow> SINVAR_BLPtrusted.node_config" where
  "system_components_to_blp SystemComponent = \<lparr> privacy_level = 1, trusted = False \<rparr>" |
  "system_components_to_blp SystemBoundaryInput = \<lparr> privacy_level = 1, trusted = False \<rparr>" |
  "system_components_to_blp SystemBoundaryOutput = \<lparr> privacy_level = 0, trusted = True \<rparr>" |
  "system_components_to_blp SystemBoundaryInputOutput = \<lparr> privacy_level = 0, trusted = True \<rparr>"

definition new_meta_system_boundary :: "('v::vertex \<times> system_components) list \<Rightarrow> ('v SecurityInvariant) list" where 
  "new_meta_system_boundary C = [
      new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = map_of (map (\<lambda>(v,c). (v, system_components_to_subnets c)) C)
          \<rparr>
      ,
      new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = map_of (map (\<lambda>(v,c). (v, system_components_to_blp c)) C)
          \<rparr>
      ]"


value[code] "let nodes = [1,2,3,4,8,9,10];
           sinvars = new_meta_system_boundary
              [(1::int, SystemBoundaryInput),
               (2, SystemComponent),
               (3, SystemBoundaryOutput),
               (4, SystemBoundaryInputOutput)
               ]
       in generate_valid_topology sinvars \<lparr>nodesL = nodes, edgesL = List.product nodes nodes \<rparr>"

ML_val{*
visualize_graph @{context} @{term "new_meta_system_boundary
              [(1::int, SystemBoundaryInput),
               (2, SystemComponent),
               (3, SystemBoundaryOutput),
               (4, SystemBoundaryInputOutput)
               ]"}
      @{term "let nodes = [1,2,3,4,8,9,10];
           sinvars = new_meta_system_boundary
              [(1::int, SystemBoundaryInput),
               (2, SystemComponent),
               (3, SystemBoundaryOutput),
               (4, SystemBoundaryInputOutput)
               ]
       in generate_valid_topology sinvars \<lparr>nodesL = nodes, edgesL = List.product nodes nodes \<rparr>"};
*}

end
