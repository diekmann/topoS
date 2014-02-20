theory NetworkModel_Library
imports String 
  "../../thy_lib/FiniteListGraph_Impl"
  NM_BLPbasic_impl NM_Dependability_impl NM_Subnets_impl 
  (*NM_DomainHierarchy_impl*) NM_DomainHierarchyNG_impl
  NM_BLPtrusted_impl
  NM_SecurityGateway_impl NM_SecGwExt_impl NM_Sink_impl
  NM_NonInterference_impl
  NM_SubnetsInGW_impl
  NM_CommunicationPartners_impl
  NM_NoRefl_impl
  NM_ACLnotCommunicateWith_impl (*TODO add, has exponential offending runtime*)
  "../../thy_lib/Efficient_Distinct"
  (*"~~/src/HOL/Library/Code_Char_chr" "~~/src/HOL/Library/Efficient_Nat" *)
  "~~/src/HOL/Library/Code_Target_Nat"
begin

(*none of those should be defined or a hide_const is missing at the end of a NM_*.thy file*)
term eval_model
term target_focus
term verify_globals
term eval


(*TODO TODO TODO TODO check all before export*)

print_interps NetworkModel_modelLibrary

(*some check: *)
  thm NM_LIB_BLPbasic_interpretation.impl_spec
  thm NM_LIB_Dependability_interpretation.impl_spec
  (*thm NM_LIB_DomainHierarchy_interpretation.impl_spec*)
  thm NM_LIB_DomainHierarchyNG_interpretation.impl_spec
  thm NM_LIB_Subnets_interpretation.impl_spec
  thm NM_LIB_BLPtrusted_interpretation.impl_spec
  thm NM_LIB_SecurityGateway_interpretation.impl_spec
  thm NM_LIB_SecurityGatewayExtended_interpretation.impl_spec
  thm NM_LIB_Sink_interpretation.impl_spec
  thm NM_LIB_NonInterference_interpretation.impl_spec
  thm NM_LIB_SubnetsInGW_interpretation.impl_spec
  thm NM_LIB_CommunicationPartners_interpretation.impl_spec


(*nothing to see here, just loads all the models, ...*)




section{*Example*}
  definition BLPexample1::"bool" where
    "BLPexample1 \<equiv> (nm_eval NM_LIB_BLPbasic) fabNet \<lparr> node_properties = [NetworkModel_Vertices.V ''PresenceSensor'' \<mapsto> 2, 
                                                    NetworkModel_Vertices.V ''Webcam'' \<mapsto> 3, 
                                                    NetworkModel_Vertices.V ''SensorSink'' \<mapsto> 3,
                                                    NetworkModel_Vertices.V ''Statistics'' \<mapsto> 3], model_global_properties = () \<rparr>"
  definition BLPexample3::"(vString \<times> vString) list list" where
    "BLPexample3 \<equiv> (nm_offending_flows NM_LIB_BLPbasic) fabNet ((nm_node_props NM_LIB_BLPbasic) sensorProps_NMParams_try3)"

  value[code] "BLPexample1"
  value[code] "BLPexample3"


end
