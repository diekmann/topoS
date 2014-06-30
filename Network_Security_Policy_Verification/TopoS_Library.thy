theory TopoS_Library
imports String 
  "Lib/FiniteListGraph_Impl"
  "Security_Invariants/SINVAR_BLPbasic_impl"
  "Security_Invariants/SINVAR_Subnets_impl"
  "Security_Invariants/SINVAR_DomainHierarchyNG_impl"
  "Security_Invariants/SINVAR_BLPtrusted_impl"
  "Security_Invariants/SINVAR_SecGwExt_impl"
  "Security_Invariants/SINVAR_Sink_impl"
  "Security_Invariants/SINVAR_SubnetsInGW_impl"
  "Security_Invariants/SINVAR_CommunicationPartners_impl"
  "Security_Invariants/SINVAR_NoRefl_impl"
  (*invariants you probably don't wat to use because of exponential runtime*)
  "Security_Invariants/SINVAR_Dependability_impl"
  "Security_Invariants/SINVAR_NonInterference_impl"
  "Security_Invariants/SINVAR_ACLnotCommunicateWith_impl"
  "Security_Invariants/SINVAR_ACLcommunicateWith_impl"
  "Security_Invariants/SINVAR_Dependability_norefl_impl"
  "Lib/Efficient_Distinct"
  "~~/src/HOL/Library/Code_Target_Nat"
begin
(*TODO some have exponentaial runtime*)
(* possibly include: "~~/src/HOL/Library/Code_Char_chr" "~~/src/HOL/Library/Efficient_Nat" *)


section{*Summarizing the Security Invariant Library*}
  
(*none of those should be defined or a hide_const is missing at the end of a SINVAR_*.thy file*)
term sinvar
term receiver_violation
term verify_globals
term eval


(*TODO TODO TODO TODO check all before export*)

print_interps TopoS_modelLibrary

(*some check: *)
  thm SINVAR_LIB_BLPbasic_interpretation.impl_spec
  thm SINVAR_LIB_Dependability_interpretation.impl_spec
  thm SINVAR_LIB_DomainHierarchyNG_interpretation.impl_spec
  thm SINVAR_LIB_Subnets_interpretation.impl_spec
  thm SINVAR_LIB_BLPtrusted_interpretation.impl_spec
  thm SINVAR_LIB_SecurityGatewayExtended_interpretation.impl_spec
  thm SINVAR_LIB_Sink_interpretation.impl_spec
  thm SINVAR_LIB_NonInterference_interpretation.impl_spec
  thm SINVAR_LIB_SubnetsInGW_interpretation.impl_spec
  thm SINVAR_LIB_CommunicationPartners_interpretation.impl_spec
  thm SINVAR_LIB_Dependability_interpretation.impl_spec
  thm SINVAR_LIB_ACLcommunicateWith_interpretation.impl_spec


(*nothing to see here, just loads all the models, ...*)




subsection{*Example*}
  definition BLPexample1::"bool" where
    "BLPexample1 \<equiv> (nm_eval SINVAR_LIB_BLPbasic) fabNet \<lparr> node_properties = [TopoS_Vertices.V ''PresenceSensor'' \<mapsto> 2, 
                                                    TopoS_Vertices.V ''Webcam'' \<mapsto> 3, 
                                                    TopoS_Vertices.V ''SensorSink'' \<mapsto> 3,
                                                    TopoS_Vertices.V ''Statistics'' \<mapsto> 3], model_global_properties = () \<rparr>"
  definition BLPexample3::"(vString \<times> vString) list list" where
    "BLPexample3 \<equiv> (nm_offending_flows SINVAR_LIB_BLPbasic) fabNet ((nm_node_props SINVAR_LIB_BLPbasic) sensorProps_NMParams_try3)"

  value[code] "BLPexample1"
  value[code] "BLPexample3"


end
