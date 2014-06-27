theory NM_BLPbasic_impl
imports NM_BLPbasic "../NetworkModel_Lists_Impl_Interface"
begin

code_identifier code_module NM_BLPbasic_impl => (Scala) NM_BLPbasic

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (nP e1) \<le> (nP e2))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition BLP_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "BLP_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_BLPbasic.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_BLPbasic.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "BLP_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_BLPbasic.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_BLPbasic.default_node_properties P))"


interpretation BLPbasic_impl:NetworkModel_List_Impl
  where default_node_properties=NM_BLPbasic.default_node_properties
  and eval_model_spec=NM_BLPbasic.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_BLPbasic.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_BLPbasic.target_focus
  and offending_flows_impl=BLP_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=BLP_eval
  apply(unfold NetworkModel_List_Impl_def)
  apply(rule conjI)
   apply(simp add: NetworkModel_BLPBasic)
   apply(simp add: list_graph_to_graph_def)
  apply(rule conjI)
   apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def BLP_offending_set BLP_offending_set_def BLP_offending_list_def)
  apply(rule conjI)
   apply(simp only: NetModel_node_props_def)
   apply(metis BLPbasic.node_props.simps BLPbasic.node_props_eq_node_props_formaldef)
  apply(simp only: BLP_eval_def)
  apply(simp add: NetworkModel_eval_impl_proofrule[OF NetworkModel_BLPBasic])
  apply(simp add: list_graph_to_graph_def)
 done



section {* BLPbasic packing *}
  definition NM_LIB_BLPbasic :: "('v::vertex, privacy_level, unit) NetworkModel_packed" where
    "NM_LIB_BLPbasic \<equiv> 
    \<lparr> nm_name = ''BLPbasic'', 
      nm_target_focus = NM_BLPbasic.target_focus,
      nm_default = NM_BLPbasic.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = BLP_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = BLP_eval
      \<rparr>"
  interpretation NM_LIB_BLPbasic_interpretation: NetworkModel_modelLibrary NM_LIB_BLPbasic 
      NM_BLPbasic.eval_model NM_BLPbasic.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_BLPbasic_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

section{* Example *}
  definition fabNet :: "vString list_graph" where
  "fabNet \<equiv> \<lparr> nodesL = [NetworkModel_Vertices.V ''Statistics'', NetworkModel_Vertices.V ''SensorSink'', NetworkModel_Vertices.V ''PresenceSensor'', NetworkModel_Vertices.V ''Webcam'', NetworkModel_Vertices.V ''TempSensor'', NetworkModel_Vertices.V ''FireSesnsor'',
                     NetworkModel_Vertices.V ''MissionControl1'', NetworkModel_Vertices.V ''MissionControl2'', NetworkModel_Vertices.V ''Watchdog'', NetworkModel_Vertices.V ''Bot1'', NetworkModel_Vertices.V ''Bot2''], 
              edgesL =[(NetworkModel_Vertices.V ''PresenceSensor'', NetworkModel_Vertices.V ''SensorSink''), (NetworkModel_Vertices.V ''Webcam'', NetworkModel_Vertices.V ''SensorSink''), 
                     (NetworkModel_Vertices.V ''TempSensor'', NetworkModel_Vertices.V ''SensorSink''),  (NetworkModel_Vertices.V ''FireSesnsor'', NetworkModel_Vertices.V ''SensorSink''),
                     (NetworkModel_Vertices.V ''SensorSink'', NetworkModel_Vertices.V ''Statistics''),
                     (NetworkModel_Vertices.V ''MissionControl1'', NetworkModel_Vertices.V ''Bot1''), (NetworkModel_Vertices.V ''MissionControl1'', NetworkModel_Vertices.V ''Bot2''),
                     (NetworkModel_Vertices.V ''MissionControl2'', NetworkModel_Vertices.V ''Bot2''),
                     (NetworkModel_Vertices.V ''Watchdog'', NetworkModel_Vertices.V ''Bot1''), (NetworkModel_Vertices.V ''Watchdog'', NetworkModel_Vertices.V ''Bot2'')] \<rparr>"
  value[code] "valid_list_graph fabNet"


  definition sensorProps_try1 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try1 \<equiv> (\<lambda> n. NM_BLPbasic.default_node_properties)(NetworkModel_Vertices.V ''PresenceSensor'' := 2, NetworkModel_Vertices.V ''Webcam'' := 3)"
  value[code] "BLP_offending_list fabNet sensorProps_try1"
  value[code] "eval_model fabNet sensorProps_try1"

  definition sensorProps_try2 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try2 \<equiv> (\<lambda> n. NM_BLPbasic.default_node_properties)(NetworkModel_Vertices.V ''PresenceSensor'' := 2, NetworkModel_Vertices.V ''Webcam'' := 3, 
                                                       NetworkModel_Vertices.V ''SensorSink'' := 3)"
  value[code] "BLP_offending_list fabNet sensorProps_try2"
  value[code] "eval_model fabNet sensorProps_try2"

  definition sensorProps_try3 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try3 \<equiv> (\<lambda> n. NM_BLPbasic.default_node_properties)(NetworkModel_Vertices.V ''PresenceSensor'' := 2, NetworkModel_Vertices.V ''Webcam'' := 3, 
                                                       NetworkModel_Vertices.V ''SensorSink'' := 3, NetworkModel_Vertices.V ''Statistics'' := 3)"
  value[code] "BLP_offending_list fabNet sensorProps_try3"
  value[code] "eval_model fabNet sensorProps_try3"

  text {* Another parameter set for confidential controlling information*}
  definition sensorProps_conf :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_conf \<equiv> (\<lambda> n. NM_BLPbasic.default_node_properties)(NetworkModel_Vertices.V ''MissionControl1'' := 1, NetworkModel_Vertices.V ''MissionControl2'' := 2,
      NetworkModel_Vertices.V ''Bot1'' := 1, NetworkModel_Vertices.V ''Bot2'' := 2 )"
  value[code] "BLP_offending_list fabNet sensorProps_conf"
  value[code] "eval_model fabNet sensorProps_conf"


text {* Complete example:*}
  
  definition sensorProps_NMParams_try3 :: "(vString, nat, unit) NetworkModel_Params" where
  "sensorProps_NMParams_try3 \<equiv> \<lparr> node_properties = [NetworkModel_Vertices.V ''PresenceSensor'' \<mapsto> 2, 
                                                    NetworkModel_Vertices.V ''Webcam'' \<mapsto> 3, 
                                                    NetworkModel_Vertices.V ''SensorSink'' \<mapsto> 3,
                                                    NetworkModel_Vertices.V ''Statistics'' \<mapsto> 3],
                                model_global_properties = () \<rparr>"
  value[code] "BLP_eval fabNet sensorProps_NMParams_try3"


export_code NM_LIB_BLPbasic in Scala

hide_const (open) NetModel_node_props BLP_offending_list BLP_eval

hide_const (open) eval_model verify_globals

end
