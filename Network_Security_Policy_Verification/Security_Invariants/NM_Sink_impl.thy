theory NM_Sink_impl
imports NM_Sink "../NetworkModel_Lists_Impl_Interface"
begin

code_identifier code_module NM_Sink_impl => (Scala) NM_Sink


section {* NetworkModel Sink (IFS) List Implementation*}

fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). e1 \<noteq> e2 \<longrightarrow> NM_Sink.allowed_sink_flow (nP e1) (nP e2))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"



definition Sink_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> NM_Sink.node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "Sink_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_sink_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_Sink.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_Sink.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Sink_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_Sink.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_Sink.default_node_properties P))"


interpretation Sink_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_Sink.default_node_properties
  and eval_model_spec=NM_Sink.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_Sink.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_Sink.target_focus
  and offending_flows_impl=Sink_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Sink_eval
 apply(unfold NetworkModel_List_Impl_def)
 apply(rule conjI)
  apply(simp add: NetworkModel_Sink list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def Sink_offending_set Sink_offending_set_def Sink_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Sink.node_props.simps Sink.node_props_eq_node_props_formaldef)
 apply(simp only: Sink_eval_def)
 apply(intro allI)
 apply(rule NetworkModel_eval_impl_proofrule[OF NetworkModel_Sink])
 apply(simp_all add: list_graph_to_graph_def)
done


section {* Sink packing *}
  definition NM_LIB_Sink :: "('v::vertex, node_config, unit) NetworkModel_packed" where
    "NM_LIB_Sink \<equiv> 
    \<lparr> nm_name = ''Sink'', 
      nm_target_focus = NM_Sink.target_focus,
      nm_default = NM_Sink.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = Sink_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Sink_eval
      \<rparr>"
  interpretation NM_LIB_Sink_interpretation: NetworkModel_modelLibrary NM_LIB_Sink
      NM_Sink.eval_model NM_Sink.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_Sink_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text {* Examples*}
  definition example_net_sink :: "nat list_graph" where
  "example_net_sink \<equiv> \<lparr> nodesL = [1::nat,2,3, 8, 11,12], 
    edgesL = [(1,8),(1,2), (2,8),(3,8),(4,8), (2,3),(3,2), (11,8),(12,8), (11,12), (1,12)] \<rparr>"
  value[code] "valid_list_graph example_net_sink"
  
  definition example_conf_sink where
  "example_conf_sink \<equiv> (\<lambda>e. NM_Sink.default_node_properties)(8:= Sink, 2:= SinkPool, 3:= SinkPool, 4:= SinkPool)" 
  
  value[code] "eval_model example_net_sink example_conf_sink"
  value[code] "Sink_offending_list example_net_sink example_conf_sink"


  definition example_net_sink_invalid where
  "example_net_sink_invalid \<equiv> example_net_sink\<lparr>edgesL := (2,1)#(8,11)#(8,2)#(edgesL example_net_sink)\<rparr>"

  value[code] "eval_model example_net_sink_invalid example_conf_sink"
  value[code] "Sink_offending_list example_net_sink_invalid example_conf_sink"


hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
