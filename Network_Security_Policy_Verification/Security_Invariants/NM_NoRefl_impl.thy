theory NM_NoRefl_impl
imports NM_NoRefl "../TopoS_Lists_Impl_Interface"
begin

code_identifier code_module  NM_NoRefl_impl => (Scala) NM_NoRefl


section {* NetworkModel NoRefl Implementation *}

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s,r) \<in> set (edgesL G). s = r \<longrightarrow> nP s = Refl)"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition NoRefl_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "NoRefl_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 = e2 \<and> nP e1 = NoRefl] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_NoRefl.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_NoRefl.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "NoRefl_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_NoRefl.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (NetworkModel.node_props NM_NoRefl.default_node_properties P))"


interpretation NoRefl_impl:TopoS_List_Impl 
  where default_node_properties=NM_NoRefl.default_node_properties
  and sinvar_spec=NM_NoRefl.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=NM_NoRefl.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_NoRefl.target_focus
  and offending_flows_impl=NoRefl_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=NoRefl_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_NoRefl list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def NoRefl_offending_set NoRefl_offending_set_def NoRefl_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis NoRefl.node_props.simps NoRefl.node_props_eq_node_props_formaldef)
 apply(simp only: NoRefl_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_NoRefl])
 apply(simp_all add: list_graph_to_graph_def)
done


section {* SecurityGateway packing *}
  definition NM_LIB_NoRefl :: "('v::vertex, node_config, unit) TopoS_packed" where
    "NM_LIB_NoRefl \<equiv> 
    \<lparr> nm_name = ''NoRefl'', 
      nm_target_focus = NM_NoRefl.target_focus,
      nm_default = NM_NoRefl.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = NoRefl_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = NoRefl_eval
      \<rparr>"
  interpretation NM_LIB_NoRefl_interpretation: TopoS_modelLibrary NM_LIB_NoRefl
      NM_NoRefl.sinvar NM_NoRefl.verify_globals
    apply(unfold TopoS_modelLibrary_def NM_LIB_NoRefl_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text {* Examples*}

  definition example_net :: "nat list_graph" where
  "example_net \<equiv> \<lparr> nodesL = [1::nat,2,3], 
    edgesL = [(1,2),(2,2),(2,1),(1,3)] \<rparr>"
  lemma "valid_list_graph example_net" by eval
  
  definition example_conf where
  "example_conf \<equiv> ((\<lambda>e. NM_NoRefl.default_node_properties)(2:= Refl))" 
  
  lemma "sinvar example_net example_conf" by eval
  lemma "NoRefl_offending_list example_net (\<lambda>e. NM_NoRefl.default_node_properties) = [[(2, 2)]]" by eval


hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
