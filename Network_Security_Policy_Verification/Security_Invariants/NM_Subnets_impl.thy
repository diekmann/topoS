theory NM_Subnets_impl
imports NM_Subnets "../TopoS_Lists_Impl_Interface"
begin


code_identifier code_module NM_Subnets_impl => (Scala) NM_Subnets

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). allowed_subnet_flow (nP e1) (nP e2))"


fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition Subnets_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) list list" where
  "Subnets_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_Subnets.default_node_properties))"
lemma[code_unfold]: "NetworkModel.node_props NM_Subnets.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Subnets_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_Subnets.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (NetworkModel.node_props NM_Subnets.default_node_properties P))"


interpretation Subnets_impl:TopoS_List_Impl 
  where default_node_properties=NM_Subnets.default_node_properties
  and sinvar_spec=NM_Subnets.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=NM_Subnets.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_Subnets.target_focus
  and offending_flows_impl=Subnets_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Subnets_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_Subnets list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def Subnets_offending_set Subnets_offending_set_def Subnets_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Subnets.node_props.simps Subnets.node_props_eq_node_props_formaldef)
 apply(simp only: Subnets_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_Subnets])
 apply(simp_all add: list_graph_to_graph_def)
done


section {* Subnets packing *}
  definition NM_LIB_Subnets :: "('v::vertex, NM_Subnets.subnets, unit) TopoS_packed" where
    "NM_LIB_Subnets \<equiv> 
    \<lparr> nm_name = ''Subnets'', 
      nm_target_focus = NM_Subnets.target_focus,
      nm_default = NM_Subnets.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = Subnets_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Subnets_eval
      \<rparr>"
  interpretation NM_LIB_Subnets_interpretation: TopoS_modelLibrary NM_LIB_Subnets
      NM_Subnets.sinvar NM_Subnets.verify_globals
    apply(unfold TopoS_modelLibrary_def NM_LIB_Subnets_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {* Examples*}
  
  definition example_net_sub :: "nat list_graph" where
  "example_net_sub \<equiv> \<lparr> nodesL = [1::nat,2,3,4, 8,9, 11,12, 42], 
    edgesL = [(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1),(3,2),(3,4),(4,1),(4,2),(4,3), 
    (4,11),(1,11), 
    (8,9),(9,8),
    (8,12),
    (11,12),
    (11,42), (12,42), (3,42)] \<rparr>"
  value[code] "valid_list_graph example_net_sub"
  
  definition example_conf_sub where
  "example_conf_sub \<equiv> ((\<lambda>e. NM_Subnets.default_node_properties)
    (1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 
     11:=BorderRouter 1,
     8:=Subnet 2, 9:=Subnet 2, 
     12:=BorderRouter 2,
     42 := Unassigned))" 
  
  value[code] "sinvar example_net_sub example_conf_sub"
  
  
  definition example_net_sub_invalid where
  "example_net_sub_invalid \<equiv> example_net_sub\<lparr>edgesL := (42,4)#(3,8)#(11,8)#(edgesL example_net_sub)\<rparr>"
  
  value[code] "sinvar example_net_sub_invalid example_conf_sub"
  value[code] "Subnets_offending_list example_net_sub_invalid example_conf_sub"
  


  
  value[code] "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      (\<lambda>e. NM_Subnets.default_node_properties)"
  value[code] "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,11,12], edgesL = [(1,2),(2,3),(3,4), (4,11),(1,11), (8,9),(9,8),(8,12),  (11,12)] \<rparr>
      ((\<lambda>e. NM_Subnets.default_node_properties)(1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 11:=BorderRouter 1,
                                    8:=Subnet 2, 9:=Subnet 2, 12:=BorderRouter 2))"
  value[code] "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,11,12], edgesL = [(1,2),(2,3),(3,4), (4,11),(1,11), (8,9),(9,8),(8,12),  (11,12)] \<rparr>
      ((\<lambda>e. NM_Subnets.default_node_properties)(1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 11:=BorderRouter 1))"
  value[code] "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      ((\<lambda>e. NM_Subnets.default_node_properties)(8:=Subnet 8, 9:=Subnet 8))"
  

hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
