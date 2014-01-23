theory NM_DomainHierarchy_impl
imports NM_DomainHierarchy NetworkModel_Lists_Impl_Interface FiniteListGraph_Impl
begin


code_identifier code_module NM_DomainHierarchy_impl => (Scala) NM_DomainHierarchy


fun eval_model :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> bool" where
  "eval_model G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (nP e2) \<le> (nP e1)) "

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> set (nodesL G). valid_hierarchy_pos tree (nP v))"



definition DomainHierarchy_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainName) \<Rightarrow> ('v \<times> 'v) list list" where
  "DomainHierarchy_offending_list G nP = (if eval_model G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> (nP e2) \<le> (nP e1)] ])"



lemma "DomainHierarchy.node_props P = 
  (\<lambda>i. case node_properties P i of None \<Rightarrow> NM_DomainHierarchy.default_node_properties | Some property \<Rightarrow> property)"
by(fact NetworkModel.node_props.simps[OF DomainHierarchy_NetworkModel, of "P"])

definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> NM_DomainHierarchy.default_node_properties))"
(*lemma[code_unfold]: "NetworkModel.node_props NM_DomainHierarchy.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done*)

(*TODO does this work?*)
lemma[code_unfold]: "DomainHierarchy.node_props P = NetModel_node_props P"
by(simp add: NetModel_node_props_def)

definition "DomainHierarchy_eval G P = (valid_list_graph G \<and> 
  verify_globals G (NetworkModel.node_props NM_DomainHierarchy.default_node_properties P) (model_global_properties P) \<and> 
  eval_model G (NetworkModel.node_props NM_DomainHierarchy.default_node_properties P))"


interpretation DomainHierarchy_impl:NetworkModel_List_Impl 
  where default_node_properties=NM_DomainHierarchy.default_node_properties
  and eval_model_spec=NM_DomainHierarchy.eval_model
  and eval_model_impl=eval_model
  and verify_globals_spec=NM_DomainHierarchy.verify_globals
  and verify_globals_impl=verify_globals
  and target_focus=NM_DomainHierarchy.target_focus
  and offending_flows_impl=DomainHierarchy_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=DomainHierarchy_eval
apply(unfold_locales)
     apply(simp add: list_graph_to_graph_def)
    apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def DomainHierarchy_offending_set DomainHierarchy_offending_set_def DomainHierarchy_offending_list_def)
  apply(simp only: NetModel_node_props_def)
 apply(metis DomainHierarchy.node_props.simps DomainHierarchy.node_props_eq_node_props_formaldef)
apply(simp only: DomainHierarchy_eval_def)
apply(rule_tac target_focus=NM_DomainHierarchy.target_focus in NetworkModel_eval_impl_proofrule)
   apply(unfold_locales) (*instance *)
apply(simp_all add: list_graph_to_graph_def)
done



section {* BLPtrusted packingc *}
  definition NM_LIB_DomainHierarchy :: "('v::vertex, domainName, domainTree) NetworkModel_packed" where
    "NM_LIB_DomainHierarchy \<equiv> 
    \<lparr> nm_name = ''DomainHierarchy'', 
      nm_target_focus = NM_DomainHierarchy.target_focus,
      nm_default = NM_DomainHierarchy.default_node_properties, 
      nm_eval_model = eval_model,
      nm_verify_globals = verify_globals,
      nm_offending_flows = DomainHierarchy_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = DomainHierarchy_eval
      \<rparr>"
  interpretation NM_LIB_DomainHierarchy_interpretation: NetworkModel_modelLibrary NM_LIB_DomainHierarchy 
      NM_DomainHierarchy.eval_model NM_DomainHierarchy.verify_globals
    apply(unfold NetworkModel_modelLibrary_def NM_LIB_DomainHierarchy_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {*Examples:*}
definition example_TUM_net :: "vString list_graph" where
  "example_TUM_net = \<lparr> nodesL=[NetworkModel_Vertices.V ''Wolfgang'', NetworkModel_Vertices.V ''Holger'', NetworkModel_Vertices.V ''Heiko'', NetworkModel_Vertices.V ''CoffeeMachine'', NetworkModel_Vertices.V ''TeaMachine'', NetworkModel_Vertices.V ''Jonas''], 
        edgesL=[(NetworkModel_Vertices.V ''Wolfgang'',NetworkModel_Vertices.V ''Holger''), (NetworkModel_Vertices.V ''Wolfgang'',NetworkModel_Vertices.V ''Heiko''), (NetworkModel_Vertices.V ''Wolfgang'',NetworkModel_Vertices.V ''CoffeeMachine''), 
        (NetworkModel_Vertices.V ''Holger'', NetworkModel_Vertices.V ''Heiko''), (NetworkModel_Vertices.V ''Holger'', NetworkModel_Vertices.V ''CoffeeMachine''), (NetworkModel_Vertices.V ''Holger'', NetworkModel_Vertices.V ''TeaMachine''), 
        (NetworkModel_Vertices.V ''Heiko'', NetworkModel_Vertices.V ''Holger''), (NetworkModel_Vertices.V ''Heiko'', NetworkModel_Vertices.V ''CoffeeMachine''), (NetworkModel_Vertices.V ''Heiko'', NetworkModel_Vertices.V ''TeaMachine'')
        ] \<rparr>"

value[code] "valid_list_graph example_TUM_net"

definition example_TUM_config :: "vString \<Rightarrow> domainName" where
  "example_TUM_config = ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (NetworkModel_Vertices.V ''Wolfgang'':= ''TUM''--Leaf, 
         NetworkModel_Vertices.V ''Holger'':= ''TUM''--''i8''--Leaf, 
         NetworkModel_Vertices.V ''Heiko'':= ''TUM''--''i8''--Leaf, 
         NetworkModel_Vertices.V ''CoffeeMachine'':= ''TUM''--''i8''--''CoffeeMachine''--Leaf,
         NetworkModel_Vertices.V ''TeaMachine'':= ''TUM''--''i8''--''TeaMachine''--Leaf,
         NetworkModel_Vertices.V ''Jonas'':= ''TUM''--''i20''--Leaf
       ))"

definition example_TUM_hierarchy :: "domainTree" where
"example_TUM_hierarchy = (Department ''TUM'' [
           Department ''i8'' [
            Department ''CoffeeMachine'' [],
            Department ''TeaMachine'' []
           ], 
           Department ''i20'' []
        ])"

value[code] "verify_globals example_TUM_net example_TUM_config example_TUM_hierarchy"
value[code] "eval_model     example_TUM_net example_TUM_config"
value[code] "DomainHierarchy_eval example_TUM_net 
    \<lparr>node_properties = [NetworkModel_Vertices.V ''Wolfgang'' \<mapsto> ''TUM''--''i8''--Leaf], model_global_properties = example_TUM_hierarchy\<rparr>"

definition example_TUM_net_invalid where
"example_TUM_net_invalid = example_TUM_net\<lparr>edgesL :=  
    (NetworkModel_Vertices.V ''Jonas'', NetworkModel_Vertices.V ''CoffeeMachine'')#(NetworkModel_Vertices.V ''CoffeeMachine'', NetworkModel_Vertices.V ''Heiko'')#(NetworkModel_Vertices.V ''CoffeeMachine'', NetworkModel_Vertices.V ''TeaMachine'')#
    (edgesL example_TUM_net)\<rparr>"

value[code] "verify_globals example_TUM_net_invalid example_TUM_config example_TUM_hierarchy"
value[code] "eval_model     example_TUM_net_invalid example_TUM_config"
value[code] "DomainHierarchy_offending_list example_TUM_net_invalid example_TUM_config"



value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4, 5,6,7,8], edgesL=[(1,2), (1,4), (2,4), (3,4), (2,3), (3,2), (5,5), (8,7), (5,7)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
      "

text{* The coffee pot can not command higher instances. *}
value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4,5,6,7,8], edgesL=[(4,1)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
        "
value[code] "DomainHierarchy_offending_list \<lparr> nodesL=[1::nat,2,3,4,5,6,7,8], edgesL=[(4,1)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
     "


text {* Non i8 Members cannot touch CoffeePot*}
value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4,5,6,7,8], edgesL=[(8,1)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
      "
value[code] "DomainHierarchy_offending_list \<lparr> nodesL=[1::nat,2,3,4,5,6,7,8], edgesL=[(8,1)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
      "

value[code] "eval_model
      \<lparr> nodesL=[1::nat,2], edgesL=[(1,2)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= Leaf, 
         2:= ''TUM''--Leaf)) 
        "




text{*Everybody commands its subjects. *}
text{*Even a (5,5) connection renders this model invalid as for the @{text "(nP e1) \<noteq> Unassigned"} requirement*}
value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4,5], edgesL=[(1,2), (1,4), (2,4), (3,4), (2,3), (3,2)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
      "

text{* The coffee pot can not command higher instances. *}
value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4], edgesL=[(4,1)] \<rparr> 
      ((\<lambda> e. NM_DomainHierarchy.default_node_properties)
        (1:= ''TUM''--Leaf, 
         2:= ''TUM''--''i8''--Leaf, 
         3:= ''TUM''--''i8''--Leaf, 
         4:= ''TUM''--''i8''--''CoffeeMachine''--Leaf))
      "


text {* partial order:*}
value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4], edgesL=[(1,2), (2,1)] \<rparr> 
      ((\<lambda> e. Unassigned)(1:= ''TUM''--Leaf, 2:= ''LMU''--Leaf)) "
value[code] "DomainHierarchy_offending_list \<lparr> nodesL=[1::nat,2,3,4], edgesL=[(1,2), (2,1)] \<rparr>"


value[code] "eval_model
      \<lparr> nodesL=[1::nat,2,3,4], edgesL=[(1,2), (2,1)] \<rparr> 
      ((\<lambda> e. Unassigned)(1:= ''TUM''--Leaf))"





hide_const (open) NetModel_node_props
hide_const (open) eval_model verify_globals

end
