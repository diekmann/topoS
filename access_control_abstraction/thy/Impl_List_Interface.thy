theory Impl_List_Interface
imports NetworkModel_Library Impl_List_Composition
    ML_GraphViz
    Impl_List_StatefulPolicy
begin


section{*Util*}

  fun rembiflowdups :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
    "rembiflowdups [] = []" |
    "rembiflowdups ((s,r)#as) = (if (s,r) \<in> set as \<or> (r,s) \<in> set as then rembiflowdups as else (s,r)#rembiflowdups as)"


  lemma rembiflowdups_complete: "\<lbrakk> \<forall>(s,r) \<in> set x. (r,s) \<in> set x \<rbrakk> \<Longrightarrow> set (rembiflowdups x) \<union> set (backlinks (rembiflowdups x)) = set x"
    proof
      assume a: "\<forall>(s,r) \<in> set x. (r,s) \<in> set x"
      have subset1: "set (rembiflowdups x) \<subseteq> set x"
        apply(induction x)
        apply(simp)
        apply(clarsimp)
        apply(simp split: split_if_asm)
        by(blast)+
      have set_backlinks_simp: "\<And> x. \<forall>(s,r) \<in> set x. (r,s) \<in> set x \<Longrightarrow> set (backlinks x) = set x"
        apply(simp add: backlinks_set)
        apply(rule)
        by fast+
      have subset2: "set (backlinks (rembiflowdups x)) \<subseteq> set x"
        apply(subst set_backlinks_simp[OF a, symmetric])
        by(simp add: backlinks_subset subset1)

      from subset1 subset2 
      show "set (rembiflowdups x) \<union> set (backlinks (rembiflowdups x)) \<subseteq> set x" by blast
    next
      show "set x \<subseteq> set (rembiflowdups x) \<union> set (backlinks (rembiflowdups x))"
        apply(rule)
        apply(induction x)
        apply(simp)
        apply(rename_tac a as e)
        apply(simp)
        apply(erule disjE)
        apply(simp)
        defer
        apply fastforce
        apply(case_tac a)
        apply(rename_tac s r)
        apply(case_tac "(s,r) \<notin> set as \<and> (r,s) \<notin> set as")
        apply(simp)
        apply(simp add: backlinks_set)
        by blast
      qed


  text{*only for prettyprinting*}
  definition filter_for_biflows:: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
    "filter_for_biflows E \<equiv> [e \<leftarrow> E. (snd e, fst e) \<in> set E]"

  definition filter_for_uniflows:: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
    "filter_for_uniflows E \<equiv> [e \<leftarrow> E. (snd e, fst e) \<notin> set E]"

  lemma filter_for_biflows_correct: "\<forall>(s,r) \<in> set (filter_for_biflows E). (r,s) \<in> set (filter_for_biflows E)"
    unfolding filter_for_biflows_def
    by(induction E, auto)

  lemma filter_for_biflows_un_filter_for_uniflows: "set (filter_for_biflows E) \<union> set (filter_for_uniflows E) = set E"
    apply(simp add: filter_for_biflows_def filter_for_uniflows_def) by blast


  definition partition_by_biflows :: "('a \<times> 'a) list \<Rightarrow> (('a \<times> 'a) list \<times> ('a \<times> 'a) list)" where
    "partition_by_biflows E \<equiv> (rembiflowdups (filter_for_biflows E), remdups (filter_for_uniflows E))"

  lemma partition_by_biflows_correct: "case partition_by_biflows E of (biflows, uniflows) \<Rightarrow> set biflows \<union> set (backlinks (biflows)) \<union> set uniflows = set E"
    apply(simp add: partition_by_biflows_def)
    by(simp add: filter_for_biflows_un_filter_for_uniflows filter_for_biflows_correct rembiflowdups_complete)


  lemma "partition_by_biflows [(1::int, 1::int), (1,2), (2, 1), (1,3)] = ([(1, 1), (2, 1)], [(1, 3)])" by eval


section {* ML Interface *}

ML{*
(*apply args to f. f ist best supplied using @{const_name "name_of_function"} *)
fun apply_function (ctx: Proof.context) (thy: theory) (f: string) (args: term list) : term = 
  let
    val _ = writeln ("applying "^f^" to ");
    val _ = List.map (fn t => Pretty.writeln (Syntax.pretty_term (Config.put show_types true ctx) t)) args;
    (*val t_eval = Code_Evaluation.dynamic_value_strict thy t;*)
    (* $ associates to the left, give f its arguments*)
    val applied_untyped_uneval : term = List.foldl (fn (t, a) => a $ t) (Const (f, dummyT)) args;
    val applied_uneval: term = Syntax.check_term ctx applied_untyped_uneval;
  in
    applied_uneval |>  Code_Evaluation.dynamic_value_strict thy
  end;


(*ctx -> thy -> edges -> (biflows, uniflows)*)
fun partition_by_biflows (ctx: Proof.context) (thy: theory) (t: term) : (term * term) = 
  apply_function ctx thy @{const_name "partition_by_biflows"} [t] |> HOLogic.dest_prod


local
  fun get_tune_node_format (edges: term) : term -> string -> string =
    if (fastype_of edges) = @{typ "(NetworkModel_Vertices.vString \<times> NetworkModel_Vertices.vString) list"}
    then
      tune_Vstring_format
    else
      Graphviz.default_tune_node_format
in
  fun visualize_edges (ctx: Proof.context) (thy: theory) (edges: term) (coloredges: (string * term) list): int = 
    let
      val _ = writeln("visualize_edges");
      val (biflows, uniflows) = partition_by_biflows ctx thy edges;
    in
      Graphviz.visualize_graph_pretty thy (get_tune_node_format edges) ([
      ("", uniflows),
      ("edge [dir=\"none\", color=\"#000000\"]", biflows)] @ coloredges) (*dir=none, dir=both*)
    end
end
*}

ML_val{*
local
  val (biflows, uniflows) = partition_by_biflows @{context} @{theory} @{term "[(1::int, 1::int), (1,2), (2, 1), (1,3)]"};
in
  val _ = Pretty.writeln (Syntax.pretty_term (Config.put show_types true @{context}) biflows);
  val _ = Pretty.writeln (Syntax.pretty_term (Config.put show_types true @{context}) uniflows);
end;

val t = fastype_of @{term "[(NetworkModel_Vertices.V ''x'', 2::nat)]"}

(*
visualize_edges @{context} @{theory} @{term "[(1::int, 1::int), (1,2), (2, 1), (1,3)]"} []; *)
*}


ML {*
(*M: security requirements, list
  G: list_graph*)
fun vizualize_graph (ctx: Proof.context) (thy: theory) (M: term) (G: term): unit = 
  let
    val all_fulfilled = apply_function ctx thy @{const_name "all_security_requirements_fulfilled"} [M, G];
    val edges = apply_function ctx thy @{const_name "edgesL"} [G];
  in
    if all_fulfilled = @{term "False"} then
      (let
        val offending = apply_function ctx thy @{const_name "implc_get_offending_flows"} [M, G];
        val offending_flat = apply_function ctx thy @{const_name "List.remdups"} [apply_function ctx thy @{const_name "List.concat"} [offending]];
      in
       writeln("offending flows:");
       Pretty.writeln (Syntax.pretty_term ctx offending);
       visualize_edges ctx thy edges [("edge [dir=\"arrow\", style=dashed, color=\"#FF0000\", constraint=false]", offending_flat)]; 
      () end)
    else if all_fulfilled <> @{term "True"} then raise ERROR "all_fulfilled neither False nor True" else (
       writeln("check TRUE");
       writeln("All valid:");
       visualize_edges ctx thy edges []; 
      ())
  end;
*}

end
