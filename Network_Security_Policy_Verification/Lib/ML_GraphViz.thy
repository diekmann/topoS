theory ML_GraphViz
imports Main
begin

ML {*
signature GRAPHVIZ =
sig
  val open_viewer: bool Unsynchronized.ref

  val default_tune_node_format: term -> string -> string

  (* edges is a term of type ('a \<times> 'a) list *)
  
  (* @{theory} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph: theory -> (term -> string -> string) -> term -> int

  (* @{theory} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph_pretty: theory -> (term -> string -> string) -> (string * term) list-> int

  (*val visualize_graph_thm: (term -> string -> string) -> thm -> int*)
end;
*}



ML {*
structure Graphviz: GRAPHVIZ =
struct

val open_viewer = Unsynchronized.ref true

val default_tune_node_format = (fn _ => I);


fun write_to_tmpfile (t: string): Path.T = 
     let 
      val p = Isabelle_System.create_tmp_path "graphviz" "graph_tmp.dot";
      val p_str = (File.platform_path p);
     in
      writeln ("using tmpfile " ^ p_str);
      File.write p (t^"\n");
      p
     end;


exception ExceptionGraphVizNotFound;
exception ExceptionViewerNotFound;

local
  (* viz is graphiz command, e.g. dot
     viewer is a PDF viewer, e.g. xdg-open
     retuns return code of bash command *)
  fun paintGraph (viewer: string) (viz: string) (f: Path.T): int =
    if (Isabelle_System.bash ("which "^viz)) <> 0 then
      raise ExceptionGraphVizNotFound
    else if (Isabelle_System.bash ("which "^viewer)) <> 0 then
      raise ExceptionViewerNotFound
    else
      let val file = (File.platform_path f);
          val filePDF = file^".pdf";
          val cmd = (viz^" -o "^filePDF^" -Tpdf "^file^" && "^viewer^" "^filePDF) (*^" && rm "^filePDF*)
      in
        if !open_viewer then
          (writeln ("executing: "^cmd); Isabelle_System.bash cmd; ())
        else
          ();
        Isabelle_System.bash ("rm "^file) (*cleanup dot file, PDF file will still exist*)
      end
in
  val paintGraphDotLinux = paintGraph "xdg-open" "dot"
  end;

fun evaluate_term (thy: theory) (edges: term) : term = 
  case Code_Evaluation.dynamic_value thy edges
    of SOME x => x
    | NONE => raise TERM ("could not evaluate", []);


local 
  local
    fun is_valid_char (c : char) : bool =
        (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
        (c <= #"9" andalso c >= #"0");
    
    fun sanitize_string (s: string) : string =
      String.map (fn c => if is_valid_char c then c else #"_") s;
  
    (*val _ = writeln (sanitize_string "asdsa sjhsa saklj \"/$(Tnd 098z8    9");*) (*Example*)
  in
    fun format_dot_edges (tune_node_format : term -> string -> string) (trm: (term * term) list): string list =
      let
        fun format_node t = t |> Syntax.pretty_term @{context} |> Pretty.string_of |> ATP_Util.unyxml |> tune_node_format t |>  sanitize_string
        fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";\n"
      in
        writeln "TODO: name clashes?"; map format_dot_edge trm
      end;
    end;
  
  fun apply_dot_header (es: string list) : string =
    "digraph graphname {\n" ^ implode es ^ "}";
in
  fun visualize_graph_pretty (thy: theory) (tune_node_format : term -> string -> string) (Es : (string * term) list ) =
    let 
      val evaluated_edges : (string * term) list = List.map (fn (str, t) => (str, evaluate_term thy t)) Es;
      val edge_to_string  : (term -> string) = HOLogic.dest_list #> map HOLogic.dest_prod #> format_dot_edges tune_node_format #> implode;
      val formatted_edges : string list = List.map (fn (str, t) => str ^ "\n" ^ (edge_to_string t)) evaluated_edges;
    in
      apply_dot_header formatted_edges 
      |> write_to_tmpfile
      (*|> ohShitOpenFileInGedit*)
      |> paintGraphDotLinux
    end;
  end;

(*
the parameter edges is just a list of pairs
[(a,b), ..]
*)
fun visualize_graph (thy: theory) (tune_node_format : term -> string -> string) (edges: term) =
  visualize_graph_pretty thy tune_node_format [("", edges)];

end;
*}


end
