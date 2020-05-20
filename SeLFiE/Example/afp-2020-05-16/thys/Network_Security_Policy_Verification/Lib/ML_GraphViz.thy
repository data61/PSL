theory ML_GraphViz
imports Main
begin

ML \<open>
(*should we open a pdf viewer to display the generated graph?*)
datatype open_viewer = DoNothing | OpenImmediately | AskTimeouted of real

signature GRAPHVIZ =
sig
  val open_viewer: open_viewer Unsynchronized.ref

  (*function to modify the printing of a node name*)
  val default_tune_node_format: term -> string -> string

  (* edges is a term of type ('a \<times> 'a) list *)
  
  (* @{context} default_tune_node_format (edges_format \<times> edges)list*)
  val visualize_graph: Proof.context -> (term -> string -> string) -> term -> unit

  (* @{context} default_tune_node_format (edges_format \<times> edges)list graphviz_header*)
  val visualize_graph_pretty: Proof.context -> (term -> string -> string) -> (string * term) list -> string-> unit

  (* helper function.
     @{context} tune_node_format node *)
  val node_to_string: Proof.context -> (term -> string -> string) ->  term -> string
  val term_to_string: Proof.context ->  term -> string;
  val term_to_string_safe: Proof.context ->  term -> string;
  val term_to_string_html: Proof.context ->  term -> string;
end

structure Graphviz: GRAPHVIZ =
struct

(*if set to `DoNothing`, graphviz will not be run and not pdf will be opened. Include ML_GraphViz_Disable.thy to run in batch mode.*)
val open_viewer = (* FIXME avoid mutable state *)
  Unsynchronized.ref (if getenv "ISABELLE_DOT" = "" then DoNothing else OpenImmediately)

val default_tune_node_format: term -> string -> string = (fn _ => I)

fun evaluate_term (ctxt: Proof.context) edges = 
  case Code_Evaluation.dynamic_value ctxt edges of
    SOME x => x
  | NONE => error "ML_GraphViz: failed to evaluate term"


fun is_valid_char c =
  (c <= #"z" andalso c >= #"a") orelse (c <= #"Z" andalso c >= #"A") orelse
  (c <= #"9" andalso c >= #"0")

val sanitize_string =
  String.map (fn c => if is_valid_char c then c else #"_")


fun term_to_string ctxt t =
  let
    val ctxt' = Config.put show_markup false ctxt;
  in Print_Mode.setmp [] (Syntax.string_of_term ctxt') t
  end;


fun term_to_string_safe ctxt t = 
  let
    val str = term_to_string ctxt t
  in
    if sanitize_string str <> str
    then (warning ("String  "^str^" contains invalid characters!"); sanitize_string str)
    else str end;

local
  val sanitize_string_html =
    String.map (fn c => if (is_valid_char c orelse c = #" " orelse (c <= #"/" andalso c >= #"(")
                            orelse c = #"|" orelse c = #"=" orelse c = #"?" orelse c = #"!" orelse c = #"_"
                            orelse c = #"[" orelse c = #"]") then c else #"_")
in
  fun term_to_string_html ctxt (n: term) : string = 
    let
      val str = term_to_string ctxt n
    in
      if sanitize_string_html str <> str
      then (warning ("String  "^str^" contains invalid characters!"); sanitize_string_html str)
      else str end
end;

fun node_to_string ctxt (tune_node_format: term -> string -> string) (n: term) : string = 
  n |> term_to_string ctxt |> tune_node_format n
  handle Subscript =>
    error ("Subscript Exception in node_to_string for string " ^
           (Pretty.string_of (Syntax.pretty_term ctxt n)));

local
  fun display_graph graph =
    if getenv "ISABELLE_DOT" = "" then
      error "Missing $ISABELLE_DOT settings variable (Graphviz \"dot\" executable)"
    else
      Isabelle_System.with_tmp_file "graphviz" "dot" (fn graph_file =>
        let
          val _ = File.write graph_file graph;
          val pdf_file = Path.explode "$ISABELLE_HOME_USER/graphviz.pdf";
          val _ =
            (Isabelle_System.bash o cat_lines)
             ["set -e",
              "cd " ^ File.bash_path (Path.dir graph_file),
              "\"$ISABELLE_DOT\" -o " ^ Bash_Syntax.string (File.platform_path pdf_file) ^
                " -Tpdf " ^ Bash_Syntax.string (File.platform_path graph_file),
              "\"$PDF_VIEWER\" " ^ File.bash_path pdf_file ^ " &"];
        in () end);

  fun format_dot_edges ctxt tune_node_format trm =
    let
      fun format_node t = let val str = node_to_string ctxt tune_node_format t in
                              if sanitize_string str <> str then
                                (warning ("Node "^str^" contains invalid characters!"); sanitize_string str)
                              else str
                            end;
      fun format_dot_edge (t1, t2) = format_node t1 ^ " -> " ^ format_node t2 ^ ";\n"
    in
      map format_dot_edge trm
    end

  fun apply_dot_header header edges =
    "digraph graphname {\n#header\n" ^ header ^"\n#edges\n\n"^ implode edges ^ "}"
in
  fun visualize_graph_pretty ctxt tune_node_format Es (header: string) =
    let 
      val evaluated_edges = map (fn (str, t) => (str, evaluate_term ctxt t)) Es;
      val edge_to_string = HOLogic.dest_list #> map HOLogic.dest_prod #> format_dot_edges ctxt tune_node_format #> implode;
      val formatted_edges = map (fn (str, t) => str ^ "\n" ^ edge_to_string t) evaluated_edges;
      fun execute_command () = display_graph (apply_dot_header header formatted_edges);
    in
      case !open_viewer of
          DoNothing => writeln "visualization disabled (Graphviz.open_viewer)"
        | OpenImmediately => execute_command ()
        | AskTimeouted wait_seconds => let val (text, promise) = Active.dialog_text ();
            val _ = writeln ("Run Grpahviz and display pdf? " ^ text "yes" ^ "/" ^ text "no" ^ " (execution paused)")
            in
              Timeout.apply (seconds wait_seconds) (fn _ => 
                let val m = (Future.join promise) in
                (if m = "yes" then execute_command () else (writeln "no"))
                end
              ) ()
             end handle Timeout.TIMEOUT _ =>
                  (writeln ("Timeouted. You did not klick yes/no. Killed to continue. " ^
                            "If you want to see the pdf, just re-run this and klick yes."))
    end
  end

fun visualize_graph ctxt tune_node_format edges =
  visualize_graph_pretty ctxt tune_node_format [("", edges)] "#TODO add header here"

end;
\<close>


end
