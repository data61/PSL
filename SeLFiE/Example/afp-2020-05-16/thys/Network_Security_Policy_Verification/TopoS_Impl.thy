theory TopoS_Impl
imports TopoS_Library TopoS_Composition_Theory_impl
    (*Mehr Meta wagen!*)
    "Security_Invariants/METASINVAR_SystemBoundary"
    (*stuff*)
    "Lib/ML_GraphViz"
    TopoS_Stateful_Policy_impl
begin


section \<open>ML Visualization Interface\<close>

definition print_offending_flows_debug ::
  "'v  SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> (string \<times> ('v \<times> 'v) list list) list" where
  "print_offending_flows_debug M G = map
    (\<lambda>m.
         (implc_description m @ '' ('' @ implc_type m @ '')''
         , implc_offending_flows m G)
    ) M"

(*TODO: move and tune*)
ML\<open>
fun pretty_assoclist ctxt header t = let
    val ls : (term * term) list = t |> HOLogic.dest_list |> map HOLogic.dest_prod;
    val pretty = fn t => Pretty.string_of (Syntax.pretty_term ctxt t);
    in ls
       |> map (fn (x, y) => "  "^pretty x^": "^pretty y)
       |> space_implode "\n"
       |> (fn s => header^s)
       |> writeln end
\<close>

subsection\<open>Utility Functions\<close>

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
        apply(simp split: if_split_asm)
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


  text\<open>only for prettyprinting\<close>
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



ML\<open>
(*apply args to f. f ist best supplied using @{const_name "name_of_function"} *)
fun apply_function (ctxt: Proof.context) (f: string) (args: term list) : term = 
  let
    val _ = writeln ("applying "^f^" to " ^ (fold (fn t => fn acc => acc^(Pretty.string_of (Syntax.pretty_term (Config.put show_types true ctxt) t))^" ") args ""));
    (*val t_eval = Code_Evaluation.dynamic_value_strict thy t;*)
    (* $ associates to the left, give f its arguments*)
    val applied_untyped_uneval: term = list_comb (Const (f, dummyT), args);
    val applied_uneval: term = Syntax.check_term ctxt applied_untyped_uneval;
  in
    applied_uneval |> Code_Evaluation.dynamic_value_strict ctxt
  end;


(*ctxt -> edges -> (biflows, uniflows)*)
fun partition_by_biflows ctxt (t: term) : (term * term) = 
  apply_function ctxt @{const_name "partition_by_biflows"} [t] |> HOLogic.dest_prod


local
  fun get_tune_node_format (edges: term) : term -> string -> string =
    if (fastype_of edges) = @{typ "(string \<times> string) list"}
    then
      tune_string_vertex_format
    else
      Graphviz.default_tune_node_format;

  fun evalutae_term ctxt (edges: term) : term = 
    case Code_Evaluation.dynamic_value ctxt edges
      of SOME x => x
      | NONE => raise TERM ("could not evaluate", []);
in
  fun visualize_edges ctxt (edges: term) (coloredges: (string * term) list) (graphviz_header: string) = 
    let
      val _ = writeln("visualize_edges");
      val (biflows, uniflows) = partition_by_biflows ctxt edges;
    in
      Graphviz.visualize_graph_pretty ctxt (get_tune_node_format edges) ([
      ("", uniflows),
      ("edge [dir=\"none\", color=\"#000000\"]", biflows)] @ coloredges) (*dir=none, dir=both*)
       graphviz_header
    end

  (*iterate over the edges in ML, useful for printing them in certain formats*)
  fun iterate_edges_ML ctxt (edges: term) (all: (string*string) -> unit) (bi: (string*string) -> unit) (uni: (string*string) -> unit): unit =
    let
      val _ = writeln("iterate_edges_ML");
      val tune_node_format = (get_tune_node_format edges);
      val node_to_string = Graphviz.node_to_string ctxt tune_node_format;
      val evaluated_edges : term = evalutae_term ctxt edges;
      val (biflows, uniflows) = partition_by_biflows ctxt evaluated_edges;
    in
      let
        fun edge_to_list (es: term) : (term * term) list = es |> HOLogic.dest_list |> map HOLogic.dest_prod;
        fun edge_to_string (es: (term * term) list) : (string * string) list =
          map (fn (v1, v2) => (node_to_string v1, node_to_string v2)) es
      in
        edge_to_list evaluated_edges |> edge_to_string |> map all;
        edge_to_list biflows |> edge_to_string |> map bi;
        edge_to_list uniflows |> edge_to_string |> map uni;
        ()
      end
      handle Subscript => writeln ("Subscript Exception in iterate_edges_ML")
    end;
    
end
\<close>

ML_val\<open>
local
  val (biflows, uniflows) = partition_by_biflows @{context} @{term "[(1::int, 1::int), (1,2), (2, 1), (1,3)]"};
in
  val _ = Pretty.writeln (Syntax.pretty_term (Config.put show_types true @{context}) biflows);
  val _ = Pretty.writeln (Syntax.pretty_term (Config.put show_types true @{context}) uniflows);
end;

val t = fastype_of @{term "[(''x'', 2::nat)]"};

\<close>
ML_val\<open>(*
visualize_edges @{context}  @{term "[(1::int, 1::int), (1,2), (2, 1), (1,3)]"} []; *)
\<close>



definition internal_get_invariant_types_list:: "'a SecurityInvariant list \<Rightarrow> string list" where
  "internal_get_invariant_types_list M \<equiv> map implc_type M"


definition internal_node_configs :: "'a list_graph \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times>'b) list" where
  "internal_node_configs G config \<equiv> zip (nodesL G) (map config (nodesL G))"

ML \<open>
local
  fun get_graphivz_node_desc ctxt (node_config: term): string =
   let
     val (node, config) = HOLogic.dest_prod node_config;
     (*TODO: tune node format? There must be a better way ...*)
     val tune_node_format = if (fastype_of node) = @{typ "string"}
      then
        tune_string_vertex_format
      else
        Graphviz.default_tune_node_format;
     val node_str = Graphviz.node_to_string ctxt tune_node_format node;
     val config_str = Graphviz.term_to_string_html ctxt config;
   in
     node_str^"[label=<<TABLE BORDER=\"0\" CELLSPACING=\"0\"><TR><TD><FONT face=\"Verdana Bold\">"^node_str^"</FONT></TD></TR><TR><TD>"^config_str^"</TD></TR></TABLE>>]\n"
   end;
in
  fun generate_graphviz_header ctxt (G: term) (configs: term): string =
    let
      val configlist: term list = apply_function ctxt @{const_name "internal_node_configs"} [G, configs] |> HOLogic.dest_list;
    in
      fold (fn c => fn acc => acc^get_graphivz_node_desc ctxt c) configlist ""
    end;
end;

(* Convenience function. Use whenever possible!
  M: security requirements, list
  G: list_graph*)
fun visualize_graph_header ctxt (M: term) (G: term) (Config: term): unit = 
  let
    val wf_list_graph = apply_function ctxt @{const_name "wf_list_graph"} [G];
    val all_fulfilled = apply_function ctxt @{const_name "all_security_requirements_fulfilled"} [M, G];
    val edges = apply_function ctxt @{const_name "edgesL"} [G];
    val invariants = apply_function ctxt @{const_name "internal_get_invariant_types_list"} [M];
    val _ = writeln("Invariants:" ^ Pretty.string_of (Syntax.pretty_term ctxt invariants));
    val header = if Config = @{term "[]"} then "#header" else generate_graphviz_header ctxt G Config;
  in
    if wf_list_graph = @{term "False"} then
      error ("The supplied graph is syntactically invalid. Check wf_list_graph.")
    else if all_fulfilled = @{term "False"} then
      (let
        val offending = apply_function ctxt @{const_name "implc_get_offending_flows"} [M, G];
        val offending_flat = apply_function ctxt @{const_name "List.remdups"} [apply_function ctxt @{const_name "List.concat"} [offending]];
        val offending_debug = apply_function ctxt @{const_name print_offending_flows_debug} [M, G];
      in
       writeln("offending flows:");
       Pretty.writeln (Syntax.pretty_term ctxt offending);
       pretty_assoclist ctxt "Offending flows per invariant:\n" offending_debug;
       visualize_edges ctxt edges [("edge [dir=\"arrow\", style=dashed, color=\"#FF0000\", constraint=false]", offending_flat)] header; 
      () end)
    else if all_fulfilled <> @{term "True"} then raise ERROR "all_fulfilled neither False nor True" else (
       writeln("All valid:");
       visualize_edges ctxt edges [] header; 
      ())
  end;


fun visualize_graph ctxt (M: term) (G: term): unit = visualize_graph_header ctxt M G @{term "[]"};
\<close>

end
