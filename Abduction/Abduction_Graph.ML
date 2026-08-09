(*  Title:      Abduction/Abduction_Graph.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

Data structure representing the abduction (AND/OR) graph used by AbductionProver.
*)
(*** ABDUCTION_GRAPH ***)
signature ABDUCTION_GRAPH =
sig

(** abduction_graph **)
(* key, PGraph_Key, and PGraph *)
datatype node_type = Or_N | And_N | O2A_E of int;
val node_type_compare: (node_type * node_type) -> order;

structure PGraph: GRAPH

type abduction_node;

type key = (node_type * terms(*normal terms not thms*));
type keys = key list;

val print_key  : Proof.context -> key -> unit list;
val equal_keys : (key * key) -> bool;

type abduction_graph;

type graph_profile =
 {nodes_total: int,
  edges_total: int,
  or_nodes: int,
  and_nodes: int,
  or2and_edge_nodes: int,
  avg_indegree: real,
  max_indegree: int,
  scc_count: int,
  cyclic_scc_count: int,
  largest_scc_size: int,
  or_projected_edges: int,
  or_projected_avg_indegree: real,
  or_projected_max_indegree: int,
  or_projected_scc_count: int,
  or_projected_cyclic_scc_count: int,
  or_projected_largest_scc_size: int,
  and_projected_edges: int,
  and_projected_avg_indegree: real,
  and_projected_max_indegree: int,
  and_projected_scc_count: int,
  and_projected_cyclic_scc_count: int,
  and_projected_largest_scc_size: int};

val graph_profile: abduction_graph -> graph_profile;

(* creation of key_val pair *)
type is_final_goal = bool;
val mk_ornode:  Proof.context -> is_final_goal -> string -> term -> (key * abduction_node);
val mk_andnode: terms -> (key * abduction_node);

(* key to term *)
val orkey_to_term  : key -> term;
val andkey_to_terms: key -> terms;

(* initialization *)
val mk_initial_graph: Proof.context -> term -> abduction_graph;

(* query on key and graph *)
val is_branch     : abduction_graph -> key -> bool;
val is_ornode     : key -> bool;
val is_andnode    : key -> bool;
val is_or2and_edge: key -> bool;
val importance    : abduction_graph -> key -> real;

(* query on abduction_node for ornode and andnode *)
val is_proved_completely                         : abduction_graph -> key -> bool;

(* query on abduction_node for ornode *)
val is_final_goal                                : abduction_graph -> key -> bool;
val lemma_name_of                                : abduction_graph -> key -> string;
val print_orkey                                  : Proof.context -> abduction_graph -> key -> unit;
val proof_of                                     : abduction_graph -> key -> strings;
val proof_id_of                                  : abduction_graph -> key -> int option;
val is_template_based                            : abduction_graph -> key -> bool;
val compute_importance_of_ornode                 : abduction_graph -> key -> real;
val sort_orkeys_based_on_importance              : abduction_graph -> keys -> keys;

val grand_parents                                : abduction_graph -> key -> keys;
val grand_children                               : abduction_graph -> key -> keys;

(* query on abduction_node for or2and_edge *)
val or2and_edge_to_proof                         : abduction_graph -> key -> strings;

(* general queries *)
val is_worth_proving                             : Proof.context -> abduction_graph -> key -> bool;
val get_final_goal_term                          : abduction_graph -> term;
val get_leaf_orterms                             : abduction_graph -> terms;
val get_final_goal_key                           : abduction_graph -> key;
type frontier_counts =
 {reachable_keys: int,
  reachable_or_nodes: int,
  reachable_or_leaf_nodes: int};
val orkeys_tobe_expanded_in_with_reachable_count :
  Proof.context -> abduction_graph -> (keys * frontier_counts);

(* query on abduction_graph *)
val final_goal_proved_completely                 : abduction_graph -> bool;
val prove_term_completely                        : Proof.state -> term -> strings option;
val prove_orkey_completely                       :
  key -> abduction_graph -> Proof.state -> strings option;
val keys                                         : abduction_graph -> keys;

val goal_as_string                               : Proof.context -> key -> string;
(* The strings are the names of the TBC-preprocessed facts the search context held as simp
   rules; a graph script's simp-consuming steps name them explicitly on the way out - see
   TBC_Utils.augment_method_with_facts. *)
val print_lemma_and_proof_of_key                 :
  Proof.context -> strings -> abduction_graph -> key -> string;
(* The int is the offset at which this node's variables are renumbered, so that an assembled
   proof has no two unrelated var_0s - see Top_Down_Util.offset_vnames. *)
val print_have_and_proof_of_key                  :
  Proof.context -> strings -> abduction_graph -> int -> key -> string;
val print_proof_of_key_only                      : abduction_graph -> key -> string;
(*TODO: no longer used.*)
val print_proof_of_graph: Proof.state -> abduction_graph -> unit;

end;

(*** Abduction_Graph ***)
structure Abduction_Graph: ABDUCTION_GRAPH =
struct

open Update_Abduction_Node;

(** abduction_graph **)
(* node_type *)
datatype node_type = Or_N | And_N | O2A_E of int;

(* node_type_compare *)
fun node_type_compare (Or_N,     Or_N    ) = EQUAL
 |  node_type_compare (Or_N,     _       ) = LESS
 |  node_type_compare (And_N,    O2A_E _ ) = LESS
 |  node_type_compare (And_N,    And_N   ) = EQUAL
 |  node_type_compare (And_N,    _       ) = GREATER
 |  node_type_compare (O2A_E i1, O2A_E i2) = Int.compare (i1, i2)
 |  node_type_compare (O2A_E _,  _       ) = GREATER;

(* PGraph_Key *)
structure PGraph_Key =
    struct
      type key = (node_type * terms(*normal terms not thms*))
      val  ord = prod_ord node_type_compare (list_ord Top_Down_Util.term_compare)
    end:KEY

(* PGraph *)
structure PGraph = Graph (PGraph_Key): GRAPH;

(* abduction_graph *)
type abduction_graph = abduction_node PGraph.T;

type graph_profile =
 {nodes_total: int,
  edges_total: int,
  or_nodes: int,
  and_nodes: int,
  or2and_edge_nodes: int,
  avg_indegree: real,
  max_indegree: int,
  scc_count: int,
  cyclic_scc_count: int,
  largest_scc_size: int,
  or_projected_edges: int,
  or_projected_avg_indegree: real,
  or_projected_max_indegree: int,
  or_projected_scc_count: int,
  or_projected_cyclic_scc_count: int,
  or_projected_largest_scc_size: int,
  and_projected_edges: int,
  and_projected_avg_indegree: real,
  and_projected_max_indegree: int,
  and_projected_scc_count: int,
  and_projected_cyclic_scc_count: int,
  and_projected_largest_scc_size: int};

(* key *)
type key  = PGraph.key

fun print_key  (ctxt:Proof.context) ((_, trms): key) =
  (
    tracing "  key is:";
    map (fn trm => tracing ("    " ^ Isabelle_Utils.trm_to_string ctxt trm)) trms
  );

(* keys *)
type keys = PGraph.key list;

type frontier_counts =
 {reachable_keys: int,
  reachable_or_nodes: int,
  reachable_or_leaf_nodes: int};

(* equal_key *)
fun equal_keys key_pair = PGraph_Key.ord key_pair = EQUAL;

(* creation of key_val pair *)
type is_final_goal = bool;

(* Standardised IN CONTEXT, so a variable the surrounding proof has fixed keeps its own name.
 *
 * This used to call the context-free standardize_vnames, and ctxt was taken but not used for it.
 * That undid, one layer down, the in-context standardisation the callers perform: the goal reached
 * focus_and_prepare_search as "double x = t2 x x" and entered the graph as
 * "double var_0 = t2 var_0 var_0", so every script found for it said "induct var_0" while the
 * caller's goal still said x. The replay then failed with "Unable to figure out induct rule" - the
 * defect docs/2026_08_02_progress_report.md 4.9 describes, whose fix was applied at
 * proof_by_abduction_with_prelude_using and not here. Measured: solve on TIP_prop_01 found a proof
 * in 448s and could not replay it, with the rename mapping legitimately empty because nothing
 * upstream had renamed anything.
 *
 * Safe for deduplication, which is the reason to check before touching this. Graph keys compare
 * through PGraph_Key.ord -> Top_Down_Util.term_compare, which standardises BOTH sides before
 * comparing, so alpha-equivalent nodes still unify whatever names the stored term carries. The
 * canonical form is a property of the comparison, not of the stored term - the same separation
 * offset_vnames rests on. *)
fun mk_ornode (ctxt:Proof.context) (is_final_goal:is_final_goal) (lemma_name:string) (goal:term) =
  let
    val standardized_goal =
      Top_Down_Util.standardize_vnames_with_mapping_in_ctxt ctxt goal |> fst;
  in
    (
      (Or_N, [standardized_goal]): key,
      Abduction_Node.mk_ornode ctxt is_final_goal lemma_name standardized_goal: abduction_node
     )
  end;

fun mk_andnode (goals:terms) =
  let
    val standardized_terms = map Top_Down_Util.standardize_vnames goals;
    val sorted_terms       = sort Term_Ord.term_ord standardized_terms;
  in
    ((And_N, sorted_terms): key,
      Abduction_Node.mk_andnode sorted_terms)
  end;

(* key to term *)
fun orkey_to_term (Or_N, [orleaf_term]) = orleaf_term
  | orkey_to_term  _                    = error "orkey_to_term failed.";

fun andkey_to_terms (And_N, terms) = terms
  | andkey_to_terms  _             = error "andkey_to_terms failed.";


(* mk_initial_graph *)
fun mk_initial_graph (ctxt:Proof.context) (goal:term) =
  let
    val root_pair = mk_ornode ctxt true "(*we do not need to pass a name for the top goal.*)" goal
                  : key * Abduction_Node.abduction_node;
    val empty_graph = PGraph.empty: abduction_graph;
  in
    PGraph.new_node root_pair empty_graph
  end;

(** query on key **)
(* is_branch *)
fun is_branch (graph:abduction_graph) (key:key) =
  PGraph.get_node graph key |> Abduction_Node.is_branch: bool;

(* is_ornode *)
fun is_ornode (Or_N, _) = true
  | is_ornode  _        = false;

(* is_andnode *)
fun is_andnode (And_N, _) = true
  | is_andnode  _         = false;

(* is_or2and_edge *)
fun is_or2and_edge (O2A_E _, _) = true
  | is_or2and_edge  _           = false;

fun int_max xs = fold (fn x => fn acc => Int.max (x, acc)) xs 0;

fun distinct_keys (ks:keys) =
  fold (fn key => fn acc => if member equal_keys acc key then acc else key :: acc) ks [] |> rev;

fun equal_key_pair ((p1, c1), (p2, c2)) =
  equal_keys (p1, p2) andalso equal_keys (c1, c2);

fun distinct_edges edges =
  fold (fn edge => fn acc => if member equal_key_pair acc edge then acc else edge :: acc) edges []
  |> rev;

fun key_in (ks:keys) key = member equal_keys ks key;

fun filter_edges_over_nodes nodes edges =
  filter (fn (p, c) => key_in nodes p andalso key_in nodes c) edges;

fun edge_in edges edge = member equal_key_pair edges edge;

fun succs_from_edges edges key =
  map snd (filter (fn (p, _) => equal_keys (p, key)) edges);

fun preds_from_edges edges key =
  map fst (filter (fn (_, c) => equal_keys (c, key)) edges);

fun reachable_from succs start =
  let
    fun visit [] seen = seen
      | visit (key :: rest) seen =
          if member equal_keys seen key
          then visit rest seen
          else visit (succs key @ rest) (key :: seen);
  in
    visit [start] []
  end;

fun subtract_keys xs ys = filter (fn x => not (member equal_keys ys x)) xs;

fun intersect_keys xs ys = filter (fn x => member equal_keys ys x) xs;

fun sccs_from_edges nodes edges =
  let
    val nodes' = distinct_keys nodes;
    fun succs key = succs_from_edges edges key;
    fun preds key = preds_from_edges edges key;
    fun loop [] acc = rev acc
      | loop (key :: rest) acc =
          let
            val forwards  = reachable_from succs key;
            val backwards = reachable_from preds key;
            val component = intersect_keys forwards backwards;
            val rest'     = subtract_keys rest component;
          in
            loop rest' (component :: acc)
          end;
  in
    loop nodes' []
  end;

type directed_profile =
 {edges: int,
  avg_indegree: real,
  max_indegree: int,
  scc_count: int,
  cyclic_scc_count: int,
  largest_scc_size: int};

fun directed_profile nodes raw_edges : directed_profile =
  let
    val nodes' = distinct_keys nodes;
    val edges = raw_edges |> filter_edges_over_nodes nodes' |> distinct_edges;
    val nodes_total = length nodes': int;
    val edges_total = length edges: int;
    val pred_counts = map (length o preds_from_edges edges) nodes': int list;
    val avg_indegree =
      if nodes_total = 0 then 0.0
      else Real.fromInt edges_total / Real.fromInt nodes_total: real;
    val sccs = sccs_from_edges nodes' edges: keys list;
    fun cyclic_component [key] = edge_in edges (key, key)
      | cyclic_component component = length component > 1;
  in
   {edges = edges_total,
    avg_indegree = avg_indegree,
    max_indegree = int_max pred_counts,
    scc_count = length sccs,
    cyclic_scc_count = length (filter cyclic_component sccs),
    largest_scc_size = int_max (map length sccs)}
  end;

fun graph_profile (graph:abduction_graph): graph_profile =
  let
    val ks = PGraph.keys graph: keys;
    fun succs key = PGraph.immediate_succs graph key;
    val full_edges = maps (fn parent => map (fn child => (parent, child)) (succs parent)) ks;
    val or_keys = filter is_ornode ks;
    val and_keys = filter is_andnode ks;
    val edge_keys = filter is_or2and_edge ks;

    fun or_projected_children parent_or =
      succs parent_or
      |> filter is_or2and_edge
      |> maps (fn edge_key =>
           succs edge_key
           |> filter is_andnode
           |> maps (fn and_key => succs and_key |> filter is_ornode))
      |> distinct_keys;

    val or_projected_edges =
      maps (fn parent_or => map (fn child_or => (parent_or, child_or))
                               (or_projected_children parent_or)) or_keys;

    fun and_projected_children parent_and =
      succs parent_and
      |> filter is_ornode
      |> maps (fn or_key =>
           succs or_key
           |> filter is_or2and_edge
           |> maps (fn edge_key => succs edge_key |> filter is_andnode))
      |> distinct_keys;

    val and_projected_edges =
      maps (fn parent_and => map (fn child_and => (parent_and, child_and))
                                (and_projected_children parent_and)) and_keys;

    val {edges = edges_total,
         avg_indegree = avg_indegree,
         max_indegree = max_indegree,
         scc_count = scc_count,
         cyclic_scc_count = cyclic_scc_count,
         largest_scc_size = largest_scc_size} = directed_profile ks full_edges;

    val {edges = or_projected_edges_total,
         avg_indegree = or_projected_avg_indegree,
         max_indegree = or_projected_max_indegree,
         scc_count = or_projected_scc_count,
         cyclic_scc_count = or_projected_cyclic_scc_count,
         largest_scc_size = or_projected_largest_scc_size} =
          directed_profile or_keys or_projected_edges;

    val {edges = and_projected_edges_total,
         avg_indegree = and_projected_avg_indegree,
         max_indegree = and_projected_max_indegree,
         scc_count = and_projected_scc_count,
         cyclic_scc_count = and_projected_cyclic_scc_count,
         largest_scc_size = and_projected_largest_scc_size} =
          directed_profile and_keys and_projected_edges;
  in
   {nodes_total = length ks,
    edges_total = edges_total,
    or_nodes = length or_keys,
    and_nodes = length and_keys,
    or2and_edge_nodes = length edge_keys,
    avg_indegree = avg_indegree,
    max_indegree = max_indegree,
    scc_count = scc_count,
    cyclic_scc_count = cyclic_scc_count,
    largest_scc_size = largest_scc_size,
    or_projected_edges = or_projected_edges_total,
    or_projected_avg_indegree = or_projected_avg_indegree,
    or_projected_max_indegree = or_projected_max_indegree,
    or_projected_scc_count = or_projected_scc_count,
    or_projected_cyclic_scc_count = or_projected_cyclic_scc_count,
    or_projected_largest_scc_size = or_projected_largest_scc_size,
    and_projected_edges = and_projected_edges_total,
    and_projected_avg_indegree = and_projected_avg_indegree,
    and_projected_max_indegree = and_projected_max_indegree,
    and_projected_scc_count = and_projected_scc_count,
    and_projected_cyclic_scc_count = and_projected_cyclic_scc_count,
    and_projected_largest_scc_size = and_projected_largest_scc_size}
  end;

(* importance *)
fun importance (ag:abduction_graph) (orkey as (Or_N, _)) =
     PGraph.get_node ag orkey |> Abduction_Node.importance
  | importance (ag:abduction_graph) (edge_key as (O2A_E _, _)) =
     PGraph.get_node ag edge_key |> Abduction_Node.importance
  | importance (ag:abduction_graph) (andkey as (And_N, _)) =
let
  val parents_of             = PGraph.immediate_preds ag;
  val parent_or2and_edges    = parents_of andkey: keys;
  fun computation f x        = (x, f x);
  val edge_and_ornodes_pairs = map (computation parents_of) parent_or2and_edges: (key * keys) list;
  val ornodess               = map snd edge_and_ornodes_pairs: keys list;
  val _ =
        if forall (fn ornodes => length ornodes = 1) ornodess then ()
        else error "importance_of_andnode failed";
  val edge_and_ornode_pairs  = map (apsnd hd) edge_and_ornodes_pairs: (key * key) list;
  val importance_pairs       =
        map (apply2 (importance ag)) edge_and_ornode_pairs: (real * real) list;
  val importances            = map (fn (imp1, imp2) => imp1 * imp2) importance_pairs: real list;
  val importance             = case Utils.reals_to_max_option importances of
                                 NONE     =>
                                   error "importance in Abduction_Graph failed. No ancestral pairs."
                               | SOME max => max: real;
in
  importance
end;

(* is_proved_completely *)
fun is_proved_completely (graph:abduction_graph) (key:key): bool =
  PGraph.get_node graph key |> Abduction_Node.is_proved_completely;

(* lemma_name_of *)
fun lemma_name_of (graph:abduction_graph) (key:key) =
  PGraph.get_node graph key |> Abduction_Node.lemma_name_of: string;

fun print_orkey  (ctxt:Proof.context) (graph:abduction_graph) (orkey as (_, [trm]): key) =
  (
    tracing "  abduced_lemma is:";
    tracing ("    " ^ lemma_name_of graph orkey);
    tracing ("    " ^ Isabelle_Utils.trm_to_string ctxt trm);
    tracing ("    " ^ "Importance is: " ^ (importance graph orkey |> Real.toString))
  );

(* grand_relatives *)
fun grand_relatives
    (graph:abduction_graph) (key:key) (preds_or_succs: abduction_graph -> key -> key list): keys =
  let
    val immediate_keys = preds_or_succs graph key: keys;
    val grand_keys = map (preds_or_succs graph) immediate_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* grand_parents *)
fun grand_parents (graph:abduction_graph) (key:key): keys =
      grand_relatives graph key PGraph.immediate_preds;

(* grand_children *)
fun grand_children (graph:abduction_graph) (key:key): keys =
      grand_relatives graph key PGraph.immediate_succs;

(* is_final_goal *)
fun is_final_goal (graph:abduction_graph) (key as (Or_N, _): key): bool =
    PGraph.get_node graph key |> Abduction_Node.is_final_goal
  | is_final_goal _ _ = false;

fun get_leaf_orterms (graph:abduction_graph) =
  let
    val all_keys     = PGraph.keys graph: keys;
    val or_keys      = filter is_ornode all_keys: keys;
    fun has_no_child (key:key) = null (PGraph.immediate_succs graph key): bool;
    val orleaf_keys  = filter has_no_child or_keys: keys;
    val orleaf_terms = map orkey_to_term orleaf_keys: terms;
  in
    orleaf_terms: terms
  end;

(* get_final_goal_key *)
fun get_final_goal_key (graph:abduction_graph) =
  let
    val final_goals = PGraph.keys graph |> filter (is_final_goal graph): keys;
    val final_goal  = if length final_goals = 1
                      then hd final_goals
                      else error "get_final_goal_key failed. Not exactly one final_goals.";
  in
    final_goal
  end;

(* get_final_goal_term *)
fun get_final_goal_term (graph:abduction_graph) =
  let
    val final_goal_key = get_final_goal_key graph: key;
    val final_goal_term = case final_goal_key of
        (Or_N, [term]) => term
      |  _ => error "get_final_goal_term in Abduction_Graph.ML failed";
  in
    final_goal_term
  end;

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (graph:abduction_graph) (key:key)  =
  PGraph.get_node graph key |> Abduction_Node.is_worth_proving ctxt: bool;

(* proof_id_of *)
fun proof_id_of (graph:abduction_graph) (key:key) =
      PGraph.get_node graph key |> Abduction_Node.proof_id_of: int option;

(* is_template_based *)
fun is_template_based (ag:abduction_graph) (key:key) =
  let
    val node   = PGraph.get_node ag key: abduction_node;
    val result = Abduction_Node.is_template_based node;
  in
    result
  end;

(* compute_importance_of_ornode *)
fun compute_importance_of_ornode (ag:abduction_graph) (orkey as (Or_N, _)) =
    let
      val parent_andkeys         = PGraph.immediate_preds ag orkey: keys;
      val importances_of_parents = map (importance ag) parent_andkeys: real list;
      val importance_from_parent = case Utils.reals_to_max_option importances_of_parents of
                                     NONE     =>
                                       error "compute_importance_of_ornode. No ancestral andnode."
                                   | SOME max => max: real;
      val importance = if is_template_based ag orkey
                       then (1.0 + importance_from_parent) / 2.0
                       else importance_from_parent: real; (*TODO: magic number & magic formula*)
    in
      importance
    end
  | compute_importance_of_ornode _ _ =
      error "compute_importance_of_ornode failed. It expects a key of an or-node.";

(* sort_orkeys_based_on_importance *)
fun sort_orkeys_based_on_importance (ag:abduction_graph) (keys:keys) =
  let
    fun key_compare (key1, key2) = Real.compare (importance ag key1, importance ag key2);
    val sorted_keys = sort key_compare keys |> rev;
  in
    sorted_keys: keys
  end;

(* proof_of *)
fun proof_of (graph:abduction_graph) (key:key) =
  let
    val maybe_proof = PGraph.get_node graph key |> Abduction_Node.proof_of: strings option;
  in
    if is_some maybe_proof
    then the maybe_proof
    else error "proof_of failed. No proof yet."
  end;

(* orkeys_tobe_expanded_in *)
fun orkeys_tobe_expanded_in_with_reachable_count
    (ctxt:Proof.context) (graph:abduction_graph): (keys * frontier_counts) =
  let
    val or_keys                        = PGraph.keys graph |> filter is_ornode           : keys;
    val orleaf_keys                    = filter_out (is_branch graph) or_keys            : keys;
    val keys_worth_trying              = filter (is_worth_proving ctxt graph) orleaf_keys: keys;
    val final_goal_key                 = get_final_goal_key graph                        : key;
    val keys_reachable_from_final_goal = PGraph.all_succs graph [final_goal_key]         : keys;
    val reachable_or_keys              = filter is_ornode keys_reachable_from_final_goal : keys;
    val reachable_orleaf_keys          = filter_out (is_branch graph) reachable_or_keys  : keys;
    val reachable_count                = length keys_reachable_from_final_goal           : int;
    val reachable_or_count             = length reachable_or_keys                        : int;
    val reachable_orleaf_count         = length reachable_orleaf_keys                    : int;
    val _                              =
          tracing ("Number of keys_reachable_from_final_goal: " ^ Int.toString reachable_count);
    val _                              =
          tracing ("Number of OR-keys reachable from final goal: "
            ^ Int.toString reachable_or_count);
    (*val _ = map (print_key ctxt) keys_reachable_from_final_goal*)
    val result                         = inter equal_keys keys_worth_trying reachable_orleaf_keys;
  in
    (result,
     {reachable_keys = reachable_count,
      reachable_or_nodes = reachable_or_count,
      reachable_or_leaf_nodes = reachable_orleaf_count})
  end;

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof (graph:abduction_graph) (key:key) =
    Abduction_Node.or2and_edge_to_proof (PGraph.get_node graph key);

(* final_goal_proved_completely *)
fun final_goal_proved_completely (graph:abduction_graph) =
  let
    val final_goal_key    = get_final_goal_key graph                 : key;
    val final_goal_proved = is_proved_completely graph final_goal_key: bool;
  in
    final_goal_proved
  end;

(* prove_term_completely *)
fun prove_term_completely (pst:Proof.state) (lemma_term:term) =
    let
      val pst_to_prove = Top_Down_Util.mk_pst_to_prove_from_term pst lemma_term: Proof.state;
      val timeouts     =
            {overall = 60.0, hammer = 8.5, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
      (*An "instance" or "interpretation" obligation needs intro_classes/unfold_locales before
        Attack_On_Or_Node can make progress on it.*)
      val strategy_name =
            TBC_Utils.strategy_for_goal "Attack_On_Or_Node" (Proof.context_of pst) lemma_term;
      val maybe_result =
            TBC_Utils.pst_to_proofscripts_opt timeouts strategy_name pst_to_prove
            : (strings * Proof.state) option;
      val maybe_script = Option.map fst maybe_result: strings option;
    in
      maybe_script
    end

(* prove_orkey_completely *)
fun prove_orkey_completely
    (or_key as (Or_N:node_type, [lemma_term]):key) (graph:abduction_graph) (pst:Proof.state) =
    let
      fun tracing' m = ();
      val lemma_name   = lemma_name_of graph or_key          : string;
      val maybe_script = prove_term_completely pst lemma_term: strings option;
      val _ =
            tracing' ((if is_some maybe_script then "Proved: " else "Did not prove: ")
              ^ lemma_name ^ " | "
              ^ Isabelle_Utils.trm_to_string (Proof.context_of pst) lemma_term)
    in
      maybe_script
    end
  | prove_orkey_completely _ _ _ = error "try_to_prove_orkey_completely failed!";

(* keys *)
fun keys (ag:abduction_graph) = PGraph.keys ag;

(* goal_as_string *)
fun goal_as_string (ctxt:Proof.context) ((Or_N, [term]):key) =
      Isabelle_Utils.trm_to_string ctxt term
  | goal_as_string (ctxt:Proof.context) ((And_N, terms):key) =
      map (Isabelle_Utils.trm_to_string ctxt) terms |> String.concatWith "\n"
  | goal_as_string _ _ = error "goal_as_string in Proof_Graph.ML failed"

(* print_lemma_and_proof_of_key *)
(* tbc_facts: the graph search ran in a context whose simp set held every non-permutative
 * TBC-preprocessed conjecture (TBC_Utils.assume_term_in_ctxt), so this script's simp-consuming
 * steps may have used any of them without naming them. They are named here, in the method text
 * itself, so the emitted script carries its dependencies - see
 * TBC_Utils.augment_method_with_facts. Falls back to the raw script when it will not parse,
 * exactly as print_have_and_proof_of_key does. *)
fun print_lemma_and_proof_of_key (ctxt:Proof.context) (tbc_facts:strings)
    (graph:abduction_graph) (key:key) =
  let
    val name  = lemma_name_of graph key : string;
    val stmt  = goal_as_string ctxt key : string;
    val proofs= proof_of graph key      : strings;
    val proof =
      case try TBC_Utils.parse_tactic_steps proofs of
        SOME steps =>
          TBC_Utils.proof_steps_to_text (TBC_Utils.augment_steps_with_facts tbc_facts steps)
      | NONE       => space_implode " " proofs;
  in
     "lemma " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ "\n" ^ proof
  end;

(* print_have_and_proof_of_key *)
(* Like print_lemma_and_proof_of_key, but with a "have" header instead of "lemma": for
 * suggesting an auxiliary fact that nests inside an already-open structured proof (a
 * "proof - ... qed" block wrapped around an in-progress goal) instead of as a fresh top-level
 * lemma, which is illegal syntax while a proof is open (suggest/solve).
 * Every free variable mentioned in the statement is listed in an explicit "for" clause, for
 * the same reason and by the same mechanism as TBC_Utils.print_conjecture_w_have - see there
 * for why this is required (not cosmetic) for a nested "have" to behave as a genuinely general
 * fact instead of one about one fixed, arbitrary value. *)
(* offset renumbers this node's variables above every earlier node's, so an assembled suggestion
 * has no two unrelated var_0s - the same renaming the replay applies, from the same function, so
 * the printed block and the applied one cannot disagree. See Top_Down_Util.offset_vnames. *)
fun print_have_and_proof_of_key (ctxt:Proof.context) (tbc_facts:strings)
    (graph:abduction_graph) (offset:int) (key:key) =
  let
    val name  = lemma_name_of graph key : string;
    val stmt0 = (case key of (Or_N, [trm]) => trm
                  | _ => error "print_have_and_proof_of_key: expected a single-term Or-node");
    val (stmt_term, renaming) = Top_Down_Util.offset_vnames offset stmt0;
    val stmt  = Isabelle_Utils.trm_to_string ctxt stmt_term: string;
    val proofs= proof_of graph key |> map (TBC_Utils.rename_vars_in_script renaming): strings;
    (* Rendered from the same proof_step list the replay applies (apply_have_of_key parses this
       very script), so a printed suggestion and an applied proof cannot describe different
       proofs. Falls back to joining the raw script when it will not parse: the replay would fail
       on such a script anyway, and printing something the reader can still inspect beats turning
       a partly-useful suggestion into an error.
       tbc_facts as in print_lemma_and_proof_of_key: the search context held these as simp
       rules, so the script's simp-consuming steps name them on the way out. *)
    val proof =
      case try TBC_Utils.parse_tactic_steps proofs of
        SOME steps =>
          TBC_Utils.proof_steps_to_text (TBC_Utils.augment_steps_with_facts tbc_facts steps)
      | NONE       => space_implode " " proofs;
    (* From the RENAMED term, so this clause is the same list apply_have_of_key fixes - see
       TBC_Utils.fixes_for_have for what went wrong when the two were computed separately, and
       note that reading it off the original term would reintroduce exactly that: a "for var_0"
       above a statement that now says var_2. *)
    val for_clause = TBC_Utils.for_clause_of ctxt stmt_term;
  in
     "have " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ for_clause ^ "\n" ^ proof
  end;

(* print_proof_of_key_only *)
(* Like print_lemma_and_proof_of_key, but without the "lemma name: stmt" header - just the
 * bare tactic script. Used for the root goal when the suggested script is meant to be pasted
 * as the continuation of an already-open proof (suggest/solve) rather
 * than as a fresh top-level lemma: the goal is already stated at that point, so restating it
 * would be wrong. *)
fun print_proof_of_key_only (graph:abduction_graph) (key:key) =
    proof_of graph key |> space_implode " ": string;

(* print_proof_of_graph *)
fun print_proof_of_graph (pst:Proof.state) (graph:abduction_graph) =
  let
    val keys             = keys graph |> filter is_ornode |> rev: keys;
    val key_prf_id_pairs =
          map (fn key => (key, proof_id_of graph key)) keys: (key * int option) list;
    val key_prf_id_pairs_solved_only =
          filter (fn (_, id) => is_some id) key_prf_id_pairs: (key * int option) list;
    val key_prf_id_pairs_wo_opt = map (apsnd the) key_prf_id_pairs_solved_only: (key * int) list;
    val key_of_original_goal    = get_final_goal_key graph: key;
    val prf_id_of_original_goal =
          proof_id_of graph key_of_original_goal
          |> Utils.the' "print_proof_of_graph faild.": int;
    val relevant_key_prf_id_pairs =
          filter (fn (_, prf_id) => prf_id <= prf_id_of_original_goal) key_prf_id_pairs_wo_opt
          : (key * int) list;
    fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2): order;
    val sorted_keys  = sort compare relevant_key_prf_id_pairs |> map fst: key list;
    (*No TBC fact names reach this dead path - see the sig's "no longer used" note.*)
    fun print_key key = print_lemma_and_proof_of_key (Proof.context_of pst) [] graph key;
    val final_script = "\n" ^ (map print_key sorted_keys |> String.concatWith "\n");
    (*TODO: Do not show the proofs of or-nodes proved after we prove the original goal.*)
    val _ = Active.sendback_markup_properties [Markup.padding_command] final_script |> tracing;
    (* Traced only, until now. This is the path prove_by_abduction takes when it prints the whole
       graph proof, and it never reached emit_proof_script - so goals proved this way were
       reported as successes and their proofs discarded. Measured: two of five. *)
    val _ = Top_Down_Util.write_proof_to_file (Proof.context_of pst) final_script;
  in
    ()
  end;

end;