(*
 * Proof_Graph.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** PROOF_GRAPH ***)
signature PROOF_GRAPH =
sig

(** proof_graph **)
(* key, PGraph_Key, and PGraph *)
datatype node_type = Or_N | And_N | O2A_E of int;
val node_type_compare: (node_type * node_type) -> order;

structure PGraph: GRAPH

type proof_node;

type key;
type keys;

val  print_key: Proof.context -> key -> unit list;
val  equal_keys: (key * key) -> bool;

type proof_graph;

(* creation of key_val pair *)
type is_final_goal = bool;
val mk_ornode:  is_final_goal -> term -> (key * proof_node);
val mk_andnode: terms -> (key * proof_node);

(* initialization *)
val mk_initial_graph                              : term -> proof_graph;

(* query on key and graph *)
val is_branch     : proof_graph -> key -> bool;
val is_ornode     : key -> bool;
val is_andnode    : key -> bool;
val is_or2and_edge: key -> bool;

(* query on proof_node for ornode and andnode *)
val is_proved_completely                         : proof_graph -> key -> bool;
val is_refuted                                   : proof_graph -> key -> bool;

(* query on proof_node for ornode *)
val is_final_goal                                : proof_graph -> key -> bool;
val lemma_name_of                                : proof_graph -> key -> string;
val proof_of                                     : proof_graph -> key -> string;
val proof_id_of                                  : proof_graph -> key -> int option;

val grand_parents                                : proof_graph -> key -> keys;
val grand_children                               : proof_graph -> key -> keys;
val all_gg_parents_are_proved                    : proof_graph -> key -> bool;

(* query on proof_node for or2and_edge *)
val ornode_proved_assmng_andnodes                : proof_graph -> key -> bool;
val or2and_edge_to_proof                         : proof_graph -> key -> string;

val is_worth_proving                             : Proof.context -> proof_graph -> key -> bool;

(*TODO: it is a little strange that we have proof_of and or2and_edge_to_proof separately.*)
val get_final_goal                               : proof_graph -> key;
val keys_tobe_expanded_in                        : Proof.context -> proof_graph -> keys;

val goal_as_string                               : Proof.state -> key -> string;

(* query on proof_graph *)
val final_goal_proved_completely                 : proof_graph -> bool;

end;

(*** Proof_Graph ***)
structure Proof_Graph: PROOF_GRAPH =
struct

open Proof_Graph_Node_Util;

(** proof_graph **)
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

fun term_compare (trm1, trm2) =
  Term_Ord.term_ord ((standardize_vnames trm1), (standardize_vnames trm2))

(* PGraph_Key *)
structure PGraph_Key =
    struct
      type key = (node_type * terms)
      val  ord = prod_ord node_type_compare (list_ord term_compare)
    end:KEY

(* PGraph *)
structure PGraph = Graph (PGraph_Key): GRAPH;

(* proof_graph *)
type proof_graph = proof_node PGraph.T;

(* key *)
type key  = PGraph.key

fun print_key  (ctxt:Proof.context) ((_, trms): key) =
  (
    tracing "  key is";
    map (fn trm => tracing ("    " ^ Isabelle_Utils.trm_to_string ctxt trm)) trms
  );

(* keys *)
type keys = PGraph.key list;

(* equal_key *)
fun equal_keys key_pair = PGraph_Key.ord key_pair = EQUAL;

(* creation of key_val pair *)
type is_final_goal = bool;

fun mk_ornode (is_final_goal:is_final_goal) (goal:term) =
  (
    (Or_N, [goal]): key,
    Proof_Graph_Node.mk_ornode is_final_goal goal: Proof_Graph_Node.proof_node
   );

fun mk_andnode (goals:terms) =
  (
    (And_N, goals): key,
    Proof_Graph_Node.And_Node {
      subgoals          = goals,
      proved_completely = false,
      refuted           = false
   });

(* mk_initial_graph *)
fun mk_initial_graph (goal:term) =
  let
    val root_pair = mk_ornode true goal: key * Proof_Graph_Node.proof_node;
    val empty_graph = PGraph.empty: proof_graph;
  in
    PGraph.new_node root_pair empty_graph
  end;

(** query on key **)
(* is_branch *)
fun is_branch (graph:proof_graph) (key:key) =
  PGraph.get_node graph key |> Proof_Graph_Node.is_branch: bool;

(* is_ornode *)
fun is_ornode (Or_N, _) = true
  | is_ornode  _        = false;

(* is_andnode *)
fun is_andnode (And_N, _) = true
  | is_andnode  _         = false;

(* is_or2and_edge *)
fun is_or2and_edge (O2A_E _, _) = true
  | is_or2and_edge  _           = false;

(* is_proved_completely *)
fun is_proved_completely (graph:proof_graph) (key:key): bool =
  PGraph.get_node graph key |> Proof_Graph_Node.is_proved_completely;

(* is_refuted *)
fun is_refuted (graph:proof_graph) (key:key): bool =
  PGraph.get_node graph key |> Proof_Graph_Node.is_refuted;

(* lemma_name_of *)
fun lemma_name_of (graph:proof_graph) (key:key) =
  PGraph.get_node graph key |> Proof_Graph_Node.lemma_name_of: string;

(* grand_relatives *)
fun grand_relatives (graph:proof_graph) (key:key) (preds_or_succs: proof_graph -> key -> key list): keys =
  let
    val immediate_keys = preds_or_succs graph key: keys;
    val grand_keys = map (preds_or_succs graph) immediate_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* grand_parents *)
fun grand_parents (graph:proof_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_preds;

(* grand_children *)
fun grand_children (graph:proof_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_succs;

(* great_grand_relatives *)
fun great_grand_relatives (graph:proof_graph) (key:key) (preds_or_succs: proof_graph -> key -> key list): keys =
  let
    val grand_relatives_keys = grand_relatives graph key preds_or_succs: keys;
    val grand_keys = map (preds_or_succs graph) grand_relatives_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* great_grand_parents *)
fun great_grand_parents (graph:proof_graph) (key:key): keys = great_grand_relatives graph key grand_parents;

(* all_gg_parents_are_proved *)
fun all_gg_parents_are_proved (graph:proof_graph) (key as (Or_N, _)): bool = all_great_grandparents_are_proved_for_or key graph
  | all_gg_parents_are_proved _ _: bool = error "all_great_grandparents_are_proved failed. And_N"
and all_great_grandparents_are_proved_for_or key graph =
  let
    val great_grand_parents_keys  = great_grand_parents graph key: keys;
    val great_grand_parents_nodes = map (PGraph.get_node graph) great_grand_parents_keys: proof_node list;
  in
   null great_grand_parents_keys orelse forall Proof_Graph_Node.is_proved_completely great_grand_parents_nodes
  end;

(* is_final_goal *)
fun is_final_goal (graph:proof_graph) (key as (Or_N, _): key): bool =
    PGraph.get_node graph key |> Proof_Graph_Node.is_final_goal
  | is_final_goal _ _ = false;

(* get_final_goal *)
fun get_final_goal (graph:proof_graph) =
  let
    val final_goals = PGraph.keys graph |> filter (is_final_goal graph): keys;
    val final_goal  = if length final_goals = 1
                      then hd final_goals
                      else error "get_final_goal failed. Not exactly one final_goals.";
  in
    final_goal
  end;

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (graph:proof_graph) (key:key)  =
  PGraph.get_node graph key |> Proof_Graph_Node.is_worth_proving ctxt: bool;

(* proof_id_of *)
fun proof_id_of (graph:proof_graph) (key:key) = PGraph.get_node graph key |> Proof_Graph_Node.proof_id_of: int option;

(* proof_of *)
fun proof_of (graph:proof_graph) (key:key) =
  let
    val maybe_proof = PGraph.get_node graph key |> Proof_Graph_Node.proof_of: string option;
  in
    if is_some maybe_proof
    then the maybe_proof
    else error "proof_of failed. No proof yet."
  end;

(* goal_as_string *)
fun goal_as_string (pst:Proof.state) ((Or_N, [term]):key) = Isabelle_Utils.trm_to_string (Proof.context_of pst) term
  | goal_as_string (pst:Proof.state) ((And_N, terms):key) = map (Isabelle_Utils.trm_to_string (Proof.context_of pst)) terms |> String.concatWith "\n"
  | goal_as_string _ _ = error "goal_as_string in Proof_Graph.ML failed"

(* keys_tobe_expanded_in *)
fun keys_tobe_expanded_in (ctxt:Proof.context) (graph:proof_graph): keys =
  let
    val or_keys                        = PGraph.keys graph |> filter is_ornode          : keys;
(*
val _ = tracing ("ALL OR_KEYS: ");
val _ = map (print_key ctxt) or_keys;
*)
    val orleaf_keys                    = filter_out (is_branch graph) or_keys           : keys
(*
val _ = tracing ("ALL orleaf_keys: ");
val _ = map (print_key ctxt) orleaf_keys;
*)
    val keys_worth_trying              = filter (is_worth_proving ctxt graph) orleaf_keys: keys;
(*
val _ = tracing ("ALL keys_worth_trying: ");
val _ = map (print_key ctxt) keys_worth_trying;
*)
    val final_goal_key                 = get_final_goal graph                           : key;
(*
val _ = tracing ("FINAL GOAL IS: ");
val _ =  print_key ctxt final_goal_key;
*)
    val keys_reachable_from_final_goal = PGraph.all_succs graph [final_goal_key]        : keys;
    val _                              = tracing ("Number of keys_reachable_from_final_goal: " ^ Int.toString (length keys_reachable_from_final_goal));
    val _ = map (print_key ctxt) keys_reachable_from_final_goal
    val result = inter equal_keys keys_worth_trying keys_reachable_from_final_goal;
    val _                              = tracing ("Number of keys_reachable_from_final_goal after removing dups: " ^ Int.toString (length result));
    val _ = map (print_key ctxt) result
  in
    result
  end;

(* ornode_proved_assmng_andnodes *)
fun ornode_proved_assmng_andnodes (graph:proof_graph) (key:key) =
    Proof_Graph_Node.ornode_proved_assmng_andnodes (PGraph.get_node graph key);

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof (graph:proof_graph) (key:key) =
    Proof_Graph_Node.or2and_edge_to_proof (PGraph.get_node graph key);

(* final_goal_proved_completely *)
fun final_goal_proved_completely (graph:proof_graph) =
  let
    val final_goal_key    = get_final_goal graph                     : key;
    val final_goal_proved = is_proved_completely graph final_goal_key: bool;
  in
    final_goal_proved
  end;

end;