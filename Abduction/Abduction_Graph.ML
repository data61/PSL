(*
 * Abduction_Graph.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
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

val print_key: Proof.context -> key -> unit list;
val equal_keys: (key * key) -> bool;

type abduction_graph;

(* creation of key_val pair *)
type is_final_goal = bool;
val mk_ornode:  is_final_goal -> string -> term -> (key * abduction_node);
val mk_andnode: terms -> (key * abduction_node);

(* key to term *)
val orkey_to_term  : key -> term;
val andkey_to_terms: key -> terms;

(* initialization *)
val mk_initial_graph                              : term -> abduction_graph; (*TODO: Is there any reason to expose this function?*)

(* query on key and graph *)
val is_branch     : abduction_graph -> key -> bool;
val is_ornode     : key -> bool;
val is_andnode    : key -> bool;
val is_or2and_edge: key -> bool;

(* query on abduction_node for ornode and andnode *)
val is_proved_completely                         : abduction_graph -> key -> bool;

(* query on abduction_node for ornode *)
val is_final_goal                                : abduction_graph -> key -> bool;
val lemma_name_of                                : abduction_graph -> key -> string;
val proof_of                                     : abduction_graph -> key -> strings;
val proof_id_of                                  : abduction_graph -> key -> int option;

val grand_parents                                : abduction_graph -> key -> keys;
val grand_children                               : abduction_graph -> key -> keys;
val all_gg_parents_are_proved                    : abduction_graph -> key -> bool;

(* query on abduction_node for or2and_edge *)
val or2and_edge_to_proof                         : abduction_graph -> key -> strings;

val is_worth_proving                             : Proof.context -> abduction_graph -> key -> bool;

(*TODO: it is a little strange that we have proof_of and or2and_edge_to_proof separately.*)
val get_final_goal_term                          : abduction_graph -> term;
val get_leaf_orterms                             : abduction_graph -> terms;
val get_final_goal_key                           : abduction_graph -> key;
val orkeys_tobe_expanded_in                      : Proof.context -> abduction_graph -> keys;

val goal_as_string                               : Proof.state -> key -> string;

(* query on abduction_graph *)
val final_goal_proved_completely                 : abduction_graph -> bool;

val mk_pst_to_prove_from_key                     : Proof.state -> key -> Proof.state;(*TODO: Is it necessary to expose this function?*)
val prove_orkey_completely                       : key -> abduction_graph -> Proof.state -> (Proof.state * strings) option;

val print_lemma_and_proof_of_key                 : Proof.state -> abduction_graph -> key -> string;
val print_proof_of_graph                         : Proof.state -> abduction_graph -> unit;

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

fun mk_ornode (is_final_goal:is_final_goal) (lemma_name:string) (goal:term) =
  let
    val standardized_goal = Top_Down_Util.standardize_vnames goal;
  in
    (
      (Or_N, [standardized_goal]): key,
      Abduction_Node.mk_ornode is_final_goal lemma_name standardized_goal: abduction_node
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
fun mk_initial_graph (goal:term) =
  let
    val root_pair = mk_ornode true "(*we do not need to pass a name for the top goal.*)" goal
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

(* is_proved_completely *)
fun is_proved_completely (graph:abduction_graph) (key:key): bool =
  PGraph.get_node graph key |> Abduction_Node.is_proved_completely;

(* lemma_name_of *)
fun lemma_name_of (graph:abduction_graph) (key:key) =
  PGraph.get_node graph key |> Abduction_Node.lemma_name_of: string;

(* grand_relatives *)
fun grand_relatives (graph:abduction_graph) (key:key) (preds_or_succs: abduction_graph -> key -> key list): keys =
  let
    val immediate_keys = preds_or_succs graph key: keys;
    val grand_keys = map (preds_or_succs graph) immediate_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* grand_parents *)
fun grand_parents (graph:abduction_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_preds;

(* grand_children *)
fun grand_children (graph:abduction_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_succs;

(* great_grand_relatives *)
fun great_grand_relatives (graph:abduction_graph) (key:key) (preds_or_succs: abduction_graph -> key -> key list): keys =
  let
    val grand_relatives_keys = grand_relatives graph key preds_or_succs: keys;
    val grand_keys = map (preds_or_succs graph) grand_relatives_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* great_grand_parents *)
fun great_grand_parents (graph:abduction_graph) (key:key): keys = great_grand_relatives graph key grand_parents;

(* all_gg_parents_are_proved *)
fun all_gg_parents_are_proved (graph:abduction_graph) (key as (Or_N, _)): bool = all_great_grandparents_are_proved_for_or key graph
  | all_gg_parents_are_proved _ _: bool = error "all_great_grandparents_are_proved failed. And_N"
and all_great_grandparents_are_proved_for_or key graph =
  let
    val great_grand_parents_keys  = great_grand_parents graph key: keys;
    val great_grand_parents_nodes = map (PGraph.get_node graph) great_grand_parents_keys: abduction_node list;
  in
   null great_grand_parents_keys orelse forall Abduction_Node.is_proved_completely great_grand_parents_nodes
  end;

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
fun proof_id_of (graph:abduction_graph) (key:key) = PGraph.get_node graph key |> Abduction_Node.proof_id_of: int option;

(* proof_of *)
fun proof_of (graph:abduction_graph) (key:key) =
  let
    val maybe_proof = PGraph.get_node graph key |> Abduction_Node.proof_of: strings option;
  in
    if is_some maybe_proof
    then the maybe_proof
    else error "proof_of failed. No proof yet."
  end;

(* goal_as_string *)
fun goal_as_string (pst:Proof.state) ((Or_N, [term]):key) = Isabelle_Utils.trm_to_string (Proof.context_of pst) term
  | goal_as_string (pst:Proof.state) ((And_N, terms):key) = map (Isabelle_Utils.trm_to_string (Proof.context_of pst)) terms |> String.concatWith "\n"
  | goal_as_string _ _ = error "goal_as_string in Proof_Graph.ML failed"

(* orkeys_tobe_expanded_in *)
fun orkeys_tobe_expanded_in (ctxt:Proof.context) (graph:abduction_graph): keys =
  let
    val or_keys                        = PGraph.keys graph |> filter is_ornode           : keys;
    val orleaf_keys                    = filter_out (is_branch graph) or_keys            : keys
    val keys_worth_trying              = filter (is_worth_proving ctxt graph) orleaf_keys: keys;
    val final_goal_key                 = get_final_goal_key graph                        : key;
    val keys_reachable_from_final_goal = PGraph.all_succs graph [final_goal_key]         : keys;
    val _                              = tracing ("Number of keys_reachable_from_final_goal: " ^ Int.toString (length keys_reachable_from_final_goal));
    (*val _ = map (print_key ctxt) keys_reachable_from_final_goal*)
    val result                         = inter equal_keys keys_worth_trying keys_reachable_from_final_goal;
  in
    result
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

(* mk_pst_to_prove_from_key *)
(*TODO: Don't ignore local assumptions.*)
(*TODO: This function is becoming outdated. Should be removed soon.*)
fun mk_pst_to_prove_from_key (pst:Proof.state) (Or_N, [term]) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key (pst:Proof.state) (And_N, [term]) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key _ _ = error "mk_pst_to_prove_from_key failed!";

(* prove_orkey_completely *)
fun prove_orkey_completely (or_key as (Or_N:node_type, [lemma_term]):key) (graph:abduction_graph) (pst:Proof.state) =
    let
      fun tracing' _ = ();
      val lemma_name            = lemma_name_of graph or_key                                                 : string;
      val _ = tracing' "Before calling mk_pst_to_prove_from_key from prove_orkey_completely"
      val pst_to_prove          = mk_pst_to_prove_from_key pst or_key                                        : Proof.state;
      val timeouts              = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}           : TBC_Utils.timeouts;
      val _ = tracing' "Before calling TBC_Utils.pst_to_proofscripts_opt from prove_orkey_completely"
      val maybe_result          = TBC_Utils.pst_to_proofscripts_opt timeouts "Attack_On_Or_Node" pst_to_prove: (strings * Proof.state) option;
      val _ = tracing' "After calling TBC_Utils.pst_to_proofscripts_opt from prove_orkey_completely"
      val cheated_pst           = TBC_Utils.cheat_lemma_term_in_pst lemma_name lemma_term pst
      fun mk_result (script, _) = Option.map (rpair script) cheated_pst;
      val result                = Option.mapPartial mk_result maybe_result: (Proof.state * strings) option
      val _ = tracing ("\n " ^ (if is_some result then "YEY! Completely proved " else "Mehhhh did NOT proved ") ^ lemma_name ^ " " ^ Isabelle_Utils.trm_to_string (Proof.context_of pst) lemma_term)
    in
      result
    end
  | prove_orkey_completely _ _ _ = error "try_to_prove_orkey_completely failed!";

(* print_lemma_and_proof_of_key *)
fun print_lemma_and_proof_of_key (pst:Proof.state) (graph:abduction_graph) (key:key) =
  let
    val name  = lemma_name_of graph key : string;
    val stmt  = goal_as_string pst key  : string;
    val proofs= proof_of graph key      : strings;
    val proof = space_implode " " proofs: string;
  in
     "lemma " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ "\n" ^ proof
  end;

(* print_proof_of_graph *)
fun print_proof_of_graph (pst:Proof.state) (graph:abduction_graph) =
  let
    val keys                         = PGraph.keys graph |> filter is_ornode |> rev           : keys;
    val key_prf_id_pairs             = map (fn key => (key, proof_id_of graph key)) keys      : (key * int option) list;
    val key_prf_id_pairs_solved_only = filter (fn (_, id) => is_some id) key_prf_id_pairs     : (key * int option) list;
    val key_prf_id_pairs_wo_opt      = map (apsnd the) key_prf_id_pairs_solved_only           : (key * int) list;
    fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2)                                 : order;
    val sorted_keys                  = sort compare key_prf_id_pairs_wo_opt |> map fst        : key list;
    val final_script                 = "\n" ^ (map (print_lemma_and_proof_of_key pst graph) sorted_keys |> String.concatWith "\n");
    val _ = Active.sendback_markup_properties [Markup.padding_command] final_script |> tracing;
  in
    ()
  end;

end;