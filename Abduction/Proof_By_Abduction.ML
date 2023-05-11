(*
 * Proof_By_Abduction.ML 
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** PROOF_BY_ABDUCTION ***)
signature PROOF_BY_ABDUCTION =
sig

type proof_graph;
type key;
type andnode;
type proof_node;
type state;

val work_on_andnode      : state -> key -> proof_graph -> proof_graph;
val work_on_ornode       : key -> (state * proof_graph) -> (state * proof_graph);
val print_proof_of_graph : state -> proof_graph -> unit;
val loop                 : int -> (state * proof_graph) -> (state * proof_graph);
val top_down_conjecturing: state -> term -> unit;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type proof_graph                     = Proof_Graph.proof_graph;
type key                             = Proof_Graph.key;
type keys                            = Proof_Graph.keys;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type andnode                         = And_Node.andnode;
type proof_node                      = Proof_Graph_Node.proof_node;
type state                           = Proof.state;

open Proof_Graph;
open Proof_Graph_Util;

structure PBAU = Proof_By_Abduction_Util;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_andnode  = PBAU.seed_of_andnode;
type seeds_of_andnode = seed_of_andnode list;



fun print_lemma_and_proof_of_key (graph:proof_graph) (pst:state) (key:key) =
    let
      val name  = lemma_name_of graph key : string;
      val stmt  = goal_as_string pst key  : string;
      val proof = proof_of graph key      : string;
    in
       "lemma " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ "\n" ^ proof
    end;

(* work_on_andnode *)
fun work_on_andnode (pst:state) (and_key as (And_N, subgoals):key) (graph:proof_graph) =
    let
(*
      val _ = tracing "Start work_on_andnode"
*)
      val pairs_to_mk_ornodes             = map (mk_ornode false) subgoals                                   : (key * proof_node) list;
      val (new_or_keys, graph_w_ornodes)  = add_ornodes (Proof.context_of pst) pairs_to_mk_ornodes graph     : keys * proof_graph;
      (*TODO: remove code-duplication of try_to_refute_key*)
      fun try_to_refute_key (state:Proof.state) (key:key) =
          (key, exists (fn trm => TBC_Utils.term_has_counterexample_in_pst trm state) (snd key))             : (key * bool)
      val pairs                           = Par_List.map (try_to_refute_key pst) new_or_keys                 : (key * bool) list;
      val graph_w_quickchecked_ornodes    = fold (PBAU.find_counterexample_update' pst) pairs graph_w_ornodes: proof_graph;
      val graph_w_edges                   = add_edges_from_andnodes_to_ornodes [and_key] graph_w_quickchecked_ornodes: proof_graph;
    in
      graph_w_edges
    end
  | work_on_andnode _ _ _ = error "work_on_andnode failed! Not an And_N key!";

fun seeds_to_updated_graph (or_key:key) (seeds: seeds_of_andnode) (pst:Proof.state) (graph:proof_graph): proof_graph =
  let
    val pairs_to_mk_andnodes                 = map (fn {andnode_key, value,...} => (andnode_key, value)) seeds                      : (key * proof_node) list;
    val graph_w_ornode_is_now_branch         = update_branch or_key graph                                                           : proof_graph;
    val (new_andnds_keys, graph_w_andnodes)  = add_andnodes (Proof.context_of pst) pairs_to_mk_andnodes graph_w_ornode_is_now_branch: (keys * proof_graph);

    val graph_w_ornodes                      = fold (work_on_andnode pst) new_andnds_keys graph_w_andnodes                          : proof_graph;

    fun one_of_ands_child_nodes_is_refuted (and_key:key) (graph:proof_graph) =
      let
        val child_ors    = PGraph.immediate_succs graph and_key: keys;
        val is_refuted   = exists (Proof_Graph.is_refuted graph) child_ors: bool;
        val result_graph = if is_refuted
                           then PGraph.map_node and_key Proof_Graph_Node_Util.update_refuted graph
                           else graph;
      in
        result_graph:proof_graph
      end;

    val graph_w_refuted_andnodes = fold one_of_ands_child_nodes_is_refuted new_andnds_keys graph_w_ornodes: proof_graph;

                                 (*fold one_of_ands_child_nodes_is_refuted new_andnds_keys graph_w_ornodes : proof_graph;*)

    fun seed_is_refuted ({andnode_key,...}:seed_of_andnode) = Proof_Graph.is_refuted graph_w_refuted_andnodes andnode_key: bool;
    val seeds_not_refuted_yet                = filter_out seed_is_refuted seeds: seeds_of_andnode;
    val seeds_of_newly_added_andnodes        = filter (fn seed => member equal_keys new_andnds_keys (#andnode_key seed)) seeds_not_refuted_yet: seeds_of_andnode;
    val graph_w_ornodes_n_or2add_edges       = fold (PBAU.add_or2and_edge or_key) seeds_of_newly_added_andnodes graph_w_ornodes               : proof_graph;
  in
    graph_w_ornodes_n_or2add_edges: Proof_Graph_Util.proof_graph
  end;

(* work_on_ornode *)
fun work_on_ornode (or_key as (Or_N, [lemma_term]):key) (pst:state, graph:proof_graph): state * Proof_Graph_Util.proof_graph =
    (*TODO: we should check if the node is still worth proving.*)
    let
       val _ = tracing "Start computing work_on_ornode"
       val maybe_proved = PBAU.prove_orkey_completely or_key graph pst: (state * string) option;
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing "We PROVED the work_on_ornode"
          val (pst_w_proved_lemma, proof) = the maybe_proved: (state * string);

          (*Important tricky part! TODO: make these as one function.*)
          val updated1      = graph    |> update_proof_n_proof_id proof or_key
          val updated2      = updated1 |> update_proved_completely_of_graph_because_orleaf_is_proved (Proof.context_of pst) or_key
          val updated_graph = updated2 |> update_gg_parent_not_finished_in_proof_graph;
        in
           (pst_w_proved_lemma, updated_graph)(*TODO: We are actually not taking advantage of pst_w_proved_lemma. pst seems good enough.*)
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val pst_to_prove       = PBAU.mk_pst_to_prove_from_key pst or_key                           : state;
          val seeds_from_tactics = PBAU.apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes pst_to_prove: seeds_of_andnode;

          (*conjecturing*)
          val seeds_from_conjectures = All_Top_Down_Conjecturing.top_down_conjectures (Proof.context_of pst) lemma_term
                                    |> map snd (*TODO: At the moment, we throw away the hints for top-down auxiliary lemma names, since incorporating this information requires changing the type of andnode.*)
                                    |> PBAU.conjectures_to_seeds_of_andnode (pst, pst_to_prove): seeds_of_andnode;
          val filtered_seeds = PBAU.filter_out_bad_seeds_of_andnode lemma_term pst graph (seeds_from_conjectures @ seeds_from_tactics): seeds_of_andnode;
(*
val _ = tracing "PRINT FILTERED SEEDS OF AND-NODES"
val _ = map (Proof_By_Abduction_Util.print_seed_of_andnode ctxt) filtered_seeds
*)
        in
          (pst, seeds_to_updated_graph or_key filtered_seeds pst graph)
        end
    end
  | work_on_ornode _ _ = error "work_on_ornode failed. Not an Or_N.";     

fun work_on_ornode_if_original_goral_is_unproved (or_key:key) (pst, graph) =
  if final_goal_proved_completely graph
  then (pst, graph)
  else work_on_ornode or_key (pst, graph)

(* print_proof_of_graph *)
(*topological sort is not good enough due to our use of state.*)
fun print_proof_of_graph (pst:state) (graph:proof_graph) =
    let
      val keys                         = PGraph.keys graph |> filter is_ornode |> rev: keys;
      val key_prf_id_pairs             = map (fn key => (key, proof_id_of graph key)) keys: (key * int option) list;
      val key_prf_id_pairs_solved_only = filter (fn (_, id) => is_some id) key_prf_id_pairs: (key * int option) list;
      val key_prf_id_pairs_wo_opt      = map (apsnd the) key_prf_id_pairs_solved_only: (key * int) list;
      fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2): order;                        
      val sorted_keys                  = sort compare key_prf_id_pairs_wo_opt |> map fst: key list;
      val final_script                 = "\n" ^ (map (print_lemma_and_proof_of_key graph pst) sorted_keys |> String.concatWith "\n");
      val _ = Active.sendback_markup_properties [Markup.padding_command] final_script |> tracing;
    in
      ()
    end;

(* loop *)
fun loop (counter:int) (pst:state, graph: proof_graph) =
    if counter < 8
    then
      let
        val _                          = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                       = Proof.context_of pst;
        val keys_worth_expanding       = keys_tobe_expanded_in ctxt graph                     : keys;
        val _ = tracing ("The number of keys worth expanding is:" ^ Int.toString (length keys_worth_expanding));
        val _ = tracing "They are:"
        val _ = map (Proof_Graph.print_key ctxt) keys_worth_expanding
        val (_, graph_w_keys_expanded) = fold work_on_ornode_if_original_goral_is_unproved keys_worth_expanding (pst, graph): (state * proof_graph);
        val solved                     = final_goal_proved_completely graph_w_keys_expanded: bool;
        val _                          = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
      in
        (if solved then K I else loop) (counter + 1) (pst, graph_w_keys_expanded) 
      end
    else
      (pst, graph);

(* top_down_conjecturing *)
fun top_down_conjecturing (pst:state) (term:term) =
    let
      val initial_graph            = mk_initial_graph term;
      val (final_pst, final_graph) = loop 0 (pst, initial_graph);
    in
      print_proof_of_graph final_pst final_graph
    end;

end;