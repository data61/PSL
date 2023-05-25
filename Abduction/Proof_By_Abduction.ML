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

type abduction_graph;
type key;
type state;

val work_on_ornode    : key -> (state * abduction_graph) -> (state * abduction_graph);(*TODO: No need to expose?*)
val loop              : int -> (state * abduction_graph) -> (state * abduction_graph);(*TODO: No need to expose?*)
val proof_by_abduction: state -> term -> unit;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type state = Proof.state;

open Abduction_Graph;
open Update_Abduction_Graph;

structure SOAN = Seed_Of_And_Node;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_andnode  = SOAN.seed_of_andnode;
type seeds_of_andnode = seed_of_andnode list;

fun seed_to_updated_graph (parent_ornd:key) (pst:Proof.state) (seed: seed_of_andnode) (graph:abduction_graph): abduction_graph =
  let
    val pair_to_mk_andnode                  = (#andnode_key seed, #value seed)                                       : (key * abduction_node);
    val graph_w_ornode_is_now_branch        = update_is_branch parent_ornd graph                                     : abduction_graph;
    val ([new_andnd_key], graph_w_andnodes) = add_andnode pair_to_mk_andnode graph_w_ornode_is_now_branch            : (keys * abduction_graph);
    val graph_w_ornodes(*expensive*)        = add_child_ornodes_for_this_andnode pst new_andnd_key graph_w_andnodes  : abduction_graph;
    val graph_w_and2or_edges                = add_edges_from_andnode_to_ornodes new_andnd_key graph_w_ornodes        : abduction_graph;
    val graph_w_ornodes_n_or2add_edges      = SOAN.add_or2and_edge parent_ornd seed graph_w_and2or_edges(*very expensive*): abduction_graph;
    (*If and_nodes are already proved_completely, we should propagate this information to upper nodes.*)
    (*TODO: cut some and2or edges depending on the proof script in or2and edges.*)
    (*TODO: We should not use andkey_to_terms here.
     * some and-terms in the and-node are not used to prove the parent_ornd.
     * We should cut the and2or edges for these and-terms. *)
    val child_ornode_terms                  = andkey_to_terms new_andnd_key                                                 : terms;
    val child_ornode_keys                   = map (fn term => (Or_N, single term)) child_ornode_terms                       : keys;
    val all_child_ornds_are_already_proved  = forall (is_proved_completely graph_w_ornodes_n_or2add_edges) child_ornode_keys: bool;
    val result: abduction_graph             = if   all_child_ornds_are_already_proved
                                              then update_proved_wo_assmng_cnjctr parent_ornd graph_w_ornodes_n_or2add_edges
                                              else graph_w_ornodes_n_or2add_edges;
  in
    result: abduction_graph
  end;

fun seeds_to_updated_graph (parent_ornd:key) (seeds: seeds_of_andnode) (pst:Proof.state) (graph:abduction_graph) =
  fold (seed_to_updated_graph parent_ornd pst) seeds graph: abduction_graph;

(* work_on_ornode *)
fun work_on_ornode (or_key as (Or_N, [lemma_term]):key) (pst:state, graph:abduction_graph): state * abduction_graph =
    (*TODO: we should check if the node is still worth proving.*)
    let
       val _ = tracing "Start computing work_on_ornode"
       (*very expensive*)
       val maybe_proved = prove_orkey_completely or_key graph pst: (state * string) option;
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing "We PROVED the work_on_ornode"
          val (pst_w_proved_lemma, proof) = the maybe_proved: (state * string);
        in
           (pst_w_proved_lemma,  update_after_proving_ornode proof or_key (Proof.context_of pst) graph)(*TODO: We are actually not taking advantage of pst_w_proved_lemma. pst seems good enough.*)
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val pst_to_prove       = mk_pst_to_prove_from_key pst or_key                                : state;
          (*a little expensive*)
          val seeds_from_tactics = SOAN.apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes pst_to_prove: seeds_of_andnode;

          (*conjecturing*)
          val seeds_from_conjectures  = All_Top_Down_Conjecturing.top_down_conjectures (Proof.context_of pst) lemma_term
                                     |> map snd (*TODO: At the moment, we throw away the hints for top-down auxiliary lemma names, since incorporating this information requires changing the type of andnode.*)
                                     |> SOAN.conjectures_to_seeds_of_andnode (pst, pst_to_prove)                           : seeds_of_andnode;
          val all_seeds               = seeds_from_conjectures @ seeds_from_tactics                                        : seeds_of_andnode;
          val filtered_seeds          = SOAN.filter_out_bad_seeds_of_andnode lemma_term pst graph all_seeds                : seeds_of_andnode;
          val seeds_wo_counterexample = filter_out (Seed_Of_And_Node.seed_of_andnode_has_counterexample pst) filtered_seeds: seeds_of_andnode;
        in
          (*seeds_to_updated_graph is very expensive*)
          (pst, seeds_to_updated_graph or_key seeds_wo_counterexample pst graph)
        end
    end
  | work_on_ornode _ _ = error "work_on_ornode failed. Not an Or_N.";     

fun work_on_ornode_if_original_goral_is_unproved (or_key:key) (pst, graph) =
  if   final_goal_proved_completely graph
  then (pst, graph)
  else work_on_ornode or_key (pst, graph)

(* loop *)
fun loop (counter:int) (pst:state, graph: abduction_graph) =
    if counter < 8
    then
      let
        val _                          = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                       = Proof.context_of pst;
        val orkeys_worth_expanding     = orkeys_tobe_expanded_in ctxt graph: keys;
        val _ = tracing ("The number of keys worth expanding is:" ^ Int.toString (length orkeys_worth_expanding));
        val _ = tracing "They are:"
        val _ = map (print_key ctxt) orkeys_worth_expanding
        val (new_pst, graph_w_keys_expanded)      = fold work_on_ornode_if_original_goral_is_unproved orkeys_worth_expanding (pst, graph): (state * abduction_graph);
(*        val graph_w_keys_expanded  = update_gg_parent_not_finished graph_w_keys_expanded                                  : abduction_graph;*)
        val solved                                = final_goal_proved_completely graph_w_keys_expanded: bool;
        val _                                     = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
      in
        (if solved then K I else loop) (counter + 1) (new_pst, graph_w_keys_expanded)
      end
    else
      (pst, graph);

(* proof_by_abduction *)
fun proof_by_abduction (pst:state) (term:(*normal*)term) =
    let
      val standardized_term        = Top_Down_Util.standardize_vnames term;
      val initial_graph            = mk_initial_graph standardized_term;
      val (final_pst, final_graph) = loop 0 (pst, initial_graph);
    in
      print_proof_of_graph final_pst final_graph
    end;

end;