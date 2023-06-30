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

val expand_ornode     : key -> (state * abduction_graph) -> (state * abduction_graph);(*TODO: No need to expose?*)
val loop              : int -> (state * abduction_graph) -> (state * abduction_graph);(*TODO: No need to expose?*)
val proof_by_abduction: state -> term -> unit;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type state = Proof.state;

open Abduction_Graph;
open Update_Abduction_Graph;

structure SOOE = Seed_Of_Or2And_Edge;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_or2and_edge  = SOOE.seed_of_or2and_edge;
type seeds_of_or2and_edge = SOOE.seeds_of_or2and_edge;

(* expand_ornode *)
fun expand_ornode (or_key as (Or_N, [lemma_term]):key) (pst:state, graph:abduction_graph): state * abduction_graph =
    (*TODO: we should check if the node is still worth proving.*)
    let
       val _ = tracing "Start computing expand_ornode"
       (*very expensive*)
       val maybe_proved = prove_orkey_completely or_key graph pst: (state * string) option;
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing "We PROVED the or-node.";
          val (pst_w_proved_lemma, proof) = the maybe_proved: (state * string);
        in
           (pst_w_proved_lemma, update_after_proving_ornode proof or_key (Proof.context_of pst) graph)(*TODO: We are actually not taking advantage of pst_w_proved_lemma. pst seems good enough.*)
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val _ = tracing "We did NOT prove the or-node.";
          val pst_to_prove            = mk_pst_to_prove_from_key pst or_key                                    : state;
          (*tactic application as conjecturing.  a little expensive*)
          val seeds_from_tactics      = SOOE.apply_PSL_to_get_seeds_of_or2and_edges pst_to_prove               : seeds_of_or2and_edge;
          (*top-down explicit conjecturing*)
          val top_down_conjectures    = All_Top_Down_Conjecturing.top_down_conjectures (Proof.context_of pst) lemma_term: (string * term) list;
          val seeds_from_conjectures  = (*TODO: At the moment, we throw away the hints for top-down auxiliary lemma names, since incorporating this information requires changing the type of andnode.*)
                                        SOOE.conjectures_to_seeds_of_or2and_edge (pst, pst_to_prove) top_down_conjectures : seeds_of_or2and_edge;
          val all_seeds               = seeds_from_conjectures @ seeds_from_tactics                            : seeds_of_or2and_edge;
          val filtered_seeds          = SOOE.filter_out_bad_seeds_of_or2and_edge lemma_term pst graph all_seeds: seeds_of_or2and_edge;
          val seeds_wo_counterexample = filter_out (SOOE.seed_has_counterexample pst) filtered_seeds           : seeds_of_or2and_edge;
(*
          val expanded_graph          = SOOE.seeds_to_updated_graph or_key seeds_wo_counterexample graph       : abduction_graph;
*)
          val good_seeds_from_tactics = filter SOOE.seed_is_from_tactic seeds_wo_counterexample                : seeds_of_or2and_edge;
          val graph_extended_by_tactics = SOOE.seeds_to_updated_graph or_key good_seeds_from_tactics graph                   : abduction_graph;
          val good_seeds_from_cnjctr    = filter_out SOOE.seed_is_from_tactic seeds_wo_counterexample                        : seeds_of_or2and_edge;
          val graph_extended_by_cnjctr  = SOOE.seeds_to_updated_graph or_key good_seeds_from_cnjctr graph_extended_by_tactics: abduction_graph;

        in
          (*seeds_to_updated_graph is very expensive*)
          (pst, graph_extended_by_cnjctr(*expanded_graph*))
        end
    end
  | expand_ornode _ _ = error "expand_ornode failed. Not an Or_N.";

fun expand_ornode_if_original_goral_is_unproved (or_key:key) (pst, graph) =
  if   final_goal_proved_completely graph
  then (pst, graph)
  else expand_ornode or_key (pst, graph)

(* loop *)
fun loop (counter:int) (pst:state, graph: abduction_graph) =
    if counter < 8
    then
      let
        val _                                = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                             = Proof.context_of pst;
        val orkeys_worth_expanding           = orkeys_tobe_expanded_in ctxt graph: keys;
        val _                                = tracing ("The number of keys worth expanding is:" ^ Int.toString (length orkeys_worth_expanding));
        val _                                = tracing "They are:"
        val _                                = map (print_key ctxt) orkeys_worth_expanding
        val (new_pst, graph_w_keys_expanded) = fold expand_ornode_if_original_goral_is_unproved orkeys_worth_expanding (pst, graph): (state * abduction_graph);
        val solved                           = final_goal_proved_completely graph_w_keys_expanded: bool;
        val _                                = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
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