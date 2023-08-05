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
val loop              : int -> int -> (state * abduction_graph) -> (state * abduction_graph);(*TODO: No need to expose?*)
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
       fun tracing' mssg = ()(*tracing mssg*);
       val _ = tracing' "Start computing expand_ornode"
       (*very expensive*)
       val maybe_proved = prove_orkey_completely or_key graph pst: (state * strings) option;
       val _ = tracing' "Finished computing expand_ornode"
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing' "We PROVED the or-node.";
          val _= tracing' (Isabelle_Utils.trm_to_string (Proof.context_of pst) lemma_term);
          val _ = tracing' "\n"
          val (_, proof) = the maybe_proved: (state * strings);
        in
           (pst, update_after_proving_ornode proof or_key (Proof.context_of pst) graph)
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val _ = tracing' "We did NOT prove the or-node.";
          (*top-down explicit conjecturing*)
          val explicit_conjectures        = All_Top_Down_Conjecturing.top_down_conjectures pst lemma_term                                         : (string * term) list;
(*
 val _ = tracing "\n\n++ explicit_conjectures ++ ";
 val _ = map snd explicit_conjectures |> map (tracing o Isabelle_Utils.trm_to_string (Proof.context_of pst));
*)
          val filtered_explicit           = filter_out (SOOE.condition_to_filter_out_cnjctr lemma_term pst graph false o snd) explicit_conjectures: (string * term) list;
(*
val _ = tracing "\n\n++ filtered_explicit ++ ";
val _ = map snd filtered_explicit |> map (tracing o Isabelle_Utils.trm_to_string (Proof.context_of pst));
*)
          val explicit_wo_counterexample  = filter_out (Shared_State.is_refuted pst o snd) filtered_explicit                                      : (string * term) list;
(*
val _ = tracing "\n\n++ explicit_wo_counterexample ++ ";
val _ = map snd explicit_wo_counterexample |> map (tracing o Isabelle_Utils.trm_to_string (Proof.context_of pst));
*)
          val seed_from_explicit          = (*TODO: At the moment, we throw away the hints for top-down auxiliary lemma names, since incorporating this information requires changing the type of andnode.*)
                                            SOOE.conjectures_to_seed_of_or2and_edge pst explicit_wo_counterexample                : seed_of_or2and_edge;
          val _ = tracing' "AAAAAAAAAAAAAAAAAAAAAA seed_from_explicit finished:"
          val graph_extended_by_cnjctr    = SOOE.decremental_abduction pst or_key seed_from_explicit graph                                        : abduction_graph;
          (*tactic application as conjecturing.  a little expensive*)
          val pst_to_prove                = mk_pst_to_prove_from_orkey pst or_key                                       : state;
          val seeds_from_tactics          = SOOE.apply_PSL_to_get_seeds_of_or2and_edges pst_to_prove                                        : seeds_of_or2and_edge;
          val _ = tracing' "\n AAAAAAAAAAAAAAAAAAAAAA The length of seeds_from_tactics:\n seeds are:"
          (*val _ = map (Seed_Of_Or2And_Edge.print_seed_of_or2and_edge ctxt) seeds_from_tactics*)
          val _ = tracing' (Int.toString (length seeds_from_tactics))
          val filtered_seeds_from_tactics = SOOE.filter_out_bad_seeds_from_tactic lemma_term pst graph_extended_by_cnjctr seeds_from_tactics
              |> (fn x => (tracing' (Int.toString (length x)); x))
              |> filter_out (SOOE.seed_has_counterexample pst)                                                   : seeds_of_or2and_edge;
          val _ = tracing' "AAAAAAAAAAAAAAAAAAAAAA The length of filtered_seeds_from_tactics:"
          val _ = tracing' (Int.toString (length filtered_seeds_from_tactics))
          val graph_extended_by_tactics = SOOE.seeds_to_updated_graph pst or_key filtered_seeds_from_tactics graph_extended_by_cnjctr       : abduction_graph;
          val _ = tracing' "AAAAAAAAAAAAAAAAAAAAAA graph_extended_by_tactics finished:"
        in
          (*seeds_to_updated_graph is very expensive*)
          (pst, graph_extended_by_tactics(*expanded_graph*))
        end
    end
  | expand_ornode _ _ = error "expand_ornode failed. Not an Or_N.";

fun expand_ornode_if_original_goral_is_unproved (or_key:key) (pst, graph) =
  if   final_goal_proved_completely graph
  then (pst, graph)
  else expand_ornode or_key (pst, graph)

(* loop *)
fun loop (counter:int) (max_depth:int) (pst:state, graph: abduction_graph) =
    if counter < 8
    then
      let
        val _                                = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                             = Proof.context_of pst;

        val orkeys_worth_expanding           = orkeys_tobe_expanded_in ctxt graph: keys;
(*
        val orkeys_worth_expanding           = Abduction_Tree_Proved.ornode_keys_that_need_proof ctxt max_depth graph: keys;
*)
        val _                                = tracing ("The number of keys worth expanding is:" ^ Int.toString (length orkeys_worth_expanding));
        val _                                = tracing "They are:"
        val _                                = map (tracing o Shared_State.get_orkey_name ctxt) orkeys_worth_expanding;
        val _                                = map (print_key ctxt) orkeys_worth_expanding
        val (new_pst, graph_w_keys_expanded) = fold expand_ornode_if_original_goral_is_unproved orkeys_worth_expanding (pst, graph): (state * abduction_graph);

        val solved                           = final_goal_proved_completely graph_w_keys_expanded: bool;
(*
        val _ = tracing "VV before calling Abduction_Tree_Proved.graph_is_proved graph_w_keys_expanded:"
        val solved                           = Abduction_Tree_Proved.graph_is_proved (Proof.context_of pst) graph_w_keys_expanded: bool;
*)
        val _                                = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
      in
        (if solved then K (K I) else loop) (counter + 1) max_depth ((*new_*)pst, graph_w_keys_expanded)
      end
    else
      (pst, graph);

(* proof_by_abduction *)
fun proof_by_abduction (pst:state) (term:(*normal*)term) =
    let
      val max_depth                = 5;
      val standardized_term        = Top_Down_Util.standardize_vnames term;
      val initial_graph            = mk_initial_graph standardized_term;
      val (final_pst, final_graph) = loop 0 max_depth (pst, initial_graph);
    in
      print_proof_of_graph final_pst final_graph
(*
      Abduction_Tree_Proved.print_proof_script final_pst max_depth final_graph
*)
    end;

end;