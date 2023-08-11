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

val proof_by_abduction: Proof.state -> term -> unit;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type state = Proof.state;

open Abduction_Graph;

structure SOOE = Seed_Of_Or2And_Edge;
structure SS   = Shared_State;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_or2and_edge  = SOOE.seed_of_or2and_edge;
type seeds_of_or2and_edge = SOOE.seeds_of_or2and_edge;

(* expand_ornode *)
fun expand_ornode_if_original_goral_is_unproved
  (pst:state, synched_agraph: SS.synched_abduction_graph, refutation:SS.synched_term2bool_table, term2name:SS.synched_term2string_table)
  (or_key as (Or_N, [lemma_term]):key): bool =
    let
       fun tracing' mssg = ()(*tracing mssg*);
       val _ = tracing' "Start computing expand_ornode"
       (*very expensive*)
       val graph        = Synchronized.value synched_agraph      : abduction_graph;
       val maybe_proved = prove_orkey_completely or_key graph pst: (state * strings) option;
       val _ = tracing' "Finished computing expand_ornode"
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing' "We PROVED the or-node.";
          val _ = tracing' (Isabelle_Utils.trm_to_string (Proof.context_of pst) lemma_term);
          val (_, proof) = the maybe_proved: (state * strings);
          val _ = SS.update_after_proving_ornode proof or_key (Proof.context_of pst) synched_agraph
        in
           SS.final_goal_proved_completely synched_agraph
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val _ = tracing' "We did NOT prove the or-node.";
          (*top-down explicit conjecturing*)
          val explicit_conjectures        = All_Top_Down_Conjecturing.top_down_conjectures term2name pst lemma_term                                          : (string * term) list;
          val filtered_explicit           = filter_out (SOOE.condition_to_filter_out_cnjctr lemma_term refutation pst graph false o snd) explicit_conjectures: (string * term) list;
          val explicit_wo_counterexample  = filter_out (Shared_State.is_refuted refutation pst o snd) filtered_explicit                                      : (string * term) list;
          val seed_from_explicit          = SOOE.conjectures_to_seed_of_or2and_edge term2name pst explicit_wo_counterexample                                 : seed_of_or2and_edge;
          val _                           = SOOE.decremental_abduction pst or_key seed_from_explicit term2name synched_agraph                                : unit;
          (*tactic application as conjecturing. A little expensive*)
          val pst_to_prove                = mk_pst_to_prove_from_orkey pst or_key                                                                            : state;
          val seeds_from_tactics          = SOOE.apply_PSL_to_get_seeds_of_or2and_edges term2name pst_to_prove                                               : seeds_of_or2and_edge;
          val graph_extended_by_cnjctr    = Synchronized.value synched_agraph                                                                                : abduction_graph;
          val filtered_seeds_from_tactics = SOOE.filter_out_bad_seeds_from_tactic lemma_term refutation pst graph_extended_by_cnjctr seeds_from_tactics
                                         |> filter_out (SOOE.seed_has_counterexample refutation pst)                                                         : seeds_of_or2and_edge;
          val _                           = SOOE.seeds_to_updated_graph pst or_key filtered_seeds_from_tactics synched_agraph                                : unit;
        in
          (*seeds_to_updated_graph is very expensive*)
          SS.final_goal_proved_completely synched_agraph
        end
    end
  | expand_ornode_if_original_goral_is_unproved _ _ = error "expand_ornode failed. Not an Or_N.";

(* loop *)
fun loop (counter:int) (max_depth:int) (pst:state, synched_agraph: SS.synched_abduction_graph, refutation:SS.synched_term2bool_table, term2name:SS.synched_term2string_table) =
    if counter < 8
    then
      let
        val _                      = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                   = Proof.context_of pst;
        val abduction_graph        = Synchronized.value synched_agraph: Abduction_Graph.abduction_graph;
        val orkeys_worth_expanding = orkeys_tobe_expanded_in ctxt abduction_graph: keys;
        val _                      = tracing ("The number of keys worth expanding is:" ^ Int.toString (length orkeys_worth_expanding));
        val _                      = tracing "They are:"
        val _                      = map (tracing o Shared_State.get_orkey_name term2name ctxt) orkeys_worth_expanding;
        val _                      = map (print_key ctxt) orkeys_worth_expanding
        val some_orkey             = Par_List.find_some (expand_ornode_if_original_goral_is_unproved (pst, synched_agraph, refutation, term2name)) orkeys_worth_expanding: key option;
        val solved                 = is_some some_orkey: bool;
        val _                      = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
      in
        (if solved then pst else loop (counter + 1) max_depth (pst, synched_agraph, refutation, term2name))
      end
    else
      pst;

(*TODO*)
fun print_proof_of_graph' (pst:Proof.state) (ag:abduction_graph) (name2term:SS.string2term_table)
      (already_printed_lemmas:strings) (results:strings) (lemma_tobe_printed::lemmas_tobe_printeds:strings) =
    let
      val lemma_term_opt = Symtab.lookup name2term lemma_tobe_printed: term option;
    in
      if is_none lemma_term_opt orelse member (op =) already_printed_lemmas lemma_tobe_printed
      then
        [(*TODO*)]
      else
        let
          val lemma_term = the lemma_term_opt;
          val orkey = (Abduction_Graph.Or_N, [lemma_term]): Abduction_Graph.key;
          val proof = Abduction_Graph.proof_of ag orkey |> String.concatWith " ": string;
          val thy   = Proof.theory_of pst: theory;
          val used_lemma_names = Top_Down_Util.get_lemma_names_from_sh_output thy proof: strings;
          val ctxt  = Proof.context_of pst: Proof.context;
          val remaining_lemmas = (lemmas_tobe_printeds @ used_lemma_names)
                              |> remove (op =) lemma_tobe_printed;
          val new_result  = Abduction_Graph.print_lemma_and_proof_of_key ctxt ag orkey: string;
          val new_results = new_result :: results: strings
        in
          print_proof_of_graph' pst ag name2term (lemma_tobe_printed::already_printed_lemmas) remaining_lemmas new_results: strings
        end
    end
 | print_proof_of_graph' _ _ _ _ results [] = results

(* proof_by_abduction *)
fun proof_by_abduction (pst:Proof.state) (term:term) =
    let
      val max_depth                = 5;
      val standardized_term        = Top_Down_Util.standardize_vnames term;
      val ctxt                     = Proof.context_of pst;
      val synched_agraph           = SS.mk_synched_abduction_graph ctxt standardized_term: SS.synched_abduction_graph;
      val synched_refutation_table = Shared_State.mk_term2bool_table ();
      val synched_lemma_name_table = Shared_State.mk_term2string_table ();
      (*TODO: make name2term table. update it whenever I prove an or-node.*)
      val final_pst                = loop 0 max_depth (pst, synched_agraph, synched_refutation_table, synched_lemma_name_table);
      val final_graph              = Synchronized.value synched_agraph: Abduction_Graph.abduction_graph;
    in
      print_proof_of_graph final_pst final_graph
    end;

end;