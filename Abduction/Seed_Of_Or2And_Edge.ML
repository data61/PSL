(*  Title:      Abduction/Seed_Of_Or2And_Edge.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

Computes the seed information used to construct OR-to-AND edges in the abduction graph.
*)
(*** SEED_OF_OR2AND_EDGE ***)
signature SEED_OF_OR2AND_EDGE =
sig

type abduction_graph;
type key;
type conjecture  = (string * term);
type conjectures = conjecture list;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type abduction_node;
type seed_of_or2and_edge =
     {new_goals : (string * term) list,
      proof     : how_to_get_andnodes_from_ornode,
      importance: real};
type seeds_of_or2and_edge;
type add_or2and_edge = (key * abduction_node * conjectures);

val print_seed_of_or2and_edge             : Proof.context -> seed_of_or2and_edge -> unit list;
val seed_is_from_tactic                   : seed_of_or2and_edge -> bool;
val apply_PSL_to_get_seeds_of_or2and_edges:
  (Shared_State.synched_term2string_table * Shared_State.synched_term2real_table) ->
  (*original*)Proof.state -> Proof.state(*to prove*)-> seeds_of_or2and_edge;
val condition_to_filter_out_conjecture:
  Shared_State.synched_filter_statistics -> term -> Shared_State.synched_term2real_table ->
  terms -> Proof.state -> abduction_graph -> bool (*from_tactic*) -> term (*conjecture*) -> bool;
val filter_out_bad_seeds_from_tactic:
  Shared_State.synched_filter_statistics -> term (*parental or-node*) ->
  Shared_State.synched_term2real_table -> terms (*original premises*) -> Proof.state ->
  abduction_graph -> seeds_of_or2and_edge -> seeds_of_or2and_edge
val conjectures_to_seed_of_or2and_edge:
  Shared_State.synched_term2string_table -> Proof.state -> (string * term) list ->
  seed_of_or2and_edge;
val seed_has_counterexample:
  Shared_State.synched_term2real_table -> Proof.state -> seed_of_or2and_edge -> bool;
val abduction_for_tactic_based_conjectures:
  Proof.state -> key -> seeds_of_or2and_edge -> Shared_State.synched_abduction_graph -> unit;
val abduction_for_explicit_conjectures:
  Proof.state -> int -> key -> conjectures ->
  (Shared_State.synched_term2string_table *
   Shared_State.synched_term2real_table *
   Shared_State.synched_abduction_graph *
   Shared_State.synched_proved_simps *
   Shared_State.synched_filter_statistics) -> unit;

end;

(*** Seed_Of_Or2And_Edge ***)
structure Seed_Of_Or2And_Edge: SEED_OF_OR2AND_EDGE =
struct

open Abduction_Graph;
structure UAG  = Update_Abduction_Graph;
structure SS   = Shared_State;
structure TDU  = Top_Down_Util;
structure SFTD = SeLFiE_For_Top_Down;

type conjecture  = (string * term);
type conjectures = (string * term) list;

type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type seed_of_or2and_edge =
     {new_goals : conjectures,
      proof     : how_to_get_andnodes_from_ornode,
      importance: real};

type seeds_of_or2and_edge = seed_of_or2and_edge list;

fun tracing' mssg = tracing mssg;

fun print_seed_of_or2and_edge ctxt ({new_goals,...}: seed_of_or2and_edge) = (
  map (fn goal => tracing' (fst goal ^ " | " ^ Isabelle_Utils.trm_to_string ctxt (snd goal)))
      new_goals
);

fun seed_is_from_tactic ({proof, ...}) = Or2And_Edge.proof_is_from_tactic proof: bool;

(* apply_Extend_Leaf_to_pst_get_records_to_mk_andnodes *)
(* The return type of this function should be seeds_of_or2and_edge because we need the resulting
 * proof states. *)
fun apply_PSL_to_get_seeds_of_or2and_edges
    (name_table: SS.synched_term2string_table,
     refutation: Shared_State.synched_term2real_table) (orig_pst) (pst_to_prove:Proof.state) =
  let
    val orig_ctxt     = Proof.context_of orig_pst;
    val ctxt_to_prove = Proof.context_of pst_to_prove;
    val extend_str    =
      PSL_Interface.lookup ctxt_to_prove "Extend_Leaf" |> the: PSL_Interface.strategy;
    val timeouts      =
      {overall = 60.0, hammer = 9.0, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
    val result_seq    =
      TBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst_to_prove []
      : (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_list   = Seq.list_of result_seq: (Dynamic_Utils.log * Proof.state) list;
    val pairs_n_psts  =
      map (apfst Dynamic_Utils.log_to_script_n_importance) result_list
      : ((strings * real) * Proof.state) list;
    fun mk_proof_key_value ((pscript:strings, importance), pst) =
        let
          val subgs              = Isabelle_Utils.pst_to_subgs pst
          val subgs_wo_meta_uni  = map TDU.strip_outermost_meta_quantifiers subgs: terms;
          val standardized_subgs = map Top_Down_Util.standardize_vnames subgs_wo_meta_uni: terms;
          val standardized_props =
            map (fn term => if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term)
                standardized_subgs
            : terms;
          val mk_lemma_name      =
            SS.get_lemma_name name_table ctxt_to_prove "tactic": term -> string;
          val nonempty_subgs =
            if length subgs = 0 (*orelse not (pass_check_print_read_terms ctxt standardized_props)*)
            then [(mk_lemma_name @{prop "True"}, @{prop "True"})]
            else map mk_lemma_name standardized_props ~~ standardized_props
                 : (string * term) list;
          val nonempty_subgs_terms =
            map snd nonempty_subgs |> map Top_Down_Util.standardize_vnames |> distinct (op =)
            : terms;

          val new_importance =
            importance * SS.refute_any_of_these true refutation orig_pst nonempty_subgs_terms
            : real;
          val result =
                       if length subgs = 0
                          (*orelse not (pass_check_print_read_terms ctxt standardized_props)*)
                       then NONE
                       else SOME {proof      = Or2And_Edge.Tactic pscript,
                                  new_goals  = nonempty_subgs,
                                  importance = new_importance
                                  }: seed_of_or2and_edge option;
        in
          result: seed_of_or2and_edge option
        end;
    val result = List.mapPartial mk_proof_key_value pairs_n_psts: seeds_of_or2and_edge;
  in
    result
  end;

(*TODO: maybe we should add the premises of parent_or to orig_prems after cleaning types and
  free-variable names.*)
fun condition_to_filter_out_conjecture
    (filter_stats:SS.synched_filter_statistics) (parent_or(*parent_or*):term)
    (refutation:SS.synched_term2real_table) (orig_prems:terms) (pst:Proof.state)
    (ag:abduction_graph) (from_tactic:bool) (conjecture:term) =
    let
      val final_goal  = get_final_goal_key ag |> snd |> hd: term;
      val upper_limit = 100.0;(*TODO: magic number*)
      fun concl_is_alpha_eq_to trm imp =
        let
          val cncl = Logic.strip_imp_concl imp |> TDU.remove_Trueprop: term;
        in
          TDU.alpha_eq_over_fvar trm cncl
        end;

      fun too_large _                 = Real.fromInt (Term.size_of_term conjecture) > upper_limit;
      fun eq_to_final_goal _          =
        Top_Down_Util.alpha_eq_over_fvar final_goal conjecture: bool;
      fun concl_is_eq_to_final_goal _ = concl_is_alpha_eq_to final_goal conjecture: bool;
      fun has_func_with_three_occs_in_a_row_even_though_the_parent_does_not_have_those _ =
          not (SFTD.run_assertion pst parent_or SFTD.has_func_with_three_occs_in_a_row)
          andalso
          SFTD.run_assertion pst conjecture SFTD.has_func_with_three_occs_in_a_row;
      fun get_concl (term:term)       = try (snd o Logic.dest_implies) term
                                    <$> Top_Down_Util.standardize_vnames
                                    <$> Isabelle_Utils.strip_atyp
                                      : term option;
      val concl_of_meta_imp_in_parent = get_concl parent_or : term option;
      val concl_of_meta_imp_in_conjec = get_concl conjecture: term option;
      fun concls_are_same _ =
        Utils.mk_option_pair (concl_of_meta_imp_in_parent, concl_of_meta_imp_in_conjec)
        <$> (op =) |> Utils.is_some_true;
      fun concl_of_conj_refuted_even_cncl_of_parent_is_not _ =
          if is_none concl_of_meta_imp_in_parent orelse is_none concl_of_meta_imp_in_conjec
          then false
          else if SS.is_refuted refutation pst (the concl_of_meta_imp_in_parent)
             then false
             else  SS.is_refuted refutation pst (the concl_of_meta_imp_in_conjec);
      fun reject reason =
        (SS.record_orelse_filter_rejection filter_stats reason conjecture; true);
    in
      if too_large ()
      then reject SS.Orelse_Too_Large
      else if eq_to_final_goal () andalso from_tactic
      then reject SS.Orelse_Eq_To_Final_Goal_From_Tactic
      else if concl_is_eq_to_final_goal () (*andalso seed_is_from_tactic seed*)
      then reject SS.Orelse_Concl_Is_Eq_To_Final_Goal
      else if has_func_with_three_occs_in_a_row_even_though_the_parent_does_not_have_those ()
      then reject SS.Orelse_Has_Func_With_Three_Occs_In_A_Row
      else if concls_are_same ()
      then reject SS.Orelse_Concls_Are_Same
      else if concl_of_conj_refuted_even_cncl_of_parent_is_not ()
      then reject SS.Orelse_Concl_Of_Conj_Refuted
      else false
(*
      (*not from_tactic andalso not orig_prem_is_refuted andalso*)
      has_counter_example_in_prems pst conjecture
      (*TODO: This is BAD. We should also check if the conclusions are the same in the
        parent-node and the conjecture.*)
*)
    end;

datatype conjecture_typ = Explicit_Conjecturing | Implicit_Conjecturing (*tactic application*);

fun condition_to_filter_out_seed_from_tactic
    (filter_stats:SS.synched_filter_statistics) (parent_or:term)
    (refutation:SS.synched_term2real_table) (orig_prems:terms) (pst:Proof.state)
    (ag:abduction_graph) (seed:seed_of_or2and_edge): bool =
  let
    val subgoals   = #new_goals seed |> map snd: terms;
    val no_subgoal = null subgoals: bool;
  in
    (*For conjectures from tactics, we do not care if a premise is equivalent to false or not
      for now.*)
    no_subgoal orelse
    exists (condition_to_filter_out_conjecture filter_stats parent_or refutation orig_prems pst ag
              true)
           subgoals
  end;

fun filter_out_bad_seeds_from_tactic
    (filter_stats:SS.synched_filter_statistics) (parent_or:term)
    (refutation:SS.synched_term2real_table) (orig_prems:terms) (pst:Proof.state)
    (graph:abduction_graph) (seeds:seeds_of_or2and_edge) =
  filter_out
    (condition_to_filter_out_seed_from_tactic filter_stats parent_or refutation orig_prems pst
       graph)
    seeds
  : seeds_of_or2and_edge;

fun conjecture_to_seed_of_or2and_edge (conjectures:(string * term) list): seed_of_or2and_edge =
  {new_goals  = conjectures: (string * term) list,
   proof      = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
   importance = 0.95};(*TODO: magic number.*)

fun conjectures_to_seed_of_or2and_edge
    (term2name:SS.synched_term2string_table) (pst:Proof.state)
    (conjectures_w_name: (string * term) list) =
  let
    fun get_ctxt_w_proof_goal trm =
      Proof.context_of (TDU.mk_pst_to_prove_from_term pst trm): Proof.context;
    fun mk_prop term              =
      if TDU.is_prop term then term else HOLogic.mk_Trueprop term: term;
    fun check_prop (trm:term)     =
      try (Syntax.check_prop (get_ctxt_w_proof_goal trm)) trm: term option;
    val conjectures               = map snd conjectures_w_name: terms;
    val conjectures_as_props      = map mk_prop conjectures: terms;
    val checked_conjectures       = List.mapPartial check_prop conjectures_as_props: terms;
    val ctxt                      = Proof.context_of pst: Proof.context;
    fun attach_lemma_name conjctr =
      (SS.get_lemma_name term2name ctxt "" conjctr, conjctr): string * term;
    val name_conjecture_pairs     =
      map attach_lemma_name checked_conjectures: (string * term) list;
    val result                    =
      conjecture_to_seed_of_or2and_edge name_conjecture_pairs: seed_of_or2and_edge;
  in
    result: seed_of_or2and_edge
  end;

fun seed_has_counterexample
    (refutation:SS.synched_term2real_table) (pst:Proof.state)
    ({new_goals,...}:seed_of_or2and_edge) =
  let
    val conjectures = map snd new_goals;
  in
    SS.any_of_these_is_refuted refutation pst conjectures
  end;

fun prove_goal_assuming_conjectures (pst:Proof.state) ((Or_N, [orterm]): key)(*parent node*)
     ({new_goals: (string * term) list,
       proof    : how_to_get_andnodes_from_ornode,...}: seed_of_or2and_edge)(*child nodes*) =
   let
     fun register_thm_in_lthy (name:string) (thm:thm) (lthy:local_theory): local_theory =
         Local_Theory.note ((Binding.name name, []), [thm]) lthy |> snd: local_theory;
     fun assm_conjecture_in_pst (name:string, conjecture:term) (pst:Proof.state) =
       let
         val ctxt                 = Proof.context_of pst: Proof.context;
         val conjecture_as_thm    = TDU.term_to_thm ctxt conjecture: thm;
         val pst_w_conjecture_opt =
           try (Proof.map_context (register_thm_in_lthy name conjecture_as_thm)) pst
           : Proof.state option;
         val pst_w_conjecture     = case pst_w_conjecture_opt of SOME no_dup_pst => no_dup_pst
                                  | _ =>
                                      (tracing ("Warning! We could not assume " ^ name ^
                                                "successfully."); pst)
       in
         pst_w_conjecture
       end;
     val pst_with_new_goals_assmed = fold assm_conjecture_in_pst new_goals pst: Proof.state;
     val pst_to_apply_tactics      =
       TDU.mk_pst_to_prove_from_term pst_with_new_goals_assmed orterm: Proof.state;
     (*apply_proof considers the first result only.*)
     fun apply_proof (proof:string) (pst_tobe_proved:Proof.state) =
     let
       val sh_result = Subtools.tool_output_n_timeout_to_logtac proof NONE 15.0 pst_tobe_proved;
       val result_pst =
         Seq.pull sh_result <$> fst <$> snd
         |> Utils.the' "prove_goal_assuming_conjectures failed.": Proof.state;
     in
       result_pst
     end;
     fun apply_proofs (proofs:strings) (pst_tobe_proved:Proof.state) =
       fold apply_proof proofs pst_tobe_proved: Proof.state;
     val proof_to_get_here = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof: strings;
     val pst_after_applying_how_to_get_andnodes_from_ornode =
       apply_proofs proof_to_get_here pst_to_apply_tactics: Proof.state;
     val timeouts             =
       {overall = 60.0, hammer = 9.0, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
     (*very expensive*)
     val script_opt_gen       =
       TBC_Utils.pst_to_proofscript_opt timeouts
         "Finish_Goal_After_Assuming_Subgoals_And_Conjectures"
         pst_after_applying_how_to_get_andnodes_from_ornode
       <$> fst: string option;
     val proved_parent_or     = is_some script_opt_gen: bool;
   in
     (proved_parent_or, script_opt_gen)
   end
  | prove_goal_assuming_conjectures _ _ _  = error "prove_goal_assuming_conjectures failed badly.";

type add_or2and_edge = ((*edge key*)key * (*edge val*)abduction_node * (*used*)conjectures);

(*step 1. prove the parental or-node using some conjectures.*)
fun prove_ornode_assuming_andnode
     (pst:Proof.state)
     (simp_mode_for_explicit_conjecturing:bool)
     (parent_orkey as (Or_N, [_]): key)(*parent node*)
     (sagraph:SS.synched_abduction_graph)
     (seed_of_or2and_edge as {new_goals, proof, importance}: seed_of_or2and_edge)(*child nodes*)
     : add_or2and_edge option =
   let
     val (proved_parent_or, script_opt_gen) =
       prove_goal_assuming_conjectures pst parent_orkey seed_of_or2and_edge: (bool * string option);
   in
     if proved_parent_or
     then
       let
         val how_we_got_andnode    = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof: strings;
         val script_to_prove_andnd =
           Utils.the' "prove_ornode_assuming_andnode failed." script_opt_gen: string;
         val script_to_prove_ornd  = how_we_got_andnode @ single script_to_prove_andnd: strings;
         val or2and_edge_val       = Abduction_Node.Or_To_And {
                                       how_to_get_andnodes_from_ornode = proof,
                                       proof_of_ornode_assmng_andnodes = script_to_prove_ornd,
                                       importance                      = importance}
                                     : abduction_node;
         val or2and_edge_key       = ((O2A_E (serial())), []): key;
         val thy                   = Proof.theory_of pst: theory;
         val used_conjecture_names =
           TDU.get_lemma_names_from_sh_output thy script_to_prove_andnd: strings;
         val used_new_goals        =
           filter (fn (name, _) => member (op =) used_conjecture_names name) new_goals
           : (string * term) list;
         val relevant_new_goals    =
           if Or2And_Edge.proof_is_from_tactic proof orelse simp_mode_for_explicit_conjecturing
           then new_goals else used_new_goals: conjectures;
       in
         SOME (or2and_edge_key, or2and_edge_val, relevant_new_goals)
       end
     else
        NONE
   end
 | prove_ornode_assuming_andnode _ _ _ _ _ =
     error "how_to_prove_ornode_assmng_subgs_of_andnode failed.";

fun add_nodes_and_edges_to_graph
  (pst:Proof.state) (parent_ornd:key) (synched_agraph:SS.synched_abduction_graph)
  ((edge_key:key, edge_val, used_conjectures): add_or2and_edge): unit =
  let
    val ctxt               = Proof.context_of pst;
    (*step 2.*)
    val _                  = SS.new_node (edge_key, edge_val) synched_agraph: unit;
    (*step 3.*)
    val _                  = SS.add_edge (parent_ornd, edge_key) synched_agraph: unit;
    val and_node_terms     = map snd used_conjectures: terms;
    (*length added_andnode_keys should be 1.*)
    (*step 4*)
    val added_andnode_keys = SS.add_andnodes and_node_terms synched_agraph: keys;
    val _                  = if length added_andnode_keys = 1 then ()
                             else error "length added_andnode_keys != 1"
    val added_andnode_key  = hd added_andnode_keys: key;
    (*step 5*)
    val _                  = SS.add_edge (edge_key, added_andnode_key) synched_agraph: unit;
    (*step 6*)
    val add_child_ornode   = SS.add_child_ornode ctxt synched_agraph: string * term -> unit;
    val _                  = map add_child_ornode used_conjectures: unit list;
    (*step 7*)
    val _                  =
      SS.add_edges_from_andnode_to_ornodes added_andnode_key synched_agraph: unit;
    (*step 8*)
    val child_orkeys       = map (fn or_term => (Or_N, [or_term])) and_node_terms: keys;
    val _                  =
      map (SS.update_importance_of_ornode synched_agraph) child_orkeys: unit list;
    (*step 9*)
    val _                  =
      SS.update_after_connecting_andnd_to_existing_ornd ctxt synched_agraph child_orkeys
      : unit list;
    (*step 10: expensive*)
    val _                  =
      Par_List.map (SS.try_to_prove_ornode_and_update_graph pst synched_agraph) child_orkeys
  in
    ()
  end;

(*implicit conjecturing:tactic-based conjecturing*)
(*
 * step 0. We have an or-node to expand.
 * step 1. prove the parental or-node using some conjectures.
 * step 2. add an or2and-edge.
 * step 3. connect the or2and-edge to its parental or-node.
 * step 4. add an and-node that consists of used conjectures.
 * step 5. connect the and-node to its parental or2and-edge.
 * step 6. add child-or-nodes that correspond to the sub-goals or used conjectures in the and-node.
 * step 7. connect the child-or-nodes to the and-node.
 * step 8. add the importance of the child-or-nodes.
 * step 9. update the values of or-nodes and and-nodes in the graph.
 * step 10. try to prove the new child or-nodes completely using Attack_On_Or_Node
 *          and update the synchronised graph in case of success.
 *)
fun abduction_for_tactic_based_conjectures
    (pst:Proof.state) (parent_or:key) (seeds: seeds_of_or2and_edge)
    (sagraph:SS.synched_abduction_graph) =
  let
    (*step 1*)
    val triples =
      Par_List.map (prove_ornode_assuming_andnode pst false parent_or sagraph) seeds
      |> Utils.somes: add_or2and_edge list;
    (*step 2 - 10*)
    val _       = Par_List.map (add_nodes_and_edges_to_graph pst parent_or sagraph) triples
  in () end;

(*explicit conjecturing*)
fun eq_conjectures (pairs1:conjectures, pairs2:conjectures): bool =
  let
    val goal_names1 = map fst pairs1;
    val goal_names2 = map fst pairs2;
  in
    eq_set (op =) (goal_names1, goal_names2)
  end;

type decremental_candidate = conjectures * int;

fun candidate_conjectures ((conjectures, _):decremental_candidate) = conjectures: conjectures;
fun candidate_depth ((_, depth):decremental_candidate) = depth: int;

fun eq_decremental_candidate ((c1, _):decremental_candidate, (c2, _):decremental_candidate) =
  eq_conjectures (c1, c2): bool;

fun insert_candidate_max_depth ((conjectures, depth):decremental_candidate) [] =
      [(conjectures, depth)]
  | insert_candidate_max_depth ((conjectures, depth):decremental_candidate)
      (((conjectures', depth')::rest):decremental_candidate list) =
      if eq_conjectures (conjectures, conjectures')
      then (conjectures', Int.max (depth, depth')) :: rest
      else (conjectures', depth') :: insert_candidate_max_depth (conjectures, depth) rest;

fun merge_candidates_max_depth (candidates:decremental_candidate list) =
  fold insert_candidate_max_depth candidates []: decremental_candidate list;

fun candidate_length_ord ((c1, d1):decremental_candidate, (c2, d2):decremental_candidate) =
  case int_ord (length c1, length c2) of
      EQUAL => int_ord (d1, d2)
    | order => order;

fun sort_candidates (candidates:decremental_candidate list) =
  candidates |> merge_candidates_max_depth |> sort candidate_length_ord |> rev
  : decremental_candidate list;

fun decremental_statistics_enabled () =
  getenv "PSL_EVAL_MODE" = "1" andalso getenv "PSL_EVAL_ABDUCTION_STATS_DIR" <> "";

datatype decremental_worker_result =
    Skipped_Duplicate of decremental_candidate
  | Skipped_Subsumed_By_Failed_Set of decremental_candidate
  | Tried_Decrement of {
      candidate: decremental_candidate,
      triple_opt: add_or2and_edge option,
      unproved_used_conjectures: conjectures};

fun int_stats (ints:int list): int * int * int =
  let
    val sorted = sort int_ord ints;
    val n = length sorted;
  in
    if n = 0 then (0, 0, 0)
    else (hd sorted, nth sorted (n div 2), List.last sorted)
  end;

fun cardinality_stats (candidates:decremental_candidate list): int * int * int =
  int_stats (map (length o candidate_conjectures) candidates): int * int * int;

fun depth_stats (candidates:decremental_candidate list): int * int * int =
  int_stats (map candidate_depth candidates): int * int * int;

fun attempted_candidates_from_results (attempt_results:decremental_worker_result list) =
  List.mapPartial
    (fn Tried_Decrement {candidate, ...} => SOME candidate
      | _ => NONE)
    attempt_results: decremental_candidate list;

fun count_skipped_duplicate (Skipped_Duplicate _) = 1
  | count_skipped_duplicate _ = 0;

fun count_skipped_subsumed (Skipped_Subsumed_By_Failed_Set _) = 1
  | count_skipped_subsumed _ = 0;

fun count_attempt (Tried_Decrement _) = 1
  | count_attempt _ = 0;

fun count_success (Tried_Decrement {triple_opt = SOME _, ...}) = 1
  | count_success _ = 0;

fun count_failure (Tried_Decrement {triple_opt = NONE, ...}) = 1
  | count_failure _ = 0;

fun safe_div_int (numerator:int) (denominator:int): real =
  if denominator <= 0
  then 0.0
  else Real.fromInt numerator / Real.fromInt denominator;

fun make_decremental_entry
    (top_loop_index:int) (parent_or_name:string) (is_root_or_node:bool)
    (decremental_round_index:int) (decremental_limit:int)
    (candidate_sets_before:int) (selected_sets:int) (carried_over_sets:int)
    (skipped_duplicate_sets:int) (skipped_subsumed_sets:int)
    (actual_proof_attempts:int) (successful_attempts:int) (failed_attempts:int)
    (new_sets:int) (candidate_sets_after:int)
    (accepted_edges_in_round:int) (accepted_edges_so_far:int)
    (selected_candidates:decremental_candidate list)
    (attempted_candidates:decremental_candidate list)
    (next_candidates:decremental_candidate list)
    (decremental_elapsed_sec:real) =
  let
    val (selected_cardinality_min, selected_cardinality_median, selected_cardinality_max) =
      cardinality_stats selected_candidates;
    val (attempted_cardinality_min, attempted_cardinality_median, attempted_cardinality_max) =
      cardinality_stats attempted_candidates;
    val (next_cardinality_min, next_cardinality_median, next_cardinality_max) =
      cardinality_stats next_candidates;
    val (selected_depth_min, selected_depth_median, selected_depth_max) =
      depth_stats selected_candidates;
    val (attempted_depth_min, attempted_depth_median, attempted_depth_max) =
      depth_stats attempted_candidates;
    val (next_depth_min, next_depth_median, next_depth_max) =
      depth_stats next_candidates;
    val decremental_exact_duplicate_hits = skipped_duplicate_sets: int;
    val decremental_failed_subsumption_hits = skipped_subsumed_sets: int;
    val decremental_cache_hits = skipped_duplicate_sets + skipped_subsumed_sets: int;
    val decremental_cache_misses = actual_proof_attempts: int;
    val decremental_exact_duplicate_hit_rate =
      safe_div_int decremental_exact_duplicate_hits
        (decremental_exact_duplicate_hits + decremental_cache_misses): real;
    val decremental_avoidance_rate =
      safe_div_int decremental_cache_hits selected_sets: real;
  in
    {top_loop_index = top_loop_index,
     parent_or_name = parent_or_name,
     is_root_or_node = is_root_or_node,
     decremental_round_index = decremental_round_index,
     decremental_limit = decremental_limit,
     candidate_sets_before = candidate_sets_before,
     selected_sets = selected_sets,
     carried_over_sets = carried_over_sets,
     skipped_duplicate_sets = skipped_duplicate_sets,
     skipped_subsumed_sets = skipped_subsumed_sets,
     actual_proof_attempts = actual_proof_attempts,
     successful_attempts = successful_attempts,
     failed_attempts = failed_attempts,
     decremental_exact_duplicate_hits = decremental_exact_duplicate_hits,
     decremental_failed_subsumption_hits = decremental_failed_subsumption_hits,
     decremental_cache_hits = decremental_cache_hits,
     decremental_cache_misses = decremental_cache_misses,
     decremental_exact_duplicate_hit_rate = decremental_exact_duplicate_hit_rate,
     decremental_avoidance_rate = decremental_avoidance_rate,
     new_sets = new_sets,
     candidate_sets_after = candidate_sets_after,
     accepted_edges_in_round = accepted_edges_in_round,
     accepted_edges_so_far = accepted_edges_so_far,
     selected_cardinality_min = selected_cardinality_min,
     selected_cardinality_median = selected_cardinality_median,
     selected_cardinality_max = selected_cardinality_max,
     attempted_cardinality_min = attempted_cardinality_min,
     attempted_cardinality_median = attempted_cardinality_median,
     attempted_cardinality_max = attempted_cardinality_max,
     next_cardinality_min = next_cardinality_min,
     next_cardinality_median = next_cardinality_median,
     next_cardinality_max = next_cardinality_max,
     selected_depth_min = selected_depth_min,
     selected_depth_median = selected_depth_median,
     selected_depth_max = selected_depth_max,
     attempted_depth_min = attempted_depth_min,
     attempted_depth_median = attempted_depth_median,
     attempted_depth_max = attempted_depth_max,
     next_depth_min = next_depth_min,
     next_depth_median = next_depth_median,
     next_depth_max = next_depth_max,
     decremental_elapsed_sec = decremental_elapsed_sec}: Abduction_Statistics.decremental_entry
  end;

fun one_decrement
    (pst:Proof.state, synched_agraph:SS.synched_abduction_graph,
     synched_proved_simps:SS.synched_proved_simps, filter_stats:SS.synched_filter_statistics)
    (top_loop_index:int) (parent_or_name:string) (is_root_or_node:bool)
    (decremental_round_index:int) (decremental_limit:int)
    (parent_ornd:key) (candidate_conjecturess:decremental_candidate list)
    (synched_checked:conjectures list Synchronized.var)
    (synched_failed_set:conjectures list Synchronized.var)
    (results:add_or2and_edge list) =
      let
        val record_decremental_statistics = decremental_statistics_enabled ();
        val decremental_round_start =
          if record_decremental_statistics then SOME (Timing.start ()) else NONE;
        (*
         * The expensive proof attempt must not be performed while holding a lock.
         * The checked and failed-set tables are created once per parent OR-node,
         * in abduction_for_explicit_conjectures, and are shared by all
         * one_decrement rounds within that decremental-conjecturing run.
         *)

        (*
         * Process only a bounded prefix of the current candidate queue in this
         * decremental round.  The remaining conjecture sets are carried over to
         * the next round instead of being submitted to Par_List.map immediately.
         *
         * Note on nesting: this code is reached from Proof_By_Abduction.run_worker_pool, which
         * has already forked numb_of_processors persistent workers, every one of which can be
         * inside its own one_decrement simultaneously. A per-round prefix of
         * numb_of_processors therefore makes the number of *queued* proof attempts
         * numb_of_processors squared (144 on a 12-core machine) rather than
         * numb_of_processors. The two levels are not coordinated: there is no shared budget,
         * and each level sizes itself from numb_of_processors independently.
         *
         * That fan-out reads alarmingly, but it was measured NOT to matter for memory, which
         * is why the bound is still numb_of_processors here. Same target, same machine, ML
         * heap ceiling removed so the raw appetite shows, only this bound varying:
         *
         *   prefix = numb_of_processors      (144 queued)   peak 23205MB
         *   prefix = numb_of_processors / 4  ( 36 queued)   peak 23179MB
         *
         * A fourfold cut in queued attempts moved the peak by 0.1%. The reason is that
         * Isabelle's future pool only ever *runs* threads=N tasks at a time regardless of how
         * many are queued, and a queued future is a closure, not a live proof attempt: the
         * memory belongs to the ~N running attempts and to Sledgehammer's own per-call
         * footprint, neither of which this bound changes. Shrinking it only costs parallelism.
         *
         *)
        val numb_of_processors = Thread.Thread.numProcessors (): int;
        val numb_of_conjecture_sets_to_try = Int.max (1, numb_of_processors): int;
        val active_candidates =
          take numb_of_conjecture_sets_to_try candidate_conjecturess: decremental_candidate list;
        val carried_over_candidates =
          drop numb_of_conjecture_sets_to_try candidate_conjecturess: decremental_candidate list;

        fun is_subset_of (sub:conjectures) (sup:conjectures) = subset (op =) (sub, sup);
        fun eq_to_one_of_conjecturess (conjectures:conjectures) (conjecturess:conjectures list) =
          exists (curry eq_conjectures conjectures) conjecturess: bool;
        fun is_subset_of_any_failed_conjectures (sub:conjectures) (failed_set:conjectures list) =
          exists (is_subset_of sub) failed_set: bool;

        fun claim_as_checked (conjectures:conjectures): bool =
          Synchronized.change_result synched_checked
            (fn checked =>
              if eq_to_one_of_conjecturess conjectures checked
              then (false, checked)
              else (true, conjectures :: checked));

        fun register_failed (conjectures:conjectures): unit =
          Synchronized.change synched_failed_set
            (fn failed_set => distinct eq_conjectures (conjectures :: failed_set));

        fun already_subsumed_by_failed_set (conjectures:conjectures): bool =
          is_subset_of_any_failed_conjectures conjectures (Synchronized.value synched_failed_set);

        fun try_one_conjecture_set
              (candidate as (conjectures, _):decremental_candidate): decremental_worker_result =
          if already_subsumed_by_failed_set conjectures
          then Skipped_Subsumed_By_Failed_Set candidate
          else if not (claim_as_checked conjectures)
          then Skipped_Duplicate candidate
          else
            let
              (*1 apply explicit conjecturing and identify used conjectures.*)
              val seed             =
                conjecture_to_seed_of_or2and_edge conjectures: seed_of_or2and_edge;
              val triple_opt       =
                prove_ornode_assuming_andnode pst false parent_ornd synched_agraph seed
                : add_or2and_edge option;
              val used_conjectures =
                if is_none triple_opt then []
                else #3 (Utils.the' "decremental failed." triple_opt): conjectures;
              (*2 identify used conjectures that are not proved.*)
              val proved_simps     = Synchronized.value synched_proved_simps;
              fun is_completely_proved cnjctr = member (op =) proved_simps cnjctr: bool;
              val unproved_used_conjectures =
                filter_out is_completely_proved used_conjectures: conjectures;
              val _ =
                if null used_conjectures
                then register_failed conjectures
                else ();
            in
              Tried_Decrement {candidate = candidate, triple_opt = triple_opt,
                               unproved_used_conjectures = unproved_used_conjectures}
            end;

        (* In order, on this thread. The OR-node worker pool above this is what keeps the
           machine busy - every worker is already on a different node - so a Par_List here was
           nesting parallelism inside parallelism at the level where it does damage rather than
           work (see Monadic_Prover's P-combinators and TBC_Preprocessor for what that cost).

           Sequential is also the stronger order for this particular loop. Each candidate
           registers its failure in synched_failed_set, and each subsequent candidate skips
           itself if some already-failed set subsumes it. Run in parallel, every candidate is
           dispatched before any of them has recorded anything, so the pruning has almost
           nothing to prune with; run in order, a failure prunes the candidates that follow
           it. *)
        val attempt_results =
          map try_one_conjecture_set active_candidates: decremental_worker_result list;

        val newly_checked = Synchronized.value synched_checked: conjectures list;
        val new_failed_set = Synchronized.value synched_failed_set: conjectures list;

        val new_triples =
          List.mapPartial
            (fn Tried_Decrement {triple_opt, ...} => triple_opt
              | _ => NONE)
            attempt_results: add_or2and_edge list;

        val unproved_used_conjectures =
          List.mapPartial
            (fn Tried_Decrement {unproved_used_conjectures, ...} =>
                  if null unproved_used_conjectures then NONE else SOME unproved_used_conjectures
              | _ => NONE)
            attempt_results
          |> flat
          |> distinct (op =): conjectures;

        val abduction_checked_conjectures =
          attempted_candidates_from_results attempt_results
          |> map candidate_conjectures
          |> flat
          |> map snd
          |> distinct (op =): terms;

        val abduction_used_conjectures =
          List.mapPartial
            (fn Tried_Decrement {triple_opt = SOME (_, _, used_conjectures), ...} =>
                  SOME used_conjectures
              | _ => NONE)
            attempt_results
          |> flat
          |> map snd
          |> distinct (op =): terms;

        val _ = SS.record_abduction_filter_input filter_stats abduction_checked_conjectures;
        val _ = SS.record_abduction_filter_used filter_stats abduction_used_conjectures;

        (*3 make new candidate sets by removing one used-but-unproved conjecture.
         * A candidate carries its maximum depth in the refinement DAG.  The
         * initial candidate has depth 0.  Whenever a set is produced by deleting
         * one conjecture from a parent set, the new depth is parent depth + 1.
         * If the same conjecture set is reached through multiple parents, we keep
         * the maximum depth.
         *)
        val generated_candidates =
          if null unproved_used_conjectures
          then []
          else
            let
              fun mk_new_candidates_from (candidate as (conjectures, depth):decremental_candidate) =
                map (fn used_conjecture =>
                      let
                        val new_conjectures =
                          remove (op =) used_conjecture conjectures: conjectures;
                      in
                        if length new_conjectures < length conjectures
                        then SOME (new_conjectures, depth + 1)
                        else NONE
                      end)
                    unproved_used_conjectures
                |> Utils.somes: decremental_candidate list;
            in
              map mk_new_candidates_from active_candidates
              |> flat
              |> sort_candidates
            end;

        val new_candidates =
          carried_over_candidates @ generated_candidates: decremental_candidate list;

        fun eq_to_one_of_checked (conjectures:conjectures) =
          eq_to_one_of_conjecturess conjectures newly_checked: bool;
        val genuinely_new_candidates =
          filter_out (eq_to_one_of_checked o candidate_conjectures) new_candidates
          : decremental_candidate list;

        fun is_subset_of_any_new_failed_conjectures (sub:conjectures) =
          is_subset_of_any_failed_conjectures sub new_failed_set: bool;
        val promising_candidates =
          filter_out (is_subset_of_any_new_failed_conjectures o candidate_conjectures)
                     genuinely_new_candidates
          |> sort_candidates: decremental_candidate list;

        val new_results = new_triples @ results: add_or2and_edge list;

        val _ =
          if record_decremental_statistics
          then
            let
              val selected_sets = length active_candidates: int;
              val carried_over_sets = length carried_over_candidates: int;
              val skipped_duplicate_sets =
                fold (fn r => fn n => n + count_skipped_duplicate r) attempt_results 0: int;
              val skipped_subsumed_sets =
                fold (fn r => fn n => n + count_skipped_subsumed r) attempt_results 0: int;
              val actual_proof_attempts =
                fold (fn r => fn n => n + count_attempt r) attempt_results 0: int;
              val successful_attempts =
                fold (fn r => fn n => n + count_success r) attempt_results 0: int;
              val failed_attempts =
                fold (fn r => fn n => n + count_failure r) attempt_results 0: int;
              val candidate_sets_before = length candidate_conjecturess: int;
              val new_sets = length generated_candidates: int;
              val candidate_sets_after = length promising_candidates: int;
              val accepted_edges_in_round = length new_triples: int;
              val accepted_edges_so_far = length new_results: int;
              val attempted_candidates =
                attempted_candidates_from_results attempt_results: decremental_candidate list;
              val elapsed_sec =
                case decremental_round_start of
                    SOME start => Time.toReal (#elapsed (Timing.result start))
                  | NONE => (0.0: real);
              val decremental_entry = make_decremental_entry
                   top_loop_index parent_or_name is_root_or_node decremental_round_index
                   decremental_limit
                   candidate_sets_before selected_sets carried_over_sets skipped_duplicate_sets
                   skipped_subsumed_sets
                   actual_proof_attempts successful_attempts failed_attempts new_sets
                   candidate_sets_after
                   accepted_edges_in_round accepted_edges_so_far
                   active_candidates attempted_candidates promising_candidates elapsed_sec;
            in
              Abduction_Statistics.record_decremental_entries pst [decremental_entry]
            end
          else ();
      in
        (promising_candidates, new_results)
      end;

fun decremental _ _
      (_:Proof.state, _:SS.synched_abduction_graph, _:SS.synched_proved_simps,
       _:SS.synched_filter_statistics)
      (_:int) (_:string) (_:bool) (_:key) ([]:decremental_candidate list)
      (_:conjectures list Synchronized.var) (_:conjectures list Synchronized.var) results =
    results: add_or2and_edge list
  | decremental (decremental_limit:int) (counter:int)
    (pst:Proof.state, synched_agraph:SS.synched_abduction_graph,
     synched_proved_simps:SS.synched_proved_simps, filter_stats:SS.synched_filter_statistics)
    (top_loop_index:int) (parent_or_name:string) (is_root_or_node:bool)
    (parent_ornd:key) (candidate_conjecturess:decremental_candidate list)
    (synched_checked:conjectures list Synchronized.var)
    (synched_failed_set:conjectures list Synchronized.var)
    (results:add_or2and_edge list) =
    if counter > 0
    then
      let
        val decremental_round_index = decremental_limit - counter + 1: int;
        val (promising_candidates, new_results) =
          one_decrement (pst, synched_agraph, synched_proved_simps, filter_stats)
            top_loop_index parent_or_name is_root_or_node decremental_round_index decremental_limit
            parent_ornd candidate_conjecturess synched_checked synched_failed_set results
      in
        decremental decremental_limit (counter - 1)
          (pst, synched_agraph, synched_proved_simps, filter_stats)
          top_loop_index parent_or_name is_root_or_node parent_ornd promising_candidates
          synched_checked synched_failed_set new_results
      end
    else results;

fun abduction_for_explicit_conjectures
  (pst:Proof.state) (top_loop_index:int) (parent_orkey:key) (conjectures:conjectures)
  (sterm2name:SS.synched_term2string_table, refutation: SS.synched_term2real_table,
   sagraph: SS.synched_abduction_graph, proved_simps:SS.synched_proved_simps,
   filter_stats:SS.synched_filter_statistics) =
  let
    fun tracing' mssg = tracing mssg;
    val _       = tracing' "\n ** Trying to prove **:";
    val parent_or_name = SS.get_orkey_name sterm2name (Proof.context_of pst) parent_orkey: string;
    val _       = tracing' parent_or_name;
    val ctxt    = Proof.context_of pst;
    val _       = Abduction_Graph.print_key ctxt parent_orkey;
    val agraph  = SS.value_of_graph sagraph: abduction_graph;
    val _       = tracing' " decremental abduction starts";
    val limit   = if   Abduction_Graph.is_final_goal agraph parent_orkey
                  then Config.get ctxt Top_Down_Util.limit_for_first_decrement
                  else Config.get ctxt Top_Down_Util.limit_for_other_decrement
    val is_root_or_node = Abduction_Graph.is_final_goal agraph parent_orkey: bool;
    val synched_checked =
      Synchronized.var "Seed_Of_Or2And_Edge.decremental.checked.parent" []
        : conjectures list Synchronized.var;
    val synched_failed_set =
      Synchronized.var "Seed_Of_Or2And_Edge.decremental.failed_set.parent" []
        : conjectures list Synchronized.var;
    val triples =
      decremental limit limit (pst, sagraph, proved_simps, filter_stats)
        top_loop_index parent_or_name is_root_or_node parent_orkey [(conjectures, 0)]
        synched_checked synched_failed_set []: add_or2and_edge list;
    val _       = tracing' " decremental abduction ends";
    fun update_imp (key, abd_node, cnjctrs:conjectures) =
      let
        val orig_term      = Abduction_Graph.get_final_goal_term agraph: term;
        val orig_size      = Term.size_of_term orig_term: int;
        fun sz_wght (t:term) = (*TODO: magic numbers*)
                               if Term.size_of_term t > (5 * orig_size) then 0.85 else
                               if Term.size_of_term t > (4 * orig_size) then 0.90 else
                               if Term.size_of_term t > (3 * orig_size) then 0.95 else 1.0;
        val cnjctr_terms   = map snd cnjctrs: terms;
        val size_penalty   =
          map sz_wght cnjctr_terms |> Utils.reals_to_min_option |> Utils.try_with 1.0 the: real;
        val new_abd_node   = Update_Abduction_Node.multiply_importance size_penalty abd_node;
      in
        (key, new_abd_node, cnjctrs)
      end;
    val new_triples = map update_imp triples: add_or2and_edge list;
    val add_nodes_and_edges_to_graph' = add_nodes_and_edges_to_graph pst parent_orkey sagraph
    val _       = Par_List.map add_nodes_and_edges_to_graph' new_triples: unit list;
  in
    (): unit
  end;

end;