(*  Title:      TBC/TBC_Preprocessor.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.

The TBC preprocessing phase run by the "prove" command before AbductionProver:
races a direct TBC_Strategy attempt on the original goal against generating and
proving template-based conjectures, so that an easy goal does not have to wait
for conjecture generation and a hard goal does not delay it either.
*)
signature TBC_PREPROCESSOR =
sig
val template_conjectures_for_term: Proof.state -> term -> TBC_Utils.pnodes;
val preprocess_term: int -> Proof.state -> term -> Proof.state * TBC_Utils.pnodes;
val preprocess_term_with_statistics:
  TBC_Preprocessor_Statistics.synched_statistics ->
  int -> Proof.state -> term -> Proof.state * TBC_Utils.pnodes;
end;

structure TBC_Preprocessor: TBC_PREPROCESSOR =
struct

type template_generation_summary =
 {generated_conjectures: int,
  refuted_by_counterexample: int,
  surviving_conjectures: int};

fun original_goal_proved_round ([]: TBC_Utils.pnodes) = NONE
  | original_goal_proved_round (pnode :: pnodes) =
      if #is_final_goal pnode andalso #proved_wo_assmng_cnjctr pnode
      then #proved_in_nth_round pnode
      else original_goal_proved_round pnodes;

fun template_conjectures_for_term_with_summary (pst:Proof.state) (goal_term:term) =
  let
    val ctxt = Proof.context_of pst;
    val (relevant_consts, relevant_binary_funcs, relevant_unary_funcs) =
      TBC_Utils.get_relevant_constants ctxt goal_term;

    val conjectures_as_tagged_terms =
      map (Template_Based_Conjecturing.ctxt_n_const_to_all_conjecture_term ctxt)
          (relevant_unary_funcs @ relevant_binary_funcs)
      |> flat: (Template_Based_Conjecturing.property * term) list;

    val _ =
      tracing ("\nTBC_PREPROCESSOR: generated "
        ^ Int.toString (length conjectures_as_tagged_terms)
        ^ " template-based conjectures.");

    val conjectures =
      map (Template_Based_Conjecturing.pst_n_property_n_trm_to_pnode pst)
          conjectures_as_tagged_terms: TBC_Utils.pnodes;

    val conjectures_w_counterexample =
      filter (fn pnode => #refuted pnode) conjectures;

    val conjectures_wo_counterexample =
      filter_out (fn pnode => #refuted pnode) conjectures;

    val _ =
      tracing ("TBC_PREPROCESSOR: "
        ^ Int.toString (length conjectures_w_counterexample)
        ^ " conjectures refuted by Quickcheck/Nitpick.");

    val _ =
      tracing ("TBC_PREPROCESSOR: "
        ^ Int.toString (length conjectures_wo_counterexample)
        ^ " conjectures survived counterexample filtering.");

    val summary =
     {generated_conjectures = length conjectures_as_tagged_terms,
      refuted_by_counterexample = length conjectures_w_counterexample,
      surviving_conjectures = length conjectures_wo_counterexample}:
        template_generation_summary;
  in
    (summary, conjectures_wo_counterexample)
  end;

fun template_conjectures_for_term pst goal_term =
  template_conjectures_for_term_with_summary pst goal_term |> snd;

fun mk_preprocessing_entry rounds_to_run direct_goal_proved direct_goal_elapsed_sec
    ({generated_conjectures, refuted_by_counterexample, surviving_conjectures}
      : template_generation_summary)
    parallel_candidate_nodes processed_pnodes preprocessing_elapsed_sec =
  let
    val original_round = original_goal_proved_round processed_pnodes;
    val original_goal_proved = TBC_Utils.original_goal_is_proved processed_pnodes;
    val parallel_rounds_run =
      if direct_goal_proved then 0
      else
        (case original_round of
           SOME n => if n > 0 then n else 0
         | NONE => rounds_to_run);
    val proved_template_lemmas =
      filter (fn pnode => not (#is_final_goal pnode) andalso #proved_wo_assmng_cnjctr pnode)
             processed_pnodes
      |> length;
  in
   {rounds_requested = rounds_to_run,
    direct_goal_attempted = true,
    direct_goal_proved = direct_goal_proved,
    direct_goal_elapsed_sec = direct_goal_elapsed_sec,
    generated_conjectures = generated_conjectures,
    refuted_by_counterexample = refuted_by_counterexample,
    surviving_conjectures = surviving_conjectures,
    parallel_rounds_run = parallel_rounds_run,
    parallel_candidate_nodes = parallel_candidate_nodes,
    proved_template_lemmas = proved_template_lemmas,
    original_goal_proved_by_tbc = original_goal_proved,
    original_goal_proved_in_round = original_round,
    tbc_preprocessing_elapsed_sec = preprocessing_elapsed_sec}:
      TBC_Preprocessor_Statistics.preprocessing_entry
  end;

fun preprocess_term_with_statistics
      synched_statistics (rounds:int) (pst:Proof.state) (goal_term:term) =
  let
    val preprocessing_start = Timing.start ();
    (*Template-based conjecturing has nothing to offer an "instance" or "interpretation"
      obligation. Such a goal is discharged by decomposing it with intro_classes or
      unfold_locales, not by conjecturing lemmas about the operations it mentions - which is
      what conjecturing does when handed one, at considerable cost. Attack it directly.*)
    val is_obligation =
      TBC_Utils.goal_shape (Proof.context_of pst) goal_term <> TBC_Utils.Ordinary_Goal;
    val rounds_to_run = if rounds < 0 orelse is_obligation then 0 else rounds;
    val _ = TBC_Utils.tbc_trace ("preprocess: entered"
              ^ (if is_obligation then " (obligation goal: skipping conjecturing)" else ""));
    val original_goal = TBC_Utils.term_to_original_goal_pnode pst goal_term;
    val _ = TBC_Utils.tbc_trace ("preprocess: original_goal pnode built, stmt = "
                                 ^ TBC_Utils.pnode_stmt (Proof.context_of pst) original_goal);

    (* The original goal is attempted directly with TBC_Strategy alone first, and template-based
       conjecturing runs only if that failed. One after the other, on this thread: nothing is
       forked here, so nothing has to be abandoned, cancelled or waited for.

       It was a race, with the loser cancelled once the direct attempt had won, and that is what
       made "solve" unusable inside somebody else's theory. Cancelling a task group interrupts
       the shared worker threads its tasks are running on (Future.cancel_now), and a worker picks
       up other queued work whenever it waits - so the interrupt can land on a thread that has
       already moved on to something else. Future.worker_exec ends every task by checking for a
       pending interrupt and cancels that task's whole group when it finds one; in a batch build
       that group is the theory's. The session then dies with a positionless "*** Interrupt"
       belonging to no command, several commands after the one that cancelled. Measured on
       HOL-Library.FuncSet with one proof replaced by "solve", eight runs each: cancelling the
       loser, four failures; not cancelling it, none. In every failing run "solve" itself had
       completed normally and left nothing pending on its own thread - the damage was always
       somebody else's.

       The safe ways to stop racing work all cost more than the race saves, because Par_List
       dispatches every conjecture at once: when you decide to stop, all of them are in flight
       and each runs to its own timeout. Waiting for the loser took Complete_Partial_Order2_solve0
       from 33s to 391s; leaving it to finish unattended merely defers the same bill to the end
       of the session, where the same case came back at 577s.

       What made the race look worth its risk was the direct attempt's own budget: at 300s it
       could spend most of the caller's prove_timeout deciding the goal was not easy, so running
       conjecturing after it rather than alongside it took that time out of the search rather
       than merely delaying the answer. That budget is now proportionate to the question it
       answers - see TBC_Utils.direct_attempt_timeout - and with it the sequential order costs a
       bounded amount and needs no concurrency at all. Measured against the racing version on
       one machine, Countable_Set_solve0 solves in 76s before the change and 82s after. *)
    val direct_start = Timing.start ();
    val (pst_after_round0, processed_after_round0) =
      TBC_Utils.conjectures_n_pst_to_pst_n_proof_parallel_w_limit
        TBC_Utils.TBC_Strategy 1 0 [original_goal] pst;
    val direct_goal_elapsed_sec = #elapsed (Timing.result direct_start) |> Time.toReal;
    val direct_goal_proved = TBC_Utils.original_goal_is_proved processed_after_round0;
    val _ = TBC_Utils.tbc_trace ("preprocess: direct attempt done in "
                                 ^ Real.fmt (StringCvt.FIX (SOME 1)) direct_goal_elapsed_sec
                                 ^ "s, direct_goal_proved = " ^ Bool.toString direct_goal_proved);
  in
    if direct_goal_proved orelse rounds_to_run = 0
    then
      let
        val preprocessing_elapsed_sec = #elapsed (Timing.result preprocessing_start) |> Time.toReal;
        val empty_generation_summary =
         {generated_conjectures = 0,
          refuted_by_counterexample = 0,
          surviving_conjectures = 0}: template_generation_summary;
        val entry =
          mk_preprocessing_entry rounds_to_run direct_goal_proved direct_goal_elapsed_sec
            empty_generation_summary 0 processed_after_round0 preprocessing_elapsed_sec;
        val _ = TBC_Preprocessor_Statistics.set_preprocessing_entry synched_statistics entry;
        val _ = TBC_Utils.tbc_trace "preprocess: returning round0 result";
      in
        (pst_after_round0, processed_after_round0)
      end
    else
      let
        val _ = TBC_Utils.tbc_trace "preprocess: direct attempt failed, conjecturing";
        val (generation_summary, surviving_conjectures) =
          template_conjectures_for_term_with_summary pst goal_term;
        val parallel_candidate_nodes = length surviving_conjectures + 1;
        val (pst_after_preprocessing, processed_pnodes) =
          TBC_Utils.conjectures_n_pst_to_pst_n_proof_parallel_w_limit
            TBC_Utils.TBC_Strategy (rounds_to_run + 1) 1
            (surviving_conjectures @ [original_goal]) pst;
        val preprocessing_elapsed_sec = #elapsed (Timing.result preprocessing_start) |> Time.toReal;
        val entry =
          mk_preprocessing_entry rounds_to_run direct_goal_proved direct_goal_elapsed_sec
            generation_summary parallel_candidate_nodes processed_pnodes preprocessing_elapsed_sec;
        val _ = TBC_Preprocessor_Statistics.set_preprocessing_entry synched_statistics entry;
      in
        (pst_after_preprocessing, processed_pnodes)
      end
  end;

fun preprocess_term (rounds:int) (pst:Proof.state) (goal_term:term) =
  let
    val synched_statistics = TBC_Preprocessor_Statistics.mk_statistics ();
  in
    preprocess_term_with_statistics synched_statistics rounds pst goal_term
  end;

end;
