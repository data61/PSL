(*  Title:      Abduction/Abduction.thy
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

The top-level theory that wires up AbductionProver and its Isar commands.
*)
theory Abduction
  imports "TBC.TBC"
  keywords "prove" :: thy_goal_stmt
  and "prove_by_abduction" :: thy_goal_stmt
  and "suggest" :: diag
  and "solve" :: prf_script
begin

ML_file \<open>Top_Down_Util.ML\<close>
ML_file \<open>And_Node.ML\<close>
ML_file \<open>Or_Node.ML\<close>
ML_file \<open>Or2And_Edge.ML\<close>
ML_file \<open>Abduction_Node.ML\<close>
ML_file \<open>Update_Abduction_Node.ML\<close>
ML_file \<open>Abduction_Graph.ML\<close>
ML_file \<open>Update_Abduction_Graph.ML\<close>
ML_file \<open>Shared_State.ML\<close>
ML_file \<open>Generalise_By_Renaming.ML\<close>
ML_file \<open>Term_Table_for_Abduction.ML\<close>
ML_file \<open>Generalise_Then_Extend.ML\<close>
ML_file \<open>Abstract_Same_Term.ML\<close>
ML_file \<open>Remove_Function.ML\<close>
ML_file \<open>Remove_Outermost_Assumption.ML\<close>
ML_file \<open>Replace_Imp_With_Eq.ML\<close>
ML_file \<open>SeLFiE_For_Top_Down.ML\<close>
ML_file \<open>All_Top_Down_Conjecturing.ML\<close>
ML_file \<open>Abduction_Statistics.ML\<close>
ML_file \<open>Seed_Of_Or2And_Edge.ML\<close>
ML_file \<open>Proof_By_Abduction.ML\<close>

strategy Extend_Leaf =
  Alts [
    Clarsimp,
    Thens [
      Cut 10 (Smart_Induct),
      Alts [
        User< simp_all>(*TODO: this simplification is sometimes harmful.*),
        Auto
      ]
    ]
  ]

strategy Finish_Goal_After_Assuming_Subgoals_And_Conjectures =
  Thens [
    Repeat (Hammer),
    IsSolved
  ]

strategy Attack_On_Or_Node =
  POrs [
    Thens [
      Auto,
      IsSolved
    ],
    PThenOne [
      Alts [
        DInduct,
        Smart_Induct
      ],
      Ors [
        Thens [
          User< simp_all>,
          IsSolved
        ],
        Thens [
          Auto,
          IsSolved
        ]
      ]
    ],
    Thens [
      Hammer,
      IsSolved
    ]
  ]

setup\<open> Config.put_global Top_Down_Util.timeout_config (60.0 * 60.0 * 10.0) \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_first_decrement 40 \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_other_decrement 40 \<close>

(* UI *)
ML\<open> (*This part (the definitions of long_keyword, long_statement, and short_statement) are
from by Pure/Pure.thy in Isabelle/HOL's source code.*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun getenv_int name default =
  case Int.fromString (getenv name) of
      SOME n => n
    | NONE => default;

(* run_abduction_search *)
(* The core search shared by theorem/"prove" and suggest below (solve goes
 * through its own, separate search/apply path - see run_solve further down - since it needs
 * the search's result graph to apply directly rather than a printed script), regardless of
 * how the (context, goal) pair was obtained: from parsing a fresh top-level statement
 * (theorem/"prove") or from focusing on the current pending subgoal of an already-open proof
 * (suggest). pst0 must already be a fresh Proof.state for standardized_cncl in the
 * context we should search in; run_abduction_search never re-derives the goal itself.
 * is_subgoal selects the suggested script's format: for a fresh top-level
 * goal the whole thing, root included, is printed as "lemma name: stmt \n
 * proof"; for a subgoal of an already-open proof (suggest) the root is
 * printed as a bare tactic script instead, since the goal is already stated
 * at the point it will be pasted into - only genuinely new auxiliary lemmas
 * still get their own "lemma name: stmt" header, using var_N throughout as
 * before (they are fresh, self-contained, universally-quantified facts, so
 * var_N is correct for them regardless of the caller's own variable names).
 * rename_mapping is only used when is_subgoal is set (pass [] otherwise): it
 * is the (var_N, original_name) mapping recovered from however
 * standardized_cncl's free variables were named before standardize_vnames
 * renamed them, used to translate the root's bare script back to those
 * original names, since the goal is already stated using them at the point
 * the script will be pasted into. Deliberately a separate parameter from
 * is_subgoal rather than inferring "is_subgoal = not (null rename_mapping)":
 * a subgoal can genuinely have zero free variables, in which case an empty
 * mapping does not mean "this is the top-level case". *)
fun run_abduction_search (use_tbc_preprocessing:bool)
    (caller: TBC_Utils.caller_context option)
    (rename_mapping: (string * string) list)
    (start:Timing.start) (pst0:Proof.state) (standardized_cncl:term): unit =
  (* The memory monitor wraps this whole function, not just the abduction search inside it.
   * TBC preprocessing below runs before Proof_By_Abduction is entered at all and is itself
   * heavily parallel, so a monitor placed inside the search leaves the phase a
   * preprocessed_abduction run starts in completely unguarded - which is exactly why an
   * earlier attempt failed to stop anything even when its own predicate was forced to report
   * "no memory". Both phases are inside the monitored task group now.
   *
   * The search slot wraps the monitor in turn. Both batch builds and jEdit fork each proof
   * block into a future, so consecutive suggest/prove commands do not wait for each other -
   * measured, a chain of 18 suggest theories completed each toplevel transaction in about a
   * second while the searches themselves piled up concurrently, sharing one deadline, one
   * stop-request flag, one hammer budget and one machine. See
   * Resource_Limit.max_parallel_searches for the numbers. Queueing here instead means each
   * search runs against the machine the monitor's floor was derived from.
   *
   * The full GC runs after the slot is acquired and before configured_floor reads
   * MemAvailable. Poly/ML returns collected segments to the OS (measured with ML_Heap.full_gc:
   * a process holding 715MB of dropped garbage went back to 91MB VmRSS), but does not collect
   * eagerly - so without this, every completed search leaves its garbage inflating the
   * process's footprint, MemAvailable sinks across a long jEdit session, each later search
   * derives a meaner floor from it, and the guard grows more and more trigger-happy until a
   * restart "fixes" it. hammer_slots reads the same signal and shrank the same way. *)
  let
    val search_limit =
      Config.get (Proof.context_of pst0) Resource_Limit.max_parallel_searches;
    (* Racy, and only a message: without it a queued command shows nothing at all until the
       earlier search finishes, which reads as a hang. *)
    val _ =
      if Resource_Limit.search_slots_in_use () >= Int.max (1, search_limit)
      then tracing ("AbductionProver: waiting for an earlier search in this session to finish"
                    ^ " before starting this one (max_parallel_searches = "
                    ^ Int.toString (Int.max (1, search_limit)) ^ ").")
      else ()
  in
  Resource_Limit.with_search_slot search_limit
    (fn () =>
  let
    val _ = ML_Heap.full_gc ();
    (* The caller's clock started when its command ran, which under the search slot can be a
       long queue wait ago - long enough that still_has_time would report the budget spent
       before the search had done anything. The search's own clock starts here, once the slot
       is held; what the verdict reports as "spent" is search effort, not queueing. *)
    val start = Timing.start ();
    (* Where the refutation watchdog leaves its finding. Outside the monitor, because the
       verdict has to be readable on every way out - including the path where the watchdog's
       own stop escalated to a hard cancel and the body never reached its verdict writer. *)
    val root_cex = Synchronized.var "root_refutation_result" (NONE: string option);
    (* The result is discarded on the guard's cancellation: everything proved so far has already
       been written to the shared graph and emitted, and this function returns unit anyway. Any
       other exception is re-raised below - it used to be discarded too, which made a crashed
       search indistinguishable from an instant, silent give-up (no verdict row, no message). *)
    val (search_result, stopped_because) =
      Proof_By_Abduction.with_memory_monitor
        (Proof_By_Abduction.configured_floor (Proof.context_of pst0))
        Proof_By_Abduction.memory_status_message
        (fn stop_search =>
  let
    (* Start the caller's prove_timeout here, before TBC preprocessing rather than at the point
       where AbductionProver's own clock starts, because preprocessing is inside the budget too -
       it was the phase running unbounded. Cleared below, so a later command does not inherit a
       deadline set for this one. See Resource_Limit.set_deadline_in. *)
    val _ =
      Resource_Limit.set_deadline_in
        (Config.get (Proof.context_of pst0) Top_Down_Util.timeout_config);
    val _ = Top_Down_Util.warn_if_proof_output_dir_unset ();
    (* Quickcheck/nitpick on the root, beside the search rather than in front of it: a true
       goal pays nothing, a false one stops the whole search instead of spending its entire
       prove_timeout trying to prove False. See fork_root_refutation_watchdog. *)
    val refutation_watchdog =
      Proof_By_Abduction.fork_root_refutation_watchdog stop_search root_cex pst0
        standardized_cncl;
    val tbc_seed_statistics = TBC_Preprocessor_Statistics.mk_statistics ();
    (* Progress snapshots start with the search, not with the graph phase: TBC preprocessing
       can dominate the wall clock, and its proved conjectures are exactly what a manager that
       abandons the search early wants to salvage. The store is cleared here - the search slot
       guarantees we are the only search - and the graph phase's own reporter takes over the
       same file when preprocessing ends. *)
    val _ = TBC_Utils.clear_progress_pnodes ();
    val tbc_progress_reporter =
      if use_tbc_preprocessing
      then SOME (Proof_By_Abduction.fork_progress_reporter pst0 start "TBC preprocessing"
             (fn () =>
                case TBC_Utils.progress_pnodes_text (Proof.context_of pst0) of
                  "" => ""
                | lemmas =>
                    "(* Standalone, fully-proved lemmas: paste them ABOVE your theorem\n\
                    \   statement, after the definitions they mention. Nothing here is\n\
                    \   sorried; each was proved outright. *)\n" ^ lemmas))
      else NONE;
    val (pst, preprocessed_nodes) =
      if use_tbc_preprocessing
      then
        let
          val rounds = getenv_int "PSL_EVAL_TBC_PREPROCESS_ROUNDS" 2;
          val _ =
                tracing ("TBC_PREPROCESSOR: running " ^ Int.toString rounds
                  ^ " preprocessing round(s) before AbductionProver.");
        in
          TBC_Preprocessor.preprocess_term_with_statistics
            tbc_seed_statistics rounds pst0 standardized_cncl
        end
      else (pst0, []: TBC_Utils.pnodes);
    val _ =
      case tbc_progress_reporter of SOME reporter => #stop reporter () | NONE => ();
    (* explicitize_tbc_pnodes does three things at once here: it drops one of each pair of
       mirrored equations (TBC's templates prove associativity twice, once each way - measured,
       the pair as rewrite rules sent a reconstruction into Interrupt_Breakdown), it rewrites
       every script to name the auxiliary facts it needs in its own method text, and it drops
       the auxiliaries nothing needs. solve's replay consumes the same function's output, so
       suggest cannot emit what solve would not apply. tbc_fact_names feeds the graph-script
       printers, whose scripts were found under the same simp bag. *)
    val (printable_nodes, tbc_fact_names) =
      Proof_By_Abduction.explicitize_tbc_pnodes pst preprocessed_nodes;
    val prelude_proofs =
      case caller of
        SOME ctx =>
          TBC_Utils.proved_nodes_to_proof_text_for_subgoal (Proof.context_of pst) ctx
            rename_mapping printable_nodes
      | NONE => TBC_Utils.proved_nodes_to_proof_text (Proof.context_of pst) printable_nodes;
    val tbc_preprocessing_solved_goal =
      use_tbc_preprocessing andalso TBC_Utils.original_goal_is_proved preprocessed_nodes;
    val abduction_invoked = not tbc_preprocessing_solved_goal;
    val proof_by_abduction_with_prelude =
      case caller of
        SOME ctx =>
          Proof_By_Abduction.proof_by_abduction_for_subgoal_with_prelude ctx rename_mapping
            tbc_fact_names
      | NONE => Proof_By_Abduction.proof_by_abduction_with_prelude tbc_fact_names;
    val (solved, abduction_elapsed_sec) =
      if tbc_preprocessing_solved_goal
      then (Proof_By_Abduction.emit_proof_script pst prelude_proofs; (true, 0.0))
      else
        let
          val abduction_start = Timing.start ();
          val solved_by_abduction =
            proof_by_abduction_with_prelude
              prelude_proofs pst abduction_start standardized_cncl;
          val elapsed_by_abduction =
                #elapsed (Timing.result abduction_start) |> Time.toReal;
        in
          (solved_by_abduction, elapsed_by_abduction)
        end;
    val elapsed = #elapsed (Timing.result start): Time.time;
    val elapsed_str = Time.toReal elapsed |> Real.toString: string;
    val _ =
      if use_tbc_preprocessing
      then
        TBC_Preprocessor_Statistics.write_final pst tbc_seed_statistics
         {abduction_invoked = abduction_invoked,
          abduction_solved = solved andalso abduction_invoked,
          abduction_elapsed_sec = abduction_elapsed_sec,
          total_elapsed_sec = Time.toReal elapsed}
      else ();
    (* Cancelled before the verdict is decided, so a counterexample can no longer arrive
       between reading root_cex and writing the row. Harmless when it already finished, and
       the cancelled/failed body paths need nothing here: those cancel the whole monitored
       group, watchdog included. *)
    val _ = Future.cancel refutation_watchdog;
    val root_refuted = Synchronized.value root_cex: string option;
    val message =
          "We spent " ^ elapsed_str ^ " seconds. "
          ^ (case (solved, root_refuted) of
               (true, _) => "And we proved the goal."
             | (false, SOME why) =>
                 "The goal has a genuine counterexample (" ^ why ^ "); there is nothing to prove."
             | (false, NONE) => "We failed, but tried.");
    val _ = tracing message: unit;
    (* tracing alone is not enough: a batch build does not surface it, so this verdict was
       invisible to every evaluation harness. See Top_Down_Util.write_verdict for what that cost
       and what the invariant below checks. A goal both proved and refuted means one of the two
       tools is unsound; say so loudly and keep the proof's verdict, which at least has a
       checkable script behind it. *)
    val _ =
      (case (solved, root_refuted) of
         (_, NONE) => Top_Down_Util.write_verdict (Proof.context_of pst) solved (Time.toReal elapsed)
       | (true, SOME why) =>
           (warning ("AbductionProver proved a goal the refutation watchdog also refuted ("
                     ^ why ^ "). One of the two is unsound; please report this goal.");
            Top_Down_Util.write_verdict (Proof.context_of pst) true (Time.toReal elapsed))
       | (false, SOME _) =>
           Top_Down_Util.write_verdict_refuted (Proof.context_of pst) (Time.toReal elapsed)): unit;
  in
    ()
  end);
    (* The deadline belongs to this search only; a later command in the same session must not
       find it still set and decline to start. Same reason clear_stop_request exists. Cleared
       out here rather than at the body's end so that every exit clears it - a body that raised
       or was cancelled used to leave it set. *)
    val _ = Resource_Limit.clear_deadline ();
    (* The hard-cancelled path: the watchdog's stop escalated and the body never reached its
       verdict writer above. The refuted row must exist anyway - it is the whole point for a
       webservice runner - and with_memory_monitor has already warned with the reason. *)
    val _ =
      case (search_result, Synchronized.value root_cex) of
        (Exn.Exn _, SOME _) =>
          Top_Down_Util.write_verdict_refuted (Proof.context_of pst0)
            (Time.toReal (#elapsed (Timing.result start)))
      | _ => ();
  in
    case (search_result, stopped_because) of
      (Exn.Res _, _) => ()
      (* The guard's stop: with_memory_monitor has already warned with the recorded reason, and
         the partial results were emitted as the search unwound. Nothing further to raise. *)
    | (Exn.Exn _, SOME _) => ()
    | (Exn.Exn exn, NONE) => Exn.reraise exn
  end)
  end;

(* mk_search_ctxt *)
(* Common context sanitisation (quieter SMT/Metis output) shared by every
 * entry point, applied to whichever context that entry point starts from. *)
fun mk_search_ctxt (ctxt:Proof.context): Proof.context =
    Config.put SMT_Config.verbose false ctxt
 |> Config.put Metis_Generate.verbose false
 |> Context_Position.set_visible false
    (* Record where a suggestion should be written while we are still on the command's own
       thread. By the time the printer runs it is on a worker with no position of its own -
       see Proof_By_Abduction.write_suggestion_beside_theory. *)
 |> Config.put Top_Down_Util.suggestion_target
      (Top_Down_Util.suggestion_target_for (Position.thread_data ()));

fun check_problem_size (cncl_as_trm:term): unit =
  if Term.size_of_term cncl_as_trm < 100 then ()
  else error ("Your problem size seems too large for Abduction Prover.\n"
              ^ " Can you rephrase it?");

fun theorem command_keyword descr use_tbc_preprocessing =
  Outer_Syntax.local_theory command_keyword ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, elems, concl) =>
       (fn lthy =>
          let
            fun is_not_fix (Element.Fixes _) = false
              | is_not_fix _                 = true
            fun is_supported (elements:Element.context list) = exists is_not_fix elements;
            val _ = if is_supported elems then () else error
                     ("Currently, the \"prover\" keyword does not support the use of following"
                      ^ " keywords: \n" ^
                      "\"constraints\", \"assumes\", \"defines\", \"notes\", and  \"lazy_notes\"."
                      ^ "\n" ^
                      "Please present your proof goal as one single term.")
            fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, strs:strings)])]) =
                  stmt: string
              | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in United_Reasoning";
            val start = (fn _ => Timing.start ()) lthy: Timing.start;
            val cncl_as_trm  = Syntax.read_term lthy (stmt_to_stmt_as_string concl)
                            |> Top_Down_Util.standardize_vnames: term;
            val _ = check_problem_size cncl_as_trm;
            val standardized_cncl = Top_Down_Util.standardize_vnames cncl_as_trm;
            val pst0 = Proof.init (mk_search_ctxt lthy): Proof.state;
            val _ = run_abduction_search use_tbc_preprocessing NONE [] start pst0 standardized_cncl;
          in
            lthy
          end)
       )
      )
     );

(* focus_and_prepare_search *)
(* Shared by suggest_command and run_solve below: both read the goal
 * from an *already open* proof instead of parsing a fresh statement, so both work wherever a
 * proof is currently open: inside a structured Isar proof (after "proof (induct x)", at a
 * "show"/"case"), or midway through a chain of "apply" steps - exactly where
 * "prove"/"prove_by_abduction" cannot be used. Subgoal.focus turns the first pending
 * subgoal's schematic/bound variables into genuine local frees and its premises into real
 * local facts in a fresh context, the same mechanism Eisbach's "match" method and
 * Sledgehammer's goal handling are built on - so the goal reaches AbductionProver as an
 * ordinary term with ordinary free variables, never round-tripped through a printed/re-read
 * string as PSL's own find_proof/try_hard do for their *result* (we still do that for
 * suggest's suggested script and solve's replayed root script, since
 * those are genuinely text/method syntax, but not for the goal itself on the way in).
 * Only ever focuses on subgoal 1, matching the default behaviour of "apply" and
 * "sledgehammer" alike; proving a different subgoal first is the usual way to reach the one
 * you want.
 * Caveat shared with sledgehammer (both read Proof.goal the same way): right after "case (C
 * x)" but before "show ?case" has been entered, Proof.goal still reflects the goal under its
 * pre-case variable name, not "x" - so a script obtained at that exact point may reference a
 * variable name that only becomes "x" once "show ?case" actually opens the case's own goal.
 * Invoke suggest/solve after "show ?case" (or mid an "apply" chain), not
 * directly after "case", for reliable variable names.
 * Returns (rename_mapping, pst0, standardized_cncl): rename_mapping is the (var_N,
 * original_name) mapping recovered from however the goal's free variables were named before
 * standardize_vnames renamed them (see Top_Down_Util.standardize_vnames_with_mapping),
 * translated through Proof_Context.extern_fixed since Subgoal.focus itself skolemizes the
 * subgoal's parameters, so the raw free variable names are internal names like "m__", not the
 * "m" the user actually typed - extern_fixed reverses exactly this skolemization (it is the
 * same lookup the pretty printer uses to display "m__" as "m" in goal output); pst0/
 * standardized_cncl are the fresh, isolated search context and goal AbductionProver actually
 * searches against - never pst_orig itself, which the caller already has and, for
 * solve, applies the found proof to separately once the search succeeds. *)
fun focus_and_prepare_search (pst_orig:Proof.state)
    : (string * string) list * Proof.state * term =
  let
    (* Proof.goal yields the pending goal AND the facts chained into it by "using"/"from"/
       "with". They live in a different place from the goal and from the subgoal's premises,
       and reading only #goal drops them silently - so a user who has just handed the prover
       the decisive lemma is told no proof exists. Carry them through to the search state
       below. See Test_Isar/Scenario_Chained_Facts.thy. *)
    val {facts = chained_facts, goal = goal_thm, ...} = Proof.goal pst_orig;
    val ({context, asms, concl, ...}: Subgoal.focus, _) =
      Subgoal.focus (Proof.context_of pst_orig) 1 NONE goal_thm;
    (* The subgoal's own premises are part of the goal. Reading only #concl hands the search a
       different statement, and usually a false one:

         n = y ==> S (count n xs) = count n (cons2 y xs)

       was searched as

         S (count n xs) = count n (cons2 y xs)

       which does not hold - counting n in "cons2 y xs" only gains one when n is y. Measured on
       the two goals with premises in the twenty-problem set, IsaPlanner prop_05 and prop_41:
       both searched their bare conclusion. prop_05 then reported "found a proof, but could not
       replay it", which is what it looks like from outside when the thing proved was not the
       goal.

       The facts a caller chained in with "using" were already carried through below, with a
       comment about how silently dropping them tells a user no proof exists. The subgoal's
       premises are the other half of that point and were being dropped in the same way. *)
    val focused_goal =
      Logic.list_implies (map Thm.term_of asms, Thm.term_of concl): term;
    (* Standardise against the FOCUS context, not the caller's.
       Subgoal.focus fixes the subgoal's own parameters in the focus context, so standardising
       there leaves every variable the goal actually talks about alone - the caller's own, the
       ones a locale or class fixed, and the ones focusing just introduced. Standardising
       against the caller's context instead left this last group unfixed and therefore renamed
       to var_N, which is a name that exists nowhere the script will be replayed or pasted; the
       mapping was then needed to undo it, and a second standardisation inside the graph search
       silently undid the undoing ("induct var_0" for a goal whose variable is "xs").
       With the focus context the mapping is normally empty and nothing needs undoing. See
       docs/2026_08_01_isar_integration_design.md: the goal the search works on should be the caller's goal. *)
    val (standardized_cncl, orig_to_var_mapping) =
      focused_goal
      |> Top_Down_Util.standardize_vnames_with_mapping_in_ctxt context
      : term * (string * string) list;
    val rename_mapping =
      map (fn (orig, var_n) => (var_n, Proof_Context.extern_fixed context orig))
        orig_to_var_mapping;
    (* Expected to be empty, and so far always is: after Subgoal.focus every free in the
       conclusion is fixed - the parameters by the focus, the rest by the enclosing context - so
       standardising against the focus context renames nothing. The renaming machinery
       downstream exists for the case where that does not hold; say so if it ever happens,
       rather than letting a silent rename reintroduce names that exist nowhere the script will
       be used. See docs/2026_08_01_isar_integration_design.md. *)
    val _ =
      if null rename_mapping then ()
      else warning ("AbductionProver: the goal's variables were renamed for the search ("
                    ^ commas (map (fn (v, orig) => v ^ " for " ^ orig) rename_mapping)
                    ^ "). This is not expected after focusing; the script will be translated"
                    ^ " back, but please report the goal.");
    val _ = check_problem_size standardized_cncl;
    (* Step 1 of docs/2026_08_01_isar_integration_design.md, as far as the caller's position allows: search the
       caller's own goal rather than a fresh Proof.theorem that merely has the same conclusion.

       Only in prove mode. Subgoal.subgoal is the Isar "subgoal" command and needs a goal actually
       being proved; in state mode - right after "proof -", and inside a "case" before its "show" -
       it fails with "Illegal application of proof command in \"state\" mode".

       Opening the goal first to get into prove mode was tried and is a dead end here. With
       "?thesis" it fails inside a case, where the pending goal is "?case". With the focused
       conclusion as a term it fails too, and the message says why: the exported rule reads
       "(add ?xa2 Z = ?xa2) ==> add (S xb__) Z = S xb__" - Subgoal.focus has skolemised the
       case's parameter to an internal name, and the case's induction hypothesis is part of the
       goal being refined. Restating is precisely the round trip this design removes, so the
       answer is not a better restatement.

       In state mode there is also nothing to retrofit into: "suggest" only prints, and "solve"
       opens its own "show" before applying anything. So state mode keeps the fresh theorem, and
       the sub-state is built where it buys something. *)
    val parameter_names =
      (case Proof.goal pst_orig of
         {goal, ...} =>
           if Thm.nprems_of goal = 0 then []
           else map fst (Logic.strip_params (Thm.prem_of goal 1)));
    val pst0 =
      if can Proof.assert_backward pst_orig
      then
        (if null parameter_names then pst_orig
         else
           snd (Subgoal.subgoal (Binding.empty, []) NONE
                  (false, map (fn n => (SOME n, Position.none)) parameter_names) pst_orig))
        |> Proof.map_context mk_search_ctxt
        |> Proof.using_facts chained_facts
      else
        Proof.theorem NONE (K I) [[(standardized_cncl, [])]] (mk_search_ctxt context)
        |> Proof.using_facts chained_facts
      : Proof.state;
  in
    (rename_mapping, pst0, standardized_cncl)
  end;

(* suggest_command *)
(* Like find_proof/try_hard/sledgehammer, this is a diagnostic command (Toplevel.keep_proof):
 * it searches and prints a suggested script, it does not itself transform the proof state or
 * close the goal. See run_solve/solve_local/solve_global below for the automatically-applying
 * sibling command. *)
(* caller_context_of *)
(* Describes the position the suggestion will be pasted into, so it can be shaped to be legal
 * there - see TBC_Utils.assemble_suggestion.
 *
 * backward distinguishes an apply-script position, where "apply"/"done" are legal and
 * "have"/"show" are not, from a structured one ("proof -" with no show yet, or inside a
 * "case"), where the reverse holds.
 *
 * The goal text is the pending subgoal printed in the CALLER's own context, so the names in it
 * are the ones visible where the script lands. It is taken after Subgoal.focus, which fixes the
 * goal's parameters and moves its premises into the context, leaving the conclusion the caller
 * has to "show".
 *
 * only_subgoal says whether the goal we are asked about is the only one pending. It decides
 * whether a structured block may close the whole proof or must focus just this subgoal - see
 * assemble_suggestion. Measured: invoked after "apply (rule conjI)", with "True" still pending
 * alongside, the suggestion opened "proof -" and showed only the first subgoal, so the pasted
 * proof could not be finished. *)
fun caller_context_of (pst_orig:Proof.state): TBC_Utils.caller_context =
  let
    val ({context, asms, concl, ...}: Subgoal.focus, _) =
      Subgoal.focus (Proof.context_of pst_orig) 1 NONE (#goal (Proof.goal pst_orig));
  in
    {backward = can Proof.assert_backward pst_orig,
     (* The goal's own meta-quantified parameter names, in order - what a "subgoal for ..."
        must fix so that the script can go on naming them. See assemble_suggestion. *)
     parameters =
       (case Proof.goal pst_orig of
          {goal, ...} =>
            if Thm.nprems_of goal = 0 then []
            else map fst (Logic.strip_params (Thm.prem_of goal 1))),
     only_subgoal = Thm.nprems_of (#goal (Proof.goal pst_orig)) <= 1,
     (* The names of whatever the caller chained in, recovered from each fact's name hint. A
        suggestion that opens a structured block has to name them again - see
        assemble_suggestion. Facts with no usable name are dropped rather than guessed at. *)
     chained_facts =
       #facts (Proof.goal pst_orig)
       |> map_filter (fn thm =>
            let val name = Thm_Name.print (Thm.get_name_hint thm)
            in if name = "" orelse name = "??.unknown" then NONE else SOME name end),
     (* The whole subgoal, premises included. assemble_suggestion puts this in a "show" inside
        "subgoal ... proof -", and that block has no "assume": the pending goal there is still
        "P ==> Q", so a show of the bare conclusion states something weaker than what has to be
        discharged and the pasted proof does not close the subgoal. Same reason the search is
        given the premises - see focus_and_prepare_search. *)
     goal_text =
       Isabelle_Utils.trm_to_string context
         (Logic.list_implies (map Thm.term_of asms, Thm.term_of concl))}
  end;

fun suggest_command (top:Toplevel.state): unit =
  let
    val pst_orig = Toplevel.proof_of top;
    val caller = caller_context_of pst_orig;
    val (rename_mapping, pst0, standardized_cncl) = focus_and_prepare_search pst_orig;
  in
    run_abduction_search true (SOME caller) rename_mapping (Timing.start ()) pst0
      standardized_cncl
  end;

(* run_solve *)
(* Unlike suggest, this actually applies the found proof to the caller's real, live
 * proof state pst_orig, closing the current subgoal, rather than merely printing a script for
 * the user to paste - see Proof_By_Abduction.search_for_subgoal_and_capture_graph/
 * apply_graph_proof_to_pst for the mechanism (driving Proof.have/Proof.refine_singleton/...
 * directly via ML rather than printing and re-parsing text), and
 * apply_tbc_prelude_aux_to_pst/apply_tbc_final_to_pst for the analogous mechanism applied to
 * TBC preprocessing's own separate pnode-based results (run_solve uses TBC preprocessing,
 * exactly like suggest/run_abduction_search above - the subgoal-focused,
 * AbductionProver-only path with no TBC preprocessing was tried first and dropped: it hit a
 * genuine type-checking failure deep in AbductionProver's own template-based conjecturing on
 * a goal needing several non-trivial auxiliary lemmas, apparently a latent bug that TBC
 * preprocessing normally shields against in practice by discharging the easier lemmas first,
 * confirmed unrelated to solve's own new code since the same failure never reaches
 * apply_graph_proof_to_pst at all - it is still mid-search when it happens. Debugging
 * AbductionProver's own conjecturing is out of scope here, and TBC preprocessing is already a
 * proven, extensively-tested path via suggest, so solve uses it too
 * rather than the AbductionProver-only mode prove_by_abduction offers at the top level).
 * pst_orig may be genuinely nested (e.g. inside "show ?case"), itself at the bottom of the
 * whole proof (e.g. a bare "lemma foo: \"P\" apply (induct x)" with no structured "proof"/
 * "qed" at all), or - a third case, distinct from both - at the bottom but not yet in
 * backward/"show"n mode at all (e.g. "lemma foo: \"P\" proof - solve qed", with the
 * user's own separate "qed" still to come in the source text). solve must close
 * correctly in all three cases, exactly as "done" itself would in the first two, but the third
 * has no real "done"-equivalent at all - a bare "apply"/"done" is not valid Isar syntax
 * directly after "proof -" without an intervening "show" - so solve cannot rely on
 * Toplevel.end_proof's own arm dispatch there, which only checks bottom-ness, not backward-
 * ness. Returns (was_already_backward, result) - see Proof_By_Abduction.apply_root_steps, whose
 * return value this directly threads through.
 *
 * The actual replay of a found script (apply_tbc_prelude_aux_to_pst/apply_tbc_final_to_pst/
 * apply_graph_proof_to_pst) is wrapped in apply_safely below: AbductionProver's search runs
 * with real thread parallelism (see the project's own threads=$(nproc) build setting), and its
 * internal variable-naming (Top_Down_Util.standardize_vnames, used pervasively across
 * conjecturing/generalisation) numbers each independently-explored term's own free variables
 * from scratch ("var_0", "var_1", ...) - confirmed, via repeated empirical reruns of the same
 * goal, that on rare occasions (roughly one run in eight to ten, for a goal needing several
 * generalised auxiliary lemmas) the assembled script ends up with a genuine name collision
 * between two different, unrelated "var_0"s of different types from different search branches,
 * which the single flat rename_mapping computed once upfront cannot possibly resolve. This is
 * a pre-existing characteristic of the shared search/printing machinery (the same risk exists,
 * unrealised so far, in suggest's own printed suggestions), not a defect in how this
 * function replays a script - so rather than attempt a deep fix of the search's internal
 * variable-naming scheme (well out of scope here), a failed replay is simply surfaced as a
 * clear, actionable error rather than an opaque, confusing raw type-checking exception. *)
fun apply_safely (f: unit -> 'a): 'a =
  (case Exn.capture f () of
    Exn.Res result => result
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else
        (* Runtime.exn_message, not General.exnMessage: Isabelle's ERROR carries its message as
           markup, which the latter renders as the literally useless string "<markup>" - which
           is exactly what a real replay failure reported, leaving nothing to diagnose. *)
        (* States what happened and does not name a cause.
         *
         * It used to attribute every replay failure to "internal variable-naming reuse across
         * parallel search branches" - the var_0 collision. That is one possible cause among
         * several, and when a different one fired the message sent the reader after a collision
         * that had not occurred: measured, a failure whose actual cause was mk_ornode
         * standardising out of context, where no two names clashed at all. A confident wrong
         * diagnosis in an error message costs more than no diagnosis. *)
        error ("solve: AbductionProver found a proof, but could not replay it against the live "
               ^ "goal (" ^ Runtime.exn_message exn ^ ").\n"
               ^ "The goal is unchanged. Set PSL_SOLVE_TRACE to a file to see which step failed "
               ^ "and what the script actually said; \"suggest\" prints the script without "
               ^ "applying it, which is often enough to see the problem."));

(* Diagnostic tracing, off unless PSL_SOLVE_TRACE names a file.
 * Written with interrupts disabled: the failures worth tracing here are precisely the ones
 * where an interrupt is already pending, and an ordinary write would itself be interrupted -
 * losing the very line that says what happened. *)
fun solve_trace (msg:string): unit =
  case getenv "PSL_SOLVE_TRACE" of
    "" => ()
  | path =>
      Thread_Attributes.uninterruptible_body (fn _ =>
        ignore (\<^try>\<open>File.append (Path.explode path) (msg ^ "\n")\<close>));

(* run_solve_body *)
(* The whole of solve's work, so that it can be run under the memory monitor - see run_solve. *)
fun run_solve_body (stop_search: string -> unit)
    (root_cex: string option Synchronized.var)
    (watchdog_holder: unit future option Unsynchronized.ref)
    (pst_orig:Proof.state): bool * Proof.state =
  let
    val _ = solve_trace "ENTER run_solve";
    val start = Timing.start ();
    val (rename_mapping, pst0, standardized_cncl) = focus_and_prepare_search pst_orig;
    (* The same watchdog suggest/prove run: quickcheck/nitpick on the root, beside the search.
       The future lands in the holder so run_solve can cancel it on every exit - this body has
       several success returns and an error raise, and a slow nitpick must not outlive the
       search slot. *)
    val _ =
      Unsynchronized.:= (watchdog_holder,
        SOME (Proof_By_Abduction.fork_root_refutation_watchdog stop_search root_cex pst0
                standardized_cncl));
    val _ = solve_trace ("  focus done; goal = "
              ^ Isabelle_Utils.trm_to_string (Proof.context_of pst0) standardized_cncl
              ^ "; mapping = " ^ ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_string
                  ML_Syntax.print_string) rename_mapping);
    val rounds = getenv_int "PSL_EVAL_TBC_PREPROCESS_ROUNDS" 2;
    (* Same whole-search progress coverage as run_abduction_search: TBC's phase reports from
       the store, the graph search's own reporter takes over the same file afterwards. *)
    val _ = TBC_Utils.clear_progress_pnodes ();
    val tbc_progress_reporter =
      Proof_By_Abduction.fork_progress_reporter pst0 start "TBC preprocessing"
        (fn () =>
           case TBC_Utils.progress_pnodes_text (Proof.context_of pst0) of
             "" => ""
           | lemmas =>
               "(* Standalone, fully-proved lemmas: paste them ABOVE your theorem\n\
               \   statement, after the definitions they mention. Nothing here is\n\
               \   sorried; each was proved outright. *)\n" ^ lemmas);
    (* No handler: if preprocessing raises, this task's failure cancels the monitored group
       and the reporter future dies with it; the explicit stop covers the normal path. *)
    val (pst_tbc, preprocessed_nodes) =
      TBC_Preprocessor.preprocess_term_with_statistics
        (TBC_Preprocessor_Statistics.mk_statistics ()) rounds pst0 standardized_cncl;
    val _ = #stop tbc_progress_reporter ();
    (* Every TBC-proven auxiliary fact must be established on pst_orig itself before either
       branch below: AbductionProver's own subsequent graph search may reference them by name
       via "using" in its own generated proofs (it searches against pst_tbc, whose context
       already has them, but the script it hands back still needs them to genuinely exist when
       replayed against pst_orig), and if TBC preprocessing alone solved the goal, the final
       script itself may reference them the same way. *)
    val _ = solve_trace "  tbc preprocessing done";
    (* The same rewrite suggest's emission goes through (see run_abduction_search): scripts name
       the facts they need, unneeded auxiliaries are dropped, and the facts are then established
       plain rather than as simp rules. tbc_fact_names reaches the graph replay below for the
       same reason it reaches the graph printers. *)
    val (emitted_nodes, tbc_fact_names) =
      Proof_By_Abduction.explicitize_tbc_pnodes pst_tbc preprocessed_nodes;
    val pst_with_tbc_aux =
      apply_safely (fn () =>
        Proof_By_Abduction.apply_tbc_prelude_aux_to_pst pst_orig emitted_nodes);
    (* solve reached none of this before: write_verdict was called from run_abduction_search,
       which prove/prove_by_abduction/suggest go through and run_solve_body does not. So the one
       command that closes a goal in a real proof reported nothing a harness could read - the same
       gap, one command over, that made "PROVED" mean "compiled" for two evaluations.

       Written at each of the four points where the outcome is decided, rather than around the
       whole body, because three of them are successes by different routes and the fourth raises.
       A run killed by the memory guard writes no row at all, which is honest: the search did not
       reach a verdict, and an absent row is not a claim. *)
    fun verdict (solved:bool) =
      Top_Down_Util.write_verdict_applied (Proof.context_of pst_orig) solved
        (Time.toReal (#elapsed (Timing.result start)));
  in
    if TBC_Utils.original_goal_is_proved preprocessed_nodes
    then
      (solve_trace "  PATH: tbc proved the final goal itself";
       verdict true;
       apply_safely (fn () =>
         Proof_By_Abduction.apply_tbc_final_to_pst rename_mapping pst_with_tbc_aux
           emitted_nodes))
    else
    case Proof_By_Abduction.proved_alias_of_goal (Proof.context_of pst0) standardized_cncl
           preprocessed_nodes of
      (* TBC already proved this very statement, under a conjecture's name rather than the
         final goal's. Use it instead of searching for what we have. *)
      SOME alias =>
        (solve_trace ("  PATH: goal already proved as conjecture " ^ alias);
         verdict true;
         apply_safely (fn () =>
           Proof_By_Abduction.apply_proved_alias_to_pst rename_mapping pst_with_tbc_aux alias))
    | NONE =>
      let
        val _ = solve_trace "  PATH: entering graph search";
        val (solved, captured) =
          Proof_By_Abduction.search_for_subgoal_and_capture_graph tbc_fact_names pst_tbc start
            standardized_cncl;
        val _ = solve_trace ("  graph search returned: solved=" ^ Bool.toString solved);
      in
        case (solved, captured) of
          (true, SOME (ag, name2term, goal_name)) =>
            (solve_trace "  entering replay";
             (* Recorded before the replay, and deliberately: the verdict is about whether the
                SEARCH found a proof. A replay that then fails is a separate failure, it raises,
                and it is not evidence that the goal was unprovable - conflating the two is how
                the var_0 collision would read as a capability loss. *)
             verdict true;
             apply_safely (fn () =>
               Proof_By_Abduction.apply_graph_proof_to_pst
                 rename_mapping tbc_fact_names pst_with_tbc_aux ag name2term goal_name)
             before solve_trace "  replay done")
        | _ =>
            (case Synchronized.value root_cex of
               SOME why =>
                 (Top_Down_Util.write_verdict_refuted (Proof.context_of pst_orig)
                    (Time.toReal (#elapsed (Timing.result start)));
                  error ("solve: the goal itself has a genuine counterexample (" ^ why
                         ^ ").\nThe goal is unchanged, and no proof exists to search for."))
             | NONE =>
                 (verdict false;
                  error ("solve: AbductionProver could not find a proof for this subgoal.\n"
                         ^ "Try suggest instead to see whatever progress it made.")))
      end
  end;

(* run_solve *)
(* solve's search under the same memory monitor that prove and suggest already ran under.
 *
 * It was not. with_memory_monitor wrapped run_abduction_search only, which prove and suggest go
 * through; run_solve has its own search path and ran unguarded - so the one command a user
 * actually drives interactively, and the one every scenario test uses, had no ceiling at all.
 * Measured: TIP_prop_06 under solve was killed outright (SIGKILL, no Isabelle-level error),
 * which is precisely the outcome the monitor exists to replace with a clean stop.
 *
 * A breach cancels the search, so the result is an interrupt rather than a proof. That is
 * reported as what it is - the goal is not proved and the state is unchanged - rather than
 * being allowed to surface as a bare interrupt attributed to whatever ran next. *)
fun run_solve (pst_orig:Proof.state): bool * Proof.state =
  (* Same search slot and same entry GC as run_abduction_search, for the same reasons: proof
     blocks are forked, so solve commands overlap each other and every suggest/prove in flight,
     and the floor below is derived from MemAvailable, which dropped garbage from earlier
     searches depresses until a full GC hands it back. *)
  let
    val search_limit =
      Config.get (Proof.context_of pst_orig) Resource_Limit.max_parallel_searches;
    val _ =
      if Resource_Limit.search_slots_in_use () >= Int.max (1, search_limit)
      then tracing ("AbductionProver: waiting for an earlier search in this session to finish"
                    ^ " before starting this one (max_parallel_searches = "
                    ^ Int.toString (Int.max (1, search_limit)) ^ ").")
      else ()
  in
  Resource_Limit.with_search_slot search_limit
    (fn () =>
  let
    val _ = ML_Heap.full_gc ();
    val start = Timing.start ();
    val ctxt = Proof.context_of pst_orig;
    val _ = Top_Down_Util.warn_if_proof_output_dir_unset ();
    val root_cex = Synchronized.var "root_refutation_result_solve" (NONE: string option);
    val watchdog_holder = Unsynchronized.ref (NONE: unit future option);
    (* solve honours prove_timeout the same way the theorem commands do. Without this the deadline
       is simply never set on this path, and an unset deadline never reports as passed, so the
       round driver's check in TBC_Utils cannot fire and prove_timeout bounds nothing here - which
       is why the same declaration bounds "prove" but not "solve". Cleared below, on every exit,
       so a later command does not inherit a deadline set for this one. *)
    val _ = Resource_Limit.set_deadline_in (Config.get ctxt Top_Down_Util.timeout_config);
    val (outcome, stopped_because) =
      Proof_By_Abduction.with_memory_monitor
        (Proof_By_Abduction.configured_floor ctxt)
        Proof_By_Abduction.memory_status_message
        (fn stop_search => run_solve_body stop_search root_cex watchdog_holder pst_orig);
    val _ = Resource_Limit.clear_deadline ();
    (* Every exit passes here, so a slow nitpick cannot outlive the search slot; harmless when
       the watchdog already finished or died with a cancelled group. *)
    val _ =
      case Unsynchronized.! watchdog_holder of
        SOME watchdog => Future.cancel watchdog
      | NONE => ();
    val _ = solve_trace ("  run_solve: monitor returned, outcome = "
              ^ (case outcome of Exn.Res _ => "Res" | Exn.Exn e => "Exn " ^ Runtime.exn_message e)
              ^ ", reason = " ^ (case stopped_because of NONE => "none" | SOME w => w));
    (* The watchdog's stop escalated to a hard cancel before run_solve_body could write its
       refuted row: write it here, for the same webservice runner the suggest path serves. *)
    val _ =
      case (outcome, Synchronized.value root_cex) of
        (Exn.Exn _, SOME _) =>
          Top_Down_Util.write_verdict_refuted ctxt (Time.toReal (#elapsed (Timing.result start)))
      | _ => ();
  in
    case (outcome, stopped_because) of
      (Exn.Res result, _) =>
        (case Synchronized.value root_cex of
           NONE => result
         | SOME why =>
             (warning ("solve closed a goal the refutation watchdog also refuted (" ^ why
                       ^ "). One of the two is unsound; please report this goal.");
              result))
      (* The monitor's own reason, not a fresh probe of memory: by the time the search has
         unwound, memory has usually recovered, so probing again reported everything as fine and
         the user saw a bare "Interrupt" for a search we had deliberately stopped. *)
    | (Exn.Exn _, SOME why) =>
        (case Synchronized.value root_cex of
           SOME _ => error ("solve: " ^ why ^ "\nThe goal is unchanged.")
         | NONE =>
             error ("solve: " ^ why ^ "\nThe goal is unchanged. Lower the floor with"
                    ^ " declare [[min_free_mb = ...]] if the machine can spare it, or try suggest,"
                    ^ " which discards the search's state as it goes."))
    | (Exn.Exn exn, NONE) => Exn.reraise exn
  end)
  end;

(* solve_local/global/combined *)
(* Registered as local_arm o global_arm, exactly Isar_Cmd.done_proof's own pattern
 * (local_done_proof o global_done_proof, Pure/Isar/isar_cmd.ML): Toplevel.end_proof's built-in
 * Proof.assert_bottom precheck raises Runtime.UNDEF and falls through to the local (nested) arm
 * whenever pst_orig is not at bottom, exactly as for real "done". But that precheck only knows
 * about bottom-ness, not backward-ness - pst_orig can be at bottom yet not backward (the third
 * case documented at run_solve above), in which case run_solve handles the closing itself
 * internally (via apply_root_steps opening and closing its own "show ?thesis" wrapper) and
 * returns false, since solve is then not actually the command responsible for the
 * outer proof's own close. The global arm below checks assert_backward itself, before ever
 * calling run_solve, specifically to detect this case cheaply and fall through to the local arm
 * without redundantly repeating the (potentially slow) search there too - run_solve then still
 * only ever actually runs once per command. *)
(* probe_pending_interrupt *)
(* Diagnostic, off unless PSL_SOLVE_PROBE is set. Consumes any interrupt left pending on this
 * thread and says so.
 *
 * It exists to test one specific explanation for a failure mode that no trace could otherwise
 * reach: "solve" completes, every step of it is traced to the end, and the build then fails with
 * a positionless "*** Interrupt" that belongs to no command. Future.worker_exec ends every task
 * with Isabelle_Thread.expose_interrupt_result, and cancels the task's whole group if it finds
 * an interrupt pending - so an interrupt we left behind is not delivered to us at all. It is
 * delivered to whatever group encloses us, which in a batch build is the theory's own. If
 * consuming it here makes the failures stop, that is the mechanism. *)
fun probe_pending_interrupt (where_:string): unit =
  case getenv "PSL_SOLVE_PROBE" of
    "" => ()
  | _ =>
      let val pending = Isabelle_Thread.expose_interrupt_result () in
        solve_trace ("  probe at " ^ where_ ^ ": "
                     ^ (if Exn.is_interrupt_exn pending then "INTERRUPT WAS PENDING"
                        else "nothing pending"))
      end;

val solve_local =
  Toplevel.proof (fn pst =>
    case run_solve pst of
      (true, result) =>
        (solve_trace "  solve_local: closing with local_done_proof";
         Proof.local_done_proof result
         before solve_trace "  solve_local: closed"
         before probe_pending_interrupt "end of solve_local")
    | (false, result) =>
        (solve_trace "  solve_local: already closed";
         probe_pending_interrupt "end of solve_local";
         result));
val solve_global =
  Toplevel.end_proof (fn _ => fn pst =>
    if not (can Proof.assert_backward pst) then raise Runtime.UNDEF
    else
      case run_solve pst of
        (true, result) => Proof.global_done_proof result
      | (false, _) => raise Runtime.UNDEF);
val solve_combined = solve_local o solve_global;

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "prove with the combo prover" true;
val _ =
  theorem \<^command_keyword>\<open>prove_by_abduction\<close>
    "prove by Pure AbductionProver" false;
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>suggest\<close>
    "try AbductionProver on the current subgoal, wherever a proof is open, and print a \
    \suggested script"
    (Scan.succeed (Toplevel.keep_proof suggest_command));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>solve\<close>
    "try AbductionProver on the current subgoal, wherever a proof is open, and automatically \
    \close it if successful"
    (Scan.succeed solve_combined);

end;
\<close>

end