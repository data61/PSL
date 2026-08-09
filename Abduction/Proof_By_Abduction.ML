(*  Title:      Abduction/Proof_By_Abduction.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

The main search procedure and Isar command implementing AbductionProver.
*)
(*** PROOF_BY_ABDUCTION ***)
signature PROOF_BY_ABDUCTION =
sig

(* Where a suggestion will be pasted, which determines the shape it must take. Shared with
   TBC_Utils, which also emits suggestions and must agree; see assemble_suggestion there. *)
type caller_context = TBC_Utils.caller_context;

(* Guards the search consults before growing: the memory counterpart of the timeout check.
   Exposed so the behaviour can be tested and reported on directly. *)
(* The guard's decision logic, kept pure and exported so it can be tested without a machine
   actually running out of memory: given the previous and current readings it says whether to
   carry on. Everything time-, thread- and /proc-related stays in with_memory_monitor. *)
datatype memory_verdict = Memory_Ok | Memory_Urgent of string | Memory_Low of string;
val memory_verdict:
  {floor_mb: real, poll_seconds: real, reaction_budget_seconds: real,
   confirmation_seconds: real} ->
  {recent: real list, available: real, consecutive_below: int} -> memory_verdict;

(* Establishes one auxiliary "have" from a graph node on a live Proof.state, renumbering its
   variables from the given offset. Exported so the renumbering can be tested directly: reaching
   this path through a real search needs a goal whose auxiliaries the graph search invents, which
   takes tens of minutes and does not reliably happen at all. *)
val apply_have_of_key:
  strings -> Abduction_Graph.abduction_graph -> int -> Abduction_Graph.key -> Proof.state ->
  Proof.state;
(* Parses one "using"-clause name into a Facts.ref. Exported so the selection syntax it has to
   understand - "foo(2)", "foo(1-3)" - can be tested without driving a whole replay. *)
val parse_fact_ref: Proof.context -> string -> Facts.ref;
(* Which variables an auxiliary "have" should fix. Pure, and exported so the rule can be
   tested directly: re-fixing a variable the surrounding proof already fixed shadows it rather
   than naming it, which quietly makes the auxiliary fact about a different variable. *)
val fixes_for_have: Proof.context -> term -> (binding * string option * mixfix) list;

val still_has_memory: real -> bool;
val configured_floor: Proof.context -> real;
val memory_status_message: unit -> string;
(* Runs body under the memory monitor. The second component of the result is the reason the
   monitor stopped the work, when it did - a caller that turns the outcome into a message needs
   to know that the interrupt it is holding was ours, and cannot find out by re-probing memory,
   which has usually recovered by the time the search has unwound.

   The body receives the monitor's own stop function: record this reason, then wind the search
   down the vetted way (Resource_Limit.request_stop, a grace, the soft group cancel, the
   escalation - see stop_the_search). It exists so that a watcher the body forks - the root
   refutation watchdog below - stops the search through exactly the machinery the guard uses,
   rather than through a second, unvetted cancellation path. *)
val with_memory_monitor:
  real -> (unit -> string) -> ((string -> unit) -> 'a) -> 'a Exn.result * string option;

(* Does the root goal itself have a genuine counterexample? Quickcheck first, then nitpick,
   each under its own config budget (Top_Down_Util.refute_root_*_timeout; <= 0 disables one).
   Only GENUINE counterexamples count - spurious/potential results, timeouts and tool failures
   all report NONE, same semantics as PSL's assertion tactics (Subtool.ML). The string names
   the tool and, for quickcheck, the counterexample itself. *)
val refute_root: Proof.state -> term -> string option;

(* Forks refute_root beside the search (inside the monitored group, so the guard sees its
   memory and a cancelled search takes it down too). On a counterexample it records the
   message in the given var and stops the search via the passed stop function. The caller
   cancels the returned future once the search is over, so a slow nitpick does not outlive
   the search slot. *)
val fork_root_refutation_watchdog:
  (string -> unit) -> string option Synchronized.var -> Proof.state -> term -> unit future;

(* Periodic progress snapshots to the Output pane and <theory>_progress.thy - see the
   implementation comment. Takes the phase's name and a snapshot closure ("" for "nothing
   proved yet"); the graph phase forks its own internally, the entry points fork one over
   TBC_Utils.progress_pnodes for the preprocessing phase. *)
val fork_progress_reporter:
  Proof.state -> Timing.start -> string -> (unit -> string) -> {stop: unit -> unit};

(* The strings argument running through the entry points below is the names of the
   TBC-preprocessed auxiliary facts the search context holds as simp rules
   (TBC_Utils.assume_term_in_ctxt): every emitted script's simp-consuming step names the ones
   it may have used, so the emitted text carries its dependencies explicitly instead of
   relying on the pasted block re-creating the search's simp set. See explicitize_tbc_pnodes. *)
val proof_by_abduction: Proof.state -> Timing.start -> term -> bool;
val proof_by_abduction_with_prelude:
  strings -> string -> Proof.state -> Timing.start -> term -> bool;
val proof_by_abduction_for_subgoal:
  caller_context -> (string * string) list -> Proof.state -> Timing.start -> term -> bool;
val proof_by_abduction_for_subgoal_with_prelude:
  caller_context -> (string * string) list -> strings -> string -> Proof.state -> Timing.start ->
  term -> bool;
val write_proof_script_in_result_file: Proof.state -> string -> unit;
val write_suggestion_beside_theory: Proof.context -> string -> unit;
val emit_proof_script: Proof.state -> string -> string;
val search_for_subgoal_and_capture_graph:
  strings -> Proof.state -> Timing.start -> term ->
  bool * (Abduction_Graph.abduction_graph * term Symtab.table * string) option;
val apply_graph_proof_to_pst:
  (string * string) list -> strings -> Proof.state -> Abduction_Graph.abduction_graph ->
  term Symtab.table -> string -> bool * Proof.state;
val apply_tbc_prelude_aux_to_pst: Proof.state -> TBC_Utils.pnodes -> Proof.state;
(* Rewrites TBC preprocessing's proved pnodes so every script names the auxiliary facts it
   needs and drops the auxiliaries nothing needs; returns the nodes to emit or replay, and the
   names of the surviving simp-bag facts for the graph-script printers above. Both suggest's
   emission and solve's replay go through this, so the two cannot disagree. *)
val explicitize_tbc_pnodes: Proof.state -> TBC_Utils.pnodes -> TBC_Utils.pnodes * strings;
(* A conjecture TBC proved that turns out to be the goal itself, and how to close the goal with
   it. See proved_alias_of_goal for why this happens. *)
val proved_alias_of_goal: Proof.context -> term -> TBC_Utils.pnodes -> string option;
val apply_proved_alias_to_pst:
  (string * string) list -> Proof.state -> string -> bool * Proof.state;
val apply_tbc_final_to_pst:
  (string * string) list -> Proof.state -> TBC_Utils.pnodes -> bool * Proof.state;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type state = Proof.state;

type caller_context = TBC_Utils.caller_context;

open Abduction_Graph;

structure SOOE = Seed_Of_Or2And_Edge;
structure SS   = Shared_State;
structure AG   = Abduction_Graph;
structure TDU  = Top_Down_Util;
structure ATDC = All_Top_Down_Conjecturing;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_or2and_edge  = SOOE.seed_of_or2and_edge;
type seeds_of_or2and_edge = SOOE.seeds_of_or2and_edge;

(* expand_ornode *)
fun prove_standard_simp_rules
  (pst:state,
   synched_agraph: SS.synched_abduction_graph,
   refutation    : SS.synched_term2real_table,
   term2name     : SS.synched_term2string_table,
   proved_simps  : SS.synched_proved_simps,
   filter_stats  : SS.synched_filter_statistics,
   orig_prems    : terms)
  (lemma_term:term): unit =
  let
    (*top-down explicit conjecturing*)
    val ctxt = Proof.context_of pst: Proof.context;
    val graph                      = SS.value_of_graph synched_agraph: abduction_graph;
    val condition_to_filter_out    =
      SOOE.condition_to_filter_out_conjecture filter_stats lemma_term refutation orig_prems pst
        graph false o snd
      : string * term -> bool;
    val explicit_conjectures       =
      ATDC.template_based_conjecture_for_simplification term2name ctxt lemma_term
      : (string * term) list;
    val filtered_explicit          =
      TDU.parallel_filter_out condition_to_filter_out explicit_conjectures: (string * term) list;
    val refute                     = Shared_State.is_refuted refutation pst o snd
                                      : (string * term) -> bool;
    val explicit_wo_counterexample =
      TDU.parallel_filter_out refute filtered_explicit: (string * term) list;
    fun prove_save_in_shared_state (lem_name:string, lem_term:term) =
      let
        (*expensive*)
        val maybe_prf = prove_term_completely pst lem_term: strings option;
      in
        if is_none maybe_prf then ()
        else SS.add_proved_simp proved_simps (lem_name, lem_term)
      end;
    val _ = Par_List.map prove_save_in_shared_state explicit_wo_counterexample: unit list;
  in
    ()
  end;

(* expand_ornode *)
fun expand_ornode_if_original_goal_is_unproved
  (top_loop_index:int)
  (pst:state,
   synched_agraph: SS.synched_abduction_graph,
   refutation    : SS.synched_term2real_table,
   term2name     : SS.synched_term2string_table,
   proved_simps  : SS.synched_proved_simps,
   filter_stats  : SS.synched_filter_statistics,
   orig_prems    : terms)
  (or_key as (Or_N, [lemma_term]):key): bool =
    let
      (*tactic application as conjecturing. A little expensive*)
      val pst_to_prove                 = TDU.mk_pst_to_prove_from_term pst lemma_term: state;
      val seeds_from_tactics           =
        SOOE.apply_PSL_to_get_seeds_of_or2and_edges (term2name, refutation) pst pst_to_prove
        : seeds_of_or2and_edge;
      val graph_extended_by_conjecture = SS.value_of_graph synched_agraph: abduction_graph;
      val filtered_seeds_from_tactics  =
        SOOE.filter_out_bad_seeds_from_tactic filter_stats lemma_term refutation orig_prems pst
          graph_extended_by_conjecture seeds_from_tactics
      val tactics_seeds_wo_counterexam =
        filter_out (SOOE.seed_has_counterexample refutation pst) filtered_seeds_from_tactics
        : seeds_of_or2and_edge;
      val _                            =
        SOOE.abduction_for_tactic_based_conjectures pst or_key tactics_seeds_wo_counterexam
          synched_agraph
        : unit;

      val graph                      = SS.value_of_graph synched_agraph: abduction_graph;
      (*top-down explicit conjecturing*)
      val explicit_conjectures       =
        All_Top_Down_Conjecturing.top_down_conjectures term2name pst lemma_term
        : (string * term) list;
      val condition_to_filter_out    =
        SOOE.condition_to_filter_out_conjecture filter_stats lemma_term refutation orig_prems pst
          graph false o snd
        : string * term -> bool;
      val filtered_explicit          =
        TDU.parallel_filter_out condition_to_filter_out explicit_conjectures
        : (string * term) list;
      val explicit_wo_counterexample =
        TDU.parallel_filter_out (Shared_State.is_refuted refutation pst o snd) filtered_explicit
        : (string * term) list;
      val seed_from_explicit         =
        SOOE.conjectures_to_seed_of_or2and_edge term2name pst explicit_wo_counterexample
        : seed_of_or2and_edge;
      val explicit_cnjnctrs          = #new_goals seed_from_explicit: SOOE.conjectures;
      val ctxt                       = Proof.context_of pst: Proof.context;
      (*TODO: simp_explicit_conjecture should move to All_Top_Down_Conjecturing?*)
      fun simp_explicit_conjecture
            (simp as (_:string, simp_term:term))
            (cnjctr as (cnjctr_name:string, cnjctr_term:term)): SOOE.conjectures =
        let
          val simp_thm = TDU.term_to_thm ctxt simp_term: thm;
          val ctxt_w_simp = Simplifier.add_simp simp_thm ctxt: Proof.context;
          val simplifier = Basic_Simplifier.simplify ctxt_w_simp: thm -> thm;(*asm_full_simplify*)
          val simplifier_w_timeout =
            try (Isabelle_Utils.timeout_apply (Time.fromSeconds 1) simplifier): thm -> thm option;
          val cnjctr_thm = TDU.term_to_thm ctxt cnjctr_term: thm;
          val simped_cnjctr = simplifier_w_timeout cnjctr_thm: thm option;
          (*TODO: Can I do something better than this?*)
          fun schematic_to_free (Var ((str, _), typ)) =
            let
              val vname = space_explode "." str |> hd
            in Free (vname, typ)
            end
            | schematic_to_free aterm = aterm;
          fun remove_schematic (term:term) = (map_aterms schematic_to_free term);
        in
          if   is_none simped_cnjctr
          then [cnjctr]
          else
            let
              val rm_Trueprop = Top_Down_Util.remove_Trueprop o Isabelle_Utils.strip_atyp;
              val simped_cnjctr_term = the simped_cnjctr |> Thm.full_prop_of
                 |> remove_schematic
              val simped_cnjctr_name    =
                SS.get_lemma_name term2name ctxt ("simped_" ^ cnjctr_name) simped_cnjctr_term
                : string;
              val size_of_simped_cnjctr = Term.size_of_term (rm_Trueprop simped_cnjctr_term): int;
              val size_of_orig_cnjctr   = Term.size_of_term (rm_Trueprop cnjctr_term): int;
            in
              if size_of_simped_cnjctr >= size_of_orig_cnjctr
                 (*orelse simped_cnjctr_term = @{term True}*)
                 (*orelse rm_Trueprop simped_cnjctr_term = rm_Trueprop lemma_term*)
              then [cnjctr]
              else [simp, (simped_cnjctr_name, simped_cnjctr_term)](*TODO: not efficient.*)
            end
        end;
      fun simp_explicit_conjectures_for_one_rule
            (simp:SOOE.conjecture) (cnjctrs:SOOE.conjectures): SOOE.conjectures =
          map (simp_explicit_conjecture simp) cnjctrs |> flat |> distinct (op =);
      fun simp_explicit_conjectures_for_many_rules
            (cnjctrs:SOOE.conjectures) (simps:SOOE.conjectures) =
          fold simp_explicit_conjectures_for_one_rule simps cnjctrs: SOOE.conjectures;
      val simps                        = Synchronized.value proved_simps: SS.proved_simps;
      val (tb_cnjctrs, td_cnjctrs)     =
        List.partition (TDU.is_template_based o fst) explicit_cnjnctrs
        : (SOOE.conjectures * SOOE.conjectures);
      val simped_explicit_conjectures  =
        simp_explicit_conjectures_for_many_rules td_cnjctrs simps: SOOE.conjectures;
      val tb_and_simped_conjectures    = tb_cnjctrs @ simped_explicit_conjectures
      val standardized_conjectures     =
        map (apsnd Top_Down_Util.standardize_vnames) tb_and_simped_conjectures
        |> distinct (op =)(*TODO: should it be done here?*)
      val _                            =
        SOOE.abduction_for_explicit_conjectures pst top_loop_index or_key standardized_conjectures
          (term2name, refutation, synched_agraph, proved_simps, filter_stats)
        : unit;
    in
      SS.final_goal_proved_completely synched_agraph
    end
  | expand_ornode_if_original_goal_is_unproved _ _ _ = error "expand_ornode failed. Not an Or_N.";

fun get_timeout (pst:Proof.state) =
  Config.get (Proof.context_of pst) Top_Down_Util.timeout_config: real;
fun current_time (start:Timing.start) = Time.toReal (#elapsed (Timing.result start)): real;
fun still_has_time (start:Timing.start) (pst:Proof.state) =
  current_time start < get_timeout pst: bool;

(* still_has_memory *)
(* The memory counterpart of still_has_time, and used in exactly the same places: a guard the
 * search consults before claiming more work, so that running out of memory ends the search the
 * way running out of time does - with whatever has been proved so far - instead of the whole
 * Isabelle process being destroyed.
 *
 * This has to live inside the prover rather than in the evaluation harness. A batch run can be
 * given an ML heap ceiling in $ISABELLE_HOME_USER/etc/settings, but somebody has to remember to
 * do it, and an interactive jEdit user invoking prove_by_abduction/suggest/solve never will.
 * When the search is left unguarded, the failure is not a polite error: 149 runs of the recorded
 * TIP15 evaluation were killed outright, either by the OS OOM killer or by Poly/ML's own "Run
 * out of store", losing every partial result.
 *
 * Two independent signals, because neither alone is sufficient:
 *
 *   - Free system memory. This is what actually decides whether the OOM killer fires, and it
 *     accounts for everything else in the picture: the ~1.5GB Isabelle JVM, the external provers
 *     Sledgehammer runs concurrently (measured: a single veriT reaching 6.35GB), and any other
 *     process on the machine. Read from /proc/meminfo, so Linux only.
 *   - The Poly/ML heap itself, via PolyML.Statistics. This is portable, and it is the signal
 *     that matters when the ML heap is approaching a limit of its own (the x86_64_32 platform
 *     tops out well below the machine's RAM) rather than the machine running dry.
 *
 * Both are deliberately fail-open: if /proc/meminfo cannot be read, or the statistics call
 * fails, the corresponding check passes. A misfiring guard that silently truncates searches
 * would be worse than the problem it prevents, so anything unmeasurable is treated as fine.
 *
 * The floor is the min_free_mb config attribute (declare [[min_free_mb = 4000]]); 0 means
 * derive it from the machine, and a negative value disables the check. *)
(* still_has_memory takes the floor as an argument rather than reading it itself: the monitor
 * runs on a plain Isabelle_Thread with no Proof.context, so the value has to be resolved from
 * the context once, where the search starts, and carried in. A floor of 0 disables the check. *)
local
  (* The floor has to absorb everything that can be allocated between one poll and the next,
   * and the collapse is far faster than intuition suggests. Measured on an 11GB machine, free
   * memory fell from 2574MB to 328MB inside a single four-second sampling window - and in
   * bursts it is faster still, because one diverging external prover can claim gigabytes at
   * once (a single veriT was seen at 6.35GB).
   *
   * This was calibrated the hard way. Two earlier floors, max(1536MB, RAM/8) and then
   * max(2048MB, RAM/5), never fired at all: the process was killed while free memory was still
   * above them, because it crossed the floor and hit zero between polls. A floor of 4500MB on
   * that same machine does fire, cancels, and the run exits cleanly.
   *
   * The quantity that matters is an absolute headroom - roughly what numb_of_processors workers
   * and their provers can grab in a moment - not a fraction of RAM, which is why the base is a
   * constant and the proportional term only takes over on large machines. *)
  (* The floor is what must stay FREE, and it is derived from the memory that was actually
   * available when the search began - not from the machine's total.
   *
   * A fraction of total is wrong whenever the session is already heavy. Importing a large
   * theory hierarchy (the AFP being the obvious case) can leave only a few gigabytes free
   * before AbductionProver starts, and a floor sized against total RAM then either forbids the
   * search from using memory it could safely have, or on a big machine sits so high that it
   * refuses to start at all. Sizing against what the search was actually given adapts to both.
   *
   * The absolute minimum still applies underneath, because a fraction of a small baseline is
   * not a safe floor: if only 800MB were free to begin with, a fifth of that leaves no room for
   * the JVM, the external provers, or the operating system. *)
  fun derived_floor_from (baseline_available_mb: real): real =
    Real.max (1024.0, baseline_available_mb * 0.2);

in

(* Memory sensing lives in PSL/Resource_Limit.ML, which is portable across Linux, macOS and
 * Windows. An earlier version read /proc directly from here, which silently degraded to
 * "always fine" on any non-Linux machine - exactly the interactive jEdit case this exists for. *)
fun still_has_memory (floor_mb: real): bool =
  if floor_mb < 0.0 then true (*disabled*)
  else
    (* configured_floor always hands over a concrete number, so 0 cannot reach here; treat it
       defensively as "derive from whatever is free now" rather than as no floor at all. *)
    case Resource_Limit.available_mb () of
      NONE => true (*unprobeable platform: fail open*)
    | SOME avail =>
        avail > (if floor_mb > 0.0 then floor_mb else derived_floor_from avail);

(* Resolve the configured floor once, in a context, for handing to the monitor - which runs on
   a plain thread with no context of its own. 0 (the default) means "derive from the machine";
   a negative value disables the check. The result is always the effective number of megabytes
   that must stay free, so callers never have to know about the 0 convention. *)
fun configured_floor (ctxt: Proof.context): real =
  let val configured = Config.get ctxt Resource_Limit.min_free_mb in
    if configured <> 0 then Real.fromInt configured
    else
      case Resource_Limit.available_mb () of
        SOME baseline => derived_floor_from baseline
      | NONE => 1024.0
  end;

end;

fun memory_status_message (): string = Resource_Limit.status_message ();

(* memory_verdict *)
(* A level threshold alone cannot serve both goals, and tuning one proved the point. A floor of
 * 4608MB free on a 12GB machine - 58% usable - fired 51 times during a Prod A/B, aborting
 * healthy searches while the ML process held only 1.3GB. Cutting it to 20% free (80% usable)
 * dropped that to 3 firings but let a hard kill back in.
 *
 * The level is the wrong signal on its own: what kills the process is memory disappearing
 * faster than the guard reacts, measured falling from 2574MB to 328MB inside four seconds. So
 * the primary trigger is projected time-to-exhaustion. Memory sitting low but stable no longer
 * aborts anything; memory falling fast fires while there is still room to unwind, even when the
 * absolute level still looks comfortable.
 *
 * Three tiers, cheapest first. *)
datatype memory_verdict = Memory_Ok | Memory_Urgent of string | Memory_Low of string;

fun memory_verdict
      {floor_mb: real, poll_seconds: real, reaction_budget_seconds: real,
       confirmation_seconds: real}
      {recent: real list, available: real, consecutive_below: int} =
  let
    val critical_floor = floor_mb / 2.0;
    (* The rate is measured across the whole window rather than between the last two readings.
     * A single delta is dominated by ordinary allocation churn: measured on a Prod run, all 36
     * spurious aborts came from momentary rates of 1000-1200MB/s that a two-sample estimate
     * treated as a trend. Averaging over the window turns those back into noise while a genuine
     * collapse, which is sustained, still registers. *)
    val window_seconds = Real.fromInt (length recent) * poll_seconds;
    val falling_per_second =
      case recent of
        [] => 0.0
      | _ =>
          if window_seconds <= 0.0 then 0.0
          else Real.max (0.0, (List.last recent - available) / window_seconds);
    val seconds_left =
      if falling_per_second <= 0.0 then Real.posInf else available / falling_per_second;
    (* The projection only counts near the edge. Far from it, "falling fast" is a normal
     * consequence of working hard, not a warning: the same Prod run fired at 6200-6450MB free -
     * over two and a half times the floor - while nothing was going wrong. The real collapse
     * that this guard exists to catch began at 1.2 times the floor. *)
    val near_the_edge = available < floor_mb * 2.0;
  in
    if available < critical_floor then Memory_Low "critically low"
    (* Urgent, not fatal. The projection says there is little headroom left, but a projection is
     * not an observation: a burst of allocation that is freed again produces exactly this
     * reading. On a small machine working hard it produces it constantly - measured on a 12GB
     * host, every one of twenty runs was stopped here at 1.9-3.5GB free while the same runs had
     * completed successfully before the guard was applied to solve at all. The monitor requires
     * this to persist across polls before acting; a real collapse keeps saying it, a burst does
     * not. *)
    (* Waiting for confirmation is only an option when there is time to collect it. The urgent
       tier below asks for the projection to persist across several polls before acting, which
       costs confirmation_seconds - and a collapse steeper than that will be over before the
       monitor has made up its mind. Measured on a 12GB host: 1034MB free falling 845MB/s, about
       1.2 seconds, against 1.5 seconds of confirmation. Two of the three runs of that problem
       never got a verdict at all and died with the search still running.

       So: when the projection says we will not survive long enough to confirm it, treat it as
       confirmed. Everything the urgent tier protects against still applies elsewhere - this
       tier needs the same near-the-edge gate and the same window-averaged rate, and it fires
       only when both say the machine is about to run out within a poll or two. *)
    else if near_the_edge andalso seconds_left < confirmation_seconds
    then Memory_Low ("falling " ^ Real.fmt (StringCvt.FIX (SOME 0)) falling_per_second
                     ^ "MB/s, about " ^ Real.fmt (StringCvt.FIX (SOME 1)) seconds_left
                     ^ "s of headroom left - too fast to wait for confirmation")
    else if near_the_edge andalso seconds_left < reaction_budget_seconds
    then Memory_Urgent ("falling " ^ Real.fmt (StringCvt.FIX (SOME 0)) falling_per_second
                        ^ "MB/s, about " ^ Real.fmt (StringCvt.FIX (SOME 1)) seconds_left
                        ^ "s of headroom left")
    else if available < floor_mb andalso consecutive_below + 1 >= 4
    then Memory_Low "below the floor and staying there"
    else Memory_Ok
  end;

(* with_memory_monitor *)
(* Runs body while a dedicated thread watches free memory, and aborts the work if it runs low.
 *
 * Polling from inside the search itself was tried first and does not work. The check sat in
 * run_worker_pool's worker_loop, consulted before a worker claims its next OR-node, but the
 * allocation happens *inside* expand_ornode - conjecturing, counterexample checking, and
 * Sledgehammer with its external provers - which runs for seconds to minutes. With every worker
 * inside an expansion nobody returns to the check, so on the target that reproduces the failure
 * the guard never fired once and the process was still killed (exit 137 at 97s, against 85s
 * unguarded). Forcing the predicate to be false outright did not stop the search either, since
 * TBC preprocessing runs before the loop is even entered.
 *
 * Hence a monitor that is not part of the work. Two properties matter:
 *
 *   - It is an Isabelle_Thread, not a future. A future that sleeps would occupy one of the
 *     threads=N worker slots for the whole search, which is precisely the mistake that made the
 *     first worker-pool implementation slower than the loop it replaced (see
 *     Shared_State.synched_work_queue).
 *   - On breach it cancels a task group rather than politely asking anything to stop. Refusing
 *     to hand out new work is useless when the memory is being consumed by expansions already
 *     in flight; cancellation propagates to sub-groups, so the forked expansions inside each
 *     worker are interrupted too.
 *
 * Cancelling loses the work in flight. That is the point: losing a search's partial progress is
 * better than losing the Isabelle process, which is what happens otherwise. *)
fun with_memory_monitor (floor_mb: real) (describe: unit -> string)
    (body: (string -> unit) -> 'a)
    : 'a Exn.result * string option =
  let
    (* The body runs on the *calling* thread, inside a task context belonging to a group the
     * monitor owns, so cancelling that group still interrupts it.
     *
     * Two wrong versions came before this. Passing in a group and simply running the body is a
     * trap - the group is empty, so the cancellation is a silent no-op. Forking the body into
     * the group instead does make cancellation work, but nests a future group inside whatever
     * task the enclosing "solve"/"prove" command is already running in, and that intermittently
     * corrupted Isabelle's interrupt handling: a theory with several searches in it failed
     * about half the time with a bare "Interrupt" or "Interrupt_Breakdown" attributed to an
     * unrelated command. Bypassing the wrapper entirely made those failures vanish, which is
     * what identified it. Future.task_context gives the cancellable group without the nested
     * fork.
     *
     * NONE as the parent was suspected (2026-08-08) of stranding the search's forked work when
     * jEdit cancels the enclosing command: the command's group does not contain this one, so
     * cancelling it reaches only the calling thread. Tested, and the suspicion was wrong: the
     * interrupt fails the task that task_context enrolled here, and a task failing cancels its
     * own group, so the search's forks die with the command anyway - parentage plays no part.
     * Search_Slot_Test pins exactly that (a monitored body's forked child must not outlive the
     * command's cancellation), so if this mechanism ever changes, the build says so. Parenting
     * the group to the command's was tried, passed the same test, and was reverted as an
     * unjustified perturbation of code whose interrupt behaviour has already produced
     * intermittent failures once. *)
    val group = Future.new_group NONE;
    val running = Synchronized.var "abduction_memory_monitor_running" true;
    (* Why the reason is recorded rather than reported here: the monitor is a plain thread with
     * no task context, and Isabelle routes messages by task. A warning raised from it reaches
     * neither jEdit's Output pane nor the batch log - which is why the failure was invisible
     * until PSL_MEMORY_MONITOR_LOG was added to work around it. The calling thread does have a
     * context, so it reports once the search has unwound. *)
    val stop_reason = Synchronized.var "abduction_memory_monitor_reason" (NONE: string option);
    val poll_interval = seconds 0.5;
    val poll_seconds = 0.5;
    (* Cancelling and unwinding is not instant, and the provers have to die too. *)
    val reaction_budget_seconds = 6.0;
    (* How many consecutive urgent polls before acting on a projection. Three is 1.5s of
       sustained decline near the floor: long enough that a burst which is freed again has
       stopped saying it, short enough to leave the reaction budget intact. memory_verdict is
       told how long that confirmation costs, because a collapse faster than that has to be
       acted on without it. *)
    val urgent_polls_before_acting = 3;
    val params =
      {floor_mb = floor_mb, poll_seconds = poll_seconds,
       reaction_budget_seconds = reaction_budget_seconds,
       confirmation_seconds = poll_seconds * Real.fromInt urgent_polls_before_acting};

    val window = 6;  (*three seconds of history at a half-second poll*)
    (* stop_the_search *)
    (* Ask, then stop the group taking on new work - without interrupting anyone.
     *
     * The request goes out first (Resource_Limit.request_stop). The search's own loops check it
     * where they already check the clock and free memory - between OR-node expansions, and between
     * conjecture attempts - and wind down by themselves.
     *
     * What follows the grace period used to be Future.cancel_group, and that was the defect. It is
     * two things welded together (Future.cancel_now):
     *
     *     val running = Task_Queue.cancel (! queue) group;
     *     val _ = running |> List.app (fn thread => ... Isabelle_Thread.interrupt_thread thread);
     *
     * The first line marks the group, which is the part we want: a marked group's queued tasks are
     * skipped when they reach the front (Task_Queue.dequeue tests is_canceled). The second
     * interrupts the *shared worker threads* running the group's tasks, and an interrupt landing on
     * a worker that has already moved on is what Isabelle reports as Interrupt_Breakdown. Measured
     * on a 12GB host: 6 of the 12 position-matrix runs in which this guard fired died that way,
     * across five of the six Isar positions - a guard whose whole purpose is to replace an abrupt
     * death with a clean message, causing one half the time it acted.
     *
     * Task_Queue.cancel_group is the first line's marking on its own: group-local, no queue
     * argument, its own lock, and public in TASK_QUEUE. So the marking is available without the
     * interrupting, and Soft_Cancel_Test establishes what it buys - work already running is left
     * alone and still delivers its value, work not yet started is skipped, and the group reports as
     * cancelled.
     *
     * The soft stop is not enough on its own, and the hard one is therefore kept as an escalation
     * rather than deleted. A prover is an external process, and interrupting the thread waiting on
     * it is what kills it: Isabelle_System.bash_process runs in an uninterruptible body whose
     * handler is "kill maybe_uuid; Exn.reraise exn", so the interrupt the hard cancel delivers is
     * what sends server_kill to the bash server. Nothing in the soft stop does that, so an attempt
     * already inside a diverging prover keeps allocating until its own --max-time expires - and
     * measured on one stock Sledgehammer call, veriT alone peaked at 6.1GB. Trading a breakdown
     * for an OOM would not be a trade.
     *
     * So: soft first, which is free and stops the search *growing*; hard only if memory keeps
     * falling afterwards, where the alternative is losing the session anyway. The point is to make
     * the hard cancel rare rather than universal - it currently fires on every one of the 12
     * position-matrix runs in which the guard acted, and breaks the session in half of them. *)
    val grace_before_cancelling = seconds 3.0;
    (* How long to watch after the soft stop, and how far below the floor is an emergency. Falling
       past half the floor with the search already told to stop means something is not listening -
       a prover that will not return - and at that point the breakdown risk is the lesser one. *)
    val emergency_window = seconds 10.0;
    val emergency_floor_mb = Real.max (256.0, floor_mb * 0.5);
    fun escalate_if_still_falling (waited: real) =
      (* The window is a grace for the soft stop to take effect, not an escape from stopping. An
         earlier version simply returned here, so a search whose memory fell slowly enough to stay
         above the emergency floor for the whole window was left running under the soft mark alone
         - which is exactly the configuration measured to end in an OS OOM kill: 524s, SIGKILL, no
         guard message. If the search is still going when the window closes, it has not taken the
         hint and the hard cancel is what is left. *)
      if waited >= Time.toReal emergency_window
      then
        if Synchronized.value running
        then (TBC_Utils.tbc_trace
                "  monitor: soft stop did not take within the window; cancelling hard";
              Future.cancel_group group)
        else ()
      else if not (Synchronized.value running) then ()   (*the search let go by itself*)
      else
        case Resource_Limit.available_mb () of
          SOME avail =>
            if avail < emergency_floor_mb
            then
              (TBC_Utils.tbc_trace ("  monitor: soft stop did not hold (" ^ Real.toString avail
                                    ^ "MB < " ^ Real.toString emergency_floor_mb
                                    ^ "MB); cancelling hard");
               Future.cancel_group group)
            else (OS.Process.sleep poll_interval;
                  escalate_if_still_falling (waited + poll_seconds))
        | NONE => ();
    fun stop_the_search () =
      (Resource_Limit.request_stop ();
       OS.Process.sleep grace_before_cancelling;
       if Synchronized.value running
       then (Task_Queue.cancel_group group Isabelle_Thread.interrupt;
             escalate_if_still_falling 0.0)
       else ());

    (* The one place a stop is recorded and acted on, so every route to it reports identically.
       PSL_MEMORY_MONITOR_LOG appends the event to a file as well: Isabelle's batch build does not
       surface warning/tracing from a plain Isabelle_Thread, so without this there is no way to
       tell "the guard fired and cancelled" apart from "the search happened to finish first" - an
       ambiguity that already caused one run to be misread as a success.

       stop_now takes the finished message: it is also handed to the body (see the signature),
       whose watchers stop the search for reasons that are not about memory, so the memory
       phrasing lives with the memory callers in stop_low_memory below. *)
    fun stop_now (msg: string) =
      let
        val _ =
          case getenv "PSL_MEMORY_MONITOR_LOG" of
            "" => ()
          | path => ignore (try (File.append (Path.explode path)) (msg ^ "\n"));
      in
        (Synchronized.change stop_reason (K (SOME msg)); stop_the_search ())
      end;

    fun stop_low_memory (why: string) =
      stop_now ("AbductionProver stopping early: running low on memory (" ^ describe ()
                ^ "; " ^ why ^ "). Returning what has been proved so far.");

    (* PSL_MEMORY_GUARD_TRIP_AFTER=<seconds>: trip the guard after that long whatever memory says.
       Off unless set, like the other diagnostics.

       It exists because the defect the guard is up against is a race between the hard cancel and
       the conjecture attempts still inside their provers, so reproducing it means controlling
       *when* the cancel lands - and that cannot be done by choosing a floor. A floor high enough
       to trip at all trips in round 0, before there is any parallel work to race with; a floor
       low enough to trip mid-round is not reachable by picking a number, because the build's own
       footprint moves the target between runs. Both were tried. *)
    fun forced_trip () =
      case getenv "PSL_MEMORY_GUARD_TRIP_AFTER" of
        "" => false
      | s =>
          (case Real.fromString s of
             NONE => false
           | SOME secs =>
               let
                 (*Waited out in slices rather than one sleep, so a search that finishes before the
                   trip time does not then wait for the monitor to wake up before it can join it.*)
                 fun wait (left: real) =
                   if not (Synchronized.value running) then ()
                   else if left <= 0.0
                   then stop_low_memory ("forced after " ^ s ^ "s by PSL_MEMORY_GUARD_TRIP_AFTER")
                   else (OS.Process.sleep poll_interval; wait (left - poll_seconds));
               in
                 (wait secs; true)
               end);

    fun poll (recent: real list) (consecutive: int) (urgent: int) =
      if not (Synchronized.value running) then ()
      else if floor_mb < 0.0 then () (*disabled*)
      else
        case Resource_Limit.available_mb () of
          NONE => (OS.Process.sleep poll_interval; poll [] 0 0) (*unprobeable: fail open*)
        | SOME avail =>
            (case memory_verdict params
                    {recent = recent, available = avail, consecutive_below = consecutive} of
               Memory_Ok =>
                 (OS.Process.sleep poll_interval;
                  poll (take window (avail :: recent))
                       (if avail < floor_mb then consecutive + 1 else 0)
                       0)
             | Memory_Urgent why =>
                 if urgent + 1 >= urgent_polls_before_acting
                 then stop_low_memory (why ^ ", sustained")
                 else
                   (OS.Process.sleep poll_interval;
                    poll (take window (avail :: recent))
                         (if avail < floor_mb then consecutive + 1 else 0)
                         (urgent + 1))
             | Memory_Low why => stop_low_memory why);
    val _ = Resource_Limit.clear_stop_request ();
    val monitor =
      Isabelle_Thread.fork (Isabelle_Thread.params "abduction_memory_monitor")
        (fn () => if forced_trip () then () else poll [] 0 0);
    val result = Exn.capture (Future.task_context "abduction_search" group (fn () => body stop_now)) ();
    val _ = TBC_Utils.tbc_trace ("  monitor: body returned "
              ^ (case result of Exn.Res _ => "Res" | Exn.Exn e => "Exn " ^ Runtime.exn_message e));
    (* Shut the monitor down by clearing its flag and waiting for it to notice, rather than by
     * interrupting it. Isabelle_Thread.interrupt_thread was tried first and is a trap: the
     * monitor spends its life in Synchronized.value and Resource_Limit.available_mb, so an
     * interrupt can land while it holds a lock, and the resulting damage surfaces later as a
     * bare "Interrupt" in an unrelated part of the theory. That failure was intermittent - two
     * runs in three - and took a theory with three searches in it to reproduce at all.
     *
     * The flag is checked once per poll interval, so the join costs at most that. *)
    val _ = Synchronized.change running (K false);
    val _ = TBC_Utils.tbc_trace "  monitor: flag cleared, joining monitor thread";
    val _ = Isabelle_Thread.join monitor;
    val _ = TBC_Utils.tbc_trace "  monitor: joined";
    val reason = Synchronized.value stop_reason;
    (* An interrupt this function caused, taken as a value at the boundary where it was caused.
     *
     * Future.cancel_group interrupts the threads running the group's tasks, and Poly/ML
     * delivers asynchronously, so an interrupt aimed at the search can arrive after the search
     * has already unwound - on this thread, with nothing left to receive it. Isabelle then
     * reports it as Interrupt_Breakdown, which is its name for a raw interrupt on a thread
     * whose break flag was never set (Isabelle_Thread.make_interrupt): an interrupt nobody
     * asked for. Measured on a 12GB host, two runs of TIP_prop_06 died exactly that way, from
     * a guard whose entire purpose is to replace an abrupt death with a clean message.
     *
     * This is Timeout.apply's own move, for the same reason and with the same care. It records
     * independently whether it caused the interrupt - there, whether its timer fired; here,
     * whether the monitor recorded a stop reason - and only then consumes it. If we did not
     * cause it, it is somebody's genuine interrupt and is released unchanged. *)
    val pending = Isabelle_Thread.expose_interrupt_result ();
    val _ =
      case reason of
        SOME _ => TBC_Utils.tbc_trace ("  monitor: stopped by the guard; pending interrupt = "
                                       ^ Bool.toString (Exn.is_interrupt_exn pending))
      | NONE => Exn.release pending;
    (* Emitted here, on the thread that owns the command, so interactive users actually see why
     * the search stopped instead of it appearing to have simply given up. *)
    val _ = case reason of NONE => () | SOME msg => warning msg;
  in
    (result, reason)
  end;

(* refute_root *)
(* Quickcheck and nitpick on the root goal itself. TBC already spends one or two seconds of
 * these tools on every generated conjecture (TBC_Utils.pst_n_conjecture_has_counterexample);
 * this is the same idea aimed at the one term whose falsehood wastes the entire prove_timeout.
 *
 * Called directly rather than through the Quick_Pick strategy, deliberately: the strategy
 * interface erases which tool refuted and what the counterexample was, and both belong in the
 * output a webservice runner or a jEdit user sees. The genuine-only semantics is copied from
 * the strategy's building blocks (Subtool.ML): quickcheck's spurious counterexamples, either
 * tool timing out, and either tool crashing all report "not refuted" - a watchdog that stops
 * a search over a maybe would be worse than no watchdog. try re-raises interrupts, so
 * cancelling the watchdog future does not read as "no counterexample". *)
fun refute_root (pst: Proof.state) (cncl: term): string option =
  let
    val ctxt = Proof.context_of pst;
    val quickcheck_budget = Config.get ctxt Top_Down_Util.refute_root_quickcheck_timeout;
    val nitpick_budget = Config.get ctxt Top_Down_Util.refute_root_nitpick_timeout;
    val goal_pst = Proof.theorem NONE (K I) [[(cncl, [])]] ctxt;
    fun render_cex [] = "counterexample found, no bindings reported"
      | render_cex bindings =
          commas (map (fn (x, t) => x ^ " = " ^ Isabelle_Utils.trm_to_string ctxt t) bindings);
    (* Each tool's outcome as a word plus its own wall seconds, kept separately from the
       user-facing message: the external consumer asked for a bounded per-tool record to
       calibrate the budgets against real goals, after establishing that their own wall
       numbers contain guest boot and session load and can never be made to answer "was that
       quickcheck or nitpick". Timeout and error are distinguished from "none": a tool that
       ran out of budget says so, which is the calibration signal. Interrupts re-raise - a
       cancelled watchdog must not read as "no counterexample". *)
    fun timed_outcome (budget: real) (run: unit -> 'a) (classify: 'a -> string * string option)
        : {outcome: string, cex: string option, secs: real} =
      if budget <= 0.0 then {outcome = "disabled", cex = NONE, secs = 0.0}
      else
        let
          val tool_start = Timing.start ();
          val result = Exn.capture (fn () => Timeout.apply (seconds budget) run ()) ();
          val secs = Time.toReal (#elapsed (Timing.result tool_start));
        in
          case result of
            Exn.Res r => let val (outcome, cex) = classify r in
                           {outcome = outcome, cex = cex, secs = secs} end
          | Exn.Exn e =>
              if Exn.is_interrupt e then Exn.reraise e
              else {outcome = (case e of Timeout.TIMEOUT _ => "timeout" | _ => "error"),
                    cex = NONE, secs = secs}
        end;
    val qc =
      timed_outcome quickcheck_budget
        (fn () => Quickcheck.quickcheck [] 1 goal_pst)
        (fn SOME (true, bindings) => ("genuine", SOME (render_cex bindings))
          | SOME (false, _) => ("spurious", NONE)
          | NONE => ("none", NONE));
    (* Auto_Try mode, not Normal, and for the returned messages rather than the try-tool
       aesthetics: Normal mode writelns the model and returns an empty list, Auto_Try
       captures the pretty-printed model into the list (nitpick.ML's outcome queue). Without
       it, the one case where quickcheck failed and the visitor most needs to see WHY their
       statement is false said only "see nitpick's own output" - the first consumer's last
       gap. The rendering is approximate by design: whitespace-flattened and bounded, good
       enough to put in front of a person. *)
    fun render_nitpick_model (msgs: string list): string =
      let
        val flat =
          msgs
          (*Pretty.string_of outside PIDE yields YXML-markup-laden text; content_of strips it
            to what a person should see. Measured: without this the line read
            "blocktext_foldblockblockAutobreak..." where it should read "Free variable: n = 0".*)
          |> map (XML.content_of o YXML.parse_body)
          |> map (fn s => String.concatWith " " (String.tokens Char.isSpace s))
          |> String.concatWith " | ";
      in
        if flat = "" then "genuine model found, but nitpick returned no rendering"
        else if size flat > 600 then String.substring (flat, 0, 600) ^ " (truncated)"
        else flat
      end;
    val np =
      if is_some (#cex qc)
      then {outcome = "not run: quickcheck refuted", cex = NONE, secs = 0.0}
      else
        timed_outcome nitpick_budget
          (fn () =>
             Nitpick.pick_nits_in_subgoal goal_pst
               (Nitpick_Commands.default_params (Proof.theory_of pst) [])
               Nitpick.Auto_Try 1 1)
          (fn (outcome, msgs) =>
             if outcome = Nitpick.genuineN
             then ("genuine", SOME (render_nitpick_model msgs))
             else (outcome, NONE));
    fun fmt_secs s = Real.fmt (StringCvt.FIX (SOME 1)) s;
    val report_lines =
      ["quickcheck: " ^ #outcome qc ^ " in " ^ fmt_secs (#secs qc) ^ "s",
       "nitpick: " ^ #outcome np ^
       (if String.isPrefix "not run" (#outcome np) orelse #outcome np = "disabled"
        then "" else " in " ^ fmt_secs (#secs np) ^ "s")]
      @ (case (#cex qc, #cex np) of
           (SOME c, _) => ["counterexample: " ^ c]
         | (_, SOME c) => ["counterexample: " ^ c]
         | _ => []);
    (* Bounded by construction on the consumer's behalf: their guest returns one small output
       disk, and an overflow costs the visitor's actual result. *)
    val report_text =
      let val text = cat_lines report_lines ^ "\n" in
        if size text <= 4000 then text
        else String.substring (text, 0, 4000) ^ "\n(truncated)\n"
      end;
    val _ =
      case getenv "PSL_PROOF_OUTPUT_DIR" of
        "" => ()
      | dir =>
          let
            val base = Context.theory_base_name (Proof_Context.theory_of ctxt);
            val tmp = Path.explode (dir ^ "/" ^ base ^ "_refutation.txt.tmp");
            val final = Path.explode (dir ^ "/" ^ base ^ "_refutation.txt");
          in
            ignore (try (fn () =>
              (File.write tmp report_text;
               OS.FileSys.rename {old = Path.implode tmp, new = Path.implode final})) ())
          end;
  in
    case #cex qc of
      SOME c => SOME ("quickcheck: " ^ c)
    | NONE =>
        (case #cex np of
           SOME m => SOME ("nitpick: " ^ m)
         | NONE => NONE)
  end;

(* fork_root_refutation_watchdog *)
(* Runs refute_root beside the search instead of in front of it, so a true goal pays nothing:
 * the check needs no result before the search may start, and a false goal stops the search
 * whenever the counterexample lands. Forked with Future.fork from the body's own thread, so
 * it lives in the monitored group - the memory guard sees nitpick's appetite, and a search
 * cancelled for any reason takes the watchdog down with it.
 *
 * The stop goes through the monitor's stop_now: reason recorded where with_memory_monitor
 * reports it, then Resource_Limit.request_stop, the grace, the soft Task_Queue.cancel_group,
 * and the escalation - the one cancellation path this codebase has vetted (see AGENTS.md on
 * the guard). The message is recorded in the caller's var BEFORE the stop, so the verdict
 * writer can tell "refuted" from "stopped for memory" whichever way the search unwinds. *)
fun fork_root_refutation_watchdog (stop: string -> unit) (cex: string option Synchronized.var)
    (pst: Proof.state) (cncl: term): unit future =
  Future.fork (fn () =>
    case refute_root pst cncl of
      NONE => ()
    | SOME why =>
        (Synchronized.change cex (K (SOME why));
         (*CONTRACT: the two phrases below - "refutation watchdog:" in the trace and
           "The goal itself has a genuine counterexample (" in the message - are anchors the
           Heinzelmen service greps to extract the counterexample for its visitors (anchoring
           on the word "counterexample" alone would match the search's OWN refuted
           conjectures). Coordinate with the service before rewording either. *)
         TBC_Utils.tbc_trace ("  refutation watchdog: " ^ why);
         stop ("The goal itself has a genuine counterexample (" ^ why
               ^ "). Stopping the proof search: there is nothing to prove.")));

fun expand_ornode_if_original_goal_is_unproved_w_timeout
      (start:Timing.start) (top_loop_index:int)
      (pst:state, synched_agraph, refutation, term2name, proved_simps, filter_stats, orig_prems)
      (or_key as (Or_N, [_]):key): bool =
    if   Time.toReal (#elapsed (Timing.result start)) < get_timeout pst
    then
      (*Why Future? Because Timeout.apply alone cannot be trusted.*)
      Future.fork
       (fn () =>
          (SS.update_is_branch or_key synched_agraph: unit;
           expand_ornode_if_original_goal_is_unproved top_loop_index)
            (pst, synched_agraph, refutation, term2name, proved_simps, filter_stats, orig_prems)
            or_key)
    |> (fn f => Timeout.apply (Time.fromSeconds 600) Future.join f
        handle Timeout.TIMEOUT _ =>
          (tracing "Timeout from expand_ornode_if_original_goal_is_unproved_w_timeout"; false))
    else false
| expand_ornode_if_original_goal_is_unproved_w_timeout _ _ _ _ =
    error "expand_ornode_if_original_goral_is_unproved_w_timeout failed.";

(* record_loop_statistics *)
(* Factored out of loop's own body unchanged (still called from there, in exactly the same
 * shape as before) so that run_worker_pool's refill step - the closest analog to a "round" in
 * the new, continuously-draining worker-pool design - can record the same statistics too. The
 * graph-frontier quantities passed in describe the state at the beginning of a round/refill,
 * whereas the refutation-cache statistics computed here describe the cumulative cache state as
 * of whenever this function actually runs (after the round/refill's own selection, before any
 * of the newly-selected nodes have themselves been attacked). *)
fun record_loop_statistics
    (pst:state) (synched_statistics: Abduction_Statistics.synched_statistics)
    (synched_agraph: SS.synched_abduction_graph) (refutation: SS.synched_term2real_table)
    (filter_stats: SS.synched_filter_statistics) (start:Timing.start)
    (top_loop_round:int) (reachable_count:int) (reachable_or_count:int)
    (reachable_orleaf_count:int) (worth_expanding_count:int) (selected_count:int)
    (numb_of_processors:int): unit =
  if Abduction_Statistics.enabled ()
  then
    let
      fun rate numerator denominator =
        if denominator = 0 then 0.0
        else Real.fromInt numerator / Real.fromInt denominator;
      val graph_after_loop = SS.value_of_graph synched_agraph: Abduction_Graph.abduction_graph;
      val {nodes_total = graph_nodes,
           edges_total = graph_edges,
           or_nodes = graph_or_nodes,
           and_nodes = graph_and_nodes,
           or2and_edge_nodes = graph_or2and_edge_nodes,
           avg_indegree = graph_avg_indegree,
           max_indegree = graph_max_indegree,
           scc_count = graph_scc_count,
           cyclic_scc_count = graph_cyclic_scc_count,
           largest_scc_size = graph_largest_scc_size,
           or_projected_edges = graph_or_projected_edges,
           or_projected_avg_indegree = graph_or_projected_avg_indegree,
           or_projected_max_indegree = graph_or_projected_max_indegree,
           or_projected_scc_count = graph_or_projected_scc_count,
           or_projected_cyclic_scc_count = graph_or_projected_cyclic_scc_count,
           or_projected_largest_scc_size = graph_or_projected_largest_scc_size,
           and_projected_edges = graph_and_projected_edges,
           and_projected_avg_indegree = graph_and_projected_avg_indegree,
           and_projected_max_indegree = graph_and_projected_max_indegree,
           and_projected_scc_count = graph_and_projected_scc_count,
           and_projected_cyclic_scc_count = graph_and_projected_cyclic_scc_count,
           and_projected_largest_scc_size = graph_and_projected_largest_scc_size} =
        Abduction_Graph.graph_profile graph_after_loop;
      val {node_attempts = graph_node_attempts,
           nodes_created = graph_nodes_created,
           node_reuses = graph_node_reuses,
           ornode_attempts = graph_ornode_attempts,
           ornodes_created = graph_ornodes_created,
           ornodes_reused = graph_ornodes_reused,
           andnode_attempts = graph_andnode_attempts,
           andnodes_created = graph_andnodes_created,
           andnodes_reused = graph_andnodes_reused,
           edge_node_attempts = graph_edge_node_attempts,
           edge_nodes_created = graph_edge_nodes_created,
           edge_nodes_reused = graph_edge_nodes_reused,
           edge_attempts = graph_edge_attempts,
           edges_created = graph_edges_created,
           edge_reuses = graph_edge_reuses,
           or_expansion_attempts = or_expansion_attempts,
           or_expansions_started = or_expansions_started} =
        SS.graph_update_statistics synched_agraph;
      val {size = ref_cache_size, hits = ref_cache_hits, misses = ref_cache_misses} =
        SS.refutation_cache_statistics refutation;
      val ref_cache_total        = ref_cache_hits + ref_cache_misses;
      val ref_cache_hit_rate     = rate ref_cache_hits ref_cache_total;
      val {refutation_checked = filter_refutation_checked,
           refutation_refuted = filter_refutation_refuted,
           refutation_survived = filter_refutation_survived,
           abduction_checked_conjectures = filter_abduction_checked_conjectures,
           abduction_used_conjectures = filter_abduction_used_conjectures,
           abduction_discarded_conjectures = filter_abduction_discarded_conjectures,
           orelse_rejected_conjectures = filter_orelse_rejected_conjectures,
           orelse_too_large = filter_orelse_too_large,
           orelse_eq_to_final_goal_from_tactic = filter_orelse_eq_to_final_goal_from_tactic,
           orelse_concl_is_eq_to_final_goal = filter_orelse_concl_is_eq_to_final_goal,
           orelse_has_func_with_three_occs_in_a_row = filter_orelse_has_func_with_three_occs_in_a_row,
           orelse_concls_are_same = filter_orelse_concls_are_same,
           orelse_concl_of_conj_refuted = filter_orelse_concl_of_conj_refuted,
           top_loop_index = _} = SS.filter_statistics_snapshot filter_stats;
      val filter_refutation_survival_rate = rate filter_refutation_survived filter_refutation_checked;
      val filter_abduction_retention_rate =
        rate filter_abduction_used_conjectures filter_abduction_checked_conjectures;
      val _                      = Abduction_Statistics.record_loop pst synched_statistics
                                    {depth = top_loop_round,
                                     reachable_keys = reachable_count,
                                     reachable_or_nodes = reachable_or_count,
                                     reachable_or_leaf_nodes = reachable_orleaf_count,
                                     worth_expanding = worth_expanding_count,
                                     selected_ornodes = selected_count,
                                     selection_rate = rate selected_count worth_expanding_count,
                                     num_processors = numb_of_processors,
                                     graph_nodes = graph_nodes,
                                     graph_edges = graph_edges,
                                     graph_or_nodes = graph_or_nodes,
                                     graph_and_nodes = graph_and_nodes,
                                     graph_or2and_edge_nodes = graph_or2and_edge_nodes,
                                     graph_avg_indegree = graph_avg_indegree,
                                     graph_max_indegree = graph_max_indegree,
                                     graph_scc_count = graph_scc_count,
                                     graph_cyclic_scc_count = graph_cyclic_scc_count,
                                     graph_largest_scc_size = graph_largest_scc_size,
                                     graph_or_projected_edges = graph_or_projected_edges,
                                     graph_or_projected_avg_indegree = graph_or_projected_avg_indegree,
                                     graph_or_projected_max_indegree = graph_or_projected_max_indegree,
                                     graph_or_projected_scc_count = graph_or_projected_scc_count,
                                     graph_or_projected_cyclic_scc_count =
                                       graph_or_projected_cyclic_scc_count,
                                     graph_or_projected_largest_scc_size =
                                       graph_or_projected_largest_scc_size,
                                     graph_and_projected_edges = graph_and_projected_edges,
                                     graph_and_projected_avg_indegree =
                                       graph_and_projected_avg_indegree,
                                     graph_and_projected_max_indegree =
                                       graph_and_projected_max_indegree,
                                     graph_and_projected_scc_count = graph_and_projected_scc_count,
                                     graph_and_projected_cyclic_scc_count =
                                       graph_and_projected_cyclic_scc_count,
                                     graph_and_projected_largest_scc_size =
                                       graph_and_projected_largest_scc_size,
                                     graph_node_attempts = graph_node_attempts,
                                     graph_nodes_created = graph_nodes_created,
                                     graph_node_reuses = graph_node_reuses,
                                     graph_node_reuse_rate = rate graph_node_reuses graph_node_attempts,
                                     graph_ornode_attempts = graph_ornode_attempts,
                                     graph_ornodes_created = graph_ornodes_created,
                                     graph_ornodes_reused = graph_ornodes_reused,
                                     graph_ornode_reuse_rate =
                                       rate graph_ornodes_reused graph_ornode_attempts,
                                     graph_andnode_attempts = graph_andnode_attempts,
                                     graph_andnodes_created = graph_andnodes_created,
                                     graph_andnodes_reused = graph_andnodes_reused,
                                     graph_andnode_reuse_rate =
                                       rate graph_andnodes_reused graph_andnode_attempts,
                                     graph_edge_node_attempts = graph_edge_node_attempts,
                                     graph_edge_nodes_created = graph_edge_nodes_created,
                                     graph_edge_nodes_reused = graph_edge_nodes_reused,
                                     graph_edge_node_reuse_rate =
                                       rate graph_edge_nodes_reused graph_edge_node_attempts,
                                     graph_edge_attempts = graph_edge_attempts,
                                     graph_edges_created = graph_edges_created,
                                     graph_edge_reuses = graph_edge_reuses,
                                     graph_edge_reuse_rate = rate graph_edge_reuses graph_edge_attempts,
                                     or_expansion_attempts = or_expansion_attempts,
                                     or_expansions_started = or_expansions_started,
                                     or_expansion_reuse_rate =
                                       rate (or_expansion_attempts - or_expansions_started)
                                            or_expansion_attempts,
                                     refutation_cache_size = ref_cache_size,
                                     refutation_cache_hits = ref_cache_hits,
                                     refutation_cache_misses = ref_cache_misses,
                                     refutation_cache_hit_rate = ref_cache_hit_rate,
                                     filter_refutation_checked = filter_refutation_checked,
                                     filter_refutation_refuted = filter_refutation_refuted,
                                     filter_refutation_survived = filter_refutation_survived,
                                     filter_refutation_survival_rate = filter_refutation_survival_rate,
                                     filter_abduction_checked_conjectures =
                                       filter_abduction_checked_conjectures,
                                     filter_abduction_used_conjectures =
                                       filter_abduction_used_conjectures,
                                     filter_abduction_discarded_conjectures =
                                       filter_abduction_discarded_conjectures,
                                     filter_abduction_retention_rate = filter_abduction_retention_rate,
                                     filter_orelse_rejected_conjectures =
                                       filter_orelse_rejected_conjectures,
                                     filter_orelse_too_large = filter_orelse_too_large,
                                     filter_orelse_eq_to_final_goal_from_tactic =
                                       filter_orelse_eq_to_final_goal_from_tactic,
                                     filter_orelse_concl_is_eq_to_final_goal =
                                       filter_orelse_concl_is_eq_to_final_goal,
                                     filter_orelse_has_func_with_three_occs_in_a_row =
                                       filter_orelse_has_func_with_three_occs_in_a_row,
                                     filter_orelse_concls_are_same = filter_orelse_concls_are_same,
                                     filter_orelse_concl_of_conj_refuted =
                                       filter_orelse_concl_of_conj_refuted,
                                     elapsed_sec = current_time start};
    in
      ()
    end
  else ();

(* loop *)
fun loop (counter:int) (max_depth:int) (start:Timing.start)
    (synched_statistics: Abduction_Statistics.synched_statistics)
    (quintuple as
    (pst:state,
     synched_agraph: SS.synched_abduction_graph,
     refutation:SS.synched_term2real_table,
     term2name:SS.synched_term2string_table,
     proved_simps:SS.synched_proved_simps,
     filter_stats:SS.synched_filter_statistics,
     orig_prems: terms)) =
  (* still_has_memory guards this path too: loop is still reachable via
   * PSL_EVAL_USE_WORKER_POOL_LOOP=0, and a rollback switch that reintroduces hard kills would
   * be a poor rollback. *)
  if counter < 15 andalso still_has_time start pst
     andalso still_has_memory (configured_floor (Proof.context_of pst))
  then
    let
      val top_loop_round         = counter + 1: int;
      val _                      =
        tracing ("==== In loop. The depth is: " ^ Int.toString counter ^ ". =====");
      val _                      = SS.reset_filter_statistics_for_loop filter_stats top_loop_round;
      val ctxt                   = Proof.context_of pst;
      val abduction_graph        =
        SS.value_of_graph synched_agraph: Abduction_Graph.abduction_graph;
      val (orkeys_worth_expanding, frontier_counts) =
        orkeys_tobe_expanded_in_with_reachable_count ctxt abduction_graph;
      val {reachable_keys = reachable_count,
           reachable_or_nodes = reachable_or_count,
           reachable_or_leaf_nodes = reachable_orleaf_count} = frontier_counts;
      val sorted_orkeys          =
        sort_orkeys_based_on_importance abduction_graph orkeys_worth_expanding: keys;
      val worth_expanding_count  = length sorted_orkeys: int;
      val _                      =
        tracing ("The number of keys worth expanding is:" ^
                 Int.toString worth_expanding_count ^ ".");
      val _                      = tracing "They are:"
      val _                      = map (print_orkey ctxt abduction_graph) sorted_orkeys
      val expand_ornode          =
        expand_ornode_if_original_goal_is_unproved_w_timeout start top_loop_round
          (pst, synched_agraph, refutation, term2name, proved_simps, filter_stats, orig_prems)
        : Abduction_Graph.key -> bool;
      val numb_of_processors     = Thread.Thread.numProcessors ():int;
      val _                      =
        tracing ("numb_of_processors is " ^ Int.toString numb_of_processors ^ ".");
      val numb_of_nds_to_expand  = numb_of_processors;(*TODO: magic number*)
      val top_ornodes            = take numb_of_nds_to_expand sorted_orkeys: keys;
      val solved                 =
        if worth_expanding_count = 0
        then
          let
            val _ = tracing "No contributive OR-leaf node remains; terminating the abduction loop.";
          in
            false
          end
        else
          let
            val some_orkey = Par_List.find_some expand_ornode top_ornodes: key option;
            val solved = is_some some_orkey: bool;
            val _ =
              tracing ("We have " ^ (if solved then "already solved" else "not solve") ^
                       " the final goal.");
          in
            solved
          end;
      (*
       * Record loop statistics after the selected OR-nodes have been attacked.
       * The graph-frontier quantities above describe the state at the beginning of
       * this loop round, whereas the refutation-cache statistics below describe the
       * cumulative cache state after this loop round has completed.
       *)
      val _ =
        record_loop_statistics pst synched_statistics synched_agraph refutation filter_stats
          start top_loop_round reachable_count reachable_or_count reachable_orleaf_count
          worth_expanding_count (length top_ornodes) numb_of_processors;
    in
      if worth_expanding_count = 0
      then false
      else if solved then solved
      else loop (counter + 1) max_depth start synched_statistics quintuple
    end
  else
    false;

(* run_worker_pool *)
(* Replaces loop's own per-round bulk dispatch (Par_List.find_some over a fixed batch of
 * numb_of_processors OR-nodes, blocking until every one of them finishes before the next
 * round can even be selected) with numb_of_processors persistent workers continuously
 * draining a shared priority queue (SS.synched_work_queue) - see the type's own doc comment
 * (Shared_State.ML) for the full rationale: Par_List.find_some does correctly cancel a
 * round's stragglers early once one succeeds (confirmed empirically this session, via
 * Future.assign_result's group-cancellation-on-exception mechanism - not the problem), but
 * whichever of the N tasks in a round finishes first still has to sit idle until the round's
 * own slowest straggler finishes before the NEXT round can be selected at all - utilization
 * degrades toward the end of every round. Between refills here, all N workers can instead pick
 * up the next queued item the instant they finish their current one, no round barrier.
 *
 * Priorities are static (decided by AskUserQuestion with the user): fixed at the point a node
 * is pushed into the queue by a refill (do_refill, reusing orkeys_tobe_expanded_in_with_
 * reachable_count/sort_orkeys_based_on_importance completely unchanged), not continuously
 * re-ranked while sitting in the queue between refills. This keeps the refill's own expensive
 * whole-graph reachability walk paid once per batch, not once per item - the leading
 * hypothesis for why an earlier, from-scratch attempt at this same redesign ended up correct
 * but slower than the code it was replacing.
 *
 * Cancellation-on-success: unlike loop's own single Par_List.find_some call (one shared
 * exception-triggered group per round, entirely managed by Par_List/Future internally), there
 * is no single enclosing batch call here for N *persistent* workers to piggyback on. All N are
 * forked into one shared Future group up front specifically so that, the moment any one of
 * them finds the goal proved, Future.cancel_group can be called on it directly and explicitly.
 *
 * do_refill's own "genuinely exhausted, stop" check is deliberately based on
 * orkeys_worth_expanding (the graph scan's own raw result) rather than the batch actually
 * pushed into the queue: the pushed batch first filters out anything already in flight (a
 * concurrently-refilling queue can otherwise legitimately re-select a key another worker is
 * still mid-expanding, unlike the old per-round design, where a single round's own batch could
 * never contain the same key twice by construction) - a batch that comes back empty only
 * because everything currently worth trying is already claimed by another worker is not the
 * same as the search having nothing left at all, and must not stop the search early. *)
fun run_worker_pool (start:Timing.start)
    (synched_statistics: Abduction_Statistics.synched_statistics)
    (quintuple as
    (pst:state,
     synched_agraph: SS.synched_abduction_graph,
     refutation:SS.synched_term2real_table,
     term2name:SS.synched_term2string_table,
     proved_simps:SS.synched_proved_simps,
     filter_stats:SS.synched_filter_statistics,
     orig_prems: terms)): bool =
  let
    val qv                  = SS.mk_synched_work_queue ();
    val group                = Future.new_group NONE;
    val numb_of_processors   = Thread.Thread.numProcessors (): int;
    val found                = Synchronized.var "abduction_worker_pool_found" false;
    val round_index          = Synchronized.var "abduction_worker_pool_round" 0;

    fun next_round_index () =
      Synchronized.change_result round_index (fn n => (n + 1, n + 1)): int;

    fun do_refill () : unit =
      let
        val this_round        = next_round_index ();
        val ctxt               = Proof.context_of pst;
        val abduction_graph     = SS.value_of_graph synched_agraph: abduction_graph;
        val (orkeys_worth_expanding, frontier_counts) =
          orkeys_tobe_expanded_in_with_reachable_count ctxt abduction_graph;
        val {reachable_keys = reachable_count,
             reachable_or_nodes = reachable_or_count,
             reachable_or_leaf_nodes = reachable_orleaf_count} = frontier_counts;
        val worth_expanding_count = length orkeys_worth_expanding: int;
        val in_flight            = SS.currently_in_flight qv: keys;
        val fresh_orkeys          =
          orkeys_worth_expanding
          |> filter_out (fn k => exists (fn ik => equal_keys (k, ik)) in_flight): keys;
        val sorted_orkeys        =
          sort_orkeys_based_on_importance abduction_graph fresh_orkeys: keys;
        val batch                =
          map (fn k => (importance abduction_graph k, k)) sorted_orkeys: (real * key) list;
        val _ =
          record_loop_statistics pst synched_statistics synched_agraph refutation filter_stats
            start this_round reachable_count reachable_or_count reachable_orleaf_count
            worth_expanding_count (length batch) numb_of_processors;
        val _ = SS.complete_refill qv batch;
        val _ = if worth_expanding_count = 0 then SS.mark_stopped qv else ();
      in
        ()
      end;

    fun worker_loop () : unit =
      if not (still_has_time start pst) then SS.mark_stopped qv
      (* Same shape as the timeout guard, and for the same reason: stop claiming work and let
       * the search wind up with whatever it has proved, rather than being killed outright and
       * losing all of it.  Checked here, before a worker claims its next OR-node, because that
       * is the point at which the search decides to grow. *)
      else if not (still_has_memory (configured_floor (Proof.context_of pst))) then
        (tracing ("Abduction stops early: running low on memory (" ^ memory_status_message ()
                  ^ ").  Returning what has been proved so far.");
         SS.mark_stopped qv)
      (* The memory guard has asked the search to wind down. Honouring it here means the guard
         does not have to insist by cancelling - see stop_the_search. *)
      else if Resource_Limit.stop_is_requested () then
        (tracing "Abduction stops early: asked to stop by the memory guard.";
         SS.mark_stopped qv)
      else
        case SS.pop_or_request_refill qv of
          SS.Work_Stop => ()
        | SS.Work_Refill => (do_refill (); worker_loop ())
        | SS.Work_Item key =>
            let
              val this_round      = Synchronized.value round_index;
              val expand_ornode    =
                expand_ornode_if_original_goal_is_unproved_w_timeout start this_round
                  (pst, synched_agraph, refutation, term2name, proved_simps, filter_stats,
                   orig_prems)
                : key -> bool;
              val solved_this      = expand_ornode key: bool;
              val _                = SS.finish_item qv key;
            in
              if solved_this
              then
                (* Record the result and stop the queue, then RETURN. Two details matter.
                 *
                 * The worker must not carry on looping: it belongs to "group", and the earlier
                 * version cancelled that group here and then recursed, so the worker's own next
                 * interrupt-aware operation - joining the queue's wakeup promise - raised
                 * Interrupt on itself. That surfaced as a bare "Interrupt", or occasionally
                 * "Interrupt_Breakdown", attributed to whichever command happened to be
                 * running, and made a single solve fail about a quarter of the time.
                 *
                 * And cancellation is not needed to shut the pool down. mark_stopped makes
                 * every other worker receive Work_Stop as soon as it next asks for work, so
                 * they exit cleanly of their own accord; the only thing cancelling would add is
                 * interrupting expansions already in flight, and those are individually bounded
                 * by expand_ornode_if_original_goal_is_unproved_w_timeout anyway. Trading a
                 * little shutdown latency for not interrupting ourselves is plainly worth it. *)
                (Synchronized.change found (K true);
                 SS.mark_stopped qv)
              else worker_loop ()
            end;

    val workers =
      Future.forks
        {name = "abduction_worker", group = SOME group, deps = [], pri = 0, interrupts = true}
        (replicate numb_of_processors (fn () => worker_loop ()));
    val _ = Future.join_results workers;
    (* By the time every worker has returned, the queue's own final SS.mark_stopped call has
       already fulfilled every wakeup future it created except its own newest, freshly-installed
       one (see SS.mutate's doc comment) - nobody is or ever will be blocked on that last one, so
       cancelling the whole group here is pure cleanup (it is a no-op on the found=true path,
       where cancel_group was already called above) rather than something any worker depends on. *)
    val _ = Future.cancel_group group;
  in
    Synchronized.value found
  end;

type string2term_table = term Symtab.table;

fun insert_into_string2term
    (name:string, term:term) (string2term:string2term_table): string2term_table =
  Symtab.insert (op =) (name, term) string2term handle Symtab.DUP _ => string2term;

fun abduction_graph_to_string2term_table (ag:abduction_graph): string2term_table =
  let
    val or_keys     = keys ag |> filter is_ornode: keys;
    fun key_to_pair (key as (Or_N, [term])) = (lemma_name_of ag key, term)
      | key_to_pair _                       = error "abduction_graph_to_string2term_table failed.";
    val pairs       = map key_to_pair or_keys: (string * term) list;
    val string2term = fold insert_into_string2term pairs Symtab.empty: string2term_table;
  in
    string2term
  end;

(*rose tree to print proofs*)
datatype print_proof_tree = PPTree of (string * print_proof_tree list);

fun get_print_proof_tree
    (pst:Proof.state) (ag:abduction_graph) (name2term:string2term_table) (lemma_name:string) =
  let
    val lemma_term_opt = Symtab.lookup name2term lemma_name: term option;
  in
    if is_none lemma_term_opt
    then
      PPTree (lemma_name, []) (*The lemma was proved before calling our tool.*)
    else
      let
        val lemma_term       = the lemma_term_opt;
        val orkey            = (Or_N, [lemma_term]): Abduction_Graph.key;
        val proof            = Abduction_Graph.proof_of ag orkey |> String.concatWith " ": string;
        val thy              = Proof.theory_of pst: theory;
        val used_lemma_names = Top_Down_Util.get_lemma_names_from_sh_output thy proof: strings;
        val result           =
          PPTree (lemma_name, map (get_print_proof_tree pst ag name2term) used_lemma_names)
      in
        result
      end
  end;

fun order_pptree' (PPTree (lem_name, []  )) = [lem_name]: strings
  | order_pptree' (PPTree (lem_name, kids)) = flat (map order_pptree' kids) @ [lem_name];

(*note that "dtheoremistinct" preserves the order*)
fun order_pptree (pptree:print_proof_tree) = order_pptree' pptree |> distinct (op =);

(* for evaluation *)
fun write_proof_script_in_result_file pst what_to_write =
  let
    val ctxt = Proof.context_of pst;
    val eval_dir = getenv "PSL_EVAL_PROOF_DIR";
    val enabled = getenv "PSL_EVAL_MODE" = "1";
    val file_name =
      "abduction_" ^
      (Local_Theory.exit_global ctxt
       |> Context.theory_name {long = true}
       |> space_explode "."
       |> String.concatWith "_");
    val result_path = Path.append (Path.explode eval_dir) (Path.basic (file_name ^ ".proof"));
    val content =
      what_to_write ^ "\n";
  in
    if enabled andalso eval_dir <> ""
    then File.write result_path content
    else ()
  end;

fun clean_markup s =
  XML.content_of (YXML.parse_body s)
  handle ERROR _ => s;

(* write_suggestion_beside_theory *)
(* Writes the suggested script to its own file next to the theory it was invoked from, named
 * after that theory and the line the command sits on - "Foo_line42.proof" beside "Foo.thy".
 *
 * The Output pane is a poor place to keep a suggestion: it is transient, it is shared with
 * every other message the search produces, and a script long enough to include auxiliary
 * lemmas is exactly the kind that gets scrolled away or truncated. Writing it beside the
 * theory means it survives, and the line number identifies which invocation produced it when a
 * file contains several.
 *
 * Silent when there is no file to write to, which is the case for a theory being edited from a
 * buffer that has never been saved.
 *
 * The target comes from the context (Top_Down_Util.suggestion_target), put there by the command
 * on its own thread. It used to be derived here from Position.thread_data (), which is wrong at
 * this point: the search runs inside with_memory_monitor's task and forks freely, so this code
 * executes on a worker carrying no position at all, and the write was silently skipped -
 * measured, a four-and-a-half-minute "suggest" that printed its script wrote no file. The
 * thread-local position is still consulted as a fallback, for callers that never set the
 * config and do happen to run on the command's own thread. *)
(* A found proof is a result, not a message, and must not be droppable.
 *
 * This used to end in "if target = \"\" then ()": when the position was unavailable - which it is
 * on a worker thread, since Position.thread_data belongs to the command's own thread - the proof
 * was discarded in silence. Measured: of five goals proved by prove_by_abduction on one machine,
 * exactly one left a file behind. Four proofs were found, reported as successes, and thrown away,
 * and nothing said so.
 *
 * That matters beyond evaluation. This is to run server-side, receiving goals and returning
 * proofs to a client, and a path that silently produces nothing is the one failure such a service
 * cannot have.
 *
 * So there are now three places to write, tried in order, and a warning if none of them worked:
 *
 *   PSL_PROOF_OUTPUT_DIR   a directory, if set - always available, independent of any position,
 *                          which is what a server needs;
 *   the context's target   set by mk_search_ctxt while still on the command's thread;
 *   the thread position    the original behaviour, for interactive use.
 *)
fun write_suggestion_beside_theory (ctxt:Proof.context) (script:string): unit =
  Top_Down_Util.write_proof_to_file ctxt script;

fun emit_proof_script pst proofs =
  let
    val _ = TBC_Utils.tbc_trace "  emit_proof_script: reached";
    val whole_proof = Active.sendback_markup_properties [Markup.padding_command] proofs;
    val _           = tracing whole_proof;
    val clean_prfs  = clean_markup proofs;
    val _           = write_proof_script_in_result_file pst clean_prfs;
    val _           = write_suggestion_beside_theory (Proof.context_of pst) clean_prfs;
  in
    whole_proof
  end;

(* rename_vars_in_step / offset_for_aux_keys *)
(* The two halves of making an assembled proof's variable names unique across its nodes.
 *
 * rename_vars_in_step moves a node's script with its statement. Only the method text carries
 * variable names; "using" carries fact names, which are not renamed and must not be.
 *
 * offset_for_aux_keys decides where each node's numbering starts. The auxiliaries begin above the
 * root's own count, so the root's rename_mapping - a flat token substitution of var_N to the
 * caller's names, computed once from the root goal alone - cannot reach into an auxiliary's
 * variables. That flat mapping meeting a var_N belonging to some other branch is the shape of the
 * defect recorded at apply_safely in Abduction.thy. *)
fun rename_vars_in_step (renaming: (string * string) list)
    (TBC_Utils.Apply_Step {using, method}) =
      TBC_Utils.Apply_Step
        {using = using, method = TBC_Utils.rename_vars_in_script renaming method}
  | rename_vars_in_step _ step = step;

fun offset_for_aux_keys (root_key: key) (aux_keys: keys): (int * key) list =
  let
    fun count key = Top_Down_Util.advance_past_vnames (orkey_to_term key): int;
    fun step key (offset, acc) = (offset + count key, (offset, key) :: acc);
  in
    fold step aux_keys (count root_key, []) |> snd |> rev
  end;

fun print_necessary_proofs_only (tbc_facts: strings)
    (prelude_proofs:string) (pst:Proof.state) (ag:abduction_graph)
    (name2term:string2term_table) (goal_name:string) =
  let
    val pptree      = get_print_proof_tree pst ag name2term goal_name: print_proof_tree;
    val lemma_names = order_pptree pptree: strings;
    val lemma_terms = map (Symtab.lookup name2term) lemma_names |> Utils.somes: terms;
    val orkeys      = map (fn trm => (Or_N, [trm])) lemma_terms: keys;
    val ctxt        = Proof.context_of pst: Proof.context;
    val abduction_proofs =
      "\n" :: map (print_lemma_and_proof_of_key ctxt tbc_facts ag) orkeys
      |> String.concatWith "\n";
    val proofs      = prelude_proofs ^ abduction_proofs;
  in
    emit_proof_script pst proofs
  end;

(* print_necessary_proofs_for_subgoal *)
(* Like print_necessary_proofs_only, but for a goal that is a subgoal of an already-open
 * proof (suggest) rather than a freshly-stated top-level lemma: the goal is already
 * stated at the point suggest was invoked, so the root goal - always last in
 * order_pptree's dependencies-first ordering - is printed as a bare tactic script rather than
 * a fresh "lemma name: stmt".
 * A top-level "lemma" header for an auxiliary fact would be just as illegal mid-proof as one
 * for the root goal itself: an open goal only accepts tactics ("apply", "using", ...) until it
 * is closed, not new top-level commands. So whenever there is at least one auxiliary fact to
 * suggest - from AbductionProver's own graph search (aux_orkeys) or already supplied by TBC
 * preprocessing (prelude_proofs; see TBC_Utils.proved_nodes_to_proof_text_for_subgoal, which
 * on the path that reaches here always returns either "" or a flat sequence of unwrapped
 * "have" blocks, never something already wrapped) - the whole suggestion is instead wrapped in
 * a single "proof - ... qed": entering a nested structured (Forward-mode) proof of the very
 * same pending goal, inside which "have" is legal again for every auxiliary fact from either
 * source, closed by "show ?thesis" with the root's own script ("?thesis" rather than e.g.
 * "?case" since that is always in scope for whatever the current goal is, regardless of how
 * the caller's proof named it). If there are no auxiliary facts at all, this wrapping is
 * skipped and the root's script is suggested bare, exactly as before - it is already directly
 * insertable with no nesting required.
 * rename_mapping translates the root's own bare script back from AbductionProver's internal
 * var_N names to whatever names its free variables actually have at the point the suggested
 * script is meant to be pasted into (see TBC_Utils.rename_vars_in_script). It is applied only
 * to the root's own script, never to an auxiliary lemma's: each auxiliary lemma is a fresh,
 * self-contained, universally-quantified fact - its own var_N names are genuinely correct
 * there, not a stand-in for anything in the caller's context. Curried so that partially
 * applying rename_mapping yields a function matching print_necessary_proofs_only's signature,
 * for use with proof_by_abduction_with_prelude_using. *)
fun print_necessary_proofs_for_subgoal (caller: caller_context)
    (rename_mapping: (string * string) list) (tbc_facts: strings)
    (prelude_proofs:string) (pst:Proof.state) (ag:abduction_graph)
    (name2term:string2term_table) (goal_name:string) =
  let
    val pptree      = get_print_proof_tree pst ag name2term goal_name: print_proof_tree;
    val lemma_names = order_pptree pptree: strings;
    val lemma_terms = map (Symtab.lookup name2term) lemma_names |> Utils.somes: terms;
    val orkeys      = map (fn trm => (Or_N, [trm])) lemma_terms: keys;
    val ctxt        = Proof.context_of pst: Proof.context;
    val aux_orkeys  = Utils.init orkeys: keys;
    val root_orkey  = Utils.last orkeys: key;
    (* The root script's simp-consuming steps name the TBC facts they may have used, exactly as
       the graph "have"s below do - the search ran with those facts in its simp set, so a bare
       "auto" here would otherwise depend on rules the pasted block no longer declares. Falls
       back to the unaugmented text when the script will not parse, as the printers do. *)
    val root_proof  =
      (case try TBC_Utils.parse_tactic_steps (proof_of ag root_orkey) of
         SOME steps =>
           TBC_Utils.proof_steps_to_text (TBC_Utils.augment_steps_with_facts tbc_facts steps)
       | NONE => print_proof_of_key_only ag root_orkey)
      |> TBC_Utils.rename_vars_in_script rename_mapping;
    val graph_haves =
      map (fn (offset, key) => print_have_and_proof_of_key ctxt tbc_facts ag offset key)
        (offset_for_aux_keys root_orkey aux_orkeys): strings;
    (* prelude_proofs carries TBC's own "have" blocks, handed over bare for folding in here;
       graph_haves carries AbductionProver's. Both are auxiliaries as far as shaping goes, and
       the shaping itself lives in TBC_Utils so that the two emitters cannot drift apart - they
       previously each had their own copy, and both copies had the same defect. *)
    val haves = (if prelude_proofs = "" then [] else [prelude_proofs]) @ graph_haves;
    val proofs = TBC_Utils.assemble_suggestion caller haves root_proof;
  in
    emit_proof_script pst proofs
  end;

(* parse_method *)
(* The ML-level equivalent of what a user typing e.g. "apply (induct x)" causes: parses the
 * method portion (without any surrounding "apply"/"using") into a Method.text value, exactly
 * as the real "apply" command's own parser does - Pure.thy registers "apply" as bare
 * "Method.parse >> ...", with no extra wrapping. That native grammar already accepts a bare,
 * argument-free method name ("auto") as-is and a compound one in its own parentheses
 * ("( induct x )") without needing any help, so the printed method text - whichever shape
 * AbductionProver's own script generation gave it - can always be fed to it completely
 * unwrapped. Wrapping it in one more pair of parentheses unconditionally was tried first and
 * is wrong: whenever the text carries a goal-restriction suffix, e.g. "auto [ 1 ]" (apply
 * "auto" to only the first of several pending subgoals - AbductionProver's own scripts use
 * this whenever a preceding step, such as "induct", left more than one), that "[ 1 ]" belongs
 * outside any parentheses in Method.parse's own grammar; wrapping moves it inside, where it
 * is read as an argument to the method itself instead ("auto" does not accept one, so this
 * fails with "Bad arguments for method auto" - confirmed by a real failure applying exactly
 * such a script). *)
fun parse_method (ctxt: Proof.context) (s: string): Method.text =
  s
  |> Token.explode (Thy_Header.get_keywords' ctxt) Position.start
  |> filter Token.is_proper
  |> Scan.read Token.stopper Method.parse
  |> (fn SOME (text, _) => text
       | _ => error ("solve: could not parse method text: " ^ s));

(* parse_fact_ref *)
(* The ML-level equivalent of what a user typing e.g. "using foo.simps(2)" causes: parses a
 * single "using"-clause name into a Facts.ref, understanding Isar's "(N)"/"(N-M)" selection
 * suffix (e.g. "double.simps(2)" - AbductionProver's own generated scripts routinely
 * reference one specific equation out of a "fun" package's simps this way, not just bare
 * names) - Proof_Context.get_thms alone does not understand this suffix at all, treating it
 * as literally part of the name and failing with "Undefined fact" (confirmed by a real
 * failure applying exactly such a script). Falls back to treating the whole string as a bare
 * name for anything that does not match "NAME(...)", rather than raising here - Facts.named
 * always succeeds at this stage regardless of whether the name itself turns out to exist;
 * that failure (if any) surfaces later, from Proof_Context.get_fact itself. *)
(* Isabelle's own parser, not a second model of its grammar.
 *
 * This used to split the string on "(" and "-" by hand and rebuild Facts.Single / Facts.FromTo
 * from the pieces. That worked for the shapes it had been shown, and it was a re-implementation
 * of a grammar Isabelle already exports as Parse.thm - a few hundred lines from
 * Subtool.ML's own "using" parser, which uses Parse.thms1 for the same job. A hand-written
 * second model of somebody else's grammar only stays correct while nobody exercises the parts
 * it never learned, which for this one included interval lists ("foo(1,3)"), qualified names
 * carrying parentheses, and anything with whitespace in it.
 *
 * The fallback stays. Facts.named always succeeds here regardless of whether the name turns out
 * to exist; a name that does not resolve fails later and more informatively, from
 * Proof_Context.get_fact itself. Raising here would turn "this fact is not in scope" into a
 * parse error. *)
fun parse_fact_ref (ctxt: Proof.context) (s: string): Facts.ref =
  let
    val tokens =
      Token.explode (Thy_Header.get_keywords' ctxt) Position.start s
      |> filter Token.is_proper;
  in
    case try (Scan.read Token.stopper Parse.thm) tokens of
      SOME (SOME (fact_ref, _)) => fact_ref
    | _ => Facts.named s
  end;

(* apply_tactic_steps *)
(* Applies a (using-fact-names, method-text) list - see TBC_Utils.parse_tactic_steps - to a
 * live Proof.state via ordinary refinement, exactly as the equivalent "apply"/"using ...
 * apply" text would. rename_mapping translates each method's var_N tokens back to the
 * caller's own variable names first (see TBC_Utils.rename_vars_in_script); pass [] for a step
 * sequence that does not need this (i.e. every auxiliary "have"'s own steps - see
 * apply_have_of_key - since those are fresh, self-contained, universally-quantified facts
 * whose own var_N names are already correct, unlike the root goal's own steps). *)
fun apply_tactic_steps (rename_mapping: (string * string) list)
    (steps: TBC_Utils.proof_step list) (pst: Proof.state): Proof.state =
  let
    fun apply_method (using_names: strings) (meth_text: string) (st: Proof.state) =
      let
        val ctxt       = Proof.context_of st: Proof.context;
        val meth_text' = TBC_Utils.rename_vars_in_script rename_mapping meth_text: string;
        val st'        =
          if null using_names then st
          else
            let val thms = maps (Proof_Context.get_fact ctxt o parse_fact_ref ctxt) using_names
                           : thm list
            in Proof.using [[(thms, [])]] st end;
      in
        Proof.refine_singleton (parse_method ctxt meth_text') st'
      end;
    (* depth counts the "subgoal" blocks currently open. Each has its own "done"; the script's
       final "done" comes at depth zero and belongs to the caller, which closes the goal
       itself - see apply_root_steps. *)
    fun apply_step (TBC_Utils.Apply_Step {using, method}) (depth, st) =
          (depth, apply_method using method st)
      | apply_step TBC_Utils.Focus_Subgoal (depth, st) =
          (depth + 1, #2 (Subgoal.subgoal (Binding.empty, []) NONE (false, []) st))
      | apply_step TBC_Utils.Defer_Subgoal (depth, st) = (depth, Proof.defer 1 st)
      | apply_step TBC_Utils.Close_Block (depth, st) =
          if depth > 0 then (depth - 1, Proof.local_done_proof st) else (depth, st);
    (* Traced per step. A replay that stops part-way says so only if each step announces itself:
       an interrupt arriving here reports no position at all, so without this the whole replay is
       one opaque point. *)
    fun traced_step step (depth, st) =
      let val _ = TBC_Utils.tbc_trace ("  replay step: " ^ TBC_Utils.string_of_proof_step step);
      in apply_step step (depth, st) end;
    val (unclosed, result) = fold traced_step steps (0, pst);
    val _ =
      if unclosed = 0 then ()
      else error ("apply_tactic_steps: script left " ^ Int.toString unclosed
                  ^ " \"subgoal\" block(s) unclosed");
  in
    result
  end;

(* replay_closes_goal *)
(* Whether these steps, as they stand, close this goal in this context - the emission-time
 * check behind making TBC's simp bag explicit. The context passed in has the bag removed (see
 * explicitize_tbc_pnodes), so a script that leaned on the bag fails here unless its method
 * text names the facts. The goal state is built exactly as the search's own attempts build
 * theirs (TBC_Utils.pnode_n_pst_to_proof_attempt): Proof.theorem over the checked term.
 *
 * The timeout bounds each check: these are replays of proofs that already succeeded, measured
 * at 0-3 seconds each on the run that prompted this, so ten seconds is generous - but ten is a
 * chosen bound, not a measured one. A genuine proof that needs longer is not lost; its node
 * merely falls back to naming the full fact list (see minimal_facts_for_steps). *)
val emission_check_timeout = seconds 10.0;

fun replay_closes_goal (ctxt: Proof.context) (goal_term: term)
    (steps: TBC_Utils.proof_step list): bool =
  let
    fun check () =
      let
        val pst = Proof.theorem NONE (K I) [[(Syntax.check_prop ctxt goal_term, [])]] ctxt;
        val result = apply_tactic_steps [] steps pst;
      in Thm.no_prems (#goal (Proof.goal result)) end;
  in
    case Exn.capture (fn () => Timeout.apply emission_check_timeout check ()) () of
      Exn.Res closed => closed
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else false
  end;

(* minimal_facts_for_steps *)
(* The facts this script actually needs, out of the candidates the search had in its simp set.
 * SOME [] when no step consults the simp set at all; NONE when even the full candidate list
 * does not make the script close the goal here (a check timeout, or a script this checker
 * cannot replay) - the caller then falls back to the full list, which is semantically the bag
 * the search proved under, made visible. Greedy linear minimisation, the same algorithm
 * Sledgehammer's minimizer uses: try dropping each candidate in turn, keep the drop when the
 * script still closes the goal. *)
fun minimal_facts_for_steps (ctxt: Proof.context) (goal_term: term)
    (steps: TBC_Utils.proof_step list) (candidates: strings): strings option =
  let
    fun consumes (TBC_Utils.Apply_Step {method, ...}) = TBC_Utils.method_consumes_simp method
      | consumes _ = false;
    fun with_facts facts = TBC_Utils.augment_steps_with_facts facts steps;
  in
    if not (exists consumes steps) orelse null candidates then SOME []
    else if not (replay_closes_goal ctxt goal_term (with_facts candidates)) then NONE
    else
      SOME (fold (fn candidate => fn kept =>
              let val reduced = remove (op =) candidate kept in
                if replay_closes_goal ctxt goal_term (with_facts reduced) then reduced else kept
              end)
            candidates candidates)
  end;

(* explicitize_tbc_pnodes *)
(* Rewrites TBC preprocessing's proved pnodes so that every script names, in its own method
 * text, the auxiliary facts it needs - and drops the auxiliaries nothing needs. This is where
 * the search's simp bag stops: inside the search the two phases deliberately differ - TBC's
 * bottom-up conjecturing wants its proved conjectures ambient in the context, where the next
 * round's simp and Sledgehammer find them without being told, while the abduction graph keeps
 * every dependency explicit in its edges - but what is EMITTED must follow the graph's
 * discipline, or the pasted block re-creates the bag (as "have foo[simp]" did) and the reader
 * cannot tell which auxiliary any step used.
 *
 * Both suggest's emission and solve's replay consume the nodes this returns, so the printed
 * script and the applied one cannot disagree. The second component is the names of the
 * surviving bag facts, for the graph-script printers: the graph search runs in the same
 * context, so its scripts' simp-consuming steps may lean on the same facts and are augmented
 * with the same names (unminimised there - a graph script cannot be replayed in isolation,
 * since its "using" references name graph facts that only exist mid-replay).
 *
 * Minimisation is all-or-nothing on finding the bag by name: if any bag fact cannot be looked
 * up in this context, a check could still prove through the remnant simp rule and a genuinely
 * needed fact would be dropped - so every node then falls back to the full list instead.
 *
 * Pruning runs only when TBC proved the final goal itself (the suggestion is then complete, so
 * "needed" is decidable); on the path where the graph search runs next, every auxiliary is
 * kept, because the graph's scripts may use any of them. An auxiliary is kept when its name
 * appears in a kept script - in the spliced method text, a "using", or a hammer-found call
 * such as "(metis foo)" - reached to a fixpoint from the final goal. *)
fun explicitize_tbc_pnodes (pst: Proof.state) (pnodes: TBC_Utils.pnodes)
    : TBC_Utils.pnodes * strings =
  let
    val ctxt0 = Proof.context_of pst;
    val proved = filter #proved_wo_assmng_cnjctr pnodes
                 |> TBC_Utils.drop_mirrored_pnodes ctxt0
                 |> TBC_Utils.sort_pnodes;
    val (final_nodes, aux_nodes) = List.partition #is_final_goal proved;
    (* The bag: what assume_term_in_ctxt declared. Permutative statements were never declared
       (they diverge as rewrite rules) and stay plain facts, referenced by name where a hammer
       chose them. *)
    val bag_nodes = filter_out (TBC_Utils.is_permutative_statement o #lemma_term) aux_nodes;
    val bag_names = map #lemma_name bag_nodes;
    (* The checker deletes the simp rule of EVERY proved node - by TERM, and with the final
       goal included. Three wrong versions preceded this, all measured on Prod TIP_prop_15:
       deleting the kept auxiliaries by name left rules the emission never shows (a replay then
       proves the goal through them and the minimiser prunes facts the pasted script needs);
       and the final goal itself is the sharpest case - when TBC proves the goal in a middle
       round, assume_term_in_ctxt notes it like any conjecture, so the checker's "auto" closed
       the goal BY ITS OWN NOTED STATEMENT and every auxiliary was pruned from a suggestion
       that then said only "apply auto" and did not compile. Deleting by name is fragile
       against how notes are qualified; the rewrite rule is determined by the statement, so
       each proved node's thm is reconstructed here exactly as assume_term_in_ctxt built it
       (Goal.prove_sorry + cheat) and deleted by structure. Permutative statements were never
       declared and need no deletion. *)
    val checker_ctxt_opt =
      let
        fun sorry_thm (t: term) =
          try (fn () =>
            Goal.prove_sorry ctxt0 (Variable.add_free_names ctxt0 t []) [] t
              (fn {context, ...} => Skip_Proof.cheat_tac context 1)) ();
        val del_thms =
          filter #proved_wo_assmng_cnjctr pnodes
          |> filter_out (TBC_Utils.is_permutative_statement o #lemma_term)
          |> map_filter (sorry_thm o #lemma_term);
      in SOME (Raw_Simplifier.del_simps del_thms ctxt0) end;
    fun facts_for (pnode: TBC_Utils.pnode) (candidates: strings): strings =
      case checker_ctxt_opt of
        NONE => candidates
      | SOME checker_ctxt =>
          (case minimal_facts_for_steps checker_ctxt (#lemma_term pnode)
                  (TBC_Utils.pnode_proof_steps pnode) candidates of
             SOME needed => needed
           | NONE =>
               (TBC_Utils.tbc_trace ("  explicitize: replay of " ^ #lemma_name pnode
                  ^ " did not confirm; emitting the full fact list");
                candidates));
    (* Each auxiliary may reference only the bag facts established BEFORE it in the emitted
       order (sort_pnodes = proof_id = chronological): a "have" chain executes top-down, so a
       later name is undefined where an earlier script mentions it. An all-but-self candidate
       list was tried first and produced exactly that - a forward reference and a two-fact
       cycle in one emitted block - because the checker context has every fact noted and
       resolves names an Isar reader cannot. Earlier-only also keeps each check's simp set no
       larger than the search's was when the node was proved: the full bag at once can diverge
       as a rewrite system (measured elsewhere in this file's history: seven conjectures made a
       plain "auto" raise Interrupt_Breakdown), which showed up here as a replay check that
       timed out for a node whose own proof is instant. *)
    val aux' =
      fold (fn pnode => fn (done, earlier) =>
        let
          val augmented =
            TBC_Utils.augment_pnode_proof_with_facts (facts_for pnode earlier) pnode;
          val earlier' =
            if member (op =) bag_names (#lemma_name pnode)
            then earlier @ [#lemma_name pnode] else earlier;
        in (done @ [augmented], earlier') end)
      aux_nodes ([], []) |> fst;
    val final' =
      map (fn p => TBC_Utils.augment_pnode_proof_with_facts (facts_for p bag_names) p)
        final_nodes;
    fun mentions (pnode: TBC_Utils.pnode) (name: string): bool =
      exists (fn TBC_Utils.Apply_Step {using, method} =>
                 exists (String.isSubstring name) using orelse String.isSubstring name method
               | _ => false)
        (TBC_Utils.pnode_proof_steps pnode);
    fun grow (kept: TBC_Utils.pnodes) =
      case filter (fn p => not (exists (fn k => #lemma_name k = #lemma_name p) kept)
                           andalso exists (fn k => mentions k (#lemma_name p)) kept) aux' of
        [] => kept
      | found => grow (kept @ found);
    val kept =
      case final' of
        [] => aux' @ final'
      | _  => grow final' |> TBC_Utils.sort_pnodes;
    val kept_bag_names =
      filter (fn n => exists (fn p => #lemma_name p = n) kept) bag_names;
    val _ = TBC_Utils.tbc_trace ("  explicitize: kept " ^ Int.toString (length kept) ^ " of "
              ^ Int.toString (length proved) ^ " proved node(s); bag = ["
              ^ commas kept_bag_names ^ "]");
  in
    (kept, kept_bag_names)
  end;

(* have_cmd_and_close *)
(* The ML-level equivalent of "have NAME: STMT for VARS <tactic-script>" - see
 * Abduction_Graph.print_have_and_proof_of_key for why the "for" clause (here, the fixes
 * argument to Proof.have_cmd) is required: without it, a nested "have" does not close over
 * its own free variables into a genuinely general fact the way a top-level "lemma" does.
 * Deliberately Proof.have_cmd (which reads the statement from a string, exactly as real Isar
 * source does) rather than Proof.have (which certifies an already-built term directly):
 * despite looking like the more natural choice given a key/pnode already carries a genuine
 * term, this was tried first and does NOT work - confirmed by a minimal, isolated
 * reproduction. With Proof.have, the statement's own free variables are not properly
 * identified with the ones fixes introduces (even though both are literally the same name and
 * type), so a later "induct" targeting one of them only rewrites the copy fixes introduced,
 * leaving the goal's own occurrences untouched - one of the resulting cases ends up identical
 * to the original, unsplit statement, and the proof silently fails to close. Proof.have_cmd
 * does not have this problem, since parsing the statement text in a context that already has
 * the fixes in scope naturally resolves every occurrence to the very same fixed variable. *)
fun have_cmd_and_close (name:string) (stmt_str:string)
    (fixes: (binding * string option * mixfix) list) (steps: TBC_Utils.proof_step list)
    (pst:Proof.state): Proof.state =
  let
    (* No attributes. The fact used to be declared [simp] here, to match how it was available
       when the script below it was found (TBC_Utils.assume_term_in_ctxt declares every
       non-permutative proved conjecture as a simp rule in the search context) - measured,
       establishing it plain while the scripts still said bare "auto" turned a found proof into
       "replaying it against the live goal failed". The scripts no longer say bare "auto":
       explicitize_tbc_pnodes splices the fact names into the method text, so the replayed
       steps carry their dependencies and the fact is established plain, exactly as the graph
       path always did. Reintroducing the attribute without also reverting that would hide the
       dependencies again - see the design note at explicitize_tbc_pnodes. *)
    val (_, pst_goal) =
      Proof.have_cmd false NONE (K I) fixes []
        [((Binding.name name, []), [(stmt_str, [])])] true pst
      : thm list * Proof.state;
  in
    apply_tactic_steps [] steps pst_goal |> Proof.local_done_proof
  end;

(* apply_have_generic *)
(* have_cmd_and_close's own Proof.have_cmd requires pst to be in Forward or Chain mode
 * (Proof.assert_forward_or_chain, asserted deep inside generic_goal) - true whenever pst is
 * nested inside a structured proof or has not yet been put into backward mode, but NOT when
 * pst is itself a bottom-level apply-chain that needs auxiliary lemmas (confirmed by a real
 * failure. "Illegal application of proof command in \"prove\" mode" - a genuine, real Isar
 * apply-script cannot contain a "have" either, for the same underlying reason, so this is a
 * real gap between what real Isar syntax allows and what solve needs to support at
 * the ML level, not an artificial one). When pst is not Forward/Chain, the auxiliary lemma is
 * instead proved in a completely separate, freshly Proof.init'd state built over the very same
 * context (always Forward by construction, regardless of pst's own mode), and the resulting
 * fact is then copied into pst's own context by name via Proof.map_context/
 * Proof_Context.note_thmss - Proof.map_context performs no mode check at all (it only ever
 * touches the current node's context component, never mode or goal), so this always succeeds
 * regardless of pst's own mode.
 *
 * Proof.init alone is not quite enough to host the have: Proof.state's own "bottom" threshold
 * is level <= 2 (Proof.assert_bottom), and have_cmd_and_close's own Proof.local_done_proof
 * requires NOT bottom (an ordinary "have" is never itself the outermost thing in a proof) -
 * but Proof.init starts at level 0, and have_cmd's own single open_block only reaches level 1,
 * still within the "bottom" range (confirmed by a real failure, "Already at bottom of proof").
 * Proof.begin_block (itself a double open_block) is applied first, taking Proof.init's level 0
 * to level 2, then have_cmd's own open_block reaches level 3 - comfortably not bottom. *)
fun apply_have_generic (name:string) (stmt_str:string)
    (fixes: (binding * string option * mixfix) list) (steps: TBC_Utils.proof_step list)
    (pst:Proof.state): Proof.state =
  (TBC_Utils.tbc_trace ("HAVE " ^ name ^ ": " ^ stmt_str
     ^ "  [fixes: " ^ commas (map (Binding.name_of o #1) fixes) ^ "]"
     ^ (if can Proof.assert_forward_or_chain pst then "  via have_cmd"
        else "  via separate Proof.init (pst not forward/chain)"));
  if can Proof.assert_forward_or_chain pst
  then have_cmd_and_close name stmt_str fixes steps pst
  else
    let
      val aux_pst0 = Proof.init (Proof.context_of pst) |> Proof.begin_block: Proof.state;
      val aux_done = have_cmd_and_close name stmt_str fixes steps aux_pst0: Proof.state;
      val aux_thms = Proof_Context.get_fact (Proof.context_of aux_done) (Facts.named name)
                     : thm list;
    in
      (* Noted plain on this path too - the two paths used to disagree about whether the fact
         became a simp rule, and a script found under one assumption replayed under the other
         stops with subgoals its own auxiliaries would have closed. There is no simp declaration
         left to keep in agreement (see have_cmd_and_close); what must agree now is only that
         the fact exists by name, which both paths establish. *)
      pst
      |> Proof.map_context (fn c =>
          c |> Proof_Context.note_thmss "" [((Binding.name name, []), [(aux_thms, [])])] |> #2)
    end);

(* fixes_for_have *)
(* Moved to TBC_Utils, which both the repliers here and the printers there can see, so the
   applied fixes and the printed "for" clause are one list rather than two computations. Kept
   under this name because it reads naturally at the call sites below and Proof_Step_Test names
   it. See TBC_Utils.fixes_for_have for the divergence that prompted the move. *)
val fixes_for_have = TBC_Utils.fixes_for_have;

(* apply_have_of_key *)
(* offset: this auxiliary's variables are renumbered to start above every earlier node's, so an
 * assembled proof has no two unrelated var_0s. See Top_Down_Util.offset_vnames for why the
 * canonical numbering cannot do this itself, and offset_for_aux_keys below for the threading.
 * The statement and the script are renamed with the same mapping; renaming one without the other
 * is the failure this repository keeps meeting. *)
fun apply_have_of_key (tbc_facts: strings) (ag:abduction_graph) (offset:int) (key:key)
    (pst:Proof.state): Proof.state =
  let
    val ctxt     = Proof.context_of pst: Proof.context;
    val name     = lemma_name_of ag key: string;
    val stmt0    = (case key of (Or_N, [trm]) => trm
                     | _ => error "apply_have_of_key: key is not a single-term Or-node");
    val (stmt, renaming) = Top_Down_Util.offset_vnames offset stmt0;
    val stmt_str = Isabelle_Utils.trm_to_string ctxt stmt: string;
    (* Augmented with the TBC facts exactly as the printed block is
       (print_have_and_proof_of_key): the graph search ran with those facts in its simp set,
       and they are plain facts here, so a bare "auto" in this script would be missing rules it
       was found with. *)
    val steps    = proof_of ag key |> TBC_Utils.parse_tactic_steps
                   |> TBC_Utils.augment_steps_with_facts tbc_facts
                   |> map (rename_vars_in_step renaming): TBC_Utils.proof_step list;
    val fixes    = fixes_for_have ctxt stmt;
  in
    (*A top-down auxiliary from AbductionProver's own graph. The graph tracks the dependencies
      between these explicitly and does not declare them during the search either.*)
    apply_have_generic name stmt_str fixes steps pst
  end;

(* apply_have_of_pnode *)
(* Like apply_have_of_key, but for a TBC-preprocessing-sourced pnode (TBC_Utils.pnode) instead
 * of an AbductionProver graph key - see run_solve in Abduction.thy, which applies TBC
 * preprocessing's own auxiliary facts to the live Proof.state exactly like this one, before
 * ever handing off to AbductionProver's own graph search (which needs those same facts
 * already established as real local facts, to reference by name via "using" in its own
 * proofs, exactly as printing already required - see
 * TBC_Utils.proved_nodes_to_proof_text_for_subgoal). The pnode carries the statement as a
 * term, so the fixes list is read straight off it; the string form is produced here only
 * because Proof.have_cmd takes its statement as text. *)
fun apply_have_of_pnode (pnode: TBC_Utils.pnode) (pst:Proof.state): Proof.state =
  let
    val ctxt       = Proof.context_of pst: Proof.context;
    val name       = #lemma_name pnode: string;
    (*The pnode carries the term; text is produced here only because Proof.have_cmd reads its
      statement from a string - see have_cmd_and_close for why the _cmd form is required.*)
    val stmt_term  = #lemma_term pnode: term;
    val stmt_str   = TBC_Utils.pnode_stmt ctxt pnode: string;
    (*The steps PSL applied, not a script parsed back into steps - see TBC_Utils.pnode's
      proof_log. A node proved by the graph search rather than by a PSL run carries text only,
      and is parsed as before.*)
    val steps      = TBC_Utils.pnode_proof_steps pnode: TBC_Utils.proof_step list;
    val fixes      = fixes_for_have ctxt stmt_term;
  in
    (*A template-based conjecture. It was declared a simp rule during the search that found the
      script below, and used to be re-declared here to match; the pnodes reaching this function
      now come through explicitize_tbc_pnodes, whose rewritten steps name the facts they need,
      so the fact is established plain - see have_cmd_and_close.*)
    apply_have_generic name stmt_str fixes steps pst
  end;

(* apply_tbc_prelude_aux_to_pst *)
(* Applies every TBC-preprocessing-proven pnode except the final goal (whether or not TBC
 * preprocessing alone went on to prove the final goal too - see apply_tbc_final_to_pst and
 * run_solve in Abduction.thy) as an auxiliary "have" to the live pst, exactly as
 * apply_graph_proof_to_pst does for AbductionProver's own graph's auxiliary facts. *)
fun apply_tbc_prelude_aux_to_pst (pst:Proof.state) (pnodes: TBC_Utils.pnodes): Proof.state =
  pnodes
  |> filter (fn p => #proved_wo_assmng_cnjctr p andalso not (#is_final_goal p))
  (*Never establish both directions of an equation: as simp rules the pair loops, which showed
    up as Interrupt_Breakdown on a goal whose auxiliaries included associativity twice.*)
  |> TBC_Utils.drop_mirrored_pnodes (Proof.context_of pst)
  |> TBC_Utils.sort_pnodes
  |> (fn aux_pnodes => fold apply_have_of_pnode aux_pnodes pst);

(* apply_root_steps *)
(* solve may be invoked at a point where pst is not yet in backward/"prove" mode -
 * concretely, right after "proof -" with no "show ?thesis" yet (e.g. "lemma foo: \"P\" proof -
 * solve qed"; a bottom-level apply-chain or a proof already past "show ?case" is
 * already backward, so this is specifically about the "proof -" case). Proof.refine_singleton
 * still silently succeeds at refining the underlying goal thm even then - the mode flag and
 * the goal thm are independent bookkeeping, and refine_singleton only ever touches the latter
 * - so the root's own tactic steps can apply and fully close the goal (0 remaining subgoals)
 * without any error appearing yet. But Proof.local_done_proof/Proof.global_done_proof do
 * require backward mode, since they are designed for exactly the "show ?thesis apply ... done"
 * pattern, and fail with "Illegal application of proof command in \"state\" mode" even though
 * the goal itself is already, genuinely fully proved (confirmed by a real failure). Entering
 * backward mode by hand (Proof.enter_backward) is not enough either - that only flips the mode
 * flag without registering the goal for closing at all ("No goal in this block" from
 * local_done_proof immediately afterwards). The fix is to open the existing goal exactly as
 * "show ?thesis" itself would - via Proof.show_cmd resolving the literal string "?thesis" -
 * rather than a term extracted from Proof.goal and resubmitted by hand (tried first: Proof.show
 * on such a term fails immediately with "Failed to refine any pending goal").
 *
 * Crucially, "show" always opens its OWN nested block, one level deeper than pst, regardless of
 * whether pst itself was already at the bottom of its enclosing proof. So once opened, that
 * block must also be closed again here, via Proof.local_done_proof, before returning - leaving
 * the result back at pst's own original level and mode, goal fully discharged. Skipping this
 * and leaving the closing to the outer caller (as an earlier version of this function did)
 * produced a real, confirmed "Not at bottom of proof" failure: the caller's own
 * local_done_proof/global_done_proof was operating on a state one level deeper than pst
 * actually started at, so a global (bottom-level) close wrongly looked non-bottom.
 *
 * Returns (was_already_backward, result). When pst was already backward (a real, textually
 * valid backward-mode goal - bottom-level apply-chain or already-shown), the root steps are
 * applied directly with no extra wrapper, and the result is deliberately left OPEN (not closed)
 * for the caller's own local_done_proof/global_done_proof, exactly mirroring what real "done"
 * would do there - true is returned so the caller knows closing is still its job. When pst was
 * not already backward, this function closes its own inner "show" wrapper itself before
 * returning, and false is returned so the caller knows to just use the (already fully closed)
 * result as-is, with no further closing call of its own - solve is then not the
 * command actually responsible for the outer proof's own close (the user's own separate "qed"
 * text is), so it must never attempt a Toplevel.end_proof-style exit in that case either; see
 * solve_local/solve_global in Abduction.thy. *)
(* apply_root_inside_focus *)
(* The root goal's own steps, applied inside Subgoal.focus and put back with Subgoal.retrofit,
 * rather than applied to the caller's state as it stands.
 *
 * This replaces with_focus_if_parameterised, which did the same job by emitting the Isar
 * "subgoal for a b" command. That worked, and is what shipped - but it was a second mechanism
 * that had to be kept in agreement with the search's own Subgoal.focus by hand, and those two
 * disagreeing is precisely the defect it was written to fix (docs/2026_08_02_progress_report.md 4.9: 8 replay
 * failures out of 8, on a goal whose found script named a parameter). Subgoal.FOCUS is the same
 * operation the search performs, applied as a tactic: it focuses, runs the body in the focused
 * context, and retrofits the result. There is then nothing left to keep in agreement, and the
 * parameter case stops being a case at all - it is no longer detected and handled, it simply
 * cannot arise.
 *
 * Measured before being relied on, in all eight Isar positions - including the two that
 * defeated step 1 of docs/2026_08_01_isar_integration_design.md, because focus and retrofit are plain ML with
 * no mode requirement where Subgoal.subgoal is the Isar command and needs prove mode. See
 * Abduction/Test_Isar/Retrofit_Probe.thy, which fails the build if that stops holding.
 *
 * The steps run in a Proof.theorem over the focused conclusion, because that is the shape
 * apply_tactic_steps drives; the theorem it yields then discharges the focused goal by
 * resolution, and FOCUS's own retrofit puts it back. Chained facts are carried in, since the
 * script may have been found with them available. *)
fun apply_root_inside_focus (rename_mapping: (string * string) list)
    (steps: TBC_Utils.proof_step list) (pst: Proof.state): Proof.state =
  let
    val chained = #facts (Proof.goal pst): thm list;
    fun body {context = ctxt1: Proof.context, concl: cterm, ...} (focused: thm) =
      let
        val pst1 =
          Proof.theorem NONE (K I) [[(Thm.term_of concl, [])]] ctxt1
          |> (if null chained then I else Proof.using_facts chained): Proof.state;
        val pst2    = apply_tactic_steps rename_mapping steps pst1: Proof.state;
        val goal_thm = #goal (Proof.goal pst2): thm;
      in
        (* Seq.empty rather than an error: a tactic that cannot close its goal fails, and the
           enclosing refine reports it in the caller's own terms. *)
        (* The finished theorem now has the shape of the whole subgoal, premises included, so
           resolving it against a goal of that same shape unifies the conclusions and leaves one
           residual subgoal per premise, each of the form "P ==> P". Measured on IsaPlanner
           prop_05, which came back with "1. n = y ==> n = y" left over. Assumption closes them.
           For a goal without premises resolution leaves nothing and this is a no-op. *)
        if Thm.nprems_of goal_thm = 0
        then (resolve_tac ctxt1 [Goal.finish ctxt1 goal_thm] 1
              THEN ALLGOALS (assume_tac ctxt1)) focused
        else Seq.empty
      end;
  in
    (* FOCUS_PARAMS, not FOCUS: the two differ exactly on the subgoal's premises. FOCUS strips
       them out of the goal and assumes them in the context, so #concl is the bare conclusion;
       FOCUS_PARAMS fixes the parameters and leaves the premises where they are, so #concl is the
       whole subgoal. The search is given the whole subgoal - see focus_and_prepare_search - and
       replay has to be handed the same statement, or the script proves "P ==> Q" and is applied
       to a goal reading "Q". Measured on IsaPlanner prop_05, which failed that way with
       "Failed to finish proof: 1. False 2. False".

       For a goal without premises the two are the same operation, since there is nothing to
       strip, so this does not disturb the eight Isar positions FOCUS was measured in.

       METHOD rather than SIMPLE_METHOD for the same reason. SIMPLE_METHOD inserts the chained
       facts into the goal before the body runs, and FOCUS used to strip them straight back out
       along with the premises - which is why the pairing worked. Keeping the premises now means
       keeping those insertions too, so the statement grew a copy of every chained fact while
       "using_facts chained" below added a second: measured on Scenario_Chained_Facts, whose goal
       came out as "[|/\n. opaque_f n = Suc n; /\n. opaque_f n = Suc n|] ==> opaque_f n = Suc n".
       Not inserting them leaves the subgoal as the search saw it, and the body still names them
       with "using". *)
    Proof.refine_singleton
      (Method.Basic (fn ctxt =>
         Method.METHOD (fn _ => Subgoal.FOCUS_PARAMS body ctxt 1))) pst
  end;

fun apply_root_steps (rename_mapping: (string * string) list)
    (steps: TBC_Utils.proof_step list) (pst: Proof.state): bool * Proof.state =
  if can Proof.assert_backward pst
  then (TBC_Utils.tbc_trace "  replay: root steps, already backward";
        (true, apply_root_inside_focus rename_mapping steps pst))
  else
    let
      val _ = TBC_Utils.tbc_trace "  replay: root steps, opening \"show ?thesis\"";
      val (_, pst_show) =
        Proof.show_cmd false NONE (K I) [] [] [((Binding.empty, []), [("?thesis", [])])] true pst
        : thm list * Proof.state;
    in
      (false,
       apply_root_inside_focus rename_mapping steps pst_show
       |> Proof.local_done_proof)
    end;

(* apply_tbc_final_to_pst *)
(* Applies the final goal's own bare script directly to the live pst (no "have" wrapper,
 * exactly like apply_graph_proof_to_pst's root_orkey handling) - used only when TBC
 * preprocessing alone already proved the final goal, so AbductionProver's own graph search
 * never has to run at all (see run_solve in Abduction.thy). rename_mapping translates the
 * script's var_N names back to the caller's own variable names, exactly as for
 * AbductionProver's own root script - see apply_tactic_steps. Returns (was_already_backward,
 * result) - see apply_root_steps. *)
fun apply_tbc_final_to_pst (rename_mapping: (string * string) list) (pst:Proof.state)
    (pnodes: TBC_Utils.pnodes): bool * Proof.state =
  let
    val final_pnode =
      pnodes |> filter (fn p => #proved_wo_assmng_cnjctr p andalso #is_final_goal p)
      |> (fn [p] => p
           | _ => error "apply_tbc_final_to_pst: expected exactly one proved final-goal pnode");
    val steps = TBC_Utils.pnode_proof_steps final_pnode: TBC_Utils.proof_step list;
    val _ = TBC_Utils.tbc_trace ("  replay: final proof = "
              ^ commas (map TBC_Utils.string_of_proof_step steps));
  in
    apply_root_steps rename_mapping steps pst
    before TBC_Utils.tbc_trace "  replay: final script applied"
  end;

(* proved_alias_of_goal *)
(* TBC preprocessing proves each generated conjecture as its own pnode, and the original goal as
 * a separate one. Nothing stops a conjecture coming out alpha-equivalent to the goal itself,
 * and when that happens the goal has been proved - just not under the name the final-goal pnode
 * carries, so original_goal_is_proved says no.
 *
 * This is not hypothetical. On "add x y = add y x", TBC proved the conjecture
 * "add var_1 var_2 = add var_2 var_1" outright, without assuming any other conjecture, while
 * the separate attempt on the final-goal pnode failed; solve then spent the graph search's
 * whole budget and reported "could not find a proof" for a statement it had already proved a
 * minute earlier. The two attempts are independent runs of a nondeterministic search, so which
 * of them succeeds is a coin toss.
 *
 * Only conjectures proved without assuming other conjectures count, which is the same condition
 * apply_tbc_prelude_aux_to_pst uses to establish them as real facts on the live state - so by
 * the time this is consulted the fact exists there, under this name, and can simply be applied.
 *)
fun proved_alias_of_goal (ctxt:Proof.context) (goal:term) (pnodes: TBC_Utils.pnodes)
    : string option =
  let
    val goal_body = Top_Down_Util.remove_Trueprop goal;
    fun same_statement (pnode: TBC_Utils.pnode) =
      Top_Down_Util.alpha_eq_over_fvar
        (Top_Down_Util.remove_Trueprop (#lemma_term pnode)) goal_body;
  in
    pnodes
    |> filter (fn p => #proved_wo_assmng_cnjctr p andalso not (#is_final_goal p))
    |> get_first (fn p => if same_statement p then SOME (#lemma_name p) else NONE)
  end;

(* apply_proved_alias_to_pst *)
(* Closes the live goal with an auxiliary fact that proved_alias_of_goal identified as the goal
 * itself. "rule" rather than a search: the fact and the goal are the same statement up to the
 * names of their free variables, and the auxiliary was stated with an explicit "for" clause
 * (see fixes_for_have), so it is general enough to resolve directly against the goal.
 * Returns (was_already_backward, result) - see apply_root_steps. *)
fun apply_proved_alias_to_pst (rename_mapping: (string * string) list) (pst:Proof.state)
    (name:string): bool * Proof.state =
  apply_root_steps rename_mapping
    [TBC_Utils.Apply_Step {using = [], method = "(rule " ^ name ^ ")"}] pst;

(* apply_graph_proof_to_pst *)
(* Like print_necessary_proofs_for_subgoal, but drives the live Proof.state pst directly via
 * apply_have_of_key/apply_tactic_steps instead of printing text - the mechanism behind solve,
 * as opposed to suggest's printed-text mechanism. pst here is the caller's own real, live
 * proof state (e.g. pst_orig in Abduction.thy's run_solve), not the isolated
 * Proof.theorem-based context the search itself runs in - ag/name2term/goal_name carry
 * everything needed from the search's own result, so pst is never touched until this function
 * runs. Returns (was_already_backward, result) - see apply_root_steps. *)
fun apply_graph_proof_to_pst (rename_mapping: (string * string) list) (tbc_facts: strings)
    (pst:Proof.state)
    (ag:abduction_graph) (name2term:string2term_table) (goal_name:string): bool * Proof.state =
  let
    val pptree      = get_print_proof_tree pst ag name2term goal_name: print_proof_tree;
    val lemma_names = order_pptree pptree: strings;
    val lemma_terms = map (Symtab.lookup name2term) lemma_names |> Utils.somes: terms;
    val orkeys      = map (fn trm => (Or_N, [trm])) lemma_terms: keys;
    val aux_orkeys  = Utils.init orkeys: keys;
    val root_orkey  = Utils.last orkeys: key;
    (* tbc_facts as in apply_have_of_key: the search saw them as simp rules, the replay has
       them plain, so the script says where they go. Mirrors print_necessary_proofs_for_subgoal
       augmenting the printed root script. *)
    val root_steps  = proof_of ag root_orkey |> TBC_Utils.parse_tactic_steps
                       |> TBC_Utils.augment_steps_with_facts tbc_facts
                       : TBC_Utils.proof_step list;
  in
    pst
    |> fold (fn (offset, key) => apply_have_of_key tbc_facts ag offset key)
         (offset_for_aux_keys root_orkey aux_orkeys)
    |> apply_root_steps rename_mapping root_steps
  end;

(* print_partial_proofs *)
(* What the search did prove, when it did not prove the goal.
 *
 * A failed search is not an empty result: it has usually proved several auxiliary lemmas
 * completely, and for a client asking "what do you know about this goal?" those are worth having.
 * Until now they were discarded - the caller printed only when solved_in_loop held.
 *
 * Ordered by proof_id, which is assigned when an or-node is proved, so the sequence is
 * chronological: a lemma appears after everything that was available when it was proved. That is
 * the order a reader can follow, and it is what print_proof_of_graph already uses.
 *
 * There is deliberately no "show" and no "qed". The root goal is unproved, so a block that
 * claimed to close it would not compile; what is emitted is the sequence of "have"s alone, under
 * a header saying so. It is a record of progress, not a proof of the goal. *)
(* The assembly alone, shared with the periodic progress reporter below: the proved or-nodes'
   haves, chronological by proof_id, or "" when nothing is proved yet. Each have's
   simp-consuming steps may name every earlier lemma of the sequence (the TBC facts plus the
   partial haves before it), so the emitted fragment carries its dependencies explicitly
   rather than assuming the reader recreates the search's ambient simp set - the same
   discipline as the final emission, without the replay-minimization. *)
fun partial_proofs_text (tbc_facts: strings) (pst:Proof.state) (graph:abduction_graph)
    : string =
  let
    val ctxt      = Proof.context_of pst;
    val or_keys   = keys graph |> filter is_ornode: keys;
    val with_ids  =
      map_filter (fn k => Option.map (fn id => (k, id)) (proof_id_of graph k)) or_keys;
    val ordered   = sort (fn ((_, a), (_, b)) => int_ord (a, b)) with_ids |> map fst: keys;
    (* No root here: the goal is unproved, so there is no root script whose rename_mapping the
       auxiliaries must stay clear of. They still have to be distinct from each other, so the
       numbering runs across them from zero. *)
    val haves     =
      let
        fun step key (offset, facts, acc) =
          (offset + Top_Down_Util.advance_past_vnames (orkey_to_term key),
           facts @ [lemma_name_of graph key],
           print_have_and_proof_of_key ctxt facts graph offset key :: acc);
      in fold step ordered (0, tbc_facts, []) |> #3 |> rev end: strings;
  in
    if null haves then "" else cat_lines haves
  end;

(* The block a timed-out search hands back, shaped to be pasted where the command was
   invoked. It closes with "show ?thesis sorry": sorry, and deliberately not oops, because
   oops ABANDONS the enclosing proof - every have inside would be checked and then discarded,
   and nothing after could use the lemma - while sorry closes only the unproved show through
   the skip-proof oracle, so Isabelle still genuinely checks every have proof, the lemma
   becomes available visibly oracle-tainted, and the user replaces the one sorry when they
   find the real proof. The show ?thesis line is right where the goal is stated exactly as it
   was searched (the statement position prove/prove_by_abduction/suggest-at-the-statement
   use); a caller mid-apply-chain whose pending goal has been transformed replaces that line
   with their own show, or drops the wrapper. See docs/2026_08_09_partial_proofs_guide.html. *)
fun wrap_partial_block (prelude_proofs: string) (haves: string): string =
  "(* AbductionProver did not prove the goal. These auxiliary lemmas were proved\n\
  \   completely, in the order they were proved. Pasted as-is at the point the prover\n\
  \   was invoked, the block establishes them for real and closes the still-open goal\n\
  \   with sorry - replace the sorry when you have the proof. *)\n\
  \proof -\n"
  ^ (if prelude_proofs = "" then "" else prelude_proofs ^ "\n")
  ^ haves
  ^ "\nshow ?thesis sorry\nqed";

fun print_partial_proofs (tbc_facts: strings) (prelude_proofs: string) (pst:Proof.state)
    (graph:abduction_graph): string =
  case (prelude_proofs, partial_proofs_text tbc_facts pst graph) of
    ("", "") => ""
  | (prelude, haves) => emit_proof_script pst (wrap_partial_block prelude haves);

(* fork_progress_reporter *)
(* Every progress_report_interval seconds while a search phase runs: the auxiliary lemmas
 * proved completely SO FAR, in the order they were proved, to two places - tracing (best
 * effort: like the memory monitor, a plain thread's messages may reach neither jEdit's
 * Output pane nor the batch log, which is why the file is the contract), and
 * $PSL_PROOF_OUTPUT_DIR/<theory>_progress.thy for a process outside Isabelle. The external
 * consumer is a web-facing manager that abandons a search after a fixed budget: even when the
 * goal is never proved, the last snapshot hands its user every auxiliary the search did prove,
 * ordered so the file reads top-down.
 *
 * The content comes from the snapshot closure ("" for "nothing yet"), so one reporter serves
 * both phases: the entry points fork one over TBC's progress store
 * (TBC_Utils.progress_pnodes) for preprocessing, and proof_by_abduction_with_prelude_using
 * forks one over the graph - prelude included, so the file stays self-contained after the
 * phase handover. Ticks every interval from search start until prove_timeout or a proof,
 * whichever ends the search; each phase's reporter overwrites the same file.
 *
 * Deliberately NOT named *.proof: write_verdict counts <stem>*.proof files as evidence that a
 * claimed proof was written, and a progress snapshot must never satisfy that invariant.
 * Written to a .tmp then renamed, so the external reader never sees a half-written file.
 *
 * The loop sleeps in one-second slices and re-checks its flag, so shutdown after the search -
 * or after the guard cancels it - costs at most a second. Reading the graph is safe
 * concurrently (SS.value_of_graph is synchronized); everything else it touches is its own. *)
fun fork_progress_reporter (pst: Proof.state) (start: Timing.start) (phase: string)
    (snapshot: unit -> string): {stop: unit -> unit} =
  let
    val ctxt = Proof.context_of pst;
    val interval = Config.get ctxt Top_Down_Util.progress_report_interval;
    val running = Synchronized.var "abduction_progress_reporter" true;
    fun stop_reporter () = Synchronized.change running (K false);
    val theory_base = Context.theory_base_name (Proof_Context.theory_of ctxt);
    fun write_file (text: string): unit =
      case getenv "PSL_PROOF_OUTPUT_DIR" of
        "" => ()
      | dir =>
          let
            val final_path = Path.explode (dir ^ "/" ^ theory_base ^ "_progress.thy");
            val tmp_path = Path.explode (dir ^ "/" ^ theory_base ^ "_progress.thy.tmp");
          in
            ignore (try (fn () =>
              (File.write tmp_path text;
               OS.FileSys.rename {old = Path.implode tmp_path, new = Path.implode final_path}))
              ())
          end;
    fun report (nth: int): unit =
      let
        val elapsed = Time.toReal (#elapsed (Timing.result start));
        val body =
          case snapshot () of
            "" => "(* No auxiliary lemma proved completely yet. *)"
          | haves => haves;
        val text =
          "(* AbductionProver progress report " ^ string_of_int nth ^ " (" ^ phase ^ "), "
          ^ Real.fmt (StringCvt.FIX (SOME 0)) elapsed
          ^ "s. The goal is not proved yet; these auxiliary lemmas are, completely, in\n\
          \   the order they were proved. *)\n"
          ^ body ^ "\n";
      in
        (tracing text; write_file text)
      end;
    (* The cap is insurance against the one path where stop is never called: a PIDE
       cancellation interrupting the owning command between fork and stop. A plain thread
       cannot be reached by group cancellation, so without a cap it would sleep-loop for the
       process's lifetime. Twice the search budget plus slack: overshoot is documented
       behaviour, and an idle 1s-sleep thread is cheap for that long. *)
    val lifetime_cap_slices =
      Real.ceil (Config.get ctxt Top_Down_Util.timeout_config * 2.0 + 600.0);
    fun loop (nth: int) (slices_used: int) (slices_left: int): unit =
      if not (Synchronized.value running) then ()
      else if slices_used > lifetime_cap_slices then ()
      else if slices_left <= 0
      then (ignore (try report nth); loop (nth + 1) slices_used (Real.ceil interval))
      else (OS.Process.sleep (seconds 1.0); loop nth (slices_used + 1) (slices_left - 1));
    (* An Isabelle_Thread, NOT a future, for the memory monitor's own reasons: a future that
     * sleeps occupies a worker slot, a joining worker can steal the sleepy task and run it
     * inline, and Future.cancel then interrupts a shared worker thread - which is how one
     * validation run died with a positionless "*** Interrupt" after both its searches had
     * finished cleanly. Shut down like the monitor too: clear the flag and join; the loop
     * notices within a second. Never interrupt it. *)
    val reporter =
      if interval <= 0.0 then NONE
      else SOME (Isabelle_Thread.fork (Isabelle_Thread.params "abduction_progress_reporter")
                   (fn () => loop 1 0 (Real.ceil interval)));
  in
    {stop = fn () =>
      (stop_reporter ();
       case reporter of NONE => () | SOME thread => Isabelle_Thread.join thread)}
  end;

(* proof_by_abduction_with_prelude_using *)
(* Shared by every proof_by_abduction* entry point below: the search itself never depends on
 * how its result is going to be printed. printer is print_necessary_proofs_only for a fresh
 * top-level goal (theorem/"prove") or print_necessary_proofs_for_subgoal/capture_graph_result
 * for a subgoal of an already-open proof (suggest/solve) - the printer
 * variants for a subgoal differ from each other in whether they print a script or capture the
 * search's result graph for solve to apply directly, and from the fresh-top-level
 * one in whether the root goal gets its own "lemma name: stmt" header at all. *)
(* tbc_facts feeds print_partial_proofs on the unsolved branch, where the graph's proved
 * auxiliaries are emitted alone; the printers for the solved branch already received it when
 * they were partially applied (see the wrappers below). *)
fun proof_by_abduction_with_prelude_using printer (tbc_facts: strings)
    (prelude_proofs:string) (pst:Proof.state) (start:Timing.start) (term:term) =
  let
    val max_depth                = 10;
    val ctxt                     = Proof.context_of pst;
    val standardized_term        =
      (* In context, so that variables the surrounding proof has fixed keep their names here
         too. focus_and_prepare_search already standardises this way, and reports the rename
         mapping the replay uses to translate the script back. Standardising again without a
         context renamed those same variables a second time, to names the mapping knows nothing
         about - so the script came back saying "induct var_0" for a goal whose variable is
         "xs", and replay failed with "Unable to figure out induct rule". *)
      Top_Down_Util.standardize_vnames_with_mapping_in_ctxt ctxt term |> fst
      |> Isabelle_Utils.strip_atyp |> Syntax.check_term ctxt;
    val synched_agraph           =
      SS.mk_synched_abduction_graph ctxt standardized_term: SS.synched_abduction_graph;
    val synched_filter_stats     = SS.mk_filter_statistics ();
    val synched_refutation_table = SS.mk_term2real_table (SOME synched_filter_stats);
    val synched_lemma_name_table = SS.mk_term2string_table ();
    val synched_proved_simps     = SS.mk_synched_proved_simps ();
    val synched_statistics       = Abduction_Statistics.mk_statistics ();
    val ori_prems                =
      Logic.strip_imp_prems term |> map TDU.standardize_vnames |> map Isabelle_Utils.strip_atyp
      : terms;
    val final_goal_key           = (Or_N, [standardized_term]);
    val _ = SS.try_to_prove_ornode_and_update_graph pst synched_agraph final_goal_key;
    val solved =
        if SS.final_goal_proved_completely synched_agraph: bool
        then (*Proof by abduction is unnecessary.*)
          let
            val agraph = SS.value_of_graph synched_agraph;
            val lemma_name2term = abduction_graph_to_string2term_table agraph: string2term_table;
            val final_goal_name = lemma_name_of agraph (Or_N, [standardized_term]);
            val _ =
              printer prelude_proofs pst agraph lemma_name2term
                final_goal_name;
          in
            true
          end
        else (*Proof by abduction is necessary.*)
          let
            val quintuple                =
              (pst, synched_agraph, synched_refutation_table, synched_lemma_name_table,
               synched_proved_simps, synched_filter_stats, ori_prems);
            (* PSL_EVAL_USE_WORKER_POOL_LOOP: rollback switch for run_worker_pool (see its own
               doc comment for the full rationale) - given a previous, from-scratch attempt at
               this same redesign ended up correct but slower than loop, defaulting to the new
               path but keeping loop itself completely untouched and reachable via one env var
               makes a direct A/B comparison always available, at zero ongoing cost. *)
            val use_worker_pool          = getenv "PSL_EVAL_USE_WORKER_POOL_LOOP" <> "0";
            (* The monitor spans TBC preprocessing as well as the search proper. An earlier
               version guarded only the search loop, which left prove_standard_simp_rules -
               itself heavily parallel and the phase a preprocessed_abduction run enters first -
               entirely unprotected. Everything expensive is inside the monitored group. *)
            fun run_search ()            =
              let
                val _ = prove_standard_simp_rules quintuple standardized_term: unit;
              in
                if use_worker_pool
                then run_worker_pool start synched_statistics quintuple
                else loop 0 max_depth start synched_statistics quintuple(*expensive abduction!*)
              end;
            (* Progress snapshots while the loop runs - see fork_progress_reporter. Forked
               outside the inner monitor (so the guard cancelling the search does not take the
               reporter with it mid-write) but stopped promptly on every way out below. The
               snapshot leads with the TBC prelude, so the file stays self-contained after the
               preprocessing phase's own reporter hands over to this one. *)
            val progress_reporter        =
              fork_progress_reporter pst start "graph search"
                (fn () =>
                   case (prelude_proofs,
                         partial_proofs_text tbc_facts pst (SS.value_of_graph synched_agraph)) of
                     ("", "") => ""
                   | (prelude, haves) => wrap_partial_block prelude haves);
            (* A cancelled search still has whatever it managed to prove recorded in the shared
               graph, so the interrupt is absorbed here and the surrounding code assembles a
               result from the graph exactly as it would after a timeout. *)
            (* No handler around this: with_memory_monitor returns an Exn.result rather than
               raising, and if this thread is interrupted anyway, the reporter future shares
               the enclosing group and dies with it. *)
            val solved_in_loop           =
              (case fst (with_memory_monitor (configured_floor (Proof.context_of pst))
                           memory_status_message (fn _ => run_search ())) of
                 Exn.Res solved => solved
               | Exn.Exn _ => SS.final_goal_proved_completely synched_agraph);
            val _                        = #stop progress_reporter ();
            val final_graph              =
              SS.value_of_graph synched_agraph: Abduction_Graph.abduction_graph;
            val lemma_name2term          =
              abduction_graph_to_string2term_table final_graph: string2term_table;
            val final_goal_name          =
              lemma_name_of final_graph (Or_N, [standardized_term]): string;
            val _                        =
              if solved_in_loop
              then (TBC_Utils.tbc_trace "  printer: solved branch";
                    printer prelude_proofs pst final_graph lemma_name2term
                      final_goal_name)
              (* Not solved - by timeout, or by the frontier of open or-nodes running out. Either
                 way, report what was proved rather than nothing. *)
              else (TBC_Utils.tbc_trace "  printer: partial branch";
                    print_partial_proofs tbc_facts prelude_proofs pst final_graph);
          in
            solved_in_loop
          end;
  in
    solved
  end;


(* capture_graph_result *)
(* A "printer" (see proof_by_abduction_with_prelude_using above) that captures the search's
 * result graph instead of printing anything, via a ref cell supplied by the caller - the
 * search itself always runs against its own isolated Proof.theorem-based context (see pst0 in
 * Abduction.thy's run_abduction_search/run_solve), never the caller's real, live proof state,
 * so the only way to get the graph out to apply it to that real state afterwards is to
 * capture it here rather than have the search apply it directly. *)
fun capture_graph_result
    (result_ref: (abduction_graph * string2term_table * string) option Unsynchronized.ref)
    (_:string) (_:Proof.state) (ag:abduction_graph) (name2term:string2term_table)
    (goal_name:string): string =
  (result_ref := SOME (ag, name2term, goal_name); "");

(* search_for_subgoal_and_capture_graph *)
(* Runs exactly the same search as proof_by_abduction_for_subgoal_with_prelude, but instead of
 * printing a suggested script, captures and returns the search's result graph (if solved) so
 * that the caller can apply it directly to a live Proof.state via apply_graph_proof_to_pst -
 * the search/apply split run_solve (Abduction.thy) uses. Always without a text prelude: unlike
 * proof_by_abduction_for_subgoal_with_prelude's own prelude_proofs (raw proof text prepended
 * ahead of the search), run_solve's own TBC-preprocessed auxiliary facts are already
 * established as real local facts in pst's context by the time this runs (see
 * apply_tbc_prelude_aux_to_pst), so no text prelude is needed here at all. Always for a
 * subgoal (solve only ever targets an already-open proof's pending subgoal). *)
fun search_for_subgoal_and_capture_graph (tbc_facts: strings) (pst:Proof.state)
    (start:Timing.start) (term:term)
    : bool * (abduction_graph * string2term_table * string) option =
  let
    val result_ref =
      Unsynchronized.ref NONE
      : (abduction_graph * string2term_table * string) option Unsynchronized.ref;
    val solved = proof_by_abduction_with_prelude_using (capture_graph_result result_ref)
      tbc_facts "" pst start term: bool;
  in
    (solved, !result_ref)
  end;

fun proof_by_abduction_with_prelude tbc_facts prelude_proofs pst start term =
  proof_by_abduction_with_prelude_using (print_necessary_proofs_only tbc_facts)
    tbc_facts prelude_proofs pst start term;

fun proof_by_abduction pst start term =
  proof_by_abduction_with_prelude [] "" pst start term;

fun proof_by_abduction_for_subgoal_with_prelude caller rename_mapping tbc_facts prelude_proofs
    pst start term =
  proof_by_abduction_with_prelude_using
    (print_necessary_proofs_for_subgoal caller rename_mapping tbc_facts) tbc_facts
    prelude_proofs pst start term;

fun proof_by_abduction_for_subgoal caller rename_mapping pst start term =
  proof_by_abduction_for_subgoal_with_prelude caller rename_mapping [] "" pst start term;

end;