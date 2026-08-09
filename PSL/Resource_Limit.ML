(*  Title:      PSL/Resource_Limit.ML
    Author:     Yutaka Nagashima

Machine-memory sensing and an admission-control gate for expensive external
tools, shared by PSL, TBC and AbductionProver.

Two facilities:

  * memory sensing (available_mb / total_mb), portable across Linux, macOS and
    Windows, always fail-open;
  * a counting gate (with_slot) that bounds how many expensive operations run at
    once, and blocks in a way that is safe inside Isabelle's future pool.

Both exist because of the same measured problem. Sledgehammer launches every
prover in "sledgehammer_provers" concurrently as external processes, and Isabelle
bounds their time but not their memory - veriT is invoked with only --max-time
(see veriT_options, ~~/src/HOL/Tools/SMT/smt_systems.ML). AbductionProver then
calls Sledgehammer from several levels of nested parallelism at once, so the
number of provers in flight is a product of those levels rather than a bound. In
the recorded TIP15 evaluation the result was 149 runs killed outright by the OS
OOM killer or by Poly/ML's "Run out of store"; a single diverging veriT was
measured at 6.35GB.
*)
signature RESOURCE_LIMIT =
sig

(* Physical memory, in megabytes. NONE when the platform cannot be probed. *)
val total_mb: unit -> real option;
val available_mb: unit -> real option;
val status_message: unit -> string;

(* Tunables, declared as Isabelle config attributes so they can be set with
   "declare [[max_parallel_hammers = 4]]" from a theory - discoverable via
   print_options, per-context, type-checked, and usable from jEdit. An earlier
   version read environment variables here, which is invisible to exactly the
   interactive users these limits exist to protect. *)
val max_parallel_hammers: int Config.T;
val max_parallel_searches: int Config.T;
val min_free_mb: int Config.T;
val hammer_memory_quota_mb: int Config.T;

(* How many Sledgehammer invocations may run at once: max (1, min (cores/2, memory/quota)).
   hammer_slots reads the machine and the context; hammer_slots_for is the rule alone, so it can
   be tested without a machine of the right shape. *)
val hammer_slots_for: {cores: int, memory_mb: real option, quota_mb: int} -> int;
val hammer_slots: Proof.context -> int;

(* Runs the body holding one slot of the budget, blocking until one is free. The
   budget bounds concurrent *expensive external* work (Sledgehammer invocations)
   independently of how many layers of parallelism sit above. The limit is passed
   in by the caller, which reads it from its own context. *)
val with_slot: int -> (unit -> 'a) -> 'a;

(* The same discipline one level up: how many whole abduction searches may run in
   this process at once. See max_parallel_searches below for why the default is one. *)
val with_search_slot: int -> (unit -> 'a) -> 'a;

(* Test instrumentation only (Search_Slot_Test): stretches the inside of release by this many
   milliseconds, so a test can land a cancellation inside it deterministically instead of
   sweeping phases and hoping. The defect this helps pin is an interrupt aborting release
   after the slot was counted; with the release masked the stretch is uninterruptible and the
   test passes by construction, with it unmasked a single aimed cancellation leaks. Zero (the
   default) is free. Same spirit as PSL_MEMORY_GUARD_TRIP_AFTER: the window cannot be hit by
   choosing timings from outside, so the code offers the handle. *)
val test_release_delay_ms: int Unsynchronized.ref;

(* How many searches hold a slot right now. For telling a user their command is queued
   behind an earlier search rather than hung; racy by nature, only good for a message. *)
val search_slots_in_use: unit -> int;

(* A request to wind the search down, and the search's side of it. See request_stop. *)
val request_stop: unit -> unit;
val clear_stop_request: unit -> unit;
val stop_is_requested: unit -> bool;

(* The whole search's wall-clock deadline, so that every phase can be bounded by the caller's
   prove_timeout and not only the phase that happens to own the clock. See set_deadline_in. *)
val set_deadline_in: real -> unit;   (*seconds from now; a non-positive value clears it*)
val clear_deadline: unit -> unit;
val deadline_passed: unit -> bool;

end;

structure Resource_Limit: RESOURCE_LIMIT =
struct

(** memory sensing **)

local

fun first_number (line:string): real option =
  case String.tokens (fn c => not (Char.isDigit c)) line of
    (digits :: _) => Option.map Real.fromInt (Int.fromString digits)
  | [] => NONE;

(* "try" rather than a bare handler: it yields NONE on a missing or unreadable
   source while still letting Interrupt through, which matters because these are
   called from inside cancellable worker tasks. *)
fun proc_field_kb (file:string) (key:string): real option =
  case try (File.read o Path.explode) file of
    NONE => NONE
  | SOME txt =>
      (case find_first (fn l => String.isPrefix (key ^ ":") l) (split_lines txt) of
         NONE => NONE
       | SOME l => first_number l);

fun shell_first_number (cmd:string): real option =
  case try Isabelle_System.bash_output cmd of
    SOME (out, 0) =>
      (case filter_out (fn l => l = "") (split_lines out) of
         (l :: _) => first_number l
       | [] => NONE)
  | _ => NONE;

fun platform () = getenv "ISABELLE_PLATFORM_FAMILY";

(* Shelling out costs far more than reading /proc, and the callers poll, so
   non-Linux results are cached briefly rather than recomputed per call. *)
val cache = Synchronized.var "Resource_Limit.cache" (Time.zeroTime, NONE: real option);
val cache_ttl = seconds 2.0;

fun cached (compute: unit -> real option): real option =
  let
    val now = Time.now ();
    val (stamp, value) = Synchronized.value cache;
  in
    if is_some value andalso Time.< (now, Time.+ (stamp, cache_ttl)) then value
    else let val v = compute () in Synchronized.change cache (K (now, v)); v end
  end;

in

fun total_mb () =
  case platform () of
    "linux" => Option.map (fn kb => kb / 1024.0) (proc_field_kb "/proc/meminfo" "MemTotal")
  | "macos" => Option.map (fn b => b / 1048576.0) (shell_first_number "sysctl -n hw.memsize")
  | "windows" =>
      Option.map (fn kb => kb / 1024.0)
        (shell_first_number "wmic ComputerSystem get TotalPhysicalMemory /value 2>/dev/null \
          \| tr -dc '0-9\\n' | grep -v '^$' | head -1")
  | _ => NONE;

fun available_mb () =
  case platform () of
    (* MemAvailable is the kernel's own estimate of what can be handed out
       without swapping, which is exactly the quantity that decides whether the
       OOM killer fires - much better than MemFree, which ignores reclaimable
       page cache. *)
    "linux" => Option.map (fn kb => kb / 1024.0) (proc_field_kb "/proc/meminfo" "MemAvailable")
  | "macos" =>
      (* vm_stat reports pages; free + inactive + speculative are reclaimable.
         The page size is fixed at 4096 on every Apple platform Isabelle runs on. *)
      cached (fn () =>
        shell_first_number
          "vm_stat | awk '/Pages (free|inactive|speculative)/ {gsub(/[^0-9]/,\"\",$NF); s+=$NF} \
            \END {print int(s*4096/1048576)}'")
  | "windows" =>
      cached (fn () =>
        Option.map (fn kb => kb / 1024.0)
          (shell_first_number "wmic OS get FreePhysicalMemory /value 2>/dev/null \
            \| tr -dc '0-9\\n' | grep -v '^$' | head -1"))
  | _ => NONE;

end;

fun status_message () =
  let
    fun show NONE = "?" | show (SOME (r:real)) = Real.fmt (StringCvt.FIX (SOME 0)) r;
  in
    "MemAvailable=" ^ show (available_mb ()) ^ "MB of " ^ show (total_mb ()) ^ "MB"
  end;


(** admission control **)

(* The gate is a counter plus a "wakeup" future that is fulfilled and replaced
   whenever a slot is released.

   Waiters block on Future.join, never on Synchronized.guarded_access. That is
   not a stylistic preference: guarded_access is a raw condition-variable wait,
   invisible to the future scheduler, so a task parked in it keeps occupying one
   of the threads=N pool slots while doing nothing. Isabelle's own implementation
   manual warns that "allocation of runtime resources may be distorted if workers
   yield CPU time (e.g. via system sleep or wait operations)". This was measured
   here rather than taken on faith: with numb_of_processors - 1 workers parked in
   guarded_access, an unrelated Par_List.map job sharing the pool went from 2.25s
   to 14.29s - essentially serialised - while the identical test using
   Future.join showed no effect at all (1.93s vs 1.95s). guarded_access remains
   perfectly appropriate for the short, non-blocking state updates it is used for
   below; what must never happen is *waiting* on it from a pool thread. *)

(* 0 means "derive from the machine": half the processors for hammers, and a
   memory floor sized in still_has_memory. Both are declared here so the two
   resource limits sit together. *)
(* Attrib.setup_config_* rather than Config.declare_*: the former also registers the attribute,
   which is what makes "declare [[max_parallel_hammers = 4]]" work from a theory. Config.declare_*
   alone yields a config only reachable from ML via Config.put - no use to the interactive users
   these limits exist to protect. *)
val max_parallel_hammers =
  Attrib.setup_config_int \<^binding>\<open>max_parallel_hammers\<close> (K 0): int Config.T;

(* How many whole searches (prove/prove_by_abduction/suggest/solve) may run in this
 * process at once. Default one: searches queue rather than overlap.
 *
 * Overlap is not hypothetical. Both a batch build and jEdit fork each proof block into a
 * future, so a theory's "suggest ... oops" completes its toplevel transaction in under a
 * second while the search runs on; the next command's search then starts beside it. Measured
 * (2026-08-08, an 18-invocation chain of suggests over TIP Prod prop_05/prop_07): three
 * searches for the same goal interleaved in one trace within the first three seconds, a
 * direct attempt whose budget is 60s took 204.2s wall under the contention, and every
 * concurrently running search shared one deadline instant - each newly starting search
 * overwrote it, and the first to finish cleared it for the rest. In a jEdit session the same
 * pile-up happens whenever edits re-execute a buffer holding several suggest commands, and it
 * ends with the memory guard requesting a stop that every search obeys - which a user sees as
 * "the prover has started giving up easily".
 *
 * Serialising also makes the process-wide deadline single-writer, keeps each search's memory
 * floor derived from a machine it has to itself, and lets each search have all the hammer
 * slots. Waiting is done gate-style (Future.join, never guarded_access - see the gate comment
 * below) and an interrupted waiter propagates the interrupt without holding anything, so PIDE
 * cancelling a queued command does not leak a slot. *)
val max_parallel_searches =
  Attrib.setup_config_int \<^binding>\<open>max_parallel_searches\<close> (K 1): int Config.T;

val min_free_mb =
  Attrib.setup_config_int \<^binding>\<open>min_free_mb\<close> (K 0): int Config.T;

(* Memory a single Sledgehammer invocation is assumed to want, in megabytes.
 *
 * One number with two jobs. It divides the machine's memory to give the number of hammers that
 * may run at once (hammer_slots_for), and it is the per-process ceiling the prover wrappers
 * impose (Eval/make_prover_memory_wrappers.sh), so admission control and enforcement cannot
 * disagree about what a hammer costs.
 *
 * 2048 because that is what the wrapper script already defaulted to, not because it is derived
 * from anything: a measured diverging veriT reached 6.35GB, so this is a budget rather than a
 * prediction. *)
val hammer_memory_quota_mb =
  Attrib.setup_config_int \<^binding>\<open>hammer_memory_quota_mb\<close> (K 2048): int Config.T;

(* How many hammers may run at once, from the machine rather than from a setting.
 *
 * Processors alone was the whole rule, and it is the wrong shape: a hammer's cost is memory, not
 * cycles. On a 12-core 12GB host that allowed six concurrent invocations, each launching every
 * prover in "sledgehammer_provers", against a machine that one diverging veriT can fill by
 * itself. The position matrix ran out of memory in 12 of 37 runs.
 *
 * Fail-open, like the rest of the sensing here: a machine whose memory cannot be probed keeps the
 * old processor-derived answer rather than being throttled to one on a guess. *)
fun hammer_slots_for {cores: int, memory_mb: real option, quota_mb: int}: int =
  let
    val by_cores = Int.max (1, cores div 2);
    val by_memory =
      if quota_mb <= 0 then by_cores
      else
        case memory_mb of
          NONE    => by_cores
        | SOME mb => Int.max (1, Real.floor (mb / Real.fromInt quota_mb));
  in
    Int.max (1, Int.min (by_cores, by_memory))
  end;

(* Read against what is free now, not against the machine's total, so the budget narrows as the
   search grows: the memory a running search already holds is memory the next hammer cannot have.
   Falling back to the total keeps a platform that reports no MemAvailable working. *)
fun hammer_slots (ctxt: Proof.context): int =
  case Config.get ctxt max_parallel_hammers of
    0 =>
      hammer_slots_for
        {cores     = Thread.Thread.numProcessors (),
         memory_mb = (case available_mb () of SOME mb => SOME mb | NONE => total_mb ()),
         quota_mb  = Config.get ctxt hammer_memory_quota_mb}
  | k => Int.max (1, k);

type gate_state = {in_use: int, wakeup: unit future};

(* request_stop / stop_is_requested *)
(* The memory guard's polite channel: "stop taking on new work", asked rather than imposed.
 *
 * The guard's hard stop is Future.cancel_group, and cancelling is what makes the session
 * unsafe. Future.cancel_now interrupts the threads currently running the group's tasks, and
 * Future.cancel_later goes on re-interrupting them until they are all finished. Under memory
 * pressure the unwinding is slow, so that loop spins - and an interrupt delivered after an
 * earlier one has already been consumed arrives on a thread whose break flag is clear, which
 * is precisely what Isabelle reports as Interrupt_Breakdown. Measured on a 12GB host, eight
 * runs of TIP_prop_01: the guard reported cleanly every time and the session died anyway in
 * four of them, with a positionless breakdown belonging to no command. The first two runs were
 * clean and the last two were not, which is the signature of a loop that spins longer the
 * worse the pressure gets.
 *
 * If the search has stopped by itself before the group is cancelled, there is nothing running
 * to interrupt: cancel_now returns empty, cancel_later never starts, and the cancellation is
 * reduced to marking the group so that queued work is skipped. That is what this flag buys.
 *
 * It is deliberately global rather than per-search. The condition it reports is a property of
 * the machine, so every search running on it should wind down, and a search that starts
 * afterwards should not inherit the request - hence clear_stop_request at the start of each
 * guarded run. *)
val stop_request = Synchronized.var "Resource_Limit.stop_request" false;
fun request_stop () = Synchronized.change stop_request (K true);
fun clear_stop_request () = Synchronized.change stop_request (K false);
fun stop_is_requested () = Synchronized.value stop_request;

(* set_deadline_in / deadline_passed *)
(* The caller's prove_timeout, as a wall-clock instant every phase can read.
 *
 * It lives here, beside the stop request, because the two answer the same kind of question -
 * "should I start more work?" - and are asked in the same places. It could not live with the
 * config it comes from: Top_Down_Util owns prove_timeout and sits in Abduction/, which imports
 * TBC, so TBC cannot see it. TBC already reads this structure for stop_is_requested, so a
 * deadline here needs no new dependency at all.
 *
 * Why it was needed. prove_timeout was read in exactly one place, Proof_By_Abduction's
 * get_timeout, so only the abduction graph search was bounded by it. TBC's preprocessing and its
 * conjecturing rounds never consulted it and were bounded instead by a round count and each
 * attempt's own hammer duration - a product that has nothing to do with what the user asked for.
 * Measured: prove_timeout = 240 still produced nine-minute sessions.
 *
 * An instant rather than a duration, so that phases which do not own the clock do not have to be
 * told how long the phases before them took. NONE means unbounded, which is what a caller that
 * never sets it gets. *)
val deadline = Synchronized.var "Resource_Limit.deadline" (NONE: Time.time option);

fun set_deadline_in (seconds_from_now: real) =
  Synchronized.change deadline
    (K (if seconds_from_now <= 0.0 then NONE
        else SOME (Time.now () + Time.fromReal seconds_from_now)));

fun clear_deadline () = Synchronized.change deadline (K NONE);

fun deadline_passed () =
  case Synchronized.value deadline of
    NONE      => false   (*unbounded: no caller has set one*)
  | SOME when => Time.now () > when;

(* The wakeup promise must not belong to any search's task group. Future.promise puts the new
 * future in a subgroup of the CALLING worker's group (promise_name uses worker_subgroup, see
 * ~~/src/Pure/Concurrent/future.ML) - and release runs on the releasing search's own thread,
 * inside its cancellable group. A promise owned that way dies with its creator: when the
 * finished search's group is torn down (an "oops" proof future's discarded result, the guard's
 * hard cancel, a failing sibling theory), the promise is cancelled and every waiter parked in
 * Future.join receives an interrupt that has nothing to do with it. Measured, 2026-08-08: two
 * searches released their slots back to back and the next two queued searches both died with
 * a bare Interrupt within seconds of starting. The hammer gate had the same hazard from the
 * day it was written - a waiter interrupted this way surfaces as "TBC skipped a generated
 * conjecture after a local parallel proof-attempt failure", i.e. as a search quietly weakened.
 *
 * So promises are manufactured on a fresh detached thread: there worker_group () is NONE and
 * the promise lands in a root-parented group nobody cancels. One short-lived thread per
 * release is noise next to the seconds-to-minutes operations these gates meter. *)
fun detached_promise (): unit future =
  let
    val holder = Synchronized.var "Resource_Limit.promise_holder" (NONE: unit future option);
    val thread =
      Isabelle_Thread.fork (Isabelle_Thread.params "resource_limit_gate")
        (fn () => Synchronized.change holder (K (SOME (Future.promise (fn () => ())))));
    val _ = Isabelle_Thread.join thread;
  in the (Synchronized.value holder) end;

fun mk_gate (name: string): gate_state Synchronized.var =
  Synchronized.var name {in_use = 0, wakeup = detached_promise ()};

(* Two independent budgets, one mechanism: hammers (external prover invocations) and whole
   searches. They must not share a counter - a search holding the only search slot goes on to
   claim hammer slots, so one gate for both would deadlock against itself. *)
val gate = mk_gate "Resource_Limit.gate";
val search_gate = mk_gate "Resource_Limit.search_gate";

val test_release_delay_ms = Unsynchronized.ref 0;

local

(* Claim a slot if one is free; otherwise report the wakeup to wait on. Both the
   test and the choice of wakeup happen inside one change_result, so no release
   can slip in between them and be missed. *)
fun try_claim (g: gate_state Synchronized.var) (limit:int) =
  Synchronized.change_result g (fn (s as {in_use, wakeup}) =>
    if in_use < limit
    then (NONE, {in_use = in_use + 1, wakeup = wakeup})
    else (SOME wakeup, s));

fun release (g: gate_state Synchronized.var) =
  let
    val fresh = detached_promise ();
    (*The stretchable point sits where the live defect hit: after the slot's replacement
      promise exists, before the count comes down. See test_release_delay_ms in the signature.*)
    val _ =
      if Unsynchronized.! test_release_delay_ms = 0 then ()
      else OS.Process.sleep (Time.fromMilliseconds (Unsynchronized.! test_release_delay_ms));
    val old =
      Synchronized.change_result g (fn {in_use, wakeup} =>
        (wakeup, {in_use = Int.max (0, in_use - 1), wakeup = fresh}));
  in
    ignore (try (Future.fulfill old) ())
  end;

(* Interrupt-safety is the whole design here, and it was measured to matter: jEdit cancels and
 * re-executes commands on every edit, so interrupts arrive at arbitrary points. The first
 * version did acquire/capture/release with interrupts live throughout, which has two windows:
 * an interrupt between a successful claim and the capture orphans the claim, and an interrupt
 * inside release (whose detached_promise forks and joins a thread - an interruptible point)
 * aborts it after the claim is still counted. Either way in_use stays high forever, and every
 * later search in the session prints "waiting for an earlier search" and waits for a slot
 * nobody holds - observed live in jEdit (2026-08-08) as "you did not fix it".
 *
 * So: the body and the *waiting* run with the caller's own attributes (a queued command must
 * stay cancellable), but the claim and the release run masked. A claim that succeeds always
 * reaches the capture below, and the release always completes; an interrupt pending at either
 * point is delivered inside the capture instead, where Exn.release re-raises it after the
 * slot is safely returned. *)
fun slotted (g: gate_state Synchronized.var) (limit:int) (body: unit -> 'a): 'a =
  Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
    let
      fun interruptible f x = Thread_Attributes.with_attributes orig_atts (fn _ => f x);
      fun wait_then_claim () =
        case try_claim g (Int.max (1, limit)) of
          NONE => ()
        | SOME wakeup =>
            (interruptible (fn () => ignore (try Future.join wakeup)) ();
             wait_then_claim ());
      val _ = wait_then_claim ();
      val result = Exn.capture (fn () => interruptible body ()) ();
      val _ = release g;
    in Exn.release result end);

in

fun with_slot (limit:int) (body: unit -> 'a): 'a = slotted gate limit body;

fun with_search_slot (limit:int) (body: unit -> 'a): 'a = slotted search_gate limit body;

fun search_slots_in_use () = #in_use (Synchronized.value search_gate);

end;

end;
