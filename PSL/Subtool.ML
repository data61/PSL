(*  Title:      src/Subtool.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file provides utility functions that are useful to generate tactics at run-time.
*)

(*** SUBTOOL: The state monad tactic interface for sub-tools. ***)
signature SUBTOOL =
sig
  val state_stttac: real -> Proof.state Dynamic_Utils.stttac;
end;

(*** SUBTOOLS: A collection of sub-tools. ***)
signature SUBTOOLS =
sig
  (* A proof step to apply: the facts to chain in, and the method text.
     This is what a sub-tool actually produces. Sledgehammer hands it to us as structured data
     (Sledgehammer.SH_Some carries the proof_method and the facts it used); representing it as
     such means the only place a method is ever parsed is where one must be, to run it. *)
  type apply_step = {using: string list, methN: string};
  val apply_step_to_logtac:
    apply_step -> real option (*importance*) -> real (*timeout*) -> Proof.state ->
    (Dynamic_Utils.log * Proof.state) Seq.seq;
  val tool_output_n_timeout_to_logtac:
    string -> real option (*importance*) -> real (*timeout*) -> Proof.state ->
    (Dynamic_Utils.log * Proof.state) Seq.seq;
  (* The method part of a printed one-line proof, rendered with the spacing it was written with. *)
  val method_text_of: Keyword.keywords -> string -> string;
  val quickcheck  : real -> Proof.state Dynamic_Utils.stttac;
  val nitpick     : real -> Proof.state Dynamic_Utils.stttac;
  val hammer      : real -> Proof.state Dynamic_Utils.stttac;
  val is_solved   : unit -> Proof.state Dynamic_Utils.stttac;
  val defer       : unit -> Proof.state Dynamic_Utils.stttac;
  val subgoal     : unit -> Proof.state Dynamic_Utils.stttac;
  val smart_induct: real -> Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
  val sh_output_to_sh_stttac:
    string -> Proof.state Dynamic_Utils.stttac;(*used in United Reasoning*)
end;

(*** SUBTOOLS: A collection of sub-tools. ***)
structure Subtools: SUBTOOLS =
struct

(** Quickcheck_Tactic: Quickcheck as assertion tactic. **)
structure Quickcheck_Tactic : SUBTOOL =
struct

fun nontac (timeout:real) (state:Proof.state) =
  let
    (*do_trace and show_trace are provided for the purpose of debugging.*)
    val do_trace        = false;
    fun show_trace text = if do_trace then tracing text else ();
    val quickcheck      = Quickcheck.quickcheck;
    val single          = Seq.single state;
    fun trace_no_cexm _ = show_trace "Quickcheck.quickcheck found no counterexample";
    fun trace_cexm _    = show_trace "Quickcheck.quickcheck found a  counterexample";
    fun trace_scexn _   = show_trace ("Quickcheck.quickcheck found a potentially spurious " ^
                                      "counterexample due to underspecified functions");
    fun trace_to to     = show_trace ("Quickcheck timed out after " ^ Timeout.message to);
    val timeout         = Isabelle_Utils.timeout_apply (seconds timeout);
    fun get_result _    =  (case timeout (quickcheck [] 1) state of
      NONE => (trace_no_cexm (); single)
    | SOME (genuine, _) => if genuine then (trace_cexm (); Seq.empty) else (trace_scexn (); single))
    handle Timeout.TIMEOUT to => (trace_to to; single);
  in
    Utils.try_with single get_result state
  end;

fun state_stttac timeout = Dynamic_Utils.log_n_nontac_to_stttac ([], nontac timeout);

end;

(** Nitpick_Tactic: Nitpick as assertion tactic. **)
structure Nitpick_Tactic : SUBTOOL =
struct

fun state_stttac (timeout:real) (state:Proof.state) (log:Dynamic_Utils.log) =
  let

    val thy:theory         = (Proof.theory_of state);
    val params             = Nitpick_Commands.default_params thy [];
    val timeout            = Isabelle_Utils.timeout_apply (seconds timeout);
    val do_trace           = false;
    fun show_trace text    = if do_trace then tracing text else ();
    fun trace_to to        = show_trace ("Nitpick timed out after " ^ Timeout.message to);
    fun nitpick_result' _  = Nitpick.pick_nits_in_subgoal state params Nitpick.Normal 1 1;
    val nitpick_result     =
          timeout nitpick_result' () handle Timeout.TIMEOUT to => (trace_to to; ("timeout", []));
    (*"genuine" means "genuine counter-example".*)
    val fst_result         = fst nitpick_result;
    val nitpick_succeed    = fst_result = Nitpick.genuineN;
    val importance         = if fst_result = Nitpick.quasi_genuineN
                             then 0.1 else if fst_result = Nitpick.potentialN
                             then 0.6 else 1.0;(*TODO: magic numbers*)
    val node               =
          Dynamic_Utils.Apply {using = [], methN = "-", back = 0, importance = SOME importance}
          : Dynamic_Utils.node;
    val single             = Seq.single (log @ [node], state);
    val nitpick_tac_result = if nitpick_succeed then Seq.empty else single
                           : (Dynamic_Utils.node list * Proof.state) Seq.seq;
  in
    nitpick_tac_result
  end;

end;

type apply_step = {using: string list, methN: string};

(* apply_step_to_logtac *)
(* Applies a step given as data: the facts to chain in, by name, and the method text.
 *
 * A method still has to be parsed - there is no way to run one otherwise - but nothing else
 * here goes through a string. In particular the facts are looked up by name rather than
 * recovered by re-parsing a "using ..." prefix out of a message someone printed earlier. *)
fun apply_step_to_logtac ({using, methN}: apply_step) (importance: real option) (to:real)
    (state:Proof.state) =
  let
    val ctxt          = Proof.context_of state;
    val check_text    = Method.check_text ctxt;
    val fail_trange   = (Method.Basic (K Method.fail), Position.no_range): Method.text_range;
    val keywords      = Thy_Header.get_keywords (Proof.theory_of state);
    val parsed_range  =
      (let
         val tokens =
           Token.explode keywords Position.none (methN ^ " parserStopsWithMe")
           |> filter_out (fn t => Token.is_kind Token.Space t);
       in fst (Method.parse tokens) end)
      handle ERROR _ => fail_trange;
    val checked_range =
      (apfst check_text parsed_range handle ERROR _ => fail_trange): Method.text_range;
    val node          =
      Dynamic_Utils.Apply {using = using, methN = methN, back = 0, importance = importance}
      : Dynamic_Utils.node;
    val state_w_using =
      if null using then state
      else
        let val thms = maps (fn name => these (try (Proof_Context.get_thms ctxt) name)) using
        in Proof.using [[(thms, [])]] state end;
    fun timeout f     = Utils.try_with Seq.empty (Isabelle_Utils.timeout_apply (seconds to) f);
    val tac_results   = timeout (Proof.apply checked_range) state_w_using
                        |> Seq.filter_results
                        |> Utils.try_with Seq.empty (timeout (Seq.try Seq.hd)): Proof.state Seq.seq;
  in
    Seq.map (fn x => ([node], x)) tac_results : (Dynamic_Utils.log * Proof.state) Seq.seq
  end;

(* method_text_of *)
(* The method part of a printed one-line proof ("apply (induct x)", "using foo by auto"),
   rendered as it was written.
 *
 * Rendered from the original tokens, blanks and all, rather than by rejoining the space-filtered
 * ones with a single blank each. That rejoin is why a method built as
 * "(induct \"var_1\" arbitrary: var_2)" came back as "( induct \"var_1\" arbitrary : var_2 )":
 * with the blanks discarded, every bracket and colon is a free-standing token and gets a space on
 * either side. It compiles, but this string is the one that ends up in a generated script, so it
 * is what a user reads and pastes.
 *
 * Parsing still runs on the space-filtered tokens - only the rendering changed. Which of the
 * original tokens to render is found by counting: the parser consumed some number of the tokens
 * it can see, and that same count of non-blank tokens locates the same place in the full list. *)
fun method_text_of (keywords: Keyword.keywords) (tool_output: string): string =
  let
    val parse_using =
          Parse.and_list1 Parse.thms1 : (Facts.ref * Token.src list) list list Token.parser;
    val parse_one   = Scan.one (K true): Token.T list -> Token.T * Token.T list;
    val p_get_meth  = (parse_one |-- parse_using) -- parse_one;
    fun is_space (token: Token.T) = Token.is_kind Token.Space token;
    val op_w_stopper = tool_output ^ " parserStopsWithMe";
    val all_tokens   = Token.explode keywords Position.none op_w_stopper: Token.T list;
    val tokens       = filter_out is_space all_tokens: Token.T list;
    val remaining    =
          if String.isPrefix "using " tool_output
          then p_get_meth tokens |> snd
          else parse_one  tokens |> snd;
    val consumed     = length tokens - length remaining: int;
    fun drop_consumed n ts =
      if n <= 0 then ts
      else
        case ts of
          []        => []
        | t :: rest => drop_consumed (if is_space t then n else n - 1) rest;
    (*drops "parserStopsWithMe" and the blank in front of it*)
    fun drop_stopper ts =
      case drop_suffix is_space ts of
        []  => []
      | ts' => drop_suffix is_space (Utils.init ts');
  in
    drop_consumed consumed all_tokens
    |> drop_prefix is_space  (*the blank between "apply"/"by" and the method itself*)
    |> drop_stopper
    |> map Token.unparse
    |> implode: string
  end;

(** sledgehammer/sem_ind output to monadic tactics on proof state **)
(* Parses a printed one-line proof back into an apply_step. Retained for callers that only have
   such a string (United Reasoning); Sledgehammer itself no longer goes through here. *)
fun tool_output_n_timeout_to_logtac
    (sh_output:string) (importance: real option) (to:real) (state:Proof.state) =
  let
    (*syntax sugars*)
    type text_range        = Method.text_range;
    fun is_using sh_output = String.isPrefix "using " sh_output;
    val parse_using =
          Parse.and_list1 Parse.thms1 : (Facts.ref * Token.src list) list list Token.parser;
    val parse_method       = Method.parse                 : text_range Token.parser;
    val parse_one          = Scan.one (K true)            : Token.T list -> Token.T * Token.T list;
    type ctxt              = Proof.context;
    type T                 = Token.T;
    type ref               = Facts.ref;
    type srcs              = Token.src list;
    type keywords          = Keyword.keywords;
    val thy                = Proof.theory_of state       : theory;
    val ctxt               = Proof.context_of state      : ctxt;
    val keywords           = Thy_Header.get_keywords thy : keywords;

    (*function body*)
    val op_w_stopper  = sh_output ^ " parserStopsWithMe";
    val tokens        = Token.explode keywords Position.none op_w_stopper
                      |> filter_out (fn token:T => Token.is_kind Token.Space token) : T list;
    val parser        = if   is_using sh_output
                        then (parse_one |-- parse_using) -- (parse_one |-- parse_method)
                        else (parse_one |-- parse_method) >> (fn x => ([], x));
    val methN:string  = method_text_of keywords sh_output;
    val result        = parser tokens
                      : ((ref * srcs) list list * text_range) * T list;
    val using_raw     = (#1 o #1) result : (ref * srcs) list list;
    val text_range    = (#2 o #1) result : text_range;
    val check_text    = Method.check_text ctxt;
    val fail_trange   = (Method.Basic (K Method.fail), Position.no_range) : Method.text_range;
    val checked_range = (apfst check_text text_range handle ERROR _ => fail_trange) : text_range;
    val using_strings = using_raw |> List.concat |> map (Facts.string_of_ref o #1) handle Empty =>
                        (if Utils.debug
                         then tracing "using_strings in sh_output_to_sh_logtac failed." else ();
                         ["Failed constructing using_strings."])
                      : string list;
    val node          =
          Dynamic_Utils.Apply {using = using_strings, methN = methN, back = 0,
            importance = importance}
          : Dynamic_Utils.node;
    (*print messages for debugging.*)
    val _ =
      let
        val app = case node of
          Dynamic_Utils.Apply app_node => app_node
        | _ => error "app in Sledgehammer_Tactic panics.";
        fun tracing1 _ = tracing ("methN in node is " ^ #methN app);
        fun tracing2 _ = tracing "using_strings are ...";
        fun tracing3 _ = map tracing using_strings;
      in
        if Utils.debug then (tracing1 (); tracing2 (); tracing3 (); ()) else ()
      end;
    val state_w_using = Proof.using_cmd using_raw state : Proof.state;
    fun timeout f     = Utils.try_with Seq.empty (Isabelle_Utils.timeout_apply (seconds to) f)
    val tac_results   = timeout (Proof.apply checked_range) state_w_using
                        |> Seq.filter_results
                        (*Why Seq.try Seq.hd? Because we want to evaluate the head of
                          sequence strictly here to catch errors immediately.*)
                        (*Note that we have to use timeout here due to the use of lazy sequence.*)
                        |> Utils.try_with Seq.empty (timeout (Seq.try Seq.hd)): Proof.state Seq.seq;
    val results_w_log =
          Seq.map (fn x => ([node], x)) tac_results : (Dynamic_Utils.log * Proof.state) Seq.seq;
  in
    results_w_log : (Dynamic_Utils.log * Proof.state) Seq.seq
  end;

fun sh_output_to_sh_stttac (output:string) =
      Dynamic_Utils.logtac_to_stttac (tool_output_n_timeout_to_logtac output NONE 7.0)
      : Proof.state Dynamic_Utils.stttac;

(** Sledgehammer_Tacctic: Sledgehammer as a state monad based tactic. **)
structure Sledgehammer_Tactic : SUBTOOL =
struct

fun hammer_logtac (timeout:real) (pstate:Proof.state): (Dynamic_Utils.log * Proof.state) Seq.seq =
  let
    (*syntax sugars*)
    infix <$>
    fun x <$> f            = Option.map f x;
    val valOf              = Option.valOf;
    val omap               = Option.map;
    val thy                = Proof.theory_of pstate : theory;
    val params             = Sledgehammer_Commands.default_params thy
                             [("isar_proofs", "false"),("smt_proofs", "false")]
    val Auto_Try           = Sledgehammer_Prover.Auto_Try;
    val fact_override      = Sledgehammer_Fact.no_fact_override;
    val run_sledgehammer   = Sledgehammer.run_sledgehammer params Auto_Try NONE 1 fact_override
                           : Proof.state -> bool * (Sledgehammer.sledgehammer_outcome * string);
    val apply_timeout      = Isabelle_Utils.timeout_apply (seconds timeout);



    (*function body*)
    (*Why Future here? Because Isabelle_Utils.timeout_apply alone is not reliable.*)
    (*TODO: Probably it is better to improve Isabelle_Utils.timeout_apply using Future.*)
    (* Resource_Limit.with_slot is the single admission-control point for Sledgehammer in the
       whole system: every caller in PSL, TBC and AbductionProver reaches the provers through
       this function, so bounding concurrency here bounds it regardless of how many layers of
       parallelism sit above - AbductionProver alone calls in from a persistent worker pool over
       OR-nodes and, beneath that, a Par_List over conjecture sets, so the number of hammers in
       flight was previously a product of those levels rather than a bound.

       This matters because each invocation runs every prover in sledgehammer_provers
       concurrently as external processes that Isabelle bounds in time but not in memory, and a
       single diverging veriT has been measured at 6.35GB.

       The gate blocks on Future.join, never on Synchronized.guarded_access; see the note in
       Resource_Limit.ML for why waiting on the latter from a pool thread is what made an
       earlier version of the abduction worker pool several times slower. *)
    (* The limit comes from the caller's own context (declare [[max_parallel_hammers = N]]);
       0 means "derive from the machine", which is now memory as well as processors - see
       Resource_Limit.hammer_slots_for. Half the processors alone allowed six concurrent
       invocations on a 12-core 12GB host, against a machine a single diverging veriT can fill. *)
    val hammer_limit       = Resource_Limit.hammer_slots (Proof.context_of pstate);
    (* The hammer runs in a group of its own, and its outcome is read as a value.
     *
     * Cancellation follows the task-group hierarchy downwards, so a group belonging to this
     * hammer alone can be cancelled without touching the caller, and Future.join_result reports
     * a cancelled or failed task as Exn.Exn rather than raising on this thread. That removes the
     * reason the previous version existed: it caught the interrupt here and consumed it with
     * expose_interrupt, which is Exn.capture without release - the implementation manual names
     * exactly that as what makes a program depend on physical effects of the environment, and it
     * behaved like it. Par_List cancels its siblings routinely as soon as one of them settles a
     * question, and the resulting interrupt used to propagate out of the hammer, out of the PSL
     * strategy, out of TBC preprocessing and out of the enclosing command; measured, that made a
     * single "solve" fail about 37% of the time with a bare "*** Interrupt" naming nothing.
     *
     * A timeout is different in kind: Timeout.apply raises Timeout.TIMEOUT, a specific exception
     * Isabelle defines for the purpose, so handling it is not interception. An interrupt that
     * does reach this thread is genuine - the user cancelling, or our own group being cancelled
     * from outside - and propagates. *)
    (* On noticing the memory guard's stop request while a hammer is running.
     *
     * The guard asks the search to wind down, waits three seconds, and only then cancels its
     * group - and cancelling is what endangers the session, because it interrupts the shared
     * workers running the search's tasks. An attempt already inside a hammer does not reach the
     * between-attempts check (TBC_Utils.pnode_n_pst_to_proof_attempt) for as long as its own
     * timeout, up to ten minutes, so in rounds 1 and 2 the guard is always forced to insist.
     * Making the hammer notice the request would remove that.
     *
     * Slicing this join - joining in half-second Timeout.apply steps and checking the request
     * between them - does not do it, and the reason is worth keeping. A worker thread joining a
     * future may execute that future's task inline, so the slice's interrupt lands on the hammer
     * itself rather than on an idle wait: the prover is killed after half a second and reports
     * that it found nothing. Measured on TIP_prop_01, which reached the same place with the same
     * conjectures proved and unproved in 129s instead of 379s - the wait had not got cheaper, the
     * provers had done less - and pinned directly by Sliced_Join_Test, where a three-second future
     * joined in half-second slices returns nothing at all. It did not reduce the breakdowns
     * either: 2 in 4, against 1 in 4 without it.
     *
     * What would work is a watcher that cancels this group - ours, forked by fork_hammer - when
     * the request appears, leaving the joining thread uninterrupted so join_result reports the
     * cancellation as a value. That is not done here yet. *)
    fun join_hammer (group, f) =
      let
        val outcome =
          SOME (apply_timeout Future.join_result f) handle Timeout.TIMEOUT _ => NONE;
      in
        case outcome of
          SOME (Exn.Res r) => SOME r
        | SOME (Exn.Exn _) => NONE   (*cancelled or failed: a value, not an event*)
        | NONE =>
            (*timed out: stop it and read its outcome, so nothing is left running*)
            (Future.cancel_group group; ignore (Future.join_result f); NONE)
      end;
    fun fork_hammer () =
      let val group = Future.new_group (Future.worker_group ()) in
        (group,
         hd (Future.forks
               {name = "psl_hammer", group = SOME group, deps = [], pri = 0, interrupts = true}
               [fn () => run_sledgehammer pstate]))
      end;
    val result             = Resource_Limit.with_slot hammer_limit (fn () =>
                               join_hammer (fork_hammer ()))
                           : (bool * (Sledgehammer.sledgehammer_outcome * string)) option;
    (* Sledgehammer's own structured answer, not its message.
     *
     * SH_Some carries the prover result and a preplay per method tried, each of which is
     * (proof_method, (play_outcome, facts used)). That is exactly what a step needs, so it is
     * used directly.
     *
     * What this replaces was a scrape of the human-readable line. The message
     * "Try this: by (metis foo bar) (0.1 ms)" was split on spaces, the first two tokens
     * dropped as "Try this:", then two - or five, decided by testing whether the reversed
     * tokens began "out)" "timed" - dropped off the end as the timing, and the remainder
     * rejoined with single spaces. Every part of that is a guess about wording that Isabelle is
     * free to change, the token counts silently mismatch for any message shaped differently,
     * did_smt_timeout raised "Something went wrong in Subtool.ML" on a short one, and rejoining
     * on single spaces is why method texts came out as "( induct \"var_1\" arbitrary : var_2 )".
     * The text was then re-parsed to recover the facts and the method that Sledgehammer had
     * just been holding as data. *)
    fun step_of_preplay (meth, (_, used_facts)) =
      let
        (*Chained facts are already chained at the goal; naming them again would be wrong.*)
        val extras =
          filter_out (fn (_, (scope, _)) => scope = ATP_Problem_Generate.Chained) used_facts;
        val fact_names = map (Pretty.unformatted_string_of o fst) extras: string list;
        (*A direct method takes its facts as arguments ("metis foo"); an indirect one needs them
          chained ("using foo apply auto"). Isabelle's own printer draws the same distinction.*)
        val direct = Sledgehammer_Proof_Methods.is_proof_method_direct meth;
        val rendered =
          Sledgehammer_Proof_Methods.string_of_proof_method
            (if direct then fact_names else []) meth;
        (*Isabelle's printer parenthesises when the method text needs it, so wrapping again
          would give "apply ((simp add: foo))".*)
        val methN =
          if String.isPrefix "(" rendered andalso String.isSuffix ")" rendered
          then rendered else "(" ^ rendered ^ ")";
      in
        {using = if direct then [] else fact_names, methN = methN}: apply_step
      end;
    fun played (_, (Sledgehammer_Proof_Methods.Played _, _)) = true
      | played _ = false;
    val step =
      case result of
        SOME (true, (Sledgehammer.SH_Some (_, preplays), _)) =>
          (case filter played preplays of
             preplay :: _ => SOME (step_of_preplay preplay)
           | [] => NONE)
      | _ => NONE;
  in
    case step of
      SOME s => apply_step_to_logtac s NONE 10.0 pstate
    | NONE => Seq.empty : (Dynamic_Utils.log * Proof.state) Seq.seq
  end;

fun state_stttac timeout =
      Dynamic_Utils.logtac_to_stttac (hammer_logtac timeout) : Proof.state Dynamic_Utils.stttac;

end;

(** Smart_Induct: Smart_Induct as a state monad based tactic. **)
structure Smart_Induct_Tactic =
struct

fun pst_to_smart_induct_output_strs (pst:Proof.state) =
let
    val thm      = Isabelle_Utils.proof_state_to_thm pst: thm;
    val thm_term = Thm.prop_of thm: term;
    val outer_path_to_unode_table =
          Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst thm_term
          : Outer_Path_To_Unode.path_to_unode_table;
    val (ind_best_records, ind_max_point) =
          Apply_SeLFiE.score_n_induct_argss_n_proof_state_to_best_pairs 0.0 [] []
            Apply_SeLFiE.Induction_Heuristic 5 pst outer_path_to_unode_table;
    fun record_to_pair {score, modifiers,...} = (score, modifiers);
    val best_pairs =
          Par_List.map record_to_pair ind_best_records
          : (real * SeLFiE_Util.induct_arguments) list;
    val fst_subg_n_chaineds   = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst: terms;
    val arb_pairs =
          Smart_Construction.proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs
            pst fst_subg_n_chaineds best_pairs
          : (real * SeLFiE_Util.induct_arguments) list;
    val (arb_best_records, _) =
          Apply_SeLFiE.score_n_induct_argss_n_proof_state_to_best_pairs ind_max_point arb_pairs
            best_pairs Apply_SeLFiE.Generalization_Heuristic 10 pst outer_path_to_unode_table;
    fun mk_arb_message (record:{modifiers: SeLFiE_Util.induct_arguments, score: real}) =
          SeLFiE_Util.induct_arguments_to_string (#modifiers record);
    val best_arb_messages     = map mk_arb_message arb_best_records: strings;
    val app_best_arb_messages = map (fn parenthesis => "apply " ^ parenthesis) best_arb_messages
in
  app_best_arb_messages:strings
end;

fun mk_state_stttac (smart_induct_output_str:string, importance:real) =
  let
    val logtac = tool_output_n_timeout_to_logtac smart_induct_output_str (SOME importance) 30.0;
    val stttac = Dynamic_Utils.logtac_to_stttac logtac: Proof.state Dynamic_Utils.stttac;
  in
    stttac
  end;

fun state_stttacs (timeout:real) (pst:Proof.state) =
  let
    val induct_output_strs =
          Utils.try_with []
            (Isabelle_Utils.timeout_apply (seconds timeout) pst_to_smart_induct_output_strs) pst
          : strings;
    val numb_of_candidates = length induct_output_strs;
    val low_importances    = replicate numb_of_candidates 0.7: real list;
    (*TODO: magic number for Abduction Prover*)
    val importances        = 0.95 :: 0.9 :: 0.85 :: 0.8 :: 0.75 :: low_importances
                          |> take numb_of_candidates: real list;
    val induct_outputs     = induct_output_strs ~~ importances: (string * real) list;
    val stttacs            =
          Par_List.map mk_state_stttac induct_outputs: Proof.state Dynamic_Utils.stttac list;
    val top_5              = take 5 stttacs: Proof.state Dynamic_Utils.stttac list;;
  in
    top_5: Proof.state Dynamic_Utils.stttac list
  end;

end;

(** The exposed part of Subtools **)
fun quickcheck to = Quickcheck_Tactic.state_stttac to;

fun nitpick to = Nitpick_Tactic.state_stttac to;

fun hammer to = Sledgehammer_Tactic.state_stttac to;

val to_stttac  = Dynamic_Utils.log_n_nontac_to_stttac;

fun is_solved_nontac(state:Proof.state) =
  let
    val done    = Proof.local_done_proof;
    val goal    = state |> Proof.goal |> #goal : thm;
    val no_goal = Thm.nprems_of goal = 0 : bool;
    val result  = if no_goal then state |> done |> Seq.single
      handle ERROR _ => Seq.single state else Seq.empty;
  in
    result : Proof.state Seq.seq
  end;

fun is_solved _ = to_stttac ([Dynamic_Utils.Done], is_solved_nontac);

fun defer _ = to_stttac ([Dynamic_Utils.Defer], Seq.single o (Proof.defer 1));

val subgoal_nontac = Seq.single o #2 o Subgoal.subgoal (Binding.empty, []) NONE (false, []);

fun subgoal _ = to_stttac ([Dynamic_Utils.Subgoal], subgoal_nontac);

fun smart_induct to pst =
      Utils.try_with []
        (Isabelle_Utils.timeout_apply (seconds to) (Smart_Induct_Tactic.state_stttacs to)) pst
      |> Seq.of_list;

end;