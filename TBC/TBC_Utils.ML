(*  Title:      TBC/TBC_Utils.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Yutaka Nagashima, Institute of Computer Science, the Czech Academy of Sciences

Core utilities shared by Template-Based Conjecturing: the pnode type tracking a
conjecture's proof/refutation status, PSL-strategy execution glue, counterexample
checking, and the round-based (sequential and parallel) conjecture-proving loops.
*)
signature TBC_UTILS =
sig

(* caller_context / assemble_suggestion *)
(* Where a suggested script is going to be pasted, and how to shape it so that it is legal
   there. Lives here rather than in Proof_By_Abduction because both TBC preprocessing and
   AbductionProver's own printer emit suggestions and must agree; the shape logic was
   previously duplicated in the two of them, and both copies had the same defect. *)
type caller_context =
  {backward: bool, only_subgoal: bool, chained_facts: strings, parameters: strings,
   goal_text: string};
val assemble_suggestion: caller_context -> strings -> string -> string;

(* goal_shape / strategy_for_goal *)
(* Which kind of proof obligation are we looking at, and hence which strategy should attack
   it. See the implementation for why these particular tests. *)
datatype goal_shape =
  Class_Instance of string    (*OFCLASS(ty, c_class), as produced by "instance"*)
| Locale_Instance of string   (*a locale predicate applied to its arguments, as produced by
                                "interpretation" or "sublocale"*)
| Ordinary_Goal;
val goal_shape:        Proof.context -> term -> goal_shape;
val strategy_for_goal: string -> Proof.context -> term -> string;

type theorem_typ;
type pnode;
type pnodes;
type timeouts;

val theorem_typ_to_str:                       theorem_typ -> string;
val mk_lemma_name:                            Proof.context -> theorem_typ -> string -> string;
val proof_id_counter:                         int Unsynchronized.ref;
val tbc_trace:                                string -> unit;
(* Consume an interrupt this thread inflicted on itself by cancelling work it started. See the
   implementation for why a self-inflicted cancellation must not be allowed to surface. *)
val absorb_self_cancellation:                 unit -> unit;
val statement_to_conjecture:                  Proof.state -> (string, string) Element.stmt -> pnode;
val pnode_stmt:                               Proof.context -> pnode -> string;
val as_prop:                                  term -> term;
val is_permutative_statement:                 term -> bool;
val term_to_original_goal_pnode:               Proof.state -> term -> pnode;
val sort_pnodes:                              pnodes -> pnodes;
val print_conjecture_w_proof:                 Proof.context -> pnode -> string;
val print_conjecture_w_have:                  Proof.context -> pnode -> string;
val rename_vars_in_script:                    (string * string) list -> string -> string;
val extract_var_names:                        string -> string list;
(* Which variables an auxiliary "have" must fix, and the "for ..." clause that states them.
   One computation, because the printed clause and the applied fixes must agree. *)
val fixes_for_have: Proof.context -> term -> (binding * string option * mixfix) list;
val for_clause_of:  Proof.context -> term -> string;
(* One step of a printed proof script. See parse_tactic_steps for the grammar these can be in
   and why "done" has to be represented rather than discarded. *)
datatype proof_step =
  Apply_Step of {using: strings, method: string}
| Focus_Subgoal   (*"subgoal": focus the first subgoal in a nested block*)
| Defer_Subgoal   (*"defer": move the first subgoal to the end*)
| Close_Block;    (*"done"*)
val parse_tactic_steps:                       strings -> proof_step list;
val string_of_proof_step:                     proof_step -> string;
(* Making the search's simp bag explicit in what is emitted. The search proves its scripts in a
   context where every non-permutative TBC conjecture is a simp rule (assume_term_in_ctxt), so
   a found script's bare "auto" names none of the facts it used. These splice the fact names
   into the method text itself, so the emitted script carries its dependencies - see
   augment_method_with_facts. *)
val method_consumes_simp:                     string -> bool;
val augment_method_with_facts:                strings -> string -> string option;
val augment_step_with_facts:                  strings -> proof_step -> proof_step;
val augment_steps_with_facts:                 strings -> proof_step list -> proof_step list;
val augment_log_with_facts:                   strings -> Dynamic_Utils.log -> Dynamic_Utils.log;
val augment_pnode_proof_with_facts:           strings -> pnode -> pnode;
val proved_nodes_to_proof_text:               Proof.context -> pnodes -> string;
(* The periodic reporter's view of what TBC has proved so far, rendered as haves in completion
   order. Sound as a module-level store because one search runs per process
   (max_parallel_searches); the entry points clear it before preprocessing starts. *)
val clear_progress_pnodes:                    unit -> unit;
val progress_pnodes_text:                     Proof.context -> string;
val proved_nodes_to_proof_text_for_subgoal:
  Proof.context -> caller_context -> (string * string) list -> pnodes -> string;
val print_proved_nodes:                       Proof.context -> pnodes -> string;
val psl_strategy_to_monadic_tactic:
  timeouts -> Monadic_Prover.str -> Proof.state -> Proof.state Monadic_Prover.monad;
val pst_to_proofscript_opt:
  timeouts -> string -> Proof.state -> (string  * Proof.state) option;
(* The same run, keeping the steps PSL applied instead of flattening them to a script. *)
val pst_to_proof_log_opt:
  timeouts -> string -> Proof.state -> (Dynamic_Utils.log * Proof.state) option;
val log_to_proof_steps:                       Dynamic_Utils.log -> proof_step list;
(* The steps that finish a pnode, whether it was proved by a PSL run or came in as text. *)
val pnode_proof_steps:                        pnode -> proof_step list;
val proof_steps_to_text:                      proof_step list -> string;
val pst_to_proofscripts_opt:
  timeouts -> string -> Proof.state -> (strings * Proof.state) option;
val pst_n_conjecture_has_counterexample:      Proof.state -> string -> bool;
val term_has_counterexample_in_pst:           Proof.state-> term -> real;
val assume_term_in_ctxt:                      (string * term) -> Proof.context -> local_theory;
val assume_terms_in_ctxt:
  (string * term) list -> Proof.context -> Proof.context;
(* Drops one of each pair of mirrored equations. TBC's templates prove an equation in both
   directions; as simp rules the pair rewrites back and forth forever. *)
val drop_mirrored_pnodes: Proof.context -> pnodes -> pnodes;
val cheat_lemma_term_in_pst:                  string -> term -> Proof.state -> Proof.state option;
datatype strategy_for_eval = TBC_Strategy;
val pnode_n_pst_to_pst_n_proof:
  strategy_for_eval -> real -> pnode -> int -> Proof.state -> Proof.state * pnode;
val original_goal_is_proved:                  pnodes -> bool;
val conjectures_n_pst_to_pst_n_proof_w_limit:
  strategy_for_eval -> int -> int -> pnodes -> Proof.state -> Proof.state * pnodes;
val conjectures_n_pst_to_pst_n_proof_parallel_w_limit:
  strategy_for_eval -> int -> int -> pnodes -> Proof.state -> Proof.state * pnodes;
val type_check:                               Proof.context -> term -> term option;
val get_relevant_constants:                   Proof.context -> term -> (terms * terms * terms);



val Long_Hammer:    Proof.state -> real;
val Direct_Attempt_Timeout: Proof.state -> real;
val Short_Hammer:   Proof.state -> real;
val short_hammer_config: real Config.T;
val long_hammer_config:  real Config.T;
val Bottom_Up:      theorem_typ;
val Original_Goal:  theorem_typ;

end;

structure TBC_Utils: TBC_UTILS =
struct

(* Short_Hammer/Long_Hammer *)
(* Per-call time budget handed to Sledgehammer, as Isabelle config attributes so a theory can
 * say "declare [[long_hammer = 10.0]]" - discoverable via print_options, per-context, and
 * reachable from jEdit. The right value is genuinely benchmark-dependent: 10.0/30.0 suit
 * Isaplanner and Prod, whereas TIP15 wants the shorter 5.0/10.0. That was recorded in a comment
 * beside two hardcoded constants and could only be honoured by editing and rebuilding, so the
 * recorded TIP15 evaluation silently used the threefold-larger Isaplanner/Prod budget.
 *
 * The budget is not only about wasted time: Sledgehammer runs every prover in
 * sledgehammer_provers concurrently as external processes, and those are time-bounded but NOT
 * memory-bounded (see veriT_options in ~~/src/HOL/Tools/SMT/smt_systems.ML, which passes only
 * --max-time). A prover that starts diverging keeps allocating for as long as its budget
 * allows, so this doubles as the only ceiling on how far such a process can grow. *)
val short_hammer_config =
  Attrib.setup_config_real \<^binding>\<open>short_hammer\<close> (K 10.0): real Config.T;

val long_hammer_config =
  Attrib.setup_config_real \<^binding>\<open>long_hammer\<close> (K 30.0): real Config.T;

(* direct_attempt_timeout *)
(* The whole budget for the first, direct attempt at the goal - the one that asks "is this easy?"
 * before any conjecturing happens. Every other attempt gets 300s.
 *
 * It used to get 300s too, and that is why the direct attempt and conjecturing were raced
 * against each other: sequencing them at that size meant a hard goal could spend most of the
 * caller's prove_timeout answering "no" before conjecturing had started, which takes the time
 * out of the search rather than merely delaying the answer. Racing them, in turn, needs a way to
 * call the loser off, and every way of doing that is either unsafe (cancelling a group
 * interrupts shared worker threads - see TBC_Preprocessor) or costs more than it saves.
 *
 * A proportionate budget removes the dilemma. Deciding that a goal is not easy does not need
 * five minutes: it needs about as long as one Sledgehammer call plus the tactics around it. At
 * this size, running the two in sequence costs a bounded amount and nothing has to be
 * abandoned, cancelled or waited for. *)
val direct_attempt_timeout_config =
  Attrib.setup_config_real \<^binding>\<open>direct_attempt_timeout\<close> (K 60.0): real Config.T;

fun Short_Hammer (pst:Proof.state) = Config.get (Proof.context_of pst) short_hammer_config;
fun Long_Hammer  (pst:Proof.state) = Config.get (Proof.context_of pst) long_hammer_config;
fun Direct_Attempt_Timeout (pst:Proof.state) =
  Config.get (Proof.context_of pst) direct_attempt_timeout_config;

datatype theorem_typ = Original_Goal | Bottom_Up;

fun theorem_typ_to_str Original_Goal = "original_goal"
  | theorem_typ_to_str Bottom_Up  = ""

fun mk_lemma_name (ctxt:Proof.context) (lemma_typ:theorem_typ) (subtyp:string) =
  let
    fun lemma_name' _ =
      let
        val postfix = serial_string (): string;
        val tentative_name = theorem_typ_to_str lemma_typ ^ subtyp ^ "_" ^ postfix;
        val is_not_used = null (Proof_Context.get_thms ctxt tentative_name handle ERROR _ => [])
      in
        if is_not_used then tentative_name else lemma_name' ()
      end;
  in
    lemma_name' ()
  end;

type pnode = {
  is_final_goal: bool,
  lemma_name: string,
  (*The statement as a term. It used to be kept as already-printed text, which meant every
    consumer that needed to reason about it - compare two conjectures, decide whether one is
    the goal, feed it to a tactic - had to parse it back first, in whatever context it happened
    to hold, and silently gave up when that failed. The term is what conjecturing produces and
    what the search reasons about; text is a rendering of it, produced where a rendering is
    actually needed.*)
  lemma_term: term,
  (*The proof that finishes this node, as the steps PSL actually applied.
    Dynamic_Utils.log is what the strategy interpreter produces and is already exactly this
    shape - "apply this method with these facts chained in", "subgoal", "defer", "done". It used
    to be flattened into a proof script here and parsed back into steps by whoever needed to
    replay it, through a hand-written tokeniser that split on whitespace and treated any word
    equal to a keyword as the start of a new step. Nothing in that round trip added information;
    it only took some away, and the parser could not express everything the log can - a non-zero
    "back" had no representation at all.*)
  proof_log: Dynamic_Utils.log option,
  (*The same proof as text, for printing and for the parts of the search that still exchange
    scripts. Derived from proof_log wherever there is one, so the two cannot disagree; nodes
    that come from elsewhere than a PSL run have text and no log.*)
  proof: string option,
  (*To track dependency, based on the timing proved with or w/o assuming conjectures.*)
  proof_id: int option,
  refuted: bool,
  proved_wo_assmng_cnjctr: bool,
  proved_in_nth_round: int option
}

type pnodes = pnode list;

(* A pnode's statement is always kept as a proposition. Conjecturing builds HOL terms of type
   bool, and the old text round-trip coerced them on the way back in - Syntax.read_prop wraps a
   bool term in Trueprop. Dropping the round-trip without keeping the coercion left every
   conjecture stated as a non-proposition, and measured, a goal that had been solving went to
   zero proved auxiliaries. *)
fun as_prop (trm:term): term =
  if fastype_of trm = propT then trm else HOLogic.mk_Trueprop trm;

(* is_permutative_statement *)
(* Whether an equation would be a permutative rewrite rule: its two sides are the same up to a
 * permutation of its variables. Commutativity is the standard example.
 *
 * This is Isabelle's own test, from Raw_Simplifier.mk_eq_True's "perm" (var_perm of the two
 * sides, not alpha-equal, left side not a bare variable), with Free where the simplifier has
 * Var - a conjecture's variables are free at this point.
 *
 * It matters because a permutative rule must not be added to the simp set. Isabelle does not
 * add one either: add.commute is not a simp rule, AC lemmas live in ac_simps and are supplied
 * where wanted. Declaring TBC's conjectures indiscriminately produced a divergent rewrite
 * system - measured, seven conjectures for TIP_prop_15 (associativity, two identities,
 * swap_unary, commutativity, and commutativity under a constructor) made a plain "by auto" on
 * the goal raise Interrupt_Breakdown, with no prover involved at all. Withholding the two
 * permutative ones makes the same goal go through in a second. They stay available as ordinary
 * facts, which is all Sledgehammer needs - it treats an equation symmetrically anyway. *)
local
  fun vperm (Free _, Free _) = true
    | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
    | vperm (trm1 $ trm2, uu1 $ uu2) = vperm (trm1, uu1) andalso vperm (trm2, uu2)
    | vperm (trm, uu) = trm = uu;
  fun frees_of trm = Term.add_frees trm [] |> map fst |> sort_distinct string_ord;
  fun var_perm (trm, uu) = vperm (trm, uu) andalso frees_of trm = frees_of uu;
in
fun is_permutative_statement (trm:term): bool =
  case (case trm of Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ body => body | other => other) of
    Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs =>
      var_perm (lhs, rhs) andalso not (lhs aconv rhs) andalso not (is_Free lhs)
  | _ => false;
end;


val proof_id_counter = Unsynchronized.ref 0: int Unsynchronized.ref;

(* Diagnostic tracing, off unless PSL_SOLVE_TRACE names a file. Written with interrupts
 * disabled: the failures worth tracing here are exactly those where an interrupt is already
 * pending, and an ordinary write would itself be interrupted, losing the line that says what
 * happened. *)
fun tbc_trace (msg:string): unit =
  case getenv "PSL_SOLVE_TRACE" of
    "" => ()
  | path =>
      Thread_Attributes.uninterruptible_body (fn _ =>
        ignore (\<^try>\<open>File.append (Path.explode path) ("  [tbc] " ^ msg ^ "\n")\<close>));

(* goal_shape *)
(* Obligations produced by "instance" and by "interpretation"/"sublocale" have very specific
 * shapes, and very specific methods that open them up - intro_classes and unfold_locales.
 * Neither appears anywhere in our ordinary strategies, so such an obligation is simply not
 * attackable by them: measured, "solve" on an instance goal reports "could not find a proof".
 * Recognising the two shapes lets us reach for the right method.
 *
 * These tests are structural. PaMpeR, which pioneered this kind of goal classification for
 * Isabelle, detected an instance proof by pretty-printing the first subgoal and searching the
 * result for the substring "OFCLASS", and enumerated locales via Locale.pretty_locale_deps -
 * a pretty-printing function used as a data source, which PaMpeR's own comment records as
 * causing trouble on HOL-Analysis. Isabelle2025-2 offers exact equivalents, so we use those
 * instead: Logic.match_of_class recognises OFCLASS as a term, and Locale.defined asks the
 * theory directly. See Abduction/LOCALE_AND_TYPE_CLASS_NOTES.md.
 *
 * Note this is about an obligation *to establish* a class or locale, not about a goal stated
 * *inside* a class or locale body - the latter is an ordinary goal that happens to mention
 * fixed parameters, and the ordinary strategies handle it. *)
datatype goal_shape =
  Class_Instance of string
| Locale_Instance of string
| Ordinary_Goal;

(* A goal thm straight out of Goal.init carries Pure's protection marker on its conclusion, so
 * the OFCLASS application is not the outermost term and matching against it silently fails.
 * Strip that before looking at the shape. *)
fun strip_protection (Const ("Pure.prop", _) $ trm) = strip_protection trm
  | strip_protection (Const ("Pure.term", _) $ trm) = strip_protection trm
  | strip_protection trm = trm;

fun goal_shape (ctxt:Proof.context) (goal:term): goal_shape =
  let
    val thy  = Proof_Context.theory_of ctxt;
    val body = strip_protection (Logic.strip_assums_concl (strip_protection goal));
  in
    case try Logic.match_of_class body of
      SOME (_, class) => Class_Instance class
    | NONE =>
        let
          val concl = the_default body (try HOLogic.dest_Trueprop body);
        in
          case Term.head_of concl of
            Const (name, _) =>
              if Locale.defined thy name then Locale_Instance name else Ordinary_Goal
          | _ => Ordinary_Goal
        end
  end;

(* chain_in_established_facts *)
(* Adds named facts already in the context to the state's chained facts, on top of whatever is
 * chained there already. Used to carry a round's proved conjectures into the next round's
 * attempts without declaring them globally - see the call site for why chaining rather than
 * declaring. Names that cannot be resolved are skipped rather than raising: a conjecture whose
 * note failed is simply not available. *)
fun chain_in_established_facts (names: strings) (pst:Proof.state): Proof.state =
  let
    val ctxt = Proof.context_of pst;
    val thms = maps (fn name => these (try (Proof_Context.get_thms ctxt) name)) names;
    val already = these (try (#facts o Proof.goal) pst);
    val _ = tbc_trace ("chain: requested " ^ Int.toString (length names)
                       ^ ", resolved " ^ Int.toString (length thms));
  in
    if null thms then pst
    else the_default pst (try (Proof.using_facts (already @ thms)) pst)
  end;

(* absorb_self_cancellation *)
(* Consume an interrupt this thread has inflicted on itself by cancelling work it started.
 *
 * Cancelling a future interrupts its task group, and the interrupt can land on the cancelling
 * thread rather than staying with the work being stopped. Left pending it is delivered later,
 * so a search that has just succeeded reports "*** Interrupt" instead of its proof. A genuine
 * cancellation from outside - where the enclosing worker group really is cancelled - is
 * re-raised, so the user's own interrupt still takes effect immediately. *)
fun absorb_self_cancellation (): unit =
  let
    val cancelled_from_outside =
      (case Future.worker_group () of
         NONE => false
       | SOME group => Task_Queue.is_canceled group);
  in
    if cancelled_from_outside
    then Isabelle_Thread.expose_interrupt ()
    else ignore (Isabelle_Thread.expose_interrupt_result ())
  end;

(* inherit_chained_facts *)
(* Restating a goal builds a fresh Proof.state, and a fresh state has no chained facts. The
 * facts the user chained in with "using"/"from"/"with" live in Proof.goal's "facts" field, so
 * every restatement drops them - and the search restates constantly, once per proof attempt,
 * from the statement text alone. The user who has just handed the prover the decisive lemma is
 * then told no proof exists.
 *
 * Carrying them across each restatement keeps them where the methods can see them: a method
 * invoked on a state receives that state's chained facts, which is exactly how "using foo
 * apply simp" behaves in an ordinary proof, and therefore what the replayed script will do at
 * the live goal too. See Test_Isar/Scenario_Chained_Facts.thy, whose goals are provable only
 * this way. *)
fun inherit_chained_facts (from:Proof.state) (to:Proof.state): Proof.state =
  case these (try (#facts o Proof.goal) from) of
    []     => to
  | facts  => the_default to (try (Proof.using_facts facts) to);

(* The subgoal a strategy is about to attack: the first pending one, or - for a goal thm fresh
 * from Goal.init, which has none yet - the statement itself. *)
fun pending_goal_of (pst:Proof.state): term =
  let val goal_thm = #goal (Proof.goal pst) in
    case Thm.prems_of goal_thm of
      subgoal :: _ => subgoal
    | []           => Thm.prop_of goal_thm
  end;

(* strategy_for_goal *)
(* The strategy to attack this goal with, given the name to use for an ordinary one. Both
 * obligation strategies keep an ordinary attack as their last resort, so a misclassified goal
 * costs a little time rather than the proof. *)
fun strategy_for_goal (ordinary:string) (ctxt:Proof.context) (goal:term): string =
  let
    val shape = goal_shape ctxt goal;
    val _ = tbc_trace ("goal_shape of " ^ Isabelle_Utils.trm_to_string ctxt goal ^ " = "
              ^ (case shape of Class_Instance c => "Class_Instance " ^ c
                             | Locale_Instance l => "Locale_Instance " ^ l
                             | Ordinary_Goal => "Ordinary_Goal"));
  in
    case shape of
      Class_Instance _  => "Class_Obligation_Strategy"
    | Locale_Instance _ => "Locale_Obligation_Strategy"
    | Ordinary_Goal     => ordinary
  end;

fun statement_to_conjecture
      (pst:Proof.state) (Element.Shows [((binding, _), [(stmt:string, _(*assumptions_maybe*))])]) =
(tracing ("TBC.thy stmt is: " ^ stmt);
 tracing ("TBC.thy content is: " ^ Isabelle_Utils.YXML_content_of stmt);
      {
        is_final_goal = true,
        lemma_name = mk_lemma_name (Proof.context_of pst) Original_Goal "": string,
        lemma_term =
          stmt |> Isabelle_Utils.YXML_content_of |> String.explode |> Utils.init |> tl
               |> String.implode |> Syntax.read_prop (Proof.context_of pst),
        proof_log = NONE,
        proof = NONE,
        proof_id = NONE,
        refuted = false,(*we assume the final goal is a true statement.*)
        proved_wo_assmng_cnjctr = false,
        proved_in_nth_round = NONE
      }): pnode
  | statement_to_conjecture _ _ = error "statement_to_conjecture failed for the final goal.";

fun term_to_original_goal_pnode (pst:Proof.state) (goal_term:term) =
  let
    val ctxt = Proof.context_of pst;
  in
    {
      is_final_goal = true,
      lemma_name = mk_lemma_name ctxt Original_Goal "": string,
      lemma_term = as_prop goal_term,
      proof_log = NONE,
      proof = NONE,
      proof_id = NONE,
      refuted = false,(*we assume the final goal is a true statement.*)
      proved_wo_assmng_cnjctr = false,
      proved_in_nth_round = NONE
    }: pnode
  end;

(* The statement as text, for the places that genuinely need it: printing a suggestion, and the
   Isar commands that read their statement from a string. Rendering happens here rather than at
   construction, so there is one term and many renderings rather than the reverse. *)
fun pnode_stmt (ctxt:Proof.context) (pnode:pnode): string =
  Isabelle_Utils.trm_to_string ctxt (#lemma_term pnode);

fun sort_pnodes (pnodes:pnodes): pnodes =
    sort (fn pnode_pair => option_ord int_ord (apply2 #proof_id pnode_pair)) pnodes;

(* Progress store for the periodic reporter (Proof_By_Abduction.fork_progress_reporter): the
 * conjectures this search has proved so far, in completion order, published at each attempt's
 * OWN success - not at the round's end, where the parallel driver converts its results, which
 * would hold every mid-round success back until the round's slowest failure timed out
 * (measured: four conjectures proved in the first seconds of a round stayed invisible for
 * three sixty-second report ticks). proof_id is NONE here: the id is assigned at conversion,
 * and the store must not race the counter for it.
 *
 * A module-level store is sound because one search runs per process
 * (Resource_Limit.max_parallel_searches, default 1) - the search that clears it at entry is
 * the only writer until it finishes. Cleared by the entry points, not here. *)
val progress_pnodes_store = Synchronized.var "TBC_Utils.progress_pnodes" ([]: pnode list);
fun clear_progress_pnodes () = Synchronized.change progress_pnodes_store (K []);

fun publish_progress_proof (nth_round: int) (pnode: pnode) (log: Dynamic_Utils.log): unit =
  Synchronized.change progress_pnodes_store (fn ps =>
    {is_final_goal               = #is_final_goal pnode,
     lemma_name                  = #lemma_name pnode,
     lemma_term                  = #lemma_term pnode,
     proof_log                   = SOME log,
     proof                       = SOME (Dynamic_Utils.mk_apply_script log),
     proof_id                    = NONE,
     refuted                     = #refuted pnode,
     proved_wo_assmng_cnjctr     = true,
     proved_in_nth_round         = SOME nth_round} :: ps);

(* rename_vars_in_script *)
(* Substitutes whole-token occurrences of names in a printed tactic script, e.g. turning
 * "apply (induct var_0)" into "apply (induct x)" given the mapping [("var_0", "x")]. Tokens
 * not present in the mapping (tactic names, lemma names, punctuation, ...) are left alone.
 * Splitting on identifier-character boundaries (rather than e.g. a naive substring
 * replacement) avoids the classic bug of "var_1" matching inside "var_10".
 * Lives here rather than in Abduction/Top_Down_Util.ML because it is needed both by
 * TBC_Preprocessor (this session) and by Proof_By_Abduction (Abduction, which depends on
 * this session) - the reverse would not typecheck. *)
fun rename_vars_in_script (mapping: (string * string) list) (script:string): string =
  let
    fun is_ident_char c = Char.isAlphaNum c orelse c = #"_";
    fun rename tok = the_default tok (AList.lookup (op =) mapping tok);
    fun flush ("":string) (acc:string list) = acc
      | flush tok acc = rename tok :: acc;
    fun go ([]: char list) (tok:string) (acc:string list) = flush tok acc
      | go (c::cs) tok acc =
          if is_ident_char c
          then go cs (tok ^ String.str c) acc
          else go cs "" (String.str c :: flush tok acc);
  in
    go (String.explode script) "" [] |> rev |> String.concat
  end;

(* fixes_for_have / for_clause_of *)
(* The "for" clause of an auxiliary "have": the statement's own free variables, except any the
 * surrounding proof has already fixed.
 *
 * Re-fixing an already-fixed variable does not name the same variable - it introduces a fresh one
 * that shadows it. The auxiliary fact is then about a different variable from the one the goal
 * talks about, so it is useless to the very proof it was generated for, and a locale or class
 * parameter re-fixed this way is cut off from the assumptions that constrain it. Variables
 * genuinely local to the auxiliary statement still get fixed, which is what makes it a general
 * lemma rather than a statement about the goal's particular variables.
 *
 * This lives here, in the lowest structure both users can see, because the printed clause and the
 * applied fixes have to be the same list. They were not: the printers derived the clause by
 * scanning the *printed statement* for "var_N" tokens (extract_var_names below), while the
 * repliers derived the fixes from the *term*. Those agree only while every free variable is named
 * var_N - which stopped being true when the search began working in the caller's focused context,
 * where variables keep the caller's own names. A statement about "xs" was then fixed by "solve"
 * and left unfixed by "suggest", so the suggestion printed a "have" about the caller's particular
 * xs where the applied one was general. Same quantity, two computations, and they diverged: the
 * shape of defect docs/2026_08_01_isar_integration_design.md is about. *)
fun fixes_for_have (ctxt:Proof.context) (stmt:term)
    : (binding * string option * mixfix) list =
  Term.add_frees stmt []
  |> filter_out (Variable.is_fixed ctxt o fst)
  |> map (fn (n, _) => (Binding.name n, NONE: string option, NoSyn));

fun for_clause_of (ctxt:Proof.context) (stmt:term): string =
  case fixes_for_have ctxt stmt of
    [] => ""
  | fixes => " for " ^ space_implode " " (map (Binding.name_of o #1) fixes);

(* extract_var_names *)
(* Collects the distinct "var_N" tokens occurring in a printed statement, in order of first
 * occurrence. Superseded by for_clause_of above, which both printers now use; kept for any caller
 * that genuinely has a script string and no term. *)
fun extract_var_names (script:string): string list =
  let
    fun is_ident_char c = Char.isAlphaNum c orelse c = #"_";
    fun is_var_tok tok =
      String.isPrefix "var_" tok andalso size tok > 4
      andalso CharVector.all Char.isDigit (String.extract (tok, 4, NONE));
    fun flush (tok:string) (acc:string list) =
      if tok <> "" andalso is_var_tok tok then tok :: acc else acc;
    fun go ([]: char list) (tok:string) (acc:string list) = flush tok acc
      | go (c::cs) tok acc =
          if is_ident_char c
          then go cs (tok ^ String.str c) acc
          else go cs "" (flush tok acc);
  in
    go (String.explode script) "" [] |> rev |> distinct (op =)
  end;

(* parse_tactic_steps *)
(* Every printed proof script AbductionProver/TBC_Preprocessor ever produces is ultimately
 * built by SeLFiE.Util.mk_apply_script out of a "log" (Dynamic_Utils.log), a list of nodes of
 * exactly these shapes: Apply {methN, using, back, ...} (rendered "using u1 u2 ... apply
 * methN back back ..."), and the terminal markers Done/Subgoal/Defer (rendered bare, e.g.
 * "done"). That is the *entire* grammar these scripts can ever be in, regardless of which
 * subsystem (TBC_Preprocessor's own strategy search, or AbductionProver's own graph search)
 * produced a given one - so a small hand-written tokenizer for exactly this grammar is safe,
 * rather than needing to handle arbitrary Isar syntax.
 * mk_apply_script also wraps its result in Active.sendback_markup_properties - real YXML
 * markup embedded directly in the string, e.g. a raw pnode's own "proof" field literally
 * starts "\^Esendback...\^Fapply ( induct ...", not just "apply ( induct ...". Left unstripped,
 * this corrupts exactly the first token, silently losing the entire first step (confirmed by
 * a real failure: a script that should have been "apply (induct x) apply fastforce apply
 * fastforce done" was tokenized as if the "apply (induct x)" step never existed, since the
 * markup-glued token matched none of the keywords below). Proof_By_Abduction.emit_proof_script
 * already strips this via its own clean_markup before ever displaying text to a user; parsing
 * needs the exact same treatment before tokenizing, since it consumes the raw field directly
 * rather than the cleaned, printed text.
 * Splits the printed script into a sequence of steps, with any "using ..." immediately
 * preceding an "apply" attached to that step. Each element of the list is parsed on its own
 * rather than after concatenating them all, because the element boundaries are information the
 * producer already has: Dynamic_Utils.log_to_script_n_importance renders one log node per
 * element. Concatenating first threw that away and then tried to recover it by looking for
 * keywords, so a step could be merged with its neighbour. Elements that do contain several
 * commands still parse, since the grammar below is applied within an element too.
 *
 * "subgoal" and "defer" are genuinely emitted, contrary to what this comment used to claim -
 * TBC_Strategy's fifth branch contains Subgoal, and a real run of "solve" on
 * "add x y = add y x" produced a root script containing one, which then failed to replay with
 * "unsupported proof step \"subgoal\"". Treating them as unsupported did not make them not
 * happen; it turned a found proof into a failure.
 *
 * Supporting them means "done" can no longer be discarded. "subgoal" opens a nested block that
 * its own "done" closes, so the two must be tracked against each other; only the script's
 * final "done", the one at depth zero, is the caller's business (the caller closes the goal
 * itself once every step has been applied - see Proof_By_Abduction.apply_tactic_steps).
 *
 * "back" is part of the same grammar (mk_apply_script renders Apply's "back" count as that
 * many bare "back" commands) but every Apply node in this codebase is constructed with
 * back = 0, so it is never emitted. It is still recognised as a keyword rather than left to be
 * swallowed into the preceding method's text, where "apply auto back" would silently become
 * the method text "auto back" and fail to parse as a method - a clear error beats that. *)
datatype proof_step =
  Apply_Step of {using: strings, method: string}
| Focus_Subgoal
| Defer_Subgoal
| Close_Block;

fun parse_tactic_steps_of_one (proof_string: string): proof_step list =
  let
    fun strip_markup s = XML.content_of (YXML.parse_body s) handle ERROR _ => s;
    val keywords = ["using", "apply", "done", "subgoal", "defer", "back"];
    val words = proof_string |> strip_markup |> String.tokens Char.isSpace;
    fun flush (kw:string) (args:string list) (acc:(string*string) list) =
      if kw = "" then acc else (kw, String.concatWith " " (rev args)) :: acc;
    fun group ([]: string list) (kw:string) (args:string list) (acc:(string*string) list) =
          rev (flush kw args acc)
      | group (w::ws) kw args acc =
          if member (op =) keywords w
          then group ws w [] (flush kw args acc)
          else group ws kw (w :: args) acc;
    val pairs = group words "" [] [];
    fun steps ([]: (string * string) list) = []
      | steps (("using", names) :: ("apply", meth) :: rest) =
          Apply_Step {using = String.tokens Char.isSpace names, method = meth} :: steps rest
      | steps (("apply", meth) :: rest) =
          Apply_Step {using = [], method = meth} :: steps rest
      | steps (("subgoal", _) :: rest) = Focus_Subgoal :: steps rest
      | steps (("defer", _)   :: rest) = Defer_Subgoal :: steps rest
      | steps (("done", _)    :: rest) = Close_Block :: steps rest
      | steps ((kw, _) :: _) =
          error ("parse_tactic_steps: unsupported proof step \"" ^ kw ^ "\"");
  in
    steps pairs
  end;

fun parse_tactic_steps (proof_strings: strings): proof_step list =
  maps parse_tactic_steps_of_one proof_strings;

(* log_to_proof_steps *)
(* PSL's own record of what it applied, in the form the replay wants. No parsing: the two
 * datatypes describe the same thing, which is the whole point - Dynamic_Utils.node and
 * proof_step were always the same four cases, with a proof script in between them purely
 * because that is what the search used to hand back.
 *
 * "back" is the one case with no counterpart. It re-picks an earlier result of the previous
 * method, and the replay has no way to express that, so it is refused rather than dropped -
 * silently discarding it would replay a different proof from the one that was found. The text
 * parser refused it too, but by failing to recognise a keyword, which said nothing useful. *)
fun log_to_proof_steps (log: Dynamic_Utils.log): proof_step list =
  let
    fun step Dynamic_Utils.Done    = Close_Block
      | step Dynamic_Utils.Subgoal = Focus_Subgoal
      | step Dynamic_Utils.Defer   = Defer_Subgoal
      | step (Dynamic_Utils.Apply {using, methN, back, ...}) =
          if back > 0
          then
            error ("log_to_proof_steps: the proof found uses \"back\" (" ^ Int.toString back
                   ^ " times, after \"apply " ^ methN ^ "\"), which cannot be replayed as a"
                   ^ " structured step.")
          else Apply_Step {using = using, method = methN};
  in
    map step log
  end;

(* pnode_proof_steps *)
(* Prefers the log, because that is what the search actually did. Falls back to parsing the text
 * for nodes that have no log - the abduction graph builds its own scripts and hands them over
 * as strings - so the parser is still needed, but only where a script genuinely arrives as a
 * script. *)
fun pnode_proof_steps (pnode:pnode): proof_step list =
  case #proof_log pnode of
    SOME log => log_to_proof_steps log
  | NONE =>
      (case #proof pnode of
         SOME text => parse_tactic_steps [text]
       | NONE =>
           error ("pnode_proof_steps: " ^ #lemma_name pnode ^ " is not proved yet"));

(* string_of_proof_step *)
(* For tracing a replay. An interrupt arriving mid-replay carries no position, so the only way to
 * see how far the script got is for each step to say what it was. *)
fun string_of_proof_step (Apply_Step {using, method}) =
      (if null using then "" else "using " ^ String.concatWith " " using ^ " ") ^ "apply " ^ method
  | string_of_proof_step Focus_Subgoal = "subgoal"
  | string_of_proof_step Defer_Subgoal = "defer"
  | string_of_proof_step Close_Block   = "done";

(* proof_steps_to_text *)
(* The steps as Isar source, one per line. This is how a suggestion is rendered, so that what is
 * printed is a rendering of the steps that were applied rather than a separately assembled
 * script - a suggestion that does not reconstruct is then a bug in one function instead of a
 * disagreement between two.
 *
 * It also means no markup to strip. Dynamic_Utils.mk_apply_script wraps its output in
 * Active.sendback_markup_properties for the one-click paste in jEdit's Output pane, and every
 * consumer that wanted the text rather than the click had to undo that first - the file writer
 * still carries a clean_markup for the paths that have not moved over yet. *)
fun proof_steps_to_text (steps: proof_step list): string =
  cat_lines (map string_of_proof_step steps);

(* augment_method_with_facts *)
(* "auto" with [f1, f2] becomes "(auto simp add: f1 f2)": the emitted counterpart of what
 * assume_term_in_ctxt does inside the search. The search proves its scripts in a context where
 * every non-permutative TBC conjecture is a simp rule, so a found script that says bare "auto"
 * names none of the facts it depends on; the reader of the emitted script cannot see the
 * dependencies without rebuilding that bag, which is exactly what declaring the emitted
 * auxiliaries [simp] used to do. The abduction graph exists to keep dependencies explicit
 * rather than ambient, so the bag is translated away at the emission boundary instead: the
 * facts a simp-consuming method could use are spliced into the method text, and the emitted
 * "have"s carry no attribute at all (see print_conjecture_w_have).
 *
 * Returns NONE for a method that does not consult the simp set (induct, metis, rule, ...):
 * splicing facts into those would be wrong, and a script whose steps are all such methods
 * depends on no bag at all. Facts already present in the method text are not spliced twice.
 *
 * A trailing goal-restriction suffix stays outside the parentheses, where Method.parse's
 * grammar requires it ("(auto simp add: f1) [ 1 ]") - see Proof_By_Abduction.parse_method for
 * what happens when it is wrapped inside. A "]"-terminated method whose bracket content is not
 * numeric is not split: that shape is an attribute suffix on a fact ("foo[symmetric]"), not a
 * goal restriction. *)
local

fun trim (s: string): string =
  let
    val n = size s;
    fun from i = if i < n andalso Char.isSpace (String.sub (s, i)) then from (i + 1) else i;
    fun till j = if j > 0 andalso Char.isSpace (String.sub (s, j - 1)) then till (j - 1) else j;
    val i = from 0;
    val j = till n;
  in if j <= i then "" else String.substring (s, i, j - i) end;

fun last_index_of (c: char) (s: string): int option =
  let
    fun go i best =
      if i >= size s then best
      else go (i + 1) (if String.sub (s, i) = c then SOME i else best);
  in go 0 NONE end;

(* "auto [ 1 ]" -> ("auto", "[ 1 ]"); "simp add: foo[symmetric]" is left whole. *)
fun split_restriction (s: string): string * string =
  if String.isSuffix "]" s
  then
    (case last_index_of #"[" s of
       NONE => (s, "")
     | SOME i =>
         let
           val inside = String.substring (s, i + 1, size s - i - 2);
           val chars  = String.explode inside;
           val numeric =
             List.all (fn c => Char.isDigit c orelse Char.isSpace c orelse c = #"-"
                               orelse c = #",") chars
             andalso List.exists Char.isDigit chars;
         in
           if numeric then (trim (String.substring (s, 0, i)), String.extract (s, i, NONE))
           else (s, "")
         end)
  else (s, "");

(* Strips one outer pair of parentheses when it encloses the whole method - "(induct x)" but
   not "(rule a, rule b), simp" - so the rebuilt text nests exactly one pair. *)
fun strip_outer_parens (s: string): string =
  if size s >= 2 andalso String.sub (s, 0) = #"(" andalso String.sub (s, size s - 1) = #")"
  then
    let
      fun encloses_whole i depth =
        if i >= size s then false
        else
          let
            val c = String.sub (s, i);
            val depth' = if c = #"(" then depth + 1 else if c = #")" then depth - 1 else depth;
          in if depth' = 0 then i = size s - 1 else encloses_whole (i + 1) depth' end;
    in
      if encloses_whole 0 0 then trim (String.substring (s, 1, size s - 2)) else s
    end
  else s;

fun method_head (s: string): string =
  let
    fun ident c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'";
    fun go i = if i < size s andalso ident (String.sub (s, i)) then go (i + 1) else i;
  in String.substring (s, 0, go 0) end;

(* The methods that consult the simp set, with the modifier keyword each uses to add rules.
   Everything else is left untouched. *)
val simp_consumer_modifiers =
  [("simp", "add:"), ("simp_all", "add:"), ("auto", "simp add:"), ("force", "simp add:"),
   ("fastforce", "simp add:"), ("clarsimp", "simp add:")];

fun analyse (methN: string): (string * string * string) option =
  let
    val (core0, restriction) = split_restriction (trim methN);
    val core = strip_outer_parens core0;
  in
    AList.lookup (op =) simp_consumer_modifiers (method_head core)
    |> Option.map (fn modifier => (core, restriction, modifier))
  end;

in

fun method_consumes_simp (methN: string): bool = is_some (analyse methN);

fun augment_method_with_facts ([]: strings) (_: string): string option = NONE
  | augment_method_with_facts facts methN =
      case analyse methN of
        NONE => NONE
      | SOME (core, restriction, modifier) =>
          (case filter_out (fn f => String.isSubstring f core) facts of
             [] => NONE
           | fresh =>
               SOME ("(" ^ core ^ " " ^ modifier ^ " " ^ space_implode " " fresh ^ ")"
                     ^ (if restriction = "" then "" else " " ^ restriction)));

end;

fun augment_step_with_facts (facts: strings) (Apply_Step {using, method}) =
      (case augment_method_with_facts facts method of
         SOME method' => Apply_Step {using = using, method = method'}
       | NONE => Apply_Step {using = using, method = method})
  | augment_step_with_facts _ step = step;

fun augment_steps_with_facts (facts: strings) (steps: proof_step list): proof_step list =
  map (augment_step_with_facts facts) steps;

fun augment_log_with_facts (facts: strings) (log: Dynamic_Utils.log): Dynamic_Utils.log =
  map (fn Dynamic_Utils.Apply {using, methN, back, importance} =>
          (case augment_method_with_facts facts methN of
             SOME methN' =>
               Dynamic_Utils.Apply
                 {using = using, methN = methN', back = back, importance = importance}
           | NONE =>
               Dynamic_Utils.Apply
                 {using = using, methN = methN, back = back, importance = importance})
        | node => node) log;

(* The proof text is re-derived from the rewritten log, the same way proof_attempt_to_pnode
   derives it, so the printed script and the replayed steps stay one thing. A node that carries
   text and no log came from the graph side and is augmented there instead - see
   Abduction_Graph.print_have_and_proof_of_key. *)
fun augment_pnode_proof_with_facts (facts: strings) (pnode: pnode): pnode =
  case #proof_log pnode of
    NONE => pnode
  | SOME log =>
      let
        val log' = augment_log_with_facts facts log;
      in
        {is_final_goal           = #is_final_goal pnode,
         lemma_name              = #lemma_name pnode,
         lemma_term              = #lemma_term pnode,
         proof_log               = SOME log',
         proof                   = SOME (Dynamic_Utils.mk_apply_script log'),
         proof_id                = #proof_id pnode,
         refuted                 = #refuted pnode,
         proved_wo_assmng_cnjctr = #proved_wo_assmng_cnjctr pnode,
         proved_in_nth_round     = #proved_in_nth_round pnode}
      end;

fun print_conjecture_w_proof (ctxt:Proof.context) (pnode as {lemma_name, ...}:pnode) =
  "lemma " ^ lemma_name ^ ": " ^ enclose "\"" "\"" (pnode_stmt ctxt pnode)
  ^ "\n" ^ proof_steps_to_text (pnode_proof_steps pnode): string;

(* print_proof_of_pnode_only *)
(* Like print_conjecture_w_proof, but without the "lemma name: stmt" header - just the bare
 * tactic script. Used for the final goal when the suggested script is meant to be pasted as
 * the continuation of an already-open proof (suggest/solve) rather than
 * as a fresh top-level lemma: the goal is already stated at that point, so restating it would
 * be wrong. *)
fun print_proof_of_pnode_only (pnode:pnode) =
  proof_steps_to_text (pnode_proof_steps pnode): string;

(* print_conjecture_w_have *)
(* Like print_conjecture_w_proof, but with a "have" header instead of "lemma": for suggesting
 * an auxiliary fact that nests inside an already-open structured proof (a "proof - ... qed"
 * block wrapped around an in-progress goal) instead of as a fresh top-level lemma, which is
 * illegal syntax while a proof is open (suggest/solve).
 * Every free variable mentioned in the statement is listed in an explicit "for" clause. This
 * is not cosmetic: a bare "have foo: "P var_1"", with "var_1" left as an ordinary implicit
 * free variable, does NOT behave like a top-level "lemma foo: "P var_1""  once nested inside
 * an already-open proof. A top-level lemma statement is always closed over its free variables
 * into a genuinely general (schematic) fact; a nested "have" is not - its free variables stay
 * fixed to that one specific (if arbitrary) value, so a later "using foo"/"simp add: foo" can
 * fail to apply even though the goal is alpha-equivalent, because the fixed variable in foo's
 * statement cannot unify with a differently-named (or even identically-named!) variable
 * elsewhere. This was confirmed by an end-to-end test: a script that succeeds with every fact
 * as its own top-level lemma started failing, with exactly this "simp otherwise-provable step
 * doesn't close the goal" symptom, once nested into one shared "proof -" block - and adding
 * "for var_1" to the "have" statement (Isar's documented idiom for a genuinely general nested
 * fact) was what fixed it, not e.g. giving every "have" uniquely-named variables (tried first;
 * made no difference, since the problem was never about name collisions between "have"s). *)
(* No [simp] on the emitted "have". It used to print one for every non-permutative statement,
 * which made the pasted block's simp set an ever-growing bag every later step drew on
 * implicitly - the reader could not tell which auxiliary any step actually used, which is the
 * dependency information the abduction graph exists to keep explicit. The scripts now name the
 * facts they use in their own method text instead (augment_method_with_facts; wired up in
 * Proof_By_Abduction.explicitize_tbc_pnodes), so the fact itself is established plain, exactly
 * as the graph path always did. *)
fun print_conjecture_w_have (ctxt:Proof.context) (pnode as {lemma_name, ...}:pnode) =
  let
    val lemma_stmt = pnode_stmt ctxt pnode;
    (* From the term, so this clause is the same list apply_have_of_pnode fixes. *)
    val for_clause = for_clause_of ctxt (#lemma_term pnode);
  in
    "have " ^ lemma_name
    ^ ": " ^ enclose "\"" "\"" lemma_stmt ^ for_clause ^ "\n"
    ^ proof_steps_to_text (pnode_proof_steps pnode)
  end: string;

fun proved_nodes_to_proof_text (ctxt:Proof.context) (pnodes:pnodes) =
  filter #proved_wo_assmng_cnjctr pnodes
  |> sort_pnodes
  |> (fn prf_nds => "\n" :: map (print_conjecture_w_proof ctxt) prf_nds)
  |> String.concatWith "\n";

(* The periodic reporter's rendering of the store: completion order as published, NOT
   sort_pnodes - the store's records carry no proof_id (see publish_progress_proof).
   Each lemma's simp-consuming steps name every earlier lemma in the fragment, so the
   fragment verifies standalone when spliced after the theory's definitions: the search
   proved these in an ambient context where all earlier conjectures were simp rules
   (assume_term_in_ctxt), and a fragment that does not say so only checks by luck. This is
   the cheap, unminimized half of the final emission's explicit-facts discipline
   (explicitize_tbc_pnodes): a superset of the needed facts, no replay - replay-minimizing
   on a reporter tick would compete with the very search it reports on. *)
fun progress_pnodes_text (ctxt: Proof.context): string =
  let
    val pnodes = Synchronized.value progress_pnodes_store |> rev: pnode list;
    fun step (pnode: pnode) (facts_so_far: strings, acc: strings) =
      let
        val augmented = augment_pnode_proof_with_facts facts_so_far pnode;
      in
        (facts_so_far @ [#lemma_name pnode],
         print_conjecture_w_proof ctxt augmented :: acc)
      end;
  in
    case pnodes of
      [] => ""
    | _ => fold step pnodes ([], []) |> snd |> rev |> String.concatWith "\n"
  end;

(* Auxiliary facts get a "have" header rather than "lemma": this text is meant to be spliced
 * into an already-open proof (suggest/solve), either directly (see the
 * second case below) or as part of a larger "proof - ... qed" block that Proof_By_Abduction.
 * print_necessary_proofs_for_subgoal assembles once AbductionProver's own search has also run
 * - a top-level "lemma" command would be illegal syntax in either case, since a proof is
 * already open at the point this text is meant to be pasted in.
 * rename_mapping translates the final goal's own bare script back from AbductionProver's
 * internal var_N names to whatever names its free variables actually have at the point the
 * suggested script is meant to be pasted into. It is applied only to the final goal's own
 * script, never to an auxiliary lemma's: each auxiliary lemma is a fresh, self-contained,
 * universally-quantified fact - its own var_N names are genuinely correct there, not a
 * stand-in for anything in the caller's context.
 * Two genuinely different shapes come out of this depending on whether TBC preprocessing
 * alone already closed the goal (i.e. whether the final-goal pnode is itself among the proved
 * pnodes):
 * - If not (the common case: TBC preprocessing only established some auxiliary facts, and
 *   AbductionProver's own graph search runs next to actually close the goal), the result is
 *   just the auxiliary "have" blocks, unwrapped - a prelude fragment for
 *   print_necessary_proofs_for_subgoal to fold into its own single "proof - ... qed" together
 *   with whatever further auxiliary facts AbductionProver's own search additionally needed.
 * - If so (TBC preprocessing fully solved the goal by itself, so AbductionProver's search
 *   never runs and this text is used directly as the complete suggestion), the result is
 *   already a complete, self-contained answer: the final goal's own bare script, wrapped
 *   together with any auxiliary "have" blocks in "proof - ... qed" if there were any, or left
 *   bare if there were none. *)
type caller_context =
  {backward: bool, only_subgoal: bool, chained_facts: strings, parameters: strings,
   goal_text: string};

(* assemble_suggestion *)
(* Four shapes, one per position a suggestion can land in. Getting this wrong does not produce
 * a worse suggestion, it produces one that cannot be pasted at all.
 *
 *   backward, no auxiliaries    a bare apply-script - already directly insertable in an apply
 *                               chain, and what was always emitted there.
 *   backward, auxiliaries       "have" is illegal in an apply chain, so a structured block has
 *                               to be opened. "proof -" IS legal after "apply" (verified);
 *                               what is not legal is closing it with "show ?thesis".
 *   structured, no auxiliaries  a "show" of the goal, then the script. Emitting a bare
 *                               apply-script here is what broke suggestion inside a "case":
 *                               pasted after "case (S x)" it consumes the goal and closes the
 *                               block, and the enclosing "qed" then fails with "Bad context".
 *   structured, auxiliaries     "have" is already legal, so the auxiliaries go in directly -
 *                               opening another "proof -" would nest a block the caller never
 *                               closes.
 *
 * The goal is always named explicitly rather than as "?thesis". "?thesis" denotes the original
 * statement of the enclosing lemma/have/show, so after any apply step has transformed the goal
 * it names the wrong proposition - "apply (rule sym)" then "proof - ... show ?thesis" fails
 * with "Failed to refine any pending goal". "?case" is not always bound either. *)
fun assemble_suggestion
    ({backward, only_subgoal, chained_facts, parameters, goal_text}: caller_context)
    (haves: strings) (final_script: string): string =
  let
    (* The caller's goal may still have its parameters meta-quantified, and the script was found
       against the focused goal, where they are fixed - so it can name them. "subgoal for a b" is
       how that is written in Isar, and is the same operation the search performed with
       Subgoal.focus. Without it the script refers to names that do not exist where it is pasted:
       measured on HOL-Library.Multiset, "apply (induct a)" against
       "show \<And>a b. (b \<subseteq># a) = (a = a \<union># b)" fails every time with
       "Unable to figure out induct rule". Proof_By_Abduction.with_focus_if_parameterised does
       the same thing for solve, so the two agree. *)
    val focus_line =
      "subgoal" ^ (if null parameters then "" else " for " ^ String.concatWith " " parameters);
    val needs_focus = not (null parameters);
    (* "proof -" consumes the facts the caller chained in with "using": the initial method
       inserts them into the goal, and the "show" that follows restates the goal without them,
       so what the caller supplied is gone by the time the script that needs it runs. Measured:
       "using g_spec" then "proof - ... show \"g x = x + x\" by simp qed" fails outright, while
       the same with "show ... using g_spec by simp" succeeds. Naming them again on the show is
       what puts them back. *)
    val show_goal =
      "show \"" ^ goal_text ^ "\""
      ^ (if null chained_facts then "" else " using " ^ String.concatWith " " chained_facts);
    val structured = haves @ [show_goal, final_script, "qed"];
    val parts =
      if backward
      then
        if null haves
        then (if needs_focus then [focus_line, final_script] else [final_script])
        else if only_subgoal andalso not needs_focus
        then "proof -" :: structured
        (*Other subgoals are pending, or this one still has its parameters bound. A bare
          "proof -" block would have to discharge every pending subgoal before its "qed" - it
          cannot, since we were only asked about this one - and it would leave the parameters
          bound. "subgoal [for ...]" focuses this subgoal alone, fixing its parameters, and
          leaves the rest to the caller, which is what the user would have written by hand.
          Verified by compiling both shapes.*)
        else focus_line :: "proof -" :: structured
      else
        if null haves then [show_goal, final_script]
        else haves @ [show_goal, final_script];
  in
    "\n" :: parts |> String.concatWith "\n"
  end;

fun proved_nodes_to_proof_text_for_subgoal (ctxt:Proof.context) (caller: caller_context)
    (rename_mapping: (string * string) list) (pnodes:pnodes) =
  let
    val proved = filter #proved_wo_assmng_cnjctr pnodes |> sort_pnodes;
    val (final_nodes, aux_nodes) = List.partition #is_final_goal proved;
    val have_blocks = map (print_conjecture_w_have ctxt) aux_nodes;
  in
    case final_nodes of
      (* No final-goal pnode: TBC proved only auxiliaries, and AbductionProver's own printer
         will fold these "have"s into whatever shape it emits, so they are handed over bare. *)
      [] => if null have_blocks then "" else "\n" :: have_blocks |> String.concatWith "\n"
    | [final_pnode] =>
        let
          val final_script =
            print_proof_of_pnode_only final_pnode |> rename_vars_in_script rename_mapping;
        in
          assemble_suggestion caller have_blocks final_script
        end
    | _ => error "proved_nodes_to_proof_text_for_subgoal: more than one final-goal pnode"
  end;

fun print_proved_nodes (ctxt:Proof.context) (pnodes:pnodes) =
  let
    val proved_pnodes = filter #proved_wo_assmng_cnjctr pnodes |> sort_pnodes;
    val _ = tracing (Int.toString (length proved_pnodes) ^ " proofs found:");
  in
    proved_nodes_to_proof_text ctxt proved_pnodes
    |> Active.sendback_markup_properties [Markup.padding_command]
  end;

structure MP = Monadic_Prover;

type timeouts = {overall: real, hammer: real, quickcheck: real, nitpick: real};

fun psl_strategy_to_monadic_tactic (timeouts:timeouts) (strategy:MP.str) =
  fn (proof_state:Proof.state) =>
  let
    val core_tac  = MP.desugar strategy;
    val interpret = MP.interpret;
  in
    interpret
      (MP.eval_prim, MP.eval_para, MP.eval_pgt, MP.eval_strategic,
       MP.m_equal, MP.iddfc, (1,20), timeouts)
      core_tac proof_state
    handle Timeout.TIMEOUT timeout =>
      (tracing ("TBC_Strategy timed out after: " ^ Time.toString timeout ^ "."); K Seq.empty)
  end: Proof.state MP.monad;


(* Run the strategy and keep what it did. Dynamic_Utils.log is the interpreter's own record of
   the steps it applied, which is the form everything downstream actually wants; the script is a
   rendering of it and is produced where a rendering is needed. *)
(* Running a PSL strategy is three steps, and the whole of it has to be inside #overall.
 *
 * PSL's monad is a function from the log accumulator - see pbind in Monadic_Prover, which is
 * "fn state0 : log => ...". So interpret returns a closure, and the search runs when that closure
 * is applied to []. The interpreter does wrap Timeout.apply_physical around #overall, but what it
 * wraps is only the construction of the closure, which is why the budget bounded nothing: the
 * application, where the work is, happens at the call site outside it.
 *
 * Measured with phase markers around each step: of 18 attempts, every one that reached the
 * application had already done its work there - "built" and "forced" move together and Seq.hd is
 * free - while attempts that overran sat in the application for 390s and more against a nominal
 * 300s budget. Bounding the force alone therefore changes nothing; the region has to start before
 * the strategy is applied.
 *
 * Takes a thunk so that construction, application and forcing are all inside the timeout. Route
 * every PSL run through here so a new call site cannot quietly reintroduce the gap. *)
fun run_under_overall (timeouts:timeouts) (on_timeout:'b) (run:unit -> 'b): 'b =
  Timeout.apply_physical (seconds (#overall timeouts)) run ()
  handle Timeout.TIMEOUT _ => on_timeout;

(* The per-attempt budget for a conjecture, overridable so it can be tuned against memory.
 * Enforcing it changed what the budget costs: attempts that used to be stopped early by their
 * hammer now run for the whole of it, and several diverging ones run concurrently in the same
 * parallel round. Measured on a 12GB host at threads=6, five attempts sat at 300s together and
 * MemAvailable fell to 985MB, tripping the memory guard - a bounded search that dies of memory is
 * not an improvement on an unbounded one that finishes. The default is unchanged. *)
fun attempt_timeout (): real =
  case Real.fromString (getenv "PSL_EVAL_ATTEMPT_TIMEOUT") of
    SOME secs => secs
  | NONE => 300.0;

fun pst_to_proof_log_opt (timeouts:timeouts) (strategy_name:string) (pst:Proof.state)
    : (Dynamic_Utils.log * Proof.state) option =
  let
    val psl_strategy = PSL_Interface.lookup (Proof.context_of pst) strategy_name |> the
                        : PSL_Interface.strategy;
  in
    run_under_overall timeouts NONE (fn () =>
      (psl_strategy_to_monadic_tactic timeouts psl_strategy pst []
        : (Dynamic_Utils.log * Proof.state) Seq.seq)
      |> try Seq.hd)
  end;

fun pst_to_proofscript_opt (timeouts:timeouts) (strategy_name:string) (pst:Proof.state)
    : (string * Proof.state) option =
  pst_to_proof_log_opt timeouts strategy_name pst
  |> Option.map (apfst Dynamic_Utils.mk_apply_script);

fun pst_to_proofscripts_opt (timeouts:timeouts) (strategy_name:string) (pst:Proof.state)
    : (strings * Proof.state) option =
  let
    val psl_strategy = PSL_Interface.lookup (Proof.context_of pst) strategy_name |> the
                        : PSL_Interface.strategy;
    val result_opt   = run_under_overall timeouts NONE (fn () =>
                         (psl_strategy_to_monadic_tactic timeouts psl_strategy pst []
                           : (Dynamic_Utils.log * Proof.state) Seq.seq)
                         |> try Seq.hd)
                        : (Dynamic_Utils.log * Proof.state) option;
    val result_pair  = Option.map (apfst Dynamic_Utils.log_to_script_n_importance) result_opt
                        : ((strings * real) * Proof.state) option;
    val result       = Option.map (apfst fst) result_pair
  in
    result
  end;


(*used in bottom-up*)
fun pst_n_conjecture_has_counterexample (pst:Proof.state) (conjecture:string) =
  let
    fun has_counterexample _ =
      let
        val ctxt             = Proof.context_of pst;
        val pst_to_be_proved = Proof.theorem_cmd NONE (K I) [[(conjecture, [])]] ctxt;
        val quickpick        = PSL_Interface.lookup ctxt "Quick_Pick" |> the
                                : PSL_Interface.strategy;
        val timeouts         = {overall = 30.0, hammer = 30.0, quickcheck = 1.0, nitpick = 2.0}
                                : timeouts;
      in
        (*Timing out here says nothing about the conjecture, so report no counterexample, which is
          what the exception branch below already does.*)
        run_under_overall timeouts false (fn () =>
          (psl_strategy_to_monadic_tactic timeouts quickpick pst_to_be_proved []
            : (Dynamic_Utils.log * Proof.state) Seq.seq)
          |> Seq.pull |> is_none)
      end;
  in
    case try has_counterexample () of
        SOME result => result
      | NONE =>
          (warning ("Quickcheck/Nitpick failed while testing a generated conjecture; \
                     \skipping counterexample result.\n  conjecture: " ^ conjecture);
           false)
  end;


(*used in top-down*)
fun term_has_counterexample_in_pst (pst:Proof.state) (term:term) =
  let
    val quickpick        = PSL_Interface.lookup (Proof.context_of pst) "Quick_Pick" |> the
                            : PSL_Interface.strategy;
    val pst_to_be_proved = Proof.theorem NONE (K I) [[(term, [])]] (Proof.context_of pst)
                            : Proof.state;
    val timeouts         = {overall = 30.0, hammer = 30.0, quickcheck = 2.0, nitpick = 3.5}
                            : timeouts;
    val result_opt       = run_under_overall timeouts NONE (fn () =>
                             (psl_strategy_to_monadic_tactic timeouts quickpick pst_to_be_proved []
                               : (Dynamic_Utils.log * Proof.state) Seq.seq)
                             |> Seq.pull)
    val result_real      = (case result_opt of
                               NONE => 0.0
                             | SOME ((log, _), _) =>
                                 Dynamic_Utils.log_to_script_n_importance log |> snd)
  in
    result_real
  end;


(* assume_term_in_ctxt *)
(* Establishes a proved conjecture in the context, as a simp rule.
 *
 * It used to be noted as a plain fact, with no attributes, which made it useless to almost
 * everything that would have wanted it. auto, simp, fastforce and clarsimp - between them the
 * body of every strategy here - only consult the simp set, so a conjecture proved in one round
 * contributed nothing to the next.
 *
 * Measured, on "rv (rv xs) = xs": TBC proved app's associativity and identity laws, then
 * generated exactly the conjecture the goal needs,
 * "rv (app xs ys) = app (rv ys) (rv xs)", and failed to prove it. With those same three facts
 * merely present as plain facts, "(induct xs) auto" does not prove it; with them named,
 * "(induct xs) (auto simp: assoc ident1 ident2)" proves it at once. The facts were there and
 * unreachable.
 *
 * simp_add rather than chaining them in: a rewrite rule is what these are, and premises would
 * have to be re-supplied at every subsequent step. *)
fun assume_term_in_ctxt (lemma_name: string, term:term) (context:Proof.context) =
  let
    val vnames    = Variable.add_free_names context term []: strings;
    val binding   = (Binding.name lemma_name, [])          : binding * Token.src list;
    (* Any failure to state the conjecture is a NONE, not an escape.
     *
     * Defensive, and unlike the fix below not driven by a measured failure of its own: what the
     * TIP_prop_25 deaths establish is that an exception leaving this function ends the whole
     * search, and "handle ERROR" covers only one kind. What is being assumed here is a conjecture
     * the search invented, so failing to restate it on its own is an ordinary outcome - the caller
     * already treats an unnoted fact as simply unavailable.
     *
     * It does not catch everything, and cannot: Goal.prove_sorry defers the proof, so a statement
     * that fails to certify fails when the future is joined, at the enclosing command rather than
     * here. That was tried as a way to test this branch and is why it is not covered by
     * Assume_Term_Test.
     *
     * Interrupts are re-raised rather than swallowed. The search is cancelled by interrupt when
     * the memory guard stops it, and turning that into "this conjecture did not state" would hide
     * a stop as a result - which is the failure mode docs/2026_08_01_concurrency_review.md is about. *)
    val some_thm  =
      case Exn.capture
             (fn () => Goal.prove_sorry context vnames [] term
                         (fn {context, ...} => (Skip_Proof.cheat_tac context 1))) () of
        Exn.Res thm => SOME thm
      | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else (warning (lemma_name ^ ": " ^ Runtime.exn_message exn); NONE);
    (* Cased rather than "try (... [the some_thm]) context". ML evaluates the argument before try
       is entered, so "the" on a failed proof raised Option outside the handler and took the whole
       search with it - leaving the NONE branch below, written for exactly this case,
       unreachable. Measured: all six Isar positions of TIP_prop_25 died this way, identically. *)
    val maybe_pair =
      case some_thm of
        NONE     => NONE
      | SOME thm => try (Local_Theory.note (binding, [thm])) context;
  in
    case maybe_pair of
      NONE => (tbc_trace ("note: FAILED for " ^ lemma_name); context)
    | SOME ((_, noted_thms), context') =>
        (tbc_trace ("note: ok for " ^ lemma_name);
         if is_permutative_statement term then context'
         else Raw_Simplifier.add_simps noted_thms context')
  end;


(* drop_reversed_duplicates *)
(* TBC's templates generate an equation in both directions - associativity arrives as both
 * "app (app x y) z = app x (app y z)" and its mirror image - and proves both. As facts that is
 * merely redundant; as simp rules the pair rewrites back and forth forever. Keep whichever
 * direction is offered first and drop its mirror.
 *
 * Only exact mirrors are dropped. A permutative rule such as commutativity is its own mirror
 * up to renaming and is left alone: the simplifier handles those safely by ordered rewriting. *)
fun drop_reversed_duplicates (name_term_pairs:(string * term) list): (string * term) list =
  let
    (*Top_Down_Util is in the Abduction session, which is loaded after this one, so its
      equivalents of these are not reachable from here.*)
    fun strip_Trueprop (Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ trm) = trm
      | strip_Trueprop trm = trm;
    (*Rename free variables to the order in which they first occur, so that two statements
      differing only in the names of their variables compare equal.*)
    fun normalise trm =
      let
        fun rename (Free (name, typ)) mapping =
              (case AList.lookup (op =) mapping name of
                 SOME renamed => (Free (renamed, typ), mapping)
               | NONE =>
                   let val fresh = "_v" ^ Int.toString (length mapping)
                   in (Free (fresh, typ), (name, fresh) :: mapping) end)
          | rename (Abs (_, typ, body)) mapping =
              let val (body', mapping') = rename body mapping
              in (Abs ("", typ, body'), mapping') end
          | rename (trm1 $ trm2) mapping =
              let
                val (trm1', mapping1) = rename trm1 mapping;
                val (trm2', mapping2) = rename trm2 mapping1;
              in (trm1' $ trm2', mapping2) end
          | rename atom mapping = (atom, mapping);
      in fst (rename (strip_Trueprop trm) []) end;
    fun same trm1 trm2 = normalise trm1 = normalise trm2;
    fun reverse_of trm =
      case strip_Trueprop trm of
        (eq as Const (\<^const_name>\<open>HOL.eq\<close>, _)) $ lhs $ rhs => SOME (eq $ rhs $ lhs)
      | _ => NONE;
    fun is_mirror_of_kept kept trm =
      case reverse_of trm of
        NONE => false
      | SOME reversed =>
          (*a self-mirroring (permutative) equation must not count as its own duplicate*)
          not (same reversed trm) andalso exists (fn t => same t reversed) kept;
    fun keep [] _ acc = rev acc
      | keep ((name, trm) :: rest) kept acc =
          if is_mirror_of_kept kept trm
          then keep rest kept acc
          else keep rest (trm :: kept) ((name, trm) :: acc);
  in
    keep name_term_pairs [] []
  end;

fun drop_mirrored_pnodes (_:Proof.context) (pnodes:pnodes): pnodes =
  let
    val named = map (fn p => ((#lemma_name p, #lemma_term p), p)) pnodes;
    val kept_names =
      drop_reversed_duplicates (map fst named) |> map fst;
  in
    map_filter (fn ((name, _), p) =>
      if member (op =) kept_names name then SOME p else NONE) named
  end;

fun assume_terms_in_ctxt (name_term_pairs:(string * term) list) (ctxt:Proof.context) =
    fold assume_term_in_ctxt (drop_reversed_duplicates name_term_pairs) ctxt;


(* The term is stated directly. It used to be printed to text, parsed back to recover the very
   term it started from, and the text handed to Proof.theorem_cmd - a round trip that could only
   lose information, and did lose it silently: when the re-parse failed the whole function
   returned NONE, reporting "could not do this" for a term that was perfectly good. *)
fun cheat_lemma_term_in_pst (lemma_name:string) (lemma_term:term) (pst:Proof.state) =
  let
    val ctxt = Proof.context_of pst;
    val pst_to_prove =
      try (fn c =>
             Proof.theorem NONE (K I) [[(Syntax.check_prop c lemma_term, [])]] c
             |> inherit_chained_facts pst) ctxt
      : Proof.state option;
  in
    Option.map
      (Proof.map_context (assume_term_in_ctxt (lemma_name, lemma_term)))
      pst_to_prove
  end;

datatype strategy_for_eval = TBC_Strategy;

fun pnode_n_pst_to_pst_n_proof
      (strategy:strategy_for_eval) (hammer_duration:real) (pnode:pnode) (nth_round:int)
      (pst:Proof.state): Proof.state * pnode =
  if #proved_wo_assmng_cnjctr pnode
  then (pst, pnode)
  else
    let
      val lemma_name = #lemma_name pnode: string;
      val lemma_term = #lemma_term pnode: term;
      val lemma_stmt = pnode_stmt (Proof.context_of pst) pnode: string;
      val _ = tracing ("  try to prove " ^ lemma_name ^ ": " ^ lemma_stmt);
      fun attempt _ =
        let
          val pst_to_be_proved =
            (*Checked in this context first. theorem_cmd used to do this implicitly by parsing
              the printed statement, and dropping the parse without replacing the check left the
              conjectures unprovable - measured, a goal that had been solving went to zero
              proved auxiliaries.*)
            Proof.theorem NONE (K I)
              [[(Syntax.check_prop (Proof.context_of pst) lemma_term, [])]] (Proof.context_of pst)
            |> inherit_chained_facts pst: Proof.state;
          val timeout_hammer   = hammer_duration
          val timeouts         =
            {overall = attempt_timeout (), hammer = timeout_hammer, quickcheck = 1.0,
             nitpick = 2.0}: timeouts;
          val ordinary_name    = case strategy of
                                 TBC_Strategy => "TBC_Strategy";
          val strategy_name    =
            strategy_for_goal ordinary_name (Proof.context_of pst_to_be_proved)
              (pending_goal_of pst_to_be_proved);
          val log_opt          =
            pst_to_proof_log_opt timeouts strategy_name pst_to_be_proved <$> fst
            : Dynamic_Utils.log option;
        in
          case log_opt of
             NONE => (pst, pnode)
           | SOME (log:Dynamic_Utils.log) =>
             let
               val script   = Dynamic_Utils.mk_apply_script log: string;
               val tracing' = if false then tracing else K ();
               val _ = tracing' script;
               val _ = ("    proved " ^ lemma_name ^ ":"^ lemma_stmt) |> tracing;
               val _ = publish_progress_proof nth_round pnode log;
               (*TODO: use cheat_lemma_term_in_pst*)
               val context       = Proof.context_of pst;
               val _             = tracing' "  Before calling Syntax.read_prop";
               val goal_term     = lemma_term;
               val _             = tracing' "  Before calling Proof.map_context";
               val pst_to_return =
                 Proof.map_context (assume_term_in_ctxt (lemma_name, goal_term)) pst;
               val _             = tracing' "  Before returning from pst_n_prfnode.";
             in
               (pst_to_return,
                 {is_final_goal               = #is_final_goal pnode: bool,
                  lemma_name                  = #lemma_name pnode: string,
                  lemma_term                  = #lemma_term pnode: term,
                  proof_log                   = SOME log: Dynamic_Utils.log option,
                  proof                       = SOME script: string option,
                  proof_id                    =
                    (Unsynchronized.inc proof_id_counter; SOME (Unsynchronized.! proof_id_counter))
                    : int option,
                  refuted                     = #refuted pnode: bool,
                  proved_wo_assmng_cnjctr     = true: bool,
                  proved_in_nth_round         = SOME nth_round: int option
                  })
             end
        end;
    in
      case try attempt () of
          SOME result => result
        | NONE =>
            (warning ("TBC skipped a generated conjecture after a local proof-attempt failure.\n\
                       \  lemma: " ^ lemma_name ^ "\n  statement: " ^ lemma_stmt);
             (pst, pnode))
    end;

fun original_goal_is_proved (nodes:pnodes) =
  exists (fn nd => #is_final_goal nd andalso #proved_wo_assmng_cnjctr nd) nodes: bool;

fun conjectures_n_pst_to_pst_n_proof_w_limit
      (strategy:strategy_for_eval) (limit:int) (counter:int) unprocessed_pnodes pst
      : (Proof.state * pnodes) =
if limit > counter
then
  let
    fun conjectures_n_pst_to_pst_n_proof' [] pst processed_pnodes = (pst, processed_pnodes)
      | conjectures_n_pst_to_pst_n_proof'
          (unprocessed_pnode::unprocessed_pnodes: pnodes) pst (processed_pnodes: pnodes) =
      let
        val _ =
          if #is_final_goal unprocessed_pnode
          then tracing "Trying to prove the original goal." else ();
        val hammer_duration =
            if  #is_final_goal unprocessed_pnode
            then Long_Hammer pst
            else
              if   counter mod 2 = 1 (*The first and third rounds are supported by long-hammer*)
              then Short_Hammer pst
              else Long_Hammer pst;
        val (new_pst, processed_pnode) =
          pnode_n_pst_to_pst_n_proof strategy hammer_duration unprocessed_pnode counter pst;
      in
        conjectures_n_pst_to_pst_n_proof' unprocessed_pnodes new_pst
          (processed_pnodes @ [processed_pnode])
      end;

    val _ =
      if counter = 0 then ()
      else tracing ("\nTemplate-Based Conjecturing. Round: " ^ Int.toString counter ^ ".");
    val (new_pst, processed_pnodes) = conjectures_n_pst_to_pst_n_proof' unprocessed_pnodes pst [];
  in
    if original_goal_is_proved processed_pnodes
    then (new_pst, processed_pnodes)
    else conjectures_n_pst_to_pst_n_proof_w_limit
           strategy limit (counter+1) processed_pnodes new_pst
  end
else (pst, unprocessed_pnodes);



fun pnode_n_pst_to_proof_attempt
      (strategy:strategy_for_eval) (hammer_duration:real) (nth_round:int) (pst:Proof.state)
      (pnode:pnode): pnode * Dynamic_Utils.log option =
  if #proved_wo_assmng_cnjctr pnode
  then (pnode, NONE)
  (* The memory guard has asked the search to wind down. Starting another attempt now would
     keep the guard waiting and force it to insist by cancelling, which is the thing that
     endangers the session - see Resource_Limit.request_stop. An attempt already running still
     finishes, bounded by its own timeout. *)
  else if Resource_Limit.stop_is_requested ()
  then (tbc_trace ("attempt " ^ #lemma_name pnode ^ ": not started, stop requested");
        (pnode, NONE))
  (* The caller's prove_timeout, which used to bound only the abduction graph search. These rounds
     were bounded by a round count and each attempt's own hammer duration instead, so a
     prove_timeout of 240 still produced nine-minute sessions. Checked here, beside the stop
     request, because both answer the same question and an attempt already running still finishes
     under its own timeout either way. *)
  else if Resource_Limit.deadline_passed ()
  then (tbc_trace ("attempt " ^ #lemma_name pnode ^ ": not started, past the deadline");
        (pnode, NONE))
  else
    let
      val lemma_name = #lemma_name pnode: string;
      val lemma_term = #lemma_term pnode: term;
      val lemma_stmt = pnode_stmt (Proof.context_of pst) pnode: string;
      val _ = tracing ("  try to prove " ^ lemma_name ^ ": " ^ lemma_stmt);
      fun attempt _ =
        let
          (* Timed per attempt. The Isar subgoal path runs the same conjectures as the top-level
             one - measured, the same associativity/identity/commutativity set - and the same
             direct attempt to within two seconds, yet its conjecturing rounds take about ten
             times longer. Round-level timing cannot say whether that is every attempt costing
             more or a few costing enormously more, and those have different causes. *)
          val attempt_start = Timing.start ();
          val _ = tbc_trace ("attempt " ^ lemma_name ^ ": " ^ lemma_stmt);
          val pst_to_be_proved =
            (*Checked in this context first. theorem_cmd used to do this implicitly by parsing
              the printed statement, and dropping the parse without replacing the check left the
              conjectures unprovable - measured, a goal that had been solving went to zero
              proved auxiliaries.*)
            Proof.theorem NONE (K I)
              [[(Syntax.check_prop (Proof.context_of pst) lemma_term, [])]] (Proof.context_of pst)
            |> inherit_chained_facts pst: Proof.state;
          val timeout_hammer   = hammer_duration;
          (*Round 0 is the direct attempt at the original goal, which runs before conjecturing
            and only has to decide whether the goal is easy - see direct_attempt_timeout.*)
          val timeout_overall  =
            if nth_round = 0 then Direct_Attempt_Timeout pst else attempt_timeout ();
          val timeouts         =
            {overall = timeout_overall, hammer = timeout_hammer, quickcheck = 1.0,
             nitpick = 2.0}: timeouts;
          val ordinary_name    = case strategy of
                                 TBC_Strategy => "TBC_Strategy";
          (*An "instance" or "interpretation" obligation needs intro_classes/unfold_locales
            before any ordinary strategy can make progress on it.*)
          val strategy_name    =
            strategy_for_goal ordinary_name (Proof.context_of pst_to_be_proved)
              (pending_goal_of pst_to_be_proved);
          val _ = if strategy_name = ordinary_name then ()
                  else tbc_trace ("attempt " ^ lemma_name ^ ": dispatching to " ^ strategy_name);
          val log_opt          =
            pst_to_proof_log_opt timeouts strategy_name pst_to_be_proved <$> fst
            : Dynamic_Utils.log option;
          val _ = tbc_trace ("attempt " ^ lemma_name ^ ": strategy returned, proved = "
                             ^ Bool.toString (is_some log_opt) ^ ", took "
                             ^ Real.fmt (StringCvt.FIX (SOME 1))
                                 (Time.toReal (#elapsed (Timing.result attempt_start))) ^ "s");
          val _ =
            if is_some log_opt
            then tracing ("    proved " ^ lemma_name ^ ":" ^ lemma_stmt) else ();
          val _ =
            case log_opt of
              SOME log => publish_progress_proof nth_round pnode log
            | NONE => ();
        in
          (pnode, log_opt)
        end;
    in
      (*Exn.result re-raises interrupts, exactly as the "try" this replaces did; the only
        change is that a swallowed failure now says what it was when tracing is on.*)
      case Exn.result attempt () of
          Exn.Res result => result
        | Exn.Exn exn =>
            (tbc_trace ("proof attempt raised on " ^ lemma_name ^ ": " ^ Runtime.exn_message exn);
             warning ("TBC skipped a generated conjecture after a local parallel \
                       \proof-attempt failure.\n  lemma: " ^ lemma_name ^
                       "\n  statement: " ^ lemma_stmt);
             (pnode, NONE))
    end;

fun proof_attempt_to_pnode (nth_round:int)
      ((pnode:pnode), (log_opt: Dynamic_Utils.log option)): pnode =
  case log_opt of
      NONE => pnode
    | SOME log =>
        (Unsynchronized.inc proof_id_counter;
         {is_final_goal               = #is_final_goal pnode: bool,
          lemma_name                  = #lemma_name pnode: string,
          lemma_term                  = #lemma_term pnode: term,
          proof_log                   = SOME log: Dynamic_Utils.log option,
          proof                       = SOME (Dynamic_Utils.mk_apply_script log): string option,
          proof_id                    = SOME (Unsynchronized.! proof_id_counter): int option,
          refuted                     = #refuted pnode: bool,
          proved_wo_assmng_cnjctr     = true: bool,
          proved_in_nth_round         = SOME nth_round: int option});

fun newly_proved_attempt_to_named_term
      (pst:Proof.state) ((pnode:pnode), (log_opt: Dynamic_Utils.log option))
      : (string * term) option =
  if is_some log_opt
  then
    let
      val context = Proof.context_of pst;
    in
      SOME (#lemma_name pnode, #lemma_term pnode)
    end
  else NONE;

fun conjectures_n_pst_to_pst_n_proof_parallel_w_limit
      (strategy:strategy_for_eval) (limit:int) (counter:int) unprocessed_pnodes pst
      : (Proof.state * pnodes) =
if limit > counter
then
  let
    val _ =
      if counter = 0 then tracing "\nTemplate-Based Conjecturing. Direct goal attempt."
      else tracing ("\nTemplate-Based Conjecturing. Parallel round: " ^ Int.toString counter ^ ".");

    fun hammer_duration_for (pnode:pnode) =
        if #is_final_goal pnode
        then Long_Hammer pst
        else
          if counter mod 2 = 1
          then Short_Hammer pst
          else Long_Hammer pst;

    fun attempt pnode =
      pnode_n_pst_to_proof_attempt strategy (hammer_duration_for pnode) counter pst pnode;

    (* In the final round the goal goes first, and the auxiliaries only run if it fails.
     *
     * A round is a Par_List barrier, so it costs max(attempt) - and in the final round that is a
     * cost the *goal* waits for after its own answer is in. Measured on the Isar subgoal path:
     * final-round attempts were 1.1, 4.5, 5.4, 324.1, 324.1, so the goal was proved 1.1s in and
     * the round then ran a further 323s. That was the whole of that path's gap against the top
     * level, whose final-round auxiliaries merely happened to be trivial.
     *
     * Skipping those auxiliaries outright would be wrong, which is worth stating because it looks
     * safe: no attempt in a round sees another's result, and the recursion ends after the final
     * round, so nothing *within TBC* can use them. But when TBC does not prove the goal, the nodes
     * it proved are handed to AbductionProver - see apply_tbc_prelude_aux_to_pst in Abduction.thy -
     * and a final-round auxiliary is exactly as useful to that search as any other. So the
     * auxiliaries are dropped only in the case where they are provably dead: the goal is already
     * proved and abduction will not run.
     *
     * The order costs one thing: when the goal is not proved, the round becomes
     * goal + max(auxiliaries) rather than max(everything). That is the case where TBC has failed
     * and abduction is about to run anyway, and it buys the auxiliaries that search needs.
     *
     * PSL_EVAL_ATTEMPT_AUX_IN_FINAL_ROUND=1 restores the flat parallel round for comparison. *)
    val final_round =
      counter + 1 >= limit andalso getenv "PSL_EVAL_ATTEMPT_AUX_IN_FINAL_ROUND" <> "1";
    val (goal_pnodes, aux_pnodes) =
      if final_round then List.partition #is_final_goal unprocessed_pnodes
      else (unprocessed_pnodes, []);

    val _ = tbc_trace ("round " ^ Int.toString counter ^ ": Par_List.map over "
                       ^ Int.toString (length goal_pnodes) ^ " pnode(s)"
                       ^ (if final_round then " (final round: goal first, "
                                              ^ Int.toString (length aux_pnodes)
                                              ^ " auxiliaries held back)"
                          else ""));
    val goal_attempts =
      Par_List.map attempt goal_pnodes: (pnode * Dynamic_Utils.log option) list;
    (* Converted once and reused. proof_attempt_to_pnode is not a pure function: it takes the next
       proof_id from a counter, and proof_id is what proved nodes are sorted by when the auxiliary
       lemmas are emitted. Calling it a second time to ask whether the goal was proved would hand
       the same attempt a different id and reorder the emitted script. *)
    val goal_processed = map (proof_attempt_to_pnode counter) goal_attempts: pnodes;
    (* Held back rather than skipped: run them exactly when their results can still be used. *)
    val aux_attempts =
      if null aux_pnodes then []
      else if original_goal_is_proved goal_processed
      then (tbc_trace ("round " ^ Int.toString counter ^ ": goal proved, "
                       ^ Int.toString (length aux_pnodes)
                       ^ " auxiliaries not started - abduction will not run");
            map (fn p => (p, NONE)) aux_pnodes)
      else (tbc_trace ("round " ^ Int.toString counter ^ ": goal not proved, running "
                       ^ Int.toString (length aux_pnodes) ^ " auxiliaries for abduction");
            Par_List.map attempt aux_pnodes);
    val attempts = goal_attempts @ aux_attempts;
    val _ = tbc_trace ("round " ^ Int.toString counter ^ ": Par_List.map returned");
    val processed_pnodes =
      goal_processed @ map (proof_attempt_to_pnode counter) aux_attempts: pnodes;
    val newly_proved_named_terms =
      map (newly_proved_attempt_to_named_term pst) attempts |> Utils.somes: (string * term) list;
    (* Establish what this round proved, then chain it into the next round's attempts.
     *
     * Establishing alone is not enough: a noted fact is invisible to auto, simp, fastforce and
     * clarsimp, which are between them the body of every strategy here, so a conjecture proved
     * in one round contributed nothing to the next. Measured on "rv (rv xs) = xs": TBC proved
     * app's associativity and identity laws, generated exactly the conjecture the goal needs -
     * "rv (app xs ys) = app (rv ys) (rv xs)" - and could not prove it, though "(induct xs)
     * (auto simp: assoc ident1 ident2)" proves it at once from those very facts.
     *
     * Chained rather than declared as simp rules. Declaring them was tried and is worse than
     * useless: the search then succeeds by relying on ambient simp state that the replayed
     * script has no way to reproduce, so a found proof fails at replay - measured on all three
     * of AC1/AC2/AC5 - and a simp set accumulating conjectures in both directions can diverge
     * (one run ended in Interrupt_Breakdown). Chaining keeps the dependency between an
     * auxiliary and the proof that uses it explicit and bounded, which is what lets the result
     * be reconstructed as a structured Isar script. *)
    val new_pst =
      pst
      |> Proof.map_context (assume_terms_in_ctxt newly_proved_named_terms)
      |> chain_in_established_facts (map fst newly_proved_named_terms): Proof.state;
  in
    if original_goal_is_proved processed_pnodes
    then (new_pst, processed_pnodes)
    else conjectures_n_pst_to_pst_n_proof_parallel_w_limit
           strategy limit (counter+1) processed_pnodes new_pst
  end
else (pst, unprocessed_pnodes);

fun type_check (ctxt:Proof.context) (trm:term) = try (Syntax.check_term ctxt) trm: term option;

fun eq_consts_by_name (Const (cname1, _)) (Const (cname2, _)) = cname1 = cname2
  | eq_consts_by_name _ _ = false;

fun is_defined_in_pure_or_hol (Const (cname, ty)) =
      String.isPrefix "Pure" cname orelse String.isPrefix "HOL" cname
  | is_defined_in_pure_or_hol _                   = error "is_defined_in_pure_or_hol failed."

fun get_relevant_constants (ctxt:Proof.context) (goal:term) =
  let
    val consts_in_cncl = goal |> (fn trm:term => Term.add_consts trm []) |> map Const;
    val cnames_in_cncl = Term.add_const_names goal []: strings;
    val defining_terms =
      (flat o map (SeLFiE_Util.ctxt_n_cname_to_definitions ctxt)) cnames_in_cncl: terms;
    val relevant_consts_in_definitions =
      map (fn trm => Term.add_consts trm []) defining_terms |> flat |> map Const: terms;
    (*TODO: Probably we can filter out some constants here in relevant_consts to avoid
            calling is_known_func twice in relevant_binary_funcs and relevant_unary_funcs.*)
    val relevant_consts = relevant_consts_in_definitions
                       |> map Isabelle_Utils.strip_atyp
                       |> distinct (uncurry eq_consts_by_name): terms;
    (*Warning: Now we take the aggressive approach of removing all functions starting with
      HOL or Pure*)
    val relevant_binary_funcs = filter (fn trm => Isabelle_Utils.takes_n_arguments trm 2
                                          andalso not (is_defined_in_pure_or_hol trm)
                                          )
                                relevant_consts: terms;
    val relevant_unary_funcs  = filter (fn trm => Isabelle_Utils.takes_n_arguments trm 1
                                          andalso not (is_defined_in_pure_or_hol trm))
                                relevant_consts: terms;

    (*
    (* debug *)
    fun range_name trm  = trm |> type_of |> body_type   |> dest_Type |> fst;
    (* debug *)
    fun print_terms (trms:term list) = map (fn trm => tracing ("  " ^ Term.term_name trm)) trms;
    fun deep_print (trms) =
      map (fn trm => tracing ("  " ^ fst (dest_Const trm) ^ " " ^ range_name trm )) trms;
    fun we_have_something (trms:'a list) (something_str:string) =
      tracing ("We have " ^ Int.toString (length trms) ^ something_str);

    (* debug *)
    val _ = we_have_something consts_in_cncl " constants in cl before filtering:";
    val _ = deep_print consts_in_cncl;
    (* debug *)
    val _ = we_have_something relevant_consts_in_definitions
              " relevant constants in definition before filtering:";
    val _ = print_terms relevant_consts_in_definitions;
    val _ = we_have_something relevant_consts " relevant constants";
    val _ = print_terms relevant_consts;
    val _ = we_have_something relevant_unary_funcs " relevant_unary_funcs after filtering:";
    val _ = print_terms relevant_unary_funcs;
    val _ = we_have_something relevant_binary_funcs " relevant_binary_funcs after filtering:";
    val _ = deep_print relevant_binary_funcs;
    *)
  in
    (relevant_consts, relevant_binary_funcs, relevant_unary_funcs)
  end;

end;
