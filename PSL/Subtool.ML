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
  val tool_output_n_timeout_to_logtac: string -> real option (*importance*)-> real (*timeout*)-> Proof.state -> (Dynamic_Utils.log * Proof.state) Seq.seq;
  val quickcheck  : real -> Proof.state Dynamic_Utils.stttac;
  val nitpick     : real -> Proof.state Dynamic_Utils.stttac;
  val hammer      : real -> Proof.state Dynamic_Utils.stttac;
  val is_solved   : unit -> Proof.state Dynamic_Utils.stttac;
  val defer       : unit -> Proof.state Dynamic_Utils.stttac;
  val subgoal     : unit -> Proof.state Dynamic_Utils.stttac;
  val smart_induct: real -> Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
  val sh_output_to_sh_stttac: string -> Proof.state Dynamic_Utils.stttac;(*used in United Reasoning*)
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
    fun trace_to to     = show_trace ("Quickcheck timed out after " ^ Timeout.print to);
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
    fun trace_to to        = show_trace ("Nitpick timed out after " ^ Timeout.print to);
    fun nitpick_result' _  = Nitpick.pick_nits_in_subgoal state params Nitpick.Normal 1 1;
    val nitpick_result     = timeout nitpick_result' () handle Timeout.TIMEOUT to => (trace_to to; ("timeout", []));
    (*"genuine" means "genuine counter-example".*)
    val fst_result         = fst nitpick_result;
    val nitpick_succeed    = fst_result = Nitpick.genuineN;
    val importance         = if fst_result = Nitpick.quasi_genuineN
                             then 0.1 else if fst_result = Nitpick.potentialN
                             then 0.6 else 1.0;(*TODO: magic numbers*)
    val node               = Dynamic_Utils.Apply {using = [], methN = "-", back = 0, importance = SOME importance}
                           : Dynamic_Utils.node;
    val single             = Seq.single (log @ [node], state);
    val nitpick_tac_result = if nitpick_succeed then Seq.empty else single
                           : (Dynamic_Utils.node list * Proof.state) Seq.seq;
  in
    nitpick_tac_result
  end;

end;

(** sledgehammer/sem_ind output to monadic tactics on proof state **)
fun tool_output_n_timeout_to_logtac (sh_output:string) (importance: real option) (to:real) (state:Proof.state) =
  let
    (*syntax sugars*)
    type text_range        = Method.text_range;
    fun is_using sh_output = String.isPrefix "using " sh_output;
    val parse_using        = Parse.and_list1 Parse.thms1 : (Facts.ref * Token.src list) list list Token.parser;
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
    val p_get_meth    = (parse_one |-- parse_using) -- parse_one
                      : T list -> ((ref * srcs) list list * T) * T list;
    fun get_str tkns  = tkns
                      |> Utils.init (*drops "parserStopsWithMe" slowly.*)
                      |> map Token.unparse |> String.concatWith " " : string;
    val methN:string  = if   is_using sh_output
                        then p_get_meth tokens |> snd |> get_str
                        else parse_one  tokens |> snd |> get_str;
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
    val node          = Dynamic_Utils.Apply {using = using_strings, methN = methN, back = 0, importance = importance}
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
    val results_w_log = Seq.map (fn x => ([node], x)) tac_results : (Dynamic_Utils.log * Proof.state) Seq.seq;
  in
    results_w_log : (Dynamic_Utils.log * Proof.state) Seq.seq
  end;

fun sh_output_to_sh_stttac (output:string) = Dynamic_Utils.logtac_to_stttac (tool_output_n_timeout_to_logtac output NONE 7.0)
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
    (*TODO: Double-check. Should we really use futures here?*)
    val result             = Future.fork (fn () => run_sledgehammer pstate)
                          |> (fn f => try (apply_timeout Future.join) f handle Timeout.TIMEOUT _ => NONE)
                           : (bool * (Sledgehammer.sledgehammer_outcome * string)) option;
    val orig_string        = result <$> snd <$> snd  handle Empty =>
                             (if Utils.debug then tracing "Empty in orig_string/hammer_logtac" else (); 
                              NONE) : string option;
    fun did_smt_timeout (out::timed::_) = (Utils.are_same ("out)", out)) andalso
                                          (Utils.are_same ("timed", timed))
     |  did_smt_timeout _  = error "Something went wrong in Subtool.ML";
    val one_line_apply     = orig_string <$> space_explode " "
                            <$> drop 2                           (* drop "Try this:"*)
                            <$> rev <$> (fn tokens =>
                                if did_smt_timeout tokens then drop 5 tokens else drop 2 tokens)
                            <$> rev           (* drop "(0.1 ms)." and such.*)
                            <$> String.concatWith " "            : string option;
    val apply_script_cntnt = omap YXML.content_of one_line_apply : string option;
    val sh_returned        = if is_some apply_script_cntnt
                             then valOf result |> fst else false : bool;
  in
    if   sh_returned
    then
      tool_output_n_timeout_to_logtac (valOf apply_script_cntnt) NONE 10.0 pstate
    else Seq.empty : (Dynamic_Utils.log * Proof.state) Seq.seq
  end;

fun state_stttac timeout = Dynamic_Utils.logtac_to_stttac (hammer_logtac timeout) : Proof.state Dynamic_Utils.stttac;

end;

(** Smart_Induct: Smart_Induct as a state monad based tactic. **)
structure Smart_Induct_Tactic =
struct

fun pst_to_smart_induct_output_strs (pst:Proof.state) =
let
    val thm                       = Isabelle_Utils.proof_state_to_thm pst                            : thm;
    val thm_term                  = Thm.prop_of thm                                                  : term;
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst thm_term: Outer_Path_To_Unode.path_to_unode_table;
    val (ind_best_records, ind_max_point) = Apply_SeLFiE.score_n_induct_argss_n_proof_state_to_best_pairs 0.0 [] [] Apply_SeLFiE.Induction_Heuristic 5 pst outer_path_to_unode_table;
    fun record_to_pair {score, modifiers,...} = (score, modifiers);
    val best_pairs            = Par_List.map record_to_pair ind_best_records: (real * SeLFiE_Util.induct_arguments) list;
    val fst_subg_n_chaineds   = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst: terms;
    val arb_pairs             = Smart_Construction.proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs pst fst_subg_n_chaineds best_pairs
                              : (real * SeLFiE_Util.induct_arguments) list;
    val (arb_best_records, _) = Apply_SeLFiE.score_n_induct_argss_n_proof_state_to_best_pairs ind_max_point arb_pairs best_pairs Apply_SeLFiE.Generalization_Heuristic 10 pst outer_path_to_unode_table;
    fun mk_arb_message (record:{modifiers: SeLFiE_Util.induct_arguments, score: real}) = SeLFiE_Util.induct_arguments_to_string (#modifiers record);
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
    val induct_output_strs = Utils.try_with [] (Isabelle_Utils.timeout_apply (seconds timeout) pst_to_smart_induct_output_strs) pst: strings;
    val numb_of_candidates = length induct_output_strs;
    val low_importances    = replicate numb_of_candidates 0.7: real list;
    val importances        = 0.95 :: 0.9 :: 0.85 :: 0.8 :: 0.75 :: low_importances (*TODO: magic number for Abduction Prover*)
                          |> take numb_of_candidates: real list;
    val induct_outputs     = induct_output_strs ~~ importances: (string * real) list;
    val stttacs            = Par_List.map mk_state_stttac induct_outputs: Proof.state Dynamic_Utils.stttac list;
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

fun smart_induct to pst = Utils.try_with [] (Isabelle_Utils.timeout_apply (seconds to) (Smart_Induct_Tactic.state_stttacs to)) pst |> Seq.of_list;

end;