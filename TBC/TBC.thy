(*
 * TBC.thy
 * Authors:
 *   Yutaka Nagashima
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
theory TBC
  imports Main "PSL.PSL"
  keywords "prove_by_conjecturing" :: thy_goal_stmt
  and      "evaluate_property_based_conjecturing" :: thy_goal_stmt
begin

declare[[names_short]]

ML\<open> (* This code-block is an adaptation of the following file found in Isabelle 2022.
    Title:      Pure/Tools/find_consts.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Hoogle-like (https://www-users.cs.york.ac.uk/~ndm/hoogle) searching by
type over constants, but matching is not fuzzy.
*)
structure Pretty_Consts =
struct

(* matching types/consts *)

fun matches_subtype thy typat =
  Term.exists_subtype (fn ty => Sign.typ_instance thy (ty, typat));

fun check_const pred (c, (ty, _)) =
  if pred (c, ty) then SOME (Term.size_of_typ ty) else NONE;

fun opt_not f (c as (_, (ty, _))) =
  if is_some (f c) then NONE else SOME (Term.size_of_typ ty);

fun filter_const _ _ NONE = NONE
  | filter_const c f (SOME rank) =
      (case f c of
        NONE => NONE
      | SOME i => SOME (Int.min (rank, i)));

(* find_consts *)

fun pretty_consts ctxt raw_criteria =
  let
    val thy = Proof_Context.theory_of ctxt;
    val low_ranking = 10000;

    fun make_pattern crit =
      let
        val raw_T = Syntax.parse_typ ctxt crit;
        val t =
          Syntax.check_term
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            (Term.dummy_pattern raw_T);
      in Term.type_of t end;

    fun make_match (Find_Consts.Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) =>
              let
                val tye = Vartab.build (Sign.typ_match thy (qty, ty));
                val sub_size =
                  Vartab.fold (fn (_, (_, t)) => fn n => Term.size_of_typ t + n) tye 0;
              in SOME sub_size end handle Type.TYPE_MATCH => NONE
          end
      | make_match (Find_Consts.Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      | make_match (Find_Consts.Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion raw_criteria;

    fun user_visible (c, _) =
      if Consts.is_concealed (Proof_Context.consts_of ctxt) c
      then NONE else SOME low_ranking;

    fun eval_entry c =
      fold (filter_const c) (user_visible :: criteria) (SOME low_ranking);

    val {constants, ...} = Consts.dest (Sign.consts_of thy);
    val matches =
      fold (fn c => (case eval_entry c of NONE => I | SOME rank => cons (rank, c))) constants []
      |> sort (prod_ord (rev_order o int_ord) (string_ord o apply2 fst))
      |> map (apsnd fst o snd);
  in
    matches
  end;
end;
\<close>

(*** "TBC_Util.ML" ***)
ML\<open>
signature TBC_UTILS =
sig

type theorem_typ;
type pnode;
type pnodes;
type timeouts;

val theorem_typ_to_str:                       theorem_typ -> string;
val mk_lemma_name:                            Proof.context -> theorem_typ -> string -> string;
val proof_id_counter:                         int Unsynchronized.ref;
val statement_to_conjecture:                  Proof.state -> (string, string) Element.stmt -> pnode;
val sort_pnodes:                              pnodes -> pnodes;
val print_conjecture_w_proof:                 pnode -> string;
val print_proved_nodes:                       pnodes -> string;
val original_goal_was_proved_in_nth_round:    pnodes -> int -> bool;
val number_of_conjectures_proved_in_nth_round:pnodes -> int -> int;
val ctxt_n_trm_to_conjecture:                 Proof.context -> term -> {lemma_name:string, lemma_stmt:string};
val psl_strategy_to_monadic_tactic:           timeouts -> Monadic_Prover.str -> Proof.state -> Proof.state Monadic_Prover.monad;
val pst_to_proofscript_opt:                   timeouts -> string -> Proof.state -> (string * Proof.state) option;
val pst_n_conjecture_has_counterexample:      Proof.state -> string -> bool;
val term_has_counterexample_in_pst:           Proof.state-> term -> bool;
val assume_term_in_ctxt:                      (string * term) -> Proof.context -> local_theory;
val assume_terms_in_ctxt:                     (string * term) list -> Proof.context -> Proof.context;
val cheat_lemma_term_in_pst:                  string -> term -> Proof.state -> Proof.state option;
datatype strategy_for_eval = TAP21 | TBC_Strategy_W_Old_Smart_Induct | TBC_Strategy;
val pnode_n_pst_to_pst_n_proof:               strategy_for_eval -> real -> pnode -> int -> Proof.state -> Proof.state * pnode;
val original_goal_is_proved:                  pnodes -> bool;
val conjectures_n_pst_to_pst_n_proof_w_limit: strategy_for_eval -> int -> int -> pnodes -> Proof.state -> Proof.state * pnodes;
val type_check:                               Proof.context -> term -> term option;
val remove_sledgehammer_mash_file:            bool -> int;
val write_one_line_in_result_file:            Proof.state -> string -> unit;
val write_proof_script_in_result_file:        Proof.state -> string -> unit;
val get_relevant_constants:                   Proof.context -> term -> (terms * terms * terms);

val Long_Hammer:    real;
val Short_Hammer:   real;
val Bottom_Up:      theorem_typ; 
val Original_Goal:  theorem_typ;

end;

structure TBC_Utils: TBC_UTILS =
struct

val Short_Hammer = 10.0(*The default is 10.0. 10.0 for Isaplanner and Prod. 5.0 for TIP15.*)
val Long_Hammer  = 30.0(*The default is 30.0. 30.0 for Isaplanner and Prod. 10.0 for TIP15.*)

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
  lemma_stmt: string,(*TODO: term?*)
  proof: string option,(*Proof script to finish proving this node. Mainly for bottom-up conjecturing. Top-down uses this field only in or_trees.*)
  proof_id: int option, (*To track dependency. based on the timing proved with or w/o assuming conjectures.*)
  refuted: bool,
  proved_wo_assmng_cnjctr: bool,
  proved_in_nth_round: int option
}

type pnodes = pnode list;

val proof_id_counter = Unsynchronized.ref 0: int Unsynchronized.ref;

fun statement_to_conjecture (pst:Proof.state) (Element.Shows [((binding, _), [(stmt:string, _(*assumptions_maybe*))])]) =
      {
        is_final_goal = true,
        lemma_name = mk_lemma_name (Proof.context_of pst) Original_Goal "": string,
        lemma_stmt = stmt |> YXML.content_of |> String.explode |> Utils.init |> tl |> String.implode,
        proof = NONE,
        proof_id = NONE,
        refuted = false,(*we assume the final goal is a true statement.*)
        proved_wo_assmng_cnjctr = false,
        proved_in_nth_round = NONE
      }: pnode
  | statement_to_conjecture _ _ = error "statement_to_conjecture failed for the final goal.";

fun sort_pnodes (pnodes:pnodes): pnodes =
    sort (fn pnode_pair => option_ord int_ord (apply2 #proof_id pnode_pair)) pnodes;

fun print_conjecture_w_proof ({lemma_name, lemma_stmt, proof, ...}:pnode) =
  if is_none proof
    then error "print_conjecture_w_proof failed! This pnode is not proved yet."
    else "lemma " ^ lemma_name ^ ": " ^ enclose "\"" "\"" lemma_stmt ^ "\n" ^ the proof: string;


fun print_proved_nodes (pnodes:pnodes) =
  filter #proved_wo_assmng_cnjctr pnodes
  |> sort_pnodes
  |> (fn prfnds => (tracing (Int.toString (length prfnds) ^ " proofs found:"); prfnds))
  |> (fn prf_nds => "\n" :: map print_conjecture_w_proof prf_nds) 
  |> String.concatWith "\n"
  |> Active.sendback_markup_properties [Markup.padding_command];

fun original_goal_was_proved_in_nth_round (pnodes:pnodes) (n:int) =
  exists (fn nd => #is_final_goal nd andalso #proved_in_nth_round nd = SOME n) pnodes;

fun number_of_conjectures_proved_in_nth_round (pnodes:pnodes) (n:int) =
  filter (fn nd => not (#is_final_goal nd) andalso #proved_in_nth_round nd = SOME n) pnodes |> length;

fun ctxt_n_trm_to_conjecture (ctxt:Proof.context) (conjecture_trm:term) =
  let
    val lemma_name = "lemma_" ^ serial_string (): string;
    val conjecture_as_string = Isabelle_Utils.trm_to_string ctxt conjecture_trm: string;
  in
    {lemma_name = lemma_name,
     lemma_stmt = conjecture_as_string}
  end;



structure MP = Monadic_Prover;

type timeouts = {overall: real, hammer: real, quickcheck: real, nitpick: real};

fun psl_strategy_to_monadic_tactic (timeouts:timeouts) (strategy:MP.str) = fn (proof_state:Proof.state) =>
  let
    val core_tac  = MP.desugar strategy;
    val interpret = MP.interpret;
  in
    interpret (MP.eval_prim, MP.eval_para, MP.eval_pgt, MP.eval_strategic, MP.m_equal, MP.iddfc, (1,20), timeouts) core_tac proof_state
    handle Timeout.TIMEOUT timeout => (tracing ("TBC_Strategy timed out after: " ^ Time.toString timeout ^ "."); K Seq.empty)
  end: Proof.state MP.monad;


fun pst_to_proofscript_opt (timeouts:timeouts) (strategy_name:string )(pst:Proof.state): (string * Proof.state) option =
  let
    val psl_strategy        = PSL_Interface.lookup (Proof.context_of pst) strategy_name |> the: PSL_Interface.strategy;
    val result_seq          = psl_strategy_to_monadic_tactic timeouts psl_strategy pst []     : (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_opt          = try Seq.hd result_seq                                           : (Dynamic_Utils.log * Proof.state) option;
    val result = Option.map (apfst Dynamic_Utils.mk_apply_script) result_opt                  : (string * Proof.state) option;
  in
    result
  end;


(*used in bottom-up*)
fun pst_n_conjecture_has_counterexample (pst:Proof.state) (conjecture:string) =
  let
    val pst_to_be_proved = Proof.theorem_cmd NONE (K I) [[(conjecture, [])]] (Proof.context_of pst)
    val quickpick        = PSL_Interface.lookup (Proof.context_of pst) "Quick_Pick" |> the      : PSL_Interface.strategy;
    val timeouts         = {overall = 30.0, hammer = 30.0, quickcheck = 1.0, nitpick = 2.0}     : timeouts;
    val result_seq       = psl_strategy_to_monadic_tactic timeouts quickpick pst_to_be_proved []: (Dynamic_Utils.log * Proof.state) Seq.seq;
  in
    is_none (Seq.pull result_seq)(*TODO: Double-Check*)
  end;


(*used in top-down*)
fun term_has_counterexample_in_pst (pst:Proof.state) (term:term) =
  let
    val quickpick        = PSL_Interface.lookup (Proof.context_of pst) "Quickcheck" |> the      : PSL_Interface.strategy;
    val pst_to_be_proved = Proof.theorem NONE (K I) [[(term, [])]] (Proof.context_of pst)       : Proof.state;
    val timeouts         = {overall = 30.0, hammer = 30.0, quickcheck = 2.0, nitpick = 2.0}     : timeouts;
    val result_seq       = psl_strategy_to_monadic_tactic timeouts quickpick pst_to_be_proved []: (Dynamic_Utils.log * Proof.state) Seq.seq;
  in
    is_none (Seq.pull result_seq)
  end;


fun assume_term_in_ctxt (lemma_name: string, term:term) (context:Proof.context) =
  let
    val vnames    = Variable.add_free_names context term []: strings;
    val binding   = (Binding.name lemma_name, [])          : binding * Token.src list;
    val some_thm  = (SOME (Goal.prove_sorry context vnames [] term (fn {context, ...} => (Skip_Proof.cheat_tac context 1))))
                     handle ERROR err => (warning lemma_name; warning err; NONE);
    val maybe_pair = try (Local_Theory.note (binding, [the some_thm])) context;
  in
    if is_some maybe_pair then snd (the maybe_pair) else context
  end;


fun assume_terms_in_ctxt (name_term_pairs:(string * term) list) (ctxt:Proof.context) =
    fold assume_term_in_ctxt name_term_pairs ctxt;


fun cheat_lemma_term_in_pst (lemma_name:string) (lemma_term:term) (pst:Proof.state) =
  let
    (*TODO: improve*)
(*val _ = tracing "cheat_lemma_term_in_pst 1"*)
    val ctxt = Proof.context_of pst;
    val lemma_stmt          = Isabelle_Utils.trm_to_string ctxt lemma_term: string;
    val term_prop           = try (Syntax.read_prop (Proof.context_of pst)) lemma_stmt: term option;
    val pst_to_prove        = try (Proof.theorem_cmd NONE (K I) [[(lemma_stmt, [])]]) ctxt: Proof.state option;
    val prop_n_pst = Utils.mk_option_pair (term_prop, pst_to_prove);
    val pst_w_cheated_lemma = Option.map (fn (prop, pst) => Proof.map_context (assume_term_in_ctxt (lemma_name, prop)) pst) prop_n_pst: Proof.state option;
  in
    pst_w_cheated_lemma
  end;

datatype strategy_for_eval = TAP21 | TBC_Strategy_W_Old_Smart_Induct | TBC_Strategy;

fun pnode_n_pst_to_pst_n_proof (strategy:strategy_for_eval) (hammer_duration:real) (pnode:pnode) (nth_round:int) (pst:Proof.state): Proof.state * pnode =
  if #proved_wo_assmng_cnjctr pnode
  then (pst, pnode)
  else
    let
      val lemma_name = #lemma_name pnode: string;
      val lemma_stmt = #lemma_stmt pnode: string;
      val _ = tracing ("  try to prove " ^ lemma_name ^ ": " ^ lemma_stmt);
      val pst_to_be_proved = Proof.theorem_cmd NONE (K I) [[(lemma_stmt, [])]] (Proof.context_of pst): Proof.state;
      val timeout_hammer   = hammer_duration
      val timeouts         = {overall = 300.0, hammer = timeout_hammer, quickcheck = 1.0, nitpick = 2.0}   : timeouts;
      val strategy_name    = case strategy of
                             TAP21                           => "TAP_2021"
                           | TBC_Strategy_W_Old_Smart_Induct => "Old_TBC_Strategy"
                           | TBC_Strategy                    => "TBC_Strategy";
      val script_opt       = pst_to_proofscript_opt timeouts strategy_name pst_to_be_proved <$> fst         : string option;
      val pst_n_prfnode    = case script_opt of
         NONE                 => (pst, pnode)
       | SOME (script:string) => (
         let
           val tracing' = if false then tracing else K ();
           val _ = tracing' script;
           val _ =  ("    proved " ^ lemma_name ^ ":"^ lemma_stmt) |> tracing;
           (*TODO: use cheat_lemma_term_in_pst*)
           val context       = Proof.context_of pst;
           val _             = tracing' "  Before calling Syntax.read_prop";
           val goal_term     = Syntax.read_prop context lemma_stmt: term;
           val _             = tracing' "  Before calling Proof.map_context";
           val pst_to_return = Proof.map_context (assume_term_in_ctxt (lemma_name, goal_term)) pst;
           val _             = tracing' "  Before returning from pst_n_prfnode.";
         in
           (pst_to_return,
             {is_final_goal               = #is_final_goal pnode: bool,
              lemma_name                  = #lemma_name pnode: string,
              lemma_stmt                  = #lemma_stmt pnode: string,
              proof                       = SOME script: string option,
              proof_id                    = (Unsynchronized.inc proof_id_counter; SOME (Unsynchronized.! proof_id_counter)): int option,
              refuted                     = #refuted pnode: bool,
              proved_wo_assmng_cnjctr     = true: bool,
              proved_in_nth_round         = SOME nth_round: int option
              })
         end);
    in
      pst_n_prfnode: Proof.state * pnode
    end;

fun original_goal_is_proved (nodes:pnodes) = exists (fn nd => #is_final_goal nd andalso #proved_wo_assmng_cnjctr nd) nodes: bool;

fun conjectures_n_pst_to_pst_n_proof_w_limit (strategy:strategy_for_eval) (limit:int) (counter:int) unprocessed_pnodes pst: (Proof.state * pnodes) =
if limit > counter
then
  let
    fun conjectures_n_pst_to_pst_n_proof' [] pst processed_pnodes = (pst, processed_pnodes)
      | conjectures_n_pst_to_pst_n_proof' (unprocessed_pnode::unprocessed_pnodes: pnodes) pst (processed_pnodes: pnodes) =
      let
        val _ = if #is_final_goal unprocessed_pnode then tracing "Trying to prove the original goal." else ();
        val hammer_duration =
            if  #is_final_goal unprocessed_pnode
            then Long_Hammer
            else
              if   counter mod 2 = 1 (*The first round and third round are supported by long-hammer*)
              then Short_Hammer
              else Long_Hammer;
        val (new_pst, processed_pnode) = pnode_n_pst_to_pst_n_proof strategy hammer_duration unprocessed_pnode counter pst;
      in
        conjectures_n_pst_to_pst_n_proof' unprocessed_pnodes new_pst (processed_pnodes @ [processed_pnode])
      end;

    val _ = if counter = 0 then () else tracing ("\nProperty-Based Conjecturing. Round: " ^ Int.toString counter ^ ".");
    val (new_pst, processed_pnodes) = conjectures_n_pst_to_pst_n_proof' unprocessed_pnodes pst [];
  in
    if original_goal_is_proved processed_pnodes
    then (new_pst, processed_pnodes)
    else conjectures_n_pst_to_pst_n_proof_w_limit strategy limit (counter+1) processed_pnodes new_pst
  end
else (pst, unprocessed_pnodes);


fun type_check (ctxt:Proof.context) (trm:term) = try (Syntax.check_term ctxt) trm: term option;


fun remove_sledgehammer_mash_file output_to_external_file =
    if   output_to_external_file
    then Isabelle_System.bash ("rm $HOME/.isabelle/Isabelle2021-1/mash_state")
    else 1;


fun write_one_line_in_result_file (pst:Proof.state) (what_to_write:string) =
  let
    val thy                 = Proof.theory_of pst;
    val file_name           = "eval_result.csv": string;
    val path                = File.platform_path (Resources.master_directory thy);
    val paths               = space_explode "\\" path;
    val unix_path           = space_implode "/" paths
    val path_to_result_file = unix_path ^ "/" ^ file_name;
    val _ = Isabelle_System.bash ("touch " ^ path_to_result_file);
    val _ = Isabelle_System.bash ("echo -n '" ^ what_to_write ^ "\n' >> " ^ path_to_result_file);
  in
    ()
  end;

                        
fun write_proof_script_in_result_file (pst:Proof.state) (what_to_write:string) =
  let                           
    val thy                 = Proof.theory_of pst;
    val ctxt                = Proof.context_of pst;
    val theory_name         = Local_Theory.exit_global ctxt |> Context.theory_name
    val file_name           = "eval_scripts.txt": string;
    val path                = File.platform_path (Resources.master_directory thy);
    val separator           = "==========" ^ theory_name ^ "==========\n";
    val paths               = space_explode "\\" path;
    val unix_path           = space_implode "/" paths
    val path_to_result_file = unix_path ^ "/" ^ file_name;
    val _ = Isabelle_System.bash ("touch " ^ path_to_result_file);
    val _ = Isabelle_System.bash ("echo -n '" ^ separator ^ what_to_write ^ "\n' >> " ^ path_to_result_file);
  in
    ()
  end;

fun eq_consts_by_name (Const (cname1, _)) (Const (cname2, _)) = cname1 = cname2
  | eq_consts_by_name _ _ = false;

fun is_defined_in_pure_or_hol (Const (cname, ty)) = String.isPrefix "Pure" cname orelse String.isPrefix "HOL" cname
  | is_defined_in_pure_or_hol _                   = error "is_defined_in_pure_or_hol failed."

fun get_relevant_constants (ctxt:Proof.context) (goal:term) =
  let
    val consts_in_cncl = goal |> (fn trm:term => Term.add_consts trm []) |> map Const;
    val cnames_in_cncl = Term.add_const_names goal []: strings;
    val defining_terms = (flat o map (SeLFiE_Util.ctxt_n_cname_to_definitions ctxt)) cnames_in_cncl: terms;
    val relevant_consts_in_definitions = map (fn trm => Term.add_consts trm []) defining_terms |> flat |> map Const: terms;
    (*TODO: Probably we can filter out some constants here in relevant_consts to avoid
            calling is_known_func twice in relevant_binary_funcs and relevant_unary_funcs.*)
    val relevant_consts = relevant_consts_in_definitions
                       |> map Isabelle_Utils.strip_atyp
                       |> distinct (uncurry eq_consts_by_name): terms;
    (*Warning: Now we take the aggressive approach of removing all functions starting with HOL or Pure*)
    val relevant_binary_funcs = filter (fn trm => Isabelle_Utils.takes_n_arguments trm 2
                                          andalso not (is_defined_in_pure_or_hol trm)
                                          )
                                relevant_consts: terms;
    val relevant_unary_funcs  = filter (fn trm => Isabelle_Utils.takes_n_arguments trm 1
                                          andalso not (is_defined_in_pure_or_hol trm)) relevant_consts: terms;
    (*
    (* debug *)
    fun range_name trm  = trm |> type_of |> body_type   |> dest_Type |> fst;
    (* debug *)
    fun print_terms (trms:term list) = map (fn trm => tracing ("  " ^ Term.term_name trm)) trms;
    fun deep_print (trms) = map (fn trm => tracing ("  " ^ fst (dest_Const trm) ^ " " ^ range_name trm )) trms;
    fun we_have_something (trms:'a list) (something_str:string) =  tracing ("We have " ^ Int.toString (length trms) ^ something_str);
    (* debug *)
    val _ = we_have_something consts_in_cncl " constants in cl before filtering:";
    val _ = deep_print consts_in_cncl;
    (* debug *)
    val _ = we_have_something relevant_consts_in_definitions " relevant constants in definition before filtering:";
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
\<close>

(*** "TBC_Eval_Util.ML" ***)
ML\<open>
signature TBC_EVAL_STAT =
sig

type stat =
{
 theory_name: string,
 proved_by_tap21: bool,(*TODO: TO BE REMOVED AFTER EVALUATION*)
 proved_by_pbc_strategy_w_old_smart_induct: bool,(*TODO: TO BE REMOVED AFTER EVALUATION*)
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_by_tap21: real(*TODO: TO BE REMOVED*),
 execution_tim_of_pbc_str_w_old_smart_induct: real(*TODO: TO BE REMOVED*),
 execution_time_of_pbc: real
};

val default_stat: stat;

type stat_morphism = stat -> stat;

val update_theory_name_by_psl_in_stat                          : string -> stat_morphism;
val update_proved_by_tap21_in_stat                             : bool   -> stat_morphism;(*TODO: TO BE REMOVED*)
val update_proved_by_pbc_strategy_w_old_smart_induct_in_stat   : bool   -> stat_morphism;(*TODO: TO BE REMOVED*)
val update_proved_in_zeroth_round_in_stat                      : bool   -> stat_morphism;
val update_proved_in_first_round_in_stat                       : bool   -> stat_morphism;
val update_proved_in_second_round_in_stat                      : bool   -> stat_morphism;
val update_proved_by_pbc_in_stat                               : bool   -> stat_morphism;
val update_number_of_relevant_constants_in_stat                : int    -> stat_morphism;
val update_number_of_relevant_unary_constants_in_stat          : int    -> stat_morphism;
val update_number_of_relevant_binary_constants_in_stat         : int    -> stat_morphism;
val update_number_of_conjectures_produced_in_stat              : int    -> stat_morphism;
val update_number_of_conjectures_refuted_in_stat               : int    -> stat_morphism;
val update_number_of_conjectures_proved_in_first_round_in_stat : int    -> stat_morphism;
val update_number_of_conjectures_proved_in_second_round_in_stat: int    -> stat_morphism;
val update_execution_time_of_pbc_in_stat                       : real   -> stat_morphism;
val update_execution_time_of_pbc_str_w_old_smart_induct_in_stat: real   -> stat_morphism;(*TODO: TO BE REMOVED*)
val update_execution_time_by_tap21_in_stat                     : real   -> stat_morphism;(*TODO: TO BE REMOVED*)
val update_because_psl_solved_problem                          : stat_morphism;
val update_because_psl_unsolved_problem:
  {relevant_binary_funcs: terms,
   relevant_consts: terms,
   relevant_unary_funcs: terms,
   conjectures_w_counterexample: TBC_Utils.pnodes,
   conjectures_wo_counterexample: TBC_Utils.pnodes,
   processed_pnodes:TBC_Utils.pnodes} -> stat_morphism;

val print_stat: stat -> string;

end

structure TBC_Eval_Stat: TBC_EVAL_STAT =
struct

type stat =
{
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real
};

val default_stat: stat =
{
 theory_name                                  = "default": string,
 proved_by_tap21                              = false: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = false: bool,
 proved_in_zeroth_round                       = false: bool,
 proved_in_first_round                        = false: bool,
 proved_in_second_round                       = false: bool,
 proved_by_pbc                                = false: bool,
 number_of_relevant_constants                 = 9999: int,
 number_of_relevant_unary_constants           = 9999: int,
 number_of_relevant_binary_constants          = 9999: int,
 number_of_conjectures_produced               = 9999: int,
 number_of_conjectures_refuted                = 9999: int,
 number_of_conjectures_proved_in_first_round  = 0: int,
 number_of_conjectures_proved_in_second_round = 0: int,
 execution_time_of_pbc                        = 9999.9: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = 9999.9: real,
 execution_time_by_tap21                      = 9999.9: real
};

type stat_morphism = stat -> stat;

fun update_theory_name_by_psl_in_stat (thy_name:string) ({
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = thy_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_by_tap21_in_stat (proved_by_tap21:bool) ({
 theory_name: string,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21, ...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_by_pbc_strategy_w_old_smart_induct_in_stat (proved:bool) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21, ...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_in_zeroth_round_in_stat (proved:bool) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21, ...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_in_first_round_in_stat (proved:bool) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21, ...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_in_second_round_in_stat (proved:bool) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_proved_by_pbc_in_stat (proved:bool) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_relevant_constants_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = numb: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_relevant_unary_constants_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = numb: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_relevant_binary_constants_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = numb: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_conjectures_produced_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real, ...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = numb: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_conjectures_refuted_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = numb: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_conjectures_proved_in_first_round_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = numb: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_number_of_conjectures_proved_in_second_round_in_stat (numb:int) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = numb: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_execution_time_of_pbc_in_stat (time:real) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = time: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_execution_time_of_pbc_str_w_old_smart_induct_in_stat (time:real) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_time_by_tap21: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = time: real,
 execution_time_by_tap21                      = execution_time_by_tap21: real
}: stat;

fun update_execution_time_by_tap21_in_stat (time:real) ({
 theory_name: string,
 proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round: bool,
 proved_in_first_round: bool,
 proved_in_second_round: bool,
 proved_by_pbc: bool,
 number_of_relevant_constants: int,
 number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants: int,
 number_of_conjectures_produced: int,
 number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct: real,...
}: stat) =
{
 theory_name                                  = theory_name: string,
 proved_by_tap21                              = proved_by_tap21: bool,
 proved_by_pbc_strategy_w_old_smart_induct    = proved_by_pbc_strategy_w_old_smart_induct: bool,
 proved_in_zeroth_round                       = proved_in_zeroth_round: bool,
 proved_in_first_round                        = proved_in_first_round: bool,
 proved_in_second_round                       = proved_in_second_round: bool,
 proved_by_pbc                                = proved_by_pbc: bool,
 number_of_relevant_constants                 = number_of_relevant_constants: int,
 number_of_relevant_unary_constants           = number_of_relevant_unary_constants: int,
 number_of_relevant_binary_constants          = number_of_relevant_binary_constants: int,
 number_of_conjectures_produced               = number_of_conjectures_produced: int,
 number_of_conjectures_refuted                = number_of_conjectures_refuted: int,
 number_of_conjectures_proved_in_first_round  = number_of_conjectures_proved_in_first_round: int,
 number_of_conjectures_proved_in_second_round = number_of_conjectures_proved_in_second_round: int,
 execution_time_of_pbc                        = execution_time_of_pbc: real,
 execution_tim_of_pbc_str_w_old_smart_induct  = execution_tim_of_pbc_str_w_old_smart_induct: real,
 execution_time_by_tap21                      = time: real
}: stat;

fun update_because_psl_solved_problem (stat_w_thy_name:stat) =
  let
    val stat_w_thy_name_w_proved_in_zeroth_round   = update_proved_in_zeroth_round_in_stat true stat_w_thy_name: stat;
    val stat_w_number_of_relevant_constatns        = update_number_of_relevant_constants_in_stat        0 stat_w_thy_name_w_proved_in_zeroth_round;
    val stat_w_number_of_relevant_unary_constatns  = update_number_of_relevant_unary_constants_in_stat  0 stat_w_number_of_relevant_constatns;
    val stat_w_number_of_relevant_binary_constatns = update_number_of_relevant_binary_constants_in_stat 0 stat_w_number_of_relevant_unary_constatns;
    val stat_w_number_of_conjectures_produced      = update_number_of_conjectures_produced_in_stat      0 stat_w_number_of_relevant_binary_constatns;
    val stat_w_number_of_conjectures_refuted       = update_number_of_conjectures_refuted_in_stat       0 stat_w_number_of_conjectures_produced;
    val stat_w_proved_by_pbc                       = update_proved_by_pbc_in_stat true stat_w_number_of_conjectures_refuted;
  in
    stat_w_proved_by_pbc
  end;

fun update_because_psl_unsolved_problem
  {relevant_consts              : terms,
   relevant_unary_funcs         : terms,
   relevant_binary_funcs        : terms,
   conjectures_w_counterexample : TBC_Utils.pnodes,
   conjectures_wo_counterexample: TBC_Utils.pnodes,
   processed_pnodes             : TBC_Utils.pnodes}
  stat_w_thy_name =
  let
    val stat_w_thy_name_w_proved_in_zeroth_round     = update_proved_in_zeroth_round_in_stat                        false                                                                   stat_w_thy_name;
    val stat_w_number_of_relevant_constatns          = update_number_of_relevant_constants_in_stat        (length relevant_consts)                                                 stat_w_thy_name_w_proved_in_zeroth_round;
    val stat_w_number_of_relevant_unary_constatns    = update_number_of_relevant_unary_constants_in_stat  (length relevant_unary_funcs)                                            stat_w_number_of_relevant_constatns;
    val stat_w_number_of_relevant_binary_constatns   = update_number_of_relevant_binary_constants_in_stat (length relevant_binary_funcs)                                           stat_w_number_of_relevant_unary_constatns;
    val stat_w_number_of_conjectures_produced        = update_number_of_conjectures_produced_in_stat      (length (conjectures_w_counterexample @ conjectures_wo_counterexample )) stat_w_number_of_relevant_binary_constatns;
    val stat_w_number_of_conjectures_refuted         = update_number_of_conjectures_refuted_in_stat       (length conjectures_w_counterexample)                                    stat_w_number_of_conjectures_produced;
    val stat_w_proved_by_pbc                         = update_proved_by_pbc_in_stat (TBC_Utils.original_goal_is_proved processed_pnodes) stat_w_number_of_conjectures_refuted;
    val original_goal_was_proved_in_fisrt_round      = TBC_Utils.original_goal_was_proved_in_nth_round processed_pnodes 1;
    val stat_w_proved_in_first_round                 = update_proved_in_first_round_in_stat original_goal_was_proved_in_fisrt_round stat_w_proved_by_pbc;
    val original_goal_was_proved_in_second_round     = TBC_Utils.original_goal_was_proved_in_nth_round processed_pnodes 2;
    val stat_w_proved_in_second_round                = update_proved_in_second_round_in_stat original_goal_was_proved_in_second_round stat_w_proved_in_first_round;
    val number_of_conjectures_proved_in_first_round  = TBC_Utils.number_of_conjectures_proved_in_nth_round processed_pnodes 1;
    val number_of_conjectures_proved_in_second_round = TBC_Utils.number_of_conjectures_proved_in_nth_round processed_pnodes 2;
    val stat_w_numb_of_cjctrs_proved_in_first        = update_number_of_conjectures_proved_in_first_round_in_stat  number_of_conjectures_proved_in_first_round  stat_w_proved_in_second_round
    val stat_w_numb_of_cjctrs_proved_in_second       = update_number_of_conjectures_proved_in_second_round_in_stat number_of_conjectures_proved_in_second_round stat_w_numb_of_cjctrs_proved_in_first
  in
    stat_w_numb_of_cjctrs_proved_in_second
  end;

fun print_bool_in_capital (b:bool) = if b then "TRUE" else "FALSE"

fun print_stat (stat:stat): string = String.concatWith ","
[#theory_name                                  stat,
 #proved_by_tap21                              stat |> print_bool_in_capital,
 #proved_by_pbc_strategy_w_old_smart_induct    stat |> print_bool_in_capital,
 #proved_in_zeroth_round                       stat |> print_bool_in_capital,
 #proved_in_first_round                        stat |> print_bool_in_capital,
 #proved_in_second_round                       stat |> print_bool_in_capital,
 #proved_by_pbc                                stat |> print_bool_in_capital,
 #number_of_relevant_constants                 stat |> Int.toString,
 #number_of_relevant_unary_constants           stat |> Int.toString,
 #number_of_relevant_binary_constants          stat |> Int.toString,
 #number_of_conjectures_produced               stat |> Int.toString,
 #number_of_conjectures_refuted                stat |> Int.toString,
 #number_of_conjectures_proved_in_first_round  stat |> Int.toString,
 #number_of_conjectures_proved_in_second_round stat |> Int.toString,
 #execution_time_by_tap21                      stat |> Real.toString,
 #execution_tim_of_pbc_str_w_old_smart_induct  stat |> Real.toString,
 #execution_time_of_pbc                        stat |> Real.toString
];

end;
\<close>

(*** "Template_Based_Conjecturing.ML" ***)
ML\<open>
(*
 * TEMPLATE_BASED_CONJECTURING
 * Authors:
 *   Yutaka Nagashima, Zijin Xu, Ningli Wang, and Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** signature TEMPLATE_BASED_CONJECTURING ***)
signature TEMPLATE_BASED_CONJECTURING =
sig

datatype property =
(* property_for_binary_function *)
  Associativity     (*f (f (x, y), z) = f (x, f (y, z))*)(*f (x, f (y, z)) = f (f (x, y), z)*)(*Prod/11*)(*Prod/12*)
| Identity          (*left identity : f (e, x) = x*) (*right identity: f (x, e) = x for all x*)(*Prod/11*)(*Prod/12*)
| (*TODO*)Invertibility
| Commutativity     (*f (x, y) = f (y, x)*)
| Idempotent_Element(*f (e, e) = e for some e*)
| Idempotency       (*f (x, x) = x *)
| Zero_Element      (*left zero : f (z, x) = z*) (*right zero: f (x, z) = z for all x*)
  (*TODO: Prod/09*) (*https://en.wikipedia.org/wiki/Absorbing_element*)
(* property_for_two_functions *)
| Distributivity      (*f (x, g (y, z)) = g(f (x, y), f (x, z))*)
                      (*f (g (x, y), z) = g (f (x, y), f (x, z))*)
| Ant_Distributivity  (*f (g (x, y)) = g (f (x), f(y))*) (*?*)
| Homomorphism_2      (*f (g (x, y)) = g (f (x), f(y))*)(*Prod/11*)
(* property_for_relations *)(*TODO: filter out functions whose return types are not Bool*)
| Transitivity (*x R y \<Longrightarrow> y R z \<Longrightarrow> x R z*)
| Symmetry     (*x R y \<Longrightarrow> y R x*)
| Connexity    (*x R y \<or> y R x \<or> (x = y)*)
| Reflexivity  (*x R x*)
(* bottom-up conjecturing for unary operators *)
| Square      (*f (f x) = x for all x *) (*Prod/11*)
|(*TODO*) Square_Root (*f (f x) = x for some x*)
| Projection  (*f (f x) = f x for all x *) (*TIP15 sorts*)
(* non-algebraic bottom-up conjecturing *)
|(*TODO*) Swap_Constructor (*Prod/13*)(*Prod/15*)
| Swap_Unary (*f (x, g (y)) = f ( g (x), y )*)
| Composite_Commutativity (* f (g (x, y)) = f (g (y, x)) *)

val property_as_string: property -> string;

val pst_n_property_n_trm_to_pnode: Proof.state -> (property * term) -> TBC_Utils.pnode;

val ctxt_n_typ_to_typs: Proof.context -> typ -> typ list;

val ctxt_n_typ_to_consts_full:        Proof.context -> typ -> terms;
val ctxt_n_typ_to_nullary_const: Proof.context -> typ -> terms;
val ctxt_n_typ_to_unary_const:   Proof.context -> typ -> terms;
val ctxt_n_typ_to_binary_const:  Proof.context -> typ -> terms;

(*property_for_binary_function*)

val ctxt_n_const_to_associativity:       Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_identity:            Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_invertibility:       Proof.context -> term -> (property * term) list
val ctxt_n_const_to_commutativity:       Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_idempotent_element:  Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_idempotence:         Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_zero_element:        Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_distributivity:     Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_anti_distributivity:Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_homomorphism_2:     Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_square:             Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_square_root:        Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_projection:         Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_swap_constructor:   Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_transitivity:       Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_symmetry:           Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_connexity:          Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_reflexibility:      Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_swap_unary:         Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_composite_commutativity: Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_all_conjecture_term: Proof.context -> term -> (property * term) list;

end;

(*** structure Template_Based_Conjecturing ***)
structure Template_Based_Conjecturing: TEMPLATE_BASED_CONJECTURING =
struct

val strip_atyp        = Isabelle_Utils.strip_atyp;
val takes_n_arguments = Isabelle_Utils.takes_n_arguments;

datatype direction = Left | Right;

datatype property =
(* property_for_binary_function*)
  Associativity
| Identity
| Invertibility
| Commutativity
| Idempotent_Element
| Idempotency
| Zero_Element
(* property_for_two_functions *)
| Distributivity     (*2,2*)
| Ant_Distributivity (*1,2*)
| Homomorphism_2     (*1,2*)
(* property_for_relations *)
| Transitivity
| Symmetry
| Connexity
| Reflexivity
(* bottom-up conjecturing for unary operators *)
| Square (*f (f x) = x for all x*) (*Prod/11*)
|(*TODO*) Square_Root (*f (f x) = x for some x*)
| Projection  (*f (f x) = f x for all x *) (*TIP15 sorts*)
(* non-algebraic bottom-up conjecturing *)
| Swap_Constructor
| Swap_Unary
| Composite_Commutativity;

fun property_as_string Associativity           = "Associativity"
  | property_as_string Identity                = "Identity"
  | property_as_string Invertibility           = "Invertibility"
  | property_as_string Commutativity           = "Commutativity"
  | property_as_string Idempotent_Element      = "Idempotent_Element"
  | property_as_string Idempotency             = "Idempotency"
  | property_as_string Zero_Element            = "Zero_Element"
  | property_as_string Distributivity          = "Distributivity"
  | property_as_string Ant_Distributivity      = "Ant_Distributivity"
  | property_as_string Homomorphism_2          = "Homomorphism_2"
  | property_as_string Transitivity            = "Transitivity"
  | property_as_string Symmetry                = "Symmetry"
  | property_as_string Connexity               = "Connexity"
  | property_as_string Reflexivity             = "Reflexivity"
  | property_as_string Square                  = "Square"
  | property_as_string Square_Root             = "Square_Root"
  | property_as_string Projection              = "Projection"
  | property_as_string Swap_Constructor        = "Swap_Constructor"
  | property_as_string Swap_Unary              = "Swap_Unary"
  | property_as_string Composite_Commutativity = "Composite_Commutativity";

fun pst_n_property_n_trm_to_pnode (pst:Proof.state) (property:property, conjecture_trm:term): TBC_Utils.pnode =
    let
      val lemma_name = TBC_Utils.mk_lemma_name (Proof.context_of pst) TBC_Utils.Bottom_Up (property_as_string property): string;
      val conjecture_as_string = Isabelle_Utils.trm_to_string (Proof.context_of pst) conjecture_trm: string;
    in
      {
        is_final_goal = false,
        lemma_name = lemma_name,
        lemma_stmt = conjecture_as_string,
        proof = NONE,
        proof_id = NONE,
        refuted = TBC_Utils.pst_n_conjecture_has_counterexample pst conjecture_as_string,
        proved_wo_assmng_cnjctr = false,
        proved_in_nth_round = NONE
      }: TBC_Utils.pnode
    end;


fun get_ancestors_of_main ctxt =
  let
    fun get_Main ctxt = SOME (Theory.check {long = true} ctxt ("Main", Position.none))
                        handle ERROR _ => NONE;
    fun ancestor_list ctxt = (Theory.ancestors_of ctxt |> map Context.theory_name)
    val maybe_main = get_Main ctxt
    val ancestors_list = case maybe_main of
              NONE   => []
            | SOME _ => ancestor_list (Context.get_theory {long = true} (Proof_Context.theory_of @{context}) "Main")
  in
    ancestors_list
  end

fun filter_out_invalid_names ctxt (const_names :strings) =
    let
      (* Isabelle sometimes creates redundant constants, we remove them by pattern matching with name *)
      val invalid_prefix = "partial_term_of_itself_inst"::"typerep_itself_inst"::
                           (get_ancestors_of_main ctxt)
      val invalid_suffix = ["_sumC", "_dom", "set_list"]
      val invalid_other_name = ["size", "term_of", "wit", "equal_"]
      val mild_exceptions = []
      val exceptions = ["HOL.True", "HOL.False", "HOL.conj", "HOL.disj", "HOL.Not"] 
      fun notin _ [] = true | notin name (x::xs) = (name<>x) andalso notin name xs

      (* checking for prefix, suffix and other *)
      fun has_invalid_prefix name prefix  = name |> (String.isPrefix prefix)
      fun has_invalid_prefixes name = notin name mild_exceptions andalso  List.exists (has_invalid_prefix name) invalid_prefix 

      fun has_other_invalid_name name other_name = name |> Long_Name.base_name |> (String.isPrefix other_name)
      fun has_other_invalid_names name  = List.exists (has_other_invalid_name name) invalid_other_name 

      fun has_invalid_suffix name suffix = name |> (String.isSuffix suffix)
      fun has_invalid_suffixes name = List.exists (has_invalid_suffix name) invalid_suffix 

      fun has_invalid_name name = has_invalid_prefixes name orelse has_invalid_suffixes name orelse has_other_invalid_names name
    in filter_out has_invalid_name const_names
    end;

val ctxt_n_typ_to_typs = undefined: Proof.context -> typ -> typ list;

fun ctxt_n_typ_to_consts_full ctxt typ =
    let
      fun ctxt_n_typ_to_consts_full' (ctxt:Proof.context) (typ:typ) =
        let
          val typ_as_string   = Syntax.string_of_typ ctxt typ
          |> YXML.parse_body
          |> XML.content_of : string;
          val const_typ_pairs = Pretty_Consts.pretty_consts ctxt [(true, Find_Consts.Strict typ_as_string)]: (string * typ) list;
          val const_names     = map fst const_typ_pairs                                                    : strings;
          val filtered_const_names = filter_out_invalid_names ctxt const_names
          val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) filtered_const_names 
                       : terms;
        in
          consts_w_dummyT: terms
        end;
    in try (ctxt_n_typ_to_consts_full' ctxt) typ |> Utils.is_some_null end;

fun ctxt_n_typ_to_consts_domain ctxt typ =
    let
      (* the 2 auxiliary functions are used to check if the domain type of the term is typ *)
      fun replace_tvars_with_dummyT typ' = map_atyps (K dummyT) typ'
      fun check_domain typ' = fst (dest_Type typ') = "fun" andalso 
                              replace_tvars_with_dummyT (domain_type typ') = replace_tvars_with_dummyT typ
      fun ctxt_n_typ_to_consts_domain' (ctxt:Proof.context) (typ:typ) =
        let
          val typ_as_string   = Syntax.string_of_typ ctxt typ
          |> YXML.parse_body
          |> XML.content_of : string;
          val const_typ_pairs = Pretty_Consts.pretty_consts ctxt [(true, Find_Consts.Loose typ_as_string)]: (string * typ) list;
          val filtered_const_typ_pairs = filter (fn pair => check_domain (snd pair)) const_typ_pairs
          val const_names     = map fst filtered_const_typ_pairs                                                    : strings;
          val filtered_const_names = filter_out_invalid_names ctxt const_names
          val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) filtered_const_names 
                       : terms;
        in
          consts_w_dummyT: terms
        end;
    in try (ctxt_n_typ_to_consts_domain' ctxt) typ |> Utils.is_some_null end;

(*to find candidates for the identity element*)
fun ctxt_n_typ_to_nullary_const ctxt typ = ctxt_n_typ_to_consts_full ctxt typ;

(*to find candidates for the inverse function*)
fun ctxt_n_typ_to_unary_const ctxt typ = ctxt_n_typ_to_consts_full ctxt (typ --> typ);

(* to find unary functions with specified domain *)
fun ctxt_n_domain_typ_to_unary_const ctxt typ = ctxt_n_typ_to_consts_domain ctxt typ;

(*to find candidates for the distributive property*)
fun ctxt_n_typ_to_binary_const ctxt typ = ctxt_n_typ_to_consts_full ctxt ([typ, typ] ---> typ);

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun mk_free_variable_of_dummyT (i:int) = mk_free_variable_of_typ dummyT i;

(*assume binary*)(*TODO: Do not assume.*)
val list_comb = Term.list_comb;

fun all_args_are_same_typ (funcs:terms) =
    let
      fun get_arg_typs (f:typ)      = snd (strip_type f)::fst (strip_type f)     : typ list;
      val typs                      = map (get_arg_typs o type_of) funcs |> flat : typ list;
      val numb_of_distinct_elements = distinct (op =) typs |> length             : int;
    in
      numb_of_distinct_elements = 1
    end;

fun all_domain_args_are_same_typ funcs = 
  let
      fun get_arg_typs (f:typ)      = fst (strip_type f)     : typ list;
      val typs                      = map (get_arg_typs o type_of) funcs |> flat : typ list;
      val numb_of_distinct_elements = distinct (op =) typs |> length             : int;
    in
      numb_of_distinct_elements = 1
    end;



(*property_for_binary_function*)

fun mk_eq (lhs:term, rhs:term) = strip_atyp @{term "HOL.eq"} $ strip_atyp lhs $ strip_atyp rhs;

fun ctxt_n_const_to_associativity (ctxt:Proof.context) (func:term) =
(*f (f (x, y), z) = f (x, f (y, z))*)
(*f (x, f (y, z)) = f (f (x, y), z)*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
     (let
        val func_w_dummyT      = map_types (K dummyT) func                   : term;
        val [var1, var2, var3] = map mk_free_variable_of_dummyT [1,2,3]      : terms;
        val lhs                = list_comb (func_w_dummyT, [var1, list_comb (func_w_dummyT, [var2, var3])]) |> strip_atyp;
        val rhs                = list_comb (func_w_dummyT, [list_comb (func_w_dummyT, [var1, var2]), var3]) |> strip_atyp;
        val assocs             = map mk_eq [(lhs, rhs), (rhs, lhs)]|> map (TBC_Utils.type_check ctxt) |> Utils.somes: terms ;
        val cnjctrs            = map (fn trm => (Associativity, trm)) assocs
      in
        cnjctrs: (property * term) list
      end)
    else [];

datatype zero_or_identity = Zero_Elem | Identity_Elem;

fun ctxt_n_const_to_zero_or_identity' (z_or_i:zero_or_identity) (ctxt:Proof.context) (direct:direction)
  (func as Const (_, typ):term) =
(*left  identity: f (e, x) = x*)
(*right identity: f (x, e) = x*)
(*left  zero    : f (z, x) = z*)
(*right zero    : f (x, z) = z*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val typ_of_arg     = binder_types typ |> (case direct of
                              Left  =>  List.hd
                            | Right => (Utils.the' "ctxt_n_trm_to_identity in Bottom_Up_Conjecturing.ML failed"
                                      o try (fn args => nth args 1)))   : typ;
        val nullary_consts = ctxt_n_typ_to_nullary_const ctxt typ_of_arg: terms;
        val func_w_dummyT  = strip_atyp func                            : term;
        val free_var       = mk_free_variable_of_dummyT     1           : term;
        fun mk_equation (identity_element:term) =
          let
            val lhs = case direct of
                Left  => list_comb (func_w_dummyT, [identity_element, free_var]): term
              | Right => list_comb (func_w_dummyT, [free_var, identity_element]): term;
            val rhs = case z_or_i of
                      Zero_Elem     => identity_element 
                    | Identity_Elem => free_var      : term;
            val eq = mk_eq (lhs, rhs)                : term;
          in
            eq: term
          end;
        val cnjctr_trms = map mk_equation nullary_consts |> map (TBC_Utils.type_check ctxt) |> Utils.somes            : terms;
        val cnjctrs     = map (fn trm => (Identity, trm)) cnjctr_trms: (property * term) list;
      in
        cnjctrs
      end
    else []
  | ctxt_n_const_to_zero_or_identity' _ _ _ _ = [];

fun ctxt_n_const_to_identity ctxt trm: (property * term) list =
    ctxt_n_const_to_zero_or_identity' Identity_Elem ctxt Left trm
  @ ctxt_n_const_to_zero_or_identity' Identity_Elem ctxt Right trm;

val ctxt_n_const_to_invertibility = undefined; (*TODO*)

fun ctxt_n_const_to_commutativity (ctxt:Proof.context) (func:term) =
  (*f (x, y) = f (y, x)*)
    if takes_n_arguments func 2 andalso all_domain_args_are_same_typ [func]
    then
      let
        val func_w_dummyT = strip_atyp func                                : term;
        val (var1,var2)   = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val lhs           = list_comb (func_w_dummyT, [var1,var2])         : term;
        val rhs           = list_comb (func_w_dummyT, [var2,var1])         : term;
        val eq            = mk_eq (lhs, rhs)                               : term;
        val commutativity = TBC_Utils.type_check ctxt eq                      : term option;
      in
        case commutativity of SOME x => [(Commutativity, x)] | _ => []
        
      end
    else [];

fun ctxt_n_const_to_idempotent_element (ctxt:Proof.context) (func as Const (_, typ): term) =
  (*f (e, e) = e for some e*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val typ_of_arg     = binder_types typ |> List.hd                : typ;
        val nullary_consts = ctxt_n_typ_to_nullary_const ctxt typ_of_arg: terms;
        val func_w_dummyT  = strip_atyp func                            : term;
        fun mk_equation (identity_element:term) =
          let
            val lhs = list_comb (func_w_dummyT, [identity_element, identity_element]): term;
            val eq  = mk_eq (lhs, identity_element)                                  : term;
          in
            TBC_Utils.type_check ctxt eq
          end;
        val idempotents = map mk_equation nullary_consts |> Utils.somes               
      in
        map (fn trm => (Idempotent_Element, trm)) idempotents
      end
    else []
  | ctxt_n_const_to_idempotent_element _ _ = [];

fun ctxt_n_const_to_idempotence (ctxt:Proof.context) (func as Const(_, _)) =
    (* f (x, x) = x *)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val func_wo_typ = strip_atyp func                 : term;
        val var         = mk_free_variable_of_dummyT 1    : term;
        val idempotence = mk_eq (list_comb (func_wo_typ, [var, var]), var) |> TBC_Utils.type_check ctxt;
      in
        case idempotence of SOME x => [(Idempotency, x)] | _ => []
        
      end
    else []
 | ctxt_n_const_to_idempotence _ _ = [];

fun ctxt_n_const_to_zero_element ctxt trm: (property * term) list =
    ctxt_n_const_to_zero_or_identity' Zero_Elem ctxt Left trm
  @ ctxt_n_const_to_zero_or_identity' Zero_Elem ctxt Right trm;

(*property_for_two_functions*)
fun ctxt_n_consts_to_distributivity' (ctxt:Proof.context) (func1:term) (func2:term) =
    let
      val (func1_wo_typ, func2_wo_typ) = Utils.map_pair strip_atyp (func1, func2): (term * term);
      val [var1, var2, var3]           = map mk_free_variable_of_dummyT [1,2,3]  : terms;
      val (left_lhs, right_lhs)        =  (list_comb (func1_wo_typ, [var1, list_comb (func2_wo_typ, [var2, var3])]),
                                           list_comb (func1_wo_typ, [list_comb (func2_wo_typ, [var1, var2]), var3])
                                           );
      val (left_rhs, right_rhs)        =  (list_comb
                                            (func2_wo_typ,
                                             [list_comb (func1_wo_typ, [var1, var2]),
                                              list_comb (func1_wo_typ, [var1, var3])
                                              ]
                                             ),
                                           list_comb
                                            (func2_wo_typ,
                                             [list_comb (func1_wo_typ, [var1, var3]),
                                              list_comb (func1_wo_typ, [var2, var3])
                                              ]
                                             )
                                           );
      val cnjctrs               = [mk_eq (left_lhs, left_rhs), mk_eq (right_lhs, right_rhs)]
                               |> map (TBC_Utils.type_check ctxt) |> Utils.somes;
    in
      cnjctrs
    end;

fun ctxt_n_consts_to_distributivity (ctxt:Proof.context) (func1 as Const (_, typ)) =
(* left-distributive:  f (x, g (y, z)) = g (f (x, y), f (x, z))
 * right-distributive: f (g (x, y), z) = g (f (x, y), f (x, z))
 *)
    if takes_n_arguments func1 2 andalso all_args_are_same_typ [func1]
    then
      let
        val return_typ = strip_type typ |> snd                  : typ;
        val b_funcs = ctxt_n_typ_to_binary_const ctxt return_typ: terms;
        val cnjctr_trms = map (ctxt_n_consts_to_distributivity' ctxt func1) b_funcs |> flat;
      in
        map (fn trm => (Distributivity, trm)) cnjctr_trms
      end
    else []
  | ctxt_n_consts_to_distributivity _ _ = [];

fun ctxt_n_consts_to_anti_distributivity' (ctxt:Proof.context) binary_func unary_func =
(*f (g (x, y)) = g (f (y), f (x))*)
    let

      val (unary_wo_typ, binary_wo_typ) = Utils.map_pair strip_atyp (unary_func, binary_func)                : (term * term);
      val (var1, var2)                  = Utils.map_pair mk_free_variable_of_dummyT (1,2)                    : (term * term);
      val lhs                           = list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var1, var2])]): term;
      val rhs                           = list_comb
                                          (binary_wo_typ,
                                           [list_comb (unary_wo_typ, [var2]),
                                            list_comb (unary_wo_typ, [var1])
                                            ]
                                           )
                                          ;
      val anti_distributivity           = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt
    in
      case anti_distributivity of SOME x => [(Ant_Distributivity, x)] | _ => []      
    end;

fun ctxt_n_consts_to_anti_distributivity (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_args_are_same_typ [binary_func]
    then
      let
        val return_typ = strip_type typ |> snd                 : typ;
        val u_funcs = ctxt_n_typ_to_unary_const ctxt return_typ: terms;
      in
        map (ctxt_n_consts_to_anti_distributivity' ctxt binary_func) u_funcs |> flat
      end
    else []
  | ctxt_n_consts_to_anti_distributivity _ _ = [];


fun ctxt_n_consts_to_composite_commutativity' (ctxt:Proof.context) binary_func unary_func =
(*f (g (x, y)) = f (g (y, x))*)
    let
      val (unary_wo_typ, binary_wo_typ) = Utils.map_pair strip_atyp (unary_func, binary_func)                : (term * term);
      val (var1, var2)                  = Utils.map_pair mk_free_variable_of_dummyT (1,2)                    : (term * term);
      val lhs                           = list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var1, var2])]): term;
      val rhs                           = list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var2, var1])]): term;
      val composite_commutativity       = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt
    in
      case composite_commutativity of SOME x => [(Composite_Commutativity, x)] | _ => []      
    end;

fun ctxt_n_consts_to_composite_commutativity (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_domain_args_are_same_typ [binary_func]
    then
      let
        val return_typ = strip_type typ |> snd                 : typ;
        val u_funcs = ctxt_n_domain_typ_to_unary_const ctxt return_typ: terms;
      in
        map (ctxt_n_consts_to_composite_commutativity' ctxt binary_func) u_funcs |> flat
      end
    else []
  | ctxt_n_consts_to_composite_commutativity _ _ = [];


fun ctxt_n_consts_to_swap_unary' (ctxt:Proof.context) (binary_func:term) (unary_func:term) =
    (* f (x, g (y)) = f (g (x), y)*)
     if all_args_are_same_typ [unary_func]
     then
       let
         val (var1, var2)           = Utils.map_pair mk_free_variable_of_dummyT (1,2): term * term;
         val lhs = binary_func $ var1 $ (unary_func $ var2): term;
         val rhs = binary_func $ (unary_func $ var1) $ var2: term;
         val equation = mk_eq (lhs, rhs);
         val property = try (Syntax.check_term ctxt) equation: term option;
       in
         (* TODO: clean-up with monad.*)
         if is_some property then [(Swap_Unary, the property)] else []
       end
     else [];
  
fun ctxt_n_consts_to_swap_unary (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_domain_args_are_same_typ [binary_func]
    then
      let
        val domain_typ = domain_type typ                       : typ;
        val u_funcs = ctxt_n_typ_to_unary_const ctxt domain_typ: terms;
      in
        map (ctxt_n_consts_to_swap_unary' ctxt (strip_atyp binary_func)) (map strip_atyp u_funcs) |> flat
      end
    else []
  | ctxt_n_consts_to_swap_unary _ _ = [];

fun ctxt_n_consts_to_homomorphism_2 (ctxt:Proof.context) (preserved_binary as (Const (_, typ)):term) =
(*f is homomorphism.*)
(*f (g (x, y)) = g (f (x), f (y))*)
    if takes_n_arguments preserved_binary 2 andalso
       all_args_are_same_typ [preserved_binary]
    then
      let
        val unaries                 = ctxt_n_typ_to_unary_const ctxt (strip_type typ |> snd): terms;
        val unaries_wo_typ          = map strip_atyp unaries                                : terms;
        val (var1, var2)            = Utils.map_pair mk_free_variable_of_dummyT (1,2)       : term * term;
        val preserved_binary_wo_typ = strip_atyp preserved_binary                           : term;
        fun get_cnjctr (homomorphism_wo_typ:term): (term option) =
          let
            val lhs       = homomorphism_wo_typ $ list_comb (strip_atyp preserved_binary, [var1, var2])                  : term;
            val rhs       = list_comb (preserved_binary_wo_typ, [homomorphism_wo_typ $ var1, homomorphism_wo_typ $ var2]): term;
            val property = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt                                                   : term option;
          in
            property
          end;
        val homos = map get_cnjctr unaries_wo_typ |> Utils.somes               
      in
        map (fn trm => (Homomorphism_2, trm)) homos
      end
    else []
  | ctxt_n_consts_to_homomorphism_2 _ _ = [];

fun ctxt_n_consts_to_square (ctxt:Proof.context) (func:term) =
(* f (f x) = x *)
    if takes_n_arguments func 1 andalso all_args_are_same_typ [func]
    then 
      let
          val tracing' = if false then tracing else K ();
          val _ = tracing' "===  takes_n_arguments func 1 returned true."
          val var1 = mk_free_variable_of_dummyT 1;
          val _ = tracing' "===  before calling square."
          val func_wo_typ = strip_atyp func;
          val square = 
                Const ("HOL.eq", dummyT )
                  $ (func_wo_typ $ (func_wo_typ $ var1)) 
                  $ var1
                |> (fn xyz => (tracing' "===  before calling Syntax.check_term"; xyz))
                |> (fn xyz => (tracing' "===  we pass this term sto Syntax.check_term:"; xyz))
                |> (fn xyz => (tracing' ("===  " ^ Isabelle_Utils.trm_to_string ctxt xyz); xyz))
                |> TBC_Utils.type_check ctxt:term option;
          val _ = tracing' " :) ctxt_n_consts_to_square almost finished successfully."
      in if is_some square then [(Square, the square)] else []
      end
    else []

val ctxt_n_consts_to_square_root = undefined; (*TODO*)

fun ctxt_n_consts_to_projection (ctxt:Proof.context) (func:term) =
(* f (f x) = f x *)
    if takes_n_arguments func 1 andalso all_args_are_same_typ [func]
    then 
      let
          val var1 = mk_free_variable_of_dummyT 1;
          val func_wo_typ = strip_atyp func;
          val projection = 
                Const ("HOL.eq", dummyT )
                  $ (func_wo_typ $ (func_wo_typ $ var1)) 
                  $ (func_wo_typ $ var1)
                |> TBC_Utils.type_check ctxt:term option;
      in if is_some projection then [(Projection, the projection)] else []
      end
    else []


val ctxt_n_consts_to_swap_constructor = undefined;(*TODO*)

(*property_for_relations*)
fun term_is_relation (Const (_, typ)) = body_type typ = @{typ "HOL.bool"}
  | term_is_relation  _               = false;


fun condition_for_relation (func:term) =
    term_is_relation func andalso
    takes_n_arguments func 2 andalso
    all_domain_args_are_same_typ [func]

fun list_implies (ctxt:Proof.context) (prems: terms, cncl) =
    Logic.list_implies (prems, cncl)
 |> TBC_Utils.type_check ctxt: term option;

fun ctxt_n_consts_to_transitivity (ctxt:Proof.context) (func as (Const _):term): (property * term) list =
(*x R y \<Longrightarrow> y R z \<Longrightarrow> x R z*)
    if condition_for_relation func
    then
      let
        val func_wo_typ        = strip_atyp func                         : term;
        val [var1, var2, var3] = map mk_free_variable_of_dummyT [1, 2, 3]: terms;
        val prem1              = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var2]))   : term;
        val prem2              = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var2, var3]))   : term;
        val cncl               = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var3]))   : term;
        val imply              = list_implies ctxt ([prem1, prem2], cncl): term option;
      in if is_some imply then [(Transitivity, the imply)] else [] end
    else []
  | ctxt_n_consts_to_transitivity _ _ = [];

fun mk_implies (ctxt:Proof.context) (prem, cncl) =
   Logic.mk_implies (prem, cncl)
|> TBC_Utils.type_check ctxt: term option;

fun ctxt_n_consts_to_symmetry (ctxt:Proof.context) (func as (Const _):term): (property * term) list =
(*x R y \<Longrightarrow> y R x*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                                : term;
        val (var1, var2) = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val premise      = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var2]))          : term;
        val conclusion   = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var2, var1]))          : term;
        val imply        = mk_implies ctxt (premise, conclusion)          : term option;
      in if is_some imply then [(Symmetry, the imply)] else []  end
    else []
  | ctxt_n_consts_to_symmetry _ _ = [];

fun ctxt_n_consts_to_connexity (ctxt:Proof.context) (func as (Const _)): (property * term) list =
(*x R y \<or> y R x \<or> (x = y)*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                                : term;
        val (var1, var2) = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val x_R_y        = list_comb (func_wo_typ, [var1, var2])          : term;
        val y_R_x        = list_comb (func_wo_typ, [var2, var1])          : term;
        val x_is_y       = HOLogic.mk_eq (var1, var2)                     : term;
        val disjuncts    = HOLogic.mk_disj (HOLogic.mk_disj (x_R_y, y_R_x), x_is_y)
                        |> TBC_Utils.type_check ctxt                         : term option;
      in if is_some disjuncts then [(Connexity, the disjuncts)] else [] end
    else []
  | ctxt_n_consts_to_connexity _ _ = [];

fun ctxt_n_consts_to_reflexibility (_:Proof.context) (func as (Const _):term) =
(*x R x*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                      : term;
        val fvar         = mk_free_variable_of_dummyT 1         : term;
        val reflex       = list_comb (func_wo_typ, [fvar, fvar]): term;
      in [(Reflexivity, reflex)] end
    else []
  | ctxt_n_consts_to_reflexibility _ _ = [];



(*TODO: name: 
  FIXME: We only start with the binary function. This is strange.*)
fun ctxt_n_const_to_all_conjecture_term (ctxt:Proof.context) (func as (Const _)): (property * term) list =
  ctxt_n_const_to_associativity            ctxt func
@ ctxt_n_const_to_identity                 ctxt func
@ ctxt_n_const_to_commutativity            ctxt func
@ ctxt_n_const_to_idempotent_element       ctxt func
@ ctxt_n_const_to_idempotence              ctxt func
@ ctxt_n_const_to_zero_element             ctxt func
@ ctxt_n_consts_to_distributivity          ctxt func
@ ctxt_n_consts_to_anti_distributivity     ctxt func
@ ctxt_n_consts_to_homomorphism_2          ctxt func 
@ ctxt_n_consts_to_projection              ctxt func
@ ctxt_n_consts_to_square                  ctxt func
@ ctxt_n_consts_to_symmetry                ctxt func
@ ctxt_n_consts_to_reflexibility           ctxt func
@ ctxt_n_consts_to_transitivity            ctxt func
@ ctxt_n_consts_to_connexity               ctxt func
@ ctxt_n_consts_to_swap_unary              ctxt func
@ ctxt_n_consts_to_composite_commutativity ctxt func


| ctxt_n_const_to_all_conjecture_term _ _ = error "ctxt_n_const_to_all_conjecture_term func. This term is not a constant.";

end;
\<close>

strategy TBC_Strategy =
Ors [
  Thens [Auto, IsSolved],
  PThenOne [Smart_Induct, Thens [Auto, IsSolved]],
  Thens [Hammer, IsSolved],
  PThenOne [
    Smart_Induct,
    Ors
      [Thens [
         Repeat (
           Ors [
             Fastforce,
             Hammer,
             Thens [
               Clarsimp,
               IsSolved
             ],
             Thens [
               Subgoal,
               Clarsimp,
               Repeat (
                 Thens [
                   Subgoal,
                   Ors [
                     Thens [Auto, IsSolved],
                     Thens [
                       Smart_Induct,
                       Auto,
                       IsSolved
                     ]
                   ]
                 ]
               ),
               IsSolved
             ]
           ]
         ),
         IsSolved   
       ]
    ]
  ]
]

strategy Quick_Pick = Thens [Quickcheck]

ML\<open> (*This part (the definitions of long_keyword, long_statement, and short_statement) are from
by Pure/Pure.thy in Isabelle/HOL's source code.*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl))
: Token.T list ->
  (bool * Attrib.binding * (xstring * Position.T) list *
   Element.context list * Element.statement)
  *
  Token.T list;

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

structure TBC = Template_Based_Conjecturing;

val zero_timing = {elapsed=Time.zeroTime: Time.time, cpu=Time.zeroTime: Time.time, gc=Time.zeroTime: Time.time};
fun elapsed_time_in_real (time:Timing.timing) = #elapsed time |> Time.toReal: real;

fun prove_by_conjecturing _ descr output_to_external_file =
  Outer_Syntax.local_theory
  (if output_to_external_file
   then @{command_keyword evaluate_property_based_conjecturing}
   else @{command_keyword prove_by_conjecturing})
  ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, _(*elems*), concl: (string, string) Element.stmt) =>
       (fn lthy: local_theory =>
          let
            val stat_w_thy_name = TBC_Eval_Stat.update_theory_name_by_psl_in_stat (Local_Theory.exit_global lthy |> Context.theory_name) TBC_Eval_Stat.default_stat;
            val pst             = Proof.init lthy: Proof.state;
            val original_goal   = TBC_Utils.statement_to_conjecture pst concl: TBC_Utils.pnode;
            val timeout = seconds 3600.0;(*3600.0 for Isaplanner and Prod, 900.0 for TIP15*)

            fun gen_old_stat (strategy) (update_proved) (update_execution_time) (stat_to_be_updated) =
              if output_to_external_file
              then
                let
                  val _ = TBC_Utils.remove_sledgehammer_mash_file output_to_external_file;
                  fun run_pbc_str_w_old_smart_induct _ = TBC_Utils.conjectures_n_pst_to_pst_n_proof_w_limit strategy 1 0 [original_goal] pst |> snd: TBC_Utils.pnodes

                  val (execution_time, original_node_by_old_psls) = Timeout.apply_physical timeout (Timing.timing run_pbc_str_w_old_smart_induct) ()
                      handle Timeout.TIMEOUT _ => (zero_timing, [original_goal]);
                  val original_node_by_old_psl =
                      if   length original_node_by_old_psls = 1
                      then hd original_node_by_old_psls
                      else error "stat_after__pbc_strategy_w_old_smart_induct faild. original_node_by_old_psls's length is not 0!"
                  val proved = #is_final_goal original_node_by_old_psl andalso #proved_wo_assmng_cnjctr original_node_by_old_psl: bool;
                  val stat_w_proved  = update_proved proved stat_to_be_updated;
                  val stat_w_execution_time = update_execution_time (elapsed_time_in_real execution_time) stat_w_proved;
                in
                  stat_w_execution_time
                end
              else stat_to_be_updated;(*dummy value.*)

            (* run TAP_2021 without conjecturing but with the old smart_induct for comparison *)
            val stat_after_tap_2021_w_old_smart_induct =
                gen_old_stat TBC_Utils.TAP21 TBC_Eval_Stat.update_proved_by_tap21_in_stat
                TBC_Eval_Stat.update_execution_time_by_tap21_in_stat stat_w_thy_name;
 
            (* run just TBC_Strategy without conjecturing but with the old smart_induct for comparison *)
            val stat_after_pbc_strategy_w_old_smart_induct =
                gen_old_stat TBC_Utils.TBC_Strategy_W_Old_Smart_Induct
                TBC_Eval_Stat.update_proved_by_pbc_strategy_w_old_smart_induct_in_stat
                TBC_Eval_Stat.update_execution_time_of_pbc_str_w_old_smart_induct_in_stat
                stat_after_tap_2021_w_old_smart_induct;

            (*run TBC*)
            fun measure_execution_time _ =
              let
                val _ = TBC_Utils.remove_sledgehammer_mash_file output_to_external_file;
                val (_, processed_nodes_after_0th_round) = TBC_Utils.conjectures_n_pst_to_pst_n_proof_w_limit TBC_Utils.TBC_Strategy 1 0 [original_goal] pst: Proof.state * TBC_Utils.pnodes;
                val (processed_nodes, stat) =
                  if TBC_Utils.original_goal_is_proved processed_nodes_after_0th_round
                  then
                    let
                      val _ = tracing (TBC_Utils.print_proved_nodes processed_nodes_after_0th_round);
                      val stat_w_proved_by_pbc = TBC_Eval_Stat.update_because_psl_solved_problem stat_after_pbc_strategy_w_old_smart_induct;
                    in
                      (processed_nodes_after_0th_round, stat_w_proved_by_pbc)
                    end
                  else
                    let
                      fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, _)])]) = stmt: string
                        | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in Template_Based_Conjecturing.thy";
                      val cncl_as_trm = Syntax.read_term lthy (stmt_to_stmt_as_string concl);
                      val (relevant_consts, relevant_binary_funcs, relevant_unary_funcs) = TBC_Utils.get_relevant_constants lthy cncl_as_trm;
                      val conjectures_as_tagged_terms = map (TBC.ctxt_n_const_to_all_conjecture_term lthy) (relevant_unary_funcs @ relevant_binary_funcs) |> flat: (TBC.property * term) list
                      val _ = tracing ("\nWe have " ^ Int.toString (length conjectures_as_tagged_terms) ^ " template-based conjectures:");
                      val _ = map (tracing o (fn str => "  " ^ str) o Isabelle_Utils.trm_to_string lthy o snd) conjectures_as_tagged_terms
                      val conjectures = map (TBC.pst_n_property_n_trm_to_pnode pst) conjectures_as_tagged_terms: TBC_Utils.pnodes;
                      val conjectures_w_counterexample  = filter     (fn pnode => #refuted pnode) conjectures: TBC_Utils.pnodes;
                      val conjectures_wo_counterexample = filter_out (fn pnode => #refuted pnode) conjectures: TBC_Utils.pnodes;
                      val _ = tracing ("\nWe have " ^ Int.toString (length conjectures_wo_counterexample) ^ " template-based conjectures w/o counterexamples:");
                      val _ = map (tracing o (fn conj => "  " ^ #lemma_name conj ^ ": " ^ #lemma_stmt conj)) conjectures_wo_counterexample;
                      val (_, processed_pnodes) = TBC_Utils.conjectures_n_pst_to_pst_n_proof_w_limit TBC_Utils.TBC_Strategy 3 1 (conjectures_wo_counterexample @ [original_goal]) pst: (Proof.state * TBC_Utils.pnodes);
                      val _ = TBC_Utils.print_proved_nodes processed_pnodes |> tracing;
                      (*produce stats for evaluation*)
                      val stat_input =
                         {relevant_consts               = relevant_consts              : terms,
                          relevant_unary_funcs          = relevant_unary_funcs         : terms,
                          relevant_binary_funcs         = relevant_binary_funcs        : terms,
                          conjectures_w_counterexample  = conjectures_w_counterexample : TBC_Utils.pnodes,
                          conjectures_wo_counterexample = conjectures_wo_counterexample: TBC_Utils.pnodes,
                          processed_pnodes              = processed_pnodes             : TBC_Utils.pnodes};
                      val stat = TBC_Eval_Stat.update_because_psl_unsolved_problem stat_input stat_w_thy_name: TBC_Eval_Stat.stat;
                    in
                      (processed_pnodes, stat)
                    end;
              in
                (processed_nodes, stat)
              end;

            (*run TBC*)
            val (execution_time, (processed_nds, stat)) = Timeout.apply_physical timeout (Timing.timing measure_execution_time) ()
                handle Timeout.TIMEOUT _ => (zero_timing, ([], stat_w_thy_name));
            val stat_after_pbc = TBC_Eval_Stat.update_execution_time_of_pbc_in_stat (elapsed_time_in_real execution_time) stat;
            val _ = if output_to_external_file
                    then (TBC_Utils.write_proof_script_in_result_file pst (TBC_Utils.print_proved_nodes processed_nds);
                          TBC_Utils.write_one_line_in_result_file pst (TBC_Eval_Stat.print_stat stat_after_pbc))
                    else ();
          in
            lthy
          end)))
     );

in

val _ = prove_by_conjecturing \<^command_keyword>\<open>prove_by_conjecturing\<close> "theorem" false;
val _ = prove_by_conjecturing \<^command_keyword>\<open>evaluate_property_based_conjecturing\<close> "theorem" true;

end;
\<close>

end