(*  Title:      PSL/SeLFiE/src/Interface/Apply_SeLFiE.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature APPLY_SELFIE =
sig

datatype heuristic_typ = Induction_Heuristic | Generalization_Heuristic | Test_Heuristic;

val score_n_induct_argss_n_proof_state_to_best_pairs:
    int ->
      (int * SeLFiE_Util.induct_arguments) list ->
        (int * SeLFiE_Util.induct_arguments) list ->
          heuristic_typ ->
            int ->
              Proof.state ->
                Outer_Path_To_Unode.path_to_unode_table ->
                  {modifiers: SeLFiE_Util.induct_arguments,
                   score: int}
                  list
                  *
                  int;

val update_assert : Inttab.key -> Eval_Syntactic_Sugar.assert -> theory -> theory;
val update_ind_mod: Inttab.key -> Eval_Syntactic_Sugar.assert -> theory -> theory;
val get_assert    : Proof.context -> Inttab.key -> Eval_Syntactic_Sugar.assert -> theory -> theory;
val get_ind_mod   : Proof.context -> Inttab.key -> Eval_Syntactic_Sugar.assert -> theory -> theory;
val activate      : unit -> unit;

end;

structure Apply_SeLFiE =
struct

structure PC  = Parser_Combinator;
structure SU  = SeLFiE_Util;
structure IU  = Isabelle_Utils;
structure ES  = Eval_Surface;
structure ESS = Eval_Syntactic_Sugar;
structure QD  = Quantifier_Domain;

datatype heuristic_typ = Induction_Heuristic | Generalization_Heuristic | Test_Heuristic;

fun heuristic_typ_ord (Induction_Heuristic,      Induction_Heuristic     ) = EQUAL
  | heuristic_typ_ord (Induction_Heuristic,      _                       ) = LESS
  | heuristic_typ_ord (Generalization_Heuristic, Generalization_Heuristic) = EQUAL
  | heuristic_typ_ord (Generalization_Heuristic, Induction_Heuristic     ) = GREATER
  | heuristic_typ_ord (Generalization_Heuristic, Test_Heuristic          ) = LESS
  | heuristic_typ_ord (Test_Heuristic,           Test_Heuristic          ) = EQUAL
  | heuristic_typ_ord (_,                        _                       ) = GREATER;

val str_n_heutyp_ord = prod_ord heuristic_typ_ord fast_string_ord;

structure Strng_N_HeuTyp_Tab = Table(type key = (heuristic_typ * string) val ord = str_n_heutyp_ord);

(*We assume that no induction heuristic can have a name taken by some generalization heuristic and vice verse.*)

structure SeLFiE_Assertion = Generic_Data
(
  type T     = (ESS.assert * real) Strng_N_HeuTyp_Tab.table;
  val empty  = Strng_N_HeuTyp_Tab.empty : T;
  val extend = I;
  val merge  = Strng_N_HeuTyp_Tab.merge (K true);
);

fun lookup_assert ctxt = (Strng_N_HeuTyp_Tab.lookup o SeLFiE_Assertion.get) (Context.Proof ctxt);

fun get_assrt (ctxt:Proof.context) (assert_name:string): (ESS.assert * real) =
  let
    val some_ind_heuristic  = lookup_assert ctxt (Induction_Heuristic,      assert_name) : (ESS.assert * real) option;
    val some_gen_heuristic  = lookup_assert ctxt (Generalization_Heuristic, assert_name) : (ESS.assert * real) option;
    val some_test_heuristic = lookup_assert ctxt (Test_Heuristic,           assert_name) : (ESS.assert * real) option;
    val heuristic =
           if is_some some_ind_heuristic  andalso not (ESS.Dummy = (fst (the some_ind_heuristic ))) then the some_ind_heuristic
      else if is_some some_gen_heuristic  andalso not (ESS.Dummy = (fst (the some_gen_heuristic ))) then the some_gen_heuristic
      else if is_some some_test_heuristic andalso not (ESS.Dummy = (fst (the some_test_heuristic))) then the some_test_heuristic
      else error (assert_name ^ "?\nDid you really define such an assertion?");
  in
    heuristic: (ESS.assert * real)
  end;

fun update_assert k v  = Strng_N_HeuTyp_Tab.update_new (k, v)
 |> SeLFiE_Assertion.map
 |> Context.theory_map: theory -> theory;

local

open PC;
open SU;

type trans_trans = Toplevel.transition -> Toplevel.transition;

in

fun mk_clean_mods (ctxt:Proof.context) (ind_mods:SU.induct_arguments) =
  let
    val normalize = IU.normalize_trm_as_string ctxt;
    val {ons, arbs, rules} = SU.dest_induct_arguments ind_mods;
    fun normalize_rule_as_string (rule_name:string) =
      let
        val short_cname_option = try (space_explode ".") rule_name
                             <$> Utils.init 
                             <$> String.concatWith "."(*<$> Utils.last*): string option;
        val long_name_option = short_cname_option <$> normalize: string option;
        infix <*>;
        fun (f <*> m) = Utils.opt_app f m;
        val clean_rule_name  = long_name_option <$> curry (op ^) <*> SOME ".induct";
        val result           = if is_some clean_rule_name then the clean_rule_name else "";
      in
        result
      end;
     fun normalize_rule_or_set (SU.Ind_Rule rule_name)  = SU.Ind_Rule (normalize_rule_as_string rule_name)
       | normalize_rule_or_set (SU.Ind_Set  set_name )  = SU.Ind_Set   set_name (*set_name does not have to be normalised. It requires the long name of a constant.*)
       | normalize_rule_or_set (SU.Hand_Rule rule_name) = SU.Hand_Rule rule_name(*I do not see any necessity to normalize hand rules.*)
     val clean_ons   = (map normalize            ) ons  : strings;
     val clean_arbs  = (map normalize            ) arbs : strings;
     val clean_rules = (map normalize_rule_or_set) rules: SU.rule_or_set list;
  in
    SU.Induct_Arguments {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: SU.induct_arguments
  end;

fun bool_to_ES_assert (true :bool) = ESS.True
  | bool_to_ES_assert (false:bool) = ESS.False;

fun run_assertion (pst:Proof.state) (ind_mods:SU.induct_arguments) (assrt:ESS.assert) =
  let
    val thm                       = Isabelle_Utils.proof_state_to_thm pst                                     : thm;
    val thm_term                  = Thm.prop_of thm                                                           : term;
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst thm_term         : Outer_Path_To_Unode.path_to_unode_table;
    val gen_path_table            = Gen_Path.Outer_Path_To_Unode outer_path_to_unode_table                    : Gen_Path.gen_path_to_unode_table;
    val outer_domains             = QD.inout_pst_n_trm_n_induct_args_to_domains QD.Out gen_path_table ind_mods: QD.domains;
  in
    ESS.eval pst outer_path_to_unode_table outer_domains ind_mods assrt = bool_to_ES_assert true
  end;

fun get_trans_trans_gen (should_b_true_or_false:bool) (assert_name:string, ind_mod) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst        = Toplevel.proof_of top     : Proof.state;
    val ctxt       = Toplevel.context_of top   : Proof.context;
    val (assrt, _) = get_assrt ctxt assert_name: (ESS.assert * real);
    val clean_mods = mk_clean_mods ctxt ind_mod: SU.induct_arguments;
    val _ = @{assert} (
            let
              val result = run_assertion pst clean_mods assrt = should_b_true_or_false;
              val _      = tracing ("Assertion " ^ (if result then "succeeded." else "failed."));
            in result end);
  in
    ()
  end): trans_trans;

val get_trans_trans_true  = get_trans_trans_gen true;
val get_trans_trans_false = get_trans_trans_gen false;

fun get_trans_trans_for_all_asserts_gen (heuristic_typ:heuristic_typ) (ind_mod: SU.induct_arguments) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst         = Toplevel.proof_of top     : Proof.state;
    val ctxt        = Toplevel.context_of top   : Proof.context;
    val key_n_vals  = (Strng_N_HeuTyp_Tab.dest o SeLFiE_Assertion.get) (Context.Proof ctxt)
                    : ((heuristic_typ * string) * (ESS.assert * real)) list;
    val key_n_vals' = filter (fn ((typ,_),(_,_)) => typ = heuristic_typ) key_n_vals
                    : ((heuristic_typ * string) * (ESS.assert * real)) list;
    val ass_names   = map (snd o fst) key_n_vals' |> distinct (op =): string list;
    val ass_n_point = map (fn ass_name => (ass_name, get_assrt ctxt ass_name)) ass_names
                    : (string * (ESS.assert * real)) list;
    val clean_mods = mk_clean_mods ctxt ind_mod: SU.induct_arguments;
    fun prnt_one_result (ass_name, (ass, _)) =
        let
          val result = run_assertion pst clean_mods ass: bool;
          val _      = tracing ("Assertion " ^ ass_name ^ (if result then " succeeded." else " failed."));
        in result end;
    val _ = map prnt_one_result ass_n_point;
  in
    ()
  end): trans_trans;

fun score_n_induct_argss_n_proof_state_to_best_pairs
  (old_maximum_point:real)
  (score_n_induct_argss   : (real * SU.induct_arguments) list)
  (score_n_induct_wo_argss: (real * SU.induct_arguments) list)
  (heuristic_typ          : heuristic_typ)
  (take_top_n             : int)
  (pst                    : Proof.state)
  (outer_path_to_unode_table: Outer_Path_To_Unode.path_to_unode_table) =
  let
    val ctxt           = Proof.context_of pst: Proof.context;
    val assertions'    = (Strng_N_HeuTyp_Tab.dest o SeLFiE_Assertion.get) (Context.Proof ctxt)
                       : ((heuristic_typ * string) * (ESS.assert * real)) list;
    val assertions     = map (fn ((htyp, ass_name), (ass, point)) => (htyp, {name = ass_name, assertion = ass, point = point})) assertions';
    fun is_same_heuristic_typ (typ:heuristic_typ) (htyp, {assertion,...}) = if typ = htyp andalso not (assertion = ESS.Dummy) then true else false;
    val input          = (filter (is_same_heuristic_typ heuristic_typ) assertions) |> map snd
                       : {assertion: Eval_Syntactic_Sugar.assert, name: string, point: real} list;
    val maximum_point  = fold (curry (op +)) (map #point input) 0.0 + old_maximum_point            : real;
    val outer_path_to_unode_table_as_gen = Gen_Path.Outer_Path_To_Unode outer_path_to_unode_table: Gen_Path.gen_path_to_unode_table; 
    fun ind_mod_to_score (ind_mod:SU.induct_arguments) =
      let
        val clean_mods          = mk_clean_mods ctxt ind_mod                                                                     : SU.induct_arguments;
        val outer_domains       = QD.inout_pst_n_trm_n_induct_args_to_domains QD.Out outer_path_to_unode_table_as_gen clean_mods : QD.domains;
        fun eval_to_true assert = ESS.eval pst outer_path_to_unode_table outer_domains clean_mods assert = bool_to_ES_assert true: bool;
        val success_scores      = filter (fn {assertion,...} => eval_to_true assertion) input |> map #point                      : real list;
        val score               = fold (curry (op +)) success_scores 0.0                                                         : real;
      in score end;
    fun get_promising_ind_mods_n_result (Induction_Heuristic     : heuristic_typ) = Screening.proof_state_to_promising_induct_argumentss_wo_arbs_n_resultss pst                                        : (real * SU.induct_arguments) list
      | get_promising_ind_mods_n_result (Generalization_Heuristic: heuristic_typ) = Screening.induct_argumentss_n_proof_state_to_promising_induct_argumentss_w_arbs_n_resultss score_n_induct_argss pst: (real * SU.induct_arguments) list
      | get_promising_ind_mods_n_result _ = error "failed in Apply_SeLFiE.ML";
    val promising_ind_mods_n_result = get_promising_ind_mods_n_result heuristic_typ: (real * SU.induct_arguments) list;
    fun get_ind_mod_n_scores promising_ind_mods_n_result =
        Par_List.map
          (fn (old_score, ind_mod) => ((*tracing ("checking " ^ SeLFiE_Util.induct_arguments_to_string ind_mod);*)
              let
                val new_score_opt = Option.map (op +) (Utils.mk_option_pair (SOME old_score, try ind_mod_to_score ind_mod)): real option;
              in
                if is_some new_score_opt then SOME {score = the new_score_opt, modifiers = ind_mod} else NONE
              end))
          promising_ind_mods_n_result
    val ind_mod_n_scores_opt = try (Timeout.apply (seconds 3000.0) get_ind_mod_n_scores) promising_ind_mods_n_result
                             |> Option.map Utils.somes
                             : {modifiers: SeLFiE_Util.induct_arguments, score: real} list option;
    fun mk_record_wo_arb  (score:real, ind_args:SU.induct_arguments) = {modifiers = ind_args, score = score};
    fun mk_records_wo_arb (pairs:(real * SU.induct_arguments) list) = map mk_record_wo_arb pairs;
    val ind_mod_n_scores     = Option.getOpt (ind_mod_n_scores_opt, mk_records_wo_arb score_n_induct_wo_argss);
    val sorted_pairs         = sort (fn (p1, p2) => Real.compare (#score p1, #score p2)) ind_mod_n_scores |> rev
                             : {modifiers: SeLFiE_Util.induct_arguments, score: real} list;
    val best_pairs           = take take_top_n sorted_pairs;
  in
    (best_pairs, maximum_point)
  end;

val semantic_induct_cmd =
  Toplevel.keep_proof
  (Timeout.apply (seconds 3000.0)
  (fn top: Toplevel.state =>
  let
(*    val _                  = tracing "smart_induct started producing combinations of induction arguments.";*)
    val fst_and_snd        = ["1st candidate is ", "2nd candidate is "]
    val third_till_tenth   = List.tabulate (11, I) |> map Int.toString |> drop 3 |> map (fn rank => rank ^ "th candidate is ");
    val fst_till_tenth     = fst_and_snd @ third_till_tenth;
    fun ind_args_to_sendb ind_args = SU.induct_arguments_to_string ind_args
                                  |> (fn induct => "apply " ^ induct)
                                  |> Active.sendback_markup_properties [Markup.padding_command]      : string;
    val pst                       = Toplevel.proof_of top                                            : Proof.state;
    val thm                       = Isabelle_Utils.proof_state_to_thm pst                            : thm;
    val thm_term                  = Thm.prop_of thm                                                  : term;
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst thm_term: Outer_Path_To_Unode.path_to_unode_table;
    val (ind_best_records, ind_max_point) = score_n_induct_argss_n_proof_state_to_best_pairs 0.0 [] [] Induction_Heuristic 5 pst outer_path_to_unode_table;
    fun record_to_pair {score, modifiers,...} = (score, modifiers);
    val best_pairs            = Par_List.map record_to_pair ind_best_records
                              : (real * SU.induct_arguments) list;
    val arb_pairs             = Smart_Construction.proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs pst (Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst) best_pairs
                              :  (real * SU.induct_arguments) list;
    val (arb_best_records, arb_max_point) = score_n_induct_argss_n_proof_state_to_best_pairs ind_max_point arb_pairs best_pairs Generalization_Heuristic 10 pst outer_path_to_unode_table;
    fun mk_arb_message record = ind_args_to_sendb (#modifiers record) ^
                             "\n  (* The score is " ^ Real.toString (#score record) ^ " out of " ^ Real.toString arb_max_point ^ ". *)";
    val best_arb_messages     = map mk_arb_message arb_best_records: strings;
    val best_arb_mssg_w_ranks = take (length best_arb_messages) fst_till_tenth ~~ best_arb_messages |> map (op ^);
(*
    val _                     = tracing "\n\nTry these promising inductions with generalization!";
*)
    val _                     = map tracing best_arb_mssg_w_ranks;
  in
    ()
  end)
  )
: trans_trans;

local

infix plus;

val non_quote_symbol = sat (fn x => not (x = "\""))
  : symbols -> (string * symbols) Seq.seq;

fun non_quotation_word' _ =
  let
    val neWord = non_quote_symbol >>= (fn x =>
                 non_quotation_word' () >>= (fn xs =>
                 result (x ^ xs))):  symbols -> (string * symbols) Seq.seq;
  in
    neWord plus result ""
 end: string parser;

val non_quotation_word = non_quotation_word' () plus result "": string Parser_Combinator.parser;

val parse_quotation =
bracket
 (string "\"" |> token)
 (non_quotation_word |> token)
 (string "\"" |> token):  string Parser_Combinator.parser;

fun parse_list' _ : string Seq.seq parser =
  bracket
    (string "[" |> token)
    (sepby  (token (parse_quotation) |> token, (string "," |> token)) |> token)
    (string "]" |> token) |> token;

fun parse_list constr name : string list parser =
  token
  (string name |> token     >>= (fn delayer =>
   parse_list'  delayer >>= (fn strategies : string Seq.seq =>
   strategies |> constr |> result)));

fun parse_ons   () = parse_list (Seq.list_of) "on"   plus result []: string list parser;
fun parse_arbs  () = parse_list (Seq.list_of) "arb"  plus result []: string list parser;
fun parse_rules () = parse_list (Seq.list_of) "rule" plus result []: string list parser;
fun parse_sets  () = parse_list (Seq.list_of) "set"  plus result []: string list parser;

fun parse_inside_bracket () =
  token
  (parse_ons   () |> token >>= (fn ons   =>
   (string "," |> token)   >>= (fn _     =>
   parse_arbs  () |> token >>= (fn arbs  =>
   (string "," |> token)   >>= (fn _     =>
   (parse_rules () |> token >>= (fn rules =>
    result
     (SU.Induct_Arguments {ons = ons, arbs  = arbs, rules = map SU.Ind_Rule rules}))) plus
   (parse_sets () |> token >>= (fn sets =>
    result
     (SU.Induct_Arguments {ons = ons, arbs  = arbs, rules = map SU.Ind_Set sets})))

   )))));

fun parse_bracket () =
  bracket
    (string "["              |> token)
    (parse_inside_bracket () |> token)
    (string "]"              |> token) |> token;

val SeLFiE_parser =
  PC.bind (PC.token PC.word) (fn assrt_name:string   =>
  PC.bind (parse_bracket ()) (fn ind_mods:SU.induct_arguments =>
  PC.result (assrt_name, ind_mods)));

val invocation_parser = PC.token SeLFiE_parser: (string * SeLFiE_Util.induct_arguments) PC.parser;

val get_trans_trans_to_token_parser = Parser_Combinator.parser_to_trans_trans_parser invocation_parser
 : (string * SU.induct_arguments -> trans_trans) -> trans_trans Token.parser;

val token_parser_true  = get_trans_trans_to_token_parser get_trans_trans_true: trans_trans Token.parser;

val token_parser_false = get_trans_trans_to_token_parser get_trans_trans_false: trans_trans Token.parser;

(*for check_all_SeLFiE*)
val check_all_SeLFiE_parser =
  PC.bind (parse_bracket ()) (fn ind_mods:SU.induct_arguments =>
  PC.result ind_mods)
: SU.induct_arguments PC.parser;

val get_trans_trans_to_token_parser_for_check_all = Parser_Combinator.parser_to_trans_trans_parser check_all_SeLFiE_parser
 : (SU.induct_arguments -> trans_trans) -> trans_trans Token.parser;

val token_parser_check_all_induction_heuristic =
    get_trans_trans_to_token_parser_for_check_all (get_trans_trans_for_all_asserts_gen Induction_Heuristic)
  : trans_trans Token.parser;

val token_parser_check_all_generalization_heuristic =
    get_trans_trans_to_token_parser_for_check_all (get_trans_trans_for_all_asserts_gen Generalization_Heuristic)
  : trans_trans Token.parser;

in

fun activate _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword assert_SeLFiE_true}
        ("check if the given combination of arguments to the induct method is compatible with " ^
         "the heuristic implemented by the SeLFiE assertion.")
        token_parser_true;

    val _ =
      Outer_Syntax.command @{command_keyword assert_SeLFiE_false}
        ("check if the given combination of arguments to the induct method is compatible with " ^
         "the heuristic implemented by the SeLFiE assertion.")
        token_parser_false;

    val _ =
     Outer_Syntax.command @{command_keyword sem_ind} "recommend which method to use." 
       (Scan.succeed semantic_induct_cmd); 

    val _ =
     Outer_Syntax.command @{command_keyword all_induction_heuristic} "check all induction heuristics."
       token_parser_check_all_induction_heuristic;

    val _ =
     Outer_Syntax.command @{command_keyword all_generalization_heuristic} "check all generalization heuristics."
       token_parser_check_all_generalization_heuristic;

  in () end;

end;

end;

end;