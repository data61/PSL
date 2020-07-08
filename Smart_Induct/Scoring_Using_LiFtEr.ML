(*  Title:      Smart_Induct/src/Scoring_Using_LiFtEr.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
structure Scoring_Using_LiFtEr =
struct

(* Utilty functions *)
infix 1 <$> <*>;
fun (m <$> f) = Option.map f m;
fun (f <*> m) = Utils.opt_app f m;

structure LiFtEr_Assertion = Apply_LiFtEr.LiFtEr_Assertion;

type trans_trans = Toplevel.transition -> Toplevel.transition;
open Parser_Combinator;
open LiFtEr_Util;

fun pst_n_ind_mods_to_result_pair (pst:Proof.state) (ind_mod:ind_mods) =
  let
    val ctxt                = Proof.context_of pst: Proof.context;
    val all_assert_pairs    = (Symtab.dest o LiFtEr_Assertion.get) (Context.Proof ctxt) |> map snd: (LiFtEr.assrt * int) list;
    (*val numb_of_all_asserts = length all_assert_pairs: int;*)
    val maximum_point = fold (curry (op +)) (map snd all_assert_pairs) 0: int;
    fun mk_clean_mods (ind_mods:ind_mods) =
      let
        val normalize = Isabelle_Utils.normalize_trm_as_string ctxt;
        val {ons, arbs, rules} = dest_mods ind_mods;
        fun normalize_rule_as_string (rule_as_string:string) =
          let
            val short_cname_option = try (space_explode ".") rule_as_string
                                 <$> Utils.init <$> Utils.last: string option;
            val long_name_option = short_cname_option <$> normalize: string option;
            val clean_rule_name  = long_name_option <$> curry (op ^) <*> SOME ".induct";
            val result           = if is_some clean_rule_name then the clean_rule_name else "";
          in
            result
          end;
         val clean_ons   = map (string_to_induct_on   o normalize                o induct_on_to_string  ) ons  : induct_on   list;
         val clean_arbs  = map (string_to_induct_arb  o normalize                o induct_arb_to_string ) arbs : induct_arb  list;
         val clean_rules = map (string_to_induct_rule o normalize_rule_as_string o induct_rule_to_string) rules: induct_rule list;
      in
        Ind_Mods {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: ind_mods
      end;                                           
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        LiFtEr.eval (pst, assrt, ind_mods): bool;
    val succeeded_assrts         = filter (fn assrt => apply_assrt (fst assrt) pst (mk_clean_mods ind_mod)) all_assert_pairs: (LiFtEr.assrt * int) list;
(*
    val numb_of_succeeded_assrts = length succeeded_assrts: int;
*)
    val score = fold (curry (op +)) (map snd succeeded_assrts) 0: int;
  in
    score: int
  end;

datatype ind_mod_gen = Ion of LiFtEr_Util.induct_on | Iarb of LiFtEr_Util.induct_arb | Irule of LiFtEr_Util.induct_rule;

fun psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.On        str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_On  |> Ion
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Arbitrary str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_Arb |> Iarb
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Rule      str) = LiFtEr_Util.Ind_Rule str |> Irule;

fun psl_ind_mods_to_lifter_ind_mods' (psl_ind_mod::psl_ind_mods) (acc as Ind_Mods {ons, arbs, rules}) = (case psl_ind_mod_to_lifter_ind_mod psl_ind_mod of
      Ion   modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons @ [modi], arbs = arbs,          rules = rules})
    | Iarb  modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs @ [modi], rules = rules})
    | Irule modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs,          rules = rules @ [modi]}))
  | psl_ind_mods_to_lifter_ind_mods' [] acc = acc;

fun psl_ind_mods_to_lifter_ind_mods (psl_ind_mods: Dynamic_Induct.Induct_Seed.modifier list) =
    psl_ind_mods_to_lifter_ind_mods' psl_ind_mods (Ind_Mods {ons = [], arbs = [], rules = []}): LiFtEr_Util.ind_mods;

val on_construct   = Dynamic_Induct.Induct_Seed.On;
val arb_construct  = Dynamic_Induct.Induct_Seed.Arbitrary;
val rule_construct = Dynamic_Induct.Induct_Seed.Rule;

fun lifter_ind_mods_to_psl_ind_mods (Ind_Mods {ons, arbs, rules}) =
    map (on_construct   o dest_print o dest_induct_on) ons @
    map (arb_construct  o dest_print o dest_induct_arb) arbs @
    map (rule_construct o dest_induct_rule) rules;

val smart_induct_cmd =
  Toplevel.keep_proof 
  (Timeout.apply (seconds 1200.0)
  (fn top: Toplevel.state =>
    let
      val _ = tracing "smart_induct started producing combinations of induction arguments.";
      val state                      = Toplevel.proof_of top                                          : Proof.state;
      val psl_modifierss             = Multi_Stage_Screening.pst_to_promising_modss state             : Dynamic_Induct.Induct_Seed.modifier list list;
      val lifter_modifierss          = map psl_ind_mods_to_lifter_ind_mods psl_modifierss             : LiFtEr_Util.ind_mods list;
      fun ind_mods_to_pair ind_mods  = (pst_n_ind_mods_to_result_pair state ind_mods, ind_mods)       : (int * ind_mods);
      val pairs                      = Par_List.map ind_mods_to_pair lifter_modifierss                : (int * ind_mods) list;
      val sorted_pairs               = sort (fn (p1, p2) => Int.compare (fst p1, fst p2)) pairs |> rev: (int * ind_mods) list;
      val best_pairs                 = take 10 sorted_pairs;
      val fst_and_snd = ["1st candidate is ", "2nd candidate is "]
      val third_till_tenth = List.tabulate (11, I) |> map Int.toString |> drop 3 |> map (fn rank => rank ^ "th candidate is ");
      val fst_till_tenth   = fst_and_snd @ third_till_tenth;
      val ctxt                = Proof.context_of state            : Proof.context;
      val all_asserts         = (Symtab.dest o LiFtEr_Assertion.get) (Context.Proof ctxt);
      val numb_of_all_asserts = length all_asserts: int;
      fun ind_mdos_to_sendback ind_mods = lifter_ind_mods_to_psl_ind_mods ind_mods
                                       |> Dynamic_Induct.modifiers_to_str 
                                       |> Active.sendback_markup_properties [Markup.padding_command]: string;
      val maximum_point = fold (curry (op +)) (map (snd o snd) all_asserts) 0: int;
      fun mk_message (i, mods) = ind_mdos_to_sendback mods ^
                                "\n  (* The score is " ^ Int.toString i ^ " out of " ^ Int.toString maximum_point ^ ". *)";
      val best_messages  = map mk_message best_pairs: strings;
      val numb_of_best_messages = length best_messages
      val _                   = tracing ("Try these " ^ Int.toString numb_of_best_messages ^ " most promising inductions!"): unit;
      val best_mess_w_ranks = take numb_of_best_messages fst_till_tenth ~~ best_messages |>  map (op ^);
      val _                = map tracing best_mess_w_ranks;
    in () end)
    );

end;