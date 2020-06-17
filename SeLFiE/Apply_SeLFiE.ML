(*  Title:      PSL/SeLFiE/src/Interface/Apply_SeLFiE.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature APPLY_SELFIE =
sig

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

structure SeLFiE_Assertion = Generic_Data
(
  type T     = ESS.assert Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup_assert ctxt = (Symtab.lookup o SeLFiE_Assertion.get) (Context.Proof ctxt);
fun update_assert k v  = Symtab.update_new (k, v)
 |> SeLFiE_Assertion.map
 |> Context.theory_map: theory -> theory;

fun get_assrt (ctxt:Proof.context) (assert_name:string): ESS.assert =
  let
    val some_assrt = lookup_assert ctxt assert_name : ESS.assert option;
    val assertion = Utils.the' (assert_name ^ "?\nDid you really define such an assertion?") some_assrt : ESS.assert;
  in
    assertion: ESS.assert
  end;

local

open PC;
open SU;

type trans_trans = Toplevel.transition -> Toplevel.transition;

in

fun get_trans_trans_gen (should_b_true_or_false:bool) (assert_name:string, ind_mod(*:ind_mods(*ind_mod_name:string*)*)) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst     = Toplevel.proof_of top        : Proof.state;
    val ctxt    = Toplevel.context_of top      : Proof.context;
    val assert  = get_assrt ctxt assert_name   : ESS.assert;
    fun mk_clean_mods (ind_mods:SU.induct_arguments) =
      let
        val normalize = IU.normalize_trm_as_string ctxt;
        val {ons, arbs, rules} = SU.dest_induct_arguments ind_mods;
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
         val clean_ons   = (map normalize               ) ons  : strings;
         val clean_arbs  = (map normalize               ) arbs : strings;
         val clean_rules = (map normalize_rule_as_string) rules: strings;
      in
        SU.Induct_Arguments {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: SU.induct_arguments
      end;
    fun bool_to_ES_assert (true :bool) = ESS.True
      | bool_to_ES_assert (false:bool) = ESS.False;
    fun run_test (assrt:ESS.assert) (pst:Proof.state) (ind_mods:SU.induct_arguments) =
        ESS.eval pst (mk_clean_mods ind_mods) assrt = bool_to_ES_assert should_b_true_or_false;
    val _ = @{assert} (
            let
              val result = run_test assert pst (mk_clean_mods ind_mod)
              val _      = tracing ("Assertion " ^ (if result then "succeeded." else "failed."));
            in result end);
  in
    ()
  end)
: trans_trans;

val get_trans_trans_true  = get_trans_trans_gen true
val get_trans_trans_false = get_trans_trans_gen false

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

fun parse_ons   ()   = parse_list (Seq.list_of) "on"   plus result []: string list parser;
fun parse_arbs  ()   = parse_list (Seq.list_of) "arb"  plus result []: string list parser;
fun parse_rules ()   = parse_list (Seq.list_of) "rule" plus result []: string list parser;

fun parse_inside_bracket () =
  token
  (parse_ons   () |> token >>= (fn ons   =>
   (string "," |> token)   >>= (fn _     =>
   parse_arbs  () |> token >>= (fn arbs  =>
   (string "," |> token)   >>= (fn _     =>
   parse_rules () |> token >>= (fn rules =>
   result
    (SU.Induct_Arguments {ons = ons, arbs  = arbs, rules = rules})))))));

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

val get_trans_trans_to_token_parser = PSL_Interface.parser_to_trans_trans_parser invocation_parser;

val token_parser_true  = get_trans_trans_to_token_parser get_trans_trans_true  : trans_trans Token.parser;

val token_parser_false = get_trans_trans_to_token_parser get_trans_trans_false : trans_trans Token.parser;

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
  in () end;

end;

end;

end;