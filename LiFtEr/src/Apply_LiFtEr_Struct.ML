(*  Title:      PSL/LiFtEr/src/Apply_LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Apply_LiFtEr =
struct

structure PC = Parser_Combinator;
structure LU = LiFtEr_Util;
structure UN = Unique_Node;
structure DI = Dynamic_Induct;
structure IU = Isabelle_Utils;

structure LiFtEr_Assertion = Generic_Data
(
  type T = LiFtEr.assrt Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup_assert ctxt = (Symtab.lookup o LiFtEr_Assertion.get) (Context.Proof ctxt);
fun update_assert k v  = Symtab.update_new (k, v)
 |> LiFtEr_Assertion.map
 |> Context.theory_map: theory -> theory;

fun get_assrt (ctxt:Proof.context) (assert_name:string): LiFtEr.assrt =
  let
    val some_assrt = lookup_assert ctxt assert_name : LiFtEr.assrt option;
    val assertion = Utils.the' (assert_name ^ "?\nDid you really define such an assertion?") some_assrt : LiFtEr.assrt;
  in
    assertion: LiFtEr.assrt
  end;

structure LiFtEr_Ind_Mod = Generic_Data
(
  type T = LiFtEr.ind_mods Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup_ind_mod ctxt = (Symtab.lookup o LiFtEr_Ind_Mod.get) (Context.Proof ctxt): Symtab.key -> LiFtEr.ind_mods option;
fun update_ind_mod k v  = Symtab.update_new (k, v)
 |> LiFtEr_Ind_Mod.map
 |> Context.theory_map: theory -> theory;

fun get_ind_mod (ctxt:Proof.context) (ind_mod_name:string): LiFtEr.ind_mods =
  let
    val some_ind_mods = lookup_ind_mod ctxt ind_mod_name: LiFtEr.ind_mods option;
    fun mk_clean_mods (ind_mods:LU.ind_mods) =
      let
        val normalize = IU.normalize_trm_as_string ctxt;
        val {ons, arbs, rules} = LU.dest_mods ind_mods;
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
         val clean_ons   = map (LU.string_to_induct_on   o normalize                o LU.induct_on_to_string  ) ons  : LU.induct_on   list;
         val clean_arbs  = map (LU.string_to_induct_arb  o normalize                o LU.induct_arb_to_string ) arbs : LU.induct_arb  list;
         val clean_rules = map (LU.string_to_induct_rule o normalize_rule_as_string o LU.induct_rule_to_string) rules: LU.induct_rule list;
      in
        LU.Ind_Mods {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: LU.ind_mods
      end;
    val clean_mods_option = some_ind_mods <$> mk_clean_mods: LU.ind_mods option;
    val clean_mods        = Utils.the' (ind_mod_name ^ "?\nDid you really define such a modifier?") clean_mods_option : LU.ind_mods;
  in
    clean_mods
  end;

val LiFtEr_parser =
  PC.bind (PC.token PC.word) (fn assrt_name:string =>
  PC.bind (PC.token PC.word) (fn ind_mod_name:string =>
  PC.result (assrt_name, ind_mod_name))):(string * string) PC.parser;

type trans_trans = Toplevel.transition -> Toplevel.transition;

fun get_trans_trans_gen (should_b_true_or_false:bool) (assert_name:string, ind_mod_name:string) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst     = Toplevel.proof_of top        : Proof.state;
    val ctxt    = Toplevel.context_of top      : Proof.context;                          
    val assert  = get_assrt ctxt assert_name   : LiFtEr.assrt;
    val ind_mod = get_ind_mod ctxt ind_mod_name: LU.ind_mods;
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        LiFtEr.eval (pst, assrt, ind_mods): bool;
    fun run_test (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        apply_assrt assrt pst ind_mods = should_b_true_or_false
    val _ = @{assert} (
            let
              val result = run_test assert pst ind_mod
              val _      = tracing ("Assertion " ^ (if result then "succeeded." else "failed."));
            in result end);    
  in
    ()
  end)
: trans_trans;

val get_trans_trans_true  = get_trans_trans_gen true : (string * string) -> trans_trans;
val get_trans_trans_false = get_trans_trans_gen false: (string * string) -> trans_trans;

val invocation_parser = PC.token LiFtEr_parser: (string * string) PC.parser;
val token_parser      = PSL_Interface.string_parser_to_token_parser invocation_parser: (string * string) Token.parser;
fun get_token_parser_result token = token_parser token |> fst: (string * string);

val get_trans_trans_to_token_parser = PSL_Interface.parser_to_trans_trans_parser invocation_parser;

val token_parser_true  = get_trans_trans_to_token_parser get_trans_trans_true : trans_trans Token.parser;
val token_parser_false = get_trans_trans_to_token_parser get_trans_trans_false: trans_trans Token.parser;

fun activate _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword assert_LiFtEr_true}
        "TODO" token_parser_true;
    
    val _ =
      Outer_Syntax.command @{command_keyword assert_LiFtEr_false}
        "TODO" token_parser_false;
  in () end;

(*TODO: refactor the following.*)

local

open PC;
open LU;

in

fun get_trans_trans_gen (should_b_true_or_false:bool) (assert_name:string, ind_mod(*:ind_mods(*ind_mod_name:string*)*)) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst     = Toplevel.proof_of top        : Proof.state;
    val ctxt    = Toplevel.context_of top      : Proof.context;                          
    val assert  = get_assrt ctxt assert_name   : LiFtEr.assrt;
    fun mk_clean_mods (ind_mods:LU.ind_mods) =
      let
        val normalize = IU.normalize_trm_as_string ctxt;
        val {ons, arbs, rules} = LU.dest_mods ind_mods;
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
         val clean_ons   = map (LU.string_to_induct_on   o normalize                o LU.induct_on_to_string  ) ons  : LU.induct_on   list;
         val clean_arbs  = map (LU.string_to_induct_arb  o normalize                o LU.induct_arb_to_string ) arbs : LU.induct_arb  list;
         val clean_rules = map (LU.string_to_induct_rule o normalize_rule_as_string o LU.induct_rule_to_string) rules: LU.induct_rule list;
      in
        LU.Ind_Mods {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: LU.ind_mods
      end;
(*
    val ind_mod = get_ind_mod ctxt ind_mod_name: LU.ind_mods;
*)
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        LiFtEr.eval (pst, assrt, ind_mods): bool;
    fun run_test (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        apply_assrt assrt pst ind_mods = should_b_true_or_false
(*
val ind_mod = Ind_Mods {ons = [], arbs = [], rules = []}
*)
    val _ = @{assert} (
            let
              val result = run_test assert pst (mk_clean_mods ind_mod)
              val _      = tracing ("Assertion " ^ (if result then "succeeded." else "failed."));
            in result end);    
  in
    ()
  end)
: trans_trans;

val get_trans_trans_true  = get_trans_trans_gen true (*: (string * ind_mods) -> trans_trans;*)
(*
val get_trans_trans_false = get_trans_trans_gen false: (string * ind_mods) -> trans_trans;
*)

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
   strategies |> constr |> result)))

fun parse_ons   ()   = parse_list (Seq.list_of) "on"   plus result []: string list parser;
fun parse_arbs  ()   = parse_list (Seq.list_of) "arb"  plus result []: string list parser;
fun parse_rules ()   = parse_list (Seq.list_of) "rule" plus result []: string list parser;

fun lifter_parser' () =
  token
  (parse_ons   () |> token >>= (fn ons     =>
   (string "," |> token)   >>= (fn _       =>
   parse_arbs  () |> token >>= (fn arbs    =>
   (string "," |> token)   >>= (fn _       =>
   parse_rules () |> token >>= (fn rules   =>
   result
    (Ind_Mods {
       ons   = map string_to_induct_on   ons,
       arbs  = map string_to_induct_arb  arbs,
       rules = map string_to_induct_rule rules})))))));

fun lifter_parser () (*:  LiFtEr_Util.ind_mods parser*) =
  bracket
    (string "["        |> token)

(*    (string "test" |> token)*)
    (lifter_parser' () |> token)
    (string "]"        |> token) |> token;

val LiFtEr_parser2 =
  PC.bind (PC.token PC.word) (fn assrt_name:string   =>
  PC.bind (lifter_parser ()) (fn ind_mods  (*:ind_mods*) =>
  PC.result (assrt_name, ind_mods))) 
(*:(string * ind_mods) PC.parser;
*)

val invocation_parser = PC.token LiFtEr_parser2 (*: (string * ind_mods) PC.parser;*)
val token_parser      = PSL_Interface.string_parser_to_token_parser invocation_parser(*: (string * ind_mods) Token.parser;*)
fun get_token_parser_result token = token_parser token |> fst(*: (string * ind_mods);*)

val get_trans_trans_to_token_parser = PSL_Interface.parser_to_trans_trans_parser invocation_parser;

val token_parser_true  = get_trans_trans_to_token_parser get_trans_trans_true : trans_trans Token.parser;

fun activate2 _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword assert_LiFtEr}
        "TODO" token_parser_true;
  in () end;

end;

val _ = Parse.ML_source;
type dasdf = Input.source parser;
(*abstype source = Source of {delimited: bool, text: Symbol_Pos.text, range: Position.range}*)
type text_of = Input.source -> Symbol_Pos.text;

end;