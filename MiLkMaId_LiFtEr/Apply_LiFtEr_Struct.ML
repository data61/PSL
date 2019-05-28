(*  Title:      PSL/MiLkMaId_LiFtEr/Apply_LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Apply_LiFtEr =
struct 

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
    val some_ind_mods = lookup_ind_mod ctxt ind_mod_name;
    val assertion = Utils.the' (ind_mod_name ^
                    "?\nDid you really define such a modifier?") some_ind_mods : LiFtEr.ind_mods;
  in
    assertion: LiFtEr.ind_mods
  end;

structure PC = Parser_Combinator;
structure LU = LiFtEr_Util;
structure UN = Unique_Node;
structure DI = Dynamic_Induct;

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

end;