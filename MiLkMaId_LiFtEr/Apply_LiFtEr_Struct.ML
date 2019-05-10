(*  Title:      PSL/MiLkMaId_LiFtEr/Apply_LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Apply_LiFtEr =
struct 

structure LiFtEr_Assertion = Generic_Data
(
  type T = LiFtEr.assrt Inttab.table;
  val empty  = Inttab.empty : T;
  val extend = I;
  val merge  = Inttab.merge (K true);
);

fun lookup_assert ctxt = (Inttab.lookup o LiFtEr_Assertion.get) (Context.Proof ctxt);
fun update_assert k v  = Inttab.update_new (k, v)
 |> LiFtEr_Assertion.map
 |> Context.theory_map: theory -> theory;

fun get_assrt (ctxt:Proof.context) ass_numb: LiFtEr.assrt =
  let
    val some_assrt = lookup_assert ctxt ass_numb : LiFtEr.assrt option;
    val assertion = Utils.the' (Int.toString ass_numb ^ "?\nDid you really define such an assertion?") some_assrt : LiFtEr.assrt;
  in
    assertion: LiFtEr.assrt
  end;

structure LiFtEr_Ind_Mod = Generic_Data
(
  type T = LiFtEr.ind_mods Inttab.table;
  val empty  = Inttab.empty : T;
  val extend = I;
  val merge  = Inttab.merge (K true);
);

fun lookup_ind_mod ctxt = (Inttab.lookup o LiFtEr_Ind_Mod.get) (Context.Proof ctxt): Inttab.key -> LiFtEr.ind_mods option;
fun update_ind_mod k v  = Inttab.update_new (k, v)
 |> LiFtEr_Ind_Mod.map
 |> Context.theory_map: theory -> theory;

fun get_ind_mod (ctxt:Proof.context) ind_mod_numb: LiFtEr.ind_mods =
  let
    val some_assrt = lookup_ind_mod ctxt ind_mod_numb;
    val assertion = Utils.the' (Int.toString ind_mod_numb ^
                    "?\nDid you really define such a modifier?") some_assrt : LiFtEr.ind_mods;
  in
    assertion: LiFtEr.ind_mods
  end;

structure PC = Parser_Combinator;
structure LU = LiFtEr_Util;
structure UN = Unique_Node;
structure DI = Dynamic_Induct;

val LiFtEr_parser =
  PC.bind (PC.int) (fn assrt_numb:int =>
  PC.bind (PC.int) (fn ind_mod_numb:int =>
  PC.result (assrt_numb, ind_mod_numb))):(int * int) PC.parser;

type trans_trans = Toplevel.transition -> Toplevel.transition;

fun get_trans_trans_gen (should_b_true_or_false:bool) (ass_numb:int, ind_mod_numb:int) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst = Toplevel.proof_of top: Proof.state;
    val ctxt = Toplevel.context_of top: Proof.context;
    val assert  = get_assrt ctxt ass_numb: LiFtEr.assrt;
    val ind_mod = get_ind_mod ctxt ind_mod_numb: LU.ind_mods;
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        LiFtEr.eval (pst, assrt, ind_mods): bool;
    fun run_test (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        if   should_b_true_or_false
        then (tracing "from the then-clause in run_test";apply_assrt assrt pst ind_mods = true)
        else apply_assrt assrt pst ind_mods = false;
    fun show_result (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        if   run_test assrt pst ind_mods
        then tracing "assertion succeed"
        else tracing "assertion failed";
    val _ = tracing "before calling show_result";
    val _ = show_result assert pst ind_mod;
    val _ = tracing "after calling show_result";
  in
    ()
  end)
: trans_trans;

val get_trans_trans_true  = get_trans_trans_gen true : (int * int) -> trans_trans;
val get_trans_trans_false = get_trans_trans_gen false: (int * int) -> trans_trans;

val invocation_parser = PC.token LiFtEr_parser: (int * int) PC.parser;
val token_parser = PSL_Interface.string_parser_to_token_parser invocation_parser: (int * int) Token.parser;
fun get_token_parser_result token = token_parser token |> fst: (int * int);

val get_trans_trans_to_token_parser = PSL_Interface.parser_to_trans_trans_parser invocation_parser;

val token_parser_true  = get_trans_trans_to_token_parser get_trans_trans_true : trans_trans Token.parser;
val token_parser_false = get_trans_trans_to_token_parser get_trans_trans_false: trans_trans Token.parser;

fun activate _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword test_LiFtEr_true}
        "TODO" token_parser_true;
    
    val _ =
      Outer_Syntax.command @{command_keyword test_LiFtEr_false}
        "TODO" token_parser_false;
  in () end;

end;