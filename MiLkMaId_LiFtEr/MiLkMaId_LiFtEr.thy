(*  Title:      PSL/MiLkMaId_LiFtEr/MiLkMaId_LiFtEr.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MiLkMaId: Machine Learning Mathematical Induction for Isabelle/HOL, and
LiFtEr:   Logical Feature Extractor.
*)
theory MiLkMaId_LiFtEr
  imports "../PSL"
  keywords "test_LiFtEr_true" :: diag
   and     "test_LiFtEr_false":: diag
begin

ML_file "../src/Utils.ML"

ML{* (*type synonyms*)
type strings = string list;
type ints    = int    list;
*}

ML_file "../MiLkMaId/src/MiLkMaId_Util.ML"
ML_file "Matrix_Sig.ML"
ML_file "Matrix_Struct.ML"
ML_file "Matrix_Test.ML"
ML_file "LiFtEr_Util_Sig.ML"
ML_file "LiFtEr_Util_Struct.ML"
ML_file "Pattern_Sig.ML"
ML_file "Pattern_Struct.ML"
ML_file "Unique_Node_Sig.ML"
ML_file "Unique_Node_Struct.ML"
ML_file "Unique_Node_Test.ML"
ML_file "Term_Table_Sig.ML"
ML_file "Term_Table_Struct.ML"
ML_file "Term_Table_Test.ML"
ML_file "DInduct_Sig.ML"
ML_file "DInduct_Struct.ML"
ML_file "LiFtEr_Sig.ML"
ML_file "LiFtEr_Struct.ML"

ML{*
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
structure TL = Test_LiFtEr;
structure UN = Unique_Node;
structure DI = Dynamic_Induct;

val sample_induct_args1 = TL.Ind_Mods
 {ons   = [TL.Ind_On (TL.Print "x")],
  arbs  = [TL.Ind_Arb (TL.Print "y")],
  rules = []
  }: TL.ind_mods;

val sample_induct_args2 = TL.Ind_Mods
 {ons   = [TL.Ind_On (TL.Print "x")],
  arbs  = [],
  rules = []
  }: TL.ind_mods;

structure L = LiFtEr;
infix And;
val op And = L.And

 val sample_assert =
  L.All_Ind (L.Sub_Trm 1,
    L.Some_Sub_Trm_Occ (L.Sub_Trm_Occ 2,
        L.Trm_Occ_Is_Of_Trm (L.Sub_Trm_Occ 2, L.Sub_Trm 1)
      And
        L.Is_Atom (L.Sub_Trm_Occ 2))): L.assrt;

val LiFtEr_parser =
  PC.bind (PC.int) (fn assrt_numb:int =>
  PC.bind (PC.int) (fn ind_mod_numb:int =>
  PC.result (assrt_numb, ind_mod_numb))):(int * int) PC.parser;

*}

setup{* update_assert 1 sample_assert; *}
ML   {* get_assrt @{context} 1;    *}

setup{* update_ind_mod 1 sample_induct_args1; *}
setup{* update_ind_mod 2 sample_induct_args2; *}
ML   {* get_ind_mod @{context} 1;    *}
ML   {* get_ind_mod @{context} 2;    *}

ML{*
type trans_trans = Toplevel.transition -> Toplevel.transition;

fun get_trans_trans_gen (should_b_true_or_false:bool) (ass_numb:int, ind_mod_numb:int) =
  Toplevel.keep_proof (fn top: Toplevel.state =>
  let
    val pst = Toplevel.proof_of top: Proof.state;
    val ctxt = Toplevel.context_of top: Proof.context;
    val assert  = get_assrt ctxt ass_numb: LiFtEr.assrt;
    val ind_mod = get_ind_mod ctxt ind_mod_numb: TL.ind_mods;
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        L.eval (pst, assrt, ind_mods): bool;
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
*}

ML_file "Apply_MeLoId.ML"

lemma "True"
  test_LiFtEr_true 1 1
  oops

end