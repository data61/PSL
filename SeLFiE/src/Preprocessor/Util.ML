(*  Title:      PSL/SeLFiE/src/Preprocessor/Util.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for SeLFiE.
*)

(*** signature SELFIE_UTIL ***)
signature SELFIE_UTIL =
sig

val same_strings_when_normalized: Proof.context -> string -> string -> bool;

val ctxt_n_string_to_cname: Proof.context -> string -> string option;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: strings};
val dest_induct_arguments: induct_arguments  -> {ons: strings, arbs: strings, rules: strings};

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

val print_qtyp: qtyp -> string;

datatype atomic_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
| Is_Nth_Child
| Is_N_Plus_One_th_Child
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
(*Eval_Induct_Argument*)
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule;

val print_atomic_assert: atomic_assert -> string;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

val print_assert: assert -> string;

end;

(*** structure SeLFiE_Util ***)
structure SeLFiE_Util: SELFIE_UTIL =
struct

fun same_strings_when_normalized (ctxt:Proof.context) st1 st2 =
  let
    val normalize          = Isabelle_Utils.normalize_trm_as_string ctxt;
    val (norm_p1, norm_p2) = apply2 normalize (st1, st2);
  in
    norm_p1 = norm_p2
  end;

infix isSubstring;

fun ctxt_n_string_to_cname  (ctxt:Proof.context) (str:string) =
  let
    val trm_option = try (Syntax.read_term ctxt) str           : term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst: string option;
  in
    trm_cname
  end;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: strings};
fun dest_induct_arguments (Induct_Arguments arguments) = arguments;

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

fun print_qtyp QOuter_Path = "QOuter_Path"
  | print_qtyp QInner_Path = "QInner_Path"
  | print_qtyp QOuter_Print = "QOuter_Print"
  | print_qtyp QInner_Print = "QInner_Print"
  | print_qtyp QOuter_Number = "QOuter_Number"
  | print_qtyp QInner_Number = "QInner_Number"
  | print_qtyp QInd = "QInd"
  | print_qtyp QArb = "QArb"
  | print_qtyp QRule = "QRule";


datatype atomic_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
| Is_Nth_Child
| Is_N_Plus_One_th_Child
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
(*Eval_Induct_Argument*)
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule;

fun print_atomic_assert (Is_Cnst               ) = "Is_Cnst"
  | print_atomic_assert (Is_Free               ) = "Is_Free"
  | print_atomic_assert (Is_Var                ) = "Is_Var"
  | print_atomic_assert (Is_Bound              ) = "Is_Bound"
  | print_atomic_assert (Is_Lambda             ) = "Is_Lambda"
  | print_atomic_assert (Is_App                ) = "Is_App"
  | print_atomic_assert (Has_Same_Prnt_As      ) = "Has_Same_Prnt_As"
  | print_atomic_assert (Is_In_Trm_Prnt        ) = "Is_In_Trm_Prnt"
  | print_atomic_assert (Is_Deeper_Than        ) = "Is_Deeper_Than"
  | print_atomic_assert (Is_Shallower_Than     ) = "Is_Shallower_Than"
  | print_atomic_assert (Is_Path_Above         ) = "Is_Path_Above"
  | print_atomic_assert (Is_Same_Path_As       ) = "Is_Same_Path_As"
  | print_atomic_assert (Is_Nth_Child          ) = "Is_Nth_Child"
  | print_atomic_assert (Is_N_Plus_One_th_Child) = "Is_N_Plus_One_th_Child"
  | print_atomic_assert (Are_Same_Prints       ) = "Are_Same_Prints"
  | print_atomic_assert (Is_Printed_As         ) = "Is_Printed_As"
  | print_atomic_assert (Unode_Has_Print       ) = "Unode_Has_Print"
  | print_atomic_assert (Is_In_Subgoal         ) = "Is_In_Subgoal"
  | print_atomic_assert (Is_In_Chained_Fact    ) = "Is_In_Chained_Fact"
  | print_atomic_assert (Is_In_Nth_Subgoal     ) = "Is_In_Nth_Subgoal"
  | print_atomic_assert (Is_In_Nth_Chained_Fact) = "Is_In_Nth_Chained_Fact"
  | print_atomic_assert (Are_Same_Number       ) = "Are_Same_Number"
  | print_atomic_assert (Is_Less_Than          ) = "Is_Less_Than"
  | print_atomic_assert (Is_Nth_Induct         ) = "Is_Nth_Induct"
  | print_atomic_assert (Is_Nth_Arbitrary      ) = "Is_Nth_Arbitrary"
  | print_atomic_assert (Is_Induct             ) = "Is_Induct"
  | print_atomic_assert (Is_Arbitrary          ) = "Is_Arbitrary"
  | print_atomic_assert (Is_Rule               ) = "Is_Rule"


datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun print_assert Not   = "Not"
  | print_assert And   = "And"
  | print_assert Or    = "Or"
  | print_assert Nor   = "Nor"
  | print_assert Imply = "Imply"
  | print_assert Ands  = "Ands"
  | print_assert Ors   = "Ors"
  | print_assert (Atomic ass) = "Atomic " ^   print_atomic_assert ass ^ " "

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype 'path literal = Path of 'path | Non_Path of non_path_literal;

type 'path literals = 'path literal list;

end;