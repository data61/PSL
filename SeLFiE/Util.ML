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
| Is_Rule_Of_Node
| Is_Defined_With
| Takes_N_Arguments
| Takes_Less_Than_N_Arguments
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode;

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

val rule_to_const_name: Proof.context -> string -> string;

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
| Is_Rule_Of_Node
| Is_Defined_With
| Takes_N_Arguments
| Takes_Less_Than_N_Arguments
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode;

fun print_atomic_assert (Is_Cnst                    ) = "Is_Cnst"
  | print_atomic_assert (Is_Free                    ) = "Is_Free"
  | print_atomic_assert (Is_Var                     ) = "Is_Var"
  | print_atomic_assert (Is_Bound                   ) = "Is_Bound"
  | print_atomic_assert (Is_Lambda                  ) = "Is_Lambda"
  | print_atomic_assert (Is_App                     ) = "Is_App"
  | print_atomic_assert (Takes_N_Arguments          ) = "Takes_N_Arguments"
  | print_atomic_assert (Takes_Less_Than_N_Arguments) = "Takes_Less_Than_N_Arguments"
  | print_atomic_assert (Is_Defined_With            ) = "Is_Defined_With"
  | print_atomic_assert (Is_Rule_Of_Node            ) = "Is_Rule_Of_Node"
  | print_atomic_assert (Has_Same_Prnt_As           ) = "Has_Same_Prnt_As"
  | print_atomic_assert (Is_Deeper_Than             ) = "Is_Deeper_Than"
  | print_atomic_assert (Is_Shallower_Than          ) = "Is_Shallower_Than"
  | print_atomic_assert (Is_Path_Above              ) = "Is_Path_Above"
  | print_atomic_assert (Is_Same_Path_As            ) = "Is_Same_Path_As"
  | print_atomic_assert (Is_Nth_Child               ) = "Is_Nth_Child"
  | print_atomic_assert (Is_N_Plus_One_th_Child     ) = "Is_N_Plus_One_th_Child"
  | print_atomic_assert (Is_Root_In_A_Location      ) = "Is_Root_In_A_Location"
  | print_atomic_assert (Are_Same_Prints            ) = "Are_Same_Prints"
  | print_atomic_assert (Is_Subprint_Of             ) = "Is_Subprint_Of"
  | print_atomic_assert (Unode_Has_Print            ) = "Unode_Has_Print"
  | print_atomic_assert (Is_In_Subgoal              ) = "Is_In_Subgoal"
  | print_atomic_assert (Is_In_Chained_Fact         ) = "Is_In_Chained_Fact"
  | print_atomic_assert (Is_In_Nth_Subgoal          ) = "Is_In_Nth_Subgoal"
  | print_atomic_assert (Is_In_Nth_Chained_Fact     ) = "Is_In_Nth_Chained_Fact"
  | print_atomic_assert (Are_Same_Number            ) = "Are_Same_Number"
  | print_atomic_assert (Is_Less_Than               ) = "Is_Less_Than"
  | print_atomic_assert (Is_Less_Than_By_One        ) = "Is_Less_Than_By_One"
  | print_atomic_assert (Is_Nth_Induct              ) = "Is_Nth_Induct"
  | print_atomic_assert (Is_Nth_Arbitrary           ) = "Is_Nth_Arbitrary"
  | print_atomic_assert (Is_Induct                  ) = "Is_Induct"
  | print_atomic_assert (Is_Arbitrary               ) = "Is_Arbitrary"
  | print_atomic_assert (Is_Rule                    ) = "Is_Rule"
  | print_atomic_assert (Is_Rule_Of_Print           ) = "Is_Rule_Of_Print"
  | print_atomic_assert (Debug_Non_Path_Literal     ) = "Debug_Non_Path_Literal"
  | print_atomic_assert (Debug_Print_Unode          ) = "Debug_Print_Unode";

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

fun split_using_period x = String.tokens (fn splitter => splitter = #".") x;

fun rule_to_const_name (ctxt:Proof.context) (rule_name:string) =
  try split_using_period rule_name
<$> Utils.init
<$> String.concatWith "."
<$> Syntax.read_term ctxt
<$> Term.dest_Const
<$> fst
 |> Utils.the' "rule_to_const_name failed.";

end;