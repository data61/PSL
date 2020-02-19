(*  Title:      PSL/SeLFiE/src/Preprocessor/Util.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for SeLFiE.
*)

(*** signature SELFIE_UTIL ***)
signature SELFIE_UTIL =
sig

type inner_path = ints;
val same_strings_when_normalized: Proof.context -> string -> string -> bool;
val inner_path_to_string        : inner_path -> string;

val ctxt_n_string_to_cname: Proof.context -> string -> string option;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: strings};
val dest_induct_arguments: induct_arguments  -> {ons: strings, arbs: strings, rules: strings};

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

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

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

datatype non_path_parameter =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

end;

(*** structure SeLFiE_Util ***)
structure SeLFiE_Util: SELFIE_UTIL =
struct

type     inner_path   = ints;

fun same_strings_when_normalized (ctxt:Proof.context) st1 st2 =
  let
    val normalize          = Isabelle_Utils.normalize_trm_as_string ctxt;
    val (norm_p1, norm_p2) = apply2 normalize (st1, st2);
  in
    norm_p1 = norm_p2
  end;
                                                                              
fun path_to_string'  []               (acc:string) = acc
  | path_to_string' (step::path:ints) (acc:string)= path_to_string' path (acc ^ "," ^ Int.toString step);

fun inner_path_to_string  []               = ""
  | inner_path_to_string (step::path:ints) = "Path is " ^ Int.toString step ^ path_to_string' path "";

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

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

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

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

datatype non_path_parameter =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

end;