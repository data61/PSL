(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Induct_Argument.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
SeLFiE: Semantic Logical Feature Extractor.
*)
(*** EVAL_INDUCT_ARGUMENT ***)
signature EVAL_INDUCT_ARGUMENT =
sig

datatype number = Number of int;
type print      = SeLFiE_Util.print;

datatype assert =
  Is_Nth_Induct    of print
| Is_Nth_Arbitrary of print
| Is_Induct        of print
| Is_Arbitrary     of print
| Is_Rule          of print;
(*
val eval: assert -> Eval_Bool.assert;
*)
end;

(*** Eval_Induct_Argument ***)
structure Eval_Induct_Argument: EVAL_INDUCT_ARGUMENT =
struct

structure EC = Eval_Bool;

datatype number = Number of int;
type print      = SeLFiE_Util.print;

datatype assert =
  Is_Nth_Induct    of print
| Is_Nth_Arbitrary of print
| Is_Induct        of print
| Is_Arbitrary     of print
| Is_Rule          of print;
(*
fun eval' (assert:assert) (SeLFiE_Util.Ind) :SeLFiE_Util.ind_mods) =
fun eval (Is_Nth_Induct print)

fun eval' (Are_Same_Number (Number numb1, Number numb2)) = numb1 = numb2
  | eval' (Number numb1 Is_Less_Than Number numb2)       = numb1 < numb2
  | eval' (Number numb Is_Int int)                       = numb = int
  | eval'  _                                             = error "eval' in Eval_Number_Struct failed!";

fun eval (Connective assert_connective) = EC.eval assert_connective
  | eval  assert                        = eval' assert |> EC.bool_to_assert;
*)
end;