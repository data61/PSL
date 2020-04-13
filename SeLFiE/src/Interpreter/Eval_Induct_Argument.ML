(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Induct_Argument.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
SeLFiE: Semantic Logical Feature Extractor.
*)
(*** EVAL_INDUCT_ARGUMENT ***)
signature EVAL_INDUCT_ARGUMENT =
sig

datatype assert =
  Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string;

val eval: assert -> SeLFiE_Util.induct_arguments -> Eval_Bool.assert;

end;

(*** Eval_Induct_Argument ***)
structure Eval_Induct_Argument: EVAL_INDUCT_ARGUMENT =
struct

structure SU = SeLFiE_Util;
structure EB = Eval_Bool;
structure EN = Eval_Number;

datatype assert =
  Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string;

fun eval' (assert:assert) (SU.Induct_Arguments {ons, arbs, rules}: SU.induct_arguments) =
  let
    fun ev (Is_Nth_Induct    (print, n)) = nth ons  n = print
      | ev (Is_Nth_Arbitrary (print, n)) = nth arbs n = print
      | ev (Is_Induct         print    ) = member (op =) ons   print
      | ev (Is_Arbitrary      print    ) = member (op =) arbs  print
      | ev (Is_Rule           print    ) = member (op =) rules print
  in ev assert end;

fun eval  assert                        (ind_args:SU.induct_arguments) = eval' assert ind_args |> EB.bool_to_assert;

end;