(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Induct_Argument.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MeLoId: Machine Learning Induction for Isabelle/HOL, and
LiFtEr: Logical Feature Extractor.
SeLFiE: Semantic Logical Feature Extractor.
*)
(*** EVAL_INDUCT_ARGUMENT ***)
signature EVAL_INDUCT_ARGUMENT =
sig

type number = Eval_Number.number;
type print  = SeLFiE_Util.print;

datatype assert =
  Connective       of Eval_Bool.assert
| Is_Nth_Induct    of print * number
| Is_Nth_Arbitrary of print * number
| Is_Induct        of print
| Is_Arbitrary     of print
| Is_Rule          of print;

val eval: assert -> SeLFiE_Util.induct_arguments -> Eval_Bool.assert;

end;

(*** Eval_Induct_Argument ***)
structure Eval_Induct_Argument: EVAL_INDUCT_ARGUMENT =
struct

structure SU = SeLFiE_Util;
structure EB = Eval_Bool;
structure EN = Eval_Number;

type number = Eval_Number.number;
type print  = SeLFiE_Util.print;

datatype assert =
  Connective       of Eval_Bool.assert
| Is_Nth_Induct    of print * number
| Is_Nth_Arbitrary of print * number
| Is_Induct        of print
| Is_Arbitrary     of print
| Is_Rule          of print;

fun eval' (assert:assert) (SU.Induct_Arguments {ons, arbs, rules}: SU.induct_arguments) =
  let
    fun ev (Is_Nth_Induct    (print, EN.Number n)) = nth ons  n = print
      | ev (Is_Nth_Arbitrary (print, EN.Number n)) = nth arbs n = print
      | ev (Is_Induct         print              ) = member (op =) ons   print
      | ev (Is_Arbitrary      print              ) = member (op =) arbs  print
      | ev (Is_Rule           print              ) = member (op =) rules print
      | ev (Connective        _                  ) = error "ev in Eval_Induct_Argument.ML failed."
  in ev assert end;

fun eval (Connective assert_connective) (_       :SU.induct_arguments) = EB.eval assert_connective
  | eval  assert                        (ind_args:SU.induct_arguments) = eval' assert ind_args |> EB.bool_to_assert;

end;