(*  Title:      PSL/SeLFeE/src/Eval_Print.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PRINT ***)
signature EVAL_PRINT =
sig

datatype assert =
  Are_Same_Prints  of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string;

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Print ***)
structure Eval_Print =
struct

structure EB = Eval_Bool;
structure SU = SeLFiE_Util;
structure EN = Eval_Number;

datatype assert =
  Are_Same_Prints  of string * string
| Is_Nth_Induct    of string * int
| Is_Nth_Arbitrary of string * int
| Is_Induct        of string
| Is_Arbitrary     of string
| Is_Rule          of string
| Is_Rule_Of       of string * string;

infix Is_Printed_As;

fun eval' (Are_Same_Prints (prnt1, prnt2)) _  = prnt1 = prnt2
  | eval' (Is_Nth_Induct    (print, n)) (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) = nth ons  n = print
  | eval' (Is_Nth_Arbitrary (print, n)) (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) = nth arbs n = print
  | eval' (Is_Induct         print    ) (SU.Induct_Arguments {ons,   ...}: SU.induct_arguments) = member (op =) ons   print
  | eval' (Is_Arbitrary      print    ) (SU.Induct_Arguments {arbs,  ...}: SU.induct_arguments) = member (op =) arbs  print
  | eval' (Is_Rule           print    ) (SU.Induct_Arguments {rules, ...}: SU.induct_arguments) = member (op =) rules print;

fun eval  assert (ind_args:SU.induct_arguments) = eval' assert ind_args |> EB.bool_to_assert;

end;