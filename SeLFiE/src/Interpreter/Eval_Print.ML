(*  Title:      PSL/SeLFeE/src/Eval_Print.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PRINT ***)
signature EVAL_PRINT =
sig

datatype assert =
  Are_Same_Prints      of string * string

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Print ***)
structure Eval_Print =
struct

structure EB = Eval_Bool;
structure SU = SeLFiE_Util;

datatype assert =
  Are_Same_Prints of string * string

infix Is_Printed_As;

fun eval (Are_Same_Prints (prnt1, prnt2)) = prnt1 = prnt2 |> EB.bool_to_assert

end;