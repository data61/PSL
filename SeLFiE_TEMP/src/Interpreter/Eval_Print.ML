(*  Title:      PSL/SeLFeE/src/Eval_Print.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PRINT ***)
signature EVAL_PRINT =
sig

type print = SeLFiE_Util.print;

datatype assert =
  Are_Same_Prints      of print * print
| Is_Printed_As        of print * string;

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Inner_Print ***)
structure Eval_Inner_Print =
struct

structure EB = Eval_Bool;
structure SU = SeLFiE_Util;

type print = SU.print;

datatype assert =
  Are_Same_Prints of print * print
| Is_Printed_As   of print * string;

infix Is_Printed_As;

fun eval (Are_Same_Prints print_pair)                = print_pair |> uncurry SU.same_prints |> EB.bool_to_assert
  | eval (SU.Print printed_str Is_Printed_As string) = EB.bool_to_assert (printed_str = string);

end;

(*** Eval_Outer_Print ***)
(*TODO*)