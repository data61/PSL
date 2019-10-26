(*  Title:      PSL/SeLFeE/src/Eval_Print_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Print_Core =
struct

structure EC = Eval_Connective;
structure LU = LiFtEr_Util;

type print = LiFtEr_Util.print;

datatype assert =
  Are_Same_Prints of print * print
| Is_Printed_As   of print * string;

infix Is_Printed_As;

fun eval (Are_Same_Prints print_pair)                = print_pair |> uncurry LU.same_prints |> EC.bool_to_assert_connective
  | eval (LU.Print printed_str Is_Printed_As string) = EC.bool_to_assert_connective (printed_str = string);

end;