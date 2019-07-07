(*  Title:      PSL/SeLFeE/src/Eval_Print_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Print_Core =
struct

open Eval_Fpunode_Sugar;
open Eval_Connective;
open LiFtEr_Util;

type print = LiFtEr_Util.print;

datatype assert_print_core =
  Assert_Fpunode_Sugar of assert_fpunode_sugar
| Are_Same_Prints      of print * print
| Is_Printed_As        of print * string;

infix Is_Printed_As;

fun eval_print_core (Assert_Fpunode_Sugar assert_fpunode_sugar) =
    eval_fpunode_sugar assert_fpunode_sugar
  | eval_print_core (Are_Same_Prints print_pair) =
    print_pair |> uncurry same_prints |> bool_to_assert_connective
  | eval_print_core (Print printed_str Is_Printed_As string) =
    bool_to_assert_connective (printed_str = string);

end;