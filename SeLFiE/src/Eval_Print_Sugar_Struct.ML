(*  Title:      PSL/SeLFeE/src/Eval_Print_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Print_Sugar: EVAL_PRINT_SUGAR =
struct

open Eval_Print_Core;
open Eval_Connective;
open Full_Path_To_Fpunode;
open Eval_Fpunode_Core;
open Eval_Print_Core;

datatype assert_print_sugar =
  Assert_Print_Core    of assert_print_core
| Connective           of assert_connective
| Are_Different_Prints of print   * print
| Fpnode_Has_Print     of fpunode * print;

infix
  Fpnode_Has_Print
  Print_Is_String

fun eval_print_sugar (Assert_Print_Core assert_print_core) = eval_print_core assert_print_core
  | eval_print_sugar (Connective assert_connective) = eval_connective assert_connective
  | eval_print_sugar (Are_Different_Prints print_pair) =
    print_pair |> Are_Same_Prints |> eval_print_core |> Not |> eval_connective
  | eval_print_sugar (fpunode Fpnode_Has_Print print1) =
    let
      val print2 = fpunode_to_unode fpunode |> #print: print;
      val result = same_prints print1 print2 |> bool_to_assert_connective;
    in
      result
    end;

end;