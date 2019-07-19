(*  Title:      PSL/SeLFeE/src/Eval_Print_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Print_Sugar: EVAL_PRINT_SUGAR =
struct

structure EC   = Eval_Connective;
structure EPC  = Eval_Print_Core;
structure FPTF = Full_Path_To_Fpunode;

type print   = LiFtEr_Util.print;
type fpunode = Full_Path_To_Fpunode.fpunode;

datatype assert =
  Connective           of EC.assert
| Are_Different_Prints of print   * print
| Fpnode_Has_Print     of fpunode * print;

infix
  Fpnode_Has_Print
  Print_Is_String;

fun eval (Connective assert_connective) = EC.eval assert_connective
  | eval (Are_Different_Prints print_pair) =
    print_pair |> EPC.Are_Same_Prints |> EPC.eval |> EC.Not |> EC.eval
  | eval (fpunode Fpnode_Has_Print print1) =
    let
      val print2 = FPTF.fpunode_to_unode fpunode |> #print: print;
      val result = LiFtEr_Util.same_prints print1 print2 |> EC.bool_to_assert_connective;
    in
      result
    end;

end;