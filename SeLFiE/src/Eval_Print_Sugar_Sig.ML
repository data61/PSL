(*  Title:      PSL/SeLFeE/src/Eval_Print_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRINT_SUGAR =
sig

type print   = LiFtEr_Util.print;
type fpunode = Full_Path_To_Fpunode.fpunode;

datatype assert =
  Connective           of Eval_Connective.assert
| Are_Different_Prints of print   * print
| Fpnode_Has_Print     of fpunode * print;

val eval: assert -> Eval_Connective.assert;

end;