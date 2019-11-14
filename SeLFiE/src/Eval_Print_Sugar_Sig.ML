(*  Title:      PSL/SeLFeE/src/Eval_Print_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRINT_SUGAR =
sig

type print   = LiFtEr_Util.print;

datatype assert =
  Connective           of Eval_Connective.assert
| Are_Different_Prints of print    * print
| Unode_Has_Print      of UN.unode * print;

val eval: assert -> Eval_Connective.assert;

end;