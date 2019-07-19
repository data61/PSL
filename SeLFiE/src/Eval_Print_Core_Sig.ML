(*  Title:      PSL/SeLFeE/src/Eval_Print_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRINT_CORE =
sig

type print = LiFtEr_Util.print;

datatype assert =
  Are_Same_Prints      of print * print
| Is_Printed_As        of print * string;

val eval: assert -> Eval_Connective.assert;

end;