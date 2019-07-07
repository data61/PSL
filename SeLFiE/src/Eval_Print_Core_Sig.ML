(*  Title:      PSL/SeLFeE/src/Eval_Print_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRINT_CORE =
sig

type assert_fpunode_sugar;
type assert_connective;
type print;

datatype assert_print_core =
  Assert_Fpunode_Sugar of assert_fpunode_sugar
| Are_Same_Prints      of print * print
| Is_Printed_As        of print * string;

val eval_print_core: assert_print_core -> assert_connective;

end;