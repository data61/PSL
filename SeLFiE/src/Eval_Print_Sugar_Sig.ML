(*  Title:      PSL/SeLFeE/src/Eval_Print_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRINT_SUGAR =
sig

type assert_print_core;
type assert_connective;
type print;
type fpunode;

datatype assert_print_sugar =
  Assert_Print_Core    of assert_print_core
| Connective           of assert_connective
| Are_Different_Prints of print   * print
| Fpnode_Has_Print     of fpunode * print;

val eval_print_sugar: assert_print_sugar -> assert_connective;

end;