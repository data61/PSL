(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

type path;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

datatype expr =
  Bound    of int
| Lambdas  of int * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies  of expr   * expr list
| Literal  of parameter
| Assert   of SeLFiE_Util.assert * expr list
| All      of SeLFiE_Util.qtyp * expr
| Some     of SeLFiE_Util.qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;