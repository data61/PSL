(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

type path;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of SeLFiE_Util.assert * expr list;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;