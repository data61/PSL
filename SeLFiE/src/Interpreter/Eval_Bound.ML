(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

type path;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of SeLFiE_Util.print
| String  of string
| Number  of int
| Int     of int
| Command of Pattern.command;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of SeLFiE_Util.assert * expr list;

val eval: term -> Proof.state -> expr -> expr;

end;