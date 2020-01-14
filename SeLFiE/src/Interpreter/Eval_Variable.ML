(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VARIABLE =
sig

type path;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of SeLFiE_Util.print
| String  of string
| Number  of Eval_Number.number
| Int     of int
| Command of Pattern.command;

datatype expr =
  Variable   of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of parameter
| Assert     of SeLFiE_Util.assert * expr list;

val eval: term -> Proof.state -> expr -> expr;

end;