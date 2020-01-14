(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

type path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string
| Number  of number
| Int     of int
| Command of command;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of SeLFiE_Util.assert * expr list;

val eval: term -> Proof.state -> expr -> expr;

end;