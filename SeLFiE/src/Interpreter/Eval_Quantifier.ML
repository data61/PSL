(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER =
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
  Variable of string
| Lambda   of string * expr
| Apply    of expr   * expr
| Literal  of parameter
| Assert   of SeLFiE_Util.assert * expr list
| All      of string * SeLFiE_Util.qtyp * expr
| Some     of string * SeLFiE_Util.qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;