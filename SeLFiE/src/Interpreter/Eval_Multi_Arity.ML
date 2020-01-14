(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

type path;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of SeLFiE_Util.assert * expr list
| Alls     of (string * SeLFiE_Util.qtyp) list * expr
| Somes    of (string * SeLFiE_Util.qtyp) list * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;