(*  Title:      PSL/SeLFeE/src/Eval_Bound_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Expression.parameter
| Assert     of Eval_Expression.assert * expr list;

val eval: Proof.state -> expr -> expr;

end;