(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
sig

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*);

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;