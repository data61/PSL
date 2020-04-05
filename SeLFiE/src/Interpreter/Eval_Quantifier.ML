(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER =
sig

datatype expr =
  Bound   of int
| Lambda  of expr
| Apply   of expr   * expr
| Literal of Eval_Parameter.literal
| Assert  of SeLFiE_Util.assert * expr list
| All     of SeLFiE_Util.qtyp * expr
| Some    of SeLFiE_Util.qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;