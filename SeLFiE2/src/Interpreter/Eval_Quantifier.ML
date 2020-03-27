(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER =
sig

type path;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

datatype expr =
  Bound   of int
| Lambda  of expr
| Apply   of expr   * expr
| Literal of parameter
| Assert  of SeLFiE_Util.assert * expr list
| All     of SeLFiE_Util.qtyp * expr
| Some    of SeLFiE_Util.qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

(*val eval: term -> Proof.state -> expr -> expr;*)

end;