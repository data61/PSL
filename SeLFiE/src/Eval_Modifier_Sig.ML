(*  Title:      PSL/SeLFiE/src/Eval_Modifier_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MODIFIER =
sig

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule;

datatype modifier = 
  Ind  of string
| Arb  of string
| Rule of string;

val pst_to_ind_domain: Proof.state -> modifier -> Eval_Parameters.parameters;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr * expr
| Connective of Eval_Connective.assert
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list
| All        of string * qtyp * expr
| Some       of string * qtyp * expr;

val eval: Proof.state -> expr -> expr;

end;