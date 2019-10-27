(*  Title:      PSL/SeLFeE/src/Eval_Var_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VAR =
sig

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of Eval_Expression.parameter
| Assert     of Eval_Expression.assert * expr list;

val eval: Proof.state -> expr -> expr;

end;