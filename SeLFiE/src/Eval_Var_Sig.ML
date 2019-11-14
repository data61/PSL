(*  Title:      PSL/SeLFeE/src/Eval_Var_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VAR =
sig

type parameter;
type parameter_assert;

(* The data-type constructors for boolean operations have to be declared in this signature.
 * because we need them in From_Var_To_Quantifier.*)
datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of parameter
| Assert     of assert * expr list;

val eval: term -> Proof.state -> expr -> expr;

end;