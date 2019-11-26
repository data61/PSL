(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
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

type qtyp(* = QFull_Path | QPrint | QInd | QArb | QRule | QNumber*)

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of assert * expr list
| Alls     of (string * qtyp) list * expr
| Somes    of (string * qtyp) list * expr;

val eval: term -> Proof.state -> expr -> expr;

end;