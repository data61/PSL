(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

type path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;
type qtyp    = SeLFiE_Util.qtyp;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string
| Number  of number
| Int     of int
| Command of command;

type atomic_assert = SeLFiE_Util.atomic_assert;

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
| Atomic of atomic_assert;

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of assert * expr list
| Alls     of (string * qtyp) list * expr
| Somes    of (string * qtyp) list * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;