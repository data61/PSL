(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Quantifier.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER =
sig

type path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

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

type qtyp = SeLFiE_Util.qtyp;

datatype expr =
  Variable of string
| Lambda   of string * expr
| Apply    of expr   * expr
| Literal  of parameter
| Assert   of assert * expr list
| All      of string * qtyp * expr
| Some     of string * qtyp * expr;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;