(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_BOUND =
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

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of assert * expr list;

val eval: term -> Proof.state -> expr -> expr;

end;