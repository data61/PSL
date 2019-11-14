(*  Title:      PSL/SeLFeE/src/Eval_Expression_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Expression has constructs from Eval_Connective.
*)
signature EVAL_EXPRESSION =
sig

type connective = Eval_Connective.assert;
type path;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;(*TODO: double-check*)

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string(*redundant?*)
| Number  of number
| Int     of int
| Command of command;

type parameters = parameter list;

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

val eval: term -> Proof.state -> assert -> parameters -> parameter;

end;