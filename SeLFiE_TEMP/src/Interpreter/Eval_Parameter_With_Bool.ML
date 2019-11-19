(*  Title:      PSL/SeLFeE/src/Eval_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Bool_With_Parameter has constructs from Eval_Bool.
    We have to have the boolean operators this way to implement quantifiers in later steps.
*)
signature EVAL_PARAMETER_WITH_BOOL =
sig

type path;
type print      = SeLFiE_Util.print;
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