(*  Title:      PSL/SeLFeE/src/Eval_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Bool_With_Parameter has constructs from Eval_Bool.
    We have to have the boolean operators this way to implement quantifiers in later steps.
*)
signature EVAL_PARAMETER_WITH_BOOL =
sig

type path;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of SeLFiE_Util.print
| String  of string
| Number  of int
| Int     of int
| Command of Pattern.command;

type parameters = parameter list;

val eval: term -> Proof.state -> SeLFiE_Util.assert -> parameters -> parameter;

end;