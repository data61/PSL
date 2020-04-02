(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*TODO: rename this to Eval_Literal?*)

(*** signature EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype literal =
  Outer_Path of outer_path
| Inner_Path of UN.inner_path
| Non_Path   of non_path_literal;

type literals = literal list;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> SeLFiE_Util.atomic_assert -> literals -> Eval_Bool.assert;

end;