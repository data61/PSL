(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

type path;

datatype parameter =
  Path      of path
| Print     of SeLFiE_Util.print
| String    of string
| Number    of Eval_Number.number
| Int       of int
| Command   of Pattern.command;

type parameters = parameter list;

type atomic_assert = SeLFiE_Util.atomic_assert;

val eval: term -> Proof.state -> atomic_assert -> parameters -> Eval_Bool.assert;

end;