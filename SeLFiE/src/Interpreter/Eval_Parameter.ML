(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

type path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

type atomic_assert = SeLFiE_Util.atomic_assert;

val eval: term -> Proof.state -> atomic_assert -> parameters -> Eval_Bool.assert;

end;