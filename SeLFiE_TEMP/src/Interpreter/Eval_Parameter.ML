(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

type path(*    = SeLFiE_Util.inner_path*);
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string(*redundant?*)
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

type parameter_assert;

val eval: term -> Proof.state -> parameter_assert -> parameters -> Eval_Bool.assert;

end;