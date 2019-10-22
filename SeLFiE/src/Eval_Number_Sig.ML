(*  Title:      PSL/SeLFeE/src/Eval_Number_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NUMBER =
sig

type print      = LiFtEr_Util.print;
type fpunode    = Full_Path_To_Fpunode.fpunode;
datatype number = Number of int;

datatype assert =
  Connective       of Eval_Connective.assert
| Are_Same_Number  of number  * number
| Is_Less_Than     of number  * number
(* TODO: Is_Nth_Ind and Is_Nth_Arb should be defined in Eval_Modifier.
| Is_Nth_Ind       of print   * number (*Counting starts with 0.*)
| Is_Nth_Arb       of print   * number (*Counting starts with 0.*)
*)
| Is_Int           of number  * int;

val eval: assert -> Eval_Connective.assert;

end;