(*  Title:      PSL/SeLFeE/src/Eval_Number_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NUMBER =
sig

datatype number = Number of int;

datatype assert =
  Connective       of Eval_Connective.assert
| Are_Same_Number  of number  * number
| Is_Less_Than     of number  * number
| Is_Int           of number  * int;

val eval: assert -> Eval_Connective.assert;

end;