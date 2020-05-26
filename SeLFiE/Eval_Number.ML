(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Number.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_NUMBER ***)
signature EVAL_NUMBER =
sig

datatype assert =
  Connective          of Eval_Bool.assert
| Are_Same_Number     of int  * int
| Is_Less_Than        of int  * int
| Is_Less_Than_By_One of int  * int;

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Number ***)
structure Eval_Number: EVAL_NUMBER =
struct

structure EB = Eval_Bool;

datatype assert =
(*We we really need Connective? We do not have syntactic sugars for Number.*)
  Connective      of Eval_Bool.assert
| Are_Same_Number of int * int
| Is_Less_Than    of int * int
| Is_Less_Than_By_One of int  * int;

infix
  Is_Less_Than
  Is_Int
  Is_Less_Than_By_One

fun eval' (Are_Same_Number (numb1, numb2))  = numb1 = numb2
  | eval' (numb1 Is_Less_Than numb2)        = numb1 < numb2
  | eval' (numb1 Is_Less_Than_By_One numb2) = numb1 + 1 = numb2
  | eval'  _                               = error "eval' in Eval_Number_Struct failed!";

fun eval (Connective assert_connective) = EB.eval assert_connective
  | eval  assert                        = eval' assert |> EB.bool_to_assert;

end;