(*  Title:      PSL/SeLFeE/src/Eval_Number_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Number: EVAL_NUMBER =
struct

structure EC = Eval_Connective;

datatype number  = Number of int;

datatype assert =
(*We we really need Connective? We do not have syntactic sugars for Number.*)
  Connective      of EC.assert
| Are_Same_Number of number  * number
| Is_Less_Than    of number  * number
| Is_Int          of number  * int;

infix
  Is_Less_Than
  Is_Int

fun eval' (Are_Same_Number (Number numb1, Number numb2)) = (numb1 = numb2)
  | eval' (Number numb1 Is_Less_Than Number numb2)       = (numb1 < numb2)
  | eval' (Number numb Is_Int int)                       = (numb = int)
  | eval'  _                                             = error "eval' in Eval_Number_Struct failed!";

fun eval (Connective assert_connective) = EC.eval assert_connective
  | eval  assert                        = eval' assert |> EC.bool_to_assert_connective;

end;