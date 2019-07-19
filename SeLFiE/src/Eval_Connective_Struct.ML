(*  Title:      PSL/SeLFeE/src/Eval_Connective_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Connective: EVAL_CONNECTIVE =
struct

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert =
  True
| False
| Not   of assert
| And   of assert * assert
| Or    of assert * assert
| Nor   of assert * assert
| Imply of assert * assert;

infix And Or Nor Imply;

fun eval'  True             = true
  | eval'  False            = false
  | eval' (Not ass)         = not (eval' ass)
  | eval' (ass1 And   ass2) = eval' ass1 andalso eval' ass2
  | eval' (ass1 Or    ass2) = eval' ass1 orelse  eval' ass2
  | eval' (ass1 Nor   ass2) = not (eval' ass1) andalso not (eval' ass2)
  | eval' (ass1 Imply ass2) = if eval' ass1 then eval' ass2 else true;

fun eval assert_connective = if eval' assert_connective then True else False;

fun bool_to_assert_connective (b:bool) = if b then True else False;

end;