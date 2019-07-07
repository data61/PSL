(*  Title:      PSL/SeLFeE/src/Eval_Connective_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Connective: EVAL_CONNECTIVE =
struct

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert_connective =
  True
| False
| Not   of assert_connective
| And   of assert_connective * assert_connective
| Or    of assert_connective * assert_connective
| Nor   of assert_connective * assert_connective
| Imply of assert_connective * assert_connective;

infix And Or Nor Imply;

fun eval_connective'  True             = true
  | eval_connective'  False            = false
  | eval_connective' (Not ass)         = not (eval_connective' ass)
  | eval_connective' (ass1 And   ass2) = eval_connective' ass1 andalso eval_connective' ass2
  | eval_connective' (ass1 Or    ass2) = eval_connective' ass1 orelse  eval_connective' ass2
  | eval_connective' (ass1 Nor   ass2) = not (eval_connective' ass1) andalso not (eval_connective' ass2)
  | eval_connective' (ass1 Imply ass2) = if eval_connective' ass1 then eval_connective' ass2 else true;

fun eval_connective assert_connective = if eval_connective' assert_connective then True else False;

fun bool_to_assert_connective (b:bool) = if b then True else False;

end;