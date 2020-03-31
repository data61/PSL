(*  Title:      PSL/SeLFeE/src/Eval_Bool_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_BOOL ***)
signature EVAL_BOOL =
sig

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert =
  True
| False
| Not   of assert
| And   of assert * assert
| Or    of assert * assert
| Nor   of assert * assert
| Imply of assert * assert
| Ands  of assert list
| Ors   of assert list;

val eval: assert -> assert;

val bool_to_assert: bool -> assert;
val assert_to_bool: assert -> bool;

end;

(*** Eval_Bool ***)
structure Eval_Bool: EVAL_BOOL =
struct

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert =
  True
| False
| Not   of assert
| And   of assert * assert
| Or    of assert * assert
| Nor   of assert * assert
| Imply of assert * assert
| Ands  of assert list
| Ors   of assert list;

fun print_asserts (True   ) = "True"
  | print_asserts (False  ) = "False"
  | print_asserts (Not   _) = "Not"
  | print_asserts (And   _) = "And"
  | print_asserts (Or    _) = "Or"
  | print_asserts (Nor   _) = "Nor"
  | print_asserts (Imply _) = "Imply"
  | print_asserts (Ands  _) = "Ands"
  | print_asserts (Ors   _) = "Ors"

val _ = print_asserts;

infix And Or Nor Imply;

fun eval'  True                = true
  | eval'  False               = false
  | eval' (Not ass)            = not (eval' ass)
  | eval' (ass1 And   ass2)    = eval' ass1 andalso eval' ass2
  | eval' (ass1 Or    ass2)    = eval' ass1 orelse  eval' ass2
  | eval' (ass1 Nor   ass2)    = not (eval' ass1) andalso not (eval' ass2)
  | eval' (ass1 Imply ass2)    = if eval' ass1 then eval' ass2 else true
  | eval' (Ands []        )    = true
  | eval' (Ands [ass])         = eval' ass
  | eval' (Ands [ass1, ass2])  = eval' (ass1 And ass2)
  | eval' (Ands (ass1::asses)) = eval' ass1 andalso eval' (Ands asses)
  | eval' (Ors []        )     = false
  | eval' (Ors [ass])          = eval' ass
  | eval' (Ors [ass1, ass2])   = eval' (ass1 Or ass2)
  | eval' (Ors (ass1::asses))  = eval' ass1 orelse eval' (Ors asses);

fun eval assert_connective = if eval' assert_connective then True else False;

fun bool_to_assert (b:bool) = if b then True else False;
fun assert_to_bool True  = true
  | assert_to_bool False = false
  | assert_to_bool _     = error "assert_to_bool failed."

end;