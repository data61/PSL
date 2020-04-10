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
| And   of assert Seq.seq
| Or    of assert Seq.seq
| Nor   of assert Seq.seq
| Imply of assert Seq.seq
| Ands  of assert Seq.seq
| Ors   of assert Seq.seq

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
| And   of assert Seq.seq
| Or    of assert Seq.seq
| Nor   of assert Seq.seq
| Imply of assert Seq.seq
| Ands  of assert Seq.seq
| Ors   of assert Seq.seq

fun print_asserts (True   ) = "True"
  | print_asserts (False  ) = "False"
  | print_asserts (Not   _) = "Not"
  | print_asserts (And   _) = "And"
  | print_asserts (Or    _) = "Or"
  | print_asserts (Nor   _) = "Nor"
  | print_asserts (Imply _) = "Imply"
  | print_asserts (Ands  _) = "Ands"
  | print_asserts (Ors   _) = "Ors"

fun eval'  True         = true
  | eval'  False        = false
  | eval' (Not ass)     = not (eval' ass)
  | eval' (And asses)   = (case Seq.pull asses of SOME (head1, tail1) => (eval' head1 andalso eval' (Seq.hd tail1))              | _ => error "And in Eval_Bool failed.")
  | eval' (Or  asses)   = (case Seq.pull asses of SOME (head1, tail1) => (eval' head1 orelse  eval' (Seq.hd tail1))              | _ => error "Or in Eval_Bool failed.")
  | eval' (Nor asses)   = (case Seq.pull asses of SOME (head1, tail1) => (eval' (Not head1) andalso  eval' (Not (Seq.hd tail1))) | _ => error "Nor in Eval_Bool failed.")
  | eval' (Imply asses) = (case Seq.pull asses of SOME (head1, tail1) => (if eval' head1 then eval' (Seq.hd tail1) else true)    | _ => error "Imply in Eval_Bool failed.")
  | eval' (Ands asses)  = (case Seq.pull asses of SOME (head1, tail1) => (eval' head1 andalso eval' (Ands tail1))                | _ => true)
  | eval' (Ors  asses)  = (case Seq.pull asses of SOME (head1, tail1) => (tracing "Ors";eval' head1 orelse eval' (Ors tail1))    | _ => false)

fun eval assert_connective = if eval' assert_connective then True else False;

fun bool_to_assert (b:bool) = if b then True else False;
fun assert_to_bool True  = true
  | assert_to_bool False = false
  | assert_to_bool _     = error "assert_to_bool failed."

end;