(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_28
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun y :: "'a list => 'a list => 'a list" where
  "y (nil2) y2 = y2"
| "y (cons2 z2 xs) y2 = cons2 z2 (y xs y2)"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y22) = x x2 y22"
print_theorems
fun elem :: "Nat => Nat list => bool" where
  "elem z (nil2) = False"
| "elem z (cons2 z2 xs) = (if x z z2 then True else elem z xs)"
thm y.simps(1)
theorem property0 :
  "elem z (y xs (cons2 z (nil2)))"
(*Why induct on xs?
  Because y is the innermost recursive constant,
  with case distinction on the first parameter.*)
(*"arbitrary:z" also works well.*)
(*Why "arbitrary:z"?
  Because z appears within "(cons2 z (nil2))", which is the second
  argument of the innermost recursive constant, "y", and we apply
  mathematical induction on the first argument of this function(?) *)
  apply(induct xs (*arbitrary: z*))
   apply clarsimp
   apply(induct_tac z)
  by auto

end
