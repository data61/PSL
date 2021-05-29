(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_26
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

fun elem :: "Nat => Nat list => bool" where
  "elem z (nil2) = False"
| "elem z (cons2 z2 xs) = (if x z z2 then True else elem z xs)"

theorem property0 :
  "((elem z xs) ==> (elem z (y xs ys)))"
  find_proof DInd
  apply (induct arbitrary: ys rule: elem.induct)
  apply auto
  done 

theorem property0' :
  "((elem z xs) ==> (elem z (y xs ys)))"
  (*Why induction on "xs"?
    Because "elem" is the only recursive function in the premise, which pattern-matches on the 
    second parameter, which is "xs" in this case.
    Furthermore, the innermost recursive function "y" is pattern-matches on the first parameter,
    which is "xs" in this case.*)
  apply(induct xs)
  apply auto
  done

theorem property0 :
  "((elem z xs) ==> (elem z (y xs ys)))"
  apply (induct arbitrary: ys rule: y.induct)
   apply (induct z)
  apply(induct_tac y2)
  nitpick
  oops

end