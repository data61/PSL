(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_30
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun elem :: "Nat => Nat list => bool" where
  "elem y (nil2) = False"
| "elem y (cons2 z2 xs) = (if x y z2 then True else elem y xs)"

fun t2 :: "Nat => Nat => bool" where
  "t2 y (Z) = False"
| "t2 (Z) (S z2) = True"
| "t2 (S x2) (S z2) = t2 x2 z2"
  (*t2 x y = x < y*)

fun ins :: "Nat => Nat list => Nat list" where
  "ins y (nil2) = cons2 y (nil2)"
| "ins y (cons2 z2 xs) =
     (if t2 y z2 then cons2 y (cons2 z2 xs) else cons2 z2 (ins y xs))"

theorem property0 :
  "elem y (ins y xs)"
  (*why induction on "xs" instead of y?
    Because the innermost recursive function, ins, is defined with the case distinction
    on the second argument.
    Because "y" appears in two different places.*)
  apply(induct xs (*arbitrary: y*))(*generalization is optional.*)
   apply clarsimp
   apply(induct_tac y)
    apply auto[1]
   apply auto[1]
  apply clarsimp(*This clarsimp uses the induction hypothesis.*)
    (*without the meta-universal quantifier the following induction becomes unnecessarily hard.*)
    (*Why "\<And>y. x y y"?
      because of "\<not> x y y" in the premises.*)
  apply(subgoal_tac "\<And>y. x y y")
   apply fastforce
  apply(induct_tac ya)
  by auto

end
