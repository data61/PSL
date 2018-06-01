(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_03
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

fun count :: "Nat => Nat list => Nat" where
  "count z (nil2) = Z"
| "count z (cons2 z2 ys) =
     (if x z z2 then S (count z ys) else count z ys)"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) y2 = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"

theorem property0 :
  "t2 (count n xs) (count n (y xs ys))"
  (*Why induction on xs?
    Because the innermost recursively defined constant "y" is defined recursively on the
    first parameter, which is "xs" in this case.
    Because "t2" is defined recursively on the first parameter, which is "count n xs" here,
    and "count" is defined recursively on the second parameter ("xs" in this case).*)
  apply(induct xs)
  (*auto can discharge these sub-goals.*)
   apply(subst count.simps)
   apply(subst t2.simps)
   apply(rule TrueI)
  apply(subst y.simps)
  apply(subst count.simps)
  apply(simp del:t2.simps)
  apply(subst t2.simps)
  apply(rule impI)
  apply(thin_tac "x n x1")
  apply assumption
  done

theorem property0' :
  "t2 (count n xs) (count n (y xs ys))"
  (*"xs" is optional.
    Other generalizations also work:
    "arbitrary: n"
    "arbitrary: n ys"
    "arbitrary: ys"
    "arbitrary: ys n"
    *)
  apply (induct xs arbitrary: n rule: TIP_prop_03.count.induct)
  apply auto
  done

theorem property0'' :
  "t2 (count n xs) (count n (y xs ys))"
  apply(induct n)
  (*This is bad:
    The first sub-goal is identical to the original goal.
   *)
  oops

theorem property0''' :
  "t2 (count n xs) (count n (y xs ys))"
  apply(induct rule:y.induct)
   apply fastforce
  nitpick
  oops

end