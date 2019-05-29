(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_59
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun last :: "Nat list => Nat" where
  "last (nil2) = Z"
| "last (cons2 z (nil2)) = z"
| "last (cons2 z (cons2 x2 x3)) = last (cons2 x2 x3)"

theorem property0 :
  "((ys = (nil2)) ==> ((last (x xs ys)) = (last xs)))"
  find_proof DInd
  apply (induct rule: TIP_prop_59.last.induct)
    apply auto
  done

theorem property0' :(*sub-optimal proof*)
  "((ys = (nil2)) ==> ((last (x xs ys)) = (last xs)))"
  apply (induct xs)
   apply auto[1]
  apply clarsimp
    (*Why "case_tac xs"?
    Because we want to simplify "last (cons2 x1 (x xs nil2))" using last.simps(3).
    and we need to pattern-match on "xs" to use x.simps(2).
   *)
  apply(case_tac xs)
   apply fastforce+
  done

end