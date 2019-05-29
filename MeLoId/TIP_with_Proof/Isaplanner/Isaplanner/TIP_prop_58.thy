(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_58
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun zip :: "'a list => 'b list => (('a, 'b) pair) list" where
  "zip (nil2) y = nil2"
| "zip (cons2 z x2) (nil2) = nil2"
| "zip (cons2 z x2) (cons2 x3 x4) = cons2 (pair2 z x3) (zip x2 x4)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

theorem property0 :
  "((drop n (zip xs ys)) = (zip (drop n xs) (drop n ys)))"
  apply(induct n arbitrary: xs ys)
   apply fastforce
    (*Why "case_tac xs"?
    Because of "drop (S n) xs" and "drop"'s pattern-matching.*)
  apply(case_tac xs)
   apply fastforce
  apply clarsimp
    (*Why "case_tac ys"?
    Because of "zip (cons2 x21 x22) ys" and "drop (S n) ys" and
    the pattern-matching of "zip" and "drop".*)
  apply(case_tac ys)
   apply clarsimp
    (*Why "case_tac "(TIP_prop_58.drop n x22)"?
     "zip (TIP_prop_58.drop n x22) nil2"*)
   apply(case_tac "(TIP_prop_58.drop n x22)")(*"case_tac" instead of "cases" because "\<And>n x2." *)
    apply fastforce+
  done

theorem property0':
  "((drop n (zip xs ys)) = (zip (drop n xs) (drop n ys)))"
  apply(induct n arbitrary: xs ys)
   apply fastforce
  apply(induct_tac xs)
   apply fastforce
  apply clarsimp
  apply(case_tac ys)
   apply clarsimp
   apply(case_tac "(TIP_prop_58.drop n x2)")(*"case_tac" instead of "cases" because "\<And>n x2." *)
    apply fastforce+
  done

theorem property0'' :(*alternative proof with sledgehammer.*)
  "((drop n (zip xs ys)) = (zip (drop n xs) (drop n ys)))"
  apply(induct n arbitrary: xs ys)
   apply fastforce
  apply(induct_tac xs)
   apply fastforce
  apply clarsimp
  apply(case_tac ys)
   apply clarsimp
   apply (metis TIP_prop_58.list.distinct(1) zip.elims)
  apply fastforce+
  done

end