(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_57
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil2"
| "take (S z) (nil2) = nil2"
| "take (S z) (cons2 x2 x3) = cons2 x2 (take z x3)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = Z"
| "t2 (S z) (Z) = S z"
| "t2 (S z) (S x2) = t2 z x2"

theorem property0 :
  "((drop n (take m xs)) = (take (t2 m n) (drop n xs)))"
  apply(induct m arbitrary: n xs)(*These generalizations are necessary.*)
   apply clarsimp
   apply(case_tac n)
    apply fastforce+
  apply(case_tac n)
   apply fastforce
  apply clarsimp
  apply(case_tac xs)
   apply clarsimp
   apply(case_tac "(t2 m x2)")
    apply fastforce+
  done


theorem property0':(*alternative proof with "induct"*)
  "((drop n (take m xs)) = (take (t2 m n) (drop n xs)))"
  apply(induct m arbitrary: n xs)
  subgoal
    apply induct
     apply auto
    done
  apply(case_tac n)
   apply fastforce
  apply clarsimp
  apply(case_tac xs)
   apply clarsimp
   apply(case_tac "(t2 m x2)")
    apply fastforce+
  done

theorem property0'' :(*alternative proof with sledgehammer*)
  "((drop n (take m xs)) = (take (t2 m n) (drop n xs)))"
  apply(induct m arbitrary: n xs)(*These generalizations are necessary.*)
   apply clarsimp
  apply (metis Nat.exhaust TIP_prop_57.drop.simps(1) TIP_prop_57.drop.simps(2))
  apply(case_tac n)
  apply fastforce
  apply clarsimp
  apply (metis (no_types, hide_lams) TIP_prop_57.drop.simps(2) TIP_prop_57.drop.simps(3) TIP_prop_57.list.exhaust TIP_prop_57.take.simps(2) TIP_prop_57.take.simps(3) take.elims)
  done

end