(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_10
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

theorem property0 :
  "((rev (rev y)) = y)"
  apply(induct y)(*"(induct rule: rev.induct)" is equally good.*)
   apply fastforce
  apply(subst rev.simps)
  (*common sub-term generalization*)
  apply(subgoal_tac "\<And>rev_y. rev (rev_y) = y \<longrightarrow> rev (x (rev_y) (cons2 x1 nil2)) = cons2 x1 y")
   apply fastforce
  apply(thin_tac "rev (rev y) = y")
  apply(rule meta_allI)
  back
  back
  back
  apply(induct_tac rev_y)
   apply auto
  done

theorem property0' :
  "((rev (rev y)) = y)"
  apply(induct rule:rev.induct) (*"(induct y)" is equally good*)
  apply fastforce
  apply(subst rev.simps)
  (*common sub-term generalization*)
  apply(subgoal_tac "\<And>rev_y. rev (rev_y) = xs \<longrightarrow> rev (x (rev_y) (cons2 z nil2)) = cons2 z xs")
   apply fastforce
  apply(thin_tac "rev (rev xs) = xs")
  apply(rule meta_allI)
  back
  back
  back
  apply(induct_tac rev_y)
   apply auto
  done
end