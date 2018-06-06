(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_05
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

theorem property0 :
  "((length (rev y)) = (length y))"
  apply(induct rule:length.induct)(*rev.induct works as well. They are the same and return the same result.*)
   apply auto[1](*\<And>z does not appear in the goal. \<rightarrow> clarsimp*)
  apply clarsimp
  apply(subgoal_tac "\<And>za lenxs revxs. 
             TIP_prop_05.length revxs = lenxs \<Longrightarrow>
             TIP_prop_05.length (x revxs (cons2 za nil2)) = S lenxs")(*common sub-terms: revxs and lenxs*)
   apply fastforce
  apply(thin_tac "TIP_prop_05.length (TIP_prop_05.rev xs) = TIP_prop_05.length xs")
  apply(subgoal_tac "TIP_prop_05.length revxs = lenxs \<longrightarrow> TIP_prop_05.length (x revxs (cons2 za nil2)) = S lenxs")
   apply fastforce
  apply(thin_tac "TIP_prop_05.length revxs = lenxs")
  apply(rule meta_allI)(*because we cannot use the arbitrary keyword with induct_tac*)
  back nitpick quickcheck
  back nitpick quickcheck
  back
  apply (induct_tac revxs) (*equivalent to (induct revxs arbitrary: lenxs) due to meta_allI*)
   apply auto[1]
  apply auto[1]
  done

theorem alternative_proof: "((length (rev y)) = (length y))"
  apply(induct y)
   apply fastforce
  apply clarsimp
    (*common sub-term*)
  apply(subgoal_tac "\<And>x1 y rev_y length_y. length rev_y = length_y \<Longrightarrow> length (x rev_y (cons2 x1 nil2)) = S length_y")
   apply fastforce
  apply(thin_tac "TIP_prop_05.length (TIP_prop_05.rev y) = TIP_prop_05.length y")
  apply(subgoal_tac "TIP_prop_05.length rev_y = length_y \<longrightarrow> TIP_prop_05.length (x rev_y (cons2 x1a nil2)) = S length_y")
   apply fastforce
  apply(thin_tac "TIP_prop_05.length rev_y = length_y")
  apply(rule meta_allI)
  back nitpick quickcheck
  back nitpick quickcheck
  back nitpick quickcheck
  apply (induct_tac rev_y)
   apply auto
  done

end
