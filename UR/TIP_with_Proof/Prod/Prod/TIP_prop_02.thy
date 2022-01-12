(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_02
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

(*nested induction with generalization*)
theorem property0 :
  "((length (x y z)) = (length (x z y)))"
  (*why "induct y" rather than "induct z"?*)
  apply(induct y)
   apply auto[1]
   apply(induct z)
    apply fastforce+
    (*clarsimp can rewrite "length (x (cons2 x1 y) z)" to "S (length (x z y))"
      because "x" is defined recursively on the first argument.*)
  apply(subst x.simps)
  apply(subst length.simps)
  apply clarsimp(*This clarsimp uses induction hypothesis.*)
  apply(rule meta_allI)(*because we cannot use the arbitrary keyword with induct_tac*)
  back
  back
  back
  back
  apply (induct_tac z rule: TIP_prop_02.length.induct)(*z is optional*)
   apply auto
  done

theorem property0_again :
  "((length (x y z)) = (length (x z y)))"
  (*why "induct y" rather than "induct z"?
    \<rightarrow> Because "induct z" leads to the following step case:
    "TIP_prop_02.length (x y (cons2 x1 z)) = TIP_prop_02.length (x (cons2 x1 z) y)".
    Here we have different terms for the first argument of "x". *)
  apply(induct z arbitrary:)
   apply clarsimp
   apply(induct y arbitrary:)
    apply fastforce+
    (* This clarsimp does not rewrite "(x y (cons2 x1 z))"
       because "x" is defined recursively on the first argument.
       We can detect this problem just after applying "induct z".
       So, we cannot induct on the first argument of the innermost recursively defined function, "x".*)
  apply(subst x.simps)
  apply(subst length.simps)
  apply(drule HOL.sym)
  apply simp
  apply(rule meta_allI)(*because we cannot use the arbitrary keyword with induct_tac*)
  back
  back
  back
  back
  apply (induct_tac y rule: TIP_prop_02.length.induct)(*y is optional*)
  apply auto
  done

lemma aux_1_0:
  "S (TIP_prop_02.length (x z a)) = TIP_prop_02.length (x z (cons2 x1 a))"
  apply(induct z rule: TIP_prop_02.length.induct)
   apply clarsimp
  apply clarsimp
  done

lemma aux_1:
  "TIP_prop_02.length (x y z) = TIP_prop_02.length (x z y) \<Longrightarrow> 
   S (TIP_prop_02.length (x z y)) = TIP_prop_02.length (x z (cons2 x1 y))"
  apply(induct z)
   apply clarsimp
  apply clarsimp
  apply(rule aux_1_0)
  done

lemma aux_0:
  "TIP_prop_02.length z = TIP_prop_02.length (x z nil2)"
  apply(induct z)
   apply auto
  done

theorem property :
  "((length (x y z)) = (length (x z y)))"
  apply(induct y)
   apply clarsimp
   apply(rule aux_0)(*just a nested induction*)
  apply clarsimp
  apply(rule aux_1)(*just a nested induction*)
  apply assumption
  done

end
