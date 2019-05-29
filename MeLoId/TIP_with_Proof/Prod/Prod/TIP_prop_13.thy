(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima and Kei Shirakizawa.*)
  theory TIP_prop_13
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun half :: "Nat => Nat" where
"half (Z) = Z"
| "half (S (Z)) = Z"
| "half (S (S z)) = S (half z)"

fun t2 :: "Nat => Nat => Nat" where
"t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

theorem property0 :
  "((half (t2 x x)) = x)"
  apply(induct x rule: half.induct)
    apply fastforce+
  (*Kei conjectured "\<And>n m. t2 n (S m) = t2 (S n) m"*)
  apply(subgoal_tac "\<And>n m. t2 n (S m) = t2 (S n) m")
   apply fastforce
  apply(thin_tac "half (t2 z z) = z")
  apply(induct_tac n)
   apply auto
  done

(*Conjecturing "\<And>n m. t2 n (S m) = t2 (S n) m" from
 *"\<And>z. half (t2 z z) = z \<Longrightarrow> half (t2 (S (S z)) (S (S z))) = S (S z)" is a hard task for machines.
 *In the following, we take a step-by-step approach.*)
theorem property04 :
  "((half (t2 x x)) = x)"
  apply(induct x rule: half.induct)
    apply fastforce+
  apply clarsimp
  (*Since "z" and "(S (S z))" in "t2 z (S (S z))" are of the same type and
   *"t2"'s pattern-matching is complete on the first argument...*)
  apply(subgoal_tac "(t2 z (S (S z))) = (t2 (S (S z)) z)")
   apply fastforce
  (*Since "S z" appears twice in "t2 z (S (S z)) = t2 (S (S z)) z", we generalize it.*)
  apply(subgoal_tac "\<And>z Sz. t2 z (S Sz) = t2 (S Sz) z")
   apply fastforce
  apply(thin_tac "half (t2 z z) = z")
  apply(induct_tac za)
   apply clarsimp
   apply(induct_tac Sz)
    apply fastforce+
  apply clarsimp
  apply(induct_tac Sz)
   apply fastforce+
  done

theorem property01 :
  "((half (t2 x x)) = x)"
  apply(induct x rule: half.induct)
    apply fastforce+
    (* "(t2 (S (S z)) (S (S z)))" in "half (t2 (S (S z)) (S (S z))) = S (S z)" is problematic:
   * t2's pattern matching is complete only on the first argument.
   * So, we want to rewrite "(t2 (S (S z)) (S (S z)))" to "t2 (S (S (S (S z))))".
   * Furthermore, "half"'s last clause can simplify "t2 (S (S (S (S z))))" very well. *)
  apply(subgoal_tac "(t2 (S (S z)) (S (S z))) = t2 (S (S (S (S z)))) z")
   apply fastforce
  apply clarsimp
  apply(thin_tac "half (t2 z z) = z")
  apply(subgoal_tac "t2 z (S (S z)) = t2 (S (S z)) z")
   apply fastforce
  apply(subgoal_tac "\<And>z Sz. t2 z (S Sz) = t2 (S Sz) z")
   apply fastforce
  apply(induct_tac za)
   apply clarsimp
   apply(induct_tac Sz)
    apply fastforce+
  apply clarsimp
  apply(induct_tac Sz)
   apply auto
  done

theorem property02 :
  "((half (t2 x x)) = x)"
  apply(induct x x rule:t2.induct)thm t2.induct
  quickcheck
  oops (*The induction step "\<And>z y. half (t2 y y) = y \<Longrightarrow> half (t2 y y) = y" is not useful at all.*)

theorem property03 :
  "((half (t2 x x)) = x)"
  apply(induct rule:t2.induct)thm t2.induct
  quickcheck
  oops

end
