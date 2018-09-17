(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_01
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S y) = S (S (double y))"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

(* manipulation of sub-terms (t2 x (S x) = t2 (S x) x)) and generalization by renaming.*)
theorem property0 :
  "((double x) = (t2 x x))"
  apply(induct x)
   apply simp
  apply clarsimp
  apply(subgoal_tac
      "(\<And>x. t2 x (S x) = t2 (S x) x) &&& 
     (\<And>x. double x = t2 x x \<Longrightarrow> S (t2 x x) = t2 (S x) x)")
   apply presburger
  apply(thin_tac "double x = t2 x x")
  apply (rule conjunctionI)
   apply simp(*mostly to get rid of x, a bit of simplification as well*)
   apply(subgoal_tac "(\<And>x y. t2 x (S y) = S (t2 x y))")(*generalization by renaming*)
    apply presburger
   apply simp(*to get rid of xa*)
   apply(induct_tac x)
    apply auto[1]
   apply auto[1]
  apply auto[1]
  done

end
