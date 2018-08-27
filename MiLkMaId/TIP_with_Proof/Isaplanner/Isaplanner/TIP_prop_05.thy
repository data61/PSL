(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
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
print_theorems
fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun count :: "Nat => Nat list => Nat" where
  "count y (nil2) = Z"
| "count y (cons2 z2 ys) =
     (if x y z2 then S (count y ys) else count y ys)"

theorem property0 :
  "((n = y) ==> ((S (count n xs)) = (count n (cons2 y xs))))"
  apply(induct y arbitrary: n xs)
   apply fastforce
  apply clarsimp
    (*Why "induct_tac xs"?
    *Because the pattern-matching of the innermost recursive constant (count) is complete
    *on the second argument (here xs), which is universally quantified with \<And>.*)
  apply(induct_tac xs)
   defer
   apply auto[1]
  apply(subgoal_tac "x y y")
   apply fastforce
  apply(thin_tac "\<not> x y y")
  apply(thin_tac "(\<And>n xs. n = y \<Longrightarrow> S (count y xs) = count y xs)")
  apply(induct_tac y)
   apply auto
  done

end