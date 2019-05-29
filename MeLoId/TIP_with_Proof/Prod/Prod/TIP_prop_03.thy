(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
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

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) z = z"
| "t2 (S z2) z = S (t2 z2 z)"

(* This apply-style proof script repeats the proof of "t2 n m = t2 m n" twice,
 * whereas Kei's original proof script caches "t2 n m = t2 m n". *)
theorem property0 :
  "((length (x y z)) = (t2 (length z) (length y)))"
  apply(induct y)
   apply simp
   apply(subgoal_tac "\<And>n m. t2 n m = t2 m n")(*(meta-)universal quantifiers are necessary.*)
    apply fastforce
   apply(induct_tac n)
    apply simp
    apply(induct_tac m)
     apply fastforce+
   apply clarsimp
   apply(case_tac m)
    apply fastforce+
   apply(thin_tac "m = S x2")
   apply(thin_tac "t2 x m = t2 m x")
   apply(induct_tac m)
    apply fastforce+
  apply(case_tac z)
   apply fastforce
  apply(subgoal_tac "\<And>n m. t2 n m = t2 m n")(*(meta-)universal quantifiers are necessary.*)
   apply fastforce
  apply(thin_tac "TIP_prop_03.length (x y z) = t2 (TIP_prop_03.length z) (TIP_prop_03.length y)")
  apply(thin_tac "z = cons2 x21 x22")
  apply(induct_tac n)
   apply simp
   apply(induct_tac m)
    apply fastforce+
  apply clarsimp
  apply(case_tac m)
   apply fastforce+
  apply(thin_tac "m = S x2")
  apply(thin_tac "t2 x m = t2 m x")
  apply(induct_tac m)
   apply fastforce+
  done

end