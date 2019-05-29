(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_07
  imports "../../Test_Base" "../../../src/Build_Database/Build_Database"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil2) y = y"
| "qrev (cons2 z xs) y = qrev xs (cons2 z y)"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 y xs) = S (length xs)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

theorem property0 :
  "((length (qrev x y)) = (t2 (length x) (length y)))"
  apply(induct x arbitrary: y (*rule: TIP_prop_07.length.induct*))
   apply auto[1]
  apply(subst qrev.simps)
    (*Note that we insert only the conclusion.*)
  apply(subgoal_tac
      "length (qrev x (cons2 x1 y)) = S (length (qrev x y)) &&&
    S (length (qrev x y)) = t2 (length (cons2 x1 x)) (length y)")
   apply presburger
  apply(rule conjunctionI)
   apply(thin_tac "(\<And>y. TIP_prop_07.length (qrev x y) = t2 (TIP_prop_07.length x) (TIP_prop_07.length y))")
   apply(rule meta_allI)
   back
   back
   back
   back
   apply(rule meta_allI)
   back
   back
   back
   apply(induct_tac rule: TIP_prop_07.length.induct)(*Note that "induct" does not work here.*)
    apply fastforce+
  done

end