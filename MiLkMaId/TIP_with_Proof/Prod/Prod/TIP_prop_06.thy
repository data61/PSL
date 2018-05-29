(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_06
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"
print_theorems
fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) z = z"
| "t2 (S z2) z = S (t2 z2 z)"

theorem property0 :
  "((length (rev (x y z))) = (t2 (length y) (length z)))"
  apply(subgoal_tac "length (rev (x y z)) = length (x y z) &&&
                     length (x y z) = t2 (length y) (length z)")
    apply presburger
   apply(subgoal_tac "\<And>z. length (rev z) = length z")(*common sub-term: z*)
    apply fastforce
   apply(induct_tac rule:length.induct)(*rev.induct works as well. They are the same and return the same result.*)
    apply auto[1](*\<And>z does not appear in the goal. \<rightarrow> clarsimp*)
   apply clarsimp
   apply(subgoal_tac "\<And>za lenxs revxs. 
             TIP_prop_06.length revxs = lenxs \<Longrightarrow>
             TIP_prop_06.length (x revxs (cons2 za nil2)) = S lenxs")(*common sub-terms: revxs and lenxs*)
    apply fastforce
   apply(thin_tac "TIP_prop_06.length (TIP_prop_06.rev xs) = TIP_prop_06.length xs")
    (*induction variable occurs in the meta-premise and meta-universally quantified \<rightarrow> induct is not applicable.*)
   apply(subgoal_tac "TIP_prop_06.length revxs = lenxs \<longrightarrow> TIP_prop_06.length (x revxs (cons2 zaa nil2)) = S lenxs")
    apply fastforce
   apply(thin_tac "TIP_prop_06.length revxs = lenxs")
   apply(rule meta_allI)(*because we cannot use the arbitrary keyword with induct_tac*)
   back
   back
   back
   apply (induct_tac revxs) (*equivalent to (induct revxs arbitrary: lenxs) due to meta_allI*)
    apply auto[1]
   apply auto[1]
  apply(induct rule:x.induct)
   apply auto
  done

end
