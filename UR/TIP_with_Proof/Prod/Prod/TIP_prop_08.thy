(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_08
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

lemma drop_nil: "drop n nil2 = nil2"
  by(case_tac n, auto)

(*
lemma drop_succ: "drop (S n) (drop m l) = drop n (drop (S m) l)"
  apply(induction l)
   apply(simp add: drop_nil, simp)
  apply(induction m, auto)
  apply(case_tac l, simp add: drop_nil, auto)
  done

theorem property0 :
  "((drop x (drop y z)) = (drop y (drop x z)))"
  apply(induct z rule: drop.induct, auto)
  apply(case_tac y, auto)
  apply(simp add: drop_succ)
  done
*)

lemma bottom_up_nested_drop_and_S:
  "drop (S n) (drop m l) = drop n (drop (S m) l)"
  apply(induct l)
   apply (simp add: drop_nil)
  apply clarsimp
  apply(induct m)
   apply fastforce
  apply clarsimp
  apply(case_tac l)(*sledgehammer can solve this as well*)
   apply(simp add: drop_nil)+
  done

(* declare [[show_types]] *)
(* Due to the fixed type variable caused by the "assumes" keyword, we cannot use the standard 
 * technique for abductive reasoning. *)
(*
lemma subgoal_as_a_separate_lemma:
 (*assumes "TIP_prop_08.drop (S (n::Nat)) (TIP_prop_08.drop (m::Nat) (l::'a TIP_prop_08.list)) = TIP_prop_08.drop n (TIP_prop_08.drop (S m) l)"*)
  shows "drop    z  (drop y           x3 ) = drop y (drop z x3) \<Longrightarrow>
         drop (S z) (drop y (cons2 x2 x3)) = drop y (drop z x3)"
  apply(simp add: bottom_up_nested_drop_and_S)
  done
*)
theorem property: "((drop x (drop y z)) = (drop y (drop x z)))"
  apply(induct z rule: drop.induct)
    apply (simp add: drop_nil)
   apply (simp add: drop_nil)
  apply clarsimp
  by (simp add: bottom_up_nested_drop_and_S)

end