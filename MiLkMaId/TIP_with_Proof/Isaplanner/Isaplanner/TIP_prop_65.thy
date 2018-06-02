(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_65
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t22 :: "Nat => Nat => Nat" where
  "t22 (Z) y = y"
| "t22 (S z) y = S (t22 z y)"

fun t2 :: "Nat => Nat => bool" where
  "t2 x (Z) = False"
| "t2 (Z) (S z) = True"
| "t2 (S x2) (S z) = t2 x2 z"

lemma "t2 i (S_t22_m_i) \<Longrightarrow> t2 i (S S_t22_m_i)"
  apply(induct S_t22_m_i rule:t2.induct)
  apply fastforce+
  oops

theorem property0 :
  "t2 i (S (t22 m i))"
  (*"induct m" is the natural choice as the innermost recursive function "t22" is defined 
   recursively on its first argument, which is "m" in this case and
   the other recursive function "t2" is defined recursively on the second argument, which is
   "t22 m i" in this case.
 *)
  apply(induct m)
   apply clarsimp
   apply(induct_tac i)(*"i" is the only variable*)
    apply fastforce+
  apply clarsimp
    (*generalization "t22 m i" \<rightarrow> "t22_m_i".
      A stronger generalization "(S (t22_m_i))" \<rightarrow> "S_t22_m_i" would be less optimal,
      since it blocks Isabelle using pattern-matching on "S" for "t2.simps"(?) *)
  apply(subgoal_tac "\<And>t22_m_i. t2 i (S (t22_m_i)) \<Longrightarrow> t2 i (S (S (t22_m_i)))")
   apply fastforce
  apply(thin_tac "t2 i (S (t22 m i))")
  apply clarsimp
  apply(subgoal_tac "\<And>t22_m_i. t2 i (S t22_m_i) \<longrightarrow> t2 i (S (S t22_m_i))")
   apply fastforce
  apply(thin_tac "t2 i (S t22_m_i)")
  apply (induct_tac t22_m_ia i rule: t2.induct)
    apply auto
  done

end