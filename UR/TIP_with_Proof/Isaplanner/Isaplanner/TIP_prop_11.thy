(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_11
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

theorem property0 :
  "((drop Z xs) = xs)"
  find_proof DInd
  (*Why not "(induct rule:drop.induct)"?
    Because of the constant "Z" in "drop Z xs"(?)
    Because the resulting sub-goal 
    "\<And>z x2 x3. TIP_prop_11.
       drop z x3 = x3 \<Longrightarrow> 
       TIP_prop_11.drop (S z) (cons2 x2 x3) = cons2 x2 x3" is non-theorem.*)
  apply (induct xs rule:list.induct)
    (*"rule:list.induct" is optional:
   "induct xs" returns the same result with only different names of a variable.*)
   apply auto[1]
  apply(subst drop.simps(1))
  apply(rule_tac HOL.refl)
  done

end
