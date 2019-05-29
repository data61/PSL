(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_23
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun max :: "Nat => Nat => Nat" where
  "max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S x2) = S (max z x2)"

theorem property0 :
  "((max a b) = (max b a))"
  (*why "induct a arbitrary: b" rather than "induct b arbitrary: a"?
    \<rightarrow> both work well.*)
  apply(induct a arbitrary: b)
   apply(induct_tac b)(*"case_tac" works well. See below.*)
    apply fastforce+
  apply(induct_tac b)(*"case_tac" works well. See below.*)
   apply fastforce+
  done

theorem property0' :
  "((max a b) = (max b a))"
  apply(induct a arbitrary: b)
   apply (case_tac b)
    apply fastforce+
  apply (case_tac b)
   apply fastforce+
  done

theorem property0'' :
  "((max a b) = (max b a))"
  apply(induct b arbitrary: a)
   apply (induct_tac a)
    apply fastforce+
  apply (induct_tac a)
   apply fastforce+
  done

theorem property0''' :
  "((max a b) = (max b a))"
  apply(induct b arbitrary: a)
   apply (case_tac a)
    apply fastforce+
  apply (case_tac a)
   apply fastforce+
  done

end