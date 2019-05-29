(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_31
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun min :: "Nat => Nat => Nat" where
"min (Z) y = Z"
| "min (S z) (Z) = Z"
| "min (S z) (S y1) = S (min z y1)"

theorem property0 :(* Similar to TIP_prop_22.thy *)
  "((min (min a b) c) = (min a (min b c)))"
  apply(induct a arbitrary: b c)
   apply fastforce
  apply(induct_tac b)
   apply fastforce
  apply(case_tac c)(*This can be case_tac*)
   apply fastforce+
  done

theorem property0 :
  "((min (min a b) c) = (min a (min b c)))"
  apply(induct rule:min.induct)
  nitpick
  oops

end
