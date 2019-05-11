(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_13
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun half :: "Nat => Nat" where
"half (Z) = Z"
| "half (S (Z)) = Z"
| "half (S (S z)) = S (half z)"

fun t2 :: "Nat => Nat => Nat" where
"t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

theorem property0 :
  "((half (t2 x x)) = x)"
  oops

end
