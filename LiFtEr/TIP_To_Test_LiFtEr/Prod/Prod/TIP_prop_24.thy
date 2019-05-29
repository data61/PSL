(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_prop_24
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun even :: "Nat => bool" where
  "even (Z) = True"
| "even (S (Z)) = False"
| "even (S (S z)) = even z"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

theorem property0 :
  "((even (t2 x y)) = (even (t2 y x)))"
  oops

end
