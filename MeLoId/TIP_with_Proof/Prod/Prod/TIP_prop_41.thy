(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_41
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun z :: "bool => bool => bool" where
  "z True y2 = y2"
| "z False y2 = False"

fun y :: "Nat => Nat => bool" where
  "y (Z) (Z) = True"
| "y (Z) (S z2) = False"
| "y (S x22) (Z) = False"
| "y (S x22) (S y22) = y x22 y22"

fun x :: "bool => bool => bool" where
  "x True y2 = True"
| "x False y2 = y2"

fun elem :: "Nat => Nat list => bool" where
  "elem x2 (nil2) = False"
| "elem x2 (cons2 z2 xs) = x (y x2 z2) (elem x2 xs)"

fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (nil2) y2 = nil2"
| "intersect (cons2 z2 xs) y2 =
     (if elem z2 y2 then cons2 z2 (intersect xs y2) else
        intersect xs y2)"

fun subset :: "Nat list => Nat list => bool" where
  "subset (nil2) y2 = True"
| "subset (cons2 z2 xs) y2 = z (elem z2 y2) (subset xs y2)"

theorem property0 :
  "((subset x2 y2) ==> ((intersect x2 y2) = x2))"
  oops

end
