(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_rotate_snoc
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun snoc :: "'a => 'a list => 'a list" where
"snoc x (nil2) = cons2 x (nil2)"
| "snoc x (cons2 z ys) = cons2 z (snoc x ys)"

fun rotate :: "Nat => 'a list => 'a list" where
"rotate (Z) y = y"
| "rotate (S z) (nil2) = nil2"
| "rotate (S z) (cons2 z2 xs1) = rotate z (snoc z2 xs1)"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun length :: "'a list => Nat" where
"length (nil2) = Z"
| "length (cons2 y l) = plus (S Z) (length l)"

theorem property0 :
  "((rotate (length xs) xs) = xs)"
  oops

end
