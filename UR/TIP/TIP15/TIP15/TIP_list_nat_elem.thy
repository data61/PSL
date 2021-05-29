(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_elem
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => Nat => 'a" where
"x (cons2 z2 x2) (Z) = z2"
| "x (cons2 z2 x2) (S x3) = x x2 x3"

fun elem :: "'a => 'a list => bool" where
"elem y (nil2) = False"
| "elem y (cons2 z2 xs) = ((z2 = y) | (elem y xs))"

theorem property0 :
  "((elem y xs) ==> (? (z :: Nat) . (y = (x xs z))))"
  oops

end
