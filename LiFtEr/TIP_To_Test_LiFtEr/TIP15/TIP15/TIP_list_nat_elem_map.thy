(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_nat_elem_map
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun map :: "('a => 'b) => 'a list => 'b list" where
"map f (nil2) = nil2"
| "map f (cons2 y xs) = cons2 (f y) (map f xs)"

fun elem :: "'a => 'a list => bool" where
"elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"

theorem property0 :
  "((elem y (map f xs)) ==>
      (? (x :: 'a) . (((f x) = y) & (elem y xs))))"
  oops

end
