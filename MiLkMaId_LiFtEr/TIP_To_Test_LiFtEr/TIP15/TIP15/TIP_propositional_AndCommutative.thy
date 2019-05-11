(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_propositional_AndCommutative
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Form = x "Form" "Form" | Not "Form" | Var "int"

fun y :: "'a list => 'a list => 'a list" where
  "y (nil2) y2 = y2"
| "y (cons2 z2 xs) y2 = cons2 z2 (y xs y2)"

fun or2 :: "bool list => bool" where
  "or2 (nil2) = False"
| "or2 (cons2 y2 xs) = (y2 | (or2 xs))"

fun models7 :: "int => ((int, bool) pair) list =>
                ((int, bool) pair) list" where
  "models7 z (nil2) = nil2"
| "models7 z (cons2 z2 xs) =
     (if (z ~= (case z2 of pair2 x2 y22 => x2)) then
        cons2 z2 (models7 z xs)
        else
        models7 z xs)"

fun models6 :: "int => ((int, bool) pair) list => bool list" where
  "models6 z (nil2) = nil2"
| "models6 z (cons2 (pair2 y22 True) x2) = models6 z x2"
| "models6 z (cons2 (pair2 y22 False) x2) =
     cons2 (z = y22) (models6 z x2)"

fun models5 :: "int => ((int, bool) pair) list =>
                ((int, bool) pair) list" where
  "models5 z (nil2) = nil2"
| "models5 z (cons2 z2 xs) =
     (if (z ~= (case z2 of pair2 x2 y22 => x2)) then
        cons2 z2 (models5 z xs)
        else
        models5 z xs)"

fun models4 :: "int => ((int, bool) pair) list => bool list" where
  "models4 z (nil2) = nil2"
| "models4 z (cons2 (pair2 y22 True) x2) =
     cons2 (z = y22) (models4 z x2)"
| "models4 z (cons2 (pair2 y22 False) x2) = models4 z x2"

function models :: "(((int, bool) pair) list) list => Form =>
                    (((int, bool) pair) list) list => (((int, bool) pair) list) list"
  and
  models2 :: "Form => (((int, bool) pair) list) list =>
                     (((int, bool) pair) list) list"
  and
  models3 :: "Form => ((int, bool) pair) list =>
                     (((int, bool) pair) list) list" where
  "models z q (nil2) = models2 q z"
| "models z q (cons2 z2 x2) = cons2 z2 (models z q x2)"
| "models2 q (nil2) = nil2"
| "models2 q (cons2 y2 z2) = models z2 q (models3 q y2)"
| "models3 (x p q) y2 = models2 q (models3 p y2)"
| "models3 (Not (x r q2)) y2 =
     y (models3 (Not r) y2) (models3 (x r (Not q2)) y2)"
| "models3 (Not (Not p2)) y2 = models3 p2 y2"
| "models3 (Not (Var x2)) y2 =
     (if (~ (or2 (models4 x2 y2))) then
        cons2 (cons2 (pair2 x2 False) (models5 x2 y2)) (nil2)
        else
        nil2)"
| "models3 (Var x3) y2 =
     (if (~ (or2 (models6 x3 y2))) then
        cons2 (cons2 (pair2 x3 True) (models7 x3 y2)) (nil2)
        else
        nil2)"
  by pat_completeness auto

fun valid :: "Form => bool" where
  "valid z =
   (case models3 (Not z) (nil2) of
      nil2 => True
      | cons2 y2 z2 => False)"

theorem property0 :
  "((valid (x p q)) = (valid (x q p)))"
  oops

end
