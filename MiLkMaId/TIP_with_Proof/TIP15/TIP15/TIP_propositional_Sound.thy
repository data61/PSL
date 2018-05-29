(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_propositional_Sound
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Form = x "Form" "Form" | Not "Form" | Var "int"

fun z :: "'a list => 'a list => 'a list" where
  "z (nil2) y2 = y2"
| "z (cons2 z2 xs) y2 = cons2 z2 (z xs y2)"

fun y :: "int => ((int, bool) pair) list => bool list" where
  "y x2 (nil2) = nil2"
| "y x2 (cons2 (pair2 y22 True) x22) = cons2 (x2 = y22) (y x2 x22)"
| "y x2 (cons2 (pair2 y22 False) x22) = y x2 x22"

fun or2 :: "bool list => bool" where
  "or2 (nil2) = False"
| "or2 (cons2 y2 xs) = (y2 | (or2 xs))"

fun models7 :: "int => ((int, bool) pair) list =>
                ((int, bool) pair) list" where
  "models7 x2 (nil2) = nil2"
| "models7 x2 (cons2 z2 xs) =
     (if (x2 ~= (case z2 of pair2 x22 y22 => x22)) then
        cons2 z2 (models7 x2 xs)
        else
        models7 x2 xs)"

fun models6 :: "int => ((int, bool) pair) list => bool list" where
  "models6 x2 (nil2) = nil2"
| "models6 x2 (cons2 (pair2 y22 True) x22) = models6 x2 x22"
| "models6 x2 (cons2 (pair2 y22 False) x22) =
     cons2 (x2 = y22) (models6 x2 x22)"

fun models5 :: "int => ((int, bool) pair) list =>
                ((int, bool) pair) list" where
  "models5 x2 (nil2) = nil2"
| "models5 x2 (cons2 z2 xs) =
     (if (x2 ~= (case z2 of pair2 x22 y22 => x22)) then
        cons2 z2 (models5 x2 xs)
        else
        models5 x2 xs)"

fun models4 :: "int => ((int, bool) pair) list => bool list" where
  "models4 x2 (nil2) = nil2"
| "models4 x2 (cons2 (pair2 y22 True) x22) =
     cons2 (x2 = y22) (models4 x2 x22)"
| "models4 x2 (cons2 (pair2 y22 False) x22) = models4 x2 x22"

function models :: "(((int, bool) pair) list) list => Form =>
                    (((int, bool) pair) list) list => (((int, bool) pair) list) list"
  and
  models2 :: "Form => (((int, bool) pair) list) list =>
                     (((int, bool) pair) list) list"
  and
  models3 :: "Form => ((int, bool) pair) list =>
                     (((int, bool) pair) list) list" where
  "models x2 q (nil2) = models2 q x2"
| "models x2 q (cons2 z2 x22) = cons2 z2 (models x2 q x22)"
| "models2 q (nil2) = nil2"
| "models2 q (cons2 y2 z2) = models z2 q (models3 q y2)"
| "models3 (x p q) y2 = models2 q (models3 p y2)"
| "models3 (Not (x r q2)) y2 =
     z (models3 (Not r) y2) (models3 (x r (Not q2)) y2)"
| "models3 (Not (Not p2)) y2 = models3 p2 y2"
| "models3 (Not (Var x22)) y2 =
     (if (~ (or2 (models4 x22 y2))) then
        cons2 (cons2 (pair2 x22 False) (models5 x22 y2)) (nil2)
        else
        nil2)"
| "models3 (Var x3) y2 =
     (if (~ (or2 (models6 x3 y2))) then
        cons2 (cons2 (pair2 x3 True) (models7 x3 y2)) (nil2)
        else
        nil2)"
  by pat_completeness auto

fun t2 :: "((int, bool) pair) list => Form => bool" where
  "t2 x2 (x p q) = ((t2 x2 p) & (t2 x2 q))"
| "t2 x2 (Not r) = (~ (t2 x2 r))"
| "t2 x2 (Var z2) = or2 (y z2 x2)"

fun formula :: "Form => (((int, bool) pair) list) list =>
              bool" where
  "formula p (nil2) = True"
| "formula p (cons2 y2 xs) = ((t2 y2 p) & (formula p xs))"

theorem property0 :
  "formula p (models3 p (nil2))"
  oops

end
