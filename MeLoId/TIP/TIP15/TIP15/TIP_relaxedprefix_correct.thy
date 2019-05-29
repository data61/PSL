(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_relaxedprefix_correct
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype It = A | B | C

fun removeOne :: "It => (It list) list => (It list) list" where
"removeOne x (nil2) = nil2"
| "removeOne x (cons2 z x2) = cons2 (cons2 x z) (removeOne x x2)"

fun removeOne2 :: "It list => (It list) list" where
"removeOne2 (nil2) = nil2"
| "removeOne2 (cons2 y xs) =
     cons2 xs (removeOne y (removeOne2 xs))"

fun or2 :: "bool list => bool" where
"or2 (nil2) = False"
| "or2 (cons2 y xs) = (y | (or2 xs))"

fun isPrefix :: "It list => It list => bool" where
"isPrefix (nil2) y = True"
| "isPrefix (cons2 z x2) (nil2) = False"
| "isPrefix (cons2 z x2) (cons2 x3 x4) =
     ((z = x3) & (isPrefix x2 x4))"

fun isRelaxedPrefix :: "It list => It list => bool" where
"isRelaxedPrefix (nil2) y = True"
| "isRelaxedPrefix (cons2 z (nil2)) y = True"
| "isRelaxedPrefix (cons2 z (cons2 x3 x4)) (nil2) = False"
| "isRelaxedPrefix (cons2 z (cons2 x3 x4)) (cons2 x5 x6) =
     (if (z = x5) then isRelaxedPrefix (cons2 x3 x4) x6 else
        isPrefix (cons2 x3 x4) (cons2 x5 x6))"

fun spec :: "It list => (It list) list => bool list" where
"spec ys (nil2) = nil2"
| "spec ys (cons2 y z) = cons2 (isPrefix y ys) (spec ys z)"

fun spec2 :: "It list => It list => bool" where
"spec2 x y = or2 (spec y (cons2 x (removeOne2 x)))"

theorem property0 :
  "((isRelaxedPrefix xs ys) = (spec2 xs ys))"
  oops

end
