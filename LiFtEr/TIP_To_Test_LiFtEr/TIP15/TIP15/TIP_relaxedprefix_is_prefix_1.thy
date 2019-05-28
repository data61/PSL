(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_relaxedprefix_is_prefix_1
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype It = A | B | C

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun isPrefix :: "It list => It list => bool" where
"isPrefix (nil2) z = True"
| "isPrefix (cons2 z2 x2) (nil2) = False"
| "isPrefix (cons2 z2 x2) (cons2 x3 x4) =
     ((z2 = x3) & (isPrefix x2 x4))"

fun isRelaxedPrefix :: "It list => It list => bool" where
"isRelaxedPrefix (nil2) z = True"
| "isRelaxedPrefix (cons2 z2 (nil2)) z = True"
| "isRelaxedPrefix (cons2 z2 (cons2 x3 x4)) (nil2) = False"
| "isRelaxedPrefix (cons2 z2 (cons2 x3 x4)) (cons2 x5 x6) =
     (if (z2 = x5) then isRelaxedPrefix (cons2 x3 x4) x6 else
        isPrefix (cons2 x3 x4) (cons2 x5 x6))"

theorem property0 :
  "isRelaxedPrefix xs (x xs ys)"
  oops

end
