(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_escape_Injective
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Token = A | B | C | D | ESC | P | Q | R

fun isSpecial :: "Token => bool" where
"isSpecial x =
   (case x of
      ESC => True
      | P => True
      | Q => True
      | R => True
      | other => False)"

fun code :: "Token => Token" where
"code x =
   (case x of
      ESC => ESC
      | P => A
      | Q => B
      | R => C
      | other => x)"

fun escape :: "Token list => Token list" where
"escape (nil2) = nil2"
| "escape (cons2 y xs) =
     (if isSpecial y then cons2 ESC (cons2 (code y) (escape xs)) else
        cons2 y (escape xs))"

theorem property0 :
  "(((escape xs) = (escape ys)) ==> (xs = ys))"
  oops

end
