(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_sort_SSortCount
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun ssortminimum1 :: "int => int list => int" where
  "ssortminimum1 x (nil2) = x"
| "ssortminimum1 x (cons2 y1 ys1) =
     (if y1 <= x then ssortminimum1 y1 ys1 else ssortminimum1 x ys1)"

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
  "deleteBy x y (nil2) = nil2"
| "deleteBy x y (cons2 y2 ys) =
     (if (x y) y2 then ys else cons2 y2 (deleteBy x y ys))"

(*fun did not finish the proof*)
function ssort :: "int list => int list" where
  "ssort (nil2) = nil2"
| "ssort (cons2 y ys) =
     (let m :: int = ssortminimum1 y ys
     in cons2
          m
          (ssort
             (deleteBy
                (% (z :: int) => % (x2 :: int) => (z = x2)) m (cons2 y ys))))"
  by pat_completeness auto

fun count :: "'a => 'a list => int" where
  "count x (nil2) = 0"
| "count x (cons2 z ys) =
     (if (x = z) then 1 + (count x ys) else count x ys)"

theorem property0 :
  "((count x (ssort xs)) = (count x xs))"
  oops

end
