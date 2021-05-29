(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_NStoogeSortCount
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

(*fun did not finish the proof*)
function third :: "int => int" where
  "third y =
   (if (y = 2) then 0 else
      (if (y = 1) then 0 else
         (if (y = 0) then 0 else 1 + (third (y - 3)))))"
  by pat_completeness auto

fun take :: "int => 'a list => 'a list" where
  "take y z =
   (if y <= 0 then nil2 else
      (case z of
         nil2 => nil2
         | cons2 z2 xs => cons2 z2 (take (y - 1) xs)))"

fun sort2 :: "int => int => int list" where
  "sort2 y z =
   (if y <= z then cons2 y (cons2 z (nil2)) else
      cons2 z (cons2 y (nil2)))"

fun reverse :: "'a list => 'a list" where
  "reverse (nil2) = nil2"
| "reverse (cons2 z xs) = x (reverse xs) (cons2 z (nil2))"

fun length :: "'a list => int" where
  "length (nil2) = 0"
| "length (cons2 z l) = 1 + (length l)"

fun drop :: "int => 'a list => 'a list" where
  "drop y z =
   (if y <= 0 then z else
      (case z of
         nil2 => nil2
         | cons2 z2 xs1 => drop (y - 1) xs1))"

fun splitAt :: "int => 'a list =>
                (('a list), ('a list)) pair" where
  "splitAt y z = pair2 (take y z) (drop y z)"

function nstooge1sort2 :: "int list => int list"
  and nstoogesort :: "int list => int list"
  and nstooge1sort1 :: "int list => int list" where
  "nstooge1sort2 y =
   (case splitAt (third (length y)) (reverse y) of
      pair2 ys2 zs2 => x (nstoogesort zs2) (reverse ys2))"
| "nstoogesort (nil2) = nil2"
| "nstoogesort (cons2 z (nil2)) = cons2 z (nil2)"
| "nstoogesort (cons2 z (cons2 y2 (nil2))) = sort2 z y2"
| "nstoogesort (cons2 z (cons2 y2 (cons2 x3 x4))) =
     nstooge1sort2
       (nstooge1sort1 (nstooge1sort2 (cons2 z (cons2 y2 (cons2 x3 x4)))))"
| "nstooge1sort1 y =
     (case splitAt (third (length y)) y of
        pair2 ys2 zs1 => x ys2 (nstoogesort zs1))"
  by pat_completeness auto

fun count :: "'a => 'a list => int" where
  "count y (nil2) = 0"
| "count y (cons2 z2 ys) =
     (if (y = z2) then 1 + (count y ys) else count y ys)"

theorem property0 :
  "((count y (nstoogesort xs)) = (count y xs))"
  oops

end
