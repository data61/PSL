(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_sort_NStoogeSort2Permutes
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

(*fun did not finish the proof*)
function twoThirds :: "int => int" where
  "twoThirds y =
   (if (y = 2) then 1 else
      (if (y = 1) then 1 else
         (if (y = 0) then 0 else 2 + (twoThirds (y - 3)))))"
  by pat_completeness auto

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

fun length :: "'a list => int" where
  "length (nil2) = 0"
| "length (cons2 z l) = 1 + (length l)"

fun elem :: "'a => 'a list => bool" where
  "elem y (nil2) = False"
| "elem y (cons2 z2 xs) = ((z2 = y) | (elem y xs))"

fun drop :: "int => 'a list => 'a list" where
  "drop y z =
   (if y <= 0 then z else
      (case z of
         nil2 => nil2
         | cons2 z2 xs1 => drop (y - 1) xs1))"

fun splitAt :: "int => 'a list =>
                (('a list), ('a list)) pair" where
  "splitAt y z = pair2 (take y z) (drop y z)"

function nstooge2sort2 :: "int list => int list"
  and nstoogesort2 :: "int list => int list"
  and nstooge2sort1 :: "int list => int list" where
  "nstooge2sort2 y =
   (case splitAt (twoThirds (length y)) y of
      pair2 ys2 zs1 => x (nstoogesort2 ys2) zs1)"
| "nstoogesort2 (nil2) = nil2"
| "nstoogesort2 (cons2 z (nil2)) = cons2 z (nil2)"
| "nstoogesort2 (cons2 z (cons2 y2 (nil2))) = sort2 z y2"
| "nstoogesort2 (cons2 z (cons2 y2 (cons2 x3 x4))) =
     nstooge2sort2
       (nstooge2sort1 (nstooge2sort2 (cons2 z (cons2 y2 (cons2 x3 x4)))))"
| "nstooge2sort1 y =
     (case splitAt (third (length y)) y of
        pair2 ys2 zs1 => x ys2 (nstoogesort2 zs1))"
  by pat_completeness auto

fun deleteBy :: "('a => ('a => bool)) => 'a => 'a list =>
                 'a list" where
  "deleteBy y z (nil2) = nil2"
| "deleteBy y z (cons2 y2 ys) =
     (if (y z) y2 then ys else cons2 y2 (deleteBy y z ys))"

fun isPermutation :: "'a list => 'a list => bool" where
  "isPermutation (nil2) (nil2) = True"
| "isPermutation (nil2) (cons2 z2 x2) = False"
| "isPermutation (cons2 x3 xs) z =
     ((elem x3 z) &
        (isPermutation
           xs (deleteBy (% (x4 :: 'a) => % (x5 :: 'a) => (x4 = x5)) x3 z)))"

theorem property0 :
  "isPermutation (nstoogesort2 xs) xs"
  oops

end
