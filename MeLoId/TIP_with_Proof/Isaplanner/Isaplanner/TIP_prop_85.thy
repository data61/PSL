(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_85
imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun zip :: "'a list => 'b list => (('a, 'b) pair) list" where
"zip (nil2) z = nil2"
| "zip (cons2 z2 x2) (nil2) = nil2"
| "zip (cons2 z2 x2) (cons2 x3 x4) =
     cons2 (pair2 z2 x3) (zip x2 x4)"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
"rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun len :: "'a list => Nat" where
"len (nil2) = Z"
| "len (cons2 z xs) = S (len xs)"

theorem property0 :
  "(((len xs) = (len ys)) ==>
      ((zip (rev xs) (rev ys)) = (rev (zip xs ys))))"
  oops

end
