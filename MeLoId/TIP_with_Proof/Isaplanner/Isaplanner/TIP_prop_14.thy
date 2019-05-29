(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_14
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter y (nil2) = nil2"
| "filter y (cons2 z2 xs) =
     (if y z2 then cons2 z2 (filter y xs) else filter y xs)"

theorem property0 :
  "((filter p (x xs ys)) = (x (filter p xs) (filter p ys)))"
  find_proof DInd
  apply (induct arbitrary: p rule: TIP_prop_14.x.induct)
   apply auto
  done

end