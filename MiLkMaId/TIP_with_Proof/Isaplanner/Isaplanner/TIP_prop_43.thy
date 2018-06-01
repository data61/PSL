(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_43
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile y (nil2) = nil2"
| "takeWhile y (cons2 z2 xs) =
     (if y z2 then cons2 z2 (takeWhile y xs) else nil2)"

fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile y (nil2) = nil2"
| "dropWhile y (cons2 z2 xs) =
     (if y z2 then dropWhile y xs else cons2 z2 xs)"

theorem property0 :
  "((x (takeWhile p xs) (dropWhile p xs)) = xs)"
  find_proof DInd
  apply (induct)
   apply auto
  done 

theorem property0' :
  "((x (takeWhile p xs) (dropWhile p xs)) = xs)"
  apply (induct xs)
   apply auto
  done

theorem property0'' :
  "((x (takeWhile p xs) (dropWhile p xs)) = xs)"
  apply (induct rule:x.induct)
  nitpick
  oops

theorem property0'' :
  "((x (takeWhile p xs) (dropWhile p xs)) = xs)"
  apply (induct "(takeWhile p xs)" rule:x.induct)
   apply fastforce
  apply clarsimp
  (*This is bad: The conclusion is equivalent to the original goal.*)
  oops

end