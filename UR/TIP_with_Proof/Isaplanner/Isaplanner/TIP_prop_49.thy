(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_49
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun butlast :: "'a list => 'a list" where
  "butlast (nil2) = nil2"
| "butlast (cons2 z (nil2)) = nil2"
| "butlast (cons2 z (cons2 x2 x3)) =
     cons2 z (butlast (cons2 x2 x3))"

fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat y (nil2) = butlast y"
| "butlastConcat y (cons2 z2 x2) = x y (butlast (cons2 z2 x2))"

theorem property0 :
  "((butlast (x xs ys)) = (butlastConcat xs ys))"
  (*Why on "xs"?
    Because "x" is defined recursively on the first parameter, which is "xs" in this case,
    and "x" is the innermost recursive function.
    and we can apply "butlast.simps" to the left-hand side if we can apply "x.simps" to "x xs ys".
   *)
  (*Why "rule:butlast.induct"?
    Because "butlast"'s pattern-matching seems to be powerful(?)
    Because we want to simplify "x xs ys" and "x xs ys" is a sub-term of "butlast (x xs ys)"(?)
   *)
  apply(induct xs rule:butlast.induct)
    apply(cases ys)
     apply fastforce+
   apply(cases ys)
    apply fastforce+
  apply(cases ys)
   apply fastforce+
  done

theorem property0' :
  "((butlast (x xs ys)) = (butlastConcat xs ys))"
  apply(induct xs rule:butlast.induct)
    apply(induct ys)
     apply fastforce+
   apply(induct ys)
    apply fastforce+
  apply(induct ys)
   apply fastforce+
  done

theorem "((butlast (x xs ys)) = (butlastConcat xs ys))"
  apply(induct ys rule:butlastConcat.induct)
  nitpick
  oops

theorem "((butlast (x xs ys)) = (butlastConcat xs ys))"
  apply(induct xs rule:butlastConcat.induct)
  nitpick
  oops

theorem "((butlast (x xs ys)) = (butlastConcat xs ys))"
(*TODO: find alternative proofs without "butlast.induct".*)
  oops

end