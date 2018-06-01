(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_22
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun max :: "Nat => Nat => Nat" where
  "max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S x2) = S (max z x2)"

theorem property0 :
  "((max (max a b) c) = (max a (max b c)))"
(*This nested induction (a \<rightarrow> b \<rightarrow> c) is easy to choose:
  "induct a" because the patter matching of "max" is exclusive on the first argument,
             and "a" is always the first argument of "max" in this case
             and for other first arguments of "max" are non-variable terms.
  We have two innermost "max"es. For one "max" the first argument is "b".
  Starting with induction on "b" also works, but the following proof becomes longer
  because it necessitates induction on the first argument of other "max", which is "a" even for
  the base case.
 *)
  apply(induct a arbitrary: b c)
   apply fastforce
  (* We still have two "max"es: "max (S a) b" and "max b c".
     But the first argument of "max (S a) b" starts with a constructor, on which we cannot induct.
   *)
  apply(induct_tac b)
   apply fastforce
  apply(induct_tac c)(*Despite the warning "Induction variable occurs also among premises: "c"", it works.*)
  apply fastforce+
  done

theorem property':(*sub-optimal proof with one extra induction step.*)
  "((max (max a b) c) = (max a (max b c)))"
  apply(induct b arbitrary: a c)
  apply(induct_tac a) (*extra induction step.*)
   apply fastforce+
  apply(induct_tac a)
   apply fastforce
  apply(induct_tac c)(*Despite the warning "Induction variable occurs also among premises: "c"", it works.*)
  apply fastforce+
  done

theorem property'':(*bad.*)
  "((max (max a b) c) = (max a (max b c)))"
  apply(induct rule:max.induct)
  nitpick
  oops

end