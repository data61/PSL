(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_73
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
"rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun filter :: "('a => bool) => 'a list => 'a list" where
"filter y (nil2) = nil2"
| "filter y (cons2 z2 xs) =
     (if y z2 then cons2 z2 (filter y xs) else filter y xs)"

theorem property0 :
  "((rev (filter p xs)) = (filter p (rev xs)))"
  apply(induct xs arbitrary: p)(*arbitrary: p is optional*)
   apply auto[1]
  apply(subst filter.simps)
  apply(subst rev.simps)
  apply(case_tac "p x1")
   apply simp
   apply(subgoal_tac "\<And>x1 xs revxs. 
      TIP_prop_73.rev (TIP_prop_73.filter p xs) = TIP_prop_73.filter p revxs \<Longrightarrow>
      p x1 \<Longrightarrow>
      x (TIP_prop_73.filter p revxs) (cons2 x1 nil2) =
      TIP_prop_73.filter p (x revxs (cons2 x1 nil2))")
    apply fastforce
   apply(induct_tac rule:x.induct)
  oops

end
