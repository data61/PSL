(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Monoid\<close>

theory Applicative_Monoid imports
  Applicative 
  "HOL-Library.Adhoc_Overloading"
begin

datatype ('a, 'b) monoid_ap = Monoid_ap 'a 'b

definition (in zero) pure_monoid_add :: "'b \<Rightarrow> ('a, 'b) monoid_ap"
where "pure_monoid_add = Monoid_ap 0"

fun (in plus) ap_monoid_add :: "('a, 'b \<Rightarrow> 'c) monoid_ap \<Rightarrow> ('a, 'b) monoid_ap \<Rightarrow> ('a, 'c) monoid_ap"
where "ap_monoid_add (Monoid_ap a1 f) (Monoid_ap a2 x) = Monoid_ap (a1 + a2) (f x)"

setup \<open>
  fold Sign.add_const_constraint
   [(@{const_name pure_monoid_add}, SOME (@{typ "'b \<Rightarrow> ('a :: monoid_add, 'b) monoid_ap"})),
    (@{const_name ap_monoid_add}, SOME (@{typ "('a :: monoid_add, 'b \<Rightarrow> 'c) monoid_ap \<Rightarrow> ('a, 'b) monoid_ap \<Rightarrow> ('a, 'c) monoid_ap"}))]
\<close>

adhoc_overloading Applicative.pure pure_monoid_add
adhoc_overloading Applicative.ap ap_monoid_add

applicative monoid_add
  for pure: pure_monoid_add
      ap: ap_monoid_add
subgoal by(simp add: pure_monoid_add_def)
subgoal for g f x by(cases g f x rule: monoid_ap.exhaust[case_product monoid_ap.exhaust, case_product monoid_ap.exhaust])(simp add: pure_monoid_add_def add.assoc)
subgoal for x by(cases x)(simp add: pure_monoid_add_def)
subgoal for f x by(cases f)(simp add: pure_monoid_add_def)
done

applicative comm_monoid_add (C)
  for pure: "pure_monoid_add :: _ \<Rightarrow> (_ :: comm_monoid_add, _) monoid_ap"
      ap: "ap_monoid_add :: (_ :: comm_monoid_add, _) monoid_ap \<Rightarrow> _"
apply(rule monoid_add.homomorphism monoid_add.pure_B_conv monoid_add.interchange)+
subgoal for f x y by(cases f x y rule: monoid_ap.exhaust[case_product monoid_ap.exhaust, case_product monoid_ap.exhaust])(simp add: pure_monoid_add_def add_ac)
apply(rule monoid_add.pure_I_conv)
done

class idemp_monoid_add = monoid_add +
  assumes add_idemp: "x + x = x"

applicative idemp_monoid_add (W)
  for pure: "pure_monoid_add :: _ \<Rightarrow> (_ :: idemp_monoid_add, _) monoid_ap"
      ap: "ap_monoid_add :: (_ :: idemp_monoid_add, _) monoid_ap \<Rightarrow> _"
apply(rule monoid_add.homomorphism monoid_add.pure_B_conv monoid_add.pure_I_conv)+
subgoal for f x by(cases f x rule: monoid_ap.exhaust[case_product monoid_ap.exhaust])(simp add: pure_monoid_add_def add.assoc add_idemp)
apply(rule monoid_add.interchange)
done

text \<open>Test case\<close>
lemma
  includes applicative_syntax
  shows "pure_monoid_add (+) \<diamondop> (x :: (nat, int) monoid_ap) \<diamondop> y = pure (+) \<diamondop> y \<diamondop> x"
by(applicative_lifting comm_monoid_add) simp

end
