(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Common applicative functors\<close>

subsection \<open>Environment functor\<close>

theory Applicative_Environment imports 
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

definition "const x = (\<lambda>_. x)"
definition "apf x y = (\<lambda>z. x z (y z))"

adhoc_overloading Applicative.pure const
adhoc_overloading Applicative.ap apf

text \<open>The declaration below demonstrates that applicative functors which lift the reductions
  for combinators K and W also lift C. However, the interchange law must be supplied in this case.\<close>

applicative env (K, W)
for
  pure: const
  ap: apf
  rel: "rel_fun (=)"
  set: range
by(simp_all add: const_def apf_def rel_fun_def)

lemma
  includes applicative_syntax
  shows "const (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
by applicative_lifting simp

end
