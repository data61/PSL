(* Author: Joshua Schneider, ETH Zurich
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>An abstract applicative functor\<close>

theory Abstract_AF imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

typedef 'a af = "UNIV :: 'a set" ..

setup_lifting type_definition_af

abbreviation "af_pure \<equiv> Abs_af"
lift_definition af_ap :: "('a \<Rightarrow> 'b) af \<Rightarrow> 'a af \<Rightarrow> 'b af" is "\<lambda>f x. f x" .

adhoc_overloading Applicative.pure Abs_af
adhoc_overloading Applicative.ap af_ap

context includes applicative_syntax
begin

lemma af_identity: "af_pure id \<diamondop> x = x"
by transfer simp

lemma af_homomorphism: "af_pure f \<diamondop> af_pure x = af_pure (f x)"
by(fact af_ap.abs_eq)

lemma af_composition: "af_pure comp \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
by transfer simp

lemma af_interchange: "f \<diamondop> af_pure x = af_pure (\<lambda>g. g x) \<diamondop> f"
by transfer simp

end

lifting_forget af.lifting

hide_const Abs_af Rep_af
hide_fact af_ap_def

applicative af
for
  pure: af_pure
  ap: af_ap
using af_homomorphism af_composition af_identity af_interchange
unfolding id_def comp_def[abs_def]
.

end
