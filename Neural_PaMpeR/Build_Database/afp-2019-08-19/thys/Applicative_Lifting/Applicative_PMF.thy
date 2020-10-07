(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Probability mass functions\<close>

theory Applicative_PMF imports
  Applicative
  "HOL-Probability.Probability"
  "HOL-Library.Adhoc_Overloading"
begin

abbreviation (input) pure_pmf :: "'a \<Rightarrow> 'a pmf"
where "pure_pmf \<equiv> return_pmf"

definition ap_pmf :: "('a \<Rightarrow> 'b) pmf \<Rightarrow> 'a pmf \<Rightarrow> 'b pmf"
where "ap_pmf f x = map_pmf (\<lambda>(f, x). f x) (pair_pmf f x)"

adhoc_overloading Applicative.ap ap_pmf

context includes applicative_syntax
begin

lemma ap_pmf_id: "pure_pmf (\<lambda>x. x) \<diamondop> x = x"
by(simp add: ap_pmf_def pair_return_pmf1 pmf.map_comp o_def)

lemma ap_pmf_comp: "pure_pmf (\<circ>) \<diamondop> u \<diamondop> v \<diamondop> w = u \<diamondop> (v \<diamondop> w)"
by(simp add: ap_pmf_def pair_return_pmf1 pair_map_pmf1 pair_map_pmf2 pmf.map_comp o_def split_def pair_pair_pmf)

lemma ap_pmf_homo: "pure_pmf f \<diamondop> pure_pmf x = pure_pmf (f x)"
by(simp add: ap_pmf_def pair_return_pmf1)

lemma ap_pmf_interchange: "u \<diamondop> pure_pmf x = pure_pmf (\<lambda>f. f x) \<diamondop> u"
by(simp add: ap_pmf_def pair_return_pmf1 pair_return_pmf2 pmf.map_comp o_def)

lemma ap_pmf_K: "return_pmf (\<lambda>x _. x) \<diamondop> x \<diamondop> y = x"
by(simp add: ap_pmf_def pair_map_pmf1 pmf.map_comp pair_return_pmf1 o_def split_def map_fst_pair_pmf)

lemma ap_pmf_C: "return_pmf (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
apply(simp add: ap_pmf_def pair_map_pmf1 pmf.map_comp pair_return_pmf1 pair_pair_pmf o_def split_def)
apply(subst (2) pair_commute_pmf)
apply(simp add: pair_map_pmf2 pmf.map_comp o_def split_def)
done

lemma ap_pmf_transfer[transfer_rule]:
  "rel_fun (rel_pmf (rel_fun A B)) (rel_fun (rel_pmf A) (rel_pmf B)) ap_pmf ap_pmf"
unfolding ap_pmf_def[abs_def] pair_pmf_def
by transfer_prover

applicative pmf (C, K)
for
  pure: pure_pmf
  ap: ap_pmf
  rel: rel_pmf
  set: set_pmf
proof -
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "rel_fun R (rel_pmf R) pure_pmf pure_pmf" by transfer_prover
next
  fix R and f :: "('a \<Rightarrow> 'b) pmf" and g :: "('a \<Rightarrow> 'c) pmf" and x
  assume [transfer_rule]: "rel_pmf (rel_fun (eq_on (set_pmf x)) R) f g"
  have [transfer_rule]: "rel_pmf (eq_on (set_pmf x)) x x" by (simp add: pmf.rel_refl_strong)
  show "rel_pmf R (ap_pmf f x) (ap_pmf g x)" by transfer_prover
qed(rule ap_pmf_comp[unfolded o_def[abs_def]] ap_pmf_homo ap_pmf_C ap_pmf_K)+

end

end
