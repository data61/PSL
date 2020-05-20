theory SPMF_Applicative imports
  Applicative_Lifting.Applicative_PMF
  Set_Applicative
  "HOL-Probability.SPMF"
begin

subsection \<open>Applicative instance for @{typ "'a spmf"}\<close>

abbreviation (input) pure_spmf :: "'a \<Rightarrow> 'a spmf"
where "pure_spmf \<equiv> return_spmf"

definition ap_spmf :: "('a \<Rightarrow> 'b) spmf \<Rightarrow> 'a spmf \<Rightarrow> 'b spmf"
where "ap_spmf f x = map_spmf (\<lambda>(f, x). f x) (pair_spmf f x)"

lemma ap_spmf_conv_bind: "ap_spmf f x = bind_spmf f (\<lambda>f. bind_spmf x (\<lambda>x. return_spmf (f x)))"
by(simp add: ap_spmf_def map_spmf_conv_bind_spmf pair_spmf_alt_def)

adhoc_overloading Applicative.ap ap_spmf

context includes applicative_syntax begin

lemma ap_spmf_id: "pure_spmf (\<lambda>x. x) \<diamondop> x = x"
by(simp add: ap_spmf_def pair_spmf_return_spmf1 spmf.map_comp o_def)

lemma ap_spmf_comp: "pure_spmf (\<circ>) \<diamondop> u \<diamondop> v \<diamondop> w = u \<diamondop> (v \<diamondop> w)"
by(simp add: ap_spmf_def pair_spmf_return_spmf1 pair_map_spmf1 pair_map_spmf2 spmf.map_comp o_def split_def pair_pair_spmf)

lemma ap_spmf_homo: "pure_spmf f \<diamondop> pure_spmf x = pure_spmf (f x)"
by(simp add: ap_spmf_def pair_spmf_return_spmf1)

lemma ap_spmf_interchange: "u \<diamondop> pure_spmf x = pure_spmf (\<lambda>f. f x) \<diamondop> u"
by(simp add: ap_spmf_def pair_spmf_return_spmf1 pair_spmf_return_spmf2 spmf.map_comp o_def)

lemma ap_spmf_C: "return_spmf (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
apply(simp add: ap_spmf_def pair_map_spmf1 spmf.map_comp pair_spmf_return_spmf1 pair_pair_spmf o_def split_def)
apply(subst (2) pair_commute_spmf)
apply(simp add: pair_map_spmf2 spmf.map_comp o_def split_def)
done

applicative spmf (C)
for
  pure: pure_spmf
  ap: ap_spmf
by(rule ap_spmf_id ap_spmf_comp[unfolded o_def[abs_def]] ap_spmf_homo ap_spmf_interchange ap_spmf_C)+

lemma set_ap_spmf [simp]: "set_spmf (p \<diamondop> q) = set_spmf p \<diamondop> set_spmf q"
by(auto simp add: ap_spmf_def ap_set_def)

lemma bind_ap_spmf: "bind_spmf (p \<diamondop> x) f = bind_spmf p (\<lambda>p. x \<bind> (\<lambda>x. f (p x)))"
by(simp add: ap_spmf_conv_bind)

lemma bind_pmf_ap_return_spmf [simp]: "bind_pmf (ap_spmf (return_spmf f) p) g = bind_pmf p (g \<circ> map_option f)"
by(auto simp add: ap_spmf_conv_bind bind_spmf_def bind_return_pmf bind_assoc_pmf intro: bind_pmf_cong split: option.split)

lemma map_spmf_conv_ap [applicative_unfold]: "map_spmf f p = return_spmf f \<diamondop> p"
by(simp add: map_spmf_conv_bind_spmf ap_spmf_conv_bind)

end

end
