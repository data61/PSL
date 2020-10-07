(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Alternative Lebesgue Measure Definition\<close>

theory Lebesgue_Functional
imports "HOL-Analysis.Lebesgue_Measure"
begin

text \<open>Lebesgue\_Measure.lborel is defined on the typeclass euclidean\_space, which does not allow the
space dimension to be dependent on a variable. As the Lebesgue measure of higher dimensions is the
product measure of the one dimensional Lebesgue measure, we can easily define a more flexible version
of the Lebesgue measure as follows. This version of the Lebesgue measure measures sets of functions
from nat to real whose values are undefined for arguments higher than n. These "Extensional Function Spaces"
 are defined in HOL/FuncSet. \<close>

definition lborel_f :: "nat \<Rightarrow> (nat \<Rightarrow> real) measure" where
  "lborel_f n = (\<Pi>\<^sub>M b\<in>{..<n}. lborel)"

lemma product_sigma_finite_interval: "product_sigma_finite (\<lambda>b. interval_measure (\<lambda>x. x))"
  unfolding product_sigma_finite_def using  sigma_finite_interval_measure by auto

lemma l_borel_f_1: "distr (lborel_f 1) lborel (\<lambda>x. x 0) = lborel"
  unfolding lborel_f_def
  using product_sigma_finite.distr_singleton[OF product_sigma_finite_interval, of 0]
    lborel_eq_real lessThan_Suc by auto

lemma space_lborel_f: "space (lborel_f n) = Pi\<^sub>E {..<n} (\<lambda>_. UNIV)" unfolding lborel_f_def
  unfolding space_PiM space_lborel space_borel by metis

lemma space_lborel_f_subset: "space (lborel_f n) \<subseteq> space (lborel_f (Suc n))"
unfolding space_lborel_f by (rule subsetI, rule PiE_I, blast,
  metis PiE_E  Suc_n_not_le_n le_cases lessThan_subset_iff subsetCE)

lemma space_lborel_add_dim:
assumes "f \<in> space (lborel_f n)"
shows "f(n:=x) \<in> space (lborel_f (Suc n))"
unfolding space_lborel_f
using assms lessThan_Suc space_lborel_f by auto

lemma integral_lborel_f:
assumes "f \<in> borel_measurable (lborel_f (Suc n))"
shows "integral\<^sup>N (lborel_f (Suc n)) f = \<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (x(n := y)) \<partial>lborel_f n \<partial>lborel"
  unfolding lborel_f_def
  using product_sigma_finite.product_nn_integral_insert_rev[OF product_sigma_finite_interval, of "{..<n}", OF finite_lessThan _]
  assms[unfolded lborel_f_def] lborel_eq_real by (simp add: lessThan_Suc)

lemma emeasure_lborel_f_Suc:
assumes "A \<in> sets (lborel_f (Suc n))"
assumes "\<And>y. {x\<in>space (lborel_f n). x(n := y) \<in> A} \<in> sets (lborel_f n)"
shows "emeasure (lborel_f (Suc n)) A = \<integral>\<^sup>+ y. emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := y) \<in> A} \<partial>lborel"
proof -
  {
    fix x y assume "x\<in>space (lborel_f n)"
    then have "(indicator A) (x(n := y)) = (indicator {x\<in>space (lborel_f n). x(n := y) \<in> A}) x" using indicator_def
      by (metis (no_types, lifting) mem_Collect_eq)
  }
  then show ?thesis
    unfolding nn_integral_indicator[OF assms(1), symmetric] nn_integral_indicator[OF assms(2), symmetric]
     integral_lborel_f[OF borel_measurable_indicator, OF assms(1)]
    using nn_integral_cong by (metis (no_types, lifting))
qed

lemma lborel_f_measurable_add_dim: "(\<lambda>f. f(n := x)) \<in> measurable (lborel_f n) (lborel_f (Suc n))"
proof -
  have "x \<in> space lborel" by simp
  have 0:"(\<lambda>(f, y). f(n := y)) \<circ> (\<lambda>xa. (xa, x)) = (\<lambda>f. f(n := x))" unfolding comp_def  using case_prod_conv by fast
  show ?thesis unfolding lborel_f_def
    using measurable_comp[OF measurable_Pair2'[of x lborel "Pi\<^sub>M {..<n} (\<lambda>b. lborel)", OF \<open>x \<in> space lborel\<close>]
    measurable_add_dim[of n "{..<n}" "\<lambda>b. lborel"], unfolded 0] lessThan_Suc by auto
qed

lemma sets_lborel_f_sub_dim:
assumes "A \<in> sets (lborel_f (Suc n))"
shows "{x. x(n := y) \<in> A} \<inter> space (lborel_f n) \<in> sets (lborel_f n)"
proof -
  have "(\<lambda>f. f(n := y)) -` A \<inter> space (lborel_f n) \<in> sets (lborel_f n)"
    using measurable_sets[OF lborel_f_measurable_add_dim assms] by auto
  moreover have "(\<lambda>f. f(n := y)) -` A = {x. x(n := y) \<in> A}" by auto
  finally show ?thesis by metis
qed

lemma lborel_f_measurable_restrict:
assumes "m \<le> n"
shows "(\<lambda>f. restrict f {..<m}) \<in> measurable (lborel_f n) (lborel_f m)"
using measurable_restrict_subset lborel_f_def assms by auto

lemma lborel_measurable_sub_dim: "(\<lambda>f. restrict f {..<n}) \<in> measurable (lborel_f (Suc n)) (lborel_f n)"
using lborel_f_measurable_restrict[of "n" "Suc n"] by linarith

lemma measurable_lborel_component [measurable]:
assumes "k<n"
shows "(\<lambda>x. x k) \<in> borel_measurable (lborel_f n)"
  unfolding lborel_f_def using assms measurable_PiM_component_rev by simp_all

end
