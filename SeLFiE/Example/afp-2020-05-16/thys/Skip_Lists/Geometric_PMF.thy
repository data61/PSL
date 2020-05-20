(*
  File:    Pi_pmf.thy
  Authors: Manuel Eberl, Max W. Haslbeck
*)
section \<open>Theorems about the Geometric Distribution\<close>
theory Geometric_PMF
  imports
    "HOL-Probability.Probability"
    Pi_pmf
    "Monad_Normalisation.Monad_Normalisation"
begin

lemma geometric_sums_times_n:
  fixes c::"'a::{banach,real_normed_field}"
  assumes "norm c < 1"
  shows "(\<lambda>n. c^n * of_nat n) sums (c / (1 - c)\<^sup>2)"
proof -
  have "(\<lambda>n. c * z ^ n) sums (c / (1 - z))" if "norm z < 1" for z
    using geometric_sums sums_mult that by fastforce
  moreover have "((\<lambda>z. c / (1 - z)) has_field_derivative (c / (1 - c)\<^sup>2)) (at c)"
      using assms by (auto intro!: derivative_eq_intros simp add: semiring_normalization_rules)
  ultimately have "(\<lambda>n. diffs (\<lambda>n. c) n * c ^ n) sums (c / (1 - c)\<^sup>2)"
    using assms by (intro termdiffs_sums_strong)
  then have "(\<lambda>n. of_nat (Suc n) * c ^ (Suc n)) sums (c / (1 - c)\<^sup>2)"
    unfolding diffs_def by (simp add: power_eq_if mult.assoc)
  then show ?thesis
    by (subst (asm) sums_Suc_iff) (auto simp add: mult.commute)
qed

lemma geometric_sums_times_norm:
  fixes c::"'a::{banach,real_normed_field}"
  assumes "norm c < 1"
  shows "(\<lambda>n. norm (c^n * of_nat n)) sums (norm c / (1 - norm c)\<^sup>2)"
proof -
  have "norm (c^n * of_nat n) = (norm c) ^ n * of_nat n" for n::nat
    by (simp add: norm_power norm_mult)
  then show ?thesis
    using geometric_sums_times_n[of "norm c"] assms
    by force
qed

lemma integrable_real_geometric_pmf:
  assumes "p \<in> {0<..1}"
  shows   "integrable (geometric_pmf p) real"
proof -
  have "summable (\<lambda>x. p * ((1 - p) ^ x * real x))"
    using geometric_sums_times_norm[of "1 - p"] assms
    by (intro summable_mult) (auto simp: sums_iff)
  hence "summable (\<lambda>x. (1 - p) ^ x * real x)"
    by (rule summable_mult_D) (use assms in auto)
  thus ?thesis
    unfolding measure_pmf_eq_density using assms
    by (subst integrable_density)
       (auto simp: integrable_count_space_nat_iff mult_ac)
qed

lemma expectation_geometric_pmf:
  assumes "p \<in> {0<..1}"
  shows   "measure_pmf.expectation (geometric_pmf p) real = (1 - p) / p"
proof -
  have "(\<lambda>n. p * ((1 - p) ^ n * n)) sums (p * ((1 - p) / p^2))"
    using assms geometric_sums_times_n[of "1-p"] by (intro sums_mult) auto
  moreover have "(\<lambda>n. p * ((1 - p) ^ n * n)) = (\<lambda>n. (1 - p) ^ n * p  * real n)"
    by auto
  ultimately have *: "(\<lambda>n. (1 - p) ^ n * p  * real n) sums ((1 - p) / p)"
    using assms sums_subst by (auto simp add: power2_eq_square)
  have "measure_pmf.expectation (geometric_pmf p) real =
        (\<integral>n. pmf (geometric_pmf p) n * real n \<partial>count_space UNIV)"
    unfolding measure_pmf_eq_density by (subst integral_density) auto
  also have "integrable (count_space UNIV) (\<lambda>n. pmf (geometric_pmf p) n * real n)"
    using * assms unfolding integrable_count_space_nat_iff by (simp add: sums_iff)
  hence "(\<integral>n. pmf (geometric_pmf p) n * real n \<partial>count_space UNIV) = (1 - p) / p"
    using * assms by (subst integral_count_space_nat) (simp_all add: sums_iff)
  finally show ?thesis by auto
qed

lemma nn_integral_geometric_pmf:
  assumes "p \<in> {0<..1}"
  shows   "nn_integral (geometric_pmf p) real = (1 - p) / p"
 using assms expectation_geometric_pmf integrable_real_geometric_pmf
  by (subst nn_integral_eq_integral) auto

lemma geometric_bind_pmf_unfold:
  assumes "p \<in> {0<..1}"
  shows "geometric_pmf p =
     do {b \<leftarrow> bernoulli_pmf p;
         if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)}"
proof -
  have *: "(Suc -` {i}) = (if i = 0 then {} else {i - 1})" for i
    by force
  have "pmf (geometric_pmf p) i =
        pmf (bernoulli_pmf p \<bind>
            (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)))
            i" for i
  proof -
    have "pmf (geometric_pmf p) i =
          (if i = 0 then p else (1 - p) * pmf (geometric_pmf p) (i - 1))"
      using assms by (simp add: power_eq_if)
    also have "\<dots> = (if i = 0  then p else (1 - p) * pmf (map_pmf Suc (geometric_pmf p)) i)"
      by (simp add: pmf_map indicator_def measure_pmf_single *)
    also have "\<dots> = measure_pmf.expectation (bernoulli_pmf p)
          (\<lambda>x. pmf (if x then return_pmf 0 else map_pmf Suc (geometric_pmf p)) i)"
      using assms by (auto simp add: pmf_map *)
    also have "\<dots> = pmf (bernoulli_pmf p \<bind>
                   (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)))
                   i"
      by (auto simp add: pmf_bind)
    finally show ?thesis .
  qed
  then show ?thesis
    using pmf_eqI by blast
qed

lemma "p \<in> {0<..<1} \<Longrightarrow> set_pmf (geometric_pmf p) = UNIV"
  by (auto simp add: measure_pmf_single set_pmf_def)

lemma "set_pmf (geometric_pmf 1) = 0"
  by (auto simp add: measure_pmf_single set_pmf_def)

lemma geometric_pmf_prob_atMost:
  assumes "p \<in> {0<..1}"
  shows  "measure_pmf.prob (geometric_pmf p) {..n} = (1 - (1 - p)^(n + 1))"
proof -
  have "(\<Sum>x\<le>n. (1 - p) ^ x * p) = 1 - (1 - p) * (1 - p) ^ n"
    by (induction n) (auto simp add: algebra_simps)
  then show ?thesis
  using assms by (auto simp add: measure_pmf_conv_infsetsum)
qed

lemma geometric_pmf_prob_lessThan:
  assumes "p \<in> {0<..1}"
  shows  "measure_pmf.prob (geometric_pmf p) {..<n} = 1 - (1 - p) ^ n"
proof -
  have "(\<Sum>x<n. (1 - p) ^ x * p) = 1 - (1 - p) ^ n"
    by (induction n) (auto simp add: algebra_simps)
  then show ?thesis
  using assms by (auto simp add: measure_pmf_conv_infsetsum)
qed

lemma geometric_pmf_prob_greaterThan:
  assumes "p \<in> {0<..1}"
  shows  "measure_pmf.prob (geometric_pmf p) {n<..} = (1 - p)^(n + 1)"
proof -
  have "(UNIV - {..n}) = {n<..}"
    by auto
  moreover have "measure_pmf.prob (geometric_pmf p) (UNIV - {..n}) = (1 - p) ^ (n + 1)"
    using assms by (subst measure_pmf.finite_measure_Diff)
                   (auto simp add: geometric_pmf_prob_atMost)
  ultimately show ?thesis
    by auto
qed

lemma geometric_pmf_prob_atLeast:
  assumes "p \<in> {0<..1}"
  shows  "measure_pmf.prob (geometric_pmf p) {n..} = (1 - p)^n"
proof -
  have "(UNIV - {..<n}) = {n..}"
    by auto
  moreover have "measure_pmf.prob (geometric_pmf p) (UNIV - {..<n}) = (1 - p) ^ n"
    using assms by (subst measure_pmf.finite_measure_Diff)
                   (auto simp add: geometric_pmf_prob_lessThan)
  ultimately show ?thesis
    by auto
qed

lemma bernoulli_pmf_of_set':
  assumes "finite A"
  shows "map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (Pi_pmf A P (\<lambda>_. bernoulli_pmf (1/2))) = pmf_of_set (Pow A)"
proof -
  have *: "Pi_pmf A P (\<lambda>_. pmf_of_set (UNIV :: bool set)) = pmf_of_set (PiE_dflt A P (\<lambda>_. UNIV :: bool set))"
    using assms by (intro Pi_pmf_of_set) auto
  have "map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (Pi_pmf A P (\<lambda>_. bernoulli_pmf (1 / 2))) =
        map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (Pi_pmf A P (\<lambda>_. pmf_of_set UNIV))"
    using bernoulli_pmf_half_conv_pmf_of_set by auto
  also have "\<dots> = map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (pmf_of_set (PiE_dflt A P (\<lambda>_. UNIV)))"
    using assms by (subst Pi_pmf_of_set) (auto)
  also have "\<dots> = pmf_of_set (Pow A)"
  proof -
    have "bij_betw (\<lambda>b. {x \<in> A. \<not> b x}) (PiE_dflt A P (\<lambda>_. UNIV)) (Pow A)"
      by (rule bij_betwI[of _ _ _ "\<lambda>B b. if b \<in> A then \<not> (b \<in> B) else P"]) (auto simp add: PiE_dflt_def)
    then show ?thesis
      using assms by (intro map_pmf_of_set_bij_betw) auto
  qed
  finally show ?thesis
    by simp
qed

lemma Pi_pmf_pmf_of_set_Suc:
  assumes "finite A"
  shows "Pi_pmf A 0 (\<lambda>_. geometric_pmf (1/2)) =
       do {
         B \<leftarrow> pmf_of_set (Pow A);
         Pi_pmf B 0 (\<lambda>_. map_pmf Suc (geometric_pmf (1/2))) }"
proof -
  have "Pi_pmf A 0 (\<lambda>_. geometric_pmf (1/2)) =
        Pi_pmf A 0 (\<lambda>_. bernoulli_pmf (1/2) \<bind>
        (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf (1/2))))"
    using assms by (subst geometric_bind_pmf_unfold) auto
  also have "\<dots> =
             Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2)) \<bind>
             (\<lambda>b. Pi_pmf A 0 (\<lambda>x. if b x then return_pmf 0 else map_pmf Suc (geometric_pmf (1/2))))"
    using assms by (subst Pi_pmf_bind[of _ _ _ _ False]) auto
  also have "\<dots> =
             do {b \<leftarrow> Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2));
                 Pi_pmf {x \<in> A. ~b x} 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1/2)))}"
    using assms by (subst Pi_pmf_if_set') auto
  also have "\<dots> =
             do {B \<leftarrow> map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2)));
                 Pi_pmf B 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1/2)))}"
    unfolding map_pmf_def apply(subst bind_assoc_pmf) apply(subst bind_return_pmf) by auto
  also have "\<dots> = pmf_of_set (Pow A) \<bind> (\<lambda>B. Pi_pmf B 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1 / 2))))"
    unfolding assms using assms by (subst bernoulli_pmf_of_set') auto
  finally show ?thesis
    by simp
qed

lemma Pi_pmf_pmf_of_set_Suc':
  assumes "finite A"
  shows "Pi_pmf A 0 (\<lambda>_. geometric_pmf (1/2)) =
       do {
         B \<leftarrow> pmf_of_set (Pow A);
         Pi_pmf B 0 (\<lambda>_. map_pmf Suc (geometric_pmf (1/2))) }"
proof -
  have "Pi_pmf A 0 (\<lambda>_. geometric_pmf (1/2)) =
        Pi_pmf A 0 (\<lambda>_. bernoulli_pmf (1/2) \<bind>
        (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf (1/2))))"
    using assms by (subst geometric_bind_pmf_unfold) auto
  also have "\<dots> =
             Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2)) \<bind>
             (\<lambda>b. Pi_pmf A 0 (\<lambda>x. if b x then return_pmf 0 else map_pmf Suc (geometric_pmf (1/2))))"
    using assms by (subst Pi_pmf_bind[of _ _ _ _ False]) auto
  also have "\<dots> =
             do {b \<leftarrow> Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2));
                 Pi_pmf {x \<in> A. ~b x} 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1/2)))}"
    using assms by (subst Pi_pmf_if_set') auto
  also have "\<dots> =
             do {B \<leftarrow> map_pmf (\<lambda>b. {x \<in> A. \<not> b x}) (Pi_pmf A False (\<lambda>_. bernoulli_pmf (1/2)));
                 Pi_pmf B 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1/2)))}"
    unfolding map_pmf_def by (auto simp add: bind_assoc_pmf bind_return_pmf)
  also have "\<dots> = pmf_of_set (Pow A) \<bind> (\<lambda>B. Pi_pmf B 0 (\<lambda>x. map_pmf Suc (geometric_pmf (1 / 2))))"
    unfolding assms using assms by (subst bernoulli_pmf_of_set') auto
  finally show ?thesis
    by simp
qed

lemma binomial_pmf_altdef':
  fixes A :: "'a set"
  assumes "finite A" and "card A = n" and p: "p \<in> {0..1}"
  shows   "binomial_pmf n p =
             map_pmf (\<lambda>f. card {x\<in>A. f x}) (Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p))" (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = binomial_pmf (card A) p"
    by simp
  also have "\<dots> = ?rhs"
  using assms(1)
  proof (induction rule: finite_induct)
    case empty
    with p show ?case by (simp add: binomial_pmf_0)
  next
    case (insert x A)
    from insert.hyps have "card (insert x A) = Suc (card A)"
      by simp
    also have "binomial_pmf \<dots> p = do {
                                     b \<leftarrow> bernoulli_pmf p;
                                     f \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
                                     return_pmf ((if b then 1 else 0) + card {y \<in> A. f y})
                                   }"
      using p by (simp add: binomial_pmf_Suc insert.IH bind_map_pmf)
    also have "\<dots> = do {
                      b \<leftarrow> bernoulli_pmf p;
                      f \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
                      return_pmf (card {y \<in> insert x A. (f(x := b)) y})
                    }"
    proof (intro bind_pmf_cong refl, goal_cases)
      case (1 b f)
      have "(if b then 1 else 0) + card {y\<in>A. f y} = card ((if b then {x} else {}) \<union> {y\<in>A. f y})"
        using insert.hyps by auto
      also have "(if b then {x} else {}) \<union> {y\<in>A. f y} = {y\<in>insert x A. (f(x := b)) y}"
        using insert.hyps by auto
      finally show ?case by simp
    qed
    also have "\<dots> = map_pmf (\<lambda>f. card {y\<in>insert x A. f y})
                      (Pi_pmf (insert x A) dflt (\<lambda>_. bernoulli_pmf p))"
      using insert.hyps by (subst Pi_pmf_insert) (simp_all add: pair_pmf_def map_bind_pmf)
    finally show ?case .
  qed
  finally show ?thesis .
qed

lemma bernoulli_pmf_Not:
  assumes "p \<in> {0..1}"
  shows "bernoulli_pmf p = map_pmf Not (bernoulli_pmf (1 - p))"
proof -
  have *: "(Not -` {True}) = {False}" "(Not -` {False}) = {True}"
    by blast+
  have "pmf (bernoulli_pmf p) b = pmf (map_pmf Not (bernoulli_pmf (1 - p))) b" for b
    using assms by (cases b) (auto simp add: pmf_map * measure_pmf_single)
  then show ?thesis
    by (rule pmf_eqI)
qed

lemma binomial_pmf_altdef'':
  assumes p: "p \<in> {0..1}"
  shows   "binomial_pmf n p =
           map_pmf (\<lambda>f. card {x. x < n \<and> f x}) (Pi_pmf {..<n} dflt (\<lambda>_. bernoulli_pmf p))"
  using assms by (subst binomial_pmf_altdef'[of "{..<n}"]) (auto)

context includes monad_normalisation
begin

lemma Pi_pmf_geometric_filter:
  assumes "finite A" "p \<in> {0<..1}"
  shows "Pi_pmf A 0 (\<lambda>_. geometric_pmf p) =
       do {
         fb \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
         Pi_pmf {x \<in> A. \<not> fb x} 0 (\<lambda>_. map_pmf Suc (geometric_pmf p)) }"
proof -
  have "Pi_pmf A 0 (\<lambda>_. geometric_pmf p) =
        Pi_pmf A 0 (\<lambda>_. bernoulli_pmf p \<bind>
                   (\<lambda>b. if b then return_pmf 0 else map_pmf Suc (geometric_pmf p)))"
    using assms by (subst geometric_bind_pmf_unfold) auto
  also have "\<dots> =
             Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p) \<bind>
             (\<lambda>b. Pi_pmf A 0 (\<lambda>x. if b x then return_pmf 0 else map_pmf Suc (geometric_pmf p)))"
    using assms by (subst Pi_pmf_bind[of _ _ _ _ dflt]) auto
  also have "\<dots> =
             do {b \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf p);
                 Pi_pmf {x \<in> A. \<not> b x} 0 (\<lambda>x. map_pmf Suc (geometric_pmf p))}"
    using assms by (subst Pi_pmf_if_set') (auto)
  finally show ?thesis
    by simp
qed

lemma Pi_pmf_geometric_filter':
  assumes "finite A" "p \<in> {0<..1}"
  shows "Pi_pmf A 0 (\<lambda>_. geometric_pmf p) =
       do {
         fb \<leftarrow> Pi_pmf A dflt (\<lambda>_. bernoulli_pmf (1 - p));
         Pi_pmf {x \<in> A. fb x} 0 (\<lambda>_. map_pmf Suc (geometric_pmf p)) }"
  using assms by (auto simp add: Pi_pmf_geometric_filter[of _ _ "\<not> dflt"] bernoulli_pmf_Not[of p]
      Pi_pmf_map[of _ _ dflt] map_pmf_def[of "((\<circ>) Not)"])

end

end
