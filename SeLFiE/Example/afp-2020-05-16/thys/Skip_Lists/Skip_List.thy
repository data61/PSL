(*
  File:    Skip_List.thy
  Authors: Max W. Haslbeck, Manuel Eberl
*)

section \<open>Randomized Skip Lists\<close>
theory Skip_List
  imports Geometric_PMF
          Pi_pmf
          Misc
          "Monad_Normalisation.Monad_Normalisation"
begin

subsection \<open>Preliminaries\<close>

lemma bind_pmf_if': "(do {c \<leftarrow> C;
                         ab \<leftarrow> (if c then A else B);
                         D ab}::'a pmf) =
                     do {c \<leftarrow> C;
                         (if c then (A \<bind> D) else (B \<bind> D))}"
  by (metis (mono_tags, lifting))

abbreviation (input) Max\<^sub>0 where "Max\<^sub>0 \<equiv> (\<lambda>A. Max (A \<union> {0}))"


subsection \<open>Definition of a Randomised Skip List\<close>

text \<open>
  Given a set A we assign a geometric random variable (counting the number of failed Bernoulli
  trials before the first success) to every element in A. That means an arbitrary element of A is
  on level n with probability $(1-p)^{n}p$. We define he height of the skip list as the maximum
  assigned level. So a skip list with only one level has height 0 but the calculation of the
  expected height is cleaner this way.
\<close>

locale random_skip_list =
  fixes p::real
begin

definition q where "q = 1 - p"

definition SL :: "('a::linorder) set \<Rightarrow> ('a \<Rightarrow> nat) pmf" where "SL A = Pi_pmf A 0 (\<lambda>_. geometric_pmf p)"
definition SL\<^sub>N :: "nat \<Rightarrow> (nat \<Rightarrow> nat) pmf" where "SL\<^sub>N n = SL {..<n}"

subsection \<open>Height of Skip List\<close>

definition H where "H A = map_pmf (\<lambda>f. Max\<^sub>0 (f ` A)) (SL A)"
definition H\<^sub>N :: "nat \<Rightarrow> nat pmf" where "H\<^sub>N n = H {..<n}"

context includes monad_normalisation
begin

text \<open>
  The height of a skip list is independent of the values in a set A. For simplicity we can
  therefore work on the skip list over the set @{term "{..< card A}"}
\<close>

lemma
  assumes "finite A"
  shows "H A = H\<^sub>N (card A)"
proof -
  define f' where "f' = (\<lambda>x. if x \<in> A
                             then the_inv_into {..<card A} ((!) (sorted_list_of_set A)) x
                             else card A)"
  have bij_f': "bij_betw f' A {..<card A}"
  proof -
    (* I know the proof looks weird, but for some reason all tools have problems with this proof *)
    have "bij_betw (the_inv_into {..<card A} ((!) (sorted_list_of_set A))) A {..<card A}"
      unfolding f'_def using sorted_list_of_set_bij_betw assms bij_betw_the_inv_into by blast
    moreover have "bij_betw (the_inv_into {..<card A} ((!) (sorted_list_of_set A))) A {..<card A}
                     = bij_betw f' A {..<card A}"
      unfolding f'_def by (rule bij_betw_cong) simp
    ultimately show ?thesis
      by blast
  qed
  have *: "Max\<^sub>0 ((f \<circ> f') ` A) = Max\<^sub>0 (f ` {..<card A})" for f :: "nat \<Rightarrow> nat"
    using  bij_betw_imp_surj_on bij_f' image_comp by metis
  have "H A = map_pmf (\<lambda>f. Max\<^sub>0 (f ` A)) (map_pmf (\<lambda>g. g \<circ> f') (SL\<^sub>N (card A)))"
    using assms bij_f' unfolding H_def SL_def SL\<^sub>N_def
    by (subst Pi_pmf_bij_betw[of _ f' "{..<card A}"]) (auto simp add: f'_def)
  also have "\<dots> =  H\<^sub>N (card A)"
    unfolding H\<^sub>N_def H_def SL\<^sub>N_def using * by (auto intro!: bind_pmf_cong simp add: map_pmf_def)
  finally show ?thesis
    by simp
qed

text \<open>
  The cumulative distribution function (CDF) of the height is the CDF of the geometric PMF to the
  power of n
\<close>

lemma prob_Max_IID_geometric_atMost:
  assumes "p \<in> {0..1}"
  shows "measure_pmf.prob (H\<^sub>N n) {..i}
       = (measure_pmf.prob (geometric_pmf p) {..i}) ^ n" (is "?lhs = ?rhs")
proof -
  note SL_def[simp] SL\<^sub>N_def[simp] H_def[simp] H\<^sub>N_def[simp]
  have "{f. Max\<^sub>0 (f ` {..<n}) \<le> i}  = {..<n} \<rightarrow> {..i}"
    by auto
  then have "?lhs = measure_pmf.prob (SL\<^sub>N n) ({..<n} \<rightarrow> {..i})"
    by (simp add: vimage_def)
  also have "\<dots> = measure_pmf.prob (SL\<^sub>N n) (PiE_dflt {..<n} 0 (\<lambda>_. {..i}))"
    by (intro measure_prob_cong_0) (auto simp add: PiE_dflt_def pmf_Pi split: if_splits)
  also have "\<dots> = measure_pmf.prob (geometric_pmf p) {..i} ^ n"
    using assms by (auto simp add: measure_Pi_pmf_PiE_dflt)
  finally show ?thesis
    by simp
qed

lemma prob_Max_IID_geometric_greaterThan:
  assumes "p \<in> {0<..1}"
  shows "measure_pmf.prob (H\<^sub>N n) {i<..} =
         1 - (1 - q ^ (i + 1)) ^ n"
proof -
  have "UNIV - {..i} = {i<..}"
    by auto
  then have "measure_pmf.prob (H\<^sub>N n) {i<..} = measure_pmf.prob (H\<^sub>N n) (space (measure_pmf (H\<^sub>N n)) - {..i})"
    by (auto)
  also have "\<dots> = 1 - (measure_pmf.prob (geometric_pmf p) {..i}) ^ n"
    using assms by (subst measure_pmf.prob_compl) (auto simp add: prob_Max_IID_geometric_atMost)
  also have "\<dots> =   1 - (1 - q ^ (i + 1)) ^ n"
    using assms unfolding q_def by (subst geometric_pmf_prob_atMost) auto
  finally show ?thesis
    by simp
qed

end (* context includes monad_normalisation *)
end (* locale skip_list *)

text \<open>
  An alternative definition of the expected value of a non-negative random variable
  \footnote{\url{https://en.wikipedia.org/w/index.php?title=Expected\_value&oldid=881384346\#Formula\_for\_non-negative\_random\_variables}}
\<close>

lemma expectation_prob_atLeast:
  assumes "(\<lambda>i. measure_pmf.prob N {i..}) abs_summable_on {1..}"
  shows "measure_pmf.expectation N real = infsetsum (\<lambda>i. measure_pmf.prob N {i..}) {1..}"
    "integrable N real"
proof -
  have "(\<lambda>(x, y). pmf N y) abs_summable_on Sigma {Suc 0..} atLeast"
    using assms by (auto simp add: measure_pmf_conv_infsetsum abs_summable_on_Sigma_iff)
  then have summable: "(\<lambda>(x, y). pmf N x) abs_summable_on Sigma {Suc 0..} (atLeastAtMost (Suc 0))"
    by (subst abs_summable_on_reindex_bij_betw[of "\<lambda>(x,y). (y,x)", symmetric])
      (auto intro!: bij_betw_imageI simp add: inj_on_def case_prod_beta)
  have "measure_pmf.expectation N real = (\<Sum>\<^sub>ax. pmf N x *\<^sub>R real x)"
    by (auto simp add: infsetsum_def integral_density measure_pmf_eq_density)
  also have "\<dots> = (\<Sum>\<^sub>ax \<in> ({0} \<union> {Suc 0..}). pmf N x *\<^sub>R real x)"
    by (auto intro!: infsetsum_cong)
  also have "\<dots> = (\<Sum>\<^sub>ax\<in>{Suc 0..}. pmf N x * real x)"
  proof -
    have "(\<lambda>x. pmf N x *\<^sub>R real x) abs_summable_on {0} \<union> {Suc 0..}"
      using summable by (subst (asm) abs_summable_on_Sigma_iff) (auto simp add: mult.commute)
    then show ?thesis
      by (subst infsetsum_Un_Int) auto
  qed
  also have "\<dots> = (\<Sum>\<^sub>a(x, y)\<in>Sigma {Suc 0..} (atLeastAtMost (Suc 0)). pmf N x)"
    using summable by (subst infsetsum_Sigma) (auto simp add: mult.commute)
  also have "\<dots> = (\<Sum>\<^sub>ax\<in>Sigma {Suc 0..} atLeast. pmf N (snd x))"
    by (subst infsetsum_reindex_bij_betw[of "\<lambda>(x,y). (y,x)", symmetric])
      (auto intro!: bij_betw_imageI simp add: inj_on_def case_prod_beta)
  also have "\<dots> = infsetsum (\<lambda>i. measure_pmf.prob N {i..}) {1..}"
    using assms
    by (subst infsetsum_Sigma)
      (auto simp add: measure_pmf_conv_infsetsum abs_summable_on_Sigma_iff infsetsum_Sigma')
  finally show "measure_pmf.expectation N real = infsetsum (\<lambda>i. measure_pmf.prob N {i..}) {1..}"
    by simp
  have "(\<lambda>x. pmf N x *\<^sub>R real x) abs_summable_on {0} \<union> {Suc 0..}"
    using summable by (subst (asm) abs_summable_on_Sigma_iff) (auto simp add: mult.commute)
  then have "(\<lambda>x. pmf N x *\<^sub>R real x) abs_summable_on UNIV"
    by (simp add: atLeast_Suc)
  then have "integrable (count_space UNIV) (\<lambda>x. pmf N x *\<^sub>R real x)"
    by (subst abs_summable_on_def[symmetric]) blast
  then show "integrable N real"
    by (subst measure_pmf_eq_density, subst integrable_density) auto
qed

text \<open>
  The expected height of a skip list has no closed-form expression but we can approximate it. We
  start by showing how we can calculate an infinite sum over the natural numbers with an integral
  over the positive reals and the floor function.
\<close>

lemma infsetsum_set_nn_integral_reals:
  assumes "f abs_summable_on UNIV" "\<And>n. f n \<ge> 0"
  shows "infsetsum f UNIV = set_nn_integral lborel {0::real..} (\<lambda>x. f (nat (floor x)))"
proof -
  have "x < 1 + (floor x)"for x::real
    by linarith
  then have "\<exists>n. real n \<le> x \<and> x < 1 + real n" if "x \<ge> 0" for x
    using that of_nat_floor by (intro exI[of _ "nat (floor x)"]) auto
  then have "{0..} = (\<Union>n. {real n..<real (Suc n)})"
    by auto
  then have "\<integral>\<^sup>+x\<in>{0::real..}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel =
             (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel)"
    by (auto simp add: disjoint_family_on_def nn_integral_disjoint_family)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f n)\<partial>lborel)"
    by(subst suminf_cong, rule nn_integral_cong_AE)
      (auto intro!: eventuallyI  simp add: indicator_def floor_eq4)
  also have "\<dots> = (\<Sum>n. ennreal (f n))"
    by (auto intro!: suminf_cong simp add: nn_integral_cmult)
  also have "\<dots> = infsetsum f {0..}"
    using assms suminf_ennreal2 abs_summable_on_nat_iff' summable_norm_cancel
    by (auto simp add: infsetsum_nat)
  finally show ?thesis
    by simp
qed

lemma nn_integral_nats_reals:
  shows "(\<integral>\<^sup>+ i. ennreal (f i) \<partial>count_space UNIV) = \<integral>\<^sup>+x\<in>{0::real..}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel"
proof -
  have "x < 1 + (floor x)"for x::real
    by linarith
  then have "\<exists>n. real n \<le> x \<and> x < 1 + real n" if "x \<ge> 0" for x
    using that of_nat_floor by (intro exI[of _ "nat (floor x)"]) auto
  then have "{0..} = (\<Union>n. {real n..<real (Suc n)})"
    by auto
  then have "\<integral>\<^sup>+x\<in>{0::real..}. f (nat \<lfloor>x\<rfloor>)\<partial>lborel =
             (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel)"
    by (auto simp add: disjoint_family_on_def nn_integral_disjoint_family)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+x\<in>{real n..<1 + real n}. ennreal (f n)\<partial>lborel)"
    by(subst suminf_cong,rule nn_integral_cong_AE)
      (auto intro!: eventuallyI  simp add: indicator_def floor_eq4)
  also have "\<dots> = (\<Sum>n. ennreal (f n))"
    by (auto intro!: suminf_cong simp add: nn_integral_cmult)
  also have "\<dots> = (\<integral>\<^sup>+ i. ennreal (f i) \<partial>count_space UNIV)"
    by (simp add: nn_integral_count_space_nat)
  finally show ?thesis
    by simp
qed

lemma nn_integral_floor_less_eq:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> f y \<le> f x"
  shows "\<integral>\<^sup>+x\<in>{0::real..}. ennreal (f x)\<partial>lborel \<le> \<integral>\<^sup>+x\<in>{0::real..}. ennreal (f (nat \<lfloor>x\<rfloor>))\<partial>lborel"
  using assms by (auto simp add: indicator_def intro!: nn_integral_mono ennreal_leI)

lemma nn_integral_finite_imp_abs_sumable_on:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "nn_integral (count_space A) (\<lambda>x. norm (f x)) < \<infinity>"
  shows   "f abs_summable_on A"
  using assms unfolding abs_summable_on_def integrable_iff_bounded by auto

lemma nn_integral_finite_imp_abs_sumable_on':
  assumes "nn_integral (count_space A) (\<lambda>x. ennreal (f x)) < \<infinity>" "\<And>x. f x \<ge> 0"
  shows   "f abs_summable_on A"
  using assms unfolding abs_summable_on_def integrable_iff_bounded by auto

text \<open>
  We now show that $\int_0^\infty 1 - (1 - q^x) ^ n\;dx = \frac{- H_n}{\ln q}$ if $0 < q < 1$.
\<close>

lemma harm_integral_x_raised_n:
  "set_integrable lborel {0::real..1} (\<lambda>x. (\<Sum>i\<in>{..<n}. x ^ i))" (is ?thesis1)
  "LBINT x = 0..1. (\<Sum>i\<in>{..<n}. x ^ i) = harm n" (is ?thesis2)
proof -
  have h: "set_integrable lborel {0::real..1} (\<lambda>x. (\<Sum>i\<in>{..<n}. x ^ i))" for n
    by (intro borel_integrable_atLeastAtMost') (auto intro!: continuous_intros)
  then show ?thesis1
    by (intro borel_integrable_atLeastAtMost') (auto intro!: continuous_intros)
  show ?thesis2
  proof (induction n)
    case (Suc n)
    have "(LBINT x=0..1.(\<Sum>i\<in>{..<n}. x ^ i) + x ^ n) =
          (LBINT x=0..1. (\<Sum>i\<in>{..<n}. x ^ i)) + (LBINT x=0..1. x ^ n)"
    proof -
      have "set_integrable lborel (einterval 0 1) (\<lambda>x. (\<Sum>i\<in>{..<n}. x ^ i))"
        by (rule set_integrable_subset) (use h in \<open>auto simp add: einterval_def\<close>)
      moreover have "set_integrable lborel (einterval 0 1) (\<lambda>x. (x ^ n))"
      proof -
        have "set_integrable lborel {0::real..1} (\<lambda>x. (x ^ n))"
          by (rule borel_integrable_atLeastAtMost')
            (auto intro!: borel_integrable_atLeastAtMost' continuous_intros)
        then show ?thesis
          by (rule set_integrable_subset) (auto simp add: einterval_def)
      qed
      ultimately show ?thesis
        by (auto intro!: borel_integrable_atLeastAtMost' simp add:  interval_lebesgue_integrable_def)
    qed
    also have "(LBINT x=0..1. x ^ n) = 1 / (1 + real n)"
    proof -
      have "(LBINT x=0..1. x ^ n) = LBINT x. x ^ n * indicator {0..1} x "
      proof -
        have "AE x in lborel. x ^ n * indicator {0..1} x = indicator (einterval 0 1) x * x ^ n"
          by(rule eventually_mono[OF eventually_conj[OF  AE_lborel_singleton[of 1]
                  AE_lborel_singleton[of 0]]])
            (auto simp add: indicator_def einterval_def)
        then show ?thesis
          using integral_cong_AE unfolding interval_lebesgue_integral_def set_lebesgue_integral_def
          by (auto intro!: integral_cong_AE)
      qed
      then show ?thesis
        by (auto simp add: integral_power)
    qed
    finally show ?case
      using Suc by (auto simp add: harm_def inverse_eq_divide)
  qed (auto simp add: harm_def)
qed

lemma harm_integral_0_1_fraction:
  "set_integrable lborel {0::real..1} (\<lambda>x. (1 - x ^ n) / (1 - x))"
  "(LBINT x = 0..1. ((1 - x ^ n) / (1 - x))) = harm n"
proof -
  show "set_integrable lborel {0::real..1} (\<lambda>x. (1 - x ^ n) / (1 - x))"
  proof -
    have "AE x\<in>{0::real..1} in lborel. (1 - x ^ n) / (1 - x) = sum ((^) x) {..<n}"
      by (auto intro!: eventually_mono[OF AE_lborel_singleton[of 1]] simp add: sum_gp_strict)
    with harm_integral_x_raised_n show ?thesis
      by (subst set_integrable_cong_AE) auto
  qed
  moreover have "AE x\<in>{0::real<..<1} in lborel. (1 - x ^ n) / (1 - x) = sum ((^) x) {..<n}"
    by (auto simp add: sum_gp_strict)
  moreover have "einterval (min 0 1) (max 0 1) = {0::real<..<1}"
    by (auto simp add: min_def max_def einterval_iff)
  ultimately show "(LBINT x = 0..1. ((1 - x ^ n) / (1 - x))) = harm n"
    using harm_integral_x_raised_n by (subst interval_integral_cong_AE) auto
qed

lemma one_minus_one_minus_q_x_n_integral:
  assumes "q \<in> {0<..<1}"
  shows "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>x. (1 - (1 - q powr x) ^ n))"
        "(LBINT x=0..\<infinity>. 1 - (1 - q powr x) ^ n) = - harm n / ln q"
proof -
  have [simp]: "q powr (log q (1-x)) = 1 - x" if "x \<in> {0<..<1}" for x
    using that assms by (subst powr_log_cancel) auto
  have 1: "((ereal \<circ> (\<lambda>x. log q (1 - x)) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right 0)"
    using assms unfolding zero_ereal_def ereal_tendsto_simps by (auto intro!: tendsto_eq_intros)
  have 2: "((ereal \<circ> (\<lambda>x. log q (1-x)) \<circ> real_of_ereal) \<longlongrightarrow> \<infinity>) (at_left 1)"
  proof -
    have "filterlim ((-) 1) (at_right 0) (at_left (1::real))"
      by (intro filterlim_at_withinI eventually_at_leftI[of 0]) (auto intro!: tendsto_eq_intros)
    then have "LIM x at_left 1. - inverse (ln q) * - ln (1 - x) :> at_top"
      using assms
      by (intro filterlim_tendsto_pos_mult_at_top [OF tendsto_const])
        (auto simp: filterlim_uminus_at_top intro!: filterlim_compose[OF ln_at_0])
    then show ?thesis
      unfolding one_ereal_def ereal_tendsto_simps log_def by (simp add: field_simps)
  qed
  have 3: "set_integrable lborel (einterval 0 1)
     (\<lambda>x. (1 - (1 - q powr (log q (1 - x))) ^ n) * (- 1 / (ln q * (1 - x))))"
  proof -
    have "set_integrable lborel (einterval 0 1) (\<lambda>x. - (1 / ln q) * ((1 - x ^ n) / (1 - x)))"
      by(intro set_integrable_mult_right)
        (auto intro!: harm_integral_0_1_fraction intro: set_integrable_subset simp add: einterval_def)
    then show ?thesis
      by(subst set_integrable_cong_AE[where g="\<lambda>x. - (1 / ln q) * ((1 - x ^ n) / (1 - x))"])
        (auto intro!: eventuallyI simp add: einterval_def)
  qed
  have 4: "LBINT x=0..1. - ((1 - (1 - q powr log q (1 - x)) ^ n) / (ln q * (1 - x))) = - (harm n / ln q)"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = LBINT x=0..1. ((1 - x ^ n) / (1 - x)) * (- 1 / ln q)"
      using assms
      by (intro interval_integral_cong_AE)
      (auto intro!: eventuallyI simp add: max_def einterval_def field_simps)
    also have "\<dots> = harm n * (-1 / ln q)"
      using harm_integral_0_1_fraction by (subst interval_lebesgue_integral_mult_left) auto
    finally show ?thesis
      by auto
  qed
  note sub = interval_integral_substitution_nonneg
             [where f = "(\<lambda>x. (1 - (1 - q powr x) ^ n))" and g="(\<lambda>x. log q (1-x))"
                    and g'="(\<lambda>x. - 1 / (ln q * (1 - x)))" and a = 0 and b = 1]
  show "set_integrable lborel (einterval 0 \<infinity>) (\<lambda>x. (1 - (1 - q powr x) ^ n))"
    using assms 1 2 3 4
    by (intro sub) (auto intro!: derivative_eq_intros mult_nonneg_nonpos2 tendsto_intros power_le_one)
  show "(LBINT x=0..\<infinity>. 1 - (1 - q powr x) ^ n) = - harm n / ln q"
    using assms 1 2 3 4
    by (subst sub) (auto intro!: derivative_eq_intros mult_nonneg_nonpos2 tendsto_intros power_le_one)
qed

lemma one_minus_one_minus_q_x_n_nn_integral:
  fixes q::real
  assumes "q \<in> {0<..<1}"
  shows "set_nn_integral lborel {0..} (\<lambda>x. (1 - (1 - q powr x) ^ n)) =
        LBINT x=0..\<infinity>. 1 - (1 - q powr x) ^ n"
proof -
  have "set_nn_integral  lborel {0..} (\<lambda>x. (1 - (1 - q powr x) ^ n)) =
        nn_integral lborel (\<lambda>x. indicator (einterval 0 \<infinity>) x *  (1 - (1 - q powr x) ^ n))"
    using assms by (intro nn_integral_cong_AE eventually_mono[OF AE_lborel_singleton[of 0]])
      (auto simp add: indicator_def einterval_def)
  also have "\<dots> = ennreal (LBINT x. indicator (einterval 0 \<infinity>) x * (1 - (1 - q powr x) ^ n))"
  using one_minus_one_minus_q_x_n_integral assms
  by(intro nn_integral_eq_integral)
    (auto simp add: indicator_def einterval_def set_integrable_def
      intro!: eventuallyI power_le_one powr_le1)
  finally show ?thesis
    by (simp add: interval_lebesgue_integral_def set_lebesgue_integral_def)
qed

text \<open>
  We can now derive bounds for the expected height.
\<close>

context random_skip_list
begin

definition EH\<^sub>N where "EH\<^sub>N n = measure_pmf.expectation (H\<^sub>N n) real"

lemma EH\<^sub>N_bounds':
  fixes n::nat
  assumes "p \<in> {0<..<1}" "0 < n"
  shows "- harm n / ln q - 1 \<le> EH\<^sub>N n"
     "EH\<^sub>N n \<le> - harm n / ln q"
     "integrable (H\<^sub>N n) real"
proof -
  define f where "f = (\<lambda>x. 1 - (1 - q ^ x) ^ n)"
  define f' where "f' = (\<lambda>x. 1 - (1 - q powr x) ^ n)"
  have q: "q \<in> {0<..<1}"
    unfolding q_def using assms by auto
  have f_descending: "f y \<le> f x" if "x \<le> y" for x y
    unfolding f_def using that q
    by (auto intro!: power_mono simp add: power_decreasing power_le_one_iff)
  have f'_descending: "f' y \<le> f' x" if "x \<le> y" "0 \<le> x" for x y
    unfolding f'_def using that q
    by (auto intro!: power_mono simp add: ln_powr powr_def mult_nonneg_nonpos)
  have [simp]: "harm n / ln q <= 0"
    using harm_nonneg ln_ge_zero_imp_ge_one q by (intro divide_nonneg_neg) auto
  have f_nn_integral_harm:
    "- harm n / ln q \<le> \<integral>\<^sup>+ x. (f x) \<partial>count_space UNIV"
    "(\<integral>\<^sup>+ i. f (i + 1) \<partial>count_space UNIV) \<le> - harm n / ln q"
  proof -
    have "(\<integral>\<^sup>+ i. f (i + 1) \<partial>count_space UNIV) = (\<integral>\<^sup>+x\<in>{0::real..}. (f (nat \<lfloor>x\<rfloor> + 1))\<partial>lborel)"
      using nn_integral_nats_reals by auto
    also have "\<dots> = \<integral>\<^sup>+x\<in>{0::real..}. ennreal (f' (nat \<lfloor>x\<rfloor> + 1))\<partial>lborel"
    proof -
      have "0 \<le> x \<Longrightarrow> (1 - q * q ^ nat \<lfloor>x\<rfloor>) ^ n = (1 - q powr (1 + real_of_int \<lfloor>x\<rfloor>)) ^ n" for x::real
        using q by (subst powr_realpow [symmetric]) (auto simp: powr_add)
      then show ?thesis
        unfolding f_def f'_def using q
        by (auto intro!: nn_integral_cong ennreal_cong  simp add: powr_real_of_int indicator_def)
    qed
    also have "\<dots> \<le> set_nn_integral lborel {0..} f'"
    proof -
      have "x \<le> 1 + real_of_int \<lfloor>x\<rfloor>" for x
        by linarith
      then show ?thesis
        by (auto simp add: indicator_def intro!: f'_descending nn_integral_mono ennreal_leI)
    qed
    also have harm_integral_f': "\<dots> = - harm n / ln q"
      unfolding f'_def using q
      by (auto intro!: ennreal_cong
          simp add: one_minus_one_minus_q_x_n_nn_integral one_minus_one_minus_q_x_n_integral)
    finally show "(\<integral>\<^sup>+ i. f (i + 1) \<partial>count_space UNIV) \<le> - harm n / ln q"
      by simp
    note harm_integral_f'[symmetric]
    also have "set_nn_integral lborel {0..} f' \<le> \<integral>\<^sup>+x\<in>{0::real..}. f' (nat \<lfloor>x\<rfloor>)\<partial>lborel"
      using assms f'_descending
      by (auto simp add: indicator_def intro!: nn_integral_mono ennreal_leI)
    also have "\<dots> = \<integral>\<^sup>+x\<in>{0::real..}. f (nat \<lfloor>x\<rfloor>)\<partial>lborel"
      unfolding f_def f'_def
      using q by (auto intro!: nn_integral_cong ennreal_cong simp add: powr_real_of_int indicator_def)
    also have "\<dots> = (\<integral>\<^sup>+ x. f x \<partial>count_space UNIV)"
      using nn_integral_nats_reals by auto
    finally show "- harm n / ln q \<le> \<integral>\<^sup>+ x. f x \<partial>count_space UNIV"
      by simp
  qed
  then have f1_abs_summable_on: "(\<lambda>i. f (i + 1)) abs_summable_on UNIV"
    unfolding f_def using q
    by (intro nn_integral_finite_imp_abs_sumable_on')
      (auto simp add: f_def le_less_trans intro!: power_le_one mult_le_one)
  then have f_abs_summable_on: "f abs_summable_on {1..}"
    using Suc_le_lessD greaterThan_0
    by (subst abs_summable_on_reindex_bij_betw[symmetric, where g="\<lambda>x. x + 1" and A="UNIV"]) auto
  also have "(f abs_summable_on {1..}) = ((\<lambda>x. measure_pmf.prob (H\<^sub>N n) {x..}) abs_summable_on {1..})"
  proof -
    have "((\<lambda>x. measure_pmf.prob (H\<^sub>N n) {x..}) abs_summable_on {1..}) =
          ((\<lambda>x. measure_pmf.prob (H\<^sub>N n) {x - 1<..}) abs_summable_on {1..})"
      by (auto intro!: measure_prob_cong_0 abs_summable_on_cong)
    also have "\<dots> = (f abs_summable_on {1..})"
      using assms
      by (intro abs_summable_on_cong) (auto simp add: f_def prob_Max_IID_geometric_greaterThan)
    finally show ?thesis
      by simp
  qed
  finally have EH\<^sub>N_sum:
    "EH\<^sub>N n = (\<Sum>\<^sub>ai\<in>{1..}. measure_pmf.prob (H\<^sub>N n) {i..})"
    "integrable (measure_pmf (H\<^sub>N n)) real"
    unfolding EH\<^sub>N_def using expectation_prob_atLeast by auto
  then show "integrable (measure_pmf (H\<^sub>N n)) real"
    by simp
  have EH\<^sub>N_sum': "EH\<^sub>N n = infsetsum f {1..}"
  proof -
    have "EH\<^sub>N n = (\<Sum>\<^sub>ak\<in>{1..}. measure_pmf.prob (H\<^sub>N n) {k - 1<..})"
      unfolding EH\<^sub>N_sum by (auto intro!: measure_prob_cong_0 infsetsum_cong)
    also have "\<dots> = infsetsum f {1..}"
      using assms
      by (intro infsetsum_cong) (auto simp add: f_def prob_Max_IID_geometric_greaterThan)
    finally show ?thesis
      by simp
  qed
  also have "\<dots> = (\<Sum>\<^sub>ak. f (k + 1))"
    using Suc_le_lessD greaterThan_0
    by (subst infsetsum_reindex_bij_betw[symmetric, where g="\<lambda>x. x + 1" and A="UNIV"]) auto
  also have "ennreal \<dots> = (\<integral>\<^sup>+x\<in>{0::real..}. f (nat \<lfloor>x\<rfloor> + 1)\<partial>lborel)"
    using f1_abs_summable_on q
    by (intro infsetsum_set_nn_integral_reals) (auto simp add: f_def mult_le_one power_le_one)
  also have "\<dots> = (\<integral>\<^sup>+ i. f (i + 1) \<partial>count_space UNIV)"
    using nn_integral_nats_reals by auto
  also have "\<dots> \<le> - harm n / ln q"
    using f_nn_integral_harm by auto
  finally show "EH\<^sub>N n \<le> - harm n / ln q"
    by (subst (asm) ennreal_le_iff) (auto)
  have "EH\<^sub>N n + 1 = (\<Sum>\<^sub>ax\<in>{Suc 0..}. f x) + (\<Sum>\<^sub>ax\<in>{0}. f x)"
    using assms by (subst EH\<^sub>N_sum') (auto simp add: f_def)
  also have "\<dots> = infsetsum f UNIV"
    using f_abs_summable_on by (subst infsetsum_Un_disjoint[symmetric]) (auto intro!: infsetsum_cong)
  also have "\<dots> = (\<integral>\<^sup>+x\<in>{0::real..}. f (nat \<lfloor>x\<rfloor>)\<partial>lborel)"
  proof -
    have "f abs_summable_on ({0} \<union> {1..})"
      using f_abs_summable_on by (intro abs_summable_on_union) (auto)
    also have "{0::nat} \<union> {1..} = UNIV"
      by auto
    finally show ?thesis
      using q
      by (intro infsetsum_set_nn_integral_reals) (auto simp add: f_def mult_le_one power_le_one)
  qed
  also have "\<dots> = (\<integral>\<^sup>+ x. f x \<partial>count_space UNIV)"
    using nn_integral_nats_reals by auto
  also have "... \<ge> - harm n / ln q"
    using f_nn_integral_harm by auto
  finally have "- harm n / ln q \<le> EH\<^sub>N n + 1"
    by (subst (asm) ennreal_le_iff) (auto simp add: EH\<^sub>N_def)
  then show "- harm n / ln q - 1 \<le> EH\<^sub>N n"
    by simp
qed

theorem EH\<^sub>N_bounds:
  fixes n::nat
  assumes "p \<in> {0<..<1}"
  shows
    "- harm n / ln q - 1 \<le> EH\<^sub>N n"
    "EH\<^sub>N n \<le> - harm n / ln q"
    "integrable (H\<^sub>N n) real"
proof -
  show "- harm n / ln q - 1 \<le> EH\<^sub>N n"
    using assms EH\<^sub>N_bounds'
    by (cases "n = 0") (auto simp add: EH\<^sub>N_def H\<^sub>N_def H_def SL_def harm_expand)
  show "EH\<^sub>N n \<le> - harm n / ln q"
    using assms EH\<^sub>N_bounds'
    by (cases "n = 0") (auto simp add: EH\<^sub>N_def H\<^sub>N_def H_def SL_def harm_expand)
  show "integrable (H\<^sub>N n) real"
    using assms EH\<^sub>N_bounds'
    by (cases "n = 0") (auto simp add: H\<^sub>N_def H_def SL_def intro!: integrable_measure_pmf_finite)
qed

end (* context random_skip_list *)

subsection \<open>Expected Length of Search Path\<close>

text \<open>
  Let @{term "A::'a::linorder set"} and @{term "f::'a \<Rightarrow> nat"} where f is an abstract description
  of a skip list (assign each value its maximum level). steps A f s u l starts on the rightmost element
  on level s in the skip lists. If possible it moves up, if not it moves to the left. For every step
  up it adds cost u and for every step to the left it adds cost l. steps A f 0 1 1 therefore walks
  from the bottom right corner of a skip list to the top left corner of a skip list and counts
  all steps.
\<close>

\<comment> \<open>NOTE: You could also define steps with lsteps and then prove that the following recursive
    definition holds\<close>

function steps :: "'a :: linorder set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "steps A f l up left = (if A = {} \<or> infinite A
              then 0
              else (let m = Max A in (if f m < l then       steps (A - {m}) f l up left
                                      else (if f m > l then up + steps A f (l + 1) up left
                                      else                  left + steps (A - {m}) f l up left))))"
  by pat_completeness auto
termination
proof (relation "(\<lambda>(A,f,l,a,b). card A) <*mlex*> (\<lambda>(A,f,l,a,b). Max (f ` A) - l) <*mlex*> {}", goal_cases)
  case 1
  then show ?case
    by(intro wf_mlex wf_empty)
next
  case 2
  then show ?case
    by (intro mlex_less) (auto simp: card_gt_0_iff)
next
  case (3 A f l a b x)
  then have "Max (f ` A) - Suc l < Max (f ` A) - l"
    by (meson Max_gr_iff Max_in diff_less_mono2 finite_imageI imageI image_is_empty lessI)
   with 3 have "((A, f, l + 1, a, b), A, f, l, a, b) \<in> (\<lambda>(A, f, l, a, b). Max (f ` A) - l) <*mlex*> {}"
     by (intro mlex_less) (auto)
   with 3 show ?case apply - apply(rule mlex_leq) by auto
next
  case 4
  then show ?case by (intro mlex_less) (auto simp: card_gt_0_iff)
qed

declare steps.simps[simp del]

text \<open>
  lsteps is similar to steps but is using lists instead of sets. This makes the proofs where we use
  induction easier.
\<close>

function lsteps :: "'a list \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lsteps [] f l up left = 0" |
  "lsteps (x#xs) f l up left = (if       f x < l then lsteps xs f l up left
                                 else (if f x > l then up + lsteps (x#xs) f (l + 1) up left
                                 else                        left + lsteps xs f l up left))"
  by pat_completeness auto
termination
proof (relation "(\<lambda>(xs,f,l,a,b). length xs) <*mlex*> (\<lambda>(xs,f,l,a,b).
                 Max (f ` set xs) - l) <*mlex*> {}",
       goal_cases)
  case 1
  then show ?case
    by(intro wf_mlex wf_empty)
next
  case 2
  then show ?case
    by (auto intro: mlex_less simp: card_gt_0_iff)
next
  case (3 n f l a b)
  show ?case
    by (rule mlex_leq) (use 3 in \<open>auto intro: mlex_less mlex_leq intro!:  diff_less_mono2 simp add: Max_gr_iff\<close>)
next
  case 4
  then show ?case by (intro mlex_less) (auto simp: card_gt_0_iff)
qed

declare lsteps.simps(2)[simp del]

lemma steps_empty [simp]: "steps {} f l up left = 0"
  by (simp add: steps.simps)

lemma steps_lsteps: "steps A f l u v = lsteps (rev (sorted_list_of_set A)) f l u v"
proof (cases "finite A \<and> A \<noteq> {}")
  case True
  then show ?thesis
  proof(induction "(rev (sorted_list_of_set A))" f l u v arbitrary: A rule: lsteps.induct)
    case (2 y ys f l u v A)
    then have y_ys: "y = Max A" "ys  = rev (sorted_list_of_set (A - {y}))"
      by (auto simp add: sorted_list_of_set_Max_snoc)
    consider (a) "l < f y" | (b) "f y < l" | (c) "f y = l"
      by fastforce
    then have "steps A f l u v = lsteps (y#ys) f l u v"
    proof cases
      case a
      then show ?thesis
        by (subst steps.simps, subst lsteps.simps) (use y_ys 2 in auto)
    next
      case b
      then show ?thesis
        using y_ys 2(1) by (cases "ys = []") (auto simp add: steps.simps lsteps.simps)
    next
      case c
      then have "steps (A - {Max A}) f l u v =
                 lsteps (rev (sorted_list_of_set (A - {Max A}))) f l u v"
        by (cases "A = {Max A}") (use y_ys 2 in \<open>auto intro!: 2(3) simp add: steps.simps\<close>)
      then show ?thesis
        by (subst steps.simps, subst lsteps.simps) (use y_ys 2 in auto)
    qed
    then show ?case
      using 2 by simp
  qed (auto simp add: steps.simps)
qed (auto simp add: steps.simps)

lemma lsteps_comp_map: "lsteps zs (f \<circ> g) l u v = lsteps (map g zs) f l u v"
  by (induction zs "f \<circ> g" l u v rule: lsteps.induct) (auto simp add: lsteps.simps)

lemma steps_image:
  assumes "finite A" "mono_on g A" "inj_on g A"
  shows "steps A (f \<circ> g) l u v = steps (g ` A) f l u v"
proof -
  have "(sorted_list_of_set (g ` A)) = map g (sorted_list_of_set A)"
    using sorted_list_of_set_image assms by auto
  also have "rev \<dots> = map g (rev (sorted_list_of_set A))"
    using rev_map by auto
  finally show ?thesis
    by (simp add: steps_lsteps lsteps_comp_map)
qed

lemma lsteps_cong:
  assumes "ys = xs" "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x" "l = l'"
  shows "lsteps xs f l u v = lsteps ys g l' u v"
  using assms proof (induction xs f l u v arbitrary: ys l' rule: lsteps.induct)
  case (2 x xs f l up left)
  then show ?case
    by (subst \<open>ys = x # xs\<close>, subst lsteps.simps, subst (2) lsteps.simps) auto
qed (auto)

lemma steps_cong:
  assumes "A = B" "\<And>x. x \<in> A \<Longrightarrow> f x = g x" "l = l'"
  shows   "steps A f l u v = steps B g l' u v"
  using assms
  by (cases "A = {} \<or> infinite A") (auto simp add: steps_lsteps steps.simps intro!: lsteps_cong)

lemma lsteps_f_add':
  shows "lsteps xs f l u v = lsteps xs (\<lambda>x. f x + m) (l + m) u v"
  by  (induction xs f l u v rule: lsteps.induct) (auto simp add: lsteps.simps)

lemma steps_f_add':
  shows "steps A f l u v = steps A (\<lambda>x. f x + m) (l + m) u v"
  by (cases "A = {} \<or> infinite A") (auto simp add: steps_lsteps steps.simps intro!: lsteps_f_add')

lemma lsteps_smaller_set:
  assumes "m \<le> l"
  shows "lsteps xs f l u v = lsteps [x \<leftarrow> xs. m \<le> f x] f l u v"
  using assms by (induction xs f l u v rule: lsteps.induct) (auto simp add: lsteps.simps)

lemma steps_smaller_set:
  assumes "finite A" "m \<le> l"
  shows "steps A f l u v = steps {x\<in>A. f x \<ge> m} f l u v"
  using assms
  by(cases "A = {} \<or> infinite A")
    (auto simp add: steps_lsteps steps.simps rev_filter sorted_list_of_set_filter
      intro!: lsteps_smaller_set)

lemma lsteps_level_greater_fun_image:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x < l"
  shows   "lsteps xs f l u v = 0"
  using assms by (induction xs f l u v rule: lsteps.induct) (auto simp add: lsteps.simps)

lemma lsteps_smaller_card_Max_fun':
  assumes "\<exists>x \<in> set xs. l \<le> f x"
  shows   "lsteps xs f l u v + l * u \<le> v * length xs + u * Max ((f ` (set xs)) \<union> {0})"
  using assms proof (induction xs f l u v rule: lsteps.induct)
  case (1 f l up left)
  then show ?case by (simp)
next
  case (2 x xs f l up left)
  consider "l = f x" "\<exists>y\<in>set xs. l \<le> f y" | "f x = l" "\<not> (\<exists>y\<in>set xs. l \<le> f y)" |
   "f x < l" | "l < f x"
    by fastforce
  then show ?case
  proof cases
    assume a: "l = f x" "\<exists>y\<in>set xs. l \<le> f y"
    have "lsteps (x # xs) f l up left + l * up = lsteps xs f l up left + f x * up + left"
      using a by (auto simp add: lsteps.simps)
    also have "lsteps xs f l up left + f x * up \<le> left * length xs + up * Max (f ` set xs \<union> {0})"
      using a 2 by blast
    also have "up * Max (f ` set xs \<union> {0}) \<le> up * Max (insert (f x) (f ` set xs))"
      by simp
    finally  show ?case
      by auto
  next
    assume a: "f x = l" "\<not> (\<exists>y\<in>set xs. l \<le> f y)"
    have "lsteps (x # xs) f l up left + l * up = lsteps xs f l up left + f x * up + left"
      using a by (auto simp add: lsteps.simps)
    also have "lsteps xs f l up left = 0"
      using a by (subst lsteps_level_greater_fun_image) auto
    also have "f x * up \<le> up * Max (insert (f x) (f ` set xs))"
      by simp
    finally show ?case
      by simp
  next
    assume a: "f x < l"
    then have "lsteps (x # xs) f l up left = lsteps xs f l up left"
      by (auto simp add: lsteps.simps)
    also have "\<dots> + l * up \<le> left * length (x # xs) + up * Max (insert 0 (f ` set xs))"
      using a 2 by auto
    also have "Max (insert 0 (f ` set xs)) \<le> Max (f ` set (x # xs) \<union> {0})"
      by simp
    finally show ?case
      by simp
  next
  assume "f x > l"
    then show ?case
      using 2 by (subst lsteps.simps) auto
  qed
qed

lemma steps_smaller_card_Max_fun':
  assumes "finite A" "\<exists>x\<in>A. l \<le> f x"
  shows   "steps A f l up left + l * up \<le> left * card A + up * Max\<^sub>0 (f ` A)"
proof -
  let ?xs = "rev (sorted_list_of_set A)"
  have "steps A f l up left  = lsteps (rev (sorted_list_of_set A)) f l up left"
    using steps_lsteps by blast
  also have "\<dots> + l * up \<le> left * length ?xs + up * Max (f ` set ?xs \<union> {0})"
    using assms by (intro lsteps_smaller_card_Max_fun') auto
  also have "left * length ?xs = left * card A"
    using assms sorted_list_of_set_length by (auto)
  also have "set ?xs = A"
    using assms by (auto)
  finally show ?thesis
    by simp
qed

lemma lsteps_height:
  assumes  "\<exists>x \<in> set xs. l \<le> f x"
  shows "lsteps xs f l up 0 + up * l = up * Max\<^sub>0 (f ` (set xs))"
  using assms proof (induction xs f l up "0::nat" rule: lsteps.induct)
  case (2 x xs f l up)
  consider "l = f x" "\<exists>y\<in>set xs. l \<le> f y" | "f x = l" "\<not> (\<exists>y\<in>set xs. l \<le> f y)" |
   "f x < l" | "l < f x"
    by fastforce
  then show ?case
 proof cases
   assume 0: "l = f x" "\<exists>y\<in>set xs. l \<le> f y"
    then have 1: "set xs \<noteq> {}"
      using 2 by auto
    then have "\<exists>xa\<in>set xs. f x \<le> f xa"
      using 0 2 by force
    then have "f x \<le> Max (f ` set xs)"
      using 0 2 by (subst Max_ge_iff) auto
    then have "max (f x) (Max (f ` set xs)) = (Max (f ` set xs))"
      using 0 2 by (auto intro!: simp add: max_def)
    then show ?case
      using 0 1 2 by (subst lsteps.simps) (auto)
  next
    assume 0: "f x = l" "\<not> (\<exists>y\<in>set xs. l \<le> f y)"
    then have "Max (insert l (f ` set xs)) = l"
      by (intro Max_eqI) (auto)
    moreover have "lsteps xs f l up 0 = 0"
      using 0 by (subst lsteps_level_greater_fun_image) auto
    ultimately show ?case
       using 0 by (subst lsteps.simps) auto
  next
    assume 0: "f x < l"
    then have 1: "set xs \<noteq> {}"
      using 2 by auto
    then have "\<exists>xa\<in>set xs. f x \<le> f xa"
      using 0 2 by force
    then have " f x \<le> Max (f ` set xs)"
      using 0 2 by (subst Max_ge_iff) auto
    then have "max (f x) (Max (f ` set xs)) = Max (f ` set xs)"
      using 0 2 by (auto intro!: simp add: max_def)
    then show ?case
      using 0 1 2 by (subst lsteps.simps) (auto)
  next
  assume "f x > l"
    then show ?case
      using 2 by (subst lsteps.simps) auto
  qed
qed (simp)

lemma steps_height:
  assumes "finite A"
  shows   "steps A f 0 up 0 = up * Max\<^sub>0 (f ` A)"
proof -
  have "steps A f 0 up 0 = lsteps (rev (sorted_list_of_set A)) f 0 up 0 + up * 0"
    by (subst steps_lsteps) simp
  also have "\<dots> = up * Max (f ` A \<union> {0})" if "A \<noteq> {}"
    using assms that by (subst lsteps_height) auto
  finally show ?thesis
    using assms by (cases "A = {}") (auto)
qed

context random_skip_list
begin

text \<open>
  We can now define the pmf describing the length of the search path in a skip list.
  Like the height it only depends on the number of elements in the skip list's underlying set.
\<close>

definition R where "R A u l = map_pmf (\<lambda>f. steps A f 0 u l) (SL A)"
definition R\<^sub>N :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat pmf" where "R\<^sub>N n u l = R {..<n} u l"


lemma R\<^sub>N_alt_def: "R\<^sub>N n u l = map_pmf (\<lambda>f. steps {..<n} f 0 u l) (SL\<^sub>N n)"
  unfolding SL\<^sub>N_def R\<^sub>N_def R_def by simp

context includes monad_normalisation
begin

lemma R_R\<^sub>N:
  assumes "finite A" "p \<in> {0..1}"
  shows "R A u l = R\<^sub>N (card A) u l"
proof -
  let ?steps = "\<lambda>A f. steps A f 0 u l"
  let ?f' = "bij_mono_map_set_to_nat A"
  have "R A u l = SL A \<bind> (\<lambda>f. return_pmf (?steps A f))"
    unfolding R_def map_pmf_def by simp
  also have "\<dots> = SL\<^sub>N (card A) \<bind> (\<lambda>f. return_pmf (?steps A (f \<circ> ?f')))"
  proof -
    have "?f' x \<notin> {..<card A}" if "x \<notin> A" for x
      using that unfolding bij_mono_map_set_to_nat_def by (auto)
    then show ?thesis
      using assms bij_mono_map_set_to_nat unfolding SL_def SL\<^sub>N_def
      by (subst Pi_pmf_bij_betw[of _ ?f' "{..<card A}"])
        (auto simp add: map_pmf_def)
  qed
  also have "\<dots> = SL\<^sub>N (card A) \<bind> (\<lambda>f. return_pmf (?steps {..<card A} f))"
    using assms bij_mono_map_set_to_nat bij_betw_def by (subst steps_image) (fastforce)+
  finally show ?thesis
    unfolding R\<^sub>N_def R_def SL\<^sub>N_def SL_def by (simp add: map_pmf_def)
qed

text \<open>
  @{const R\<^sub>N} fulfills a recurrence relation. If we move up or to the left the ``remaining'' length of the
  search path is again a slightly different probability distribution over the length.
\<close>

lemma R\<^sub>N_recurrence:
  assumes "0 < n" "p \<in> {0<..1}"
  shows   "R\<^sub>N n u l =
             do {
               b \<leftarrow> bernoulli_pmf p;
               if b then               \<comment> \<open>leftwards\<close>
                 map_pmf (\<lambda>n. n + l) (R\<^sub>N (n - 1) u l)
               else do {               \<comment> \<open>upwards\<close>
                 m \<leftarrow> binomial_pmf (n - 1) (1 - p);
                 map_pmf (\<lambda>n. n + u) (R\<^sub>N (m + 1) u l)
               }
             }"
proof -
  define B where "B = (\<lambda>b. insert (n-1) {x \<in> {..<n - 1}. \<not> b x})"
  have "R\<^sub>N n u l = map_pmf (\<lambda>f. steps {..<n} f 0 u l) (SL\<^sub>N n)"
    by (auto simp add: R\<^sub>N_def R_def SL\<^sub>N_def)
  also have "\<dots> = map_pmf (\<lambda>f. steps {..<n} f 0 u l)
                          (map_pmf (\<lambda>(y, f). f(n-1 := y)) (pair_pmf (geometric_pmf p) (SL\<^sub>N (n - 1))))"
  proof -
    have "{..<n} = insert (n - Suc 0) {..<n - 1}"
      using assms by force
    then have "(Pi_pmf {..<n} 0 (\<lambda>_. geometric_pmf p)) =
                map_pmf (\<lambda>(y, f). f(n - 1 := y)) (pair_pmf (geometric_pmf p)
                     (Pi_pmf {..<n-1} 0 (\<lambda>_. geometric_pmf p)))"
      using assms
      by (subst Pi_pmf_insert[of "{..<n-1}" "n-1" 0 "\<lambda>_. geometric_pmf p", symmetric])  (auto)
    then show ?thesis
      by (simp add: SL\<^sub>N_def SL_def)
  qed
  also have "\<dots> =
        do { g \<leftarrow> geometric_pmf p;
             f \<leftarrow> SL\<^sub>N (n - 1);
             return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l)}"
    by (simp add: case_prod_beta map_pmf_def pair_pmf_def)
  also have "\<dots> =
        do { b \<leftarrow>  bernoulli_pmf p;
             g \<leftarrow> if b then return_pmf 0 else map_pmf Suc (geometric_pmf p);
             f \<leftarrow> SL\<^sub>N (n - 1);
             return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l)}"
    using assms by (subst geometric_bind_pmf_unfold) (auto)
  also have "\<dots> =
        do { b \<leftarrow> bernoulli_pmf p;
             if b
               then do { g \<leftarrow> return_pmf 0;
                         f \<leftarrow> SL\<^sub>N (n - 1);
                         return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l) }
               else do { g \<leftarrow> map_pmf Suc (geometric_pmf p);
                         f \<leftarrow> SL\<^sub>N (n - 1);
                         return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l) }}"
    by (subst bind_pmf_if') (auto)
  also have "do { g \<leftarrow> return_pmf 0;
                       f \<leftarrow> SL\<^sub>N (n - 1);
                       return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l) }  =
              do { f \<leftarrow> SL\<^sub>N (n - 1);
                        return_pmf (steps {..<n} (f(n - 1 := 0)) 0 u l) }"
    by (subst bind_return_pmf) auto
  also have "\<dots> = map_pmf (\<lambda>n. n + l) (map_pmf (\<lambda>f. steps {..<n - 1} f 0 u l) (SL\<^sub>N (n - 1)))"
  proof -
    have I: "{..<n} - {n - Suc 0} = {..<n - Suc 0}"
      by fastforce
    have "Max {..<n} = n - Suc 0"
      using assms by (intro Max_eqI) (auto)
    then have "steps {..<n} (f(n - 1 := 0)) 0 u l = l + steps {..<n - 1} f 0 u l" for f
      using assms by (subst steps.simps) (auto intro!: steps_cong simp add: I simp add: Let_def)
    then show ?thesis
      by (auto simp add: add_ac map_pmf_def)
  qed
  also have "\<dots> = map_pmf (\<lambda>n. n + l) (R\<^sub>N (n - 1) u l)"
    unfolding R\<^sub>N_def R_def SL\<^sub>N_def by simp
  also have "map_pmf Suc (geometric_pmf p) \<bind>
             (\<lambda>g. SL\<^sub>N (n - 1) \<bind>
             (\<lambda>f. return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l)))
             =
             Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p) \<bind>
             (\<lambda>b. map_pmf Suc (geometric_pmf p) \<bind>
             (\<lambda>g. Pi_pmf {x \<in> {..<n - 1}. \<not> b x} 0 (\<lambda>_. map_pmf Suc (geometric_pmf p)) \<bind>
             (\<lambda>f. return_pmf (steps {..<n} (f(n - 1 := g)) 0 u l))))"
    using assms unfolding SL\<^sub>N_def SL_def by (subst Pi_pmf_geometric_filter) (auto)
  also have "\<dots> =
             do {
             b \<leftarrow> Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p);
             f \<leftarrow> Pi_pmf (insert (n-1) {x \<in> {..<n - 1}. \<not> b x}) 0 (\<lambda>_. map_pmf Suc (geometric_pmf p));
             return_pmf (steps {..<n} f 0 u l)}" (is "_ = ?rhs")
    using assms by (subst Pi_pmf_insert') (auto)
  also have "\<dots> =
             do {
               b \<leftarrow> Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p);
               f \<leftarrow> Pi_pmf (B b) 1 (\<lambda>_. map_pmf Suc (geometric_pmf p));
               return_pmf (steps {..<n} (\<lambda>x. if x \<in> (B b) then f x else 0) 0 u l)}"
    by (subst Pi_pmf_default_swap[symmetric, of _ _ _ 1]) (auto simp add: map_pmf_def B_def)
  also have "\<dots> =
             do {
               b \<leftarrow> Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p);
               f \<leftarrow> SL (B b);
               return_pmf (steps {..<n} (\<lambda>x. if x \<in> (B b) then Suc (f x) else 0) 0 u l)}"
  proof -
    have *: "(Suc \<circ> f) x = Suc (f x)" for x and f::"nat \<Rightarrow> nat"
      by simp
    have "(\<lambda>f. return_pmf (steps {..<n} (\<lambda>x. if x \<in> B b then (Suc \<circ> f) x else 0) 0 u l)) =
          (\<lambda>f. return_pmf (steps {..<n} (\<lambda>x. if x \<in> B b then Suc (f x) else 0) 0 u l))" for b
      by (subst *) (simp)
    then show ?thesis
      by (subst Pi_pmf_map[of _ _ 0]) (auto simp add: map_pmf_def B_def SL_def)
  qed
  also have "\<dots> =
               do {
               b \<leftarrow> Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p);
               r \<leftarrow> R (B b) u l;
               return_pmf (u + r)}"
  proof -
    have "steps {..<n} (\<lambda>x. if x \<in> B b then Suc (f x) else 0) 0 u l = u + steps (B b) f 0 u l"
      for f b
    proof -
      have "Max {..<n} = n - 1"
        using assms by (intro Max_eqI) auto
      then have "steps {..<n} (\<lambda>x. if x \<in> B b then Suc (f x) else 0) 0 u l =
              u + (steps {..<n} (\<lambda>x. if x \<in> (B b) then Suc (f x) else 0) 1 u l)"
        unfolding B_def using assms by (subst steps.simps) (auto simp add: Let_def)
      also have "steps {..<n} (\<lambda>x. if x \<in> (B b) then Suc (f x) else 0) 1 u l =
                   steps (B b) (\<lambda>x. if x \<in> (B b) then Suc (f x) else 0) 1 u l"
      proof -
        have "{x \<in> {..<n}. 1 \<le> (if x \<in> B b then Suc (f x) else 0)} = B b"
          using assms unfolding B_def by force
        then show ?thesis
          by (subst steps_smaller_set[of _ 1]) auto
      qed
      also have "\<dots> = steps (B b) (\<lambda>x. f x + 1) 1 u l"
        by (rule steps_cong) (auto)
      also have "\<dots> = steps (B b) f 0 u l"
        by (subst (2) steps_f_add'[of _ _ _ _ _ 1]) simp
      finally show ?thesis
        by auto
    qed
    then show ?thesis
      by (simp add: R_def map_pmf_def)
  qed
  also have "\<dots> = do {
                   b \<leftarrow> Pi_pmf {..<n - 1} False (\<lambda>_. bernoulli_pmf (1 - p));
                   let m = 1 + card {x. x < n - 1 \<and> b x};
                   r \<leftarrow> R {..<m} u l;
                   return_pmf (u + r)}"
  proof -
    have *: "card (insert (n - Suc 0) {x. x < n - 1 \<and> b x}) =
              (Suc (card {x. x < n - 1 \<and> b x}))" for b
      using assms by (auto simp add: card_insert_if)
    have "Pi_pmf {..<n - 1} True (\<lambda>_. bernoulli_pmf p) =
              Pi_pmf {..<n - 1} True (\<lambda>_. map_pmf Not (bernoulli_pmf (1 - p)))"
      using assms by (subst bernoulli_pmf_Not) auto
    also have "\<dots> = map_pmf ((\<circ>) Not) (Pi_pmf {..<n - 1}  False (\<lambda>_. bernoulli_pmf (1 - p)))"
      using assms by (subst Pi_pmf_map[of _ _ False]) auto
    finally show ?thesis
      unfolding B_def using assms *
      by (subst R_R\<^sub>N) (auto simp add: R_R\<^sub>N map_pmf_def)
  qed
  also have "\<dots> = binomial_pmf (n - 1) (1 - p) \<bind> (\<lambda>m. map_pmf (\<lambda>n. n + u) (R\<^sub>N (m + 1) u l))"
    using assms
    by (subst binomial_pmf_altdef'[where A = "{..<n - 1}" and dflt = "False"])
      (auto simp add: R\<^sub>N_def R_def SL_def map_pmf_def ac_simps)
  finally show ?thesis
    by simp
qed

end (* context includes monad_normalisation *)

text \<open>
  The expected height and length of search path defined as non-negative integral. It's easier
  to prove the recurrence relation of the expected length of the search path using non-negative
  integrals.
\<close>

definition NH\<^sub>N where "NH\<^sub>N n = nn_integral (H\<^sub>N n) real"
definition NR\<^sub>N where "NR\<^sub>N n u l = nn_integral (R\<^sub>N n u l) real"

lemma NH\<^sub>N_EH\<^sub>N:
  assumes "p \<in> {0<..<1}"
  shows "NH\<^sub>N n = EH\<^sub>N n"
  using assms EH\<^sub>N_bounds unfolding EH\<^sub>N_def NH\<^sub>N_def by (subst nn_integral_eq_integral) (auto)

lemma R\<^sub>N_0 [simp]: "R\<^sub>N 0 u l = return_pmf 0"
  unfolding R\<^sub>N_def R_def SL_def by (auto simp add: steps.simps)

lemma NR\<^sub>N_bounds:
  fixes u l::nat
  shows "NR\<^sub>N n u l \<le> l * n + u * NH\<^sub>N n"
proof -
  have "NR\<^sub>N n u l = \<integral>\<^sup>+ x. x \<partial>measure_pmf (R\<^sub>N n u l)"
    unfolding NR\<^sub>N_def R\<^sub>N_alt_def
    by (simp add: ennreal_of_nat_eq_real_of_nat)
  also have "\<dots> \<le> \<integral>\<^sup>+ x. x \<partial>(measure_pmf (map_pmf (\<lambda>f. l * n + u * Max\<^sub>0 (f ` {..<n})) (SL\<^sub>N n)))"
    using of_nat_mono[OF steps_smaller_card_Max_fun'[of "{..<n}" 0 _ u l]] unfolding R\<^sub>N_alt_def
    by (cases "n = 0") (auto intro!: nn_integral_mono)
  also have "\<dots> = l * n + u * NH\<^sub>N n"
    unfolding NH\<^sub>N_def H\<^sub>N_def H_def SL\<^sub>N_def
    by (auto simp add: nn_integral_add nn_integral_cmult ennreal_of_nat_eq_real_of_nat ennreal_mult)
  finally show "NR\<^sub>N n u l \<le> l * n + u * NH\<^sub>N n"
    by simp
qed

lemma NR\<^sub>N_recurrence:
  assumes "0 < n" "p \<in> {0<..<1}"
  shows "NR\<^sub>N n u l = (p * (l + NR\<^sub>N (n - 1) u l) +
                     q * (u + (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * (pmf (binomial_pmf (n - 1) q) k))))
                     / (1 - (q ^ n))"
proof -
  define B where "B = (\<lambda>n k. pmf (binomial_pmf n q) k)"
  have q: "q \<in> {0<..<1}"
    using assms unfolding q_def by auto
  then have "q ^ n < 1"
    using assms power_Suc_less_one by (induction n) (auto)
  then have qn: "q ^ n \<in> {0<..<1}"
    using assms q by (auto)
  have "NR\<^sub>N n u l = p * (l + NR\<^sub>N (n - 1) u l) +
                    q * (u + \<integral>\<^sup>+ k. NR\<^sub>N (k + 1) u l  \<partial>measure_pmf (binomial_pmf (n - 1) q))"
    using assms unfolding NR\<^sub>N_def
    by(subst R\<^sub>N_recurrence)
      (auto simp add: field_simps nn_integral_add q_def ennreal_of_nat_eq_real_of_nat)
  also have "(\<integral>\<^sup>+ m. NR\<^sub>N (m + 1) u l  \<partial>measure_pmf (binomial_pmf (n - 1) q)) =
    (\<Sum>k\<le>n - 1. NR\<^sub>N (k + 1) u l * B (n - 1) k)"
    using assms unfolding B_def q_def
    by (auto simp add: nn_integral_measure_pmf_finite)
  also have "\<dots> = (\<Sum>k\<in>{..<n - 1} \<union> {n - 1}. NR\<^sub>N (k + 1) u l * B (n - 1) k)"
    by (rule sum.cong) (auto)
  also have "\<dots> = (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * B (n - 1) k) + NR\<^sub>N n u l * q ^ (n - 1)"
    unfolding B_def q_def using assms by (subst sum.union_disjoint) (auto)
  finally have "NR\<^sub>N n u l = p * (l + NR\<^sub>N (n - 1) u l) +
                            q * ((\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * B (n - 1) k) + u) +
                            NR\<^sub>N n u l * (q ^ (n - 1)) * q"
    using assms by (auto simp add: field_simps numerals)
  also have "NR\<^sub>N n u l * (q ^ (n - 1)) * q = (q ^ n) * NR\<^sub>N n u l"
    using q power_minus_mult[of _ q] assms
    by (subst mult_ac, subst ennreal_mult[symmetric], auto simp add: mult_ac)
  finally have 1: "NR\<^sub>N n u l = p * (l + NR\<^sub>N (n - 1) u l) +
                               q * (u + (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * (B (n - 1) k))) +
                               (q ^ n) * NR\<^sub>N n u l "
    by (simp add: add_ac)
  have "x - z = y" if "x = y + z" "z \<noteq> \<top>" for x y z::ennreal
     using that by (subst that) (auto)
   have "NR\<^sub>N n u l \<le> l * n + u * NH\<^sub>N n"
     using NR\<^sub>N_bounds by (auto simp add: ennreal_of_nat_eq_real_of_nat)
   also have "NH\<^sub>N n = EH\<^sub>N n"
     using assms NH\<^sub>N_EH\<^sub>N by auto
   also have "(l * n) + u * ennreal (EH\<^sub>N n) < \<top>"
     by (simp add: ennreal_mult_less_top of_nat_less_top)
   finally have 3: "NR\<^sub>N n u l \<noteq> \<top>"
     by simp
  have 2: "x = y / (1 - a)" if "x = y + a * x" and t: "x \<noteq> \<top>" "a \<in> {0<..<1}" for x y::ennreal
          and a::real
  proof -
    have "y = x - a * x"
      using t by (subst that) (auto simp add: ennreal_mult_eq_top_iff)
    also have "\<dots> = x * (ennreal 1 - ennreal a)"
      using that by (auto simp add: mult_ac ennreal_right_diff_distrib)
    also have "ennreal 1 - ennreal a = ennreal (1 - a)"
      using that by (subst ennreal_minus) (auto)
    also have "x * (1 - a) / (1 - a) = x"
      using that ennreal_minus_eq_0 not_less by (subst mult_divide_eq_ennreal) auto
    finally show ?thesis
      by simp
  qed
  have "NR\<^sub>N n u l = (p * (l + NR\<^sub>N (n - 1) u l) +
                     q * (u + (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * (B (n - 1) k))))
                   / (1 - (q ^ n))"
    using 1 3 assms qn by (intro 2) auto
  then show ?thesis
    unfolding B_def by simp
qed

lemma NR\<^sub>n_NH\<^sub>N: "NR\<^sub>N n u 0 = u * NH\<^sub>N n"
proof -
  have "NR\<^sub>N n u 0 = \<integral>\<^sup>+ f. steps {..<n} f 0 u 0 \<partial>measure_pmf (SL\<^sub>N n)"
    unfolding NR\<^sub>N_def R\<^sub>N_alt_def by (auto simp add: ennreal_of_nat_eq_real_of_nat)
  also have "\<dots> = \<integral>\<^sup>+ f. of_nat u * of_nat (Max\<^sub>0 (f ` {..<n})) \<partial>measure_pmf (SL\<^sub>N n)"
    by (intro nn_integral_cong) (auto simp add: steps_height)
  also have "\<dots> = u * NH\<^sub>N n"
    by (auto simp add: NH\<^sub>N_def H\<^sub>N_def H_def SL\<^sub>N_def  ennreal_of_nat_eq_real_of_nat nn_integral_cmult)
  finally show ?thesis
    by simp
qed

lemma NR\<^sub>N_recurrence':
  assumes "0 < n" "p \<in> {0<..<1}"
  shows "NR\<^sub>N n u l = (p * l + p * NR\<^sub>N (n - 1) u l +
                     q * u + q * (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u l * (pmf (binomial_pmf (n - 1) q) k)))
                     / (1 - (q ^ n))"
  unfolding NR\<^sub>N_recurrence[OF assms]
  by (auto simp add: field_simps ennreal_of_nat_eq_real_of_nat ennreal_mult' ennreal_mult'')


lemma NR\<^sub>N_l_0:
  assumes "0 < n" "p \<in> {0<..<1}"
  shows "NR\<^sub>N n u 0 = (p * NR\<^sub>N (n - 1) u 0 +
                     q * (u + (\<Sum>k<n - 1. NR\<^sub>N (k + 1) u 0 * (pmf (binomial_pmf (n - 1) q) k))))
                     / (1 - (q ^ n))"
  unfolding NR\<^sub>N_recurrence[OF assms] by (simp)

lemma NR\<^sub>N_u_0:
  assumes "0 < n" "p \<in> {0<..<1}"
  shows "NR\<^sub>N n 0 l = (p * (l + NR\<^sub>N (n - 1) 0 l) +
                     q * (\<Sum>k<n - 1. NR\<^sub>N (k + 1) 0 l * (pmf (binomial_pmf (n - 1) q) k)))
                     / (1 - (q ^ n))"
  unfolding NR\<^sub>N_recurrence[OF assms] by (simp)

lemma NR\<^sub>N_0[simp]: "NR\<^sub>N 0 u l = 0"
  unfolding NR\<^sub>N_def R\<^sub>N_def R_def by (auto)

lemma NR\<^sub>N_1:
  assumes "p \<in> {0<..<1}"
  shows "NR\<^sub>N 1 u l = (u * q + l * p) / p"
proof -
  have "NR\<^sub>N 1 u l = (ennreal p * of_nat l + ennreal q * of_nat u) / ennreal (1 - q)"
    using assms by (subst NR\<^sub>N_recurrence) auto
  also have "(ennreal p * of_nat l + ennreal q * of_nat u) = (u * q + l * p)"
    using assms q_def by (subst ennreal_plus)
      (auto simp add: field_simps ennreal_mult' ennreal_of_nat_eq_real_of_nat)
  also have "\<dots> / ennreal (1 - q) = ennreal ((u * q + l * p) / (1 - q))"
     using q_def assms by (intro divide_ennreal) auto
  finally show ?thesis
    unfolding q_def by simp
qed

lemma NR\<^sub>N_NR\<^sub>N_l_0:
  assumes n: "0 < n" and p: "p \<in> {0<..<1}" and "u \<ge> 1"
  shows "NR\<^sub>N n u 0 = (u * q / (u * q + l * p)) * NR\<^sub>N n u l"
  using n proof (induction n rule: less_induct)
  case (less i)
  have 1: "0 < u * q"
    unfolding q_def using assms by simp
  moreover have "0 \<le> l * p"
    using assms by auto
  ultimately have 2: "0 < u * q + l * p"
    by arith
  define c where "c = ennreal (u * q / (u * q + l * p))"
  have [simp]: "c / c = 1"
  proof -
    have "u * q / (u * q + l * p) \<noteq> 0"
      using assms q_def 2 by auto
    then show ?thesis
      unfolding c_def using p q_def by (auto intro!: ennreal_divide_self)
  qed
  show ?case
  proof (cases "i = 1")
    case True
    have "c * NR\<^sub>N i u l = c * ((u * q + l * p) / p)"
      unfolding c_def True by (subst NR\<^sub>N_1[OF p]) auto
    also have "\<dots> = ennreal ((u * q / (u * q + l * p)) * ((u * q + l * p) / p))"
      unfolding c_def using assms q_def by (subst ennreal_mult'') auto
    also have "(u * q / (u * q + l * p)) * ((u * q + l * p) / p) = u * q / p"
    proof -
      have I: "(a / b) * (b / c) = a / c" if "0 < b" for a b c::"real"
        using that by (auto)
      show ?thesis
        using 2 q_def by (intro I) auto
    qed
    also have "\<dots> = NR\<^sub>N i u 0"
      unfolding True c_def by (subst NR\<^sub>N_1[OF p]) (auto)
    finally show ?thesis
      unfolding c_def using True by simp
  next
    case False
    then have i: "i > 1"
      using less by auto
    define c where "c = ennreal (u * q / (u * q + l * p))"
    define B where "B = (\<Sum>k<i - 1. NR\<^sub>N (k + 1) u l * ennreal (pmf (binomial_pmf (i - 1) q) k))"
    have "NR\<^sub>N i u 0 = (p * NR\<^sub>N (i - 1) u 0 +
                     q * (u + (\<Sum>k<i - 1. NR\<^sub>N (k + 1) u 0 * (pmf (binomial_pmf (i - 1) q) k))))
                     / (1 - (q ^ i))"
      using less assms by (subst NR\<^sub>N_l_0) auto
    also have "q * (u + (\<Sum>k<i - 1. NR\<^sub>N (k + 1) u 0 * (pmf (binomial_pmf (i - 1) q) k))) =
             q * u + q * (\<Sum>k<i - 1. NR\<^sub>N (k + 1) u 0 * (pmf (binomial_pmf (i - 1) q) k))"
      using assms q_def
      by (auto simp add: field_simps ennreal_of_nat_eq_real_of_nat ennreal_mult)
    also have "NR\<^sub>N (i - 1) u 0 = c * NR\<^sub>N (i - 1) u l"
      unfolding c_def using less i by (intro less) (auto)
    also have "(\<Sum>k<i - 1. NR\<^sub>N (k + 1) u 0 * ennreal (pmf (binomial_pmf (i - 1) q) k)) =
             (\<Sum>k<i - 1. c * NR\<^sub>N (k + 1) u l * ennreal (pmf (binomial_pmf (i - 1) q) k))"
      by (auto intro!: sum.cong simp add: less c_def)
    also have "\<dots> = c * B"
      unfolding B_def by (subst sum_distrib_left) (auto intro!: sum.cong mult_ac)
    also have "q * (c * B) = c * (q * B)"
      by (simp add: mult_ac)
    also have "ennreal (q * real u) = q * u * ((u * q + l * p) / (u * q + l * p))"
      using assms 2 by (auto simp add: field_simps q_def)
    also have "\<dots> = c * (real u * q + real l * p)"
      unfolding c_def using 2 by (subst ennreal_mult''[symmetric]) (auto simp add: mult_ac)
    also have "c * ennreal (real u * q + real l * p) + c * (ennreal q * B) =
             c * (ennreal (real u * q + real l * p) + (ennreal q * B))"
      by (auto simp add: field_simps)
    also have "ennreal p * (c * NR\<^sub>N (i - 1) u l) = c * (ennreal p * NR\<^sub>N (i - 1) u l)"
      by (simp add: mult_ac)
    also have "(c * (ennreal p * NR\<^sub>N (i - 1) u l) + c * (ennreal (u * q + l * p) + ennreal q * B))
            = c * ((ennreal p * NR\<^sub>N (i - 1) u l) + (ennreal (u * q + l * p) + ennreal q * B))"
      by (auto simp add: field_simps)
    also have " c * (ennreal p * NR\<^sub>N (i - 1) u l + (ennreal (u * q + l * p) + ennreal q * B)) / ennreal (1 - q ^ i)
         =  c * ((ennreal p * NR\<^sub>N (i - 1) u l + (ennreal (u * q + l * p) + ennreal q * B)) / ennreal (1 - q ^ i))"
      by (auto simp add: ennreal_times_divide)
    also have "(ennreal p * NR\<^sub>N (i - 1) u l + (ennreal (real u * q + real l * p) + ennreal q * B)) / ennreal (1 - q ^ i)
        = NR\<^sub>N i u l"
      apply(subst (2) NR\<^sub>N_recurrence')
      using i assms q_def by
        (auto simp add: field_simps B_def ennreal_of_nat_eq_real_of_nat ennreal_mult' ennreal_mult'')
    finally show ?thesis
      unfolding c_def by simp
  qed
qed

text \<open>
  Assigning 1 as the cost for going up and/or left, we can now show the relation between the
  expected length of the reverse search path and the expected height.
\<close>

definition EL\<^sub>N where "EL\<^sub>N n = measure_pmf.expectation (R\<^sub>N n 1 1) real"


theorem EH\<^sub>N_EL\<^sub>s\<^sub>p:
  assumes "p \<in> {0<..<1}"
  shows "1 / q * EH\<^sub>N n = EL\<^sub>N n"
proof -
  have 1: "ennreal (1 / y * x) = r" if "ennreal x = y * r" "x \<ge> 0" "y > 0"
    for x y::real and r::ennreal
  proof -
    have "ennreal ((1 / y) * x) = ennreal (1 / y) * ennreal x"
      using that apply(subst ennreal_mult'') by auto
    also note that(1)
    also have "ennreal (1 / y) * (ennreal y * r) = ennreal ((1 / y) * y) * r"
      using that by (subst ennreal_mult'') (auto simp add: mult_ac)
    also have "(1 / y) * y = 1"
      using that by (auto)
    finally show ?thesis
      by auto
  qed
  have "EH\<^sub>N n = NH\<^sub>N n"
    using NH\<^sub>N_EH\<^sub>N assms by auto
  also have "NH\<^sub>N n = NR\<^sub>N n 1 0"
    using NR\<^sub>n_NH\<^sub>N by auto
  also have "NR\<^sub>N n 1 0 = q * NR\<^sub>N n 1 1" if "n > 0"
    using NR\<^sub>N_NR\<^sub>N_l_0[of _ 1 1] that assms q_def by force
  finally have "ennreal (EH\<^sub>N n) = q * NR\<^sub>N n 1 1" if "n > 0"
    using that by blast
  then have "1 / q * EH\<^sub>N n = NR\<^sub>N n 1 1" if "n > 0"
    using that assms q_def by (intro 1) (auto simp add: EH\<^sub>N_def H\<^sub>N_def H_def)
  moreover have "1 / q * EH\<^sub>N n = NR\<^sub>N n 1 1" if "n = 0"
    unfolding that by (auto simp add: EH\<^sub>N_def H\<^sub>N_def H_def)
  ultimately have 2: "ennreal (1 / q * EH\<^sub>N n) = NR\<^sub>N n 1 1"
    by blast
  also have "NR\<^sub>N n 1 1 = EL\<^sub>N n"
    using 2 assms EH\<^sub>N_bounds unfolding EL\<^sub>N_def NR\<^sub>N_def
    by(subst nn_integral_eq_integral)
      (auto intro!: integrableI_nn_integral_finite[where x="EH\<^sub>N n / q"])
  finally show ?thesis
    using assms q_def ennreal_inj unfolding EL\<^sub>N_def EH\<^sub>N_def H\<^sub>N_def H_def SL_def
    by (auto)
qed

end (* context random_skip_list *)

thm random_skip_list.EH\<^sub>N_EL\<^sub>s\<^sub>p[unfolded random_skip_list.q_def]
    random_skip_list.EH\<^sub>N_bounds'[unfolded random_skip_list.q_def]


end
