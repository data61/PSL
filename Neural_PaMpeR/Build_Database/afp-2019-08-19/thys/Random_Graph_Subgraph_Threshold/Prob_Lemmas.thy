theory Prob_Lemmas
imports
  "HOL-Probability.Probability"
  Girth_Chromatic.Girth_Chromatic
  Ugraph_Misc
begin

section\<open>Lemmas about probabilities\<close>

text\<open>In this section, auxiliary lemmas for computing bounds on expectation and probabilites
of random variables are set up.\<close>

subsection\<open>Indicator variables and valid probability values\<close>

abbreviation rind :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where
"rind \<equiv> indicator"

lemma product_indicator:
  "rind A x * rind B x = rind (A \<inter> B) x"
unfolding indicator_def
by auto

text\<open>We call a real number `valid' iff it is in the range 0 to 1, inclusively, and additionally
`nonzero' iff it is neither 0 nor 1.\<close>

abbreviation "valid_prob (p :: real) \<equiv> 0 \<le> p \<and> p \<le> 1"
abbreviation "nonzero_prob (p :: real) \<equiv> 0 < p \<and> p < 1"

text\<open>A function @{typ "'a \<Rightarrow> real"} is a `valid probability function' iff each value in the image
is valid, and similarly for `nonzero'.\<close>

abbreviation "valid_prob_fun f \<equiv> (\<forall>n. valid_prob (f n))"
abbreviation "nonzero_prob_fun f \<equiv> (\<forall>n. nonzero_prob (f n))"

lemma nonzero_fun_is_valid_fun: "nonzero_prob_fun f \<Longrightarrow> valid_prob_fun f"
by (simp add: less_imp_le)

subsection\<open>Expectation and variance\<close>

context prob_space
begin

text\<open>Note that there is already a notion of independent sets (see @{term indep_set}), but we use
the following -- simpler -- definition:\<close>

definition "indep A B \<longleftrightarrow> prob (A \<inter> B) = prob A * prob B"

text\<open>The probability of an indicator variable is equal to its expectation:\<close>

lemma expectation_indicator:
  "A \<in> events \<Longrightarrow> expectation (rind A) = prob A"
  by simp

text\<open>For a non-negative random variable @{term X}, the Markov inequality gives the following
upper bound: \[ \Pr[X \ge a] \le \frac{\Ex[X]}{a} \]\<close>

lemma markov_inequality:
  assumes "\<And>a. 0 \<le> X a" and "integrable M X" "0 < t"
  shows "prob {a \<in> space M. t \<le> X a} \<le> expectation X / t"
proof -
  \<comment> \<open>proof adapted from @{thm [source] edge_space.Markov_inequality}, but generalized to arbitrary
       @{term prob_space}s\<close>
  have "(\<integral>\<^sup>+ x. ennreal (X x) \<partial>M) = (\<integral>x. X x \<partial>M)"
    using assms by (intro nn_integral_eq_integral) auto
  thus ?thesis
    using assms nn_integral_Markov_inequality[of X M "space M" "1 / t"]
    by (auto cong: nn_integral_cong simp: emeasure_eq_measure ennreal_mult[symmetric])
qed

text\<open>$\Var[X] = \Ex[X^2] - \Ex[X]^2 $\<close>

lemma variance_expectation:
  fixes X :: "'a \<Rightarrow> real"
  assumes "integrable M (\<lambda>x. (X x)^2)" and "X \<in> borel_measurable M"
  shows
    "integrable M (\<lambda>x. (X x - expectation X)^2)" (is ?integrable)
    "variance X = expectation (\<lambda>x. (X x)^2) - (expectation X)^2" (is ?variance)
proof -
  have int: "integrable M X"
    using integrable_squareD[OF assms] by simp

  have "(\<lambda>x. (X x - expectation X)^2) = (\<lambda>x. (X x)^2 + (expectation X)^2 - (2 * X x * expectation X))"
    by (simp only: power2_diff)
  hence
    "variance X = expectation (\<lambda>x. (X x)^2) + (expectation X)^2 + expectation (\<lambda>x. - (2 * X x * expectation X))"
    ?integrable
    using integral_add by (simp add: int assms prob_space)+

  thus ?variance ?integrable
    by (simp add: int power2_eq_square)+
qed

text\<open>A corollary from the Markov inequality is Chebyshev's inequality, which gives an upper
bound for the deviation of a random variable from its expectation:
\[ \Pr[\left| Y - \Ex[Y] \right| \ge s] \le \frac{\Var[X]}{a^2} \]\<close>

lemma chebyshev_inequality:
  fixes Y :: "'a \<Rightarrow> real"
  assumes Y_int: "integrable M (\<lambda>y. (Y y)^2)"
  assumes Y_borel: "Y \<in> borel_measurable M"
  fixes s :: "real"
  assumes s_pos: "0 < s"
  shows "prob {a \<in> space M. s \<le> \<bar>Y a - expectation Y\<bar>} \<le> variance Y / s^2"
proof -
  let ?X = "\<lambda>a. (Y a - expectation Y)^2"
  let ?t = "s^2"

  have "0 < ?t"
    using s_pos by simp
  hence "prob {a \<in> space M. ?t \<le> ?X a} \<le> variance Y / s^2"
    using markov_inequality variance_expectation[OF Y_int Y_borel] by (simp add: field_simps)
  moreover have "{a \<in> space M. ?t \<le> ?X a} = {a \<in> space M. s \<le> \<bar>Y a - expectation Y\<bar>}"
    using abs_le_square_iff s_pos by force
  ultimately show ?thesis
    by simp
qed

text\<open>Hence, we can derive an upper bound for the probability that a random variable is $0$.\<close>

corollary chebyshev_prob_zero:
  fixes Y :: "'a \<Rightarrow> real"
  assumes Y_int: "integrable M (\<lambda>y. (Y y)^2)"
  assumes Y_borel: "Y \<in> borel_measurable M"
  assumes \<mu>_pos: "expectation Y > 0"
  shows "prob {a \<in> space M. Y a = 0} \<le> expectation (\<lambda>y. (Y y)^2) / (expectation Y)^2 - 1"
proof -
  let ?s = "expectation Y"

  have "prob {a \<in> space M. Y a = 0} \<le> prob {a \<in> space M. ?s \<le> \<bar>Y a - ?s\<bar>}"
    using Y_borel by (auto intro!: finite_measure_mono borel_measurable_diff borel_measurable_abs borel_measurable_le)
  also have "\<dots> \<le> variance Y / ?s^2"
    using assms by (fact chebyshev_inequality)
  also have "\<dots> = (expectation (\<lambda>y. (Y y)^2) - ?s^2) / ?s^2"
    using Y_int Y_borel by (simp add: variance_expectation)
  also have "\<dots> = expectation (\<lambda>y. (Y y)^2) / ?s^2 - 1"
    using \<mu>_pos by (simp add: field_simps)
  finally show ?thesis .
qed

end

subsection\<open>Sets of indicator variables\<close>

text\<open>\label{sec:delta}
This section introduces some inequalities about expectation and other values related to the sum of
a set of random indicators.\<close>

locale prob_space_with_indicators = prob_space +
  fixes I :: "'i set"
  assumes finite_I: "finite I"

  fixes A :: "'i \<Rightarrow> 'a set"
  assumes A: "A ` I \<subseteq> events"

  assumes prob_non_zero: "\<exists>i \<in> I. 0 < prob (A i)"
begin

text\<open>We call the underlying sets @{term "A i"} for each @{term "i \<in> I"}, and the corresponding
indicator variables @{term "X i"}. The sum is denoted by @{term Y}, and its expectation by
@{term \<mu>}.\<close>

definition "X i = rind (A i)"
definition "Y x = (\<Sum>i \<in> I. X i x)"

definition "\<mu> = expectation Y"

text\<open>In the lecture notes, the following two relations are called $\sim$ and $\nsim$,
respectively. Note that they are not the opposite of each other.\<close>

abbreviation ineq_indep :: "'i \<Rightarrow> 'i \<Rightarrow> bool" where
"ineq_indep i j \<equiv> (i \<noteq> j \<and> indep (A i) (A j))"

abbreviation ineq_dep :: "'i \<Rightarrow> 'i \<Rightarrow> bool" where
"ineq_dep i j \<equiv> (i \<noteq> j \<and> \<not>indep (A i) (A j))"

definition "\<Delta>\<^sub>a = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> i \<noteq> j. prob (A i \<inter> A j))"
definition "\<Delta>\<^sub>d = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> ineq_dep i j. prob (A i \<inter> A j))"

lemma \<Delta>_zero:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep (A i) (A j)"
  shows "\<Delta>\<^sub>d = 0"
proof -
  {
    fix i
    assume "i \<in> I"
    hence "{j. j \<in> I \<and> ineq_dep i j} = {}"
      using assms by auto
    hence "(\<Sum>j | j \<in> I \<and> ineq_dep i j. prob (A i \<inter> A j)) = 0"
      using sum.empty by metis
  }
  hence "\<Delta>\<^sub>d = (0 :: real) * card I"
    unfolding \<Delta>\<^sub>d_def by simp
  thus ?thesis
    by simp
qed

lemma A_events[measurable]: "i \<in> I \<Longrightarrow> A i \<in> events"
using A by auto

lemma expectation_X_Y: "\<mu> = (\<Sum>i\<in>I. expectation (X i))"
unfolding \<mu>_def Y_def[abs_def] X_def
by (simp add: less_top[symmetric])

lemma expectation_X_non_zero: "\<exists>i \<in> I. 0 < expectation (X i)"
unfolding X_def using prob_non_zero expectation_indicator by simp

corollary \<mu>_non_zero[simp]: "0 < \<mu>"
unfolding expectation_X_Y
using expectation_X_non_zero
by (auto intro!: sum_lower finite_I
         simp add: expectation_indicator X_def)

lemma \<Delta>\<^sub>d_nonneg: "0 \<le> \<Delta>\<^sub>d"
unfolding \<Delta>\<^sub>d_def
by (simp add: sum_nonneg)

corollary \<mu>_sq_non_zero[simp]: "0 < \<mu>^2"
by (rule zero_less_power) simp

lemma Y_square_unfold: "(\<lambda>x. (Y x)^2) = (\<lambda>x. \<Sum>i \<in> I. \<Sum>j \<in> I. rind (A i \<inter> A j) x)"
unfolding fun_eq_iff Y_def X_def
by (auto simp: sum_square product_indicator)

lemma integrable_Y_sq[simp]: "integrable M (\<lambda>y. (Y y)^2)"
unfolding Y_square_unfold
by (simp add: sets.Int less_top[symmetric])

lemma measurable_Y[measurable]: "Y \<in> borel_measurable M"
unfolding Y_def[abs_def] X_def by simp

lemma expectation_Y_\<Delta>: "expectation (\<lambda>x. (Y x)^2) = \<mu> + \<Delta>\<^sub>a"
proof -
  let ?ei = "\<lambda>i j. expectation (rind (A i \<inter> A j))"

  have "expectation (\<lambda>x. (Y x)^2) = (\<Sum>i \<in> I. \<Sum>j \<in> I. ?ei i j)"
    unfolding Y_square_unfold by (simp add: less_top[symmetric])
  also have "\<dots> = (\<Sum>i \<in> I. \<Sum>j \<in> I. if i = j then ?ei i j else ?ei i j)"
    by simp
  also have "\<dots> = (\<Sum>i \<in> I. (\<Sum>j | j \<in> I \<and> i = j. ?ei i j) + (\<Sum>j | j \<in> I \<and> i \<noteq> j. ?ei i j))"
    by (simp only: sum_split[OF finite_I])
  also have "\<dots> = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> i = j. ?ei i j) + (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> i \<noteq> j. ?ei i j)" (is "_ = ?lhs + ?rhs")
    by (fact sum.distrib)
  also have "\<dots> =  \<mu> + \<Delta>\<^sub>a"
    proof -
      have "?lhs = \<mu>"
        proof -
          {
            fix i
            assume i: "i \<in> I"
            have "(\<Sum>j | j \<in> I \<and> i = j. ?ei i j) = (\<Sum>j | j \<in> I \<and> i = j. ?ei i i)"
              by simp
            also have "\<dots> = (\<Sum>j | i = j. ?ei i i)"
              using i by metis
            also have "\<dots> = expectation (rind (A i))"
              by auto
            finally have "(\<Sum>j | j \<in> I \<and> i = j. ?ei i j) = \<dots>" .
          }
          hence "?lhs = (\<Sum>i\<in>I. expectation (rind (A i)))"
            by force
          also have "\<dots> = \<mu>"
            unfolding expectation_X_Y X_def ..
          finally show "?lhs = \<mu>" .
        qed
      moreover have "?rhs = \<Delta>\<^sub>a"
        proof -
          {
            fix i j
            assume "i \<in> I" "j \<in> I"
            with A have "A i \<inter> A j \<in> events" by blast
            hence "?ei i j = prob (A i \<inter> A j)"
              by (fact expectation_indicator)
          }
          thus ?thesis
            unfolding \<Delta>\<^sub>a_def by simp
        qed
      ultimately show "?lhs + ?rhs = \<mu> + \<Delta>\<^sub>a"
        by simp
    qed
  finally show ?thesis .
qed

lemma \<Delta>_expectation_X: "\<Delta>\<^sub>a \<le> \<mu>^2 + \<Delta>\<^sub>d"
proof -
  let ?p = "\<lambda>i j. prob (A i \<inter> A j)"
  let ?p' = "\<lambda>i j. prob (A i) * prob (A j)"
  let ?ie = "\<lambda>i j. indep (A i) (A j)"

  have "\<Delta>\<^sub>a = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> i \<noteq> j. if ?ie i j then ?p i j else ?p i j)"
    unfolding \<Delta>\<^sub>a_def by simp
  also have "\<dots> = (\<Sum>i \<in> I. (\<Sum>j | j \<in> I \<and> ineq_indep i j. ?p i j) + (\<Sum>j | j \<in> I \<and> ineq_dep i j. ?p i j))"
    by (simp only: sum_split2[OF finite_I])
  also have "\<dots> = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> ineq_indep i j. ?p i j) + \<Delta>\<^sub>d" (is "_ = ?lhs + _")
    unfolding \<Delta>\<^sub>d_def by (fact sum.distrib)
  also have "\<dots> \<le> \<mu>^2 + \<Delta>\<^sub>d"
    proof (rule add_right_mono)
      have "(\<Sum>i\<in>I. \<Sum>j | j \<in> I \<and> ineq_indep i j. ?p i j) = (\<Sum>i \<in> I. \<Sum>j | j \<in> I \<and> ineq_indep i j. ?p' i j)"
        unfolding indep_def by simp
      also have "\<dots> \<le> (\<Sum>i \<in> I. \<Sum>j \<in> I. ?p' i j)"
        proof (rule sum_mono)
          fix i
          assume "i \<in> I"
          show "(\<Sum>j | j \<in> I \<and> ineq_indep i j. ?p' i j) \<le> (\<Sum>j\<in>I. ?p' i j)"
            by (rule sum_upper[OF finite_I]) (simp add: zero_le_mult_iff)
        qed
      also have "\<dots> = (\<Sum>i \<in> I. prob (A i))^2"
        by (fact sum_square[symmetric])
      also have "\<dots> = (\<Sum>i \<in> I. expectation (X i))^2"
        unfolding X_def using expectation_indicator A by simp
      also have "\<dots> = \<mu>^2"
        using expectation_X_Y[symmetric] by simp
      finally show "?lhs \<le> \<mu>^2" .
    qed
  finally show ?thesis .
qed

lemma prob_\<mu>_\<Delta>\<^sub>a: "prob {a \<in> space M. Y a = 0} \<le> 1 / \<mu> + \<Delta>\<^sub>a / \<mu>^2 - 1"
proof -
  have "prob {a \<in> space M. Y a = 0} \<le> expectation (\<lambda>y. (Y y)^2) / \<mu>^2 - 1"
    unfolding \<mu>_def by (rule chebyshev_prob_zero) (simp add: \<mu>_def[symmetric])+
  also have "\<dots> = (\<mu> + \<Delta>\<^sub>a) / \<mu>^2 - 1"
    using expectation_Y_\<Delta> by simp
  also have "\<dots> = 1 / \<mu> + \<Delta>\<^sub>a / \<mu>^2 - 1"
    unfolding power2_eq_square by (simp add: field_simps add_divide_distrib)
  finally show ?thesis .
qed

lemma prob_\<mu>_\<Delta>\<^sub>d: "prob {a \<in> space M. Y a = 0} \<le> 1/\<mu> + \<Delta>\<^sub>d/\<mu>^2"
proof -
  have "prob {a \<in> space M. Y a = 0} \<le> 1/\<mu> + \<Delta>\<^sub>a/\<mu>^2 - 1"
    by (fact prob_\<mu>_\<Delta>\<^sub>a)
  also have "\<dots> = (1/\<mu> - 1) + \<Delta>\<^sub>a/\<mu>^2"
    by simp
  also have "\<dots> \<le> (1/\<mu> - 1) + (\<mu>^2 + \<Delta>\<^sub>d)/\<mu>^2"
    using divide_right_mono[OF \<Delta>_expectation_X] by simp
  also have "\<dots> = 1/\<mu> + \<Delta>\<^sub>d/\<mu>^2"
    using \<mu>_sq_non_zero by (simp add: field_simps)
  finally show ?thesis .
qed

end

end
