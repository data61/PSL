theory Utility_Functions
imports
  Complex_Main
  "HOL-Probability.Probability"
  Lotteries
  Preference_Profiles
begin

subsection \<open>Definition of von Neumann--Morgenstern utility functions\<close>

locale vnm_utility = finite_total_preorder_on +
  fixes u :: "'a \<Rightarrow> real"
  assumes utility_le_iff: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> u x \<le> u y \<longleftrightarrow> x \<preceq>[le] y"
begin

lemma utility_le: "x \<preceq>[le] y \<Longrightarrow> u x \<le> u y"
  using not_outside[of x y] utility_le_iff by simp

lemma utility_less_iff:
  "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> u x < u y \<longleftrightarrow> x \<prec>[le] y"
  using utility_le_iff[of x y] utility_le_iff[of y x]
  by (auto simp: strongly_preferred_def)

lemma utility_less: "x \<prec>[le] y \<Longrightarrow> u x < u y"
  using not_outside[of x y] utility_less_iff by (simp add: strongly_preferred_def)

text \<open>
  The following lemma allows us to compute the expected utility by summing
  over all indifference classes, using the fact that alternatives in the same
  indifference class must have the same utility.
\<close>
lemma expected_utility_weak_ranking:
  assumes "p \<in> lotteries_on carrier"
  shows   "measure_pmf.expectation p u =
             (\<Sum>A\<leftarrow>weak_ranking le. u (SOME x. x \<in> A) * measure_pmf.prob p A)"
proof -
  from assms have "measure_pmf.expectation p u = (\<Sum>a\<in>carrier. u a * pmf p a)"
    by (subst integral_measure_pmf[OF finite_carrier])
       (auto simp: lotteries_on_def ac_simps)
  also have carrier: "carrier = \<Union>(set (weak_ranking le))" by (simp add: weak_ranking_Union)
  also from carrier have finite: "finite A" if "A \<in> set (weak_ranking le)" for A
    using that by (blast intro!: finite_subset[OF _ finite_carrier, of A])
  hence "(\<Sum>a\<in>\<Union>(set (weak_ranking le)). u a * pmf p a) =
           (\<Sum>A\<leftarrow>weak_ranking le. \<Sum>a\<in>A. u a * pmf p a)" (is "_ = sum_list ?xs")
    using weak_ranking_total_preorder
    by (subst sum.Union_disjoint)
       (auto simp: is_weak_ranking_iff disjoint_def sum.distinct_set_conv_list)
  also have "?xs  = map (\<lambda>A. \<Sum>a\<in>A. u (SOME a. a\<in>A) * pmf p a) (weak_ranking le)"
  proof (intro map_cong HOL.refl sum.cong)
    fix x A assume x: "x \<in> A" and A: "A \<in> set (weak_ranking le)"
    have "(SOME x. x \<in> A) \<in> A" by (rule someI_ex) (insert x, blast)
    from weak_ranking_eqclass1[OF A x this] weak_ranking_eqclass1[OF A this x] x this A
      have "u x = u (SOME x. x \<in> A)"
      by (intro antisym; subst utility_le_iff) (auto simp: carrier)
    thus "u x * pmf p x = u (SOME x. x \<in> A) * pmf p x" by simp
  qed
  also have "\<dots> = map (\<lambda>A. u (SOME a. a \<in> A) * measure_pmf.prob p A) (weak_ranking le)"
    using finite by (intro map_cong HOL.refl)
                    (auto simp: sum_distrib_left measure_measure_pmf_finite)
  finally show ?thesis .
qed

lemma scaled: "c > 0 \<Longrightarrow> vnm_utility carrier le (\<lambda>x. c * u x)"
  by unfold_locales (insert utility_le_iff, auto)

lemma add_right:
  assumes "\<And>x y. le x y \<Longrightarrow> f x \<le> f y"
  shows   "vnm_utility carrier le (\<lambda>x. u x + f x)"
proof
  fix x y assume xy: "x \<in> carrier" "y \<in> carrier"
  from assms[of x y] utility_le_iff[OF xy] assms[of y x] utility_le_iff[OF xy(2,1)]
    show "(u x + f x \<le> u y + f y) = le x y" by auto
qed

lemma add_left:
  "(\<And>x y. le x y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> vnm_utility carrier le (\<lambda>x. f x + u x)"
  by (subst add.commute) (rule add_right)

text \<open>
  Given a consistent utility function, any function that assigns equal values to
  equivalent alternatives can be added to it (scaled with a sufficiently small @{term "\<epsilon>"}),
  again yielding a consistent utility function.
\<close>
lemma add_epsilon:
  assumes A: "\<And>x y. le x y \<Longrightarrow> le y x \<Longrightarrow> f x = f y"
  shows "\<exists>\<epsilon>>0. vnm_utility carrier le (\<lambda>x. u x + \<epsilon> * f x)"
proof -
  let ?A = "{(u y - u x) / (f x - f y) |x y. x \<prec>[le] y \<and> f x > f y}"
  have "?A = (\<lambda>(x,y). (u y - u x) / (f x - f y)) ` {(x,y) |x y. x \<prec>[le] y \<and> f x > f y}" by auto
  also have "finite {(x,y) |x y. x \<prec>[le] y \<and> f x > f y}"
    by (rule finite_subset[of _ "carrier \<times> carrier"])
       (insert not_outside, auto simp: strongly_preferred_def)
  hence "finite ((\<lambda>(x,y). (u y - u x) / (f x - f y)) ` {(x,y) |x y. x \<prec>[le] y \<and> f x > f y})"
    by simp
  finally have finite: "finite ?A" .

  define \<epsilon> where "\<epsilon> = Min (insert 1 ?A) / 2"
  from finite have "Min (insert 1 ?A) > 0"
    by (auto intro!: divide_pos_pos simp: utility_less)
  hence \<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def by simp

  have mono: "u x + \<epsilon> * f x < u y + \<epsilon> * f y" if xy: "x \<prec>[le] y" for x y
  proof (cases "f x > f y")
    assume less: "f x > f y"
    from \<epsilon> have "\<epsilon> < Min (insert 1 ?A)" unfolding \<epsilon>_def by linarith
    also from less xy finite have "Min (insert 1 ?A) \<le> (u y - u x) / (f x - f y)" unfolding \<epsilon>_def
      by (intro Min_le) auto
    finally show ?thesis using less by (simp add: field_simps)
  next
    assume "\<not>f x > f y"
    with utility_less[OF xy] \<epsilon> show ?thesis
      by (simp add: algebra_simps not_less add_less_le_mono)
  qed
  have eq: "u x + \<epsilon> * f x = u y + \<epsilon> * f y" if xy: "x \<preceq>[le] y" "y \<preceq>[le] x" for x y
    using xy[THEN utility_le] A[OF xy] by simp
  have "vnm_utility carrier le (\<lambda>x. u x + \<epsilon> * f x)"
  proof
    fix x y assume xy: "x \<in> carrier" "y \<in> carrier"
    show "(u x + \<epsilon> * f x \<le> u y + \<epsilon> * f y) \<longleftrightarrow> le x y"
      using total[OF xy] mono[of x y] mono[of y x] eq[of x y]
      by (cases "le x y"; cases "le y x") (auto simp: strongly_preferred_def)
  qed
  from \<epsilon> this show ?thesis by blast
qed

lemma diff_epsilon:
  assumes "\<And>x y. le x y \<Longrightarrow> le y x \<Longrightarrow> f x = f y"
  shows "\<exists>\<epsilon>>0. vnm_utility carrier le (\<lambda>x. u x - \<epsilon> * f x)"
proof -
  from assms have "\<exists>\<epsilon>>0. vnm_utility carrier le (\<lambda>x. u x + \<epsilon> * -f x)"
    by (intro add_epsilon) (subst neg_equal_iff_equal)
  thus ?thesis by simp
qed

end

end
