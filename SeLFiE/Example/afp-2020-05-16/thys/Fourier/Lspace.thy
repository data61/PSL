section\<open>Lspace as it is in HOL Light\<close>

text\<open>Mainly a repackaging of existing material from Lp\<close>

theory Lspace
  imports Lp.Lp 
begin

abbreviation lspace :: "'a measure \<Rightarrow> ennreal \<Rightarrow> ('a \<Rightarrow> real) set"
  where "lspace M p \<equiv> space\<^sub>N (\<LL> p M)"

lemma lspace_1:
  assumes "S \<in> sets lebesgue"
  shows "f \<in> lspace (lebesgue_on S) 1 \<longleftrightarrow> f absolutely_integrable_on S"
  using assms by (simp add: L1_space integrable_restrict_space set_integrable_def)

lemma lspace_ennreal_iff:
  assumes "p > 0"
  shows "lspace (lebesgue_on S) (ennreal p) = {f \<in> borel_measurable (lebesgue_on S). integrable (lebesgue_on S) (\<lambda>x. (norm(f x) powr p))}"
  using assms  by (fastforce simp: Lp_measurable Lp_D intro: Lp_I)

lemma lspace_iff:
  assumes "\<infinity> > p" "p > 0"
  shows "lspace (lebesgue_on S) p = {f \<in> borel_measurable (lebesgue_on S). integrable (lebesgue_on S) (\<lambda>x. (norm(f x) powr (enn2real p)))}"
proof -
  obtain q::real where "p = enn2real q"
    using Lp_cases assms by auto
  then show ?thesis
    using assms lspace_ennreal_iff by auto
qed

lemma lspace_iff':
  assumes p: "\<infinity> > p" "p > 0" and S: "S \<in> sets lebesgue"
  shows "lspace (lebesgue_on S) p = {f \<in> borel_measurable (lebesgue_on S). (\<lambda>x. (norm(f x) powr (enn2real p))) integrable_on S}"
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using assms integrable_on_lebesgue_on by (auto simp: lspace_iff)
next
  show "?rhs \<subseteq> ?lhs"
  proof (clarsimp simp: lspace_iff [OF p])
    show "integrable (lebesgue_on S) (\<lambda>xa. \<bar>f xa\<bar> powr enn2real p)"
      if "f \<in> borel_measurable (lebesgue_on S)" and "(\<lambda>x. \<bar>f x\<bar> powr enn2real p) integrable_on S" for f
    proof -
      have "(\<lambda>x. \<bar>f x\<bar> powr enn2real p) absolutely_integrable_on S"
        by (simp add: absolutely_integrable_on_iff_nonneg that(2))
      then show ?thesis
        using L1_space S lspace_1 by blast
    qed
  qed
qed

lemma lspace_mono:
  assumes "f \<in> lspace (lebesgue_on S) q" and S: "S \<in> lmeasurable" and "p > 0" "p \<le> q" "q < \<infinity>"
  shows "f \<in> lspace (lebesgue_on S) p"
proof -
  have "p < \<infinity>"
    using assms by (simp add: top.not_eq_extremum)
  with assms show ?thesis
  proof (clarsimp simp add: lspace_iff')
    show "(\<lambda>x. \<bar>f x\<bar> powr enn2real p) integrable_on S"
      if "f \<in> borel_measurable (lebesgue_on S)"
        and "(\<lambda>x. \<bar>f x\<bar> powr enn2real q) integrable_on S"
    proof (rule measurable_bounded_by_integrable_imp_integrable)
      show "(\<lambda>x. \<bar>f x\<bar> powr enn2real p) \<in> borel_measurable (lebesgue_on S)"
        using measurable_abs_powr that(1) by blast
      let ?g = "\<lambda>x. max 1 (norm(f x) powr enn2real q)"
      have "?g absolutely_integrable_on S"
      proof (rule absolutely_integrable_max_1)
        show "(\<lambda>x. norm (f x) powr enn2real q) absolutely_integrable_on S"
          by (simp add: nonnegative_absolutely_integrable_1 that(2))
      qed (simp add: S)
      then show "?g integrable_on S"
        using absolutely_integrable_abs_iff by blast
      show "norm (\<bar>f x\<bar> powr enn2real p) \<le> ?g x" if "x \<in> S" for x
      proof -
        have "\<bar>f x\<bar> powr enn2real p \<le> \<bar>f x\<bar> powr enn2real q" if "1 \<le> \<bar>f x\<bar>"
          using assms enn2real_mono powr_mono that by auto
        then show ?thesis
          using powr_le1 by (fastforce simp add: le_max_iff_disj)
      qed
      show "S \<in> sets lebesgue"
        by (simp add: S fmeasurableD)
    qed
  qed
qed

lemma lspace_inclusion:
  assumes "S \<in> lmeasurable" and "p > 0" "p \<le> q" "q < \<infinity>"
  shows "lspace (lebesgue_on S) q \<subseteq> lspace (lebesgue_on S) p"
  using assms lspace_mono by auto

lemma lspace_const:
  fixes p::real
  assumes "p > 0""S \<in> lmeasurable"
  shows "(\<lambda>x. c) \<in> lspace (lebesgue_on S) p"
  by (simp add: Lp_space assms finite_measure.integrable_const finite_measure_lebesgue_on)

lemma lspace_max:
  fixes p::real
  assumes "f \<in> lspace (lebesgue_on S) p" "g \<in> lspace (lebesgue_on S) p" "p > 0"
  shows "(\<lambda>x. max (f x) (g x)) \<in> lspace (lebesgue_on S) p"
proof -
  have "integrable (lebesgue_on S) (\<lambda>x. \<bar>max (f x) (g x)\<bar> powr p)"
    if f: "f \<in> borel_measurable (lebesgue_on S)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
      and g: "g \<in> borel_measurable (lebesgue_on S)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>g x\<bar> powr p)"
  proof -
    have "integrable (lebesgue_on S) (\<lambda>x. \<bar>\<bar>f x\<bar> powr p\<bar>)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>\<bar>g x\<bar> powr p\<bar>)"
      using integrable_abs that by blast+
    then have "integrable (lebesgue_on S) (\<lambda>x. max (\<bar>\<bar>f x\<bar> powr p\<bar>) (\<bar>\<bar>g x\<bar> powr p\<bar>))"
      using integrable_max by blast
    then show ?thesis
    proof (rule Bochner_Integration.integrable_bound)
      show "(\<lambda>x. \<bar>max (f x) (g x)\<bar> powr p) \<in> borel_measurable (lebesgue_on S)"
        using borel_measurable_max measurable_abs_powr that by blast
    qed auto
  qed
  then show ?thesis
    using assms by (auto simp: Lp_space borel_measurable_max)
qed

lemma lspace_min:
  fixes p::real
  assumes "f \<in> lspace (lebesgue_on S) p" "g \<in> lspace (lebesgue_on S) p" "p > 0"
  shows "(\<lambda>x. min (f x) (g x)) \<in> lspace (lebesgue_on S) p"
proof -
  have "integrable (lebesgue_on S) (\<lambda>x. \<bar>min (f x) (g x)\<bar> powr p)"
    if f: "f \<in> borel_measurable (lebesgue_on S)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar> powr p)"
      and g: "g \<in> borel_measurable (lebesgue_on S)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>g x\<bar> powr p)"
  proof -
    have "integrable (lebesgue_on S) (\<lambda>x. \<bar>\<bar>f x\<bar> powr p\<bar>)" "integrable (lebesgue_on S) (\<lambda>x. \<bar>\<bar>g x\<bar> powr p\<bar>)"
      using integrable_abs that by blast+
    then have "integrable (lebesgue_on S) (\<lambda>x. max (\<bar>\<bar>f x\<bar> powr p\<bar>) (\<bar>\<bar>g x\<bar> powr p\<bar>))"
      using integrable_max by blast
    then show ?thesis
    proof (rule Bochner_Integration.integrable_bound)
      show "(\<lambda>x. \<bar>min (f x) (g x)\<bar> powr p) \<in> borel_measurable (lebesgue_on S)"
        using borel_measurable_min measurable_abs_powr that by blast
    qed auto
  qed
  then show ?thesis
    using assms by (auto simp: Lp_space borel_measurable_min)
qed

lemma Lp_space_numeral:
  assumes "numeral n > (0::int)"
  shows "space\<^sub>N (\<LL> (numeral n) M) = {f \<in> borel_measurable M. integrable M (\<lambda>x. \<bar>f x\<bar> ^ numeral n)}"
  using Lp_space [of "numeral n" M] assms by simp

end
