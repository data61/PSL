(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Ptolemy's Theorem\<close>

theory Ptolemys_Theorem
imports
  "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to Rat theory\<close>

hide_const (open) normalize

subsubsection \<open>Additions to Transcendental theory\<close>

text \<open>
Lemmas about @{const arcsin} and @{const arccos} commonly involve to show that their argument is
in the domain of those partial functions, i.e., the argument @{term y} is between @{term "-1::real"}
and @{term "1::real"}.
As the argumentation for @{term "(-1::real) \<le> y"} and @{term "y \<le> (1::real)"} is often very similar,
we prefer to prove @{term "\<bar>y\<bar> \<le> (1::real)"} to the two goals above.

The lemma for rewriting the term @{term "cos (arccos y)"} is already provided in the Isabelle
distribution with name @{thm [source] cos_arccos_abs}. Here, we further provide the analogue on
@{term "arcsin"} for rewriting @{term "sin (arcsin y)"}.
\<close>

lemma sin_arcsin_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> sin (arcsin y) = y"
  by (simp add: abs_le_iff)

text \<open>
The further lemmas are the required variants from existing lemmas @{thm [source] arccos_lbound}
and @{thm [source] arccos_ubound}.
\<close>

lemma arccos_lbound_abs [simp]:
  "\<bar>y\<bar> \<le> 1 \<Longrightarrow> 0 \<le> arccos y"
by (simp add: arccos_lbound)

lemma arccos_ubound_abs [simp]:
  "\<bar>y\<bar> \<le> 1 \<Longrightarrow> arccos y \<le> pi"
by (simp add: arccos_ubound)

text \<open>
As we choose angles to be between @{term "0::real"} between @{term "2 * pi"},
we need some lemmas to reason about the sign of @{term "sin x"}
for angles @{term "x"}.
\<close>

lemma sin_ge_zero_iff:
  assumes "0 \<le> x" "x < 2 * pi"
  shows "0 \<le> sin x \<longleftrightarrow> x \<le> pi"
proof
  assume "0 \<le> sin x"
  show "x \<le> pi"
  proof (rule ccontr)
    assume "\<not> x \<le> pi"
    from this \<open>x < 2 * pi\<close> have "sin x < 0"
      using sin_lt_zero by auto
    from this \<open>0 \<le> sin x\<close> show False by auto
  qed
next
  assume "x \<le> pi"
  from this \<open>0 \<le> x\<close> show "0 \<le> sin x" by (simp add: sin_ge_zero)
qed

lemma sin_less_zero_iff:
  assumes "0 \<le> x" "x < 2 * pi"
  shows "sin x < 0 \<longleftrightarrow> pi < x"
using assms sin_ge_zero_iff by fastforce

subsubsection \<open>Addition to Finite-Cartesian-Product theory\<close>

text \<open>
Here follow generally useful additions and specialised equations
for two-dimensional real-valued vectors.
\<close>

lemma axis_nth_eq_0 [simp]:
  assumes "i \<noteq> j"
  shows "axis i x $ j = 0"
using assms unfolding axis_def by simp

lemma norm_axis:
  fixes x :: real
  shows "norm (axis i x) = abs x"
by (simp add: norm_eq_sqrt_inner inner_axis_axis)

lemma norm_eq_on_real_2_vec:
  fixes x :: "real ^ 2"
  shows "norm x = sqrt ((x $ 1) ^ 2 + (x $ 2) ^ 2)"
by (simp add: norm_eq_sqrt_inner inner_vec_def UNIV_2 power2_eq_square)

lemma dist_eq_on_real_2_vec:
  fixes a b :: "real ^ 2"
  shows "dist a b = sqrt ((a $ 1 - b $ 1) ^ 2 + (a $ 2 - b $ 2) ^ 2)"
unfolding dist_norm norm_eq_on_real_2_vec by simp

subsection \<open>Polar Form of Two-Dimensional Real-Valued Vectors\<close>

subsubsection \<open>Definitions to Transfer to Polar Form and Back\<close>

definition of_radiant :: "real \<Rightarrow> real ^ 2"
where
  "of_radiant \<omega> = axis 1 (cos \<omega>) + axis 2 (sin \<omega>)"

definition normalize :: "real ^ 2 \<Rightarrow> real ^ 2"
where
  "normalize p = (if p = 0 then axis 1 1 else (1 / norm p) *\<^sub>R p)"

definition radiant_of :: "real ^ 2 \<Rightarrow> real"
where
  "radiant_of p = (THE \<omega>. 0 \<le> \<omega> \<and> \<omega> < 2 * pi \<and> of_radiant \<omega> = normalize p)"

text \<open>
The vector @{term "of_radiant \<omega>"} is the vector with length @{term "1::real"} and angle @{term "\<omega>"}
to the first axis.
We normalize vectors to length @{term "1::real"} keeping their orientation with the normalize function.
Conversely, @{term "radiant_of p"} is the angle of vector @{term p} to the first axis, where we
choose @{term "radiant_of"} to return angles between @{term "0::real"} and @{term "2 * pi"},
following the usual high-school convention.
With these definitions, we can express the main result
@{term "norm p *\<^sub>R of_radiant (radiant_of p) = p"}.
Note that the main result holds for any definition of @{term "radiant_of 0"}.
So, we choose to define @{term "normalize 0"} and @{term "radiant_of 0"}, such that
@{term "radiant_of 0 = 0"}.
\<close>

subsubsection \<open>Lemmas on @{const of_radiant}\<close>

lemma nth_of_radiant_1 [simp]:
  "of_radiant \<omega> $ 1 = cos \<omega>"
unfolding of_radiant_def by simp

lemma nth_of_radiant_2 [simp]:
  "of_radiant \<omega> $ 2 = sin \<omega>"
unfolding of_radiant_def by simp

lemma norm_of_radiant:
  "norm (of_radiant \<omega>) = 1"
unfolding of_radiant_def norm_eq_on_real_2_vec by simp

lemma of_radiant_plus_2pi:
  "of_radiant (\<omega> + 2 * pi) = of_radiant \<omega>"
unfolding of_radiant_def by simp

lemma of_radiant_minus_2pi:
  "of_radiant (\<omega> - 2 * pi) = of_radiant \<omega>"
proof -
  have "of_radiant (\<omega> - 2 * pi) = of_radiant (\<omega> - 2 * pi + 2 * pi)"
    by (simp only: of_radiant_plus_2pi)
  also have "\<dots> = of_radiant \<omega>" by simp
  finally show ?thesis .
qed

subsubsection \<open>Lemmas on @{const normalize}\<close>

lemma normalize_eq:
  "norm p *\<^sub>R normalize p = p"
unfolding normalize_def by simp

lemma norm_normalize:
  "norm (normalize p) = 1"
unfolding normalize_def by (auto simp add: norm_axis)

lemma nth_normalize [simp]:
  "\<bar>normalize p $ i\<bar> \<le> 1"
using norm_normalize component_le_norm_cart by metis

lemma normalize_square:
  "(normalize p $ 1)\<^sup>2 + (normalize p $ 2)\<^sup>2 = 1"
using dot_square_norm[of "normalize p"]
by (simp add: inner_vec_def UNIV_2 power2_eq_square norm_normalize)

lemma nth_normalize_ge_zero_iff:
  "0 \<le> normalize p $ i \<longleftrightarrow> 0 \<le> p $ i"
proof
  assume "0 \<le> normalize p $ i"
  from this show "0 \<le> p $ i"
    unfolding normalize_def by (auto split: if_split_asm simp add: zero_le_divide_iff)
next
  assume "0 \<le> p $ i"
  have "0 \<le> axis 1 (1 :: real) $ i"
    using exhaust_2[of i] by auto
  from this \<open>0 \<le> p $ i\<close> show "0 \<le> normalize p $ i"
    unfolding normalize_def by auto
qed

lemma nth_normalize_less_zero_iff:
  "normalize p $ i < 0 \<longleftrightarrow> p $ i < 0"
using nth_normalize_ge_zero_iff leD leI by metis

lemma normalize_boundary_iff:
  "\<bar>normalize p $ 1\<bar> = 1 \<longleftrightarrow> p $ 2 = 0"
proof
  assume "\<bar>normalize p $ 1\<bar> = 1"
  from this have 1: "(p $ 1) ^ 2 = norm p ^ 2"
    unfolding normalize_def by (auto split: if_split_asm simp add: power2_eq_iff)
  moreover have "(p $ 1) ^ 2 + (p $ 2) ^ 2 = norm p ^ 2"
    using norm_eq_on_real_2_vec by auto
  ultimately show "p $ 2 = 0" by simp
next
  assume "p $ 2 = 0"
  from this have "\<bar>p $ 1\<bar> = norm p"
    by (auto simp add: norm_eq_on_real_2_vec)
  from this show "\<bar>normalize p $ 1\<bar> = 1"
    unfolding normalize_def by simp
qed

lemma between_normalize_if_distant_from_0:
  assumes "norm p \<ge> 1"
  shows "between (0, p) (normalize p)"
using assms by (auto simp add: between_mem_segment closed_segment_def normalize_def)

lemma between_normalize_if_near_0:
  assumes "norm p \<le> 1"
  shows "between (0, normalize p) p"
proof -
  have "0 \<le> norm p" by simp
  from assms have "p = (norm p / norm p) *\<^sub>R p \<and> 0 \<le> norm p \<and> norm p \<le> 1" by auto
  from this have "\<exists>u. p = (u / norm p) *\<^sub>R p \<and> 0 \<le> u \<and> u \<le> 1" by blast
  from this show ?thesis
    by (auto simp add: between_mem_segment closed_segment_def normalize_def)
qed

subsubsection \<open>Lemmas on @{const radiant_of}\<close>

lemma radiant_of:
  "0 \<le> radiant_of p \<and> radiant_of p < 2 * pi \<and> of_radiant (radiant_of p) = normalize p"
proof -
  let ?a = "if 0 \<le> p $ 2 then arccos (normalize p $ 1) else pi + arccos (- (normalize p $ 1))"
  have "0 \<le> ?a \<and> ?a < 2 * pi \<and> of_radiant ?a = normalize p"
  proof -
    have "0 \<le> ?a" by auto
    moreover have "?a < 2 * pi"
    proof cases
      assume "0 \<le> p $ 2"
      from this have "?a \<le> pi" by simp
      from this show ?thesis
        using pi_gt_zero by linarith
    next
      assume "\<not> 0 \<le> p $ 2"
      have "arccos (- normalize p $ 1) < pi"
      proof -
        have "\<bar>normalize p $ 1\<bar> \<noteq> 1"
          using \<open>\<not> 0 \<le> p $ 2\<close> by (simp only: normalize_boundary_iff)
        from this have "arccos (- normalize p $ 1) \<noteq> pi"
          unfolding arccos_minus_1[symmetric] by (subst arccos_eq_iff) auto
        moreover have "arccos (- normalize p $ 1) \<le> pi" by simp
        ultimately show "arccos (- normalize p $ 1) < pi" by linarith
      qed
      from this \<open>\<not> 0 \<le> p $ 2\<close> show ?thesis by simp
    qed
    moreover have "of_radiant ?a = normalize p"
    proof -
      have "of_radiant ?a $ i = normalize p $ i" for i
      proof -
        have "of_radiant ?a $ 1 = normalize p $ 1"
          unfolding of_radiant_def by (simp add: cos_arccos_abs)
        moreover have "of_radiant ?a $ 2 = normalize p $ 2"
        proof cases
          assume "0 \<le> p $ 2"
          have "sin (arccos (normalize p $ 1)) = sqrt (1 - (normalize p $ 1) ^ 2)"
            by (simp add: sin_arccos_abs)
          also have "\<dots> = normalize p $ 2"
          proof -
            have "1 - (normalize p $ 1)\<^sup>2 = (normalize p $ 2)\<^sup>2"
              using normalize_square[of p] by auto
            from this \<open>0 \<le> p $ 2\<close> show ?thesis by (simp add: nth_normalize_ge_zero_iff)
          qed
          finally show ?thesis
            using \<open>0 \<le> p $ 2\<close> unfolding of_radiant_def by auto
        next
          assume "\<not> 0 \<le> p $ 2"
          have "- sin (arccos (- normalize p $ 1)) = - sqrt (1 - (normalize p $ 1)\<^sup>2)"
            by (simp add: sin_arccos_abs)
          also have "\<dots> = normalize p $ 2"
          proof -
            have "1 - (normalize p $ 1)\<^sup>2 = (normalize p $ 2)\<^sup>2"
              using normalize_square[of p] by auto
            from this \<open>\<not> 0 \<le> p $ 2\<close> show ?thesis
              using nth_normalize_ge_zero_iff by fastforce
          qed
          finally show ?thesis
            using \<open>\<not> 0 \<le> p $ 2\<close> unfolding of_radiant_def by auto
        qed
        ultimately show ?thesis by (metis exhaust_2[of i])
      qed
      from this show ?thesis by (simp add: vec_eq_iff)
    qed
    ultimately show ?thesis by blast
  qed
  moreover {
    fix \<omega>
    assume "0 \<le> \<omega> \<and> \<omega> < 2 * pi \<and> of_radiant \<omega> = normalize p"
    from this have "0 \<le> \<omega>" "\<omega> < 2 * pi" "normalize p = of_radiant \<omega>" by auto
    from this have "cos \<omega> = normalize p $ 1" "sin \<omega> = normalize p $ 2" by auto
    have "\<omega> = ?a"
    proof cases
      assume "0 \<le> p $ 2"
      from this have "\<omega> \<le> pi"
        using \<open>0 \<le> \<omega>\<close> \<open>\<omega> < 2 * pi\<close> \<open>sin \<omega> = normalize p $ 2\<close>
        by (simp add: sin_ge_zero_iff[symmetric] nth_normalize_ge_zero_iff)
      from \<open>0 \<le> \<omega>\<close> this have "\<omega> = arccos (cos \<omega>)" by (simp add: arccos_cos)
      from \<open>cos \<omega> = normalize p $ 1\<close> this have "\<omega> = arccos (normalize p $ 1)"
        by (simp add: arccos_eq_iff)
      from this show "\<omega> = ?a" using \<open>0 \<le> p $ 2\<close> by auto
    next
      assume "\<not> 0 \<le> p $ 2"
      from this have "\<omega> > pi"
        using \<open>0 \<le> \<omega>\<close> \<open>\<omega> < 2 * pi\<close> \<open>sin \<omega> = normalize p $ 2\<close>
        by (simp add: sin_less_zero_iff[symmetric] nth_normalize_less_zero_iff)
      from this \<open>\<omega> < 2 * pi\<close> have "\<omega> - pi = arccos (cos (\<omega> - pi))"
        by (auto simp only: arccos_cos)
      from this \<open>cos \<omega> = normalize p $ 1\<close> have "\<omega> - pi = arccos (- normalize p $ 1)" by simp
      from this have "\<omega> = pi + arccos (- normalize p $ 1)" by simp
      from this show "\<omega> = ?a" using \<open>\<not> 0 \<le> p $ 2\<close> by auto
    qed
  }
  ultimately show ?thesis
    unfolding radiant_of_def by (rule theI)
qed

lemma radiant_of_bounds [simp]:
  "0 \<le> radiant_of p" "radiant_of p < 2 * pi"
using radiant_of by auto

lemma radiant_of_weak_ubound [simp]:
  "radiant_of p \<le> 2 * pi"
using radiant_of_bounds(2)[of p] by linarith

subsubsection \<open>Main Equations for Transforming to Polar Form\<close>

lemma polar_form_eq:
  "norm p *\<^sub>R of_radiant (radiant_of p) = p"
using radiant_of normalize_eq by simp

lemma relative_polar_form_eq:
  "Q + dist P Q *\<^sub>R of_radiant (radiant_of (P - Q)) = P"
proof -
  have "norm (P - Q) *\<^sub>R of_radiant (radiant_of (P - Q)) = P - Q"
    unfolding polar_form_eq ..
  moreover have "dist P Q = norm (P - Q)" by (simp add: dist_norm)
  ultimately show ?thesis by (metis add.commute diff_add_cancel)
qed

subsection \<open>Ptolemy's Theorem\<close>

lemma dist_circle_segment:
  assumes "0 \<le> radius" "0 \<le> \<alpha>" "\<alpha> \<le> \<beta>" "\<beta> \<le> 2 * pi"
  shows "dist (center + radius *\<^sub>R of_radiant \<alpha>) (center + radius *\<^sub>R of_radiant \<beta>) = 2 * radius * sin ((\<beta> - \<alpha>) / 2)"
    (is "?lhs = ?rhs")
proof -
  have trigonometry: "(cos \<alpha> - cos \<beta>)\<^sup>2 + (sin \<alpha> - sin \<beta>)\<^sup>2 = (2 *  sin ((\<beta> - \<alpha>) / 2))\<^sup>2"
  proof -
    have sin_diff_minus: "sin ((\<alpha> - \<beta>) / 2) = - sin ((\<beta> - \<alpha>) / 2)"
      by (simp only: sin_minus[symmetric] minus_divide_left minus_diff_eq)
    have "(cos \<alpha> - cos \<beta>)\<^sup>2 + (sin \<alpha> - sin \<beta>)\<^sup>2 =
      (2 * sin ((\<alpha> + \<beta>) / 2) * sin ((\<beta> - \<alpha>) / 2))\<^sup>2 + (2 * sin ((\<alpha> - \<beta>) / 2) * cos ((\<alpha> + \<beta>) / 2))\<^sup>2"
      by (simp only: cos_diff_cos sin_diff_sin)
    also have "\<dots> = (2 * sin ((\<beta> - \<alpha>) / 2))\<^sup>2 * ((sin ((\<alpha> + \<beta>) / 2))\<^sup>2 + (cos ((\<alpha> + \<beta>) / 2))\<^sup>2)"
      unfolding sin_diff_minus by algebra
    also have "\<dots> = (2 *  sin ((\<beta> - \<alpha>) / 2))\<^sup>2" by simp
    finally show ?thesis .
  qed
  from assms have "0 \<le> sin ((\<beta> - \<alpha>) / 2)" by (simp add: sin_ge_zero)
  have "?lhs = sqrt (radius\<^sup>2 * ((cos \<alpha> - cos \<beta>)\<^sup>2 + (sin \<alpha> - sin \<beta>)\<^sup>2))"
    unfolding dist_eq_on_real_2_vec by simp algebra
  also have "\<dots> = sqrt (radius\<^sup>2 *  (2 * sin ((\<beta> - \<alpha>) / 2))\<^sup>2)" by (simp add: trigonometry)
  also have "\<dots> = ?rhs"
    using \<open>0 \<le> radius\<close> \<open>0 \<le> sin ((\<beta> - \<alpha>) / 2)\<close> by (simp add: real_sqrt_mult)
  finally show ?thesis .
qed

theorem ptolemy_trigonometric:
  fixes \<omega>\<^sub>1 \<omega>\<^sub>2 \<omega>\<^sub>3 :: real
  shows "sin (\<omega>\<^sub>1 + \<omega>\<^sub>2) * sin (\<omega>\<^sub>2 + \<omega>\<^sub>3) = sin \<omega>\<^sub>1 * sin \<omega>\<^sub>3 + sin \<omega>\<^sub>2 * sin (\<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3)"
proof -
  have "sin (\<omega>\<^sub>1 + \<omega>\<^sub>2) * sin (\<omega>\<^sub>2 + \<omega>\<^sub>3) = ((sin \<omega>\<^sub>2)\<^sup>2 + (cos \<omega>\<^sub>2)\<^sup>2) * sin \<omega>\<^sub>1 * sin \<omega>\<^sub>3 + sin \<omega>\<^sub>2 * sin (\<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3)"
    by (simp only: sin_add cos_add) algebra
  also have "\<dots> = sin \<omega>\<^sub>1 * sin \<omega>\<^sub>3 + sin \<omega>\<^sub>2 * sin (\<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3)" by simp
  finally show ?thesis .
qed

theorem ptolemy:
  fixes A B C D center :: "real ^ 2"
  assumes "dist center A = radius" and "dist center B = radius"
  assumes "dist center C = radius" and "dist center D = radius"
  assumes ordering_of_points:
    "radiant_of (A - center) \<le> radiant_of (B - center)"
    "radiant_of (B - center) \<le> radiant_of (C - center)"
    "radiant_of (C - center) \<le> radiant_of (D - center)"
  shows "dist A C * dist B D = dist A B * dist C D + dist A D * dist B C"
proof -
  from \<open>dist center A = radius\<close> have "0 \<le> radius" by auto
  define \<alpha> \<beta> \<gamma> \<delta>
    where "\<alpha> = radiant_of (A - center)" and "\<beta> = radiant_of (B - center)"
    and "\<gamma> = radiant_of (C - center)" and "\<delta> = radiant_of (D - center)"
  from ordering_of_points have angle_basics:
    "\<alpha> \<le> \<beta>" "\<beta> \<le> \<gamma>" "\<gamma> \<le> \<delta>"
    "0 \<le> \<alpha>" "\<alpha> \<le> 2 * pi" "0 \<le> \<beta>" "\<beta> \<le> 2 * pi"
    "0 \<le> \<gamma>" "\<gamma> \<le> 2 * pi" "0 \<le> \<delta>" "\<delta> \<le> 2 * pi"
    unfolding \<alpha>_def \<beta>_def \<gamma>_def \<delta>_def by auto
  from assms(1-4) have
    "A = center + radius *\<^sub>R of_radiant \<alpha>" "B = center + radius *\<^sub>R of_radiant \<beta>"
    "C = center + radius *\<^sub>R of_radiant \<gamma>" "D = center + radius *\<^sub>R of_radiant \<delta>"
    unfolding \<alpha>_def \<beta>_def \<gamma>_def \<delta>_def
    using relative_polar_form_eq dist_commute by metis+

  from this have dist_eqs:
    "dist A C = 2 * radius * sin ((\<gamma> - \<alpha>) / 2)"
    "dist B D = 2 * radius * sin ((\<delta> - \<beta>) / 2)"
    "dist A B = 2 * radius * sin ((\<beta> - \<alpha>) / 2)"
    "dist C D = 2 * radius * sin ((\<delta> - \<gamma>) / 2)"
    "dist A D = 2 * radius * sin ((\<delta> - \<alpha>) / 2)"
    "dist B C = 2 * radius * sin ((\<gamma> - \<beta>) / 2)"
    using angle_basics \<open>radius \<ge> 0\<close> dist_circle_segment by (auto)

  have "dist A C * dist B D = 4 * radius ^ 2 * sin ((\<gamma> - \<alpha>) / 2) * sin ((\<delta> - \<beta>) / 2)"
    unfolding dist_eqs by (simp add: power2_eq_square)
  also have "\<dots> = 4 * radius ^ 2 * (sin ((\<beta> - \<alpha>) / 2) * sin ((\<delta> - \<gamma>) / 2) + sin ((\<gamma> - \<beta>) / 2) * sin ((\<delta> - \<alpha>) / 2))"
  proof -
    define \<omega>\<^sub>1 \<omega>\<^sub>2 \<omega>\<^sub>3 where "\<omega>\<^sub>1 = (\<beta> - \<alpha>) / 2" and "\<omega>\<^sub>2 = (\<gamma> - \<beta>) / 2" and "\<omega>\<^sub>3 = (\<delta> - \<gamma>) / 2"
    have "(\<gamma> - \<alpha>) / 2 = \<omega>\<^sub>1 + \<omega>\<^sub>2" and "(\<delta> - \<beta>) / 2 = \<omega>\<^sub>2 + \<omega>\<^sub>3" and "(\<delta> - \<alpha>) / 2 = \<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3"
      unfolding \<omega>\<^sub>1_def \<omega>\<^sub>2_def \<omega>\<^sub>3_def by (auto simp add: field_simps)
    have "sin ((\<gamma> - \<alpha>) / 2) * sin ((\<delta> - \<beta>) / 2) = sin (\<omega>\<^sub>1 + \<omega>\<^sub>2) * sin (\<omega>\<^sub>2 + \<omega>\<^sub>3)"
      using \<open>(\<gamma> - \<alpha>) / 2 = \<omega>\<^sub>1 + \<omega>\<^sub>2\<close> \<open>(\<delta> - \<beta>) / 2 = \<omega>\<^sub>2 + \<omega>\<^sub>3\<close> by (simp only:)
    also have "\<dots> = sin \<omega>\<^sub>1 * sin \<omega>\<^sub>3 + sin \<omega>\<^sub>2 * sin (\<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3)"
      by (rule ptolemy_trigonometric)
    also have "\<dots> = (sin ((\<beta> - \<alpha>) / 2) * sin ((\<delta> - \<gamma>) / 2) + sin ((\<gamma> - \<beta>) / 2) * sin ((\<delta> - \<alpha>) / 2))"
      using \<omega>\<^sub>1_def \<omega>\<^sub>2_def \<omega>\<^sub>3_def \<open>(\<delta> - \<alpha>) / 2 = \<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3\<close> by (simp only:)
    finally show ?thesis by simp
  qed
  also have "\<dots> = dist A B * dist C D + dist A D * dist B C"
    unfolding dist_eqs by (simp add: distrib_left power2_eq_square)
  finally show ?thesis .
qed

end
