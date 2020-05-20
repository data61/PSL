(* ---------------------------------------------------------------------------- *)
section \<open>Introduction\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>The complex plane or some of its parts (e.g., the unit disc or the upper half plane) are often
taken as the domain in which models of various geometries (both Euclidean and non-Euclidean ones)
are formalized. The complex plane gives simpler and more compact formulas than the Cartesian plane.
Within complex plane is easier to describe geometric objects and perform the calculations (usually
shedding some new light on the subject). We give a formalization of the extended complex
plane (given both as a complex projective space and as the Riemann sphere), its objects (points,
circles and lines), and its transformations (Möbius transformations).\<close>

(* ---------------------------------------------------------------------------- *)
section \<open>Related work\<close>
(* ---------------------------------------------------------------------------- *)

text\<open>During the last decade, there have been many results in formalizing
geometry in proof-assistants. Parts of Hilbert’s seminal book
,,Foundations of Geometry'' \cite{hilbert} have been formalized both
in Coq and Isabelle/Isar.  Formalization of first two groups of axioms
in Coq, in an intuitionistic setting was done by Dehlinger et
al. \cite{hilbert-coq}. First formalization in Isabelle/HOL was done
by Fleuriot and Meikele \cite{hilbert-isabelle}, and some further
developments were made in master thesis of Scott \cite{hilbert-scott}.
Large fragments of Tarski's geometry \cite{tarski} have been
formalized in Coq by Narboux et al. \cite{narboux-tarski}. Within Coq,
there are also formalizations of von Plato’s constructive geometry by
Kahn \cite{vonPlato,von-plato-formalization}, French high school
geometry by Guilhot \cite{guilhot} and ruler and compass geometry by
Duprat \cite{duprat2008}, etc.

In our previous work \cite{petrovic2012formalizing}, we have already
formally investigated a Cartesian model of Euclidean geometry. 
\<close>

(* ---------------------------------------------------------------------------- *)
section \<open>Background theories\<close> 
(* ---------------------------------------------------------------------------- *)

text \<open>In this section we introduce some basic mathematical notions and prove some lemmas needed in the rest of our
formalization. We describe:

    \<^item> trigonometric functions,

    \<^item> complex numbers, 

    \<^item> systems of two and three linear equations with two unknowns (over arbitrary fields), 

    \<^item> quadratic equations (over real and complex numbers), systems of quadratic and real
      equations, and systems of two quadratic equations,

    \<^item> two-dimensional vectors and matrices over complex numbers.
\<close>

(* -------------------------------------------------------------------------- *)
subsection \<open>Library Additions for Trigonometric Functions\<close>
(* -------------------------------------------------------------------------- *)

theory More_Transcendental
  imports Complex_Main
begin

text \<open>Additional properties of @{term sin} and @{term cos} functions that are later used in proving
conjectures for argument of complex number.\<close>

text \<open>Sign of trigonometric functions on some characteristic intervals.\<close>

lemma cos_lt_zero_on_pi2_pi [simp]:
  assumes "x > pi/2" and "x \<le> pi"
  shows "cos x < 0"
  using cos_gt_zero_pi[of "pi - x"] assms
  by simp

text \<open>Value of trigonometric functions in points $k\pi$ and $\frac{\pi}{2} + k\pi$.\<close>

lemma sin_kpi [simp]:
  fixes k::int
  shows "sin (k * pi) = 0"
  by (simp add: sin_zero_iff_int2)

lemma cos_odd_kpi [simp]:
  fixes k::int
  assumes "odd k"
  shows "cos (k * pi) = -1"
proof (cases "k \<ge> 0")
  case True
  hence "odd (nat k)"
    using  \<open>odd k\<close>
    by (auto simp add: even_nat_iff)
  thus ?thesis
    using \<open>k \<ge> 0\<close> cos_npi[of "nat k"]
    by auto
next
  case False
  hence "-k \<ge> 0" "odd (nat (-k))"
    using \<open>odd k\<close>
    by (auto simp add: even_nat_iff)
  thus ?thesis
    using cos_npi[of "nat (-k)"]
    by auto
qed

lemma cos_even_kpi [simp]:
  fixes k::int
  assumes "even k"
  shows "cos (k * pi) = 1"
proof (cases "k \<ge> 0")
  case True
  hence "even (nat k)"
    using  \<open>even k\<close>
    by (simp add: even_nat_iff)
  thus ?thesis
    using \<open>k \<ge> 0\<close> cos_npi[of "nat k"]
    by auto
next
  case False
  hence "-k \<ge> 0" "even (nat (-k))"
    using \<open>even k\<close>
    by (auto simp add: even_nat_iff)
  thus ?thesis
    using  cos_npi[of "nat (-k)"]
    by auto
qed

lemma sin_pi2_plus_odd_kpi [simp]:
  fixes k::int
  assumes "odd k"
  shows "sin (pi / 2 + k * pi) = -1"
  using assms
  by (simp add: sin_add)

lemma sin_pi2_plus_even_kpi [simp]:
  fixes k::int
  assumes "even k"
  shows "sin (pi / 2 + k * pi) = 1"
  using assms
  by (simp add: sin_add)

text \<open>Solving trigonometric equations and systems with special values (0, 1, or -1) of sine and cosine functions\<close>

lemma cos_0_iff_canon:
  assumes "cos \<phi> = 0" and "-pi < \<phi>" and "\<phi> \<le> pi"
  shows "\<phi> = pi/2 \<or> \<phi> = -pi/2"
proof-
  obtain k::int where "odd k" "\<phi> = k * pi/2"
    using cos_zero_iff_int[of \<phi>] assms(1)
    by auto
  thus ?thesis
  proof (cases "k > 1 \<or> k < -1")
    case True
    hence "k \<ge> 3 \<or> k \<le> -3"
      using \<open>odd k\<close>
      by (smt dvd_refl even_minus)
    hence "\<phi> \<ge> 3*pi/2 \<or> \<phi> \<le> -3*pi/2"
      using mult_right_mono[of k "-3" "pi / 2"]
      using \<open>\<phi> = k * pi/2\<close>
      by auto
    thus ?thesis
      using \<open>- pi < \<phi>\<close> \<open>\<phi> \<le> pi\<close>
      by auto
  next
    case False
    hence "k = -1 \<or> k = 0 \<or> k = 1"
      by auto
    hence "k = -1 \<or> k = 1"
      using \<open>odd k\<close>
      by auto
    thus ?thesis
      using \<open>\<phi> = k * pi/2\<close>
      by auto
  qed
qed

lemma sin_0_iff_canon:
  assumes "sin \<phi> = 0" and "-pi < \<phi>" and "\<phi> \<le> pi"
  shows "\<phi> = 0 \<or> \<phi> = pi"
proof-
  obtain k::int where "even k" "\<phi> = k * pi/2"
    using sin_zero_iff_int[of \<phi>] assms(1)
    by auto
  thus ?thesis
  proof (cases "k > 2 \<or> k < 0")
    case True
    hence "k \<ge> 4 \<or> k \<le> -2"
      using \<open>even k\<close>
      by (smt evenE)
    hence "\<phi> \<ge> 2*pi \<or> \<phi> \<le> -pi"
    proof
      assume "4 \<le> k"
      hence "4 * pi/2 \<le> \<phi>"
        using mult_right_mono[of "4" "k" "pi/2"]
        by (subst \<open>\<phi> = k * pi/2\<close>) auto
      thus ?thesis
        by simp
    next
      assume "k \<le> -2"
      hence "-2*pi/2 \<ge> \<phi>"
        using mult_right_mono[of "k" "-2" "pi/2"]
        by (subst \<open>\<phi> = k * pi/2\<close>, auto)
      thus ?thesis
        by simp
    qed
    thus ?thesis
      using \<open>- pi < \<phi>\<close> \<open>\<phi> \<le> pi\<close>
      by auto
  next
    case False
    hence "k = 0 \<or> k = 1 \<or> k = 2"
      by auto
    hence "k = 0 \<or> k = 2"
      using \<open>even k\<close>
      by auto
    thus ?thesis
      using \<open>\<phi> = k * pi/2\<close>
      by auto
  qed
qed

lemma cos0_sin1:
  assumes "cos \<phi> = 0" and "sin \<phi> = 1"
  shows "\<exists> k::int. \<phi> = pi/2 + 2*k*pi"
proof-
  from \<open>cos \<phi> = 0\<close>
  obtain k::int where "odd k" "\<phi> = k * (pi / 2)"
    using cos_zero_iff_int[of "\<phi>"]
    by auto
  then obtain k'::int where "k = 2*k' + 1"
    using oddE by blast
  hence "\<phi> = pi/2 + (k' * pi)"
    using \<open>\<phi> = k * (pi / 2)\<close>
    by (auto simp add: field_simps)
  hence "even k'"
    using \<open>sin \<phi> = 1\<close> sin_pi2_plus_odd_kpi[of k']
    by auto
  thus ?thesis
    using \<open>\<phi> = pi /2 + (k' * pi)\<close>
    unfolding even_iff_mod_2_eq_zero
    by auto
qed

lemma cos1_sin0:
  assumes "cos \<phi> = 1" and "sin \<phi> = 0"
  shows "\<exists> k::int. \<phi> = 2*k*pi"
proof-
  from \<open>sin \<phi> = 0\<close>
  obtain k::int where "even k" "\<phi> = k * (pi / 2)"
    using sin_zero_iff_int[of "\<phi>"]
    by auto
  then obtain k'::int where "k = 2*k'"
    using evenE by blast
  hence "\<phi> = k' * pi"
    using \<open>\<phi> = k * (pi / 2)\<close>
    by (auto simp add: field_simps)
  hence "even k'"
    using \<open>cos \<phi> = 1\<close> cos_odd_kpi[of k']
    by auto
  thus ?thesis
    using \<open>\<phi> = k' * pi\<close>
    using assms(1) cos_one_2pi_int by auto
qed

(* TODO: add lemmas for cos = -1, sin = 0 and cos = 0, sin = -1 *)


text \<open>Sine is injective on $[-\frac{\pi}{2}, \frac{\pi}{2}]$\<close>

lemma sin_inj:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2" and "-pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2"
  assumes "\<alpha> \<noteq> \<alpha>'"
  shows "sin \<alpha> \<noteq> sin \<alpha>'"
  using assms
  using sin_monotone_2pi[of \<alpha> \<alpha>'] sin_monotone_2pi[of \<alpha>' \<alpha>]
  by (cases "\<alpha> < \<alpha>'") auto

text \<open>Periodicity of trigonometric functions\<close>

text \<open>The following are available in HOL-Decision\_Procs.Approximation\_Bounds, but we want to avoid
that dependency\<close>

lemma sin_periodic_nat [simp]: 
  fixes n :: nat
  shows "sin (x + n * (2 * pi)) = sin x"
proof (induct n arbitrary: x)
  case (Suc n)
  have split_pi_off: "x + (Suc n) * (2 * pi) = (x + n * (2 * pi)) + 2 * pi"
    unfolding Suc_eq_plus1  distrib_right
    by (auto simp add: field_simps)
  show ?case unfolding split_pi_off using Suc by auto
qed auto

lemma sin_periodic_int [simp]:
  fixes i :: int
  shows "sin (x + i * (2 * pi)) = sin x"
proof(cases "0 \<le> i")
  case True
  thus ?thesis
    using sin_periodic_nat[of x "nat i"]
    by auto
next
  case False hence i_nat: "i = - real (nat (-i))" by auto
  have "sin x = sin (x + i * (2 * pi) - i * (2 * pi))" by auto
  also have "\<dots> = sin (x + i * (2 * pi))"
    unfolding i_nat mult_minus_left diff_minus_eq_add by (rule sin_periodic_nat)
  finally show ?thesis by auto
qed

lemma cos_periodic_nat [simp]: 
  fixes n :: nat
  shows "cos (x + n * (2 * pi)) = cos x"
proof (induct n arbitrary: x)
  case (Suc n)
  have split_pi_off: "x + (Suc n) * (2 * pi) = (x + n * (2 * pi)) + 2 * pi"
    unfolding Suc_eq_plus1  distrib_right
    by (auto simp add: field_simps)
  show ?case unfolding split_pi_off using Suc by auto
qed auto

lemma cos_periodic_int [simp]:
  fixes i :: int
  shows "cos (x + i * (2 * pi)) = cos x"
proof(cases "0 \<le> i")
  case True
  thus ?thesis
    using cos_periodic_nat[of x "nat i"]
    by auto
next
  case False hence i_nat: "i = - real (nat (-i))" by auto
  have "cos x = cos (x + i * (2 * pi) - i * (2 * pi))" by auto
  also have "\<dots> = cos (x + i * (2 * pi))"
    unfolding i_nat mult_minus_left diff_minus_eq_add by (rule cos_periodic_nat)
  finally show ?thesis by auto
qed

text \<open>Values of both sine and cosine are repeated only after multiples of $2\cdot \pi$\<close>

lemma sin_cos_eq:
  fixes a b :: real
  assumes "cos a = cos b" and "sin a = sin b"
  shows "\<exists> k::int. a - b = 2*k*pi"
proof-
  from assms have "sin (a - b) = 0" "cos (a - b) = 1"
    using sin_diff[of a b] cos_diff[of a b]
    by auto
  thus ?thesis
    using cos1_sin0
    by auto
qed

text \<open>The following two lemmas are consequences of surjectivity of cosine for the range $[-1, 1]$.\<close>

lemma ex_cos_eq:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2"
  assumes "a \<ge> 0" and "a < 1"
  shows "\<exists> \<alpha>'. -pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2 \<and> \<alpha>' \<noteq> \<alpha> \<and> cos (\<alpha> - \<alpha>') = a"
proof-
  have "arccos a > 0" "arccos a \<le> pi/2"
    using \<open>a \<ge> 0\<close> \<open>a < 1\<close>
    using arccos_lt_bounded arccos_le_pi2
    by auto

  show ?thesis
  proof (cases "\<alpha> - arccos a \<ge> - pi/2")
    case True
    thus ?thesis
      using assms \<open>arccos a > 0\<close> \<open>arccos a \<le> pi/2\<close>
      by (rule_tac x = "\<alpha> - arccos a" in exI) auto
  next
    case False
    thus ?thesis
      using assms \<open>arccos a > 0\<close> \<open>arccos a \<le> pi/2\<close>
      by (rule_tac x = "\<alpha> + arccos a" in exI) auto
  qed
qed

lemma ex_cos_gt:
  assumes "-pi/2 \<le> \<alpha> \<and> \<alpha> \<le> pi/2"
  assumes "a < 1"
  shows "\<exists> \<alpha>'. -pi/2 \<le> \<alpha>' \<and> \<alpha>' \<le> pi/2 \<and> \<alpha>' \<noteq> \<alpha> \<and> cos (\<alpha> - \<alpha>') > a"
proof-
  have "\<exists> a'. a' \<ge> 0 \<and> a' > a \<and> a' < 1"
    using \<open>a < 1\<close>
    using divide_strict_right_mono[of "2*a + (1 - a)" 2 2]
    by (rule_tac x="if a < 0 then 0 else a + (1-a)/2" in exI) (auto simp add: field_simps)
  then obtain a' where "a' \<ge> 0" "a' > a" "a' < 1"
    by auto
  thus ?thesis
    using ex_cos_eq[of \<alpha> a'] assms
    by auto
qed

text \<open>The function @{term atan2} is a generalization of @{term arctan} that takes a pair of coordinates
of non-zero points returns its angle in the range $[-\pi, \pi)$.\<close>

definition atan2 where
  "atan2 y x =
    (if x > 0 then arctan (y/x)
     else if x < 0 then
          if y > 0 then arctan (y/x) + pi else arctan (y/x) - pi
     else
          if y > 0 then pi/2 else if y < 0 then -pi/2 else 0)"

lemma atan2_bounded: 
  shows "-pi \<le> atan2 y x \<and> atan2 y x < pi"
  using arctan_bounded[of "y/x"] zero_le_arctan_iff[of "y/x"] arctan_le_zero_iff[of "y/x"] zero_less_arctan_iff[of "y/x"] arctan_less_zero_iff[of "y/x"]
  using divide_neg_neg[of y x] divide_neg_pos[of y x] divide_pos_pos[of y x]  divide_pos_neg[of y x]
  unfolding atan2_def
  by (simp (no_asm_simp)) auto

end
