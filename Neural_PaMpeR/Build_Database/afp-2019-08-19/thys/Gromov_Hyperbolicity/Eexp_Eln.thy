(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>The exponential on extended real numbers.\<close>

theory Eexp_Eln
  imports Library_Complements
begin

text \<open>To define the distance on the Gromov completion of hyperbolic spaces, we need to use
the exponential on extended real numbers. We can not use the symbol \verb+exp+, as this symbol
is already used in Banach algebras, so we use \verb+ennexp+ instead. We prove its basic
properties (together with properties of the logarithm) here. We also use it to define the square
root on ennreal. Finally, we also define versions from ereal to ereal.\<close>

function ennexp::"ereal \<Rightarrow> ennreal" where
"ennexp (ereal r) = ennreal (exp r)"
| "ennexp (\<infinity>) = \<infinity>"
| "ennexp (-\<infinity>) = 0"
by (auto intro: ereal_cases)
termination by standard (rule wf_empty)

lemma ennexp_0 [simp]:
  "ennexp 0 = 1"
by (auto simp add: zero_ereal_def one_ennreal_def)

function eln::"ennreal \<Rightarrow> ereal" where
"eln (ennreal r) = (if r \<le> 0 then -\<infinity> else ereal (ln r))"
| "eln (\<infinity>) = \<infinity>"
by (auto intro: ennreal_cases, metis ennreal_eq_0_iff, simp add: ennreal_neg)
termination by standard (rule wf_empty)

lemma eln_simps [simp]:
  "eln 0 = -\<infinity>"
  "eln 1 = 0"
  "eln top = \<infinity>"
apply (simp only: eln.simps ennreal_0[symmetric], simp)
apply (simp only: eln.simps ennreal_1[symmetric], simp)
using eln.simps(2) by auto

lemma eln_real_pos:
  assumes "r > 0"
  shows "eln (ennreal r) = ereal (ln r)"
using eln.simps assms by auto

lemma eln_ennexp [simp]:
  "eln (ennexp x) = x"
apply (cases x) using eln.simps by auto

lemma ennexp_eln [simp]:
  "ennexp (eln x) = x"
apply (cases x) using eln.simps by auto

lemma ennexp_strict_mono:
  "strict_mono ennexp"
proof -
  have "ennexp x < ennexp y" if "x < y" for x y
    apply (cases x, cases y)
    using that apply (auto simp add: ennreal_less_iff)
    by (cases y, auto)
  then show ?thesis unfolding strict_mono_def by auto
qed

lemma ennexp_mono:
  "mono ennexp"
using ennexp_strict_mono by (simp add: strict_mono_mono)

lemma ennexp_strict_mono2 [mono_intros]:
  assumes "x < y"
  shows "ennexp x < ennexp y"
using ennexp_strict_mono assms unfolding strict_mono_def by auto

lemma ennexp_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "ennexp x \<le> ennexp y"
using ennexp_mono assms unfolding mono_def by auto

lemma ennexp_le1 [simp]:
  "ennexp x \<le> 1 \<longleftrightarrow> x \<le> 0"
by (metis ennexp_0 ennexp_mono2 ennexp_strict_mono eq_iff le_cases strict_mono_eq)

lemma ennexp_ge1 [simp]:
  "ennexp x \<ge> 1 \<longleftrightarrow> x \<ge> 0"
by (metis ennexp_0 ennexp_mono2 ennexp_strict_mono eq_iff le_cases strict_mono_eq)

lemma eln_strict_mono:
  "strict_mono eln"
by (metis ennexp_eln strict_monoI ennexp_strict_mono strict_mono_less)

lemma eln_mono:
  "mono eln"
using eln_strict_mono by (simp add: strict_mono_mono)

lemma eln_strict_mono2 [mono_intros]:
  assumes "x < y"
  shows "eln x < eln y"
using eln_strict_mono assms unfolding strict_mono_def by auto

lemma eln_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "eln x \<le> eln y"
using eln_mono assms unfolding mono_def by auto

lemma eln_le0 [simp]:
  "eln x \<le> 0 \<longleftrightarrow> x \<le> 1"
by (metis ennexp_eln ennexp_le1)

lemma eln_ge0 [simp]:
  "eln x \<ge> 0 \<longleftrightarrow> x \<ge> 1"
by (metis ennexp_eln ennexp_ge1)

lemma bij_ennexp:
  "bij ennexp"
by (auto intro!: bij_betw_byWitness[of _ eln])

lemma bij_eln:
  "bij eln"
by (auto intro!: bij_betw_byWitness[of _ ennexp])

lemma ennexp_continuous:
  "continuous_on UNIV ennexp"
apply (rule continuous_onI_mono)
using ennexp_mono unfolding mono_def by (auto simp add: bij_ennexp bij_is_surj)

lemma ennexp_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. ennexp(u n)) \<longlongrightarrow> ennexp l) F"
using ennexp_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma eln_continuous:
  "continuous_on UNIV eln"
apply (rule continuous_onI_mono)
using eln_mono unfolding mono_def by (auto simp add: bij_eln bij_is_surj)

lemma eln_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. eln(u n)) \<longlongrightarrow> eln l) F"
using eln_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma ennexp_special_values [simp]:
  "ennexp x = 0 \<longleftrightarrow> x = -\<infinity>"
  "ennexp x = 1 \<longleftrightarrow> x = 0"
  "ennexp x = \<infinity> \<longleftrightarrow> x = \<infinity>"
  "ennexp x = top \<longleftrightarrow> x = \<infinity>"
by auto (metis eln_ennexp eln_simps)+

lemma eln_special_values [simp]:
  "eln x = -\<infinity> \<longleftrightarrow> x = 0"
  "eln x = 0 \<longleftrightarrow> x = 1"
  "eln x = \<infinity> \<longleftrightarrow> x = \<infinity>"
apply auto
apply (metis ennexp.simps ennexp_eln ennexp_0)+
by (metis ennexp.simps(2) ennexp_eln infinity_ennreal_def)

lemma ennexp_add_mult:
  assumes "\<not>((a = \<infinity> \<and> b = -\<infinity>) \<or> (a = -\<infinity> \<and> b = \<infinity>))"
  shows "ennexp(a+b) = ennexp a * ennexp b"
apply (cases a, cases b)
using assms by (auto simp add: ennreal_mult'' exp_add ennreal_top_eq_mult_iff)

lemma eln_mult_add:
  assumes "\<not>((a = \<infinity> \<and> b = 0) \<or> (a = 0 \<and> b = \<infinity>))"
  shows "eln(a * b) = eln a + eln b"
by (smt assms ennexp.simps(2) ennexp.simps(3) ennexp_add_mult ennexp_eln eln_ennexp)

text \<open>We can also define the square root on ennreal using the above exponential.\<close>

definition ennsqrt::"ennreal \<Rightarrow> ennreal"
  where "ennsqrt x = ennexp(eln x/2)"

lemma ennsqrt_square [simp]:
  "(ennsqrt x) * (ennsqrt x) = x"
proof -
  have "y/2 + y/2 = y" for y::ereal
    by (cases y, auto)
  then show ?thesis
    unfolding ennsqrt_def by (subst ennexp_add_mult[symmetric], auto)
qed

lemma ennsqrt_simps [simp]:
  "ennsqrt 0 = 0"
  "ennsqrt 1 = 1"
  "ennsqrt \<infinity> = \<infinity>"
  "ennsqrt top = top"
unfolding ennsqrt_def by auto

lemma ennsqrt_mult:
  "ennsqrt(a * b) = ennsqrt a * ennsqrt b"
proof -
  have [simp]: "z/ereal 2 = -\<infinity> \<longleftrightarrow> z = -\<infinity>" for z
    by (auto simp add: ereal_divide_eq)

  consider "a = 0" | "b = 0" | "a > 0 \<and> b > 0"
    using zero_less_iff_neq_zero by auto
  then show ?thesis
    apply (cases, auto)
    apply (cases a, cases b, auto simp add: ennreal_mult_top ennreal_top_mult)
    unfolding ennsqrt_def apply (subst ennexp_add_mult[symmetric], auto)
    apply (subst eln_mult_add, auto)
    done
qed

lemma ennsqrt_square2 [simp]:
  "ennsqrt (x * x) = x"
  unfolding ennsqrt_mult by auto

lemma ennsqrt_eq_iff_square:
  "ennsqrt x = y \<longleftrightarrow> x = y * y"
by auto

lemma ennsqrt_bij:
  "bij ennsqrt"
by (rule bij_betw_byWitness[of _ "\<lambda>x. x * x"], auto)

lemma ennsqrt_strict_mono:
  "strict_mono ennsqrt"
  unfolding ennsqrt_def
  apply (rule strict_mono_compose[OF ennexp_strict_mono])
  apply (rule strict_mono_compose[OF _ eln_strict_mono])
  by (auto simp add: ereal_less_divide_pos ereal_mult_divide strict_mono_def)

lemma ennsqrt_mono:
  "mono ennsqrt"
using ennsqrt_strict_mono by (simp add: strict_mono_mono)

lemma ennsqrt_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "ennsqrt x \<le> ennsqrt y"
using ennsqrt_mono assms unfolding mono_def by auto

lemma ennsqrt_continuous:
  "continuous_on UNIV ennsqrt"
apply (rule continuous_onI_mono)
using ennsqrt_mono unfolding mono_def by (auto simp add: ennsqrt_bij bij_is_surj)

lemma ennsqrt_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. ennsqrt(u n)) \<longlongrightarrow> ennsqrt l) F"
using ennsqrt_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma ennsqrt_ennreal_ennreal_sqrt [simp]:
  assumes "t \<ge> (0::real)"
  shows "ennsqrt (ennreal t) = ennreal (sqrt t)"
proof -
  have "ennreal t = ennreal (sqrt t) * ennreal(sqrt t)"
    apply (subst ennreal_mult[symmetric]) using assms by auto
  then show ?thesis
    by auto
qed

lemma ennreal_sqrt2:
  "ennreal (sqrt 2) = ennsqrt 2"
using ennsqrt_ennreal_ennreal_sqrt[of 2] by auto

lemma ennsqrt_4 [simp]:
  "ennsqrt 4 = 2"
by (metis ennreal_numeral ennsqrt_ennreal_ennreal_sqrt real_sqrt_four zero_le_numeral)

lemma ennsqrt_le [simp]:
  "ennsqrt x \<le> ennsqrt y \<longleftrightarrow> x \<le> y"
proof
  assume "ennsqrt x \<le> ennsqrt y"
  then have "ennsqrt x * ennsqrt x \<le> ennsqrt y * ennsqrt y"
    by (intro mult_mono, auto)
  then show "x \<le> y" by auto
qed (auto intro: mono_intros)

text \<open>We can also define the square root on ereal using the square root on ennreal, and $0$
for negative numbers.\<close>

definition esqrt::"ereal \<Rightarrow> ereal"
  where "esqrt x = enn2ereal(ennsqrt (e2ennreal x))"

lemma esqrt_square [simp]:
  assumes "x \<ge> 0"
  shows "(esqrt x) * (esqrt x) = x"
unfolding esqrt_def times_ennreal.rep_eq[symmetric] ennsqrt_square[of "e2ennreal x"]
using assms enn2ereal_e2ennreal by auto

lemma esqrt_of_neg [simp]:
  assumes "x \<le> 0"
  shows "esqrt x = 0"
  unfolding esqrt_def e2ennreal_neg[OF assms] by (auto simp add: zero_ennreal.rep_eq)

lemma esqrt_nonneg [simp]:
  "esqrt x \<ge> 0"
unfolding esqrt_def by auto

lemma esqrt_eq_iff_square [simp]:
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "esqrt x = y \<longleftrightarrow> x = y * y"
using esqrt_def esqrt_square assms apply auto
by (metis e2ennreal_enn2ereal ennsqrt_square2 eq_onp_same_args ereal_ennreal_cases leD times_ennreal.abs_eq)

lemma esqrt_simps [simp]:
  "esqrt 0 = 0"
  "esqrt 1 = 1"
  "esqrt \<infinity> = \<infinity>"
  "esqrt top = top"
  "esqrt (-\<infinity>) = 0"
by (auto simp: top_ereal_def)

lemma esqrt_mult:
  assumes "a \<ge> 0"
  shows "esqrt(a * b) = esqrt a * esqrt b"
proof (cases "b \<ge> 0")
  case True
  show ?thesis
    unfolding esqrt_def apply (subst times_ennreal.rep_eq[symmetric])
    apply (subst ennsqrt_mult[of "e2ennreal a" "e2ennreal b", symmetric])
    apply (subst times_ennreal.abs_eq)
    using assms True by (auto simp add: eq_onp_same_args)
next
  case False
  then have "a * b \<le> 0" using assms ereal_mult_le_0_iff by auto
  then have "esqrt(a * b) = 0" by auto
  moreover have "esqrt b = 0" using False by auto
  ultimately show ?thesis by auto
qed

lemma esqrt_square2 [simp]:
  "esqrt(x * x) = abs(x)"
proof -
  have "esqrt(x * x) = esqrt(abs x * abs x)"
    by (metis (no_types, hide_lams) abs_ereal_ge0 ereal_abs_mult ereal_zero_le_0_iff linear)
  also have "... = abs x"
    by (auto simp add: esqrt_mult)
  finally show ?thesis by auto
qed

lemma esqrt_mono:
  "mono esqrt"
unfolding esqrt_def mono_def by (auto intro: mono_intros)

lemma esqrt_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "esqrt x \<le> esqrt y"
using esqrt_mono assms unfolding mono_def by auto

lemma esqrt_continuous:
  "continuous_on UNIV esqrt"
unfolding esqrt_def apply (rule continuous_on_compose2[of UNIV enn2ereal], intro continuous_on_enn2ereal)
by (rule continuous_on_compose2[of UNIV ennsqrt], auto intro!: ennsqrt_continuous continuous_on_e2ennreal)

lemma esqrt_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. esqrt(u n)) \<longlongrightarrow> esqrt l) F"
using esqrt_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma esqrt_ereal_ereal_sqrt [simp]:
  assumes "t \<ge> (0::real)"
  shows "esqrt (ereal t) = ereal (sqrt t)"
proof -
  have "ereal t = ereal (sqrt t) * ereal(sqrt t)"
    using assms by auto
  then show ?thesis
    using assms ereal_less_eq(5) esqrt_mult esqrt_square real_sqrt_ge_zero by presburger
qed

lemma ereal_sqrt2:
  "ereal (sqrt 2) = esqrt 2"
using esqrt_ereal_ereal_sqrt[of 2] by auto

lemma esqrt_4 [simp]:
  "esqrt 4 = 2"
by auto

lemma esqrt_le [simp]:
  "esqrt x \<le> esqrt y \<longleftrightarrow> (x \<le> 0 \<or> x \<le> y)"
apply (auto simp add: esqrt_mono2)
by (metis eq_iff ereal_zero_times esqrt_mono2 esqrt_square le_cases)

text \<open>Finally, we define eexp, as the composition of ennexp and the injection of ennreal in ereal.\<close>

definition eexp::"ereal \<Rightarrow> ereal" where
  "eexp x = enn2ereal (ennexp x)"

lemma eexp_special_values [simp]:
  "eexp 0 = 1"
  "eexp (\<infinity>) = \<infinity>"
  "eexp(-\<infinity>) = 0"
unfolding eexp_def by (auto simp add: zero_ennreal.rep_eq one_ennreal.rep_eq)

lemma eexp_strict_mono:
  "strict_mono eexp"
unfolding eexp_def using ennexp_strict_mono unfolding strict_mono_def by (auto intro: mono_intros)

lemma eexp_mono:
  "mono eexp"
using eexp_strict_mono by (simp add: strict_mono_mono)

lemma eexp_strict_mono2 [mono_intros]:
  assumes "x < y"
  shows "eexp x < eexp y"
using eexp_strict_mono assms unfolding strict_mono_def by auto

lemma eexp_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "eexp x \<le> eexp y"
using eexp_mono assms unfolding mono_def by auto

lemma eexp_le_eexp_iff_le:
  "eexp x \<le> eexp y \<longleftrightarrow> x \<le> y"
using eexp_strict_mono2 not_le by (auto intro: mono_intros)

lemma eexp_lt_eexp_iff_lt:
  "eexp x < eexp y \<longleftrightarrow> x < y"
using eexp_mono2 not_le by (auto intro: mono_intros)

lemma eexp_special_values_iff [simp]:
  "eexp x = 0 \<longleftrightarrow> x = -\<infinity>"
  "eexp x = 1 \<longleftrightarrow> x = 0"
  "eexp x = \<infinity> \<longleftrightarrow> x = \<infinity>"
  "eexp x = top \<longleftrightarrow> x = \<infinity>"
unfolding eexp_def apply (auto simp add: zero_ennreal.rep_eq one_ennreal.rep_eq top_ereal_def)
apply (metis e2ennreal_enn2ereal ennexp.simps(3) ennexp_strict_mono strict_mono_eq zero_ennreal_def)
by (metis e2ennreal_enn2ereal eln_ennexp eln_simps(2) one_ennreal_def)

lemma eexp_ineq_iff [simp]:
  "eexp x \<le> 1 \<longleftrightarrow> x \<le> 0"
  "eexp x \<ge> 1 \<longleftrightarrow> x \<ge> 0"
  "eexp x > 1 \<longleftrightarrow> x > 0"
  "eexp x < 1 \<longleftrightarrow> x < 0"
  "eexp x \<ge> 0"
  "eexp x > 0 \<longleftrightarrow> x \<noteq> - \<infinity>"
  "eexp x < \<infinity> \<longleftrightarrow> x \<noteq> \<infinity>"
apply (metis eexp_le_eexp_iff_le eexp_lt_eexp_iff_lt eexp_special_values)+
apply (simp add: eexp_def)
using eexp_strict_mono2 apply (force)
by simp

lemma eexp_ineq [mono_intros]:
  "x \<le> 0 \<Longrightarrow> eexp x \<le> 1"
  "x < 0 \<Longrightarrow> eexp x < 1"
  "x \<ge> 0 \<Longrightarrow> eexp x \<ge> 1"
  "x > 0 \<Longrightarrow> eexp x > 1"
  "eexp x \<ge> 0"
  "x > -\<infinity> \<Longrightarrow> eexp x > 0"
  "x < \<infinity> \<Longrightarrow> eexp x < \<infinity>"
by auto

lemma eexp_continuous:
  "continuous_on UNIV eexp"
unfolding eexp_def by (rule continuous_on_compose2[of UNIV enn2ereal], auto simp: continuous_on_enn2ereal ennexp_continuous)


lemma eexp_tendsto' [simp]:
  "((\<lambda>n. eexp(u n)) \<longlongrightarrow> eexp l) F \<longleftrightarrow> ((\<lambda>n. u n) \<longlongrightarrow> l) F"
proof
  assume H: "((\<lambda>n. eexp (u n)) \<longlongrightarrow> eexp l) F"
  have "((\<lambda>n. eln (e2ennreal (eexp (u n)))) \<longlongrightarrow> eln (e2ennreal (eexp l))) F"
    by (intro tendsto_intros H)
  then show "(u \<longlongrightarrow> l) F"
    unfolding eexp_def by auto
next
  assume "(u \<longlongrightarrow> l) F"
  then show "((\<lambda>n. eexp(u n)) \<longlongrightarrow> eexp l) F"
    using eexp_continuous by (metis UNIV_I continuous_on tendsto_compose)
qed

lemma eexp_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. eexp(u n)) \<longlongrightarrow> eexp l) F"
using assms by auto

lemma eexp_add_mult:
  assumes "\<not>((a = \<infinity> \<and> b = -\<infinity>) \<or> (a = -\<infinity> \<and> b = \<infinity>))"
  shows "eexp(a+b) = eexp a * eexp b"
using ennexp_add_mult[OF assms] unfolding eexp_def by (simp add: times_ennreal.rep_eq)

lemma eexp_ereal [simp]:
  "eexp(ereal x) = ereal(exp x)"
by (simp add: eexp_def)

end (*of theory Eexp_Eln*)
