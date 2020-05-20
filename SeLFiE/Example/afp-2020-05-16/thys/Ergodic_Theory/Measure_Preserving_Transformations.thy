(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Measure preserving or quasi-preserving maps\<close>

theory Measure_Preserving_Transformations
  imports SG_Library_Complement
begin

text \<open>Ergodic theory in general is the study of the properties of measure preserving or
quasi-preserving dynamical systems. In this section, we introduce the basic definitions
in this respect.\<close>

subsection \<open>The different classes of transformations\<close>

definition quasi_measure_preserving::"'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "quasi_measure_preserving M N
    = {f \<in> measurable M N. \<forall> A \<in> sets N. (f -` A \<inter> space M \<in> null_sets M) = (A \<in> null_sets N)}"

lemma quasi_measure_preservingI [intro]:
  assumes "f \<in> measurable M N"
          "\<And>A. A \<in> sets N \<Longrightarrow> (f -` A \<inter> space M \<in> null_sets M) = (A \<in> null_sets N)"
  shows "f \<in> quasi_measure_preserving M N"
using assms unfolding quasi_measure_preserving_def by auto

lemma quasi_measure_preservingE:
  assumes "f \<in> quasi_measure_preserving M N"
  shows "f \<in> measurable M N"
        "\<And>A. A \<in> sets N \<Longrightarrow> (f -` A \<inter> space M \<in> null_sets M) = (A \<in> null_sets N)"
using assms unfolding quasi_measure_preserving_def by auto

lemma id_quasi_measure_preserving:
  "(\<lambda>x. x) \<in> quasi_measure_preserving M M"
unfolding quasi_measure_preserving_def by auto

lemma quasi_measure_preserving_composition:
  assumes "f \<in> quasi_measure_preserving M N"
          "g \<in> quasi_measure_preserving N P"
  shows "(\<lambda>x. g(f x)) \<in> quasi_measure_preserving M P"
proof (rule quasi_measure_preservingI)
  have f_meas [measurable]: "f \<in> measurable M N" by (rule quasi_measure_preservingE(1)[OF assms(1)])
  have g_meas [measurable]: "g \<in> measurable N P" by (rule quasi_measure_preservingE(1)[OF assms(2)])
  then show [measurable]: "(\<lambda>x. g (f x)) \<in> measurable M P" by auto

  fix C assume [measurable]: "C \<in> sets P"
  define B where "B = g-`C \<inter> space N"
  have [measurable]: "B \<in> sets N" unfolding B_def by simp
  have *: "B \<in> null_sets N \<longleftrightarrow> C \<in> null_sets P"
    unfolding B_def using quasi_measure_preservingE(2)[OF assms(2)] by simp

  define A where "A = f-`B \<inter> space M"
  have [measurable]: "A \<in> sets M" unfolding A_def by simp
  have "A \<in> null_sets M \<longleftrightarrow> B \<in> null_sets N"
    unfolding A_def using quasi_measure_preservingE(2)[OF assms(1)] by simp

  then have "A \<in> null_sets M \<longleftrightarrow> C \<in> null_sets P" using * by simp
  moreover have "A = (\<lambda>x. g (f x)) -` C \<inter> space M"
    by (auto simp add: A_def B_def) (meson f_meas measurable_space)
  ultimately show "((\<lambda>x. g (f x)) -` C \<inter> space M \<in> null_sets M) \<longleftrightarrow> C \<in> null_sets P" by simp
qed

lemma quasi_measure_preserving_comp:
  assumes "f \<in> quasi_measure_preserving M N"
          "g \<in> quasi_measure_preserving N P"
  shows "g o f \<in> quasi_measure_preserving M P"
unfolding comp_def using assms quasi_measure_preserving_composition by blast

lemma quasi_measure_preserving_AE:
  assumes "f \<in> quasi_measure_preserving M N"
          "AE x in N. P x"
  shows "AE x in M. P (f x)"
proof -
  obtain A where "\<And>x. x \<in> space N - A \<Longrightarrow> P x" "A \<in> null_sets N"
    using AE_E3[OF assms(2)] by blast
  define B where "B = f-`A \<inter> space M"
  have "B \<in> null_sets M"
    unfolding B_def using quasi_measure_preservingE(2)[OF assms(1)] \<open>A \<in> null_sets N\<close> by auto
  moreover have "x \<in> space M - B \<Longrightarrow> P (f x)" for x
    using \<open>\<And>x. x \<in> space N - A \<Longrightarrow> P x\<close> quasi_measure_preservingE(1)[OF assms(1)]
    unfolding B_def by (metis (no_types, lifting) Diff_iff IntI measurable_space vimage_eq)
  ultimately show ?thesis using AE_not_in AE_space by force
qed

lemma quasi_measure_preserving_AE':
  assumes "f \<in> quasi_measure_preserving M N"
          "AE x in M. P (f x)"
          "{x \<in> space N. P x} \<in> sets N"
  shows "AE x in N. P x"
proof -
  have [measurable]: "f \<in> measurable M N" using quasi_measure_preservingE(1)[OF assms(1)] by simp
  define U where "U = {x \<in> space N. \<not>(P x)}"
  have [measurable]: "U \<in> sets N" unfolding U_def using assms(3) by auto
  have "f-`U \<inter> space M = {x \<in> space M. \<not>(P (f x))}"
    unfolding U_def using \<open>f \<in> measurable M N\<close> by (auto, meson measurable_space)
  also have "... \<in> null_sets M"
    apply (subst AE_iff_null[symmetric]) using assms by auto
  finally have "U \<in> null_sets N"
    using quasi_measure_preservingE(2)[OF assms(1) \<open>U \<in> sets N\<close>] by auto
  then show ?thesis unfolding U_def using AE_iff_null by blast
qed

text \<open>The push-forward under a quasi-measure preserving map $f$ of a measure absolutely
continuous with respect to $M$ is absolutely continuous with respect to $N$.\<close>
lemma quasi_measure_preserving_absolutely_continuous:
  assumes "f \<in> quasi_measure_preserving M N"
          "u \<in> borel_measurable M"
  shows "absolutely_continuous N (distr (density M u) N f)"
proof -
  have [measurable]: "f \<in> measurable M N" using quasi_measure_preservingE[OF assms(1)] by auto
  have "S \<in> null_sets (distr (density M u) N f)" if [measurable]: "S \<in> null_sets N" for S
  proof -
    have [measurable]: "S \<in> sets N" using null_setsD2[OF that] by auto
    have *: "AE x in N. x \<notin> S"
      by (metis AE_not_in that)
    have "AE x in M. f x \<notin> S"
      by (rule quasi_measure_preserving_AE[OF _ *], simp add: assms)
    then have *: "AE x in M. indicator S (f x) * u x = 0"
      by force

    have "emeasure (distr (density M u) N f) S = (\<integral>\<^sup>+x. indicator S x \<partial>(distr (density M u) N f))"
      by auto
    also have "... = (\<integral>\<^sup>+x. indicator S (f x) \<partial>(density M u))"
      by (rule nn_integral_distr, auto)
    also have "... = (\<integral>\<^sup>+x. indicator S (f x) * u x \<partial>M)"
      by (rule nn_integral_densityR[symmetric], auto simp add: assms)
    also have "... = (\<integral>\<^sup>+x. 0 \<partial>M)"
      using * by (rule nn_integral_cong_AE)
    finally have "emeasure (distr (density M u) N f) S = 0" by auto
    then show ?thesis by auto
  qed
  then show ?thesis unfolding absolutely_continuous_def by auto
qed

definition measure_preserving::"'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "measure_preserving M N
          = {f \<in> measurable M N. (\<forall> A \<in> sets N. emeasure M (f-`A \<inter> space M) = emeasure N A)}"

lemma measure_preservingE:
  assumes "f \<in> measure_preserving M N"
  shows "f \<in> measurable M N"
        "\<And>A. A \<in> sets N \<Longrightarrow> emeasure M (f-`A \<inter> space M) = emeasure N A"
using assms unfolding measure_preserving_def by auto

lemma measure_preservingI [intro]:
  assumes "f \<in> measurable M N"
          "\<And>A. A \<in> sets N \<Longrightarrow> emeasure M (f-`A \<inter> space M) = emeasure N A"
  shows "f \<in> measure_preserving M N"
using assms unfolding measure_preserving_def by auto

lemma measure_preserving_distr:
  assumes "f \<in> measure_preserving M N"
  shows "distr M N f = N"
proof -
  let ?N2 = "distr M N f"
  have "sets ?N2 = sets N" by simp
  moreover have "emeasure ?N2 A = emeasure N A" if "A \<in> sets N" for A
  proof -
    have "emeasure ?N2 A = emeasure M (f-`A \<inter> space M)"
      using \<open>A \<in> sets N\<close> assms emeasure_distr measure_preservingE(1)[OF assms] by blast
    then show "emeasure ?N2 A = emeasure N A"
      using \<open>A \<in> sets N\<close> measure_preservingE(2)[OF assms] by auto
  qed
  ultimately show ?thesis by (metis measure_eqI)
qed

lemma measure_preserving_distr':
  assumes "f \<in> measurable M N"
  shows "f \<in> measure_preserving M (distr M N f)"
proof (rule measure_preservingI)
  show "f \<in> measurable M (distr M N f)" using assms(1) by auto
  show "emeasure M (f-`A \<inter> space M) = emeasure (distr M N f) A" if "A \<in> sets (distr M N f)" for A
    using that emeasure_distr[OF assms] by auto
qed

lemma measure_preserving_preserves_nn_integral:
  assumes "T \<in> measure_preserving M N"
          "f \<in> borel_measurable N"
  shows "(\<integral>\<^sup>+x. f x \<partial>N) = (\<integral>\<^sup>+x. f (T x) \<partial>M)"
proof -
  have "(\<integral>\<^sup>+x. f (T x) \<partial>M) = (\<integral>\<^sup>+y. f y \<partial>distr M N T)"
    using assms nn_integral_distr[of T M N f, OF measure_preservingE(1)[OF assms(1)]] by simp
  also have "... = (\<integral>\<^sup>+y. f y \<partial>N)"
    using measure_preserving_distr[OF assms(1)] by simp
  finally show ?thesis by simp
qed

lemma measure_preserving_preserves_integral:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "T \<in> measure_preserving M N"
      and [measurable]: "integrable N f"
  shows "integrable M (\<lambda>x. f(T x))" "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)"
proof -
  have a [measurable]: "T \<in> measurable M N" by (rule measure_preservingE(1)[OF assms(1)])
  have b [measurable]: "f \<in> borel_measurable N" by simp
  have "distr M N T = N" using measure_preserving_distr[OF assms(1)] by simp
  then have "integrable (distr M N T) f" using assms(2) by simp
  then show "integrable M (\<lambda>x. f(T x))" using integrable_distr_eq[OF a b] by simp

  have "(\<integral>x. f (T x) \<partial>M) = (\<integral>y. f y \<partial>distr M N T)" using integral_distr[OF a b] by simp
  then show "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)" using \<open>distr M N T = N\<close> by simp
qed

lemma measure_preserving_preserves_integral':
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "T \<in> measure_preserving M N"
      and [measurable]: "integrable M (\<lambda>x. f (T x))" "f \<in> borel_measurable N"
  shows "integrable N f" "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)"
proof -
  have a [measurable]: "T \<in> measurable M N" by (rule measure_preservingE(1)[OF assms(1)])
  have "integrable M (\<lambda>x. f(T x))" using assms(2) unfolding comp_def by auto
  then have "integrable (distr M N T) f"
    using integrable_distr_eq[OF a assms(3)] by simp
  then show *: "integrable N f" using measure_preserving_distr[OF assms(1)] by simp

  then show "(\<integral>x. f x \<partial>N) = (\<integral>x. f (T x) \<partial>M)"
    using measure_preserving_preserves_integral[OF assms(1) *] by simp
qed

lemma id_measure_preserving:
  "(\<lambda>x. x) \<in> measure_preserving M M"
unfolding measure_preserving_def by auto

lemma measure_preserving_is_quasi_measure_preserving:
  assumes "f \<in> measure_preserving M N"
  shows "f \<in> quasi_measure_preserving M N"
using assms unfolding measure_preserving_def quasi_measure_preserving_def apply auto
by (metis null_setsD1 null_setsI, metis measurable_sets null_setsD1 null_setsI)

lemma measure_preserving_composition:
  assumes "f \<in> measure_preserving M N"
          "g \<in> measure_preserving N P"
  shows "(\<lambda>x. g(f x)) \<in> measure_preserving M P"
proof (rule measure_preservingI)
  have f [measurable]: "f \<in> measurable M N" by (rule measure_preservingE(1)[OF assms(1)])
  have g [measurable]: "g \<in> measurable N P" by (rule measure_preservingE(1)[OF assms(2)])
  show [measurable]: "(\<lambda>x. g (f x)) \<in> measurable M P" by auto

  fix C assume [measurable]: "C \<in> sets P"
  define B where "B = g-`C \<inter> space N"
  have [measurable]: "B \<in> sets N" unfolding B_def by simp
  have *: "emeasure N B = emeasure P C"
    unfolding B_def using measure_preservingE(2)[OF assms(2)] by simp

  define A where "A = f-`B \<inter> space M"
  have [measurable]: "A \<in> sets M" unfolding A_def by simp
  have "emeasure M A = emeasure N B"
    unfolding A_def using measure_preservingE(2)[OF assms(1)] by simp

  then have "emeasure M A = emeasure P C" using * by simp
  moreover have "A = (\<lambda>x. g(f x))-`C \<inter> space M"
    by (auto simp add: A_def B_def) (meson f measurable_space)
  ultimately show "emeasure M ((\<lambda>x. g(f x))-`C \<inter> space M) = emeasure P C" by simp
qed

lemma measure_preserving_comp:
  assumes "f \<in> measure_preserving M N"
          "g \<in> measure_preserving N P"
  shows "g o f \<in> measure_preserving M P"
unfolding o_def using measure_preserving_composition assms by blast

lemma measure_preserving_total_measure:
  assumes "f \<in> measure_preserving M N"
  shows "emeasure M (space M) = emeasure N (space N)"
proof -
  have "f \<in> measurable M N" by (rule measure_preservingE(1)[OF assms(1)])
  then have "f-`(space N) \<inter> space M = space M" by (meson Int_absorb1 measurable_space subsetI vimageI)
  then show "emeasure M (space M) = emeasure N (space N)"
    by (metis (mono_tags, lifting) measure_preservingE(2)[OF assms(1)] sets.top)
qed

lemma measure_preserving_finite_measure:
  assumes "f \<in> measure_preserving M N"
  shows "finite_measure M \<longleftrightarrow> finite_measure N"
using measure_preserving_total_measure[OF assms]
by (metis finite_measure.emeasure_finite finite_measureI infinity_ennreal_def)

lemma measure_preserving_prob_space:
  assumes "f \<in> measure_preserving M N"
  shows "prob_space M \<longleftrightarrow> prob_space N"
using measure_preserving_total_measure[OF assms] by (metis prob_space.emeasure_space_1 prob_spaceI)

locale qmpt = sigma_finite_measure +
  fixes T
  assumes Tqm: "T \<in> quasi_measure_preserving M M"

locale mpt = qmpt +
  assumes Tm: "T \<in> measure_preserving M M"

locale fmpt = mpt + finite_measure

locale pmpt = fmpt + prob_space

lemma qmpt_I:
  assumes "sigma_finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> ((T-`A \<inter> space M) \<in> null_sets M) \<longleftrightarrow> (A \<in> null_sets M)"
  shows "qmpt M T"
unfolding qmpt_def qmpt_axioms_def quasi_measure_preserving_def
by (auto simp add: assms)

lemma mpt_I:
  assumes "sigma_finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "mpt M T"
proof -
  have *: "T \<in> measure_preserving M M"
    by (rule measure_preservingI[OF assms(2) assms(3)])
  then have **: "T \<in> quasi_measure_preserving M M"
    using measure_preserving_is_quasi_measure_preserving by auto
  show "mpt M T"
    unfolding mpt_def qmpt_def qmpt_axioms_def mpt_axioms_def using * ** assms(1) by auto
qed

lemma fmpt_I:
  assumes "finite_measure M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "fmpt M T"
proof -
  have *: "T \<in> measure_preserving M M"
    by (rule measure_preservingI[OF assms(2) assms(3)])
  then have **: "T \<in> quasi_measure_preserving M M"
    using measure_preserving_is_quasi_measure_preserving by auto
  show "fmpt M T"
    unfolding fmpt_def mpt_def qmpt_def mpt_axioms_def qmpt_axioms_def
    using * ** assms(1) finite_measure_def by auto
qed

lemma pmpt_I:
  assumes "prob_space M"
          "T \<in> measurable M M"
          "\<And>A. A \<in> sets M \<Longrightarrow> emeasure M (T-`A \<inter> space M) = emeasure M A"
  shows "pmpt M T"
proof -
  have *: "T \<in> measure_preserving M M"
    by (rule measure_preservingI[OF assms(2) assms(3)])
  then have **: "T \<in> quasi_measure_preserving M M"
    using measure_preserving_is_quasi_measure_preserving by auto
  show "pmpt M T"
    unfolding pmpt_def fmpt_def mpt_def qmpt_def mpt_axioms_def qmpt_axioms_def
    using * ** assms(1) prob_space_imp_sigma_finite prob_space.finite_measure by auto
qed

subsection \<open>Examples\<close>

lemma fmpt_null_space:
  assumes "emeasure M (space M) = 0"
          "T \<in> measurable M M"
  shows "fmpt M T"
apply (rule fmpt_I)
apply (auto simp add: assms finite_measureI)
apply (metis assms emeasure_eq_0 measurable_sets sets.sets_into_space sets.top)
done

lemma fmpt_empty_space:
  assumes "space M = {}"
  shows "fmpt M T"
by (rule fmpt_null_space, auto simp add: assms measurable_empty_iff)

text \<open>Translations are measure-preserving\<close>

lemma mpt_translation:
  fixes c :: "'a::euclidean_space"
  shows "mpt lborel (\<lambda>x. x + c)"
proof (rule mpt_I, auto simp add: lborel.sigma_finite_measure_axioms)
  fix A::"'a set" assume [measurable]: "A \<in> sets borel"
  have "emeasure lborel ((\<lambda>x. x + c) -` A) = emeasure lborel ((((+))c)-`A)" by (meson add.commute)
  also have "... = emeasure lborel ((((+))c)-`A \<inter> space lborel)" by simp
  also have "... = emeasure (distr lborel borel ((+) c)) A" by (rule emeasure_distr[symmetric], auto)
  also have "... = emeasure lborel A" using lborel_distr_plus[of c] by simp
  finally show "emeasure lborel ((\<lambda>x. x + c) -` A) = emeasure lborel A" by simp
qed

text \<open>Skew products are fibered maps of the form $(x,y)\mapsto (Tx, U(x,y))$. If the base map
and the fiber maps all are measure preserving, so is the skew product.\<close>

lemma pair_measure_null_product:
  assumes "emeasure M (space M) = 0"
  shows "emeasure (M \<Otimes>\<^sub>M N) (space (M \<Otimes>\<^sub>M N)) = 0"
proof -
  have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator X (x,y) \<partial>N) \<partial>M) = 0" for X
  proof -
    have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator X (x,y) \<partial>N) \<partial>M) = (\<integral>\<^sup>+x. 0 \<partial>M)"
      by (intro nn_integral_cong_AE emeasure_0_AE[OF assms])
    then show ?thesis by auto
  qed
  then have "M \<Otimes>\<^sub>M N = measure_of (space M \<times> space N)
      {a \<times> b | a b. a \<in> sets M \<and> b \<in> sets N}
      (\<lambda>X. 0)"
    unfolding pair_measure_def by auto
  then show ?thesis by (simp add: emeasure_sigma)
qed

lemma mpt_skew_product:
  assumes "mpt M T"
          "AE x in M. mpt N (U x)"
    and [measurable]: "(\<lambda>(x,y). U x y) \<in> measurable (M \<Otimes>\<^sub>M N) N"
  shows "mpt (M \<Otimes>\<^sub>M N) (\<lambda>(x,y). (T x, U x y))"
proof (cases)
  assume H: "emeasure M (space M) = 0"
  then have *: "emeasure (M \<Otimes>\<^sub>M N) (space (M \<Otimes>\<^sub>M N)) = 0"
    using pair_measure_null_product by auto
  have [measurable]: "T \<in> measurable M M"
    using assms(1) unfolding mpt_def qmpt_def qmpt_axioms_def quasi_measure_preserving_def by auto
  then have [measurable]: "(\<lambda>(x, y). (T x, U x y)) \<in> measurable (M \<Otimes>\<^sub>M N) (M \<Otimes>\<^sub>M N)" by auto
  with fmpt_null_space[OF *] show ?thesis by (simp add: fmpt.axioms(1))
next
  assume "\<not>(emeasure M (space M) = 0)"
  show ?thesis
  proof (rule mpt_I)
    have "sigma_finite_measure M" using assms(1) unfolding mpt_def qmpt_def by auto
    then interpret M: sigma_finite_measure M .

    have "\<exists>p. \<not> almost_everywhere M p"
      by (metis (lifting) AE_E \<open>emeasure M (space M) \<noteq> 0\<close> emeasure_eq_AE emeasure_notin_sets)
    then have "\<exists>x. mpt N (U x)" using assms(2) \<open>\<not>(emeasure M (space M) = 0)\<close>
      by (metis (full_types) \<open>AE x in M. mpt N (U x)\<close> eventually_mono)
    then have "sigma_finite_measure N" unfolding mpt_def qmpt_def by auto
    then interpret N: sigma_finite_measure N .
    show "sigma_finite_measure (M \<Otimes>\<^sub>M N)"
      by (rule sigma_finite_pair_measure) standard+

    have [measurable]: "T \<in> measurable M M"
      using assms(1) unfolding mpt_def qmpt_def qmpt_axioms_def quasi_measure_preserving_def by auto
    show [measurable]: "(\<lambda>(x, y). (T x, U x y)) \<in> measurable (M \<Otimes>\<^sub>M N) (M \<Otimes>\<^sub>M N)" by auto
    have "T \<in> measure_preserving M M" using assms(1) by (simp add: mpt.Tm)

    fix A assume [measurable]: "A \<in> sets (M \<Otimes>\<^sub>M N)"
    then have [measurable]: "(\<lambda> (x,y). (indicator A (x,y))::ennreal) \<in> borel_measurable (M \<Otimes>\<^sub>M N)" by auto
    then have [measurable]: "(\<lambda>x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>N) \<in> borel_measurable M"
      by simp

    define B where "B = (\<lambda>(x, y). (T x, U x y)) -` A \<inter> space (M \<Otimes>\<^sub>M N)"
    then have [measurable]: "B \<in> sets (M \<Otimes>\<^sub>M N)" by auto

    have "(\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) = (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N)" if "x \<in> space M" "mpt N (U x)" for x
    proof -
      have "T x \<in> space M" by (meson \<open>T \<in> measurable M M\<close> \<open>x \<in> space M\<close> measurable_space)
      then have 1: "(\<lambda>y. (indicator A (T x, y))::ennreal) \<in> borel_measurable N" using \<open>A \<in> sets (M \<Otimes>\<^sub>M N)\<close> by auto
      have 2: "\<And>y. ((indicator B (x, y))::ennreal) = indicator A (T x, U x y) * indicator (space M) x * indicator (space N) y"
        unfolding B_def by (simp add: indicator_def space_pair_measure)
      have 3: "U x \<in> measure_preserving N N" using assms(2) that(2) by (simp add: mpt.Tm)

      have "(\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) = (\<integral>\<^sup>+y. indicator A (T x, U x y) \<partial>N)"
        using 2 by (intro nn_integral_cong_simp) (auto simp add: indicator_def \<open>x \<in> space M\<close>)
      also have "... = (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N)"
        by (rule measure_preserving_preserves_nn_integral[OF 3, symmetric], metis 1)
      finally show ?thesis by simp
    qed
    then have *: "AE x in M. (\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) = (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N)"
      using assms(2) by auto

    have "emeasure (M \<Otimes>\<^sub>M N) B = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator B (x,y) \<partial>N) \<partial>M)"
      using \<open>B \<in> sets (M \<Otimes>\<^sub>M N)\<close> \<open>sigma_finite_measure N\<close> sigma_finite_measure.emeasure_pair_measure by fastforce
    also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator A (T x, y) \<partial>N) \<partial>M)"
      by (intro nn_integral_cong_AE *)
    also have "... = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator A (x, y) \<partial>N) \<partial>M)"
      by (rule measure_preserving_preserves_nn_integral[OF \<open>T \<in> measure_preserving M M\<close>, symmetric]) auto
    also have "... = emeasure (M \<Otimes>\<^sub>M N) A"
      by (simp add: \<open>sigma_finite_measure N\<close> sigma_finite_measure.emeasure_pair_measure)
    finally show "emeasure (M \<Otimes>\<^sub>M N) ((\<lambda>(x, y). (T x, U x y)) -` A \<inter> space (M \<Otimes>\<^sub>M N)) = emeasure (M \<Otimes>\<^sub>M N) A"
      unfolding B_def by simp
  qed
qed

lemma mpt_skew_product_real:
  fixes f::"'a \<Rightarrow> 'b::euclidean_space"
  assumes "mpt M T" and [measurable]: "f \<in> borel_measurable M"
  shows "mpt (M \<Otimes>\<^sub>M lborel) (\<lambda>(x,y). (T x, y + f x))"
by (rule mpt_skew_product, auto simp add: mpt_translation assms(1))


subsection \<open>Preimages restricted to $space M$\<close>

context qmpt begin

text \<open>One is all the time lead to take the preimages of sets, and restrict them to
\verb+space M+ where the dynamics is living. We introduce a shortcut for this notion.\<close>

definition vimage_restr :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr "--`" 90)
where
  "f --` A \<equiv> f-` (A \<inter> space M) \<inter> space M"

lemma vrestr_eq [simp]:
  "a \<in> f--` A \<longleftrightarrow> a \<in> space M \<and> f a \<in> A \<inter> space M"
unfolding vimage_restr_def by auto

lemma vrestr_intersec [simp]:
  "f--` (A \<inter> B) = (f--`A) \<inter> (f--` B)"
using vimage_restr_def by auto

lemma vrestr_union [simp]:
  "f--` (A \<union> B) = f--`A \<union> f--`B"
using vimage_restr_def by auto

lemma vrestr_difference [simp]:
  "f--`(A-B) = f--`A - f--`B"
using vimage_restr_def by auto

lemma vrestr_inclusion:
  "A \<subseteq> B \<Longrightarrow> f--`A \<subseteq> f--`B"
using vimage_restr_def by auto

lemma vrestr_Union [simp]:
  "f --` (\<Union>A) = (\<Union>X\<in>A. f --` X)"
using vimage_restr_def by auto

lemma vrestr_UN [simp]:
  "f --` (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. f --` B x)"
using vimage_restr_def by auto

lemma vrestr_Inter [simp]:
  assumes "A \<noteq> {}"
  shows "f --` (\<Inter>A) = (\<Inter>X\<in>A. f --` X)"
using vimage_restr_def assms by auto

lemma vrestr_INT [simp]:
  assumes "A \<noteq> {}"
  shows "f --` (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. f --` B x)"
using vimage_restr_def assms by auto

lemma vrestr_empty [simp]:
  "f--`{} = {}"
using vimage_restr_def by auto

lemma vrestr_sym_diff [simp]:
  "f--`(A \<Delta> B) = (f--`A) \<Delta> (f--`B)"
by auto

lemma vrestr_image:
  assumes "x \<in> f--`A"
  shows "x \<in> space M" "f x \<in> space M" "f x \<in> A"
using assms unfolding vimage_restr_def by auto

lemma vrestr_intersec_in_space:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "A \<inter> f--`B = A \<inter> f-`B"
unfolding vimage_restr_def using assms sets.sets_into_space by auto

lemma vrestr_compose:
  assumes "g \<in> measurable M M"
  shows "(\<lambda> x. f(g x))--` A = g--` (f--` A)"
proof -
  define B where "B = A \<inter> space M"
  have "(\<lambda> x. f(g x))--` A = (\<lambda> x. f(g x)) -` B \<inter> space M"
    using B_def vimage_restr_def by blast
  moreover have "(\<lambda> x. f(g x)) -` B \<inter> space M = g-` (f-` B \<inter> space M) \<inter> space M"
    using measurable_space[OF \<open>g \<in> measurable M M\<close>] by auto
  moreover have "g-` (f-` B \<inter> space M) \<inter> space M = g--` (f--` A)"
    using B_def vimage_restr_def by simp
  ultimately show ?thesis by auto
qed

lemma vrestr_comp:
  assumes "g \<in> measurable M M"
  shows "(f o g)--` A = g--` (f--` A)"
proof -
  have "f o g = (\<lambda> x. f(g x))" by auto
  then have "(f o g)--` A = (\<lambda> x. f(g x))--` A" by auto
  moreover have "(\<lambda> x. f(g x))--` A = g--` (f--` A)" using vrestr_compose assms by auto
  ultimately show ?thesis by simp
qed

lemma vrestr_of_set:
  assumes "g \<in> measurable M M"
  shows "A \<in> sets M \<Longrightarrow> g--`A = g-`A \<inter> space M"
by (simp add: vimage_restr_def)

lemma vrestr_meas [measurable (raw)]:
  assumes "g \<in> measurable M M"
          "A \<in> sets M"
  shows "g--`A \<in> sets M"
using assms vimage_restr_def by auto

lemma vrestr_same_emeasure_f:
  assumes "f \<in> measure_preserving M M"
          "A \<in> sets M"
  shows "emeasure M (f--`A) = emeasure M A"
by (metis (mono_tags, lifting) assms measure_preserving_def mem_Collect_eq sets.Int_space_eq2 vimage_restr_def)

lemma vrestr_same_measure_f:
  assumes "f \<in> measure_preserving M M"
          "A \<in> sets M"
  shows "measure M (f--`A) = measure M A"
proof -
  have "measure M (f--`A) = enn2real (emeasure M (f--`A))" by (simp add: Sigma_Algebra.measure_def)
  also have "... = enn2real (emeasure M A)" using vrestr_same_emeasure_f[OF assms] by simp
  also have "... = measure M A" by (simp add: Sigma_Algebra.measure_def)
  finally show "measure M (f--` A) = measure M A" by simp
qed


subsection \<open>Basic properties of qmpt\<close>

lemma T_meas [measurable (raw)]:
  "T \<in> measurable M M"
by (rule quasi_measure_preservingE(1)[OF Tqm])

lemma Tn_quasi_measure_preserving:
  "T^^n \<in> quasi_measure_preserving M M"
proof (induction n)
    case 0
    show ?case using id_quasi_measure_preserving by simp
  next
    case (Suc n)
    then show ?case using Tqm quasi_measure_preserving_comp by (metis funpow_Suc_right)
qed

lemma Tn_meas [measurable (raw)]:
  "T^^n \<in> measurable M M"
by (rule quasi_measure_preservingE(1)[OF Tn_quasi_measure_preserving])

lemma T_vrestr_meas [measurable]:
  assumes "A \<in> sets M"
  shows "T--` A \<in> sets M"
        "(T^^n)--` A \<in> sets M"
by (auto simp add: vrestr_meas assms)

text \<open>We state the next lemma both with $T^0$ and with $id$ as sometimes the simplifier
simplifies $T^0$ to $id$ before applying the first instance of the lemma.\<close>

lemma T_vrestr_0 [simp]:
  assumes "A \<in> sets M"
  shows "(T^^0)--`A = A"
        "id--`A = A"
using sets.sets_into_space[OF assms] by auto

lemma T_vrestr_composed:
  assumes "A \<in> sets M"
  shows "(T^^n)--` (T^^m)--` A = (T^^(n+m))--` A"
        "T--` (T^^m)--` A = (T^^(m+1))--` A"
        "(T^^m)--` T--` A = (T^^(m+1))--` A"
proof -
  show "(T^^n)--` (T^^m)--` A = (T^^(n+m))--` A"
    by (simp add: Tn_meas funpow_add add.commute vrestr_comp)
  show "T--` (T^^m)--` A = (T^^(m+1))--` A"
    by (metis Suc_eq_plus1 T_meas funpow_Suc_right vrestr_comp)
  show "(T^^m)--` T--` A = (T^^(m+1))--` A"
    by (simp add: Tn_meas vrestr_comp)
qed

text \<open>In the next two lemmas, we give measurability statements that show up all the time
for the usual preimage.\<close>

lemma T_intersec_meas [measurable]:
  assumes [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "A \<inter> T-`B \<in> sets M"
        "A \<inter> (T^^n)-`B \<in> sets M"
        "T-`A \<inter> B \<in> sets M"
        "(T^^n)-`A \<inter> B \<in> sets M"
        "A \<inter> (T \<circ> T ^^ n) -` B \<in> sets M"
        "(T \<circ> T ^^ n) -` A \<inter> B \<in> sets M"
by (metis T_meas Tn_meas assms(1) assms(2) measurable_comp sets.Int inf_commute
      vrestr_intersec_in_space vrestr_meas)+

lemma T_diff_meas [measurable]:
  assumes [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "A - T-`B \<in> sets M"
        "A - (T^^n)-`B \<in> sets M"
proof -
  have "A - T-`B = A \<inter> space M - (T-`B \<inter> space M)"
    using sets.sets_into_space[OF assms(1)] by auto
  then show "A - T-`B \<in> sets M" by auto
  have "A - (T^^n)-`B = A \<inter> space M - ((T^^n)-`B \<inter> space M)"
    using sets.sets_into_space[OF assms(1)] by auto
  then show "A - (T^^n)-`B \<in> sets M" by auto
qed

lemma T_spaceM_stable [simp]:
  assumes "x \<in> space M"
  shows "T x \<in> space M"
        "(T^^n) x \<in> space M"
proof -
  show "T x \<in> space M" by (meson measurable_space T_meas measurable_def assms)
  show "(T^^n) x \<in> space M" by (meson measurable_space Tn_meas measurable_def assms)
qed

lemma T_quasi_preserves_null:
  assumes "A \<in> sets M"
  shows "A \<in> null_sets M \<longleftrightarrow> T--` A \<in> null_sets M"
        "A \<in> null_sets M \<longleftrightarrow> (T^^n)--` A \<in> null_sets M"
using Tqm Tn_quasi_measure_preserving unfolding quasi_measure_preserving_def
by (auto simp add: assms vimage_restr_def)

lemma T_quasi_preserves:
  assumes "A \<in> sets M"
  shows "emeasure M A = 0 \<longleftrightarrow> emeasure M (T--` A) = 0"
        "emeasure M A = 0 \<longleftrightarrow> emeasure M ((T^^n)--` A) = 0"
using T_quasi_preserves_null[OF assms] T_vrestr_meas assms by blast+

lemma T_quasi_preserves_null2:
  assumes "A \<in> null_sets M"
  shows "T--` A \<in> null_sets M"
        "(T^^n)--` A \<in> null_sets M"
using T_quasi_preserves_null[OF null_setsD2[OF assms]] assms by auto

lemma T_composition_borel [measurable]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. f(T x)) \<in> borel_measurable M" "(\<lambda>x. f((T^^k) x)) \<in> borel_measurable M"
using T_meas Tn_meas assms measurable_compose by auto

lemma T_AE_iterates:
  assumes "AE x in M. P x"
  shows "AE x in M. \<forall>n. P ((T^^n) x)"
proof -
  have "AE x in M. P ((T^^n) x)" for n
    by (rule quasi_measure_preserving_AE[OF Tn_quasi_measure_preserving[of n] assms])
  then show ?thesis unfolding AE_all_countable by simp
qed

lemma qmpt_power:
  "qmpt M (T^^n)"
by (standard, simp add: Tn_quasi_measure_preserving)

lemma T_Tn_T_compose:
  "T ((T^^n) x) = (T^^(Suc n)) x"
  "(T^^n) (T x) = (T^^(Suc n)) x"
by (auto simp add: funpow_swap1)

lemma (in qmpt) qmpt_density:
  assumes [measurable]: "h \<in> borel_measurable M"
      and "AE x in M. h x \<noteq> 0" "AE x in M. h x \<noteq> \<infinity>"
  shows "qmpt (density M h) T"
proof -
  interpret A: sigma_finite_measure "density M h"
    apply (subst sigma_finite_iff_density_finite) using assms by auto
  show ?thesis
    apply (standard) apply (rule quasi_measure_preservingI)
    unfolding null_sets_density[OF \<open>h \<in> borel_measurable M\<close> \<open>AE x in M. h x \<noteq> 0\<close>] sets_density space_density
    using quasi_measure_preservingE(2)[OF Tqm] by auto
qed

end




subsection \<open>Basic properties of mpt\<close>

context mpt
begin

lemma Tn_measure_preserving:
  "T^^n \<in> measure_preserving M M"
proof (induction n)
    case (Suc n)
    then show ?case using Tm measure_preserving_comp by (metis funpow_Suc_right)
qed (simp add: id_measure_preserving)

lemma T_integral_preserving:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. f(T x))" "(\<integral>x. f(T x) \<partial>M) = (\<integral>x. f x \<partial>M)"
using measure_preserving_preserves_integral[OF Tm assms] by auto

lemma Tn_integral_preserving:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. f((T^^n) x))" "(\<integral>x. f((T^^n) x) \<partial>M) = (\<integral>x. f x \<partial>M)"
using measure_preserving_preserves_integral[OF Tn_measure_preserving assms] by auto

lemma T_nn_integral_preserving:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f(T x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
using measure_preserving_preserves_nn_integral[OF Tm assms] by auto

lemma Tn_nn_integral_preserving:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+x. f((T^^n) x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
using measure_preserving_preserves_nn_integral[OF Tn_measure_preserving assms(1)] by auto

lemma mpt_power:
  "mpt M (T^^n)"
by (standard, simp_all add: Tn_quasi_measure_preserving Tn_measure_preserving)

lemma T_vrestr_same_emeasure:
  assumes "A \<in> sets M"
  shows "emeasure M (T--` A) = emeasure M A"
        "emeasure M ((T ^^ n)--`A) = emeasure M A"
by (auto simp add: vrestr_same_emeasure_f Tm Tn_measure_preserving assms)

lemma T_vrestr_same_measure:
  assumes "A \<in> sets M"
  shows "measure M (T--` A) = measure M A"
        "measure M ((T ^^ n)--`A) = measure M A"
by (auto simp add: vrestr_same_measure_f Tm Tn_measure_preserving assms)

lemma (in fmpt) fmpt_power:
  "fmpt M (T^^n)"
by (standard, simp_all add: Tn_quasi_measure_preserving Tn_measure_preserving)


end


subsection \<open>Birkhoff sums\<close>

text \<open>Birkhoff sums, obtained by summing a function along the orbit of a map, are basic objects
to be understood in ergodic theory.\<close>

context qmpt
begin

definition birkhoff_sum::"('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b"
  where "birkhoff_sum f n x = (\<Sum>i\<in>{..<n}. f((T^^i)x))"

lemma birkhoff_sum_meas [measurable]:
  fixes f::"'a \<Rightarrow> 'b::{second_countable_topology, topological_comm_monoid_add}"
  assumes "f \<in> borel_measurable M"
  shows "birkhoff_sum f n \<in> borel_measurable M"
proof -
  define F where "F = (\<lambda>i x. f((T^^i)x))"
  have "\<And>i. F i \<in> borel_measurable M" using assms F_def by auto
  then have "(\<lambda>x. (\<Sum>i<n. F i x)) \<in> borel_measurable M" by measurable
  then have "(\<lambda>x. birkhoff_sum f n x) \<in> borel_measurable M" unfolding birkhoff_sum_def F_def by auto
  then show ?thesis by simp
qed

lemma birkhoff_sum_1 [simp]:
  "birkhoff_sum f 0 x = 0"
  "birkhoff_sum f 1 x = f x"
  "birkhoff_sum f (Suc 0) x = f x"
unfolding birkhoff_sum_def by auto

lemma birkhoff_sum_cocycle:
  "birkhoff_sum f (n+m) x = birkhoff_sum f n x + birkhoff_sum f m ((T^^n)x)"
proof -
  have "(\<Sum>i<m. f ((T ^^ i) ((T ^^ n) x))) = (\<Sum>i<m. f ((T ^^ (i+n)) x))" by (simp add: funpow_add)
  also have "... = (\<Sum>j\<in>{n..< m+n}. f ((T ^^j) x))"
    using atLeast0LessThan sum.shift_bounds_nat_ivl[where ?g = "\<lambda>j. f((T^^j)x)" and ?k = n and ?m = 0 and ?n = m, symmetric]
          add.commute add.left_neutral by auto
  finally have *: "birkhoff_sum f m ((T^^n)x) = (\<Sum>j\<in>{n..< m+n}. f ((T ^^j) x))" unfolding birkhoff_sum_def by auto
  have "birkhoff_sum f (n+m) x = (\<Sum>i<n. f((T^^i)x)) + (\<Sum>i\<in>{n..<m+n}. f((T^^i)x))"
    unfolding birkhoff_sum_def by (metis add.commute add.right_neutral atLeast0LessThan le_add2 sum.atLeastLessThan_concat)
  also have "... = birkhoff_sum f n x + (\<Sum>i\<in>{n..<m+n}. f((T^^i)x))" unfolding birkhoff_sum_def by simp
  finally show ?thesis using * by simp
qed

lemma birkhoff_sum_mono:
  fixes f g::"_ \<Rightarrow> real"
  assumes "\<And>x. f x \<le> g x"
  shows "birkhoff_sum f n x \<le> birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: assms sum_mono)

lemma birkhoff_sum_abs:
  fixes f::"_ \<Rightarrow> 'b::real_normed_vector"
  shows "norm(birkhoff_sum f n x) \<le> birkhoff_sum (\<lambda>x. norm(f x)) n x"
unfolding birkhoff_sum_def using norm_sum by auto

lemma birkhoff_sum_add:
  "birkhoff_sum (\<lambda>x. f x + g x) n x = birkhoff_sum f n x + birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: sum.distrib)

lemma birkhoff_sum_diff:
  fixes f g::"_ \<Rightarrow> real"
  shows "birkhoff_sum (\<lambda>x. f x - g x) n x = birkhoff_sum f n x - birkhoff_sum g n x"
unfolding birkhoff_sum_def by (simp add: sum_subtractf)

lemma birkhoff_sum_cmult:
  fixes f::"_ \<Rightarrow> real"
  shows "birkhoff_sum (\<lambda>x. c * f x) n x = c * birkhoff_sum f n x"
unfolding birkhoff_sum_def by (simp add: sum_distrib_left)

lemma skew_product_real_iterates:
  fixes f::"'a \<Rightarrow> real"
  shows "((\<lambda>(x,y). (T x, y + f x))^^n) (x,y) = ((T^^n) x, y + birkhoff_sum f n x)"
apply (induction n)
apply (auto)
apply (metis (no_types, lifting) Suc_eq_plus1 birkhoff_sum_cocycle qmpt.birkhoff_sum_1(2) qmpt_axioms)
done

end

lemma (in mpt) birkhoff_sum_integral:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "integrable M f"
  shows "integrable M (birkhoff_sum f n)" "(\<integral>x. birkhoff_sum f n x \<partial>M) = n *\<^sub>R (\<integral>x. f x \<partial>M)"
proof -
  have a: "\<And>k. integrable M (\<lambda>x. f((T^^k) x))"
    using Tn_integral_preserving(1) assms by blast
  then have "integrable M (\<lambda>x. \<Sum>k\<in>{..<n}. f((T^^k) x))" by simp
  then have "integrable M (\<lambda>x. birkhoff_sum f n x)" unfolding birkhoff_sum_def by auto
  then show "integrable M (birkhoff_sum f n)" by simp

  have b: "\<And>k. (\<integral>x. f((T^^k)x) \<partial>M) = (\<integral>x. f x \<partial>M)"
    using Tn_integral_preserving(2) assms by blast
  have "(\<integral>x. birkhoff_sum f n x \<partial>M) = (\<integral>x. (\<Sum>k\<in>{..<n}. f((T^^k) x)) \<partial>M)"
    unfolding birkhoff_sum_def by blast
  also have "... = (\<Sum>k\<in>{..<n}. (\<integral>x. f((T^^k) x) \<partial>M))"
    by (rule Bochner_Integration.integral_sum, simp add: a)
  also have "... = (\<Sum>k\<in>{..<n}. (\<integral>x. f x \<partial>M))" using b by simp
  also have "... = n *\<^sub>R (\<integral>x. f x \<partial>M)" by (simp add: sum_constant_scaleR)
  finally show "(\<integral>x. birkhoff_sum f n x \<partial>M) = n *\<^sub>R (\<integral>x. f x \<partial>M)" by simp
qed

lemma (in mpt) birkhoff_sum_nn_integral:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable M" and pos: "\<And>x. f x \<ge> 0"
  shows "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) = n * (\<integral>\<^sup>+x. f x \<partial>M)"
proof -
  have [measurable]: "\<And>k. (\<lambda>x. f((T^^k)x)) \<in> borel_measurable M" by simp
  have posk: "\<And>k x. f((T^^k)x) \<ge> 0" using pos by simp
  have b: "\<And>k. (\<integral>\<^sup>+x. f((T^^k)x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
    using Tn_nn_integral_preserving assms by blast
  have "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>k\<in>{..<n}. f((T^^k) x)) \<partial>M)"
    unfolding birkhoff_sum_def by blast
  also have "... = (\<Sum>k\<in>{..<n}. (\<integral>\<^sup>+x. f((T^^k) x) \<partial>M))"
    by (rule nn_integral_sum, auto simp add: posk)
  also have "... = (\<Sum>k\<in>{..<n}. (\<integral>\<^sup>+x. f x \<partial>M))" using b by simp
  also have "... = n * (\<integral>\<^sup>+x. f x \<partial>M)" by simp
  finally show "(\<integral>\<^sup>+x. birkhoff_sum f n x \<partial>M) = n * (\<integral>\<^sup>+x. f x \<partial>M)" by simp
qed


subsection \<open>Inverse map\<close>

context qmpt begin

definition
  "invertible_qmpt \<equiv> (bij T \<and> inv T \<in> measurable M M)"

definition
  "Tinv \<equiv> inv T"

lemma T_Tinv_of_set:
  assumes "invertible_qmpt"
          "A \<in> sets M"
  shows "T-`(Tinv-`A \<inter> space M) \<inter> space M = A"
using assms sets.sets_into_space unfolding Tinv_def invertible_qmpt_def
apply (auto simp add: bij_betw_def)
using T_spaceM_stable(1) by blast

lemma Tinv_quasi_measure_preserving:
  assumes "invertible_qmpt"
  shows "Tinv \<in> quasi_measure_preserving M M"
proof (rule quasi_measure_preservingI, auto)
  fix A assume [measurable]: "A \<in> sets M" "Tinv -` A \<inter> space M \<in> null_sets M"
  then have "T-`(Tinv -` A \<inter> space M) \<inter> space M \<in> null_sets M"
    by (metis T_quasi_preserves_null2(1) null_sets.Int_space_eq2 vimage_restr_def)
  then show "A \<in> null_sets M"
    using T_Tinv_of_set[OF assms \<open>A \<in> sets M\<close>] by auto
next
  show [measurable]: "Tinv \<in> measurable M M"
    using assms unfolding Tinv_def invertible_qmpt_def by blast
  fix A assume [measurable]: "A \<in> sets M" "A \<in> null_sets M"
  then have "T-`(Tinv -` A \<inter> space M) \<inter> space M \<in> null_sets M"
    using T_Tinv_of_set[OF assms \<open>A \<in> sets M\<close>] by auto
  moreover have [measurable]: "Tinv-`A \<inter> space M \<in> sets M"
    by auto
  ultimately show "Tinv -` A \<inter> space M \<in> null_sets M"
    using T_meas T_quasi_preserves_null(1) vrestr_of_set by presburger
qed

lemma Tinv_qmpt:
  assumes "invertible_qmpt"
  shows "qmpt M Tinv"
unfolding qmpt_def qmpt_axioms_def using Tinv_quasi_measure_preserving[OF assms]
by (simp add: sigma_finite_measure_axioms)

end

lemma (in mpt) Tinv_measure_preserving:
  assumes "invertible_qmpt"
  shows "Tinv \<in> measure_preserving M M"
proof (rule measure_preservingI)
  show [measurable]: "Tinv \<in> measurable M M"
    using assms unfolding Tinv_def invertible_qmpt_def by blast
  fix A assume [measurable]: "A \<in> sets M"
  have "A = T-`(Tinv -` A \<inter> space M) \<inter> space M"
    using T_Tinv_of_set[OF assms \<open>A \<in> sets M\<close>] by auto
  then show "emeasure M (Tinv -` A \<inter> space M) = emeasure M A"
    by (metis T_vrestr_same_emeasure(1) \<open>A \<in> sets M\<close> \<open>Tinv \<in> M \<rightarrow>\<^sub>M M\<close> measurable_sets sets.Int_space_eq2 vimage_restr_def)
qed

lemma (in mpt) Tinv_mpt:
  assumes "invertible_qmpt"
  shows "mpt M Tinv"
unfolding mpt_def mpt_axioms_def using Tinv_qmpt[OF assms] Tinv_measure_preserving[OF assms] by auto

lemma (in fmpt) Tinv_fmpt:
  assumes "invertible_qmpt"
  shows "fmpt M Tinv"
unfolding fmpt_def using Tinv_mpt[OF assms] by (simp add: finite_measure_axioms)

lemma (in pmpt) Tinv_fmpt:
  assumes "invertible_qmpt"
  shows "pmpt M Tinv"
unfolding pmpt_def using Tinv_fmpt[OF assms] by (simp add: prob_space_axioms)


subsection \<open>Factors\<close>

text \<open>Factors of a system are quotients of this system, i.e., systems that can be obtained by
a projection, forgetting some part of the dynamics. It is sometimes possible to transfer a result
from a factor to the original system, making it possible to prove theorems by reduction to a
simpler situation.

The dual notion, extension, is equally important and useful. We only mention factors below, as
the results for extension readily follow by considering the original system as a factor of its
extension.

In this paragraph, we define factors both in the qmpt and mpt categories, and prove their basic
properties.
\<close>

definition (in qmpt) qmpt_factor::"('a \<Rightarrow> 'b) \<Rightarrow> ('b measure) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool"
  where "qmpt_factor proj M2 T2 =
    ((proj \<in> quasi_measure_preserving M M2) \<and> (AE x in M. proj (T x) = T2 (proj x)) \<and> qmpt M2 T2)"

lemma (in qmpt) qmpt_factorE:
  assumes "qmpt_factor proj M2 T2"
  shows "proj \<in> quasi_measure_preserving M M2"
        "AE x in M. proj (T x) = T2 (proj x)"
        "qmpt M2 T2"
using assms unfolding qmpt_factor_def by auto

lemma (in qmpt) qmpt_factor_iterates:
  assumes "qmpt_factor proj M2 T2"
  shows "AE x in M. \<forall>n. proj ((T^^n) x) = (T2^^n) (proj x)"
proof -
  have "AE x in M. \<forall>n. proj (T ((T^^n) x)) = T2 (proj ((T^^n) x))"
    by (rule T_AE_iterates[OF qmpt_factorE(2)[OF assms]])
  moreover
  {
    fix x assume "\<forall>n. proj (T ((T^^n) x)) = T2 (proj ((T^^n) x))"
    then have H: "proj (T ((T^^n) x)) = T2 (proj ((T^^n) x))" for n by auto
    have "proj ((T^^n) x) = (T2^^n) (proj x)" for n
      apply (induction n) using H by auto
    then have "\<forall>n. proj ((T^^n) x) = (T2^^n) (proj x)" by auto
  }
  ultimately show ?thesis by fast
qed

lemma (in qmpt) qmpt_factorI:
  assumes "proj \<in> quasi_measure_preserving M M2"
          "AE x in M. proj (T x) = T2 (proj x)"
          "qmpt M2 T2"
  shows "qmpt_factor proj M2 T2"
using assms unfolding qmpt_factor_def by auto

text \<open>When there is a quasi-measure-preserving projection, then the quotient map
automatically is quasi-measure-preserving. The same goes for measure-preservation below.\<close>

lemma (in qmpt) qmpt_factorI':
  assumes "proj \<in> quasi_measure_preserving M M2"
          "AE x in M. proj (T x) = T2 (proj x)"
          "sigma_finite_measure M2"
          "T2 \<in> measurable M2 M2"
  shows "qmpt_factor proj M2 T2"
proof -
  have [measurable]: "T \<in> measurable M M"
                     "T2 \<in> measurable M2 M2"
                     "proj \<in> measurable M M2"
    using assms(4) quasi_measure_preservingE(1)[OF assms(1)] by auto

  have *: "(T2 -` A \<inter> space M2 \<in> null_sets M2) = (A \<in> null_sets M2)" if "A \<in> sets M2" for A
  proof -
    obtain U where U: "\<And>x. x \<in> space M - U \<Longrightarrow> proj (T x) = T2 (proj x)" "U \<in> null_sets M"
      using AE_E3[OF assms(2)] by blast

    then have [measurable]: "U \<in> sets M" by auto
    have [measurable]: "A \<in> sets M2" using that by simp
    have e1: "(T-`(proj-`A \<inter> space M)) \<inter> space M = T-`(proj-`A) \<inter> space M"
      using subset_eq by auto
    have e2: "T-`(proj-`A) \<inter> space M - U = proj-`(T2-`A) \<inter> space M - U"
      using U(1) by auto
    have e3: "proj-`(T2-`A) \<inter> space M = proj-`(T2-`A \<inter> space M2) \<inter> space M"
      by (auto, meson \<open>proj \<in> M \<rightarrow>\<^sub>M M2\<close> measurable_space)

    have "A \<in> null_sets M2 \<longleftrightarrow> proj-`A \<inter> space M \<in> null_sets M"
      using quasi_measure_preservingE(2)[OF assms(1)] by simp
    also have "... \<longleftrightarrow> (T-`(proj-`A \<inter> space M)) \<inter> space M \<in> null_sets M"
      by (rule quasi_measure_preservingE(2)[OF Tqm, symmetric], auto)
    also have "... \<longleftrightarrow> T-`(proj-`A) \<inter> space M \<in> null_sets M"
      using e1 by simp
    also have "... \<longleftrightarrow> T-`(proj-`A) \<inter> space M - U \<in> null_sets M"
      using emeasure_Diff_null_set[OF \<open>U \<in> null_sets M\<close>] unfolding null_sets_def by auto
    also have "... \<longleftrightarrow> proj-`(T2-`A) \<inter> space M - U \<in> null_sets M"
      using e2 by simp
    also have "... \<longleftrightarrow> proj-`(T2-`A) \<inter> space M \<in> null_sets M"
      using emeasure_Diff_null_set[OF \<open>U \<in> null_sets M\<close>] unfolding null_sets_def by auto
    also have "... \<longleftrightarrow> proj-`(T2-`A \<inter> space M2) \<inter> space M \<in> null_sets M"
      using e3 by simp
    also have "... \<longleftrightarrow> T2-`A \<inter> space M2 \<in> null_sets M2"
      using quasi_measure_preservingE(2)[OF assms(1), of "T2-`A \<inter> space M2"] by simp
    finally show "T2-`A \<inter> space M2 \<in> null_sets M2 \<longleftrightarrow> A \<in> null_sets M2"
      by simp
  qed
  show ?thesis
    by (intro qmpt_factorI qmpt_I) (auto simp add: assms *)
qed

lemma qmpt_factor_compose:
  assumes "qmpt M1 T1"
          "qmpt.qmpt_factor M1 T1 proj1 M2 T2"
          "qmpt.qmpt_factor M2 T2 proj2 M3 T3"
  shows "qmpt.qmpt_factor M1 T1 (proj2 o proj1) M3 T3"
proof -
  have *: "proj1 \<in> quasi_measure_preserving M1 M2 \<Longrightarrow> AE x in M2. proj2 (T2 x) = T3 (proj2 x)
      \<Longrightarrow> (AE x in M1. proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x)))"
  proof -
    assume "AE y in M2. proj2 (T2 y) = T3 (proj2 y)"
           "proj1 \<in> quasi_measure_preserving M1 M2"
    then have "AE x in M1. proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      using quasi_measure_preserving_AE by auto
    moreover
    {
      fix x assume "proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      then have "proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
        by auto
    }
    ultimately show "AE x in M1. proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      by auto
  qed

  interpret I: qmpt M1 T1 using assms(1) by simp
  interpret J: qmpt M2 T2 using I.qmpt_factorE(3)[OF assms(2)] by simp
  show "I.qmpt_factor (proj2 o proj1) M3 T3"
    apply (rule I.qmpt_factorI)
    using I.qmpt_factorE[OF assms(2)] J.qmpt_factorE[OF assms(3)]
    by (auto simp add: quasi_measure_preserving_comp *)
qed

text \<open>The left shift on natural integers is a very natural dynamical system, that can be used to
model many systems as we see below. For invertible systems, one uses rather all the integers.\<close>

definition nat_left_shift::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "nat_left_shift x = (\<lambda>i. x (i+1))"

lemma nat_left_shift_continuous [intro, continuous_intros]:
  "continuous_on UNIV nat_left_shift"
by (rule continuous_on_coordinatewise_then_product, auto simp add: nat_left_shift_def)

lemma nat_left_shift_measurable [intro, measurable]:
  "nat_left_shift \<in> measurable borel borel"
by (rule borel_measurable_continuous_onI, auto)

definition int_left_shift::"(int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a)"
  where "int_left_shift x = (\<lambda>i. x (i+1))"

definition int_right_shift::"(int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a)"
  where "int_right_shift x = (\<lambda>i. x (i-1))"

lemma int_shift_continuous [intro, continuous_intros]:
  "continuous_on UNIV int_left_shift"
  "continuous_on UNIV int_right_shift"
apply (rule continuous_on_coordinatewise_then_product, auto simp add: int_left_shift_def)
apply (rule continuous_on_coordinatewise_then_product, auto simp add: int_right_shift_def)
done

lemma int_shift_measurable [intro, measurable]:
  "int_left_shift \<in> measurable borel borel"
  "int_right_shift \<in> measurable borel borel"
by (rule borel_measurable_continuous_onI, auto)+

lemma int_shift_bij:
  "bij int_left_shift" "inv int_left_shift = int_right_shift"
  "bij int_right_shift" "inv int_right_shift = int_left_shift"
proof -
  show "bij int_left_shift"
    apply (rule bij_betw_byWitness[where ?f' = "\<lambda>x. (\<lambda>i. x (i-1))"]) unfolding int_left_shift_def by auto
  show "inv int_left_shift = int_right_shift"
    apply (rule inv_equality)
    unfolding int_left_shift_def int_right_shift_def by auto
  show "bij int_right_shift"
    apply (rule bij_betw_byWitness[where ?f' = "\<lambda>x. (\<lambda>i. x (i+1))"]) unfolding int_right_shift_def by auto
  show "inv int_right_shift = int_left_shift"
    apply (rule inv_equality)
    unfolding int_left_shift_def int_right_shift_def by auto
qed

lemma (in qmpt) qmpt_factor_projection:
  fixes f::"'a \<Rightarrow> ('b::second_countable_topology)"
  assumes [measurable]: "f \<in> borel_measurable M"
      and "sigma_finite_measure (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
  shows "qmpt_factor (\<lambda>x. (\<lambda>n. f ((T^^n)x))) (distr M borel (\<lambda>x. (\<lambda>n. f ((T^^n)x)))) nat_left_shift"
proof (rule qmpt_factorI')
  have * [measurable]: "(\<lambda>x. (\<lambda>n. f ((T^^n)x))) \<in> borel_measurable M"
    using measurable_coordinatewise_then_product by measurable
  show "(\<lambda>x n. f ((T ^^ n) x)) \<in> quasi_measure_preserving M (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
    by (rule measure_preserving_is_quasi_measure_preserving[OF measure_preserving_distr'[OF *]])
  have "(\<lambda>n. f ((T ^^ n) (T x))) = nat_left_shift (\<lambda>n. f ((T ^^ n) x))" for x
    unfolding nat_left_shift_def by (auto simp add: funpow_swap1)
  then show "AE x in M. (\<lambda>n. f ((T ^^ n) (T x))) = nat_left_shift (\<lambda>n. f ((T ^^ n) x))"
    by simp
qed (auto simp add: assms(2))


text \<open>Let us now define factors of measure-preserving transformations, in the same way
as above.\<close>

definition (in mpt) mpt_factor::"('a \<Rightarrow> 'b) \<Rightarrow> ('b measure) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool"
  where "mpt_factor proj M2 T2 =
    ((proj \<in> measure_preserving M M2) \<and> (AE x in M. proj (T x) = T2 (proj x)) \<and> mpt M2 T2)"

lemma (in mpt) mpt_factor_is_qmpt_factor:
  assumes "mpt_factor proj M2 T2"
  shows "qmpt_factor proj M2 T2"
using assms unfolding mpt_factor_def qmpt_factor_def
by (simp add: measure_preserving_is_quasi_measure_preserving mpt_def)

lemma (in mpt) mpt_factorE:
  assumes "mpt_factor proj M2 T2"
  shows "proj \<in> measure_preserving M M2"
        "AE x in M. proj (T x) = T2 (proj x)"
        "mpt M2 T2"
using assms unfolding mpt_factor_def by auto

lemma (in mpt) mpt_factorI:
  assumes "proj \<in> measure_preserving M M2"
          "AE x in M. proj (T x) = T2 (proj x)"
          "mpt M2 T2"
  shows "mpt_factor proj M2 T2"
using assms unfolding mpt_factor_def by auto

text \<open>When there is a measure-preserving projection commuting with the dynamics, and the
dynamics above preserves the measure, then so does the dynamics below.\<close>

lemma (in mpt) mpt_factorI':
  assumes "proj \<in> measure_preserving M M2"
          "AE x in M. proj (T x) = T2 (proj x)"
          "sigma_finite_measure M2"
          "T2 \<in> measurable M2 M2"
  shows "mpt_factor proj M2 T2"
proof -
  have [measurable]: "T \<in> measurable M M"
                     "T2 \<in> measurable M2 M2"
                     "proj \<in> measurable M M2"
    using assms(4) measure_preservingE(1)[OF assms(1)] by auto

  have *: "emeasure M2 (T2 -` A \<inter> space M2) = emeasure M2 A" if "A \<in> sets M2" for A
  proof -
    obtain U where U: "\<And>x. x \<in> space M - U \<Longrightarrow> proj (T x) = T2 (proj x)" "U \<in> null_sets M"
      using AE_E3[OF assms(2)] by blast

    then have [measurable]: "U \<in> sets M" by auto
    have [measurable]: "A \<in> sets M2" using that by simp
    have e1: "(T-`(proj-`A \<inter> space M)) \<inter> space M = T-`(proj-`A) \<inter> space M"
      using subset_eq by auto
    have e2: "T-`(proj-`A) \<inter> space M - U = proj-`(T2-`A) \<inter> space M - U"
      using U(1) by auto
    have e3: "proj-`(T2-`A) \<inter> space M = proj-`(T2-`A \<inter> space M2) \<inter> space M"
      by (auto, meson \<open>proj \<in> M \<rightarrow>\<^sub>M M2\<close> measurable_space)

    have "emeasure M2 A = emeasure M (proj-`A \<inter> space M)"
      using measure_preservingE(2)[OF assms(1)] by simp
    also have "... = emeasure M (T-`(proj-`A \<inter> space M) \<inter> space M)"
      by (rule measure_preservingE(2)[OF Tm, symmetric], auto)
    also have "... = emeasure M (T-`(proj-`A) \<inter> space M)"
      using e1 by simp
    also have "... = emeasure M (T-`(proj-`A) \<inter> space M - U)"
      using emeasure_Diff_null_set[OF \<open>U \<in> null_sets M\<close>] by auto
    also have "... = emeasure M (proj-`(T2-`A) \<inter> space M - U)"
      using e2 by simp
    also have "... = emeasure M (proj-`(T2-`A) \<inter> space M)"
      using emeasure_Diff_null_set[OF \<open>U \<in> null_sets M\<close>] by auto
    also have "... = emeasure M (proj-`(T2-`A \<inter> space M2) \<inter> space M)"
      using e3 by simp
    also have "... = emeasure M2 (T2-`A \<inter> space M2)"
      using measure_preservingE(2)[OF assms(1), of "T2-`A \<inter> space M2"] by simp
    finally show "emeasure M2 (T2-`A \<inter> space M2) = emeasure M2 A"
      by simp
  qed
  show ?thesis
    by (intro mpt_factorI mpt_I) (auto simp add: assms *)
qed

lemma (in fmpt) mpt_factorI'':
  assumes "proj \<in> measure_preserving M M2"
          "AE x in M. proj (T x) = T2 (proj x)"
          "T2 \<in> measurable M2 M2"
  shows "mpt_factor proj M2 T2"
apply (rule mpt_factorI', auto simp add: assms)
using measure_preserving_finite_measure[OF assms(1)] finite_measure_axioms finite_measure_def by blast

lemma (in fmpt) fmpt_factor:
  assumes "mpt_factor proj M2 T2"
  shows "fmpt M2 T2"
unfolding fmpt_def using mpt_factorE(3)[OF assms]
measure_preserving_finite_measure[OF mpt_factorE(1)[OF assms]] finite_measure_axioms by auto

lemma (in pmpt) pmpt_factor:
  assumes "mpt_factor proj M2 T2"
  shows "pmpt M2 T2"
unfolding pmpt_def using fmpt_factor[OF assms]
measure_preserving_prob_space[OF mpt_factorE(1)[OF assms]] prob_space_axioms by auto

lemma mpt_factor_compose:
  assumes "mpt M1 T1"
          "mpt.mpt_factor M1 T1 proj1 M2 T2"
          "mpt.mpt_factor M2 T2 proj2 M3 T3"
  shows "mpt.mpt_factor M1 T1 (proj2 o proj1) M3 T3"
proof -
  have *: "proj1 \<in> measure_preserving M1 M2 \<Longrightarrow> AE x in M2. proj2 (T2 x) = T3 (proj2 x) \<Longrightarrow>
    (AE x in M1. proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x)))"
  proof -
    assume "AE y in M2. proj2 (T2 y) = T3 (proj2 y)"
           "proj1 \<in> measure_preserving M1 M2"
    then have "AE x in M1. proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      using quasi_measure_preserving_AE measure_preserving_is_quasi_measure_preserving by blast
    moreover
    {
      fix x assume "proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      then have "proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
        by auto
    }
    ultimately show "AE x in M1. proj1 (T1 x) = T2 (proj1 x) \<longrightarrow> proj2 (T2 (proj1 x)) = T3 (proj2 (proj1 x))"
      by auto
  qed

  interpret I: mpt M1 T1 using assms(1) by simp
  interpret J: mpt M2 T2 using I.mpt_factorE(3)[OF assms(2)] by simp
  show "I.mpt_factor (proj2 o proj1) M3 T3"
    apply (rule I.mpt_factorI)
    using I.mpt_factorE[OF assms(2)] J.mpt_factorE[OF assms(3)]
    by (auto simp add: measure_preserving_comp *)
qed

text \<open>Left shifts are naturally factors of finite measure preserving transformations.\<close>

lemma (in mpt) mpt_factor_projection:
  fixes f::"'a \<Rightarrow> ('b::second_countable_topology)"
  assumes [measurable]: "f \<in> borel_measurable M"
      and "sigma_finite_measure (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
  shows "mpt_factor (\<lambda>x. (\<lambda>n. f ((T^^n)x))) (distr M borel (\<lambda>x. (\<lambda>n. f ((T^^n)x)))) nat_left_shift"
proof (rule mpt_factorI')
  have * [measurable]: "(\<lambda>x. (\<lambda>n. f ((T^^n)x))) \<in> borel_measurable M"
    using measurable_coordinatewise_then_product by measurable
  show "(\<lambda>x n. f ((T ^^ n) x)) \<in> measure_preserving M (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
    by (rule measure_preserving_distr'[OF *])
  have "(\<lambda>n. f ((T ^^ n) (T x))) = nat_left_shift (\<lambda>n. f ((T ^^ n) x))" for x
    unfolding nat_left_shift_def by (auto simp add: funpow_swap1)
  then show "AE x in M. (\<lambda>n. f ((T ^^ n) (T x))) = nat_left_shift (\<lambda>n. f ((T ^^ n) x))"
    by simp
qed (auto simp add: assms(2))

lemma (in fmpt) fmpt_factor_projection:
  fixes f::"'a \<Rightarrow> ('b::second_countable_topology)"
  assumes [measurable]: "f \<in> borel_measurable M"
  shows "mpt_factor (\<lambda>x. (\<lambda>n. f ((T^^n)x))) (distr M borel (\<lambda>x. (\<lambda>n. f ((T^^n)x)))) nat_left_shift"
proof (rule mpt_factor_projection, simp add: assms)
  have * [measurable]: "(\<lambda>x. (\<lambda>n. f ((T^^n)x))) \<in> borel_measurable M"
    using measurable_coordinatewise_then_product by measurable
  have **: "(\<lambda>x n. f ((T ^^ n) x)) \<in> measure_preserving M (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
    by (rule measure_preserving_distr'[OF *])
  have a: "finite_measure (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
    using measure_preserving_finite_measure[OF **] finite_measure_axioms by blast
  then show "sigma_finite_measure (distr M borel (\<lambda>x n. f ((T ^^ n) x)))"
    by (simp add: finite_measure_def)
qed


subsection \<open>Natural extension\<close>

text \<open>Many probability preserving dynamical systems are not invertible, while invertibility is
often useful in proofs. The notion of natural extension is a solution to this problem: it shows that
(essentially) any system has an extension which is invertible.

This extension is constructed by considering the space of orbits indexed by integer numbers, with
the left shift acting on it. If one considers the orbits starting from time $-N$
(for some fixed $N$), then there is a natural measure on this space: such an orbit is
parameterized by its starting point at time $-N$, hence one may use the original measure on this
point. The invariance of the measure ensures that these measures are compatible with each other.
Their projective limit (when $N$ tends to infinity) is thus an invariant measure on the bilateral
shift. The shift with this measure is the desired extension of the original system.

There is a difficulty in the above argument: one needs to make sure that the projective limit of
a system of compatible measures is well defined. This requires some topological conditions on the
measures (they should be inner regular, i.e., the measure of any set should be approximated from
below by compact subsets -- this is automatic on polish spaces). The existence of projective limits
is proved in \verb+Projective_Limits.thy+ under the (sufficient) polish condition. We use this
theory, so we need the underlying space to be a polish space and the measure to be a Borel
measure. This is almost completely satisfactory.

What is not completely satisfactory is that the completion of a Borel measure on a polish space
(i.e., we add all subsets of sets of measure $0$ into the sigma algebra) does not fit into this
setting, while this is an important framework in dynamical systems. It would readily follow
once \verb+Projective_Limits.thy+ is extended to the more general inner regularity setting
(the completion of a Borel measure on a polish space is always inner regular).
\<close>

locale polish_pmpt = pmpt "M::('a::polish_space measure)" T for M T
  + assumes M_eq_borel: "sets M = sets borel"
begin

definition natural_extension_map
  where "natural_extension_map = (int_left_shift::((int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a)))"

definition natural_extension_measure::"(int \<Rightarrow> 'a) measure"
  where "natural_extension_measure =
    projective_family.lim UNIV (\<lambda>I. distr M (\<Pi>\<^sub>M i\<in>I. borel) (\<lambda>x. (\<lambda>i\<in>I. (T^^(nat(i- Min I))) x))) (\<lambda>i. borel)"

definition natural_extension_proj::"(int \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "natural_extension_proj = (\<lambda>x. x 0)"

theorem natural_extension:
  "pmpt natural_extension_measure natural_extension_map"
  "qmpt.invertible_qmpt natural_extension_measure natural_extension_map"
  "mpt.mpt_factor natural_extension_measure natural_extension_map natural_extension_proj M T"
proof -
  define P::"int set \<Rightarrow> (int \<Rightarrow> 'a) measure" where
    "P = (\<lambda>I. distr M (\<Pi>\<^sub>M i\<in>I. borel) (\<lambda>x. (\<lambda>i\<in>I. (T^^(nat(i- Min I))) x)))"
  have [measurable]: "(T^^n) \<in> measurable M borel" for n
    using M_eq_borel by auto

  interpret polish_projective UNIV P
  unfolding polish_projective_def projective_family_def
  proof (auto)
    show "prob_space (P I)" if "finite I" for I unfolding P_def by (rule prob_space_distr, auto)
    fix J H::"int set" assume "J \<subseteq> H" "finite H"
    then have "H \<inter> J = J" by blast

    have "((\<lambda>f. restrict f J) o (\<lambda>x. (\<lambda>i\<in>H. (T^^(nat(i- Min H))) x))) x
        = ((\<lambda>x. (\<lambda>i\<in>J. (T^^(nat(i- Min J))) x)) o (T^^(nat(Min J - Min H)))) x" for x
    proof -
      have "nat(i- Min H) = nat(i- Min J) + nat(Min J - Min H)" if "i \<in> J" for i
      proof -
        have "finite J" using \<open>J \<subseteq> H\<close> \<open>finite H\<close> finite_subset by auto
        then have "Min J \<in> J" using Min_in \<open>i \<in> J\<close> by auto
        then have "Min J \<in> H" using \<open>J \<subseteq> H\<close> by blast
        then have "Min H \<le> Min J" using Min.coboundedI[OF \<open>finite H\<close>] by auto
        moreover have "Min J \<le> i" using Min.coboundedI[OF \<open>finite J\<close> \<open>i \<in> J\<close>] by auto
        ultimately show ?thesis by auto
      qed
      then show ?thesis
        unfolding comp_def by (auto simp add: \<open>H \<inter> J = J\<close> funpow_add)
    qed
    then have *: "(\<lambda>f. restrict f J) o (\<lambda>x. (\<lambda>i\<in>H. (T^^(nat(i- Min H))) x))
        = (\<lambda>x. (\<lambda>i\<in>J. (T^^(nat(i- Min J))) x)) o (T^^(nat(Min J - Min H)))"
      by auto

    have "distr (P H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J)
            = distr M (\<Pi>\<^sub>M i\<in>J. borel) ((\<lambda>f. restrict f J) o (\<lambda>x. (\<lambda>i\<in>H. (T^^(nat(i- Min H))) x)))"
      unfolding P_def by (rule distr_distr, auto simp add: \<open>J \<subseteq> H\<close> measurable_restrict_subset)
    also have "... = distr M (\<Pi>\<^sub>M i\<in>J. borel) ((\<lambda>x. (\<lambda>i\<in>J. (T^^(nat(i- Min J))) x)) o (T^^(nat(Min J - Min H))))"
      using * by auto
    also have "... = distr (distr M M (T^^(nat(Min J - Min H)))) (\<Pi>\<^sub>M i\<in>J. borel) (\<lambda>x. (\<lambda>i\<in>J. (T^^(nat(i- Min J))) x))"
      by (rule distr_distr[symmetric], auto)
    also have "... = distr M (\<Pi>\<^sub>M i\<in>J. borel) (\<lambda>x. (\<lambda>i\<in>J. (T^^(nat(i- Min J))) x))"
      using measure_preserving_distr[OF Tn_measure_preserving] by auto
    also have "... = P J"
      unfolding P_def by auto
    finally show "P J = distr (P H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
      by simp
  qed

  have S: "sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) = sets (borel::(int \<Rightarrow> 'a) measure)"
    by (rule sets_PiM_equal_borel)
  have "natural_extension_measure = lim"
    unfolding natural_extension_measure_def P_def by simp
  have "measurable lim lim = measurable borel borel"
    by (rule measurable_cong_sets, auto simp add: S)
  then have [measurable]: "int_left_shift \<in> measurable lim lim" "int_right_shift \<in> measurable lim lim"
    using int_shift_measurable by fast+
  have [simp]: "space lim = UNIV"
    unfolding space_lim space_PiM space_borel by auto

  show "pmpt natural_extension_measure natural_extension_map"
  proof (rule pmpt_I)
    show "prob_space natural_extension_measure"
      unfolding \<open>natural_extension_measure = lim\<close> by (simp add: P.prob_space_axioms)
    show "natural_extension_map \<in> measurable natural_extension_measure natural_extension_measure"
      unfolding natural_extension_map_def \<open>natural_extension_measure = lim\<close> by simp

    define E where "E = {(\<Pi>\<^sub>E i\<in>UNIV. X i) |X::(int \<Rightarrow> 'a set). (\<forall>i. X i \<in> sets borel) \<and> finite {i. X i \<noteq> UNIV}}"
    have "lim = distr lim lim int_left_shift"
    proof (rule measure_eqI_generator_eq[of E UNIV, where ?A = "\<lambda>_. UNIV"])
      show "sets lim = sigma_sets UNIV E"
        unfolding E_def using sets_PiM_finite[of "UNIV::int set" "\<lambda>_. (borel::'a measure)"]
        by (simp add: PiE_def)
      moreover have "sets (distr lim lim int_left_shift) = sets lim" by auto
      ultimately show "sets (distr lim lim int_left_shift) = sigma_sets UNIV E" by simp

      show "emeasure lim UNIV \<noteq> \<infinity>" by (simp add: P.prob_space_axioms)
      have "UNIV = (\<Pi>\<^sub>E i\<in>(UNIV::int set). (UNIV::'a set))" by (simp add: PiE_def)
      moreover have "... \<in> E" unfolding E_def by auto
      ultimately show "range (\<lambda>(i::nat). (UNIV::(int \<Rightarrow> 'a) set)) \<subseteq> E"
        by auto

      show "Int_stable E"
      proof (rule Int_stableI)
        fix U V assume "U \<in> E" "V \<in> E"
        then obtain X Y where H: "U = (\<Pi>\<^sub>E i\<in>UNIV. X i)" "\<And>i. X i \<in> sets borel" "finite {i. X i \<noteq> UNIV}"
                                 "V = (\<Pi>\<^sub>E i\<in>UNIV. Y i)" "\<And>i. Y i \<in> sets borel" "finite {i. Y i \<noteq> UNIV}"
          unfolding E_def by blast
        define Z where "Z = (\<lambda>i. X i \<inter> Y i)"
        have "{i. Z i \<noteq> UNIV} \<subseteq> {i. X i \<noteq> UNIV} \<union> {i. Y i \<noteq> UNIV}"
          unfolding Z_def by auto
        then have "finite {i. Z i \<noteq> UNIV}"
          using H(3) H(6) finite_subset by auto
        moreover have "U \<inter> V = (\<Pi>\<^sub>E i\<in>UNIV. Z i)"
          unfolding Z_def using H(1) H(4) by auto
        moreover have "\<And>i. Z i \<in> sets borel"
          unfolding Z_def using H(2) H(5) by auto
        ultimately show "U \<inter> V \<in> E"
          unfolding E_def by auto
      qed

      fix U assume "U \<in> E"
      then obtain X where H [measurable]: "U = (\<Pi>\<^sub>E i\<in>UNIV. X i)" "\<And>i. X i \<in> sets borel" "finite {i. X i \<noteq> UNIV}"
        unfolding E_def by blast
      define I where "I = {i. X i \<noteq> UNIV}"
      have [simp]: "finite I" unfolding I_def using H(3) by auto
      have [measurable]: "(\<Pi>\<^sub>E i\<in>I. X i) \<in> sets (Pi\<^sub>M I (\<lambda>i. borel))" using H(2) by simp
      have *: "U = emb UNIV I (\<Pi>\<^sub>E i\<in>I. X i)"
        unfolding H(1) I_def prod_emb_def space_borel apply (auto simp add: PiE_def)
        by (metis (mono_tags, lifting) PiE UNIV_I mem_Collect_eq restrict_Pi_cancel)
      have "emeasure lim U = emeasure lim (int_left_shift-`U)"
      proof (cases "I = {}")
        case True
        then have "U = UNIV" unfolding H(1) I_def by auto
        then show ?thesis by auto
      next
        case False
        have "emeasure lim U = emeasure (P I) (\<Pi>\<^sub>E i\<in>I. X i)"
          unfolding * by (rule emeasure_lim_emb, auto)
        also have "... = emeasure M (((\<lambda>x. (\<lambda>i\<in>I. (T^^(nat(i- Min I))) x)))-`(\<Pi>\<^sub>E i\<in>I. X i) \<inter> space M)"
          unfolding P_def by (rule emeasure_distr, auto)
        finally have A: "emeasure lim U = emeasure M (((\<lambda>x. (\<lambda>i\<in>I. (T^^(nat(i- Min I))) x)))-`(\<Pi>\<^sub>E i\<in>I. X i) \<inter> space M)"
          by simp

        have i: "int_left_shift-`U = (\<Pi>\<^sub>E i\<in>UNIV. X (i-1))"
          unfolding H(1) apply (auto simp add: int_left_shift_def PiE_def)
          by (metis PiE UNIV_I diff_add_cancel, metis Pi_mem add.commute add_diff_cancel_left' iso_tuple_UNIV_I)
        define Im where "Im = {i. X (i-1) \<noteq> UNIV}"
        have "Im = (\<lambda>i. i+1)`I"
          unfolding I_def Im_def using image_iff by (auto, fastforce)
        then have [simp]: "finite Im" by auto
        have *: "int_left_shift-`U = emb UNIV Im (\<Pi>\<^sub>E i\<in>Im. X (i-1))"
          unfolding i Im_def prod_emb_def space_borel apply (auto simp add: PiE_def)
          by (metis (mono_tags, lifting) PiE UNIV_I mem_Collect_eq restrict_Pi_cancel)
        have "emeasure lim (int_left_shift-`U) = emeasure (P Im) (\<Pi>\<^sub>E i\<in>Im. X (i-1))"
          unfolding * by (rule emeasure_lim_emb, auto)
        also have "... = emeasure M (((\<lambda>x. (\<lambda>i\<in>Im. (T^^(nat(i- Min Im))) x)))-`(\<Pi>\<^sub>E i\<in>Im. X (i-1)) \<inter> space M)"
          unfolding P_def by (rule emeasure_distr, auto)
        finally have B: "emeasure lim (int_left_shift-`U) = emeasure M (((\<lambda>x. (\<lambda>i\<in>Im. (T^^(nat(i- Min Im))) x)))-`(\<Pi>\<^sub>E i\<in>Im. X (i-1)) \<inter> space M)"
          by simp

        have "Min Im = Min I + 1" unfolding \<open>Im = (\<lambda>i. i+1)`I\<close>
          by (rule mono_Min_commute[symmetric], auto simp add: False monoI)
        have "((\<lambda>x. (\<lambda>i\<in>Im. (T^^(nat(i- Min Im))) x)))-`(\<Pi>\<^sub>E i\<in>Im. X (i-1)) = ((\<lambda>x. (\<lambda>i\<in>I. (T^^(nat(i- Min I))) x)))-`(\<Pi>\<^sub>E i\<in>I. X i)"
          unfolding \<open>Min Im = Min I + 1\<close> unfolding \<open>Im = (\<lambda>i. i+1)`I\<close> by (auto simp add: Pi_iff)
        then show "emeasure lim U = emeasure lim (int_left_shift -` U)" using A B by auto
      qed
      also have "... = emeasure lim (int_left_shift-`U \<inter> space lim)"
        unfolding \<open>space lim = UNIV\<close> by auto
      also have "... = emeasure (distr lim lim int_left_shift) U"
        apply (rule emeasure_distr[symmetric], auto) using * by auto
      finally show "emeasure lim U = emeasure (distr lim lim int_left_shift) U"
        by simp
    qed (auto)

    fix U assume "U \<in> sets natural_extension_measure"
    then have [measurable]: "U \<in> sets lim" using \<open>natural_extension_measure = lim\<close> by simp
    have "emeasure natural_extension_measure (natural_extension_map -` U \<inter> space natural_extension_measure)
          = emeasure lim (int_left_shift-`U \<inter> space lim)"
      unfolding \<open>natural_extension_measure = lim\<close> natural_extension_map_def by simp
    also have "... = emeasure (distr lim lim int_left_shift) U"
      apply (rule emeasure_distr[symmetric], auto) using \<open>U \<in> P.events\<close> by auto
    also have "... = emeasure lim U"
      using \<open>lim = distr lim lim int_left_shift\<close> by simp
    also have "... = emeasure natural_extension_measure U"
      using \<open>natural_extension_measure = lim\<close> by simp
    finally show "emeasure natural_extension_measure (natural_extension_map -` U \<inter> space natural_extension_measure)
                  = emeasure natural_extension_measure U"
      by simp
  qed
  then interpret I: pmpt natural_extension_measure natural_extension_map by simp

  show "I.invertible_qmpt"
    unfolding I.invertible_qmpt_def unfolding natural_extension_map_def \<open>natural_extension_measure = lim\<close>
    by (auto simp add: int_shift_bij)

  show "I.mpt_factor natural_extension_proj M T" unfolding I.mpt_factor_def
  proof (auto)
    show "mpt M T" by (simp add: mpt_axioms)
    show "natural_extension_proj \<in> measure_preserving natural_extension_measure M"
    unfolding \<open>natural_extension_measure = lim\<close>
    proof
      have *: "measurable lim M = measurable borel borel"
        apply (rule measurable_cong_sets) using sets_PiM_equal_borel M_eq_borel by auto
      show "natural_extension_proj \<in> measurable lim M"
        unfolding * natural_extension_proj_def by auto

      fix U assume [measurable]: "U \<in> sets M"
      have *: "(((\<lambda>x. \<lambda>i\<in>{0}. (T ^^ nat (i - Min {0})) x))-` ({0} \<rightarrow>\<^sub>E U) \<inter> space M) = U"
        using sets.sets_into_space[OF \<open>U \<in> sets M\<close>] by auto

      have "natural_extension_proj-`U \<inter> space lim = emb UNIV {0} (\<Pi>\<^sub>E i\<in>{0}. U)"
        unfolding \<open>space lim = UNIV\<close> natural_extension_proj_def prod_emb_def by (auto simp add: PiE_iff)
      then have "emeasure lim (natural_extension_proj-`U \<inter> space lim) = emeasure lim (emb UNIV {0} (\<Pi>\<^sub>E i\<in>{0}. U))"
        by simp
      also have "... = emeasure (P {0}) (\<Pi>\<^sub>E i\<in>{0}. U)"
        apply (rule emeasure_lim_emb, auto) using \<open>U \<in> sets M\<close> M_eq_borel by auto
      also have "... = emeasure M (((\<lambda>x. \<lambda>i\<in>{0}. (T ^^ nat (i - Min {0})) x))-` ({0} \<rightarrow>\<^sub>E U) \<inter> space M)"
        unfolding P_def apply (rule emeasure_distr) using \<open>U \<in> sets M\<close> M_eq_borel by auto
      also have "... = emeasure M U"
        using * by simp
      finally show "emeasure lim (natural_extension_proj-`U \<inter> space lim) = emeasure M U" by simp
    qed

    define U::"(int \<Rightarrow> 'a) set" where "U = {x \<in> space (Pi\<^sub>M {0, 1} (\<lambda>i. borel)). x 1 = T (x 0)}"
    have *: "((\<lambda>x. \<lambda>i\<in>{0, 1}. (T ^^ nat (i - Min {0, 1})) x))-` U \<inter> space M = space M"
      unfolding U_def space_PiM space_borel by auto
    have [measurable]: "T \<in> measurable borel borel"
      using M_eq_borel by auto
    have [measurable]: "U \<in> sets (Pi\<^sub>M {0, 1} (\<lambda>i. borel))"
      unfolding U_def by (rule measurable_equality_set, auto)
    have "emeasure natural_extension_measure (emb UNIV {0, 1} U) = emeasure (P {0, 1}) U"
      unfolding \<open>natural_extension_measure = lim\<close> by (rule emeasure_lim_emb, auto)
    also have "... = emeasure M (((\<lambda>x. \<lambda>i\<in>{0, 1}. (T ^^ nat (i - Min {0, 1})) x))-` U \<inter> space M)"
      unfolding P_def by (rule emeasure_distr, auto)
    also have "... = emeasure M (space M)"
      using * by simp
    also have "... = 1" by (simp add: emeasure_space_1)
    finally have *: "emeasure natural_extension_measure (emb UNIV {0, 1} U) = 1" by simp
    have "AE x in natural_extension_measure. x \<in> emb UNIV {0, 1} U"
      apply (rule I.AE_prob_1) using * by (simp add: I.emeasure_eq_measure)
    moreover
    {
      fix x assume "x \<in> emb UNIV {0, 1} U"
      then have "x 1 = T (x 0)" unfolding prod_emb_def U_def by auto
      then have "natural_extension_proj (natural_extension_map x) = T (natural_extension_proj x)"
        unfolding natural_extension_proj_def natural_extension_map_def int_left_shift_def by auto
    }
    ultimately show "AE x in natural_extension_measure.
        natural_extension_proj (natural_extension_map x) = T (natural_extension_proj x)"
      by auto
  qed
qed

end

end (*of Measure_Preserving_Transformations.thy*)
