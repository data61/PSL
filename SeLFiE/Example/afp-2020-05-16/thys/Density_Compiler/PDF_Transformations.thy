(*
  Theory: PDF_Transformations.thy
  Author: Manuel Eberl

  Provides lemmas for transformations of measure spaces with a density.
*)

section \<open>Measure Space Transformations\<close>

theory PDF_Transformations
imports Density_Predicates
begin

lemma not_top_le_1_ennreal[simp]: "\<not> top \<le> (1::ennreal)"
  by (simp add: top_unique)

lemma range_int: "range int = {n. n \<ge> 0}"
proof (intro equalityI subsetI)
  fix n :: int assume "n \<in> {n. n \<ge> 0}"
  hence "n = int (nat n)" by simp
  thus "n \<in> range int" by blast
qed auto

lemma range_exp: "range (exp :: real \<Rightarrow> real) = {x. x > 0}"
proof (intro equalityI subsetI)
  fix x :: real assume "x \<in> {x. x > 0}"
  hence "x = exp (ln x)" by simp
  thus "x \<in> range exp" by blast
qed auto

lemma Int_stable_Icc: "Int_stable (range (\<lambda>(a, b). {a .. b::real}))"
  by (auto simp: Int_stable_def)

lemma distr_mult_real:
  assumes "c \<noteq> 0" "has_density M lborel (f :: real \<Rightarrow> ennreal)"
  shows "has_density (distr M borel ((*) c)) lborel (\<lambda>x. f (x / c) * inverse (abs c))"
            (is "has_density ?M' _ ?f'")
proof
  from assms(2) have "M = density lborel f" by (rule has_densityD)
  also from assms have Mf[measurable]: "f \<in> borel_measurable borel"
    by (auto dest: has_densityD)
  hence "distr (density lborel f) borel ((*) c) = density lborel ?f'" (is "?M1 = ?M2")
  proof (intro measure_eqI)
    fix X assume X[measurable]: "X \<in> sets (distr (density lborel f) borel ((*) c))"
    with assms have "emeasure ?M1 X = \<integral>\<^sup>+x. f x * indicator X (c * x) \<partial>lborel"
      by (subst emeasure_distr, simp, simp, subst emeasure_density)
         (auto dest: has_densityD intro!: measurable_sets_borel nn_integral_cong
               split: split_indicator)
    also from assms(1) and X have "... = \<integral>\<^sup>+x. ?f' x * indicator X x \<partial>lborel"
      apply (subst lborel_distr_mult'[of "inverse c"])
      apply simp
      apply (subst nn_integral_density)
      apply (simp_all add: nn_integral_distr field_simps)
      done
    also from X have "... = emeasure ?M2 X"
      by (subst emeasure_density) auto
    finally show "emeasure ?M1 X = emeasure ?M2 X" .
  qed simp
  finally show "distr M borel ((*) c) = density lborel ?f'" .
qed (insert assms, auto dest: has_densityD)

lemma distr_uminus_real:
  assumes "has_density M lborel (f :: real \<Rightarrow> ennreal)"
  shows "has_density (distr M borel uminus) lborel (\<lambda>x. f (- x))"
proof-
  from assms have "has_density (distr M borel ((*) (- 1))) lborel
                       (\<lambda>x. f (x / -1) * ennreal (inverse (abs (-1))))"
    by (intro distr_mult_real) simp_all
  also have "(*) (-1) = (uminus :: real \<Rightarrow> real)" by (intro ext) simp
  also have "(\<lambda>x. f (x / -1) * ennreal (inverse (abs (-1)))) = (\<lambda>x. f (-x))"
    by (intro ext) (simp add: one_ennreal_def[symmetric])
  finally show ?thesis .
qed

lemma distr_plus_real:
  assumes "has_density M lborel (f :: real \<Rightarrow> ennreal)"
  shows "has_density (distr M borel ((+) c)) lborel (\<lambda>x. f (x - c))"
proof
  from assms have "M = density lborel f" by (rule has_densityD)
  also from assms have Mf[measurable]: "f \<in> borel_measurable borel"
    by (auto dest: has_densityD)
  hence "distr (density lborel f) borel ((+) c) = density lborel (\<lambda>x. f (x - c))" (is "?M1 = ?M2")
  proof (intro measure_eqI)
    fix X assume X: "X \<in> sets (distr (density lborel f) borel ((+) c))"
    with assms have "emeasure ?M1 X = \<integral>\<^sup>+x. f x * indicator X (c + x) \<partial>lborel"
      by (subst emeasure_distr, simp, simp, subst emeasure_density)
         (auto dest: has_densityD intro!: measurable_sets_borel nn_integral_cong
               split: split_indicator)
    also from X have "... = \<integral>\<^sup>+x. f (x - c) * indicator X x \<partial>lborel"
      by (subst lborel_distr_plus[where c = "-c", symmetric], subst nn_integral_distr) auto
    also from X have "... = emeasure ?M2 X"
      by (subst emeasure_density)
         (auto simp: emeasure_density intro!: measurable_compose[OF borel_measurable_diff Mf])
    finally show "emeasure ?M1 X = emeasure ?M2 X" .
  qed simp
  finally show "distr M borel ((+) c) = density lborel (\<lambda>x. f (x - c))" .
qed (insert assms, auto dest: has_densityD)

lemma count_space_uminus:
  "count_space UNIV = distr (count_space UNIV) (count_space UNIV) (uminus :: ('a :: ring \<Rightarrow> _))"
proof (rule distr_bij_count_space[symmetric])
  show "bij (uminus :: 'a \<Rightarrow> 'a)"
    by (auto intro!: o_bij[where g=uminus])
qed

lemma count_space_plus:
  "count_space UNIV = distr (count_space UNIV) (count_space UNIV) ((+) (c :: ('a :: ring)))"
  by (rule distr_bij_count_space [symmetric]) simp

lemma distr_uminus_ring_count_space:
  assumes "has_density M (count_space UNIV) (f :: _ :: ring \<Rightarrow> ennreal)"
  shows "has_density (distr M (count_space UNIV) uminus) (count_space UNIV) (\<lambda>x. f (- x))"
proof
  from assms have "M = density (count_space UNIV) f" by (rule has_densityD)
  also have "distr (density (count_space UNIV) f) (count_space UNIV) uminus =
               density (count_space UNIV)(\<lambda>x. f (- x))" (is "?M1 = ?M2")
  proof (intro measure_eqI)
    fix X assume X: "X \<in> sets (distr (density (count_space UNIV) f) (count_space UNIV) uminus)"
    with assms have "emeasure ?M1 X = \<integral>\<^sup>+x. f x * indicator X (-x) \<partial>count_space UNIV"
      by (subst emeasure_distr, simp, simp, subst emeasure_density)
         (auto dest: has_densityD intro!: measurable_sets_borel nn_integral_cong
               split: split_indicator)
    also from X have "... = emeasure ?M2 X"
      by (subst count_space_uminus) (simp_all add: nn_integral_distr emeasure_density)
    finally show "emeasure ?M1 X = emeasure ?M2 X" .
  qed simp
  finally show "distr M (count_space UNIV) uminus = density (count_space UNIV) (\<lambda>x. f (- x))" .
qed (insert assms, auto dest: has_densityD)

lemma distr_plus_ring_count_space:
  assumes "has_density M (count_space UNIV) (f :: _ :: ring \<Rightarrow> ennreal)"
  shows "has_density (distr M (count_space UNIV) ((+) c)) (count_space UNIV) (\<lambda>x. f (x - c))"
proof
  from assms have "M = density (count_space UNIV) f" by (rule has_densityD)
  also have "distr (density (count_space UNIV) f) (count_space UNIV) ((+) c) =
               density (count_space UNIV)(\<lambda>x. f (x - c))" (is "?M1 = ?M2")
  proof (intro measure_eqI)
    fix X assume X: "X \<in> sets (distr (density (count_space UNIV) f) (count_space UNIV) ((+) c))"
    with assms have "emeasure ?M1 X = \<integral>\<^sup>+x. f x * indicator X (c + x) \<partial>count_space UNIV"
      by (subst emeasure_distr, simp, simp, subst emeasure_density)
         (auto dest: has_densityD intro!: measurable_sets_borel nn_integral_cong
               split: split_indicator)
    also from X have "... = emeasure ?M2 X"
      by (subst count_space_plus[of "-c"]) (simp_all add: nn_integral_distr emeasure_density)
    finally show "emeasure ?M1 X = emeasure ?M2 X" .
  qed simp
  finally show "distr M (count_space UNIV) ((+) c) = density (count_space UNIV) (\<lambda>x. f (x - c))" .
qed (insert assms, auto dest: has_densityD)


lemma subprob_density_distr_real_eq:
  assumes dens: "has_subprob_density M lborel f"
  assumes Mh: "h \<in> borel_measurable borel"
  assumes Mg: "g \<in> borel_measurable borel"
  assumes measure_eq:
    "\<And>a b. a \<le> b \<Longrightarrow> emeasure (distr (density lborel f) lborel h) {a..b} =
                          emeasure (density lborel g) {a..b}"
  shows "has_subprob_density (distr M borel (h :: real \<Rightarrow> real)) lborel g"
proof (rule has_subprob_densityI)
  from dens have sets_M: "sets M = sets borel" by (auto dest: has_subprob_densityD)
  have meas_M[simp]: "measurable M = measurable borel"
    by (intro ext, subst measurable_cong_sets[OF sets_M refl]) auto
  from Mh and dens show subprob_space: "subprob_space (distr M borel h)"
    by (intro subprob_space.subprob_space_distr) (auto dest: has_subprob_densityD)
  show "distr M borel h = density lborel g"
  proof (rule measure_eqI_generator_eq[OF Int_stable_Icc, of UNIV])
    {
      fix x :: real
      obtain n :: nat where "n > abs x" using reals_Archimedean2 by auto
      hence "\<exists>n::nat. x \<in> {-real n..real n}" by (intro exI[of _ n]) auto
    }
    thus "(\<Union>i::nat. {-real i..real i}) = UNIV" by blast
  next
    fix i :: nat
    from subprob_space have "emeasure (distr M borel h) {-real i..real i} \<le> 1"
      by (intro subprob_space.subprob_emeasure_le_1) (auto dest: has_subprob_densityD)
    thus "emeasure (distr M borel h) {- real i..real i} \<noteq> \<infinity>" by auto
  next
    fix X :: "real set" assume "X \<in> range (\<lambda>(a,b). {a..b})"
    then obtain a b where "X = {a..b}" by auto
    with dens have "emeasure (distr M lborel h) X = emeasure (density lborel g) X"
      by (cases "a \<le> b") (auto simp: measure_eq dest: has_subprob_densityD)
    also have "distr M lborel h = distr M borel h"
      by (rule distr_cong) auto
    finally show "emeasure (distr M borel h) X = emeasure (density lborel g) X" .
  qed (auto simp: borel_eq_atLeastAtMost)
qed (insert assms, auto)

lemma subprob_density_distr_real_exp:
  assumes dens: "has_subprob_density M lborel f"
  shows "has_subprob_density (distr M borel exp) lborel
           (\<lambda>x. if x > 0 then f (ln x) * ennreal (inverse x) else 0)"
           (is "has_subprob_density _ _ ?g")
proof (rule subprob_density_distr_real_eq[OF dens])
  from dens have [measurable]: "f \<in> borel_measurable borel"
    by (auto dest: has_subprob_densityD)

  have Mf: "(\<lambda>x. f (ln x) * ennreal (inverse x)) \<in> borel_measurable borel" by simp

  fix a b :: real assume "a \<le> b"

  let ?A = "\<lambda>i. {inverse (Suc i) :: real ..}"
  let ?M1 = "distr (density lborel f) lborel exp" and ?M2 = "density lborel ?g"
  {
    fix x :: real assume "\<forall>i. x < inverse (Suc i)"
    hence "x \<le> 0" by (intro tendsto_lowerbound[OF LIMSEQ_inverse_real_of_nat])
                     (auto intro!: always_eventually less_imp_le)
  }
  hence decomp: "{a..b} = {x\<in>{a..b}. x \<le> 0} \<union> (\<Union>i. ?A i \<inter> {a..b})" (is "_ = ?C \<union> ?D")
    by (auto simp: not_le)
  have inv_le: "\<And>x i. x \<ge> inverse (real (Suc i)) \<Longrightarrow> \<not>(x \<le> 0)"
    by (subst not_le, erule dual_order.strict_trans1, simp)
  hence "emeasure ?M1 {a..b} = emeasure ?M1 ?C + emeasure ?M1 ?D"
    by (subst decomp, intro plus_emeasure[symmetric]) auto
  also have "emeasure ?M1 ?C = 0" by (subst emeasure_distr) auto
  also have "0 = emeasure ?M2 ?C"
    by (subst emeasure_density, simp, simp, rule sym, subst nn_integral_0_iff) auto
  also have "emeasure ?M1 (\<Union>i. ?A i \<inter> {a..b}) = (SUP i. emeasure ?M1 (?A i \<inter> {a..b}))"
    by (rule SUP_emeasure_incseq[symmetric])
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "\<And>i. emeasure ?M1 (?A i \<inter> {a..b}) = emeasure ?M2 (?A i \<inter> {a..b})"
  proof (case_tac "inverse (Suc i) \<le> b")
    fix i assume True: "inverse (Suc i) \<le> b"
    let ?a = "inverse (Suc i)"
    from \<open>a \<le> b\<close> have A: "?A i \<inter> {a..b} = {max ?a a..b}" (is "?E = ?F") by auto
    hence "emeasure ?M1 ?E = emeasure ?M1 ?F" by simp
    also have "strict_mono_on ln {max (inverse (real (Suc i))) a..b}"
      by (rule strict_mono_onI, subst ln_less_cancel_iff)
         (auto dest: inv_le simp del: of_nat_Suc)
    with \<open>a \<le> b\<close> True dens
      have "emeasure ?M1 ?F = emeasure (density lborel (\<lambda>x. f (ln x) * inverse x)) ?F"
      by (intro emeasure_density_distr_interval)
         (auto simp: Mf not_less not_le range_exp dest: has_subprob_densityD dest!: inv_le
               intro!: DERIV_ln continuous_on_inverse continuous_on_id simp del: of_nat_Suc)
    also note A[symmetric]
    also have "emeasure (density lborel (\<lambda>x. f (ln x) * inverse x)) ?E = emeasure ?M2 ?E"
      by (subst (1 2) emeasure_density)
         (auto intro!: nn_integral_cong split: split_indicator dest!: inv_le simp del: of_nat_Suc)
    finally show "emeasure ?M1 (?A i \<inter> {a..b}) = emeasure ?M2 (?A i \<inter> {a..b})" .
  qed simp
  hence "(SUP i. emeasure ?M1 (?A i \<inter> {a..b})) = (SUP i. emeasure ?M2 (?A i \<inter> {a..b}))" by simp
  also have "... = emeasure ?M2 (\<Union>i. ?A i \<inter> {a..b})"
    by (rule SUP_emeasure_incseq)
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "emeasure ?M2 ?C + emeasure ?M2 ?D = emeasure ?M2 (?C \<union> ?D)"
    by (rule plus_emeasure) (auto dest: inv_le simp del: of_nat_Suc)
  also note decomp[symmetric]
  finally show "emeasure ?M1 {a..b} = emeasure ?M2 {a..b}" .
qed (insert dens, auto dest!: has_subprob_densityD(1))

lemma subprob_density_distr_real_inverse_aux:
  assumes dens: "has_subprob_density M lborel f"
  shows "has_subprob_density (distr M borel (\<lambda>x. - inverse x)) lborel
              (\<lambda>x. f (-inverse x) * ennreal (inverse (x * x)))"
           (is "has_subprob_density _ _ ?g")
proof (rule subprob_density_distr_real_eq[OF dens])
  from dens have Mf[measurable]: "f \<in> borel_measurable borel" by (auto dest: has_subprob_densityD)
  show Mg: "?g \<in> borel_measurable borel" by measurable

  have surj[simp]: "surj (\<lambda>x. - inverse x :: real)"
    by (intro surjI[of _ "\<lambda>x. - inverse x"]) (simp add: field_simps)
  fix a b :: real assume "a \<le> b"
  let ?A1 = "\<lambda>i. {..-inverse (Suc i) :: real}" and  ?A2 = "\<lambda>i. {inverse (Suc i) :: real ..}"
  let ?C = "if 0 \<in> {a..b} then {0} else {}"
  let ?M1 = "distr (density lborel f) lborel (\<lambda>x. - inverse x)" and ?M2 = "density lborel ?g"
  have inv_le: "\<And>x i. x \<ge> inverse (real (Suc i)) \<Longrightarrow> \<not>(x \<le> 0)"
    by (subst not_le, erule dual_order.strict_trans1, simp)
  have "\<And>x. x > 0 \<Longrightarrow> \<exists>i. x \<ge> inverse (Suc i)"
  proof (rule ccontr)
    fix x :: real assume "x > 0" "\<not>(\<exists>i. x \<ge> inverse (Suc i))"
    hence "x \<le> 0" by (intro tendsto_lowerbound[OF LIMSEQ_inverse_real_of_nat])
                      (auto intro!: always_eventually less_imp_le simp: not_le)
    with \<open>x > 0\<close> show False by simp
  qed
  hence A: "(\<Union>i. ?A2 i) = {0<..}" by (auto dest: inv_le simp del: of_nat_Suc)
  moreover have "\<And>x. x < 0 \<Longrightarrow> \<exists>i. x \<le> -inverse (Suc i)"
  proof (rule ccontr)
    fix x :: real assume "x < 0" "\<not>(\<exists>i. x \<le> -inverse (Suc i))"
    hence "x \<ge> 0"
      by (intro tendsto_upperbound, simp)
         (auto intro!: always_eventually less_imp_le LIMSEQ_inverse_real_of_nat_add_minus simp: not_le)
    with \<open>x < 0\<close> show False by simp
  qed
  hence B: "(\<Union>i. ?A1 i) = {..<0}"
    by (auto simp: le_minus_iff[of _ "inverse x" for x] dest!: inv_le simp del: of_nat_Suc)
  ultimately have C: "UNIV = (\<Union>i. ?A1 i) \<union> (\<Union>i. ?A2 i) \<union> {0}" by (subst A, subst B) force
  have UN_Int_distrib: "\<And>f A. (\<Union>i. f i) \<inter> A = (\<Union>i. f i \<inter> A)" by blast
  have decomp: "{a..b} = (\<Union>i. ?A1 i \<inter> {a..b}) \<union> (\<Union>i. ?A2 i \<inter> {a..b}) \<union> ?C" (is "_ = ?D \<union> ?E \<union> _")
    by (subst Int_UNIV_left[symmetric], simp only: C Int_Un_distrib2 UN_Int_distrib)
       (simp split: if_split)
  have "emeasure ?M1 {a..b} = emeasure ?M1 ?D + emeasure ?M1 ?E + emeasure ?M1 ?C"
    apply (subst decomp)
    apply (subst plus_emeasure[symmetric], simp, simp, simp)
    apply (subst plus_emeasure[symmetric])
    apply (auto dest!: inv_le simp: not_le le_minus_iff[of _ "inverse x" for x] simp del: of_nat_Suc)
    done
  also have "(\<lambda>x. - inverse x) -` {0 :: real} = {0}" by (auto simp: field_simps)
  hence "emeasure ?M1 ?C = 0"
    by (subst emeasure_distr)  (auto split: if_split simp: emeasure_density Mf)
  also have "emeasure ?M2 {0} = 0" by (simp add: emeasure_density)
  hence "0 = emeasure ?M2 ?C"
    by (rule_tac sym, rule_tac order.antisym, rule_tac order.trans, rule_tac emeasure_mono[of _ "{0}"]) simp_all
  also have "emeasure ?M1 (\<Union>i. ?A1 i \<inter> {a..b}) = (SUP i. emeasure ?M1 (?A1 i \<inter> {a..b}))"
    by (rule SUP_emeasure_incseq[symmetric])
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "\<And>i. emeasure ?M1 (?A1 i \<inter> {a..b}) = emeasure ?M2 (?A1 i \<inter> {a..b})"
  proof (case_tac "-inverse (Suc i) \<ge> a")
    fix i assume True: "-inverse (Suc i) \<ge> a"
    let ?a = "-inverse (Suc i)"
    from \<open>a \<le> b\<close> have A: "?A1 i \<inter> {a..b} = {a..min ?a b}" (is "?F = ?G") by auto
    hence "emeasure ?M1 ?F = emeasure ?M1 ?G" by simp
    also have "strict_mono_on (\<lambda>x. -inverse x) {a..min ?a b}"
      by (rule strict_mono_onI)
         (auto simp: le_minus_iff[of _ "inverse x" for x] dest!: inv_le simp del: of_nat_Suc)
    with \<open>a \<le> b\<close> True dens
      have "emeasure ?M1 ?G = emeasure ?M2 ?G"
      by (intro emeasure_density_distr_interval)
         (auto simp: Mf not_less dest: has_subprob_densityD inv_le
               intro!: derivative_eq_intros continuous_on_mult continuous_on_inverse continuous_on_id)
    also note A[symmetric]
    finally show "emeasure ?M1 (?A1 i \<inter> {a..b}) = emeasure ?M2 (?A1 i \<inter> {a..b})" .
  qed simp
  hence "(SUP i. emeasure ?M1 (?A1 i \<inter> {a..b})) = (SUP i. emeasure ?M2 (?A1 i \<inter> {a..b}))" by simp
  also have "... = emeasure ?M2 (\<Union>i. ?A1 i \<inter> {a..b})"
    by (rule SUP_emeasure_incseq)
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "emeasure ?M1 (\<Union>i. ?A2 i \<inter> {a..b}) = (SUP i. emeasure ?M1 (?A2 i \<inter> {a..b}))"
    by (rule SUP_emeasure_incseq[symmetric])
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "\<And>i. emeasure ?M1 (?A2 i \<inter> {a..b}) = emeasure ?M2 (?A2 i \<inter> {a..b})"
  proof (case_tac "inverse (Suc i) \<le> b")
    fix i assume True: "inverse (Suc i) \<le> b"
    let ?a = "inverse (Suc i)"
    from \<open>a \<le> b\<close> have A: "?A2 i \<inter> {a..b} = {max ?a a..b}" (is "?F = ?G") by auto
    hence "emeasure ?M1 ?F = emeasure ?M1 ?G" by simp
    also have "strict_mono_on (\<lambda>x. -inverse x) {max ?a a..b}"
      by (rule strict_mono_onI) (auto dest!: inv_le simp: not_le simp del: of_nat_Suc)
    with \<open>a \<le> b\<close> True dens
      have "emeasure ?M1 ?G = emeasure ?M2 ?G"
      by (intro emeasure_density_distr_interval)
         (auto simp: Mf not_less dest: has_subprob_densityD inv_le
               intro!: derivative_eq_intros continuous_on_mult continuous_on_inverse continuous_on_id)
    also note A[symmetric]
    finally show "emeasure ?M1 (?A2 i \<inter> {a..b}) = emeasure ?M2 (?A2 i \<inter> {a..b})" .
  qed simp
  hence "(SUP i. emeasure ?M1 (?A2 i \<inter> {a..b})) = (SUP i. emeasure ?M2 (?A2 i \<inter> {a..b}))" by simp
  also have "... = emeasure ?M2 (\<Union>i. ?A2 i \<inter> {a..b})"
    by (rule SUP_emeasure_incseq)
       (auto simp: incseq_def max_def not_le dest: order.strict_trans1)
  also have "emeasure ?M2 ?D + emeasure ?M2 ?E + emeasure ?M2 ?C = emeasure ?M2 {a..b}"
    apply (subst (4) decomp)
    apply (subst plus_emeasure, simp, simp)
    apply (auto dest!: inv_le simp: not_le le_minus_iff[of _ "inverse x" for x] simp del: of_nat_Suc)
    apply (subst plus_emeasure)
    apply (auto dest!: inv_le simp: not_le le_minus_iff[of _ "inverse x" for x])
    done
  finally show "emeasure ?M1 {a..b} = emeasure ?M2 {a..b}" .
qed simp

lemma subprob_density_distr_real_inverse:
  assumes dens: "has_subprob_density M lborel f"
  shows "has_subprob_density (distr M borel inverse) lborel (\<lambda>x. f (inverse x) * ennreal (inverse (x * x)))"
proof (unfold has_subprob_density_def, intro conjI)
  let ?g' = "(\<lambda>x. f (-inverse x) * ennreal (inverse (x * x)))"
  have prob: "has_subprob_density (distr M borel (\<lambda>x. -inverse x)) lborel ?g'"
    by (rule subprob_density_distr_real_inverse_aux[OF assms])
  from assms have sets_M: "sets M = sets borel" by (auto dest: has_subprob_densityD)
  have [simp]: "measurable M = measurable borel"
    by (intro ext, subst measurable_cong_sets[OF sets_M refl]) auto
  from prob have dens: "has_density (distr M lborel (\<lambda>x. -inverse x)) lborel
                 (\<lambda>x. f (-inverse x) * ennreal (inverse (x * x)))"
    unfolding has_subprob_density_def by (simp cong: distr_cong)
  from distr_uminus_real[OF this]
    show "has_density (distr M borel inverse) lborel
              (\<lambda>x. f (inverse x) * ennreal (inverse (x * x)))"
    by (simp add: distr_distr o_def cong: distr_cong)
  show "subprob_space (distr M borel inverse)"
    by (intro subprob_space.subprob_space_distr has_subprob_densityD[OF assms]) simp_all
qed

lemma distr_convolution_real:
  assumes "has_density M lborel (f :: (real \<times> real) \<Rightarrow> ennreal)"
  shows "has_density (distr M borel (case_prod (+))) lborel (\<lambda>z. \<integral>\<^sup>+x. f (x, z - x) \<partial>lborel)"
            (is "has_density ?M' _ ?f'")
proof
  from has_densityD[OF assms] have Mf[measurable]: "f \<in> borel_measurable borel" by simp
  show Mf': "(\<lambda>z. \<integral>\<^sup>+ x. f (x, z - x) \<partial>lborel) \<in> borel_measurable lborel" by measurable

  from assms have sets_M: "sets M = sets borel" by (auto dest: has_densityD)
  hence [simp]: "space M = UNIV" by (subst sets_eq_imp_space_eq[OF sets_M]) simp
  from sets_M have [simp]: "measurable M = measurable borel"
    by (intro ext measurable_cong_sets) simp_all
  have M_add: "case_prod (+) \<in> borel_measurable (borel :: (real \<times> real) measure)"
    by (simp add: borel_prod[symmetric])

  show "distr M borel (case_prod (+)) = density lborel ?f'"
  proof (rule measure_eqI)
    fix X :: "real set" assume X[measurable]: "X \<in> sets (distr M borel (case_prod (+)))"
    hence "emeasure (distr M borel (case_prod (+))) X = emeasure M ((\<lambda>(x, y). x + y) -` X)"
      by (simp_all add: M_add emeasure_distr)
    also from X have "... = \<integral>\<^sup>+z. f z * indicator ((\<lambda>(x, y). x + y) -` X) z \<partial>(lborel \<Otimes>\<^sub>M lborel)"
      by (simp add: emeasure_density has_densityD[OF assms]
                     measurable_sets_borel[OF M_add] lborel_prod)
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x, y) * indicator ((\<lambda>(x, y). x + y) -` X) (x,y) \<partial>lborel \<partial>lborel"
      apply (rule lborel.nn_integral_fst[symmetric])
      apply measurable
      apply (simp_all add: borel_prod)
      done
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x, y) * indicator ((\<lambda>(x, y). x + y) -` X) (x,y)
                          \<partial>distr lborel borel ((+) (-x)) \<partial>lborel"
      by (rule nn_integral_cong, subst lborel_distr_plus) simp
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+z. f (x, z-x) * indicator ((\<lambda>(x, y). x + y) -` X) (x, z-x)
                          \<partial>lborel \<partial>lborel"
      apply (rule nn_integral_cong)
      apply (subst nn_integral_distr)
      apply simp_all
      apply measurable
      apply (subst space_count_space)
      apply auto
      done
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+z. f (x, z-x) * indicator X z \<partial>lborel \<partial>lborel"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also have "... = \<integral>\<^sup>+z. \<integral>\<^sup>+x. f (x, z-x) * indicator X z \<partial>lborel \<partial>lborel" using X
      by (subst lborel_pair.Fubini')
         (simp_all add: pair_sigma_finite_def)
    also have "... = \<integral>\<^sup>+z. (\<integral>\<^sup>+x. f (x, z-x) \<partial>lborel) * indicator X z \<partial>lborel"
      by (rule nn_integral_cong) (simp split: split_indicator)
    also have "... = emeasure (density lborel ?f') X" using X
      by (simp add: emeasure_density)
    finally show "emeasure (distr M borel (case_prod (+))) X = emeasure (density lborel ?f') X" .
  qed (insert assms, auto dest: has_densityD)
qed simp_all

lemma distr_convolution_ring_count_space:
  assumes C: "countable (UNIV :: 'a set)"
  assumes "has_density M (count_space UNIV) (f :: (('a :: ring) \<times> 'a) \<Rightarrow> ennreal)"
  shows "has_density (distr M (count_space UNIV) (case_prod (+))) (count_space UNIV)
             (\<lambda>z. \<integral>\<^sup>+x. f (x, z - x) \<partial>count_space UNIV)"
            (is "has_density ?M' _ ?f'")
proof
  let ?CS = "count_space UNIV :: 'a measure" and ?CSP = "count_space UNIV :: ('a \<times> 'a) measure"
  show Mf': "(\<lambda>z. \<integral>\<^sup>+ x. f (x, z - x) \<partial>count_space UNIV) \<in> borel_measurable ?CS" by simp

  from assms have sets_M: "sets M = UNIV" and [simp]: "space M = UNIV"
    by (auto dest: has_densityD)
  from assms have [simp]: "measurable M = measurable (count_space UNIV)"
    by (intro ext measurable_cong_sets) (simp_all add: sets_M)

  interpret sigma_finite_measure ?CS by (rule sigma_finite_measure_count_space_countable[OF C])
  show "distr M ?CS (case_prod (+)) = density ?CS ?f'"
  proof (rule measure_eqI)
    fix X :: "'a set" assume X: "X \<in> sets (distr M ?CS (case_prod (+)))"
    hence "emeasure (distr M ?CS (case_prod (+))) X = emeasure M ((\<lambda>(x, y). x + y) -` X)"
      by (simp_all add: emeasure_distr)
    also from X have "... = \<integral>\<^sup>+z. f z * indicator ((\<lambda>(x, y). x + y) -` X) z \<partial>(?CS \<Otimes>\<^sub>M ?CS)"
      by (simp add: emeasure_density has_densityD[OF assms(2)]
                     sets_M pair_measure_countable C)
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x, y) * indicator ((\<lambda>(x, y). x + y) -` X) (x,y) \<partial>?CS \<partial>?CS"
      by (rule nn_integral_fst[symmetric]) (simp add: pair_measure_countable C)
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x, y) * indicator ((\<lambda>(x, y). x + y) -` X) (x,y)
                          \<partial>distr ?CS ?CS ((+) (-x)) \<partial>?CS"
      by (rule nn_integral_cong, subst count_space_plus) simp
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+z. f (x, z-x) * indicator ((\<lambda>(x, y). x + y) -` X) (x, z-x) \<partial>?CS \<partial>?CS"
      by (rule nn_integral_cong) (simp_all add: nn_integral_distr)
    also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+z. f (x, z-x) * indicator X z \<partial>?CS \<partial>?CS"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also have "... = \<integral>\<^sup>+z. \<integral>\<^sup>+x. f (x, z-x) * indicator X z \<partial>?CS \<partial>?CS" using X
      by (subst pair_sigma_finite.Fubini')
         (simp_all add: pair_sigma_finite_def sigma_finite_measure_count_space_countable
                        C pair_measure_countable)
    also have "... = \<integral>\<^sup>+z. (\<integral>\<^sup>+x. f (x, z-x) \<partial>?CS) * indicator X z \<partial>?CS"
      by (rule nn_integral_cong) (simp split: split_indicator)
    also have "... = emeasure (density ?CS ?f') X" using X by (simp add: emeasure_density)
    finally show "emeasure (distr M ?CS (case_prod (+))) X = emeasure (density ?CS ?f') X" .
  qed (insert assms, auto dest: has_densityD)
qed simp_all

end
