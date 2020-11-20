(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Continuous-time Markov chains\<close>

theory Continuous_Time_Markov_Chain
  imports Discrete_Time_Markov_Process Discrete_Time_Markov_Chain
begin

subsection \<open>Trace Operations: relate @{typ "('a \<times> real) stream"} and @{typ "real \<Rightarrow> 'a"}\<close>

partial_function (tailrec) trace_at :: "'a \<Rightarrow> (real \<times> 'a) stream \<Rightarrow> real \<Rightarrow> 'a"
where
  "trace_at s \<omega> j = (case \<omega> of (t', s')##\<omega> \<Rightarrow> if t' \<le> j then trace_at s' \<omega> j else s)"

lemma trace_at_simp[simp]: "trace_at s ((t', s')##\<omega>) j = (if t' \<le> j then trace_at s' \<omega> j else s)"
  by (subst trace_at.simps) simp

lemma trace_at_eq:
  "trace_at s \<omega> j = (case sfirst (\<lambda>x. j < fst (shd x)) \<omega> of \<infinity> \<Rightarrow> undefined | enat i \<Rightarrow> (s ## smap snd \<omega>) !! i)"
proof (split enat.split; safe)
  assume "sfirst (\<lambda>x. j < fst (shd x)) \<omega> = \<infinity>"
  with sfirst_finite[of "\<lambda>x. j < fst (shd x)" \<omega>]
  have "alw (\<lambda>x. fst (shd x) \<le> j) \<omega>"
    by (simp add: not_ev_iff not_less)
  then show "trace_at s \<omega> j = undefined"
    by (induction arbitrary: s \<omega> rule: trace_at.fixp_induct) (auto split: stream.split)
next
  show "sfirst (\<lambda>x. j < fst (shd x)) \<omega> = enat n \<Longrightarrow> trace_at s \<omega> j = (s ## smap snd \<omega>) !! n" for n
  proof (induction n arbitrary: s \<omega>)
    case 0 then show ?case
      by (subst trace_at.simps) (auto simp add: enat_0 sfirst_eq_0 split: stream.split)
  next
    case (Suc n) show ?case
      using sfirst.simps[of "\<lambda>x. j < fst (shd x)" \<omega>] Suc.prems Suc.IH[of "stl \<omega>" "snd (shd \<omega>)"]
      by (cases \<omega>) (auto simp add: eSuc_enat[symmetric] split: stream.split if_split_asm)
  qed
qed

lemma trace_at_shift: "trace_at s (smap (\<lambda>(t, s'). (t + t', s')) \<omega>) t = trace_at s \<omega> (t - t')"
  by (induction arbitrary: s \<omega> rule: trace_at.fixp_induct) (auto split: stream.split)

primcorec merge_at :: "(real \<times> 'a) stream \<Rightarrow> real \<Rightarrow> (real \<times> 'a) stream \<Rightarrow> (real \<times> 'a) stream"
where
  "merge_at \<omega> j \<omega>' = (case \<omega> of (t, s) ## \<omega> \<Rightarrow> if t \<le> j then (t, s)##merge_at \<omega> j \<omega>' else \<omega>')"

lemma merge_at_simp[simp]: "merge_at (x##\<omega>) j \<omega>' = (if fst x \<le> j then x##merge_at \<omega> j \<omega>' else \<omega>')"
  by (cases x) (subst merge_at.code; simp)

subsection \<open>Exponential Distribution\<close>

definition exponential :: "real \<Rightarrow> real measure"
where
  "exponential l = density lborel (exponential_density l)"

lemma space_exponential: "space (exponential l) = UNIV"
  by (simp add: exponential_def)

lemma sets_exponential[measurable_cong]: "sets (exponential l) = sets borel"
  by (simp add: exponential_def)

lemma prob_space_exponential: "0 < l \<Longrightarrow> prob_space (exponential l)"
  unfolding exponential_def by (intro prob_space_exponential_density)

lemma AE_exponential: "0 < l \<Longrightarrow> AE x in exponential l. 0 < x"
  unfolding exponential_def using AE_lborel_singleton[of 0] by (auto simp add: AE_density exponential_density_def)

lemma emeasure_exponential_Ioi_cutoff:
  assumes "0 < l"
  shows "emeasure (exponential l) {x <..} = exp (- (max 0 x) * l)"
proof -
  interpret prob_space "exponential l"
    unfolding exponential_def using \<open>0<l\<close> by (rule prob_space_exponential_density)
  have *: "prob {xa \<in> space (exponential l). max 0 x < xa} = exp (- max 0 x * l)"
    apply (rule exponential_distributedD_gt[OF _ _ \<open>0<l\<close>])
    apply (auto simp: exponential_def distributed_def)
    apply (subst (6) distr_id[symmetric])
    apply (subst (2) distr_cong)
    apply simp_all
    done
  have "emeasure (exponential l) {x <..} = emeasure (exponential l) {max 0 x <..}"
    using AE_exponential[OF \<open>0<l\<close>] by (intro emeasure_eq_AE) auto
  also have "\<dots> = exp (- (max 0 x) * l)"
    using * unfolding emeasure_eq_measure by (simp add: space_exponential greaterThan_def)
  finally show ?thesis .
qed

lemma emeasure_exponential_Ioi:
  "0 < l \<Longrightarrow> 0 \<le> x \<Longrightarrow> emeasure (exponential l) {x <..} = exp (- x * l)"
  using emeasure_exponential_Ioi_cutoff[of l x] by simp

lemma exponential_eq_stretch:
  assumes "0 < l"
  shows "exponential l = distr (exponential 1) borel (\<lambda>x. (1/l) * x)"
proof (intro measure_eqI)
  fix A assume "A \<in> sets (exponential l)"
  then have [measurable]: "A \<in> sets borel"
    by (simp add: sets_exponential)
  then have [measurable]: "(\<lambda>x. x / l) -` A \<in> sets borel"
    by (rule measurable_sets_borel[rotated]) simp
  have "emeasure (exponential l) A =
    (\<integral>\<^sup>+x. ennreal l * (indicator (((*) (1/l) -` A) \<inter> {0 ..}) (l * x) * ennreal (exp (- (l * x)))) \<partial>lborel)"
    using \<open>0 < l\<close>
    by (auto simp: ac_simps emeasure_distr exponential_def emeasure_density exponential_density_def
                   ennreal_mult zero_le_mult_iff
             intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+x. indicator (((*) (1/l) -` A) \<inter> {0 ..}) x * ennreal (exp (- x)) \<partial>lborel)"
    using \<open>0<l\<close>
    apply (subst nn_integral_stretch)
      apply (auto simp: nn_integral_cmult)
    apply (simp add: ennreal_mult[symmetric] mult.assoc[symmetric])
    done
  also have "\<dots> = emeasure (distr (exponential 1) borel (\<lambda>x. (1/l) * x)) A"
    by (auto simp add: emeasure_distr exponential_def emeasure_density exponential_density_def
        intro!: nn_integral_cong split: split_indicator)
  finally show "emeasure (exponential l) A = emeasure (distr (exponential 1) borel (\<lambda>x. (1/l) * x)) A" .
qed (simp add: sets_exponential)

lemma uniform_measure_exponential:
  assumes "0 < l" "0 \<le> t"
  shows "uniform_measure (exponential l) {t <..} = distr (exponential l) borel ((+) t)" (is "?L = ?R")
proof (rule measure_eqI_lessThan)
  fix x
  have "0 < emeasure (exponential l) {t<..}"
    unfolding emeasure_exponential_Ioi[OF assms] by simp
  with assms show "?L {x<..} < \<infinity>"
    by (simp add: ennreal_divide_eq_top_iff less_top[symmetric] lessThan_Int_lessThan
      emeasure_exponential_Ioi)
  have *: "((+) t -` {x<..} \<inter> space (exponential l)) = {x - t <..}"
    by (auto simp: space_exponential)
  show "?L {x<..} = ?R {x<..}"
    using assms by (simp add: lessThan_Int_lessThan emeasure_exponential_Ioi divide_ennreal
      emeasure_distr * emeasure_exponential_Ioi_cutoff exp_diff[symmetric] field_simps split: split_max)
qed (auto simp: sets_exponential)

lemma emeasure_PiM_exponential_Ioi_finite:
  assumes "J \<subseteq> I" "finite J" "\<And>i. i \<in> I \<Longrightarrow> 0 < R i" "0 \<le> x"
  shows "emeasure (\<Pi>\<^sub>M i\<in>I. exponential (R i)) (prod_emb I (\<lambda>i. exponential (R i)) J (\<Pi>\<^sub>E j\<in>J. {x<..})) = exp (- x * (\<Sum>i\<in>J. R i))"
proof (subst emeasure_PiM_emb)
  from assms show "(\<Prod>i\<in>J. emeasure (exponential (R i)) {x<..}) = ennreal (exp (- x * sum R J))"
    by (subst prod.cong[OF refl emeasure_exponential_Ioi])
       (auto simp add: prod_ennreal exp_sum sum_negf[symmetric] sum_distrib_left)
qed (insert assms, auto intro!: prob_space_exponential)

lemma emeasure_PiM_exponential_Ioi_sequence:
  assumes R: "summable R" "\<And>i. 0 < R i" "0 \<le> x"
  shows "emeasure (\<Pi>\<^sub>M i\<in>UNIV. exponential (R i)) (\<Pi> i\<in>UNIV. {x<..}) = exp (- x * suminf R)"
proof -
  let ?R = "\<lambda>i. exponential (R i)" let ?P = "\<Pi>\<^sub>M i\<in>UNIV. ?R i"
  let ?N = "\<lambda>n::nat. prod_emb UNIV ?R {..<n} (\<Pi>\<^sub>E i\<in>{..<n}. {x<..})"
  interpret prob_space ?P
    by (intro prob_space_PiM prob_space_exponential R)
  have "(\<Pi>\<^sub>M i\<in>UNIV. exponential (R i)) (\<Inter>n. ?N n) = (INF n. (\<Pi>\<^sub>M i\<in>UNIV. exponential (R i)) (?N n))"
    by (intro INF_emeasure_decseq[symmetric] decseq_emb_PiE) (auto simp: incseq_def)
  also have "\<dots> = (INF n. ennreal (exp (- x * (\<Sum>i<n. R i))))"
    using R by (intro INF_cong emeasure_PiM_exponential_Ioi_finite) auto
  also have "\<dots> = ennreal (exp (- x * (SUP n. (\<Sum>i<n. R i))))"
    using R
    by (subst continuous_at_Sup_antimono[where f="\<lambda>r. ennreal (exp (- x * r))"])
       (auto intro!: bdd_aboveI2[where M="\<Sum>i. R i"] sum_le_suminf summable_mult mult_left_mono
                     continuous_mult continuous_at_ennreal continuous_within_exp[THEN continuous_within_compose3] continuous_minus
             simp: less_imp_le antimono_def image_comp)
  also have "\<dots> = ennreal (exp (- x * (\<Sum>i. R i)))"
    using R by (subst suminf_eq_SUP_real) (auto simp: less_imp_le)
  also have "(\<Inter>n. ?N n) = (\<Pi> i\<in>UNIV. {x<..})"
    by (fastforce simp: prod_emb_def Pi_iff PiE_iff space_exponential)
  finally show ?thesis
    using R by simp
qed

lemma emeasure_PiM_exponential_Ioi_countable:
  assumes R: "J \<subseteq> I" "countable J" "\<And>i. i \<in> I \<Longrightarrow> 0 < R i" "0 \<le> x" and finite: "integrable (count_space J) R"
  shows "emeasure (\<Pi>\<^sub>M i\<in>I. exponential (R i)) (prod_emb I (\<lambda>i. exponential (R i)) J (\<Pi>\<^sub>E j\<in>J. {x<..})) =
    exp (- x * (LINT i|count_space J. R i))"
proof cases
  assume "finite J" with assms show ?thesis
    by (subst emeasure_PiM_exponential_Ioi_finite)
       (auto simp: lebesgue_integral_count_space_finite)
next
  assume "infinite J"
  let ?R = "\<lambda>i. exponential (R i)" let ?P = "\<Pi>\<^sub>M i\<in>I. ?R i"
  define f where "f = from_nat_into J"
  have J_eq: "J = range f" and f: "inj f" "f \<in> UNIV \<rightarrow> I"
    using from_nat_into_inj_infinite[of J] range_from_nat_into[of J] \<open>countable J\<close> \<open>infinite J\<close> \<open>J \<subseteq> I\<close>
    by (auto simp: inj_on_def f_def simp del: range_from_nat_into)
  have Bf: "bij_betw f UNIV J"
    unfolding J_eq using inj_on_imp_bij_betw[OF f(1)] .

  have summable_R: "summable (\<lambda>i. R (f i))"
    using finite unfolding integrable_bij_count_space[OF Bf, symmetric] integrable_count_space_nat_iff
    by (rule summable_norm_cancel)

  have "emeasure (\<Pi>\<^sub>M i\<in>UNIV. exponential (R (f i))) (\<Pi> i\<in>UNIV. {x<..}) = exp (- x * (\<Sum>i. R (f i)))"
    using finite assms unfolding J_eq by (intro emeasure_PiM_exponential_Ioi_sequence[OF summable_R]) auto
  also have "(\<Pi>\<^sub>M i\<in>UNIV. exponential (R (f i))) = distr ?P (\<Pi>\<^sub>M i\<in>UNIV. exponential (R (f i))) (\<lambda>\<omega>. \<lambda>i\<in>UNIV. \<omega> (f i))"
    using R by (intro distr_PiM_reindex[symmetric, OF _ f] prob_space_exponential) auto
  also have "\<dots> (\<Pi> i\<in>UNIV. {x<..}) = ?P ((\<lambda>\<omega>. \<lambda>i\<in>UNIV. \<omega> (f i)) -` (\<Pi> i\<in>UNIV. {x<..}) \<inter> space ?P)"
    using f(2) by (intro emeasure_distr infprod_in_sets) (auto simp: Pi_iff)
  also have "(\<lambda>\<omega>. \<lambda>i\<in>UNIV. \<omega> (f i)) -` (\<Pi> i\<in>UNIV. {x<..}) \<inter> space ?P = prod_emb I ?R J (\<Pi>\<^sub>E j\<in>J. {x<..})"
    by (auto simp: prod_emb_def space_PiM space_exponential Pi_iff J_eq)
  also have "(\<Sum>i. R (f i)) = (LINT i|count_space J. R i)"
    using finite
    by (subst integral_count_space_nat[symmetric])
       (auto simp: integrable_bij_count_space[OF Bf] integral_bij_count_space[OF Bf])
  finally show ?thesis .
qed

lemma AE_PiM_exponential_suminf_infty:
  fixes R :: "nat \<Rightarrow> real"
  assumes R: "\<And>n. 0 < R n" and finite: "(\<Sum>n. ennreal (1 / R n)) = top"
  shows "AE \<omega> in \<Pi>\<^sub>M n\<in>UNIV. exponential (R n). (\<Sum>n. ereal (\<omega> n)) = \<infinity>"
proof -
  let ?P = "\<Pi>\<^sub>M n\<in>UNIV. exponential (R n)"
  interpret prob_space "exponential (R n)" for n
    by (intro prob_space_exponential R)
  interpret product_prob_space "\<lambda>n. exponential (R n)" UNIV
    proof qed

  have AE_pos: "AE \<omega> in ?P. \<forall>i. 0 < \<omega> i"
    unfolding AE_all_countable by (intro AE_PiM_component allI prob_space_exponential R AE_exponential) simp

  have indep: "indep_vars (\<lambda>i. borel) (\<lambda>i x. x i) UNIV"
    using PiM_component
    apply (subst P.indep_vars_iff_distr_eq_PiM)
     apply (auto simp: restrict_UNIV distr_id2)
    apply (subst distr_id2)
     apply (intro sets_PiM_cong)
      apply (auto simp: sets_exponential cong: distr_cong)
    done

  have [simp]: "0 \<le> x + x * R i \<longleftrightarrow> 0 \<le> x" for x i
    using zero_le_mult_iff[of x "1 + R i"] R[of i] by (simp add: field_simps)

  have "(\<integral>\<^sup>+\<omega>. eexp (\<Sum>n. - ereal (\<omega> n)) \<partial>?P) = (\<integral>\<^sup>+\<omega>. (INF n. \<Prod>i<n. eexp (- ereal (\<omega> i))) \<partial>?P)"
  proof (intro nn_integral_cong_AE, use AE_pos in eventually_elim)
    fix \<omega> :: "nat \<Rightarrow> real" assume \<omega>: "\<forall>i. 0 < \<omega> i"
    show "eexp (\<Sum>n. - ereal (\<omega> n)) = (\<Sqinter>n. \<Prod>i<n. eexp (- ereal (\<omega> i)))"
    proof (rule LIMSEQ_unique[OF _ LIMSEQ_INF])
      show "(\<lambda>i. \<Prod>i<i. eexp (- ereal (\<omega> i))) \<longlonglongrightarrow> eexp (\<Sum>n. - ereal (\<omega> n))"
        using \<omega> by (intro eexp_suminf summable_minus_ereal summable_ereal_pos) (auto intro: less_imp_le)
      show "decseq (\<lambda>n. \<Prod>i<n. eexp (- ereal (\<omega> i)))"
        using \<omega> by (auto simp: decseq_def intro!: prod_mono3 intro: less_imp_le)
    qed
  qed
  also have "\<dots> = (INF n. (\<integral>\<^sup>+\<omega>. (\<Prod>i<n. eexp (- ereal (\<omega> i))) \<partial>?P))"
  proof (intro nn_integral_monotone_convergence_INF_AE')
    show "AE \<omega> in ?P. (\<Prod>i<Suc n. eexp (- ereal (\<omega> i))) \<le> (\<Prod>i<n. eexp (- ereal (\<omega> i)))" for n
      using AE_pos
    proof eventually_elim
      case (elim \<omega>)
      show ?case
        by (rule prod_mono3) (auto simp: elim le_less)
    qed
  qed (auto simp: less_top[symmetric])
  also have "\<dots> = (INF n. (\<Prod>i<n. (\<integral>\<^sup>+\<omega>. eexp (- ereal (\<omega> i)) \<partial>?P)))"
  proof (intro INF_cong refl indep_vars_nn_integral)
    show "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. eexp (- ereal (\<omega> i))) {..<n}" for n
    proof (rule indep_vars_compose2[of _ _ _ "\<lambda>i x. eexp(- ereal x)"])
      show "indep_vars (\<lambda>i. borel) (\<lambda>i x. x i) {..<n}"
        by (rule indep_vars_subset[OF indep]) auto
    qed auto
  qed auto
  also have "\<dots> = (INF n. (\<Prod>i<n. R i * (\<integral>\<^sup>+x. indicator {0 ..} ((1 + R i) * x) * ennreal (exp (- ((1 + R i) * x))) \<partial>lborel)))"
    by (subst product_nn_integral_component)
       (auto simp: field_simps exponential_def nn_integral_density ennreal_mult'[symmetric] ennreal_mult''[symmetric]
                   exponential_density_def exp_diff exp_minus nn_integral_cmult[symmetric]
             intro!: INF_cong prod.cong nn_integral_cong split: split_indicator)
  also have "\<dots> = (INF n. (\<Prod>i<n. ennreal (R i / (1 + R i))))"
  proof (intro INF_cong prod.cong refl)
    show "R i * (\<integral>\<^sup>+ x. indicator {0..} ((1 + R i) * x) * ennreal (exp (- ((1 + R i) * x))) \<partial>lborel) =
      ennreal (R i / (1 + R i))" for i
      using nn_intergal_power_times_exp_Ici[of 0] \<open>0 < R i\<close>
      by (subst nn_integral_stretch[where c="1 + R i"])
         (auto simp: mult.assoc[symmetric] ennreal_mult''[symmetric] less_imp_le mult.commute)
  qed
  also have "\<dots> = (INF n. ennreal (\<Prod>i<n. R i / (1 + R i)))"
    using R by (intro INF_cong refl prod_ennreal divide_nonneg_nonneg) (auto simp: less_imp_le)
  also have "\<dots> = (INF n. ennreal (inverse (\<Prod>i<n. (1 + R i) / R i)))"
    by (subst prod_inversef[symmetric]) simp_all
  also have "\<dots> = (INF n. inverse (ennreal (\<Prod>i<n. (1 + R i) / R i)))"
    using R by (subst inverse_ennreal) (auto intro!: prod_pos divide_pos_pos simp: add_pos_pos)
  also have "\<dots> = inverse (SUP n. ennreal (\<Prod>i<n. (1 + R i) / R i))"
    by (subst continuous_at_Sup_antimono [where f = inverse])
      (auto simp: antimono_def image_comp intro!: continuous_on_imp_continuous_within[OF continuous_on_inverse_ennreal'])
  also have "(SUP n. ennreal (\<Prod>i<n. (1 + R i) / R i)) = top"
  proof (cases "SUP n. ennreal (\<Prod>i<n. (1 + R i) / R i)")
    case (real r)
    have "(\<lambda>n. ennreal (\<Prod>i<n. (1 + R i) / R i)) \<longlonglongrightarrow> r"
      using R unfolding real(2)[symmetric]
      by (intro LIMSEQ_SUP monoI ennreal_leI prod_mono2) (auto intro!: divide_nonneg_nonneg add_nonneg_nonneg intro: less_imp_le)
    then have "(\<lambda>n. (\<Prod>i<n. (1 + R i) / R i)) \<longlonglongrightarrow> r"
      by (rule tendsto_ennrealD)
         (use R real in \<open>auto intro!: always_eventually prod_nonneg divide_nonneg_nonneg add_nonneg_nonneg intro: less_imp_le\<close>)
    moreover have "(1 + R i) / R i = 1 / R i + 1" for i
      using \<open>0 < R i\<close> by (auto simp: field_simps)
    ultimately have "convergent (\<lambda>n. \<Prod>i<n. 1 / R i + 1)"
      by (auto simp: convergent_def)
    then have "summable (\<lambda>i. 1 / R i)"
      using R by (subst summable_iff_convergent_prod) (auto intro: less_imp_le)
    moreover have "0 \<le> 1 / R i" for i
      using R by (auto simp: less_imp_le)
    ultimately show ?thesis
      using finite ennreal_suminf_neq_top[of "\<lambda>i. 1 / R i"] by blast
  qed
  finally have "(\<integral>\<^sup>+\<omega>. eexp (\<Sum>n. - ereal (\<omega> n)) \<partial>?P) = 0"
    by simp
  then have "AE \<omega> in ?P. eexp (\<Sum>n. - ereal (\<omega> n)) = 0"
    by (subst (asm) nn_integral_0_iff_AE) auto
  then show ?thesis
    using AE_pos
  proof eventually_elim
    show "(\<forall>i. 0 < \<omega> i) \<Longrightarrow> eexp (\<Sum>n. - ereal (\<omega> n)) = 0 \<Longrightarrow> (\<Sum>n. ereal (\<omega> n)) = \<infinity>" for \<omega>
      apply (auto simp del: uminus_ereal.simps simp add: uminus_ereal.simps[symmetric]
                  intro!: summable_iff_suminf_neq_top intro: less_imp_le)
      apply (subst (asm) suminf_minus_ereal)
      apply (auto intro!: summable_ereal_pos intro: less_imp_le)
      done
  qed
qed

subsection \<open>Transition Rates\<close>

locale transition_rates =
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes R_nonneg[simp]: "\<And>x y. 0 \<le> R x y"
  assumes R_diagonal_0[simp]: "\<And>x. R x x = 0"
  assumes finite_weight: "\<And>x. (\<integral>\<^sup>+y. R x y \<partial>count_space UNIV) < \<infinity>"
  assumes positive_weight: "\<And>x. 0 < (\<integral>\<^sup>+y. R x y \<partial>count_space UNIV)"
begin

abbreviation S :: "(real \<times> 'a) measure"
where "S \<equiv> (borel \<Otimes>\<^sub>M count_space UNIV)"

abbreviation T :: "(real \<times> 'a) stream measure"
where "T \<equiv> stream_space S"

abbreviation I :: "'a \<Rightarrow> 'a set"
where "I x \<equiv> {y. 0 < R x y}"

lemma I_countable: "countable (I x)"
proof -
  let ?P = "point_measure UNIV (R x)"
  interpret finite_measure ?P
  proof
    show "emeasure ?P (space ?P) \<noteq> \<infinity>"
      using finite_weight
      by (simp add: emeasure_density point_measure_def less_top)
  qed
  from countable_support emeasure_point_measure_finite2[of "{_}" UNIV "R x"]
  show ?thesis
    by (simp add: emeasure_eq_measure less_le)
qed

definition escape_rate :: "'a \<Rightarrow> real" where
  "escape_rate x = \<integral>y. R x y \<partial>count_space UNIV"

lemma ennreal_escape_rate: "ennreal (escape_rate x) = (\<integral>\<^sup>+y. R x y \<partial>count_space UNIV)"
  using finite_weight[of x] unfolding escape_rate_def
  by (intro nn_integral_eq_integral[symmetric]) (auto simp: integrable_iff_bounded)

lemma escape_rate_pos: "0 < escape_rate x"
  using positive_weight unfolding ennreal_escape_rate[symmetric] by simp

lemma nonneg_escape_rate[simp]: "0 \<le> escape_rate x"
  using escape_rate_pos[THEN less_imp_le] .

lemma prob_space_exponential_escape_rate: "prob_space (exponential (escape_rate x))"
  using escape_rate_pos by (rule prob_space_exponential)

lemma measurable_escape_rate[measurable]: "escape_rate \<in> count_space UNIV \<rightarrow>\<^sub>M borel"
  by auto

lemma measurable_exponential_escape_rate[measurable]: "(\<lambda>x. exponential (escape_rate x)) \<in> count_space UNIV \<rightarrow>\<^sub>M prob_algebra borel"
  by (auto simp: space_prob_algebra sets_exponential prob_space_exponential_escape_rate)

interpretation pmf_as_function .

lift_definition J :: "'a \<Rightarrow> 'a pmf" is "\<lambda>x y.  R x y / escape_rate x"
proof safe
  show "0 \<le> R x y / escape_rate x" for x y
    by (auto intro!: integral_nonneg_AE divide_nonneg_nonneg R_nonneg simp: escape_rate_def)
  show "(\<integral>\<^sup>+y. R x y / escape_rate x \<partial>count_space UNIV) = 1" for x
    using escape_rate_pos[of x]
    by (auto simp add: divide_ennreal[symmetric] nn_integral_divide ennreal_escape_rate[symmetric] intro!: ennreal_divide_self)
qed

lemma set_pmf_J: "set_pmf (J x) = I x"
  using escape_rate_pos[of x] by (auto simp: set_pmf_iff J.rep_eq less_le)

interpretation exp_esc: pair_prob_space "distr (exponential (escape_rate x)) borel ((+) t)" "J x" for x
proof -
  interpret prob_space "distr (exponential (escape_rate x)) borel ((+) t)"
    by (intro prob_space.prob_space_distr prob_space_exponential_escape_rate) simp
  show "pair_prob_space (distr (exponential (escape_rate x)) borel ((+) t)) (measure_pmf (J x))"
    by standard
qed

subsection \<open>Continuous-time Kernel\<close>

definition K :: "(real \<times> 'a) \<Rightarrow> (real \<times> 'a) measure" where
  "K = (\<lambda>(t, x). (distr (exponential (escape_rate x)) borel ((+) t)) \<Otimes>\<^sub>M J x)"

interpretation K: discrete_Markov_process "borel \<Otimes>\<^sub>M count_space UNIV" K
proof
  show "K \<in> borel \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (borel \<Otimes>\<^sub>M count_space UNIV)"
    unfolding K_def
    apply measurable
    apply (rule measurable_snd[THEN measurable_compose])
    apply (auto simp: space_prob_algebra prob_space_measure_pmf)
    done
qed

interpretation DTMC: MC_syntax J .

lemma in_space_S[simp]: "x \<in> space S"
  by (simp add: space_pair_measure)

lemma in_space_T[simp]: "x \<in> space T"
  by (simp add: space_pair_measure space_stream_space)

lemma in_space_lim_stream: "\<omega> \<in> space (K.lim_stream x)"
  unfolding K.space_lim_stream space_stream_space[symmetric] by simp

lemma prob_space_K_lim: "prob_space (K.lim_stream x)"
  using K.lim_stream[THEN measurable_space] by (simp add: space_prob_algebra)

definition select_first :: "'a \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool"
where "select_first x p y = (y \<in> I x \<and> (\<forall>y'\<in>I x - {y}. p y < p y'))"

lemma select_firstD1: "select_first x p y \<Longrightarrow> y \<in> I x"
  by (simp add: select_first_def)

lemma select_first_unique:
  assumes y: "select_first x p y1" " select_first x p y2" shows "y1 = y2"
proof -
  have "y1 \<noteq> y2 \<Longrightarrow> p y1 < p y2" "y1 \<noteq> y2 \<Longrightarrow> p y2 < p y1"
    using y by (auto simp: select_first_def)
  then show "y1 = y2"
    by (rule_tac ccontr) auto
qed

lemma The_select_first[simp]: "select_first x p y \<Longrightarrow> The (select_first x p) = y"
  by (intro the_equality select_first_unique)

lemma select_first_INF:
  "select_first x p y \<Longrightarrow> (INF x\<in>I x. p x) = p y"
  by (intro antisym cINF_greatest cINF_lower bdd_belowI2[where m="p y"])
     (auto simp: select_first_def le_less)

lemma measurable_select_first[measurable]:
  "(\<lambda>p. select_first x p y) \<in> (\<Pi>\<^sub>M y\<in>I x. borel) \<rightarrow>\<^sub>M count_space UNIV"
  using I_countable unfolding select_first_def by (intro measurable_pred_countable pred_intros_conj1') measurable

lemma measurable_THE_select_first[measurable]:
  "(\<lambda>p. The (select_first x p)) \<in> (\<Pi>\<^sub>M y\<in>I x. borel) \<rightarrow>\<^sub>M count_space UNIV"
  by (rule measurable_THE) (auto intro: select_first_unique I_countable dest: select_firstD1)

lemma sets_S_eq: "sets S = sigma_sets UNIV { {t ..} \<times> A | t A. A \<subseteq> - I x \<or> (\<exists>s\<in>I x. A = {s}) }"
proof (subst sets_pair_eq)
  let ?CI = "\<lambda>a::real. {a ..}" let ?Ea = "range ?CI"

  show "?Ea \<subseteq> Pow (space borel)" "sets borel = sigma_sets (space borel) ?Ea"
    unfolding borel_Ici by auto
  show "?CI`Rats \<subseteq> ?Ea" "(\<Union>i\<in>Rats. ?CI i) = space borel"
    using Rats_dense_in_real[of "x - 1" "x" for x] by (auto intro: less_imp_le)

  let ?Eb = "Pow (- I x) \<union> (\<lambda>s. {s}) ` I x"
  have "b \<in> sigma_sets UNIV (Pow (- I x) \<union> (\<lambda>s. {s}) ` I x)" for b
  proof -
    have "b = (b - I x) \<union> (\<Union>x\<in>b \<inter> I x. {x})"
      by auto
    also have "\<dots> \<in> sigma UNIV (Pow (- I x) \<union> (\<lambda>s. {s}) ` I x)"
      using I_countable by (intro sets.Un sets.countable_UN') auto
    finally show ?thesis
      by simp
  qed
  then show "sets (count_space UNIV) = sigma_sets (space (count_space UNIV)) ?Eb"
    by auto
  show "countable ({- I x} \<union> (\<Union>s\<in>I x. {{s}}))"
    using I_countable by auto
  show "sets (sigma (space borel \<times> space (count_space UNIV)) {a \<times> b |a b. a \<in> ?Ea \<and> b \<in> ?Eb}) =
    sigma_sets UNIV {{t ..} \<times> A |t A. A \<subseteq> - I x \<or> (\<exists>s\<in>I x. A = {s})}"
    apply simp
    apply (intro arg_cong[where f="sigma_sets _"])
    apply auto
    done
qed (auto intro: countable_rat)

subsection \<open>Kernel equals Parallel Choice\<close>

abbreviation PAR :: "'a \<Rightarrow> ('a \<Rightarrow> real) measure"
where
  "PAR x \<equiv> (\<Pi>\<^sub>M y\<in>I x. exponential (R x y))"

lemma PAR_least:
  assumes y: "y \<in> I x"
  shows "PAR x {p\<in>space (PAR x). t \<le> p y \<and> select_first x p y} =
     emeasure (exponential (escape_rate x)) {t ..} * ennreal (pmf (J x) y)"
proof -
  let ?E = "\<lambda>y. exponential (R x y)" let ?P' = "\<Pi>\<^sub>M y\<in>I x - {y}. ?E y"
  interpret P': prob_space ?P'
    by (intro prob_space_PiM prob_space_exponential) simp
  have *: "PAR x = (\<Pi>\<^sub>M y\<in>insert y (I x - {y}). ?E y)"
    using y by (intro PiM_cong) auto
  have "0 < R x y"
    using y by simp
  have **: "(\<lambda>(x, X). X(y := x)) \<in> exponential (R x y) \<Otimes>\<^sub>M Pi\<^sub>M (I x - {y}) (\<lambda>i. exponential (R x i)) \<rightarrow>\<^sub>M PAR x"
    using y
    apply (subst measurable_cong_sets[OF sets_pair_measure_cong[OF sets_exponential sets_PiM_cong[OF refl sets_exponential]] sets_PiM_cong[OF refl sets_exponential]])
    apply measurable
    apply (rule measurable_fun_upd[where J="I x - {y}"])
    apply auto
    done
  have "PAR x {p\<in>space (PAR x). t \<le> p y \<and> (\<forall>y'\<in>I x-{y}. p y < p y')} =
    (\<integral>\<^sup>+ty. indicator {t..} ty * ?P' {p\<in>space ?P'. \<forall>y'\<in>I x-{y}. ty < p y'} \<partial>?E y)"
    unfolding * using \<open>y \<in> I x\<close>
    apply (subst distr_pair_PiM_eq_PiM[symmetric])
    apply (auto intro!: prob_space_exponential simp: emeasure_distr insert_absorb)
    apply (subst emeasure_distr[OF **])
    subgoal
      using I_countable by (auto simp: pred_def[symmetric])
    apply (subst P'.emeasure_pair_measure_alt)
    subgoal
      using I_countable[of x]
      apply (intro measurable_sets[OF **])
      apply (auto simp: pred_def[symmetric])
      done
    apply (auto intro!: nn_integral_cong arg_cong2[where f=emeasure] split: split_indicator if_split_asm
      simp: space_exponential space_PiM space_pair_measure PiE_iff extensional_def)
    done
  also have "\<dots> = (\<integral>\<^sup>+ty. indicator {t..} ty * ennreal (exp (- ty * (escape_rate x - R x y))) \<partial>?E y)"
    apply (intro nn_integral_cong_AE)
    using AE_exponential[OF \<open>0 < R x y\<close>]
  proof eventually_elim
    fix ty :: real assume "0 < ty"
    have "escape_rate x =
      (\<integral>\<^sup>+y'. R x y' * indicator {y} y' \<partial>count_space UNIV) + (\<integral>\<^sup>+y'. R x y' * indicator (I x - {y}) y' \<partial>count_space UNIV)"
      unfolding ennreal_escape_rate by (subst nn_integral_add[symmetric]) (auto simp: less_le split: split_indicator intro!: nn_integral_cong)
    also have "\<dots> = R x y + (\<integral>\<^sup>+y'. R x y' \<partial>count_space (I x - {y}))"
      by (auto simp add: nn_integral_count_space_indicator less_le simp del: nn_integral_indicator_singleton
               intro!: arg_cong2[where f="(+)"] nn_integral_cong split: split_indicator)
    finally have "(\<integral>\<^sup>+y'. R x y' \<partial>count_space (I x - {y})) = escape_rate x - R x y \<and> R x y \<le> escape_rate x"
      using escape_rate_pos[THEN less_imp_le]
      by (cases "(\<integral>\<^sup>+y'. R x y' \<partial>count_space (I x - {y}))")
         (auto simp: add_top ennreal_plus[symmetric] simp del: ennreal_plus)
    then have "integrable (count_space (I x - {y})) (R x)" "(LINT y'|count_space (I x - {y}). R x y') = escape_rate x - R x y"
      by (auto simp: nn_integral_eq_integrable)
    then have "?P' (prod_emb (I x-{y}) ?E (I x-{y}) (\<Pi>\<^sub>E j\<in>(I x-{y}). {ty<..})) = exp (- ty * (escape_rate x - R x y))"
      using I_countable \<open>0 < ty\<close> by (subst emeasure_PiM_exponential_Ioi_countable) auto
    also have "prod_emb (I x-{y}) ?E (I x-{y}) (\<Pi>\<^sub>E j\<in>(I x-{y}). {ty<..}) = {p\<in>space ?P'. \<forall>y'\<in>I x-{y}. ty < p y'}"
      by (simp add: set_eq_iff prod_emb_def space_PiM space_exponential ac_simps Pi_iff)
    finally show "indicator {t..} ty * ?P' {p\<in>space ?P'. \<forall>y'\<in>I x-{y}. ty < p y'} =
      indicator {t..} ty * ennreal (exp (- ty * (escape_rate x - R x y)))"
      by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+ty. ennreal (R x y) * (ennreal (exp (- ty * escape_rate x)) * indicator {max 0 t..} ty) \<partial>lborel)"
    by (auto simp add: exponential_def exponential_density_def nn_integral_density ennreal_mult[symmetric] exp_add[symmetric] field_simps
                intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (R x y / escape_rate x) * emeasure (exponential (escape_rate x)) {max 0 t..}"
    using escape_rate_pos[of x]
    by (auto simp: exponential_def exponential_density_def emeasure_density nn_integral_cmult[symmetric] ennreal_mult[symmetric]
             split: split_indicator intro!: nn_integral_cong )
  also have "\<dots> = pmf (J x) y * emeasure (exponential (escape_rate x)) {t..}"
    using AE_exponential[OF escape_rate_pos[of x]]
    by (intro arg_cong2[where f="(*)"] emeasure_eq_AE) (auto simp: J.rep_eq )
  finally show ?thesis
    using assms by (simp add: mult_ac select_first_def)
qed

lemma AE_PAR_least: "AE p in PAR x. \<exists>y\<in>I x. select_first x p y"
proof -
  have D: "disjoint_family_on (\<lambda>y. {p \<in> space (PAR x). select_first x p y}) (I x)"
    by (auto simp: disjoint_family_on_def dest: select_first_unique)
  have "PAR x {p\<in>space (PAR x). \<exists>y\<in>I x. select_first x p y} =
    PAR x (\<Union>y\<in>I x. {p\<in>space (PAR x). select_first x p y})"
    by (auto intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = (\<integral>\<^sup>+y. PAR x {p\<in>space (PAR x). select_first x p y} \<partial>count_space (I x))"
    using I_countable by (intro emeasure_UN_countable D) auto
  also have "\<dots> = (\<integral>\<^sup>+y. PAR x {p\<in>space (PAR x). 0 \<le> p y \<and> select_first x p y} \<partial>count_space (I x))"
  proof (intro nn_integral_cong emeasure_eq_AE, goal_cases)
    case (1 y) with AE_PiM_component[of "I x" "\<lambda>y. exponential (R x y)" y "(<) 0"] AE_exponential[of "R x y"] show ?case
      by (auto simp: prob_space_exponential)
  qed (insert I_countable, auto)
  also have "\<dots> = (\<integral>\<^sup>+y. emeasure (exponential (escape_rate x)) {0 ..} * ennreal (pmf (J x) y) \<partial>count_space (I x))"
    by (auto simp add: PAR_least intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+y. emeasure (exponential (escape_rate x)) {0 ..} \<partial>J x)"
    by (auto simp: nn_integral_measure_pmf nn_integral_count_space_indicator ac_simps pmf_eq_0_set_pmf set_pmf_J
             simp del: nn_integral_const intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = 1"
    using AE_exponential[of "escape_rate x"]
    by (auto intro!: prob_space.emeasure_eq_1_AE prob_space_exponential simp: escape_rate_pos less_imp_le)
  finally show ?thesis
    using I_countable
    by (subst prob_space.AE_iff_emeasure_eq_1 prob_space_PiM prob_space_exponential)
       (auto intro!: prob_space_PiM prob_space_exponential simp del: Set.bex_simps(6))
qed

lemma K_alt: "K (t, x) = distr (\<Pi>\<^sub>M y\<in>I x. exponential (R x y)) S (\<lambda>p. (t + (INF y\<in>I x. p y), The (select_first x p)))" (is "_ = ?R")
proof (rule measure_eqI_generator_eq_countable)
  let ?E = "{ {t ..} \<times> A | (t::real) A. A \<subseteq> - I x \<or> (\<exists>s\<in>I x. A = {s}) }"
  show "Int_stable ?E"
    apply (auto simp: Int_stable_def)
    subgoal for t1 A1 t2 A2
      by (intro exI[of _ "max t1 t2"] exI[of _ "A1 \<inter> A2"]) auto
    subgoal for t1 t2 y1 y2
      by (intro exI[of _ "max t1 t2"] exI[of _ "{y1} \<inter> {y2}"]) auto
    done
  show "sets (K (t, x)) = sigma_sets UNIV ?E"
    unfolding K.sets_K[OF in_space_S] by (subst sets_S_eq) rule
  show "sets ?R = sigma_sets UNIV ?E"
    using sets_S_eq by simp
  show "countable ((\<lambda>(t, A). {t ..} \<times> A) ` (\<rat> \<times> ({- I x} \<union> (\<lambda>s. {s}) ` I x)))"
    by (intro countable_image countable_SIGMA countable_rat countable_Un I_countable) auto

   have *: "(+) t -` {t'..} \<inter> space (exponential (escape_rate x)) = {t' - t..}" for t'
     by (auto simp: space_exponential)
  { fix X assume "X \<in> ?E"
    then consider
        t' s where "s \<in> I x" "X = {t' ..} \<times> {s}"
      | t' A where "A \<subseteq> - I x" "X = {t' ..} \<times> A"
      by auto
    then show "K (t, x) X = ?R X"
    proof cases
      case 1
      have "AE p in PAR x. (t' - t \<le> p s \<and> select_first x p s) =
              (t' \<le> t + (\<Sqinter>x\<in>I x. p x) \<and> The (select_first x p) = s)"
        using AE_PAR_least by eventually_elim (auto dest: select_first_unique simp: select_first_INF)
      with 1 I_countable show ?thesis
        by (auto simp add: K_def measure_pmf.emeasure_pair_measure_Times emeasure_distr emeasure_pmf_single *
          PAR_least[symmetric] intro!: emeasure_eq_AE)
    next
      case 2
      moreover
      then have "emeasure (measure_pmf (J x)) A = 0"
        by (subst AE_iff_measurable[symmetric, where P="\<lambda>x. x \<notin> A"])
           (auto simp: AE_measure_pmf_iff set_pmf_J subset_eq)
      moreover
      have "PAR x ((\<lambda>p. (t + \<Sqinter>(p ` (I x)), The (select_first x p))) -` ({t'..} \<times> A) \<inter> space (PAR x)) = 0"
        using \<open>A \<subseteq> - I x\<close> AE_PAR_least[of x] I_countable
        by (subst AE_iff_measurable[symmetric, where P="\<lambda>p. (t + \<Sqinter>(p ` (I x)), The (select_first x p)) \<notin> {t'..} \<times> A"])
           (auto simp del: all_simps(5) simp add: imp_ex imp_conjL subset_eq)
      ultimately show ?thesis
        using I_countable
        by (simp add: K_def measure_pmf.emeasure_pair_measure_Times emeasure_distr *)
    qed }

  interpret prob_space "K ts" for ts
    by (rule K.prob_space_K) simp
  show "emeasure (K (t, x)) a \<noteq> \<infinity>" for a
    using emeasure_finite by simp
qed (insert  Rats_dense_in_real[of "x - 1" x for x], auto, blast intro: less_imp_le)

lemma AE_K: "AE y in K x. fst x < fst y \<and> snd y \<in> J (snd x)"
  unfolding K_def split_beta
  apply (subst exp_esc.AE_pair_iff[symmetric])
  apply measurable
  apply (simp_all add: AE_distr_iff AE_measure_pmf_iff exponential_def AE_density exponential_density_def cong del: AE_cong)
  using AE_lborel_singleton[of 0]
  apply eventually_elim
  apply simp
  done

lemma AE_lim_stream:
  "AE \<omega> in K.lim_stream x. \<forall>i. snd ((x ## \<omega>) !! i) \<in> DTMC.acc``{snd x} \<and> snd (\<omega> !! i) \<in> J (snd ((x ## \<omega>) !! i)) \<and> fst ((x ## \<omega>) !! i) < fst (\<omega> !! i)"
  (is "AE \<omega> in K.lim_stream x. \<forall>i. ?P \<omega> i")
  unfolding AE_all_countable
proof
  let ?F = "\<lambda>i x \<omega>. fst ((x ## \<omega>) !! i)" and ?S = "\<lambda>i x \<omega>. snd ((x ## \<omega>) !! i)"
  fix i show "AE \<omega> in K.lim_stream x. ?P \<omega> i"
  proof (induction i arbitrary: x)
    case 0 with AE_K[of x] show ?case
      by (subst K.AE_lim_stream) (auto simp add: space_pair_measure cong del: AE_cong)
  next
    case (Suc i)
    show ?case
    proof (subst K.AE_lim_stream, goal_cases)
      case 2 show ?case
        using DTMC.countable_reachable
        by (intro measurable_compose_countable_restrict[where f="?S (Suc i) x"])
           (simp_all del: Image_singleton_iff)
    next
      case 3 show ?case
        apply (simp del: AE_conj_iff cong del: AE_cong)
        using AE_K[of x]
        apply eventually_elim
        subgoal premises K_prems for y
          using Suc
          by eventually_elim (insert K_prems, auto intro: converse_rtrancl_into_rtrancl)
        done
    qed (simp add: space_pair_measure)
  qed
qed

lemma measurable_merge_at[measurable]: "(\<lambda>(\<omega>, \<omega>'). merge_at \<omega> j \<omega>') \<in> (T \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M T"
proof (rule measurable_stream_space2)
  define F where "F x n = (case x of (\<omega>::(real \<times> 'a) stream, \<omega>') \<Rightarrow> merge_at \<omega> j \<omega>') !! n" for x n
  fix n
  have "(\<lambda>x. F x n) \<in> stream_space S \<Otimes>\<^sub>M stream_space S \<rightarrow>\<^sub>M S"
  proof (induction n)
    case 0 then show ?case
      by (simp add: F_def split_beta' stream.case_eq_if)
  next
    case (Suc n)
    from Suc[measurable]
    have eq: "F x (Suc n) = (case fst x of (t, s) ## \<omega> \<Rightarrow> if t \<le> j then F (\<omega>, snd x) n else snd x !! Suc n)" for x
      by (auto simp: F_def split: prod.split stream.split)
    show ?case
      unfolding eq stream.case_eq_if by measurable
  qed
  then show "(\<lambda>x. (case x of (\<omega>, \<omega>') \<Rightarrow> merge_at \<omega> j \<omega>') !! n) \<in> stream_space S \<Otimes>\<^sub>M stream_space S \<rightarrow>\<^sub>M S"
    unfolding F_def by auto
qed

lemma measurable_trace_at[measurable]: "(\<lambda>(s, \<omega>). trace_at s \<omega> j) \<in> (count_space UNIV \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M count_space UNIV"
  unfolding trace_at_eq by measurable

lemma measurable_trace_at': "(\<lambda>((s, j), \<omega>). trace_at s \<omega> j) \<in> ((count_space UNIV \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M T) \<rightarrow>\<^sub>M count_space UNIV"
  unfolding trace_at_eq split_beta' by measurable

lemma K_time_split:
  assumes "t \<le> j" and [measurable]: "f \<in> S \<rightarrow>\<^sub>M borel"
  shows "(\<integral>\<^sup>+x. f x * indicator {j <..} (fst x) \<partial>K (t, s)) = (\<integral>\<^sup>+x. f x \<partial>K (j, s)) * exponential (escape_rate s) {j - t <..}"
proof -
  have "(\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (t + x, y) * indicator {j<..} (t + x) \<partial>exponential (escape_rate s) \<partial>J s) =
    (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (t + x, y) * indicator {j - t<..} x \<partial>exponential (escape_rate s) \<partial>J s)"
    by (intro nn_integral_cong) (auto split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (t + x, y) \<partial>uniform_measure (exponential (escape_rate s)) {j-t <..} \<partial>J s) *
      emeasure (exponential (escape_rate s)) {j - t <..}"
    using \<open>t \<le> j\<close> escape_rate_pos
    by (subst nn_integral_uniform_measure)
       (auto simp: nn_integral_divide ennreal_divide_times emeasure_exponential_Ioi)
  also have "\<dots> = (\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f (j + x, y) \<partial>exponential (escape_rate s) \<partial>J s) *
      emeasure (exponential (escape_rate s)) {j - t <..}"
    using \<open>t \<le> j\<close> escape_rate_pos by (simp add: uniform_measure_exponential nn_integral_distr)
  finally show ?thesis
    by (simp add: K_def exp_esc.nn_integral_snd[symmetric] nn_integral_distr)
qed

lemma K_in_space[simp]: "K x \<in> space (prob_algebra S)"
  by (rule measurable_space [OF K.K]) simp

lemma L_in_space[simp]: "K.lim_stream x \<in> space (prob_algebra T)"
  by (rule measurable_space [OF K.lim_stream]) simp

subsection \<open>Markov Chain Property\<close>

lemma lim_time_split:
  "t \<le> j \<Longrightarrow> K.lim_stream (t, s) = do { \<omega> \<leftarrow> K.lim_stream (t, s) ; \<omega>' \<leftarrow> K.lim_stream (j, trace_at s \<omega> j) ; return T (merge_at \<omega> j \<omega>')}"
    (is "_ \<Longrightarrow> _ = ?DO t s")
proof (coinduction arbitrary: t s rule: K.lim_stream_eq_coinduct)
  case step let ?L = K.lim_stream

  note measurable_compose[OF measurable_prob_algebraD measurable_emeasure_subprob_algebra, measurable (raw)]

  define B' where "B' = (\<lambda>(t', s). if t' \<le> j then ?DO t' s else ?L (t', s))"
  show ?case
  proof (intro bexI conjI AE_I2)
    show [measurable]: "B' \<in> S \<rightarrow>\<^sub>M prob_algebra T"
      unfolding B'_def by measurable
    show "(\<exists>t s. y = (t, s) \<and> B' y = ?DO t s \<and> t \<le> j) \<or> ?L y = B' y" for y
      by (cases y; cases "fst y \<le> j") (auto simp: B'_def)
    let ?C = "\<lambda>x. do { \<omega> \<leftarrow> ?L x; \<omega>' \<leftarrow> ?L (j, trace_at s (x##\<omega>) j); return T (merge_at (x##\<omega>) j \<omega>') }"
    have "?DO t s = do { x \<leftarrow> K (t, s); ?C x }"
      apply (subst K.lim_stream_eq[OF in_space_S])
      apply (subst bind_assoc[OF measurable_prob_algebraD measurable_prob_algebraD])
      apply (subst measurable_cong_sets[OF K.sets_K[OF in_space_S] refl])
      apply measurable
      apply (subst bind_assoc[OF measurable_prob_algebraD measurable_prob_algebraD])
      apply measurable
      apply (subst bind_cong[OF refl bind_cong[OF refl bind_return[OF measurable_prob_algebraD]]])
      apply measurable
      done
    also have "\<dots> = K (t, s) \<bind> (\<lambda>y. B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>)))" (is "?DO' = ?R")
    proof (rule measure_eqI)
      have "sets ?DO' = sets T"
        by (intro sets_bind'[OF K_in_space]) measurable
      moreover have "sets ?R = sets T"
        by (intro sets_bind'[OF K_in_space]) measurable
      ultimately show "sets ?DO' = sets ?R"
        by simp
      fix A assume "A \<in> sets ?DO'"
      then have A[measurable]: "A \<in> T"
        unfolding \<open>sets ?DO' = sets T\<close> .
      have "?DO' A = (\<integral>\<^sup>+x. ?C x A \<partial>K (t, s))"
        by (subst emeasure_bind_prob_algebra[OF K_in_space]) measurable
      also have "\<dots> = (\<integral>\<^sup>+x. ?C x A * indicator {.. j} (fst x) \<partial>K (t, s)) +
        (\<integral>\<^sup>+x. ?C x A * indicator {j <..} (fst x) \<partial>K (t, s))"
        by (subst nn_integral_add[symmetric]) (auto intro!: nn_integral_cong split: split_indicator)
      also have "(\<integral>\<^sup>+x. ?C x A * indicator {.. j} (fst x) \<partial>K (t, s)) =
        (\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {.. j} (fst y) \<partial>K (t, s))"
      proof (intro nn_integral_cong ennreal_mult_right_cong refl arg_cong2[where f=emeasure])
        fix x :: "real \<times> 'a" assume "indicator {..j} (fst x) \<noteq> (0::ennreal)"
        then have "fst x \<le> j"
          by (auto split: split_indicator_asm)
        then show "?C x = (B' x \<bind> (\<lambda>\<omega>. return T (x ## \<omega>)))"
          apply (cases x)
          apply (simp add: B'_def)
          apply (subst bind_assoc[OF measurable_prob_algebraD measurable_prob_algebraD])
          apply measurable
          apply (subst bind_assoc[OF measurable_prob_algebraD measurable_prob_algebraD])
          apply measurable
          apply (subst bind_return)
          apply measurable
          done
      qed
      also have "(\<integral>\<^sup>+x. ?C x A * indicator {j <..} (fst x) \<partial>K (t, s)) =
        (\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {j <..} (fst y) \<partial>K (t, s))"
      proof -
        have *: "(+) t -` {j<..} = {j - t <..}"
          by auto

        have "(\<integral>\<^sup>+x. ?C x A * indicator {j <..} (fst x) \<partial>K (t, s)) =
          (\<integral>\<^sup>+x. ?L (j, s) A * indicator {j <..} (fst x) \<partial>K (t, s))"
          by (intro nn_integral_cong ennreal_mult_right_cong refl arg_cong2[where f=emeasure])
             (auto simp: K.sets_lim_stream bind_return'' bind_const' prob_space_K_lim prob_space_imp_subprob_space split: split_indicator_asm)
        also have "\<dots> = ?L (j, s) A * exponential (escape_rate s) {j - t <..}"
          by (subst nn_integral_cmult) (simp_all add: K_def exp_esc.nn_integral_snd[symmetric] emeasure_distr space_exponential *)
        also have "\<dots> = (\<integral>\<^sup>+x. emeasure (?L x \<bind> (\<lambda>\<omega>. return T (x ## \<omega>))) A \<partial>K (j, s)) * exponential (escape_rate s) {j - t <..}"
          by (subst K.lim_stream_eq) (auto simp: emeasure_bind_prob_algebra[OF K_in_space _ A])
        also have "\<dots> = (\<integral>\<^sup>+y. emeasure (?L y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {j <..} (fst y) \<partial>K (t, s))"
          using \<open>t \<le> j\<close> by (rule K_time_split[symmetric]) measurable
        also have "\<dots> = (\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {j <..} (fst y) \<partial>K (t, s))"
          by (intro nn_integral_cong ennreal_mult_right_cong refl arg_cong2[where f=emeasure])
             (auto simp add: B'_def split: split_indicator_asm)
        finally show ?thesis .
      qed
      also have "(\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {.. j} (fst y) \<partial>K (t, s)) +
        (\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A * indicator {j <..} (fst y) \<partial>K (t, s)) =
        (\<integral>\<^sup>+y. emeasure (B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>))) A \<partial>K (t, s))"
        by (subst nn_integral_add[symmetric]) (auto intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = emeasure (K (t, s) \<bind> (\<lambda>y. B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>)))) A"
        by (rule emeasure_bind_prob_algebra[symmetric, OF K_in_space _ A]) auto
      finally show "?DO' A = emeasure (K (t, s) \<bind> (\<lambda>y. B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>)))) A" .
    qed
    finally show "?DO t s = K (t, s) \<bind> (\<lambda>y. B' y \<bind> (\<lambda>\<omega>. return T (y ## \<omega>)))" .
  qed
qed (simp add: space_pair_measure)

lemma K_eq: "K (t, s) = distr (exponential (escape_rate s) \<Otimes>\<^sub>M J s) S (\<lambda>(t', s). (t + t', s))"
proof -
  have "distr (exponential (escape_rate s)) borel ((+) t) \<Otimes>\<^sub>M distr (J s) (J s) (\<lambda>x. x) =
    distr (exponential (escape_rate s) \<Otimes>\<^sub>M J s) (borel \<Otimes>\<^sub>M J s) (\<lambda>(x, y). (t + x, y))"
  proof (intro pair_measure_distr)
    interpret prob_space "distr (measure_pmf (J s)) (measure_pmf (J s)) (\<lambda>x. x)"
      by (intro measure_pmf.prob_space_distr) simp
    show "sigma_finite_measure (distr (measure_pmf (J s)) (measure_pmf (J s)) (\<lambda>x. x))"
      by unfold_locales
  qed auto
  also have "\<dots> = distr (exponential (escape_rate s) \<Otimes>\<^sub>M J s) S (\<lambda>(x, y). (t + x, y))"
    by (intro distr_cong refl sets_pair_measure_cong) simp
  finally show ?thesis
    by (simp add: K_def)
qed

lemma K_shift: "K (t + t', s) = distr (K (t, s)) S (\<lambda>(t, s). (t + t', s))"
  unfolding K_eq by (subst distr_distr) (auto simp: comp_def split_beta' ac_simps)

lemma K_not_empty: "space (K x) \<noteq> {}"
  by (simp add: K_def space_pair_measure split: prod.split)

lemma lim_stream_not_empty: "space (K.lim_stream x) \<noteq> {}"
  by (simp add: K.space_lim_stream space_pair_measure split: prod.split)

lemma lim_shift: \<comment> \<open>Generalize to bijective function on @{const K.lim_stream} invariant on @{const K}\<close>
  "K.lim_stream (t + t', s) = distr (K.lim_stream (t, s)) T (smap (\<lambda>(t, s). (t + t', s)))"
  (is "_ = ?D t s")
proof (coinduction arbitrary: t s rule: K.lim_stream_eq_coinduct)
  case step then show ?case
  proof (intro bexI[of _ "\<lambda>(t, s). ?D (t - t') s"] conjI)
    show "?D t s = K (t + t', s) \<bind> (\<lambda>y. (case y of (t, s) \<Rightarrow> ?D (t - t') s) \<bind> (\<lambda>\<omega>. return T (y ## \<omega>)))"
      apply (subst K.lim_stream_eq[OF in_space_S])
      apply (subst K_shift)
      apply (subst distr_bind[OF measurable_prob_algebraD K_not_empty])
      apply (measurable; fail)
      apply (measurable; fail)
      apply (subst bind_distr[OF _ measurable_prob_algebraD K_not_empty])
      apply (measurable; fail)
      apply (measurable; fail)
      apply (intro bind_cong refl)
      apply (subst distr_bind[OF measurable_prob_algebraD lim_stream_not_empty])
      apply (measurable; fail)
      apply (measurable; fail)
      apply (simp add: distr_return split_beta)
      apply (subst bind_distr[OF _ measurable_prob_algebraD lim_stream_not_empty])
      apply (measurable; fail)
      apply (measurable; fail)
      apply (simp add: split_beta')
      done
  qed (auto cong: conj_cong intro!: exI[of _ "_ - t'"])
qed simp

lemma lim_0: "K.lim_stream (t, s) = distr (K.lim_stream (0, s)) T (smap (\<lambda>(t', s). (t' + t, s)))"
  using lim_shift[of 0 t s] by simp

subsection \<open>Explosion time\<close>

definition explosion :: "(real \<times> 'a) stream \<Rightarrow> ereal"
  where "explosion \<omega> = (SUP i. ereal (fst (\<omega> !! i)))"

lemma ball_less_Suc_eq: "(\<forall>i<Suc n. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i<n. P (Suc i)))"
  using less_Suc_eq_0_disj by auto

lemma lim_stream_timediff_eq_exponential_1:
  "distr (K.lim_stream ts) (PiM UNIV (\<lambda>_. borel))
    (\<lambda>\<omega> i. escape_rate (snd ((ts##\<omega>) !! i)) * (fst (\<omega> !! i) - fst ((ts##\<omega>) !! i))) =
    PiM UNIV (\<lambda>_. exponential 1)"
  (is "?D = ?P")
proof (rule measure_eqI_PiM_sequence)
  show "sets ?D = sets (PiM UNIV (\<lambda>_. borel))" "sets ?P = sets (PiM UNIV (\<lambda>_. borel))"
    by (auto intro!: sets_PiM_cong simp: sets_exponential)
  have [measurable]: "ts \<in> space S"
    by auto
  { interpret prob_space ?D
      by (intro prob_space.prob_space_distr K.prob_space_lim_stream measurable_abs_UNIV) auto
    show "finite_measure ?D"
      by unfold_locales }

  interpret E: prob_space "exponential 1"
    by (rule prob_space_exponential) simp
  interpret P: product_prob_space "\<lambda>_. exponential 1" UNIV
    by unfold_locales

  let "distr _ _ (?f ts)" = ?D

  fix A :: "nat \<Rightarrow> real set" and n :: nat assume A[measurable]: "\<And>i. A i \<in> sets borel"
  define n' where "n' = Suc n"
  have "emeasure ?D (prod_emb UNIV (\<lambda>_. borel) {..n} (Pi\<^sub>E {..n} A)) =
    emeasure (K.lim_stream ts) {\<omega>\<in>space (stream_space S). \<forall>i<n'. ?f ts \<omega> i \<in> A i}"
    apply (subst emeasure_distr)
      apply (auto intro!: measurable_abs_UNIV arg_cong[where f="emeasure _"])
      apply (auto simp: prod_emb_def K.space_lim_stream space_pair_measure n'_def)
    done
  also have "\<dots> = (\<Prod>i<n'. emeasure (exponential 1) (A i))"
    using A
  proof (induction n' arbitrary: A ts)
    case 0 then show ?case
      using prob_space.emeasure_space_1[OF prob_space_K_lim]
      by (simp add: K.space_lim_stream space_pair_measure)
  next
    case (Suc n A ts)
    from Suc.prems[measurable]
    have [measurable]: "ts \<in> space S"
      by auto

    have "emeasure (K.lim_stream ts) {\<omega> \<in> space (stream_space S). \<forall>i<Suc n. ?f ts \<omega> i \<in> A i} =
      (\<integral>\<^sup>+ts'. indicator (A 0) (escape_rate (snd ts) * (fst ts' - fst ts)) *
        emeasure (K.lim_stream ts') {\<omega> \<in> space (stream_space S). \<forall>i<n. ?f ts' \<omega> i \<in> A (Suc i)} \<partial>K ts)"
      apply (subst K.emeasure_lim_stream)
      apply simp
       apply measurable
      apply (auto intro!: nn_integral_cong arg_cong2[where f=emeasure] split: split_indicator
        simp: ball_less_Suc_eq)
      done
    also have "\<dots> = (\<integral>\<^sup>+ts'. indicator (A 0) (escape_rate (snd ts) * (fst ts' - fst ts)) \<partial>K ts) *
      (\<Prod>i<n. emeasure (exponential 1) (A (Suc i)))"
      by (subst Suc.IH) (simp_all add: nn_integral_multc)
    also have "(\<integral>\<^sup>+ts'. indicator (A 0) (escape_rate (snd ts) * (fst ts' - fst ts)) \<partial>K ts) =
      (\<integral>\<^sup>+t. indicator (A 0) (escape_rate (snd ts) * t) \<partial>exponential (escape_rate (snd ts)))"
      by (simp add: K_def exp_esc.nn_integral_snd[symmetric] nn_integral_distr split: prod.split)
    also have "\<dots> = emeasure (exponential 1) (A 0)"
      using escape_rate_pos[of "snd ts"]
      by (subst exponential_eq_stretch) (simp_all add: nn_integral_distr)
    also have "emeasure (exponential 1) (A 0) * (\<Prod>i<n. emeasure (exponential 1) (A (Suc i))) =
      (\<Prod>i<Suc n. emeasure (exponential 1) (A i))"
      by (rule prod.lessThan_Suc_shift[symmetric])
    finally show ?case .
  qed
  also have "\<dots> = emeasure ?P (prod_emb UNIV (\<lambda>_. borel) {..<n'} (Pi\<^sub>E {..<n'} A))"
    using P.emeasure_PiM_emb[of "{..<n'}" A] by (simp add: prod_emb_def space_exponential)
  finally show "emeasure ?D (prod_emb UNIV (\<lambda>_. borel) {..n} (Pi\<^sub>E {..n} A)) =
    emeasure ?P (prod_emb UNIV (\<lambda>_. borel) {..n} (Pi\<^sub>E {..n} A))"
    by (simp add: n'_def lessThan_Suc_atMost)
qed

lemma AE_explosion_infty:
  assumes bdd: "bdd_above (range escape_rate)"
  shows "AE \<omega> in K.lim_stream x. explosion \<omega> = \<infinity>"
proof -
  have "escape_rate undefined \<le> (SUP x. escape_rate x)"
    using bdd by (intro cSUP_upper) auto
  then have SUP_escape_pos: "0 < (SUP x. escape_rate x)"
    using escape_rate_pos[of undefined] by simp
  then have SUP_escape_nonneg: "0 \<le> (SUP x. escape_rate x)"
    by (rule less_imp_le)

  have [measurable]: "x \<in> space S" by auto
  have "(\<Sum>i. 1::ennreal) = top"
    by (rule sums_unique[symmetric]) (auto simp: sums_def of_nat_tendsto_top_ennreal)
  then have "AE \<omega> in (PiM UNIV (\<lambda>_. exponential 1)). (\<Sum>i. ereal (\<omega> i)) = \<infinity>"
    by (intro AE_PiM_exponential_suminf_infty) auto
  then have "AE \<omega> in K.lim_stream x.
    (\<Sum>i. ereal (escape_rate (snd ((x##\<omega>) !! i)) * (fst (\<omega> !! i) - fst ((x##\<omega>) !! i)))) = \<infinity>"
    apply (subst (asm) lim_stream_timediff_eq_exponential_1[symmetric, of x])
    apply (subst (asm) AE_distr_iff)
    apply (auto intro!: measurable_abs_UNIV)
    done
  then show ?thesis
    using AE_lim_stream
  proof eventually_elim
    case (elim \<omega>)
    then have le: "fst ((x##\<omega>) !! n) \<le> fst ((x ## \<omega>) !! m)" if "n \<le> m" for n m
      by (intro lift_Suc_mono_le[OF _ \<open>n \<le> m\<close>, of "\<lambda>i. fst ((x ## \<omega>) !! i)"]) (auto intro: less_imp_le)
    have [simp]: "fst x \<le> fst ((x##\<omega>) !! i)" "fst ((x##\<omega>) !! i) \<le> fst (\<omega> !! i)" for i
      using le[of "i" "Suc i"] le[of 0 i] by auto

    have "(\<Sum>i. ereal (escape_rate (snd ((x ## \<omega>) !! i)) * (fst (\<omega> !! i) - fst ((x ## \<omega>) !! i)))) =
      (SUP n. \<Sum>i<n. ereal (escape_rate (snd ((x ## \<omega>) !! i)) * (fst (\<omega> !! i) - fst ((x ## \<omega>) !! i))))"
      by (intro suminf_ereal_eq_SUP) (auto intro!: mult_nonneg_nonneg)
    also have "\<dots> \<le> (SUP n. (SUP x. escape_rate x) * (ereal (fst ((x ## \<omega>) !! n)) - ereal (fst x)))"
    proof (intro SUP_least SUP_upper2)
      fix n
      have "(\<Sum>i<n. ereal (escape_rate (snd ((x ## \<omega>) !! i)) * (fst (\<omega> !! i) - fst ((x ## \<omega>) !! i)))) \<le>
        (\<Sum>i<n. ereal ((SUP i. escape_rate i) * (fst (\<omega> !! i) - fst ((x ## \<omega>) !! i))))"
        using elim bdd by (intro sum_mono) (auto intro!: cSUP_upper)
      also have "\<dots> = (SUP i. escape_rate i) * (\<Sum>i<n. fst ((x ## \<omega>) !! Suc i) - fst ((x ## \<omega>) !! i))"
        using elim bdd by (subst sum_ereal) (auto simp: sum_distrib_left)
      also have "\<dots> = (SUP i. escape_rate i) * (fst ((x ## \<omega>) !! n) - fst x)"
        by (subst sum_lessThan_telescope) simp
      finally show "(\<Sum>i<n. ereal (escape_rate (snd ((x ## \<omega>) !! i)) * (fst (\<omega> !! i) - fst ((x ## \<omega>) !! i))))
         \<le> (SUP x. escape_rate x) * (ereal (fst ((x ## \<omega>) !! n)) - ereal (fst x))"
        by simp
    qed simp
    also have "\<dots> = (SUP x. escape_rate x) * ((SUP n. ereal (fst ((x ## \<omega>) !! n))) - ereal (fst x))"
      using elim SUP_escape_nonneg by (subst SUP_ereal_mult_left) (auto simp: SUP_ereal_minus_left[symmetric])
    also have "(SUP n. ereal (fst ((x ## \<omega>) !! n))) = explosion \<omega>"
      unfolding explosion_def
      apply (intro SUP_eq)
      subgoal for i by (intro bexI[of _ i]) auto
      subgoal for i by (intro bexI[of _ "Suc i"]) auto
      done
    finally show "explosion \<omega> = \<infinity>"
      using elim SUP_escape_pos by (cases "explosion \<omega>") (auto split: if_splits)
  qed
qed

subsection \<open>Transition probability $p_t$\<close>

context
begin

declare [[inductive_internals = true]]

inductive trace_in :: "'a set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> (real \<times> 'a) stream \<Rightarrow> bool" for S t
where
  "t < t' \<Longrightarrow> s \<in> S \<Longrightarrow> trace_in S t s ((t', s')##\<omega>)"
| "t \<ge> t' \<Longrightarrow> trace_in S t s' \<omega> \<Longrightarrow> trace_in S t s ((t', s')##\<omega>)"

end

lemma trace_in_simps[simp]:
  "trace_in ss t s (x##\<omega>) = (if t < fst x then s \<in> ss else trace_in ss t (snd x) \<omega>)"
  by (cases x) (subst trace_in.simps; auto)

lemma trace_in_eq_lfp:
  "trace_in ss t = lfp (\<lambda>F s. \<lambda>(t', s')##\<omega> \<Rightarrow> if t < t' then s \<in> ss else F s' \<omega>)"
  unfolding trace_in_def by (intro arg_cong[where f=lfp] ext) (auto split: stream.splits)

lemma trace_in_shiftD: "trace_in ss t s \<omega> \<Longrightarrow> trace_in ss (t + t') s (smap (\<lambda>(t, s'). (t + t', s')) \<omega>)"
  by (induction rule: trace_in.induct) auto

lemma trace_in_shift[simp]: "trace_in ss t s (smap (\<lambda>(t, s'). (t + t', s')) \<omega>) \<longleftrightarrow> trace_in ss (t - t') s \<omega>"
  using trace_in_shiftD[of ss t s "smap (\<lambda>(t, s'). (t + t', s')) \<omega>" "- t'"]
    trace_in_shiftD[of ss "t - t'" s \<omega> t']
  by (auto simp add: stream.map_comp prod.case_eq_if)

lemma measurable_trace_in':
  "Measurable.pred (borel \<Otimes>\<^sub>M count_space UNIV \<Otimes>\<^sub>M T) (\<lambda>(t, s, \<omega>). trace_in ss t s \<omega>)"
    (is "?M (\<lambda>(t, s, \<omega>). trace_in ss t s \<omega>)")
proof -
  let ?F = "\<lambda>F. \<lambda>(t, s, (t', s')##\<omega>) \<Rightarrow> if t < t' then s \<in> ss else F (t, s', \<omega>)"
  have [measurable]: "Measurable.pred (count_space UNIV) (\<lambda>x. x \<in> ss)"
    by simp
  have "trace_in ss = (\<lambda>t s \<omega>. lfp ?F (t, s, \<omega>))"
    unfolding trace_in_def
    apply (subst lfp_arg)
    apply (subst lfp_rolling[where g="\<lambda>F t s \<omega>. F (t, s, \<omega>)"])
    subgoal by (auto simp: mono_def le_fun_def split: stream.splits)
    subgoal by (auto simp: mono_def le_fun_def split: stream.splits)
    subgoal
      by (intro arg_cong[where f=lfp])
         (auto simp: mono_def le_fun_def split_beta' not_less fun_eq_iff split: stream.splits intro!: arg_cong[where f=lfp])
    done
  then have eq: "(\<lambda>(t, s, \<omega>). trace_in ss t s \<omega>) = lfp ?F"
    by simp
  have "sup_continuous ?F"
    by (auto simp: sup_continuous_def fun_eq_iff split: stream.splits)
  then show ?thesis
    unfolding eq
  proof (rule measurable_lfp)
    fix F assume "?M F" then show "?M (?F F)"
      by measurable
  qed
qed

lemma measurable_trace_in[measurable (raw)]:
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M borel" "g \<in> M \<rightarrow>\<^sub>M count_space UNIV" "h \<in> M \<rightarrow>\<^sub>M T"
  shows "Measurable.pred M (\<lambda>x. trace_in ss (f x) (g x) (h x))"
  using measurable_compose[of "\<lambda>x. (f x, g x, h x)" M, OF _ measurable_trace_in'[of ss]] by simp

definition p :: "'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real"
where "p s s' t = \<P>(\<omega> in K.lim_stream (0, s). trace_in {s'} t s \<omega>)"

lemma p[measurable]: "(\<lambda>(s, t). p s s' t) \<in> (count_space UNIV \<Otimes>\<^sub>M borel) \<rightarrow>\<^sub>M borel"
proof -
  have *: "(SIGMA x:space (count_space UNIV \<Otimes>\<^sub>M borel). {\<omega> \<in> streams (space S). trace_in {s'} (snd x) (fst x) \<omega>}) =
    {x\<in>space ((count_space UNIV \<Otimes>\<^sub>M borel) \<Otimes>\<^sub>M T). trace_in {s'} (snd (fst x)) (fst (fst x)) (snd x)}"
    by (auto simp: space_pair_measure)

  note measurable_trace_at'[measurable]
  show ?thesis
    unfolding p_def[abs_def] split_beta'
    by (rule measure_measurable_prob_algebra2[where N=T])
       (auto simp: K.space_lim_stream * pred_def[symmetric]
                intro!: pred_count_space_const1 measurable_trace_at'[unfolded split_beta'])
qed

lemma p_nonpos: assumes "t \<le> 0" shows "p s s' t = of_bool (s = s')"
proof -
  have "AE \<omega> in K.lim_stream (0, s). trace_in {s'} t s \<omega> = (s = s')"
  proof (subst K.AE_lim_stream)
    show "AE y in K (0, s). AE \<omega> in K.lim_stream y. trace_in {s'} t s (y ## \<omega>) = (s = s')"
      using AE_K
    proof eventually_elim
      fix y :: "real \<times> 'a" assume "fst (0, s) < fst y \<and> snd y \<in> set_pmf (J (snd (0, s)))"
      with \<open>t\<le>0\<close> show "AE \<omega> in K.lim_stream y. trace_in {s'} t s (y ## \<omega>) = (s = s')"
        by (cases y) auto
    qed
  qed auto
  then have "p s s' t = \<P>(\<omega> in K.lim_stream (0, s). s = s')"
    unfolding p_def by (intro prob_space.prob_eq_AE K.prob_space_lim_stream) auto
  then show ?thesis
    using prob_space.prob_space[OF K.prob_space_lim_stream] by simp
qed

lemma p_0: "p s s' 0 = of_bool (s = s')"
  using p_nonpos[of 0] by simp

lemma in_sets_T[measurable (raw)]: "Measurable.pred T P \<Longrightarrow> {\<omega>. P \<omega>} \<in> sets T"
  unfolding pred_def by simp

lemma distr_id': "sets M = sets N \<Longrightarrow> distr M N (\<lambda>x. x) = M"
  by (subst distr_cong[of M M N M _ "\<lambda>x. x"] ) simp_all

lemma p_nonneg[simp]: "0 \<le> p s s' t"
  by (simp add: p_def)

lemma p_le_1[simp]: "p s s' t \<le> 1"
  unfolding p_def by (intro prob_space.prob_le_1 K.prob_space_lim_stream) simp

lemma p_eq:
  assumes "0 \<le> t"
  shows "p s s'' t = (of_bool (s = s'') + (LINT u:{0..t}|lborel. escape_rate s * exp (escape_rate s * u) * (LINT s'|J s. p s' s'' u))) / exp (t * escape_rate s)"
proof -
  have *: "(+) 0 = (\<lambda>x::real. x)"
    by auto
  interpret L: prob_space "K.lim_stream x" for x
    by (rule K.prob_space_lim_stream) simp
  interpret E: prob_space "exponential (escape_rate s)" for s
    by (intro escape_rate_pos prob_space_exponential)
  have "p s s'' t = emeasure (K.lim_stream (0, s)) {\<omega>\<in>space T. trace_in {s''} t s \<omega>}"
    by (simp add: p_def L.emeasure_eq_measure K.space_lim_stream space_stream_space del: in_space_T)
  also have "\<dots> = (\<integral>\<^sup>+y. emeasure (K.lim_stream y) {\<omega>\<in>space T. trace_in {s''} t s (y##\<omega>) } \<partial>K (0, s))"
    apply (subst K.lim_stream_eq[OF in_space_S])
    apply (subst emeasure_bind_prob_algebra[OF K_in_space])
    apply (measurable; fail)
    apply (measurable; fail)
    apply (subst bind_return_distr'[OF lim_stream_not_empty])
    apply (measurable; fail)
    apply (simp add: emeasure_distr)
    done
  also have "\<dots> = (\<integral>\<^sup>+y. indicator {t <..} (fst y) * of_bool (s = s'') + indicator {0<..t} (fst y) * p (snd y) s'' (t - fst y) \<partial>K (0, s))"
    apply (intro nn_integral_cong_AE)
    using AE_K
    apply eventually_elim
    subgoal for y
      using L.emeasure_space_1
      apply (cases y)
      apply (auto split: split_indicator simp del: in_space_T)
      subgoal for t' s2
        unfolding p_def L.emeasure_eq_measure[symmetric] K.space_lim_stream space_stream_space[symmetric]
        by (subst lim_0) (simp add: emeasure_distr)
      subgoal
        by (auto split: split_indicator cong: rev_conj_cong simp add: K.space_lim_stream space_stream_space simp del: in_space_T)
      done
    done
  also have "\<dots> = (\<integral>\<^sup>+u. \<integral>\<^sup>+s'. indicator {t <..} u * of_bool (s = s'') +
    indicator {0<..t} u * p s' s'' (t - u) \<partial>J s \<partial>exponential (escape_rate s))"
    unfolding K_def
    by (simp add: K_def measure_pmf.nn_integral_fst[symmetric] * distr_id' sets_exponential)
  also have "\<dots> = ennreal (exp (- t * escape_rate s) * of_bool (s = s'')) +
      (\<integral>\<^sup>+u. indicator {0<..t} u * \<integral>\<^sup>+s'. p s' s'' (t - u) \<partial>J s \<partial>exponential (escape_rate s))"
    using \<open>0\<le>t\<close> by (simp add: nn_integral_add nn_integral_cmult ennreal_indicator ennreal_mult emeasure_exponential_Ioi escape_rate_pos)
  also have "(\<integral>\<^sup>+u. indicator {0<..t} u * \<integral>\<^sup>+s'. p s' s'' (t - u) \<partial>J s \<partial>exponential (escape_rate s)) =
      (\<integral>\<^sup>+u. indicator {0<..t} u *\<^sub>R (LINT s'|J s. p s' s'' (t - u)) \<partial>exponential (escape_rate s))"
    by (simp add: measure_pmf.integrable_const_bound[of _ 1] nn_integral_eq_integral ennreal_mult ennreal_indicator)
  also have "\<dots> = (LINT u:{0<..t}|exponential (escape_rate s). (LINT s'|J s. p s' s'' (t - u)))"
    unfolding set_lebesgue_integral_def
    by (intro nn_integral_eq_integral E.integrable_const_bound[of _ 1] AE_I2)
       (auto intro!: mult_le_one measure_pmf.integral_le_const measure_pmf.integrable_const_bound[of _ 1])
  also have "\<dots> = (LINT u:{0<..t}|lborel. escape_rate s * exp (- escape_rate s * u) * (LINT s'|J s. p s' s'' (t - u)))"
    unfolding exponential_def set_lebesgue_integral_def
    by (subst integral_density)
       (auto simp: ac_simps exponential_density_def fun_eq_iff split: split_indicator
             simp del: integral_mult_right integral_mult_right_zero intro!: arg_cong2[where f="integral\<^sup>L"])
  also have "\<dots> = (LINT u:{0..t}|lborel. escape_rate s * exp (- escape_rate s * (t - u)) * (LINT s'|J s. p s' s'' u))"
    using AE_lborel_singleton[of 0] AE_lborel_singleton[of t] unfolding set_lebesgue_integral_def
    by (subst lborel_integral_real_affine[where t=t and c="-1"])
       (auto intro!: integral_cong_AE split: split_indicator)
  also have "\<dots> = exp (- t * escape_rate s) * escape_rate s * (LINT u:{0..t}|lborel. exp (escape_rate s * u) * (LINT s'|J s. p s' s'' u))"
    by (simp add: field_simps exp_diff exp_minus)
  finally show "p s s'' t = (of_bool (s = s'') + (LBINT u:{0..t}. escape_rate s * exp (escape_rate s * u) * (LINT s'|J s. p s' s'' u))) / exp (t * escape_rate s)"
    unfolding set_lebesgue_integral_def
    by (simp del: ennreal_plus add: ennreal_plus[symmetric] exp_minus field_simps)
qed

lemma continuous_on_p: "continuous_on A (p s s')"
proof -
  interpret E: prob_space "exponential (escape_rate s'')" for s''
    by (intro escape_rate_pos prob_space_exponential)
  have "continuous_on {..0} (p s s')"
    by (simp add: p_nonpos continuous_on_const cong: continuous_on_cong_simp)
  moreover have "continuous_on {0..} (p s s')"
  proof (subst continuous_on_cong[OF refl p_eq])
    let ?I = "\<lambda>t. escape_rate s * exp (escape_rate s * t) * (LINT s''|J s. p s'' s' t)"
    show "continuous_on {0..} (\<lambda>t. (of_bool (s = s') + (LBINT u:{0..t}. ?I u)) / exp (t * escape_rate s))"
    proof (intro continuous_intros continuous_on_LBINT[THEN continuous_on_subset])
      fix t :: real assume t: "0 \<le> t"
      then have "0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> exp (x * escape_rate s) * (LINT s''|J s. p s'' s' x) \<le> exp (t * escape_rate s) * 1" for x
        by (intro mult_mono) (auto intro!: mult_mono measure_pmf.integral_le_const measure_pmf.integrable_const_bound[of _ 1])
      with t show "set_integrable lborel {0..t} ?I"
        using escape_rate_pos[of s] unfolding set_integrable_def
        by (intro integrableI_bounded_set_indicator[where B="escape_rate s * exp (escape_rate s * t)"])
           (auto simp: field_simps)
    qed auto
  qed simp
  ultimately have "continuous_on ({0..} \<union> {..0}) (p s s')"
    by (intro continuous_on_closed_Un) auto
  also have "{0..} \<union> {..0::real} = UNIV" by auto
  finally show ?thesis
    by (rule continuous_on_subset) simp
qed

lemma p_vector_derivative: \<comment> \<open>Backward equation\<close>
  assumes "0 \<le> t"
  shows "(p s s' has_vector_derivative (LINT s''|count_space UNIV. R s s'' * p s'' s' t) - escape_rate s * p s s' t)
    (at t within {0..})"
    (is "(_ has_vector_derivative ?A) _")
proof -
  let ?I = "\<lambda>t. escape_rate s * exp (escape_rate s * t) * (LINT s''|J s. p s'' s' t)"
  let ?p = "\<lambda>t. (of_bool (s = s') + integral {0..t} ?I) * exp (t *\<^sub>R - escape_rate s)"

  { fix t :: real assume "0 \<le> t"
    have "p s s' t = (of_bool (s = s') + (LBINT u:{0..t}. ?I u)) * exp (- t * escape_rate s)"
      using p_eq[OF \<open>0 \<le> t\<close>, of s s'] by (simp add: exp_minus field_simps)
    also have "(LBINT u:{0..t}. ?I u) = integral {0..t} ?I"
    proof (intro set_borel_integral_eq_integral)
      have "0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> exp (x * escape_rate s) * (LINT s''|J s. p s'' s' x) \<le> exp (t * escape_rate s) * 1" for x
        by (intro mult_mono) (auto intro!: mult_mono measure_pmf.integral_le_const measure_pmf.integrable_const_bound[of _ 1])
      with \<open>0\<le>t\<close> show "set_integrable lborel {0..t} ?I"
        using escape_rate_pos[of s] unfolding set_integrable_def
        by (intro integrableI_bounded_set_indicator[where B="escape_rate s * exp (escape_rate s * t)"])
           (auto simp: field_simps)
    qed
    finally have "p s s' t = ?p t"
      by simp }
  note p_eq = this

  have at_eq: "at t within {0..} = at t within {0 .. t + 1}"
    by (intro at_within_nhd[where S="{..< t+1}"]) auto

  have c_I: "continuous_on {0..t + 1} ?I"
    by (intro continuous_intros continuous_on_LINT_pmf[where B=1] continuous_on_p) simp

  show ?thesis
  proof (subst has_vector_derivative_cong_ev)
    show "\<forall>\<^sub>F u in nhds t. u \<in> {0..} \<longrightarrow> p s s' u = ?p u" "p s s' t = ?p t"
      using \<open>0\<le>t\<close> by (simp_all add: p_eq)
    have "(?p has_vector_derivative escape_rate s * ((LINT s''|J s. p s'' s' t) - p s s' t)) (at t within {0..})"
      unfolding at_eq
      apply (intro refl derivative_eq_intros)
      apply rule
      apply (rule integral_has_vector_derivative[OF c_I])
      apply (simp add: \<open>0 \<le> t\<close>)
      apply rule
      apply (rule exp_scaleR_has_vector_derivative_right)
      apply (simp add: field_simps exp_minus p_eq \<open>0\<le>t\<close> split del: split_of_bool)
      done
    also have "escape_rate s * ((LINT s''|J s. p s'' s' t) - p s s' t) =
        (LINT s''|count_space UNIV. R s s'' * p s'' s' t) - escape_rate s * p s s' t"
      using escape_rate_pos[of s]
      by (simp add: measure_pmf_eq_density integral_density J.rep_eq field_simps)
    finally show "(?p has_vector_derivative  ?A) (at t within {0..})" .
  qed
qed

coinductive wf_times :: "real \<Rightarrow> (real \<times> 'a) stream \<Rightarrow> bool"
where
  "t < t' \<Longrightarrow> wf_times t' \<omega> \<Longrightarrow> wf_times t ((t', s') ## \<omega>)"

lemma wf_times_simp[simp]: "wf_times t (x ## \<omega>) \<longleftrightarrow> t < fst x \<and> wf_times (fst x) \<omega>"
  by (cases x) (subst wf_times.simps; simp)

lemma trace_in_merge_at:
  assumes \<omega>': "wf_times t' \<omega>'"
  shows "trace_in ss t x (merge_at \<omega> t' \<omega>') \<longleftrightarrow>
    (if t < t' then trace_in ss t x \<omega> else \<exists>y. trace_in {y} t' x \<omega> \<and> trace_in ss t y \<omega>')"
    (is "?merge \<longleftrightarrow> ?cases")
proof safe
  assume ?merge from this \<omega>' show ?cases
  proof (induction \<omega>\<equiv>"merge_at \<omega> t' \<omega>'" arbitrary: \<omega> \<omega>')
    case (1 j s' y \<omega>'') then show ?case
      by (cases \<omega>) (auto split: if_splits)
  next
    case (2 j x \<omega>' s' \<omega> \<omega>'') then show ?case
      by (cases \<omega>) (auto split: if_splits)
  qed
next
  assume ?cases then show ?merge
  proof (split if_split_asm)
    assume "trace_in ss t x \<omega>" "t < t'" from this \<omega>' show ?thesis
    proof induction
      case 1 then show ?case
        by (cases \<omega>') auto
    qed auto
  next
    assume "\<exists>y. trace_in {y} t' x \<omega> \<and> trace_in ss t y \<omega>'" "\<not> t < t'"
    then obtain y where "trace_in {y} t' x \<omega>" "trace_in ss t y \<omega>'" "t' \<le> t"
      by auto
    from this \<omega>' show ?thesis
      by induction auto
  qed
qed

lemma AE_lim_wf_times: "AE \<omega> in K.lim_stream (t, s). wf_times t \<omega>"
  using AE_lim_stream
proof eventually_elim
  fix \<omega> assume *: "\<forall>i. snd (((t, s) ## \<omega>) !! i) \<in> DTMC.acc `` {snd (t, s)} \<and>
             snd (\<omega> !! i) \<in> J (snd (((t, s) ## \<omega>) !! i)) \<and>
             fst (((t, s) ## \<omega>) !! i) < fst (\<omega> !! i)"
  have "(t ## smap fst \<omega>) !! i < fst (\<omega> !! i)" for i
    using *[THEN spec, of i] by (cases i) auto
  then show "wf_times t \<omega>"
  proof (coinduction arbitrary: t \<omega>)
    case wf_times from this[THEN spec, of 0] this[THEN spec, of "Suc i" for i]  show ?case
      by (cases \<omega>) auto
  qed
qed

lemma wf_times_shiftD: "wf_times t' (smap (\<lambda>(t', y). (t' + t, y)) \<omega>) \<Longrightarrow> wf_times (t' - t) \<omega>"
  apply (coinduction arbitrary: t' t \<omega>)
  subgoal for t' t \<omega>
    apply (cases \<omega>; cases "shd \<omega>")
    apply (auto simp: )
    subgoal for \<omega>' j x
      by (rule exI[of _ "j + t"]) auto
    done
  done

lemma wf_times_shift[simp]: "wf_times t' (smap (\<lambda>(t', y). (t' + t, y)) \<omega>) = wf_times (t' - t) \<omega>"
  using wf_times_shiftD[of "t' - t" "-t" "smap (\<lambda>(t', y). (t' + t, y)) \<omega>"]
  by (auto simp: stream.map_comp stream.case_eq_if prod.case_eq_if wf_times_shiftD)

lemma trace_in_unique: "trace_in {y1} t x \<omega> \<Longrightarrow> trace_in {y2} t x \<omega> \<Longrightarrow> y1 = y2"
  by (induction rule: trace_in.induct) auto

lemma trace_at_eq: "trace_in {z} t x \<omega> \<Longrightarrow> trace_at x \<omega> t = z"
  by (induction rule: trace_in.induct) auto

lemma AE_lim_acc: "AE \<omega> in K.lim_stream (t, x). \<forall>t z. trace_in {z} t x \<omega> \<longrightarrow> (x, z) \<in> DTMC.acc"
  using AE_lim_stream
proof (eventually_elim, safe)
  fix t' z \<omega> assume *: "\<forall>i. snd (((t, x) ## \<omega>) !! i) \<in> DTMC.acc `` {snd (t, x)} \<and>
    snd (\<omega> !! i) \<in> J (snd (((t, x) ## \<omega>) !! i)) \<and> fst (((t, x) ## \<omega>) !! i) < fst (\<omega> !! i)"
    and t: "trace_in {z} t' x \<omega>"
  define X where "X = DTMC.acc `` {x}"
  have "(x ## smap snd \<omega>) !! i \<in> X" for i
    using *[THEN spec, of i] by (cases i) (auto simp: X_def)
  from t this have "z \<in> X"
  proof induction
    case (1 j y x \<omega>) with "1.prems"[of 0] show ?case
      by simp
  next
    case (2 j y \<omega> x) with "2.prems"[of "Suc i" for i] show ?case
      by simp
  qed
  then show "(x, z) \<in> DTMC.acc"
    by (simp add: X_def)
qed

lemma p_add:
  assumes "0 \<le> t" "0 \<le> t'"
  shows "p x y (t + t') = (LINT z|count_space (DTMC.acc``{x}). p x z t * p z y t')"
proof -
  interpret L: prob_space "K.lim_stream xy" for xy
    by (rule K.prob_space_lim_stream) simp
  interpret A: sigma_finite_measure "count_space (DTMC.acc``{x})"
    by (intro sigma_finite_measure_count_space_countable DTMC.countable_acc) simp
  interpret LA: pair_sigma_finite "count_space (DTMC.acc``{x})" "K.lim_stream xy" for xy
    by unfold_locales

  have "p x y (t + t') = (\<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+\<omega>'. indicator {\<omega>\<in>space T. trace_in {y} (t + t') x \<omega>} (merge_at \<omega> t \<omega>')
    \<partial>K.lim_stream (t, trace_at x \<omega> t) \<partial>K.lim_stream (0, x))"
    unfolding p_def L.emeasure_eq_measure[symmetric]
    apply (subst lim_time_split[OF \<open>0 \<le> t\<close>])
    apply (subst emeasure_bind[OF lim_stream_not_empty measurable_prob_algebraD])
    apply (measurable; fail)
    apply (measurable; fail)
    apply (intro nn_integral_cong)
    apply (subst emeasure_bind[OF lim_stream_not_empty measurable_prob_algebraD])
    apply (measurable; fail)
    apply (measurable; fail)
    apply (simp add: in_space_lim_stream)
    done
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+\<omega>'. indicator {\<omega>\<in>space T. trace_in {y} (t + t') x \<omega>} (merge_at \<omega> t (smap (\<lambda>(t'', s). (t'' + t, s)) \<omega>'))
    \<partial>K.lim_stream (0, trace_at x \<omega> t) \<partial>K.lim_stream (0, x))"
    unfolding lim_0[of t] by (subst nn_integral_distr) (measurable; fail)+
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+\<omega>'. of_bool (\<exists>z\<in>DTMC.acc``{x}. trace_in {z} t x \<omega> \<and> trace_in {y} t' z \<omega>')
    \<partial>K.lim_stream (0, trace_at x \<omega> t) \<partial>K.lim_stream (0, x))"
    apply (rule nn_integral_cong_AE)
    using AE_lim_wf_times AE_lim_acc
    apply eventually_elim
    subgoal premises \<omega> for \<omega>
      apply (rule nn_integral_cong_AE)
      using AE_lim_wf_times AE_lim_acc
      apply eventually_elim
      using \<omega> assms
      apply (auto simp add: trace_in_merge_at indicator_def Bex_def)
      done
    done
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+\<omega>'. \<integral>\<^sup>+z. of_bool (trace_in {z} t x \<omega> \<and> trace_in {y} t' z \<omega>')
    \<partial>count_space (DTMC.acc``{x}) \<partial>K.lim_stream (0, trace_at x \<omega> t) \<partial>K.lim_stream (0, x))"
    by (intro nn_integral_cong of_bool_Bex_eq_nn_integral) (auto dest: trace_in_unique)
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+z. \<integral>\<^sup>+\<omega>'. of_bool (trace_in {z} t x \<omega> \<and> trace_in {y} t' z \<omega>')
    \<partial>K.lim_stream (0, trace_at x \<omega> t) \<partial>count_space (DTMC.acc``{x}) \<partial>K.lim_stream (0, x))"
    apply (subst LA.Fubini')
    apply (subst measurable_split_conv)
    apply (rule measurable_compose_countable'[OF _ measurable_fst])
    apply (auto simp: DTMC.countable_acc)
    done
  also have "\<dots> = (\<integral>\<^sup>+z. \<integral>\<^sup>+ \<omega>. of_bool (trace_in {z} t x \<omega>) * \<integral>\<^sup>+\<omega>'. of_bool (trace_in {y} t' z \<omega>')
    \<partial>K.lim_stream (0, z) \<partial>K.lim_stream (0, x) \<partial>count_space (DTMC.acc``{x}))"
    apply (subst LA.Fubini')
    apply (subst measurable_split_conv)
    apply (rule measurable_compose_countable'[OF _ measurable_fst])
    apply (rule nn_integral_measurable_subprob_algebra2)
    apply (measurable; fail)
    apply (rule measurable_prob_algebraD)
    apply (auto simp: DTMC.countable_acc trace_at_eq intro!: nn_integral_cong)
    done
  also have "\<dots> = (\<integral>\<^sup>+z. (\<integral>\<^sup>+ \<omega>. of_bool (trace_in {z} t x \<omega>)\<partial>K.lim_stream (0, x)) *
      (\<integral>\<^sup>+\<omega>'. of_bool (trace_in {y} t' z \<omega>') \<partial>K.lim_stream (0, z)) \<partial>count_space (DTMC.acc``{x}))"
     by (auto intro!: nn_integral_cong simp: nn_integral_multc)
  also have "\<dots> = (\<integral>\<^sup>+z. ennreal (p x z t) * ennreal (p z y t') \<partial>count_space (DTMC.acc``{x}))"
    unfolding p_def L.emeasure_eq_measure[symmetric]
    by (auto intro!: nn_integral_cong arg_cong2[where f="(*)"]
             simp: nn_integral_indicator[symmetric] simp del: nn_integral_indicator )
  finally have "(\<integral>\<^sup>+z. p x z t * p z y t' \<partial>count_space (DTMC.acc``{x})) = p x y (t + t')"
    by (simp add: ennreal_mult)
  then show ?thesis
    by (subst (asm) nn_integral_eq_integrable) auto
qed

end

end
