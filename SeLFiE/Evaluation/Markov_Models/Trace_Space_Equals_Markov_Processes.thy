(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

subsection \<open>Trace Space equal to Markov Chains\<close>

theory Trace_Space_Equals_Markov_Processes
  imports Discrete_Time_Markov_Chain
begin

text \<open>
  We can construct for each time-homogeneous discrete-time Markov chain a corresponding
  probability space using @{theory Markov_Models.Discrete_Time_Markov_Chain}. The constructed probability space
  has the same probabilities.
\<close>

locale Time_Homogeneous_Discrete_Markov_Process = M?: prob_space +
  fixes S :: "'s set" and X :: "nat \<Rightarrow> 'a \<Rightarrow> 's"
  assumes X [measurable]: "\<And>t. X t \<in> measurable M (count_space UNIV)"
  assumes S: "countable S" "\<And>n. AE x in M. X n x \<in> S"
  assumes MC: "\<And>n s s'.
    \<P>(\<omega> in M. \<forall>t\<le>n. X t \<omega> = s t ) \<noteq> 0 \<Longrightarrow>
    \<P>(\<omega> in M. X (Suc n) \<omega> = s' \<bar> \<forall>t\<le>n. X t \<omega> = s t ) =
    \<P>(\<omega> in M. X (Suc n) \<omega> = s' \<bar> X n \<omega> = s n )"
  assumes TH: "\<And>n m s t.
    \<P>(\<omega> in M. X n \<omega> = t) \<noteq> 0 \<Longrightarrow> \<P>(\<omega> in M. X m \<omega> = t) \<noteq> 0 \<Longrightarrow>
    \<P>(\<omega> in M. X (Suc n) \<omega> = s \<bar> X n \<omega> = t) = \<P>(\<omega> in M. X (Suc m) \<omega> = s \<bar> X m \<omega> = t)"
begin

context
begin

interpretation pmf_as_measure .

lift_definition I :: "'s pmf" is "distr M (count_space UNIV) (X 0)"
proof -
  let ?X = "distr M (count_space UNIV) (X 0)"
  interpret X: prob_space ?X
    by (auto simp: prob_space_distr)
  have "AE x in ?X. measure ?X {x} \<noteq> 0"
    using S by (subst X.AE_support_countable) (auto simp: AE_distr_iff intro!: exI[of _ S])
  then show "prob_space ?X \<and> sets ?X = UNIV \<and> (AE x in ?X. measure ?X {x} \<noteq> 0)"
    by (simp add: prob_space_distr AE_support_countable)
qed

lemma I_in_S:
  assumes "pmf I s \<noteq> 0" shows "s \<in> S"
proof -
  from \<open>pmf I s \<noteq> 0\<close> have "0 \<noteq> \<P>(x in M. X 0 x = s)"
    by transfer (auto simp: measure_distr vimage_def Int_def conj_commute)
  also have "\<P>(x in M. X 0 x = s) = \<P>(x in M. X 0 x = s \<and> s \<in> S)"
    using S(2)[of 0] by (intro M.finite_measure_eq_AE) auto
  finally show ?thesis
    by (cases "s \<in> S") auto
qed

lift_definition K :: "'s \<Rightarrow> 's pmf" is
  "\<lambda>s. with (\<lambda>n. \<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0)
     (\<lambda>n. distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n)))
     (uniform_measure (count_space UNIV) {s})"
proof (rule withI)
  fix s n assume *: "\<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0"
  let ?D = "distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n))"
  have D: "prob_space ?D"
    by (intro prob_space.prob_space_distr prob_space_uniform_measure)
       (auto simp: M.emeasure_eq_measure *)
  then interpret D: prob_space ?D .
  have sets_D: "sets ?D = UNIV"
    by simp
  moreover have "AE x in ?D. measure ?D {x} \<noteq> 0"
    unfolding D.AE_support_countable[OF sets_D]
  proof (intro exI[of _ S] conjI)
    show "countable S" by (rule S)
    show "AE x in ?D. x \<in> S"
      using * S(2)[of "Suc n"] by (auto simp add: AE_distr_iff AE_uniform_measure M.emeasure_eq_measure)
  qed
  ultimately show "prob_space ?D \<and> sets ?D = UNIV \<and> (AE x in ?D. measure ?D {x} \<noteq> 0)"
    using D by blast
qed (auto intro!: prob_space_uniform_measure AE_uniform_measureI)

lemma pmf_K:
  assumes n: "0 < \<P>(\<omega> in M. X n \<omega> = s)"
  shows "pmf (K s) t = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
proof (transfer fixing: n s t)
  let ?P = "\<lambda>n. \<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0"
  let ?D = "\<lambda>n. distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n))"
  let ?U = "uniform_measure (count_space UNIV) {s}"
  show "measure (with ?P ?D ?U) {t} = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
  proof (rule withI)
    fix n' assume "?P n'"
    moreover have "X (Suc n') -` {t} \<inter> space M = {x\<in>space M. X (Suc n') x = t}"
      by auto
    ultimately show "measure (?D n') {t} = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
      using n M.measure_uniform_measure_eq_cond_prob[of "\<lambda>x. X (Suc n') x = t" "\<lambda>x. X n' x = s"]
      by (auto simp: measure_distr M.emeasure_eq_measure simp del: measure_uniform_measure intro!: TH)
  qed (insert n, simp)
qed

lemma pmf_K2:
  "(\<And>n. \<P>(\<omega> in M. X n \<omega> = s) = 0) \<Longrightarrow> pmf (K s) t = indicator {t} s"
  apply (transfer fixing: s t)
  apply (rule withI)
  apply (auto split: split_indicator)
  done

end

sublocale K: MC_syntax K .

lemma bind_I_K_eq_M: "K.T' I = distr M K.S (\<lambda>\<omega>. to_stream (\<lambda>n. X n \<omega>))" (is "_ = ?D")
proof (rule stream_space_eq_sstart)
  note streams_sets[measurable]
  note measurable_abs_UNIV[measurable (raw)]
  note sstart_sets[measurable]

  { fix s assume "s \<in> S"
    from K.AE_T_enabled[of s] have "AE \<omega> in K.T s. \<omega> \<in> streams S"
    proof eventually_elim
      fix \<omega> assume "K.enabled s \<omega>" from this \<open>s\<in>S\<close> show "\<omega> \<in> streams S"
      proof (coinduction arbitrary: s \<omega>)
        case streams
        then have 1: "pmf (K s) (shd \<omega>) \<noteq> 0"
          by (simp add: K.enabled.simps[of s] set_pmf_iff)
        have "shd \<omega> \<in> S"
        proof cases
          assume "\<exists>n. 0 < \<P>(\<omega> in M. X n \<omega> = s)"
          then obtain n where "0 < \<P>(\<omega> in M. X n \<omega> = s)" by auto
          with 1 have 2: "\<P>(\<omega>' in M. X (Suc n) \<omega>' = shd \<omega> \<and> X n \<omega>' = s) \<noteq> 0"
            by (simp add: pmf_K cond_prob_def)
          show "shd \<omega> \<in> S"
          proof (rule ccontr)
            assume "shd \<omega> \<notin> S"
            with S(2)[of "Suc n"] have "\<P>(\<omega>' in M. X (Suc n) \<omega>' = shd \<omega> \<and> X n \<omega>' = s) = 0"
              by (intro M.prob_eq_0_AE) auto
            with 2 show False by contradiction
          qed
        next
          assume "\<not> (\<exists>n. 0 < \<P>(\<omega> in M. X n \<omega> = s))"
          then have "pmf (K s) (shd \<omega>) = indicator {shd \<omega>} s"
            by (intro pmf_K2) (auto simp: not_less measure_le_0_iff)
          with 1 \<open>s\<in>S\<close> show ?thesis
            by (auto split: split_indicator_asm)
        qed
        with streams show ?case
          by (cases \<omega>) (auto simp: K.enabled.simps[of s])
      qed
    qed }
  note AE_streams = this

  show "prob_space (K.T' I)"
    by (rule K.prob_space_T')
  show "prob_space ?D"
    by (rule M.prob_space_distr) simp

  show "AE x in K.T' I. x \<in> streams S"
    by (auto simp add: K.AE_T' set_pmf_iff I_in_S AE_distr_iff streams_Stream intro!: AE_streams)
  show "AE x in ?D. x \<in> streams S"
    by (simp add: AE_distr_iff to_stream_in_streams AE_all_countable S)
  show "sets (K.T' I) = sets (stream_space (count_space UNIV))"
    by (simp add: K.sets_T')
  show "sets ?D = sets (stream_space (count_space UNIV))"
    by simp

  fix xs' assume "xs' \<noteq> []" "xs' \<in> lists S"
  then obtain s xs where xs': "xs' = s # xs" and s: "s \<in> S" and xs: "xs \<in> lists S"
    by (auto simp: neq_Nil_conv del: in_listsD)

  have "emeasure (K.T' I) (sstart S xs') = (\<integral>\<^sup>+s. emeasure (K.T s) {\<omega>\<in>space K.S. s ## \<omega> \<in> sstart S xs'} \<partial>I)"
    by (rule K.emeasure_T') measurable
  also have "\<dots> = (\<integral>\<^sup>+s'. emeasure (K.T s) (sstart S xs) * indicator {s} s' \<partial>I)"
    by (intro arg_cong2[where f=emeasure] nn_integral_cong)
       (auto split: split_indicator simp: emeasure_distr vimage_def space_stream_space neq_Nil_conv xs')
  also have "\<dots> = pmf I s * emeasure (K.T s) (sstart S xs)"
    by (auto simp add: max_def emeasure_pmf_single intro: mult_ac)
  also have "emeasure (K.T s) (sstart S xs) = ennreal (\<Prod>i<length xs. pmf (K ((s#xs)!i)) (xs!i))"
    using xs s
  proof (induction arbitrary: s)
    case Nil then show ?case
      by (simp add: K.T.emeasure_eq_1_AE AE_streams)
  next
    case (Cons t xs)
    have "emeasure (K.T s) (sstart S (t # xs)) =
      emeasure (K.T s) {x\<in>space (K.T s). shd x = t \<and> stl x \<in> sstart S xs}"
      by (intro arg_cong2[where f=emeasure]) (auto simp: space_stream_space)
    also have "\<dots> = (\<integral>\<^sup>+t'. emeasure (K.T t') {x\<in>space K.S. t' = t \<and> x \<in> sstart S xs} \<partial>K s)"
      by (subst K.emeasure_Collect_T) auto
    also have "\<dots> = (\<integral>\<^sup>+t'. emeasure (K.T t) (sstart S xs) * indicator {t} t' \<partial>K s)"
      by (intro nn_integral_cong) (auto split: split_indicator simp: space_stream_space)
    also have "\<dots> = emeasure (K.T t) (sstart S xs) * pmf (K s) t"
      by (simp add: emeasure_pmf_single max_def)
    finally show ?case
      by (simp add: lessThan_Suc_eq_insert_0 zero_notin_Suc_image prod.reindex Cons
        prod_nonneg ennreal_mult[symmetric])
  qed
  also have "pmf I s * ennreal (\<Prod>i<length xs. pmf (K ((s#xs)!i)) (xs!i)) =
    \<P>(x in M. \<forall>i\<le>length xs. X i x = (s # xs) ! i)"
    using xs s
  proof (induction xs rule: rev_induct)
    case Nil
    have "pmf I s = prob {x \<in> space M. X 0 x = s}"
      by transfer (simp add: vimage_def Int_def measure_distr conj_commute)
    then show ?case
      by simp
  next
    case (snoc t xs)
    let ?l = "length xs" and ?lt = "length (xs @ [t])" and ?xs' = "s # xs @ [t]"
    have "ennreal (pmf I s) * (\<Prod>i<?lt. pmf (K ((?xs') ! i)) ((xs @ [t]) ! i)) =
      (ennreal (pmf I s) * (\<Prod>i<?l. pmf (K ((s # xs) ! i)) (xs ! i))) * pmf (K ((s # xs) ! ?l)) t"
      by (simp add: lessThan_Suc mult_ac nth_append append_Cons[symmetric] prod_nonneg ennreal_mult[symmetric]
               del: append_Cons)
    also have "\<dots> = \<P>(x in M. \<forall>i\<le>?l. X i x = (s # xs) ! i) * pmf (K ((s # xs) ! ?l)) t"
      using snoc by (simp add: ennreal_mult[symmetric])
    also have "\<dots> = \<P>(x in M. \<forall>i\<le>?lt. X i x = (?xs') ! i)"
    proof cases
      assume "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) = 0"
      moreover have "\<P>(x in M. \<forall>i\<le>?lt. X i x = (?xs') ! i) \<le> \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      moreover have "\<P>(x in M. \<forall>i\<le>?l. X i x = (s # xs) ! i) \<le> \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      ultimately show ?thesis
        by (simp add: measure_le_0_iff)
    next
      assume "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) \<noteq> 0"
      then have *: "0 < \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        unfolding less_le by simp
      moreover have "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) \<le> \<P>(\<omega> in M. X ?l \<omega> = (s # xs) ! ?l)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      ultimately have "\<P>(\<omega> in M. X ?l \<omega> = (s # xs) ! ?l) \<noteq> 0"
        by auto
      then have "pmf (K ((s # xs) ! ?l)) t = \<P>(\<omega> in M. X ?lt \<omega> = ?xs' ! ?lt \<bar> X ?l \<omega> = (s # xs) ! ?l)"
        by (subst pmf_K) (auto simp: less_le)
      also have "\<dots> = \<P>(\<omega> in M. X ?lt \<omega> = ?xs' ! ?lt \<bar> \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        using * MC[of ?l "\<lambda>i. (s # xs) ! i" "?xs' ! ?lt"] by simp
      also have "\<dots> = \<P>(\<omega> in M. \<forall>i\<le>?lt. X i \<omega> = ?xs' ! i) / \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        unfolding cond_prob_def
        by (intro arg_cong2[where f="(/)"] arg_cong2[where f=measure]) (auto simp: nth_Cons nth_append split: nat.splits)
      finally show ?thesis
        using * by simp
    qed
    finally show ?case .
  qed
  also have "\<dots> = emeasure ?D (sstart S xs')"
  proof -
    have "AE x in M. \<forall>i. X i x \<in> S"
      using S(2) by (simp add: AE_all_countable)
    then have "AE x in M. (\<forall>i\<le>length xs. X i x = (s # xs) ! i) = (to_stream (\<lambda>n. X n x) \<in> sstart S xs')"
    proof eventually_elim
      fix x assume "\<forall>i. X i x \<in> S"
      then have "to_stream (\<lambda>n. X n x) \<in> streams S"
        by (auto simp: streams_iff_snth to_stream_def)
      then show "(\<forall>i\<le>length xs. X i x = (s # xs) ! i) = (to_stream (\<lambda>n. X n x) \<in> sstart S xs')"
        by (simp add: sstart_eq xs' to_stream_def less_Suc_eq_le del: sstart.simps(1) in_sstart)
    qed
    then show ?thesis
      by (auto simp: emeasure_distr M.emeasure_eq_measure intro!: M.finite_measure_eq_AE)
  qed
  finally show "emeasure (K.T' I) (sstart S xs') = emeasure ?D (sstart S xs')" .
qed (rule S)

end

lemma (in MC_syntax) is_THDTMC:
  fixes I :: "'s pmf"
  defines "U \<equiv> (SIGMA s:UNIV. K s)\<^sup>* `` I"
  shows "Time_Homogeneous_Discrete_Markov_Process (T' I) U (\<lambda>n \<omega>. \<omega> !! n)"
proof -
  have [measurable]: "U \<in> sets (count_space UNIV)"
    by auto

  interpret prob_space "T' I"
    by (rule prob_space_T')

  { fix s t I
    have "\<And>t s. \<P>(\<omega> in T s. s = t) = indicator {t} s"
      using T.prob_space by (auto split: split_indicator)
    moreover then have "\<And>t t' s. \<P>(\<omega> in T s. shd \<omega> = t' \<and> s = t) = pmf (K t) t' * indicator {t} s"
      by (subst prob_T) (auto split: split_indicator simp: pmf.rep_eq)
    ultimately have "\<P>(\<omega> in T' I. shd (stl \<omega>) = t \<and> shd \<omega> = s) = \<P>(\<omega> in T' I. shd \<omega> = s) * pmf (K s) t"
      by (simp add: prob_T' pmf.rep_eq) }
  note start_eq = this

  { fix n s t assume "\<P>(\<omega> in T' I. \<omega> !! n = s) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<omega> !! (Suc n) = t \<and> \<omega> !! n = s) = \<P>(\<omega> in T' I. \<omega> !! n = s) * pmf (K s) t"
    proof (induction n arbitrary: I)
      case (Suc n) then show ?case
        by (subst (1 2) prob_T') (simp_all del: space_T add: T_eq_T')
    qed (simp add: start_eq)
    ultimately have "\<P>(\<omega> in T' I. stl \<omega> !! n = t \<bar> \<omega> !! n = s) = pmf (K s) t"
      by (simp add: cond_prob_def field_simps) }
  note TH = this

  { fix n \<omega>' t assume "\<P>(\<omega> in T' I. \<forall>i\<le>n. \<omega> !! i = \<omega>' i) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<omega> !! (Suc n) = t \<and> (\<forall>i\<le>n. \<omega> !! i = \<omega>' i)) =
      \<P>(\<omega> in T' I. \<forall>i\<le>n. \<omega> !! i = \<omega>' i) * pmf (K (\<omega>' n)) t"
    proof (induction n arbitrary: I \<omega>')
      case (Suc n)
      have *[simp]: "\<And>s P. measure (T' (K s)) {x. s = \<omega>' 0 \<and> P x} =
        measure (T' (K (\<omega>' 0))) {x. P x} * indicator {\<omega>' 0} s"
        by (auto split: split_indicator)
      from Suc[of _ "\<lambda>i. \<omega>' (Suc i)"] show ?case
        by (subst (1 2) prob_T')
           (simp_all add: T_eq_T' all_Suc_split[where P="\<lambda>i. i \<le> Suc n \<longrightarrow> Q i" for n Q] conj_commute conj_left_commute sets_eq_imp_space_eq[OF sets_T'])
    qed (simp add: start_eq)
    ultimately have "\<P>(\<omega> in T' I. stl \<omega> !! n = t \<bar> \<forall>i\<le>n. \<omega> !! i = \<omega>' i) = pmf (K (\<omega>' n)) t"
      by (simp add: cond_prob_def field_simps) }
  note MC = this

  { fix n \<omega>' assume "\<P>(\<omega> in T' I. \<forall>t\<le>n. \<omega> !! t = \<omega>' t) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<forall>t\<le>n. \<omega> !! t = \<omega>' t) \<le> \<P>(\<omega> in T' I. \<omega> !! n = \<omega>' n)"
      by (auto intro!: finite_measure_mono_AE simp: sets_T' sets_eq_imp_space_eq[OF sets_T'])
    ultimately have "\<P>(\<omega> in T' I. \<omega> !! n = \<omega>' n) \<noteq> 0"
      by (auto simp: neq_iff not_less measure_le_0_iff) }
  note MC' = this

  show ?thesis
  proof
    show "countable U"
      unfolding U_def by (rule countable_reachable countable_Image countable_set_pmf)+
    show "\<And>t. (\<lambda>\<omega>. \<omega> !! t) \<in> measurable (T' I) (count_space UNIV)"
      by (subst measurable_cong_sets[OF sets_T' refl]) simp
  next
    fix n
    have "\<forall>x\<in>I. AE y in T x. (x ## y) !! n \<in> U"
      unfolding U_def
    proof (induction n arbitrary: I)
      case 0 then show ?case
        by auto
    next
      case (Suc n)
      { fix x assume "x \<in> I"
        have "AE y in T x. y !! n \<in> (SIGMA x:UNIV. K x)\<^sup>* `` K x"
          apply (subst AE_T_iff)
          apply (rule measurable_compose[OF measurable_snth], simp)
          apply (rule Suc)
          done
        moreover have "(SIGMA x:UNIV. K x)\<^sup>* `` K x \<subseteq> (SIGMA x:UNIV. K x)\<^sup>* `` I"
          using \<open>x \<in> I\<close> by (auto intro: converse_rtrancl_into_rtrancl)
        ultimately have "AE y in T x. y !! n \<in> (SIGMA x:UNIV. K x)\<^sup>* `` I"
          by (auto simp: subset_eq) }
      then show ?case
        by simp
    qed
    then show "AE x in T' I. x !! n \<in> U"
      by (simp add: AE_T')
  qed (simp_all add: TH MC MC')
qed

end
