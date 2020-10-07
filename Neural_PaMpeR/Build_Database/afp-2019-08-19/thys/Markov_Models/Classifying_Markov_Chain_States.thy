section \<open>Classifying Markov Chain States\<close>

theory Classifying_Markov_Chain_States
  imports
    "HOL-Computational_Algebra.Group_Closure"
    Discrete_Time_Markov_Chain
begin

lemma eventually_mult_Gcd:
  fixes S :: "nat set"
  assumes S: "\<And>s t. s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> s + t \<in> S"
  assumes s: "s \<in> S" "s > 0"
  shows "eventually (\<lambda>m. m * Gcd S \<in> S) sequentially"
proof -
  define T where "T = insert 0 (int ` S)"
  with s S have "int s \<in> T" "0 \<in> T" and T: "r \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> r + t \<in> T" for r t
    by (auto simp del: of_nat_add simp add: of_nat_add [symmetric])
  have "Gcd T \<in> group_closure T"
    by (rule Gcd_in_group_closure)
  also have "group_closure T = {s - t | s t. s \<in> T \<and> t \<in> T}"
  proof (auto intro: group_closure.base group_closure.diff)
    fix x assume "x \<in> group_closure T"
    then show "\<exists>s t. x = s - t \<and> s \<in> T \<and> t \<in> T"
    proof induction
      case (base x) with \<open>0 \<in> T\<close> show ?case
        apply (rule_tac x=x in exI)
        apply (rule_tac x=0 in exI)
        apply auto
        done
    next
      case (diff x y)
      then obtain a b c d where
        "a \<in> T" "b \<in> T" "x = a - b"
        "c \<in> T" "d \<in> T" "y = c - d"
        by auto
      then show ?case
        apply (rule_tac x="a + d" in exI)
        apply (rule_tac x="b + c" in exI)
        apply (auto intro: T)
        done
    qed
  qed
  finally obtain s' t' :: int
    where "s' \<in> T" "t' \<in> T" "Gcd T = s' - t'"
    by blast
  moreover define s and t where "s = nat s'" and "t = nat t'"
  moreover have "int (Gcd S) = - int t \<longleftrightarrow> S \<subseteq> {0} \<and> t = 0"
    by auto (metis Gcd_dvd_nat dvd_0_right dvd_antisym nat_int nat_zminus_int) 
  ultimately have 
    st: "s = 0 \<or> s \<in> S" "t = 0 \<or> t \<in> S" and Gcd_S: "Gcd S = s - t"
    using T_def by safe simp_all
  with s
  have "t < s"
    by (rule_tac ccontr) auto

  { fix s n have "0 < n \<Longrightarrow> s \<in> S \<Longrightarrow> n * s \<in> S"
    proof (induct n)
      case (Suc n) then show ?case
        by (cases n) (auto intro: S)
    qed simp }
  note cmult_S = this

  show ?thesis
    unfolding eventually_sequentially
  proof cases
    assume "s = 0 \<or> t = 0"
    with st Gcd_S s have *: "Gcd S \<in> S"
      by (auto simp: int_eq_iff)
    then show "\<exists>N. \<forall>n\<ge>N. n * Gcd S \<in> S" by (auto intro!: exI[of _ 1] cmult_S)
  next
    assume "\<not> (s = 0 \<or> t = 0)"
    with st have "s \<in> S" "t \<in> S" "t \<noteq> 0" by auto
    then have "Gcd S dvd t" by auto
    then obtain a where a: "t = Gcd S * a" ..
    with \<open>t \<noteq> 0\<close> have "0 < a" by auto

    show "\<exists>N. \<forall>n\<ge>N. n * Gcd S \<in> S"
    proof (safe intro!: exI[of _ "a * a"])
      fix n
      define m where "m = (n - a * a) div a"
      define r where "r = (n - a * a) mod a"
      with \<open>0 < a\<close> have "r < a" by simp
      moreover define am where "am = a + m"
      ultimately have "r < am" by simp
      assume "a * a \<le> n" then have n: "n = a * a + (m * a + r)"
        unfolding m_def r_def by simp
      have "n * Gcd S = am * t + r * Gcd S"
        unfolding n a by (simp add: field_simps am_def)
      also have "\<dots> = r * s + (am - r) * t"
        unfolding \<open>Gcd S = s - t\<close>
        using \<open>t < s\<close> \<open>r < am\<close> by (simp add: field_simps diff_mult_distrib2)
      also have "\<dots> \<in> S"
        using \<open>s \<in> S\<close> \<open>t \<in> S\<close> \<open>r < am\<close>
        by (cases "r = 0") (auto intro!: cmult_S S)
      finally show "n * Gcd S \<in> S" .
    qed
  qed
qed

context MC_syntax
begin

subsection \<open>Expected number of visits\<close>

definition "G s t = (\<integral>\<^sup>+\<omega>. scount (HLD {t}) (s ## \<omega>) \<partial>T s)"

lemma G_eq: "G s t = (\<integral>\<^sup>+\<omega>. emeasure (count_space UNIV) {i. (s ## \<omega>) !! i = t} \<partial>T s)"
  by (simp add: G_def scount_eq_emeasure HLD_iff)

definition "p s t n = \<P>(\<omega> in T s. (s ## \<omega>) !! n = t)"

definition "gf_G s t z = (\<Sum>n. p s t n *\<^sub>R z ^ n)"

definition "convergence_G s t z \<longleftrightarrow> summable (\<lambda>n. p s t n * norm z ^ n)"

lemma p_nonneg[simp]: "0 \<le> p x y n"
  by (simp add: p_def)

lemma p_le_1: "p x y n \<le> 1"
  by (simp add: p_def)

lemma p_x_x_0[simp]: "p x x 0 = 1"
  by (simp add: p_def T.prob_space del: space_T)

lemma p_0: "p x y 0 = (if x = y then 1 else 0)"
  by (simp add: p_def T.prob_space del: space_T)

lemma p_in_reachable: assumes "(x, y) \<notin> (SIGMA x:UNIV. K x)\<^sup>*" shows "p x y n = 0"
  unfolding p_def
proof (rule T.prob_eq_0_AE)
  from AE_T_reachable show "AE \<omega> in T x. (x ## \<omega>) !! n \<noteq> y"
  proof eventually_elim
    fix \<omega> assume "alw (HLD ((SIGMA \<omega>:UNIV. K \<omega>)\<^sup>* `` {x})) \<omega>"
    then have "alw (HLD (- {y})) \<omega>"
      using assms by (auto intro: alw_mono simp: HLD_iff)
    then show "(x ## \<omega>) !! n \<noteq> y"
      using assms by (cases n) (auto simp: alw_HLD_iff_streams streams_iff_snth)
  qed
qed

lemma p_Suc: "ennreal (p x y (Suc n)) = (\<integral>\<^sup>+ w. p w y n \<partial>K x)"
  unfolding p_def T.emeasure_eq_measure[symmetric] by (subst emeasure_Collect_T) simp_all

lemma p_Suc':
  "p x y (Suc n) = (\<integral>x'. p x' y n \<partial>K x)"
  using p_Suc[of x y n]
  by (subst (asm) nn_integral_eq_integral)
     (auto simp: p_le_1 intro!: measure_pmf.integrable_const_bound[where B=1])

lemma p_add: "p x y (n + m) = (\<integral>\<^sup>+ w. p x w n * p w y m \<partial>count_space UNIV)"
proof (induction n arbitrary: x)
  case 0
  have [simp]: "\<And>w. (if x = w then 1 else 0) * p w y m = ennreal (p x y m) * indicator {x} w"
    by auto
  show ?case
    by (simp add: p_0 one_ennreal_def[symmetric] max_def)
next
  case (Suc n)
  define X where "X = (SIGMA x:UNIV. K x)\<^sup>* `` K x"
  then have X: "countable X"
    by (blast intro: countable_Image countable_reachable countable_set_pmf)

  then interpret X: sigma_finite_measure "count_space X"
    by (rule sigma_finite_measure_count_space_countable)
  interpret XK: pair_sigma_finite "K x" "count_space X"
    by unfold_locales

  have "ennreal (p x y (Suc n + m)) = (\<integral>\<^sup>+t. (\<integral>\<^sup>+w. p t w n * p w y m \<partial>count_space UNIV) \<partial>K x)"
    by (simp add: p_Suc Suc)
  also have "\<dots> = (\<integral>\<^sup>+t. (\<integral>\<^sup>+w. ennreal (p t w n * p w y m) * indicator X w \<partial>count_space UNIV) \<partial>K x)"
    by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff AE_count_space Image_iff p_in_reachable X_def             split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+t. (\<integral>\<^sup>+w. p t w n * p w y m \<partial>count_space X) \<partial>K x)"
    by (subst nn_integral_restrict_space[symmetric]) (simp_all add: restrict_count_space)
  also have "\<dots> = (\<integral>\<^sup>+w. (\<integral>\<^sup>+t. p t w n * p w y m \<partial>K x) \<partial>count_space X)"
    apply (rule XK.Fubini'[symmetric])
    unfolding measurable_split_conv
    apply (rule measurable_compose_countable'[OF _ measurable_snd X])
    apply (rule measurable_compose[OF measurable_fst])
    apply simp
    done
  also have "\<dots> = (\<integral>\<^sup>+w. (\<integral>\<^sup>+t. ennreal (p t w n * p w y m) * indicator X w \<partial>K x) \<partial>count_space UNIV)"
    by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space nn_integral_multc)
  also have "\<dots> = (\<integral>\<^sup>+w. (\<integral>\<^sup>+t. ennreal (p t w n * p w y m) \<partial>K x) \<partial>count_space UNIV)"
    by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff AE_count_space Image_iff p_in_reachable X_def             split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+w. (\<integral>\<^sup>+t. p t w n \<partial>K x) * p w y m \<partial>count_space UNIV)"
    by (simp add: nn_integral_multc[symmetric] ennreal_mult)
  finally show ?case
    by (simp add: ennreal_mult p_Suc)
qed

lemma prob_reachable_le:
  assumes [simp]: "m \<le> n"
  shows "p x y m * p y w (n - m) \<le> p x w n"
proof -
  have "p x y m * p y w (n - m) = (\<integral>\<^sup>+y'. ennreal (p x y m * p y w (n - m)) * indicator {y} y' \<partial>count_space UNIV)"
    by simp
  also have "\<dots> \<le> p x w (m + (n - m))"
    by (subst p_add)
       (auto intro!: nn_integral_mono split: split_indicator simp del: nn_integral_indicator_singleton)
  finally show ?thesis
    by simp
qed

lemma G_eq_suminf: "G x y = (\<Sum>i. ennreal (p x y i))"
proof -
  have *: "\<And>i \<omega>. indicator {\<omega> \<in> space S. (x ## \<omega>) !! i = y} \<omega> = indicator {i. (x ## \<omega>) !! i = y} i"
    by (auto simp: space_stream_space split: split_indicator)

  have "G x y = (\<integral>\<^sup>+ \<omega>. (\<Sum>i. indicator {\<omega>\<in>space (T x). (x ## \<omega>) !! i = y} \<omega>) \<partial>T x)"
    unfolding G_eq by (simp add: nn_integral_count_space_nat[symmetric] *)
  also have "\<dots> = (\<Sum>i. ennreal (p x y i))"
    by (simp add: T.emeasure_eq_measure[symmetric] p_def nn_integral_suminf)
  finally show ?thesis .
qed

lemma G_eq_real_suminf:
  "convergence_G x y (1::real) \<Longrightarrow> G x y = ennreal (\<Sum>i. p x y i)"
  unfolding G_eq_suminf
  by (intro suminf_ennreal ennreal_suminf_neq_top p_nonneg)
     (auto simp: convergence_G_def p_def)

lemma convergence_norm_G:
  "convergence_G x y z \<Longrightarrow> summable (\<lambda>n. p x y n * norm z ^ n)"
  unfolding convergence_G_def .

lemma convergence_G:
  "convergence_G x y (z::'a::{banach, real_normed_div_algebra}) \<Longrightarrow> summable (\<lambda>n. p x y n *\<^sub>R z ^ n)"
  unfolding convergence_G_def
  by (rule summable_norm_cancel) (simp add: abs_mult norm_power)

lemma convergence_G_less_1:
  fixes z :: "_ :: {banach, real_normed_field}"
  assumes z: "norm z < 1" shows "convergence_G x y z"
  unfolding convergence_G_def
proof (rule summable_comparison_test)
  have "\<And>n. p x y n * norm (z ^ n) \<le> 1 * norm (z ^ n)"
    by (intro mult_right_mono p_le_1) simp_all
  then show "\<exists>N. \<forall>n\<ge>N. norm (p x y n * norm z ^ n) \<le> norm z ^ n"
    by (simp add: norm_power)
qed (simp add: z summable_geometric)

lemma lim_gf_G: "((\<lambda>z. ennreal (gf_G x y z)) \<longlongrightarrow> G x y) (at_left (1::real))"
  unfolding gf_G_def G_eq_suminf real_scaleR_def
  by (intro power_series_tendsto_at_left p_nonneg p_le_1 summable_power_series)

subsection \<open>Reachability probability\<close>

definition "u x y n = \<P>(\<omega> in T x. ev_at (HLD {y}) n \<omega>)"

definition "U s t = \<P>(\<omega> in T s. ev (HLD {t}) \<omega>)"

definition "gf_U x y z = (\<Sum>n. u x y n *\<^sub>R z ^ Suc n)"

definition "f x y n = \<P>(\<omega> in T x. ev_at (HLD {y}) n (x ## \<omega>))"

definition "F s t = \<P>(\<omega> in T s. ev (HLD {t}) (s ## \<omega>))"

definition "gf_F x y z = (\<Sum>n. f x y n * z ^ n)"

lemma f_Suc: "x \<noteq> y \<Longrightarrow> f x y (Suc n) = u x y n"
  by (simp add: u_def f_def)

lemma f_Suc_eq: "f x x (Suc n) = 0"
  by (simp add: f_def)

lemma f_0: "f x y 0 = (if x = y then 1 else 0)"
  using T.prob_space by (simp add: f_def)

lemma shows u_nonneg: "0 \<le> u x y n" and u_le_1: "u x y n \<le> 1"
  by (simp_all add: u_def)

lemma shows f_nonneg: "0 \<le> f x y n" and f_le_1: "f x y n \<le> 1"
  by (simp_all add: f_def)

lemma U_nonneg[simp]: "0 \<le> U x y"
  by (simp add: U_def)

lemma U_le_1: "U s t \<le> 1"
  by (auto simp add: U_def intro!: antisym)

lemma U_cases: "U s s = 1 \<or> U s s < 1"
  by (auto simp add: U_def intro!: antisym)

lemma u_sums_U: "u x y sums U x y"
  unfolding u_def[abs_def] U_def ev_iff_ev_at by (intro T.prob_sums) (auto intro: ev_at_unique)

lemma gf_U_eq_U: "gf_U x y 1 = U x y"
  using u_sums_U[THEN sums_unique] by (simp add: gf_U_def U_def)

lemma f_sums_F: "f x y sums F x y"
  unfolding f_def[abs_def] F_def ev_iff_ev_at
  by (intro T.prob_sums) (auto intro: ev_at_unique)

lemma F_nonneg[simp]: "0 \<le> F x y"
  by (auto simp: F_def)

lemma F_le_1: "F x y \<le> 1"
  by (simp add: F_def)

lemma gf_F_eq_F: "gf_F x y 1 = F x y"
  using f_sums_F[THEN sums_unique] by (simp add: gf_F_def F_def)

lemma gf_F_le_1:
  fixes z :: real
  assumes z: "0 \<le> z" "z \<le> 1"
  shows "gf_F x y z \<le> 1"
proof -
  have "gf_F x y z \<le> gf_F x y 1"
    using z unfolding gf_F_def
    by (intro suminf_le[OF _ summable_comparison_test[OF _ sums_summable[OF f_sums_F[of x y]]]] mult_left_mono allI f_nonneg)
       (simp_all add: power_le_one f_nonneg mult_right_le_one_le f_le_1 sums_summable[OF f_sums_F[of x y]])
  also have "\<dots> \<le> 1"
    by (simp add: gf_F_eq_F F_def)
  finally show ?thesis .
qed

lemma u_le_p: "u x y n \<le> p x y (Suc n)"
  unfolding u_def p_def by (auto intro!: T.finite_measure_mono dest: ev_at_HLD_imp_snth)

lemma f_le_p: "f x y n \<le> p x y n"
  unfolding f_def p_def by (auto intro!: T.finite_measure_mono dest: ev_at_HLD_imp_snth)

lemma convergence_norm_U:
  fixes z :: "_ :: real_normed_div_algebra"
  assumes z: "convergence_G x y z"
  shows "summable (\<lambda>n. u x y n * norm z ^ Suc n)"
  using summable_ignore_initial_segment[OF convergence_norm_G[OF z], of 1]
  by (rule summable_comparison_test[rotated])
     (auto simp add: u_nonneg abs_mult intro!: exI[of _ 0] mult_right_mono u_le_p)

lemma convergence_norm_F:
  fixes z :: "_ :: real_normed_div_algebra"
  assumes z: "convergence_G x y z"
  shows "summable (\<lambda>n. f x y n * norm z ^ n)"
  using convergence_norm_G[OF z]
  by (rule summable_comparison_test[rotated])
     (auto simp add: f_nonneg abs_mult intro!: exI[of _ 0] mult_right_mono f_le_p)

lemma gf_G_nonneg:
  fixes z :: real
  shows "0 \<le> z \<Longrightarrow> z < 1 \<Longrightarrow> 0 \<le> gf_G x y z"
  unfolding gf_G_def
  by (intro suminf_nonneg convergence_G convergence_G_less_1) simp_all

lemma gf_F_nonneg:
  fixes z :: real
  shows "0 \<le> z \<Longrightarrow> z < 1 \<Longrightarrow> 0 \<le> gf_F x y z"
  unfolding gf_F_def
  using convergence_norm_F[OF convergence_G_less_1, of z x y]
  by (intro suminf_nonneg) (simp_all add: f_nonneg)

lemma convergence_U:
  fixes z :: "_ :: banach"
  shows "convergence_G x y z \<Longrightarrow> summable (\<lambda>n. u x y n * z ^ Suc n)"
  by (rule summable_norm_cancel)
     (auto simp add: abs_mult u_nonneg power_abs dest!: convergence_norm_U)

lemma p_eq_sum_p_u: "p x y (Suc n) = (\<Sum>i\<le>n. p y y (n - i) * u x y i)"
proof -
  have "\<And>\<omega>. \<omega> !! n = y \<Longrightarrow> (\<exists>i. i \<le> n \<and> ev_at (HLD {y}) i \<omega>)"
  proof (induction n)
    case (Suc n)
    then obtain i where "i \<le> n" "ev_at (HLD {y}) i (stl \<omega>)"
      by auto
    then show ?case
      by (auto intro!: exI[of _ "if HLD {y} \<omega> then 0 else Suc i"])
  qed (simp add: HLD_iff)
  then have "p x y (Suc n) = (\<Sum>i\<le>n. \<P>(\<omega> in T x. ev_at (HLD {y}) i \<omega> \<and> \<omega> !! n = y))"
    unfolding p_def by (intro T.prob_sum) (auto intro: ev_at_unique)
  also have "\<dots> = (\<Sum>i\<le>n. p y y (n - i) * u x y i)"
  proof (intro sum.cong refl)
    fix i assume i: "i \<in> {.. n}"
    then have "\<And>\<omega>. (Suc i \<le> n \<longrightarrow> \<omega> !! (n - Suc i) = y) \<longleftrightarrow> ((y ## \<omega>) !! (n - i) = y)"
      by (auto simp: Stream_snth diff_Suc split: nat.split)
    from i have "i \<le> n" by auto
    then have "\<P>(\<omega> in T x. ev_at (HLD {y}) i \<omega> \<and> \<omega> !! n = y) =
      (\<integral>\<omega>'. \<P>(\<omega> in T y. (y ## \<omega>) !! (n - i) = y) *
        indicator {\<omega>'\<in>space (T x). ev_at (HLD {y}) i \<omega>' } \<omega>' \<partial>T x)"
      by (subst prob_T_split[where n="Suc i"])
         (auto simp: ev_at_shift ev_at_HLD_single_imp_snth shift_snth diff_Suc
               split: split_indicator nat.split intro!: Bochner_Integration.integral_cong arg_cong2[where f=measure]
               simp del: stake.simps integral_mult_right_zero)
    then show "\<P>(\<omega> in T x. ev_at (HLD {y}) i \<omega> \<and> \<omega> !! n = y) = p y y (n - i) * u x y i"
      by (simp add: p_def u_def)
  qed
  finally show ?thesis .
qed

lemma p_eq_sum_p_f: "p x y n = (\<Sum>i\<le>n. p y y (n - i) * f x y i)"
  by (cases n)
     (simp_all del: sum.atMost_Suc
               add: f_0 p_0 p_eq_sum_p_u atMost_Suc_eq_insert_0 zero_notin_Suc_image sum.reindex
                    f_Suc f_Suc_eq)

lemma gf_G_eq_gf_F:
  assumes z: "norm z < 1"
  shows "gf_G x y z = gf_F x y z * gf_G y y z"
proof -
  have "gf_G x y z = (\<Sum>n. \<Sum>i\<le>n. p y y (n - i) * f x y i * z^n)"
    by (simp add: gf_G_def p_eq_sum_p_f[of x y] sum_distrib_right)
  also have "\<dots> = (\<Sum>n. \<Sum>i\<le>n. (f x y i * z^i) * (p y y (n - i) * z^(n - i)))"
    by (intro arg_cong[where f=suminf] sum.cong ext atLeast0AtMost[symmetric])
       (simp_all add: power_add[symmetric])
  also have "\<dots> = (\<Sum>n. f x y n * z^n) * (\<Sum>n. p y y n * z^n)"
    using convergence_norm_F[OF convergence_G_less_1[OF z]] convergence_norm_G[OF convergence_G_less_1[OF z]]
    by (intro Cauchy_product[symmetric]) (auto simp: f_nonneg abs_mult power_abs)
  also have "\<dots> = gf_F x y z * gf_G y y z"
    by (simp add: gf_F_def gf_G_def)
  finally show ?thesis .
qed

lemma gf_G_eq_gf_U:
  fixes z :: "'z :: {banach, real_normed_field}"
  assumes z: "convergence_G x x z"
  shows "gf_G x x z = 1 / (1 - gf_U x x z)" "gf_U x x z \<noteq> 1"
proof -
  { fix n
    have "p x x (Suc n) *\<^sub>R z^Suc n = (\<Sum>i\<le>n. (p x x (n - i) * u x x i) *\<^sub>R z^Suc n)"
      unfolding scaleR_sum_left[symmetric] by (simp add: p_eq_sum_p_u)
    also have "\<dots> = (\<Sum>i\<le>n. (u x x i *\<^sub>R z^Suc i) * (p x x (n - i) *\<^sub>R z^(n - i)))"
      by (intro sum.cong refl) (simp add: field_simps power_diff cong: disj_cong)
    finally have "p x x (Suc n) *\<^sub>R z^(Suc n) = (\<Sum>i\<le>n. (u x x i *\<^sub>R z^Suc i) * (p x x (n - i) *\<^sub>R z^(n - i)))"
      unfolding atLeast0AtMost . }
  note gfs_Suc_eq = this

  have "gf_G x x z = 1 + (\<Sum>n. p x x (Suc n) *\<^sub>R z^(Suc n))"
    unfolding gf_G_def
    by (subst suminf_split_initial_segment[OF convergence_G[OF z], of 1]) simp
  also have "\<dots> = 1 + (\<Sum>n. \<Sum>i\<le>n. (u x x i *\<^sub>R z^Suc i) * (p x x (n - i) *\<^sub>R z^(n - i)))"
    unfolding gfs_Suc_eq ..
  also have "\<dots> = 1 + gf_U x x z * gf_G x x z"
    unfolding gf_U_def gf_G_def
    by (subst Cauchy_product)
       (auto simp: u_nonneg norm_power simp del: power_Suc
             intro!: z convergence_norm_G convergence_norm_U)
  finally show "gf_G x x z = 1 / (1 - gf_U x x z)" "gf_U x x z \<noteq> 1"
    apply -
    apply (cases "gf_U x x z = 1")
    apply (auto simp add: field_simps)
    done
qed

lemma gf_U: "(gf_U x y \<longlongrightarrow> U x y) (at_left 1)"
proof -
  have "((\<lambda>z. ennreal (\<Sum>n. u x y n * z ^ n)) \<longlongrightarrow> (\<Sum>n. ennreal (u x y n))) (at_left 1)"
    using u_le_1 u_nonneg by (intro power_series_tendsto_at_left summable_power_series)
  also have "(\<Sum>n. ennreal (u x y n)) = ennreal (suminf (u x y))"
    by (intro u_nonneg suminf_ennreal ennreal_suminf_neq_top sums_summable[OF u_sums_U])
  also have "suminf (u x y) = U x y"
    using u_sums_U by (rule sums_unique[symmetric])
  finally have "((\<lambda>z. \<Sum>n. u x y n * z ^ n) \<longlongrightarrow> U x y) (at_left 1)"
    by (rule tendsto_ennrealD)
       (auto simp: u_nonneg u_le_1 intro!: suminf_nonneg summable_power_series eventually_at_left_1)
  then have "((\<lambda>z. z * (\<Sum>n. u x y n * z ^ n)) \<longlongrightarrow> 1 * U x y) (at_left 1)"
    by (intro tendsto_intros) simp
  then have "((\<lambda>z. \<Sum>n. u x y n * z ^ Suc n) \<longlongrightarrow> 1 * U x y) (at_left 1)"
    apply (rule filterlim_cong[OF refl refl, THEN iffD1, rotated])
    apply (rule eventually_at_left_1)
    apply (subst suminf_mult[symmetric])
    apply (auto intro!: summable_power_series u_le_1 u_nonneg)
    apply (simp add: field_simps)
    done
  then show ?thesis
    by (simp add: gf_U_def[abs_def] U_def)
qed

lemma gf_U_le_1: assumes z: "0 < z" "z < 1" shows "gf_U x y z \<le> (1::real)"
proof -
  note u = u_sums_U[of x y, THEN sums_summable]
  have "gf_U x y z \<le> gf_U x y 1"
    using z
    unfolding gf_U_def real_scaleR_def
    by (intro suminf_le allI mult_mono power_mono summable_comparison_test_ev[OF _ u] always_eventually)
       (auto simp: u_nonneg intro!: mult_left_le mult_le_one power_le_one)
  also have "\<dots> \<le> 1"
    unfolding gf_U_eq_U by (rule U_le_1)
  finally show ?thesis .
qed

lemma gf_F: "(gf_F x y \<longlongrightarrow> F x y) (at_left 1)"
proof -
  have "((\<lambda>z. ennreal (\<Sum>n. f x y n * z ^ n)) \<longlongrightarrow> (\<Sum>n. ennreal (f x y n))) (at_left 1)"
    using f_le_1 f_nonneg by (intro power_series_tendsto_at_left summable_power_series)
  also have "(\<Sum>n. ennreal (f x y n)) = ennreal (suminf (f x y))"
    by (intro f_nonneg suminf_ennreal ennreal_suminf_neq_top sums_summable[OF f_sums_F])
  also have "suminf (f x y) = F x y"
    using f_sums_F by (rule sums_unique[symmetric])
  finally have "((\<lambda>z. \<Sum>n. f x y n * z ^ n) \<longlongrightarrow> F x y) (at_left 1)"
    by (rule tendsto_ennrealD)
       (auto simp: f_nonneg f_le_1 intro!: suminf_nonneg summable_power_series eventually_at_left_1)
  then show ?thesis
    by (simp add: gf_F_def[abs_def] F_def)
qed

lemma U_bounded: "0 \<le> U x y" "U x y \<le> 1"
  unfolding U_def by simp_all

subsection \<open>Recurrent states\<close>

definition recurrent :: "'s \<Rightarrow> bool" where
  "recurrent s \<longleftrightarrow> (AE \<omega> in T s. ev (HLD {s}) \<omega>)"

lemma recurrent_iff_U_eq_1: "recurrent s \<longleftrightarrow> U s s = 1"
    unfolding recurrent_def U_def by (subst T.prob_Collect_eq_1) simp_all

definition "H s t = \<P>(\<omega> in T s. alw (ev (HLD {t})) \<omega>)"

lemma H_eq:
  "recurrent s \<longleftrightarrow> H s s = 1"
  "\<not> recurrent s \<longleftrightarrow> H s s = 0"
  "H s t = U s t * H t t"
proof -
  define H' where "H' t n = {\<omega>\<in>space S. enat n \<le> scount (HLD {t::'s}) \<omega>}" for t n
  have [measurable]: "\<And>y n. H' y n \<in> sets S"
    by (simp add: H'_def)
  let ?H' = "\<lambda>s t n. measure (T s) (H' t n)"
  { fix x y :: 's and \<omega>
    have "Suc 0 \<le> scount (HLD {y}) \<omega> \<longleftrightarrow> ev (HLD {y}) \<omega>"
      using scount_eq_0_iff[of "HLD {y}" \<omega>]
      by (cases "scount (HLD {y}) \<omega>" rule: enat_coexhaust)
         (auto simp: not_ev_iff[symmetric] eSuc_enat[symmetric] enat_0 HLD_iff[abs_def]) }
  then have H'_1: "\<And>x y. ?H' x y 1 = U x y"
    unfolding H'_def U_def by simp

  { fix n and x y :: 's
    let ?U = "(not (HLD {y}) suntil (HLD {y} aand nxt (\<lambda>\<omega>. enat n \<le> scount (HLD {y}) \<omega>)))"
    { fix \<omega>
      have "enat (Suc n) \<le> scount (HLD {y}) \<omega> \<longleftrightarrow> ?U \<omega>"
      proof
        assume "enat (Suc n) \<le> scount (HLD {y}) \<omega>"
        with scount_eq_0_iff[of "HLD {y}" \<omega>] have "ev (HLD {y}) \<omega>" "enat (Suc n) \<le> scount (HLD {y}) \<omega>"
          by (auto simp add: not_ev_iff[symmetric] eSuc_enat[symmetric])
        then show "?U \<omega>"
          by (induction rule: ev_induct_strong)
             (auto simp: scount_simps eSuc_enat[symmetric] intro: suntil.intros)
      next
        assume "?U \<omega>" then show "enat (Suc n) \<le> scount (HLD {y}) \<omega>"
          by induction (auto simp: scount_simps  eSuc_enat[symmetric])
      qed }
    then have "emeasure (T x) (H' y (Suc n)) = emeasure (T x) {\<omega>\<in>space (T x). ?U \<omega>}"
      by (simp add: H'_def)
    also have "\<dots> = U x y * ?H' y y n"
      by (subst emeasure_suntil_HLD) (simp_all add: T.emeasure_eq_measure U_def H'_def ennreal_mult)
    finally have "?H' x y (Suc n) = U x y * ?H' y y n"
      by (simp add: T.emeasure_eq_measure) }
  note H'_Suc = this

  { fix m and x :: 's
    have "?H' x x (Suc m) = U x x^Suc m"
      using H'_1 H'_Suc by (induct m) auto }
  note H'_eq = this

  { fix x y
    have "?H' x y \<longlonglongrightarrow> measure (T x) (\<Inter>i. H' y i)"
      apply (rule T.finite_Lim_measure_decseq)
      apply safe
      apply simp
      apply (auto simp add: decseq_Suc_iff subset_eq H'_def eSuc_enat[symmetric]
                  intro: ile_eSuc order_trans)
      done
    also have "(\<Inter>i. H' y i) = {\<omega>\<in>space (T x). alw (ev (HLD {y})) \<omega>}"
      by (auto simp: H'_def scount_infinite_iff[symmetric]) (metis Suc_ile_eq enat.exhaust neq_iff)
    finally have "?H' x y \<longlonglongrightarrow> H x y"
      unfolding H_def . }
  note H'_lim = this

  from H'_lim[of s s, THEN LIMSEQ_Suc]
  have "(\<lambda>n. U s s ^ Suc n) \<longlonglongrightarrow> H s s"
    by (simp add: H'_eq)
  then have lim_H: "(\<lambda>n. U s s ^ n) \<longlonglongrightarrow> H s s"
    by (rule LIMSEQ_imp_Suc)

  have "U s s < 1 \<Longrightarrow> (\<lambda>n. U s s ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_realpow_zero) (simp_all add: U_def)
  with lim_H have "U s s < 1 \<Longrightarrow> H s s = 0"
    by (blast intro: LIMSEQ_unique)
  moreover have "U s s = 1 \<Longrightarrow> (\<lambda>n. U s s ^ n) \<longlonglongrightarrow> 1"
    by simp
  with lim_H have "U s s = 1 \<Longrightarrow> H s s = 1"
    by (blast intro: LIMSEQ_unique)
  moreover note recurrent_iff_U_eq_1 U_cases
  ultimately show "recurrent s \<longleftrightarrow> H s s = 1" "\<not> recurrent s \<longleftrightarrow> H s s = 0"
    by (metis one_neq_zero)+

  from H'_lim[of s t, THEN LIMSEQ_Suc] H'_Suc[of s]
  have "(\<lambda>n. U s t * ?H' t t n) \<longlonglongrightarrow> H s t"
    by simp
  moreover have "(\<lambda>n. U s t * ?H' t t n) \<longlonglongrightarrow> U s t * H t t"
    by (intro tendsto_intros H'_lim)
  ultimately show "H s t = U s t * H t t"
    by (blast intro: LIMSEQ_unique)
qed

lemma recurrent_iff_G_infinite: "recurrent x \<longleftrightarrow> G x x = \<infinity>"
proof -
  have "((\<lambda>z. ennreal (gf_G x x z)) \<longlongrightarrow> G x x) (at_left 1)"
    by (rule lim_gf_G)
  then have G: "((\<lambda>z. ennreal (1 / (1 - gf_U x x z))) \<longlongrightarrow> G x x) (at_left (1::real))"
    apply (rule filterlim_cong[OF refl refl, THEN iffD1, rotated])
    apply (rule eventually_at_left_1)
    apply (subst gf_G_eq_gf_U)
    apply (rule convergence_G_less_1)
    apply simp
    apply simp
    done

  { fix z :: real assume z: "0 < z" "z < 1"
    have 1: "summable (u x x)"
      using u_sums_U by (rule sums_summable)
    have "gf_U x x z \<noteq> 1"
      using gf_G_eq_gf_U[OF convergence_G_less_1[of z]] z by simp
    moreover
    have "gf_U x x z \<le> U x x"
      unfolding gf_U_def gf_U_eq_U[symmetric]
      using z
      by (intro suminf_le)
         (auto simp add: 1 convergence_U convergence_G_less_1 u_nonneg simp del: power_Suc
               intro!: mult_right_le_one_le power_le_one)
    ultimately have "gf_U x x z < 1"
      using U_bounded[of x x] by simp }
  note strict = this

  { assume "U x x = 1"
    moreover have "((\<lambda>xa. 1 - gf_U x x xa :: real) \<longlongrightarrow> 1 - U x x) (at_left 1)"
      by (intro tendsto_intros gf_U)
    moreover have "eventually (\<lambda>z. gf_U x x z < 1) (at_left (1::real))"
      by (auto intro!: eventually_at_left_1 strict simp: \<open>U x x = 1\<close> gf_U_eq_U)
    ultimately have "((\<lambda>z. ennreal (1 / (1 - gf_U x x z))) \<longlongrightarrow> top) (at_left 1)"
      unfolding ennreal_tendsto_top_eq_at_top
      by (intro LIM_at_top_divide[where a=1] tendsto_const zero_less_one)
         (auto simp: field_simps)
    with G have "G x x = top"
      by (rule tendsto_unique[rotated]) simp }
  moreover
  { assume "U x x < 1"
    then have "((\<lambda>xa. ennreal (1 / (1 - gf_U x x xa))) \<longlongrightarrow> 1 / (1 - U x x)) (at_left 1)"
      by (intro tendsto_intros gf_U tendsto_ennrealI) simp
    from tendsto_unique[OF _ G this] have "G x x \<noteq> \<infinity>"
      by simp }
  ultimately show ?thesis
    using U_cases recurrent_iff_U_eq_1 by auto
qed

definition communicating :: "('s \<times> 's) set" where
  "communicating = acc \<inter> acc\<inverse>"

definition essential_class :: "'s set \<Rightarrow> bool" where
  "essential_class C \<longleftrightarrow> C \<in> UNIV // communicating \<and> acc `` C \<subseteq> C"

lemma accI_U:
  assumes "0 < U x y" shows "(x, y) \<in> acc"
proof (rule ccontr)
  assume *: "(x, y) \<notin> acc"

  { fix \<omega> assume "ev (HLD {y}) \<omega>" "alw (HLD (acc `` {x})) \<omega>" from this * have False
      by induction (auto simp: HLD_iff) }
  with AE_T_reachable[of x] have "U x y = 0"
    unfolding U_def by (intro T.prob_eq_0_AE) auto
  with \<open>0 < U x y\<close> show False by auto
qed

lemma accD_pos:
  assumes "(x, y) \<in> acc"
  shows "\<exists>n. 0 < p x y n"
using assms proof induction
  case base with T.prob_space[of x] show ?case
    by (auto intro!: exI[of _ 0])
next
  have [simp]: "\<And>x y. (if x = y then 1 else 0::real) = indicator {y} x"
    by simp
  case (step w y)
  then obtain n where "0 < p x w n" and "0 < pmf (K w) y"
    by (auto simp: set_pmf_iff less_le)
  then have "0 < p x w n * pmf (K w) y"
    by (intro mult_pos_pos)
  also have "\<dots> \<le> p x w n * p w y (Suc 0)"
    by (simp add: p_Suc' p_0 pmf.rep_eq)
  also have "\<dots> \<le> p x y (Suc n)"
    using prob_reachable_le[of n "Suc n" x w y] by simp
  finally show ?case ..
qed

lemma accI_pos: "0 < p x y n \<Longrightarrow> (x, y) \<in> acc"
proof (induct n arbitrary: x)
  case (Suc n)
  then have less: "0 < (\<integral>x'. p x' y n \<partial>K x)"
    by (simp add: p_Suc')
  have "\<exists>x'\<in>K x. 0 < p x' y n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "AE x' in K x. p x' y n = 0"
      by (simp add: AE_measure_pmf_iff less_le)
    then have "(\<integral>x'. p x' y n \<partial>K x) = (\<integral>x'. 0 \<partial>K x)"
      by (intro integral_cong_AE) simp_all
    with less show False by simp
  qed
  with Suc show ?case
    by (auto intro: converse_rtrancl_into_rtrancl)
qed (simp add: p_0 split: if_split_asm)

lemma recurrent_iffI_communicating:
  assumes "(x, y) \<in> communicating"
  shows "recurrent x \<longleftrightarrow> recurrent y"
proof -
  from assms obtain n m where "0 < p x y n" "0 < p y x m"
    by (force simp: communicating_def dest: accD_pos)
  moreover
  { fix x y n m assume "0 < p x y n" "0 < p y x m" "G y y = \<infinity>"
    then have "\<infinity> = ennreal (p x y n * p y x m) * G y y"
      by (auto intro: mult_pos_pos simp: ennreal_mult_top)
    also have "ennreal (p x y n * p y x m) * G y y = (\<Sum>i. ennreal (p x y n * p y x m) * p y y i)"
      unfolding G_eq_suminf by (rule ennreal_suminf_cmult[symmetric])
    also have "\<dots> \<le> (\<Sum>i. ennreal (p x x (n + i + m)))"
    proof (intro suminf_le allI)
      fix i
      have "(p x y n * p y y ((n + i) - n)) * p y x ((n + i + m) - (n + i)) \<le> p x y (n + i) * p y x ((n + i + m) - (n + i))"
        by (intro mult_right_mono prob_reachable_le) simp_all
      also have "\<dots> \<le> p x x (n + i + m)"
         by (intro prob_reachable_le) simp_all
      finally show "ennreal (p x y n * p y x m) * p y y i \<le> ennreal (p x x (n + i + m))"
        by (simp add: ac_simps ennreal_mult'[symmetric])
    qed auto
    also have "\<dots> \<le> (\<Sum>i. ennreal (p x x (i + (n + m))))"
      by (simp add: ac_simps)
    also have "\<dots> \<le> (\<Sum>i. ennreal (p x x i))"
      by (subst suminf_offset[of "\<lambda>i. ennreal (p x x i)" "n + m"]) auto
    also have "\<dots> \<le> G x x"
      unfolding G_eq_suminf by (auto intro!: suminf_le_pos)
    finally have "G x x = \<infinity>"
      by (simp add: top_unique) }
  ultimately show ?thesis
    using recurrent_iff_G_infinite by blast
qed

lemma recurrent_acc:
  assumes "recurrent x" "(x, y) \<in> acc"
  shows "U y x = 1" "H y x = 1" "recurrent y" "(x, y) \<in> communicating"
proof -
  { fix w y assume step: "(x, w) \<in> acc" "y \<in> K w" "U w x = 1" "H w x = 1" "recurrent w" "x \<noteq> y"
    have "measure (K w) UNIV = U w x"
      using step measure_pmf.prob_space[of "K w"] by simp
    also have "\<dots> = (\<integral>v. indicator {x} v + U v x * indicator (- {x}) v \<partial>K w)"
      unfolding U_def
      by (subst prob_T)
         (auto intro!: Bochner_Integration.integral_cong arg_cong2[where f=measure] AE_I2
               simp: ev_Stream T.prob_eq_1 split: split_indicator)
    also have "\<dots> = measure (K w) {x} + (\<integral>v. U v x * indicator (- {x}) v \<partial>K w)"
      by (subst Bochner_Integration.integral_add)
         (auto intro!: measure_pmf.integrable_const_bound[where B=1]
               simp: abs_mult mult_le_one U_bounded(2) measure_pmf.emeasure_eq_measure)
    finally have "measure (K w) UNIV - measure (K w) {x} = (\<integral>v. U v x * indicator (- {x}) v \<partial>K w)"
      by simp
    also have "measure (K w) UNIV - measure (K w) {x} = measure (K w) (UNIV - {x})"
      by (subst measure_pmf.finite_measure_Diff) auto
    finally have "0 = (\<integral>v. indicator (- {x}) v \<partial>K w) - (\<integral>v. U v x * indicator (- {x}) v \<partial>K w)"
      by (simp add: measure_pmf.emeasure_eq_measure Compl_eq_Diff_UNIV)
    also have "\<dots> = (\<integral>v. (1 - U v x) * indicator (- {x}) v \<partial>K w)"
      by (subst Bochner_Integration.integral_diff[symmetric])
         (auto intro!: measure_pmf.integrable_const_bound[where B=1] Bochner_Integration.integral_cong
               simp: abs_mult mult_le_one U_bounded(2) split: split_indicator)
    also have "\<dots> \<ge> (\<integral>v. (1 - U y x) * indicator {y} v \<partial>K w)" (is "_ \<ge> ?rhs")
      using \<open>recurrent x\<close>
      by (intro integral_mono measure_pmf.integrable_const_bound[where B=1])
         (auto simp: abs_mult mult_le_one U_bounded(2) recurrent_iff_U_eq_1 field_simps
               split: split_indicator)
    also (xtrans) have "?rhs = (1 - U y x) * pmf (K w) y"
      by (simp add: measure_pmf.emeasure_eq_measure pmf.rep_eq)
    finally have "(1 - U y x) * pmf (K w) y = 0"
      by (auto intro!: antisym simp: U_bounded(2) mult_le_0_iff)
    with \<open>y \<in> K w\<close> have "U y x = 1"
      by (simp add: set_pmf_iff)
    then have "U y x = 1" "H y x = 1"
      using H_eq(3)[of y x] H_eq(1)[of x] by (simp_all add: \<open>recurrent x\<close>)
    then have "(y, x) \<in> acc"
      by (intro accI_U) auto
    with step have "(x, y) \<in> communicating"
      by (auto simp add: communicating_def intro: rtrancl_trans)
    with \<open>recurrent x\<close> have "recurrent y"
      by (simp add: recurrent_iffI_communicating)
    note this \<open>U y x = 1\<close> \<open>H y x = 1\<close> \<open>(x, y) \<in> communicating\<close> }
  note enabled = this

  from \<open>(x, y) \<in> acc\<close>
  show "U y x = 1" "H y x = 1" "recurrent y" "(x, y) \<in> communicating"
  proof induction
    case base then show "U x x = 1" "H x x = 1" "recurrent x" "(x, x) \<in> communicating"
      using \<open>recurrent x\<close> H_eq(1)[of x] by (auto simp: recurrent_iff_U_eq_1 communicating_def)
  next
    case (step w y)
    with enabled[of w y] \<open>recurrent x\<close> H_eq(1)[of x]
    have "U y x = 1 \<and> H y x = 1 \<and> recurrent y \<and> (x, y) \<in> communicating"
      by (cases "x = y") (auto simp: recurrent_iff_U_eq_1 communicating_def)
    then show "U y x = 1" "H y x = 1" "recurrent y" "(x, y) \<in> communicating"
      by auto
  qed
qed

lemma equiv_communicating: "equiv UNIV communicating"
  by (auto simp: equiv_def sym_def communicating_def refl_on_def trans_def)

lemma recurrent_class:
  assumes "recurrent x"
  shows "acc `` {x} = communicating `` {x}"
  using recurrent_acc(4)[OF \<open>recurrent x\<close>] by (auto simp: communicating_def)

lemma irreduccible_recurrent_class:
  assumes "recurrent x" shows "acc `` {x} \<in> UNIV // communicating"
  unfolding recurrent_class[OF \<open>recurrent x\<close>] by (rule quotientI) simp

lemma essential_classI:
  assumes C: "C \<in> UNIV // communicating"
  assumes eq: "\<And>x y. x \<in> C \<Longrightarrow> (x, y) \<in> acc \<Longrightarrow> y \<in> C"
  shows "essential_class C"
  by (auto simp: essential_class_def intro: C) (metis eq)

lemma essential_recurrent_class:
  assumes "recurrent x" shows "essential_class (communicating `` {x})"
  unfolding recurrent_class[OF \<open>recurrent x\<close>, symmetric]
  apply (rule essential_classI)
  apply (rule irreduccible_recurrent_class[OF assms])
  apply (auto simp: communicating_def)
  done

lemma essential_classD2:
  "essential_class C \<Longrightarrow> x \<in> C \<Longrightarrow> (x, y) \<in> acc \<Longrightarrow> y \<in> C"
  unfolding essential_class_def by auto

lemma essential_classD3:
  "essential_class C \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> (x, y) \<in> communicating"
  unfolding essential_class_def
  by (auto elim!: quotientE simp: communicating_def)

lemma AE_acc:
  shows "AE \<omega> in T x. \<forall>m. (x, (x ## \<omega>) !! m) \<in> acc"
  using AE_T_reachable
  by eventually_elim (auto simp: alw_HLD_iff_streams streams_iff_snth Stream_snth split: nat.splits)

lemma finite_essential_class_imp_recurrent:
  assumes C: "essential_class C" "finite C" and x: "x \<in> C"
  shows "recurrent x"
proof -
  have "AE \<omega> in T x. \<exists>y\<in>C. alw (ev (HLD {y})) \<omega>"
    using AE_T_reachable
  proof eventually_elim
    fix \<omega> assume "alw (HLD (acc `` {x})) \<omega>"
    then have "alw (HLD C) \<omega>"
      by (rule alw_mono) (auto simp: HLD_iff intro: assms essential_classD2)
    then show "\<exists>y\<in>C. alw (ev (HLD {y})) \<omega>"
      by (rule pigeonhole_stream) fact
  qed
  then have "1 = \<P>(\<omega> in T x. \<exists>y\<in>C. alw (ev (HLD {y})) \<omega>)"
    by (subst (asm) T.prob_Collect_eq_1[symmetric]) (auto simp: \<open>finite C\<close>)
  also have "\<dots> = measure (T x) (\<Union>y\<in>C. {\<omega>\<in>space (T x). alw (ev (HLD {y})) \<omega>})"
    by (intro arg_cong2[where f=measure]) auto
  also have "\<dots> \<le> (\<Sum>y\<in>C. H x y)"
    unfolding H_def using \<open>finite C\<close> by (rule T.finite_measure_subadditive_finite) auto
  also have "\<dots> = (\<Sum>y\<in>C. U x y * H y y)"
    by (auto intro!: sum.cong H_eq)
  finally have "\<exists>y\<in>C. recurrent y"
    by (rule_tac ccontr) (simp add: H_eq(2))
  then guess y ..
  from essential_classD3[OF C(1) x this(1)] recurrent_acc(3)[OF this(2)]
  show "recurrent x"
    by (simp add: communicating_def)
qed

lemma irreducibleD:
  "C \<in> UNIV // communicating \<Longrightarrow> a \<in> C \<Longrightarrow> b \<in> C \<Longrightarrow> (a, b) \<in> communicating"
  by (auto elim!: quotientE simp: communicating_def)

lemma irreducibleD2:
  "C \<in> UNIV // communicating \<Longrightarrow> a \<in> C \<Longrightarrow> (a, b) \<in> communicating \<Longrightarrow> b \<in> C"
  by (auto elim!: quotientE simp: communicating_def)

lemma essential_class_iff_recurrent:
  "finite C \<Longrightarrow> C \<in> UNIV // communicating \<Longrightarrow> essential_class C \<longleftrightarrow> (\<forall>x\<in>C. recurrent x)"
  by (metis finite_essential_class_imp_recurrent irreducibleD2 recurrent_acc(4) essential_classI)

definition "U' x y = (\<integral>\<^sup>+\<omega>. eSuc (sfirst (HLD {y}) \<omega>) \<partial>T x)"

lemma U'_neq_zero[simp]: "U' x y \<noteq> 0"
  unfolding U'_def by (simp add: nn_integral_add)

definition "gf_U' x y z = (\<Sum>n. u x y n * Suc n * z ^ n)"

definition "pos_recurrent x \<longleftrightarrow> recurrent x \<and> U' x x \<noteq> \<infinity>"

lemma summable_gf_U':
  assumes z: "norm z < 1"
  shows "summable (\<lambda>n. u x y n * Suc n * z ^ n)"
proof -
  have "summable (\<lambda>n. n * \<bar>z\<bar> ^ n)"
  proof (rule root_test_convergence)
    have "(\<lambda>n. root n n * \<bar>z\<bar>) \<longlonglongrightarrow> 1 * \<bar>z\<bar>"
      by (intro tendsto_intros LIMSEQ_root)
    then show "(\<lambda>n. root n (norm (n * \<bar>z\<bar> ^ n))) \<longlonglongrightarrow> \<bar>z\<bar>"
      by (rule filterlim_cong[THEN iffD1, rotated 3])
         (auto intro!: exI[of _ 1]
               simp add: abs_mult u_nonneg real_root_mult power_abs eventually_sequentially real_root_power)
  qed (insert z, simp add: abs_less_iff)
  note summable_mult[OF this, of "1 / \<bar>z\<bar>"]
  from summable_ignore_initial_segment[OF this, of 1]
  show "summable (\<lambda>n. u x y n * Suc n * z ^ n)"
    apply (rule summable_comparison_test[rotated])
    using z
    apply (auto intro!: exI[of _ 1]
                simp: abs_mult u_nonneg power_abs Suc_le_eq gr0_conv_Suc field_simps le_divide_eq u_le_1
                simp del: of_nat_Suc)
    done
qed

lemma gf_U'_nonneg[simp]: "0 < z \<Longrightarrow> z < 1 \<Longrightarrow> 0 \<le> gf_U' x y z"
  unfolding gf_U'_def
  by (intro suminf_nonneg summable_gf_U') (auto simp: u_nonneg)

lemma DERIV_gf_U:
  fixes z :: real assumes z: "0 < z" "z < 1"
  shows "DERIV (gf_U x y) z :> gf_U' x y z"
  unfolding gf_U_def[abs_def]  gf_U'_def real_scaleR_def u_def[symmetric]
  using z by (intro DERIV_power_series'[where R=1] summable_gf_U') auto

lemma sfirst_finiteI_recurrent:
  "recurrent x \<Longrightarrow> (x, y) \<in> acc \<Longrightarrow> AE \<omega> in T x. sfirst (HLD {y}) \<omega> < \<infinity>"
  using recurrent_acc(1)[of y x] recurrent_acc[of x y]
    T.AE_prob_1[of x "{\<omega>\<in>space (T x). ev (HLD {y}) \<omega>}"]
  unfolding sfirst_finite U_def by (simp add: space_stream_space communicating_def)

lemma U'_eq_suminf:
  assumes x: "recurrent x" "(x, y) \<in> acc"
  shows "U' x y = (\<Sum>i. ennreal (u x y i * Suc i))"
proof -
  have "(\<integral>\<^sup>+\<omega>. eSuc (sfirst (HLD {y}) \<omega>) \<partial>T x) =
      (\<integral>\<^sup>+\<omega>. (\<Sum>i. ennreal (Suc i) * indicator {\<omega>\<in>space (T y). ev_at (HLD {y}) i \<omega>} \<omega>) \<partial>T x)"
    using sfirst_finiteI_recurrent[OF x]
  proof (intro nn_integral_cong_AE, eventually_elim)
    fix \<omega> assume "sfirst (HLD {y}) \<omega> < \<infinity>"
    then obtain n :: nat where [simp]: "sfirst (HLD {y}) \<omega> = n"
      by auto
    show "eSuc (sfirst (HLD {y}) \<omega>) = (\<Sum>i. ennreal (Suc i) * indicator {\<omega>\<in>space (T y). ev_at (HLD {y}) i \<omega>} \<omega>)"
      by (subst suminf_cmult_indicator[where i=n])
         (auto simp: disjoint_family_on_def ev_at_unique space_stream_space
                     sfirst_eq_enat_iff[symmetric] ennreal_of_nat_eq_real_of_nat
               split: split_indicator)
  qed
  also have "\<dots> = (\<Sum>i. ennreal (Suc i) * emeasure (T x) {\<omega>\<in>space (T x). ev_at (HLD {y}) i \<omega>})"
    by (subst nn_integral_suminf)
       (auto intro!: arg_cong[where f=suminf] nn_integral_cmult_indicator simp: fun_eq_iff)
  finally show ?thesis
    by (simp add: U'_def u_def T.emeasure_eq_measure mult_ac ennreal_mult)
qed

lemma gf_U'_tendsto_U':
  assumes x: "recurrent x" "(x, y) \<in> acc"
  shows "((\<lambda>z. ennreal (gf_U' x y z)) \<longlongrightarrow> U' x y) (at_left 1)"
  unfolding U'_eq_suminf[OF x] gf_U'_def
  by (auto intro!: power_series_tendsto_at_left summable_gf_U' mult_nonneg_nonneg u_nonneg simp del: of_nat_Suc)

lemma one_le_integral_t:
  assumes x: "recurrent x" shows "1 \<le> U' x x"
  by (simp add: nn_integral_add T.emeasure_space_1 U'_def del: space_T)

lemma gf_U'_pos:
  fixes z :: real
  assumes z: "0 < z" "z < 1" and "U x y \<noteq> 0"
  shows "0 < gf_U' x y z"
  unfolding gf_U'_def
proof (subst suminf_pos_iff)
  show "summable (\<lambda>n. u x y n * real (Suc n) * z ^ n)"
    using z by (intro summable_gf_U') simp
  show pos: "\<forall>n. 0 \<le> u x y n * real (Suc n) * z ^ n"
    using z by (auto intro!: mult_nonneg_nonneg u_nonneg)
  show "\<exists>n. 0 < u x y n * real (Suc n) * z ^ n"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. 0 < u x y n * real (Suc n) * z ^ n)"
    with pos have "\<forall>n. u x y n * real (Suc n) * z ^ n = 0"
      by (intro antisym allI) (simp_all add: not_less)
    with z have "u x y = (\<lambda>n. 0)"
      by (intro ext) simp
    with u_sums_U[of x y, THEN sums_unique] \<open>U x y \<noteq> 0\<close> show False
      by simp
  qed
qed

lemma inverse_gf_U'_tendsto:
  assumes "recurrent y"
  shows "((\<lambda>x. - 1 / - gf_U' y y x) \<longlongrightarrow> enn2real (1 / U' y y)) (at_left (1::real))"
proof cases
  assume inf: "U' y y = \<infinity>"
  with gf_U'_tendsto_U'[of y y] \<open>recurrent y\<close>
  have "LIM z (at_left 1). gf_U' y y z :> at_top"
    by (auto simp: ennreal_tendsto_top_eq_at_top U'_def)
  then have "LIM z (at_left 1). gf_U' y y z :> at_infinity"
    by (rule filterlim_mono) (auto simp: at_top_le_at_infinity)
  with inf show ?thesis
    by (auto intro!: tendsto_divide_0)
next
  assume fin: "U' y y \<noteq> \<infinity>"
  then obtain r where r: "U' y y = ennreal r" and [simp]: "0 \<le> r"
    by (cases "U' y y") (auto simp: U'_def)
  then have eq: "enn2real (1 / U' y y) = - 1 / - r" and "1 \<le> r"
    using one_le_integral_t[OF \<open>recurrent y\<close>]
    by (auto simp add: ennreal_1[symmetric] divide_ennreal simp del: ennreal_1)
  have "((\<lambda>z. ennreal (gf_U' y y z)) \<longlongrightarrow> ennreal r) (at_left 1)"
    using gf_U'_tendsto_U'[OF \<open>recurrent y\<close>, of y] r by simp
  then have gf_U': "(gf_U' y y \<longlongrightarrow> r) (at_left (1::real))"
    by (rule tendsto_ennrealD)
       (insert summable_gf_U', auto intro!: eventually_at_left_1 suminf_nonneg simp: gf_U'_def u_nonneg)
  show ?thesis
    using \<open>1 \<le> r\<close> unfolding eq by (intro tendsto_intros gf_U') simp
qed

lemma gf_G_pos:
  fixes z :: real
  assumes z: "0 < z" "z < 1" and *: "(x, y) \<in> acc"
  shows "0 < gf_G x y z"
  unfolding gf_G_def
proof (subst suminf_pos_iff)
  show "summable (\<lambda>n. p x y n *\<^sub>R z ^ n)"
    using z by (intro convergence_G convergence_G_less_1) simp
  show pos: "\<forall>n. 0 \<le> p x y n *\<^sub>R z ^ n"
    using z by (auto intro!: mult_nonneg_nonneg p_nonneg)
  show "\<exists>n. 0 < p x y n *\<^sub>R z ^ n"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. 0 < p x y n *\<^sub>R z ^ n)"
    with pos have "\<forall>n. p x y n * z ^ n = 0"
      by (intro antisym allI) (simp_all add: not_less)
    with z have "\<And>n. p x y n = 0"
      by simp
    with *[THEN accD_pos] show False
      by simp
  qed
qed

lemma pos_recurrentI_communicating:
  assumes y: "pos_recurrent y" and x: "(y, x) \<in> communicating"
  shows "pos_recurrent x"
proof -
  from y x have recurrent: "recurrent y" "recurrent x" and fin: "U' y y \<noteq> \<infinity>"
    by (auto simp: pos_recurrent_def recurrent_iffI_communicating nn_integral_add)
  have pos: "0 < enn2real (1 / U' y y)"
    using one_le_integral_t[OF \<open>recurrent y\<close>] fin
    by (auto simp: U'_def enn2real_positive_iff less_top[symmetric] ennreal_zero_less_divide ennreal_divide_eq_top_iff)

  from fin obtain r where r: "U' y y = ennreal r" and [simp]: "0 \<le> r"
    by (cases "U' y y") (auto simp: U'_def)

  from x obtain n m where "0 < p x y n" "0 < p y x m"
    by (auto dest!: accD_pos simp: communicating_def)

  let ?L = "at_left (1::real)"
  have le: "eventually (\<lambda>z. p x y n * p y x m * z^(n + m) \<le> (1 - gf_U y y z) / (1 - gf_U x x z)) ?L"
  proof (rule eventually_at_left_1)
    fix z :: real assume z: "0 < z" "z < 1"
    then have conv: "\<And>x. convergence_G x x z"
      by (intro convergence_G_less_1) simp
    have sums: "(\<lambda>i. (p x y n * p y x m * z^(n + m)) * (p y y i * z^i)) sums ((p x y n * p y x m * z^(n + m)) * gf_G y y z)"
      unfolding gf_G_def
      by (intro sums_mult summable_sums) (auto intro!: conv convergence_G[where 'a=real, simplified])
    have "(\<Sum>i. (p x y n * p y x m * z^(n + m)) * (p y y i * z^i)) \<le> (\<Sum>i. p x x (i + (n + m)) * z^(i + (n + m)))"
    proof (intro allI suminf_le sums_summable[OF sums] summable_ignore_initial_segment convergence_G[where 'a=real, simplified] convergence_G_less_1)
      show "norm z < 1" using z by simp
      fix i
      have "(p x y n * p y y ((n + i) - n)) * p y x ((n + i + m) - (n + i)) \<le> p x y (n + i) * p y x ((n + i + m) - (n + i))"
        by (intro mult_right_mono prob_reachable_le) simp_all
      also have "\<dots> \<le> p x x (n + i + m)"
         by (intro prob_reachable_le) simp_all
      finally show "p x y n * p y x m * z ^ (n + m) * (p y y i * z ^ i) \<le> p x x (i + (n + m)) * z ^ (i + (n + m))"
        using z by (auto simp add: ac_simps power_add intro!: mult_left_mono)
    qed
    also have "\<dots> \<le> gf_G x x z"
      unfolding gf_G_def
      using z
      apply (subst (2) suminf_split_initial_segment[where k="n + m"])
      apply (intro convergence_G conv)
      apply (simp add: sum_nonneg)
      done
    finally have "(p x y n * p y x m * z^(n + m)) * gf_G y y z \<le> gf_G x x z"
      using sums_unique[OF sums] by simp
    then have "(p x y n * p y x m * z^(n + m)) \<le> gf_G x x z / gf_G y y z"
      using z gf_G_pos[of z y y] by (simp add: field_simps)
    also have "\<dots> = (1 - gf_U y y z) / (1 - gf_U x x z)"
      unfolding gf_G_eq_gf_U[OF conv] using gf_G_eq_gf_U(2)[OF conv] by (simp add: field_simps )
    finally show "p x y n * p y x m * z^(n + m) \<le> (1 - gf_U y y z) / (1 - gf_U x x z)" .
  qed

  have "U' x x \<noteq> \<infinity>"
  proof
    assume "U' x x = \<infinity>"
    have "((\<lambda>z. (1 - gf_U y y z) / (1 - gf_U x x z)) \<longlongrightarrow> 0) ?L"
    proof (rule lhopital_left)
      show "((\<lambda>z. 1 - gf_U y y z) \<longlongrightarrow> 0) ?L"
        using gf_U[of y] recurrent_iff_U_eq_1[of y] \<open>recurrent y\<close> by (auto intro!: tendsto_eq_intros)
      show "((\<lambda>z. 1 - gf_U x x z) \<longlongrightarrow> 0) ?L"
        using gf_U[of x] recurrent_iff_U_eq_1[of x] \<open>recurrent x\<close> by (auto intro!: tendsto_eq_intros)
      show "eventually (\<lambda>z. 1 - gf_U x x z \<noteq> 0) ?L"
        by (auto intro!: eventually_at_left_1 simp: gf_G_eq_gf_U(2) convergence_G_less_1)
      show "eventually (\<lambda>z. - gf_U' x x z \<noteq> 0) ?L"
        using gf_U'_pos[of _ x x] recurrent_iff_U_eq_1[of x] \<open>recurrent x\<close>
        by (auto intro!: eventually_at_left_1) (metis less_le)
      show "eventually (\<lambda>z. DERIV (\<lambda>xa. 1 - gf_U x x xa) z :> - gf_U' x x z) ?L"
        by (auto intro!: eventually_at_left_1 derivative_eq_intros DERIV_gf_U)
      show "eventually (\<lambda>z. DERIV (\<lambda>xa. 1 - gf_U y y xa) z :> - gf_U' y y z) ?L"
        by (auto intro!: eventually_at_left_1 derivative_eq_intros DERIV_gf_U)

      have "(gf_U' y y \<longlongrightarrow> U' y y) ?L"
        using \<open>recurrent y\<close> by (rule gf_U'_tendsto_U') simp
      then have *: "(gf_U' y y \<longlongrightarrow> r) ?L"
        by (auto simp add: r eventually_at_left_1 dest!: tendsto_ennrealD)
      moreover
      have "(gf_U' x x \<longlongrightarrow> U' x x) ?L"
        using \<open>recurrent x\<close> by (rule gf_U'_tendsto_U') simp
      then have "LIM z ?L. - gf_U' x x z :> at_bot"
        by (simp add: ennreal_tendsto_top_eq_at_top \<open>U' x x = \<infinity>\<close> filterlim_uminus_at_top
                 del: ennreal_of_enat_eSuc)
      then have "LIM z ?L. - gf_U' x x z :> at_infinity"
        by (rule filterlim_mono) (auto simp: at_bot_le_at_infinity)
      ultimately show "((\<lambda>z. - gf_U' y y z / - gf_U' x x z) \<longlongrightarrow> 0) ?L"
        by (intro tendsto_divide_0[where c="- r"] tendsto_intros)
    qed
    moreover
    have "((\<lambda>z. p x y n * p y x m * z^(n + m)) \<longlongrightarrow> p x y n * p y x m) ?L"
      by (auto intro!: tendsto_eq_intros)
    ultimately have "p x y n * p y x m \<le> 0"
      using le by (rule tendsto_le[OF trivial_limit_at_left_real])
    with \<open>0 < p x y n\<close> \<open>0 < p y x m\<close> show False
      by (auto simp add: mult_le_0_iff)
  qed
  with \<open>recurrent x\<close> show ?thesis
    by (simp add: pos_recurrent_def nn_integral_add)
qed

lemma pos_recurrent_iffI_communicating:
  "(y, x) \<in> communicating \<Longrightarrow> pos_recurrent y \<longleftrightarrow> pos_recurrent x"
  using pos_recurrentI_communicating[of x y] pos_recurrentI_communicating[of y x]
  by (auto simp add: communicating_def)

lemma U_le_F: "U x y \<le> F x y"
  by (auto simp: U_def F_def intro!: T.finite_measure_mono)

lemma not_empty_irreducible: "C \<in> UNIV // communicating \<Longrightarrow> C \<noteq> {}"
  by (auto simp: quotient_def Image_def communicating_def)

subsection \<open>Stationary distribution\<close>

definition stat :: "'s set \<Rightarrow> 's measure" where
  "stat C = point_measure UNIV (\<lambda>x. indicator C x / U' x x)"

lemma sets_stat[simp]: "sets (stat C) = sets (count_space UNIV)"
  by (simp add: stat_def sets_point_measure)

lemma space_stat[simp]: "space (stat C) = UNIV"
  by (simp add: stat_def space_point_measure)

lemma stat_subprob:
  assumes C: "essential_class C" and "countable C" and pos: "\<forall>c\<in>C. pos_recurrent c"
  shows "emeasure (stat C) C \<le> 1"
proof -
  let ?L = "at_left (1::real)"
  from finite_sequence_to_countable_set[OF \<open>countable C\<close>] guess A . note A = this
  then have "(\<lambda>n. emeasure (stat C) (A n)) \<longlonglongrightarrow> emeasure (stat C) (\<Union>i. A i)"
    by (intro Lim_emeasure_incseq) (auto simp: incseq_Suc_iff)
  then have "emeasure (stat C) (\<Union>i. A i) \<le> 1"
  proof (rule LIMSEQ_le[OF _ tendsto_const], intro exI allI impI)
    fix n
    from A(1,3) have A_n: "finite (A n)"
      by auto

    from C have "C \<noteq> {}"
      by (simp add: essential_class_def not_empty_irreducible)
    then obtain x where "x \<in> C" by auto

    have "((\<lambda>z. (\<Sum>y\<in>A n. gf_F x y z * ((1 - z) / (1 - gf_U y y z)))) \<longlongrightarrow> (\<Sum>y\<in>A n. F x y * enn2real (1 / U' y y))) ?L"
    proof (intro tendsto_intros gf_F, rule lhopital_left)
      fix y assume "y \<in> A n"
      with \<open>A n \<subseteq> C\<close> have "y \<in> C"
        by auto
      show "((-) 1 \<longlongrightarrow> 0) ?L"
        by (intro tendsto_eq_intros) simp_all
      have "recurrent y"
        using pos[THEN bspec, OF \<open>y\<in>C\<close>] by (simp add: pos_recurrent_def)
      then have "U y y = 1"
        by (simp add: recurrent_iff_U_eq_1)

      show "((\<lambda>x. 1 - gf_U y y x) \<longlongrightarrow> 0) ?L"
        using gf_U[of y y] \<open>U y y = 1\<close> by (intro tendsto_eq_intros) auto
      show "eventually (\<lambda>x. 1 - gf_U y y x \<noteq> 0) ?L"
        using gf_G_eq_gf_U(2)[OF convergence_G_less_1, where 'z=real] by (auto intro!: eventually_at_left_1)
      have "eventually (\<lambda>x. 0 < gf_U' y y x) ?L"
        by (intro eventually_at_left_1 gf_U'_pos) (simp_all add: \<open>U y y = 1\<close>)
      then show "eventually (\<lambda>x. - gf_U' y y x \<noteq> 0) ?L"
        by eventually_elim simp
      show "eventually (\<lambda>x. DERIV (\<lambda>x. 1 - gf_U y y x) x :> - gf_U' y y x) ?L"
        by (auto intro!: eventually_at_left_1 derivative_eq_intros DERIV_gf_U)
      show "eventually (\<lambda>x. DERIV ((-) 1) x :> - 1) ?L"
        by (auto intro!: eventually_at_left_1 derivative_eq_intros)
      show "((\<lambda>x. - 1 / - gf_U' y y x) \<longlongrightarrow> enn2real (1 / U' y y)) ?L"
        using \<open>recurrent y\<close> by (rule inverse_gf_U'_tendsto)
    qed
    also have "(\<Sum>y\<in>A n. F x y * enn2real (1 / U' y y)) = (\<Sum>y\<in>A n. enn2real (1 / U' y y))"
    proof (intro sum.cong refl)
      fix y assume "y \<in> A n"
      with \<open>A n \<subseteq> C\<close> have "y \<in> C" by auto
      with \<open>x \<in> C\<close> have "(x, y) \<in> communicating"
        by (rule essential_classD3[OF C])
      with \<open>y\<in>C\<close> have "recurrent y" "(y, x) \<in> acc"
        using pos[THEN bspec, of y] by (auto simp add: pos_recurrent_def communicating_def)
      then have "U x y = 1"
        by (rule recurrent_acc)
      with F_le_1[of x y] U_le_F[of x y] have "F x y = 1" by simp
      then show "F x y * enn2real (1 / U' y y) = enn2real (1 / U' y y)"
        by simp
    qed
    finally have le: "(\<Sum>y\<in>A n. enn2real (1 / U' y y)) \<le> 1"
    proof (rule tendsto_le[OF trivial_limit_at_left_real tendsto_const], intro eventually_at_left_1)
      fix z :: real assume z: "0 < z" "z < 1"
      with \<open>x \<in> C\<close> have "norm z < 1"
        by auto
      then have conv: "\<And>x y. convergence_G x y z"
        by (simp add: convergence_G_less_1)
      have "(\<Sum>y\<in>A n. gf_F x y z / (1 - gf_U y y z)) = (\<Sum>y\<in>A n. gf_G x y z)"
        using \<open>norm z < 1\<close>
        apply (intro sum.cong refl)
        apply (subst gf_G_eq_gf_F)
        apply assumption
        apply (subst gf_G_eq_gf_U(1)[OF conv])
        apply auto
        done
      also have "\<dots> = (\<Sum>y\<in>A n. \<Sum>n. p x y n * z^n)"
        by (simp add: gf_G_def)
      also have "\<dots>  = (\<Sum>i. \<Sum>y\<in>A n. p x y i *\<^sub>R z^i)"
        by (subst suminf_sum[OF convergence_G[OF conv]]) simp
      also have "\<dots>  \<le> (\<Sum>i. z^i)"
      proof (intro suminf_le summable_sum convergence_G conv summable_geometric allI)
        fix l
        have "(\<Sum>y\<in>A n. p x y l *\<^sub>R z ^ l) = (\<Sum>y\<in>A n. p x y l) * z ^ l"
          by (simp add: sum_distrib_right)
        also have "\<dots> \<le> z ^ l"
        proof (intro mult_left_le_one_le)
          have "(\<Sum>y\<in>A n. p x y l) = \<P>(\<omega> in T x. (x ## \<omega>) !! l \<in> A n)"
            unfolding p_def using \<open>finite (A n)\<close>
            by (subst T.finite_measure_finite_Union[symmetric])
               (auto simp: disjoint_family_on_def intro!: arg_cong2[where f=measure])
          then show "(\<Sum>y\<in>A n. p x y l) \<le> 1"
            by simp
        qed (insert z, auto simp: sum_nonneg)
        finally show "(\<Sum>y\<in>A n. p x y l *\<^sub>R z ^ l) \<le> z ^ l" .
      qed fact
      also have "\<dots> = 1 / (1 - z)"
        using sums_unique[OF geometric_sums, OF \<open>norm z < 1\<close>] ..
      finally have "(\<Sum>y\<in>A n. gf_F x y z / (1 - gf_U y y z)) \<le> 1 / (1 - z)" .
      then have "(\<Sum>y\<in>A n. gf_F x y z / (1 - gf_U y y z)) * (1 - z) \<le> 1"
        using z by (simp add: field_simps)
      then have "(\<Sum>y\<in>A n. gf_F x y z / (1 - gf_U y y z) * (1 - z)) \<le> 1"
        by (simp add: sum_distrib_right)
      then show "(\<Sum>y\<in>A n. gf_F x y z * ((1 - z) / (1 - gf_U y y z))) \<le> 1"
        by simp
    qed

    from A_n have "emeasure (stat C) (A n) = (\<Sum>y\<in>A n. emeasure (stat C) {y})"
      by (intro emeasure_eq_sum_singleton) simp_all
    also have "\<dots> = (\<Sum>y\<in>A n. inverse (U' y y))"
      unfolding stat_def U'_def using A(1)[of n]
      apply (intro sum.cong refl)
      apply (subst emeasure_point_measure_finite2)
        apply (auto simp: divide_ennreal_def Collect_conv_if)
      done
    also have "\<dots> = ennreal (\<Sum>y\<in>A n. enn2real (1 / U' y y))"
      apply (subst sum_ennreal[symmetric], simp)
    proof (intro sum.cong refl)
      fix y assume "y \<in> A n"
      with \<open>A n \<subseteq> C\<close> pos have "pos_recurrent y"
        by auto
      with one_le_integral_t[of y] obtain r where "U' y y = ennreal r" "1 \<le> U' y y" and [simp]: "0 \<le> r"
        by (cases "U' y y") (auto simp: pos_recurrent_def nn_integral_add)
      then show "inverse (U' y y) = ennreal (enn2real (1 / U' y y))"
        by (simp add: ennreal_1[symmetric] divide_ennreal inverse_ennreal inverse_eq_divide del: ennreal_1)
    qed
    also have "\<dots> \<le> 1"
      using le by simp
    finally show "emeasure (stat C) (A n) \<le> 1" .
  qed
  with A show ?thesis
    by simp
qed

lemma emeasure_stat_not_C:
  assumes "y \<notin> C"
  shows "emeasure (stat C) {y} = 0"
  unfolding stat_def using \<open>y \<notin> C\<close>
  by (subst emeasure_point_measure_finite2) auto

definition stationary_distribution :: "'s pmf \<Rightarrow> bool" where
  "stationary_distribution N \<longleftrightarrow> N = bind_pmf N K"

lemma stationary_distributionI:
  assumes le: "\<And>y. (\<integral>x. pmf (K x) y \<partial>measure_pmf N) \<le> pmf N y"
  shows "stationary_distribution N"
  unfolding stationary_distribution_def
proof (rule pmf_eqI antisym)+
  fix i
  show "pmf (bind_pmf N K) i \<le> pmf N i"
    by (simp add: pmf_bind le)

  define \<Omega> where "\<Omega> = N \<union> (\<Union>i\<in>N. set_pmf (K i))"
  then have \<Omega>: "countable \<Omega>"
    by (auto intro: countable_set_pmf)
  then interpret N: sigma_finite_measure "count_space \<Omega>"
    by (rule sigma_finite_measure_count_space_countable)
  interpret pN: pair_sigma_finite N "count_space \<Omega>"
    by unfold_locales

  have measurable_pmf[measurable]: "(\<lambda>(x, y). pmf (K x) y) \<in> borel_measurable (N \<Otimes>\<^sub>M count_space \<Omega>)"
    unfolding measurable_split_conv
    apply (rule measurable_compose_countable'[OF _ measurable_snd])
    apply (rule measurable_compose[OF measurable_fst])
    apply (simp_all add: \<Omega>)
    done

  { assume *: "(\<integral>y. pmf (K y) i \<partial>N) < pmf N i"
    have "0 \<le> (\<integral>y. pmf (K y) i \<partial>N)"
      by (intro integral_nonneg_AE) simp
    with * have i: "i \<in> set_pmf N" "i \<in> \<Omega>"
      by (auto simp: set_pmf_iff \<Omega>_def not_le[symmetric])
    from * have "0 < pmf N i - (\<integral>y. pmf (K y) i \<partial>N)"
      by (simp add: field_simps)
    also have "\<dots> = (\<integral>t. (pmf N i - (\<integral>y. pmf (K y) i \<partial>N)) * indicator {i} t \<partial>count_space \<Omega>)"
      by (simp add: i)
    also have "\<dots> \<le> (\<integral>t. pmf N t - \<integral>y. pmf (K y) t \<partial>N \<partial>count_space \<Omega>)"
      using le
      by (intro integral_mono integrable_diff)
         (auto simp: i pmf_bind[symmetric] integrable_pmf field_simps split: split_indicator)
    also have "\<dots> = (\<integral>t. pmf N t \<partial>count_space \<Omega>) - (\<integral>t. \<integral>y. pmf (K y) t \<partial>N \<partial>count_space \<Omega>)"
      by (subst Bochner_Integration.integral_diff) (auto intro!: integrable_pmf simp: pmf_bind[symmetric])
    also have "(\<integral>t. \<integral>y. pmf (K y) t \<partial>N \<partial>count_space \<Omega>) = (\<integral>y. \<integral>t. pmf (K y) t \<partial>count_space \<Omega> \<partial>N)"
      apply (intro pN.Fubini_integral integrable_iff_bounded[THEN iffD2] conjI)
      apply (auto simp add: N.nn_integral_fst[symmetric] nn_integral_eq_integral integrable_pmf)
      unfolding less_top[symmetric] unfolding infinity_ennreal_def[symmetric]
      apply (intro integrableD)
      apply (auto intro!: measure_pmf.integrable_const_bound[where B=1]
                  simp: AE_measure_pmf_iff integral_nonneg_AE integral_pmf)
      done
    also have "(\<integral>y. \<integral>t. pmf (K y) t \<partial>count_space \<Omega> \<partial>N) = (\<integral>y. 1 \<partial>N)"
      by (intro integral_cong_AE)
         (auto simp: AE_measure_pmf_iff integral_pmf \<Omega>_def intro!: measure_pmf.prob_eq_1[THEN iffD2])
    finally have False
      using measure_pmf.prob_space[of N] by (simp add: integral_pmf field_simps not_le[symmetric]) }
  then show "pmf N i \<le> pmf (bind_pmf N K) i"
    by (auto simp: pmf_bind not_le[symmetric])
qed

lemma stationary_distribution_iterate:
  assumes N: "stationary_distribution N"
  shows "ennreal (pmf N y) = (\<integral>\<^sup>+x. p x y n \<partial>N)"
proof (induct n arbitrary: y)
  have [simp]: "\<And>x y. ennreal (if x = y then 1 else 0) = indicator {y} x"
    by simp
  case 0 then show ?case
    by (simp add: p_0 pmf.rep_eq measure_pmf.emeasure_eq_measure)
next
  case (Suc n) with N show ?case
    apply (simp add: nn_integral_eq_integral[symmetric] p_le_1 p_Suc'
                     measure_pmf.integrable_const_bound[where B=1])
    apply (subst nn_integral_bind[symmetric, where B="count_space UNIV"])
    apply (auto simp: stationary_distribution_def measure_pmf_bind[symmetric]
                simp del: measurable_pmf_measure1)
    done
qed

lemma stationary_distribution_iterate':
  assumes "stationary_distribution N"
  shows "measure N {y} = (\<integral>x. p x y n \<partial>N)"
  using stationary_distribution_iterate[OF assms]
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: measure_pmf.integrable_const_bound[where B=1] simp: p_le_1 pmf.rep_eq)

lemma stationary_distributionD:
  assumes C: "essential_class C" "countable C"
  assumes N: "stationary_distribution N" "N \<subseteq> C"
  shows "\<forall>x\<in>C. pos_recurrent x" "measure_pmf N = stat C"
proof -
  have integrable_K: "\<And>f x. integrable N (\<lambda>s. pmf (K s) (f x))"
    by (rule measure_pmf.integrable_const_bound[where B=1]) (simp_all add: pmf_le_1)

  have measure_C: "measure N C = 1" and ae_C: "AE x in N. x \<in> C"
    using N C measure_pmf.prob_eq_1[of C] by (auto simp: AE_measure_pmf_iff)

  have integrable_p: "\<And>n y. integrable N (\<lambda>x. p x y n)"
    by (rule measure_pmf.integrable_const_bound[where B=1]) (simp_all add: p_le_1)

  { fix e :: real assume "0 < e"
    then have [simp]: "0 \<le> e" by simp
    have "\<exists>A\<subseteq>C. finite A \<and> 1 - e < measure N A"
    proof (rule ccontr)
      assume contr: "\<not> (\<exists>A \<subseteq> C. finite A \<and> 1 - e < measure N A)"
      from finite_sequence_to_countable_set[OF \<open>countable C\<close>] guess F . note F = this
      then have *: "(\<lambda>n. measure N (F n)) \<longlonglongrightarrow> measure N (\<Union>i. F i)"
        by (intro measure_pmf.finite_Lim_measure_incseq) (auto simp: incseq_Suc_iff)
      with F contr have "measure N (\<Union>i. F i) \<le> 1 - e"
        by (intro LIMSEQ_le[OF * tendsto_const]) (auto simp: not_less)
      with F \<open>0 < e\<close> show False
        by (simp add: measure_C)
    qed
    then obtain A where "A \<subseteq> C" "finite A" and e: "1 - e < measure N A" by auto

    { fix y n assume "y \<in> C"
      from N(1) have "measure N {y} = (\<integral>x. p x y n \<partial>N)"
        by (rule stationary_distribution_iterate')
      also have "\<dots> \<le> (\<integral>x. p x y n * indicator A x + indicator (C - A) x \<partial>N)"
        using ae_C \<open>A \<subseteq> C\<close>
        by (intro integral_mono_AE)
           (auto elim!: eventually_mono
                 intro!: integral_add integral_indicator p_le_1 integrable_real_mult_indicator
                   integrable_add
                 split: split_indicator simp: integrable_p less_top[symmetric] top_unique)
      also have "\<dots> = (\<integral>x. p x y n * indicator A x \<partial>N) + measure N (C - A)"
        using ae_C \<open>A \<subseteq> C\<close>
        apply (subst Bochner_Integration.integral_add)
        apply (auto elim!: eventually_mono
                    intro!: integral_add integral_indicator p_le_1 integrable_real_mult_indicator
                    split: split_indicator simp: integrable_p less_top[symmetric] top_unique)
        done
      also have "\<dots> \<le> (\<integral>x. p x y n * indicator A x \<partial>N) + e"
        using e \<open>A \<subseteq> C\<close>  by (simp add: measure_pmf.finite_measure_Diff measure_C)
      finally have "measure N {y} \<le> (\<integral>x. p x y n * indicator A x \<partial>N) + e" .
      then have "emeasure N {y} \<le> ennreal (\<integral>x. p x y n * indicator A x \<partial>N) + e"
        by (simp add: measure_pmf.emeasure_eq_measure ennreal_plus[symmetric] del: ennreal_plus)
      also have "\<dots> = (\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) + e"
        by (subst nn_integral_eq_integral[symmetric])
           (auto intro!: measure_pmf.integrable_const_bound[where B=1]
                 simp: abs_mult p_le_1 mult_le_one ennreal_indicator ennreal_mult)
      finally have "emeasure N {y} \<le> (\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) + e" . }
    note v_le = this

    { fix y and z :: real assume y: "y \<in> C" and z: "0 < z" "z < 1"
      have summable_int_p: "summable (\<lambda>n. (\<integral> x. p x y n * indicator A x \<partial>N) * (1 - z) * z ^ n)"
        using \<open>y\<in>C\<close> z \<open>A \<subseteq> C\<close>
        by (auto intro!: summable_comparison_test[OF _ summable_mult[OF summable_geometric[of z], of 1]] exI[of _ 0] mult_le_one
                            measure_pmf.integral_le_const integrable_real_mult_indicator integrable_p AE_I2 p_le_1
                    simp: abs_mult integral_nonneg_AE)

      from y z have sums_y: "(\<lambda>n. measure N {y} * (1 - z) * z ^ n) sums measure N {y}"
        using sums_mult[OF geometric_sums[of z], of "measure N {y} * (1 - z)"] by simp
      then have "emeasure N {y} = ennreal (\<Sum>n. (measure N {y} * (1 - z)) * z ^ n)"
        by (auto simp add: sums_unique[symmetric] measure_pmf.emeasure_eq_measure)
      also have "\<dots> = (\<Sum>n. emeasure N {y} * (1 - z) * z ^ n)"
        using z  summable_mult[OF summable_geometric[of z], of "measure_pmf.prob N {y} * (1 - z)"]
        by (subst suminf_ennreal[symmetric])
           (auto simp: measure_pmf.emeasure_eq_measure ennreal_mult[symmetric] ennreal_suminf_neq_top)
      also have "\<dots> \<le> (\<Sum>n. ((\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) + e) * (1 - z) * z ^ n)"
        using \<open>y\<in>C\<close> z \<open>A \<subseteq> C\<close>
        by (intro suminf_le mult_right_mono v_le allI)
           (auto simp: measure_pmf.emeasure_eq_measure)
      also have "\<dots> = (\<Sum>n. (\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) * (1 - z) * z ^ n) + e"
        using \<open>0 < e\<close> z sums_mult[OF geometric_sums[of z], of "e * (1 - z)"] \<open>0<z\<close> \<open>z<1\<close>
        by (simp add: distrib_right suminf_add[symmetric] ennreal_suminf_cmult[symmetric]
                      ennreal_mult[symmetric] suminf_ennreal_eq sums_unique[symmetric]
                 del: ennreal_suminf_cmult)
      also have "\<dots> = (\<Sum>n. ennreal (1 - z) * ((\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) * z ^ n)) + e"
        by (simp add: ac_simps)
      also have "\<dots> = ennreal (1 - z) * (\<Sum>n. ((\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) * z ^ n)) + e"
        using z by (subst ennreal_suminf_cmult) simp_all
      also have "(\<Sum>n. ((\<integral>\<^sup>+x. ennreal (p x y n) * indicator A x \<partial>N) * z ^ n)) =
          (\<Sum>n. (\<integral>\<^sup>+x. ennreal (p x y n * z ^ n) * indicator A x \<partial>N))"
        using z by (simp add: ac_simps nn_integral_cmult[symmetric] ennreal_mult)
      also have "\<dots> = (\<integral>\<^sup>+x. ennreal (gf_G x y z) * indicator A x \<partial>N)"
        using z
        apply (subst nn_integral_suminf[symmetric])
        apply (auto simp add: gf_G_def simp del: suminf_ennreal
                    intro!: ennreal_mult_right_cong suminf_ennreal2 nn_integral_cong)
        apply (intro summable_comparison_test[OF _ summable_mult[OF summable_geometric[of z], of 1]] impI)
        apply (simp_all add: abs_mult p_le_1 mult_le_one power_le_one split: split_indicator)
        done
      also have "\<dots> = (\<integral>\<^sup>+x. ennreal (gf_F x y z * gf_G y y z) * indicator A x \<partial>N)"
        using z by (intro nn_integral_cong) (simp add: gf_G_eq_gf_F[symmetric])
      also have "\<dots> = ennreal (gf_G y y z) * (\<integral>\<^sup>+x. ennreal (gf_F x y z) * indicator A x \<partial>N)"
        using z by (subst nn_integral_cmult[symmetric]) (simp_all add: gf_G_nonneg gf_F_nonneg ac_simps ennreal_mult)
      also have "\<dots> = ennreal (1 / (1 - gf_U y y z)) * (\<integral>\<^sup>+x. ennreal (gf_F x y z) * indicator A x \<partial>N)"
        using z \<open>y \<in> C\<close> by (subst gf_G_eq_gf_U) (auto intro!: convergence_G_less_1)
      finally have "emeasure N {y} \<le> ennreal ((1 - z) / (1 - gf_U y y z)) * (\<integral>\<^sup>+x. gf_F x y z * indicator A x \<partial>N) + e"
        using z
        by (subst (asm) mult.assoc[symmetric])
           (simp add: ennreal_indicator[symmetric] ennreal_mult'[symmetric] gf_F_nonneg)
      then have "measure N {y} \<le> (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e"
        using z
        by (subst (asm) nn_integral_eq_integral[OF measure_pmf.integrable_const_bound[where B=1]])
           (auto simp: gf_F_nonneg gf_U_le_1 gf_F_le_1 measure_pmf.emeasure_eq_measure mult_le_one
                       ennreal_mult''[symmetric] ennreal_plus[symmetric]
                 simp del: ennreal_plus) }
    then have "\<exists>A \<subseteq> C. finite A \<and> (\<forall>y\<in>C. \<forall>z. 0 < z \<longrightarrow> z < 1 \<longrightarrow> measure N {y} \<le> (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e)"
      using \<open>A \<subseteq> C\<close> \<open>finite A\<close> by auto }
  note eps = this

  { fix y A assume "y \<in> C" "finite A" "A \<subseteq> C"
    then have "((\<lambda>z. \<integral>x. gf_F x y z * indicator A x \<partial>N) \<longlongrightarrow> \<integral>x. F x y * indicator A x \<partial>N) (at_left 1)"
      by (subst (1 2) integral_measure_pmf[of A]) (auto intro!: tendsto_intros gf_F simp: indicator_eq_0_iff) }
  note int_gf_F = this

  have all_recurrent: "\<forall>y\<in>C. recurrent y"
  proof (rule ccontr)
    assume "\<not> (\<forall>y\<in>C. recurrent y)"
    then obtain x where "x \<in> C" "\<not> recurrent x" by auto
    then have transient: "\<And>x. x \<in> C \<Longrightarrow> \<not> recurrent x"
      using C by (auto simp: essential_class_def recurrent_iffI_communicating[symmetric] elim!: quotientE)

    { fix y assume "y \<in> C"
      with transient have "U y y < 1"
        by (metis recurrent_iff_U_eq_1 U_cases)
      have "measure N {y} \<le> 0"
      proof (rule dense_ge)
        fix e :: real assume "0 < e"
        from eps[OF this] \<open>y \<in> C\<close> obtain A where
          A: "finite A" "A \<subseteq> C" and
          le: "\<And>z. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> measure N {y} \<le> (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e"
          by auto
        have "((\<lambda>z. (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e) \<longlongrightarrow>
          (1 - 1) / (1 - U y y) * (\<integral>x. F x y * indicator A x \<partial>N) + e) (at_left (1::real))"
          using A \<open>U y y < 1\<close> \<open>y \<in> C\<close> by (intro tendsto_intros gf_U int_gf_F) auto
        then have 1: "((\<lambda>z. (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e) \<longlongrightarrow> e) (at_left (1::real))"
          by simp
        with le show "measure N {y} \<le> e"
          by (intro tendsto_le[OF trivial_limit_at_left_real _ tendsto_const])
             (auto simp: eventually_at_left_1)
      qed
      then have "measure N {y} = 0"
        by (intro antisym measure_nonneg) }
    then have "emeasure N C = 0"
      by (subst emeasure_countable_singleton) (auto simp: measure_pmf.emeasure_eq_measure nn_integral_0_iff_AE ae_C C)
    then show False
      using \<open>measure N C = 1\<close> by (simp add: measure_pmf.emeasure_eq_measure)
  qed
  then have "\<And>x. x \<in> C \<Longrightarrow> U x x = 1"
    by (metis recurrent_iff_U_eq_1)

  { fix y assume "y \<in> C"
    then have "U y y = 1" "recurrent y"
      using \<open>y \<in> C \<Longrightarrow> U y y = 1\<close> all_recurrent by auto
    have "measure N {y} \<le> enn2real (1 / U' y y)"
    proof (rule field_le_epsilon)
      fix e :: real assume "0 < e"
      from eps[OF \<open>0 < e\<close>] \<open>y \<in> C\<close> obtain A where
        A: "finite A" "A \<subseteq> C" and
        le: "\<And>z. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> measure N {y} \<le> (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e"
        by auto
      let ?L = "at_left (1::real)"
      have "((\<lambda>z. (1 - z) / (1 - gf_U y y z) * (\<integral>x. gf_F x y z * indicator A x \<partial>N) + e) \<longlongrightarrow>
          enn2real (1 / U' y y) * (\<integral>x. F x y * indicator A x \<partial>N) + e) ?L"
      proof (intro tendsto_add tendsto_const tendsto_mult int_gf_F,
             rule lhopital_left[where f'="\<lambda>x. - 1" and g'="\<lambda>z. - gf_U' y y z"])
        show "((-) 1 \<longlongrightarrow> 0) ?L" "((\<lambda>x. 1 - gf_U y y x) \<longlongrightarrow> 0) ?L"
          using gf_U[of y y] by (auto intro!: tendsto_eq_intros simp: \<open>U y y = 1\<close>)
        show "y \<in> C" "finite A" "A \<subseteq> C" by fact+
        show "eventually (\<lambda>x. 1 - gf_U y y x \<noteq> 0) ?L"
          using gf_G_eq_gf_U(2)[OF convergence_G_less_1, where 'z=real] by (auto intro!: eventually_at_left_1)
        show "((\<lambda>x. - 1 / - gf_U' y y x) \<longlongrightarrow> enn2real (1 / U' y y)) ?L"
          using \<open>recurrent y\<close> by (rule inverse_gf_U'_tendsto)
        have "eventually (\<lambda>x. 0 < gf_U' y y x) ?L"
          by (intro eventually_at_left_1 gf_U'_pos) (simp_all add: \<open>U y y = 1\<close>)
        then show "eventually (\<lambda>x. - gf_U' y y x \<noteq> 0) ?L"
          by eventually_elim simp
        show "eventually (\<lambda>x. DERIV (\<lambda>x. 1 - gf_U y y x) x :> - gf_U' y y x) ?L"
          by (auto intro!: eventually_at_left_1 derivative_eq_intros DERIV_gf_U)
        show "eventually (\<lambda>x. DERIV ((-) 1) x :> - 1) ?L"
          by (auto intro!: eventually_at_left_1 derivative_eq_intros)
      qed
      then have "measure N {y} \<le> enn2real (1 / U' y y) * (\<integral>x. F x y * indicator A x \<partial>N) + e"
        by (rule tendsto_le[OF trivial_limit_at_left_real _ tendsto_const]) (intro eventually_at_left_1 le)
      then have "measure N {y} - e \<le> enn2real (1 / U' y y) * (\<integral>x. F x y * indicator A x \<partial>N)"
        by simp
      also have "\<dots> \<le> enn2real (1 / U' y y)"
        using A
        by (intro mult_left_le measure_pmf.integral_le_const measure_pmf.integrable_const_bound[where B=1])
           (auto simp: mult_le_one F_le_1 U'_def)
      finally show "measure N {y} \<le> enn2real (1 / U' y y) + e"
        by simp
    qed }
  note measure_y_le = this

  show pos: "\<forall>y\<in>C. pos_recurrent y"
  proof (rule ccontr)
    assume "\<not> (\<forall>y\<in>C. pos_recurrent y)"
    then obtain x where x: "x \<in> C" "\<not> pos_recurrent x" by auto
    { fix y assume "y \<in> C"
      with x have "\<not> pos_recurrent y"
        using C by (auto simp: essential_class_def pos_recurrent_iffI_communicating[symmetric] elim!: quotientE)
      with all_recurrent \<open>y \<in> C\<close> have "enn2real (1 / U' y y) = 0"
        by (simp add: pos_recurrent_def nn_integral_add)
      with measure_y_le[OF \<open>y \<in> C\<close>] have "measure N {y} = 0"
        by (auto intro!: antisym simp: pos_recurrent_def) }
    then have "emeasure N C = 0"
      by (subst emeasure_countable_singleton) (auto simp: C ae_C measure_pmf.emeasure_eq_measure nn_integral_0_iff_AE)
    then show False
      using \<open>measure N C = 1\<close> by (simp add: measure_pmf.emeasure_eq_measure)
  qed

  { fix A :: "'s set" assume [simp]: "countable A"
    have "emeasure N A = (\<integral>\<^sup>+x. emeasure N {x} \<partial>count_space A)"
      by (intro emeasure_countable_singleton) auto
    also have "\<dots> \<le> (\<integral>\<^sup>+x. emeasure (stat C) {x} \<partial>count_space A)"
    proof (intro nn_integral_mono)
      fix y assume "y \<in> space (count_space A)"
      show "emeasure N {y} \<le> emeasure (stat C) {y}"
      proof cases
        assume "y \<in> C"
        with pos have "pos_recurrent y"
          by auto
        with one_le_integral_t[of y] obtain r where r: "U' y y = ennreal r" "1 \<le> U' y y" and [simp]: "0 \<le> r"
          by (cases "U' y y") (auto simp: pos_recurrent_def nn_integral_add)

        from measure_y_le[OF \<open>y \<in> C\<close>]
        have "emeasure N {y} \<le> ennreal (enn2real (1 / U' y y))"
          by (simp add: measure_pmf.emeasure_eq_measure)
        also have "\<dots> = emeasure (stat C) {y}"
          unfolding stat_def using \<open>y \<in> C\<close> r
          by (subst emeasure_point_measure_finite2)
             (auto simp add: ennreal_1[symmetric] divide_ennreal inverse_ennreal inverse_eq_divide ennreal_mult[symmetric]
                   simp del: ennreal_1)
        finally show "emeasure N {y} \<le> emeasure (stat C) {y}"
          by simp
      next
        assume "y \<notin> C"
        with ae_C have "emeasure N {y} = 0"
          by (subst AE_iff_measurable[symmetric, where P="\<lambda>x. x \<noteq> y"]) (auto elim!: eventually_mono)
        moreover have "emeasure (stat C) {y} = 0"
          using emeasure_stat_not_C[OF \<open>y \<notin> C\<close>] .
        ultimately show ?thesis by simp
      qed
    qed
    also have "\<dots> = emeasure (stat C) A"
      by (intro emeasure_countable_singleton[symmetric]) auto
    finally have "emeasure N A \<le> emeasure (stat C) A" . }
  note N_le_C = this

  from stat_subprob[OF C(1) \<open>countable C\<close> pos] N_le_C[OF \<open>countable C\<close>] \<open>measure N C = 1\<close>
  have stat_C_eq_1: "emeasure (stat C) C = 1"
    by (auto simp add: measure_pmf.emeasure_eq_measure one_ennreal_def)
  moreover have "emeasure (stat C) (UNIV - C) = 0"
    by (subst AE_iff_measurable[symmetric, where P="\<lambda>x. x \<in> C"])
       (auto simp: stat_def AE_point_measure sets_point_measure space_point_measure
                split: split_indicator cong del: AE_cong)
  ultimately have "emeasure (stat C) (space (stat C)) = 1"
    using plus_emeasure[of C "stat C" "UNIV - C"] by (simp add: Un_absorb1)
  interpret stat: prob_space "stat C"
    by standard fact

  show "measure_pmf N = stat C"
  proof (rule measure_eqI_countable_AE)
    show "sets N = UNIV" "sets (stat C) = UNIV"
      by auto
    show "countable C" "AE x in N. x \<in> C" and ae_stat: "AE x in stat C. x \<in> C"
      using C ae_C stat_C_eq_1 by (auto intro!: stat.AE_prob_1 simp: stat.emeasure_eq_measure)

    { assume "\<exists>x. emeasure N {x} \<noteq> emeasure (stat C) {x}"
      then obtain x where [simp]: "emeasure N {x} \<noteq> emeasure (stat C) {x}" by auto
      with N_le_C[of "{x}"] have x: "emeasure N {x} < emeasure (stat C) {x}"
        by (auto simp: less_le)
      have "1 = emeasure N {x} + emeasure N (C - {x})"
        using ae_C
        by (subst plus_emeasure) (auto intro!: measure_pmf.emeasure_eq_1_AE)
      also have "\<dots> < emeasure (stat C) {x} + emeasure (stat C) (C - {x})"
        using x N_le_C[of "C - {x}"] C ae_C
        by (simp add: stat.emeasure_eq_measure measure_pmf.emeasure_eq_measure
                      ennreal_plus[symmetric] ennreal_less_iff
                 del: ennreal_plus)
      also have "\<dots> = 1"
        using ae_stat by (subst plus_emeasure) (auto intro!: stat.emeasure_eq_1_AE)
      finally have False by simp }
    then show "\<And>x. emeasure N {x} = emeasure (stat C) {x}" by auto
  qed
qed

lemma measure_point_measure_singleton:
  "x \<in> A \<Longrightarrow> measure (point_measure A X) {x} = enn2real (X x)"
  unfolding measure_def by (subst emeasure_point_measure_finite2) auto

lemma stationary_distribution_imp_int_t:
  assumes C: "essential_class C" "countable C" "stationary_distribution N" "N \<subseteq> C"
  assumes x: "x \<in> C" shows "U' x x = 1 / ennreal (pmf N x)"
proof -
  from stationary_distributionD[OF C]
  have "measure_pmf N = stat C" and *: "\<forall>x\<in>C. pos_recurrent x" by auto
  show ?thesis
    unfolding \<open>measure_pmf N = stat C\<close> pmf.rep_eq stat_def
    using *[THEN bspec, OF x] x
    apply (simp add: measure_point_measure_singleton)
    apply (cases "U' x x")
    subgoal for r
      by (cases "r = 0")
         (simp_all add: divide_ennreal_def inverse_ennreal)
    apply simp
    done
qed

definition "period_set x = {i. 0 < i \<and> 0 < p x x i }"
definition "period C = (SOME d. \<forall>x\<in>C. d = Gcd (period_set x))"

lemma Gcd_period_set_invariant:
  assumes c: "(x, y) \<in> communicating"
  shows "Gcd (period_set x) = Gcd (period_set y)"
proof -
  { fix x y n assume c: "(x, y) \<in> communicating" "x \<noteq> y" and n: "n \<in> period_set x"
    from c obtain l k where "0 < p x y l" "0 < p y x k"
      by (auto simp: communicating_def dest!: accD_pos)
    moreover with \<open>x \<noteq> y\<close> have "l \<noteq> 0 \<and> k \<noteq> 0"
      by (intro notI conjI) (auto simp: p_0)
    ultimately have pos: "0 < l" "0 < k" and l: "0 < p x y l" and k: "0 < p y x k"
      by auto

    from mult_pos_pos[OF k l] prob_reachable_le[of k "k + l" y x y] c
    have k_l: "0 < p y y (k + l)"
      by simp
    then have "Gcd (period_set y) dvd k + l"
      using pos by (auto intro!: Gcd_dvd_nat simp: period_set_def)
    moreover
    from n have "0 < p x x n" "0 < n" by (auto simp: period_set_def)
    from mult_pos_pos[OF k this(1)] prob_reachable_le[of k "k + n" y x x] c
    have "0 < p y x (k + n)"
      by simp
    from mult_pos_pos[OF this(1) l] prob_reachable_le[of "k + n" "(k + n) + l" y x y] c
    have "0 < p y y (k + n + l)"
      by simp
    then have "Gcd (period_set y) dvd (k + l) + n"
      using pos by (auto intro!: Gcd_dvd_nat simp: period_set_def ac_simps)
    ultimately have "Gcd (period_set y) dvd n"
      by (metis dvd_add_left_iff add.commute) }
  note this[of x y] this[of y x] c
  moreover have "(y, x) \<in> communicating"
    using c by (simp add: communicating_def)
  ultimately show ?thesis
    by (auto intro: dvd_antisym Gcd_greatest Gcd_dvd)
qed

lemma period_eq:
  assumes "C \<in> UNIV // communicating" "x \<in> C"
  shows "period C = Gcd (period_set x)"
  unfolding period_def
  using assms
  by (rule_tac someI2[where a="Gcd (period_set x)"])
     (auto intro!: Gcd_period_set_invariant irreducibleD)

definition "aperiodic C \<longleftrightarrow> C \<in> UNIV // communicating \<and> period C = 1"

definition "not_ephemeral C \<longleftrightarrow> C \<in> UNIV // communicating \<and> \<not> (\<exists>x. C = {x} \<and> p x x 1 = 0)"

lemma not_ephemeralD:
  assumes C: "not_ephemeral C" "x \<in> C"
  shows "\<exists>n>0. 0 < p x x n"
proof cases
  assume "\<exists>x. C = {x}"
  with \<open>x \<in> C\<close> have "C = {x}" by auto
  with C p_nonneg[of x x 1] have "0 < p x x 1"
    by (auto simp: not_ephemeral_def less_le)
  with \<open>C = {x}\<close> show ?thesis by auto
next
  from C have irr: "C \<in> UNIV // communicating"
    by (auto simp: not_ephemeral_def)
  assume "\<not>(\<exists>x. C = {x})"
  then have "\<forall>x. C \<noteq> {x}" by auto
  with \<open>x \<in> C\<close> obtain y where "y \<in> C" "x \<noteq> y"
    by blast
  with irreducibleD[OF irr, of x y] C \<open>x \<in> C\<close> have c: "(x, y) \<in> communicating" by auto
  with accD_pos[of x y] accD_pos[of y x]
  obtain k l where pos: "0 < p x y k" "0 < p y x l"
    by (auto simp: communicating_def)
  with \<open>x \<noteq> y\<close> have "l \<noteq> 0"
    by (intro notI) (auto simp: p_0)
  have "0 < p x y k * p y x (k + l - k)"
    using pos by auto
  also have "p x y k * p y x (k + l - k) \<le> p x x (k + l)"
    using prob_reachable_le[of "k" "k + l" x y x] c by auto
  finally show ?thesis
    using \<open>l \<noteq> 0\<close> \<open>x \<in> C\<close> by (auto intro!: exI[of _ "k + l"])
qed

lemma not_ephemeralD_pos_period:
  assumes C: "not_ephemeral C"
  shows "0 < period C"
proof -
  from C not_empty_irreducible[of C] obtain x where "x \<in> C"
    by (auto simp: not_ephemeral_def)
  from not_ephemeralD[OF C this]
  obtain n where n: "0 < p x x n" "0 < n" by auto
  have C': "C \<in> UNIV // communicating"
    using C by (auto simp: not_ephemeral_def)

  have "period C \<noteq> 0"
    unfolding period_eq [OF C' \<open>x \<in> C\<close>]
    using n by (auto simp: period_set_def)
  then show ?thesis by auto
qed


lemma period_posD:
  assumes C: "C \<in> UNIV // communicating" and "0 < period C" "x \<in> C"
  shows "\<exists>n>0. 0 < p x x n"
proof -
  from \<open>0 < period C\<close> have "period C \<noteq> 0"
    by auto
  then show ?thesis
    unfolding period_eq [OF C \<open>x \<in> C\<close>]
    unfolding period_set_def by auto
qed

lemma not_ephemeralD_pos_period':
  assumes C: "C \<in> UNIV // communicating"
  shows "not_ephemeral C \<longleftrightarrow> 0 < period C"
proof (auto dest!: not_ephemeralD_pos_period intro: C)
  from C not_empty_irreducible[of C] obtain x where "x \<in> C"
    by (auto simp: not_ephemeral_def)

  assume "0 < period C"
  then show "not_ephemeral C"
    apply (auto simp: not_ephemeral_def C)
oops \<comment> \<open>should be easy to finish\<close>


lemma eventually_periodic:
  assumes C: "C \<in> UNIV // communicating" "0 < period C" "x \<in> C"
  shows "eventually (\<lambda>m. 0 < p x x (m * period C)) sequentially"
proof -
  from period_posD[OF assms] obtain n where n: "0 < p x x n" "0 < n" by auto
  have C': "C \<in> UNIV // communicating"
    using C by auto

  have "period C \<noteq> 0"
    unfolding period_eq [OF C' \<open>x \<in> C\<close>]
    using n by (auto simp: period_set_def)
  have "eventually (\<lambda>m. m * Gcd (period_set x) \<in> (period_set x)) sequentially"
  proof (rule eventually_mult_Gcd)
    show "n > 0" "n \<in> period_set x"
      using n by (auto simp add: period_set_def)
    fix k l  assume "k \<in> period_set x" "l \<in> period_set x"
    then have "0 < p x x k * p x x l" "0 < l" "0 < k"
      by (auto simp: period_set_def)
    moreover have "p x x k * p x x l \<le> p x x (k + l)"
      using prob_reachable_le[of k "k + l" x x x] \<open>x \<in> C\<close>
      by auto
    ultimately show "k + l \<in> period_set x"
      using \<open>0 < l\<close> by (auto simp: period_set_def)
  qed
  with eventually_ge_at_top[of 1] show "eventually (\<lambda>m. 0 < p x x (m * period C)) sequentially"
    by eventually_elim 
       (insert \<open>period C \<noteq> 0\<close> period_eq[OF C' \<open>x \<in> C\<close>, symmetric], auto simp: period_set_def)
qed


lemma aperiodic_eventually_recurrent:
  "aperiodic C \<longleftrightarrow> C \<in> UNIV // communicating \<and> (\<forall>x\<in>C. eventually (\<lambda>m. 0 < p x x m) sequentially)"
proof safe
  fix x assume "x \<in> C" "aperiodic C"
  with eventually_periodic[of C x]
  show "eventually (\<lambda>m. 0 < p x x m) sequentially"
    by (auto simp add: aperiodic_def)
next
  assume "\<forall>x\<in>C. eventually (\<lambda>m. 0 < p x x m) sequentially" and C: "C \<in> UNIV // communicating"
  moreover from not_empty_irreducible[OF C] obtain x where "x \<in> C" by auto
  ultimately obtain N where "\<And>M.  M\<ge>N \<Longrightarrow> 0 < p x x M"
    by (auto simp: eventually_sequentially)
  then have "{N <..} \<subseteq> period_set x"
    by (auto simp: period_set_def)
  from C show "aperiodic C"
    unfolding period_eq [OF C \<open>x \<in> C\<close>] aperiodic_def
  proof
    show "Gcd (period_set x) = 1"
    proof (rule Gcd_eqI)
      from one_dvd show "1 dvd q" for q :: nat .
      fix m
      assume "\<And>q. q \<in> period_set x \<Longrightarrow> m dvd q"
      moreover from \<open>{N <..} \<subseteq> period_set x\<close>
      have "{Suc N, Suc (Suc N)} \<subseteq> period_set x"
        by auto
      ultimately have "m dvd Suc (Suc N)" and "m dvd Suc N"
        by auto
      then have "m dvd Suc (Suc N) - Suc N"
        by (rule dvd_diff_nat)
      then show "is_unit m"
        by simp
    qed simp
  qed
qed (simp add: aperiodic_def)

lemma stationary_distributionD_emeasure:
  assumes N: "stationary_distribution N"
  shows "emeasure N A = (\<integral>\<^sup>+s. emeasure (K s) A \<partial>N)"
proof -
  have "prob_space (measure_pmf N)"
    by intro_locales
  then interpret subprob_space "measure_pmf N"
    by (rule prob_space_imp_subprob_space)
  show ?thesis
    unfolding measure_pmf.emeasure_eq_measure
    apply (subst N[unfolded stationary_distribution_def])
    apply (simp add: measure_pmf_bind)
    apply (subst measure_pmf.measure_bind[where N="count_space UNIV"])
    apply (rule measurable_compose[OF _ measurable_measure_pmf])
    apply (auto intro!: nn_integral_eq_integral[symmetric] measure_pmf.integrable_const_bound[where B=1])
    done
qed

lemma communicatingD1:
  "C \<in> UNIV // communicating \<Longrightarrow> (a, b) \<in> communicating \<Longrightarrow> a \<in> C \<Longrightarrow> b \<in> C"
  by (auto elim!: quotientE) (auto simp add: communicating_def)

lemma communicatingD2:
  "C \<in> UNIV // communicating \<Longrightarrow> (a, b) \<in> communicating \<Longrightarrow> b \<in> C \<Longrightarrow> a \<in> C"
  by (auto elim!: quotientE) (auto simp add: communicating_def)

lemma acc_iff: "(x, y) \<in> acc \<longleftrightarrow> (\<exists>n. 0 < p x y n)"
  by (blast intro: accD_pos accI_pos)

lemma communicating_iff: "(x, y) \<in> communicating \<longleftrightarrow> (\<exists>n. 0 < p x y n) \<and> (\<exists>n. 0 < p y x n)"
  by (auto simp add: acc_iff communicating_def)

end

context MC_pair
begin

lemma p_eq_p1_p2:
  "p (x1, x2) (y1, y2) n = K1.p x1 y1 n * K2.p x2 y2 n"
  unfolding p_def K1.p_def K2.p_def
  by (subst prod_eq_prob_T)
     (auto intro!: arg_cong2[where f=measure] split: nat.splits simp: Stream_snth)

lemma P_accD:
  assumes "((x1, x2), (y1, y2)) \<in> acc"shows "(x1, y1) \<in> K1.acc" "(x2, y2) \<in> K2.acc"
  using assms by (auto simp: acc_iff K1.acc_iff K2.acc_iff p_eq_p1_p2 zero_less_mult_iff not_le[of 0, symmetric]
                       cong: conj_cong)

lemma aperiodicI_pair:
  assumes C1: "K1.aperiodic C1" and C2: "K2.aperiodic C2"
  shows "aperiodic (C1 \<times> C2)"
  unfolding aperiodic_eventually_recurrent
proof safe
  from C1[unfolded K1.aperiodic_eventually_recurrent] C2[unfolded K2.aperiodic_eventually_recurrent]
  have C1: "C1 \<in> UNIV // K1.communicating" and C2: "C2 \<in> UNIV // K2.communicating" and
    ev: "\<And>x. x \<in> C1 \<Longrightarrow> eventually (\<lambda>m. 0 < K1.p x x m) sequentially" "\<And>x. x \<in> C2 \<Longrightarrow> eventually (\<lambda>m. 0 < K2.p x x m) sequentially"
    by auto
  { fix x1 x2 assume x: "x1 \<in> C1" "x2 \<in> C2"
    from ev(1)[OF x(1)] ev(2)[OF x(2)]
    show "eventually (\<lambda>m. 0 < p (x1, x2) (x1, x2) m) sequentially"
       by eventually_elim  (simp add: p_eq_p1_p2 x) }

  { fix x1 x2 y1 y2
    assume acc: "(x1, y1) \<in> K1.acc" "(x2, y2) \<in> K2.acc" "x1 \<in> C1" "y1 \<in> C1" "x2 \<in> C2" "y2 \<in> C2"
    then obtain k l where "0 < K1.p x1 y1 l" "0 < K2.p x2 y2 k"
      by (auto dest!: K1.accD_pos K2.accD_pos)
    with acc ev(1)[of y1] ev(2)[of y2]
    have "eventually (\<lambda>m. 0 < K1.p x1 y1 l * K1.p y1 y1 m \<and> 0 < K2.p x2 y2 k * K2.p y2 y2 m) sequentially"
      by (auto elim: eventually_elim2)
    then have "eventually (\<lambda>m. 0 < K1.p x1 y1 (m + l) \<and> 0 < K2.p x2 y2 (m + k)) sequentially"
    proof eventually_elim
      fix m assume "0 < K1.p x1 y1 l * K1.p y1 y1 m \<and> 0 < K2.p x2 y2 k * K2.p y2 y2 m"
      with acc
        K1.prob_reachable_le[of l "l + m" x1 y1 y1]
        K2.prob_reachable_le[of k "k + m" x2 y2 y2]
      show "0 < K1.p x1 y1 (m + l) \<and> 0 < K2.p x2 y2 (m + k)"
        by (auto simp add: ac_simps)
    qed
    then have "eventually (\<lambda>m. 0 < K1.p x1 y1 m \<and> 0 < K2.p x2 y2 m) sequentially"
      unfolding eventually_conj_iff by (subst (asm) (1 2) eventually_sequentially_seg) (auto elim: eventually_elim2)
    then obtain N where "0 < K1.p x1 y1 N" "0 < K2.p x2 y2 N"
      by (auto simp: eventually_sequentially)
    with acc have "0 < p (x1, x2) (y1, y2) N"
      by (auto simp add: p_eq_p1_p2)
    with acc have "((x1, x2), (y1, y2)) \<in> acc"
      by (auto intro!: accI_pos) }
  note 1 = this

  { fix x1 x2 y1 y2 assume acc:"((x1, x2), (y1, y2)) \<in> acc"
    moreover from acc obtain k where "0 < p (x1, x2) (y1, y2) k" by (auto dest!: accD_pos)
    ultimately have "(x1, y1) \<in> K1.acc \<and> (x2, y2) \<in> K2.acc"
      by (subst (asm) p_eq_p1_p2)
         (auto intro!: K1.accI_pos K2.accI_pos simp: zero_less_mult_iff not_le[of 0, symmetric]) }
  note 2 = this

  from K1.not_empty_irreducible[OF C1] K2.not_empty_irreducible[OF C2]
  obtain x1 x2 where xC: "x1 \<in> C1" "x2 \<in> C2" by auto
  show "C1 \<times> C2 \<in> UNIV // communicating"
    apply (simp add: quotient_def Image_def)
    apply (safe intro!: exI[of _ x1] exI[of _ x2])
  proof -
    fix y1 y2 assume yC: "y1 \<in> C1" "y2 \<in> C2"
    from K1.irreducibleD[OF C1 \<open>x1 \<in> C1\<close> \<open>y1 \<in> C1\<close>] K2.irreducibleD[OF C2 \<open>x2 \<in> C2\<close> \<open>y2 \<in> C2\<close>]
    show "((x1, x2), (y1, y2)) \<in> communicating"
      using 1[of x1 y1 x2 y2] 1[of y1 x1 y2 x2] xC yC
      by (auto simp: communicating_def K1.communicating_def K2.communicating_def)
  next
    fix y1 y2 assume "((x1, x2), (y1, y2)) \<in> communicating"
    with 2[of x1 x2 y1 y2] 2[of y1 y2 x1 x2]
    have "(x1, y1) \<in> K1.communicating" "(x2, y2) \<in> K2.communicating"
      by (auto simp: communicating_def K1.communicating_def K2.communicating_def)
    with xC show "y1 \<in> C1" "y2 \<in> C2"
      using K1.communicatingD1[OF C1] K2.communicatingD1[OF C2] by auto
  qed
qed

lemma stationary_distributionI_pair:
  assumes N1: "K1.stationary_distribution N1"
  assumes N2: "K2.stationary_distribution N2"
  shows "stationary_distribution (pair_pmf N1 N2)"
  unfolding stationary_distribution_def
  unfolding Kp_def pair_pmf_def
  apply (subst N1[unfolded K1.stationary_distribution_def])
  apply (subst N2[unfolded K2.stationary_distribution_def])
  apply (simp add: bind_assoc_pmf bind_return_pmf)
  apply (subst bind_commute_pmf[of N2])
  apply simp
  done

end

context MC_syntax
begin

lemma stationary_distribution_imp_limit:
  assumes C: "aperiodic C" "essential_class C" "countable C" and N: "stationary_distribution N" "N \<subseteq> C"
  assumes [simp]: "y \<in> C"
  shows "(\<lambda>n. \<integral>x. \<bar>p y x n - pmf N x\<bar> \<partial>count_space C) \<longlonglongrightarrow> 0"
    (is "?L \<longlonglongrightarrow> 0")
proof -
  from \<open>essential_class C\<close> have C_comm: "C \<in> UNIV // communicating"
    by (simp add: essential_class_def)

  define K' where "K' = (\<lambda>Some x \<Rightarrow> map_pmf Some (K x) | None \<Rightarrow> map_pmf Some N)"

  interpret K2: MC_syntax K' .
  interpret KN: MC_pair K K' .

  from stationary_distributionD[OF C(2,3) N]
  have pos: "\<And>x. x \<in> C \<Longrightarrow> pos_recurrent x" and "measure_pmf N = stat C" by auto

  have pos: "\<And>x. x \<in> C \<Longrightarrow> 0 < emeasure N {x}"
    using pos unfolding stat_def \<open>measure_pmf N = stat C\<close>
    by (subst emeasure_point_measure_finite2)
       (auto simp: U'_def pos_recurrent_def nn_integral_add ennreal_zero_less_divide less_top)
  then have rpos: "\<And>x. x \<in> C \<Longrightarrow> 0 < pmf N x"
    by (simp add: measure_pmf.emeasure_eq_measure pmf.rep_eq)

  have eq: "\<And>x y. (if x = y then 1 else 0) = indicator {y} x" by auto

  have intK: "\<And>f x. (\<integral>x. (f x :: real) \<partial>K' (Some x)) = (\<integral>x. f (Some x) \<partial>K x)"
    by (simp add: K'_def integral_distr map_pmf_rep_eq)

  { fix m and x y :: 's
    have "K2.p (Some x) (Some y) m = p x y m"
      by (induct m arbitrary: x)
         (auto intro!: integral_cong simp add: K2.p_Suc' p_Suc' intK K2.p_0 p_0) }
  note K_p_eq = this

  { fix n and x :: 's have "K2.p (Some x) None n = 0"
      by (induct n arbitrary: x) (auto simp: K2.p_Suc' K2.p_0 intK cong: integral_cong) }
  note K_S_None = this

  from not_empty_irreducible[OF C_comm] obtain c0 where c0: "c0 \<in> C" by auto

  have K2_acc: "\<And>x y. (Some x, y) \<in> K2.acc \<longleftrightarrow> (\<exists>z. y = Some z \<and> (x, z) \<in> acc)"
    apply (auto simp: K2.acc_iff acc_iff K_p_eq)
    apply (case_tac y)
    apply (auto simp: K_p_eq K_S_None)
    done

  have K2_communicating: "\<And>c x. c \<in> C \<Longrightarrow> (Some c, x) \<in> K2.communicating \<longleftrightarrow> (\<exists>c'\<in>C. x = Some c')"
  proof safe
    fix x c assume "c \<in> C" "(Some c, x) \<in> K2.communicating"
    then show "\<exists>c'\<in>C. x = Some c'"
      by (cases x)
         (auto simp: communicating_iff K2.communicating_iff K_p_eq K_S_None intro!: irreducibleD2[OF C_comm \<open>c\<in>C\<close>])
  next
    fix c c' x assume "c \<in> C" "c' \<in> C"
    with irreducibleD[OF C_comm this] show "(Some c, Some c') \<in> K2.communicating"
      by (auto simp: K2.communicating_iff communicating_iff K_p_eq)
  qed

  have "Some ` C \<in> UNIV // K2.communicating"
    by (auto simp add: quotient_def Image_def c0 K2_communicating
             intro!: exI[of _ "Some c0"])
  then have "K2.essential_class (Some ` C)"
    by (rule K2.essential_classI)
       (auto simp: K2_acc essential_classD2[OF \<open>essential_class C\<close>])

  have "K2.aperiodic (Some ` C)"
    unfolding K2.aperiodic_eventually_recurrent
  proof safe
    fix x assume "x \<in> C" then show "eventually (\<lambda>m. 0 < K2.p (Some x) (Some x) m) sequentially"
      using \<open>aperiodic C\<close> unfolding aperiodic_eventually_recurrent
      by (auto elim!: eventually_mono simp: K_p_eq)
  qed fact
  then have aperiodic: "KN.aperiodic (C \<times> Some ` C)"
    by (rule KN.aperiodicI_pair[OF \<open>aperiodic C\<close>])

  have KN_essential: "KN.essential_class (C \<times> Some ` C)"
  proof (rule KN.essential_classI)
    show "C \<times> Some ` C \<in> UNIV // KN.communicating"
      using aperiodic by (simp add: KN.aperiodic_def)
  next
    fix x y assume "x \<in> C \<times> Some ` C" "(x, y) \<in> KN.acc"
    with KN.P_accD[of "fst x" "snd x" "fst y" "snd y"]
    show "y \<in> C \<times> Some ` C"
      by (cases x y rule: prod.exhaust[case_product prod.exhaust])
         (auto simp: K2_acc essential_classD2[OF \<open>essential_class C\<close>])
  qed

  { fix n and x y :: 's
    have "measure N {y} = \<P>(\<omega> in K2.T None. (None ## \<omega>) !! (Suc n) = Some y)"
      unfolding stationary_distribution_iterate'[OF N(1), of y n]
      apply (subst K2.p_def[symmetric])
      apply (subst K2.p_Suc')
      apply (subst K'_def)
      apply (simp add: map_pmf_rep_eq integral_distr K_p_eq)
      done
    then have "measure N {y} = \<P>(\<omega> in K2.T None. \<omega> !! n = Some y)"
      by simp }
  note measure_y_eq = this

  define D where "D = {x::'s \<times> 's option. Some (fst x) = snd x}"

  have [measurable]:
    "\<And>P::('s \<times> 's option \<Rightarrow> bool). P \<in> measurable (count_space UNIV) (count_space UNIV)"
    by simp

  { fix n and x :: 's
    have "\<P>(\<omega> in KN.T (y, None). \<exists>i<n. snd (\<omega> !! n) = Some x \<and> ev_at (HLD D) i \<omega>) =
      (\<Sum>i<n. \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> ev_at (HLD D) i \<omega>))"
      by (subst KN.T.finite_measure_finite_Union[symmetric])
         (auto simp: disjoint_family_on_def intro!: arg_cong2[where f=measure] dest: ev_at_unique)
    also have "\<dots> = (\<Sum>i<n. \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> ev_at (HLD D) i \<omega>))"
    proof (intro sum.cong refl)
      fix i assume i: "i \<in> {..< n}"
      show "\<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> ev_at (HLD D) i \<omega>) =
        \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> ev_at (HLD D) i \<omega>)"
        apply (subst (1 2) KN.prob_T_split[where n="Suc i"])
        apply (simp_all add: ev_at_shift snth_Stream del: stake.simps KN.space_T)
        unfolding ev_at_shift snth_Stream
      proof (intro Bochner_Integration.integral_cong refl)
        fix \<omega> :: "('s \<times> 's option) stream" let ?s = "\<lambda>\<omega>'. stake (Suc i) \<omega> @- \<omega>'"
        show "\<P>(\<omega>' in KN.T (\<omega> !! i). snd (?s \<omega>' !! n) = Some x \<and> ev_at (HLD D) i \<omega>) =
          \<P>(\<omega>' in KN.T (\<omega> !! i). fst (?s \<omega>' !! n) = x \<and> ev_at (HLD D) i \<omega>)"
        proof cases
          assume "ev_at (HLD D) i \<omega>"
          from ev_at_imp_snth[OF this]
          have eq: "snd (\<omega> !! i) = Some (fst (\<omega> !! i))"
            by (simp add: D_def HLD_iff)

          have "\<P>(\<omega>' in KN.T (\<omega> !! i). fst (\<omega>' !! (n - Suc i)) = x) =
            \<P>(\<omega>' in T (fst (\<omega> !! i)). \<omega>' !! (n - Suc i) = x) * \<P>(\<omega>' in K2.T (snd (\<omega> !! i)). True)"
            by (subst KN.prod_eq_prob_T) simp_all
          also have "\<dots> = p (fst (\<omega> !! i)) x (Suc (n - Suc i))"
            using K2.T.prob_space by (simp add: p_def)
          also have "\<dots> = K2.p (snd (\<omega> !! i)) (Some x) (Suc (n - Suc i))"
            by (simp add: K_p_eq eq)
          also have "\<dots> = \<P>(\<omega>' in T (fst (\<omega> !! i)). True) * \<P>(\<omega>' in K2.T (snd (\<omega> !! i)). \<omega>' !! (n - Suc i) = Some x)"
            using T.prob_space by (simp add: K2.p_def)
          also have "\<dots> = \<P>(\<omega>' in KN.T (\<omega> !! i). snd (\<omega>' !! (n - Suc i)) = Some x)"
            by (subst KN.prod_eq_prob_T) simp_all
          finally show ?thesis using \<open>ev_at (HLD D) i \<omega>\<close> i
            by (simp del: stake.simps)
        qed simp
      qed
    qed
    also have "\<dots> = \<P>(\<omega> in KN.T (y, None). (\<exists>i<n. fst (\<omega> !! n) = x \<and> ev_at (HLD D) i \<omega>))"
      by (subst KN.T.finite_measure_finite_Union[symmetric])
         (auto simp add: disjoint_family_on_def dest: ev_at_unique
               intro!: arg_cong2[where f=measure])
    finally have eq: "\<P>(\<omega> in KN.T (y, None). (\<exists>i<n. snd (\<omega> !! n) = Some x \<and> ev_at (HLD D) i \<omega>)) =
      \<P>(\<omega> in KN.T (y, None). (\<exists>i<n. fst (\<omega> !! n) = x \<and> ev_at (HLD D) i \<omega>))" .

    have "p y x (Suc n) - measure N {x} = \<P>(\<omega> in T y. \<omega> !! n = x) - \<P>(\<omega> in K2.T None. \<omega> !! n = Some x)"
      unfolding p_def by (subst measure_y_eq) simp_all
    also have "\<P>(\<omega> in T y. \<omega> !! n = x) = \<P>(\<omega> in T y. \<omega> !! n = x) * \<P>(\<omega> in K2.T None. True)"
      using K2.T.prob_space by simp
    also have "\<dots> = \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x)"
      by (subst KN.prod_eq_prob_T) auto
    also have "\<dots> = \<P>(\<omega> in KN.T (y, None). (\<exists>i<n. fst (\<omega> !! n) = x \<and> ev_at (HLD D) i \<omega>)) +
      \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))"
      by (subst KN.T.finite_measure_Union[symmetric])
         (auto intro!: arg_cong2[where f=measure])
    also have "\<P>(\<omega> in K2.T None. \<omega> !! n = Some x) = \<P>(\<omega> in T y. True) * \<P>(\<omega> in K2.T None. \<omega> !! n = Some x)"
      using T.prob_space by simp
    also have "\<dots> = \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x)"
      by (subst KN.prod_eq_prob_T) auto
    also have "\<dots> = \<P>(\<omega> in KN.T (y, None). (\<exists>i<n. snd (\<omega> !! n) = Some x \<and> ev_at (HLD D) i \<omega>)) +
      \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))"
      by (subst KN.T.finite_measure_Union[symmetric])
         (auto intro!: arg_cong2[where f=measure])
    finally have "\<bar> p y x (Suc n) - measure N {x} \<bar> =
      \<bar> \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) -
      \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) \<bar>"
      unfolding eq by (simp add: field_simps)
    also have "\<dots> \<le> \<bar> \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) \<bar> +
      \<bar> \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) \<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) +
      \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))"
      by simp
    finally have "\<bar> p y x (Suc n) - measure N {x} \<bar> \<le> \<dots>" . }
  note mono = this

  { fix n :: nat
    have "(\<integral>\<^sup>+x. \<bar> p y x (Suc n) - measure N {x} \<bar> \<partial>count_space C) \<le>
      (\<integral>\<^sup>+x. ennreal (\<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))) +
      ennreal (\<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))) \<partial>count_space C)"
      using mono by (intro nn_integral_mono) (simp add: ennreal_plus[symmetric] del: ennreal_plus)
    also have "\<dots> = (\<integral>\<^sup>+x. \<P>(\<omega> in KN.T (y, None). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) \<partial>count_space C) +
      (\<integral>\<^sup>+x. \<P>(\<omega> in KN.T (y, None). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)) \<partial>count_space C)"
      by (subst nn_integral_add) auto
    also have "\<dots> = emeasure (KN.T (y, None)) (\<Union>x\<in>C. {\<omega>\<in>space (KN.T (y, None)). fst (\<omega> !! n) = x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)}) +
      emeasure (KN.T (y, None)) (\<Union>x\<in>C. {\<omega>\<in>space (KN.T (y, None)). snd (\<omega> !! n) = Some x \<and> \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)})"
      by (subst (1 2) emeasure_UN_countable)
         (auto simp add: disjoint_family_on_def KN.T.emeasure_eq_measure C)
    also have "\<dots> \<le> ennreal (\<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))) + ennreal (\<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)))"
      unfolding KN.T.emeasure_eq_measure
      by (intro add_mono) (auto intro!: KN.T.finite_measure_mono)
    also have "\<dots> \<le> 2 * \<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))"
      by (simp add: ennreal_plus[symmetric] del: ennreal_plus)
    finally have "?L (Suc n) \<le> 2 * \<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))"
      by (auto intro!: integral_real_bounded simp add: pmf.rep_eq) }
  note le_2 = this

  have c0_D: "(c0, Some c0) \<in> D"
    by (simp add: D_def c0)

  let ?N' = "map_pmf Some N"
  interpret NP: pair_prob_space N ?N' ..

  have pos_recurrent: "\<forall>x\<in>C \<times> Some ` C. KN.pos_recurrent x"
  proof (rule KN.stationary_distributionD(1)[OF KN_essential _ KN.stationary_distributionI_pair[OF N(1)]])
    show "K2.stationary_distribution ?N'"
      unfolding K2.stationary_distribution_def
      by (subst N(1)[unfolded stationary_distribution_def])
         (auto intro!: bind_pmf_cong simp: K'_def map_pmf_def bind_assoc_pmf bind_return_pmf)
    show "countable (C \<times> Some`C)"
      using C by auto
    show "set_pmf (pair_pmf N (map_pmf Some N)) \<subseteq> C \<times> Some ` C"
      using \<open>N \<subseteq> C\<close> by auto
  qed

  from c0_D have "\<P>(\<omega> in KN.T (y, None). alw (not (HLD D)) \<omega>) \<le> \<P>(\<omega> in KN.T (y, None). alw (not (HLD {(c0, Some c0)})) \<omega>)"
    apply (auto intro!: KN.T.finite_measure_mono)
    apply (rule alw_mono, assumption)
    apply (auto simp: HLD_iff)
    done
  also have "\<dots> = 0"
    apply (rule KN.T.prob_eq_0_AE)
    apply (simp add: not_ev_iff[symmetric])
    apply (subst KN.AE_T_iff)
    apply simp
  proof
    fix t assume t: "t \<in> KN.Kp (y, None)"
    then obtain a b where t_eq: "t = (a, Some b)" "a \<in> K y" "b \<in> N"
      unfolding KN.Kp_def by (auto simp: K'_def)
    with \<open>y \<in> C\<close> have "a \<in> C"
      using essential_classD2[OF \<open>essential_class C\<close> \<open>y \<in> C\<close>] by auto
    have "b \<in> C"
      using \<open>N \<subseteq> C\<close> \<open>b \<in> N\<close> by auto

    from pos_recurrent[THEN bspec, of "(c0, Some c0)"]
    have recurrent_c0: "KN.recurrent (c0, Some c0)"
      by (simp add: KN.pos_recurrent_def c0)
    have "C \<times> Some ` C \<in> UNIV // KN.communicating"
      using aperiodic by (simp add: KN.aperiodic_def)
    then have "((c0, Some c0), t) \<in> KN.communicating"
      by (rule KN.irreducibleD) (simp_all add: t_eq c0 \<open>b \<in> C\<close> \<open>a \<in> C\<close>)
    then have "((c0, Some c0), t) \<in> KN.acc"
      by (simp add: KN.communicating_def)
    then have "KN.U t (c0, Some c0) = 1"
      by (rule KN.recurrent_acc(1)[OF recurrent_c0])
    then show "AE \<omega> in KN.T t. ev (HLD {(c0, Some c0)}) (t ## \<omega>)"
      unfolding KN.U_def by (subst (asm) KN.T.prob_Collect_eq_1) (auto simp add: ev_Stream)
  qed
  finally have "\<P>(\<omega> in KN.T (y, None). alw (not (HLD D)) \<omega>) = 0"
    by (intro antisym measure_nonneg)

  have "(\<lambda>n. \<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))) \<longlonglongrightarrow>
    measure (KN.T (y, None)) (\<Inter>n. {\<omega>\<in>space (KN.T (y, None)). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)})"
    by (rule KN.T.finite_Lim_measure_decseq) (auto simp: decseq_def)
  also have "(\<Inter>n. {\<omega>\<in>space (KN.T (y, None)). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>)}) =
    {\<omega>\<in>space (KN.T (y, None)). alw (not (HLD D)) \<omega>}"
    by (auto simp: not_ev_iff[symmetric] ev_iff_ev_at)
  also have "\<P>(\<omega> in KN.T (y, None). alw (not (HLD D)) \<omega>) = 0" by fact
  finally have *: "(\<lambda>n. 2 * \<P>(\<omega> in KN.T (y, None). \<not> (\<exists>i<n. ev_at (HLD D) i \<omega>))) \<longlonglongrightarrow> 0"
    by (intro tendsto_eq_intros) auto

  show ?thesis
    apply (rule LIMSEQ_imp_Suc)
    apply (rule tendsto_sandwich[OF _ _ tendsto_const *])
    using le_2
    apply (simp_all add: integral_nonneg_AE)
    done
qed

lemma stationary_distribution_imp_p_limit:
  assumes "aperiodic C" "essential_class C" and [simp]: "countable C"
  assumes N: "stationary_distribution N" "N \<subseteq> C"
  assumes [simp]: "x \<in> C" "y \<in> C"
  shows "p x y \<longlonglongrightarrow> pmf N y"
proof -
  define D where "D y n = \<bar>p x y n - pmf N y\<bar>" for y n

  from stationary_distribution_imp_limit[OF assms(1,2,3,4,5,6)]
  have INT: "(\<lambda>n. \<integral>y. D y n \<partial>count_space C) \<longlonglongrightarrow> 0"
    unfolding D_def .

  { fix n
    have "D y n \<le> (\<integral>z. D y n * indicator {y} z \<partial>count_space C)"
      by simp
    also have "\<dots> \<le> (\<integral>y. D y n \<partial>count_space C)"
      by (intro integral_mono)
         (auto split: split_indicator simp: D_def p_def disjoint_family_on_def
               intro!: Bochner_Integration.integrable_diff integrable_pmf T.integrable_measure)
    finally have "D y n \<le> (\<integral>y. D y n \<partial>count_space C)" . }
  note * = this

  have D_nonneg: "\<And>n. 0 \<le> D y n" by (simp add: D_def)

  have "D y \<longlonglongrightarrow> 0"
    by (rule tendsto_sandwich[OF _ _ tendsto_const INT])
       (auto simp: eventually_sequentially * D_nonneg)
  then show ?thesis
    using Lim_null[where l="pmf N y" and net=sequentially and f="p x y"]
    by (simp add: D_def [abs_def] tendsto_rabs_zero_iff)
qed

end

lemma (in MC_syntax) essential_classI2:
  assumes "X \<noteq> {}"
  assumes accI: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> (x, y) \<in> acc"
  assumes ED: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> set_pmf (K x) \<Longrightarrow> y \<in> X"
  shows "essential_class X"
proof (rule essential_classI)
  { fix x y assume "(x, y) \<in> acc" "x \<in> X"
    then show "y \<in> X"
      by induct (auto dest: ED)}
  note accD = this

  from \<open>X \<noteq> {}\<close> obtain x where "x \<in> X" by auto
  from \<open>x \<in> X\<close> show "X \<in> UNIV // communicating"
    by (auto simp add: quotient_def Image_def communicating_def accI dest: accD intro!: exI[of _ x])
qed

end
