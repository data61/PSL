section \<open>Various preliminary material\<close>
theory Zeta_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Real_Asymp.Real_Asymp"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
begin

subsection \<open>Facts about limits\<close>

lemma at_within_altdef:
  "at x within A = (INF S\<in>{S. open S \<and> x \<in> S}. principal (S \<inter> (A - {x})))"
  unfolding at_within_def nhds_def inf_principal [symmetric]
    by (subst INF_inf_distrib [symmetric]) (auto simp: INF_constant)

lemma tendsto_at_left_realI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X (at_left c) sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) (at_left c)"
proof -
  obtain A where A: "decseq A" "open (A n)" "y \<in> A n" "nhds y = (INF n. principal (A n))" for n
    by (rule nhds_countable[of y]) (rule that)

  have "\<forall>m. \<exists>d<c. \<forall>x\<in>{d<..<c}. f x \<in> A m"
  proof (rule ccontr)
    assume "\<not> (\<forall>m. \<exists>d<c. \<forall>x\<in>{d<..<c}. f x \<in> A m)"
    then obtain m where **: "\<And>d. d < c \<Longrightarrow> \<exists>x\<in>{d<..<c}. f x \<notin> A m"
      by auto
    have "\<exists>X. \<forall>n. (f (X n) \<notin> A m \<and> X n < c) \<and> X (Suc n) > c - max 0 ((c - X n) / 2)"
    proof (intro dependent_nat_choice, goal_cases)
      case 1
      from **[of "c - 1"] show ?case by auto
    next
      case (2 x n)
      with **[of "c - max 0 (c - x) / 2"] show ?case by force
    qed
    then obtain X where X: "\<And>n. f (X n) \<notin> A m" "\<And>n. X n < c" "\<And>n. X (Suc n) > c - max 0 ((c - X n) / 2)"
      by auto
    have X_ge: "X n \<ge> c - (c - X 0) / 2 ^ n" for n
    proof (induction n)
      case (Suc n)
      have "c - (c - X 0) / 2 ^ Suc n = c - (c - (c - (c - X 0) / 2 ^ n)) / 2"
        by simp
      also have "c - (c - (c - (c - X 0) / 2 ^ n)) / 2 \<le> c - (c - X n) / 2"
        by (intro diff_left_mono divide_right_mono Suc diff_right_mono) auto
      also have "\<dots> = c - max 0 ((c - X n) / 2)"
        using X[of n] by (simp add: max_def)
      also have "\<dots> < X (Suc n)"
        using X[of n] by simp
      finally show ?case by linarith
    qed auto

    have "X \<longlonglongrightarrow> c"
    proof (rule tendsto_sandwich)
      show "eventually (\<lambda>n. X n \<le> c) sequentially"
        using X by (intro always_eventually) (auto intro!: less_imp_le)
      show "eventually (\<lambda>n. X n \<ge> c - (c - X 0) / 2 ^ n) sequentially"
        using X_ge by (intro always_eventually) auto
    qed real_asymp+
    hence "filterlim X (at_left c) sequentially"
      by (rule tendsto_imp_filterlim_at_left)
         (use X in \<open>auto intro!: always_eventually less_imp_le\<close>)
    from topological_tendstoD[OF *[OF this] A(2, 3), of m] X(1) show False
      by auto
  qed

  then obtain d where d: "d m < c" "x \<in> {d m<..<c} \<Longrightarrow> f x \<in> A m" for m x
    by metis
  have ***: "at_left c = (INF S\<in>{S. open S \<and> c \<in> S}. principal (S \<inter> {..<c}))"
    by (simp add: at_within_altdef)
  from d show ?thesis
    unfolding *** A using A(1,2) by (intro filterlim_base[of _ "\<lambda>m. {d m<..}"]) auto
qed

lemma
  shows at_right_PInf [simp]: "at_right (\<infinity> :: ereal) = bot"
    and at_left_MInf [simp]: "at_left (-\<infinity> :: ereal) = bot"
proof -
  have "{(\<infinity>::ereal)<..} = {}" "{..<-(\<infinity>::ereal)} = {}"
    by auto
  thus "at_right (\<infinity> :: ereal) = bot" "at_left (-\<infinity> :: ereal) = bot"
    by (simp_all add: at_within_def)
qed

lemma tendsto_at_left_erealI_sequentially:
  fixes f :: "ereal \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X (at_left c) sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) (at_left c)"
proof (cases c)
  case [simp]: PInf
  have "((\<lambda>x. f (ereal x)) \<longlongrightarrow> y) at_top" using assms
    by (intro tendsto_at_topI_sequentially assms)
       (simp_all flip: ereal_tendsto_simps add: o_def filterlim_at)
  thus ?thesis
    by (simp add: at_left_PInf filterlim_filtermap)
next
  case [simp]: MInf
  thus ?thesis by auto
next
  case [simp]: (real c')
  have "((\<lambda>x. f (ereal x)) \<longlongrightarrow> y) (at_left c')"
  proof (intro tendsto_at_left_realI_sequentially assms)
    fix X assume *: "filterlim X (at_left c') sequentially"
    show "filterlim (\<lambda>n. ereal (X n)) (at_left c) sequentially"
      by (rule filterlim_compose[OF _ *])
         (simp add: sequentially_imp_eventually_within tendsto_imp_filterlim_at_left)
  qed
  thus ?thesis
    by (simp add: at_left_ereal filterlim_filtermap)
qed

lemma tendsto_at_right_realI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X (at_right c) sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) (at_right c)"
proof -
  obtain A where A: "decseq A" "open (A n)" "y \<in> A n" "nhds y = (INF n. principal (A n))" for n
    by (rule nhds_countable[of y]) (rule that)

  have "\<forall>m. \<exists>d>c. \<forall>x\<in>{c<..<d}. f x \<in> A m"
  proof (rule ccontr)
    assume "\<not> (\<forall>m. \<exists>d>c. \<forall>x\<in>{c<..<d}. f x \<in> A m)"
    then obtain m where **: "\<And>d. d > c \<Longrightarrow> \<exists>x\<in>{c<..<d}. f x \<notin> A m"
      by auto
    have "\<exists>X. \<forall>n. (f (X n) \<notin> A m \<and> X n > c) \<and> X (Suc n) < c + max 0 ((X n - c) / 2)"
    proof (intro dependent_nat_choice, goal_cases)
      case 1
      from **[of "c + 1"] show ?case by auto
    next
      case (2 x n)
      with **[of "c + max 0 (x - c) / 2"] show ?case by force
    qed
    then obtain X where X: "\<And>n. f (X n) \<notin> A m" "\<And>n. X n > c" "\<And>n. X (Suc n) < c + max 0 ((X n - c) / 2)"
      by auto
    have X_le: "X n \<le> c + (X 0 - c) / 2 ^ n" for n
    proof (induction n)
      case (Suc n)
      have "X (Suc n) < c + max 0 ((X n - c) / 2)"
        by (intro X) 
      also have "\<dots> = c + (X n - c) / 2"
        using X[of n] by (simp add: field_simps max_def)
      also have "\<dots> \<le> c + (c + (X 0 - c) / 2 ^ n - c) / 2"
        by (intro add_left_mono divide_right_mono Suc diff_right_mono) auto
      also have "\<dots> = c + (X 0 - c) / 2 ^ Suc n"
        by simp
      finally show ?case by linarith
    qed auto

    have "X \<longlonglongrightarrow> c"
    proof (rule tendsto_sandwich)
      show "eventually (\<lambda>n. X n \<ge> c) sequentially"
        using X by (intro always_eventually) (auto intro!: less_imp_le)
      show "eventually (\<lambda>n. X n \<le> c + (X 0 - c) / 2 ^ n) sequentially"
        using X_le by (intro always_eventually) auto
    qed real_asymp+
    hence "filterlim X (at_right c) sequentially"
      by (rule tendsto_imp_filterlim_at_right)
         (use X in \<open>auto intro!: always_eventually less_imp_le\<close>)
    from topological_tendstoD[OF *[OF this] A(2, 3), of m] X(1) show False
      by auto
  qed

  then obtain d where d: "d m > c" "x \<in> {c<..<d m} \<Longrightarrow> f x \<in> A m" for m x
    by metis
  have ***: "at_right c = (INF S\<in>{S. open S \<and> c \<in> S}. principal (S \<inter> {c<..}))"
    by (simp add: at_within_altdef)
  from d show ?thesis
    unfolding *** A using A(1,2) by (intro filterlim_base[of _ "\<lambda>m. {..<d m}"]) auto
qed

lemma tendsto_at_right_erealI_sequentially:
  fixes f :: "ereal \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X (at_right c) sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) (at_right c)"
proof (cases c)
  case [simp]: MInf
  have "((\<lambda>x. f (-ereal x)) \<longlongrightarrow> y) at_top" using assms
   by (intro tendsto_at_topI_sequentially assms)
      (simp_all flip: uminus_ereal.simps ereal_tendsto_simps add: o_def filterlim_at)
  thus ?thesis
    by (simp add: at_right_MInf filterlim_filtermap at_top_mirror)
next
  case [simp]: PInf
  thus ?thesis by auto
next
  case [simp]: (real c')
  have "((\<lambda>x. f (ereal x)) \<longlongrightarrow> y) (at_right c')"
  proof (intro tendsto_at_right_realI_sequentially assms)
    fix X assume *: "filterlim X (at_right c') sequentially"
    show "filterlim (\<lambda>n. ereal (X n)) (at_right c) sequentially"
      by (rule filterlim_compose[OF _ *])
         (simp add: sequentially_imp_eventually_within tendsto_imp_filterlim_at_right)
  qed
  thus ?thesis
    by (simp add: at_right_ereal filterlim_filtermap)
qed

proposition analytic_continuation':
  assumes hol: "f holomorphic_on S" "g holomorphic_on S"
      and "open S" and "connected S"
      and "U \<subseteq> S" and "\<xi> \<in> S"
      and "\<xi> islimpt U"
      and fU0 [simp]: "\<And>z. z \<in> U \<Longrightarrow> f z = g z"
      and "w \<in> S"
    shows "f w = g w"
  using analytic_continuation[OF holomorphic_on_diff[OF hol] assms(3-7) _ assms(9)] assms(8)
  by simp


subsection \<open>Various facts about integrals\<close>

lemma continuous_on_imp_set_integrable_cbox:
  fixes h :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "continuous_on (cbox a b) h"
  shows   "set_integrable lborel (cbox a b) h"
proof -
  from assms have "h absolutely_integrable_on cbox a b"
    by (rule absolutely_integrable_continuous)
  moreover have "(\<lambda>x. indicat_real (cbox a b) x *\<^sub>R h x) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on_indicator) (use assms in auto)
  ultimately show ?thesis
    unfolding set_integrable_def using assms by (subst (asm) integrable_completion) auto
qed

lemma set_nn_integral_cong:
  assumes "M = M'" "A = B" "\<And>x. x \<in> space M \<inter> A \<Longrightarrow> f x = g x"
  shows   "set_nn_integral M A f = set_nn_integral M' B g"
  using assms unfolding assms(1,2) by (intro nn_integral_cong) (auto simp: indicator_def)

lemma set_integrable_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and g :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_borel_measurable M A g"
  assumes "AE x in M. x \<in> A \<longrightarrow> norm (g x) \<le> norm (f x)"
  shows   "set_integrable M A g"
  unfolding set_integrable_def
proof (rule Bochner_Integration.integrable_bound)
  from assms(1) show "integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (simp add: set_integrable_def)
  from assms(2) show "(\<lambda>x. indicat_real A x *\<^sub>R g x) \<in> borel_measurable M"
    by (simp add: set_borel_measurable_def)
  from assms(3) show "AE x in M. norm (indicat_real A x *\<^sub>R g x) \<le> norm (indicat_real A x *\<^sub>R f x)"
    by eventually_elim (simp add: indicator_def)
qed

(* TODO replace version in library. Better name? *)
lemma nn_integral_has_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg: "\<And>x. x \<in> \<Omega> \<Longrightarrow> 0 \<le> f x" and I: "(f has_integral I) \<Omega>"
  shows "integral\<^sup>N lborel (\<lambda>x. indicator \<Omega> x * f x) = I"
proof -
  from I have "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
    by (rule has_integral_implies_lebesgue_measurable)
  then obtain f' :: "'a \<Rightarrow> real"
    where [measurable]: "f' \<in> borel \<rightarrow>\<^sub>M borel" and eq: "AE x in lborel. indicator \<Omega> x * f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)

  from I have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV"
    using nonneg by (simp add: indicator_def if_distrib[of "\<lambda>x. x * f y" for y] cong: if_cong)
  also have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV \<longleftrightarrow> ((\<lambda>x. abs (f' x)) has_integral I) UNIV"
    using eq by (intro has_integral_AE) auto
  finally have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = I"
    by (rule nn_integral_has_integral_lborel[rotated 2]) auto
  also have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = integral\<^sup>N lborel (\<lambda>x. abs (indicator \<Omega> x * f x))"
    using eq by (intro nn_integral_cong_AE) auto
  also have "(\<lambda>x. abs (indicator \<Omega> x * f x)) = (\<lambda>x. indicator \<Omega> x * f x)"
    using nonneg by (auto simp: indicator_def fun_eq_iff)
  finally show ?thesis .
qed


subsection \<open>Uniform convergence of integrals\<close>

lemma has_absolute_integral_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x)) :: real ^ 1) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x))) = (vec b :: real ^ 1)
         \<longleftrightarrow> (\<lambda>x. vec (f x) :: real ^ 1) absolutely_integrable_on (g ` S) \<and>
           integral (g ` S) (\<lambda>x. vec (f x)) = (vec b :: real ^ 1)"
    using assms unfolding has_field_derivative_iff_has_vector_derivative
    by (intro has_absolute_integral_change_of_variables_1 assms) auto
  thus ?thesis
    by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq)
qed

lemma set_nn_integral_lborel_eq_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes "set_borel_measurable borel A f"
  assumes "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "(\<integral>\<^sup>+x\<in>A. f x \<partial>lborel) < \<infinity>"
  shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>lborel) = integral A f"
proof -
  have eq: "(\<integral>\<^sup>+x\<in>A. f x \<partial>lborel) = (\<integral>\<^sup>+x. ennreal (indicator A x * f x) \<partial>lborel)"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = integral UNIV (\<lambda>x. indicator A x * f x)"
    using assms eq by (intro nn_integral_lborel_eq_integral)
                      (auto simp: indicator_def set_borel_measurable_def)
  also have "integral UNIV (\<lambda>x. indicator A x * f x) = integral A (\<lambda>x. indicator A x * f x)"
    by (rule integral_spike_set) (auto simp: indicator_def)
  also have "\<dots> = integral A f"
    by (rule integral_cong) (auto simp: indicator_def)
  finally show ?thesis .
qed

lemma nn_integral_has_integral_lebesgue':
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg: "\<And>x. x \<in> \<Omega> \<Longrightarrow> 0 \<le> f x" and I: "(f has_integral I) \<Omega>"
  shows "integral\<^sup>N lborel (\<lambda>x. ennreal (f x) * indicator \<Omega> x) = ennreal I"
proof -
  have "integral\<^sup>N lborel (\<lambda>x. ennreal (f x) * indicator \<Omega> x) =
        integral\<^sup>N lborel (\<lambda>x. ennreal (indicator \<Omega> x * f x))"
    by (intro nn_integral_cong) (auto simp: indicator_def)
  also have "\<dots> = ennreal I"
    using assms by (intro nn_integral_has_integral_lebesgue)
  finally show ?thesis .
qed

lemma uniform_limit_set_lebesgue_integral:
  fixes f :: "'a \<Rightarrow> 'b :: euclidean_space \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes "set_integrable lborel X' g"
  assumes [measurable]: "X' \<in> sets borel"
  assumes [measurable]: "\<And>y. y \<in> Y \<Longrightarrow> set_borel_measurable borel X' (f y)"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> (AE t\<in>X' in lborel. norm (f y t) \<le> g t)"
  assumes "eventually (\<lambda>x. X x \<in> sets borel \<and> X x \<subseteq> X') F"
  assumes "filterlim (\<lambda>x. set_lebesgue_integral lborel (X x) g)
             (nhds (set_lebesgue_integral lborel X' g)) F"
  shows "uniform_limit Y
           (\<lambda>x y. set_lebesgue_integral lborel (X x) (f y))
           (\<lambda>y. set_lebesgue_integral lborel X' (f y)) F"
proof (rule uniform_limitI, goal_cases)
  case (1 \<epsilon>)
  have integrable_g: "set_integrable lborel U g"
    if "U \<in> sets borel" "U \<subseteq> X'" for U
    by (rule set_integrable_subset[OF assms(1)]) (use that in auto)
  have "eventually (\<lambda>x. dist (set_lebesgue_integral lborel (X x) g)
                             (set_lebesgue_integral lborel X' g) < \<epsilon>) F"
    using \<open>\<epsilon> > 0\<close> assms by (auto simp: tendsto_iff)
  from this show ?case using \<open>eventually (\<lambda>_. _ \<and> _) F\<close>
  proof eventually_elim
    case (elim x)
    hence [measurable]:"X x \<in> sets borel" and "X x \<subseteq> X'" by auto
    have integrable: "set_integrable lborel U (f y)"
      if "y \<in> Y" "U \<in> sets borel" "U \<subseteq> X'" for y U
      apply (rule set_integrable_subset)
        apply (rule set_integrable_bound[OF assms(1)])
         apply (use assms(3) that in \<open>simp add: set_borel_measurable_def\<close>)
      using assms(4)[OF \<open>y \<in> Y\<close>] apply eventually_elim apply force
      using that apply simp_all
      done
    show ?case
    proof
      fix y assume "y \<in> Y"
      have "dist (set_lebesgue_integral lborel (X x) (f y))
                 (set_lebesgue_integral lborel X' (f y)) =
            norm (set_lebesgue_integral lborel X' (f y) -
                  set_lebesgue_integral lborel (X x) (f y))"
        by (simp add: dist_norm norm_minus_commute)
      also have "set_lebesgue_integral lborel X' (f y) -
                    set_lebesgue_integral lborel (X x) (f y) =
                 set_lebesgue_integral lborel (X' - X x) (f y)"
        unfolding set_lebesgue_integral_def
        apply (subst Bochner_Integration.integral_diff [symmetric])
        unfolding set_integrable_def [symmetric]
          apply (rule integrable; (fact | simp))
         apply (rule integrable; fact)
        apply (intro Bochner_Integration.integral_cong)
         apply (use \<open>X x \<subseteq> X'\<close> in \<open>auto simp: indicator_def\<close>)
        done
      also have "norm \<dots> \<le> (\<integral>t\<in>X'-X x. norm (f y t) \<partial>lborel)"
        by (intro set_integral_norm_bound integrable) (fact | simp)+
      also have "AE t\<in>X' - X x in lborel. norm (f y t) \<le> g t"
        using assms(4)[OF \<open>y \<in> Y\<close>] by eventually_elim auto
      with \<open>y \<in> Y\<close> have "(\<integral>t\<in>X'-X x. norm (f y t) \<partial>lborel) \<le> (\<integral>t\<in>X'-X x. g t \<partial>lborel)"
        by (intro set_integral_mono_AE set_integrable_norm integrable integrable_g) auto
      also have "\<dots> = (\<integral>t\<in>X'. g t \<partial>lborel) - (\<integral>t\<in>X x. g t \<partial>lborel)"
        unfolding set_lebesgue_integral_def
        apply (subst Bochner_Integration.integral_diff [symmetric])
        unfolding set_integrable_def [symmetric]
          apply (rule integrable_g; (fact | simp))
         apply (rule integrable_g; fact)
        apply (intro Bochner_Integration.integral_cong)
         apply (use \<open>X x \<subseteq> X'\<close> in \<open>auto simp: indicator_def\<close>)
        done
      also have "\<dots> \<le> dist (\<integral>t\<in>X x. g t \<partial>lborel) (\<integral>t\<in>X'. g t \<partial>lborel)"
        by (simp add: dist_norm)
      also have "\<dots> < \<epsilon>" by fact
      finally show "dist (set_lebesgue_integral lborel (X x) (f y))
                         (set_lebesgue_integral lborel X' (f y)) < \<epsilon>" .
    qed
  qed
qed

lemma integral_dominated_convergence_at_right:
  fixes s :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}" and w :: "'a \<Rightarrow> real"
    and f :: "'a \<Rightarrow> 'b" and M and c :: real
  assumes "f \<in> borel_measurable M" "\<And>t. s t \<in> borel_measurable M" "integrable M w"
  assumes lim: "AE x in M. ((\<lambda>i. s i x) \<longlongrightarrow> f x) (at_right c)"
  assumes bound: "\<forall>\<^sub>F i in at_right c. AE x in M. norm (s i x) \<le> w x"
  shows "((\<lambda>t. integral\<^sup>L M (s t)) \<longlongrightarrow> integral\<^sup>L M f) (at_right c)"
proof (rule tendsto_at_right_realI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume X: "filterlim X (at_right c) sequentially"
  from filterlim_iff[THEN iffD1, OF this, rule_format, OF bound]
  obtain N where w: "\<And>n. N \<le> n \<Longrightarrow> AE x in M. norm (s (X n) x) \<le> w x"
    by (auto simp: eventually_sequentially)

  show "(\<lambda>n. integral\<^sup>L M (s (X n))) \<longlonglongrightarrow> integral\<^sup>L M f"
  proof (rule LIMSEQ_offset, rule integral_dominated_convergence)
    show "AE x in M. norm (s (X (n + N)) x) \<le> w x" for n
      by (rule w) auto
    show "AE x in M. (\<lambda>n. s (X (n + N)) x) \<longlonglongrightarrow> f x"
      using lim
    proof eventually_elim
      fix x assume "((\<lambda>i. s i x) \<longlongrightarrow> f x) (at_right c)"
      then show "(\<lambda>n. s (X (n + N)) x) \<longlonglongrightarrow> f x"
        by (intro LIMSEQ_ignore_initial_segment filterlim_compose[OF _ X])
    qed
  qed fact+
qed

lemma integral_dominated_convergence_at_left:
  fixes s :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}" and w :: "'a \<Rightarrow> real"
    and f :: "'a \<Rightarrow> 'b" and M and c :: real
  assumes "f \<in> borel_measurable M" "\<And>t. s t \<in> borel_measurable M" "integrable M w"
  assumes lim: "AE x in M. ((\<lambda>i. s i x) \<longlongrightarrow> f x) (at_left c)"
  assumes bound: "\<forall>\<^sub>F i in at_left c. AE x in M. norm (s i x) \<le> w x"
  shows "((\<lambda>t. integral\<^sup>L M (s t)) \<longlongrightarrow> integral\<^sup>L M f) (at_left c)"
proof (rule tendsto_at_left_realI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume X: "filterlim X (at_left c) sequentially"
  from filterlim_iff[THEN iffD1, OF this, rule_format, OF bound]
  obtain N where w: "\<And>n. N \<le> n \<Longrightarrow> AE x in M. norm (s (X n) x) \<le> w x"
    by (auto simp: eventually_sequentially)

  show "(\<lambda>n. integral\<^sup>L M (s (X n))) \<longlonglongrightarrow> integral\<^sup>L M f"
  proof (rule LIMSEQ_offset, rule integral_dominated_convergence)
    show "AE x in M. norm (s (X (n + N)) x) \<le> w x" for n
      by (rule w) auto
    show "AE x in M. (\<lambda>n. s (X (n + N)) x) \<longlonglongrightarrow> f x"
      using lim
    proof eventually_elim
      fix x assume "((\<lambda>i. s i x) \<longlongrightarrow> f x) (at_left c)"
      then show "(\<lambda>n. s (X (n + N)) x) \<longlonglongrightarrow> f x"
        by (intro LIMSEQ_ignore_initial_segment filterlim_compose[OF _ X])
    qed
  qed fact+
qed

lemma uniform_limit_interval_integral_right:
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes "interval_lebesgue_integrable lborel a b g"
  assumes [measurable]: "\<And>y. y \<in> Y \<Longrightarrow> set_borel_measurable borel (einterval a b) (f y)"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> (AE t\<in>einterval a b in lborel. norm (f y t) \<le> g t)"
  assumes "a < b"
  shows   "uniform_limit Y (\<lambda>b' y. LBINT t=a..b'. f y t) (\<lambda>y. LBINT t=a..b. f y t) (at_left b)"
proof (cases "Y = {}")
  case False
  have g_nonneg: "AE t\<in>einterval a b in lborel. g t \<ge> 0"
  proof -
    from \<open>Y \<noteq> {}\<close> obtain y where "y \<in> Y" by auto
    from assms(3)[OF this] show ?thesis 
      by eventually_elim (auto elim: order.trans[rotated])
  qed

  have ev: "eventually (\<lambda>b'. b' \<in> {a<..<b}) (at_left b)"
    using \<open>a < b\<close> by (intro eventually_at_leftI)
  with \<open>a < b\<close> have "?thesis \<longleftrightarrow> uniform_limit Y (\<lambda>b' y. \<integral>t\<in>einterval a (min b b'). f y t \<partial>lborel)
                                  (\<lambda>y. \<integral>t\<in>einterval a b. f y t \<partial>lborel) (at_left b)"
    by (intro filterlim_cong arg_cong2[where f = uniformly_on])
       (auto simp: interval_lebesgue_integral_def fun_eq_iff min_def
             intro!: eventually_mono[OF ev])
  also have \<dots>
  proof (rule uniform_limit_set_lebesgue_integral[where g = g], goal_cases)
    show "\<forall>\<^sub>F b' in at_left b. einterval a (min b b') \<in> sets borel \<and>
                              einterval a (min b b') \<subseteq> einterval a b"
      using ev by eventually_elim (auto simp: einterval_def)
  next
    show "((\<lambda>b'. set_lebesgue_integral lborel (einterval a (min b b')) g) \<longlongrightarrow>
            set_lebesgue_integral lborel (einterval a b) g) (at_left b)"
      unfolding set_lebesgue_integral_def
    proof (intro tendsto_at_left_erealI_sequentially integral_dominated_convergence)
      have *: "set_borel_measurable borel (einterval a b) g"
        using assms(1) less_imp_le[OF \<open>a < b\<close>]
        by (simp add: interval_lebesgue_integrable_def set_integrable_def set_borel_measurable_def)
      show "(\<lambda>x. indicat_real (einterval a b) x *\<^sub>R g x) \<in> borel_measurable lborel"
        using * by (simp add: set_borel_measurable_def)
      fix X :: "nat \<Rightarrow> ereal" and n :: nat
      have "set_borel_measurable borel (einterval a (min b (X n))) g"
        by (rule set_borel_measurable_subset[OF *]) (auto simp: einterval_def)
      thus "(\<lambda>x. indicat_real (einterval a (min b (X n))) x *\<^sub>R g x) \<in> borel_measurable lborel"
        by (simp add: set_borel_measurable_def)
    next
      fix X :: "nat \<Rightarrow> ereal"
      assume X: "filterlim X (at_left b) sequentially"
      show "AE x in lborel. (\<lambda>n. indicat_real (einterval a (min b (X n))) x *\<^sub>R g x)
               \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x"
      proof (rule AE_I2)
        fix x :: real
        have "(\<lambda>t. indicator (einterval a (min b (X t))) x :: real) \<longlonglongrightarrow>
                indicator (einterval a b) x"
        proof (cases "x \<in> einterval a b")
          case False
          hence "x \<notin> einterval a (min b (X t))"for t by (auto simp: einterval_def)
          with False show ?thesis by (simp add: indicator_def)
        next
          case True
          with \<open>a < b\<close> have "eventually (\<lambda>t. t \<in> {max a x<..<b}) (at_left b)"
            by (intro eventually_at_leftI[of "ereal x"]) (auto simp: einterval_def min_def)
          from this and X have "eventually (\<lambda>t. X t \<in> {max a x<..<b}) sequentially"
            by (rule eventually_compose_filterlim)
          hence "eventually (\<lambda>t. indicator (einterval a (min b (X t))) x = (1 :: real)) sequentially"
            by eventually_elim (use True in \<open>auto simp: indicator_def einterval_def\<close>)
          from tendsto_eventually[OF this] and True show ?thesis
            by (simp add: indicator_def)
        qed
        thus "(\<lambda>n. indicat_real (einterval a (min b (X n))) x *\<^sub>R g x)
                 \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x" by (intro tendsto_intros)
      qed
    next
      fix X :: "nat \<Rightarrow> ereal" and n :: nat
      show "AE x in lborel. norm (indicator (einterval a (min b (X n))) x *\<^sub>R g x) \<le>
              indicator (einterval a b) x *\<^sub>R g x"
        using g_nonneg by eventually_elim (auto simp: indicator_def einterval_def)
    qed (use assms less_imp_le[OF \<open>a < b\<close>] in 
         \<open>auto simp: interval_lebesgue_integrable_def set_integrable_def\<close>) 
  qed (use assms in \<open>auto simp: interval_lebesgue_integrable_def\<close>)
  finally show ?thesis .
qed auto

lemma uniform_limit_interval_integral_left:
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes "interval_lebesgue_integrable lborel a b g"
  assumes [measurable]: "\<And>y. y \<in> Y \<Longrightarrow> set_borel_measurable borel (einterval a b) (f y)"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> (AE t\<in>einterval a b in lborel. norm (f y t) \<le> g t)"
  assumes "a < b"
  shows   "uniform_limit Y (\<lambda>a' y. LBINT t=a'..b. f y t) (\<lambda>y. LBINT t=a..b. f y t) (at_right a)"
proof (cases "Y = {}")
  case False
  have g_nonneg: "AE t\<in>einterval a b in lborel. g t \<ge> 0"
  proof -
    from \<open>Y \<noteq> {}\<close> obtain y where "y \<in> Y" by auto
    from assms(3)[OF this] show ?thesis 
      by eventually_elim (auto elim: order.trans[rotated])
  qed

  have ev: "eventually (\<lambda>b'. b' \<in> {a<..<b}) (at_right a)"
    using \<open>a < b\<close> by (intro eventually_at_rightI)
  with \<open>a < b\<close> have "?thesis \<longleftrightarrow> uniform_limit Y (\<lambda>a' y. \<integral>t\<in>einterval (max a a') b. f y t \<partial>lborel)
                                  (\<lambda>y. \<integral>t\<in>einterval a b. f y t \<partial>lborel) (at_right a)"
    by (intro filterlim_cong arg_cong2[where f = uniformly_on])
       (auto simp: interval_lebesgue_integral_def fun_eq_iff max_def
             intro!: eventually_mono[OF ev])
  also have \<dots>
  proof (rule uniform_limit_set_lebesgue_integral[where g = g], goal_cases)
    show "\<forall>\<^sub>F a' in at_right a. einterval (max a a') b \<in> sets borel \<and>
                              einterval (max a a') b \<subseteq> einterval a b"
      using ev by eventually_elim (auto simp: einterval_def)
  next
    show "((\<lambda>a'. set_lebesgue_integral lborel (einterval (max a a') b) g) \<longlongrightarrow>
            set_lebesgue_integral lborel (einterval a b) g) (at_right a)"
      unfolding set_lebesgue_integral_def
    proof (intro tendsto_at_right_erealI_sequentially integral_dominated_convergence)
      have *: "set_borel_measurable borel (einterval a b) g"
        using assms(1) less_imp_le[OF \<open>a < b\<close>]
        by (simp add: interval_lebesgue_integrable_def set_integrable_def set_borel_measurable_def)
      show "(\<lambda>x. indicat_real (einterval a b) x *\<^sub>R g x) \<in> borel_measurable lborel"
        using * by (simp add: set_borel_measurable_def)
      fix X :: "nat \<Rightarrow> ereal" and n :: nat
      have "set_borel_measurable borel (einterval (max a (X n)) b) g"
        by (rule set_borel_measurable_subset[OF *]) (auto simp: einterval_def)
      thus "(\<lambda>x. indicat_real (einterval (max a (X n)) b) x *\<^sub>R g x) \<in> borel_measurable lborel"
        by (simp add: set_borel_measurable_def)
    next
      fix X :: "nat \<Rightarrow> ereal"
      assume X: "filterlim X (at_right a) sequentially"
      show "AE x in lborel. (\<lambda>n. indicat_real (einterval (max a (X n)) b) x *\<^sub>R g x)
               \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x"
      proof (rule AE_I2)
        fix x :: real
        have "(\<lambda>t. indicator (einterval (max a (X t)) b) x :: real) \<longlonglongrightarrow>
                indicator (einterval a b) x"
        proof (cases "x \<in> einterval a b")
          case False
          hence "x \<notin> einterval (max a (X t)) b"for t by (auto simp: einterval_def)
          with False show ?thesis by (simp add: indicator_def)
        next
          case True
          with \<open>a < b\<close> have "eventually (\<lambda>t. t \<in> {a<..<x}) (at_right a)"
            by (intro eventually_at_rightI[of _ "ereal x"]) (auto simp: einterval_def min_def)
          from this and X have "eventually (\<lambda>t. X t \<in> {a<..<x}) sequentially"
            by (rule eventually_compose_filterlim)
          hence "eventually (\<lambda>t. indicator (einterval (max a (X t)) b) x = (1 :: real)) sequentially"
            by eventually_elim (use True in \<open>auto simp: indicator_def einterval_def\<close>)
          from tendsto_eventually[OF this] and True show ?thesis
            by (simp add: indicator_def)
        qed
        thus "(\<lambda>n. indicat_real (einterval (max a (X n)) b) x *\<^sub>R g x)
                 \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x" by (intro tendsto_intros)
      qed
    next
      fix X :: "nat \<Rightarrow> ereal" and n :: nat
      show "AE x in lborel. norm (indicator (einterval (max a (X n)) b) x *\<^sub>R g x) \<le>
              indicator (einterval a b) x *\<^sub>R g x"
        using g_nonneg by eventually_elim (auto simp: indicator_def einterval_def)
    qed (use assms less_imp_le[OF \<open>a < b\<close>] in 
         \<open>auto simp: interval_lebesgue_integrable_def set_integrable_def\<close>) 
  qed (use assms in \<open>auto simp: interval_lebesgue_integrable_def\<close>)
  finally show ?thesis .
qed auto

lemma uniform_limit_interval_integral_sequentially:
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes "interval_lebesgue_integrable lborel a b g"
  assumes [measurable]: "\<And>y. y \<in> Y \<Longrightarrow> set_borel_measurable borel (einterval a b) (f y)"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> (AE t\<in>einterval a b in lborel. norm (f y t) \<le> g t)"
  assumes a': "filterlim a' (at_right a) sequentially"
  assumes b': "filterlim b' (at_left b) sequentially"
  assumes "a < b"
  shows   "uniform_limit Y (\<lambda>n y. LBINT t=a' n..b' n. f y t)
             (\<lambda>y. LBINT t=a..b. f y t) sequentially"
proof (cases "Y = {}")
  case False
  have g_nonneg: "AE t\<in>einterval a b in lborel. g t \<ge> 0"
  proof -
    from \<open>Y \<noteq> {}\<close> obtain y where "y \<in> Y" by auto
    from assms(3)[OF this] show ?thesis 
      by eventually_elim (auto elim: order.trans[rotated])
  qed

  have ev: "eventually (\<lambda>n. a < a' n \<and> a' n < b' n \<and> b' n < b) sequentially"
  proof -
    from ereal_dense2[OF \<open>a < b\<close>] obtain t where t: "a < ereal t" "ereal t < b" by blast
    from t have "eventually (\<lambda>n. a' n \<in> {a<..<t}) sequentially"
      by (intro eventually_compose_filterlim[OF _ a'] eventually_at_rightI[of _ "ereal t"])
    moreover from t have "eventually (\<lambda>n. b' n \<in> {t<..<b}) sequentially"
      by (intro eventually_compose_filterlim[OF _ b'] eventually_at_leftI[of "ereal t"])
    ultimately show "eventually (\<lambda>n. a < a' n \<and> a' n < b' n \<and> b' n < b) sequentially"
      by eventually_elim auto
  qed

  have "?thesis \<longleftrightarrow> uniform_limit Y (\<lambda>n y. \<integral>t\<in>einterval (max a (a' n)) (min b (b' n)). f y t \<partial>lborel)
                      (\<lambda>y. \<integral>t\<in>einterval a b. f y t \<partial>lborel) sequentially" using \<open>a < b\<close>
    by (intro filterlim_cong arg_cong2[where f = uniformly_on])
       (auto simp: interval_lebesgue_integral_def fun_eq_iff min_def max_def
             intro!: eventually_mono[OF ev])
  also have \<dots>
  proof (rule uniform_limit_set_lebesgue_integral[where g = g], goal_cases)
    show "\<forall>\<^sub>F n in sequentially. einterval (max a (a' n)) (min b (b' n)) \<in> sets borel \<and>
                                einterval (max a (a' n)) (min b (b' n)) \<subseteq> einterval a b"
      using ev by eventually_elim (auto simp: einterval_def)
  next
    show "((\<lambda>n. set_lebesgue_integral lborel (einterval (max a (a' n)) (min b (b' n))) g) \<longlongrightarrow>
            set_lebesgue_integral lborel (einterval a b) g) sequentially"
      unfolding set_lebesgue_integral_def
    proof (intro integral_dominated_convergence)
      have *: "set_borel_measurable borel (einterval a b) g"
        using assms(1) less_imp_le[OF \<open>a < b\<close>]
        by (simp add: interval_lebesgue_integrable_def set_integrable_def set_borel_measurable_def)
      show "(\<lambda>x. indicat_real (einterval a b) x *\<^sub>R g x) \<in> borel_measurable lborel"
        using * by (simp add: set_borel_measurable_def)
      fix n :: nat
      have "set_borel_measurable borel (einterval (max a (a' n)) (min b (b' n))) g"
        by (rule set_borel_measurable_subset[OF *]) (auto simp: einterval_def)
      thus "(\<lambda>x. indicat_real (einterval (max a (a' n)) (min b (b' n))) x *\<^sub>R g x) \<in> borel_measurable lborel"
        by (simp add: set_borel_measurable_def)
    next
      show "AE x in lborel. (\<lambda>n. indicat_real (einterval (max a (a' n)) (min b (b' n))) x *\<^sub>R g x)
               \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x"
      proof (rule AE_I2)
        fix x :: real
        have "(\<lambda>t. indicator (einterval (max a (a' t)) (min b (b' t))) x :: real) \<longlonglongrightarrow>
                indicator (einterval a b) x"
        proof (cases "x \<in> einterval a b")
          case False
          hence "x \<notin> einterval (max a (a' t)) (min b (b' t))"for t
            by (auto simp: einterval_def)
          with False show ?thesis by (simp add: indicator_def)
        next
          case True
          with \<open>a < b\<close> have "eventually (\<lambda>t. t \<in> {a<..<x}) (at_right a)"
            by (intro eventually_at_rightI[of _ "ereal x"]) (auto simp: einterval_def min_def)

          have "eventually (\<lambda>n. x \<in> {a' n<..<b' n}) sequentially"
          proof -
            have "eventually (\<lambda>n. a' n \<in> {a<..<x}) sequentially" using True
              by (intro eventually_compose_filterlim[OF _ a'] eventually_at_rightI[of _ "ereal x"])
                 (auto simp: einterval_def)
            moreover have "eventually (\<lambda>n. b' n \<in> {x<..<b}) sequentially" using True
              by (intro eventually_compose_filterlim[OF _ b'] eventually_at_leftI[of "ereal x"])
                 (auto simp: einterval_def)
            ultimately show "eventually (\<lambda>n. x \<in> {a' n<..<b' n}) sequentially"
              by eventually_elim auto
          qed
          hence "eventually (\<lambda>t. indicator (einterval (max a (a' t)) (min b (b' t))) x = (1 :: real)) sequentially"
            by eventually_elim (use True in \<open>auto simp: indicator_def einterval_def\<close>)
          from tendsto_eventually[OF this] and True show ?thesis
            by (simp add: indicator_def)
        qed
        thus "(\<lambda>n. indicat_real (einterval (max a (a' n)) (min b (b' n))) x *\<^sub>R g x)
                 \<longlonglongrightarrow> indicat_real (einterval a b) x *\<^sub>R g x" by (intro tendsto_intros)
      qed
    next
      fix X :: "nat \<Rightarrow> ereal" and n :: nat
      show "AE x in lborel. norm (indicator (einterval (max a (a' n)) (min b (b' n))) x *\<^sub>R g x) \<le>
              indicator (einterval a b) x *\<^sub>R g x"
        using g_nonneg by eventually_elim (auto simp: indicator_def einterval_def)
    qed (use assms less_imp_le[OF \<open>a < b\<close>] in 
         \<open>auto simp: interval_lebesgue_integrable_def set_integrable_def\<close>) 
  qed (use assms in \<open>auto simp: interval_lebesgue_integrable_def\<close>)
  finally show ?thesis .
qed auto

lemma interval_lebesgue_integrable_combine:
  assumes "interval_lebesgue_integrable lborel A B f"
  assumes "interval_lebesgue_integrable lborel B C f"
  assumes "set_borel_measurable borel (einterval A C) f"
  assumes "A \<le> B" "B \<le> C"
  shows   "interval_lebesgue_integrable lborel A C f"
proof -
  have meas: "set_borel_measurable borel (einterval A B \<union> einterval B C) f"
    by (rule set_borel_measurable_subset[OF assms(3)]) (use assms in \<open>auto simp: einterval_def\<close>)
  have "set_integrable lborel (einterval A B \<union> einterval B C) f"
    using assms by (intro set_integrable_Un) (auto simp: interval_lebesgue_integrable_def)
  also have "?this \<longleftrightarrow> set_integrable lborel (einterval A C) f"
  proof (cases "B \<in> {\<infinity>, -\<infinity>}")
    case True
    with assms have "einterval A B \<union> einterval B C = einterval A C"
      by (auto simp: einterval_def)
    thus ?thesis by simp
  next
    case False
    then obtain B' where [simp]: "B = ereal B'"
      by (cases B) auto
    have "indicator (einterval A C) x = (indicator (einterval A B \<union> einterval B C) x :: real)"
      if "x \<noteq> B'" for x using assms(4,5) that
      by (cases A; cases C) (auto simp: einterval_def indicator_def)
    hence "{x \<in> space lborel. indicat_real (einterval A B \<union> einterval B C) x *\<^sub>R f x \<noteq>
              indicat_real (einterval A C) x *\<^sub>R f x} \<subseteq> {B'}" by force
    thus ?thesis unfolding set_integrable_def using meas assms
      by (intro integrable_cong_AE AE_I[of _ _ "{B'}"])
         (simp_all add: set_borel_measurable_def)
  qed
  also have "\<dots> \<longleftrightarrow> ?thesis"
    using order.trans[OF assms(4,5)] by (simp add: interval_lebesgue_integrable_def)
  finally show ?thesis .
qed

lemma interval_lebesgue_integrable_bigo_right:
  fixes A B :: real
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> O[at_left B](g)"
  assumes cont: "continuous_on {A..<B} f"
  assumes meas: "set_borel_measurable borel {A<..<B} f"
  assumes "interval_lebesgue_integrable lborel A B g"
  assumes "A < B"
  shows   "interval_lebesgue_integrable lborel A B f"
proof -
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) (at_left B)"
    by (elim landau_o.bigE)
  then obtain B' where B': "B' < B" "\<And>x. x \<in> {B'<..<B} \<Longrightarrow> norm (f x) \<le> c * norm (g x)"
    using \<open>A < B\<close> by (auto simp: Topological_Spaces.eventually_at_left[of A])

  show ?thesis
  proof (rule interval_lebesgue_integrable_combine)
    show "interval_lebesgue_integrable lborel A (max A B') f"
      using B' assms
      by (intro interval_integrable_continuous_on continuous_on_subset[OF cont]) auto
    show "set_borel_measurable borel (einterval (ereal A) (ereal B)) f"
      using assms by simp
    have meas': "set_borel_measurable borel {max A B'<..<B} f"
      by (rule set_borel_measurable_subset[OF meas]) auto
    have "set_integrable lborel {max A B'<..<B} f"
    proof (rule set_integrable_bound[OF _ _ AE_I2[OF impI]])
      have "set_integrable lborel {A<..<B} (\<lambda>x. c * g x)"
        using assms by (simp add: interval_lebesgue_integrable_def)
      thus "set_integrable lborel {max A B'<..<B} (\<lambda>x. c * g x)"
        by (rule set_integrable_subset) auto
    next
      fix x assume "x \<in> {max A B'<..<B}"
      hence "norm (f x) \<le> c * norm (g x)"
        by (intro B') auto
      also have "\<dots> \<le> norm (c * g x)"
        unfolding norm_mult by (intro mult_right_mono) auto
      finally show  "norm (f x) \<le> norm (c * g x)" .
    qed (use meas' in \<open>simp_all add: set_borel_measurable_def\<close>)
    thus "interval_lebesgue_integrable lborel (ereal (max A B')) (ereal B) f"
      unfolding interval_lebesgue_integrable_def einterval_eq_Icc using \<open>B' < B\<close> assms by simp
  qed (use B' assms in auto)
qed

lemma interval_lebesgue_integrable_bigo_left:
  fixes A B :: real
  fixes f :: "real \<Rightarrow> real"
  assumes "f \<in> O[at_right A](g)"
  assumes cont: "continuous_on {A<..B} f"
  assumes meas: "set_borel_measurable borel {A<..<B} f"
  assumes "interval_lebesgue_integrable lborel A B g"
  assumes "A < B"
  shows   "interval_lebesgue_integrable lborel A B f"
proof -
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) (at_right A)"
    by (elim landau_o.bigE)
  then obtain A' where A': "A' > A" "\<And>x. x \<in> {A<..<A'} \<Longrightarrow> norm (f x) \<le> c * norm (g x)"
    using \<open>A < B\<close> by (auto simp: Topological_Spaces.eventually_at_right[of A])

  show ?thesis
  proof (rule interval_lebesgue_integrable_combine)
    show "interval_lebesgue_integrable lborel (min B A') B f"
      using A' assms
      by (intro interval_integrable_continuous_on continuous_on_subset[OF cont]) auto
    show "set_borel_measurable borel (einterval (ereal A) (ereal B)) f"
      using assms by simp
    have meas': "set_borel_measurable borel {A<..<min B A'} f"
      by (rule set_borel_measurable_subset[OF meas]) auto
    have "set_integrable lborel {A<..<min B A'} f"
    proof (rule set_integrable_bound[OF _ _ AE_I2[OF impI]])
      have "set_integrable lborel {A<..<B} (\<lambda>x. c * g x)"
        using assms by (simp add: interval_lebesgue_integrable_def)
      thus "set_integrable lborel {A<..<min B A'} (\<lambda>x. c * g x)"
        by (rule set_integrable_subset) auto
    next
      fix x assume "x \<in> {A<..<min B A'}"
      hence "norm (f x) \<le> c * norm (g x)"
        by (intro A') auto
      also have "\<dots> \<le> norm (c * g x)"
        unfolding norm_mult by (intro mult_right_mono) auto
      finally show  "norm (f x) \<le> norm (c * g x)" .
    qed (use meas' in \<open>simp_all add: set_borel_measurable_def\<close>)
    thus "interval_lebesgue_integrable lborel (ereal A) (ereal (min B A')) f"
      unfolding interval_lebesgue_integrable_def einterval_eq_Icc using \<open>A' > A\<close> assms by simp
  qed (use A' assms in auto)
qed


subsection \<open>Other material\<close>

(* TODO: Library *)
lemma summable_comparison_test_bigo:
  fixes f :: "nat \<Rightarrow> real"
  assumes "summable (\<lambda>n. norm (g n))" "f \<in> O(g)"
  shows   "summable f"
proof -
  from \<open>f \<in> O(g)\<close> obtain C where C: "eventually (\<lambda>x. norm (f x) \<le> C * norm (g x)) at_top"
    by (auto elim: landau_o.bigE)
  thus ?thesis
    by (rule summable_comparison_test_ev) (insert assms, auto intro: summable_mult)
qed

lemma fps_expansion_cong:
  assumes "eventually (\<lambda>x. g x = h x) (nhds x)"
  shows   "fps_expansion g x = fps_expansion h x"
proof -
  have "(deriv ^^ n) g x = (deriv ^^ n) h x" for n
    by (intro higher_deriv_cong_ev assms refl)
  thus ?thesis by (simp add: fps_expansion_def)
qed

lemma fps_expansion_eq_zero_iff:
  assumes "g holomorphic_on ball z r" "r > 0"
  shows   "fps_expansion g z = 0 \<longleftrightarrow> (\<forall>z\<in>ball z r. g z = 0)"
proof
  assume *: "\<forall>z\<in>ball z r. g z = 0"
  have "eventually (\<lambda>w. w \<in> ball z r) (nhds z)"
    using assms by (intro eventually_nhds_in_open) auto
  hence "eventually (\<lambda>z. g z = 0) (nhds z)"
    by eventually_elim (use * in auto)
  hence "fps_expansion g z = fps_expansion (\<lambda>_. 0) z"
    by (intro fps_expansion_cong)
  thus "fps_expansion g z = 0"
    by (simp add: fps_expansion_def fps_zero_def)
next
  assume *: "fps_expansion g z = 0"
  have "g w = 0" if "w \<in> ball z r" for w
    by (rule holomorphic_fun_eq_0_on_ball[OF assms(1) that])
       (use * in \<open>auto simp: fps_expansion_def fps_eq_iff\<close>)
  thus "\<forall>w\<in>ball z r. g w = 0" by blast
qed

lemma fds_nth_higher_deriv:
  "fds_nth ((fds_deriv ^^ k) F) = (\<lambda>n. (-1) ^ k * of_real (ln n) ^ k * fds_nth F n)"
  by (induction k) (auto simp: fds_nth_deriv fun_eq_iff simp flip: scaleR_conv_of_real)

lemma binomial_n_n_minus_one [simp]: "n > 0 \<Longrightarrow> n choose (n - Suc 0) = n"
  by (cases n) auto

lemma has_field_derivative_complex_powr_right:
  "w \<noteq> 0 \<Longrightarrow> ((\<lambda>z. w powr z) has_field_derivative Ln w * w powr z) (at z within A)"
  by (rule DERIV_subset, rule has_field_derivative_powr_right) auto

lemmas has_field_derivative_complex_powr_right' =
  has_field_derivative_complex_powr_right[THEN DERIV_chain2]

end