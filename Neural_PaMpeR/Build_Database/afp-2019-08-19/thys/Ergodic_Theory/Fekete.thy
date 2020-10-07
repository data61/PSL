(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Subadditive and submultiplicative sequences\<close>

theory Fekete
  imports "HOL-Analysis.Analysis"
begin

text \<open>A real sequence is subadditive if $u_{n+m} \leq u_n+u_m$. This implies the
convergence of $u_n/n$ to $Inf\{u_n/n\} \in [-\infty, +\infty)$, a useful result known
as Fekete lemma. We prove it below.

Taking logarithms, the same result applies to submultiplicative sequences. We illustrate
it with the definition of the spectral radius as the limit of $\|x^n\|^{1/n}$, the
convergence following from Fekete lemma.\<close>


subsection \<open>Subadditive sequences\<close>

text \<open>We define subadditive sequences, either from the start or eventually.\<close>

definition subadditive::"(nat\<Rightarrow>real) \<Rightarrow> bool"
  where "subadditive u = (\<forall>m n. u (m+n) \<le> u m + u n)"

lemma subadditiveI:
  assumes "\<And>m n. u (m+n) \<le> u m + u n"
  shows "subadditive u"
unfolding subadditive_def using assms by auto

lemma subadditiveD:
  assumes "subadditive u"
  shows "u (m+n) \<le> u m + u n"
using assms unfolding subadditive_def by auto

lemma subadditive_un_le_nu1:
  assumes "subadditive u"
          "n > 0"
  shows "u n \<le> n * u 1"
proof -
  have *: "n = 0 \<or> (u n \<le> n * u 1)" for n
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    consider "n = 0" | "n > 0" by auto
    then show ?case
    proof (cases)
      case 1
      then show ?thesis by auto
    next
      case 2
      then have "u (Suc n) \<le> u n + u 1" using subadditiveD[OF assms(1), of n 1] by auto
      then show ?thesis using Suc.IH 2 by (auto simp add: algebra_simps)
    qed
  qed
  show ?thesis using *[of n] \<open>n > 0\<close> by auto
qed

definition eventually_subadditive::"(nat\<Rightarrow>real) \<Rightarrow> nat \<Rightarrow> bool"
  where "eventually_subadditive u N0 = (\<forall>m>N0. \<forall>n>N0. u (m+n) \<le> u m + u n)"

lemma eventually_subadditiveI:
  assumes "\<And>m n. m > N0 \<Longrightarrow> n > N0 \<Longrightarrow> u (m+n) \<le> u m + u n"
  shows "eventually_subadditive u N0"
unfolding eventually_subadditive_def using assms by auto

lemma subadditive_imp_eventually_subadditive:
  assumes "subadditive u"
  shows "eventually_subadditive u 0"
using assms unfolding subadditive_def eventually_subadditive_def by auto

text \<open>The main inequality that will lead to convergence is given in the next lemma:
given $n$, then eventually $u_m/m$ is bounded by $u_n/n$, up to an arbitrarily small error.
This is proved by doing the euclidean division of $m$ by $n$ and using the subadditivity.
(the remainder in the euclidean division will give the error term.)\<close>

lemma eventually_subadditive_ineq:
  assumes "eventually_subadditive u N0" "e>0" "n>N0"
  shows "\<exists>N>N0. \<forall>m\<ge>N. u m/m < u n/n + e"
proof -
  have ineq_rec: "u(a*n+r) \<le> a * u n + u r" if "n>N0" "r>N0" for a n r
  proof (induct a)
    case (Suc a)
    have "a*n+r>N0" using \<open>r>N0\<close> by simp
    have "u((Suc a)*n+r) = u(a*n+r+n)" by (simp add: algebra_simps)
    also have "... \<le> u(a*n+r)+u n" using assms \<open>n>N0\<close> \<open>a*n+r>N0\<close> eventually_subadditive_def by blast
    also have "... \<le> a*u n + u r + u n" by (simp add: Suc.hyps)
    also have "... = (Suc a) * u n + u r" by (simp add: algebra_simps)
    finally show ?case by simp
  qed (simp)

  have "n>0" "real n > 0" using \<open>n>N0\<close> by auto
  define C where "C = Max {abs(u i) |i. i\<le>2*n}"
  have ineq_C: "abs(u i) \<le> C" if "i \<le> 2 * n" for i
    unfolding C_def by (intro Max_ge, auto simp add: that)

  have ineq_all_m: "u m/m \<le> u n/n + 3*C/m" if "m\<ge>n" for m
  proof -
    have "real m>0" using \<open>m\<ge>n\<close> \<open>0 < real n\<close> by linarith

    obtain a0 r0 where "r0<n" "m = a0*n+r0"
      using \<open>0 < n\<close> mod_div_decomp mod_less_divisor by blast
    define a where "a = a0-1"
    define r where "r = r0+n"
    have "r<2*n" "r\<ge>n" unfolding r_def by (auto simp add: \<open>r0<n\<close>)
    have "a0>0" using \<open>m = a0*n + r0\<close> \<open>n \<le> m\<close> \<open>r0 < n\<close> not_le by fastforce
    then have "m = a * n + r" using a_def r_def \<open>m = a0*n+r0\<close> mult_eq_if by auto
    then have real_eq: "-r = real n * a - m" by simp

    have "r>N0" using \<open>r\<ge>n\<close> \<open>n>N0\<close> by simp
    then have "u m \<le> a * u n + u r" using ineq_rec \<open>m = a*n+r\<close> \<open>n>N0\<close> by simp
    then have "n * u m \<le> n * (a * u n + u r)" using \<open>real n>0\<close> by simp
    then have "n * u m - m * u n \<le> -r * u n + n * u r"
      unfolding real_eq by (simp add: algebra_simps)
    also have "... \<le> r * abs(u n) + n * abs(u r)"
      apply (intro add_mono mult_left_mono) using real_0_le_add_iff by fastforce+
    also have "... \<le> (2 * n) * C + n * C"
      apply (intro add_mono mult_mono ineq_C) using less_imp_le[OF \<open>r < 2 * n\<close>] by auto
    finally have "n * u m - m * u n \<le> 3*C*n" by auto
    then show "u m/m \<le> u n/n + 3*C/m"
      using \<open>0 < real n\<close> \<open>0 < real m\<close> by (simp add: divide_simps mult.commute)
  qed

  obtain M::nat where M: "M \<ge> 3 * C / e" using real_nat_ceiling_ge by auto
  define N where "N = M + n + N0 + 1"
  have "N > 3 * C / e" "N \<ge> n" "N > N0" unfolding N_def using M by auto
  have "u m/m < u n/n + e" if "m \<ge> N" for m
  proof -
    have "3 * C / m < e"
      using that \<open>N > 3 * C / e\<close> \<open>e > 0\<close> apply (auto simp add: algebra_simps divide_simps)
      by (meson le_less_trans linorder_not_le mult_less_cancel_left_pos of_nat_less_iff)
    then show ?thesis using ineq_all_m[of m] \<open>n \<le> N\<close> \<open>N \<le> m\<close> by auto
  qed
  then show ?thesis using \<open>N0 < N\<close> by blast
qed

text \<open>From the inequality above, we deduce the convergence of $u_n/n$ to its infimum. As this
infimum might be $-\infty$, we formulate this convergence in the extended reals. Then, we
specialize it to the real situation, separating the cases where $u_n/n$ is bounded below or not.\<close>

lemma subadditive_converges_ereal':
  assumes "eventually_subadditive u N0"
  shows "(\<lambda>m. ereal(u m/m)) \<longlonglongrightarrow> Inf {ereal(u n/n) | n. n>N0}"
proof -
  define v where "v = (\<lambda>m. ereal(u m/m))"
  define V where "V = {v n | n. n>N0}"
  define l where "l = Inf V"

  have "\<And>t. t\<in>V \<Longrightarrow> t\<ge>l" by (simp add: Inf_lower l_def)
  then have "v n \<ge> l" if "n > N0" for n using V_def that by blast
  then have lower: "eventually (\<lambda>n. a < v n) sequentially" if "a < l" for a
    by (meson that dual_order.strict_trans1 eventually_at_top_dense)

  have upper: "eventually (\<lambda>n. a > v n) sequentially" if "a > l" for a
  proof -
    obtain t where "t\<in>V" "t<a" by (metis \<open>a>l\<close> Inf_greatest l_def not_le)
    then obtain e::real where "e>0" "t+e < a" by (meson ereal_le_epsilon2 leD le_less_linear)
    obtain n where "n>N0" "t = u n/n" using V_def v_def \<open>t \<in> V\<close> by blast
    then have "u n/n + e < a" using \<open>t+e < a\<close> by simp
    obtain N where "\<forall>m\<ge>N. u m/m < u n/n + e"
      using eventually_subadditive_ineq[OF assms] \<open>0 < e\<close> \<open>N0 < n\<close> by blast
    then have "u m/m < a" if "m \<ge> N" for m
      using that \<open>u n/n + e < a\<close> less_ereal.simps(1) less_trans by blast
    then have "v m< a" if "m \<ge> N" for m using v_def that by blast
    then show ?thesis using eventually_at_top_linorder by auto
  qed
  show ?thesis
    using lower upper unfolding V_def l_def v_def by (simp add: order_tendsto_iff)
qed

lemma subadditive_converges_ereal:
  assumes "subadditive u"
  shows "(\<lambda>m. ereal(u m/m)) \<longlonglongrightarrow> Inf {ereal(u n/n) | n. n>0}"
by (rule subadditive_converges_ereal'[OF subadditive_imp_eventually_subadditive[OF assms]])

lemma subadditive_converges_bounded':
  assumes "eventually_subadditive u N0"
          "bdd_below {u n/n | n. n>N0}"
  shows "(\<lambda>n. u n/n) \<longlonglongrightarrow> Inf {u n/n | n. n>N0}"
proof-
  have *: "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> Inf {ereal(u n/n)|n. n > N0}"
    by (simp add: assms(1) subadditive_converges_ereal')
  define V where "V = {u n/n | n. n>N0}"
  have a: "bdd_below V" "V\<noteq>{}" by (auto simp add: V_def assms(2))
  have "Inf {ereal(t)| t. t\<in>V} = ereal(Inf V)" by (subst ereal_Inf'[OF a], simp add: Setcompr_eq_image)
  moreover have "{ereal(t)| t. t\<in>V} = {ereal(u n/n)|n. n > N0}" using V_def by blast
  ultimately have "Inf {ereal(u n/n)|n. n > N0} = ereal(Inf {u n/n |n. n > N0})" using V_def by auto
  then have "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> ereal(Inf {u n/n | n. n>N0})" using * by auto
  then show ?thesis by simp
qed

lemma subadditive_converges_bounded:
  assumes "subadditive u"
          "bdd_below {u n/n | n. n>0}"
  shows "(\<lambda>n. u n/n) \<longlonglongrightarrow> Inf {u n/n | n. n>0}"
by (rule subadditive_converges_bounded'[OF subadditive_imp_eventually_subadditive[OF assms(1)] assms(2)])

text \<open>We reformulate the previous lemma in a more directly usable form, avoiding the infimum.\<close>

lemma subadditive_converges_bounded'':
  assumes "subadditive u"
          "\<And>n. n > 0 \<Longrightarrow> u n \<ge> n * (a::real)"
  shows "\<exists>l. (\<lambda>n. u n / n) \<longlonglongrightarrow> l \<and> (\<forall>n>0. u n \<ge> n * l)"
proof -
  have B: "bdd_below {u n/n | n. n>0}"
    apply (rule bdd_belowI[of _ a]) using assms(2)
    apply (auto simp add: divide_simps)
    by (metis linordered_field_class.sign_simps(5) mult_left_le_imp_le of_nat_0_less_iff)
  define l where "l = Inf {u n/n | n. n>0}"
  have *: "u n / n \<ge> l" if "n > 0" for n
    unfolding l_def using that by (auto intro!: cInf_lower[OF _ B])
  show ?thesis
    apply (rule exI[of _ l], auto)
    using subadditive_converges_bounded[OF assms(1) B] apply (simp add: l_def)
    using * by (simp add: divide_simps algebra_simps)
qed

lemma subadditive_converges_unbounded':
  assumes "eventually_subadditive u N0"
          "\<not> (bdd_below {u n/n | n. n>N0})"
  shows "(\<lambda>n. ereal(u n/n)) \<longlonglongrightarrow> -\<infinity>"
proof -
  have *: "(\<lambda>n. ereal(u n /n)) \<longlonglongrightarrow> Inf {ereal(u n/n)|n. n > N0}"
    by (simp add: assms(1) subadditive_converges_ereal')
  define V where "V = {u n/n | n. n>N0}"
  then have "\<not> bdd_below V" using assms by simp
  have "Inf {ereal(t) | t. t\<in>V} = -\<infinity>"
    by (rule ereal_bot, metis (mono_tags, lifting) \<open>\<not> bdd_below V\<close> bdd_below_def
        leI Inf_lower2 ereal_less_eq(3) le_less mem_Collect_eq)
  moreover have "{ereal(t)| t. t\<in>V} = {ereal(u n/n)|n. n > N0}" using V_def by blast
  ultimately have "Inf {ereal(u n/n)|n. n > N0} = -\<infinity>" by auto
  then show ?thesis using * by simp
qed

lemma subadditive_converges_unbounded:
  assumes "subadditive u"
          "\<not> (bdd_below {u n/n | n. n>0})"
  shows "(\<lambda>n. ereal(u n/n)) \<longlonglongrightarrow> -\<infinity>"
by (rule subadditive_converges_unbounded'[OF subadditive_imp_eventually_subadditive[OF assms(1)] assms(2)])

subsection \<open>Superadditive sequences\<close>

text \<open>While most applications involve subadditive sequences, one sometimes encounters superadditive
sequences. We reformulate quickly some of the above results in this setting.\<close>

definition superadditive::"(nat\<Rightarrow>real) \<Rightarrow> bool"
  where "superadditive u = (\<forall>m n. u (m+n) \<ge> u m + u n)"

lemma subadditive_of_superadditive:
  assumes "superadditive u"
  shows "subadditive (\<lambda>n. -u n)"
using assms unfolding superadditive_def subadditive_def by (auto simp add: algebra_simps)

lemma superadditive_un_ge_nu1:
  assumes "superadditive u"
          "n > 0"
  shows "u n \<ge> n * u 1"
using subadditive_un_le_nu1[OF subadditive_of_superadditive[OF assms(1)] assms(2)] by auto

lemma superadditive_converges_bounded'':
  assumes "superadditive u"
          "\<And>n. n > 0 \<Longrightarrow> u n \<le> n * (a::real)"
  shows "\<exists>l. (\<lambda>n. u n / n) \<longlonglongrightarrow> l \<and> (\<forall>n>0. u n \<le> n * l)"
proof -
  have "\<exists>l. (\<lambda>n. -u n / n) \<longlonglongrightarrow> l \<and> (\<forall>n>0. -u n \<ge> n * l)"
    apply (rule subadditive_converges_bounded''[OF subadditive_of_superadditive[OF assms(1)], of "-a"])
    using assms(2) by auto
  then obtain l where l: "(\<lambda>n. -u n / n) \<longlonglongrightarrow> l" "(\<forall>n>0. -u n \<ge> n * l)" by blast
  have "(\<lambda>n. -((-u n)/n)) \<longlonglongrightarrow> -l"
    by (intro tendsto_intros l)
  moreover have "\<forall>n>0. u n \<le> n * (-l)"
    using l(2) by (auto simp add: algebra_simps) (metis minus_equation_iff neg_le_iff_le)
  ultimately show ?thesis
    by auto
qed


subsection \<open>Almost additive sequences\<close>

text \<open>One often encounters sequences which are both subadditive and superadditive, but only up
to an additive constant. Adding or subtracting this constant, one can make the sequence
genuinely subadditive or superadditive, and thus deduce results about its convergence, as follows.
Such sequences appear notably when dealing with quasimorphisms.\<close>

lemma almost_additive_converges:
  fixes u::"nat \<Rightarrow> real"
  assumes "\<And>m n. abs(u(m+n) - u m - u n) \<le> C"
  shows "convergent (\<lambda>n. u n/n)"
        "abs(u k - k * lim (\<lambda>n. u n / n)) \<le> C"
proof -
  have "(abs (u 0)) \<le> C" using assms[of 0 0] by auto
  then have "C \<ge> 0" by auto

  define v where "v = (\<lambda>n. u n + C)"
  have "subadditive v"
    unfolding subadditive_def v_def using assms by (auto simp add: algebra_simps abs_diff_le_iff)
  then have vle: "v n \<le> n * v 1" if "n > 0" for n
    using subadditive_un_le_nu1 that by auto
  define w where "w = (\<lambda>n. u n - C)"
  have "superadditive w"
    unfolding superadditive_def w_def using assms by (auto simp add: algebra_simps abs_diff_le_iff)
  then have wge: "w n \<ge> n * w 1" if "n > 0" for n
    using superadditive_un_ge_nu1 that by auto

  have I: "v n \<ge> w n" for n
    unfolding v_def w_def using \<open>C \<ge> 0\<close> by auto
  then have *: "v n \<ge> n * w 1" if "n > 0" for n using order_trans[OF wge[OF that]] by auto
  then obtain lv where lv: "(\<lambda>n. v n/n) \<longlonglongrightarrow> lv" "\<And>n. n > 0 \<Longrightarrow> v n \<ge> n * lv"
    using subadditive_converges_bounded''[OF \<open>subadditive v\<close> *] by auto
  have *: "w n \<le> n * v 1" if "n > 0" for n using order_trans[OF _ vle[OF that]] I by auto
  then obtain lw where lw: "(\<lambda>n. w n/n) \<longlonglongrightarrow> lw" "\<And>n. n > 0 \<Longrightarrow> w n \<le> n * lw"
    using superadditive_converges_bounded''[OF \<open>superadditive w\<close> *] by auto

  have *: "v n/n = w n /n + 2*C*(1/n)" for n
    unfolding v_def w_def by (auto simp add: algebra_simps divide_simps)
  have "(\<lambda>n. w n /n + 2*C*(1/n)) \<longlonglongrightarrow> lw + 2*C*0"
    by (intro tendsto_add tendsto_mult lim_1_over_n lw, auto)
  then have "lw = lv"
    unfolding *[symmetric] using lv(1) LIMSEQ_unique by auto

  have *: "u n/n = w n /n + C*(1/n)" for n
    unfolding w_def by (auto simp add: algebra_simps divide_simps)
  have "(\<lambda>n. u n /n) \<longlonglongrightarrow> lw + C*0"
    unfolding * by (intro tendsto_add tendsto_mult lim_1_over_n lw, auto)
  then have lu: "convergent (\<lambda>n. u n/n)" "lim (\<lambda>n. u n/n) = lw"
    by (auto simp add: convergentI limI)
  then show "convergent (\<lambda>n. u n/n)" by simp

  show "abs(u k - k * lim (\<lambda>n. u n / n)) \<le> C"
  proof (cases "k>0")
    case False
    then show ?thesis using assms[of 0 0] by auto
  next
    case True
    have "u k - k * lim (\<lambda>n. u n/n) = v k - C - k * lv" unfolding lu(2) \<open>lw = lv\<close> v_def by auto
    also have "... \<ge> -C" using lv(2)[OF True] by auto
    finally have A: "u k - k * lim (\<lambda>n. u n/n) \<ge> - C" by simp
    have "u k - k * lim (\<lambda>n. u n/n) = w k + C - k * lw" unfolding lu(2) w_def by auto
    also have "... \<le> C" using lw(2)[OF True] by auto
    finally show ?thesis using A by auto
  qed
qed


subsection \<open>Submultiplicative sequences, application to the spectral radius\<close>

text \<open>In the same way as subadditive sequences, one may define submultiplicative sequences.
Essentially, a sequence is submultiplicative if its logarithm is subadditive. A difference is
that we allow a submultiplicative sequence to take the value $0$, as this shows up in applications.
This implies that we have to distinguish in the proofs the situations where the value $0$
is taken or not. In the latter situation, we can use directly the results from the
subadditive case to deduce convergence. In the former situation, convergence to $0$ is obvious
as the sequence vanishes eventually.\<close>

lemma submultiplicative_converges:
  fixes u::"nat\<Rightarrow>real"
  assumes "\<And>n. u n \<ge> 0"
          "\<And>m n. u (m+n) \<le> u m * u n"
  shows "(\<lambda>n. root n (u n))\<longlonglongrightarrow> Inf {root n (u n) | n. n>0}"
proof -
  define v where "v = (\<lambda> n. root n (u n))"
  define V where "V = {v n | n. n>0}"
  then have "V \<noteq> {}" by blast
  have "t \<ge> 0" if "t \<in> V" for t using that V_def v_def assms(1) by auto
  then have "Inf V \<ge> 0" by (simp add: \<open>V \<noteq> {}\<close> cInf_greatest)
  have "bdd_below V" by (meson \<open>\<And>t. t \<in> V \<Longrightarrow> 0 \<le> t\<close> bdd_below_def)

  show ?thesis
  proof cases
    assume "\<exists>n. u n = 0"
    then obtain n where "u n = 0" by auto
    then have "u m = 0" if "m \<ge> n" for m by (metis that antisym_conv assms(1) assms(2) le_Suc_ex mult_zero_left)
    then have *: "v m = 0" if "m \<ge> n" for m using v_def that by simp
    then have "v \<longlonglongrightarrow> 0" using tendsto_explicit by force

    have "v (Suc n) \<in> V" using V_def by blast
    moreover have "v (Suc n) = 0" using * by auto
    ultimately have "Inf V \<le> 0" by (simp add: \<open>bdd_below V\<close> cInf_lower)
    then have "Inf V = 0" using \<open>0 \<le> Inf V\<close> by auto
    then show ?thesis using V_def v_def \<open>v \<longlonglongrightarrow> 0\<close> by auto
  next
    assume "\<not> (\<exists>n. u n = 0)"
    then have "u n > 0" for n by (metis assms(1) less_eq_real_def)
    define w where "w n = ln (u n)" for n
    have express_vn: "v n = exp(w n/n)" if "n>0" for n
    proof -
      have "(exp(w n/n))^n = exp(n*(w n/n))" by (metis exp_of_nat_mult)
      also have "... = exp(w n)" by (simp add: \<open>0 < n\<close>)
      also have "... = u n" by (simp add: \<open>\<And>n. 0 < u n\<close> w_def)
      finally have "exp(w n/n) = root n (u n)" by (metis \<open>0 < n\<close> exp_ge_zero real_root_power_cancel)
      then show ?thesis unfolding v_def by simp
    qed

    have "eventually_subadditive w 0"
    proof (rule eventually_subadditiveI)
      fix m n
      have "w (m+n) = ln (u (m+n))" by (simp add: w_def)
      also have "... \<le> ln(u m * u n)"
        by (meson \<open>\<And>n. 0 < u n\<close> assms(2) zero_less_mult_iff ln_le_cancel_iff)
      also have "... = ln(u m) + ln(u n)" by (simp add: \<open>\<And>n. 0 < u n\<close> ln_mult)
      also have "... = w m + w n" by (simp add: w_def)
      finally show "w (m+n) \<le> w m + w n".
    qed

    define l where "l = Inf V"
    then have "v n\<ge>l" if "n > 0" for n
      using V_def that by (metis (mono_tags, lifting) \<open>bdd_below V\<close> cInf_lower mem_Collect_eq)
    then have lower: "eventually (\<lambda>n. a < v n) sequentially" if "a < l" for a
      by (meson that dual_order.strict_trans1 eventually_at_top_dense)

    have upper: "eventually (\<lambda>n. a > v n) sequentially" if "a > l" for a
    proof -
      obtain t where "t\<in>V" "t < a" using \<open>V \<noteq> {}\<close> cInf_lessD l_def \<open>a>l\<close> by blast
      then have "t > 0" using V_def \<open>\<And>n. 0 < u n\<close> v_def by auto
      then have "a/t > 1" using \<open>t<a\<close> by simp
      define e where "e = ln(a/t)/2"
      have "e > 0" "e < ln(a/t)" unfolding e_def by (simp_all add: \<open>1 < a / t\<close> ln_gt_zero)
      then have "exp(e) < a/t" by (metis \<open>1 < a / t\<close> exp_less_cancel_iff exp_ln less_trans zero_less_one)

      obtain n where "n>0" "t = v n" using V_def v_def \<open>t \<in> V\<close> by blast
      then have "v n * exp(e) < a" using \<open>exp(e) < a/t\<close> by (metis \<open>0 < t\<close> linordered_field_class.sign_simps(24) pos_less_divide_eq)

      obtain N where *: "N>0" "\<And>m. m\<ge>N \<Longrightarrow> w m/m < w n/n + e"
        using eventually_subadditive_ineq[OF \<open>eventually_subadditive w 0\<close>] \<open>0 < n\<close> \<open>e>0\<close> by blast
      have "v m < a" if "m \<ge> N" for m
      proof -
        have "m>0" using that \<open>N>0\<close> by simp
        have "w m/m < w n/n + e" by (simp add: \<open>N \<le> m\<close> *)
        then have "exp(w m/m) < exp(w n/n + e)" by simp
        also have "... = exp(w n/n) * exp(e)" by (simp add: mult_exp_exp)
        finally have "v m < v n * exp(e)" using express_vn \<open>m>0\<close> \<open>n>0\<close> by simp
        then show "v m < a" using \<open>v n * exp(e) < a\<close> by simp
      qed
      then show ?thesis using eventually_at_top_linorder by auto
    qed

    show ?thesis
      using lower upper unfolding v_def l_def V_def by (simp add: order_tendsto_iff)
  qed
qed

text \<open>An important application of submultiplicativity is to prove the existence of the
spectral radius of a matrix, as the limit of $\|A^n\|^{1/n}$.\<close>

definition spectral_radius::"'a::real_normed_algebra_1 \<Rightarrow> real"
  where "spectral_radius x = Inf {root n (norm(x^n))| n. n>0}"

lemma spectral_radius_aux:
  fixes x::"'a::real_normed_algebra_1"
  defines "V \<equiv> {root n (norm(x^n))| n. n>0}"
  shows "\<And>t. t\<in>V \<Longrightarrow> t \<ge> spectral_radius x"
        "\<And>t. t\<in>V \<Longrightarrow> t \<ge> 0"
        "bdd_below V"
        "V \<noteq> {}"
        "Inf V \<ge> 0"
proof -
  show "V\<noteq>{}" using V_def by blast
  show *: "t \<ge> 0" if "t \<in> V" for t using that unfolding V_def using real_root_pos_pos_le by auto
  then show "bdd_below V" by (meson bdd_below_def)
  then show "Inf V \<ge> 0" by (simp add: \<open>V \<noteq> {}\<close> * cInf_greatest)
  show "\<And>t. t\<in>V \<Longrightarrow> t \<ge> spectral_radius x" by (metis (mono_tags, lifting) \<open>bdd_below V\<close> assms cInf_lower spectral_radius_def)
qed

lemma spectral_radius_nonneg [simp]:
  "spectral_radius x \<ge> 0"
by (simp add: spectral_radius_aux(5) spectral_radius_def)

lemma spectral_radius_upper_bound [simp]:
  "(spectral_radius x)^n \<le> norm(x^n)"
proof (cases)
  assume "\<not>(n = 0)"
  have "root n (norm(x^n)) \<ge> spectral_radius x"
    using spectral_radius_aux \<open>n \<noteq> 0\<close> by auto
  then show ?thesis
    by (metis \<open>n \<noteq> 0\<close> spectral_radius_nonneg norm_ge_zero not_gr0 power_mono real_root_pow_pos2)
qed (simp)

lemma spectral_radius_limit:
  "(\<lambda>n. root n (norm(x^n))) \<longlonglongrightarrow> spectral_radius x"
proof -
  have "norm(x^(m+n)) \<le> norm(x^m) * norm(x^n)" for m n by (simp add: power_add norm_mult_ineq)
  then show ?thesis unfolding spectral_radius_def using submultiplicative_converges by auto
qed

end (*of Fekete.thy*)
