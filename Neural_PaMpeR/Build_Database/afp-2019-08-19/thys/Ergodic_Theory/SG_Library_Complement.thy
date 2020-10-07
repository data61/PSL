(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>SG Libary complements\<close>

theory SG_Library_Complement
  imports "HOL-Probability.Probability"
begin

text \<open>In this file are included many statements that were useful to me, but belong rather
naturally to existing theories. In a perfect world, some of these statements would get included
into these files.

I tried to indicate to which of these classical theories the statements could be added.
\<close>

subsection \<open>Basic logic\<close>

text \<open>This one is certainly available, but I could not locate it...\<close>
lemma equiv_neg:
  "\<lbrakk> P \<Longrightarrow> Q; \<not>P \<Longrightarrow> \<not>Q \<rbrakk> \<Longrightarrow> (P\<longleftrightarrow>Q)"
by blast


subsection \<open>Basic set theory\<close>

lemma compl_compl_eq_id [simp]:
  "UNIV - (UNIV - s) = s"
by auto

abbreviation sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<Delta>" 70) where
  "sym_diff A B \<equiv> ((A - B) \<union> (B-A))"

text \<open>Not sure the next lemmas are useful, as they are proved solely by auto, so they
could be reproved automatically whenever necessary.\<close>

lemma sym_diff_inc:
  "A \<Delta> C \<subseteq> A \<Delta> B \<union> B \<Delta> C"
by auto

lemma sym_diff_vimage [simp]:
  "f-`(A \<Delta> B) = (f-`A) \<Delta> (f-`B)"
by auto

lemma card_finite_union:
  assumes "finite I"
  shows "card(\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. card(A i))"
using assms apply (induct, auto)
using card_Un_le nat_add_left_cancel_le order_trans by blast


subsection \<open>Set-Interval.thy\<close>

text \<open>The next two lemmas belong naturally to \verb+Set_Interval.thy+, next to
\verb+UN_le_add_shift+. They are not trivially equivalent to the corresponding lemmas
with large inequalities, due to the difference when $n = 0$.\<close>

lemma UN_le_add_shift_strict:
  "(\<Union>i<n::nat. M(i+k)) = (\<Union>i\<in>{k..<n+k}. M i)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain i where i: "i \<in> {k..<n+k}" "x \<in> M(i)" by auto
    then have "i - k < n \<and> x \<in> M((i-k) + k)" by auto
    then show "x \<in> ?A" using UN_le_add_shift by blast
  qed
qed (fastforce)

lemma UN_le_eq_Un0_strict:
  "(\<Union>i<n+1::nat. M i) = (\<Union>i\<in>{1..<n+1}. M i) \<union> M 0" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain i where i: "i<n+1" "x \<in> M i" by auto
    show "x \<in> ?B"
    proof(cases i)
      case 0 with i show ?thesis by simp
    next
      case (Suc j) with i show ?thesis by auto
    qed
  qed
qed (auto)

text \<open>I use repeatedly this one, but I could not find it directly\<close>

lemma union_insert_0:
  "(\<Union>n::nat. A n) = A 0 \<union> (\<Union>n\<in>{1..}. A n)"
by (metis UN_insert Un_insert_left sup_bot.left_neutral One_nat_def atLeast_0 atLeast_Suc_greaterThan ivl_disj_un_singleton(1))

text \<open>Next one could be close to \verb+sum.nat_group+\<close>

lemma sum_arith_progression:
  "(\<Sum>r<(N::nat). (\<Sum>i<a. f (i*N+r))) = (\<Sum>j<a*N. f j)"
proof -
  have *: "(\<Sum>r<N. f (i*N+r)) = (\<Sum> j \<in> {i*N..<i*N + N}. f j)" for i
    by (rule sum.reindex_bij_betw, rule bij_betw_byWitness[where ?f' = "\<lambda>r. r-i*N"], auto)

  have "(\<Sum>r<N. (\<Sum>i<a. f (i*N+r))) = (\<Sum>i<a. (\<Sum>r<N. f (i*N+r)))"
    using sum.swap by auto
  also have "... = (\<Sum>i<a. (\<Sum> j \<in> {i*N..<i*N + N}. f j))"
    using * by auto
  also have "... = (\<Sum>j<a*N. f j)"
    by (rule sum.nat_group)
  finally show ?thesis by simp
qed


subsection \<open>Miscellanous basic results\<close>

lemma ind_from_1 [case_names 1 Suc, consumes 1]:
  assumes "n > 0"
  assumes "P 1"
      and "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof -
  have "(n = 0) \<or> P n"
  proof (induction n)
    case 0 then show ?case by auto
  next
    case (Suc k)
    consider "Suc k = 1" | "Suc k > 1" by linarith
    then show ?case
      apply (cases) using assms Suc.IH by auto
  qed
  then show ?thesis using \<open>n > 0\<close> by auto
qed

text \<open>This lemma is certainly available somewhere, but I couldn't
locate it\<close>

lemma tends_to_real_e:
  fixes u::"nat \<Rightarrow> real"
  assumes "u \<longlonglongrightarrow> l"
          "e>0"
  shows "\<exists>N. \<forall>n>N. abs(u n -l) < e"
proof-
  have "eventually (\<lambda>n. dist (u n) l < e) sequentially" using assms tendstoD by auto
  then have "\<forall>\<^sub>F n in sequentially. abs(u n - l) < e" using dist_real_def by auto
  then show ?thesis by (simp add: eventually_at_top_dense)
qed

lemma nat_mod_cong:
  assumes "a = b+(c::nat)"
          "a mod n = b mod n"
  shows "c mod n = 0"
proof -
  let ?k = "a mod n"
  obtain a1 where "a = a1*n + ?k" by (metis div_mult_mod_eq)
  moreover obtain b1 where "b = b1*n + ?k" using assms(2) by (metis div_mult_mod_eq)
  ultimately have "a1 * n + ?k = b1 * n + ?k + c" using assms(1) by arith
  then have "c = (a1 - b1) * n" by (simp add: diff_mult_distrib)
  then show ?thesis by simp
qed

lemma funpow_add': "(f ^^ (m + n)) x = (f ^^ m) ((f ^^ n) x)"
by (simp add: funpow_add)

text \<open>The next two lemmas are not directly equivalent, since $f$ might
not be injective.\<close>

lemma abs_Max_sum:
  fixes A::"real set"
  assumes "finite A" "A \<noteq> {}"
  shows "abs(Max A) \<le> (\<Sum>a\<in>A. abs(a))"
using assms by (induct rule: finite_ne_induct, auto)

lemma abs_Max_sum2:
  fixes f::"_ \<Rightarrow> real"
  assumes "finite A" "A \<noteq> {}"
  shows "abs(Max (f`A)) \<le> (\<Sum>a\<in>A. abs(f a))"
using assms by (induct rule: finite_ne_induct, auto)

subsection \<open>Conditionally-Complete-Lattices.thy\<close>

lemma mono_cInf:
  fixes f :: "'a::conditionally_complete_lattice \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes "mono f" "A \<noteq> {}" "bdd_below A"
  shows "f(Inf A) \<le> Inf (f`A)"
using assms by (simp add: cINF_greatest cInf_lower monoD)

lemma mono_bij_cInf:
  fixes f :: "'a::conditionally_complete_linorder \<Rightarrow> 'b::conditionally_complete_linorder"
  assumes "mono f" "bij f" "A \<noteq> {}" "bdd_below A"
  shows "f (Inf A) = Inf (f`A)"
proof -
  have "(inv f) (Inf (f`A)) \<le> Inf ((inv f)`(f`A))"
    apply (rule cInf_greatest, auto simp add: assms(3))
    using mono_inv[OF assms(1) assms(2)] assms by (simp add: mono_def bdd_below_image_mono cInf_lower)
  then have "Inf (f`A) \<le> f (Inf ((inv f)`(f`A)))"
    by (metis (no_types, lifting) assms(1) assms(2) mono_def bij_inv_eq_iff)
  also have "... = f(Inf A)"
    using assms by (simp add: bij_is_inj)
  finally show ?thesis using mono_cInf[OF assms(1) assms(3) assms(4)] by auto
qed

subsection \<open>Topological-spaces.thy\<close>

lemma open_less_abs [simp]:
  "open {x. (C::real) < abs x}"
proof -
  have *: "{x. C < abs x} = abs-`{C<..}" by auto
  show ?thesis unfolding * by (auto intro!: continuous_intros)
qed

lemma closed_le_abs [simp]:
  "closed {x. (C::real) \<le> abs x}"
proof -
  have *: "{x. C \<le> \<bar>x\<bar>} = abs-`{C..}" by auto
  show ?thesis unfolding * by (auto intro!: continuous_intros)
qed

text \<open>The next statements come from the same statements for true subsequences\<close>

lemma eventually_weak_subseq:
  fixes u::"nat \<Rightarrow> nat"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "eventually P sequentially"
  shows "eventually (\<lambda>n. P (u n)) sequentially"
proof -
  obtain N where *: "\<forall>n\<ge>N. P n" using assms(2) unfolding eventually_sequentially by auto
  obtain M where "\<forall>m\<ge>M. ereal(u m) \<ge> N" using assms(1) by (meson Lim_PInfty)
  then have "\<And>m. m \<ge> M \<Longrightarrow> u m \<ge> N" by auto
  then have "\<And>m. m \<ge> M \<Longrightarrow> P(u m)" using \<open>\<forall>n\<ge>N. P n\<close> by simp
  then show ?thesis unfolding eventually_sequentially by auto
qed

lemma filterlim_weak_subseq:
  fixes u::"nat \<Rightarrow> nat"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>"
  shows "LIM n sequentially. u n:> at_top"
unfolding filterlim_iff by (metis assms eventually_weak_subseq)

lemma limit_along_weak_subseq:
  fixes u::"nat \<Rightarrow> nat" and v::"nat \<Rightarrow> _"
  assumes "(\<lambda>n. real(u n)) \<longlonglongrightarrow> \<infinity>" "v \<longlonglongrightarrow> l"
  shows "(\<lambda> n. v(u n)) \<longlonglongrightarrow> l"
using filterlim_compose[of v, OF _ filterlim_weak_subseq] assms by auto

lemma frontier_indist_le:
  assumes "x \<in> frontier {y. infdist y S \<le> r}"
  shows "infdist x S = r"
proof -
  have "infdist x S = r" if H: "\<forall>e>0. (\<exists>y. infdist y S \<le> r \<and> dist x y < e) \<and> (\<exists>z. \<not> infdist z S \<le> r \<and> dist x z < e)"
  proof -
    have "infdist x S < r + e" if "e > 0" for e
    proof -
      obtain y where "infdist y S \<le> r" "dist x y < e"
        using H \<open>e > 0\<close> by blast
      then show ?thesis
        by (metis add.commute add_mono_thms_linordered_field(3) infdist_triangle le_less_trans)
    qed
    then have A: "infdist x S \<le> r"
      by (meson field_le_epsilon order.order_iff_strict)
    have "r < infdist x S + e" if "e > 0" for e
    proof -
      obtain y where "\<not>(infdist y S \<le> r)" "dist x y < e"
        using H \<open>e > 0\<close> by blast
      then have "r < infdist y S" by auto
      also have "... \<le> infdist x S + dist y x"
        by (rule infdist_triangle)
      finally show ?thesis using \<open>dist x y < e\<close>
        by (simp add: dist_commute)
      qed
    then have B: "r \<le> infdist x S"
      by (meson field_le_epsilon order.order_iff_strict)
    show ?thesis using A B by auto
  qed
  then show ?thesis
    using assms unfolding frontier_straddle by auto
qed


subsection \<open>Connected.thy\<close>

text \<open>The next lemma is missing in the library, contrary to its cousin \verb+continuous_infdist+.\<close>

lemma continuous_on_infdist [continuous_intros]:
  assumes "continuous_on S f"
  shows "continuous_on S (\<lambda>x. infdist (f x) A)"
using assms unfolding continuous_on by (auto intro: tendsto_infdist)


subsection \<open>Transcendental.thy\<close>

text \<open>In \verb+Transcendental.thy+, the assumptions of the next two lemmas are
$x > 0$ and $y > 0$, while large inequalities are sufficient, with the same proof.\<close>

lemma powr_divide: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x / y) powr a = (x powr a) / (y powr a)"
  for a b x :: real
  apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
  apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
  done

lemma powr_mult_base: "0 \<le> x \<Longrightarrow>x * x powr y = x powr (1 + y)"
  for x :: real
  by (auto simp: powr_add)



subsection \<open>Limits\<close>

text \<open>\verb+lim_1_over_n+ is very useful, it could --should?-- be declared as simp and tendsto-intros.\<close>

declare lim_1_over_n [tendsto_intros]

text \<open>The next lemmas are not very natural, but I needed them several times\<close>

lemma tendsto_shift_1_over_n [tendsto_intros]:
  fixes f::"nat \<Rightarrow> real"
  assumes "(\<lambda>n. f n / n) \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (n+k) / n) \<longlonglongrightarrow> l"
proof -
  have "(1+k*(1/n))* (f(n+k)/(n+k)) = f(n+k)/n" if "n>0" for n using that by (auto simp add: divide_simps)
  with eventually_mono[OF eventually_gt_at_top[of "0::nat"] this]
  have "eventually (\<lambda>n.(1+k*(1/n))* (f(n+k)/(n+k)) = f(n+k)/n) sequentially"
    by auto
  moreover have "(\<lambda>n. (1+k*(1/n))* (f(n+k)/(n+k))) \<longlonglongrightarrow> (1+real k*0) * l"
    by (intro tendsto_intros LIMSEQ_ignore_initial_segment assms)
  ultimately show ?thesis using Lim_transform_eventually by auto
qed

lemma tendsto_shift_1_over_n' [tendsto_intros]:
  fixes f::"nat \<Rightarrow> real"
  assumes "(\<lambda>n. f n / n) \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (n-k) / n) \<longlonglongrightarrow> l"
proof -
  have "(1-k*(1/(n+k)))* (f n/ n) = f n/(n+k)" if "n>0" for n using that by (auto simp add: divide_simps)
  with eventually_mono[OF eventually_gt_at_top[of "0::nat"] this]
  have "eventually (\<lambda>n. (1-k*(1/(n+k)))* (f n/ n) = f n/(n+k)) sequentially"
    by auto
  moreover have "(\<lambda>n. (1-k*(1/(n+k)))* (f n/ n)) \<longlonglongrightarrow> (1-real k*0) * l"
    by (intro tendsto_intros assms LIMSEQ_ignore_initial_segment)
  ultimately have "(\<lambda>n. f n / (n+k)) \<longlonglongrightarrow> l" using Lim_transform_eventually by auto
  then have a: "(\<lambda>n. f(n-k)/(n-k+k)) \<longlonglongrightarrow> l" using seq_offset_neg by auto

  have "f(n-k)/(n-k+k) = f(n-k)/n" if "n>k" for n
    using that by auto
  with eventually_mono[OF eventually_gt_at_top[of k] this]
  have "eventually (\<lambda>n. f(n-k)/(n-k+k) = f(n-k)/n) sequentially"
    by auto
  with Lim_transform_eventually[OF this a]
  show ?thesis by auto
qed

declare LIMSEQ_realpow_zero [tendsto_intros]

subsection \<open>Topology-Euclidean-Space\<close>

lemma Inf_as_limit:
  fixes A::"'a::{linorder_topology, first_countable_topology, complete_linorder} set"
  assumes "A \<noteq> {}"
  shows "\<exists>u. (\<forall>n. u n \<in> A) \<and> u \<longlonglongrightarrow> Inf A"
proof (cases "Inf A \<in> A")
  case True
  show ?thesis
    by (rule exI[of _ "\<lambda>n. Inf A"], auto simp add: True)
next
  case False
  obtain y where "y \<in> A" using assms by auto
  then have "Inf A < y" using False Inf_lower less_le by auto
  obtain F :: "nat \<Rightarrow> 'a set" where F: "\<And>i. open (F i)" "\<And>i. Inf A \<in> F i"
                                       "\<And>u. (\<forall>n. u n \<in> F n) \<Longrightarrow> u \<longlonglongrightarrow> Inf A"
    by (metis first_countable_topology_class.countable_basis)
  define u where "u = (\<lambda>n. SOME z. z \<in> F n \<and> z \<in> A)"
  have "\<exists>z. z \<in> U \<and> z \<in> A" if "Inf A \<in> U" "open U" for U
  proof -
    obtain b where "b > Inf A" "{Inf A ..<b} \<subseteq> U"
      using open_right[OF \<open>open U\<close> \<open>Inf A \<in> U\<close> \<open>Inf A < y\<close>] by auto
    obtain z where "z < b" "z \<in> A"
      using \<open>Inf A < b\<close> Inf_less_iff by auto
    then have "z \<in> {Inf A ..<b}"
      by (simp add: Inf_lower)
    then show ?thesis using \<open>z \<in> A\<close> \<open>{Inf A ..<b} \<subseteq> U\<close> by auto
  qed
  then have *: "u n \<in> F n \<and> u n \<in> A" for n
    using \<open>Inf A \<in> F n\<close> \<open>open (F n)\<close> unfolding u_def by (metis (no_types, lifting) someI_ex)
  then have "u \<longlonglongrightarrow> Inf A" using F(3) by simp
  then show ?thesis using * by auto
qed

text \<open>A (more usable) variation around \verb+continuous_on_closure_sequentially+. The assumption
that the spaces are metric spaces is definitely too strong, but sufficient for most applications.\<close>

lemma continuous_on_closure_sequentially':
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on (closure C) f"
          "\<And>(n::nat). u n \<in> C"
          "u \<longlonglongrightarrow> l"
  shows "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f l"
proof -
  have "l \<in> closure C" unfolding closure_sequential using assms by auto
  then show ?thesis
    using \<open>continuous_on (closure C) f\<close> unfolding comp_def continuous_on_closure_sequentially
    using assms by auto
qed


subsection \<open>Convexity\<close>

lemma convex_on_mean_ineq:
  fixes f::"real \<Rightarrow> real"
  assumes "convex_on A f" "x \<in> A" "y \<in> A"
  shows "f ((x+y)/2) \<le> (f x + f y) / 2"
using convex_onD[OF assms(1), of "1/2" x y] using assms by (auto simp add: divide_simps)

lemma convex_on_closure:
  assumes "convex (C::'a::real_normed_vector set)"
          "convex_on C f"
          "continuous_on (closure C) f"
  shows "convex_on (closure C) f"
proof (rule convex_onI)
  fix x y::'a and t::real
  assume "x \<in> closure C" "y \<in> closure C" "0 < t" "t < 1"
  obtain u v::"nat \<Rightarrow> 'a" where *: "\<And>n. u n \<in> C" "u \<longlonglongrightarrow> x"
                                   "\<And>n. v n \<in> C" "v \<longlonglongrightarrow> y"
    using \<open>x \<in> closure C\<close> \<open>y \<in> closure C\<close> unfolding closure_sequential by blast
  define w where "w = (\<lambda>n. (1-t) *\<^sub>R (u n) + t *\<^sub>R (v n))"
  have "w n \<in> C" for n
    using \<open>0 < t\<close> \<open>t< 1\<close> convexD[OF \<open>convex C\<close> *(1)[of n] *(3)[of n]] unfolding w_def by auto
  have "w \<longlonglongrightarrow> ((1-t) *\<^sub>R x + t *\<^sub>R y)"
    unfolding w_def using *(2) *(4) by (intro tendsto_intros)

  have *: "f(w n) \<le> (1-t) * f(u n) + t * f (v n)" for n
    using *(1) *(3) \<open>convex_on C f\<close> \<open>0<t\<close> \<open>t<1\<close> less_imp_le unfolding w_def
    convex_on_alt[OF assms(1)] by (simp add: add.commute)
  have i: "(\<lambda>n. f (w n)) \<longlonglongrightarrow> f ((1-t) *\<^sub>R x + t *\<^sub>R y)"
    by (rule continuous_on_closure_sequentially'[OF assms(3) \<open>\<And>n. w n \<in> C\<close> \<open>w \<longlonglongrightarrow> ((1-t) *\<^sub>R x + t *\<^sub>R y)\<close>])
  have ii: "(\<lambda>n. (1-t) * f(u n) + t * f (v n)) \<longlonglongrightarrow> (1-t) * f x + t * f y"
    apply (intro tendsto_intros)
    apply (rule continuous_on_closure_sequentially'[OF assms(3) \<open>\<And>n. u n \<in> C\<close> \<open>u \<longlonglongrightarrow> x\<close>])
    apply (rule continuous_on_closure_sequentially'[OF assms(3) \<open>\<And>n. v n \<in> C\<close> \<open>v \<longlonglongrightarrow> y\<close>])
    done
  show "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    apply (rule LIMSEQ_le[OF i ii]) using * by auto
qed

lemma convex_on_norm [simp]:
  "convex_on UNIV (\<lambda>(x::'a::real_normed_vector). norm x)"
using convex_on_dist[of UNIV "0::'a"] by auto

lemma continuous_abs_powr [continuous_intros]:
  assumes "p > 0"
  shows "continuous_on UNIV (\<lambda>(x::real). \<bar>x\<bar> powr p)"
apply (rule continuous_on_powr') using assms by (auto intro: continuous_intros)

lemma continuous_mult_sgn [continuous_intros]:
  fixes f::"real \<Rightarrow> real"
  assumes "continuous_on UNIV f" "f 0 = 0"
  shows "continuous_on UNIV (\<lambda>x. sgn x * f x)"
proof -
  have *: "continuous_on {0..} (\<lambda>x. sgn x * f x)"
    apply (subst continuous_on_cong[of "{0..}" "{0..}" _ f], auto simp add: sgn_real_def assms(2))
    by (rule continuous_on_subset[OF assms(1)], auto)
  have **: "continuous_on {..0} (\<lambda>x. sgn x * f x)"
    apply (subst continuous_on_cong[of "{..0}" "{..0}" _ "\<lambda>x. -f x"], auto simp add: sgn_real_def assms(2))
    by (rule continuous_on_subset[of UNIV], auto simp add: assms intro!: continuous_intros)
  show ?thesis
    using continuous_on_closed_Un[OF _ _ * **] apply (auto intro: continuous_intros)
    using continuous_on_subset by fastforce
qed

lemma DERIV_abs_powr [derivative_intros]:
  assumes "p > (1::real)"
  shows "DERIV (\<lambda>x. \<bar>x\<bar> powr p) x :> p * sgn x * \<bar>x\<bar> powr (p - 1)"
proof -
  consider "x = 0" | "x>0" | "x < 0" by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "continuous_on UNIV (\<lambda>x. sgn x * \<bar>x\<bar> powr (p - 1))"
      by (auto simp add: assms intro!:continuous_intros)
    then have "(\<lambda>h. sgn h * \<bar>h\<bar> powr (p-1)) \<midarrow>0\<rightarrow> (\<lambda>h. sgn h * \<bar>h\<bar> powr (p-1)) 0"
      using continuous_on_def by blast
    moreover have "\<bar>h\<bar> powr p / h = sgn h * \<bar>h\<bar> powr (p-1)" for h
    proof -
      have "\<bar>h\<bar> powr p / h = sgn h * \<bar>h\<bar> powr p / \<bar>h\<bar>"
        by (auto simp add: algebra_simps divide_simps sgn_real_def)
      also have "... = sgn h * \<bar>h\<bar> powr (p-1)"
        using assms apply (cases "h = 0") apply (auto)
        by (metis abs_ge_zero powr_diff [symmetric] powr_one_gt_zero_iff times_divide_eq_right)
      finally show ?thesis by simp
    qed
    ultimately have "(\<lambda>h. \<bar>h\<bar> powr p / h) \<midarrow>0\<rightarrow> 0" by auto
    then show ?thesis unfolding DERIV_def by (auto simp add: \<open>x = 0\<close>)
  next
    case 2
    have *: "\<forall>\<^sub>F y in nhds x. \<bar>y\<bar> powr p = y powr p"
      unfolding eventually_nhds apply (rule exI[of _ "{0<..}"]) using \<open>x > 0\<close> by auto
    show ?thesis
      apply (subst DERIV_cong_ev[of _ x _ "(\<lambda>x. x powr p)" _ "p * x powr (p-1)"])
      using \<open>x > 0\<close> by (auto simp add: * has_real_derivative_powr)
  next
    case 3
    have *: "\<forall>\<^sub>F y in nhds x. \<bar>y\<bar> powr p = (-y) powr p"
      unfolding eventually_nhds apply (rule exI[of _ "{..<0}"]) using \<open>x < 0\<close> by auto
    show ?thesis
      apply (subst DERIV_cong_ev[of _ x _ "(\<lambda>x. (-x) powr p)" _ "p * (- x) powr (p - real 1) * - 1"])
      using \<open>x < 0\<close> apply (simp, simp add: *, simp)
      apply (rule DERIV_fun_powr[of "\<lambda>y. -y" "-1" "x" p]) using \<open>x < 0\<close> by (auto simp add: derivative_intros)
  qed
qed

lemma convex_abs_powr:
  assumes "p \<ge> 1"
  shows "convex_on UNIV (\<lambda>x::real. \<bar>x\<bar> powr p)"
proof (cases "p = 1")
  case True
  have "convex_on UNIV (\<lambda>x::real. norm x)"
    by (rule convex_on_norm)
  moreover have "\<bar>x\<bar> powr p = norm x" for x using True by auto
  ultimately show ?thesis by simp
next
  case False
  then have "p > 1" using assms by auto
  define g where "g = (\<lambda>x::real. p * sgn x * \<bar>x\<bar> powr (p - 1))"
  have *: "DERIV (\<lambda>x. \<bar>x\<bar> powr p) x :> g x" for x
    unfolding g_def using \<open>p>1\<close> by (intro derivative_intros)
  have **: "g x \<le> g y" if "x \<le> y" for x y
  proof -
    consider "x \<ge> 0 \<and> y \<ge> 0" | "x \<le> 0 \<and> y \<le> 0" | "x < 0 \<and> y > 0" using \<open>x \<le> y\<close> by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis unfolding g_def sgn_real_def using \<open>p>1\<close> \<open>x \<le> y\<close> by (auto simp add: powr_mono2)
    next
      case 2
      then show ?thesis unfolding g_def sgn_real_def using \<open>p>1\<close> \<open>x \<le> y\<close> by (auto simp add: powr_mono2)
    next
      case 3
      then have "g x \<le> 0" "0 \<le> g y" unfolding g_def using \<open>p > 1\<close> by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    apply (rule convex_on_realI[of _ _ g]) using * ** by auto
qed

lemma convex_powr:
  assumes "p \<ge> 1"
  shows "convex_on {0..} (\<lambda>x::real. x powr p)"
proof -
  have "convex_on {0..} (\<lambda>x::real. \<bar>x\<bar> powr p)"
    using convex_abs_powr[OF \<open>p \<ge> 1\<close>] convex_on_subset by auto
  moreover have "\<bar>x\<bar> powr p = x powr p" if "x \<in> {0..}" for x using that by auto
  ultimately show ?thesis by (simp add: convex_on_def)
qed

lemma convex_powr':
  assumes "p > 0" "p \<le> 1"
  shows "convex_on {0..} (\<lambda>x::real. - (x powr p))"
proof -
  have "convex_on {0<..} (\<lambda>x::real. - (x powr p))"
    apply (rule convex_on_realI[of _ _ "\<lambda>x. -p * x powr (p-1)"])
    apply (auto intro!:derivative_intros simp add: has_real_derivative_powr)
    using \<open>p > 0\<close> \<open>p \<le> 1\<close> by (auto simp add: algebra_simps divide_simps powr_mono2')
  moreover have "continuous_on {0..} (\<lambda>x::real. - (x powr p))"
    by (rule continuous_on_minus, rule continuous_on_powr', auto simp add: \<open>p > 0\<close> intro!: continuous_intros)
  moreover have "{(0::real)..} = closure {0<..}" "convex {(0::real)<..}" by auto
  ultimately show ?thesis using convex_on_closure by metis
qed

lemma convex_fx_plus_fy_ineq:
  fixes f::"real \<Rightarrow> real"
  assumes "convex_on {0..} f"
          "x \<ge> 0" "y \<ge> 0" "f 0 = 0"
  shows "f x + f y \<le> f (x+y)"
proof -
  have *: "f a + f b \<le> f (a+b)" if "a \<ge> 0" "b \<ge> a" for a b
  proof (cases "a = 0")
    case False
    then have "a > 0" "b > 0" using \<open>b \<ge> a\<close> \<open>a \<ge> 0\<close> by auto
    have "(f 0 - f a) / (0 - a) \<le> (f 0 - f (a+b))/ (0 - (a+b))"
      apply (rule convex_on_diff[OF \<open>convex_on {0..} f\<close>]) using \<open>a > 0\<close> \<open>b > 0\<close> by auto
    also have "... \<le> (f b - f (a+b)) / (b - (a+b))"
      apply (rule convex_on_diff[OF \<open>convex_on {0..} f\<close>]) using \<open>a > 0\<close> \<open>b > 0\<close> by auto
    finally show ?thesis
      using \<open>a > 0\<close> \<open>b > 0\<close> \<open>f 0 = 0\<close> by (auto simp add: divide_simps algebra_simps)
  qed (simp add: \<open>f 0 = 0\<close>)
  then show ?thesis
    using \<open>x \<ge> 0\<close> \<open>y \<ge> 0\<close> by (metis add.commute le_less not_le)
qed

lemma x_plus_y_p_le_xp_plus_yp:
  fixes p x y::real
  assumes "p > 0" "p \<le> 1" "x \<ge> 0" "y \<ge> 0"
  shows "(x + y) powr p \<le> x powr p + y powr p"
using convex_fx_plus_fy_ineq[OF convex_powr'[OF \<open>p > 0\<close> \<open>p \<le> 1\<close>] \<open>x \<ge> 0\<close> \<open>y \<ge> 0\<close>] by auto


subsection \<open>Nonnegative-extended-real.thy\<close>

lemma x_plus_top_ennreal [simp]:
  "x + \<top> = (\<top>::ennreal)"
by simp

lemma ennreal_ge_nat_imp_PInf:
  fixes x::ennreal
  assumes "\<And>N. x \<ge> of_nat N"
  shows "x = \<infinity>"
using assms apply (cases x, auto) by (meson not_less reals_Archimedean2)

lemma ennreal_archimedean:
  assumes "x \<noteq> (\<infinity>::ennreal)"
  shows "\<exists>n::nat. x \<le> n"
proof (cases x)
  case (real r)
  then show ?thesis using real_arch_simple[of r] by auto
next
  case top
  then show ?thesis using assms by auto
qed

lemma e2ennreal_mult:
  fixes a b::ereal
  assumes "a \<ge> 0"
  shows "e2ennreal(a * b) = e2ennreal a * e2ennreal b"
by (metis assms e2ennreal_neg eq_onp_same_args ereal_mult_le_0_iff linear times_ennreal.abs_eq)

lemma e2ennreal_mult':
  fixes a b::ereal
  assumes "b \<ge> 0"
  shows "e2ennreal(a * b) = e2ennreal a * e2ennreal b"
using e2ennreal_mult[OF assms, of a] by (simp add: mult.commute)

lemma SUP_real_ennreal:
  assumes "A \<noteq> {}" "bdd_above (f`A)"
  shows "(SUP a\<in>A. ennreal (f a)) = ennreal(SUP a\<in>A. f a)"
apply (rule antisym, simp add: SUP_least assms(2) cSUP_upper ennreal_leI)
by (metis assms(1) ennreal_SUP ennreal_less_top le_less)

lemma e2ennreal_Liminf:
  "F \<noteq> bot \<Longrightarrow> e2ennreal (Liminf F f) = Liminf F (\<lambda>n. e2ennreal (f n))"
  by (rule Liminf_compose_continuous_mono[symmetric])
     (auto simp: mono_def e2ennreal_mono continuous_on_e2ennreal)

lemma e2ennreal_eq_infty[simp]: "0 \<le> x \<Longrightarrow> e2ennreal x = top \<longleftrightarrow> x = \<infinity>"
  by (cases x) (auto)

lemma ennreal_Inf_cmult:
  assumes "c>(0::real)"
  shows "Inf {ennreal c * x |x. P x} = ennreal c * Inf {x. P x}"
proof -
  have "(\<lambda>x::ennreal. c * x) (Inf {x::ennreal. P x}) = Inf ((\<lambda>x::ennreal. c * x)`{x::ennreal. P x})"
    apply (rule mono_bij_Inf)
    apply (simp add: monoI mult_left_mono)
    apply (rule bij_betw_byWitness[of _ "\<lambda>x. (x::ennreal) / c"], auto simp add: assms)
    apply (metis assms ennreal_lessI ennreal_neq_top mult.commute mult_divide_eq_ennreal not_less_zero)
    apply (metis assms divide_ennreal_def ennreal_less_zero_iff ennreal_neq_top less_irrefl mult.assoc mult.left_commute mult_divide_eq_ennreal)
    done
  then show ?thesis by (simp only: setcompr_eq_image[symmetric])
qed

lemma continuous_on_const_minus_ennreal:
  fixes f :: "'a :: topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. a - f x)"
  including ennreal.lifting
proof (transfer fixing: A; clarsimp)
  fix f :: "'a \<Rightarrow> ereal" and a :: "ereal" assume "0 \<le> a" "\<forall>x. 0 \<le> f x" and f: "continuous_on A f"
  then show "continuous_on A (\<lambda>x. max 0 (a - f x))"
  proof cases
    assume "\<exists>r. a = ereal r"
    with f show ?thesis
      by (auto simp: continuous_on_def minus_ereal_def ereal_Lim_uminus[symmetric]
              intro!: tendsto_add_ereal_general tendsto_max)
  next
    assume "\<nexists>r. a = ereal r"
    with \<open>0 \<le> a\<close> have "a = \<infinity>"
      by (cases a) auto
    then show ?thesis
      by (simp add: continuous_on_const)
  qed
qed

lemma const_minus_Liminf_ennreal:
  fixes a :: ennreal
  shows "F \<noteq> bot \<Longrightarrow> a - Liminf F f = Limsup F (\<lambda>x. a - f x)"
by (intro Limsup_compose_continuous_antimono[symmetric])
   (auto simp: antimono_def ennreal_mono_minus continuous_on_id continuous_on_const_minus_ennreal)

declare tendsto_ennrealI [tendsto_intros]

lemma tendsto_mult_ennreal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ennreal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l = 0 \<and> m = \<infinity>) \<or> (m = 0 \<and> l = \<infinity>))"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof -
  have "((\<lambda>x. enn2ereal(f x) * enn2ereal(g x)) \<longlongrightarrow> enn2ereal l * enn2ereal m) F"
    apply (auto intro!: tendsto_intros simp add: assms)
    by (insert assms le_zero_eq less_eq_ennreal.rep_eq, fastforce)+
  then have "((\<lambda>x. enn2ereal(f x * g x)) \<longlongrightarrow> enn2ereal(l * m)) F"
    using times_ennreal.rep_eq by auto
  then show ?thesis
    by (auto intro!: tendsto_intros)
qed

lemma tendsto_cmult_ennreal [tendsto_intros]:
  fixes c l::ennreal
  assumes "\<not>(c = \<infinity> \<and> l = 0)"
          "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>x. c * f x) \<longlongrightarrow> c * l) F"
by (cases "c = 0", insert assms, auto intro!: tendsto_intros)


subsection \<open>Indicator-Function.thy\<close>

text \<open>There is something weird with \verb+sum_mult_indicator+: it is defined both
in Indicator.thy and BochnerIntegration.thy, with a different meaning. I am surprised
there is no name collision... Here, I am using the version from BochnerIntegration.\<close>

lemma sum_indicator_eq_card2:
  assumes "finite I"
  shows "(\<Sum>i\<in>I. (indicator (P i) x)::nat) = card {i\<in>I. x \<in> P i}"
using sum_mult_indicator [OF assms, of "\<lambda>y. 1::nat" P "\<lambda>y. x"]
unfolding card_eq_sum by auto

lemma disjoint_family_indicator_le_1:
  assumes "disjoint_family_on A I"
  shows "(\<Sum> i\<in> I. indicator (A i) x) \<le> (1::'a:: {comm_monoid_add,zero_less_one})"
proof (cases "finite I")
  case True
  then have *: "(\<Sum> i\<in> I. indicator (A i) x) = ((indicator (\<Union>i\<in>I. A i) x)::'a)"
    by (simp add: indicator_UN_disjoint[OF True assms(1), of x])
  show ?thesis
    unfolding * unfolding indicator_def by (simp add: order_less_imp_le)
next
  case False
  then show ?thesis by (simp add: order_less_imp_le)
qed

subsection \<open>sigma-algebra.thy\<close>

lemma algebra_intersection:
  assumes "algebra \<Omega> A"
          "algebra \<Omega> B"
  shows "algebra \<Omega> (A \<inter> B)"
apply (subst algebra_iff_Un) using assms by (auto simp add: algebra_iff_Un)

lemma sigma_algebra_intersection:
  assumes "sigma_algebra \<Omega> A"
          "sigma_algebra \<Omega> B"
  shows "sigma_algebra \<Omega> (A \<inter> B)"
apply (subst sigma_algebra_iff) using assms by (auto simp add: sigma_algebra_iff algebra_intersection)

lemma subalgebra_M_M [simp]:
  "subalgebra M M"
by (simp add: subalgebra_def)

text \<open>The next one is \verb+disjoint_family_Suc+ with inclusions reversed.\<close>

lemma disjoint_family_Suc2:
  assumes Suc: "\<And>n. A (Suc n) \<subseteq> A n"
  shows "disjoint_family (\<lambda>i. A i - A (Suc i))"
proof -
  have "A (m+n) \<subseteq> A n" for m n
  proof (induct m)
    case 0 show ?case by simp
  next
    case (Suc m) then show ?case
      by (metis Suc_eq_plus1 assms add.commute add.left_commute subset_trans)
  qed
  then have "A m \<subseteq> A n" if "m > n" for m n
    by (metis that add.commute le_add_diff_inverse nat_less_le)
  then show ?thesis
    by (auto simp add: disjoint_family_on_def)
       (metis insert_absorb insert_subset le_SucE le_antisym not_le_imp_less)
qed


subsection \<open>Measure-Space.thy\<close>

lemma emeasure_union_inter:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M A + emeasure M B = emeasure M (A \<union> B) + emeasure M (A \<inter> B)"
proof -
  have "A = (A-B) \<union> (A \<inter> B)" by auto
  then have 1: "emeasure M A = emeasure M (A-B) + emeasure M (A \<inter> B)"
    by (metis Diff_Diff_Int Diff_disjoint assms(1) assms(2) plus_emeasure sets.Diff)

  have "A \<union> B = (A-B) \<union> B" by auto
  then have 2: "emeasure M (A \<union> B) = emeasure M (A-B) + emeasure M B"
    by (metis Diff_disjoint Int_commute assms(1) assms(2) plus_emeasure sets.Diff)

  show ?thesis using 1 2 by (metis add.assoc add.commute)
qed

lemma AE_equal_sum:
  assumes "\<And>i. AE x in M. f i x = g i x"
  shows "AE x in M. (\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)"
proof (cases)
  assume "finite I"
  have "\<exists>A. A \<in> null_sets M \<and> (\<forall>x\<in> (space M - A). f i x = g i x)" for i
    using assms(1)[of i] by (metis (mono_tags, lifting) AE_E3)
  then obtain A where A: "\<And>i. A i \<in> null_sets M \<and> (\<forall>x\<in> (space M -A i). f i x = g i x)"
    by metis
  define B where "B = (\<Union>i\<in>I. A i)"
  have "B \<in> null_sets M" using \<open>finite I\<close> A B_def by blast
  then have "AE x in M. x \<in> space M - B" by (simp add: AE_not_in)
  moreover
  {
    fix x assume "x \<in> space M - B"
    then have "\<And>i. i \<in> I \<Longrightarrow> f i x = g i x" unfolding B_def using A by auto
    then have "(\<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. g i x)" by auto
  }
  ultimately show ?thesis by auto
qed (simp)

lemma emeasure_pos_unionE:
  assumes "\<And> (N::nat). A N \<in> sets M"
          "emeasure M (\<Union>N. A N) > 0"
  shows "\<exists>N. emeasure M (A N) > 0"
proof (rule ccontr)
  assume "\<not>(\<exists>N. emeasure M (A N) > 0)"
  then have "\<And>N. A N \<in> null_sets M"
    using assms(1) by auto
  then have "(\<Union>N. A N) \<in> null_sets M" by auto
  then show False using assms(2) by auto
qed

lemma (in prob_space) emeasure_intersection:
  fixes e::"nat \<Rightarrow> real"
  assumes [measurable]: "\<And>n. U n \<in> sets M"
      and [simp]: "\<And>n. 0 \<le> e n" "summable e"
      and ge: "\<And>n. emeasure M (U n) \<ge> 1 - (e n)"
  shows "emeasure M (\<Inter>n. U n) \<ge> 1 - (\<Sum>n. e n)"
proof -
  define V where "V = (\<lambda>n. space M - (U n))"
  have [measurable]: "V n \<in> sets M" for n
    unfolding V_def by auto
  have *: "emeasure M (V n) \<le> e n" for n
    unfolding V_def using ge[of n] by (simp add: emeasure_eq_measure prob_compl ennreal_leI)
  have "emeasure M (\<Union>n. V n) \<le> (\<Sum>n. emeasure M (V n))"
    by (rule emeasure_subadditive_countably, auto)
  also have "... \<le> (\<Sum>n. ennreal (e n))"
    using * by (intro suminf_le) auto
  also have "... = ennreal (\<Sum>n. e n)"
    by (intro suminf_ennreal_eq) auto
  finally have "emeasure M (\<Union>n. V n) \<le> suminf e" by simp
  then have "1 - suminf e \<le> emeasure M (space M - (\<Union>n. V n))"
    by (simp add: emeasure_eq_measure prob_compl suminf_nonneg)
  also have "... \<le> emeasure M (\<Inter>n. U n)"
    by (rule emeasure_mono) (auto simp: V_def)
  finally show ?thesis by simp
qed

lemma null_sym_diff_transitive:
  assumes "A \<Delta> B \<in> null_sets M" "B \<Delta> C \<in> null_sets M"
      and [measurable]: "A \<in> sets M" "C \<in> sets M"
  shows "A \<Delta> C \<in> null_sets M"
proof -
  have "A \<Delta> B \<union> B \<Delta> C \<in> null_sets M" using assms(1) assms(2) by auto
  moreover have "A \<Delta> C \<subseteq> A \<Delta> B \<union> B \<Delta> C" by auto
  ultimately show ?thesis by (meson null_sets_subset assms(3) assms(4) sets.Diff sets.Un)
qed

lemma Delta_null_of_null_is_null:
  assumes "B \<in> sets M" "A \<Delta> B \<in> null_sets M" "A \<in> null_sets M"
  shows "B \<in> null_sets M"
proof -
  have "B \<subseteq> A \<union> (A \<Delta> B)" by auto
  then show ?thesis using assms by (meson null_sets.Un null_sets_subset)
qed

lemma Delta_null_same_emeasure:
  assumes "A \<Delta> B \<in> null_sets M" and [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "emeasure M A = emeasure M B"
proof -
  have "A = (A \<inter> B) \<union> (A-B)" by blast
  moreover have "A-B \<in> null_sets M" using assms null_sets_subset by blast
  ultimately have a: "emeasure M A = emeasure M (A \<inter> B)" using emeasure_Un_null_set by (metis assms(2) assms(3) sets.Int)

  have "B = (A \<inter> B) \<union> (B-A)" by blast
  moreover have "B-A \<in> null_sets M" using assms null_sets_subset by blast
  ultimately have "emeasure M B = emeasure M (A \<inter> B)" using emeasure_Un_null_set by (metis assms(2) assms(3) sets.Int)
  then show ?thesis using a by auto
qed

lemma AE_upper_bound_inf_ereal:
  fixes F G::"'a \<Rightarrow> ereal"
  assumes "\<And>e. (e::real) > 0 \<Longrightarrow> AE x in M. F x \<le> G x + e"
  shows "AE x in M. F x \<le> G x"
proof -
  have "AE x in M. \<forall>n::nat. F x \<le> G x + ereal (1 / Suc n)"
    using assms by (auto simp: AE_all_countable)
  then show ?thesis
  proof (eventually_elim)
    fix x assume x: "\<forall>n::nat. F x \<le> G x + ereal (1 / Suc n)"
    show "F x \<le> G x"
    proof (intro ereal_le_epsilon2[of _ "G x"] allI impI)
      fix e :: real assume "0 < e"
      then obtain n where n: "1 / Suc n < e"
        by (blast elim: nat_approx_posE)
      have "F x \<le> G x + 1 / Suc n"
        using x by simp
      also have "\<dots> \<le> G x + e"
        using n by (intro add_mono ennreal_leI) auto
      finally show "F x \<le> G x + ereal e" .
    qed
  qed
qed


text \<open>Egorov theorem asserts that, if a sequence of functions converges almost everywhere to a
limit, then the convergence is uniform on a subset of close to full measure. The first step in the
proof is the following lemma, often useful by itself, asserting the same result for predicates:
if a property $P_n x$ is eventually true for almost every $x$, then there exists $N$
such that $P_n x$ is true for all $n\geq N$ and all $x$ in a set of close to full measure.
\<close>
lemma (in finite_measure) Egorov_lemma:
  assumes [measurable]: "\<And>n. (P n) \<in> measurable M (count_space UNIV)"
      and "AE x in M. eventually (\<lambda>n. P n x) sequentially"
          "epsilon > 0"
  shows "\<exists>U N. U \<in> sets M \<and> (\<forall>n \<ge> N. \<forall>x \<in> U. P n x) \<and> emeasure M (space M - U) < epsilon"
proof -
  define K where "K = (\<lambda>n. {x \<in> space M. \<exists>k\<ge>n. \<not>(P k x)})"
  have [measurable]: "K n \<in> sets M" for n
    unfolding K_def by auto
  have "x \<notin> (\<Inter>n. K n)" if "eventually (\<lambda>n. P n x) sequentially" for x
    unfolding K_def using that unfolding K_def eventually_sequentially by auto
  then have "AE x in M. x \<notin> (\<Inter>n. K n)" using assms by auto
  then have Z: "0 = emeasure M (\<Inter>n. K n)"
    using AE_iff_measurable[of "(\<Inter>n. K n)" M "\<lambda>x. x \<notin> (\<Inter>n. K n)"] unfolding K_def by auto
  have *: "(\<lambda>n. emeasure M (K n)) \<longlonglongrightarrow> 0"
    unfolding Z apply (rule Lim_emeasure_decseq) using order_trans by (auto simp add: K_def decseq_def)
  have "eventually (\<lambda>n. emeasure M (K n) < epsilon) sequentially"
    by (rule order_tendstoD(2)[OF * \<open>epsilon > 0\<close>])
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> emeasure M (K n) < epsilon"
    unfolding eventually_sequentially by auto
  define U where "U = space M - K N"
  have A [measurable]: "U \<in> sets M" unfolding U_def by auto
  have "space M - U = K N"
    unfolding U_def K_def by auto
  then have B: "emeasure M (space M - U) < epsilon"
    using N by auto
  have "\<forall>n \<ge> N. \<forall>x \<in> U. P n x"
    unfolding U_def K_def by auto
  then show ?thesis using A B by blast
qed

text \<open>The next lemma asserts that, in an uncountable family of disjoint sets, then there is one
set with zero measure (and in fact uncountably many). It is often applied to the boundaries of
$r$-neighborhoods of a given set, to show that one could choose $r$ for which this boundary has
zero measure (this shows up often in relation with weak convergence).\<close>

lemma (in finite_measure) uncountable_disjoint_family_then_exists_zero_measure:
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
      and "uncountable I"
          "disjoint_family_on A I"
  shows "\<exists>i\<in>I. measure M (A i) = 0"
proof -
  define f where "f = (\<lambda>(r::real). {i \<in> I. measure M (A i) > r})"
  have *: "finite (f r)" if "r > 0" for r
  proof -
    obtain N::nat where N: "measure M (space M)/r \<le> N"
      using real_arch_simple by blast
    have "finite (f r) \<and> card (f r) \<le> N"
    proof (rule finite_if_finite_subsets_card_bdd)
      fix G assume G: "G \<subseteq> f r" "finite G"
      then have "G \<subseteq> I" unfolding f_def by auto
      have "card G * r = (\<Sum>i \<in> G. r)" by auto
      also have "... \<le> (\<Sum>i \<in> G. measure M (A i))"
        apply (rule sum_mono) using G unfolding f_def by auto
      also have "... = measure M (\<Union>i\<in>G. A i)"
        apply (rule finite_measure_finite_Union[symmetric])
        using \<open>finite G\<close> \<open>G \<subseteq> I\<close> \<open>disjoint_family_on A I\<close> disjoint_family_on_mono by auto
      also have "... \<le> measure M (space M)"
        by (simp add: bounded_measure)
      finally have "card G \<le> measure M (space M)/r"
        using \<open>r > 0\<close> by (simp add: divide_simps)
      then show "card G \<le> N" using N by auto
    qed
    then show ?thesis by simp
  qed
  have "countable (\<Union>n. f (((1::real)/2)^n))"
    by (rule countable_UN, auto intro!: countable_finite *)
  then have "I - (\<Union>n. f (((1::real)/2)^n)) \<noteq> {}"
    using assms(2) by (metis countable_empty uncountable_minus_countable)
  then obtain i where "i \<in> I" "i \<notin> (\<Union>n. f ((1/2)^n))" by auto
  then have "measure M (A i) \<le> (1 / 2) ^ n" for n
    unfolding f_def using linorder_not_le by auto
  moreover have "(\<lambda>n. ((1::real) / 2) ^ n) \<longlonglongrightarrow> 0"
    by (intro tendsto_intros, auto)
  ultimately have "measure M (A i) \<le> 0"
    using LIMSEQ_le_const by force
  then have "measure M (A i) = 0"
    by (simp add: measure_le_0_iff)
  then show ?thesis using \<open>i \<in> I\<close> by auto
qed

text \<open>The next statements are useful measurability statements.\<close>

lemma measurable_Inf [measurable]:
  assumes [measurable]: "\<And>(n::nat). P n \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. Inf {n. P n x}) \<in> measurable M (count_space UNIV)" (is "?f \<in> _")
proof -
  define A where "A = (\<lambda>n. (P n)-`{True} \<inter> space M - (\<Union>m<n. (P m)-`{True} \<inter> space M))"
  have A_meas [measurable]: "A n \<in> sets M" for n unfolding A_def by measurable
  define B where "B = (\<lambda>n. if n = 0 then (space M - (\<Union>n. A n)) else A (n-1))"
  show ?thesis
  proof (rule measurable_piecewise_restrict2[of B])
    show "B n \<in> sets M" for n unfolding B_def by simp
    show "space M = (\<Union>n. B n)"
      unfolding B_def using sets.sets_into_space [OF A_meas] by auto
    have *: "?f x = n" if "x \<in> A n" for x n
      apply (rule cInf_eq_minimum) using that unfolding A_def by auto
    moreover have **: "?f x = (Inf ({}::nat set))" if "x \<in> space M - (\<Union>n. A n)" for x
    proof -
      have "\<not>(P n x)" for n
        apply (induction n rule: nat_less_induct) using that unfolding A_def by auto
      then show ?thesis by simp
    qed
    ultimately have "\<exists>c. \<forall>x \<in> B n. ?f x = c" for n
      apply (cases "n = 0") unfolding B_def by auto
    then show "\<exists>h \<in> measurable M (count_space UNIV). \<forall>x \<in> B n. ?f x = h x" for n
      by fastforce
  qed
qed

lemma measurable_T_iter [measurable]:
  fixes f::"'a \<Rightarrow> nat"
  assumes [measurable]: "T \<in> measurable M M"
          "f \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. (T^^(f x)) x) \<in> measurable M M"
proof -
  have [measurable]: "(T^^n) \<in> measurable M M" for n::nat
    by (induction n, auto)
  show ?thesis
    by (rule measurable_compose_countable, auto)
qed

lemma measurable_infdist [measurable]:
  "(\<lambda>x. infdist x S) \<in> borel_measurable borel"
by (rule borel_measurable_continuous_on1, intro continuous_intros)

text \<open>The next lemma shows that, in a sigma finite measure space, sets with large measure
can be approximated by sets with large but finite measure.\<close>

lemma (in sigma_finite_measure) approx_with_finite_emeasure:
  assumes W_meas: "W \<in> sets M"
      and W_inf: "emeasure M W > C"
  obtains Z where "Z \<in> sets M" "Z \<subseteq> W" "emeasure M Z < \<infinity>" "emeasure M Z > C"
proof (cases "emeasure M W = \<infinity>")
  case True
  obtain r where r: "C = ennreal r" using W_inf by (cases C, auto)
  obtain Z where "Z \<in> sets M" "Z \<subseteq> W" "emeasure M Z < \<infinity>" "emeasure M Z > C"
    unfolding r using approx_PInf_emeasure_with_finite[OF W_meas True, of r] by auto
  then show ?thesis using that by blast
next
  case False
  then have "W \<in> sets M" "W \<subseteq> W" "emeasure M W < \<infinity>" "emeasure M W > C"
    using assms apply auto using top.not_eq_extremum by blast
  then show ?thesis using that by blast
qed

subsection \<open>Nonnegative-Lebesgue-Integration.thy\<close>

text \<open>The next lemma is a variant of \verb+nn_integral_density+,
with the density on the right instead of the left, as seems more common.\<close>

lemma nn_integral_densityR:
  assumes [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable F"
  shows "(\<integral>\<^sup>+ x. f x * g x \<partial>F) = (\<integral>\<^sup>+ x. f x \<partial>(density F g))"
proof -
  have "(\<integral>\<^sup>+ x. f x * g x \<partial>F) = (\<integral>\<^sup>+ x. g x * f x \<partial>F)" by (simp add: mult.commute)
  also have "... = (\<integral>\<^sup>+ x. f x \<partial>(density F g))"
    by (rule nn_integral_density[symmetric], simp_all add: assms)
  finally show ?thesis by simp
qed

lemma not_AE_zero_int_ennreal_E:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes "(\<integral>\<^sup>+x. f x \<partial>M) > 0"
      and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>A\<in>sets M. \<exists>e::real>0. emeasure M A > 0 \<and> (\<forall>x \<in> A. f x \<ge> e)"
proof (rule not_AE_zero_ennreal_E, auto simp add: assms)
  assume *: "AE x in M. f x = 0"
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. 0 \<partial>M)" by (rule nn_integral_cong_AE, simp add: *)
  then have "(\<integral>\<^sup>+x. f x \<partial>M) = 0" by simp
  then show False using assms by simp
qed

lemma (in finite_measure) nn_integral_bounded_eq_bound_then_AE:
  assumes "AE x in M. f x \<le> ennreal c" "(\<integral>\<^sup>+x. f x \<partial>M) = c * emeasure M (space M)"
      and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f x = c"
proof (cases)
  assume "emeasure M (space M) = 0"
  then show ?thesis by (rule emeasure_0_AE)
next
  assume "emeasure M (space M) \<noteq> 0"
  have fin: "AE x in M. f x \<noteq> top" using assms by (auto simp: top_unique)
  define g where "g = (\<lambda>x. c - f x)"
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def by auto
  have "(\<integral>\<^sup>+x. g x \<partial>M) = (\<integral>\<^sup>+x. c \<partial>M) - (\<integral>\<^sup>+x. f x \<partial>M)"
    unfolding g_def by (rule nn_integral_diff, auto simp add: assms ennreal_mult_eq_top_iff)
  also have "\<dots> = 0" using assms(2) by (auto simp: ennreal_mult_eq_top_iff)
  finally have "AE x in M. g x = 0"
    by (subst nn_integral_0_iff_AE[symmetric]) auto
  then have "AE x in M. c \<le> f x" unfolding g_def using fin by (auto simp: ennreal_minus_eq_0)
  then show ?thesis using assms(1) by auto
qed


lemma null_sets_density:
  assumes [measurable]: "h \<in> borel_measurable M"
      and "AE x in M. h x \<noteq> 0"
  shows "null_sets (density M h) = null_sets M"
proof -
  have *: "A \<in> sets M \<and> (AE x\<in>A in M. h x = 0) \<longleftrightarrow> A \<in> null_sets M" for A
  proof (auto)
    assume "A \<in> sets M" "AE x\<in>A in M. h x = 0"
    then show "A \<in> null_sets M"
      unfolding AE_iff_null_sets[OF \<open>A \<in> sets M\<close>] using assms(2) by auto
  next
    assume "A \<in> null_sets M"
    then show "AE x\<in>A in M. h x = 0"
      by (metis (mono_tags, lifting) AE_not_in eventually_mono)
  qed
  show ?thesis
    apply (rule set_eqI)
    unfolding null_sets_density_iff[OF \<open>h \<in> borel_measurable M\<close>] using * by auto
qed


text \<open>The next proposition asserts that, if a function $h$ is integrable, then its integral on
any set with small enough measure is small. The good conceptual proof is by considering the
distribution of the function $h$ on $\mathbb{R}$ and looking at its tails. However, there is a
less conceptual but more direct proof, based on dominated convergence and a proof by contradiction.
This is the proof we give below.\<close>

proposition integrable_small_integral_on_small_sets:
  fixes h::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M h"
      and "delta > 0"
  shows "\<exists>epsilon>(0::real). \<forall>U \<in> sets M. emeasure M U < epsilon \<longrightarrow> abs (\<integral>x\<in>U. h x \<partial>M) < delta"
proof (rule ccontr)
  assume H: "\<not> (\<exists>epsilon>0. \<forall>U\<in>sets M. emeasure M U < ennreal epsilon \<longrightarrow> abs(set_lebesgue_integral M U h) < delta)"
  have "\<exists>f. \<forall>epsilon\<in>{0<..}. f epsilon \<in>sets M \<and> emeasure M (f epsilon) < ennreal epsilon
                            \<and> \<not>(abs(set_lebesgue_integral M (f epsilon) h) < delta)"
    apply (rule bchoice) using H by auto
  then obtain f::"real \<Rightarrow> 'a set" where f:
              "\<And>epsilon. epsilon > 0 \<Longrightarrow> f epsilon \<in>sets M"
              "\<And>epsilon. epsilon > 0 \<Longrightarrow> emeasure M (f epsilon) < ennreal epsilon"
              "\<And>epsilon. epsilon > 0 \<Longrightarrow> \<not>(abs(set_lebesgue_integral M (f epsilon) h) < delta)"
    by blast
  define A where "A = (\<lambda>n::nat. f ((1/2)^n))"
  have [measurable]: "A n \<in> sets M" for n
    unfolding A_def using f(1) by auto
  have *: "emeasure M (A n) < ennreal ((1/2)^n)" for n
    unfolding A_def using f(2) by auto
  have Large: "\<not>(abs(set_lebesgue_integral M (A n) h) < delta)" for n
    unfolding A_def using f(3) by auto

  have S: "summable (\<lambda>n. Sigma_Algebra.measure M (A n))"
    apply (rule summable_comparison_test'[of "\<lambda>n. (1/2)^n" 0])
    apply (rule summable_geometric, auto)
    apply (subst ennreal_le_iff[symmetric], simp)
    using less_imp_le[OF *] by (metis * emeasure_eq_ennreal_measure top.extremum_strict)
  have "AE x in M. eventually (\<lambda>n. x \<in> space M - A n) sequentially"
    apply (rule borel_cantelli_AE1, auto simp add: S)
    by (metis * top.extremum_strict top.not_eq_extremum)
  moreover have "(\<lambda>n. indicator (A n) x * h x) \<longlonglongrightarrow> 0"
    if "eventually (\<lambda>n. x \<in> space M - A n) sequentially" for x
  proof -
    have "eventually (\<lambda>n. indicator (A n) x * h x = 0) sequentially"
      apply (rule eventually_mono[OF that]) unfolding indicator_def by auto
    then show ?thesis
      unfolding eventually_sequentially using tendsto_explicit by force
  qed
  ultimately have A: "AE x in M. ((\<lambda>n. indicator (A n) x * h x) \<longlonglongrightarrow> 0)"
    by auto
  have I: "integrable M (\<lambda>x. abs(h x))"
    using \<open>integrable M h\<close> by auto
  have L: "(\<lambda>n. abs (\<integral>x. indicator (A n) x * h x \<partial>M)) \<longlonglongrightarrow> abs (\<integral>x. 0 \<partial>M)"
    apply (intro tendsto_intros)
    apply (rule integral_dominated_convergence[OF _ _ I A])
    unfolding indicator_def by auto
  have "eventually (\<lambda>n. abs (\<integral>x. indicator (A n) x * h x \<partial>M) < delta) sequentially"
    apply (rule order_tendstoD[OF L]) using \<open>delta > 0\<close> by auto
  then show False
    using Large by (auto simp: set_lebesgue_integral_def)
qed

text \<open>We also give the version for nonnegative ennreal valued functions. It follows from the
previous one.\<close>

proposition small_nn_integral_on_small_sets:
  fixes h::"'a \<Rightarrow> ennreal"
  assumes [measurable]: "h \<in> borel_measurable M"
      and "delta > (0::real)" "(\<integral>\<^sup>+x. h x \<partial>M) \<noteq> \<infinity>"
  shows "\<exists>epsilon>(0::real). \<forall>U \<in> sets M. emeasure M U < epsilon \<longrightarrow> (\<integral>\<^sup>+x\<in>U. h x \<partial>M) < delta"
proof -
  define f where "f = (\<lambda>x. enn2real(h x))"
  have "AE x in M. h x \<noteq> \<infinity>"
    using assms by (metis nn_integral_PInf_AE)
  then have *: "AE x in M. ennreal (f x) = h x"
    unfolding f_def using ennreal_enn2real_if by auto
  have **: "(\<integral>\<^sup>+x. ennreal (f x) \<partial>M) \<noteq> \<infinity>"
    using nn_integral_cong_AE[OF *] assms by auto
  have [measurable]: "f \<in> borel_measurable M" unfolding f_def by auto
  have "integrable M f"
    apply (rule integrableI_nonneg) using assms * f_def ** apply auto
    using top.not_eq_extremum by blast
  obtain epsilon::real where H: "epsilon > 0" "\<And>U. U \<in> sets M \<Longrightarrow> emeasure M U < epsilon \<Longrightarrow> abs(\<integral>x\<in>U. f x \<partial>M) < delta"
    using integrable_small_integral_on_small_sets[OF \<open>integrable M f\<close> \<open>delta > 0\<close>] by blast
  have "(\<integral>\<^sup>+x\<in>U. h x \<partial>M) < delta" if [measurable]: "U \<in> sets M" "emeasure M U < epsilon" for U
  proof -
    have "(\<integral>\<^sup>+x. indicator U x * h x \<partial>M) = (\<integral>\<^sup>+x. ennreal(indicator U x * f x) \<partial>M)"
      apply (rule nn_integral_cong_AE) using * unfolding indicator_def by auto
    also have "... = ennreal (\<integral>x. indicator U x * f x \<partial>M)"
      apply (rule nn_integral_eq_integral)
      apply (rule Bochner_Integration.integrable_bound[OF \<open>integrable M f\<close>])
      unfolding indicator_def f_def by auto
    also have "... < ennreal delta"
      apply (rule ennreal_lessI) using H(2)[OF that] by (auto simp: set_lebesgue_integral_def)
    finally show ?thesis by (auto simp add: mult.commute)
  qed
  then show ?thesis using \<open>epsilon > 0\<close> by auto
qed

subsection \<open>Lebesgue-Measure.thy\<close>

text \<open>The next lemma is the same as \verb+lborel_distr_plus+ which is only formulated
on the real line, but on any euclidean space\<close>

lemma lborel_distr_plus2:
  fixes c :: "'a::euclidean_space"
  shows "distr lborel borel ((+) c) = lborel"
by (subst lborel_affine[of 1 c], auto simp: density_1)


subsection \<open>Probability-measure.thy\<close>

text \<open>The next lemmas ensure that, if sets have a probability close to $1$, then their
intersection also does.\<close>

lemma (in prob_space) sum_measure_le_measure_inter:
  assumes "A \<in> sets M" "B \<in> sets M"
  shows "prob A + prob B \<le> 1 + prob (A \<inter> B)"
proof -
  have "prob A + prob B = prob (A \<union> B) + prob (A \<inter> B)"
    by (simp add: assms(1) assms(2) fmeasurable_eq_sets measure_Un3)
  also have "... \<le> 1 + prob (A \<inter> B)"
    by auto
  finally show ?thesis by simp
qed

lemma (in prob_space) sum_measure_le_measure_inter3:
  assumes [measurable]: "A \<in> sets M" "B \<in> sets M" "C \<in> sets M"
  shows "prob A + prob B + prob C \<le> 2 + prob (A \<inter> B \<inter> C)"
using sum_measure_le_measure_inter[of B C] sum_measure_le_measure_inter[of A "B \<inter> C"]
by (auto simp add: inf_assoc)

lemma (in prob_space) sum_measure_le_measure_Inter:
  assumes [measurable]: "finite I" "I \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(\<Sum>i\<in>I. prob (A i)) \<le> real(card I) - 1 + prob (\<Inter>i\<in>I. A i)"
using assms proof (induct I rule: finite_ne_induct)
  fix x F assume H: "finite F" "F \<noteq> {}" "x \<notin> F"
            "((\<And>i. i \<in> F \<Longrightarrow> A i \<in> events) \<Longrightarrow> (\<Sum>i\<in>F. prob (A i)) \<le> real (card F) - 1 + prob (\<Inter>(A ` F)))"
        and [measurable]: "(\<And>i. i \<in> insert x F \<Longrightarrow> A i \<in> events)"
  have "(\<Inter>x\<in>F. A x) \<in> events" using \<open>finite F\<close> \<open>F \<noteq> {}\<close> by auto
  have "(\<Sum>i\<in>insert x F. prob (A i)) = (\<Sum>i\<in>F. prob (A i)) + prob (A x)"
    using H(1) H(3) by auto
  also have "... \<le> real (card F)-1 + prob (\<Inter>(A ` F)) + prob (A x)"
    using H(4) by auto
  also have "... \<le> real (card F) + prob ((\<Inter>(A ` F)) \<inter> A x)"
    using sum_measure_le_measure_inter[OF \<open>(\<Inter>x\<in>F. A x) \<in> events\<close>, of "A x"] by auto
  also have "... = real (card (insert x F)) - 1 + prob (\<Inter>(A ` (insert x F)))"
    using H(1) H(2) unfolding card_insert_disjoint[OF \<open>finite F\<close> \<open>x \<notin> F\<close>] by (simp add: inf_commute)
  finally show "(\<Sum>i\<in>insert x F. prob (A i)) \<le> real (card (insert x F)) - 1 + prob (\<Inter>(A ` (insert x F)))"
    by simp
qed (auto)

text \<open>A random variable gives a small mass to small neighborhoods of
infinity.\<close>
lemma (in prob_space) random_variable_small_tails:
  assumes "alpha > 0" and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>(C::real). prob {x \<in> space M. abs(f x) \<ge> C} < alpha \<and> C \<ge> K"
proof -
  have *: "(\<Inter>(n::nat). {x\<in>space M. abs(f x) \<ge> n}) = {}"
    apply auto
    by (metis real_arch_simple add.right_neutral add_mono_thms_linordered_field(4) not_less zero_less_one)
  have **: "(\<lambda>n. prob {x \<in> space M. abs(f x) \<ge> n}) \<longlonglongrightarrow> prob (\<Inter>(n::nat). {x \<in> space M. abs(f x) \<ge> n})"
    by (rule finite_Lim_measure_decseq, auto simp add: decseq_def)
  have "eventually (\<lambda>n. prob {x \<in> space M. abs(f x) \<ge> n} < alpha) sequentially"
    apply (rule order_tendstoD[OF _ \<open>alpha > 0\<close>]) using ** unfolding * by auto
  then obtain N::nat where N: "\<And>n::nat. n \<ge> N \<Longrightarrow> prob {x \<in> space M. abs(f x) \<ge> n} < alpha"
    unfolding eventually_sequentially by blast
  have "\<exists>n::nat. n \<ge> N \<and> n \<ge> K"
    by (meson le_cases of_nat_le_iff order.trans real_arch_simple)
  then obtain n::nat where n: "n \<ge> N" "n \<ge> K" by blast
  show ?thesis
    apply (rule exI[of _ "of_nat n"]) using N n by auto
qed

subsection \<open>Distribution-functions.thy\<close>

text \<open>There is a locale called \verb+finite_borel_measure+ in \verb+distribution-functions.thy+.
However, it only deals with real measures, and real weak convergence. I will not need the
weak convergence in more general settings, but still it seems more natural to me to do the
proofs in the natural settings. Let me introduce the locale \verb+finite_borel_measure'+ for
this, although it would be better to rename the locale in the library file.\<close>

locale finite_borel_measure' = finite_measure M for M :: "('a::metric_space) measure" +
  assumes M_is_borel [simp, measurable_cong]: "sets M = sets borel"
begin

lemma space_eq_univ [simp]: "space M = UNIV"
  using M_is_borel[THEN sets_eq_imp_space_eq] by simp

lemma measurable_finite_borel [simp]:
  "f \<in> borel_measurable borel \<Longrightarrow> f \<in> borel_measurable M"
  by (rule borel_measurable_subalgebra[where N = borel]) auto

text \<open>Any closed set can be slightly enlarged to obtain a set whose boundary has $0$ measure.\<close>

lemma approx_closed_set_with_set_zero_measure_boundary:
  assumes "closed S" "epsilon > 0" "S \<noteq> {}"
  shows "\<exists>r. r < epsilon \<and> r > 0 \<and> measure M {x. infdist x S = r} = 0 \<and> measure M {x. infdist x S \<le> r} < measure M S + epsilon"
proof -
  have [measurable]: "S \<in> sets M"
    using \<open>closed S\<close> by auto
  define T where "T = (\<lambda>r. {x. infdist x S \<le> r})"
  have [measurable]: "T r \<in> sets borel" for r
    unfolding T_def by measurable
  have *: "(\<Inter>n. T ((1/2)^n)) = S"
  unfolding T_def proof (auto)
    fix x assume *: "\<forall>n. infdist x S \<le> (1 / 2) ^n"
    have "infdist x S \<le> 0"
      apply (rule LIMSEQ_le_const[of "\<lambda>n. (1/2)^n"], intro tendsto_intros) using * by auto
    then show "x \<in> S"
      using assms infdist_pos_not_in_closed by fastforce
  qed
  have A: "((1::real)/2)^n \<le> (1/2)^m" if "m \<le> n" for m n::nat
    using that by (simp add: power_decreasing)
  have "(\<lambda>n. measure M (T ((1/2)^n))) \<longlonglongrightarrow> measure M S"
    unfolding *[symmetric] apply (rule finite_Lim_measure_decseq, auto simp add: T_def decseq_def)
    using A order.trans by blast
  then have B: "eventually (\<lambda>n. measure M (T ((1/2)^n)) < measure M S + epsilon) sequentially"
    apply (rule order_tendstoD) using \<open>epsilon > 0\<close> by simp
  have C: "eventually (\<lambda>n. (1/2)^n < epsilon) sequentially"
    by (rule order_tendstoD[OF _ \<open>epsilon > 0\<close>], intro tendsto_intros, auto)
  obtain n where n: "(1/2)^n < epsilon" "measure M (T ((1/2)^n)) < measure M S + epsilon"
    using eventually_conj[OF B C] unfolding eventually_sequentially by auto
  have "\<exists>r\<in>{0<..<(1/2)^n}. measure M {x. infdist x S = r} = 0"
    apply (rule uncountable_disjoint_family_then_exists_zero_measure, auto simp add: disjoint_family_on_def)
    using uncountable_open_interval by fastforce
  then obtain r where r: "r\<in>{0<..<(1/2)^n}" "measure M {x. infdist x S = r} = 0"
    by blast
  then have r2: "r > 0" "r < epsilon" using n by auto
  have "measure M {x. infdist x S \<le> r} \<le> measure M {x. infdist x S \<le> (1/2)^n}"
    apply (rule finite_measure_mono) using r by auto
  then have "measure M {x. infdist x S \<le> r} < measure M S + epsilon"
    using n(2) unfolding T_def by auto
  then show ?thesis
    using r(2) r2 by auto
qed
end (* of locale finite_borel_measure'*)

sublocale finite_borel_measure \<subseteq> finite_borel_measure'
  by (standard, simp add: M_is_borel)


subsection \<open>Weak-convergence.thy\<close>

text \<open>Since weak convergence is not implemented as a topology, the fact that the convergence of
a sequence implies the convergence of a subsequence is not automatic. We prove it in the lemma
below..\<close>

lemma weak_conv_m_subseq:
  assumes "weak_conv_m M_seq M" "strict_mono r"
  shows "weak_conv_m (\<lambda>n. M_seq (r n)) M"
using assms LIMSEQ_subseq_LIMSEQ unfolding weak_conv_m_def weak_conv_def comp_def by auto

context
  fixes \<mu> :: "nat \<Rightarrow> real measure"
    and M :: "real measure"
  assumes \<mu>: "\<And>n. real_distribution (\<mu> n)"
  assumes M: "real_distribution M"
  assumes \<mu>_to_M: "weak_conv_m \<mu> M"
begin

text \<open>The measure of a closed set behaves upper semicontinuously with respect to weak convergence:
if $\mu_n \to \mu$, then $\limsup \mu_n(F) \leq \mu(F)$ (and the inequality can be strict, think of
the situation where $\mu$ is a Dirac mass at $0$ and $F = \{0\}$, but $\mu_n$ has a density so that
$\mu_n(\{0\}) = 0$).\<close>

lemma closed_set_weak_conv_usc:
  assumes "closed S" "measure M S < l"
  shows "eventually (\<lambda>n. measure (\<mu> n) S < l) sequentially"
proof (cases "S = {}")
  case True
  then show ?thesis
    using \<open>measure M S < l\<close> by auto
next
  case False
  interpret real_distribution M using M by simp
  define epsilon where "epsilon = l - measure M S"
  have "epsilon > 0" unfolding epsilon_def using assms(2) by auto
  obtain r where r: "r > 0" "r < epsilon" "measure M {x. infdist x S = r} = 0" "measure M {x. infdist x S \<le> r} < measure M S + epsilon"
    using approx_closed_set_with_set_zero_measure_boundary[OF \<open>closed S\<close> \<open>epsilon > 0\<close> \<open>S \<noteq> {}\<close>] by blast
  define T where "T = {x. infdist x S \<le> r}"
  have [measurable]: "T \<in> sets borel"
    unfolding T_def by auto
  have "S \<subseteq> T"
    unfolding T_def using \<open>closed S\<close> \<open>r > 0\<close> by auto
  have "measure M T < l"
    using r(4) unfolding T_def epsilon_def by auto
  have "measure M (frontier T) \<le> measure M {x. infdist x S = r}"
    apply (rule finite_measure_mono) unfolding T_def using frontier_indist_le by auto
  then have "measure M (frontier T) = 0"
    using \<open>measure M {x. infdist x S = r} = 0\<close> by (auto simp add: measure_le_0_iff)
  then have "(\<lambda>n. measure (\<mu> n) T) \<longlonglongrightarrow> measure M T"
    using \<mu>_to_M by (simp add: \<mu> emeasure_eq_measure real_distribution_axioms weak_conv_imp_continuity_set_conv)
  then have *: "eventually (\<lambda>n. measure (\<mu> n) T < l) sequentially"
    apply (rule order_tendstoD) using \<open>measure M T < l\<close> by simp
  have **: "measure (\<mu> n) S \<le> measure (\<mu> n) T" for n
    apply (rule finite_measure.finite_measure_mono)
    using \<mu> apply (simp add: finite_borel_measure.axioms(1) real_distribution.finite_borel_measure_M)
    using \<open>S \<subseteq> T\<close> apply simp
    by (simp add: \<mu> real_distribution.events_eq_borel)
  show ?thesis
    apply (rule eventually_mono[OF *]) using ** le_less_trans by auto
qed

text \<open>In the same way, the measure of an open set behaves lower semicontinuously with respect to
weak convergence: if $\mu_n \to \mu$, then $\liminf \mu_n(U) \geq \mu(U)$ (and the inequality can be
strict). This follows from the same statement for closed sets by passing to the complement.\<close>

lemma open_set_weak_conv_lsc:
  assumes "open S" "measure M S > l"
  shows "eventually (\<lambda>n. measure (\<mu> n) S > l) sequentially"
proof -
  interpret real_distribution M
    using M by auto
  have [measurable]: "S \<in> events" using assms(1) by auto
  have "eventually (\<lambda>n. measure (\<mu> n) (UNIV - S) < 1 - l) sequentially"
    apply (rule closed_set_weak_conv_usc)
    using assms prob_compl[of S] by auto
  moreover have "measure (\<mu> n) (UNIV - S) = 1 - measure (\<mu> n) S" for n
  proof -
    interpret mu: real_distribution "\<mu> n"
      using \<mu> by auto
    have "S \<in> mu.events" using assms(1) by auto
    then show ?thesis using mu.prob_compl[of S] by auto
  qed
  ultimately show ?thesis by auto
qed

end (*of context weak_conv_m*)

end (*of SG_Library_Complement.thy*)
