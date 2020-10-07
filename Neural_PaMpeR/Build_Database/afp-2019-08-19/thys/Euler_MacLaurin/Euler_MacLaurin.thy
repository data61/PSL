section \<open>The Euler--MacLaurin summation formula\<close>
theory Euler_MacLaurin
imports 
  "HOL-Analysis.Analysis"
  "HOL-Library.Multiset"
  Bernoulli.Periodic_Bernpoly
  Bernoulli.Bernoulli_FPS
begin
  
subsection \<open>Auxiliary facts\<close>

(* TODO Move? *)
lemma pbernpoly_of_int [simp]: "pbernpoly n (of_int a) = bernoulli n"
  by (simp add: pbernpoly_def)

lemma continuous_on_bernpoly' [continuous_intros]:
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. bernpoly n (f x) :: 'a :: real_normed_algebra_1)"
  using continuous_on_compose2[OF continuous_on_bernpoly assms, of UNIV n] by auto

lemma sum_atLeastAtMost_int_last:
  assumes "a < (b :: int)"
  shows   "sum f {a..b} = sum f {a..<b} + f b"
proof -
  from assms have "{a..b} = insert b {a..<b}" by auto
  also have "sum f \<dots> = sum f {a..<b} + f b"
    by (subst sum.insert) (auto simp: add_ac)
  finally show ?thesis .
qed

lemma sum_atLeastAtMost_int_head:
  assumes "a < (b :: int)"
  shows   "sum f {a..b} = f a + sum f {a<..b}"
proof -
  from assms have "{a..b} = insert a {a<..b}" by auto
  also have "sum f \<dots> = f a + sum f {a<..b}"
    by (subst sum.insert) auto
  finally show ?thesis .
qed

lemma not_in_nonpos_Reals_imp_add_nonzero:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0" "x \<ge> 0"
  shows   "z + of_real x \<noteq> 0"
  using assms by (auto simp: add_eq_0_iff2)
(* END TODO *)

lemma negligible_atLeastAtMostI: "b \<le> a \<Longrightarrow> negligible {a..(b::real)}"
  by (cases "b < a") auto
    
lemma integrable_on_negligible: 
 "negligible A \<Longrightarrow> (f :: 'n :: euclidean_space \<Rightarrow> 'a :: banach) integrable_on A"
  by (subst integrable_spike_set_eq[of _ "{}"]) (simp_all add: integrable_on_empty)  
    
lemma Union_atLeastAtMost_real_of_int:
  assumes "a < b" 
  shows   "(\<Union>n\<in>{a..<b}. {real_of_int n..real_of_int (n + 1)}) = {real_of_int a..real_of_int b}"
proof (intro equalityI subsetI)
  fix x assume x: "x \<in> {real_of_int a..real_of_int b}"
  thus "x \<in> (\<Union>n\<in>{a..<b}. {real_of_int n..real_of_int (n + 1)})"
  proof (cases "x = real_of_int b")
    case True
    with assms show ?thesis by (auto intro!: bexI[of _ "b - 1"])
  next
    case False
    with x have x: "x \<ge> real_of_int a" "x < real_of_int b" by simp_all
    hence "x \<ge> of_int \<lfloor>x\<rfloor>" "x \<le> of_int \<lfloor>x\<rfloor> + 1" by linarith+
    moreover from x have "\<lfloor>x\<rfloor> \<ge> a" "\<lfloor>x\<rfloor> < b" by linarith+ 
    ultimately have "\<exists>n\<in>{a..<b}. x \<in> {of_int n..of_int (n + 1)}"
      by (intro bexI[of _ "\<lfloor>x\<rfloor>"]) simp_all
    thus ?thesis by blast
  qed
qed auto


subsection \<open>The remainder terms\<close>

text \<open>
  The following describes the remainder term in the classical version of the Euler--MacLaurin
  formula.
\<close>
definition EM_remainder' :: "nat \<Rightarrow> (real \<Rightarrow> 'a :: banach) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a" where
  "EM_remainder' n f a b = ((-1) ^ Suc n / fact n) *\<^sub>R integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t)"


text \<open>
  Next, we define the remainder term that occurs when one lets the right bound of summation 
  in the Euler--MacLaurin formula tend to infinity.
\<close>
definition EM_remainder_converges :: "nat \<Rightarrow> (real \<Rightarrow> 'a :: banach) \<Rightarrow> int \<Rightarrow> bool" where
  "EM_remainder_converges n f a \<longleftrightarrow> (\<exists>L. ((\<lambda>x. EM_remainder' n f a (of_int x)) \<longlongrightarrow> L) at_top)"

definition EM_remainder :: "nat \<Rightarrow> (real \<Rightarrow> 'a :: banach) \<Rightarrow> int \<Rightarrow> 'a" where
  "EM_remainder n f a = 
     (if EM_remainder_converges n f a then
        Lim at_top (\<lambda>x. EM_remainder' n f a (of_int x)) else 0)"

text \<open>
  The following lemmas are fairly obvious -- but tedious to prove -- 
  properties of the remainder terms.
\<close>

lemma EM_remainder_eqI: 
  fixes L
  assumes "((\<lambda>x. EM_remainder' n f b (of_int x)) \<longlongrightarrow> L) at_top"
  shows   "EM_remainder n f b = L"
  using assms by (auto simp: EM_remainder_def EM_remainder_converges_def intro!: tendsto_Lim)

lemma integrable_EM_remainder'_int:
  fixes a b :: int and f :: "real \<Rightarrow> 'a :: banach"
  assumes "continuous_on {of_int a..of_int b} f"
  shows   "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on {a..b}"
proof -
  have [continuous_intros]: "continuous_on A f" if "A \<subseteq> {of_int a..of_int b}" for A
    using continuous_on_subset[OF assms that] .
  consider "a > b" | "a = b" | "a < b" "n = 1" | "a < b" "n \<noteq> 1"
    by (cases a b rule: linorder_cases) auto
  thus ?thesis
  proof cases
    assume "a < b" and "n \<noteq> 1"
    thus ?thesis by (intro integrable_continuous_real continuous_intros) auto
  next
    assume ab: "a < b" and [simp]: "n = 1"
    let ?A = "(\<lambda>n. {real_of_int n..real_of_int (n+1)}) ` {a..<b}"
    show ?thesis
    proof (rule integrable_combine_division; (intro ballI)?)
      show "?A division_of {of_int a..of_int b}"
        using Union_atLeastAtMost_real_of_int[OF ab] by (simp add: division_of_def)
    next
      fix I assume "I \<in> ?A"
      then obtain i where i: "i \<in> {a..<b}" "I = {of_int i..of_int (i + 1)}" by auto
      show "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on I"
      proof (rule integrable_spike)
        show "(\<lambda>t. (t - of_int i - 1/2) *\<^sub>R f t) integrable_on I"
          using i by (auto intro!: integrable_continuous_real continuous_intros)
      next
        fix x assume "x \<in> I - {of_int (i + 1)}"
        with i have "of_int i \<le> x" "x < of_int i + 1" by simp_all
        hence "floor x = i" by linarith
        thus "pbernpoly n x *\<^sub>R f x = (x - of_int i - 1 / 2) *\<^sub>R f x"
          by (simp add: pbernpoly_def bernpoly_def frac_def)
      qed simp_all
    qed
  qed (simp_all add: integrable_on_negligible)
qed

lemma integrable_EM_remainder':
  fixes a b :: real and f :: "real \<Rightarrow> 'a :: banach"
  assumes "continuous_on {a..b} f"
  shows   "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on {a..b}"
proof (cases "\<lceil>a\<rceil> \<le> \<lfloor>b\<rfloor>")
  case True
  define a' b' where "a' = \<lceil>a\<rceil>" and "b' = \<lfloor>b\<rfloor>"
  from True have *: "a' \<le> b'" "a' \<ge> a" "b' \<le> b" by (auto simp: a'_def b'_def)
  from * have A: "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on ({a'..b'})"
    by (intro integrable_EM_remainder'_int continuous_on_subset[OF assms]) auto
  have B: "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on ({a..a'})"
  proof (rule integrable_spike)
    show "pbernpoly n x *\<^sub>R f x = bernpoly n (x - of_int (floor a)) *\<^sub>R f x" 
         if "x \<in> {a..real_of_int a'} - {real_of_int a'}"for x
    proof -
      have "x \<ge> a" "x <real_of_int a'" using that by auto
      with True have "floor x = floor a" unfolding a'_def
        using ceiling_diff_floor_le_1[of a] by (intro floor_unique; linarith) 
      thus ?thesis by (simp add: pbernpoly_def frac_def)
    qed
  qed (insert *, auto intro!: continuous_intros integrable_continuous_real 
         continuous_on_subset[OF assms])
  have C: "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on ({b'..b})"
  proof (rule integrable_spike)
    show "pbernpoly n x *\<^sub>R f x = bernpoly n (x - of_int b') *\<^sub>R f x"
         if "x \<in> {real_of_int b'..b} - {real_of_int b'}" for x
    proof -
      have "x \<le> b" "x > real_of_int b'" using that by auto
      with True have "floor x = b'" unfolding b'_def by (intro floor_unique; linarith) 
      thus ?thesis by (simp add: pbernpoly_def frac_def)
    qed
  qed (insert *, auto intro!: continuous_intros integrable_continuous_real 
         continuous_on_subset[OF assms])
  have "(\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on ({a..a'} \<union> {a'..b'} \<union> {b'..b})" using * A B C
    by (intro integrable_Un; (subst ivl_disj_un)?)
       (auto simp: ivl_disj_un max_def min_def)
  also have "{a..a'} \<union> {a'..b'} \<union> {b'..b} = {a..b}" using * by auto
  finally show ?thesis .
next
  assume *: "\<not>ceiling a \<le> floor b"
  show ?thesis
  proof (rule integrable_spike)
    show "(\<lambda>t. bernpoly n (t - floor a) *\<^sub>R f t) integrable_on {a..b}" using *
      by (auto intro!: integrable_continuous_real continuous_intros assms)
  next
    show "pbernpoly n x *\<^sub>R f x = bernpoly n (x - floor a) *\<^sub>R f x"
         if "x \<in> {a..b} - {}" for x
    proof -
      from * have **: "b < floor a + 1" 
        unfolding ceiling_altdef by (auto split: if_splits simp: le_floor_iff)
      from that have x: "x \<ge> a" "x \<le> b" by simp_all
      with * ** have "floor x = floor a" by linarith
      thus ?thesis by (simp add: pbernpoly_def frac_def)
    qed
  qed simp_all
qed

lemma EM_remainder'_bounded_linear:
  assumes "bounded_linear h"
  assumes "continuous_on {a..b} f"
  shows   "EM_remainder' n (\<lambda>x. h (f x)) a b = h (EM_remainder' n f a b)"
proof -
  have "integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R h (f t)) = 
           integral {a..b} (\<lambda>t. h (pbernpoly n t *\<^sub>R f t))" using assms
    by (simp add: linear_simps)
  also have "\<dots> = h (integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t))"
    by (subst integral_linear [OF _ assms(1), symmetric])
       (auto intro!: integrable_EM_remainder' assms(2) simp: o_def)
  finally show ?thesis using assms(1)
    by (simp add: EM_remainder'_def linear_simps)
qed

lemma EM_remainder_converges_of_real:
  assumes "EM_remainder_converges n f a" "continuous_on {of_int a..} f"
  shows   "EM_remainder_converges n (\<lambda>x. of_real (f x)) a"
proof -
  from assms obtain L 
    where L: "((\<lambda>b. EM_remainder' n f (real_of_int a) (real_of_int b)) \<longlongrightarrow> L) at_top"
    by (auto simp: EM_remainder_converges_def)
  have "((\<lambda>b. EM_remainder' n (\<lambda>x. of_real (f x)) (of_int a) (of_int b)) \<longlongrightarrow> of_real L) at_top"
  proof (rule Lim_transform_eventually)
    show "eventually (\<lambda>b. of_real (EM_remainder' n f (of_int a) (of_int b)) = 
            EM_remainder' n (\<lambda>x. of_real (f x)) (of_int a) (of_int b)) at_top"
      using eventually_ge_at_top[of a]
      by eventually_elim
         (intro EM_remainder'_bounded_linear [OF bounded_linear_of_real, symmetric]
                continuous_on_subset[OF assms(2)], auto)
  qed (intro tendsto_intros L)
  thus ?thesis unfolding EM_remainder_converges_def ..
qed

lemma EM_remainder_converges_of_real_iff:
  fixes f :: "real \<Rightarrow> real"
  assumes "continuous_on {of_int a..} f"
  shows   "EM_remainder_converges n (\<lambda>x. of_real (f x) :: 
            'a :: {banach, real_normed_algebra_1, real_inner}) a \<longleftrightarrow> EM_remainder_converges n f a"
proof
  assume "EM_remainder_converges n (\<lambda>x. of_real (f x) :: 'a) a"
  then obtain L :: 'a
    where L: "((\<lambda>b. EM_remainder' n (\<lambda>x. of_real (f x)) (of_int a) (of_int b)) \<longlongrightarrow> L) at_top"
    by (auto simp: EM_remainder_converges_def)
  have "((\<lambda>b. EM_remainder' n f (of_int a) (of_int b)) \<longlongrightarrow> L \<bullet> 1) at_top"
  proof (rule Lim_transform_eventually)
    show "eventually (\<lambda>b. EM_remainder' n (\<lambda>x. of_real (f x) :: 'a) (of_int a) (of_int b) \<bullet> 1 =
            EM_remainder' n f (of_int a) (of_int b)) at_top" using eventually_ge_at_top[of a]
      by eventually_elim
         (subst EM_remainder'_bounded_linear [OF bounded_linear_of_real],
          auto intro!: continuous_on_subset[OF assms])
  qed (intro tendsto_intros L)
  thus "EM_remainder_converges n f a" unfolding EM_remainder_converges_def ..
qed (intro EM_remainder_converges_of_real assms)

lemma EM_remainder_of_real:
  assumes "continuous_on {a..} f"
  shows   "EM_remainder n (\<lambda>x. of_real (f x) :: 
             'a :: {banach, real_normed_algebra_1, real_inner}) a = 
             of_real (EM_remainder n f a)"
proof -
  have eq: "EM_remainder' n (\<lambda>x. of_real (f x) :: 'a) (real_of_int a) = 
              (\<lambda>x::int. of_real (EM_remainder' n f a x))"
      by (intro ext EM_remainder'_bounded_linear[OF bounded_linear_of_real]
            continuous_on_subset[OF assms]) auto
  show ?thesis
  proof (cases "EM_remainder_converges n f a")
    case False
    with EM_remainder_converges_of_real_iff[OF assms, of n] show ?thesis
      by (auto simp: EM_remainder_def)
  next
    case True
    then obtain L where L: "((\<lambda>x. EM_remainder' n f a (real_of_int x)) \<longlongrightarrow> L) at_top" 
      by (auto simp: EM_remainder_converges_def)
    have L': "((\<lambda>x. EM_remainder' n (\<lambda>x. of_real (f x) :: 'a) a 
                (real_of_int x)) \<longlongrightarrow> of_real L) at_top" unfolding eq by (intro tendsto_of_real L)
    from L L' tendsto_Lim[OF _ L] tendsto_Lim[OF _ L'] show ?thesis
      by (auto simp: EM_remainder_def EM_remainder_converges_def)
  qed
qed

lemma EM_remainder'_cong:
  assumes "\<And>x. x \<in> {a..b} \<Longrightarrow> f x = g x" "n = n'" "a = a'" "b = b'"
  shows   "EM_remainder' n f a b = EM_remainder' n' g a' b'"
proof -
  have "integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t) = integral {a'..b'} (\<lambda>t. pbernpoly n' t *\<^sub>R g t)"
    unfolding assms using assms by (intro integral_cong) auto
  with assms show ?thesis by (simp add: EM_remainder'_def)
qed

lemma EM_remainder_converges_cong:
  assumes "\<And>x. x \<ge> of_int a \<Longrightarrow> f x = g x" "n = n'" "a = a'"
  shows   "EM_remainder_converges n f a = EM_remainder_converges n' g a'"
  unfolding EM_remainder_converges_def
  by (subst EM_remainder'_cong[OF _ refl refl refl, of _ _ f g]) (use assms in auto)

lemma EM_remainder_cong:
  assumes "\<And>x. x \<ge> of_int a \<Longrightarrow> f x = g x" "n = n'" "a = a'"
  shows   "EM_remainder n f a = EM_remainder n' g a'"
proof -
  have *: "EM_remainder_converges n f a = EM_remainder_converges n' g a'"
    using assms by (intro EM_remainder_converges_cong) auto
  show ?thesis unfolding EM_remainder_def
    by (subst EM_remainder'_cong[OF _ refl refl refl, of _ _ f g]) (use assms * in auto)
qed

lemma EM_remainder_converges_cnj: 
  assumes "continuous_on {a..} f" and "EM_remainder_converges n f a"
  shows   "EM_remainder_converges n (\<lambda>x. cnj (f x)) a"
proof -
  interpret bounded_linear cnj by (rule bounded_linear_cnj)
  obtain L where L: "((\<lambda>x. EM_remainder' n f (real_of_int a) (real_of_int x)) \<longlongrightarrow> L) at_top"
    using assms unfolding EM_remainder_converges_def by blast
  note tendsto_cnj [OF this]
  also have "(\<lambda>x. cnj (EM_remainder' n f (real_of_int a) (real_of_int x))) =
               (\<lambda>x. EM_remainder' n (\<lambda>x. cnj (f x)) (real_of_int a) (real_of_int x))"
    by (subst EM_remainder'_bounded_linear [OF bounded_linear_cnj])
       (rule continuous_on_subset [OF assms(1)], auto)
  finally have L': "(\<dots> \<longlongrightarrow> cnj L) at_top" .
  thus "EM_remainder_converges n (\<lambda>x. cnj (f x)) a"
    by (auto simp: EM_remainder_converges_def)
qed

lemma EM_remainder_converges_cnj_iff:
  assumes "continuous_on {of_int a..} f"
  shows   "EM_remainder_converges n (\<lambda>x. cnj (f x)) a \<longleftrightarrow> EM_remainder_converges n f a"
proof
  assume "EM_remainder_converges n (\<lambda>x. cnj (f x)) a"
  hence "EM_remainder_converges n (\<lambda>x. cnj (cnj (f x))) a"
    by (rule EM_remainder_converges_cnj [rotated]) (auto intro: continuous_intros assms)
  thus "EM_remainder_converges n f a" by simp
qed (intro EM_remainder_converges_cnj assms)

lemma EM_remainder_cnj: 
  assumes "continuous_on {a..} f"
  shows   "EM_remainder n (\<lambda>x. cnj (f x)) a = cnj (EM_remainder n f a)"
proof (cases "EM_remainder_converges n f a")
  case False
  hence "\<not>EM_remainder_converges n (\<lambda>x. cnj (f x)) a"
    by (subst EM_remainder_converges_cnj_iff [OF assms])
  with False show ?thesis by (simp add: EM_remainder_def)
next
  case True
  then obtain L where L: "((\<lambda>x. EM_remainder' n f (real_of_int a) (real_of_int x)) \<longlongrightarrow> L) at_top"
    unfolding EM_remainder_converges_def by blast
  note tendsto_cnj [OF this]
  also have "(\<lambda>x. cnj (EM_remainder' n f (real_of_int a) (real_of_int x))) =
               (\<lambda>x. EM_remainder' n (\<lambda>x. cnj (f x)) (real_of_int a) (real_of_int x))"
    by (subst EM_remainder'_bounded_linear [OF bounded_linear_cnj])
       (rule continuous_on_subset [OF assms(1)], auto)
  finally have L': "(\<dots> \<longlongrightarrow> cnj L) at_top" .
  moreover from assms and L have "EM_remainder n f a = L"
    by (intro EM_remainder_eqI)
  ultimately show "EM_remainder n (\<lambda>x. cnj (f x)) a = cnj (EM_remainder n f a)"
    using L' by (intro EM_remainder_eqI) simp_all
qed

lemma EM_remainder'_combine:
  fixes f :: "real \<Rightarrow> 'a :: banach"
  assumes [continuous_intros]: "continuous_on {a..c} f"
  assumes "a \<le> b" "b \<le> c"
  shows   "EM_remainder' n f a b + EM_remainder' n f b c = EM_remainder' n f a c"
proof -
  have "integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t) + integral {b..c} (\<lambda>t. pbernpoly n t *\<^sub>R f t) =
          integral {a..c} (\<lambda>t. pbernpoly n t *\<^sub>R f t)"
    by (intro integral_combine assms integrable_EM_remainder')
  from this [symmetric] show ?thesis by (simp add: EM_remainder'_def algebra_simps) 
qed

lemma uniformly_convergent_EM_remainder':
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> 'b :: {banach,real_normed_algebra}"
  assumes deriv: "\<And>y. a \<le> y \<Longrightarrow> (G has_real_derivative g y) (at y within {a..})"
  assumes integrable: "\<And>a' b y. y \<in> A \<Longrightarrow>  a \<le> a' \<Longrightarrow> a' \<le> b \<Longrightarrow> 
                         (\<lambda>t. pbernpoly n t *\<^sub>R f y t) integrable_on {a'..b}"
  assumes conv: "convergent (\<lambda>y. G (real y))"
  assumes bound: "eventually (\<lambda>x. \<forall>y\<in>A. norm (f y x) \<le> g x) at_top"
  shows   "uniformly_convergent_on A (\<lambda>b s. EM_remainder' n (f s) a b)"
proof -
  interpret bounded_linear "\<lambda>x::'b. ((- 1) ^ Suc n / fact n) *\<^sub>R x"
    by (rule bounded_linear_scaleR_right)

  from bounded_pbernpoly[of n] guess C . note C = this
  from C[of 0] have [simp]: "C \<ge> 0" by simp

  show ?thesis unfolding EM_remainder'_def
  proof (intro uniformly_convergent_on uniformly_convergent_improper_integral')
    fix x assume "x \<ge> a"
    thus "((\<lambda>x. C * G x) has_real_derivative C * g x) (at x within {a..})"
      by (intro DERIV_cmult deriv)
  next
    fix y a' b assume "y \<in> A" "a \<le> a'" "a' \<le> b"
    thus "(\<lambda>t. pbernpoly n t *\<^sub>R f y t) integrable_on {a'..b}"
      by (rule integrable)
  next
    from conv obtain L where "(\<lambda>y. G (real y)) \<longlonglongrightarrow> L"
      by (auto simp: convergent_def)
    from tendsto_mult[OF tendsto_const[of C] this]
      show "convergent (\<lambda>y. C * G (real y))"
        by (auto simp: convergent_def)
  next
    show "\<forall>\<^sub>F x in at_top. \<forall>y\<in>A. norm (pbernpoly n x *\<^sub>R f y x) \<le> C * g x"
      using C unfolding norm_scaleR 
      by (intro eventually_mono[OF bound] ballI mult_mono) auto
  qed
qed

lemma uniform_limit_EM_remainder:
  fixes f :: "'a \<Rightarrow> real \<Rightarrow> 'b :: {banach,real_normed_algebra}"
  assumes deriv: "\<And>y. a \<le> y \<Longrightarrow> (G has_real_derivative g y) (at y within {a..})"
  assumes integrable: "\<And>a' b y. y \<in> A \<Longrightarrow>  a \<le> a' \<Longrightarrow> a' \<le> b \<Longrightarrow> 
                         (\<lambda>t. pbernpoly n t *\<^sub>R f y t) integrable_on {a'..b}"
  assumes conv: "convergent (\<lambda>y. G (real y))"
  assumes bound: "eventually (\<lambda>x. \<forall>y\<in>A. norm (f y x) \<le> g x) at_top"
  shows   "uniform_limit A (\<lambda>b s. EM_remainder' n (f s) a b) 
             (\<lambda>s. EM_remainder n (f s) a) sequentially"
proof -
  have *: "uniformly_convergent_on A (\<lambda>b s. EM_remainder' n (f s) a b)"
    by (rule uniformly_convergent_EM_remainder'[OF assms])
  also have "?this \<longleftrightarrow> ?thesis"
    unfolding uniformly_convergent_uniform_limit_iff
  proof (intro uniform_limit_cong refl always_eventually allI ballI)
    fix s assume "s \<in> A"
    with * have **: "convergent (\<lambda>b. EM_remainder' n (f s) a b)"
      by (rule uniformly_convergent_imp_convergent)
    show "lim (\<lambda>b. EM_remainder' n (f s) a b) = EM_remainder n (f s) a"
    proof (rule sym, rule EM_remainder_eqI)
      have "((\<lambda>x. EM_remainder' n (f s) (real_of_int a) (real x)) \<longlongrightarrow>
               lim (\<lambda>x. EM_remainder' n (f s) (real_of_int a) (real x))) at_top"
        (is "(_ \<longlongrightarrow> ?L) _") using ** unfolding convergent_LIMSEQ_iff by blast
      hence "((\<lambda>x. EM_remainder' n (f s) (real_of_int a) (real (nat x))) \<longlongrightarrow> ?L) at_top"
        by (rule filterlim_compose) (fact filterlim_nat_sequentially)
      thus "((\<lambda>x. EM_remainder' n (f s) (real_of_int a) (real_of_int x)) \<longlongrightarrow> ?L) at_top"
        by (rule Lim_transform_eventually [rotated])
           (auto intro: eventually_mono[OF eventually_ge_at_top[of 0]])
    qed
  qed
  finally show \<dots> .
qed

lemma tendsto_EM_remainder:
  fixes f :: "real \<Rightarrow> 'b :: {banach,real_normed_algebra}"
  assumes deriv: "\<And>y. a \<le> y \<Longrightarrow> (G has_real_derivative g y) (at y within {a..})"
  assumes integrable: "\<And>a' b . a \<le> a' \<Longrightarrow> a' \<le> b \<Longrightarrow> 
                         (\<lambda>t. pbernpoly n t *\<^sub>R f t) integrable_on {a'..b}"
  assumes conv: "convergent (\<lambda>y. G (real y))"
  assumes bound: "eventually (\<lambda>x. norm (f x) \<le> g x) at_top"
  shows   "filterlim (\<lambda>b. EM_remainder' n f a b) 
             (nhds (EM_remainder n f a)) sequentially"
proof -
  have "uniform_limit {()} (\<lambda>b s. EM_remainder' n f a b) 
             (\<lambda>s. EM_remainder n f a) sequentially"
    using assms by (intro uniform_limit_EM_remainder[where G = G and g = g]) auto
  moreover have "() \<in> {()}" by simp
  ultimately show ?thesis by (rule tendsto_uniform_limitI)
qed

lemma EM_remainder_0 [simp]: "EM_remainder n (\<lambda>x. 0) a = 0"
  by (rule EM_remainder_eqI) (simp add: EM_remainder'_def)

lemma holomorphic_EM_remainder':
  assumes deriv: 
    "\<And>z t. z \<in> U \<Longrightarrow> t \<in> {a..x} \<Longrightarrow> 
       ((\<lambda>z. f z t) has_field_derivative f' z t) (at z within U)"
  assumes int: "\<And>b c z e. a \<le> b \<Longrightarrow> c \<le> x \<Longrightarrow> z \<in> U \<Longrightarrow>
                  (\<lambda>t. of_real (bernpoly n (t - e)) * f z t) integrable_on {b..c}"
  assumes cont: "continuous_on (U \<times> {a..x}) (\<lambda>(z, t). f' z t)"
  assumes "convex U"
  shows "(\<lambda>s. EM_remainder' n (f s) a x) holomorphic_on U"
  unfolding EM_remainder'_def scaleR_conv_of_real
proof (intro holomorphic_intros)
  have holo: "(\<lambda>z. integral (cbox b c) (\<lambda>t. of_real (bernpoly n (t - e)) * f z t)) holomorphic_on U"
    if "b \<ge> a" "c \<le> x" for b c e :: real
  proof (rule leibniz_rule_holomorphic)
    fix z t assume "z \<in> U" "t \<in> cbox b c"
    thus "((\<lambda>z. complex_of_real (bernpoly n (t - e)) * f z t) has_field_derivative
             complex_of_real (bernpoly n (t - e)) * f' z t) (at z within U)"
      using that by (intro DERIV_cmult deriv) auto
  next
    fix z assume "z \<in> U"
    thus "(\<lambda>t. complex_of_real (bernpoly n (t - e)) * f z t) integrable_on cbox b c"
      using that int[of b c z] by auto
  next
    have "continuous_on (U \<times> {b..c}) (\<lambda>(z, t). f' z t)"
      using cont by (rule continuous_on_subset) (insert that, auto)
    thus "continuous_on (U \<times> cbox b c) (\<lambda>(z, t).
            complex_of_real (bernpoly n (t - e)) * f' z t)"
      by (auto simp: case_prod_unfold intro!: continuous_intros)
  qed fact+

  consider "a > x" | "a \<le> x" "floor x \<le> a" | "a \<le> x" "floor x > a" by force
  hence "(\<lambda>z. integral (cbox a x) (\<lambda>t. of_real (pbernpoly n t) * f z t)) holomorphic_on U"
    (is "?f a x holomorphic_on _")
  proof cases
    case 2
    have "(\<lambda>z. integral (cbox a x) (\<lambda>t. of_real (bernpoly n (t - of_int \<lfloor>x\<rfloor>)) * f z t))
                   holomorphic_on U" 
      by (intro holo) auto
    also have "(\<lambda>z. integral (cbox a x) (\<lambda>t. of_real (bernpoly n (t - of_int \<lfloor>x\<rfloor>)) * f z t)) = ?f a x"
    proof (intro ext integral_cong, goal_cases)
      case (1 z t)
      hence "t \<ge> a" "t \<le> x" by auto
      hence "floor t = floor x" using 2 by linarith
      thus ?case by (simp add: pbernpoly_def frac_def)
    qed
    finally show ?thesis .
  next
    case 3
          define N :: "int set" where "N = {\<lceil>a\<rceil>..<\<lfloor>x\<rfloor>}"
    define A where "A = insert {a..of_int \<lceil>a\<rceil>} (insert {of_int \<lfloor>x\<rfloor>..x} 
                          ((\<lambda>n. {of_int n..of_int n + 1}) ` N))"
    {
      fix X assume "X \<in> A"
      then consider "X = {a..of_int \<lceil>a\<rceil>}" | "X = {of_int \<lfloor>x\<rfloor>..x}" |
             n where "X = {of_int n..of_int n + 1}" "n \<in> N" by (auto simp: A_def)
    } note A_cases = this

    have division: "A division_of {a..x}"
    proof (rule division_ofI)
      show "finite A" by (auto simp: A_def N_def)
      fix K assume K: "K \<in> A"
      from 3 have "of_int \<lceil>a\<rceil> \<le> x" 
        using ceiling_le[of a "floor x"] by linarith
      moreover from 3 have "of_int \<lfloor>x\<rfloor> \<ge> a" by linarith
      ultimately show "K \<subseteq> {a..x}" using K 3 by (auto simp: A_def N_def) linarith+
      from K show "K \<noteq> {}" and "\<exists>a b. K = cbox a b" by (auto simp: A_def)
    next
      fix K1 K2 assume K: "K1 \<in> A" "K2 \<in> A" "K1 \<noteq> K2"
      have F1: "interior {a..\<lceil>a\<rceil>} \<inter> interior {\<lfloor>x\<rfloor>..x} = {}" using 3 ceiling_le[of a "floor x"]
        by (auto simp: min_def max_def) 
      hence F2: "interior {\<lfloor>x\<rfloor>..x} \<inter> interior {a..\<lceil>a\<rceil>} = {}" by simp
      have F3: "interior {a..\<lceil>a\<rceil>} \<inter> interior {of_int n..of_int n+1} = {}"
               "interior {\<lfloor>x\<rfloor>..x} \<inter> interior {of_int n..of_int n+1} = {}"
               "interior {of_int n..of_int n+1} \<inter> interior {a..\<lceil>a\<rceil>} = {}"
               "interior {of_int n..of_int n+1} \<inter> interior {\<lfloor>x\<rfloor>..x} = {}"if "n \<in> N" for n
        using 3 ceiling_le[of a "floor x"] that by (auto simp: min_def max_def N_def)
      have F4: "interior {real_of_int n..of_int n+1} \<inter> interior {of_int m..of_int m+1} = {}"
        if "{real_of_int n..of_int n+1} \<noteq> {of_int m..of_int m+1}" for m n
      proof -
        from that have "n \<noteq> m" by auto
        thus ?thesis by simp
      qed
      from F1 F2 F3 F4 K show "interior K1 \<inter> interior K2 = {}"
        by (elim A_cases) (simp_all only: not_False_eq_True)
    next
      show "\<Union>A = {a..x}"
      proof (cases "\<lceil>a\<rceil> = \<lfloor>x\<rfloor>")
        case True
        thus ?thesis using 3 by (auto simp: A_def N_def intro: order.trans) linarith+
      next
        case False
        with 3 have *: "\<lceil>a\<rceil> < \<lfloor>x\<rfloor>" by linarith
        have "\<Union>A = {a..of_int \<lceil>a\<rceil>} \<union> (\<Union>n\<in>N. {of_int n..of_int (n + 1)}) \<union> {of_int \<lfloor>x\<rfloor>..x}"
          by (simp add: A_def Un_ac)
        also have "(\<Union>n\<in>N. {of_int n..of_int (n + 1)}) = {of_int \<lceil>a\<rceil>..real_of_int \<lfloor>x\<rfloor>}"
          using * unfolding N_def by (intro Union_atLeastAtMost_real_of_int)
        also have "{a..of_int \<lceil>a\<rceil>} \<union> \<dots> = {a..real_of_int \<lfloor>x\<rfloor>}"
          using 3 * by (intro ivl_disj_un) auto
        also have "\<dots> \<union> {of_int \<lfloor>x\<rfloor>..x} = {a..x}"
          using 3 * by (intro ivl_disj_un) auto
        finally show ?thesis .
      qed
    qed


    have "(\<lambda>z. \<Sum>X\<in>A. integral X (\<lambda>t. of_real (bernpoly n (t - \<lfloor>Inf X\<rfloor>)) * f z t)) 
            holomorphic_on U"
    proof (intro holomorphic_on_sum holo, goal_cases)
      case (1 X)
      from 1 and division have subset: "X \<subseteq> {a..x}" by (auto simp: division_of_def)
      from 1 obtain b c where [simp]: "X = cbox b c" "b \<le> c" by (auto simp: A_def)
      from subset have "b \<ge> a" "c \<le> x" by auto
      hence "(\<lambda>x. integral (cbox b c) (\<lambda>t. of_real (bernpoly n (t - \<lfloor>Inf {b..c}\<rfloor>)) * f x t)) 
               holomorphic_on U" by (intro holo) auto
      thus ?case by simp
    qed
    also have "?this \<longleftrightarrow> (\<lambda>z. integral {a..x} (\<lambda>t. of_real (pbernpoly n t) * f z t)) 
                           holomorphic_on U"
    proof (intro holomorphic_cong refl, goal_cases)
      case (1 z)
      have "((\<lambda>t. of_real (pbernpoly n t) * f z t) has_integral
              (\<Sum>X\<in>A. integral X (\<lambda>t. of_real (bernpoly n (t - \<lfloor>Inf X\<rfloor>)) * f z t))) {a..x}"
        using division
      proof (rule has_integral_combine_division)
        fix X assume X: "X \<in> A"
        then obtain b c where X': "X = {b..c}" "b \<le> c" by (elim A_cases) auto
        from X and division have "X \<subseteq> {a..x}" by (auto simp: division_of_def)
        with X' have bc: "b \<ge> a" "c \<le> x" by auto
        have "((\<lambda>t. of_real (bernpoly n (t - of_int \<lfloor>Inf X\<rfloor>)) * f z t) has_integral
                 integral X (\<lambda>t. of_real (bernpoly n (t - of_int \<lfloor>Inf X\<rfloor>)) * f z t)) X"
          unfolding X' using \<open>z \<in> U\<close> bc by (intro integrable_integral int)
        also have "?this \<longleftrightarrow> ((\<lambda>t. of_real (pbernpoly n t) * f z t) has_integral
                 integral X (\<lambda>t. of_real (bernpoly n (t - of_int \<lfloor>Inf X\<rfloor>)) * f z t)) X"
        proof (rule has_integral_spike_eq[of "{Sup X}"], goal_cases)
          case (2 t)
          note t = this
          from \<open>X \<in> A\<close> have "\<lfloor>t\<rfloor> = \<lfloor>Inf X\<rfloor>"
          proof (cases rule: A_cases [consumes 1])
            case 1
            with t show ?thesis
              by (intro floor_unique) (auto simp: ceiling_altdef split: if_splits, (linarith+)?)
          next
            case 2
            with t show ?thesis
              by (intro floor_unique) (auto simp: ceiling_altdef split: if_splits, (linarith+)?)
          next
            case 3
            with t show ?thesis
              by (intro floor_unique) (auto simp: ceiling_altdef N_def split: if_splits)
          qed
          thus ?case by (simp add: pbernpoly_def frac_def)
        qed auto
        finally show \<dots> .
      qed
      thus ?case by (simp add: has_integral_iff)
    qed
    finally show ?thesis by simp
  qed auto
  thus "(\<lambda>z. integral {a..x} (\<lambda>t. of_real (pbernpoly n t) * f z t)) holomorphic_on U"
    by simp
qed

lemma
  assumes deriv: "\<And>y. a \<le> y \<Longrightarrow> (G has_real_derivative g y) (at y within {a..})"
  assumes deriv': 
    "\<And>z t x. z \<in> U \<Longrightarrow> x \<ge> a \<Longrightarrow> t \<in> {a..x} \<Longrightarrow> 
       ((\<lambda>z. f z t) has_field_derivative f' z t) (at z within U)"
  assumes cont: "continuous_on (U \<times> {of_int a..}) (\<lambda>(z, t). f' z t)"
  assumes int: "\<And>b c z e. a \<le> b \<Longrightarrow> z \<in> U \<Longrightarrow>
                  (\<lambda>t. of_real (bernpoly n (t - e)) * f z t) integrable_on {b..c}"
  assumes int': "\<And>a' b y. y \<in> U \<Longrightarrow>  a \<le> a' \<Longrightarrow> a' \<le> b \<Longrightarrow> 
                         (\<lambda>t. pbernpoly n t *\<^sub>R f y t) integrable_on {a'..b}"
  assumes conv: "convergent (\<lambda>y. G (real y))"
  assumes bound: "eventually (\<lambda>x. \<forall>y\<in>U. norm (f y x) \<le> g x) at_top"
  assumes "open U" 
  shows analytic_EM_remainder: "(\<lambda>s::complex. EM_remainder n (f s) a) analytic_on U"
    and holomorphic_EM_remainder: "(\<lambda>s::complex. EM_remainder n (f s) a) holomorphic_on U"
proof -
  show "(\<lambda>s::complex. EM_remainder n (f s) a) analytic_on U"
  unfolding analytic_on_def
  proof
    fix z assume "z \<in> U"
    from \<open>z \<in> U\<close> and \<open>open U\<close> obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "ball z \<epsilon> \<subseteq> U"
      by (auto simp: open_contains_ball)
    have "(\<lambda>s. EM_remainder n (f s) a) holomorphic_on ball z \<epsilon>"
    proof (rule holomorphic_uniform_sequence)
      fix x :: nat
      show "(\<lambda>s. EM_remainder' n (f s) a x) holomorphic_on ball z \<epsilon>"
      proof (rule holomorphic_EM_remainder', goal_cases)
        fix s t assume "s \<in> ball z \<epsilon>" "t \<in> {real_of_int a..real x}"
        thus "((\<lambda>z. f z t) has_field_derivative f' s t) (at s within ball z \<epsilon>)"
          using \<epsilon> by (intro DERIV_subset[OF deriv'[of _ x]]) auto
      next
        case (2 b c s e)
        with \<epsilon> have "s \<in> U" by blast
        with 2 show ?case using \<epsilon> int[of b s e c] by (cases "a \<le> x") auto
      next
        from cont show "continuous_on (ball z \<epsilon> \<times> {real_of_int a..real x}) (\<lambda>(z, t). f' z t)"
          by (rule continuous_on_subset) (insert \<epsilon>, auto)
      qed (auto)
    next
      fix s assume s: "s \<in> ball z \<epsilon>"
      have "open (ball z \<epsilon>)" by simp
      with s obtain \<delta> where \<delta>: "\<delta> > 0" "cball s \<delta> \<subseteq> ball z \<epsilon>" 
        unfolding open_contains_cball by blast
      moreover have bound': "eventually (\<lambda>x. \<forall>y\<in>cball s \<delta>. norm (f y x) \<le> g x) at_top"
        by (intro eventually_mono [OF bound]) (insert \<delta> \<epsilon>, auto)
      have "uniform_limit (cball s \<delta>) (\<lambda>x s. EM_remainder' n (f s) (real_of_int a) (real x))
                        (\<lambda>s. EM_remainder n (f s) a) sequentially"
        by (rule uniform_limit_EM_remainder[OF deriv int' conv bound']) (insert \<delta> \<epsilon> s, auto)
      ultimately show "\<exists>\<delta>>0. cball s \<delta> \<subseteq> ball z \<epsilon> \<and> uniform_limit (cball s \<delta>)
                          (\<lambda>x s. EM_remainder' n (f s) (real_of_int a) (real x))
                          (\<lambda>s. EM_remainder n (f s) a) sequentially" by blast
    qed auto
    with \<epsilon> show "\<exists>\<epsilon>>0. (\<lambda>s. EM_remainder n (f s) a) holomorphic_on ball z \<epsilon>"
      by blast
  qed
  thus "(\<lambda>s::complex. EM_remainder n (f s) a) holomorphic_on U"
    by (rule analytic_imp_holomorphic)
qed



text \<open>
  The following lemma is the first step in the proof of the Euler--MacLaurin formula: 
  We show the relationship between the first-order remainder term and the difference of 
  the integral and the sum.
\<close>
  
context
  fixes f f' :: "real \<Rightarrow> 'a :: banach"
  fixes a b :: int and I S :: 'a
  fixes Y :: "real set"
  assumes "a \<le> b"
  assumes fin: "finite Y"
  assumes cont: "continuous_on {real_of_int a..real_of_int b} f"
  assumes deriv [derivative_intros]: 
            "\<And>x::real. x \<in> {a..b} - Y \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
  defines S_def: "S \<equiv> (\<Sum>i\<in>{a<..b}. f i)" and I_def: "I \<equiv> integral {a..b} f"
begin
  
lemma
  diff_sum_integral_has_integral_int:
    "((\<lambda>t. (frac t - 1/2) *\<^sub>R f' t) has_integral (S - I - (f b - f a) /\<^sub>R 2)) {a..b}"
proof (cases "a = b")
  case True
  thus ?thesis by (simp_all add: S_def I_def has_integral_refl)
next
  case False
  with \<open>a \<le> b\<close> have ab: "a < b" by simp
  let ?A = "(\<lambda>n. {real_of_int n..real_of_int (n+1)}) ` {a..<b}"
  have division: "?A division_of {of_int a..of_int b}"
    using Union_atLeastAtMost_real_of_int[OF ab] by (simp add: division_of_def)
  have cont' [continuous_intros]: "continuous_on A f" if "A \<subseteq> {of_int a..of_int b}" for A
    using continuous_on_subset[OF cont that] .
  
  define d where "d = (\<lambda>x. (f x + f (x + 1)) /\<^sub>R 2 - integral {x..x+1} f)"    
  have "((\<lambda>t. (frac t - 1/2) *\<^sub>R f' t) has_integral d i) {of_int i..of_int (i+1)}"
    if i: "i \<in> {a..<b}" for i
  proof (rule has_integral_spike)
    show "(frac x - 1 / 2) *\<^sub>R f' x = (x - of_int i - 1 / 2) *\<^sub>R f' x"
         if "x \<in> {of_int i..of_int (i + 1)} - {of_int (i + 1)}" for x
    proof -
      have "x \<ge> of_int i" "x < of_int (i + 1)" using that by auto
      hence "floor x = of_int i" by (subst floor_unique) auto
      thus ?thesis by (simp add: frac_def)
    qed
  next
    define h where "h = (\<lambda>x::real. (x - of_int i - 1 / 2) *\<^sub>R f' x)"
    define g where "g = (\<lambda>x::real. (x - of_int i - 1/2) *\<^sub>R f x - integral {of_int i..x} f)"
    have *: "((\<lambda>x. integral {real_of_int i..x} f) has_vector_derivative f x) (at x within {i..i+1})"
      if "x \<in> {of_int i<..<of_int i + 1}" for x using that i
      by (intro integral_has_vector_derivative cont') auto
    have "((\<lambda>x. integral {real_of_int i..x} f) has_vector_derivative f x) (at x)" 
      if "x \<in> {of_int i<..<of_int i + 1}" for x 
      using that i at_within_interior[of x "{of_int i..of_int (i + 1)}"] *[of x] by simp
    hence "(h has_integral g (of_int (i + 1)) - g (of_int i)) {of_int i..of_int (i+1)}"
      unfolding g_def h_def using that 
      by (intro fundamental_theorem_of_calculus_interior_strong[OF fin])
         (auto intro!: derivative_eq_intros continuous_intros indefinite_integral_continuous_1
             integrable_continuous_real)
    also have "g (of_int (i + 1)) - g (of_int i) = d i"
      by (simp add: g_def scaleR_add_right [symmetric] d_def)
    finally show "(h has_integral d i) {of_int i..of_int (i + 1)}" .
  qed simp_all
  hence *: "\<And>I. I\<in>?A \<Longrightarrow> ((\<lambda>x. (frac x - 1 / 2) *\<^sub>R f' x) has_integral d (\<lfloor>Inf I\<rfloor>)) I"
    by (auto simp: add_ac)
  have "((\<lambda>x::real. (frac x - 1 / 2) *\<^sub>R f' x) has_integral (\<Sum>I\<in>?A. d (\<lfloor>Inf I\<rfloor>))) (\<Union>?A)"
    by (intro has_integral_Union * finite_imageI) (force intro!: negligible_atLeastAtMostI pairwiseI)+
  also have "\<Union>?A = {of_int a..of_int b}"
    by (intro Union_atLeastAtMost_real_of_int ab)
  also have "(\<Sum>I\<in>?A. d (\<lfloor>Inf I\<rfloor>)) = (\<Sum>i=a..<b. d i)"
    by (subst sum.reindex) (auto simp: inj_on_def)
  also have "\<dots> = (1 / 2) *\<^sub>R ((\<Sum>i = a..<b. f (real_of_int i)) +
                    (\<Sum>i = a..<b. f (real_of_int (i + 1)))) -
                  (\<Sum>i = a..<b. integral {real_of_int i..1 + real_of_int i} f)"
    (is "_ = _ *\<^sub>R (?S1 + ?S2) - ?S3") 
    by (simp add: d_def algebra_simps sum.distrib sum_subtractf scaleR_sum_right)
  also have "?S1 = (\<Sum>i = a..b. f (real_of_int i)) - f b"
    unfolding S_def using ab by (subst sum_atLeastAtMost_int_last) auto
  also have "(\<Sum>i = a..b. f (real_of_int i)) = S + f a"
    unfolding S_def using ab by (subst sum_atLeastAtMost_int_head) auto
  also have "?S2 = S" unfolding S_def
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i-1" "\<lambda>i. i+1"]) auto
  also have "(1 / 2) *\<^sub>R (S + f a - f b + S) = 
                (1/2) *\<^sub>R S + (1/2) *\<^sub>R S - (f b - f a) /\<^sub>R 2"
    by (simp add: algebra_simps)
  also have "(1/2) *\<^sub>R S + (1/2) *\<^sub>R S = S" by (simp add: scaleR_add_right [symmetric])
      
  also have "?S3 = (\<Sum>I\<in>?A. integral I f)"
    by (subst sum.reindex) (auto simp: inj_on_def add_ac)
  also have "\<dots> = I" unfolding I_def
    by (intro integral_combine_division_topdown [symmetric] division integrable_continuous_real 
              continuous_intros) simp_all
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma diff_sum_integral_has_integral_int':
  "((\<lambda>t. pbernpoly 1 t *\<^sub>R f' t) has_integral (S - I - (f b - f a) /\<^sub>R 2 )) {a..b}"
  using diff_sum_integral_has_integral_int by (simp add: pbernpoly_def bernpoly_def)
  
lemma EM_remainder'_Suc_0: "EM_remainder' (Suc 0) f' a b = S - I - (f b - f a) /\<^sub>R 2"
  using diff_sum_integral_has_integral_int' by (simp add: has_integral_iff EM_remainder'_def)

end


text \<open>
  Next, we show that the $n$-th-order remainder can be expressed in terms of the $n+1$-th-order 
  remainder term. Iterating this essentially yields the Euler--MacLaurin formula.
\<close>

context
  fixes f f' :: "real \<Rightarrow> 'a :: banach" and a b :: int and n :: nat and A :: "real set"
  assumes ab: "a \<le> b" and n: "n > 0"
  assumes fin:   "finite A"
  assumes cont:  "continuous_on {of_int a..of_int b} f"
  assumes cont': "continuous_on {of_int a..of_int b} f'"
  assumes deriv: "\<And>x. x \<in> {of_int a<..<of_int b} - A \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
begin
  
lemma EM_remainder'_integral_conv_Suc:
  shows   "integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t) =
              (bernoulli (Suc n) / real (Suc n)) *\<^sub>R (f b - f a) -
              integral {a..b} (\<lambda>t. pbernpoly (Suc n) t *\<^sub>R f' t) /\<^sub>R real (Suc n)"
  unfolding EM_remainder'_def
proof -
  let ?h = "\<lambda>i. (pbernpoly (Suc n) (real_of_int i) / real (Suc n)) *\<^sub>R f (real_of_int i)"
  define T where "T = integral {a..b} (\<lambda>t. (pbernpoly (Suc n) t / real (Suc n)) *\<^sub>R f' t)"
  note [derivative_intros] = has_field_derivative_pbernpoly_Suc'
  let ?A = "real_of_int ` {a..b} \<union> A"
    
  have "((\<lambda>t. pbernpoly n t *\<^sub>R f t) has_integral (-T + (?h b - ?h a))) {a..b}"
  proof (rule integration_by_parts_interior_strong[OF bounded_bilinear_scaleR])
    from fin show "finite ?A" by simp
    from \<open>n > 0\<close> show "continuous_on {of_int a..of_int b} (\<lambda>t. pbernpoly (Suc n) t / real (Suc n))"
      by (intro continuous_intros) auto
    show "continuous_on {of_int a..of_int b} f" by fact
    show "(f has_vector_derivative f' t) (at t)" if "t \<in> {of_int a<..<of_int b} - ?A" for t
      using deriv[of t] that by auto
    have "(\<lambda>t. pbernpoly (Suc n) t *\<^sub>R f' t) integrable_on {a..b}"
      by (intro integrable_EM_remainder' cont')
    hence "(\<lambda>t. (1 / real (Suc n)) *\<^sub>R pbernpoly (Suc n) t *\<^sub>R f' t) integrable_on {a..b}" 
      by (rule integrable_cmul)
    also have "(\<lambda>t. (1 / real (Suc n)) *\<^sub>R pbernpoly (Suc n) t *\<^sub>R f' t) =
                 (\<lambda>t. (pbernpoly (Suc n) t / real (Suc n)) *\<^sub>R f' t)"
      by (rule ext) (simp add: algebra_simps)
    finally show "((\<lambda>t. (pbernpoly (Suc n) t / real (Suc n)) *\<^sub>R f' t) 
                    has_integral ?h b - ?h a - (- T + (?h b - ?h a))) {a..b}"
      using integrable_EM_remainder'[of a b f' "Suc n"]
        by (simp add: has_integral_iff T_def)
    qed (insert ab n, auto intro!: derivative_eq_intros
           simp: has_field_derivative_iff_has_vector_derivative [symmetric] not_le elim!: Ints_cases)
    also have "?h b - ?h a = (bernoulli (Suc n) / real (Suc n)) *\<^sub>R (f b - f a)"
      using n by (simp add: algebra_simps bernoulli'_def)
    finally have "integral {a..b} (\<lambda>t. pbernpoly n t *\<^sub>R f t) = \<dots> - T"
      by (simp add: has_integral_iff)
    also have "T = integral {a..b} (\<lambda>t. (1 / real (Suc n)) *\<^sub>R (pbernpoly (Suc n) t) *\<^sub>R f' t)"
      by (simp add: T_def)
    also have "\<dots> = integral {a..b} (\<lambda>t. pbernpoly (Suc n) t *\<^sub>R f' t) /\<^sub>R real (Suc n)"
      by (subst integral_cmul) (simp_all add: divide_simps)
    finally show ?thesis .
qed 

lemma EM_remainder'_conv_Suc: 
  "EM_remainder' n f a b = 
     ((-1) ^ Suc n * bernoulli (Suc n) / fact (Suc n)) *\<^sub>R (f b - f a) + 
     EM_remainder' (Suc n) f' a b"
  by (simp add: EM_remainder'_def EM_remainder'_integral_conv_Suc scaleR_diff_right 
                scaleR_add_right field_simps del: of_nat_Suc)

end

context
  fixes f f' :: "real \<Rightarrow> 'a :: banach" and a :: int and n :: nat and A :: "real set" and C
  assumes n: "n > 0"
  assumes fin:   "finite A"
  assumes cont:  "continuous_on {of_int a..} f"
  assumes cont': "continuous_on {of_int a..} f'"
  assumes lim:   "(f \<longlongrightarrow> C) at_top"
  assumes deriv: "\<And>x. x \<in> {of_int a<..} - A \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
begin  
  
lemma
  shows EM_remainder_converges_iff_Suc_converges:
          "EM_remainder_converges n f a \<longleftrightarrow> EM_remainder_converges (Suc n) f' a"
  and   EM_remainder_conv_Suc: 
           "EM_remainder_converges n f a \<Longrightarrow> 
              EM_remainder n f a = 
                  ((-1) ^ Suc n * bernoulli (Suc n) / fact (Suc n)) *\<^sub>R (C - f a) + 
                  EM_remainder (Suc n) f' a"
proof (rule iffI)
  define g where "g = (\<lambda>x. ((-1) ^ Suc n * bernoulli (Suc n) / fact (Suc n)) *\<^sub>R (f x - f a))"
  define G where "G = ((-1) ^ Suc n * bernoulli (Suc n) / fact (Suc n)) *\<^sub>R (C - f a)"
  have limit_g: "(g \<longlongrightarrow> G) at_top" unfolding g_def G_def by (intro tendsto_intros lim)
  have *: "eventually (\<lambda>x. EM_remainder' n f (real_of_int a) (real_of_int x) = 
              g x + EM_remainder' (Suc n) f' (real_of_int a) (real_of_int x)) at_top"
    using eventually_ge_at_top[of a]
  proof eventually_elim
    case (elim b)
    thus ?case
    using EM_remainder'_conv_Suc[OF elim n fin continuous_on_subset[OF cont] 
            continuous_on_subset[OF cont'] deriv] by (auto simp: g_def)
  qed
  
  {
    assume "EM_remainder_converges n f a"
    then obtain L
      where L: "((\<lambda>b. EM_remainder' n f (real_of_int a) (real_of_int b)) \<longlongrightarrow> L) at_top"
      by (auto simp: EM_remainder_converges_def)
    have *: "((\<lambda>b. EM_remainder' (Suc n) f' (real_of_int a) (real_of_int b)) \<longlongrightarrow> L - G) at_top"
    proof (rule Lim_transform_eventually)
      show "\<forall>\<^sub>F x in at_top. EM_remainder' n f (real_of_int a) (real_of_int x) - g x =
               EM_remainder' (Suc n) f' (real_of_int a) (real_of_int x)"
        using * by (simp add: algebra_simps)
      show "((\<lambda>x. EM_remainder' n f (real_of_int a) (real_of_int x) - g x) \<longlongrightarrow> L - G) at_top"
        by (intro tendsto_intros filterlim_compose[OF limit_g] L)
    qed
    from * show "EM_remainder_converges (Suc n) f' a" unfolding EM_remainder_converges_def ..
    from * have "EM_remainder (Suc n) f' a = L - G" by (rule EM_remainder_eqI)
    moreover from L have "EM_remainder n f a = L" by (rule EM_remainder_eqI)
    ultimately show "EM_remainder n f a = G + EM_remainder (Suc n) f' a" by (simp add: G_def)
  }
  {
    assume "EM_remainder_converges (Suc n) f' a" 
    then obtain L
      where L: "((\<lambda>b. EM_remainder' (Suc n) f' (real_of_int a) (real_of_int b)) \<longlongrightarrow> L) at_top"
      by (auto simp: EM_remainder_converges_def)
    have *: "((\<lambda>b. EM_remainder' n f (real_of_int a) (real_of_int b)) \<longlongrightarrow> G + L) at_top"
    proof (rule Lim_transform_eventually)
      show "\<forall>\<^sub>F x in at_top. g x + EM_remainder' (Suc n) f' (real_of_int a) (real_of_int x) =
                EM_remainder' n f (real_of_int a) (real_of_int x)"
        using * by (subst eq_commute)
      show "((\<lambda>x. g x + EM_remainder' (Suc n) f' (real_of_int a) (real_of_int x)) \<longlongrightarrow> G + L) at_top"
        by (intro tendsto_intros filterlim_compose[OF limit_g] L)
    qed
    thus "EM_remainder_converges n f a" unfolding EM_remainder_converges_def ..
  }
qed

end
  


subsection \<open>The conventional version of the Euler--MacLaurin formula\<close>

text \<open>
  The following theorems are the classic Euler--MacLaurin formula that can be found,
  with slight variations, in many sources (e.\,g.\ \cite{AS_HMF, apostol99, GKP_CM}).
\<close>

context
  fixes f :: "real \<Rightarrow> 'a :: banach"
  fixes fs :: "nat \<Rightarrow> real \<Rightarrow> 'a"
  fixes a b :: int assumes ab: "a \<le> b"
  fixes N :: nat assumes N: "N > 0"
  fixes Y :: "real set" assumes fin: "finite Y"
  assumes fs_0 [simp]: "fs 0 = f"
  assumes fs_cont [continuous_intros]:  
    "\<And>k. k \<le> N \<Longrightarrow> continuous_on {real_of_int a..real_of_int b} (fs k)"
  assumes fs_deriv [derivative_intros]: 
    "\<And>k x. k < N \<Longrightarrow> x \<in> {a..b} - Y \<Longrightarrow> (fs k has_vector_derivative fs (Suc k) x) (at x)"
begin

theorem euler_maclaurin_raw_strong_int:
  defines "S \<equiv> (\<Sum>i\<in>{a<..b}. f (of_int i))"
  defines "I \<equiv> integral {of_int a..of_int b} f"
  defines "c' \<equiv> \<lambda>k. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k b - fs k a)"
  shows   "S - I = (\<Sum>k<N. c' k) + EM_remainder' N (fs N) a b"
proof -
  define c :: "nat \<Rightarrow> 'a" 
    where "c = (\<lambda>k. ((-1) ^ (Suc k) * bernoulli (Suc k) / fact (Suc k)) *\<^sub>R (fs k b - fs k a))"
  have "S - I = (\<Sum>k<m. c k) + EM_remainder' m (fs m) a b" if "m \<ge> 1" "m \<le> N" for m
  using that
  proof (induction m rule: dec_induct)
    case base
    with ab fin fs_cont[of 0] show ?case using fs_deriv[of 0] N unfolding One_nat_def
      by (subst EM_remainder'_Suc_0[of _ _ Y f]) (simp_all add: algebra_simps S_def I_def c_def)
  next
    case (step n)
    from step.prems have "S - I = (\<Sum>k<n. c k) + EM_remainder' n (fs n) a b"
      by (intro step.IH) simp_all
    also have "(\<Sum>k<n. c k) = (\<Sum>k<Suc n. c k) +
                  (((-1) ^ n * bernoulli (Suc n) / fact (Suc n)) *\<^sub>R (fs n b - fs n a))"
      (is "_ = _ + ?c") by (simp add: EM_remainder'_Suc_0 c_def)
    also have "\<dots> + EM_remainder' n (fs n) a b = (\<Sum>k<Suc n. c k) + (?c + EM_remainder' n (fs n) a b)"
      by (simp add: add.assoc)
    also from step.prems step.hyps ab fin
      have "?c + EM_remainder' n (fs n) a b = EM_remainder' (Suc n) (fs (Suc n)) a b"
      by (subst EM_remainder'_conv_Suc [where A = Y]) 
         (auto intro!: fs_deriv fs_cont)
    finally show ?case .
  qed
  from this[of N] and N 
    have "S - I = sum c {..<N} + EM_remainder' N (fs N) (real_of_int a) (real_of_int b)" by simp
  also have "sum c {..<N} = sum c' {..<N}"
  proof (intro sum.cong refl)
    fix k :: nat
    show "c k = c' k"
      by (cases "even k")
         (auto simp: c_def c'_def bernoulli'_def algebra_simps bernoulli_odd_eq_0)
  qed
  finally show ?thesis .
qed

end

theorem euler_maclaurin_strong_raw_nat:
  assumes "a \<le> b" "0 < N" "finite Y" "fs 0 = f"
    "(\<And>k. k \<le> N \<Longrightarrow> continuous_on {real a..real b} (fs k))"
    "(\<And>k x. k < N \<Longrightarrow> x \<in> {real a..real b} - Y \<Longrightarrow>
       (fs k has_vector_derivative fs (Suc k) x) (at x))"
  shows "(\<Sum>i\<in>{a<..b}. f (real i)) - integral {real a..real b} f =
           (\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k (real b) - fs k (real a))) +
           EM_remainder' N (fs N) (real a) (real b)"
proof -
  have "(\<Sum>i\<in>{int a<..int b}. f (real_of_int i)) - 
           integral {real_of_int (int a)..real_of_int (int b)} f =
           (\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R 
             (fs k (real_of_int (int b)) - fs k (real_of_int (int a)))) +
           EM_remainder' N (fs N) (real_of_int (int a)) (real_of_int (int b))"
    using assms by (intro euler_maclaurin_raw_strong_int[where Y = Y] assms) simp_all
  also have "(\<Sum>i\<in>{int a<..int b}. f (real_of_int i)) = (\<Sum>i\<in>{a<..b}. f (real i))"
    by (intro sum.reindex_bij_witness[of _ int nat]) auto
  finally show ?thesis by simp
qed

  
subsection \<open>The ``Concrete Mathematics'' version of the Euler--MacLaurin formula\<close>

text \<open>
  As explained in \textit{Concrete Mathematics}~\cite{GKP_CM}, the above form of the 
  formula has some drawbacks: When applying it to determine the asymptotics of some concrete 
  function, one is usually left with several different unwieldy constant terms that are difficult 
  to get rid of.

  There is no general way to determine what these constant terms are, but in concrete applications, 
  they can often be determined or estimated by other means. We can therefore simply group all the 
  constant terms into a single constant and have the user provide a proof of what it is.
\<close>

locale euler_maclaurin_int =
  fixes F f :: "real \<Rightarrow> 'a :: banach"
  fixes fs :: "nat \<Rightarrow> real \<Rightarrow> 'a"
  fixes a :: int
  fixes N :: nat assumes N: "N > 0"
  fixes C :: 'a
  fixes Y :: "real set" assumes fin: "finite Y"
  assumes fs_0 [simp]: "fs 0 = f"
  assumes fs_cont [continuous_intros]:  
    "\<And>k. k \<le> N \<Longrightarrow> continuous_on {real_of_int a..} (fs k)"
  assumes fs_deriv [derivative_intros]: 
    "\<And>k x. k < N \<Longrightarrow> x \<in> {of_int a..} - Y \<Longrightarrow> (fs k has_vector_derivative fs (Suc k) x) (at x)"
  assumes F_cont [continuous_intros]: "continuous_on {of_int a..} F"
  assumes F_deriv [derivative_intros]: 
    "\<And>x. x \<in> {of_int a..} - Y \<Longrightarrow> (F has_vector_derivative f x) (at x)" 
  assumes limit: 
    "((\<lambda>b. (\<Sum>k=a..b. f k) - F (of_int b) - 
         (\<Sum>i<N. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b))) \<longlongrightarrow> C) at_top"
begin

context
  fixes C' T
  defines "C' \<equiv> -f a + F a + C + (\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k (of_int a)))"
      and "T \<equiv> (\<lambda>x. \<Sum>i<N. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i x)"
begin
  
lemma euler_maclaurin_strong_int_aux:
  assumes ab: "a \<le> b"
  defines "S \<equiv> (\<Sum>k=a..b. f (of_int k))"
  shows "S - F (of_int b) - T (of_int b) = EM_remainder' N (fs N) (of_int a) (of_int b) + (C - C')"
proof (cases "a = b")
  case True
  thus ?thesis unfolding C'_def by (simp add: S_def EM_remainder'_def T_def)
next
  case False
  with assms have ab: "a < b" by simp
  define T' where "T' = (\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k (of_int a)))"
  have "(\<Sum>i\<in>{a<..b}. f (of_int i)) - integral {of_int a..of_int b} f =
          (\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k (of_int b) - fs k (of_int a))) +
          EM_remainder' N (fs N) (of_int a) (of_int b)" using ab
    by (intro euler_maclaurin_raw_strong_int [where Y = Y] N fin fs_0
              continuous_on_subset[OF fs_cont] fs_deriv) auto
  also have "(f has_integral (F b - F a)) {of_int a..of_int b}" using ab
    by (intro fundamental_theorem_of_calculus_strong[OF fin])
       (auto intro!: continuous_on_subset[OF F_cont] derivative_intros)
  hence "integral {of_int a..of_int b} f = F (of_int b) - F (of_int a)"
    by (simp add: has_integral_iff)
  also have "(\<Sum>k<N. (bernoulli' (Suc k) / fact (Suc k)) *\<^sub>R (fs k (of_int b) - fs k (of_int a))) =
               T (of_int b) - T'"
    by (simp add: T_def T'_def algebra_simps sum_subtractf)
  also have "(\<Sum>i\<in>{a<..b}. f (of_int i)) = S - f (of_int a)"
    unfolding S_def using ab by (subst sum_atLeastAtMost_int_head) auto
  finally show ?thesis by (simp add: algebra_simps C'_def T'_def)  
qed

lemma EM_remainder_limit:
  assumes ab: "a \<le> b"
  defines "D \<equiv> EM_remainder' N (fs N) (of_int a) (of_int b)"
  shows "EM_remainder N (fs N) b = C' - D"
    and EM_remainder_converges: "EM_remainder_converges N (fs N) b"
proof -
  note limit
  also have "((\<lambda>b. (\<Sum>k = a..b. f (of_int k)) - F (of_int b) -
               (\<Sum>i<N. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b))) \<longlongrightarrow> C) at_top =
             ((\<lambda>b. (\<Sum>k = a..b. f (of_int k)) - F (of_int b) - T (of_int b)) \<longlongrightarrow> C) at_top"
    unfolding T_def ..
  also have "eventually (\<lambda>x. (\<Sum>k=a..x. f k) - F (of_int x) - T (of_int x) = 
               EM_remainder' N (fs N) (of_int a) (of_int x) + (C - C')) at_top"
    (is "eventually (\<lambda>x. ?f x = ?g x) _")
    using eventually_gt_at_top[of b]
    by eventually_elim (rule euler_maclaurin_strong_int_aux, insert ab, simp_all)
  hence "(?f \<longlongrightarrow> C) at_top \<longleftrightarrow> (?g \<longlongrightarrow> C) at_top" by (intro filterlim_cong refl)
  finally have "((\<lambda>x. ?g x - (C - C')) \<longlongrightarrow> (C - (C - C'))) at_top"
    by (rule tendsto_diff[OF _ tendsto_const])
  hence *: "((\<lambda>x. EM_remainder' N (fs N) (of_int a) (of_int x)) \<longlongrightarrow> C') at_top"
    by simp
  
  have "((\<lambda>x. EM_remainder' N (fs N) (of_int a) (of_int x) - D) \<longlongrightarrow> C' - D) at_top"
    by (intro tendsto_intros *)
  also have "eventually (\<lambda>x. EM_remainder' N (fs N) (of_int a) (of_int x) - D = 
                          EM_remainder' N (fs N) (of_int b) (of_int x)) at_top" 
    (is "eventually (\<lambda>x. ?f x = ?g x) _") using eventually_ge_at_top[of b]
  proof eventually_elim
    case (elim x)
    have "EM_remainder' N (fs N) (of_int a) (of_int x) = 
            D + EM_remainder' N (fs N) (of_int b) (of_int x)" 
      using elim ab unfolding D_def
      by (intro EM_remainder'_combine [symmetric] continuous_on_subset[OF fs_cont]) auto
    thus ?case by simp
  qed
  hence "(?f \<longlongrightarrow> C' - D) at_top \<longleftrightarrow> (?g \<longlongrightarrow> C' - D) at_top" by (intro filterlim_cong refl)
  finally have *: \<dots> .
  from * show "EM_remainder_converges N (fs N) b" unfolding EM_remainder_converges_def ..
  from * show "EM_remainder N (fs N) b = C' - D"
    by (rule EM_remainder_eqI)
qed

theorem euler_maclaurin_strong_int:
  assumes ab: "a \<le> b"
  defines "S \<equiv> (\<Sum>k=a..b. f (of_int k))"
  shows "S = F (of_int b) + C + T (of_int b) - EM_remainder N (fs N) b"
proof -
  have "S = F (of_int b) + T (of_int b) + - (C' - EM_remainder' N (fs N) (of_int a) (of_int b)) + C"
    using euler_maclaurin_strong_int_aux[OF ab] by (simp add: algebra_simps S_def)
  also have "C' - EM_remainder' N (fs N) (of_int a) (of_int b) = EM_remainder N (fs N) b"
    using ab by (rule EM_remainder_limit(1) [symmetric])
  finally show ?thesis by simp
qed
  
end
end


text \<open>
  The following version of the formula removes all the terms where the associated
  Bernoulli numbers vanish. 
\<close>

locale euler_maclaurin_int' =
  fixes F f :: "real \<Rightarrow> 'a :: banach"
  fixes fs :: "nat \<Rightarrow> real \<Rightarrow> 'a"
  fixes a :: int
  fixes N :: nat
  fixes C :: 'a
  fixes Y :: "real set" assumes fin: "finite Y"
  assumes fs_0 [simp]: "fs 0 = f"
  assumes fs_cont [continuous_intros]:  
    "\<And>k. k \<le> 2*N+1 \<Longrightarrow> continuous_on {real_of_int a..} (fs k)"
  assumes fs_deriv [derivative_intros]: 
    "\<And>k x. k \<le> 2*N \<Longrightarrow> x \<in> {of_int a..} - Y \<Longrightarrow> (fs k has_vector_derivative fs (Suc k) x) (at x)"
  assumes F_cont [continuous_intros]: "continuous_on {of_int a..} F"
  assumes F_deriv [derivative_intros]: 
    "\<And>x. x \<in> {of_int a..} - Y \<Longrightarrow> (F has_vector_derivative f x) (at x)" 
  assumes limit: 
    "((\<lambda>b. (\<Sum>k=a..b. f k) - F (of_int b) -
         (\<Sum>i<2*N+1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b))) \<longlongrightarrow> C) at_top"
begin

sublocale euler_maclaurin_int F f fs a "2*N+1" C Y
  by standard (insert fin fs_0 fs_cont fs_deriv F_cont F_deriv limit, simp_all)

theorem euler_maclaurin_strong_int':
  assumes "a \<le> b"
  shows   "(\<Sum>k=a..b. f (of_int k)) = 
             F (of_int b) + C + (1 / 2) *\<^sub>R f (of_int b) +
             (\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (of_int b)) - 
             EM_remainder (2*N+1) (fs (2*N+1)) b"
proof -
  have "(\<Sum>k=a..b. f (real_of_int k)) = 
               F (of_int b) + C + (\<Sum>i<2*N+1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b)) - 
               EM_remainder (2*N+1) (fs (2*N+1)) b"
    by (rule euler_maclaurin_strong_int)
       (simp_all only: lessThan_Suc_atMost Suc_eq_plus1 [symmetric] assms)
  also have "{..<2*N+1} = insert 0 {1..2*N}" by auto
  also have "(\<Sum>i\<in>\<dots>. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b)) =
               (1 / 2) *\<^sub>R f (of_int b) + 
               (\<Sum>i\<in>{1..2*N}. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b))"
    by (subst sum.insert) (auto simp: assms bernoulli'_def)
  also have "(\<Sum>i\<in>{1..2*N}. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (of_int b)) =
               (\<Sum>i\<in>{1..N}. (bernoulli' (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (of_int b))"
  proof (rule sym, rule sum.reindex_bij_witness_not_neutral)
    fix i assume "i \<in> {1..2*N} - {i\<in>{1..2*N}. even i}"
    thus "2 * ((i + 1) div 2) - 1 = i" "(i + 1) div 2 \<in> {1..N} - {}" 
      by (auto elim!: oddE)
  qed (auto simp: bernoulli_odd_eq_0 bernoulli'_def algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>{1..N}. (bernoulli (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (of_int b))"
    by (intro sum.cong refl) (auto simp: bernoulli'_def)
  finally show ?thesis by (simp only: add_ac)
qed

end


text \<open>
  For convenience, we also offer a version where the sum ranges over natural numbers
  instead of integers.
\<close>

lemma sum_atLeastAtMost_of_int_nat_transfer:
  "(\<Sum>k=int a..int b. f (of_int k)) = (\<Sum>k=a..b. f (of_nat k))"
  by (intro sum.reindex_bij_witness[of _ int nat]) auto
  
lemma euler_maclaurin_nat_int_transfer:
  fixes F and f :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "((\<lambda>b. (\<Sum>k=a..b. f (real k)) - F (real b) - T (real b)) \<longlongrightarrow> C) at_top"
  shows   "((\<lambda>b. (\<Sum>k=int a..b. f (of_int k)) - F (of_int b) - T (of_int b)) \<longlongrightarrow> C) at_top"
proof -
  have *: "((\<lambda>b. (\<Sum>k=int a..int b. f (of_int k)) - F (of_int (int b)) - T (of_int (int b)))
            \<longlongrightarrow> C) at_top" using assms by (subst sum_atLeastAtMost_of_int_nat_transfer) simp
  thus ?thesis by (rule filterlim_int_of_nat_at_topD)
qed
  
locale euler_maclaurin_nat =
  fixes F f :: "real \<Rightarrow> 'a :: banach"
  fixes fs :: "nat \<Rightarrow> real \<Rightarrow> 'a"
  fixes a :: nat
  fixes N :: nat assumes N: "N > 0"
  fixes C :: 'a
  fixes Y :: "real set" assumes fin: "finite Y"
  assumes fs_0 [simp]: "fs 0 = f"
  assumes fs_cont [continuous_intros]:  
    "\<And>k. k \<le> N \<Longrightarrow> continuous_on {real a..} (fs k)"
  assumes fs_deriv [derivative_intros]: 
    "\<And>k x. k < N \<Longrightarrow> x \<in> {real a..} - Y \<Longrightarrow> (fs k has_vector_derivative fs (Suc k) x) (at x)"
  assumes F_cont [continuous_intros]: "continuous_on {real a..} F"
  assumes F_deriv [derivative_intros]: 
    "\<And>x. x \<in> {real a..} - Y \<Longrightarrow> (F has_vector_derivative f x) (at x)" 
  assumes limit: 
    "((\<lambda>b. (\<Sum>k=a..b. f k) - F (real b) - 
         (\<Sum>i<N. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (real b))) \<longlongrightarrow> C) at_top"
begin

sublocale euler_maclaurin_int F f fs "int a" N C Y
  by standard (insert N fin fs_cont fs_deriv F_cont F_deriv 
                 euler_maclaurin_nat_int_transfer[OF limit], simp_all)

theorem euler_maclaurin_strong_nat:
  assumes ab: "a \<le> b"
  defines "S \<equiv> (\<Sum>k=a..b. f (real k))"
  shows "S = F (real b) + C + (\<Sum>i<N. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (real b)) - 
               EM_remainder N (fs N) (int b)"
  using euler_maclaurin_strong_int[of "int b"]
  by (simp add: assms sum_atLeastAtMost_of_int_nat_transfer)

end

locale euler_maclaurin_nat' =
  fixes F f :: "real \<Rightarrow> 'a :: banach"
  fixes fs :: "nat \<Rightarrow> real \<Rightarrow> 'a"
  fixes a :: nat
  fixes N :: nat
  fixes C :: 'a
  fixes Y :: "real set" assumes fin: "finite Y"
  assumes fs_0 [simp]: "fs 0 = f"
  assumes fs_cont [continuous_intros]:  
    "\<And>k. k \<le> 2*N+1 \<Longrightarrow> continuous_on {real a..} (fs k)"
  assumes fs_deriv [derivative_intros]: 
    "\<And>k x. k \<le> 2*N \<Longrightarrow> x \<in> {real a..} - Y \<Longrightarrow> (fs k has_vector_derivative fs (Suc k) x) (at x)"
  assumes F_cont [continuous_intros]: "continuous_on {real a..} F"
  assumes F_deriv [derivative_intros]: 
    "\<And>x. x \<in> {real a..} - Y \<Longrightarrow> (F has_vector_derivative f x) (at x)" 
  assumes limit: 
    "((\<lambda>b. (\<Sum>k=a..b. f k) - F (real b) - 
        (\<Sum>i<2*N+1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (real b))) \<longlongrightarrow> C) at_top"
begin

sublocale euler_maclaurin_int' F f fs "int a" N C Y
  by standard (insert fin fs_cont fs_deriv F_cont F_deriv 
                 euler_maclaurin_nat_int_transfer[OF limit], simp_all)

theorem euler_maclaurin_strong_nat':
  assumes "a \<le> b"
  shows   "(\<Sum>k=a..b. f (real k)) = 
             F (real b) + C + (1 / 2) *\<^sub>R f (real b) +
             (\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (real b)) - 
             EM_remainder (2*N+1) (fs (2*N+1)) b"
  using euler_maclaurin_strong_int'[of b]
  by (simp add: assms sum_atLeastAtMost_of_int_nat_transfer)
    
end


subsection \<open>Bounds on the remainder term\<close>

text \<open>
  The following theorems provide some simple means to bound the remainder terms.
  In practice, better bounds can often be obtained e.\,g. for the $n$-th remainder term
  by expanding it to the sum of the first discarded term in the expansion and the $n+1$-th 
  remainder term.
\<close>

lemma
  fixes f :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and g g' :: "real \<Rightarrow> real"
  assumes fin:     "finite Y"
  assumes pbernpoly_bound: "\<forall>x. \<bar>pbernpoly n x\<bar> \<le> D"
  assumes cont_f:  "continuous_on {a..} f"
  assumes cont_g:  "continuous_on {a..} g"
  assumes cont_g': "continuous_on {a..} g'"
  assumes limit_g: "(g \<longlongrightarrow> C) at_top"
  assumes f_bound: "\<And>x. x \<ge> a \<Longrightarrow> norm (f x) \<le> g' x"
  assumes deriv:   "\<And>x. x \<in> {a..} - Y \<Longrightarrow> (g has_field_derivative g' x) (at x)"
  shows   norm_EM_remainder_le_strong_int:
            "\<forall>x. of_int x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D / fact n * (C - g x)"
  and     norm_EM_remainder_le_strong_nat:
            "\<forall>x. real x \<ge> a \<longrightarrow> norm (EM_remainder n f (int x)) \<le> D / fact n * (C - g x)"
proof -
  from pbernpoly_bound have D: "norm (pbernpoly n x) \<le> D" for x by auto 
  from this[of 0] have D_nonneg: "D \<ge> 0" by simp
  define D' where "D' = D / fact n"
  from D_nonneg have D'_nonneg: "D' \<ge> 0" by (simp add: D'_def)

  have bound: "norm (EM_remainder' n f x y) \<le> D' * (g y - g x)"
    if xy: "x \<ge> a" "x \<le> y" for x y :: real
  proof -
    have "norm (EM_remainder' n f x y) = norm (integral {x..y} (\<lambda>t. pbernpoly n t *\<^sub>R f t)) / fact n"
      by (simp add: EM_remainder'_def)
    also have "(\<lambda>t. D * g' t) integrable_on {x..y}" using xy
      by (intro integrable_continuous_real continuous_intros continuous_on_subset[OF cont_g'])
         auto
    hence "norm (integral {x..y} (\<lambda>t. pbernpoly n t *\<^sub>R f t)) \<le>
            integral {x..y} (\<lambda>t. D * g' t)" using D D_nonneg xy
      by (intro integral_norm_bound_integral integrable_EM_remainder' 
               continuous_on_subset[OF cont_f]) (auto intro!: mult_mono f_bound)
    also have "\<dots> = D * integral {x..y} g'" by simp
    also have "(g' has_integral (g y - g x)) {x..y}" using xy
      by (intro fundamental_theorem_of_calculus_strong[OF fin] continuous_on_subset[OF cont_g])
         (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] intro!: deriv)
    hence "integral {x..y} g' = g y - g x" by (simp add: has_integral_iff)
    finally show ?thesis by (simp add: D'_def divide_simps)
  qed
  
  have lim: "((\<lambda>y. EM_remainder' n f x (of_int y)) \<longlongrightarrow> EM_remainder n f x) at_top" 
    if x: "x \<ge> a" for x :: int
  proof -
    have "(\<lambda>n. g (real n)) \<longlonglongrightarrow> C" 
      by (rule filterlim_compose[OF limit_g filterlim_real_sequentially])
    hence Cauchy: "Cauchy (\<lambda>n. g (real n))" using convergent_eq_Cauchy by blast
    have "Cauchy (\<lambda>y. EM_remainder' n f x (int y))"
    proof (rule CauchyI', goal_cases)
      case (1 \<epsilon>)
      define \<epsilon>' where "\<epsilon>' = (if D' = 0 then 1 else \<epsilon> / (2*D'))"
      from \<open>\<epsilon> > 0\<close> D'_nonneg have \<epsilon>': "\<epsilon>' > 0" by (simp add: \<epsilon>'_def divide_simps)
      from CauchyD[OF Cauchy this] obtain M 
        where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (g (real m) - g (real n)) < \<epsilon>'" by blast
      show ?case
      proof (intro CauchyI' exI[of _ "max (max 0 M) (nat x)"] allI impI, goal_cases)
        case (1 k l)
        have "EM_remainder' n f x k + EM_remainder' n f k l = EM_remainder' n f x l"
          using 1 x by (intro EM_remainder'_combine continuous_on_subset[OF cont_f]) auto
        hence "EM_remainder' n f x l - EM_remainder' n f x k = EM_remainder' n f k l" 
          by (simp add: algebra_simps)
        also from 1 x have "norm \<dots> \<le> D' * (g l - g k)" by (intro bound) auto
        also have "g l - g k \<le> norm (g l - g k)" by simp
        also from 1 have "\<dots> \<le> \<epsilon>'" using M[of l k] by auto
        also from \<open>\<epsilon> > 0\<close> have "D' * \<epsilon>' \<le> \<epsilon> / 2" by (simp add: \<epsilon>'_def)
        also from \<open>\<epsilon> > 0\<close> have "\<dots> < \<epsilon>" by simp
        finally show ?case by (simp add: D'_nonneg mult_left_mono dist_norm norm_minus_commute)
      qed
    qed
    then obtain L where "(\<lambda>y. EM_remainder' n f x (int y)) \<longlonglongrightarrow> L"
      by (auto simp: Cauchy_convergent_iff convergent_def)
    from filterlim_int_of_nat_at_topD[OF this]
      have "((\<lambda>y. EM_remainder' n f x (of_int y)) \<longlongrightarrow> L) at_top" by simp
    moreover from this have "EM_remainder n f x = L" by (rule EM_remainder_eqI)
    ultimately show "((\<lambda>y. EM_remainder' n f x (of_int y)) \<longlongrightarrow> EM_remainder n f x) at_top"
      by simp
  qed
  
  have *: "norm (EM_remainder n f x) \<le> D' * (C - g x)" if x: "x \<ge> a" for x :: int
  proof (rule tendsto_le)
    show "((\<lambda>y. D' * (g (of_int y) - g (of_int x))) \<longlongrightarrow> D' * (C - g (of_int x))) at_top"
      by (intro tendsto_intros filterlim_compose[OF limit_g])
    show "((\<lambda>y. norm (EM_remainder' n f x (of_int y))) \<longlongrightarrow> norm (EM_remainder n f x)) at_top"
      using x by (intro tendsto_norm lim)
    show "eventually (\<lambda>y. norm (EM_remainder' n f (of_int x) (of_int y))
             \<le> D' * (g (of_int y) - g (of_int x))) at_top" 
      using eventually_ge_at_top[of x] by eventually_elim (rule bound, insert x, simp_all)
  qed simp_all
  thus "\<forall>x. of_int x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D' * (C - g x)" by blast
  
  have "norm (EM_remainder n f x) \<le> D' * (C - g x)" if x: "x \<ge> a" for x :: nat
    using x *[of "int x"] by simp
  thus "\<forall>x. real x \<ge> a \<longrightarrow> norm (EM_remainder n f (int x)) \<le> D' * (C - g x)" by blast
qed

lemma
  fixes f :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and g g' :: "real \<Rightarrow> real"
  assumes fin:     "finite Y"
  assumes pbernpoly_bound: "\<forall>x. \<bar>pbernpoly n x\<bar> \<le> D"
  assumes cont_f:  "continuous_on {a..} f"
  assumes cont_g:  "continuous_on {a..} g"
  assumes cont_g': "continuous_on {a..} g'"
  assumes limit_g: "(g \<longlongrightarrow> 0) at_top"
  assumes f_bound: "\<And>x. x \<ge> a \<Longrightarrow> norm (f x) \<le> g' x"
  assumes deriv:   "\<And>x. x \<in> {a..} - Y \<Longrightarrow> (g has_field_derivative -g' x) (at x)"
  shows   norm_EM_remainder_le_strong_int': 
            "\<forall>x. of_int x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D / fact n * g x"
    and   norm_EM_remainder_le_strong_nat': 
            "\<forall>x. real x \<ge> a \<longrightarrow> norm (EM_remainder n f (int x)) \<le> D / fact n * g x"
proof -
  have "\<forall>x. of_int x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D / fact n * (0 - (-g x))" using assms
    by (intro norm_EM_remainder_le_strong_int[OF fin pbernpoly_bound _ _ cont_g'])
       (auto intro!: continuous_intros tendsto_eq_intros derivative_eq_intros)
  thus "\<forall>x. of_int x \<ge> a \<longrightarrow> norm (EM_remainder n f x) \<le> D / fact n * g x" by auto
next
  have "\<forall>x. real x \<ge> a \<longrightarrow> norm (EM_remainder n f (int x)) \<le> D / fact n * (0 - (-g x))" using assms
    by (intro norm_EM_remainder_le_strong_nat[OF fin pbernpoly_bound _ _ cont_g'])
       (auto intro!: continuous_intros tendsto_eq_intros derivative_eq_intros)
  thus "\<forall>x. real x \<ge> a \<longrightarrow> norm (EM_remainder n f (int x)) \<le> D / fact n * g x" by auto
qed

lemma norm_EM_remainder'_le:
  fixes f :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and g g' :: "real \<Rightarrow> real"
  assumes cont_f: "continuous_on {a..} f"
  assumes cont_g': "continuous_on {a..} g'"
  assumes f_bigo: "eventually (\<lambda>x. norm (f x) \<le> g' x) at_top"
  assumes deriv:  "eventually (\<lambda>x. (g has_field_derivative g' x) (at x)) at_top"
  obtains C D where
    "eventually (\<lambda>x. norm (EM_remainder' n f a x) \<le> C + D * g x) at_top"
proof -
  note cont = continuous_on_subset[OF cont_f] continuous_on_subset[OF cont_g']
  from bounded_pbernpoly[of n] obtain D where D: "\<And>x. norm (pbernpoly n x) \<le> D" by blast
  from this[of 0] have D_nonneg: "D \<ge> 0" by simp
  from eventually_conj[OF f_bigo eventually_conj[OF deriv eventually_ge_at_top[of a]]] 
    obtain x0 where x0:
      "x0 \<ge> a" "\<And>x. x \<ge> x0 \<Longrightarrow> norm (f x) \<le> g' x" 
      "\<And>x. x \<ge> x0 \<Longrightarrow> (g has_field_derivative g' x) (at x)"
      by (auto simp: eventually_at_top_linorder)
  define C where "C = (norm (integral {a..x0} (\<lambda>t. pbernpoly n t *\<^sub>R f t)) - D * g x0) / fact n"
      
  have "eventually (\<lambda>x. norm (EM_remainder' n f a x) \<le> C + D / fact n * g x) at_top"
    using eventually_ge_at_top[of x0]
  proof eventually_elim
    case (elim x)
    have "integral {a..x} (\<lambda>t. pbernpoly n t *\<^sub>R f t) =
            integral {a..x0} (\<lambda>t. pbernpoly n t *\<^sub>R f t) +
            integral {x0..x} (\<lambda>t. pbernpoly n t *\<^sub>R f t)" (is "_ = ?I1 + ?I2") using elim x0(1)
      by (intro integral_combine [symmetric] integrable_EM_remainder' cont) auto
    also have "norm \<dots> \<le> norm ?I1 + norm ?I2" by (rule norm_triangle_ineq)
    also have "norm ?I2 \<le> integral {x0..x} (\<lambda>t. D * g' t)"
      using x0 D D_nonneg
      by (intro integral_norm_bound_integral integrable_EM_remainder')
         (auto intro!: integrable_continuous_real continuous_intros cont mult_mono)
    also have "\<dots> = D * integral {x0..x} g'" by simp
    also from elim have "(g' has_integral (g x - g x0)) {x0..x}"
      by (intro fundamental_theorem_of_calculus) 
         (auto intro!: has_field_derivative_at_within[OF x0(3)] 
               simp: has_field_derivative_iff_has_vector_derivative [symmetric])
    hence "integral {x0..x} g' = g x - g x0" by (simp add: has_integral_iff)
    finally have "norm (integral {a..x} (\<lambda>t. pbernpoly n t *\<^sub>R f t)) \<le> norm ?I1 + D * (g x - g x0)"
      by simp_all
    thus "norm (EM_remainder' n f a x) \<le> C + D / fact n * g x"
      by (simp add: EM_remainder'_def field_simps C_def)
  qed
  thus ?thesis by (rule that)
qed


subsection \<open>Application to harmonic numbers\<close>

text \<open>
  As a first application, we can apply the machinery we have developed to the 
  harmonic numbers.
\<close>

definition harm_remainder :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "harm_remainder N n = EM_remainder (2*N+1) (\<lambda>x. -fact (2*N+1) / x ^ (2*N+2)) (int n)"

lemma harm_expansion:
  assumes n: "n > 0" and N: "N > 0"
  shows "harm n = ln n + euler_mascheroni + 1 / (2*n) -
                     (\<Sum>i=1..N. bernoulli (2*i) / ((2*i) * n ^ (2*i))) - harm_remainder N n"
proof -
  define fs where "fs = (\<lambda>k x. (-1) ^ k * fact k / x ^ (Suc k) :: real)"    
  interpret euler_maclaurin_nat' ln "\<lambda>x. 1/x" fs 1 N euler_mascheroni "{}"
  proof
    fix k x assume "k \<le> 2*N" "x \<in> {real 1..} - {}"
    thus "(fs k has_vector_derivative fs (Suc k) x) (at x)"
      by (cases "k = 0")
         (auto intro!: derivative_eq_intros 
               simp: fs_def has_field_derivative_iff_has_vector_derivative [symmetric] 
                     field_simps power_diff)
  next
    have "(\<lambda>b. harm b - ln (real b) -
                 (\<Sum>i<2*N+1. bernoulli' (Suc i) * (- 1) ^ i / (real (Suc i) * (real b ^ Suc i))))
            \<longlonglongrightarrow> (euler_mascheroni - (\<Sum>i<2*N+1. 0))"
      by (intro tendsto_diff euler_mascheroni_LIMSEQ tendsto_sum 
            real_tendsto_divide_at_top[OF tendsto_const] 
            filterlim_tendsto_pos_mult_at_top[OF tendsto_const] filterlim_pow_at_top
            filterlim_real_sequentially) auto
    thus "(\<lambda>b. (\<Sum>k = 1..b. 1 / real k) - ln (real b) - 
            (\<Sum>i<2*N+1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (real b))) \<longlonglongrightarrow> euler_mascheroni"
      by (simp add: harm_def divide_simps fs_def)
  qed (insert n N, auto intro!: continuous_intros derivative_eq_intros
         simp: fs_def has_field_derivative_iff_has_vector_derivative [symmetric])
       
  have "harm n = (\<Sum>k=1..n. 1 / real k)" by (simp add: harm_def divide_simps)
  also have "\<dots> = ln (real n) + euler_mascheroni + (1/2) *\<^sub>R (1 / real n) +
                     (\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (real n)) -
                     EM_remainder (2*N+1) (fs (2*N+1)) (int n)" using n N
    using n by (intro euler_maclaurin_strong_nat') simp_all
  also have "(\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R (fs (2*i-1) (real n))) =
               (\<Sum>i=1..N. -(bernoulli (2*i) / (real (2*i) * real n ^ (2*i))))"
    by (intro sum.cong refl) 
       (simp_all add: fs_def divide_simps fact_reduce del: of_nat_Suc power_Suc)
  also have "\<dots> = -(\<Sum>i=1..N. bernoulli (2*i) / (real (2*i) * real n ^ (2*i)))" 
    by (simp add: sum_negf)
  finally show ?thesis unfolding fs_def by (simp add: harm_remainder_def)
qed

lemma of_nat_ge_1_iff: "of_nat x \<ge> (1 :: 'a :: linordered_semidom) \<longleftrightarrow> x \<ge> 1"
  using of_nat_le_iff[of 1 x] by (simp del: of_nat_le_iff)

lemma harm_remainder_bound:
  fixes N :: nat
  assumes N: "N > 0"
  shows "\<exists>C. \<forall>n\<ge>1. norm (harm_remainder N n) \<le> C / real n ^ (2*N+1)"
proof -
  from bounded_pbernpoly[of "2*N+1"] obtain D where D: "\<forall>x. \<bar>pbernpoly (2*N+1) x\<bar> \<le> D" by auto
  have "\<forall>x. 1 \<le> real x \<longrightarrow> norm (harm_remainder N x) \<le>
          D / fact (2*N+1) * (fact (2*N) / x ^ (2*N+1))"
    unfolding harm_remainder_def of_int_of_nat_eq
  proof (rule norm_EM_remainder_le_strong_nat'[of "{}"])
    fix x :: real assume x: "x \<ge> 1"
    show "norm (-fact (2*N+1) / x ^ (2 * N + 2)) \<le> fact (2*N+1) / x ^ (2*N+2)"
      using x by simp
  next
    show "((\<lambda>x::real. fact (2 * N) / x ^ (2 * N + 1)) \<longlongrightarrow> 0) at_top"
      by (intro real_tendsto_divide_at_top[OF tendsto_const] filterlim_pow_at_top filterlim_ident)
         simp_all
  qed (insert N D, auto intro!: derivative_eq_intros continuous_intros simp: field_simps power_diff)
  hence "\<forall>x. 1 \<le> x \<longrightarrow> norm (harm_remainder N x) \<le> D / (2*N+1) / real x ^ (2*N+1)" by simp
  thus ?thesis by blast
qed
  

subsection \<open>Application to sums of inverse squares\<close>

text \<open>
  In the same vein, we can derive the asymptotics of the partial sum of inverse squares.
\<close>

lemma sum_inverse_squares_expansion:
  assumes n: "n > 0" and N: "N > 0"
  shows "(\<Sum>k=1..n. 1 / real k ^ 2) = 
            pi ^ 2 / 6 - 1 / real n + 1 / (2 * real n ^ 2) -
                     (\<Sum>i=1..N. bernoulli (2*i) / n ^ (2*i+1)) - 
                    EM_remainder (2*N+1) (\<lambda>x. -fact (2*N+2) / x ^ (2*N+3)) (int n)"
proof -
  have 3: "3 = Suc (Suc (Suc 0))" by (simp add: eval_nat_numeral)
  define fs where "fs = (\<lambda>k x. (-1) ^ k * fact (Suc k) / x ^ (k+2) :: real)"    
  interpret euler_maclaurin_nat' "\<lambda>x. -1/x" "\<lambda>x. 1/x^2" fs 1 N "pi^2/6" "{}"
  proof
    fix k x assume "k \<le> 2*N" "x \<in> {real 1..} - {}"
    thus "(fs k has_vector_derivative fs (Suc k) x) (at x)"
      by (cases "k = 0")
         (auto intro!: derivative_eq_intros 
               simp: fs_def has_field_derivative_iff_has_vector_derivative [symmetric] 
                     field_simps power_diff)
  next
    from inverse_squares_sums
      have "(\<lambda>n. \<Sum>k<n. 1 / real (Suc k) ^ 2) \<longlonglongrightarrow> pi\<^sup>2 / 6" by (simp add: sums_def)
    also have "(\<lambda>n. \<Sum>k<n. 1 / real (Suc k) ^ 2) = (\<lambda>n. \<Sum>k=1..n. 1 / real k ^ 2)"
      by (intro ext sum.reindex_bij_witness[of _ "\<lambda>n. n - 1" Suc]) auto
    finally have "(\<lambda>b. (\<Sum>k = 1..b. 1 / real k^2) + 1 / real b -
                 (\<Sum>i<2*N+1. bernoulli' (Suc i) * (- 1) ^ i / (real b ^ (i+2))))
            \<longlonglongrightarrow> (pi^2/6 + 0 - (\<Sum>i<2*N+1. 0))"
      by (intro tendsto_diff tendsto_add real_tendsto_divide_at_top[OF tendsto_const] 
            filterlim_tendsto_pos_mult_at_top[OF tendsto_const] filterlim_pow_at_top
            filterlim_real_sequentially tendsto_sum) auto
    thus "(\<lambda>b. (\<Sum>k = 1..b. 1 / real k^2) - (- 1 / real b) - 
            (\<Sum>i<2*N+1. (bernoulli' (Suc i) / fact (Suc i)) *\<^sub>R fs i (real b))) \<longlonglongrightarrow> pi^2/6"
      by (simp add: harm_def field_simps fs_def del: power_Suc of_nat_Suc)
  qed (insert n N, auto intro!: continuous_intros derivative_eq_intros
         simp: fs_def has_field_derivative_iff_has_vector_derivative [symmetric] power2_eq_square)

  have "(\<Sum>k=1..n. 1 / real k ^ 2) = - 1 / real n + pi^2/6 + (1/2) *\<^sub>R (1 / real n^2) +
               (\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R fs (2*i-1) (real n)) -
               EM_remainder (2*N+1) (fs (2*N+1)) (int n)" using n N
    using n by (intro euler_maclaurin_strong_nat') simp_all
  also have "(\<Sum>i=1..N. (bernoulli (2*i) / fact (2*i)) *\<^sub>R (fs (2*i-1) (real n))) =
               (\<Sum>i=1..N. -(bernoulli (2*i) / (real n ^ (2*i+1))))"
    by (intro sum.cong refl) 
       (simp_all add: fs_def divide_simps fact_reduce del: of_nat_Suc power_Suc)
  also have "\<dots> = -(\<Sum>i=1..N. bernoulli (2*i) / real n ^ (2*i+1))"
    by (simp add: sum_negf)
  finally show ?thesis unfolding fs_def by (simp add: fs_def 3)
qed

lemma sum_inverse_squares_remainder_bound:
  fixes N :: nat
  assumes N: "N > 0"
  defines "R \<equiv> (\<lambda>n. EM_remainder (2*N+1) (\<lambda>x. -fact (2*N+2) / x ^ (2*N+3)) (int n))"
  shows   "\<exists>C. \<forall>n\<ge>1. norm (R n) \<le> C / real n ^ (2*N+2)"
proof -
  have 3: "3 = Suc (Suc (Suc 0))" by simp
  from bounded_pbernpoly[of "2*N+1"] obtain D where D: "\<forall>x. \<bar>pbernpoly (2*N+1) x\<bar> \<le> D" by auto
  have "\<forall>x. 1 \<le> real x \<longrightarrow> norm (R x) \<le> D / fact (2*N+1) * (fact (2*N+1) / x ^ (2*N+2))"
    unfolding R_def of_int_of_nat_eq
  proof (rule norm_EM_remainder_le_strong_nat'[of "{}"])
    fix x :: real assume x: "x \<ge> 1"
    show "norm (-fact (2*N+2) / x ^ (2*N+3)) \<le> fact (2*N+2) / x ^ (2*N+3)"
      using x by simp
  next
    show "((\<lambda>x::real. fact (2*N+1) / x ^ (2*N+2)) \<longlongrightarrow> 0) at_top"
      by (intro real_tendsto_divide_at_top[OF tendsto_const] filterlim_pow_at_top filterlim_ident)
         simp_all
  qed (insert N D, auto intro!: derivative_eq_intros continuous_intros simp: field_simps power_diff 3)
  hence "\<forall>x\<ge>1. norm (R x) \<le> D / real x ^ (2 * N + 2)" by simp
  thus ?thesis by blast
qed

end
