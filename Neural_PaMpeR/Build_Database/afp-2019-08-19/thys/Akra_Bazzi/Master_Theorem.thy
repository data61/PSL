(*
  File:   Master_Theorem.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  The Master theorem in a generalised form as derived from the Akra-Bazzi theorem.
*)
section \<open>The Master theorem\<close>
theory Master_Theorem
imports
  "HOL-Analysis.Analysis"
  Akra_Bazzi_Library
  Akra_Bazzi
begin

lemma fundamental_theorem_of_calculus_real:
  "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. (f has_real_derivative f' x) (at x within {a..b}) \<Longrightarrow>
      (f' has_integral (f b - f a)) {a..b}"
  by (intro fundamental_theorem_of_calculus ballI)
     (simp_all add: has_field_derivative_iff_has_vector_derivative[symmetric])

lemma integral_powr:
  "y \<noteq> -1 \<Longrightarrow> a \<le> b \<Longrightarrow> a > 0 \<Longrightarrow> integral {a..b} (\<lambda>x. x powr y :: real) =
     inverse (y + 1) * (b powr (y + 1) - a powr (y + 1))"
  by (subst right_diff_distrib, intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros)

lemma integral_ln_powr_over_x:
  "y \<noteq> -1 \<Longrightarrow> a \<le> b \<Longrightarrow> a > 1 \<Longrightarrow> integral {a..b} (\<lambda>x. ln x powr y / x :: real) =
     inverse (y + 1) * (ln b powr (y + 1) - ln a powr (y + 1))"
  by (subst right_diff_distrib, intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros)

lemma integral_one_over_x_ln_x:
  "a \<le> b \<Longrightarrow> a > 1 \<Longrightarrow> integral {a..b} (\<lambda>x. inverse (x * ln x) :: real) = ln (ln b) - ln (ln a)"
  by (intro integral_unique fundamental_theorem_of_calculus_real)
     (auto intro!: derivative_eq_intros simp: field_simps)

lemma akra_bazzi_integral_kurzweil_henstock:
  "akra_bazzi_integral (\<lambda>f a b. f integrable_on {a..b}) (\<lambda>f a b. integral {a..b} f)"
apply unfold_locales
apply (rule integrable_const_ivl)
apply simp
apply (erule integrable_subinterval_real, simp)
apply (blast intro!: integral_le)
apply (rule integral_combine, simp_all) []
done


locale master_theorem_function = akra_bazzi_recursion +
  fixes g :: "nat \<Rightarrow> real"
  assumes f_nonneg_base: "x \<ge> x\<^sub>0 \<Longrightarrow> x < x\<^sub>1 \<Longrightarrow> f x \<ge> 0"
  and     f_rec:         "x \<ge> x\<^sub>1 \<Longrightarrow> f x = g x + (\<Sum>i<k. as!i * f ((ts!i) x))"
  and     g_nonneg:      "x \<ge> x\<^sub>1 \<Longrightarrow> g x \<ge> 0"
  and     ex_pos_a:      "\<exists>a\<in>set as. a > 0"
begin

interpretation akra_bazzi_integral "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f"
  by (rule akra_bazzi_integral_kurzweil_henstock)

sublocale akra_bazzi_function x\<^sub>0 x\<^sub>1 k as bs ts f "\<lambda>f a b. f integrable_on {a..b}"
            "\<lambda>f a b. integral {a..b} f" g
  using f_nonneg_base f_rec g_nonneg ex_pos_a by unfold_locales

context
begin

private lemma g_nonneg': "eventually (\<lambda>x. g x \<ge> 0) at_top"
  using g_nonneg by (force simp: eventually_at_top_linorder)

private lemma g_pos:
  assumes "g \<in> \<Omega>(h)"
  assumes "eventually (\<lambda>x. h x > 0) at_top"
  shows   "eventually (\<lambda>x. g x > 0) at_top"
proof-
  from landau_omega.bigE_nonneg_real[OF assms(1) g_nonneg'] guess c . note c = this
  from assms(2) c(2) show ?thesis
    by eventually_elim (rule less_le_trans[OF mult_pos_pos[OF c(1)]], simp_all)
qed

private lemma f_pos:
  assumes "g \<in> \<Omega>(h)"
  assumes "eventually (\<lambda>x. h x > 0) at_top"
  shows   "eventually (\<lambda>x. f x > 0) at_top"
  using g_pos[OF assms(1,2)] eventually_ge_at_top[of x\<^sub>1]
  by (eventually_elim) (subst f_rec, insert step_ge_x0,
         auto intro!: add_pos_nonneg sum_nonneg mult_nonneg_nonneg[OF a_ge_0] f_nonneg)

lemma bs_lower_bound: "\<exists>C>0. \<forall>b\<in>set bs. C < b"
proof (intro exI conjI ballI)
  from b_pos show A: "Min (set bs) / 2 > 0" by auto
  fix b assume b: "b \<in> set bs"
  from A have "Min (set bs) / 2 < Min (set bs)" by simp
  also from b have "... \<le> b" by simp
  finally show "Min (set bs) / 2 < b" .
qed

private lemma powr_growth2:
  "\<exists>C c2. 0 < c2 \<and> C < Min (set bs) \<and>
      eventually (\<lambda>x. \<forall>u\<in>{C * x..x}. c2 * x powr p' \<ge> u powr p') at_top"
proof (intro exI conjI allI ballI)
  define C where "C = Min (set bs) / 2"
  from b_bounds bs_nonempty have C_pos: "C > 0" unfolding C_def by auto
  thus "C < Min (set bs)" unfolding C_def by simp
  show "max (C powr p') 1 > 0" by simp
  show "eventually (\<lambda>x. \<forall>u\<in>{C * x..x}.
    max ((Min (set bs)/2) powr p') 1 * x powr p' \<ge> u powr p') at_top"
    using eventually_gt_at_top[of "0::real"] apply eventually_elim
  proof clarify
    fix x u assume x: "x > 0" and "u \<in> {C*x..x}"
    hence u: "u \<ge> C*x" "u \<le> x" unfolding C_def by  simp_all
    from u have "u powr p' \<le> max ((C*x) powr p') (x powr p')" using C_pos x
      by (intro powr_upper_bound mult_pos_pos) simp_all
    also from u x C_pos have "max ((C*x) powr p') (x powr p') = x powr p' * max (C powr p') 1"
      by (subst max_mult_left) (simp_all add: powr_mult algebra_simps)
    finally show "u powr p' \<le> max ((Min (set bs)/2) powr p') 1 * x powr p'"
      by (simp add: C_def algebra_simps)
  qed
qed

private lemma powr_growth1:
  "\<exists>C c1. 0 < c1 \<and> C < Min (set bs) \<and>
      eventually (\<lambda>x. \<forall>u\<in>{C * x..x}. c1 * x powr p' \<le> u powr p') at_top"
proof (intro exI conjI allI ballI)
  define C where "C = Min (set bs) / 2"
  from b_bounds bs_nonempty have C_pos: "C > 0" unfolding C_def by auto
  thus "C < Min (set bs)" unfolding C_def by simp
  from C_pos show "min (C powr p') 1 > 0" by simp
  show "eventually (\<lambda>x. \<forall>u\<in>{C * x..x}.
          min ((Min (set bs)/2) powr p') 1 * x powr p' \<le> u powr p') at_top"
    using eventually_gt_at_top[of "0::real"] apply eventually_elim
  proof clarify
    fix x u assume x: "x > 0" and "u \<in> {C*x..x}"
    hence u: "u \<ge> C*x" "u \<le> x" unfolding C_def by  simp_all
    from u x C_pos have "x powr p' * min (C powr p') 1 = min ((C*x) powr p') (x powr p')"
      by (subst min_mult_left) (simp_all add: powr_mult algebra_simps)
    also from u have "u powr p' \<ge> min ((C*x) powr p') (x powr p')" using C_pos x
      by (intro powr_lower_bound mult_pos_pos) simp_all
    finally show "u powr p' \<ge> min ((Min (set bs)/2) powr p') 1 * x powr p'"
      by (simp add: C_def algebra_simps)
  qed
qed

private lemma powr_ln_powr_lower_bound:
  "a > 1 \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
     min (a powr p) (b powr p) * min (ln a powr p') (ln b powr p') \<le> x powr p * ln x powr p'"
  by (intro mult_mono powr_lower_bound) (auto intro: min.coboundedI1)

private lemma powr_ln_powr_upper_bound:
  "a > 1 \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow>
     max (a powr p) (b powr p) * max (ln a powr p') (ln b powr p') \<ge> x powr p * ln x powr p'"
  by (intro mult_mono powr_upper_bound) (auto intro: max.coboundedI1)

private lemma powr_ln_powr_upper_bound':
  "eventually (\<lambda>a. \<forall>b>a. \<exists>c. \<forall>x\<in>{a..b}. x powr p * ln x powr p' \<le> c) at_top"
  by (subst eventually_at_top_dense) (force intro: powr_ln_powr_upper_bound)

private lemma powr_upper_bound':
  "eventually (\<lambda>a::real. \<forall>b>a. \<exists>c. \<forall>x\<in>{a..b}. x powr p' \<le> c) at_top"
  by (subst eventually_at_top_dense) (force intro: powr_upper_bound)

lemmas bounds =
  powr_ln_powr_lower_bound powr_ln_powr_upper_bound powr_ln_powr_upper_bound' powr_upper_bound'


private lemma eventually_ln_const:
  assumes "(C::real) > 0"
  shows   "eventually (\<lambda>x. ln (C*x) / ln x > 1/2) at_top"
proof-
  from tendstoD[OF tendsto_ln_over_ln[of C 1], of "1/2"] assms
    have "eventually (\<lambda>x. \<bar>ln (C*x) / ln x - 1\<bar> < 1/2) at_top" by (simp add: dist_real_def)
  thus ?thesis by eventually_elim linarith
qed

private lemma powr_ln_powr_growth1: "\<exists>C c1. 0 < c1 \<and> C < Min (set bs) \<and>
  eventually (\<lambda>x. \<forall>u\<in>{C * x..x}. c1 * (x powr r * ln x powr r') \<le> u powr r * ln u powr r') at_top"
proof (intro exI conjI)
  let ?C = "Min (set bs) / 2" and ?f = "\<lambda>x. x powr r * ln x powr r'"
  define C where "C = ?C"
  from b_bounds have C_pos: "C > 0" unfolding C_def by simp
  let ?T = "min (C powr r) (1 powr r) * min ((1/2) powr r') (1 powr r')"
  from C_pos show "?T > 0" unfolding min_def by (auto split: if_split)
  from bs_nonempty b_bounds have C_pos: "C > 0" unfolding C_def by simp
  thus "C < Min (set bs)" by (simp add: C_def)

  show "eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. ?T * ?f x \<le> ?f u) at_top"
    using eventually_gt_at_top[of "max 1 (inverse C)"] eventually_ln_const[OF C_pos]
    apply eventually_elim
  proof clarify
    fix x u assume x: "x > max 1 (inverse C)" and u: "u \<in> {C*x..x}"
    hence x': "x > 1" by (simp add: field_simps)
    with C_pos have x_pos: "x > 0" by (simp add: field_simps)
    from x u C_pos have u': "u > 1" by (simp add: field_simps)
    assume A: "ln (C*x) / ln x > 1/2"
    have "min (C powr r) (1 powr r) \<le> (u/x) powr r"
      using x u u' C_pos by (intro powr_lower_bound) (simp_all add: field_simps)
    moreover {
      note A
      also from C_pos x' u u' have "ln (C*x) \<le> ln u" by (subst ln_le_cancel_iff) simp_all
      with x' have "ln (C*x) / ln x \<le> ln u / ln x" by (simp add: field_simps)
      finally have "min ((1/2) powr r') (1 powr r') \<le> (ln u / ln x) powr r'"
        using x u u' C_pos A by (intro powr_lower_bound) simp_all
    }
    ultimately have "?T \<le> (u/x) powr r * (ln u / ln x) powr r'"
      using x_pos by (intro mult_mono) simp_all
    also from x u u' have "... = ?f u / ?f x" by (simp add: powr_divide)
    finally show "?T * ?f x \<le> ?f u" using x' by (simp add: field_simps)
  qed
qed

private lemma powr_ln_powr_growth2: "\<exists>C c1. 0 < c1 \<and> C < Min (set bs) \<and>
  eventually (\<lambda>x. \<forall>u\<in>{C * x..x}. c1 * (x powr r * ln x powr r') \<ge> u powr r * ln u powr r') at_top"
proof (intro exI conjI)
  let ?C = "Min (set bs) / 2" and ?f = "\<lambda>x. x powr r * ln x powr r'"
  define C where "C = ?C"
  let ?T = "max (C powr r) (1 powr r) * max ((1/2) powr r') (1 powr r')"
  show "?T > 0" by simp
  from b_bounds bs_nonempty have C_pos: "C > 0" unfolding C_def by simp
  thus "C < Min (set bs)" by (simp add: C_def)

  show "eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. ?T * ?f x \<ge> ?f u) at_top"
    using eventually_gt_at_top[of "max 1 (inverse C)"] eventually_ln_const[OF C_pos]
    apply eventually_elim
  proof clarify
    fix x u assume x: "x > max 1 (inverse C)" and u: "u \<in> {C*x..x}"
    hence x': "x > 1" by (simp add: field_simps)
    with C_pos have x_pos: "x > 0" by (simp add: field_simps)
    from x u C_pos have u': "u > 1" by (simp add: field_simps)
    assume A: "ln (C*x) / ln x > 1/2"
    from x u u' have "?f u / ?f x = (u/x) powr r * (ln u/ln x) powr r'" by (simp add: powr_divide)
    also {
      have "(u/x) powr r \<le> max (C powr r) (1 powr r)"
        using x u u' C_pos by (intro powr_upper_bound) (simp_all add: field_simps)
      moreover {
        note A
        also from C_pos x' u u' have "ln (C*x) \<le> ln u" by (subst ln_le_cancel_iff) simp_all
        with x' have "ln (C*x) / ln x \<le> ln u / ln x" by (simp add: field_simps)
        finally have "(ln u / ln x) powr r' \<le> max ((1/2) powr r') (1 powr r')"
          using x u u' C_pos A by (intro powr_upper_bound) simp_all
      } ultimately have "(u/x) powr r * (ln u / ln x) powr r' \<le> ?T"
        using x_pos by (intro mult_mono) simp_all
    }
    finally show "?T * ?f x \<ge> ?f u" using x' by (simp add: field_simps)
  qed
qed

lemmas growths = powr_growth1 powr_growth2 powr_ln_powr_growth1 powr_ln_powr_growth2


private lemma master_integrable:
  "\<exists>a::real. \<forall>b\<ge>a. (\<lambda>u. u powr r * ln u powr s / u powr t) integrable_on {a..b}"
  "\<exists>a::real. \<forall>b\<ge>a. (\<lambda>u. u powr r / u powr s) integrable_on {a..b}"
  by (rule exI[of _ 2], force intro!: integrable_continuous_real continuous_intros)+

private lemma master_integral:
  fixes a p p' :: real
  assumes p: "p \<noteq> p'" and a: "a > 0"
  obtains c d where "c \<noteq> 0" "p > p' \<longrightarrow> d \<noteq> 0"
    "(\<lambda>x::nat. x powr p * (1 + integral {a..x} (\<lambda>u. u powr p' / u powr (p+1)))) \<in>
             \<Theta>(\<lambda>x::nat. d * x powr p + c * x powr p')"
proof-
  define e where "e = a powr (p' - p)"
  from assms have e: "e \<ge> 0" by (simp add: e_def)
  define c where "c = inverse (p' - p)"
  define d where "d = 1 - inverse (p' - p) * e"
  have "c \<noteq> 0" and "p > p' \<longrightarrow> d \<noteq> 0"
    using e p a unfolding c_def d_def by (auto simp: field_simps)
  thus ?thesis
    apply (rule that) apply (rule bigtheta_real_nat_transfer, rule bigthetaI_cong)
    using eventually_ge_at_top[of a]
  proof eventually_elim
    fix x assume x: "x \<ge> a"
    hence "integral {a..x} (\<lambda>u. u powr p' / u powr (p+1)) =
               integral {a..x} (\<lambda>u. u powr (p' - (p + 1)))"
      by (intro Henstock_Kurzweil_Integration.integral_cong) (simp_all add: powr_diff [symmetric] )
    also have "... = inverse (p' - p) * (x powr (p' - p) - a powr (p' - p))"
      using p x0_less_x1 a x by (simp add: integral_powr)
    also have "x powr p * (1 + ...) = d * x powr p + c * x powr p'"
      using p unfolding c_def d_def by (simp add: algebra_simps powr_diff e_def)
    finally show "x powr p * (1 + integral {a..x} (\<lambda>u. u powr p' / u powr (p+1))) =
                      d * x powr p + c * x powr p'" .
  qed
qed

private lemma master_integral':
  fixes a p p' :: real
  assumes p': "p' \<noteq> 0" and a: "a > 1"
  obtains c d :: real where "p' < 0 \<longrightarrow> c \<noteq> 0" "d \<noteq> 0"
    "(\<lambda>x::nat. x powr p * (1 + integral {a..x} (\<lambda>u. u powr p * ln u powr (p'-1) / u powr (p+1)))) \<in>
       \<Theta>(\<lambda>x::nat. c * x powr p + d * x powr p * ln x powr p')"
proof-
  define e where "e = ln a powr p'"
  from assms have e: "e > 0" by (simp add: e_def)
  define c where "c = 1 - inverse p' * e"
  define d where "d = inverse p'"
  from assms e have "p' < 0 \<longrightarrow> c \<noteq> 0" "d \<noteq> 0" unfolding c_def d_def by (auto simp: field_simps)
  thus ?thesis
    apply (rule that) apply (rule landau_real_nat_transfer, rule bigthetaI_cong)
    using eventually_ge_at_top[of a]
  proof eventually_elim
    fix x :: real assume x: "x \<ge> a"
    have "integral {a..x} (\<lambda>u. u powr p * ln u powr (p' - 1) / u powr (p + 1)) =
          integral {a..x} (\<lambda>u. ln u powr (p' - 1) / u)" using x a x0_less_x1
      by (intro Henstock_Kurzweil_Integration.integral_cong) (simp_all add: powr_add)
    also have "... = inverse p' * (ln x powr p' - ln a powr p')"
      using p' x0_less_x1 a(1) x by (simp add: integral_ln_powr_over_x)
    also have "x powr p * (1 + ...) = c * x powr p + d * x powr p * ln x powr p'"
      using p' by (simp add: algebra_simps c_def d_def e_def)
    finally show "x powr p * (1+integral {a..x} (\<lambda>u. u powr p * ln u powr (p'-1) / u powr (p+1))) =
                  c * x powr p + d * x powr p * ln x powr p'" .
  qed
qed

private lemma master_integral'':
  fixes a p p' :: real
  assumes a: "a > 1"
  shows "(\<lambda>x::nat. x powr p * (1 + integral {a..x} (\<lambda>u. u powr p * ln u powr - 1/u powr (p+1)))) \<in>
           \<Theta>(\<lambda>x::nat. x powr p * ln (ln x))"
proof (rule landau_real_nat_transfer)
  have "(\<lambda>x::real. x powr p * (1 + integral {a..x} (\<lambda>u. u powr p * ln u powr - 1/u powr (p+1)))) \<in>
          \<Theta>(\<lambda>x::real. (1 - ln (ln a)) * x powr p + x powr p * ln (ln x))" (is "?f \<in> _")
    apply (rule bigthetaI_cong) using eventually_ge_at_top[of a]
  proof eventually_elim
    fix x assume x: "x \<ge> a"
    have "integral {a..x} (\<lambda>u. u powr p * ln u powr -1 / u powr (p + 1)) =
          integral {a..x} (\<lambda>u. inverse (u * ln u))" using x a x0_less_x1
      by (intro Henstock_Kurzweil_Integration.integral_cong) (simp_all add: powr_add powr_minus field_simps)
    also have "... = ln (ln x) - ln (ln a)"
      using x0_less_x1 a(1) x by (subst integral_one_over_x_ln_x) simp_all
    also have "x powr p * (1 + ...) = (1 - ln (ln a)) * x powr p + x powr p * ln (ln x)"
      by (simp add: algebra_simps)
    finally show "x powr p * (1 + integral {a..x} (\<lambda>u. u powr p * ln u powr - 1 / u powr (p+1))) =
                    (1 - ln (ln a)) * x powr p + x powr p * ln (ln x)" .
  qed
  also have "(\<lambda>x. (1 - ln (ln a)) * x powr p + x powr p * ln (ln x)) \<in>
                \<Theta>(\<lambda>x. x powr p * ln (ln x))" by simp
  finally show "?f \<in> \<Theta>(\<lambda>a. a powr p * ln (ln a))" .
qed



lemma master1_bigo:
  assumes g_bigo: "g \<in> O(\<lambda>x. real x powr p')"
  assumes less_p': "(\<Sum>i<k. as!i * bs!i powr p') > 1"
  shows "f \<in> O(\<lambda>x. real x powr p)"
proof-
  interpret akra_bazzi_upper x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>x. x powr p'"
    using assms growths g_bigo master_integrable by unfold_locales (assumption | simp)+
  from less_p' have less_p: "p' < p" by (rule p_greaterI)
  from bigo_f[of "0"] guess a . note a = this
  note a(2)
  also from a(1) less_p x0_less_x1 have "p \<noteq> p'" by simp_all
  from master_integral[OF this a(1)] guess c d . note cd = this
  note cd(3)
  also from cd(1,2) less_p
    have "(\<lambda>x::nat. d * real x powr p + c * real x powr p') \<in> \<Theta>(\<lambda>x. real x powr p)" by force
  finally show "f \<in> O(\<lambda>x::nat. x powr p)" .
qed


lemma master1:
  assumes g_bigo: "g \<in> O(\<lambda>x. real x powr p')"
  assumes less_p': "(\<Sum>i<k. as!i * bs!i powr p') > 1"
  assumes f_pos:  "eventually (\<lambda>x. f x > 0) at_top"
  shows "f \<in> \<Theta>(\<lambda>x. real x powr p)"
proof (rule bigthetaI)
  interpret akra_bazzi_lower x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>_. 0"
    using assms(1,3) bs_lower_bound by unfold_locales (auto intro: always_eventually)
  from bigomega_f show "f \<in> \<Omega>(\<lambda>x. real x powr p)" by force
qed (fact master1_bigo[OF g_bigo less_p'])

lemma master2_3:
  assumes g_bigtheta: "g \<in> \<Theta>(\<lambda>x. real x powr p * ln (real x) powr (p' - 1))"
  assumes p': "p' > 0"
  shows "f \<in> \<Theta>(\<lambda>x. real x powr p * ln (real x) powr p')"
proof-
  have "eventually (\<lambda>x::real. x powr p * ln x powr (p' - 1) > 0) at_top"
    using eventually_gt_at_top[of "1::real"] by eventually_elim simp
  hence "eventually (\<lambda>x. f x > 0) at_top"
    by (rule f_pos[OF bigthetaD2[OF g_bigtheta] eventually_nat_real])
  then interpret akra_bazzi x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>x. x powr p * ln x powr (p' - 1)"
    using assms growths bounds master_integrable by unfold_locales (assumption | simp)+
  from bigtheta_f[of "1"] guess a . note a = this
  note a(2)
  also from a(1) p' have "p' \<noteq> 0" by simp_all
  from master_integral'[OF this a(1), of p] guess c d . note cd = this
  note cd(3)
  also have "(\<lambda>x::nat. c * real x powr p + d * real x powr p * ln (real x) powr p') \<in>
                 \<Theta>(\<lambda>x::nat. x powr p * ln x powr p')" using cd(1,2) p' by force
  finally show "f \<in> \<Theta>(\<lambda>x. real x powr p * ln (real x) powr p')" .
qed

lemma master2_1:
  assumes g_bigtheta: "g \<in> \<Theta>(\<lambda>x. real x powr p * ln (real x) powr p')"
  assumes p': "p' < -1"
  shows "f \<in> \<Theta>(\<lambda>x. real x powr p)"
proof-
  have "eventually (\<lambda>x::real. x powr p * ln x powr p' > 0) at_top"
    using eventually_gt_at_top[of "1::real"] by eventually_elim simp
  hence "eventually (\<lambda>x. f x > 0) at_top"
    by (rule f_pos[OF bigthetaD2[OF g_bigtheta] eventually_nat_real])
  then interpret akra_bazzi x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>x. x powr p * ln x powr p'"
    using assms growths bounds master_integrable by unfold_locales (assumption | simp)+
  from bigtheta_f[of "1"] guess a . note a = this
  note a(2)
  also from a(1) p' have A: "p' + 1 \<noteq> 0" by simp_all
  obtain c d :: real where cd: "c \<noteq> 0" "d \<noteq> 0" and
    "(\<lambda>x::nat. x powr p * (1 + integral {a..x} (\<lambda>u. u powr p * ln u powr p'/ u powr (p+1)))) \<in>
       \<Theta>(\<lambda>x::nat. c * x powr p + d * x powr p * ln x powr (p' + 1))"
    by (rule master_integral'[OF A a(1), of p]) (insert p', simp)
  note this(3)
  also have "(\<lambda>x::nat. c * real x powr p + d * real x powr p * ln (real x) powr (p' + 1)) \<in>
                 \<Theta>(\<lambda>x::nat. x powr p)" using cd(1,2) p' by force
  finally show "f \<in> \<Theta>(\<lambda>x::nat. x powr p)" .
qed

lemma master2_2:
  assumes g_bigtheta: "g \<in> \<Theta>(\<lambda>x. real x powr p / ln (real x))"
  shows "f \<in> \<Theta>(\<lambda>x. real x powr p * ln (ln (real x)))"
proof-
  have "eventually (\<lambda>x::real. x powr p / ln x > 0) at_top"
    using eventually_gt_at_top[of "1::real"] by eventually_elim simp
  hence "eventually (\<lambda>x. f x > 0) at_top"
    by (rule f_pos[OF bigthetaD2[OF g_bigtheta] eventually_nat_real])
  moreover from g_bigtheta have g_bigtheta': "g \<in> \<Theta>(\<lambda>x. real x powr p * ln (real x) powr -1)"
    by (rule landau_theta.trans, intro landau_real_nat_transfer) simp
  ultimately interpret akra_bazzi x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>x. x powr p * ln x powr -1"
    using assms growths bounds master_integrable by unfold_locales (assumption | simp)+
  from bigtheta_f[of 1] guess a . note a = this
  note a(2)
  also note master_integral''[OF a(1)]
  finally show "f \<in> \<Theta>(\<lambda>x::nat. x powr p * ln (ln x))" .
qed

lemma master3:
  assumes g_bigtheta: "g \<in> \<Theta>(\<lambda>x. real x powr p')"
  assumes p'_greater': "(\<Sum>i<k. as!i * bs!i powr p') < 1"
  shows "f \<in> \<Theta>(\<lambda>x. real x powr p')"
proof-
  have "eventually (\<lambda>x::real. x powr p' > 0) at_top"
    using eventually_gt_at_top[of "1::real"] by eventually_elim simp
  hence "eventually (\<lambda>x. f x > 0) at_top"
    by (rule f_pos[OF bigthetaD2[OF g_bigtheta] eventually_nat_real])
  then interpret akra_bazzi x\<^sub>0 x\<^sub>1 k as bs ts f
    "\<lambda>f a b. f integrable_on {a..b}" "\<lambda>f a b. integral {a..b} f" g "\<lambda>x. x powr p'"
    using assms growths bounds master_integrable by unfold_locales (assumption | simp)+
  from p'_greater' have p'_greater: "p' > p" by (rule p_lessI)
  from bigtheta_f[of 0] guess a . note a = this
  note a(2)
  also from p'_greater have "p \<noteq> p'" by simp
  from master_integral[OF this a(1)] guess c d . note cd = this
  note cd(3)
  also have "(\<lambda>x::nat. d * x powr p + c * x powr p') \<in> \<Theta>(\<lambda>x::real. x powr p')"
    using p'_greater cd(1,2) by force
  finally show "f \<in> \<Theta>(\<lambda>x. real x powr p')" .
qed

end
end

end
