(*
  File:   Akra_Bazzi_Real.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  The continuous version of the Akra-Bazzi theorem for functions on the reals.
*)

section \<open>The continuous Akra-Bazzi theorem\<close>
theory Akra_Bazzi_Real
imports
  Complex_Main
  Akra_Bazzi_Asymptotics
begin

text \<open>
  We want to be generic over the integral definition used; we fix some arbitrary
  notions of integrability and integral and assume just the properties we need.
  The user can then instantiate the theorems with any desired integral definition.
\<close>
locale akra_bazzi_integral =
  fixes integrable :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
    and integral   :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  assumes integrable_const: "c \<ge> 0 \<Longrightarrow> integrable (\<lambda>_. c) a b"
      and integral_const:   "c \<ge> 0 \<Longrightarrow> a \<le> b \<Longrightarrow> integral (\<lambda>_. c) a b = (b - a) * c"
      and integrable_subinterval:
            "integrable f a b \<Longrightarrow> a \<le> a' \<Longrightarrow> b' \<le> b \<Longrightarrow> integrable f a' b'"
      and integral_le:
            "integrable f a b \<Longrightarrow> integrable g a b \<Longrightarrow> (\<And>x. x \<in> {a..b} \<Longrightarrow> f x \<le> g x) \<Longrightarrow>
                 integral f a b \<le> integral g a b"
      and integral_combine:
            "a \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> integrable f a b \<Longrightarrow>
                 integral f a c + integral f c b = integral f a b"
begin
lemma integral_nonneg:
  "a \<le> b \<Longrightarrow> integrable f a b \<Longrightarrow> (\<And>x. x \<in> {a..b} \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> integral f a b \<ge> 0"
  using integral_le[OF integrable_const[of 0], of f a b]  by (simp add: integral_const)
end


declare sum.cong[fundef_cong]

lemma strict_mono_imp_ex1_real:
  fixes f :: "real \<Rightarrow> real"
  assumes lim_neg_inf: "LIM x at_bot. f x :> at_top"
  assumes lim_inf: "(f \<longlongrightarrow> z) at_top"
  assumes mono: "\<And>a b. a < b \<Longrightarrow> f b < f a"
  assumes cont: "\<And>x. isCont f x"
  assumes y_greater_z: "z < y"
  shows   "\<exists>!x. f x = y"
proof (rule ex_ex1I)
  fix a b assume "f a = y" "f b = y"
  thus "a = b" by (cases rule: linorder_cases[of a b]) (auto dest: mono)
next
  from lim_neg_inf have "eventually (\<lambda>x. y \<le> f x) at_bot" by (subst (asm) filterlim_at_top) simp
  then obtain l where l: "\<And>x. x \<le> l \<Longrightarrow> y \<le> f x" by (subst (asm) eventually_at_bot_linorder) auto

  from order_tendstoD(2)[OF lim_inf y_greater_z]
    obtain u where u: "\<And>x. x \<ge> u \<Longrightarrow> f x < y" by (subst (asm) eventually_at_top_linorder) auto
  define a where "a = min l u"
  define b where "b = max l u"
  have a: "f a \<ge> y" unfolding a_def by (intro l) simp
  moreover have b: "f b < y" unfolding b_def by (intro u) simp
  moreover have a_le_b: "a \<le> b" by (simp add: a_def b_def)
  ultimately have "\<exists>x\<ge>a. x \<le> b \<and> f x = y" using cont by (intro IVT2) auto
  thus "\<exists>x. f x = y" by blast
qed

text \<open>The parameter @{term "p"} in the Akra-Bazzi theorem always exists and is unique.\<close>

definition akra_bazzi_exponent :: "real list \<Rightarrow> real list \<Rightarrow> real" where
  "akra_bazzi_exponent as bs \<equiv> (THE p. (\<Sum>i<length as. as!i * bs!i powr p) = 1)"

locale akra_bazzi_params =
  fixes k :: nat and as bs :: "real list"
  assumes length_as: "length as = k"
  and     length_bs: "length bs = k"
  and     k_not_0:   "k \<noteq> 0"
  and     a_ge_0:    "a \<in> set as \<Longrightarrow> a \<ge> 0"
  and     b_bounds:  "b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"
begin

abbreviation p :: real where "p \<equiv> akra_bazzi_exponent as bs"

lemma p_def: "p = (THE p. (\<Sum>i<k. as!i * bs!i powr p) = 1)"
  by (simp add: akra_bazzi_exponent_def length_as)

lemma b_pos: "b \<in> set bs \<Longrightarrow> b > 0" and b_less_1: "b \<in> set bs \<Longrightarrow> b < 1"
  using b_bounds by simp_all

lemma as_nonempty [simp]: "as \<noteq> []" and bs_nonempty [simp]: "bs \<noteq> []"
  using length_as length_bs k_not_0 by auto

lemma a_in_as[intro, simp]: "i < k \<Longrightarrow> as ! i \<in> set as"
  by (rule nth_mem) (simp add: length_as)

lemma b_in_bs[intro, simp]: "i < k \<Longrightarrow> bs ! i \<in> set bs"
  by (rule nth_mem) (simp add: length_bs)

end


locale akra_bazzi_params_nonzero =
  fixes k :: nat and as bs :: "real list"
  assumes length_as: "length as = k"
  and     length_bs: "length bs = k"
  and     a_ge_0:    "a \<in> set as \<Longrightarrow> a \<ge> 0"
  and     ex_a_pos:  "\<exists>a\<in>set as. a > 0"
  and     b_bounds:  "b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"
begin

sublocale akra_bazzi_params k as bs
 by unfold_locales (insert length_as length_bs a_ge_0 ex_a_pos b_bounds, auto)

lemma akra_bazzi_p_strict_mono:
  assumes "x < y"
  shows "(\<Sum>i<k. as!i * bs!i powr y) < (\<Sum>i<k. as!i * bs!i powr x)"
proof (intro sum_strict_mono_ex1 ballI)
  from ex_a_pos obtain a where "a \<in> set as" "a > 0" by blast
  then obtain i where "i < k" "as!i > 0" by (force simp: in_set_conv_nth length_as)
  with b_bounds \<open>x < y\<close> have "as!i * bs!i powr y < as!i * bs!i powr x"
    by (intro mult_strict_left_mono powr_less_mono') auto
  with \<open>i < k\<close> show "\<exists>i\<in>{..<k}. as!i * bs!i powr y < as!i * bs!i powr x" by blast
next
  fix i assume "i \<in> {..<k}"
  with a_ge_0 b_bounds[of "bs!i"] \<open>x < y\<close> show "as!i * bs!i powr y \<le> as!i * bs!i powr x"
    by (intro mult_left_mono powr_mono') simp_all
qed simp_all

lemma akra_bazzi_p_mono:
  assumes "x \<le> y"
  shows "(\<Sum>i<k. as!i * bs!i powr y) \<le> (\<Sum>i<k. as!i * bs!i powr x)"
apply (cases "x < y")
using akra_bazzi_p_strict_mono[of x y] assms apply simp_all
done


lemma akra_bazzi_p_unique:
  "\<exists>!p. (\<Sum>i<k. as!i * bs!i powr p) = 1"
proof (rule strict_mono_imp_ex1_real)
  from as_nonempty have [simp]: "k > 0" by (auto simp: length_as[symmetric])
  have [simp]: "\<And>i. i < k \<Longrightarrow> as!i \<ge> 0" by (rule a_ge_0) simp
  from ex_a_pos obtain a where "a \<in> set as" "a > 0" by blast
  then obtain i where i: "i < k" "as!i > 0" by (force simp: in_set_conv_nth length_as)

  hence "LIM p at_bot. as!i * bs!i powr p :> at_top" using b_bounds i
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const] real_powr_at_bot_neg) simp_all
  moreover have "\<forall>p. as!i*bs!i powr p \<le> (\<Sum>i\<in>{..<k}. as ! i * bs ! i powr p)"
  proof
    fix p :: real
    from a_ge_0 b_bounds have "(\<Sum>i\<in>{..<k}-{i}. as ! i * bs ! i powr p) \<ge> 0"
      by (intro sum_nonneg mult_nonneg_nonneg) simp_all
    also have "as!i * bs!i powr p + ... = (\<Sum>i\<in>insert i {..<k}. as ! i * bs ! i powr p)"
      by (simp add: sum.insert_remove)
    also from i have "insert i {..<k} = {..<k}" by blast
    finally show "as!i*bs!i powr p \<le> (\<Sum>i\<in>{..<k}. as ! i * bs ! i powr p)" by simp
  qed
  ultimately show "LIM p at_bot. \<Sum>i<k. as ! i * bs ! i powr p :> at_top"
    by (rule filterlim_at_top_mono[OF _ always_eventually])
next
  from b_bounds show "((\<lambda>x. \<Sum>i<k. as ! i * bs ! i powr x) \<longlongrightarrow> (\<Sum>i<k. 0)) at_top"
    by (intro tendsto_sum tendsto_mult_right_zero real_powr_at_top_neg) simp_all
next
  fix x
  from b_bounds have A: "\<And>i. i < k \<Longrightarrow> bs ! i > 0" by simp
  show "isCont (\<lambda>x. \<Sum>i<k. as ! i * bs ! i powr x) x"
    using b_bounds[OF nth_mem] by (intro continuous_intros) (auto dest: A)
qed (simp_all add: akra_bazzi_p_strict_mono)

lemma p_props:  "(\<Sum>i<k. as!i * bs!i powr p) = 1"
  and p_unique: "(\<Sum>i<k. as!i * bs!i powr p') = 1 \<Longrightarrow> p = p'"
proof-
  from theI'[OF akra_bazzi_p_unique] the1_equality[OF akra_bazzi_p_unique]
    show "(\<Sum>i<k. as!i * bs!i powr p) = 1" "(\<Sum>i<k. as!i * bs!i powr p') = 1 \<Longrightarrow> p = p'"
    unfolding p_def by - blast+
qed

lemma p_greaterI: "1 < (\<Sum>i<k. as!i * bs!i powr p') \<Longrightarrow> p' < p"
  by (rule disjE[OF le_less_linear, of p p'], drule akra_bazzi_p_mono, subst (asm) p_props, simp_all)

lemma p_lessI: "1 > (\<Sum>i<k. as!i * bs!i powr p') \<Longrightarrow> p' > p"
  by (rule disjE[OF le_less_linear, of p' p], drule akra_bazzi_p_mono, subst (asm) p_props, simp_all)

lemma p_geI: "1 \<le> (\<Sum>i<k. as!i * bs!i powr p') \<Longrightarrow> p' \<le> p"
  by (rule disjE[OF le_less_linear, of p' p], simp, drule akra_bazzi_p_strict_mono,
      subst (asm) p_props, simp_all)

lemma p_leI: "1 \<ge> (\<Sum>i<k. as!i * bs!i powr p') \<Longrightarrow> p' \<ge> p"
  by (rule disjE[OF le_less_linear, of p p'], simp, drule akra_bazzi_p_strict_mono,
      subst (asm) p_props, simp_all)

lemma p_boundsI: "(\<Sum>i<k. as!i * bs!i powr x) \<le> 1 \<and> (\<Sum>i<k. as!i * bs!i powr y) \<ge> 1 \<Longrightarrow> p \<in> {y..x}"
  by (elim conjE, drule p_leI, drule p_geI, simp)

lemma p_boundsI': "(\<Sum>i<k. as!i * bs!i powr x) < 1 \<and> (\<Sum>i<k. as!i * bs!i powr y) > 1 \<Longrightarrow> p \<in> {y<..<x}"
  by (elim conjE, drule p_lessI, drule p_greaterI, simp)

lemma p_nonneg: "sum_list as \<ge> 1 \<Longrightarrow> p \<ge> 0"
proof (rule p_geI)
  assume "sum_list as \<ge> 1"
  also have "... = (\<Sum>i<k. as!i)" by (simp add: sum_list_sum_nth length_as atLeast0LessThan)
  also {
    fix i assume "i < k"
    with b_bounds have "bs!i > 0" by simp
    hence "as!i * bs!i powr 0 = as!i" by simp
  }
  hence "(\<Sum>i<k. as!i) = (\<Sum>i<k. as!i * bs!i powr 0)" by (intro sum.cong) simp_all
  finally show "1 \<le> (\<Sum>i<k. as ! i * bs ! i powr 0)" .
qed

end


locale akra_bazzi_real_recursion =
  fixes as bs :: "real list" and hs :: "(real \<Rightarrow> real) list" and k :: nat and x\<^sub>0 x\<^sub>1 hb e p :: real
  assumes length_as: "length as = k"
  and     length_bs: "length bs = k"
  and     length_hs: "length hs = k"
  and     k_not_0:   "k \<noteq> 0"
  and     a_ge_0:    "a \<in> set as \<Longrightarrow> a \<ge> 0"
  and     b_bounds:  "b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"

  (* The recursively-defined function *)
  and     x0_ge_1:      "x\<^sub>0 \<ge> 1"
  and     x0_le_x1:     "x\<^sub>0 \<le> x\<^sub>1"
  and     x1_ge:        "b \<in> set bs \<Longrightarrow> x\<^sub>1 \<ge> 2 * x\<^sub>0 * inverse b"
  (* Bounds on the variation functions *)
  and     e_pos:        "e > 0"
  and     h_bounds:     "x \<ge> x\<^sub>1 \<Longrightarrow> h \<in> set hs \<Longrightarrow> \<bar>h x\<bar> \<le> hb * x / ln x powr (1 + e)"
  (* Asymptotic inequalities *)
  and     asymptotics:  "x \<ge> x\<^sub>0 \<Longrightarrow> b \<in> set bs \<Longrightarrow> akra_bazzi_asymptotics b hb e p x"
begin

sublocale akra_bazzi_params k as bs
  using length_as length_bs k_not_0 a_ge_0 b_bounds by unfold_locales

lemma h_in_hs[intro, simp]: "i < k \<Longrightarrow> hs ! i \<in> set hs"
  by (rule nth_mem) (simp add: length_hs)

lemma x1_gt_1: "x\<^sub>1 > 1"
proof-
  from bs_nonempty obtain b where "b \<in> set bs" by (cases bs) auto
  from b_pos[OF this] b_less_1[OF this] x0_ge_1 have "1 < 2 * x\<^sub>0 * inverse b"
    by (simp add: field_simps)
  also from x1_ge and \<open>b \<in> set bs\<close> have "... \<le> x\<^sub>1" by simp
  finally show ?thesis .
qed

lemma x1_ge_1: "x\<^sub>1 \<ge> 1" using x1_gt_1 by simp

lemma x1_pos: "x\<^sub>1 > 0" using x1_ge_1 by simp

lemma bx_le_x: "x \<ge> 0 \<Longrightarrow> b \<in> set bs \<Longrightarrow>  b * x \<le> x"
  using b_pos[of b] b_less_1[of b] by (intro mult_left_le_one_le) (simp_all)

lemma x0_pos: "x\<^sub>0 > 0" using x0_ge_1 by simp

lemma
  assumes "x \<ge> x\<^sub>0" "b \<in> set bs"
  shows x0_hb_bound0: "hb / ln x powr (1 + e) < b/2"
  and   x0_hb_bound1: "hb / ln x powr (1 + e) < (1 - b) / 2"
  and   x0_hb_bound2: "x*(1 - b - hb / ln x powr (1 + e)) > 1"
using asymptotics[OF assms] unfolding akra_bazzi_asymptotic_defs by blast+

lemma step_diff:
  assumes "i < k" "x \<ge> x\<^sub>1"
  shows   "bs ! i * x + (hs ! i) x + 1 < x"
proof-
  have "bs ! i * x + (hs ! i) x + 1 \<le> bs ! i * x + \<bar>(hs ! i) x\<bar> + 1" by simp
  also from assms have "\<bar>(hs ! i) x\<bar> \<le> hb * x / ln x powr (1 + e)" by (simp add: h_bounds)
  also from assms x0_le_x1 have "x*(1 - bs ! i - hb / ln x powr (1 + e)) > 1"
    by (simp add: x0_hb_bound2)
  hence "bs ! i * x + hb * x / ln x powr (1 + e) + 1 < x" by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma step_le_x: "i < k \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> bs ! i * x + (hs ! i) x \<le> x"
  by (drule (1) step_diff) simp

lemma x0_hb_bound0': "\<And>x b. x \<ge> x\<^sub>0 \<Longrightarrow> b \<in> set bs \<Longrightarrow> hb / ln x powr (1 + e) < b"
  by (drule (1) x0_hb_bound0, erule less_le_trans) (simp add: b_pos)

lemma step_pos:
  assumes "i < k" "x \<ge> x\<^sub>1"
  shows   "bs ! i * x + (hs ! i) x > 0"
proof-
  from assms x0_le_x1 have "hb / ln x powr (1 + e) < bs ! i" by (simp add: x0_hb_bound0')
  with assms x0_pos x0_le_x1 have "x * 0 < x * (bs ! i - hb / ln x powr (1 + e))" by simp
  also have "... = bs ! i * x - hb * x / ln x powr (1 + e)"
    by (simp add: algebra_simps)
  also from assms have "-hb * x / ln x powr (1 + e) \<le> -\<bar>(hs ! i) x\<bar>" by (simp add: h_bounds)
  hence "bs ! i * x - hb * x / ln x powr (1 + e) \<le> bs ! i * x + -\<bar>(hs ! i) x\<bar>" by simp
  also have "-\<bar>(hs ! i) x\<bar> \<le> (hs ! i) x" by simp
  finally show "bs ! i * x + (hs ! i) x > 0" by simp
qed

lemma step_nonneg: "i < k \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> bs ! i * x + (hs ! i) x \<ge> 0"
  by (drule (1) step_pos) simp

lemma step_nonneg': "i < k \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> bs ! i + (hs ! i) x / x \<ge> 0"
  by (frule (1) step_nonneg, insert x0_pos x0_le_x1) (simp_all add: field_simps)

lemma hb_nonneg: "hb \<ge> 0"
proof-
  from k_not_0 and length_hs have "hs \<noteq> []" by auto
  then obtain h where h: "h \<in> set hs" by (cases hs) auto
  have "0 \<le> \<bar>h x\<^sub>1\<bar>" by simp
  also from h have "\<bar>h x\<^sub>1\<bar> \<le> hb * x\<^sub>1 / ln x\<^sub>1 powr (1+e)" by (intro h_bounds) simp_all
  finally have "0 \<le> hb * x\<^sub>1 / ln x\<^sub>1 powr (1 + e)" .
  hence "0 \<le> ... * (ln x\<^sub>1 powr (1 + e) / x\<^sub>1)"
    by (rule mult_nonneg_nonneg) (intro divide_nonneg_nonneg, insert x1_pos, simp_all)
  also have "... = hb" using x1_gt_1 by (simp add: field_simps)
  finally show ?thesis .
qed

lemma x0_hb_bound3:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "x - (bs ! i * x + (hs ! i) x) \<le> x"
proof-
  have "-(hs ! i) x \<le> \<bar>(hs ! i) x\<bar>" by simp
  also from assms have "... \<le> hb * x / ln x powr (1 + e)" by (simp add: h_bounds)
  also have "... = x * (hb / ln x powr (1 + e))" by simp
  also from assms x0_pos x0_le_x1 have "... < x * bs ! i"
    by (intro mult_strict_left_mono x0_hb_bound0') simp_all
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma x0_hb_bound4:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "(bs ! i + (hs ! i) x / x) > bs ! i / 2"
proof-
  from assms x0_le_x1 have "hb / ln x powr (1 + e) < bs ! i / 2" by (intro x0_hb_bound0) simp_all
  with assms x0_pos x0_le_x1 have "(-bs ! i / 2) * x < (-hb / ln x powr (1 + e)) * x"
    by (intro mult_strict_right_mono) simp_all
  also from assms x0_pos have "... \<le> -\<bar>(hs ! i) x\<bar>" using h_bounds by simp
  also have "... \<le> (hs ! i) x" by simp
  finally show ?thesis using assms x1_pos by (simp add: field_simps)
qed

lemma x0_hb_bound4': "x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> (bs ! i + (hs ! i) x / x) \<ge> bs ! i / 2"
  by (drule (1) x0_hb_bound4) simp

lemma x0_hb_bound5:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "(bs ! i + (hs ! i) x / x) \<le> bs ! i * 3/2"
proof-
  have "(hs ! i) x \<le> \<bar>(hs ! i) x\<bar>" by simp
  also from assms have "... \<le> hb * x / ln x powr (1 + e)" by (simp add: h_bounds)
  also have "... = x * (hb / ln x powr (1 + e))" by simp
  also from assms x0_pos x0_le_x1 have "... < x * (bs ! i / 2)"
    by (intro mult_strict_left_mono x0_hb_bound0) simp_all
  finally show ?thesis using assms x1_pos by (simp add: field_simps)
qed

lemma x0_hb_bound6:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "x * ((1 - bs ! i) / 2) \<le> x - (bs ! i * x + (hs ! i) x)"
proof-
  from assms x0_le_x1 have "hb / ln x powr (1 + e) < (1 - bs ! i) / 2" using x0_hb_bound1 by simp
  with assms x1_pos have "x * ((1 - bs ! i) / 2) \<le> x * (1 - (bs ! i + hb / ln x powr (1 + e)))"
    by (intro mult_left_mono) (simp_all add: field_simps)
  also have "... = x - bs ! i * x + -hb * x / ln x powr (1 + e)" by (simp add: algebra_simps)
  also from h_bounds assms have "-hb * x / ln x powr (1 + e) \<le> -\<bar>(hs ! i) x\<bar>"
    by (simp add: length_hs)
  also have "... \<le> -(hs ! i) x" by simp
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma x0_hb_bound7:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "bs!i*x + (hs!i) x > x\<^sub>0"
proof-
  from assms x0_le_x1 have x': "x \<ge> x\<^sub>0" by simp
  from x1_ge assms have "2 * x\<^sub>0 * inverse (bs!i) \<le> x\<^sub>1" by simp
  with assms b_pos have "x\<^sub>0 \<le> x\<^sub>1 * (bs!i / 2)" by (simp add: field_simps)
  also from assms x' have "bs!i/2 < bs!i + (hs!i) x / x" by (intro x0_hb_bound4)
  also from assms step_nonneg' x' have "x\<^sub>1 * ... \<le> x * ..." by (intro mult_right_mono) (simp_all)
  also from assms x1_pos have "x * (bs!i + (hs!i) x / x) = bs!i*x + (hs!i) x"
    by (simp add: field_simps)
  finally show ?thesis using x1_pos by simp
qed

lemma x0_hb_bound7': "x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> bs!i*x + (hs!i) x > 1"
  by (rule le_less_trans[OF _ x0_hb_bound7]) (insert x0_le_x1 x0_ge_1, simp_all)

lemma x0_hb_bound8:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "bs!i*x - hb * x / ln x powr (1+e) > x\<^sub>0"
proof-
  from assms have "2 * x\<^sub>0 * inverse (bs!i) \<le> x\<^sub>1" by (intro x1_ge) simp_all
  with b_pos assms have "x\<^sub>0 \<le> x\<^sub>1 * (bs!i/2)" by (simp add: field_simps)
  also from assms b_pos have "... \<le> x * (bs!i/2)" by simp
  also from assms x0_le_x1 have "hb / ln x powr (1+e) < bs!i/2" by (intro x0_hb_bound0) simp_all
  with assms have "bs!i/2 < bs!i - hb / ln x powr (1+e)" by (simp add: field_simps)
  also have "x * ... = bs!i*x - hb * x / ln x powr (1+e)" by (simp add: algebra_simps)
  finally show ?thesis using assms x1_pos by (simp add: field_simps)
qed

lemma x0_hb_bound8':
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "bs!i*x + hb * x / ln x powr (1+e) > x\<^sub>0"
proof-
  from assms have "x\<^sub>0 < bs!i*x - hb * x / ln x powr (1+e)" by (rule x0_hb_bound8)
  also from assms hb_nonneg x1_pos have "hb * x / ln x powr (1+e) \<ge> 0"
    by (intro mult_nonneg_nonneg divide_nonneg_nonneg) simp_all
  hence "bs!i*x - hb * x / ln x powr (1+e) \<le> bs!i*x + hb * x / ln x powr (1+e)" by simp
  finally show ?thesis .
qed

lemma
  assumes "x \<ge> x\<^sub>0"
  shows   asymptotics1: "i < k \<Longrightarrow> 1 + ln x powr (- e / 2) \<le>
             (1 - hb * inverse (bs!i) * ln x powr -(1+e)) powr p *
             (1 + ln (bs!i*x + hb*x/ln x powr (1+e)) powr (-e/2))"
  and     asymptotics2: "i < k \<Longrightarrow> 1 - ln x powr (- e / 2) \<ge>
             (1 + hb * inverse (bs!i) * ln x powr -(1+e)) powr p *
             (1 - ln (bs!i*x + hb*x/ln x powr (1+e)) powr (-e/2))"
  and     asymptotics1': "i < k \<Longrightarrow> 1 + ln x powr (- e / 2) \<le>
             (1 + hb * inverse (bs!i) * ln x powr -(1+e)) powr p *
             (1 + ln (bs!i*x + hb*x/ln x powr (1+e)) powr (-e/2))"
  and     asymptotics2': "i < k \<Longrightarrow> 1 - ln x powr (- e / 2) \<ge>
             (1 - hb * inverse (bs!i) * ln x powr -(1+e)) powr p *
             (1 - ln (bs!i*x + hb*x/ln x powr (1+e)) powr (-e/2))"
  and     asymptotics3: "(1 + ln x powr (- e / 2)) / 2 \<le> 1"
  and     asymptotics4: "(1 - ln x powr (- e / 2)) * 2 \<ge> 1"
  and     asymptotics5: "i < k \<Longrightarrow> ln (bs!i*x - hb*x*ln x powr -(1+e)) powr (-e/2) < 1"
apply -
using assms asymptotics[of x "bs!i"] unfolding akra_bazzi_asymptotic_defs
apply simp_all[4]
using assms asymptotics[of x "bs!0"] unfolding akra_bazzi_asymptotic_defs
apply simp_all[2]
using assms asymptotics[of x "bs!i"] unfolding akra_bazzi_asymptotic_defs
apply simp_all
done


lemma x0_hb_bound9:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "ln (bs!i*x + (hs!i) x) powr -(e/2) < 1"
proof-
  from b_pos assms have "0 < bs!i/2" by simp
  also from assms x0_le_x1 have "... < bs!i + (hs!i) x / x" by (intro x0_hb_bound4) simp_all
  also from assms x1_pos have "x * ... = bs!i*x + (hs!i) x" by (simp add: field_simps)
  finally have pos: "bs!i*x + (hs!i) x > 0" using assms x1_pos by simp
  from x0_hb_bound8[OF assms] x0_ge_1 have pos': "bs!i*x - hb * x / ln x powr (1+e) > 1" by simp

  from assms have "-(hb * x / ln x powr (1+e)) \<le> -\<bar>(hs!i) x\<bar>"
    by (intro le_imp_neg_le h_bounds) simp_all
  also have "... \<le> (hs!i) x" by simp
  finally have "ln (bs!i*x - hb * x / ln x powr (1+e)) \<le> ln (bs!i*x + (hs!i) x)"
    using assms b_pos x0_pos pos' by (intro ln_mono mult_pos_pos pos) simp_all
  hence "ln (bs!i*x + (hs!i) x) powr -(e/2) \<le> ln (bs!i*x - hb * x / ln x powr (1+e)) powr -(e/2)"
    using assms e_pos asymptotics5[of x] pos' by (intro powr_mono2' ln_gt_zero) simp_all
  also have "... < 1" using asymptotics5[of x i] assms x0_le_x1
    by (subst (asm) powr_minus) (simp_all add: field_simps)
  finally show ?thesis .
qed


definition akra_bazzi_measure :: "real \<Rightarrow> nat" where
  "akra_bazzi_measure x = nat \<lceil>x\<rceil>"

lemma akra_bazzi_measure_decreases:
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "akra_bazzi_measure (bs!i*x + (hs!i) x) < akra_bazzi_measure x"
proof-
  from step_diff assms have "(bs!i * x + (hs!i) x) + 1 < x" by (simp add: algebra_simps)
  hence "\<lceil>(bs!i * x + (hs!i) x) + 1\<rceil> \<le> \<lceil>x\<rceil>" by (intro ceiling_mono) simp
  hence "\<lceil>(bs!i * x + (hs!i) x)\<rceil> < \<lceil>x\<rceil>" by simp
  with assms x1_pos have "nat \<lceil>(bs!i * x + (hs!i) x)\<rceil> < nat \<lceil>x\<rceil>" by (subst nat_mono_iff) simp_all
  thus ?thesis unfolding akra_bazzi_measure_def .
qed


lemma akra_bazzi_induct[consumes 1, case_names base rec]:
  assumes "x \<ge> x\<^sub>0"
  assumes base: "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> P x"
  assumes rec:  "\<And>x. x > x\<^sub>1 \<Longrightarrow> (\<And>i. i < k \<Longrightarrow> P (bs!i*x + (hs!i) x)) \<Longrightarrow> P x"
  shows   "P x"
proof (insert \<open>x \<ge> x\<^sub>0\<close>, induction "akra_bazzi_measure x" arbitrary: x rule: less_induct)
  case less
  show ?case
  proof (cases "x \<le> x\<^sub>1")
    case True
    with base and \<open>x \<ge> x\<^sub>0\<close> show ?thesis .
  next
    case False
    hence x: "x > x\<^sub>1" by simp
    thus ?thesis
    proof (rule rec)
      fix i assume i: "i < k"
      from x0_hb_bound7[OF _ i, of x] x have "bs!i*x + (hs!i) x \<ge> x\<^sub>0" by simp
      with i x show "P (bs ! i * x + (hs ! i) x)"
        by (intro less akra_bazzi_measure_decreases) simp_all
    qed
  qed
qed

end


locale akra_bazzi_real = akra_bazzi_real_recursion +
  fixes integrable integral
  assumes integral: "akra_bazzi_integral integrable integral"
  fixes f :: "real \<Rightarrow> real"
  and   g :: "real \<Rightarrow> real"
  and   C :: real
  assumes p_props:      "(\<Sum>i<k. as!i * bs!i powr p) = 1"
  and     f_base:       "x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f x \<ge> 0"
  and     f_rec:        "x > x\<^sub>1 \<Longrightarrow> f x = g x + (\<Sum>i<k. as!i * f (bs!i * x + (hs!i) x))"
  and     g_nonneg:     "x \<ge> x\<^sub>0 \<Longrightarrow> g x \<ge> 0"
  and     C_bound:      "b \<in> set bs \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> C*x \<le> b*x - hb*x/ln x powr (1+e)"
  and     g_integrable: "x \<ge> x\<^sub>0 \<Longrightarrow> integrable (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x"
begin

interpretation akra_bazzi_integral integrable integral by (rule integral)

lemma akra_bazzi_integrable:
  "a \<ge> x\<^sub>0 \<Longrightarrow> a \<le> b \<Longrightarrow> integrable (\<lambda>x. g x / x powr (p + 1)) a b"
  by (rule integrable_subinterval[OF g_integrable, of b]) simp_all

definition g_approx :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "g_approx i x = x powr p * integral (\<lambda>u. g u / u powr (p + 1)) (bs!i * x + (hs!i) x) x"

lemma f_nonneg: "x \<ge> x\<^sub>0 \<Longrightarrow> f x \<ge> 0"
proof (induction x rule: akra_bazzi_induct)
  case (base x)
  with f_base[of x] show ?case by simp
next
  case (rec x)
  with x0_le_x1 have "g x \<ge> 0" by (intro g_nonneg) simp_all
  moreover {
    fix i assume i: "i < k"
    with rec.IH have "f (bs!i*x + (hs!i) x) \<ge> 0" by simp
    with i have "as!i * f (bs!i*x + (hs!i) x) \<ge> 0"
        by (intro mult_nonneg_nonneg[OF a_ge_0]) simp_all
  }
  hence "(\<Sum>i<k. as!i * f (bs!i*x + (hs!i) x)) \<ge> 0" by (intro sum_nonneg) blast
  ultimately show "f x \<ge> 0" using rec.hyps by (subst f_rec) simp_all
qed


definition f_approx :: "real \<Rightarrow> real" where
  "f_approx x = x powr p * (1 + integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x)"

lemma f_approx_aux:
  assumes "x \<ge> x\<^sub>0"
  shows   "1 + integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x \<ge> 1"
proof-
  from assms have "integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x \<ge> 0"
    by (intro integral_nonneg ballI g_nonneg divide_nonneg_nonneg g_integrable) simp_all
  thus ?thesis by simp
qed

lemma f_approx_pos: "x \<ge> x\<^sub>0 \<Longrightarrow> f_approx x > 0"
  unfolding f_approx_def by (intro mult_pos_pos, insert x0_pos, simp, drule f_approx_aux, simp)

lemma f_approx_nonneg: "x \<ge> x\<^sub>0 \<Longrightarrow> f_approx x \<ge> 0"
  using f_approx_pos[of x] by simp


lemma f_approx_bounded_below:
  obtains c where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f_approx x \<ge> c" "c > 0"
proof-
  {
    fix x assume x: "x \<ge> x\<^sub>0" "x \<le> x\<^sub>1"
    with x0_pos have "x powr p \<ge> min (x\<^sub>0 powr p) (x\<^sub>1 powr p)"
      by (intro powr_lower_bound) simp_all
    with x have "f_approx x \<ge> min (x\<^sub>0 powr p) (x\<^sub>1 powr p) * 1"
      unfolding f_approx_def by (intro mult_mono f_approx_aux) simp_all
  }
  from this x0_pos x1_pos show ?thesis by (intro that[of "min (x\<^sub>0 powr p) (x\<^sub>1 powr p)"]) auto
qed


lemma asymptotics_aux:
  assumes "x \<ge> x\<^sub>1" "i < k"
  assumes "s \<equiv> (if p \<ge> 0 then 1 else -1)"
  shows "(bs!i*x - s*hb*x*ln x powr -(1+e)) powr p \<le> (bs!i*x + (hs!i) x) powr p" (is "?thesis1")
  and   "(bs!i*x + (hs!i) x) powr p \<le> (bs!i*x + s*hb*x*ln x powr -(1+e)) powr p" (is "?thesis2")
proof-
  from assms x1_gt_1 have ln_x_pos: "ln x > 0" by simp
  from assms x1_pos have x_pos: "x > 0" by simp
  from assms x0_le_x1 have *: "hb / ln x powr (1+e) < bs!i/2" by (intro x0_hb_bound0) simp_all
  with hb_nonneg ln_x_pos have "(bs!i - hb * ln x powr -(1+e)) > 0"
    by (subst powr_minus) (simp_all add: field_simps)
  with * have "0 < x * (bs!i - hb * ln x powr -(1+e))" using x_pos
    by (subst (asm) powr_minus, intro mult_pos_pos)
  hence A: "0 < bs!i*x - hb * x * ln x powr -(1+e)" by (simp add: algebra_simps)

  from assms have "-(hb*x*ln x powr -(1+e)) \<le> -\<bar>(hs!i) x\<bar>"
    using h_bounds[of x "hs!i"] by (subst neg_le_iff_le, subst powr_minus) (simp add: field_simps)
  also have "... \<le> (hs!i) x" by simp
  finally have B: "bs!i*x - hb*x*ln x powr -(1+e) \<le> bs!i*x + (hs!i) x" by simp

  have "(hs!i) x \<le> \<bar>(hs!i) x\<bar>" by simp
  also from assms have "... \<le> (hb*x*ln x powr -(1+e))"
     using h_bounds[of x "hs!i"] by (subst powr_minus) (simp_all add: field_simps)
  finally have C: "bs!i*x + hb*x*ln x powr -(1+e) \<ge> bs!i*x + (hs!i) x" by simp

  from A B C show ?thesis1
    by (cases "p \<ge> 0") (auto intro: powr_mono2 powr_mono2' simp: assms(3))
  from A B C show ?thesis2
    by (cases "p \<ge> 0") (auto intro: powr_mono2 powr_mono2' simp: assms(3))
qed

lemma asymptotics1':
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "(bs!i*x) powr p * (1 + ln x powr (-e/2)) \<le>
           (bs!i*x + (hs!i) x) powr p * (1 + ln (bs!i*x + (hs!i) x) powr (-e/2))"
proof-
  from assms x0_le_x1 have x: "x \<ge> x\<^sub>0" by simp
  from b_pos[of "bs!i"] assms have b_pos: "bs!i > 0" "bs!i \<noteq> 0" by simp_all
  from b_less_1[of "bs!i"] assms have b_less_1: "bs!i < 1" by simp
  from x1_gt_1 assms have ln_x_pos: "ln x > 0" by simp
  have mono: "\<And>a b. a \<le> b \<Longrightarrow> (bs!i*x) powr p * a \<le> (bs!i*x) powr p * b"
    by (rule mult_left_mono) simp_all

  define s :: real where [abs_def]: "s = (if p \<ge> 0 then 1 else -1)"
  have "1 + ln x powr (-e/2) \<le>
          (1 - s*hb*inverse(bs!i)*ln x powr -(1+e)) powr p *
          (1 + ln (bs!i*x + hb * x / ln x powr (1+e)) powr (-e/2))" (is "_ \<le> ?A * ?B")
    using assms x unfolding s_def using asymptotics1[OF x assms(2)] asymptotics1'[OF x assms(2)]
    by simp
  also have "(bs!i*x) powr p * ... = (bs!i*x) powr p * ?A * ?B" by simp
  also from x0_hb_bound0'[OF x, of "bs!i"] hb_nonneg x ln_x_pos assms
    have "s*hb * ln x powr -(1 + e) < bs ! i"
    by (subst powr_minus) (simp_all add: field_simps s_def)
  hence "(bs!i*x) powr p * ?A = (bs!i*x*(1 - s*hb*inverse (bs!i)*ln x powr -(1+e))) powr p"
    using b_pos assms x x0_pos b_less_1 ln_x_pos
    by (subst powr_mult[symmetric]) (simp_all add: s_def field_simps)
  also have "bs!i*x*(1 - s*hb*inverse (bs!i)*ln x powr -(1+e)) = bs!i*x - s*hb*x*ln x powr -(1+e)"
    using b_pos assms by (simp add: algebra_simps)
  also have "?B = 1 + ln (bs!i*x + hb*x*ln x powr -(1+e)) powr (-e/2)"
    by (subst powr_minus) (simp add: field_simps)

  also {
    from x assms have "(bs!i*x - s*hb*x*ln x powr -(1+e)) powr p \<le> (bs!i*x + (hs!i) x) powr p"
      using asymptotics_aux(1)[OF assms(1,2) s_def] by blast
    moreover {
      have "(hs!i) x \<le> \<bar>(hs!i) x\<bar>" by simp
      also from assms have "\<bar>(hs!i) x\<bar> \<le> hb * x / ln x powr (1+e)" by (intro h_bounds) simp_all
      finally have "(hs ! i) x \<le> hb * x * ln x powr -(1 + e)"
        by (subst powr_minus) (simp_all add: field_simps)
      moreover from x hb_nonneg x0_pos have "hb * x * ln x powr -(1+e) \<ge> 0"
        by (intro mult_nonneg_nonneg) simp_all
      ultimately have "1 + ln (bs!i*x + hb * x * ln x powr -(1+e)) powr (-e/2) \<le>
                       1 + ln (bs!i*x + (hs!i) x) powr (-e/2)" using assms x e_pos b_pos x0_pos
      by (intro add_left_mono powr_mono2' ln_mono ln_gt_zero step_pos x0_hb_bound7'
                add_pos_nonneg mult_pos_pos) simp_all
    }
    ultimately have "(bs!i*x - s*hb*x*ln x powr -(1+e)) powr p *
                         (1 + ln (bs!i*x + hb * x * ln x powr -(1+e)) powr (-e/2))
                     \<le> (bs!i*x + (hs!i) x) powr p * (1 + ln (bs!i*x + (hs!i) x) powr (-e/2))"
      by (rule mult_mono) simp_all
  }
  finally show ?thesis by (simp_all add: mono)
qed

lemma asymptotics2':
  assumes "x \<ge> x\<^sub>1" "i < k"
  shows   "(bs!i*x + (hs!i) x) powr p * (1 - ln (bs!i*x + (hs!i) x) powr (-e/2)) \<le>
           (bs!i*x) powr p * (1 - ln x powr (-e/2))"
proof-
  define s :: real where "s = (if p \<ge> 0 then 1 else -1)"
  from assms x0_le_x1 have x: "x \<ge> x\<^sub>0" by simp
  from assms x1_gt_1 have ln_x_pos: "ln x > 0" by simp
  from b_pos[of "bs!i"] assms have b_pos: "bs!i > 0" "bs!i \<noteq> 0" by simp_all
  from b_pos hb_nonneg have pos: "1 + s * hb * (inverse (bs!i) * ln x powr -(1+e)) > 0"
    using x0_hb_bound0'[OF x, of "bs!i"] b_pos assms ln_x_pos
    by (subst powr_minus) (simp add: field_simps s_def)
  have mono: "\<And>a b. a \<le> b \<Longrightarrow> (bs!i*x) powr p * a \<le> (bs!i*x) powr p * b"
    by (rule mult_left_mono) simp_all

  let ?A = "(1 + s*hb*inverse(bs!i)*ln x powr -(1+e)) powr p"
  let ?B = "1 - ln (bs!i*x + (hs!i) x) powr (-e/2)"
  let ?B' = "1 - ln (bs!i*x + hb * x / ln x powr (1+e)) powr (-e/2)"

  from assms x have "(bs!i*x + (hs!i) x) powr p \<le> (bs!i*x + s*hb*x*ln x powr -(1+e)) powr p"
    by (intro asymptotics_aux(2)) (simp_all add: s_def)
  moreover from x0_hb_bound9[OF assms(1,2)] have "?B \<ge> 0" by (simp add: field_simps)
  ultimately have "(bs!i*x + (hs!i) x) powr p * ?B \<le>
                   (bs!i*x + s*hb*x*ln x powr -(1+e)) powr p * ?B" by (rule mult_right_mono)
  also from assms e_pos pos have "?B \<le> ?B'"
  proof -
    from x0_hb_bound8'[OF assms(1,2)] x0_hb_bound8[OF assms(1,2)] x0_ge_1
    have *: "bs ! i * x + s*hb * x / ln x powr (1 + e) > 1" by (simp add: s_def)
    moreover from * have "... > 0" by simp
    moreover from x0_hb_bound7[OF assms(1,2)] x0_ge_1 have "bs ! i * x + (hs ! i) x > 1" by simp
    moreover {
      have "(hs!i) x \<le> \<bar>(hs!i) x\<bar>" by simp
      also from assms x0_le_x1 have "... \<le> hb*x/ln x powr (1+e)" by (intro h_bounds) simp_all
      finally have "bs!i*x + (hs!i) x \<le> bs!i*x + hb*x/ln x powr (1+e)" by simp
    }
    ultimately show "?B \<le> ?B'" using assms e_pos x step_pos
      by (intro diff_left_mono powr_mono2' ln_mono ln_gt_zero) simp_all
  qed
  hence "(bs!i*x + s*hb*x*ln x powr -(1+e)) powr p * ?B \<le>
             (bs!i*x + s*hb*x*ln x powr -(1+e)) powr p * ?B'" by (intro mult_left_mono) simp_all
  also have "bs!i*x + s*hb*x*ln x powr -(1+e) = bs!i*x*(1 + s*hb*inverse (bs!i)*ln x powr -(1+e))"
    using b_pos by (simp_all add: field_simps)
  also have "... powr p = (bs!i*x) powr p * ?A"
    using b_pos x x0_pos pos by (intro powr_mult) simp_all
  also have "(bs!i*x) powr p * ?A * ?B' = (bs!i*x) powr p * (?A * ?B')" by simp
  also have "?A * ?B' \<le> 1 - ln x powr (-e/2)" using assms x
    using asymptotics2[OF x assms(2)] asymptotics2'[OF x assms(2)] by (simp add: s_def)
  finally show ?thesis by (simp_all add: mono)
qed

lemma Cx_le_step:
  assumes "i < k" "x \<ge> x\<^sub>1"
  shows   "C*x \<le> bs!i*x + (hs!i) x"
proof-
  from assms have "C*x \<le> bs!i*x - hb*x/ln x powr (1+e)" by (intro C_bound) simp_all
  also from assms have "-(hb*x/ln x powr (1+e)) \<le> -\<bar>(hs!i) x\<bar>"
    by (subst neg_le_iff_le, intro h_bounds) simp_all
  hence "bs!i*x - hb*x/ln x powr (1+e) \<le> bs!i*x + -\<bar>(hs!i) x\<bar>" by simp
  also have "-\<bar>(hs!i) x\<bar> \<le> (hs!i) x" by simp
  finally show ?thesis by simp
qed

end


locale akra_bazzi_nat_to_real = akra_bazzi_real_recursion +
  fixes f :: "nat \<Rightarrow> real"
  and   g :: "real \<Rightarrow> real"
  assumes f_base: "real x \<ge> x\<^sub>0 \<Longrightarrow> real x \<le> x\<^sub>1 \<Longrightarrow> f x \<ge> 0"
  and     f_rec:  "real x > x\<^sub>1 \<Longrightarrow>
                          f x = g (real x) + (\<Sum>i<k. as!i * f (nat \<lfloor>bs!i * x + (hs!i) (real x)\<rfloor>))"
  and     x0_int: "real (nat \<lfloor>x\<^sub>0\<rfloor>) = x\<^sub>0"
begin

function f' :: "real \<Rightarrow> real" where
  "x \<le> x\<^sub>1 \<Longrightarrow> f' x = f (nat \<lfloor>x\<rfloor>)"
| "x > x\<^sub>1 \<Longrightarrow> f' x = g x + (\<Sum>i<k. as!i * f' (bs!i * x + (hs!i) x))"
by (force, simp_all)
termination by (relation "Wellfounded.measure akra_bazzi_measure")
               (simp_all add: akra_bazzi_measure_decreases)

lemma f'_base: "x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f' x \<ge> 0"
  apply (subst f'.simps(1), assumption)
  apply (rule f_base)
  apply (rule order.trans[of _ "real (nat \<lfloor>x\<^sub>0\<rfloor>)"], simp add: x0_int)
  apply (subst of_nat_le_iff, intro nat_mono floor_mono, assumption)
  using x0_pos apply linarith
  done

lemmas f'_rec = f'.simps(2)

end


locale akra_bazzi_real_lower = akra_bazzi_real +
  fixes fb2 gb2 c2 :: real
  assumes f_base2:   "x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f x \<ge> fb2"
  and     fb2_pos:   "fb2 > 0"
  and     g_growth2: "\<forall>x\<ge>x\<^sub>1. \<forall>u\<in>{C*x..x}. c2 * g x \<ge> g u"
  and     c2_pos:    "c2 > 0"
  and     g_bounded: "x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> g x \<le> gb2"
begin

interpretation akra_bazzi_integral integrable integral by (rule integral)

lemma gb2_nonneg: "gb2 \<ge> 0" using g_bounded[of x\<^sub>0] x0_le_x1 x0_pos g_nonneg[of x\<^sub>0] by simp

lemma g_growth2':
  assumes "x \<ge> x\<^sub>1" "i < k" "u \<in> {bs!i*x+(hs!i) x..x}"
  shows   "c2 * g x \<ge> g u"
proof-
  from assms have "C*x \<le> bs!i*x+(hs!i) x" by (intro Cx_le_step)
  with assms have "u \<in> {C*x..x}" by auto
  with assms g_growth2 show ?thesis by simp
qed

lemma g_bounds2:
  obtains c4 where "\<And>x i. x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> g_approx i x \<le> c4 * g x" "c4 > 0"
proof-
  define c4
    where "c4 = Max {c2 / min 1 (min ((b/2) powr (p+1)) ((b*3/2) powr (p+1))) |b. b \<in> set bs}"

  {
    from bs_nonempty obtain b where b: "b \<in> set bs" by (cases bs) auto
    let ?m = "min 1 (min ((b/2) powr (p+1)) ((b*3/2) powr (p+1)))"
    from b b_pos have "?m > 0" unfolding min_def by (auto simp: not_le)
    with b b_pos c2_pos have "c2 / ?m > 0" by (simp_all add: field_simps)
    with b have "c4 > 0" unfolding c4_def by (subst Max_gr_iff) (simp, simp, blast)
  }

  {
    fix x i assume i: "i < k" and x: "x \<ge> x\<^sub>1"
    have powr_negD: "a powr b \<le> 0 \<Longrightarrow> a = 0"
      for a b :: real unfolding powr_def by (simp split: if_split_asm)
    let ?m = "min 1 (min ((bs!i/2) powr (p+1)) ((bs!i*3/2) powr (p+1)))"
    have "min 1 ((bs!i + (hs ! i) x / x) powr (p+1)) \<ge> min 1 (min ((bs!i/2) powr (p+1)) ((bs!i*3/2) powr (p+1)))"
      apply (insert x i x0_le_x1 x1_pos step_pos b_pos[OF b_in_bs[OF i]],
             rule min.mono, simp, cases "p + 1 \<ge> 0")
      apply (rule order.trans[OF min.cobounded1 powr_mono2[OF _ _ x0_hb_bound4']], simp_all add: field_simps) []
      apply (rule order.trans[OF min.cobounded2 powr_mono2'[OF _ _ x0_hb_bound5]], simp_all add: field_simps) []
      done
    with i b_pos[of "bs!i"] have "c2 / min 1 ((bs!i + (hs ! i) x / x) powr (p+1)) \<le> c2 / ?m" using c2_pos
      unfolding min_def by (intro divide_left_mono) (auto intro!: mult_pos_pos dest!: powr_negD)

    also from i x have "... \<le> c4" unfolding c4_def by (intro Max.coboundedI) auto
    finally have "c2 / min 1 ((bs!i + (hs ! i) x / x) powr (p+1)) \<le> c4" .
  } note c4 = this

  {
    fix x :: real and i :: nat
    assume x: "x \<ge> x\<^sub>1" and i: "i < k"
    from x x1_pos have x_pos: "x > 0" by simp
    let ?x' = "bs ! i * x + (hs ! i) x"
    let ?x'' = "bs ! i + (hs ! i) x / x"
    from x x1_ge_1 i g_growth2' x0_le_x1 c2_pos
      have c2: "c2 > 0" "\<forall>u\<in>{?x'..x}. g u \<le> c2 * g x" by auto

    from x0_le_x1 x i have x'_le_x: "?x' \<le> x" by (intro step_le_x) simp_all
    let ?m = "min (?x' powr (p + 1)) (x powr (p + 1))"
    define m' where "m' = min 1 (?x'' powr (p + 1))"
    have [simp]: "bs ! i > 0" by (intro b_pos nth_mem) (simp add: i length_bs)
    from x0_le_x1 x i have [simp]: "?x' > 0" by (intro step_pos) simp_all


    {
      fix u assume u: "u \<ge> ?x'" "u \<le> x"
      have "?m \<le> u powr (p + 1)" using x u by (intro powr_lower_bound mult_pos_pos) simp_all
      moreover from c2 and u have "g u \<le> c2 * g x" by simp
      ultimately have "g u * ?m \<le> c2 * g x * u powr (p + 1)" using c2 x x1_pos x0_le_x1
        by (intro mult_mono mult_nonneg_nonneg g_nonneg) auto
    }
    hence "integral (\<lambda>u. g u / u powr (p+1)) ?x' x \<le> integral (\<lambda>u. c2 * g x / ?m) ?x' x"
      using x_pos step_pos[OF i x] x0_hb_bound7[OF x i] c2 x x0_le_x1
      by (intro integral_le x'_le_x akra_bazzi_integrable ballI integrable_const)
         (auto simp: field_simps intro!: mult_nonneg_nonneg g_nonneg)

    also from x0_pos x x0_le_x1 x'_le_x c2 have "... = (x - ?x') * (c2 * g x / ?m)"
      by (subst integral_const) (simp_all add: g_nonneg)
    also from c2 x_pos x x0_le_x1 have "c2 * g x \<ge> 0"
      by (intro mult_nonneg_nonneg g_nonneg) simp_all
    with x i x0_le_x1 have "(x - ?x') * (c2 * g x / ?m) \<le> x * (c2 * g x / ?m)"
      by (intro x0_hb_bound3 mult_right_mono) (simp_all add: field_simps)

    also have "x powr (p + 1) = x powr (p + 1) * 1" by simp
    also have "(bs ! i * x + (hs ! i) x) powr (p + 1) =
               (bs ! i + (hs ! i) x / x) powr (p + 1) * x powr (p + 1)"
      using x x1_pos step_pos[OF i x] x_pos i x0_le_x1
      by (subst powr_mult[symmetric]) (simp add: field_simps, simp, simp add: algebra_simps)
    also have "... = x powr (p + 1) * (bs ! i + (hs ! i) x / x) powr (p + 1)" by simp
    also have "min ... (x powr (p + 1) * 1) = x powr (p + 1) * m'" unfolding m'_def using x_pos
      by (subst min.commute, intro min_mult_left[symmetric]) simp

    also from x_pos have "x * (c2 * g x / (x powr (p + 1) * m')) = (c2/m') * (g x / x powr p)"
      by (simp add: field_simps powr_add)
    also from x i g_nonneg x0_le_x1 x1_pos have "... \<le> c4 * (g x / x powr p)" unfolding m'_def
      by (intro mult_right_mono c4) (simp_all add: field_simps)
    finally have "g_approx i x \<le> c4 * g x"
      unfolding g_approx_def using x_pos by (simp add: field_simps)
  }
  thus ?thesis using that \<open>c4 > 0\<close> by blast
qed

lemma f_approx_bounded_above:
  obtains c where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f_approx x \<le> c" "c > 0"
proof-
  let ?m1 = "max (x\<^sub>0 powr p) (x\<^sub>1 powr p)"
  let ?m2 = "max (x\<^sub>0 powr (-(p+1))) (x\<^sub>1 powr (-(p+1)))"
  let ?m3 = "gb2 * ?m2"
  let ?m4 = "1 + (x\<^sub>1 - x\<^sub>0) * ?m3"
  let ?int = "\<lambda>x. integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x"
  {
    fix x assume x: "x \<ge> x\<^sub>0" "x \<le> x\<^sub>1"
    with x0_pos have "x powr p \<le> ?m1" "?m1 \<ge> 0" by (intro powr_upper_bound) (simp_all add: max_def)
    moreover {
      fix u assume u: "u \<in> {x\<^sub>0..x}"
      have "g u / u powr (p + 1) = g u * u powr (-(p+1))"
        by (subst powr_minus) (simp add: field_simps)
      also from u x x0_pos have "u powr (-(p+1)) \<le> ?m2"
        by (intro powr_upper_bound) simp_all
      hence "g u * u powr (-(p+1)) \<le> g u * ?m2"
        using u g_nonneg x0_pos by (intro mult_left_mono) simp_all
      also from x u x0_pos have "g u \<le> gb2" by (intro g_bounded) simp_all
      hence "g u * ?m2 \<le> gb2 * ?m2" by (intro mult_right_mono) (simp_all add: max_def)
      finally have "g u / u powr (p + 1) \<le> ?m3" .
    } note A = this
    {
      from A x gb2_nonneg have "?int x \<le> integral (\<lambda>_. ?m3) x\<^sub>0 x"
        by (intro integral_le akra_bazzi_integrable integrable_const mult_nonneg_nonneg)
           (simp_all add: le_max_iff_disj)
      also from x gb2_nonneg have "... \<le> (x - x\<^sub>0) * ?m3"
        by (subst integral_const) (simp_all add: le_max_iff_disj)
      also from x gb2_nonneg have "... \<le> (x\<^sub>1 - x\<^sub>0) * ?m3"
        by (intro mult_right_mono mult_nonneg_nonneg) (simp_all add: max_def)
      finally have "1 + ?int x \<le> ?m4" by simp
    }
    moreover from x g_nonneg x0_pos have "?int x \<ge> 0"
      by (intro integral_nonneg akra_bazzi_integrable) (simp_all add: powr_def field_simps)
    hence "1 + ?int x \<ge> 0" by simp
    ultimately have "f_approx x \<le> ?m1 * ?m4"
      unfolding f_approx_def by (intro mult_mono)
    hence "f_approx x \<le> max 1 (?m1 * ?m4)" by simp
  }
  from that[OF this] show ?thesis by auto
qed

lemma f_bounded_below:
  assumes c': "c' > 0"
  obtains c where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> 2 * (c * f_approx x) \<le> f x" "c \<le> c'" "c > 0"
proof-
  obtain c where c: "\<And>x. x\<^sub>0 \<le> x \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f_approx x \<le> c" "c > 0"
    by (rule f_approx_bounded_above) blast
  {
    fix x assume x: "x\<^sub>0 \<le> x" "x \<le> x\<^sub>1"
    with c have "inverse c * f_approx x \<le> 1" by (simp add: field_simps)
    moreover from x f_base2 x0_pos have "f x \<ge> fb2" by auto
    ultimately have "inverse c * f_approx x * fb2 \<le> 1 * f x" using fb2_pos
      by (intro mult_mono) simp_all
    hence "inverse c * fb2 * f_approx x \<le> f x" by (simp add: field_simps)
    moreover have "min c' (inverse c * fb2) * f_approx x \<le> inverse c * fb2 * f_approx x"
      using f_approx_nonneg x c
      by (intro mult_right_mono f_approx_nonneg) (simp_all add: field_simps)
    ultimately have "2 * (min c' (inverse c * fb2) / 2 * f_approx x) \<le> f x" by simp
  }
  moreover from c' have "min c' (inverse c * fb2) / 2 \<le> c'" by simp
  moreover have "min c' (inverse c * fb2) / 2 > 0"
    using c fb2_pos c' by simp
  ultimately show ?thesis by (rule that)
qed

lemma akra_bazzi_lower:
  obtains c5 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> f x \<ge> c5 * f_approx x" "c5 > 0"
proof-
  obtain c4 where c4: "\<And>x i. x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> g_approx i x \<le> c4 * g x" "c4 > 0"
    by (rule g_bounds2) blast
  hence "inverse c4 / 2 > 0" by simp
  then obtain c5 where c5: "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> 2 * (c5 * f_approx x) \<le> f x"
                           "c5 \<le> inverse c4 / 2" "c5 > 0"
    by (rule f_bounded_below) blast

  {
  fix x :: real assume x: "x \<ge> x\<^sub>0"
  from c5 x have  " c5 * 1 * f_approx x \<le> c5 * (1 + ln x powr (- e / 2)) * f_approx x"
    by (intro mult_right_mono mult_left_mono f_approx_nonneg) simp_all
  also from x have "c5 * (1 + ln x powr (-e/2)) * f_approx x \<le> f x"
  proof (induction x rule: akra_bazzi_induct)
    case (base x)
    have "1 + ln x powr (-e/2) \<le> 2" using asymptotics3 base by simp
    hence "(1 + ln x powr (-e/2)) * (c5 * f_approx x) \<le> 2 * (c5 * f_approx x)"
      using c5 f_approx_nonneg base x0_ge_1 by (intro mult_right_mono mult_nonneg_nonneg) simp_all
    also from base have "2 * (c5 * f_approx x) \<le> f x"  by (intro c5) simp_all
    finally show ?case by (simp add: algebra_simps)
  next
    case (rec x)
    let ?a = "\<lambda>i. as!i" and ?b = "\<lambda>i. bs!i" and ?h = "\<lambda>i. hs!i"
    let ?int = "integral (\<lambda>u. g u / u powr (p+1)) x\<^sub>0 x"
    let ?int1 = "\<lambda>i. integral (\<lambda>u. g u / u powr (p+1)) x\<^sub>0 (?b i*x+?h i x)"
    let ?int2 = "\<lambda>i. integral (\<lambda>u. g u / u powr (p+1)) (?b i*x+?h i x) x"
    let ?l = "ln x powr (-e/2)" and ?l' = "\<lambda>i. ln (?b i*x + ?h i x) powr (-e/2)"

    from rec and x0_le_x1 x0_ge_1 have x: "x \<ge> x\<^sub>0" and x_gt_1: "x > 1" by simp_all
    with x0_pos have x_pos: "x > 0" and x_nonneg: "x \<ge> 0" by simp_all
    from c5 c4 have "c5 * c4 \<le> 1/2" by (simp add: field_simps)
    moreover from asymptotics3 x have "(1 + ?l) \<le> 2" by (simp add: field_simps)
    ultimately have "(c5*c4)*(1 + ?l) \<le> (1/2) * 2" by (rule mult_mono) simp_all
    hence "0 \<le> 1 - c5*c4*(1 + ?l)" by simp
    with g_nonneg[OF x] have "0 \<le> g x * ..." by (intro mult_nonneg_nonneg) simp_all
    hence "c5 * (1 + ?l) * f_approx x \<le> c5 * (1 + ?l) * f_approx x + g x - c5*c4*(1 + ?l) * g x"
      by (simp add: algebra_simps)
    also from x_gt_1 have "... = c5 * x powr p * (1 + ?l) * (1 + ?int - c4*g x/x powr p) + g x"
      by (simp add: field_simps f_approx_def powr_minus)
    also have "c5 * x powr p * (1 + ?l) * (1 + ?int - c4*g x/x powr p) =
                 (\<Sum>i<k. (?a i * ?b i powr p) * (c5 * x powr p * (1 + ?l) * (1 + ?int - c4*g x/x powr p)))"
      by (subst sum_distrib_right[symmetric]) (simp add: p_props)
    also have "... \<le> (\<Sum>i<k. ?a i * f (?b i*x + ?h i x))"
    proof (intro sum_mono, clarify)
      fix i assume i: "i < k"
      let ?f = "c5 * ?a i * (?b i * x) powr p"
      from rec.hyps i have "x\<^sub>0 < bs ! i * x + (hs ! i) x" by (intro x0_hb_bound7) simp_all
      hence "1 + ?int1 i \<ge> 1" by (intro f_approx_aux x0_hb_bound7) simp_all
      hence int_nonneg: "1 + ?int1 i \<ge> 0" by simp

      have "(?a i * ?b i powr p) * (c5 * x powr p * (1 + ?l) * (1 + ?int - c4*g x/x powr p)) =
            ?f * (1 + ?l) * (1 + ?int - c4*g x/x powr p)" (is "?expr = ?A * ?B")
            using x_pos b_pos[of "bs!i"] i by (subst powr_mult) simp_all
      also from rec.hyps i have "g_approx i x \<le> c4 * g x" by (intro c4) simp_all
      hence "c4*g x/x powr p \<ge> ?int2 i" unfolding g_approx_def using x_pos
        by (simp add: field_simps)
      hence "?A * ?B \<le> ?A * (1 + (?int - ?int2 i))" using i c5 a_ge_0
        by (intro mult_left_mono mult_nonneg_nonneg) simp_all
      also from rec.hyps i have "x\<^sub>0 < bs ! i * x + (hs ! i) x" by (intro x0_hb_bound7) simp_all
      hence "?int - ?int2 i = ?int1 i"
        apply (subst diff_eq_eq, subst eq_commute)
        apply (intro integral_combine akra_bazzi_integrable)
        apply (insert rec.hyps step_le_x[OF i, of x], simp_all)
        done
      also have "?A * (1 + ?int1 i) = (c5*?a i*(1 + ?int1 i)) * ((?b i*x) powr p * (1 + ?l))"
        by (simp add: algebra_simps)
      also have "... \<le> (c5*?a i*(1 + ?int1 i)) * ((?b i*x + ?h i x) powr p * (1 + ?l' i))"
        using rec.hyps i c5 a_ge_0 int_nonneg
        by (intro mult_left_mono asymptotics1' mult_nonneg_nonneg) simp_all
      also have "... = ?a i*(c5*(1 + ?l' i)*f_approx (?b i*x + ?h i x))"
        by (simp add: algebra_simps f_approx_def)
      also from i have "... \<le> ?a i * f (?b i*x + ?h i x)"
        by (intro mult_left_mono a_ge_0 rec.IH) simp_all
      finally show "?expr \<le> ?a i * f (?b i*x + ?h i x)" .
    qed
    also have "... + g x = f x" using f_rec[of x] rec.hyps x0_le_x1 by simp
    finally show ?case by simp
  qed
  finally have "c5 * f_approx x \<le> f x" by simp
  }
  from this and c5(3) show ?thesis by (rule that)
qed

lemma akra_bazzi_bigomega:
  "f \<in> \<Omega>(\<lambda>x. x powr p * (1 + integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x))"
apply (fold f_approx_def, rule akra_bazzi_lower, erule landau_omega.bigI)
apply (subst eventually_at_top_linorder, rule exI[of _ x\<^sub>0])
apply (simp add: f_nonneg f_approx_nonneg)
done

end


locale akra_bazzi_real_upper = akra_bazzi_real +
  fixes fb1 c1 :: real
  assumes f_base1:   "x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f x \<le> fb1"
  and     g_growth1: "\<forall>x\<ge>x\<^sub>1. \<forall>u\<in>{C*x..x}. c1 * g x \<le> g u"
  and     c1_pos:    "c1 > 0"
begin

interpretation akra_bazzi_integral integrable integral by (rule integral)

lemma g_growth1':
  assumes "x \<ge> x\<^sub>1" "i < k" "u \<in> {bs!i*x+(hs!i) x..x}"
  shows   "c1 * g x \<le> g u"
proof-
  from assms have "C*x \<le> bs!i*x+(hs!i) x" by (intro Cx_le_step)
  with assms have "u \<in> {C*x..x}" by auto
  with assms g_growth1 show ?thesis by simp
qed

lemma g_bounds1:
  obtains c3 where
    "\<And>x i. x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> c3 * g x \<le> g_approx i x" "c3 > 0"
proof-
  define c3 where "c3 =
    Min {c1*((1-b)/2) / max 1 (max ((b/2) powr (p+1)) ((b*3/2) powr (p+1))) |b. b \<in> set bs}"

  {
    fix b assume b: "b \<in> set bs"
    let ?x = "max 1 (max ((b/2) powr (p+1)) ((b*3/2) powr (p+1)))"
    have "?x \<ge> 1" by simp
    hence "?x > 0" by (rule less_le_trans[OF zero_less_one])
    with b b_less_1 c1_pos have "c1*((1-b)/2) / ?x > 0"
      by (intro divide_pos_pos mult_pos_pos) (simp_all add: algebra_simps)
  }
  hence "c3 > 0" unfolding c3_def by (subst Min_gr_iff) auto

  {
    fix x i assume i: "i < k" and x: "x \<ge> x\<^sub>1"
    with b_less_1 have b_less_1': "bs ! i < 1" by simp
    let ?m = "max 1 (max ((bs!i/2) powr (p+1)) ((bs!i*3/2) powr (p+1)))"
    from i x have "c3 \<le> c1*((1-bs!i)/2) / ?m" unfolding c3_def by (intro Min.coboundedI) auto
    also have "max 1 ((bs!i + (hs ! i) x / x) powr (p+1)) \<le> max 1 (max ((bs!i/2) powr (p+1)) ((bs!i*3/2) powr (p+1)))"
      apply (insert x i x0_le_x1 x1_pos step_pos[OF i x] b_pos[OF b_in_bs[OF i]],
             rule max.mono, simp, cases "p + 1 \<ge> 0")
      apply (rule order.trans[OF powr_mono2[OF _ _ x0_hb_bound5] max.cobounded2], simp_all add: field_simps) []
      apply (rule order.trans[OF powr_mono2'[OF _ _ x0_hb_bound4'] max.cobounded1], simp_all add: field_simps) []
      done
    with b_less_1' c1_pos have "c1*((1-bs!i)/2) / ?m \<le>
          c1*((1-bs!i)/2) / max 1 ((bs!i + (hs ! i) x / x) powr (p+1))"
      by (intro divide_left_mono mult_nonneg_nonneg) (simp_all add: algebra_simps)
    finally have "c3 \<le> c1*((1-bs!i)/2) / max 1 ((bs!i + (hs ! i) x / x) powr (p+1))" .
  } note c3 = this

  {
    fix x :: real and i :: nat
    assume x: "x \<ge> x\<^sub>1" and i: "i < k"
    from x x1_pos have x_pos: "x > 0" by simp
    let ?x' = "bs ! i * x + (hs ! i) x"
    let ?x'' = "bs ! i + (hs ! i) x / x"
    from x x1_ge_1 x0_le_x1 i c1_pos g_growth1'
      have c1: "c1 > 0" "\<forall>u\<in>{?x'..x}. g u \<ge> c1 * g x" by auto
    define b' where "b' = (1 - bs!i)/2"

    from x x0_le_x1 i have x'_le_x: "?x' \<le> x" by (intro step_le_x) simp_all
    let ?m = "max (?x' powr (p + 1)) (x powr (p + 1))"
    define m' where "m' = max 1 (?x'' powr (p + 1))"
    have [simp]: "bs ! i > 0" by (intro b_pos nth_mem) (simp add: i length_bs)
    from x x0_le_x1 i have x'_pos: "?x' > 0" by (intro step_pos) simp_all
    have m_pos: "?m > 0" unfolding max_def using x_pos step_pos[OF i x] by auto
    with x x0_le_x1 c1 have c1_g_m_nonneg: "c1 * g x / ?m \<ge> 0"
      by (intro mult_nonneg_nonneg divide_nonneg_pos g_nonneg) simp_all

    from x i g_nonneg x0_le_x1 have "c3 * (g x / x powr p) \<le> (c1*b'/m') * (g x / x powr p)"
      unfolding m'_def b'_def by (intro mult_right_mono c3) (simp_all add: field_simps)
    also from x_pos have "... = (x * b') * (c1 * g x / (x powr (p + 1) * m'))"
      by (simp add: field_simps powr_add)
    also from x i c1_pos x1_pos x0_le_x1
      have "... \<le> (x - ?x') * (c1 * g x / (x powr (p + 1) * m'))"
      unfolding b'_def m'_def by (intro x0_hb_bound6 mult_right_mono mult_nonneg_nonneg
                                        divide_nonneg_nonneg g_nonneg) simp_all
    also have "x powr (p + 1) * m' =
                 max (x powr (p + 1) * (bs ! i + (hs ! i) x / x) powr (p + 1)) (x powr (p + 1) * 1)"
      unfolding m'_def using x_pos by (subst max.commute, intro max_mult_left) simp
    also have "(x powr (p + 1) * (bs ! i + (hs ! i) x / x) powr (p + 1)) =
                 (bs ! i + (hs ! i) x / x) powr (p + 1) * x powr (p + 1)" by simp
    also have "... = (bs ! i * x + (hs ! i) x) powr (p + 1)"
      using x x1_pos step_pos[OF i x] x_pos i x0_le_x1 x_pos
      by (subst powr_mult[symmetric]) (simp add: field_simps, simp, simp add: algebra_simps)
    also have "x powr (p + 1) * 1 = x powr (p + 1)" by simp
    also have "(x - ?x') * (c1 * g x / ?m) = integral (\<lambda>_. c1 * g x / ?m) ?x' x"
      using x'_le_x by (subst integral_const[OF c1_g_m_nonneg]) auto
    also {
      fix u assume u: "u \<ge> ?x'" "u \<le> x"
      have "u powr (p + 1) \<le> ?m" using x u x'_pos by (intro powr_upper_bound mult_pos_pos) simp_all
      moreover from x'_pos u have "u \<ge> 0" by simp
      moreover from c1 and u have "c1 * g x \<le> g u" by simp
      ultimately have "c1 * g x * u powr (p + 1) \<le> g u * ?m" using c1 x u x0_hb_bound7[OF x i]
        by (intro mult_mono g_nonneg) auto
      with m_pos u step_pos[OF i x]
        have "c1 * g x / ?m \<le> g u / u powr (p + 1)" by (simp add: field_simps)
    }
    hence "integral (\<lambda>_. c1 * g x / ?m) ?x' x \<le> integral (\<lambda>u. g u / u powr (p + 1)) ?x' x"
      using x0_hb_bound7[OF x i] x'_le_x
      by (intro integral_le ballI akra_bazzi_integrable integrable_const c1_g_m_nonneg) simp_all
    finally have "c3 * g x \<le> g_approx i x" using x_pos
      unfolding g_approx_def by (simp add: field_simps)
  }
  thus ?thesis using that \<open>c3 > 0\<close> by blast
qed


lemma f_bounded_above:
  assumes c': "c' > 0"
  obtains c where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f x \<le> (1/2) * (c * f_approx x)" "c \<ge> c'" "c > 0"
proof-
  obtain c where c: "\<And>x. x\<^sub>0 \<le> x \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f_approx x \<ge> c" "c > 0"
    by (rule f_approx_bounded_below) blast
  have fb1_nonneg: "fb1 \<ge> 0" using f_base1[of "x\<^sub>0"] f_nonneg[of x\<^sub>0] x0_le_x1 by simp
  {
    fix x assume x: "x \<ge> x\<^sub>0" "x \<le> x\<^sub>1"
    with f_base1 x0_pos have "f x \<le> fb1" by simp
    moreover from c and x have "f_approx x \<ge> c" by blast
    ultimately have "f x * c \<le> fb1 * f_approx x" using c fb1_nonneg by (intro mult_mono) simp_all
    also from f_approx_nonneg x have "... \<le> (fb1 + 1) * f_approx x" by (simp add: algebra_simps)
    finally have "f x \<le> ((fb1+1) / c) * f_approx x" by (simp add: field_simps c)
    also have "... \<le> max ((fb1+1) / c) c' * f_approx x"
      by (intro mult_right_mono) (simp_all add: f_approx_nonneg x)
    finally have "f x \<le> 1/2 * (max ((fb1+1) / c) c' * 2 * f_approx x)" by simp
  }
  moreover have "max ((fb1+1) / c) c' * 2 \<ge> max ((fb1+1) / c) c'"
    by (subst mult_le_cancel_left1) (insert c', simp)
  hence "max ((fb1+1) / c) c' * 2 \<ge> c'" by (rule order.trans[OF max.cobounded2])
  moreover from fb1_nonneg and c have "(fb1+1) / c > 0" by simp
  hence "max ((fb1+1) / c) c' * 2 > 0" by simp
  ultimately show ?thesis by (rule that)
qed


lemma akra_bazzi_upper:
  obtains c6 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> f x \<le> c6 * f_approx x" "c6 > 0"
proof-
  obtain c3 where c3: "\<And>x i. x \<ge> x\<^sub>1 \<Longrightarrow> i < k \<Longrightarrow> c3 * g x \<le> g_approx i x" "c3 > 0"
    by (rule g_bounds1) blast
  hence "2 / c3 > 0" by simp
  then obtain c6 where c6: "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x \<le> x\<^sub>1 \<Longrightarrow> f x \<le> 1/2 * (c6 * f_approx x)"
                           "c6 \<ge> 2 / c3" "c6 > 0"
    by (rule f_bounded_above) blast

  {
  fix x :: real assume x: "x \<ge> x\<^sub>0"
  hence "f x \<le> c6 * (1 - ln x powr (-e/2)) * f_approx x"
  proof (induction x rule: akra_bazzi_induct)
    case (base x)
    from base have "f x \<le> 1/2 * (c6 * f_approx x)"  by (intro c6) simp_all
    also have "1 - ln x powr (-e/2) \<ge> 1/2" using asymptotics4 base by simp
    hence "(1 - ln x powr (-e/2)) * (c6 * f_approx x) \<ge> 1/2 * (c6 * f_approx x)"
      using c6 f_approx_nonneg base x0_ge_1 by (intro mult_right_mono mult_nonneg_nonneg) simp_all
    finally show ?case by (simp add: algebra_simps)
  next
    case (rec x)
    let ?a = "\<lambda>i. as!i" and ?b = "\<lambda>i. bs!i" and ?h = "\<lambda>i. hs!i"
    let ?int = "integral (\<lambda>u. g u / u powr (p+1)) x\<^sub>0 x"
    let ?int1 = "\<lambda>i. integral (\<lambda>u. g u / u powr (p+1)) x\<^sub>0 (?b i*x+?h i x)"
    let ?int2 = "\<lambda>i. integral (\<lambda>u. g u / u powr (p+1)) (?b i*x+?h i x) x"
    let ?l = "ln x powr (-e/2)" and ?l' = "\<lambda>i. ln (?b i*x + ?h i x) powr (-e/2)"

    from rec and x0_le_x1 have x: "x \<ge> x\<^sub>0" by simp
    with x0_pos have x_pos: "x > 0" and x_nonneg: "x \<ge> 0" by simp_all
    from c6 c3 have "c6 * c3 \<ge> 2" by (simp add: field_simps)
    have "f x = (\<Sum>i<k. ?a i * f (?b i*x + ?h i x)) + g x" (is "_ = ?sum + _")
      using f_rec[of x] rec.hyps x0_le_x1 by simp
    also have "?sum \<le> (\<Sum>i<k. (?a i*?b i powr p) * (c6*x powr p*(1 - ?l)*(1 + ?int - c3*g x/x powr p)))" (is "_ \<le> ?sum'")
    proof (rule sum_mono, clarify)
      fix i assume i: "i < k"
      from rec.hyps i have "x\<^sub>0 < bs ! i * x + (hs ! i) x" by (intro x0_hb_bound7) simp_all
      hence "1 + ?int1 i \<ge> 1" by (intro f_approx_aux x0_hb_bound7) simp_all
      hence int_nonneg: "1 + ?int1 i \<ge> 0" by simp
      have l_le_1: "ln x powr -(e/2) \<le> 1" using asymptotics3[OF x] by (simp add: field_simps)

      from i have "f (?b i*x + ?h i x) \<le> c6 * (1 - ?l' i) * f_approx (?b i*x + ?h i x)"
        by (rule rec.IH)
      hence "?a i * f (?b i*x + ?h i x) \<le> ?a i * ..." using a_ge_0 i
        by (intro mult_left_mono) simp_all
      also have "... = (c6*?a i*(1 + ?int1 i)) * ((?b i*x + ?h i x) powr p * (1 - ?l' i))"
        unfolding f_approx_def by (simp add: algebra_simps)
      also from i rec.hyps c6 a_ge_0
        have "... \<le> (c6*?a i*(1 + ?int1 i)) * ((?b i*x) powr p * (1 - ?l))"
        by (intro mult_left_mono asymptotics2' mult_nonneg_nonneg int_nonneg) simp_all
      also have "... = (1 + ?int1 i) * (c6*?a i*(?b i*x) powr p * (1 - ?l))"
        by (simp add: algebra_simps)
      also from rec.hyps i have "x\<^sub>0 < bs ! i * x + (hs ! i) x" by (intro x0_hb_bound7) simp_all
      hence "?int1 i = ?int - ?int2 i"
        apply (subst eq_diff_eq)
        apply (intro integral_combine akra_bazzi_integrable)
        apply (insert rec.hyps step_le_x[OF i, of x], simp_all)
        done
      also from rec.hyps i have "c3 * g x \<le> g_approx i x" by (intro c3) simp_all
      hence "?int2 i \<ge> c3*g x/x powr p" unfolding g_approx_def using x_pos
        by (simp add: field_simps)
      hence "(1 + (?int - ?int2 i)) * (c6*?a i*(?b i*x) powr p * (1 - ?l)) \<le>
             (1 + ?int - c3*g x/x powr p) * (c6*?a i*(?b i*x) powr p * (1 - ?l))"
             using i c6 a_ge_0 l_le_1
             by (intro mult_right_mono mult_nonneg_nonneg) (simp_all add: field_simps)
      also have "... = (?a i*?b i powr p) * (c6*x powr p*(1 - ?l) * (1 + ?int - c3*g x/x powr p))"
        using b_pos[of "bs!i"] x x0_pos i by (subst powr_mult) (simp_all add: algebra_simps)
      finally show "?a i * f (?b i*x + ?h i x) \<le> ..." .
    qed

    hence "?sum + g x \<le> ?sum' + g x" by simp
    also have "... = c6 * x powr p * (1 - ?l) * (1 + ?int - c3*g x/x powr p) + g x"
      by (simp add: sum_distrib_right[symmetric] p_props)
    also have "... = c6 * (1 - ?l) * f_approx x - (c6*c3*(1 - ?l) - 1) * g x"
      unfolding f_approx_def using x_pos by (simp add: field_simps)
    also {
       from c6 c3 have "c6*c3 \<ge> 2" by (simp add: field_simps)
       moreover have "(1 - ?l) \<ge> 1/2" using asymptotics4[OF x] by simp
       ultimately have "c6*c3*(1 - ?l) \<ge> 2 * (1/2)" by (intro mult_mono) simp_all
       with x x_pos have "(c6*c3*(1 - ?l) - 1) * g x \<ge> 0"
         by (intro mult_nonneg_nonneg g_nonneg) simp_all
       hence "c6 * (1 - ?l) * f_approx x - (c6*c3*(1 - ?l) - 1) * g x \<le>
                  c6 * (1 - ?l) * f_approx x" by (simp add: algebra_simps)
    }
    finally show ?case .
  qed
  also from x c6 have "... \<le> c6 * 1 * f_approx x"
    by (intro mult_left_mono mult_right_mono f_approx_nonneg) simp_all
  finally have "f x \<le> c6 * f_approx x" by simp
  }
  from this and c6(3) show ?thesis by (rule that)
qed

lemma akra_bazzi_bigo:
  "f \<in> O(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g u / u powr (p + 1)) x\<^sub>0 x))"
apply (fold f_approx_def, rule akra_bazzi_upper, erule landau_o.bigI)
apply (subst eventually_at_top_linorder, rule exI[of _ x\<^sub>0])
apply (simp add: f_nonneg f_approx_nonneg)
done

end

end
