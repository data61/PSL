(*
  File:   Landau_Library.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Auxiliary lemmas that should be merged into HOL.
*)
section \<open>Auxiliary lemmas\<close>

theory Landau_Library
imports Complex_Main 
begin

subsection \<open>Filters\<close>

lemma eventually_at_top_compose:
  assumes "\<And>c. eventually (\<lambda>x. (f x:: 'a :: linorder) \<ge> c) F" "eventually P at_top"
  shows   "eventually (\<lambda>x. P (f x)) F"
  using assms filterlim_at_top filterlim_iff by blast

lemma eventually_False_at_top_linorder [simp]: 
  "eventually (\<lambda>_::_::linorder. False) at_top \<longleftrightarrow> False"
  unfolding eventually_at_top_linorder by force

lemma eventually_not_equal: "eventually (\<lambda>x::'a::linordered_semidom. x \<noteq> a) at_top"
  using eventually_ge_at_top[of "a+1"] by eventually_elim (insert less_add_one[of a], auto)

lemma eventually_subst':
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> eventually (\<lambda>x. P x (f x)) F = eventually (\<lambda>x. P x (g x)) F"
  by (rule eventually_subst, erule eventually_rev_mp) simp

lemma eventually_nat_real:
  assumes "eventually P (at_top :: real filter)"
  shows   "eventually (\<lambda>x. P (real x)) (at_top :: nat filter)"
  using assms filterlim_real_sequentially
  unfolding filterlim_def le_filter_def eventually_filtermap by auto

lemma filterlim_cong':
  assumes "filterlim f F G"
  assumes "eventually (\<lambda>x. f x = g x) G"
  shows   "filterlim g F G"
  using assms by (subst filterlim_cong[OF refl refl, of _ f]) (auto elim: eventually_mono)

lemma eventually_ln_at_top: "eventually (\<lambda>x. P (ln x :: real)) at_top = eventually P at_top"
proof
  fix P assume "eventually (\<lambda>x. P (ln x :: real)) at_top"
  then obtain x0 where x0: "\<And>x. x \<ge> x0 \<Longrightarrow> P (ln x)"
    by (subst (asm) eventually_at_top_linorder) auto
  {
    fix x assume "x \<ge> ln (max 1 x0)"
    hence "exp x \<ge> max 1 x0" by (subst (2) exp_ln[symmetric], simp, subst exp_le_cancel_iff)
    hence "exp x \<ge> x0" by simp
    from x0[OF this] have "P x" by simp
  }
  thus "eventually P at_top" by (subst eventually_at_top_linorder) blast
next
  fix P :: "real \<Rightarrow> bool" assume  "eventually P at_top"
  then obtain x0 where x0: "\<And>x. x \<ge> x0 \<Longrightarrow> P x"
    by (subst (asm) eventually_at_top_linorder) auto
  {
    fix x assume "x \<ge> exp x0"
    hence "ln x \<ge> x0" by (subst ln_exp[symmetric], subst ln_le_cancel_iff)
                         (simp_all add: less_le_trans[OF exp_gt_zero])
    from x0[OF this] have "P (ln x)" .
  }
  thus "eventually (\<lambda>x. P (ln x)) at_top"
    by (subst eventually_at_top_linorder) blast
qed

lemma filtermap_ln_at_top: "filtermap (ln :: real \<Rightarrow> real) at_top = at_top"
  by (simp add: filter_eq_iff eventually_filtermap eventually_ln_at_top)

lemma eventually_ln_not_equal: "eventually (\<lambda>x::real. ln x \<noteq> a) at_top"
  by (subst eventually_ln_at_top) (rule eventually_not_equal)


subsection \<open>Miscellaneous\<close>

lemma ln_mono: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x \<le> y \<Longrightarrow> ln (x::real) \<le> ln y"
  by (subst ln_le_cancel_iff) simp_all

lemma ln_mono_strict: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x < y \<Longrightarrow> ln (x::real) < ln y"
  by (subst ln_less_cancel_iff) simp_all

lemma prod_list_pos: "(\<And>x::_::linordered_semidom. x \<in> set xs \<Longrightarrow> x > 0) \<Longrightarrow> prod_list xs > 0"
  by (induction xs) auto

lemma (in monoid_mult) fold_plus_prod_list_rev:
  "fold times xs = times (prod_list (rev xs))"
proof
  fix x
  have "fold times xs x = prod_list (rev xs @ [x])"
    by (simp add: foldr_conv_fold prod_list.eq_foldr)
  also have "\<dots> = prod_list (rev xs) * x"
    by simp
  finally show "fold times xs x = prod_list (rev xs) * x" .
qed


subsection \<open>Real powers\<close>

lemma powr_realpow_eventually: 
  assumes "filterlim f at_top F"
  shows   "eventually (\<lambda>x. f x powr (real n) = f x ^ n) F"
proof-
  from assms have "eventually (\<lambda>x. f x > 0) F" using filterlim_at_top_dense by blast
  thus ?thesis by eventually_elim (simp add: powr_realpow)
qed

lemma zero_powr [simp]: "(0::real) powr x = 0"
  unfolding powr_def by simp

lemma powr_negD: "(a::real) powr b \<le> 0 \<Longrightarrow> a = 0"
  unfolding powr_def by (simp split: if_split_asm)

lemma inverse_powr [simp]:
  assumes "(x::real) \<ge> 0"
  shows   "inverse x powr y = inverse (x powr y)"
proof (cases "x > 0")
  assume x: "x > 0"
  from x have "inverse x powr y = exp (y * ln (inverse x))" by (simp add: powr_def)
  also have "ln (inverse x) = -ln x" by (simp add: x ln_inverse)
  also have "exp (y * -ln x) = inverse (exp (y * ln x))" by (simp add: exp_minus)
  also from x have "exp (y * ln x) = x powr y" by (simp add: powr_def)
  finally show ?thesis .
qed (insert assms, simp)

lemma powr_mono':
  assumes "(x::real) > 0" "x \<le> 1" "a \<le> b"
  shows   "x powr b \<le> x powr a"
proof-
  have "inverse x powr a \<le> inverse x powr b" using assms
    by (intro powr_mono) (simp_all add: field_simps)
  hence "inverse (x powr a) \<le> inverse (x powr b)" using assms by simp
  with assms show ?thesis by (simp add: field_simps)
qed

lemma powr_less_mono':
  assumes "(x::real) > 0" "x < 1" "a < b"
  shows   "x powr b < x powr a"
proof-
  have "inverse x powr a < inverse x powr b" using assms
    by (intro powr_less_mono) (simp_all add: field_simps)
  hence "inverse (x powr a) < inverse (x powr b)" using assms by simp
  with assms show ?thesis by (simp add: field_simps)
qed

lemma powr_lower_bound: "\<lbrakk>(l::real) > 0; l \<le> x; x \<le> u\<rbrakk> \<Longrightarrow> min (l powr z) (u powr z) \<le> x powr z"
apply (cases "z \<ge> 0")
apply (rule order.trans[OF min.cobounded1 powr_mono2], simp_all) []
apply (rule order.trans[OF min.cobounded2 powr_mono2'], simp_all) []
done

lemma powr_upper_bound: "\<lbrakk>(l::real) > 0; l \<le> x; x \<le> u\<rbrakk> \<Longrightarrow> max (l powr z) (u powr z) \<ge> x powr z"
apply (cases "z \<ge> 0")
apply (rule order.trans[OF powr_mono2 max.cobounded2], simp_all) []
apply (rule order.trans[OF powr_mono2' max.cobounded1], simp_all) []
done

lemma powr_eventually_exp_ln: "eventually (\<lambda>x. (x::real) powr p = exp (p * ln x)) at_top"
  using eventually_gt_at_top[of "0::real"] unfolding powr_def by eventually_elim simp_all

lemma powr_eventually_exp_ln': 
  assumes "x > 0"
  shows   "eventually (\<lambda>x. (x::real) powr p = exp (p * ln x)) (nhds x)"
proof-
  let ?A = "{(0::real)<..}"
  from assms have "eventually (\<lambda>x. x > 0) (nhds x)" unfolding eventually_nhds
    by (intro exI[of _ "{(0::real)<..}"]) simp_all
  thus ?thesis by eventually_elim (simp add: powr_def)
qed


lemma powr_at_top: 
  assumes "(p::real) > 0"
  shows   "filterlim (\<lambda>x. x powr p) at_top at_top"
proof-
  have "LIM x at_top. exp (p * ln x) :> at_top"
    by (rule filterlim_compose[OF exp_at_top filterlim_tendsto_pos_mult_at_top[OF tendsto_const]])
       (simp_all add: ln_at_top assms)
  thus ?thesis by (subst filterlim_cong[OF refl refl powr_eventually_exp_ln])
qed

lemma powr_at_top_neg: 
  assumes "(a::real) > 0" "a < 1"
  shows   "((\<lambda>x. a powr x) \<longlongrightarrow> 0) at_top"
proof-
  from assms have "LIM x at_top. ln (inverse a) * x :> at_top"
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const])
       (simp_all add: filterlim_ident field_simps)
  with assms have "LIM x at_top. ln a * x :> at_bot"
    by (subst filterlim_uminus_at_bot) (simp add: ln_inverse)
  hence "((\<lambda>x. exp (x * ln a)) \<longlongrightarrow> 0) at_top"
    by (intro filterlim_compose[OF exp_at_bot]) (simp_all add: mult.commute)
  with assms show ?thesis unfolding powr_def by simp
qed

lemma powr_at_bot:
  assumes "(a::real) > 1"
  shows   "((\<lambda>x. a powr x) \<longlongrightarrow> 0) at_bot"
proof-
  from assms have "filterlim (\<lambda>x. ln a * x) at_bot at_bot"
    by (intro filterlim_tendsto_pos_mult_at_bot[OF tendsto_const _ filterlim_ident]) auto
  hence "((\<lambda>x. exp (x * ln a)) \<longlongrightarrow> 0) at_bot"
    by (intro filterlim_compose[OF exp_at_bot]) (simp add: algebra_simps)
  thus ?thesis using assms unfolding powr_def by simp
qed

lemma powr_at_bot_neg:
  assumes "(a::real) > 0" "a < 1"
  shows   "filterlim (\<lambda>x. a powr x) at_top at_bot"
proof-
  from assms have "LIM x at_bot. ln (inverse a) * -x :> at_top"
    by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const] filterlim_uminus_at_top_at_bot)
       (simp_all add: ln_inverse)
  with assms have "LIM x at_bot. x * ln a :> at_top" 
    by (subst (asm) ln_inverse) (simp_all add: mult.commute)
  hence "LIM x at_bot. exp (x * ln a) :> at_top"
    by (intro filterlim_compose[OF exp_at_top]) simp
  thus ?thesis using assms unfolding powr_def by simp
qed

lemma DERIV_powr: 
  assumes "x > 0"
  shows   "((\<lambda>x. x powr p) has_real_derivative p * x powr (p - 1)) (at x)"
proof-
  have "((\<lambda>x. exp (p * ln x)) has_real_derivative
         exp (p * ln x) * (p * inverse x)) (at x)"
    unfolding powr_def by (intro DERIV_fun_exp DERIV_cmult DERIV_ln) fact
  also have "exp (p * ln x) * (p * inverse x) = p * x powr (p - 1)"
    unfolding powr_def by (simp add: field_simps exp_diff assms)
  finally show ?thesis using assms by (subst DERIV_cong_ev[OF refl powr_eventually_exp_ln' refl])
qed

end
