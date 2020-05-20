(*
  File:   Akra_Bazzi_Library.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Lemma bucket for the Akra-Bazzi theorem.
*)

section \<open>Auxiliary lemmas\<close>
theory Akra_Bazzi_Library
imports 
  Complex_Main
  "Landau_Symbols.Landau_More"
begin

(* TODO: Move? *)

lemma ln_mono: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x \<le> y \<Longrightarrow> ln (x::real) \<le> ln y"
  by (subst ln_le_cancel_iff) simp_all

lemma ln_mono_strict: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x < y \<Longrightarrow> ln (x::real) < ln y"
  by (subst ln_less_cancel_iff) simp_all

declare DERIV_powr[THEN DERIV_chain2, derivative_intros]

lemma sum_pos':
  assumes "finite I"
  assumes "\<exists>x\<in>I. f x > (0 :: _ :: linordered_ab_group_add)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> f x \<ge> 0"
  shows   "sum f I > 0"
proof-
  from assms(2) guess x by (elim bexE) note x = this
  from x have "I = insert x I" by blast
  also from assms(1) have "sum f ... = f x + sum f (I - {x})" by (rule sum.insert_remove)
  also from x assms have "... > 0" by (intro add_pos_nonneg sum_nonneg) simp_all
  finally show ?thesis .
qed


lemma min_mult_left:
  assumes "(x::real) > 0"
  shows   "x * min y z = min (x*y) (x*z)"
  using assms by (auto simp add: min_def algebra_simps)

lemma max_mult_left:
  assumes "(x::real) > 0"
  shows   "x * max y z = max (x*y) (x*z)"
  using assms by (auto simp add: max_def algebra_simps)

lemma DERIV_nonneg_imp_mono:
  assumes "\<And>t. t\<in>{x..y} \<Longrightarrow> (f has_field_derivative f' t) (at t)"
  assumes "\<And>t. t\<in>{x..y} \<Longrightarrow> f' t \<ge> 0"
  assumes "(x::real) \<le> y"
  shows   "(f x :: real) \<le> f y"
proof (cases x y rule: linorder_cases)
  assume xy: "x < y"
  hence "\<exists>z. x < z \<and> z < y \<and> f y - f x = (y - x) * f' z"
    by (rule MVT2) (insert assms(1), simp)
  then guess z by (elim exE conjE) note z = this
  from z(1,2) assms(2) xy have "0 \<le> (y - x) * f' z" by (intro mult_nonneg_nonneg) simp_all
  also note z(3)[symmetric]
  finally show "f x \<le> f y" by simp
qed (insert assms(3), simp_all)

lemma eventually_conjE: "eventually (\<lambda>x. P x \<and> Q x) F \<Longrightarrow> (eventually P F \<Longrightarrow> eventually Q F \<Longrightarrow> R) \<Longrightarrow> R"
  apply (frule eventually_rev_mp[of _ _ P], simp)
  apply (drule eventually_rev_mp[of _ _ Q], simp)
  apply assumption
  done

lemma real_natfloor_nat: "x \<in> \<nat> \<Longrightarrow> real (nat \<lfloor>x\<rfloor>) = x" by (elim Nats_cases) simp

lemma eventually_natfloor:
  assumes "eventually P (at_top :: nat filter)"
  shows   "eventually (\<lambda>x. P (nat \<lfloor>x\<rfloor>)) (at_top :: real filter)"
proof-
  from assms obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> P n" using eventually_at_top_linorder by blast
  have "\<forall>n\<ge>real N. P (nat \<lfloor>n\<rfloor>)" by (intro allI impI N le_nat_floor) simp_all
  thus ?thesis using eventually_at_top_linorder by blast
qed

lemma tendsto_0_smallo_1: "f \<in> o(\<lambda>x. 1 :: real) \<Longrightarrow> (f \<longlongrightarrow> 0) at_top"
  by (drule smalloD_tendsto) simp

lemma smallo_1_tendsto_0: "(f \<longlongrightarrow> 0) at_top \<Longrightarrow> f \<in> o(\<lambda>x. 1 :: real)"
  by (rule smalloI_tendsto) simp_all

lemma filterlim_at_top_smallomega_1: 
  assumes "f \<in> \<omega>[F](\<lambda>x. 1 :: real)" "eventually (\<lambda>x. f x > 0) F"
  shows   "filterlim f at_top F"
proof -
  from assms have "filterlim (\<lambda>x. norm (f x / 1)) at_top F"
    by (intro smallomegaD_filterlim_at_top_norm) (auto elim: eventually_mono)
  also have "?this \<longleftrightarrow> ?thesis"
    using assms by (intro filterlim_cong refl) (auto elim!: eventually_mono)
  finally show ?thesis .
qed

lemma smallo_imp_abs_less_real:
  assumes "f \<in> o[F](g)" "eventually (\<lambda>x. g x > (0::real)) F"
  shows   "eventually (\<lambda>x. \<bar>f x\<bar> < g x) F"
proof -
  have "1/2 > (0::real)" by simp
  from landau_o.smallD[OF assms(1) this] assms(2) show ?thesis
    by eventually_elim auto
qed

lemma smallo_imp_less_real:
  assumes "f \<in> o[F](g)" "eventually (\<lambda>x. g x > (0::real)) F"
  shows   "eventually (\<lambda>x. f x < g x) F"
  using smallo_imp_abs_less_real[OF assms] by eventually_elim simp

lemma smallo_imp_le_real: 
  assumes "f \<in> o[F](g)" "eventually (\<lambda>x. g x \<ge> (0::real)) F"
  shows   "eventually (\<lambda>x. f x \<le> g x) F"
  using landau_o.smallD[OF assms(1) zero_less_one] assms(2) by eventually_elim simp

(* TODO MOVE *)
lemma filterlim_at_right: 
  "filterlim f (at_right a) F \<longleftrightarrow> eventually (\<lambda>x. f x > a) F \<and> filterlim f (nhds a) F"
  by (subst filterlim_at) (auto elim!: eventually_mono)
(* END TODO *)

lemma one_plus_x_powr_approx_ex:
  assumes x: "abs (x::real) \<le> 1/2"
  obtains t where "abs t < 1/2" "(1 + x) powr p = 
    1 + p * x + p * (p - 1) * (1 + t) powr (p - 2) / 2 * x ^ 2"
proof (cases "x = 0")
  assume x': "x \<noteq> 0"
  let ?f = "\<lambda>x. (1 + x) powr p"
  let ?f' = "\<lambda>x. p * (1 + x) powr (p - 1)"
  let ?f'' = "\<lambda>x. p * (p - 1) * (1 + x) powr (p - 2)"
  let ?fs = "(!) [?f, ?f', ?f'']"
 
  have A: "\<forall>m t. m < 2 \<and> t \<ge> -0.5 \<and> t \<le> 0.5 \<longrightarrow> (?fs m has_real_derivative ?fs (Suc m) t) (at t)"
  proof (clarify)
    fix m :: nat and t :: real assume m: "m < 2" and t: "t \<ge> -0.5" "t \<le> 0.5"
    thus "(?fs m has_real_derivative ?fs (Suc m) t) (at t)"
      using m by (cases m) (force intro: derivative_eq_intros algebra_simps)+
  qed
  have "\<exists>t. (if x < 0 then x < t \<and> t < 0 else 0 < t \<and> t < x) \<and>
              (1 + x) powr p = (\<Sum>m<2. ?fs m 0 / (fact m) * (x - 0)^m) + 
              ?fs 2 t / (fact 2) * (x - 0)\<^sup>2"
    using assms x' by (intro Taylor[OF _ _ A]) simp_all
  then guess t by (elim exE conjE)
  note t = this
  with assms have "abs t < 1/2" by (auto split: if_split_asm)
  moreover from t(2) have "(1 + x) powr p = 1 + p * x + p * (p - 1) * (1 + t) powr (p - 2) / 2 * x ^ 2"
    by (simp add: numeral_2_eq_2 of_nat_Suc)
  ultimately show ?thesis by (rule that)
next
  assume "x = 0"
  with that[of 0] show ?thesis by simp
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

lemma one_plus_x_powr_Taylor2:
  obtains k where "\<And>x. abs (x::real) \<le> 1/2 \<Longrightarrow> abs ((1 + x) powr p - 1 - p*x) \<le> k*x^2"
proof-
  define k where "k = \<bar>p*(p - 1)\<bar> * max ((1/2) powr (p - 2)) ((3/2) powr (p - 2)) / 2"
  show ?thesis
  proof (rule that[of k])
    fix x :: real assume "abs x \<le> 1/2"
    from one_plus_x_powr_approx_ex[OF this, of p] guess t . note t = this
    from t have "abs ((1 + x) powr p - 1 - p*x) = \<bar>p*(p - 1)\<bar> * (1 + t) powr (p - 2)/2 * x\<^sup>2"
      by (simp add: abs_mult)
    also from t(1) have "(1 + t) powr (p - 2) \<le> max ((1/2) powr (p - 2)) ((3/2) powr (p - 2))"
      by (intro powr_upper_bound) simp_all
    finally show "abs ((1 + x) powr p - 1 - p*x) \<le> k*x^2" 
      by (simp add: mult_left_mono mult_right_mono k_def)
  qed
qed

lemma one_plus_x_powr_Taylor2_bigo:
  assumes lim: "(f \<longlongrightarrow> 0) F"
  shows   "(\<lambda>x. (1 + f x) powr (p::real) - 1 - p * f x) \<in> O[F](\<lambda>x. f x ^ 2)"
proof -
  from one_plus_x_powr_Taylor2[of p] guess k .
  moreover from tendstoD[OF lim, of "1/2"] 
    have "eventually (\<lambda>x. abs (f x) < 1/2) F" by (simp add: dist_real_def)
  ultimately have "eventually (\<lambda>x. norm ((1 + f x) powr p - 1 - p * f x) \<le> k * norm (f x ^ 2)) F"
    by (auto elim!: eventually_mono)
  thus ?thesis by (rule bigoI)
qed

lemma one_plus_x_powr_Taylor1_bigo:
  assumes lim: "(f \<longlongrightarrow> 0) F"
  shows   "(\<lambda>x. (1 + f x) powr (p::real) - 1) \<in> O[F](\<lambda>x. f x)"
proof -
  from assms have "(\<lambda>x. (1 + f x) powr p - 1 - p * f x) \<in> O[F](\<lambda>x. (f x)\<^sup>2)"
    by (rule one_plus_x_powr_Taylor2_bigo)
  also from assms have "f \<in> O[F](\<lambda>_. 1)" by (intro bigoI_tendsto) simp_all
  from landau_o.big.mult[of f F f, OF _ this] have "(\<lambda>x. (f x)^2) \<in> O[F](\<lambda>x. f x)"
    by (simp add: power2_eq_square)
  finally have A: "(\<lambda>x. (1 + f x) powr p - 1 - p * f x) \<in> O[F](f)" .
  have B: "(\<lambda>x. p * f x) \<in> O[F](f)" by simp
  from sum_in_bigo(1)[OF A B] show ?thesis by simp
qed

lemma x_times_x_minus_1_nonneg: "x \<le> 0 \<or> x \<ge> 1 \<Longrightarrow> (x::_::linordered_idom) * (x - 1) \<ge> 0"
proof (elim disjE)
  assume x: "x \<le> 0"
  also have "0 \<le> x^2" by simp
  finally show "x * (x - 1) \<ge> 0" by (simp add: power2_eq_square algebra_simps)
qed simp

lemma x_times_x_minus_1_nonpos: "x \<ge> 0 \<Longrightarrow> x \<le> 1 \<Longrightarrow> (x::_::linordered_idom) * (x - 1) \<le> 0"
  by (intro mult_nonneg_nonpos) simp_all

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

lemma real_powr_at_bot:
  assumes "(a::real) > 1"
  shows   "((\<lambda>x. a powr x) \<longlongrightarrow> 0) at_bot"
proof-
  from assms have "filterlim (\<lambda>x. ln a * x) at_bot at_bot"
    by (intro filterlim_tendsto_pos_mult_at_bot[OF tendsto_const _ filterlim_ident]) auto
  hence "((\<lambda>x. exp (x * ln a)) \<longlongrightarrow> 0) at_bot"
    by (intro filterlim_compose[OF exp_at_bot]) (simp add: algebra_simps)
  thus ?thesis using assms unfolding powr_def by simp
qed

lemma real_powr_at_bot_neg:
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

lemma real_powr_at_top_neg: 
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

lemma eventually_nat_real:
  assumes "eventually P (at_top :: real filter)"
  shows   "eventually (\<lambda>x. P (real x)) (at_top :: nat filter)"
  using assms filterlim_real_sequentially
  unfolding filterlim_def le_filter_def eventually_filtermap by auto

end
