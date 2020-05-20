chapter \<open>Exp Upper and Lower Bounds\<close>

theory Exp_Bounds
imports Bounds_Lemmas
        "HOL-Library.Sum_of_Squares"
        Sturm_Sequences.Sturm

begin

text\<open>Covers all bounds used in exp-upper.ax, exp-lower.ax and exp-extended.ax.\<close>

section \<open>Taylor Series Bounds\<close>

text\<open>\<open>exp_positive\<close> is the theorem @{thm Transcendental.exp_ge_zero}\<close>

text\<open>\<open>exp_lower_taylor_1\<close> is the theorem @{thm Transcendental.exp_ge_add_one_self}\<close>

text\<open>All even approximants are lower bounds.\<close>
lemma exp_lower_taylor_even: 
  fixes x::real
  shows "even n \<Longrightarrow> (\<Sum>m<n. (x ^ m) / (fact m)) \<le> exp x"
  using Maclaurin_exp_le [of x n]
  by (auto simp add: zero_le_even_power)

lemma exp_upper_taylor_even:
  fixes x::real
  assumes n: "even n"
      and pos: "(\<Sum>m<n. ((-x) ^ m) / (fact m)) > 0"  (is "?sum > 0")
    shows "exp x \<le> inverse ?sum"
  using exp_lower_taylor_even [OF n, of "-x"]
  by (metis exp_minus inverse_inverse_eq le_imp_inverse_le pos)

text\<open>3 if the previous lemma is expressed in terms of @{term "2*m"}.\<close>
lemma exp_lower_taylor_3:
  fixes x::real
  shows "1 + x + (1/2)*x^2 + (1/6)*x^3 + (1/24)*x^4 + (1/120)*x^5 \<le> exp x"
  by (rule order_trans [OF _ exp_lower_taylor_even [of 6]])
     (auto simp: lessThan_nat_numeral fact_numeral)

lemma exp_lower_taylor_3_cubed:
  fixes x::real
  shows "(1 + x/3 + (1/2)*(x/3)^2 + (1/6)*(x/3)^3 + (1/24)*(x/3)^4 + (1/120)*(x/3)^5)^3 \<le> exp x"
proof -
  have "(1 + x/3 + (1/2)*(x/3)^2 + (1/6)*(x/3)^3 + (1/24)*(x/3)^4 + (1/120)*(x/3)^5) ^ 3
        \<le> exp (x/3) ^ 3"
    by (metis power_mono_odd odd_numeral exp_lower_taylor_3)
 also have "... = exp x"
   by (simp add: exp_of_nat_mult [symmetric])
 finally show ?thesis .
qed

lemma exp_lower_taylor_2:
  fixes x::real
  shows "1 + x + (1/2)*x^2 + (1/6)*x^3 \<le> exp x"
proof -
  have "even (4::nat)" by simp
  then have "(\<Sum>m<4. x ^ m / (fact m)) \<le> exp x"
    by (rule exp_lower_taylor_even)
  then show ?thesis by (auto simp add: numeral_eq_Suc)
qed

lemma exp_upper_bound_case_3:
  fixes x::real
  assumes "x \<le> 3.19"
  shows "exp x \<le> 2304 / (-(x^3) + 6*x^2 - 24*x + 48)^2"
proof -
  have "(1/48)*(-(x^3) + 6*x^2 - 24*x + 48) = (1 + (-x/2) + (1/2)*(-x/2)^2 + (1/6)*(-x/2)^3)"
    by (simp add: field_simps power2_eq_square power3_eq_cube)
  also have "... \<le> exp (-x/2)"
    by (rule exp_lower_taylor_2)
  finally have 1: "(1/48)*(-(x^3) + 6*x^2 - 24*x + 48) \<le> exp (-x/2)" .
  have "(-(x^3) + 6*x^2 - 24*x + 48)^2 / 2304 = ((1/48)*(-(x^3) + 6*x^2 - 24*x + 48))^2"
    by (simp add: field_simps power2_eq_square power3_eq_cube)
  also have "... \<le> (exp (-x/2))^2"
    apply (rule power_mono [OF 1])
    apply (simp add: algebra_simps)
    using assms
    apply (sos "((R<1 + ((R<1 * ((R<1323/13 * [~15/49*x + 1]^2) + (R<1/637 * [x]^2))) + (((A<0 * R<1) * (R<50/13 * [1]^2)) + ((A<=0 * R<1) * ((R<56/13 * [~5/56*x + 1]^2) + (R<199/728 * [x]^2)))))))")
    done
  also have "... = inverse (exp x)"
    by (metis exp_minus mult_exp_exp power2_eq_square field_sum_of_halves)
  finally have 2: "(-(x^3) + 6*x^2 - 24*x + 48)^2 / 2304 \<le> inverse (exp x)" .
  have "6 * x\<^sup>2 - x ^ 3 - 24 * x + 48 \<noteq> 0" using assms
    by (sos "((R<1 + (([~400/13] * A=0) + ((R<1 * ((R<1323/13 * [~15/49*x + 1]^2) + (R<1/637 * [x]^2))) + ((A<=0 * R<1) * ((R<56/13 * [~5/56*x + 1]^2) + (R<199/728 * [x]^2)))))))")
  then show ?thesis
    using Fields.linordered_field_class.le_imp_inverse_le [OF 2]
    by simp
qed

lemma exp_upper_bound_case_5:
  fixes x::real
  assumes "x \<le> 6.36"
  shows "exp x \<le> 21743271936 / (-(x^3) + 12*x^2 - 96*x + 384)^4"
proof -
  have "(1/384)*(-(x^3) + 12*x^2 - 96*x + 384) = (1 + (-x/4) + (1/2)*(-x/4)^2 + (1/6)*(-x/4)^3)"
    by (simp add: field_simps power2_eq_square power3_eq_cube)
  also have "... \<le> exp (-x/4)"
    by (rule exp_lower_taylor_2)
  finally have 1: "(1/384)*(-(x^3) + 12*x^2 - 96*x + 384) \<le> exp (-x/4)" .
  have "(-(x^3) + 12*x^2 - 96*x + 384)^4 / 21743271936 = ((1/384)*(-(x^3) + 12*x^2 - 96*x + 384))^4"
    by (simp add: divide_simps)
  also have "... \<le> (exp (-x/4))^4"
    apply (rule power_mono [OF 1])
    apply (simp add: algebra_simps)
    using assms
    apply (sos "((R<1 + ((R<1 * ((R<1777/32 * [~539/3554*x + 1]^2) + (R<907/227456 * [x]^2))) + (((A<0 * R<1) * (R<25/1024 * [1]^2)) + ((A<=0 * R<1) * ((R<49/32 * [~2/49*x + 1]^2) + (R<45/1568 * [x]^2)))))))")
    done
  also have "... = inverse (exp x)"
    by (simp add: exp_of_nat_mult [symmetric] exp_minus [symmetric])
  finally have 2: "(-(x^3) + 12*x^2 - 96*x + 384)^4 / 21743271936 \<le> inverse (exp x)" .
  have "12 * x\<^sup>2 - x ^ 3 - 96 * x + 384 \<noteq> 0" using assms
    by (sos "((R<1 + (([~25/32] * A=0) + ((R<1 * ((R<1777/32 * [~539/3554*x + 1]^2) + (R<907/227456 * [x]^2))) + ((A<=0 * R<1) * ((R<49/32 * [~2/49*x + 1]^2) + (R<45/1568 * [x]^2)))))))")
  then show ?thesis
    using Fields.linordered_field_class.le_imp_inverse_le [OF 2]
    by simp
qed


section \<open>Continued Fraction Bound 2\<close>

definition exp_cf2 :: "real \<Rightarrow> real"
  where "exp_cf2 \<equiv> \<lambda>x. (x^2 + 6*x + 12) / (x^2 - 6*x + 12)"

lemma denom_cf2_pos: fixes x::real shows "x\<^sup>2 - 6 * x + 12 > 0"
  by (sos "((R<1 + ((R<1 * ((R<5 * [~3/10*x + 1]^2) + (R<1/20 * [x]^2))) + ((A<=0 * R<1) * (R<1/2 * [1]^2)))))")

lemma numer_cf2_pos: fixes x::real shows "x\<^sup>2 + 6 * x + 12 > 0"
  by (sos "((R<1 + ((R<1 * ((R<5 * [3/10*x + 1]^2) + (R<1/20 * [x]^2))) + ((A<=0 * R<1) * (R<1/2 * [1]^2)))))")

lemma exp_cf2_pos: "exp_cf2 x > 0"
  unfolding exp_cf2_def
  by (auto simp add: divide_simps denom_cf2_pos numer_cf2_pos)

definition diff_delta_lnexp_cf2 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf2 \<equiv> \<lambda>x. - (x^4) / ((x^2 - 6*x + 12) * (x^2 + 6*x + 12))"

lemma d_delta_lnexp_cf2_nonpos: "diff_delta_lnexp_cf2 x \<le> 0"
unfolding diff_delta_lnexp_cf2_def
by (sos "(((R<1 + ((R<1 * ((R<5/4 * [~3/40*x^2 + 1]^2) + (R<11/1280 * [x^2]^2))) +
      ((A<1 * R<1) * (R<1/64 * [1]^2))))) & ((R<1 + ((R<1 * ((R<5/4 * [~3/40*x^2 + 1]^2) + (R<11/1280 * [x^2]^2))) + ((A<1 * R<1) * (R<1/64 * [1]^2))))))")

lemma d_delta_lnexp_cf2:
    "((\<lambda>x. ln (exp_cf2 x) - x) has_field_derivative diff_delta_lnexp_cf2 x) (at x)"
  unfolding exp_cf2_def diff_delta_lnexp_cf2_def
  apply (intro derivative_eq_intros | simp)+
  apply (metis exp_cf2_def exp_cf2_pos)
  apply (simp_all add: )
  using denom_cf2_pos [of x] numer_cf2_pos [of x]
  apply (auto simp: divide_simps)
  apply algebra
  done

text\<open>Upper bound for non-positive x\<close>
lemma ln_exp_cf2_upper_bound_neg:
  assumes "x \<le> 0"
    shows "x \<le> ln (exp_cf2 x)"
  by (rule gen_upper_bound_decreasing [OF assms d_delta_lnexp_cf2 d_delta_lnexp_cf2_nonpos])
     (simp add: exp_cf2_def)

theorem exp_cf2_upper_bound_neg: "x\<le>0 \<Longrightarrow> exp(x) \<le> exp_cf2 x"
  by (metis ln_exp_cf2_upper_bound_neg exp_cf2_pos exp_le_cancel_iff exp_ln_iff)

text\<open>Lower bound for non-negative x\<close>
lemma ln_exp_cf2_lower_bound_pos:
  assumes "0\<le>x"
    shows "ln (exp_cf2 x) \<le> x"
  by (rule gen_lower_bound_increasing [OF assms d_delta_lnexp_cf2 d_delta_lnexp_cf2_nonpos])
     (simp add: exp_cf2_def)

theorem exp_cf2_lower_bound_pos: "0\<le>x \<Longrightarrow> exp_cf2 x \<le> exp x"
  by (metis exp_cf2_pos exp_le_cancel_iff exp_ln ln_exp_cf2_lower_bound_pos)


section \<open>Continued Fraction Bound 3\<close>

text\<open>This bound crosses the X-axis twice, causing complications.\<close>

definition numer_cf3 :: "real \<Rightarrow> real"
  where "numer_cf3 \<equiv> \<lambda>x. x^3 + 12*x^2 + 60*x + 120"

definition exp_cf3 :: "real \<Rightarrow> real"
  where "exp_cf3 \<equiv> \<lambda>x. numer_cf3 x / numer_cf3 (-x)"

lemma numer_cf3_pos: "-4.64 \<le> x \<Longrightarrow> numer_cf3 x > 0"
  unfolding numer_cf3_def
  by sturm

lemma exp_cf3_pos: "numer_cf3 x > 0 \<Longrightarrow> numer_cf3 (-x) > 0 \<Longrightarrow> exp_cf3 x > 0"
  by (simp add: exp_cf3_def)

definition diff_delta_lnexp_cf3 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf3 \<equiv> \<lambda>x. (x^6) / (numer_cf3 (-x) * numer_cf3 x)"

lemma d_delta_lnexp_cf3_nonneg: "numer_cf3 x > 0 \<Longrightarrow> numer_cf3 (-x) > 0 \<Longrightarrow> diff_delta_lnexp_cf3 x \<ge> 0"
  unfolding diff_delta_lnexp_cf3_def
  by (auto simp: mult_less_0_iff intro: divide_nonneg_neg)

lemma d_delta_lnexp_cf3:
  assumes "numer_cf3 x > 0" "numer_cf3 (-x) > 0"
  shows "((\<lambda>x. ln (exp_cf3 x) - x) has_field_derivative diff_delta_lnexp_cf3 x) (at x)"
unfolding exp_cf3_def numer_cf3_def diff_delta_lnexp_cf3_def
apply (intro derivative_eq_intros | simp)+
using assms numer_cf3_pos [of x] numer_cf3_pos [of "-x"]
apply (auto simp: numer_cf3_def)
apply (auto simp add: divide_simps add_nonneg_eq_0_iff)
apply algebra
done

lemma numer_cf3_mono: "y \<le> x \<Longrightarrow> numer_cf3 y \<le> numer_cf3 x"
  unfolding numer_cf3_def
  by (sos "(((A<0 * R<1) + ((A<=0 * R<1) * ((R<60 * [1/10*x + 1/10*y + 1]^2) +
                ((R<2/5 * [x + ~1/4*y]^2) + (R<3/8 * [y]^2))))))")

text\<open>Upper bound for non-negative x\<close>
lemma ln_exp_cf3_upper_bound_nonneg:
  assumes x0: "0 \<le> x" and xless: "numer_cf3 (-x) > 0"
    shows "x \<le> ln (exp_cf3 x)"
proof -
  have ncf3: "\<And>y. 0 \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> numer_cf3 (-y) > 0"
    by (metis neg_le_iff_le numer_cf3_mono order.strict_trans2 xless)
  show ?thesis
    apply (rule gen_upper_bound_increasing [OF x0 d_delta_lnexp_cf3 d_delta_lnexp_cf3_nonneg])
    apply (auto simp add: ncf3 assms numer_cf3_pos)
    apply (simp add: exp_cf3_def numer_cf3_def)
    done
qed

theorem exp_cf3_upper_bound_pos: "0 \<le> x \<Longrightarrow> numer_cf3 (-x) > 0 \<Longrightarrow> exp x \<le> exp_cf3 x"
  using ln_exp_cf3_upper_bound_nonneg [of x] exp_cf3_pos [of x] numer_cf3_pos [of x]
  by auto (metis exp_le_cancel_iff exp_ln_iff)

corollary "0 \<le> x \<Longrightarrow> x \<le> 4.64 \<Longrightarrow> exp x \<le> exp_cf3 x"
  by (metis numer_cf3_pos neg_le_iff_le exp_cf3_upper_bound_pos)


text\<open>Lower bound for negative x, provided @{term"exp_cf3 x > 0"}]\<close>
lemma ln_exp_cf3_lower_bound_neg:
  assumes x0: "x \<le> 0" and xgtr: "numer_cf3 x > 0"
    shows "ln (exp_cf3 x) \<le> x"
proof -
  have ncf3: "\<And>y. x \<le> y \<Longrightarrow> y \<le> 0 \<Longrightarrow> numer_cf3 y > 0"
    by (metis dual_order.strict_trans1 numer_cf3_mono xgtr)
  show ?thesis
    apply (rule gen_lower_bound_decreasing [OF x0 d_delta_lnexp_cf3 d_delta_lnexp_cf3_nonneg])
    apply (auto simp add: ncf3 assms numer_cf3_pos)
    apply (simp add: exp_cf3_def numer_cf3_def)
    done
qed

theorem exp_cf3_lower_bound_pos:
  assumes "x \<le> 0" shows "exp_cf3 x \<le> exp x"
proof (cases "numer_cf3 x > 0")
  case True
  then have "exp_cf3 x > 0"
    using assms numer_cf3_pos [of "-x"]
    by (auto simp: exp_cf3_pos)
  then show ?thesis
  using ln_exp_cf3_lower_bound_neg [of x] assms True
    by auto (metis exp_le_cancel_iff exp_ln_iff)
next
  case False
  then have "exp_cf3 x \<le> 0"
    using assms numer_cf3_pos [of "-x"]
    unfolding exp_cf3_def
    by (simp add: divide_nonpos_pos)
  then show ?thesis
    by (metis exp_ge_zero order.trans)
qed


section \<open>Continued Fraction Bound 4\<close>

text \<open>Here we have the extended exp continued fraction bounds\<close>

definition numer_cf4 :: "real \<Rightarrow> real"
  where "numer_cf4 \<equiv> \<lambda>x. x^4 + 20*x^3 + 180*x^2 + 840*x + 1680"

definition exp_cf4 :: "real \<Rightarrow> real"
  where "exp_cf4 \<equiv> \<lambda>x. numer_cf4 x / numer_cf4 (-x)"

lemma numer_cf4_pos: fixes x::real shows "numer_cf4 x > 0"
unfolding numer_cf4_def
by (sos "((R<1 + ((R<1 * ((R<4469/256 * [1135/71504*x^2 + 4725/17876*x + 1]^2) + ((R<3728645/18305024 * [536265/2982916*x^2 + x]^2) + (R<106265/24436047872 * [x^2]^2)))) + ((A<=0 * R<1) * (R<45/4096 * [1]^2)))))")

lemma exp_cf4_pos: "exp_cf4 x > 0"
  unfolding exp_cf4_def
  by (auto simp add: divide_simps numer_cf4_pos)

definition diff_delta_lnexp_cf4 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf4 \<equiv> \<lambda>x. - (x^8) / (numer_cf4 (-x) * numer_cf4 x)"

lemma d_delta_lnexp_cf4_nonpos: "diff_delta_lnexp_cf4 x \<le> 0"
  unfolding diff_delta_lnexp_cf4_def
  using numer_cf4_pos [of x] numer_cf4_pos [of "-x"]
  by (simp add: zero_le_divide_iff zero_le_mult_iff)

lemma d_delta_lnexp_cf4:
    "((\<lambda>x. ln (exp_cf4 x) - x) has_field_derivative diff_delta_lnexp_cf4 x) (at x)"
  unfolding exp_cf4_def numer_cf4_def diff_delta_lnexp_cf4_def
  apply (intro derivative_eq_intros | simp)+
  using exp_cf4_pos
  apply (simp add: exp_cf4_def numer_cf4_def)
  apply (simp_all add: )
  using numer_cf4_pos [of x]  numer_cf4_pos [of "-x"]
  apply (auto simp: divide_simps numer_cf4_def)
  apply algebra
  done

text\<open>Upper bound for non-positive x\<close>
lemma ln_exp_cf4_upper_bound_neg:
  assumes "x \<le> 0"
    shows "x \<le> ln (exp_cf4 x)"
  by (rule gen_upper_bound_decreasing [OF assms d_delta_lnexp_cf4 d_delta_lnexp_cf4_nonpos])
     (simp add: exp_cf4_def numer_cf4_def)

theorem exp_cf4_upper_bound_neg: "x\<le>0 \<Longrightarrow> exp(x) \<le> exp_cf4 x"
  by (metis ln_exp_cf4_upper_bound_neg exp_cf4_pos exp_le_cancel_iff exp_ln_iff)

text\<open>Lower bound for non-negative x\<close>
lemma ln_exp_cf4_lower_bound_pos:
  assumes "0\<le>x"
    shows "ln (exp_cf4 x) \<le> x"
  by (rule gen_lower_bound_increasing [OF assms d_delta_lnexp_cf4 d_delta_lnexp_cf4_nonpos])
     (simp add: exp_cf4_def numer_cf4_def)

theorem exp_cf4_lower_bound_pos: "0\<le>x \<Longrightarrow> exp_cf4 x \<le> exp x"
  by (metis exp_cf4_pos exp_le_cancel_iff exp_ln ln_exp_cf4_lower_bound_pos)


section \<open>Continued Fraction Bound 5\<close>

text\<open>This bound crosses the X-axis twice, causing complications.\<close>

definition numer_cf5 :: "real \<Rightarrow> real"
  where "numer_cf5 \<equiv> \<lambda>x. x^5 + 30*x^4 + 420*x^3 + 3360*x^2 + 15120*x + 30240"

definition exp_cf5 :: "real \<Rightarrow> real"
  where "exp_cf5 \<equiv> \<lambda>x. numer_cf5 x / numer_cf5 (-x)"

lemma numer_cf5_pos: "-7.293 \<le> x \<Longrightarrow> numer_cf5 x > 0"
  unfolding numer_cf5_def
  by sturm

lemma exp_cf5_pos: "numer_cf5 x > 0 \<Longrightarrow> numer_cf5 (-x) > 0 \<Longrightarrow> exp_cf5 x > 0"
  unfolding exp_cf5_def numer_cf5_def
  by (simp add: divide_neg_neg)

definition diff_delta_lnexp_cf5 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf5 \<equiv> \<lambda>x. (x^10) / (numer_cf5 (-x) * numer_cf5 x)"

lemma d_delta_lnexp_cf5_nonneg: "numer_cf5 x > 0 \<Longrightarrow> numer_cf5 (-x) > 0 \<Longrightarrow> diff_delta_lnexp_cf5 x \<ge> 0"
  unfolding diff_delta_lnexp_cf5_def
  by (auto simp add: mult_less_0_iff intro: divide_nonneg_neg )

lemma d_delta_lnexp_cf5:
  assumes "numer_cf5 x > 0" "numer_cf5 (-x) > 0"
  shows "((\<lambda>x. ln (exp_cf5 x) - x) has_field_derivative diff_delta_lnexp_cf5 x) (at x)"
unfolding exp_cf5_def numer_cf5_def diff_delta_lnexp_cf5_def
apply (intro derivative_eq_intros | simp)+
using assms numer_cf5_pos [of x] numer_cf5_pos [of "-x"]
apply (auto simp: numer_cf5_def)
apply (auto simp add: divide_simps add_nonneg_eq_0_iff)
apply algebra
done

subsection\<open>Proving monotonicity via a non-negative derivative\<close>

definition numer_cf5_deriv :: "real \<Rightarrow> real"
  where "numer_cf5_deriv \<equiv> \<lambda>x. 5*x^4 + 120*x^3 + 1260*x^2 + 6720*x + 15120"

lemma numer_cf5_deriv:
  shows "(numer_cf5 has_field_derivative numer_cf5_deriv x) (at x)"
  unfolding numer_cf5_def numer_cf5_deriv_def
  by (intro derivative_eq_intros | simp)+

lemma numer_cf5_deriv_pos: "numer_cf5_deriv x \<ge> 0"
  unfolding numer_cf5_deriv_def
  by (sos "((R<1 + ((R<1 * ((R<185533/8192 * [73459/5937056*x^2 + 43050/185533*x + 1]^2) + ((R<4641265253/24318181376 * [700850925/4641265253*x^2 + x]^2) + (R<38142496079/38933754831437824 * [x^2]^2)))) + ((A<0 * R<1) * (R<205/131072 * [1]^2)))))")

lemma numer_cf5_mono: "y \<le> x \<Longrightarrow> numer_cf5 y \<le> numer_cf5 x"
  by (auto intro: DERIV_nonneg_imp_nondecreasing numer_cf5_deriv numer_cf5_deriv_pos)

subsection\<open>Results\<close>

text\<open>Upper bound for non-negative x\<close>
lemma ln_exp_cf5_upper_bound_nonneg:
  assumes x0: "0 \<le> x" and xless: "numer_cf5 (-x) > 0"
    shows "x \<le> ln (exp_cf5 x)"
proof -
  have ncf5: "\<And>y. 0 \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> numer_cf5 (-y) > 0"
    by (metis neg_le_iff_le numer_cf5_mono order.strict_trans2 xless)
  show ?thesis
    apply (rule gen_upper_bound_increasing [OF x0 d_delta_lnexp_cf5 d_delta_lnexp_cf5_nonneg])
    apply (auto simp add: ncf5 assms numer_cf5_pos)
    apply (simp add: exp_cf5_def numer_cf5_def)
    done
qed

theorem exp_cf5_upper_bound_pos: "0 \<le> x \<Longrightarrow> numer_cf5 (-x) > 0 \<Longrightarrow> exp x \<le> exp_cf5 x"
  using ln_exp_cf5_upper_bound_nonneg [of x] exp_cf5_pos [of x] numer_cf5_pos [of x]
  by auto (metis exp_le_cancel_iff exp_ln_iff)

corollary "0 \<le> x \<Longrightarrow> x \<le> 7.293 \<Longrightarrow> exp x \<le> exp_cf5 x"
  by (metis neg_le_iff_le numer_cf5_pos exp_cf5_upper_bound_pos)

text\<open>Lower bound for negative x, provided @{term"exp_cf5 x > 0"}]\<close>
lemma ln_exp_cf5_lower_bound_neg:
  assumes x0: "x \<le> 0" and xgtr: "numer_cf5 x > 0"
    shows "ln (exp_cf5 x) \<le> x"
proof -
  have ncf5: "\<And>y. x \<le> y \<Longrightarrow> y \<le> 0 \<Longrightarrow> numer_cf5 y > 0"
    by (metis dual_order.strict_trans1 numer_cf5_mono xgtr)
  show ?thesis
    apply (rule gen_lower_bound_decreasing [OF x0 d_delta_lnexp_cf5 d_delta_lnexp_cf5_nonneg])
    apply (auto simp add: ncf5 assms numer_cf5_pos)
    apply (simp add: exp_cf5_def numer_cf5_def)
    done
qed

theorem exp_cf5_lower_bound_pos:
  assumes "x \<le> 0" shows "exp_cf5 x \<le> exp x"
proof (cases "numer_cf5 x > 0")
  case True
  then have "exp_cf5 x > 0"
    using assms numer_cf5_pos [of "-x"]
    by (auto simp: exp_cf5_pos)
  then show ?thesis
  using ln_exp_cf5_lower_bound_neg [of x] assms True
    by auto (metis exp_le_cancel_iff exp_ln_iff)
next
  case False
  then have "exp_cf5 x \<le> 0"
    using assms numer_cf5_pos [of "-x"]
    unfolding exp_cf5_def numer_cf5_def
    by (simp add: divide_nonpos_pos)
  then show ?thesis
    by (metis exp_ge_zero order.trans)
qed


section \<open>Continued Fraction Bound 6\<close>

definition numer_cf6 :: "real \<Rightarrow> real"
  where "numer_cf6 \<equiv> \<lambda>x. x^6 + 42*x^5 + 840*x^4 + 10080*x^3 + 75600*x^2 + 332640*x + 665280"

definition exp_cf6 :: "real \<Rightarrow> real"
  where "exp_cf6 \<equiv> \<lambda>x. numer_cf6 x / numer_cf6 (-x)"

lemma numer_cf6_pos: fixes x::real shows "numer_cf6 x > 0"
  unfolding numer_cf6_def
  by sturm

lemma exp_cf6_pos: "exp_cf6 x > 0"
  unfolding exp_cf6_def
  by (auto simp add: divide_simps numer_cf6_pos)

definition diff_delta_lnexp_cf6 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf6 \<equiv> \<lambda>x. - (x^12) / (numer_cf6 (-x) * numer_cf6 x)"

lemma d_delta_lnexp_cf6_nonpos: "diff_delta_lnexp_cf6 x \<le> 0"
  unfolding diff_delta_lnexp_cf6_def
  using numer_cf6_pos [of x]  numer_cf6_pos [of "-x"]
  by (simp add: zero_le_divide_iff zero_le_mult_iff)

lemma d_delta_lnexp_cf6:
    "((\<lambda>x. ln (exp_cf6 x) - x) has_field_derivative diff_delta_lnexp_cf6 x) (at x)"
  unfolding exp_cf6_def diff_delta_lnexp_cf6_def numer_cf6_def
  apply (intro derivative_eq_intros | simp)+
  using exp_cf6_pos
  apply (simp add: exp_cf6_def numer_cf6_def)
  apply (simp_all add: )
  using numer_cf6_pos [of x]  numer_cf6_pos [of "-x"]
  apply (auto simp: divide_simps numer_cf6_def)
  apply algebra
  done

text\<open>Upper bound for non-positive x\<close>
lemma ln_exp_cf6_upper_bound_neg:
  assumes "x \<le> 0"
    shows "x \<le> ln (exp_cf6 x)"
  by (rule gen_upper_bound_decreasing [OF assms d_delta_lnexp_cf6 d_delta_lnexp_cf6_nonpos])
     (simp add: exp_cf6_def numer_cf6_def)

theorem exp_cf6_upper_bound_neg: "x\<le>0 \<Longrightarrow> exp(x) \<le> exp_cf6 x"
  by (metis ln_exp_cf6_upper_bound_neg exp_cf6_pos exp_le_cancel_iff exp_ln_iff)

text\<open>Lower bound for non-negative x\<close>
lemma ln_exp_cf6_lower_bound_pos:
  assumes "0\<le>x"
    shows "ln (exp_cf6 x) \<le> x"
  by (rule gen_lower_bound_increasing [OF assms d_delta_lnexp_cf6 d_delta_lnexp_cf6_nonpos])
     (simp add: exp_cf6_def numer_cf6_def)

theorem exp_cf6_lower_bound_pos: "0\<le>x \<Longrightarrow> exp_cf6 x \<le> exp x"
  by (metis exp_cf6_pos exp_le_cancel_iff exp_ln ln_exp_cf6_lower_bound_pos)

  
section \<open>Continued Fraction Bound 7\<close>

text\<open>This bound crosses the X-axis twice, causing complications.\<close>

definition numer_cf7 :: "real \<Rightarrow> real"
  where "numer_cf7 \<equiv> \<lambda>x. x^7 + 56*x^6 + 1512*x^5 + 25200*x^4 + 277200*x^3 + 1995840*x^2 + 8648640*x + 17297280"

definition exp_cf7 :: "real \<Rightarrow> real"
  where "exp_cf7 \<equiv> \<lambda>x. numer_cf7 x / numer_cf7 (-x)"

lemma numer_cf7_pos: "-9.943 \<le> x \<Longrightarrow> numer_cf7 x > 0"
  unfolding numer_cf7_def
  by sturm

lemma exp_cf7_pos: "numer_cf7 x > 0 \<Longrightarrow> numer_cf7 (-x) > 0 \<Longrightarrow> exp_cf7 x > 0"
  by (simp add: exp_cf7_def)

definition diff_delta_lnexp_cf7 :: "real \<Rightarrow> real"
  where "diff_delta_lnexp_cf7 \<equiv> \<lambda>x. (x^14) / (numer_cf7 (-x) * numer_cf7 x)"

lemma d_delta_lnexp_cf7_nonneg: "numer_cf7 x > 0 \<Longrightarrow> numer_cf7 (-x) > 0 \<Longrightarrow> diff_delta_lnexp_cf7 x \<ge> 0"
  unfolding diff_delta_lnexp_cf7_def
  by (auto simp: mult_less_0_iff intro: divide_nonneg_neg)

lemma d_delta_lnexp_cf7:
  assumes "numer_cf7 x > 0" "numer_cf7 (-x) > 0"
  shows "((\<lambda>x. ln (exp_cf7 x) - x) has_field_derivative diff_delta_lnexp_cf7 x) (at x)"
unfolding exp_cf7_def numer_cf7_def diff_delta_lnexp_cf7_def
apply (intro derivative_eq_intros | simp)+
using assms numer_cf7_pos [of x] numer_cf7_pos [of "-x"]
apply (auto simp: numer_cf7_def)
apply (auto simp: divide_simps add_nonneg_eq_0_iff)
apply algebra
done

subsection\<open>Proving monotonicity via a non-negative derivative\<close>

definition numer_cf7_deriv :: "real \<Rightarrow> real"
  where "numer_cf7_deriv \<equiv> \<lambda>x. 7*x^6 + 336*x^5 + 7560*x^4 + 100800*x^3 + 831600*x^2 + 3991680*x + 8648640"

lemma numer_cf7_deriv:
  shows "(numer_cf7 has_field_derivative numer_cf7_deriv x) (at x)"
  unfolding numer_cf7_def numer_cf7_deriv_def
  by (intro derivative_eq_intros | simp)+

lemma numer_cf7_deriv_pos: "numer_cf7_deriv x \<ge> 0"
  unfolding numer_cf7_deriv_def
  apply (rule order.strict_implies_order)  \<comment> \<open>FIXME should not be necessary\<close>
  by sturm

lemma numer_cf7_mono: "y \<le> x \<Longrightarrow> numer_cf7 y \<le> numer_cf7 x"
  by (auto intro: DERIV_nonneg_imp_nondecreasing numer_cf7_deriv numer_cf7_deriv_pos)

subsection\<open>Results\<close>

text\<open>Upper bound for non-negative x\<close>
lemma ln_exp_cf7_upper_bound_nonneg:
  assumes x0: "0 \<le> x" and xless: "numer_cf7 (-x) > 0"
    shows "x \<le> ln (exp_cf7 x)"
proof -
  have ncf7: "\<And>y. 0 \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> numer_cf7 (-y) > 0"
    by (metis neg_le_iff_le numer_cf7_mono order.strict_trans2 xless)
  show ?thesis
    apply (rule gen_upper_bound_increasing [OF x0 d_delta_lnexp_cf7 d_delta_lnexp_cf7_nonneg])
    apply (auto simp add: ncf7 assms numer_cf7_pos)
    apply (simp add: exp_cf7_def numer_cf7_def)
    done
qed

theorem exp_cf7_upper_bound_pos: "0 \<le> x \<Longrightarrow> numer_cf7 (-x) > 0 \<Longrightarrow> exp x \<le> exp_cf7 x"
  using ln_exp_cf7_upper_bound_nonneg [of x] exp_cf7_pos [of x] numer_cf7_pos [of x]
  by auto (metis exp_le_cancel_iff exp_ln_iff)

corollary "0 \<le> x \<Longrightarrow> x \<le> 9.943 \<Longrightarrow> exp x \<le> exp_cf7 x"
  by (metis neg_le_iff_le numer_cf7_pos exp_cf7_upper_bound_pos)

text\<open>Lower bound for negative x, provided @{term"exp_cf7 x > 0"}]\<close>
lemma ln_exp_cf7_lower_bound_neg:
  assumes x0: "x \<le> 0" and xgtr: "numer_cf7 x > 0"
    shows "ln (exp_cf7 x) \<le> x"
proof -
  have ncf7: "\<And>y. x \<le> y \<Longrightarrow> y \<le> 0 \<Longrightarrow> numer_cf7 y > 0"
    by (metis dual_order.strict_trans1 numer_cf7_mono xgtr)
  show ?thesis
    apply (rule gen_lower_bound_decreasing [OF x0 d_delta_lnexp_cf7 d_delta_lnexp_cf7_nonneg])
    apply (auto simp add: ncf7 assms numer_cf7_pos)
    apply (simp add: exp_cf7_def numer_cf7_def)
    done
qed

theorem exp_cf7_lower_bound_pos:
  assumes "x \<le> 0" shows "exp_cf7 x \<le> exp x"
proof (cases "numer_cf7 x > 0")
  case True
  then have "exp_cf7 x > 0"
    using assms numer_cf7_pos [of "-x"]
    by (auto simp: exp_cf7_pos)
  then show ?thesis
  using ln_exp_cf7_lower_bound_neg [of x] assms True
    by auto (metis exp_le_cancel_iff exp_ln_iff)
next
  case False
  then have "exp_cf7 x \<le> 0"
    using assms numer_cf7_pos [of "-x"]
    unfolding exp_cf7_def
    by (simp add: divide_nonpos_pos)
  then show ?thesis
    by (metis exp_ge_zero order.trans)
qed

end

