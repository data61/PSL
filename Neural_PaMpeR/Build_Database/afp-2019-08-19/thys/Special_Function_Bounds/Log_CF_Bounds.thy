chapter \<open>Log Upper and Lower Bounds\<close>

theory Log_CF_Bounds
imports Bounds_Lemmas

begin

theorem ln_upper_1: "0<x \<Longrightarrow> ln(x::real) \<le> x - 1"
by (rule ln_le_minus_one)

definition ln_lower_1 :: "real \<Rightarrow> real"
  where "ln_lower_1 \<equiv> \<lambda>x. 1 - (inverse x)"

corollary ln_lower_1: "0<x \<Longrightarrow> ln_lower_1 x \<le> ln x"
  unfolding ln_lower_1_def
  by (metis ln_inverse ln_le_minus_one positive_imp_inverse_positive minus_diff_eq minus_le_iff)

theorem ln_lower_1_eq: "0<x \<Longrightarrow> ln_lower_1 x = (x - 1)/x"
  by (auto simp: ln_lower_1_def divide_simps)

section \<open>Upper Bound 3\<close>

definition ln_upper_3 :: "real \<Rightarrow> real"
  where "ln_upper_3 \<equiv> \<lambda>x. (x + 5)*(x - 1) / (2*(2*x + 1))"

definition diff_delta_ln_upper_3 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_3 \<equiv> \<lambda>x. (x - 1)^3 / ((2*x + 1)^2 * x)"

lemma d_delta_ln_upper_3: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_3 x - ln x) has_field_derivative diff_delta_ln_upper_3 x) (at x)"
unfolding ln_upper_3_def diff_delta_ln_upper_3_def
apply (intro derivative_eq_intros | simp)+
apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
done

text\<open>Strict inequalities also possible\<close>
lemma ln_upper_3_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_3 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_3])
apply (auto simp: diff_delta_ln_upper_3_def ln_upper_3_def)
done

lemma ln_upper_3_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_3 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_3])
using assms
apply (auto simp: diff_delta_ln_upper_3_def divide_simps ln_upper_3_def)
done

theorem ln_upper_3: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_3 x"
by (metis le_less_linear less_eq_real_def ln_upper_3_neg ln_upper_3_pos)

definition ln_lower_3 :: "real \<Rightarrow> real"
  where "ln_lower_3 \<equiv> \<lambda>x. - ln_upper_3 (inverse x)"

corollary ln_lower_3: "0<x \<Longrightarrow> ln_lower_3 x \<le> ln x"
  unfolding ln_lower_3_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_3)

theorem ln_lower_3_eq: "0<x \<Longrightarrow> ln_lower_3 x = (1/2)*(1 + 5*x)*(x - 1) / (x*(2 + x))"
  unfolding ln_lower_3_def ln_upper_3_def
  by (simp add: divide_simps) algebra


section \<open>Upper Bound 5\<close>

definition ln_upper_5 :: "real \<Rightarrow> real"
  where "ln_upper_5 x \<equiv> (x^2 + 19*x + 10)*(x - 1) / (3*(3*x^2 + 6*x + 1))"

definition diff_delta_ln_upper_5 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_5 \<equiv> \<lambda>x. (x - 1)^5 / ((3*x^2 + 6*x + 1)^2*x)"

lemma d_delta_ln_upper_5: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_5 x - ln x) has_field_derivative diff_delta_ln_upper_5 x) (at x)"
  unfolding ln_upper_5_def diff_delta_ln_upper_5_def
  apply (intro derivative_eq_intros | simp add: add_nonneg_eq_0_iff)+
  apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
  done

lemma ln_upper_5_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_5 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_5])
apply (auto simp: diff_delta_ln_upper_5_def ln_upper_5_def)
done

lemma ln_upper_5_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_5 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_5])
using assms
apply (auto simp: diff_delta_ln_upper_5_def divide_simps ln_upper_5_def mult_less_0_iff)
done

theorem ln_upper_5: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_5 x"
by (metis le_less_linear less_eq_real_def ln_upper_5_neg ln_upper_5_pos)

definition ln_lower_5 :: "real \<Rightarrow> real"
  where "ln_lower_5 \<equiv> \<lambda>x. - ln_upper_5 (inverse x)"

corollary ln_lower_5: "0<x \<Longrightarrow> ln_lower_5 x \<le> ln x"
  unfolding ln_lower_5_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_5)

theorem ln_lower_5_eq: "0<x \<Longrightarrow>
    ln_lower_5 x = (1/3)*(10*x^2 + 19*x + 1)*(x - 1) / (x*(x^2 + 6*x + 3))"
  unfolding ln_lower_5_def ln_upper_5_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq divide_simps)
     algebra


section \<open>Upper Bound 7\<close>

definition ln_upper_7 :: "real \<Rightarrow> real"
  where "ln_upper_7 x \<equiv> (3*x^3 + 131*x^2 + 239*x + 47)*(x - 1) / (12*(4*x^3 + 18*x^2 + 12*x + 1))"

definition diff_delta_ln_upper_7 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_7 \<equiv> \<lambda>x. (x - 1)^7 / ((4*x^3 + 18*x^2 + 12*x + 1)^2 * x)"

lemma d_delta_ln_upper_7: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_7 x - ln x) has_field_derivative diff_delta_ln_upper_7 x) (at x)"
unfolding ln_upper_7_def diff_delta_ln_upper_7_def
apply (intro derivative_eq_intros | simp)+
apply auto
apply (auto simp: add_pos_pos dual_order.strict_implies_not_eq divide_simps, algebra)
done

lemma ln_upper_7_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_7 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_7])
apply (auto simp: diff_delta_ln_upper_7_def ln_upper_7_def)
done

lemma ln_upper_7_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_7 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_7])
using assms
apply (auto simp: diff_delta_ln_upper_7_def divide_simps ln_upper_7_def mult_less_0_iff)
done

theorem ln_upper_7: "0 < x \<Longrightarrow> ln(x) \<le> ln_upper_7 x"
  by (metis le_less_linear less_eq_real_def ln_upper_7_neg ln_upper_7_pos)

definition ln_lower_7 :: "real \<Rightarrow> real"
  where "ln_lower_7 \<equiv> \<lambda>x. - ln_upper_7 (inverse x)"

corollary ln_lower_7: "0 < x \<Longrightarrow> ln_lower_7 x \<le> ln x"
  unfolding ln_lower_7_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_7)

theorem ln_lower_7_eq: "0 < x \<Longrightarrow>
  ln_lower_7 x = (1/12)*(47*x^3 + 239*x^2 + 131*x + 3)*(x - 1) / (x*(x^3 + 12*x^2 + 18*x + 4))"
  unfolding ln_lower_7_def ln_upper_7_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq divide_simps)
     algebra


section \<open>Upper Bound 9\<close>

definition ln_upper_9 :: "real \<Rightarrow> real"
  where "ln_upper_9 x \<equiv> (6*x^4 + 481*x^3 + 1881*x^2 + 1281*x + 131)*(x - 1) /
                         (30 * (5*x^4 + 40*x^3 + 60*x^2 + 20*x + 1))"

definition diff_delta_ln_upper_9 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_9 \<equiv> \<lambda>x. (x - 1)^9 / (((5*x^4 + 40*x^3 + 60*x^2 + 20*x + 1)^2) * x)"

lemma d_delta_ln_upper_9: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_9 x - ln x) has_field_derivative diff_delta_ln_upper_9 x) (at x)"
unfolding ln_upper_9_def diff_delta_ln_upper_9_def
apply (intro derivative_eq_intros | simp)+
apply auto
apply (auto simp: add_pos_pos dual_order.strict_implies_not_eq divide_simps, algebra)
done

lemma ln_upper_9_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_9 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_9])
apply (auto simp: diff_delta_ln_upper_9_def ln_upper_9_def)
done

lemma ln_upper_9_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_9 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_9])
using assms
apply (auto simp: diff_delta_ln_upper_9_def divide_simps ln_upper_9_def mult_less_0_iff)
done

theorem ln_upper_9: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_9 x"
by (metis le_less_linear less_eq_real_def ln_upper_9_neg ln_upper_9_pos)


definition ln_lower_9 :: "real \<Rightarrow> real"
  where "ln_lower_9 \<equiv> \<lambda>x. - ln_upper_9 (inverse x)"

corollary ln_lower_9: "0 < x \<Longrightarrow> ln_lower_9 x \<le> ln x"
  unfolding ln_lower_9_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_9)

theorem ln_lower_9_eq: "0 < x \<Longrightarrow>
      ln_lower_9 x = (1/30)*(6 + 481*x + 1881*x^2 + 1281*x^3 + 131*x^4)*(x - 1) /
                     (x*(5 + 40*x + 60*x^2 + 20*x^3 + x^4))"
  unfolding ln_lower_9_def ln_upper_9_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq divide_simps)
     algebra


section \<open>Upper Bound 11\<close>

text\<open>Extended bounds start here\<close>

definition ln_upper_11 :: "real \<Rightarrow> real"
  where "ln_upper_11 x \<equiv>
           (5*x^5 + 647*x^4 + 4397*x^3 + 6397*x^2 + 2272*x + 142) * (x - 1) /
           (30*(6*x^5 + 75*x^4 + 200*x^3 + 150*x^2 + 30*x + 1))"

definition diff_delta_ln_upper_11 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_11 \<equiv> \<lambda>x. (x - 1)^11 / ((6*x^5 + 75*x^4 + 200*x^3 + 150*x^2 + 30*x + 1)^2 * x)"

lemma d_delta_ln_upper_11: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_11 x - ln x) has_field_derivative diff_delta_ln_upper_11 x) (at x)"
unfolding ln_upper_11_def diff_delta_ln_upper_11_def
apply (intro derivative_eq_intros | simp)+
apply auto
apply (auto simp: add_pos_pos dual_order.strict_implies_not_eq divide_simps, algebra)
done

lemma ln_upper_11_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_11 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_11])
apply (auto simp: diff_delta_ln_upper_11_def ln_upper_11_def)
done

lemma ln_upper_11_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_11 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_11])
using assms
apply (auto simp: diff_delta_ln_upper_11_def divide_simps ln_upper_11_def mult_less_0_iff)
done

theorem ln_upper_11: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_11 x"
by (metis le_less_linear less_eq_real_def ln_upper_11_neg ln_upper_11_pos)

definition ln_lower_11 :: "real \<Rightarrow> real"
  where "ln_lower_11 \<equiv> \<lambda>x. - ln_upper_11 (inverse x)"

corollary ln_lower_11: "0<x \<Longrightarrow> ln_lower_11 x \<le> ln x"
  unfolding ln_lower_11_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_11)

theorem ln_lower_11_eq: "0<x \<Longrightarrow>
    ln_lower_11 x = (1/30)*(142*x^5 + 2272*x^4 + 6397*x^3 + 4397*x^2 + 647*x + 5)*(x - 1) /
                    (x*(x^5 + 30*x^4 + 150*x^3 + 200*x^2 + 75*x + 6))"
  unfolding ln_lower_11_def ln_upper_11_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq divide_simps)
     algebra


section \<open>Upper Bound 13\<close>

definition ln_upper_13 :: "real \<Rightarrow> real"
  where "ln_upper_13 x \<equiv> (353 + 8389*x + 20149*x^4 + 50774*x^3 + 38524*x^2 + 1921*x^5 + 10*x^6) * (x - 1)
                          / (70*(1 + 42*x + 525*x^4 + 700*x^3 + 315*x^2 + 126*x^5 + 7*x^6))"

definition diff_delta_ln_upper_13 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_13 \<equiv> \<lambda>x. (x - 1)^13 /
                     ((1 + 42*x + 525*x^4 + 700*x^3 + 315*x^2 + 126*x^5 + 7*x^6)^2*x)"

lemma d_delta_ln_upper_13: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_13 x - ln x) has_field_derivative diff_delta_ln_upper_13 x) (at x)"
unfolding ln_upper_13_def diff_delta_ln_upper_13_def
apply (intro derivative_eq_intros | simp)+
apply auto
apply (auto simp: add_pos_pos dual_order.strict_implies_not_eq divide_simps, algebra)
done

lemma ln_upper_13_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_13 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_13])
apply (auto simp: diff_delta_ln_upper_13_def ln_upper_13_def)
done

lemma ln_upper_13_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_13 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_13])
using assms
apply (auto simp: diff_delta_ln_upper_13_def divide_simps ln_upper_13_def mult_less_0_iff)
done

theorem ln_upper_13: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_13 x"
  by (metis le_less_linear less_eq_real_def ln_upper_13_neg ln_upper_13_pos)

definition ln_lower_13 :: "real \<Rightarrow> real"
  where "ln_lower_13 \<equiv> \<lambda>x. - ln_upper_13 (inverse x)"

corollary ln_lower_13: "0<x \<Longrightarrow> ln_lower_13 x \<le> ln x"
  unfolding ln_lower_13_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_13)

theorem ln_lower_13_eq: "0<x \<Longrightarrow>
    ln_lower_13 x = (1/70)*(10 + 1921*x + 20149*x^2 + 50774*x^3 + 38524*x^4 + 8389*x^5 + 353*x^6)*(x - 1) /
                    (x*(7 + 126*x + 525*x^2 + 700*x^3 + 315*x^4 + 42*x^5 + x^6))"
  unfolding ln_lower_13_def ln_upper_13_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq divide_simps)
     algebra


section \<open>Upper Bound 15\<close>

definition ln_upper_15 :: "real \<Rightarrow> real"
  where "ln_upper_15 x \<equiv>
           (1487 + 49199*x + 547235*x^4 + 718735*x^3 + 334575*x^2 + 141123*x^5 + 35*x^7 + 9411*x^6)*(x - 1) /
           (280*(1 + 56*x + 2450*x^4 + 1960*x^3 + 588*x^2 + 1176*x^5 + 8*x^7 + 196*x^6))"

definition diff_delta_ln_upper_15 :: "real \<Rightarrow> real"
  where "diff_delta_ln_upper_15
         \<equiv> \<lambda>x. (x - 1)^15 / ((1+56*x+2450*x^4+1960*x^3+588*x^2+8*x^7+196*x^6+1176*x^5)^2 * x)"

lemma d_delta_ln_upper_15: "x > 0 \<Longrightarrow>
    ((\<lambda>x. ln_upper_15 x - ln x) has_field_derivative diff_delta_ln_upper_15 x) (at x)"
unfolding ln_upper_15_def diff_delta_ln_upper_15_def
apply (intro derivative_eq_intros | simp)+
apply auto
apply (auto simp: add_pos_pos dual_order.strict_implies_not_eq divide_simps, algebra)
done

lemma ln_upper_15_pos:
  assumes "1 \<le> x" shows "ln(x) \<le> ln_upper_15 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_ln_upper_15])
apply (auto simp: diff_delta_ln_upper_15_def ln_upper_15_def)
done

lemma ln_upper_15_neg:
  assumes "0 < x" and x1: "x \<le> 1" shows "ln(x) \<le> ln_upper_15 x"
apply (rule gen_upper_bound_decreasing [OF x1 d_delta_ln_upper_15])
using assms
apply (auto simp: diff_delta_ln_upper_15_def divide_simps ln_upper_15_def mult_less_0_iff)
done

theorem ln_upper_15: "0<x \<Longrightarrow> ln(x) \<le> ln_upper_15 x"
  by (metis le_less_linear less_eq_real_def ln_upper_15_neg ln_upper_15_pos)


definition ln_lower_15 :: "real \<Rightarrow> real"
  where "ln_lower_15 \<equiv> \<lambda>x. - ln_upper_15 (inverse x)"

corollary ln_lower_15: "0<x \<Longrightarrow> ln_lower_15 x \<le> ln x"
  unfolding ln_lower_15_def
  by (metis ln_inverse inverse_positive_iff_positive minus_le_iff ln_upper_15)

theorem ln_lower_15_eq: "0<x \<Longrightarrow>
    ln_lower_15 x = (1/280)*(35 + 9411*x + 141123*x^2 + 547235*x^3 + 718735*x^4 + 334575*x^5 + 49199*x^6 + 1487*x^7)*(x - 1) /
                    (x*(8 + 196*x + 1176*x^2 + 2450*x^3 + 1960*x^4 + 588*x^5 + 56*x^6 + x^7))"
  unfolding ln_lower_15_def ln_upper_15_def
  by (simp add: zero_less_mult_iff add_pos_pos dual_order.strict_implies_not_eq
              divide_simps) algebra

end
