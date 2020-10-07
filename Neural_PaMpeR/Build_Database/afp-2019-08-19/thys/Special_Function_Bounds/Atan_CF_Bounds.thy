chapter \<open>Arctan Upper and Lower Bounds\<close>

theory Atan_CF_Bounds
imports Bounds_Lemmas  
        "HOL-Library.Sum_of_Squares"

begin

text\<open>Covers all bounds used in arctan-upper.ax, arctan-lower.ax and arctan-extended.ax,
excepting only arctan-extended2.ax, which is used in two atan-error-analysis problems.\<close>

section \<open>Upper Bound 1\<close>

definition arctan_upper_11 :: "real \<Rightarrow> real"
  where "arctan_upper_11 \<equiv> \<lambda>x. -(pi/2) - 1/x"

definition diff_delta_arctan_upper_11 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_11 \<equiv> \<lambda>x. 1 / (x^2 * (1 + x^2))"

lemma d_delta_arctan_upper_11: "x \<noteq> 0 \<Longrightarrow>
    ((\<lambda>x. arctan_upper_11 x - arctan x) has_field_derivative diff_delta_arctan_upper_11 x) (at x)"
unfolding arctan_upper_11_def diff_delta_arctan_upper_11_def
apply (intro derivative_eq_intros | simp)+
apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
done

lemma d_delta_arctan_upper_11_pos: "x \<noteq> 0 \<Longrightarrow> diff_delta_arctan_upper_11 x > 0"
unfolding diff_delta_arctan_upper_11_def
by (simp add: divide_simps zero_less_mult_iff add_pos_pos)

text\<open>Different proof needed here: they coincide not at zero, but at (-) infinity!\<close>

lemma arctan_upper_11:
  assumes "x < 0"
    shows "arctan(x) < arctan_upper_11 x"
proof -
  have "((\<lambda>x. arctan_upper_11 x - arctan x) \<longlongrightarrow> - (pi / 2) - 0 - (- (pi / 2))) at_bot"
    unfolding arctan_upper_11_def
    apply (intro tendsto_intros tendsto_arctan_at_bot, auto simp: ext [OF divide_inverse])
    apply (metis tendsto_inverse_0 at_bot_le_at_infinity tendsto_mono)
    done
  then have *: "((\<lambda>x. arctan_upper_11 x - arctan x) \<longlongrightarrow> 0) at_bot"
    by simp
  have "0 < arctan_upper_11 x - arctan x"
    apply (rule DERIV_pos_imp_increasing_at_bot [OF _ *])
    apply (metis assms d_delta_arctan_upper_11 d_delta_arctan_upper_11_pos not_le)
    done
  then show ?thesis
    by auto
qed

definition arctan_upper_12 :: "real \<Rightarrow> real"
  where "arctan_upper_12 \<equiv> \<lambda>x. 3*x / (x^2 + 3)"

definition diff_delta_arctan_upper_12 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_12 \<equiv> \<lambda>x. -4*x^4 / ((x^2+3)^2 * (1+x^2))"

lemma d_delta_arctan_upper_12:
     "((\<lambda>x. arctan_upper_12 x - arctan x) has_field_derivative diff_delta_arctan_upper_12 x) (at x)"
  unfolding arctan_upper_12_def diff_delta_arctan_upper_12_def
  apply (intro derivative_eq_intros,  simp_all)
  apply (auto simp: divide_simps add_nonneg_eq_0_iff, algebra)
  done

text\<open>Strict inequalities also possible\<close>
lemma arctan_upper_12:
  assumes "x \<le> 0" shows "arctan(x) \<le> arctan_upper_12 x"
apply (rule gen_upper_bound_decreasing [OF assms d_delta_arctan_upper_12])
apply (auto simp: diff_delta_arctan_upper_12_def arctan_upper_12_def)
done

definition arctan_upper_13 :: "real \<Rightarrow> real"
  where "arctan_upper_13 \<equiv> \<lambda>x. x"

definition diff_delta_arctan_upper_13 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_13 \<equiv> \<lambda>x. x^2 / (1 + x^2)"

lemma d_delta_arctan_upper_13:
    "((\<lambda>x. arctan_upper_13 x - arctan x) has_field_derivative diff_delta_arctan_upper_13 x) (at x)"
unfolding arctan_upper_13_def diff_delta_arctan_upper_13_def
apply (intro derivative_eq_intros, simp_all)
apply (simp add: divide_simps add_nonneg_eq_0_iff)
done

lemma arctan_upper_13:
  assumes "x \<ge> 0" shows "arctan(x) \<le> arctan_upper_13 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_arctan_upper_13])
apply (auto simp: diff_delta_arctan_upper_13_def arctan_upper_13_def)
done

definition arctan_upper_14 :: "real \<Rightarrow> real"
  where "arctan_upper_14 \<equiv> \<lambda>x. pi/2 - 3*x / (1 + 3*x^2)"

definition diff_delta_arctan_upper_14 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_14 \<equiv> \<lambda>x. -4 / ((1 + 3*x^2)^2 * (1+x^2))"

lemma d_delta_arctan_upper_14:
  "((\<lambda>x. arctan_upper_14 x - arctan x) has_field_derivative diff_delta_arctan_upper_14 x) (at x)"
unfolding arctan_upper_14_def diff_delta_arctan_upper_14_def
apply (intro derivative_eq_intros | simp add: add_nonneg_eq_0_iff)+
apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
done

lemma d_delta_arctan_upper_14_neg: "diff_delta_arctan_upper_14 x < 0"
unfolding diff_delta_arctan_upper_14_def
apply (auto simp: divide_simps add_nonneg_eq_0_iff zero_less_mult_iff)
using power2_less_0 [of x]
apply arith
done

lemma lim14: "((\<lambda>x::real. 3 * x / (1 + 3 * x\<^sup>2)) \<longlongrightarrow> 0) at_infinity"
  apply (rule tendsto_0_le [where f = inverse and K=1])
  apply (metis tendsto_inverse_0)
  apply (simp add: eventually_at_infinity)
  apply (rule_tac x=1 in exI)
  apply (simp add: power_eq_if abs_if divide_simps add_sign_intros)
  done

text\<open>Different proof needed here: they coincide not at zero, but at (+) infinity!\<close>

lemma arctan_upper_14:
  assumes "x > 0"
    shows "arctan(x) < arctan_upper_14 x"
proof -
  have "((\<lambda>x. arctan_upper_14 x - arctan x) \<longlongrightarrow> pi / 2 - 0 - pi / 2) at_top"
    unfolding arctan_upper_14_def
    apply (intro tendsto_intros tendsto_arctan_at_top)
    apply (auto simp: tendsto_mono [OF at_top_le_at_infinity lim14])
    done
  then have *: "((\<lambda>x. arctan_upper_14 x - arctan x) \<longlongrightarrow> 0) at_top"
    by simp
  have "0 < arctan_upper_14 x - arctan x"
    apply (rule DERIV_neg_imp_decreasing_at_top [OF _ *])
    apply (metis d_delta_arctan_upper_14 d_delta_arctan_upper_14_neg)
    done
  then show ?thesis
    by auto
qed

section \<open>Lower Bound 1\<close>

definition arctan_lower_11 :: "real \<Rightarrow> real"
  where "arctan_lower_11 \<equiv> \<lambda>x. -(pi/2) - 3*x / (1 + 3*x^2)"

lemma arctan_lower_11:
  assumes "x < 0"
    shows "arctan(x) > arctan_lower_11 x"
    using arctan_upper_14 [of "-x"] assms
    by (auto simp: arctan_upper_14_def arctan_lower_11_def arctan_minus)

abbreviation "arctan_lower_12 \<equiv> arctan_upper_13"

lemma arctan_lower_12:
  assumes "x \<le> 0"
    shows "arctan(x) \<ge> arctan_lower_12 x"
    using arctan_upper_13 [of "-x"] assms
    by (auto simp: arctan_upper_13_def arctan_minus)

abbreviation "arctan_lower_13 \<equiv> arctan_upper_12"

lemma arctan_lower_13:
  assumes "x \<ge> 0"
    shows "arctan(x) \<ge> arctan_lower_13 x"
    using arctan_upper_12 [of "-x"] assms
    by (auto simp: arctan_upper_12_def arctan_minus)

definition arctan_lower_14 :: "real \<Rightarrow> real"
  where "arctan_lower_14 \<equiv> \<lambda>x. pi/2 - 1/x"

lemma arctan_lower_14:
  assumes "x > 0"
    shows "arctan(x) > arctan_lower_14 x"
    using arctan_upper_11 [of "-x"] assms
    by (auto simp: arctan_upper_11_def arctan_lower_14_def arctan_minus)

section \<open>Upper Bound 3\<close>

definition arctan_upper_31 :: "real \<Rightarrow> real"
  where "arctan_upper_31 \<equiv> \<lambda>x. -(pi/2) - (64 + 735*x^2 + 945*x^4) / (15*x*(15 + 70*x^2 + 63*x^4))"

definition diff_delta_arctan_upper_31 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_31 \<equiv> \<lambda>x. 64 / (x^2 * (15 + 70*x^2 + 63*x^4)^2 * (1 + x^2))"

lemma d_delta_arctan_upper_31:
  assumes "x \<noteq> 0"
    shows "((\<lambda>x. arctan_upper_31 x - arctan x) has_field_derivative diff_delta_arctan_upper_31 x) (at x)"
  unfolding arctan_upper_31_def diff_delta_arctan_upper_31_def
  using assms
  apply (intro derivative_eq_intros)
  apply (rule refl | simp add: add_nonneg_eq_0_iff)+
  apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
  done

lemma d_delta_arctan_upper_31_pos: "x \<noteq> 0 \<Longrightarrow> diff_delta_arctan_upper_31 x > 0"
unfolding diff_delta_arctan_upper_31_def
by (auto simp: divide_simps zero_less_mult_iff add_pos_pos add_nonneg_eq_0_iff)

lemma arctan_upper_31:
  assumes "x < 0"
    shows "arctan(x) < arctan_upper_31 x"
proof -
  have *: "\<And>x::real.  (15 + 70 * x\<^sup>2 + 63 * x ^ 4) > 0"
    by (sos "((R<1 + ((R<1 * ((R<7/8 * [19/7*x^2 + 1]^2) + ((R<4 * [x]^2) + (R<10/7 * [x^2]^2)))) + ((A<=0 * R<1) * (R<1/8 * [1]^2)))))")
  then have **: "\<And>x::real. \<not> (15 + 70 * x\<^sup>2 + 63 * x ^ 4) < 0"
    by (simp add: not_less)
  have "((\<lambda>x::real. (64 + 735 * x\<^sup>2 + 945 * x ^ 4) / (15 * x * (15 + 70 * x\<^sup>2 + 63 * x ^ 4))) \<longlongrightarrow> 0) at_bot"
    apply (rule tendsto_0_le [where f = inverse and K=2])
    apply (metis at_bot_le_at_infinity tendsto_inverse_0 tendsto_mono)
    apply (simp add: eventually_at_bot_linorder)
    apply (rule_tac x="-1" in exI)
    apply (auto simp: divide_simps abs_if zero_less_mult_iff **)
    done
  then have "((\<lambda>x. arctan_upper_31 x - arctan x) \<longlongrightarrow> - (pi / 2) - 0 - (- (pi / 2))) at_bot"
    unfolding arctan_upper_31_def
    apply (intro tendsto_intros tendsto_arctan_at_bot, auto)
    done
  then have *: "((\<lambda>x. arctan_upper_31 x - arctan x) \<longlongrightarrow> 0) at_bot"
    by simp
  have "0 < arctan_upper_31 x - arctan x"
    apply (rule DERIV_pos_imp_increasing_at_bot [OF _ *])
    apply (metis assms d_delta_arctan_upper_31 d_delta_arctan_upper_31_pos not_le)
    done
  then show ?thesis
    by auto
qed

definition arctan_upper_32 :: "real \<Rightarrow> real"
  where "arctan_upper_32 \<equiv> \<lambda>x. 7*(33*x^4 + 170*x^2 + 165)*x / (5*(5*x^6 + 105*x^4 + 315*x^2 + 231))"

definition diff_delta_arctan_upper_32 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_32 \<equiv> \<lambda>x. -256*x^12 / ((5*x^6+105*x^4+315*x^2+231)^2*(1+x^2))"

lemma d_delta_arctan_upper_32:
    "((\<lambda>x. arctan_upper_32 x - arctan x) has_field_derivative diff_delta_arctan_upper_32 x) (at x)"
    unfolding arctan_upper_32_def diff_delta_arctan_upper_32_def
    apply (intro derivative_eq_intros | simp)+
    apply simp_all
    apply (auto simp: add_nonneg_eq_0_iff divide_simps, algebra)
    done

lemma arctan_upper_32:
  assumes "x \<le> 0" shows "arctan(x) \<le> arctan_upper_32 x"
apply (rule gen_upper_bound_decreasing [OF assms d_delta_arctan_upper_32])
apply (auto simp: diff_delta_arctan_upper_32_def arctan_upper_32_def)
done

definition arctan_upper_33 :: "real \<Rightarrow> real"
  where "arctan_upper_33 \<equiv> \<lambda>x. (64*x^4+735*x^2+945)*x / (15*(15*x^4+70*x^2+63))"

definition diff_delta_arctan_upper_33 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_33 \<equiv> \<lambda>x. 64*x^10 / ((15*x^4+70*x^2+63)^2*(1+x^2))"

lemma d_delta_arctan_upper_33:
    "((\<lambda>x. arctan_upper_33 x - arctan x) has_field_derivative diff_delta_arctan_upper_33 x) (at x)"
unfolding arctan_upper_33_def diff_delta_arctan_upper_33_def
apply (intro derivative_eq_intros, simp_all)
apply (auto simp: add_nonneg_eq_0_iff divide_simps, algebra)
done

lemma arctan_upper_33:
  assumes "x \<ge> 0" shows "arctan(x) \<le> arctan_upper_33 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_arctan_upper_33])
apply (auto simp: diff_delta_arctan_upper_33_def arctan_upper_33_def)
done

definition arctan_upper_34 :: "real \<Rightarrow> real"
  where "arctan_upper_34 \<equiv>
         \<lambda>x. pi/2 - (33 + 170*x^2 + 165*x^4)*7*x / (5*(5 + 105*x^2 + 315*x^4 + 231*x^6))"

definition diff_delta_arctan_upper_34 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_34 \<equiv> \<lambda>x. -256 / ((5+105*x^2+315*x^4+231*x^6)^2*(1+x^2))"

lemma d_delta_arctan_upper_34:
  "((\<lambda>x. arctan_upper_34 x - arctan x) has_field_derivative diff_delta_arctan_upper_34 x) (at x)"
unfolding arctan_upper_34_def diff_delta_arctan_upper_34_def
apply (intro derivative_eq_intros | simp add: add_nonneg_eq_0_iff)+
apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
done

lemma d_delta_arctan_upper_34_pos: "diff_delta_arctan_upper_34 x < 0"
unfolding diff_delta_arctan_upper_34_def
apply (simp add: divide_simps add_nonneg_eq_0_iff zero_less_mult_iff)
using power2_less_0 [of x]
apply arith
done

lemma arctan_upper_34:
  assumes "x > 0"
    shows "arctan(x) < arctan_upper_34 x"
proof -
  have "((\<lambda>x. arctan_upper_34 x - arctan x) \<longlongrightarrow> pi / 2 - 0 - pi / 2) at_top"
    unfolding arctan_upper_34_def
    apply (intro tendsto_intros tendsto_arctan_at_top, auto)
    apply (rule tendsto_0_le [where f = inverse and K=1])
    apply (metis tendsto_inverse_0 at_top_le_at_infinity tendsto_mono)
    apply (simp add: eventually_at_top_linorder)
    apply (rule_tac x=1 in exI)
    apply (auto simp: divide_simps power_eq_if add_pos_pos algebra_simps)
    done
  then have *: "((\<lambda>x. arctan_upper_34 x - arctan x) \<longlongrightarrow> 0) at_top"
    by simp
  have "0 < arctan_upper_34 x - arctan x"
    apply (rule DERIV_neg_imp_decreasing_at_top [OF _ *])
    apply (metis d_delta_arctan_upper_34 d_delta_arctan_upper_34_pos)
    done
  then show ?thesis
    by auto
qed

section \<open>Lower Bound 3\<close>

definition arctan_lower_31 :: "real \<Rightarrow> real"
  where "arctan_lower_31 \<equiv> \<lambda>x. -(pi/2) - (33 + 170*x^2 + 165*x^4)*7*x / (5*(5 + 105*x^2 + 315*x^4 + 231*x^6))"

lemma arctan_lower_31:
  assumes "x < 0"
    shows "arctan(x) > arctan_lower_31 x"
    using arctan_upper_34 [of "-x"] assms
    by (auto simp: arctan_upper_34_def arctan_lower_31_def arctan_minus)

abbreviation "arctan_lower_32 \<equiv> arctan_upper_33"

lemma arctan_lower_32:
  assumes "x \<le> 0"
    shows "arctan(x) \<ge> arctan_lower_32 x"
    using arctan_upper_33 [of "-x"] assms
    by (auto simp: arctan_upper_33_def arctan_minus)

abbreviation "arctan_lower_33 \<equiv> arctan_upper_32"

lemma arctan_lower_33:
  assumes "x \<ge> 0"
    shows "arctan(x) \<ge> arctan_lower_33 x"
    using arctan_upper_32 [of "-x"] assms
    by (auto simp: arctan_upper_32_def arctan_minus)

definition arctan_lower_34 :: "real \<Rightarrow> real"
  where "arctan_lower_34 \<equiv> \<lambda>x. pi/2 - (64 + 735*x^2 + 945*x^4) / (15*x*(15 + 70*x^2 + 63*x^4))"

lemma arctan_lower_34:
  assumes "x > 0"
    shows "arctan(x) > arctan_lower_34 x"
    using arctan_upper_31 [of "-x"] assms
    by (auto simp: arctan_upper_31_def arctan_lower_34_def arctan_minus)

section \<open>Upper Bound 4\<close>

definition arctan_upper_41 :: "real \<Rightarrow> real"
  where "arctan_upper_41 \<equiv>
        \<lambda>x. -(pi/2) - (256 + 5943*x^2 + 19250*x^4 + 15015*x^6) /
               (35*x*(35 + 315*x^2 + 693*x^4 + 429*x^6))"

definition diff_delta_arctan_upper_41 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_41 \<equiv> \<lambda>x. 256 / (x^2*(35+315*x^2+693*x^4+429*x^6)^2*(1+x^2))"

lemma d_delta_arctan_upper_41:
  assumes "x \<noteq> 0"
    shows "((\<lambda>x. arctan_upper_41 x - arctan x) has_field_derivative diff_delta_arctan_upper_41 x) (at x)"
  unfolding arctan_upper_41_def diff_delta_arctan_upper_41_def
  using assms
  apply (intro derivative_eq_intros)
  apply (rule refl | simp add: add_nonneg_eq_0_iff)+
  apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
  done

lemma d_delta_arctan_upper_41_pos: "x \<noteq> 0 \<Longrightarrow> diff_delta_arctan_upper_41 x > 0"
unfolding diff_delta_arctan_upper_41_def
by (auto simp: zero_less_mult_iff add_pos_pos add_nonneg_eq_0_iff)

lemma arctan_upper_41:
  assumes "x < 0"
    shows "arctan(x) < arctan_upper_41 x"
proof -
  have *: "\<And>x::real. (35 + 315 * x\<^sup>2 + 693 * x ^ 4 + 429 * x ^ 6) > 0"
    by (sos "((R<1 + ((R<1 * ((R<13/8589934592 * [95/26*x^2 + 1]^2) + ((R<38654705675/4294967296 * [170080704731/154618822700*x^3 + x]^2) + ((R<14271/446676598784 * [x^2]^2) + (R<3631584276674589067439/2656331147370089676800 * [x^3]^2))))) + ((A<=0 * R<1) * (R<245426703/8589934592 * [1]^2)))))")
  then have **: "\<And>x::real. x < 0 \<Longrightarrow> \<not> (35 + 315 * x\<^sup>2 + 693 * x ^ 4 + 429 * x ^ 6) < 0"
    by (simp add: not_less)
  have "((\<lambda>x::real. (256 + 5943 * x\<^sup>2 + 19250 * x ^ 4 + 15015 * x ^ 6) /
           (35 * x * (35 + 315 * x\<^sup>2 + 693 * x ^ 4 + 429 * x ^ 6))) \<longlongrightarrow> 0) at_bot"
    apply (rule tendsto_0_le [where f = inverse and K=2])
    apply (metis at_bot_le_at_infinity tendsto_inverse_0 tendsto_mono)
    apply (simp add: eventually_at_bot_linorder)
    apply (rule_tac x="-1" in exI)
    apply (auto simp: ** abs_if divide_simps zero_less_mult_iff)
    done
  then have "((\<lambda>x. arctan_upper_41 x - arctan x) \<longlongrightarrow> - (pi / 2) - 0 - (- (pi / 2))) at_bot"
    unfolding arctan_upper_41_def
    apply (intro tendsto_intros tendsto_arctan_at_bot, auto)
    done
  then have *: "((\<lambda>x. arctan_upper_41 x - arctan x) \<longlongrightarrow> 0) at_bot"
    by simp
  have "0 < arctan_upper_41 x - arctan x"
    apply (rule DERIV_pos_imp_increasing_at_bot [OF _ *])
    apply (metis assms d_delta_arctan_upper_41 d_delta_arctan_upper_41_pos not_le)
    done
  then show ?thesis
    by auto
qed

definition arctan_upper_42 :: "real \<Rightarrow> real"
  where "arctan_upper_42 \<equiv>
          \<lambda>x. (15159*x^6+147455*x^4+345345*x^2+225225)*x / (35*(35*x^8+1260*x^6+6930*x^4+12012*x^2+6435))"

definition diff_delta_arctan_upper_42 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_42 \<equiv>
            \<lambda>x. -16384*x^16 / ((35*x^8+1260*x^6+6930*x^4+12012*x^2+6435)^2*(1+x^2))"

lemma d_delta_arctan_upper_42:
    "((\<lambda>x. arctan_upper_42 x - arctan x) has_field_derivative diff_delta_arctan_upper_42 x) (at x)"
    unfolding arctan_upper_42_def diff_delta_arctan_upper_42_def
    apply (intro derivative_eq_intros, simp_all)
    apply (auto simp: divide_simps add_nonneg_eq_0_iff, algebra)
    done

lemma arctan_upper_42:
  assumes "x \<le> 0" shows "arctan(x) \<le> arctan_upper_42 x"
apply (rule gen_upper_bound_decreasing [OF assms d_delta_arctan_upper_42])
apply (auto simp: diff_delta_arctan_upper_42_def arctan_upper_42_def)
done

definition arctan_upper_43 :: "real \<Rightarrow> real"
  where "arctan_upper_43 \<equiv>
          \<lambda>x. (256*x^6+5943*x^4+19250*x^2+15015)*x /
              (35 * (35*x^6+315*x^4+693*x^2+429))"

definition diff_delta_arctan_upper_43 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_43 \<equiv> \<lambda>x. 256*x^14 / ((35*x^6+315*x^4+693*x^2+429)^2*(1+x^2))"

lemma d_delta_arctan_upper_43:
    "((\<lambda>x. arctan_upper_43 x - arctan x) has_field_derivative diff_delta_arctan_upper_43 x) (at x)"
unfolding arctan_upper_43_def diff_delta_arctan_upper_43_def
apply (intro derivative_eq_intros, simp_all)
apply (auto simp: add_nonneg_eq_0_iff divide_simps, algebra)
done

lemma arctan_upper_43:
  assumes "x \<ge> 0" shows "arctan(x) \<le> arctan_upper_43 x"
apply (rule gen_upper_bound_increasing [OF assms d_delta_arctan_upper_43])
apply (auto simp: diff_delta_arctan_upper_43_def arctan_upper_43_def)
done

definition arctan_upper_44 :: "real \<Rightarrow> real"
  where "arctan_upper_44 \<equiv>
         \<lambda>x. pi/2 - (15159+147455*x^2+345345*x^4+225225*x^6)*x /
                 (35*(35+1260*x^2+6930*x^4+12012*x^6+6435*x^8))"

definition diff_delta_arctan_upper_44 :: "real \<Rightarrow> real"
  where "diff_delta_arctan_upper_44 \<equiv>
    \<lambda>x. -16384 / ((35+1260*x^2+6930*x^4+12012*x^6+6435*x^8)^2*(1+x^2))"

lemma d_delta_arctan_upper_44:
  "((\<lambda>x. arctan_upper_44 x - arctan x) has_field_derivative diff_delta_arctan_upper_44 x) (at x)"
unfolding arctan_upper_44_def diff_delta_arctan_upper_44_def
apply (intro derivative_eq_intros | simp add: add_nonneg_eq_0_iff)+
apply (simp add: divide_simps add_nonneg_eq_0_iff, algebra)
done

lemma d_delta_arctan_upper_44_pos: "diff_delta_arctan_upper_44 x < 0"
unfolding diff_delta_arctan_upper_44_def
apply (auto simp: divide_simps add_nonneg_eq_0_iff zero_less_mult_iff)
using power2_less_0 [of x]
apply arith
done

lemma arctan_upper_44:
  assumes "x > 0"
    shows "arctan(x) < arctan_upper_44 x"
proof -
  have "((\<lambda>x. arctan_upper_44 x - arctan x) \<longlongrightarrow> pi / 2 - 0 - pi / 2) at_top"
    unfolding arctan_upper_44_def
    apply (intro tendsto_intros tendsto_arctan_at_top, auto)
    apply (rule tendsto_0_le [where f = inverse and K=1])
    apply (metis tendsto_inverse_0 at_top_le_at_infinity tendsto_mono)
    apply (simp add: eventually_at_top_linorder)
    apply (rule_tac x=1 in exI)
    apply (auto simp: zero_le_mult_iff divide_simps not_le[symmetric] power_eq_if algebra_simps)
    done
  then have *: "((\<lambda>x. arctan_upper_44 x - arctan x) \<longlongrightarrow> 0) at_top"
    by simp
  have "0 < arctan_upper_44 x - arctan x"
    apply (rule DERIV_neg_imp_decreasing_at_top [OF _ *])
    apply (metis d_delta_arctan_upper_44 d_delta_arctan_upper_44_pos)
    done
  then show ?thesis
    by auto
qed

section \<open>Lower Bound 4\<close>

definition arctan_lower_41 :: "real \<Rightarrow> real"
  where "arctan_lower_41 \<equiv>
     \<lambda>x. -(pi/2) - (15159+147455*x^2+345345*x^4+225225*x^6)*x /
                   (35*(35+1260*x^2+6930*x^4+12012*x^6+6435*x^8))"

lemma arctan_lower_41:
  assumes "x < 0"
    shows "arctan(x) > arctan_lower_41 x"
    using arctan_upper_44 [of "-x"] assms
    by (auto simp: arctan_upper_44_def arctan_lower_41_def arctan_minus)

abbreviation "arctan_lower_42 \<equiv> arctan_upper_43"

lemma arctan_lower_42:
  assumes "x \<le> 0"
    shows "arctan(x) \<ge> arctan_lower_42 x"
    using arctan_upper_43 [of "-x"] assms
    by (auto simp: arctan_upper_43_def arctan_minus)

abbreviation "arctan_lower_43 \<equiv> arctan_upper_42"

lemma arctan_lower_43:
  assumes "x \<ge> 0"
    shows "arctan(x) \<ge> arctan_lower_43 x"
    using arctan_upper_42 [of "-x"] assms
    by (auto simp: arctan_upper_42_def arctan_minus)

definition arctan_lower_44 :: "real \<Rightarrow> real"
  where "arctan_lower_44 \<equiv>
    \<lambda>x. pi/2 - (256+5943*x^2+19250*x^4+15015*x^6) /
               (35*x*(35+315*x^2+693*x^4+429*x^6))"

lemma arctan_lower_44:
  assumes "x > 0"
    shows "arctan(x) > arctan_lower_44 x"
    using arctan_upper_41 [of "-x"] assms
    by (auto simp: arctan_upper_41_def arctan_lower_44_def arctan_minus)

end

