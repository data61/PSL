chapter \<open>Square Root Upper and Lower Bounds\<close>

theory Sqrt_Bounds
imports Bounds_Lemmas
        "HOL-Library.Sum_of_Squares"

begin

text\<open>Covers all bounds used in sqrt-upper.ax, sqrt-lower.ax and sqrt-extended.ax.\<close>

section\<open>Upper bounds\<close>

primrec sqrtu :: "[real,nat] \<Rightarrow> real" where
  "sqrtu x 0 = (x+1)/2"
| "sqrtu x (Suc n) = (sqrtu x n + x/sqrtu x n) / 2"

lemma sqrtu_upper: "x \<le> sqrtu x n ^ 2"
proof (induction n)
  case 0 show ?case
    apply (simp add: power2_eq_square)
    apply (sos "(((A<0 * R<1) + (R<1 * (R<1 * [~1*x + 1]^2))))")
    done
next
  case (Suc n)
  have xy: "\<And>y. \<lbrakk>x \<le> y * y; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * (2 * (y * y)) \<le> x * x + y * (y * (y * y))"
    by (sos "(((((A<0 * A<1) * R<1) + ((A<0 * R<1) * (R<1 * [~1*y^2 + x]^2)))) &
                   ((((A<0 * A<1) * R<1) + ((A<0 * R<1) * (R<1 * [~1*y^2 + x]^2)))))")
  show ?case using Suc
    by (auto simp: power2_eq_square algebra_simps divide_simps xy)
qed

lemma sqrtu_numeral:
  "sqrtu x (numeral n) = (sqrtu x (pred_numeral n) + x/sqrtu x (pred_numeral n)) / 2"
  by (simp add: numeral_eq_Suc)

lemma sqrtu_gt_0: "x \<ge> 0 \<Longrightarrow> sqrtu x n > 0"
apply (induct n)
apply (auto simp: field_simps)
by (metis add_strict_increasing2 mult_zero_left not_real_square_gt_zero)

theorem gen_sqrt_upper: "0 \<le> x \<Longrightarrow> sqrt x \<le> sqrtu x n"
using real_sqrt_le_mono [OF sqrtu_upper [of x n]]
by auto (metis abs_of_nonneg dual_order.strict_iff_order sqrtu_gt_0)

lemma sqrt_upper_bound_0:
  assumes "x \<ge> 0" shows "sqrt x \<le> (x+1)/2" (is "_ \<le> ?rhs")
proof -
  have "sqrt x \<le> sqrtu x 0"
    by (metis assms gen_sqrt_upper)
  also have "... = ?rhs"
    by (simp add: divide_simps)
  finally show ?thesis .
qed

lemma sqrt_upper_bound_1:
  assumes "x \<ge> 0" shows "sqrt x \<le> (1/4)*(x^2+6*x+1) / (x+1)" (is "_ \<le> ?rhs")
proof -
  have "sqrt x \<le> sqrtu x 1"
    by (metis assms gen_sqrt_upper)
  also have "... = ?rhs"
    by (simp add: divide_simps) algebra
  finally show ?thesis .
qed

lemma sqrtu_2_eq:
   "sqrtu x 2 = (1/8)*(x^4 + 28*x^3 + 70*x^2 + 28*x + 1) / ((x + 1)*(x^2 + 6*x + 1))"
  by (simp add: sqrtu_numeral divide_simps) algebra

lemma sqrt_upper_bound_2:
  assumes "x \<ge> 0"
    shows "sqrt x \<le> (1/8)*(x^4 + 28*x^3 + 70*x^2 + 28*x + 1) / ((x + 1)*(x^2 + 6*x + 1))"
  by (metis assms gen_sqrt_upper sqrtu_2_eq)

lemma sqrtu_4_eq:
   "x \<ge> 0 \<Longrightarrow>
    sqrtu x 4 = (1/32)*(225792840*x^6+64512240*x^5+601080390*x^8+471435600*x^7+496*x+1+35960*x^2+906192*x^3+10518300*x^4+x^16+906192*x^13+10518300*x^12+496*x^15+35960*x^14+471435600*x^9+225792840*x^10+64512240*x^11)
             / ((x+1)*(x^2+6*x+1)*(x^4+28*x^3+70*x^2+28*x+1)*(1820*x^6+8008*x^5+x^8+120*x^7+120*x+1+1820*x^2+8008*x^3+12870*x^4))"
  by (simp add: sqrtu_numeral divide_simps add_nonneg_eq_0_iff) algebra

lemma sqrt_upper_bound_4:
  assumes "x \<ge> 0"
    shows "sqrt x \<le> (1/32)*(225792840*x^6+64512240*x^5+601080390*x^8+471435600*x^7+496*x+1+35960*x^2+906192*x^3+10518300*x^4+x^16+906192*x^13+10518300*x^12+496*x^15+35960*x^14+471435600*x^9+225792840*x^10+64512240*x^11)
             / ((x+1)*(x^2+6*x+1)*(x^4+28*x^3+70*x^2+28*x+1)*(1820*x^6+8008*x^5+x^8+120*x^7+120*x+1+1820*x^2+8008*x^3+12870*x^4))"
  by (metis assms gen_sqrt_upper sqrtu_4_eq)

lemma gen_sqrt_upper_scaled:
  assumes "0 \<le> x" "0 < u"
    shows "sqrt x \<le> sqrtu (x*u^2) n / u"
proof -
  have "sqrt x = sqrt x * sqrt (u^2) / u"
    using assms
    by simp
  also have "... = sqrt (x*u^2) / u"
    by (metis real_sqrt_mult)
  also have "... \<le> sqrtu (x*u^2) n / u"
    using assms
    by (simp add: divide_simps) (metis gen_sqrt_upper zero_le_mult_iff zero_le_power2)
  finally show ?thesis .
qed

lemma sqrt_upper_bound_2_small:
  assumes "0 \<le> x"
    shows "sqrt x \<le> (1/32)*(65536*x^4 + 114688*x^3 + 17920*x^2 + 448*x + 1) / ((16*x + 1)*(256*x^2 + 96*x + 1))"
apply (rule order_trans [OF gen_sqrt_upper_scaled [of x 4 2] eq_refl])
using assms
apply (auto simp: sqrtu_2_eq )
apply (simp add: divide_simps)
apply algebra
done

lemma sqrt_upper_bound_2_large:
  assumes "0 \<le> x"
    shows "sqrt x \<le> (1/32)*(65536 + 114688*x + 17920*x^2 + 448*x^3 + x^4) / ((x + 16)*(256 + 96*x + x^2))"
apply (rule order_trans [OF gen_sqrt_upper_scaled [of x "1/4" 2] eq_refl])
using assms
apply (auto simp: sqrtu_2_eq )
apply (simp add: divide_simps)
apply algebra
done

section\<open>Lower bounds\<close>

lemma sqrt_lower_bound_id:
  assumes "0 \<le> x" "x \<le> 1"
    shows "x \<le> sqrt x"
proof -
  have "x^2 \<le> x" using assms
    by (metis one_le_numeral power_decreasing power_one_right)
  then show ?thesis
    by (metis real_le_rsqrt)
qed

definition sqrtl :: "[real,nat] \<Rightarrow> real" where
  "sqrtl x n = x/sqrtu x n"

lemma sqrtl_lower: "0 \<le> x \<Longrightarrow> sqrtl x n ^ 2 \<le> x"
  unfolding sqrtl_def using sqrtu_upper [of x n]
  by (auto simp: power2_eq_square divide_simps mult_left_mono)

theorem gen_sqrt_lower:  "0 \<le> x \<Longrightarrow> sqrtl x n \<le> sqrt x"
using real_sqrt_le_mono [OF sqrtl_lower [of x n]]
by auto

lemma sqrt_lower_bound_0:
  assumes "x \<ge> 0" shows "2*x/(x+1) \<le> sqrt x" (is "?lhs \<le> _")
proof -
  have "?lhs = sqrtl x 0"
    by (simp add: sqrtl_def)
  also have "... \<le> sqrt x"
    by (metis assms gen_sqrt_lower)
  finally show ?thesis .
qed

lemma sqrt_lower_bound_1:
  assumes "x \<ge> 0" shows "4*x*(x+1) / (x^2+6*x+1) \<le> sqrt x" (is "?lhs \<le> _")
proof -
  have "?lhs = sqrtl x 1" using assms
    by (simp add: sqrtl_def power_eq_if algebra_simps divide_simps)
  also have "... \<le> sqrt x"
    by (metis assms gen_sqrt_lower)
  finally show ?thesis .
qed

lemma sqrtl_2_eq: "sqrtl x 2 =
    8*x*(x + 1)*(x^2 + 6*x + 1) / (x^4 + 28*x^3 + 70*x^2 + 28*x + 1)"
  using sqrtu_gt_0 [of x 2]
  by (simp add: sqrtl_def sqrtu_2_eq)

lemma sqrt_lower_bound_2:
  assumes "x \<ge> 0"
    shows "8*x*(x + 1)*(x^2 + 6*x + 1) / (x^4 + 28*x^3 + 70*x^2 + 28*x + 1) \<le> sqrt x"
  by (metis assms sqrtl_2_eq gen_sqrt_lower)

lemma sqrtl_4_eq: "x \<ge> 0 \<Longrightarrow>
  sqrtl x 4
    = (32*x*(x+1)*(x^2+6*x+1)*(x^4+28*x^3+70*x^2+28*x+1)*(1820*x^6+8008*x^5+x^8+120*x^7+120*x+1+1820*x^2+8008*x^3+12870*x^4))
    / (225792840*x^6+64512240*x^5+601080390*x^8+471435600*x^7+496*x+1+35960*x^2+906192*x^3+10518300*x^4+x^16+906192*x^13+10518300*x^12+496*x^15+35960*x^14+471435600*x^9+225792840*x^10+64512240*x^11)"
  using sqrtu_gt_0 [of x 4]
  by (simp add: sqrtl_def sqrtu_4_eq)

lemma sqrt_lower_bound_4:
  assumes "x \<ge> 0"
    shows "(32*x*(x+1)*(x^2+6*x+1)*(x^4+28*x^3+70*x^2+28*x+1)*(1820*x^6+8008*x^5+x^8+120*x^7+120*x+1+1820*x^2+8008*x^3+12870*x^4))
           / (225792840*x^6+64512240*x^5+601080390*x^8+471435600*x^7+496*x+1+35960*x^2+906192*x^3+10518300*x^4+x^16+906192*x^13+10518300*x^12+496*x^15+35960*x^14+471435600*x^9+225792840*x^10+64512240*x^11)
           \<le> sqrt x"
  by (metis assms sqrtl_4_eq gen_sqrt_lower)

lemma gen_sqrt_lower_scaled:
  assumes "0 \<le> x" "0 < u"
    shows "sqrtl (x*u^2) n / u \<le> sqrt x"
proof -
  have "sqrtl (x*u^2) n / u \<le> sqrt (x*u^2) / u"
    using assms
    by (simp add: divide_simps) (metis gen_sqrt_lower zero_le_mult_iff zero_le_power2)
  also have "... = sqrt x * sqrt (u^2) / u"
    by (metis real_sqrt_mult)
  also have "... = sqrt x"
    using assms
    by simp
  finally show ?thesis .
qed

lemma sqrt_lower_bound_2_small:
  assumes "0 \<le> x"
    shows "32*x*(16*x + 1)*(256*x^2 + 96*x + 1) / (65536*x^4 + 114688*x^3 + 17920*x^2 + 448*x + 1) \<le> sqrt x"
apply (rule order_trans [OF eq_refl gen_sqrt_lower_scaled [of x 4 2]])
using assms
apply (auto simp: sqrtl_2_eq )
apply (simp add: divide_simps)
apply algebra
done

lemma sqrt_lower_bound_2_large:
  assumes "0 \<le> x"
    shows "32*x*(x + 16)*(x^2 + 96*x + 256) / (x^4 + 448*x^3 + 17920*x^2 + 114688*x + 65536) \<le> sqrt x"
apply (rule order_trans [OF eq_refl gen_sqrt_lower_scaled [of x "1/4" 2]])
using assms
apply (auto simp: sqrtl_2_eq)
apply (simp add: divide_simps)
done

end

