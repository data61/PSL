theory Lemmas_log
imports Complex_Main
begin

lemma ld_sum_inequality:
  assumes "x > 0" "y > 0"
  shows   "log 2 x + log 2 y + 2 \<le> 2 * log 2 (x + y)"
proof -
  have 0: "0 \<le> (x-y)^2" using assms by(simp)
  have "2 powr (2 + log 2 x + log 2 y) = 4 * x * y" using assms
    by(simp add: powr_add)
  also have "4*x*y \<le> (x+y)^2" using 0 by(simp add: algebra_simps numeral_eq_Suc)
  also have "\<dots> = 2 powr (log 2 (x + y) * 2)" using assms
    by(simp add: powr_powr[symmetric] powr_numeral)
  finally show ?thesis by (simp add: mult_ac)
qed

lemma ld_ld_1_less:
  "\<lbrakk>x > 0; y > 0 \<rbrakk> \<Longrightarrow> 1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
using ld_sum_inequality[of x y] by linarith
(*
proof -
  have 1: "2*x*y < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  show ?thesis
    apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed
*)

lemma ld_le_2ld:
  assumes "x \<ge> 0" "y \<ge> 0" shows "log 2 (1+x+y) \<le> 1 + log 2 (1+x) + log 2 (1+y)"
proof -
  have 1: "1+x+y \<le> (x+1)*(y+1)" using assms
    by(simp add: algebra_simps)
  show ?thesis
    apply(rule powr_le_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add algebra_simps)
qed

lemma ld_ld_less2: assumes "x \<ge> 2" "y \<ge> 2"
  shows "1 + log 2 x + log 2 y \<le> 2 * log 2 (x + y - 1)"
proof-
  from assms have "2*x \<le> x*x" "2*y \<le> y*y" by simp_all
  hence 1: "2 * x * y \<le> (x + y - 1)^2"
    by(simp add: numeral_eq_Suc algebra_simps)
  show ?thesis
    apply(rule powr_le_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed

end
