(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Proving Falling Factorial of a Sum with Vandermonde Identity\<close>

theory Falling_Factorial_Sum_Vandermonde
imports
  "Discrete_Summation.Factorials"
begin

text \<open>Note the potentially special copyright license condition of the following proof.\<close>

lemma ffact_add_nat:
  shows "ffact k (n + m) = (\<Sum>i\<le>k. (k choose i) * ffact i n * ffact (k - i) m)"
proof -
  have "ffact k (n + m) = fact k * ((n + m) choose k)"
    by (simp only: ffact_eq_fact_mult_binomial)
  also have "\<dots> = fact k * (\<Sum>i\<le>k. (n choose i) * (m choose (k - i)))"
    by (simp only: vandermonde)
  also have "\<dots> = (\<Sum>i\<le>k. fact k * (n choose i) * (m choose (k - i)))"
    by (simp add: sum_distrib_left field_simps)
  also have "\<dots> = (\<Sum>i\<le>k. (fact i * fact (k - i) * (k choose i)) * (n choose i) * (m choose (k - i)))"
    by (simp add: binomial_fact_lemma)
  also have "\<dots> = (\<Sum>i\<le>k. (k choose i) * (fact i * (n choose i)) * (fact (k - i) * (m choose (k - i))))"
    by (auto intro: sum.cong)
  also have "\<dots> = (\<Sum>i\<le>k. (k choose i) * ffact i n * ffact (k - i) m)"
    by (simp only: ffact_eq_fact_mult_binomial)
  finally show ?thesis .
qed

end