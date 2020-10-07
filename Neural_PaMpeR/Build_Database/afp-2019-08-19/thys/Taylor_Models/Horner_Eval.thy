section \<open>Horner Evaluation\<close>
theory Horner_Eval
  imports Interval
begin

text \<open>Function and lemmas for evaluating polynomials via the horner scheme.
   Because interval multiplication is not distributive, interval polynomials
   expressed as a sum of monomials are not equivalent to their respective horner form.
   The functions and lemmas in this theory can be used to express interval
   polynomials in horner form and prove facts about them.\<close>

fun horner_eval' where
  "horner_eval' f x v 0 = v"
| "horner_eval' f x v (Suc i) = horner_eval' f x (f i + x * v) i"

definition horner_eval
  where "horner_eval f x n = horner_eval' f x 0 n"

lemma horner_eval_cong:
  assumes "\<And>i. i < n \<Longrightarrow> f i = g i"
  assumes "x = y"
  assumes "n = m"
  shows "horner_eval f x n = horner_eval g y m"
proof-
  {
    fix v have "horner_eval' f x v n = horner_eval' g x v n"
      using assms(1) by (induction n arbitrary: v, simp_all)
  }
  thus ?thesis
    by (simp add: assms(2,3) horner_eval_def)
qed

lemma horner_eval_eq_setsum:
  fixes x::"'a::linordered_idom"
  shows "horner_eval f x n = (\<Sum>i<n. f i * x^i)"
proof-
  {
    fix v have "horner_eval' f x v n = (\<Sum>i<n. f i * x^i) + v * x^n"
      by (induction n arbitrary: v, simp_all add: distrib_left mult.commute)
  }
  thus ?thesis by (simp add: horner_eval_def)
qed

lemma horner_eval_Suc[simp]:
  fixes x::"'a::linordered_idom"
  shows "horner_eval f x (Suc n) = horner_eval f x n + (f n) * x^n"
  unfolding horner_eval_eq_setsum
  by simp

lemma horner_eval_Suc'[simp]:
  fixes x::"'a::{comm_monoid_add, times}"
  shows "horner_eval f x (Suc n) = f 0 + x * (horner_eval (\<lambda>i. f (Suc i)) x n)"
proof-
  {
    fix v have "horner_eval' f x v (Suc n) = f 0 + x * horner_eval' (\<lambda>i. f (Suc i)) x v n"
      by (induction n arbitrary: v, simp_all)
  }
  thus ?thesis by (simp add: horner_eval_def)
qed

lemma horner_eval_0[simp]:
  shows "horner_eval f x 0 = 0"
  by (simp add: horner_eval_def)

lemma horner_eval'_interval:
  fixes x::"'a::linordered_ring"
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> set_of (g i)"
  assumes "x \<in>\<^sub>i I" "v \<in>\<^sub>i V"
  shows "horner_eval' f x v n \<in>\<^sub>i horner_eval' g I V n"
  using assms
  by (induction n arbitrary: v V) (auto intro!: plus_in_intervalI times_in_intervalI)

lemma horner_eval_interval:
  fixes x::"'a::linordered_idom"
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> set_of (g i)"
  assumes "x \<in> set_of I"
  shows "horner_eval f x n \<in>\<^sub>i horner_eval g I n"
  unfolding horner_eval_def
  using assms
  by (rule horner_eval'_interval) (auto simp: set_of_eq)

end
