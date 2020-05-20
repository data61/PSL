(*  Title:      Serial_Rel.thy
    Author:     Sebastian Ullrich
*)

subsection "Serial Relations"

text \<open>A serial relation on a finite carrier induces a cycle.\<close>

theory Serial_Rel
imports Main
begin

definition "serial_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<exists>y \<in> A. (x,y) \<in> r)"
lemmas serial_onI = serial_on_def[THEN iffD2, rule_format]
lemmas serial_onE = serial_on_def[THEN iffD1, rule_format, THEN bexE]

fun iterated_serial_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "iterated_serial_on A r x 0 = x"
| "iterated_serial_on A r x (Suc n) = (SOME y. y \<in> A \<and> (iterated_serial_on A r x n,y) \<in> r)"

lemma iterated_serial_on_linear: "iterated_serial_on A r x (n+m) = iterated_serial_on A r (iterated_serial_on A r x n) m"
by (induction m) auto

lemma iterated_serial_on_in_A:
  assumes "serial_on A r" "a \<in> A"
  shows "iterated_serial_on A r a n \<in> A"
proof (induct n)
  case (Suc n)
  thus ?case
    using assms(1, 2) by (subst iterated_serial_on.simps(2)) (rule someI2_ex, auto elim: serial_onE)
qed (simp add:assms(2))

lemma iterated_serial_on_in_power:
  assumes "serial_on A r" "a \<in> A"
  shows "(a,iterated_serial_on A r a n) \<in> r ^^ n"
proof (induct n)
  case (Suc n)
  moreover obtain b where "(iterated_serial_on A r a n,b) \<in> r" "b \<in> A"
    using iterated_serial_on_in_A[OF assms, of n] assms(1) by - (rule serial_onE)
  ultimately show ?case by (subst iterated_serial_on.simps(2)) (rule someI2_ex, auto)
qed simp

lemma trancl_powerI: "a \<in> R ^^ n \<Longrightarrow> n > 0 \<Longrightarrow> a \<in> R\<^sup>+"
by (auto simp:trancl_power)

theorem serial_on_finite_cycle:
  assumes "serial_on A r" "A \<noteq> {}" "finite A"
  obtains a where "a \<in> A" "(a,a) \<in> r\<^sup>+"
proof-
  from assms(2) obtain a where a: "a \<in> A" by auto
  let ?f = "iterated_serial_on A r a"
  from a have "range ?f \<subseteq> A" using assms(1) by (auto intro: iterated_serial_on_in_A)
  with assms(3) have "\<exists>m\<in>UNIV.\<not> finite {n \<in> UNIV. ?f n = ?f m}"
    by - (rule pigeonhole_infinite, auto simp: finite_subset)
  then obtain n m where "?f m = ?f n" and[simp]: "n < m"
    by (metis (mono_tags, lifting) finite_nat_set_iff_bounded mem_Collect_eq not_less_eq)
  hence "?f n = iterated_serial_on A r (?f n) (m-n)"
    using iterated_serial_on_linear[of A r a n "m-n"] by (auto simp:less_imp_le_nat)
  also have "(?f n,iterated_serial_on A r (?f n) (m-n)) \<in> r ^^ (m - n)"
    by (rule iterated_serial_on_in_power[OF assms(1)], rule iterated_serial_on_in_A[OF assms(1) a])
  finally show ?thesis
    by - (rule that[of "?f n"], rule iterated_serial_on_in_A[OF assms(1) a], rule trancl_powerI, auto)
qed

end
