(*
  File:     Generalized_Primality_Test.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  Generic probabilistic primality test
*)
section \<open>A Generic View on Probabilistic Prime Tests\<close>
theory Generalized_Primality_Test
imports 
  "HOL-Probability.Probability" 
  Algebraic_Auxiliaries
begin

definition primality_test :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool pmf" where
  "primality_test P n = 
    (if n < 3 \<or> even n then return_pmf (n = 2) else
      do {
        a \<leftarrow> pmf_of_set {2..< n};
        return_pmf (P n a)
      })"

(* TODO Move *)
lemma expectation_of_bool_is_pmf: "measure_pmf.expectation M of_bool = pmf M True"
  by (simp add: integral_measure_pmf_real[where A=UNIV] UNIV_bool)

lemma eq_bernoulli_pmfI:
  assumes "pmf p True = x"
  shows   "p = bernoulli_pmf x"
proof (intro pmf_eqI)
  fix b :: bool
  from assms have "x \<in> {0..1}" by (auto simp: pmf_le_1)
  thus "pmf p b = pmf (bernoulli_pmf x) b"
    using assms by (cases b) (auto simp: pmf_False_conv_True)
qed

text \<open>
  We require a probabilistic primality test to never classify a prime as composite.
  It may, however, mistakenly classify composites as primes.
\<close>
locale prob_primality_test =
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool" and n :: nat
  assumes P_works: "odd n \<Longrightarrow> 2 \<le> a \<Longrightarrow> a < n \<Longrightarrow> prime n \<Longrightarrow> P n a"
begin

lemma FalseD:
  assumes false: "False \<in> set_pmf (primality_test P n)"
  shows   "\<not> prime n"
proof -
  from false consider "n \<noteq> 2" "n < 3" | "n \<noteq> 2" "even n" | 
      a where "\<not> P n a" "odd n" "2 \<le> a" "a < n"
    by (auto simp: primality_test_def not_less split: if_splits)

  then show ?thesis proof cases
  case 1
  then show ?thesis 
    by (cases rule: linorder_neqE_nat) (use prime_ge_2_nat[of n] in auto)
  next
    case 2
    then show ?thesis using primes_dvd_imp_eq two_is_prime_nat by blast
  next
    case 3
    then show ?thesis using P_works by blast
  qed 
qed

theorem prime:
  assumes odd_prime: "prime n"
  shows   "primality_test P n = return_pmf True"
proof -
  have "set_pmf (primality_test P n) \<subseteq> {True, False}"
    by auto
  moreover from assms have "False \<notin> set_pmf (primality_test P n)"
    using FalseD by auto
  ultimately have "set_pmf (primality_test P n) \<subseteq> {True}"
    by auto
  thus ?thesis
    by (subst (asm) set_pmf_subset_singleton)
qed

end

text \<open>
  We call a primality test \<open>q\<close>-good for a fixed positive real number \<open>q\<close> if the probability
  that it mistakenly classifies a composite as a prime is less than \<open>q\<close>.
\<close>
locale good_prob_primality_test = prob_primality_test +
  fixes q :: real
  assumes q_pos: "q > 0"
  assumes composite_witness_bound:
            "\<not>prime n \<Longrightarrow> 2 < n \<Longrightarrow> odd n \<Longrightarrow>
               real (card {a . 2 \<le> a \<and> a < n \<and> P n a}) < q * real (n - 2)"
begin

lemma composite_aux:
  assumes "\<not>prime n"
  shows   "measure_pmf.expectation (primality_test P n) of_bool < q"
  unfolding primality_test_def using assms composite_witness_bound q_pos
  by (auto simp: pmf_expectation_bind[where A = "{2..< n}"] sum_of_bool_eq_card field_simps
           simp flip: sum_divide_distrib)

theorem composite:
  assumes "\<not>prime n"
  shows   "pmf (primality_test P n) True < q"
  using composite_aux[OF assms] by (simp add: expectation_of_bool_is_pmf)

end

end