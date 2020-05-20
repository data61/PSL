(*
  File:     Fermat_Test.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  The probabilistic prime test known as Fermat's test
*)
section \<open>Fermat's Test\<close>
theory Fermat_Test
imports 
  Fermat_Witness
  Generalized_Primality_Test
begin

definition "fermat_test = primality_test (\<lambda>n a. fermat_liar a n)"

text \<open>
  The Fermat test is a good probabilistic primality test on non-Carmichael numbers.
\<close>
locale fermat_test_not_Carmichael_number =
  fixes n :: nat
  assumes not_Carmichael_number: "\<not>Carmichael_number n \<or> n < 3"
begin

sublocale fermat_test: good_prob_primality_test "\<lambda>a n. fermat_liar n a" n "1 / 2"
  rewrites "primality_test (\<lambda> a n. fermat_liar n a) = fermat_test"
proof -
  show "good_prob_primality_test (\<lambda>a n. fermat_liar n a) n (1 / 2)"
    using not_Carmichael_number not_Carmichael_number_imp_card_fermat_witness_bound(3)[of n]
          prime_imp_fermat_liar[of n]
    by unfold_locales auto
qed (auto simp: fermat_test_def)

end

lemma not_coprime_imp_fermat_witness:
  fixes n :: nat
  assumes "n > 1" "\<not>coprime a n"
  shows   "fermat_witness a n"
  using assms lucas_coprime_lemma[of "n - 1" a n]
  by (auto simp: fermat_witness_def)

theorem fermat_test_prime:
  assumes "prime n"
  shows   "fermat_test n = return_pmf True"
proof -
  interpret fermat_test_not_Carmichael_number n
    using assms Carmichael_number_not_prime by unfold_locales auto
  from assms show ?thesis by (rule fermat_test.prime)
qed

theorem fermat_test_composite:
  assumes "\<not>prime n" "\<not>Carmichael_number n \<or> n < 3"
  shows   "pmf (fermat_test n) True < 1 / 2"
proof -
  interpret fermat_test_not_Carmichael_number n by unfold_locales fact+
  from assms(1) show ?thesis by (rule fermat_test.composite)
qed

text \<open>
  For a Carmichael number $n$, Fermat's test as defined above mistakenly returns `True'
  with probability $(\varphi(n)-1) / (n - 2)$. This probability is close to 1 if \<open>n\<close>
  has few and big prime factors; it is not quite as bad if it has many and/or small factors,
  but in that case, simple trial division can also detect compositeness.

  Moreover, Fermat's test only succeeds for a Carmichael number if it happens to guess a
  number that is not coprime to \<open>n\<close>. In that case, the fact that we have found
  a number between 2 and \<open>n\<close> that is not coprime to \<open>n\<close> alone is 
  proof that \<open>n\<close> is composite, and indeed we can even find a non-trivial factor
  by computing the GCD. This means that for Carmichael numbers, Fermat's test is essentially
  no better than the very crude method of attempting to guess numbers coprime to \<open>n\<close>.

  This means that, in general, Fermat's test is not very helpful for Carmichael numbers.
\<close>
theorem fermat_test_Carmichael_number:
  assumes "Carmichael_number n"
  shows   "fermat_test n = bernoulli_pmf (real (totient n - 1) / real (n - 2))"
proof (rule eq_bernoulli_pmfI)
  from assms have n: "n > 3" "odd n"
    using Carmichael_number_odd Carmichael_number_gt_3 by auto
  from n have "fermat_test n = pmf_of_set {2..<n} \<bind> (\<lambda>a. return_pmf (fermat_liar a n))"
    by (simp add: fermat_test_def primality_test_def)
  also have "\<dots> = pmf_of_set {2..<n} \<bind> (\<lambda>a. return_pmf (coprime a n))"
    using n assms lucas_coprime_lemma[of "n - 1" _ n]
    by (intro bind_pmf_cong refl) (auto simp: Carmichael_number_def fermat_liar_def)
  also have "pmf \<dots> True = (\<Sum>a=2..<n. indicat_real {True} (coprime a n)) / real (n - 2)"
    using n by (auto simp: pmf_bind_pmf_of_set)
  also have "(\<Sum>a=2..<n. indicat_real {True} (coprime a n)) =
               (\<Sum>a | a \<in> {2..<n} \<and> coprime a n. 1)"
    by (intro sum.mono_neutral_cong_right) auto
  also have "\<dots> = card {a\<in>{2..<n}. coprime a n}"
    by simp
  also have "{a\<in>{2..<n}. coprime a n} = totatives n - {1}"
    using n by (auto simp: totatives_def order.strict_iff_order[of _ n])
  also have "card \<dots> = totient n - 1"
    using n by (subst card_Diff_subset) (auto simp: totient_def)
  finally show "pmf (fermat_test n) True = real (totient n - 1) / real (n - 2)"
    using n by simp
qed

end
