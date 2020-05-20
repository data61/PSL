(*
  File:     Solovay_Strassen.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  The Solovay--Strassen primality test.
*)
section \<open>The Solovay--Strassen Test\<close>
theory Solovay_Strassen_Test
imports 
  Generalized_Primality_Test
  Euler_Witness
begin

definition solovay_strassen_witness :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "solovay_strassen_witness n a =
     (let x = Jacobi (int a) (int n) in x \<noteq> 0 \<and> [x = int a ^ ((n - 1) div 2)] (mod n))"

definition solovay_strassen :: "nat \<Rightarrow> bool pmf" where
  "solovay_strassen = primality_test solovay_strassen_witness"

lemma prime_imp_solovay_strassen_witness:
  assumes "prime p" "odd p" "a \<in> {2..<p}"
  shows   "solovay_strassen_witness p a"
proof -
  have eq: "Jacobi a p = Legendre a p"
    using prime_p_Jacobi_eq_Legendre assms by simp
  from \<open>prime p\<close> have "coprime p a"
    by (rule prime_imp_coprime) (use assms in auto)

  show ?thesis unfolding solovay_strassen_witness_def Let_def eq
  proof
    from \<open>coprime p a\<close> and \<open>prime p\<close> show "Legendre (int a) (int p) \<noteq> 0"
      by (auto simp: coprime_commute)
  next
    show "[Legendre (int a) (int p) = int a ^ ((p - 1) div 2)] (mod int p)"
      using assms by (intro euler_criterion) auto
  qed
qed
    
lemma card_solovay_strassen_liars_composite:
  fixes n :: nat
  assumes "\<not>prime n" "n > 2" "odd n"
  shows   "card {a \<in> {2..<n}. solovay_strassen_witness n a} < (n - 2) div 2"
    (is "card ?A < _")
proof -
  interpret euler_witness_context n
    using assms unfolding euler_witness_context_def by simp
  have "card H < (n - 1) div 2"
    by (intro card_euler_liars_cosets_limit(2) assms)
  also from assms have "H = insert 1 ?A"
    by (auto simp: solovay_strassen_witness_def Let_def
                   euler_witness_def H_def Jacobi_eq_0_iff_not_coprime)
  also have "card \<dots> = card ?A + 1"
    by (subst card.insert) auto
  finally show "card ?A < (n - 2) div 2"
    by linarith
qed

interpretation solovay_strassen: good_prob_primality_test solovay_strassen_witness n "1 / 2"
  rewrites "primality_test solovay_strassen_witness = solovay_strassen"
proof -
  show "good_prob_primality_test solovay_strassen_witness n (1 / 2)"
  proof
    fix n :: nat assume "\<not>prime n" "n > 2" "odd n"
    thus "real (card {a. 2 \<le> a \<and> a < n \<and> solovay_strassen_witness n a}) < (1 / 2) * real (n - 2)"
      using card_solovay_strassen_liars_composite[of n] by auto
  qed (use prime_imp_solovay_strassen_witness in auto)
qed (simp_all add: solovay_strassen_def)

end