section \<open>Auxiliary material\<close>
theory Lucas_Lehmer_Auxiliary
imports
  "HOL-Algebra.Ring"
  "Probabilistic_Prime_Tests.Jacobi_Symbol"
begin

(* TODO: Much of this belongs in the library *)

subsection \<open>Auxiliary  number-theoretic material\<close>

lemma congD: "[a = b] (mod n) \<Longrightarrow> a mod n = b mod n"
  by (auto simp: cong_def)

lemma eval_coprime:
  "(b :: 'a :: euclidean_semiring_gcd) \<noteq> 0 \<Longrightarrow> coprime a b \<longleftrightarrow> coprime b (a mod b)"
  by (simp add: coprime_commute)

lemma two_power_odd_mod_12:
  assumes "odd n" "n > 1"
  shows   "[2 ^ n = 8] (mod (12 :: nat))"
  using assms
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 3")
    case False
    with less.prems have "n > 3" by (auto elim!: oddE)
    hence "[2 ^ (n - 2 + 2) = (8 * 4 :: nat)] (mod 12)"
      unfolding power_add using less.prems by (intro cong_mult less) auto
    also have "n - 2 + 2 = n"
      using \<open>n > 3\<close> by simp
    finally show ?thesis by (simp add: cong_def)
  qed auto
qed

lemma Legendre_3_right:
  fixes p :: nat
  assumes p: "prime p" "p > 3"
  shows   "p mod 12 \<in> {1, 5, 7, 11}" and "Legendre p 3 = (if p mod 12 \<in> {1, 7} then 1 else -1)"
proof -
  have "coprime p 2" using p prime_nat_not_dvd[of p 2]
    by (intro prime_imp_coprime) (auto dest: dvd_imp_le)
  moreover have "coprime p 3" using p
    by (intro prime_imp_coprime) auto
  ultimately have "coprime p (2 * 2 * 3)"
    unfolding coprime_mult_right_iff by auto
  hence "coprime 12 p"
    by (simp add: coprime_commute)
  
  hence "p mod 12 \<in> {p\<in>{..11}. coprime 12 p}" by auto
  also have "{p\<in>{..11}. coprime 12 p} = {1::nat, 5, 7, 11}"
    unfolding atMost_nat_numeral pred_numeral_simps arith_simps
    by (auto simp del: coprime_imp_gcd_eq_1 simp: eval_coprime)
  finally show "p mod 12 \<in> {1, 5, 7, 11}" by auto
  hence "p mod 12 = 1 \<or> p mod 12 = 5 \<or> p mod 12 = 7 \<or> p mod 12 = 11"
    by auto
  thus "Legendre p 3 = (if p mod 12 \<in> {1, 7} then 1 else -1)"
  proof safe
    assume "p mod 12 = 1"
    have "Legendre (int p) 3 = Legendre (int p mod 3) 3"
      by (intro Legendre_mod [symmetric]) auto
    also from \<open>p mod 12 = 1\<close> have "p mod 12 mod 3 = 1" by simp
    hence "p mod 3 = 1" by (simp add: mod_mod_cancel)
    hence "int p mod 3 = 1" by presburger
    finally have "Legendre p 3 = 1" by simp
    thus ?thesis using \<open>p mod 12 = 1\<close> by simp
  next
    assume "p mod 12 = 5"
    have "Legendre (int p) 3 = Legendre (int p mod 3) 3"
      by (intro Legendre_mod [symmetric]) auto
    also from \<open>p mod 12 = 5\<close> have "p mod 12 mod 3 = 2" by simp
    hence "p mod 3 = 2" by (simp add: mod_mod_cancel)
    hence "int p mod 3 = 2" by presburger
    finally have "Legendre p 3 = -1" by (simp add: supplement2_Legendre)
    thus ?thesis using \<open>p mod 12 = 5\<close> by simp
  next
    assume "p mod 12 = 7"
    have "Legendre (int p) 3 = Legendre (int p mod 3) 3"
      by (intro Legendre_mod [symmetric]) auto
    also from \<open>p mod 12 = 7\<close> have "p mod 12 mod 3 = 1" by simp
    hence "p mod 3 = 1" by (simp add: mod_mod_cancel)
    hence "int p mod 3 = 1" by presburger
    finally have "Legendre p 3 = 1" by simp
    thus ?thesis using \<open>p mod 12 = 7\<close> by simp
  next
    assume "p mod 12 = 11"
    have "Legendre (int p) 3 = Legendre (int p mod 3) 3"
      by (intro Legendre_mod [symmetric]) auto
    also from \<open>p mod 12 = 11\<close> have "p mod 12 mod 3 = 2" by simp
    hence "p mod 3 = 2" by (simp add: mod_mod_cancel)
    hence "int p mod 3 = 2" by presburger
    finally have "Legendre p 3 = -1" by (simp add: supplement2_Legendre)
    thus ?thesis using \<open>p mod 12 = 11\<close> by simp
  qed
qed

lemma Legendre_3_left:
  fixes p :: nat
  assumes p: "prime p" "p > 3"
  shows   "Legendre 3 p = (if p mod 12 \<in> {1, 11} then 1 else -1)"
proof (cases "p mod 12 = 1 \<or> p mod 12 = 5")
  case True
  hence "p mod 12 mod 4 = 1" by auto
  hence "even ((p - Suc 0) div 2)"
    by (intro even_mod_4_div_2) (auto simp: mod_mod_cancel)
  with Quadratic_Reciprocity[of p 3] Legendre_3_right(2)[of p] assms True show ?thesis
    by auto
next
  case False
  with Legendre_3_right(1)[OF assms] have *: "p mod 12 = 7 \<or> p mod 12 = 11" by auto
  hence "p mod 12 mod 4 = 3" by auto
  hence "odd ((p - Suc 0) div 2)"
    by (intro odd_mod_4_div_2) (auto simp: mod_mod_cancel)
  with Quadratic_Reciprocity[of p 3] Legendre_3_right(2)[of p] assms * show ?thesis
    by fastforce
qed

lemma supplement2_Legendre':
  assumes "prime p" "p \<noteq> 2"
  shows "Legendre 2 p = (if p mod 8 = 1 \<or> p mod 8 = 7 then 1 else -1)"
proof -
  from assms have "p > 2"
    using prime_gt_1_int[of p] by auto
  moreover from this and assms have "odd p"
    by (auto simp: prime_odd_int)
  ultimately show ?thesis
    using supplement2_Jacobi'[of p] assms prime_odd_int[of p]
    by (simp add: prime_p_Jacobi_eq_Legendre)
qed  

lemma little_Fermat_nat:
  fixes a :: nat
  assumes "prime p" "\<not>p dvd a"
  shows   "[a ^ p = a] (mod p)"
proof -
  have "p = Suc (p - 1)"
    using prime_gt_0_nat[OF assms(1)] by simp
  also have "p - 1 = totient p"
    using assms by (simp add: totient_prime)
  also have "a ^ (Suc \<dots>) = a * a ^ totient p"
    by simp
  also have "[\<dots> = a * 1] (mod p)"
    using prime_imp_coprime[of p a] assms
    by (intro cong_mult cong_refl euler_theorem) (auto simp: coprime_commute)
  finally show ?thesis by simp
qed

lemma little_Fermat_int:
  fixes a :: int and p :: nat
  assumes "prime p" "\<not>p dvd a"
  shows   "[a ^ p = a] (mod p)"
proof -
  have "p > 1" using prime_gt_1_nat assms by simp
  have "\<not>int p dvd a mod int p"
    using assms by (simp add: dvd_mod_iff)
  also from \<open>p > 1\<close> have "a mod int p = int (nat (a mod int p))"
    by simp
  finally have not_dvd: "\<not>p dvd nat (a mod int p)"
    by (subst (asm) int_dvd_int_iff)

  have "[a ^ p = (a mod p) ^ p] (mod p)"
    by (intro cong_pow) (auto simp: cong_def)
  also have "(a mod p) ^ p = (int (nat (a mod p))) ^ p"
    using \<open>p > 1\<close> by (subst of_nat_nat) auto
  also have "\<dots> = int (nat (a mod p) ^ p)"
    by simp
  also have "[\<dots> = int (nat (a mod p))] (mod p)"
    by (subst cong_int_iff, rule little_Fermat_nat) (use assms not_dvd in auto)
  also have "int (nat (a mod p)) = a mod p"
    using \<open>p > 1\<close> by simp
  also have "[a mod p = a] (mod p)"
    by (auto simp: cong_def)
  finally show ?thesis .
qed

lemma prime_dvd_choose:
  assumes "0 < k" "k < p" "prime p" 
  shows "p dvd (p choose k)"
proof -
  have "k \<le> p" using \<open>k < p\<close> by auto 

  have "p dvd fact p" using assms by (simp add: prime_dvd_fact_iff)   
  
  moreover have "\<not> p dvd fact k * fact (p - k)"
    unfolding prime_dvd_mult_iff[OF assms(3)] prime_dvd_fact_iff[OF assms(3)] 
    using assms by simp
  
  ultimately show ?thesis
    unfolding binomial_fact_lemma[OF \<open>k \<le> p\<close>, symmetric]
    using assms prime_dvd_multD by blast
qed

lemma prime_natD:
  assumes "prime (p :: nat)" "a dvd p"
  shows   "a = 1 \<or> a = p"
  using assms by (auto simp: prime_nat_iff)
  
  lemma not_prime_imp_ex_prod_nat:
  assumes "m > 1" "\<not> prime (m::nat)"
  shows   "\<exists>n k. m = n * k \<and> 1 < n \<and> n < m \<and> 1 < k \<and> k < m"
proof -
  from assms have "\<not>Factorial_Ring.irreducible m"
    by (simp flip: prime_elem_iff_irreducible)
  with assms obtain n k where nk: "m = n * k" "n \<noteq> 1" "k \<noteq> 1"
    by (auto simp: Factorial_Ring.irreducible_def)
  moreover from this assms have "n > 0" "k > 0"
    by auto
  with nk have "n > 1" "k > 1" by auto
  moreover {
    from assms nk have "n dvd m" "k dvd m" by auto
    with assms have "n \<le> m" "k \<le> m"
      by (auto intro!: dvd_imp_le)
    moreover from nk \<open>n > 1\<close> \<open>k > 1\<close> have "n \<noteq> m" "k \<noteq> m"
      by auto
    ultimately have "n < m" "k < m" by auto
  }
  ultimately show ?thesis by blast
qed


subsection \<open>Auxiliary algebraic material\<close>

lemma (in group) ord_eqI_prime_factors:
  assumes "\<And>p. p \<in> prime_factors n \<Longrightarrow> x [^] (n div p) \<noteq> \<one>" and "x [^] n = \<one>"
  assumes "x \<in> carrier G" "n > 0"
  shows   "group.ord G x = n"
proof -
  have "group.ord G x dvd n"
    using assms by (subst pow_eq_id [symmetric]) auto
  then obtain k where k: "n = group.ord G x * k"
    by auto
  have "k = 1"
  proof (rule ccontr)
    assume "k \<noteq> 1"
    then obtain p where p: "prime p" "p dvd k"
      using prime_factor_nat by blast
    have "x [^] (group.ord G x * (k div p)) = \<one>"
      by (subst pow_eq_id) (use assms in auto)
    also have "group.ord G x * (k div p) = n div p"
      using p by (auto simp: k)
    finally have "x [^] (n div p) = \<one>" .
    moreover have "x [^] (n div p) \<noteq> \<one>"
      using p k assms by (intro assms) (auto simp: in_prime_factors_iff)
    ultimately show False by contradiction
  qed
  with k show ?thesis by simp
qed

lemma (in monoid) pow_nat_eq_1_imp_unit:
  fixes n :: nat
  assumes "x [^] n = \<one>" and "n > 0" and [simp]: "x \<in> carrier G"
  shows   "x \<in> Units G"
proof -
  from \<open>n > 0\<close> have "x [^] (1 :: nat) \<otimes> x [^] (n - 1) = x [^] n"
    by (subst nat_pow_mult) auto
  with assms have "x \<otimes> x [^] (n - 1) = \<one>"
    by simp
  moreover from \<open>n > 0\<close> have "x [^] (n - 1) \<otimes> x [^] (1 :: nat) = x [^] n"
    by (subst nat_pow_mult) auto
  with assms have "x [^] (n - 1) \<otimes> x = \<one>"
    by simp
  ultimately show ?thesis by (auto simp: Units_def)
qed

lemma (in cring) finsum_reindex_bij_betw:
  assumes "bij_betw h S T" "g \<in> T \<rightarrow> carrier R"
  shows   "finsum R (\<lambda>x. g (h x)) S = finsum R g T"
  using assms by (auto simp: bij_betw_def finsum_reindex)

lemma (in cring) finsum_reindex_bij_witness:
  assumes witness:
    "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
    "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
    "\<And>b. b \<in> S \<Longrightarrow> g b \<in> carrier R"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows "finsum R g S = finsum R h T"
proof -
  have bij: "bij_betw j S T"
    using bij_betw_byWitness[where A=S and f=j and f'=i and A'=T] witness by auto
  hence T_eq: "T = j ` S" by (auto simp: bij_betw_def)
  from assms have "h \<in> T \<rightarrow> carrier R"
    by (subst T_eq) auto
  moreover have "finsum R g S = finsum R (\<lambda>x. h (j x)) S"
    using assms by (intro finsum_cong) (auto simp: eq)
  ultimately show ?thesis using assms(5)
    using finsum_reindex_bij_betw[OF bij, of h] by simp
qed

lemma (in cring) binomial:
  fixes n :: nat
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R"
  shows   "(x \<oplus> y) [^] n = (\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (n - i)))"
proof (induction n)
  case (Suc n)
  have binomial_Suc: "Suc n choose i = (n choose (i - 1)) + (n choose i)" if "i \<in> {1..n}" for i
    using that by (cases i) auto
  have Suc_diff: "Suc n - i = Suc (n - i)" if "i \<le> n" for i
    using that by linarith
  have "(x \<oplus> y) [^] Suc n =
          (\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (n - i))) \<otimes> x \<oplus>
          (\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (n - i))) \<otimes> y"
    by (simp add: semiring_simprules Suc)
  also have "(\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (n - i))) \<otimes> x =
             (\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] Suc i \<otimes> y [^] (n - i)))"
    by (subst finsum_ldistr)
       (auto simp: cring_simprules Suc add_pow_rdistr intro!: finsum_cong)
  also have "\<dots> = (\<Oplus>i\<in>{1..Suc n}. add_pow R (n choose (i - 1)) (x [^] i \<otimes> y [^] (Suc n - i)))"
    by (intro finsum_reindex_bij_witness[of _ "\<lambda>i. i - 1" Suc]) auto
  also have "{1..Suc n} = insert (Suc n) {1..n}" by auto
  also have "(\<Oplus>i\<in>\<dots>. add_pow R (n choose (i - 1)) (x [^] i \<otimes> y [^] (Suc n - i))) =
             x [^] Suc n \<oplus> (\<Oplus>i\<in>{1..n}. add_pow R (n choose (i - 1)) (x [^] i \<otimes> y [^] (Suc n - i)))"
    (is "_ = _ \<oplus> ?S1") by (subst finsum_insert) auto
  also have "(\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (n - i))) \<otimes> y =
             (\<Oplus>i\<in>{..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (Suc n - i)))" 
    by (subst finsum_ldistr)
       (auto simp: cring_simprules Suc add_pow_rdistr Suc_diff intro!: finsum_cong)
  also have "{..n} = insert 0 {1..n}" by auto
  also have "(\<Oplus>i\<in>\<dots>. add_pow R (n choose i) (x [^] i \<otimes> y [^] (Suc n - i))) =
             y [^] Suc n \<oplus> (\<Oplus>i\<in>{1..n}. add_pow R (n choose i) (x [^] i \<otimes> y [^] (Suc n - i)))"
    (is "_ = _ \<oplus> ?S2") by (subst finsum_insert) auto
  also have "(x [^] Suc n \<oplus> ?S1) \<oplus> (y [^] Suc n \<oplus> ?S2) =
               x [^] Suc n \<oplus> y [^] Suc n \<oplus> (?S1 \<oplus> ?S2)"
    by (simp add: cring_simprules)
  also have "?S1 \<oplus> ?S2 = (\<Oplus>i\<in>{1..n}. add_pow R (Suc n choose i) (x [^] i \<otimes> y [^] (Suc n - i)))"
    by (subst finsum_addf [symmetric], simp, simp, rule finsum_cong')
       (auto intro!: finsum_cong simp: binomial_Suc add.nat_pow_mult)
  also have "x [^] Suc n \<oplus> y [^] Suc n \<oplus> \<dots> =
               (\<Oplus>i\<in>{0, Suc n} \<union> {1..n}. add_pow R (Suc n choose i) (x [^] i \<otimes> y [^] (Suc n - i)))"
    by (subst finsum_Un_disjoint) (auto simp: cring_simprules)
  also have "{0, Suc n} \<union> {1..n} = {..Suc n}" by auto
  finally show ?case .
qed auto

lemma (in cring) binomial_finite_char:
  fixes p :: nat
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R" and "add_pow R p \<one> = \<zero>" "prime p"
  shows   "(x \<oplus> y) [^] p = x [^] p \<oplus> y [^] p"
proof -
  have *: "add_pow R (p choose i) (x [^] i \<otimes> y [^] (p - i)) = \<zero>" if "i \<in> {1..<p}" for i
  proof -
    have "p dvd (p choose i)"
      by (rule prime_dvd_choose) (use that assms in auto)
    then obtain k where [simp]: "(p choose i) = p * k"
      by auto
    have "add_pow R (p choose i) (x [^] i \<otimes> y [^] (p - i)) =
            add_pow R (p choose i) \<one> \<otimes> (x [^] i \<otimes> y [^] (p - i))"
      by (simp add: add_pow_ldistr)
    also have "add_pow R (p choose i) \<one> = \<zero>"
      using assms by (simp flip: add.nat_pow_pow)
    finally show ?thesis by simp
  qed

  have "(x \<oplus> y) [^] p = (\<Oplus>i\<in>{..p}. add_pow R (p choose i) (x [^] i \<otimes> y [^] (p - i)))"
    by (rule binomial) auto
  also have "\<dots> = (\<Oplus>i\<in>{0, p}. add_pow R (p choose i) (x [^] i \<otimes> y [^] (p - i)))"
    using * by (intro add.finprod_mono_neutral_cong_right) auto
  also have "\<dots> = x [^] p \<oplus> y [^] p"
    using assms prime_gt_0_nat[of p] by (simp add: cring_simprules)
  finally show ?thesis .
qed

lemma (in ring_hom_cring) hom_add_pow_nat:
  "x \<in> carrier R \<Longrightarrow> h (add_pow R (n::nat) x) = add_pow S n (h x)"
  by (induction n) auto

end