theory Lehmer
imports
  Main
  "HOL-Number_Theory.Residues"
begin

section \<open>Lehmer's Theorem\<close>
text_raw \<open>\label{sec:lehmer}\<close>

text \<open>
  In this section we prove Lehmer's Theorem~\cite{lehmer1927fermat_converse} and its converse.
  These two theorems characterize a necessary and complete criterion for primality. This criterion
  is the basis of the Lucas-Lehmer primality test and the primality certificates of
  Pratt~\cite{pratt1975certificate}.
\<close>

lemma mod_1_coprime_nat:
  "coprime a b" if "0 < n" "[a ^ n = 1] (mod b)" for a b :: nat
proof -
  from that coprime_1_left have "coprime (a ^ n) b"
    using cong_imp_coprime cong_sym by blast
  with \<open>0 < n\<close> show ?thesis
    by simp
qed

text \<open>
  This is a weak variant of Lehmer's theorem: All numbers less then @{term "p - 1 :: nat"}
  must be considered.
\<close>

lemma lehmers_weak_theorem:
  assumes "2 \<le> p"
  assumes min_cong1: "\<And>x. 0 < x \<Longrightarrow> x < p - 1 \<Longrightarrow> [a ^ x \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof (rule totient_imp_prime)
  from \<open>2 \<le> p\<close> cong1 have "coprime a p"
    by (intro mod_1_coprime_nat[of "p - 1"]) auto
  then have "[a ^ totient p = 1] (mod p)"
    by (intro euler_theorem) auto
  then have "totient p \<ge> p - 1 \<or> totient p = 0"
    using min_cong1[of "totient p"] by fastforce
  moreover have "totient p > 0"
    using \<open>2 \<le> p\<close> by simp
  moreover from \<open>p \<ge> 2\<close> have "totient p < p" by (intro totient_less) auto
  ultimately show "totient p = p - 1" by presburger
qed (insert \<open>p \<ge> 2\<close>, auto)

lemma prime_factors_elem:
  fixes n :: nat assumes "1 < n" shows "\<exists>p. p \<in> prime_factors n"
  using assms by (cases "prime n") (auto simp: prime_factors_dvd prime_factor_nat)

lemma cong_pow_1_nat:
  "[a ^ x = 1] (mod b)" if "[a = 1] (mod b)" for a b :: nat
  using cong_pow [of a 1 b x] that by simp

lemma cong_gcd_eq_1_nat:
  fixes a b :: nat
  assumes "0 < m" and cong_props: "[a ^ m = 1] (mod b)" "[a ^ n = 1] (mod b)"
  shows "[a ^ gcd m n = 1] (mod b)"
proof -
  obtain c d where gcd: "m * c = n * d + gcd m n" using bezout_nat[of m n] \<open>0 < m\<close>
    by auto
  have cong_m: "[a ^ (m * c) = 1] (mod b)" and cong_n: "[a ^ (n * d) = 1] (mod b)"
    using cong_props by (simp_all only: cong_pow_1_nat power_mult)
  have "[1 * a ^ gcd m n = a ^ (n * d) * a ^ gcd m n] (mod b)"
    by (rule cong_scalar_right, rule cong_sym) (fact cong_n)
  also have "[a ^ (n * d) * a ^ gcd m n = a ^ (m * c)] (mod b)"
    using gcd by (simp add: power_add)
  also have "[a ^ (m * c) = 1] (mod b)" using cong_m by simp
  finally show "[a ^ gcd m n = 1] (mod b)" by simp
qed

lemma One_leq_div:
  "1 < b div a" if "a dvd b" "a < b" for a b :: nat
  using that by (metis dvd_div_mult_self mult.left_neutral mult_less_cancel2)

theorem lehmers_theorem:
  assumes "2 \<le> p"
  assumes pf_notcong1: "\<And>x. x \<in> prime_factors (p - 1) \<Longrightarrow> [a ^ ((p - 1) div x) \<noteq> 1] (mod p)"
  assumes cong1: "[a ^ (p - 1) = 1] (mod p)"
  shows "prime p"
proof cases
  assume "[a = 1] (mod p)" with \<open>2 \<le>p\<close> pf_notcong1 show ?thesis
    by (metis cong_pow_1_nat less_diff_conv linorder_neqE_nat linorder_not_less
      one_add_one prime_factors_elem two_is_prime_nat)
next
  assume A_notcong_1: "[a \<noteq> 1] (mod p)"
  { fix x assume "0 < x" "x < p - 1"
    have "[a ^ x \<noteq> 1] (mod p)"
    proof
      assume "[a ^ x = 1] (mod p)"
      then have gcd_cong_1: "[a ^ gcd x (p - 1) = 1] (mod p)"
        by (rule cong_gcd_eq_1_nat[OF \<open>0 < x\<close> _ cong1])

      have "gcd x (p - 1) = p - 1"
      proof (rule ccontr)
        assume "\<not>?thesis"
        then have gcd_p1: "gcd x (p - 1) dvd (p - 1)" "gcd x (p - 1) < p - 1"
          using gcd_le2_nat[of "p - 1" x] \<open>2 \<le> p\<close> by (simp, linarith)

        define c where "c = (p - 1) div (gcd x (p - 1))"
        then have p_1_eq: "p - 1 = gcd x (p - 1) * c" unfolding c_def using gcd_p1
          by (metis dvd_mult_div_cancel)

        from gcd_p1 have "1 < c" unfolding c_def by (rule One_leq_div)
        then obtain q where q_pf: "q \<in> prime_factors c"
          using prime_factors_elem by auto
        then have "q dvd c" by auto

        have "q \<in> prime_factors (p - 1)" using q_pf \<open>1 < c\<close> \<open>2 \<le> p\<close>
          by (subst p_1_eq) (simp add: prime_factors_product)
        moreover
        have "[a ^ ((p - 1) div q) = 1] (mod p)"
          by (subst p_1_eq,subst dvd_div_mult_self[OF \<open>q dvd c\<close>,symmetric])
             (simp del: One_nat_def add: power_mult gcd_cong_1 cong_pow_1_nat)
        ultimately
        show False using pf_notcong1 by metis
      qed
      then show False using \<open>x < p - 1\<close>
        by (metis \<open>0 < x\<close> gcd_le1_nat gr_implies_not0 linorder_not_less)
    qed
  }
  with lehmers_weak_theorem[OF \<open>2 \<le> p\<close> _ cong1] show ?thesis by metis
qed

text \<open>
  The converse of Lehmer's theorem is also true.
\<close>

lemma converse_lehmer_weak:
 assumes prime_p: "prime p"
 shows "\<exists> a. [a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))
             \<and> a > 0 \<and> a < p"
 proof -
   have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
   obtain a where a:"a \<in> {1 .. p - 1} \<and> {1 .. p - 1} = {a^i mod p | i . i \<in> UNIV}"
    using residue_prime_mult_group_has_gen[OF prime_p] by blast
  {
   { fix x::nat assume x:"0 < x \<and> x \<le> p - 2 \<and> [a^x = 1] (mod p)"
     have "{a^i mod p| i. i \<in> UNIV} = {a^i mod p | i. 0 < i \<and> i \<le> x}"
     proof
      show "{a ^ i mod p | i. 0 < i \<and> i \<le> x} \<subseteq> {a ^ i mod p | i. i \<in> UNIV}" by blast
      { fix y assume y:"y \<in> {a^i mod p| i . i \<in> UNIV}"
        then obtain i where i:"y = a^i mod p" by auto
        define q r where "q = i div x" and "r = i mod x"
        have "i = q*x + r" by (simp add: r_def q_def)
        hence y_q_r:"y = (((a ^ (q*x)) mod p) * ((a ^ r) mod p)) mod p"
          by (simp add: i power_add mod_mult_eq)
        have "a ^ (q*x) mod p = (a ^ x mod p) ^ q mod p"
          by (simp add: power_mod mult.commute power_mult[symmetric])
        then have y_r:"y = a ^ r mod p" using \<open>p\<ge>2\<close> x
          by (simp add: cong_def y_q_r)
        have "y \<in> {a ^ i mod p | i. 0 < i \<and> i \<le> x}"
        proof (cases)
          assume "r = 0"
          then have "y = a^x mod p" using \<open>p\<ge>2\<close> x
            by (simp add: cong_def y_r)
          thus ?thesis using x by blast
        next
          assume "r \<noteq> 0"
          thus ?thesis using x by (auto simp add: y_r r_def)
        qed
      }
      thus " {a ^ i mod p|i. i \<in> UNIV} \<subseteq> {a ^ i mod p | i. 0 < i \<and> i \<le> x}" by auto
    qed
    note X = this

    have "p - 1 = card {1 .. p - 1}" by auto
    also have "{1 .. p - 1} = {a^i mod p | i. 1 \<le> i \<and> i \<le> x}" using X a by auto
    also have "\<dots> = (\<lambda> i. a^i mod p) ` {1..x}" by auto
    also have "card \<dots> \<le> p - 2"
      using Finite_Set.card_image_le[of "{1..x}" "\<lambda> i. a^i mod p"] x by auto
    finally have False using \<open>2 \<le> p\<close> by arith
   }
   hence "\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p)" by auto
 } note a_is_gen = this
 {
    assume "a>1"
    have "\<not> p dvd a "
    proof (rule ccontr)
      assume "\<not> \<not> p dvd a"
      hence "p dvd a" by auto
      have "p \<le> a" using dvd_nat_bounds[OF _ \<open>p dvd a\<close>] a by simp
      thus False using \<open>a>1\<close> a by force
    qed
    hence "coprime a p"
      using prime_imp_coprime_nat [OF prime_p] by (simp add: ac_simps)
    then have "[a ^ totient p = 1] (mod p)"
      by (rule euler_theorem)
    also from prime_p have "totient p = p - 1"
      by (rule totient_prime)
    finally have "[a ^ (p - 1) = 1] (mod p)" .
  }
  hence "[a^(p - 1) = 1] (mod p)" using a by fastforce
  thus ?thesis using a_is_gen a by auto
 qed

theorem converse_lehmer:
 assumes prime_p:"prime(p)"
 shows "\<exists> a . [a^(p - 1) = 1] (mod p) \<and>
              (\<forall> q. q \<in> prime_factors (p - 1) \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))
              \<and> a > 0 \<and> a < p"
 proof -
  have "p \<ge> 2" by (rule prime_ge_2_nat[OF prime_p])
  obtain a where a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> x . 0 < x \<longrightarrow> x \<le> p - 2 \<longrightarrow> [a^x \<noteq> 1] (mod p))
                    \<and> a > 0 \<and> a < p"
    using converse_lehmer_weak[OF prime_p] by blast
  { fix q assume q:"q \<in> prime_factors (p - 1)"
    hence "0 < q \<and> q \<le> p - 1" using \<open>p\<ge>2\<close>
      by (auto simp add: dvd_nat_bounds prime_factors_gt_0_nat)
    hence "(p - 1) div q \<ge> 1" using div_le_mono[of "q" "p - 1" q] div_self[of q] by simp
    have "q \<ge> 2" using q by (auto intro: prime_ge_2_nat)
    hence "(p - 1) div q < p - 1" using \<open>p \<ge> 2\<close> by simp
    hence "[a^((p - 1) div q) \<noteq> 1] (mod p)" using a \<open>(p - 1) div q \<ge> 1\<close>
      by (auto simp add: Suc_diff_Suc less_eq_Suc_le)
  }
  thus ?thesis using a by auto
 qed

end
