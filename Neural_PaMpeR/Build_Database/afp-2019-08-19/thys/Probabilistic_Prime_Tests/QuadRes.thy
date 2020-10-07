(*
  File:     Miller_Rabin.thy
  Authors:  Daniel Stüwe

  Some facts about Quadratic Residues that are missing from the library
*)
section \<open>Additional Material on Quadratic Residues\<close>
theory QuadRes
imports 
  Jacobi_Symbol
  Algebraic_Auxiliaries
begin

text \<open>Proofs are inspired by \cite{Quadratic_Residues}.\<close>

lemma inj_on_QuadRes:
  fixes p :: int
  assumes "prime p"
  shows "inj_on (\<lambda>x. x^2 mod p) {0..(p-1) div 2}"
proof 
  fix x y :: int
  assume elem: "x \<in> {0..(p-1) div 2}" "y \<in> {0..(p-1) div 2}"

  have * : "abs(a) < p \<Longrightarrow> p dvd a \<Longrightarrow> a = 0" for a :: int
    using dvd_imp_le_int by force

  assume "x\<^sup>2 mod p = y\<^sup>2 mod p"

  hence "[x\<^sup>2 = y\<^sup>2] (mod p)" unfolding cong_def .

  hence "p dvd (x\<^sup>2 - y\<^sup>2)" by (simp add: cong_iff_dvd_diff)

  hence "p dvd (x + y) * (x - y)" 
    by (simp add: power2_eq_square square_diff_square_factored) 
  
  hence "p dvd (x + y) \<or> p dvd (x - y)"
    using \<open>prime p\<close> by (simp add: prime_dvd_mult_iff) 

  moreover have "p dvd x + y \<Longrightarrow> x + y = 0" "p dvd x - y \<Longrightarrow> x - y = 0" 
           and "0 \<le> x" "0 \<le> y"
      using elem  
      by (fastforce intro!: * )+
  
  ultimately show "x = y" by auto
qed

lemma QuadRes_set_prime: 
  assumes "prime p" and "odd p"
  shows "{x . QuadRes p x \<and> x \<in> {0..<p}} = {x^2 mod p | x . x \<in> {0..(p-1) div 2}}"
proof(safe, goal_cases)
  case (1 x)
  then obtain y where "[y\<^sup>2 = x] (mod p)" 
    unfolding QuadRes_def by blast

  then have A: "[(y mod p)\<^sup>2 = x] (mod p)" 
    unfolding cong_def
    by (simp add: power_mod)

  then have "[(-(y mod p))\<^sup>2 = x] (mod p)" 
    by simp

  then have B: "[(p - (y mod p))\<^sup>2 = x] (mod p)" 
    unfolding cong_def 
    using minus_mod_self1
    by (metis power_mod)

  have "p = 1 + ((p - 1) div 2) * 2"
    using prime_gt_0_int[OF \<open>prime p\<close>] \<open>odd p\<close>
    by simp

  then have C: "(p - (y mod p)) \<in> {0..(p - 1) div 2} \<or> y mod p \<in> {0..(p - 1) div 2}"
    using prime_gt_0_int[OF \<open>prime p\<close>] 
    by (clarsimp, auto simp: le_less)

  then show ?case proof
    show ?thesis if "p - y mod p \<in> {0..(p - 1) div 2}"
      using that B
      unfolding cong_def
      using \<open>x \<in> {0..<p}\<close> by auto

    show ?thesis if "y mod p \<in> {0..(p - 1) div 2}"
      using that A
      unfolding cong_def
      using \<open>x \<in> {0..<p}\<close> by auto
  qed
qed (auto simp: QuadRes_def cong_def)

corollary QuadRes_iff: 
  assumes "prime p" and "odd p"
  shows "(QuadRes p x \<and> x \<in> {0..<p}) \<longleftrightarrow> (\<exists> a \<in> {0..(p-1) div 2}. a^2 mod p = x)"
proof -
  have "(QuadRes p x \<and> x \<in> {0..<p}) \<longleftrightarrow> x \<in> {x. QuadRes p x \<and> x \<in> {0..<p}}"
    by auto
  also note QuadRes_set_prime[OF assms]
  also have "(x \<in> {x\<^sup>2 mod p |x. x \<in> {0..(p - 1) div 2}}) = (\<exists>a\<in>{0..(p - 1) div 2}. a\<^sup>2 mod p = x)"
    by blast
  finally show ?thesis .
qed

corollary card_QuadRes_set_prime:
  fixes p :: int
  assumes "prime p" and "odd p"
  shows "card {x. QuadRes p x \<and> x \<in> {0..<p}} = nat (p+1) div 2"
proof -
  have "card {x. QuadRes p x \<and> x \<in> {0..<p}} = card {x\<^sup>2 mod p | x . x \<in> {0..(p-1) div 2}}"
    unfolding QuadRes_set_prime[OF assms] ..

  also have "{x\<^sup>2 mod p | x . x \<in> {0..(p-1) div 2}} = (\<lambda>x. x\<^sup>2 mod p) ` {0..(p-1) div 2}"
    by auto

  also have "card ... = card {0..(p-1) div 2}"
    using inj_on_QuadRes[OF \<open>prime p\<close>] by (rule card_image)

  also have "... = nat (p+1) div 2" by simp

  finally show ?thesis .
qed

corollary card_not_QuadRes_set_prime:
  fixes p :: int
  assumes "prime p" and "odd p"
  shows "card {x. \<not>QuadRes p x \<and> x \<in> {0..<p}} = nat (p-1) div 2"
proof -
  have "{0..<p} \<inter> {x. QuadRes p x \<and> x \<in> {0..<p}} = {x. QuadRes p x \<and> x \<in> {0..<p}}"
    by blast

  moreover have "nat p - nat (p + 1) div 2 = nat (p - 1) div 2"
    using \<open>odd p\<close> prime_gt_0_int[OF \<open>prime p\<close>]
    by (auto elim!: oddE simp: nat_add_distrib nat_mult_distrib)

  ultimately have "card {0..<p} - card ({0..<p} \<inter> {x. QuadRes p x \<and> x \<in> {0..<p}}) = nat (p - 1) div 2"
    using card_QuadRes_set_prime[OF assms] and card_atLeastZeroLessThan_int by presburger    

  moreover have "{x. \<not>QuadRes p x \<and> x \<in> {0..<p}} = {0..<p} - {x. QuadRes p x \<and> x \<in> {0..<p}}"
    by blast

  ultimately show ?thesis by (auto simp add: card_Diff_subset_Int)
qed

lemma not_QuadRes_ex_if_prime:
  assumes "prime p" and "odd p"
  shows "\<exists> x. \<not>QuadRes p x"
proof -
  have "2 < p" using odd_prime_gt_2_int assms by blast

  then have False if "{x . \<not>QuadRes p x \<and> x \<in> {0..<p}} = {}"
    using card_not_QuadRes_set_prime[OF assms]
    unfolding that
    by simp

  thus ?thesis by blast
qed

lemma not_QuadRes_ex:
  "1 < p \<Longrightarrow> odd p \<Longrightarrow> \<exists>x. \<not>QuadRes p x"
proof (induction p rule: prime_divisors_induct)
  case (factor p x)
  then show ?case 
    by (meson not_QuadRes_ex_if_prime QuadRes_def cong_iff_dvd_diff dvd_mult_left even_mult_iff)
qed simp_all

end