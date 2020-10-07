(*
  File:     Legendre_Symbol.thy
  Authors:  Daniel Stüwe

  Some more facts about the Legendre symbol that are missing from HOL-Number_Theory
*)
section \<open>Additional Facts about the Legendre Symbol\<close>
theory Legendre_Symbol
imports 
  "HOL-Number_Theory.Number_Theory"
begin

lemma basic_cong[simp]: 
  fixes p :: int
  assumes "2 < p"
  shows   "[-1 \<noteq>  1] (mod p)"
          "[ 1 \<noteq> -1] (mod p)"
          "[ 0 \<noteq>  1] (mod p)"
          "[ 1 \<noteq>  0] (mod p)"
          "[ 0 \<noteq> -1] (mod p)"
          "[-1 \<noteq>  0] (mod p)"
  using assms by (simp_all add: cong_iff_dvd_diff zdvd_not_zless)

lemma [simp]: "0 < n \<Longrightarrow> (a mod 2) ^ n = a mod 2" for n :: nat and a :: int
 by (metis not_mod_2_eq_0_eq_1 power_one zero_power)

lemma Legendre_in_cong_eq: 
  fixes p :: int
  assumes "p > 2" and "b \<in> {-1,0,1}"
  shows   "[Legendre a m = b] (mod p) \<longleftrightarrow> Legendre a m = b"
  using assms unfolding Legendre_def by auto

lemma Legendre_p_eq_2[simp]: "Legendre a 2 = a mod 2"  
  by (clarsimp simp: Legendre_def QuadRes_def cong_iff_dvd_diff) presburger

lemma Legendre_p_eq_1[simp]: "Legendre a 1 = 0" by (simp add: Legendre_def)

lemma euler_criterion_int:
  assumes "prime p" and "2 < p" 
  shows "[Legendre a p = a^((nat p-1) div 2)] (mod p)"
  using euler_criterion assms prime_int_nat_transfer
  by (metis int_nat_eq nat_numeral prime_gt_0_int zless_nat_conj) 

lemma QuadRes_neg[simp]: "QuadRes (-p) a = QuadRes p a" unfolding QuadRes_def by auto

lemma Legendre_neg[simp]: "Legendre a (-p) = Legendre a p" unfolding Legendre_def by auto

lemma Legendre_mult[simp]:
  assumes "prime p"
  shows "Legendre (a*b) p = Legendre a p * Legendre b p"
proof -
  consider "p = 2" | "p > 2"
    using assms order_le_less prime_ge_2_int by auto

  thus ?thesis proof (cases)
  case 1
    then show ?thesis
      by (metis Legendre_p_eq_2 mod_mult_eq mod_self mult_cancel_right2
                mult_eq_0_iff not_mod_2_eq_1_eq_0 one_mod_two_eq_one)
  next
  case 2
    hence "[Legendre (a*b) p = (a*b)^((nat p-1) div 2)] (mod p)"
      using euler_criterion_int assms by blast
  
    also have "[(a*b)^((nat p-1) div 2) = a^((nat p-1) div 2) * b^((nat p-1) div 2)] (mod p)"
      by (simp add: field_simps)
      
    also have "[a^((nat p-1) div 2) * b^((nat p-1) div 2) = Legendre a p * Legendre b p] (mod p)"
      using cong_sym[OF euler_criterion_int] assms 2 cong_mult by blast
  
    finally show ?thesis using Legendre_in_cong_eq[OF 2] by (simp add: Legendre_def)
  qed
qed

lemma QuadRes_mod[simp]: "p dvd n \<Longrightarrow> QuadRes p (a mod n) = QuadRes p a"
  by (simp add: mod_mod_cancel QuadRes_def cong_def)

lemma Legendre_mod[simp]: "p dvd n \<Longrightarrow> Legendre (a mod n) p = Legendre a p"
  by (simp add: mod_mod_cancel Legendre_def cong_def)

lemma two_cong_0_iff: "[2 = 0] (mod p) \<longleftrightarrow> p = 1 \<or> p = 2" for p :: nat
  unfolding cong_altdef_nat[of 0 2 p, simplified]
  using dvd_refl prime_nat_iff two_is_prime_nat by blast

lemma two_cong_0_iff_nat: "[2 = 0] (mod int p) \<longleftrightarrow> p = 1 \<or> p = 2"
  unfolding cong_iff_dvd_diff
  using two_is_prime_nat prime_nat_iff int_dvd_int_iff[of p 2]
  by auto

lemma two_cong_0_iff_int: "p > 0 \<Longrightarrow> [2 = 0] (mod p) \<longleftrightarrow> p = 1 \<or> p = 2" for p :: int
  by (metis of_nat_numeral pos_int_cases semiring_char_0_class.of_nat_eq_1_iff two_cong_0_iff_nat)

lemma QuadRes_2_2 [simp, intro]: "QuadRes 2 2"
  unfolding QuadRes_def
  unfolding cong_def
  by presburger

lemma Suc_mod_eq[simp]: "[Suc a = Suc b] (mod 2) = [a = b] (mod 2)"
  using Suc_eq_plus1_left cong_add_lcancel_nat by presburger

lemma div_cancel_aux: "c dvd a \<Longrightarrow> (d + a * b) div c = (d div c) + a div c * b" for a b c :: nat
  by (metis div_plus_div_distrib_dvd_right dvd_div_mult dvd_trans dvd_triv_left)

corollary div_cancel_Suc: "c dvd a \<Longrightarrow> 1 < c \<Longrightarrow> Suc (a * b) div c = a div c * b"
  using div_cancel_aux[where d = 1] by fastforce

lemma cong_aux_eq_1: "odd p \<Longrightarrow> [(p - 1) div 2 - p div 4 = (p^2 - 1) div 8] (mod 2)" for p :: nat
proof (induction p rule: nat_less_induct)
  case (1 n)

  consider "n = 1" | "n > 1" using odd_pos[OF \<open>odd n\<close>] by linarith

  then show ?case proof (cases) 
    assume "n > 1"

    then obtain m where m: "m = n - 2" and m': "odd m" "m < n" using \<open>odd n\<close> by simp
    then obtain b where b: "m = 2 * b + 1" using oddE by blast
  
    have IH: "[(m - 1) div 2 - m div 4 = (m^2 - 1) div 8] (mod 2)" using "1.IH" m' by simp

    have [simp]: "n = 2 * b + 1 + 2" using m \<open>n > 1\<close> b by auto

    have *: "(n\<^sup>2 - 1) div 8 = ((n - 2)\<^sup>2 - 1) div 8 + (n - 1) div 2"
      unfolding  power2_sum power2_eq_square by simp

    have "[(n - 1) div 2 - n div 4 = (n - 2 - 1) div 2 - (n - 2) div 4 + (n - 1) div 2] (mod 2)"
      by (rule cong_sym, cases "even b") (auto simp: cong_altdef_nat div_cancel_Suc elim: oddE)
    also have "[(n - 2 - 1) div 2 - (n - 2) div 4 + (n - 1) div 2 = (n\<^sup>2 - 1) div 8] (mod 2)"
        using IH cong_add_rcancel_nat unfolding * m by presburger
    finally show ?thesis . 
     
  qed simp
qed

lemma cong_2_pow[intro]: "(-1 :: int)^a = (-1)^b" if "[a = b] (mod 2)" for a b :: nat
proof -
  have "even a = even b"
    by (simp add: cong_dvd_iff that) 
  then show ?thesis by auto
qed

lemma card_Int: "card (A \<inter> B) = card A - card (A - B)" if "finite A"
  by (metis Diff_Diff_Int Diff_subset card_Diff_subset finite_Diff that)

text \<open>Proofs are inspired by \cite{Quadratic_Reciprocity}.\<close>

theorem supplement2_Legendre:
  fixes p :: int
  assumes "p > 2" "prime p"
  shows "Legendre 2 p = (-1) ^ (((nat p)^2 - 1) div 8)"
proof -
  interpret GAUSS "nat p" 2
    using assms
    unfolding GAUSS_def prime_int_nat_transfer
    by (simp add: two_cong_0_iff_int)

  have "card E = card ((\<lambda>x. x * 2 mod p) `
          {0<..(p - 1) div 2} \<inter> {(p - 1) div 2<..})" (is "_ = card ?A")
    unfolding E_def C_def B_def A_def image_image using assms by simp
  also have "(\<lambda>x. x * 2 mod p) ` {0<..(p - 1) div 2} = ((*) 2) ` {0<..(p - 1) div 2}"
    by (intro image_cong) auto
  also have "card (\<dots> \<inter> {(p - 1) div 2<..}) =
               nat ((p - 1) div 2) - card ((*) 2 ` {0<..(p - 1) div 2} - {(p - 1) div 2<..})"
    using assms by (subst card_Int) (auto simp: card_image inj_onI)
  also have "card (((*) 2) ` {0<..(p - 1) div 2} - {(p - 1) div 2<..}) = card {0 <.. (p div 4)}"
    by (rule sym, intro bij_betw_same_card[of "(*) 2"] bij_betw_imageI inj_onI)
       (insert assms prime_odd_int[of p], auto simp: image_def elim!: oddE)
  also have "\<dots> = nat p div 4" using assms by simp
  also have "nat ((p - 1) div 2) - nat p div 4 =  nat ((p - 1) div 2 - p div 4)"
    using assms by (simp add: nat_diff_distrib nat_div_distrib)
  finally have "card E = \<dots>" .

  then have "Legendre 2 p = (-1) ^ nat ((p - 1) div 2 - p div 4)"
    using gauss_lemma assms by simp
  also have "nat ((p - 1) div 2 - p div 4) = (nat p - 1) div 2 - nat p div 4"
    using assms by (simp add: nat_div_distrib nat_diff_distrib)
  also have "(-1) ^ \<dots> = ((-1) ^ (((nat p)^2 - 1) div 8) :: int)"
    using cong_aux_eq_1[of "nat p"] odd_p by blast 
  finally show ?thesis .
qed

theorem supplement1_Legendre:
  "prime p \<Longrightarrow> 2 < p \<Longrightarrow> Legendre (-1) p = (-1)^((p-1) div 2)"
  using euler_criterion[of p "-1"] Legendre_in_cong_eq[symmetric, of p]
  by (simp add: minus_one_power_iff)

lemma QuadRes_1_right [intro, simp]: "QuadRes p 1"
  by (metis QuadRes_def cong_def power_one)

lemma Legendre_1_left [simp]: "prime p \<Longrightarrow> Legendre 1 p = 1"
  by (auto simp add: Legendre_def cong_iff_dvd_diff not_prime_unit)

lemma cong_eq_0_not_coprime: "prime p \<Longrightarrow> [a = 0] (mod p) \<Longrightarrow> \<not>coprime a p" for a p :: int
  unfolding cong_iff_dvd_diff prime_int_iff 
  by auto

lemma not_coprime_cong_eq_0: "prime p \<Longrightarrow> \<not>coprime a p \<Longrightarrow> [a = 0] (mod p)" for a p :: int
  unfolding cong_iff_dvd_diff
  using prime_imp_coprime[of p a]
  by (auto simp: coprime_commute)

lemma prime_cong_eq_0_iff: "prime p \<Longrightarrow> [a = 0] (mod p) \<longleftrightarrow> \<not>coprime a p" for a p :: int
  using not_coprime_cong_eq_0[of p a] cong_eq_0_not_coprime[of p a]
  by auto

lemma Legendre_eq_0_iff [simp]: "prime p \<Longrightarrow> Legendre a p = 0 \<longleftrightarrow> \<not>coprime a p"
  unfolding Legendre_def by (auto simp: prime_cong_eq_0_iff)

lemma Legendre_prod_mset [simp]: "prime p \<Longrightarrow> Legendre (prod_mset M) p = (\<Prod>q\<in>#M. Legendre q p)"
  by (induction M) simp_all

lemma Legendre_0_eq_0[simp]: "Legendre 0 p = 0" unfolding Legendre_def by auto

lemma Legendre_values: "Legendre p q \<in> {1, - 1, 0}"
  unfolding Legendre_def by auto

end