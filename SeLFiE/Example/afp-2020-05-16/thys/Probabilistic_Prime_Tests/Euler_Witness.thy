(*
  File:     Euler_Witness.thy
  Author:   Daniel Stüwe

  Euler Witnesses as used in the Solovay--Strassen primality test
*)
section \<open>Euler Witnesses\<close>
theory Euler_Witness
imports 
  Jacobi_Symbol
  Residues_Nat
  QuadRes
begin

text \<open>
Proofs are inspired by \cite{solovay_strassen_ori, SolovayStrassenTest, wiki:Solovay_Strassen_test, planetmath:SolovayStrassenTest}.
\<close>
definition "euler_witness a p \<longleftrightarrow> [Jacobi a p \<noteq> a ^ ((p - 1) div 2)] (mod p)"
abbreviation "euler_liar a p \<equiv> \<not> euler_witness a p"

lemma euler_witness_mod[simp]: "euler_witness (a mod p) p = euler_witness a p"
  unfolding euler_witness_def cong_def
  by (simp add: power_mod)

lemma euler_liar_mod: "euler_liar (a mod p) p = euler_liar a p" by simp

lemma euler_liar_cong:
  assumes "[a = b] (mod p)"
  shows "euler_liar a p = euler_liar b p"
  by (metis assms cong_def euler_witness_mod)

lemma euler_witnessI: 
  "[x ^ ((n - 1) div 2) = a] (mod int n ) \<Longrightarrow> [Jacobi x (int n) \<noteq> a] (mod int n)
    \<Longrightarrow>  euler_witness x n"
  unfolding euler_witness_def  using cong_trans by blast

lemma euler_witnessI2:
  fixes a b :: int and k :: nat
  assumes "[a \<noteq> b] (mod k)"
    and "k dvd n" 
    and main: "euler_liar x n \<Longrightarrow> [Jacobi x n = a] (mod k)"
              "euler_liar x n \<Longrightarrow> [x ^ ((n - 1) div 2) = b] (mod k)"
  shows "euler_witness x n"
proof (rule ccontr)
  assume "euler_liar x n"
  then have "[Jacobi x (int n) = x ^ ((n - 1) div 2)] (mod k)"
    using \<open>k dvd n\<close> cong_dvd_modulus euler_witness_def int_dvd_int_iff by blast

  moreover note main[OF \<open>euler_liar x n\<close>]
  
  ultimately show False  
    using \<open>[a \<noteq> b] (mod k)\<close> and cong_trans cong_sym
    by metis
qed

lemma euler_witness_exists_weak:
  assumes "odd n" "\<not>prime n" "2 < n"
  shows "\<exists>a. euler_witness a n \<and> coprime a n"
proof -
  show ?thesis proof (cases "squarefree n")
    case True

    obtain p k where n: "n = p * k" and "1 < p" "p < n" "1 < k" "k < n" "prime p"
      using prime_divisor_exists_strong_nat[of n] \<open>\<not>prime n\<close> \<open>2 < n\<close> by auto

    have "coprime p k" using \<open>n = p * k\<close> and \<open>squarefree n\<close>
      using squarefree_mult_imp_coprime by blast

    hence "coprime (int p) (int k)" by simp

    have "odd p" using n \<open>odd n\<close> by simp
    
    then obtain b where "\<not>QuadRes p b" 
      using not_QuadRes_ex[of "int p"]
      using \<open>prime p\<close> prime_gt_1_int by auto 

    then have "[b \<noteq> 0] (mod p)" 
      unfolding cong_def QuadRes_def
      by (metis zero_power2)
    
    from binary_chinese_remainder_int[OF \<open>coprime (int p) (int k)\<close>, of b 1] 
    obtain x :: int where x: "[x = b] (mod p)" "[x = 1] (mod k)" by blast

    have "euler_witness x n"
    proof (rule euler_witnessI2[of "-1" 1 k])
      show "[x ^ ((n - 1) div 2) = 1] (mod k)" 
        using \<open>[x = 1] (mod k)\<close> and cong_def
        using cong_pow by fastforce
    next 
      have "Jacobi x n = Jacobi x p * Jacobi x k" 
        unfolding n 
        using \<open>1 < k\<close> \<open>1 < p\<close> by fastforce
  
      also note Jacobi_mod_cong[OF \<open>[x = b] (mod p)\<close>]
      also have "Jacobi b p = Legendre b p" 
        using \<open>prime p\<close> by (simp add: prime_p_Jacobi_eq_Legendre) 
      also have "... = -1" 
        unfolding Legendre_def 
        using \<open>[b \<noteq> 0] (mod p)\<close> and \<open>\<not> QuadRes p b\<close> by auto
  
     also note Jacobi_mod_cong[OF \<open>[x = 1] (mod k)\<close>] 
  
     finally show "[Jacobi x (int n) = - 1] (mod int k)"
       using \<open>1 < k\<close> by auto
    next 
      have "2 < k"
        using \<open>odd n\<close> and \<open>1 < k\<close> unfolding n 
        by(cases "k = 2") auto
        
      then show "[- 1 \<noteq> 1] (mod k)" by auto
    next
      show "k dvd n" unfolding n by simp
    qed

    have "coprime x p"
      using \<open>[b \<noteq> 0] (mod int p)\<close> \<open>[x = b] (mod int p)\<close> and \<open>prime p\<close> not_coprime_cong_eq_0[of p x] prime_nat_int_transfer
      by (blast intro: cong_sym cong_trans)

    then have "coprime x n"
      using n \<open>[x = 1] (mod int k)\<close>
      by (metis coprime_iff_invertible_int coprime_mult_right_iff mult.right_neutral of_nat_mult)

    then show ?thesis 
      using \<open>euler_witness x n\<close> by blast

  next
    case False
    then obtain p where p: "prime p" "p^2 dvd n" using \<open>odd n\<close>
      by (metis less_not_refl2 odd_pos squarefree_factorial_semiring) 
    hence "p dvd n" by auto

    from p have Z: "p dvd n div p" by (auto intro: dvd_mult_imp_div simp: power2_eq_square)

    have n: "n = p * (n div p)"
      using p(2) unfolding power2_eq_square by (metis dvd_mult_div_cancel dvd_mult_right)
    
    have "odd p" using p \<open>odd n\<close>
      by (meson dvd_trans even_power pos2)
      
    then have "2 < p" using prime_ge_2_nat[OF \<open>prime p\<close>] 
      by presburger  

    define a where a_def: "a = n div p + 1"

    have A: "a^p = (\<Sum>k=0..p. (p choose k) * (n div p)^k)" 
      unfolding binomial a_def
      using atLeast0AtMost by auto
               
    also have B: "... = 1 + (\<Sum>k = 1..p. (p choose k) * (n div p) ^ k)" (is "?A = 1 + ?B")
      by (simp add: sum.atLeast_Suc_atMost)

    also have C: "?B = (n div p) * (\<Sum>k = 1..p. (p choose k) * (n div p) ^ (k - 1))" (is "_ = _ * ?C")
      unfolding sum_distrib_left 
    proof (rule sum.cong)
      fix x
      assume "x \<in> {1..p}"
      hence "0 < x" by simp
      hence "(n div p) ^ x = n div p * (n div p) ^ (x - 1)"
        by (metis mult.commute power_minus_mult)
      thus "(p choose x) * (n div p) ^ x = n div p * ((p choose x) * (n div p) ^ (x-1))"
        by simp
    qed simp

    finally have 1: "a ^ p = 1 + n div p * (\<Sum>k = 1..p. (p choose k) * (n div p) ^ (k - 1))" .

    have D: "p dvd ?C"
    proof (rule dvd_sum, goal_cases)
      fix a
      assume "a \<in> {1..p}"
      show "p dvd (p choose a) * (n div p) ^ (a - 1)"
      proof(cases "a = p")
        note * = dvd_power_le[of _ _ 1, simplified]
        case True
        thus ?thesis 
          using \<open>p dvd n div p\<close> \<open>2 < p\<close> by (auto intro: *)
      next
        case False
        thus ?thesis 
          using \<open>a \<in> {1..p}\<close> and \<open>prime p\<close> 
          by (auto intro!: dvd_mult2 prime_dvd_choose)
      qed
    qed
    
    then obtain m where m: "?C = p * m"
      using dvdE by blast

    have "0 < p" using \<open>odd p\<close> and odd_pos by blast

    then have "?C \<noteq> 0"
      using   sum.atLeast_Suc_atMost[OF Suc_leI]
      by (simp add: Suc_leI sum.atLeast_Suc_atMost)

    then have "m \<noteq> 0" using m by fastforce 

    have "n dvd ?B"
      unfolding C m  using p by (auto simp: power2_eq_square)

    hence "?B mod n = 0" by presburger

    hence "[a^p = 1] (mod n)" 
      unfolding A B cong_def
      by (subst mod_Suc_eq[symmetric, unfolded Suc_eq_plus1_left]) simp

    have "\<not> p dvd n - 1"
      using p assms(1)
      by (metis One_nat_def Suc_leI dvd_diffD1 dvd_mult_right not_prime_unit odd_pos power2_eq_square)

    have "[(n div p + 1) \<noteq> 1] (mod n)"
      using \<open>2 < p\<close> \<open>odd n\<close> and \<open>prime p\<close> \<open>p\<^sup>2 dvd n\<close>
      using div_mult2_eq n nonzero_mult_div_cancel_left by (force dest!: cong_to_1_nat)

    then have "ord n a \<noteq> 1"
      using \<open>2 < p\<close> \<open>odd n\<close> and \<open>prime p\<close> \<open>p\<^sup>2 dvd n\<close>
      using ord_works[of a n] 
      unfolding a_def 
      by auto

    then have "ord n a = p"
      using ord_divides[of a p n] \<open>[a ^ p = 1] (mod n)\<close> \<open>prime p\<close>
      using prime_nat_iff by blast

    have "coprime n a"
      using \<open>prime p\<close> \<open>p\<^sup>2 dvd n\<close> \<open>p dvd n div p\<close> n
      unfolding a_def
      by (metis coprime_add_one_right coprime_mult_left_iff dvd_def)

    have "[(n - 1) div 2 \<noteq> 0] (mod p)" 
      using \<open>\<not> p dvd n - 1\<close> \<open>odd n\<close>
      by (subst cong_altdef_nat) (auto elim!: oddE)

    then have "[p \<noteq> (n - 1) div 2] (mod p)"
      using cong_mult_self_right[of 1 p, simplified] cong_sym cong_trans by blast

    then have "[a^((n-1) div 2) \<noteq> 1] (mod n)"
      using \<open>[a ^ p = 1] (mod n)\<close>
      using order_divides_expdiff[OF \<open>coprime n a\<close>, of p "(n-1) div 2", symmetric]
      unfolding \<open>ord n a = p\<close>
      using cong_sym cong_trans
      by blast

    then have "[(int a)^((n-1) div 2) \<noteq> 1] (mod n)"
      unfolding cong_def
      by (metis of_nat_1 of_nat_eq_iff of_nat_mod of_nat_power)

    have "Jacobi a n = Jacobi a (p * int (n div p))"
      using n by (metis of_nat_mult)
      
    also have "... = Jacobi a p * Jacobi a (n div p)"
      using \<open>odd n\<close> and \<open>n = p * (n div p)\<close>
      by (subst Jacobi_mult_right) auto

    also have "Jacobi a p = Jacobi 1 p"
      using \<open>p dvd n div p\<close>
      by (intro Jacobi_mod_cong) (auto simp: cong_iff_dvd_diff a_def)

    also have "... = 1"
      by (simp add: \<open>0 < p\<close>)

    also have "Jacobi a (n div p) = Jacobi 1 (n div p)"
      by (rule Jacobi_mod_cong) (simp add: cong_iff_dvd_diff a_def)

    also have "... = 1"
      using \<open>p dvd n\<close> \<open>prime p\<close> \<open>n > 2\<close>
      by (intro Jacobi_1_eq_1) (auto intro!: Nat.gr0I elim!: dvdE)

    finally show ?thesis using \<open>[int a ^ ((n - 1) div 2) \<noteq> 1] (mod n)\<close> \<open>coprime n a\<close>
      unfolding euler_witness_def
      by (intro exI[of _ "int a"]) (auto simp: cong_sym coprime_commute)
  qed
qed

lemma euler_witness_exists:
  assumes "odd n" "\<not>prime n" "2 < n"
  shows "\<exists>a. euler_witness a n \<and> coprime a n \<and> 0 < a \<and> a < n"
proof -
  obtain a where a: "euler_witness a n" "coprime a n"
    using euler_witness_exists_weak assms by blast

  then have "euler_witness (a mod n) n" "coprime (a mod n) n"
    using \<open>odd n\<close> by (simp_all add: odd_pos)

  moreover have "0 < (a mod n)" 
  proof -
    have "0 \<le> (a mod n)" by (rule pos_mod_sign) (use \<open>2 < n\<close> in simp)

    moreover have "0 \<noteq> (a mod n)"
    using \<open>coprime (a mod n) n\<close>  coprime_0_left_iff[of "int n"] \<open>2 < n\<close> by auto

    ultimately show ?thesis by linarith
  qed

  moreover have "a mod n < n"
    by (rule pos_mod_bound) (use \<open>2 < n\<close> in simp)

  ultimately show ?thesis by blast
qed

lemma euler_witness_exists_nat:
  assumes "odd n" "\<not>prime n" "2 < n"
  shows "\<exists>a. euler_witness (int a) n \<and> coprime a n \<and> 0 < a \<and> a < n"
  using euler_witness_exists[OF assms]
  using zero_less_imp_eq_int by fastforce

lemma euler_liar_1_p[intro, simp]: "p \<noteq> 0 \<Longrightarrow> euler_liar 1 p"
  unfolding euler_witness_def by simp

lemma euler_liar_mult:
  shows "euler_liar y n \<Longrightarrow> euler_liar x n \<Longrightarrow> euler_liar (x*y) n"
  unfolding euler_witness_def
  by (auto simp: power_mult_distrib intro: cong_mult)

lemma euler_liar_mult':
  assumes "1 < n" "coprime y n"
  shows "euler_liar y n \<Longrightarrow> euler_witness x n \<Longrightarrow> euler_witness (x*y) n"
proof(simp add: euler_witness_def power_mult_distrib, rule cong_mult_uneq', goal_cases)
case 1
  then show ?case 
    using Jacobi_eq_0_iff_not_coprime[of n y] Jacobi_values[of y n] and assms
    by auto
qed simp_all

lemma prime_imp_euler_liar:
  assumes "prime p" "2 < p" "0 < x" "x < p"
  shows   "euler_liar x p"
  using assms prime_p_Jacobi_eq_Legendre and euler_criterion
  unfolding euler_witness_def 
  by simp

locale euler_witness_context =
  fixes p :: nat
  assumes p_gt_1: "p > 1" and odd_p: "odd p"
begin

definition G where "G = Residues_Mult p"

sublocale residues_mult_nat p G
  by unfold_locales (use p_gt_1 in \<open>simp_all add: G_def\<close>)

definition "H = {x. coprime x p \<and> euler_liar (int x) p \<and> x \<in> {1..<p}}"
         
sublocale H: subgroup H G
proof -
  have subset: "H \<subseteq> carrier G" by (auto simp: H_def totatives_def)
  show "subgroup H G"
  proof (rule group.subgroupI, goal_cases)
    case 1
    then show ?case by (fact is_group)
  next
    case 3
    have "euler_liar 1 p" using p_gt_1
      unfolding euler_witness_def cong_def by simp
    then show ?case
      using p_gt_1 by (auto simp: H_def)
  next
    case (4 x)
    then have "coprime x p" "euler_liar x p" "1 \<le> x" "x < p"
      by (auto simp: H_def)

    define y where "y = inv\<^bsub>G\<^esub> x"

    from \<open>x \<in> H\<close> have "x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>"
      unfolding y_def using subset by (intro r_inv) auto

    hence *: "(x * y) mod p = 1" by (auto simp: y_def)
    hence **: "(int x * int y) mod p = 1"
      by (metis of_nat_1 of_nat_mod of_nat_mult)

    from * have "coprime y p" 
      using p_gt_1 \<open>x < p\<close> 
      by (auto simp add: coprime_iff_invertible'_nat cong_def mult.commute)

    moreover from 4 have "y \<in> carrier G" 
      using subset unfolding y_def by (intro inv_closed) auto

    hence "1 \<le> y" "y < p" using p_gt_1 totatives_less[of y p]
      by (auto simp: totatives_def)    

    moreover have "euler_liar 1 p"
      using p_gt_1 by (intro euler_liar_1_p) auto
    then have "euler_liar (int x * int y) p"
      using ** p_gt_1 by (subst euler_liar_cong[of "int x * int y" 1 p]) (auto simp: cong_def)

    then have "euler_liar y p"
      using \<open>coprime x p\<close> \<open>euler_liar x p\<close> and euler_liar_mult'[OF p_gt_1, of x y]
      by (metis coprime_int_iff mult.commute)
      
    ultimately show ?case by (auto simp: H_def simp flip: y_def) 
  next
    case (5 x y)
    then show ?case
      unfolding euler_witness_def H_def
      by (auto intro!: gre1I_nat cong_mult
               simp: coprime_commute coprime_dvd_mult_left_iff
                     nat_dvd_not_less zmod_int power_mult_distrib)
  qed fact+
qed

lemma H_finite: "finite H"
  unfolding H_def by simp

lemma euler_witness_coset:
  assumes "euler_witness x p"
  shows "y \<in> H #>\<^bsub>G\<^esub> x \<Longrightarrow> euler_witness y p"
  using assms euler_liar_mult'[OF p_gt_1, of _ x] unfolding r_coset_is_image H_def  
  by (auto simp add: mult.commute of_nat_mod)

lemma euler_liar_coset:
  assumes "euler_liar x p" "x \<in> carrier G"
  shows "y \<in> H #>\<^bsub>G\<^esub> x \<Longrightarrow> euler_liar y p"
  using is_group H.rcos_const[of x] assms totatives_less[of x p] p_gt_1
  by (auto simp: H_def totatives_def)

lemma in_cosets_aux:
  assumes "euler_witness x p" "x \<in> carrier G"
  shows "H #>\<^bsub>G\<^esub> x \<in> rcosets\<^bsub>G\<^esub> H"
  using assms by (intro rcosetsI) (auto simp: H_def totatives_def)

lemma H_cosets_aux:
  assumes "euler_witness x p"
  shows "(H #>\<^bsub>G\<^esub> x) \<inter> H = {}"
  using euler_witness_coset assms unfolding H_def by blast

lemma H_rcosets_aux:
  assumes "euler_witness x p" "x \<in> carrier G"
  shows "{H, H #>\<^bsub>G\<^esub> x} \<subseteq> rcosets\<^bsub>G\<^esub> H"
  using in_cosets_aux[OF assms] H.subgroup_in_rcosets[OF is_group]
  by blast

lemma H_not_eq_coset:
  assumes "euler_witness x p"
  shows "H \<noteq> H #>\<^bsub>G\<^esub> x"
  using H.one_closed H_def assms(1) euler_witness_coset by blast

lemma finite_cosets_H: "finite (rcosets\<^bsub>G\<^esub> H)"
  using rcosets_part_G[OF H.is_subgroup] 
  by (auto intro: finite_UnionD)

lemma card_cosets_limit:
  assumes "euler_witness x p" "x \<in> carrier G"
  shows "2 \<le> card (rcosets\<^bsub>G\<^esub> H)"
  using H_not_eq_coset[OF assms(1)] card_mono[OF finite_cosets_H H_rcosets_aux[OF assms]]
  by simp

lemma card_euler_liars_cosets_limit:
  assumes "\<not>prime p" "2 < p"
  shows "2 \<le> card (rcosets\<^bsub>G\<^esub> H)" "card H < (p - 1) div 2"
proof -
  have "H \<in> rcosets\<^bsub>G\<^esub> H" " H \<subseteq> carrier G"
    by (auto simp: is_group H.subgroup_in_rcosets simp del: carrier_eq)

  obtain a :: nat where "euler_witness a p" "coprime a p" "0 < a" "a < p"
    using odd_p assms euler_witness_exists_nat
    by blast

  moreover have a: "a \<in> carrier G"
    using calculation by (auto simp: totatives_def)

  ultimately show "2 \<le> card (rcosets\<^bsub>G\<^esub> H)"
    using card_cosets_limit by blast

  have "finite H"
    by (rule finite_subset[OF H.subset]) auto

  have "finite (H #>\<^bsub>G\<^esub> a)"
    by (rule cosets_finite[OF rcosetsI]) (use H.subset a in auto)

  have "H #>\<^bsub>G\<^esub> a \<in> rcosets\<^bsub>G\<^esub> H"
    using H.subset rcosetsI \<open>a \<in> carrier G\<close> by blast

  then have "card H = card (H #>\<^bsub>G\<^esub> a)"
    using card_rcosets_equal H.subset by blast

  moreover have "H \<union> H #>\<^bsub>G\<^esub> a \<subseteq> carrier G"
    using rcosets_part_G[OF H.is_subgroup]
    using H.subgroup_in_rcosets[OF is_group] and \<open>H #>\<^bsub>G\<^esub> a \<in> rcosets\<^bsub>G\<^esub> H\<close>
    by auto

  then have "card H + card (H #>\<^bsub>G\<^esub> a) \<le> card (carrier G)"
    using \<open>finite H\<close> \<open>finite (H #>\<^bsub>G\<^esub> a)\<close>
    using H_cosets_aux[OF \<open>euler_witness a p\<close>]
    using H.subset finite_subset card_Un_disjoint
    by (subst card_Un_disjoint[symmetric]) (auto intro: card_mono simp flip: card_Un_disjoint)

  ultimately have "card H \<le> card (carrier G) div 2"
    by linarith

  obtain pa k where pa: "p = pa * k" "1 < pa" "pa < p" "1 < k" "k < p" "prime pa"
    using prime_divisor_exists_strong_nat[OF p_gt_1 \<open>\<not> prime p\<close>]
    by blast

  hence "\<not>coprime pa p" by simp

  then have "carrier G \<subset> {1..<p}"
    using \<open>\<not> prime p\<close> pa(2, 3) by (auto simp: totatives_def)

  then have "card (carrier G) < p - 1"
    by (metis card_atLeastLessThan finite_atLeastLessThan psubset_card_mono)

  show "card H < (p - 1) div 2"
    using \<open>card H \<le> card (carrier G) div 2\<close> \<open>card (carrier G) < p - 1\<close>
    using odd_p less_mult_imp_div_less[of "card (carrier G)" "(p - 1) div 2" 2]
    by auto
qed

lemma prime_imp_G_is_H:
  assumes "prime p" "2 < p"
  shows "carrier G = H"
  unfolding H_def using assms prime_imp_euler_liar[of p] totatives_less[of _ p]
  by (auto simp: totatives_def)

end

end