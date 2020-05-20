theory Number_Theory_Aux imports
  "HOL-Number_Theory.Cong"
  "HOL-Number_Theory.Residues"
begin

lemma bezw_inverse:
  assumes "gcd (e :: nat) (N ::nat) = 1" 
  shows "[nat e * nat ((fst (bezw e N)) mod N) = 1] (mod nat N)"
proof-
  have "(fst (bezw e N) * e + snd (bezw e N) * N) mod N = 1 mod N"
    by (metis assms bezw_aux zmod_int)
  hence "(fst (bezw e N) mod N * e mod N) = 1 mod N" 
    by (simp add: mod_mult_right_eq mult.commute)
  hence cong_eq: "[(fst (bezw e N) mod N * e) = 1] (mod N)" 
    by (metis of_nat_1 zmod_int cong_def)
  hence "[nat (fst (bezw e N) mod N) * e = 1] (mod N)" 
  proof -
    { assume "int (nat (fst (bezw e N) mod int N)) \<noteq> fst (bezw e N) mod int N"
      have "N = 0 \<longrightarrow> 0 \<le> fst (bezw e N) mod int N"
        by fastforce
      then have "int (nat (fst (bezw e N) mod int N)) = fst (bezw e N) mod int N"
        by fastforce }
    then have "[int (nat (fst (bezw e N) mod int N) * e) = int 1] (mod int N)"
      by (metis cong_eq of_nat_1 of_nat_mult)
    then show ?thesis 
      using cong_int_iff by blast
  qed
  then show ?thesis by(simp add: mult.commute)
qed

lemma inverse: 
  assumes "gcd x (q::nat) = 1" 
    and "q > 0" 
  shows "[x * (fst (bezw x q)) = 1] (mod q)"
proof-
  have int_eq: "fst (bezw  x q) * x + snd (bezw x q) * int q = 1" 
    by (metis assms(1) bezw_aux of_nat_1)
  hence int_eq': "(fst (bezw  x q) * x + snd (bezw x q) * int q) mod q = 1 mod q" 
    by (metis of_nat_1 zmod_int)
  hence "(fst (bezw x q) * x) mod q = 1 mod q"
    by simp 
  hence "[(fst (bezw x q)) * x  = 1] (mod q)" 
    using cong_def int_eq int_eq' by metis
  then show ?thesis by(simp add: mult.commute) 
qed

lemma prod_not_prime: 
  assumes "prime (x::nat)" 
    and "prime y" 
    and "x > 2" 
    and "y > 2" 
  shows "\<not> prime ((x-1)*(y-1))"
  by (metis assms One_nat_def Suc_diff_1 nat_neq_iff numeral_2_eq_2 prime_gt_0_nat prime_product)

lemma ex_inverse:
  assumes coprime: "coprime (e :: nat) ((P-1)*(Q-1))" 
    and "prime P" 
    and "prime Q"   
    and "P \<noteq> Q" 
  shows "\<exists> d. [e*d = 1] (mod (P-1)) \<and> d \<noteq> 0"
proof-
  have "coprime e (P-1)" 
    using assms(1) by simp
  then obtain d where d: "[e*d = 1] (mod (P-1))" 
    using cong_solve_coprime_nat by auto
  then show ?thesis by (metis cong_0_1_nat cong_1 mult_0_right zero_neq_one)
qed

lemma ex_k1_k2:
  assumes coprime: "coprime (e :: nat) ((P-1)*(Q-1))" 
    and "[e*d = 1] (mod (P-1))"
  shows "\<exists> k1 k2. e*d + k1*(P-1) = 1 + k2*(P-1)"
  by (metis assms(2) cong_iff_lin_nat)

lemma ex_k_mod:
  assumes coprime: "coprime (e :: nat) ((P-1)*(Q-1))" 
    and "P \<noteq> Q"
    and "prime P"
    and "prime Q"
    and "d \<noteq> 0"
    and " [e*d = 1] (mod (P-1))"
  shows "\<exists> k. e*d = 1 + k*(P-1)"
proof-
  have "e > 0"  
    using assms(1) assms(2) prime_gt_0_nat by fastforce
  then have "e*d \<ge> 1" using assms by simp
  then obtain k where k: "e*d = 1 + k*(P-1)" 
    using assms(6) cong_to_1'_nat by auto
  then show ?thesis
    by simp
qed

lemma fermat_little:
  assumes "prime (P :: nat)" 
  shows "[x^P = x] (mod P)" 
proof(cases "P dvd x")
  case True
  hence "x mod P = 0" by simp
  moreover have "x ^ P mod P = 0" 
    by (simp add: True assms prime_dvd_power_nat_iff prime_gt_0_nat)
  ultimately show ?thesis 
    by (simp add: cong_def)
next
  case False
  hence "[x ^ (P - 1) = 1] (mod P)" 
    using fermat_theorem assms by blast
  then show ?thesis  
    by (metis assms cong_def diff_diff_cancel diff_is_0_eq' diff_zero mod_mult_right_eq power_eq_if power_one_right prime_ge_1_nat zero_le_one)
qed

end