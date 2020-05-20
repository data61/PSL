theory Number_Theory_Aux imports
  "HOL-Number_Theory.Cong"
  "HOL-Number_Theory.Residues"
begin

abbreviation inverse where "inverse x q \<equiv> (fst (bezw x q))"

lemma inverse: assumes "gcd x q = 1" 
  shows "[x * inverse x q = 1] (mod q)"
proof-
  have 2: "fst (bezw x q) * x + snd (bezw x q) * int q = 1" 
    using bezw_aux assms int_minus 
    by (metis Num.of_nat_simps(2)) 
  hence 3: "(fst (bezw x q) * x + snd (bezw x q) * int q) mod q = 1 mod q" 
    by (metis assms bezw_aux of_nat_mod)
  hence 4: "(fst (bezw x q) * x) mod q = 1 mod q"
    by simp 
  hence 5:  "[(fst (bezw x q)) * x  = 1] (mod q)" 
    using 2 3 cong_def by force 
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
    and " [e*d = 1] (mod (P-1))"
  shows "\<exists> k1 k2. e*d + k1*(P-1) = 1 + k2*(P-1)"
  by (metis assms(2) cong_iff_lin_nat)
lemma "a > b \<Longrightarrow>int a - int b = int (a - b)" 
  by simp

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

lemma fermat_little_theorem:
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
  hence "[x ^ (P - 1) = 1] (mod P)" using fermat_theorem assms by blast
  then show ?thesis  
    by (metis Suc_diff_1 assms cong_scalar_left nat_mult_1_right not_gr_zero not_prime_0 power_Suc)
qed

lemma prime_field:
  assumes "prime (q::nat)" 
    and "a < q" 
    and "a \<noteq> 0"
  shows "coprime a q"
  by (meson assms coprime_commute dvd_imp_le linorder_not_le neq0_conv prime_imp_coprime)

end