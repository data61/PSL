subsubsection \<open>RSA instantiation\<close>

text\<open>It is known that the RSA collection forms an ETP. Here we instantitate our proof of security for OT 
that uses a general ETP for RSA. We use the proof of the general construction of OT. The main proof effort 
here is in showing the RSA collection meets the requirements of an ETP, mainly this involves showing the 
RSA mapping is a bijection.\<close>

theory ETP_RSA_OT imports
  ETP_OT
  Number_Theory_Aux
begin

type_synonym index = "(nat \<times> nat)"
type_synonym trap = nat
type_synonym range = nat
type_synonym domain = nat
type_synonym viewP1 = "((bool \<times> bool) \<times> nat \<times> nat) spmf"
type_synonym viewP2 = "(bool \<times> index \<times> (bool \<times> bool)) spmf"
type_synonym dist2 = "(bool \<times> index \<times> bool \<times> bool) \<Rightarrow> bool spmf"
type_synonym advP2 = "index \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> dist2 \<Rightarrow> bool spmf"

locale rsa_base = 
  fixes prime_set :: "nat set" \<comment> \<open>the set of primes used\<close>
    and B :: "index \<Rightarrow> nat \<Rightarrow> bool"
  assumes prime_set_ass: "prime_set \<subseteq> {x. prime x \<and> x > 2}"
    and finite_prime_set: "finite prime_set" 
    and prime_set_gt_2: "card prime_set > 2"
begin

lemma prime_set_non_empty: "prime_set \<noteq> {}" 
  using prime_set_gt_2 by auto

definition coprime_set :: "nat \<Rightarrow> nat set"
  where "coprime_set N \<equiv> {x. coprime x N \<and> x > 1 \<and> x < N}"

lemma coprime_set_non_empty: 
  assumes "N > 2" 
  shows "coprime_set N \<noteq> {}"
  by(simp add: coprime_set_def; metis assms(1) Suc_lessE coprime_Suc_right_nat lessI numeral_2_eq_2)

definition sample_coprime :: "nat \<Rightarrow> nat spmf"
  where "sample_coprime N = spmf_of_set (coprime_set (N))" 

lemma lossless_sample_coprime: 
  assumes "\<not> prime N" 
    and "N > 2"
  shows  "lossless_spmf (sample_coprime N)"
proof-
  have "coprime_set N \<noteq> {}" 
    by(simp add: coprime_set_non_empty assms) 
  also have "finite (coprime_set N)" 
    by(simp add: coprime_set_def)
  ultimately show ?thesis by(simp add: sample_coprime_def)
qed

lemma set_spmf_sample_coprime: 
  shows "set_spmf (sample_coprime N) = {x. coprime x N \<and> x > 1 \<and> x < N}"
  by(simp add: sample_coprime_def coprime_set_def)

definition sample_primes :: "nat spmf"
  where "sample_primes = spmf_of_set prime_set"

lemma lossless_sample_primes:
  shows "lossless_spmf sample_primes"
    by(simp add: sample_primes_def prime_set_non_empty finite_prime_set)

definition sample_primes_excl :: "nat set \<Rightarrow> nat spmf"
  where "sample_primes_excl P = spmf_of_set (prime_set - P)"

lemma lossless_sample_primes_excl: 
  shows "lossless_spmf (sample_primes_excl {P})"
  apply(simp add: sample_primes_excl_def finite_prime_set) 
  using prime_set_gt_2 subset_singletonD by fastforce

lemma set_spmf_sample_primes: 
  shows "set_spmf sample_primes \<subseteq> {x. prime x \<and> x > 2}"
  by(auto simp add: sample_primes_def prime_set_ass finite_prime_set)
  
lemma mem_samp_primes_gt_2: 
  shows "x \<in> set_spmf sample_primes \<Longrightarrow> x > 2" 
  apply (simp add: finite_prime_set sample_primes_def)
  using prime_set_ass by blast

lemma mem_samp_primes_prime: 
  shows "x \<in> set_spmf sample_primes \<Longrightarrow> prime x" 
  apply (simp add: finite_prime_set sample_primes_def prime_set_ass)
  using prime_set_ass by blast

lemma mem_samp_primes_excl_gt_2: 
  shows "x \<in> set_spmf (sample_primes_excl {y}) \<Longrightarrow> x > 2" 
  apply(simp add: finite_prime_set sample_primes_excl_def  prime_set_ass ) 
  using prime_set_ass by blast

lemma mem_samp_primes_excl_prime : 
  shows "x \<in> set_spmf (sample_primes_excl {y}) \<Longrightarrow> prime x" 
  apply (simp add: finite_prime_set sample_primes_excl_def)
  using prime_set_ass by blast

lemma sample_coprime_lem: 
  assumes "x \<in> set_spmf sample_primes" 
    and " y \<in> set_spmf (sample_primes_excl {x}) "
  shows "lossless_spmf (sample_coprime ((x - Suc 0) * (y - Suc 0)))"
proof-
  have gt_2: "x > 2" "y > 2" 
    using mem_samp_primes_gt_2 assms mem_samp_primes_excl_gt_2 by auto
  have "\<not> prime ((x-1)*(y-1))"  
  proof-
    have "prime x" "prime y" 
      using mem_samp_primes_prime mem_samp_primes_excl_prime assms by auto
    then show ?thesis using prod_not_prime gt_2 by simp
  qed
  also have "((x-1)*(y-1)) > 2" 
    by (metis (no_types, lifting) gt_2 One_nat_def Suc_diff_1 assms(1) assms(2) calculation 
          divisors_zero less_2_cases nat_1_eq_mult_iff nat_neq_iff not_numeral_less_one numeral_2_eq_2 
              prime_gt_0_nat rsa_base.mem_samp_primes_excl_prime rsa_base.mem_samp_primes_prime rsa_base_axioms two_is_prime_nat)
  ultimately show ?thesis using lossless_sample_coprime by simp
qed    

definition I :: "(index \<times> trap) spmf"
  where "I = do {
    P \<leftarrow> sample_primes;  
    Q \<leftarrow> sample_primes_excl {P};
    let N = P*Q;
    let N' = (P-1)*(Q-1);
    e \<leftarrow> sample_coprime N';
    let d = nat ((fst (bezw e N')) mod N');
    return_spmf ((N, e), d)}"

lemma lossless_I: "lossless_spmf I"
  by(auto simp add: I_def lossless_sample_primes lossless_sample_primes_excl Let_def sample_coprime_lem)

lemma set_spmf_I: 
  assumes "((N,e),d) \<in> set_spmf I" 
  obtains P Q where "N = P * Q" and "P \<noteq> Q"  and "prime P" and "prime Q" and "coprime e ((P - 1)*(Q - 1))"
  using assms apply(auto simp add: I_def Let_def) 
  using finite_prime_set mem_samp_primes_prime rsa_base.sample_primes_excl_def rsa_base_axioms sample_primes_def 
  by (simp add: set_spmf_sample_coprime)

definition domain :: "index \<Rightarrow> nat set"
  where "domain index \<equiv> {..< fst index}"

definition range :: "index \<Rightarrow> nat set"
  where "range index \<equiv> {..< fst index}"

lemma finite_range: "finite (range index)" 
  by(simp add: range_def)

lemma dom_eq_ran: "domain index = range index" 
  by(simp add: range_def domain_def)

definition f :: "index \<Rightarrow> (nat \<Rightarrow> nat)"
  where "f index x = x ^ (snd index) mod (fst index)"

text \<open>We must prove the RSA function is a bijection\<close>

lemma rsa_bijection:
  assumes coprime: "coprime e ((P-1)*(Q-1))"
    and prime_P: "prime (P::nat)" 
    and prime_Q: "prime Q"   
    and P_neq_Q: "P \<noteq> Q" 
    and x_lt_pq: "x < P * Q"
    and y_lt_pd: "y < P * Q"
    and rsa_map_eq: "x ^ e mod (P * Q) = y ^ e mod (P * Q)"
  shows "x = y"
proof-
  have flt_xP: "[x ^ P = x] (mod P)" 
    using fermat_little prime_P by blast
  have flt_yP: "[y ^ P = y] (mod P)" 
    using fermat_little prime_P by blast
  have flt_xQ: "[x ^ Q = x] (mod Q)" 
    using fermat_little prime_Q by blast
  have flt_yQ: "[y ^ Q = y] (mod Q)" 
    using fermat_little prime_Q by blast
  show ?thesis 
  proof(cases "y \<ge> x")
    case True
    hence ye_gt_xe: "y^e \<ge> x^e"
      by (simp add: power_mono)
    have x_y_exp_e: "[x^e = y^e] (mod P)"
      using cong_modulus_mult_nat  cong_altdef_nat True ye_gt_xe cong_sym cong_def assms by blast
    obtain d where d:  "[e*d = 1] (mod (P-1)) \<and> d \<noteq> 0" 
      using ex_inverse assms by blast
    then obtain k where k: "e*d = 1 + k*(P-1)" 
      using ex_k_mod assms by blast 
    hence xk_yk: "[x^(1 + k*(P-1)) = y^(1 + k*(P-1))] (mod P)" 
      by(metis k power_mult x_y_exp_e cong_pow) 
    have xk_x: "[x^(1 + k*(P-1)) = x] (mod P)" 
    proof(induct k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      assume  asm: "[x ^ (1 + k * (P - 1)) = x] (mod P)"
      then show ?case
      proof-
        have exp_rewrite: "(k * (P - 1) + P) = (1 + (k + 1) * (P - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_P prime_gt_1_nat semiring_normalization_rules(3))
        have "[x * x ^ (k * (P - 1)) = x] (mod P)" using asm by simp
        hence "[x ^ (k * (P - 1)) * x ^ P = x] (mod P)" using flt_xP
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[x ^ (k * (P - 1) + P) = x] (mod P)"
          by (simp add: power_add)
        hence "[x ^ (1 + (k + 1) * (P - 1)) = x] (mod P)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have yk_y: "[y^(1 + k*(P-1)) = y] (mod P)" 
    proof(induct k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      assume  asm: "[y ^ (1 + k * (P - 1)) = y] (mod P)"
      then show ?case
      proof-
        have exp_rewrite: "(k * (P - 1) + P) = (1 + (k + 1) * (P - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_P prime_gt_1_nat semiring_normalization_rules(3))
        have "[y * y ^ (k * (P - 1)) = y] (mod P)" using asm by simp
        hence "[y ^ (k * (P - 1)) * y ^ P = y] (mod P)" using flt_yP
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[y ^ (k * (P - 1) + P) = y] (mod P)"
          by (simp add: power_add)
        hence "[y ^ (1 + (k + 1) * (P - 1)) = y] (mod P)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have "[x^e = y^e] (mod Q)"
      by (metis rsa_map_eq cong_modulus_mult_nat cong_def mult.commute) 
    obtain d' where d':  "[e*d' = 1] (mod (Q-1)) \<and> d' \<noteq> 0" 
      by (metis mult.commute ex_inverse prime_P prime_Q P_neq_Q coprime)
    then obtain k' where k': "e*d' = 1 + k'*(Q-1)" 
      by(metis ex_k_mod mult.commute prime_P prime_Q P_neq_Q coprime)
    hence xk_yk': "[x^(1 + k'*(Q-1)) = y^(1 + k'*(Q-1))] (mod Q)"
      by(metis k' power_mult \<open>[x ^ e = y ^ e] (mod Q)\<close> cong_pow) 
    have xk_x': "[x^(1 + k'*(Q-1)) = x] (mod Q)" 
    proof(induct k')
      case 0
      then show ?case by simp
    next
      case (Suc k')
      assume  asm: "[x ^ (1 + k' * (Q - 1)) = x] (mod Q)"
      then show ?case
      proof-
        have exp_rewrite: "(k' * (Q - 1) + Q) = (1 + (k' + 1) * (Q - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_Q prime_gt_1_nat semiring_normalization_rules(3))
        have "[x * x ^ (k' * (Q - 1)) = x] (mod Q)" using asm by simp
        hence "[x ^ (k' * (Q - 1)) * x ^ Q = x] (mod Q)" using flt_xQ
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[x ^ (k' * (Q - 1) + Q) = x] (mod Q)"
          by (simp add: power_add)
        hence "[x ^ (1 + (k' + 1) * (Q - 1)) = x] (mod Q)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have yk_y': "[y^(1 + k'*(Q-1)) = y] (mod Q)" 
    proof(induct k')
      case 0
      then show ?case by simp
    next
      case (Suc k')
      assume  asm: "[y ^ (1 + k' * (Q - 1)) = y] (mod Q)"
      then show ?case
      proof-
        have exp_rewrite: "(k' * (Q - 1) + Q) = (1 + (k' + 1) * (Q - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_Q prime_gt_1_nat semiring_normalization_rules(3))
        have "[y * y ^ (k' * (Q - 1)) = y] (mod Q)" using asm by simp
        hence "[y ^ (k' * (Q - 1)) * y ^ Q = y] (mod Q)" using flt_yQ
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[y ^ (k' * (Q - 1) + Q) = y] (mod Q)"
          by (simp add: power_add)
        hence "[y ^ (1 + (k' + 1) * (Q - 1)) = y] (mod Q)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have P_dvd_xy: "P dvd (y - x)"
    proof-
      have "[x = y] (mod P)"
      using xk_x yk_y xk_yk 
      by (simp add: cong_def)
    thus ?thesis
      using cong_altdef_nat cong_sym True by blast
    qed
    have Q_dvd_xy: "Q dvd (y - x)"
    proof-
      have "[x = y] (mod Q)"
      using xk_x' yk_y' xk_yk'  
      by (simp add: cong_def)
    thus ?thesis
      using cong_altdef_nat cong_sym True by blast
    qed
    show ?thesis 
    proof-
    have "P*Q dvd (y - x)" using P_dvd_xy  Q_dvd_xy  
      by (simp add: assms divides_mult primes_coprime)
    then have "[x = y] (mod P*Q)" 
      by (simp add: cong_altdef_nat cong_sym True)
    hence "x mod P*Q = y mod P*Q" 
      using  cong_def xk_x xk_yk yk_y by metis 
    then show ?thesis 
      using \<open>[x = y] (mod P * Q)\<close> cong_less_modulus_unique_nat x_lt_pq y_lt_pd by blast 
    qed
  next 
    case False
    hence ye_gt_xe: "x^e \<ge> y^e" 
      by (simp add: power_mono)
    have pow_eq: "[x^e = y^e] (mod P*Q)" 
      by (simp add: cong_def assms)
    then have PQ_dvd_ye_xe: "(P*Q) dvd (x^e - y^e)" 
      using cong_altdef_nat False ye_gt_xe cong_sym by blast
    then have "[x^e = y^e] (mod P)"
      using cong_modulus_mult_nat pow_eq by blast
    obtain d where d:  "[e*d = 1] (mod (P-1)) \<and> d \<noteq> 0" using ex_inverse assms
      by blast
    then obtain k where k: "e*d = 1 + k*(P-1)" using ex_k_mod assms by blast 
    have xk_yk: "[x^(1 + k*(P-1)) = y^(1 + k*(P-1))] (mod P)"
    proof-
      have "[(x^e)^d = (y^e)^d] (mod P)" 
        using \<open>[x ^ e = y ^ e] (mod P)\<close> cong_pow by blast 
      then have "[x^(e*d) = y^(e*d)] (mod P)" 
        by (simp add: power_mult)
      thus ?thesis using k by simp
    qed
    have xk_x: "[x^(1 + k*(P-1)) = x] (mod P)"  
   proof(induct k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      assume  asm: "[x ^ (1 + k * (P - 1)) = x] (mod P)"
      then show ?case
      proof-
        have exp_rewrite: "(k * (P - 1) + P) = (1 + (k + 1) * (P - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_P prime_gt_1_nat semiring_normalization_rules(3))
        have "[x * x ^ (k * (P - 1)) = x] (mod P)" using asm by simp
        hence "[x ^ (k * (P - 1)) * x ^ P = x] (mod P)" using flt_xP
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[x ^ (k * (P - 1) + P) = x] (mod P)"
          by (simp add: power_add)
        hence "[x ^ (1 + (k + 1) * (P - 1)) = x] (mod P)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have yk_y: "[y^(1 + k*(P-1)) = y] (mod P)" 
   proof(induct k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      assume  asm: "[y ^ (1 + k * (P - 1)) = y] (mod P)"
      then show ?case
      proof-
        have exp_rewrite: "(k * (P - 1) + P) = (1 + (k + 1) * (P - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_P prime_gt_1_nat semiring_normalization_rules(3))
        have "[y * y ^ (k * (P - 1)) = y] (mod P)" using asm by simp
        hence "[y ^ (k * (P - 1)) * y ^ P = y] (mod P)" using flt_yP
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[y ^ (k * (P - 1) + P) = y] (mod P)"
          by (simp add: power_add)
        hence "[y ^ (1 + (k + 1) * (P - 1)) = y] (mod P)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have P_dvd_xy: "P dvd (x - y)"
    proof-
      have "[x = y] (mod P)" using xk_x yk_y xk_yk 
        by (simp add: cong_def)
      thus ?thesis 
        using cong_altdef_nat cong_sym False by simp
    qed
    have "[x^e = y^e] (mod Q)"
      using cong_modulus_mult_nat pow_eq PQ_dvd_ye_xe cong_dvd_modulus_nat dvd_triv_right by blast 
    obtain d' where d':  "[e*d' = 1] (mod (Q-1)) \<and> d' \<noteq> 0" 
      by (metis mult.commute ex_inverse prime_P prime_Q coprime P_neq_Q)
    then obtain k' where k': "e*d' = 1 + k'*(Q-1)" 
      by(metis ex_k_mod mult.commute prime_P prime_Q coprime P_neq_Q)
    have xk_yk': "[x^(1 + k'*(Q-1)) = y^(1 + k'*(Q-1))] (mod Q)"
    proof-
      have "[(x^e)^d' = (y^e)^d'] (mod Q)" 
        using \<open>[x ^ e = y ^ e] (mod Q)\<close> cong_pow by blast 
      then have "[x^(e*d') = y^(e*d')] (mod Q)" 
        by (simp add: power_mult)
      thus ?thesis using k'
        by simp
    qed
    have xk_x': "[x^(1 + k'*(Q-1)) = x] (mod Q)"  
   proof(induct k')
      case 0
      then show ?case by simp
    next
      case (Suc k')
      assume  asm: "[x ^ (1 + k' * (Q - 1)) = x] (mod Q)"
      then show ?case
      proof-
        have exp_rewrite: "(k' * (Q - 1) + Q) = (1 + (k' + 1) * (Q - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_Q prime_gt_1_nat semiring_normalization_rules(3))
        have "[x * x ^ (k' * (Q - 1)) = x] (mod Q)" using asm by simp
        hence "[x ^ (k' * (Q - 1)) * x ^ Q = x] (mod Q)" using flt_xQ
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[x ^ (k' * (Q - 1) + Q) = x] (mod Q)"
          by (simp add: power_add)
        hence "[x ^ (1 + (k' + 1) * (Q - 1)) = x] (mod Q)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have yk_y': "[y^(1 + k'*(Q-1)) = y] (mod Q)" 
    proof(induct k')
      case 0
      then show ?case by simp
    next
      case (Suc k')
      assume  asm: "[y ^ (1 + k' * (Q - 1)) = y] (mod Q)"
      then show ?case
      proof-
        have exp_rewrite: "(k' * (Q - 1) + Q) = (1 + (k' + 1) * (Q - 1))" 
          by (smt add.assoc add.commute le_add_diff_inverse nat_le_linear not_add_less1 prime_Q prime_gt_1_nat semiring_normalization_rules(3))
        have "[y * y ^ (k' * (Q - 1)) = y] (mod Q)" using asm by simp
        hence "[y ^ (k' * (Q - 1)) * y ^ Q = y] (mod Q)" using flt_yQ
          by (metis cong_scalar_right cong_trans mult.commute)
        hence "[y ^ (k' * (Q - 1) + Q) = y] (mod Q)"
          by (simp add: power_add)
        hence "[y ^ (1 + (k' + 1) * (Q - 1)) = y] (mod Q)"  
          using exp_rewrite by argo
        thus ?thesis by simp
      qed
    qed 
    have Q_dvd_xy: "Q dvd (x - y)"
    proof-
      have "[x = y] (mod Q)" 
        using xk_x' yk_y' xk_yk' by (simp add: cong_def)
      thus ?thesis
        using cong_altdef_nat cong_sym False by simp
    qed
    show ?thesis
    proof-
      have "P*Q dvd (x - y)" 
        using P_dvd_xy Q_dvd_xy by (simp add: assms divides_mult primes_coprime)
      hence 1: "[x = y] (mod P*Q)" 
        using False cong_altdef_nat linear by blast
      hence "x mod P*Q = y mod P*Q" 
        using cong_less_modulus_unique_nat x_lt_pq y_lt_pd by blast 
      thus ?thesis 
        using 1 cong_less_modulus_unique_nat x_lt_pq y_lt_pd by blast
    qed
  qed
qed

lemma rsa_bij_betw:
  assumes "coprime e ((P - 1)*(Q - 1))"
    and "prime P" 
    and "prime Q"   
    and "P \<noteq> Q"
  shows "bij_betw (f ((P * Q), e)) (range ((P * Q), e)) (range ((P * Q), e))"
proof-
  have PQ_not_0: "prime P \<longrightarrow> prime Q \<longrightarrow> P * Q \<noteq> 0"
  using assms by auto
  have "inj_on (\<lambda>x. x ^ snd (P * Q, e) mod fst (P * Q, e)) {..<fst (P * Q, e)}"
    apply(simp add: inj_on_def) 
    using rsa_bijection assms by blast
  moreover have "(\<lambda>x. x ^ snd (P * Q, e) mod fst (P * Q, e)) ` {..<fst (P * Q, e)} = {..<fst (P * Q, e)}"
    apply(simp add: assms(2) assms(3) prime_gt_0_nat PQ_not_0)
    apply(rule endo_inj_surj; auto simp add: assms(2) assms(3) image_subsetI prime_gt_0_nat PQ_not_0 inj_on_def) 
    using rsa_bijection assms by blast
  ultimately show ?thesis 
  unfolding bij_betw_def f_def range_def by blast
qed

lemma bij_betw1:
  assumes "((N,e),d) \<in> set_spmf I" 
  shows " bij_betw (f ((N), e)) (range ((N), e)) (range ((N), e))"
proof-
  obtain P Q where "N = P * Q" and "bij_betw (f ((P*Q), e)) (range ((P*Q), e)) (range ((P*Q), e))"
  proof-
    obtain P Q where "prime P" and "prime Q" and "N = P * Q" and "P \<noteq> Q" and "coprime e ((P - 1)*(Q - 1))"
      using set_spmf_I assms by blast
    then show ?thesis
      using rsa_bij_betw that by blast
  qed
  thus ?thesis by blast 
qed

sublocale etp: etp I domain range f B 
  by (auto simp add: etp_def dom_eq_ran finite_range bij_betw1 lossless_I; metis Iio_eq_empty_iff bot_nat_def fst_conv mult_eq_0_iff not_prime_0 range_def set_spmf_I)

sublocale etp: ETP_base I domain range f B
  apply(auto simp add: ETP_base_def dom_eq_ran finite_range local.etp.non_empty_range lossless_I)
  using dom_eq_ran local.etp.non_empty_range bij_betw1 by auto

end 

text\<open>After proving the RSA collection is an ETP the proofs of security come easily from the general proofs.\<close>

locale rsa_proof = rsa_base + 
  fixes HCP_ad :: real
begin

sublocale etp_proof: ETP_ot_12 I domain range f 
   by (auto simp add: etp.ETP_base_axioms ETP_ot_12_def)

lemma "sim_det_def.correctness funct_OT_12 etp.protocol m1 m2" 
  by (metis etp.correctness etp_proof.OT_12.correctness_def surj_pair)

lemma P1_sec: "sim_det_def.inf_theoretic_P1 etp.R1 etp.S1 funct_OT_12 m1 m2" 
  using local.etp_proof.P1_security by auto

lemma P2_sec:
  assumes "\<forall> a. lossless_spmf (D a)"
    and "\<And>b\<^sub>\<sigma>. local.etp.HCP_adv etp.\<A> m2 b\<^sub>\<sigma> D \<le> HCP_ad"
  shows "sim_det_def.adv_P2 etp.R2 etp.S2 funct_OT_12 m1 m2 D \<le> 2 * HCP_ad"
  using assms etp_proof.P2_security by blast

end 

locale rsa_asym =
  fixes prime_set :: "nat \<Rightarrow> nat set"
    and B :: "index \<Rightarrow> nat \<Rightarrow> bool"
    and hcp_advantage :: "nat \<Rightarrow> real"
  assumes rsa_proof_assm: "\<And> n. rsa_proof (prime_set n)"
begin

sublocale rsa_proof "(prime_set n)" B "(hcp_advantage n)"  
  using local.rsa_proof_assm  by simp

lemma P1_sec_asym: "sim_det_def.inf_theoretic_P1 (etp.R1 n) (etp.S1 n) funct_OT_12 m1 m2" 
  using P1_sec by simp 

lemma P2_sec_asym: 
  assumes "\<forall> a. lossless_spmf (D a)" 
    and HCP_adv_neg: "negligible (\<lambda> n. hcp_advantage n)"
    and hcp_adv_bound:  "\<forall>b\<^sub>\<sigma> n. local.etp.HCP_adv n etp.\<A> m2 b\<^sub>\<sigma> D \<le> hcp_advantage n"
  shows "negligible (\<lambda> n. sim_det_def.adv_P2  (etp.R2 n) (etp.S2 n) funct_OT_12 m1 m2 D)"
proof-
  have "negligible (\<lambda> n. 2 * hcp_advantage n)" using HCP_adv_neg 
    by (simp add: negligible_cmultI)
  moreover have "\<bar>sim_det_def.adv_P2  (etp.R2 n) (etp.S2 n) funct_OT_12 m1 m2 D\<bar> 
            = sim_det_def.adv_P2 (etp.R2 n) (etp.S2 n) funct_OT_12 m1 m2 D" 
    for n unfolding sim_det_def.adv_P2_def etp_proof.OT_12.adv_P2_def by linarith
  moreover have "sim_det_def.adv_P2 (etp.R2 n) (etp.S2 n) funct_OT_12 m1 m2 D \<le> 2 * hcp_advantage n" for n
    using P2_sec assms by blast
  ultimately show ?thesis 
    using assms negligible_le by presburger 
qed

end

end