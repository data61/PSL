(*
  File:     Gauss_Sums_Auxiliary.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM
*)
section \<open>Auxiliary material\<close>
theory Gauss_Sums_Auxiliary
imports
  Dirichlet_L.Dirichlet_Characters
  Dirichlet_Series.Moebius_Mu
  Dirichlet_Series.More_Totient
begin

subsection \<open>Various facts\<close>

lemma sum_div_reduce:
  fixes d :: nat and f :: "nat \<Rightarrow> complex"
  assumes "d dvd k" "d > 0" 
  shows "(\<Sum>n | n \<in> {1..k} \<and> d dvd n. f n) = (\<Sum>c \<in> {1..k div d}. f (c*d))" 
   by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k * d" "\<lambda>k. k div d"])
     (use assms in \<open>fastforce simp: div_le_mono\<close>)+

lemma prod_div_sub:
  fixes f :: "nat \<Rightarrow> complex"
  assumes "finite A" "B \<subseteq> A" "\<forall>b \<in> B. f b \<noteq> 0"
  shows "(\<Prod> i \<in> A - B. f i) = ((\<Prod> i \<in> A. f i) div (\<Prod> i \<in> B. f i))"
  using assms
proof (induction "card B" arbitrary: B)
case 0
  then show ?case 
    using infinite_super by fastforce
next
  case (Suc n)
  then show ?case 
  proof -
    obtain B' x where decomp: "B = B' \<union> {x} \<and> x \<notin> B'" 
      using card_eq_SucD[OF Suc(2)[symmetric]] insert_is_Un by auto
    then have B'card: "card B' = n" using Suc(2) 
      using Suc.prems(2) assms(1) finite_subset by fastforce
    have "prod f (A - B) = prod f ((A-B') - {x})"
      by (simp add: decomp,subst Diff_insert,simp)
    also have "\<dots> = (prod f (A-B')) div f x"  
      using prod_diff1[of "A-B'" f x] Suc decomp by auto
    also have "\<dots> = (prod f A div prod f B') div f x"
      using Suc(1)[of B'] Suc(3) B'card decomp
            Suc.prems(2) Suc.prems(3) by force
    also have "\<dots> = prod f A div (prod f B' * f x)" by auto
    also have "\<dots> = prod f A div prod f B"
      using decomp Suc.prems(2) assms(1) finite_subset by fastforce
    finally show ?thesis by blast
  qed
qed 

lemma linear_gcd:
  fixes a b c d :: nat
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "coprime a c" "coprime b d" 
  shows "gcd (a*b) (c*d) = (gcd a d) * (gcd b c)"
  using assms
proof -
  define q1 :: nat where "q1 = a div gcd a d" 
  define q2 :: nat where "q2 = c div gcd b c" 
  define q3 :: nat where "q3 = b div gcd b c"
  define q4 :: nat where "q4 = d div gcd a d"
  
  have "coprime q1 q2" "coprime q3 q4" 
    unfolding q1_def q2_def q3_def q4_def
  proof -
    have "coprime (a div gcd a d) c" 
      using \<open>coprime a c\<close> coprime_mult_left_iff[of "a div gcd a d" "gcd a d" c]
            dvd_mult_div_cancel[OF gcd_dvd1, of a b] by simp
    then show "coprime (a div gcd a d) (c div gcd b c)"
      using coprime_mult_right_iff[of "a div gcd a d" "gcd b c" "c div gcd b c"]
          dvd_div_mult_self[OF gcd_dvd2[of b c]] by auto    
    have "coprime (b div gcd b c) d" 
      using \<open>coprime b d\<close> coprime_mult_left_iff[of "b div gcd b c" "gcd b c" d]
            dvd_mult_div_cancel[OF gcd_dvd1, of a b] by simp
    then show "coprime (b div gcd b c) (d div gcd a d)"
      using coprime_mult_right_iff[of "b div gcd b c" "gcd a d" "d div gcd a d"]
          dvd_div_mult_self[OF gcd_dvd2[of b c]] by auto 
  qed
  moreover have "coprime q1 q4" "coprime q3 q2"
    unfolding q1_def q2_def q3_def q4_def 
    using assms div_gcd_coprime by blast+
  ultimately have 1: "coprime (q1*q3) (q2*q4)" 
    by simp 
  have "gcd (a*b) (c*d) = (gcd a d) * (gcd b c) * gcd (q1*q3) (q2*q4)"
    unfolding q1_def q2_def q3_def q4_def
    by (subst gcd_mult_distrib_nat[of "gcd a d * gcd b c"],
       simp add: field_simps,
       simp add: mult.left_commute semiring_normalization_rules(18))
  from this 1 show "gcd (a*b) (c*d) = (gcd a d) * (gcd b c)" by auto
qed  

lemma reindex_product_bij:
  fixes a b m k :: nat
  defines "S \<equiv> {(d1,d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}"
  defines "T \<equiv> {d. d dvd (gcd a m) * (gcd k b)}"
  defines "f \<equiv> (\<lambda>(d1,d2). d1 * d2)"
  assumes "coprime a k"
  shows "bij_betw f S T"
  unfolding bij_betw_def
proof
  show inj: "inj_on f S"
    unfolding f_def 
  proof -
    {fix d1 d2 d1' d2'
    assume "(d1,d2) \<in> S" "(d1',d2') \<in> S"
    then have dvd: "d1 dvd gcd a m" "d2 dvd gcd k b" 
              "d1' dvd gcd a m" "d2' dvd gcd k b"
      unfolding S_def by simp+
    assume "f (d1,d2) = f (d1',d2')" 
    then have eq: "d1 * d2 = d1' * d2'" 
      unfolding f_def by simp
    from eq dvd have eq1: "d1 = d1'" 
      by (simp,meson assms coprime_crossproduct_nat coprime_divisors)
    from eq dvd have eq2: "d2 = d2'"
      using assms(4) eq1 by auto
    from eq1 eq2 have "d1 = d1' \<and> d2 = d2'" by simp} 
   then show "inj_on (\<lambda>(d1, d2). d1 * d2) S" 
    using S_def f_def by (intro inj_onI,blast)
  qed
  show surj: "f ` S = T" 
  proof -
    {fix d
      have "d dvd (gcd a m) * (gcd k b)
       \<longleftrightarrow> (\<exists>d1 d2. d = d1*d2 \<and> d1 dvd gcd a m \<and> d2 dvd gcd k b)"
        using division_decomp mult_dvd_mono by blast}
      then show ?thesis
        unfolding f_def S_def T_def image_def
        by auto
  qed
qed

lemma p_div_set:
  shows "{p. p \<in>prime_factors a \<and> \<not> p dvd N} = 
         ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
  (is "?A = ?B") 
proof 
  show "?A \<subseteq> ?B" 
  proof (simp)
    { fix p 
      assume as: "p \<in># prime_factorization a" "\<not> p dvd N"
      then have 1: "p \<in> prime_factors (a * N)" 
      proof -
        from in_prime_factors_iff[of p a] as
        have "a \<noteq> 0" "p dvd a" "prime p" by simp+
        have "N \<noteq> 0" using \<open>\<not> p dvd N\<close> by blast
        have "a * N \<noteq> 0" using \<open>a \<noteq> 0\<close> \<open>N \<noteq> 0\<close> by auto
        have "p dvd a*N" using \<open>p dvd a\<close> by simp
        show ?thesis 
          using \<open>a*N \<noteq> 0\<close> \<open>p dvd a*N\<close> \<open>prime p\<close> in_prime_factors_iff by blast
      qed
      from as have 2: "p \<notin> prime_factors N" by blast
      from 1 2 have "p \<in> prime_factors (a * N) - prime_factors N"
       by blast 
    }
    then show "{p. p \<in># prime_factorization a \<and> \<not> p dvd N}
               \<subseteq> prime_factors (a * N) - prime_factors N" by blast
  qed

  show "?B \<subseteq> ?A"
  proof (simp)
    { fix p 
      assume as: "p \<in> prime_factors (a * N) - prime_factors N"
      then have 1: "\<not> p dvd N" 
      proof -
        from as have "p \<in> prime_factors (a * N)" "p \<notin> prime_factors N"
          using DiffD1 DiffD2 by blast+
        then show ?thesis by (simp add: in_prime_factors_iff)        
      qed
      have 2: "p \<in># prime_factorization a" 
      proof -
        have "p dvd (a*N)" "prime p" "a*N \<noteq> 0" using in_prime_factors_iff as by blast+
        have "p dvd a" using \<open>\<not> p dvd N\<close> prime_dvd_multD[OF \<open>prime p\<close> \<open>p dvd (a*N)\<close>] by blast
        have "a \<noteq> 0" using \<open>a*N \<noteq> 0\<close> by simp
        show ?thesis using in_prime_factors_iff \<open>a \<noteq> 0\<close> \<open>p dvd a\<close> \<open>prime p\<close> by blast
      qed
      from 1 2 have "p \<in> {p. p \<in># prime_factorization a \<and> \<not> p dvd N}" by blast
    }
    then show "prime_factors (a * N) - prime_factors N
               \<subseteq> {p. p \<in># prime_factorization a \<and> \<not> p dvd N}" by blast
  qed
qed

lemma coprime_iff_prime_factors_disjoint:
  fixes x y :: "'a :: factorial_semiring"
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows "coprime x y \<longleftrightarrow> prime_factors x \<inter> prime_factors y = {}"
proof 
  assume "coprime x y"
  have False if "p \<in> prime_factors x" "p \<in> prime_factors y" for p
  proof -
    from that assms have "p dvd x" "p dvd y"
      by (auto simp: prime_factors_dvd)
    with \<open>coprime x y\<close> have "p dvd 1"
      using coprime_common_divisor by auto
    with that assms show False by (auto simp: prime_factors_dvd)
  qed
  thus "prime_factors x \<inter> prime_factors y = {}" by auto
next
  assume disjoint: "prime_factors x \<inter> prime_factors y = {}"
  show "coprime x y"
  proof (rule coprimeI)
    fix d assume d: "d dvd x" "d dvd y"
    show "is_unit d"
    proof (rule ccontr)
      assume "\<not>is_unit d"
      moreover from this and d assms have "d \<noteq> 0" by auto
      ultimately obtain p where p: "prime p" "p dvd d"
        using prime_divisor_exists by auto
      with d and assms have "p \<in> prime_factors x \<inter> prime_factors y"
        by (auto simp: prime_factors_dvd)
      with disjoint show False by auto
    qed
  qed
qed

lemma coprime_cong_prime_factors:
  fixes x y :: "'a :: factorial_semiring_gcd"
  assumes "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0"
  assumes "prime_factors x = prime_factors x'"
  assumes "prime_factors y = prime_factors y'"
  shows   "coprime x y \<longleftrightarrow> coprime x' y'"
  using assms by (simp add: coprime_iff_prime_factors_disjoint)

lemma moebius_prod_not_coprime:
  assumes "\<not> coprime N d"
  shows "moebius_mu (N*d) = 0"
proof -
  from assms obtain l where l_form: "l dvd N \<and> l dvd d \<and> \<not> is_unit l" 
    unfolding coprime_def by blast
  then have "l * l dvd N * d" using mult_dvd_mono by auto
  then have "l\<^sup>2 dvd N*d" by (subst power2_eq_square,blast) 
  then have "\<not> squarefree (N*d)" 
    unfolding squarefree_def coprime_def using l_form by blast
  then show "moebius_mu (N*d) = 0" 
    using moebius_mu_def by auto 
qed

text\<open>Theorem 2.18\<close>

(* TODO Place in corresponding theory *)
lemma sum_divisors_moebius_mu_times_multiplicative:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "multiplicative_function f" and "n > 0"
  shows   "(\<Sum>d | d dvd n. moebius_mu d * f d) = (\<Prod>p\<in>prime_factors n. 1 - f p)"
proof -
  define g where "g = (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d * f d)"
  define g' where "g' = dirichlet_prod (\<lambda>n. moebius_mu n * f n) (\<lambda>n. if n = 0 then 0 else 1)"
  interpret f: multiplicative_function f by fact
  have "multiplicative_function (\<lambda>n. if n = 0 then 0 else 1 :: 'a)"
    by standard auto
  interpret multiplicative_function g' unfolding g'_def
    by (intro multiplicative_dirichlet_prod multiplicative_function_mult
              moebius_mu.multiplicative_function_axioms assms) fact+

  have g'_primepow: "g' (p ^ k) = 1 - f p" if "prime p" "k > 0" for p k
  proof -
    have "g' (p ^ k) = (\<Sum>i\<le>k. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (simp add: g'_def dirichlet_prod_prime_power)
    also have "\<dots> = (\<Sum>i\<in>{0, 1}. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (intro sum.mono_neutral_right) (auto simp: moebius_mu_power')
    also have "\<dots> = 1 - f p"
      using that by (simp add: moebius_mu.prime)
    finally show ?thesis .
  qed

  have "g' n = g n"
    by (simp add: g_def g'_def dirichlet_prod_def)
  also from assms have "g' n = (\<Prod>p\<in>prime_factors n. g' (p ^ multiplicity p n))"
   by (intro prod_prime_factors) auto
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 1 - f p)"
    by (intro prod.cong) (auto simp: g'_primepow prime_factors_multiplicity)
  finally show ?thesis by (simp add: g_def)
qed

lemma multiplicative_ind_coprime [intro]: "multiplicative_function (ind (coprime N))"
  by (intro multiplicative_function_ind) auto

lemma sum_divisors_moebius_mu_times_multiplicative_revisited:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "multiplicative_function f" "n > 0" "N > 0"
  shows   "(\<Sum>d | d dvd n \<and> coprime N d. moebius_mu d * f d) =
           (\<Prod>p\<in>{p. p \<in> prime_factors n \<and> \<not> (p dvd N)}. 1 - f p)"
proof -
  have "(\<Sum>d | d dvd n \<and> coprime N d. moebius_mu d * f d) =
          (\<Sum>d | d dvd n. moebius_mu d * (ind (coprime N) d * f d))"
    using assms by (intro sum.mono_neutral_cong_left) (auto simp: ind_def)
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 1 - ind (coprime N) p * f p)"
    using assms by (intro sum_divisors_moebius_mu_times_multiplicative)
                   (auto intro: multiplicative_function_mult)
  also from assms have "\<dots> = (\<Prod>p | p \<in> prime_factors n \<and> \<not>(p dvd N). 1 - f p)"
    by (intro prod.mono_neutral_cong_right)
       (auto simp: ind_def prime_factors_dvd coprime_commute dest: prime_imp_coprime)
  finally show ?thesis .
qed

subsection \<open>Neutral element of the Dirichlet product\<close>

definition "dirichlet_prod_neutral n = (if n = 1 then 1 else 0)" for n :: nat

lemma dirichlet_prod_neutral_intro: 
  fixes S :: "nat \<Rightarrow> complex" and f :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  defines "S \<equiv> (\<lambda>(n::nat). (\<Sum>k | k \<in> {1..n} \<and> coprime k n. (f k n)))" 
  shows "S(n) = (\<Sum>k \<in> {1..n}. f k n * dirichlet_prod_neutral (gcd k n))"
proof -
  let ?g = "\<lambda>k. (f k n)* (dirichlet_prod_neutral (gcd k n))"
  have zeros: "\<forall>k \<in> {1..n} - {k. k \<in> {1..n} \<and> coprime k n}. ?g k = 0"
  proof
    fix k 
    assume "k \<in> {1..n} - {k \<in> {1..n}. coprime k n}"
    then show "(f k n) * dirichlet_prod_neutral (gcd k n) = 0" 
      by (simp add: dirichlet_prod_neutral_def[of "gcd k n"] split: if_splits,presburger) 
  qed
  
  have "S n = (\<Sum>k | k \<in> {1..n} \<and> coprime k n. (f k n))"
    by (simp add: S_def)
  also have "\<dots> = sum ?g {k. k \<in> {1..n} \<and> coprime k n}"
    by (simp add: dirichlet_prod_neutral_def split: if_splits)    
  also have "\<dots> = sum ?g {1..n}"
    by (intro sum.mono_neutral_left, auto simp add: zeros)
  finally show ?thesis by blast 
qed

lemma dirichlet_prod_neutral_right_neutral:
 "dirichlet_prod f dirichlet_prod_neutral n = f n " if "n > 0" for f :: "nat \<Rightarrow> complex" and n 
proof -
  {fix d :: nat
    assume "d dvd n"
    then have eq: "n = d \<longleftrightarrow> n div d = 1"
      using div_self that dvd_mult_div_cancel by force
    have "f(d)*dirichlet_prod_neutral(n div d) = (if n = d then f(d) else 0)" 
      by (simp add: dirichlet_prod_neutral_def eq)}
  note summand = this

  have "dirichlet_prod f dirichlet_prod_neutral n = 
          (\<Sum>d | d dvd n. f(d)*dirichlet_prod_neutral(n div d))"
    unfolding dirichlet_prod_def by blast
  also have "\<dots> = (\<Sum>d | d dvd n. (if n = d then f(d) else 0))"
    using summand by simp
  also have "\<dots> = (\<Sum>d | d = n. (if n = d then f(d) else 0))"
    using that by (intro sum.mono_neutral_right, auto)
  also have "\<dots> = f(n)"  by simp
  finally show ?thesis by simp 
qed

lemma dirichlet_prod_neutral_left_neutral:
 "dirichlet_prod dirichlet_prod_neutral f n = f n " 
 if "n > 0" for f :: "nat \<Rightarrow> complex" and n
  using dirichlet_prod_neutral_right_neutral[OF that, of f] 
        dirichlet_prod_commutes[of f dirichlet_prod_neutral]
  by argo

corollary I_right_neutral_0:
  fixes f :: "nat \<Rightarrow> complex" 
  assumes "f 0 = 0"
  shows "dirichlet_prod f dirichlet_prod_neutral n = f n"
  using assms dirichlet_prod_neutral_right_neutral by (cases n, simp, blast)

subsection \<open>Multiplicative functions\<close>

lemma mult_id: "multiplicative_function id" 
  by (simp add: multiplicative_function_def)

lemma mult_moebius: "multiplicative_function moebius_mu"
  using Moebius_Mu.moebius_mu.multiplicative_function_axioms
  by simp

lemma mult_of_nat: "multiplicative_function of_nat" 
  using multiplicative_function_def of_nat_0 of_nat_1 of_nat_mult by blast

lemma mult_of_nat_c: "completely_multiplicative_function of_nat" 
  by (simp add: completely_multiplicative_function_def)

lemma completely_multiplicative_nonzero:
  fixes f :: "nat \<Rightarrow> complex"
  assumes "completely_multiplicative_function f" 
          "d \<noteq> 0"
          "\<And>p. prime p \<Longrightarrow> f(p) \<noteq> 0" 
  shows "f(d) \<noteq> 0"
  using assms(2)
proof (induction d rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof (cases "n = 1")
    case True
    then show ?thesis 
      using assms(1)
      unfolding completely_multiplicative_function_def by simp
  next
    case False
    then obtain p where 2:"prime p \<and> p dvd n" 
      using prime_factor_nat by blast
    then obtain a where 3: "n = p * a"  "a \<noteq> 0" 
      using 1 by auto
    then have 4: "f(a) \<noteq> 0" using 1 
      using 2 prime_nat_iff by fastforce
    have 5: "f(p) \<noteq> 0" using assms(3) 2 by simp
    from 3 4 5 show ?thesis
      by (simp add: assms(1) completely_multiplicative_function.mult)
  qed
qed

lemma multipl_div: 
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "multiplicative_function f" "d1 dvd m" "d2 dvd k" "coprime m k"
  shows "f ((m*k) div (d1*d2)) = f(m div d1) * f(k div d2)"
  using assms
  unfolding multiplicative_function_def
  using assms(1) multiplicative_function.mult_coprime by fastforce

lemma multipl_div_mono: 
  fixes m k d :: nat and f :: "nat \<Rightarrow> complex"
  assumes "completely_multiplicative_function f" 
          "d dvd k" "d > 0" 
          "\<And>p. prime p \<Longrightarrow> f(p) \<noteq> 0" 
  shows "f (k div d) = f(k) div f(d)"
proof -
  have "d \<noteq> 0" using assms(2,3) by auto
  then have nz: "f(d) \<noteq> 0" using assms(1,4) completely_multiplicative_nonzero by simp

  from assms(2,3) obtain a where div: "k = a * d " by fastforce
  have "f (k div d) = f ((a*d) div d)" using div by simp
  also have "\<dots> = f(a)" using assms(3) div by simp
  also have "\<dots> = f(a)*f(d) div f(d)" using nz by auto
  also have "\<dots> = f(a*d) div f(d)" 
    by (simp add: div assms(1) completely_multiplicative_function.mult)
  also have "\<dots> = f (k) div f(d)" using div by simp
  finally show ?thesis by simp
qed

lemma comp_to_mult: "completely_multiplicative_function f \<Longrightarrow>
       multiplicative_function f"
  unfolding completely_multiplicative_function_def
            multiplicative_function_def by auto

end