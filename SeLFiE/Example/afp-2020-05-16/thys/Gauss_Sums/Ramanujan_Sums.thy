(*
  File:     Ramanujan_Sums.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  Ramanujan sums and generalised Ramanujan sums
*)
section \<open>Ramanujan sums\<close>
theory Ramanujan_Sums
imports
  Dirichlet_Series.Moebius_Mu
  Gauss_Sums_Auxiliary
  Finite_Fourier_Series
begin

subsection \<open>Basic sums\<close>

definition ramanujan_sum :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  where "ramanujan_sum k n = (\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m*n))"

notation ramanujan_sum ("c")

lemma ramanujan_sum_0_n [simp]: "c 0 n = 0"
  unfolding ramanujan_sum_def by simp

lemma sum_coprime_conv_dirichlet_prod_moebius_mu:
  fixes F S :: "nat \<Rightarrow> complex" and f :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  defines "F \<equiv> (\<lambda>n. (\<Sum>k \<in> {1..n}. f k n))"
  defines "S \<equiv> (\<lambda>n. (\<Sum>k | k \<in> {1..n} \<and> coprime k n . f k n))"
  assumes "\<And>a b d. d dvd a \<Longrightarrow> d dvd b \<Longrightarrow> f (a div d) (b div d) = f a b" 
  shows "S n = dirichlet_prod moebius_mu F n"
proof (cases "n = 0")
  case True
  then show ?thesis 
    using assms(2) unfolding dirichlet_prod_def by fastforce
next
  case False
  have "S(n) = (\<Sum>k | k \<in> {1..n} \<and> coprime k n . (f k n))"
    using assms by blast
  also have "\<dots> = (\<Sum>k \<in> {1..n}. (f k n)* dirichlet_prod_neutral (gcd k n))"
    using dirichlet_prod_neutral_intro by blast
  also have "\<dots> = (\<Sum>k \<in> {1..n}. (f k n)* (\<Sum>d | d dvd (gcd k n). moebius_mu d))"
  proof -
    {
      fix k
      have "dirichlet_prod_neutral (gcd k n) = (if gcd k n = 1 then 1 else 0)"
        using dirichlet_prod_neutral_def[of "gcd k n"] by blast
      also have "\<dots> = (\<Sum>d | d dvd gcd k n. moebius_mu d)"
        using sum_moebius_mu_divisors'[of "gcd k n"] by auto
      finally have "dirichlet_prod_neutral (gcd k n) = (\<Sum>d | d dvd gcd k n. moebius_mu d)" 
        by auto
    } note summand = this
    then show ?thesis by (simp add: summand)
  qed
  also have "\<dots> = (\<Sum>k = 1..n. (\<Sum>d | d dvd gcd k n. (f k n) *  moebius_mu d))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>k = 1..n. (\<Sum>d | d dvd gcd n k. (f k n) *  moebius_mu d))"
    using gcd.commute[of _ n] by simp
  also have "\<dots> = (\<Sum>d | d dvd n. \<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n) * moebius_mu d)"
    using sum.swap_restrict[of "{1..n}" "{d. d dvd n}"
             "\<lambda>k d. (f k n)*moebius_mu d" "\<lambda>k d. d dvd k"] False by auto
  also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * (\<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n)))" 
    by (simp add: sum_distrib_left mult.commute)
  also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * (\<Sum>q \<in> {1..n div d}. (f q (n div d))))"
  proof - 
    have st: "
      (\<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n)) =
        (\<Sum>q \<in> {1..n div d}. (f q (n div d)))" 
      if "d dvd n" "d > 0" for d :: nat
      by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k * d" "\<lambda>k. k div d"])
         (use assms(3) that in \<open>fastforce simp: div_le_mono\<close>)+
    show ?thesis 
      by (intro sum.cong) (use st False in fastforce)+
  qed
  also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * F(n div d))"
  proof - 
    have "F (n div d) = (\<Sum>q \<in> {1..n div d}. (f q (n div d)))" 
      if "d dvd n" for d
        by (simp add: F_def real_of_nat_div that)
     then show ?thesis by auto
  qed
  also have "\<dots> = dirichlet_prod moebius_mu F n"
    by (simp add: dirichlet_prod_def)
  finally show ?thesis by simp
qed

lemma dirichlet_prod_neutral_sum:
  "dirichlet_prod_neutral n = (\<Sum>k = 1..n. unity_root n k)" for n :: nat
proof (cases "n = 0")
  case True then show ?thesis unfolding dirichlet_prod_neutral_def by simp
next
  case False
  have 1: "unity_root n 0 = 1" by simp
  have 2: "unity_root n n = 1" 
    using unity_periodic_arithmetic[of n] add.left_neutral
  proof -
    have "1 = unity_root n (int 0)"
       using 1 by auto
    also have "unity_root n (int 0) = unity_root n (int (0 + n))"
      using unity_periodic_arithmetic[of n] periodic_arithmetic_def by algebra
    also have "\<dots> = unity_root n (int n)" by simp
    finally show ?thesis by auto 
  qed
  have "(\<Sum>k = 1..n. unity_root n k) = (\<Sum>k = 0..n. unity_root n k) - 1"
    by (simp add: sum.atLeast_Suc_atMost sum.atLeast0_atMost_Suc_shift 1)
  also have "\<dots> = ((\<Sum>k = 0..n-1. unity_root n k)+1) - 1"
    using sum.atLeast0_atMost_Suc[of "(\<lambda>k. unity_root n k)" "n-1"] False 
    by (simp add: 2)
  also have "\<dots> = (\<Sum>k = 0..n-1. unity_root n k)"
    by simp
  also have "\<dots> = unity_root_sum n 1"
    unfolding unity_root_sum_def using \<open>n \<noteq> 0\<close> by (intro sum.cong) auto
  also have "\<dots> = dirichlet_prod_neutral n"
    using unity_root_sum[of n 1] False
    by (cases "n = 1",auto simp add: False dirichlet_prod_neutral_def)
  finally have 3: "dirichlet_prod_neutral n = (\<Sum>k = 1..n. unity_root n k)" by auto
  then show ?thesis by blast 
qed

lemma moebius_coprime_sum:
  "moebius_mu n = (\<Sum>k | k \<in> {1..n} \<and> coprime k n . unity_root n (int k))"
proof -
  let ?f = "(\<lambda>k n. unity_root n k)"
  from div_dvd_div have " 
      d dvd a \<Longrightarrow> d dvd b \<Longrightarrow>
      unity_root (a div d) (b div d) = 
      unity_root a b" for a b d :: nat
    using unity_root_def real_of_nat_div by fastforce
  then have "(\<Sum>k | k \<in> {1..n} \<and> coprime k n. ?f k n) =
        dirichlet_prod moebius_mu (\<lambda>n. \<Sum>k = 1..n. ?f k n) n"
    using sum_coprime_conv_dirichlet_prod_moebius_mu[of ?f n] by blast
  also have "\<dots> = dirichlet_prod moebius_mu dirichlet_prod_neutral n"
    by (simp add: dirichlet_prod_neutral_sum)
  also have "\<dots> = moebius_mu n" 
    by (cases "n = 0") (simp_all add: dirichlet_prod_neutral_right_neutral)
  finally have "moebius_mu n = (\<Sum>k | k \<in> {1..n} \<and> coprime k n. ?f k n)"
    by argo
  then show ?thesis by blast
qed

corollary ramanujan_sum_1_right [simp]: "c k (Suc 0) = moebius_mu k"
  unfolding ramanujan_sum_def using moebius_coprime_sum[of k] by simp

lemma ramanujan_sum_dvd_eq_totient:
  assumes "k dvd n"
    shows "c k n = totient k"
  unfolding ramanujan_sum_def
proof - 
  have "unity_root k (m*n) = 1" for m
    using assms by (cases "k = 0") (auto simp: unity_root_eq_1_iff_int)
  then have "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m * n)) = 
               (\<Sum>m | m \<in> {1..k} \<and> coprime m k. 1)" by simp
  also have "\<dots> = card {m. m \<in> {1..k} \<and> coprime m k}" by simp
  also have "\<dots> = totient k"
   unfolding totient_def totatives_def 
  proof -
    have "{1..k} = {0<..k}" by auto
    then show " of_nat (card {m \<in> {1..k}. coprime m k}) =
              of_nat (card {ka \<in> {0<..k}. coprime ka k})" by auto
  qed
  finally show "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m * n)) = totient k" 
    by auto
qed

subsection \<open>Generalised sums\<close>

definition gen_ramanujan_sum :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "gen_ramanujan_sum f g = (\<lambda>k n. \<Sum>d | d dvd gcd n k. f d * g (k div d))"

notation gen_ramanujan_sum ("s")

lemma gen_ramanujan_sum_k_1: "s f g k 1 = f 1 * g k"
  unfolding gen_ramanujan_sum_def by auto

lemma gen_ramanujan_sum_1_n: "s f g 1 n = f 1 * g 1"
  unfolding gen_ramanujan_sum_def by simp

lemma gen_ramanujan_sum_periodic: "periodic_arithmetic (s f g k) k"
  unfolding gen_ramanujan_sum_def periodic_arithmetic_def by simp

text \<open>Theorem 8.5\<close>
theorem gen_ramanujan_sum_fourier_expansion:
  fixes f g :: "nat \<Rightarrow> complex" and a :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  assumes "k > 0" 
  defines "a \<equiv> (\<lambda>k m. (1/k) * (\<Sum>d| d dvd (gcd m k). g d * f (k div d) * d))"
  shows "s f g k n = (\<Sum>m\<le>k-1. a k m * unity_root k (m*n))"
proof -
  let ?g = "(\<lambda>x. 1 / of_nat k * (\<Sum>m<k. s f g k m * unity_root k (-x*m)))"
  {fix m :: nat
  let ?h = "\<lambda>n d. f d * g (k div d) * unity_root k (- m * int n)"
  have "(\<Sum>l<k. s f g k l * unity_root k (-m*l)) =
               (\<Sum>l \<in> {0..k-1}. s f g k l * unity_root k (-m*l))"
    using \<open>k > 0\<close> by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>l \<in> {1..k}. s f g k l * unity_root k (-m*l))"
  proof -
    have "periodic_arithmetic (\<lambda>l. unity_root k (-m*l)) k"
      using unity_periodic_arithmetic_mult by blast
    then have "periodic_arithmetic (\<lambda>l. s f g k l * unity_root k (-m*l)) k"
      using gen_ramanujan_sum_periodic mult_periodic_arithmetic by blast
    from this periodic_arithmetic_sum_periodic_arithmetic_shift[of _ k 1  ]
    have "sum (\<lambda>l. s f g k l * unity_root k (-m*l)) {0..k - 1} = 
          sum (\<lambda>l. s f g k l * unity_root k (-m*l)) {1..k}"
      using assms(1) zero_less_one by simp
    then show ?thesis by argo
  qed
  also have "\<dots> = (\<Sum>n\<in>{1..k}. (\<Sum>d | d dvd (gcd n k). f(d) * g(k div d)) * unity_root k (-m*n))"
    by (simp add: gen_ramanujan_sum_def)
  also have "\<dots> = (\<Sum>n\<in>{1..k}. (\<Sum>d | d dvd (gcd n k). f(d) * g(k div d) * unity_root k (-m*n)))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)"
  proof -
    have "(\<Sum>n = 1..k. \<Sum>d | d dvd gcd n k. ?h n d) =
          (\<Sum>n = 1..k. \<Sum>d | d dvd k \<and> d dvd n . ?h n d)"
      using gcd.commute[of _ k] by simp
    also have "\<dots> = (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)"
      using sum.swap_restrict[of "{1..k}" "{d. d dvd k}"
                            _ "\<lambda>n d. d dvd n"] assms by fastforce
    finally have "
      (\<Sum>n = 1..k. \<Sum>d | d dvd gcd n k. ?h n d) = 
      (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)" by blast
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>n | n \<in> {1..k} \<and> d dvd n. unity_root k (- m * int n)))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>e \<in> {1..k div d}. unity_root k (- m * (e*d))))"
    using assms(1) sum_div_reduce div_greater_zero_iff dvd_div_gt0 by auto
  also have "\<dots> = (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>e \<in> {1..k div d}. unity_root (k div d) (- m * e)))"
  proof -
    {
      fix d e
      assume "d dvd k"
      hence "2 * pi * real_of_int (- int m * int (e * d)) / real k =
              2 * pi * real_of_int (- int m * int e) / real (k div d)" by auto
      hence "unity_root k (- m * (e * d)) = unity_root (k div d) (- m * e)"
        unfolding unity_root_def by simp
    }
    then show ?thesis by simp
  qed
  also have "\<dots> = dirichlet_prod (\<lambda>d. f(d)*g(k div d))
                    (\<lambda>d. (\<Sum>e \<in> {1..d}. unity_root d (- m * e))) k"
    unfolding dirichlet_prod_def by blast
  also have "\<dots> = dirichlet_prod (\<lambda>d. (\<Sum>e \<in> {1..d}. unity_root d (- m * e)))
                    (\<lambda>d. f(d)*g(k div d)) k"
    using dirichlet_prod_commutes[of 
            "(\<lambda>d. f(d)*g(k div d))"
            "(\<lambda>d. (\<Sum>e \<in> {1..d}. unity_root d (- m * e)))"] by argo
  also have "\<dots> = (\<Sum>d | d dvd k.
             (\<Sum>e \<in> {1..(d::nat)}. unity_root d (- m * e))*(f(k div d)*g(k div (k div d))))"  
    unfolding dirichlet_prod_def by blast 
  also have "\<dots> = (\<Sum>d | d dvd k. (\<Sum>e \<in> {1..(d::nat)}.
                      unity_root d (- m * e))*(f(k div d)*g(d)))"  
  proof -
    {
      fix d :: nat
      assume "d dvd k"
      then have "k div (k div d) = d"
        by (simp add: assms(1) div_div_eq_right)
    }
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>(d::nat) | d dvd k \<and> d dvd m. d*(f(k div d)*g(d)))"  
  proof -
    {
      fix d
      assume "d dvd k"
      with assms have "d > 0" by (intro Nat.gr0I) auto
      have "periodic_arithmetic (\<lambda>x. unity_root d (- m * int x)) d"
        using unity_periodic_arithmetic_mult by blast
      then have "(\<Sum>e \<in> {1..d}. unity_root d (- m * e)) = 
            (\<Sum>e \<in> {0..d-1}. unity_root d (- m * e))"
        using periodic_arithmetic_sum_periodic_arithmetic_shift[of "\<lambda>e. unity_root d (- m * e)"  d 1] assms \<open>d dvd k\<close>
        by fastforce
      also have "\<dots> = unity_root_sum d (-m)" 
        unfolding unity_root_sum_def using \<open>d > 0\<close> by (intro sum.cong) auto
      finally have 
        "(\<Sum>e \<in> {1..d}. unity_root d (- m * e)) = unity_root_sum d (-m)"
        by argo
    }
    then have "
      (\<Sum>d | d dvd k. (\<Sum>e = 1..d. unity_root d (- m * int e)) * (f (k div d) * g d)) = 
      (\<Sum>d | d dvd k. unity_root_sum d (-m) * (f (k div d) * g d))" by simp
    also have "\<dots> = (\<Sum>d | d dvd k \<and> d dvd m. unity_root_sum d (-m) * (f (k div d) * g d))"
    proof (intro sum.mono_neutral_right,simp add: \<open>k > 0\<close>,blast,standard)
      fix i
      assume as: "i \<in> {d. d dvd k} - {d. d dvd k \<and> d dvd m}"
      then have "i \<ge> 1" using \<open>k > 0\<close> by auto
      have "k \<ge> 1" using \<open>k > 0\<close> by auto  
      have "\<not> i dvd (-m)" using as by auto
      thus "unity_root_sum i (- int m) * (f (k div i) * g i) = 0" 
        using \<open>i \<ge> 1\<close> by (subst unity_root_sum(2)) auto
    qed   
    also have "\<dots> = (\<Sum>d | d dvd k \<and> d dvd m. d * (f (k div d) * g d))"
    proof - 
      {fix d :: nat
        assume 1: "d dvd m" 
        assume 2: "d dvd k"
        then have "unity_root_sum d (-m) = d"
          using unity_root_sum[of d "(-m)"] assms(1) 1 2
          by auto}
      then show ?thesis by auto
    qed
    finally show ?thesis by argo
  qed
  also have "\<dots> = (\<Sum>d | d dvd gcd m k. of_nat d * (f (k div d) * g d))" 
    by (simp add: gcd.commute)
  also have "\<dots> = (\<Sum>d | d dvd gcd m k. g d * f (k div d) * d)" 
    by (simp add: algebra_simps sum_distrib_left)
  also have "1 / k * \<dots> = a k m" using a_def by auto
  finally have "?g m = a k m" by simp}
  note a_eq_g = this
  {
    fix m
    from fourier_expansion_periodic_arithmetic(2)[of k "s f g k" ] gen_ramanujan_sum_periodic assms(1) 
    have "s f g k m = (\<Sum>n<k. ?g n * unity_root k (int m * n))"
      by blast
    also have "\<dots> = (\<Sum>n<k. a k n * unity_root k (int m * n))"
      using a_eq_g by simp
    also have "\<dots> = (\<Sum>n\<le>k-1. a k n * unity_root k (int m * n))"
      using \<open>k > 0\<close> by (intro sum.cong) auto
    finally have "s f g k m =
      (\<Sum>n\<le>k - 1. a k n * unity_root k (int n * int m))"
      by (simp add: algebra_simps)
  }
  then show ?thesis by blast
qed

text \<open>Theorem 8.6\<close>
theorem ramanujan_sum_dirichlet_form:
  fixes k n :: nat
  assumes "k > 0"
  shows "c k n = (\<Sum>d | d dvd gcd n k. d * moebius_mu (k div d))"
proof -
  define a :: "nat \<Rightarrow> nat \<Rightarrow> complex" 
    where "a  =  (\<lambda>k m.
   1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat (k div d) * of_nat d))"

  {fix m
  have "a k m = (if gcd m k = 1 then 1 else 0)"
  proof -
   have "a k m = 1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat (k div d) * of_nat d)"
      unfolding a_def by blast
   also have 2: "\<dots> = 1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat k)"
   proof -
     {fix d :: nat
     assume dvd: "d dvd gcd m k"
     have "moebius_mu d * of_nat (k div d) * of_nat d = moebius_mu d * of_nat k"
     proof -
       have "(k div d) * d = k" using dvd by auto
       then show "moebius_mu d * of_nat (k div d) * of_nat d = moebius_mu d * of_nat k"  
         by (simp add: algebra_simps,subst of_nat_mult[symmetric],simp)
     qed} note eq = this
     show ?thesis using sum.cong by (simp add: eq)
   qed

   also have 3: "\<dots> = (\<Sum>d | d dvd gcd m k. moebius_mu d)"
     by (simp add: sum_distrib_left assms) 
   also have 4: "\<dots> =  (if gcd m k = 1 then 1 else 0)"
     using sum_moebius_mu_divisors' by blast
   finally show "a k m  = (if gcd m k = 1 then 1 else 0)" 
     using coprime_def by blast
 qed} note a_expr = this

  let ?f = "(\<lambda>m. (if gcd m k = 1 then 1 else 0) *
                 unity_root k (int m * n))"
  from gen_ramanujan_sum_fourier_expansion[of k id moebius_mu n] assms
  have "s (\<lambda>x. of_nat (id x)) moebius_mu k n =
  (\<Sum>m\<le>k - 1.
      1 / of_nat k *
      (\<Sum>d | d dvd gcd m k.
         moebius_mu d * of_nat (k div d) * of_nat d) *
      unity_root k (int m * n))" by simp
  also have "\<dots> = (\<Sum>m\<le>k - 1.
      a k m *
      unity_root k (int m * n))" using a_def by blast
  also have "\<dots> = (\<Sum>m\<le>k - 1.
      (if gcd m k = 1 then 1 else 0) *
      unity_root k (int m * n))" using a_expr by auto
  also have "\<dots> = (\<Sum>m \<in> {1..k}.
      (if gcd m k = 1 then 1 else 0) *
      unity_root k (int m * n))"
  proof -    
    have "periodic_arithmetic (\<lambda>m. (if gcd m k = 1 then 1 else 0) *
                 unity_root k (int m * n)) k"
    proof -
      have "periodic_arithmetic (\<lambda>m. if gcd m k = 1 then 1 else 0) k"
        by (simp add: periodic_arithmetic_def)
      moreover have "periodic_arithmetic (\<lambda>m. unity_root k (int m * n)) k" 
        using unity_periodic_arithmetic_mult[of k n]
        by (subst mult.commute,simp) 
      ultimately show "periodic_arithmetic ?f k"
        using mult_periodic_arithmetic by simp
    qed
    then have "sum ?f {0..k - 1} = sum ?f {1..k}"
      using periodic_arithmetic_sum_periodic_arithmetic_shift[of ?f k 1] by force
    then show ?thesis by (simp add: atMost_atLeast0)    
  qed  
  also have "\<dots> = (\<Sum>m | m \<in> {1..k} \<and> gcd m k = 1.
                  (if gcd m k = 1 then 1 else 0) *     
                  unity_root k (int m * int n))"
    by (intro sum.mono_neutral_right,auto)
  also have "\<dots> = (\<Sum>m | m \<in> {1..k} \<and> gcd m k = 1.
                  unity_root k (int m * int n))" by simp    
  also have "\<dots> = (\<Sum>m | m \<in> {1..k} \<and> coprime m k.
                  unity_root k (int m * int n))"
    using coprime_iff_gcd_eq_1 by presburger
  also have "\<dots> = c k n" unfolding ramanujan_sum_def by simp
  finally show ?thesis unfolding gen_ramanujan_sum_def by auto
qed

corollary ramanujan_sum_conv_gen_ramanujan_sum:
 "k > 0 \<Longrightarrow> c k n = s id moebius_mu k n"
  using ramanujan_sum_dirichlet_form unfolding gen_ramanujan_sum_def by simp

text \<open>Theorem 8.7\<close>
theorem gen_ramanujan_sum_distrib:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "a > 0" "b > 0" "m > 0" "k > 0" (* remove cond. on m,n *)
  assumes "coprime a k" "coprime b m" "coprime k m"
  assumes "multiplicative_function f" and 
          "multiplicative_function g"
  shows "s f g (m*k) (a*b) = s f g m a * s f g k b"
proof -
  from assms(1-6) have eq: "gcd (m*k) (a*b) = gcd a m * gcd k b"
   by (simp add: linear_gcd  gcd.commute mult.commute)
  have "s f g (m*k) (a*b) = 
        (\<Sum>d | d dvd gcd (m*k) (a*b). f(d) * g((m*k) div d))"
    unfolding gen_ramanujan_sum_def by (rule sum.cong, simp add: gcd.commute,blast) 
  also have "\<dots> = 
     (\<Sum>d | d dvd gcd a m * gcd k b. f(d) * g((m*k) div d))"
    using eq by simp
  also have "\<dots> = 
     (\<Sum>(d1,d2) | d1 dvd gcd a m \<and>  d2 dvd gcd k b. 
          f(d1*d2) * g((m*k) div (d1*d2)))" 
  proof -
    have b: "bij_betw (\<lambda>(d1, d2). d1 * d2)
   {(d1, d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}
   {d. d dvd gcd a m * gcd k b}" 
      using assms(5) reindex_product_bij by blast
    have "(\<Sum>(d1, d2) | d1 dvd gcd a m \<and> d2 dvd gcd k b.
     f (d1 * d2) * g (m * k div (d1 * d2))) = 
      (\<Sum>x\<in>{(d1, d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}.
     f (case x of (d1, d2) \<Rightarrow> d1 * d2)*
       g (m * k div (case x of (d1, d2) \<Rightarrow> d1 * d2)))"
        by (rule sum.cong,auto)
      also have "\<dots> = (\<Sum>d | d dvd gcd a m * gcd k b. f d * g (m * k div d))"
        using b by (rule sum.reindex_bij_betw[of "\<lambda>(d1,d2). d1*d2" ])
      finally show ?thesis by argo     
    qed 
  also have "\<dots> = (\<Sum>d1 | d1 dvd gcd a m. \<Sum>d2 | d2 dvd gcd k b. 
                     f (d1*d2) * g ((m*k) div (d1*d2)))"
      by (simp add: sum.cartesian_product) (rule sum.cong,auto) 
    also have "\<dots> = (\<Sum>d1 | d1 dvd gcd a m. \<Sum>d2 | d2 dvd gcd k b. 
                      f d1 * f d2 * g ((m*k) div (d1*d2)))"
      using assms(5) assms(8) multiplicative_function.mult_coprime
      by (intro sum.cong refl) fastforce+
    also have "\<dots> = (\<Sum>d1 | d1 dvd gcd a m. \<Sum>d2 | d2 dvd gcd k b.
                      f d1 * f d2* g (m div d1) * g (k div d2))"
    proof (intro sum.cong refl, clarify, goal_cases)
      case (1 d1 d2)
      hence "g (m * k div (d1 * d2)) = g (m div d1) * g (k div d2)" 
        using assms(7,9) multipl_div
        by (meson coprime_commute dvd_gcdD1 dvd_gcdD2)
      thus ?case by simp
    qed
    also have "\<dots> = (\<Sum>i\<in>{d1. d1 dvd gcd a m}. \<Sum>j\<in>{d2. d2 dvd gcd k b}.
                      f i * g (m div i) * (f j * g (k div j)))"
      by (rule sum.cong,blast,rule sum.cong,blast,simp)   
    also have "\<dots> = (\<Sum>d1 | d1 dvd gcd a m. f d1 * g (m div d1)) *
                      (\<Sum>d2 | d2 dvd gcd k b. f d2 * g (k div d2))"
      by (simp add: sum_product)
    also have "\<dots> = s f g m a * s f g k b"
      unfolding gen_ramanujan_sum_def by (simp add: gcd.commute)
    finally show ?thesis by blast
qed

corollary gen_ramanujan_sum_distrib_right:
 fixes f g :: "nat \<Rightarrow> complex"
 assumes "a > 0" and "b > 0" and "m > 0" (* TODO: remove cond. on m,n *)
 assumes "coprime b m"
 assumes "multiplicative_function f" and 
         "multiplicative_function g"
 shows "s f g m (a * b) = s f g m a"
proof -
  have "s f g m (a*b) = s f g m a * s f g 1 b"
    using assms gen_ramanujan_sum_distrib[of a b m 1 f g] by simp
  also have "\<dots> = s f g m a * f 1 * g 1"
    using gen_ramanujan_sum_1_n by auto
  also have "\<dots> = s f g m a"
    using  assms(5-6) 
    by (simp add: multiplicative_function_def)
  finally show "s f g m (a*b) = s f g m a" by blast
qed

corollary gen_ramanujan_sum_distrib_left:
 fixes f g :: "nat \<Rightarrow> complex"
 assumes "a > 0" and "k > 0" and "m > 0" (* TODO: remove cond. on m,n *)
 assumes "coprime a k" and "coprime k m"
 assumes "multiplicative_function f" and 
         "multiplicative_function g"
 shows "s f g (m*k) a = s f g m a * g k"
proof -
  have "s f g (m*k) a = s f g m a * s f g k 1"
    using assms gen_ramanujan_sum_distrib[of a 1 m k f g] by simp
  also have "\<dots> = s f g m a * f(1) * g(k)" 
    using gen_ramanujan_sum_k_1 by auto
  also have "\<dots> = s f g m a *  g k" 
    using assms(6)
    by (simp add: multiplicative_function_def)
  finally show ?thesis by blast
qed

corollary ramanujan_sum_distrib:
 assumes "a > 0" and "k > 0" and "m > 0" and "b > 0" (* TODO: remove cond. on m,n *)
 assumes "coprime a k" "coprime b m" "coprime m k"
 shows "c (m*k) (a*b) = c m a * c k b"
proof -
  have "c (m*k) (a*b) = s id moebius_mu (m*k) (a*b)" 
    using ramanujan_sum_conv_gen_ramanujan_sum assms(2,3) by simp
  
  also have "\<dots> = (s id moebius_mu m a) * (s id moebius_mu k b)"
    using gen_ramanujan_sum_distrib[of a b m k id moebius_mu]
          assms mult_id mult_moebius mult_of_nat         
          coprime_commute[of m k] by auto
  also have "\<dots> = c m a * c k b" using ramanujan_sum_conv_gen_ramanujan_sum assms by simp
  finally show ?thesis by simp
qed

corollary ramanujan_sum_distrib_right:
 assumes "a > 0" and "k > 0" and "m > 0" and "b > 0" (* remove cond. on m,n *)
 assumes "coprime b m" 
 shows "c m (a*b) = c m a"
  using assms ramanujan_sum_conv_gen_ramanujan_sum mult_id mult_moebius 
        mult_of_nat gen_ramanujan_sum_distrib_right by auto

corollary ramanujan_sum_distrib_left:
 assumes "a > 0" "k > 0" "m > 0"  (* remove cond. on m,n *)
 assumes "coprime a k" "coprime m k" 
 shows "c (m*k) a = c m a * moebius_mu k"
  using assms
  by (simp add: ramanujan_sum_conv_gen_ramanujan_sum, subst gen_ramanujan_sum_distrib_left)
     (auto simp: coprime_commute mult_of_nat mult_moebius)

lemma dirichlet_prod_completely_multiplicative_left:
  fixes f h :: "nat \<Rightarrow> complex" and k :: nat
  defines "g \<equiv> (\<lambda>k. moebius_mu k * h k)" 
  defines "F \<equiv> dirichlet_prod f g"
  assumes "k > 0"
  assumes "completely_multiplicative_function f" 
          "multiplicative_function h" 
  assumes "\<And>p. prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)" 
  shows "F k = f k * (\<Prod>p\<in>prime_factors k. 1 - h p / f p)"
proof -
  have 1: "multiplicative_function (\<lambda>p. h(p) div f(p))"
    using multiplicative_function_divide
          comp_to_mult assms(4,5) by blast
  have "F k = dirichlet_prod g f k"
    unfolding F_def using dirichlet_prod_commutes[of f g] by auto
  also have "\<dots> = (\<Sum>d | d dvd k. moebius_mu d * h d * f(k div d))"
    unfolding g_def dirichlet_prod_def by blast
  also have "\<dots> = (\<Sum>d | d dvd k. moebius_mu d * h d * (f(k) div f(d)))"
    using multipl_div_mono[of f _ k] assms(4,6) 
    by (intro sum.cong,auto,force)  
  also have "\<dots> = f k * (\<Sum>d | d dvd k. moebius_mu d * (h d div f(d)))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = f k * (\<Prod>p\<in>prime_factors k. 1 - (h p div f p))"
    using sum_divisors_moebius_mu_times_multiplicative[of "\<lambda>p. h p div f p" k] 1
          assms(3) by simp
  finally show F_eq: "F k = f k * (\<Prod>p\<in>prime_factors k. 1 - (h p div f p))"
    by blast
qed

text \<open>Theorem 8.8\<close>
theorem gen_ramanujan_sum_dirichlet_expr:
  fixes f h :: "nat \<Rightarrow> complex" and n k :: nat
  defines "g \<equiv> (\<lambda>k. moebius_mu k * h k)" 
  defines "F \<equiv> dirichlet_prod f g"
  defines "N \<equiv> k div gcd n k" 
  assumes "completely_multiplicative_function f" 
          "multiplicative_function h" 
  assumes "\<And>p. prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)" 
  assumes "k > 0" "n > 0"  
  shows "s f g k n = (F(k)*g(N)) div (F(N))"
proof -
  define a where "a \<equiv> gcd n k" 
  have 2: "k = a*N" unfolding a_def N_def by auto
  have 3: "a > 0" using a_def assms(7,8) by simp
  have Ngr0: "N > 0" using assms(7,8) 2 N_def by fastforce
  have f_k_not_z: "f k \<noteq> 0" 
    using completely_multiplicative_nonzero assms(4,6,7) by blast
  have f_N_not_z: "f N \<noteq> 0" 
      using completely_multiplicative_nonzero assms(4,6) Ngr0 by blast
  have bij: "bij_betw (\<lambda>d. a div d) {d. d dvd a} {d. d dvd a}"
    unfolding bij_betw_def
  proof
    show inj: "inj_on (\<lambda>d. a div d) {d. d dvd a}"
      using inj_on_def "3" dvd_div_eq_2 by blast
    show surj: "(\<lambda>d. a div d) ` {d. d dvd a} = {d. d dvd a}"
      unfolding image_def 
    proof 
      show " {y. \<exists>x\<in>{d. d dvd a}. y = a div x} \<subseteq> {d. d dvd a}"
        by auto
      show "{d. d dvd a} \<subseteq> {y. \<exists>x\<in>{d. d dvd a}. y = a div x}"
      proof 
        fix d
        assume a: "d \<in> {d. d dvd a}"
        from a have 1: "(a div d) \<in> {d. d dvd a}" by auto
        from a have 2: "d = a div (a div d)" using 3 by auto
        from 1 2 show "d \<in> {y. \<exists>x\<in>{d. d dvd a}. y = a div x} " by blast        
      qed
    qed
  qed
  
  have "s f g k n = (\<Sum>d | d dvd a. f(d)*moebius_mu(k div d)*h(k div d))"
    unfolding gen_ramanujan_sum_def g_def a_def by (simp add: mult.assoc)
  also have "\<dots> = (\<Sum>d | d dvd a. f(d) * moebius_mu(a*N div d)*h(a*N div d))"
    using 2 by blast
  also have "\<dots> = (\<Sum>d | d dvd a. f(a div d) * moebius_mu(N*d)*h(N*d))"
    (is "?a = ?b")
  proof -
    define f_aux where "f_aux \<equiv> (\<lambda>d. f d * moebius_mu (a * N div d) * h (a * N div d))"
    have 1: "?a = (\<Sum>d | d dvd a. f_aux d)" using f_aux_def by blast
    {fix d :: nat
    assume "d dvd a"
    then have "N * a div (a div d) = N * d" 
      using 3 by force}
    then have 2: "?b = (\<Sum>d | d dvd a. f_aux (a div d))" 
      unfolding f_aux_def by (simp add: algebra_simps)
    show "?a = ?b" 
      using bij 1 2
      by (simp add: sum.reindex_bij_betw[of "((div) a)" "{d. d dvd a}" "{d. d dvd a}"])
  qed
  also have "\<dots> = moebius_mu N * h N * f a * (\<Sum>d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d))"
   (is "?a = ?b")
  proof -
    have "?a = (\<Sum>d | d dvd a \<and> coprime N d. f(a div d) * moebius_mu (N*d) * h (N*d))"
      by (rule sum.mono_neutral_right)(auto simp add: moebius_prod_not_coprime 3)
    also have "\<dots> = (\<Sum>d | d dvd a \<and> coprime N d. moebius_mu N * h N * f(a div d) * moebius_mu d * h d)"
    proof (rule sum.cong,simp)
      fix d
      assume a: "d \<in> {d. d dvd a \<and> coprime N d}"
      then have 1: "moebius_mu (N*d) = moebius_mu N * moebius_mu d"
        using mult_moebius unfolding multiplicative_function_def 
        by (simp add: moebius_mu.mult_coprime)
      from a have 2: "h (N*d) = h N * h d"
         using assms(5) unfolding multiplicative_function_def 
         by (simp add: assms(5) multiplicative_function.mult_coprime)
      show "f (a div d) * moebius_mu (N * d) * h (N * d) =
         moebius_mu N * h N * f (a div d) * moebius_mu d * h d"
       by (simp add: divide_simps 1 2)
    qed
    also have "\<dots> = (\<Sum>d | d dvd a \<and> coprime N d. moebius_mu N * h N * (f a div f d) * moebius_mu d * h d)"
      by (intro sum.cong refl) (use multipl_div_mono[of f _ a] assms(4,6-8) 3 in force)
    also have "\<dots> = moebius_mu N * h N * f a * (\<Sum>d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d))"
      by (simp add: sum_distrib_left algebra_simps)
    finally show ?thesis by blast
  qed
  also have "\<dots> =
           moebius_mu N * h N * f a * (\<Prod>p\<in>{p. p \<in> prime_factors a \<and> \<not> (p dvd N)}. 1 - (h p div f p))"
   proof -
     have "multiplicative_function (\<lambda>d. h d div f d)" 
       using multiplicative_function_divide 
             comp_to_mult 
             assms(4,5) by blast
     then have "(\<Sum>d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d)) =
    (\<Prod>p\<in>{p. p \<in> prime_factors a \<and> \<not> (p dvd N)}. 1 - (h p div f p))"
       using sum_divisors_moebius_mu_times_multiplicative_revisited[
         of "(\<lambda>d. h d div f d)" a N]         
           assms(8) Ngr0 3 by blast 
    then show ?thesis by argo
  qed    
  also have "\<dots> = f(a) * moebius_mu(N) * h(N) * 
     ((\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p)))"
  proof -
    have "{p. p \<in>prime_factors a \<and> \<not> p dvd N} = 
          ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
      using p_div_set[of a N] by blast
    then have eq2: "(\<Prod>p\<in>{p. p \<in>prime_factors a \<and> \<not> p dvd N}. 1 - h p / f p) = 
          prod (\<lambda>p. 1 - h p / f p) ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
      by auto
    also have eq: "\<dots> = prod (\<lambda>p. 1 - h p / f p) {p. p \<in>prime_factors (a*N)} div
                     prod (\<lambda>p. 1 - h p / f p) {p. p \<in>prime_factors N}"
    proof (intro prod_div_sub,simp,simp,simp add: "3" Ngr0 dvd_prime_factors,simp,standard)
      fix b
      assume "b \<in># prime_factorization N"
      then have p_b: "prime b" using in_prime_factors_iff by blast
      then show "f b = 0 \<or> h b \<noteq> f b" using assms(6)[OF p_b] by auto
    qed
    also have "\<dots> = (\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p))" by blast
    finally have "(\<Prod>p\<in>{p. p \<in>prime_factors a \<and> \<not> p dvd N}. 1 - h p / f p) = 
        (\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p))" 
      using eq eq2 by auto
    then show ?thesis by simp
  qed
  also have "\<dots> = f(a) * moebius_mu(N) * h(N) * (F(k) div f(k)) * (f(N) div F(N))"
   (is "?a = ?b")
  proof -
    have "F(N) = (f N) *(\<Prod>p\<in> prime_factors N. 1 - (h p div f p))"
      unfolding F_def g_def
      by (intro dirichlet_prod_completely_multiplicative_left) (auto simp add: Ngr0 assms(4-6))
    then have eq_1: "(\<Prod>p\<in> prime_factors N. 1 - (h p div f p)) = 
               F N div f N" using 2 f_N_not_z by simp
    have "F(k) = (f k) * (\<Prod>p\<in> prime_factors k. 1 - (h p div f p))"
      unfolding F_def g_def
      by (intro dirichlet_prod_completely_multiplicative_left) (auto simp add: assms(4-7))
    then have eq_2: "(\<Prod>p\<in> prime_factors k. 1 - (h p div f p)) = 
               F k div f k" using 2 f_k_not_z by simp

    have "?a = f a * moebius_mu N * h N * 
           ((\<Prod>p\<in> prime_factors k. 1 - (h p div f p)) div
           (\<Prod>p\<in> prime_factors N. 1 - (h p div f p)))"
      using 2 by (simp add: algebra_simps) 
    also have  "\<dots> = f a * moebius_mu N * h N * ((F k div f k) div (F N div f N))"
      by (simp add: eq_1 eq_2)
    finally show ?thesis by simp
  qed
  also have "\<dots> = moebius_mu N * h N * ((F k * f a * f N) div (F N * f k))"
    by (simp add: algebra_simps) 
  also have "\<dots> = moebius_mu N * h N * ((F k * f(a*N)) div (F N * f k))"
  proof -
    have "f a * f N = f (a*N)" 
    proof (cases "a = 1 \<or> N = 1")
      case True
      then show ?thesis  
        using assms(4) completely_multiplicative_function_def[of f] 
        by auto
    next
      case False
      then show ?thesis 
        using 2 assms(4) completely_multiplicative_function_def[of f] 
             Ngr0 3 by auto
    qed
    then show ?thesis by simp
  qed 
  also have "\<dots> = moebius_mu N * h N * ((F k * f(k)) div (F N * f k))"
    using 2 by blast
  also have "\<dots> = g(N) * (F k div F N)"
    using f_k_not_z g_def by simp
  also have "\<dots> = (F(k)*g(N)) div (F(N))" by auto
  finally show ?thesis by simp
qed

(*TODO remove this and substitute 
 the theorem totient_conv_moebius_mu in More_totient by 
 this version: int \<rightarrow> of_nat*)
lemma totient_conv_moebius_mu_of_nat:
  "of_nat (totient n) = dirichlet_prod moebius_mu of_nat n"
proof (cases "n = 0")
  case False
  show ?thesis
    by (rule moebius_inversion)
       (insert False, simp_all add: of_nat_sum [symmetric] totient_divisor_sum del: of_nat_sum)
qed simp_all

corollary ramanujan_sum_k_n_dirichlet_expr:
 fixes k n :: nat
 assumes "k > 0" "n > 0" 
 shows "c k n = of_nat (totient k) * 
                moebius_mu (k div gcd n k) div 
                of_nat (totient (k div gcd n k))" 
proof -
  define f :: "nat \<Rightarrow> complex" 
    where "f \<equiv> of_nat"
  define F :: "nat \<Rightarrow> complex"
    where "F \<equiv> (\<lambda>d. dirichlet_prod f moebius_mu d)"
  define g :: "nat \<Rightarrow> complex "
    where "g \<equiv> (\<lambda>l. moebius_mu l)" 
  define N where "N \<equiv> k div gcd n k" 
  define h :: "nat \<Rightarrow> complex"
    where "h \<equiv> (\<lambda>x. (if x = 0 then 0 else 1))" 
  
  have F_is_totient_k: "F k = totient k"
    by (simp add: F_def f_def dirichlet_prod_commutes totient_conv_moebius_mu_of_nat[of k])
  have F_is_totient_N: "F N = totient N"
    by (simp add: F_def f_def dirichlet_prod_commutes totient_conv_moebius_mu_of_nat[of N])

  have "c k n = s id moebius_mu k n"
    using ramanujan_sum_conv_gen_ramanujan_sum assms by blast
  also have "\<dots> =  s f g k n" 
    unfolding f_def g_def by auto
  also have "g = (\<lambda>k. moebius_mu k * h k)"
    by (simp add: fun_eq_iff h_def g_def)
  also have "multiplicative_function h"
    unfolding h_def by standard auto
  hence "s f (\<lambda>k. moebius_mu k * h k) k n =
           dirichlet_prod of_nat (\<lambda>k. moebius_mu k * h k) k *
           (moebius_mu (k div gcd n k) * h (k div gcd n k)) /
           dirichlet_prod of_nat (\<lambda>k. moebius_mu k * h k) (k div gcd n k)" 
    unfolding f_def using assms mult_of_nat_c
    by (intro gen_ramanujan_sum_dirichlet_expr) (auto simp: h_def)
  also have "\<dots> = of_nat (totient k) * moebius_mu (k div gcd n k) / of_nat (totient (k div gcd n k))"
    using F_is_totient_k F_is_totient_N by (auto simp: h_def F_def N_def f_def)
  finally show ?thesis .
qed

no_notation ramanujan_sum ("c")
no_notation gen_ramanujan_sum ("s")

end