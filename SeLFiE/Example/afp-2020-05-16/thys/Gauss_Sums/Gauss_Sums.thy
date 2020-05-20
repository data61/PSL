(*
  File:     Gauss_Sums.thy
  Authors:  Rodrigo Raya, EPFL; Manuel Eberl, TUM

  Gauss sums and more on Dirichlet characters: induced moduli, separability, primitive characters
*)
theory Gauss_Sums
imports 
  "HOL-Algebra.Coset"
  "HOL-Real_Asymp.Real_Asymp"
  Ramanujan_Sums
begin

section \<open>Gauss sums\<close>

bundle vec_lambda_notation
begin
notation vec_lambda (binder "\<chi>" 10)
end

bundle no_vec_lambda_notation
begin
no_notation vec_lambda (binder "\<chi>" 10)
end

unbundle no_vec_lambda_notation


subsection \<open>Definition and basic properties\<close>
context dcharacter
begin                            

(* TODO remove when integrating periodic and periodic_function *)
lemma dir_periodic_arithmetic: "periodic_arithmetic \<chi> n"
  unfolding periodic_arithmetic_def by (simp add: periodic)

definition "gauss_sum k = (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*k))"

lemma gauss_sum_periodic: 
  "periodic_arithmetic (\<lambda>n. gauss_sum n) n"
proof - 
  have "periodic_arithmetic \<chi> n" using dir_periodic_arithmetic by simp
  let ?h = "\<lambda>m k. \<chi>(m) * unity_root n (m*k)"
  {fix m :: nat
  have "periodic_arithmetic (\<lambda>k. unity_root n (m*k)) n"
    using unity_periodic_arithmetic_mult[of n m] by simp
  have "periodic_arithmetic (?h m) n" 
    using scalar_mult_periodic_arithmetic[OF \<open>periodic_arithmetic (\<lambda>k. unity_root n (m*k)) n\<close>]
    by blast}
  then have per_all: "\<forall>m \<in> {1..n}. periodic_arithmetic (?h m) n" by blast
  have "periodic_arithmetic (\<lambda>k. (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*k))) n" 
    using fin_sum_periodic_arithmetic_set[OF per_all] by blast
  then show ?thesis
    unfolding gauss_sum_def by blast
qed

lemma ramanujan_sum_conv_gauss_sum:
  assumes "\<chi> = principal_dchar n"
  shows "ramanujan_sum n k = gauss_sum k" 
proof -
  {fix m
  from assms  
    have 1: "coprime m n \<Longrightarrow> \<chi>(m) = 1" and
         2: "\<not> coprime m n \<Longrightarrow> \<chi>(m) = 0"  
      unfolding principal_dchar_def by auto}
  note eq = this

  have "gauss_sum k = (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*k))"
    unfolding gauss_sum_def by simp
  also have "\<dots> = (\<Sum>m | m \<in> {1..n} \<and> coprime m n . \<chi>(m) * unity_root n (m*k))"
    by (rule sum.mono_neutral_right,simp,blast,simp add: eq) 
  also have "\<dots> = (\<Sum>m | m \<in> {1..n} \<and> coprime m n . unity_root n (m*k))"
    by (simp add: eq)
  also have "\<dots> = ramanujan_sum n k" unfolding ramanujan_sum_def by blast
  finally show ?thesis ..
qed

lemma cnj_mult_self:
  assumes "coprime k n"
  shows "cnj (\<chi> k) * \<chi> k = 1"
proof -
  have "cnj (\<chi> k) * \<chi> k = norm (\<chi> k)^2"
    by (simp add: mult.commute complex_mult_cnj cmod_def)
  also have "\<dots> = 1" 
    using norm[of k] assms by simp
  finally show ?thesis .
qed

text \<open>Theorem 8.9\<close>
theorem gauss_sum_reduction:
  assumes "coprime k n" 
  shows "gauss_sum k = cnj (\<chi> k) * gauss_sum 1"
proof -
  from n have n_pos: "n > 0" by simp
  have "gauss_sum k = (\<Sum>r = 1..n . \<chi>(r) * unity_root n (r*k))"
    unfolding gauss_sum_def by simp
  also have "\<dots> = (\<Sum>r = 1..n . cnj (\<chi>(k)) * \<chi> k * \<chi> r * unity_root n (r*k))"
    using assms by (intro sum.cong) (auto simp: cnj_mult_self)
  also have "\<dots> = (\<Sum>r = 1..n . cnj (\<chi>(k)) * \<chi> (k*r) * unity_root n (r*k))"
    by (intro sum.cong) auto
  also have "\<dots> = cnj (\<chi>(k)) * (\<Sum>r = 1..n . \<chi> (k*r) * unity_root n (r*k))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots>= cnj (\<chi>(k)) * (\<Sum>r = 1..n . \<chi> r * unity_root n r)"
  proof -
    have 1: "periodic_arithmetic (\<lambda>r. \<chi> r * unity_root n r) n"
      using dir_periodic_arithmetic unity_periodic_arithmetic mult_periodic_arithmetic by blast
    have "(\<Sum>r = 1..n . \<chi> (k*r) * unity_root n (r*k)) = 
          (\<Sum>r = 1..n . \<chi> (r)* unity_root n r)"
      using periodic_arithmetic_remove_homothecy[OF assms(1) 1 n_pos]
      by (simp add: algebra_simps n)
    then show ?thesis by argo
  qed
  also have "\<dots> = cnj (\<chi>(k)) * gauss_sum 1" 
    using gauss_sum_def by simp
  finally show ?thesis .
qed


text \<open>
  The following variant takes an integer argument instead.
\<close>
definition "gauss_sum_int k = (\<Sum>m=1..n. \<chi> m * unity_root n (int m*k))"

sublocale gauss_sum_int: periodic_fun_simple gauss_sum_int "int n"
proof
  fix k
  show "gauss_sum_int (k + int n) = gauss_sum_int k"
    by (simp add: gauss_sum_int_def ring_distribs unity_root_add)
qed

lemma gauss_sum_int_cong:
  assumes "[a = b] (mod int n)"
  shows   "gauss_sum_int a = gauss_sum_int b"
proof -
  from assms obtain k where k: "b = a + int n * k"
    by (subst (asm) cong_iff_lin) auto
  thus ?thesis
    using gauss_sum_int.plus_of_int[of a k] by (auto simp: algebra_simps)
qed

lemma gauss_sum_conv_gauss_sum_int:
  "gauss_sum k = gauss_sum_int (int k)" 
  unfolding gauss_sum_def gauss_sum_int_def by auto

lemma gauss_sum_int_conv_gauss_sum:
  "gauss_sum_int k = gauss_sum (nat (k mod n))"
proof -
  have "gauss_sum (nat (k mod n)) = gauss_sum_int (int (nat (k mod n)))"
    by (simp add: gauss_sum_conv_gauss_sum_int)
  also have "\<dots> = gauss_sum_int k"
    using n
    by (intro gauss_sum_int_cong) (auto simp: cong_def)
  finally show ?thesis ..
qed

lemma gauss_int_periodic: "periodic_arithmetic gauss_sum_int n" 
  unfolding periodic_arithmetic_def gauss_sum_int_conv_gauss_sum by simp

proposition dcharacter_fourier_expansion:
  "\<chi> m = (\<Sum>k=1..n. 1 / n * gauss_sum_int (-k) * unity_root n (m*k))"
proof -
  define g where "g = (\<lambda>x. 1 / of_nat n *
      (\<Sum>m<n. \<chi> m * unity_root n (- int x * int m)))"
  have per: "periodic_arithmetic \<chi> n" using dir_periodic_arithmetic by simp
  have "\<chi> m = (\<Sum>k<n. g k * unity_root n (m * int k))"
    using fourier_expansion_periodic_arithmetic(2)[OF _ per, of m] n by (auto simp: g_def)
  also have "\<dots> = (\<Sum>k = 1..n. g k * unity_root n (m * int k))"
  proof -
    have g_per: "periodic_arithmetic g n"
      using fourier_expansion_periodic_arithmetic(1)[OF _ per] n by (simp add: g_def)
    have fact_per: "periodic_arithmetic (\<lambda>k. g k * unity_root n (int m * int k)) n"
      using mult_periodic_arithmetic[OF g_per] unity_periodic_arithmetic_mult by auto
    show ?thesis
    proof -
      have "(\<Sum>k<n. g k * unity_root n (int m * int k)) =
            (\<Sum>l = 0..n - Suc 0. g l * unity_root n (int m * int l))"
        using n by (intro sum.cong) auto
      also have "\<dots> = (\<Sum>l = Suc 0..n. g l * unity_root n (int m * int l))"
        using periodic_arithmetic_sum_periodic_arithmetic_shift[OF fact_per, of 1] n by auto
      finally show ?thesis by simp
    qed
  qed
  also have "\<dots> = (\<Sum>k = 1..n. (1 / of_nat n) * gauss_sum_int (-k) * unity_root n (m*k))"
  proof -
    {fix k :: nat
    have shift: "(\<Sum>m<n. \<chi> m * unity_root n (- int k * int m)) = 
        (\<Sum>m = 1..n. \<chi> m * unity_root n (- int k * int m))"
    proof -
      have per_unit: "periodic_arithmetic (\<lambda>m. unity_root n (- int k * int m)) n"
        using unity_periodic_arithmetic_mult by blast
      then have prod_per: "periodic_arithmetic (\<lambda>m. \<chi> m * unity_root n (- int k * int m)) n"
        using per mult_periodic_arithmetic by blast
      show ?thesis
      proof -
        have "(\<Sum>m<n. \<chi> m * unity_root n (- int k * int m)) =
              (\<Sum>l = 0..n - Suc 0. \<chi> l * unity_root n (- int k * int l))"
          using n by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>m = 1..n. \<chi> m * unity_root n (- int k * int m))"
          using periodic_arithmetic_sum_periodic_arithmetic_shift[OF prod_per, of 1] n by auto
        finally show ?thesis by simp
      qed
    qed
    have "g k = 1 / of_nat n *
      (\<Sum>m<n. \<chi> m * unity_root n (- int k * int m))"
      using g_def by auto
    also have "\<dots> = 1 / of_nat n *
      (\<Sum>m = 1..n. \<chi> m * unity_root n (- int k * int m))"
      using shift by simp
    also have "\<dots> = 1 / of_nat n * gauss_sum_int (-k)"
      unfolding gauss_sum_int_def 
      by (simp add: algebra_simps)
    finally have "g k = 1 / of_nat n * gauss_sum_int (-k)" by simp} 
    note g_expr = this
      show ?thesis
        by (rule sum.cong, simp, simp add: g_expr) 
    qed
    finally show ?thesis by auto
qed


subsection \<open>Separability\<close>

definition "separable k \<longleftrightarrow> gauss_sum k = cnj (\<chi> k) * gauss_sum 1"

corollary gauss_coprime_separable:
  assumes "coprime k n" 
  shows   "separable k" 
  using gauss_sum_reduction[OF assms] unfolding separable_def by simp

text \<open>Theorem 8.10\<close>
theorem global_separability_condition:
  "(\<forall>n>0. separable n) \<longleftrightarrow> (\<forall>k>0. \<not>coprime k n \<longrightarrow> gauss_sum k = 0)"
proof -
  {fix k 
  assume "\<not> coprime k n"
  then have "\<chi>(k) = 0" by (simp add: eq_zero)
  then have "cnj (\<chi> k) = 0" by blast
  then have "separable k \<longleftrightarrow> gauss_sum k = 0" 
    unfolding separable_def by auto} 
  note not_case = this
  
  show ?thesis
    using gauss_coprime_separable not_case separable_def by blast      
qed

lemma of_real_moebius_mu [simp]: "of_real (moebius_mu k) = moebius_mu k"
  by (simp add: moebius_mu_def)

corollary principal_not_totally_separable:
  assumes "\<chi> = principal_dchar n"
  shows "\<not>(\<forall>k > 0. separable k)"
proof -
  have n_pos: "n > 0" using n by simp  
  have tot_0: "totient n \<noteq> 0" by (simp add: n_pos)
  have "moebius_mu (n div gcd n n) \<noteq> 0" by (simp add: \<open>n > 0\<close>)
  then have moeb_0: "\<exists>k. moebius_mu (n div gcd k n) \<noteq> 0" by blast
  
  have lem: "gauss_sum k = totient n * moebius_mu (n div gcd k n) / totient (n div gcd k n)"
    if "k > 0" for k
  proof -
    have "gauss_sum k = ramanujan_sum n k"
      using ramanujan_sum_conv_gauss_sum[OF assms(1)] ..
    also have "\<dots> = totient n * moebius_mu (n div gcd k n) / (totient (n div gcd k n))"
      by (simp add: ramanujan_sum_k_n_dirichlet_expr[OF n_pos that])
    finally show ?thesis .
  qed
  have 2: "\<not> coprime n n" using n by auto
  have 3: "gauss_sum n \<noteq> 0" 
    using lem[OF n_pos] tot_0 moebius_mu_1 by simp
  from n_pos 2 3 have
    "\<exists>k>0. \<not>coprime k n \<and> gauss_sum k \<noteq> 0" by blast
  then obtain k where "k > 0 \<and> \<not> coprime k n \<and> gauss_sum k \<noteq> 0" by blast
  note right_not_zero = this

  have "cnj (\<chi> k) * gauss_sum 1 = 0" if "\<not>coprime k n" for k
    using that assms by (simp add: principal_dchar_def)
  then show ?thesis 
     unfolding separable_def using right_not_zero by auto
qed

text \<open>Theorem 8.11\<close>
theorem gauss_sum_1_mod_square_eq_k: 
  assumes "(\<forall>k. k > 0 \<longrightarrow> separable k)" 
  shows "norm (gauss_sum 1) ^ 2 = real n" 
proof -
  have "(norm (gauss_sum 1))^2 = gauss_sum 1 * cnj (gauss_sum 1)"
    using complex_norm_square by blast
  also have "\<dots> = gauss_sum 1 * (\<Sum>m = 1..n. cnj (\<chi>(m)) * unity_root n (-m))"
  proof -
    have "cnj (gauss_sum 1) = (\<Sum>m = 1..n. cnj (\<chi>(m)) * unity_root n (-m))"
      unfolding gauss_sum_def by (simp add: unity_root_uminus)
    then show ?thesis by argo
  qed
  also have "\<dots> = (\<Sum>m = 1..n. gauss_sum 1 * cnj (\<chi>(m)) * unity_root n (-m))"
    by (subst sum_distrib_left)(simp add: algebra_simps)
  also have "\<dots> = (\<Sum>m = 1..n. gauss_sum m * unity_root n (-m))"
  proof (rule sum.cong,simp)   
    fix x
    assume as: "x \<in> {1..n}"
    show "gauss_sum 1 * cnj (\<chi> x) * unity_root n (-x) =
          gauss_sum x * unity_root n (-x)"
      using assms(1) unfolding separable_def 
      by (rule allE[of _ x]) (use as in auto)
  qed
  also have "\<dots> = (\<Sum>m = 1..n. (\<Sum>r = 1..n. \<chi> r * unity_root n (r*m) * unity_root n (-m)))"
    unfolding gauss_sum_def 
    by (rule sum.cong,simp,rule sum_distrib_right)
  also have "\<dots> = (\<Sum>m = 1..n. (\<Sum>r = 1..n. \<chi> r * unity_root n (m*(r-1)) ))"
    by (intro sum.cong refl) (auto simp: unity_root_diff of_nat_diff unity_root_uminus field_simps)
  also have "\<dots> = (\<Sum>r=1..n. (\<Sum>m=1..n.  \<chi>(r) *unity_root n (m*(r-1))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>r=1..n. \<chi>(r) *(\<Sum>m=1..n. unity_root n (m*(r-1))))"
    by (rule sum.cong, simp, simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>r=1..n. \<chi>(r) * unity_root_sum n (r-1))" 
  proof (intro sum.cong refl)
    fix x
    assume "x \<in> {1..n}" 
    then have 1: "periodic_arithmetic (\<lambda>m. unity_root n (int (m * (x - 1)))) n"
      using unity_periodic_arithmetic_mult[of n "x-1"] 
      by (simp add: mult.commute)
    have "(\<Sum>m = 1..n. unity_root n (int (m * (x - 1)))) = 
          (\<Sum>m = 0..n-1. unity_root n (int (m * (x - 1))))"
      using periodic_arithmetic_sum_periodic_arithmetic_shift[OF 1 _, of 1] n by simp
    also have "\<dots> = unity_root_sum n (x-1)"
      using n unfolding unity_root_sum_def by (intro sum.cong) (auto simp: mult_ac)
    finally have "(\<Sum>m = 1..n. unity_root n (int (m * (x - 1)))) =
                  unity_root_sum n (int (x - 1))" .
    then show "\<chi> x * (\<Sum>m = 1..n. unity_root n (int (m * (x - 1)))) =
               \<chi> x * unity_root_sum n (int (x - 1))" by argo
  qed
  also have "\<dots> = (\<Sum>r \<in> {1}. \<chi> r * unity_root_sum n (int (r - 1)))"    
    using n unity_root_sum_nonzero_iff int_ops(6)
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = \<chi> 1 * n" using n by simp 
  also have "\<dots> = n" by simp
  finally show ?thesis
    using of_real_eq_iff by fastforce
qed

text \<open>Theorem 8.12\<close>
theorem gauss_sum_nonzero_noncoprime_necessary_condition:
  assumes "gauss_sum k \<noteq> 0" "\<not>coprime k n" "k > 0"
  defines "d \<equiv> n div gcd k n"  
  assumes "coprime a n" "[a = 1] (mod d)" 
  shows   "d dvd n" "d < n" "\<chi> a = 1" 
proof -
  show "d dvd n" 
    unfolding d_def using n by (subst div_dvd_iff_mult) auto
  from assms(2) have "gcd k n \<noteq> 1" by blast
  then have "gcd k n > 1" using assms(3,4) by (simp add: nat_neq_iff)
  with n show "d < n" by (simp add: d_def)

  have "periodic_arithmetic (\<lambda>r. \<chi> (r)* unity_root n (k*r)) n" 
    using mult_periodic_arithmetic[OF dir_periodic_arithmetic unity_periodic_arithmetic_mult] by auto
  then have 1: "periodic_arithmetic (\<lambda>r. \<chi> (r)* unity_root n (r*k)) n" 
    by (simp add: algebra_simps)
  
  have "gauss_sum k = (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*k))"
    unfolding gauss_sum_def by blast
  also have "\<dots> = (\<Sum>m = 1..n . \<chi>(m*a) * unity_root n (m*a*k))"
    using periodic_arithmetic_remove_homothecy[OF assms(5) 1] n by auto
  also have "\<dots> = (\<Sum>m = 1..n . \<chi>(m*a) * unity_root n (m*k))"  
  proof (intro sum.cong refl)
    fix m
    from assms(6) obtain b where "a = 1 + b*d" 
      using \<open>d < n\<close> assms(5) cong_to_1'_nat by auto
    then have "m*a*k = m*k+m*b*(n div gcd k n)*k"
      by (simp add: algebra_simps d_def)
    also have "\<dots> = m*k+m*b*n*(k div gcd k n)"
      by (simp add: div_mult_swap dvd_div_mult)
    also obtain p where "\<dots> = m*k+m*b*n*p" by blast
    finally have "m*a*k = m*k+m*b*p*n" by simp
    then have 1: "m*a*k mod n= m*k mod n" 
      using mod_mult_self1 by simp
    then have "unity_root n (m * a * k) = unity_root n (m * k)" 
    proof -
      have "unity_root n (m * a * k) = unity_root n ((m * a * k) mod n)"
        using unity_root_mod[of n] zmod_int by simp
      also have "\<dots> = unity_root n (m * k)" 
        using unity_root_mod[of n] zmod_int 1 by presburger
      finally show ?thesis by blast
    qed
    then show "\<chi> (m * a) * unity_root n (int (m * a * k)) =
               \<chi> (m * a) * unity_root n (int (m * k))" by auto
  qed
  also have "\<dots> = (\<Sum>m = 1..n . \<chi>(a) * (\<chi>(m) * unity_root n (m*k)))"
    by (rule sum.cong,simp,subst mult,simp)
  also have "\<dots> =  \<chi>(a) * (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*k))"
    by (simp add: sum_distrib_left[symmetric]) 
  also have "\<dots> = \<chi>(a) * gauss_sum k" 
    unfolding gauss_sum_def by blast
  finally have "gauss_sum k = \<chi>(a) * gauss_sum k" by blast
  then show "\<chi> a = 1" 
    using assms(1) by simp
qed


subsection \<open>Induced moduli and primitive characters\<close>

definition "induced_modulus d \<longleftrightarrow> d dvd n \<and> (\<forall>a. coprime a n \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = 1)"

lemma induced_modulus_dvd: "induced_modulus d \<Longrightarrow> d dvd n"
  unfolding induced_modulus_def by blast

lemma induced_modulusI [intro?]:
  "d dvd n \<Longrightarrow> (\<And>a. coprime a n \<Longrightarrow> [a = 1] (mod d) \<Longrightarrow> \<chi> a = 1) \<Longrightarrow> induced_modulus d"
  unfolding induced_modulus_def by auto

lemma induced_modulusD: "induced_modulus d \<Longrightarrow> coprime a n \<Longrightarrow> [a = 1] (mod d) \<Longrightarrow> \<chi> a = 1"
  unfolding induced_modulus_def by blast

lemma zero_not_ind_mod: "\<not>induced_modulus 0" 
  unfolding induced_modulus_def using n by simp

lemma div_gcd_dvd1: "(a :: 'a :: semiring_gcd) div gcd a b dvd a"
  by (metis dvd_def dvd_div_mult_self gcd_dvd1)

lemma div_gcd_dvd2: "(b :: 'a :: semiring_gcd) div gcd a b dvd b"
  by (metis div_gcd_dvd1 gcd.commute)

lemma g_non_zero_ind_mod:
  assumes "gauss_sum k \<noteq> 0" "\<not>coprime k n" "k > 0"
  shows  "induced_modulus (n div gcd k n)"
proof
  show "n div gcd k n dvd n"
    by (metis dvd_div_mult_self dvd_triv_left gcd.commute gcd_dvd1)
  fix a :: nat
  assume "coprime a n" "[a = 1] (mod n div gcd k n)"
  thus "\<chi> a = 1"
    using assms n gauss_sum_nonzero_noncoprime_necessary_condition(3) by auto
qed

lemma induced_modulus_modulus: "induced_modulus n"
  unfolding induced_modulus_def 
proof (rule conjI,simp,safe) 
  fix a 
  assume "[a = 1] (mod n)" 
  then have "a mod n = 1 mod n" 
    using cong_def[of a 1 n] by blast
  also have "\<dots> = 1" 
    using eq_zero_iff zero_eq_0 by fastforce
  finally have 1: "a mod n = 1" by simp
  
  have "\<chi> a = \<chi> (a mod n)" by simp
  also have "\<dots> = \<chi> 1" using cong_def 1 by auto
  also have "\<dots> = 1" by simp
  finally show "\<chi> a = 1" by blast
qed

text \<open>Theorem 8.13\<close>
theorem one_induced_iff_principal:
 "induced_modulus 1 \<longleftrightarrow> \<chi> = principal_dchar n"
proof
  assume "induced_modulus 1" 
  then have "(\<forall>a. coprime a n \<longrightarrow> \<chi> a = 1)"
    unfolding induced_modulus_def by simp
  then show "\<chi> = principal_dchar n" 
    unfolding principal_dchar_def using eq_zero by auto
next
  assume as: "\<chi> = principal_dchar n"
  {fix a
  assume "coprime a n"
  then have "\<chi> a = 1" 
    using principal_dchar_def as by simp}
  then show "induced_modulus 1"
    unfolding induced_modulus_def by auto
qed

end


locale primitive_dchar = dcharacter +
  assumes no_induced_modulus: "\<not>(\<exists>d<n. induced_modulus d)"

locale nonprimitive_dchar = dcharacter +
  assumes induced_modulus: "\<exists>d<n. induced_modulus d"

lemma (in nonprimitive_dchar) nonprimitive: "\<not>primitive_dchar n \<chi>"
proof
  assume "primitive_dchar n \<chi>"
  then interpret A: primitive_dchar n "residue_mult_group n" \<chi>
    by auto
  from A.no_induced_modulus induced_modulus show False by contradiction
qed

lemma (in dcharacter) primitive_dchar_iff:
  "primitive_dchar n \<chi> \<longleftrightarrow> \<not>(\<exists>d<n. induced_modulus d)"
  unfolding primitive_dchar_def primitive_dchar_axioms_def
  using dcharacter_axioms by metis

lemma (in residues_nat) principal_not_primitive: 
  "\<not>primitive_dchar n (principal_dchar n)"
  unfolding principal.primitive_dchar_iff
  using principal.one_induced_iff_principal n by auto

lemma (in dcharacter) not_primitive_imp_nonprimitive:
  assumes "\<not>primitive_dchar n \<chi>"
  shows   "nonprimitive_dchar n \<chi>"
  using assms dcharacter_axioms
  unfolding nonprimitive_dchar_def primitive_dchar_def
            primitive_dchar_axioms_def nonprimitive_dchar_axioms_def by auto


text \<open>Theorem 8.14\<close>
theorem (in dcharacter) prime_nonprincipal_is_primitive:
  assumes "prime n"
  assumes "\<chi> \<noteq> principal_dchar n" 
  shows   "primitive_dchar n \<chi>"
proof -
  {fix m
  assume "induced_modulus m" 
  then have "m = n" 
    using assms prime_nat_iff induced_modulus_def
          one_induced_iff_principal by blast}
  then show ?thesis using primitive_dchar_iff by blast
qed

text \<open>Theorem 8.15\<close>
corollary (in primitive_dchar) primitive_encoding:
  "\<forall>k>0. \<not>coprime k n \<longrightarrow> gauss_sum k = 0" 
  "\<forall>k>0. separable k"
  "norm (gauss_sum 1) ^ 2 = n"
proof safe
  show 1: "gauss_sum k = 0" if "k > 0" and "\<not>coprime k n" for k
  proof (rule ccontr)
    assume "gauss_sum k \<noteq> 0"
    hence "induced_modulus (n div gcd k n)"
      using that by (intro g_non_zero_ind_mod) auto
    moreover have "n div gcd k n < n"
      using n that
      by (meson coprime_iff_gcd_eq_1 div_eq_dividend_iff le_less_trans
                linorder_neqE_nat nat_dvd_not_less principal.div_gcd_dvd2 zero_le_one)
    ultimately show False using no_induced_modulus by blast
  qed

  have "(\<forall>n>0. separable n)"
    unfolding global_separability_condition by (auto intro!: 1)
  thus "separable n" if "n > 0" for n
    using that by blast
  thus "norm (gauss_sum 1) ^ 2 = n"
    using gauss_sum_1_mod_square_eq_k by blast
qed

text \<open>Theorem 8.16\<close>
lemma (in dcharacter) induced_modulus_altdef1:
  "induced_modulus d \<longleftrightarrow>
     d dvd n \<and> (\<forall>a b. coprime a n \<and> coprime b n \<and> [a = b] (mod d) \<longrightarrow> \<chi> a = \<chi> b)"
proof 
  assume 1: "induced_modulus d"
  with n have d: "d dvd n" "d > 0"
    by (auto simp: induced_modulus_def intro: Nat.gr0I)
  show " d dvd n \<and> (\<forall>a b. coprime a n \<and> coprime b n \<and> [a = b] (mod d) \<longrightarrow> \<chi>(a) = \<chi>(b))"
  proof safe
    fix a b
    assume 2: "coprime a n" "coprime b n" "[a = b] (mod d)"
    show "\<chi>(a) = \<chi>(b)" 
    proof -
      from 2(1) obtain a' where eq: "[a*a' = 1] (mod n)"
        using cong_solve by blast
      from this d have "[a*a' = 1] (mod d)"
        using cong_dvd_modulus_nat by blast
      from this 1 have "\<chi>(a*a') = 1" 
        unfolding induced_modulus_def
        by (meson "2"(2) eq cong_imp_coprime cong_sym coprime_divisors gcd_nat.refl one_dvd)
      then have 3: "\<chi>(a)*\<chi>(a') = 1" 
        by simp

      from 2(3) have "[a*a' = b*a'] (mod d)" 
        by (simp add: cong_scalar_right)
      moreover have 4: "[b*a' = 1] (mod d)" 
        using \<open>[a * a' = 1] (mod d)\<close> calculation cong_sym cong_trans by blast
      have "\<chi>(b*a') = 1" 
      proof -
        have "coprime (b*a') n"
          using "2"(2) cong_imp_coprime[OF cong_sym[OF eq]] by simp
        then show ?thesis using 4 induced_modulus_def 1 by blast
      qed
      then have 4: "\<chi>(b)*\<chi>(a') = 1" 
        by simp
      from 3 4 show "\<chi>(a) = \<chi>(b)" 
        using mult_cancel_left
        by (cases "\<chi>(a') = 0") (fastforce simp add: field_simps)+
    qed
  qed fact+
next 
  assume *: "d dvd n \<and> (\<forall>a b. coprime a n \<and> coprime b n \<and> [a = b] (mod d) \<longrightarrow> \<chi> a = \<chi> b)"
  then have "\<forall>a . coprime a n \<and> coprime 1 n \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = \<chi> 1"
    by blast
  then have "\<forall>a . coprime a n \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = 1"
    using coprime_1_left by simp
  then show "induced_modulus d"
    unfolding induced_modulus_def using * by blast
qed

text \<open>Exercise 8.4\<close>

lemma induced_modulus_altdef2_lemma:
  fixes n a d q :: nat
  defines "q \<equiv> (\<Prod> p | prime p \<and> p dvd n \<and> \<not> (p dvd a). p)"
  defines "m \<equiv> a + q * d"
  assumes "n > 0" "coprime a d"
  shows "[m = a] (mod d)" and "coprime m n"
proof (simp add: assms(2) cong_add_lcancel_0_nat cong_mult_self_right)
  have fin: "finite {p. prime p \<and> p dvd n \<and> \<not> (p dvd a)}" by (simp add: assms)
  { fix p
    assume 4: "prime p" "p dvd m" "p dvd n"
    have "p = 1"
    proof (cases "p dvd a")
      case True
      from this assms 4(2) have "p dvd q*d" 
       by (simp add: dvd_add_right_iff)
      then have a1: "p dvd q \<or> p dvd d"
       using 4(1) prime_dvd_mult_iff by blast
    
      have a2: "\<not> (p dvd q)" 
      proof (rule ccontr,simp)  
       assume "p dvd q"
       then have "p dvd (\<Prod> p | prime p \<and> p dvd n \<and> \<not> (p dvd a). p)" 
         unfolding assms by simp
       then have "\<exists>x\<in>{p. prime p \<and> p dvd n \<and> \<not> p dvd a}. p dvd x"
        using prime_dvd_prod_iff[OF fin 4(1)] by simp
       then obtain x where c: "p dvd x \<and> prime x \<and> \<not> x dvd a" by blast
       then have "p = x" using 4(1) by (simp add: primes_dvd_imp_eq)
       then show "False" using True c by auto
      qed
      have a3: "\<not> (p dvd d)" 
        using True assms "4"(1) coprime_def not_prime_unit by auto
  
      from a1 a2 a3 show ?thesis by simp
    next
      case False
      then have "p dvd q" 
      proof -
       have in_s: "p \<in> {p. prime p \<and> p dvd n \<and> \<not> p dvd a}"
        using False 4(3) 4(1) by simp
       show "p dvd q" 
        unfolding assms using dvd_prodI[OF fin in_s ] by fast
      qed
      then have "p dvd q*d" by simp
      then have "p dvd a" using 4(2) assms
        by (simp add: dvd_add_left_iff)
      then show ?thesis using False by auto
    qed
  }
  note lem = this
  show "coprime m n" 
  proof (subst coprime_iff_gcd_eq_1)
    {fix a 
     assume "a dvd m" "a dvd n" "a \<noteq> 1"
     {fix p
      assume "prime p" "p dvd a"
      then have "p dvd m" "p dvd n" 
       using \<open>a dvd m\<close> \<open>a dvd n\<close> by auto
      from lem have "p = a" 
       using not_prime_1 \<open>prime p\<close> \<open>p dvd m\<close> \<open>p dvd n\<close> by blast}
      then have "prime a" 
       using prime_prime_factor[of a] \<open>a \<noteq> 1\<close> by blast
      then have "a = 1" using lem \<open>a dvd m\<close> \<open>a dvd n\<close> by blast
      then have "False" using \<open>a = 1\<close> \<open>a \<noteq> 1\<close> by blast
    }
    then show "gcd m n = 1" by blast
  qed
qed

text \<open>Theorem 8.17\<close>
text\<open>The case \<open>d = 1\<close> is exactly the case described in @{thm dcharacter.one_induced_iff_principal}.\<close>
theorem (in dcharacter) induced_modulus_altdef2:
  assumes "d dvd n" "d \<noteq> 1" 
  defines "\<chi>\<^sub>1 \<equiv> principal_dchar n"
  shows "induced_modulus d \<longleftrightarrow> (\<exists>\<Phi>. dcharacter d \<Phi> \<and> (\<forall>k. \<chi> k = \<Phi> k * \<chi>\<^sub>1 k))"
proof
  from n have n_pos: "n > 0" by simp
  assume as_im: "induced_modulus d" 
  define f where
    "f \<equiv> (\<lambda>k. k + 
      (if k = 1 then
         0
       else (prod id {p. prime p \<and> p dvd n \<and> \<not> (p dvd k)})*d)
      )"
  have [simp]: "f (Suc 0) = 1" unfolding f_def by simp
  {
    fix k
    assume as: "coprime k d" 
    hence "[f k = k] (mod d)" "coprime (f k) n" 
      using induced_modulus_altdef2_lemma[OF n_pos as] by (simp_all add: f_def)
  }
  note m_prop = this
  
  define \<Phi> where
   "\<Phi> \<equiv> (\<lambda>n. (if \<not> coprime n d then 0 else \<chi>(f n)))"

  have \<Phi>_1: "\<Phi> 1 = 1" 
    unfolding \<Phi>_def by simp

  from assms(1,2) n have "d > 0" by (intro Nat.gr0I) auto
  from induced_modulus_altdef1 assms(1) \<open>d > 0\<close> as_im 
    have b: "(\<forall>a b. coprime a n \<and> coprime b n \<and> 
                 [a = b] (mod d) \<longrightarrow> \<chi> a = \<chi> b)" by blast

  have \<Phi>_periodic:  " \<forall>a. \<Phi> (a + d) = \<Phi> a" 
  proof 
    fix a
    have "gcd (a+d) d = gcd a d" by auto
    then have cop: "coprime (a+d) d = coprime a d"  
      using coprime_iff_gcd_eq_1 by presburger
    show "\<Phi> (a + d) = \<Phi> a"
    proof (cases "coprime a d")
      case True
      from True cop have cop_ad: "coprime (a+d) d" by blast      
      have p1: "[f (a+d) = f a] (mod d)" 
        using m_prop(1)[of "a+d", OF cop_ad] 
              m_prop(1)[of "a",OF True] by (simp add: cong_def)
      have p2: "coprime (f (a+d)) n" "coprime (f a) n" 
        using m_prop(2)[of "a+d", OF cop_ad]
              m_prop(2)[of "a", OF True] by blast+ 
      from b p1 p2 have eq: "\<chi> (f (a + d)) = \<chi> (f a)" by blast
      show ?thesis 
        unfolding \<Phi>_def 
        by (subst cop,simp,safe, simp add: eq) 
    next
      case False
      then show ?thesis unfolding \<Phi>_def by (subst cop,simp)
    qed  
  qed

  have \<Phi>_mult: "\<forall>a b. a \<in> totatives d \<longrightarrow>
          b \<in> totatives d \<longrightarrow> \<Phi> (a * b) = \<Phi> a * \<Phi> b"
  proof (safe)
    fix a b
    assume "a \<in> totatives d" "b \<in> totatives d"  
    consider (ab) "coprime a d \<and> coprime b d" | 
             (a)  "coprime a d \<and> \<not> coprime b d" |
             (b)  "coprime b d \<and> \<not> coprime a d" |
             (n)  "\<not> coprime a d \<and> \<not> coprime b d" by blast
    then show "\<Phi> (a * b) = \<Phi> a * \<Phi> b" 
    proof cases
      case ab 
      then have c_ab: 
        "coprime (a*b) d" "coprime a d" "coprime b d" by simp+ 
      then have p1: "[f (a * b) = a * b] (mod d)" "coprime (f (a * b)) n"
        using m_prop[of "a*b", OF c_ab(1)] by simp+
      moreover have p2: "[f a = a] (mod d)" "coprime (f a) n"
                    "[f b = b] (mod d)" "coprime (f b) n"
        using m_prop[of "a",OF c_ab(2)]
              m_prop[of "b",OF c_ab(3) ] by simp+
      have p1s: "[f (a * b) = (f a) * (f b)] (mod d)"
      proof -
        have "[f (a * b) = a * b] (mod d)"
          using p1(1) by blast
        moreover have "[a * b = f(a) * f(b)] (mod d)" 
          using p2(1) p2(3) by (simp add: cong_mult cong_sym)
        ultimately show ?thesis using cong_trans by blast
      qed
      have p2s: "coprime (f a*f b) n"
        using p2(2) p2(4) by simp
      have "\<chi> (f (a * b)) = \<chi> (f a * f b)" 
        using p1s p2s p1(2) b by blast 
      then show ?thesis 
        unfolding \<Phi>_def by (simp add: c_ab)
    qed (simp_all add: \<Phi>_def)
  qed
  have d_gr_1: "d > 1" using assms(1,2) 
    using \<open>0 < d\<close> by linarith
  show "\<exists>\<Phi>. dcharacter d \<Phi> \<and> (\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n)" 
  proof (standard,rule conjI) 
    show "dcharacter d \<Phi>" 
      unfolding dcharacter_def residues_nat_def dcharacter_axioms_def 
      using d_gr_1 \<Phi>_def f_def \<Phi>_mult \<Phi>_1 \<Phi>_periodic by simp
    show "\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n" 
    proof
      fix k
      show "\<chi> k = \<Phi> k * \<chi>\<^sub>1 k"
      proof (cases "coprime k n")
        case True
        then have "coprime k d" using assms(1) by auto
        then have "\<Phi>(k) = \<chi>(f k)" using \<Phi>_def by simp
        moreover have "[f k = k] (mod d)" 
          using m_prop[OF \<open>coprime k d\<close>] by simp
        moreover have "\<chi>\<^sub>1 k = 1" 
          using assms(3) principal_dchar_def \<open>coprime k n\<close> by auto
        ultimately show "\<chi>(k) = \<Phi>(k) * \<chi>\<^sub>1(k)" 
        proof -
          assume "\<Phi> k = \<chi> (f k)" "[f k = k] (mod d)" "\<chi>\<^sub>1 k = 1"
          then have "\<chi> k = \<chi> (f k)"
            using \<open>local.induced_modulus d\<close> induced_modulus_altdef1 assms(1) \<open>d > 0\<close>
                  True \<open>coprime k d\<close> m_prop(2) by auto
          also have "\<dots> = \<Phi> k" by (simp add: \<open>\<Phi> k = \<chi> (f k)\<close>)
          also have "\<dots> = \<Phi> k * \<chi>\<^sub>1 k" by (simp add: \<open>\<chi>\<^sub>1 k = 1\<close>)
          finally show ?thesis by simp
        qed
      next
        case False
        hence "\<chi> k = 0"
          using eq_zero_iff by blast 
        moreover have "\<chi>\<^sub>1 k = 0"
          using False assms(3) principal_dchar_def by simp       
        ultimately show ?thesis by simp
      qed      
    qed
  qed
next
  assume "(\<exists>\<Phi>. dcharacter d \<Phi> \<and> (\<forall>k. \<chi> k = \<Phi> k * \<chi>\<^sub>1 k))"
  then obtain \<Phi> where 1: "dcharacter d \<Phi>" "(\<forall>k. \<chi> k = \<Phi> k * \<chi>\<^sub>1 k)" by blast
  show "induced_modulus d"
    unfolding induced_modulus_def    
  proof (rule conjI,fact,safe)
    fix k
    assume 2: "coprime k n" "[k = 1] (mod d)"
    then have "\<chi>\<^sub>1 k = 1" "\<Phi> k = 1" 
    proof (simp add: assms(3) principal_dchar_def)
      have "\<Phi> k = \<Phi> (k mod d)" by (simp add: dcharacter.mod[OF 1(1), of k])
      also have "\<dots> = \<Phi> (1 mod d)" using cong_def[of k 1 d] 2(2) by simp
      also have "\<dots> = \<Phi> 1" using assms(2) "1"(1) dcharacter.mod by blast
      also have "\<dots> = 1" using dcharacter.Suc_0[OF 1(1)] by simp
      finally show "\<Phi> k = 1" by simp
    qed
    then show "\<chi> k = 1" using 1(2) by simp    
  qed
qed


subsection \<open>The conductor of a character\<close>

context dcharacter
begin

definition "conductor = Min {d. induced_modulus d}"

lemma conductor_fin: "finite {d. induced_modulus d}"
proof -
  let ?A = "{d. induced_modulus d}" 
  have "?A \<subseteq> {d. d dvd n}" 
    unfolding induced_modulus_def by blast
  moreover have "finite {d. d dvd n}" using n by simp
  ultimately show "finite ?A" using finite_subset by auto
qed

lemma conductor_induced: "induced_modulus conductor"
proof -
  have "{d. induced_modulus d} \<noteq> {}" using induced_modulus_modulus by blast
  then show "induced_modulus conductor"             
    using Min_in[OF conductor_fin ] conductor_def by auto
qed

lemma conductor_le_iff: "conductor \<le> a \<longleftrightarrow> (\<exists>d\<le>a. induced_modulus d)"
  unfolding conductor_def using conductor_fin induced_modulus_modulus by (subst Min_le_iff) auto

lemma conductor_ge_iff: "conductor \<ge> a \<longleftrightarrow> (\<forall>d. induced_modulus d \<longrightarrow> d \<ge> a)"
  unfolding conductor_def using conductor_fin induced_modulus_modulus by (subst Min_ge_iff) auto

lemma conductor_leI: "induced_modulus d \<Longrightarrow> conductor \<le> d"
  by (subst conductor_le_iff) auto

lemma conductor_geI: "(\<And>d. induced_modulus d \<Longrightarrow> d \<ge> a) \<Longrightarrow> conductor \<ge> a"
  by (subst conductor_ge_iff) auto

lemma conductor_dvd: "conductor dvd n"
  using conductor_induced unfolding induced_modulus_def by blast

lemma conductor_le_modulus: "conductor \<le> n"
  using conductor_dvd by (rule dvd_imp_le) (use n in auto)

lemma conductor_gr_0: "conductor > 0"
  unfolding conductor_def using zero_not_ind_mod 
  using conductor_def conductor_induced neq0_conv by fastforce

lemma conductor_eq_1_iff_principal: "conductor = 1 \<longleftrightarrow> \<chi> = principal_dchar n" 
proof
  assume "conductor = 1" 
  then have "induced_modulus 1"
    using conductor_induced by auto
  then show "\<chi> = principal_dchar n"
    using one_induced_iff_principal by blast
next
  assume "\<chi> = principal_dchar n"
  then have im_1: "induced_modulus 1" using one_induced_iff_principal by auto
  show "conductor = 1" 
  proof -
    have "conductor \<le> 1" 
      using conductor_fin Min_le[OF conductor_fin,simplified,OF im_1]
      by (simp add: conductor_def[symmetric])
    then show ?thesis using conductor_gr_0 by auto
  qed
qed

lemma conductor_principal [simp]: "\<chi> = principal_dchar n \<Longrightarrow> conductor = 1"
  by (subst conductor_eq_1_iff_principal)
  
lemma nonprimitive_imp_conductor_less:
  assumes "\<not>primitive_dchar n \<chi>"
  shows "conductor < n" 
proof -
  obtain d where d: "induced_modulus d" "d < n" 
    using primitive_dchar_iff assms by blast
  from d(1) have "conductor \<le> d"
    by (rule conductor_leI)
  also have "\<dots> < n" by fact
  finally show ?thesis .
qed

lemma (in nonprimitive_dchar) conductor_less_modulus: "conductor < n"
  using nonprimitive_imp_conductor_less nonprimitive by metis


text \<open>Theorem 8.18\<close>
theorem primitive_principal_form:
  defines "\<chi>\<^sub>1 \<equiv> principal_dchar n"
  assumes "\<chi> \<noteq> principal_dchar n"
  shows "\<exists>\<Phi>. primitive_dchar conductor \<Phi> \<and> (\<forall>n. \<chi>(n) = \<Phi>(n) * \<chi>\<^sub>1(n))"
proof -
  (*
    TODO: perhaps residues_nat should be relaxed to allow n = 1.
    Then we could remove the unnecessary precondition here.
    It makes no real difference though.
  *)
  from n have n_pos: "n > 0" by simp
  define d where "d = conductor" 
  have induced: "induced_modulus d" 
    unfolding d_def using conductor_induced by blast
  then have d_not_1: "d \<noteq> 1" 
    using one_induced_iff_principal assms by auto
  hence d_gt_1: "d > 1" using conductor_gr_0 by (auto simp: d_def)
  
  from induced obtain \<Phi> where \<Phi>_def: "dcharacter d \<Phi> \<and> (\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n)"
    using d_not_1
    by (subst (asm) induced_modulus_altdef2) (auto simp: d_def conductor_dvd \<chi>\<^sub>1_def)
  have phi_dchars: "\<Phi> \<in> dcharacters d" using \<Phi>_def dcharacters_def by auto

  interpret \<Phi>: dcharacter d "residue_mult_group d" \<Phi>
    using \<Phi>_def by auto

  have \<Phi>_prim: "primitive_dchar d \<Phi>" 
  proof (rule ccontr)
    assume "\<not> primitive_dchar d \<Phi>"   
    then obtain q where 
      1: "q dvd d \<and> q < d \<and> \<Phi>.induced_modulus q"
      unfolding \<Phi>.induced_modulus_def \<Phi>.primitive_dchar_iff by blast
    then have 2: "induced_modulus q" 
    proof -
      {fix k
      assume mod_1: "[k = 1] (mod q)" 
      assume cop: "coprime k n" 
      have "\<chi>(k) = \<Phi>(k)*\<chi>\<^sub>1(k)" using \<Phi>_def by auto
      also have "\<dots> = \<Phi>(k)" 
        using cop by (simp add: assms principal_dchar_def)  
      also have "\<dots> = 1" 
          using 1 mod_1 \<Phi>.induced_modulus_def 
                \<open>induced_modulus d\<close> cop induced_modulus_def by auto
      finally have "\<chi>(k) = 1" by blast}

      then show ?thesis 
        using induced_modulus_def "1" \<open>induced_modulus d\<close> by auto
    qed
     
    from 1 have "q < d" by simp
    moreover have "d \<le> q" unfolding d_def
      by (intro conductor_leI) fact
    ultimately show False by linarith
  qed     

  from \<Phi>_def \<Phi>_prim d_def phi_dchars show ?thesis by blast
qed

definition primitive_extension :: "nat \<Rightarrow> complex" where
  "primitive_extension =
     (SOME \<Phi>. primitive_dchar conductor \<Phi> \<and> (\<forall>k. \<chi> k = \<Phi> k * principal_dchar n k))"

lemma
  assumes nonprincipal: "\<chi> \<noteq> principal_dchar n"
  shows primitive_primitive_extension: "primitive_dchar conductor primitive_extension"
    and principal_decomposition:       "\<chi> k = primitive_extension k * principal_dchar n k"
proof -
  note * = someI_ex[OF primitive_principal_form[OF nonprincipal], folded primitive_extension_def]
  from * show "primitive_dchar conductor primitive_extension" by blast
  from * show "\<chi> k = primitive_extension k * principal_dchar n k" by blast
qed

end


subsection \<open>The connection between primitivity and separability\<close>

lemma residue_mult_group_coset:
  fixes m n m1 m2 :: nat and f :: "nat \<Rightarrow> nat" and G H
  defines "G \<equiv> residue_mult_group n"
  defines "H \<equiv> residue_mult_group m"
  defines "f \<equiv> (\<lambda>k. k mod m)"
  assumes "b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f)"
  assumes "m1 \<in> b" "m2 \<in> b"
  assumes "n > 1" "m dvd n"
  shows "m1 mod m = m2 mod m"
proof -
  have h_1: "\<one>\<^bsub>H\<^esub> = 1" 
    using assms(2) unfolding residue_mult_group_def totatives_def by simp
    
  from assms(4)
  obtain a :: nat where cos_expr: "b = (kernel G H f) #>\<^bsub>G\<^esub> a \<and> a \<in> carrier G" 
    using RCOSETS_def[of G "kernel G H f"] by blast
  then have cop: "coprime a n" 
    using assms(1) unfolding residue_mult_group_def totatives_def by auto
  
  obtain a' where "[a * a' = 1] (mod n)"
    using cong_solve_coprime_nat[OF cop] by auto
  then have a_inv: "(a*a') mod n = 1" 
    using cong_def[of "a*a'" 1 n] assms(7) by simp

  have "m1 \<in> (\<Union>h\<in>kernel G H f. {h \<otimes>\<^bsub>G\<^esub> a})"
       "m2 \<in> (\<Union>h\<in>kernel G H f. {h \<otimes>\<^bsub>G\<^esub> a})"
    using r_coset_def[of G "kernel G H f" a] cos_expr assms(5,6) by blast+
  then have "m1 \<in> (\<Union>h\<in>kernel G H f. {(h * a) mod n})"
            "m2 \<in> (\<Union>h\<in>kernel G H f. {(h * a) mod n})"
    using assms(1) unfolding residue_mult_group_def[of n] by auto
  then obtain m1' m2' where 
    m_expr: "m1 = (m1'* a) mod n \<and> m1' \<in> kernel G H f" 
            "m2 = (m2'* a) mod n \<and> m2' \<in> kernel G H f" 
    by blast

  have eq_1: "m1 mod m = a mod m" 
  proof -
    have "m1 mod m = ((m1'* a) mod n) mod m" using m_expr by blast
    also have "\<dots> = (m1' * a) mod m" 
      using euclidean_semiring_cancel_class.mod_mod_cancel assms(8) by blast
    also have "\<dots> = (m1' mod m) * (a mod m) mod m" 
      by (simp add: mod_mult_eq)
    also have "\<dots> = (a mod m) mod m" 
      using m_expr(1) h_1 unfolding kernel_def assms(3) by simp
    also have "\<dots> = a mod m" by auto
    finally show ?thesis by simp
  qed

  have eq_2: "m2 mod m = a mod m" 
  proof -
    have "m2 mod m = ((m2'* a) mod n) mod m" using m_expr by blast
    also have "\<dots> = (m2' * a) mod m" 
      using euclidean_semiring_cancel_class.mod_mod_cancel assms(8) by blast
    also have "\<dots> = (m2' mod m) * (a mod m) mod m" 
      by (simp add: mod_mult_eq)
    also have "\<dots> = (a mod m) mod m" 
      using m_expr(2) h_1 unfolding kernel_def assms(3) by simp
    also have "\<dots> = a mod m" by auto
    finally show ?thesis by simp
  qed

  from eq_1 eq_2 show ?thesis by argo
qed

lemma residue_mult_group_kernel_partition:
  fixes m n :: nat and f :: "nat \<Rightarrow> nat" and G H
  defines "G \<equiv> residue_mult_group n"
  defines "H \<equiv> residue_mult_group m"
  defines "f \<equiv> (\<lambda>k. k mod m)"
  assumes "m > 1" "n > 0" "m dvd n" 
  shows "partition (carrier G) (rcosets\<^bsub>G\<^esub> kernel G H f)"
        and "card (rcosets\<^bsub>G\<^esub> kernel G H f) = totient m"
        and "card (kernel G H f) = totient n div totient m"
        and "b \<in>(rcosets\<^bsub>G\<^esub> kernel G H f) \<Longrightarrow> b \<noteq> {}"
        and "b \<in>(rcosets\<^bsub>G\<^esub> kernel G H f) \<Longrightarrow> card (kernel G H f) = card b"
        and "bij_betw (\<lambda>b. (the_elem (f ` b))) (rcosets\<^bsub>G\<^esub> kernel G H f) (carrier H)"
proof -
  have "1 < m" by fact
  also have "m \<le> n" using \<open>n > 0\<close> \<open>m dvd n\<close> by (intro dvd_imp_le) auto
  finally have "n > 1" .
  note mn = \<open>m > 1\<close> \<open>n > 1\<close> \<open>m dvd n\<close> \<open>m \<le> n\<close>

  interpret n: residues_nat n G
    using mn by unfold_locales (auto simp: assms)
  interpret m: residues_nat m H
    using mn by unfold_locales (auto simp: assms)
  
  from mn have subset: "f ` carrier G \<subseteq> carrier H"
    by (auto simp: assms(1-3) residue_mult_group_def totatives_def
             dest: coprime_common_divisor_nat intro!: Nat.gr0I)
  moreover have super_set: "carrier H \<subseteq> f ` carrier G"
  proof safe
    fix k assume "k \<in> carrier H"
    hence k: "k > 0" "k \<le> m" "coprime k m"             
      by (auto simp: assms(2) residue_mult_group_def totatives_def)
    from mn \<open>k \<in> carrier H\<close> have "k < m"
      by (simp add: totatives_less assms(2) residue_mult_group_def)
    define P where "P = {p \<in> prime_factors n. \<not>(p dvd m)}"
    define a where "a = \<Prod>P"
    have [simp]: "a \<noteq> 0" by (auto simp: P_def a_def intro!: Nat.gr0I)
    have [simp]: "prime_factors a = P"
    proof -
      have "prime_factors a = set_mset (sum prime_factorization P)"
        unfolding a_def using mn
        by (subst prime_factorization_prod)
           (auto simp: P_def prime_factors_dvd prime_gt_0_nat)
      also have "sum prime_factorization P = (\<Sum>p\<in>P. {#p#})"
        using mn by (intro sum.cong) (auto simp: P_def prime_factorization_prime prime_factors_dvd)
      finally show ?thesis by (simp add: P_def)
    qed

    from mn have "coprime m a"
      by (subst coprime_iff_prime_factors_disjoint) (auto simp: P_def)
    hence "\<exists>x. [x = k] (mod m) \<and> [x = 1] (mod a)"
      by (intro binary_chinese_remainder_nat)
    then obtain x where x: "[x = k] (mod m)" "[x = 1] (mod a)"
      by auto
    from x(1) mn k have [simp]: "x \<noteq> 0"
      using coprime_common_divisor[of k m] by (auto intro!: Nat.gr0I simp: cong_def)
      
    from x(2) have "coprime x a"
      using cong_imp_coprime cong_sym by force
    hence "coprime x (a * m)"
      using k cong_imp_coprime[OF cong_sym[OF x(1)]] by auto
    also have "?this \<longleftrightarrow> coprime x n" using mn
      by (intro coprime_cong_prime_factors)
         (auto simp: prime_factors_product P_def in_prime_factors_iff)
    finally have "x mod n \<in> totatives n"
      using mn by (auto simp: totatives_def intro!: Nat.gr0I)

    moreover have "f (x mod n) = k"
      using x(1) k mn \<open>k < m\<close> by (auto simp: assms(3) cong_def mod_mod_cancel)
    ultimately show "k \<in> f ` carrier G"
      by (auto simp: assms(1) residue_mult_group_def)
  qed

  ultimately have image_eq: "f ` carrier G = carrier H" by blast

  have [simp]: "f (k \<otimes>\<^bsub>G\<^esub> l) = f k \<otimes>\<^bsub>H\<^esub> f l" if "k \<in> carrier G" "l \<in> carrier G" for k l
    using that mn by (auto simp: assms(1-3) residue_mult_group_def totatives_def
                                 mod_mod_cancel mod_mult_eq)
  interpret f: group_hom G H f
    using subset by unfold_locales (auto simp: hom_def)

  show "bij_betw (\<lambda>b. (the_elem (f ` b))) (rcosets\<^bsub>G\<^esub> kernel G H f) (carrier H)"
    unfolding bij_betw_def  
  proof 
    show "inj_on (\<lambda>b. (the_elem (f ` b))) (rcosets\<^bsub>G\<^esub> kernel G H f)"
      using f.FactGroup_inj_on unfolding FactGroup_def by auto
    have eq: "f ` carrier G = carrier H" 
      using subset super_set by blast
    show "(\<lambda>b. the_elem (f ` b)) ` (rcosets\<^bsub>G\<^esub> kernel G H f) = carrier H"
      using f.FactGroup_onto[OF eq] unfolding FactGroup_def by simp
  qed
  
  show "partition (carrier G) (rcosets\<^bsub>G\<^esub> kernel G H f)"
  proof 
    show "\<And>a. a \<in> carrier G \<Longrightarrow>
         \<exists>!b. b \<in> rcosets\<^bsub>G\<^esub> kernel G H f \<and> a \<in> b"
    proof -
      fix a
      assume a_in: "a \<in> carrier G"
      show "\<exists>!b. b \<in> rcosets\<^bsub>G\<^esub> kernel G H f \<and> a \<in> b"
      proof -
       (*exists*)
        have "\<exists>b. b \<in> rcosets\<^bsub>G\<^esub> kernel G H f \<and> a \<in> b"
          using a_in n.rcosets_part_G[OF f.subgroup_kernel]
          by blast
        then show ?thesis
          using group.rcos_disjoint[OF n.is_group f.subgroup_kernel]
          by (auto simp: disjoint_def)
      qed       
    qed
  next
    show "\<And>b. b \<in> rcosets\<^bsub>G\<^esub> kernel G H f \<Longrightarrow> b \<subseteq> carrier G"
      using n.rcosets_part_G f.subgroup_kernel by auto
  qed
   
  (* sizes *)
  have lagr: "card (carrier G) = card (rcosets\<^bsub>G\<^esub> kernel G H f) * card (kernel G H f)" 
        using group.lagrange_finite[OF n.is_group n.fin f.subgroup_kernel] Coset.order_def[of G] by argo
  have k_size: "card (kernel G H f) > 0" 
    using f.subgroup_kernel finite_subset n.subgroupE(1) n.subgroupE(2) by fastforce
  have G_size: "card (carrier G) = totient n"
    using n.order Coset.order_def[of G] by simp
  have H_size: " totient m = card (carrier H)"
    using n.order Coset.order_def[of H] by simp
  also have "\<dots> = card (carrier (G Mod kernel G H f))" 
    using f.FactGroup_iso[OF image_eq] card_image f.FactGroup_inj_on f.FactGroup_onto image_eq by fastforce
  also have "\<dots> = card (carrier G) div card (kernel G H f)"
  proof -    
    have "card (carrier (G Mod kernel G H f)) = 
          card (rcosets\<^bsub>G\<^esub> kernel G H f)" 
      unfolding FactGroup_def by simp
    also have "\<dots> = card (carrier G) div card (kernel G H f)"
      by (simp add: lagr k_size)
    finally show ?thesis by blast
  qed
  also have "\<dots> = totient n div card (kernel G H f)"
    using G_size by argo
  finally have eq: "totient m = totient n div card (kernel G H f)" by simp
  show "card (kernel G H f) = totient n div totient m"
  proof -
    have "totient m \<noteq> 0" 
      using totient_0_iff[of m] assms(4) by blast
    have "card (kernel G H f) dvd totient n" 
      using lagr \<open>card (carrier G) = totient n\<close> by auto
    have "totient m * card (kernel G H f) = totient n"
      unfolding eq using \<open>card (kernel G H f) dvd totient n\<close> by auto
    have "totient n div totient m = totient m * card (kernel G H f) div totient m"
      using \<open>totient m * card (kernel G H f) = totient n\<close> by auto
    also have "\<dots> = card (kernel G H f)"
      using nonzero_mult_div_cancel_left[OF \<open>totient m \<noteq> 0\<close>] by blast
    finally show ?thesis by auto
  qed

  show "card (rcosets\<^bsub>G\<^esub> kernel G H f) = totient m"
  proof -
    have H_size: " totient m = card (carrier H)"
      using n.order Coset.order_def[of H] by simp
    also have "\<dots> = card (carrier (G Mod kernel G H f))" 
      using f.FactGroup_iso[OF image_eq] card_image f.FactGroup_inj_on f.FactGroup_onto image_eq by fastforce
    also have "card (carrier (G Mod kernel G H f)) = 
          card (rcosets\<^bsub>G\<^esub> kernel G H f)" 
      unfolding FactGroup_def by simp 
    finally show "card (rcosets\<^bsub>G\<^esub> kernel G H f) = totient m"
      by argo
  qed

  assume "b \<in> rcosets\<^bsub>G\<^esub> kernel G H f"
  then show "b \<noteq> {}"
  proof -
    have "card b = card (kernel G H f)"
      using \<open>b \<in> rcosets\<^bsub>G\<^esub> kernel G H f\<close> f.subgroup_kernel n.card_rcosets_equal n.subgroupE(1) by auto
    then have "card b > 0" 
      by (simp add: k_size)
    then show ?thesis by auto
  qed

  assume b_cos: "b \<in> rcosets\<^bsub>G\<^esub> kernel G H f"
  show "card (kernel G H f) = card b" 
    using group.card_rcosets_equal[OF n.is_group b_cos] 
          f.subgroup_kernel subgroup.subset by blast    
qed


lemma primitive_iff_separable_lemma:
 assumes prod: "(\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n) \<and> primitive_dchar d \<Phi>"
 assumes \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close> \<open>k > 1\<close>
 shows "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m) * unity_root d m) =
        (totient k div totient d) * (\<Sum>m | m \<in> {1..d} \<and> coprime m d. \<Phi>(m) * unity_root d m)"
proof -
  from assms interpret \<Phi>: primitive_dchar d "residue_mult_group d" \<Phi>
    by auto
  define G where "G = residue_mult_group k"
  define H where "H = residue_mult_group d"
  define f where "f = (\<lambda>t. t mod d)" 
  
  from residue_mult_group_kernel_partition(2)[OF \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close>]
  have fin_cosets: "finite (rcosets\<^bsub>G\<^esub> kernel G H f)"         
   using \<open>1 < d\<close> card_infinite by (fastforce simp: G_def H_def f_def)
          
  have fin_G: "finite (carrier G)"
    unfolding G_def residue_mult_group_def by simp
  
  have eq: "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m) * unity_root d m) =
         (\<Sum>m | m \<in> carrier G . \<Phi>(m) * unity_root d m)"
   unfolding residue_mult_group_def totatives_def G_def
   by (rule sum.cong,auto)
  also have "\<dots> = sum (\<lambda>m. \<Phi>(m) * unity_root d m) (carrier G)" by simp
  also have eq': "\<dots> = sum (sum (\<lambda>m. \<Phi> m * unity_root d (int m))) (rcosets\<^bsub>G\<^esub> kernel G H f)"
    by (rule disjoint_sum [symmetric])
       (use fin_G fin_cosets residue_mult_group_kernel_partition(1)[OF \<open>d > 1\<close> \<open>k > 0\<close> \<open>d dvd k\<close>] in
          \<open>auto simp: G_def H_def f_def\<close>)
  also have "\<dots> =
   (\<Sum>b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f) . (\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)))" by simp
  finally have 1: "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m) * unity_root d m) =
                   (\<Sum>b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f) . (\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)))" 
    using eq eq' by auto
  have eq''': "\<dots> =
    (\<Sum>b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f) . (totient k div totient d) * (\<Phi> (the_elem (f ` b)) * unity_root d (int (the_elem (f ` b)))))"
  proof (rule sum.cong,simp) 
    fix b
    assume b_in: "b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f)" 
    note b_not_empty = residue_mult_group_kernel_partition(4)
                         [OF \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close> b_in[unfolded G_def H_def f_def]] 
  
    {
      fix m1 m2
      assume m_in: "m1 \<in> b" "m2 \<in> b" 
      have m_mod: "m1 mod d = m2 mod d"   
        using residue_mult_group_coset[OF b_in[unfolded G_def H_def f_def] m_in \<open>k > 1\<close> \<open>d dvd k\<close>]
        by blast
    } note m_mod = this
    {
      fix m1 m2
      assume m_in: "m1 \<in> b" "m2 \<in> b" 
      have "\<Phi> m1 * unity_root d (int m1) = \<Phi> m2 * unity_root d (int m2)"
      proof -
        have \<Phi>_periodic: "periodic_arithmetic \<Phi> d" using \<Phi>.dir_periodic_arithmetic by blast
        have 1: "\<Phi> m1 = \<Phi> m2" 
         using mod_periodic_arithmetic[OF \<open>periodic_arithmetic \<Phi> d\<close> m_mod[OF m_in]] by simp 
       have 2: "unity_root d m1 = unity_root d m2"
         using m_mod[OF m_in] by (intro unity_root_cong) (auto simp: cong_def simp flip: zmod_int)
       from 1 2 show ?thesis by simp
      qed
    } note all_eq_in_coset = this   
   
    from all_eq_in_coset b_not_empty 
    obtain l where l_prop: "l \<in> b \<and> (\<forall>y \<in> b. \<Phi> y * unity_root d (int y) = 
                                \<Phi> l * unity_root d (int l))" by blast
     
    have "(\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)) =
            ((totient k div totient d) * (\<Phi> l * unity_root d (int l)))"
    proof -
      have "(\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)) =
              (\<Sum>m \<in> b. \<Phi> l * unity_root d (int l))"              
          by (rule sum.cong,simp) (use all_eq_in_coset l_prop in blast)
      also have "\<dots> = card b * \<Phi> l * unity_root d (int l)"
        by simp
      also have "\<dots> = (totient k div totient d) * \<Phi> l * unity_root d (int l)"
        using residue_mult_group_kernel_partition(3)[OF \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close>] 
              residue_mult_group_kernel_partition(5)
                [OF \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close> b_in [unfolded G_def H_def f_def]]
        by argo
      finally have 2:
        "(\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)) = 
         (totient k div totient d) * \<Phi> l * unity_root d (int l)" 
        by blast
      from b_not_empty 2 show ?thesis by auto
    qed
    also have "\<dots> = ((totient k div totient d) * (\<Phi> (the_elem (f ` b)) * unity_root d (int (the_elem (f ` b)))))"
    proof -
      have foral: "(\<And>y. y \<in> b \<Longrightarrow> f y = f l)" 
         using m_mod l_prop unfolding f_def by blast
      have eq: "the_elem (f ` b) = f l"
        using the_elem_image_unique[of _ f l, OF b_not_empty foral] by simp
      have per: "periodic_arithmetic \<Phi> d" using prod \<Phi>.dir_periodic_arithmetic by blast
      show ?thesis
        unfolding eq using mod_periodic_arithmetic[OF per, of "l mod d" l]
        by (auto simp: f_def unity_root_mod zmod_int)
    qed
  finally show "(\<Sum>m \<in> b. \<Phi> m * unity_root d (int m)) = 
                 ((totient k div totient d) * (\<Phi> (the_elem (f ` b)) * unity_root d (int (the_elem (f ` b)))))"
    by blast
  qed
  have "\<dots> =
             (\<Sum>b \<in> (rcosets\<^bsub>G\<^esub> kernel G H f) . (totient k div totient d) * (\<Phi> (the_elem (f ` b)) * unity_root d (int (the_elem (f ` b)))))"
    by blast
  also have eq'': "
     \<dots> = (\<Sum>h \<in> carrier H . (totient k div totient d) * (\<Phi> (h) * unity_root d (int (h))))"
    unfolding H_def G_def f_def
    by (rule sum.reindex_bij_betw[OF residue_mult_group_kernel_partition(6)[OF \<open>d > 1\<close> \<open>0 < k\<close> \<open>d dvd k\<close>]])
  finally have 2: "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m) * unity_root d m) = 
                  (totient k div totient d)*(\<Sum>h \<in> carrier H .  (\<Phi> (h) * unity_root d (int (h))))"
    using 1 by (simp add: eq'' eq''' sum_distrib_left)
  also have "\<dots> = (totient k div totient d)*(\<Sum>m | m \<in> {1..d} \<and> coprime m d . (\<Phi> (m) * unity_root d (int (m))))"
    unfolding H_def residue_mult_group_def by (simp add: totatives_def Suc_le_eq)
  finally show ?thesis by simp
qed


text \<open>Theorem 8.19\<close>
theorem (in dcharacter) primitive_iff_separable:
  "primitive_dchar n \<chi> \<longleftrightarrow> (\<forall>k>0. separable k)"
proof (cases "\<chi> = principal_dchar n")
  case True
  thus ?thesis
    using principal_not_primitive principal_not_totally_separable by auto
next
  case False
  note nonprincipal = this
  show ?thesis
  proof 
    assume "primitive_dchar n \<chi>" 
    then interpret A: primitive_dchar n "residue_mult_group n" \<chi> by auto
    show "(\<forall>k. k > 0 \<longrightarrow> separable k)" 
      using n A.primitive_encoding(2) by blast
  next
    assume tot_separable: "\<forall>k>0. separable k" 
    {
      assume as: "\<not> primitive_dchar n \<chi>"
      have "\<exists>r. r \<noteq> 0 \<and> \<not> coprime r n \<and> gauss_sum r \<noteq> 0"
      proof -
        from n have "n > 0" by simp
        define d where "d = conductor"
        have "d > 0" unfolding d_def using conductor_gr_0 .
        then have "d > 1" using nonprincipal d_def conductor_eq_1_iff_principal by auto
        have "d < n" unfolding d_def using nonprimitive_imp_conductor_less[OF as] .
        have "d dvd n" unfolding d_def using conductor_dvd by blast
        define r where "r = n div d"
        have 0: "r \<noteq> 0" unfolding r_def 
          using \<open>0 < n\<close> \<open>d dvd n\<close> dvd_div_gt0 by auto
        have "gcd r n > 1" 
          unfolding r_def 
        proof -  
          have "n div d > 1" using \<open>1 < n\<close> \<open>d < n\<close> \<open>d dvd n\<close> by auto
          have "n div d dvd n" using \<open>d dvd n\<close> by force 
          have "gcd (n div d) n = n div d" using gcd_nat.absorb1[OF \<open>n div d dvd n\<close>] by blast
          then show "1 < gcd (n div d) n" using \<open>n div d > 1\<close> by argo
        qed
        then have 1: "\<not> coprime r n" by auto
        define \<chi>\<^sub>1 where "\<chi>\<^sub>1 = principal_dchar n"
        from primitive_principal_form[OF nonprincipal]
        obtain \<Phi> where 
           prod: "(\<forall>k. \<chi>(k) = \<Phi>(k)*\<chi>\<^sub>1(k)) \<and> primitive_dchar d \<Phi>" 
          using d_def unfolding \<chi>\<^sub>1_def by blast
        then have prod1: "(\<forall>k. \<chi>(k) = \<Phi>(k)*\<chi>\<^sub>1(k))" "primitive_dchar d \<Phi>" by blast+ 
        then interpret \<Phi>: primitive_dchar d "residue_mult_group d" \<Phi>
          by auto
    
        have "gauss_sum r  = (\<Sum>m = 1..n . \<chi>(m) * unity_root n (m*r))"
          unfolding gauss_sum_def by blast
        also have "\<dots> = (\<Sum>m = 1..n . \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root n (m*r))"
          by (rule sum.cong,auto simp add: prod) 
        also have "\<dots> = (\<Sum>m | m \<in> {1..n} \<and> coprime m n. \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root n (m*r))"
          by (intro sum.mono_neutral_right) (auto simp: \<chi>\<^sub>1_def principal_dchar_def)
        also have "\<dots> = (\<Sum>m | m \<in> {1..n} \<and> coprime m n. \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root d m)"
        proof (rule sum.cong,simp)
          fix x
          assume "x \<in> {m \<in> {1..n}. coprime m n}" 
          have "unity_root n (int (x * r)) = unity_root d (int x)"
            using unity_div_num[OF \<open>n > 0\<close> \<open>d > 0\<close> \<open>d dvd n\<close>]
            by (simp add: algebra_simps r_def)
          then show "\<Phi> x * \<chi>\<^sub>1 x * unity_root n (int (x * r)) =
                     \<Phi> x * \<chi>\<^sub>1 x * unity_root d (int x)" by auto
        qed
        also have "\<dots> = (\<Sum>m | m \<in> {1..n} \<and> coprime m n. \<Phi>(m) * unity_root d m)"
          by (rule sum.cong,auto simp add: \<chi>\<^sub>1_def principal_dchar_def)
        also have "\<dots> = (totient n div totient d) * (\<Sum>m | m \<in> {1..d} \<and> coprime m d. \<Phi>(m) * unity_root d m)"
          using primitive_iff_separable_lemma[OF prod \<open>d > 1\<close> \<open>n > 0\<close> \<open>d dvd n\<close> \<open>n > 1\<close>] by blast
        also have "\<dots> = (totient n div totient d) * \<Phi>.gauss_sum 1"
        proof -
          have "\<Phi>.gauss_sum 1 = (\<Sum>m = 1..d . \<Phi> m * unity_root d (int (m )))"
            by (simp add: \<Phi>.gauss_sum_def)
          also have "\<dots> = (\<Sum>m | m \<in> {1..d} . \<Phi> m * unity_root d (int m))"
            by (rule sum.cong,auto)
          also have "\<dots> = (\<Sum>m | m \<in> {1..d} \<and> coprime m d. \<Phi>(m) * unity_root d m)"
            by (rule sum.mono_neutral_right) (use \<Phi>.eq_zero in auto)
          finally have "\<Phi>.gauss_sum 1 = (\<Sum>m | m \<in> {1..d} \<and> coprime m d. \<Phi>(m) * unity_root d m)"
            by blast
          then show ?thesis by metis
        qed
        finally have g_expr: "gauss_sum r = (totient n div totient d) * \<Phi>.gauss_sum 1"
          by blast
        have t_non_0: "totient n div totient d \<noteq> 0"
          by (simp add: \<open>0 < n\<close> \<open>d dvd n\<close> dvd_div_gt0 totient_dvd) 
        have "(norm (\<Phi>.gauss_sum 1))\<^sup>2 = d" 
          using \<Phi>.primitive_encoding(3) by simp  
        then have "\<Phi>.gauss_sum 1 \<noteq> 0" 
          using \<open>0 < d\<close> by auto
        then have 2: "gauss_sum r \<noteq> 0"
          using g_expr t_non_0 by auto
        from 0 1 2 show "\<exists>r. r \<noteq> 0 \<and> \<not> coprime r n \<and> gauss_sum r \<noteq> 0" 
          by blast
      qed
    }
    note contr = this
   
    show "primitive_dchar n \<chi>"
    proof (rule ccontr)
      assume "\<not> primitive_dchar n \<chi>"
      then obtain r where 1: "r \<noteq> 0 \<and> \<not> coprime r n \<and> gauss_sum r \<noteq> 0"
        using contr by blast
      from global_separability_condition tot_separable 
      have 2: "(\<forall>k>0. \<not> coprime k n \<longrightarrow> gauss_sum k = 0)" 
        by blast
      from 1 2 show "False" by blast
    qed
  qed
qed


text\<open>Theorem 8.20\<close>
theorem (in primitive_dchar) fourier_primitive:
  includes no_vec_lambda_notation
  fixes \<tau> :: complex
  defines "\<tau> \<equiv> gauss_sum 1 / sqrt n"
  shows   "\<chi> m = \<tau> / sqrt n * (\<Sum>k=1..n. cnj (\<chi> k) * unity_root n (-m*k))"
  and     "norm \<tau> = 1"
proof -
  have chi_not_principal: "\<chi> \<noteq> principal_dchar n" 
    using principal_not_totally_separable primitive_encoding(2) by blast

  then have case_0: "(\<Sum>k=1..n. \<chi> k) = 0"
  proof -
    have "sum \<chi> {0..n-1} = sum \<chi> {1..n}"
      using periodic_arithmetic_sum_periodic_arithmetic_shift[OF dir_periodic_arithmetic, of 1] n
      by auto
    also have "{0..n-1} = {..<n}"
      using n by auto
    finally show "(\<Sum>n = 1..n . \<chi> n) = 0"
      using sum_dcharacter_block chi_not_principal by simp
  qed

  have "\<chi> m =
    (\<Sum>k = 1..n. 1 / of_nat n * gauss_sum_int (- int k) *
      unity_root n (int (m * k)))"
    using dcharacter_fourier_expansion[of m] by auto
  also have "\<dots> = (\<Sum>k = 1..n. 1 / of_nat n * gauss_sum (nat ((- k) mod n)) *
      unity_root n (int (m * k)))"
    by (auto simp: gauss_sum_int_conv_gauss_sum)
  also have "\<dots> = (\<Sum>k = 1..n. 1 / of_nat n * cnj (\<chi> (nat ((- k) mod n))) * gauss_sum 1 * unity_root n (int (m * k)))"
  proof (rule sum.cong,simp)
    fix k
    assume "k \<in> {1..n}" 
    have "gauss_sum (nat (- int k mod int n)) = 
          cnj (\<chi> (nat (- int k mod int n))) * gauss_sum 1"
    proof (cases "nat ((- k) mod n) > 0")
      case True
      then show ?thesis 
        using mp[OF spec[OF primitive_encoding(2)] True]
        unfolding separable_def by auto
    next
      case False
      then have nat_0: "nat ((- k) mod n) = 0" by blast
      show ?thesis 
      proof -
        have "gauss_sum (nat (- int k mod int n)) = gauss_sum 0" 
          using nat_0 by argo
        also have "\<dots> =  (\<Sum>m = 1..n. \<chi> m)" 
          unfolding gauss_sum_def by (rule sum.cong) auto
        also have "\<dots> = 0" using case_0 by blast
        finally have 1: "gauss_sum (nat (- int k mod int n)) = 0"
          by blast

        have 2: "cnj (\<chi> (nat (- int k mod int n))) = 0"
          using nat_0 zero_eq_0 by simp
        show ?thesis using 1 2 by simp
      qed
    qed
    then show "1 / of_nat n * gauss_sum (nat (- int k mod int n)) * unity_root n (int (m * k)) =
               1 / of_nat n * cnj (\<chi> (nat (- int k mod int n))) * gauss_sum 1 * unity_root n (int (m * k))" 
      by auto
  qed
  also have "\<dots> = (\<Sum>k = 1..n. 1 / of_nat n * cnj (\<chi> (nat (- int k mod int n))) * 
                    gauss_sum 1 * unity_root n (int (m * (nat (int k mod int n)))))"
  proof (rule sum.cong,simp)
    fix x   
    assume "x \<in> {1..n}" 
    have "unity_root n (m * x) = unity_root n (m * x mod n)"
      using unity_root_mod_nat[of n "m*x"] by (simp add: nat_mod_as_int)
    also have "\<dots> = unity_root n (m * (x mod n))"
      by (rule unity_root_cong)
         (auto simp: cong_def mod_mult_right_eq simp flip: zmod_int of_nat_mult)
    finally have "unity_root n (m * x) = unity_root n (m * (x mod n))" by blast
    then show "1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) *
                 gauss_sum 1 * unity_root n (int (m * x)) =
               1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) * gauss_sum 1 *
                 unity_root n (int (m * nat (int x mod int n)))" 
      by (simp add: nat_mod_as_int)    
  qed
  also have "\<dots> = (\<Sum>k = 0..n-1. 1 / of_nat n * cnj (\<chi> k) * gauss_sum 1 * unity_root n (- int (m * k)))"
  proof -
    have b: "bij_betw (\<lambda>k. nat((-k) mod n)) {1..n} {0..n-1}"
      unfolding bij_betw_def
    proof 
      show "inj_on (\<lambda>k. nat (- int k mod int n)) {1..n}"
        unfolding inj_on_def
      proof (safe)
        fix x y
        assume a1: "x \<in> {1..n}" "y \<in> {1..n}"
        assume a2: "nat (- x mod n) = nat (- y mod n)"
        then have "(- x) mod n = - y mod n"
          using n eq_nat_nat_iff by auto
        then have "[-int x = - int y] (mod n)" 
          using cong_def by blast
        then have "[x = y] (mod n)" 
          by (simp add: cong_int_iff cong_minus_minus_iff)
        then have cong: "x mod n = y mod n" using cong_def by blast
        then show "x = y"
        proof (cases "x = n")
          case True then show ?thesis using cong a1(2) by auto
        next
          case False
          then have "x mod n = x" using a1(1) by auto
          then have "y \<noteq> n" using a1(1) local.cong by fastforce
          then have "y mod n = y" using a1(2) by auto
          then show ?thesis using \<open>x mod n = x\<close> cong by linarith
        qed
      qed
      show "(\<lambda>k. nat (- int k mod int n)) ` {1..n} = {0..n - 1}"
        unfolding image_def 
      proof
        let ?A = "{y. \<exists>x\<in>{1..n}. y = nat (- int x mod int n)}"
        let ?B = "{0..n - 1}" 
        show "?A \<subseteq> ?B" 
        proof
          fix y
          assume "y \<in> {y. \<exists>x\<in>{1..n}. y = nat (- int x mod int n)}"
          then obtain x where "x\<in>{1..n} \<and> y = nat (- int x mod int n)" by blast
          then show "y \<in> {0..n - 1}" by (simp add: nat_le_iff of_nat_diff)
        qed
        show "?A \<supseteq> ?B" 
        proof 
          fix x
          assume 1: "x \<in> {0..n-1}"
          then have "n - x \<in> {1..n}"
            using n by auto
          have "x = nat (- int (n-x) mod int n)"
          proof -
            have "nat (- int (n-x) mod int n) = nat (int x) mod int n"
              apply(simp add: int_ops(6),rule conjI)
              using \<open>n - x \<in> {1..n}\<close> by force+
            also have "\<dots> = x" 
              using 1 n by auto
            finally show ?thesis by presburger
          qed
          then show "x \<in> {y. \<exists>x\<in>{1..n}. y = nat (- int x mod int n)}"
            using \<open>n - x \<in> {1..n}\<close> by blast
        qed
      qed
    qed
    show ?thesis 
    proof -
      have 1: "(\<Sum>k = 1..n. 1 / of_nat n * cnj (\<chi> (nat (- int k mod int n))) *
        gauss_sum 1 * unity_root n (int (m * nat (int k mod int n)))) = 
            (\<Sum>x = 1..n. 1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) *
        gauss_sum 1 * unity_root n (- int (m * nat (- int x mod int n))))"
      proof (rule sum.cong,simp)
        fix x        
        have "(int m * (int x mod int n)) mod n = (m*x) mod n"
          by (simp add: mod_mult_right_eq zmod_int)
        also have "\<dots> = (- ((- int (m*x) mod n))) mod n"
          by (simp add: mod_minus_eq of_nat_mod)
        have "(int m * (int x mod int n)) mod n = (- (int m * (- int x mod int n))) mod n"
          apply(subst mod_mult_right_eq,subst add.inverse_inverse[symmetric],subst (5) add.inverse_inverse[symmetric])
          by (subst minus_mult_minus,subst mod_mult_right_eq[symmetric],auto)
        then have "unity_root n (int m * (int x mod int n)) =
                   unity_root n (- (int m * (- int x mod int n)))"
          using unity_root_mod[of n "int m * (int x mod int n)"] 
                 unity_root_mod[of n " - (int m * (- int x mod int n))"] by argo
        then show "1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) *
         gauss_sum 1 *
         unity_root n (int (m * nat (int x mod int n))) =
         1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) *
         gauss_sum 1 *
         unity_root n (- int (m * nat (- int x mod int n)))" by auto
      qed
      also have 2: "(\<Sum>x = 1..n. 1 / of_nat n * cnj (\<chi> (nat (- int x mod int n))) *
          gauss_sum 1 * unity_root n (- int (m * nat (- int x mod int n)))) =
            (\<Sum>md = 0..n - 1. 1 / of_nat n * cnj (\<chi> md) * gauss_sum 1 *
          unity_root n (- int (m * md)))"
       using sum.reindex_bij_betw[OF b, of "\<lambda>md. 1 / of_nat n * cnj (\<chi> md) * gauss_sum 1 * unity_root n (- int (m * md))"]
       by blast
      also have 3: "\<dots> = (\<Sum>k = 0..n - 1.
        1 / of_nat n * cnj (\<chi> k) * gauss_sum 1 *
        unity_root n (- int (m * k)))" by blast
      finally have "(\<Sum>k = 1..n. 1 / of_nat n * cnj (\<chi> (nat (- int k mod int n))) *
        gauss_sum 1 * unity_root n (int (m * nat (int k mod int n)))) = 
          (\<Sum>k = 0..n - 1.
        1 / of_nat n * cnj (\<chi> k) * gauss_sum 1 *
        unity_root n (- int (m * k)))" using 1 2 3 by argo
      then show ?thesis by blast
    qed
  qed
  also have "\<dots> = (\<Sum>k = 1..n.
         1 / of_nat n * cnj (\<chi> k) * gauss_sum 1 *
         unity_root n (- int (m * k)))"
  proof -
    let ?f = "(\<lambda>k. 1 / of_nat n * cnj (\<chi> k) * gauss_sum 1 * unity_root n (- int (m * k)))"
    have "?f 0 = 0" 
      using zero_eq_0 by auto
    have "?f n = 0" 
      using zero_eq_0 mod_periodic_arithmetic[OF dir_periodic_arithmetic, of n 0]
      by simp
    have "(\<Sum>n = 0..n - 1. ?f n) = (\<Sum>n = 1..n - 1. ?f n)"
      using sum_shift_lb_Suc0_0[of ?f, OF \<open>?f 0 = 0\<close>]
      by auto
    also have "\<dots> = (\<Sum>n = 1..n. ?f n)"
    proof (rule sum.mono_neutral_left,simp,simp,safe)
      fix i
      assume "i \<in> {1..n}" "i \<notin> {1..n - 1}" 
      then have "i = n" using n by auto
      then show "1 / of_nat n * cnj (\<chi> i) * gauss_sum 1 * unity_root n (- int (m * i)) = 0" 
        using \<open>?f n = 0\<close> by blast
    qed
    finally show ?thesis by blast
  qed
  also have "\<dots> = (\<Sum>k = 1..n. (\<tau> / sqrt n) * cnj (\<chi> k) * unity_root n (- int (m * k)))"
  proof (rule sum.cong,simp)
    fix x
    assume "x \<in> {1..n}"
    have "\<tau> / sqrt (real n) = 1 / of_nat n  * gauss_sum 1"
    proof -
      have "\<tau> / sqrt (real n) = gauss_sum 1 / sqrt n / sqrt n"
        using assms by auto
      also have "\<dots> = gauss_sum 1 / (sqrt n * sqrt n)"
        by (subst divide_divide_eq_left,subst of_real_mult,blast) 
      also have "\<dots> = gauss_sum 1 / n" 
        using real_sqrt_mult_self by simp
      finally show ?thesis by simp
    qed
    then show 
     "1 / of_nat n * cnj (\<chi> x) * gauss_sum 1 * unity_root n (- int (m * x)) =
      (\<tau> / sqrt n) * cnj (\<chi> x) * unity_root n (- int (m * x))" by simp
  qed
  also have "\<dots> = \<tau> / sqrt (real n) * 
         (\<Sum>k = 1..n. cnj (\<chi> k) * unity_root n (- int (m * k)))"
  proof -
    have "(\<Sum>k = 1..n. \<tau> / sqrt (real n) * cnj (\<chi> k) * unity_root n (- int (m * k))) = 
          (\<Sum>k = 1..n. \<tau> / sqrt (real n) * (cnj (\<chi> k) *  unity_root n (- int (m * k))))" 
      by (rule sum.cong,simp, simp add: algebra_simps)
    also have "\<dots> = \<tau> / sqrt (real n) * (\<Sum>k = 1..n. cnj (\<chi> k) * unity_root n (- int (m * k)))"
      by (rule sum_distrib_left[symmetric])
    finally show ?thesis by blast
  qed

  finally show "\<chi> m = (\<tau> / sqrt (real n)) *
    (\<Sum>k=1..n. cnj (\<chi> k) * unity_root n (- int m * int k))" by simp

  have 1: "norm (gauss_sum 1) = sqrt n" 
    using gauss_sum_1_mod_square_eq_k[OF primitive_encoding(2)]
    by (simp add: cmod_def)
  from assms have 2: "norm \<tau> = norm (gauss_sum 1) / \<bar>sqrt n\<bar>"
    by (simp add: norm_divide)
  show "norm \<tau> = 1" using 1 2 n by simp
qed

unbundle vec_lambda_notation

end