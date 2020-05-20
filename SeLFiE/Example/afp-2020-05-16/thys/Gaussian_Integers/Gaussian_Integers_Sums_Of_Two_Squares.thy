(*
  File:     Gaussian_Integers_Sums_Of_Two_Squares.thy
  Author:   Manuel Eberl, TU München

  Application of Gaussian integers to determining which natural numbers can be written as a sum
  of two squares
*)
subsection \<open>Sums of two squares\<close>
theory Gaussian_Integers_Sums_Of_Two_Squares
  imports Gaussian_Integers
begin

text \<open>
  As an application, we can now easily prove that a positive natural number is the
  sum of two squares if and only if all prime factors congruent 3 modulo 4 have even
  multiplicity.
\<close>

inductive sum_of_2_squares_nat :: "nat \<Rightarrow> bool" where
  "sum_of_2_squares_nat (a ^ 2 + b ^ 2)"

lemma sum_of_2_squares_nat_altdef: "sum_of_2_squares_nat n \<longleftrightarrow> n \<in> range gauss_int_norm"
proof (safe elim!: sum_of_2_squares_nat.cases)
  fix a b :: nat
  have "a ^ 2 + b ^ 2 = gauss_int_norm (of_nat a + \<i>\<^sub>\<int> * of_nat b)"
    by (auto simp: gauss_int_norm_def nat_add_distrib nat_power_eq)
  thus "a ^ 2 + b ^ 2 \<in> range gauss_int_norm" by blast
next
  fix z :: gauss_int
  have "gauss_int_norm z = nat \<bar>ReZ z\<bar> ^ 2 + nat \<bar>ImZ z\<bar> ^ 2"
    by (auto simp: gauss_int_norm_def nat_add_distrib simp flip: nat_power_eq)
  thus "sum_of_2_squares_nat (gauss_int_norm z)"
    by (auto intro: sum_of_2_squares_nat.intros)
qed

lemma sum_of_2_squares_nat_gauss_int_norm [intro]: "sum_of_2_squares_nat (gauss_int_norm z)"
  by (auto simp: sum_of_2_squares_nat_altdef)

lemma sum_of_2_squares_nat_0 [simp, intro]: "sum_of_2_squares_nat 0" 
  and sum_of_2_squares_nat_1 [simp, intro]: "sum_of_2_squares_nat 1"
  and sum_of_2_squares_nat_Suc_0 [simp, intro]: "sum_of_2_squares_nat (Suc 0)"
  and sum_of_2_squares_nat_2 [simp, intro]: "sum_of_2_squares_nat 2"
  using sum_of_2_squares_nat.intros[of 0 0] sum_of_2_squares_nat.intros[of 0 1]
        sum_of_2_squares_nat.intros[of 1 1] by (simp_all add: numeral_2_eq_2)

lemma sum_of_2_squares_nat_mult [intro]:
  assumes "sum_of_2_squares_nat x" "sum_of_2_squares_nat y"
  shows   "sum_of_2_squares_nat (x * y)"
proof -
  from assms obtain z1 z2 where "x = gauss_int_norm z1" "y = gauss_int_norm z2"
    by (auto simp: sum_of_2_squares_nat_altdef)
  hence "x * y = gauss_int_norm (z1 * z2)"
    by (simp add: gauss_int_norm_mult)
  thus ?thesis by auto
qed

lemma sum_of_2_squares_nat_power [intro]:
  assumes "sum_of_2_squares_nat m"
  shows   "sum_of_2_squares_nat (m ^ n)"
  using assms by (induction n) auto

lemma sum_of_2_squares_nat_prod [intro]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> sum_of_2_squares_nat (f x)"
  shows   "sum_of_2_squares_nat (\<Prod>x\<in>A. f x)"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma sum_of_2_squares_nat_prod_mset [intro]:
  assumes "\<And>x. x \<in># A \<Longrightarrow> sum_of_2_squares_nat x"
  shows   "sum_of_2_squares_nat (prod_mset A)"
  using assms by (induction A) auto

lemma sum_of_2_squares_nat_necessary:
  assumes "sum_of_2_squares_nat n" "n > 0"
  assumes "prime p" "[p = 3] (mod 4)"
  shows   "even (multiplicity p n)"
proof -
  define k where "k = multiplicity p n"
  from assms obtain z where z: "gauss_int_norm z = n"
    by (auto simp: sum_of_2_squares_nat_altdef)
  from assms and z have [simp]: "z \<noteq> 0"
    by auto
  have prime': "prime (of_nat p :: gauss_int)"
    using assms prime_gauss_int_of_nat by blast
  have [simp]: "multiplicity (of_nat p) (gauss_cnj z) = multiplicity (of_nat p) z"
    using multiplicity_gauss_cnj[of "of_nat p" z] by simp
  have "multiplicity (of_nat p) (of_nat n :: gauss_int) =
        multiplicity (of_nat p) (z * gauss_cnj z)"
    using z by (simp add: self_mult_gauss_cnj)
  also have "\<dots> = 2 * multiplicity (of_nat p) z"
    using prime' by (subst prime_elem_multiplicity_mult_distrib) auto
  finally have "multiplicity p n = 2 * multiplicity (of_nat p) z"
    by (subst (asm) multiplicity_gauss_int_of_nat)
  thus ?thesis by auto
qed

lemma sum_of_2_squares_nat_sufficient:
  fixes n :: nat
  assumes "n > 0"
  assumes "\<And>p. p \<in> prime_factors n \<Longrightarrow> [p = 3] (mod 4) \<Longrightarrow> even (multiplicity p n)"
  shows "sum_of_2_squares_nat n"
proof -
  define P2 where "P2 = {p\<in>prime_factors n. [p = 1] (mod 4)}"
  define P3 where "P3 = {p\<in>prime_factors n. [p = 3] (mod 4)}"
  from \<open>n > 0\<close> have "n = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)"
    by (subst prime_factorization_nat) auto
  also have "\<dots> = (\<Prod>p\<in>{2}\<union>P2\<union>P3. p ^ multiplicity p n)"
    using prime_mod_4_cases
    by (intro prod.mono_neutral_left)
       (auto simp: P2_def P3_def in_prime_factors_iff not_dvd_imp_multiplicity_0)
  also have "\<dots> = (\<Prod>p\<in>{2}\<union>P2. p ^ multiplicity p n) * (\<Prod>p\<in>P3. p ^ multiplicity p n)"
    by (intro prod.union_disjoint) (auto simp: P2_def P3_def cong_def)
  also have "(\<Prod>p\<in>{2}\<union>P2. p ^ multiplicity p n) =
               2 ^ multiplicity 2 n * (\<Prod>p\<in>P2. p ^ multiplicity p n)"
    by (subst prod.union_disjoint) (auto simp: P2_def cong_def)
  also have "(\<Prod>p\<in>P3. p ^ multiplicity p n) = (\<Prod>p\<in>P3. (p ^ 2) ^ (multiplicity p n div 2))"
  proof (intro prod.cong refl)
    fix p :: nat assume p: "p \<in> P3"
    have "(p ^ 2) ^ (multiplicity p n div 2) = p ^ (2 * (multiplicity p n div 2))"
      by (simp add: power_mult)
    also have "even (multiplicity p n)"
      using assms p by (auto simp: P3_def)
    hence "2 * (multiplicity p n div 2) = multiplicity p n"
      by simp
    finally show "p ^ multiplicity p n = (p ^ 2) ^ (multiplicity p n div 2)"
      by simp
  qed
  finally have "n = 2 ^ multiplicity 2 n * (\<Prod>p\<in>P2. p ^ multiplicity p n) * 
                      (\<Prod>p\<in>P3. p\<^sup>2 ^ (multiplicity p n div 2))" .

  also have "sum_of_2_squares_nat \<dots>"
  proof (intro sum_of_2_squares_nat_mult sum_of_2_squares_nat_prod; rule sum_of_2_squares_nat_power)
    fix p :: nat assume p: "p \<in> P2"
    with prime_cong_1_mod_4_gauss_int_norm_exists[of p] show "sum_of_2_squares_nat p"
      by (auto simp: P2_def)
  next
    fix p :: nat assume p: "p \<in> P3"
    have "sum_of_2_squares_nat (gauss_int_norm (of_nat p))" ..
    also have "gauss_int_norm (of_nat p) = p ^ 2"
      by simp
    finally show "sum_of_2_squares_nat (p ^ 2)" .
  qed auto
  finally show ?thesis .
qed

theorem sum_of_2_squares_nat_iff:
  "sum_of_2_squares_nat n \<longleftrightarrow>
     n = 0 \<or> (\<forall>p\<in>prime_factors n. [p = 3] (mod 4) \<longrightarrow> even (multiplicity p n))"
  using sum_of_2_squares_nat_necessary[of n] sum_of_2_squares_nat_sufficient[of n] by auto

end