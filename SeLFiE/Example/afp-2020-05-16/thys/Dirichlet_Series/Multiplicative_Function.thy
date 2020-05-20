(*
    File:      Multiplicative_Function.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Multiplicative arithmetic functions\<close>
theory Multiplicative_Function
  imports 
    "HOL-Number_Theory.Number_Theory" 
    Dirichlet_Misc
begin

subsection \<open>Definition\<close>

locale multiplicative_function =
  fixes f :: "nat \<Rightarrow> 'a :: comm_semiring_1"
  assumes zero [simp]: "f 0 = 0"
  assumes one [simp]: "f 1 = 1"
  assumes mult_coprime_aux: "a > 1 \<Longrightarrow> b > 1 \<Longrightarrow> coprime a b \<Longrightarrow> f (a * b) = f a * f b"
begin

lemma Suc_0 [simp]: "f (Suc 0) = 1"
  using one by (simp del: one)
    
lemma mult_coprime:
  assumes "coprime a b"
  shows   "f (a * b) = f a * f b"
proof -
  {fix n :: nat consider "n = 0" | "n = 1" | "n > 1" by force} note P = this
  show ?thesis by (cases a rule: P; cases b rule: P) (simp_all add: mult_coprime_aux assms)
qed

lemma prod_coprime:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> coprime (g x) (g y)"
  shows   "f (prod g A) = (\<Prod>x\<in>A. f (g x))"
  using assms
proof (induction rule: infinite_finite_induct)
  case (insert x A)
  from insert have "f (prod g (insert x A)) = f (g x * prod g A)" by simp
  also have "\<dots> = f (g x) * f (prod g A)" using insert.prems insert.hyps
    by (auto intro: mult_coprime prod_coprime_right)
  also have "\<dots> = (\<Prod>x\<in>insert x A. f (g x))" using insert by simp
  finally show ?case .
qed auto

lemma prod_prime_factors:
  assumes "n > 0"
  shows   "f n = (\<Prod>p\<in>prime_factors n. f (p ^ multiplicity p n))"
proof -
  have "n = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)"
    using Primes.prime_factorization_nat assms by blast
  also have "f \<dots> = (\<Prod>p\<in>prime_factors n. f (p ^ multiplicity p n))"
    by (rule prod_coprime) (auto simp add: in_prime_factors_imp_prime primes_coprime) 
  finally show ?thesis .
qed

lemma multiplicative_sum_divisors: "multiplicative_function (\<lambda>n. \<Sum>d | d dvd n. f d)"
proof
  fix a b :: nat assume ab: "a > 1" "b > 1" "coprime a b"
  hence "(\<Sum>d | d dvd a * b. f d) = (\<Sum>r | r dvd a. \<Sum>s | s dvd b. f (r * s))"
    by (intro sum_divisors_coprime_mult)
  also have "\<dots> = (\<Sum>r | r dvd a. \<Sum>s | s dvd b. f r * f s)"
    using ab(3)
    by (auto intro!: sum.cong intro: mult_coprime coprime_imp_coprime dvd_trans)
  also have "\<dots> = (\<Sum>r | r dvd a. f r) * (\<Sum>s | s dvd b. f s)"
    by (subst sum_distrib_right, subst sum_distrib_left) simp_all
  finally show "(\<Sum>d | d dvd a * b. f d) = (\<Sum>r | r dvd a. f r) * (\<Sum>s | s dvd b. f s)" .
qed auto

end

locale multiplicative_function' = multiplicative_function f for f :: "nat \<Rightarrow> 'a :: comm_semiring_1" +
  fixes f_prime_power :: "nat \<Rightarrow> nat \<Rightarrow> 'a" and f_prime :: "nat \<Rightarrow> 'a"
  assumes prime_power: "prime p \<Longrightarrow> k > 0 \<Longrightarrow> f (p ^ k) = f_prime_power p k"
  assumes prime_aux: "prime p \<Longrightarrow> f_prime_power p 1 = f_prime p"
begin
  
lemma prime: "prime p \<Longrightarrow> f p = f_prime p"
  using prime_power[of p 1] prime_aux[of p] by simp

lemma prod_prime_factors':
  assumes "n > 0"
  shows   "f n = (\<Prod>p\<in>prime_factors n. f_prime_power p (multiplicity p n))"
  by (subst prod_prime_factors[OF assms(1)])
     (intro prod.cong refl prime_power, auto simp: prime_factors_multiplicity)

lemma efficient_code_aux:
  assumes "n > 0" "set ps = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n" "distinct ps"
  shows   "f n = (\<Prod>(p,d) \<leftarrow> ps. f_prime_power p (Suc d))"
proof -
  from assms have 
    "(\<Prod>(p,d) \<leftarrow> ps. f_prime_power p (Suc d)) = 
       (\<Prod>(p,d)\<in>(\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n. f_prime_power p (Suc d))"
    by (subst prod.distinct_set_conv_list [symmetric]) simp_all
  also have "\<dots> = (\<Prod>x\<in>prime_factors n. f_prime_power x (multiplicity x n))"
    by (subst prod.reindex) (auto simp: inj_on_def prime_factors_multiplicity intro!: prod.cong)
  also have "\<dots> = f n" by (rule prod_prime_factors' [symmetric]) fact+
  finally show ?thesis ..
qed

lemma efficient_code:
  assumes "set (ps ()) = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n" "distinct (ps ())"
  shows   "f n = (if n = 0 then 0 else (\<Prod>(p,d) \<leftarrow> ps (). f_prime_power p (Suc d)))"
  using efficient_code_aux[of n "ps ()"] assms by simp

end


locale completely_multiplicative_function =
  fixes f :: "nat \<Rightarrow> 'a :: comm_semiring_1"
  assumes zero_aux: "f 0 = 0"
  assumes one_aux:  "f (Suc 0) = 1"
  assumes mult_aux: "a > 1 \<Longrightarrow> b > 1 \<Longrightarrow> f (a * b) = f a * f b"
begin
  
lemma mult: "f (a * b) = f a * f b"
proof -
  {fix n :: nat consider "n = 0" | "n = 1" | "n > 1" by force} note P = this
  show ?thesis by (cases a rule: P; cases b rule: P) (simp_all add: zero_aux one_aux mult_aux)
qed

sublocale multiplicative_function f
  by standard (simp_all add: zero_aux one_aux mult)
 
lemma prod: "f (prod g A) = (\<Prod>x\<in>A. f (g x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: mult)
    
lemma power: "f (n ^ m) = f n ^ m"
  by (induction m) (simp_all add: mult)

lemma prod_prime_factors': "n > 0 \<Longrightarrow> f n = (\<Prod>p\<in>prime_factors n. f p ^ multiplicity p n)"
  by (subst prime_factorization_nat) (simp_all add: prod power)

end

locale completely_multiplicative_function' =
  completely_multiplicative_function f for f :: "nat \<Rightarrow> 'a :: comm_semiring_1" +
  fixes f_prime :: "nat \<Rightarrow> 'a"
  assumes f_prime: "prime p \<Longrightarrow> f p = f_prime p"
begin

lemma prod_prime_factors'': "n > 0 \<Longrightarrow> f n = (\<Prod>p\<in>prime_factors n. f_prime p ^ multiplicity p n)"
  by (subst prod_prime_factors') (auto simp: f_prime prime_factors_multiplicity intro!: prod.cong)
    
lemma efficient_code_aux:
  assumes "n > 0" "set ps = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n" "distinct ps"
  shows   "f n = (\<Prod>(p,d) \<leftarrow> ps. f_prime p ^ Suc d)"
proof -
  from assms have 
    "(\<Prod>(p,d) \<leftarrow> ps. f_prime p ^ Suc d) = 
       (\<Prod>(p,d)\<in>(\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n. f_prime p ^ Suc d)"
    by (subst prod.distinct_set_conv_list [symmetric]) simp_all
  also have "\<dots> = (\<Prod>x\<in>prime_factors n. f_prime x ^ multiplicity x n)"
    by (subst prod.reindex) (auto simp: inj_on_def prime_factors_multiplicity 
                                  simp del: power_Suc intro!: prod.cong)
  also have "\<dots> = f n" by (rule prod_prime_factors'' [symmetric]) fact+
  finally show ?thesis ..
qed

lemma efficient_code:
  assumes "set (ps ()) = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n" "distinct (ps ())"
  shows   "f n = (if n = 0 then 0 else (\<Prod>(p,d) \<leftarrow> ps (). f_prime p ^ Suc d))"
  using efficient_code_aux[of n "ps ()"] assms by simp

end
  
lemma multiplicative_function_eqI:
  assumes "multiplicative_function f" "multiplicative_function g"
  assumes "\<And>p k. prime p \<Longrightarrow> k > 0 \<Longrightarrow> f (p ^ k) = g (p ^ k)"
  shows   "f n = g n"
proof -
  interpret f: multiplicative_function f by fact
  interpret g: multiplicative_function g by fact
  show ?thesis
  proof (cases "n > 0")
    case True
    thus ?thesis 
      using f.prod_prime_factors[OF True] g.prod_prime_factors[OF True]
      by (auto intro!: prod.cong assms simp: prime_factors_multiplicity)
  qed simp_all
qed

lemma multiplicative_function_of_natI:
  "multiplicative_function f \<Longrightarrow> multiplicative_function (\<lambda>n. of_nat (f n))"
  unfolding multiplicative_function_def by auto

lemma multiplicative_function_of_natD:
  "multiplicative_function (\<lambda>n. of_nat (f n) :: 'a :: {ring_char_0, comm_semiring_1}) \<Longrightarrow> 
     multiplicative_function f"
  unfolding multiplicative_function_def 
  by (auto simp: of_nat_mult [symmetric] of_nat_eq_1_iff simp del: of_nat_mult)

lemma multiplicative_function_mult:
  assumes "multiplicative_function f"  "multiplicative_function g"
  shows   "multiplicative_function (\<lambda>n. f n * g n)"
proof
  interpret f: multiplicative_function f by fact
  interpret g: multiplicative_function g by fact
  show "f 0 * g 0 = 0" "f 1 * g 1 = 1" by simp_all
  fix a b :: nat assume "a > 1" "b > 1" "coprime a b"
  thus "f (a * b) * g (a * b) = (f a * g a) * (f b * g b)"
    by (simp_all add: f.mult_coprime g.mult_coprime mult_ac)
qed

lemma multiplicative_function_inverse:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "multiplicative_function f"
  shows   "multiplicative_function (\<lambda>n. inverse (f n))"
proof
  interpret f: multiplicative_function f by fact
  show "inverse (f 0) = 0" "inverse (f 1) = 1" by simp_all
  fix a b :: nat assume "a > 1" "b > 1" "coprime a b"
  thus "inverse (f (a * b)) = inverse (f a) * inverse (f b)"
    by (simp_all add: f.mult_coprime field_simps)
qed

lemma multiplicative_function_divide:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "multiplicative_function f"  "multiplicative_function g"
  shows   "multiplicative_function (\<lambda>n. f n / g n)"
proof -
  have "multiplicative_function (\<lambda>n. f n * inverse (g n))"
    by (intro multiplicative_function_mult multiplicative_function_inverse assms)
  also have "(\<lambda>n. f n * inverse (g n)) = (\<lambda>n. f n / g n)" 
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma completely_multiplicative_function_mult:
  assumes "completely_multiplicative_function f" "completely_multiplicative_function g"
  shows   "completely_multiplicative_function (\<lambda>n. f n * g n)"
proof
  interpret f: completely_multiplicative_function f by fact
  interpret g: completely_multiplicative_function g by fact
  show "f 0 * g 0 = 0" "f (Suc 0) * g (Suc 0) = 1" by simp_all
  fix a b :: nat assume "a > 1" "b > 1"
  thus "f (a * b) * g (a * b) = (f a * g a) * (f b * g b)"
    by (simp_all add: f.mult g.mult mult_ac)
qed

lemma completely_multiplicative_function_inverse:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "completely_multiplicative_function f"
  shows   "completely_multiplicative_function (\<lambda>n. inverse (f n))"
proof
  interpret f: completely_multiplicative_function f by fact
  show "inverse (f 0) = 0" "inverse (f (Suc 0)) = 1" by simp_all
  fix a b :: nat assume "a > 1" "b > 1"
  thus "inverse (f (a * b)) = inverse (f a) * inverse (f b)"
    by (simp_all add: f.mult field_simps)
qed

lemma completely_multiplicative_function_divide:
  fixes f :: "nat \<Rightarrow> 'a :: field"
  assumes "completely_multiplicative_function f"  "completely_multiplicative_function g"
  shows   "completely_multiplicative_function (\<lambda>n. f n / g n)"
proof -
  have "completely_multiplicative_function (\<lambda>n. f n * inverse (g n))"
    by (intro completely_multiplicative_function_mult 
              completely_multiplicative_function_inverse assms)
  also have "(\<lambda>n. f n * inverse (g n)) = (\<lambda>n. f n / g n)" 
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma (in multiplicative_function) completely_multiplicativeI:
  assumes "\<And>p k. prime p \<Longrightarrow> k > 0 \<Longrightarrow> f (p ^ k) = f p ^ k"
  shows   "completely_multiplicative_function f"
proof
  fix m n :: nat assume mn: "m > 1" "n > 1"
  define P where "P = prime_factors (m * n)"
  have "f (m * n) = (\<Prod>p\<in>P. f (p ^ multiplicity p (m * n)))"
    using mn by (subst prod_prime_factors) (auto simp: P_def)
  also have "\<dots> = (\<Prod>p\<in>P. f p ^ multiplicity p (m * n))"
    by (intro prod.cong) (auto simp: assms prime_factors_multiplicity P_def)
  also have "\<dots> = (\<Prod>p\<in>P. f p ^ multiplicity p m * f p ^ multiplicity p n)"
    by (intro prod.cong refl, subst prime_elem_multiplicity_mult_distrib)
       (use mn in \<open>auto simp: P_def prime_factors_multiplicity power_add\<close>)
  also have "\<dots> = (\<Prod>p\<in>P. f p ^ multiplicity p m) * (\<Prod>p\<in>P. f p ^ multiplicity p n)"
    by (rule prod.distrib)
  also have "(\<Prod>p\<in>P. f p ^ multiplicity p m) = (\<Prod>p\<in>prime_factors m. f p ^ multiplicity p m)"
    unfolding P_def by (intro prod.mono_neutral_right dvd_prime_factors finite_set_mset)
                       (use mn in \<open>auto simp: prime_factors_multiplicity\<close>)
  also have "\<dots> = (\<Prod>p\<in>prime_factors m. f (p ^ multiplicity p m))"
    by (intro prod.cong) (auto simp: assms prime_factors_multiplicity)
  also have "\<dots> = f m"
    using mn by (intro prod_prime_factors [symmetric]) auto
  also have "(\<Prod>p\<in>P. f p ^ multiplicity p n) = (\<Prod>p\<in>prime_factors n. f p ^ multiplicity p n)"
    unfolding P_def by (intro prod.mono_neutral_right dvd_prime_factors finite_set_mset)
                       (use mn in \<open>auto simp: prime_factors_multiplicity\<close>)
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. f (p ^ multiplicity p n))"
    by (intro prod.cong) (auto simp: assms prime_factors_multiplicity)
  also have "\<dots> = f n"
    using mn by (intro prod_prime_factors [symmetric]) auto
  finally show "f (m * n) = f m * f n" .
qed auto


subsection \<open>Indicator function\<close>

definition ind :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a :: semiring_1" where
  "ind P n = (if n > 0 \<and> P n then 1 else 0)"
  
lemma ind_0 [simp]: "ind P 0 = 0" by (simp add: ind_def)

lemma ind_nonzero: "n > 0 \<Longrightarrow> ind P n = (if P n then 1 else 0)"
  by (simp add: ind_def)

lemma ind_True [simp]: "P n \<Longrightarrow> n > 0 \<Longrightarrow> ind P n = 1"
  by (simp add: ind_nonzero)

lemma ind_False [simp]: "\<not>P n \<Longrightarrow> n > 0 \<Longrightarrow> ind P n = 0"
  by (simp add: ind_nonzero)

lemma ind_eq_1_iff: "ind P n = 1 \<longleftrightarrow> n > 0 \<and> P n"
  by (simp add: ind_def)

lemma ind_eq_0_iff: "ind P n = 0 \<longleftrightarrow> n = 0 \<or> \<not>P n"
  by (simp add: ind_def)

lemma multiplicative_function_ind [intro?]:
  assumes "P 1" "\<And>a b. a > 1 \<Longrightarrow> b > 1 \<Longrightarrow> coprime a b \<Longrightarrow> P (a * b) \<longleftrightarrow> P a \<and> P b"
  shows   "multiplicative_function (ind P)"
  by standard (insert assms, auto simp: ind_nonzero)

end
