(*
    File:      Dirichlet_Efficient_Code.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Efficient code for number-theoretic functions\<close>
theory Dirichlet_Efficient_Code
imports 
  Main 
  Moebius_Mu 
  More_Totient 
  Divisor_Count
  Liouville_Lambda
  "HOL-Library.Code_Target_Numeral"
  Polynomial_Factorization.Prime_Factorization
begin

definition prime_factorization_nat' :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "prime_factorization_nat' n = (
     let ps = prime_factorization_nat n
     in  map (\<lambda>p. (p, length (filter ((=) p) ps) - 1)) (remdups_adj (sort ps)))"
  
lemma set_prime_factorization_nat':
  "set (prime_factorization_nat' n) = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n"
proof (intro equalityI subsetI; clarify)
  fix p k :: nat
  assume pk: "(p, k) \<in> set (prime_factorization_nat' n)"
  hence p: "p \<in> prime_factors n"
    by (auto simp: prime_factorization_nat'_def Let_def multiset_prime_factorization_nat_correct)
  hence p': "prime p" by (simp add: prime_factors_multiplicity)
  from pk p' have "k = multiplicity p n - 1"
    by (auto simp: prime_factorization_nat'_def Let_def multiset_prime_factorization_nat_correct
          count_prime_factorization_prime [symmetric] count_mset )
  with p show "(p, k) \<in> (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n" by auto
next
  fix p :: nat
  assume "p \<in> prime_factors n"
  moreover from this have "prime p" by (simp add: prime_factors_multiplicity)
  ultimately show "(p, multiplicity p n - 1) \<in> set (prime_factorization_nat' n)"
    by (auto simp: prime_factorization_nat'_def Let_def multiset_prime_factorization_nat_correct 
          count_prime_factorization_prime [symmetric] count_mset)
qed
  
lemma distinct_prime_factorization_nat' [simp]: "distinct (prime_factorization_nat' n)"
  by (simp add: distinct_map inj_on_def prime_factorization_nat'_def Let_def)

lemmas (in multiplicative_function') efficient_code' = 
   efficient_code [of "\<lambda>_. prime_factorization_nat' n" n for n, 
     OF set_prime_factorization_nat' distinct_prime_factorization_nat']

  
subsection \<open>M\"{o}bius $\mu$ function\<close>

definition moebius_mu_aux :: "nat \<Rightarrow> (unit \<Rightarrow> nat list) \<Rightarrow> int" where
  "moebius_mu_aux n ps = 
     (if n \<noteq> 0 \<and> \<not>4 dvd n \<and> \<not>9 dvd n then
        (let ps = ps () in if distinct ps then if even (length ps) then 1 else -1 else 0) else 0)"

lemma moebius_mu_conv_moebius_mu_aux:
  fixes qs :: "unit \<Rightarrow> nat list"
  defines "ps \<equiv> qs ()"
  assumes "mset ps = prime_factorization n"
  shows   "moebius_mu n = of_int (moebius_mu_aux n qs)"
proof (cases "n = 0 \<or> 4 dvd n \<or> 9 dvd n")
  case False
  hence [simp]: "n > 0" by auto
  have "set_mset (mset ps) = prime_factors n" by (subst assms) simp
  hence [simp]: "set ps = prime_factors n" by simp
  show ?thesis
  proof (cases "distinct ps")
    case True
    have "multiplicity p n = 1" if p: "p \<in> prime_factors n" for p
    proof -
      from p and True have "count (mset ps) p = 1" by (auto simp: distinct_count_atmost_1)
      also from assms and p have "count (mset ps) p = multiplicity p n"
        by (simp add: prime_factors_multiplicity count_prime_factorization_prime)
      finally show "multiplicity p n = 1" .
    qed
    moreover from True have "card (prime_factors n) = length ps"
      by (simp only: assms [symmetric] set_mset_mset distinct_card)
    ultimately show ?thesis using False and True
      by (auto simp add: moebius_mu_def moebius_mu_aux_def ps_def 
            Let_def squarefree_factorial_semiring')
  next
    case False
    then obtain p where "count (mset ps) p \<noteq> (if p \<in> set ps then 1 else 0)"
      by (subst (asm) distinct_count_atmost_1) auto
    moreover from this have p: "p \<in> prime_factors n" 
      by (cases "count (mset ps) p = 0") (auto split: if_splits)
    ultimately have "count (mset ps) p > 1" by (cases "count (mset ps) p") auto
    with p and assms have "multiplicity p n > 1"
      by (simp add: prime_factors_multiplicity count_prime_factorization_prime)
    with False and assms and p have "\<not>squarefree n"
      by (auto simp: squarefree_factorial_semiring'')
    with False and assms and p show ?thesis 
      by (auto simp: moebius_mu_def moebius_mu_aux_def)
  qed
next
  case True
  with not_squarefreeI[of 2 n] and not_squarefreeI[of 3 n] show ?thesis
    by (auto simp: moebius_mu_aux_def)
qed

lemma moebius_mu_code [code]: 
    "moebius_mu n = of_int (moebius_mu_aux n (\<lambda>_. prime_factorization_nat n))"
  by (rule moebius_mu_conv_moebius_mu_aux) (simp_all add: multiset_prime_factorization_nat_correct)

value "moebius_mu 12578972695257 :: int"


subsection \<open>Euler's $\phi$ function\<close>
  
primrec totient_aux1 :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "totient_aux1 n [] = n"
| "totient_aux1 n (p # ps) = totient_aux1 (n - n div p) ps"
  
lemma of_nat_totient_aux1:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> prime p" "\<And>p. p \<in> set ps \<Longrightarrow> p dvd n" "distinct ps"
  shows   "real (totient_aux1 n ps) = real n * (\<Prod>p\<in>set ps. 1 - 1 / real p)"
using assms
proof (induction ps arbitrary: n)
  case (Cons p ps n)
  from Cons.prems have p: "prime p" "p dvd n" by auto
  have "real (totient_aux1 n (p # ps)) = real (totient_aux1 (n - n div p) ps)" by simp
  also have "\<dots> = real (n - n div p) * (\<Prod>p\<in>set ps. 1 - 1 / real p)"
  proof (rule Cons.IH)
    fix q assume q: "q \<in> set ps"
    define m where "m = n div p"
    from p have m: "n = p * m" by (simp add: m_def)
    from Cons.prems q have "prime q" "q dvd n" "p \<noteq> q" by auto
    hence "q dvd m" using primes_dvd_imp_eq[of q p]  p by (auto simp add: m prime_dvd_mult_iff)
    thus "q dvd n - n div p" unfolding m_def using p \<open>q dvd n\<close> by simp
  qed (insert Cons.prems, auto)
  also have "real (n - n div p) = real n * (1 - 1 / real p)"
    by (simp add: of_nat_diff real_of_nat_div p field_simps)
  also have "\<dots> * (\<Prod>p\<in>set ps. 1 - 1 / real p) = real n * (\<Prod>p\<in>set (p#ps). 1 - 1 / real p)"
    using Cons.prems by simp
  finally show ?case .
qed simp_all
  
lemma totient_conv_totient_aux1:
  assumes "set ps = prime_factors n" "distinct ps"
  shows   "totient n = totient_aux1 n ps"
proof -
  from assms have "real (totient_aux1 n ps) = real n * (\<Prod>p\<in>set ps. 1 - 1 / real p)"
    by (intro of_nat_totient_aux1) auto
  also have "set ps = prime_factors n" by fact
  also have "real n * (\<Prod>p\<in>prime_factors n. 1 - 1 / real p) = real (totient n)"
    by (rule totient_formula2 [symmetric])
  finally show ?thesis by (simp only: of_nat_eq_iff)
qed

definition prime_factors_nat :: "nat \<Rightarrow> nat list" where
  "prime_factors_nat n = remdups_adj (sort (prime_factorization_nat n))"
  
lemma set_prime_factors_nat [simp]: "set (prime_factors_nat n) = prime_factors n"
  unfolding prime_factors_nat_def multiset_prime_factorization_nat_correct by simp

lemma distinct_prime_factors_nat [simp]: "distinct (prime_factors_nat n)"
  by (simp add: prime_factors_nat_def)


definition totient_aux2 :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "totient_aux2 xs = (\<Prod>(p,k)\<leftarrow>xs. p ^ k * (p - 1))"
  
lemma totient_conv_totient_aux2:
  assumes "n \<noteq> 0"
  assumes "set xs = (\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n"
  assumes "distinct xs"
  shows   "totient n = totient_aux2 xs"
proof -
  have "totient_aux2 xs = (\<Prod>(p,k)\<leftarrow>xs. p ^ k * (p - 1))" by (fact totient_aux2_def)
  also from assms have "\<dots> = 
    (\<Prod>x\<in>(\<lambda>p. (p, multiplicity p n - 1)) ` prime_factors n. case x of (p, k) \<Rightarrow> p ^ k * (p - Suc 0))"
    by (subst prod.distinct_set_conv_list [symmetric]) simp_all
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n - 1) * (p - Suc 0))"
    by (subst prod.reindex) (auto simp: inj_on_def)
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n - p ^ (multiplicity p n - 1))"
    by (intro prod.cong refl) (auto simp: prime_factors_multiplicity algebra_simps
                                 power_Suc [symmetric] simp del: power_Suc)
  also have "\<dots> = totient n" using assms(1) by (subst totient.prod_prime_factors') auto
  finally show ?thesis ..
qed

lemma totient_code1: "totient n = totient_aux1 n (prime_factors_nat n)"
  by (intro totient_conv_totient_aux1) simp_all
    
lemma totient_code2: "totient n = (if n = 0 then 0 else totient_aux2 (prime_factorization_nat' n))"
  by (simp_all add: set_prime_factorization_nat' totient_conv_totient_aux2 split: if_splits)

declare totient_code_naive [code del]

lemmas [code] = totient_code2

value "totient 125789726827482323235784"


subsection \<open>Divisor Functions\<close>

lemmas [code del] = divisor_count_naive divisor_sum_naive
lemmas [code] = divisor_count.efficient_code' divisor_sum.efficient_code'

value "int (divisor_count 378568418621)"
value "int (divisor_sum 378568418621)"


subsection \<open>Liouville's $\lambda$ function\<close>

lemma [code]: "liouville_lambda n = 
  (if n = 0 then 0 else if even (length (prime_factorization_nat n)) then 1 else -1)"
  by (auto simp: liouville_lambda_def multiset_prime_factorization_nat_correct)

value "liouville_lambda 1264785343674 :: int"

end
