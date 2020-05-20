(*
  File:     Jacobi_Symbol.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  The Jacobi symbol, a generalisation of the Legendre symbol.
  This is used in the Solovay--Strassen test.
*)
section \<open>The Jacobi Symbol\<close>
theory Jacobi_Symbol
imports 
  Legendre_Symbol
  Algebraic_Auxiliaries
begin

text \<open>
  The Jacobi symbol is a generalisation of the Legendre symbol to non-primes \cite{Legendre_Symbol, Jacobi_Symbol}.
  It is defined as
  \[\left(\frac{a}{n}\right) =
      \left(\frac{a}{p_1}\right)^{k_1} \ldots \left(\frac{a}{p_l}\right)^{k_l}\]
  where $(\frac{a}{p})$ denotes the Legendre symbol, \<open>a\<close> is an integer, \<open>n\<close> is an odd natural
  number and $p_1^{k_1}\ldots p_l^{k_l}$ is its prime factorisation.

  There is, however, a fairly natural generalisation to all non-zero integers for \<open>n\<close>.
  It is less clear what a good choice for \<open>n = 0\<close> is; Mathematica and Maxima adopt
  the convention that $(\frac{\pm 1}{0}) = 1$ and $(\frac{a}{0}) = 0$ otherwise. However,
  we chose the slightly different convention $(\frac{a}{0}) = 0$ for \<^emph>\<open>all\<close> \<open>a\<close> because then
  the Jacobi symbol is completely multiplicative in both arguments without any restrictions.
\<close>
definition Jacobi :: "int \<Rightarrow> int \<Rightarrow> int" where
  "Jacobi a n = (if n = 0 then 0 else
                  (\<Prod>p\<in>#prime_factorization n. Legendre a p))"

lemma Jacobi_0_right [simp]: "Jacobi a 0 = 0"
  by (simp add: Jacobi_def)

lemma Jacobi_mult_left [simp]: "Jacobi (a * b) n = Jacobi a n * Jacobi b n"
proof (cases "n = 0")
  case False
  have *: "{# Legendre (a * b) p          . p \<in># prime_factorization n #} =
           {# Legendre a p * Legendre b p . p \<in># prime_factorization n #}"
    by (meson Legendre_mult in_prime_factors_imp_prime image_mset_cong)

  show ?thesis using False unfolding Jacobi_def * prod_mset.distrib by auto
qed auto

lemma Jacobi_mult_right [simp]: "Jacobi a (n * m) = Jacobi a n * Jacobi a m"
  by (cases "m = 0"; cases "n = 0")
     (auto simp: Jacobi_def prime_factorization_mult)

lemma prime_p_Jacobi_eq_Legendre[intro!]: "prime p \<Longrightarrow> Jacobi a p = Legendre a p"
  unfolding Jacobi_def prime_factorization_prime by simp

lemma Jacobi_mod [simp]: "Jacobi (a mod m) n = Jacobi a n" if "n dvd m"
proof -
  have *: "{# Legendre (a mod m) p . p \<in># prime_factorization n #} =
           {# Legendre a p . p \<in># prime_factorization n #}" using that
    by (intro image_mset_cong, subst Legendre_mod)
       (auto intro: dvd_trans[OF in_prime_factors_imp_dvd])
  thus ?thesis by (simp add: Jacobi_def)
qed

lemma Jacobi_mod_cong: "[a = b] (mod n) \<Longrightarrow> Jacobi a n = Jacobi b n"
  by (metis Jacobi_mod cong_def dvd_refl)

lemma Jacobi_1_eq_1 [simp]: "p \<noteq> 0 \<Longrightarrow> Jacobi 1 p = 1"
  by (simp add: Jacobi_def in_prime_factors_imp_prime cong: image_mset_cong)

lemma Jacobi_eq_0_not_coprime:
  assumes "n \<noteq> 0" "\<not>coprime a n"
  shows   "Jacobi a n = 0"
proof -
  from assms have "\<exists>p. p dvd gcd a n \<and> prime p"
    by (intro prime_divisor_exists) auto
  then obtain p where p: "p dvd a" "p dvd n" "prime p"
    by auto
  hence "Legendre a p = 0" using assms
    by (auto simp: prime_int_iff)
  thus ?thesis using p assms
    unfolding Jacobi_def 
    by (auto simp: image_iff prime_factors_dvd)
qed

lemma Jacobi_p_eq_2'[simp]: "n > 0 \<Longrightarrow> Jacobi a (2^n) = a mod 2"
  by (auto simp add: Jacobi_def prime_factorization_prime_power)

lemma Jacobi_prod_mset[simp]: "n \<noteq> 0 \<Longrightarrow> Jacobi (prod_mset M) n = (\<Prod>q\<in>#M. Jacobi q n)"
  by (induction M) simp_all

lemma non_trivial_coprime_neq:
  "1 < a \<Longrightarrow> 1 < b \<Longrightarrow> coprime a b \<Longrightarrow> a \<noteq> b" for a b :: int by auto


lemma odd_odd_even: 
  fixes a b :: int 
  assumes "odd a" "odd b"
  shows "even ((a*b-1) div 2) = even ((a-1) div 2 + (b-1) div 2)"
  using assms by (auto elim!: oddE simp: algebra_simps)

lemma prime_nonprime_wlog [case_names primes nonprime sym]:
  assumes "\<And>p q. prime p \<Longrightarrow> prime q \<Longrightarrow> P p q"
  assumes "\<And>p q. \<not>prime p \<Longrightarrow> P p q"
  assumes "\<And>p q. P p q \<Longrightarrow> P q p"
  shows   "P p q"
  by (cases "prime p"; cases "prime q") (auto intro: assms)

lemma Quadratic_Reciprocity_Jacobi:
  fixes p q :: int
  assumes "coprime p q"
      and "2 < p" "2 < q"
      and "odd p" "odd q"
    shows "Jacobi p q * Jacobi q p =
           (- 1) ^ (nat ((p - 1) div 2 * ((q - 1) div 2)))"
  using assms
proof (induction "nat p" "nat q" arbitrary: p q 
         rule: measure_induct_rule[where f = "\<lambda>(a, b). a + b", split_format(complete), simplified])
  case (1 p q)
  thus ?case
  proof (induction p q rule: prime_nonprime_wlog)
    case (sym p q)
    thus ?case by (simp only: add_ac coprime_commute mult_ac) blast
  next
    case (primes p q)
    from \<open>prime p\<close> \<open>prime q\<close> have "prime (nat p)" "prime (nat q)" "p \<noteq> q"
      using prime_int_nat_transfer primes(4) non_trivial_coprime_neq prime_gt_1_int
      by blast+

    with Quadratic_Reciprocity_int and prime_p_Jacobi_eq_Legendre
    show ?case
      using \<open>prime p\<close> \<open>prime q\<close> primes(5-) 
      by presburger
  next
    case (nonprime p q)
    from \<open>\<not>prime p\<close> obtain a b where *: "p = a * b" "1 < b" "1 < a"
      using \<open>2 < p\<close> prime_divisor_exists_strong[of p] by auto

    hence odd_ab: "odd a" "odd b" using \<open>odd p\<close> by simp_all

    moreover have "2 < b" and "2 < a" 
      using odd_ab and * by presburger+

    moreover have "coprime a q" and "coprime b q" using \<open>coprime p q\<close> 
      unfolding * by simp_all

    ultimately have IH: "Jacobi a q * Jacobi q a = (- 1) ^ nat ((a - 1) div 2 * ((q - 1) div 2))"
                        "Jacobi b q * Jacobi q b = (- 1) ^ nat ((b - 1) div 2 * ((q - 1) div 2))"
      by (auto simp: * nonprime)

    have pos: "0 < q" "0 < p" "0 < a" "0 < b" 
      using * \<open>2 < q\<close> by simp_all

    have "Jacobi p q * Jacobi q p = (Jacobi a q * Jacobi q a) * (Jacobi b q * Jacobi q b)"
      using * by simp

    also have "... = (- 1) ^ nat ((a - 1) div 2 * ((q - 1) div 2)) *
                     (- 1) ^ nat ((b - 1) div 2 * ((q - 1) div 2))"
      using IH by presburger

    also from odd_odd_even[OF odd_ab]
    have "... = (- 1) ^ nat ((p - 1) div 2 * ((q - 1) div 2))"
      unfolding * minus_one_power_iff using \<open>2 < q\<close> *
      by (auto simp add: even_nat_iff pos_imp_zdiv_nonneg_iff)

    finally show ?case .
  qed
qed

lemma Jacobi_values: "Jacobi p q \<in> {1, -1, 0}"
proof (cases "q = 0")
  case False
  hence "\<bar>Legendre p x\<bar> = 1" if "x \<in># prime_factorization q" "Jacobi p q \<noteq> 0" for x
    using that prod_mset_zero_iff Legendre_values[of p x]
    unfolding Jacobi_def is_unit_prod_mset_iff set_image_mset
    by fastforce

  then have "is_unit (prod_mset (image_mset (Legendre p) (prime_factorization q)))"
    if "Jacobi p q \<noteq> 0"
    using that False
    unfolding Jacobi_def is_unit_prod_mset_iff 
    by auto

  thus ?thesis by (auto simp: Jacobi_def)
qed auto

lemma Quadratic_Reciprocity_Jacobi':
  fixes p q :: int
  assumes "coprime p q"
      and "2 < p" "2 < q"
      and "odd p" "odd q"
    shows "Jacobi q p = (if p mod 4 = 3 \<and> q mod 4 = 3 then -1 else 1) * Jacobi p q"
proof -
  have aux: "a \<in> {1, -1, 0} \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> a*b = c \<Longrightarrow> b = c * a" for b c a :: int by auto

  from Quadratic_Reciprocity_Jacobi[OF assms] 
  have "Jacobi q p = (-1) ^ nat ((p - 1) div 2 * ((q - 1) div 2)) * Jacobi p q"
    using Jacobi_values by (fastforce intro!: aux)

  also have "(-1 :: int) ^ nat ((p - 1) div 2 * ((q - 1) div 2)) = (if even ((p - 1) div 2) \<or> even ((q - 1) div 2) then 1 else - 1)"
    unfolding minus_one_power_iff using \<open>2 < p\<close> \<open>2 < q\<close>
    by (auto simp: even_nat_iff)

  also have "... = (if p mod 4 = 3 \<and> q mod 4 = 3 then -1 else 1)"
    using \<open>odd p\<close> \<open>odd q\<close> by presburger

  finally show ?thesis .

qed

lemma dvd_odd_square: "8 dvd a\<^sup>2 - 1" if "odd a" for a :: int 
proof -
  obtain x where "a = 2*x + 1" using \<open>odd a\<close> by (auto elim: oddE)
  thus ?thesis
    by(cases "odd x") 
      (auto elim: oddE simp: power2_eq_square algebra_simps)
qed 

lemma odd_odd_even': 
  fixes a b :: int 
  assumes "odd a" "odd b"
  shows "even (((a * b)\<^sup>2 - 1) div 8) \<longleftrightarrow> even (((a\<^sup>2 - 1) div 8) + ((b\<^sup>2 - 1) div 8))"
proof -
  obtain x where [simp]: "a = 2*x + 1" using \<open>odd a\<close> by (auto elim: oddE)
  obtain y where [simp]: "b = 2*y + 1" using \<open>odd b\<close> by (auto elim: oddE)
  show ?thesis
    by (cases "even x"; cases "even y"; elim oddE evenE)
       (auto simp: power2_eq_square algebra_simps)
qed

lemma odd_odd_even_nat': 
  fixes a b :: nat 
  assumes "odd a" "odd b"
  shows "even (((a * b)\<^sup>2 - 1) div 8) \<longleftrightarrow> even (((a\<^sup>2 - 1) div 8) + ((b\<^sup>2 - 1) div 8))"
proof -
  obtain x where [simp]: "a = 2*x + 1" using \<open>odd a\<close> by (auto elim: oddE)
  obtain y where [simp]: "b = 2*y + 1" using \<open>odd b\<close> by (auto elim: oddE)
  show ?thesis
    by (cases "even x"; cases "even y"; elim oddE evenE)
       (auto simp: power2_eq_square algebra_simps)
qed

lemma supplement2_Jacobi: "odd p \<Longrightarrow> p > 1 \<Longrightarrow> Jacobi 2 p = (- 1) ^ (((nat p)\<^sup>2 - 1) div 8)"
proof (induction p rule: prime_divisors_induct)
  case (factor p x)

  then have "odd x" by force

  have "2 < p" 
    using \<open>odd (p * x)\<close> prime_gt_1_int[OF \<open>prime p\<close>] 
    by (cases "p = 2") auto

  have "odd p" using prime_odd_int[OF \<open>prime p\<close> \<open>2 < p\<close>] .

  have "0 < x"
    using \<open>1 < (p * x)\<close> prime_gt_0_int[OF \<open>prime p\<close>]
    and less_trans less_numeral_extra(1) zero_less_mult_pos by blast

  have base_case : "Jacobi 2 p = (- 1) ^ (((nat p)\<^sup>2 - 1) div 8)" 
    using \<open>2 < p\<close> \<open>prime p\<close> supplement2_Legendre and prime_p_Jacobi_eq_Legendre
    by presburger

  show ?case proof (cases "x = 1")
    case True
    thus ?thesis using base_case by force
  next
    case False
    have "Jacobi 2 (p * x) = Jacobi 2 p * Jacobi 2 x"
      using \<open>2 < p\<close> \<open>0 < x\<close> by simp

    also have "Jacobi 2 x = (- 1) ^ (((nat x)\<^sup>2 - 1) div 8)"
      using \<open>odd x\<close> \<open>0 < x\<close> \<open>x \<noteq> 1\<close> by (intro factor.IH) auto

    also note base_case

    also have "(-1) ^ (((nat p)\<^sup>2 - 1) div 8) * (-1) ^ (((nat x)\<^sup>2 - 1) div 8)
             = (-1 :: int) ^ (((nat (p * x))\<^sup>2 - 1) div 8)" 
      unfolding minus_one_power_iff
      using \<open>2 < p\<close> \<open>0 < x\<close> \<open>odd x\<close> \<open>odd p\<close> and odd_odd_even_nat'
      using [[linarith_split_limit = 0]]
      by (force simp add: nat_mult_distrib even_nat_iff)

    finally show ?thesis .
  qed
qed simp_all

lemma mod_nat_wlog [consumes 1, case_names modulo]:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "b > 0"
  assumes "\<And>k. k \<in> {0..<b} \<Longrightarrow> n mod b = k \<Longrightarrow> P n"
  shows   "P n"
  using assms and mod_less_divisor 
  by fastforce

lemma mod_int_wlog [consumes 1, case_names modulo]:
  fixes P :: "int \<Rightarrow> bool"
  assumes "b > 0"
  assumes "\<And>k. 0 \<le> k \<Longrightarrow> k < b \<Longrightarrow> n mod b = k \<Longrightarrow> P n"
  shows   "P n"
  using assms and pos_mod_conj by blast 

lemma supplement2_Jacobi':
  assumes "odd p" and "p > 1"
  shows "Jacobi 2 p = (if p mod 8 = 1 \<or> p mod 8 = 7 then 1 else -1)"
proof -
  have "0 < (4 :: nat)" by simp
  then have *: "even ((p\<^sup>2 - 1) div 8) = (p mod 8 = 1 \<or> p mod 8 = 7)" if "odd p" for p :: nat
  proof(induction p rule: mod_nat_wlog)
    case (modulo k)
    then consider "p mod 4 = 1" | "p mod 4 = 3"
      using \<open>odd p\<close>
      by (metis dvd_0_right even_even_mod_4_iff even_numeral mod_exhaust_less_4)

    then show ?case proof (cases)
      case 1
      then obtain l where l: "p = 4 * l + 1" using mod_natE by blast
      have "even l = ((4 * l + 1) mod 8 = 1 \<or> (4 * l + 1) mod 8 = 7)" by presburger
      thus ?thesis by (simp add: l power2_eq_square algebra_simps)
    next
      case 2
      then obtain l where l: "p = 4 * l + 3" using mod_natE by blast
      have "odd l = ((3 + l * 4) mod 8 = Suc 0 \<or> (3 + l * 4) mod 8 = 7)" by presburger
      thus ?thesis by (simp add: l power2_eq_square algebra_simps)
    qed
  qed

  have [simp]: "nat p mod 8 = nat (p mod 8)"
    using \<open>p > 1\<close> using nat_mod_distrib[of p 8] by simp
  from assms have "odd (nat p)" by (simp add: even_nat_iff)
  show ?thesis
    unfolding supplement2_Jacobi[OF assms]
              minus_one_power_iff *[OF \<open>odd (nat p)\<close>]
    by (simp add: nat_eq_iff)
qed

theorem supplement1_Jacobi:
  "odd p \<Longrightarrow> 1 < p \<Longrightarrow> Jacobi (-1) p = (-1) ^ (nat ((p - 1) div 2))"
proof (induction p rule: prime_divisors_induct)
  case (factor p x)
  then have "odd x" by force

  have "2 < p" 
    using \<open>odd (p * x)\<close> prime_gt_1_int[OF \<open>prime p\<close>]
    by (cases "p = 2") auto

  have "prime (nat p)"
    using \<open>prime p\<close> prime_int_nat_transfer
    by blast

  have "Jacobi (-1) p = Legendre (-1) p"
    using prime_p_Jacobi_eq_Legendre[OF \<open>prime p\<close>] .

  also have "... = (-1) ^ ((nat p - 1) div 2)"
    using \<open>prime p\<close> \<open>2 < p\<close> and supplement1_Legendre[of "nat p"]
    by (metis int_nat_eq nat_mono_iff nat_numeral_as_int prime_gt_0_int prime_int_nat_transfer) 

  also have "((nat p - 1) div 2) = nat ((p - 1) div 2)" by force

  finally have base_case: "Jacobi (-1) p = (-1) ^ nat ((p - 1) div 2)" .

  show ?case proof (cases "x = 1")
    case True
    then show ?thesis using base_case by simp
  next
    case False
    have "0 < x" 
      using \<open>1 < (p * x)\<close> prime_gt_0_int[OF \<open>prime p\<close>]
      by (meson int_one_le_iff_zero_less not_less not_less_iff_gr_or_eq zero_less_mult_iff)
  
    have "odd p" using \<open>prime p\<close> \<open>2 < p\<close> by (simp add: prime_odd_int) 

    have "Jacobi (-1) (p * x) = Jacobi (-1) p * Jacobi (-1) x"
      using \<open>2 < p\<close> \<open>0 < x\<close> by simp

    also note base_case

    also have "Jacobi (-1) x = (-1) ^ nat ((x - 1) div 2)"
      using \<open>0 < x\<close> False \<open>odd x\<close> factor.IH 
      by fastforce

    also have "(- 1) ^ nat ((p - 1) div 2) * (- 1) ^ nat ((x - 1) div 2) =
               (- 1 :: int) ^ nat ((p*x - 1) div 2)"
      unfolding minus_one_power_iff
      using \<open>2 < p\<close> \<open>0 < x\<close> and \<open>odd x\<close> \<open>odd p\<close>
      by (fastforce elim!: oddE simp: even_nat_iff algebra_simps)

    finally show ?thesis .
  qed
qed simp_all

theorem supplement1_Jacobi':
  "odd n \<Longrightarrow> 1 < n \<Longrightarrow> Jacobi (-1) n = (if n mod 4 = 1 then 1 else -1)"
  by (simp add: even_nat_iff minus_one_power_iff supplement1_Jacobi)
     presburger?

lemma Jacobi_0_eq_0: "\<not>is_unit n \<Longrightarrow> Jacobi 0 n = 0"
  by (cases "prime_factorization n = {#}")
     (auto simp: Jacobi_def prime_factorization_empty_iff image_iff intro: Nat.gr0I)

lemma is_unit_Jacobi_aux: "is_unit x \<Longrightarrow> Jacobi a x = 1"
  unfolding Jacobi_def using prime_factorization_empty_iff[of x] by auto

lemma is_unit_Jacobi[simp]: "Jacobi a 1 = 1" "Jacobi a (-1) = 1"
  using is_unit_Jacobi_aux by simp_all

lemma Jacobi_neg_right [simp]:
  "Jacobi a (-n) = Jacobi a n"
proof -
  have * : "-n = (-1) * n" by simp
  show ?thesis unfolding *
    by (subst Jacobi_mult_right) auto
qed

lemma Jacobi_neg_left:
  assumes "odd n" "1 < n" 
  shows   "Jacobi (-a) n = (if n mod 4 = 1 then 1 else -1) * Jacobi a n"
proof -
  have * : "-a = (-1) * a" by simp
  show ?thesis unfolding * Jacobi_mult_left supplement1_Jacobi'[OF assms] ..
qed

function jacobi_code :: "int \<Rightarrow> int \<Rightarrow> int" where
"jacobi_code a n = ( 
        if n = 0 then 0
   else if n = 1 then 1
   else if a = 1 then 1
   else if n < 0 then jacobi_code a (-n)
   else if even n then if even a then 0 else jacobi_code a (n div 2)
   else if a < 0 then (if n mod 4 = 1 then 1 else -1) * jacobi_code (-a) n
   else if a = 0 then 0
   else if a \<ge> n then jacobi_code (a mod n) n
   else if even a      then (if n mod 8 \<in> {1, 7} then 1 else -1) * jacobi_code (a div 2) n
   else if coprime a n then (if n mod 4 = 3 \<and> a mod 4 = 3 then -1 else 1) * jacobi_code n a
   else 0)"
  by auto
termination
proof (relation "measure (\<lambda>(a, n). nat(abs(a) + abs(n)*2) + 
                   (if n < 0 then 1 else 0) + (if a < 0 then 1 else 0))", goal_cases)
  case (5 a n)
  thus ?case by (fastforce intro!: less_le_trans[OF pos_mod_bound])
qed auto

lemmas [simp del] = jacobi_code.simps

lemma Jacobi_code [code]: "Jacobi a n = jacobi_code a n"
proof (induction a n rule: jacobi_code.induct)
  case (1 a n)
  show ?case
  proof (cases "n = 0")
    case 2: False
    then show ?thesis proof (cases "n = 1")
      case 3: False
      then show ?thesis proof (cases "a = 1")
        case 4: False
          then show ?thesis proof (cases "n < 0")
            case True
            then show ?thesis using 2 3 4 1(1) by (subst jacobi_code.simps) simp
            next
            case 5: False
            then show ?thesis proof (cases "even n")
              case True
              then show ?thesis using 2 3 4 5 1(2)
                by (elim evenE, subst jacobi_code.simps) (auto simp: prime_p_Jacobi_eq_Legendre)
            next
              case 6: False
              then show ?thesis  proof (cases "a < 0")
                case True
                then show ?thesis using 2 3 4 5 6
                  by(subst jacobi_code.simps, subst 1(3)[symmetric]) (simp_all add: Jacobi_neg_left)
              next
                case 7: False
                then show ?thesis proof (cases "a = 0")
                  case True
                  have *: "\<not> is_unit n" using 3 5 by simp
                  then show ?thesis
                    using Jacobi_0_eq_0[OF *] 2 3 4 5 7 True
                    by (subst jacobi_code.simps) simp
                next
                  case 8: False
                  then show ?thesis proof (cases "a \<ge> n")
                    case True
                    then show ?thesis using 2 3 4 5 6 7 8 1(4)
                      by (subst jacobi_code.simps) simp
                  next
                    case 9: False
                    then show ?thesis proof (cases "even a")
                      case True
                      hence "a = 2 * (a div 2)" by simp
                      also have "Jacobi \<dots> n = Jacobi 2 n * Jacobi (a div 2) n"
                        by simp
                      also have "Jacobi (a div 2) n = jacobi_code (a div 2) n"
                        using 2 3 4 5 6 7 8 9 True by (intro 1(5))
                      also have "Jacobi 2 n = (if n mod 8 \<in> {1, 7} then 1 else - 1)"
                        using 2 3 5 supplement2_Jacobi'[OF 6] by simp
                      also have "\<dots> * jacobi_code (a div 2) n = jacobi_code a n"
                        using 2 3 4 5 6 7 8 9 True
                        by (subst (2) jacobi_code.simps) (simp only: if_False if_True HOL.simp_thms)
                      finally show ?thesis .
                    next
                      case 10: False
                      note foo = 1 2 3
                      then show ?thesis proof (cases "coprime a n")
                        case True
                        note this_case = 2 3 4 5 6 7 8 9 10 True
                        have "2 < a" using 10 4 7 by presburger
                        moreover have "2 < n" using 3 5 6 by presburger
                        ultimately have "jacobi_code a n = (if n mod 4 = 3 \<and> a mod 4 = 3 then - 1 else 1)
                                                        * jacobi_code n a"
                          using this_case by (subst jacobi_code.simps) simp
                        also have "jacobi_code n a = Jacobi n a"
                          using this_case by (intro 1(6) [symmetric]) auto
                        also have "(if n mod 4 = 3 \<and> a mod 4 = 3 then -1 else 1) * \<dots> = Jacobi a n"
                          using this_case and \<open>2 < a\<close>
                          by (intro Quadratic_Reciprocity_Jacobi' [symmetric])
                             (auto simp: coprime_commute)
                        finally show ?thesis ..
                      next
                        case False
                        have *: "0 < a" "0 < n" using 5 7 8 9 by linarith+ 
                        show ?thesis
                          using 1 2 3 4 5 6 7 8 9 10 False *
                          by (subst jacobi_code.simps) (auto simp: Jacobi_eq_0_not_coprime)
                      qed
                    qed
                  qed
                qed
              qed
            qed
        qed
      qed (subst jacobi_code.simps, simp)
    qed (subst jacobi_code.simps, simp)
  qed (subst jacobi_code.simps, simp)
qed

lemma Jacobi_eq_0_imp_not_coprime:
  assumes "p \<noteq> 0" "p \<noteq> 1"
  shows   "Jacobi n p = 0 \<Longrightarrow> \<not>coprime n p"
  using assms Jacobi_mod_cong coprime_iff_invertible_int by force

lemma Jacobi_eq_0_iff_not_coprime:
  assumes "p \<noteq> 0" "p \<noteq> 1"
  shows "Jacobi n p = 0 \<longleftrightarrow> \<not>coprime n p"
proof -
  from assms and Jacobi_eq_0_imp_not_coprime 
  show ?thesis using Jacobi_eq_0_not_coprime by auto
qed

end