section \<open>The Lucas--Lehmer test\<close>
theory Lucas_Lehmer
imports
  Lucas_Lehmer_Auxiliary
  "HOL-Algebra.Ring"
  "Probabilistic_Prime_Tests.Jacobi_Symbol"
  "Pell.Pell" (* only needed for irrationality of sqrt(3) *)
begin

subsection \<open>General properties of Mersenne numbers and Mersenne primes\<close>

text \<open>
  We mostly follow the proofs given on Wikipedia~\cite{wiki:mersenne,wiki:lucas_lehmer} in the
  following sections.

  We first show some basic and theorems about Mersenne numbers and Mersenne primes in general,
  beginning with this: Mersenne primes are the only primes of the form $a^n - 1$ for $n > 1$.
\<close>
lemma prime_power_minus_oneD:
  fixes a n :: nat
  assumes "prime (a ^ n - 1)"
  shows   "n = 1 \<or> a = 2"
proof -
  from assms have "n > 0"
    by (intro Nat.gr0I) auto
  have "a \<noteq> 0" "a \<noteq> 1"
    by (rule notI, use \<open>n > 0\<close> assms in \<open>simp add: zero_power\<close>)+
  hence "a > 1" by auto
  have "[a - 1 + 1 = 0 + 1] (mod (a - 1))"
    by (rule cong_add) (auto simp: cong_def)
  hence "[a = 1] (mod (a - 1))"
    using \<open>a > 1\<close> by simp
  hence "[a ^ n - 1 = 1 ^ n - 1] (mod (a - 1))"
    using \<open>a > 1\<close> by (intro cong_pow cong_diff_nat) auto
  hence "(a - 1) dvd (a ^ n - 1)"
    by (simp add: cong_0_iff)
  have "a - 1 = 1 \<or> a - 1 = a ^ n - 1"
    using \<open>prime (a ^ n - 1)\<close> and \<open>(a - 1) dvd _\<close> by (rule prime_natD)
  thus ?thesis
  proof
    assume "a - 1 = 1"
    hence "a = 2" by simp
    thus ?thesis by simp
  next
    assume "a - 1 = a ^ n - 1"
    hence "a ^ n = a ^ 1"
      using \<open>a > 1\<close> by (simp add: Nat.eq_diff_iff)
    hence "n = 1"
      using \<open>a > 1\<close> by (subst (asm) power_inject_exp) auto
    thus ?thesis by simp
  qed
qed

text \<open>
  Next, we show that if a prime \<open>q\<close> divides a Mersenne number $2^p - 1$ with an odd prime
  exponent \<open>p\<close>, then \<open>q\<close> must be of the form $q = 1 + 2kp$ for some $k > 0$.
\<close>
lemma prime_dvd_mersenneD:
  fixes p q :: nat
  assumes "prime p" "p \<noteq> 2" "prime q" "q dvd (2 ^ p - 1)"
  shows   "[q = 1] (mod (2 * p))"
proof -
  from assms have "odd p"
    using prime_gt_1_nat[of p] by (intro prime_odd_nat) auto
  have "q \<noteq> 0" "q \<noteq> 1" "q \<noteq> 2"
    using assms by (auto intro!: Nat.gr0I)
  hence "q > 2" by simp
  with \<open>prime q\<close> have "odd q"
    by (simp add: prime_odd_nat)

  have "ord q 2 = p"
  proof -
    from assms have "[2 ^ p - 1 + 1 = 0 + 1] (mod q)"
      by (intro cong_add cong_refl) (auto simp: cong_0_iff)
    hence "[2 ^ p = 1] (mod q)" by simp
    hence "ord q 2 dvd p"
      by (subst (asm) ord_divides)
    hence "ord q 2 = 1 \<or> ord q 2 = p"
      using \<open>prime p\<close> and prime_natD by blast
    moreover have "ord q 2 \<noteq> 1"
      using ord_works[of 2 q] and \<open>prime q\<close> by (auto simp: cong_altdef_nat)
    ultimately show "ord q 2 = p" by blast
  qed

  have q_dvd_iff: "q dvd (2 ^ x - 1) \<longleftrightarrow> p dvd x" for x :: nat
  proof -
    have "q dvd (2 ^ x - 1) \<longleftrightarrow> [2 ^ x = 1] (mod q)"
      by (auto simp: cong_altdef_nat)
    also have "\<dots> \<longleftrightarrow> ord q 2 dvd x"
      by (rule ord_divides)
    also note \<open>ord q 2 = p\<close>
    finally show ?thesis .
  qed

  from \<open>q > 2\<close> and assms have "\<not>q dvd 2"
    using primes_dvd_imp_eq two_is_prime_nat by blast
  hence "[2 ^ (q - 1) - 1 = 1 - 1] (mod q)"
    using assms by (intro fermat_theorem cong_diff_nat) auto
  hence "q dvd (2 ^ (q - 1) - 1)"
    by (simp add: cong_0_iff)
  hence "p dvd (q - 1)"
    by (subst (asm) q_dvd_iff)
  hence "[q = 1] (mod p)"
    using \<open>q > 2\<close> by (auto simp: cong_altdef_nat prime_gt_1_nat)

  moreover have "[q = 1] (mod 2)"
    using \<open>odd q\<close> by (auto simp: cong_def odd_iff_mod_2_eq_one)
  ultimately show "[q = 1] (mod (2 * p))"
    using \<open>odd p\<close> by (intro coprime_cong_mult_nat) auto
qed

lemma prime_dvd_mersenneD':
  fixes p q :: nat
  assumes "prime p" "p \<noteq> 2" "prime q" "q dvd (2 ^ p - 1)"
  shows "\<exists>k>0. q = 1 + 2 * k * p"
proof -
  have "q \<noteq> 0" "q \<noteq> 1" "q \<noteq> 2"
    using assms by (auto intro!: Nat.gr0I)
  hence "q > 2" by simp

  have "[q = 1] (mod (2 * p))"
    by (rule prime_dvd_mersenneD) fact+
  hence "(2 * p) dvd (q - 1)"
    using \<open>q > 2\<close> by (auto simp: cong_altdef_nat)
  then obtain k where k: "q - 1 = (2 * p) * k"
    by blast
  hence "q = 1 + 2 * k * p"
    using \<open>q > 2\<close> by (simp add: algebra_simps)
  moreover have "k > 0"
    using \<open>q > 2\<close> and k by (intro Nat.gr0I) auto
  ultimately show ?thesis by blast
qed


text \<open>
  A Mersenne number is any number of the form $2^p - 1$ for a natural number $p$. To make things
  a bit more pleasant, we additionally exclude $2^2 - 1$, i.e. we require $p > 2$. It can
  be shown that $p$ is then always an odd prime.
\<close>
locale mersenne_prime =
  fixes p M :: nat
  defines "M \<equiv> 2 ^ p - 1"
  assumes p_gt_2: "p > 2" and prime: "prime M"
begin

lemma M_gt_6: "M > 6"
proof -
  from p_gt_2 have "2 ^ p \<ge> (2 ^ 3 :: nat)"
    by (intro power_increasing) auto
  thus ?thesis by (simp add: M_def)
qed

lemma M_odd: "odd M"
  using p_gt_2 by (auto simp: M_def)

theorem p_prime: "prime p"
proof (rule ccontr)
  assume "\<not>prime p"
  then obtain a b where ab: "p = a * b" "a > 1" "b > 1"
    using p_gt_2 not_prime_imp_ex_prod_nat[of p] by auto

  have geometric_sum_aux: "(x - (1 :: int)) * (\<Sum>k<a. x ^ k) = x ^ a - 1" for x
    by (induction a) (auto simp: algebra_simps)
  have "(2 ^ b - 1 :: int) * (\<Sum>k<a. (2 ^ b) ^ k) = (2 ^ b) ^ a - 1"
    by (rule geometric_sum_aux)
  hence "2 ^ (a*b) - 1 = (2 ^ b - 1 :: int) * (\<Sum>k<a. 2 ^ (k*b))"
    by (simp flip: power_mult add: algebra_simps)
  hence "(2 ^ b - 1) dvd (2 ^ (a*b) - 1 :: int)"
    by simp
  hence "int (2 ^ b - 1) dvd int (2 ^ (a * b) - 1)"
    by (subst of_nat_diff) (auto simp: of_nat_diff)
  hence "(2 ^ b - 1) dvd (2 ^ (a * b) - 1 :: nat)"
    by (subst (asm) int_dvd_int_iff)
  with prime have "2 ^ b - 1 = (1 :: nat) \<or> 2 ^ b - 1 = (2 ^ p - 1 :: nat)"
    unfolding ab M_def by (intro prime_natD) auto
  moreover have "2 ^ b > (2 ^ 1 :: nat)"
    using ab by (intro power_strict_increasing) auto
  moreover have "2 ^ b < (2 ^ p :: nat)"
    using ab by (intro power_strict_increasing) auto
  hence "2 ^ b - 1 < (2 ^ p - 1 :: nat)"
    by (subst less_diff_iff) auto
  ultimately show False by auto
qed

lemma p_odd: "odd p"
  using p_prime p_gt_2 prime_odd_nat by auto

text \<open>
  We now first show a few more properties of Mersenne primes regarding congruences
  and the Legendre symbol.
\<close>
lemma M_cong_7_mod_12: "[M = 7] (mod 12)"
proof -
  have "[M = 8 - 1] (mod 12)"
    using p_gt_2 p_odd unfolding M_def by (intro cong_diff_nat two_power_odd_mod_12) auto
  thus "[M = 7] (mod 12)" by simp
qed

lemma Legendre_3_M: "Legendre 3 M = -1"
  using prime M_cong_7_mod_12 by (subst Legendre_3_left) (auto simp: cong_def)

lemma M_cong_7_mod_8: "[M = 7] (mod 8)"
proof -
  have "2 ^ 3 dvd (2 ^ p :: int)"
    using p_gt_2 by (intro le_imp_power_dvd) auto
  hence "[2 ^ p - 1 = 0 - 1] (mod (8 :: int))"
    by (intro cong_diff) (auto simp: cong_def)
  also have "2 ^ p - 1 = int M"
    by (simp add: M_def of_nat_diff)
  finally have "int M mod int 8 = 7"
    by (simp add: cong_def)
  thus "[M = 7] (mod 8)"
    by (subst (asm) zmod_int [symmetric]) (auto simp: cong_def)
qed 

lemma Legendre_2_M: "Legendre 2 M = 1"
  using prime M_gt_6 M_cong_7_mod_8
  by (subst supplement2_Legendre') (auto simp: cong_def nat_mod_as_int)

lemma M_not_dvd_24: "\<not>M dvd 24"
proof
  assume "M dvd 24"
  hence "M dvd 2 * 2 * 2 * 3"
    by simp
  also have "?this \<longleftrightarrow> M dvd 2 \<or> M dvd 3"
    using prime by (simp only: prime_dvd_mult_iff) auto
  finally show False using M_gt_6 by (auto dest: dvd_imp_le)
qed

end


subsection \<open>The Lucas--Lehmer sequence\<close>

text \<open>
  We now define the Lucas--Lehmer sequence $a_{n+1} = a_n ^ 2 - 2$. The starting value
  we will always use is $a_0 = 4$.
\<close>
primrec gen_lucas_lehmer_sequence :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "gen_lucas_lehmer_sequence a 0 = a"
| "gen_lucas_lehmer_sequence a (Suc n) = gen_lucas_lehmer_sequence a n ^ 2 - 2"

lemma gen_lucas_lehmer_sequence_Suc':
  "gen_lucas_lehmer_sequence a (Suc n) = gen_lucas_lehmer_sequence (a ^ 2 - 2) n"
  by (induction n arbitrary: a) auto

lemmas gen_lucas_lehmer_code [code] =
  gen_lucas_lehmer_sequence.simps(1) gen_lucas_lehmer_sequence_Suc'

text \<open>
  For $a_0 = 4$, the recurrence has the closed form $a_{4,n} = \omega^{2^n} + \bar\omega^{2^n}$
  with $\omega = 2 + \sqrt{3}$ and $\bar\omega = 2 - \sqrt{3}$.
\<close>
lemma gen_lucas_lehmer_sequence_4_closed_form1:
  "real_of_int (gen_lucas_lehmer_sequence 4 n) = (2 + sqrt 3) ^ (2 ^ n) + (2 - sqrt 3) ^ (2 ^ n)"
  by (induction n)
     (auto simp: algebra_simps power2_eq_square power_mult simp flip: power_mult_distrib)

lemma gen_lucas_lehmer_sequence_4_closed_form2:
  "gen_lucas_lehmer_sequence 4 n = round ((2 + sqrt 3) ^ (2 ^ n))"
proof (rule sym, rule round_unique')
  have "5 / 3 < sqrt (3 :: real)"
    by (rule real_less_rsqrt) (auto simp: power2_eq_square)
  hence "(2 - sqrt 3) ^ (2 ^ n) < (1 / 3) ^ (2 ^ n)"
    by (intro power_strict_mono) (auto simp: real_le_lsqrt)
  also have "\<dots> \<le> (1 / 3) ^ 1"
    by (intro power_decreasing) auto
  finally have "(2 - sqrt 3) ^ (2 ^ n) < 1 / 2" by simp
  moreover have "(2 - sqrt 3) ^ (2 ^ n) \<ge> 0"
    by (intro zero_le_power) (auto simp: real_le_lsqrt)
  ultimately show "\<bar>(2 + sqrt 3) ^ 2 ^ n - real_of_int (gen_lucas_lehmer_sequence 4 n)\<bar> < 1 / 2"
    unfolding gen_lucas_lehmer_sequence_4_closed_form1 by linarith
qed

lemma gen_lucas_lehmer_sequence_4_closed_form3:
  "gen_lucas_lehmer_sequence 4 n = \<lceil>(2 + sqrt 3) ^ (2 ^ n)\<rceil>"
proof (rule sym, rule ceiling_unique)
  show "real_of_int (gen_lucas_lehmer_sequence 4 n) \<ge> (2 + sqrt 3) ^ 2 ^ n"
    unfolding gen_lucas_lehmer_sequence_4_closed_form1 by (auto intro!: zero_le_power real_le_lsqrt)
next
  have "5 / 3 < sqrt (3 :: real)"
    by (rule real_less_rsqrt) (auto simp: power2_eq_square)
  hence "(2 - sqrt 3) ^ (2 ^ n) < (1 / 3) ^ (2 ^ n)"
    by (intro power_strict_mono) (auto simp: real_le_lsqrt)
  also have "\<dots> \<le> (1 / 3) ^ 1"
    by (intro power_decreasing) auto
  finally have "(2 - sqrt 3) ^ (2 ^ n) < 1 / 2" by simp
  moreover have "(2 - sqrt 3) ^ (2 ^ n) \<ge> 0"
    by (intro zero_le_power) (auto simp: real_le_lsqrt)
  ultimately show "real_of_int (gen_lucas_lehmer_sequence 4 n) - 1 < (2 + sqrt 3) ^ 2 ^ n"
    unfolding gen_lucas_lehmer_sequence_4_closed_form1 by linarith
qed


subsection \<open>The ring $\mathbb{Z}[\sqrt{3}]$\<close>

text \<open>
  To relate this sequence to Mersenne primes, we now first need to define the ring
  $\mathbb{Z}[\sqrt{3}]$, which is a subring of $\mathbb{R}$. This ring can be seen as the
  lattice on $\mathbb{R}$ that is freely generated by $1$ and $\sqrt{3}$.

  It is, however, more convenient to explicitly describe it as a ring structure over the 
  set $\mathbb{Z}\times\mathbb{Z}$ with a corresponding injective homomorphism
  $\mathbb{Z}\times\mathbb{Z} \to \mathbb{R}$.
\<close>

definition lucas_lehmer_add' :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "lucas_lehmer_add' = (\<lambda>(a,b) (c,d). (a + c, b + d))"

definition lucas_lehmer_mult' :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "lucas_lehmer_mult' = (\<lambda>(a,b) (c,d). (a * c + 3 * b * d, a * d + b * c))"

definition lucas_lehmer_ring :: "(int \<times> int) ring" where
  "lucas_lehmer_ring =
     \<lparr>carrier = UNIV,
      monoid.mult = lucas_lehmer_mult',
      one = (1, 0),
      ring.zero = (0, 0),
      add = lucas_lehmer_add'\<rparr>"

lemma carrier_lucas_lehmer_ring [simp]: "carrier lucas_lehmer_ring = UNIV"
  by (simp add: lucas_lehmer_ring_def)

lemma cring_lucas_lehmer_ring [intro]: "cring (lucas_lehmer_ring)"
proof
  have "\<exists>aa ba. lucas_lehmer_add' (aa, ba) (a, b) = (0, 0) \<and>
                lucas_lehmer_add' (a, b) (aa, ba) = (0, 0)" for a b
    by (rule exI[of _ "-a"], rule exI[of _ "-b"]) (auto simp: lucas_lehmer_add'_def)
  thus "carrier (add_monoid lucas_lehmer_ring) \<subseteq> Units (add_monoid lucas_lehmer_ring)"
    by (auto simp: Units_def lucas_lehmer_ring_def)
qed (auto simp: lucas_lehmer_ring_def lucas_lehmer_add'_def lucas_lehmer_mult'_def algebra_simps)


subsection \<open>The ring $(\mathbb{Z}/m\mathbb{Z})[\sqrt{3}]$\<close>

text \<open>
  We shall also need the ring $(\mathbb{Z}/m\mathbb{Z})[\sqrt{3}]$, which is obtained from
  $\mathbb{Z}[\sqrt{3}]$ by reducing each component separately modulo $m$. This essentially
  identifies any two points that are a multiple of $m$ apart and then all those that are
  a multiple of $m\sqrt{3}$ apart.
\<close>
definition lucas_lehmer_mult :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "lucas_lehmer_mult m = (\<lambda>(a,b) (c,d). ((a * c + 3 * b * d) mod m, (a * d + b * c) mod m))"

definition lucas_lehmer_add :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "lucas_lehmer_add m = (\<lambda>(a,b) (c,d). ((a + c) mod m, (b + d) mod m))"

definition lucas_lehmer_ring_mod :: "nat \<Rightarrow> (nat \<times> nat) ring" where
  "lucas_lehmer_ring_mod m =
     \<lparr>carrier = {..<m} \<times> {..<m},
      monoid.mult = lucas_lehmer_mult m,
      one = (1, 0),
      ring.zero = (0, 0),
      add = lucas_lehmer_add m\<rparr>"

lemma lucas_lehmer_add_in_carrier: "m > 0 \<Longrightarrow> lucas_lehmer_add m x y \<in> {..<m} \<times> {..<m}"
  by (auto simp: lucas_lehmer_add_def split: prod.splits)

lemma lucas_lehmer_mult_in_carrier: "m > 0 \<Longrightarrow> lucas_lehmer_mult m x y \<in> {..<m} \<times> {..<m}"
  by (auto simp: lucas_lehmer_mult_def split: prod.splits)

lemma lucas_lehmer_add_cong:
  "[fst (lucas_lehmer_add m x y) = fst x + fst y] (mod m)"
  "[snd (lucas_lehmer_add m x y) = snd x + snd y] (mod m)"
  by (simp_all add: lucas_lehmer_add_def cong_def case_prod_unfold)

lemma lucas_lehmer_mult_cong:
  "[fst (lucas_lehmer_mult m x y) = fst x * fst y + 3 * snd x * snd y] (mod m)"
  "[snd (lucas_lehmer_mult m x y) = fst x * snd y + snd x * fst y] (mod m)"
  by (simp_all add: lucas_lehmer_mult_def cong_def case_prod_unfold)

lemma lucas_lehmer_add_neutral [simp]:
  assumes "fst x < m" "snd x < m"
  shows   "lucas_lehmer_add m (0, 0) x = x"
    and   "lucas_lehmer_add m x (0, 0) = x"
  using assms by (auto simp: lucas_lehmer_add_def case_prod_unfold)

lemma lucas_lehmer_mult_neutral [simp]:
  assumes "fst x < m" "snd x < m"
  shows   "lucas_lehmer_mult m (Suc 0, 0) x = x"
    and   "lucas_lehmer_mult m x (Suc 0, 0) = x"
  using assms by (auto simp: lucas_lehmer_mult_def case_prod_unfold)

lemma lucas_lehmer_add_commute: "lucas_lehmer_add m x y = lucas_lehmer_add m y x"
  by (simp add: lucas_lehmer_add_def algebra_simps case_prod_unfold)

lemma lucas_lehmer_mult_commute: "lucas_lehmer_mult m x y = lucas_lehmer_mult m y x"
  by (simp add: lucas_lehmer_mult_def algebra_simps case_prod_unfold)

lemma lucas_lehmer_add_assoc:
  assumes m: "m > 0"
  shows   "lucas_lehmer_add m x (lucas_lehmer_add m y z) =
           lucas_lehmer_add m (lucas_lehmer_add m x y) z"
proof (rule prod_eqI)
  let ?add = "lucas_lehmer_add m"
  have "[fst (?add x (?add y z)) = fst x + (fst y + fst z)] (mod m)"
    by (rule lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+
  also have "fst x + (fst y + fst z) = (fst x + fst y) + fst z"
    by (simp add: add_ac)
  also have "[\<dots> = fst (?add (?add x y) z)] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "fst (?add x (?add y z)) = fst (?add (?add x y) z)"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_add_def case_prod_unfold\<close>)

  have "[snd (?add x (?add y z)) = snd x + (snd y + snd z)] (mod m)"
    by (rule lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+
  also have "snd x + (snd y + snd z) = (snd x + snd y) + snd z"
    by (simp add: add_ac)
  also have "[\<dots> = snd (?add (?add x y) z)] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "snd (?add x (?add y z)) = snd (?add (?add x y) z)"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_add_def case_prod_unfold\<close>)
qed

lemma lucas_lehmer_mult_assoc:
  assumes m: "m > 0"
  shows   "lucas_lehmer_mult m x (lucas_lehmer_mult m y z) =
           lucas_lehmer_mult m (lucas_lehmer_mult m x y) z"
proof (rule prod_eqI)
  let ?mul = "lucas_lehmer_mult m"
  have "[fst (?mul x (?mul y z)) = fst x * (fst y * fst z + 3 * snd y * snd z) +
           3 * snd x * (fst y * snd z + snd y * fst z)] (mod m)"
    by (rule lucas_lehmer_mult_cong[THEN cong_trans] cong_add cong_mult cong_refl)+
  also have "fst x * (fst y * fst z + 3 * snd y * snd z) +
               3 * snd x * (fst y * snd z + snd y * fst z) =
             (fst x * fst y + 3 * snd x * snd y) * fst z +
               3 * (fst x * snd y + snd x * fst y) * snd z"
    by (simp add: algebra_simps)
  also have "[\<dots> = fst (?mul (?mul x y) z)] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_mult_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "fst (?mul x (?mul y z)) = fst (?mul (?mul x y) z)"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_mult_def case_prod_unfold\<close>)

  have "[snd (?mul x (?mul y z)) = fst x * (fst y * snd z + snd y * fst z) +
     snd x * (fst y * fst z + 3 * snd y * snd z)] (mod m)"
    by (rule lucas_lehmer_mult_cong[THEN cong_trans] cong_add cong_mult cong_refl)+
  also have "fst x * (fst y * snd z + snd y * fst z) + snd x * (fst y * fst z + 3 * snd y * snd z) =
             (fst x * fst y + 3 * snd x * snd y) * snd z + (fst x * snd y + snd x * fst y) * fst z"
    by (simp add: algebra_simps)
  also have "[\<dots> = snd (?mul (?mul x y) z)] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_mult_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "snd (?mul x (?mul y z)) = snd (?mul (?mul x y) z)"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_mult_def case_prod_unfold\<close>)
qed

lemma lucas_lehmer_distrib_right:
  assumes m: "m > 1"
  shows "lucas_lehmer_mult m (lucas_lehmer_add m x y) z =
         lucas_lehmer_add m (lucas_lehmer_mult m x z) (lucas_lehmer_mult m y z)"
proof (rule prod_eqI)
  let ?mul = "lucas_lehmer_mult m" and ?add = "lucas_lehmer_add m"
  have "[fst (?mul (?add x y) z) = (fst x + fst y) * fst z + 3 * (snd x + snd y) * snd z] (mod m)"
    by (rule lucas_lehmer_mult_cong[THEN cong_trans] lucas_lehmer_add_cong[THEN cong_trans]
             cong_add cong_mult cong_refl)+
  also have "(fst x + fst y) * fst z + 3 * (snd x + snd y) * snd z =
               (fst x * fst z + 3 * snd x * snd z) + (fst y * fst z + 3 * snd y * snd z)"
    by (simp add: algebra_simps)
  also have "[\<dots> = fst (?add (?mul x z) (?mul y z))] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_mult_cong[THEN cong_trans]
          lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "fst (?mul (?add x y) z) = fst (?add (?mul x z) (?mul y z))"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_add_def lucas_lehmer_mult_def case_prod_unfold\<close>)

  have "[snd (?mul (?add x y) z) = (fst x + fst y) * snd z + (snd x + snd y) * fst z] (mod m)"
    by (rule lucas_lehmer_mult_cong[THEN cong_trans] lucas_lehmer_add_cong[THEN cong_trans]
             cong_add cong_mult cong_refl)+
  also have "(fst x + fst y) * snd z + (snd x + snd y) * fst z =
               (fst x * snd z + snd x * fst z) + (fst y * snd z + snd y * fst z)"
    by (simp add: algebra_simps)
  also have "[\<dots> = snd (?add (?mul x z) (?mul y z))] (mod m)"
    by (rule cong_sym, (rule lucas_lehmer_mult_cong[THEN cong_trans]
          lucas_lehmer_add_cong[THEN cong_trans] cong_add cong_mult cong_refl)+)
  finally show "snd (?mul (?add x y) z) = snd (?add (?mul x z) (?mul y z))"
    by (rule cong_less_modulus_unique_nat)
       (use m in \<open>auto simp: lucas_lehmer_add_def lucas_lehmer_mult_def case_prod_unfold\<close>)
qed

lemma lucas_lehmer_distrib_left:
  assumes "m > 1"
  shows "lucas_lehmer_mult m z (lucas_lehmer_add m x y) =
         lucas_lehmer_add m (lucas_lehmer_mult m z x) (lucas_lehmer_mult m z y)"
  using lucas_lehmer_distrib_right[of m x y z] assms
  by (simp add: lucas_lehmer_mult_commute)

lemma cring_lucas_lehmer_ring_mod [intro]:
  assumes "m > 1"
  shows   "cring (lucas_lehmer_ring_mod m)"
proof unfold_locales
  let ?neg = "\<lambda>x. if x = 0 then 0 else m - x"
  have "\<exists>x\<in>carrier (lucas_lehmer_ring_mod m).
           x \<oplus>\<^bsub>lucas_lehmer_ring_mod m\<^esub> (a, b) = \<zero>\<^bsub>lucas_lehmer_ring_mod m\<^esub> \<and>
           (a, b) \<oplus>\<^bsub>lucas_lehmer_ring_mod m\<^esub> x = \<zero>\<^bsub>lucas_lehmer_ring_mod m\<^esub>"
    if "(a, b) \<in> carrier (lucas_lehmer_ring_mod m)" for a b
    using that assms
    by (intro bexI[of _ "(?neg a, ?neg b)"])
       (auto simp: lucas_lehmer_ring_mod_def lucas_lehmer_add_def)
  thus "carrier (add_monoid (lucas_lehmer_ring_mod m)) \<subseteq> Units (add_monoid (lucas_lehmer_ring_mod m))"
    by (auto simp: Units_def)
qed (insert assms,
     auto simp: lucas_lehmer_ring_mod_def algebra_simps lucas_lehmer_mult_assoc
                lucas_lehmer_add_assoc lucas_lehmer_distrib_right lucas_lehmer_distrib_left
          intro: lucas_lehmer_mult_in_carrier lucas_lehmer_add_in_carrier
                 lucas_lehmer_add_commute lucas_lehmer_mult_commute)

text \<open>
  Since $0$ is clearly not a unit in the ring and its carrier has size $m ^ 2$, the 
  number of units is strictly less than $m ^ 2$.
\<close>
lemma card_lucas_lehmer_Units:
  assumes "m > 1"
  shows   "card (Units (lucas_lehmer_ring_mod m)) < m ^ 2"
proof -
  interpret cring "lucas_lehmer_ring_mod m"
    using assms by auto
  have "m ^ 2 > 0"
    using assms by auto
  from assms have "card (Units (lucas_lehmer_ring_mod m)) \<le> card ({..<m} \<times> {..<m} - {(0, 0)})"
    by (intro card_mono) (auto simp: Units_def lucas_lehmer_ring_mod_def lucas_lehmer_mult_def)
  also have "\<dots> = m ^ 2 - 1"
    using assms by (subst card_Diff_subset) (auto simp: power2_eq_square)
  finally show ?thesis using \<open>m ^ 2 > 0\<close> by linarith
qed

text \<open>
  Consider now the case of a prime modulus $m$: Since $\mathbb{Z}/m\mathbb{Z} = \text{GF}(m)$
  is a field, any element of $\mathbb{Z}/m\mathbb{Z}$ is a unit in
  $(\mathbb{Z}/m\mathbb{Z})[\sqrt{3}]$.
\<close>
lemma int_in_Units_lucas_lehmer_ring_mod:
  assumes "prime p"
  assumes "x > 0" "x < p"
  shows   "(x, 0) \<in> Units (lucas_lehmer_ring_mod p)"
proof -
  define R where "R = lucas_lehmer_ring_mod p"
  have "[x * (x ^ (p - 2) mod p) = x * x ^ (p - 2)] (mod p)"
    by (intro cong_mult) (auto simp: cong_def)
  also have "x * x ^ (p - 2) = x ^ (Suc (p - 2))"
    by (simp add: mult_ac)
  also have "Suc (p - 2) = p - 1"
    using prime_gt_1_nat[of p] assms by simp
  also have "[x ^ (p - 1) = 1] (mod p)"
    using assms by (intro fermat_theorem) (auto dest: dvd_imp_le)
  finally have "(x, 0) \<otimes>\<^bsub>R\<^esub> (x ^ (p - 2) mod p, 0) = \<one>\<^bsub>R\<^esub>"
               "(x ^ (p - 2) mod p, 0) \<otimes>\<^bsub>R\<^esub> (x, 0) = \<one>\<^bsub>R\<^esub>"
               "(x ^ (p - 2) mod p, 0) \<in> carrier R"
    using prime_gt_1_nat[of p] assms
    by (auto simp: lucas_lehmer_mult_def cong_def lucas_lehmer_ring_mod_def mult_ac R_def)
  moreover from assms have "(x, 0) \<in> carrier R"
    by (auto simp: R_def lucas_lehmer_ring_mod_def)
  ultimately show ?thesis using assms
    by (auto simp: Units_def R_def)
qed


subsection \<open>$\mathbb{Z}[\sqrt{3}]$ as a subring of $\mathbb{R}$\<close>

text \<open>
  We now define the homomorphism from $\mathbb{Z}[\sqrt{3}]$ into the reals:
\<close>
definition lucas_lehmer_to_real :: "int \<times> int \<Rightarrow> real" where
  "lucas_lehmer_to_real = (\<lambda>(a,b). real_of_int a + real_of_int b * sqrt 3)"

context
begin

interpretation cring lucas_lehmer_ring ..

lemma minus_lucas_lehmer_ring: "\<ominus>\<^bsub>lucas_lehmer_ring\<^esub> x = (case x of (a, b) \<Rightarrow> (-a, -b))"
  by (rule sym, rule sum_zero_eq_neg)
     (auto simp: case_prod_unfold lucas_lehmer_ring_def lucas_lehmer_add'_def)

lemma lucas_lehmer_to_real_simps1:
      "lucas_lehmer_to_real (a, b) = of_int a + of_int b * sqrt 3"
      "lucas_lehmer_to_real (x \<oplus>\<^bsub>lucas_lehmer_ring\<^esub> y) =
       lucas_lehmer_to_real x + lucas_lehmer_to_real y"
      "lucas_lehmer_to_real (x \<otimes>\<^bsub>lucas_lehmer_ring\<^esub> y) =
       lucas_lehmer_to_real x * lucas_lehmer_to_real y"
      "lucas_lehmer_to_real (\<ominus>\<^bsub>lucas_lehmer_ring\<^esub> x) = -lucas_lehmer_to_real x"
      "lucas_lehmer_to_real (\<zero>\<^bsub>lucas_lehmer_ring\<^esub>) = 0"
      "lucas_lehmer_to_real (\<one>\<^bsub>lucas_lehmer_ring\<^esub>) = 1"
  using minus_lucas_lehmer_ring
  by (simp_all add: lucas_lehmer_to_real_def lucas_lehmer_add'_def lucas_lehmer_mult'_def
                    case_prod_unfold algebra_simps lucas_lehmer_ring_def)

lemma lucas_lehmer_to_add_pow_nat:
  "lucas_lehmer_to_real ([n] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x) = of_nat n * lucas_lehmer_to_real x"
  by (induction n) (auto simp: lucas_lehmer_to_real_simps1 algebra_simps)

lemma lucas_lehmer_to_add_pow_int:
  "lucas_lehmer_to_real ([n] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x) = of_int n * lucas_lehmer_to_real x"
proof (cases "n \<ge> 0")
  case True
  hence "lucas_lehmer_to_real ([n] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x) =
         lucas_lehmer_to_real ([int (nat n)] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x)"
    by simp
  also have "\<dots> = lucas_lehmer_to_real ([nat n] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x)"
    by (simp add: add_pow_int_ge)
  also have "\<dots> = of_int n * lucas_lehmer_to_real x" using True
    by (simp add: lucas_lehmer_to_add_pow_nat algebra_simps)
  finally show ?thesis .
next
  case False
  hence "lucas_lehmer_to_real ([n] \<cdot>\<^bsub>lucas_lehmer_ring\<^esub> x) =
         lucas_lehmer_to_real (add_pow lucas_lehmer_ring (-int (nat (-n))) x)"
    by simp
  also have "add_pow lucas_lehmer_ring (-int (nat (-n))) x =
              \<ominus>\<^bsub>lucas_lehmer_ring\<^esub> (add_pow lucas_lehmer_ring (nat (-n)) x)"
    using False by (subst add.int_pow_neg_int) (auto simp: lucas_lehmer_ring_def)
  also have "lucas_lehmer_to_real \<dots> = of_int n * lucas_lehmer_to_real x" using False
    by (simp add: lucas_lehmer_to_add_pow_nat lucas_lehmer_to_real_simps1 algebra_simps)
  finally show ?thesis .
qed

lemma lucas_lehmer_to_real_power:
  "lucas_lehmer_to_real (x [^]\<^bsub>lucas_lehmer_ring\<^esub> (n :: nat)) = lucas_lehmer_to_real x ^ n"
  by (induction n) (auto simp: lucas_lehmer_to_real_simps1)

lemmas lucas_lehmer_to_real_simps =
  lucas_lehmer_to_real_simps1 lucas_lehmer_to_real_power
  lucas_lehmer_to_add_pow_nat lucas_lehmer_to_add_pow_int

end

lemma lucas_lehmer_to_real_inj: "inj lucas_lehmer_to_real"
proof (rule injI, clarify)
  fix a b c d :: int
  assume eq: "lucas_lehmer_to_real (a, b) = lucas_lehmer_to_real (c, d)"
  have "b = d"
  proof (rule ccontr)
    assume "b \<noteq> d"
    hence "sqrt 3 = (c - a) / (b - d)"
      using eq by (simp add: lucas_lehmer_to_real_def field_simps)
    also have "\<dots> \<in> \<rat>" by auto
    finally have "sqrt 3 \<in> \<rat>" .
    moreover have "sqrt 3 \<notin> \<rat>"
      using is_nth_power_prime_power_nat_iff[of 3 2 1] irrat_sqrt_nonsquare[of 3] by auto
    ultimately show False by contradiction
  qed
  moreover from this and eq have "a = c"
    by (auto simp: lucas_lehmer_to_real_def)
  ultimately show "a = c \<and> b = d" by blast
qed


subsection \<open>The canonical homomorphism $\mathbb{Z}[\sqrt 3] \to (\mathbb{Z}/m\mathbb{Z})[\sqrt 3]$\<close>

text \<open>
  Next, we show that reduction modulo $m$ is indeed a homomorphism.
\<close>
definition lucas_lehmer_hom :: "nat \<Rightarrow> (int \<times> int) \<Rightarrow> (nat \<times> nat)" where
  "lucas_lehmer_hom m = (\<lambda>(x,y). (nat (x mod m), nat (y mod m)))"

lemma lucas_lehmer_hom_cong:
  "[fst x = fst y] (mod int m) \<Longrightarrow> [snd x = snd y] (mod int m) \<Longrightarrow>
   lucas_lehmer_hom m x = lucas_lehmer_hom m y"
  by (auto simp: lucas_lehmer_hom_def cong_def case_prod_unfold)

lemma lucas_lehmer_hom_cong':
  "[a = b] (mod int m) \<Longrightarrow> [c = d] (mod int m) \<Longrightarrow>
   lucas_lehmer_hom m (a, c) = lucas_lehmer_hom m (b, d)"
  by (auto simp: lucas_lehmer_hom_def cong_def)

context
  fixes m :: nat
  assumes m: "m > 1"
begin

lemma lucas_lehmer_hom_in_carrier: "lucas_lehmer_hom m x \<in> {..<m} \<times> {..<m}"
  using m nat_less_iff by (auto simp: lucas_lehmer_hom_def case_prod_unfold)

lemma lucas_lehmer_hom_add:
  "lucas_lehmer_hom m (lucas_lehmer_add' x y) =
   lucas_lehmer_add m (lucas_lehmer_hom m x) (lucas_lehmer_hom m y)"
proof (rule prod_eqI)
  let ?add1 = "lucas_lehmer_add'" and ?add2 = "lucas_lehmer_add m"
  let ?\<phi> = "lucas_lehmer_hom m"
  have "fst (?\<phi> (?add1 x y)) = nat ((fst x + fst y) mod int m)"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_add'_def case_prod_unfold)
  also have "(fst x + fst y) mod int m = ((fst x mod m) + (fst y mod m)) mod int m"
    by (simp add: mod_add_eq)
  also have "nat \<dots> = (nat (fst x mod int m) + nat (fst y mod int m)) mod m"
    using m nat_add_distrib nat_mod_distrib by auto
  also have "\<dots> = fst (?add2 (?\<phi> x) (?\<phi> y))"
    by (auto simp: lucas_lehmer_hom_def lucas_lehmer_add_def case_prod_unfold)
  finally show "fst (?\<phi> (?add1 x y)) = fst (?add2 (?\<phi> x) (?\<phi> y))" .

  have "snd (?\<phi> (?add1 x y)) = nat ((snd x + snd y) mod int m)"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_add'_def case_prod_unfold)
  also have "(snd x + snd y) mod int m = ((snd x mod m) + (snd y mod m)) mod int m"
    by (simp add: mod_add_eq)
  also have "nat \<dots> = (nat (snd x mod int m) + nat (snd y mod int m)) mod m"
    using m nat_add_distrib nat_mod_distrib by auto
  also have "\<dots> = snd (?add2 (?\<phi> x) (?\<phi> y))"
    by (auto simp: lucas_lehmer_hom_def lucas_lehmer_add_def case_prod_unfold)
  finally show "snd (?\<phi> (?add1 x y)) = snd (?add2 (?\<phi> x) (?\<phi> y))" .
qed

lemma lucas_lehmer_hom_mult:
  "lucas_lehmer_hom m (lucas_lehmer_mult' x y) =
   lucas_lehmer_mult m (lucas_lehmer_hom m x) (lucas_lehmer_hom m y)"
proof (rule prod_eqI)
  let ?mul1 = "lucas_lehmer_mult'" and ?mul2 = "lucas_lehmer_mult m"
  let ?\<phi> = "lucas_lehmer_hom m"
  have "fst (?\<phi> (?mul1 x y)) = nat ((fst x * fst y + 3 * snd x * snd y) mod int m)"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_mult'_def case_prod_unfold)
  also have "(fst x * fst y + 3 * snd x * snd y) mod int m =
               ((fst x mod int m) * (fst y mod int m) +
                3 * (snd x mod int m) * (snd y mod int m)) mod m"
    by (intro congD cong_mult cong_add cong_refl) (auto simp: cong_def)
  also have "\<dots> = int (nat (((fst x mod int m) * (fst y mod int m) +
                3 * (snd x mod int m) * (snd y mod int m)) mod m))"
    using m by (subst of_nat_nat) auto
  also have "\<dots> = int (nat (fst x mod int m) * nat (fst y mod int m) +
                3 * (nat (snd x mod int m)) * nat (snd y mod int m)) mod m"
    using m by simp
  also have "nat \<dots> = (nat (fst x mod int m) * nat (fst y mod int m) +
           3 * nat (snd x mod int m) * nat (snd y mod int m)) mod m"
    using m by (metis nat_int zmod_int)
  also have "\<dots> = fst (?mul2 (?\<phi> x) (?\<phi> y))"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_mult_def case_prod_unfold)
  finally show "fst (?\<phi> (?mul1 x y)) = fst (?mul2 (?\<phi> x) (?\<phi> y))" .

  have "snd (?\<phi> (?mul1 x y)) = nat ((fst x * snd y + snd x * fst y) mod int m)"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_mult'_def case_prod_unfold)
  also have "(fst x * snd y + snd x * fst y) mod int m =
               ((fst x mod int m) * (snd y mod int m) +
                (snd x mod int m) * (fst y mod int m)) mod m"
    by (intro congD cong_mult cong_add cong_refl) (auto simp: cong_def)
  also have "\<dots> = int (nat (((fst x mod int m) * (snd y mod int m) +
                (snd x mod int m) * (fst y mod int m)) mod m))"
    using m by (subst of_nat_nat) auto
  also have "\<dots> = int (nat (fst x mod int m) * nat (snd y mod int m) +
                    (nat (snd x mod int m)) * nat (fst y mod int m)) mod m"
    using m by simp
  also have "nat \<dots> = (nat (fst x mod int m) * nat (snd y mod int m) +
               nat (snd x mod int m) * nat (fst y mod int m)) mod m"
    using m by (metis nat_int zmod_int)
  also have "\<dots> = snd (?mul2 (?\<phi> x) (?\<phi> y))"
    by (simp add: lucas_lehmer_hom_def lucas_lehmer_mult_def case_prod_unfold)
  finally show "snd (?\<phi> (?mul1 x y)) = snd (?mul2 (?\<phi> x) (?\<phi> y))" .
qed

lemma lucas_lehmer_hom_1 [simp]: "lucas_lehmer_hom m (1, 0) = (1, 0)"
  using m by (simp add: lucas_lehmer_hom_def)

lemma ring_hom_lucas_lehmer_hom:
  "lucas_lehmer_hom m \<in> ring_hom lucas_lehmer_ring (lucas_lehmer_ring_mod m)"
proof -
  interpret R: cring lucas_lehmer_ring ..
  from m interpret S: cring "lucas_lehmer_ring_mod m" ..
  show ?thesis
    unfolding ring_hom_def using lucas_lehmer_hom_in_carrier m
    by (auto simp: lucas_lehmer_ring_mod_def lucas_lehmer_hom_add
                   lucas_lehmer_ring_def lucas_lehmer_hom_mult)
qed

end


subsection \<open>Correctness of the Lucas--Lehmer test\<close>

text \<open>
  In this section, we will prove that the Lucas--Lehmer test is both a necessary and sufficient
  condition for the primality of a Mersenne number of the form $2^p - 1$ for an odd prime $p$.
  The proof that shall be given here is rather explicit and heavily draws from the Wikipedia
  article on the Lucas--Lehmer test~\cite{wiki:lucas_lehmer}.

  A shorter and more high-level proof of a more general statement can be obtained using more
  theory on finite fields (in particular the field $\text{GF}(q^2)$ (cf.\ e.\,g.\ 
  Rödseth~\cite{roedseth94}).
\<close>

definition lucas_lehmer_test where
  "lucas_lehmer_test p = (p > 2 \<and>
     (2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2))"

text \<open>
  We can now prove that any Mersenne number $2^p - 1$ for $p$ prime that passes the 
  Lucas--Lehmer test is prime. We follow the simple argument given by Bruce~\cite{bruce93},
  which is also given on Wikipedia~\cite{wiki:lucas_lehmer}.
\<close>
theorem lucas_lehmer_sufficient:
  assumes "prime p" "odd p"
  assumes "(2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
  shows   "prime (2 ^ p - 1 :: nat)"
proof (rule ccontr)
  assume not_prime: "\<not>prime (2 ^ p - 1 :: nat)"
  from assms obtain k :: int where k: "gen_lucas_lehmer_sequence 4 (p - 2) = k * (2 ^ p - 1)"
    by (elim dvdE) (auto simp: mult_ac)
  from assms have "p > 2"
    using odd_prime_gt_2_nat by blast
  from \<open>p > 2\<close> have "2 ^ p \<ge> (2 ^ 3 :: nat)" by (intro power_increasing) auto
  hence "2 ^ p \<ge> (8 :: nat)" by simp

  define q :: nat where "q = Min (prime_factors (2 ^ p - 1))"
  have "q \<in> prime_factors (2 ^ p - 1)" using \<open>2 ^ p \<ge> 8\<close>
    unfolding q_def by (intro Min_in) (auto simp: prime_factorization_empty_iff)
  hence q: "prime q" "q dvd (2 ^ p - 1 :: nat)"
    by (auto simp: in_prime_factors_iff)
  have q_minimal: "q \<le> q'" if "q' \<in> prime_factors (2 ^ p - 1)" for q'
    unfolding q_def by (rule Min_le) (use that in auto)

  have "2 ^ p - 1 \<ge> q ^ 2"
  proof -
    from q obtain k where k: "2 ^ p - 1 = q * k" by auto
    have "prime_factorization (2 ^ p - 1 :: nat) \<noteq> {#q#}"
    proof
      assume *: "prime_factorization (2 ^ p - 1 :: nat) = {#q#}"
      have "2 ^ p - 1 = prod_mset (prime_factorization (2 ^ p - 1 :: nat))"
        using \<open>2 ^ p \<ge> 8\<close> by (subst prod_mset_prime_factorization_nat) auto
      also have "\<dots> = q" by (subst *) auto
      finally show False using not_prime q by simp
    qed
    hence "prime_factorization k \<noteq> {#}" using q k \<open>2 ^ p \<ge> 8\<close>
      by (subst (asm) k, subst (asm) prime_factorization_mult)
         (auto intro!: Nat.gr0I simp: prime_factorization_prime)
    hence "k \<noteq> 1" by (auto simp: prime_factorization_empty_iff)
    then obtain q' where q': "prime q'" "q' dvd k"
      using prime_factor_nat by blast
    from q' k \<open>2 ^ p \<ge> 8\<close> have "q \<le> q'"
      by (intro q_minimal) (auto simp: in_prime_factors_iff intro!: Nat.gr0I)
    hence "q ^ 2 \<le> q * q'"
      unfolding power2_eq_square by (intro mult_mono) auto
    also have "q * q' \<le> 2 ^ p - 1"
      using q q' k \<open>2 ^ p \<ge> 8\<close> by (intro dvd_imp_le) (auto intro!: Nat.gr0I)
    finally show "2 ^ p - 1 \<ge> q ^ 2" .
  qed

  have "q \<noteq> 2" using q \<open>p > 2\<close> by auto
  moreover from q have "q \<noteq> 0" "q \<noteq> 1" by auto
  ultimately have "q > 2" by auto

  write lucas_lehmer_ring ("R")
  define S where "S = lucas_lehmer_ring_mod q"
  define S' where "S' = units_of S"
  define \<phi> where "\<phi> = lucas_lehmer_hom q"

  interpret R: cring R ..
  interpret S: cring S
    unfolding S_def by (rule cring_lucas_lehmer_ring_mod) (use \<open>q > 2\<close> in auto)
  interpret S': comm_group S'
    unfolding S'_def by (rule S.units_comm_group)
  have "\<phi> \<in> ring_hom R S"
    unfolding \<phi>_def S_def by (rule ring_hom_lucas_lehmer_hom) (use \<open>q > 2\<close> in auto)
  interpret \<phi>: ring_hom_cring R S \<phi>
    by standard fact

  have "(2 + sqrt 3) ^ (2 ^ (p - 2)) + (2 - sqrt 3) ^ (2 ^ (p - 2)) =
          real_of_int (gen_lucas_lehmer_sequence 4 (p - 2))"
    unfolding gen_lucas_lehmer_sequence_4_closed_form1 ..
  also have "\<dots> = real_of_int k * (2 ^ p - 1)"
    by (simp add: k)
  finally have *: "(2 + sqrt 3) ^ (2 ^ (p - 2)) =
                     real_of_int k * (2 ^ p - 1) - (2 - sqrt 3) ^ (2 ^ (p - 2))"
    by (simp add: algebra_simps)
  have "((2 + sqrt 3) ^ (2 ^ (p - 2))) ^ 2 =
             real_of_int k * (2 ^ p - 1) * (2 + sqrt 3) ^ (2 ^ (p - 2)) -
             (2 - sqrt 3) ^ (2 ^ (p - 2)) * (2 + sqrt 3) ^ (2 ^ (p - 2))"
    unfolding power2_eq_square by (subst *) (simp add: algebra_simps)
  also have "((2 + sqrt 3) ^ (2 ^ (p - 2))) ^ 2 = (2 + sqrt 3) ^ (2 * 2 ^ (p - 2))"
    by (simp flip: power_mult add: mult_ac)
  also have "2 * 2 ^ (p - 2) = 2 ^ (Suc (p - 2))"
    by simp
  also from \<open>p > 2\<close> have "Suc (p - 2) = p - 1"
    by linarith
  also have "(2 - sqrt 3) ^ (2 ^ (p - 2)) * (2 + sqrt 3) ^ (2 ^ (p - 2)) = 1"
    by (subst power_mult_distrib [symmetric]) (auto simp: algebra_simps)
  finally have "(2 + sqrt 3) ^ (2 ^ (p - 1)) =
                  real_of_int k * (2 ^ p - 1) * (2 + sqrt 3) ^ (2 ^ (p - 2)) - 1" .

  also have "(2 + sqrt 3) ^ (2 ^ (p - 1)) =
               lucas_lehmer_to_real ((2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 1) :: nat))"
    by (simp add: lucas_lehmer_to_real_simps)
  also have "real_of_int k * (2 ^ p - 1) * (2 + sqrt 3) ^ (2 ^ (p - 2)) - 1 =
               lucas_lehmer_to_real ((k * (2 ^ p - 1), 0) \<otimes>\<^bsub>R\<^esub>
                 (2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)"
    by (simp add: lucas_lehmer_to_real_simps)
  finally have "((2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 1) :: nat)) =
                ((k * (2 ^ p - 1), 0) \<otimes>\<^bsub>R\<^esub> (2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)"
    by (rule injD[OF lucas_lehmer_to_real_inj])

  hence "\<phi> ((2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 1) :: nat)) =
           \<phi> ((k * (2 ^ p - 1), 0) \<otimes>\<^bsub>R\<^esub> (2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)"
    by (simp only:)
  also have "\<phi> ((2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 1) :: nat)) = \<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ (p - 1) :: nat)"
    by simp
  also {
    have "int q dvd int (2 ^ p - 1)"
      by (subst int_dvd_int_iff) (use q in auto)
    also have "int (2 ^ p - 1) = 2 ^ p - 1"
      by (simp add: of_nat_diff)
    finally have "\<phi> (k * (2 ^ p - 1), 0) = \<zero>\<^bsub>S\<^esub>"
      by (simp add: \<phi>_def lucas_lehmer_hom_def S_def lucas_lehmer_ring_mod_def)
  }
  hence "\<phi> ((k * (2 ^ p - 1), 0) \<otimes>\<^bsub>R\<^esub> (2, 1) [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) = 
           \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
    by simp
  finally have eq: "\<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ (p - 1) :: nat) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>" .

  have "\<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ p :: nat) = \<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ (p - 1) * 2 :: nat)"
    using \<open>p > 2\<close> by (cases p) (auto simp: mult_ac)
  also have "\<dots> = (\<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ (p - 1) :: nat)) [^]\<^bsub>S\<^esub> (2 :: nat)"
    by (subst S.nat_pow_pow) auto
  also have "\<dots> = \<one>\<^bsub>S\<^esub>"
    by (subst eq) (auto simp: numeral_2_eq_2 S.l_minus)
  finally have eq': "\<phi> (2, 1) [^]\<^bsub>S\<^esub> (2 ^ p :: nat) = \<one>\<^bsub>S\<^esub>" .

  from eq' have unit: "\<phi> (2, 1) \<in> Units S"
    by (rule S.pow_nat_eq_1_imp_unit) auto

  have neg_one_not_one: "\<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub> \<noteq> \<one>\<^bsub>S\<^esub>"
  proof
    assume *: "\<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub> = \<one>\<^bsub>S\<^esub>"
    have "(\<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>) \<oplus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub> = \<zero>\<^bsub>S\<^esub>"
      by (rule S.l_neg) auto
    hence "\<one>\<^bsub>S\<^esub> \<oplus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub> = \<zero>\<^bsub>S\<^esub>"
      by (simp only: *)
    thus False using \<open>q > 2\<close>
      by (auto simp: S_def lucas_lehmer_ring_mod_def lucas_lehmer_add_def)
  qed

  have fin: "finite (Units S)"
    by (rule finite_subset[of _ "carrier S"]) (auto simp: Units_def S_def lucas_lehmer_ring_mod_def)

  have "group.ord S' (\<phi> (2, 1)) = 2 ^ p"
    using \<open>p > 2\<close> eq eq' unit neg_one_not_one
    by (intro S'.ord_eqI_prime_factors)
       (auto simp: prime_factors_power prime_factorization_prime
                   S'_def S.units_of_pow units_of_carrier units_of_one power_diff)
  hence "2 ^ p = group.ord S' (\<phi> (2, 1))"
    by simp
  also have "\<dots> = card (generate S' {\<phi> (2, 1)})"
    using unit fin
    by (intro S'.generate_pow_card) (auto simp: S'_def units_of_carrier)
  also have "\<dots> \<le> card (carrier S')"
    using fin unit by (intro card_mono S'.generate_incl) (auto simp: S'_def units_of_carrier)
  also have "\<dots> < q ^ 2"
    unfolding S'_def S_def using card_lucas_lehmer_Units[of q] \<open>q > 2\<close>
    by (auto simp: units_of_carrier)
  also note \<open>q ^ 2 \<le> 2 ^ p - 1\<close>
  finally show False by simp
qed

text \<open>
  Next, we show that any Mersenne prime passes the Lucas--Lehmer test. We again follow the
  rather explicit proof outlined on Wikipedia~\cite{wiki:lucas_lehmer}, which is a simplified
  (but less general and less abstract) version of the proof by Rödseth~\cite{roedseth94}.
\<close>
theorem (in mersenne_prime) lucas_lehmer_necessary:
  "(2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
proof -
  write lucas_lehmer_ring ("R")
  define S where "S = lucas_lehmer_ring_mod M"
  define S' where "S' = units_of S"
  define \<phi> where "\<phi> = lucas_lehmer_hom M"

  interpret R: cring R ..
  interpret S: cring S unfolding S_def
    by (rule cring_lucas_lehmer_ring_mod) (use M_gt_6 in auto)
  interpret S': comm_group S'
    unfolding S'_def by (rule S.units_comm_group)
  have "\<phi> \<in> ring_hom R S" unfolding \<phi>_def S_def
    by (rule ring_hom_lucas_lehmer_hom) (use M_gt_6 in auto)
  interpret \<phi>: ring_hom_cring R S \<phi>
    by standard fact

  have R_pow_int: "(n, 0) [^]\<^bsub>R\<^esub> m = (n ^ m, 0)" for n :: int and m :: nat
    by (induction m; simp; simp add: lucas_lehmer_ring_def lucas_lehmer_mult'_def)

  have "add_pow R n \<one>\<^bsub>R\<^esub> = (int n, 0)" for n
    by (induction n; simp; simp add: lucas_lehmer_ring_def lucas_lehmer_add'_def)
  hence "add_pow R M \<one>\<^bsub>R\<^esub> = (int M, 0)"
    by simp
  also have "\<phi> \<dots> = \<zero>\<^bsub>S\<^esub>"
    by (simp add: \<phi>_def S_def lucas_lehmer_ring_mod_def lucas_lehmer_hom_def)
  finally have "add_pow S M \<one>\<^bsub>S\<^esub> = \<zero>\<^bsub>S\<^esub>"
    by (simp add: \<phi>.hom_add_pow_nat)

  define \<sigma> :: "int \<times> int" where "\<sigma> = (0, 2)"
  have eq1: "\<phi> ((6, 2) [^]\<^bsub>R\<^esub> M) = \<phi> (6, -2)"
  proof -
    have "(6, 2) = (6, 0) \<oplus>\<^bsub>R\<^esub> \<sigma>"
      by (simp add: lucas_lehmer_ring_def \<sigma>_def lucas_lehmer_add'_def)
    also have "\<phi> (\<dots> [^]\<^bsub>R\<^esub> M) = \<phi> ((6, 0) [^]\<^bsub>R\<^esub> M) \<oplus>\<^bsub>S\<^esub> \<phi> (\<sigma> [^]\<^bsub>R\<^esub> M)"
      using prime and \<open>add_pow S M \<one>\<^bsub>S\<^esub> = \<zero>\<^bsub>S\<^esub>\<close>
      by (simp add: S.binomial_finite_char)
    also have "(6, 0) [^]\<^bsub>R\<^esub> M = (6 ^ M, 0)"
      by (simp add: R_pow_int)
    also have "[6 ^ M = 6] (mod (int M))" using M_gt_6
      by (intro little_Fermat_int) (use prime in \<open>auto simp flip: dvd_nat_abs_iff\<close>)
    hence "\<phi> (6 ^ M, 0) = \<phi> (6, 0)"
      unfolding \<phi>_def by (intro lucas_lehmer_hom_cong) auto
    also have "\<sigma> = (2, 0) \<otimes>\<^bsub>R\<^esub> (0, 1)"
      by (simp add: \<sigma>_def lucas_lehmer_ring_def lucas_lehmer_mult'_def)
    hence "\<phi> (\<sigma> [^]\<^bsub>R\<^esub> M) = \<phi> ((2, 0) [^]\<^bsub>R\<^esub> M \<otimes>\<^bsub>R\<^esub> (0, 1) [^]\<^bsub>R\<^esub> M)"
      by (subst R.nat_pow_distrib [symmetric]) auto
    also have "\<dots> = \<phi> ((2, 0) [^]\<^bsub>R\<^esub> M) \<otimes>\<^bsub>S\<^esub> \<phi> ((0, 1) [^]\<^bsub>R\<^esub> M)"
      by simp
    also have "(2, 0) [^]\<^bsub>R\<^esub> M = (2 ^ M, 0)"
      by (simp add: R_pow_int)
    also have "[2 ^ M = 2] (mod int M)" using M_gt_6 prime
      by (intro little_Fermat_int) (auto simp flip: dvd_nat_abs_iff dest: dvd_imp_le)
    hence "\<phi> (2 ^ M, 0) = \<phi> (2, 0)"
      unfolding \<phi>_def by (intro lucas_lehmer_hom_cong) auto
    also have M_eq: "M = Suc (2 * ((M - 1) div 2))"
      using M_odd by auto
    have "(0, 1) [^]\<^bsub>R\<^esub> M = (0, 1) \<otimes>\<^bsub>R\<^esub> ((0, 1) [^]\<^bsub>R\<^esub> (2::nat)) [^]\<^bsub>R\<^esub> ((M - 1) div 2)"
      by (subst M_eq) (auto simp: R.nat_pow_mult R.nat_pow_pow R.cring_simprules)
    also have "(0, 1) [^]\<^bsub>R\<^esub> (2::nat) = (3, 0)"
      by (simp add: eval_nat_numeral) (simp add: lucas_lehmer_ring_def lucas_lehmer_mult'_def)
    also have "\<phi> ((0, 1) \<otimes>\<^bsub>R\<^esub> (3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) = 
                 \<phi> ((3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) \<otimes>\<^bsub>S\<^esub> \<phi> (0, 1)"
      by (simp add: S.cring_simprules)
    also have "(3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2) = (3 ^ ((M - 1) div 2), 0)"
      by (simp add: R_pow_int)
    also have "\<phi> (3 ^ ((M - 1) div 2), 0) = \<phi> (-1, 0)"
      unfolding \<phi>_def
    proof (intro lucas_lehmer_hom_cong')
      have "[3 ^ ((M - 1) div 2) = Legendre 3 M] (mod int M)"
        by (rule cong_sym, rule euler_criterion) (use prime M_gt_6 in auto)
      thus "[3 ^ ((M - 1) div 2) = -1] (mod int M)"
        by (simp add: Legendre_3_M)
    qed auto
    also have "\<phi> (2, 0) \<otimes>\<^bsub>S\<^esub> (\<phi> (- 1, 0) \<otimes>\<^bsub>S\<^esub> \<phi> (0, 1)) = \<phi> ((2, 0) \<otimes>\<^bsub>R\<^esub> (-1, 0) \<otimes>\<^bsub>R\<^esub> (0, 1))"
      by (simp add: R.cring_simprules S.cring_simprules)
    also have "\<phi> (6, 0) \<oplus>\<^bsub>S\<^esub> \<phi> ((2, 0) \<otimes>\<^bsub>R\<^esub> (- 1, 0) \<otimes>\<^bsub>R\<^esub> (0, 1)) =
                 \<phi> ((6, 0) \<oplus>\<^bsub>R\<^esub> (2, 0) \<otimes>\<^bsub>R\<^esub> (- 1, 0) \<otimes>\<^bsub>R\<^esub> (0, 1))"
      by simp
    also have "\<dots> = \<phi> (6, -2)" unfolding \<phi>_def
      by (intro lucas_lehmer_hom_cong)
         (auto simp: lucas_lehmer_ring_def lucas_lehmer_mult'_def lucas_lehmer_add'_def)
    finally show "\<phi> ((6, 2) [^]\<^bsub>R\<^esub> M) = \<phi> (6, -2)"
      by (simp add: R.cring_simprules S.cring_simprules)
  qed

  have eq2: "\<phi> ((24, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
  proof -
    have "(24, 0) = (2, 0) [^]\<^bsub>R\<^esub> (3::nat) \<otimes>\<^bsub>R\<^esub> (3, 0)"
      by (simp add: eval_nat_numeral) (auto simp: lucas_lehmer_ring_def lucas_lehmer_mult'_def)
    also have "\<dots> [^]\<^bsub>R\<^esub> ((M - 1) div 2) =
                 ((2, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) [^]\<^bsub>R\<^esub> (3::nat) \<otimes>\<^bsub>R\<^esub> (3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)"
      by (simp add: R.cring_simprules R.nat_pow_distrib R.nat_pow_pow mult_ac)
    also have "\<phi> \<dots> = (\<phi> ((2, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2))) [^]\<^bsub>S\<^esub> (3::nat) \<otimes>\<^bsub>S\<^esub> 
                      \<phi> ((3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2))" by simp
    also have "(2, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2) = (2 ^ ((M - 1) div 2), 0)"
      by (simp add: R_pow_int)
    also have "\<phi> \<dots> = \<phi> (1, 0)"
      unfolding \<phi>_def
    proof (intro lucas_lehmer_hom_cong')
      have "[2 ^ ((M - 1) div 2) = Legendre 2 M] (mod int M)"
        by (rule cong_sym, rule euler_criterion) (use prime M_gt_6 in auto)
      thus "[2 ^ ((M - 1) div 2) = 1] (mod int M)"
        using Legendre_2_M by simp
    qed auto
    also have "(1, 0) = \<one>\<^bsub>R\<^esub>"
      by (simp add: lucas_lehmer_ring_def)
    also have "(3, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2) = (3 ^ ((M - 1) div 2), 0)"
      by (simp add: R_pow_int)
    also have "\<phi> \<dots> = \<phi> (-1, 0)"
      unfolding \<phi>_def
    proof  (intro lucas_lehmer_hom_cong')
      have "[3 ^ ((M - 1) div 2) = Legendre 3 M] (mod int M)"
        by (rule cong_sym, rule euler_criterion) (use prime M_gt_6 in auto)
      thus "[3 ^ ((M - 1) div 2) = -1] (mod int M)"
        using Legendre_3_M by simp
    qed auto
    also have "(-1, 0) = \<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>"
      using minus_lucas_lehmer_ring by (simp add: lucas_lehmer_ring_def)
    finally show "\<phi> ((24, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
      by simp
  qed

  define \<omega> \<omega>' :: "int \<times> int" where "\<omega> = (2, 1)" and "\<omega>' = (2, -1)"
  have eq3: "\<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2)) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
  proof -
    have "(M + 1) div 2 = Suc ((M - 1) div 2)"
      using M_odd M_gt_6 by (auto elim!: oddE)  
    have *: "\<phi> ((24, 0) \<otimes>\<^bsub>R\<^esub> \<omega>) = \<phi> ((6, 2) [^]\<^bsub>R\<^esub> (2 :: nat))" unfolding \<phi>_def
      by (intro lucas_lehmer_hom_cong)
         (simp_all add: eval_nat_numeral,
          auto simp: lucas_lehmer_ring_def lucas_lehmer_mult'_def \<omega>_def)
    have "\<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<phi> ((24, 0) \<otimes>\<^bsub>R\<^esub> \<omega>) [^]\<^bsub>S\<^esub> ((M + 1) div 2) =
            \<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<phi> ((6, 2) [^]\<^bsub>R\<^esub> (2 :: nat)) [^]\<^bsub>S\<^esub> ((M + 1) div 2)"
      by (subst *) auto
    hence "\<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<phi> ((24, 0) [^]\<^bsub>R\<^esub> ((M + 1) div 2)) \<otimes>\<^bsub>S\<^esub> \<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2)) =
            \<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<phi> ((6, 2) [^]\<^bsub>R\<^esub> (2 * ((M + 1) div 2)))"
      by (simp add: R.nat_pow_distrib S.nat_pow_distrib R.nat_pow_pow
                    S.nat_pow_pow R.cring_simprules S.cring_simprules)
    also have "2 * ((M + 1) div 2) = M + 1"
      using M_odd by auto
    finally have "\<phi> (24, 0) \<otimes>\<^bsub>S\<^esub> (\<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<phi> ((24, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2))) \<otimes>\<^bsub>S\<^esub> 
                    \<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2)) =
                  \<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> (\<phi> (6, 2) \<otimes>\<^bsub>S\<^esub> \<phi> ((6, 2) [^]\<^bsub>R\<^esub> M))"
      by (subst (asm) \<open>(M + 1) div 2 = _\<close>) (simp add: S.cring_simprules R.cring_simprules)
  
    also have "\<phi> ((24, 0) [^]\<^bsub>R\<^esub> ((M - 1) div 2)) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
      by (subst eq2) auto
    also have "(\<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<otimes>\<^bsub>S\<^esub> \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>) = \<one>\<^bsub>S\<^esub>"
      by (simp add: S.cring_simprules)
    also have "\<phi> ((6, 2) [^]\<^bsub>R\<^esub> M) = \<phi> (6, -2)"
      by (subst eq1) auto
    also have "\<phi> (6, 2) \<otimes>\<^bsub>S\<^esub> \<phi> (6, -2) = \<phi> ((6, 2) \<otimes>\<^bsub>R\<^esub> (6, -2))"
      by simp
    also have "\<dots> = \<phi> (24, 0)" unfolding \<phi>_def
      by (intro lucas_lehmer_hom_cong) (auto simp: lucas_lehmer_ring_def lucas_lehmer_mult'_def)
    finally have "\<phi> (24, 0) \<otimes>\<^bsub>S\<^esub> (\<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2))) =
                  \<phi> (24, 0) \<otimes>\<^bsub>S\<^esub> \<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)"
      by (simp add: S.cring_simprules)
    also have "\<phi> (24, 0) = (24 mod M, 0)"
      by (simp add: \<phi>_def lucas_lehmer_hom_def nat_mod_as_int)
    finally have "(24 mod M, 0) \<otimes>\<^bsub>S\<^esub> (\<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2))) =
                  (24 mod M, 0) \<otimes>\<^bsub>S\<^esub> \<phi> (\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)" .
    moreover have "(24 mod M, 0) \<in> Units S"
      unfolding S_def using M_gt_6 prime M_not_dvd_24
      by (intro int_in_Units_lucas_lehmer_ring_mod) (auto simp: dvd_mod_iff intro!: Nat.gr0I)
    ultimately show "\<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2)) = \<ominus>\<^bsub>S\<^esub> \<one>\<^bsub>S\<^esub>"
      by (subst (asm) S.Units_l_cancel) auto
  qed

  have eq4: "\<phi> (\<omega> [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<omega>' [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat)) = \<zero>\<^bsub>S\<^esub>"
    (is "\<phi> ?lhs = _")
  proof -
    have "\<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 2)) \<otimes>\<^bsub>S\<^esub> \<phi> (\<omega>' [^]\<^bsub>R\<^esub> ((M + 1) div 4)) \<oplus>\<^bsub>S\<^esub>
            \<phi> (\<omega>' [^]\<^bsub>R\<^esub> ((M + 1) div 4)) = \<zero>\<^bsub>S\<^esub>"
      by (subst eq3) (auto simp: S.cring_simprules)
    also have "2 ^ 2 dvd (2 ^ p :: nat)"
      by (intro le_imp_power_dvd) (use p_gt_2 in auto)
    hence "4 dvd (M + 1)" by (auto simp: M_def)
    hence "(M + 1) div 2 = (M + 1) div 4 + (M + 1) div 4"
      by presburger
    also have "\<phi> (\<omega> [^]\<^bsub>R\<^esub> \<dots>) \<otimes>\<^bsub>S\<^esub> \<phi> (\<omega>' [^]\<^bsub>R\<^esub> ((M + 1) div 4)) =
               \<phi> (\<omega> \<otimes>\<^bsub>R\<^esub> \<omega>') [^]\<^bsub>S\<^esub> ((M + 1) div 4) \<otimes>\<^bsub>S\<^esub> \<phi> (\<omega> [^]\<^bsub>R\<^esub> ((M + 1) div 4))"
      by (simp add: S.cring_simprules S.nat_pow_distrib flip: S.nat_pow_mult)
    also have "\<phi> (\<omega> \<otimes>\<^bsub>R\<^esub> \<omega>') = \<phi> \<one>\<^bsub>R\<^esub>" unfolding \<phi>_def
      by (intro lucas_lehmer_hom_cong)
         (auto simp: \<omega>_def \<omega>'_def lucas_lehmer_ring_def lucas_lehmer_mult'_def)
    also have "(M + 1) div 4 = 2 ^ (p - 2)"
      using p_gt_2 by (auto simp: M_def power_diff)
    finally show eq4: "\<phi> (\<omega> [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat) \<oplus>\<^bsub>R\<^esub> \<omega>' [^]\<^bsub>R\<^esub> (2 ^ (p - 2) :: nat)) = \<zero>\<^bsub>S\<^esub>"
      by simp
  qed

  have "\<phi> ?lhs = \<zero>\<^bsub>S\<^esub>"
    by (rule eq4)
  also have "lucas_lehmer_to_real ?lhs =
             lucas_lehmer_to_real (gen_lucas_lehmer_sequence 4 (p - 2), 0)"
    by (simp add: \<omega>_def \<omega>'_def lucas_lehmer_to_real_simps gen_lucas_lehmer_sequence_4_closed_form1)
  hence "?lhs = (gen_lucas_lehmer_sequence 4 (p - 2), 0)"
    by (rule injD[OF lucas_lehmer_to_real_inj])
  finally have "gen_lucas_lehmer_sequence 4 (p - 2) mod M = 0" using M_gt_6
    by (auto simp: \<phi>_def lucas_lehmer_hom_def S_def lucas_lehmer_ring_mod_def)
  thus "(2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
    by (simp add: M_def mod_eq_0_iff_dvd of_nat_diff)
qed

corollary lucas_lehmer_correct:
  "prime (2 ^ p - 1 :: nat) \<longleftrightarrow>
     prime p \<and> (p = 2 \<or> (2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2))"
proof (intro iffI; (elim conjE)?)
  assume prime: "prime (2 ^ p - 1 :: nat)"
  from prime have "p \<noteq> 0" "p \<noteq> 1"
    by (auto intro!: Nat.gr0I)
  hence "p = 2 \<or> p > 2" by auto
  thus "prime p \<and> (p = 2 \<or> (2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2))"
  proof (elim disjE)
    assume "p > 2"
    with prime interpret mersenne_prime p "2 ^ p - 1"
      by unfold_locales
    from lucas_lehmer_necessary p_prime show ?thesis by auto
  qed auto
next
  assume prime: "prime p" and *: "p = 2 \<or> (2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
  from * consider "p = 2" | "p \<noteq> 2" "(2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
    by auto
  thus "prime (2 ^ p - 1 :: nat)"
  proof cases
    assume "p \<noteq> 2" and dvd: "(2 ^ p - 1) dvd gen_lucas_lehmer_sequence 4 (p - 2)"
    from \<open>prime p\<close> and \<open>p \<noteq> 2\<close> have "p > 2"
      using prime_gt_1_nat[of p] by auto
    with prime have "odd p" by (auto simp: prime_odd_nat)
    with prime dvd show ?thesis      
      by (intro lucas_lehmer_sufficient)
  qed auto
qed

corollary lucas_lehmer_correct':
  "prime (2 ^ p - 1 :: nat) \<longleftrightarrow> prime p \<and> (p = 2 \<or> lucas_lehmer_test p)"
  using lucas_lehmer_correct[of p] prime_gt_1_nat[of p]
  by (auto simp: lucas_lehmer_test_def)


subsection \<open>A first executable version Lucas--Lehmer test\<close>

text \<open>
  The following is an implementation of the Lucas--Lehmer test using modular
  arithmetic on the integers. This is not the most efficient implementation --
  the modular arithmetic can be replaced by much cheaper bitwise operations,
  and we will do that in the next section.
\<close>

primrec gen_lucas_lehmer_sequence' :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "gen_lucas_lehmer_sequence' m a 0 = a"
| "gen_lucas_lehmer_sequence' m a (Suc n) = gen_lucas_lehmer_sequence' m ((a ^ 2 - 2) mod m) n"

lemma gen_lucas_lehmer_sequence'_Suc':
  "gen_lucas_lehmer_sequence' m a (Suc n) = (gen_lucas_lehmer_sequence' m a n ^ 2 - 2) mod m"
  by (induction n arbitrary: a) auto

lemma gen_lucas_lehmer_sequence'_correct:
  assumes "a \<in> {0..<m}"
  shows   "gen_lucas_lehmer_sequence' m a n = gen_lucas_lehmer_sequence a n mod m"
  using assms
proof (induction n)
  case (Suc n)
  have "gen_lucas_lehmer_sequence' m a (Suc n) =
          ((gen_lucas_lehmer_sequence a n mod m)\<^sup>2 - 2) mod m"
    using Suc unfolding gen_lucas_lehmer_sequence'_Suc' by simp
  also have "\<dots> = ((gen_lucas_lehmer_sequence a n)\<^sup>2 - 2) mod m"
    by (intro congD cong_diff cong_pow cong_refl) (auto simp: cong_def)
  finally show ?case by simp
qed auto

lemma lucas_lehmer_test_code_arithmetic [code]:
  "lucas_lehmer_test p = (p > 2 \<and>
     gen_lucas_lehmer_sequence' (2 ^ p - 1) 4 (p - 2) = 0)"
  unfolding lucas_lehmer_test_def
proof (intro conj_cong refl)
  assume p: "p > 2"
  from p have "2 ^ p \<ge> (2 ^ 3 :: int)" by (intro power_increasing) auto
  have "(2 ^ p - 1 dvd gen_lucas_lehmer_sequence 4 (p - 2)) \<longleftrightarrow>
          gen_lucas_lehmer_sequence 4 (p - 2) mod (2 ^ p - 1) = 0"
    by auto
  also have "gen_lucas_lehmer_sequence 4 (p - 2) mod (2 ^ p - 1) =
             gen_lucas_lehmer_sequence' (2 ^ p - 1) 4 (p - 2)"
    using \<open>2 ^ p \<ge> 2 ^ 3\<close>
    by (intro gen_lucas_lehmer_sequence'_correct [symmetric]) auto
  finally show "(2 ^ p - 1 dvd gen_lucas_lehmer_sequence 4 (p - 2)) =
                (gen_lucas_lehmer_sequence' (2 ^ p - 1) 4 (p - 2) = 0)" .
qed

lemma mersenne_prime_iff: "mersenne_prime p \<longleftrightarrow> p > 2 \<and> prime (2 ^ p - 1 :: nat)"
  by (simp add: mersenne_prime_def)

lemma mersenne_prime_code [code]:
  "mersenne_prime p \<longleftrightarrow> prime p \<and> lucas_lehmer_test p"
  unfolding mersenne_prime_iff using lucas_lehmer_correct'[of p]
  by (auto simp: lucas_lehmer_test_def)

end