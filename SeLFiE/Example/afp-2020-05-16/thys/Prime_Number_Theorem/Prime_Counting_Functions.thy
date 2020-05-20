(*
  File:     Prime_Counting_Functions.thy
  Author:   Manuel Eberl (TU München)

  Definitions and basic properties of prime-counting functions like pi, theta, and psi
*)
section \<open>Prime-Counting Functions\<close>
theory Prime_Counting_Functions
  imports Prime_Number_Theorem_Library
begin

text \<open>
  We will now define the basic prime-counting functions \<open>\<pi>\<close>, \<open>\<theta>\<close>, and \<open>\<psi>\<close>. Additionally, we 
  shall define a function M that is related to Mertens' theorems and Newman's proof of the
  Prime Number Theorem. Most of the results in this file are not actually required to prove 
  the Prime Number Theorem, but are still nice to have.
\<close>

subsection \<open>Definitions\<close>

definition prime_sum_upto :: "(nat \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a :: semiring_1" where
  "prime_sum_upto f x = (\<Sum>p | prime p \<and> real p \<le> x. f p)"

lemma prime_sum_upto_altdef1:
  "prime_sum_upto f x = sum_upto (\<lambda>p. ind prime p * f p) x"
  unfolding sum_upto_def prime_sum_upto_def
  by (intro sum.mono_neutral_cong_left finite_subset[OF _ finite_Nats_le_real[of x]])
     (auto dest: prime_gt_1_nat simp: ind_def)

lemma prime_sum_upto_altdef2:
  "prime_sum_upto f x = (\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. f p)"
  unfolding sum_upto_altdef prime_sum_upto_altdef1
  by (intro sum.mono_neutral_cong_right) (auto simp: ind_def dest: prime_gt_1_nat)

lemma prime_sum_upto_altdef3:
  "prime_sum_upto f x = (\<Sum>p\<leftarrow>primes_upto (nat \<lfloor>x\<rfloor>). f p)"
proof -
  have "(\<Sum>p\<leftarrow>primes_upto (nat \<lfloor>x\<rfloor>). f p) = (\<Sum>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. f p)"
    by (subst sum_list_distinct_conv_sum_set) (auto simp: set_primes_upto conj_commute)
  thus ?thesis by (simp add: prime_sum_upto_altdef2)
qed

lemma prime_sum_upto_eqI:
  assumes "a \<le> b" "\<And>k. k \<in> {nat \<lfloor>a\<rfloor><..nat\<lfloor>b\<rfloor>} \<Longrightarrow> \<not>prime k"
  shows   "prime_sum_upto f a = prime_sum_upto f b"
proof -
  have *: "k \<le> nat \<lfloor>a\<rfloor>" if "k \<le> nat \<lfloor>b\<rfloor>" "prime k" for k
    using that assms(2)[of k] by (cases "k \<le> nat \<lfloor>a\<rfloor>") auto
  from assms(1) have "nat \<lfloor>a\<rfloor> \<le> nat \<lfloor>b\<rfloor>" by linarith
  hence "(\<Sum>p | prime p \<and> p \<le> nat \<lfloor>a\<rfloor>. f p) = (\<Sum>p | prime p \<and> p \<le> nat \<lfloor>b\<rfloor>. f p)"
    using assms by (intro sum.mono_neutral_left) (auto dest: *)
  thus ?thesis by (simp add: prime_sum_upto_altdef2)
qed

lemma prime_sum_upto_eqI':
  assumes "a' \<le> nat \<lfloor>a\<rfloor>" "a \<le> b" "nat \<lfloor>b\<rfloor> \<le> b'" "\<And>k. k \<in> {a'<..b'} \<Longrightarrow> \<not>prime k"
  shows   "prime_sum_upto f a = prime_sum_upto f b"
  by (rule prime_sum_upto_eqI) (use assms in auto)

lemmas eval_prime_sum_upto = prime_sum_upto_altdef3[unfolded primes_upto_sieve]

lemma of_nat_prime_sum_upto: "of_nat (prime_sum_upto f x) = prime_sum_upto (\<lambda>p. of_nat (f p)) x"
  by (simp add: prime_sum_upto_def)

lemma prime_sum_upto_mono:
  assumes "\<And>n. n > 0 \<Longrightarrow> f n \<ge> (0::real)" "x \<le> y"
  shows   "prime_sum_upto f x \<le> prime_sum_upto f y"
  using assms unfolding prime_sum_upto_altdef1 sum_upto_altdef
  by (intro sum_mono2) (auto simp: le_nat_iff' le_floor_iff ind_def)

lemma prime_sum_upto_nonneg:
  assumes "\<And>n. n > 0 \<Longrightarrow> f n \<ge> (0 :: real)"
  shows   "prime_sum_upto f x \<ge> 0"
  unfolding prime_sum_upto_altdef1 sum_upto_altdef
  by (intro sum_nonneg) (auto simp: ind_def assms)

lemma prime_sum_upto_eq_0:
  assumes "x < 2"
  shows   "prime_sum_upto f x = 0"
proof -
  from assms have "nat \<lfloor>x\<rfloor> = 0 \<or> nat \<lfloor>x\<rfloor> = 1" by linarith
  thus ?thesis by (auto simp: eval_prime_sum_upto)
qed

lemma measurable_prime_sum_upto [measurable]:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> real"
  assumes [measurable]: "\<And>y. (\<lambda>t. f t y) \<in> M \<rightarrow>\<^sub>M borel"
  assumes [measurable]: "x \<in> M \<rightarrow>\<^sub>M borel"
  shows "(\<lambda>t. prime_sum_upto (f t) (x t)) \<in> M \<rightarrow>\<^sub>M borel"
  unfolding prime_sum_upto_altdef1 by measurable

text \<open>
  The following theorem breaks down a sum over all prime powers no greater than
  fixed bound into a nicer form.
\<close>
lemma sum_upto_primepows:
  fixes f :: "nat \<Rightarrow> 'a :: comm_monoid_add"
  assumes "\<And>n. \<not>primepow n \<Longrightarrow> f n = 0" "\<And>p i. prime p \<Longrightarrow> i > 0 \<Longrightarrow> f (p ^ i) = g p i"
  shows   "sum_upto f x = (\<Sum>(p, i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> x. g p i)"
proof -
  let ?d = aprimedivisor
  have g: "g (?d n) (multiplicity (?d n) n) = f n" if "primepow n" for n using that 
      by (subst assms(2) [symmetric])
         (auto simp: primepow_decompose aprimedivisor_prime_power primepow_gt_Suc_0
               intro!: aprimedivisor_nat multiplicity_aprimedivisor_gt_0_nat)
  have "sum_upto f x = (\<Sum>n | primepow n \<and> real n \<le> x. f n)"
    unfolding sum_upto_def using assms
    by (intro sum.mono_neutral_cong_right) (auto simp: primepow_gt_0_nat)
  also have "\<dots> = (\<Sum>(p, i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> x. g p i)" (is "_ = sum _ ?S")
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(p,i). p ^ i" "\<lambda>n. (?d n, multiplicity (?d n) n)"])
       (auto simp: aprimedivisor_prime_power primepow_decompose primepow_gt_Suc_0 g
             simp del: of_nat_power intro!: aprimedivisor_nat multiplicity_aprimedivisor_gt_0_nat)
  finally show ?thesis .
qed


definition primes_pi    where "primes_pi = prime_sum_upto (\<lambda>p. 1 :: real)"
definition primes_theta where "primes_theta = prime_sum_upto (\<lambda>p. ln (real p))"
definition primes_psi   where "primes_psi = sum_upto (mangoldt :: nat \<Rightarrow> real)"
definition primes_M     where "primes_M = prime_sum_upto (\<lambda>p. ln (real p) / real p)"

text \<open>
  Next, we define some nice optional notation for these functions.
\<close>

bundle prime_counting_notation
begin

notation primes_pi    ("\<pi>")
notation primes_theta ("\<theta>")
notation primes_psi   ("\<psi>")
notation primes_M     ("\<MM>")

end

bundle no_prime_counting_notation
begin

no_notation primes_pi    ("\<pi>")
no_notation primes_theta ("\<theta>")
no_notation primes_psi   ("\<psi>")
no_notation primes_M     ("\<MM>")

end

(*<*)
unbundle prime_counting_notation
(*>*)

lemmas \<pi>_def = primes_pi_def
lemmas \<theta>_def = primes_theta_def
lemmas \<psi>_def = primes_psi_def

lemmas eval_\<pi> = primes_pi_def[unfolded eval_prime_sum_upto]
lemmas eval_\<theta> = primes_theta_def[unfolded eval_prime_sum_upto]
lemmas eval_\<MM> = primes_M_def[unfolded eval_prime_sum_upto]


subsection \<open>Basic properties\<close>

text \<open>
  The proofs in this section are mostly taken from Apostol~\cite{apostol1976analytic}.
\<close>

lemma measurable_\<pi> [measurable]: "\<pi> \<in> borel \<rightarrow>\<^sub>M borel"
  and measurable_\<theta> [measurable]: "\<theta> \<in> borel \<rightarrow>\<^sub>M borel"
  and measurable_\<psi> [measurable]: "\<psi> \<in> borel \<rightarrow>\<^sub>M borel"
  and measurable_primes_M [measurable]: "\<MM> \<in> borel \<rightarrow>\<^sub>M borel"
  unfolding primes_M_def \<pi>_def \<theta>_def \<psi>_def by measurable

lemma \<pi>_eq_0 [simp]: "x < 2 \<Longrightarrow> \<pi> x = 0"
  and \<theta>_eq_0 [simp]: "x < 2 \<Longrightarrow> \<theta> x = 0"
  and primes_M_eq_0 [simp]: "x < 2 \<Longrightarrow> \<MM> x = 0"
  unfolding primes_pi_def primes_theta_def primes_M_def
  by (rule prime_sum_upto_eq_0; simp)+

lemma \<pi>_nat_cancel [simp]: "\<pi> (nat x) = \<pi> x"
  and \<theta>_nat_cancel [simp]: "\<theta> (nat x) = \<theta> x"
  and primes_M_nat_cancel [simp]: "\<MM> (nat x) = \<MM> x"
  and \<psi>_nat_cancel [simp]: "\<psi> (nat x) = \<psi> x"
  and \<pi>_floor_cancel [simp]: "\<pi> (of_int \<lfloor>y\<rfloor>) = \<pi> y"
  and \<theta>_floor_cancel [simp]: "\<theta> (of_int \<lfloor>y\<rfloor>) = \<theta> y"
  and primes_M_floor_cancel [simp]: "\<MM> (of_int \<lfloor>y\<rfloor>) = \<MM> y"
  and \<psi>_floor_cancel [simp]: "\<psi> (of_int \<lfloor>y\<rfloor>) = \<psi> y"
  by (simp_all add: \<pi>_def \<theta>_def \<psi>_def primes_M_def prime_sum_upto_altdef2 sum_upto_altdef)

lemma \<pi>_nonneg [intro]: "\<pi> x \<ge> 0"
  and \<theta>_nonneg [intro]: "\<theta> x \<ge> 0"
  and primes_M_nonneg [intro]: "\<MM> x \<ge> 0"
  unfolding primes_pi_def primes_theta_def primes_M_def
  by (rule prime_sum_upto_nonneg; simp)+

lemma \<pi>_mono [intro]: "x \<le> y \<Longrightarrow> \<pi> x \<le> \<pi> y"
  and \<theta>_mono [intro]: "x \<le> y \<Longrightarrow> \<theta> x \<le> \<theta> y"
  and primes_M_mono [intro]: "x \<le> y \<Longrightarrow> \<MM> x \<le> \<MM> y"
  unfolding primes_pi_def primes_theta_def primes_M_def
  by (rule prime_sum_upto_mono; simp)+

lemma \<pi>_pos_iff: "\<pi> x > 0 \<longleftrightarrow> x \<ge> 2"
proof
  assume x: "x \<ge> 2"
  show "\<pi> x > 0"
    by (rule less_le_trans[OF _ \<pi>_mono[OF x]]) (auto simp: eval_\<pi>)
next
  assume "\<pi> x > 0"
  hence "\<not>(x < 2)" by auto
  thus "x \<ge> 2" by simp
qed

lemma \<pi>_pos: "x \<ge> 2 \<Longrightarrow> \<pi> x > 0"
  by (simp add: \<pi>_pos_iff)

lemma \<psi>_eq_0 [simp]:
  assumes "x < 2"
  shows   "\<psi> x = 0"
proof -
  from assms have "nat \<lfloor>x\<rfloor> \<le> 1" by linarith
  hence "mangoldt n = (0 :: real)" if "n \<in> {0<..nat \<lfloor>x\<rfloor>}" for n
    using that by (auto simp: mangoldt_def dest!: primepow_gt_Suc_0)
  thus ?thesis unfolding \<psi>_def sum_upto_altdef by (intro sum.neutral) auto
qed

lemma \<psi>_nonneg [intro]: "\<psi> x \<ge> 0"
  unfolding \<psi>_def sum_upto_def by (intro sum_nonneg mangoldt_nonneg)

lemma \<psi>_mono: "x \<le> y \<Longrightarrow> \<psi> x \<le> \<psi> y"
  unfolding \<psi>_def sum_upto_def by (intro sum_mono2 mangoldt_nonneg) auto


subsection \<open>The $n$-th prime number\<close>

text \<open>
  Next we define the $n$-th prime number, where counting starts from 0. In traditional
  mathematics, it seems that counting usually starts from 1, but it is more natural to
  start from 0 in HOL and the asymptotics of the function are the same.
\<close>
definition nth_prime :: "nat \<Rightarrow> nat" where
  "nth_prime n = (THE p. prime p \<and> card {q. prime q \<and> q < p} = n)"

lemma finite_primes_less [intro]: "finite {q::nat. prime q \<and> q < p}"
  by (rule finite_subset[of _ "{..<p}"]) auto

lemma nth_prime_unique_aux:
  fixes p p' :: nat
  assumes "prime p"  "card {q. prime q \<and> q < p} = n"
  assumes "prime p'" "card {q. prime q \<and> q < p'} = n"
  shows   "p = p'"
  using assms
proof (induction p p' rule: linorder_wlog)
  case (le p p')
  have "finite {q. prime q \<and> q < p'}" by (rule finite_primes_less)
  moreover from le have "{q. prime q \<and> q < p} \<subseteq> {q. prime q \<and> q < p'}"
    by auto
  moreover from le have "card {q. prime q \<and> q < p} = card {q. prime q \<and> q < p'}"
    by simp
  ultimately have "{q. prime q \<and> q < p} = {q. prime q \<and> q < p'}"
    by (rule card_subset_eq)
  with \<open>prime p\<close> have "\<not>(p < p')" by blast
  with \<open>p \<le> p'\<close> show "p = p'" by auto
qed auto

lemma \<pi>_smallest_prime_beyond:
  "\<pi> (real (smallest_prime_beyond m)) = \<pi> (real (m - 1)) + 1"
proof (cases m)
  case 0
  have "smallest_prime_beyond 0 = 2"
    by (rule smallest_prime_beyond_eq) (auto dest: prime_gt_1_nat)
  with 0 show ?thesis by (simp add: eval_\<pi>)
next
  case (Suc n) 
  define n' where "n' = smallest_prime_beyond (Suc n)"
  have "n < n'"
    using smallest_prime_beyond_le[of "Suc n"] unfolding n'_def by linarith
  have "prime n'" by (simp add: n'_def)
  have "n' \<le> p" if "prime p" "p > n" for p
    using that smallest_prime_beyond_smallest[of p "Suc n"] by (auto simp: n'_def)
  note n' = \<open>n < n'\<close> \<open>prime n'\<close> this

  have "\<pi> (real n') = real (card {p. prime p \<and> p \<le> n'})"
    by (simp add: \<pi>_def prime_sum_upto_def)
  also have "Suc n \<le> n'" unfolding n'_def by (rule smallest_prime_beyond_le)
  hence "{p. prime p \<and> p \<le> n'} = {p. prime p \<and> p \<le> n} \<union> {p. prime p \<and> p \<in> {n<..n'}}"
    by auto
  also have "real (card \<dots>) = \<pi> (real n) + real (card {p. prime p \<and> p \<in> {n<..n'}})"
    by (subst card_Un_disjoint) (auto simp: \<pi>_def prime_sum_upto_def)
  also have "{p. prime p \<and> p \<in> {n<..n'}} = {n'}"
    using n' by (auto intro: antisym)
  finally show ?thesis using Suc by (simp add: n'_def)
qed

lemma \<pi>_inverse_exists: "\<exists>n. \<pi> (real n) = real m"
proof (induction m)
  case 0
  show ?case by (intro exI[of _ 0]) auto
next
  case (Suc m)
  from Suc.IH obtain n where n: "\<pi> (real n) = real m"
    by auto
  hence "\<pi> (real (smallest_prime_beyond (Suc n))) = real (Suc m)"
    by (subst \<pi>_smallest_prime_beyond) auto
  thus ?case by blast
qed

lemma nth_prime_exists: "\<exists>p::nat. prime p \<and> card {q. prime q \<and> q < p} = n"
proof -
  from \<pi>_inverse_exists[of n] obtain m where "\<pi> (real m) = real n" by blast
  hence card: "card {q. prime q \<and> q \<le> m} = n"
    by (auto simp: \<pi>_def prime_sum_upto_def)

  define p where "p = smallest_prime_beyond (Suc m)"
  have "m < p" using smallest_prime_beyond_le[of "Suc m"] unfolding p_def by linarith
  have "prime p" by (simp add: p_def)
  have "p \<le> q" if "prime q" "q > m" for q
    using smallest_prime_beyond_smallest[of q "Suc m"] that by (simp add: p_def)
  note p = \<open>m < p\<close> \<open>prime p\<close> this

  have "{q. prime q \<and> q < p} = {q. prime q \<and> q \<le> m}"
  proof safe
    fix q assume "prime q" "q < p"
    hence "\<not>(q > m)" using p(1,2) p(3)[of q] by auto
    thus "q \<le> m" by simp
  qed (insert p, auto)
  also have "card \<dots> = n" by fact
  finally show ?thesis using \<open>prime p\<close> by blast
qed

lemma nth_prime_exists1: "\<exists>!p::nat. prime p \<and> card {q. prime q \<and> q < p} = n"
  by (intro ex_ex1I nth_prime_exists) (blast intro: nth_prime_unique_aux)

lemma prime_nth_prime [intro]:    "prime (nth_prime n)"
  and card_less_nth_prime [simp]: "card {q. prime q \<and> q < nth_prime n} = n"
  using theI'[OF nth_prime_exists1[of n]] by (simp_all add: nth_prime_def)

lemma card_le_nth_prime [simp]: "card {q. prime q \<and> q \<le> nth_prime n} = Suc n"
proof -
  have "{q. prime q \<and> q \<le> nth_prime n} = insert (nth_prime n) {q. prime q \<and> q < nth_prime n}"
    by auto
  also have "card \<dots> = Suc n" by simp
  finally show ?thesis .
qed

lemma \<pi>_nth_prime [simp]: "\<pi> (real (nth_prime n)) = real n + 1"
  by (simp add: \<pi>_def prime_sum_upto_def)

lemma nth_prime_eqI:
  assumes "prime p" "card {q. prime q \<and> q < p} = n"
  shows   "nth_prime n = p"
  unfolding nth_prime_def
  by (rule the1_equality[OF nth_prime_exists1]) (use assms in auto)

lemma nth_prime_eqI':
  assumes "prime p" "card {q. prime q \<and> q \<le> p} = Suc n"
  shows   "nth_prime n = p"
proof (rule nth_prime_eqI)
  have "{q. prime q \<and> q \<le> p} = insert p {q. prime q \<and> q < p}"
    using assms by auto
  also have "card \<dots> = Suc (card {q. prime q \<and> q < p})"
    by simp
  finally show "card {q. prime q \<and> q < p} = n" using assms by simp
qed (use assms in auto)

lemma nth_prime_eqI'':
  assumes "prime p" "\<pi> (real p) = real n + 1"
  shows   "nth_prime n = p"
proof (rule nth_prime_eqI')
  have "real (card {q. prime q \<and> q \<le> p}) = \<pi> (real p)"
    by (simp add: \<pi>_def prime_sum_upto_def)
  also have "\<dots> = real (Suc n)" by (simp add: assms)
  finally show "card {q. prime q \<and> q \<le> p} = Suc n"
    by (simp only: of_nat_eq_iff)
qed fact+

lemma nth_prime_0 [simp]: "nth_prime 0 = 2"
  by (intro nth_prime_eqI) (auto dest: prime_gt_1_nat)

lemma nth_prime_Suc: "nth_prime (Suc n) = smallest_prime_beyond (Suc (nth_prime n))"
  by (rule nth_prime_eqI'') (simp_all add: \<pi>_smallest_prime_beyond)

lemmas nth_prime_code [code] = nth_prime_0 nth_prime_Suc

lemma strict_mono_nth_prime: "strict_mono nth_prime"
proof (rule strict_monoI_Suc)
  fix n :: nat
  have "Suc (nth_prime n) \<le> smallest_prime_beyond (Suc (nth_prime n))" by simp
  also have "\<dots> = nth_prime (Suc n)" by (simp add: nth_prime_Suc)
  finally show "nth_prime n < nth_prime (Suc n)" by simp
qed

lemma nth_prime_le_iff [simp]: "nth_prime m \<le> nth_prime n \<longleftrightarrow> m \<le> n"
  using strict_mono_less_eq[OF strict_mono_nth_prime] by blast

lemma nth_prime_less_iff [simp]: "nth_prime m < nth_prime n \<longleftrightarrow> m < n"
  using strict_mono_less[OF strict_mono_nth_prime] by blast

lemma nth_prime_eq_iff [simp]: "nth_prime m = nth_prime n \<longleftrightarrow> m = n"
  using strict_mono_eq[OF strict_mono_nth_prime] by blast

lemma nth_prime_ge_2: "nth_prime n \<ge> 2"
  using nth_prime_le_iff[of 0 n] by (simp del: nth_prime_le_iff)

lemma nth_prime_lower_bound: "nth_prime n \<ge> Suc (Suc n)"
proof -
  have "n = card {q. prime q \<and> q < nth_prime n}"
    by simp
  also have "\<dots> \<le> card {2..<nth_prime n}"
    by (intro card_mono) (auto dest: prime_gt_1_nat)
  also have "\<dots> = nth_prime n - 2" by simp
  finally show ?thesis using nth_prime_ge_2[of n] by linarith
qed

lemma nth_prime_at_top: "filterlim nth_prime at_top at_top"
proof (rule filterlim_at_top_mono)
  show "filterlim (\<lambda>n::nat. n + 2) at_top at_top" by real_asymp
qed (auto simp: nth_prime_lower_bound)

lemma \<pi>_at_top: "filterlim \<pi> at_top at_top"
  unfolding filterlim_at_top
proof safe
  fix C :: real
  define x0 where "x0 = real (nth_prime (nat \<lceil>max 0 C\<rceil>))"
  show "eventually (\<lambda>x. \<pi> x \<ge> C) at_top"
    using eventually_ge_at_top
  proof eventually_elim
    fix x assume "x \<ge> x0"
    have "C \<le> real (nat \<lceil>max 0 C\<rceil> + 1)" by linarith
    also have "real (nat \<lceil>max 0 C\<rceil> + 1) = \<pi> x0"
      unfolding x0_def by simp
    also have "\<dots> \<le> \<pi> x" by (rule \<pi>_mono) fact
    finally show "\<pi> x \<ge> C" .
  qed
qed

text\<open>
  An unbounded, strictly increasing sequence $a_n$ partitions $[a_0; \infty)$ into
  segments of the form $[a_n; a_{n+1})$.
\<close>
lemma strict_mono_sequence_partition:
  assumes "strict_mono (f :: nat \<Rightarrow> 'a :: {linorder, no_top})"
  assumes "x \<ge> f 0"
  assumes "filterlim f at_top at_top"
  shows   "\<exists>k. x \<in> {f k..<f (Suc k)}"
proof -
  define k where "k = (LEAST k. f (Suc k) > x)"
  {
    obtain n where "x \<le> f n"
      using assms by (auto simp: filterlim_at_top eventually_at_top_linorder)
    also have "f n < f (Suc n)"
      using assms by (auto simp: strict_mono_Suc_iff)
    finally have "\<exists>n. f (Suc n) > x" by auto
  }
  from LeastI_ex[OF this] have "x < f (Suc k)"
    by (simp add: k_def)
  moreover have "f k \<le> x"
  proof (cases k)
    case (Suc k')
    have "k \<le> k'" if "f (Suc k') > x"
      using that unfolding k_def by (rule Least_le)
    with Suc show "f k \<le> x" by (cases "f k \<le> x") (auto simp: not_le)
  qed (use assms in auto)
  ultimately show ?thesis by auto
qed

lemma nth_prime_partition:
  assumes "x \<ge> 2"
  shows   "\<exists>k. x \<in> {nth_prime k..<nth_prime (Suc k)}"
  using strict_mono_sequence_partition[OF strict_mono_nth_prime, of x] assms nth_prime_at_top
  by simp

lemma nth_prime_partition':
  assumes "x \<ge> 2"
  shows   "\<exists>k. x \<in> {real (nth_prime k)..<real (nth_prime (Suc k))}"
  by (rule strict_mono_sequence_partition)
     (auto simp: strict_mono_Suc_iff assms
           intro!: filterlim_real_sequentially filterlim_compose[OF _ nth_prime_at_top])

lemma between_nth_primes_imp_nonprime:
  assumes "n > nth_prime k" "n < nth_prime (Suc k)"
  shows   "\<not>prime n"
  using assms by (metis Suc_leI not_le nth_prime_Suc smallest_prime_beyond_smallest)

lemma nth_prime_partition'':
  assumes "x \<ge> (2 :: real)"
  shows "x \<in> {real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))..<real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))}"
proof -
  obtain n where n: "x \<in> {nth_prime n..<nth_prime (Suc n)}"
    using nth_prime_partition' assms by auto
  have "\<pi> (nth_prime n) = \<pi> x"
    unfolding \<pi>_def using between_nth_primes_imp_nonprime n
    by (intro prime_sum_upto_eqI) (auto simp: le_nat_iff le_floor_iff)
  hence "real n = \<pi> x - 1"
    by simp
  hence n_eq: "n = nat \<lfloor>\<pi> x\<rfloor> - 1" "Suc n = nat \<lfloor>\<pi> x\<rfloor>"
    by linarith+
  with n show ?thesis 
    by simp
qed


subsection \<open>Relations between different prime-counting functions\<close>

text \<open>
  The \<open>\<psi>\<close> function can be expressed as a sum of \<open>\<theta>\<close>.
\<close>
lemma \<psi>_altdef:
  assumes "x > 0"
  shows   "\<psi> x = sum_upto (\<lambda>m. prime_sum_upto ln (root m x)) (log 2 x)" (is "_ = ?rhs")
proof -
  have finite: "finite {p. prime p \<and> real p \<le> y}" for y
    by (rule finite_subset[of _ "{..nat \<lfloor>y\<rfloor>}"]) (auto simp: le_nat_iff' le_floor_iff)
  define S where "S = (SIGMA i:{i. 0 < i \<and> real i \<le> log 2 x}. {p. prime p \<and> real p \<le> root i x})"
  have "\<psi> x = (\<Sum>(p, i) | prime p \<and> 0 < i \<and> real (p ^ i) \<le> x. ln (real p))"  unfolding \<psi>_def
    by (subst sum_upto_primepows[where g = "\<lambda>p i. ln (real p)"])
       (auto simp: case_prod_unfold mangoldt_non_primepow)
  also have "\<dots> = (\<Sum>(i, p) | prime p \<and> 0 < i \<and> real (p ^ i) \<le> x. ln (real p))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>(x,y). (y,x)" "\<lambda>(x,y). (y,x)"]) auto
  also have "{(i, p). prime p \<and> 0 < i \<and> real (p ^ i) \<le> x} = S"
    unfolding S_def
  proof safe
    fix i p :: nat assume ip: "i > 0" "real i \<le> log 2 x" "prime p" "real p \<le> root i x"
    hence "real (p ^ i) \<le> root i x ^ i" unfolding of_nat_power by (intro power_mono) auto
    with ip assms show "real (p ^ i) \<le> x" by simp
  next
    fix i p assume ip: "prime p" "i > 0" "real (p ^ i) \<le> x"
    from ip have "2 ^ i \<le> p ^ i" by (intro power_mono) (auto dest: prime_gt_1_nat)
    also have "\<dots> \<le> x" using ip by simp
    finally show "real i \<le> log 2 x"
      using assms by (simp add: le_log_iff powr_realpow)
    have "root i (real p ^ i) \<le> root i x" using ip assms
      by (subst real_root_le_iff) auto
    also have "root i (real p ^ i) = real p"
      using assms ip by (subst real_root_pos2) auto
    finally show "real p \<le> root i x" .
  qed
  also have "(\<Sum>(i,p)\<in>S. ln p) = sum_upto (\<lambda>m. prime_sum_upto ln (root m x)) (log 2 x)"
    unfolding sum_upto_def prime_sum_upto_def S_def using finite by (subst sum.Sigma) auto
  finally show ?thesis .
qed

lemma \<psi>_conv_\<theta>_sum: "x > 0 \<Longrightarrow> \<psi> x = sum_upto (\<lambda>m. \<theta> (root m x)) (log 2 x)"
  by (simp add: \<psi>_altdef \<theta>_def)

lemma \<psi>_minus_\<theta>:
  assumes x: "x \<ge> 2"
  shows   "\<psi> x - \<theta> x = (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. \<theta> (root i x))"
proof -
  have finite: "finite {i. 2 \<le> i \<and> real i \<le> log 2 x}"
    by (rule finite_subset[of _ "{2..nat \<lfloor>log 2 x\<rfloor>}"]) (auto simp: le_nat_iff' le_floor_iff)
  have "\<psi> x = (\<Sum>i | 0 < i \<and> real i \<le> log 2 x. \<theta> (root i x))" using x
    by (simp add: \<psi>_conv_\<theta>_sum sum_upto_def)
  also have "{i. 0 < i \<and> real i \<le> log 2 x} = insert 1 {i. 2 \<le> i \<and> real i \<le> log 2 x}" using x
    by (auto simp: le_log_iff)
  also have "(\<Sum>i\<in>\<dots>. \<theta> (root i x)) - \<theta> x =
               (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. \<theta> (root i x))" using finite
    by (subst sum.insert) auto
  finally show ?thesis .
qed

text \<open>
  The following theorems use summation by parts to relate different prime-counting functions to
  one another with an integral as a remainder term.
\<close>
lemma \<theta>_conv_\<pi>_integral:
  assumes "x \<ge> 2"
  shows   "((\<lambda>t. \<pi> t / t) has_integral (\<pi> x * ln x - \<theta> x)) {2..x}"
proof (cases "x = 2")
  case False
  note [intro] = finite_vimage_real_of_nat_greaterThanAtMost
  from False and assms have x: "x > 2" by simp
  have "((\<lambda>t. sum_upto (ind prime) t * (1 / t)) has_integral
          sum_upto (ind prime) x * ln x - sum_upto (ind prime) 2 * ln 2 -
          (\<Sum>n\<in>real -` {2<..x}. ind prime n * ln (real n))) {2..x}" using x
    by (intro partial_summation_strong[where X = "{}"])
       (auto intro!: continuous_intros derivative_eq_intros
             simp flip: has_field_derivative_iff_has_vector_derivative)
  hence "((\<lambda>t. \<pi> t / t) has_integral (\<pi> x * ln x -
           (\<pi> 2 * ln 2 + (\<Sum>n\<in>real -` {2<..x}. ind prime n * ln n)))) {2..x}"
    by (simp add: \<pi>_def prime_sum_upto_altdef1 algebra_simps)
  also have "\<pi> 2 * ln 2 + (\<Sum>n\<in>real -` {2<..x}. ind prime n * ln n) =
               (\<Sum>n\<in>insert 2 (real -` {2<..x}). ind prime n * ln n)"
    by (subst sum.insert) (auto simp: eval_\<pi>)
  also have "\<dots> = \<theta> x" unfolding \<theta>_def prime_sum_upto_def using x
    by (intro sum.mono_neutral_cong_right) (auto simp: ind_def dest: prime_gt_1_nat)
  finally show ?thesis .
qed (auto simp: has_integral_refl eval_\<pi> eval_\<theta>)

lemma \<pi>_conv_\<theta>_integral:
  assumes "x \<ge> 2"
  shows   "((\<lambda>t. \<theta> t / (t * ln t ^ 2)) has_integral (\<pi> x - \<theta> x / ln x)) {2..x}"
proof (cases "x = 2")
  case False
  define b where "b = (\<lambda>p. ind prime p * ln (real p))"
  note [intro] = finite_vimage_real_of_nat_greaterThanAtMost
  from False and assms have x: "x > 2" by simp
  have "((\<lambda>t. -(sum_upto b t * (-1 / (t * (ln t)\<^sup>2)))) has_integral
          -(sum_upto b x * (1 / ln x) - sum_upto b 2 * (1 / ln 2) -
              (\<Sum>n\<in>real -` {2<..x}. b n * (1 / ln (real n))))) {2..x}" using x
    by (intro has_integral_neg partial_summation_strong[where X = "{}"])
       (auto intro!: continuous_intros derivative_eq_intros
             simp flip: has_field_derivative_iff_has_vector_derivative simp add: power2_eq_square)
  also have "sum_upto b = \<theta>"
    by (simp add: \<theta>_def b_def prime_sum_upto_altdef1 fun_eq_iff)
  also have "\<theta> x * (1 / ln x) - \<theta> 2 * (1 / ln 2) - 
                   (\<Sum>n\<in>real -` {2<..x}. b n * (1 / ln (real n))) =
               \<theta> x * (1 / ln x) - (\<Sum>n\<in>insert 2 (real -` {2<..x}). b n * (1 / ln (real n)))"
    by (subst sum.insert) (auto simp: b_def eval_\<theta>)
  also have "(\<Sum>n\<in>insert 2 (real -` {2<..x}). b n * (1 / ln (real n))) = \<pi> x" using x
    unfolding \<pi>_def prime_sum_upto_altdef1 sum_upto_def
  proof (intro sum.mono_neutral_cong_left ballI, goal_cases)
    case (3 p)
    hence "p = 1" by auto
    thus ?case by auto
  qed (auto simp: b_def)
  finally show ?thesis by simp
qed (auto simp: has_integral_refl eval_\<pi> eval_\<theta>)

lemma integrable_weighted_\<theta>:
  assumes "2 \<le> a" "a \<le> x"
  shows   "((\<lambda>t. \<theta> t / (t * ln t ^ 2)) integrable_on {a..x})"
proof (cases "a < x")
  case True
  hence "((\<lambda>t. \<theta> t * (1 / (t * ln t ^ 2))) integrable_on {a..x})" using assms
    unfolding \<theta>_def prime_sum_upto_altdef1
    by (intro partial_summation_integrable_strong[where X = "{}" and f = "\<lambda>x. -1 / ln x"])
       (auto simp flip: has_field_derivative_iff_has_vector_derivative
             intro!: derivative_eq_intros continuous_intros simp: power2_eq_square field_simps)
  thus ?thesis by simp
qed (insert has_integral_refl[of _ a] assms, auto simp: has_integral_iff)

lemma \<theta>_conv_\<MM>_integral:
  assumes "x \<ge> 2"
  shows  "(\<MM> has_integral (\<MM> x * x - \<theta> x)) {2..x}"
proof (cases "x = 2")
  case False
  with assms have x: "x > 2" by simp
  define b :: "nat \<Rightarrow> real" where "b = (\<lambda>p. ind prime p * ln p / p)"
  note [intro] = finite_vimage_real_of_nat_greaterThanAtMost
  have prime_le_2: "p = 2" if "p \<le> 2" "prime p" for p :: nat
    using that by (auto simp: prime_nat_iff)

  have "((\<lambda>t. sum_upto b t * 1) has_integral sum_upto b x * x - sum_upto b 2 * 2 -
          (\<Sum>n\<in>real -` {2<..x}. b n * real n)) {2..x}" using x
    by (intro partial_summation_strong[of "{}"])
       (auto simp flip: has_field_derivative_iff_has_vector_derivative
             intro!: derivative_eq_intros continuous_intros)
  also have "sum_upto b = \<MM>"
    by (simp add: fun_eq_iff primes_M_def b_def prime_sum_upto_altdef1)
  also have "\<MM> x * x - \<MM> 2 * 2 - (\<Sum>n\<in>real -` {2<..x}. b n * real n) =
               \<MM> x * x - (\<Sum>n\<in>insert 2 (real -` {2<..x}). b n * real n)"
    by (subst sum.insert) (auto simp: eval_\<MM> b_def)
  also have "(\<Sum>n\<in>insert 2 (real -` {2<..x}). b n * real n) = \<theta> x"
    unfolding \<theta>_def prime_sum_upto_def using x
    by (intro sum.mono_neutral_cong_right) (auto simp: b_def ind_def not_less prime_le_2)
  finally show ?thesis by simp
qed (auto simp: eval_\<theta> eval_\<MM>)

lemma \<MM>_conv_\<theta>_integral:
  assumes "x \<ge> 2"
  shows  "((\<lambda>t. \<theta> t / t\<^sup>2) has_integral (\<MM> x - \<theta> x / x)) {2..x}"
proof (cases "x = 2")
  case False
  with assms have x: "x > 2" by simp
  define b :: "nat \<Rightarrow> real" where "b = (\<lambda>p. ind prime p * ln p)"
  note [intro] = finite_vimage_real_of_nat_greaterThanAtMost
  have prime_le_2: "p = 2" if "p \<le> 2" "prime p" for p :: nat
    using that by (auto simp: prime_nat_iff)

  have "((\<lambda>t. sum_upto b t * (1 / t^2)) has_integral
          sum_upto b x * (-1 / x) - sum_upto b 2 * (-1 / 2) -
          (\<Sum>n\<in>real -` {2<..x}. b n * (-1 / real n))) {2..x}" using x
    by (intro partial_summation_strong[of "{}"])
       (auto simp flip: has_field_derivative_iff_has_vector_derivative simp: power2_eq_square
             intro!: derivative_eq_intros continuous_intros)
  also have "sum_upto b = \<theta>"
    by (simp add: fun_eq_iff \<theta>_def b_def prime_sum_upto_altdef1)
  also have "\<theta> x * (-1 / x) - \<theta> 2 * (-1 / 2) - (\<Sum>n\<in>real -` {2<..x}. b n * (-1 / real n)) =
               -(\<theta> x / x - (\<Sum>n\<in>insert 2 (real -` {2<..x}). b n / real n))"
    by (subst sum.insert) (auto simp: eval_\<theta> b_def sum_negf)
  also have "(\<Sum>n\<in>insert 2 (real -` {2<..x}). b n / real n) = \<MM> x"
    unfolding primes_M_def prime_sum_upto_def using x
    by (intro sum.mono_neutral_cong_right) (auto simp: b_def ind_def not_less prime_le_2)
  finally show ?thesis by simp
qed (auto simp: eval_\<theta> eval_\<MM>)

lemma integrable_primes_M: "\<MM> integrable_on {x..y}" if "2 \<le> x" for x y :: real
proof -
  have "(\<lambda>x. \<MM> x * 1) integrable_on {x..y}" if "2 \<le> x" "x < y" for x y :: real
    unfolding primes_M_def prime_sum_upto_altdef1 using that
    by (intro partial_summation_integrable_strong[where X = "{}" and f = "\<lambda>x. x"])
       (auto simp flip: has_field_derivative_iff_has_vector_derivative
             intro!: derivative_eq_intros continuous_intros)
  thus ?thesis using that has_integral_refl(2)[of \<MM> x] by (cases x y rule: linorder_cases) auto
qed


subsection \<open>Bounds\<close>

lemma \<theta>_upper_bound_coarse:
  assumes "x \<ge> 1"
  shows   "\<theta> x \<le> x * ln x"
proof -
  have "\<theta> x \<le> sum_upto (\<lambda>_. ln x) x" unfolding \<theta>_def prime_sum_upto_altdef1 sum_upto_def
    by (intro sum_mono) (auto simp: ind_def)
  also have "\<dots> \<le> real_of_int \<lfloor>x\<rfloor> * ln x" using assms
    by (simp add: sum_upto_altdef)
  also have "\<dots> \<le> x * ln x" using assms by (intro mult_right_mono) auto
  finally show ?thesis .
qed

lemma \<theta>_le_\<psi>: "\<theta> x \<le> \<psi> x"
proof (cases "x \<ge> 2")
  case False
  hence "nat \<lfloor>x\<rfloor> = 0 \<or> nat \<lfloor>x\<rfloor> = 1" by linarith
  thus ?thesis by (auto simp: eval_\<theta>)
next
  case True
  hence "\<psi> x - \<theta> x = (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. \<theta> (root i x))"
    by (rule \<psi>_minus_\<theta>)
  also have "\<dots> \<ge> 0" by (intro sum_nonneg) auto
  finally show ?thesis by simp
qed

lemma \<pi>_upper_bound_coarse:
  assumes "x \<ge> 0"
  shows   "\<pi> x \<le> x / 3 + 2"
proof -
  have "{p. prime p \<and> p \<le> nat \<lfloor>x\<rfloor>} \<subseteq> {2, 3} \<union> {p. p \<noteq> 1 \<and> odd p \<and> \<not>3 dvd p \<and> p \<le> nat \<lfloor>x\<rfloor>}"
    using primes_dvd_imp_eq[of "2 :: nat"] primes_dvd_imp_eq[of "3 :: nat"] by auto
  also have "\<dots> \<subseteq> {2, 3} \<union> ((\<lambda>k. 6*k+1) ` {0<..<nat \<lfloor>(x+5)/6\<rfloor>} \<union> (\<lambda>k. 6*k+5) ` {..<nat \<lfloor>(x+1)/6\<rfloor>})"
    (is "_ \<union> ?lhs \<subseteq> _ \<union> ?rhs")
  proof (intro Un_mono subsetI)
    fix p :: nat assume "p \<in> ?lhs"
    hence p: "p \<noteq> 1" "odd p" "\<not>3 dvd p" "p \<le> nat \<lfloor>x\<rfloor>" by auto
    from p (1-3) have "(\<exists>k. k > 0 \<and> p = 6 * k + 1 \<or> p = 6 * k + 5)" by presburger
    then obtain k where "k > 0 \<and> p = 6 * k + 1 \<or> p = 6 * k + 5" by blast
    hence "p = 6 * k + 1 \<and> k > 0 \<and> k < nat \<lfloor>(x+5)/6\<rfloor> \<or> p = 6*k+5 \<and> k < nat \<lfloor>(x+1)/6\<rfloor>"
      unfolding add_divide_distrib using p(4) by linarith
    thus "p \<in> ?rhs" by auto
  qed
  finally have subset: "{p. prime p \<and> p \<le> nat \<lfloor>x\<rfloor>} \<subseteq> \<dots>" (is "_ \<subseteq> ?A") .

  have "\<pi> x = real (card {p. prime p \<and> p \<le> nat \<lfloor>x\<rfloor>})"
    by (simp add: \<pi>_def prime_sum_upto_altdef2)
  also have "card {p. prime p \<and> p \<le> nat \<lfloor>x\<rfloor>} \<le> card ?A"
    by (intro card_mono subset) auto
  also have "\<dots> \<le> 2 + (nat \<lfloor>(x+5)/6\<rfloor> - 1 + nat \<lfloor>(x+1)/6\<rfloor>)"
    by (intro order.trans[OF card_Un_le] add_mono order.trans[OF card_image_le]) auto
  also have "\<dots> \<le> x / 3 + 2"
    using assms unfolding add_divide_distrib by (cases "x \<ge> 1", linarith, simp)
  finally show ?thesis by simp
qed

lemma le_numeral_iff: "m \<le> numeral n \<longleftrightarrow> m = numeral n \<or> m \<le> pred_numeral n"
  using numeral_eq_Suc by presburger

text \<open>
  The following nice proof for the upper bound $\theta(x) \leq \ln 4 \cdot x$ is taken
  from Otto Forster's lecture notes on Analytic Number Theory~\cite{forsteranalytic}.
\<close>
lemma prod_primes_upto_less:
  defines "F \<equiv> (\<lambda>n. (\<Prod>{p::nat. prime p \<and> p \<le> n}))"
  shows   "n > 0 \<Longrightarrow> F n < 4 ^ n"
proof (induction n rule: less_induct)
  case (less n)
  have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> even n \<and> n \<ge> 4 \<or> odd n \<and> n \<ge> 4"
    by presburger
  then consider "n = 0" | "n = 1" | "n = 2" | "n = 3" | "even n" "n \<ge> 4" | "odd n" "n \<ge> 4"
    by metis
  thus ?case
  proof cases
    assume [simp]: "n = 1"
    have *: "{p. prime p \<and> p \<le> Suc 0} = {}" by (auto dest: prime_gt_1_nat)
    show ?thesis by (simp add: F_def *)
  next
    assume [simp]: "n = 2"
    have *: "{p. prime p \<and> p \<le> 2} = {2 :: nat}"
      by (auto simp: le_numeral_iff dest: prime_gt_1_nat)
    thus ?thesis by (simp add: F_def *)
  next
    assume [simp]: "n = 3"
    have *: "{p. prime p \<and> p \<le> 3} = {2, 3 :: nat}"
      by (auto simp: le_numeral_iff dest: prime_gt_1_nat)
    thus ?thesis by (simp add: F_def *)
  next
    assume n: "even n" "n \<ge> 4"
    from n have "F (n - 1) < 4 ^ (n - 1)" by (intro less.IH) auto
    also have "prime p \<and> p \<le> n \<longleftrightarrow> prime p \<and> p \<le> n - 1" for p
      using n prime_odd_nat[of n] by (cases "p = n") auto
    hence "F (n - 1) = F n" by (simp add: F_def)
    also have "4 ^ (n - 1) \<le> (4 ^ n :: nat)" by (intro power_increasing) auto
    finally show ?case .
  next
    assume n: "odd n" "n \<ge> 4"
    then obtain k where k_eq: "n = Suc (2 * k)" by (auto elim: oddE)
    from n have k: "k \<ge> 2" unfolding k_eq by presburger
    have prime_dvd: "p dvd (n choose k)" if p: "prime p" "p \<in> {k+1<..n}" for p
    proof -
      from p k n have "p dvd pochhammer (k + 2) k"
        unfolding pochhammer_prod
        by (subst prime_dvd_prod_iff)
           (auto intro!: bexI[of _ "p - k - 2"] simp: k_eq numeral_2_eq_2 Suc_diff_Suc)
      also have "pochhammer (real (k + 2)) k = real ((n choose k) * fact k)"
        by (simp add: binomial_gbinomial gbinomial_pochhammer' k_eq field_simps)
      hence "pochhammer (k + 2) k = (n choose k) * fact k"
        unfolding pochhammer_of_nat of_nat_eq_iff .
      finally show "p dvd (n choose k)" using p
        by (auto simp: prime_dvd_fact_iff prime_dvd_mult_nat)
    qed

    have "\<Prod>{p. prime p \<and> p \<in> {k+1<..n}} dvd (n choose k)"
    proof (rule multiplicity_le_imp_dvd, goal_cases)
      case (2 p)
      thus ?case
      proof (cases "p \<in> {k+1<..n}")
        case False
        hence "multiplicity p (\<Prod>{p. prime p \<and> p \<in> {k+1<..n}}) = 0" using 2
          by (subst prime_elem_multiplicity_prod_distrib) (auto simp: prime_multiplicity_other)
        thus ?thesis by auto
      next
        case True
        hence "multiplicity p (\<Prod>{p. prime p \<and> p \<in> {k+1<..n}}) =
                 sum (multiplicity p) {p. prime p \<and> Suc k < p \<and> p \<le> n}" using 2
          by (subst prime_elem_multiplicity_prod_distrib) auto
        also have "\<dots> = sum (multiplicity p) {p}" using True 2
        proof (intro sum.mono_neutral_right ballI)
          fix q :: nat assume "q \<in> {p. prime p \<and> Suc k < p \<and> p \<le> n} - {p}"
          thus "multiplicity p q = 0" using 2
            by (cases "p = q") (auto simp: prime_multiplicity_other)
        qed auto
        also have "\<dots> = 1" using 2 by simp
        also have "1 \<le> multiplicity p (n choose k)"
          using prime_dvd[of p] 2 True by (intro multiplicity_geI) auto
        finally show ?thesis .
      qed
    qed auto
    hence "\<Prod>{p. prime p \<and> p \<in> {k+1<..n}} \<le> (n choose k)"
      by (intro dvd_imp_le) (auto simp: k_eq)
    also have "\<dots> = 1 / 2 * (\<Sum>i\<in>{k, Suc k}. n choose i)"
      using central_binomial_odd[of n] by (simp add: k_eq)
    also have "(\<Sum>i\<in>{k, Suc k}. n choose i) < (\<Sum>i\<in>{0, k, Suc k}. n choose i)"
      using k by simp
    also have "\<dots> \<le> (\<Sum>i\<le>n. n choose i)"
      by (intro sum_mono2) (auto simp: k_eq)
    also have "\<dots> = (1 + 1) ^ n"
      using binomial[of 1 1 n] by simp
    also have "1 / 2 * \<dots> = real (4 ^ k)"
      by (simp add: k_eq power_mult)
    finally have less: "(\<Prod>{p. prime p \<and> p \<in> {k + 1<..n}}) < 4 ^ k"
      unfolding of_nat_less_iff by simp

    have "F n = F (Suc k) * (\<Prod>{p. prime p \<and> p \<in> {k+1<..n}})" unfolding F_def
      by (subst prod.union_disjoint [symmetric]) (auto intro!: prod.cong simp: k_eq)
    also have "\<dots> < 4 ^ Suc k * 4 ^ k" using n
      by (intro mult_strict_mono less less.IH) (auto simp: k_eq)
    also have "\<dots> = 4 ^ (Suc k + k)"
      by (simp add: power_add)
    also have "Suc k + k = n" by (simp add: k_eq)
    finally show ?case .
  qed (insert less.prems, auto)
qed

lemma \<theta>_upper_bound:
  assumes x: "x \<ge> 1"
  shows   "\<theta> x < ln 4 * x"
proof -
  have "4 powr (\<theta> x / ln 4) = (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. 4 powr (log 4 (real p)))"
    by (simp add: \<theta>_def powr_sum prime_sum_upto_altdef2 sum_divide_distrib log_def)
  also have "\<dots> = (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. real p)"
    by (intro prod.cong) (auto dest: prime_gt_1_nat)
  also have "\<dots> = real (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. p)"
    by simp
  also have "(\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. p) < 4 ^ nat \<lfloor>x\<rfloor>"
    using x by (intro prod_primes_upto_less) auto
  also have "\<dots> = 4 powr real (nat \<lfloor>x\<rfloor>)"
    using x by (subst powr_realpow) auto
  also have "\<dots> \<le> 4 powr x"
    using x by (intro powr_mono) auto
  finally have "4 powr (\<theta> x / ln 4) < 4 powr x"
    by simp
  thus "\<theta> x < ln 4 * x"
    by (subst (asm) powr_less_cancel_iff) (auto simp: field_simps)
qed

lemma \<theta>_bigo: "\<theta> \<in> O(\<lambda>x. x)"
  by (intro le_imp_bigo_real[of "ln 4"] eventually_mono[OF eventually_ge_at_top[of 1]]
            less_imp_le[OF \<theta>_upper_bound]) auto

lemma \<psi>_minus_\<theta>_bound:
  assumes x: "x \<ge> 2"
  shows   "\<psi> x - \<theta> x \<le> 2 * ln x * sqrt x"
proof -
  have "\<psi> x - \<theta> x = (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. \<theta> (root i x))" using x
    by (rule \<psi>_minus_\<theta>)
  also have "\<dots> \<le> (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. ln 4 * root i x)"
    using x by (intro sum_mono less_imp_le[OF \<theta>_upper_bound]) auto
  also have "\<dots> \<le> (\<Sum>i | 2 \<le> i \<and> real i \<le> log 2 x. ln 4 * root 2 x)" using x
    by (intro sum_mono mult_mono) (auto simp: le_log_iff powr_realpow intro!: real_root_decreasing)
  also have "\<dots> = card {i. 2 \<le> i \<and> real i \<le> log 2 x} * ln 4 * sqrt x"
    by (simp add: sqrt_def)
  also have "{i. 2 \<le> i \<and> real i \<le> log 2 x} = {2..nat \<lfloor>log 2 x\<rfloor>}"
    by (auto simp: le_nat_iff' le_floor_iff)
  also have "log 2 x \<ge> 1" using x by (simp add: le_log_iff)
  hence "real (nat \<lfloor>log 2 x\<rfloor> - 1) \<le> log 2 x" using x by linarith
  hence "card {2..nat \<lfloor>log 2 x\<rfloor>} \<le> log 2 x" by simp
  also have "ln (2 * 2 :: real) = 2 * ln 2" by (subst ln_mult) auto
  hence "log 2 x * ln 4 * sqrt x = 2 * ln x * sqrt x" using x
    by (simp add: ln_sqrt log_def power2_eq_square field_simps)
  finally show ?thesis using x by (simp add: mult_right_mono)
qed

lemma \<psi>_minus_\<theta>_bigo: "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)"
proof (intro bigoI[of _ "2"] eventually_mono[OF eventually_ge_at_top[of 2]])
  fix x :: real assume "x \<ge> 2"
  thus "norm (\<psi> x - \<theta> x) \<le> 2 * norm (ln x * sqrt x)"
    using \<psi>_minus_\<theta>_bound[of x] \<theta>_le_\<psi>[of x] by simp
qed

lemma \<psi>_bigo: "\<psi> \<in> O(\<lambda>x. x)"
proof -
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)"
    by (rule \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x. ln x * sqrt x) \<in> O(\<lambda>x. x)"
    by real_asymp
  finally have "(\<lambda>x. \<psi> x - \<theta> x + \<theta> x) \<in> O(\<lambda>x. x)"
    by (rule sum_in_bigo) (fact \<theta>_bigo)
  thus ?thesis by simp
qed

text \<open>
  We shall now attempt to get some more concrete bounds on the difference
  between $\pi(x)$ and $\theta(x)/\ln x$ These will be essential in showing the Prime
  Number Theorem later.

  We first need some bounds on the integral
  \[\int\nolimits_2^x \frac{1}{\ln^2 t}\,\mathrm{d}t\]
  in order to bound the contribution of the remainder term. This integral actually has an
  antiderivative in terms of the logarithmic integral $\textrm{li}(x)$, but since we do not have a
  formalisation of it in Isabelle, we will instead use the following ad-hoc bound given by Apostol:
\<close>
lemma integral_one_over_log_squared_bound:
  assumes x: "x \<ge> 4"
  shows   "integral {2..x} (\<lambda>t. 1 / ln t ^ 2) \<le> sqrt x / ln 2 ^ 2 + 4 * x / ln x ^ 2"
proof -
  from x have "x * 1 \<le> x ^ 2" unfolding power2_eq_square by (intro mult_left_mono) auto
  with x have x': "2 \<le> sqrt x" "sqrt x \<le> x"
    by (auto simp: real_sqrt_le_iff' intro!: real_le_rsqrt)
  have "integral {2..x} (\<lambda>t. 1 / ln t ^ 2) =
          integral {2..sqrt x} (\<lambda>t. 1 / ln t ^ 2) + integral {sqrt x..x} (\<lambda>t. 1 / ln t ^ 2)"
    (is "_ = ?I1 + ?I2") using x x'
    by (intro Henstock_Kurzweil_Integration.integral_combine [symmetric] integrable_continuous_real)
       (auto intro!: continuous_intros)
  also have "?I1 \<le> integral {2..sqrt x} (\<lambda>_. 1 / ln 2 ^ 2)" using x
    by (intro integral_le integrable_continuous_real divide_left_mono
              power_mono continuous_intros) auto
  also have "\<dots> \<le> sqrt x / ln 2 ^ 2" using x' by (simp add: field_simps)
  also have "?I2 \<le> integral {sqrt x..x} (\<lambda>t. 1 / ln (sqrt x) ^ 2)" using x'
    by (intro integral_le integrable_continuous_real divide_left_mono
              power_mono continuous_intros) auto
  also have "\<dots> \<le> 4 * x / ln x ^ 2" using x' by (simp add: ln_sqrt field_simps)
  finally show ?thesis by simp
qed

lemma integral_one_over_log_squared_bigo:
  "(\<lambda>x::real. integral {2..x} (\<lambda>t. 1 / ln t ^ 2)) \<in> O(\<lambda>x. x / ln x ^ 2)"
proof -
  define ub where "ub = (\<lambda>x::real. sqrt x / ln 2 ^ 2 + 4 * x / ln x ^ 2)"
  have "eventually (\<lambda>x. \<bar>integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)\<bar> \<le> \<bar>ub x\<bar>) at_top"
    using eventually_ge_at_top[of 4]
  proof eventually_elim
    case (elim x)
    hence "\<bar>integral {2..x} (\<lambda>t. 1 / ln t ^ 2)\<bar> = integral {2..x} (\<lambda>t. 1 / ln t ^ 2)"
      by (intro abs_of_nonneg integral_nonneg integrable_continuous_real continuous_intros) auto
    also have "\<dots> \<le> \<bar>ub x\<bar>"
      using integral_one_over_log_squared_bound[of x] elim by (simp add: ub_def)
    finally show ?case .
  qed
  hence "(\<lambda>x. integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)) \<in> O(ub)"
    by (intro landau_o.bigI[of 1]) auto
  also have "ub \<in> O(\<lambda>x. x / ln x ^ 2)" unfolding ub_def by real_asymp
  finally show ?thesis .
qed

lemma \<pi>_\<theta>_bound:
  assumes "x \<ge> (4 :: real)"
  defines "ub \<equiv> 2 / ln 2 * sqrt x + 8 * ln 2 * x / ln x ^ 2"
  shows   "\<pi> x - \<theta> x / ln x \<in> {0..ub}"
proof -
  define r where "r = (\<lambda>x. integral {2..x} (\<lambda>t. \<theta> t / (t * ln t ^ 2)))"
  have integrable: "(\<lambda>t. c / ln t ^ 2) integrable_on {2..x}" for c
    by (intro integrable_continuous_real continuous_intros) auto

  have "r x \<le> integral {2..x} (\<lambda>t. ln 4 / ln t ^ 2)" unfolding r_def
    using integrable_weighted_\<theta>[of 2 x] integrable[of "ln 4"] assms less_imp_le[OF \<theta>_upper_bound]
    by (intro integral_le divide_right_mono) (auto simp: field_simps)
  also have "\<dots> = ln 4 * integral {2..x} (\<lambda>t. 1 / ln t ^ 2)"
    using integrable[of 1] by (subst integral_mult) auto
  also have "\<dots> \<le> ln 4 * (sqrt x / ln 2 ^ 2 + 4 * x / ln x ^ 2)"
    using assms by (intro mult_left_mono integral_one_over_log_squared_bound) auto
  also have "ln (4 :: real) = 2 * ln 2"
    using ln_realpow[of 2 2] by simp
  also have "\<dots> * (sqrt x / ln 2 ^ 2 + 4 * x / ln x ^ 2) = ub"
    using assms by (simp add: field_simps power2_eq_square ub_def)
  finally have "r x \<le> \<dots>" .
  moreover have "r x \<ge> 0" unfolding r_def using assms
    by (intro integral_nonneg integrable_weighted_\<theta> divide_nonneg_pos) auto
  ultimately have "r x \<in> {0..ub}" by auto
  with \<pi>_conv_\<theta>_integral[of x] assms(1) show ?thesis
    by (simp add: r_def has_integral_iff)
qed

text \<open>
  The following statement already indicates that the asymptotics of \<open>\<pi>\<close> and \<open>\<theta>\<close>
  are very closely related, since through it, $\pi(x) \sim x / \ln x$ and $\theta(x) \sim x$
  imply each other.
\<close>
lemma \<pi>_\<theta>_bigo: "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x ^ 2)"
proof -
  define ub where "ub = (\<lambda>x. 2 / ln 2 * sqrt x + 8 * ln 2 * x / ln x ^ 2)"
  have "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(ub)"
  proof (intro le_imp_bigo_real[of 1] eventually_mono[OF eventually_ge_at_top])
    fix x :: real assume "x \<ge> 4"
    from \<pi>_\<theta>_bound[OF this] show "\<pi> x - \<theta> x / ln x \<ge> 0" and "\<pi> x - \<theta> x / ln x \<le> 1 * ub x"
      by (simp_all add: ub_def)
  qed auto
  also have "ub \<in> O(\<lambda>x. x / ln x ^ 2)"
    unfolding ub_def by real_asymp
  finally show ?thesis .
qed

text \<open>
  As a foreshadowing of the Prime Number Theorem, we can already show
  the following upper bound on $\pi(x)$:
\<close>
lemma \<pi>_upper_bound:
  assumes "x \<ge> (4 :: real)"
  shows   "\<pi> x < ln 4 * x / ln x  +  8 * ln 2 * x / ln x ^ 2  +  2 / ln 2 * sqrt x"
proof -
  define ub where "ub = 2 / ln 2 * sqrt x + 8 * ln 2 * x / ln x ^ 2"
  have "\<pi> x \<le> \<theta> x / ln x + ub"
    using \<pi>_\<theta>_bound[of x] assms unfolding ub_def by simp
  also from assms have "\<theta> x / ln x < ln 4 * x / ln x"
    by (intro \<theta>_upper_bound divide_strict_right_mono) auto
  finally show ?thesis
    using assms by (simp add: algebra_simps ub_def)
qed

lemma \<pi>_bigo: "\<pi> \<in> O(\<lambda>x. x / ln x)"
proof -
  have "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x ^ 2)"
    by (fact \<pi>_\<theta>_bigo)
  also have "(\<lambda>x::real. x / ln x ^ 2) \<in> O(\<lambda>x. x / ln x)"
    by real_asymp
  finally have "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x)" .
  moreover have "eventually (\<lambda>x::real. ln x > 0) at_top" by real_asymp
  hence "eventually (\<lambda>x::real. ln x \<noteq> 0) at_top" by eventually_elim auto
  hence "(\<lambda>x. \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x)"
    using \<theta>_bigo by (intro landau_o.big.divide_right)
  ultimately have "(\<lambda>x. \<pi> x - \<theta> x / ln x + \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x)"
    by (rule sum_in_bigo)
  thus ?thesis by simp
qed


subsection \<open>Equivalence of various forms of the Prime Number Theorem\<close>

text \<open>
  In this section, we show that the following forms of the Prime Number Theorem are
  all equivalent:
    \<^enum> $\pi(x) \sim x / \ln x$
    \<^enum> $\pi(x) \ln \pi(x) \sim x$
    \<^enum> $p_n \sim n \ln n$
    \<^enum> $\vartheta(x) \sim x$
    \<^enum> $\psi(x) \sim x$

  We show the following implication chains:
    \<^item> \<open>(1) \<rightarrow> (2) \<rightarrow> (3) \<rightarrow> (2) \<rightarrow> (1)\<close>
    \<^item> \<open>(1) \<rightarrow> (4) \<rightarrow> (1)\<close>
    \<^item> \<open>(4) \<rightarrow> (5) \<rightarrow> (4)\<close>

  All of these proofs are taken from Apostol's book.
\<close>

lemma PNT1_imp_PNT1':
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
proof -
  (* TODO: Tedious Landau sum reasoning *)
  from assms have "((\<lambda>x. \<pi> x / (x / ln x)) \<longlongrightarrow> 1) at_top"
    by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto
  hence "((\<lambda>x. ln (\<pi> x / (x / ln x))) \<longlongrightarrow> ln 1) at_top"
    by (rule tendsto_ln) auto
  also have "?this \<longleftrightarrow> ((\<lambda>x. ln (\<pi> x) - ln x + ln (ln x)) \<longlongrightarrow> 0) at_top"
    by (intro filterlim_cong eventually_mono[OF eventually_gt_at_top[of 2]])
       (auto simp: ln_div field_simps ln_mult \<pi>_pos)
  finally have "(\<lambda>x. ln (\<pi> x) - ln x + ln (ln x)) \<in> o(\<lambda>_. 1)"
    by (intro smalloI_tendsto) auto
  also have "(\<lambda>_::real. 1 :: real) \<in> o(\<lambda>x. ln x)"
    by real_asymp
  finally have "(\<lambda>x. ln (\<pi> x) - ln x + ln (ln x) - ln (ln x)) \<in> o(\<lambda>x. ln x)"
    by (rule sum_in_smallo) real_asymp+
  thus *: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] ln"
    by (simp add: asymp_equiv_altdef)
qed

lemma PNT1_imp_PNT2:
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
proof -
  have "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x / ln x * ln x)"
    by (intro asymp_equiv_intros assms PNT1_imp_PNT1')
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x)"
    by (intro asymp_equiv_refl_ev eventually_mono[OF eventually_gt_at_top[of 1]])
       (auto simp: field_simps)
  finally show "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
    by simp
qed

lemma PNT2_imp_PNT3:
  assumes "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  shows   "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)"
proof -
  have "(\<lambda>n. nth_prime n) \<sim>[at_top] (\<lambda>n. \<pi> (nth_prime n) * ln (\<pi> (nth_prime n)))"
    using assms
    by (rule asymp_equiv_symI [OF asymp_equiv_compose'])
       (auto intro!: filterlim_compose[OF filterlim_real_sequentially nth_prime_at_top])
  also have "\<dots> = (\<lambda>n. real (Suc n) * ln (real (Suc n)))"
    by (simp add: add_ac)
  also have "\<dots> \<sim>[at_top] (\<lambda>n. real n * ln (real n))"
    by real_asymp
  finally show "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)" .
qed

lemma PNT3_imp_PNT2:
  assumes "nth_prime \<sim>[at_top] (\<lambda>n. n * ln n)"
  shows   "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
proof (rule asymp_equiv_symI, rule asymp_equiv_sandwich_real)
  show "eventually (\<lambda>x. x \<in> {real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))..real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))})
          at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim x)
    with nth_prime_partition''[of x] show ?case by auto
  qed
next
  have "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))) \<sim>[at_top]
           (\<lambda>x. real (nat \<lfloor>\<pi> x\<rfloor> - 1) * ln (real (nat \<lfloor>\<pi> x\<rfloor> - 1)))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top], rule asymp_equiv_compose'[OF assms]) real_asymp
  also have "\<dots> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top]) real_asymp
  finally show "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor> - 1))) \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))" .
next
  have "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))) \<sim>[at_top]
           (\<lambda>x. real (nat \<lfloor>\<pi> x\<rfloor>) * ln (real (nat \<lfloor>\<pi> x\<rfloor>)))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top], rule asymp_equiv_compose'[OF assms]) real_asymp
  also have "\<dots> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))"
    by (rule asymp_equiv_compose'[OF _ \<pi>_at_top]) real_asymp
  finally show "(\<lambda>x. real (nth_prime (nat \<lfloor>\<pi> x\<rfloor>))) \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x))" .
qed

lemma PNT2_imp_PNT1:
  assumes "(\<lambda>x. \<pi> x * ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x)"
  shows   "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. ln x)"
    and   "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
   have ev: "eventually (\<lambda>x. \<pi> x > 0) at_top"
            "eventually (\<lambda>x. ln (\<pi> x) > 0) at_top"
            "eventually (\<lambda>x. ln (ln (\<pi> x)) > 0) at_top"
    by (rule eventually_compose_filterlim[OF _ \<pi>_at_top], real_asymp)+

  let ?f = "\<lambda>x. 1 + ln (ln (\<pi> x)) / ln (\<pi> x) - ln x / ln (\<pi> x)"
  have "((\<lambda>x. ln (\<pi> x) * ?f x) \<longlongrightarrow> ln 1) at_top"
  proof (rule Lim_transform_eventually)
    from assms have "((\<lambda>x. \<pi> x * ln (\<pi> x) / x) \<longlongrightarrow> 1) at_top"
      by (rule asymp_equivD_strong[OF _ eventually_mono[OF eventually_gt_at_top[of 1]]]) auto
    then show "((\<lambda>x. ln (\<pi> x * ln (\<pi> x) / x)) \<longlongrightarrow> ln 1) at_top"
      by (rule tendsto_ln) auto
    show "\<forall>\<^sub>F x in at_top. ln (\<pi> x * ln (\<pi> x) / x) = ln (\<pi> x) * ?f x"
      using eventually_gt_at_top[of 0] ev
      by eventually_elim (simp add: field_simps ln_mult ln_div)
  qed
  moreover have "((\<lambda>x. 1 / ln (\<pi> x)) \<longlongrightarrow> 0) at_top"
    by (rule filterlim_compose[OF _ \<pi>_at_top]) real_asymp
  ultimately have "((\<lambda>x. ln (\<pi> x) * ?f x * (1 / ln (\<pi> x))) \<longlongrightarrow> ln 1 * 0) at_top"
    by (rule tendsto_mult)
  moreover have "eventually (\<lambda>x. ln (\<pi> x) * ?f x * (1 / ln (\<pi> x)) = ?f x) at_top"
    using ev by eventually_elim auto
  ultimately have "(?f \<longlongrightarrow> ln 1 * 0) at_top"
    by (rule Lim_transform_eventually)
  hence "((\<lambda>x. 1 + ln (ln (\<pi> x)) / ln (\<pi> x) - ?f x) \<longlongrightarrow> 1 + 0 - ln 1 * 0) at_top"
    by (intro tendsto_intros filterlim_compose[OF _ \<pi>_at_top]) (real_asymp | simp)+
  hence "((\<lambda>x. ln x / ln (\<pi> x)) \<longlongrightarrow> 1) at_top"
    by simp
  thus *: "(\<lambda>x. ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. ln x)"
    by (rule asymp_equiv_symI[OF asymp_equivI'])

  have "eventually (\<lambda>x. \<pi> x = \<pi> x * ln (\<pi> x) / ln (\<pi> x)) at_top"
    using ev by eventually_elim auto
  hence "\<pi> \<sim>[at_top] (\<lambda>x. \<pi> x * ln (\<pi> x) / ln (\<pi> x))"
    by (rule asymp_equiv_refl_ev)
  also from assms and * have "(\<lambda>x. \<pi> x * ln (\<pi> x) / ln (\<pi> x)) \<sim>[at_top] (\<lambda>x. x / ln x)"
    by (rule asymp_equiv_intros)
  finally show "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)" .
qed

lemma PNT4_imp_PNT5:
  assumes "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<psi> \<sim>[at_top] (\<lambda>x. x)"
proof -
  define r where "r = (\<lambda>x. \<psi> x - \<theta> x)"
  have "r \<in> O(\<lambda>x. ln x * sqrt x)"
    unfolding r_def by (fact \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x::real. ln x * sqrt x) \<in> o(\<lambda>x. x)"
    by real_asymp
  finally have r: "r \<in> o(\<lambda>x. x)" .

  have "(\<lambda>x. \<theta> x + r x) \<sim>[at_top] (\<lambda>x. x)"
    using assms r by (subst asymp_equiv_add_right) auto
  thus ?thesis by (simp add: r_def)
qed

lemma PNT4_imp_PNT1:
  assumes "\<theta> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
proof -
  have "(\<lambda>x. (\<pi> x - \<theta> x / ln x) + ((\<theta> x - x) / ln x)) \<in> o(\<lambda>x. x / ln x)"
  proof (rule sum_in_smallo)
    have "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> O(\<lambda>x. x / ln x ^ 2)"
      by (rule \<pi>_\<theta>_bigo)
    also have "(\<lambda>x. x / ln x ^ 2) \<in> o(\<lambda>x. x / ln x :: real)"
      by real_asymp
    finally show "(\<lambda>x. \<pi> x - \<theta> x / ln x) \<in> o(\<lambda>x. x / ln x)" .
  next
    have "eventually (\<lambda>x::real. ln x > 0) at_top" by real_asymp
    hence "eventually (\<lambda>x::real. ln x \<noteq> 0) at_top" by eventually_elim auto
    thus "(\<lambda>x. (\<theta> x - x) / ln x) \<in> o(\<lambda>x. x / ln x)"
      by (intro landau_o.small.divide_right asymp_equiv_imp_diff_smallo assms)
  qed
  thus ?thesis by (simp add: diff_divide_distrib asymp_equiv_altdef)
qed

lemma PNT1_imp_PNT4:
  assumes "\<pi> \<sim>[at_top] (\<lambda>x. x / ln x)"
  shows   "\<theta> \<sim>[at_top] (\<lambda>x. x)"
proof -
  have "\<theta> \<sim>[at_top] (\<lambda>x. \<pi> x * ln x)"
  proof (rule smallo_imp_asymp_equiv)
    have "(\<lambda>x. \<theta> x - \<pi> x * ln x) \<in> \<Theta>(\<lambda>x. - ((\<pi> x - \<theta> x / ln x) * ln x))"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 1]])
         (auto simp: field_simps)
    also have "(\<lambda>x. - ((\<pi> x - \<theta> x / ln x) * ln x)) \<in> O(\<lambda>x. x / (ln x)\<^sup>2 * ln x)"
      unfolding landau_o.big.uminus_in_iff by (intro landau_o.big.mult_right \<pi>_\<theta>_bigo)
    also have "(\<lambda>x::real. x / (ln x)\<^sup>2 * ln x) \<in> o(\<lambda>x. x / ln x * ln x)"
      by real_asymp
    also have "(\<lambda>x. x / ln x * ln x) \<in> \<Theta>(\<lambda>x. \<pi> x * ln x)"
      by (intro asymp_equiv_imp_bigtheta asymp_equiv_intros asymp_equiv_symI[OF assms])
    finally show "(\<lambda>x. \<theta> x - \<pi> x * ln x) \<in> o(\<lambda>x. \<pi> x * ln x)" .
  qed
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x / ln x * ln x)"
    by (intro asymp_equiv_intros assms)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x)"
    by real_asymp
  finally show ?thesis .
qed

lemma PNT5_imp_PNT4:
  assumes "\<psi> \<sim>[at_top] (\<lambda>x. x)"
  shows   "\<theta> \<sim>[at_top] (\<lambda>x. x)"
proof -
  define r where "r = (\<lambda>x. \<theta> x - \<psi> x)"
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)"
    by (fact \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x. \<psi> x - \<theta> x) = (\<lambda>x. -r x)"
    by (simp add: r_def)
  finally have "r \<in> O(\<lambda>x. ln x * sqrt x)"
    by simp
  also have "(\<lambda>x::real. ln x * sqrt x) \<in> o(\<lambda>x. x)"
    by real_asymp
  finally have r: "r \<in> o(\<lambda>x. x)" .

  have "(\<lambda>x. \<psi> x + r x) \<sim>[at_top] (\<lambda>x. x)"
    using assms r by (subst asymp_equiv_add_right) auto
  thus ?thesis by (simp add: r_def)
qed


subsection \<open>The asymptotic form of Mertens' First Theorem\<close>

text \<open>
  Mertens' first theorem states that $\mathfrak{M}(x) - \ln x$ is bounded, i.\,e.\ 
  $\mathfrak{M}(x) = \ln x + O(1)$.

  With some work, one can also show some absolute bounds for $|\mathfrak{M}(x) - \ln x|$, and we
  will, in fact, do this later. However, this asymptotic form is somewhat easier to obtain and it is
  (as we shall see) enough to prove the Prime Number Theorem, so we prove the weak form here first
  for the sake of a smoother presentation.

  First of all, we need a very weak version of Stirling's formula for the logarithm of
  the factorial, namely:
  \[\ln(\lfloor x\rfloor!) = \sum\limits_{n\leq x} \ln x = x \ln x + O(x)\]
  We show this using summation by parts.
\<close>
lemma stirling_weak:
  assumes x: "x \<ge> 1"
  shows   "sum_upto ln x \<in> {x * ln x - x - ln x + 1 .. x * ln x}"
proof (cases "x = 1")
  case True
  have "{0<..Suc 0} = {1}" by auto
  with True show ?thesis by (simp add: sum_upto_altdef)
next
  case False
  with assms have x: "x > 1" by simp
  have "((\<lambda>t. sum_upto (\<lambda>_. 1) t * (1 / t)) has_integral
          sum_upto (\<lambda>_. 1) x * ln x - sum_upto (\<lambda>_. 1) 1 * ln 1 -
          (\<Sum>n\<in>real -` {1<..x}. 1 * ln (real n))) {1..x}" using x
    by (intro partial_summation_strong[of "{}"])
       (auto simp flip: has_field_derivative_iff_has_vector_derivative
             intro!: derivative_eq_intros continuous_intros)
  hence "((\<lambda>t. real (nat \<lfloor>t\<rfloor>) / t) has_integral
           real (nat \<lfloor>x\<rfloor>) * ln x - (\<Sum>n\<in>real -` {1<..x}. ln (real n))) {1..x}"
    by (simp add: sum_upto_altdef)
  also have "(\<Sum>n\<in>real -` {1<..x}. ln (real n)) = sum_upto ln x" unfolding sum_upto_def
    by (intro sum.mono_neutral_left)
       (auto intro!: finite_subset[OF _ finite_vimage_real_of_nat_greaterThanAtMost[of 0 x]])
  finally have *: "((\<lambda>t. real (nat \<lfloor>t\<rfloor>) / t) has_integral \<lfloor>x\<rfloor> * ln x - sum_upto ln x) {1..x}"
    using x by simp

  have "0 \<le> real_of_int \<lfloor>x\<rfloor> * ln x - sum_upto (\<lambda>n. ln (real n)) x"
    using * by (rule has_integral_nonneg) auto
  also have "\<dots> \<le> x * ln x - sum_upto ln x"
    using x by (intro diff_mono mult_mono) auto
  finally have upper: "sum_upto ln x \<le> x * ln x" by simp

  have "(x - 1) * ln x - x + 1 \<le> \<lfloor>x\<rfloor> * ln x - x + 1"
    using x by (intro diff_mono mult_mono add_mono) auto
  also have "((\<lambda>t. 1) has_integral (x - 1)) {1..x}"
    using has_integral_const_real[of "1::real" 1 x] x by simp
  from * and this have "\<lfloor>x\<rfloor> * ln x - sum_upto ln x \<le> x - 1"
    by (rule has_integral_le) auto
  hence "\<lfloor>x\<rfloor> * ln x - x + 1 \<le> sum_upto ln x"
    by simp
  finally have "sum_upto ln x \<ge> x * ln x - x - ln x + 1"
    by (simp add: algebra_simps)
  with upper show ?thesis by simp
qed

lemma stirling_weak_bigo: "(\<lambda>x::real. sum_upto ln x - x * ln x) \<in> O(\<lambda>x. x)"
proof -
  have "(\<lambda>x. sum_upto ln x - x * ln x) \<in> O(\<lambda>x. -(sum_upto ln x - x * ln x))"
    by (subst landau_o.big.uminus) auto
  also have "(\<lambda>x. -(sum_upto ln x - x * ln x)) \<in> O(\<lambda>x. x + ln x - 1)"
  proof (intro le_imp_bigo_real[of 2] eventually_mono[OF eventually_ge_at_top[of 1]], goal_cases)
    case (2 x)
    thus ?case using stirling_weak[of x] by (auto simp: algebra_simps)
  next
    case (3 x)
    thus ?case using stirling_weak[of x] by (auto simp: algebra_simps)
  qed auto
  also have "(\<lambda>x. x + ln x - 1) \<in> O(\<lambda>x::real. x)" by real_asymp
  finally show ?thesis .
qed

lemma floor_floor_div_eq:
  fixes x :: real and d :: nat
  assumes "x \<ge> 0"
  shows   "\<lfloor>nat \<lfloor>x\<rfloor> / real d\<rfloor> = \<lfloor>x / real d\<rfloor>"
proof -
  have "\<lfloor>nat \<lfloor>x\<rfloor> / real_of_int (int d)\<rfloor> = \<lfloor>x / real_of_int (int d)\<rfloor>" using assms
    by (subst (1 2) floor_divide_real_eq_div) auto
  thus ?thesis by simp
qed

text \<open>
  The key to showing Mertens' first theorem is the function
  \[h(x) := \sum\limits_{n \leq x} \frac{\Lambda(d)}{d}\]
  where $\Lambda$ is the Mangoldt function, which is equal to $\ln p$ for any prime power
  $p^k$ and $0$ otherwise. As we shall see, $h(x)$ is a good approximation for $\mathfrak M(x)$,
  as the difference between them is bounded by a constant.
\<close>
lemma sum_upto_mangoldt_over_id_minus_phi_bounded:
    "(\<lambda>x. sum_upto (\<lambda>d. mangoldt d / real d) x - \<MM> x) \<in> O(\<lambda>_. 1)"
proof -
  define f where "f = (\<lambda>d. mangoldt d / real d)"
  define C where "C = (\<Sum>p. ln (real (p + 1)) * (1 / real (p * (p - 1))))"
  have summable: "summable (\<lambda>p::nat. ln (p + 1) * (1 / (p * (p - 1))))"
  proof (rule summable_comparison_test_bigo)
    show "summable (\<lambda>p. norm (p powr (-3/2)))"
      by (simp add: summable_real_powr_iff)
  qed real_asymp

  have diff_bound: "sum_upto f x - \<MM> x \<in> {0..C}" if x: "x \<ge> 4" for x
  proof -
    define S where "S = {(p, i). prime p \<and> 0 < i \<and> real (p ^ i) \<le> x}"
    define S' where "S' = (SIGMA p:{2..nat \<lfloor>root 2 x\<rfloor>}. {2..nat \<lfloor>log 2 x\<rfloor>})"
    have "S \<subseteq> {..nat \<lfloor>x\<rfloor>} \<times> {..nat \<lfloor>log 2 x\<rfloor>}" unfolding S_def
      using x primepows_le_subset[of x 1] by (auto simp: Suc_le_eq)
    hence "finite S" by (rule finite_subset) auto
    note fin = finite_subset[OF _ this, unfolded S_def]
  
    have "sum_upto f x = (\<Sum>(p, i)\<in>S. ln (real p) / real (p ^ i))" unfolding S_def
      by (intro sum_upto_primepows) (auto simp: f_def mangoldt_non_primepow)
    also have "S = {p. prime p \<and> p \<le> x} \<times> {1} \<union> {(p, i). prime p \<and> 1 < i \<and> real (p ^ i) \<le> x}"
      by (auto simp: S_def not_less le_Suc_eq not_le intro!: Suc_lessI)
    also have "(\<Sum>(p,i)\<in>\<dots>. ln (real p) / real (p ^ i)) =
                 (\<Sum>(p, i) \<in> {p. prime p \<and> of_nat p \<le> x} \<times> {1}. ln (real p) / real (p ^ i)) +
                 (\<Sum>(p, i) | prime p \<and> real (p ^ i) \<le> x \<and> i > 1. ln (real p) / real (p ^ i))"
      (is "_ = ?S1 + ?S2")
      by (subst sum.union_disjoint[OF fin fin]) (auto simp: conj_commute case_prod_unfold)
    also have "?S1 = \<MM> x"
      by (subst sum.cartesian_product [symmetric]) (auto simp: primes_M_def prime_sum_upto_def)
    finally have eq: "sum_upto f x - \<MM> x = ?S2" by simp
    have "?S2 \<le> (\<Sum>(p, i)\<in>S'. ln (real p) / real (p ^ i))"
      using primepows_le_subset[of x 2] x unfolding case_prod_unfold of_nat_power
      by (intro sum_mono2 divide_nonneg_pos zero_less_power)
         (auto simp: eval_nat_numeral Suc_le_eq S'_def subset_iff dest: prime_gt_1_nat)+
    also have "\<dots> = (\<Sum>p=2..nat \<lfloor>sqrt x\<rfloor>. ln p * (\<Sum>i\<in>{2..nat \<lfloor>log 2 x\<rfloor>}. (1 / real p) ^ i))"
      by (simp add: S'_def sum.Sigma case_prod_unfold
                    sum_distrib_left sqrt_def field_simps)
    also have "\<dots> \<le> (\<Sum>p=2..nat \<lfloor>sqrt x\<rfloor>. ln p * (1 / (p * (p - 1))))"
      unfolding sum_upto_def
    proof (intro sum_mono, goal_cases)
      case (1 p)
      from x have "nat \<lfloor>log 2 x\<rfloor> \<ge> 2"
        by (auto simp: le_nat_iff' le_log_iff)
      hence "(\<Sum>i\<in>{2..nat \<lfloor>log 2 x\<rfloor>}. (1 / real p) ^ i) = 
               ((1 / p)\<^sup>2 - (1 / p) ^ nat \<lfloor>log 2 x\<rfloor> / p) / (1 - 1 / p)" using 1
        by (subst sum_gp) (auto dest!: prime_gt_1_nat simp: field_simps power2_eq_square)
      also have "\<dots> \<le> ((1 / p) ^ 2 - 0) / (1 - 1 / p)"
        using 1 by (intro divide_right_mono diff_mono power_mono)
                   (auto simp: field_simps dest: prime_gt_0_nat)
      also have "\<dots> = 1 / (p * (p - 1))"
        by (auto simp: divide_simps power2_eq_square dest: prime_gt_0_nat)
      finally show ?case
        using 1 by (intro mult_left_mono) (auto dest: prime_gt_0_nat)
    qed
    also have "\<dots> \<le> (\<Sum>p=2..nat \<lfloor>sqrt x\<rfloor>. ln (p + 1) * (1 / (p * (p - 1))))"
      by (intro sum_mono mult_mono) auto
    also have "\<dots> \<le> C" unfolding C_def
      by (intro sum_le_suminf summable) auto
    finally have "?S2 \<le> C" by simp
    moreover have "?S2 \<ge> 0" by (intro sum_nonneg) (auto dest: prime_gt_0_nat)
    ultimately show ?thesis using eq by simp
  qed

  from diff_bound[of 4] have "C \<ge> 0" by auto
  with diff_bound show "(\<lambda>x. sum_upto f x - \<MM> x) \<in> O(\<lambda>_. 1)"
    by (intro le_imp_bigo_real[of C] eventually_mono[OF eventually_ge_at_top[of 4]]) auto
qed

text \<open>
  Next, we show that our $h(x)$ itself is close to $\ln x$, i.\,e.:
  \[\sum\limits_{n \leq x} \frac{\Lambda(d)}{d} = \ln x + O(1)\]
\<close>
lemma sum_upto_mangoldt_over_id_asymptotics:
  "(\<lambda>x. sum_upto (\<lambda>d. mangoldt d / real d) x - ln x) \<in> O(\<lambda>_. 1)"
proof -
  define r where "r = (\<lambda>n::real. sum_upto (\<lambda>d. mangoldt d * (n / d - real_of_int \<lfloor>n / d\<rfloor>)) n)"
  have r: "r \<in> O(\<psi>)"
  proof (intro landau_o.bigI[of 1] eventually_mono[OF eventually_ge_at_top[of 0]])
    fix x :: real assume x: "x \<ge> 0"
    have eq: "{1..nat \<lfloor>x\<rfloor>} = {0<..nat \<lfloor>x\<rfloor>}" by auto
    hence "r x \<ge> 0" unfolding r_def sum_upto_def
      by (intro sum_nonneg mult_nonneg_nonneg mangoldt_nonneg)
         (auto simp: floor_le_iff)
    moreover have "x / real d \<le> 1 + real_of_int \<lfloor>x / real d\<rfloor>" for d by linarith
    hence "r x \<le> sum_upto (\<lambda>d. mangoldt d * 1) x" unfolding sum_upto_altdef eq r_def using x
      by (intro sum_mono mult_mono mangoldt_nonneg)
         (auto simp:  less_imp_le[OF frac_lt_1] algebra_simps)
    ultimately show "norm (r x) \<le> 1 * norm (\<psi> x)" by (simp add: \<psi>_def)
  qed auto
  also have "\<psi> \<in> O(\<lambda>x. x)" by (fact \<psi>_bigo)
  finally have r: "r \<in> O(\<lambda>x. x)" .

  define r' where "r' = (\<lambda>x::real. sum_upto ln x - x * ln x)"
  have r'_bigo: "r' \<in> O(\<lambda>x. x)"
    using stirling_weak_bigo unfolding r'_def .
  have ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)" for n
    by (induction n) (simp_all add: ln_mult)
  hence r': "sum_upto ln n = n * ln n + r' n" for n :: real
    unfolding r'_def sum_upto_altdef by (auto intro!: sum.cong)

  have "eventually (\<lambda>n. sum_upto (\<lambda>d. mangoldt d / d) n - ln n = r' n / n + r n / n) at_top"
    using eventually_gt_at_top
  proof eventually_elim
    fix x :: real assume x: "x > 0"
    have "sum_upto ln x = sum_upto (\<lambda>n. mangoldt n * real (nat \<lfloor>x / n\<rfloor>)) x"
      unfolding sum_upto_ln_conv_sum_upto_mangoldt ..
    also have "\<dots> = sum_upto (\<lambda>d. mangoldt d * (x / d)) x - r x"
      unfolding sum_upto_def by (simp add: algebra_simps sum_subtractf r_def sum_upto_def)
    also have "sum_upto (\<lambda>d. mangoldt d * (x / d)) x = x * sum_upto (\<lambda>d. mangoldt d / d) x"
      unfolding sum_upto_def by (subst sum_distrib_left) (simp add: field_simps)
    finally have "x * sum_upto (\<lambda>d. mangoldt d / real d) x = r' x + r x + x * ln x"
      by (simp add: r' algebra_simps)
    thus "sum_upto (\<lambda>d. mangoldt d / d) x - ln x = r' x / x + r x / x"
      using x by (simp add: field_simps)
  qed
  hence "(\<lambda>x. sum_upto (\<lambda>d. mangoldt d / d) x - ln x) \<in> \<Theta>(\<lambda>x. r' x / x + r x / x)"
    by (rule bigthetaI_cong)
  also have "(\<lambda>x. r' x / x + r x / x) \<in> O(\<lambda>_. 1)"
    by (intro sum_in_bigo) (insert r r'_bigo, auto simp: landau_divide_simps)
  finally show ?thesis .
qed

text \<open>
  Combining these two gives us Mertens' first theorem.
\<close>
theorem mertens_bounded: "(\<lambda>x. \<MM> x - ln x) \<in> O(\<lambda>_. 1)"
proof -
  define f where "f = sum_upto (\<lambda>d. mangoldt d / d)"
  have "(\<lambda>x. (f x - ln x) - (f x - \<MM> x)) \<in> O(\<lambda>_. 1)"
    using sum_upto_mangoldt_over_id_asymptotics
          sum_upto_mangoldt_over_id_minus_phi_bounded
    unfolding f_def by (rule sum_in_bigo)
  thus ?thesis by simp
qed

lemma primes_M_bigo: "\<MM> \<in> O(\<lambda>x. ln x)"
proof -
  have "(\<lambda>x. \<MM> x - ln x) \<in> O(\<lambda>_. 1)"
    by (rule mertens_bounded)
  also have "(\<lambda>_::real. 1) \<in> O(\<lambda>x. ln x)"
    by real_asymp
  finally have "(\<lambda>x. \<MM> x - ln x + ln x) \<in> O(\<lambda>x. ln x)"
    by (rule sum_in_bigo) auto
  thus ?thesis by simp
qed

(*<*)
unbundle no_prime_counting_notation
(*>*)

end
