(*
  File:    Prime_Distribution_Elementary_Library.thy
  Author:  Manuel Eberl, TU München

  Various auxiliary material, much of which should probably be moved somewhere else
  eventually.
*)
section \<open>Auxiliary material\<close>
theory Prime_Distribution_Elementary_Library
imports
  Zeta_Function.Zeta_Function
  Prime_Number_Theorem.Prime_Counting_Functions
  Stirling_Formula.Stirling_Formula
begin

lemma divisor_count_pos [intro]: "n > 0 \<Longrightarrow> divisor_count n > 0"
  by (auto simp: divisor_count_def intro!: Nat.gr0I)

lemma divisor_count_eq_0_iff [simp]: "divisor_count n = 0 \<longleftrightarrow> n = 0"
  by (cases "n = 0") auto

lemma divisor_count_pos_iff [simp]: "divisor_count n > 0 \<longleftrightarrow> n > 0"
  by (cases "n = 0") auto

lemma smallest_prime_beyond_eval:
  "prime n \<Longrightarrow> smallest_prime_beyond n = n"
  "\<not>prime n \<Longrightarrow> smallest_prime_beyond n = smallest_prime_beyond (Suc n)"
proof -
  assume "prime n"
  thus "smallest_prime_beyond n = n"
    by (rule smallest_prime_beyond_eq) auto
next
  assume "\<not>prime n"
  show "smallest_prime_beyond n = smallest_prime_beyond (Suc n)"
  proof (rule antisym)
    show "smallest_prime_beyond n \<le> smallest_prime_beyond (Suc n)"
      by (rule smallest_prime_beyond_smallest)
         (auto intro: order.trans[OF _ smallest_prime_beyond_le])
  next
    have "smallest_prime_beyond n \<noteq> n"
      using prime_smallest_prime_beyond[of n] \<open>\<not>prime n\<close> by metis
    hence "smallest_prime_beyond n > n"
      using smallest_prime_beyond_le[of n] by linarith
    thus "smallest_prime_beyond n \<ge> smallest_prime_beyond (Suc n)"
      by (intro smallest_prime_beyond_smallest) auto
  qed
qed

lemma nth_prime_numeral:
  "nth_prime (numeral n) = smallest_prime_beyond (Suc (nth_prime (pred_numeral n)))"
  by (subst nth_prime_Suc[symmetric]) auto

lemmas nth_prime_eval = smallest_prime_beyond_eval nth_prime_Suc nth_prime_numeral

lemma nth_prime_1 [simp]: "nth_prime (Suc 0) = 3"
  by (simp add: nth_prime_eval)

lemma nth_prime_2 [simp]: "nth_prime 2 = 5"
  by (simp add: nth_prime_eval)

lemma nth_prime_3 [simp]: "nth_prime 3 = 7"
  by (simp add: nth_prime_eval)

(* TODO: copied from afp-devel; delete in AFP 2019 *)
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
  includes prime_counting_notation
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
(* END TODO *)

(* TODO: Move *)
lemma asymp_equivD_strong:
  assumes "f \<sim>[F] g" "eventually (\<lambda>x. f x \<noteq> 0 \<or> g x \<noteq> 0) F"
  shows   "((\<lambda>x. f x / g x) \<longlongrightarrow> 1) F"
proof -
  from assms(1) have "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"
    by (rule asymp_equivD)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro filterlim_cong eventually_mono[OF assms(2)]) auto
  finally show ?thesis .
qed

lemma hurwitz_zeta_shift:
  fixes s :: complex
  assumes "a > 0" and "s \<noteq> 1"
  shows   "hurwitz_zeta (a + real n) s = hurwitz_zeta a s - (\<Sum>k<n. (a + real k) powr -s)"
proof (rule analytic_continuation_open[where f = "\<lambda>s. hurwitz_zeta (a + real n) s"])
  fix s assume s: "s \<in> {s. Re s > 1}"
  have "(\<lambda>k. (a + of_nat (k + n)) powr -s) sums hurwitz_zeta (a + real n) s"
    using sums_hurwitz_zeta[of "a + real n" s] s assms by (simp add: add_ac)
  moreover have "(\<lambda>k. (a + of_nat k) powr -s) sums hurwitz_zeta a s"
    using sums_hurwitz_zeta[of a s] s assms by (simp add: add_ac)
  hence "(\<lambda>k. (a + of_nat (k + n)) powr -s) sums
            (hurwitz_zeta a s - (\<Sum>k<n. (a + of_nat k) powr -s))"
    by (rule sums_split_initial_segment)
  ultimately show "hurwitz_zeta (a + real n) s = hurwitz_zeta a s - (\<Sum>k<n. (a + real k) powr -s)"
    by (simp add: sums_iff)
next
  show "connected (-{1::complex})"
    by (rule connected_punctured_universe) auto
qed (use assms in \<open>auto intro!: holomorphic_intros open_halfspace_Re_gt exI[of _ 2]\<close>)

lemma pbernpoly_bigo: "pbernpoly n \<in> O(\<lambda>_. 1)"
proof -
  from bounded_pbernpoly[of n] obtain c where "\<And>x. norm (pbernpoly n x) \<le> c"
    by auto
  thus ?thesis by (intro bigoI[of _ c]) auto
qed

lemma harm_le: "n \<ge> 1 \<Longrightarrow> harm n \<le> ln n + 1"
  using euler_mascheroni_sequence_decreasing[of 1 n]
  by (simp add: harm_expand)

lemma sum_upto_1 [simp]: "sum_upto f 1 = f 1"
proof -
  have "{0<..Suc 0} = {1}" by auto
  thus ?thesis by (simp add: sum_upto_altdef)
qed

(* TODO: replace original *)
lemma sum_upto_cong' [cong]:
  "(\<And>n. n > 0 \<Longrightarrow> real n \<le> x \<Longrightarrow> f n = f' n) \<Longrightarrow> x = x' \<Longrightarrow> sum_upto f x = sum_upto f' x'"
  unfolding sum_upto_def by (intro sum.cong) auto

lemma finite_primes_le: "finite {p. prime p \<and> real p \<le> x}"
  by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)

lemma frequently_filtermap: "frequently P (filtermap f F) = frequently (\<lambda>n. P (f n)) F"
  by (auto simp: frequently_def eventually_filtermap)

lemma frequently_mono_filter: "frequently P F \<Longrightarrow> F \<le> F' \<Longrightarrow> frequently P F'"
  using filter_leD[of F F' "\<lambda>x. \<not>P x"] by (auto simp: frequently_def)

lemma \<pi>_at_top: "filterlim primes_pi at_top at_top"
  unfolding filterlim_at_top
proof safe
  fix C :: real
  define x0 where "x0 = real (nth_prime (nat \<lceil>max 0 C\<rceil>))"
  show "eventually (\<lambda>x. primes_pi x \<ge> C) at_top"
    using eventually_ge_at_top
  proof eventually_elim
    fix x assume "x \<ge> x0"
    have "C \<le> real (nat \<lceil>max 0 C\<rceil> + 1)" by linarith
    also have "real (nat \<lceil>max 0 C\<rceil> + 1) = primes_pi x0"
      unfolding x0_def by simp
    also have "\<dots> \<le> primes_pi x" by (rule \<pi>_mono) fact
    finally show "primes_pi x \<ge> C" .
  qed
qed

lemma sum_upto_ln_stirling_weak_bigo: "(\<lambda>x. sum_upto ln x - x * ln x + x) \<in> O(ln)"
proof -
  let ?f = "\<lambda>x. x * ln x - x + ln (2 * pi * x) / 2"
  have "ln (fact n) - (n * ln n - n + ln (2 * pi * n) / 2) \<in> {0..1/(12*n)}" if "n > 0" for n :: nat
    using ln_fact_bounds[OF that] by (auto simp: algebra_simps)
  hence "(\<lambda>n. ln (fact n) - ?f n) \<in> O(\<lambda>n. 1 / real n)"
    by (intro bigoI[of _ "1/12"] eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x. 1 / real (nat \<lfloor>x\<rfloor>))"
    by (rule landau_o.big.compose)
       (intro filterlim_compose[OF filterlim_nat_sequentially] filterlim_floor_sequentially)
  also have "(\<lambda>x. 1 / real (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x::real. ln x)" by real_asymp
  finally have "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f (nat \<lfloor>x\<rfloor>) + (?f (nat \<lfloor>x\<rfloor>) - ?f x)) \<in> O(\<lambda>x. ln x)"
    by (rule sum_in_bigo) real_asymp
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f x) \<in> O(\<lambda>x. ln x)"
    by (simp add: algebra_simps)
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f x + ln (2 * pi * x) / 2) \<in> O(\<lambda>x. ln x)"
    by (rule sum_in_bigo) real_asymp
  thus ?thesis by (simp add: sum_upto_ln_conv_ln_fact algebra_simps)
qed


subsection \<open>Various facts about Dirichlet series\<close>

lemma fds_mangoldt':
  "fds mangoldt = fds_zeta * fds_deriv (fds moebius_mu)"
proof -
  have "fds mangoldt = (fds moebius_mu * fds (\<lambda>n. of_real (ln (real n)) :: 'a))"
    (is "_ = ?f") by (subst fds_mangoldt) auto
  also have "\<dots> = fds_zeta * fds_deriv (fds moebius_mu)"
  proof (intro fds_eqI)
    fix n :: nat assume n: "n > 0"
    have "fds_nth ?f n = (\<Sum>d | d dvd n. moebius_mu d * of_real (ln (real (n div d))))"
      by (auto simp: fds_eq_iff fds_nth_mult dirichlet_prod_def)
    also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * of_real (ln (real n / real d)))"
      by (intro sum.cong) (auto elim!: dvdE simp: ln_mult split: if_splits)
    also have "\<dots> = (\<Sum>d | d dvd n. moebius_mu d * of_real (ln n - ln d))"
      using n by (intro sum.cong refl) (subst ln_div, auto elim!: dvdE)
    also have "\<dots> = of_real (ln n) * (\<Sum>d | d dvd n. moebius_mu d) -
                      (\<Sum>d | d dvd n. of_real (ln d) * moebius_mu d)"
      by (simp add: sum_subtractf sum_distrib_left sum_distrib_right algebra_simps)
    also have "of_real (ln n) * (\<Sum>d | d dvd n. moebius_mu d) = 0"
      by (subst sum_moebius_mu_divisors') auto
    finally show "fds_nth ?f n = fds_nth (fds_zeta * fds_deriv (fds moebius_mu) :: 'a fds) n"
      by (simp add: fds_nth_mult dirichlet_prod_altdef1 fds_nth_deriv sum_negf scaleR_conv_of_real)
  qed
  finally show ?thesis .
qed

lemma sum_upto_divisor_sum1:
  "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x = sum_upto (\<lambda>n. f n * floor (x / n)) x"
proof -
  have "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x =
          sum_upto (\<lambda>n. f n * real (nat (floor (x / n)))) x"
    using sum_upto_dirichlet_prod[of f "\<lambda>_. 1" x]
    by (simp add: dirichlet_prod_def sum_upto_altdef)
  also have "\<dots> = sum_upto (\<lambda>n. f n * floor (x / n)) x"
    unfolding sum_upto_def by (intro sum.cong) auto
  finally show ?thesis .
qed

lemma sum_upto_divisor_sum2:
  "sum_upto (\<lambda>n. \<Sum>d | d dvd n. f d :: real) x = sum_upto (\<lambda>n. sum_upto f (x / n)) x"
  using sum_upto_dirichlet_prod[of "\<lambda>_. 1" f x] by (simp add: dirichlet_prod_altdef1)

lemma sum_upto_moebius_times_floor_linear:
  "sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x = (if x \<ge> 1 then 1 else 0)"
proof -
  have "real_of_int (sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x) =
          sum_upto (\<lambda>n. moebius_mu n * of_int \<lfloor>x / real n\<rfloor>) x"
    by (simp add: sum_upto_def)
  also have "\<dots> = sum_upto (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d :: real) x"
    using sum_upto_divisor_sum1[of moebius_mu x] by auto
  also have "\<dots> = sum_upto (\<lambda>n. if n = 1 then 1 else 0) x"
    by (intro sum_upto_cong sum_moebius_mu_divisors' refl)
  also have "\<dots> = real_of_int (if x \<ge> 1 then 1 else 0)"
    by (auto simp: sum_upto_def)
  finally show ?thesis unfolding of_int_eq_iff .
qed

lemma ln_fact_conv_sum_mangoldt:
  "sum_upto (\<lambda>n. mangoldt n * \<lfloor>x / real n\<rfloor>) x = ln (fact (nat \<lfloor>x\<rfloor>))"
proof -
  have "sum_upto (\<lambda>n. mangoldt n * of_int \<lfloor>x / real n\<rfloor>) x =
          sum_upto (\<lambda>n. \<Sum>d | d dvd n. mangoldt d :: real) x"
    using sum_upto_divisor_sum1[of mangoldt x] by auto
  also have "\<dots> = sum_upto (\<lambda>n. of_real (ln (real n))) x"
    by (intro sum_upto_cong mangoldt_sum refl) auto
  also have "\<dots> = (\<Sum>n\<in>{0<..nat \<lfloor>x\<rfloor>}. ln n)"
    by (simp add: sum_upto_altdef)
  also have "\<dots> = ln (\<Prod>{0<..nat \<lfloor>x\<rfloor>})"
    unfolding of_nat_prod by (subst ln_prod) auto
  also have "{0<..nat \<lfloor>x\<rfloor>} = {1..nat \<lfloor>x\<rfloor>}" by auto
  also have "\<Prod>\<dots> = fact (nat \<lfloor>x\<rfloor>)"
    by (simp add: fact_prod)
  finally show ?thesis by simp
qed


subsection \<open>Facts about prime-counting functions\<close>

lemma abs_\<pi> [simp]: "\<bar>primes_pi x\<bar> = primes_pi x"
  by (subst abs_of_nonneg) auto

lemma \<pi>_less_self:
  includes prime_counting_notation
  assumes "x > 0"
  shows   "\<pi> x < x"
proof -
  have "\<pi> x \<le> (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. 1)"
    unfolding \<pi>_def prime_sum_upto_altdef2 by (intro sum_mono2) (auto dest: prime_gt_1_nat)
  also have "\<dots> = real (nat \<lfloor>x\<rfloor> - 1)"
    using assms by simp
  also have "\<dots> < x" using assms by linarith
  finally show ?thesis .
qed

lemma \<pi>_le_self':
  includes prime_counting_notation
  assumes "x \<ge> 1"
  shows   "\<pi> x \<le> x - 1"
proof -
  have "\<pi> x \<le> (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. 1)"
    unfolding \<pi>_def prime_sum_upto_altdef2 by (intro sum_mono2) (auto dest: prime_gt_1_nat)
  also have "\<dots> = real (nat \<lfloor>x\<rfloor> - 1)"
    using assms by simp
  also have "\<dots> \<le> x - 1" using assms by linarith
  finally show ?thesis .
qed

lemma \<pi>_le_self:
  includes prime_counting_notation
  assumes "x \<ge> 0"
  shows   "\<pi> x \<le> x"
  using \<pi>_less_self[of x] assms by (cases "x = 0") auto

subsection \<open>Strengthening `Big-O' bounds\<close>

text \<open>
  The following two statements are crucial: They allow us to strengthen a `Big-O' statement
  for $n\to\infty$ or $x\to\infty$ to a bound for \<^emph>\<open>all\<close> $n\geq n_0$ or all $x\geq x_0$ under
  some mild conditions.

  This allows us to use all the machinery of asymptotics in Isabelle and still get a bound
  that is applicable over the full domain of the function in the end. This is important because
  Newman often shows that $f(x) \in O(g(x))$ and then writes
  \[\sum_{n\leq x} f(\frac{x}{n}) = \sum_{n\leq x} O(g(\frac{x}{n}))\]
  which is not easy to justify otherwise.
\<close>
lemma natfun_bigoE:
  fixes f :: "nat \<Rightarrow> _"
  assumes bigo: "f \<in> O(g)" and nz: "\<And>n. n \<ge> n0 \<Longrightarrow> g n \<noteq> 0"
  obtains c where "c > 0" "\<And>n. n \<ge> n0 \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
proof -
  from bigo obtain c where c: "c > 0" "eventually (\<lambda>n. norm (f n) \<le> c * norm (g n)) at_top"
    by (auto elim: landau_o.bigE)
  then obtain n0' where n0': "\<And>n. n \<ge> n0' \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
    by (auto simp: eventually_at_top_linorder)
  define c' where "c' = Max ((\<lambda>n. norm (f n) / norm (g n)) ` (insert n0 {n0..<n0'}))"
  have "norm (f n) \<le> max 1 (max c c') * norm (g n)" if "n \<ge> n0" for n
  proof (cases "n \<ge> n0'")
    case False
    with that have "norm (f n) / norm (g n) \<le> c'"
      unfolding c'_def by (intro Max.coboundedI) auto
    also have "\<dots> \<le> max 1 (max c c')" by simp
    finally show ?thesis using nz[of n] that by (simp add: field_simps)
  next
    case True
    hence "norm (f n) \<le> c * norm (g n)" by (rule n0')
    also have "\<dots> \<le> max 1 (max c c') * norm (g n)"
      by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  with that[of "max 1 (max c c')"] show ?thesis by auto
qed

lemma bigoE_bounded_real_fun:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<in> O(g)"
  assumes "\<And>x. x \<ge> x0 \<Longrightarrow> \<bar>g x\<bar> \<ge> cg" "cg > 0"
  assumes "\<And>b. b \<ge> x0 \<Longrightarrow> bounded (f ` {x0..b})"
  shows   "\<exists>c>0. \<forall>x\<ge>x0. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
proof -
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top"
    by (elim landau_o.bigE) auto
  then obtain b where b: "\<And>x. x \<ge> b \<Longrightarrow> \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
    by (auto simp: eventually_at_top_linorder)
  have "bounded (f ` {x0..max x0 b})" by (intro assms) auto
  then obtain C where C: "\<And>x. x \<in> {x0..max x0 b} \<Longrightarrow> \<bar>f x\<bar> \<le> C"
    unfolding bounded_iff by fastforce

  define c' where "c' = max c (C / cg)"
  have "\<bar>f x\<bar> \<le> c' * \<bar>g x\<bar>" if "x \<ge> x0" for x
  proof (cases "x \<ge> b")
    case False
    hence "\<bar>f x\<bar> / \<bar>g x\<bar> \<le> C / cg"
      using that by (intro frac_le assms C) auto
    also have "\<dots> \<le> c'" by (simp add: c'_def)
    finally show "\<bar>f x\<bar> \<le> c' * \<bar>g x\<bar>"
      using that False assms(2)[of x] assms(3) by (auto simp add: divide_simps split: if_splits)
  next
    case True
    hence "\<bar>f x\<bar> \<le> c * \<bar>g x\<bar>" by (intro b) auto
    also have "\<dots> \<le> c' * \<bar>g x\<bar>" by (intro mult_right_mono) (auto simp: c'_def)
    finally show ?thesis .
  qed
  moreover from c(1) have "c' > 0" by (auto simp: c'_def)
  ultimately show ?thesis by blast
qed

lemma sum_upto_asymptotics_lift_nat_real_aux:
  fixes f :: "nat \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes bigo: "(\<lambda>n. (\<Sum>k=1..n. f k) - g (real n)) \<in> O(\<lambda>n. h (real n))"
  assumes g_bigo_self: "(\<lambda>n. g (real n) - g (real (Suc n))) \<in> O(\<lambda>n. h (real n))"
  assumes h_bigo_self: "(\<lambda>n. h (real n)) \<in> O(\<lambda>n. h (real (Suc n)))"
  assumes h_pos: "\<And>x. x \<ge> 1 \<Longrightarrow> h x > 0"
  assumes mono_g: "mono_on g {1..} \<or> mono_on (\<lambda>x. - g x) {1..}"
  assumes mono_h: "mono_on h {1..} \<or> mono_on (\<lambda>x. - h x) {1..}"
  shows   "\<exists>c>0. \<forall>x\<ge>1. sum_upto f x - g x \<le> c * h x"
proof -
  have h_nz: "h (real n) \<noteq> 0" if "n \<ge> 1" for n
    using h_pos[of n] that by simp

  from natfun_bigoE[OF bigo h_nz] obtain c1 where
    c1: "c1 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm ((\<Sum>k=1..n. f k) - g (real n)) \<le> c1 * norm (h (real n))"
    by auto
  from natfun_bigoE[OF g_bigo_self h_nz] obtain c2 where
    c2: "c2 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm (g (real n) - g (real (Suc n))) \<le> c2 * norm (h (real n))"
    by auto
  from natfun_bigoE[OF h_bigo_self h_nz] obtain c3 where
    c3: "c3 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm (h (real n)) \<le> c3 * norm (h (real (Suc n)))"
    by auto

  {
    fix x :: real assume x: "x \<ge> 1"
    define n where "n = nat \<lfloor>x\<rfloor>"
    from x have n: "n \<ge> 1" unfolding n_def by linarith

    have "(\<Sum>k = 1..n. f k) - g x \<le> (c1 + c2) * h (real n)" using mono_g
    proof
      assume mono: "mono_on (\<lambda>x. -g x) {1..}"
      from x have "x \<le> real (Suc n)"
        unfolding n_def by linarith
      hence "(\<Sum>k=1..n. f k) - g x \<le> (\<Sum>k=1..n. f k) - g n + (g n - g (Suc n))"
        using mono_onD[OF mono, of x "real (Suc n)"] x by auto
      also have "\<dots> \<le> norm ((\<Sum>k=1..n. f k) - g n) + norm (g n - g (Suc n))"
        by simp
      also have "\<dots> \<le> c1 * norm (h n) + c2 * norm (h n)"
        using n by (intro add_mono c1 c2) auto
      also have "\<dots> = (c1 + c2) * h n"
        using h_pos[of "real n"] n by (simp add: algebra_simps)
      finally show ?thesis .
    next
      assume mono: "mono_on g {1..}"
      have "(\<Sum>k=1..n. f k) - g x \<le> (\<Sum>k=1..n. f k) - g n"
        using x by (intro diff_mono mono_onD[OF mono]) (auto simp: n_def)
      also have "\<dots> \<le> c1 * h (real n)"
        using c1(2)[of n] n h_pos[of n] by simp
      also have "\<dots> \<le> (c1 + c2) * h (real n)"
        using c2 h_pos[of n] n by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    also have "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x"
      using mono_h
    proof
      assume mono: "mono_on (\<lambda>x. -h x) {1..}"
      have "(c1 + c2) * h (real n) \<le> (c1 + c2) * (c3 * h (real (Suc n)))"
        using c3(2)[of n] n h_pos[of n] h_pos[of "Suc n"] c1(1) c2(1)
        by (intro mult_left_mono) (auto)
      also have "\<dots> = (c1 + c2) * c3 * h (real (Suc n))"
        by (simp add: mult_ac)
      also have "\<dots> \<le> (c1 + c2) * (1 + c3) * h (real (Suc n))"
        using c1(1) c2(1) c3(1) h_pos[of "Suc n"] by (intro mult_left_mono mult_right_mono) auto
      also from x have "x \<le> real (Suc n)"
        unfolding n_def by linarith
      hence "(c1 + c2) * (1 + c3) * h (real (Suc n)) \<le> (c1 + c2) * (1 + c3) * h x"
        using c1(1) c2(1) c3(1) mono_onD[OF mono, of x "real (Suc n)"] x
        by (intro mult_left_mono) (auto simp: n_def)
      finally show "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x" .
    next
      assume mono: "mono_on h {1..}"
      have "(c1 + c2) * h (real n) = 1 * ((c1 + c2) * h (real n))" by simp
      also have "\<dots> \<le> (1 + c3) * ((c1 + c2) * h (real n))"
        using c1(1) c2(1) c3(1) h_pos[of n] x n by (intro mult_right_mono) auto
      also have "\<dots> = (1 + c3) * (c1 + c2) * h (real n)"
        by (simp add: mult_ac)
      also have "\<dots> \<le> (1 + c3) * (c1 + c2) * h x"
        using x c1(1) c2(1) c3(1) h_pos[of n] n
        by (intro mult_left_mono mono_onD[OF mono]) (auto simp: n_def)
      finally show "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x"
        by (simp add: mult_ac)
    qed
    also have "(\<Sum>k = 1..n. f k) = sum_upto f x"
      unfolding sum_upto_altdef n_def by (intro sum.cong) auto
    finally have "sum_upto f x - g x \<le> (c1 + c2) * (1 + c3) * h x" .
  }
  moreover have "(c1 + c2) * (1 + c3) > 0"
    using c1(1) c2(1) c3(1) by (intro mult_pos_pos add_pos_pos) auto
  ultimately show ?thesis by blast
qed

lemma sum_upto_asymptotics_lift_nat_real:
  fixes f :: "nat \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes bigo: "(\<lambda>n. (\<Sum>k=1..n. f k) - g (real n)) \<in> O(\<lambda>n. h (real n))"
  assumes g_bigo_self: "(\<lambda>n. g (real n) - g (real (Suc n))) \<in> O(\<lambda>n. h (real n))"
  assumes h_bigo_self: "(\<lambda>n. h (real n)) \<in> O(\<lambda>n. h (real (Suc n)))"
  assumes h_pos: "\<And>x. x \<ge> 1 \<Longrightarrow> h x > 0"
  assumes mono_g: "mono_on g {1..} \<or> mono_on (\<lambda>x. - g x) {1..}"
  assumes mono_h: "mono_on h {1..} \<or> mono_on (\<lambda>x. - h x) {1..}"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto f x - g x\<bar> \<le> c * h x"
proof -
  have "\<exists>c>0. \<forall>x\<ge>1. sum_upto f x - g x \<le> c * h x"
    by (intro sum_upto_asymptotics_lift_nat_real_aux assms)
  then obtain c1 where c1: "c1 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> sum_upto f x - g x \<le> c1 * h x"
    by auto

  have "(\<lambda>n. -(g (real n) - g (real (Suc n)))) \<in> O(\<lambda>n. h (real n))"
    by (subst landau_o.big.uminus_in_iff) fact
  also have "(\<lambda>n. -(g (real n) - g (real (Suc n)))) = (\<lambda>n. g (real (Suc n)) - g (real n))"
    by simp
  finally have "(\<lambda>n. g (real (Suc n)) - g (real n)) \<in> O(\<lambda>n. h (real n))" .
  moreover {
    have "(\<lambda>n. -((\<Sum>k=1..n. f k) - g (real n))) \<in> O(\<lambda>n. h (real n))"
      by (subst landau_o.big.uminus_in_iff) fact
    also have "(\<lambda>n. -((\<Sum>k=1..n. f k) - g (real n))) =
                 (\<lambda>n. (\<Sum>k=1..n. -f k) + g (real n))" by (simp add: sum_negf)
    finally have "(\<lambda>n. (\<Sum>k=1..n. - f k) + g (real n)) \<in> O(\<lambda>n. h (real n))" .
  }
  ultimately have "\<exists>c>0. \<forall>x\<ge>1. sum_upto (\<lambda>n. -f n) x - (-g x) \<le> c * h x" using mono_g
    by (intro sum_upto_asymptotics_lift_nat_real_aux assms) (simp_all add: disj_commute)
  then obtain c2 where c2: "c2 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> sum_upto (\<lambda>n. - f n) x + g x \<le> c2 * h x"
    by auto

  {
    fix x :: real assume x: "x \<ge> 1"
    have "sum_upto f x - g x \<le> max c1 c2 * h x"
      using h_pos[of x] x by (intro order.trans[OF c1(2)] mult_right_mono) auto
    moreover have "sum_upto (\<lambda>n. -f n) x + g x \<le> max c1 c2 * h x"
      using h_pos[of x] x by (intro order.trans[OF c2(2)] mult_right_mono) auto
    hence "-(sum_upto f x - g x) \<le> max c1 c2 * h x"
      by (simp add: sum_upto_def sum_negf)
    ultimately have "\<bar>sum_upto f x - g x\<bar> \<le> max c1 c2 * h x" by linarith
  }
  moreover from c1(1) c2(1) have "max c1 c2 > 0" by simp
  ultimately show ?thesis by blast
qed

lemma (in factorial_semiring) primepow_divisors_induct [case_names zero unit factor]:
  assumes "P 0" "\<And>x. is_unit x \<Longrightarrow> P x"
          "\<And>p k x. prime p \<Longrightarrow> k > 0 \<Longrightarrow> \<not>p dvd x \<Longrightarrow> P x \<Longrightarrow> P (p ^ k * x)"
  shows   "P x"
proof -
  have "finite (prime_factors x)" by simp
  thus ?thesis
  proof (induction "prime_factors x" arbitrary: x rule: finite_induct)
    case empty
    hence "prime_factors x = {}" by metis
    hence "prime_factorization x = {#}" by simp
    thus ?case using assms(1,2) by (auto simp: prime_factorization_empty_iff)
  next
    case (insert p A x)
    define k where "k = multiplicity p x"
    have "k > 0" using insert.hyps
      by (auto simp: prime_factors_multiplicity k_def)
    have p: "p \<in> prime_factors x" using insert.hyps by auto
    from p have "x \<noteq> 0" "\<not>is_unit p" by (auto simp: in_prime_factors_iff)

    from multiplicity_decompose'[OF this] obtain y where y: "x = p ^ k * y" "\<not>p dvd y"
      by (auto simp: k_def)
    have "prime_factorization x = replicate_mset k p + prime_factorization y"
      using p \<open>k > 0\<close> y unfolding y
      by (subst prime_factorization_mult)
         (auto simp: prime_factorization_prime_power in_prime_factors_iff)
    moreover from y p have "p \<notin> prime_factors y"
      by (auto simp: in_prime_factors_iff)
    ultimately have "prime_factors y = prime_factors x - {p}"
      by auto
    also have "\<dots> = A"
      using insert.hyps by auto
    finally have "P y" using insert by auto
    thus "P x"
      unfolding y using y \<open>k > 0\<close> p by (intro assms(3)) (auto simp: in_prime_factors_iff)
  qed
qed

end