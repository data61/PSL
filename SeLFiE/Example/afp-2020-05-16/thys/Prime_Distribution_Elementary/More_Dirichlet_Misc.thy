(*
  File:    More_Dirichlet_Misc.thy
  Author:  Manuel Eberl, TU München

  Generalised Dirichlet products and Legendre's identity, and a weighted sum
  of the Möbius \<mu> function
*)
section \<open>Miscellaneous material\<close>
theory More_Dirichlet_Misc
imports 
  Prime_Distribution_Elementary_Library
  Prime_Number_Theorem.Prime_Counting_Functions
begin

subsection \<open>Generalised Dirichlet products\<close>

(* TODO: Move to Dirichlet_Series *)

definition dirichlet_prod' :: "(nat \<Rightarrow> 'a :: comm_semiring_1) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a" where
  "dirichlet_prod' f g x = sum_upto (\<lambda>m. f m * g (x / real m)) x"

lemma dirichlet_prod'_one_left:
  "dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x = (if x \<ge> 1 then f x else 0)"
proof -
  have  "dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x =
           (\<Sum>i | 0 < i \<and> real i \<le> x. (if i = Suc 0 then 1 else 0) * f (x / real i))"
    by (simp add: dirichlet_prod'_def sum_upto_def)
  also have "\<dots> = (\<Sum>i\<in>(if x \<ge> 1 then {1::nat} else {}). f x)"
    by (intro sum.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = (if x \<ge> 1 then f x else 0)"
    by simp
  finally show ?thesis .
qed

lemma dirichlet_prod'_cong:
  assumes "\<And>n. n > 0 \<Longrightarrow> real n \<le> x \<Longrightarrow> f n = f' n"
  assumes "\<And>y. y \<ge> 1 \<Longrightarrow> y \<le> x \<Longrightarrow> g y = g' y"
  assumes "x = x'"
  shows   "dirichlet_prod' f g x = dirichlet_prod' f' g' x'"
  unfolding dirichlet_prod'_def 
  by (intro sum_upto_cong' assms, (subst assms | simp add: assms field_simps)+)

(* 2.21 *)
lemma dirichlet_prod'_assoc:
  "dirichlet_prod' f (\<lambda>y. dirichlet_prod' g h y) x = dirichlet_prod' (dirichlet_prod f g) h x"
proof -
  have "dirichlet_prod' f (\<lambda>y. dirichlet_prod' g h y) x =
          (\<Sum>m | m > 0 \<and> real m \<le> x. \<Sum>n | n > 0 \<and> real n \<le> x / m. f m * g n * h (x / (m * n)))"
    by (simp add: algebra_simps dirichlet_prod'_def dirichlet_prod_def
                  sum_upto_def sum_distrib_left sum_distrib_right)
  also have "\<dots> = (\<Sum>(m,n)\<in>(SIGMA m:{m. m > 0 \<and> real m \<le> x}. {n. n > 0 \<and> real n \<le> x / m}).
                     f m * g n * h (x / (m * n)))"
    by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>(mn, m)\<in>(SIGMA mn:{mn. mn > 0 \<and> real mn \<le> x}. {m. m dvd mn}).
                    f m * g (mn div m) * h (x / mn))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(mn, m). (m, mn div m)" "\<lambda>(m, n). (m * n, m)"])
       (auto simp: case_prod_unfold field_simps dest: dvd_imp_le)
  also have "\<dots> = dirichlet_prod' (dirichlet_prod f g) h x"
    by (subst sum.Sigma [symmetric])
       (simp_all add: dirichlet_prod'_def dirichlet_prod_def sum_upto_def
                      algebra_simps sum_distrib_left sum_distrib_right)
  finally show ?thesis .
qed

(* 2.22 *)
lemma dirichlet_prod'_inversion1:
  assumes "\<forall>x\<ge>1. g x = dirichlet_prod' a f x" "x \<ge> 1"
          "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "f x = dirichlet_prod' ainv g x"
proof -
  have "dirichlet_prod' ainv g x = dirichlet_prod' ainv (dirichlet_prod' a f) x"
    using assms by (intro dirichlet_prod'_cong) auto
  also have "\<dots> = dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) f x"
    using assms by (simp add: dirichlet_prod'_assoc dirichlet_prod_commutes)
  also have "\<dots> = f x"
    using assms by (subst dirichlet_prod'_one_left) auto
  finally show ?thesis ..
qed

lemma dirichlet_prod'_inversion2:
  assumes "\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x" "x \<ge> 1"
          "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "g x = dirichlet_prod' a f x"
proof -
  have "dirichlet_prod' a f x = dirichlet_prod' a (dirichlet_prod' ainv g) x"
    using assms by (intro dirichlet_prod'_cong) auto
  also have "\<dots> = dirichlet_prod' (\<lambda>n. if n = 1 then 1 else 0) g x"
    using assms by (simp add: dirichlet_prod'_assoc dirichlet_prod_commutes)
  also have "\<dots> = g x"
    using assms by (subst dirichlet_prod'_one_left) auto
  finally show ?thesis ..
qed

lemma dirichlet_prod'_inversion:
  assumes "dirichlet_prod a ainv = (\<lambda>n. if n = 1 then 1 else 0)"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow> (\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x)"
  using dirichlet_prod'_inversion1[of g a f _ ainv] dirichlet_prod'_inversion2[of f ainv g _ a]
        assms by blast

lemma dirichlet_prod'_inversion':
  assumes "a 1 * y = 1"
  defines "ainv \<equiv> dirichlet_inverse a y"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow> (\<forall>x\<ge>1. f x = dirichlet_prod' ainv g x)"
  unfolding ainv_def
  by (intro dirichlet_prod'_inversion dirichlet_prod_inverse assms)

(* 3.11 *)
lemma dirichlet_prod'_floor_conv_sum_upto:
  "dirichlet_prod' f (\<lambda>x. real_of_int (floor x)) x = sum_upto (\<lambda>n. sum_upto f (x / n)) x"
proof -
  have [simp]: "sum_upto (\<lambda>_. 1 :: real) x = real (nat \<lfloor>x\<rfloor>)" for x
    by (simp add: sum_upto_altdef)
  show ?thesis
    using sum_upto_dirichlet_prod[of "\<lambda>n. 1::real" f] sum_upto_dirichlet_prod[of f "\<lambda>n. 1::real"]
    by (simp add: dirichlet_prod'_def dirichlet_prod_commutes)
qed

lemma (in completely_multiplicative_function) dirichlet_prod_self:
  "dirichlet_prod f f n = f n * of_nat (divisor_count n)"
proof (cases "n = 0")
  case False
  have "dirichlet_prod f f n = (\<Sum>(r, d) | r * d = n. f (r * d))"
    by (simp add: dirichlet_prod_altdef2 mult)
  also have "\<dots> = (\<Sum>(r, d) | r * d = n. f n)"
    by (intro sum.cong) auto
  also have "\<dots> = f n * of_nat (card {(r, d). r * d = n})"
    by (simp add: mult.commute)
  also have "bij_betw fst {(r, d). r * d = n} {r. r dvd n}"
    by (rule bij_betwI[of _ _ _ "\<lambda>r. (r, n div r)"]) (use False in auto)
  hence "card {(r, d). r * d = n} = card {r. r dvd n}"
    by (rule bij_betw_same_card)
  also have "\<dots> = divisor_count n"
    by (simp add: divisor_count_def)
  finally show ?thesis .
qed auto

lemma completely_multiplicative_imp_moebius_mu_inverse:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "completely_multiplicative_function f"
  shows   "dirichlet_prod f (\<lambda>n. moebius_mu n * f n) n = (if n = 1 then 1 else 0)"
proof -
  interpret completely_multiplicative_function f by fact
  have [simp]: "fds f \<noteq> 0" by (auto simp: fds_eq_iff)
  have "dirichlet_prod f (\<lambda>n. moebius_mu n * f n) n =
          (\<Sum>(r, d) | r * d = n. moebius_mu r * f (r * d))"
    by (subst dirichlet_prod_commutes)
       (simp add: fds_eq_iff fds_nth_mult fds_nth_fds dirichlet_prod_altdef2 mult_ac mult)
  also have "\<dots> = (\<Sum>(r, d) | r * d = n. moebius_mu r * f n)"
    by (intro sum.cong) auto
  also have "\<dots> = dirichlet_prod moebius_mu (\<lambda>_. 1) n * f n"
    by (simp add: dirichlet_prod_altdef2 sum_distrib_right case_prod_unfold mult)
  also have "dirichlet_prod moebius_mu (\<lambda>_. 1) n = fds_nth (fds moebius_mu * fds_zeta) n"
    by (simp add: fds_nth_mult)
  also have "fds moebius_mu * fds_zeta = 1"
    by (simp add: mult_ac fds_zeta_times_moebius_mu)
  also have "fds_nth 1 n * f n = fds_nth 1 n"
    by (auto simp: fds_eq_iff fds_nth_one)
  finally show ?thesis by (simp add: fds_nth_one)
qed

(* 2.23 *)
lemma dirichlet_prod_inversion_completely_multiplicative:
  fixes a :: "nat \<Rightarrow> 'a :: comm_ring_1"
  assumes "completely_multiplicative_function a"
  shows   "(\<forall>x\<ge>1. g x = dirichlet_prod' a f x) \<longleftrightarrow>
             (\<forall>x\<ge>1. f x = dirichlet_prod' (\<lambda>n. moebius_mu n * a n) g x)"
  by (intro dirichlet_prod'_inversion ext completely_multiplicative_imp_moebius_mu_inverse assms)

lemma divisor_sigma_conv_dirichlet_prod:
  "divisor_sigma x n = dirichlet_prod (\<lambda>n. real n powr x) (\<lambda>_. 1) n"
proof (cases "n = 0")
  case False
  have "fds (divisor_sigma x) = fds_shift x fds_zeta * fds_zeta"
    using fds_divisor_sigma[of x] by (simp add: mult_ac)
  thus ?thesis using False by (auto simp: fds_eq_iff fds_nth_mult)
qed simp_all


subsection \<open>Legendre's identity\<close>

definition legendre_aux :: "real \<Rightarrow> nat \<Rightarrow> nat" where
  "legendre_aux x p = (if prime p then (\<Sum>m | m > 0 \<and> real (p ^ m) \<le> x. nat \<lfloor>x / p ^ m\<rfloor>) else 0)"

lemma legendre_aux_not_prime [simp]: "\<not>prime p \<Longrightarrow> legendre_aux x p = 0"
  by (simp add: legendre_aux_def)

lemma legendre_aux_eq_0:
  assumes "real p > x"
  shows   "legendre_aux x p = 0"
proof (cases "prime p")
  case True
  have [simp]: "\<not>real p ^ m \<le> x" if "m > 0" for m
  proof -
    have "x < real p ^ 1" using assms by simp
    also have "\<dots> \<le> real p ^ m"
      using prime_gt_1_nat[OF True] that by (intro power_increasing) auto
    finally show ?thesis by auto
  qed
  from assms have *: "{m. m > 0 \<and> real (p ^ m) \<le> x} = {}"
    using prime_gt_1_nat[OF True] by auto
  show ?thesis unfolding legendre_aux_def
    by (subst *) auto
qed (auto simp: legendre_aux_def)

lemma legendre_aux_posD:
  assumes "legendre_aux x p > 0"
  shows   "prime p" "real p \<le> x"
proof -
  show "real p \<le> x" using legendre_aux_eq_0[of x p] assms
    by (cases "real p \<le> x") auto
qed (use assms in \<open>auto simp: legendre_aux_def split: if_splits\<close>)

lemma exponents_le_finite:
  assumes "p > (1 :: nat)" "k > 0"
  shows   "finite {i. real (p ^ (k * i + l)) \<le> x}"
proof (rule finite_subset)
  show "{i. real (p ^ (k * i + l)) \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
  proof safe
    fix i assume i: "real (p ^ (k * i + l)) \<le> x"
    have "i < 2 ^ i" by (induction i) auto
    also from assms have "i \<le> k * i + l" by (cases k) auto
    hence "2 ^ i \<le> (2 ^ (k * i + l) :: nat)"
      using assms by (intro power_increasing) auto
    also have "\<dots> \<le> p ^ (k * i + l)" using assms by (intro power_mono) auto
    also have "real \<dots> \<le> x" using i by simp
    finally show "i \<le> nat \<lfloor>x\<rfloor>" by linarith
  qed
qed auto

lemma finite_sum_legendre_aux: 
  assumes "prime p"
  shows   "finite {m. m > 0 \<and> real (p ^ m) \<le> x}"
  by (rule finite_subset[OF _ exponents_le_finite[where k = 1 and l = 0 and p = p]])
     (use assms prime_gt_1_nat[of p] in auto)

lemma legendre_aux_set_eq:
  assumes "prime p" "x \<ge> 1"
  shows   "{m. m > 0 \<and> real (p ^ m) \<le> x} = {0<..nat \<lfloor>log (real p) x\<rfloor>}"
  using prime_gt_1_nat[OF assms(1)] assms
  by (auto simp: le_nat_iff le_log_iff le_floor_iff powr_realpow)

lemma legendre_aux_altdef1:
  "legendre_aux x p = (if prime p \<and> x \<ge> 1 then
                         (\<Sum>m\<in>{0<..nat \<lfloor>log (real p) x\<rfloor>}. nat \<lfloor>x / p ^ m\<rfloor>) else 0)"
proof (cases "prime p \<and> x < 1")
  case False
  thus ?thesis using legendre_aux_set_eq[of p x] by (auto simp: legendre_aux_def)
next
  case True
  have [simp]: "\<not>(real p ^ m \<le> x)" for m
  proof -
    have "x < real 1" using True by simp
    also have "real 1 \<le> real (p ^ m)"
      unfolding of_nat_le_iff by (intro one_le_power) (use prime_gt_1_nat[of p] True in auto)
    finally show "\<not>(real p ^ m \<le> x)" by auto
  qed
  have "{m. m > 0 \<and> real (p ^ m) \<le> x} = {}" by simp
  with True show ?thesis by (simp add: legendre_aux_def)
qed

lemma legendre_aux_altdef2:
  assumes "x \<ge> 1" "prime p" "real p ^ Suc k > x"
  shows   "legendre_aux x p = (\<Sum>m\<in>{0<..k}. nat \<lfloor>x / p ^ m\<rfloor>)"
proof -
  have "legendre_aux x p = (\<Sum>m | m > 0 \<and> real (p ^ m) \<le> x. nat \<lfloor>x / p ^ m\<rfloor>)"
    using assms by (simp add: legendre_aux_def)
  also have "\<dots> = (\<Sum>m\<in>{0<..k}. nat \<lfloor>x / p ^ m\<rfloor>)"
  proof (intro sum.mono_neutral_left)
    show "{m. 0 < m \<and> real (p ^ m) \<le> x} \<subseteq> {0<..k}"
    proof safe
      fix m assume "m > 0" "real (p ^ m) \<le> x"
      hence "real p ^ m \<le> x" by simp
      also note \<open>x < real p ^ Suc k\<close>
      finally show "m \<in> {0<..k}" using \<open>m > 0\<close>
        using prime_gt_1_nat[OF \<open>prime p\<close>] by (subst (asm) power_strict_increasing_iff) auto
    qed
  qed (use prime_gt_0_nat[of p] assms in \<open>auto simp: field_simps\<close>)
  finally show ?thesis .
qed

(* 3.14 *)
theorem legendre_identity:
  "sum_upto ln x = prime_sum_upto (\<lambda>p. legendre_aux x p * ln p) x"
proof -
  define S where "S = (SIGMA p:{p. prime p \<and> real p \<le> x}. {i. i > 0 \<and> real (p ^ i) \<le> x})"

  have prime_power_leD: "real p \<le> x" if "real p ^ i \<le> x" "prime p" "i > 0" for p i
  proof -
    have "real p ^ 1 \<le> real p ^ i"
      using that prime_gt_1_nat[of p] by (intro power_increasing) auto
    also have "\<dots> \<le> x" by fact
    finally show "real p \<le> x" by simp
  qed

  have "sum_upto ln x = sum_upto (\<lambda>n. mangoldt n * real (nat \<lfloor>x / real n\<rfloor>)) x"
    by (rule sum_upto_ln_conv_sum_upto_mangoldt)
  also have "\<dots> = (\<Sum>(p, i) | prime p \<and> 0 < i \<and> real (p ^ i) \<le> x.
                     ln p * real (nat \<lfloor>x / real (p ^ i)\<rfloor>))"
    by (subst sum_upto_primepows[where g = "\<lambda>p i. ln p * real (nat \<lfloor>x / real (p ^ i)\<rfloor>)"])
       (auto simp: mangoldt_non_primepow)
  also have "\<dots> = (\<Sum>(p,i)\<in>S. ln p * real (nat \<lfloor>x / p ^ i\<rfloor>))"
    using prime_power_leD by (intro sum.cong refl) (auto simp: S_def)
  also have "\<dots> = (\<Sum>p | prime p \<and> real p \<le> x. \<Sum>i | i > 0 \<and> real (p ^ i) \<le> x.
                     ln p * real (nat \<lfloor>x / p ^ i\<rfloor>))"
  proof (unfold S_def, subst sum.Sigma)
    have "{p. prime p \<and> real p \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
      by (auto simp: le_nat_iff le_floor_iff)
    thus "finite {p. prime p \<and> real p \<le> x}"
      by (rule finite_subset) auto
  next
    show "\<forall>p\<in>{p. prime p \<and> real p \<le> x}. finite {i. 0 < i \<and> real (p ^ i) \<le> x}"
      by (intro ballI finite_sum_legendre_aux) auto
  qed auto
  also have "\<dots> = (\<Sum>p | prime p \<and> real p \<le> x. ln p *
                    real (\<Sum>i | i > 0 \<and> real (p ^ i) \<le> x. (nat \<lfloor>x / p ^ i\<rfloor>)))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>p | prime p \<and> real p \<le> x. ln p * real (legendre_aux x p))"
    by (intro sum.cong refl) (auto simp: legendre_aux_def)
  also have "\<dots> = prime_sum_upto (\<lambda>p. ln p * real (legendre_aux x p)) x"
    by (simp add: prime_sum_upto_def)
  finally show ?thesis by (simp add: mult_ac)
qed

lemma legendre_identity':
  "fact (nat \<lfloor>x\<rfloor>) = (\<Prod>p | prime p \<and> real p \<le> x. p ^ legendre_aux x p)"
proof -
  have fin: "finite {p. prime p \<and> real p \<le> x}"
    by (rule finite_subset[of _ "{..nat \<lfloor>x\<rfloor>}"]) (auto simp: le_nat_iff le_floor_iff)
  have "real (fact (nat \<lfloor>x\<rfloor>)) = exp (sum_upto ln x)"
    by (subst sum_upto_ln_conv_ln_fact) auto
  also have "sum_upto ln x = prime_sum_upto (\<lambda>p. legendre_aux x p * ln p) x"
    by (rule legendre_identity)
  also have "exp \<dots> = (\<Prod>p | prime p \<and> real p \<le> x. exp (ln (real p) * legendre_aux x p))"
    unfolding prime_sum_upto_def using fin by (subst exp_sum) (auto simp: mult_ac)
  also have "\<dots> = (\<Prod>p | prime p \<and> real p \<le> x. real (p ^ legendre_aux x p))"
  proof (intro prod.cong refl)
    fix p assume "p \<in> {p. prime p \<and> real p \<le> x}"
    hence "p > 0" using prime_gt_0_nat[of p] by auto
    from \<open>p > 0\<close> have "exp (ln (real p) * legendre_aux x p) = real p powr real (legendre_aux x p)"
      by (simp add: powr_def)
    also from \<open>p > 0\<close> have "\<dots> = real (p ^ legendre_aux x p)"
      by (subst powr_realpow) auto
    finally show "exp (ln (real p) * legendre_aux x p) = \<dots>" .
  qed
  also have "\<dots> = real (\<Prod>p | prime p \<and> real p \<le> x. p ^ legendre_aux x p)"
    by simp
  finally show ?thesis unfolding of_nat_eq_iff .
qed


subsection \<open>A weighted sum of the Möbius \<open>\<mu>\<close> function\<close>

(* TODO: Move to Dirichlet_Series? *)

(* 3.13 *)
context
  fixes M :: "real \<Rightarrow> real"
  defines "M \<equiv> (\<lambda>x. sum_upto (\<lambda>n. moebius_mu n / n) x)"
begin

lemma abs_sum_upto_moebius_mu_over_n_less:
  assumes x: "x \<ge> 2"
  shows   "\<bar>M x\<bar> < 1"
proof -
  have "x * sum_upto (\<lambda>n. moebius_mu n / n) x - sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x =
          sum_upto (\<lambda>n. moebius_mu n * (x / n - frac (x / n))) x"
    by (subst mult.commute[of x])
       (simp add: sum_upto_def sum_distrib_right sum_subtractf ring_distribs)
  also have "(\<lambda>n. x / real n - frac (x / real n)) = (\<lambda>n. of_int (floor (x / real n)))"
    by (simp add: frac_def)
  also have "sum_upto (\<lambda>n. moebius_mu n * real_of_int \<lfloor>x / real n\<rfloor>) x =
               real_of_int (sum_upto (\<lambda>n. moebius_mu n * \<lfloor>x / real n\<rfloor>) x)"
    by (simp add: sum_upto_def)
  also have "\<dots> = 1"
    using x by (subst sum_upto_moebius_times_floor_linear) auto
  finally have eq: "x * M x = 1 + sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x"
    by (simp add: M_def)

  have "x * \<bar>M x\<bar> = \<bar>x * M x\<bar>"
    using x by (simp add: abs_mult)
  also note eq
  also have "\<bar>1 + sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar> \<le>
               1 + \<bar>sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar>"
    by linarith
  also have "\<bar>sum_upto (\<lambda>n. moebius_mu n * frac (x / n)) x\<bar> \<le>
               sum_upto (\<lambda>n. \<bar>moebius_mu n * frac (x / n)\<bar>) x"
    unfolding sum_upto_def by (rule sum_abs)
  also have "\<dots> \<le> sum_upto (\<lambda>n. frac (x / n)) x"
    unfolding sum_upto_def by (intro sum_mono) (auto simp: moebius_mu_def abs_mult)
  also have "\<dots> = (\<Sum>n\<in>{0<..nat \<lfloor>x\<rfloor>}. frac (x / n))"
    by (simp add: sum_upto_altdef)
  also have "{0<..nat \<lfloor>x\<rfloor>} = insert 1 {1<..nat \<lfloor>x\<rfloor>}"
    using x by (auto simp: le_nat_iff le_floor_iff)
  also have "(\<Sum>n\<in>\<dots>. frac (x / n)) = frac x + (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. frac (x / n))"
    by (subst sum.insert) auto
  also have "(\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. frac (x / n)) < (\<Sum>n\<in>{1<..nat \<lfloor>x\<rfloor>}. 1)"
    using x by (intro sum_strict_mono frac_lt_1) auto
  also have "\<dots> = nat \<lfloor>x\<rfloor> - 1" by simp
  also have "1 + (frac x + real (nat \<lfloor>x\<rfloor> - 1)) = x"
    using x by (subst of_nat_diff) (auto simp: le_nat_iff le_floor_iff frac_def)
  finally have "x * \<bar>M x\<bar> < x * 1" by simp
  with x show "\<bar>M x\<bar> < 1"
    by (subst (asm) mult_less_cancel_left_pos) auto
qed 

lemma sum_upto_moebius_mu_over_n_eq:
  assumes "x < 2"
  shows   "M x = (if x \<ge> 1 then 1 else 0)"
proof (cases "x \<ge> 1")
  case True
  have "M x = (\<Sum>n\<in>{n. n > 0 \<and> real n \<le> x}. moebius_mu n / n)"
    by (simp add: M_def sum_upto_def)
  also from assms True have "{n. n > 0 \<and> real n \<le> x} = {1}"
    by auto
  thus ?thesis using True by (simp add: M_def sum_upto_def)
next
  case False
  have "M x = (\<Sum>n\<in>{n. n > 0 \<and> real n \<le> x}. moebius_mu n / n)"
    by (simp add: M_def sum_upto_def)
  also from False have "{n. n > 0 \<and> real n \<le> x} = {}"
    by auto
  finally show ?thesis using False by (simp add: M_def)
qed

lemma abs_sum_upto_moebius_mu_over_n_le: "\<bar>M x\<bar> \<le> 1"
  using sum_upto_moebius_mu_over_n_eq[of x] abs_sum_upto_moebius_mu_over_n_less[of x]
  by (cases "x < 2") auto

end

end