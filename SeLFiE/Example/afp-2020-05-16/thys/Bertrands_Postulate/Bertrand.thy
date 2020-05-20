(*
  File:     Bertrand.thy
  Authors:  Julian Biendarra, Manuel Eberl <eberlm@in.tum.de>, Larry Paulson

  A proof of Bertrand's postulate (based on John Harrison's HOL Light proof).
  Uses reflection and the approximation tactic.
*)
theory Bertrand
  imports 
    Complex_Main
    "HOL-Number_Theory.Number_Theory"
    "HOL-Library.Discrete"
    "HOL-Decision_Procs.Approximation_Bounds"
    "HOL-Library.Code_Target_Numeral"
    Pratt_Certificate.Pratt_Certificate
begin

subsection \<open>Auxiliary facts\<close>
 
lemma ln_2_le: "ln 2 \<le> 355 / (512 :: real)"
proof -
  have "ln 2 \<le> real_of_float (ub_ln2 12)" by (rule ub_ln2)
  also have "ub_ln2 12 = Float 5680 (- 13)" by code_simp
  finally show ?thesis by simp
qed

lemma ln_2_ge: "ln 2 \<ge> (5677 / 8192 :: real)"
proof -
  have "ln 2 \<ge> real_of_float (lb_ln2 12)" by (rule lb_ln2)
  also have "lb_ln2 12 = Float 5677 (-13)" by code_simp
  finally show ?thesis by simp
qed

lemma ln_2_ge': "ln (2 :: real) \<ge> 2/3" and ln_2_le': "ln (2 :: real) \<le> 16/23"
  using ln_2_le ln_2_ge by simp_all

lemma of_nat_ge_1_iff: "(of_nat x :: 'a :: linordered_semidom) \<ge> 1 \<longleftrightarrow> x \<ge> 1"
  using of_nat_le_iff[of 1 x] by (subst (asm) of_nat_1)
  
lemma floor_conv_div_nat:
  "of_int (floor (real m / real n)) = real (m div n)"
  by (subst floor_divide_of_nat_eq) simp

lemma frac_conv_mod_nat:
  "frac (real m / real n) = real (m mod n) / real n"
  by (cases "n = 0")
     (simp_all add: frac_def floor_conv_div_nat field_simps of_nat_mult 
        [symmetric] of_nat_add [symmetric] del: of_nat_mult of_nat_add)

lemma of_nat_prod_mset: "prod_mset (image_mset of_nat A) = of_nat (prod_mset A)"
  by (induction A) simp_all

lemma prod_mset_pos: "(\<And>x :: 'a :: linordered_semidom. x \<in># A \<Longrightarrow> x > 0) \<Longrightarrow> prod_mset A > 0"
  by (induction A) simp_all

lemma ln_msetprod:
  assumes "\<And>x. x \<in>#I \<Longrightarrow> x > 0"
  shows "(\<Sum>p::nat\<in>#I. ln p) = ln (\<Prod>p\<in>#I. p)"
  using assms by (induction I) (simp_all add: of_nat_prod_mset ln_mult prod_mset_pos)

lemma ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)"
  by (induction n) (simp_all add: ln_mult)

lemma overpower_lemma:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f a \<le> g a"
  assumes "\<And>x. a \<le> x \<Longrightarrow> ((\<lambda>x. g x - f x) has_real_derivative (d x)) (at x)"
  assumes "\<And>x. a \<le> x \<Longrightarrow> d x \<ge> 0"
  assumes "a \<le> x"
  shows   "f x \<le> g x"
proof (cases "a < x")
  case True
  with assms have "\<exists>z. z > a \<and> z < x \<and> g x - f x - (g a - f a) = (x - a) * d z"
    by (intro MVT2) auto
  then obtain z where z: "z > a" "z < x" "g x - f x - (g a - f a) = (x - a) * d z" by blast
  hence "f x = g x + (f a - g a) + (a - x) * d z" by (simp add: algebra_simps)
  also from assms have "f a - g a \<le> 0" by (simp add: algebra_simps)
  also from assms z have "(a - x) * d z \<le> 0 * d z"
    by (intro mult_right_mono) simp_all
  finally show ?thesis by simp
qed (insert assms, auto)


subsection \<open>Preliminary definitions\<close>

definition primepow_even :: "nat \<Rightarrow> bool" where
  "primepow_even q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k))"

definition primepow_odd :: "nat \<Rightarrow> bool" where
  "primepow_odd q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k+1))"

abbreviation (input) isprimedivisor :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isprimedivisor q p \<equiv> prime p \<and> p dvd q"

definition pre_mangoldt :: "nat \<Rightarrow> nat" where
  "pre_mangoldt d = (if primepow d then aprimedivisor d else 1)"

definition mangoldt_even :: "nat \<Rightarrow> real" where
  "mangoldt_even d = (if primepow_even d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_odd :: "nat \<Rightarrow> real" where
  "mangoldt_odd d = (if primepow_odd d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_1 :: "nat \<Rightarrow> real" where
  "mangoldt_1 d = (if prime d then ln d else 0)"

definition psi :: "nat \<Rightarrow> real" where
  "psi n = (\<Sum>d=1..n. mangoldt d)"

definition psi_even :: "nat \<Rightarrow> real" where
  "psi_even n = (\<Sum>d=1..n. mangoldt_even d)"

definition psi_odd :: "nat \<Rightarrow> real" where
  "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"

abbreviation (input) psi_even_2 :: "nat \<Rightarrow> real" where
  "psi_even_2 n \<equiv> (\<Sum>d=2..n. mangoldt_even d)"

abbreviation (input) psi_odd_2 :: "nat \<Rightarrow> real" where
  "psi_odd_2 n \<equiv> (\<Sum>d=2..n. mangoldt_odd d)"

definition theta :: "nat \<Rightarrow> real" where
  "theta n = (\<Sum>p=1..n. if prime p then ln (real p) else 0)"

subsection \<open>Properties of prime powers\<close>  

lemma primepow_even_imp_primepow:
  assumes "primepow_even n"
  shows   "primepow n"
proof -
  from assms obtain p k where "1 \<le> k" "prime p" "n = p ^ (2 * k)"
    unfolding primepow_even_def by blast
  moreover from \<open>1 \<le> k\<close> have "2 * k > 0"
    by simp
  ultimately show ?thesis unfolding primepow_def by blast
qed

lemma primepow_odd_imp_primepow:
  assumes "primepow_odd n"
  shows   "primepow n"
proof -
 from assms obtain p k where "1 \<le> k" "prime p" "n = p ^ (2 * k + 1)"
   unfolding primepow_odd_def by blast
  moreover from \<open>1 \<le> k\<close> have "Suc (2 * k) > 0"
    by simp
  ultimately show ?thesis unfolding primepow_def
    by (auto simp del: power_Suc)
qed

lemma primepow_odd_altdef:
  "primepow_odd n \<longleftrightarrow>
     primepow n \<and> odd (multiplicity (aprimedivisor n) n) \<and> multiplicity (aprimedivisor n) n > 1"
proof (intro iffI conjI; (elim conjE)?)
  assume "primepow_odd n"
  then obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ (2 * k + 1)"
    by (auto simp: primepow_odd_def)
  thus "odd (multiplicity (aprimedivisor n) n)" "multiplicity (aprimedivisor n) n > 1"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
next
  assume A: "primepow n" and B: "odd (multiplicity (aprimedivisor n) n)"
     and C: "multiplicity (aprimedivisor n) n > 1"
  from A obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ k"
    by (auto simp: primepow_def Suc_le_eq)
  with B C have "odd k" "k > 1"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
  then obtain j where j: "k = 2 * j + 1" "j > 0" by (auto elim!: oddE)
  with n show "primepow_odd n" by (auto simp: primepow_odd_def intro!: exI[of _ p, OF exI[of _ j]])
qed (auto dest: primepow_odd_imp_primepow)

lemma primepow_even_altdef:
  "primepow_even n \<longleftrightarrow> primepow n \<and> even (multiplicity (aprimedivisor n) n)"
proof (intro iffI conjI; (elim conjE)?)
  assume "primepow_even n"
  then obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ (2 * k)"
    by (auto simp: primepow_even_def)
  thus "even (multiplicity (aprimedivisor n) n)"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
next
  assume A: "primepow n" and B: "even (multiplicity (aprimedivisor n) n)"
  from A obtain p k where n: "k \<ge> 1" "prime p" "n = p ^ k"
    by (auto simp: primepow_def Suc_le_eq)
  with B have "even k"
    by (simp_all add: aprimedivisor_primepow prime_elem_multiplicity_mult_distrib)
  then obtain j where j: "k = 2 * j" by (auto elim!: evenE)
  from j n have "j \<noteq> 0" by (intro notI) simp_all
  with j n show "primepow_even n"
    by (auto simp: primepow_even_def intro!: exI[of _ p, OF exI[of _ j]])
qed (auto dest: primepow_even_imp_primepow)

lemma primepow_odd_mult:
  assumes "d > Suc 0"
  shows   "primepow_odd (aprimedivisor d * d) \<longleftrightarrow> primepow_even d"
    using assms
    by (auto simp: primepow_odd_altdef primepow_even_altdef primepow_mult_aprimedivisorI
                   aprimedivisor_primepow prime_aprimedivisor' aprimedivisor_dvd'
                   prime_elem_multiplicity_mult_distrib prime_elem_aprimedivisor_nat
             dest!: primepow_multD)

lemma pre_mangoldt_primepow:
  assumes "primepow n" "aprimedivisor n = p"
  shows   "pre_mangoldt n = p"
  using assms by (simp add: pre_mangoldt_def)

lemma pre_mangoldt_notprimepow:
  assumes "\<not>primepow n"
  shows   "pre_mangoldt n = 1"
  using assms by (simp add: pre_mangoldt_def)

lemma primepow_cases:
  "primepow d \<longleftrightarrow>
     (  primepow_even d \<and> \<not> primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and>   primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and> \<not> primepow_odd d \<and>   prime d)"
  by (auto simp: primepow_even_altdef primepow_odd_altdef multiplicity_aprimedivisor_Suc_0_iff
           elim!: oddE intro!: Nat.gr0I)


subsection \<open>Deriving a recurrence for the psi function\<close>
  
lemma ln_fact_bounds:
  assumes "n > 0"
  shows "abs(ln (fact n) - n * ln n + n) \<le> 1 + ln n"
proof -
  have "\<forall>n\<in>{0<..}. \<exists>z>real n. z < real (n + 1) \<and> real (n + 1) * ln (real (n + 1)) - 
          real n * ln (real n) = (real (n + 1) - real n) * (ln z + 1)"
    by (intro ballI MVT2) (auto intro!: derivative_eq_intros)
  hence "\<forall>n\<in>{0<..}. \<exists>z>real n. z < real (n + 1) \<and> real (n + 1) * ln (real (n + 1)) - 
          real n * ln (real n) = (ln z + 1)" by (simp add: algebra_simps)
  from bchoice[OF this] obtain k :: "nat \<Rightarrow> real"
    where lb: "real n < k n" and ub: "k n < real (n + 1)" and 
          mvt: "real (n+1) * ln (real (n+1)) - real n * ln (real n) = ln (k n) + 1" 
          if "n > 0" for n::nat by blast
  have *: "(n + 1) * ln (n + 1) = (\<Sum>i=1..n. ln(k i) + 1)" for n::nat
  proof (induction n)
    case (Suc n)
    have "(\<Sum>i = 1..n+1. ln (k i) + 1) = (\<Sum>i = 1..n. ln (k i) + 1) + ln (k (n+1)) + 1"
      by simp
    also from Suc.IH have "(\<Sum>i = 1..n. ln (k i) + 1) = real (n+1) * ln (real (n+1))" ..
    also from mvt[of "n+1"] have "\<dots> = real (n+2) * ln (real (n+2)) - ln (k (n+1)) - 1"
      by simp
    finally show ?case
      by simp
  qed simp
  have **: "abs((\<Sum>i=1..n+1. ln i) - ((n+1) * ln (n+1) - (n+1))) \<le> 1 + ln(n+1)" for n::nat
  proof -
    have "(\<Sum>i=1..n+1. ln i) \<le> (\<Sum>i=1..n. ln i) + ln (n+1)"
      by simp
    also have "(\<Sum>i=1..n. ln i) \<le> (\<Sum>i=1..n. ln (k i))"
      by (intro sum_mono, subst ln_le_cancel_iff) (auto simp: Suc_le_eq dest: lb ub)
    also have "\<dots> = (\<Sum>i=1..n. ln (k i) + 1) - n"
      by (simp add: sum.distrib)
    also from * have "\<dots> = (n+1) * ln (n+1) - n"
      by simp
    finally have a_minus_b: "(\<Sum>i=1..n+1. ln i) - ((n+1) * ln (n+1) - (n+1)) \<le> 1 + ln (n+1)"
      by simp

    from * have "(n+1) * ln (n+1) - n = (\<Sum>i=1..n. ln (k i) + 1) - n"
      by simp
    also have "\<dots> = (\<Sum>i=1..n. ln (k i))"
      by (simp add: sum.distrib)
    also have "\<dots> \<le> (\<Sum>i=1..n. ln (i+1))"
      by (intro sum_mono, subst ln_le_cancel_iff) (auto simp: Suc_le_eq dest: lb ub)
    also from sum.shift_bounds_cl_nat_ivl[of "ln" 1 1 n] have "\<dots> = (\<Sum>i=1+1..n+1. ln i)" ..
    also have "\<dots> = (\<Sum>i=1..n+1. ln i)"
      by (rule sum.mono_neutral_left) auto
    finally have b_minus_a: "((n+1) * ln (n+1) - (n+1)) - (\<Sum>i=1..n+1. ln i) \<le> 1"
      by simp
    have "0 \<le> ln (n+1)"
      by simp
    with b_minus_a have "((n+1) * ln (n+1) - (n+1)) - (\<Sum>i=1..n+1. ln i) \<le> 1 + ln (n+1)"
      by linarith
    with a_minus_b show ?thesis
      by linarith
  qed
  from \<open>n > 0\<close> have "n \<ge> 1" by simp
  thus ?thesis
  proof (induction n rule: dec_induct)
    case base
    then show ?case by simp
  next
    case (step n)
    from ln_fact[of "n+1"] **[of n] show ?case by simp
  qed
qed

lemma ln_fact_diff_bounds:
  "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2) \<le> 4 * ln (if n = 0 then 1 else n) + 3"
proof (cases "n div 2 = 0")
  case True
  hence "n \<le> 1" by simp
  with ln_le_minus_one[of "2::real"] show ?thesis by (cases n) simp_all
next
  case False
  then have "n > 1" by simp
  let ?a = "real n * ln 2"
  let ?b = "4 * ln (real n) + 3"
  let ?l1 = "ln (fact (n div 2))"
  let ?a1 = "real (n div 2) * ln (real (n div 2)) - real (n div 2)"
  let ?b1 = "1 + ln (real (n div 2))"
  let ?l2 = "ln (fact n)"
  let ?a2 = "real n * ln (real n) - real n"
  let ?b2 = "1 + ln (real n)"
  have abs_a: "abs(?a - (?a2 - 2 * ?a1)) \<le> ?b - 2 * ?b1 - ?b2"
  proof (cases "even n")
    case True
    then have "real (2 * (n div 2)) = real n"
      by simp
    then have n_div_2: "real (n div 2) = real n / 2"
      by simp
    from \<open>n > 1\<close> have *: "abs(?a - (?a2 - 2 * ?a1)) = 0"
      by (simp add: n_div_2 ln_div algebra_simps)
    from \<open>even n\<close> and \<open>n > 1\<close> have "0 \<le> ln (real n) - ln (real (n div 2))"
      by (auto elim: evenE)
    also have "2 * \<dots> \<le> 3 * ln (real n) - 2 * ln (real (n div 2))"
      using \<open>n > 1\<close> by (auto intro!: ln_ge_zero)
    also have "\<dots> = ?b - 2 * ?b1 - ?b2" by simp
    finally show ?thesis using * by simp
  next
    case False
    then have "real (2 * (n div 2)) = real (n - 1)"
      by simp
    with \<open>n > 1\<close> have n_div_2: "real (n div 2) = (real n - 1) / 2"
      by simp
    from \<open>odd n\<close> \<open>n div 2 \<noteq> 0\<close> have "n \<ge> 3"
      by presburger

    have "?a - (?a2 - 2 * ?a1) = real n * ln 2 - real n * ln (real n) + real n + 
             2 * real (n div 2) * ln (real (n div 2)) - 2* real (n div 2)"
      by (simp add: algebra_simps)
    also from n_div_2 have "2 * real (n div 2) = real n - 1"
      by simp
    also have "real n * ln 2 - real n * ln (real n) + real n + 
                   (real n - 1) * ln (real (n div 2)) - (real n - 1)
                 = real n * (ln (real n - 1) - ln (real n)) - ln (real (n div 2)) + 1"
      using \<open>n > 1\<close> by (simp add: algebra_simps n_div_2 ln_div)
    finally have lhs: "abs(?a - (?a2 - 2 * ?a1)) = 
        abs(real n * (ln (real n - 1) - ln (real n)) - ln (real (n div 2)) + 1)"
      by simp

    from \<open>n > 1\<close> have "real n * (ln (real n - 1) - ln (real n)) \<le> 0"
      by (simp add: algebra_simps mult_left_mono)
    moreover from \<open>n > 1\<close> have "ln (real (n div 2)) \<le> ln (real n)" by simp
    moreover {
      have "exp 1 \<le> (3::real)" by (rule exp_le)
      also from \<open>n \<ge> 3\<close> have "\<dots> \<le> exp (ln (real n))" by simp
      finally have "ln (real n) \<ge> 1" by simp
    }
    ultimately have ub: "real n * (ln (real n - 1) - ln (real n)) - ln(real (n div 2)) + 1 \<le> 
                           3 * ln (real n) - 2 * ln(real (n div 2))" by simp
 
    have mon: "real n' * (ln (real n') - ln (real n' - 1)) \<le> 
                 real n * (ln (real n) - ln (real n - 1))" 
      if "n \<ge> 3" "n' \<ge> n" for n n'::nat
    proof (rule DERIV_nonpos_imp_nonincreasing[where f = "\<lambda>x. x * (ln x - ln (x - 1))"])
      fix t assume t: "real n \<le> t" "t \<le> real n'"
      with that have "1 / (t - 1) \<ge> ln (1 + 1/(t - 1))"
        by (intro ln_add_one_self_le_self) simp_all
      also from t that have "ln (1 + 1/(t - 1)) = ln t- ln (t - 1)"
        by (simp add: ln_div [symmetric] field_simps)
      finally have "ln t - ln (t - 1) \<le> 1 / (t - 1)" .
      with that t
      show "\<exists>y. ((\<lambda>x. x * (ln x - ln (x - 1))) has_field_derivative y) (at t) \<and> y \<le> 0"
        by (intro exI[of _ "1 / (1 - t) + ln t - ln (t - 1)"])
          (force intro!: derivative_eq_intros simp: field_simps)+
    qed (use that in simp_all)

    from \<open>n > 1\<close> have "ln 2 = ln (real n) - ln (real n / 2)"
      by (simp add: ln_div)
    also from \<open>n > 1\<close> have "\<dots> \<le> ln (real n) - ln (real (n div 2))" 
      by simp
    finally have *: "3*ln 2 + ln(real (n div 2)) \<le> 3* ln(real n) - 2* ln(real (n div 2))"
      by simp
    
    have "- real n * (ln (real n - 1) - ln (real n)) + ln(real (n div 2)) - 1 = 
            real n * (ln (real n) - ln (real n - 1)) - 1 + ln(real (n div 2))"
      by (simp add: algebra_simps)
    also have "real n * (ln (real n) - ln (real n - 1)) \<le> 3 * (ln 3 - ln (3 - 1))"
      using mon[OF _ \<open>n \<ge> 3\<close>] by simp
    also {
      have "Some (Float 3 (-1)) = ub_ln 1 3" by code_simp
      from ub_ln(1)[OF this] have "ln 3 \<le> (1.6 :: real)" by simp
      also have "1.6 - 1 / 3 \<le> 2 * (2/3 :: real)" by simp
      also have "2/3 \<le> ln (2 :: real)" by (rule ln_2_ge')
      finally have "ln 3 - 1 / 3 \<le> 2 * ln (2 :: real)" by simp
    }
    hence "3 * (ln 3 - ln (3 - 1)) - 1 \<le> 3 * ln (2 :: real)" by simp
    also note *
    finally have "- real n * (ln (real n - 1) - ln (real n)) + ln(real (n div 2)) - 1 \<le> 
                    3 * ln (real n) - 2 * ln (real (n div 2))" by simp
    hence lhs': "abs(real n * (ln (real n - 1) - ln (real n)) - ln(real (n div 2)) + 1) \<le> 
                   3 * ln (real n) - 2 * ln (real (n div 2))"
      using ub by simp
    have rhs: "?b - 2 * ?b1 - ?b2 = 3* ln (real n) - 2 * ln (real (n div 2))"
      by simp
    from \<open>n > 1\<close> have "ln (real (n div 2)) \<le> 3* ln (real n) - 2* ln (real (n div 2))"
      by simp
    with rhs lhs lhs' show ?thesis
      by simp
  qed
  then have minus_a: "-?a \<le> ?b - 2 * ?b1 - ?b2 - (?a2 - 2 * ?a1)"
    by simp
  from abs_a have a: "?a \<le> ?b - 2 * ?b1 - ?b2 + ?a2 - 2 * ?a1"
    by (simp)
  from ln_fact_bounds[of "n div 2"] False have abs_l1: "abs(?l1 - ?a1) \<le> ?b1"
    by (simp add: algebra_simps)
  then have minus_l1: "?a1 - ?l1 \<le> ?b1"
    by linarith
  from abs_l1 have l1: "?l1 - ?a1 \<le> ?b1"
    by linarith
  from ln_fact_bounds[of n] False have abs_l2: "abs(?l2 - ?a2) \<le> ?b2"
    by (simp add: algebra_simps)
  then have l2: "?l2 - ?a2 \<le> ?b2"
    by simp
  from abs_l2 have minus_l2: "?a2 - ?l2 \<le> ?b2"
    by simp
  from minus_a minus_l1 l2 have "?l2 - 2 * ?l1 - ?a \<le> ?b"
    by simp
  moreover from a l1 minus_l2 have "- ?l2 + 2 * ?l1 + ?a \<le> ?b"
    by simp
  ultimately have "abs((?l2 - 2*?l1) - ?a) \<le> ?b"
    by simp
  then show ?thesis 
    by simp
qed  
  
lemma ln_primefact:
  assumes "n \<noteq> (0::nat)"
  shows   "ln n = (\<Sum>d=1..n. if primepow d \<and> d dvd n then ln (aprimedivisor d) else 0)" 
          (is "?lhs = ?rhs")
proof -
  have "?rhs = (\<Sum>d\<in>{x \<in> {1..n}. primepow x \<and> x dvd n}. ln (real (aprimedivisor d)))" 
    unfolding primepow_factors_def by (subst sum.inter_filter [symmetric]) simp_all
  also have "{x \<in> {1..n}. primepow x \<and> x dvd n} = primepow_factors n"
    using assms by (auto simp: primepow_factors_def dest: dvd_imp_le primepow_gt_Suc_0)
  finally have *: "(\<Sum>d\<in>primepow_factors n. ln (real (aprimedivisor d))) = ?rhs" ..
  from in_prime_factors_imp_prime prime_gt_0_nat 
    have pf_pos: "\<And>p. p\<in>#prime_factorization n \<Longrightarrow> p > 0"
    by blast
  from ln_msetprod[of "prime_factorization n", OF pf_pos] assms
    have "ln n = (\<Sum>p\<in>#prime_factorization n. ln p)"
      by (simp add: of_nat_prod_mset)
  also from * sum_prime_factorization_conv_sum_primepow_factors[of n ln, OF assms(1)]
    have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

context
begin

private lemma divisors:
  fixes x d::nat
  assumes "x \<in> {1..n}"
  assumes "d dvd x"
  shows "\<exists>k\<in>{1..n div d}. x = d * k"
proof -
  from assms have "x \<le> n"
    by simp
  then have ub: "x div d \<le> n div d"
    by (simp add: div_le_mono \<open>x \<le> n\<close>)
  from assms have "1 \<le> x div d" by (auto elim!: dvdE)
  with ub have "x div d \<in> {1..n div d}"
    by simp
  with \<open>d dvd x\<close> show ?thesis by (auto intro!: bexI[of _ "x div d"])
qed

lemma ln_fact_conv_mangoldt: "ln (fact n) = (\<Sum>d=1..n. mangoldt d * floor (n / d))"
proof -
  have *: "(\<Sum>da=1..n. if primepow da \<and> da dvd d then ln (aprimedivisor da) else 0) = 
             (\<Sum>(da::nat)=1..d. if primepow da \<and> da dvd d then ln (aprimedivisor da) else 0)" 
    if d: "d \<in> {1..n}" for d
    by (rule sum.mono_neutral_right, insert d) (auto dest: dvd_imp_le)
  have "(\<Sum>d=1..n. \<Sum>da=1..d. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0) = 
      (\<Sum>d=1..n. \<Sum>da=1..n. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0)"
    by (rule sum.cong) (insert *, simp_all)
  also have "\<dots> = (\<Sum>da=1..n. \<Sum>d=1..n. if primepow da \<and>
                     da dvd d then ln (aprimedivisor da) else 0)"
    by (rule sum.swap)
  also have "\<dots> = sum (\<lambda>d. mangoldt d * floor (n/d)) {1..n}"
  proof (rule sum.cong)
    fix d assume d: "d \<in> {1..n}"
    have "(\<Sum>da = 1..n. if primepow d \<and> d dvd da then ln (real (aprimedivisor d)) else 0) =
            (\<Sum>da = 1..n. if d dvd da then mangoldt d else 0)"
      by (intro sum.cong) (simp_all add: mangoldt_def)
    also have "\<dots> = mangoldt d * real (card {x. x \<in> {1..n} \<and> d dvd x})"
      by (subst sum.inter_filter [symmetric]) (simp_all add: algebra_simps)
    also {
      have "{x. x \<in> {1..n} \<and> d dvd x} = {x. \<exists>k \<in>{1..n div d}. x=k*d}"
      proof safe
        fix x assume "x \<in> {1..n}" "d dvd x"
        thus "\<exists>k\<in>{1..n div d}. x = k * d" using divisors[of x n d] by auto
      next
        fix x k assume k: "k \<in> {1..n div d}"
        from k have "k * d \<le> n div d * d" by (intro mult_right_mono) simp_all
        also have "n div d * d \<le> n div d * d + n mod d" by (rule le_add1)
        also have "\<dots> = n" by simp
        finally have "k * d \<le> n" .
        thus "k * d \<in> {1..n}" using d k by auto
      qed auto
      also have "\<dots> = (\<lambda>k. k*d) ` {1..n div d}"
        by fast
      also have "card \<dots> = card {1..n div d}"
        by (rule card_image) (simp add: inj_on_def)
      also have "\<dots> = n div d"
        by simp
      also have "... = \<lfloor>n / d\<rfloor>"
        by (simp add: floor_divide_of_nat_eq)
      finally have "real (card {x. x \<in> {1..n} \<and> d dvd x}) = real_of_int \<lfloor>n / d\<rfloor>"
        by force
    }
    finally show "(\<Sum>da = 1..n. if primepow d \<and> d dvd da then ln (real (aprimedivisor d)) else 0) =
            mangoldt d * real_of_int \<lfloor>real n / real d\<rfloor>" .
  qed simp_all
  finally have "(\<Sum>d=1..n. \<Sum>da=1..d. if primepow da \<and>
      da dvd d then ln (aprimedivisor da) else 0) = 
    sum (\<lambda>d. mangoldt d * floor (n/d)) {1..n}" .
  with ln_primefact have "(\<Sum>d=1..n. ln d) =
    (\<Sum>d=1..n. mangoldt d * floor (n/d))"
    by simp
  with ln_fact show ?thesis
    by simp
qed

end

context
begin

private lemma div_2_mult_2_bds:
  fixes n d :: nat
  assumes "d > 0"
  shows "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
proof -
  have "\<lfloor>2::real\<rfloor> * \<lfloor>(n div 2) / d\<rfloor> \<le> \<lfloor>2 * ((n div 2) / d)\<rfloor>" 
    by (rule le_mult_floor) simp_all
  also from assms have "\<dots> \<le> \<lfloor>n / d\<rfloor>" by (intro floor_mono) (simp_all add: field_simps)
  finally show "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" by (simp add: algebra_simps)
next  
  have "real (n div d) \<le> real (2 * ((n div 2) div d) + 1)"
    by (subst div_mult2_eq [symmetric], simp only: mult.commute, subst div_mult2_eq) simp
  thus "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
    unfolding of_nat_add of_nat_mult floor_conv_div_nat [symmetric] by simp_all
qed

private lemma n_div_d_eq_1: "d \<in> {n div 2 + 1..n} \<Longrightarrow> \<lfloor>real n / real d\<rfloor> = 1"
  by (cases "n = d") (auto simp: field_simps intro: floor_eq)
    
lemma psi_bounds_ln_fact:
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
        "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
proof -
  fix n::nat
  let ?k = "n div 2" and ?d = "n mod 2"
  have *: "\<lfloor>?k / d\<rfloor> = 0" if "d > ?k" for d
  proof -
    from that div_less have "0 = ?k div d" by simp
    also have "\<dots> = \<lfloor>?k / d\<rfloor>" by (rule floor_divide_of_nat_eq [symmetric])
    finally show "\<lfloor>?k / d\<rfloor> = 0" by simp
  qed
  have sum_eq: "(\<Sum>d=1..2*?k+?d. mangoldt d * \<lfloor>?k / d\<rfloor>) = (\<Sum>d=1..?k. mangoldt d * \<lfloor>?k / d\<rfloor>)"
    by (intro sum.mono_neutral_right) (auto simp: *)
  from ln_fact_conv_mangoldt have "ln (fact n) = (\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>)" .
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * \<lfloor>(2 * (n div 2) + n mod 2) / d\<rfloor>)"
    by simp
  also have "\<dots> \<le> (\<Sum>d=1..n. mangoldt d * (2 * \<lfloor>?k / d\<rfloor> + 1))"
    using div_2_mult_2_bds(2)[of _ n]
    by (intro sum_mono mult_left_mono, subst of_int_le_iff)
       (auto simp: algebra_simps mangoldt_nonneg)
  also have "\<dots> = 2 * (\<Sum>d=1..n. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by (simp add: algebra_simps sum.distrib sum_distrib_left)
  also have "\<dots> = 2 * (\<Sum>d=1..2*?k+?d. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by presburger
  also from sum_eq have "\<dots> = 2 * (\<Sum>d=1..?k. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>) + (\<Sum>d=1..n. mangoldt d)"
    by presburger
  also from ln_fact_conv_mangoldt psi_def have "\<dots> = 2 * ln (fact ?k) + psi n"
    by presburger
  finally show "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
    by simp
next
  fix n::nat
  let ?k = "n div 2" and  ?d = "n mod 2"
  from psi_def have "psi n - psi ?k = (\<Sum>d=1..2*?k+?d. mangoldt d) - (\<Sum>d=1..?k. mangoldt d)"
    by presburger
  also have "\<dots> = sum mangoldt ({1..2 * (n div 2) + n mod 2} - {1..n div 2})"
    by (subst sum_diff) simp_all
  also have "\<dots> = (\<Sum>d\<in>({1..2 * (n div 2) + n mod 2} - {1..n div 2}). 
                    (if d \<le> ?k then 0 else mangoldt d))"
    by (intro sum.cong) simp_all
  also have "\<dots> = (\<Sum>d=1..2*?k+?d. (if d \<le> ?k then 0 else mangoldt d))"
    by (intro sum.mono_neutral_left) auto
  also have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then 0 else mangoldt d))"
    by presburger
  also have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * 0 else mangoldt d))"
    by (intro sum.cong) simp_all
  also from div_2_mult_2_bds(1) have "\<dots> \<le> (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * (\<lfloor>n/d\<rfloor> - 2 * \<lfloor>?k/d\<rfloor>) else mangoldt d))"
    by (intro sum_mono) 
       (auto simp: algebra_simps mangoldt_nonneg intro!: mult_left_mono simp del: of_int_mult)
  also from n_div_d_eq_1 have "\<dots> = (\<Sum>d=1..n. (if d \<le> ?k then mangoldt d * (\<lfloor>n/d\<rfloor> - 2 * \<lfloor>?k/d\<rfloor>) else mangoldt d * \<lfloor>n/d\<rfloor>))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * real_of_int (\<lfloor>real n / real d\<rfloor>) -
                     (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (intro sum.cong refl) (auto simp: algebra_simps)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * real_of_int (\<lfloor>real n / real d\<rfloor>)) - 
                  (\<Sum>d=1..n. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (rule sum_subtractf)    
  also have "(\<Sum>d=1..n. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0)) =
               (\<Sum>d=1..?k. (if d \<le> ?k then 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor> else 0))"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (\<Sum>d=1..?k. 2 * mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor>)"
    by (intro sum.cong) simp_all
  also have "\<dots> = 2 * (\<Sum>d=1..?k. mangoldt d * real_of_int \<lfloor>real ?k / real d\<rfloor>)"
    by (simp add: sum_distrib_left mult_ac)
  also have "(\<Sum>d = 1..n. mangoldt d * real_of_int \<lfloor>real n / real d\<rfloor>) - \<dots> = 
               ln (fact n) - 2 * ln (fact (n div 2))"
    by (simp add: ln_fact_conv_mangoldt)
  finally show "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" .
qed

end

lemma psi_bounds_induct:
  "real n * ln 2 - (4 * ln (real (if n = 0 then 1 else n)) + 3) \<le> psi n"
  "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)"
proof -
  from le_imp_neg_le[OF ln_fact_diff_bounds]
    have "n * ln 2 - (4 * ln (if n = 0 then 1 else n) + 3)
         \<le> n * ln 2 - abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)"
    by simp
  also have "\<dots> \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  also from psi_bounds_ln_fact (1) have "\<dots> \<le> psi n"
    by simp
  finally show "real n * ln 2 - (4 * ln (real (if n = 0 then 1 else n)) + 3) \<le> psi n" .
next
  from psi_bounds_ln_fact (2) have "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" .
  also have "\<dots> \<le> n * ln 2 + abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)"
    by simp
  also from ln_fact_diff_bounds [of n] 
    have "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2)
            \<le> (4 * ln (real (if n = 0 then 1 else n)) + 3)" by simp
  finally show "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)"
    by simp
qed
  

subsection \<open>Bounding the psi function\<close>

text \<open>
  In this section, we will first prove the relatively tight estimate
  @{prop "psi n \<le> 3 / 2 + ln 2 * n"} for @{term "n \<le> 128"} and then use the 
  recurrence we have just derived to extend it to @{prop "psi n \<le> 551 / 256"} for 
  @{term "n \<le> 1024"}, at which point applying the recurrence can be used to prove 
  the same bound for arbitrarily big numbers.

  First of all, we will prove the bound for @{term "n <= 128"} using reflection and
  approximation.
\<close>  

context
begin

private lemma Ball_insertD:
  assumes "\<forall>x\<in>insert y A. P x"
  shows   "P y" "\<forall>x\<in>A. P x"
  using assms by auto

private lemma meta_eq_TrueE: "PROP A \<equiv> Trueprop True \<Longrightarrow> PROP A"
  by simp

private lemma pre_mangoldt_pos: "pre_mangoldt n > 0"
  unfolding pre_mangoldt_def by (auto simp: primepow_gt_Suc_0)

private lemma psi_conv_pre_mangoldt: "psi n = ln (real (prod pre_mangoldt {1..n}))"
  by (auto simp: psi_def mangoldt_def pre_mangoldt_def ln_prod primepow_gt_Suc_0 intro!: sum.cong)

private lemma eval_psi_aux1: "psi 0 = ln (real (numeral Num.One))"
  by (simp add: psi_def)

private lemma eval_psi_aux2:
  assumes "psi m = ln (real (numeral x))" "pre_mangoldt n = y" "m + 1 = n" "numeral x * y = z"
  shows   "psi n = ln (real z)"
proof -
  from assms(2) [symmetric] have [simp]: "y > 0" by (simp add: pre_mangoldt_pos)
  have "psi n = psi (Suc m)" by (simp add: assms(3) [symmetric])
  also have "\<dots> = ln (real y * (\<Prod>x = Suc 0..m. real (pre_mangoldt x)))"
    using assms(2,3) [symmetric] by (simp add: psi_conv_pre_mangoldt prod.nat_ivl_Suc' mult_ac)
  also have "\<dots> = ln (real y) + psi m"
    by (subst ln_mult) (simp_all add: pre_mangoldt_pos prod_pos psi_conv_pre_mangoldt)
  also have "psi m = ln (real (numeral x))" by fact
  also have "ln (real y) + \<dots> = ln (real (numeral x * y))" by (simp add: ln_mult)
  finally show ?thesis by (simp add: assms(4) [symmetric])
qed

private lemma Ball_atLeast0AtMost_doubleton:
  assumes "psi 0 \<le> 3 / 2 * ln 2 * real 0"
  assumes "psi 1 \<le> 3 / 2 * ln 2 * real 1"
  shows   "(\<forall>x\<in>{0..1}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms unfolding One_nat_def atLeast0_atMost_Suc ball_simps by auto

private lemma Ball_atLeast0AtMost_insert:
  assumes "(\<forall>x\<in>{0..m}. psi x \<le> 3 / 2 * ln 2 * real x)"
  assumes "psi (numeral n) \<le> 3 / 2 * ln 2 * real (numeral n)" "m = pred_numeral n"
  shows   "(\<forall>x\<in>{0..numeral n}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms
  by (subst numeral_eq_Suc[of n], subst atLeast0_atMost_Suc,
      subst ball_simps, simp only: numeral_eq_Suc [symmetric])

private lemma eval_psi_ineq_aux:
  assumes "psi n = x" "x \<le> 3 / 2 * ln 2 * n"
  shows   "psi n \<le> 3 / 2 * ln 2 * n"
  using assms by simp_all
    
private lemma eval_psi_ineq_aux2:
  assumes "numeral m ^ 2 \<le> (2::nat) ^ (3 * n)"
  shows   "ln (real (numeral m)) \<le> 3 / 2 * ln 2 * real n"
proof -
  have "ln (real (numeral m)) \<le> 3 / 2 * ln 2 * real n \<longleftrightarrow> 
          2 * log 2 (real (numeral m)) \<le> 3 * real n"
    by (simp add: field_simps log_def)
  also have "2 * log 2 (real (numeral m)) = log 2 (real (numeral m ^ 2))"
    by (subst of_nat_power, subst log_nat_power) simp_all
  also have "\<dots> \<le> 3 * real n \<longleftrightarrow> real ((numeral m) ^ 2) \<le> 2 powr real (3 * n)"
    by (subst Transcendental.log_le_iff) simp_all
  also have "2 powr (3 * n) = real (2 ^ (3 * n))" 
    by (simp add: powr_realpow [symmetric])
  also have "real ((numeral m) ^ 2) \<le> \<dots> \<longleftrightarrow> numeral m ^ 2 \<le> (2::nat) ^ (3 * n)"
    by (rule of_nat_le_iff)
  finally show ?thesis using assms by blast
qed

private lemma eval_psi_ineq_aux_mono:
  assumes "psi n = x" "psi m = x" "psi n \<le> 3 / 2 * ln 2 * n" "n \<le> m"
  shows   "psi m \<le> 3 / 2 * ln 2 * m"
proof -
  from assms have "psi m = psi n" by simp
  also have "\<dots> \<le> 3 / 2 * ln 2 * n" by fact
  also from \<open>n \<le> m\<close> have "\<dots> \<le> 3 / 2 * ln 2 * m" by simp
  finally show ?thesis .
qed

lemma not_primepow_1_nat: "\<not>primepow (1 :: nat)" by auto
                 
ML_file \<open>bertrand.ML\<close>

(* This should not take more than 1 minute *)
local_setup \<open>fn ctxt =>
let
  fun tac {context = ctxt, ...} =
    let
      val psi_cache = Bertrand.prove_psi ctxt 129
      fun prove_psi_ineqs ctxt =
        let
          fun tac {context = ctxt, ...} = 
            HEADGOAL (resolve_tac ctxt @{thms eval_psi_ineq_aux2} THEN' Simplifier.simp_tac ctxt)
          fun prove_by_approx n thm =
            let
              val thm = thm RS @{thm eval_psi_ineq_aux}
              val [prem] = Thm.prems_of thm
              val prem = Goal.prove ctxt [] [] prem tac
            in
              prem RS thm
            end
          fun prove_by_mono last_thm last_thm' thm =
            let
              val thm = @{thm eval_psi_ineq_aux_mono} OF [last_thm, thm, last_thm']
              val [prem] = Thm.prems_of thm
              val prem = Goal.prove ctxt [] [] prem (K (HEADGOAL (Simplifier.simp_tac ctxt)))
            in
              prem RS thm
            end
          fun go _ acc [] = acc
            | go last acc ((n, x, thm) :: xs) =
                let
                  val thm' =
                    case last of
                      NONE => prove_by_approx n thm
                    | SOME (last_x, last_thm, last_thm') => 
                        if last_x = x then 
                          prove_by_mono last_thm last_thm' thm 
                        else
                          prove_by_approx n thm
                in
                  go (SOME (x, thm, thm')) (thm' :: acc) xs
                end
        in
          rev o go NONE []
        end
            
      val psi_ineqs = prove_psi_ineqs ctxt psi_cache
      fun prove_ball ctxt (thm1 :: thm2 :: thms) =
            let
              val thm = @{thm Ball_atLeast0AtMost_doubleton} OF [thm1, thm2]
              fun solve_prem thm =
                let
                  fun tac {context = ctxt, ...} = HEADGOAL (Simplifier.simp_tac ctxt)
                  val thm' = Goal.prove ctxt [] [] (Thm.cprem_of thm 1 |> Thm.term_of) tac
                in
                  thm' RS thm
                end
              fun go thm thm' = (@{thm Ball_atLeast0AtMost_insert} OF [thm', thm]) |> solve_prem
            in
              fold go thms thm
            end
        | prove_ball _ _ = raise Match
    in
      HEADGOAL (resolve_tac ctxt [prove_ball ctxt psi_ineqs])
    end
  val thm = Goal.prove @{context} [] [] @{prop "\<forall>n\<in>{0..128}. psi n \<le> 3 / 2 * ln 2 * n"} tac
in
  Local_Theory.note ((@{binding psi_ubound_log_128}, []), [thm]) ctxt |> snd
end
\<close>

end


context
begin
  
private lemma psi_ubound_aux:
  defines "f \<equiv> \<lambda>x::real. (4 * ln x + 3) / (ln 2 * x)"
  assumes "x \<ge> 2" "x \<le> y"
  shows   "f x \<ge> f y"
using assms(3)
proof (rule DERIV_nonpos_imp_nonincreasing, goal_cases)
  case (1 t)
  define f' where "f' = (\<lambda>x. (1 - 4 * ln x) / x^2 / ln 2 :: real)"
  from 1 assms(2) have "(f has_real_derivative f' t) (at t)" unfolding f_def f'_def
    by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
  moreover {
    from ln_2_ge have "1/4 \<le> ln (2::real)" by simp
    also from assms(2) 1 have "\<dots> \<le> ln t" by simp
    finally have "ln t \<ge> 1/4" .
  }
  with 1 assms(2) have "f' t \<le> 0" by (simp add: f'_def field_simps)
  ultimately show ?case by (intro exI[of _ "f' t"]) simp_all
qed  

text \<open>
  These next rules are used in combination with @{thm psi_bounds_induct} and 
  @{thm psi_ubound_log_128} to extend the upper bound for @{term "psi"} from values no greater 
  than 128 to values no greater than 1024. The constant factor of the upper bound changes every 
  time, but once we have reached 1024, the recurrence is self-sustaining in the sense that we do 
  not have to adjust the constant factor anymore in order to double the range.
\<close>
lemma psi_ubound_log_double_cases':
  assumes "\<And>n. n \<le> m \<Longrightarrow> psi n \<le> c * ln 2 * real n" "n \<le> m'" "m' = 2*m"
          "c \<le> c'" "c \<ge> 0" "m \<ge> 1" "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
  shows   "psi n \<le> c' * ln 2 * real n"
proof (cases "n > m")
  case False
  hence "psi n \<le> c * ln 2 * real n" by (intro assms) simp_all
  also have "c \<le> c'" by fact
  finally show ?thesis by - (simp_all add: mult_right_mono)
next
  case True
  hence n: "n \<ge> m+1" by simp
  from psi_bounds_induct(2)[of n] True
    have "psi n \<le> real n * ln 2 + 4 * ln (real n) + 3 + psi (n div 2)" by simp
  also from assms have "psi (n div 2) \<le> c * ln 2 * real (n div 2)" 
    by (intro assms) simp_all
  also have "real (n div 2) \<le> real n / 2" by simp
  also have "c * ln 2 * \<dots> = c / 2 * ln 2 * real n" by simp
  also have "real n * ln 2 + 4 * ln (real n) + 3 + \<dots> = 
               (1 + c/2) * ln 2 * real n + (4 * ln (real n) + 3)" by (simp add: field_simps)
  also {
    have "(4 * ln (real n) + 3) / (ln 2 * (real n)) \<le> (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
      using n assms by (intro psi_ubound_aux) simp_all
    also from assms have "(4 * ln (m+1) + 3) / (ln 2 * (m+1)) \<le> c' - 1 - c/2" 
      by (simp add: algebra_simps)
    finally have "4 * ln (real n) + 3 \<le> (c' - 1 - c/2) * ln 2 * real n" 
      using n by (simp add: field_simps)
  }
  also have "(1 + c / 2) * ln 2 * real n + (c' - 1 - c / 2) * ln 2 * real n = c' * ln 2 * real n"
    by (simp add: field_simps)
  finally show ?thesis using \<open>c \<ge> 0\<close> by (simp_all add: mult_left_mono)
qed

end  

lemma psi_ubound_log_double_cases:
  assumes "\<forall>n\<le>m. psi n \<le> c * ln 2 * real n"
          "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
          "m' = 2*m" "c \<le> c'" "c \<ge> 0" "m \<ge> 1" 
  shows   "\<forall>n\<le>m'. psi n \<le> c' * ln 2 * real n"
  using assms(1) by (intro allI impI assms psi_ubound_log_double_cases'[of m c _ m' c']) auto

lemma psi_ubound_log_1024:
  "\<forall>n\<le>1024. psi n \<le> 551 / 256 * ln 2 * real n"
proof -
  from psi_ubound_log_128 have "\<forall>n\<le>128. psi n \<le> 3 / 2 * ln 2 * real n" by simp
  hence "\<forall>n\<le>256. psi n \<le> 1025 / 512 * ln 2 * real n"
  proof (rule psi_ubound_log_double_cases, goal_cases)
    case 1
    have "Some (Float 624 (- 7)) = ub_ln 9 129" by code_simp
    from ub_ln(1)[OF this] and ln_2_ge show ?case by (simp add: field_simps)
  qed simp_all
  hence "\<forall>n\<le>512. psi n \<le> 549 / 256 * ln 2 * real n"
  proof (rule psi_ubound_log_double_cases, goal_cases)
    case 1
    have "Some (Float 180 (- 5)) = ub_ln 7 257" by code_simp
    from ub_ln(1)[OF this] and ln_2_ge show ?case by (simp add: field_simps)
  qed simp_all
  thus "\<forall>n\<le>1024. psi n \<le> 551 / 256 * ln 2 * real n"
  proof (rule psi_ubound_log_double_cases, goal_cases)
    case 1
    have "Some (Float 203 (- 5)) = ub_ln 7 513" by code_simp
    from ub_ln(1)[OF this] and ln_2_ge show ?case by (simp add: field_simps)
  qed simp_all
qed
  
lemma psi_bounds_sustained_induct:
  assumes "4 * ln (1 + 2 ^ j) + 3 \<le> d * ln 2 * (1 + 2^j)"
  assumes "4 / (1 + 2^j) \<le> d * ln 2"
  assumes "0 \<le> c"
  assumes "c / 2 + d + 1 \<le> c"
  assumes "j \<le> k"
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "n \<le> 2^(Suc k)"
  shows "psi n \<le> c * ln 2 * n"
proof (cases "n \<le> 2^k")
  case True
  with assms(6) show ?thesis .
next
  case False
  from psi_bounds_induct(2) 
    have "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)" .
  also from False have "(if n = 0 then 1 else n) = n"
    by simp
  finally have "psi n \<le> real n * ln 2 + (4 * ln (real n) + 3) + psi (n div 2)"
    by simp
  also from assms(6,7) have "psi (n div 2) \<le> c * ln 2 * (n div 2)"
    by simp
  also have "real (n div 2) \<le> real n / 2"
    by simp
  also have "real n * ln 2 + (4 * ln (real n) + 3) + c * ln 2 * (n / 2) \<le> c * ln 2 * real n"
    proof (rule overpower_lemma[of
            "\<lambda>x. x * ln 2 + (4 * ln x + 3) + c * ln 2 * (x / 2)" "1+2^j"
            "\<lambda>x. c * ln 2 * x" "\<lambda>x. c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2"
            "real n"])
      from assms(1) have "4 * ln (1 + 2^j) + 3 \<le> d * ln 2 * (1 + 2^j)" .
      also from assms(4) have "d \<le> c - c/2 - 1"
        by simp
      also have "(\<dots>) * ln 2 * (1 + 2 ^ j) = c * ln 2 * (1 + 2 ^ j) - c / 2 * ln 2 * (1 + 2 ^ j)
          - (1 + 2 ^ j) * ln 2"
        by (simp add: left_diff_distrib)
      finally have "4 * ln (1 + 2^j) + 3 \<le> c * ln 2 * (1 + 2 ^ j) - c / 2 * ln 2 * (1 + 2 ^ j)
          - (1 + 2 ^ j) * ln 2"
        by (simp add: add_pos_pos)
      then show "(1 + 2 ^ j) * ln 2 + (4 * ln (1 + 2 ^ j) + 3)
                    + c * ln 2 * ((1 + 2 ^ j) / 2) \<le> c * ln 2 * (1 + 2 ^ j)"
        by simp
    next
      fix x::real
      assume x: "1 + 2^j \<le> x"
      moreover have "1 + 2 ^ j > (0::real)" by (simp add: add_pos_pos)
      ultimately have x_pos: "x > 0" by linarith
      show "((\<lambda>x. c * ln 2 * x - (x * ln 2 + (4 * ln x + 3) + c * ln 2 * (x / 2)))
              has_real_derivative c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2) (at x)"
        by (rule derivative_eq_intros refl | simp add: \<open>0 < x\<close>)+
      from \<open>0 < x\<close> \<open>0 < 1 + 2^j\<close> have "0 < x * (1 + 2^j)"
        by (rule mult_pos_pos)
      have "4 / x \<le> 4 / (1 + 2^j)"
        by (intro divide_left_mono mult_pos_pos add_pos_pos x x_pos) simp_all
      also from assms(2) have "4 / (1 + 2^j) \<le> d * ln 2" .
      also from assms(4) have "d \<le> c - c/2 - 1" by simp
      also have "\<dots> * ln 2 = c * ln 2 - c/2 * ln 2 - ln 2" by (simp add: algebra_simps)
      finally show "0 \<le> c * ln 2 - ln 2 - 4 / x - c / 2 * ln 2" by simp
    next
      have "1 + 2^j = real (1 + 2^j)" by simp
      also from assms(5) have "\<dots> \<le> real (1 + 2^k)" by simp
      also from False have "2^k \<le> n - 1" by simp
      finally show "1 + 2^j \<le> real n" using False by simp 
    qed
    finally show ?thesis using assms by - (simp_all add: mult_left_mono)
qed

lemma psi_bounds_sustained:
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "4 * ln (1 + 2^k) + 3 \<le> (c/2 - 1) * ln 2 * (1 + 2^k)"
  assumes "4 / (1 + 2^k) \<le> (c/2 - 1) * ln 2"
  assumes "c \<ge> 0"
  shows "psi n \<le> c * ln 2 * n"
proof -
  have *: "psi n \<le> c * ln 2 * n" if "n \<le> 2^j" for j n
  using that
  proof (induction j arbitrary: n)
    case 0
    with assms(4) 0 show ?case unfolding psi_def mangoldt_def by (cases n) auto
  next
    case (Suc j)
    show ?case
      proof (cases "k \<le> j")
        case True
        from assms(4) have c_div_2: "c/2 + (c/2 - 1) + 1 \<le> c"
          by simp
        from psi_bounds_sustained_induct[of k "c/2 -1" c j,
             OF assms(2) assms(3) assms(4) c_div_2 True Suc.IH Suc.prems]
          show ?thesis by simp
      next
        case False
        then have j_lt_k: "Suc j \<le> k" by simp
        from Suc.prems have "n \<le> 2 ^ Suc j" .
        also have "(2::nat) ^ Suc j \<le> 2 ^ k"
          using power_increasing[of "Suc j" k "2::nat", OF j_lt_k]
          by simp
        finally show ?thesis using assms(1) by simp
      qed
    qed
    have "n < 2 ^ n" by (induction n) simp_all
    with *[of n n] show ?thesis by simp
qed

lemma psi_ubound_log: "psi n \<le> 551 / 256 * ln 2 * n"
proof (rule psi_bounds_sustained)
  show "0 \<le> 551 / (256 :: real)" by simp
next
  fix n :: nat assume "n \<le> 2 ^ 10"
  with psi_ubound_log_1024 show "psi n \<le> 551 / 256 * ln 2 * real n" by auto
next
  have "4 / (1 + 2 ^ 10) \<le> (551 / 256 / 2 - 1) * (2/3 :: real)"
    by simp
  also have "\<dots> \<le> (551 / 256 / 2 - 1) * ln 2"
    by (intro mult_left_mono ln_2_ge') simp_all
  finally show "4 / (1 + 2 ^ 10) \<le> (551 / 256 / 2 - 1) * ln (2 :: real)" .
next
  have "Some (Float 16 (-1)) = ub_ln 3 1025" by code_simp
  from ub_ln(1)[OF this] and ln_2_ge 
    have "2048 * ln 1025 + 1536 \<le> 39975 * (ln 2::real)" by simp
  thus "4 * ln (1 + 2 ^ 10) + 3 \<le> (551 / 256 / 2 - 1) * ln 2 * (1 + 2 ^ 10 :: real)"
    by simp
qed

lemma psi_ubound_3_2: "psi n \<le> 3/2 * n"
proof -
  have "(551 / 256) * ln 2 \<le> (551 / 256) * (16/23 :: real)" 
    by (intro mult_left_mono ln_2_le') auto
  also have "\<dots> \<le> 3 / 2" by simp
  finally have "551 / 256 * ln 2 \<le> 3/(2::real)" .
  with of_nat_0_le_iff mult_right_mono have "551 / 256 * ln 2 * n \<le> 3/2 * n"
    by blast
  with psi_ubound_log[of "n"] show ?thesis
    by linarith
qed


subsection \<open>Doubling psi and theta\<close>  

lemma psi_residues_compare_2:
  "psi_odd_2 n \<le> psi_even_2 n"
proof -
  have "psi_odd_2 n = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_odd d}. mangoldt_odd d)"
    unfolding mangoldt_odd_def by (rule sum.mono_neutral_right) auto
  also have "\<dots> = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_odd d}. ln (real (aprimedivisor d)))"
    by (intro sum.cong refl) (simp add: mangoldt_odd_def)
  also have "\<dots> \<le> (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_even d}. ln (real (aprimedivisor d)))"
  proof (rule sum_le_included [where i = "\<lambda>y. y * aprimedivisor y"]; clarify?)
    fix d :: nat assume "d \<in> {2..n}" "primepow_odd d"
    note d = this
    then obtain p k where d': "k \<ge> 1" "prime p" "d = p ^ (2*k+1)" 
      by (auto simp: primepow_odd_def)
    from d' have "p ^ (2 * k) \<le> p ^ (2 * k + 1)" 
      by (subst power_increasing_iff) (auto simp: prime_gt_Suc_0_nat)
    also from d d' have "\<dots> \<le> n" by simp
    finally have "p ^ (2 * k) \<le> n" .
    moreover from d' have "p ^ (2 * k) > 1" 
      by (intro one_less_power) (simp_all add: prime_gt_Suc_0_nat)
    ultimately have "p ^ (2 * k) \<in> {2..n}" by simp
    moreover from d' have "primepow_even (p ^ (2 * k))"
      by (auto simp: primepow_even_def)
    ultimately show "\<exists>y\<in>{d \<in> {2..n}. primepow_even d}. y * aprimedivisor y = d \<and>
                       ln (real (aprimedivisor d)) \<le> ln (real (aprimedivisor y))" using d'
      by (intro bexI[of _ "p ^ (2 * k)"])
         (auto simp: aprimedivisor_prime_power aprimedivisor_primepow)
  qed (simp_all add: of_nat_ge_1_iff Suc_le_eq)
  also have "\<dots> = (\<Sum>d\<in>{d. d \<in> {2..n} \<and> primepow_even d}. mangoldt_even d)"
    by (intro sum.cong refl) (simp add: mangoldt_even_def)
  also have "\<dots> = psi_even_2 n"
    unfolding mangoldt_even_def by (rule sum.mono_neutral_left) auto
  finally show ?thesis .
qed

lemma psi_residues_compare:
  "psi_odd n \<le> psi_even n"
proof -
  have "\<not> primepow_odd 1" by (simp add: primepow_odd_def)
  hence *: "mangoldt_odd 1 = 0" by (simp add: mangoldt_odd_def)
  have "\<not> primepow_even 1"
    using primepow_gt_Suc_0[OF primepow_even_imp_primepow, of 1] by auto
  with mangoldt_even_def have **: "mangoldt_even 1 = 0"
    by simp
  from psi_odd_def have "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"
    by simp
  also from * have "\<dots> = psi_odd_2 n"
    by (cases "n \<ge> 1") (simp_all add: eval_nat_numeral sum.atLeast_Suc_atMost)
  also from psi_residues_compare_2 have "\<dots> \<le> psi_even_2 n" .
  also from ** have "\<dots> = psi_even n"
    by (cases "n \<ge> 1") (simp_all add: eval_nat_numeral sum.atLeast_Suc_atMost psi_even_def)
  finally show ?thesis .
qed

lemma primepow_iff_even_sqr:
  "primepow n \<longleftrightarrow> primepow_even (n^2)"
  by (cases "n = 0")
     (auto simp: primepow_even_altdef aprimedivisor_primepow_power primepow_power_iff_nat
                 prime_elem_multiplicity_power_distrib prime_aprimedivisor' prime_imp_prime_elem
                 unit_factor_nat_def primepow_gt_0_nat dest: primepow_gt_Suc_0)

lemma psi_sqrt: "psi (Discrete.sqrt n) = psi_even n"
proof (induction n)
  case 0
  with psi_def psi_even_def show ?case by simp
next
  case (Suc n)
  then show ?case
    proof cases
      assume asm: "\<exists> m. Suc n = m^2"
      with sqrt_Suc have sqrt_seq: "Discrete.sqrt(Suc n) = Suc(Discrete.sqrt n)"
        by simp
      from asm obtain "m" where "   Suc n = m^2"
        by blast
      with sqrt_seq have "Suc(Discrete.sqrt n) = m"
        by simp
      with \<open>Suc n = m^2\<close> have suc_sqrt_n_sqrt: "(Suc(Discrete.sqrt n))^2 = Suc n"
        by simp
      from sqrt_seq have "psi (Discrete.sqrt (Suc n)) = psi (Suc (Discrete.sqrt n))"
        by simp
      also from psi_def have "\<dots> = psi (Discrete.sqrt n) + mangoldt (Suc (Discrete.sqrt n))"
        by simp
      also from Suc.IH have "psi (Discrete.sqrt n) = psi_even n" .
      also have "mangoldt (Suc (Discrete.sqrt n)) = mangoldt_even (Suc n)"
      proof (cases "primepow (Suc(Discrete.sqrt n))")
        case True
        with primepow_iff_even_sqr have True2: "primepow_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        from suc_sqrt_n_sqrt have "mangoldt_even (Suc n) = mangoldt_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        also from mangoldt_even_def True2
          have "\<dots> = ln (aprimedivisor ((Suc (Discrete.sqrt n))^2))"
          by simp
        also from True have "aprimedivisor ((Suc (Discrete.sqrt n))^2) = aprimedivisor (Suc (Discrete.sqrt n))"
          by (simp add: aprimedivisor_primepow_power)
        also from True have "ln (\<dots>) = mangoldt (Suc (Discrete.sqrt n))"
          by (simp add: mangoldt_def)
        finally show ?thesis ..
      next
        case False
        with primepow_iff_even_sqr
          have False2: "\<not> primepow_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        from suc_sqrt_n_sqrt have "mangoldt_even (Suc n) = mangoldt_even ((Suc(Discrete.sqrt n))^2)"
          by simp
        also from mangoldt_even_def False2
          have "\<dots> = 0"
          by simp
        also from False have "\<dots> = mangoldt (Suc (Discrete.sqrt n))"
          by (simp add: mangoldt_def)
        finally show ?thesis ..
      qed  
      also from psi_even_def have "psi_even n + mangoldt_even (Suc n) = psi_even (Suc n)"
        by simp
      finally show ?case .
    next
      assume asm: "\<not>(\<exists>m. Suc n = m^2)"
      with sqrt_Suc have sqrt_eq: "Discrete.sqrt (Suc n) = Discrete.sqrt n"
        by simp
      then have lhs: "psi (Discrete.sqrt (Suc n)) = psi (Discrete.sqrt n)"
        by simp
      have "\<not> primepow_even (Suc n)"
        proof
          assume "primepow_even (Suc n)"
          with primepow_even_def obtain "p" "k"
            where "1 \<le> k \<and> prime p \<and> Suc n = p ^ (2 * k)" 
            by blast
          with power_even_eq have "Suc n = (p ^ k)^2"
            by simp
          with asm show False by blast
        qed
      with psi_even_def mangoldt_even_def
        have rhs: "psi_even (Suc n) = psi_even n"
        by simp
      from Suc.IH lhs rhs show ?case
        by simp
    qed
qed

lemma mangoldt_split:
  "mangoldt d = mangoldt_1 d + mangoldt_even d + mangoldt_odd d"
proof (cases "primepow d")
  case False
  thus ?thesis
    by (auto simp: mangoldt_def mangoldt_1_def mangoldt_even_def mangoldt_odd_def
             dest: primepow_even_imp_primepow primepow_odd_imp_primepow)
next
  case True
  thus ?thesis
    by (auto simp: mangoldt_def mangoldt_1_def mangoldt_even_def mangoldt_odd_def primepow_cases)
qed

lemma psi_split: "psi n = theta n + psi_even n + psi_odd n"
  by (induction n) 
     (simp_all add: psi_def theta_def psi_even_def psi_odd_def mangoldt_1_def mangoldt_split)

lemma psi_mono: "m \<le> n \<Longrightarrow> psi m \<le> psi n" unfolding psi_def
  by (intro sum_mono2 mangoldt_nonneg) auto

lemma psi_pos: "0 \<le> psi n"
  by (auto simp: psi_def intro!: sum_nonneg mangoldt_nonneg)

lemma mangoldt_odd_pos: "0 \<le> mangoldt_odd d"
  using aprimedivisor_gt_Suc_0[of d]
  by (auto simp: mangoldt_odd_def of_nat_le_iff[of 1, unfolded of_nat_1] Suc_le_eq
           intro!: ln_ge_zero dest!: primepow_odd_imp_primepow primepow_gt_Suc_0)

lemma psi_odd_mono: "m \<le> n \<Longrightarrow> psi_odd m \<le> psi_odd n"
  using mangoldt_odd_pos sum_mono2[of "{1..n}" "{1..m}" "mangoldt_odd"] 
  by (simp add: psi_odd_def)

lemma psi_odd_pos: "0 \<le> psi_odd n"
  by (auto simp: psi_odd_def intro!: sum_nonneg mangoldt_odd_pos)

lemma psi_theta:
  "theta n + psi (Discrete.sqrt n) \<le> psi n" "psi n \<le> theta n + 2 * psi (Discrete.sqrt n)"
  using psi_odd_pos[of n] psi_residues_compare[of n] psi_sqrt[of n] psi_split[of n]
  by simp_all

context
begin

private lemma sum_minus_one: 
  "(\<Sum>x \<in> {1..y}. (- 1 :: real) ^ (x + 1)) = (if odd y then 1 else 0)"
  by (induction y) simp_all
  
private lemma div_invert:
  fixes x y n :: nat
  assumes "x > 0" "y > 0" "y \<le> n div x"
  shows "x \<le> n div y"
proof -
  from assms(1,3) have "y * x \<le> (n div x) * x"
    by simp
  also have "\<dots> \<le> n"
    by (simp add: minus_mod_eq_div_mult[symmetric])
  finally have "y * x \<le> n" .
  with assms(2) show ?thesis
    using div_le_mono[of "y*x" n y] by simp
qed

lemma sum_expand_lemma:
  "(\<Sum>d=1..n. (-1) ^ (d + 1) * psi (n div d)) = 
     (\<Sum>d = 1..n. (if odd (n div d) then 1 else 0) * mangoldt d)"
proof -
  have **: "x \<le> n" if "x \<le> n div y" for x y
    using div_le_dividend order_trans that by blast
  have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) = 
          (\<Sum>d=1..n. (-1)^(d+1) * (\<Sum>e=1..n div d. mangoldt e))"
    by (simp add: psi_def)
  also have "\<dots> = (\<Sum>d = 1..n. \<Sum>e = 1..n div d. (-1)^(d+1) * mangoldt e)"
    by (simp add: sum_distrib_left)
  also from ** have "\<dots> = (\<Sum>d = 1..n. \<Sum>e\<in>{y\<in>{1..n}. y \<le> n div d}. (-1)^(d+1) * mangoldt e)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>y = 1..n. \<Sum>x | x \<in> {1..n} \<and> y \<le> n div x. (- 1) ^ (x + 1) * mangoldt y)"
    by (rule sum.swap_restrict) simp_all
  also have "\<dots> = (\<Sum>y = 1..n. \<Sum>x | x \<in> {1..n} \<and> x \<le> n div y. (- 1) ^ (x + 1) * mangoldt y)"
    by (intro sum.cong) (auto intro: div_invert)
  also from ** have "\<dots> = (\<Sum>y = 1..n. \<Sum>x \<in> {1..n div y}. (- 1) ^ (x + 1) * mangoldt y)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>y = 1..n. (\<Sum>x \<in> {1..n div y}. (- 1) ^ (x + 1)) * mangoldt y)"
    by (intro sum.cong) (simp_all add: sum_distrib_right)
  also have "\<dots> = (\<Sum>y = 1..n. (if odd (n div y) then 1 else 0) * mangoldt y)"
    by (intro sum.cong refl) (simp_all only: sum_minus_one)
  finally show ?thesis .
qed

private lemma floor_half_interval:
  fixes n d :: nat
  assumes "d \<noteq> 0"
  shows "real (n div d) - real (2 * ((n div 2) div d)) = (if odd (n div d) then 1 else 0)"
proof -
  have "((n div 2) div d) = (n div (2 * d))"
    by (rule div_mult2_eq[symmetric])
  also have "\<dots> = ((n div d) div 2)"
    by (simp add: mult_ac div_mult2_eq)
  also have "real (n div d) - real (2 * \<dots>) = (if odd (n div d) then 1 else 0)"
    by (cases "odd (n div d)", cases "n div d = 0 ", simp_all)
  finally show ?thesis by simp
qed

lemma fact_expand_psi:
  "ln (fact n) - 2 * ln (fact (n div 2)) = (\<Sum>d=1..n. (-1)^(d+1) * psi (n div d))"
proof -
  have "ln (fact n) - 2 * ln (fact (n div 2)) =
    (\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>) - 2 * (\<Sum>d=1..n div 2. mangoldt d * \<lfloor>(n div 2) / d\<rfloor>)"
    by (simp add:  ln_fact_conv_mangoldt)
  also have "(\<Sum>d=1..n div 2. mangoldt d * \<lfloor>real (n div 2) / d\<rfloor>) =
               (\<Sum>d=1..n. mangoldt d * \<lfloor>real (n div 2) / d\<rfloor>)"
    by (rule sum.mono_neutral_left) (auto simp: floor_unique[of 0])
  also have "2 * \<dots> = (\<Sum>d=1..n. mangoldt d * 2 * \<lfloor>real (n div 2) / d\<rfloor>)"
    by (simp add: sum_distrib_left mult_ac)
  also have "(\<Sum>d=1..n. mangoldt d * \<lfloor>n / d\<rfloor>) - \<dots> = 
               (\<Sum>d=1..n. (mangoldt d * \<lfloor>n / d\<rfloor> - mangoldt d * 2 * \<lfloor>real (n div 2) / d\<rfloor>))"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * (\<lfloor>n / d\<rfloor> - 2 * \<lfloor>real (n div 2) / d\<rfloor>))"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>d=1..n. mangoldt d * (if odd(n div d) then 1 else 0))"
    by (intro sum.cong refl)
       (simp_all add: floor_conv_div_nat [symmetric] floor_half_interval [symmetric])
  also have "\<dots> = (\<Sum>d=1..n. (if odd(n div d) then 1 else 0) * mangoldt d)"
    by (simp add: mult_ac)
  also from sum_expand_lemma[symmetric] have "\<dots> = (\<Sum>d=1..n. (-1)^(d+1) * psi (n div d))" .  
  finally show ?thesis .
qed
  
end

lemma psi_expansion_cutoff:
  assumes "m \<le> p"
  shows   "(\<Sum>d=1..2*m. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*p. (-1)^(d+1) * psi (n div d))"
          "(\<Sum>d=1..2*p+1. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*m+1. (-1)^(d+1) * psi (n div d))"
using assms
proof (induction m rule: inc_induct)
  case (step k)
  have "(\<Sum>d = 1..2 * k. (-1)^(d + 1) * psi (n div d)) \<le> 
          (\<Sum>d = 1..2 * Suc k. (-1)^(d + 1) * psi (n div d))"
    by (simp add: psi_mono div_le_mono2)
  with step.IH(1)
    show "(\<Sum>d = 1..2 * k. (-1)^(d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..2 * p. (-1)^(d + 1) * psi (n div d))"
      by simp
  from step.IH(2)
    have "(\<Sum>d = 1..2 * p + 1. (-1)^(d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..2 * Suc k + 1. (-1)^(d + 1) * psi (n div d))" .
  also have "\<dots> \<le> (\<Sum>d = 1..2 * k + 1. (-1)^(d + 1) * psi (n div d))"
    by (simp add: psi_mono div_le_mono2)
  finally show "(\<Sum>d = 1..2 * p + 1. (-1)^(d + 1) * psi (n div d))
       \<le> (\<Sum>d = 1..2 * k + 1. (-1)^(d + 1) * psi (n div d))" .
qed simp_all

lemma fact_psi_bound_even:
  assumes "even k"
  shows   "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
proof -
  have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
  proof (cases "k \<le> n")
    case True
    with psi_expansion_cutoff(1)[of "k div 2" "n div 2" n]
      have "(\<Sum>d=1..2*(k div 2). (-1)^(d+1) * psi (n div d))
        \<le> (\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))"
      by simp
    also from assms have "2*(k div 2) = k"
      by simp
    also have "(\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))
      \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
    proof (cases "even n")
      case True
      then show ?thesis
        by simp
    next
      case False
      from psi_pos have "(\<Sum>d = 1..2*(n div 2). (- 1) ^ (d + 1) * psi (n div d))
          \<le> (\<Sum>d = 1..2*(n div 2) + 1. (- 1) ^ (d + 1) * psi (n div d))"
        by simp
      with False show ?thesis
        by simp
    qed
    finally show ?thesis .
  next
    case False
    hence *: "n div 2 \<le> (k-1) div 2"
      by simp
    have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le>
            (\<Sum>d=1..2*((k-1) div 2) + 1. (-1)^(d+1) * psi (n div d))"
    proof (cases "k = 0")
      case True
      with psi_pos show ?thesis by simp
    next
      case False
      with sum.cl_ivl_Suc[of "\<lambda>d. (-1)^(d+1) * psi (n div d)" 1 "k-1"]
      have "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) = (\<Sum>d=1..k-1. (-1)^(d+1) * psi (n div d))
          + (-1)^(k+1) * psi (n div k)"
        by simp
      also from assms psi_pos have "(-1)^(k+1) * psi (n div k) \<le> 0"
        by simp
      also from assms False have "k-1 = 2*((k-1) div 2) + 1"
        by presburger
      finally show ?thesis by simp
    qed
    also from * psi_expansion_cutoff(2)[of "n div 2" "(k-1) div 2" n]
      have "\<dots> \<le> (\<Sum>d=1..2*(n div 2) + 1. (-1)^(d+1) * psi (n div d))" by blast
    also have "\<dots> \<le> (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_def)
    finally show ?thesis .
  qed
  also from fact_expand_psi have "\<dots> = ln (fact n) - 2 * ln (fact (n div 2))" ..
  finally show ?thesis .
qed

lemma fact_psi_bound_odd:
  assumes "odd k"
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
proof -
  from fact_expand_psi 
    have "ln (fact n) - 2 * ln (fact (n div 2)) = (\<Sum>d = 1..n. (- 1) ^ (d + 1) * psi (n div d))" .
  also have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
  proof (cases "k \<le> n")
    case True
    have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) \<le> (
             \<Sum>d=1..2*(n div 2)+1. (-1)^(d+1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_pos)
    also from True assms psi_expansion_cutoff(2)[of "k div 2" "n div 2" n]
      have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
        by simp
    finally show ?thesis .
  next
    case False
    have "(\<Sum>d=1..n. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*((n+1) div 2). (-1)^(d+1) * psi (n div d))"
      by (cases "even n") (simp_all add: psi_def)
    also from False assms psi_expansion_cutoff(1)[of "(n+1) div 2" "k div 2" n]
      have "(\<Sum>d=1..2*((n+1) div 2). (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*(k div 2). (-1)^(d+1) * psi (n div d))"
        by simp
    also from assms have "\<dots> \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
      by (auto elim: oddE simp: psi_pos)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma fact_psi_bound_2_3:
  "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n - psi (n div 2) + psi (n div 3)"
proof -
  show "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))" 
    by (rule psi_bounds_ln_fact (2))
next
  from fact_psi_bound_odd[of 3 n] have "ln (fact n) - 2 * ln (fact (n div 2))
  \<le> (\<Sum>d = 1..3. (- 1) ^ (d + 1) * psi (n div d))"
    by simp
  also have "\<dots> = psi n - psi (n div 2) + psi (n div 3)"
    by (simp add: sum.atLeast_Suc_atMost numeral_2_eq_2)
  finally show "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n - psi (n div 2) + psi (n div 3)" .
qed

lemma ub_ln_1200: "ln 1200 \<le> 57 / (8 :: real)"
proof -
  have "Some (Float 57 (-3)) = ub_ln 8 1200" by code_simp
  from ub_ln(1)[OF this] show ?thesis by simp
qed
  
lemma psi_double_lemma:
  assumes "n \<ge> 1200"
  shows "real n / 6 \<le> psi n - psi (n div 2)"
proof -
  from ln_fact_diff_bounds
    have "\<bar>ln (fact n) - 2 * ln (fact (n div 2)) - real n * ln 2\<bar>
        \<le> 4 * ln (real (if n = 0 then 1 else n)) + 3" .
  with assms have "ln (fact n) - 2 * ln (fact (n div 2))
        \<ge> real n * ln 2 - 4 * ln (real n) - 3"
    by simp
  moreover have "real n * ln 2 - 4 * ln (real n) - 3 \<ge> 2 / 3 * n"
  proof (rule overpower_lemma[of "\<lambda>n. 2/3 * n" 1200])
    show "2 / 3 * 1200 \<le> 1200 * ln 2 - 4 * ln 1200 - (3::real)"
        using ub_ln_1200 ln_2_ge by linarith
  next
    fix x::real
    assume "1200 \<le> x"
    then have "0 < x"
      by simp
    show "((\<lambda>x. x * ln 2 - 4 * ln x - 3 - 2 / 3 * x)
        has_real_derivative ln 2 - 4 / x - 2 / 3) (at x)"
      by (rule derivative_eq_intros refl | simp add: \<open>0 < x\<close>)+
  next
    fix x::real
    assume "1200 \<le> x"
    then have "12 / x \<le> 12 / 1200" by simp
    then have "0 \<le> 0.67 - 4 / x - 2 / 3" by simp
    also have "0.67 \<le> ln (2::real)" using ln_2_ge by simp
    finally show "0 \<le> ln 2 - 4 / x - 2 / 3" by simp
  next
    from assms show "1200 \<le> real n"
      by simp
  qed
  ultimately have "2 / 3 * real n \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  with psi_ubound_3_2[of "n div 3"]
    have "n/6 + psi (n div 3) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
    by simp
  with fact_psi_bound_2_3[of "n"] show ?thesis
    by simp
qed

lemma theta_double_lemma:
  assumes "n \<ge> 1200"
  shows "theta (n div 2) < theta n"
proof -
  from psi_theta[of "n div 2"] psi_pos[of "Discrete.sqrt (n div 2)"]
    have theta_le_psi_n_2: "theta (n div 2) \<le> psi (n div 2)"
    by simp
  have "(Discrete.sqrt n * 18)^2 \<le> 324 * n"
    by simp
  from mult_less_cancel2[of "324" "n" "n"] assms have "324 * n < n^2"
    by (simp add: power2_eq_square)
  with \<open>(Discrete.sqrt n * 18)^2 \<le> 324 * n\<close> have "(Discrete.sqrt n*18)^2 < n^2"
    by presburger
  with power2_less_imp_less assms have "Discrete.sqrt n * 18 < n"
    by blast
  with psi_ubound_3_2[of "Discrete.sqrt n"] have "2 * psi (Discrete.sqrt n) < n / 6"
    by simp
  with psi_theta[of "n"] have psi_lt_theta_n: "psi n - n / 6 < theta n"
    by simp
  from psi_double_lemma[OF assms(1)] have "psi (n div 2) \<le> psi n - n / 6"
    by simp
  with theta_le_psi_n_2 psi_lt_theta_n show ?thesis
    by simp
qed
  

subsection \<open>Proof of the main result\<close>

lemma theta_mono: "mono theta"
  by (auto simp: theta_def [abs_def] intro!: monoI sum_mono2)
  
lemma theta_lessE:
  assumes "theta m < theta n" "m \<ge> 1"
  obtains p where "p \<in> {m<..n}" "prime p"
proof -
  from mono_invE[OF theta_mono assms(1)] have "m \<le> n" by blast
  hence "theta n = theta m + (\<Sum>p\<in>{m<..n}. if prime p then ln (real p) else 0)"
    unfolding theta_def using assms(2)
    by (subst sum.union_disjoint [symmetric]) (auto simp: ivl_disj_un)
  also note assms(1)
  finally have "(\<Sum>p\<in>{m<..n}. if prime p then ln (real p) else 0) \<noteq> 0" by simp
  from sum.not_neutral_contains_not_neutral [OF this] guess p .
  thus ?thesis using that[of p] by (auto intro!: exI[of _ p] split: if_splits)
qed

theorem bertrand:
  fixes   n :: nat
  assumes "n > 1"
  shows   "\<exists>p\<in>{n<..<2*n}. prime p"
proof cases
  assume n_less: "n < 600"
  define prime_constants
    where "prime_constants = {2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631::nat}"
  from \<open>n > 1\<close> n_less have "\<exists>p \<in> prime_constants. n < p \<and> p < 2 * n"
    unfolding bex_simps greaterThanLessThan_iff prime_constants_def by presburger
  moreover have "\<forall>p\<in>prime_constants. prime p" 
    unfolding prime_constants_def ball_simps HOL.simp_thms by (intro conjI; pratt (silent))
  ultimately show ?thesis
    unfolding greaterThanLessThan_def greaterThan_def lessThan_def by blast
next
  assume n: "\<not>(n < 600)"
  from n have "theta n < theta (2 * n)" using theta_double_lemma[of "2 * n"] by simp
  with assms obtain p where "p \<in> {n<..2*n}" "prime p" by (auto elim!: theta_lessE)
  moreover from assms have "\<not>prime (2*n)" by (auto dest!: prime_product)
  with \<open>prime p\<close> have "p \<noteq> 2 * n" by auto
  ultimately show ?thesis
    by auto
qed
  
  
subsection \<open>Proof of Mertens' first theorem\<close>

text \<open>
  The following proof of Mertens' first theorem was ported from John Harrison's HOL Light
  proof by Larry Paulson:
\<close>

lemma sum_integral_ubound_decreasing':
  fixes f :: "real \<Rightarrow> real"
  assumes "m \<le> n"
      and der: "\<And>x. x \<in> {of_nat m - 1..of_nat n} \<Longrightarrow> (g has_field_derivative f x) (at x)"
      and le:  "\<And>x y. \<lbrakk>real m - 1 \<le> x; x \<le> y; y \<le> real n\<rbrakk> \<Longrightarrow> f y \<le> f x"
    shows "(\<Sum>k = m..n. f (of_nat k)) \<le> g (of_nat n) - g (of_nat m - 1)"
proof -
  have "(\<Sum>k = m..n. f (of_nat k)) \<le> (\<Sum>k = m..n. g (of_nat(Suc k) - 1) - g (of_nat k - 1))"
  proof (rule sum_mono, clarsimp)
    fix r
    assume r: "m \<le> r" "r \<le> n"
    hence "\<exists>z>real r - 1. z < real r \<and> g (real r) - g (real r - 1) = (real r - (real r - 1)) * f z"
      using assms by (intro MVT2) auto
    hence "\<exists>z\<in>{of_nat r - 1..of_nat r}. g (real r) - g (real r - 1) = f z" by auto
    then obtain u::real where u: "u \<in> {of_nat r - 1..of_nat r}"
                        and eq: "g r - g (of_nat r - 1) = f u" by blast
    have "real m \<le> u + 1"
      using r u by auto
    then have "f (of_nat r) \<le> f u"
      using r(2) and u by (intro le) auto
    then show "f (of_nat r) \<le> g r - g (of_nat r - 1)"
      by (simp add: eq)
  qed
  also have "\<dots> \<le> g (of_nat n) - g (of_nat m - 1)"
    using \<open>m \<le> n\<close> by (subst sum_Suc_diff) auto
  finally show ?thesis .
qed

lemma Mertens_lemma:
  assumes "n \<noteq> 0"
    shows "\<bar>(\<Sum>d = 1..n. mangoldt d / real d) - ln n\<bar> \<le> 4"
proof -
  have *: "\<lbrakk>abs(s' - nl + n) \<le> a; abs(s' - s) \<le> (k - 1) * n - a\<rbrakk>
        \<Longrightarrow> abs(s - nl) \<le> n * k" for s' s k nl a::real
    by (auto simp: algebra_simps abs_if split: if_split_asm)
  have le: "\<bar>(\<Sum>d=1..n. mangoldt d * floor (n / d)) - n * ln n + n\<bar> \<le> 1 + ln n"
    using ln_fact_bounds ln_fact_conv_mangoldt assms by simp
  have "\<bar>real n * ((\<Sum>d = 1..n. mangoldt d / real d) - ln n)\<bar> =
        \<bar>((\<Sum>d = 1..n. real n * mangoldt d / real d) - n * ln n)\<bar>"
    by (simp add: algebra_simps sum_distrib_left)
  also have "\<dots> \<le> real n * 4"
  proof (rule * [OF le])
    have "\<bar>(\<Sum>d = 1..n. mangoldt d * \<lfloor>n / d\<rfloor>) - (\<Sum>d = 1..n. n * mangoldt d / d)\<bar>
        = \<bar>\<Sum>d = 1..n. mangoldt d * (\<lfloor>n / d\<rfloor> - n / d)\<bar>"
      by (simp add: sum_subtractf algebra_simps)
    also have "\<dots> \<le> psi n" (is "\<bar>?sm\<bar> \<le> ?rhs")
    proof -
      have "-?sm = (\<Sum>d = 1..n. mangoldt d * (n/d - \<lfloor>n/d\<rfloor>))"
        by (simp add: sum_subtractf algebra_simps)
      also have "\<dots> \<le> (\<Sum>d = 1..n. mangoldt d * 1)"
        by (intro sum_mono mult_left_mono mangoldt_nonneg) linarith+
      finally have "-?sm \<le> ?rhs" by (simp add: psi_def)
      moreover
      have "?sm \<le> 0"
        using mangoldt_nonneg by (simp add: mult_le_0_iff sum_nonpos)
      ultimately show ?thesis by (simp add: abs_if)
    qed
    also have "\<dots> \<le> 3/2 * real n"
      by (rule psi_ubound_3_2)
    also have "\<dots>\<le> (4 - 1) * real n - (1 + ln n)"
      using ln_le_minus_one [of n] assms by (simp add: divide_simps)
    finally
    show "\<bar>(\<Sum>d = 1..n. mangoldt d * real_of_int \<lfloor>real n / real d\<rfloor>) -
           (\<Sum>d = 1..n. real n * mangoldt d / real d)\<bar>
          \<le> (4 - 1) * real n - (1 + ln n)" .
  qed
  finally have "\<bar>real n * ((\<Sum>d = 1..n. mangoldt d / real d) - ln n)\<bar> \<le> real n * 4" .
  then show ?thesis
    using assms mult_le_cancel_left_pos by (simp add: abs_mult)
qed

lemma Mertens_mangoldt_versus_ln:
  assumes "I \<subseteq> {1..n}"
  shows "\<bar>(\<Sum>i\<in>I. mangoldt i / i) - (\<Sum>p | prime p \<and> p \<in> I. ln p / p)\<bar> \<le> 3"
        (is "\<bar>?lhs\<bar> \<le> 3")
proof (cases "n = 0")
  case True
  with assms show ?thesis by simp
next
  case False
    have "finite I"
      using assms finite_subset by blast
    have "0 \<le> (\<Sum>i\<in>I. mangoldt i / i - (if prime i then ln i / i else 0))"
      using mangoldt_nonneg by (intro sum_nonneg) simp_all
    moreover have "\<dots> \<le> (\<Sum>i = 1..n. mangoldt i / i - (if prime i then ln i / i else 0))"
      using assms by (intro sum_mono2) (auto simp: mangoldt_nonneg)
    ultimately have *: "\<bar>\<Sum>i\<in>I. mangoldt i / i - (if prime i then ln i / i else 0)\<bar>
                      \<le> \<bar>\<Sum>i = 1..n. mangoldt i / i - (if prime i then ln i / i else 0)\<bar>"
      by linarith
    moreover have "?lhs = (\<Sum>i\<in>I. mangoldt i / i - (if prime i then ln i / i else 0))"
                  "(\<Sum>i = 1..n. mangoldt i / i - (if prime i then ln i / i else 0))
                        = (\<Sum>d = 1..n. mangoldt d / d) - (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p)"
      using sum.inter_restrict [of _ "\<lambda>i. ln (real i) / i" "Collect prime", symmetric]  
       by (force simp: sum_subtractf \<open>finite I\<close> intro: sum.cong)+
    ultimately have "\<bar>?lhs\<bar> \<le> \<bar>(\<Sum>d = 1..n. mangoldt d / d) - 
                          (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p)\<bar>" by linarith
    also have "\<dots> \<le> 3"
    proof -
      have eq_sm: "(\<Sum>i = 1..n. mangoldt i / i) = 
                     (\<Sum>i \<in> {p^k |p k. prime p \<and> p^k \<le> n \<and> k \<ge> 1}. mangoldt i / i)"
      proof (intro sum.mono_neutral_right ballI, goal_cases)
        case (3 i)
        hence "\<not>primepow i" by (auto simp: primepow_def Suc_le_eq)
        thus ?case by (simp add: mangoldt_def)
      qed (auto simp: Suc_le_eq prime_gt_0_nat)
      have "(\<Sum>i = 1..n. mangoldt i / i) - (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p) =
            (\<Sum>i \<in> {p^k |p k. prime p \<and> p^k \<le> n \<and> k \<ge> 2}. mangoldt i / i)"
      proof -
        have eq: "{p ^ k |p k. prime p \<and> p ^ k \<le> n \<and> 1 \<le> k} =
                  {p ^ k |p k. prime p \<and> p ^ k \<le> n \<and> 2 \<le> k} \<union> {p. prime p \<and> p \<in> {1..n}}"
          (is "?A = ?B \<union> ?C")
        proof (intro equalityI subsetI; (elim UnE)?)
          fix x assume "x \<in> ?A"
          then obtain p k where "x = p ^ k" "prime p" "p ^ k \<le> n" "k \<ge> 1" by auto
          thus "x \<in> ?B \<union> ?C"
            by (cases "k \<ge> 2") (auto simp: prime_power_iff Suc_le_eq)
        next
          fix x assume "x \<in> ?B"
          then obtain p k where "x = p ^ k" "prime p" "p ^ k \<le> n" "k \<ge> 1" by auto
          thus "x \<in> ?A" by (auto simp: prime_power_iff Suc_le_eq)
        next
          fix x assume "x \<in> ?C"
          then obtain p where "x = p ^ 1" "1 \<ge> (1::nat)" "prime p" "p ^ 1 \<le> n" by auto
          thus "x \<in> ?A" by blast
        qed
        have eqln: "(\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p) = 
                      (\<Sum>p | prime p \<and> p \<in> {1..n}. mangoldt p / p)"
          by (rule sum.cong) auto
        have "(\<Sum>i \<in> {p^k |p k. prime p \<and> p^k \<le> n \<and> k \<ge> 1}. mangoldt i / i) = 
                (\<Sum>i \<in> {p ^ k |p k. prime p \<and> p ^ k \<le> n \<and> 2 \<le> k} \<union> 
                {p. prime p \<and> p \<in> {1..n}}. mangoldt i / i)" by (subst eq) simp_all
        also have "\<dots> = (\<Sum>i \<in> {p^k |p k. prime p \<and> p^k \<le> n \<and> k \<ge> 2}. mangoldt i / i)
                       + (\<Sum>p | prime p \<and> p \<in> {1..n}. mangoldt p / p)"
          by (intro sum.union_disjoint) (auto simp: prime_power_iff finite_nat_set_iff_bounded_le)
        also have "\<dots> = (\<Sum>i \<in> {p^k |p k. prime p \<and> p^k \<le> n \<and> k \<ge> 2}. mangoldt i / i)
                       + (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p)" by (simp only: eqln)
        finally show ?thesis
          using eq_sm by auto
      qed
      have "(\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p) \<le> (\<Sum>p | prime p \<and> p \<in> {1..n}. mangoldt p / p)"
        using mangoldt_nonneg by (auto intro: sum_mono)
      also have "\<dots> \<le> (\<Sum>i = Suc 0..n. mangoldt i / i)"
        by (intro sum_mono2) (auto simp: mangoldt_nonneg)
      finally have "0 \<le> (\<Sum>i = 1..n. mangoldt i / i) - (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p)"
        by simp
      moreover have "(\<Sum>i = 1..n. mangoldt i / i) - (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p / p) \<le> 3"
                     (is "?M - ?L \<le> 3")
      proof -
        have *: "\<exists>q. \<exists>j\<in>{1..n}. prime q \<and> 1 \<le> q \<and> q \<le> n \<and>
                  (q ^ j = p ^ k \<and> mangoldt (p ^ k) / real p ^ k \<le> ln (real q) / real q ^ j)"
          if "prime p" "p ^ k \<le> n" "1 \<le> k" for p k
        proof -
          have "mangoldt (p ^ k) / real p ^ k \<le> ln p / p ^ k"
            using that by (simp add: divide_simps)
          moreover have "p \<le> n"
            using that self_le_power[of p k] by (simp add: prime_ge_Suc_0_nat)
          moreover have "k \<le> n"
          proof -
            have "k < 2^k"
              using of_nat_less_two_power of_nat_less_numeral_power_cancel_iff by blast
            also have "\<dots> \<le> p^k"
              by (simp add: power_mono prime_ge_2_nat that)
            also have "\<dots> \<le> n"
              by (simp add: that)
            finally show ?thesis by (simp add: that)
          qed
          ultimately show ?thesis
            using prime_ge_1_nat that by auto (use atLeastAtMost_iff in blast)
        qed
        have finite: "finite {p ^ k |p k. prime p \<and> p ^ k \<le> n \<and> 1 \<le> k}"
          by (rule finite_subset[of _ "{..n}"]) auto
        have "?M \<le> (\<Sum>(x, k)\<in>{p. prime p \<and> p \<in> {1..n}} \<times> {1..n}. ln (real x) / real x ^ k)"
          by (subst eq_sm, intro sum_le_included [where i = "\<lambda>(p,k). p^k"])
             (insert * finite, auto)
        also have "\<dots> = (\<Sum>p | prime p \<and> p \<in> {1..n}. (\<Sum>k = 1..n. ln p / p^k))"
          by (subst sum.Sigma) auto
        also have "\<dots> = ?L + (\<Sum>p | prime p \<and> p \<in> {1..n}. (\<Sum>k = 2..n. ln p / p^k))"
          by (simp add: comm_monoid_add_class.sum.distrib sum.atLeast_Suc_atMost numeral_2_eq_2)
        finally have "?M - ?L \<le> (\<Sum>p | prime p \<and> p \<in> {1..n}. (\<Sum>k = 2..n. ln p / p^k))"
          by (simp add: algebra_simps)
        also have "\<dots> = (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p * (\<Sum>k = 2..n. inverse p ^ k))"
          by (simp add: field_simps sum_distrib_left)
        also have "\<dots> = (\<Sum>p | prime p \<and> p \<in> {1..n}. 
                          ln p * (((inverse p)\<^sup>2 - inverse p ^ Suc n) / (1 - inverse p)))"
          by (intro sum.cong refl) (simp add: sum_gp)
        also have "\<dots> \<le> (\<Sum>p | prime p \<and> p \<in> {1..n}. ln p * inverse (real (p * (p - 1))))"
          by (intro sum_mono mult_left_mono)
             (auto simp: divide_simps power2_eq_square of_nat_diff mult_less_0_iff)
        also have "\<dots> \<le> (\<Sum>p = 2..n. ln p * inverse (real (p * (p - 1))))"
          by (rule sum_mono2) (use prime_ge_2_nat in auto)
        also have "\<dots> \<le> (\<Sum>i = 2..n. ln i / (i - 1)\<^sup>2)"
          unfolding divide_inverse power2_eq_square mult.assoc
          by (auto intro: sum_mono mult_left_mono mult_right_mono)
        also have "\<dots> \<le> 3"
        proof (cases "n \<ge> 3")
          case False then show ?thesis
          proof (cases "n \<ge> 2")
            case False then show ?thesis by simp
          next
            case True
            then have "n = 2" using False by linarith
            with ln_le_minus_one [of 2] show ?thesis by simp
          qed
        next
          case True
          have "(\<Sum>i = 3..n. ln (real i) / (real (i - Suc 0))\<^sup>2)
                \<le> (ln (of_nat n - 1)) - (ln (of_nat n)) - (ln (of_nat n) / (of_nat n - 1)) + 2 * ln 2"
          proof -
            have 1: "((\<lambda>z. ln (z - 1) - ln z - ln z / (z - 1)) has_field_derivative ln x / (x - 1)\<^sup>2) (at x)"
              if x: "x \<in> {2..real n}" for x
              by (rule derivative_eq_intros | rule refl | 
                   (use x in \<open>force simp: power2_eq_square divide_simps\<close>))+
            have 2: "ln y / (y - 1)\<^sup>2 \<le> ln x / (x - 1)\<^sup>2" if xy: "2 \<le> x" "x \<le> y" "y \<le> real n" for x y
            proof (cases "x = y")
              case False
              define f' :: "real \<Rightarrow> real"
                where "f' = (\<lambda>u. ((u - 1)\<^sup>2 / u - ln u * (2 * u - 2)) / (u - 1) ^ 4)"
              have f'_altdef: "f' u = inverse u * inverse ((u - 1)\<^sup>2) - 2 * ln u / (u - 1) ^ 3" 
                if u: "u \<in> {x..y}" for u::real unfolding f'_def using u (* TODO ugly *)
                by (simp add: eval_nat_numeral divide_simps) (simp add: algebra_simps)?
              have deriv: "((\<lambda>z. ln z / (z - 1)\<^sup>2) has_field_derivative f' u) (at u)"
                if u: "u \<in> {x..y}" for u::real unfolding f'_def
                by (rule derivative_eq_intros refl | (use u xy in \<open>force simp: divide_simps\<close>))+
              hence "\<exists>z>x. z < y \<and> ln y / (y - 1)\<^sup>2 - ln x / (x - 1)\<^sup>2 = (y - x) * f' z"
                using xy and \<open>x \<noteq> y\<close> by (intro MVT2) auto
              then obtain \<xi>::real where "x < \<xi>" "\<xi> < y"
                and \<xi>: "ln y / (y - 1)\<^sup>2 - ln x / (x - 1)\<^sup>2 = (y - x) * f' \<xi>" by blast
              have "f' \<xi> \<le> 0"
              proof -
                have "2/3 \<le> ln (2::real)" by (fact ln_2_ge')
                also have "\<dots> \<le> ln \<xi>"
                  using \<open>x < \<xi>\<close> xy by auto
                finally have "1 \<le> 2 * ln \<xi>" by simp
                then have *: "\<xi> \<le> \<xi> * (2 * ln \<xi>)"
                  using \<open>x < \<xi>\<close> xy by auto
                hence "\<xi> - 1 \<le> ln \<xi> * 2 * \<xi>" by (simp add: algebra_simps)
                hence "1 / (\<xi> * (\<xi> - 1)\<^sup>2) \<le> ln \<xi> * 2 / (\<xi> - 1) ^ 3"
                  using xy \<open>x < \<xi>\<close> by (simp add: divide_simps power_eq_if)
                thus ?thesis using xy \<open>x < \<xi>\<close> \<open>\<xi> < y\<close> by (subst f'_altdef) (auto simp: divide_simps)
              qed
              then have "(ln y / (y - 1)\<^sup>2 - ln x / (x - 1)\<^sup>2) \<le> 0"
                using \<open>x \<le> y\<close> by (simp add: mult_le_0_iff \<xi>)
              then show ?thesis by simp
            qed simp_all
            show ?thesis
              using sum_integral_ubound_decreasing'
                [OF \<open>3 \<le> n\<close>, of "\<lambda>z. ln(z-1) - ln z - ln z / (z - 1)" "\<lambda>z. ln z / (z-1)\<^sup>2"]
                1 2 \<open>3 \<le> n\<close>
              by (auto simp: in_Reals_norm of_nat_diff)
          qed
          also have "\<dots> \<le> 2"
          proof -
            have "ln (real n - 1) - ln n \<le> 0"  "0 \<le> ln n / (real n - 1)"
              using \<open>3 \<le> n\<close> by auto
            then have "ln (real n - 1) - ln n - ln n / (real n - 1) \<le> 0"
              by linarith
            with ln_2_less_1 show ?thesis by linarith
          qed
          also have "\<dots> \<le> 3 - ln 2"
            using ln_2_less_1 by (simp add: algebra_simps)
        finally show ?thesis
          using True by (simp add: algebra_simps sum.atLeast_Suc_atMost [of 2 n])
      qed
        finally show ?thesis .
      qed
      ultimately show ?thesis
        by linarith
    qed
  finally show ?thesis .
qed

proposition Mertens:
  assumes "n \<noteq> 0"
  shows "\<bar>(\<Sum>p | prime p \<and> p \<le> n. ln p / of_nat p) - ln n\<bar> \<le> 7"
proof -
  have "\<bar>(\<Sum>d = 1..n. mangoldt d / real d) - (\<Sum>p | prime p \<and> p \<in> {1..n}. ln (real p) / real p)\<bar>
             \<le> 7 - 4" using Mertens_mangoldt_versus_ln [of "{1..n}" n] by simp_all
  also have "{p. prime p \<and> p \<in> {1..n}} = {p. prime p \<and> p \<le> n}"
    using atLeastAtMost_iff prime_ge_1_nat by blast
  finally have "\<bar>(\<Sum>d = 1..n. mangoldt d / real d) - (\<Sum>p\<in>\<dots>. ln (real p) / real p)\<bar> \<le> 7 - 4" .
  moreover from assms have "\<bar>(\<Sum>d = 1..n. mangoldt d / real d) - ln n\<bar> \<le> 4"
    by (rule Mertens_lemma)
  ultimately show ?thesis by linarith
qed

end
