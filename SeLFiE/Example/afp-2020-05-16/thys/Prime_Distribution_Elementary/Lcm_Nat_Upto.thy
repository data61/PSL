(*
  File:    Lcm_Nat_Upto.thy
  Author:  Manuel Eberl, TU München

  The LCM of {1..n}, including the relationship Lcm {1..n} = exp (\<psi> n).
*)

section \<open>The LCM of the first $n$ natural numbers\<close>
theory Lcm_Nat_Upto
  imports Prime_Number_Theorem.Prime_Counting_Functions
begin

text \<open>
  In this section, we examine @{term "Lcm {1..(n::nat)}"}. In particular,
  we will show that it is equal to $e^{\psi(n)}$ and thus (by the PNT) $e^{n + o(n)}$.
\<close>
lemma multiplicity_Lcm:
  fixes A :: "'a :: {semiring_Gcd, factorial_semiring_gcd} set"
  assumes "finite A" "A \<noteq> {}" "prime p" "0 \<notin> A"
  shows   "multiplicity p (Lcm A) = Max (multiplicity p ` A)"
  using assms
proof (induction A rule: finite_ne_induct)
  case (insert x A)
  have "Lcm (insert x A) = lcm x (Lcm A)" by simp
  also have "multiplicity p \<dots> = Max (multiplicity p ` insert x A)"
    using insert by (subst multiplicity_lcm) (auto simp: Lcm_0_iff)
  finally show ?case by simp
qed auto

text \<open>
  The multiplicity of any prime \<open>p\<close> in @{term "Lcm {1..(n::nat)}"} differs from
  that in @{term "Lcm {1..(n - 1 :: nat)}"} iff \<open>n\<close> is a power of \<open>p\<close>, in which case
  it is greater by 1.
\<close>
lemma multiplicity_Lcm_atLeast1AtMost_Suc:
  fixes p n :: nat
  assumes p: "prime p" and n: "n > 0"
  shows "multiplicity p (Lcm {1..Suc n}) =
           (if \<exists>k. Suc n = p ^ k then 1 else 0) + multiplicity p (Lcm {1..n})"
proof -
  define k where "k = Max (multiplicity p ` {1..n})"
  define l where "l = multiplicity p (Suc n)"
  have eq: "{1..Suc n} = insert (Suc n) {1..n}" by auto
  from \<open>prime p\<close> have "p > 1" by (auto dest: prime_gt_1_nat)

  have "multiplicity p (Lcm {1..Suc n}) = Max (multiplicity p ` {1..Suc n})"
    using assms by (subst multiplicity_Lcm) auto
  also have "multiplicity p ` {1..Suc n} =
               insert (multiplicity p (Suc n)) (multiplicity p ` {1..n})"
    by (simp only: eq image_insert)
  also have "Max \<dots> = max l k"
    unfolding l_def k_def using assms by (subst Max.insert) auto
  also have "\<dots> = (if \<exists>k. Suc n = p ^ k then 1 else 0) + k"
  proof (cases "\<exists>k. Suc n = p ^ k")
    case False
    have "p ^ l dvd Suc n"
      unfolding l_def by (intro multiplicity_dvd)
    hence "p ^ l \<le> Suc n"
      unfolding l_def by (intro dvd_imp_le multiplicity_dvd) auto
    moreover have "Suc n \<noteq> p ^ l" using False by blast
    ultimately have "p ^ l < Suc n" by linarith
    moreover have "p ^ l > 0" using \<open>p > 1\<close> by (intro zero_less_power) auto
    ultimately have "l = multiplicity p (p ^ l)" and "p ^ l \<in> {1..n}"
      using \<open>prime p\<close> by auto
    hence "l \<le> k" unfolding k_def by (intro Max.coboundedI) auto
    with False show ?thesis by (simp add: l_def k_def)
  next
    case True
    then obtain x where x: "Suc n = p ^ x" by blast
    from x and \<open>n > 0\<close> have "x > 0" by (intro Nat.gr0I) auto
    from x have [simp]: "l = x" using \<open>prime p\<close> by (simp add: l_def)
    have "x = k + 1"
    proof (intro antisym)
      have "p ^ (x - 1) < Suc n"
        using \<open>x > 0\<close> \<open>p > 1\<close> unfolding x by (intro power_strict_increasing) auto
      moreover have "p ^ (x - 1) > 0"
        using \<open>p > 1\<close> by (intro zero_less_power) auto
      ultimately have "multiplicity p (p ^ (x - 1)) = x - 1" and "p ^ (x - 1) \<in> {1..n}"
        using \<open>prime p\<close> by auto
      hence "x - 1 \<le> k"
        unfolding k_def by (intro Max.coboundedI) force+
      thus "x \<le> k + 1" by linarith
    next
      have "multiplicity p y < x" if "y \<in> {1..n}" for y
      proof -
        have "p ^ multiplicity p y \<le> y"
          using that by (intro dvd_imp_le multiplicity_dvd) auto
        also have "\<dots> < Suc n" using that by simp
        also have "\<dots> = p ^ x" by (fact x)
        finally show "multiplicity p y < x"
          using \<open>p > 1\<close> by (subst (asm) power_strict_increasing_iff)
      qed
      hence "k < x"
        using \<open>n > 0\<close> unfolding k_def by (subst Max_less_iff) auto
      thus "k + 1 \<le> x" by simp
    qed
    thus ?thesis using True by simp
  qed
  also have "k = multiplicity p (Lcm {1..n})"
    unfolding k_def using \<open>n > 0\<close> and \<open>prime p\<close> by (subst multiplicity_Lcm) auto
  finally show ?thesis .
qed

text \<open>
  Consequently, \<^term>\<open>Lcm {1..(n::nat)}\<close> differs from \<^term>\<open>Lcm {1..(n-1::nat)}\<close>
  iff \<open>n\<close> is of the form $p^k$ for some prime $p$, in which case it is greater by a factor
  of \<open>p\<close>.
\<close>
lemma Lcm_atLeast1AtMost_Suc:
  "Lcm {1..Suc n} = Lcm {1..n} * (if primepow (Suc n) then aprimedivisor (Suc n) else 1)"
proof (cases "n > 0")
  case True
  show ?thesis
  proof (rule multiplicity_eq_nat)
    fix p :: nat assume "prime p"
    define x where "x = (if primepow (Suc n) then aprimedivisor (Suc n) else 1)"
    have "x > 0"
      using \<open>n > 0\<close> by (auto simp: x_def intro!: aprimedivisor_pos_nat)
  
    have "multiplicity p (Lcm {1..n} * x) = multiplicity p (Lcm {1..n}) + multiplicity p x"
      using \<open>prime p\<close> \<open>x > 0\<close> by (subst prime_elem_multiplicity_mult_distrib) auto
    also consider "\<exists>k. Suc n = p ^ k" | "primepow (Suc n)" "\<not>(\<exists>k. Suc n = p ^ k)" 
                | "\<not>primepow (Suc n)" by blast
    hence "multiplicity p x = (if \<exists>k. Suc n = p ^ k then 1 else 0)"
    proof cases
      assume "\<exists>k. Suc n = p ^ k"
      thus ?thesis using \<open>prime p\<close> \<open>n > 0\<close>
        by (auto simp: x_def aprimedivisor_prime_power intro!: Nat.gr0I)
    next
      assume *: "primepow (Suc n)" "\<nexists>k. Suc n = p ^ k"
      then obtain q k where qk: "prime q" "Suc n = q ^ k" "k > 0" "q \<noteq> p"
        by (auto simp: primepow_def)
      thus ?thesis using \<open>prime p\<close>
        by (subst *) (auto simp: x_def aprimedivisor_prime_power prime_multiplicity_other)
    next
      assume *: "\<not>primepow (Suc n)"
      hence **: "\<nexists>k. Suc n = p ^ k" using \<open>prime p\<close> \<open>n > 0\<close> by auto
      from * show ?thesis unfolding x_def
        by (subst **) auto
    qed
    also have "multiplicity p (Lcm {1..n}) + \<dots> = multiplicity p (Lcm {1..Suc n})"
      using \<open>prime p\<close> \<open>n > 0\<close> by (subst multiplicity_Lcm_atLeast1AtMost_Suc) (auto simp: x_def)
    finally show "multiplicity p (Lcm {1..Suc n}) = multiplicity p (Lcm {1..n} * x)" ..
  qed (use \<open>n > 0\<close> in \<open>auto intro!: Nat.gr0I dest: aprimedivisor_pos_nat\<close>) 
qed auto

text \<open>
  It follows by induction that $\text{Lcm}\ \{1..n\} = e^{\psi(n)}$.
\<close>
lemma Lcm_atLeast1AtMost_conv_\<psi>:
  includes prime_counting_notation
  shows "real (Lcm {1..n}) = exp (\<psi> (real n))"
proof (induction n)
  case (Suc n)
  have "real (Lcm {1..Suc n}) =
          real (Lcm {1..n}) * (if primepow (Suc n) then aprimedivisor (Suc n) else 1)"
    by (subst Lcm_atLeast1AtMost_Suc) auto
  also {
    assume "primepow (Suc n)"
    hence "Suc n > Suc 0" by (rule primepow_gt_Suc_0)
    hence "aprimedivisor (Suc n) > 0" by (intro aprimedivisor_pos_nat) auto
  }
  hence "(if primepow (Suc n) then aprimedivisor (Suc n) else 1) = exp (mangoldt (Suc n))"
    by (simp add: mangoldt_def)
  also have "Lcm {1..n} * \<dots> = exp (\<psi> (real n + 1))"
    using Suc.IH by (simp add: primes_psi_def sum_upto_plus1 exp_add)
  finally show ?case by (simp add: add_ac)
qed simp_all

lemma Lcm_upto_real_conv_\<psi>:
  includes prime_counting_notation
  shows "real (Lcm {1..nat \<lfloor>x\<rfloor>}) = exp (\<psi> x)"
  by (subst Lcm_atLeast1AtMost_conv_\<psi>) (simp add: primes_psi_def sum_upto_altdef)

end