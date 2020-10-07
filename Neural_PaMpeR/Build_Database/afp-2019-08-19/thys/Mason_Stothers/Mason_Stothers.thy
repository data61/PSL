(*
  File:     Mason_Stothers.thy
  Author:   Manuel Eberl, TU München

  A simple proof of the Mason--Stothers theorem, the analogue of the abc conjecture
  for polynomials.
*)
section \<open>The Mason--Stother's Theorem\<close>
theory Mason_Stothers
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

subsection \<open>Auxiliary material\<close>

(* TODO Rename this to fps_radical or whatever *)
hide_const (open) Formal_Power_Series.radical

lemma degree_div:
  assumes "a dvd b"
  shows   "degree (b div a) = degree b - degree a"
  using assms by (cases "a = 0"; cases "b = 0") (auto elim!: dvdE simp: degree_mult_eq)

lemma degree_pderiv_le:
  shows   "degree (pderiv p) \<le> degree p - 1"
  by (rule degree_le, cases "degree p = 0") (auto simp: coeff_pderiv coeff_eq_0)

lemma degree_pderiv_less:
  assumes "pderiv p \<noteq> 0"
  shows   "degree (pderiv p) < degree p"
proof -
  have "degree (pderiv p) \<le> degree p - 1"
    by (rule degree_pderiv_le)
  also have "degree p \<noteq> 0"
    using assms by (auto intro!: Nat.gr0I elim!: degree_eq_zeroE)
  hence "degree p - 1 < degree p" by simp
  finally show ?thesis .
qed

lemma pderiv_eq_0:
  assumes "degree p = 0"
  shows   "pderiv p = 0"
  using assms by (auto elim!: degree_eq_zeroE)


subsection \<open>Definition of a radical\<close>

text \<open>
  The following definition of a radical is generic for any factorial semiring.
\<close>

context factorial_semiring
begin

definition radical :: "'a \<Rightarrow> 'a" where
  "radical x = (if x = 0 then 0 else \<Prod>(prime_factors x))"

lemma radical_0 [simp]: "radical 0 = 0"
  by (simp add: radical_def)

lemma radical_nonzero: "x \<noteq> 0 \<Longrightarrow> radical x = \<Prod>(prime_factors x)"
  by (simp add: radical_def)

lemma radical_eq_0_iff [simp]: "radical x = 0 \<longleftrightarrow> x = 0"
  by (auto simp: radical_def)

lemma prime_factorization_radical [simp]:
  assumes "x \<noteq> 0"
  shows   "prime_factorization (radical x) = mset_set (prime_factors x)"
proof -
  have "prime_factorization (radical x) = (\<Sum>p\<in>prime_factors x. prime_factorization p)"
    unfolding radical_def using assms by (auto intro!: prime_factorization_prod)
  also have "\<dots> = (\<Sum>p\<in>prime_factors x. {#p#})"
    by (intro Groups_Big.sum.cong) (auto intro!: prime_factorization_prime)
  also have "\<dots> = mset_set (prime_factors x)" by simp
  finally show ?thesis .
qed

lemma prime_factors_radical [simp]: "x \<noteq> 0 \<Longrightarrow> prime_factors (radical x) = prime_factors x"
  by simp

lemma radical_dvd [simp, intro]: "radical x dvd x"
  by (cases "x = 0") (force intro: prime_factorization_subset_imp_dvd mset_set_set_mset_msubset)+

lemma multiplicity_radical_prime:
  assumes "prime p" "x \<noteq> 0"
  shows   "multiplicity p (radical x) = (if p dvd x then 1 else 0)"
proof -
  have "multiplicity p (radical x) = (\<Sum>q\<in>prime_factors x. multiplicity p q)"
    using assms unfolding radical_def
    by (auto simp: prime_elem_multiplicity_prod_distrib)
  also have "\<dots> = (\<Sum>q\<in>prime_factors x. if p = q then 1 else 0)"
    using assms by (intro Groups_Big.sum.cong) (auto intro!: prime_multiplicity_other)
  also have "\<dots> = (if p \<in> prime_factors x then 1 else 0)" by simp
  also have "\<dots> = (if p dvd x then 1 else 0)"
    using assms by (auto simp: prime_factors_dvd)
  finally show ?thesis .
qed

lemma radical_1 [simp]: "radical 1 = 1"
  by (simp add: radical_def)

lemma radical_unit [simp]: "is_unit x \<Longrightarrow> radical x = 1"
  by (auto simp: radical_def prime_factorization_unit)

lemma prime_factors_power:
  assumes "n > 0"
  shows   "prime_factors (x ^ n) = prime_factors x"
  using assms by (cases "x = 0") (auto simp: prime_factors_dvd zero_power prime_dvd_power_iff)

lemma radical_power [simp]: "n > 0 \<Longrightarrow> radical (x ^ n) = radical x"
  by (auto simp add: radical_def prime_factors_power)

end

context factorial_semiring_gcd
begin

lemma radical_mult_coprime:
  assumes "coprime a b"
  shows   "radical (a * b) = radical a * radical b"
proof (cases "a = 0 \<or> b = 0")
  case False
  with assms have "prime_factors a \<inter> prime_factors b = {}"
    using not_prime_unit coprime_common_divisor by (auto simp: prime_factors_dvd)
  hence "\<Prod>(prime_factors a \<union> prime_factors b) = \<Prod>(prime_factors a) * \<Prod>(prime_factors b)"
    by (intro prod.union_disjoint) auto
  with False show ?thesis by (simp add: radical_def prime_factorization_mult)
qed auto

lemma multiplicity_le_imp_dvd':
  assumes "x \<noteq> 0" "\<And>p. p \<in> prime_factors x \<Longrightarrow> multiplicity p x \<le> multiplicity p y"
  shows   "x dvd y"
proof (rule multiplicity_le_imp_dvd)
  fix p assume "prime p"
  thus "multiplicity p x \<le> multiplicity p y" using assms(1) assms(2)[of p] 
    by (cases "p dvd x") (auto simp: prime_factors_dvd not_dvd_imp_multiplicity_0)
qed fact+

end


subsection \<open>Main result\<close>

text \<open>
  The following proofs are basically a one-to-one translation of Franz Lemmermeyer's
  presentation~\cite{lemmermeyer05} of Snyder's proof of the Mason--Stothers theorem.
\<close>
lemma prime_power_dvd_pderiv:
  fixes f p :: "'a :: {factorial_ring_gcd, field} poly"
  assumes "prime_elem p"
  defines "n \<equiv> multiplicity p f - 1"
  shows   "p ^ n dvd pderiv f"
proof (cases "p dvd f \<and> f \<noteq> 0")
  case True
  hence "multiplicity p f > 0" using assms
    by (subst prime_multiplicity_gt_zero_iff) auto
  hence Suc_n: "Suc n = multiplicity p f" by (simp add: n_def)
  define g where "g = f div p ^ Suc n"
  have "p ^ Suc n dvd f" unfolding Suc_n by (rule multiplicity_dvd)
  hence f_eq: "f = p ^ Suc n * g" by (simp add: g_def)
  also have "pderiv \<dots> = p ^ n * (smult (of_nat (Suc n)) (pderiv p * g) + p * pderiv g)"
    by (simp only: pderiv_mult pderiv_power_Suc) (simp add: algebra_simps)
  also have "p ^ n dvd \<dots>" by simp
  finally show ?thesis .
qed (auto simp: n_def not_dvd_imp_multiplicity_0)

lemma poly_div_radical_dvd_pderiv:
  fixes p :: "'a :: {factorial_ring_gcd, field} poly"
  shows "p div radical p dvd pderiv p"
proof (cases "pderiv p = 0")
  case False
  hence "p \<noteq> 0" by auto
  show ?thesis
  proof (rule multiplicity_le_imp_dvd')
    fix q :: "'a poly" assume q: "q \<in> prime_factors (p div radical p)"
    hence "q dvd p div radical p" by auto
    also from \<open>p \<noteq> 0\<close> have "\<dots> dvd p" by (subst div_dvd_iff_mult) auto
    finally have "q dvd p" .

    have "p = p div radical p * radical p" by simp
    also from q and \<open>p \<noteq> 0\<close> have "multiplicity q \<dots> = Suc (multiplicity q (p div radical p))"
      by (subst prime_elem_multiplicity_mult_distrib)
         (auto simp: dvd_div_eq_0_iff multiplicity_radical_prime \<open>q dvd p\<close> prime_factors_dvd)
    finally have "multiplicity q (p div radical p) \<le> multiplicity q p - 1" by simp
    also have "\<dots> \<le> multiplicity q (pderiv p)" using \<open>pderiv p \<noteq> 0\<close> and q and \<open>p \<noteq> 0\<close>
      by (intro multiplicity_geI prime_power_dvd_pderiv)
         (auto simp: prime_factors_dvd dvd_div_eq_0_iff)
    finally show "multiplicity q (p div radical p) \<le> multiplicity q (pderiv p)" .
  qed (insert \<open>p \<noteq> 0\<close>, auto simp: dvd_div_eq_0_iff)
qed auto

lemma degree_pderiv_mult_less:
  assumes "pderiv C \<noteq> 0"
  shows   "degree (pderiv C * B) < degree B + degree C"
proof -
  have "degree (pderiv C * B) \<le> degree (pderiv C) + degree B"
    by (rule degree_mult_le)
  also from assms have "degree (pderiv C) < degree C" by (rule degree_pderiv_less)
  finally show ?thesis by simp
qed

lemma Mason_Stothers_aux:
  fixes A B C :: "'a :: {factorial_ring_gcd, field} poly"
  assumes nz: "A \<noteq> 0" "B \<noteq> 0" "C \<noteq> 0" and sum: "A + B + C = 0" and coprime: "Gcd {A, B, C} = 1" 
     and deg_ge: "degree A \<ge> degree (radical (A * B * C))"
   shows "pderiv A = 0" "pderiv B = 0" "pderiv C = 0"
proof -
  have C_eq: "C = -A - B" "-C = A + B" using sum by algebra+
  from coprime have "gcd A (gcd B (-C)) = 1" by simp
  also note C_eq(2)
  finally have "coprime A B" by (simp add: gcd.commute add.commute[of A B] coprime_iff_gcd_eq_1)
  hence "coprime A (-C)" "coprime B (-C)"
    unfolding C_eq by (simp_all add: gcd.commute[of B A] gcd.commute[of B "A + B"]
                                     add.commute coprime_iff_gcd_eq_1)
  hence "coprime A C" "coprime B C" by simp_all
  note coprime = coprime \<open>coprime A B\<close> this
  have coprime1: "coprime (A div radical A) (B div radical B)"
    by (rule coprime_divisors[OF _ _ \<open>coprime A B\<close>]) (insert nz, auto simp: div_dvd_iff_mult)
  have coprime2: "coprime (A div radical A) (C div radical C)"
    by (rule coprime_divisors[OF _ _ \<open>coprime A C\<close>]) (insert nz, auto simp: div_dvd_iff_mult)
  have coprime3: "coprime (B div radical B) (C div radical C)"
    by (rule coprime_divisors[OF _ _ \<open>coprime B C\<close>]) (insert nz, auto simp: div_dvd_iff_mult)
  have coprime4: "coprime (A div radical A * (B div radical B)) (C div radical C)"
    using coprime2 coprime3 by (subst coprime_mult_left_iff) auto

  have eq: "A * pderiv B - pderiv A * B = pderiv C * B - C * pderiv B"
    by (simp add: C_eq pderiv_add pderiv_diff pderiv_minus algebra_simps)

  have "A div radical A dvd (A * pderiv B - pderiv A * B)"
    using nz by (intro dvd_diff dvd_mult2 poly_div_radical_dvd_pderiv) (auto simp: div_dvd_iff_mult)
  with eq have "A div radical A dvd (pderiv C * B - C * pderiv B)" by simp
  moreover have "C div radical C dvd (pderiv C * B - C * pderiv B)"
    using nz by (intro dvd_diff dvd_mult2 poly_div_radical_dvd_pderiv) (auto simp: div_dvd_iff_mult)
  moreover have "B div radical B dvd (pderiv C * B - C * pderiv B)"
    using nz by (intro dvd_diff dvd_mult poly_div_radical_dvd_pderiv) (auto simp: div_dvd_iff_mult)
  ultimately have "(A div radical A) * (B div radical B) * (C div radical C) dvd 
                     (pderiv C * B - C * pderiv B)" using coprime coprime1 coprime4
    by (intro divides_mult) auto
  also have "(A div radical A) * (B div radical B) * (C div radical C) =
               (A * B * C) div (radical A * radical B * radical C)"
    by (simp add: div_mult_div_if_dvd mult_dvd_mono)
  also have "radical A * radical B * radical C = radical (A * B) * radical C"
    using coprime by (subst radical_mult_coprime) auto
  also have "\<dots> = radical (A * B * C)"
    using coprime by (subst radical_mult_coprime [symmetric]) auto
  finally have dvd: "((A * B * C) div radical (A * B * C)) dvd (pderiv C * B - C * pderiv B)" . 

  have "pderiv B = 0 \<and> pderiv C = 0"
  proof (rule ccontr)
    assume "\<not>(pderiv B = 0 \<and> pderiv C = 0)"
    hence *: "pderiv B \<noteq> 0 \<or> pderiv C \<noteq> 0" by blast

    have "degree (pderiv C * B - C * pderiv B) \<le> 
            max (degree (pderiv C * B)) (degree (C * pderiv B))" by (rule degree_diff_le_max)
    also have "\<dots> < degree B + degree C"
      using degree_pderiv_mult_less[of B C] degree_pderiv_mult_less[of C B] *
      by (cases "pderiv B = 0"; cases "pderiv C = 0") (auto simp add: algebra_simps)
    also have "degree B + degree C = degree (B * C)"
      using nz by (subst degree_mult_eq) auto
    also have "\<dots> = degree (A * (B * C)) - degree A"
      using nz by (subst (2) degree_mult_eq) auto
    also have "\<dots> \<le> degree (A * B * C) - degree (radical (A * B * C))" unfolding mult.assoc
      using assms by (intro diff_le_mono2) (auto simp: mult_ac)
    also have "\<dots> = degree ((A * B * C) div radical (A * B * C))"
      by (intro degree_div [symmetric]) auto
    finally have less: "degree (pderiv C * B - C * pderiv B) <
                          degree (A * B * C div radical (A * B * C))" by simp

    have eq': "pderiv C * B - C * pderiv B = 0"
    proof (rule ccontr)
      assume "pderiv C * B - C * pderiv B \<noteq> 0"
      hence "degree (A * B * C div radical (A * B * C)) \<le> degree (pderiv C * B - C * pderiv B)"
        using dvd by (intro dvd_imp_degree_le) auto
      with less show False by linarith
    qed
    from * show False
    proof (elim disjE)
      assume [simp]: "pderiv C \<noteq> 0"
      have "C dvd C * pderiv B" by simp
      also from eq' have "\<dots> = pderiv C * B" by simp
      finally have "C dvd pderiv C" using coprime
        by (subst (asm) coprime_dvd_mult_left_iff) (auto simp: coprime_commute)
      hence "degree C \<le> degree (pderiv C)" by (intro dvd_imp_degree_le) auto
      moreover have "degree (pderiv C) < degree C" by (intro degree_pderiv_less) auto
      ultimately show False by simp
    next
      assume [simp]: "pderiv B \<noteq> 0"
      have "B dvd B * pderiv C" by simp
      also from eq' have "\<dots> = pderiv B * C" by (simp add: mult_ac)
      finally have "B dvd pderiv B" using coprime
        by (subst (asm) coprime_dvd_mult_left_iff) auto
      hence "degree B \<le> degree (pderiv B)" by (intro dvd_imp_degree_le) auto
      moreover have "degree (pderiv B) < degree B" by (intro degree_pderiv_less) auto
      ultimately show False by simp
    qed
  qed
  with eq and nz show "pderiv A = 0" "pderiv B = 0" "pderiv C = 0" by auto
qed

theorem Mason_Stothers:
  fixes A B C :: "'a :: {factorial_ring_gcd, field} poly"
  assumes nz: "A \<noteq> 0" "B \<noteq> 0" "C \<noteq> 0" "\<exists>p\<in>{A,B,C}. pderiv p \<noteq> 0" 
      and sum: "A + B + C = 0" and coprime: "Gcd {A, B, C} = 1" 
    shows "Max {degree A, degree B, degree C} < degree (radical (A * B * C))"
proof -
  have "degree A < degree (radical (A * B * C))"
    if "\<forall>p\<in>{A,B,C}. p \<noteq> 0" "\<exists>p\<in>{A,B,C}. pderiv p \<noteq> 0" "sum_mset {#A,B,C#} = 0" "Gcd {A, B, C} = 1"
    for A B C :: "'a poly"
  proof (rule ccontr)
    assume "\<not>(degree A < degree (radical (A * B * C)))"
    hence "degree A \<ge> degree (radical (A * B * C))" by simp
    with Mason_Stothers_aux[of A B C] that show False by (auto simp: add_ac)
  qed
  from this[of A B C] this[of B C A] this[of C A B] assms show ?thesis
    by (simp only: insert_commute mult_ac add_ac) (auto simp: add_ac mult_ac)
qed

text \<open>
  The result can be simplified a bit more in fields of characteristic 0:
\<close>
corollary Mason_Stothers_char_0:
  fixes A B C :: "'a :: {factorial_ring_gcd, field_char_0} poly"
  assumes nz: "A \<noteq> 0" "B \<noteq> 0" "C \<noteq> 0" and deg: "\<exists>p\<in>{A,B,C}. degree p \<noteq> 0"
      and sum: "A + B + C = 0" and coprime: "Gcd {A, B, C} = 1" 
    shows "Max {degree A, degree B, degree C} < degree (radical (A * B * C))"
proof -
  from deg have "\<exists>p\<in>{A,B,C}. pderiv p \<noteq> 0"
    by (auto simp: pderiv_eq_0_iff)
  from Mason_Stothers[OF assms(1-3) this assms(5-)] show ?thesis .
qed

text \<open>
  As a nice corollary, we get a kind of analogue of Fermat's last theorem for polynomials:
  Given non-zero polynomials $A$, $B$, $C$ with $A ^ n + B ^ n + C ^ n = 0$ on lowest terms, 
  we must either have $n \leq 2$ or $(A ^ n)' = (B ^ n)' = (C ^ n)' = 0$.

  In the case of a field with characteristic 0, this last possibility is equivalent to 
  $A$, $B$, and $C$ all being constant.
\<close>
corollary fermat_poly:
  fixes A B C :: "'a :: {factorial_ring_gcd,field} poly"
  assumes sum: "A ^ n + B ^ n + C ^ n = 0" and cop: "Gcd {A, B, C} = 1"
  assumes nz:  "A \<noteq> 0" "B \<noteq> 0" "C \<noteq> 0"    and deg: "\<exists>p\<in>{A,B,C}. pderiv (p ^ n) \<noteq> 0"
  shows "n \<le> 2"
proof (rule ccontr)
  assume "\<not>(n \<le> 2)"
  hence "n > 2" by simp
  have "Max {degree (A ^ n), degree (B ^ n), degree (C ^ n)} < 
          degree (radical (A ^ n * B ^ n * C ^ n))" (is "_ < ?d")
    using assms by (intro Mason_Stothers) (auto simp: degree_power_eq gcd_exp)
  hence "Max {degree (A ^ n), degree (B ^ n), degree (C ^ n)} + 1 \<le> ?d" by linarith
  hence "n * degree A + 1 \<le> ?d" "n * degree B + 1 \<le> ?d" "n * degree C + 1 \<le> ?d"
    using assms by (simp_all add: degree_power_eq)
  hence "n * (degree A + degree B + degree C) + 3 \<le> 3 * ?d"
    unfolding ring_distribs by linarith
  also have "A ^ n * B ^ n * C ^ n = (A * B * C) ^ n" by (simp add: mult_ac power_mult_distrib)
  also have "radical \<dots> = radical (A * B * C)"
    using \<open>n > 2\<close> by simp
  also have "degree (radical (A * B * C)) \<le> degree (A * B * C)"
    using nz by (intro dvd_imp_degree_le) auto
  also have "\<dots> = degree A + degree B + degree C"
    using nz by (simp add: degree_mult_eq)
  finally have "(3 - n) * (degree A + degree B + degree C) \<ge> 3"
    by (simp add: algebra_simps)
  hence "3 - n \<noteq> 0" by (intro notI) auto
  hence "n < 3" by simp
  with \<open>n > 2\<close> show False by simp
qed

corollary fermat_poly_char_0:
  fixes A B C :: "'a :: {factorial_ring_gcd,field_char_0} poly"
  assumes sum: "A ^ n + B ^ n + C ^ n = 0" and cop: "Gcd {A, B, C} = 1"
  assumes nz:  "A \<noteq> 0" "B \<noteq> 0" "C \<noteq> 0"    and deg: "\<exists>p\<in>{A,B,C}. degree p > 0"
  shows "n \<le> 2"
proof (rule ccontr)
  assume *: "\<not>(n \<le> 2)"
  with nz and deg have "\<exists>p\<in>{A,B,C}. pderiv (p ^ n) \<noteq> 0"
    by (auto simp: pderiv_eq_0_iff degree_power_eq)
  from fermat_poly[OF assms(1-5) this] and * show False by simp
qed

end