(*
  File:    Gaussian_Integers.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Gaussian Integers\<close>
theory Gaussian_Integers
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
begin

subsection \<open>Auxiliary material\<close>

lemma coprime_iff_prime_factors_disjoint:
  fixes x y :: "'a :: factorial_semiring"
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows "coprime x y \<longleftrightarrow> prime_factors x \<inter> prime_factors y = {}"
proof 
  assume "coprime x y"
  have False if "p \<in> prime_factors x" "p \<in> prime_factors y" for p
  proof -
    from that assms have "p dvd x" "p dvd y"
      by (auto simp: prime_factors_dvd)
    with \<open>coprime x y\<close> have "p dvd 1"
      using coprime_common_divisor by auto
    with that assms show False by (auto simp: prime_factors_dvd)
  qed
  thus "prime_factors x \<inter> prime_factors y = {}" by auto
next
  assume disjoint: "prime_factors x \<inter> prime_factors y = {}"
  show "coprime x y"
  proof (rule coprimeI)
    fix d assume d: "d dvd x" "d dvd y"
    show "is_unit d"
    proof (rule ccontr)
      assume "\<not>is_unit d"
      moreover from this and d assms have "d \<noteq> 0" by auto
      ultimately obtain p where p: "prime p" "p dvd d"
        using prime_divisor_exists by auto
      with d and assms have "p \<in> prime_factors x \<inter> prime_factors y"
        by (auto simp: prime_factors_dvd)
      with disjoint show False by auto
    qed
  qed
qed

lemma product_dvd_irreducibleD:
  fixes a b x :: "'a :: algebraic_semidom"
  assumes "irreducible x"
  assumes "a * b dvd x"
  shows "a dvd 1 \<or> b dvd 1"
proof -
  from assms obtain c where "x = a * b * c"
    by auto
  hence "x = a * (b * c)"
    by (simp add: mult_ac)
  from irreducibleD[OF assms(1) this] show "a dvd 1 \<or> b dvd 1"
    by (auto simp: is_unit_mult_iff)
qed

lemma prime_elem_mult_dvdI:
  assumes "prime_elem p" "p dvd c" "b dvd c" "\<not>p dvd b"
  shows   "p * b dvd c"
proof -
  from assms(3) obtain a where c: "c = a * b"
    using mult.commute by blast
  with assms(2) have "p dvd a * b"
    by simp
  with assms have "p dvd a"
    by (subst (asm) prime_elem_dvd_mult_iff) auto
  with c show ?thesis by (auto intro: mult_dvd_mono)
qed

lemma prime_elem_power_mult_dvdI:
  fixes p :: "'a :: algebraic_semidom"
  assumes "prime_elem p" "p ^ n dvd c" "b dvd c" "\<not>p dvd b"
  shows   "p ^ n * b dvd c"
proof (cases "n = 0")
  case False
  from assms(3) obtain a where c: "c = a * b"
    using mult.commute by blast
  with assms(2) have "p ^ n dvd b * a"
    by (simp add: mult_ac)
  hence "p ^ n dvd a"
    by (rule prime_power_dvd_multD[OF assms(1)]) (use assms False in auto)
  with c show ?thesis by (auto intro: mult_dvd_mono)
qed (use assms in auto)

lemma prime_mod_4_cases:
  fixes p :: nat
  assumes "prime p"
  shows   "p = 2 \<or> [p = 1] (mod 4) \<or> [p = 3] (mod 4)"
proof (cases "p = 2")
  case False
  with prime_gt_1_nat[of p] assms have "p > 2" by auto
  have "\<not>4 dvd p"
    using assms product_dvd_irreducibleD[of p 2 2]
    by (auto simp: prime_elem_iff_irreducible simp flip: prime_elem_nat_iff)
  hence "p mod 4 \<noteq> 0"
    by (auto simp: mod_eq_0_iff_dvd)
  moreover have "p mod 4 \<noteq> 2"
  proof
    assume "p mod 4 = 2"
    hence "p mod 4 mod 2 = 0"
      by (simp add: cong_def)
    thus False using \<open>prime p\<close> \<open>p > 2\<close> prime_odd_nat[of p]
      by (auto simp: mod_mod_cancel)
  qed
  moreover have "p mod 4 \<in> {0,1,2,3}"
    by auto
  ultimately show ?thesis by (auto simp: cong_def)
qed auto

lemma of_nat_prod_mset: "of_nat (prod_mset A) = prod_mset (image_mset of_nat A)"
  by (induction A) auto

lemma multiplicity_0_left [simp]: "multiplicity 0 x = 0"
  by (cases "x = 0") (auto simp: not_dvd_imp_multiplicity_0)

lemma is_unit_power [intro]: "is_unit x \<Longrightarrow> is_unit (x ^ n)"
  by (subst is_unit_power_iff) auto

lemma (in factorial_semiring) pow_divides_pow_iff:
  assumes "n > 0"
  shows   "a ^ n dvd b ^ n \<longleftrightarrow> a dvd b"
proof (cases "b = 0")
  case False
  show ?thesis
  proof
    assume dvd: "a ^ n dvd b ^ n"
    with \<open>b \<noteq> 0\<close> have "a \<noteq> 0"
      using \<open>n > 0\<close> by (auto simp: power_0_left)
    show "a dvd b"
    proof (rule multiplicity_le_imp_dvd)
      fix p :: 'a assume p: "prime p"
      from dvd \<open>b \<noteq> 0\<close> have "multiplicity p (a ^ n) \<le> multiplicity p (b ^ n)"
        by (intro dvd_imp_multiplicity_le) auto
      thus "multiplicity p a \<le> multiplicity p b"
        using p \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>n > 0\<close> by (simp add: prime_elem_multiplicity_power_distrib)
    qed fact+
  qed (auto intro: dvd_power_same)
qed (use assms in \<open>auto simp: power_0_left\<close>)

lemma multiplicity_power_power:
  fixes p :: "'a :: {factorial_semiring, algebraic_semidom}"
  assumes "n > 0"
  shows   "multiplicity (p ^ n) (x ^ n) = multiplicity p x"
proof (cases "x = 0 \<or> p = 0 \<or> is_unit p")
  case True
  thus ?thesis using \<open>n > 0\<close>
    by (auto simp: power_0_left is_unit_power_iff multiplicity_unit_left)
next
  case False
  show ?thesis
  proof (intro antisym multiplicity_geI)
    have "(p ^ multiplicity p x) ^ n dvd x ^ n"
      by (intro dvd_power_same) (simp add: multiplicity_dvd)
    thus "(p ^ n) ^ multiplicity p x dvd x ^ n"
      by (simp add: mult_ac flip: power_mult)
  next
    have "(p ^ n) ^ multiplicity (p ^ n) (x ^ n) dvd x ^ n"
      by (simp add: multiplicity_dvd)
    hence "(p ^ multiplicity (p ^ n) (x ^ n)) ^ n dvd x ^ n"
      by (simp add: mult_ac flip: power_mult)
    thus "p ^ multiplicity (p ^ n) (x ^ n) dvd x"
      by (subst (asm) pow_divides_pow_iff) (use assms in auto)
  qed (use False \<open>n > 0\<close> in \<open>auto simp: is_unit_power_iff\<close>)
qed

lemma even_square_cong_4_int:
  fixes x :: int
  assumes "even x"
  shows   "[x ^ 2 = 0] (mod 4)"
proof -
  from assms have "even \<bar>x\<bar>"
    by simp
  hence [simp]: "\<bar>x\<bar> mod 2 = 0"
    by presburger
  have "(\<bar>x\<bar> ^ 2) mod 4 = ((\<bar>x\<bar> mod 4) ^ 2) mod 4"
    by (simp add: power_mod)
  also from assms have "\<bar>x\<bar> mod 4 = 0 \<or> \<bar>x\<bar> mod 4 = 2"
    using mod_double_modulus[of 2 "\<bar>x\<bar>"] by simp
  hence "((\<bar>x\<bar> mod 4) ^ 2) mod 4 = 0"
    by auto
  finally show ?thesis by (simp add: cong_def)
qed

lemma even_square_cong_4_nat: "even (x::nat) \<Longrightarrow> [x ^ 2 = 0] (mod 4)"
  using even_square_cong_4_int[of "int x"] by (auto simp flip: cong_int_iff)

lemma odd_square_cong_4_int:
  fixes x :: int
  assumes "odd x"
  shows   "[x ^ 2 = 1] (mod 4)"
proof -
  from assms have "odd \<bar>x\<bar>"
    by simp
  hence [simp]: "\<bar>x\<bar> mod 2 = 1"
    by presburger
  have "(\<bar>x\<bar> ^ 2) mod 4 = ((\<bar>x\<bar> mod 4) ^ 2) mod 4"
    by (simp add: power_mod)
  also from assms have "\<bar>x\<bar> mod 4 = 1 \<or> \<bar>x\<bar> mod 4 = 3"
    using mod_double_modulus[of 2 "\<bar>x\<bar>"] by simp
  hence "((\<bar>x\<bar> mod 4) ^ 2) mod 4 = 1"
    by auto
  finally show ?thesis by (simp add: cong_def)
qed

lemma odd_square_cong_4_nat: "odd (x::nat) \<Longrightarrow> [x ^ 2 = 1] (mod 4)"
  using odd_square_cong_4_int[of "int x"] by (auto simp flip: cong_int_iff)


text \<open>
  Gaussian integers will require a notion of an element being a power up to a unit,
  so we introduce this here. This should go in the library eventually.
\<close>
definition is_nth_power_upto_unit where
  "is_nth_power_upto_unit n x \<longleftrightarrow> (\<exists>u. is_unit u \<and> is_nth_power n (u * x))"

lemma is_nth_power_upto_unit_base: "is_nth_power n x \<Longrightarrow> is_nth_power_upto_unit n x"
  by (auto simp: is_nth_power_upto_unit_def intro: exI[of _ 1])

lemma is_nth_power_upto_unitI:
  assumes "normalize (x ^ n) = normalize y"
  shows   "is_nth_power_upto_unit n y"
proof -
  from associatedE1[OF assms] obtain u where "is_unit u" "u * y = x ^ n"
    by metis
  thus ?thesis
    by (auto simp: is_nth_power_upto_unit_def intro!: exI[of _ u])
qed

lemma is_nth_power_upto_unit_conv_multiplicity: 
  fixes x :: "'a :: factorial_semiring"
  assumes "n > 0"
  shows   "is_nth_power_upto_unit n x \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x)"
proof (cases "x = 0")
  case False
  show ?thesis
  proof safe
    fix p :: 'a assume p: "prime p"
    assume "is_nth_power_upto_unit n x"
    then obtain u y where uy: "is_unit u" "u * x = y ^ n"
      by (auto simp: is_nth_power_upto_unit_def elim!: is_nth_powerE)
    from p uy assms False have [simp]: "y \<noteq> 0" by (auto simp: power_0_left)
    have "multiplicity p (u * x) = multiplicity p (y ^ n)"
      by (subst uy(2) [symmetric]) simp
    also have "multiplicity p (u * x) = multiplicity p x"
      by (simp add: multiplicity_times_unit_right uy(1))
    finally show "n dvd multiplicity p x"
      using False and p and uy and assms
      by (auto simp: prime_elem_multiplicity_power_distrib)
  next
    assume *: "\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x"
    have "multiplicity p ((\<Prod>p\<in>prime_factors x. p ^ (multiplicity p x div n)) ^ n) = 
            multiplicity p x" if "prime p" for p
    proof -
      from that and * have "n dvd multiplicity p x" by blast
      have "multiplicity p x = 0" if "p \<notin> prime_factors x"
        using that and \<open>prime p\<close> by (simp add: prime_factors_multiplicity)
      with that and * and assms show ?thesis unfolding prod_power_distrib power_mult [symmetric]
        by (subst multiplicity_prod_prime_powers) (auto simp: in_prime_factors_imp_prime elim: dvdE)
    qed
    with assms False 
      have "normalize ((\<Prod>p\<in>prime_factors x. p ^ (multiplicity p x div n)) ^ n) = normalize x"
      by (intro multiplicity_eq_imp_eq) (auto simp: multiplicity_prod_prime_powers)
    thus "is_nth_power_upto_unit n x"
      by (auto intro: is_nth_power_upto_unitI)
  qed
qed (use assms in \<open>auto simp: is_nth_power_upto_unit_def\<close>)

lemma is_nth_power_upto_unit_0_left [simp, intro]: "is_nth_power_upto_unit 0 x \<longleftrightarrow> is_unit x"
proof
  assume "is_unit x"
  thus "is_nth_power_upto_unit 0 x"
    unfolding is_nth_power_upto_unit_def by (intro exI[of _ "1 div x"]) auto
next
  assume "is_nth_power_upto_unit 0 x"
  then obtain u where "is_unit u" "u * x = 1"
    by (auto simp: is_nth_power_upto_unit_def)
  thus "is_unit x"
    by (metis dvd_triv_right)
qed

lemma is_nth_power_upto_unit_unit [simp, intro]:
  assumes "is_unit x"
  shows   "is_nth_power_upto_unit n x"
  using assms by (auto simp: is_nth_power_upto_unit_def intro!: exI[of _ "1 div x"])

lemma is_nth_power_upto_unit_1_left [simp, intro]: "is_nth_power_upto_unit 1 x"
  by (auto simp: is_nth_power_upto_unit_def intro: exI[of _ 1])

lemma is_nth_power_upto_unit_mult_coprimeD1:
  fixes x y :: "'a :: factorial_semiring"
  assumes "coprime x y" "is_nth_power_upto_unit n (x * y)"
  shows   "is_nth_power_upto_unit n x"
proof -
  consider "n = 0" | "x = 0" "n > 0" | "x \<noteq> 0" "y = 0" "n > 0" | "n > 0" "x \<noteq> 0" "y \<noteq> 0"
    by force
  thus ?thesis
  proof cases
    assume [simp]: "n = 0"
    from assms have "is_unit (x * y)"
      by auto
    hence "is_unit x"
      using is_unit_mult_iff by blast
    thus ?thesis using assms by auto
  next
    assume "x = 0" "n > 0"
    thus ?thesis by (auto simp: is_nth_power_upto_unit_def)
  next
    assume *: "x \<noteq> 0" "y = 0" "n > 0"
    with assms show ?thesis by auto
  next
    assume *: "n > 0" and [simp]: "x \<noteq> 0" "y \<noteq> 0"
    show ?thesis
    proof (subst is_nth_power_upto_unit_conv_multiplicity[OF \<open>n > 0\<close>]; safe)
      fix p :: 'a assume p: "prime p"
      show "n dvd multiplicity p x"
      proof (cases "p dvd x")
        case False
        thus ?thesis
          by (simp add: not_dvd_imp_multiplicity_0)
      next
        case True
        have "n dvd multiplicity p (x * y)"
          using assms(2) \<open>n > 0\<close> p by (auto simp: is_nth_power_upto_unit_conv_multiplicity)
        also have "\<dots> = multiplicity p x + multiplicity p y"
          using p by (subst prime_elem_multiplicity_mult_distrib) auto
        also have "\<not>p dvd y"
          using \<open>coprime x y\<close> \<open>p dvd x\<close> p not_prime_unit coprime_common_divisor by blast
        hence "multiplicity p y = 0"
          by (rule not_dvd_imp_multiplicity_0)
        finally show ?thesis by simp
      qed
    qed
  qed
qed

lemma is_nth_power_upto_unit_mult_coprimeD2:
  fixes x y :: "'a :: factorial_semiring"
  assumes "coprime x y" "is_nth_power_upto_unit n (x * y)"
  shows   "is_nth_power_upto_unit n y"
  using assms is_nth_power_upto_unit_mult_coprimeD1[of y x]
  by (simp_all add: mult_ac coprime_commute)


subsection \<open>Definition\<close>

text \<open>
  Gaussian integers are the ring $\mathbb{Z}[i]$ which is formed either by formally adjoining
  an element $i$ with $i^2 = -1$ to $\mathbb{Z}$ or by taking all the complex numbers with
  integer real and imaginary part.

  We define them simply by giving an appropriate ring structure to $\mathbb{Z}^2$, with the first
  component representing the real part and the second component the imaginary part:
\<close>
codatatype gauss_int = Gauss_Int (ReZ: int) (ImZ: int)

text \<open>
  The following is the imaginary unit $i$ in the Gaussian integers, which we will denote as
  \<open>\<i>\<^sub>\<int>\<close>:
\<close>
primcorec gauss_i where
  "ReZ gauss_i = 0"
| "ImZ gauss_i = 1"

lemma gauss_int_eq_iff: "x = y \<longleftrightarrow> ReZ x = ReZ y \<and> ImZ x = ImZ y"
  by (cases x; cases y) auto


(*<*)
bundle gauss_int_notation
begin

notation gauss_i ("\<i>\<^sub>\<int>")

end

bundle no_gauss_int_notation
begin

no_notation (output) gauss_i ("\<i>\<^sub>\<int>")

end

bundle gauss_int_output_notation
begin

notation (output) gauss_i ("\<ii>")

end

unbundle gauss_int_notation
(*>*)


text \<open>
  Next, we define the canonical injective homomorphism from the Gaussian integers into the
  complex numbers:
\<close>
primcorec gauss2complex where
  "Re (gauss2complex z) = of_int (ReZ z)"
| "Im (gauss2complex z) = of_int (ImZ z)"

declare [[coercion gauss2complex]]

lemma gauss2complex_eq_iff [simp]: "gauss2complex z = gauss2complex u \<longleftrightarrow> z = u"
  by (simp add: complex_eq_iff gauss_int_eq_iff)

text \<open>
  Gaussian integers also have conjugates, just like complex numbers:
\<close>
primcorec gauss_cnj where
  "ReZ (gauss_cnj z) = ReZ z"
| "ImZ (gauss_cnj z) = -ImZ z"


text \<open>
  In the remainder of this section, we prove that Gaussian integers are a commutative ring
  of characteristic 0 and several other trivial algebraic properties.
\<close>

instantiation gauss_int :: comm_ring_1
begin

primcorec zero_gauss_int where
  "ReZ zero_gauss_int = 0"
| "ImZ zero_gauss_int = 0"

primcorec one_gauss_int where
  "ReZ one_gauss_int = 1"
| "ImZ one_gauss_int = 0"

primcorec uminus_gauss_int where
  "ReZ (uminus_gauss_int x) = -ReZ x"
| "ImZ (uminus_gauss_int x) = -ImZ x"

primcorec plus_gauss_int where
  "ReZ (plus_gauss_int x y) = ReZ x + ReZ y"
| "ImZ (plus_gauss_int x y) = ImZ x + ImZ y"

primcorec minus_gauss_int where
  "ReZ (minus_gauss_int x y) = ReZ x - ReZ y"
| "ImZ (minus_gauss_int x y) = ImZ x - ImZ y"

primcorec times_gauss_int where
  "ReZ (times_gauss_int x y) = ReZ x * ReZ y - ImZ x * ImZ y"
| "ImZ (times_gauss_int x y) = ReZ x * ImZ y + ImZ x * ReZ y"

instance
  by intro_classes (auto simp: gauss_int_eq_iff algebra_simps)

end

lemma gauss_i_times_i [simp]: "\<i>\<^sub>\<int> * \<i>\<^sub>\<int> = (-1 :: gauss_int)"
  and gauss_cnj_i [simp]: "gauss_cnj \<i>\<^sub>\<int> = -\<i>\<^sub>\<int>"
  by (simp_all add: gauss_int_eq_iff)

lemma gauss_cnj_eq_0_iff [simp]: "gauss_cnj z = 0 \<longleftrightarrow> z = 0"
  by (auto simp: gauss_int_eq_iff)

lemma gauss_cnj_eq_self: "Im z = 0 \<Longrightarrow> gauss_cnj z = z"
  and gauss_cnj_eq_minus_self: "Re z = 0 \<Longrightarrow> gauss_cnj z = -z"
  by (auto simp: gauss_int_eq_iff)

lemma ReZ_of_nat [simp]: "ReZ (of_nat n) = of_nat n"
  and ImZ_of_nat [simp]: "ImZ (of_nat n) = 0"
  by (induction n; simp)+

lemma ReZ_of_int [simp]: "ReZ (of_int n) = n"
  and ImZ_of_int [simp]: "ImZ (of_int n) = 0"
  by (induction n; simp)+

lemma ReZ_numeral [simp]: "ReZ (numeral n) = numeral n"
  and ImZ_numeral [simp]: "ImZ (numeral n) = 0"
  by (subst of_nat_numeral [symmetric], subst ReZ_of_nat ImZ_of_nat, simp)+

lemma gauss2complex_0 [simp]: "gauss2complex 0 = 0"
  and gauss2complex_1 [simp]: "gauss2complex 1 = 1"
  and gauss2complex_i [simp]: "gauss2complex \<i>\<^sub>\<int> = \<i>"
  and gauss2complex_add [simp]: "gauss2complex (x + y) = gauss2complex x + gauss2complex y"
  and gauss2complex_diff [simp]: "gauss2complex (x - y) = gauss2complex x - gauss2complex y"
  and gauss2complex_mult [simp]: "gauss2complex (x * y) = gauss2complex x * gauss2complex y"
  and gauss2complex_uminus [simp]: "gauss2complex (-x) = -gauss2complex x"
  and gauss2complex_cnj [simp]: "gauss2complex (gauss_cnj x) = cnj (gauss2complex x)"
  by (simp_all add: complex_eq_iff)

lemma gauss2complex_of_nat [simp]: "gauss2complex (of_nat n) = of_nat n"
  by (simp add: complex_eq_iff)

lemma gauss2complex_eq_0_iff [simp]: "gauss2complex x = 0 \<longleftrightarrow> x = 0"
  and gauss2complex_eq_1_iff [simp]: "gauss2complex x = 1 \<longleftrightarrow> x = 1"
  and zero_eq_gauss2complex_iff [simp]: "0 = gauss2complex x \<longleftrightarrow> x = 0"
  and one_eq_gauss2complex_iff [simp]: "1 = gauss2complex x \<longleftrightarrow> x = 1"
  by (simp_all add: complex_eq_iff gauss_int_eq_iff)

lemma gauss_i_times_gauss_i_times [simp]: "\<i>\<^sub>\<int> * (\<i>\<^sub>\<int> * x) = (-x :: gauss_int)"
  by (subst mult.assoc [symmetric], subst gauss_i_times_i) auto

lemma gauss_i_neq_0 [simp]: "\<i>\<^sub>\<int> \<noteq> 0" "0 \<noteq> \<i>\<^sub>\<int>"
  and gauss_i_neq_1 [simp]: "\<i>\<^sub>\<int> \<noteq> 1" "1 \<noteq> \<i>\<^sub>\<int>"
  and gauss_i_neq_of_nat [simp]: "\<i>\<^sub>\<int> \<noteq> of_nat n" "of_nat n \<noteq> \<i>\<^sub>\<int>"
  and gauss_i_neq_of_int [simp]: "\<i>\<^sub>\<int> \<noteq> of_int n" "of_int n \<noteq> \<i>\<^sub>\<int>"
  and gauss_i_neq_numeral [simp]: "\<i>\<^sub>\<int> \<noteq> numeral m" "numeral m \<noteq> \<i>\<^sub>\<int>"
  by (auto simp: gauss_int_eq_iff)

lemma gauss_cnj_0 [simp]: "gauss_cnj 0 = 0"
  and gauss_cnj_1 [simp]: "gauss_cnj 1 = 1"
  and gauss_cnj_cnj [simp]: "gauss_cnj (gauss_cnj z) = z"
  and gauss_cnj_uminus [simp]: "gauss_cnj (-a) = -gauss_cnj a"
  and gauss_cnj_add [simp]: "gauss_cnj (a + b) = gauss_cnj a + gauss_cnj b"
  and gauss_cnj_diff [simp]: "gauss_cnj (a - b) = gauss_cnj a - gauss_cnj b"
  and gauss_cnj_mult [simp]: "gauss_cnj (a * b) = gauss_cnj a * gauss_cnj b"
  and gauss_cnj_of_nat [simp]: "gauss_cnj (of_nat n1) = of_nat n1"
  and gauss_cnj_of_int [simp]: "gauss_cnj (of_int n2) = of_int n2"
  and gauss_cnj_numeral [simp]: "gauss_cnj (numeral n3) = numeral n3"
  by (simp_all add: gauss_int_eq_iff)

lemma gauss_cnj_power [simp]: "gauss_cnj (a ^ n) = gauss_cnj a ^ n"
  by (induction n) auto

lemma gauss_cnj_sum [simp]: "gauss_cnj (sum f A) = (\<Sum>x\<in>A. gauss_cnj (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma gauss_cnj_prod [simp]: "gauss_cnj (prod f A) = (\<Prod>x\<in>A. gauss_cnj (f x))"
  by (induction A rule: infinite_finite_induct) auto

lemma of_nat_dvd_of_nat:
  assumes "a dvd b"
  shows   "of_nat a dvd (of_nat b :: 'a :: comm_semiring_1)"
  using assms by auto

lemma of_int_dvd_imp_dvd_gauss_cnj:
  fixes z :: gauss_int
  assumes "of_int n dvd z"
  shows   "of_int n dvd gauss_cnj z"
proof -
  from assms obtain u where "z = of_int n * u" by blast
  hence "gauss_cnj z = of_int n * gauss_cnj u"
    by simp
  thus ?thesis by auto
qed

lemma of_nat_dvd_imp_dvd_gauss_cnj:
  fixes z :: gauss_int
  assumes "of_nat n dvd z"
  shows   "of_nat n dvd gauss_cnj z"
  using of_int_dvd_imp_dvd_gauss_cnj[of "int n"] assms by simp

lemma of_int_dvd_of_int_gauss_int_iff:
  "(of_int m :: gauss_int) dvd of_int n \<longleftrightarrow> m dvd n"
proof
  assume "of_int m dvd (of_int n :: gauss_int)"
  then obtain a :: gauss_int where "of_int n = of_int m * a"
    by blast
  thus "m dvd n"
    by (auto simp: gauss_int_eq_iff)
qed auto

lemma of_nat_dvd_of_nat_gauss_int_iff:
  "(of_nat m :: gauss_int) dvd of_nat n \<longleftrightarrow> m dvd n"
  using of_int_dvd_of_int_gauss_int_iff[of "int m" "int n"] by simp

lemma gauss_cnj_dvd:
  assumes "a dvd b"
  shows   "gauss_cnj a dvd gauss_cnj b"
proof -
  from assms obtain c where "b = a * c"
    by blast
  hence "gauss_cnj b = gauss_cnj a * gauss_cnj c"
    by simp
  thus ?thesis by auto
qed

lemma gauss_cnj_dvd_iff: "gauss_cnj a dvd gauss_cnj b \<longleftrightarrow> a dvd b"
  using gauss_cnj_dvd[of a b] gauss_cnj_dvd[of "gauss_cnj a" "gauss_cnj b"] by auto

lemma gauss_cnj_dvd_left_iff: "gauss_cnj a dvd b \<longleftrightarrow> a dvd gauss_cnj b"
  by (subst gauss_cnj_dvd_iff [symmetric]) auto

lemma gauss_cnj_dvd_right_iff: "a dvd gauss_cnj b \<longleftrightarrow> gauss_cnj a dvd b"
  by (rule gauss_cnj_dvd_left_iff [symmetric])


instance gauss_int :: idom
proof
  fix z u :: gauss_int
  assume "z \<noteq> 0" "u \<noteq> 0"
  hence "gauss2complex z * gauss2complex u \<noteq> 0"
    by simp
  also have "gauss2complex z * gauss2complex u = gauss2complex (z * u)"
    by simp
  finally show "z * u \<noteq> 0"
    unfolding gauss2complex_eq_0_iff .
qed

instance gauss_int :: ring_char_0
  by intro_classes (auto intro!: injI simp: gauss_int_eq_iff)


subsection \<open>Pretty-printing\<close>

text \<open>
  The following lemma collection provides better pretty-printing of Gaussian integers so that
  e.g.\ evaluation with the `value' command produces nicer results.
\<close>
lemma gauss_int_code_post [code_post]:
  "Gauss_Int 0 0 = 0"
  "Gauss_Int 0 1 = \<i>\<^sub>\<int>"
  "Gauss_Int 0 (-1) = -\<i>\<^sub>\<int>"
  "Gauss_Int 1 0 = 1"
  "Gauss_Int 1 1 = 1 + \<i>\<^sub>\<int>"
  "Gauss_Int 1 (-1) = 1 - \<i>\<^sub>\<int>"
  "Gauss_Int (-1) 0 = -1"
  "Gauss_Int (-1) 1 = -1 + \<i>\<^sub>\<int>"
  "Gauss_Int (-1) (-1) = -1 - \<i>\<^sub>\<int>"  
  "Gauss_Int (numeral b) 0 = numeral b"
  "Gauss_Int (-numeral b) 0 = -numeral b"
  "Gauss_Int (numeral b) 1 = numeral b + \<i>\<^sub>\<int>"
  "Gauss_Int (-numeral b) 1 = -numeral b + \<i>\<^sub>\<int>"
  "Gauss_Int (numeral b) (-1) = numeral b - \<i>\<^sub>\<int>"
  "Gauss_Int (-numeral b) (-1) = -numeral b - \<i>\<^sub>\<int>"
  "Gauss_Int 0 (numeral b) = numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int 0 (-numeral b) = -numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int 1 (numeral b) = 1 + numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int 1 (-numeral b) = 1 - numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (-1) (numeral b) = -1 + numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (-1) (-numeral b) = -1 - numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (numeral a) (numeral b) = numeral a + numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (numeral a) (-numeral b) = numeral a - numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (-numeral a) (numeral b) = -numeral a + numeral b * \<i>\<^sub>\<int>"
  "Gauss_Int (-numeral a) (-numeral b) = -numeral a - numeral b * \<i>\<^sub>\<int>"
  by (simp_all add: gauss_int_eq_iff)

value "\<i>\<^sub>\<int> ^ 3"
value "2 * (3 + \<i>\<^sub>\<int>)"
value "(2 + \<i>\<^sub>\<int>) * (2 - \<i>\<^sub>\<int>)"


subsection \<open>Norm\<close>

text \<open>
  The square of the complex norm (or complex modulus) on the Gaussian integers gives us a norm
  that always returns a natural number. We will later show that this is also a Euclidean norm
  (in the sense of a Euclidean ring).
\<close>
definition gauss_int_norm :: "gauss_int \<Rightarrow> nat" where
  "gauss_int_norm z = nat (ReZ z ^ 2 + ImZ z ^ 2)"

lemma gauss_int_norm_0 [simp]: "gauss_int_norm 0 = 0"
  and gauss_int_norm_1 [simp]: "gauss_int_norm 1 = 1"
  and gauss_int_norm_i [simp]: "gauss_int_norm \<i>\<^sub>\<int> = 1"
  and gauss_int_norm_cnj [simp]: "gauss_int_norm (gauss_cnj z) = gauss_int_norm z"
  and gauss_int_norm_of_nat [simp]: "gauss_int_norm (of_nat n) = n ^ 2"
  and gauss_int_norm_of_int [simp]: "gauss_int_norm (of_int m) = nat (m ^ 2)"
  and gauss_int_norm_of_numeral [simp]: "gauss_int_norm (numeral n') = numeral (Num.sqr n')"
  by (simp_all add: gauss_int_norm_def nat_power_eq)

lemma gauss_int_norm_uminus [simp]: "gauss_int_norm (-z) = gauss_int_norm z"
  by (simp add: gauss_int_norm_def)

lemma gauss_int_norm_eq_0_iff [simp]: "gauss_int_norm z = 0 \<longleftrightarrow> z = 0"
proof
  assume "gauss_int_norm z = 0"
  hence "ReZ z ^ 2 + ImZ z ^ 2 \<le> 0"
    by (simp add: gauss_int_norm_def)
  moreover have "ReZ z ^ 2 + ImZ z ^ 2 \<ge> 0"
    by simp
  ultimately have "ReZ z ^ 2 + ImZ z ^ 2 = 0"
    by linarith
  thus "z = 0"
    by (auto simp: gauss_int_eq_iff)
qed auto

lemma gauss_int_norm_pos_iff [simp]: "gauss_int_norm z > 0 \<longleftrightarrow> z \<noteq> 0"
  using gauss_int_norm_eq_0_iff[of z] by (auto intro: Nat.gr0I)

lemma real_gauss_int_norm: "real (gauss_int_norm z) = norm (gauss2complex z) ^ 2"
  by (auto simp: cmod_def gauss_int_norm_def)

lemma gauss_int_norm_mult: "gauss_int_norm (z * u) = gauss_int_norm z * gauss_int_norm u"
proof -
  have "real (gauss_int_norm (z * u)) = real (gauss_int_norm z * gauss_int_norm u)"
    unfolding of_nat_mult by (simp add: real_gauss_int_norm norm_power norm_mult power_mult_distrib)
  thus ?thesis by (subst (asm) of_nat_eq_iff)
qed

lemma self_mult_gauss_cnj: "z * gauss_cnj z = of_nat (gauss_int_norm z)"
  by (simp add: gauss_int_norm_def gauss_int_eq_iff algebra_simps power2_eq_square)

lemma gauss_cnj_mult_self: "gauss_cnj z * z = of_nat (gauss_int_norm z)"
  by (subst mult.commute, rule self_mult_gauss_cnj)

lemma self_plus_gauss_cnj: "z + gauss_cnj z = of_int (2 * ReZ z)"
  and self_minus_gauss_cnj: "z - gauss_cnj z = of_int (2 * ImZ z) * \<i>\<^sub>\<int>"
  by (auto simp: gauss_int_eq_iff)

lemma gauss_int_norm_dvd_mono:
  assumes "a dvd b"
  shows "gauss_int_norm a dvd gauss_int_norm b"
proof -
  from assms obtain c where "b = a * c" by blast
  hence "gauss_int_norm b = gauss_int_norm (a * c)"
    by metis
  thus ?thesis by (simp add: gauss_int_norm_mult)
qed

text \<open>
  A Gaussian integer is a unit iff its norm is 1, and this is the case precisely for the four
  elements \<open>\<plusminus>1\<close> and \<open>\<plusminus>\<i>\<close>:
\<close>
lemma is_unit_gauss_int_iff: "x dvd 1 \<longleftrightarrow> x \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int> :: gauss_int}"
  and is_unit_gauss_int_iff': "x dvd 1 \<longleftrightarrow> gauss_int_norm x = 1"
proof -
  have "x dvd 1" if "x \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int>}"
  proof -
    from that have *: "x * gauss_cnj x = 1"
      by (auto simp: gauss_int_norm_def)
    show "x dvd 1" by (subst * [symmetric]) simp
  qed
  moreover have "gauss_int_norm x = 1" if "x dvd 1"
    using gauss_int_norm_dvd_mono[OF that] by simp
  moreover have "x \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int>}" if "gauss_int_norm x = 1"
  proof -
    from that have *: "(ReZ x)\<^sup>2 + (ImZ x)\<^sup>2 = 1"
      by (auto simp: gauss_int_norm_def nat_eq_iff)
    hence "ReZ x ^ 2 \<le> 1" and "ImZ x ^ 2 \<le> 1"
      using zero_le_power2[of "ImZ x"] zero_le_power2[of "ReZ x"] by linarith+
    hence "\<bar>ReZ x\<bar> \<le> 1" and "\<bar>ImZ x\<bar> \<le> 1"
      by (auto simp: abs_square_le_1)
    hence "ReZ x \<in> {-1, 0, 1}" and "ImZ x \<in> {-1, 0, 1}"
      by auto
    thus "x \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int> :: gauss_int}"
      using * by (auto simp: gauss_int_eq_iff)    
  qed
  ultimately show "x dvd 1 \<longleftrightarrow> x \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int> :: gauss_int}"
              and "x dvd 1 \<longleftrightarrow> gauss_int_norm x = 1"
    by blast+
qed

lemma is_unit_gauss_i [simp, intro]: "(gauss_i :: gauss_int) dvd 1"
  by (simp add: is_unit_gauss_int_iff)

lemma gauss_int_norm_eq_Suc_0_iff: "gauss_int_norm x = Suc 0 \<longleftrightarrow> x dvd 1"
  by (simp add: is_unit_gauss_int_iff')

lemma is_unit_gauss_cnj [intro]: "z dvd 1 \<Longrightarrow> gauss_cnj z dvd 1"
  by (simp add: is_unit_gauss_int_iff')

lemma is_unit_gauss_cnj_iff [simp]: "gauss_cnj z dvd 1 \<longleftrightarrow> z dvd 1"
  by (simp add: is_unit_gauss_int_iff')


subsection \<open>Division and normalisation\<close>

text \<open>
  We define a rounding operation that takes a complex number and returns a Gaussian integer
  by rounding the real and imaginary parts separately:
\<close>
primcorec round_complex :: "complex \<Rightarrow> gauss_int" where
  "ReZ (round_complex z) = round (Re z)"
| "ImZ (round_complex z) = round (Im z)"

text \<open>
  The distance between a rounded complex number and the original one is no more than
  $\frac{1}{2}\sqrt{2}$:
\<close>
lemma norm_round_complex_le: "norm (z - gauss2complex (round_complex z)) ^ 2 \<le> 1 / 2"
proof -
  have "(Re z - ReZ (round_complex z)) ^ 2 \<le> (1 / 2) ^ 2"
    using of_int_round_abs_le[of "Re z"]
    by (subst abs_le_square_iff [symmetric]) (auto simp: abs_minus_commute)
  moreover have "(Im z - ImZ (round_complex z)) ^ 2 \<le> (1 / 2) ^ 2"
    using of_int_round_abs_le[of "Im z"]
    by (subst abs_le_square_iff [symmetric]) (auto simp: abs_minus_commute)
  ultimately have "(Re z - ReZ (round_complex z)) ^ 2 + (Im z - ImZ (round_complex z)) ^ 2 \<le>
                     (1 / 2) ^ 2 + (1 / 2) ^ 2"
    by (rule add_mono)
  thus "norm (z - gauss2complex (round_complex z)) ^ 2 \<le> 1 / 2"
    by (simp add: cmod_def power2_eq_square)
qed

lemma dist_round_complex_le: "dist z (gauss2complex (round_complex z)) \<le> sqrt 2 / 2"
proof -
  have "dist z (gauss2complex (round_complex z)) ^ 2 =
        norm (z - gauss2complex (round_complex z)) ^ 2"
    by (simp add: dist_norm)
  also have "\<dots> \<le> 1 / 2"
    by (rule norm_round_complex_le)
  also have "\<dots> = (sqrt 2 / 2) ^ 2"
    by (simp add: power2_eq_square)
  finally show ?thesis
    by (rule power2_le_imp_le) auto
qed


text \<open>
  We can now define division on Gaussian integers simply by performing the division in the
  complex numbers and rounding the result. This also gives us a remainder operation defined
  accordingly for which the norm of the remainder is always smaller than the norm of the divisor.

  We can also define a normalisation operation that returns a canonical representative for each
  association class. Since the four units of the Gaussian integers are \<open>\<plusminus>1\<close> and \<open>\<plusminus>\<i>\<close>, each
  association class (other than \<open>0\<close>) has four representatives, one in each quadrant. We simply
  define the on in the upper-right quadrant (i.e.\ the one with non-negative imaginary part
  and positive real part) as the canonical one.

  Thus, the Gaussian integers form a Euclidean ring. This gives us many things, most importantly
  the existence of GCDs and LCMs and unique factorisation.
\<close>
instantiation gauss_int :: algebraic_semidom
begin

definition divide_gauss_int :: "gauss_int \<Rightarrow> gauss_int \<Rightarrow> gauss_int" where
  "divide_gauss_int a b = round_complex (gauss2complex a / gauss2complex b)"

instance proof
  fix a :: gauss_int
  show "a div 0 = 0"
    by (auto simp: gauss_int_eq_iff divide_gauss_int_def)
next
  fix a b :: gauss_int assume "b \<noteq> 0"
  thus "a * b div b = a"
    by (auto simp: gauss_int_eq_iff divide_gauss_int_def)
qed

end

instantiation gauss_int :: semidom_divide_unit_factor
begin

definition unit_factor_gauss_int :: "gauss_int \<Rightarrow> gauss_int" where
  "unit_factor_gauss_int z =
     (if z = 0 then 0 else 
      if ImZ z \<ge> 0 \<and> ReZ z > 0 then 1
      else if ReZ z \<le> 0 \<and> ImZ z > 0 then \<i>\<^sub>\<int>
      else if ImZ z \<le> 0 \<and> ReZ z < 0 then -1
      else -\<i>\<^sub>\<int>)"

instance proof
  show "unit_factor (0 :: gauss_int) = 0"
    by (simp add: unit_factor_gauss_int_def)
next
  fix z :: gauss_int
  assume "is_unit z"
  thus "unit_factor z = z"
    by (subst (asm) is_unit_gauss_int_iff) (auto simp: unit_factor_gauss_int_def)
next
  fix z :: gauss_int
  assume z: "z \<noteq> 0"
  thus "is_unit (unit_factor z)"
    by (subst is_unit_gauss_int_iff) (auto simp: unit_factor_gauss_int_def)
next
  fix z u :: gauss_int
  assume "is_unit z"
  hence "z \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int>}"
    by (subst (asm) is_unit_gauss_int_iff)
  thus "unit_factor (z * u) = z * unit_factor u"
    by (safe; auto simp: unit_factor_gauss_int_def gauss_int_eq_iff[of u 0])
qed

end

instantiation gauss_int :: normalization_semidom
begin

definition normalize_gauss_int :: "gauss_int \<Rightarrow> gauss_int" where
  "normalize_gauss_int z =
     (if z = 0 then 0 else 
      if ImZ z \<ge> 0 \<and> ReZ z > 0 then z
      else if ReZ z \<le> 0 \<and> ImZ z > 0 then -\<i>\<^sub>\<int> * z
      else if ImZ z \<le> 0 \<and> ReZ z < 0 then -z
      else \<i>\<^sub>\<int> * z)"

instance proof
  show "normalize (0 :: gauss_int) = 0"
    by (simp add: normalize_gauss_int_def)
next
  fix z :: gauss_int
  show "unit_factor z * normalize z = z"
    by (auto simp: normalize_gauss_int_def unit_factor_gauss_int_def algebra_simps)
qed

end

lemma normalize_gauss_int_of_nat [simp]: "normalize (of_nat n :: gauss_int) = of_nat n"
  and normalize_gauss_int_of_int [simp]: "normalize (of_int m :: gauss_int) = of_int \<bar>m\<bar>"
  and normalize_gauss_int_of_numeral [simp]: "normalize (numeral n' :: gauss_int) = numeral n'"
  by (auto simp: normalize_gauss_int_def)

lemma normalize_gauss_i [simp]: "normalize \<i>\<^sub>\<int> = 1"
  by (simp add: normalize_gauss_int_def)

lemma gauss_int_norm_normalize [simp]: "gauss_int_norm (normalize x) = gauss_int_norm x"
  by (simp add: normalize_gauss_int_def gauss_int_norm_mult)

lemma normalized_gauss_int:
  assumes "normalize z = z"
  shows   "ReZ z \<ge> 0" "ImZ z \<ge> 0"
  using assms
  by (cases "ReZ z" "0 :: int" rule: linorder_cases;
      cases "ImZ z" "0 :: int" rule: linorder_cases;
      simp add: normalize_gauss_int_def gauss_int_eq_iff)+

lemma normalized_gauss_int':
  assumes "normalize z = z" "z \<noteq> 0"
  shows   "ReZ z > 0" "ImZ z \<ge> 0"
  using assms
  by (cases "ReZ z" "0 :: int" rule: linorder_cases;
      cases "ImZ z" "0 :: int" rule: linorder_cases;
      simp add: normalize_gauss_int_def gauss_int_eq_iff)+

lemma normalized_gauss_int_iff:
  "normalize z = z \<longleftrightarrow> z = 0 \<or> ReZ z > 0 \<and> ImZ z \<ge> 0"
  by (cases "ReZ z" "0 :: int" rule: linorder_cases;
      cases "ImZ z" "0 :: int" rule: linorder_cases;
      simp add: normalize_gauss_int_def gauss_int_eq_iff)+

instantiation gauss_int :: idom_modulo
begin

definition modulo_gauss_int :: "gauss_int \<Rightarrow> gauss_int \<Rightarrow> gauss_int" where
  "modulo_gauss_int a b = a - a div b * b"

instance proof
  fix a b :: gauss_int
  show "a div b * b + a mod b = a"
    by (simp add: modulo_gauss_int_def)
qed

end

lemma gauss_int_norm_mod_less_aux:
  assumes [simp]: "b \<noteq> 0"
  shows   "2 * gauss_int_norm (a mod b) \<le> gauss_int_norm b"
proof -
  define a' b' where "a' = gauss2complex a" and "b' = gauss2complex b"
  have [simp]: "b' \<noteq> 0" by (simp add: b'_def)
  have "gauss_int_norm (a mod b) = 
          norm (gauss2complex (a - round_complex (a' / b') * b)) ^ 2"
    unfolding modulo_gauss_int_def
    by (subst real_gauss_int_norm [symmetric]) (auto simp add: divide_gauss_int_def a'_def b'_def)
  also have "gauss2complex (a - round_complex (a' / b') * b) =
               a' - gauss2complex (round_complex (a' / b')) * b'"
    by (simp add: a'_def b'_def)
  also have "\<dots> = (a' / b' - gauss2complex (round_complex (a' / b'))) * b'"
    by (simp add: field_simps)
  also have "norm \<dots> ^ 2 = norm (a' / b' - gauss2complex (round_complex (a' / b'))) ^ 2 * norm b' ^ 2"
    by (simp add: norm_mult power_mult_distrib)
  also have "\<dots> \<le> 1 / 2 * norm b' ^ 2"
    by (intro mult_right_mono norm_round_complex_le) auto
  also have "norm b' ^ 2 = gauss_int_norm b"
    by (simp add: b'_def real_gauss_int_norm)
  finally show ?thesis by linarith
qed

lemma gauss_int_norm_mod_less:
  assumes [simp]: "b \<noteq> 0"
  shows   "gauss_int_norm (a mod b) < gauss_int_norm b"
proof -
  have "gauss_int_norm b > 0" by simp
  thus "gauss_int_norm (a mod b) < gauss_int_norm b"
    using gauss_int_norm_mod_less_aux[OF assms, of a] by presburger
qed

lemma gauss_int_norm_dvd_imp_le:
  assumes "b \<noteq> 0"
  shows   "gauss_int_norm a \<le> gauss_int_norm (a * b)"
proof (cases "a = 0")
  case False
  thus ?thesis using assms by (intro dvd_imp_le gauss_int_norm_dvd_mono) auto
qed auto

instantiation gauss_int :: euclidean_ring
begin

definition euclidean_size_gauss_int :: "gauss_int \<Rightarrow> nat" where
  [simp]: "euclidean_size_gauss_int = gauss_int_norm"

instance proof
  show "euclidean_size (0 :: gauss_int) = 0"
    by simp
next
  fix a b :: gauss_int assume [simp]: "b \<noteq> 0"
  show "euclidean_size (a mod b) < euclidean_size b"
    using gauss_int_norm_mod_less[of b a] by simp
  show "euclidean_size a \<le> euclidean_size (a * b)"
    by (simp add: gauss_int_norm_dvd_imp_le)
qed

end

instance gauss_int :: normalization_euclidean_semiring ..

instantiation gauss_int :: euclidean_ring_gcd
begin

definition gcd_gauss_int :: "gauss_int \<Rightarrow> gauss_int \<Rightarrow> gauss_int" where
  "gcd_gauss_int \<equiv> normalization_euclidean_semiring_class.gcd"
definition lcm_gauss_int :: "gauss_int \<Rightarrow> gauss_int \<Rightarrow> gauss_int" where
  "lcm_gauss_int \<equiv> normalization_euclidean_semiring_class.lcm"
definition Gcd_gauss_int :: "gauss_int set \<Rightarrow> gauss_int" where
  "Gcd_gauss_int \<equiv> normalization_euclidean_semiring_class.Gcd"
definition Lcm_gauss_int :: "gauss_int set \<Rightarrow> gauss_int" where
  "Lcm_gauss_int \<equiv> normalization_euclidean_semiring_class.Lcm"

instance 
  by intro_classes
     (simp_all add: gcd_gauss_int_def lcm_gauss_int_def Gcd_gauss_int_def Lcm_gauss_int_def)

end

lemma multiplicity_gauss_cnj: "multiplicity (gauss_cnj a) (gauss_cnj b) = multiplicity a b"
  unfolding multiplicity_def gauss_cnj_power [symmetric] gauss_cnj_dvd_iff ..
    
lemma multiplicity_gauss_int_of_nat:
  "multiplicity (of_nat a) (of_nat b :: gauss_int) = multiplicity a b"
  unfolding multiplicity_def of_nat_power [symmetric] of_nat_dvd_of_nat_gauss_int_iff ..

lemma gauss_int_dvd_same_norm_imp_associated:
  assumes "z1 dvd z2" "gauss_int_norm z1 = gauss_int_norm z2"
  shows   "normalize z1 = normalize z2"
proof (cases "z1 = 0")
  case [simp]: False
  from assms(1) obtain u where u: "z2 = z1 * u" by blast
  from assms have "gauss_int_norm u = 1"
    by (auto simp: gauss_int_norm_mult u)
  hence "is_unit u"
    by (simp add: is_unit_gauss_int_iff')
  with u show ?thesis by simp
qed (use assms in auto)

lemma gcd_of_int_gauss_int: "gcd (of_int a :: gauss_int) (of_int b) = of_int (gcd a b)"
proof (induction "nat \<bar>b\<bar>" arbitrary: a b rule: less_induct)
  case (less b a)
  show ?case
  proof (cases "b = 0")
    case False
    have "of_int (gcd a b) = (of_int (gcd b (a mod b)) :: gauss_int)"
      by (subst gcd_red_int) auto
    also have "\<dots> = gcd (of_int b) (of_int (a mod b))"
      using False by (intro less [symmetric]) (auto intro!: abs_mod_less)
    also have "a mod b = (a - a div b * b)"
      by (simp add: minus_div_mult_eq_mod)
    also have "of_int \<dots> = of_int (-(a div b)) * of_int b + (of_int a :: gauss_int)"
      by (simp add: algebra_simps)
    also have "gcd (of_int b) \<dots> = gcd (of_int b) (of_int a)"
      by (rule gcd_add_mult)
    finally show ?thesis by (simp add: gcd.commute)
  qed auto
qed

lemma coprime_of_int_gauss_int: "coprime (of_int a :: gauss_int) (of_int b) = coprime a b"
  unfolding coprime_iff_gcd_eq_1 gcd_of_int_gauss_int by auto

lemma gcd_of_nat_gauss_int: "gcd (of_nat a :: gauss_int) (of_nat b) = of_nat (gcd a b)"
  using gcd_of_int_gauss_int[of "int a" "int b"] by simp

lemma coprime_of_nat_gauss_int: "coprime (of_nat a :: gauss_int) (of_nat b) = coprime a b"
  unfolding coprime_iff_gcd_eq_1 gcd_of_nat_gauss_int by auto

lemma gauss_cnj_dvd_self_iff: "gauss_cnj z dvd z \<longleftrightarrow> ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
proof
  assume "gauss_cnj z dvd z"
  hence "normalize (gauss_cnj z) = normalize z"
    by (rule gauss_int_dvd_same_norm_imp_associated) auto
  then obtain u :: gauss_int where "is_unit u"  and u: "gauss_cnj z = u * z"
    using associatedE1 by blast
  hence "u \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int>}"
    by (simp add: is_unit_gauss_int_iff)
  thus "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
  proof (elim insertE emptyE)
    assume [simp]: "u = \<i>\<^sub>\<int>"
    have "ReZ z = ReZ (gauss_cnj z)"
      by simp
    also have "gauss_cnj z = \<i>\<^sub>\<int> * z"
      using u by simp
    also have "ReZ \<dots> = -ImZ z"
      by simp
    finally show "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
      by auto
  next
    assume [simp]: "u = -\<i>\<^sub>\<int>"
    have "ReZ z = ReZ (gauss_cnj z)"
      by simp
    also have "gauss_cnj z = -\<i>\<^sub>\<int> * z"
      using u by simp
    also have "ReZ \<dots> = ImZ z"
      by simp
    finally show "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
      by auto
  next
    assume [simp]: "u = 1"
    have "ImZ z = -ImZ (gauss_cnj z)"
      by simp
    also have "gauss_cnj z = z"
      using u by simp
    finally show "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
      by auto
  next
    assume [simp]: "u = -1"
    have "ReZ z = ReZ (gauss_cnj z)"
      by simp
    also have "gauss_cnj z = -z"
      using u by simp
    also have "ReZ \<dots> = -ReZ z"
      by simp
    finally show "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
      by auto
  qed
next
  assume "ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
  thus "gauss_cnj z dvd z"
  proof safe
    assume "\<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
    then obtain u :: int where "is_unit u" and u: "ImZ z = u * ReZ z"
      using associatedE2[of "ReZ z" "ImZ z"] by auto
    from \<open>is_unit u\<close> have "u \<in> {1, -1}"
      by auto
    hence "z = gauss_cnj z * (of_int u * \<i>\<^sub>\<int>)"
      using u by (auto simp: gauss_int_eq_iff)
    thus ?thesis
      by (metis dvd_triv_left)
  qed (auto simp: gauss_cnj_eq_self gauss_cnj_eq_minus_self)
qed

lemma self_dvd_gauss_cnj_iff: "z dvd gauss_cnj z \<longleftrightarrow> ReZ z = 0 \<or> ImZ z = 0 \<or> \<bar>ReZ z\<bar> = \<bar>ImZ z\<bar>"
  using gauss_cnj_dvd_self_iff[of z] by (subst (asm) gauss_cnj_dvd_left_iff) auto


subsection \<open>Prime elements\<close>

text \<open>
  Next, we analyse what the prime elements of the Gaussian integers are. First, note that
  according to the conventions of Isabelle's computational algebra library, a prime element
  is called a prime iff it is also normalised, i.e.\ in our case it lies in the upper right
  quadrant.

  As a first fact, we can show that a Gaussian integer whose norm is \<open>\<int>\<close>-prime must be
  $\mathbb{Z}[i]$-prime:
\<close>

lemma prime_gauss_int_norm_imp_prime_elem:
  assumes "prime (gauss_int_norm q)"
  shows   "prime_elem q"
proof -
  have "irreducible q"
  proof (rule irreducibleI)
    fix a b assume "q = a * b"
    hence "gauss_int_norm q = gauss_int_norm a * gauss_int_norm b"
      by (simp_all add: gauss_int_norm_mult)
    thus "is_unit a \<or> is_unit b"
      using assms by (auto dest!: prime_product simp: gauss_int_norm_eq_Suc_0_iff)
  qed (use assms in \<open>auto simp: is_unit_gauss_int_iff'\<close>)
  thus "prime_elem q"
    using irreducible_imp_prime_elem_gcd by blast
qed

text \<open>
  Also, a conjugate is a prime element iff the original element is a prime element:
\<close>
lemma prime_elem_gauss_cnj [intro]: "prime_elem z \<Longrightarrow> prime_elem (gauss_cnj z)"
  by (auto simp: prime_elem_def gauss_cnj_dvd_left_iff)

lemma prime_elem_gauss_cnj_iff [simp]: "prime_elem (gauss_cnj z) \<longleftrightarrow> prime_elem z"
  using prime_elem_gauss_cnj[of z] prime_elem_gauss_cnj[of "gauss_cnj z"] by auto


subsubsection \<open>The factorisation of 2\<close>

text \<open>
  2 factors as $-i (1 + i)^2$ in the Gaussian integers, where $-i$ is a unit and
  $1 + i$ is prime.
\<close>

lemma gauss_int_2_eq: "2 = -\<i>\<^sub>\<int> * (1 + \<i>\<^sub>\<int>) ^ 2"
  by (simp add: gauss_int_eq_iff power2_eq_square)

lemma prime_elem_one_plus_i_gauss_int: "prime_elem (1 + \<i>\<^sub>\<int>)"
  by (rule prime_gauss_int_norm_imp_prime_elem) (auto simp: gauss_int_norm_def)

lemma prime_one_plus_i_gauss_int: "prime (1 + \<i>\<^sub>\<int>)"
  by (simp add: prime_def prime_elem_one_plus_i_gauss_int
                gauss_int_eq_iff normalize_gauss_int_def)

lemma prime_factorization_2_gauss_int:
  "prime_factorization (2 :: gauss_int) = {#1 + \<i>\<^sub>\<int>, 1 + \<i>\<^sub>\<int>#}"
proof -
  have "prime_factorization (2 :: gauss_int) =
        (prime_factorization (prod_mset {#1 + gauss_i, 1 + gauss_i#}))"
    by (subst prime_factorization_unique) (auto simp: gauss_int_eq_iff normalize_gauss_int_def)
  also have "prime_factorization (prod_mset {#1 + gauss_i, 1 + gauss_i#}) =
               {#1 + gauss_i, 1 + gauss_i#}"
    using prime_one_plus_i_gauss_int by (subst prime_factorization_prod_mset_primes) auto
  finally show ?thesis .
qed


subsubsection \<open>Inert primes\<close>

text \<open>
  Any \<open>\<int>\<close>-prime congruent 3 modulo 4 is also a Gaussian prime. These primes are called
  \<^emph>\<open>inert\<close>, because they do not decompose when moving from \<open>\<int>\<close> to $\mathbb{Z}[i]$.
\<close>

lemma gauss_int_norm_not_3_mod_4: "[gauss_int_norm z \<noteq> 3] (mod 4)"
proof -
  have A: "ReZ z mod 4 \<in> {0..3}" "ImZ z mod 4 \<in> {0..3}" by auto
  have B: "{0..3} = {0, 1, 2, 3 :: int}" by auto

  have "[ReZ z ^ 2 + ImZ z ^ 2 = (ReZ z mod 4) ^ 2 + (ImZ z mod 4) ^ 2] (mod 4)"
    by (intro cong_add cong_pow) (auto simp: cong_def)
  moreover have "((ReZ z mod 4) ^ 2 + (ImZ z mod 4) ^ 2) mod 4 \<noteq> 3 mod 4"
    using A unfolding B by auto
  ultimately have "[ReZ z ^ 2 + ImZ z ^ 2 \<noteq> 3] (mod 4)"
    unfolding cong_def by metis
  hence "[int (nat (ReZ z ^ 2 + ImZ z ^ 2)) \<noteq> int 3] (mod (int 4))"
    by simp
  thus ?thesis unfolding gauss_int_norm_def
    by (subst (asm) cong_int_iff)
qed

lemma prime_elem_gauss_int_of_nat:
  fixes n :: nat
  assumes prime: "prime n" and "[n = 3] (mod 4)"
  shows   "prime_elem (of_nat n :: gauss_int)"
proof (intro irreducible_imp_prime_elem irreducibleI)
  from assms show "of_nat n \<noteq> (0 :: gauss_int)"
    by (auto simp: gauss_int_eq_iff)
next
  show "\<not>is_unit (of_nat n :: gauss_int)"
    using assms by (subst is_unit_gauss_int_iff) (auto simp: gauss_int_eq_iff)
next
  fix a b :: gauss_int
  assume *: "of_nat n = a * b"
  hence "gauss_int_norm (a * b) = gauss_int_norm (of_nat n)"
    by metis
  hence *: "gauss_int_norm a * gauss_int_norm b = n ^ 2"
    by (simp add: gauss_int_norm_mult power2_eq_square flip: nat_mult_distrib)
  from prime_power_mult_nat[OF prime this] obtain i j :: nat
    where ij: "gauss_int_norm a = n ^ i" "gauss_int_norm b = n ^ j" by blast
  
  have "i + j = 2"
  proof -
    have "n ^ (i + j) = n ^ 2"
      using ij * by (simp add: power_add)
    from prime_power_inj[OF prime this] show ?thesis by simp
  qed
  hence "i = 0 \<and> j = 2 \<or> i = 1 \<and> j = 1 \<or> i = 2 \<and> j = 0"
    by auto
  thus "is_unit a \<or> is_unit b"
  proof (elim disjE)
    assume "i = 1 \<and> j = 1"
    with ij have "gauss_int_norm a = n"
      by auto
    hence "[gauss_int_norm a = n] (mod 4)"
      by simp
    also have "[n = 3] (mod 4)" by fact
    finally have "[gauss_int_norm a = 3] (mod 4)" .
    moreover have "[gauss_int_norm a \<noteq> 3] (mod 4)"
      by (rule gauss_int_norm_not_3_mod_4)
    ultimately show ?thesis by contradiction
  qed (use ij in \<open>auto simp: is_unit_gauss_int_iff'\<close>)
qed

theorem prime_gauss_int_of_nat:
  fixes n :: nat
  assumes prime: "prime n" and "[n = 3] (mod 4)"
  shows   "prime (of_nat n :: gauss_int)"
  using prime_elem_gauss_int_of_nat[OF assms]
  unfolding prime_def by simp


subsubsection \<open>Non-inert primes\<close>

text \<open>
  Any \<open>\<int>\<close>-prime congruent 1 modulo 4 factors into two conjugate Gaussian primes.
\<close>

lemma minimal_QuadRes_neg1:
  assumes "QuadRes n (-1)" "n > 1" "odd n"
  obtains x :: nat where "x \<le> (n - 1) div 2" and "[x ^ 2 + 1 = 0] (mod n)"
proof -
  from \<open>QuadRes n (-1)\<close> obtain x where "[x ^ 2 = (-1)] (mod (int n))"
    by (auto simp: QuadRes_def)
  hence "[x ^ 2 + 1 = -1 + 1] (mod (int n))"
    by (intro cong_add) auto
  also have "x ^ 2 + 1 = int (nat \<bar>x\<bar> ^ 2 + 1)"
    by simp
  finally have "[int (nat \<bar>x\<bar> ^ 2 + 1) = int 0] (mod (int n))"
    by simp
  hence "[nat \<bar>x\<bar> ^ 2 + 1 = 0] (mod n)"
    by (subst (asm) cong_int_iff)

  define x' where
    "x' = (if nat \<bar>x\<bar> mod n \<le> (n - 1) div 2 then nat \<bar>x\<bar> mod n else n - (nat \<bar>x\<bar> mod n))"
  have x'_quadres: "[x' ^ 2 + 1 = 0] (mod n)"
  proof (cases "nat \<bar>x\<bar> mod n \<le> (n - 1) div 2")
    case True
    hence "[x' ^ 2 + 1 = (nat \<bar>x\<bar> mod n) ^ 2 + 1] (mod n)"
      by (simp add: x'_def)
    also have "[(nat \<bar>x\<bar> mod n) ^ 2 + 1 = nat \<bar>x\<bar> ^ 2 + 1] (mod n)"
      by (intro cong_add cong_pow) (auto simp: cong_def)
    also have "[nat \<bar>x\<bar> ^ 2 + 1 = 0] (mod n)" by fact
    finally show ?thesis .
  next
    case False
    hence "[int (x' ^ 2 + 1) = (int n - int (nat \<bar>x\<bar> mod n)) ^ 2 + 1] (mod int n)"
      using \<open>n > 1\<close> by (simp add: x'_def of_nat_diff add_ac)
    also have "[(int n - int (nat \<bar>x\<bar> mod n)) ^ 2 + 1 =
                (0 - int (nat \<bar>x\<bar> mod n)) ^ 2 + 1] (mod int n)"
      by (intro cong_add cong_pow) (auto simp: cong_def)
    also have "[(0 - int (nat \<bar>x\<bar> mod n)) ^ 2 + 1 = int ((nat \<bar>x\<bar> mod n) ^ 2 + 1)] (mod (int n))"
      by (simp add: add_ac)
    finally have "[x' ^ 2 + 1 = (nat \<bar>x\<bar> mod n)\<^sup>2 + 1] (mod n)"
      by (subst (asm) cong_int_iff)
    also have "[(nat \<bar>x\<bar> mod n)\<^sup>2 + 1 = nat \<bar>x\<bar> ^ 2 + 1] (mod n)"
      by (intro cong_add cong_pow) (auto simp: cong_def)
    also have "[nat \<bar>x\<bar> ^ 2 + 1 = 0] (mod n)" by fact
    finally show ?thesis .
  qed
  moreover have x'_le: "x' \<le> (n - 1) div 2"
    using \<open>odd n\<close> by (auto elim!: oddE simp: x'_def)
  ultimately show ?thesis by (intro that[of x'])
qed

text \<open>
  Let \<open>p\<close> be some prime number that is congruent 1 modulo 4.
\<close>
locale noninert_gauss_int_prime =
  fixes p :: nat
  assumes prime_p: "prime p" and cong_1_p: "[p = 1] (mod 4)"
begin

lemma p_gt_2: "p > 2" and odd_p: "odd p"
proof -
  from prime_p and cong_1_p have "p > 1" "p \<noteq> 2"
    by (auto simp: prime_gt_Suc_0_nat cong_def)
  thus "p > 2" by auto
  with prime_p show "odd p"
    using primes_dvd_imp_eq two_is_prime_nat by blast
qed

text \<open>
  -1 is a quadratic residue modulo \<open>p\<close>, so there exists some \<open>x\<close> such that
  $x^2 + 1$ is divisible by \<open>p\<close>. Moreover, we can choose \<open>x\<close> such that it is positive and
  no greater than $\frac{1}{2}(p-1)$:
\<close>
lemma minimal_QuadRes_neg1:
  obtains x where "x > 0" "x \<le> (p - 1) div 2" "[x ^ 2 + 1 = 0] (mod p)"
proof -
  have "[Legendre (-1) (int p) = (- 1) ^ ((p - 1) div 2)] (mod (int p))"
    using prime_p p_gt_2 by (intro euler_criterion) auto
  also have "[p - 1 = 1 - 1] (mod 4)"
    using p_gt_2 by (intro cong_diff_nat cong_refl) (use cong_1_p in auto)
  hence "2 * 2 dvd p - 1"
    by (simp add: cong_0_iff)
  hence "even ((p - 1) div 2)"
    using dvd_mult_imp_div by blast
  hence "(-1) ^ ((p - 1) div 2) = (1 :: int)"
    by simp
  finally have "Legendre (-1) (int p) mod p = 1"
    using p_gt_2 by (auto simp: cong_def)
  hence "Legendre (-1) (int p) = 1"
    using p_gt_2 by (auto simp: Legendre_def cong_def zmod_minus1 split: if_splits)
  hence "QuadRes p (-1)"
    by (simp add: Legendre_def split: if_splits)
  from minimal_QuadRes_neg1[OF this] p_gt_2 odd_p
    obtain x where x: "x \<le> (p - 1) div 2" "[x ^ 2 + 1 = 0] (mod p)" by auto
  have "x > 0"
    using x p_gt_2 by (auto intro!: Nat.gr0I simp: cong_def)
  from x and this show ?thesis by (intro that[of x]) auto
qed

text \<open>
  We can show from this that \<open>p\<close> is not prime as a Gaussian integer.
\<close>
lemma not_prime: "\<not>prime_elem (of_nat p :: gauss_int)"
proof
  assume prime: "prime_elem (of_nat p :: gauss_int)"
  obtain x where x: "x > 0" "x \<le> (p - 1) div 2" "[x ^ 2 + 1 = 0] (mod p)"
    using  minimal_QuadRes_neg1 .

  have "of_nat p dvd (of_nat (x ^ 2 + 1) :: gauss_int)"
    using x by (intro of_nat_dvd_of_nat) (auto simp: cong_0_iff)
  also have eq: "of_nat (x ^ 2 + 1) = ((of_nat x + \<i>\<^sub>\<int>) * (of_nat x - \<i>\<^sub>\<int>) :: gauss_int)"
    using \<open>x > 0\<close> by (simp add: algebra_simps gauss_int_eq_iff power2_eq_square of_nat_diff)
  finally have "of_nat p dvd ((of_nat x + \<i>\<^sub>\<int>) * (of_nat x - \<i>\<^sub>\<int>) :: gauss_int)" .

  from prime and this
    have "of_nat p dvd (of_nat x + \<i>\<^sub>\<int> :: gauss_int) \<or> of_nat p dvd (of_nat x - \<i>\<^sub>\<int> :: gauss_int)"
    by (rule prime_elem_dvd_multD)
  hence dvd: "of_nat p dvd (of_nat x + \<i>\<^sub>\<int> :: gauss_int)" "of_nat p dvd (of_nat x - \<i>\<^sub>\<int> :: gauss_int)"
    by (auto dest: of_nat_dvd_imp_dvd_gauss_cnj)

  have "of_nat (p ^ 2) = (of_nat p * of_nat p :: gauss_int)"
    by (simp add: power2_eq_square)
  also from dvd have "\<dots> dvd ((of_nat x + \<i>\<^sub>\<int>) * (of_nat x - \<i>\<^sub>\<int>))"
    by (intro mult_dvd_mono)
  also have "\<dots> = of_nat (x ^ 2 + 1)"
    by (rule eq [symmetric])
  finally have "p ^ 2 dvd (x ^ 2 + 1)"
    by (subst (asm) of_nat_dvd_of_nat_gauss_int_iff)
  hence "p ^ 2 \<le> x ^ 2 + 1"
    by (intro dvd_imp_le) auto
  moreover have "p ^ 2 > x ^ 2 + 1"
  proof -
    have "x ^ 2 + 1 \<le> ((p - 1) div 2) ^ 2 + 1"
      using x by (intro add_mono power_mono) auto
    also have "\<dots> \<le> (p - 1) ^ 2 + 1"
      by auto
    also have "(p - 1) * (p - 1) < (p - 1) * (p + 1)"
      using p_gt_2 by (intro mult_strict_left_mono) auto
    hence "(p - 1) ^ 2 + 1 < p ^ 2"
      by (simp add: algebra_simps power2_eq_square)
    finally show ?thesis .
  qed
  ultimately show False by linarith
qed

text \<open>
  Any prime factor of \<open>p\<close> in the Gaussian integers must have norm \<open>p\<close>.
\<close>
lemma norm_prime_divisor:
  fixes q :: gauss_int
  assumes q: "prime_elem q" "q dvd of_nat p"
  shows "gauss_int_norm q = p"
proof -
  from assms obtain r where r: "of_nat p = q * r"
    by auto
  have "p ^ 2 = gauss_int_norm (of_nat p)"
    by simp
  also have "\<dots> = gauss_int_norm q * gauss_int_norm r"
    by (auto simp: r gauss_int_norm_mult)
  finally have *: "gauss_int_norm q * gauss_int_norm r = p ^ 2"
    by simp
  hence "\<exists>i j. gauss_int_norm q = p ^ i \<and> gauss_int_norm r = p ^ j"
    using prime_p by (intro prime_power_mult_nat)
  then obtain i j where ij: "gauss_int_norm q = p ^ i" "gauss_int_norm r = p ^ j"
    by blast
  have ij_eq_2: "i + j = 2"
  proof -
    from * have "p ^ (i + j) = p ^ 2"
      by (simp add: power_add ij)
    thus ?thesis
      using p_gt_2 by (subst (asm) power_inject_exp) auto
  qed
  hence "i = 0 \<and> j = 2 \<or> i = 1 \<and> j = 1 \<or> i = 2 \<and> j = 0" by auto
  hence "i = 1"
  proof (elim disjE)
    assume "i = 2 \<and> j = 0"
    hence "is_unit r"
      using ij by (simp add: gauss_int_norm_eq_Suc_0_iff)
    hence "prime_elem (of_nat p :: gauss_int)" using \<open>prime_elem q\<close>
      by (simp add: prime_elem_mult_unit_left r mult.commute[of _ r])
    with not_prime show "i = 1" by contradiction
  qed (use q ij in \<open>auto simp: gauss_int_norm_eq_Suc_0_iff\<close>)
  thus ?thesis using ij by simp
qed

text \<open>
  We now show two lemmas that characterise the two prime factors of \<open>p\<close> in the
  Gaussian integers: they are two conjugates $x\pm iy$ for positive integers \<open>x\<close> and \<open>y\<close> such
  that $x^2 + y^2 = p$.
\<close>
lemma prime_divisor_exists:
  obtains q where "prime q" "prime_elem (gauss_cnj q)" "ReZ q > 0" "ImZ q > 0"
                  "of_nat p = q * gauss_cnj q" "gauss_int_norm q = p"
proof -
  have "\<exists>q::gauss_int. q dvd of_nat p \<and> prime q"
    by (rule prime_divisor_exists) (use prime_p in \<open>auto simp: is_unit_gauss_int_iff'\<close>)
  then obtain q :: gauss_int where q: "prime q" "q dvd of_nat p"
    by blast
  from \<open>prime q\<close> have [simp]: "q \<noteq> 0" by auto
  have "normalize q = q"
    using q by simp
  hence q_signs: "ReZ q > 0" "ImZ q \<ge> 0"
    by (subst (asm) normalized_gauss_int_iff; simp)+
  
  from q have "gauss_int_norm q = p"
    using norm_prime_divisor[of q] by simp
  moreover from this have "gauss_int_norm (gauss_cnj q) = p"
    by simp
  hence "prime_elem (gauss_cnj q)"
    using prime_p by (intro prime_gauss_int_norm_imp_prime_elem) auto
  moreover have "of_nat p = q * gauss_cnj q"
    using \<open>gauss_int_norm q = p\<close> by (simp add: self_mult_gauss_cnj)
  moreover have "ImZ q \<noteq> 0"
  proof
    assume [simp]: "ImZ q = 0"
    define m where "m = nat (ReZ q)"
    have [simp]: "q = of_nat m"
      using q_signs by (auto simp: gauss_int_eq_iff m_def)
    with q have "m dvd p"
      by (simp add: of_nat_dvd_of_nat_gauss_int_iff)
    with prime_p have "m = 1 \<or> m = p"
      using prime_nat_iff by blast
    with q show False using not_prime by auto
  qed
  with q_signs have "ImZ q > 0" by simp
  ultimately show ?thesis using q q_signs by (intro that[of q])
qed

theorem prime_factorization:
  obtains q1 q2
  where "prime q1" "prime q2" "prime_factorization (of_nat p) = {#q1, q2#}" 
        "gauss_int_norm q1 = p" "gauss_int_norm q2 = p" "q2 = \<i>\<^sub>\<int> * gauss_cnj q1"
        "ReZ q1 > 0" "ImZ q1 > 0" "ReZ q1 > 0" "ImZ q2 > 0"
proof -
  obtain q where q: "prime q" "prime_elem (gauss_cnj q)" "ReZ q > 0" "ImZ q > 0"
                    "of_nat p = q * gauss_cnj q" "gauss_int_norm q = p"
    using prime_divisor_exists by metis
  from \<open>prime q\<close> have [simp]: "q \<noteq> 0" by auto
  define q' where "q' = normalize (gauss_cnj q)"
  have "prime_factorization (of_nat p) = prime_factorization (prod_mset {#q, q'#})"
    by (subst prime_factorization_unique) (auto simp: q q'_def)
  also have "\<dots> = {#q, q'#}"
    using q by (subst prime_factorization_prod_mset_primes) (auto simp: q'_def)
  finally have "prime_factorization (of_nat p) = {#q, q'#}" .
  moreover have "q' = \<i>\<^sub>\<int> * gauss_cnj q"
    using q by (auto simp: normalize_gauss_int_def q'_def)
  moreover have "prime q'"
    using q by (auto simp: q'_def)
  ultimately show ?thesis using q
    by (intro that[of q q']) (auto simp: q'_def gauss_int_norm_mult)
qed

end

text \<open>
  In particular, a consequence of this is that any prime congruent 1 modulo 4
  can be written as a sum of squares of positive integers.
\<close>
lemma prime_cong_1_mod_4_gauss_int_norm_exists:
  fixes p :: nat
  assumes "prime p" "[p = 1] (mod 4)"
  shows   "\<exists>z. gauss_int_norm z = p \<and> ReZ z > 0 \<and> ImZ z > 0"
proof -
  from assms interpret noninert_gauss_int_prime p
    by unfold_locales
  from prime_divisor_exists obtain q
    where q: "prime q" "of_nat p = q * gauss_cnj q" 
             "ReZ q > 0" "ImZ q > 0" "gauss_int_norm q = p" by metis
  have "p = gauss_int_norm q"
    using q by simp
  thus ?thesis using q by blast
qed


subsubsection \<open>Full classification of Gaussian primes\<close>

text \<open>
  Any prime in the ring of Gaussian integers is of the form

    \<^item> \<open>1 + \<i>\<^sub>\<int>\<close>

    \<^item> \<open>p\<close> where \<open>p \<in> \<nat>\<close> is prime in \<open>\<nat>\<close> and congruent 1 modulo 4

    \<^item> $x + iy$ where $x,y$ are positive integers and $x^2 + y^2$ is a prime congruent 3 modulo 4

  or an associated element of one of these.  
\<close>
theorem gauss_int_prime_classification:
  fixes x :: gauss_int
  assumes "prime x"
  obtains 
    (one_plus_i) "x = 1 + \<i>\<^sub>\<int>"
  | (cong_3_mod_4) p where "x = of_nat p" "prime p" "[p = 3] (mod 4)"
  | (cong_1_mod_4) "prime (gauss_int_norm x)" "[gauss_int_norm x = 1] (mod 4)"
                   "ReZ x > 0" "ImZ x > 0" "ReZ x \<noteq> ImZ x"
proof -
  define N where "N = gauss_int_norm x"
  have "x dvd x * gauss_cnj x"
    by simp
  also have "\<dots> = of_nat (gauss_int_norm x)"
    by (simp add: self_mult_gauss_cnj)
  finally have "x \<in> prime_factors (of_nat N)"
    using assms by (auto simp: in_prime_factors_iff N_def)
  also have "N = prod_mset (prime_factorization N)"
    using assms unfolding N_def by (subst prod_mset_prime_factorization_nat) auto
  also have "(of_nat \<dots> :: gauss_int) = 
               prod_mset (image_mset of_nat (prime_factorization N))"
    by (subst of_nat_prod_mset) auto
  also have "prime_factors \<dots> = (\<Union>p\<in>prime_factors N. prime_factors (of_nat p))"
    by (subst prime_factorization_prod_mset) auto
  finally obtain p where p: "p \<in> prime_factors N" "x \<in> prime_factors (of_nat p)"
    by auto

  have "prime p"
    using p by auto
  hence "\<not>(2 * 2) dvd p"
    using product_dvd_irreducibleD[of p 2 2]
    by (auto simp flip: prime_elem_iff_irreducible)
  hence "[p \<noteq> 0] (mod 4)"
    using p by (auto simp: cong_0_iff in_prime_factors_iff)
  hence "p mod 4 \<in> {1,2,3}" by (auto simp: cong_def)
  thus ?thesis
  proof (elim singletonE insertE)
    assume "p mod 4 = 2"
    hence "p mod 4 mod 2 = 0"
      by simp
    hence "p mod 2 = 0"
      by (simp add: mod_mod_cancel)
    with \<open>prime p\<close> have [simp]: "p = 2"
      using prime_prime_factor two_is_prime_nat by blast
    have "prime_factors (of_nat p) = {1 + \<i>\<^sub>\<int> :: gauss_int}"
      by (simp add: prime_factorization_2_gauss_int)
    with p show ?thesis using that(1) by auto
  next
    assume *: "p mod 4 = 3"
    hence "prime_factors (of_nat p) = {of_nat p :: gauss_int}"
      using prime_gauss_int_of_nat[of p] \<open>prime p\<close>
      by (subst prime_factorization_prime) (auto simp: cong_def)
    with p show ?thesis using that(2)[of p] *
      by (auto simp: cong_def)
  next
    assume *: "p mod 4 = 1"
    then interpret noninert_gauss_int_prime p
      by unfold_locales (use \<open>prime p\<close> in \<open>auto simp: cong_def\<close>)
    obtain q1 q2 :: gauss_int where q12:
      "prime q1" "prime q2" "prime_factorization (of_nat p) = {#q1, q2#}"
      "gauss_int_norm q1 = p" "gauss_int_norm q2 = p" "q2 = \<i>\<^sub>\<int> * gauss_cnj q1"
      "ReZ q1 > 0" "ImZ q1 > 0" "ReZ q1 > 0" "ImZ q2 > 0"
      using prime_factorization by metis
    from p q12 have "x = q1 \<or> x = q2" by auto
    with q12 have **: "gauss_int_norm x = p" "ReZ x > 0" "ImZ x > 0"
      by auto
    have "ReZ x \<noteq> ImZ x"
    proof
      assume "ReZ x = ImZ x"
      hence "even (gauss_int_norm x)"
        by (auto simp: gauss_int_norm_def nat_mult_distrib)
      hence "even p" using \<open>gauss_int_norm x = p\<close>
        by simp
      with \<open>p mod 4 = 1\<close> show False
        by presburger
    qed
    thus ?thesis using that(3) \<open>prime p\<close> * **
      by (simp add: cong_def)
  qed
qed

lemma prime_gauss_int_norm_squareD:
  fixes z :: gauss_int
  assumes "prime z" "gauss_int_norm z = p ^ 2"
  shows   "prime p \<and> z = of_nat p"
  using assms(1)
proof (cases rule: gauss_int_prime_classification)
  case one_plus_i
  have "prime (2 :: nat)" by simp
  also from one_plus_i have "2 = p ^ 2"
    using assms(2) by (auto simp: gauss_int_norm_def)
  finally show ?thesis by (simp add: prime_power_iff)
next
  case (cong_3_mod_4 p)
  thus ?thesis using assms by auto
next
  case cong_1_mod_4
  with assms show ?thesis
    by (auto simp: prime_power_iff)
qed

lemma gauss_int_norm_eq_prime_squareD:
  assumes "prime p" and "[p = 3] (mod 4)" and "gauss_int_norm z = p ^ 2"
  shows   "normalize z = of_nat p" and "prime_elem z"
proof -
  have "\<exists>q::gauss_int. q dvd z \<and> prime q"
    by (rule prime_divisor_exists) (use assms in \<open>auto simp: is_unit_gauss_int_iff'\<close>)
  then obtain q :: gauss_int where q: "q dvd z" "prime q" by blast
  have "gauss_int_norm q dvd gauss_int_norm z"
    by (rule gauss_int_norm_dvd_mono) fact
  also have "\<dots> = p ^ 2" by fact
  finally obtain i where i: "i \<le> 2" "gauss_int_norm q = p ^ i"
    by (subst (asm) divides_primepow_nat) (use assms q in auto)
  from i assms q have "i \<noteq> 0"
    by (auto intro!: Nat.gr0I simp: gauss_int_norm_eq_Suc_0_iff)
  moreover from i assms q have "i \<noteq> 1"
    using gauss_int_norm_not_3_mod_4[of q] by auto
  ultimately have "i = 2" using i by auto
  with i have "gauss_int_norm q = p ^ 2" by auto
  hence [simp]: "q = of_nat p"
    using prime_gauss_int_norm_squareD[of q p] q by auto
  have "normalize (of_nat p) = normalize z"
    using q assms
    by (intro gauss_int_dvd_same_norm_imp_associated) auto
  thus *: "normalize z = of_nat p" by simp

  have "prime (normalize z)"
    using prime_gauss_int_of_nat[of p] assms by (subst *) auto
  thus "prime_elem z" by simp
qed

text \<open>
  The following can be used as a primality test for Gaussian integers. It effectively
  reduces checking the primality of a Gaussian integer to checking the primality of an
  integer.

  A Gaussian integer is prime if either its norm is either \<open>\<int>\<close>-prime or the square of
  a \<open>\<int>\<close>-prime that is congruent 3 modulo 4.
\<close>
lemma prime_elem_gauss_int_iff:
  fixes z :: gauss_int
  defines "n \<equiv> gauss_int_norm z"
  shows   "prime_elem z \<longleftrightarrow> prime n \<or> (\<exists>p. n = p ^ 2 \<and> prime p \<and> [p = 3] (mod 4))"
proof
  assume "prime n \<or> (\<exists>p. n = p ^ 2 \<and> prime p \<and> [p = 3] (mod 4))"
  thus "prime_elem z"
    by (auto intro: gauss_int_norm_eq_prime_squareD(2)
                    prime_gauss_int_norm_imp_prime_elem simp: n_def)
next
  assume "prime_elem z"
  hence "prime (normalize z)" by simp
  thus "prime n \<or> (\<exists>p. n = p ^ 2 \<and> prime p \<and> [p = 3] (mod 4))"
  proof (cases rule: gauss_int_prime_classification)
    case one_plus_i
    have "n = gauss_int_norm (normalize z)"
      by (simp add: n_def)
    also have "normalize z = 1 + \<i>\<^sub>\<int>"
      by fact
    also have "gauss_int_norm \<dots> = 2"
      by (simp add: gauss_int_norm_def)
    finally show ?thesis by simp
  next
    case (cong_3_mod_4 p)
    have "n = gauss_int_norm (normalize z)"
      by (simp add: n_def)
    also have "normalize z = of_nat p"
      by fact
    also have "gauss_int_norm \<dots> = p ^ 2"
      by simp
    finally show ?thesis using cong_3_mod_4 by simp
  next
    case cong_1_mod_4
    thus ?thesis by (simp add: n_def)
  qed
qed


subsubsection \<open>Multiplicities of primes\<close>

text \<open>
  In this section, we will show some results connecting the multiplicity of a Gaussian prime \<open>p\<close>
  in a Gaussian integer \<open>z\<close> to the \<open>\<int>\<close>-multiplicity of the norm of \<open>p\<close> in the norm of \<open>z\<close>.
\<close>

text \<open>
  The multiplicity of the Gaussian prime \<^term>\<open>1 + \<i>\<^sub>\<int>\<close> in an integer \<open>c\<close> is simply
  twice the \<open>\<int>\<close>-multiplicity of 2 in \<open>c\<close>:
\<close>
lemma multiplicity_prime_1_plus_i_aux: "multiplicity (1 + \<i>\<^sub>\<int>) (of_nat c) = 2 * multiplicity 2 c"
proof (cases "c = 0")
  case [simp]: False
  have "2 * multiplicity 2 c = multiplicity 2 (c ^ 2)"
    by (simp add: prime_elem_multiplicity_power_distrib)
  also have "multiplicity 2 (c ^ 2) = multiplicity (of_nat 2) (of_nat c ^ 2 :: gauss_int)"
    by (simp flip: multiplicity_gauss_int_of_nat)
  also have "of_nat 2 = (-\<i>\<^sub>\<int>) * (1 + \<i>\<^sub>\<int>) ^ 2"
    by (simp add: algebra_simps power2_eq_square)
  also have "multiplicity \<dots> (of_nat c ^ 2) = multiplicity ((1 + \<i>\<^sub>\<int>) ^ 2) (of_nat c ^ 2)"
    by (subst multiplicity_times_unit_left) auto
  also have "\<dots> = multiplicity (1 + \<i>\<^sub>\<int>) (of_nat c)"
    by (subst multiplicity_power_power) auto
  finally show ?thesis ..
qed auto

text \<open>
  Tha multiplicity of an inert Gaussian prime $q\in\mathbb{Z}$ in a Gaussian integer \<open>z\<close> is 
  precisely half the \<open>\<int>\<close>-multiplicity of \<open>q\<close> in the norm of \<open>z\<close>.
\<close>
lemma multiplicity_prime_cong_3_mod_4:
  assumes "prime (of_nat q :: gauss_int)"
  shows   "multiplicity q (gauss_int_norm z) = 2 * multiplicity (of_nat q) z"
proof (cases "z = 0")
  case [simp]: False
  have "multiplicity q (gauss_int_norm z) =
          multiplicity (of_nat q) (of_nat (gauss_int_norm z) :: gauss_int)"
    by (simp add: multiplicity_gauss_int_of_nat)
  also have "\<dots> = multiplicity (of_nat q) (z * gauss_cnj z)"
    by (simp add: self_mult_gauss_cnj)
  also have "\<dots> = multiplicity (of_nat q) z + multiplicity (gauss_cnj (of_nat q)) (gauss_cnj z)"
    using assms by (subst prime_elem_multiplicity_mult_distrib) auto
  also have "multiplicity (gauss_cnj (of_nat q)) (gauss_cnj z) = multiplicity (of_nat q) z"
    by (subst multiplicity_gauss_cnj) auto
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by simp
  finally show ?thesis .
qed auto

text \<open>
  For Gaussian primes \<open>p\<close> whose norm is congruent 1 modulo 4, the $\mathbb{Z}[i]$-multiplicity
  of \<open>p\<close> in an integer \<open>c\<close> is just the \<open>\<int>\<close>-multiplicity of their norm in \<open>c\<close>.
\<close>
lemma multiplicity_prime_cong_1_mod_4_aux:
  fixes p :: gauss_int
  assumes "prime_elem p" "ReZ p > 0" "ImZ p > 0" "ImZ p \<noteq> ReZ p"
  shows "multiplicity p (of_nat c) = multiplicity (gauss_int_norm p) c"
proof (cases "c = 0")
  case [simp]: False
  show ?thesis
  proof (intro antisym multiplicity_geI)
    define k where "k = multiplicity p (of_nat c)"
    have "p ^ k dvd of_nat c"
      by (simp add: multiplicity_dvd k_def)
    moreover have "gauss_cnj p ^ k dvd of_nat c"
      using multiplicity_dvd[of "gauss_cnj p" "of_nat c"]
            multiplicity_gauss_cnj[of p "of_nat c"] by (simp add: k_def)
    moreover have "\<not>p dvd gauss_cnj p"
      using assms by (subst self_dvd_gauss_cnj_iff) auto
    hence "\<not>p dvd gauss_cnj p ^ k"
      using assms prime_elem_dvd_power by blast
    ultimately have "p ^ k * gauss_cnj p ^ k dvd of_nat c"
      using assms by (intro prime_elem_power_mult_dvdI) auto
    also have "p ^ k * gauss_cnj p ^ k = of_nat (gauss_int_norm p ^ k)"
      by (simp flip: self_mult_gauss_cnj add: power_mult_distrib)
    finally show "gauss_int_norm p ^ k dvd c"
      by (subst (asm) of_nat_dvd_of_nat_gauss_int_iff)
  next
    define k where "k = multiplicity (gauss_int_norm p) c"
    have "p ^ k dvd (p * gauss_cnj p) ^ k"
      by (intro dvd_power_same) auto
    also have "\<dots> = of_nat (gauss_int_norm p ^ k)"
      by (simp add: self_mult_gauss_cnj)
    also have "\<dots> dvd of_nat c"
      unfolding of_nat_dvd_of_nat_gauss_int_iff by (auto simp: k_def multiplicity_dvd)
    finally show "p ^ k dvd of_nat c" .
  qed (use assms in \<open>auto simp: gauss_int_norm_eq_Suc_0_iff\<close>)
qed auto

text \<open>
  The multiplicity of a Gaussian prime with norm congruent 1 modulo 4 in some Gaussian integer \<open>z\<close>
  and the multiplicity of its conjugate in \<open>z\<close> sum to the the \<open>\<int>\<close>-multiplicity of their norm in
  the norm of \<open>z\<close>:
\<close>
lemma multiplicity_prime_cong_1_mod_4:
  fixes p :: gauss_int
  assumes "prime_elem p" "ReZ p > 0" "ImZ p > 0" "ImZ p \<noteq> ReZ p"
  shows "multiplicity (gauss_int_norm p) (gauss_int_norm z) =
           multiplicity p z + multiplicity (gauss_cnj p) z"
proof (cases "z = 0")
  case [simp]: False
  have "multiplicity (gauss_int_norm p) (gauss_int_norm z) = 
          multiplicity p (of_nat (gauss_int_norm z))"
    using assms by (subst multiplicity_prime_cong_1_mod_4_aux) auto
  also have "\<dots> = multiplicity p (z * gauss_cnj z)"
    by (simp add: self_mult_gauss_cnj)
  also have "\<dots> = multiplicity p z + multiplicity p (gauss_cnj z)"
    using assms by (subst prime_elem_multiplicity_mult_distrib) auto
  also have "multiplicity p (gauss_cnj z) = multiplicity (gauss_cnj p) z"
    by (subst multiplicity_gauss_cnj [symmetric]) auto
  finally show ?thesis .
qed auto

text \<open>
  The multiplicity of the Gaussian prime \<^term>\<open>1 + \<i>\<^sub>\<int>\<close> in a Gaussian integer \<open>z\<close> is precisely
  the \<open>\<int>\<close>-multiplicity of 2 in the norm of \<open>z\<close>:
\<close>
lemma multiplicity_prime_1_plus_i: "multiplicity (1 + \<i>\<^sub>\<int>) z = multiplicity 2 (gauss_int_norm z)"
proof (cases "z = 0")
  case [simp]: False
  note [simp] = prime_elem_one_plus_i_gauss_int
  have "2 * multiplicity 2 (gauss_int_norm z) = multiplicity (1 + \<i>\<^sub>\<int>) (of_nat (gauss_int_norm z))" 
    by (rule multiplicity_prime_1_plus_i_aux [symmetric])
  also have "\<dots> = multiplicity (1 + \<i>\<^sub>\<int>) (z * gauss_cnj z)"
    by (simp add: self_mult_gauss_cnj)
  also have "\<dots> = multiplicity (1 + \<i>\<^sub>\<int>) z + multiplicity (gauss_cnj (1 - \<i>\<^sub>\<int>)) (gauss_cnj z)"
    by (subst prime_elem_multiplicity_mult_distrib) auto
  also have "multiplicity (gauss_cnj (1 - \<i>\<^sub>\<int>)) (gauss_cnj z) = multiplicity (1 - \<i>\<^sub>\<int>) z"
    by (subst multiplicity_gauss_cnj) auto
  also have "1 - \<i>\<^sub>\<int> = (-\<i>\<^sub>\<int>) * (1 + \<i>\<^sub>\<int>)"
    by (simp add: algebra_simps)
  also have "multiplicity \<dots> z = multiplicity (1 + \<i>\<^sub>\<int>) z"
    by (subst multiplicity_times_unit_left) auto
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by simp
  finally show ?thesis by simp
qed auto


subsection \<open>Coprimality of an element and its conjugate\<close>

text \<open>
  Using the classification of the primes, we now show that if the real and imaginary parts of a
  Gaussian integer are coprime and its norm is odd, then it is coprime to its own conjugate.
\<close>
lemma coprime_self_gauss_cnj:
  assumes "coprime (ReZ z) (ImZ z)" and "odd (gauss_int_norm z)"
  shows   "coprime z (gauss_cnj z)"
proof (rule coprimeI)
  fix d assume "d dvd z" "d dvd gauss_cnj z"
  have *: False if "p \<in> prime_factors z" "p \<in> prime_factors (gauss_cnj z)" for p
  proof -
    from that have p: "prime p" "p dvd z" "p dvd gauss_cnj z"
      by auto

    define p' where "p' = gauss_cnj p"
    define d where "d = gauss_int_norm p"
    have of_nat_d_eq: "of_nat d = p * p'"
      by (simp add: p'_def self_mult_gauss_cnj d_def)
    have "prime_elem p" "prime_elem p'" "p dvd z" "p' dvd z" "p dvd gauss_cnj z" "p' dvd gauss_cnj z"
      using that by (auto simp: in_prime_factors_iff p'_def gauss_cnj_dvd_left_iff)

    have "prime p"
      using that by auto
    then obtain q where q: "prime q" "of_nat q dvd z"
    proof (cases rule: gauss_int_prime_classification)
      case one_plus_i
      hence "2 = gauss_int_norm p"
        by (auto simp: gauss_int_norm_def)
      also have "gauss_int_norm p dvd gauss_int_norm z"
        using p by (intro gauss_int_norm_dvd_mono) auto
      finally have "even (gauss_int_norm z)" .
      with \<open>odd (gauss_int_norm z)\<close> show ?thesis
        by contradiction
    next
      case (cong_3_mod_4 q)
      thus ?thesis using that[of q] p by simp
    next
      case cong_1_mod_4
      hence "\<not>p dvd p'"
        unfolding p'_def by (subst self_dvd_gauss_cnj_iff) auto
      hence "p * p' dvd z" using p
        by (intro prime_elem_mult_dvdI) (auto simp: p'_def gauss_cnj_dvd_left_iff)
      also have "p * p' = of_nat (gauss_int_norm p)"
        by (simp add: p'_def self_mult_gauss_cnj)
      finally show ?thesis using that[of "gauss_int_norm p"] cong_1_mod_4
        by simp
    qed

    have "of_nat q dvd gcd (2 * of_int (ReZ z)) (2 * \<i>\<^sub>\<int> * of_int (ImZ z))"
    proof (rule gcd_greatest)
      have "of_nat q dvd (z + gauss_cnj z)"
        using q by (auto simp: gauss_cnj_dvd_right_iff)
      also have "\<dots> = 2 * of_int (ReZ z)"
        by (simp add: self_plus_gauss_cnj)
      finally show "of_nat q dvd (2 * of_int (ReZ z) :: gauss_int)" .
    next
      have "of_nat q dvd (z - gauss_cnj z)"
        using q by (auto simp: gauss_cnj_dvd_right_iff)
      also have "\<dots> = 2 * \<i>\<^sub>\<int> * of_int (ImZ z)"
        by (simp add: self_minus_gauss_cnj)
      finally show "of_nat q dvd (2 * \<i>\<^sub>\<int> * of_int (ImZ z))" .
    qed
    also have "\<dots> = 2"
    proof -
      have "odd (ReZ z) \<or> odd (ImZ z)"
        using assms by (auto simp: gauss_int_norm_def even_nat_iff)
      thus ?thesis
      proof
        assume "odd (ReZ z)"
        hence "coprime (of_int (ReZ z)) (of_int 2 :: gauss_int)"
          unfolding coprime_of_int_gauss_int coprime_right_2_iff_odd .
        thus ?thesis
          using assms
          by (subst gcd_mult_left_right_cancel)
             (auto simp: coprime_of_int_gauss_int coprime_commute is_unit_left_imp_coprime
                         is_unit_right_imp_coprime gcd_proj1_if_dvd gcd_proj2_if_dvd)
      next
        assume "odd (ImZ z)"
        hence "coprime (of_int (ImZ z)) (of_int 2 :: gauss_int)"
          unfolding coprime_of_int_gauss_int coprime_right_2_iff_odd .
        hence "gcd (2 * of_int (ReZ z)) (2 * \<i>\<^sub>\<int> * of_int (ImZ z)) = gcd (2 * of_int (ReZ z)) (2 * \<i>\<^sub>\<int>)"
          using assms
          by (subst gcd_mult_right_right_cancel)
             (auto simp: coprime_of_int_gauss_int coprime_commute is_unit_left_imp_coprime
                         is_unit_right_imp_coprime)
        also have "\<dots> = normalize (2 * gcd (of_int (ReZ z)) \<i>\<^sub>\<int>)"
          by (subst gcd_mult_left) auto
        also have "gcd (of_int (ReZ z)) \<i>\<^sub>\<int> = 1"
          by (subst coprime_iff_gcd_eq_1 [symmetric], rule is_unit_right_imp_coprime) auto
        finally show ?thesis by simp
      qed
    qed
    finally have "of_nat q dvd (of_nat 2 :: gauss_int)"
      by simp
    hence "q dvd 2"
      by (simp only: of_nat_dvd_of_nat_gauss_int_iff)
    with \<open>prime q\<close> have "q = 2"
      using primes_dvd_imp_eq two_is_prime_nat by blast
    with q have "2 dvd z"
      by auto

    have "2 dvd gauss_int_norm 2"
      by simp
    also have "\<dots> dvd gauss_int_norm z"
      using \<open>2 dvd z\<close> by (intro gauss_int_norm_dvd_mono)
    finally show False using \<open>odd (gauss_int_norm z)\<close> by contradiction
  qed

  fix d :: gauss_int
  assume d: "d dvd z" "d dvd gauss_cnj z"
  show "is_unit d"
  proof (rule ccontr)
    assume "\<not>is_unit d"
    moreover from d assms have "d \<noteq> 0"
      by auto
    ultimately obtain p where p: "prime p" "p dvd d"
      using prime_divisorE by blast
    with d have "p \<in> prime_factors z" "p \<in> prime_factors (gauss_cnj z)"
      using assms by (auto simp: in_prime_factors_iff)
    with *[of p] show False by blast
  qed
qed


subsection \<open>Square decompositions of prime numbers congruent 1 mod 4\<close>

lemma prime_1_mod_4_sum_of_squares_unique_aux:
  fixes p x y :: nat
  assumes "prime p" "[p = 1] (mod 4)" "x ^ 2 + y ^ 2 = p"
  shows   "x > 0 \<and> y > 0 \<and> x \<noteq> y"
proof safe
  from assms show "x > 0" "y > 0"
    by (auto intro!: Nat.gr0I simp: prime_power_iff)
next
  assume "x = y"
  with assms have "p = 2 * x ^ 2"
    by simp
  with \<open>prime p\<close> have "p = 2"
    by (auto dest: prime_product)
  with \<open>[p = 1] (mod 4)\<close> show False
    by (simp add: cong_def)
qed

text \<open>
  Any prime number congruent 1 modulo 4 can be written \<^emph>\<open>uniquely\<close> as a sum of two squares
  $x^2 + y^2$ (up to commutativity of the addition). Additionally, we have shown above that
  \<open>x\<close> and \<open>y\<close> are both positive and \<open>x \<noteq> y\<close>.
\<close>
lemma prime_1_mod_4_sum_of_squares_unique:
  fixes p :: nat
  assumes "prime p" "[p = 1] (mod 4)"
  shows   "\<exists>!(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p"
proof (rule ex_ex1I)
  obtain z where z: "gauss_int_norm z = p"
    using prime_cong_1_mod_4_gauss_int_norm_exists[OF assms] by blast
  show "\<exists>z. case z of (x,y) \<Rightarrow> x \<le> y \<and> x ^ 2 + y ^ 2 = p"
  proof (cases "\<bar>ReZ z\<bar> \<le> \<bar>ImZ z\<bar>")
    case True
    with z show ?thesis by
      (intro exI[of _ "(nat \<bar>ReZ z\<bar>, nat \<bar>ImZ z\<bar>)"])
      (auto simp: gauss_int_norm_def nat_add_distrib simp flip: nat_power_eq)
  next
    case False
    with z show ?thesis by
      (intro exI[of _ "(nat \<bar>ImZ z\<bar>, nat \<bar>ReZ z\<bar>)"])
      (auto simp: gauss_int_norm_def nat_add_distrib simp flip: nat_power_eq)
  qed
next
  fix z1 z2
  assume z1: "case z1 of (x, y) \<Rightarrow> x \<le> y \<and> x\<^sup>2 + y\<^sup>2 = p"
  assume z2: "case z2 of (x, y) \<Rightarrow> x \<le> y \<and> x\<^sup>2 + y\<^sup>2 = p"
  define z1' :: gauss_int where "z1' = of_nat (fst z1) + \<i>\<^sub>\<int> * of_nat (snd z1)"
  define z2' :: gauss_int where "z2' = of_nat (fst z2) + \<i>\<^sub>\<int> * of_nat (snd z2)"
  from assms interpret noninert_gauss_int_prime p
    by unfold_locales auto
  have norm_z1': "gauss_int_norm z1' = p"
    using z1 by (simp add: z1'_def gauss_int_norm_def case_prod_unfold nat_add_distrib nat_power_eq)
  have norm_z2': "gauss_int_norm z2' = p"
    using z2 by (simp add: z2'_def gauss_int_norm_def case_prod_unfold nat_add_distrib nat_power_eq)

  have sgns: "fst z1 > 0" "snd z1 > 0" "fst z2 > 0" "snd z2 > 0" "fst z1 \<noteq> snd z1" "fst z2 \<noteq> snd z2"
    using prime_1_mod_4_sum_of_squares_unique_aux[OF assms, of "fst z1" "snd z1"] z1
          prime_1_mod_4_sum_of_squares_unique_aux[OF assms, of "fst z2" "snd z2"] z2 by auto
  have [simp]: "normalize z1' = z1'" "normalize z2' = z2'"
    using sgns by (subst normalized_gauss_int_iff; simp add: z1'_def z2'_def)+
  have "prime z1'" "prime z2'"
    using norm_z1' norm_z2' assms unfolding prime_def
    by (auto simp: prime_gauss_int_norm_imp_prime_elem)

  have "of_nat p = z1' * gauss_cnj z1'"
    by (simp add: self_mult_gauss_cnj norm_z1')
  hence "z1' dvd of_nat p"
    by simp
  also have "of_nat p = z2' * gauss_cnj z2'"
    by (simp add: self_mult_gauss_cnj norm_z2')
  finally have "z1' dvd z2' \<or> z1' dvd gauss_cnj z2'" using assms
    by (subst (asm) prime_elem_dvd_mult_iff)
       (simp add: norm_z1' prime_gauss_int_norm_imp_prime_elem)
  thus "z1 = z2"
  proof
    assume "z1' dvd z2'"
    with \<open>prime z1'\<close> \<open>prime z2'\<close> have "z1' = z2'"
      by (simp add: primes_dvd_imp_eq)
    thus ?thesis
      by (simp add: z1'_def z2'_def gauss_int_eq_iff prod_eq_iff)
  next
    assume dvd: "z1' dvd gauss_cnj z2'"
    have "normalize (\<i>\<^sub>\<int> * gauss_cnj z2') = \<i>\<^sub>\<int> * gauss_cnj z2'"
      using sgns by (subst normalized_gauss_int_iff) (auto simp: z2'_def)
    moreover have "prime_elem (\<i>\<^sub>\<int> * gauss_cnj z2')"
      by (rule prime_gauss_int_norm_imp_prime_elem)
         (simp add: gauss_int_norm_mult norm_z2' \<open>prime p\<close>)
    ultimately have "prime (\<i>\<^sub>\<int> * gauss_cnj z2')"
      by (simp add: prime_def)
    moreover from dvd have "z1' dvd \<i>\<^sub>\<int> * gauss_cnj z2'"
      by simp
    ultimately have "z1' = \<i>\<^sub>\<int> * gauss_cnj z2'"
      using \<open>prime z1'\<close> by (simp add: primes_dvd_imp_eq)
    hence False using z1 z2 sgns
      by (auto simp: gauss_int_eq_iff z1'_def z2'_def)
    thus ?thesis ..
  qed
qed

lemma two_sum_of_squares_nat_iff: "(x :: nat) ^ 2 + y ^ 2 = 2 \<longleftrightarrow> x = 1 \<and> y = 1"
proof
  assume eq: "x ^ 2 + y ^ 2 = 2"
  have square_neq_2: "n ^ 2 \<noteq> 2" for n :: nat
  proof
    assume *: "n ^ 2 = 2"
    have "prime (2 :: nat)"
      by simp
    thus False by (subst (asm) * [symmetric]) (auto simp: prime_power_iff)
  qed

  from eq have "x ^ 2 < 2 ^ 2" "y ^ 2 < 2 ^ 2"
    by simp_all
  hence "x < 2" "y < 2"
    using power2_less_imp_less[of x 2] power2_less_imp_less[of y 2] by auto
  moreover have "x > 0" "y > 0"
    using eq square_neq_2[of x] square_neq_2[of y] by (auto intro!: Nat.gr0I)
  ultimately show "x = 1 \<and> y = 1"
    by auto
qed auto

lemma prime_sum_of_squares_unique:
  fixes p :: nat
  assumes "prime p" "p = 2 \<or> [p = 1] (mod 4)"
  shows   "\<exists>!(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p"
  using assms(2)
proof
  assume [simp]: "p = 2"
  have **: "(\<lambda>(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p) = (\<lambda>z. z = (1,1 :: nat))"
    using two_sum_of_squares_nat_iff by (auto simp: fun_eq_iff)
  thus ?thesis
    by (subst **) auto
qed (use prime_1_mod_4_sum_of_squares_unique[of p] assms in auto)

text \<open>
  We now give a simple and inefficient algorithm to compute the canonical decomposition
  $x ^ 2 + y ^ 2$ with $x\leq y$.
\<close>
definition prime_square_sum_nat_decomp :: "nat \<Rightarrow> nat \<times> nat" where
  "prime_square_sum_nat_decomp p =
     (if prime p \<and> (p = 2 \<or> [p = 1] (mod 4))
      then THE (x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p else (0, 0))"

lemma prime_square_sum_nat_decomp_eqI:
  assumes "prime p" "x ^ 2 + y ^ 2 = p" "x \<le> y"
  shows   "prime_square_sum_nat_decomp p = (x, y)"
proof -
  have "[gauss_int_norm (of_nat x + \<i>\<^sub>\<int> * of_nat y) \<noteq> 3] (mod 4)"
    by (rule gauss_int_norm_not_3_mod_4)
  also have "gauss_int_norm (of_nat x + \<i>\<^sub>\<int> * of_nat y) = p"
    using assms by (auto simp: gauss_int_norm_def nat_add_distrib nat_power_eq)
  finally have "[p \<noteq> 3] (mod 4)" .
  with prime_mod_4_cases[of p] assms have *: "p = 2 \<or> [p = 1] (mod 4)"
    by auto

  have "prime_square_sum_nat_decomp p = (THE (x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p)"
    using * \<open>prime p\<close> by (simp add: prime_square_sum_nat_decomp_def)
  also have "\<dots> = (x, y)"
  proof (rule the1_equality)
    show "\<exists>!(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p"
      using \<open>prime p\<close> * by (rule prime_sum_of_squares_unique)
  qed (use assms in auto)
  finally show ?thesis .
qed

lemma prime_square_sum_nat_decomp_correct:
  assumes "prime p" "p = 2 \<or> [p = 1] (mod 4)"
  defines "z \<equiv> prime_square_sum_nat_decomp p"
  shows "fst z ^ 2 + snd z ^ 2 = p" "fst z \<le> snd z"
proof -
  define z' where "z' = (THE (x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p)"
  have "z = z'"
    unfolding z_def z'_def using assms by (simp add: prime_square_sum_nat_decomp_def)
  also have"\<exists>!(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p"
    using assms by (intro prime_sum_of_squares_unique)
  hence "case z' of (x, y) \<Rightarrow> x \<le> y \<and> x ^ 2 + y ^ 2 = p"
    unfolding z'_def by (rule theI')
  finally show "fst z ^ 2 + snd z ^ 2 = p" "fst z \<le> snd z"
    by auto
qed

lemma sum_of_squares_nat_bound:
  fixes x y n :: nat
  assumes "x ^ 2 + y ^ 2 = n"
  shows   "x \<le> n"
proof (cases "x = 0")
  case False
  hence "x * 1 \<le> x ^ 2"
    unfolding power2_eq_square by (intro mult_mono) auto
  also have "\<dots> \<le> x ^ 2 + y ^ 2"
    by simp
  also have "\<dots> = n"
    by fact
  finally show ?thesis by simp
qed auto

lemma sum_of_squares_nat_bound':
  fixes x y n :: nat
  assumes "x ^ 2 + y ^ 2 = n"
  shows   "y \<le> n"
  using sum_of_squares_nat_bound[of y x] assms by (simp add: add.commute)

lemma is_singleton_conv_Ex1:
  "is_singleton A \<longleftrightarrow> (\<exists>!x. x \<in> A)"
proof
  assume "is_singleton A"
  thus "\<exists>!x. x \<in> A"
    by (auto elim!: is_singletonE)
next
  assume "\<exists>!x. x \<in> A"
  thus "is_singleton A"
    by (metis equals0D is_singletonI')
qed

lemma the_elemI:
  assumes "is_singleton A"
  shows   "the_elem A \<in> A"
  using assms by (elim is_singletonE) auto

lemma prime_square_sum_nat_decomp_code_aux:
  assumes "prime p" "p = 2 \<or> [p = 1] (mod 4)"
  defines "z \<equiv> the_elem (Set.filter (\<lambda>(x,y). x ^ 2 + y ^ 2 = p) (SIGMA x:{0..p}. {x..p}))"
  shows "prime_square_sum_nat_decomp p = z"
proof -
  let ?A = "Set.filter (\<lambda>(x,y). x ^ 2 + y ^ 2 = p) (SIGMA x:{0..p}. {x..p})"
  have eq: "?A = {(x,y). x \<le> y \<and> x ^ 2 + y ^ 2 = p}"
    using sum_of_squares_nat_bound sum_of_squares_nat_bound' by auto
  have z: "z \<in> Set.filter (\<lambda>(x,y). x ^ 2 + y ^ 2 = p) (SIGMA x:{0..p}. {x..p})"
    unfolding z_def eq using prime_sum_of_squares_unique[OF assms(1,2)]
    by (intro the_elemI) (simp add: is_singleton_conv_Ex1)
  have "prime_square_sum_nat_decomp p = (fst z, snd z)"
    using z by (intro prime_square_sum_nat_decomp_eqI[OF assms(1)]) auto
  also have "\<dots> = z"
    by simp
  finally show ?thesis .
qed

lemma prime_square_sum_nat_decomp_code [code]:
  "prime_square_sum_nat_decomp p =
     (if prime p \<and> (p = 2 \<or> [p = 1] (mod 4))
      then the_elem (Set.filter (\<lambda>(x,y). x ^ 2 + y ^ 2 = p) (SIGMA x:{0..p}. {x..p}))
      else (0, 0))"
  using prime_square_sum_nat_decomp_code_aux[of p]
  by (auto simp: prime_square_sum_nat_decomp_def)


subsection \<open>Executable factorisation of Gaussian integers\<close>

text \<open>
  Lastly, we use all of the above to give an executable (albeit not very efficient) factorisation
  algorithm for Gaussian integers based on factorisation of regular integers. Note that we will
  only compute the set of prime factors without multiplicity, but given that, it would be fairly
  easy to determine the multiplicity as well.

  First, we need the following function that computes the Gaussian integer factors of a 
  \<open>\<int>\<close>-prime \<open>p\<close>:
\<close>
definition factor_gauss_int_prime_nat :: "nat \<Rightarrow> gauss_int list" where
  "factor_gauss_int_prime_nat p =
     (if p = 2 then [1 + \<i>\<^sub>\<int>]
      else if [p = 3] (mod 4) then [of_nat p]
      else case prime_square_sum_nat_decomp p of
             (x, y) \<Rightarrow> [of_nat x + \<i>\<^sub>\<int> * of_nat y, of_nat y + \<i>\<^sub>\<int> * of_nat x])"

lemma factor_gauss_int_prime_nat_correct:
  assumes "prime p"
  shows   "set (factor_gauss_int_prime_nat p) = prime_factors (of_nat p)"
  using prime_mod_4_cases[OF assms]
proof (elim disjE)
  assume "p = 2"
  thus ?thesis
    by (auto simp: prime_factorization_2_gauss_int factor_gauss_int_prime_nat_def)
next
  assume *: "[p = 3] (mod 4)"
  with assms have "prime (of_nat p :: gauss_int)"
    by (intro prime_gauss_int_of_nat)
  thus ?thesis using assms *
    by (auto simp: prime_factorization_prime factor_gauss_int_prime_nat_def cong_def)
next
  assume *: "[p = 1] (mod 4)"
  then interpret noninert_gauss_int_prime p
    using \<open>prime p\<close> by unfold_locales
  define z where "z = prime_square_sum_nat_decomp p"
  define x y where "x = fst z" and "y = snd z"
  have xy: "x ^ 2 + y ^ 2 = p" "x \<le> y"
    using prime_square_sum_nat_decomp_correct[of p] * assms
    by (auto simp: x_def y_def z_def)
  from xy have xy_signs: "x > 0" "y > 0"
    using prime_1_mod_4_sum_of_squares_unique_aux[of p x y] assms * by auto
  have norms: "gauss_int_norm (of_nat x + \<i>\<^sub>\<int> * of_nat y) = p"
              "gauss_int_norm (of_nat y + \<i>\<^sub>\<int> * of_nat x) = p"
    using xy by (auto simp: gauss_int_norm_def nat_add_distrib nat_power_eq)
  have prime: "prime (of_nat x + \<i>\<^sub>\<int> * of_nat y)" "prime (of_nat y + \<i>\<^sub>\<int> * of_nat x)"
    using norms xy_signs \<open>prime p\<close> unfolding prime_def normalized_gauss_int_iff
    by (auto intro!: prime_gauss_int_norm_imp_prime_elem)

  have "normalize ((of_nat x + \<i>\<^sub>\<int> * of_nat y) * (of_nat y + \<i>\<^sub>\<int> * of_nat x)) = of_nat p"
  proof -
    have "(of_nat x + \<i>\<^sub>\<int> * of_nat y) * (of_nat y + \<i>\<^sub>\<int> * of_nat x) = (\<i>\<^sub>\<int> * of_nat p :: gauss_int)"
      by (subst xy(1) [symmetric]) (auto simp: gauss_int_eq_iff power2_eq_square)
    also have "normalize \<dots> = of_nat p"
      by simp
    finally show ?thesis .
  qed
  hence "prime_factorization (of_nat p) =
         prime_factorization (prod_mset {#of_nat x + \<i>\<^sub>\<int> * of_nat y, of_nat y + \<i>\<^sub>\<int> * of_nat x#})"
    using assms xy by (subst prime_factorization_unique) (auto simp: gauss_int_eq_iff)
  also have "\<dots> = {#of_nat x + \<i>\<^sub>\<int> * of_nat y, of_nat y + \<i>\<^sub>\<int> * of_nat x#}"
    using prime by (subst prime_factorization_prod_mset_primes) auto
  finally have "prime_factors (of_nat p) = {of_nat x + \<i>\<^sub>\<int> * of_nat y, of_nat y + \<i>\<^sub>\<int> * of_nat x}"
    by simp
  also have "\<dots> = set (factor_gauss_int_prime_nat p)"
    using * unfolding factor_gauss_int_prime_nat_def case_prod_unfold
    by (auto simp: cong_def x_def y_def z_def)
  finally show ?thesis ..
qed

text \<open>
  Next, we lift this to compute the prime factorisation of any integer in the Gaussian integers:
\<close>
definition prime_factors_gauss_int_of_nat :: "nat \<Rightarrow> gauss_int set" where
  "prime_factors_gauss_int_of_nat n = (if n = 0 then {} else 
     (\<Union>p\<in>prime_factors n. set (factor_gauss_int_prime_nat p)))"

lemma prime_factors_gauss_int_of_nat_correct:
  "prime_factors_gauss_int_of_nat n = prime_factors (of_nat n)"
proof (cases "n = 0")
  case False
  from False have [simp]: "n > 0" by auto
  have "prime_factors (of_nat n :: gauss_int) =
          prime_factors (of_nat (prod_mset (prime_factorization n)))"
    by (subst prod_mset_prime_factorization_nat [symmetric]) auto
  also have "\<dots> = prime_factors (prod_mset (image_mset of_nat (prime_factorization n)))"
    by (subst of_nat_prod_mset) auto
  also have "\<dots> = (\<Union>p\<in>prime_factors n. prime_factors (of_nat p))"
    by (subst prime_factorization_prod_mset) auto
  also have "\<dots> = (\<Union>p\<in>prime_factors n. set (factor_gauss_int_prime_nat p))"
    by (intro SUP_cong refl factor_gauss_int_prime_nat_correct [symmetric]) auto
  finally show ?thesis by (simp add: prime_factors_gauss_int_of_nat_def)
qed (auto simp:  prime_factors_gauss_int_of_nat_def)

text \<open>
  We can now use this to factor any Gaussian integer by computing a factorisation of its
  norm and removing all the prime divisors that do not actually divide it.
\<close>
definition prime_factors_gauss_int :: "gauss_int \<Rightarrow> gauss_int set" where
  "prime_factors_gauss_int z = (if z = 0 then {} 
     else Set.filter (\<lambda>p. p dvd z) (prime_factors_gauss_int_of_nat (gauss_int_norm z)))"

lemma prime_factors_gauss_int_correct [code_unfold]: "prime_factors z = prime_factors_gauss_int z"
proof (cases "z = 0")
  case [simp]: False
  define n where "n = gauss_int_norm z"
  from False have [simp]: "n > 0" by (auto simp: n_def)

  have "prime_factors_gauss_int z = Set.filter (\<lambda>p. p dvd z) (prime_factors (of_nat n))"
    by (simp add: prime_factors_gauss_int_of_nat_correct prime_factors_gauss_int_def n_def)
  also have "of_nat n = z * gauss_cnj z"
    by (simp add: n_def self_mult_gauss_cnj)
  also have "prime_factors \<dots> = prime_factors z \<union> prime_factors (gauss_cnj z)"
    by (subst prime_factors_product) auto
  also have "Set.filter (\<lambda>p. p dvd z) \<dots> = prime_factors z"
    by (auto simp: in_prime_factors_iff)
  finally show ?thesis by simp
qed (auto simp: prime_factors_gauss_int_def)

(*<*)
unbundle no_gauss_int_notation
(*>*)

end