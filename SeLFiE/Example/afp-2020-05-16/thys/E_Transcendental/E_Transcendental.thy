(*
  File:       E_Transcendental.thy
  Author:     Manuel Eberl <eberlm@in.tum.de>

  A proof that e (Euler's number) is transcendental.
  Could possibly be extended to a transcendence proof for pi or
  the very general Lindemann-Weierstrass theorem.
*)
section \<open>Proof of the Transcendence of $e$\<close>
theory E_Transcendental
  imports
    "HOL-Complex_Analysis.Complex_Analysis"
    "HOL-Number_Theory.Number_Theory"
    "HOL-Computational_Algebra.Polynomial"
begin

(* TODO: Lots of stuff to move to the distribution *)
  
subsection \<open>Various auxiliary facts\<close>

lemma fact_dvd_pochhammer:
  assumes "m \<le> n + 1"
  shows   "fact m dvd pochhammer (int n - int m + 1) m"
proof -
  have "(real n gchoose m) * fact m = of_int (pochhammer (int n - int m + 1) m)"
    by (simp add: gbinomial_pochhammer' pochhammer_of_int [symmetric])
  also have "(real n gchoose m) * fact m = of_int (int (n choose m) * fact m)"
    by (simp add: binomial_gbinomial)
  finally have "int (n choose m) * fact m = pochhammer (int n - int m + 1) m"
    by (subst (asm) of_int_eq_iff)
  from this [symmetric] show ?thesis by simp
qed

lemma of_nat_eq_1_iff [simp]: "of_nat x = (1 :: 'a :: semiring_char_0) \<longleftrightarrow> x = 1"
  by (fact of_nat_eq_1_iff)

lemma prime_elem_int_not_dvd_neg1_power:
  "prime_elem (p :: int) \<Longrightarrow> \<not>p dvd (-1) ^ n"
  by (rule notI, frule (1) prime_elem_dvd_power, cases "p \<ge> 0") (auto simp: prime_elem_def)

lemma nat_fact [simp]: "nat (fact n) = fact n"
  by (subst of_nat_fact [symmetric]) (rule nat_int)

lemma prime_dvd_fact_iff_int:
  "p dvd fact n \<longleftrightarrow> p \<le> int n" if "prime p"
  using that prime_dvd_fact_iff [of "nat \<bar>p\<bar>" n]
  by auto (simp add: prime_ge_0_int)

lemma filterlim_minus_nat_at_top:
  "filterlim (\<lambda>n. n - k :: nat) at_top at_top"
proof -
  have "sequentially = filtermap (\<lambda>n. n + k) at_top"
    by (auto simp: filter_eq_iff eventually_filtermap)
  also have "filterlim (\<lambda>n. n - k :: nat) at_top \<dots>"
    by (simp add: filterlim_filtermap filterlim_ident)
  finally show ?thesis .
qed

lemma power_over_fact_tendsto_0:
  "(\<lambda>n. (x :: real) ^ n / fact n) \<longlonglongrightarrow> 0"
  using summable_exp[of x] by (intro summable_LIMSEQ_zero) (simp add: sums_iff field_simps)

lemma power_over_fact_tendsto_0':
  "(\<lambda>n. c * (x :: real) ^ n / fact n) \<longlonglongrightarrow> 0"
  using tendsto_mult[OF tendsto_const[of c] power_over_fact_tendsto_0[of x]] by simp


subsection \<open>Lifting integer polynomials\<close>

lift_definition of_int_poly :: "int poly \<Rightarrow> 'a :: comm_ring_1 poly" is "\<lambda>g x. of_int (g x)"
  by (auto elim: eventually_mono)

lemma coeff_of_int_poly [simp]: "coeff (of_int_poly p) n = of_int (coeff p n)"
  by transfer' simp

lemma of_int_poly_0 [simp]: "of_int_poly 0 = 0"
  by transfer (simp add: fun_eq_iff)

lemma of_int_poly_pCons [simp]: "of_int_poly (pCons c p) = pCons (of_int c) (of_int_poly p)"
  by transfer' (simp add: fun_eq_iff split: nat.splits)

lemma of_int_poly_smult [simp]: "of_int_poly (smult c p) = smult (of_int c) (of_int_poly p)"
  by transfer simp

lemma of_int_poly_1 [simp]: "of_int_poly 1 = 1"
  by (simp add: one_pCons)

lemma of_int_poly_add [simp]: "of_int_poly (p + q) = of_int_poly p + of_int_poly q"
  by transfer' (simp add: fun_eq_iff)

lemma of_int_poly_mult [simp]: "of_int_poly (p * q) = (of_int_poly p * of_int_poly q)"
  by (induction p) simp_all

lemma of_int_poly_sum [simp]: "of_int_poly (sum f A) = sum (\<lambda>x. of_int_poly (f x)) A"
  by (induction A rule: infinite_finite_induct) simp_all

lemma of_int_poly_prod [simp]: "of_int_poly (prod f A) = prod (\<lambda>x. of_int_poly (f x)) A"
  by (induction A rule: infinite_finite_induct) simp_all

lemma of_int_poly_power [simp]: "of_int_poly (p ^ n) = of_int_poly p ^ n"
  by (induction n) simp_all

lemma of_int_poly_monom [simp]: "of_int_poly (monom c n) = monom (of_int c) n"
  by transfer (simp add: fun_eq_iff)

lemma poly_of_int_poly [simp]: "poly (of_int_poly p) (of_int x) = of_int (poly p x)"
  by (induction p) simp_all

lemma poly_of_int_poly_of_nat [simp]: "poly (of_int_poly p) (of_nat x) = of_int (poly p (int x))"
  by (induction p) simp_all

lemma poly_of_int_poly_0 [simp]: "poly (of_int_poly p) 0 = of_int (poly p 0)"
  by (induction p) simp_all

lemma poly_of_int_poly_1 [simp]: "poly (of_int_poly p) 1 = of_int (poly p 1)"
  by (induction p) simp_all

lemma poly_of_int_poly_of_real [simp]:
    "poly (of_int_poly p) (of_real x) = of_real (poly (of_int_poly p) x)"
  by (induction p) simp_all

lemma of_int_poly_eq_iff [simp]:
  "of_int_poly p = (of_int_poly q :: 'a :: {comm_ring_1, ring_char_0} poly) \<longleftrightarrow> p = q"
  by (simp add: poly_eq_iff)

lemma of_int_poly_eq_0_iff [simp]:
  "of_int_poly p = (0 :: 'a :: {comm_ring_1, ring_char_0} poly) \<longleftrightarrow> p = 0"
  using of_int_poly_eq_iff[of p 0] by (simp del: of_int_poly_eq_iff)

lemma degree_of_int_poly [simp]:
  "degree (of_int_poly p :: 'a :: {comm_ring_1, ring_char_0} poly) = degree p"
  by (simp add: degree_def)

lemma pderiv_of_int_poly [simp]: "pderiv (of_int_poly p) = of_int_poly (pderiv p)"
  by (induction p) (simp_all add: pderiv_pCons)

lemma higher_pderiv_of_int_poly [simp]:
  "(pderiv ^^ n) (of_int_poly p) = of_int_poly ((pderiv ^^ n) p)"
  by (induction n) simp_all

lemma int_polyE:
  assumes "\<And>n. coeff (p :: 'a :: {comm_ring_1, ring_char_0} poly) n \<in> \<int>"
  obtains p' where "p = of_int_poly p'"
proof -
  from assms have "\<forall>n. \<exists>c. coeff p n = of_int c" by (auto simp: Ints_def)
  hence "\<exists>c. \<forall>n. of_int (c n) = coeff p n" by (simp add: choice_iff eq_commute)
  then obtain c where c: "of_int (c n) = coeff p n" for n by blast
  have [simp]: "coeff (Abs_poly c) = c"
  proof (rule poly.Abs_poly_inverse, clarify)
    have "eventually (\<lambda>n. n > degree p) at_top" by (rule eventually_gt_at_top)
    hence "eventually (\<lambda>n. coeff p n = 0) at_top"
      by eventually_elim (simp add: coeff_eq_0)
    thus "eventually (\<lambda>n. c n = 0) cofinite"
      by (simp add: c [symmetric] cofinite_eq_sequentially)
  qed
  have "p = of_int_poly (Abs_poly c)"
    by (rule poly_eqI) (simp add: c)
  thus ?thesis by (rule that)
qed


subsection \<open>General facts about polynomials\<close>

lemma pderiv_power:
  "pderiv (p ^ n) = smult (of_nat n) (p ^ (n - 1) * pderiv p)"
  by (cases n) (simp_all add: pderiv_power_Suc del: power_Suc)

lemma degree_prod_sum_eq:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow>
     degree (prod f A :: 'a :: idom poly) = (\<Sum>x\<in>A. degree (f x))"
  by (induction A rule: infinite_finite_induct) (auto simp: degree_mult_eq)

lemma pderiv_monom:
  "pderiv (monom c n) = monom (of_nat n * c) (n - 1)"
  by (cases n)
     (simp_all add: monom_altdef pderiv_power_Suc pderiv_smult pderiv_pCons mult_ac del: power_Suc)

lemma power_poly_const [simp]: "[:c:] ^ n = [:c ^ n:]"
  by (induction n) (simp_all add: power_commutes)

lemma monom_power: "monom c n ^ k = monom (c ^ k) (n * k)"
  by (induction k) (simp_all add: mult_monom)

lemma coeff_higher_pderiv:
  "coeff ((pderiv ^^ m) f) n = pochhammer (of_nat (Suc n)) m * coeff f (n + m)"
  by (induction m arbitrary: n) (simp_all add: coeff_pderiv pochhammer_rec algebra_simps)

lemma higher_pderiv_add: "(pderiv ^^ n) (p + q) = (pderiv ^^ n) p + (pderiv ^^ n) q"
  by (induction n arbitrary: p q) (simp_all del: funpow.simps add: funpow_Suc_right pderiv_add)

lemma higher_pderiv_smult: "(pderiv ^^ n) (smult c p) = smult c ((pderiv ^^ n) p)"
  by (induction n arbitrary: p) (simp_all del: funpow.simps add: funpow_Suc_right pderiv_smult)

lemma higher_pderiv_0 [simp]: "(pderiv ^^ n) 0 = 0"
  by (induction n) simp_all

lemma higher_pderiv_monom:
  "m \<le> n + 1 \<Longrightarrow> (pderiv ^^ m) (monom c n) = monom (pochhammer (int n - int m + 1) m * c) (n - m)"
proof (induction m arbitrary: c n)
  case (Suc m)
  thus ?case
    by (cases n)
       (simp_all del: funpow.simps add: funpow_Suc_right pderiv_monom pochhammer_rec' Suc.IH)
qed simp_all

lemma higher_pderiv_monom_eq_zero:
  "m > n + 1 \<Longrightarrow> (pderiv ^^ m) (monom c n) = 0"
proof (induction m arbitrary: c n)
  case (Suc m)
  thus ?case
    by (cases n)
       (simp_all del: funpow.simps add: funpow_Suc_right pderiv_monom pochhammer_rec' Suc.IH)
qed simp_all

lemma higher_pderiv_sum: "(pderiv ^^ n) (sum f A) = (\<Sum>x\<in>A. (pderiv ^^ n) (f x))"
  by (induction A rule: infinite_finite_induct) (simp_all add: higher_pderiv_add)

lemma fact_dvd_higher_pderiv:
  "[:fact n :: int:] dvd (pderiv ^^ n) p"
proof -
  have "[:fact n:] dvd (pderiv ^^ n) (monom c k)" for c :: int and k :: nat
    by (cases "n \<le> k + 1")
       (simp_all add: higher_pderiv_monom higher_pderiv_monom_eq_zero
          fact_dvd_pochhammer const_poly_dvd_iff)
  hence "[:fact n:] dvd (pderiv ^^ n) (\<Sum>k\<le>degree p. monom (coeff p k) k)"
    by (simp_all add: higher_pderiv_sum dvd_sum)
  thus ?thesis by (simp add: poly_as_sum_of_monoms)
qed

lemma fact_dvd_poly_higher_pderiv_aux:
  "(fact n :: int) dvd poly ((pderiv ^^ n) p) x"
proof -
  have "[:fact n:] dvd (pderiv ^^ n) p" by (rule fact_dvd_higher_pderiv)
  then obtain q where "(pderiv ^^ n) p = [:fact n:] * q" by (erule dvdE)
  thus ?thesis by simp
qed

lemma fact_dvd_poly_higher_pderiv_aux':
  "m \<le> n \<Longrightarrow> (fact m :: int) dvd poly ((pderiv ^^ n) p) x"
  by (rule dvd_trans[OF fact_dvd fact_dvd_poly_higher_pderiv_aux]) simp_all

lemma algebraicE':
  assumes "algebraic (x :: 'a :: field_char_0)"
  obtains p where "p \<noteq> 0" "poly (of_int_poly p) x = 0"
proof -
  from assms obtain q where "\<And>i. coeff q i \<in> \<int>" "q \<noteq> 0" "poly q x = 0"
    by (erule algebraicE)
  moreover from this(1) obtain q' where "q = of_int_poly q'" by (erule int_polyE)
  ultimately show ?thesis by (intro that[of q']) simp_all
qed

lemma algebraicE'_nonzero:
  assumes "algebraic (x :: 'a :: field_char_0)" "x \<noteq> 0"
  obtains p where "p \<noteq> 0" "coeff p 0 \<noteq> 0" "poly (of_int_poly p) x = 0"
proof -
  from assms(1) obtain p where p: "p \<noteq> 0" "poly (of_int_poly p) x = 0"
    by (erule algebraicE')
  define n :: nat where "n = order 0 p"
  have "monom 1 n dvd p" by (simp add: monom_1_dvd_iff p n_def)
  then obtain q where q: "p = monom 1 n * q" by (erule dvdE)
  from p have "q \<noteq> 0" "poly (of_int_poly q) x = 0" by (auto simp: q poly_monom assms(2))
  moreover from this have "order 0 p = n + order 0 q" by (simp add: q order_mult)
  hence "order 0 q = 0" by (simp add: n_def)
  with \<open>q \<noteq> 0\<close> have "poly q 0 \<noteq> 0" by (simp add: order_root)
  ultimately show ?thesis using that[of q] by (auto simp: poly_0_coeff_0)
qed

lemma algebraic_of_real_iff [simp]:
   "algebraic (of_real x :: 'a :: {real_algebra_1,field_char_0}) \<longleftrightarrow> algebraic x"
proof
  assume "algebraic (of_real x :: 'a)"
  then obtain p where "p \<noteq> 0" "poly (of_int_poly p) (of_real x :: 'a) = 0"
    by (erule algebraicE')
  hence "(of_int_poly p :: real poly) \<noteq> 0"
        "poly (of_int_poly p :: real poly) x = 0" by simp_all
  thus "algebraic x" by (intro algebraicI[of "of_int_poly p"]) simp_all
next
  assume "algebraic x"
  then obtain p where "p \<noteq> 0" "poly (of_int_poly p) x = 0" by (erule algebraicE')
  hence "of_int_poly p \<noteq> (0 :: 'a poly)" "poly (of_int_poly p) (of_real x :: 'a) = 0"
    by simp_all
  thus "algebraic (of_real x)" by (intro algebraicI[of "of_int_poly p"]) simp_all
qed


subsection \<open>Main proof\<close>

lemma lindemann_weierstrass_integral:
  fixes u :: complex and f :: "complex poly"
  defines "df \<equiv> \<lambda>n. (pderiv ^^ n) f"
  defines "m \<equiv> degree f"
  defines "I \<equiv> \<lambda>f u. exp u * (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) 0) -
                       (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) u)"
  shows "((\<lambda>t. exp (u - t) * poly f t) has_contour_integral I f u) (linepath 0 u)"
proof -
  note [derivative_intros] =
    exp_scaleR_has_vector_derivative_right vector_diff_chain_within
  let ?g = "\<lambda>t. 1 - t" and ?f = "\<lambda>t. -exp (t *\<^sub>R u)"
  have "((\<lambda>t. exp ((1 - t) *\<^sub>R u) * u) has_integral
          (?f \<circ> ?g) 1 - (?f \<circ> ?g) 0) {0..1}"
    by (rule fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros simp del: o_apply)
  hence aux_integral: "((\<lambda>t. exp (u - t *\<^sub>R u) * u) has_integral exp u - 1) {0..1}"
    by (simp add: algebra_simps)

  have "((\<lambda>t. exp (u - t *\<^sub>R u) * u * poly f (t *\<^sub>R u)) has_integral I f u) {0..1}"
    unfolding df_def m_def
  proof (induction "degree f" arbitrary: f)
    case 0
    then obtain c where c: "f = [:c:]" by (auto elim: degree_eq_zeroE)
    have "((\<lambda>t. c * (exp (u - t *\<^sub>R u) * u)) has_integral c * (exp u - 1)) {0..1}"
      using aux_integral by (rule has_integral_mult_right)
    with c show ?case by (simp add: algebra_simps I_def)
  next
    case (Suc m)
    define df where "df = (\<lambda>j. (pderiv ^^ j) f)"
    show ?case
    proof (rule integration_by_parts[OF bounded_bilinear_mult])
      fix t :: real assume "t \<in> {0..1}"
      have "((?f \<circ> ?g) has_vector_derivative exp (u - t *\<^sub>R u) * u) (at t)"
        by (auto intro!: derivative_eq_intros simp: algebra_simps simp del: o_apply)
      thus "((\<lambda>t. -exp (u - t *\<^sub>R u)) has_vector_derivative exp (u - t *\<^sub>R u) * u) (at t)"
        by (simp add: algebra_simps o_def)
    next
      fix t :: real assume "t \<in> {0..1}"
      have "(poly f \<circ> (\<lambda>t. t *\<^sub>R u) has_vector_derivative u * poly (pderiv f) (t *\<^sub>R u)) (at t)"
        by (rule field_vector_diff_chain_at) (auto intro!: derivative_eq_intros)
      thus "((\<lambda>t. poly f (t *\<^sub>R u)) has_vector_derivative u * poly (pderiv f) (t *\<^sub>R u)) (at t)"
        by (simp add: o_def)
    next
      from Suc(2) have m: "m = degree (pderiv f)" by (simp add: degree_pderiv)
      from Suc(1)[OF this] this
        have "((\<lambda>t. exp (u - t *\<^sub>R u) * u * poly (pderiv f) (t *\<^sub>R u)) has_integral
                exp u * (\<Sum>j=0..m. poly (df (Suc j)) 0) - (\<Sum>j=0..m. poly (df (Suc j)) u)) {0..1}"
        by (simp add: df_def funpow_swap1 atMost_atLeast0 I_def)
      also have "(\<Sum>j=0..m. poly (df (Suc j)) 0) = (\<Sum>j=Suc 0..Suc m. poly (df j) 0)"
        by (rule sum.shift_bounds_cl_Suc_ivl [symmetric])
      also have "\<dots> = (\<Sum>j=0..Suc m. poly (df j) 0) - poly f 0"
        by (subst (2) sum.atLeast_Suc_atMost) (simp_all add: df_def)
      also have "(\<Sum>j=0..m. poly (df (Suc j)) u) = (\<Sum>j=Suc 0..Suc m. poly (df j) u)"
        by (rule sum.shift_bounds_cl_Suc_ivl [symmetric])
      also have "\<dots> = (\<Sum>j=0..Suc m. poly (df j) u) - poly f u"
        by (subst (2) sum.atLeast_Suc_atMost) (simp_all add: df_def)
      finally have "((\<lambda>t. - (exp (u - t *\<^sub>R u) * u * poly (pderiv f) (t *\<^sub>R u))) has_integral
                        -(exp u * ((\<Sum>j = 0..Suc m. poly (df j) 0) - poly f 0) -
                                  ((\<Sum>j = 0..Suc m. poly (df j) u) - poly f u))) {0..1}"
          (is "(_ has_integral ?I) _") by (rule has_integral_neg)
      also have "?I = - exp (u - 1 *\<^sub>R u) * poly f (1 *\<^sub>R u) -
                       - exp (u - 0 *\<^sub>R u) * poly f (0 *\<^sub>R u) - I f u"
        by (simp add: df_def algebra_simps Suc(2) atMost_atLeast0 I_def)
      finally show "((\<lambda>t. - exp (u - t *\<^sub>R u) * (u * poly (pderiv f) (t *\<^sub>R u)))
                        has_integral \<dots>) {0..1}" by (simp add: algebra_simps)
    qed (auto intro!: continuous_intros)
  qed
  thus ?thesis by (simp add: has_contour_integral_linepath algebra_simps)
qed

locale lindemann_weierstrass_aux =
  fixes f :: "complex poly"
begin

definition I :: "complex \<Rightarrow> complex" where
  "I u = exp u * (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) 0) -
                       (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) u)"

lemma lindemann_weierstrass_integral_bound:
  fixes u :: complex
  assumes "C \<ge> 0" "\<And>t. t \<in> closed_segment 0 u \<Longrightarrow> norm (poly f t) \<le> C"
  shows "norm (I u) \<le> norm u * exp (norm u) * C"
proof -
  have "I u = contour_integral (linepath 0 u) (\<lambda>t. exp (u - t) * poly f t)"
    using contour_integral_unique[OF lindemann_weierstrass_integral[of u f]] unfolding I_def ..
  also have "norm \<dots> \<le> exp (norm u) * C * norm (u - 0)"
  proof (intro contour_integral_bound_linepath)
    fix t assume t: "t \<in> closed_segment 0 u"
    then obtain s where s: "s \<in> {0..1}" "t = s *\<^sub>R u" by (auto simp: closed_segment_def)
    hence "s * norm u \<le> 1 * norm u" by (intro mult_right_mono) simp_all
    with s have norm_t: "norm t \<le> norm u" by auto

    from s have "Re u - Re t = (1 - s) * Re u" by (simp add: algebra_simps)
    also have "\<dots> \<le> norm u"
    proof (cases "Re u \<ge> 0")
      case True
      with \<open>s \<in> {0..1}\<close> have "(1 - s) * Re u \<le> 1 * Re u" by (intro mult_right_mono) simp_all
      also have "Re u \<le> norm u" by (rule complex_Re_le_cmod)
      finally show ?thesis by simp
    next
      case False
      with \<open>s \<in> {0..1}\<close> have "(1 - s) * Re u \<le> 0" by (intro mult_nonneg_nonpos) simp_all
      also have "\<dots> \<le> norm u" by simp
      finally show ?thesis .
    qed
    finally have "exp (Re u - Re t) \<le> exp (norm u)" by simp

    hence "exp (Re u - Re t) * norm (poly f t) \<le> exp (norm u) * C"
      using assms t norm_t by (intro mult_mono) simp_all
    thus "norm (exp (u - t) * poly f t) \<le> exp (norm u) * C"
      by (simp add: norm_mult exp_diff norm_divide field_simps)
  qed (auto simp: intro!: mult_nonneg_nonneg contour_integrable_continuous_linepath
                          continuous_intros assms)
  finally show ?thesis by (simp add: mult_ac)
qed

end

lemma poly_higher_pderiv_aux1:
  fixes c :: "'a :: idom"
  assumes "k < n"
  shows   "poly ((pderiv ^^ k) ([:-c, 1:] ^ n * p)) c = 0"
  using assms
proof (induction k arbitrary: n p)
  case (Suc k n p)
  from Suc.prems obtain n' where n: "n = Suc n'" by (cases n) auto
  from Suc.prems n have "k < n'" by simp
  have "(pderiv ^^ Suc k) ([:- c, 1:] ^ n * p) =
          (pderiv ^^ k) ([:- c, 1:] ^ n * pderiv p + [:- c, 1:] ^ n' * smult (of_nat n) p)"
    by (simp only: funpow_Suc_right o_def pderiv_mult n pderiv_power_Suc,
        simp only: n [symmetric]) (simp add: pderiv_pCons mult_ac)
  also from Suc.prems \<open>k < n'\<close> have "poly \<dots> c = 0"
    by (simp add: higher_pderiv_add Suc.IH del: mult_smult_right)
  finally show ?case .
qed simp_all

lemma poly_higher_pderiv_aux1':
  fixes c :: "'a :: idom"
  assumes "k < n" "[:-c, 1:] ^ n dvd p"
  shows   "poly ((pderiv ^^ k) p) c = 0"
proof -
  from assms(2) obtain q where "p = [:-c, 1:] ^ n * q" by (elim dvdE)
  also from assms(1) have "poly ((pderiv ^^ k) \<dots>) c = 0"
    by (rule poly_higher_pderiv_aux1)
  finally show ?thesis .
qed

lemma poly_higher_pderiv_aux2:
  fixes c :: "'a :: {idom, semiring_char_0}"
  shows   "poly ((pderiv ^^ n) ([:-c, 1:] ^ n * p)) c = fact n * poly p c"
proof (induction n arbitrary: p)
  case (Suc n p)
  have "(pderiv ^^ Suc n) ([:- c, 1:] ^ Suc n * p) =
          (pderiv ^^ n) ([:- c, 1:] ^ Suc n * pderiv p) +
            (pderiv ^^ n) ([:- c, 1:] ^ n * smult (1 + of_nat n) p)"
    by (simp del: funpow.simps power_Suc add: funpow_Suc_right pderiv_mult
          pderiv_power_Suc higher_pderiv_add pderiv_pCons mult_ac)
  also have "[:- c, 1:] ^ Suc n * pderiv p = [:- c, 1:] ^ n * ([:-c, 1:] * pderiv p)"
    by (simp add: algebra_simps)
  finally show ?case by (simp add: Suc.IH del: mult_smult_right power_Suc)
qed simp_all

lemma poly_higher_pderiv_aux3:
  fixes c :: "'a :: {idom,semiring_char_0}"
  assumes "k \<ge> n"
  shows   "\<exists>q. poly ((pderiv ^^ k) ([:-c, 1:] ^ n * p)) c = fact n * poly q c"
  using assms
proof (induction k arbitrary: n p)
  case (Suc k n p)
  show ?case
  proof (cases n)
    fix n' assume n: "n = Suc n'"
    have "poly ((pderiv ^^ Suc k) ([:-c, 1:] ^ n * p)) c =
            poly ((pderiv ^^ k) ([:- c, 1:] ^ n * pderiv p)) c +
              of_nat n * poly ((pderiv ^^ k) ([:-c, 1:] ^ n' * p)) c"
      by (simp del: funpow.simps power_Suc add: funpow_Suc_right pderiv_power_Suc
            pderiv_mult n pderiv_pCons higher_pderiv_add mult_ac higher_pderiv_smult)
    also have "\<exists>q1. poly ((pderiv ^^ k) ([:-c, 1:] ^ n * pderiv p)) c = fact n * poly q1 c"
      using Suc.prems Suc.IH[of n "pderiv p"]
      by (cases "n' = k") (auto simp: n poly_higher_pderiv_aux1 simp del: power_Suc of_nat_Suc
                                intro: exI[of _ "0::'a poly"])
    then obtain q1
      where "poly ((pderiv ^^ k) ([:-c, 1:] ^ n * pderiv p)) c = fact n * poly q1 c" ..
    also from Suc.IH[of n' p] Suc.prems obtain q2
      where "poly ((pderiv ^^ k) ([:-c, 1:] ^ n' * p)) c = fact n' * poly q2 c"
      by (auto simp: n)
    finally show ?case by (auto intro!: exI[of _ "q1 + q2"] simp: n algebra_simps)
  qed auto
qed auto

lemma poly_higher_pderiv_aux3':
  fixes c :: "'a :: {idom, semiring_char_0}"
  assumes "k \<ge> n" "[:-c, 1:] ^ n dvd p"
  shows   "fact n dvd poly ((pderiv ^^ k) p) c"
proof -
  from assms(2) obtain q where "p = [:-c, 1:] ^ n * q" by (elim dvdE)
  with poly_higher_pderiv_aux3[OF assms(1), of c q] show ?thesis by auto
qed

lemma e_transcendental_aux_bound:
  obtains C where "C \<ge> 0"
    "\<And>x. x \<in> closed_segment 0 (of_nat n) \<Longrightarrow>
        norm (\<Prod>k\<in>{1..n}. (x - of_nat k :: complex)) \<le> C"
proof -
  let ?f = "\<lambda>x. (\<Prod>k\<in>{1..n}. (x - of_nat k))"
  define C where "C = max 0 (Sup (cmod ` ?f ` closed_segment 0 (of_nat n)))"
  have "C \<ge> 0" by (simp add: C_def)
  moreover {
    fix x :: complex assume "x \<in> closed_segment 0 (of_nat n)"
    hence "cmod (?f x) \<le> Sup ((cmod \<circ> ?f) ` closed_segment 0 (of_nat n))"
      by (intro cSup_upper bounded_imp_bdd_above compact_imp_bounded compact_continuous_image)
         (auto intro!: continuous_intros)
    also have "\<dots> \<le> C" by (simp add: C_def image_comp)
    finally have "cmod (?f x) \<le> C" .
  }
  ultimately show ?thesis by (rule that)
qed


theorem e_transcendental_complex: "\<not> algebraic (exp 1 :: complex)"
proof
  assume "algebraic (exp 1 :: complex)"
  then obtain q :: "int poly"
    where q: "q \<noteq> 0" "coeff q 0 \<noteq> 0" "poly (of_int_poly q) (exp 1 :: complex) = 0"
      by (elim algebraicE'_nonzero) simp_all

  define n :: nat where "n = degree q"
  from q have [simp]: "n \<noteq> 0" by (intro notI) (auto simp: n_def elim!: degree_eq_zeroE)
  define qmax where "qmax = Max (insert 0 (abs ` set (coeffs q)))"
  have qmax_nonneg [simp]: "qmax \<ge> 0" by (simp add: qmax_def)
  have qmax: "\<bar>coeff q k\<bar> \<le> qmax" for k
    by (cases "k \<le> degree q")
       (auto simp: qmax_def coeff_eq_0 coeffs_def simp del: upt_Suc intro: Max.coboundedI)
  obtain C where C: "C \<ge> 0"
    "\<And>x. x \<in> closed_segment 0 (of_nat n) \<Longrightarrow> norm (\<Prod>k\<in>{1..n}. (x - of_nat k :: complex)) \<le> C"
    by (erule e_transcendental_aux_bound)
  define E where "E = (1 + real n) * real_of_int qmax * real n * exp (real n) / real n"
  define F where "F = real n * C"

  have ineq: "fact (p - 1) \<le> E * F ^ p" if p: "prime p" "p > n" "p > abs (coeff q 0)" for p
  proof -
    from p(1) have p_pos: "p > 0" by (simp add: prime_gt_0_nat)
    define f :: "int poly"
      where "f = monom 1 (p - 1) * (\<Prod>k\<in>{1..n}. [:-of_nat k, 1:] ^ p)"
    have poly_f: "poly (of_int_poly f) x = x ^ (p - 1) * (\<Prod>k\<in>{1..n}. (x - of_nat k)) ^ p"
      for x :: complex by (simp add: f_def poly_prod poly_monom prod_power_distrib)
    define m :: nat where "m = degree f"
    from p_pos have m: "m = (n + 1) * p - 1"
      by (simp add: m_def f_def degree_mult_eq degree_monom_eq degree_prod_sum_eq degree_linear_power)

    define M :: int where "M = (- 1) ^ (n * p) * fact n ^ p"
    with p have p_not_dvd_M: "\<not>int p dvd M"
      by (auto simp: M_def prime_elem_int_not_dvd_neg1_power prime_dvd_power_iff
            prime_gt_0_nat prime_dvd_fact_iff_int prime_dvd_mult_iff)

    interpret lindemann_weierstrass_aux "of_int_poly f" .
    define J :: complex where "J = (\<Sum>k\<le>n. of_int (coeff q k) * I (of_nat k))"
    define idxs where "idxs = ({..n}\<times>{..m}) - {(0, p - 1)}"

    hence "J = (\<Sum>k\<le>n. of_int (coeff q k) * exp 1 ^ k) * (\<Sum>n\<le>m. of_int (poly ((pderiv ^^ n) f) 0)) -
                 of_int (\<Sum>k\<le>n. \<Sum>n\<le>m. coeff q k * poly ((pderiv ^^ n) f) (int k))"
      by (simp add: J_def I_def algebra_simps sum_subtractf sum_distrib_left m_def
                    exp_of_nat_mult [symmetric])
    also have "(\<Sum>k\<le>n. of_int (coeff q k) * exp 1 ^ k) = poly (of_int_poly q) (exp 1 :: complex)"
      by (simp add: poly_altdef n_def)
    also have "\<dots> = 0" by fact
    finally have "J = of_int (-(\<Sum>(k,n)\<in>{..n}\<times>{..m}. coeff q k * poly ((pderiv ^^ n) f) (int k)))"
      by (simp add: sum.cartesian_product)
    also have "{..n}\<times>{..m} = insert (0, p - 1) idxs" by (auto simp: m idxs_def)
    also have "-(\<Sum>(k,n)\<in>\<dots>. coeff q k * poly ((pderiv ^^ n) f) (int k)) =
       - (coeff q 0 * poly ((pderiv ^^ (p - 1)) f) 0) -
         (\<Sum>(k, n)\<in>idxs. coeff q k * poly ((pderiv ^^ n) f) (of_nat k))"
      by (subst sum.insert) (simp_all add: idxs_def)
    also have "coeff q 0 * poly ((pderiv ^^ (p - 1)) f) 0 = coeff q 0 * M * fact (p - 1)"
    proof -
      have "f = [:-0, 1:] ^ (p - 1) * (\<Prod>k = 1..n. [:- of_nat k, 1:] ^ p)"
        by (simp add: f_def monom_altdef)
      also have "poly ((pderiv ^^ (p - 1)) \<dots>) 0 =
                   fact (p - 1) * poly (\<Prod>k = 1..n. [:- of_nat k, 1:] ^ p) 0"
        by (rule poly_higher_pderiv_aux2)
      also have "poly (\<Prod>k = 1..n. [:- of_nat k :: int, 1:] ^ p) 0 = (-1)^(n*p) * fact n ^ p"
        by (induction n) (simp_all add: prod.nat_ivl_Suc' power_mult_distrib mult_ac
                            power_minus' power_add del: of_nat_Suc)
      finally show ?thesis by (simp add: mult_ac M_def)
    qed
    also have "\<exists>N. (\<Sum>(k, n)\<in>idxs. coeff q k * poly ((pderiv ^^ n) f) (int k)) = fact p * N"
    proof -
      have "\<forall>(k, n)\<in>idxs. fact p dvd poly ((pderiv ^^ n) f) (of_nat k)"
      proof clarify
        fix k j assume idxs: "(k, j) \<in> idxs"
        then consider "k = 0" "j < p - 1" | "k = 0" "j > p - 1" | "k \<noteq> 0" "j < p" | "k \<noteq> 0" "j \<ge> p"
          by (fastforce simp: idxs_def)
        thus "fact p dvd poly ((pderiv ^^ j) f) (of_nat k)"
        proof cases
          case 1
          thus ?thesis
            by (simp add: f_def poly_higher_pderiv_aux1' monom_altdef)
        next
          case 2
          thus ?thesis
            by (simp add: f_def poly_higher_pderiv_aux3' monom_altdef fact_dvd_poly_higher_pderiv_aux')
        next
          case 3
          thus ?thesis unfolding f_def
            by (subst poly_higher_pderiv_aux1'[of _ p])
               (insert idxs, auto simp: idxs_def intro!: dvd_mult)
        next
          case 4
          thus ?thesis unfolding f_def
            by (intro poly_higher_pderiv_aux3') (insert idxs, auto intro!: dvd_mult simp: idxs_def)
        qed
      qed
      hence "fact p dvd (\<Sum>(k, n)\<in>idxs. coeff q k * poly ((pderiv ^^ n) f) (int k))"
        by (auto intro!: dvd_sum dvd_mult simp del: of_int_fact)
      thus ?thesis by (blast elim: dvdE)
    qed
    then guess N .. note N = this
    also from p have "- (coeff q 0 * M * fact (p - 1)) - fact p * N =
                        - fact (p - 1) * (coeff q 0 * M + p * N)"
      by (subst fact_reduce[of p]) (simp_all add: algebra_simps)
    finally have J: "J = -of_int (fact (p - 1) * (coeff q 0 * M + p * N))" by simp

    from p q(2) have "\<not>p dvd coeff q 0 * M + p * N"
      by (auto simp: dvd_add_left_iff p_not_dvd_M prime_dvd_fact_iff_int prime_dvd_mult_iff
               dest: dvd_imp_le_int)
    hence "coeff q 0 * M + p * N \<noteq> 0" by (intro notI) simp_all
    hence "abs (coeff q 0 * M + p * N) \<ge> 1" by simp
    hence "norm (of_int (coeff q 0 * M + p * N) :: complex) \<ge> 1" by (simp only: norm_of_int)
    hence "fact (p - 1) * \<dots> \<ge> fact (p - 1) * 1" by (intro mult_left_mono) simp_all
    hence J_lower: "norm J \<ge> fact (p - 1)" unfolding J norm_minus_cancel of_int_mult of_int_fact
      by (simp add: norm_mult)

    have "norm J \<le> (\<Sum>k\<le>n. norm (of_int (coeff q k) * I (of_nat k)))"
      unfolding J_def by (rule norm_sum)
    also have "\<dots> \<le> (\<Sum>k\<le>n. of_int qmax * (real n * exp (real n) * real n ^ (p - 1) * C ^ p))"
    proof (intro sum_mono)
      fix k assume k: "k \<in> {..n}"
      have "n > 0" by (rule ccontr) simp
      {
        fix x :: complex assume x: "x \<in> closed_segment 0 (of_nat k)"
        then obtain t where t: "t \<ge> 0" "t \<le> 1" "x = of_real t * of_nat k"
          by (auto simp: closed_segment_def scaleR_conv_of_real)
        hence "norm x = t * real k" by (simp add: norm_mult)
        also from \<open>t \<le> 1\<close> k have *: "\<dots> \<le> 1 * real n" by (intro mult_mono) simp_all
        finally have x': "norm x \<le> real n" by simp
        from t \<open>n > 0\<close> * have x'': "x \<in> closed_segment 0 (of_nat n)"
          by (auto simp: closed_segment_def scaleR_conv_of_real field_simps
                   intro!: exI[of _ "t * real k / real n"] )
        have "norm (poly (of_int_poly f) x) =
                norm x ^ (p - 1) * cmod (\<Prod>i = 1..n. x - i) ^ p"
          by (simp add: poly_f norm_mult norm_power)
        also from x x' x'' have "\<dots> \<le> of_nat n ^ (p - 1) * C ^ p"
          by (intro mult_mono C power_mono) simp_all
        finally have "norm (poly (of_int_poly f) x) \<le> real n ^ (p - 1) * C ^ p" .
      } note A = this

      have "norm (I (of_nat k)) \<le>
                      cmod (of_nat k) * exp (cmod (of_nat k)) * (of_nat n ^ (p - 1) * C ^ p)"
        by (intro lindemann_weierstrass_integral_bound[OF _ A]
              C mult_nonneg_nonneg zero_le_power) auto
      also have "\<dots> \<le> cmod (of_nat n) * exp (cmod (of_nat n)) * (of_nat n ^ (p - 1) * C ^ p)"
        using k by (intro mult_mono zero_le_power mult_nonneg_nonneg C) simp_all
      finally show "cmod (of_int (coeff q k) * I (of_nat k)) \<le>
                      of_int qmax * (real n * exp (real n) * real n ^ (p - 1) * C ^ p)"
        unfolding norm_mult
        by (intro mult_mono) (simp_all add: qmax of_int_abs [symmetric] del: of_int_abs)
    qed
    also have "\<dots> = E * F ^ p" using p_pos
      by (simp add: power_diff power_mult_distrib E_def F_def)
    finally show "fact (p - 1) \<le> E * F ^ p" using J_lower by linarith
  qed

  have "(\<lambda>n. E * F * F ^ (n - 1) / fact (n - 1)) \<longlonglongrightarrow> 0" (is ?P)
    by (intro filterlim_compose[OF power_over_fact_tendsto_0' filterlim_minus_nat_at_top])
  also have "?P \<longleftrightarrow> (\<lambda>n. E * F ^ n / fact (n - 1)) \<longlonglongrightarrow> 0"
    by (intro filterlim_cong refl eventually_mono[OF eventually_gt_at_top[of "0::nat"]])
       (auto simp: power_Suc [symmetric] simp del: power_Suc)
  finally have "eventually (\<lambda>n. E * F ^ n / fact (n - 1) < 1) at_top"
    by (rule order_tendstoD) simp_all
  hence "eventually (\<lambda>n. E * F ^ n < fact (n - 1)) at_top" by eventually_elim simp
  then obtain P where P: "\<And>n. n \<ge> P \<Longrightarrow> E * F ^ n < fact (n - 1)"
    by (auto simp: eventually_at_top_linorder)

  have "\<exists>p. prime p \<and> p > Max {nat (abs (coeff q 0)), n, P}" by (rule bigger_prime)
  then obtain p where "prime p" "p > Max {nat (abs (coeff q 0)), n, P}" by blast
  hence "int p > abs (coeff q 0)" "p > n" "p \<ge> P" by auto
  with ineq[of p] \<open>prime p\<close> have "fact (p - 1) \<le> E * F ^ p" by simp
  moreover from \<open>p \<ge> P\<close> have "fact (p - 1) > E * F ^ p" by (rule P)
  ultimately show False by linarith
qed

corollary e_transcendental_real: "\<not> algebraic (exp 1 :: real)"
proof -
  have "\<not>algebraic (exp 1 :: complex)" by (rule e_transcendental_complex)
  also have "(exp 1 :: complex) = of_real (exp 1)" using exp_of_real[of 1] by simp
  also have "algebraic \<dots> \<longleftrightarrow> algebraic (exp 1 :: real)" by simp
  finally show ?thesis .
qed

end
