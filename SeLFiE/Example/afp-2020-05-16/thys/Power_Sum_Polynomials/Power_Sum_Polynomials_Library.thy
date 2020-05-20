(*
  File:     Power_Sum_Polynomials_Library.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Auxiliary material\<close>
theory Power_Sum_Polynomials_Library
imports
  "Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized"  
  "Symmetric_Polynomials.Symmetric_Polynomials"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

subsection \<open>Miscellaneous\<close>

lemma atLeastAtMost_nat_numeral:
  "atLeastAtMost m (numeral k :: nat) =
     (if m \<le> numeral k then insert (numeral k) (atLeastAtMost m (pred_numeral k))
                 else {})"
  by (simp add: numeral_eq_Suc atLeastAtMostSuc_conv)

lemma sum_in_Rats [intro]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>) \<Longrightarrow> sum f A \<in> \<rat>"
  by (induction A rule: infinite_finite_induct) auto

(* TODO Move *)
lemma (in monoid_mult) prod_list_distinct_conv_prod_set:
  "distinct xs \<Longrightarrow> prod_list (map f xs) = prod f (set xs)"
  by (induct xs) simp_all

lemma (in monoid_mult) interv_prod_list_conv_prod_set_nat:
  "prod_list (map f [m..<n]) = prod f (set [m..<n])"
  by (simp add: prod_list_distinct_conv_prod_set)

lemma (in monoid_mult) prod_list_prod_nth:
  "prod_list xs = (\<Prod>i = 0..< length xs. xs ! i)"
  using interv_prod_list_conv_prod_set_nat [of "(!) xs" 0 "length xs"] by (simp add: map_nth)


lemma gcd_poly_code_aux_reduce:
  "gcd_poly_code_aux p 0 = normalize p"
  "q \<noteq> 0 \<Longrightarrow> gcd_poly_code_aux p q = gcd_poly_code_aux q (primitive_part (pseudo_mod p q))"
  by (subst gcd_poly_code_aux.simps; simp)+

lemma coprimeI_primes:
  fixes a b :: "'a :: factorial_semiring"
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  assumes "\<And>p. prime p \<Longrightarrow> p dvd a \<Longrightarrow> p dvd b \<Longrightarrow> False"
  shows   "coprime a b"
proof (rule coprimeI)
  fix d assume d: "d dvd a" "d dvd b"
  with assms(1) have [simp]: "d \<noteq> 0" by auto
  show "is_unit d"
  proof (rule ccontr)
    assume "\<not>is_unit d"
    then obtain p where p: "prime p" "p dvd d"
      using prime_divisor_exists[of d] by auto
    from assms(2)[of p] and p and d show False
      using dvd_trans by auto
  qed
qed

lemma coprime_pderiv_imp_squarefree:
  assumes "coprime p (pderiv p)"
  shows   "squarefree p"
proof (rule squarefreeI)
  fix d assume d: "d ^ 2 dvd p"
  then obtain q where q: "p = d ^ 2 * q"
    by (elim dvdE)
  hence "d dvd p" "d dvd pderiv p"
    by (auto simp: pderiv_mult pderiv_power_Suc numeral_2_eq_2)
  with assms show "is_unit d"
    using not_coprimeI by blast
qed

lemma squarefree_field_poly_iff:
  fixes p :: "'a :: {field_char_0,euclidean_ring_gcd,semiring_gcd_mult_normalize} poly"
  assumes [simp]: "p \<noteq> 0"
  shows "squarefree p \<longleftrightarrow> coprime p (pderiv p)"
proof
  assume "squarefree p"
  show "coprime p (pderiv p)"
  proof (rule coprimeI_primes)
    fix d assume d: "d dvd p" "d dvd pderiv p" "prime d"
    from d(1) obtain q where q: "p = d * q"
      by (elim dvdE)   
    from d(2) and q have "d dvd q * pderiv d"
      by (simp add: pderiv_mult dvd_add_right_iff)
    with \<open>prime d\<close> have "d dvd q \<or> d dvd pderiv d"
      using prime_dvd_mult_iff by blast
    thus False
    proof
      assume "d dvd q"
      hence "d ^ 2 dvd p"
        by (auto simp: q power2_eq_square)
      with \<open>squarefree p\<close> show False
        using d(3) not_prime_unit squarefreeD by blast
    next
      assume "d dvd pderiv d"
      hence "Polynomial.degree d = 0" by simp
      moreover have "d \<noteq> 0" using d by auto
      ultimately show False
        using d(3) is_unit_iff_degree not_prime_unit by blast
    qed
  qed auto
qed (use coprime_pderiv_imp_squarefree[of p] in auto)

lemma coprime_pderiv_imp_rsquarefree:
  assumes "coprime (p :: 'a :: field_char_0 poly) (pderiv p)"
  shows   "rsquarefree p"
  unfolding rsquarefree_roots
proof safe
  fix x assume "poly p x = 0" "poly (pderiv p) x = 0"
  hence "[:-x, 1:] dvd p" "[:-x, 1:] dvd pderiv p"
    by (auto simp: poly_eq_0_iff_dvd)
  with assms have "is_unit [:-x, 1:]"
    using not_coprimeI by blast
  thus False by auto
qed

lemma poly_of_nat [simp]: "poly (of_nat n) x = of_nat n"
  by (induction n) auto

lemma poly_of_int [simp]: "poly (of_int n) x = of_int n"
  by (cases n) auto

lemma order_eq_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p = 0 \<longleftrightarrow> poly p x \<noteq> 0"
  by (auto simp: order_root)

lemma order_pos_iff: "p \<noteq> 0 \<Longrightarrow> order x p > 0 \<longleftrightarrow> poly p x = 0"
  by (auto simp: order_root)

lemma order_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "order x (\<Prod>y\<in>A. f y) = (\<Sum>y\<in>A. order x (f y))"
  using assms by (induction A rule: infinite_finite_induct) (auto simp: order_mult)

lemma order_prod_mset:
  assumes "0 \<notin># A"
  shows   "order x (prod_mset A) = sum_mset (image_mset (order x) A)"
  using assms by (induction A) (auto simp: order_mult)

lemma order_prod_list:
  assumes "0 \<notin> set xs"
  shows   "order x (prod_list xs) = sum_list (map (order x) xs)"
  using assms by (induction xs) (auto simp: order_mult)

lemma order_power: "p \<noteq> 0 \<Longrightarrow> order x (p ^ n) = n * order x p"
  by (induction n) (auto simp: order_mult)


lemma smult_0_right [simp]: "MPoly_Type.smult p 0 = 0"
  by (transfer, transfer) auto

lemma mult_smult_right [simp]: 
  fixes c :: "'a :: comm_semiring_0"
  shows "p * MPoly_Type.smult c q = MPoly_Type.smult c (p * q)"
  by (simp add: smult_conv_mult mult_ac)

lemma mapping_single_eq_iff [simp]:
  "Poly_Mapping.single a b = Poly_Mapping.single c d \<longleftrightarrow> b = 0 \<and> d = 0 \<or> a = c \<and> b = d"
  by transfer (unfold fun_eq_iff when_def, metis)

lemma monom_of_set_plus_monom_of_set:
  assumes "A \<inter> B = {}" "finite A" "finite B"
  shows   "monom_of_set A + monom_of_set B = monom_of_set (A \<union> B)"
  using assms by transfer (auto simp: fun_eq_iff)
  
lemma mpoly_monom_0_eq_Const: "monom 0 c = Const c"
  by (intro mpoly_eqI) (auto simp: coeff_monom when_def mpoly_coeff_Const)

lemma mpoly_Const_0 [simp]: "Const 0 = 0"
  by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const mpoly_coeff_0)

lemma mpoly_Const_1 [simp]: "Const 1 = 1"
  by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const mpoly_coeff_1)

lemma mpoly_Const_uminus: "Const (-a) = -Const a"
  by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const)

lemma mpoly_Const_add: "Const (a + b) = Const a + Const b"
  by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const)

lemma mpoly_Const_mult: "Const (a * b) = Const a * Const b"
  unfolding mpoly_monom_0_eq_Const [symmetric] mult_monom by simp

lemma mpoly_Const_power: "Const (a ^ n) = Const a ^ n"
  by (induction n) (auto simp: mpoly_Const_mult)

lemma of_nat_mpoly_eq: "of_nat n = Const (of_nat n)"
proof (induction n)
  case 0
  have "0 = (Const 0 :: 'a mpoly)"
    by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const)
  thus ?case
    by simp
next
  case (Suc n)
  have "1 + Const (of_nat n) = Const (1 + of_nat n)"
    by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const mpoly_coeff_1)
  thus ?case
    using Suc by auto
qed

lemma insertion_of_nat [simp]: "insertion f (of_nat n) = of_nat n"
  by (simp add: of_nat_mpoly_eq)
  
lemma insertion_monom_of_set [simp]:
  "insertion f (monom (monom_of_set X) c) = c * (\<Prod>i\<in>X. f i)"
proof (cases "finite X")
  case [simp]: True
  have "insertion f (monom (monom_of_set X) c) = c * (\<Prod>a. f a ^ (if a \<in> X then 1 else 0))"
    by (auto simp: lookup_monom_of_set)
  also have "(\<Prod>a. f a ^ (if a \<in> X then 1 else 0)) = (\<Prod>i\<in>X. f i ^ (if i \<in> X then 1 else 0))"
    by (intro Prod_any.expand_superset) auto
  also have "\<dots> = (\<Prod>i\<in>X. f i)"
    by (intro prod.cong) auto
  finally show ?thesis .
qed (auto simp: lookup_monom_of_set)


(* TODO: Move! Version in AFP is too weak! *)
lemma symmetric_mpoly_symmetric_sum:
  assumes "\<And>\<pi>. \<pi> permutes A \<Longrightarrow> g \<pi> permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g \<pi> x)"
  shows "symmetric_mpoly A (\<Sum>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (sum f X) = (\<Sum>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Sum>x\<in>X. f (g \<pi> x))"
    by (intro sum.cong assms \<pi> refl)
  also have "\<dots> = (\<Sum>x\<in>g \<pi>`X. f x)"
    using assms(1)[OF \<pi>] by (subst sum.reindex) (auto simp: permutes_inj_on)
  also have "g \<pi> ` X = X"
    using assms(1)[OF \<pi>] by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (sum f X) = sum f X" .
qed

lemma sym_mpoly_0 [simp]:
  assumes "finite A"
  shows   "sym_mpoly A 0 = 1"
  using assms by (transfer, transfer) (auto simp: fun_eq_iff when_def)

lemma sym_mpoly_eq_0 [simp]:
  assumes "k > card A"
  shows   "sym_mpoly A k = 0"
proof (transfer fixing: A k, transfer fixing: A k, intro ext)
  fix mon
  have "\<not>(finite A \<and> (\<exists>Y\<subseteq>A. card Y = k \<and> mon = monom_of_set Y))"
  proof safe
    fix Y assume Y: "finite A" "Y \<subseteq> A" "k = card Y" "mon = monom_of_set Y"
    hence "card Y \<le> card A" by (intro card_mono) auto
    with Y and assms show False by simp
  qed
  thus "(if finite A \<and> (\<exists>Y\<subseteq>A. card Y = k \<and> mon = monom_of_set Y) then 1 else 0) = 0"
    by auto
qed

lemma coeff_sym_mpoly_monom_of_set_eq_0:
  assumes "finite X" "Y \<subseteq> X" "card Y \<noteq> k"
  shows   "MPoly_Type.coeff (sym_mpoly X k) (monom_of_set Y) = 0"
  using assms finite_subset[of _ X] by (auto simp: coeff_sym_mpoly)

lemma coeff_sym_mpoly_monom_of_set_eq_0':
  assumes "finite X" "\<not>Y \<subseteq> X" "finite Y"
  shows   "MPoly_Type.coeff (sym_mpoly X k) (monom_of_set Y) = 0"
  using assms finite_subset[of _ X] by (auto simp: coeff_sym_mpoly)


subsection \<open>The set of roots of a univariate polynomial\<close>

lift_definition poly_roots :: "'a :: idom poly \<Rightarrow> 'a multiset" is
  "\<lambda>p x. if p = 0 then 0 else order x p"
proof -
  fix p :: "'a poly"
  show "(\<lambda>x. if p = 0 then 0 else order x p) \<in> multiset"
    by (cases "p = 0") (auto simp: multiset_def order_pos_iff poly_roots_finite)
qed

lemma poly_roots_0 [simp]: "poly_roots 0 = {#}"
  by transfer auto

lemma poly_roots_1 [simp]: "poly_roots 1 = {#}"
  by transfer auto

lemma count_poly_roots [simp]:
  assumes "p \<noteq> 0"
  shows   "count (poly_roots p) x = order x p"
  using assms by transfer auto

lemma in_poly_roots_iff [simp]: "p \<noteq> 0 \<Longrightarrow> x \<in># poly_roots p \<longleftrightarrow> poly p x = 0"
  by (subst count_greater_zero_iff [symmetric], subst count_poly_roots) (auto simp: order_pos_iff)

lemma set_mset_poly_roots: "p \<noteq> 0 \<Longrightarrow> set_mset (poly_roots p) = {x. poly p x = 0}"
  using in_poly_roots_iff[of p] by blast

lemma count_poly_roots': "count (poly_roots p) x = (if p = 0 then 0 else order x p)"
  by transfer' auto

lemma poly_roots_const [simp]: "poly_roots [:c:] = {#}"
  by (intro multiset_eqI) (auto simp: count_poly_roots' order_eq_0_iff)

lemma poly_roots_linear [simp]: "poly_roots [:-x, 1:] = {#x#}"
  by (intro multiset_eqI) (auto simp: count_poly_roots' order_eq_0_iff)

lemma poly_roots_monom [simp]: "c \<noteq> 0 \<Longrightarrow> poly_roots (Polynomial.monom c n) = replicate_mset n 0"
  by (intro multiset_eqI) (auto simp: count_poly_roots' order_eq_0_iff poly_monom)

lemma poly_roots_smult [simp]: "c \<noteq> 0 \<Longrightarrow> poly_roots (Polynomial.smult c p) = poly_roots p"
  by (intro multiset_eqI) (auto simp: count_poly_roots' order_smult)

lemma poly_roots_mult: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> poly_roots (p * q) = poly_roots p + poly_roots q"
  by (intro multiset_eqI) (auto simp: count_poly_roots' order_mult)

lemma poly_roots_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "poly_roots (prod f A) = (\<Sum>x\<in>A. poly_roots (f x))"
  using assms by (induction A rule: infinite_finite_induct) (auto simp: poly_roots_mult)

lemma poly_roots_prod_mset:
  assumes "0 \<notin># A"
  shows   "poly_roots (prod_mset A) = sum_mset (image_mset poly_roots A)"
  using assms by (induction A) (auto simp: poly_roots_mult)

lemma poly_roots_prod_list:
  assumes "0 \<notin> set xs"
  shows   "poly_roots (prod_list xs) = sum_list (map poly_roots xs)"
  using assms by (induction xs) (auto simp: poly_roots_mult)

lemma poly_roots_power: "p \<noteq> 0 \<Longrightarrow> poly_roots (p ^ n) = repeat_mset n (poly_roots p)"
  by (induction n) (auto simp: poly_roots_mult)

lemma rsquarefree_poly_roots_eq:
  assumes "rsquarefree p"
  shows   "poly_roots p = mset_set {x. poly p x = 0}"
proof (rule multiset_eqI)
  fix x :: 'a
  from assms show "count (poly_roots p) x = count (mset_set {x. poly p x = 0}) x"
    by (cases "poly p x = 0") (auto simp: poly_roots_finite order_eq_0_iff rsquarefree_def)
qed

lemma rsquarefree_imp_distinct_roots:
  assumes "rsquarefree p" and "mset xs = poly_roots p"
  shows   "distinct xs"
proof (cases "p = 0")
  case [simp]: False
  have *: "mset xs = mset_set {x. poly p x = 0}"
    using assms by (simp add: rsquarefree_poly_roots_eq)
  hence "set_mset (mset xs) = set_mset (mset_set {x. poly p x = 0})"
    by (simp only: )
  hence [simp]: "set xs = {x. poly p x = 0}"
    by (simp add: poly_roots_finite)
  from * show ?thesis
    by (subst distinct_count_atmost_1) (auto simp: poly_roots_finite)
qed (use assms in auto)

lemma poly_roots_factorization:
  fixes p c A
  assumes [simp]: "c \<noteq> 0"
  defines "p \<equiv> Polynomial.smult c (prod_mset (image_mset (\<lambda>x. [:-x, 1:]) A))"
  shows   "poly_roots p = A"
proof -
  have "poly_roots p = poly_roots (\<Prod>x\<in>#A. [:-x, 1:])"
    by (auto simp: p_def)
  also have "\<dots> = A"
    by (subst poly_roots_prod_mset) (auto simp: image_mset.compositionality o_def)
  finally show ?thesis .
qed

lemma fundamental_theorem_algebra_factorized':
  fixes p :: "complex poly"
  shows "p = Polynomial.smult (Polynomial.lead_coeff p) 
               (prod_mset (image_mset (\<lambda>x. [:-x, 1:]) (poly_roots p)))"
proof (cases "p = 0")
  case [simp]: False
  obtain xs where
    xs: "Polynomial.smult (Polynomial.lead_coeff p) (\<Prod>x\<leftarrow>xs. [:-x, 1:]) = p"
        "length xs = Polynomial.degree p"
    using fundamental_theorem_algebra_factorized[of p] by auto
  define A where "A = mset xs"

  note xs(1)
  also have "(\<Prod>x\<leftarrow>xs. [:-x, 1:]) = prod_mset (image_mset (\<lambda>x. [:-x, 1:]) A)"
    unfolding A_def by (induction xs) auto
  finally have *: "Polynomial.smult (Polynomial.lead_coeff p) (\<Prod>x\<in>#A. [:- x, 1:]) = p" .
  also have "A = poly_roots p"
    using poly_roots_factorization[of "Polynomial.lead_coeff p" A]
    by (subst * [symmetric]) auto
  finally show ?thesis ..
qed auto
  
lemma poly_roots_eq_imp_eq:
  fixes p q :: "complex poly"
  assumes "Polynomial.lead_coeff p = Polynomial.lead_coeff q"
  assumes "poly_roots p = poly_roots q"
  shows   "p = q"
proof (cases "p = 0 \<or> q = 0")
  case False
  hence [simp]: "p \<noteq> 0" "q \<noteq> 0"
    by auto
  have "p = Polynomial.smult (Polynomial.lead_coeff p) 
               (prod_mset (image_mset (\<lambda>x. [:-x, 1:]) (poly_roots p)))"
    by (rule fundamental_theorem_algebra_factorized')
  also have "\<dots> = Polynomial.smult (Polynomial.lead_coeff q) 
                   (prod_mset (image_mset (\<lambda>x. [:-x, 1:]) (poly_roots q)))"
    by (simp add: assms)
  also have "\<dots> = q"
    by (rule fundamental_theorem_algebra_factorized' [symmetric])
  finally show ?thesis .
qed (use assms in auto)

lemma Sum_any_zeroI': "(\<And>x. P x \<Longrightarrow> f x = 0) \<Longrightarrow> Sum_any (\<lambda>x. f x when P x) = 0"
  by (auto simp: Sum_any.expand_set)

(* TODO: This was not really needed here, but it is important nonetheless.
   It should go in the Symmetric_Polynomials entry. *)
lemma sym_mpoly_insert:
  assumes "finite X" "x \<notin> X"
  shows   "(sym_mpoly (insert x X) (Suc k) :: 'a :: semiring_1 mpoly) =
             monom (monom_of_set {x}) 1 * sym_mpoly X k + sym_mpoly X (Suc k)" (is "?lhs = ?A + ?B")
proof (rule mpoly_eqI)
  fix mon
  show "coeff ?lhs mon = coeff (?A + ?B) mon"
  proof (cases "\<forall>i. lookup mon i \<le> 1 \<and> (i \<notin> insert x X \<longrightarrow> lookup mon i = 0)")
    case False
    then obtain i where i: "lookup mon i > 1 \<or> i \<notin> insert x X \<and> lookup mon i > 0"
      by (auto simp: not_le)
    
    have "coeff ?A mon = prod_fun (coeff (monom (monom_of_set {x}) 1))
                                  (coeff (sym_mpoly X k)) mon"
      by (simp add: coeff_mpoly_times)
    also have "\<dots> = (\<Sum>l. \<Sum>q. coeff (monom (monom_of_set {x}) 1) l * coeff (sym_mpoly X k) q
                         when mon = l + q)"
        unfolding prod_fun_def 
        by (intro Sum_any.cong, subst Sum_any_right_distrib, force)
           (auto simp: Sum_any_right_distrib when_def intro!: Sum_any.cong)
    also have "\<dots> = 0"
    proof (rule Sum_any_zeroI, rule Sum_any_zeroI')
      fix ma mb assume *: "mon = ma + mb"
      show "coeff (monom (monom_of_set {x}) (1::'a)) ma * coeff (sym_mpoly X k) mb = 0"
      proof (cases "i = x")
        case [simp]: True
        show ?thesis
        proof (cases "lookup mb i > 0")
          case True
          hence "coeff (sym_mpoly X k) mb = 0" using \<open>x \<notin> X\<close>
            by (auto simp: coeff_sym_mpoly lookup_monom_of_set split: if_splits)
          thus ?thesis
            using mult_not_zero by blast
        next
          case False
          hence "coeff (monom (monom_of_set {x}) 1) ma = 0"
            using i by (auto simp: coeff_monom when_def * lookup_add)
          thus ?thesis
            using mult_not_zero by blast
        qed
      next
        case [simp]: False
        show ?thesis
        proof (cases "lookup ma i > 0")
          case False
          hence "lookup mb i = lookup mon i"
            using * by (auto simp: lookup_add)
          hence "coeff (sym_mpoly X k) mb = 0" using i
            by (auto simp: coeff_sym_mpoly lookup_monom_of_set split: if_splits)
          thus ?thesis
            using mult_not_zero by blast
        next
          case True
          hence "coeff (monom (monom_of_set {x}) 1) ma = 0"
            using i by (auto simp: coeff_monom when_def * lookup_add)
          thus ?thesis
            using mult_not_zero by blast
        qed
      qed
    qed
    finally have "coeff ?A mon = 0" .
    moreover from False have "coeff ?lhs mon = 0"
      by (subst coeff_sym_mpoly) (auto simp: lookup_monom_of_set split: if_splits)
    moreover from False have "coeff (sym_mpoly X (Suc k)) mon = 0"
      by (subst coeff_sym_mpoly) (auto simp: lookup_monom_of_set split: if_splits)
    ultimately show ?thesis
      by auto
  next
    case True
    define A where "A = keys mon"
    have A: "A \<subseteq> insert x X"
      using True by (auto simp: A_def)
    have [simp]: "mon = monom_of_set A"
      unfolding A_def using True by transfer (force simp: fun_eq_iff le_Suc_eq)
    have "finite A"
      using finite_subset A assms by blast
    show ?thesis
    proof (cases "x \<in> A")
      case False
      have "coeff ?A mon = prod_fun (coeff (monom (monom_of_set {x}) 1))
                                    (coeff (sym_mpoly X k)) (monom_of_set A)"
        by (simp add: coeff_mpoly_times)
      also have "\<dots> = (\<Sum>l. \<Sum>q. coeff (monom (monom_of_set {x}) 1) l * coeff (sym_mpoly X k) q
                         when monom_of_set A = l + q)"
        unfolding prod_fun_def 
        by (intro Sum_any.cong, subst Sum_any_right_distrib, force)
           (auto simp: Sum_any_right_distrib when_def intro!: Sum_any.cong)
      also have "\<dots> = 0"
      proof (rule Sum_any_zeroI, rule Sum_any_zeroI')
        fix ma mb assume *: "monom_of_set A = ma + mb"
        hence "keys ma \<subseteq> A"
          using \<open>finite A\<close> by transfer (auto simp: fun_eq_iff split: if_splits)
        thus "coeff (monom (monom_of_set {x}) (1::'a)) ma * coeff (sym_mpoly X k) mb = 0"
          using \<open>x \<notin> A\<close> by (auto simp: coeff_monom when_def)
      qed
      finally show ?thesis
        using False A assms finite_subset[of _ "insert x X"] finite_subset[of _ X]
        by (auto simp: coeff_sym_mpoly)
    next
      case True
      have "mon = monom_of_set {x} + monom_of_set (A - {x})"
        using \<open>x \<in> A\<close> \<open>finite A\<close> by (auto simp: monom_of_set_plus_monom_of_set)
      also have "coeff ?A \<dots> = coeff (sym_mpoly X k) (monom_of_set (A - {x}))"
        by (subst coeff_monom_mult) auto
      also have "\<dots> = (if card A = Suc k then 1 else 0)"
      proof (cases "card A = Suc k")
        case True
        thus ?thesis
          using assms \<open>finite A\<close> \<open>x \<in> A\<close> A
          by (subst coeff_sym_mpoly_monom_of_set) auto
      next
        case False
        thus ?thesis
          using assms \<open>x \<in> A\<close> A \<open>finite A\<close> card_Suc_Diff1[of A x]
          by (subst coeff_sym_mpoly_monom_of_set_eq_0) auto
      qed
      moreover have "coeff ?B (monom_of_set A) = 0"
        using assms \<open>x \<in> A\<close> \<open>finite A\<close>
        by (subst coeff_sym_mpoly_monom_of_set_eq_0') auto
      moreover have "coeff ?lhs (monom_of_set A) = (if card A = Suc k then 1 else 0)"
        using assms A \<open>finite A\<close> finite_subset[of _ "insert x X"] by (auto simp: coeff_sym_mpoly)
      ultimately show ?thesis by simp
    qed
  qed
qed


end