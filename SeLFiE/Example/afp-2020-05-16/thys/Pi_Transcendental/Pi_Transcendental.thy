(*
    File:      Pi_Transcendendtal.thy
    Author:    Manuel Eberl, TU München

   A proof of the transcendence of pi
*)
section \<open>The Transcendence of $\pi$\<close>
theory Pi_Transcendental
imports
  "E_Transcendental.E_Transcendental"
  "Symmetric_Polynomials.Symmetric_Polynomials"
  "HOL-Real_Asymp.Real_Asymp" 
  Pi_Transcendental_Polynomial_Library
begin

lemma ring_homomorphism_to_poly [intro]: "ring_homomorphism (\<lambda>i. [:i:])"
  by standard auto

lemma (in ring_closed) coeff_power_closed:
  "(\<And>m. coeff p m \<in> A) \<Longrightarrow> coeff (p ^ n) m \<in> A"
  by (induction n arbitrary: m)
     (auto simp: mpoly_coeff_1 coeff_mpoly_times intro!: prod_fun_closed)

lemma (in ring_closed) coeff_prod_closed:
  "(\<And>x m. x \<in> X \<Longrightarrow> coeff (f x) m \<in> A) \<Longrightarrow> coeff (prod f X) m \<in> A"
  by (induction X arbitrary: m rule: infinite_finite_induct)
     (auto simp: mpoly_coeff_1 coeff_mpoly_times intro!: prod_fun_closed)

lemma map_of_rat_of_int_poly [simp]: "map_poly of_rat (of_int_poly p) = of_int_poly p"
  by (intro poly_eqI) (auto simp: coeff_map_poly)

text \<open>
  Given a polynomial with rational coefficients, we can obtain an integer polynomial that
  differs from it only by a nonzero constant by clearing the denominators.
\<close>
lemma ratpoly_to_intpoly:
  assumes "\<forall>i. poly.coeff p i \<in> \<rat>"
  obtains q c where "c \<noteq> 0" "p = Polynomial.smult (inverse (of_nat c)) (of_int_poly q)"
proof (cases "p = 0")
  case True
  with that[of 1 0] show ?thesis by auto
next
  case False
  from assms obtain p' where p': "p = map_poly of_rat p'"
    using ratpolyE by auto
  define c where "c = Lcm ((nat \<circ> snd \<circ> quotient_of \<circ> poly.coeff p') ` {..Polynomial.degree p'})"
  have "\<not>snd (quotient_of x) \<le> 0" for x
    using quotient_of_denom_pos[of x, OF surjective_pairing] by auto
  hence "c \<noteq> 0" by (auto simp: c_def)
  define q where "q = Polynomial.smult (of_nat c) p'"

  have "poly.coeff q i \<in> \<int>" for i
  proof (cases "i > Polynomial.degree p'")
    case False
    define m n 
      where "m = fst (quotient_of (poly.coeff p' i))"
        and "n = nat (snd (quotient_of (poly.coeff p' i)))"
    have mn: "n > 0" "poly.coeff p' i = of_int m / of_nat n"
      using quotient_of_denom_pos[of "poly.coeff p' i", OF surjective_pairing]
            quotient_of_div[of "poly.coeff p' i", OF surjective_pairing]
      by (auto simp: m_def n_def)
    from False have "n dvd c" unfolding c_def
      by (intro dvd_Lcm) (auto simp: c_def n_def o_def not_less)
    hence "of_nat c * (of_int m / of_nat n) = (of_nat (c div n) * of_int m :: rat)"
      by (auto simp: of_nat_div)
    also have "\<dots> \<in> \<int>" by auto
    finally show ?thesis using mn by (auto simp: q_def)
  qed (auto simp: q_def coeff_eq_0)
  with int_polyE obtain q' where q': "q = of_int_poly q'" by auto
  moreover have "p = Polynomial.smult (inverse (of_nat c)) (map_poly of_rat (of_int_poly q'))"
    unfolding smult_conv_map_poly q'[symmetric] p' using \<open>c \<noteq> 0\<close>
    by (intro poly_eqI) (auto simp: coeff_map_poly q_def of_rat_mult)
  ultimately show ?thesis
    using q' p' \<open>c \<noteq> 0\<close> by (auto intro!: that[of c q'])
qed

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

(* TODO: The version of this theorem in the AFP is to weak and should be replaced by this one. *)
lemma symmetric_mpoly_symmetric_prod:
  assumes "g permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g x)"
  shows "symmetric_mpoly A (\<Prod>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (prod f X) = (\<Prod>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Prod>x\<in>X. f (g x))"
    by (intro prod.cong assms \<pi> refl)
  also have "\<dots> = (\<Prod>x\<in>g`X. f x)"
    using assms by (subst prod.reindex) (auto simp: permutes_inj_on)
  also have "g ` X = X"
    using assms by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (prod f X) = prod f X" .
qed


text \<open>
  We now prove the transcendence of $i\pi$, from which the transcendence of $\pi$ will follow
  as a trivial corollary. The first proof of this was given by von Lindemann~\cite{lindemann_pi82}.
  The central ingredient is the fundamental theorem of symmetric functions.

  The proof can, by now, be considered folklore and one can easily find many similar variants of
  it, but we mostly follows the nice exposition given by Niven~\cite{niven_pi39}.

  An independent previous formalisation in Coq that uses the same basic techniques was given by
  Bernard et al.~\cite{bernard_pi16}. They later also formalised the much stronger
  Lindemann--Weierstraß theorem~\cite{bernard_lw17}.
\<close>
lemma transcendental_i_pi: "\<not>algebraic (\<i> * pi)"
proof
  \<comment> \<open>Suppose $i\pi$ were algebraic.\<close>
  assume "algebraic (\<i> * pi)"
  \<comment> \<open>We obtain some nonzero integer polynomial that has $i\pi$ as a root. We can assume
      w.\,l.\,o.\,g.\ that the constant coefficient of this polynomial is nonzero.\<close>
  then obtain p
    where p: "poly (of_int_poly p) (\<i> * pi) = 0" "p \<noteq> 0" "poly.coeff p 0 \<noteq> 0"
    by (elim algebraicE'_nonzero) auto
  define n where "n = Polynomial.degree p"

  \<comment> \<open>We define the sequence of the roots of this polynomial:\<close>
  obtain root where "Polynomial.smult (Polynomial.lead_coeff (of_int_poly p))
                       (\<Prod>i<n. [:-root i :: complex, 1:]) = of_int_poly p"
    using complex_poly_decompose'[of "of_int_poly p"] unfolding n_def by auto
  note root = this [symmetric]

  \<comment> \<open>We note that $i\pi$ is, of course, among these roots.\<close>
  from p and root obtain idx where idx: "idx < n" "root idx = \<i> * pi"
    by (auto simp: poly_prod)

  \<comment> \<open>We now define a new polynomial \<open>P'\<close>, whose roots are all numbers that arise as a
      sum of any subset of roots of \<open>p\<close>. We also count all those subsets that sum up to 0
      and call their number \<open>A\<close>.\<close>
  define root' where "root' = (\<lambda>X. (\<Sum>j\<in>X. root j))"
  define P where "P = (\<lambda>i. \<Prod>X | X \<subseteq> {..<n} \<and> card X = i. [:-root' X, 1:])"
  define P' where "P' = (\<Prod>i\<in>{0<..n}. P i)"
  define A where "A = card {X\<in>Pow {..<n}. root' X = 0}"
  have [simp]: "P' \<noteq> 0" by (auto simp: P'_def P_def)

  \<comment> \<open>We give the name \<open>Roots'\<close> to those subsets that do not sum to zero and note that there
      is at least one, namely $\{i\pi\}$.\<close>
  define Roots' where "Roots' = {X. X \<subseteq> {..<n} \<and> root' X \<noteq> 0}"
  have [intro]: "finite Roots'" by (auto simp: Roots'_def)
  have "{idx} \<in> Roots'" using idx by (auto simp: Roots'_def root'_def)
  hence "Roots' \<noteq> {}" by auto
  hence card_Roots': "card Roots' > 0" by (auto simp: card_eq_0_iff)

  have P'_altdef: "P' = (\<Prod>X\<in>Pow {..<n} - {{}}. [:-root' X, 1:])"
  proof -
    have "P' = (\<Prod>(i, X)\<in>(SIGMA x:{0<..n}. {X. X \<subseteq> {..<n} \<and> card X = x}). [:- root' X, 1:])"
      unfolding P'_def P_def by (subst prod.Sigma) auto
    also have "\<dots> = (\<Prod>X\<in>Pow{..<n} - {{}}. [:- root' X, 1:])"
      using card_mono[of "{..<n}"]
      by (intro prod.reindex_bij_witness[of _ "\<lambda>X. (card X, X)" "\<lambda>(_, X). X"])
         (auto simp: case_prod_unfold card_gt_0_iff intro: finite_subset[of _ "{..<n}"])
    finally show ?thesis .
  qed

  \<comment> \<open>Clearly, @{term A} is nonzero, since the empty set sums to 0.\<close>
  have "A > 0"
  proof -
    have "{} \<in> {X\<in>Pow {..<n}. root' X = 0}"
      by (auto simp: root'_def)
    thus ?thesis by (auto simp: A_def card_gt_0_iff)
  qed

  \<comment> \<open>Since $e^{i\pi} + 1 = 0$, we know the following:\<close>
  have "0 = (\<Prod>i<n. exp (root i) + 1)"
    using idx by force
  \<comment> \<open>We rearrange this product of sums into a sum of products and collect all summands that are
      1 into a separate sum, which we call @{term A}:\<close>
  also have "\<dots> = (\<Sum>X\<in>Pow {..<n}. \<Prod>i\<in>X. exp (root i))"
    by (subst prod_add) auto
  also have "\<dots> = (\<Sum>X\<in>Pow {..<n}. exp (root' X))"
    by (intro sum.cong refl, subst exp_sum [symmetric])
       (auto simp: root'_def intro: finite_subset[of _ "{..<n}"])
  also have "Pow {..<n} = {X\<in>Pow {..<n}. root' X \<noteq> 0} \<union> {X\<in>Pow {..<n}. root' X = 0}"
    by auto
  also have "(\<Sum>X\<in>\<dots>. exp (root' X)) = (\<Sum>X | X \<subseteq> {..<n} \<and> root' X \<noteq> 0. exp (root' X)) +
                                       (\<Sum>X | X \<subseteq> {..<n} \<and> root' X = 0. exp (root' X))"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>X | X \<subseteq> {..<n} \<and> root' X = 0. exp (root' X)) = of_nat A"
    by (simp add: A_def)
  \<comment> \<open>Finally, we obtain the fact that the sum of $\exp(u)$ with $u$ ranging over all the non-zero
      roots of @{term P'} is a negative integer.\<close>
  finally have eq: "(\<Sum>X | X \<subseteq> {..<n} \<and> root' X \<noteq> 0. exp (root' X)) = -of_nat A"
    by (simp add: add_eq_0_iff2)

  \<comment> \<open>Next, we show that \<open>P'\<close> is a rational polynomial since it can be written as a symmetric
      polynomial expression (with rational coefficients) in the roots of \<open>p\<close>.\<close>
  define ratpolys where "ratpolys = {p::complex poly. \<forall>i. poly.coeff p i \<in> \<rat>}"
  have ratpolysI: "p \<in> ratpolys" if "\<And>i. poly.coeff p i \<in> \<rat>" for p
    using that by (auto simp: ratpolys_def)

  have "P' \<in> ratpolys"
  proof -
    define Pmv :: "nat \<Rightarrow> complex poly mpoly"
      where "Pmv = (\<lambda>i. \<Prod>X | X \<subseteq> {..<n} \<and> card X = i. Const ([:0,1:]) -
                          (\<Sum>i\<in>X. monom (Poly_Mapping.single i 1) 1))"
    define P'mv where "P'mv = (\<Prod>i\<in>{0<..n}. Pmv i)"
    have "insertion (\<lambda>i. [:root i:]) P'mv \<in> ratpolys"
    proof (rule symmetric_poly_of_roots_in_subring[where l = "\<lambda>x. [:x:]"])
      show "ring_closed ratpolys"
        by standard (auto simp: ratpolys_def coeff_mult)
      then interpret ring_closed ratpolys .
      show "\<forall>m. coeff P'mv m \<in> ratpolys"
        by (auto simp: P'mv_def Pmv_def coeff_monom when_def mpoly_coeff_Const coeff_pCons' ratpolysI
                 intro!: coeff_prod_closed minus_closed sum_closed uminus_closed)
      show "\<forall>i. [:poly.coeff (of_int_poly p) i:] \<in> ratpolys"
        by (intro ratpolysI allI) (auto simp: coeff_pCons')
      show "[:inverse (of_int (Polynomial.lead_coeff p)):] *
              [:of_int (Polynomial.lead_coeff p) :: complex:] = 1"
        using \<open>p \<noteq> 0\<close> by (auto intro!: poly_eqI simp: field_simps)
    next
      have "symmetric_mpoly {..<n} (Pmv k)" for k
        unfolding symmetric_mpoly_def
      proof safe
        fix \<pi> :: "nat \<Rightarrow> nat" assume \<pi>: "\<pi> permutes {..<n}"
        hence "mpoly_map_vars \<pi> (Pmv k) =
                 (\<Prod>X | X \<subseteq> {..<n} \<and> card X = k. Const [:0, 1:] -
                    (\<Sum>x\<in>X. MPoly_Type.monom (Poly_Mapping.single (\<pi> x) (Suc 0)) 1))"
          by (simp add: Pmv_def permutes_bij)
        also have "\<dots> = (\<Prod>X | X \<subseteq> {..<n} \<and> card X = k. Const [:0, 1:] -
                          (\<Sum>x\<in>\<pi>`X. MPoly_Type.monom (Poly_Mapping.single x (Suc 0)) 1))"
          using \<pi> by (subst sum.reindex) (auto simp: permutes_inj_on)
        also have "\<dots> = (\<Prod>X \<in> (\<lambda>X. \<pi>`X)`{X. X \<subseteq> {..<n} \<and> card X = k}. Const [:0, 1:] -
                          (\<Sum>x\<in>X. MPoly_Type.monom (Poly_Mapping.single x (Suc 0)) 1))"
          by (subst prod.reindex) (auto intro!: inj_on_image permutes_inj_on[OF \<pi>])
        also have "(\<lambda>X. \<pi>`X)`{X. X \<subseteq> {..<n} \<and> card X = k} = {X. X \<subseteq> \<pi> ` {..<n} \<and> card X = k}"
          using \<pi> by (subst image_image_fixed_card_subset) (auto simp: permutes_inj_on)
        also have "\<pi> ` {..<n} = {..<n}"
          by (intro permutes_image \<pi>)
        finally show "mpoly_map_vars \<pi> (Pmv k) = Pmv k" by (simp add: Pmv_def)
      qed
      thus "symmetric_mpoly {..<n} P'mv"
        unfolding P'mv_def by (intro symmetric_mpoly_prod) auto
    next
      show vars_P'mv: "vars P'mv \<subseteq> {..<n}"
        unfolding P'mv_def Pmv_def
        by (intro order.trans[OF vars_prod] UN_least order.trans[OF vars_diff]
                   Un_least order.trans[OF vars_sum] order.trans[OF vars_monom_subset]) auto
    qed (insert root, auto intro!: ratpolysI simp: coeff_pCons')
    also have "insertion (\<lambda>i. [:root i:]) (Pmv k) = P k" for k
      by (simp add: Pmv_def insertion_prod insertion_diff insertion_sum root'_def P_def
                    sum_to_poly del: insertion_monom)
      (* TODO: insertion_monom should not be a simp rule *)
    hence "insertion (\<lambda>i. [:root i:]) P'mv = P'"
      by (simp add: P'mv_def insertion_prod P'_def)
    finally show "P' \<in> ratpolys" .
  qed

  \<comment> \<open>We clear the denominators and remove all powers of $X$ from @{term P'} to obtain a new
      integer polynomial \<open>Q\<close>.\<close>
  define Q' where "Q' = (\<Prod>X\<in>Roots'. [:- root' X, 1:])"
  have "P' = (\<Prod>X\<in>Pow {..<n}-{{}}. [:-root' X, 1:])"
    by (simp add: P'_altdef)
  also have "Pow {..<n}-{{}} = Roots' \<union>
               {X. X \<in> Pow {..<n} - {{}} \<and> root' X = 0}" by (auto simp: root'_def Roots'_def)
  also have "(\<Prod>X\<in>\<dots>. [:-root' X, 1:]) =
               Q' * [:0, 1:] ^ card {X. X \<subseteq> {..<n} \<and> X \<noteq> {} \<and> root' X = 0}"
    by (subst prod.union_disjoint) (auto simp: Q'_def Roots'_def)
  also have "{X. X \<subseteq> {..<n} \<and> X \<noteq> {} \<and> root' X = 0} = {X. X \<subseteq> {..<n} \<and> root' X = 0} - {{}}"
    by auto
  also have "card \<dots> = A - 1"  unfolding A_def
    by (subst card_Diff_singleton) (auto simp: root'_def)
  finally have Q': "P' = Polynomial.monom 1 (A - 1) * Q'"
    by (simp add: Polynomial.monom_altdef)
  have degree_Q': "Polynomial.degree P' = Polynomial.degree Q' + (A - 1)"
    by (subst Q')
       (auto simp: Q'_def Roots'_def degree_mult_eq Polynomial.degree_monom_eq degree_prod_eq)

  have "\<forall>i. poly.coeff Q' i \<in> \<rat>"
  proof
    fix i :: nat
    have "poly.coeff Q' i = Polynomial.coeff P' (i + (A - 1))"
      by (simp add: Q' Polynomial.coeff_monom_mult)
    also have "\<dots> \<in> \<rat>" using \<open>P' \<in> ratpolys\<close> by (auto simp: ratpolys_def)
    finally show "poly.coeff Q' i \<in> \<rat>" .
  qed
  from ratpoly_to_intpoly[OF this] obtain c Q
    where [simp]: "c \<noteq> 0" and Q: "Q' = Polynomial.smult (inverse (of_nat c)) (of_int_poly Q)"
    by metis
  have [simp]: "Q \<noteq> 0" using Q Q' by auto
  have Q': "of_int_poly Q = Polynomial.smult (of_nat c) Q'"
    using Q by simp
  have degree_Q: "Polynomial.degree Q = Polynomial.degree Q'"
    by (subst Q) auto
  have "Polynomial.lead_coeff (of_int_poly Q :: complex poly) = c"
    by (subst Q') (simp_all add: degree_Q Q'_def lead_coeff_prod)
  hence lead_coeff_Q: "Polynomial.lead_coeff Q = int c"
    using of_int_eq_iff[of "Polynomial.lead_coeff Q" "of_nat c"] by (auto simp del: of_int_eq_iff)  
  have Q_decompose: "of_int_poly Q =
               Polynomial.smult (of_nat c) (\<Prod>X\<in>Roots'. [:- root' X, 1:])"
    by (subst Q') (auto simp: Q'_def lead_coeff_Q)
  have "poly (of_int_poly Q) (\<i> * pi) = 0"
    using \<open>{idx} \<in> Roots'\<close> \<open>finite Roots'\<close> idx 
    by (force simp: root'_def Q_decompose poly_prod)
  have degree_Q: "Polynomial.degree (of_int_poly Q :: complex poly) = card Roots'"
    by (subst Q') (auto simp: Q'_def degree_prod_eq)
  have "poly (of_int_poly Q) (0 :: complex) \<noteq> 0"
    by (subst Q') (auto simp: Q'_def Roots'_def poly_prod)
  hence [simp]: "poly Q 0 \<noteq> 0" by simp
  have [simp]: "poly (of_int_poly Q) (root' Y) = 0" if "Y \<in> Roots'" for Y
    using that \<open>finite Roots'\<close> by (auto simp: Q' Q'_def poly_prod)

  \<comment> \<open>We find some closed ball that contains all the roots of @{term Q}.\<close>
  define r where "r = Polynomial.degree Q"
  have "r > 0" using degree_Q card_Roots' by (auto simp: r_def)
  define Radius where "Radius = Max ((\<lambda>Y. norm (root' Y)) ` Roots')"
  have Radius: "norm (root' Y) \<le> Radius" if "Y \<in> Roots'" for Y
    using \<open>finite Roots'\<close> that by (auto simp: Radius_def)
  from Radius[of "{idx}"] have "Radius \<ge> pi"
    using idx by (auto simp: Roots'_def norm_mult root'_def)
  hence Radius_nonneg: "Radius \<ge> 0" and "Radius > 0" using pi_gt3 by linarith+

  \<comment> \<open>Since this ball is compact, @{term Q} is bounded on it. We obtain such a bound.\<close>
  have "compact (poly (of_int_poly Q :: complex poly) ` cball 0 Radius)"
    by (intro compact_continuous_image continuous_intros) auto
  then obtain Q_ub
    where Q_ub: "Q_ub > 0" 
                "\<And>u :: complex. u \<in> cball 0 Radius \<Longrightarrow> norm (poly (of_int_poly Q) u) \<le> Q_ub"
    by (auto dest!: compact_imp_bounded simp: bounded_pos cball_def)

  \<comment> \<open>Using this, define another upper bound that we will need later.\<close>
  define fp_ub
    where "fp_ub = (\<lambda>p. \<bar>c\<bar> ^ (r * p - 1) / fact (p - 1) * (Radius ^ (p - 1) * Q_ub ^ p))"
  have fp_ub_nonneg: "fp_ub p \<ge> 0" for p
    unfolding fp_ub_def using \<open>Radius \<ge> 0\<close> Q_ub
    by (intro mult_nonneg_nonneg divide_nonneg_pos zero_le_power) auto
  define C where "C = card Roots' * Radius * exp Radius"

  \<comment> \<open>We will now show that any sufficiently large prime number leads to
      \<open>C * fp_ub p \<ge> 1\<close>, from which we will then derive a contradiction.\<close>
  define primes_at_top where "primes_at_top = inf_class.inf sequentially (principal {p. prime p})"
  have "eventually (\<lambda>p. \<forall>x\<in>{nat \<bar>poly Q 0\<bar>, c, A}. p > x) sequentially"
    by (intro eventually_ball_finite ballI eventually_gt_at_top) auto
  hence "eventually (\<lambda>p. \<forall>x\<in>{nat \<bar>poly Q 0\<bar>, c, A}. p > x) primes_at_top"
    unfolding primes_at_top_def eventually_inf_principal by eventually_elim auto
  moreover have "eventually (\<lambda>p. prime p) primes_at_top"
    by (auto simp: primes_at_top_def eventually_inf_principal)
  ultimately have "eventually (\<lambda>p. C * fp_ub p \<ge> 1) primes_at_top"
  proof eventually_elim
    case (elim p)
    hence p: "prime p" "p > nat \<bar>poly Q 0\<bar>" "p > c" "p > A" by auto
    hence "p > 1" by (auto dest: prime_gt_1_nat)

    \<comment> \<open>We define the polynomial $f(X) = \frac{c^s}{(p-1)!} X^{p-1} Q(X)^p$, where $c$ is
        the leading coefficient of $Q$. We also define $F(X)$ to be the sum of all its
        derivatives.\<close>
    define s where "s = r * p - 1"
    define fp :: "complex poly"
      where "fp = Polynomial.smult (of_nat c ^ s / fact (p - 1))
                    (Polynomial.monom 1 (p - 1) * of_int_poly Q ^ p)"
    define Fp where "Fp = (\<Sum>i\<le>s+p. (pderiv ^^ i) fp)"
    define f F where "f = poly fp" and "F = poly Fp"
    have degree_fp: "Polynomial.degree fp = s + p" using degree_Q card_Roots' \<open>p > 1\<close>
      by (simp add: fp_def s_def degree_mult_eq degree_monom_eq
                    degree_power_eq r_def algebra_simps)

    \<comment> \<open>Using the same argument as in the case of the transcendence of $e$, we now 
        consider the function
        \[I(u) := e^u F(0) - F(u) = u \int\limits_0^1 e^{(1-t)x} f(tx)\,\textrm{d}t\]
        whose absolute value can be bounded with a standard ``maximum times length'' estimate
        using our upper bound on $f$. All of this can be reused from the proof for $e$, so
        there is not much to do here. In particular, we will look at $\sum I(x_i)$ with the
        $x_i$ ranging over the roots of $Q$ and bound this sum in two different ways.\<close>
    interpret lindemann_weierstrass_aux fp .
    have I_altdef: "I = (\<lambda>u. exp u * F 0 - F u)"
      by (intro ext) (simp add: I_def degree_fp F_def Fp_def poly_sum)

    \<comment> \<open>We show that @{term fp_ub} is indeed an upper bound for $f$.\<close>
    have fp_ub:  "norm (poly fp u) \<le> fp_ub p" if "u \<in> cball 0 Radius" for u
    proof -
      have "norm (poly fp u) = \<bar>c\<bar> ^ (r * p - 1) / fact (p - 1) * (norm u ^ (p - 1) *
                                 norm (poly (of_int_poly Q) u) ^ p)"
        by (simp add: fp_def f_def s_def norm_mult poly_monom norm_divide norm_power)
      also have "\<dots> \<le> fp_ub p"
        unfolding fp_ub_def using that Q_ub \<open>Radius \<ge> 0\<close>
        by (intro mult_left_mono[OF mult_mono] power_mono zero_le_power) auto
      finally show ?thesis .
    qed    

    \<comment> \<open>We now show that the following sum is an integer multiple of $p$. This argument again
        uses the fundamental theorem of symmetric functions, exploiting that the inner sums are
        symmetric over the roots of $Q$.\<close>
    have "(\<Sum>i=p..s+p. \<Sum>Y\<in>Roots'. poly ((pderiv ^^ i) fp) (root' Y)) / p \<in> \<int>"
    proof (subst sum_divide_distrib, intro Ints_sum[of "{a..b}" for a b])
      fix i assume i: "i \<in> {p..s+p}"
      then obtain roots' where roots': "distinct roots'" "set roots' = Roots'"
        using finite_distinct_list \<open>finite Roots'\<close> by metis
      define l where "l = length roots'"
      define fp' where "fp' = (pderiv ^^ i) fp"
      define d where "d = Polynomial.degree fp'"
      \<comment> \<open>We define a multivariate polynomial for the inner sum $\sum f(x_i)/p$ in order
          to show that it is indeed a symmetric function over the $x_i$.\<close>
      define R where "R = (smult (1 / of_nat p) (\<Sum>k\<le>d. \<Sum>i<l. smult (poly.coeff fp' k)
                             (monom (Poly_Mapping.single i k) (1 / of_int (c ^ k)))) :: complex mpoly)"

      \<comment> \<open>The $j$-th coefficient of the $i$-th derivative of $f$ are integer multiples
          of $c^j p$ since $i \geq p$.\<close>
      have integer: "poly.coeff fp' j / (of_nat c ^ j * of_nat p) \<in> \<int>" if "j \<le> d" for j
      proof -
        define fp'' where "fp'' = Polynomial.monom 1 (p - 1) * Q ^ p"
        define x
          where "x = c ^ s * poly.coeff ((pderiv ^^ i) (Polynomial.monom 1 (p - 1) * Q ^ p)) j"
        have "[:fact p:] dvd ([:fact i:] :: int poly)" using i
          by (auto intro: fact_dvd)
        also have "[:fact i:] dvd ((pderiv ^^ i) (Polynomial.monom 1 (p - 1) * Q ^ p))"
          by (rule fact_dvd_higher_pderiv)
        finally have "c ^ j * fact p dvd x" unfolding x_def of_nat_mult using that i
          by (intro mult_dvd_mono)
             (auto intro!: le_imp_power_dvd simp: s_def d_def fp'_def degree_higher_pderiv degree_fp)
        hence "of_int x / (of_int (c ^ j * fact p) :: complex) \<in> \<int>"
          by (intro of_int_divide_in_Ints) auto
        also have "of_int x / (of_int (c ^ j * fact p) :: complex) =
                     poly.coeff fp' j / (of_nat c ^ j * of_nat p)" using \<open>p > 1\<close>
          by (auto simp: fact_reduce[of p] fp'_def fp_def higher_pderiv_smult x_def field_simps
                   simp flip: coeff_of_int_poly higher_pderiv_of_int_poly)
        finally show ?thesis .
      qed

      \<comment> \<open>Evaluating $R$ yields is an integer since it is symmetric.\<close>
      have "insertion (\<lambda>i. c * root' (roots' ! i)) R \<in> \<int>"
      proof (intro symmetric_poly_of_roots_in_subring_monic allI)
        define Q' where "Q' = of_int_poly Q \<circ>\<^sub>p [:0, 1 / of_nat c :: complex:]"
        show "symmetric_mpoly {..<l} R" unfolding R_def
          by (intro symmetric_mpoly_smult symmetric_mpoly_sum[of "{..d}"] symmetric_mpoly_symmetric_sum)
             (simp_all add: mpoly_map_vars_monom permutes_bij permutep_single bij_imp_bij_inv permutes_inv_inv)
        show "MPoly_Type.coeff R m \<in> \<int>" for m unfolding R_def coeff_sum coeff_smult sum_distrib_left
          using integer by (auto simp: R_def coeff_monom when_def intro!: Ints_sum)
        show "vars R \<subseteq> {..<l}" unfolding R_def
          by (intro order.trans[OF vars_smult] order.trans[OF vars_sum] UN_least
                    order.trans[OF vars_monom_subset]) auto
        show "ring_closed \<int>" by standard auto
  
        have "(\<Prod>i<l. [:- (of_nat c * root' (roots' ! i)), 1:]) =
                (\<Prod>Y\<leftarrow>roots'. [:- (of_nat c * root' Y), 1:])"
          by (subst prod_list_prod_nth) (auto simp: atLeast0LessThan l_def)
        also have "\<dots> = (\<Prod>Y\<in>Roots'. [:- (of_nat c * root' Y), 1:])"
          using roots' by (subst prod.distinct_set_conv_list [symmetric]) auto
        also have "\<dots> = (\<Prod>Y\<in>Roots'. Polynomial.smult (of_nat c) ([:-root' Y, 1:])) \<circ>\<^sub>p [:0, 1 / c:]"
          by (simp add: pcompose_prod pcompose_pCons)
        also have "(\<Prod>Y\<in>Roots'. Polynomial.smult (of_nat c) ([:-root' Y, 1:])) =
                     Polynomial.smult (of_nat c ^ card Roots') (\<Prod>Y\<in>Roots'. [:-root' Y, 1:])"
          by (subst prod_smult) auto
        also have "\<dots> = Polynomial.smult (of_nat c ^ (card Roots' - 1))
                          (Polynomial.smult c (\<Prod>Y\<in>Roots'. [:-root' Y, 1:]))"
          using \<open>finite Roots'\<close> and \<open>Roots' \<noteq> {}\<close>
          by (subst power_diff) (auto simp: Suc_le_eq card_gt_0_iff)
        also have "Polynomial.smult c (\<Prod>Y\<in>Roots'. [:-root' Y, 1:]) = of_int_poly Q"
          using Q_decompose by simp
        finally show "Polynomial.smult (of_nat c ^ (card Roots' - 1)) Q' =
                        (\<Prod>i<l. [:- (of_nat c * root' (roots' ! i)), 1:])"
          by (simp add: pcompose_smult Q'_def)
        fix i :: nat
        show "poly.coeff (Polynomial.smult (of_nat c ^ (card Roots' - 1)) Q') i \<in> \<int>"
        proof (cases i "Polynomial.degree Q" rule: linorder_cases)
          case greater
          thus ?thesis by (auto simp: Q'_def coeff_pcompose_linear coeff_eq_0)
        next
          case equal
          thus ?thesis using \<open>Roots' \<noteq> {}\<close> degree_Q card_Roots' lead_coeff_Q
            by (auto simp: Q'_def coeff_pcompose_linear lead_coeff_Q power_divide power_diff)
        next
          case less
          have "poly.coeff (Polynomial.smult (of_nat c ^ (card Roots' - 1)) Q') i =
                  of_int (poly.coeff Q i) * (of_int (c ^ (card Roots' - 1)) / of_int (c ^ i))"
            by (auto simp: Q'_def coeff_pcompose_linear power_divide)
          also have "\<dots> \<in> \<int>" using less degree_Q
            by (intro Ints_mult of_int_divide_in_Ints) (auto intro!: le_imp_power_dvd)
          finally show ?thesis .
        qed
      qed auto
      \<comment> \<open>Moreover, by definition, evaluating @{term R} gives us $\sum f(x_i)/p$.\<close>
      also have "insertion (\<lambda>i. c * root' (roots' ! i)) R =
                   (\<Sum>Y\<leftarrow>roots'. poly fp' (root' Y)) / of_nat p"
        by (simp add: insertion_sum R_def poly_altdef d_def sum_list_sum_nth atLeast0LessThan
                    l_def power_mult_distrib algebra_simps 
                    sum.swap[of _ "{..Polynomial.degree fp'}"] del: insertion_monom)
      also have "\<dots> = (\<Sum>Y\<in>Roots'. poly ((pderiv ^^ i) fp) (root' Y)) / of_nat p"
        using roots' by (subst sum_list_distinct_conv_sum_set) (auto simp: fp'_def poly_pcompose)
      finally show "\<dots> \<in> \<int>" .
    qed
    then obtain K where K: "(\<Sum>i=p..s+p. \<Sum>Y\<in>Roots'. 
                               poly ((pderiv ^^ i) fp) (root' Y)) = of_int K * p"
      using \<open>p > 1\<close> by (auto elim!: Ints_cases simp: field_simps)

    \<comment> \<open>Next, we show that $F(0)$ is an integer and coprime to $p$.\<close>
    obtain F0 :: int where F0: "F 0 = of_int F0" "coprime (int p) F0"
    proof -
      have "(\<Sum>i=p..s + p. poly ((pderiv ^^ i) fp) 0) / of_nat p \<in> \<int>"
        unfolding sum_divide_distrib
      proof (intro Ints_sum)
        fix i assume i: "i \<in> {p..s+p}"
        hence "fact p dvd poly ((pderiv ^^ i) ([:0, 1:] ^ (p - 1) * Q ^ p)) 0"
          by (intro fact_dvd_poly_higher_pderiv_aux') auto
        then obtain k where k: "poly ((pderiv ^^ i) ([:0, 1:] ^ (p - 1) * Q ^ p)) 0 = k * fact p"
          by auto
  
        have "(pderiv ^^ i) fp = Polynomial.smult (of_nat c ^ s / fact (p - 1))
                (of_int_poly ((pderiv ^^ i) ([:0, 1:] ^ (p - 1) * Q ^ p)))"
          by (simp add: fp_def higher_pderiv_smult Polynomial.monom_altdef
                   flip: higher_pderiv_of_int_poly)
        also have "poly \<dots> 0 / of_nat p = of_int (c ^ s * k)"
          using k \<open>p > 1\<close> by (simp add: fact_reduce[of p])
        also have "\<dots> \<in> \<int>" by simp
        finally show "poly ((pderiv ^^ i) fp) 0 / of_nat p \<in> \<int>" .
      qed
      then obtain S where S: "(\<Sum>i=p..s + p. poly ((pderiv ^^ i) fp) 0) = of_int S * p"
        using \<open>p > 1\<close> by (auto elim!: Ints_cases simp: field_simps)
  
      have "F 0 = (\<Sum>i\<le>s + p. poly ((pderiv ^^ i) fp) 0)"
        by (auto simp: F_def Fp_def poly_sum)
      also have "\<dots> = (\<Sum>i\<in>insert (p - 1) {p..s + p}. poly ((pderiv ^^ i) fp) 0)"
      proof (intro sum.mono_neutral_right ballI)
        fix i assume i: "i \<in> {..s + p} - insert (p - 1) {p..s + p}"
        hence "i < p - 1" by auto
        have "Polynomial.monom 1 (p - 1) dvd fp"
          by (auto simp: fp_def intro: dvd_smult)
        with i show "poly ((pderiv ^^ i) fp) 0 = 0"
          by (intro poly_higher_pderiv_aux1'[of _ "p - 1"]) (auto simp: Polynomial.monom_altdef)
      qed auto
      also have "\<dots> = poly ((pderiv ^^ (p - 1)) fp) 0 + of_int S * of_nat p"
        using \<open>p > 1\<close> S by (subst sum.insert) auto
      also have "poly ((pderiv ^^ (p - 1)) fp) 0 = of_int (c ^ s * poly Q 0 ^ p)"
        using poly_higher_pderiv_aux2[of "p - 1" 0 "of_int_poly Q ^ p :: complex poly"]
        by (simp add: fp_def higher_pderiv_smult Polynomial.monom_altdef)
      finally have "F 0 = of_int (S * int p + c ^ s * poly Q 0 ^ p)"
        by simp
      moreover have "coprime p c" "coprime (int p) (poly Q 0)"
        using p by (auto intro!: prime_imp_coprime dest: dvd_imp_le_int[rotated])
      hence "coprime (int p) (c ^ s * poly Q 0 ^ p)"
        by auto
      hence "coprime (int p) (S * int p + c ^ s * poly Q 0 ^ p)"
        unfolding coprime_iff_gcd_eq_1 gcd_add_mult by auto
      ultimately show ?thesis using that[of "S * int p + c ^ s * poly Q 0 ^ p"] by blast
    qed

    \<comment> \<open>Putting everything together, we have shown that $\sum I(x_i)$ is an integer coprime
        to $p$, and therefore a nonzero integer, and therefore has an absolute value of at least 1.\<close>
    have "(\<Sum>Y\<in>Roots'. I (root' Y)) = F 0 * (\<Sum>Y\<in>Roots'. exp (root' Y)) - (\<Sum>Y\<in>Roots'. F (root' Y))"
      by (simp add: I_altdef sum_subtractf sum_distrib_left sum_distrib_right algebra_simps)
    also have "\<dots> = -(of_int (F0 * int A) +
                      (\<Sum>i\<le>s+p. \<Sum>Y\<in>Roots'. poly ((pderiv ^^ i) fp) (root' Y)))"
      using F0 by (simp add: Roots'_def eq F_def Fp_def poly_sum sum.swap[of _ "{..s+p}"])
    also have "(\<Sum>i\<le>s+p. \<Sum>Y\<in>Roots'. poly ((pderiv ^^ i) fp) (root' Y)) =
                 (\<Sum>i=p..s+p. \<Sum>Y\<in>Roots'. poly ((pderiv ^^ i) fp) (root' Y))"
    proof (intro sum.mono_neutral_right ballI sum.neutral)
      fix i Y assume i: "i \<in> {..s+p} - {p..s+p}" and Y: "Y \<in> Roots'"
      have "[:-root' Y, 1:] ^ p dvd of_int_poly Q ^ p"
        by (intro dvd_power_same) (auto simp: dvd_iff_poly_eq_0 Y)
      hence "[:-root' Y, 1:] ^ p dvd fp"
        by (auto simp: fp_def intro!: dvd_smult)
      thus "poly ((pderiv ^^ i) fp) (root' Y) = 0"
        using i by (intro poly_higher_pderiv_aux1') auto
    qed auto
    also have "\<dots> = of_int (K * int p)" using K by simp
    finally have "(\<Sum>Y\<in>Roots'. I (root' Y)) = -of_int (K * int p + F0 * int A)"
      by simp
    moreover have "coprime p A"
      using p \<open>A > 0\<close> by (intro prime_imp_coprime) (auto dest!: dvd_imp_le)
    hence "coprime (int p) (F0 * int A)"
      using F0 by auto
    hence "coprime (int p) (K * int p + F0 * int A)"
      using F0 unfolding coprime_iff_gcd_eq_1 gcd_add_mult by auto
    hence "K * int p + F0 * int A \<noteq> 0"
      using p by (intro notI) auto
    hence "norm (-of_int (K * int p + F0 * int A) :: complex) \<ge> 1"
      unfolding norm_minus_cancel norm_of_int by linarith
    ultimately have "1 \<le> norm (\<Sum>Y\<in>Roots'. I (root' Y))" by metis

    \<comment> \<open>The M--L bound on the integral gives us an upper bound:\<close>
    also have "norm (\<Sum>Y\<in>Roots'. I (root' Y)) \<le>
                 (\<Sum>Y\<in>Roots'. norm (root' Y) * exp (norm (root' Y)) * fp_ub p)"
    proof (intro sum_norm_le lindemann_weierstrass_integral_bound fp_ub fp_ub_nonneg)
      fix Y u assume *: "Y \<in> Roots'" "u \<in> closed_segment 0 (root' Y)"
      hence "closed_segment 0 (root' Y) \<subseteq> cball 0 Radius"
        using \<open>Radius \<ge> 0\<close> Radius[of Y] by (intro closed_segment_subset) auto
      with * show "u \<in> cball 0 Radius" by auto
    qed
    also have "\<dots> \<le> (\<Sum>Y\<in>Roots'. Radius * exp (Radius) * fp_ub p)"
      using Radius by (intro sum_mono mult_right_mono mult_mono fp_ub_nonneg \<open>Radius \<ge> 0\<close>) auto
    also have "\<dots> = C * fp_ub p" by (simp add: C_def)
    finally show "1 \<le> C * fp_ub p" .
  qed

  \<comment> \<open>It now only remains to show that this inequality is inconsistent for large $p$.
      This is obvious, since the upper bound is an exponential divided by a factorial and 
      therefore clearly tends to zero.\<close>
  have "(\<lambda>p. C * fp_ub p) \<in> \<Theta>(\<lambda>p. (C / (Radius * \<bar>c\<bar>)) * (p / 2 ^ p) *
                                     ((2 * \<bar>c\<bar> ^ r * Radius * Q_ub) ^ p / fact p))"
    (is "_ \<in> \<Theta>(?f)") using degree_Q card_Roots' \<open>Radius > 0\<close>
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: fact_reduce power_mult [symmetric] r_def
                   fp_ub_def power_diff power_mult_distrib)
  also have "?f \<in> o(\<lambda>p. 1 * 1 * 1)"
  proof (intro landau_o.big_small_mult landau_o.big_mult)
    have "(\<lambda>x. (real_of_int (2 * \<bar>c\<bar> ^ r) * Radius * Q_ub) ^ x / fact x) \<longlonglongrightarrow> 0"
      by (intro power_over_fact_tendsto_0)
    thus "(\<lambda>x. (real_of_int (2 * \<bar>c\<bar> ^ r) * Radius * Q_ub) ^ x / fact x) \<in> o(\<lambda>x. 1)"
      by (intro smalloI_tendsto) auto
  qed real_asymp+
  finally have "(\<lambda>p. C * fp_ub p) \<in> o(\<lambda>_. 1)" by simp
  from smalloD_tendsto[OF this] have "(\<lambda>p. C * fp_ub p) \<longlonglongrightarrow> 0" by simp
  hence "eventually (\<lambda>p. C * fp_ub p < 1) at_top"
    by (intro order_tendstoD) auto
  hence "eventually (\<lambda>p. C * fp_ub p < 1) primes_at_top"
    unfolding primes_at_top_def eventually_inf_principal by eventually_elim auto
  moreover note \<open>eventually (\<lambda>p. C * fp_ub p \<ge> 1) primes_at_top\<close>
  \<comment> \<open>We therefore have a contradiction for any sufficiently large prime.\<close>
  ultimately have "eventually (\<lambda>p. False) primes_at_top"
    by eventually_elim auto

  \<comment> \<open>Since sufficiently large primes always exist, this concludes the theorem.\<close>
  moreover have "frequently (\<lambda>p. prime p) sequentially"
    using primes_infinite by (simp add: cofinite_eq_sequentially[symmetric] Inf_many_def)
  ultimately show False
    by (auto simp: frequently_def eventually_inf_principal primes_at_top_def)
qed

theorem transcendental_pi: "\<not>algebraic pi"
  using transcendental_i_pi by (simp add: algebraic_times_i_iff)

end