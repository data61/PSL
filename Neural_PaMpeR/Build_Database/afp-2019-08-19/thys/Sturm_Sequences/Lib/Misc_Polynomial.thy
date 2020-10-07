(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Misc_Polynomial
imports "HOL-Computational_Algebra.Polynomial" "HOL-Computational_Algebra.Polynomial_Factorial"
begin

subsection \<open>Analysis\<close>

lemma fun_eq_in_ivl:
  assumes "a \<le> b" "\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> eventually (\<lambda>\<xi>. f \<xi> = f x) (at x)"
  shows "f a = f b"
proof (rule connected_local_const)
  show "connected {a..b}" "a \<in> {a..b}" "b \<in> {a..b}" using \<open>a \<le> b\<close> by (auto intro: connected_Icc)
  show "\<forall>aa\<in>{a..b}. eventually (\<lambda>b. f aa = f b) (at aa within {a..b})"
  proof
    fix x assume "x \<in> {a..b}"
    with assms(2)[rule_format, of x]
    show "eventually (\<lambda>b. f x = f b) (at x within {a..b})"
      by (auto simp: eventually_at_filter elim: eventually_mono)
  qed
qed

subsection \<open>Polynomials\<close>

subsubsection \<open>General simplification lemmas\<close>

lemma pderiv_div:
  assumes [simp]: "q dvd p" "q \<noteq> 0"
  shows "pderiv (p div q) = (q * pderiv p - p * pderiv q) div (q * q)"
        "q*q dvd (q * pderiv p - p * pderiv q)"
proof-
  from assms obtain r where "p = q * r" unfolding dvd_def by blast
  hence "q * pderiv p - p * pderiv q = (q * q) * pderiv r"
      by (simp add: algebra_simps pderiv_mult)
  thus "q*q dvd (q * pderiv p - p * pderiv q)" by simp
  note 0 = pderiv_mult[of q "p div q"]
  have 1: "q * (p div q) = p" 
    by (metis assms(1) assms(2) dvd_def nonzero_mult_div_cancel_left)
  have f1: "pderiv (p div q) * (q * q) div (q * q) = pderiv (p div q)"
    by simp
  have f2: "pderiv p = q * pderiv (p div q) + p div q * pderiv q"
    by (metis 0 1) 
  have "p * pderiv q = pderiv q * (q * (p div q))"
    by (metis 1 mult.commute) 
  then have "p * pderiv q = q * (p div q * pderiv q)"
    by fastforce
  then have "q * pderiv p - p * pderiv q = q * (q * pderiv (p div q))"
    using f2 by (metis add_diff_cancel_right' distrib_left)
  then show "pderiv (p div q) = (q * pderiv p - p * pderiv q) div (q * q)"
    using f1 by (metis mult.commute mult.left_commute)
qed


subsubsection \<open>Divisibility of polynomials\<close>

text \<open>
  Two polynomials that are coprime have no common roots.
\<close>
lemma coprime_imp_no_common_roots:
  "\<not> (poly p x = 0 \<and> poly q x = 0)" if "coprime p q"
     for x :: "'a :: field"
proof clarify
  assume "poly p x = 0" "poly q x = 0"
  then have "[:-x, 1:] dvd p" "[:-x, 1:] dvd q"
    by (simp_all add: poly_eq_0_iff_dvd)
  with that have "is_unit [:-x, 1:]"
    by (rule coprime_common_divisor)
  then show False
    by (auto simp add: is_unit_pCons_iff)
qed

lemma poly_div:
  assumes "poly q x \<noteq> 0" and "(q::'a :: field poly) dvd p"
  shows "poly (p div q) x = poly p x / poly q x"
proof-
  from assms have [simp]: "q \<noteq> 0" by force
  have "poly q x * poly (p div q) x = poly (q * (p div q)) x" by simp
  also have "q * (p div q) = p"
      using assms by (simp add: div_mult_swap)
  finally show "poly (p div q) x = poly p x / poly q x"
      using assms by (simp add: field_simps)
qed

(* TODO: make this less ugly *)
lemma poly_div_gcd_squarefree_aux:
  assumes "pderiv (p::('a::{field_char_0,euclidean_ring_gcd}) poly) \<noteq> 0"
  defines "d \<equiv> gcd p (pderiv p)"
  shows "coprime (p div d) (pderiv (p div d))" and
        "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0"
proof -
  obtain r s where "bezout_coefficients p (pderiv p) = (r, s)"
    by (auto simp add: prod_eq_iff)
  then have "r * p + s * pderiv p = gcd p (pderiv p)"
    by (rule bezout_coefficients)
  then have rs: "d = r * p + s * pderiv p"
    by (simp add: d_def)
  define t where "t = p div d"
  define p' where [simp]: "p' = pderiv p"
  define d' where [simp]: "d' = pderiv d"
  define u where "u = p' div d"
  have A: "p = t * d" and B: "p' = u * d"
    by (simp_all add: t_def u_def d_def algebra_simps)
  from poly_squarefree_decomp[OF assms(1) A B[unfolded p'_def] rs]
    show "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0" by (auto simp: t_def)

  from rs have C: "s*t*d' = d * (1 - r*t - s*pderiv t)"
      by (simp add: A B algebra_simps pderiv_mult)
  from assms have [simp]: "p \<noteq> 0" "d \<noteq> 0" "t \<noteq> 0"
      by (force, force, subst (asm) A, force)

  have "\<And>x. \<lbrakk>x dvd t; x dvd (pderiv t)\<rbrakk> \<Longrightarrow> x dvd 1"
  proof -
    fix x assume "x dvd t" "x dvd (pderiv t)"
    then obtain v w where vw:
        "t = x*v" "pderiv t = x*w" unfolding dvd_def by blast
    define x' v' where [simp]: "x' = pderiv x" and [simp]: "v' = pderiv v"
    from vw have "x*v' + v*x' = x*w" by (simp add: pderiv_mult)
    hence "v*x' = x*(w - v')" by (simp add: algebra_simps)
    hence "x dvd v*pderiv x" by simp
    then obtain y where y: "v*x' = x*y" unfolding dvd_def by force
    from \<open>t \<noteq> 0\<close> and vw have "x \<noteq> 0" by simp

    have x_pow_n_dvd_d: "\<And>n. x^n dvd d"
    proof-
      fix n show "x ^ n dvd d"
      proof (induction n, simp, rename_tac n, case_tac n)
        fix n assume "n = (0::nat)"
        from vw and C have "d = x*(d*r*v + d*s*w + s*v*d')"
            by (simp add: algebra_simps)
        with \<open>n = 0\<close> show "x^Suc n dvd d" by (force intro: dvdI)
      next
        fix n n' assume IH: "x^n dvd d" and "n = Suc n'"
        hence [simp]: "Suc n' = n" "x * x^n' = x^n" by simp_all
        define c :: "'a poly" where "c = [:of_nat n:]"
        from pderiv_power_Suc[of x n']
            have [simp]: "pderiv (x^n) = c*x^n' * x'" unfolding c_def
            by simp

        from IH obtain z where d: "d = x^n * z" unfolding dvd_def by blast
        define z' where [simp]: "z' = pderiv z"
        from d \<open>d \<noteq> 0\<close> have "x^n \<noteq> 0" "z \<noteq> 0" by force+
        from C d have "x^n*z = z*r*v*x^Suc n + z*s*c*x^n*(v*x') +
                          s*v*z'*x^Suc n + s*z*(v*x')*x^n + s*z*v'*x^Suc n"
            by (simp add: algebra_simps vw pderiv_mult)
        also have "... = x^n*x * (z*r*v + z*s*c*y + s*v*z' + s*z*y + s*z*v')"
            by (simp only: y, simp add: algebra_simps)
        finally have "z = x*(z*r*v+z*s*c*y+s*v*z'+s*z*y+s*z*v')"
             using \<open>x^n \<noteq> 0\<close> by force
        hence "x dvd z" by (metis dvd_triv_left)
        with d show "x^Suc n dvd d" by simp
     qed
   qed

   have "degree x = 0"
   proof (cases "degree x", simp)
     case (Suc n)
       hence "x \<noteq> 0" by auto
       with Suc have "degree (x ^ (Suc (degree d))) > degree d"
           by (subst degree_power_eq, simp_all)
       moreover from x_pow_n_dvd_d[of "Suc (degree d)"] and \<open>d \<noteq> 0\<close>
           have "degree (x^Suc (degree d)) \<le> degree d"
                by (simp add: dvd_imp_degree_le)
       ultimately show ?thesis by simp
    qed
    then obtain c where [simp]: "x = [:c:]" by (cases x, simp split: if_split_asm)
    moreover from \<open>x \<noteq> 0\<close> have "c \<noteq> 0" by simp
    ultimately show "x dvd 1" using dvdI[of 1 x "[:inverse c:]"]
      by simp
  qed

  then show "coprime t (pderiv t)"
    by (rule coprimeI)
qed

lemma normalize_field:
  "normalize (x :: 'a :: {field,normalization_semidom}) = (if x = 0 then 0 else 1)"
  by (auto simp: is_unit_normalize dvd_field_iff)

lemma normalize_field_eq_1 [simp]:
  "x \<noteq> 0 \<Longrightarrow> normalize (x :: 'a :: {field,normalization_semidom}) = 1"
  by (simp add: normalize_field)

lemma unit_factor_field [simp]:
  "unit_factor (x :: 'a :: {field,normalization_semidom}) = x"
  by (cases "x = 0") (auto simp: is_unit_unit_factor dvd_field_iff)

text \<open>
  Dividing a polynomial by its gcd with its derivative yields
  a squarefree polynomial with the same roots.
\<close>
lemma poly_div_gcd_squarefree:
  assumes "(p :: ('a::{field_char_0,euclidean_ring_gcd}) poly) \<noteq> 0"
  defines "d \<equiv> gcd p (pderiv p)"
  shows "coprime (p div d) (pderiv (p div d))" (is ?A) and
        "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0" (is "\<And>x. ?B x")
proof-
  have "?A \<and> (\<forall>x. ?B x)"
  proof (cases "pderiv p = 0")
    case False
      from poly_div_gcd_squarefree_aux[OF this] show ?thesis
          unfolding d_def by auto
  next
    case True
      then obtain c where [simp]: "p = [:c:]" using pderiv_iszero by blast
      from assms(1) have "c \<noteq> 0" by simp
      from True have "d = smult (inverse c) p"
        by (simp add: d_def normalize_poly_def map_poly_pCons field_simps)
      with \<open>p \<noteq> 0\<close> \<open>c \<noteq> 0\<close> have "p div d = [:c:]"
        by (simp add: pCons_one)
      with \<open>c \<noteq> 0\<close> show ?thesis
        by (simp add: normalize_const_poly is_unit_triv)
  qed
  thus ?A and "\<And>x. ?B x" by simp_all
qed



subsubsection \<open>Sign changes of a polynomial\<close>

text \<open>
  If a polynomial has different signs at two points, it has a root inbetween.
\<close>
lemma poly_different_sign_imp_root:
  assumes "a < b" and "sgn (poly p a) \<noteq> sgn (poly p (b::real))"
  shows "\<exists>x. a \<le> x \<and> x \<le> b \<and> poly p x = 0"
proof (cases "poly p a = 0 \<or> poly p b = 0")
  case True
    thus ?thesis using assms(1)
        by (elim disjE, rule_tac exI[of _ a], simp,
                        rule_tac exI[of _ b], simp)
next
  case False
    hence [simp]: "poly p a \<noteq> 0" "poly p b \<noteq> 0" by simp_all
    show ?thesis
    proof (cases "poly p a < 0")
      case True
        hence "sgn (poly p a) = -1" by simp
        with assms True have "poly p b > 0"
            by (auto simp: sgn_real_def split: if_split_asm)
        from poly_IVT_pos[OF \<open>a < b\<close> True this] guess x ..
        thus ?thesis by (intro exI[of _ x], simp)
    next
      case False
        hence "poly p a > 0" by (simp add: not_less less_eq_real_def)
        hence "sgn (poly p a) = 1"  by simp
        with assms False have "poly p b < 0"
            by (auto simp: sgn_real_def not_less
                           less_eq_real_def split: if_split_asm)
        from poly_IVT_neg[OF \<open>a < b\<close> \<open>poly p a > 0\<close> this] guess x ..
        thus ?thesis by (intro exI[of _ x], simp)
    qed
qed

lemma poly_different_sign_imp_root':
  assumes "sgn (poly p a) \<noteq> sgn (poly p (b::real))"
  shows "\<exists>x. poly p x = 0"
using assms by (cases "a < b", auto dest!: poly_different_sign_imp_root
                                    simp: less_eq_real_def not_less)


lemma no_roots_inbetween_imp_same_sign:
  assumes "a < b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> (0::real)"
  shows "sgn (poly p a) = sgn (poly p b)"
  using poly_different_sign_imp_root assms by auto



subsubsection \<open>Limits of polynomials\<close>

lemma poly_neighbourhood_without_roots:
  assumes "(p :: real poly) \<noteq> 0"
  shows "eventually (\<lambda>x. poly p x \<noteq> 0) (at x\<^sub>0)"
proof-
  {
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    have fin: "finite {x. \<bar>x-x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}"
        using poly_roots_finite[OF assms] by simp
    with \<open>\<epsilon> > 0\<close>have "\<exists>\<delta>>0. \<delta>\<le>\<epsilon> \<and> (\<forall>x. \<bar>x-x\<^sub>0\<bar> < \<delta> \<and> x \<noteq> x\<^sub>0 \<longrightarrow> poly p x \<noteq> 0)"
    proof (induction "card {x. \<bar>x-x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}"
           arbitrary: \<epsilon> rule: less_induct)
    case (less \<epsilon>)
    let ?A = "{x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}"
    show ?case
      proof (cases "card ?A")
      case 0
        hence "?A = {}" using less by auto
        thus ?thesis using less(2) by (rule_tac exI[of _ \<epsilon>], auto)
      next
      case (Suc _)
        with less(3) have "{x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0} \<noteq> {}" by force
        then obtain x where x_props: "\<bar>x - x\<^sub>0\<bar> < \<epsilon>" "x \<noteq> x\<^sub>0" "poly p x = 0" by blast
        define \<epsilon>' where "\<epsilon>' = \<bar>x - x\<^sub>0\<bar> / 2"
        have "\<epsilon>' > 0" "\<epsilon>' < \<epsilon>" unfolding \<epsilon>'_def using x_props by simp_all
        from x_props(1,2) and \<open>\<epsilon> > 0\<close>
            have "x \<notin> {x'. \<bar>x' - x\<^sub>0\<bar> < \<epsilon>' \<and> x' \<noteq> x\<^sub>0 \<and> poly p x' = 0}" (is "_ \<notin> ?B")
            by (auto simp: \<epsilon>'_def)
        moreover from x_props
            have "x \<in> {x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}" by blast
        ultimately have "?B \<subset> ?A" by auto
        hence "card ?B < card ?A" "finite ?B"
            by (rule psubset_card_mono[OF less(3)],
                blast intro: finite_subset[OF _ less(3)])
        from less(1)[OF this(1) \<open>\<epsilon>' > 0\<close> this(2)]
            show ?thesis using \<open>\<epsilon>' < \<epsilon>\<close> by force
      qed
    qed
  }
  from this[of "1"]
    show ?thesis by (auto simp: eventually_at dist_real_def)
qed


lemma poly_neighbourhood_same_sign:
  assumes "poly p (x\<^sub>0 :: real) \<noteq> 0"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^sub>0)) (at x\<^sub>0)"
proof -
  have cont: "isCont (\<lambda>x. sgn (poly p x)) x\<^sub>0"
      by (rule isCont_sgn, rule poly_isCont, rule assms)
  then have "eventually (\<lambda>x. \<bar>sgn (poly p x) - sgn (poly p x\<^sub>0)\<bar> < 1) (at x\<^sub>0)"
      by (auto simp: isCont_def tendsto_iff dist_real_def)
  then show ?thesis
    by (rule eventually_mono) (simp add: sgn_real_def split: if_split_asm)
qed

lemma poly_lhopital:
  assumes "poly p (x::real) = 0" "poly q x = 0" "q \<noteq> 0"
  assumes "(\<lambda>x. poly (pderiv p) x / poly (pderiv q) x) \<midarrow>x\<rightarrow> y"
  shows "(\<lambda>x. poly p x / poly q x) \<midarrow>x\<rightarrow> y"
using assms
proof (rule_tac lhopital)
  have "isCont (poly p) x" "isCont (poly q) x" by simp_all
  with assms(1,2) show "poly p \<midarrow>x\<rightarrow> 0" "poly q \<midarrow>x\<rightarrow> 0"
       by (simp_all add: isCont_def)
  from \<open>q \<noteq> 0\<close> and \<open>poly q x = 0\<close> have "pderiv q \<noteq> 0"
      by (auto dest: pderiv_iszero)
  from poly_neighbourhood_without_roots[OF this]
      show "eventually (\<lambda>x. poly (pderiv q) x \<noteq> 0) (at x)" .
qed (auto intro: poly_DERIV poly_neighbourhood_without_roots)


lemma poly_roots_bounds:
  assumes "p \<noteq> 0"
  obtains l u
  where "l \<le> (u :: real)"
    and "poly p l \<noteq> 0"
    and "poly p u \<noteq> 0"
    and "{x. x > l \<and> x \<le> u \<and> poly p x = 0 } = {x. poly p x = 0}"
    and "\<And>x. x \<le> l \<Longrightarrow> sgn (poly p x) = sgn (poly p l)"
    and "\<And>x. x \<ge> u \<Longrightarrow> sgn (poly p x) = sgn (poly p u)"
proof
  from assms have "finite {x. poly p x = 0}" (is "finite ?roots")
      using poly_roots_finite by fast
  let ?roots' = "insert 0 ?roots"

  define l where "l = Min ?roots' - 1"
  define u where "u = Max ?roots' + 1"

  from \<open>finite ?roots\<close> have A: "finite ?roots'"  by auto
  from Min_le[OF this, of 0] and Max_ge[OF this, of 0]
      show "l \<le>  u" by (simp add: l_def u_def)
  from Min_le[OF A] have l_props: "\<And>x. x\<le>l \<Longrightarrow> poly p x \<noteq> 0"
      by (fastforce simp: l_def)
  from Max_ge[OF A] have u_props: "\<And>x. x\<ge>u \<Longrightarrow> poly p x \<noteq> 0"
      by (fastforce simp: u_def)
  from l_props u_props show [simp]: "poly p l \<noteq> 0" "poly p u \<noteq> 0" by auto

  from l_props have "\<And>x. poly p x = 0 \<Longrightarrow> x > l" by (metis not_le)
  moreover from u_props have "\<And>x. poly p x = 0 \<Longrightarrow> x \<le> u" by (metis linear)
  ultimately show "{x. x > l \<and> x \<le> u \<and> poly p x = 0} = ?roots" by auto

  {
    fix x assume A: "x < l" "sgn (poly p x) \<noteq> sgn (poly p l)"
    with poly_IVT_pos[OF A(1), of p] poly_IVT_neg[OF A(1), of p] A(2)
        have False by (auto split: if_split_asm
                         simp: sgn_real_def l_props not_less less_eq_real_def)
  }
  thus "\<And>x. x \<le> l \<Longrightarrow> sgn (poly p x) = sgn (poly p l)"
      by (case_tac "x = l", auto simp: less_eq_real_def)

  {
    fix x assume A: "x > u" "sgn (poly p x) \<noteq> sgn (poly p u)"
    with u_props poly_IVT_neg[OF A(1), of p] poly_IVT_pos[OF A(1), of p] A(2)
        have False by (auto split: if_split_asm
                         simp: sgn_real_def l_props not_less less_eq_real_def)
  }
  thus "\<And>x. x \<ge> u \<Longrightarrow> sgn (poly p x) = sgn (poly p u)"
      by (case_tac "x = u", auto simp: less_eq_real_def)
qed



definition poly_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where
  "poly_inf p \<equiv> sgn (coeff p (degree p))"
definition poly_neg_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where
  "poly_neg_inf p \<equiv> if even (degree p) then sgn (coeff p (degree p))
                                       else -sgn (coeff p (degree p))"
lemma poly_inf_0_iff[simp]:
    "poly_inf p = 0 \<longleftrightarrow> p = 0" "poly_neg_inf p = 0 \<longleftrightarrow> p = 0"
    by (auto simp: poly_inf_def poly_neg_inf_def sgn_zero_iff)

lemma poly_inf_mult[simp]:
  fixes p :: "('a::real_normed_field) poly"
  shows "poly_inf (p*q) = poly_inf p * poly_inf q"
        "poly_neg_inf (p*q) = poly_neg_inf p * poly_neg_inf q"
unfolding poly_inf_def poly_neg_inf_def
by ((cases "p = 0 \<or> q = 0",auto simp: sgn_zero_iff
         degree_mult_eq[of p q] coeff_mult_degree_sum Real_Vector_Spaces.sgn_mult)[])+


lemma poly_neq_0_at_infinity:
  assumes "(p :: real poly) \<noteq> 0"
  shows "eventually (\<lambda>x. poly p x \<noteq> 0) at_infinity"
proof-
  from poly_roots_bounds[OF assms] guess l u .
  note lu_props = this
  define b where "b = max (-l) u"
  show ?thesis
  proof (subst eventually_at_infinity, rule exI[of _ b], clarsimp)
    fix x assume A: "\<bar>x\<bar> \<ge> b" and B: "poly p x = 0"
    show False
    proof (cases "x \<ge> 0")
      case True
        with A have "x \<ge> u" unfolding b_def by simp
        with lu_props(3, 6) show False by (metis sgn_zero_iff B)
    next
      case False
        with A have "x \<le> l" unfolding b_def by simp
        with lu_props(2, 5) show False by (metis sgn_zero_iff B)
    qed
  qed
qed




lemma poly_limit_aux:
  fixes p :: "real poly"
  defines "n \<equiv> degree p"
  shows "((\<lambda>x. poly p x / x ^ n) \<longlongrightarrow> coeff p n) at_infinity"
proof (subst filterlim_cong, rule refl, rule refl)
  show "eventually (\<lambda>x. poly p x / x^n = (\<Sum>i\<le>n. coeff p i / x^(n-i)))
            at_infinity"
  proof (rule eventually_mono)
    show "eventually (\<lambda>x::real. x \<noteq> 0) at_infinity"
        by (simp add: eventually_at_infinity, rule exI[of _ 1], auto)
    fix x :: real assume [simp]: "x \<noteq> 0"
    show "poly p x / x ^ n = (\<Sum>i\<le>n. coeff p i / x ^ (n - i))"
        by (simp add: n_def sum_divide_distrib power_diff poly_altdef)
  qed

  let ?a = "\<lambda>i. if i = n then coeff p n else 0"
  have "\<forall>i\<in>{..n}. ((\<lambda>x. coeff p i / x ^ (n - i)) \<longlongrightarrow> ?a i) at_infinity"
  proof
    fix i assume "i \<in> {..n}"
    hence "i \<le> n" by simp
    show "((\<lambda>x. coeff p i / x ^ (n - i)) \<longlongrightarrow> ?a i) at_infinity"
    proof (cases "i = n")
      case True
        thus ?thesis by (intro tendstoI, subst eventually_at_infinity,
                         intro exI[of _ 1], simp add: dist_real_def)
    next
      case False
        hence "n - i > 0" using \<open>i \<le> n\<close> by simp
        from tendsto_inverse_0 and divide_real_def[of 1]
            have "((\<lambda>x. 1 / x :: real) \<longlongrightarrow> 0) at_infinity" by simp
        from tendsto_power[OF this, of "n - i"]
            have "((\<lambda>x::real. 1 / x ^ (n - i)) \<longlongrightarrow> 0) at_infinity"
                using \<open>n - i > 0\<close> by (simp add: power_0_left power_one_over)
        from tendsto_mult_right_zero[OF this, of "coeff p i"]
            have "((\<lambda>x. coeff p i / x ^ (n - i)) \<longlongrightarrow> 0) at_infinity"
                by (simp add: field_simps)
        thus ?thesis using False by simp
    qed
  qed
  hence "((\<lambda>x. \<Sum>i\<le>n. coeff p i / x^(n-i)) \<longlongrightarrow> (\<Sum>i\<le>n. ?a i)) at_infinity"
    by (force intro!: tendsto_sum)
  also have "(\<Sum>i\<le>n. ?a i) = coeff p n" by (subst sum.delta, simp_all)
  finally show "((\<lambda>x. \<Sum>i\<le>n. coeff p i / x^(n-i)) \<longlongrightarrow> coeff p n) at_infinity" .
qed



lemma poly_at_top_at_top:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) > 0"
  shows "LIM x at_top. poly p x :> at_top"
proof-
  let ?n = "degree p"
  define f g where "f x = poly p x / x^?n" and "g x = x ^ ?n" for x :: real

  from poly_limit_aux have "(f \<longlongrightarrow> coeff p (degree p)) at_top"
      using tendsto_mono at_top_le_at_infinity unfolding f_def by blast
  moreover from assms
      have "LIM x at_top. g x :> at_top"
        by (auto simp add: g_def intro!: filterlim_pow_at_top filterlim_ident)
  ultimately have "LIM x at_top. f x * g x :> at_top"
      using filterlim_tendsto_pos_mult_at_top assms by simp
  also have "eventually (\<lambda>x. f x * g x = poly p x) at_top"
      unfolding f_def g_def
      by (subst eventually_at_top_linorder, rule exI[of _ 1],
          simp add: poly_altdef field_simps sum_distrib_left power_diff)
  note filterlim_cong[OF refl refl this]
  finally show ?thesis .
qed

lemma poly_at_bot_at_top:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) < 0"
  shows "LIM x at_top. poly p x :> at_bot"
proof-
  from poly_at_top_at_top[of "-p"] and assms
      have "LIM x at_top. -poly p x :> at_top" by simp
  thus ?thesis by (simp add: filterlim_uminus_at_bot)
qed

lemma poly_lim_inf:
  "eventually (\<lambda>x::real. sgn (poly p x) = poly_inf p) at_top"
proof (cases "degree p \<ge> 1")
  case False
    hence "degree p = 0" by simp
    then obtain c where "p = [:c:]" by (cases p, auto split: if_split_asm)
    thus ?thesis
        by (simp add: eventually_at_top_linorder poly_inf_def)
next
  case True
    note deg = this
    let ?lc = "coeff p (degree p)"
    from True have "?lc \<noteq> 0" by force
    show ?thesis
    proof (cases "?lc > 0")
      case True
        from poly_at_top_at_top[OF deg this]
          obtain x\<^sub>0 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
              by (fastforce simp: filterlim_at_top
                      eventually_at_top_linorder less_eq_real_def)
        hence "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
        thus ?thesis by (simp only: eventually_at_top_linorder poly_inf_def,
                             intro exI[of _ x\<^sub>0], simp add: True)
    next
      case False
        hence "?lc < 0" using \<open>?lc \<noteq> 0\<close> by linarith
        from poly_at_bot_at_top[OF deg this]
          obtain x\<^sub>0 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
              by (fastforce simp: filterlim_at_bot
                      eventually_at_top_linorder less_eq_real_def)
        hence "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
        thus ?thesis by (simp only: eventually_at_top_linorder poly_inf_def,
                             intro exI[of _ x\<^sub>0], simp add: \<open>?lc < 0\<close>)
    qed
qed

lemma poly_at_top_or_bot_at_bot:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) > 0"
  shows "LIM x at_bot. poly p x :> (if even (degree p) then at_top else at_bot)"
proof-
  let ?n = "degree p"
  define f g where "f x = poly p x / x ^ ?n" and "g x = x ^ ?n" for x :: real

  from poly_limit_aux have "(f \<longlongrightarrow> coeff p (degree p)) at_bot"
      using tendsto_mono at_bot_le_at_infinity by (force simp: f_def [abs_def])
  moreover from assms
      have "LIM x at_bot. g x :> (if even (degree p) then at_top else at_bot)"
        by (auto simp add: g_def split: if_split_asm intro: filterlim_pow_at_bot_even filterlim_pow_at_bot_odd filterlim_ident)
  ultimately have "LIM x at_bot. f x * g x :>
                      (if even ?n then at_top else at_bot)"
      by (auto simp: assms intro: filterlim_tendsto_pos_mult_at_top
                                  filterlim_tendsto_pos_mult_at_bot)
  also have "eventually (\<lambda>x. f x * g x = poly p x) at_bot"
      unfolding f_def g_def
      by (subst eventually_at_bot_linorder, rule exI[of _ "-1"],
          simp add: poly_altdef field_simps sum_distrib_left power_diff)
  note filterlim_cong[OF refl refl this]
  finally show ?thesis .
qed


lemma poly_at_bot_or_top_at_bot:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) < 0"
  shows "LIM x at_bot. poly p x :> (if even (degree p) then at_bot else at_top)"
proof-
  from poly_at_top_or_bot_at_bot[of "-p"] and assms
      have "LIM x at_bot. -poly p x :>
                (if even (degree p) then at_top else at_bot)" by simp
  thus ?thesis by (auto simp: filterlim_uminus_at_bot)
qed

lemma poly_lim_neg_inf:
  "eventually (\<lambda>x::real. sgn (poly p x) = poly_neg_inf p) at_bot"
proof (cases "degree p \<ge> 1")
  case False
    hence "degree p = 0" by simp
    then obtain c where "p = [:c:]" by (cases p, auto split: if_split_asm)
    thus ?thesis
        by (simp add: eventually_at_bot_linorder poly_neg_inf_def)
next
  case True
    note deg = this
    let ?lc = "coeff p (degree p)"
    from True have "?lc \<noteq> 0" by force
    show ?thesis
    proof (cases "?lc > 0")
      case True
        note lc_pos = this
        show ?thesis
        proof (cases "even (degree p)")
          case True
            from poly_at_top_or_bot_at_bot[OF deg lc_pos] and True
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
                by (fastforce simp add: filterlim_at_top filterlim_at_bot
                        eventually_at_bot_linorder less_eq_real_def)
                hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
              thus ?thesis
                by (simp add: True eventually_at_bot_linorder poly_neg_inf_def,
                    intro exI[of _ x\<^sub>0], simp add: lc_pos)
       next
          case False
            from poly_at_top_or_bot_at_bot[OF deg lc_pos] and False
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
                by (fastforce simp add: filterlim_at_bot
                        eventually_at_bot_linorder less_eq_real_def)
                hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
              thus ?thesis
                by (simp add: False eventually_at_bot_linorder poly_neg_inf_def,
                              intro exI[of _ x\<^sub>0], simp add: lc_pos)
      qed
    next
      case False
        hence lc_neg: "?lc < 0" using \<open>?lc \<noteq> 0\<close> by linarith
        show ?thesis
        proof (cases "even (degree p)")
          case True
            with poly_at_bot_or_top_at_bot[OF deg lc_neg]
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
                  by (fastforce simp: filterlim_at_bot
                          eventually_at_bot_linorder less_eq_real_def)
              hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
              thus ?thesis
                by (simp only: True eventually_at_bot_linorder poly_neg_inf_def,
                               intro exI[of _ x\<^sub>0], simp add: lc_neg)
        next
          case False
            with poly_at_bot_or_top_at_bot[OF deg lc_neg]
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
                  by (fastforce simp: filterlim_at_top
                          eventually_at_bot_linorder less_eq_real_def)
              hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
              thus ?thesis
                by (simp only: False eventually_at_bot_linorder poly_neg_inf_def,
                               intro exI[of _ x\<^sub>0], simp add: lc_neg)
        qed
    qed
qed





subsubsection \<open>Signs of polynomials for sufficiently large values\<close>

lemma polys_inf_sign_thresholds:
  assumes "finite (ps :: real poly set)"
  obtains l u
  where "l \<le> u"
    and "\<And>p. \<lbrakk>p \<in> ps; p \<noteq> 0\<rbrakk> \<Longrightarrow>
              {x. l < x \<and> x \<le> u \<and> poly p x = 0} = {x. poly p x = 0}"
    and "\<And>p x. \<lbrakk>p \<in> ps; x \<ge> u\<rbrakk> \<Longrightarrow> sgn (poly p x) = poly_inf p"
    and "\<And>p x. \<lbrakk>p \<in> ps; x \<le> l\<rbrakk> \<Longrightarrow> sgn (poly p x) = poly_neg_inf p"
proof goal_cases
  case prems: 1
  have "\<exists>l u. l \<le> u \<and> (\<forall>p x. p \<in> ps \<and> x \<ge> u \<longrightarrow> sgn (poly p x) = poly_inf p) \<and>
              (\<forall>p x. p \<in> ps \<and> x \<le> l \<longrightarrow> sgn (poly p x) = poly_neg_inf p)"
      (is "\<exists>l u. ?P ps l u")
  proof (induction rule: finite_subset_induct[OF assms(1), where A = UNIV])
    case 1
      show ?case by simp
  next
    case 2
      show ?case by (intro exI[of _ 42], simp)
  next
    case prems: (3 p ps)
      from prems(4) obtain l u where lu_props: "?P ps l u" by blast
      from poly_lim_inf obtain u'
          where u'_props: "\<forall>x\<ge>u'. sgn (poly p x) = poly_inf p"
          by (force simp add: eventually_at_top_linorder)
      from poly_lim_neg_inf obtain l'
          where l'_props: "\<forall>x\<le>l'. sgn (poly p x) = poly_neg_inf p"
          by (force simp add: eventually_at_bot_linorder)
      show ?case
          by (rule exI[of _ "min l l'"], rule exI[of _ "max u u'"],
              insert lu_props l'_props u'_props, auto)
  qed
  then obtain l u where lu_props: "l \<le> u"
        "\<And>p x. p \<in> ps \<Longrightarrow> u \<le> x \<Longrightarrow> sgn (poly p x) = poly_inf p"
        "\<And>p x. p \<in> ps \<Longrightarrow> x \<le> l \<Longrightarrow> sgn (poly p x) = poly_neg_inf p" by blast
  moreover {
    fix p x assume A: "p \<in> ps" "p \<noteq> 0" "poly p x = 0"
    from A have "l < x" "x < u"
        by (auto simp: not_le[symmetric] dest: lu_props(2,3))
  }
  note A = this
  have "\<And>p. p \<in> ps \<Longrightarrow> p \<noteq> 0 \<Longrightarrow>
                 {x. l < x \<and> x \<le> u \<and> poly p x = 0} = {x. poly p x = 0}"
      by (auto dest: A)

  from prems[OF lu_props(1) this lu_props(2,3)] show thesis .
qed


subsubsection \<open>Positivity of polynomials\<close>

lemma poly_pos:
  "(\<forall>x::real. poly p x > 0) \<longleftrightarrow> poly_inf p = 1 \<and> (\<forall>x. poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x::real. poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. poly p x \<noteq> 0" by simp

  from poly_lim_inf obtain x where "sgn (poly p x) = poly_inf p"
      by (auto simp: eventually_at_top_linorder)
  with A show "poly_inf p = 1"
      by (simp add: sgn_real_def split: if_split_asm)
next
  assume "poly_inf p = 1 \<and> (\<forall>x. poly p x \<noteq> 0)"
  hence A: "poly_inf p = 1" and B: "(\<forall>x. poly p x \<noteq> 0)" by simp_all
  from poly_lim_inf obtain x where C: "sgn (poly p x) = poly_inf p"
      by (auto simp: eventually_at_top_linorder)
  show "\<forall>x. poly p x > 0"
  proof (rule ccontr)
    assume "\<not>(\<forall>x. poly p x > 0)"
    then obtain x' where "poly p x' \<le> 0" by (auto simp: not_less)
    with A and C have "sgn (poly p x') \<noteq> sgn (poly p x)"
        by (auto simp: sgn_real_def split: if_split_asm)
    from poly_different_sign_imp_root'[OF this] and B
        show False by blast
  qed
qed

lemma poly_pos_greater:
  "(\<forall>x::real. x > a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    poly_inf p = 1 \<and> (\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x::real. x > a \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. x > a \<longrightarrow> poly p x \<noteq> 0" by auto

  from poly_lim_inf obtain x\<^sub>0 where
      "\<forall>x\<ge>x\<^sub>0. sgn (poly p x) = poly_inf p"
      by (auto simp: eventually_at_top_linorder)
  hence "poly_inf p = sgn (poly p (max x\<^sub>0 (a + 1)))" by simp
  also from A have "... = 1" by force
  finally show "poly_inf p = 1" .
next
  assume "poly_inf p = 1 \<and> (\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "poly_inf p = 1" and
        B: "(\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0)" by simp_all
  from poly_lim_inf obtain x\<^sub>0 where
      C: "\<forall>x\<ge>x\<^sub>0. sgn (poly p x) = poly_inf p"
      by (auto simp: eventually_at_top_linorder)
  hence "sgn (poly p (max x\<^sub>0 (a+1))) = poly_inf p" by simp
  with A have D: "sgn (poly p (max x\<^sub>0 (a+1))) = 1" by simp
  show "\<forall>x. x > a \<longrightarrow> poly p x > 0"
  proof (rule ccontr)
    assume "\<not>(\<forall>x. x > a \<longrightarrow> poly p x > 0)"
    then obtain x' where "x' > a" "poly p x' \<le> 0" by (auto simp: not_less)
    with A and D have E: "sgn (poly p x') \<noteq> sgn (poly p (max x\<^sub>0(a+1)))"
        by (auto simp: sgn_real_def split: if_split_asm)
    show False
        apply (cases x' "max x\<^sub>0 (a+1)" rule: linorder_cases)
        using B E \<open>x' > a\<close>
            apply (force dest!: poly_different_sign_imp_root[of _ _ p])+
        done
  qed
qed

lemma poly_pos_geq:
  "(\<forall>x::real. x \<ge> a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    poly_inf p = 1 \<and> (\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x::real. x \<ge> a \<longrightarrow> poly p x > 0"
  hence "\<forall>x::real. x > a \<longrightarrow> poly p x > 0" by simp
  also note poly_pos_greater
  finally have "poly_inf p = 1" "(\<forall>x>a. poly p x \<noteq> 0)" by simp_all
  moreover from A have "poly p a > 0" by simp
  ultimately show "poly_inf p = 1" "\<forall>x\<ge>a. poly p x \<noteq> 0"
      by (auto simp: less_eq_real_def)
next
  assume "poly_inf p = 1 \<and> (\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "poly_inf p = 1" and
        B: "poly p a \<noteq> 0" and C: "\<forall>x>a. poly p x \<noteq> 0" by simp_all
  from A and C and poly_pos_greater have "\<forall>x>a. poly p x > 0" by simp
  moreover with B C poly_IVT_pos[of a "a+1" p] have "poly p a > 0" by force
  ultimately show "\<forall>x\<ge>a. poly p x > 0" by (auto simp: less_eq_real_def)
qed

lemma poly_pos_less:
  "(\<forall>x::real. x < a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    poly_neg_inf p = 1 \<and> (\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x::real. x < a \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. x < a \<longrightarrow> poly p x \<noteq> 0" by auto

  from poly_lim_neg_inf obtain x\<^sub>0 where
      "\<forall>x\<le>x\<^sub>0. sgn (poly p x) = poly_neg_inf p"
      by (auto simp: eventually_at_bot_linorder)
  hence "poly_neg_inf p = sgn (poly p (min x\<^sub>0 (a - 1)))" by simp
  also from A have "... = 1" by force
  finally show "poly_neg_inf p = 1" .
next
  assume "poly_neg_inf p = 1 \<and> (\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "poly_neg_inf p = 1" and
        B: "(\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0)" by simp_all
  from poly_lim_neg_inf obtain x\<^sub>0 where
      C: "\<forall>x\<le>x\<^sub>0. sgn (poly p x) = poly_neg_inf p"
      by (auto simp: eventually_at_bot_linorder)
  hence "sgn (poly p (min x\<^sub>0 (a - 1))) = poly_neg_inf p" by simp
  with A have D: "sgn (poly p (min x\<^sub>0 (a - 1))) = 1" by simp
  show "\<forall>x. x < a \<longrightarrow> poly p x > 0"
  proof (rule ccontr)
    assume "\<not>(\<forall>x. x < a \<longrightarrow> poly p x > 0)"
    then obtain x' where "x' < a" "poly p x' \<le> 0" by (auto simp: not_less)
    with A and D have E: "sgn (poly p x') \<noteq> sgn (poly p (min x\<^sub>0 (a - 1)))"
        by (auto simp: sgn_real_def split: if_split_asm)
    show False
        apply (cases x' "min x\<^sub>0 (a - 1)" rule: linorder_cases)
        using B E \<open>x' < a\<close>
            apply (auto dest!: poly_different_sign_imp_root[of _ _ p])+
        done
  qed
qed

lemma poly_pos_leq:
  "(\<forall>x::real. x \<le> a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    poly_neg_inf p = 1 \<and> (\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x::real. x \<le> a \<longrightarrow> poly p x > 0"
  hence "\<forall>x::real. x < a \<longrightarrow> poly p x > 0" by simp
  also note poly_pos_less
  finally have "poly_neg_inf p = 1" "(\<forall>x<a. poly p x \<noteq> 0)" by simp_all
  moreover from A have "poly p a > 0" by simp
  ultimately show "poly_neg_inf p = 1" "\<forall>x\<le>a. poly p x \<noteq> 0"
      by (auto simp: less_eq_real_def)
next
  assume "poly_neg_inf p = 1 \<and> (\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "poly_neg_inf p = 1" and
        B: "poly p a \<noteq> 0" and C: "\<forall>x<a. poly p x \<noteq> 0" by simp_all
  from A and C and poly_pos_less have "\<forall>x<a. poly p x > 0" by simp
  moreover with B C poly_IVT_neg[of "a - 1" a p] have "poly p a > 0" by force
  ultimately show "\<forall>x\<le>a. poly p x > 0" by (auto simp: less_eq_real_def)
qed

lemma poly_pos_between_less_less:
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    (a \<ge> b \<or> poly p ((a+b)/2) > 0) \<and> (\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" by auto
  from A show "a \<ge> b \<or> poly p ((a+b)/2) > 0" by (cases "a < b", auto)
next
  assume "(b \<le> a \<or> 0 < poly p ((a+b)/2)) \<and> (\<forall>x. a<x \<and> x<b \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "b \<le> a \<or> 0 < poly p ((a+b)/2)" and
        B: "\<forall>x. a<x \<and> x<b \<longrightarrow> poly p x \<noteq> 0" by simp_all
  show "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x > 0"
  proof (cases "a \<ge> b", simp, clarify, rule_tac ccontr,
         simp only: not_le not_less)
    fix x assume "a < b" "a < x" "x < b" "poly p x \<le> 0"
    with B have "poly p x < 0" by (simp add: less_eq_real_def)
    moreover from A and \<open>a < b\<close> have "poly p ((a+b)/2) > 0" by simp
    ultimately have "sgn (poly p x) \<noteq> sgn (poly p ((a+b)/2))" by simp
    thus False using B
       apply (cases x "(a+b)/2" rule: linorder_cases)
       apply (drule poly_different_sign_imp_root[of _ _ p], assumption,
              insert \<open>a < b\<close> \<open>a < x\<close> \<open>x < b\<close> , force) []
       apply simp
       apply (drule poly_different_sign_imp_root[of _ _ p], simp,
              insert \<open>a < b\<close> \<open>a < x\<close> \<open>x < b\<close> , force)
       done
  qed
qed

lemma poly_pos_between_less_leq:
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    (a \<ge> b \<or> poly p b > 0) \<and> (\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0" by auto
  from A show "a \<ge> b \<or> poly p b > 0" by (cases "a < b", auto)
next
  assume "(b \<le> a \<or> 0 < poly p b) \<and> (\<forall>x. a<x \<and> x\<le>b \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "b \<le> a \<or> 0 < poly p b" and B: "\<forall>x. a<x \<and> x\<le>b \<longrightarrow> poly p x \<noteq> 0"
      by simp_all
  show "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x > 0"
  proof (cases "a \<ge> b", simp, clarify, rule_tac ccontr,
         simp only: not_le not_less)
    fix x assume "a < b" "a < x" "x \<le> b" "poly p x \<le> 0"
    with B have "poly p x < 0" by (simp add: less_eq_real_def)
    moreover from A and \<open>a < b\<close> have "poly p b > 0" by simp
    ultimately have "x < b" using \<open>x \<le> b\<close> by (auto simp: less_eq_real_def)
    from \<open>poly p x < 0\<close> and \<open>poly p b > 0\<close>
        have "sgn (poly p x) \<noteq> sgn (poly p b)" by simp
    from poly_different_sign_imp_root[OF \<open>x < b\<close> this] and B and \<open>x > a\<close>
        show False by auto
  qed
qed

lemma poly_pos_between_leq_less:
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    (a \<ge> b \<or> poly p a > 0) \<and> (\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" by auto
  from A show "a \<ge> b \<or> poly p a > 0" by (cases "a < b", auto)
next
  assume "(b \<le> a \<or> 0 < poly p a) \<and> (\<forall>x. a\<le>x \<and> x<b \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "b \<le> a \<or> 0 < poly p a" and B: "\<forall>x. a\<le>x \<and> x<b \<longrightarrow> poly p x \<noteq> 0"
      by simp_all
  show "\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x > 0"
  proof (cases "a \<ge> b", simp, clarify, rule_tac ccontr,
         simp only: not_le not_less)
    fix x assume "a < b" "a \<le> x" "x < b" "poly p x \<le> 0"
    with B have "poly p x < 0" by (simp add: less_eq_real_def)
    moreover from A and \<open>a < b\<close> have "poly p a > 0" by simp
    ultimately have "x > a" using \<open>x \<ge> a\<close> by (auto simp: less_eq_real_def)
    from \<open>poly p x < 0\<close> and \<open>poly p a > 0\<close>
        have "sgn (poly p a) \<noteq> sgn (poly p x)" by simp
    from poly_different_sign_imp_root[OF \<open>x > a\<close> this] and B and \<open>x < b\<close>
        show False by auto
  qed
qed

lemma poly_pos_between_leq_leq:
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
    (a > b \<or> poly p a > 0) \<and> (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0)"
proof (intro iffI conjI)
  assume A: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x > 0"
  have "\<And>x. poly p (x::real) > 0 \<Longrightarrow> poly p x \<noteq> 0" by simp
  with A show "\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0" by auto
  from A show "a > b \<or> poly p a > 0" by (cases "a \<le> b", auto)
next
  assume "(b < a \<or> 0 < poly p a) \<and> (\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> poly p x \<noteq> 0)"
  hence A: "b < a \<or> 0 < poly p a" and B: "\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> poly p x \<noteq> 0"
      by simp_all
  show "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x > 0"
  proof (cases "a > b", simp, clarify, rule_tac ccontr,
         simp only: not_le not_less)
    fix x assume "a \<le> b" "a \<le> x" "x \<le> b" "poly p x \<le> 0"
    with B have "poly p x < 0" by (simp add: less_eq_real_def)
    moreover from A and \<open>a \<le> b\<close> have "poly p a > 0" by simp
    ultimately have "x > a" using \<open>x \<ge> a\<close> by (auto simp: less_eq_real_def)
    from \<open>poly p x < 0\<close> and \<open>poly p a > 0\<close>
        have "sgn (poly p a) \<noteq> sgn (poly p x)" by simp
    from poly_different_sign_imp_root[OF \<open>x > a\<close> this] and B and \<open>x \<le> b\<close>
        show False by auto
  qed
qed

end
