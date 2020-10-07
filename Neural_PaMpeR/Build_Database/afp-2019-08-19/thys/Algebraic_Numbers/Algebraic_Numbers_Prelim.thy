(*
    Author:      René Thiemann
                 Sebastiaan Joosten
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers -- Excluding Addition and Multiplication\<close>

text \<open>This theory contains basic definition and results on algebraic numbers, namely that
  algebraic numbers are closed under negation, inversion, $n$-th roots, and
  that every rational number is algebraic. For all of these closure properties, corresponding
  polynomial witnesses are available.

  Moreover, this theory contains the uniqueness result,
  that for every algebraic number there is exactly one content-free irreducible polynomial with
  positive leading coefficient for it.
  This result is stronger than similar ones which you find in many textbooks.
  The reason is that here we do not require a least degree construction.

  This is essential, since given some content-free irreducible polynomial for x,
  how should we check whether the degree is optimal. In the formalized result, this is
  not required. The result is proven via GCDs, and that the GCD does not change
  when executed on the rational numbers or on the reals or complex numbers, and that
  the GCD of a rational polynomial can be expressed via the GCD of integer polynomials.\<close>

text \<open>Many results are taken from the textbook \cite[pages 317ff]{AlgNumbers}.\<close>

theory Algebraic_Numbers_Prelim
imports
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  Polynomial_Factorization.Rational_Factorization
  Berlekamp_Zassenhaus.Factorize_Int_Poly
  Berlekamp_Zassenhaus.Unique_Factorization_Poly
begin

text \<open>For algebraic numbers, it turned out that @{const gcd_int_poly} is not
  preferable to the default implementation of @{const gcd}, which just implements
  Collin's primitive remainder sequence.\<close>
declare gcd_int_poly_code[code_unfold del]

lemma primitive_imp_unit_iff:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes pr: "primitive p"
  shows "p dvd 1 \<longleftrightarrow> degree p = 0"
proof
  assume "degree p = 0"
  from degree0_coeffs[OF this] obtain p0 where p: "p = [:p0:]" by auto
  then have "\<forall>c \<in> set (coeffs p). p0 dvd c" by (simp add: cCons_def)
  with pr have "p0 dvd 1" by (auto dest: primitiveD)
  with p show "p dvd 1" by auto
next
  assume "p dvd 1"
  then show "degree p = 0" by (auto simp: poly_dvd_1)
qed

lemma dvd_all_coeffs_imp_dvd:
  assumes "\<forall>a \<in> set (coeffs p). c dvd a" shows "[:c:] dvd p"
proof (insert assms, induct p)
  case 0
  then show ?case by simp
next
  case (pCons a p)
  have "pCons a p = [:a:] + pCons 0 p" by simp
  also have "[:c:] dvd ..."
  proof (rule dvd_add)
    from pCons show "[:c:] dvd [:a:]" by (auto simp: cCons_def)
    from pCons have "[:c:] dvd p" by auto
    from Rings.dvd_mult[OF this]
    show "[:c:] dvd pCons 0 p" by (subst pCons_0_as_mult)
  qed
  finally show ?case.
qed

lemma irreducible_content:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "irreducible p" shows "degree p = 0 \<or> primitive p"
proof(rule ccontr)
  assume not: "\<not>?thesis"
  then obtain c where c1: "\<not>c dvd 1" and "\<forall>a \<in> set (coeffs p). c dvd a" by (auto elim: not_primitiveE)
  from dvd_all_coeffs_imp_dvd[OF this(2)]
  obtain r where p: "p = r * [:c:]" by (elim dvdE, auto)
  from irreducibleD[OF assms this] have "r dvd 1 \<or> [:c:] dvd 1" by auto
  with c1 have "r dvd 1" unfolding const_poly_dvd_1 by auto
  then have "degree r = 0" unfolding poly_dvd_1 by auto
  with p have "degree p = 0" by auto
  with not show False by auto
qed

(* TODO: move *)
lemma linear_irreducible_field:
  fixes p :: "'a :: field poly"
  assumes deg: "degree p = 1" shows "irreducible p"
proof (intro irreducibleI)
  from deg show p0: "p \<noteq> 0" by auto
  from deg show "\<not> p dvd 1" by (auto simp: poly_dvd_1)
  fix a b assume p: "p = a * b"
  with p0 have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by auto
  from degree_mult_eq[OF this, folded p] assms
  consider "degree a = 1" "degree b = 0" | "degree a = 0" "degree b = 1" by force
  then show "a dvd 1 \<or> b dvd 1"
    by (cases; insert a0 b0, auto simp: primitive_imp_unit_iff)
qed

(* TODO: move *)
lemma linear_irreducible_int:
  fixes p :: "int poly"
  assumes deg: "degree p = 1" and cp: "content p dvd 1"
  shows "irreducible p"
proof (intro irreducibleI)
  from deg show p0: "p \<noteq> 0" by auto
  from deg show "\<not> p dvd 1" by (auto simp: poly_dvd_1)
  fix a b assume p: "p = a * b"
  note * = cp[unfolded p is_unit_content_iff, unfolded content_mult]
  have a1: "content a dvd 1" and b1: "content b dvd 1"
    using content_ge_0_int[of a] pos_zmult_eq_1_iff_lemma[OF *] * by (auto simp: abs_mult)
  with p0 have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by auto
  from degree_mult_eq[OF this, folded p] assms
  consider "degree a = 1" "degree b = 0" | "degree a = 0" "degree b = 1" by force
  then show "a dvd 1 \<or> b dvd 1"
    by (cases; insert a1 b1, auto simp: primitive_imp_unit_iff)
qed

lemma irreducible_connect_rev:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes irr: "irreducible p" and deg: "degree p > 0"
  shows "irreducible\<^sub>d p"
proof(intro irreducible\<^sub>dI deg)
  fix q r
  assume degq: "degree q > 0" and diff: "degree q < degree p" and p: "p = q * r"
  from degq have nu: "\<not> q dvd 1" by (auto simp: poly_dvd_1)
  from irreducibleD[OF irr p] nu have "r dvd 1" by auto
  then have "degree r = 0" by (auto simp: poly_dvd_1)
  with degq diff show False unfolding p using degree_mult_le[of q r] by auto
qed

subsection \<open>Polynomial Evaluation of Integer and Rational Polynomials in Fields.\<close>

abbreviation ipoly where "ipoly f x \<equiv> poly (of_int_poly f) x"

lemma poly_map_poly_code[code_unfold]: "poly (map_poly h p) x = fold_coeffs (\<lambda> a b. h a + x * b) p 0"
  by (induct p, auto)

abbreviation real_of_int_poly :: "int poly \<Rightarrow> real poly" where
  "real_of_int_poly \<equiv> of_int_poly"

abbreviation real_of_rat_poly :: "rat poly \<Rightarrow> real poly" where
  "real_of_rat_poly \<equiv> map_poly of_rat"

lemma of_rat_of_int[simp]: "of_rat \<circ> of_int = of_int" by auto

lemma ipoly_of_rat[simp]: "ipoly p (of_rat y) = of_rat (ipoly p y)"
proof-
  have id: "of_int = of_rat o of_int" unfolding comp_def by auto
  show ?thesis by (subst id, subst map_poly_map_poly[symmetric], auto)
qed

lemma ipoly_of_real[simp]:
  "ipoly p (of_real x :: 'a :: {field,real_algebra_1}) = of_real (ipoly p x)"
proof -
  have id: "of_int = of_real o of_int" unfolding comp_def by auto
  show ?thesis by (subst id, subst map_poly_map_poly[symmetric], auto)
qed

lemma finite_ipoly_roots: assumes "p \<noteq> 0"
  shows "finite {x :: real. ipoly p x = 0}"
proof -
  let ?p = "real_of_int_poly p"
  from assms have "?p \<noteq> 0" by auto
  thus ?thesis by (rule poly_roots_finite)
qed

subsection \<open>Algebraic Numbers -- Definition, Inverse, and Roots\<close>

text \<open>A number @{term "x :: 'a :: field"} is algebraic iff it is the root of an integer polynomial.
  Whereas the Isabelle distribution this is defined via the embedding
  of integers in an field via @{const Ints}, we work with integer polynomials
  of type @{type int} and then use @{const ipoly} for evaluating the polynomial at
  a real or complex point.\<close>

lemma algebraic_altdef_ipoly:
  shows "algebraic x \<longleftrightarrow> (\<exists>p. ipoly p x = 0 \<and> p \<noteq> 0)"
unfolding algebraic_def
proof (safe, goal_cases)
  case (1 p)
  define the_int where "the_int = (\<lambda>x::'a. THE r. x = of_int r)"
  define p' where "p' = map_poly the_int p"
  have of_int_the_int: "of_int (the_int x) = x" if "x \<in> \<int>" for x
    unfolding the_int_def by (rule sym, rule theI') (insert that, auto simp: Ints_def)
  have the_int_0_iff: "the_int x = 0 \<longleftrightarrow> x = 0" if "x \<in> \<int>"
    using of_int_the_int[OF that] by auto
  have "map_poly of_int p' = map_poly (of_int \<circ> the_int) p"
      by (simp add: p'_def map_poly_map_poly)
  also from 1 of_int_the_int have "\<dots> = p"
    by (subst poly_eq_iff) (auto simp: coeff_map_poly)
  finally have p_p': "map_poly of_int p' = p" .
  show ?case
  proof (intro exI conjI notI)
    from 1 show "ipoly p' x = 0" by (simp add: p_p')
  next
    assume "p' = 0"
    hence "p = 0" by (simp add: p_p' [symmetric])
    with \<open>p \<noteq> 0\<close> show False by contradiction
  qed
next
  case (2 p)
  thus ?case by (intro exI[of _ "map_poly of_int p"], auto)
qed

text \<open>Definition of being algebraic with explicit witness polynomial.\<close>

definition represents :: "int poly \<Rightarrow> 'a :: field_char_0 \<Rightarrow> bool" (infix "represents" 51)
  where "p represents x = (ipoly p x = 0 \<and> p \<noteq> 0)"

lemma representsI[intro]: "ipoly p x = 0 \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> p represents x"
  unfolding represents_def by auto

lemma representsD:
  assumes "p represents x" shows "p \<noteq> 0" and "ipoly p x = 0" using assms unfolding represents_def by auto

lemma representsE:
  assumes "p represents x" and "p \<noteq> 0 \<Longrightarrow> ipoly p x = 0 \<Longrightarrow> thesis"
  shows thesis using assms unfolding represents_def by auto

lemma represents_imp_degree:
  fixes x :: "'a :: field_char_0"
  assumes "p represents x" shows "degree p \<noteq> 0"
proof-
  from assms have "p \<noteq> 0" and px: "ipoly p x = 0" by (auto dest:representsD)
  then have "(of_int_poly p :: 'a poly) \<noteq> 0" by auto
  then have "degree (of_int_poly p :: 'a poly) \<noteq> 0" by (fold poly_zero[OF px])
  then show ?thesis by auto
qed

lemma representsE_full[elim]:
  assumes rep: "p represents x"
    and main: "p \<noteq> 0 \<Longrightarrow> ipoly p x = 0 \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow> thesis"
  shows thesis
  by (rule main, insert represents_imp_degree[OF rep] rep, auto elim: representsE)

lemma represents_of_rat[simp]: "p represents (of_rat x) = p represents x" by (auto elim!:representsE)
lemma represents_of_real[simp]: "p represents (of_real x) = p represents x" by (auto elim!:representsE)

lemma algebraic_iff_represents: "algebraic x \<longleftrightarrow> (\<exists> p. p represents x)"
  unfolding algebraic_altdef_ipoly represents_def ..

lemma represents_irr_non_0:
  assumes irr: "irreducible p" and ap: "p represents x" and x0: "x \<noteq> 0"
  shows "poly p 0 \<noteq> 0"
proof
  have nu: "\<not> [:0,1::int:] dvd 1" by (auto simp: poly_dvd_1)
  assume "poly p 0 = 0"
  hence dvd: "[: 0, 1 :] dvd p" by (unfold dvd_iff_poly_eq_0, simp)
  then obtain q where pq: "p = [:0,1:] * q" by (elim dvdE)
  from irreducibleD[OF irr this] nu have "q dvd 1" by auto
  from this obtain r where "q = [:r:]" "r dvd 1" by (auto simp add: poly_dvd_1 dest: degree0_coeffs)
  with pq have "p = [:0,r:]" by auto
  with ap have "x = 0" by (auto simp: of_int_hom.map_poly_pCons_hom)
  with x0 show False by auto
qed

text \<open>The polynomial encoding a rational number.\<close>

definition poly_rat :: "rat \<Rightarrow> int poly" where
  "poly_rat x = (case quotient_of x of (n,d) \<Rightarrow> [:-n,d:])"

definition abs_int_poly:: "int poly \<Rightarrow> int poly" where
  "abs_int_poly p \<equiv> if lead_coeff p < 0 then -p else p"

lemma pos_poly_abs_poly[simp]:
  shows "lead_coeff (abs_int_poly p) > 0 \<longleftrightarrow> p \<noteq> 0"
proof-
  have "p \<noteq> 0 \<longleftrightarrow> lead_coeff p * sgn (lead_coeff p) > 0" by (fold abs_sgn, auto)
  then show ?thesis by (auto simp: abs_int_poly_def mult.commute)
qed

lemma abs_int_poly_0[simp]: "abs_int_poly 0 = 0"
  by (auto simp: abs_int_poly_def)

lemma abs_int_poly_eq_0_iff[simp]: "abs_int_poly p = 0 \<longleftrightarrow> p = 0"
  by (auto simp: abs_int_poly_def sgn_eq_0_iff)

lemma degree_abs_int_poly[simp]: "degree (abs_int_poly p) = degree p"
  by (auto simp: abs_int_poly_def sgn_eq_0_iff)

lemma abs_int_poly_dvd[simp]: "abs_int_poly p dvd q \<longleftrightarrow> p dvd q"
  by (unfold abs_int_poly_def, auto)

(*TODO: move & generalize *)
lemma (in idom) irreducible_uminus[simp]: "irreducible (-x) \<longleftrightarrow> irreducible x"
proof-
  have "-x = -1 * x" by simp
  also have "irreducible ... \<longleftrightarrow> irreducible x" by (rule irreducible_mult_unit_left, auto)
  finally show ?thesis.
qed

lemma irreducible_abs_int_poly[simp]:
  "irreducible (abs_int_poly p) \<longleftrightarrow> irreducible p"
  by (unfold abs_int_poly_def, auto)

lemma coeff_abs_int_poly[simp]:
  "coeff (abs_int_poly p) n = (if lead_coeff p < 0 then - coeff p n else coeff p n)"
  by (simp add: abs_int_poly_def)

lemma lead_coeff_abs_int_poly[simp]:
  "lead_coeff (abs_int_poly p) = abs (lead_coeff p)"
  by auto

lemma ipoly_abs_int_poly_eq_zero_iff[simp]:
  "ipoly (abs_int_poly p) (x :: 'a :: comm_ring_1) = 0 \<longleftrightarrow> ipoly p x = 0"
  by (auto simp: abs_int_poly_def sgn_eq_0_iff of_int_poly_hom.hom_uminus)

lemma abs_int_poly_represents[simp]:
  "abs_int_poly p represents x \<longleftrightarrow> p represents x" by (auto elim!:representsE)


(* TODO: Move *)
lemma content_pCons[simp]: "content (pCons a p) = gcd a (content p)"
  by (unfold content_def coeffs_pCons_eq_cCons cCons_def, auto)

lemma content_uminus[simp]:
  fixes p :: "'a :: ring_gcd poly" shows "content (-p) = content p"
  by (induct p, auto)

lemma primitive_abs_int_poly[simp]:
  "primitive (abs_int_poly p) \<longleftrightarrow> primitive p"
  by (auto simp: abs_int_poly_def)

lemma abs_int_poly_inv[simp]: "smult (sgn (lead_coeff p)) (abs_int_poly p) = p"
  by (cases "lead_coeff p > 0", auto simp: abs_int_poly_def)



definition cf_pos :: "int poly \<Rightarrow> bool" where
  "cf_pos p = (content p = 1 \<and> lead_coeff p > 0)"

definition cf_pos_poly :: "int poly \<Rightarrow> int poly" where
  "cf_pos_poly f = (let
      c = content f;
      d = (sgn (lead_coeff f) * c)
    in sdiv_poly f d)"

lemma sgn_is_unit[intro!]:
  fixes x :: "'a :: linordered_idom" (* find/make better class *)
  assumes "x \<noteq> 0"
  shows "sgn x dvd 1" using assms by(cases x "0::'a" rule:linorder_cases, auto)

lemma cf_pos_poly_0[simp]: "cf_pos_poly 0 = 0" by (unfold cf_pos_poly_def sdiv_poly_def, auto)

lemma cf_pos_poly_eq_0[simp]: "cf_pos_poly f = 0 \<longleftrightarrow> f = 0"
proof(cases "f = 0")
  case True
  thus ?thesis unfolding cf_pos_poly_def Let_def by (simp add: sdiv_poly_def)
next
  case False
  then have lc0: "lead_coeff f \<noteq> 0" by auto
  then have s0: "sgn (lead_coeff f) \<noteq> 0" (is "?s \<noteq> 0") and "content f \<noteq> 0" (is "?c \<noteq> 0") by (auto simp: sgn_0_0)
  then have sc0: "?s * ?c \<noteq> 0" by auto
  { fix i
    from content_dvd_coeff sgn_is_unit[OF lc0]
    have "?s * ?c dvd coeff f i" by (auto simp: unit_dvd_iff)
    then have "coeff f i div (?s * ?c) = 0 \<longleftrightarrow> coeff f i = 0" by (auto simp:dvd_div_eq_0_iff)
  } note * = this
  show ?thesis unfolding cf_pos_poly_def Let_def sdiv_poly_def poly_eq_iff by (auto simp: coeff_map_poly *)
qed

lemma
  shows cf_pos_poly_main: "smult (sgn (lead_coeff f) * content f) (cf_pos_poly f) = f" (is ?g1)
    and content_cf_pos_poly[simp]: "content (cf_pos_poly f) = (if f = 0 then 0 else 1)" (is ?g2)
    and lead_coeff_cf_pos_poly[simp]: "lead_coeff (cf_pos_poly f) > 0 \<longleftrightarrow> f \<noteq> 0" (is ?g3)
    and cf_pos_poly_dvd[simp]: "cf_pos_poly f dvd f" (is ?g4)
proof(atomize(full), (cases "f = 0"; intro conjI))
  case True
  then show ?g1 ?g2 ?g3 ?g4 by simp_all
next
  case f0: False
  let ?s = "sgn (lead_coeff f)"
  have s: "?s \<in> {-1,1}" using f0 unfolding sgn_if by auto
  define g where "g \<equiv> smult ?s f"
  define d where "d \<equiv> ?s * content f"
  have "content g = content ([:?s:] * f)" unfolding g_def by simp
  also have "\<dots> = content [:?s:] * content f" unfolding content_mult by simp
  also have "content [:?s:] = 1" using s by (auto simp: content_def)
  finally have cg: "content g = content f" by simp
  from f0
  have d: "cf_pos_poly f = sdiv_poly f d"  by (auto simp: cf_pos_poly_def Let_def d_def)
  let ?g = "primitive_part g"
  define ng where "ng = primitive_part g"
  note d
  also have "sdiv_poly f d = sdiv_poly g (content g)" unfolding cg unfolding g_def d_def
    by (rule poly_eqI, unfold coeff_sdiv_poly coeff_smult, insert s, auto simp: div_minus_right)
  finally have fg: "cf_pos_poly f = primitive_part g" unfolding primitive_part_alt_def .
  have "lead_coeff f \<noteq> 0" using f0 by auto
  hence lg: "lead_coeff g > 0" unfolding g_def lead_coeff_smult
    by (meson linorder_neqE_linordered_idom sgn_greater sgn_less zero_less_mult_iff)
  hence g0: "g \<noteq> 0" by auto
  from f0 content_primitive_part[OF this]
  show ?g2 unfolding fg by auto
  from g0 have "content g \<noteq> 0" by simp
  with arg_cong[OF content_times_primitive_part[of g], of lead_coeff, unfolded lead_coeff_smult]
    lg content_ge_0_int[of g] have lg': "lead_coeff ng > 0" unfolding ng_def
    by (metis dual_order.antisym dual_order.strict_implies_order zero_less_mult_iff)
  with f0 show ?g3 unfolding fg ng_def by auto

  have d0: "d \<noteq> 0" using s f0 by (force simp add: d_def)
  have "smult d (cf_pos_poly f) = smult ?s (smult (content f) (sdiv_poly (smult ?s f) (content f)))"
    unfolding fg primitive_part_alt_def cg by (simp add: g_def d_def)
  also have "sdiv_poly (smult ?s f) (content f) = smult ?s (sdiv_poly f (content f))"
    using s by (metis cg g_def primitive_part_alt_def primitive_part_smult_int sgn_sgn)
  finally have "smult d (cf_pos_poly f) = smult (content f) (primitive_part f)"
    unfolding primitive_part_alt_def using s by auto
  also have "\<dots> = f" by (rule content_times_primitive_part)
  finally have df: "smult d (cf_pos_poly f) = f" .
  with d0 show ?g1 by (auto simp: d_def)
  from df have *: "f = cf_pos_poly f * [:d:]" by simp
  from dvdI[OF this] show ?g4.
qed

(* TODO: remove *)
lemma irreducible_connect_int:
  fixes p :: "int poly"
  assumes ir: "irreducible\<^sub>d p" and c: "content p = 1"
  shows "irreducible p"
  using c primitive_iff_content_eq_1 ir irreducible_primitive_connect by blast

lemma
  fixes x :: "'a :: {idom,ring_char_0}"
  shows ipoly_cf_pos_poly_eq_0[simp]: "ipoly (cf_pos_poly p) x = 0 \<longleftrightarrow> ipoly p x = 0"
    and degree_cf_pos_poly[simp]: "degree (cf_pos_poly p) = degree p"
    and cf_pos_cf_pos_poly[intro]: "p \<noteq> 0 \<Longrightarrow> cf_pos (cf_pos_poly p)"
proof-
  show "degree (cf_pos_poly p) = degree p"
    by (subst(3) cf_pos_poly_main[symmetric], auto simp:sgn_eq_0_iff)
  {
    assume p: "p \<noteq> 0"
    show "cf_pos (cf_pos_poly p)" using cf_pos_poly_main p by (auto simp: cf_pos_def)
    have "(ipoly (cf_pos_poly p) x = 0) = (ipoly p x = 0)"
      apply (subst(3) cf_pos_poly_main[symmetric]) by (auto simp: sgn_eq_0_iff hom_distribs)
  }
  then show "(ipoly (cf_pos_poly p) x = 0) = (ipoly p x = 0)" by (cases "p = 0", auto)
qed


lemma cf_pos_poly_eq_1: "cf_pos_poly f = 1 \<longleftrightarrow> degree f = 0 \<and> f \<noteq> 0" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI conjI)
  assume ?r
  then have df0: "degree f = 0" and f0: "f \<noteq> 0" by auto
  from  degree0_coeffs[OF df0] obtain f0 where f: "f = [:f0:]" by auto
  show "cf_pos_poly f = 1" using f0 unfolding f cf_pos_poly_def Let_def sdiv_poly_def
    by (auto simp: content_def mult_sgn_abs)
next
  assume l: ?l
  then have "degree (cf_pos_poly f) = 0" by auto
  then show "degree f = 0" by simp
  from l have "cf_pos_poly f \<noteq> 0" by auto
  then show "f \<noteq> 0" by simp
qed



lemma irr_cf_root_free_poly_rat[simp]: "irreducible (poly_rat x)"
  "lead_coeff (poly_rat x) > 0" "primitive (poly_rat x)" "root_free (poly_rat x)"
  "square_free (poly_rat x)"
proof -
  obtain n d where x: "quotient_of x = (n,d)" by force
  hence id: "poly_rat x = [:-n,d:]" by (auto simp: poly_rat_def)
  from quotient_of_denom_pos[OF x] have d: "d > 0" by auto
  show "root_free (poly_rat x)" unfolding id root_free_def using d by auto
  show "lead_coeff (poly_rat x) > 0" "primitive (poly_rat x)"
    unfolding id cf_pos_def using d quotient_of_coprime[OF x] by (auto simp: content_def)
  from this[unfolded cf_pos_def]
  show irr: "irreducible (poly_rat x)" unfolding id using d by (auto intro!: linear_irreducible_int)
  show "square_free (poly_rat x)"
    by (rule irreducible_imp_square_free[OF irr])
qed

lemma poly_rat[simp]: "ipoly (poly_rat x) (of_rat x :: 'a :: field_char_0) = 0" "ipoly (poly_rat x) x = 0"
  "poly_rat x \<noteq> 0" "ipoly (poly_rat x) y = 0 \<longleftrightarrow> y = (of_rat x :: 'a)"
proof -
  from irr_cf_root_free_poly_rat(1)[of x] show "poly_rat x \<noteq> 0"
    unfolding Factorial_Ring.irreducible_def by auto
  obtain n d where x: "quotient_of x = (n,d)" by force
  hence id: "poly_rat x = [:-n,d:]" by (auto simp: poly_rat_def)
  from quotient_of_denom_pos[OF x] have d: "d \<noteq> 0" by auto
  have "y * of_int d = of_int n \<Longrightarrow> y = of_int n / of_int d" using d
    by (simp add: eq_divide_imp)
  with d id show "ipoly (poly_rat x) (of_rat x) = 0" "ipoly (poly_rat x) x = 0"
    "ipoly (poly_rat x) y = 0 \<longleftrightarrow> y = (of_rat x :: 'a)"
    by (auto simp: of_rat_minus of_rat_divide simp: quotient_of_div[OF x])
qed

lemma poly_rat_represents_of_rat: "(poly_rat x) represents (of_rat x)" by auto

lemma ipoly_smult_0_iff: assumes c: "c \<noteq> 0"
  shows "(ipoly (smult c p) x = (0 :: real)) = (ipoly p x = 0)"
  using c by (simp add: hom_distribs)


(* TODO *)
lemma not_irreducibleD:
  assumes "\<not> irreducible x" and "x \<noteq> 0" and "\<not> x dvd 1"
  shows "\<exists>y z. x = y * z \<and> \<not> y dvd 1 \<and> \<not> z dvd 1" using assms
  apply (unfold Factorial_Ring.irreducible_def) by auto


lemma cf_pos_poly_represents[simp]: "(cf_pos_poly p) represents x \<longleftrightarrow> p represents x"
  unfolding represents_def by auto

definition factors_of_int_poly :: "int poly \<Rightarrow> int poly list" where
  "factors_of_int_poly p = map (abs_int_poly o fst) (snd (factorize_int_poly p))"

lemma factors_of_int_poly_const: assumes "degree p = 0"
  shows "factors_of_int_poly p = []"
proof -
  from degree0_coeffs[OF assms] obtain a where p: "p = [: a :]" by auto
  show ?thesis unfolding p factors_of_int_poly_def
    factorize_int_poly_generic_def x_split_def
    by (cases "a = 0", auto simp add: Let_def factorize_int_last_nz_poly_def)
qed

lemma coprime_prod: (* TODO: move *)
  "a \<noteq> 0 \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> coprime (a * b) (c * d) \<Longrightarrow> coprime b (d::'a::{semiring_gcd})"
  by auto

lemma smult_prod: (* TODO: move or find corresponding lemma *)
  "smult a b = monom a 0 * b"
  by (simp add: monom_0)

lemma degree_map_poly_2:
  assumes "f (lead_coeff p) \<noteq> 0"
  shows   "degree (map_poly f p) = degree p"
proof (cases "p=0")
  case False thus ?thesis
    unfolding degree_eq_length_coeffs Polynomial.coeffs_map_poly
    using assms by (simp add:coeffs_def)
qed auto

lemma degree_of_gcd: "degree (gcd q r) \<noteq> 0 \<longleftrightarrow>
 degree (gcd (of_int_poly q :: 'a :: {field_char_0,euclidean_ring_gcd} poly) (of_int_poly r)) \<noteq> 0"
proof -
  let ?r = "of_rat :: rat \<Rightarrow> 'a"
  interpret rpoly: field_hom' ?r
    by (unfold_locales, auto simp: of_rat_add of_rat_mult)
  {
    fix p
    have "of_int_poly p = map_poly (?r o of_int) p" unfolding o_def
      by auto
    also have "\<dots> = map_poly ?r (map_poly of_int p)"
      by (subst map_poly_map_poly, auto)
    finally have "of_int_poly p = map_poly ?r (map_poly of_int p)" .
  } note id = this
  show ?thesis unfolding id by (fold hom_distribs, simp add: gcd_rat_to_gcd_int)
qed


lemma irreducible_cf_pos_poly:
  assumes irr: "irreducible p" and deg: "degree p \<noteq> 0"
  shows "irreducible (cf_pos_poly p)" (is "irreducible ?p")
proof (unfold irreducible_altdef, intro conjI allI impI)
  from irr show "?p \<noteq> 0" by auto
  from deg have "degree ?p \<noteq> 0" by simp
  then show "\<not> ?p dvd 1" unfolding poly_dvd_1 by auto
  fix b assume "b dvd cf_pos_poly p"
  also note cf_pos_poly_dvd
  finally have "b dvd p".
  with irr[unfolded irreducible_altdef] have "p dvd b \<or> b dvd 1" by auto
  then show "?p dvd b \<or> b dvd 1" by (auto dest: dvd_trans[OF cf_pos_poly_dvd])
qed

locale dvd_preserving_hom = comm_semiring_1_hom +
  assumes hom_eq_mult_hom_imp: "hom x = hom y * hz \<Longrightarrow> \<exists>z. hz = hom z \<and> x = y * z"
begin

  lemma hom_dvd_hom_iff[simp]: "hom x dvd hom y \<longleftrightarrow> x dvd y"
  proof
    assume "hom x dvd hom y"
    then obtain hz where "hom y = hom x * hz" by (elim dvdE)
    from hom_eq_mult_hom_imp[OF this] obtain z
    where "hz = hom z" and mult: "y = x * z" by auto
    then show "x dvd y" by auto
  qed auto

  sublocale unit_preserving_hom
  proof unfold_locales
    fix x assume "hom x dvd 1" then have "hom x dvd hom 1" by simp
    then show "x dvd 1" by (unfold hom_dvd_hom_iff)
  qed

  sublocale zero_hom_0
  proof (unfold_locales)
    fix a :: 'a
    assume "hom a = 0"
    then have "hom 0 dvd hom a" by auto
    then have "0 dvd a" by (unfold hom_dvd_hom_iff)
    then show "a = 0" by auto
  qed

end


lemma factors_of_int_poly:
  defines "rp \<equiv> ipoly :: int poly \<Rightarrow> 'a :: {euclidean_ring_gcd,field_char_0} \<Rightarrow> 'a"
  assumes "factors_of_int_poly p = qs"
  shows "\<And> q. q \<in> set qs \<Longrightarrow> irreducible q \<and> lead_coeff q > 0 \<and> degree q \<le> degree p \<and> degree q \<noteq> 0"
  "p \<noteq> 0 \<Longrightarrow> rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)"
  "p \<noteq> 0 \<Longrightarrow> rp p x = 0 \<Longrightarrow> \<exists>! q \<in> set qs. rp q x = 0"
  "distinct qs"
proof -
  obtain c qis where factt: "factorize_int_poly p = (c,qis)" by force
  from assms[unfolded factors_of_int_poly_def factt]
  have qs: "qs = map (abs_int_poly \<circ> fst) (snd (c, qis))" by auto
  note fact = factorize_int_poly(1)[OF factt]
  note fact_mem = factorize_int_poly(2,3)[OF factt]
  have sqf: "square_free_factorization p (c, qis)" by (rule fact(1))
  note sff = square_free_factorizationD[OF sqf]
  have sff': "p = Polynomial.smult c (\<Prod>(a, i)\<leftarrow> qis. a ^ Suc i)"
    unfolding sff(1) prod.distinct_set_conv_list[OF sff(5)] ..
  {
    fix q
    assume q: "q \<in> set qs"
    then obtain r i where qi: "(r,i) \<in> set qis" and qr: "q = abs_int_poly r" unfolding qs by auto
    from split_list[OF qi] obtain qis1 qis2 where qis: "qis = qis1 @ (r,i) # qis2" by auto
    have dvd: "r dvd p" unfolding sff' qis dvd_def
      by (intro exI[of _ "smult c (r ^ i * (\<Prod>(a, i)\<leftarrow>qis1 @  qis2. a ^ Suc i))"], auto)
    from fact_mem[OF qi] have r0: "r \<noteq> 0" by auto
    from qi factt have p: "p \<noteq> 0" by (cases p, auto)
    with dvd have deg: "degree r \<le> degree p" by (metis dvd_imp_degree_le)
    with fact_mem[OF qi] r0
    show "irreducible q \<and> lead_coeff q > 0 \<and> degree q \<le> degree p \<and> degree q \<noteq> 0"
      unfolding qr lead_coeff_abs_int_poly by auto
  } note * = this
  show "distinct qs" unfolding distinct_conv_nth
  proof (intro allI impI)
    fix i j
    assume "i < length qs" "j < length qs" and diff: "i \<noteq> j"
    hence ij: "i < length qis" "j < length qis"
      and id: "qs ! i = abs_int_poly (fst (qis ! i))" "qs ! j = abs_int_poly (fst (qis ! j))" unfolding qs by auto
    obtain qi I where qi: "qis ! i = (qi, I)" by force
    obtain qj J where qj: "qis ! j = (qj, J)" by force
    from sff(5)[unfolded distinct_conv_nth, rule_format, OF ij diff] qi qj
    have diff: "(qi, I) \<noteq> (qj, J)" by auto
    from ij qi qj have "(qi, I) \<in> set qis" "(qj, J) \<in> set qis" unfolding set_conv_nth by force+
    from sff(3)[OF this diff] sff(2) this
    have cop: "coprime qi qj" "degree qi \<noteq> 0" "degree qj \<noteq> 0" by auto
    note i = cf_pos_poly_main[of qi, unfolded smult_prod monom_0]
    note j = cf_pos_poly_main[of qj, unfolded smult_prod monom_0]
    from cop(2) i have deg: "degree (qs ! i) \<noteq> 0" by (auto simp: id qi)
    have cop: "coprime (qs ! i) (qs ! j)"
      unfolding id qi qj fst_conv
      apply (rule coprime_prod[of "[:sgn (lead_coeff qi):]" "[:sgn (lead_coeff qj):]"])
      using cop
      unfolding i j by (auto simp: sgn_eq_0_iff)
    show "qs ! i \<noteq> qs ! j"
    proof
      assume id: "qs ! i = qs ! j"
      have "degree (gcd (qs ! i) (qs ! j)) = degree (qs ! i)"  unfolding id by simp
      also have "\<dots> \<noteq> 0" using deg by simp
      finally show False using cop by simp
    qed
  qed
  assume p: "p \<noteq> 0"
  from fact(1) p have c: "c \<noteq> 0" using sff(1) by auto
  let ?r = "of_int :: int \<Rightarrow> 'a"
  let ?rp = "map_poly ?r"
  have rp: "\<And> x p. rp p x = 0 \<longleftrightarrow> poly (?rp p) x = 0" unfolding rp_def ..
  have "rp p x = 0 \<longleftrightarrow> rp (\<Prod>(x, y)\<leftarrow>qis. x ^ Suc y) x = 0" unfolding sff'(1)
    unfolding rp hom_distribs using c by simp
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp (q ^ Suc i)) x = 0)"
    unfolding qs rp of_int_poly_hom.hom_prod_list poly_prod_list_zero_iff set_map by fastforce
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp q) x = 0)"
    unfolding of_int_poly_hom.hom_power poly_power_zero_iff by auto
  also have "\<dots> = (\<exists> q \<in> fst ` set qis. poly (?rp q) x = 0)" by force
  also have "\<dots> = (\<exists> q \<in> set qs. rp q x = 0)" unfolding rp qs snd_conv o_def bex_simps set_map
    by simp
  finally show iff: "rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)" by auto
  assume "rp p x = 0"
  with iff obtain q where q: "q \<in> set qs" and rtq: "rp q x = 0" by auto
  then obtain i q' where qi: "(q',i) \<in> set qis" and qq': "q = abs_int_poly q'" unfolding qs by auto
  show "\<exists>! q \<in> set qs. rp q x = 0"
  proof (intro ex1I, intro conjI, rule q, rule rtq, clarify)
    fix r
    assume "r \<in> set qs" and rtr: "rp r x = 0"
    then obtain j r' where rj: "(r',j) \<in> set qis" and rr': "r = abs_int_poly r'" unfolding qs by auto
    from rtr rtq have rtr: "rp r' x = 0" and rtq: "rp q' x = 0"
      unfolding rp rr' qq' by auto
    from rtr rtq have "[:-x,1:] dvd ?rp q'" "[:-x,1:] dvd ?rp r'" unfolding rp
      by (auto simp: poly_eq_0_iff_dvd)
    hence "[:-x,1:] dvd gcd (?rp q') (?rp r')" by simp
    hence "gcd (?rp q') (?rp r') = 0 \<or> degree (gcd (?rp q') (?rp r')) \<noteq> 0"
      by (metis is_unit_gcd_iff is_unit_iff_degree is_unit_pCons_iff one_poly_eq_simps(1))
    hence "gcd q' r' = 0 \<or> degree (gcd q' r') \<noteq> 0"
      unfolding gcd_eq_0_iff degree_of_gcd[of q' r',symmetric] by auto
    hence "\<not> coprime q' r'" by auto
    with sff(3)[OF qi rj] have "q' = r'" by auto
    thus "r = q" unfolding rr' qq' by simp
  qed
qed

lemma factors_int_poly_represents:
  fixes x :: "'a :: {field_char_0,euclidean_ring_gcd}"
  assumes p: "p represents x"
  shows "\<exists> q \<in> set (factors_of_int_poly p).
    q represents x \<and> irreducible q \<and> lead_coeff q > 0  \<and> degree q \<le> degree p"
proof -
  from representsD[OF p] have p: "p \<noteq> 0" and rt: "ipoly p x = 0" by auto
  note fact = factors_of_int_poly[OF refl]
  from fact(2)[OF p, of x] rt obtain q where q: "q \<in> set (factors_of_int_poly p)" and
    rt: "ipoly q x = 0" by auto
  from fact(1)[OF q] rt show ?thesis
    by (intro bexI[OF _ q], auto simp: represents_def irreducible_def)
qed

lemma smult_inverse_monom:"p \<noteq> 0 \<Longrightarrow> smult (inverse c) (p::rat poly) = 1 \<longleftrightarrow> p = [: c :]"
  proof (cases "c=0")
    case True thus "p \<noteq> 0 \<Longrightarrow> ?thesis" by auto
  next
    case False thus ?thesis by (metis left_inverse right_inverse smult_1 smult_1_left smult_smult)
  qed

lemma of_int_monom:"of_int_poly p = [:rat_of_int c:] \<longleftrightarrow> p = [: c :]" by (induct p, auto)

lemma degree_0_content:
  fixes p :: "int poly"
  assumes deg: "degree p = 0" shows "content p = abs (coeff p 0)"
proof-
  from deg obtain a where p: "p = [:a:]" by (auto dest: degree0_coeffs)
  show ?thesis by (auto simp: p)
qed

lemma prime_elem_imp_gcd_eq:
  fixes x::"'a:: ring_gcd"
  shows "prime_elem x \<Longrightarrow> gcd x y = normalize x \<or> gcd x y = 1"
  using prime_elem_imp_coprime [of x y]
  by (auto simp add: gcd_proj1_iff intro: coprime_imp_gcd_eq_1) 

lemma irreducible_pos_gcd:
  fixes p :: "int poly"
  assumes ir: "irreducible p" and pos: "lead_coeff p > 0" shows "gcd p q \<in> {1,p}"
proof-
  from pos have "[:sgn (lead_coeff p):] = 1" by auto
  with prime_elem_imp_gcd_eq[of p, unfolded prime_elem_iff_irreducible, OF ir, of q]
  show ?thesis by (auto simp: normalize_poly_def)
qed

lemma irreducible_pos_gcd_twice:
  fixes p q :: "int poly"
  assumes p: "irreducible p" "lead_coeff p > 0"
  and q: "irreducible q" "lead_coeff q > 0"
  shows "gcd p q = 1 \<or> p = q"
proof (cases "gcd p q = 1")
  case False note pq = this
  have "p = gcd p q" using irreducible_pos_gcd [OF p, of q] pq
    by auto
  also have "\<dots> = q" using irreducible_pos_gcd [OF q, of p] pq
    by (auto simp add: ac_simps)
  finally show ?thesis by auto
qed simp

interpretation of_rat_hom: field_hom_0' of_rat..

lemma poly_zero_imp_not_unit:
  assumes "poly p x = 0" shows "\<not> p dvd 1"
proof (rule notI)
  assume "p dvd 1"
  from poly_hom.hom_dvd_1[OF this] have "poly p x dvd 1" by auto
  with assms show False by auto
qed

lemma poly_prod_mset_zero_iff:
  fixes x :: "'a :: idom"
  shows "poly (prod_mset F) x = 0 \<longleftrightarrow> (\<exists>f \<in># F. poly f x = 0)"
  by (induct F, auto simp: poly_mult_zero_iff)

lemma algebraic_imp_represents_irreducible:
  fixes x :: "'a :: field_char_0"
  assumes "algebraic x"
  shows "\<exists>p. p represents x \<and> irreducible p"
proof -
  from assms obtain p
  where px0: "ipoly p x = 0" and p0: "p \<noteq> 0" unfolding algebraic_altdef_ipoly by auto
  from poly_zero_imp_not_unit[OF px0]
  have "\<not> p dvd 1" by (auto dest: of_int_poly_hom.hom_dvd_1[where 'a = 'a])
  from mset_factors_exist[OF p0 this]
  obtain F where F: "mset_factors F p" by auto
  then have "p = prod_mset F" by auto
  also have "(of_int_poly ... :: 'a poly) = prod_mset (image_mset of_int_poly F)" by simp
  finally have "poly ... x = 0" using px0 by auto
  from this[unfolded poly_prod_mset_zero_iff]
  obtain f where "f \<in># F" and fx0: "ipoly f x = 0" by auto
  with F have "irreducible f" by auto
  with fx0 show ?thesis by auto
qed

lemma algebraic_imp_represents_irreducible_cf_pos:
  assumes "algebraic (x::'a::field_char_0)"
  shows "\<exists>p. p represents x \<and> irreducible p \<and> lead_coeff p > 0 \<and> primitive p"
proof -
  from algebraic_imp_represents_irreducible[OF assms(1)]
  obtain p where px: "p represents x" and irr: "irreducible p" by auto
  let ?p = "cf_pos_poly p"
  from px irr represents_imp_degree
  have 1: "?p represents x" and 2: "irreducible ?p" and 3: "cf_pos ?p"
    by (auto intro: irreducible_cf_pos_poly)
  then show ?thesis by (auto intro: exI[of _ ?p] simp: cf_pos_def)
qed

lemma gcd_of_int_poly: "gcd (of_int_poly f) (of_int_poly g :: 'a :: {field_char_0,euclidean_ring_gcd} poly) =
  smult (inverse (of_int (lead_coeff (gcd f g)))) (of_int_poly (gcd f g))"
proof -
  let ?ia = "of_int_poly :: _ \<Rightarrow> 'a poly"
  let ?ir = "of_int_poly :: _ \<Rightarrow> rat poly"
  let ?ra = "map_poly of_rat :: _ \<Rightarrow> 'a poly"
  have id: "?ia x = ?ra (?ir x)" for x by (subst map_poly_map_poly, auto)
  show ?thesis
    unfolding id
    unfolding of_rat_hom.map_poly_gcd[symmetric]
    unfolding gcd_rat_to_gcd_int by (auto simp: hom_distribs)
qed

lemma algebraic_imp_represents_unique:
  fixes x :: "'a :: {field_char_0,euclidean_ring_gcd}"
  assumes "algebraic x"
  shows "\<exists>! p. p represents x \<and> irreducible p \<and> lead_coeff p > 0" (is "Ex1 ?p")
proof -
  from assms obtain p
  where p: "?p p" and cfp: "cf_pos p"
    by (auto simp: cf_pos_def dest: algebraic_imp_represents_irreducible_cf_pos)
  show ?thesis
  proof (rule ex1I)
    show "?p p" by fact
    fix q
    assume q: "?p q"
    then have "q represents x" by auto
    from represents_imp_degree[OF this] q irreducible_content[of q]
    have cfq: "cf_pos q" by (auto simp: cf_pos_def)
    show "q = p"
    proof (rule ccontr)
      let ?ia = "map_poly of_int :: int poly \<Rightarrow> 'a poly"
      assume "q \<noteq> p"
      with irreducible_pos_gcd_twice[of p q] p q cfp cfq have gcd: "gcd p q = 1" by auto
      from p q have rt: "ipoly p x = 0" "ipoly q x = 0" unfolding represents_def by auto
      define c :: 'a where "c = inverse (of_int (lead_coeff (gcd p q)))"
      have rt: "poly (?ia p) x = 0" "poly (?ia q) x = 0" using rt by auto
      hence "[:-x,1:] dvd ?ia p" "[:-x,1:] dvd ?ia q"
        unfolding poly_eq_0_iff_dvd by auto
      hence "[:-x,1:] dvd gcd (?ia p) (?ia q)" by (rule gcd_greatest)
      also have "\<dots> = smult c (?ia (gcd p q))" unfolding gcd_of_int_poly c_def ..
      also have "?ia (gcd p q) = 1" by (simp add: gcd)
      also have "smult c 1 = [: c :]" by simp
      finally show False using c_def gcd by (simp add: dvd_iff_poly_eq_0)
    qed
  qed
qed

corollary irreducible_represents_imp_degree:
  fixes x :: "'a :: {field_char_0,euclidean_ring_gcd}"
  assumes "irreducible f" and "f represents x" and "g represents x"
  shows "degree f \<le> degree g"
proof -
  from factors_of_int_poly(1)[OF refl, of _ g] factors_of_int_poly(3)[OF refl, of g x]
     assms(3) obtain h where *: "h represents x" "degree h \<le> degree g" "irreducible h"
    by blast
  let ?af = "abs_int_poly f"
  let ?ah = "abs_int_poly h"
  from assms have af: "irreducible ?af" "?af represents x" "lead_coeff ?af > 0" by fastforce+
  from * have ah: "irreducible ?ah" "?ah represents x" "lead_coeff ?ah > 0" by fastforce+
  from algebraic_imp_represents_unique[of x] af ah have id: "?af = ?ah"
    unfolding algebraic_iff_represents by blast
  show ?thesis using arg_cong[OF id, of degree] \<open>degree h \<le> degree g\<close> by simp
qed

lemma ipoly_poly_compose:
  fixes x :: "'a :: idom"
  shows "ipoly (p \<circ>\<^sub>p q) x = ipoly p (ipoly q x)"
proof (induct p)
  case (pCons a p)
  have "ipoly ((pCons a p) \<circ>\<^sub>p q) x = of_int a + ipoly (q * p \<circ>\<^sub>p q) x" by (simp add: hom_distribs)
  also have "ipoly (q * p \<circ>\<^sub>p q) x = ipoly q x * ipoly (p \<circ>\<^sub>p q) x" by (simp add: hom_distribs)
  also have "ipoly (p \<circ>\<^sub>p q) x = ipoly p (ipoly q x)" unfolding pCons(2) ..
  also have "of_int a + ipoly q x * \<dots> = ipoly (pCons a p) (ipoly q x)"
    unfolding map_poly_pCons[OF pCons(1)] by simp
  finally show ?case .
qed simp

text \<open>Polynomial for unary minus.\<close>

definition poly_uminus :: "'a :: ring_1 poly \<Rightarrow> 'a poly" where [code del]:
  "poly_uminus p \<equiv> \<Sum>i\<le>degree p. monom ((-1)^i * coeff p i) i"

lemma poly_uminus_pCons_pCons[simp]:
  "poly_uminus (pCons a (pCons b p)) = pCons a (pCons (-b) (poly_uminus p))" (is "?l = ?r")
proof(cases "p = 0")
  case False
  then have deg: "degree (pCons a (pCons b p)) = Suc (Suc (degree p))" by simp
  show ?thesis
  by (unfold poly_uminus_def deg sum.atMost_Suc_shift monom_Suc monom_0 sum_pCons_0_commute, simp)
next
  case True
  then show ?thesis by (auto simp add: poly_uminus_def monom_0 monom_Suc)
qed

fun poly_uminus_inner :: "'a :: ring_1 list \<Rightarrow> 'a poly"
where "poly_uminus_inner [] = 0"
  |   "poly_uminus_inner [a] = [:a:]"
  |   "poly_uminus_inner (a#b#cs) = pCons a (pCons (-b) (poly_uminus_inner cs))"

lemma poly_uminus_code[code,simp]: "poly_uminus p = poly_uminus_inner (coeffs p)"
proof-
  have "poly_uminus (Poly as) = poly_uminus_inner as" for as :: "'a list"
  proof (induct "length as" arbitrary:as rule: less_induct)
    case less
    show ?case
    proof(cases as)
      case Nil
      then show ?thesis by (simp add: poly_uminus_def)
    next
      case [simp]: (Cons a bs)
      show ?thesis
      proof (cases bs)
        case Nil
        then show ?thesis by (simp add: poly_uminus_def monom_0)
      next
        case [simp]: (Cons b cs)
        show ?thesis by (simp add: less)
      qed
    qed
  qed
  from this[of "coeffs p"]
  show ?thesis by simp
qed

lemma poly_uminus_inner_0[simp]: "poly_uminus_inner as = 0 \<longleftrightarrow> Poly as = 0"
  by (induct as rule: poly_uminus_inner.induct, auto)

lemma degree_poly_uminus_inner[simp]: "degree (poly_uminus_inner as) = degree (Poly as)"
  by (induct as rule: poly_uminus_inner.induct, auto)

lemma ipoly_uminus_inner[simp]:
  "ipoly (poly_uminus_inner as) (x::'a::comm_ring_1) = ipoly (Poly as) (-x)"
  by (induct as rule: poly_uminus_inner.induct, auto simp: hom_distribs ring_distribs)

lemma represents_uminus: assumes alg: "p represents x"
  shows "(poly_uminus p) represents (-x)"
proof -
  from representsD[OF alg] have "p \<noteq> 0" and rp: "ipoly p x = 0" by auto
  hence 0: "poly_uminus p \<noteq> 0" by simp
  show ?thesis
    by (rule representsI[OF _ 0], insert rp, auto)
qed


lemma content_poly_uminus_inner[simp]:
  fixes as :: "'a :: ring_gcd list"
  shows "content (poly_uminus_inner as) = content (Poly as)"
  by (induct as rule: poly_uminus_inner.induct, auto)


text \<open>Multiplicative inverse is represented by @{const reflect_poly}.\<close>

lemma inverse_pow_minus: assumes "x \<noteq> (0 :: 'a :: field)"
  and "i \<le> n"
  shows "inverse x ^ n * x ^ i = inverse x ^ (n - i)"
  using assms by (simp add: field_class.field_divide_inverse power_diff power_inverse)

lemma (in inj_idom_hom) reflect_poly_hom:
  "reflect_poly (map_poly hom p) = map_poly hom (reflect_poly p)"
proof -
  obtain xs where xs: "rev (coeffs p) = xs" by auto
  show ?thesis unfolding reflect_poly_def coeffs_map_poly_hom rev_map
    xs by (induct xs, auto simp: hom_distribs)
qed

lemma ipoly_reflect_poly: assumes x: "(x :: 'a :: field_char_0) \<noteq> 0"
  shows "ipoly (reflect_poly p) x = x ^ (degree p) * ipoly p (inverse x)" (is "?l = ?r")
proof -
  let ?or = "of_int :: int \<Rightarrow> 'a"
  have hom: "inj_idom_hom ?or" ..
  show ?thesis
    using poly_reflect_poly_nz[OF x, of "map_poly ?or p"] by (simp add: inj_idom_hom.reflect_poly_hom[OF hom])
qed

lemma represents_inverse: assumes x: "x \<noteq> 0"
  and alg: "p represents x"
  shows "(reflect_poly p) represents (inverse x)"
proof (intro representsI)
  from representsD[OF alg] have "p \<noteq> 0" and rp: "ipoly p x = 0" by auto
  then show "reflect_poly p \<noteq> 0" by simp
  show "ipoly (reflect_poly p) (inverse x) = 0" by (subst ipoly_reflect_poly, insert x, auto simp:rp)
qed

lemma inverse_roots: assumes x: "(x :: 'a :: field_char_0) \<noteq> 0"
  shows "ipoly (reflect_poly p) x = 0 \<longleftrightarrow> ipoly p (inverse x) = 0"
  using x by (auto simp: ipoly_reflect_poly)

context
  fixes n :: nat
begin
text \<open>Polynomial for n-th root.\<close>

definition poly_nth_root :: "'a :: idom poly \<Rightarrow> 'a poly" where
  "poly_nth_root p = p \<circ>\<^sub>p monom 1 n"

lemma ipoly_nth_root:
  fixes x :: "'a :: idom"
  shows "ipoly (poly_nth_root p) x = ipoly p (x ^ n)"
  unfolding poly_nth_root_def ipoly_poly_compose by (simp add: map_poly_monom poly_monom)

context
  assumes n: "n \<noteq> 0"
begin
lemma poly_nth_root_0[simp]: "poly_nth_root p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_nth_root_def
  by (rule pcompose_eq_0, insert n, auto simp: degree_monom_eq)

lemma represents_nth_root:
  assumes y: "y^n = x" and alg: "p represents x"
  shows "(poly_nth_root p) represents y"
proof -
  from representsD[OF alg] have "p \<noteq> 0" and rp: "ipoly p x = 0" by auto
  hence 0: "poly_nth_root p \<noteq> 0" by simp
  show ?thesis
    by (rule representsI[OF _ 0], unfold ipoly_nth_root y rp, simp)
qed

lemma represents_nth_root_odd_real:
  assumes alg: "p represents x" and odd: "odd n"
  shows "(poly_nth_root p) represents (root n x)"
  by (rule represents_nth_root[OF odd_real_root_pow[OF odd] alg])

lemma represents_nth_root_pos_real:
  assumes alg: "p represents x" and pos: "x > 0"
  shows "(poly_nth_root p) represents (root n x)"
proof -
  from n have id: "Suc (n - 1) = n" by auto
  show ?thesis
  proof (rule represents_nth_root[OF _ alg])
    show "root n x ^ n = x" using id pos by auto
  qed
qed

lemma represents_nth_root_neg_real:
  assumes alg: "p represents x" and neg: "x < 0"
  shows "(poly_uminus (poly_nth_root (poly_uminus p))) represents (root n x)"
proof -
  have rt: "root n x = - root n (-x)" unfolding real_root_minus by simp
  show ?thesis unfolding rt
    by (rule represents_uminus[OF represents_nth_root_pos_real[OF represents_uminus[OF alg]]], insert neg, auto)
qed
end
end

lemma represents_csqrt:
  assumes alg: "p represents x" shows "(poly_nth_root 2 p) represents (csqrt x)"
  by (rule represents_nth_root[OF _ _ alg], auto)

lemma represents_sqrt:
  assumes alg: "p represents x" and pos: "x \<ge> 0"
  shows "(poly_nth_root 2 p) represents (sqrt x)"
  by (rule represents_nth_root[OF _ _ alg], insert pos, auto)

lemma represents_degree:
  assumes "p represents x" shows "degree p \<noteq> 0"
proof
  assume "degree p = 0"
  from degree0_coeffs[OF this] obtain c where p: "p = [:c:]" by auto
  from assms[unfolded represents_def p]
  show False by auto
qed


text \<open>Polynomial for multiplying a rational number with an algebraic number.\<close>

definition poly_mult_rat_main where
  "poly_mult_rat_main n d (f :: 'a :: idom poly) = (let fs = coeffs f; k = length fs in
    poly_of_list (map (\<lambda> (fi, i). fi * d ^ i * n ^ (k - Suc i)) (zip fs [0 ..< k])))"

definition poly_mult_rat :: "rat \<Rightarrow> int poly \<Rightarrow> int poly" where
  "poly_mult_rat r p \<equiv> case quotient_of r of (n,d) \<Rightarrow> poly_mult_rat_main n d p"

lemma coeff_poly_mult_rat_main: "coeff (poly_mult_rat_main n d f) i = coeff f i * n ^ (degree f - i) * d ^ i"
proof -
  have id: "coeff (poly_mult_rat_main n d f) i = (coeff f i * d ^ i) * n ^ (length (coeffs f) - Suc i)"
    unfolding poly_mult_rat_main_def Let_def poly_of_list_def coeff_Poly
    unfolding nth_default_coeffs_eq[symmetric]
    unfolding nth_default_def by auto
  show ?thesis unfolding id by (simp add: degree_eq_length_coeffs)
qed

lemma degree_poly_mult_rat_main: "n \<noteq> 0 \<Longrightarrow> degree (poly_mult_rat_main n d f) = (if d = 0 then 0 else degree f)"
proof (cases "d = 0")
  case True
  thus ?thesis unfolding degree_def unfolding coeff_poly_mult_rat_main by simp
next
  case False
  hence id: "(d = 0) = False" by simp
  show "n \<noteq> 0 \<Longrightarrow> ?thesis" unfolding degree_def coeff_poly_mult_rat_main id
    by (simp add: id)
qed

lemma ipoly_mult_rat_main:
  fixes x :: "'a :: {field,ring_char_0}"
  assumes "d \<noteq> 0" and "n \<noteq> 0"
  shows "ipoly (poly_mult_rat_main n d p) x = of_int n ^ degree p * ipoly p (x * of_int d / of_int n)"
proof -
  from assms have d: "(if d = 0 then t else f) = f" for t f :: 'b by simp
  show ?thesis
    unfolding poly_altdef of_int_hom.coeff_map_poly_hom mult.assoc[symmetric] of_int_mult[symmetric]
      sum_distrib_left
    unfolding of_int_hom.degree_map_poly_hom degree_poly_mult_rat_main[OF assms(2)] d
  proof (rule sum.cong[OF refl])
    fix i
    assume "i \<in> {..degree p}"
    hence i: "i \<le> degree p" by auto
    hence id: "of_int n ^ (degree p - i) = (of_int n ^ degree p / of_int n ^ i :: 'a)"
      by (simp add: assms(2) power_diff)
    thus "of_int (coeff (poly_mult_rat_main n d p) i) * x ^ i = of_int n ^ degree p * of_int (coeff p i) * (x * of_int d / of_int n) ^ i"
      unfolding coeff_poly_mult_rat_main
      by (simp add: field_simps)
  qed
qed

lemma degree_poly_mult_rat[simp]: assumes "r \<noteq> 0" shows "degree (poly_mult_rat r p) = degree p"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" by auto
  with assms r have n0: "n \<noteq> 0" by simp
  from quot have id: "poly_mult_rat r p = poly_mult_rat_main n d p"  unfolding poly_mult_rat_def by simp
  show ?thesis unfolding id degree_poly_mult_rat_main[OF n0] using d by simp
qed

lemma ipoly_mult_rat:
  assumes r0: "r \<noteq> 0"
  shows "ipoly (poly_mult_rat r p) x = of_int (fst (quotient_of r)) ^ degree p * ipoly p (x * inverse (of_rat r))"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" by auto
  from r r0 have n: "n \<noteq> 0" by simp
  from r d n have inv: "of_int d / of_int n = inverse r" by simp
  from quot have id: "poly_mult_rat r p = poly_mult_rat_main n d p"  unfolding poly_mult_rat_def by simp
  show ?thesis unfolding id ipoly_mult_rat_main[OF d n] quot fst_conv of_rat_inverse[symmetric] inv[symmetric]
    by (simp add: of_rat_divide)
qed

lemma poly_mult_rat_main_0[simp]:
  assumes "n \<noteq> 0" "d \<noteq> 0" shows "poly_mult_rat_main n d p = 0 \<longleftrightarrow> p = 0"
proof
  assume "p = 0" thus "poly_mult_rat_main n d p = 0"
    by (simp add: poly_mult_rat_main_def)
next
  assume 0: "poly_mult_rat_main n d p = 0"
  {
    fix i
    from 0 have "coeff (poly_mult_rat_main n d p) i = 0" by simp
    hence "coeff p i = 0" unfolding coeff_poly_mult_rat_main using assms by simp
  }
  thus "p = 0" by (intro poly_eqI, auto)
qed


lemma poly_mult_rat_0[simp]: assumes r0: "r \<noteq> 0" shows "poly_mult_rat r p = 0 \<longleftrightarrow> p = 0"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" by auto
  from r r0 have n: "n \<noteq> 0" by simp
  from quot have id: "poly_mult_rat r p = poly_mult_rat_main n d p"  unfolding poly_mult_rat_def by simp
  show ?thesis unfolding id using n d by simp
qed

lemma represents_mult_rat:
  assumes r: "r \<noteq> 0" and "p represents x" shows "(poly_mult_rat r p) represents (of_rat r * x)"
  using assms
  unfolding represents_def ipoly_mult_rat[OF r] by (simp add: field_simps)

text \<open>Polynomial for adding a rational number on an algebraic number.
  Again, we do not have to factor afterwards.\<close>

definition poly_add_rat :: "rat \<Rightarrow> int poly \<Rightarrow> int poly" where
  "poly_add_rat r p \<equiv> case quotient_of r of (n,d) \<Rightarrow>
     (poly_mult_rat_main d 1 p \<circ>\<^sub>p [:-n,d:])"

lemma poly_add_rat_code[code]: "poly_add_rat r p \<equiv> case quotient_of r of (n,d) \<Rightarrow>
     let p' = (let fs = coeffs p; k = length fs in poly_of_list (map (\<lambda>(fi, i). fi * d ^ (k - Suc i)) (zip fs [0..<k])));
         p'' = p' \<circ>\<^sub>p [:-n,d:]
      in p''"
  unfolding poly_add_rat_def poly_mult_rat_main_def Let_def by simp

lemma degree_poly_add_rat[simp]: "degree (poly_add_rat r p) = degree p"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" "d > 0" by auto
  show ?thesis unfolding poly_add_rat_def quot split
    by (simp add: degree_poly_mult_rat_main d)
qed

lemma ipoly_add_rat: "ipoly (poly_add_rat r p) x = (of_int (snd (quotient_of r)) ^ degree p) * ipoly p (x - of_rat r)"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" "d > 0" by auto
  have id: "ipoly [:- n, 1:] (x / of_int d :: 'a) = - of_int n + x / of_int d" by simp
  show ?thesis unfolding poly_add_rat_def quot split
    by (simp add: ipoly_mult_rat_main ipoly_poly_compose d r degree_poly_mult_rat_main field_simps id of_rat_divide)
qed

lemma poly_add_rat_0[simp]: "poly_add_rat r p = 0 \<longleftrightarrow> p = 0"
proof -
  obtain n d where quot: "quotient_of r = (n,d)" by force
  from quotient_of_div[OF quot] have r: "r = of_int n / of_int d" by auto
  from quotient_of_denom_pos[OF quot] have d: "d \<noteq> 0" "d > 0" by auto
  show ?thesis unfolding poly_add_rat_def quot split
    by (simp add: d pcompose_eq_0)
qed

lemma add_rat_roots: "ipoly (poly_add_rat r p) x = 0 \<longleftrightarrow> ipoly p (x - of_rat r) = 0"
  unfolding ipoly_add_rat using quotient_of_nonzero by auto

lemma represents_add_rat:
  assumes "p represents x" shows "(poly_add_rat r p) represents (of_rat r + x)"
  using assms unfolding represents_def ipoly_add_rat by simp

(* TODO: move? *)
lemmas pos_mult[simplified,simp] = mult_less_cancel_left_pos[of _ 0] mult_less_cancel_left_pos[of _ _ 0]

lemma ipoly_add_rat_pos_neg:
  "ipoly (poly_add_rat r p) (x::'a::linordered_field) < 0 \<longleftrightarrow> ipoly p (x - of_rat r) < 0"
  "ipoly (poly_add_rat r p) (x::'a::linordered_field) > 0 \<longleftrightarrow> ipoly p (x - of_rat r) > 0"
  using quotient_of_nonzero unfolding ipoly_add_rat by auto

lemma sgn_ipoly_add_rat[simp]:
  "sgn (ipoly (poly_add_rat r p) (x::'a::linordered_field)) = sgn (ipoly p (x - of_rat r))" (is "sgn ?l = sgn ?r")
  using ipoly_add_rat_pos_neg[of r p x]
  by (cases ?r "0::'a" rule: linorder_cases,auto simp:  sgn_1_pos sgn_1_neg sgn_eq_0_iff)


lemma irreducible_preservation:
  fixes x :: "'a :: {field_char_0,euclidean_ring_gcd}"
  assumes irr: "irreducible p"
  and x: "p represents x"
  and y: "q represents y"
  and deg: "degree p \<ge> degree q"
  and f: "\<And> q. q represents y \<Longrightarrow> (f q) represents x \<and> degree (f q) \<le> degree q"
  and pr: "primitive q"
  shows "irreducible q"
proof (rule ccontr)
  define pp where "pp = abs_int_poly p"
  have dp: "degree p \<noteq> 0" using x by (rule represents_degree)
  have dq: "degree q \<noteq> 0" using y by (rule represents_degree)
  from dp have p0: "p \<noteq> 0" by auto
  from x deg irr p0
  have irr: "irreducible pp" and x: "pp represents x" and
    deg: "degree pp \<ge> degree q" and cf_pos: "lead_coeff pp > 0"
    unfolding pp_def lead_coeff_abs_int_poly by (auto intro!: representsI)
  from x have ax: "algebraic x" unfolding algebraic_altdef_ipoly represents_def by blast
  assume "\<not> ?thesis"
  from this irreducible_connect_int[of q] pr have "\<not> irreducible\<^sub>d q" by auto
  from this dq obtain r where
    r: "degree r \<noteq> 0" "degree r < degree q" and "r dvd q" by auto
  then obtain rr where q: "q = r * rr" unfolding dvd_def by auto
  have "degree q = degree r + degree rr" using dq unfolding q
    by (subst degree_mult_eq, auto)
  with r have rr: "degree rr \<noteq> 0" "degree rr < degree q" by auto
  from representsD(2)[OF y, unfolded q hom_distribs]
  have "ipoly r y = 0 \<or> ipoly rr y = 0" by auto
  with r rr have "r represents y \<or> rr represents y" unfolding represents_def by auto
  with r rr obtain r where r: "r represents y" "degree r < degree q" by blast
  from f[OF r(1)] deg r(2) obtain r where r: "r represents x" "degree r < degree pp" by auto
  from factors_int_poly_represents[OF r(1)] r(2) obtain r where
    r: "r represents x" "irreducible r" "lead_coeff r > 0" and deg: "degree r < degree pp" by force
  from algebraic_imp_represents_unique[OF ax] r irr cf_pos x have "r = pp" by auto
  with deg show False by auto
qed

lemma deg_nonzero_represents:
  assumes deg: "degree p \<noteq> 0" shows "\<exists> x :: complex. p represents x"
proof -
  let ?p = "of_int_poly p :: complex poly"
  from fundamental_theorem_algebra_factorized[of ?p]
  obtain as c where id: "smult c (\<Prod>a\<leftarrow>as. [:- a, 1:]) = ?p"
    and len: "length as = degree ?p" by blast
  have "degree ?p = degree p" by simp
  with deg len obtain b bs where as: "as = b # bs" by (cases as, auto)
  have "p represents b" unfolding represents_def id[symmetric] as using deg by auto
  thus ?thesis by blast
qed

declare irreducible_const_poly_iff [simp]

lemma poly_uminus_irreducible:
  assumes p: "irreducible (p :: int poly)" and deg: "degree p \<noteq> 0"
  shows "irreducible (poly_uminus p)"
proof-
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_uminus[OF x]
  have y: "poly_uminus p represents (- x)" .
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force)
    from deg irreducible_imp_primitive[OF p] have "primitive p" by auto
    then show "primitive (poly_uminus p)" by simp
    fix q
    assume "q represents (- x)"
    from represents_uminus[OF this] have "(poly_uminus q) represents x" by simp
    thus "(poly_uminus q) represents x \<and> degree (poly_uminus q) \<le> degree q" by auto
  qed
qed

lemma reflect_poly_irreducible:
  fixes x :: "'a :: {field_char_0,euclidean_ring_gcd}"
  assumes p: "irreducible p" and x: "p represents x" and x0: "x \<noteq> 0"
  shows "irreducible (reflect_poly p)"
proof -
  from represents_inverse[OF x0 x]
  have y: "(reflect_poly p) represents (inverse x)" by simp
  from x0 have ix0: "inverse x \<noteq> 0" by auto
  show ?thesis
  proof (rule irreducible_preservation[OF p x y])
    from x irreducible_imp_primitive[OF p]
    show "primitive (reflect_poly p)" by (auto simp: content_reflect_poly)
    fix q
    assume "q represents (inverse x)"
    from represents_inverse[OF ix0 this] have "(reflect_poly q) represents x" by simp
    with degree_reflect_poly_le
    show "(reflect_poly q) represents x \<and> degree (reflect_poly q) \<le> degree q" by auto
  qed (insert p, auto simp: degree_reflect_poly_le)
qed

lemma poly_add_rat_irreducible:
  assumes p: "irreducible p" and deg: "degree p \<noteq> 0"
  shows "irreducible (cf_pos_poly (poly_add_rat r p))"
proof -
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_add_rat[OF x]
  have y: "cf_pos_poly (poly_add_rat r p) represents (of_rat r + x)" by simp
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force)
    fix q
    assume "q represents (of_rat r + x)"
    from represents_add_rat[OF this, of "- r"] have "(poly_add_rat (- r) q) represents x" by (simp add: of_rat_minus)
    thus "(poly_add_rat (- r) q) represents x \<and> degree (poly_add_rat (- r) q) \<le> degree q" by auto
  qed (insert p, auto)
qed

lemma poly_mult_rat_irreducible:
  assumes p: "irreducible p" and deg: "degree p \<noteq> 0" and r: "r \<noteq> 0"
  shows "irreducible (cf_pos_poly (poly_mult_rat r p))"
proof -
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_mult_rat[OF r x]
  have y: "cf_pos_poly (poly_mult_rat r p) represents (of_rat r * x)" by simp
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force simp: r)
    fix q
    from r have r': "inverse r \<noteq> 0" by simp
    assume "q represents (of_rat r * x)"
    from represents_mult_rat[OF r' this] have "(poly_mult_rat (inverse r) q) represents x" using r
      by (simp add: of_rat_divide field_simps)
    thus "(poly_mult_rat (inverse r) q) represents x \<and> degree (poly_mult_rat (inverse r) q) \<le> degree q"
      using r by auto
  qed (insert p r, auto)
qed

end
