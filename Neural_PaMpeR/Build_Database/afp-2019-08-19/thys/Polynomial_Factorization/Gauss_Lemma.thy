(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
(*TODO: Rename! *)
section \<open>Gauss Lemma\<close>

text \<open>We formalized Gauss Lemma, that the content of a product of two polynomials $p$ and $q$
  is the product of the contents of $p$ and $q$. As a corollary we provide an algorithm
  to convert a rational factor of an integer polynomial into an integer factor.
  
  In contrast to the theory on unique factorization domains -- where Gauss Lemma is also proven 
   in a more generic setting --
  we are here in an executable setting and do not use the unspecified $some-gcd$ function.
  Moreover, there is a slight difference in the definition of content: in this theory it is only
  defined for integer-polynomials, whereas in the UFD theory, the content is defined for 
  polynomials in the fraction field.\<close>

theory Gauss_Lemma
imports 
  "HOL-Computational_Algebra.Primes"
  Polynomial_Interpolation.Ring_Hom_Poly
  Missing_Polynomial_Factorial
begin

lemma primitive_part_alt_def:
  "primitive_part p = sdiv_poly p (content p)"
  by (simp add: primitive_part_def sdiv_poly_def)

definition common_denom :: "rat list \<Rightarrow> int \<times> int list" where
  "common_denom xs \<equiv> let 
     nds = map quotient_of xs;
     denom = list_lcm (map snd nds);
     ints = map (\<lambda> (n,d). n * denom div d) nds
   in (denom, ints)"

definition rat_to_int_poly :: "rat poly \<Rightarrow> int \<times> int poly" where
  "rat_to_int_poly p \<equiv> let
     ais = coeffs p;
     d = fst (common_denom ais)
   in (d, map_poly (\<lambda> x. case quotient_of x of (p,q) \<Rightarrow> p * d div q) p)"

definition rat_to_normalized_int_poly :: "rat poly \<Rightarrow> rat \<times> int poly" where
  "rat_to_normalized_int_poly p \<equiv> if p = 0 then (1,0) else case rat_to_int_poly p of (s,q)
    \<Rightarrow> (of_int (content q) / of_int s, primitive_part q)"

lemma rat_to_normalized_int_poly_code[code]:
  "rat_to_normalized_int_poly p = (if p = 0 then (1,0) else case rat_to_int_poly p of (s,q)
    \<Rightarrow> let c = content q in (of_int c / of_int s, sdiv_poly q c))"
    unfolding Let_def rat_to_normalized_int_poly_def primitive_part_alt_def ..

lemma common_denom: assumes cd: "common_denom xs = (dd,ys)"
  shows "xs = map (\<lambda> i. of_int i / of_int dd) ys" "dd > 0"
  "\<And>x. x \<in> set xs \<Longrightarrow> rat_of_int (case quotient_of x of (n, x) \<Rightarrow> n * dd div x) / rat_of_int dd = x"
proof -
  let ?nds = "map quotient_of xs"
  define nds where "nds = ?nds"
  let ?denom = "list_lcm (map snd nds)"
  let ?ints = "map (\<lambda> (n,d). n * dd div d) nds"
  from cd[unfolded common_denom_def Let_def]
  have dd: "dd = ?denom" and ys: "ys = ?ints" unfolding nds_def by auto
  show dd0: "dd > 0" unfolding dd 
    by (intro list_lcm_pos(3), auto simp: nds_def quotient_of_nonzero)
  {
    fix x
    assume x: "x \<in> set xs"
    obtain p q where quot: "quotient_of x = (p,q)" by force
    from x have "(p,q) \<in> set nds" unfolding nds_def using quot by force
    hence "q \<in> set (map snd nds)" by force
    from list_lcm[OF this] have q: "q dvd dd" unfolding dd .
    show "rat_of_int (case quotient_of x of (n, x) \<Rightarrow> n * dd div x) / rat_of_int dd = x"
      unfolding quot split unfolding quotient_of_div[OF quot]  
    proof -
      have f1: "q * (dd div q) = dd"
        using dvd_mult_div_cancel q by blast
      have "rat_of_int (dd div q) \<noteq> 0"
        using dd0 dvd_mult_div_cancel q by fastforce
      thus "rat_of_int (p * dd div q) / rat_of_int dd = rat_of_int p / rat_of_int q"
        using f1 by (metis (no_types) div_mult_swap mult_divide_mult_cancel_right of_int_mult q)
    qed
  } note main = this
  show "xs = map (\<lambda> i. of_int i / of_int dd) ys" unfolding ys map_map o_def nds_def
    by (rule sym, rule map_idI, rule main)
qed

lemma rat_to_int_poly: assumes "rat_to_int_poly p = (d,q)"
  shows "p = smult (inverse (of_int d)) (map_poly of_int q)" "d > 0"
proof -
  let ?f = "\<lambda> x. case quotient_of x of (pa, x) \<Rightarrow> pa * d div x"
  define f where "f = ?f"
  from assms[unfolded rat_to_int_poly_def Let_def] 
    obtain xs where cd: "common_denom (coeffs p) = (d,xs)"
    and q: "q = map_poly f p" unfolding f_def by (cases "common_denom (coeffs p)", auto)
  from common_denom[OF cd] have d: "d > 0"  and 
    id: "\<And> x. x \<in> set (coeffs p) \<Longrightarrow> rat_of_int (f x) / rat_of_int d = x" 
    unfolding f_def by auto
  have f0: "f 0 = 0" unfolding f_def by auto
  have id: "rat_of_int (f (coeff p n)) / rat_of_int d = coeff p n" for n
    using id[of "coeff p n"] f0 range_coeff by (cases "coeff p n = 0", auto)
  show "d > 0" by fact
  show "p = smult (inverse (of_int d)) (map_poly of_int q)"
    unfolding q smult_as_map_poly using id f0
    by (intro poly_eqI, auto simp: field_simps coeff_map_poly)
qed

lemma content_ge_0_int: "content p \<ge> (0 :: int)"
  unfolding content_def
  by (cases "coeffs p", auto)

lemma abs_content_int[simp]: fixes p :: "int poly"
  shows "abs (content p) = content p" using content_ge_0_int[of p] by auto

lemma content_smult_int: fixes p :: "int poly" 
  shows "content (smult a p) = abs a * content p" by simp

lemma normalize_non_0_smult: "\<exists> a. (a :: 'a :: semiring_gcd) \<noteq> 0 \<and> smult a (primitive_part p) = p"
  by (cases "p = 0", rule exI[of _ 1], simp, rule exI[of _ "content p"], auto)

lemma rat_to_normalized_int_poly: assumes "rat_to_normalized_int_poly p = (d,q)"
  shows "p = smult d (map_poly of_int q)" "d > 0" "p \<noteq> 0 \<Longrightarrow> content q = 1" "degree q = degree p"
proof -
  have "p = smult d (map_poly of_int q) \<and> d > 0 \<and> (p \<noteq> 0 \<longrightarrow> content q = 1)"
  proof (cases "p = 0")
    case True
    thus ?thesis using assms unfolding rat_to_normalized_int_poly_def
      by (auto simp: eval_poly_def)
  next
    case False
    hence p0: "p \<noteq> 0" by auto
    obtain s r where id: "rat_to_int_poly p = (s,r)" by force
    let ?cr = "rat_of_int (content r)"
    let ?s = "rat_of_int s"
    let ?q = "map_poly rat_of_int q"
    from rat_to_int_poly[OF id] have p: "p = smult (inverse ?s) (map_poly of_int r)"
    and s: "s > 0" by auto
    let ?q = "map_poly rat_of_int q"
    from p0 assms[unfolded rat_to_normalized_int_poly_def id split]
    have d: "d = ?cr / ?s" and q: "q = primitive_part r" by auto
    from content_times_primitive_part[of r, folded q] have qr: "smult (content r) q = r" .
    have "smult d ?q = smult (?cr / ?s) ?q"
      unfolding d by simp
    also have "?cr / ?s = ?cr * inverse ?s" by (rule divide_inverse)
    also have "\<dots> = inverse ?s * ?cr" by simp
    also have "smult (inverse ?s * ?cr) ?q = smult (inverse ?s) (smult ?cr ?q)" by simp
    also have "smult ?cr ?q = map_poly of_int (smult (content r) q)" by (simp add: hom_distribs)
    also have "\<dots> = map_poly of_int r" unfolding qr ..
    finally have pq: "p = smult d ?q" unfolding p by simp
    from p p0 have r0: "r \<noteq> 0" by auto
    from content_eq_zero_iff[of r] content_ge_0_int[of r] r0 have cr: "?cr > 0" by linarith
    with s have d0: "d > 0" unfolding d by auto
    from content_primitive_part[OF r0] have cq: "content q = 1" unfolding q .
    from pq d0 cq show ?thesis by auto
  qed
  thus p: "p = smult d (map_poly of_int q)" and d: "d > 0" and "p \<noteq> 0 \<Longrightarrow> content q = 1" by auto
  show "degree q = degree p" unfolding p smult_as_map_poly
    by (rule sym, subst map_poly_map_poly, force+, rule degree_map_poly, insert d, auto)
qed

lemma content_dvd_1:
  "content g = 1" if "content f = (1 :: 'a :: semiring_gcd)" "g dvd f" 
proof -
  from \<open>g dvd f\<close> have "content g dvd content f"
    by (rule content_dvd_contentI)
  with \<open>content f = 1\<close> show ?thesis
    by simp
qed

lemma dvd_smult_int: fixes c :: int assumes c: "c \<noteq> 0"
  and dvd: "q dvd (smult c p)"
  shows "primitive_part q dvd p"
proof (cases "p = 0")
  case True thus ?thesis by auto
next
  case False note p0 = this
  let ?cp = "smult c p"
  from p0 c have cp0: "?cp \<noteq> 0" by auto
  from dvd obtain r where prod: "?cp = q * r" unfolding dvd_def by auto
  from prod cp0 have q0: "q \<noteq> 0" and r0: "r \<noteq> 0" by auto
  let ?c = "content :: int poly \<Rightarrow> int"
  let ?n = "primitive_part :: int poly \<Rightarrow> int poly"
  let ?pn = "\<lambda> p. smult (?c p) (?n p)"
  have cq: "(?c q = 0) = False" using content_eq_zero_iff q0 by auto
  from prod have id1: "?cp = ?pn q * ?pn r" unfolding content_times_primitive_part by simp
  from arg_cong[OF this, of content, unfolded content_smult_int content_mult
    content_primitive_part[OF r0] content_primitive_part[OF q0], symmetric]
    p0[folded content_eq_zero_iff] c
  have "abs c dvd ?c q * ?c r" unfolding dvd_def by auto
  hence "c dvd ?c q * ?c r" by auto
  then obtain d where id: "?c q * ?c r = c * d" unfolding dvd_def by auto
  have "?cp = ?pn q * ?pn r" by fact
  also have "\<dots> = smult (c * d) (?n q * ?n r)" unfolding id [symmetric]
    by (metis content_mult content_times_primitive_part primitive_part_mult)
  finally have id: "?cp = smult c (?n q * smult d (?n r))" by (simp add: mult.commute)
  interpret map_poly_inj_zero_hom "(*) c" using c by (unfold_locales, auto)
  have "p = ?n q * smult d (?n r)" using id[unfolded smult_as_map_poly[of c]] by auto
  thus dvd: "?n q dvd p" unfolding dvd_def by blast
qed

lemma irreducible\<^sub>d_primitive_part:
  fixes p :: "int poly" (* can be relaxed but primitive_part_mult has bad type constraint *)
  shows "irreducible\<^sub>d (primitive_part p) \<longleftrightarrow> irreducible\<^sub>d p" (is "?l \<longleftrightarrow> ?r")
proof (rule iffI, rule irreducible\<^sub>dI)
  assume l: ?l
  show "degree p > 0" using l by auto
  have dpp: "degree (primitive_part p) = degree p" by simp
  fix q r
  assume deg: "degree q < degree p" "degree r < degree p" and "p = q * r"
  then have pp: "primitive_part p = primitive_part q * primitive_part r" by (simp add: primitive_part_mult)
  have "\<not> irreducible\<^sub>d (primitive_part p)"
    apply (intro reducible\<^sub>dI, rule exI[of _ "primitive_part q"], rule exI[of _ "primitive_part r"], unfold dpp)
    using deg pp by auto
  with l show False by auto
next
  show "?r \<Longrightarrow> ?l" by (metis irreducible\<^sub>d_smultI normalize_non_0_smult)
qed

lemma irreducible\<^sub>d_smult_int:
  fixes c :: int assumes c: "c \<noteq> 0"
  shows "irreducible\<^sub>d (smult c p) = irreducible\<^sub>d p" (is "?l = ?r")
  using irreducible\<^sub>d_primitive_part[of "smult c p", unfolded primitive_part_smult] c
  apply (cases "c < 0", simp)
  apply (metis add.inverse_inverse add.inverse_neutral c irreducible\<^sub>d_smultI normalize_non_0_smult smult_1_left smult_minus_left)
  apply (simp add: irreducible\<^sub>d_primitive_part)
  done

lemma irreducible\<^sub>d_as_irreducible:
  fixes p :: "int poly"
  shows "irreducible\<^sub>d p \<longleftrightarrow> irreducible (primitive_part p)"
  using irreducible_primitive_connect[of "primitive_part p"]
  by (cases "p = 0", auto simp: irreducible\<^sub>d_primitive_part)


lemma rat_to_int_factor_content_1: fixes p :: "int poly" 
  assumes cp: "content p = 1"
  and pgh: "map_poly rat_of_int p = g * h"
  and g: "rat_to_normalized_int_poly g = (r,rg)"
  and h: "rat_to_normalized_int_poly h = (s,sh)"
  and p: "p \<noteq> 0"
  shows "p = rg * sh"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  from p have rp0: "?rp p \<noteq> 0" by simp
  with pgh have g0: "g \<noteq> 0" and h0: "h \<noteq> 0" by auto
  from rat_to_normalized_int_poly[OF g] g0 
  have r: "r > 0" "r \<noteq> 0" and g: "g = smult r (?rp rg)" and crg: "content rg = 1" by auto
  from rat_to_normalized_int_poly[OF h] h0 
  have s: "s > 0" "s \<noteq> 0" and h: "h = smult s (?rp sh)" and csh: "content sh = 1" by auto
  let ?irs = "inverse (r * s)"
  from r s have irs0: "?irs \<noteq> 0" by (auto simp: field_simps)
  have "?rp (rg * sh) = ?rp rg * ?rp sh" by (simp add: hom_distribs)
  also have "\<dots> = smult ?irs (?rp p)" unfolding pgh g h using r s
    by (simp add: field_simps)
  finally have id: "?rp (rg * sh) = smult ?irs (?rp p)" by auto
  have rsZ: "?irs \<in> \<int>"
  proof (rule ccontr)
    assume not: "\<not> ?irs \<in> \<int>"
    obtain n d where irs': "quotient_of ?irs = (n,d)" by force
    from quotient_of_denom_pos[OF irs'] have "d > 0" .
    from not quotient_of_div[OF irs'] have "d \<noteq> 1" "d \<noteq> 0" and irs: "?irs = ?r n / ?r d" by auto
    with irs0 have n0: "n \<noteq> 0" by auto
    from \<open>d > 0\<close> \<open>d \<noteq> 1\<close> have "d \<ge> 2" and "\<not> d dvd 1" by auto
    with content_iff[of d p, unfolded cp] obtain c where 
      c: "c \<in> set (coeffs p)" and dc: "\<not> d dvd c" 
      by auto
    from c range_coeff[of p] obtain i where "c = coeff p i" by auto 
    from arg_cong[OF id, of "\<lambda> p. coeff p i", 
      unfolded coeff_smult of_int_hom.coeff_map_poly_hom this[symmetric] irs]
    have "?r n / ?r d * ?r c \<in> \<int>" by (metis Ints_of_int)
    also have "?r n / ?r d * ?r c = ?r (n * c) / ?r d" by simp
    finally have inZ: "?r (n * c) / ?r d \<in> \<int>" .
    have cop: "coprime n d" by (rule quotient_of_coprime[OF irs'])
    (* now there comes tedious reasoning that `coprime n d` `\<not> d dvd c` ` nc / d \<in> \<int>` yields a 
       contradiction *)
    define prod where "prod = ?r (n * c) / ?r d"
    obtain n' d' where quot: "quotient_of prod = (n',d')" by force
    have qr: "\<And> x. quotient_of (?r x) = (x, 1)"
      using Rat.of_int_def quotient_of_int by auto
    from quotient_of_denom_pos[OF quot] have "d' > 0" .
    with quotient_of_div[OF quot] inZ[folded prod_def] have "d' = 1"
      by (metis Ints_cases Rat.of_int_def old.prod.inject quot quotient_of_int)
    with quotient_of_div[OF quot] have "prod = ?r n'" by auto
    from arg_cong[OF this, of quotient_of, unfolded prod_def rat_divide_code qr Let_def split]
    have "Rat.normalize (n * c, d) = (n',1)" by simp
    from normalize_crossproduct[OF \<open>d \<noteq> 0\<close>, of 1 "n * c" n', unfolded this]
    have id: "n * c = n' * d" by auto 
    from quotient_of_coprime[OF irs'] have "coprime n d" .
    with id have "d dvd c"
      by (metis coprime_commute coprime_dvd_mult_right_iff dvd_triv_right)
    with dc show False ..
  qed
  then obtain irs where irs: "?irs = ?r irs" unfolding Ints_def by blast
  from id[unfolded irs, folded hom_distribs, unfolded of_int_poly_hom.eq_iff]
  have p: "rg * sh = smult irs p" by auto
  have "content (rg * sh) = 1" unfolding content_mult crg csh by auto
  from this[unfolded p content_smult_int cp] have "abs irs = 1" by simp
  hence "abs ?irs = 1" using irs by auto
  with r s have "?irs = 1" by auto
  with irs have "irs = 1" by auto
  with p show p: "p = rg * sh" by auto
qed

lemma rat_to_int_factor_explicit: fixes p :: "int poly" 
  assumes pgh: "map_poly rat_of_int p = g * h"
  and g: "rat_to_normalized_int_poly g = (r,rg)"
  shows "\<exists> r. p = rg * smult (content p) r"
proof -
  show ?thesis
  proof (cases "p = 0")
    case True
    show ?thesis unfolding True
      by (rule exI[of _ 0], auto simp: degree_monom_eq)
  next
    case False
    hence p: "p \<noteq> 0" by auto
    let ?r = "rat_of_int"
    let ?rp = "map_poly ?r"
    define q where "q = primitive_part p"
    from content_times_primitive_part[of p, folded q_def] content_eq_zero_iff[of p] p
      obtain a where a: "a \<noteq> 0" and pq: "p = smult a q" and acp: "content p = a" by metis
    from a pq p have ra: "?r a \<noteq> 0" and q0: "q \<noteq> 0" by auto
    from content_primitive_part[OF p, folded q_def] have cq: "content q = 1" by auto
    obtain s sh where h: "rat_to_normalized_int_poly (smult (inverse (?r a)) h) = (s,sh)" by force
    from arg_cong[OF pgh[unfolded pq], of "smult (inverse (?r a))"] ra
    have "?rp q = g * smult (inverse (?r a)) h" by (auto simp: hom_distribs)
    from rat_to_int_factor_content_1[OF cq this g h q0]
    have qrs: "q = rg * sh" .
    show ?thesis unfolding acp unfolding pq qrs 
      by (rule exI[of _ sh], auto)
  qed
qed

lemma rat_to_int_factor: fixes p :: "int poly" 
  assumes pgh: "map_poly rat_of_int p = g * h"
  shows "\<exists> g' h'. p = g' * h' \<and> degree g' = degree g \<and> degree h' = degree h"
proof(cases "p = 0")
  case True
  with pgh have "g = 0 \<or> h = 0" by auto
  then show ?thesis
    by (metis True degree_0 mult_hom.hom_zero mult_zero_left rat_to_normalized_int_poly(4) surj_pair)
next
  case False
  obtain r rg where ri: "rat_to_normalized_int_poly (smult (1 / of_int (content p)) g) = (r,rg)" by force
  obtain q qh where ri2: "rat_to_normalized_int_poly h = (q,qh)" by force
  show ?thesis
  proof (intro exI conjI)
    have "of_int_poly (primitive_part p) = smult (1 / of_int (content p)) (g * h)"
      apply (auto simp: primitive_part_def pgh[symmetric] smult_map_poly map_poly_map_poly o_def intro!: map_poly_cong)
      by (metis (no_types, lifting) content_dvd_coeffs div_by_0 dvd_mult_div_cancel floor_of_int nonzero_mult_div_cancel_left of_int_hom.hom_zero of_int_mult)
    also have "\<dots> = smult (1 / of_int (content p)) g * h" by simp
    finally have "of_int_poly (primitive_part p) = \<dots>".
    note main = rat_to_int_factor_content_1[OF _ this ri ri2, simplified, OF False]
    show "p = smult (content p) rg * qh" by (simp add: main[symmetric])
    from ri2 show "degree qh = degree h" by (fact rat_to_normalized_int_poly)
    from rat_to_normalized_int_poly(4)[OF ri] False
    show "degree (smult (content p) rg) = degree g" by auto
  qed
qed

lemma rat_to_int_factor_normalized_int_poly: fixes p :: "rat poly" 
  assumes pgh: "p = g * h"
  and p: "rat_to_normalized_int_poly p = (i,ip)"
  shows "\<exists> g' h'. ip = g' * h' \<and> degree g' = degree g"
proof -
  from rat_to_normalized_int_poly[OF p]
  have p: "p = smult i (map_poly rat_of_int ip)" and i: "i \<noteq> 0" by auto
  from arg_cong[OF p, of "smult (inverse i)", unfolded pgh] i
  have "map_poly rat_of_int ip = g * smult (inverse i) h" by auto
  from rat_to_int_factor[OF this] show ?thesis by auto
qed

(* TODO: move *)
lemma irreducible_smult [simp]:
  fixes c :: "'a :: field"
  shows "irreducible (smult c p) \<longleftrightarrow> irreducible p \<and> c \<noteq> 0"
  using irreducible_mult_unit_left[of "[:c:]", simplified] by force

text \<open>A polynomial with integer coefficients is
   irreducible over the rationals, if it is irreducible over the integers.\<close>
theorem irreducible\<^sub>d_int_rat: fixes p :: "int poly" 
  assumes p: "irreducible\<^sub>d p"
  shows "irreducible\<^sub>d (map_poly rat_of_int p)"
proof (rule irreducible\<^sub>dI)
  from irreducible\<^sub>dD[OF p]
  have p: "degree p \<noteq> 0" and irr: "\<And> q r. degree q < degree p \<Longrightarrow> degree r < degree p \<Longrightarrow> p \<noteq> q * r" by auto
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  from p show rp: "degree (?rp p) > 0" by auto
  from p have p0: "p \<noteq> 0" by auto
  fix g h :: "rat poly"
  assume deg: "degree g > 0" "degree g < degree (?rp p)" "degree h > 0" "degree h < degree (?rp p)" and pgh: "?rp p = g * h"
  from rat_to_int_factor[OF pgh] obtain g' h' where p: "p = g' * h'" and dg: "degree g' = degree g" "degree h' = degree h"
    by auto
  from irr[of g' h'] deg[unfolded dg]
  show False using degree_mult_eq[of g' h'] by (auto simp: p dg)
qed

corollary irreducible\<^sub>d_rat_to_normalized_int_poly: 
  assumes rp: "rat_to_normalized_int_poly rp = (a, ip)"
  and ip: "irreducible\<^sub>d ip"
  shows "irreducible\<^sub>d rp"
proof -
  from rat_to_normalized_int_poly[OF rp] 
  have rp: "rp = smult a (map_poly rat_of_int ip)" and a: "a \<noteq> 0" by auto
  with irreducible\<^sub>d_int_rat[OF ip] show ?thesis by auto
qed

lemma dvd_content_dvd: assumes dvd: "content f dvd content g" "primitive_part f dvd primitive_part g"
  shows "f dvd g" 
proof -
  let ?cf = "content f" let ?nf = "primitive_part f" 
  let ?cg = "content g" let ?ng = "primitive_part g" 
  have "f dvd g = (smult ?cf ?nf dvd smult ?cg ?ng)" 
    unfolding content_times_primitive_part by auto
  from dvd(1) obtain ch where cg: "?cg = ?cf * ch" unfolding dvd_def by auto
  from dvd(2) obtain nh where ng: "?ng = ?nf * nh" unfolding dvd_def by auto
  have "f dvd g = (smult ?cf ?nf dvd smult ?cg ?ng)" 
    unfolding content_times_primitive_part[of f] content_times_primitive_part[of g] by auto
  also have "\<dots> = (smult ?cf ?nf dvd smult ?cf ?nf * smult ch nh)" unfolding cg ng
    by (metis mult.commute mult_smult_right smult_smult)
  also have "\<dots>" by (rule dvd_triv_left)
  finally show ?thesis .
qed

lemma sdiv_poly_smult: "c \<noteq> 0 \<Longrightarrow> sdiv_poly (smult c f) c = f"
  by (intro poly_eqI, unfold coeff_sdiv_poly coeff_smult, auto)

lemma primitive_part_smult_int: fixes f :: "int poly" shows
  "primitive_part (smult d f) = smult (sgn d) (primitive_part f)" 
proof (cases "d = 0 \<or> f = 0")
  case False
  obtain cf where cf: "content f = cf" by auto
  with False have 0: "d \<noteq> 0" "f \<noteq> 0" "cf \<noteq> 0" by auto
  show ?thesis 
  proof (rule poly_eqI, unfold primitive_part_alt_def coeff_sdiv_poly content_smult_int coeff_smult cf)
    fix n
    consider (pos) "d > 0" | (neg) "d < 0" using 0(1) by linarith
    thus "d * coeff f n div (\<bar>d\<bar> * cf) = sgn d * (coeff f n div cf)"
    proof cases
      case neg
      hence "?thesis = (d * coeff f n div - (d * cf) = - (coeff f n div cf))" by auto
      also have "d * coeff f n div - (d * cf) = - (d * coeff f n div (d * cf))" 
        by (subst dvd_div_neg, insert 0(1), auto simp: cf[symmetric])
      also have "d * coeff f n div (d * cf) = coeff f n div cf" using 0(1) by auto
      finally show ?thesis by simp
    qed auto
  qed
qed auto

end
