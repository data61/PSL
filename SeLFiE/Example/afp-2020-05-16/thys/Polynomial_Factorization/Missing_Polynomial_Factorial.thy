section \<open>More on Polynomials\<close>

text \<open>This theory contains several results on content, gcd, primitive part, etc..
  Moreover, there is a slightly improved code-equation for computing the gcd.\<close>

theory Missing_Polynomial_Factorial
  imports "HOL-Computational_Algebra.Polynomial_Factorial"
   Polynomial_Interpolation.Missing_Polynomial  
begin

text \<open>Improved code equation for @{const gcd_poly_code}
  which avoids computing the content twice.\<close>
lemma gcd_poly_code_code[code]: "gcd_poly_code p q =
           (if p = 0 then normalize q else if q = 0 then normalize p else let
              c1 = content p;
              c2 = content q;
              p' = map_poly (\<lambda> x. x div c1) p;
              q' = map_poly (\<lambda> x. x div c2) q
              in smult (gcd c1 c2) (gcd_poly_code_aux p' q'))"
  unfolding gcd_poly_code_def Let_def primitive_part_def by simp

lemma gcd_smult: fixes f g :: "'a :: {factorial_ring_gcd,semiring_gcd_mult_normalize} poly"
  defines cf: "cf \<equiv> content f"
  and cg: "cg \<equiv> content g"
shows "gcd (smult a f) g = (if a = 0 \<or> f = 0 then normalize g else
  smult (gcd a (cg div (gcd cf cg))) (gcd f g))"
proof (cases "a = 0 \<or> f = 0")
  case False
  let ?c = "content"
  let ?pp = primitive_part
  let ?ua = "unit_factor a"
  let ?na = "normalize a"
  define H where "H = gcd (?c f) (?c g)"
  have "H dvd ?c f" unfolding H_def by auto
  then obtain F where fh: "?c f = H * F" unfolding dvd_def by blast
  from False have cf0: "?c f \<noteq> 0" by auto
  hence H: "H \<noteq> 0" unfolding H_def by auto
  from arg_cong[OF fh, of "\<lambda> f. f div H"] H have F: "F = ?c f div H" by auto
  have "H dvd ?c g" unfolding H_def by auto
  then obtain G where gh: "?c g = H * G" unfolding dvd_def by blast
  from arg_cong[OF gh, of "\<lambda> f. f div H"] H have G: "G = ?c g div H" by auto
  have "coprime F G" using H unfolding F G H_def
    using cf0 div_gcd_coprime by blast
  have "is_unit ?ua" using False by simp
  then have ua: "is_unit [: ?ua :]"
    by (simp add: is_unit_const_poly_iff)
  have "gcd (smult a f) g = smult (gcd (?na * ?c f) (?c g))
     (gcd (smult ?ua (?pp f)) (?pp g))"
    unfolding gcd_poly_decompose[of "smult a f"]
    content_smult primitive_part_smult by simp
  also have "smult ?ua (?pp f) = ?pp f * [: ?ua :]" by simp
  also have "gcd \<dots> (?pp g) = gcd (?pp f) (?pp g)"
    unfolding gcd_mult_unit1[OF ua] ..
  also have "gcd (?na * ?c f) (?c g) = gcd ((?na * F) * H) (G * H)"
    unfolding fh gh by (simp add: ac_simps)
  also have "\<dots> = gcd (?na * F) G * normalize H" unfolding gcd_mult_right gcd.commute[of G]
    by (simp add: normalize_mult)
  also have "normalize H = H" by (metis H_def normalize_gcd)
  finally
  have "gcd (smult a f) g = smult (gcd (?na * F) G) (smult  H (gcd (?pp f) (?pp g)))" by simp
  also have "smult H (gcd (?pp f) (?pp g)) = gcd f g" unfolding H_def
    by (rule gcd_poly_decompose[symmetric])
  also have "gcd (?na * F) G = gcd (F * ?na) G" by (simp add: ac_simps)
  also have "\<dots> = gcd ?na G"
    using \<open>coprime F G\<close> by (simp add: gcd_mult_right_left_cancel ac_simps)
  finally show ?thesis unfolding G H_def cg cf using False by simp
next
  case True
  hence "gcd (smult a f) g = normalize g" by (cases "a = 0", auto)
  thus ?thesis using True by simp
qed

lemma gcd_smult_ex: assumes "a \<noteq> 0"
  shows "\<exists> b. gcd (smult a f) g = smult b (gcd f g) \<and> b \<noteq> 0"
proof (cases "f = 0")
  case True
  thus ?thesis by (intro exI[of _ 1], auto)
next
  case False
  hence id: "(a = 0 \<or> f = 0) = False" using assms by auto
  show ?thesis unfolding gcd_smult id if_False
    by (intro exI conjI, rule refl, insert assms, auto)
qed

lemma primitive_part_idemp[simp]:
  fixes f :: "'a :: {semiring_gcd,normalization_semidom_multiplicative} poly"
  shows "primitive_part (primitive_part f) = primitive_part f"
  by (metis content_primitive_part[of f] primitive_part_eq_0_iff primitive_part_prim)

lemma content_gcd_primitive:
   "f \<noteq> 0 \<Longrightarrow> content (gcd (primitive_part f) g) = 1"
   "f \<noteq> 0 \<Longrightarrow> content (gcd (primitive_part f) (primitive_part g)) = 1"
  by (metis (no_types, lifting) content_dvd_contentI content_primitive_part gcd_dvd1 is_unit_content_iff)+

lemma content_gcd_content: "content (gcd f g) = gcd (content f) (content g)"
  (is "?l = ?r")
proof -
  let ?c = "content"
  have "?l = normalize (gcd (?c f) (?c g)) *
    ?c (gcd (primitive_part f) (primitive_part g))"
    unfolding gcd_poly_decompose[of f g] content_smult ..
  also have "\<dots> = gcd (?c f) (?c g) *
    ?c (gcd (primitive_part f) (primitive_part g))" by simp
  also have "\<dots> = ?r" using content_gcd_primitive[of f g]
    by (metis (no_types, lifting) content_dvd_contentI content_eq_zero_iff
    content_primitive_part gcd_dvd2 gcd_eq_0_iff is_unit_content_iff mult_cancel_left1)
  finally show ?thesis .
qed

lemma gcd_primitive_part:
  "gcd (primitive_part f) (primitive_part g) = normalize (primitive_part (gcd f g))"
  proof(cases "f = 0")
    case True
    show ?thesis unfolding gcd_poly_decompose[of f g] gcd_0_left primitive_part_0 True
      by (simp add: associatedI primitive_part_dvd_primitive_partI)
  next
    case False
    have "normalize 1 = normalize (unit_factor (gcd (content f) (content g)))"
      by (simp add: False)
    then show ?thesis unfolding gcd_poly_decompose[of f g]
      by (metis (no_types) Polynomial.normalize_smult content_gcd_primitive(1)[OF False] content_times_primitive_part normalize_gcd primitive_part_smult)
qed

lemma primitive_part_gcd: "primitive_part (gcd f g)
  = unit_factor (gcd f g) * gcd (primitive_part f) (primitive_part g)"
  unfolding gcd_primitive_part
  by (metis (no_types, lifting)
  content_times_primitive_part gcd.normalize_idem mult_cancel_left2 mult_smult_left
  normalize_eq_0_iff normalize_mult_unit_factor primitive_part_eq_0_iff
  smult_content_normalize_primitive_part unit_factor_mult_normalize)

lemma primitive_part_normalize: 
  fixes f :: "'a :: {semiring_gcd,idom_divide,normalization_semidom_multiplicative} poly"
  shows "primitive_part (normalize f) = normalize (primitive_part f)"
proof (cases "f = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "normalize (content (normalize (primitive_part f))) = 1"
    using content_primitive_part[OF False] content_dvd content_const
          content_dvd_contentI dvd_normalize_iff is_unit_content_iff by (metis (no_types))
  then have "content (normalize (primitive_part f)) = 1" by fastforce
  then have "content (normalize f) = 1 * content f"
    by (metis (no_types) content_smult mult.commute normalize_content
    smult_content_normalize_primitive_part)
  then have "content f = content (normalize f)"
    by simp
  then show ?thesis unfolding smult_content_normalize_primitive_part[of f,symmetric]
    by (metis (no_types) False content_times_primitive_part mult.commute mult_cancel_left
                                   mult_smult_right smult_content_normalize_primitive_part)
qed

lemma length_coeffs_primitive_part[simp]: "length (coeffs (primitive_part f)) = length (coeffs f)"
proof (cases "f = 0")
  case False
  hence "length (coeffs f) \<noteq> 0" "length (coeffs (primitive_part f)) \<noteq> 0" by auto
  thus ?thesis using degree_primitive_part[of f, unfolded degree_eq_length_coeffs] by linarith
qed simp

lemma degree_unit_factor[simp]: "degree (unit_factor f) = 0"
  by (simp add: monom_0 unit_factor_poly_def)

lemma degree_normalize[simp]: "degree (normalize f) = degree f"
proof (cases "f = 0")
  case False
  have "degree f = degree (unit_factor f * normalize f)" by simp
  also have "\<dots> = degree (unit_factor f) + degree (normalize f)"
    by (rule degree_mult_eq, insert False, auto)
  finally show ?thesis by simp
qed simp
  
lemma content_iff: "x dvd content p \<longleftrightarrow> (\<forall> c \<in> set (coeffs p). x dvd c)"
  by (simp add: content_def dvd_gcd_list_iff)
  
lemma is_unit_field_poly[simp]: "(p::'a::field poly) dvd 1 \<longleftrightarrow> p \<noteq> 0 \<and> degree p = 0"
proof(intro iffI conjI, unfold conj_imp_eq_imp_imp)
  assume "is_unit p"
  then obtain q where *: "p * q = 1" by (elim dvdE, auto)
  from * show p0: "p \<noteq> 0" by auto
  from * have q0: "q \<noteq> 0" by auto
  from * degree_mult_eq[OF p0 q0]
  show "degree p = 0" by auto
next
  assume "degree p = 0"
  from degree0_coeffs[OF this]
  obtain c where c: "p = [:c:]" by auto
  assume "p \<noteq> 0"
  with c have "c \<noteq> 0" by auto
  with c have "1 = p * [:1/c:]" by auto
  from dvdI[OF this] show "is_unit p".
qed

definition primitive where
  "primitive f \<longleftrightarrow> (\<forall>x. (\<forall>y \<in> set (coeffs f). x dvd y) \<longrightarrow> x dvd 1)"

lemma primitiveI:
  assumes "(\<And>x. (\<And>y. y \<in> set (coeffs f) \<Longrightarrow> x dvd y) \<Longrightarrow> x dvd 1)"
  shows "primitive f" by (insert assms, auto simp: primitive_def)

lemma primitiveD:
  assumes "primitive f"
  shows "(\<And>y. y \<in> set (coeffs f) \<Longrightarrow> x dvd y) \<Longrightarrow> x dvd 1"
    by (insert assms, auto simp: primitive_def)

lemma not_primitiveE:
  assumes "\<not> primitive f"
      and "\<And>x. (\<And>y. y \<in> set (coeffs f) \<Longrightarrow> x dvd y) \<Longrightarrow> \<not> x dvd 1 \<Longrightarrow> thesis"
  shows thesis by (insert assms, auto simp: primitive_def)

lemma primitive_iff_content_eq_1[simp]:
  fixes f :: "'a :: semiring_gcd poly"
  shows "primitive f \<longleftrightarrow> content f = 1"
proof(intro iffI primitiveI)
  fix x
  assume "(\<And>y. y \<in> set (coeffs f) \<Longrightarrow> x dvd y)"
  from gcd_list_greatest[of "coeffs f", OF this]
  have "x dvd content f" by (simp add: content_def)
  also assume "content f = 1"
  finally show "x dvd 1".
next
  assume "primitive f"
  from primitiveD[OF this list_gcd[of _ "coeffs f"], folded content_def]
  show "content f = 1" by simp
qed

lemma primitive_prod_list:
  fixes fs :: "'a :: {factorial_semiring,semiring_Gcd,normalization_semidom_multiplicative} poly list"
  assumes "primitive (prod_list fs)" and "f \<in> set fs" shows "primitive f"
proof (insert assms, induct fs arbitrary: f)
  case (Cons f' fs)
  from Cons.prems
  have "is_unit (content f' * content (prod_list fs))" by (auto simp: content_mult)
  from this[unfolded is_unit_mult_iff]
  have "content f' = 1" and "content (prod_list fs) = 1" by auto
  moreover from Cons.prems have "f = f' \<or> f \<in> set fs" by auto
  ultimately show ?case using Cons.hyps[of f] by auto
qed auto

lemma irreducible_imp_primitive:
  fixes f :: "'a :: {idom,semiring_gcd} poly"
  assumes irr: "irreducible f" and deg: "degree f \<noteq> 0" shows "primitive f"
proof (rule ccontr)
  assume not: "\<not> ?thesis"
  then have "\<not> [:content f:] dvd 1" by simp
  moreover have "f = [:content f:] * primitive_part f" by simp
    note Factorial_Ring.irreducibleD[OF irr this]
  ultimately
  have "primitive_part f dvd 1" by auto
  from this[unfolded poly_dvd_1] have "degree f = 0" by auto
  with deg show False by auto
qed
  
lemma irreducible_primitive_connect:
  fixes f :: "'a :: {idom,semiring_gcd} poly"
  assumes cf: "primitive f" shows "irreducible\<^sub>d f \<longleftrightarrow> irreducible f" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l show ?r
  proof(rule ccontr, elim not_irreducibleE)
    from l have deg: "degree f > 0" by (auto dest: irreducible\<^sub>dD)
    from cf have f0: "f \<noteq> 0" by auto
    then show "f = 0 \<Longrightarrow> False" by auto
    show "f dvd 1 \<Longrightarrow> False" using deg by (auto simp:poly_dvd_1)
    fix a b assume fab: "f = a * b" and a1: "\<not> a dvd 1" and b1: "\<not> b dvd 1"
    then have af: "a dvd f" and bf: "b dvd f" by auto
    with f0 have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by auto
    from irreducible\<^sub>dD(2)[OF l, of a] af dvd_imp_degree_le[OF af f0]
    have "degree a = 0 \<or> degree a = degree f"
      by (metis degree_smult_le irreducible\<^sub>d_dvd_smult l le_antisym Nat.neq0_conv)
    then show False
    proof(elim disjE)
      assume "degree a = 0"
      then obtain c where ac: "a = [:c:]" by (auto dest: degree0_coeffs)
      from fab[unfolded ac] have "c dvd content f" by (simp add: content_iff coeffs_smult)
      with cf have "c dvd 1" by simp
      then have "a dvd 1" by (auto simp: ac)
      with a1 show False by auto
    next
      assume dega: "degree a = degree f"
      with f0 degree_mult_eq[OF a0 b0] fab have "degree b = 0" by (auto simp: ac_simps)
      then obtain c where bc: "b = [:c:]" by (auto dest: degree0_coeffs)
      from fab[unfolded bc] have "c dvd content f" by (simp add: content_iff coeffs_smult)
      with cf have "c dvd 1" by simp
      then have "b dvd 1" by (auto simp: bc)
      with b1 show False by auto
    qed
  qed
next
  assume r: ?r
  show ?l
  proof(intro irreducible\<^sub>dI)
    show "degree f > 0"
    proof (rule ccontr)
      assume "\<not>degree f > 0"
      then obtain f0 where f: "f = [:f0:]" by (auto dest: degree0_coeffs)
      from cf[unfolded this] have "normalize f0 = 1" by auto
      then have "f0 dvd 1" by (unfold normalize_1_iff)
      with r[unfolded f irreducible_const_poly_iff] show False by auto
    qed
  next
    fix g h assume deg_g: "degree g > 0" and deg_gf: "degree g < degree f" and fgh: "f = g * h"
    with r have "g dvd 1 \<or> h dvd 1" by auto
    with deg_g have "degree h = 0" by (auto simp: poly_dvd_1)
    with deg_gf[unfolded fgh] degree_mult_eq[of g h] show False by (cases "g = 0 \<or> h = 0", auto)
  qed
qed

lemma deg_not_zero_imp_not_unit: 
  fixes f:: "'a::{idom_divide,semidom_divide_unit_factor} poly"
  assumes deg_f: "degree f > 0"
  shows "\<not> is_unit f"
proof -
  have "degree (normalize f) > 0" 
    using deg_f degree_normalize by auto  
  hence "normalize f \<noteq> 1"
    by fastforce
  thus "\<not> is_unit f" using normalize_1_iff by auto
qed

lemma content_pCons[simp]: "content (pCons a p) = gcd a (content p)"
proof(induct p arbitrary: a)
  case 0 show ?case by simp
next
  case (pCons c p)
  then show ?case by (cases "p = 0", auto simp: content_def cCons_def)
qed

lemma content_field_poly:
  fixes f :: "'a :: {field,semiring_gcd} poly"
  shows "content f = (if f = 0 then 0 else 1)"
  by(induct f, auto simp: dvd_field_iff is_unit_normalize)


end
