(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers: Addition and Multiplication\<close>

text \<open>This theory contains the remaining field operations for algebraic numbers, namely
  addition and multiplication.\<close>

theory Algebraic_Numbers
imports
  Algebraic_Numbers_Prelim
  Resultant
  Polynomial_Factorization.Polynomial_Divisibility
begin

interpretation coeff_hom: monoid_add_hom "\<lambda>p. coeff p i" by (unfold_locales, auto)
interpretation coeff_hom: comm_monoid_add_hom "\<lambda>p. coeff p i"..
interpretation coeff_hom: group_add_hom "\<lambda>p. coeff p i"..
interpretation coeff_hom: ab_group_add_hom "\<lambda>p. coeff p i"..
interpretation coeff_0_hom: monoid_mult_hom "\<lambda>p. coeff p 0" by (unfold_locales, auto simp: coeff_mult)
interpretation coeff_0_hom: semiring_hom "\<lambda>p. coeff p 0"..
interpretation coeff_0_hom: comm_monoid_mult_hom "\<lambda>p. coeff p 0"..
interpretation coeff_0_hom: comm_semiring_hom "\<lambda>p. coeff p 0"..

subsection \<open>Addition of Algebraic Numbers\<close>

definition "x_y \<equiv> [: [: 0, 1 :], -1 :]"

definition "poly_x_minus_y p = poly_lift p \<circ>\<^sub>p x_y"


text \<open>The following polynomial represents the sum of two algebraic numbers.\<close>

definition poly_add :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_add p q = resultant (poly_x_minus_y p) (poly_lift q)"

subsubsection \<open>@{term poly_add} has desired root\<close>

interpretation poly_x_minus_y_hom:
  comm_ring_hom poly_x_minus_y by (unfold_locales; simp add: poly_x_minus_y_def hom_distribs)

lemma poly2_x_y[simp]:
  fixes x :: "'a :: comm_ring_1"
  shows "poly2 x_y x y = x - y" unfolding poly2_def by (simp add: x_y_def)

lemma degree_poly_x_minus_y[simp]:
  fixes p :: "'a::idom poly"
  shows "degree (poly_x_minus_y p) = degree p" unfolding poly_x_minus_y_def x_y_def by auto

lemma poly_x_minus_y_pCons[simp]:
  "poly_x_minus_y (pCons a p) = [:[: a :]:] + poly_x_minus_y p * x_y"
  unfolding poly_x_minus_y_def x_y_def by simp

lemma poly_poly_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly (poly (poly_x_minus_y p) q) x = poly p (x - poly q x)"
  by (induct p; simp add: ring_distribs x_y_def)

lemma poly2_poly_x_minus_y[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_x_minus_y p) x y = poly p (x-y)" unfolding poly2_def by simp

interpretation x_y_mult_hom: zero_hom_0 "\<lambda>p :: 'a :: comm_ring_1 poly poly. x_y * p"
proof (unfold_locales)
  fix p :: "'a poly poly"
  assume "x_y * p = 0"
  then show "p = 0" apply (simp add: x_y_def)
    by (metis eq_neg_iff_add_eq_0 minus_equation_iff minus_pCons synthetic_div_unique_lemma)
qed

lemma x_y_nonzero[simp]: "x_y \<noteq> 0" by (simp add: x_y_def)

lemma degree_x_y[simp]: "degree x_y = 1" by (simp add: x_y_def)

interpretation x_y_mult_hom: inj_comm_monoid_add_hom "\<lambda>p :: 'a :: idom poly poly. x_y * p"
proof (unfold_locales)
  show "x_y * p = x_y * q \<Longrightarrow> p = q" for p q :: "'a poly poly"
  proof (induct p arbitrary:q)
    case 0
    then show ?case by simp
  next
    case p: (pCons a p)
    from p(3)[unfolded mult_pCons_right]
    have "x_y * (monom a 0 + pCons 0 1 * p) = x_y * q"
      apply (subst(asm) pCons_0_as_mult)
      apply (subst(asm) smult_prod) by (simp only: field_simps distrib_left)
    then have "monom a 0 + pCons 0 1 * p = q" by simp
    then show "pCons a p = q" using pCons_as_add by (simp add: monom_0 monom_Suc)
  qed
qed

interpretation poly_x_minus_y_hom: inj_idom_hom poly_x_minus_y
proof
  fix p :: "'a poly"
  assume 0: "poly_x_minus_y p = 0"
  then have "poly_lift p \<circ>\<^sub>p x_y = 0" by (simp add: poly_x_minus_y_def)
  then show "p = 0"
  proof (induct p)
    case 0
    then show ?case by simp
  next
    case (pCons a p)
    note p = this[unfolded poly_lift_pCons pcompose_pCons]
    show ?case
    proof (cases "a=0")
      case a0: True
      with p have "x_y * poly_lift p \<circ>\<^sub>p x_y = 0" by simp
      then have "poly_lift p \<circ>\<^sub>p x_y = 0" by simp
      then show ?thesis using p by simp
    next
      case a0: False
      with p have p0: "p \<noteq> 0" by auto
      from p have "[:[:a:]:] = - x_y * poly_lift p \<circ>\<^sub>p x_y" by (simp add: eq_neg_iff_add_eq_0)
      then have "degree [:[:a:]:] = degree (x_y * poly_lift p \<circ>\<^sub>p x_y)" by simp
      also have "... = degree (x_y::'a poly poly) + degree (poly_lift p \<circ>\<^sub>p x_y)"
        apply (subst degree_mult_eq)
          apply simp
         apply (subst pcompose_eq_0)
          apply (simp add: x_y_def)
         apply (simp add: p0)
        apply simp
       done
      finally have False by simp 
      then show ?thesis..
    qed
  qed
qed

lemma poly_add:
  fixes p q :: "'a ::comm_ring_1 poly"
  assumes q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
  shows "poly (poly_add p q) (x+y) = 0"
proof (unfold poly_add_def, rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using poly_zero q0 y by auto
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y, simp_all)


subsubsection \<open>@{const poly_add} is nonzero\<close>

text \<open>
  We first prove that @{const poly_lift} preserves factorization. The result will be essential
  also in the next section for division of algebraic numbers.
\<close>

interpretation coeff_lift_hom:
  factor_preserving_hom "coeff_lift :: 'a :: {comm_semiring_1,semiring_no_zero_divisors} \<Rightarrow> _"
  by (unfold_locales, auto)

interpretation poly_lift_hom:
  unit_preserving_hom "poly_lift :: 'a :: {comm_semiring_1,semiring_no_zero_divisors} poly \<Rightarrow> _"
proof
  fix x :: "'a poly"
  assume "poly_lift x dvd 1"
  then have "poly_y_x (poly_lift x) dvd poly_y_x 1"
    by simp
  then show "x dvd 1"
    by (auto simp add: poly_y_x_poly_lift)
qed

interpretation poly_lift_hom:
  factor_preserving_hom "poly_lift::'a::idom poly \<Rightarrow> 'a poly poly"
proof unfold_locales
  fix p :: "'a poly"
  assume p: "irreducible p"
  show "irreducible (poly_lift p)"
  proof(rule ccontr)
    from p have p0: "p \<noteq> 0" and "\<not> p dvd 1" by (auto dest: irreducible_not_unit)
    with poly_lift_hom.hom_dvd[of p 1] have p1: "\<not> poly_lift p dvd 1" by auto
    assume "\<not> irreducible (poly_lift p)"
    from this[unfolded irreducible_altdef,simplified] p0 p1
    obtain q where "q dvd poly_lift p" and pq: "\<not> poly_lift p dvd q" and q: "\<not> q dvd 1" by auto
    then obtain r where "q * r = poly_lift p" by (elim dvdE, auto)
    then have "poly_y_x (q * r) = poly_y_x (poly_lift p)" by auto
    also have "... = [:p:]" by (auto simp: poly_y_x_poly_lift monom_0)
    also have "poly_y_x (q * r) = poly_y_x q * poly_y_x r" by (auto simp: hom_distribs)
    finally have "... = [:p:]" by auto
    then have qp: "poly_y_x q dvd [:p:]" by (metis dvdI)
    from dvd_const[OF this] p0 have "degree (poly_y_x q) = 0" by auto
    from degree_0_id[OF this,symmetric] obtain s
      where qs: "poly_y_x q = [:s:]" by auto
    have "poly_lift s = poly_y_x (poly_y_x (poly_lift s))" by auto
      also have "... = poly_y_x [:s:]" by (auto simp: poly_y_x_poly_lift monom_0)
      also have "... = q" by (auto simp: qs[symmetric])
    finally have sq: "poly_lift s = q" by auto
    from qp[unfolded qs] have sp: "s dvd p" by (auto simp: const_poly_dvd)
    from irreducibleD'[OF p this] sq q pq show False by auto
  qed
qed

text \<open>
  We now show that @{const poly_x_minus_y} is a factor-preserving homomorphism. This is
  essential for this section. This is easy since @{const poly_x_minus_y} can be represented
  as the composition of two factor-preserving homomorphisms.
\<close>

lemma poly_x_minus_y_as_comp: "poly_x_minus_y = (\<lambda>p. p \<circ>\<^sub>p x_y) \<circ> poly_lift"
  by (intro ext, unfold poly_x_minus_y_def, auto)
context idom_isom begin
  sublocale comm_semiring_isom..
end
interpretation poly_x_minus_y_hom:
  factor_preserving_hom "poly_x_minus_y :: 'a :: idom poly \<Rightarrow> 'a poly poly"
proof-
  interpret x_y_hom: bijective "\<lambda>p :: 'a poly poly. p \<circ>\<^sub>p x_y"
  proof (unfold bijective_eq_bij, rule id_imp_bij)
    fix p :: "'a poly poly" show "p \<circ>\<^sub>p x_y \<circ>\<^sub>p x_y = p"
      apply (induct p,simp)
      apply(unfold x_y_def hom_distribs pcompose_pCons) by (simp)
  qed
  interpret x_y_hom: idom_isom "\<lambda>p :: 'a poly poly. p \<circ>\<^sub>p x_y" by (unfold_locales, auto)
  show "factor_preserving_hom (poly_x_minus_y :: 'a poly \<Rightarrow> _)"
    by (unfold poly_x_minus_y_as_comp, rule factor_preserving_hom_comp, unfold_locales)
qed

text \<open>
  Now we show that results of @{const poly_x_minus_y} and @{const poly_lift} are coprime.
\<close>

lemma poly_y_x_const[simp]: "poly_y_x [:[:a:]:] = [:[:a:]:]" by (simp add: poly_y_x_def monom_0)

context begin

private abbreviation "y_x == [: [: 0, -1 :], 1 :]"

lemma poly_y_x_x_y[simp]: "poly_y_x x_y = y_x" by (simp add: x_y_def poly_y_x_def monom_Suc monom_0)

private lemma y_x[simp]: fixes x :: "'a :: comm_ring_1" shows "poly2 y_x x y = y - x"
  unfolding poly2_def by simp

private definition "poly_y_minus_x p \<equiv> poly_lift p \<circ>\<^sub>p y_x"

private lemma poly_y_minus_x_0[simp]: "poly_y_minus_x 0 = 0" by (simp add: poly_y_minus_x_def)

private lemma poly_y_minus_x_pCons[simp]:
  "poly_y_minus_x (pCons a p) = [:[: a :]:] + poly_y_minus_x p * y_x" by (simp add: poly_y_minus_x_def)

private lemma poly_y_x_poly_x_minus_y:
  fixes p :: "'a :: idom poly"
  shows "poly_y_x (poly_x_minus_y p) = poly_y_minus_x p"
  apply (induct p, simp)
  apply (unfold poly_x_minus_y_pCons hom_distribs) by simp

lemma degree_poly_y_minus_x[simp]:
  fixes p :: "'a :: idom poly"
  shows "degree (poly_y_x (poly_x_minus_y p)) = degree p" 
  by (simp add: poly_y_minus_x_def poly_y_x_poly_x_minus_y)

end

lemma dvd_all_coeffs_iff:
  fixes x :: "'a :: comm_semiring_1" (* No addition needed! *)
  shows "(\<forall>pi \<in> set (coeffs p). x dvd pi) \<longleftrightarrow> (\<forall>i. x dvd coeff p i)" (is "?l = ?r")
proof-
  have "?r = (\<forall>i\<in>{..degree p} \<union> {Suc (degree p)..}. x dvd coeff p i)" by auto
  also have "... = (\<forall>i\<le>degree p. x dvd coeff p i)" by (auto simp add: ball_Un coeff_eq_0)
  also have "... = ?l" by (auto simp: coeffs_def)
  finally show ?thesis..
qed

lemma primitive_imp_no_constant_factor:
  fixes p :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} poly"
  assumes pr: "primitive p" and F: "mset_factors F p" and fF: "f \<in># F"
  shows "degree f \<noteq> 0"
proof
  from F fF have irr: "irreducible f" and fp: "f dvd p" by (auto dest: mset_factors_imp_dvd)
  assume deg: "degree f = 0"
  then obtain f0 where f0: "f = [:f0:]" by (auto dest: degree0_coeffs)
  with fp have "[:f0:] dvd p" by simp
  then have "f0 dvd coeff p i" for i by (simp add: const_poly_dvd_iff)
  with primitiveD[OF pr] dvd_all_coeffs_iff have "f0 dvd 1" by (auto simp: coeffs_def)
  with f0 irr show False by auto
qed

lemma coprime_poly_x_minus_y_poly_lift:
  fixes p q :: "'a :: ufd poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
    and pr: "primitive p"
  shows "coprime (poly_x_minus_y p) (poly_lift q)"
proof(rule ccontr)
  from degp have p: "\<not> p dvd 1" by (auto simp: dvd_const)
  from degp have p0: "p \<noteq> 0" by auto
  from mset_factors_exist[of p, OF p0 p]
  obtain F where F: "mset_factors F p" by auto
  with poly_x_minus_y_hom.hom_mset_factors
  have pF: "mset_factors (image_mset poly_x_minus_y F) (poly_x_minus_y p)" by auto

  from degq have q: "\<not> q dvd 1" by (auto simp: dvd_const)
  from degq have q0: "q \<noteq> 0" by auto
  from mset_factors_exist[OF q0 q]
  obtain G where G: "mset_factors G q" by auto
  with poly_lift_hom.hom_mset_factors
  have pG: "mset_factors (image_mset poly_lift G) (poly_lift q)" by auto

  assume "\<not> coprime (poly_x_minus_y p) (poly_lift q)"
  from this[unfolded not_coprime_iff_common_factor]
  obtain r
  where rp: "r dvd (poly_x_minus_y p)"
    and rq: "r dvd (poly_lift q)"
    and rU: "\<not> r dvd 1" by auto note poly_lift_hom.hom_dvd
  from rp p0 have r0: "r \<noteq> 0" by auto
  from mset_factors_exist[OF r0 rU]
  obtain H where H: "mset_factors H r" by auto
  then have "H \<noteq> {#}" by auto
  then obtain h where hH: "h \<in># H" by fastforce
  with H mset_factors_imp_dvd have hr: "h dvd r" and h: "irreducible h" by auto
  from irreducible_not_unit[OF h] have hU: "\<not> h dvd 1" by auto
  from hr rp have "h dvd (poly_x_minus_y p)" by (rule dvd_trans)
  from irreducible_dvd_imp_factor[OF this h pF] p0
  obtain f where f: "f \<in># F" and fh: "poly_x_minus_y f ddvd h" by auto
  from hr rq have "h dvd (poly_lift q)" by (rule dvd_trans)
  from irreducible_dvd_imp_factor[OF this h pG] q0
  obtain g where g: "g \<in># G" and gh: "poly_lift g ddvd h" by auto
  from fh gh have "poly_x_minus_y f ddvd poly_lift g" using ddvd_trans by auto
  then have "poly_y_x (poly_x_minus_y f) ddvd poly_y_x (poly_lift g)" by simp
  also have "poly_y_x (poly_lift g) = [:g:]" unfolding poly_y_x_poly_lift monom_0 by auto
  finally have ddvd: "poly_y_x (poly_x_minus_y f) ddvd [:g:]" by auto
  then have "degree (poly_y_x (poly_x_minus_y f)) = 0" by (metis degree_pCons_0 dvd_0_left_iff dvd_const)
  then have "degree f = 0" by simp
  with primitive_imp_no_constant_factor[OF pr F f] show False by auto
qed

lemma poly_add_nonzero:
  fixes p q :: "'a :: ufd poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
      and pr: "primitive p"
  shows "poly_add p q \<noteq> 0"
proof
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by (metis gr0I)
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by (metis gr0I)
  assume 0: "poly_add p q = 0"
  from resultant_zero_imp_common_factor[OF _ this[unfolded poly_add_def]] degp
   and coprime_poly_x_minus_y_poly_lift[OF degp degq pr]
  show False by auto
qed


subsubsection \<open>Summary for addition\<close>

text \<open>Now we lift the results to one that uses @{const ipoly}, by showing some homomorphism lemmas.\<close>

lemma (in comm_ring_hom) map_poly_x_minus_y:
  "map_poly (map_poly hom) (poly_x_minus_y p) = poly_x_minus_y (map_poly hom p)"
proof-
  interpret mp: map_poly_comm_ring_hom hom..
  interpret mmp: map_poly_comm_ring_hom "map_poly hom"..
  show ?thesis
    apply (induct p, simp)
    apply(unfold x_y_def hom_distribs poly_x_minus_y_pCons, simp) done
qed

lemma (in comm_ring_hom) hom_poly_lift[simp]:
  "map_poly (map_poly hom) (poly_lift q) = poly_lift (map_poly hom q)"
proof -
  show ?thesis
    unfolding poly_lift_def
    unfolding map_poly_map_poly[of coeff_lift,OF coeff_lift_hom.hom_zero]
    unfolding map_poly_coeff_lift_hom by simp
qed


lemma lead_coeff_poly_x_minus_y:
  fixes p :: "'a::idom poly"
  shows "lead_coeff (poly_x_minus_y p) = [:lead_coeff p * ((- 1) ^ degree p):]" (is "?l = ?r")
proof-
  have "?l = Polynomial.smult (lead_coeff p) ((- 1) ^ degree p)"
    by (unfold poly_x_minus_y_def, subst lead_coeff_comp; simp add: x_y_def)
  also have "... = ?r" by (unfold hom_distribs, simp add: smult_as_map_poly[symmetric])
  finally show ?thesis.
qed

lemma (in idom_hom) poly_add_hom:
  assumes p0: "hom (lead_coeff p) \<noteq> 0" and q0: "hom (lead_coeff q) \<noteq> 0"
  shows "map_poly hom (poly_add p q) = poly_add (map_poly hom p) (map_poly hom q)"
proof -
  interpret mh: map_poly_idom_hom..
  show ?thesis unfolding poly_add_def
    apply (subst mh.resultant_map_poly(1)[symmetric])
       apply (subst degree_map_poly_2)
       apply (unfold lead_coeff_poly_x_minus_y, unfold hom_distribs, simp add: p0)
      apply simp
     apply (subst degree_map_poly_2)
      apply (simp_all add: q0 map_poly_x_minus_y)
    done
qed

lemma(in zero_hom) hom_lead_coeff_nonzero_imp_map_poly_hom:
  assumes "hom (lead_coeff p) \<noteq> 0"
  shows "map_poly hom p \<noteq> 0"
proof
  assume "map_poly hom p = 0"
  then have "coeff (map_poly hom p) (degree p) = 0" by simp
  with assms show False by simp
qed

lemma ipoly_poly_add:
  fixes x y :: "'a :: idom"
  assumes p0: "(of_int (lead_coeff p) :: 'a) \<noteq> 0" and q0: "(of_int (lead_coeff q) :: 'a) \<noteq> 0"
      and x: "ipoly p x = 0" and y: "ipoly q y = 0"
  shows "ipoly (poly_add p q) (x+y) = 0"
  using assms of_int_hom.hom_lead_coeff_nonzero_imp_map_poly_hom[OF q0]
  by (auto intro: poly_add simp: of_int_hom.poly_add_hom[OF p0 q0])

lemma (in comm_monoid_gcd) gcd_list_eq_0_iff[simp]: "listgcd xs = 0 \<longleftrightarrow> (\<forall>x \<in> set xs. x = 0)"
  by (induct xs, auto)

lemma primitive_field_poly[simp]: "primitive (p :: 'a :: field poly) \<longleftrightarrow> p \<noteq> 0"
  by (unfold primitive_iff_some_content_dvd_1,auto simp: dvd_field_iff coeffs_def)

lemma ipoly_poly_add_nonzero:
  fixes x y :: "'a :: field"
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0"
      and "(of_int (lead_coeff p) :: 'a) \<noteq> 0" and "(of_int (lead_coeff q) :: 'a) \<noteq> 0"
  shows "poly_add p q \<noteq> 0"
proof-
  from assms have "(of_int_poly (poly_add p q) :: 'a poly) \<noteq> 0"
    apply (subst of_int_hom.poly_add_hom,simp,simp)
    by (rule poly_add_nonzero, auto dest:of_int_hom.hom_lead_coeff_nonzero_imp_map_poly_hom)
  then show ?thesis by auto
qed

lemma represents_add:
  assumes x: "p represents x" and y: "q represents y"
  shows "(poly_add p q) represents (x + y)"
  using assms by (intro representsI ipoly_poly_add ipoly_poly_add_nonzero, auto)

subsection \<open>Division of Algebraic Numbers\<close>

definition poly_x_mult_y where
  [code del]: "poly_x_mult_y p \<equiv> (\<Sum> i \<le> degree p. monom (monom (coeff p i) i) i)"

lemma coeff_poly_x_mult_y:
  shows "coeff (poly_x_mult_y p) i = monom (coeff p i) i" (is "?l = ?r")
proof(cases "degree p < i")
  case i: False
  have "?l = sum (\<lambda>j. if j = i then (monom (coeff p j) j) else 0) {..degree p}"
   (is "_ = sum ?f ?A") by (simp add: poly_x_mult_y_def coeff_sum)
  also have "... = sum ?f {i}" using i by (intro sum.mono_neutral_right, auto)
  also have "... = ?f i" by simp
  also have "... = ?r" by auto
  finally show ?thesis.
next
  case True then show ?thesis by (auto simp: poly_x_mult_y_def coeff_eq_0 coeff_sum)
qed

lemma poly_x_mult_y_code[code]: "poly_x_mult_y p = (let cs = coeffs p
  in poly_of_list (map (\<lambda> (i, ai). monom ai i) (zip [0 ..< length cs] cs)))" 
  unfolding Let_def poly_of_list_def 
proof (rule poly_eqI, unfold coeff_poly_x_mult_y)
  fix n
  let ?xs = "zip [0..<length (coeffs p)] (coeffs p)" 
  let ?f = "(\<lambda>(i, ai). monom ai i)" 
  show "monom (coeff p n) n = coeff (Poly (map ?f ?xs)) n" 
  proof (cases "n < length (coeffs p)")
    case True
    hence n: "n < length (map ?f ?xs)" and nn: "n < length ?xs" 
      unfolding degree_eq_length_coeffs by auto
    show ?thesis unfolding coeff_Poly nth_default_nth[OF n] nth_map[OF nn]
      using True by (simp add: nth_coeffs_coeff)
  next
    case False
    hence id: "coeff (Poly (map ?f ?xs)) n = 0" unfolding coeff_Poly
      by (subst nth_default_beyond, auto)
    from False have "n > degree p \<or> p = 0" unfolding degree_eq_length_coeffs by (cases n, auto)
    hence "monom (coeff p n) n = 0" using coeff_eq_0[of p n] by auto
    thus ?thesis unfolding id by simp
  qed
qed

definition poly_div :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_div p q = resultant (poly_x_mult_y p) (poly_lift q)"

text \<open>@{const poly_div} has desired roots.\<close>

lemma poly2_poly_x_mult_y:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "poly2 (poly_x_mult_y p) x y = poly p (x * y)"
  apply (subst(3) poly_as_sum_of_monoms[symmetric])
  apply (unfold poly_x_mult_y_def hom_distribs)
  by (auto simp: poly2_monom poly_monom power_mult_distrib ac_simps)

lemma poly_div:
  fixes p q :: "'a ::field poly"
  assumes q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0" and y0: "y \<noteq> 0"
  shows "poly (poly_div p q) (x/y) = 0"
proof (unfold poly_div_def, rule poly_resultant_zero[OF disjI2])
  have "degree q > 0" using poly_zero q0 y by auto
  thus degq: "degree (poly_lift q) > 0" by auto
qed (insert x y y0, simp_all add: poly2_poly_x_mult_y)


text \<open>@{const poly_div} is nonzero.\<close>

interpretation poly_x_mult_y_hom: ring_hom "poly_x_mult_y :: 'a :: {idom,ring_char_0} poly \<Rightarrow> _"
  by (unfold_locales, auto intro: poly2_ext simp: poly2_poly_x_mult_y hom_distribs)

interpretation poly_x_mult_y_hom: inj_ring_hom "poly_x_mult_y :: 'a :: {idom,ring_char_0} poly \<Rightarrow> _"
proof
  let ?h = poly_x_mult_y
  fix f :: "'a poly"
  assume "?h f = 0"
  then have "poly2 (?h f) x 1 = 0" for x by simp
  from this[unfolded poly2_poly_x_mult_y]
  show "f = 0" by auto
qed

lemma degree_poly_x_mult_y[simp]:
  fixes p :: "'a :: {idom, ring_char_0} poly"
  shows "degree (poly_x_mult_y p) = degree p" (is "?l = ?r")
proof(rule antisym)
  show "?r \<le> ?l" by (cases "p=0", auto intro: le_degree simp: coeff_poly_x_mult_y)
  show "?l \<le> ?r" unfolding poly_x_mult_y_def
    by (auto intro: degree_sum_le le_trans[OF degree_monom_le])
qed

interpretation poly_x_mult_y_hom: unit_preserving_hom "poly_x_mult_y :: 'a :: field_char_0 poly \<Rightarrow> _"
proof(unfold_locales)
  let ?h = "poly_x_mult_y :: 'a poly \<Rightarrow> _"
  fix f :: "'a poly"
  assume unit: "?h f dvd 1"
  then have "degree (?h f) = 0" and "coeff (?h f) 0 dvd 1" unfolding poly_dvd_1 by auto
  then have deg: "degree f = 0" by (auto simp add: degree_monom_eq)
  with unit show "f dvd 1" by(cases "f = 0", auto)
qed

lemmas poly_y_x_o_poly_lift = o_def[of poly_y_x poly_lift, unfolded poly_y_x_poly_lift]

lemma irreducible_dvd_degree: assumes "(f::'a::field poly) dvd g"
 "irreducible g"
 "degree f > 0"
 shows "degree f = degree g"
  using assms
 by (metis irreducible_altdef degree_0 dvd_refl is_unit_field_poly linorder_neqE_nat poly_divides_conv0)

lemma coprime_poly_x_mult_y_poly_lift:
  fixes p q :: "'a :: field_char_0 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
    and nz: "poly p 0 \<noteq> 0 \<or> poly q 0 \<noteq> 0" 
  shows "coprime (poly_x_mult_y p) (poly_lift q)"
proof(rule ccontr)
  from degp have p: "\<not> p dvd 1" by (auto simp: dvd_const)
  from degp have p0: "p \<noteq> 0" by auto
  from mset_factors_exist[of p, OF p0 p]
  obtain F where F: "mset_factors F p" by auto
  then have pF: "prod_mset (image_mset poly_x_mult_y F) = poly_x_mult_y p"
    by (auto simp: hom_distribs)

  from degq have q: "\<not> is_unit q" by (auto simp: dvd_const)
  from degq have q0: "q \<noteq> 0" by auto
  from mset_factors_exist[OF q0 q]
  obtain G where G: "mset_factors G q" by auto
  with poly_lift_hom.hom_mset_factors
  have pG: "mset_factors (image_mset poly_lift G) (poly_lift q)" by auto
  from poly_y_x_hom.hom_mset_factors[OF this]
  have pG: "mset_factors (image_mset coeff_lift G) [:q:]"
    by (auto simp: poly_y_x_poly_lift monom_0 image_mset.compositionality poly_y_x_o_poly_lift)

  assume "\<not> coprime (poly_x_mult_y p) (poly_lift q)"
  then have "\<not> coprime (poly_y_x (poly_x_mult_y p)) (poly_y_x (poly_lift q))"
    by (simp del: coprime_iff_coprime)
  from this[unfolded not_coprime_iff_common_factor]
  obtain r
  where rp: "r dvd poly_y_x (poly_x_mult_y p)"
    and rq: "r dvd poly_y_x (poly_lift q)"
    and rU: "\<not> r dvd 1" by auto
  from rp p0 have r0: "r \<noteq> 0" by auto
  from mset_factors_exist[OF r0 rU]
  obtain H where H: "mset_factors H r" by auto
  then have "H \<noteq> {#}" by auto
  then obtain h where hH: "h \<in># H" by fastforce
  with H mset_factors_imp_dvd have hr: "h dvd r" and h: "irreducible h" by auto
  from irreducible_not_unit[OF h] have hU: "\<not> h dvd 1" by auto
  from hr rp have "h dvd poly_y_x (poly_x_mult_y p)" by (rule dvd_trans)
  note this[folded pF,unfolded poly_y_x_hom.hom_prod_mset image_mset.compositionality]
  from prime_elem_dvd_prod_mset[OF h[folded prime_elem_iff_irreducible] this]
  obtain f where f: "f \<in># F" and hf: "h dvd poly_y_x (poly_x_mult_y f)" by auto
  have irrF: "irreducible f" using f F by blast
    from dvd_trans[OF hr rq] have "h dvd [:q:]" by (simp add: poly_y_x_poly_lift monom_0)
    from irreducible_dvd_imp_factor[OF this h pG] q0
    obtain g where g: "g \<in># G" and gh: "[:g:] dvd h" by auto
    from dvd_trans[OF gh hf] have *: "[:g:] dvd poly_y_x (poly_x_mult_y f)" using dvd_trans by auto
  show False
  proof (cases "poly f 0 = 0")
    case f_0: False
    from poly_hom.hom_dvd[OF *]
    have "g dvd poly (poly_y_x (poly_x_mult_y f)) [:0:]" by simp
    also have "... = [:poly f 0:]" by (intro poly_ext, fold poly2_def, simp add: poly2_poly_x_mult_y)
    also have "... dvd 1" using f_0 by auto
    finally have "g dvd 1".
    with g G show False by (auto elim!: mset_factorsE dest!: irreducible_not_unit)
  next
    case True
    hence "[:0,1:] dvd f" by (unfold dvd_iff_poly_eq_0, simp)
    from irreducible_dvd_degree[OF this irrF]
    have "degree f = 1" by auto
    from degree1_coeffs[OF this] True obtain c where c: "c \<noteq> 0" and f: "f = [:0,c:]" by auto
    from g G have irrG: "irreducible g" by auto
    from poly_hom.hom_dvd[OF *]
    have "g dvd poly (poly_y_x (poly_x_mult_y f)) 1" by simp
    also have "\<dots> = f" by (auto simp: f poly_x_mult_y_code Let_def c poly_y_x_pCons map_poly_monom poly_monom poly_lift_def)
    also have "\<dots> dvd [:0,1:]" unfolding f dvd_def using c 
      by (intro exI[of _ "[: inverse c :]"], auto)
    finally have g01: "g dvd [:0,1:]" .
    from divides_degree[OF this] irrG have "degree g = 1" by auto
    from degree1_coeffs[OF this] obtain a b where g: "g = [:b,a:]" and a: "a \<noteq> 0" by auto
    from g01[unfolded dvd_def] g obtain k where id: "[:0,1:] = g * k" by auto
    from id have 0: "g \<noteq> 0" "k \<noteq> 0" by auto
    from arg_cong[OF id, of degree] have "degree k = 0" unfolding degree_mult_eq[OF 0] 
      unfolding g using a by auto
    from degree0_coeffs[OF this] obtain kk where k: "k = [:kk:]" by auto
    from id[unfolded g k] a have "b = 0" by auto
    hence "poly g 0 = 0" by (auto simp: g)
    from True this nz \<open>f \<in># F\<close> \<open>g \<in># G\<close> F G
    show False by (auto dest!:mset_factors_imp_dvd elim:dvdE)
  qed
qed

lemma poly_div_nonzero:
  fixes p q :: "'a :: field_char_0 poly"
  assumes p0: "p \<noteq> 0" and q0: "q \<noteq> 0" and x: "poly p x = 0" and y: "poly q y = 0"
      and p_0: "poly p 0 \<noteq> 0 \<or> poly q 0 \<noteq> 0"
  shows "poly_div p q \<noteq> 0"
proof
  have degp: "degree p > 0" using le_0_eq order_degree order_root p0 x by (metis gr0I)
  have degq: "degree q > 0" using le_0_eq order_degree order_root q0 y by (metis gr0I)
  assume 0: "poly_div p q = 0"
  from resultant_zero_imp_common_factor[OF _ this[unfolded poly_div_def]] degp
   and coprime_poly_x_mult_y_poly_lift[OF degp degq] p_0
  show False by auto
qed

subsubsection \<open>Summary for division\<close>

text \<open>Now we lift the results to one that uses @{const ipoly}, by showing some homomorphism lemmas.\<close>

lemma (in inj_comm_ring_hom) poly_x_mult_y_hom:
  "poly_x_mult_y (map_poly hom p) = map_poly (map_poly hom) (poly_x_mult_y p)"
proof -
  interpret mh: map_poly_inj_comm_ring_hom..
  interpret mmh: map_poly_inj_comm_ring_hom "map_poly hom"..
  show ?thesis unfolding poly_x_mult_y_def by (simp add: hom_distribs)
qed

lemma (in inj_comm_ring_hom) poly_div_hom:
  "map_poly hom (poly_div p q) = poly_div (map_poly hom p) (map_poly hom q)"
proof -
  have zero: "\<forall>x. hom x = 0 \<longrightarrow> x = 0" by simp
  interpret mh: map_poly_inj_comm_ring_hom..
  show ?thesis unfolding poly_div_def mh.resultant_hom[symmetric]
    by (simp add: poly_x_mult_y_hom)
qed

lemma ipoly_poly_div:
  fixes x y :: "'a :: field_char_0"
  assumes "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0" and "y \<noteq> 0"
  shows "ipoly (poly_div p q) (x/y) = 0"
  by (unfold of_int_hom.poly_div_hom, rule poly_div, insert assms, auto)

lemma ipoly_poly_div_nonzero:
  fixes x y :: "'a :: field_char_0"
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "ipoly p x = 0" and "ipoly q y = 0" and "poly p 0 \<noteq> 0 \<or> poly q 0 \<noteq> 0"
  shows "poly_div p q \<noteq> 0"
proof-
  from assms have "(of_int_poly (poly_div p q) :: 'a poly) \<noteq> 0" using of_int_hom.poly_map_poly[of p]
    by (subst of_int_hom.poly_div_hom, subst poly_div_nonzero, auto) 
  then show ?thesis by auto
qed

lemma represents_div:
  fixes x y :: "'a :: field_char_0"
  assumes "p represents x" and "q represents y" and "poly q 0 \<noteq> 0"
  shows "(poly_div p q) represents (x / y)"
  using assms by (intro representsI ipoly_poly_div ipoly_poly_div_nonzero, auto)


subsection \<open>Multiplication of Algebraic Numbers\<close>

definition poly_mult where "poly_mult p q \<equiv> poly_div p (reflect_poly q)"

lemma represents_mult:
  assumes px: "p represents x" and qy: "q represents y" and q_0: "poly q 0 \<noteq> 0" 
  shows "(poly_mult p q) represents (x * y)"
proof-
  from q_0 qy have y0: "y \<noteq> 0" by auto
  from represents_inverse[OF y0 qy] y0 px q_0
  have "poly_mult p q represents x / (inverse y)"
    unfolding poly_mult_def by (intro represents_div, auto)
  with y0 show ?thesis by (simp add: field_simps)
qed

subsection \<open>Summary: Closure Properties of Algebraic Numbers\<close>

lemma algebraic_representsI: "p represents x \<Longrightarrow> algebraic x"
  unfolding represents_def algebraic_altdef_ipoly by auto

lemma algebraic_of_rat: "algebraic (of_rat x)"
  by (rule algebraic_representsI[OF poly_rat_represents_of_rat])

lemma algebraic_uminus: "algebraic x \<Longrightarrow> algebraic (-x)"
  by (auto dest: algebraic_imp_represents_irreducible intro: algebraic_representsI represents_uminus)

lemma algebraic_inverse: "algebraic x \<Longrightarrow> algebraic (inverse x)"
  using algebraic_of_rat[of 0]
  by (cases "x = 0", auto dest: algebraic_imp_represents_irreducible intro: algebraic_representsI represents_inverse)

lemma algebraic_plus: "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x + y)"
  by (auto dest!: algebraic_imp_represents_irreducible_cf_pos intro!: algebraic_representsI[OF represents_add])

lemma algebraic_div:
  assumes x: "algebraic x" and y: "algebraic y" shows "algebraic (x/y)"
proof(cases "y = 0 \<or> x = 0")
  case True
  then show ?thesis using algebraic_of_rat[of 0] by auto
next
  case False
  then have x0: "x \<noteq> 0" and y0: "y \<noteq> 0" by auto
  from x y obtain p q
  where px: "p represents x" and irr: "irreducible q" and qy: "q represents y"
    by (auto dest!: algebraic_imp_represents_irreducible)
  show ?thesis
    using False px represents_irr_non_0[OF irr qy]
    by (auto intro!: algebraic_representsI[OF represents_div] qy)
qed

lemma algebraic_times: "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x * y)"
  using algebraic_div[OF _ algebraic_inverse, of x y] by (simp add: field_simps)

lemma algebraic_root: "algebraic x \<Longrightarrow> algebraic (root n x)"
proof -
  assume "algebraic x"
  then obtain p where p: "p represents x" by (auto dest: algebraic_imp_represents_irreducible_cf_pos)
  from 
    algebraic_representsI[OF represents_nth_root_neg_real[OF _ this, of n]]
    algebraic_representsI[OF represents_nth_root_pos_real[OF _ this, of n]]
    algebraic_of_rat[of 0]
  show ?thesis by (cases "n = 0", force, cases "n > 0", force, cases "n < 0", auto)
qed

lemma algebraic_nth_root: "n \<noteq> 0 \<Longrightarrow> algebraic x \<Longrightarrow> y^n = x \<Longrightarrow> algebraic y"
  by (auto dest: algebraic_imp_represents_irreducible_cf_pos intro: algebraic_representsI represents_nth_root)

hide_const x_y

end
