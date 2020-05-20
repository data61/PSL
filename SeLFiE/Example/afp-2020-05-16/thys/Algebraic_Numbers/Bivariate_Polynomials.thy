(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Resultants\<close>

text \<open>We need some results on resultants to show that 
  a suitable prime for Berlekamp's algorithm always exists
  if the input is square free. Most of this theory has
  been developed for algebraic numbers, though. We moved this
  theory here, so that algebraic numbers can already use the
  factorization algorithm of this entry.\<close>

subsection \<open>Bivariate Polynomials\<close>

theory Bivariate_Polynomials
imports 
  Polynomial_Interpolation.Ring_Hom_Poly
  Subresultants.More_Homomorphisms 
  Berlekamp_Zassenhaus.Unique_Factorization_Poly (* Only for preserving sublocaling *)
begin

subsubsection \<open>Evaluation of Bivariate Polynomials\<close>

definition poly2 :: "'a::comm_semiring_1 poly poly \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "poly2 p x y = poly (poly p [: y :]) x"

lemma poly2_by_map: "poly2 p x = poly (map_poly (\<lambda>c. poly c x) p)"
  apply (rule ext) unfolding poly2_def by (induct p; simp)

lemma poly2_const[simp]: "poly2 [:[:a:]:] x y = a" by (simp add: poly2_def)
lemma poly2_smult[simp,hom_distribs]: "poly2 (smult a p) x y = poly a x * poly2 p x y" by (simp add: poly2_def)

interpretation poly2_hom: comm_semiring_hom "\<lambda>p. poly2 p x y" by (unfold_locales; simp add: poly2_def)
interpretation poly2_hom: comm_ring_hom "\<lambda>p. poly2 p x y"..
interpretation poly2_hom: idom_hom "\<lambda>p. poly2 p x y"..

lemma poly2_pCons[simp,hom_distribs]: "poly2 (pCons a p) x y = poly a x + y * poly2 p x y" by (simp add: poly2_def)
lemma poly2_monom: "poly2 (monom a n) x y = poly a x * y ^ n" by (auto simp: poly_monom poly2_def)

lemma poly_poly_as_poly2: "poly2 p x (poly q x) = poly (poly p q) x" by (induct p; simp add:poly2_def)

text \<open>The following lemma is an extension rule for bivariate polynomials.\<close>

lemma poly2_ext:
  fixes p q :: "'a :: {ring_char_0,idom} poly poly"
  assumes "\<And>x y. poly2 p x y = poly2 q x y" shows "p = q"
proof(intro poly_ext)
  fix r x
  show "poly (poly p r) x = poly (poly q r) x"
    unfolding poly_poly_as_poly2[symmetric] using assms by auto
qed

abbreviation (input) "coeff_lift2 == \<lambda>a. [:[: a :]:]"


lemma coeff_lift2_lift: "coeff_lift2 = coeff_lift \<circ> coeff_lift" by auto

definition "poly_lift = map_poly coeff_lift"
definition "poly_lift2 = map_poly coeff_lift2"

lemma degree_poly_lift[simp]: "degree (poly_lift p) = degree p"
  unfolding poly_lift_def by(rule degree_map_poly; auto)

lemma poly_lift_0[simp]: "poly_lift 0 = 0" unfolding poly_lift_def by simp

lemma poly_lift_0_iff[simp]: "poly_lift p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_lift_def by(induct p;simp)

lemma poly_lift_pCons[simp]:
  "poly_lift (pCons a p) = pCons [:a:] (poly_lift p)"
  unfolding poly_lift_def map_poly_simps by simp

lemma coeff_poly_lift[simp]:
  fixes p:: "'a :: comm_monoid_add poly"
  shows "coeff (poly_lift p) i = coeff_lift (coeff p i)"
  unfolding poly_lift_def by simp

interpretation poly_lift_hom: inj_comm_monoid_add_hom poly_lift
proof-
  interpret map_poly_inj_comm_monoid_add_hom coeff_lift..
  show "inj_comm_monoid_add_hom poly_lift" by (unfold_locales, auto simp: poly_lift_def hom_distribs)
qed
interpretation poly_lift_hom: inj_comm_semiring_hom poly_lift
proof-
  interpret map_poly_inj_comm_semiring_hom coeff_lift..
  show "inj_comm_semiring_hom poly_lift" by (unfold_locales, auto simp add: poly_lift_def hom_distribs)
qed
interpretation poly_lift_hom: inj_comm_ring_hom poly_lift..
interpretation poly_lift_hom: inj_idom_hom poly_lift..

lemma (in comm_monoid_add_hom) map_poly_hom_coeff_lift[simp, hom_distribs]:
  "map_poly hom (coeff_lift a) = coeff_lift (hom a)" by (cases "a=0";simp)

lemma (in comm_ring_hom) map_poly_coeff_lift_hom:
  "map_poly (coeff_lift \<circ> hom) p = map_poly (map_poly hom) (map_poly coeff_lift p)"
proof (induct p)
  case (pCons a p) show ?case
    proof(cases "a = 0")
      case True
        hence "poly_lift p \<noteq> 0" using pCons(1) by simp
        thus ?thesis
          unfolding map_poly_pCons[OF pCons(1)]
          unfolding pCons(2) True by simp
      next case False
        hence "coeff_lift a \<noteq> 0" by simp
        thus ?thesis
        unfolding map_poly_pCons[OF pCons(1)]
        unfolding pCons(2) by simp
    qed
qed auto

lemma poly_poly_lift[simp]:
  fixes p :: "'a :: comm_semiring_0 poly"
  shows "poly (poly_lift p) [:x:] = [: poly p x :]"
proof (induct p)
  case 0 show ?case by simp
  next case (pCons a p) show ?case
    unfolding poly_lift_pCons
    unfolding poly_pCons
    unfolding pCons apply (subst mult.commute) by auto
qed

lemma degree_poly_lift2[simp]:
  "degree (poly_lift2 p) = degree p" unfolding poly_lift2_def by (induct p; auto)

lemma poly_lift2_0[simp]: "poly_lift2 0 = 0" unfolding poly_lift2_def by simp

lemma poly_lift2_0_iff[simp]: "poly_lift2 p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_lift2_def by(induct p;simp)

lemma poly_lift2_pCons[simp]:
  "poly_lift2 (pCons a p) = pCons [:[:a:]:] (poly_lift2 p)"
  unfolding poly_lift2_def map_poly_simps by simp

lemma poly_lift2_lift: "poly_lift2 = poly_lift \<circ> poly_lift" (is "?l = ?r")
proof
  fix p show "?l p = ?r p"
    unfolding poly_lift2_def coeff_lift2_lift poly_lift_def by (induct p; auto)
qed

lemma poly2_poly_lift[simp]: "poly2 (poly_lift p) x y = poly p y" by (induct p;simp)

lemma poly_lift2_nonzero:
  assumes "p \<noteq> 0" shows "poly_lift2 p \<noteq> 0"
  unfolding poly_lift2_def
  apply (subst map_poly_zero)
  using assms by auto

subsubsection \<open>Swapping the Order of Variables\<close>

definition
  "poly_y_x p \<equiv> \<Sum>i\<le>degree p. \<Sum>j\<le>degree (coeff p i). monom (monom (coeff (coeff p i) j) i) j"

lemma poly_y_x_fix_y_deg:
  assumes ydeg: "\<forall>i\<le>degree p. degree (coeff p i) \<le> d"
  shows "poly_y_x p = (\<Sum>i\<le>degree p. \<Sum>j\<le>d. monom (monom (coeff (coeff p i) j) i) j)"
    (is "_ = sum (\<lambda>i. sum (?f i) _) _")
  unfolding poly_y_x_def
  apply (rule sum.cong,simp)
  unfolding atMost_iff
proof -
  fix i assume i: "i \<le> degree p"
  let ?d = "degree (coeff p i)"
  have "{..d} = {..?d} \<union> {Suc ?d .. d}" using ydeg[rule_format, OF i] by auto
  also have "sum (?f i) ... = sum (?f i) {..?d} + sum (?f i) {Suc ?d .. d}"
    by(rule sum.union_disjoint,auto)
  also { fix j
    assume j: "j \<in> { Suc ?d .. d }"
    have "coeff (coeff p i) j = 0" apply (rule coeff_eq_0) using j by auto
    hence "?f i j = 0" by auto
  } hence "sum (?f i) {Suc ?d .. d} = 0" by auto
  finally show "sum (?f i) {..?d} = sum (?f i) {..d}" by auto
qed

lemma poly_y_x_fixed_deg:
  fixes p :: "'a :: comm_monoid_add poly poly"
  defines "d \<equiv> Max { degree (coeff p i) | i. i \<le> degree p }" 
  shows "poly_y_x p = (\<Sum>i\<le>degree p. \<Sum>j\<le>d. monom (monom (coeff (coeff p i) j) i) j)"
  apply (rule poly_y_x_fix_y_deg, intro allI impI)
  unfolding d_def
  by (subst Max_ge,auto)

lemma poly_y_x_swapped:
  fixes p :: "'a :: comm_monoid_add poly poly"
  defines "d \<equiv> Max { degree (coeff p i) | i. i \<le> degree p }" 
  shows "poly_y_x p = (\<Sum>j\<le>d. \<Sum>i\<le>degree p. monom (monom (coeff (coeff p i) j) i) j)"
  using poly_y_x_fixed_deg[of p, folded d_def] sum.swap by auto

lemma poly2_poly_y_x[simp]: "poly2 (poly_y_x p) x y = poly2 p y x"
  using [[unfold_abs_def = false]]
  apply(subst(3) poly_as_sum_of_monoms[symmetric])
  apply(subst poly_as_sum_of_monoms[symmetric,of "coeff p _"])
  unfolding poly_y_x_def
  unfolding coeff_sum monom_sum
  unfolding poly2_hom.hom_sum
  apply(rule sum.cong, simp)
  apply(rule sum.cong, simp)
  unfolding poly2_monom poly_monom
  unfolding mult.assoc
  unfolding mult.commute..

context begin
private lemma poly_monom_mult:
  fixes p :: "'a :: comm_semiring_1"
  shows "poly (monom p i * q ^ j) y = poly (monom p j * [:y:] ^ i) (poly q y)"
  unfolding poly_hom.hom_mult
  unfolding poly_monom
  apply(subst mult.assoc)
  apply(subst(2) mult.commute)
  by (auto simp: mult.assoc)

lemma poly_poly_y_x:
  fixes p :: "'a :: comm_semiring_1 poly poly"
  shows "poly (poly (poly_y_x p) q) y = poly (poly p [:y:]) (poly q y)"
  apply(subst(5) poly_as_sum_of_monoms[symmetric])
  apply(subst poly_as_sum_of_monoms[symmetric,of "coeff p _"])
  unfolding poly_y_x_def
  unfolding coeff_sum monom_sum
  unfolding poly_hom.hom_sum
  apply(rule sum.cong, simp)
  apply(rule sum.cong, simp)
  unfolding atMost_iff
  unfolding poly2_monom poly_monom
  apply(subst poly_monom_mult)..

end

interpretation poly_y_x_hom: zero_hom poly_y_x by (unfold_locales, auto simp: poly_y_x_def)
interpretation poly_y_x_hom: one_hom poly_y_x by (unfold_locales, auto simp: poly_y_x_def monom_0)


lemma map_poly_sum_commute:
  assumes "h 0 = 0" "\<forall>p q. h (p + q) = h p + h q"
  shows "sum (\<lambda>i. map_poly h (f i)) S = map_poly h (sum f S)"
  apply(induct S rule: infinite_finite_induct)
  using map_poly_add[OF assms] by auto

lemma poly_y_x_const: "poly_y_x [:p:] = poly_lift p" (is "?l = ?r")
proof -
  have "?l = (\<Sum>j\<le>degree p. monom [:coeff p j:] j)"
    unfolding poly_y_x_def by (simp add: monom_0)
  also have "... = poly_lift (\<Sum>x\<le>degree p. monom (coeff p x) x)"
    unfolding poly_lift_hom.hom_sum unfolding poly_lift_def by simp
  also have "... = poly_lift p" unfolding poly_as_sum_of_monoms..
  finally show ?thesis.
qed

lemma poly_y_x_pCons:
  shows "poly_y_x (pCons a p) = poly_lift a + map_poly (pCons 0) (poly_y_x p)"
proof(cases "p = 0")
  interpret ml: map_poly_comm_monoid_add_hom "coeff_lift"..
  interpret mc: map_poly_comm_monoid_add_hom "pCons 0"..
  interpret mm: map_poly_comm_monoid_add_hom "\<lambda>x. monom x i" for i..
  { case False show ?thesis (* I know this is a worst kind of a proof... *)
    apply(subst(1) poly_y_x_fixed_deg)
    apply(unfold degree_pCons_eq[OF False])
    apply(subst(2) atLeast0AtMost[symmetric])
    apply(subst atLeastAtMost_insertL[OF le0,symmetric])
    apply(subst sum.insert,simp,simp)
    apply(unfold coeff_pCons_0)
    apply(unfold monom_0)
    apply(fold coeff_lift_hom.map_poly_hom_monom poly_lift_def)
    apply(fold poly_lift_hom.hom_sum)
    apply(subst poly_as_sum_of_monoms')
    apply(subst Max_ge,simp,simp,force,simp)
    apply(rule cong[of "\<lambda>x. poly_lift a + x", OF refl])
    apply(simp only: image_Suc_atLeastAtMost [symmetric])
    apply(unfold atLeast0AtMost)
    apply(subst sum.reindex,simp)
    apply(unfold o_def)
    apply(unfold coeff_pCons_Suc)
    apply(unfold monom_Suc)
    apply (subst poly_y_x_fix_y_deg[of _ "Max {degree (coeff (pCons a p) i) | i. i \<le> Suc (degree p)}"])
    apply (intro allI impI)
    apply (rule Max.coboundedI)
    by (auto simp: hom_distribs intro: exI[of _ "Suc _"])
  }
  case True show ?thesis by (simp add: True poly_y_x_const)
qed

lemma poly_y_x_pCons_0: "poly_y_x (pCons 0 p) = map_poly (pCons 0) (poly_y_x p)"
proof(cases "p=0")
  case False
  interpret mc: map_poly_comm_monoid_add_hom "pCons 0"..
  interpret mm: map_poly_comm_monoid_add_hom "\<lambda>x. monom x i" for i..
  from False show ?thesis
    apply (unfold poly_y_x_def degree_pCons_eq)
    apply (unfold sum.atMost_Suc_shift)
    by (simp add: hom_distribs monom_Suc)
qed simp

lemma poly_y_x_map_poly_pCons_0: "poly_y_x (map_poly (pCons 0) p) = pCons 0 (poly_y_x p)"
proof-
  let ?l = "\<lambda>i j. monom (monom (coeff (pCons 0 (coeff p i)) j) i) j"
  let ?r = "\<lambda>i j. pCons 0 (monom (monom (coeff (coeff p i) j) i) j)"
  have *: "(\<Sum>j\<le>degree (pCons 0 (coeff p i)). ?l i j) = (\<Sum>j\<le>degree (coeff p i). ?r i j)" for i
  proof(cases "coeff p i = 0")
    case True then show ?thesis by simp
  next
    case False
    show ?thesis
      apply (unfold degree_pCons_eq[OF False])
      apply (unfold sum.atMost_Suc_shift,simp)
      apply (fold monom_Suc)..
  qed
  show ?thesis
    apply (unfold poly_y_x_def)
    apply (unfold hom_distribs pCons_0_hom.degree_map_poly_hom pCons_0_hom.coeff_map_poly_hom)
    unfolding *..
qed

interpretation poly_y_x_hom: comm_monoid_add_hom "poly_y_x :: 'a :: comm_monoid_add poly poly \<Rightarrow> _"
proof (unfold_locales)
  fix p q :: "'a poly poly"
  show "poly_y_x (p + q) = poly_y_x p + poly_y_x q"
  proof (induct p arbitrary:q)
    case 0 show ?case by simp
  next
    case p: (pCons a p)
    show ?case
    proof (induct q)
      case q: (pCons b q)
      show ?case
      apply (unfold add_pCons)
      apply (unfold poly_y_x_pCons)
      apply (unfold p)
      by (simp add: poly_y_x_const ac_simps hom_distribs)
    qed auto
  qed
qed

text \<open>@{const poly_y_x} is bijective.\<close>
lemma poly_y_x_poly_lift:
  fixes p :: "'a :: comm_monoid_add poly"
  shows "poly_y_x (poly_lift p) = [:p:]"
  apply(subst poly_y_x_fix_y_deg[of _ 0],force)
  apply(subst(10) poly_as_sum_of_monoms[symmetric])
  by (auto simp add: monom_sum monom_0 hom_distribs)

lemma poly_y_x_id[simp]:
  fixes p:: "'a :: comm_monoid_add poly poly"
  shows "poly_y_x (poly_y_x p) = p"
proof (induct p)
  case 0
  then show ?case by simp
next
  case (pCons a p)
  interpret mm: map_poly_comm_monoid_add_hom "\<lambda>x. monom x i" for i..
  interpret mc: map_poly_comm_monoid_add_hom "pCons 0" ..
  have pCons_as_add: "pCons a p = [:a:] + pCons 0 p" by simp
  from pCons show ?case
    apply (unfold pCons_as_add)
    by (simp add: poly_y_x_pCons poly_y_x_poly_lift poly_y_x_map_poly_pCons_0 hom_distribs)
qed

interpretation poly_y_x_hom:
  bijective "poly_y_x :: 'a :: comm_monoid_add poly poly \<Rightarrow> _"
  by(unfold bijective_eq_bij, auto intro!:o_bij[of poly_y_x])

lemma inv_poly_y_x[simp]: "Hilbert_Choice.inv poly_y_x = poly_y_x" by auto

interpretation poly_y_x_hom: comm_monoid_add_isom poly_y_x
  by (unfold_locales, auto)

lemma pCons_as_add:
  fixes p :: "'a :: comm_semiring_1 poly"
  shows "pCons a p = [:a:] + monom 1 1 * p" by (auto simp: monom_Suc)

lemma mult_pCons_0: "(*) (pCons 0 1) = pCons 0" by auto

lemma pCons_0_as_mult:(*TODO: Move *)
  shows "pCons (0 :: 'a :: comm_semiring_1)  = (\<lambda>p. pCons 0 1 * p)" by auto

lemma map_poly_pCons_0_as_mult:
  fixes p :: "'a :: comm_semiring_1 poly poly"
  shows "map_poly (pCons 0) p = [:pCons 0 1:] * p"
  apply (subst(1) pCons_0_as_mult)
  apply (fold smult_as_map_poly) by simp

lemma poly_y_x_monom:
  fixes a :: "'a :: comm_semiring_1 poly"
  shows "poly_y_x (monom a n) = smult (monom 1 n) (poly_lift a)"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  interpret map_poly_comm_monoid_add_hom "\<lambda>x. c * x" for c :: "'a poly"..
  from False show ?thesis
    apply (unfold poly_y_x_def)
    apply (unfold degree_monom_eq)
    apply (subst(2) lessThan_Suc_atMost[symmetric])
    apply (unfold sum.lessThan_Suc)
    apply (subst sum.neutral,force)
    apply (subst(14) poly_as_sum_of_monoms[symmetric])
    apply (unfold smult_as_map_poly)
    apply (auto simp: monom_altdef[unfolded x_as_monom x_pow_n,symmetric] hom_distribs)
    done
qed

lemma poly_y_x_smult:
  fixes c :: "'a :: comm_semiring_1 poly"
  shows "poly_y_x (smult c p) = poly_lift c * poly_y_x p" (is "?l = ?r")
proof-
  have "smult c p = (\<Sum>i\<le>degree p. monom (coeff (smult c p) i) i)"
    by (metis (no_types, lifting) degree_smult_le poly_as_sum_of_monoms' sum.cong)
  also have "... = (\<Sum>i\<le>degree p. monom (c * coeff p i) i)"
    by auto
  also have "poly_y_x ... = poly_lift c * (\<Sum>i\<le>degree p. smult (monom 1 i) (poly_lift (coeff p i)))"
    by (simp add: poly_y_x_monom hom_distribs)
  also have "... = poly_lift c * poly_y_x (\<Sum>i\<le>degree p. monom (coeff p i) i)"
    by (simp add: poly_y_x_monom hom_distribs)
  finally show ?thesis by (simp add: poly_as_sum_of_monoms)
qed

interpretation poly_y_x_hom:
  comm_semiring_isom "poly_y_x :: 'a :: comm_semiring_1 poly poly \<Rightarrow> _"
proof
  fix p q :: "'a poly poly"
  show "poly_y_x (p * q) = poly_y_x p * poly_y_x q"
  proof (induct p)
    case 0
    then show ?case by simp
  next
    case p: (pCons a p)
    show ?case
      apply (unfold mult_pCons_left)
      apply (unfold hom_distribs)
      apply (unfold poly_y_x_smult)
      apply (unfold poly_y_x_pCons_0)
      apply (unfold p)
      by (simp add: poly_y_x_pCons map_poly_pCons_0_as_mult field_simps)
  qed
qed

interpretation poly_y_x_hom: comm_ring_isom "poly_y_x"..
interpretation poly_y_x_hom: idom_isom "poly_y_x"..

lemma Max_degree_coeff_pCons:
  "Max { degree (coeff (pCons a p) i) | i. i \<le> degree (pCons a p)} =
   max (degree a) (Max {degree (coeff p x) |x. x \<le> degree p})"
proof (cases "p = 0")
  case True show ?thesis unfolding True by simp
next
  case False show ?thesis
    unfolding degree_pCons_eq[OF False]
    unfolding image_Collect[symmetric]
    unfolding atMost_def[symmetric]
    apply(subst(1) atLeast0AtMost[symmetric])
    unfolding atLeastAtMost_insertL[OF le0,symmetric]
    unfolding image_insert
    apply(subst Max_insert,simp,simp)
    unfolding image_Suc_atLeastAtMost [symmetric]
    unfolding image_image
    unfolding atLeast0AtMost by simp
qed


lemma degree_poly_y_x:
  fixes p :: "'a :: comm_ring_1 poly poly"
  assumes "p \<noteq> 0"
  shows "degree (poly_y_x p) = Max { degree (coeff p i) | i. i \<le> degree p }"
    (is "_ = ?d p")
  using assms
proof(induct p)
  interpret rhm: map_poly_comm_ring_hom coeff_lift ..
  let ?f = "\<lambda>p i j. monom (monom (coeff (coeff p i) j) i) j"
  case (pCons a p)
    show ?case
    proof(cases "p=0")
      case True show ?thesis unfolding True unfolding poly_y_x_pCons by auto
      next case False
        note IH = pCons(2)[OF False]
        let ?a = "poly_lift a"
        let ?p = "map_poly (pCons 0) (poly_y_x p)"
        show ?thesis
        proof(cases rule:linorder_cases[of "degree ?a" "degree ?p"])
          case less
            have dle: "degree a \<le> degree (poly_y_x p)"
              apply(rule le_trans[OF less_imp_le[OF less[simplified]]])
              using degree_map_poly_le by auto
            show ?thesis
              unfolding poly_y_x_pCons
              unfolding degree_add_eq_right[OF less]
              unfolding Max_degree_coeff_pCons
              unfolding IH[symmetric]
              unfolding max_absorb2[OF dle]
              apply (rule degree_map_poly) by auto
          next case equal
            have dega: "degree ?a = degree a" by auto
            have degp: "degree (poly_y_x p) = degree a"
              using equal[unfolded dega]
              using degree_map_poly[of "pCons 0" "poly_y_x p"] by auto
            have *: "degree (?a + ?p) = degree a"
            proof(cases "a = 0")
              case True show ?thesis using equal unfolding True by auto
              next case False show ?thesis
                apply(rule antisym)
                  apply(rule degree_add_le, simp, fold equal, simp)
                apply(rule le_degree)
                unfolding coeff_add
                using False
                by auto
            qed
            show ?thesis unfolding poly_y_x_pCons
              unfolding *
              unfolding Max_degree_coeff_pCons
              unfolding IH[symmetric]
              unfolding degp by auto
          next case greater
            have dge: "degree a \<ge> degree (poly_y_x p)"
              apply(rule le_trans[OF _ less_imp_le[OF greater[simplified]]])
              by auto
            show ?thesis
              unfolding poly_y_x_pCons
              unfolding degree_add_eq_left[OF greater]
              unfolding Max_degree_coeff_pCons
              unfolding IH[symmetric]
              unfolding max_absorb1[OF dge] by simp
       qed
   qed
qed auto

end
