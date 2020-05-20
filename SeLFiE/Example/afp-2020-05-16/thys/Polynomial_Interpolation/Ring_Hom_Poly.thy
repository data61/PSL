(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Connecting Polynomials with Homomorphism Locales\<close>

theory Ring_Hom_Poly
imports 
  "HOL-Computational_Algebra.Euclidean_Algorithm"
  Ring_Hom
  Missing_Polynomial
begin

text\<open>@{term poly} as a homomorphism. Note that types differ.\<close>

interpretation poly_hom: comm_semiring_hom "\<lambda>p. poly p a" by (unfold_locales, auto)

interpretation poly_hom: comm_ring_hom "\<lambda>p. poly p a"..

interpretation poly_hom: idom_hom "\<lambda>p. poly p a"..

text \<open>@{term "(\<circ>\<^sub>p)"} as a homomorphism.\<close>

interpretation pcompose_hom: comm_semiring_hom "\<lambda>q. q \<circ>\<^sub>p p"
  using pcompose_add pcompose_mult pcompose_1 by (unfold_locales, auto)

interpretation pcompose_hom: comm_ring_hom "\<lambda>q. q \<circ>\<^sub>p p" ..

interpretation pcompose_hom: idom_hom "\<lambda>q. q \<circ>\<^sub>p p" ..



definition eval_poly :: "('a \<Rightarrow> 'b :: comm_semiring_1) \<Rightarrow> 'a :: zero poly \<Rightarrow> 'b \<Rightarrow> 'b" where
  [code del]: "eval_poly h p = poly (map_poly h p)"

lemma eval_poly_code[code]: "eval_poly h p x = fold_coeffs (\<lambda> a b. h a + x * b) p 0" 
  by (induct p, auto simp: eval_poly_def)

lemma eval_poly_as_sum:
  fixes h :: "'a :: zero \<Rightarrow> 'b :: comm_semiring_1"
  assumes "h 0 = 0"
  shows "eval_poly h p x = (\<Sum>i\<le>degree p. x^i * h (coeff p i))"
  unfolding eval_poly_def
proof (induct p)
  case 0 show ?case using assms by simp
  next case (pCons a p) thus ?case
    proof (cases "p = 0")
      case True show ?thesis by (simp add: True map_poly_simps assms)
      next case False show ?thesis
        unfolding degree_pCons_eq[OF False]
        unfolding sum.atMost_Suc_shift
        unfolding map_poly_pCons[OF pCons(1)]
        by (simp add: pCons(2) sum_distrib_left mult.assoc)
  qed
qed

lemma coeff_const: "coeff [: a :] i = (if i = 0 then a else 0)"
  by (metis coeff_monom monom_0)

lemma x_as_monom: "[:0,1:] = monom 1 1"
  by (simp add: monom_0 monom_Suc)

lemma x_pow_n: "monom 1 1 ^ n = monom 1 n"
  by (induct n) (simp_all add: monom_0 monom_Suc)

lemma map_poly_eval_poly: assumes h0: "h 0 = 0"
  shows "map_poly h p = eval_poly (\<lambda> a. [: h a :]) p [:0,1:]" (is "?mp = ?ep")
proof (rule poly_eqI)
  fix i :: nat
  have 2: "(\<Sum>x\<le>i. \<Sum>xa\<le>degree p. (if xa = x then 1 else 0) * coeff [:h (coeff p xa):] (i - x)) 
    = h (coeff p i)" (is "sum ?f ?s = ?r")
  proof -
    have "sum ?f ?s = ?f i + sum ?f ({..i} - {i})"
      by (rule sum.remove[of _ i], auto)
    also have "sum ?f ({..i} - {i}) = 0"
      by (rule sum.neutral, intro ballI, rule sum.neutral, auto simp: coeff_const)
    also have "?f i = (\<Sum>xa\<le>degree p. (if xa = i then 1 else 0) * h (coeff p xa))" (is "_ = ?m")
      unfolding coeff_const by simp
    also have "\<dots> = ?r"
    proof (cases "i \<le> degree p")
      case True
      show ?thesis
        by (subst sum.remove[of _ i], insert True, auto)
    next
      case False
      hence [simp]: "coeff p i = 0" using le_degree by blast
      show ?thesis
        by (subst sum.neutral, auto simp: h0)
    qed
    finally show ?thesis by simp
  qed
  have h'0: "[: h 0 :] = 0" using h0 by auto
  show "coeff ?mp i = coeff ?ep i"
    unfolding coeff_map_poly[of h, OF h0]
    unfolding eval_poly_as_sum[of "\<lambda>a. [: h a :]", OF h'0]
    unfolding coeff_sum
    unfolding x_as_monom x_pow_n coeff_mult
    unfolding sum.swap[of _ _ "{..degree p}"]
    unfolding coeff_monom using 2 by auto
qed

lemma smult_as_map_poly: "smult a = map_poly ((*) a)"
  by (rule ext, rule poly_eqI, subst coeff_map_poly, auto)


subsection \<open>@{const map_poly} of Homomorphisms\<close>

context zero_hom begin
  text \<open>We will consider @{term hom} is always simpler than @{term "map_poly hom"}.\<close>
  lemma map_poly_hom_monom[simp]: "map_poly hom (monom a i) = monom (hom a) i"
    by(rule map_poly_monom, auto)
  lemma coeff_map_poly_hom[simp]: "coeff (map_poly hom p) i = hom (coeff p i)"
    by (rule coeff_map_poly, rule hom_zero)
end

locale map_poly_zero_hom = base: zero_hom
begin
  sublocale zero_hom "map_poly hom" by (unfold_locales, auto)
end

text \<open>@{const map_poly} preserves homomorphisms over addition.\<close>

context comm_monoid_add_hom
begin
  lemma map_poly_hom_add[hom_distribs]:
    "map_poly hom (p + q) = map_poly hom p + map_poly hom q"
    by (rule map_poly_add; simp add: hom_distribs)
end

locale map_poly_comm_monoid_add_hom = base: comm_monoid_add_hom
begin
  sublocale comm_monoid_add_hom "map_poly hom" by (unfold_locales, auto simp:hom_distribs)
end

text \<open>To preserve homomorphisms over multiplication, it demands commutative ring homomorphisms.\<close>
context comm_semiring_hom begin
  lemma map_poly_pCons_hom[hom_distribs]: "map_poly hom (pCons a p) = pCons (hom a) (map_poly hom p)"
    unfolding map_poly_simps by auto
  lemma map_poly_hom_smult[hom_distribs]:
    "map_poly hom (smult c p) = smult (hom c) (map_poly hom p)"
    by (induct p, auto simp: hom_distribs)
  lemma poly_map_poly[simp]: "poly (map_poly hom p) (hom x) = hom (poly p x)"
    by (induct p; simp add: hom_distribs)
end

locale map_poly_comm_semiring_hom = base: comm_semiring_hom
begin
  sublocale map_poly_comm_monoid_add_hom..
  sublocale comm_semiring_hom "map_poly hom"
  proof
    show "map_poly hom 1 = 1" by simp
    fix p q show "map_poly hom (p * q) = map_poly hom p * map_poly hom q"
      by (induct p, auto simp: hom_distribs)
  qed
end

locale map_poly_comm_ring_hom = base: comm_ring_hom
begin
  sublocale map_poly_comm_semiring_hom..
  sublocale comm_ring_hom "map_poly hom"..
end

locale map_poly_idom_hom = base: idom_hom
begin
  sublocale map_poly_comm_ring_hom..
  sublocale idom_hom "map_poly hom"..
end

subsubsection \<open>Injectivity\<close>

locale map_poly_inj_zero_hom = base: inj_zero_hom
begin
  sublocale inj_zero_hom "map_poly hom"
  proof (unfold_locales)
    fix p q :: "'a poly" assume "map_poly hom p = map_poly hom q"
    from cong[of "\<lambda>p. coeff p _", OF refl this] show "p = q" by (auto intro: poly_eqI)
  qed simp
end

locale map_poly_inj_comm_monoid_add_hom = base: inj_comm_monoid_add_hom
begin
  sublocale map_poly_comm_monoid_add_hom..
  sublocale map_poly_inj_zero_hom..
  sublocale inj_comm_monoid_add_hom "map_poly hom"..
end

locale map_poly_inj_comm_semiring_hom = base: inj_comm_semiring_hom
begin
  sublocale map_poly_comm_semiring_hom..
  sublocale map_poly_inj_zero_hom..
  sublocale inj_comm_semiring_hom "map_poly hom"..
end

locale map_poly_inj_comm_ring_hom = base: inj_comm_ring_hom
begin
  sublocale map_poly_inj_comm_semiring_hom..
  sublocale inj_comm_ring_hom "map_poly hom"..
end

locale map_poly_inj_idom_hom = base: inj_idom_hom
begin
  sublocale map_poly_inj_comm_ring_hom..
  sublocale inj_idom_hom "map_poly hom"..
end




lemma degree_map_poly_le: "degree (map_poly f p) \<le> degree p"
  by(induct p;auto)

lemma coeffs_map_poly: (* An exact variant *)
  assumes "f (lead_coeff p) = 0 \<longleftrightarrow> p = 0"
  shows "coeffs (map_poly f p) = map f (coeffs p)"
  unfolding coeffs_map_poly using assms by (simp add:coeffs_def)

lemma degree_map_poly: (* An exact variant *)
  assumes "f (lead_coeff p) = 0 \<longleftrightarrow> p = 0"
  shows   "degree (map_poly f p) = degree p"
  unfolding degree_eq_length_coeffs unfolding coeffs_map_poly[of f, OF assms] by simp

context zero_hom_0 begin
  lemma degree_map_poly_hom[simp]: "degree (map_poly hom p) = degree p"
    by (rule degree_map_poly, auto)
  lemma coeffs_map_poly_hom[simp]: "coeffs (map_poly hom p) = map hom (coeffs p)"
    by (rule coeffs_map_poly, auto)
  lemma hom_lead_coeff[simp]: "lead_coeff (map_poly hom p) = hom (lead_coeff p)"
    by simp
end

context comm_semiring_hom begin

  interpretation map_poly_hom: map_poly_comm_semiring_hom..

  lemma poly_map_poly_0[simp]:
    "poly (map_poly hom p) 0 = hom (poly p 0)" (is "?l = ?r")
  proof-
    have "?l = poly (map_poly hom p) (hom 0)" by auto
    then show ?thesis unfolding poly_map_poly.
  qed

  lemma poly_map_poly_1[simp]:
    "poly (map_poly hom p) 1 = hom (poly p 1)" (is "?l = ?r")
  proof-
    have "?l = poly (map_poly hom p) (hom 1)" by auto
    then show ?thesis unfolding poly_map_poly.
  qed

  lemma map_poly_hom_as_monom_sum:
    "(\<Sum>j\<le>degree p. monom (hom (coeff p j)) j) = map_poly hom p"
  proof -
    show ?thesis
      by (subst(6) poly_as_sum_of_monoms'[OF le_refl, symmetric], simp add: hom_distribs)
  qed

  lemma map_poly_pcompose[hom_distribs]:
    "map_poly hom (f \<circ>\<^sub>p g) = map_poly hom f \<circ>\<^sub>p map_poly hom g"
    by (induct f arbitrary: g; auto simp: hom_distribs)

end

context comm_semiring_hom begin

lemma eval_poly_0[simp]: "eval_poly hom 0 x = 0" unfolding eval_poly_def by simp
lemma eval_poly_monom: "eval_poly hom (monom a n) x = hom a * x ^ n"
  unfolding eval_poly_def
  unfolding map_poly_monom[of hom, OF hom_zero] using poly_monom.

lemma poly_map_poly_eval_poly: "poly (map_poly hom p) = eval_poly hom p"
  unfolding eval_poly_def..

lemma map_poly_eval_poly: 
  "map_poly hom p = eval_poly (\<lambda> a. [: hom a :]) p [:0,1:]" 
  by (rule map_poly_eval_poly, simp)

lemma degree_extension: assumes "degree p \<le> n"
  shows "(\<Sum>i\<le>degree p. x ^ i * hom (coeff p i))
      = (\<Sum>i\<le>n. x ^ i * hom (coeff p i))" (is "?l = ?r")
proof -
  let ?f = "\<lambda> i. x ^ i * hom (coeff p i)"
  define m where "m = n - degree p"
  have n: "n = degree p + m" unfolding m_def using assms by auto
  have "?r = (\<Sum> i \<le> degree p + m. ?f i)" unfolding n ..
  also have "\<dots> = ?l + sum ?f {Suc (degree p) .. degree p + m}"
    by (subst sum.union_disjoint[symmetric], auto intro: sum.cong)
  also have "sum ?f {Suc (degree p) .. degree p + m} = 0"
    by (rule sum.neutral, auto simp: coeff_eq_0)
  finally show ?thesis by simp
qed

lemma eval_poly_add[simp]: "eval_poly hom (p + q) x = eval_poly hom p x + eval_poly hom q x"
  unfolding eval_poly_def hom_distribs..

lemma eval_poly_sum: "eval_poly hom (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. eval_poly hom (p k) x)"
proof (induct A rule: infinite_finite_induct)
  case (insert a A)
  show ?case
    unfolding sum.insert[OF insert(1-2)] insert(3)[symmetric] by simp
qed (auto simp: eval_poly_def)

lemma eval_poly_poly: "eval_poly hom p (hom x) = hom (poly p x)"
  unfolding eval_poly_def by auto

end

context comm_ring_hom begin
  interpretation map_poly_hom: map_poly_comm_ring_hom..

  lemma pseudo_divmod_main_hom:
    "pseudo_divmod_main (hom lc) (map_poly hom q) (map_poly hom r) (map_poly hom d) dr i =
     map_prod (map_poly hom) (map_poly hom) (pseudo_divmod_main lc q r d dr i)"
  proof-
    show ?thesis by (induct lc q r d dr i rule:pseudo_divmod_main.induct, auto simp: Let_def hom_distribs)
  qed
end

lemma(in inj_comm_ring_hom) pseudo_divmod_hom:
  "pseudo_divmod (map_poly hom p) (map_poly hom q) =
   map_prod (map_poly hom) (map_poly hom) (pseudo_divmod p q)"
  unfolding pseudo_divmod_def using pseudo_divmod_main_hom[of _ 0] by (cases "q = 0",auto)

lemma(in inj_idom_hom) pseudo_mod_hom:
  "pseudo_mod (map_poly hom p) (map_poly hom q) = map_poly hom (pseudo_mod p q)"
  using pseudo_divmod_hom unfolding pseudo_mod_def by auto

lemma(in idom_hom) map_poly_pderiv[hom_distribs]:
  "map_poly hom (pderiv p) = pderiv (map_poly hom p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  then show ?case unfolding pderiv.simps map_poly_pCons_hom by (cases "p = 0", auto simp: hom_distribs)
qed

context field_hom
begin

lemma map_poly_pdivmod[hom_distribs]:
  "map_prod (map_poly hom) (map_poly hom) (p div q, p mod q) =
    (map_poly hom p div map_poly hom q, map_poly hom p mod map_poly hom q)"
  (is "?l = ?r")
proof -
  let ?mp = "map_poly hom"
  interpret map_poly_hom: map_poly_idom_hom..
  obtain r s where dm: "(p div q, p mod q) = (r, s)"
    by force  
  hence r: "r = p div q" and s: "s = p mod q"
    by simp_all
  from dm [folded pdivmod_pdivmodrel] have "eucl_rel_poly p q (r, s)"
    by auto
  from this[unfolded eucl_rel_poly_iff]
  have eq: "p = r * q + s" and cond: "(if q = 0 then r = 0 else s = 0 \<or> degree s < degree q)" by auto
  from arg_cong[OF eq, of ?mp, unfolded map_poly_add]
  have eq: "?mp p = ?mp q * ?mp r + ?mp s" by (auto simp: hom_distribs)
  from cond have cond: "(if ?mp q = 0 then ?mp r = 0 else ?mp s = 0 \<or> degree (?mp s) < degree (?mp q))"
    by simp
  from eq cond have "eucl_rel_poly (?mp p) (?mp q) (?mp r, ?mp s)"
    unfolding eucl_rel_poly_iff by auto
  from this[unfolded pdivmod_pdivmodrel]
  show ?thesis unfolding dm prod.simps by simp
qed

lemma map_poly_div[hom_distribs]: "map_poly hom (p div q) = map_poly hom p div map_poly hom q"
  using map_poly_pdivmod[of p q] by simp

lemma map_poly_mod[hom_distribs]: "map_poly hom (p mod q) = map_poly hom p mod map_poly hom q"
  using map_poly_pdivmod[of p q] by simp

end

locale field_hom' = field_hom hom
  for hom :: "'a :: {field_gcd} \<Rightarrow> 'b :: {field_gcd}"
begin

lemma map_poly_normalize[hom_distribs]: "map_poly hom (normalize p) = normalize (map_poly hom p)"
  by (simp add: normalize_poly_def hom_distribs)

lemma map_poly_gcd[hom_distribs]: "map_poly hom (gcd p q) = gcd (map_poly hom p) (map_poly hom q)"
  by (induct p q rule: eucl_induct)
    (simp_all add: map_poly_normalize ac_simps hom_distribs)

end

definition div_poly :: "'a :: euclidean_semiring \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "div_poly a p = map_poly (\<lambda> c. c div a) p"

lemma smult_div_poly: assumes "\<And> c. c \<in> set (coeffs p) \<Longrightarrow> a dvd c"
  shows "smult a (div_poly a p) = p" 
  unfolding smult_as_map_poly div_poly_def 
  by (subst map_poly_map_poly, force, subst map_poly_idI, insert assms, auto)

lemma coeff_div_poly: "coeff (div_poly a f) n = coeff f n div a" 
  unfolding div_poly_def
  by (rule coeff_map_poly, auto)

locale map_poly_inj_idom_divide_hom = base: inj_idom_divide_hom
begin
sublocale map_poly_idom_hom ..
sublocale map_poly_inj_zero_hom .. 
sublocale inj_idom_hom "map_poly hom" ..
lemma divide_poly_main_hom: defines "hh \<equiv> map_poly hom" 
  shows "hh (divide_poly_main lc f g h i j) = divide_poly_main (hom lc) (hh f) (hh g) (hh h) i j"  
  unfolding hh_def
proof (induct j arbitrary: lc f g h i)
  case (Suc j lc f g h i)
  let ?h = "map_poly hom" 
  show ?case unfolding divide_poly_main.simps Let_def
    unfolding base.coeff_map_poly_hom base.hom_div[symmetric] base.hom_mult[symmetric] base.eq_iff
      if_distrib[of ?h] hom_zero
    by (rule if_cong[OF refl _ refl], subst Suc, simp add: hom_minus hom_add hom_mult)
qed simp

sublocale inj_idom_divide_hom "map_poly hom" 
proof
  fix f g :: "'a poly" 
  let ?h = "map_poly hom" 
  show "?h (f div g) = (?h f) div (?h g)" unfolding divide_poly_def if_distrib[of ?h]
    divide_poly_main_hom by simp
qed

lemma order_hom: "order (hom x) (map_poly hom f) = order x f"
  unfolding Polynomial.order_def unfolding hom_dvd_iff[symmetric]
  unfolding hom_power by (simp add: base.hom_uminus)
end


subsection \<open>Example Interpretations\<close>

abbreviation "of_int_poly \<equiv> map_poly of_int"

interpretation of_int_poly_hom: map_poly_comm_semiring_hom of_int..
interpretation of_int_poly_hom: map_poly_comm_ring_hom of_int..
interpretation of_int_poly_hom: map_poly_idom_hom of_int..
interpretation of_int_poly_hom:
  map_poly_inj_comm_ring_hom "of_int :: int  \<Rightarrow> 'a :: {comm_ring_1,ring_char_0}" ..
interpretation of_int_poly_hom:
  map_poly_inj_idom_hom "of_int :: int  \<Rightarrow> 'a :: {idom,ring_char_0}" ..


text \<open>The following operations are homomorphic w.r.t. only @{class monoid_add}.\<close>

interpretation pCons_0_hom: injective "pCons 0" by (unfold_locales, auto)
interpretation pCons_0_hom: zero_hom_0 "pCons 0" by (unfold_locales, auto)
interpretation pCons_0_hom: inj_comm_monoid_add_hom "pCons 0" by (unfold_locales, auto)
interpretation pCons_0_hom: inj_ab_group_add_hom "pCons 0" by (unfold_locales, auto)

interpretation monom_hom: injective "\<lambda>x. monom x d" by (unfold_locales, auto)
interpretation monom_hom: inj_monoid_add_hom "\<lambda>x. monom x d" by (unfold_locales, auto simp: add_monom)
interpretation monom_hom: inj_comm_monoid_add_hom "\<lambda>x. monom x d"..

end
