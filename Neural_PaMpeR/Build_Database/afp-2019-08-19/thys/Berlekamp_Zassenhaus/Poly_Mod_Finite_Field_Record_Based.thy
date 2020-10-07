(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsubsection \<open>Over a Finite Field\<close>
theory Poly_Mod_Finite_Field_Record_Based
imports
  Poly_Mod_Finite_Field
  Finite_Field_Record_Based
  Polynomial_Record_Based
begin

locale arith_ops_record = arith_ops ops + poly_mod m for ops :: "'i arith_ops_record" and m :: int
begin
definition M_rel_i :: "'i \<Rightarrow> int \<Rightarrow> bool" where 
  "M_rel_i f F = (arith_ops_record.to_int ops f = M F)" 

definition Mp_rel_i :: "'i list \<Rightarrow> int poly \<Rightarrow> bool" where 
  "Mp_rel_i f F = (map (arith_ops_record.to_int ops) f = coeffs (Mp F))" 

lemma Mp_rel_i_Mp[simp]: "Mp_rel_i f (Mp F) = Mp_rel_i f F" unfolding Mp_rel_i_def by auto

lemma Mp_rel_i_Mp_to_int_poly_i: "Mp_rel_i f F \<Longrightarrow> Mp (to_int_poly_i ops f) = to_int_poly_i ops f" 
  unfolding Mp_rel_i_def to_int_poly_i_def by simp
end

locale mod_ring_gen = ring_ops ff_ops R for ff_ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: nontriv mod_ring \<Rightarrow> bool" +
  fixes p :: int 
  assumes p: "p = int CARD('a)"
  and of_int: "0 \<le> x \<Longrightarrow> x < p \<Longrightarrow> R (arith_ops_record.of_int ff_ops x) (of_int x)" 
  and to_int: "R y z \<Longrightarrow> arith_ops_record.to_int ff_ops y = to_int_mod_ring z" 
  and to_int': "0 \<le> arith_ops_record.to_int ff_ops y \<Longrightarrow> arith_ops_record.to_int ff_ops y < p \<Longrightarrow> 
    R y (of_int (arith_ops_record.to_int ff_ops y))" 
begin

lemma nat_p: "nat p = CARD('a)" unfolding p by simp

sublocale poly_mod_type p "TYPE('a)"
  by (unfold_locales, rule p)

lemma coeffs_to_int_poly: "coeffs (to_int_poly (x :: 'a mod_ring poly)) = map to_int_mod_ring (coeffs x)" 
  by (rule coeffs_map_poly, auto)

lemma coeffs_of_int_poly: "coeffs (of_int_poly (Mp x) :: 'a mod_ring poly) = map of_int (coeffs (Mp x))"
  apply (rule coeffs_map_poly)
  by (metis M_0 M_M Mp_coeff leading_coeff_0_iff of_int_hom.hom_zero to_int_mod_ring_of_int_M)

lemma to_int_poly_i: assumes "poly_rel f g" shows "to_int_poly_i ff_ops f = to_int_poly g"
proof -
  have *: "map (arith_ops_record.to_int ff_ops) f = coeffs (to_int_poly g)"
    unfolding coeffs_to_int_poly 
    by (rule nth_equalityI, insert assms, auto simp: list_all2_conv_all_nth poly_rel_def to_int)
  show ?thesis unfolding coeffs_eq_iff to_int_poly_i_def poly_of_list_def coeffs_Poly *
    strip_while_coeffs..
qed

lemma poly_rel_of_int_poly: assumes id: "f' = of_int_poly_i ff_ops (Mp f)" "f'' = of_int_poly (Mp f)" 
  shows "poly_rel f' f''" unfolding id poly_rel_def
  unfolding list_all2_conv_all_nth coeffs_of_int_poly of_int_poly_i_def length_map
  by (rule conjI[OF refl], intro allI impI, simp add: nth_coeffs_coeff Mp_coeff M_def, rule of_int,
    insert p, auto)

sublocale arith_ops_record ff_ops p .

lemma Mp_rel_iI: "poly_rel f1 f2 \<Longrightarrow> MP_Rel f3 f2 \<Longrightarrow> Mp_rel_i f1 f3" 
  unfolding Mp_rel_i_def MP_Rel_def poly_rel_def
  by (auto simp add: list_all2_conv_all_nth to_int intro: nth_equalityI)

lemma M_rel_iI: "R f1 f2 \<Longrightarrow> M_Rel f3 f2 \<Longrightarrow> M_rel_i f1 f3" 
  unfolding M_rel_i_def M_Rel_def by (simp add: to_int)

lemma M_rel_iI': assumes "R f1 f2" 
  shows "M_rel_i f1 (arith_ops_record.to_int ff_ops f1)" 
  by (rule M_rel_iI[OF assms], simp add: to_int[OF assms] M_Rel_def M_to_int_mod_ring)

lemma Mp_rel_iI': assumes "poly_rel f1 f2" 
  shows "Mp_rel_i f1 (to_int_poly_i ff_ops f1)" 
proof (rule Mp_rel_iI[OF assms], unfold to_int_poly_i[OF assms]) 
  show "MP_Rel (to_int_poly f2) f2" unfolding MP_Rel_def by (simp add: Mp_to_int_poly)
qed

lemma M_rel_iD: assumes "M_rel_i f1 f3"
  shows 
    "R f1 (of_int (M f3))"
    "M_Rel f3 (of_int (M f3))"  
proof -
  show "M_Rel f3 (of_int (M f3))"
    using M_Rel_def to_int_mod_ring_of_int_M by auto
  from assms show "R f1 (of_int (M f3))" 
    unfolding M_rel_i_def
    by (metis int_one_le_iff_zero_less leD linear m1 poly_mod.M_def pos_mod_conj to_int')
qed

lemma Mp_rel_iD: assumes "Mp_rel_i f1 f3"
  shows 
    "poly_rel f1 (of_int_poly (Mp f3))"
    "MP_Rel f3 (of_int_poly (Mp f3))"  
proof -
  show Rel: "MP_Rel f3 (of_int_poly (Mp f3))"
    using MP_Rel_def Mp_Mp Mp_f_representative by auto
  let ?ti = "arith_ops_record.to_int ff_ops" 
  from assms[unfolded Mp_rel_i_def] have
    *: "coeffs (Mp f3) = map ?ti f1" by auto
  {
    fix x
    assume "x \<in> set f1"
    hence "?ti x \<in> set (map ?ti f1)" by auto
    from this[folded *] have "?ti x \<in> range M"
      by (metis (no_types, lifting) MP_Rel_def M_to_int_mod_ring Rel coeffs_to_int_poly ex_map_conv range_eqI)    
    hence "?ti x \<ge> 0" "?ti x < p" unfolding M_def using m1 by auto
    hence "R x (of_int (?ti x))"
      by (rule to_int')
  }
  thus "poly_rel f1 (of_int_poly (Mp f3))" using *
    unfolding poly_rel_def coeffs_of_int_poly
    by (auto simp: list_all2_map2 list_all2_same)
qed
end

locale prime_field_gen = field_ops ff_ops R + mod_ring_gen ff_ops R p for ff_ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: prime_card mod_ring \<Rightarrow> bool" and p :: int
begin

sublocale poly_mod_prime_type p "TYPE('a)"
  by (unfold_locales, rule p)

end

lemma (in mod_ring_locale) mod_ring_rel_of_int: 
  "0 \<le> x \<Longrightarrow> x < p \<Longrightarrow> mod_ring_rel x (of_int x)" 
  unfolding mod_ring_rel_def
  by (transfer, auto simp: p)

context prime_field
begin


lemma prime_field_finite_field_ops_int: "prime_field_gen (finite_field_ops_int p) mod_ring_rel p" 
proof -
  interpret field_ops "finite_field_ops_int p" mod_ring_rel by (rule finite_field_ops_int)
  show ?thesis
    by (unfold_locales, rule p, 
    auto simp: finite_field_ops_int_def p mod_ring_rel_def of_int_of_int_mod_ring)
qed

lemma prime_field_finite_field_ops_integer: "prime_field_gen (finite_field_ops_integer (integer_of_int p)) mod_ring_rel_integer p" 
proof -
  interpret field_ops "finite_field_ops_integer (integer_of_int p)" mod_ring_rel_integer by (rule finite_field_ops_integer, simp)
  have pp: "p = int_of_integer (integer_of_int p)" by auto
  interpret int: prime_field_gen "finite_field_ops_int p" mod_ring_rel
    by (rule prime_field_finite_field_ops_int)
  show ?thesis
    by (unfold_locales, rule p, auto simp: finite_field_ops_integer_def 
      mod_ring_rel_integer_def[OF pp] urel_integer_def[OF pp] mod_ring_rel_of_int
      int.to_int[symmetric] finite_field_ops_int_def) 
qed

lemma prime_field_finite_field_ops32: assumes small: "p \<le> 65535" 
  shows "prime_field_gen (finite_field_ops32 (uint32_of_int p)) mod_ring_rel32 p" 
proof -
  let ?pp = "uint32_of_int p" 
  have ppp: "p = int_of_uint32 ?pp"
    by (subst int_of_uint32_inv, insert small p2, auto)
  note * = ppp small 
  interpret field_ops "finite_field_ops32 ?pp" mod_ring_rel32 
    by (rule finite_field_ops32, insert *)
  interpret int: prime_field_gen "finite_field_ops_int p" mod_ring_rel
    by (rule prime_field_finite_field_ops_int)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops32_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_int_def)
    thus "mod_ring_rel32 (uint32_of_int x) (of_int x)" unfolding mod_ring_rel32_def[OF *]
      by (intro exI[of _ x], auto simp: urel32_def[OF *], subst int_of_uint32_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel32 y z" 
    from this[unfolded mod_ring_rel32_def[OF *]] obtain x where yx: "urel32 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_int_def)
    show "int_of_uint32 y = to_int_mod_ring z" unfolding zx using yx unfolding urel32_def[OF *] by simp
  next
    fix y
    show "0 \<le> int_of_uint32 y \<Longrightarrow> int_of_uint32 y < p \<Longrightarrow> mod_ring_rel32 y (of_int (int_of_uint32 y))"
      unfolding mod_ring_rel32_def[OF *] urel32_def[OF *]
      by (intro exI[of _ "int_of_uint32 y"], auto simp: mod_ring_rel_of_int)
  qed
qed

lemma prime_field_finite_field_ops64: assumes small: "p \<le> 4294967295" 
  shows "prime_field_gen (finite_field_ops64 (uint64_of_int p)) mod_ring_rel64 p" 
proof -
  let ?pp = "uint64_of_int p" 
  have ppp: "p = int_of_uint64 ?pp"
    by (subst int_of_uint64_inv, insert small p2, auto)
  note * = ppp small 
  interpret field_ops "finite_field_ops64 ?pp" mod_ring_rel64
    by (rule finite_field_ops64, insert *)
  interpret int: prime_field_gen "finite_field_ops_int p" mod_ring_rel
    by (rule prime_field_finite_field_ops_int)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops64_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_int_def)
    thus "mod_ring_rel64 (uint64_of_int x) (of_int x)" unfolding mod_ring_rel64_def[OF *]
      by (intro exI[of _ x], auto simp: urel64_def[OF *], subst int_of_uint64_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel64 y z" 
    from this[unfolded mod_ring_rel64_def[OF *]] obtain x where yx: "urel64 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_int_def)
    show "int_of_uint64 y = to_int_mod_ring z" unfolding zx using yx unfolding urel64_def[OF *] by simp
  next
    fix y
    show "0 \<le> int_of_uint64 y \<Longrightarrow> int_of_uint64 y < p \<Longrightarrow> mod_ring_rel64 y (of_int (int_of_uint64 y))"
      unfolding mod_ring_rel64_def[OF *] urel64_def[OF *]
      by (intro exI[of _ "int_of_uint64 y"], auto simp: mod_ring_rel_of_int)
  qed
qed
end

context mod_ring_locale
begin
lemma mod_ring_finite_field_ops_int: "mod_ring_gen (finite_field_ops_int p) mod_ring_rel p" 
proof -
  interpret ring_ops "finite_field_ops_int p" mod_ring_rel by (rule ring_finite_field_ops_int)
  show ?thesis
    by (unfold_locales, rule p, 
      auto simp: finite_field_ops_int_def p mod_ring_rel_def of_int_of_int_mod_ring)
qed

lemma mod_ring_finite_field_ops_integer: "mod_ring_gen (finite_field_ops_integer (integer_of_int p)) mod_ring_rel_integer p" 
proof -
  interpret ring_ops "finite_field_ops_integer (integer_of_int p)" mod_ring_rel_integer by (rule ring_finite_field_ops_integer, simp)
  have pp: "p = int_of_integer (integer_of_int p)" by auto
  interpret int: mod_ring_gen "finite_field_ops_int p" mod_ring_rel
    by (rule mod_ring_finite_field_ops_int)
  show ?thesis
    by (unfold_locales, rule p, auto simp: finite_field_ops_integer_def 
      mod_ring_rel_integer_def[OF pp] urel_integer_def[OF pp] mod_ring_rel_of_int
      int.to_int[symmetric] finite_field_ops_int_def) 
qed


lemma mod_ring_finite_field_ops32: assumes small: "p \<le> 65535" 
  shows "mod_ring_gen (finite_field_ops32 (uint32_of_int p)) mod_ring_rel32 p" 
proof -
  let ?pp = "uint32_of_int p" 
  have ppp: "p = int_of_uint32 ?pp"
    by (subst int_of_uint32_inv, insert small p2, auto)
  note * = ppp small 
  interpret ring_ops "finite_field_ops32 ?pp" mod_ring_rel32 
    by (rule ring_finite_field_ops32, insert *)
  interpret int: mod_ring_gen "finite_field_ops_int p" mod_ring_rel
    by (rule mod_ring_finite_field_ops_int)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops32_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_int_def)
    thus "mod_ring_rel32 (uint32_of_int x) (of_int x)" unfolding mod_ring_rel32_def[OF *]
      by (intro exI[of _ x], auto simp: urel32_def[OF *], subst int_of_uint32_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel32 y z" 
    from this[unfolded mod_ring_rel32_def[OF *]] obtain x where yx: "urel32 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_int_def)
    show "int_of_uint32 y = to_int_mod_ring z" unfolding zx using yx unfolding urel32_def[OF *] by simp
  next
    fix y
    show "0 \<le> int_of_uint32 y \<Longrightarrow> int_of_uint32 y < p \<Longrightarrow> mod_ring_rel32 y (of_int (int_of_uint32 y))"
      unfolding mod_ring_rel32_def[OF *] urel32_def[OF *]
      by (intro exI[of _ "int_of_uint32 y"], auto simp: mod_ring_rel_of_int)
  qed
qed

lemma mod_ring_finite_field_ops64: assumes small: "p \<le> 4294967295" 
  shows "mod_ring_gen (finite_field_ops64 (uint64_of_int p)) mod_ring_rel64 p" 
proof -
  let ?pp = "uint64_of_int p" 
  have ppp: "p = int_of_uint64 ?pp"
    by (subst int_of_uint64_inv, insert small p2, auto)
  note * = ppp small 
  interpret ring_ops "finite_field_ops64 ?pp" mod_ring_rel64 
    by (rule ring_finite_field_ops64, insert *)
  interpret int: mod_ring_gen "finite_field_ops_int p" mod_ring_rel
    by (rule mod_ring_finite_field_ops_int)
  show ?thesis
  proof (unfold_locales, rule p, auto simp: finite_field_ops64_def)
    fix x
    assume x: "0 \<le> x" "x < p" 
    from int.of_int[OF this] have "mod_ring_rel x (of_int x)" by (simp add: finite_field_ops_int_def)
    thus "mod_ring_rel64 (uint64_of_int x) (of_int x)" unfolding mod_ring_rel64_def[OF *]
      by (intro exI[of _ x], auto simp: urel64_def[OF *], subst int_of_uint64_inv, insert * x, auto)
  next
    fix y z
    assume "mod_ring_rel64 y z" 
    from this[unfolded mod_ring_rel64_def[OF *]] obtain x where yx: "urel64 y x" and xz: "mod_ring_rel x z" by auto
    from int.to_int[OF xz] have zx: "to_int_mod_ring z = x" by (simp add: finite_field_ops_int_def)
    show "int_of_uint64 y = to_int_mod_ring z" unfolding zx using yx unfolding urel64_def[OF *] by simp
  next
    fix y
    show "0 \<le> int_of_uint64 y \<Longrightarrow> int_of_uint64 y < p \<Longrightarrow> mod_ring_rel64 y (of_int (int_of_uint64 y))"
      unfolding mod_ring_rel64_def[OF *] urel64_def[OF *]
      by (intro exI[of _ "int_of_uint64 y"], auto simp: mod_ring_rel_of_int)
  qed
qed
end

end
