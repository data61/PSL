(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Reconstructing Factors of Integer Polynomials\<close>

subsection \<open>Square-Free Polynomials over Finite Fields and Integers\<close>
theory Square_Free_Int_To_Square_Free_GFp
imports   
  Subresultants.Subresultant_Gcd 
  Polynomial_Factorization.Rational_Factorization
  Finite_Field
  Polynomial_Factorization.Square_Free_Factorization
begin

lemma square_free_int_rat: assumes sf: "square_free f"
  shows "square_free (map_poly rat_of_int f)"
proof -
  let ?r = "map_poly rat_of_int" 
  from sf[unfolded square_free_def] have f0: "f \<noteq> 0" "\<And> q. degree q \<noteq> 0 \<Longrightarrow> \<not> q * q dvd f" by auto
  show ?thesis
  proof (rule square_freeI)
    show "?r f \<noteq> 0" using f0 by auto
    fix q
    assume dq: "degree q > 0" and dvd: "q * q dvd ?r f" 
    hence q0: "q \<noteq> 0" by auto
    obtain q' c where norm: "rat_to_normalized_int_poly q = (c,q')" by force
    from rat_to_normalized_int_poly[OF norm] have c0: "c \<noteq> 0" by auto
    note q = rat_to_normalized_int_poly(1)[OF norm]
    from dvd obtain k where rf: "?r f = q * (q * k)" unfolding dvd_def by (auto simp: ac_simps)
    from rat_to_int_factor_explicit[OF this norm] obtain s where 
      f: "f = q' * smult (content f) s" by auto
    let ?s = "smult (content f) s" 
    from arg_cong[OF f, of ?r] c0 
    have "?r f = q * (smult (inverse c) (?r ?s))" 
      by (simp add: field_simps q hom_distribs)
    from arg_cong[OF this[unfolded rf], of "\<lambda> f. f div q"] q0 
    have "q * k = smult (inverse c) (?r ?s)" 
      by (metis nonzero_mult_div_cancel_left)
    from arg_cong[OF this, of "smult c"] have "?r ?s = q * smult c k" using c0
      by (auto simp: field_simps)
    from rat_to_int_factor_explicit[OF this norm] obtain t where "?s = q' * t" by blast
    from f[unfolded this] sf[unfolded square_free_def] f0 have "degree q' = 0" by auto
    with rat_to_normalized_int_poly(4)[OF norm] dq show False by auto
  qed
qed

lemma content_free_unit:
  assumes "content (p::'a::{idom,semiring_gcd} poly) = 1"
  shows "p dvd 1 \<longleftrightarrow> degree p = 0"
  by (insert assms, auto dest!:degree0_coeffs simp: normalize_1_iff poly_dvd_1)

lemma square_free_imp_resultant_non_zero: assumes sf: "square_free (f :: int poly)"
  shows "resultant f (pderiv f) \<noteq> 0" 
proof (cases "degree f = 0")
  case True
  from degree0_coeffs[OF this] obtain c where f: "f = [:c:]" by auto
  with sf have c: "c \<noteq> 0" unfolding square_free_def by auto  
  show ?thesis unfolding f by simp
next
  case False note deg = this
  define pp where "pp = primitive_part f" 
  define c where "c = content f"
  from sf have f0: "f \<noteq> 0" unfolding square_free_def by auto
  hence c0: "c \<noteq> 0" unfolding c_def by auto
  have f: "f = smult c pp" unfolding c_def pp_def unfolding content_times_primitive_part[of f] ..
  from sf[unfolded f] c0 have sf': "square_free pp" by (metis dvd_smult smult_0_right square_free_def)  
  from deg[unfolded f] c0 have deg': "\<And> x. degree pp > 0 \<or> x" by auto
  from content_primitive_part[OF f0] have cp: "content pp = 1" unfolding pp_def .
  let ?p' = "pderiv pp" 
  {
    assume "resultant pp ?p' = 0" 
    from this[unfolded resultant_0_gcd] have "\<not> coprime pp ?p'" by auto
    then obtain r where r: "r dvd pp" "r dvd ?p'" "\<not> r dvd 1"
      by (blast elim: not_coprimeE) 
    from r(1) obtain k where "pp = r * k" ..
    from pos_zmult_eq_1_iff_lemma[OF arg_cong[OF this, 
      of content, unfolded content_mult cp, symmetric]] content_ge_0_int[of r]
    have cr: "content r = 1" by auto
    with r(3) content_free_unit have dr: "degree r \<noteq> 0" by auto
    let ?r = "map_poly rat_of_int"
    from r(1) have dvd: "?r r dvd ?r pp" unfolding dvd_def by (auto simp: hom_distribs)
    from r(2) have "?r r dvd ?r ?p'" apply (intro of_int_poly_hom.hom_dvd) by auto
    also have "?r ?p' = pderiv (?r pp)" unfolding of_int_hom.map_poly_pderiv ..
    finally have dvd': "?r r dvd pderiv (?r pp)" by auto
    from dr have dr': "degree (?r r) \<noteq> 0" by simp
    from square_free_imp_separable[OF square_free_int_rat[OF sf']]
    have "separable (?r pp)" .
    hence cop: "coprime (?r pp) (pderiv (?r pp))" unfolding separable_def .
    from f0 f have pp0: "pp \<noteq> 0" by auto
    from dvd dvd' have "?r r dvd gcd (?r pp) (pderiv (?r pp))" by auto
    from divides_degree[OF this] pp0 have "degree (?r r) \<le> degree (gcd (?r pp) (pderiv (?r pp)))" 
      by auto
    with dr' have "degree (gcd (?r pp) (pderiv (?r pp))) \<noteq> 0" by auto
    hence "\<not> coprime (?r pp) (pderiv (?r pp))" by auto
    with cop have False by auto
  }
  hence "resultant pp ?p' \<noteq> 0" by auto
  with resultant_smult_left[OF c0, of pp ?p', folded f] c0 
  have "resultant f ?p' \<noteq> 0" by auto
  with resultant_smult_right[OF c0, of f ?p', folded pderiv_smult f] c0
  show "resultant f (pderiv f) \<noteq> 0" by auto
qed

lemma large_mod_0: assumes "(n :: int) > 1" "\<bar>k\<bar> < n" "k mod n = 0" shows "k = 0" 
proof -
  from \<open>k mod n = 0\<close> have "n dvd k"
    by auto
  then obtain m where "k = n * m" ..
  with \<open>n > 1\<close> \<open>\<bar>k\<bar> < n\<close> show ?thesis
    by (auto simp add: abs_mult)
qed

definition separable_bound :: "int poly \<Rightarrow> int" where
  "separable_bound f = max (abs (resultant f (pderiv f))) 
    (max (abs (lead_coeff f)) (abs (lead_coeff (pderiv f))))"

lemma square_free_int_imp_resultant_non_zero_mod_ring: assumes sf: "square_free f" 
  and large: "int CARD('a) > separable_bound f"
  shows "resultant (map_poly of_int f :: 'a :: prime_card mod_ring poly) (pderiv (map_poly of_int f)) \<noteq> 0
  \<and> map_poly of_int f \<noteq> (0 :: 'a mod_ring poly)" 
proof (intro conjI, rule notI)
  let ?i = "of_int :: int \<Rightarrow> 'a mod_ring"
  let ?m = "of_int_poly :: _ \<Rightarrow> 'a mod_ring poly"
  let ?f = "?m f" 
  from sf[unfolded square_free_def] have f0: "f \<noteq> 0" by auto
  hence lf: "lead_coeff f \<noteq> 0" by auto
  {
    fix k :: int
    have C1: "int CARD('a) > 1" using prime_card[where 'a = 'a] by (auto simp: prime_nat_iff)
    assume "abs k < CARD('a)" and "?i k = 0" 
    hence "k = 0" unfolding of_int_of_int_mod_ring
        by (transfer) (rule large_mod_0[OF C1])
  } note of_int_0 = this
  from square_free_imp_resultant_non_zero[OF sf]
  have non0: "resultant f (pderiv f) \<noteq> 0" .
  {
    fix g :: "int poly" 
    assume abs: "abs (lead_coeff g) < CARD('a)"
    have "degree (?m g) = degree g" by (rule degree_map_poly, insert of_int_0[OF abs], auto)
  } note deg = this
  note large = large[unfolded separable_bound_def]
  from of_int_0[of "lead_coeff f"] large lf have "?i (lead_coeff f) \<noteq> 0" by auto
  thus f0: "?f \<noteq> 0" unfolding poly_eq_iff by auto  
  assume 0: "resultant ?f (pderiv ?f) = 0" 
  have "resultant ?f (pderiv ?f) = ?i (resultant f (pderiv f))"
    unfolding of_int_hom.map_poly_pderiv[symmetric]
    by (subst of_int_hom.resultant_map_poly(1)[OF deg deg], insert large, auto simp: hom_distribs)
  from of_int_0[OF _ this[symmetric, unfolded 0]] non0
  show False using large by auto
qed

lemma square_free_int_imp_separable_mod_ring: assumes sf: "square_free f" 
  and large: "int CARD('a) > separable_bound f"
  shows "separable (map_poly of_int f :: 'a :: prime_card mod_ring poly)" 
proof - 
  define g where "g = map_poly (of_int :: int \<Rightarrow> 'a mod_ring) f"
  from square_free_int_imp_resultant_non_zero_mod_ring[OF sf large]
  have res: "resultant g (pderiv g) \<noteq> 0" and g: "g \<noteq> 0" unfolding g_def by auto
  from res[unfolded resultant_0_gcd] have "degree (gcd g (pderiv g)) = 0" by auto
  from degree0_coeffs[OF this]
  have "separable g" unfolding separable_def
    by (metis degree_pCons_0 g gcd_eq_0_iff is_unit_gcd is_unit_iff_degree)
  thus ?thesis unfolding g_def .
qed

lemma square_free_int_imp_square_free_mod_ring: assumes sf: "square_free f" 
  and large: "int CARD('a) > separable_bound f"
shows "square_free (map_poly of_int f :: 'a :: prime_card mod_ring poly)" 
  using separable_imp_square_free[OF square_free_int_imp_separable_mod_ring[OF assms]] .

end
