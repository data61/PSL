(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Executable dvdm operation\<close>

text \<open>This theory contains some results about division of integer polynomials which are not part of 
  Polynomial\_Factorization.Dvd\_Int\_Poly.thy. 

  Essentially, we give an executable implementation of division modulo m.
\<close> 

theory Missing_Dvd_Int_Poly
imports 
  Berlekamp_Zassenhaus.Poly_Mod_Finite_Field
  Berlekamp_Zassenhaus.Polynomial_Record_Based
  Berlekamp_Zassenhaus.Hensel_Lifting (* for thm pdivmod_monic, should be moved *)
  Subresultants.Subresultant (* for abbreviation pdivmod *)
  Perron_Frobenius.Cancel_Card_Constraint
begin

(*In mathematics, this lemma also works if q = 0 since degree 0 = -\<infinity>, but in Isabelle degree 0 = 0.*)
lemma degree_div_mod_smult:
  fixes g::"int poly"
  assumes g: "degree g < j"
  and r: "degree r < d"
  and u: "degree u = d"
  and g1: "g = q * u + smult m r" 
  and q: "q \<noteq> 0" and m_not0: "m \<noteq> 0"
shows "degree q < j - d"
proof -
  have u_not0: "u\<noteq>0" using u r by auto
  have d_uq: "d \<le> degree (u*q)" using u degree_mult_right_le[OF q] by auto
  have j: "j > degree (q* u + smult m r)" using g1 g by auto
  have "degree (smult m r) < d" using degree_smult_eq m_not0 r by auto
  also have "... \<le> degree (u*q)" using d_uq by auto
  finally have deg_mr_uq: "degree (smult m r) < degree (q*u)"
    by (simp add: mult.commute)
  have j2: "degree (q* u + smult m r) = degree (q*u)"
    by (rule degree_add_eq_left[OF deg_mr_uq])
  also have "... = degree q + degree u" 
    by (rule degree_mult_eq[OF q u_not0])
  finally have "degree q = degree g - degree u" using g1 by auto
  thus ?thesis 
    using j j2 \<open>degree (q * u) = degree q + degree u\<close> u 
    by linarith
qed

subsection \<open>Uniqueness of division algorithm for polynomials\<close>

lemma uniqueness_algorithm_division_poly:
  fixes f::"'a::{comm_ring,semiring_1_no_zero_divisors} poly"
  assumes f1: "f = g * q1 + r1"
      and f2: "f = g * q2 + r2"
      and g: "g \<noteq> 0"
      and r1: "r1 = 0 \<or> degree r1 < degree g"
      and r2: "r2 = 0 \<or> degree r2 < degree g"
    shows "q1 = q2 \<and> r1 = r2"
proof -
  have "0 =  g * q1 + r1 - (g * q2 + r2)" using f1 f2 by auto
  also have "... = g * (q1 - q2) + r1 - r2"
    by (simp add: right_diff_distrib)
  finally have eq: "g * (q1 - q2) = r2 - r1" by auto
  have q_eq: "q1 = q2" 
  proof (rule ccontr)
    assume q1_not_q2: "q1 \<noteq> q2" 
    hence nz: "g * (q1 - q2) \<noteq> 0" using g by auto
    hence "degree (g * (q1 - q2)) \<ge> degree g"      
      by (simp add: degree_mult_right_le)
    moreover have "degree (r2 - r1) < degree g"
      using eq nz degree_diff_less r1 r2 by auto
    ultimately show False using eq by auto
  qed
  moreover have "r1 = r2" using eq q_eq by auto
  ultimately show ?thesis by simp
qed

lemma pdivmod_eq_pdivmod_monic:
  assumes g: "monic g"
  shows "pdivmod f g = pdivmod_monic f g"
proof -
  obtain q r where qr: "pdivmod f g = (q,r)" by simp
  obtain Q R where QR: "pdivmod_monic f g = (Q,R)" by (meson surj_pair)
  have g0: "g \<noteq> 0" using g by auto
  have f1: "f = g * q + r"
    by (metis Pair_inject mult_div_mod_eq qr)
  have r: "r=0 \<or> degree r < degree g"
    by (metis Pair_inject assms degree_mod_less leading_coeff_0_iff qr zero_neq_one)
  have f2: "f = g * Q + R"    
    by (simp add: QR assms pdivmod_monic(1))
  have R: "R=0 \<or> degree R < degree g" 
    by (rule pdivmod_monic[OF g QR])  
  have "q=Q \<and> r=R" by (rule uniqueness_algorithm_division_poly[OF f1 f2 g0 r R])
  thus ?thesis using qr QR by auto
qed

context poly_mod
begin

definition "pdivmod2 f g = (if Mp g = 0 then (0, f)
 else let ilc = inverse_p m ((lead_coeff (Mp g))); 
      h = Polynomial.smult ilc (Mp g); (q, r) = pseudo_divmod (Mp f) (Mp h) 
      in (Polynomial.smult ilc q, r))"
end

context poly_mod_prime_type
begin

lemma dvdm_iff_pdivmod0:
  assumes f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g"
  shows "g dvdm f = (snd (pdivmod F G) = 0)"
proof -  
  have [transfer_rule]: "MP_Rel f F" unfolding MP_Rel_def
    by (simp add: Mp_f_representative f)  
  have [transfer_rule]: "MP_Rel g G" unfolding MP_Rel_def
    by (simp add: Mp_f_representative g)  
  have "(snd (pdivmod F G) = 0) = (G dvd F)"
    unfolding dvd_eq_mod_eq_0 by auto
  from this [untransferred] show ?thesis by simp
qed

lemma of_int_poly_Mp_0[simp]: "(of_int_poly (Mp a) = (0:: 'a mod_ring poly)) = (Mp a = 0)"
  by (auto, metis Mp_f_representative map_poly_0 poly_mod.Mp_Mp)

lemma uniqueness_algorithm_division_of_int_poly:
  assumes g0: "Mp g \<noteq> 0"
  and f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g"
  and F: "F = G * Q + R"
  and R: "R = 0 \<or> degree R < degree G"
  and Mp_f: "Mp f = Mp g * q + r"
  and r: "r = 0 \<or> degree r < degree (Mp g)"
shows "Q = of_int_poly q \<and> R = of_int_poly r"
proof (rule uniqueness_algorithm_division_poly[OF F _ _ R])
  have f': "Mp f = to_int_poly F" unfolding f 
    by (simp add: Mp_f_representative)
  have g': "Mp g = to_int_poly G" unfolding g
    by (simp add: Mp_f_representative)
  have f'': "of_int_poly (Mp f) = F"
    by (metis (no_types, lifting) Dp_Mp_eq Mp_f_representative 
        Mp_smult_m_0 add_cancel_left_right f map_poly_zero of_int_hom.map_poly_hom_add 
        to_int_mod_ring_hom.hom_zero to_int_mod_ring_hom.injectivity)
  have g'': "of_int_poly (Mp g) = G"
    by (metis (no_types, lifting) Dp_Mp_eq Mp_f_representative 
        Mp_smult_m_0 add_cancel_left_right g map_poly_zero of_int_hom.map_poly_hom_add 
        to_int_mod_ring_hom.hom_zero to_int_mod_ring_hom.injectivity)
  have "F = of_int_poly (Mp g * q + r)" using Mp_f  f'' by auto
  also have "... = G * of_int_poly q + of_int_poly r"
    by (simp add: g'' of_int_poly_hom.hom_add of_int_poly_hom.hom_mult)
  finally show "F = G * of_int_poly q + of_int_poly r" .    
  show "of_int_poly r = 0 \<or> degree (of_int_poly r::'a mod_ring poly) < degree G"
  proof (cases "r = 0")
    case True
    hence "of_int_poly r = 0" by auto
    then show ?thesis by auto
  next
    case False
    have "degree (of_int_poly r::'a mod_ring poly) \<le> degree (r)" 
    by (simp add: degree_map_poly_le)
    also have "... < degree (Mp g)" using r False by auto
    also have "... = degree G" by (simp add: g')    
    finally show ?thesis by auto
  qed
  show "G \<noteq> 0" using g0 unfolding g''[symmetric] by simp    
qed

corollary uniqueness_algorithm_division_to_int_poly:
  assumes g0: "Mp g \<noteq> 0"
  and f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g"
  and F: "F = G * Q + R"
  and R: "R = 0 \<or> degree R < degree G"
  and Mp_f: "Mp f = Mp g * q + r"
  and r: "r = 0 \<or> degree r < degree (Mp g)"
  shows "Mp q = to_int_poly Q \<and> Mp r = to_int_poly R"
  using uniqueness_algorithm_division_of_int_poly[OF assms]
  by (auto simp add: Mp_f_representative)

lemma uniqueness_algorithm_division_Mp_Rel: 
  assumes monic_Mpg: "monic (Mp g)"
    and f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g"
  and qr: "pseudo_divmod (Mp f) (Mp g) = (q,r)"
  and QR: "pseudo_divmod F G = (Q,R)"
shows "MP_Rel q Q \<and> MP_Rel r R "
proof (unfold MP_Rel_def, rule uniqueness_algorithm_division_to_int_poly[OF _ f g])
  show f_gq_r: "Mp f = Mp g * q + r" 
    by (rule pdivmod_monic(1)[OF monic_Mpg], simp add: pdivmod_monic_pseudo_divmod qr monic_Mpg)
  have monic_G: "monic G" using monic_Mpg
    using Mp_f_representative g by auto
  show "F = G * Q + R" 
    by (rule pdivmod_monic(1)[OF monic_G], simp add: pdivmod_monic_pseudo_divmod QR monic_G)
  show "Mp g \<noteq> 0" using monic_Mpg by auto
  show "R = 0 \<or> degree R < degree G"
    by (rule pdivmod_monic(2)[OF monic_G], 
        auto simp add: pdivmod_monic_pseudo_divmod monic_G intro: QR)
  show "r = 0 \<or> degree r < degree (Mp g)"
    by (rule pdivmod_monic(2)[OF monic_Mpg], 
        auto simp add: pdivmod_monic_pseudo_divmod monic_Mpg intro: qr)
qed

definition "MP_Rel_Pair A B \<equiv> (let (a,b) = A; (c,d) = B in MP_Rel a c \<and> MP_Rel b d)"

lemma pdivmod2_rel[transfer_rule]: 
  "(MP_Rel ===> MP_Rel ===> MP_Rel_Pair) (pdivmod2) (pdivmod)"
proof (auto simp add: rel_fun_def MP_Rel_Pair_def)
  interpret pm: prime_field m 
    using m unfolding prime_field_def mod_ring_locale_def by auto
  have p: "prime_field TYPE('a) m" 
    using m unfolding prime_field_def mod_ring_locale_def by auto
  fix f F g G a b 
  assume 1[transfer_rule]: "MP_Rel f F" 
     and 2[transfer_rule]: "MP_Rel g G" 
     and 3: "pdivmod2 f g = (a, b)"
  have "MP_Rel a (F div G) \<and> MP_Rel b (F mod G)"
  proof (cases "Mp g \<noteq> 0")
    case True note Mp_g = True    
    have G: "G \<noteq> 0" using Mp_g 2 unfolding MP_Rel_def by auto
    have gG[transfer_rule]: "pm.mod_ring_rel (lead_coeff (Mp g)) (lead_coeff G)" 
      using 2 
      unfolding pm.mod_ring_rel_def MP_Rel_def
      by auto  
    have [transfer_rule]: "(pm.mod_ring_rel ===> pm.mod_ring_rel) (inverse_p m) inverse"
      by (rule prime_field.mod_ring_inverse[OF p])
    hence rel_inverse_p[transfer_rule]: 
      "pm.mod_ring_rel (inverse_p m ((lead_coeff (Mp g)))) (inverse (lead_coeff G))" 
      using gG unfolding rel_fun_def by auto
    let ?h= "(Polynomial.smult (inverse_p m (lead_coeff (Mp g))) g)"
    define h where h: "h = Polynomial.smult (inverse_p m (lead_coeff (Mp g))) (Mp g)"
    define H where H: "H = Polynomial.smult (inverse (lead_coeff G)) G"
    have hH': "MP_Rel ?h H" unfolding MP_Rel_def unfolding H 
      by (metis (mono_tags, hide_lams) "2" MP_Rel_def M_to_int_mod_ring Mp_f_representative 
         rel_inverse_p functional_relation left_total_MP_Rel of_int_hom.map_poly_hom_smult 
         pm.mod_ring_rel_def right_unique_MP_Rel to_int_mod_ring_hom.injectivity to_int_mod_ring_of_int_M)
     have "Mp (Polynomial.smult (inverse_p m (lead_coeff (Mp g))) g) 
      = Mp (Polynomial.smult (inverse_p m (lead_coeff (Mp g))) (Mp g))" by simp
    hence hH: "MP_Rel h H" using hH' h unfolding MP_Rel_def by auto   
    obtain q x where pseudo_fh: "pseudo_divmod (Mp f) (Mp h) = (q, x)" by (meson surj_pair)  
    hence lc_G: "(lead_coeff G) \<noteq> 0" using G by auto
    have a: "a = Polynomial.smult (inverse_p m ((lead_coeff (Mp g)))) q" 
      using 3 pseudo_fh Mp_g 
      unfolding pdivmod2_def Let_def h by auto
    have b: "b = x" using 3 pseudo_fh Mp_g 
      unfolding pdivmod2_def Let_def h by auto  
    have Mp_Rel_FH: "MP_Rel q (F div H) \<and> MP_Rel x (F mod H)"
    proof (rule uniqueness_algorithm_division_Mp_Rel)
      show "monic (Mp h)" 
      proof -        
        have aux: "(inverse_p m (lead_coeff (Mp g))) = to_int_mod_ring (inverse (lead_coeff G))"
          using rel_inverse_p unfolding pm.mod_ring_rel_def by auto
        hence "M (inverse_p m (M (poly.coeff g (degree (Mp g))))) 
          = to_int_mod_ring (inverse (lead_coeff G))"
          by (simp add: M_to_int_mod_ring Mp_coeff)  
        thus ?thesis unfolding h unfolding Mp_coeff by auto
          (metis (no_types, lifting) "2" H MP_Rel_def Mp_coeff aux degree_smult_eq gG hH' 
          inverse_zero_imp_zero lc_G left_inverse pm.mod_ring_rel_def to_int_mod_ring_hom.degree_map_poly_hom
          to_int_mod_ring_hom.hom_one to_int_mod_ring_times)
      qed
      hence monic_H: "monic H" using hH H lc_G by auto
      show f: "F = of_int_poly f" 
        using 1 unfolding MP_Rel_def
        by (simp add: Mp_f_representative poly_eq_iff)
      have "pdivmod F H = pdivmod_monic F H" 
        by (rule pdivmod_eq_pdivmod_monic[OF monic_H])
      also have "... = pseudo_divmod F H" 
        by (rule pdivmod_monic_pseudo_divmod[OF monic_H])
      finally show "pseudo_divmod F H = (F div H, F mod H)" by simp
      show "H = of_int_poly h"
        by (meson MP_Rel_def Mp_f_representative hH right_unique_MP_Rel right_unique_def)
      show "pseudo_divmod (Mp f) (Mp h) = (q, x)" by (rule pseudo_fh)
    qed
    hence Mp_Rel_F_div_H: "MP_Rel q (F div H)" and Mp_Rel_F_mod_H: "MP_Rel x (F mod H)" by auto  
    have "F div H = Polynomial.smult (lead_coeff G) (F div G)" 
      unfolding H using div_smult_right[OF lc_G] inverse_inverse_eq
      by (metis div_smult_right inverse_zero)
    hence F_div_G: "(F div G) = Polynomial.smult (inverse (lead_coeff G)) (F div H)"
      using lc_G by auto
    have "MP_Rel a (F div G)" 
    proof -
      have "of_int_poly (Polynomial.smult (inverse_p m ((lead_coeff (Mp g)))) q) 
        = smult (inverse (lead_coeff G)) (F div H)" 
        by (metis (mono_tags) MP_Rel_def M_to_int_mod_ring Mp_Rel_F_div_H Mp_f_representative 
            of_int_hom.map_poly_hom_smult pm.mod_ring_rel_def rel_inverse_p right_unique_MP_Rel 
            right_unique_def to_int_mod_ring_hom.injectivity to_int_mod_ring_of_int_M)
      thus ?thesis 
      using Mp_Rel_F_div_H
      unfolding MP_Rel_def a F_div_G Mp_f_representative by auto
    qed
    moreover have "MP_Rel b (F mod G)" 
      using Mp_Rel_F_mod_H b H inverse_zero_imp_zero lc_G    
      by (metis mod_smult_right)
    ultimately show ?thesis by auto
  next
    assume Mp_g_0: "\<not> Mp g \<noteq> 0"
    hence "pdivmod2 f g = (0, f)" unfolding pdivmod2_def by auto
    hence a: "a = 0" and b: "b = f" using 3 by auto
    have G0: "G = 0" using Mp_g_0 2 unfolding MP_Rel_def by auto
    have "MP_Rel a (F div G)" unfolding MP_Rel_def G0 a by auto
    moreover have "MP_Rel b (F mod G)" using 1 unfolding MP_Rel_def G0 a b by auto
    ultimately show ?thesis by simp
  qed
  thus "MP_Rel a (F div G)" and "MP_Rel b (F mod G)" by auto
qed

subsection \<open>Executable division operation modulo $m$ for polynomials\<close>

lemma dvdm_iff_Mp_pdivmod2:
  shows "g dvdm f = (Mp (snd (pdivmod2 f g)) = 0)"  
proof -  
  let ?F="(of_int_poly f)::'a mod_ring poly"
  let ?G="(of_int_poly g)::'a mod_ring poly"
  have a[transfer_rule]: "MP_Rel f ?F"
    by (simp add: MP_Rel_def Mp_f_representative)
  have b[transfer_rule]: "MP_Rel g ?G" 
    by (simp add: MP_Rel_def Mp_f_representative)
  have "MP_Rel_Pair (pdivmod2 f g) (pdivmod ?F ?G)" 
    using pdivmod2_rel unfolding rel_fun_def using a b by auto
  hence "MP_Rel (snd (pdivmod2 f g)) (snd (pdivmod ?F ?G))" 
    unfolding MP_Rel_Pair_def by auto
  hence "(Mp (snd (pdivmod2 f g)) = 0) = (snd (pdivmod ?F ?G) = 0)" 
    unfolding MP_Rel_def by auto
  thus ?thesis using dvdm_iff_pdivmod0 by auto
qed
   
end

lemmas (in poly_mod_prime) dvdm_pdivmod = poly_mod_prime_type.dvdm_iff_Mp_pdivmod2
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, 
   unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemma (in poly_mod) dvdm_code:
   "g dvdm f = (if prime m then Mp (snd (pdivmod2 f g)) = 0 
    else Code.abort (STR ''dvdm error: m is not a prime number'') (\<lambda> _. g dvdm f))"
  using poly_mod_prime.dvdm_pdivmod[unfolded poly_mod_prime_def]
  by auto

declare poly_mod.pdivmod2_def[code]
declare poly_mod.dvdm_code[code]

end
