(*
    Author:      René Thiemann
    License:     BSD
*)

section \<open>GCD of rational polynomials via GCD for integer polynomials\<close>

text \<open>This theory contains an algorithm to compute GCDs of rational polynomials via 
  a conversion to integer polynomials and then invoking the integer polynomial GCD algorithm.\<close>

theory Gcd_Rat_Poly
imports 
  Gauss_Lemma
  "HOL-Computational_Algebra.Field_as_Ring"
begin

definition gcd_rat_poly :: "rat poly \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "gcd_rat_poly f g = (let
     f' = snd (rat_to_int_poly f);
     g' = snd (rat_to_int_poly g);
     h = map_poly rat_of_int (gcd f' g')
   in smult (inverse (lead_coeff h)) h)"

lemma gcd_rat_poly[simp]: "gcd_rat_poly = gcd"
proof (intro ext)
  fix f g
  let ?ri = "map_poly rat_of_int"
  obtain a' f' where faf': "rat_to_int_poly f = (a',f')" by force
  from rat_to_int_poly[OF this] obtain a where 
    f: "f = smult a (?ri f')" and a: "a \<noteq> 0" by auto
  obtain b' g' where gbg': "rat_to_int_poly g = (b',g')" by force
  from rat_to_int_poly[OF this] obtain b where 
    g: "g = smult b (?ri g')" and b: "b \<noteq> 0" by auto
  define h where "h = gcd f' g'"
  let ?h = "?ri h"
  define lc where "lc = inverse (coeff ?h (degree ?h))"
  let ?gcd = "smult lc ?h"
  have id: "gcd_rat_poly f g = ?gcd"
    unfolding lc_def h_def gcd_rat_poly_def Let_def faf' gbg' snd_conv by auto
  show "gcd_rat_poly f g = gcd f g" unfolding id
  proof (rule gcdI)
    have "h dvd f'" unfolding h_def by auto
    hence "?h dvd ?ri f'" unfolding dvd_def by (auto simp: hom_distribs)
    hence "?h dvd f" unfolding f by (rule dvd_smult)
    thus dvd_f: "?gcd dvd f"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    have "h dvd g'" unfolding h_def by auto
    hence "?h dvd ?ri g'" unfolding dvd_def by (auto simp: hom_distribs)
    hence "?h dvd g" unfolding g by (rule dvd_smult)
    thus dvd_g: "?gcd dvd g"
      by (metis dvdE inverse_zero_imp_zero lc_def leading_coeff_neq_0 mult_eq_0_iff smult_dvd_iff)
    show "normalize ?gcd = ?gcd"
      by (cases "lc = 0")
        (simp_all add: normalize_poly_def pCons_one field_simps lc_def)
    fix k
    assume dvd: "k dvd f" "k dvd g"
    obtain k' c where kck: "rat_to_normalized_int_poly k = (c,k')" by force
    from rat_to_normalized_int_poly[OF this] have k: "k = smult c (?ri k')" and c: "c \<noteq> 0" by auto
    from dvd(1) have kf: "k dvd ?ri f'" unfolding f using a by (rule dvd_smult_cancel)
    from dvd(2) have kg: "k dvd ?ri g'" unfolding g using b by (rule dvd_smult_cancel)
    from kf kg obtain kf kg where kf: "?ri f' = k * kf" and kg: "?ri g' = k * kg" unfolding dvd_def by auto    
    from rat_to_int_factor_explicit[OF kf kck] have kf: "k' dvd f'" unfolding dvd_def by blast
    from rat_to_int_factor_explicit[OF kg kck] have kg: "k' dvd g'" unfolding dvd_def by blast
    from kf kg have "k' dvd h" unfolding h_def by simp
    hence "?ri k' dvd ?ri h" unfolding dvd_def by (auto simp: hom_distribs)
    hence "k dvd ?ri h" unfolding k using c by (rule smult_dvd)
    thus "k dvd ?gcd" by (rule dvd_smult)
  qed
qed

lemma gcd_rat_poly_unfold[code_unfold]: "gcd = gcd_rat_poly" by simp
end
