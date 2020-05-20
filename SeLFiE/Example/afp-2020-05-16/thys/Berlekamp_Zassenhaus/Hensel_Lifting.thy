(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Hensel Lifting\<close>

subsection \<open>Properties about Factors\<close>

text \<open>We define and prove properties of Hensel-lifting. Here, we show the result that 
  Hensel-lifting can lift a factorization mod $p$ to a factorization mod $p^n$. 
  For the lifting we have proofs for both versions, the original linear Hensel-lifting or 
  the quadratic approach from Zassenhaus. 
  Via the linear version, we also show a uniqueness result, however only in the 
  binary case, i.e., where $f = g \cdot h$. Uniqueness of the general case will later be shown 
  in theory Berlekamp-Hensel by incorporating the factorization algorithm for finite fields algorithm.\<close>

theory Hensel_Lifting
imports 
  "HOL-Computational_Algebra.Euclidean_Algorithm"
  Poly_Mod_Finite_Field_Record_Based
  Polynomial_Factorization.Square_Free_Factorization
begin


lemma uniqueness_poly_equality:
  fixes f g :: "'a :: {factorial_ring_gcd,semiring_gcd_mult_normalize} poly"
  assumes cop: "coprime f g"
  and deg: "B = 0 \<or> degree B < degree f" "B' = 0 \<or> degree B' < degree f"
  and f: "f \<noteq> 0" and eq: "A * f + B * g = A' * f + B' * g" 
  shows "A = A'" "B = B'" 
proof -
  from eq have *: "(A - A') * f = (B' - B) * g" by (simp add: field_simps)
  hence "f dvd (B' - B) * g" unfolding dvd_def by (intro exI[of _ "A - A'"], auto simp: field_simps)
  with cop[simplified] have dvd: "f dvd (B' - B)"
    by (simp add: coprime_dvd_mult_right_iff ac_simps)
  from divides_degree[OF this] have "degree f \<le> degree (B' - B) \<or> B = B'" by auto
  with degree_diff_le_max[of B' B] deg 
  show "B = B'" by auto
  with * f show "A = A'" by auto
qed

lemmas (in poly_mod_prime_type) uniqueness_poly_equality =
  uniqueness_poly_equality[where 'a="'a mod_ring", untransferred]
lemmas (in poly_mod_prime) uniqueness_poly_equality = poly_mod_prime_type.uniqueness_poly_equality
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemma pseudo_divmod_main_list_1_is_divmod_poly_one_main_list: 
  "pseudo_divmod_main_list (1 :: 'a :: comm_ring_1) q f g n = divmod_poly_one_main_list q f g n"
  by (induct n arbitrary: q f g, auto simp: Let_def)

lemma pdivmod_monic_pseudo_divmod: assumes g: "monic g" shows "pdivmod_monic f g = pseudo_divmod f g" 
proof -
  from g have id: "(coeffs g = []) = False" by auto
  from g have mon: "hd (rev (coeffs g)) = 1" by (metis coeffs_eq_Nil hd_rev id last_coeffs_eq_coeff_degree)
  show ?thesis
    unfolding pseudo_divmod_impl pseudo_divmod_list_def id if_False pdivmod_monic_def Let_def mon
      pseudo_divmod_main_list_1_is_divmod_poly_one_main_list by (auto split: prod.splits)
qed

lemma pdivmod_monic: assumes g: "monic g" and res: "pdivmod_monic f g = (q, r)"
  shows "f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  from g have g0: "g \<noteq> 0" by auto
  from pseudo_divmod[OF g0 res[unfolded pdivmod_monic_pseudo_divmod[OF g]], unfolded g]
  show "f = g * q + r" "r = 0 \<or> degree r < degree g" by auto
qed

definition dupe_monic :: "'a :: comm_ring_1  poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow>
  'a poly * 'a poly" where
  "dupe_monic D H S T U = (case pdivmod_monic (T * U) D of (q,r) \<Rightarrow>
     (S * U + H * q, r))"

lemma dupe_monic: assumes 1: "D*S + H*T = 1" 
  and mon: "monic D" 
  and dupe: "dupe_monic D H S T U = (A,B)" 
shows "A * D + B * H = U" "B = 0 \<or> degree B < degree D"
proof -
  obtain Q R where div: "pdivmod_monic ((T * U)) D = (Q,R)" by force
  from dupe[unfolded dupe_monic_def div split]
  have A: "A = (S * U + H * Q)" and B: "B = R" by auto
  from pdivmod_monic[OF mon div] have TU: "T * U = D * Q + R" and 
    deg: "R = 0 \<or> degree R < degree D" by auto
  hence R: "R = T * U - D * Q" by simp
  have "A * D + B * H = (D * S + H * T) * U" unfolding A B R by (simp add: field_simps)
  also have "\<dots> = U" unfolding 1 by simp
  finally show eq: "A * D + B * H = U" .
  show "B = 0 \<or> degree B < degree D" using deg unfolding B .
qed

lemma dupe_monic_unique: fixes D :: "'a ::  {factorial_ring_gcd,semiring_gcd_mult_normalize} poly" 
  assumes 1: "D*S + H*T = 1" 
  and mon: "monic D" 
  and dupe: "dupe_monic D H S T U = (A,B)" 
  and cop: "coprime D H"
  and other: "A' * D + B' * H = U" "B' = 0 \<or> degree B' < degree D"
shows "A' = A" "B' = B"
proof -
  from dupe_monic[OF 1 mon dupe] have one: "A * D + B * H = U" "B = 0 \<or> degree B < degree D" by auto
  from mon have D0: "D \<noteq> 0" by auto
  from uniqueness_poly_equality[OF cop one(2) other(2) D0, of A A', unfolded other, OF one(1)] 
  show "A' = A" "B' = B" by auto
qed

context ring_ops
begin
lemma poly_rel_dupe_monic_i: assumes mon: "monic D" 
  and rel: "poly_rel d D" "poly_rel h H" "poly_rel s S" "poly_rel t T" "poly_rel u U" 
shows "rel_prod poly_rel poly_rel (dupe_monic_i ops d h s t u) (dupe_monic D H S T U)" 
proof -
  note defs = dupe_monic_i_def dupe_monic_def
  note [transfer_rule] = rel
  have [transfer_rule]: "rel_prod poly_rel poly_rel 
    (pdivmod_monic_i ops (times_poly_i ops t u) d) 
    (pdivmod_monic (T * U) D)" 
    by (rule poly_rel_pdivmod_monic[OF mon], transfer_prover+)
  show ?thesis unfolding defs by transfer_prover
qed
end
              
context mod_ring_gen
begin 

lemma monic_of_int_poly: "monic D \<Longrightarrow> monic (of_int_poly (Mp D) :: 'a mod_ring poly)"
  using Mp_f_representative Mp_to_int_poly monic_Mp by auto

lemma dupe_monic_i: assumes dupe_i: "dupe_monic_i ff_ops d h s t u = (a,b)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and A: "A = to_int_poly_i ff_ops a" 
  and B: "B = to_int_poly_i ff_ops b" 
  and d: "Mp_rel_i d D" 
  and h: "Mp_rel_i h H" 
  and s: "Mp_rel_i s S" 
  and t: "Mp_rel_i t T" 
  and u: "Mp_rel_i u U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp_rel_i a A" 
  "Mp_rel_i b B"
proof -
  let ?I = "\<lambda> f. of_int_poly (Mp f) :: 'a mod_ring poly" 
  let ?i = "to_int_poly_i ff_ops" 
  note dd = Mp_rel_iD[OF d]
  note hh = Mp_rel_iD[OF h]
  note ss = Mp_rel_iD[OF s]
  note tt = Mp_rel_iD[OF t]
  note uu = Mp_rel_iD[OF u]  
  obtain A' B' where dupe: "dupe_monic (?I D) (?I H) (?I S) (?I T) (?I U) = (A',B')"  by force
  from poly_rel_dupe_monic_i[OF monic_of_int_poly[OF mon] dd(1) hh(1) ss(1) tt(1) uu(1), unfolded dupe_i dupe]
  have a: "poly_rel a A'" and b: "poly_rel b B'" by auto
  show aa: "Mp_rel_i a A" by (rule Mp_rel_iI'[OF a, folded A])
  show bb: "Mp_rel_i b B" by (rule Mp_rel_iI'[OF b, folded B])
  note Aa = Mp_rel_iD[OF aa]
  note Bb = Mp_rel_iD[OF bb]
  from poly_rel_inj[OF a Aa(1)] A have A: "A' = ?I A" by simp
  from poly_rel_inj[OF b Bb(1)] B have B: "B' = ?I B" by simp
  note Mp = dd(2) hh(2) ss(2) tt(2) uu(2)
  note [transfer_rule] = Mp
  have "(=) (D * S + H * T =m 1) (?I D * ?I S + ?I H * ?I T = 1)" by transfer_prover
  with 1 have 11: "?I D * ?I S + ?I H * ?I T = 1" by simp
  from dupe_monic[OF 11 monic_of_int_poly[OF mon] dupe, unfolded A B]
  have res: "?I A * ?I D + ?I B * ?I H = ?I U" "?I B = 0 \<or> degree (?I B) < degree (?I D)" by auto  
  note [transfer_rule] = Aa(2) Bb(2)
  have "(=) (A * D + B * H =m U) (?I A * ?I D + ?I B * ?I H = ?I U)"
       "(=) (B =m 0 \<or> degree_m B < degree_m D) (?I B = 0 \<or> degree (?I B) < degree (?I D))" by transfer_prover+
  with res have *: "A * D + B * H =m U" "B =m 0 \<or> degree_m B < degree_m D" by auto
  show "A * D + B * H =m U" by fact
  have B: "Mp B = B" using Mp_rel_i_Mp_to_int_poly_i assms(5) bb by blast
  from *(2) show "B = 0 \<or> degree B < degree D" unfolding B using degree_m_le[of D] by auto
qed

lemma Mp_rel_i_of_int_poly_i: assumes "Mp F = F"
  shows "Mp_rel_i (of_int_poly_i ff_ops F) F" 
  by (metis Mp_f_representative Mp_rel_iI' assms poly_rel_of_int_poly to_int_poly_i)

lemma dupe_monic_i_int: assumes dupe_i: "dupe_monic_i_int ff_ops D H S T U = (A,B)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and norm: "Mp D = D" "Mp H = H" "Mp S = S" "Mp T = T" "Mp U = U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp A = A" 
  "Mp B = B" 
proof -
  let ?oi = "of_int_poly_i ff_ops" 
  let ?ti = "to_int_poly_i ff_ops"
  note rel = norm[THEN Mp_rel_i_of_int_poly_i]
  obtain a b where dupe: "dupe_monic_i ff_ops (?oi D) (?oi H) (?oi S) (?oi T) (?oi U) = (a,b)" by force
  from dupe_i[unfolded dupe_monic_i_int_def this Let_def] have AB: "A = ?ti a" "B = ?ti b" by auto
  from dupe_monic_i[OF dupe 1 mon AB rel] Mp_rel_i_Mp_to_int_poly_i 
  show "A * D + B * H =m U" 
    "B = 0 \<or> degree B < degree D" 
    "Mp A = A" 
    "Mp B = B"
    unfolding AB by auto
qed

end

definition dupe_monic_dynamic 
  :: "int \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "dupe_monic_dynamic p = ( 
    if p \<le> 65535 
    then dupe_monic_i_int (finite_field_ops32 (uint32_of_int p))
    else if p \<le> 4294967295
    then dupe_monic_i_int (finite_field_ops64 (uint64_of_int p))
    else dupe_monic_i_int (finite_field_ops_integer (integer_of_int p)))" 

context poly_mod_2
begin

lemma dupe_monic_i_int_finite_field_ops_integer: assumes 
      dupe_i: "dupe_monic_i_int (finite_field_ops_integer (integer_of_int m)) D H S T U = (A,B)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and norm: "Mp D = D" "Mp H = H" "Mp S = S" "Mp T = T" "Mp U = U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp A = A" 
  "Mp B = B" 
  using m1 mod_ring_gen.dupe_monic_i_int[OF 
        mod_ring_locale.mod_ring_finite_field_ops_integer[unfolded mod_ring_locale_def], 
        internalize_sort "'a :: nontriv", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF _ assms] by auto

lemma dupe_monic_i_int_finite_field_ops32: assumes 
      m: "m \<le> 65535"
  and dupe_i: "dupe_monic_i_int (finite_field_ops32 (uint32_of_int m)) D H S T U = (A,B)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and norm: "Mp D = D" "Mp H = H" "Mp S = S" "Mp T = T" "Mp U = U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp A = A" 
  "Mp B = B" 
  using m1 mod_ring_gen.dupe_monic_i_int[OF 
        mod_ring_locale.mod_ring_finite_field_ops32[unfolded mod_ring_locale_def], 
        internalize_sort "'a :: nontriv", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF _ assms] by auto

lemma dupe_monic_i_int_finite_field_ops64: assumes 
      m: "m \<le> 4294967295"
  and dupe_i: "dupe_monic_i_int (finite_field_ops64 (uint64_of_int m)) D H S T U = (A,B)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and norm: "Mp D = D" "Mp H = H" "Mp S = S" "Mp T = T" "Mp U = U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp A = A" 
  "Mp B = B" 
  using m1 mod_ring_gen.dupe_monic_i_int[OF 
        mod_ring_locale.mod_ring_finite_field_ops64[unfolded mod_ring_locale_def], 
        internalize_sort "'a :: nontriv", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF _ assms] by auto

lemma dupe_monic_dynamic: assumes dupe: "dupe_monic_dynamic m D H S T U = (A,B)" 
  and 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and norm: "Mp D = D" "Mp H = H" "Mp S = S" "Mp T = T" "Mp U = U" 
shows 
  "A * D + B * H =m U" 
  "B = 0 \<or> degree B < degree D" 
  "Mp A = A" 
  "Mp B = B"
  using dupe
    dupe_monic_i_int_finite_field_ops32[OF _ _ 1 mon norm, of A B]
    dupe_monic_i_int_finite_field_ops64[OF _ _ 1 mon norm, of A B]
    dupe_monic_i_int_finite_field_ops_integer[OF _ 1 mon norm, of A B]
  unfolding dupe_monic_dynamic_def by (auto split: if_splits)
end


context poly_mod
begin

definition dupe_monic_int :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> 
  int poly * int poly" where
  "dupe_monic_int D H S T U = (case pdivmod_monic (Mp (T * U)) D of (q,r) \<Rightarrow>
     (Mp (S * U + H * q), Mp r))"

end

declare poly_mod.dupe_monic_int_def[code]

text \<open>Old direct proof on int poly. 
  It does not permit to change implementation.
  This proof is still present, since we did not export the uniqueness part
  from the type-based uniqueness result @{thm dupe_monic_unique} via the various relations.\<close>

lemma (in poly_mod_2) dupe_monic_int: assumes 1: "D*S + H*T =m 1" 
  and mon: "monic D" 
  and dupe: "dupe_monic_int D H S T U = (A,B)" 
  shows "A * D + B * H =m U" "B = 0 \<or> degree B < degree D" "Mp A = A" "Mp B = B" 
    "coprime_m D H \<Longrightarrow> A' * D + B' * H =m U \<Longrightarrow> B' = 0 \<or> degree B' < degree D \<Longrightarrow> Mp D = D 
    \<Longrightarrow> Mp A' = A' \<Longrightarrow> Mp B' = B' \<Longrightarrow> prime m
    \<Longrightarrow> A' = A \<and> B' = B"
proof -
  obtain Q R where div: "pdivmod_monic (Mp (T * U)) D = (Q,R)" by force
  from dupe[unfolded dupe_monic_int_def div split]
  have A: "A = Mp (S * U + H * Q)" and B: "B = Mp R" by auto
  from pdivmod_monic[OF mon div] have TU: "Mp (T * U) = D * Q + R" and 
    deg: "R = 0 \<or> degree R < degree D" by auto
  hence "Mp R = Mp (Mp (T * U) - D * Q)" by simp
  also have "\<dots> = Mp (T * U - Mp (Mp (Mp D * Q)))" unfolding Mp_Mp unfolding minus_Mp
    using minus_Mp mult_Mp by metis
  also have "\<dots> = Mp (T * U - D * Q)" by simp
  finally have r: "Mp R = Mp (T * U - D * Q)" by simp
  have "Mp (A * D + B * H) = Mp (Mp (A * D) + Mp (B * H))" by simp
  also have "Mp (A * D) = Mp ((S * U + H * Q) * D)" unfolding A by simp
  also have "Mp (B * H) = Mp (Mp R * Mp H)" unfolding B by simp
  also have "\<dots> = Mp ((T * U - D * Q) * H)" unfolding r by simp
  also have "Mp (Mp ((S * U + H * Q) * D) + Mp ((T * U - D * Q) * H)) = 
    Mp ((S * U + H * Q) * D + (T * U - D * Q) * H)" by simp
  also have "(S * U + H * Q) * D + (T * U - D * Q) * H = (D * S + H * T) * U"
    by (simp add: field_simps)
  also have "Mp \<dots> = Mp (Mp (D * S + H * T) * U)" by simp
  also have "Mp (D * S + H * T) = 1" using 1 by simp
  finally show eq: "A * D + B * H =m U" by simp
  have id: "degree_m (Mp R) = degree_m R" by simp
  have id': "degree D = degree_m D" using mon by simp
  show degB: "B = 0 \<or> degree B < degree D" using deg unfolding B id id'
    using degree_m_le[of R] by (cases "R = 0", auto)
  show Mp: "Mp A = A" "Mp B = B" unfolding A B by auto
  assume another: "A' * D + B' * H =m U" and degB': "B' = 0 \<or> degree B' < degree D" 
    and norm: "Mp A' = A'" "Mp B' = B'" and cop: "coprime_m D H" and D: "Mp D = D" 
    and prime: "prime m"
  from degB Mp D have degB: "B =m 0 \<or> degree_m B < degree_m D" by auto
  from degB' Mp D norm have degB': "B' =m 0 \<or> degree_m B' < degree_m D" by auto
  from mon D have D0: "\<not> (D =m 0)" by auto
  from prime interpret poly_mod_prime m by unfold_locales
  from another eq have "A' * D + B' * H =m A * D + B * H" by simp
  from uniqueness_poly_equality[OF cop degB' degB D0 this]
  show "A' = A \<and> B' = B" unfolding norm Mp by auto
qed


lemma coprime_bezout_coefficients:
  assumes cop: "coprime f g"
    and ext: "bezout_coefficients f g = (a, b)" 
  shows "a * f + b * g = 1"
  using assms bezout_coefficients [of f g a b]
  by simp

lemma (in poly_mod_prime_type) bezout_coefficients_mod_int: assumes f: "(F :: 'a mod_ring poly) = of_int_poly f"
  and g: "(G :: 'a mod_ring poly) = of_int_poly g" 
  and cop: "coprime_m f g" 
  and fact: "bezout_coefficients F G = (A,B)" 
  and a: "a = to_int_poly A"
  and b: "b = to_int_poly B"
  shows "f * a + g * b =m 1"
proof -
  have f[transfer_rule]: "MP_Rel f F" unfolding f MP_Rel_def by (simp add: Mp_f_representative)
  have g[transfer_rule]: "MP_Rel g G" unfolding g MP_Rel_def by (simp add: Mp_f_representative)
  have [transfer_rule]: "MP_Rel a A" unfolding a MP_Rel_def by (rule Mp_to_int_poly)
  have [transfer_rule]: "MP_Rel b B" unfolding b MP_Rel_def by (rule Mp_to_int_poly)
  from cop have "coprime F G" using coprime_MP_Rel[unfolded rel_fun_def] f g by auto
  from coprime_bezout_coefficients [OF this fact]
  have "A * F + B * G = 1" .
  from this [untransferred]
  show ?thesis by (simp add: ac_simps)
qed
  
definition bezout_coefficients_i :: "'i arith_ops_record \<Rightarrow> 'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<times> 'i list" where
  "bezout_coefficients_i ff_ops f g = fst (euclid_ext_poly_i ff_ops f g)"

definition euclid_ext_poly_mod_main :: "int \<Rightarrow> 'a arith_ops_record \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "euclid_ext_poly_mod_main p ff_ops f g = (case bezout_coefficients_i ff_ops (of_int_poly_i ff_ops f) (of_int_poly_i ff_ops g) of 
      (a,b) \<Rightarrow> (to_int_poly_i ff_ops a, to_int_poly_i ff_ops b))" 

definition euclid_ext_poly_dynamic :: "int \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "euclid_ext_poly_dynamic p = ( 
    if p \<le> 65535 
    then euclid_ext_poly_mod_main p (finite_field_ops32 (uint32_of_int p))
    else if p \<le> 4294967295
    then euclid_ext_poly_mod_main p (finite_field_ops64 (uint64_of_int p))
    else euclid_ext_poly_mod_main p (finite_field_ops_integer (integer_of_int p)))" 
  
context prime_field_gen
begin
lemma bezout_coefficients_i[transfer_rule]: 
  "(poly_rel ===> poly_rel ===> rel_prod poly_rel poly_rel)
     (bezout_coefficients_i ff_ops) bezout_coefficients"
  unfolding bezout_coefficients_i_def bezout_coefficients_def
  by transfer_prover

lemma bezout_coefficients_i_sound: assumes f: "f' = of_int_poly_i ff_ops f" "Mp f = f"
  and g: "g' = of_int_poly_i ff_ops g" "Mp g = g"  
  and cop: "coprime_m f g" 
  and res: "bezout_coefficients_i ff_ops f' g' = (a',b')" 
  and a: "a = to_int_poly_i ff_ops a'"
  and b: "b = to_int_poly_i ff_ops b'"
shows "f * a + g * b =m 1"
  "Mp a = a" "Mp b = b" 
proof -
  from f have f': "f' = of_int_poly_i ff_ops (Mp f)" by simp
  define f'' where "f'' \<equiv> of_int_poly (Mp f) :: 'a mod_ring poly"
  have f'': "f'' = of_int_poly f" unfolding f''_def f by simp
  have rel_f[transfer_rule]: "poly_rel f' f''" 
    by (rule poly_rel_of_int_poly[OF f'], simp add: f'' f)
  from g have g': "g' = of_int_poly_i ff_ops (Mp g)" by simp
  define g'' where "g'' \<equiv> of_int_poly (Mp g) :: 'a mod_ring poly"
  have g'': "g'' = of_int_poly g" unfolding g''_def g by simp
  have rel_g[transfer_rule]: "poly_rel g' g''"     
    by (rule poly_rel_of_int_poly[OF g'], simp add: g'' g)
  obtain a'' b'' where eucl: "bezout_coefficients f'' g'' = (a'',b'')" by force
  from bezout_coefficients_i[unfolded rel_fun_def rel_prod_conv, rule_format, OF rel_f rel_g,
    unfolded res split eucl]
  have rel[transfer_rule]: "poly_rel a' a''" "poly_rel b' b''" by auto
  with to_int_poly_i have a: "a = to_int_poly a''" 
    and b: "b = to_int_poly b''" unfolding a b by auto
  from bezout_coefficients_mod_int [OF f'' g'' cop eucl a b]
  show "f * a + g * b =m 1" .
  show "Mp a = a" "Mp b = b" unfolding a b by (auto simp: Mp_to_int_poly)
qed

lemma euclid_ext_poly_mod_main: assumes cop: "coprime_m f g" 
  and f: "Mp f = f" and g: "Mp g = g" 
  and res: "euclid_ext_poly_mod_main m ff_ops f g = (a,b)" 
shows "f * a + g * b =m 1" 
  "Mp a = a" "Mp b = b" 
proof -
  obtain a' b' where res': "bezout_coefficients_i ff_ops (of_int_poly_i ff_ops f) 
    (of_int_poly_i ff_ops g) = (a', b')" by force
  show "f * a + g * b =m 1" 
  "Mp a = a" "Mp b = b"
    by (insert bezout_coefficients_i_sound[OF refl f refl g cop res']
    res [unfolded euclid_ext_poly_mod_main_def res'], auto)
qed

end

context poly_mod_prime begin

lemmas euclid_ext_poly_mod_integer = prime_field_gen.euclid_ext_poly_mod_main
  [OF prime_field.prime_field_finite_field_ops_integer,
  unfolded prime_field_def mod_ring_locale_def poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas euclid_ext_poly_mod_uint32 = prime_field_gen.euclid_ext_poly_mod_main
  [OF prime_field.prime_field_finite_field_ops32,
  unfolded prime_field_def mod_ring_locale_def poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas euclid_ext_poly_mod_uint64 = prime_field_gen.euclid_ext_poly_mod_main[OF prime_field.prime_field_finite_field_ops64,
  unfolded prime_field_def mod_ring_locale_def poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemma euclid_ext_poly_dynamic:
  assumes cop: "coprime_m f g" and f: "Mp f = f" and g: "Mp g = g"
    and res: "euclid_ext_poly_dynamic p f g = (a,b)" 
  shows "f * a + g * b =m 1" 
    "Mp a = a" "Mp b = b"
  using euclid_ext_poly_mod_integer[OF cop f g, of p a b]
    euclid_ext_poly_mod_uint32[OF _ cop f g, of p a b]
    euclid_ext_poly_mod_uint64[OF _ cop f g, of p a b]
    res[unfolded euclid_ext_poly_dynamic_def] by (auto split: if_splits)

end

lemma range_sum_prod: assumes xy: "x \<in> {0..<q}" "(y :: int) \<in> {0..<p}" 
  shows "x + q * y \<in> {0..<p * q}"
proof -
  {
    fix x q :: int
    have "x \<in> {0 ..< q} \<longleftrightarrow> 0 \<le> x \<and> x < q" by auto
  } note id = this
  from xy have 0: "0 \<le> x + q * y" by auto
  have "x + q * y \<le> q - 1 + q * y" using xy by simp
  also have "q * y \<le> q * (p - 1)" using xy by auto
  finally have "x + q * y \<le> q - 1 + q * (p - 1)" by auto
  also have "\<dots> = p * q - 1" by (simp add: field_simps)
  finally show ?thesis using 0 by auto
qed

context 
  fixes C :: "int poly" 
begin

context
  fixes p :: int and S T D1 H1 :: "int poly" 
begin
(* The linear lifting is implemented for ease of provability.
   Aim: show uniqueness of factorization *)
fun linear_hensel_main where 
  "linear_hensel_main (Suc 0) = (D1,H1)" 
| "linear_hensel_main (Suc n) = (
      let (D,H) = linear_hensel_main n;
        q = p ^ n;
        U = poly_mod.Mp p (sdiv_poly (C - D * H) q);   \<comment> \<open>\<open>H2 + H3\<close>\<close>
        (A,B) = poly_mod.dupe_monic_int p D1 H1 S T U
      in (D + smult q B, H + smult q A)) \<comment> \<open>\<open>H4\<close>\<close>"
    | "linear_hensel_main 0 = (D1,H1)" 

lemma linear_hensel_main: assumes 1: "poly_mod.eq_m p (D1 * S + H1 * T) 1" 
  and equiv: "poly_mod.eq_m p (D1 * H1) C"
  and monD1: "monic D1" 
  and normDH1: "poly_mod.Mp p D1 = D1" "poly_mod.Mp p H1 = H1"
  and res: "linear_hensel_main n = (D,H)" 
  and n: "n \<noteq> 0" 
  and prime: "prime p" \<comment> \<open>\<open>p > 1\<close> suffices if one does not need uniqueness\<close>
  and cop: "poly_mod.coprime_m p D1 H1"
  shows "poly_mod.eq_m (p^n) (D * H) C
    \<and> monic D
    \<and> poly_mod.eq_m p D D1 \<and> poly_mod.eq_m p H H1
    \<and> poly_mod.Mp (p^n) D = D
    \<and> poly_mod.Mp (p^n) H = H \<and> 
    (poly_mod.eq_m (p^n) (D' * H') C \<longrightarrow>
     poly_mod.eq_m p D' D1 \<longrightarrow> 
     poly_mod.eq_m p H' H1 \<longrightarrow>
     poly_mod.Mp (p^n) D' = D' \<longrightarrow>
     poly_mod.Mp (p^n) H' = H' \<longrightarrow> monic D' \<longrightarrow> D' = D \<and> H' = H)
     " 
  using res n 
proof (induct n arbitrary: D H D' H')
  case (Suc n D' H' D'' H'')
  show ?case
  proof (cases "n = 0")
    case True
    with Suc equiv monD1 normDH1 show ?thesis by auto
  next
    case False
    hence n: "n \<noteq> 0" by auto
    let ?q = "p^n"
    let ?pq = "p * p^n"
    from prime have p: "p > 1" using prime_gt_1_int by force
    from n p have q: "?q > 1" by auto
    from n p have pq: "?pq > 1" by (metis power_gt1_lemma)
    interpret p: poly_mod_2 p using p unfolding poly_mod_2_def .
    interpret q: poly_mod_2 ?q using q unfolding poly_mod_2_def .
    interpret pq: poly_mod_2 ?pq using pq unfolding poly_mod_2_def .
    obtain D H where rec: "linear_hensel_main n = (D,H)" by force
    obtain V where V: "sdiv_poly (C - D * H) ?q = V" by force
    obtain U where U: "p.Mp (sdiv_poly (C - D * H) ?q) = U" by auto
    obtain A B where dupe: "p.dupe_monic_int D1 H1 S T U = (A,B)" by force
    note IH = Suc(1)[OF rec n]
    from IH
    have CDH: "q.eq_m (D * H) C"
      and monD: "monic D"
      and p_eq: "p.eq_m D D1" "p.eq_m H H1"
      and norm: "q.Mp D = D" "q.Mp H = H" by auto
    from n obtain k where n: "n = Suc k" by (cases n, auto)
    have qq: "?q * ?q = ?pq * p^k" unfolding n by simp
    from Suc(2)[unfolded n linear_hensel_main.simps, folded n, unfolded rec split Let_def U dupe]
    have D': "D' = D + smult ?q B" and H': "H' = H + smult ?q A" by auto
    note dupe = p.dupe_monic_int[OF 1 monD1 dupe]
    from CDH have "q.Mp C - q.Mp (D * H) = 0" by simp
    hence "q.Mp (q.Mp C - q.Mp (D * H)) = 0" by simp
    hence "q.Mp (C - D*H) = 0" by simp
    from q.Mp_0_smult_sdiv_poly[OF this] have CDHq: "smult ?q (sdiv_poly (C - D * H) ?q) = C - D * H" .
    have ADBHU: "p.eq_m (A * D + B * H) U" using p_eq dupe(1) 
      by (metis (mono_tags, lifting) p.mult_Mp(2) poly_mod.plus_Mp)
    have "pq.Mp (D' * H') = pq.Mp ((D + smult ?q B) * (H + smult ?q A))" 
      unfolding D' H' by simp
    also have "(D + smult ?q B) * (H + smult ?q A) = (D * H + smult ?q (A * D + B * H)) + smult (?q * ?q) (A * B)" 
      by (simp add: field_simps smult_distribs)
    also have "pq.Mp \<dots> = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)) + pq.Mp (smult (?q * ?q) (A * B)))"
      using pq.plus_Mp by metis
    also have "pq.Mp (smult (?q * ?q) (A * B)) = 0" unfolding qq
      by (metis pq.Mp_smult_m_0 smult_smult)
    finally have DH': "pq.Mp (D' * H') = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)))" by simp
    also have "pq.Mp (smult ?q (A * D + B * H)) = pq.Mp (smult ?q U)"
      using p.Mp_lift_modulus[OF ADBHU, of ?q] by simp
    also have "\<dots> = pq.Mp (C - D * H)" 
      unfolding arg_cong[OF CDHq, of pq.Mp, symmetric] U[symmetric] V
      by (rule p.Mp_lift_modulus[of _ _ ?q], auto) 
    also have "pq.Mp (D * H + pq.Mp (C - D * H)) = pq.Mp C" by simp
    finally have CDH: "pq.eq_m C (D' * H')" by simp

    have deg: "degree D1 = degree D" using p_eq(1) monD1 monD
      by (metis p.monic_degree_m)
    have mon: "monic D'" unfolding D' using dupe(2) monD unfolding deg by (rule monic_smult_add_small)
    have normD': "pq.Mp D' = D'" 
      unfolding D' pq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq coeff_smult 
    proof 
      fix i
      from norm(1) dupe(4) have "coeff D i \<in> {0..<?q}" "coeff B i \<in> {0..<p}" 
        unfolding p.Mp_ident_iff q.Mp_ident_iff by auto
      thus "coeff D i + ?q * coeff B i \<in> {0..< ?pq}" by (rule range_sum_prod)
    qed
    have normH': "pq.Mp H' = H'" 
      unfolding H' pq.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq coeff_smult 
    proof 
      fix i
      from norm(2) dupe(3) have "coeff H i \<in> {0..<?q}" "coeff A i \<in> {0..<p}" 
        unfolding p.Mp_ident_iff q.Mp_ident_iff by auto
      thus "coeff H i + ?q * coeff A i \<in> {0..< ?pq}" by (rule range_sum_prod)
    qed
    have eq: "p.eq_m D D'" "p.eq_m H H'" unfolding D' H' n 
        poly_eq_iff p.Mp_coeff p.M_def by (auto simp: field_simps)
    with p_eq have eq: "p.eq_m D' D1" "p.eq_m H' H1" by auto
    {
      assume CDH'': "pq.eq_m C (D'' * H'')" 
        and DH1'': "p.eq_m D1 D''" "p.eq_m H1 H''"
        and norm'': "pq.Mp D'' = D''" "pq.Mp H'' = H''" 
        and monD'': "monic D''" 
      from q.Dp_Mp_eq[of D''] obtain d B' where D'': "D'' = q.Mp d + smult ?q B'" by auto
      from q.Dp_Mp_eq[of H''] obtain h A' where H'': "H'' = q.Mp h + smult ?q A'" by auto
      {
        fix A B
        assume *: "pq.Mp (q.Mp A + smult ?q B) = q.Mp A + smult ?q B" 
        have "p.Mp B = B" unfolding p.Mp_ident_iff
        proof 
          fix i
          from arg_cong[OF *, of "\<lambda> f. coeff f i", unfolded pq.Mp_coeff pq.M_def]
          have "coeff (q.Mp A + smult ?q B) i \<in> {0 ..< ?pq}" using "*" pq.Mp_ident_iff by blast 
          hence sum: "coeff (q.Mp A) i + ?q * coeff B i \<in> {0 ..< ?pq}" by auto
          have "q.Mp (q.Mp A) = q.Mp A" by auto
          from this[unfolded q.Mp_ident_iff] have A: "coeff (q.Mp A) i \<in> {0 ..< p^n}" by auto
          {
            assume "coeff B i < 0" hence "coeff B i \<le> -1" by auto
            from mult_left_mono[OF this, of ?q] q.m1 have "?q * coeff B i \<le> -?q" by simp
            with A sum have False by auto
          } hence "coeff B i \<ge> 0" by force
          moreover
          {
            assume "coeff B i \<ge> p" 
            from mult_left_mono[OF this, of ?q] q.m1 have "?q * coeff B i \<ge> ?pq" by simp
            with A sum have False by auto
          } hence "coeff B i < p" by force
          ultimately show "coeff B i \<in> {0 ..< p}" by auto
        qed
      } note norm_convert = this
      from norm_convert[OF norm''(1)[unfolded D'']] have normB': "p.Mp B' = B'" . 
      from norm_convert[OF norm''(2)[unfolded H'']] have normA': "p.Mp A' = A'" . 
      let ?d = "q.Mp d" 
      let ?h = "q.Mp h"
      {
        assume lt: "degree ?d < degree B'"
        hence eq: "degree D'' = degree B'" unfolding D'' using q.m1 p.m1
          by (subst degree_add_eq_right, auto)
        from lt have [simp]: "coeff ?d (degree B') = 0" by (rule coeff_eq_0)
        from monD''[unfolded eq, unfolded D'', simplified] False q.m1 lt have False
          by (metis mod_mult_self1_is_0 poly_mod.M_def q.M_1 zero_neq_one)
      }
      hence deg_dB': "degree ?d \<ge> degree B'" by presburger
      {
        assume eq: "degree ?d = degree B'" and B': "B' \<noteq> 0"  
        let ?B = "coeff B' (degree B')" 
        from normB'[unfolded p.Mp_ident_iff, rule_format, of "degree B'"] B'
        have "?B \<in> {0..<p} - {0}" by simp
        hence bnds: "?B > 0" "?B < p" by auto
        have degD'': "degree D'' \<le> degree ?d" unfolding D'' using eq by (simp add: degree_add_le)
        have "?q * ?B \<ge> 1 * 1" by (rule mult_mono, insert q.m1 bnds, auto) 
        moreover have "coeff D'' (degree ?d) = 1 + ?q * ?B" using monD''
          unfolding D'' using eq 
          by (metis D'' coeff_smult monD'' plus_poly.rep_eq poly_mod.Dp_Mp_eq 
              poly_mod.degree_m_eq_monic poly_mod.plus_Mp(1) 
              q.Mp_smult_m_0 q.m1 q.monic_Mp q.plus_Mp(2))
        ultimately have gt: "coeff D'' (degree ?d) > 1" by auto
        hence "coeff D'' (degree ?d) \<noteq> 0" by auto
        hence "degree D'' \<ge> degree ?d" by (rule le_degree)
        with degree_add_le_max[of ?d "smult ?q B'", folded D''] eq 
        have deg: "degree D'' = degree ?d" using degD'' by linarith
        from gt[folded this] have "\<not> monic D''" by auto
        with monD'' have False by auto
      }
      with deg_dB' have deg_dB2: "B' = 0 \<or> degree B' < degree ?d" by fastforce
      have d: "q.Mp D'' = ?d" unfolding D''
        by (metis add.right_neutral poly_mod.Mp_smult_m_0 poly_mod.plus_Mp)
      have h: "q.Mp H'' = ?h" unfolding H''
        by (metis add.right_neutral poly_mod.Mp_smult_m_0 poly_mod.plus_Mp)
      from CDH'' have "pq.Mp C = pq.Mp (D'' * H'')" by simp
      from arg_cong[OF this, of q.Mp] 
      have "q.Mp C = q.Mp (D'' * H'')"
        using p.m1 q.Mp_product_modulus by auto
      also have "\<dots> = q.Mp (q.Mp D'' * q.Mp H'')" by simp
      also have "\<dots> = q.Mp (?d * ?h)" unfolding d h by simp
      finally have eqC: "q.eq_m (?d * ?h) C" by auto
      have d1: "p.eq_m ?d D1" unfolding d[symmetric] using DH1''
        using assms(4) n p.Mp_product_modulus p.m1 by auto
      have h1: "p.eq_m ?h H1" unfolding h[symmetric] using DH1''
        using assms(5) n p.Mp_product_modulus p.m1 by auto
      have mond: "monic (q.Mp d)" using monD'' deg_dB2 unfolding D''
        using d q.monic_Mp[OF monD''] by simp
      from eqC d1 h1 mond IH[of "q.Mp d" "q.Mp h"] have IH: "?d = D" "?h = H" by auto
      from deg_dB2[unfolded IH] have degB': "B' = 0 \<or> degree B' < degree D" by auto
      from IH have D'': "D'' = D + smult ?q B'" and H'': "H'' = H + smult ?q A'" 
        unfolding D'' H'' by auto
      have "pq.Mp (D'' * H'') = pq.Mp (D' * H')" using CDH'' CDH  by simp
      also have "pq.Mp (D'' * H'') = pq.Mp ((D + smult ?q B') * (H + smult ?q A'))" 
        unfolding D'' H'' by simp
      also have "(D + smult ?q B') * (H + smult ?q A') = (D * H + smult ?q (A' * D + B' * H)) + smult (?q * ?q) (A' * B')" 
        by (simp add: field_simps smult_distribs)
      also have "pq.Mp \<dots> = pq.Mp (D * H + pq.Mp (smult ?q (A' * D + B' * H)) + pq.Mp (smult (?q * ?q) (A' * B')))"
        using pq.plus_Mp by metis
      also have "pq.Mp (smult (?q * ?q) (A' * B')) = 0" unfolding qq
        by (metis pq.Mp_smult_m_0 smult_smult)
      finally have "pq.Mp (D * H + pq.Mp (smult ?q (A' * D + B' * H))) 
        = pq.Mp (D * H + pq.Mp (smult ?q (A * D + B * H)))" unfolding DH' by simp
      hence "pq.Mp (smult ?q (A' * D + B' * H)) = pq.Mp (smult ?q (A * D + B * H))"
        by (metis (no_types, lifting) add_diff_cancel_left' poly_mod.minus_Mp(1) poly_mod.plus_Mp(2))
      hence "p.Mp (A' * D + B' * H) = p.Mp (A * D + B * H)" unfolding poly_eq_iff p.Mp_coeff pq.Mp_coeff coeff_smult
        by (insert p, auto simp: p.M_def pq.M_def)
      hence "p.Mp (A' * D1 + B' * H1) = p.Mp (A * D1 + B * H1)" using p_eq
        by (metis p.mult_Mp(2) poly_mod.plus_Mp)
      hence eq: "p.eq_m (A' * D1 + B' * H1) U" using dupe(1) by auto
      have "degree D = degree D1" using monD monD1 
          arg_cong[OF p_eq(1), of degree] 
          p.degree_m_eq_monic[OF _ p.m1] by auto
      hence "B' = 0 \<or> degree B' < degree D1" using degB' by simp
      from dupe(5)[OF cop eq this normDH1(1) normA' normB' prime] have "A' = A" "B' = B" by auto
      hence "D'' = D'" "H'' = H'" unfolding D'' H'' D' H' by auto
    }
    thus ?thesis using normD' normH' CDH mon eq by simp
  qed
qed simp
end
end

definition linear_hensel_binary :: "int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "linear_hensel_binary p n C D H = (let
     (S,T) = euclid_ext_poly_dynamic p D H
     in linear_hensel_main C p S T D H n)"

lemma (in poly_mod_prime) unique_hensel_binary: 
  assumes prime: "prime p"
  and cop: "coprime_m D H" and eq: "eq_m (D * H) C"
  and normalized_input: "Mp D = D" "Mp H = H"
  and monic_input: "monic D" 
  and n: "n \<noteq> 0" 
shows "\<exists>! (D',H'). \<comment> \<open>\<open>D'\<close>, \<open>H'\<close> are computed via \<open>linear_hensel_binary\<close>\<close>
      poly_mod.eq_m (p^n) (D' * H') C \<comment> \<open>the main result: equivalence mod \<open>p^n\<close>\<close>
    \<and> monic D' \<comment> \<open>monic output\<close>
    \<and> eq_m D D' \<and> eq_m H H' \<comment> \<open>apply \<open>`mod p`\<close> on \<open>D'\<close> and \<open>H'\<close> yields \<open>D\<close> and \<open>H\<close> again\<close>
    \<and> poly_mod.Mp (p^n) D' = D' \<and> poly_mod.Mp (p^n) H' = H' \<comment> \<open>output is normalized\<close>"
proof -
  obtain D' H' where hensel_result: "linear_hensel_binary p n C D H = (D',H')" by force
  from m1 have p: "p > 1" .
  obtain S T where ext: "euclid_ext_poly_dynamic p D H = (S,T)" by force
  obtain D1 H1 where main: "linear_hensel_main C p S T D H n = (D1,H1)" by force
  from hensel_result[unfolded linear_hensel_binary_def ext split Let_def main]
  have id: "D1 = D'" "H1 = H'" by auto
  note eucl = euclid_ext_poly_dynamic [OF cop normalized_input ext]
  from linear_hensel_main [OF eucl(1)
    eq monic_input normalized_input main [unfolded id] n prime cop]
  show ?thesis by (intro ex1I, auto)
qed

(* The quadratic lifting is implemented more efficienty.
   Aim: compute factorization *)
context
  fixes C :: "int poly"
begin

lemma hensel_step_main: assumes 
      one_q: "poly_mod.eq_m q (D * S + H * T) 1"
  and one_p: "poly_mod.eq_m p (D1 * S1 + H1 * T1) 1"
  and CDHq: "poly_mod.eq_m q C (D * H)"
  and D1D: "poly_mod.eq_m p D1 D" 
  and H1H: "poly_mod.eq_m p H1 H" 
  and S1S: "poly_mod.eq_m p S1 S" 
  and T1T: "poly_mod.eq_m p T1 T" 
  and mon: "monic D" 
  and mon1: "monic D1" 
  and q: "q > 1" 
  and p: "p > 1" 
  and D1: "poly_mod.Mp p D1 = D1" 
  and H1: "poly_mod.Mp p H1 = H1"
  and S1: "poly_mod.Mp p S1 = S1" 
  and T1: "poly_mod.Mp p T1 = T1"
  and D: "poly_mod.Mp q D = D" 
  and H: "poly_mod.Mp q H = H"
  and S: "poly_mod.Mp q S = S" 
  and T: "poly_mod.Mp q T = T"
  and U1: "U1 = poly_mod.Mp p (sdiv_poly (C - D * H) q)"
  and dupe1: "dupe_monic_dynamic p D1 H1 S1 T1 U1 = (A,B)" 
  and D': "D' = D + smult q B"
  and H': "H' = H + smult q A" 
  and U2: "U2 = poly_mod.Mp q (sdiv_poly (S*D' + T*H' - 1) p)" 
  and dupe2: "dupe_monic_dynamic q D H S T U2 = (A',B')" 
  and rq: "r = p * q" 
  and pq: "p dvd q"  
  and S': "S' = poly_mod.Mp r (S - smult p A')"
  and T': "T' = poly_mod.Mp r (T - smult p B')" 
shows "poly_mod.eq_m r C (D' * H')" 
  "poly_mod.Mp r D' = D'" 
  "poly_mod.Mp r H' = H'" 
  "poly_mod.Mp r S' = S'" 
  "poly_mod.Mp r T' = T'" 
  "poly_mod.eq_m r (D' * S' + H' * T') 1" 
  "monic D'" 
  unfolding rq
proof -
  from pq obtain k where qp: "q = p * k" unfolding dvd_def by auto
  from arg_cong[OF qp, of sgn] q p have k0: "k > 0" unfolding sgn_mult by (auto simp: sgn_1_pos)
  from qp have qq: "q * q = p * q * k" by auto
  let ?r = "p * q" 
  interpret poly_mod_2 p by (standard, insert p, auto)
  interpret q: poly_mod_2 q by (standard, insert q, auto)
  from p q have r: "?r > 1" by (simp add: less_1_mult)
  interpret r: poly_mod_2 ?r using r unfolding poly_mod_2_def .  
  have Mp_conv: "Mp (q.Mp x) = Mp x" for x unfolding qp
    by (rule Mp_product_modulus[OF refl k0])
  from arg_cong[OF CDHq, of Mp, unfolded Mp_conv] have "Mp C = Mp (Mp D * Mp H)"
    by simp
  also have "Mp D = Mp D1" using D1D by simp
  also have "Mp H = Mp H1" using H1H by simp
  finally have CDHp: "eq_m C (D1 * H1)" by simp
  have "Mp U1 = U1" unfolding U1 by simp
  note dupe1 = dupe_monic_dynamic[OF dupe1 one_p mon1 D1 H1 S1 T1 this]
  have "q.Mp U2 = U2" unfolding U2 by simp
  note dupe2 = q.dupe_monic_dynamic[OF dupe2 one_q mon D H S T this]
  from CDHq have "q.Mp C - q.Mp (D * H) = 0" by simp
  hence "q.Mp (q.Mp C - q.Mp (D * H)) = 0" by simp
  hence "q.Mp (C - D*H) = 0" by simp
  from q.Mp_0_smult_sdiv_poly[OF this] have CDHq: "smult q (sdiv_poly (C - D * H) q) = C - D * H" .
  {
    fix A B
    have "Mp (A * D1 + B * H1) = Mp (Mp (A * D1) + Mp (B * H1))" by simp
    also have "Mp (A * D1) = Mp (A * Mp D1)" by simp
    also have "\<dots> = Mp (A * D)" unfolding D1D by simp
    also have "Mp (B * H1) = Mp (B * Mp H1)" by simp
    also have "\<dots> = Mp (B * H)" unfolding H1H by simp
    finally have "Mp (A * D1 + B * H1) = Mp (A * D + B * H)" by simp
  } note D1H1 = this
  have "r.Mp (D' * H') = r.Mp ((D + smult q B) * (H + smult q A))" 
    unfolding D' H' by simp
  also have "(D + smult q B) * (H + smult q A) = (D * H + smult q (A * D + B * H)) + smult (q * q) (A * B)" 
    by (simp add: field_simps smult_distribs)
  also have "r.Mp \<dots> = r.Mp (D * H + r.Mp (smult q (A * D + B * H)) + r.Mp (smult (q * q) (A * B)))"
    using r.plus_Mp by metis
  also have "r.Mp (smult (q * q) (A * B)) = 0" unfolding qq
    by (metis r.Mp_smult_m_0 smult_smult)
  also have "r.Mp (smult q (A * D + B * H)) = r.Mp (smult q U1)" 
  proof (rule Mp_lift_modulus[of _ _ q])
    show "Mp (A * D + B * H) = Mp U1" using dupe1(1) unfolding D1H1 by simp
  qed
  also have "\<dots> = r.Mp (C - D * H)" 
    unfolding arg_cong[OF CDHq, of r.Mp, symmetric]
    using Mp_lift_modulus[of U1 "sdiv_poly (C - D * H) q" q] unfolding U1 
    by simp
  also have "r.Mp (D * H + r.Mp (C - D * H) + 0) = r.Mp C" by simp
  finally show CDH: "r.eq_m C (D' * H')" by simp
  have "degree D1 = degree (Mp D1)" using mon1 by simp
  also have "\<dots> = degree D" unfolding D1D using mon by simp
  finally have deg_eq: "degree D1 = degree D" by simp
  show mon: "monic D'" unfolding D' using dupe1(2) mon unfolding deg_eq by (rule monic_smult_add_small)
  have "Mp (S * D' + T * H' - 1) = Mp (Mp (D * S + H * T) + (smult q (S * B + T * A) - 1))" 
    unfolding D' H' plus_Mp by (simp add: field_simps smult_distribs)
  also have "Mp (D * S + H * T) = Mp (Mp (D1 * Mp S) + Mp (H1 * Mp T))" using  D1H1[of S T] by (simp add: ac_simps)
  also have "\<dots> = 1" using one_p unfolding S1S[symmetric] T1T[symmetric] by simp
  also have "Mp (1 + (smult q (S * B + T * A) - 1)) = Mp (smult q (S * B + T * A))" by simp
  also have "\<dots> = 0" unfolding qp by (metis Mp_smult_m_0 smult_smult)
  finally have "Mp (S * D' + T * H' - 1) = 0" .
  from Mp_0_smult_sdiv_poly[OF this] 
  have SDTH: "smult p (sdiv_poly (S * D' + T * H' - 1) p) = S * D' + T * H' - 1" .
  have swap: "q * p = p * q" by simp
  have "r.Mp (D' * S' + H' * T') = 
    r.Mp ((D + smult q B) * (S - smult p A') + (H + smult q A) * (T - smult p B'))"
    unfolding D' S' H' T' rq using r.plus_Mp r.mult_Mp by metis
  also have "\<dots> = r.Mp ((D * S + H * T +
    smult q (B * S + A * T)) - smult p (A' * D + B' * H) - smult ?r (A * B' + B * A'))" 
    by (simp add: field_simps smult_distribs)
  also have "\<dots> = r.Mp ((D * S + H * T +
    smult q (B * S + A * T)) - r.Mp (smult p (A' * D + B' * H)) - r.Mp (smult ?r (A * B' + B * A')))"
    using r.plus_Mp r.minus_Mp by metis
  also have "r.Mp (smult ?r (A * B' + B * A')) = 0" by simp
  also have "r.Mp (smult p (A' * D + B' * H)) = r.Mp (smult p U2)" 
    using q.Mp_lift_modulus[OF dupe2(1), of p] unfolding swap .
  also have "\<dots> = r.Mp (S * D' + T * H' - 1)" 
    unfolding arg_cong[OF SDTH, of r.Mp, symmetric] 
    using q.Mp_lift_modulus[of U2 "sdiv_poly (S * D' + T * H' - 1) p" p] 
    unfolding U2 swap by simp
  also have "S * D' + T * H' - 1 = S * D + T * H + smult q (B * S + A * T) - 1" 
    unfolding D' H' by (simp add: field_simps smult_distribs)
  also have "r.Mp (D * S + H * T + smult q (B * S + A * T) -
     r.Mp (S * D + T * H + smult q (B * S + A * T) - 1) - 0) 
       = 1" by simp
  finally show 1: "r.eq_m (D' * S' + H' * T') 1" by simp
  show D': "r.Mp D' = D'" unfolding D' r.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq
    coeff_smult 
  proof 
    fix n
    from D dupe1(4) have "coeff D n \<in> {0..<q}" "coeff B n \<in> {0..<p}" 
      unfolding q.Mp_ident_iff Mp_ident_iff by auto
    thus "coeff D n + q * coeff B n \<in> {0..<?r}" by (metis range_sum_prod)
  qed
  show H': "r.Mp H' = H'" unfolding H' r.Mp_ident_iff poly_mod.Mp_coeff plus_poly.rep_eq
    coeff_smult 
  proof 
    fix n
    from H dupe1(3) have "coeff H n \<in> {0..<q}" "coeff A n \<in> {0..<p}" 
      unfolding q.Mp_ident_iff Mp_ident_iff by auto
    thus "coeff H n + q * coeff A n \<in> {0..<?r}" by (metis range_sum_prod)
  qed
  show "poly_mod.Mp ?r S' = S'" "poly_mod.Mp ?r T' = T'" 
    unfolding S' T' rq by auto
qed

definition hensel_step where 
  "hensel_step p q S1 T1 D1 H1 S T D H = (
      let U = poly_mod.Mp p (sdiv_poly (C - D * H) q); \<comment> \<open>\<open>Z2 and Z3\<close>\<close>        
        (A,B) = dupe_monic_dynamic p D1 H1 S1 T1 U;
        D' = D + smult q B; \<comment> \<open>\<open>Z4\<close>\<close>
        H' = H + smult q A;
        U' = poly_mod.Mp q (sdiv_poly (S*D' + T*H' - 1) p); \<comment> \<open>\<open>Z5 + Z6\<close>\<close>
        (A',B') = dupe_monic_dynamic q D H S T U';
        q' = p * q;
        S' = poly_mod.Mp q' (S - smult p A'); \<comment> \<open>\<open>Z7\<close>\<close>
        T' = poly_mod.Mp q' (T - smult p B')
     in (S',T',D',H'))" 

definition "quadratic_hensel_step q S T D H = hensel_step q q S T D H S T D H" 

lemma quadratic_hensel_step_code[code]:
  "quadratic_hensel_step q S T D H =
    (let dupe = dupe_monic_dynamic q D H S T; \<comment> \<open>this will share the conversions of \<open>D H S T\<close>\<close>
         U = poly_mod.Mp q (sdiv_poly (C - D * H) q); 
         (A, B) = dupe U; 
         D' = D + Polynomial.smult q B;
         H' = H + Polynomial.smult q A; 
         U' = poly_mod.Mp q (sdiv_poly (S * D' + T * H' - 1) q); 
         (A', B') = dupe U';
         q' = q * q; 
         S' = poly_mod.Mp q' (S - Polynomial.smult q A'); 
         T' = poly_mod.Mp q' (T - Polynomial.smult q B')
           in (S', T', D', H'))" 
  unfolding quadratic_hensel_step_def[unfolded hensel_step_def] Let_def ..

definition simple_quadratic_hensel_step where \<comment> \<open>do not compute new values \<open>S'\<close> and \<open>T'\<close>\<close>
  "simple_quadratic_hensel_step q S T D H = (
      let U = poly_mod.Mp q (sdiv_poly (C - D * H) q); \<comment> \<open>\<open>Z2 + Z3\<close>\<close>
        (A,B) = dupe_monic_dynamic q D H S T U;
        D' = D + smult q B; \<comment> \<open>\<open>Z4\<close>\<close>
        H' = H + smult q A
     in (D',H'))" 

lemma hensel_step: assumes step: "hensel_step p q S1 T1 D1 H1 S T D H = (S', T', D', H')"
  and one_p: "poly_mod.eq_m p (D1 * S1 + H1 * T1) 1"
  and mon1: "monic D1" 
  and p: "p > 1" 
  and CDHq: "poly_mod.eq_m q C (D * H)"
  and one_q: "poly_mod.eq_m q (D * S + H * T) 1"
  and D1D: "poly_mod.eq_m p D1 D"
  and H1H: "poly_mod.eq_m p H1 H"
  and S1S: "poly_mod.eq_m p S1 S"
  and T1T: "poly_mod.eq_m p T1 T"
  and mon: "monic D" 
  and q: "q > 1" 
  and D1: "poly_mod.Mp p D1 = D1" 
  and H1: "poly_mod.Mp p H1 = H1"
  and S1: "poly_mod.Mp p S1 = S1" 
  and T1: "poly_mod.Mp p T1 = T1"
  and D: "poly_mod.Mp q D = D" 
  and H: "poly_mod.Mp q H = H"
  and S: "poly_mod.Mp q S = S" 
  and T: "poly_mod.Mp q T = T"
  and rq: "r = p * q" 
  and pq: "p dvd q"  
shows 
  "poly_mod.eq_m r C (D' * H')" 
  "poly_mod.eq_m r (D' * S' + H' * T') 1"
  "poly_mod.Mp r D' = D'" 
  "poly_mod.Mp r H' = H'" 
  "poly_mod.Mp r S' = S'" 
  "poly_mod.Mp r T' = T'" 
  "poly_mod.Mp p D1 = poly_mod.Mp p D'" 
  "poly_mod.Mp p H1 = poly_mod.Mp p H'" 
  "poly_mod.Mp p S1 = poly_mod.Mp p S'" 
  "poly_mod.Mp p T1 = poly_mod.Mp p T'" 
  "monic D'" 
proof -
  define U where U: "U = poly_mod.Mp p (sdiv_poly (C - D * H) q)" 
  note step = step[unfolded hensel_step_def Let_def, folded U]
  obtain A B where dupe1: "dupe_monic_dynamic p D1 H1 S1 T1 U = (A,B)" by force
  note step = step[unfolded dupe1 split]  
  from step have D': "D' = D + smult q B" and H': "H' = H + smult q A"
    by (auto split: prod.splits)
  define U' where U': "U' = poly_mod.Mp q (sdiv_poly (S * D' + T * H' - 1) p)" 
  obtain A' B' where dupe2: "dupe_monic_dynamic q D H S T U' = (A',B')" by force
  from step[folded D' H', folded U', unfolded dupe2 split, folded rq]  
  have S': "S' = poly_mod.Mp r (S - Polynomial.smult p A')" and
    T': "T' = poly_mod.Mp r (T - Polynomial.smult p B')" by auto
  from hensel_step_main[OF one_q one_p CDHq D1D H1H S1S T1T mon mon1 q p D1 H1 S1 T1 D H S T U 
    dupe1 D' H' U' dupe2 rq pq S' T']
  show "poly_mod.eq_m r (D' * S' + H' * T') 1"
    "poly_mod.eq_m r C (D' * H')" 
    "poly_mod.Mp r D' = D'" 
    "poly_mod.Mp r H' = H'" 
    "poly_mod.Mp r S' = S'" 
    "poly_mod.Mp r T' = T'"
    "monic D'" by auto
  from pq obtain s where q: "q = p * s" by (metis dvdE)
  show "poly_mod.Mp p D1 = poly_mod.Mp p D'" 
    "poly_mod.Mp p H1 = poly_mod.Mp p H'" 
    unfolding q D' D1D H' H1H
    by (metis add.right_neutral poly_mod.Mp_smult_m_0 poly_mod.plus_Mp(2) smult_smult)+  
  from \<open>q > 1\<close> have q0: "q > 0" by auto
  show "poly_mod.Mp p S1 = poly_mod.Mp p S'" 
    "poly_mod.Mp p T1 = poly_mod.Mp p T'" 
    unfolding S' S1S T' T1T poly_mod_2.Mp_product_modulus[OF poly_mod_2.intro[OF \<open>p > 1\<close>] rq q0]
    by (metis group_add_class.diff_0_right poly_mod.Mp_smult_m_0 poly_mod.minus_Mp(2))+  
qed

lemma quadratic_hensel_step: assumes step: "quadratic_hensel_step q S T D H = (S', T', D', H')"
  and CDH: "poly_mod.eq_m q C (D * H)"
  and one: "poly_mod.eq_m q (D * S + H * T) 1"
  and D: "poly_mod.Mp q D = D" 
  and H: "poly_mod.Mp q H = H"
  and S: "poly_mod.Mp q S = S" 
  and T: "poly_mod.Mp q T = T"
  and mon: "monic D" 
  and q: "q > 1" 
  and rq: "r = q * q" 
shows 
  "poly_mod.eq_m r C (D' * H')" 
  "poly_mod.eq_m r (D' * S' + H' * T') 1"
  "poly_mod.Mp r D' = D'" 
  "poly_mod.Mp r H' = H'" 
  "poly_mod.Mp r S' = S'" 
  "poly_mod.Mp r T' = T'" 
  "poly_mod.Mp q D = poly_mod.Mp q D'" 
  "poly_mod.Mp q H = poly_mod.Mp q H'" 
  "poly_mod.Mp q S = poly_mod.Mp q S'" 
  "poly_mod.Mp q T = poly_mod.Mp q T'" 
  "monic D'" 
proof (atomize(full), goal_cases)
  case 1
  from hensel_step[OF step[unfolded quadratic_hensel_step_def] one mon q CDH one refl refl refl refl mon q D H S T D H S T rq]
  show ?case by auto
qed

context
  fixes p :: int and S1 T1 D1 H1 :: "int poly" 
begin
private lemma decrease[termination_simp]: "\<not> j \<le> 1 \<Longrightarrow> odd j \<Longrightarrow> Suc (j div 2) < j" by presburger

fun quadratic_hensel_loop where 
  "quadratic_hensel_loop (j :: nat) = (
      if j \<le> 1 then (p, S1, T1, D1, H1) else
      if even j then 
          (case quadratic_hensel_loop (j div 2) of
             (q, S, T, D, H) \<Rightarrow>
          let qq = q * q in 
          (case quadratic_hensel_step q S T D H of \<comment> \<open>quadratic step\<close>
            (S', T', D', H') \<Rightarrow> (qq, S', T', D', H')))
     else \<comment> \<open>odd \<open>j\<close>\<close>
        (case quadratic_hensel_loop (j div 2 + 1) of
           (q, S, T, D, H) \<Rightarrow>       
          (case quadratic_hensel_step q S T D H of \<comment> \<open>quadratic step\<close>
            (S', T', D', H') \<Rightarrow> 
                let qq = q * q; pj = qq div p; down = poly_mod.Mp pj in
                  (pj, down S', down T', down D', down H'))))"

definition "quadratic_hensel_main j = (case quadratic_hensel_loop j of 
    (qq, S, T, D, H) \<Rightarrow> (D, H))" 

declare quadratic_hensel_loop.simps[simp del]

\<comment> \<open>unroll the definition of \<open>hensel_loop\<close> so that in outermost iteration we can use \<open>simple_hensel_step\<close>\<close>
lemma quadratic_hensel_main_code[code]: "quadratic_hensel_main j = (
   if j \<le> 1 then (D1, H1)
      else if even j
      then (case quadratic_hensel_loop (j div 2) of
            (q, S, T, D, H) \<Rightarrow>
               simple_quadratic_hensel_step q S T D H)            
       else (case quadratic_hensel_loop (j div 2 + 1) of
            (q, S, T, D, H) \<Rightarrow>
              (case simple_quadratic_hensel_step q S T D H of 
                (D', H') \<Rightarrow> let down = poly_mod.Mp (q * q div p) in (down D', down H'))))"
  unfolding quadratic_hensel_loop.simps[of j] quadratic_hensel_main_def Let_def 
  by (simp split: if_splits prod.splits option.splits sum.splits 
      add: quadratic_hensel_step_code simple_quadratic_hensel_step_def Let_def)


context
  fixes j :: nat 
  assumes 1: "poly_mod.eq_m p (D1 * S1 + H1 * T1) 1"
  and CDH1: "poly_mod.eq_m p C (D1 * H1)" 
  and mon1: "monic D1" 
  and p: "p > 1" 
  and D1: "poly_mod.Mp p D1 = D1" 
  and H1: "poly_mod.Mp p H1 = H1"  
  and S1: "poly_mod.Mp p S1 = S1" 
  and T1: "poly_mod.Mp p T1 = T1"  
  and j: "j \<ge> 1" 
begin

lemma quadratic_hensel_loop:
  assumes "quadratic_hensel_loop j = (q, S, T, D, H)"
  shows "(poly_mod.eq_m q C (D * H) \<and> monic D
    \<and> poly_mod.eq_m p D1 D \<and> poly_mod.eq_m p H1 H
    \<and> poly_mod.eq_m q (D * S + H * T) 1
    \<and> poly_mod.Mp q D = D \<and> poly_mod.Mp q H = H
    \<and> poly_mod.Mp q S = S \<and> poly_mod.Mp q T = T
    \<and> q = p^j)" 
  using j assms
proof (induct j arbitrary: q S T D H rule: less_induct)
  case (less j q' S' T' D' H')
  note res = less(3)
  interpret poly_mod_2 p using p by (rule poly_mod_2.intro)
  let ?hens = "quadratic_hensel_loop" 
  note simp[simp] = quadratic_hensel_loop.simps[of j]
  show ?case
  proof (cases "j = 1")
    case True
    show ?thesis using res simp unfolding True using CDH1 1 mon1 D1 H1 S1 T1 by auto
  next
    case False
    with less(2) have False: "(j \<le> 1) = False" by auto
    have mod_2: "k \<ge> 1 \<Longrightarrow> poly_mod_2 (p^k)" for k by (intro poly_mod_2.intro, insert p, auto)
    {
      fix k D
      assume *: "k \<ge> 1" "k \<le> j" "poly_mod.Mp (p ^ k) D = D" 
      from *(2) have "{0..<p ^ k} \<subseteq> {0..<p ^ j}" using p by auto
      hence "poly_mod.Mp (p ^ j) D = D" 
        unfolding poly_mod_2.Mp_ident_iff[OF mod_2[OF less(2)]]
        using *(3)[unfolded poly_mod_2.Mp_ident_iff[OF mod_2[OF *(1)]]] by blast
    } note lift_norm = this
    show ?thesis
    proof (cases "even j")
      case True
      let ?j2 = "j div 2" 
      from False have lt: "?j2 < j" "1 \<le> ?j2" by auto
      obtain q S T D H where rec: "?hens ?j2 = (q, S, T, D, H)" by (cases "?hens ?j2", auto)
      note IH = less(1)[OF lt rec]
      from IH
      have *: "poly_mod.eq_m q C (D * H)" 
        "poly_mod.eq_m q (D * S + H * T) 1"
        "monic D" 
        "eq_m D1 D" 
        "eq_m H1 H"
        "poly_mod.Mp q D = D"
        "poly_mod.Mp q H = H"
        "poly_mod.Mp q S = S"
        "poly_mod.Mp q T = T"
        "q = p ^ ?j2"
        by auto
      hence norm: "poly_mod.Mp (p ^ j) D = D" "poly_mod.Mp (p ^ j) H = H"
        "poly_mod.Mp (p ^ j) S = S" "poly_mod.Mp (p ^ j) T = T"
        using lift_norm[OF lt(2)] by auto
      from lt p have q: "q > 1" unfolding * by simp
      let ?step = "quadratic_hensel_step q S T D H" 
      obtain S2 T2 D2 H2 where step_res: "?step = (S2, T2, D2, H2)" by (cases ?step, auto)
      note step = quadratic_hensel_step[OF step_res *(1,2,6-9,3) q refl]
      let ?qq = "q * q"
      {
        fix D D2
        assume "poly_mod.Mp q D = poly_mod.Mp q D2" 
        from arg_cong[OF this, of Mp] Mp_Mp_pow_is_Mp[of ?j2, OF _ p, folded *(10)] lt
        have "Mp D = Mp D2" by simp
      } note shrink = this
      have **: "poly_mod.eq_m ?qq C (D2 * H2)" 
        "poly_mod.eq_m ?qq (D2 * S2 + H2 * T2) 1" 
        "monic D2" 
        "eq_m D1 D2"
        "eq_m H1 H2" 
        "poly_mod.Mp ?qq D2 = D2" 
        "poly_mod.Mp ?qq H2 = H2" 
        "poly_mod.Mp ?qq S2 = S2" 
        "poly_mod.Mp ?qq T2 = T2" 
        using step shrink[of H H2] shrink[of D D2] *(4-7) by auto
      note simp = simp False if_False rec split Let_def step_res option.simps
      from True have j: "p ^ j = p ^ (2 * ?j2)" by auto
      with *(10) have qq: "q * q = p ^ j"
        by (simp add: power_mult_distrib semiring_normalization_rules(30-))
      from res[unfolded simp] True have id': "q' = ?qq" "S' = S2" "T' = T2" "D' = D2" "H' = H2" by auto 
      show ?thesis unfolding id' using ** by (auto simp: qq)
    next
      case odd: False
      hence False': "(even j) = False" by auto
      let ?j2 = "j div 2 + 1" 
      from False odd have lt: "?j2 < j" "1 \<le> ?j2" by presburger+
      obtain q S T D H where rec: "?hens ?j2 = (q, S, T, D, H)" by (cases "?hens ?j2", auto)
      note IH = less(1)[OF lt rec]
      note simp = simp False if_False rec sum.simps split Let_def False' option.simps
      from IH have *: "poly_mod.eq_m q C (D * H)" 
          "poly_mod.eq_m q (D * S + H * T) 1"
          "monic D" 
          "eq_m D1 D" 
          "eq_m H1 H"
          "poly_mod.Mp q D = D"
          "poly_mod.Mp q H = H"
          "poly_mod.Mp q S = S"
          "poly_mod.Mp q T = T"
          "q = p ^ ?j2"
          by auto
      hence norm: "poly_mod.Mp (p ^ j) D = D" "poly_mod.Mp (p ^ j) H = H" 
        using lift_norm[OF lt(2)] lt by auto
      from lt p have q: "q > 1" unfolding *
        using mod_2 poly_mod_2.m1 by blast
      let ?step = "quadratic_hensel_step q S T D H" 
      obtain S2 T2 D2 H2 where step_res: "?step = (S2, T2, D2, H2)" by (cases ?step, auto)
      have dvd: "q dvd q" by auto
      note step = quadratic_hensel_step[OF step_res *(1,2,6-9,3) q refl]         
      let ?qq = "q * q"
      {
        fix D D2
        assume "poly_mod.Mp q D = poly_mod.Mp q D2" 
        from arg_cong[OF this, of Mp] Mp_Mp_pow_is_Mp[of ?j2, OF _ p, folded *(10)] lt
        have "Mp D = Mp D2" by simp
      } note shrink = this
      have **: "poly_mod.eq_m ?qq C (D2 * H2)" 
        "poly_mod.eq_m ?qq (D2 * S2 + H2 * T2) 1" 
        "monic D2" 
        "eq_m D1 D2"
        "eq_m H1 H2" 
        "poly_mod.Mp ?qq D2 = D2" 
        "poly_mod.Mp ?qq H2 = H2" 
        "poly_mod.Mp ?qq S2 = S2"
        "poly_mod.Mp ?qq T2 = T2"
        using step shrink[of H H2] shrink[of D D2] *(4-7) by auto
      note simp = simp False if_False rec split Let_def step_res option.simps
      from odd have j: "Suc j = 2 * ?j2" by auto
      from arg_cong[OF this, of "\<lambda> j. p ^ j div p"]
      have pj: "p ^ j = q * q div p" and qq: "q * q = p ^ j * p" unfolding *(10) using p
        by (simp add: power_mult_distrib semiring_normalization_rules(30-))+
      let ?pj = "p ^ j" 
      from res[unfolded simp] pj
      have id: 
        "q' = p^j" 
        "S' = poly_mod.Mp ?pj S2" 
        "T' = poly_mod.Mp ?pj T2" 
        "D' = poly_mod.Mp ?pj D2" 
        "H' = poly_mod.Mp ?pj H2" 
        by auto
      interpret pj: poly_mod_2 ?pj by (rule mod_2[OF \<open>1 \<le> j\<close>])
      have norm: "pj.Mp D' = D'" "pj.Mp H' = H'"
        unfolding id by (auto simp: poly_mod.Mp_Mp)
      have mon: "monic D'" using pj.monic_Mp[OF step(11)] unfolding id .
      have id': "Mp (pj.Mp D) = Mp D" for D using \<open>1 \<le> j\<close>
        by (simp add: Mp_Mp_pow_is_Mp p)
      have eq: "eq_m D1 D2 \<Longrightarrow> eq_m D1 (pj.Mp D2)" for D1 D2 
        unfolding id' by auto
      have id'': "pj.Mp (poly_mod.Mp (q * q) D) = pj.Mp D" for D
        unfolding qq by (rule pj.Mp_product_modulus[OF refl], insert p, auto)
      {
        fix D1 D2
        assume "poly_mod.eq_m (q * q) D1 D2" 
        hence "poly_mod.Mp (q * q) D1 = poly_mod.Mp (q * q) D2" by simp
        from arg_cong[OF this, of pj.Mp] 
        have "pj.Mp D1 = pj.Mp D2" unfolding id'' .
      } note eq' = this
      from eq'[OF step(1)] have eq1: "pj.eq_m C (D' * H')" unfolding id by simp
      from eq'[OF step(2)] have eq2: "pj.eq_m (D' * S' + H' * T') 1" 
        unfolding id by (metis pj.mult_Mp pj.plus_Mp)
      from **(4-5) have eq3: "eq_m D1 D'" "eq_m H1 H'" 
        unfolding id by (auto intro: eq)
      from norm mon eq1 eq2 eq3
      show ?thesis unfolding id by simp
    qed
  qed
qed

lemma quadratic_hensel_main: assumes res: "quadratic_hensel_main j = (D,H)" 
  shows "poly_mod.eq_m (p^j) C (D * H)"
  "monic D" 
  "poly_mod.eq_m p D1 D" 
  "poly_mod.eq_m p H1 H" 
  "poly_mod.Mp (p^j) D = D" 
  "poly_mod.Mp (p^j) H = H" 
proof (atomize(full), goal_cases)
  case 1
  let ?hen = "quadratic_hensel_loop j"
  from res obtain q S T where hen: "?hen = (q, S, T, D, H)" 
    by (cases ?hen, auto simp: quadratic_hensel_main_def)
  from quadratic_hensel_loop[OF hen] show ?case by auto
qed
end
end
end

datatype 'a factor_tree = Factor_Leaf 'a "int poly" | Factor_Node 'a "'a factor_tree" "'a factor_tree" 

fun factor_node_info :: "'a factor_tree \<Rightarrow> 'a" where
  "factor_node_info (Factor_Leaf i x) = i" 
| "factor_node_info (Factor_Node i l r) = i" 
  
fun factors_of_factor_tree :: "'a factor_tree \<Rightarrow> int poly multiset" where
  "factors_of_factor_tree (Factor_Leaf i x) = {#x#}" 
| "factors_of_factor_tree (Factor_Node i l r) = factors_of_factor_tree l + factors_of_factor_tree r"
  
fun product_factor_tree :: "int \<Rightarrow> 'a factor_tree \<Rightarrow> int poly factor_tree" where
  "product_factor_tree p (Factor_Leaf i x) = (Factor_Leaf x x)" 
| "product_factor_tree p (Factor_Node i l r) = (let 
    L = product_factor_tree p l;
    R = product_factor_tree p r;
    f = factor_node_info L;
    g = factor_node_info R;
    fg = poly_mod.Mp p (f * g) 
   in Factor_Node fg L R)"
  
fun sub_trees :: "'a factor_tree \<Rightarrow> 'a factor_tree set" where
  "sub_trees (Factor_Leaf i x) = {Factor_Leaf i x}" 
| "sub_trees (Factor_Node i l r) = insert (Factor_Node i l r) (sub_trees l \<union> sub_trees r)" 
  
lemma sub_trees_refl[simp]: "t \<in> sub_trees t" by (cases t, auto)
  
lemma product_factor_tree: assumes "\<And> x. x \<in># factors_of_factor_tree t \<Longrightarrow> poly_mod.Mp p x = x" 
  shows "u \<in> sub_trees (product_factor_tree p t) \<Longrightarrow> factor_node_info u = f \<Longrightarrow> 
  poly_mod.Mp p f = f \<and> f = poly_mod.Mp p (prod_mset (factors_of_factor_tree u)) \<and> 
  factors_of_factor_tree (product_factor_tree p t) = factors_of_factor_tree t" 
  using assms
proof (induct t arbitrary: u f)
  case (Factor_Node i l r u f)
  interpret poly_mod p . 
  let ?L = "product_factor_tree p l" 
  let ?R = "product_factor_tree p r"
  let ?f = "factor_node_info ?L"
  let ?g = "factor_node_info ?R"
  let ?fg = "Mp (?f * ?g)" 
  have "Mp ?f = ?f \<and> ?f = Mp (prod_mset (factors_of_factor_tree ?L)) \<and>
      (factors_of_factor_tree ?L) = (factors_of_factor_tree l)"      
      by (rule Factor_Node(1)[OF sub_trees_refl refl], insert Factor_Node(5), auto)
  hence IH1: "?f = Mp (prod_mset (factors_of_factor_tree ?L))" 
      "(factors_of_factor_tree ?L) = (factors_of_factor_tree l)" by blast+
  have "Mp ?g = ?g \<and> ?g = Mp (prod_mset (factors_of_factor_tree ?R)) \<and>
      (factors_of_factor_tree ?R) = (factors_of_factor_tree r)" 
      by (rule Factor_Node(2)[OF sub_trees_refl refl], insert Factor_Node(5), auto)
  hence IH2: "?g = Mp (prod_mset (factors_of_factor_tree ?R))" 
      "(factors_of_factor_tree ?R) = (factors_of_factor_tree r)" by blast+
  have id: "(factors_of_factor_tree (product_factor_tree p (Factor_Node i l r))) =
    (factors_of_factor_tree (Factor_Node i l r))" by (simp add: Let_def IH1 IH2)
  from Factor_Node(3) consider (root) "u = Factor_Node ?fg ?L ?R" 
    | (l) "u \<in> sub_trees ?L" | (r) "u \<in> sub_trees ?R" 
    by (auto simp: Let_def)  
  thus ?case
  proof cases
    case root
    with Factor_Node have f: "f = ?fg" by auto
    show ?thesis unfolding f root id by (simp add: Let_def ac_simps IH1 IH2)
  next
    case l
    have "Mp f = f \<and> f = Mp (prod_mset (factors_of_factor_tree u))" 
      using Factor_Node(1)[OF l Factor_Node(4)] Factor_Node(5) by auto
    thus ?thesis unfolding id by blast
  next
    case r
    have "Mp f = f \<and> f = Mp (prod_mset (factors_of_factor_tree u))" 
      using Factor_Node(2)[OF r Factor_Node(4)] Factor_Node(5) by auto
    thus ?thesis unfolding id by blast
  qed
qed auto

fun create_factor_tree_simple :: "int poly list \<Rightarrow> unit factor_tree" where
  "create_factor_tree_simple xs = (let n = length xs in if n \<le> 1 then Factor_Leaf () (hd xs)
    else let i = n div 2;
      xs1 = take i xs;
      xs2 = drop i xs
      in Factor_Node () (create_factor_tree_simple xs1) (create_factor_tree_simple xs2)
      )" 
  
declare create_factor_tree_simple.simps[simp del]
  
lemma create_factor_tree_simple: "xs \<noteq> [] \<Longrightarrow> factors_of_factor_tree (create_factor_tree_simple xs) = mset xs" 
proof (induct xs rule: wf_induct[OF wf_measure[of length]])
  case (1 xs)
  from 1(2) have xs: "length xs \<noteq> 0" by auto
  then consider (base) "length xs = 1" | (step) "length xs > 1" by linarith
  thus ?case
  proof cases
    case base
    then obtain x where xs: "xs = [x]" by (cases xs; cases "tl xs"; auto)
    thus ?thesis by (auto simp: create_factor_tree_simple.simps)
  next
    case step
    let ?i = "length xs div 2" 
    let ?xs1 = "take ?i xs" 
    let ?xs2 = "drop ?i xs" 
    from step have xs1: "(?xs1, xs) \<in> measure length" "?xs1 \<noteq> []" by auto
    from step have xs2: "(?xs2, xs) \<in> measure length" "?xs2 \<noteq> []" by auto
    from step have id: "create_factor_tree_simple xs = Factor_Node () (create_factor_tree_simple (take ?i xs))
            (create_factor_tree_simple (drop ?i xs))" unfolding create_factor_tree_simple.simps[of xs] Let_def by auto
    have xs: "xs = ?xs1 @ ?xs2" by auto
    show ?thesis unfolding id arg_cong[OF xs, of mset] mset_append
      using 1(1)[rule_format, OF xs1] 1(1)[rule_format, OF xs2]
      by auto
  qed
qed

text \<open>We define a better factorization tree which balances the trees according to their degree.,
  cf. Modern Computer Algebra, Chapter 15.5 on Multifactor Hensel lifting.\<close>
  
fun partition_factors_main :: "nat \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list \<times> ('a \<times> nat) list" where
  "partition_factors_main s [] = ([], [])" 
| "partition_factors_main s ((f,d) # xs) = (if d \<le> s then case partition_factors_main (s - d) xs of
     (l,r) \<Rightarrow> ((f,d) # l, r) else case partition_factors_main d xs of 
     (l,r) \<Rightarrow> (l, (f,d) # r))" 
  
lemma partition_factors_main: "partition_factors_main s xs = (a,b) \<Longrightarrow> mset xs = mset a + mset b" 
  by (induct s xs arbitrary: a b rule: partition_factors_main.induct, auto split: if_splits prod.splits)

definition partition_factors :: "('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list \<times> ('a \<times> nat) list" where
  "partition_factors xs = (let n = sum_list (map snd xs) div 2 in
     case partition_factors_main n xs of
     ([], x # y # ys) \<Rightarrow> ([x], y # ys)
   | (x # y # ys, []) \<Rightarrow> ([x], y # ys)
   | pair \<Rightarrow> pair)" 
  
lemma partition_factors: "partition_factors xs = (a,b) \<Longrightarrow> mset xs = mset a + mset b"
  unfolding partition_factors_def Let_def 
  by (cases "partition_factors_main (sum_list (map snd xs) div 2) xs", auto split: list.splits
    simp: partition_factors_main)

lemma partition_factors_length: assumes "\<not> length xs \<le> 1" "(a,b) = partition_factors xs"
  shows [termination_simp]: "length a < length xs" "length b < length xs" and "a \<noteq> []" "b \<noteq> []" 
proof -
  obtain ys zs where main: "partition_factors_main (sum_list (map snd xs) div 2) xs = (ys,zs)" by force
  note res = assms(2)[unfolded partition_factors_def Let_def main split]
  from arg_cong[OF partition_factors_main[OF main], of size] have len: "length xs = length ys + length zs" by auto
  with assms(1) have len2: "length ys + length zs \<ge> 2" by auto
  from res len2 have "length a < length xs \<and> length b < length xs \<and> a \<noteq> [] \<and> b \<noteq> []" unfolding len
    by (cases ys; cases zs; cases "tl ys"; cases "tl zs"; auto)
  thus "length a < length xs" "length b < length xs" "a \<noteq> []" "b \<noteq> []" by blast+
qed 
  
fun create_factor_tree_balanced :: "(int poly \<times> nat)list \<Rightarrow> unit factor_tree" where
  "create_factor_tree_balanced xs = (if length xs \<le> 1 then Factor_Leaf () (fst (hd xs)) else
     case partition_factors xs of (l,r) \<Rightarrow> Factor_Node () 
      (create_factor_tree_balanced l)
      (create_factor_tree_balanced r))" 

definition create_factor_tree :: "int poly list \<Rightarrow> unit factor_tree" where
  "create_factor_tree xs = (let ys = map (\<lambda> f. (f, degree f)) xs;
     zs = rev (sort_key snd ys)
     in create_factor_tree_balanced zs)" 

lemma create_factor_tree_balanced: "xs \<noteq> [] \<Longrightarrow> factors_of_factor_tree (create_factor_tree_balanced xs) = mset (map fst xs)" 
proof (induct xs rule: create_factor_tree_balanced.induct)
  case (1 xs)
  show ?case
  proof (cases "length xs \<le> 1")
    case True
    with 1(3) obtain x where xs: "xs = [x]" by (cases xs; cases "tl xs", auto)
    show ?thesis unfolding xs by auto
  next
    case False
    obtain a b where part: "partition_factors xs = (a,b)" by force
    note abp = this[symmetric]
    note nonempty = partition_factors_length(3-4)[OF False abp]
    note IH = 1(1)[OF False abp nonempty(1)] 1(2)[OF False abp nonempty(2)]
    show ?thesis unfolding create_factor_tree_balanced.simps[of xs] part split using 
      False IH partition_factors[OF part] by auto
  qed
qed

lemma create_factor_tree: assumes "xs \<noteq> []"
  shows "factors_of_factor_tree (create_factor_tree xs) = mset xs" 
proof -
  let ?xs = "rev (sort_key snd (map (\<lambda>f. (f, degree f)) xs))" 
  from assms have "set xs \<noteq> {}" by auto
  hence "set ?xs \<noteq> {}" by auto
  hence xs: "?xs \<noteq> []" by blast
  show ?thesis unfolding create_factor_tree_def Let_def create_factor_tree_balanced[OF xs]
    by (auto, induct xs, auto)
qed

context
  fixes p :: int and n :: nat
begin

definition quadratic_hensel_binary :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> int poly \<times> int poly" where
  "quadratic_hensel_binary C D H = (
     case euclid_ext_poly_dynamic p D H of 
      (S,T) \<Rightarrow> quadratic_hensel_main C p S T D H n)" 

fun hensel_lifting_main :: "int poly \<Rightarrow> int poly factor_tree \<Rightarrow> int poly list" where
  "hensel_lifting_main U (Factor_Leaf _ _) = [U]"
| "hensel_lifting_main U (Factor_Node _ l r) = (let 
    v = factor_node_info l;
    w = factor_node_info r;
    (V,W) = quadratic_hensel_binary U v w
    in hensel_lifting_main V l @ hensel_lifting_main W r)"

definition hensel_lifting_monic :: "int poly \<Rightarrow> int poly list \<Rightarrow> int poly list" where
  "hensel_lifting_monic u vs = (if vs = [] then [] else let 
     pn = p^n; 
     C = poly_mod.Mp pn u;
     tree = product_factor_tree p (create_factor_tree vs)
     in hensel_lifting_main C tree)" 

definition hensel_lifting :: "int poly \<Rightarrow> int poly list \<Rightarrow> int poly list" where 
  "hensel_lifting f gs = (let lc = lead_coeff f; 
     ilc = inverse_mod lc (p^n);
     g = smult ilc f
     in hensel_lifting_monic g gs)"

end


context poly_mod_prime begin

context
  fixes n :: nat
  assumes n: "n \<noteq> 0" 
begin

abbreviation "hensel_binary \<equiv> quadratic_hensel_binary p n" 

abbreviation "hensel_main \<equiv> hensel_lifting_main p n" 

lemma hensel_binary: 
  assumes cop: "coprime_m D H" and eq: "eq_m C (D * H)"
  and normalized_input: "Mp D = D" "Mp H = H"
  and monic_input: "monic D" 
  and hensel_result: "hensel_binary C D H = (D',H')" 
  shows "poly_mod.eq_m (p^n) C (D' * H') \<comment> \<open>the main result: equivalence mod \<open>p^n\<close>\<close>
    \<and> monic D' \<comment> \<open>monic output\<close>
    \<and> eq_m D D' \<and> eq_m H H' \<comment> \<open>apply \<open>`mod p`\<close> on \<open>D'\<close> and \<open>H'\<close> yields \<open>D\<close> and \<open>H\<close> again\<close>
    \<and> poly_mod.Mp (p^n) D' = D' \<and> poly_mod.Mp (p^n) H' = H' \<comment> \<open>output is normalized\<close>"
proof -
  from m1 have p: "p > 1" .
  obtain S T where ext: "euclid_ext_poly_dynamic p D H = (S,T)" by force
  obtain D1 H1 where main: "quadratic_hensel_main C p S T D H n = (D1,H1)" by force
  note hen = hensel_result[unfolded quadratic_hensel_binary_def ext split Let_def main]
  from n have n: "n \<ge> 1" by simp
  note eucl = euclid_ext_poly_dynamic[OF cop normalized_input ext]
  note main = quadratic_hensel_main[OF eucl(1) eq monic_input p normalized_input eucl(2-) n main]
  show ?thesis using hen main by auto
qed

lemma hensel_main: 
  assumes eq: "eq_m C (prod_mset (factors_of_factor_tree Fs))"
  and "\<And> F. F \<in># factors_of_factor_tree Fs \<Longrightarrow> Mp F = F \<and> monic F"  
  and hensel_result: "hensel_main C Fs = Gs" 
  and C: "monic C" "poly_mod.Mp (p^n) C = C" 
  and sf: "square_free_m C" 
  and "\<And> f t. t \<in> sub_trees Fs \<Longrightarrow> factor_node_info t = f \<Longrightarrow> f = Mp (prod_mset (factors_of_factor_tree t))"
  shows "poly_mod.eq_m (p^n) C (prod_list Gs) \<comment> \<open>the main result: equivalence mod \<open>p^n\<close>\<close>
    \<and> factors_of_factor_tree Fs = mset (map Mp Gs)
    \<and> (\<forall> G. G \<in> set Gs \<longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G)"
  using assms
proof (induct Fs arbitrary: C Gs)
  case (Factor_Leaf f fs C Gs)
  thus ?case by auto
next
  case (Factor_Node f l r C Gs) note * = this
  note simps = hensel_lifting_main.simps
  note IH1 = *(1)[rule_format]
  note IH2 = *(2)[rule_format]
  note res = *(5)[unfolded simps Let_def]
  note eq = *(3)
  note Fs = *(4)
  note C = *(6,7)
  note sf = *(8)
  note inv = *(9)
  interpret pn: poly_mod_2 "p^n" apply (unfold_locales) using m1 n by auto
  let ?Mp = "pn.Mp"
  define D where "D \<equiv> prod_mset (factors_of_factor_tree l)" 
  define H where "H \<equiv> prod_mset (factors_of_factor_tree r)" 
  let ?D = "Mp D" 
  let ?H = "Mp H"
  let ?D' = "factor_node_info l" 
  let ?H' = "factor_node_info r" 
  obtain A B where hen: "hensel_binary C ?D' ?H' = (A,B)" by force
  note res = res[unfolded hen split]  
  obtain AD where AD': "AD = hensel_main A l" by auto
  obtain BH where BH': "BH = hensel_main B r" by auto
  from inv[of l, OF _ refl] have D': "?D' = ?D" unfolding D_def by auto
  from inv[of r, OF _ refl] have H': "?H' = ?H" unfolding H_def by auto
  from eq[simplified]
  have eq': "Mp C = Mp (?D * ?H)" unfolding D_def H_def by simp
  from square_free_m_cong[OF sf, of "?D * ?H", OF eq'] 
  have sf': "square_free_m (?D * ?H)" .
  from poly_mod_prime.square_free_m_prod_imp_coprime_m[OF _ this]
  have cop': "coprime_m ?D ?H" unfolding poly_mod_prime_def using prime .
  from eq' have eq': "eq_m C (?D * ?H)" by simp
  have monD: "monic D" unfolding D_def by (rule monic_prod_mset, insert Fs, auto)
  from hensel_binary[OF _ _ _ _ _ hen, unfolded D' H', OF cop' eq' Mp_Mp Mp_Mp monic_Mp[OF monD]] 
  have step: "poly_mod.eq_m (p ^ n) C (A * B) \<and> monic A \<and> eq_m ?D A \<and>
     eq_m ?H B \<and> ?Mp A = A \<and> ?Mp B = B" .
  from res have Gs: "Gs = AD @ BH" by (simp add: AD' BH')
  have AD: "eq_m A ?D" "?Mp A = A" "eq_m A (prod_mset (factors_of_factor_tree l))"  
    and monA: "monic A"
    using step by (auto simp: D_def)
  note sf_fact = square_free_m_factor[OF sf']
  from square_free_m_cong[OF sf_fact(1)] AD have sfA: "square_free_m A" by auto
  have IH1: "poly_mod.eq_m (p ^ n) A (prod_list AD) \<and>
    factors_of_factor_tree l = mset (map Mp AD) \<and>
    (\<forall>G. G \<in> set AD \<longrightarrow> monic G \<and> ?Mp G = G)"
    by (rule IH1[OF AD(3) Fs AD'[symmetric] monA AD(2) sfA inv], auto)
  have BH: "eq_m B ?H" "pn.Mp B = B" "eq_m B (prod_mset (factors_of_factor_tree r))"
      using step by (auto simp: H_def)
  from step have "pn.eq_m C (A * B)" by simp
  hence "?Mp C = ?Mp (A * B)" by simp
  with C AD(2) have "pn.Mp C = pn.Mp (A * pn.Mp B)" by simp
  from arg_cong[OF this, of lead_coeff] C
  have "monic (pn.Mp (A * B))" by simp
  then have "lead_coeff (pn.Mp A) * lead_coeff (pn.Mp B) = 1"
    by (metis lead_coeff_mult leading_coeff_neq_0 local.step mult_cancel_right2 pn.degree_m_eq pn.m1 poly_mod.M_def poly_mod.Mp_coeff)
  with monA AD(2) BH(2) have monB: "monic B" by simp
  from square_free_m_cong[OF sf_fact(2)] BH have sfB: "square_free_m B" by auto
  have IH2: "poly_mod.eq_m (p ^ n) B (prod_list BH) \<and>
      factors_of_factor_tree r = mset (map Mp BH) \<and>
      (\<forall>G. G \<in> set BH \<longrightarrow> monic G \<and> ?Mp G = G)" 
    by (rule IH2[OF BH(3) Fs BH'[symmetric] monB BH(2) sfB inv], auto)
  from step have "?Mp C = ?Mp (?Mp A * ?Mp B)" by auto
  also have "?Mp A = ?Mp (prod_list AD)" using IH1 by auto
  also have "?Mp B = ?Mp (prod_list BH)" using IH2 by auto
  finally have "poly_mod.eq_m (p ^ n) C (prod_list AD * prod_list BH)" 
    by (auto simp: poly_mod.mult_Mp)
  thus ?case unfolding Gs using IH1 IH2 by auto
qed

lemma hensel_lifting_monic: 
  assumes eq: "poly_mod.eq_m p C (prod_list Fs)"
  and Fs: "\<And> F. F \<in> set Fs \<Longrightarrow> poly_mod.Mp p F = F \<and> monic F"  
  and res: "hensel_lifting_monic p n C Fs = Gs" 
  and mon: "monic (poly_mod.Mp (p^n) C)" 
  and sf: "poly_mod.square_free_m p C"
  shows "poly_mod.eq_m (p^n) C (prod_list Gs)"
    "mset (map (poly_mod.Mp p) Gs) = mset Fs" 
    "G \<in> set Gs \<Longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G"
proof -
  note res = res[unfolded hensel_lifting_monic_def Let_def]
  let ?Mp = "poly_mod.Mp (p ^ n)" 
  let ?C = "?Mp C" 
  interpret poly_mod_prime p
    by (unfold_locales, insert n prime, auto)
  interpret pn: poly_mod_2 "p^n" using m1 n poly_mod_2.intro by auto
  from eq n have eq: "eq_m (?Mp C) (prod_list Fs)"
    using Mp_Mp_pow_is_Mp eq m1 n by force
  have "poly_mod.eq_m (p^n) C (prod_list Gs) \<and> mset (map (poly_mod.Mp p) Gs) = mset Fs
    \<and> (G \<in> set Gs \<longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G)" 
  proof (cases "Fs = []")
    case True
    with res have Gs: "Gs = []" by auto
    from eq have "Mp ?C = 1" unfolding True by simp
    hence "degree (Mp ?C) = 0" by simp
    with degree_m_eq_monic[OF mon m1] have "degree ?C = 0" by simp
    with mon have "?C = 1" using monic_degree_0 by blast
    thus ?thesis unfolding True Gs by auto
  next
    case False
    let ?t = "create_factor_tree Fs" 
    note tree = create_factor_tree[OF False]
    from False res have hen: "hensel_main ?C (product_factor_tree p ?t) = Gs" by auto
    have tree1: "x \<in># factors_of_factor_tree ?t \<Longrightarrow> Mp x = x" for x unfolding tree using Fs by auto
    from product_factor_tree[OF tree1 sub_trees_refl refl, of ?t]
    have id: "(factors_of_factor_tree (product_factor_tree p ?t)) =
        (factors_of_factor_tree ?t)" by auto
    have eq: "eq_m ?C (prod_mset (factors_of_factor_tree (product_factor_tree p ?t)))"
      unfolding id tree using eq by auto  
    have id': "Mp C = Mp ?C" using n by (simp add: Mp_Mp_pow_is_Mp m1)
    have "pn.eq_m ?C (prod_list Gs) \<and> mset Fs = mset (map Mp Gs) \<and> (\<forall>G. G \<in> set Gs \<longrightarrow> monic G \<and> pn.Mp G = G)"
      by (rule hensel_main[OF eq Fs hen mon pn.Mp_Mp square_free_m_cong[OF sf id'], unfolded id tree],
      insert product_factor_tree[OF tree1], auto)
    thus ?thesis by auto
  qed
  thus "poly_mod.eq_m (p^n) C (prod_list Gs)"
    "mset (map (poly_mod.Mp p) Gs) = mset Fs" 
    "G \<in> set Gs \<Longrightarrow> monic G \<and> poly_mod.Mp (p^n) G = G" by blast+
qed

lemma hensel_lifting:
  assumes res: "hensel_lifting p n f fs = gs"                      \<comment> \<open>result of hensel is fact. \<open>gs\<close>\<close>
    and cop: "coprime (lead_coeff f) p"
    and sf: "poly_mod.square_free_m p f"
    and fact: "poly_mod.factorization_m p f (c, mset fs)"          \<comment> \<open>input is fact. \<open>fs mod p\<close>\<close>
    and c: "c \<in> {0..<p}"
    and norm: "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})"
  shows "poly_mod.factorization_m (p^n) f (lead_coeff f, mset gs) \<comment> \<open>factorization mod \<open>p^n\<close>\<close>"
      "sort (map degree fs) = sort (map degree gs)                \<comment> \<open>degrees stay the same\<close>"
      "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and>   \<comment> \<open>monic and normalized\<close>
        irreducible_m g \<and>                               \<comment> \<open>irreducibility even mod \<open>p\<close>\<close>
        degree_m g = degree g   \<comment> \<open>mod \<open>p\<close> does not change degree of \<open>g\<close>\<close>"
proof -
  interpret poly_mod_prime p using prime by unfold_locales
  interpret q: poly_mod_2 "p^n" using m1 n unfolding poly_mod_2_def by auto
  from fact have eq: "eq_m f (smult c (prod_list fs))"  
    and mon_fs: "(\<forall>fi\<in>set fs. monic (Mp fi) \<and> irreducible\<^sub>d_m fi)"
    unfolding factorization_m_def by auto
  {
    fix f
    assume "f \<in> set fs" 
    with mon_fs norm have "set (coeffs f) \<subseteq> {0..<p}" and "monic (Mp f)" by auto
    hence "monic f" using Mp_ident_iff' by force
  } note mon_fs' = this
  have Mp_id: "\<And> f. Mp (q.Mp f) = Mp f" by (simp add: Mp_Mp_pow_is_Mp m1 n)
  let ?lc = "lead_coeff f" 
  let ?q = "p ^ n" 
  define ilc where "ilc \<equiv> inverse_mod ?lc ?q" 
  define F where "F \<equiv> smult ilc f" 
  from res[unfolded hensel_lifting_def Let_def] 
  have hen: "hensel_lifting_monic p n F fs = gs" 
    unfolding ilc_def F_def .
  from m1 n cop have inv: "q.M (ilc * ?lc) = 1"
    by (auto simp add: q.M_def inverse_mod_pow ilc_def)
  hence ilc0: "ilc \<noteq> 0" by (cases "ilc = 0", auto)
  {
    fix q
    assume "ilc * ?lc = ?q * q" 
    from arg_cong[OF this, of q.M] have "q.M (ilc * ?lc) = 0" 
      unfolding q.M_def by auto
    with inv have False by auto
  } note not_dvd = this
  have mon: "monic (q.Mp F)" unfolding F_def q.Mp_coeff coeff_smult
    by (subst q.degree_m_eq [OF _ q.m1]) (auto simp: inv ilc0 [symmetric] intro: not_dvd)
  have "q.Mp f = q.Mp (smult (q.M (?lc * ilc)) f)" using inv by (simp add: ac_simps)
  also have "\<dots> = q.Mp (smult ?lc F)" by (simp add: F_def)
  finally have f: "q.Mp f = q.Mp (smult ?lc F)" .
  from arg_cong[OF f, of Mp]
  have f_p: "Mp f = Mp (smult ?lc F)" 
    by (simp add: Mp_Mp_pow_is_Mp n m1)
  from arg_cong[OF this, of square_free_m, unfolded Mp_square_free_m] sf
  have "square_free_m (smult ?lc F)" by simp
  from square_free_m_smultD[OF this] have sf: "square_free_m F" .
  
  define c' where "c' \<equiv> M (c * ilc)"
  from factorization_m_smult[OF fact, of ilc, folded F_def] 
  have fact: "factorization_m F (c', mset fs)" unfolding c'_def factorization_m_def by auto
  hence eq: "eq_m F (smult c' (prod_list fs))" unfolding factorization_m_def by auto
  from factorization_m_lead_coeff[OF fact] monic_Mp[OF mon, unfolded Mp_id] have "M c' = 1" 
    by auto
  hence c': "c' = 1" unfolding c'_def by auto
  with eq have eq: "eq_m F (prod_list fs)" by auto 
  {
    fix f
    assume "f \<in> set fs" 
    with mon_fs' norm have "Mp f = f \<and> monic f" unfolding Mp_ident_iff'
      by auto
  } note fs = this
  note hen = hensel_lifting_monic[OF eq fs hen mon sf]
  from hen(2) have gs_fs: "mset (map Mp gs) = mset fs" by auto
  have eq: "q.eq_m f (smult ?lc (prod_list gs))" 
    unfolding f using arg_cong[OF hen(1), of "\<lambda> f. q.Mp (smult ?lc f)"] by simp
  {
    fix g 
    assume g: "g \<in> set gs"
    from hen(3)[OF _ g] have mon_g: "monic g" and Mp_g: "q.Mp g = g" by auto
    from g have "Mp g \<in># mset (map Mp gs)" by auto
    from this[unfolded gs_fs] obtain f where f: "f \<in> set fs" and fg: "eq_m f g" by auto
    from mon_fs f fs have irr_f: "irreducible\<^sub>d_m f" and mon_f: "monic f" and Mp_f: "Mp f = f" by auto
    have deg: "degree_m g = degree g" 
      by (rule degree_m_eq_monic[OF mon_g m1])
    from irr_f fg have irr_g: "irreducible\<^sub>d_m g" 
      unfolding irreducible\<^sub>d_m_def dvdm_def by simp
    have "q.irreducible\<^sub>d_m g"
      by (rule irreducible\<^sub>d_lifting[OF n _ irr_g], unfold deg, rule q.degree_m_eq_monic[OF mon_g q.m1])
    note mon_g Mp_g deg irr_g this
  } note g = this
  {
    fix g
    assume "g \<in> set gs" 
    from g[OF this]
    show "monic g \<and> q.Mp g = g \<and> irreducible_m g \<and> degree_m g = degree g" by auto
  }
  show "sort (map degree fs) = sort (map degree gs)" 
  proof (rule sort_key_eq_sort_key)
    have "mset (map degree fs) = image_mset degree (mset fs)" by auto
    also have "\<dots> = image_mset degree (mset (map Mp gs))" unfolding gs_fs ..
    also have "\<dots> = mset (map degree (map Mp gs))" unfolding mset_map ..
    also have "map degree (map Mp gs) = map degree_m gs" by auto
    also have "\<dots> = map degree gs" using g(3) by auto
    finally show "mset (map degree fs) = mset (map degree gs)" .
  qed auto
  show "q.factorization_m f (lead_coeff f, mset gs)" 
    using eq g unfolding q.factorization_m_def by auto
qed

end

end
end
