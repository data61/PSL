(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Correctness of the LLL factorization algorithm\<close>

text \<open>This theory connects short vectors of lattices and factors of polynomials. 
  From this connection, we derive soundness of the lattice based factorization algorithm. 
\<close> 

theory LLL_Factorization
  imports
    LLL_Factorization_Impl  
    Berlekamp_Zassenhaus.Factorize_Int_Poly
begin

subsection \<open>Basic facts about the auxiliary functions\<close>
hide_const (open) module.smult

lemma nth_factorization_lattice:
  fixes u and d
  defines "n \<equiv> degree u"
  assumes "i < n + d"
  shows "factorization_lattice u d m ! i =
    vec_of_poly_n (if i < d then u * monom 1 (d - Suc i) else monom m (n+d-Suc i)) (n+d)"
  using assms
  by (unfold factorization_lattice_def, auto simp: nth_append smult_monom Let_def not_less)

lemma length_factorization_lattice[simp]: 
  shows "length (factorization_lattice u d m) = degree u + d"
  by (auto simp: factorization_lattice_def Let_def)

lemma dim_factorization_lattice:
  assumes "x < degree u + d" 
  shows "dim_vec (factorization_lattice u d m ! x) = degree u + d"
  unfolding factorization_lattice_def using assms nth_append
  by (simp add: nth_append Let_def)

lemma dim_factorization_lattice_element: 
  assumes "x \<in> set (factorization_lattice u d m)" shows "dim_vec x = degree u + d" 
  using assms by (auto simp: factorization_lattice_def Let_def)

lemma set_factorization_lattice_in_carrier[simp]: "set (factorization_lattice u d m) \<subseteq> carrier_vec (degree u + d)" 
  using dim_factorization_lattice by (auto simp: factorization_lattice_def Let_def) 

lemma choose_u_Cons: "choose_u (x#xs) = 
  (if xs = [] then x else min_degree_poly x (choose_u xs))"
  by (cases xs, auto)

lemma choose_u_member: "xs \<noteq> [] \<Longrightarrow> choose_u xs \<in> set xs"
  by (induct xs, auto simp: choose_u_Cons)

declare choose_u.simps[simp del]


subsection \<open>Facts about Sylvester matrices and norms\<close>

lemma (in LLL) lattice_is_span [simp]: "lattice_of xs = span_list xs"
  by (unfold lattice_of_def span_list_def lincomb_list_def image_def, auto)

lemma sq_norm_row_sylvester_mat1:
  fixes f g :: "'a :: conjugatable_ring poly"
  assumes i: "i < degree g"
  shows "\<parallel>(row (sylvester_mat f g) i)\<parallel>\<^sup>2 = \<parallel>f\<parallel>\<^sup>2"
proof (cases "f = 0")
  case True
  thus ?thesis
    by (auto simp add: sylvester_mat_def row_def sq_norm_vec_def o_def
        interv_sum_list_conv_sum_set_nat i intro!: sum_list_zero)
next
  case False note f = False         
  let ?f = "\<lambda>j. if i \<le> j \<and> j - i \<le> degree f then coeff f (degree f + i - j) else 0"
  let ?h = "\<lambda>j. j + i"
  let ?row = "vec (degree f + degree g) ?f "
  let ?g = "\<lambda>j. degree f - j"
  have image_g: "?g ` {0..<Suc (degree f)} = {0..<Suc (degree f)}" 
    by (auto simp add: image_def) 
       (metis (no_types, hide_lams) Nat.add_diff_assoc add.commute add_diff_cancel_left' 
        atLeastLessThan_iff diff_Suc_Suc diff_Suc_less less_Suc_eq_le zero_le)
  have bij_h: "bij_betw ?h {0..<Suc (degree f)} {i..< Suc (degree f + i)}"
    unfolding bij_betw_def image_def
    by (auto, metis atLeastLessThan_iff le_add_diff_inverse2 
        less_diff_conv linorder_not_less not_less_eq zero_order(3))
  have "\<parallel>row (sylvester_mat f g) i\<parallel>\<^sup>2 = \<parallel>?row\<parallel>\<^sup>2" 
    by (rule arg_cong[of _ _ "sq_norm_vec"], insert i, 
        auto simp add: row_def sylvester_mat_def sylvester_mat_sub_def)
  also have "... = sum_list (map (sq_norm \<circ> ?f) [0..<degree f + degree g])" 
    unfolding sq_norm_vec_def by auto
  also have "... = sum (sq_norm \<circ> ?f) {0..<degree f + degree g}"
    unfolding interv_sum_list_conv_sum_set_nat by auto
  also have "... = sum (sq_norm \<circ> ?f) {i..< Suc (degree f + i)}" 
    by (rule sum.mono_neutral_right, insert i, auto)
  also have "... = sum ((sq_norm \<circ> ?f) \<circ> ?h) {0..<Suc (degree f)}" 
    by (unfold o_def, rule sum.reindex_bij_betw[symmetric, OF bij_h])
  also have "... = sum (\<lambda>j. sq_norm (coeff f (degree f - j))) {0..<Suc (degree f)}" 
    by (rule sum.cong, auto)
  also have "... = sum ((\<lambda>j. sq_norm (coeff f j)) \<circ> ?g) {0..<Suc (degree f)}" 
    unfolding o_def ..  
  also have "... = sum (\<lambda>j. sq_norm (coeff f j)) (?g ` {0..<Suc (degree f)})"
    by (rule sum.reindex[symmetric], auto simp add: inj_on_def)
  also have "... = sum (sq_norm \<circ> coeff f) {0..<Suc (degree f)}" unfolding image_g by simp
  also have "... = sum_list (map sq_norm (coeffs f))" 
     unfolding coeffs_def using f 
     by (simp add: interv_sum_list_conv_sum_set_nat)
  finally show ?thesis unfolding sq_norm_poly_def by auto
qed


lemma sq_norm_row_sylvester_mat2:
  fixes f g :: "'a :: conjugatable_ring poly"
  assumes i1: "degree g \<le> i" and i2: "i < degree f + degree g"
  shows "\<parallel>row (sylvester_mat f g) i\<parallel>\<^sup>2 = \<parallel>g\<parallel>\<^sup>2"
proof -
  let ?f = "\<lambda>j. if i - degree g \<le> j \<and> j \<le> i then coeff g (i - j) else 0"
  let ?row = "vec (degree f + degree g) ?f"
  let ?h = "\<lambda>j. j + i - degree g"
  let ?g = "\<lambda>j. degree g - j"
  have image_g: "?g ` {0..<Suc (degree g)} = {0..<Suc (degree g)}" 
    by (auto simp add: image_def)
       (metis atLeastLessThan_iff diff_diff_cancel diff_le_self less_Suc_eq_le zero_le)
  have x: "x - (i - degree g) \<le> degree g" if x: "x < Suc i" for x using x by auto
  have bij_h: "bij_betw ?h {0..<Suc (degree g)} {i - degree g..<Suc i}" 
    unfolding bij_betw_def inj_on_def using i1 i2 unfolding image_def
    by (auto, metis (no_types) Nat.add_diff_assoc atLeastLessThan_iff x less_Suc_eq_le 
        less_eq_nat.simps(1) ordered_cancel_comm_monoid_diff_class.diff_add)  
  have "\<parallel>row (sylvester_mat f g) i\<parallel>\<^sup>2 = \<parallel>?row\<parallel>\<^sup>2" 
    by (rule arg_cong[of _ _ "sq_norm_vec"], insert i1 i2, 
        auto simp add: row_def sylvester_mat_def sylvester_mat_sub_def)
  also have "... = sum_list (map (sq_norm \<circ> ?f) [0..<degree f + degree g])" 
    unfolding sq_norm_vec_def by auto
  also have "... = sum (sq_norm \<circ> ?f) {0..<degree f + degree g}"
    unfolding interv_sum_list_conv_sum_set_nat by auto
  also have "... = sum (sq_norm \<circ> ?f) {i - degree g..< Suc i}" 
    by (rule sum.mono_neutral_right, insert i2, auto)
  also have "... = sum ((sq_norm \<circ> ?f) \<circ> ?h) {0..<Suc (degree g)}"
    by (unfold o_def, rule sum.reindex_bij_betw[symmetric, OF bij_h])
  also have "... = sum (\<lambda>j. sq_norm (coeff g (degree g - j))) {0..<Suc (degree g)}" 
    by (rule sum.cong, insert i1, auto)
  also have "... = sum ((\<lambda>j. sq_norm (coeff g j)) \<circ> ?g) {0..<Suc (degree g)}" 
    unfolding o_def ..  
  also have "... = sum (\<lambda>j. sq_norm (coeff g j)) (?g ` {0..<Suc (degree g)})"
    by (rule sum.reindex[symmetric], auto simp add: inj_on_def)
  also have "... = sum (sq_norm \<circ> coeff g) {0..<Suc (degree g)}" unfolding image_g by simp
  also have "... = sum_list (map sq_norm (coeffs g))" 
     unfolding coeffs_def
     by (simp add: interv_sum_list_conv_sum_set_nat)
  finally show ?thesis unfolding sq_norm_poly_def by auto
qed

lemma Hadamard's_inequality_int:
  fixes A::"int mat"
  assumes A: "A \<in> carrier_mat n n" 
  shows "\<bar>det A\<bar> \<le> sqrt (of_int (prod_list (map sq_norm (rows A))))"
proof -
  let ?A = "map_mat real_of_int A" 
  have "\<bar>det A\<bar> = \<bar>det ?A\<bar>" unfolding of_int_hom.hom_det by simp
  also have "\<dots> \<le> sqrt (prod_list (map sq_norm (rows ?A)))" 
    by (rule Hadamard's_inequality[of ?A n], insert A, auto)
  also have "\<dots> = sqrt (of_int (prod_list (map sq_norm (rows A))))" unfolding of_int_hom.hom_prod_list map_map
    by (rule arg_cong[of _ _ "\<lambda> x. sqrt (prod_list x)"], rule nth_equalityI, force, 
      auto simp: sq_norm_of_int[symmetric] row_def intro!: arg_cong[of _ _ sq_norm_vec])
  finally show ?thesis .
qed

lemma resultant_le_prod_sq_norm:
  fixes f g::"int poly"
  defines "n \<equiv> degree f" and "k \<equiv> degree g"
  shows "\<bar>resultant f g\<bar> \<le> sqrt (of_int (\<parallel>f\<parallel>\<^sup>2^k * \<parallel>g\<parallel>\<^sup>2^n))"
proof -
  let ?S = "sylvester_mat f g"
  let ?f = "sq_norm \<circ> row ?S"
  have map_rw1: "map ?f [0..<degree g] = replicate k \<parallel>f\<parallel>\<^sup>2"
  proof (rule nth_equalityI)
    let ?M = "map (sq_norm \<circ> row (sylvester_mat f g)) [0..<degree g]"
    show "length ?M = length (replicate k \<parallel>f\<parallel>\<^sup>2)" using k_def by auto
    show "?M ! i = replicate k \<parallel>f\<parallel>\<^sup>2 ! i" if i: "i < length ?M" for i
    proof -
      have ik: "i<k" using i k_def by auto
      hence i_deg_g: "i < degree g" using k_def by auto
      have "replicate k \<parallel>f\<parallel>\<^sup>2 ! i = \<parallel>f\<parallel>\<^sup>2" by (rule nth_replicate[OF ik])
      also have "... = (sq_norm \<circ> row (sylvester_mat f g)) (0 + i)"
        using sq_norm_row_sylvester_mat1 ik k_def by force      
      also have "... = ?M ! i" by (rule nth_map_upt[symmetric], simp add: i_deg_g)
      finally show "?M ! i = replicate k \<parallel>f\<parallel>\<^sup>2 ! i" ..
    qed
  qed    
  have map_rw2: "map ?f [degree g..<degree f + degree g] = replicate n \<parallel>g\<parallel>\<^sup>2"
  proof (rule nth_equalityI)
    let ?M = "map (sq_norm \<circ> row (sylvester_mat f g)) [degree g..<degree f + degree g]"
    show "length ?M = length (replicate n \<parallel>g\<parallel>\<^sup>2)" by (simp add: n_def)
    show "?M ! i = replicate n \<parallel>g\<parallel>\<^sup>2 ! i" if "i<length ?M" for i
    proof -
      have i_n: "i<n" using n_def that by auto
      hence i_deg_f: "i < degree f" using n_def by auto
      have "replicate n \<parallel>g\<parallel>\<^sup>2 ! i = \<parallel>g\<parallel>\<^sup>2" by (rule nth_replicate[OF i_n])
      also have "... = (sq_norm \<circ> row (sylvester_mat f g)) (degree g + i)"
        using i_n n_def
        by (simp add: sq_norm_row_sylvester_mat2)
      also have "... = ?M ! i"
        by (simp add: i_deg_f)
      finally show "?M ! i = replicate n \<parallel>g\<parallel>\<^sup>2 ! i" ..
    qed
  qed
  have p1: "prod_list (map ?f [0..<degree g]) = \<parallel>f\<parallel>\<^sup>2^k"
    unfolding map_rw1 by (rule prod_list_replicate)
  have p2: "prod_list (map ?f [degree g..<degree f + degree g]) = \<parallel>g\<parallel>\<^sup>2^n"
    unfolding map_rw2 by (rule prod_list_replicate)
  have list_rw: "[0..<degree f + degree g] = [0..<degree g] @ [degree g..<degree f + degree g]"
    by (metis add.commute upt_add_eq_append zero_le)
  have "\<bar>resultant f g\<bar> = \<bar>det ?S\<bar>"  unfolding resultant_def ..
  also have "... \<le> sqrt (of_int (prod_list (map sq_norm (rows ?S))))"
    by (rule Hadamard's_inequality_int, auto)
  also have "map sq_norm (rows ?S) = map ?f [0..<degree f + degree g]"
    unfolding Matrix.rows_def by auto
  also have "... =  map ?f ([0..<degree g] @ [degree g..<degree f + degree g])"
    by (simp add: list_rw)
  also have "prod_list ... = prod_list (map ?f [0..<degree g])
    * prod_list (map ?f [degree g..<degree f + degree g])" by auto
  finally show ?thesis unfolding p1 p2 .
qed

subsection \<open>Proof of the key lemma 16.20\<close>
(* Lemma 16.20 *)
lemma common_factor_via_short:
  fixes f g u :: "int poly"
  defines "n \<equiv> degree f" and "k \<equiv> degree g"
  assumes n0: "n > 0" and k0: "k > 0"
      and monic: "monic u" and deg_u: "degree u > 0"
      and uf: "poly_mod.dvdm m u f" and ug: "poly_mod.dvdm m u g"
      and short: "\<parallel>f\<parallel>\<^sup>2^k * \<parallel>g\<parallel>\<^sup>2^n < m\<^sup>2" 
      and m: "m \<ge> 0"
    shows "degree (gcd f g) > 0"
proof -
  interpret poly_mod m .
  have f_not0: "f \<noteq> 0" and g_not0: "g \<noteq> 0"
    using n0 k0 k_def n_def by auto
  have deg_f: "degree f > 0" using n0 n_def by simp
  have deg_g: "degree g > 0" using k0 k_def by simp
  obtain s t where deg_s: "degree s < degree g" and deg_t: "degree t < degree f" 
    and res_eq: "[:resultant f g:] = s * f + t * g" and s_not0: "s \<noteq> 0" and t_not0: "t \<noteq> 0"
    using resultant_as_nonzero_poly[OF deg_f deg_g] by auto
  have res_eq_modulo: "[:resultant f g:] =m s * f + t * g" using res_eq
    by simp 
  have u_dvdm_res: "u dvdm [:resultant f g:]"
  proof (unfold res_eq, rule dvdm_add)
    show "u dvdm s * f"
      using dvdm_factor[OF uf, of s]
      unfolding mult.commute[of f s] by auto
    show "u dvdm t * g"
      using dvdm_factor[OF ug, of t] 
      unfolding mult.commute[of g t] by auto    
  qed
  have res_0_mod: "resultant f g mod m = 0"
    by (rule monic_dvdm_constant[OF u_dvdm_res monic deg_u])
  have res0: "resultant f g = 0"
  proof (rule mod_0_abs_less_imp_0)
    show "[resultant f g = 0] (mod m)" using res_0_mod unfolding cong_def by auto
    have "\<bar>resultant f g\<bar> \<le> sqrt ((sq_norm_poly f)^k * (sq_norm_poly g)^n)" 
      unfolding k_def n_def
      by (rule resultant_le_prod_sq_norm)
    also have "... < m"
    proof (rule real_less_lsqrt)
      show "0 \<le> real_of_int (\<parallel>f\<parallel>\<^sup>2 ^ k * \<parallel>g\<parallel>\<^sup>2 ^ n)"
        by (simp add: sq_norm_poly_ge_0)
      show "0 \<le> real_of_int m" using m by simp
      show "real_of_int (\<parallel>f\<parallel>\<^sup>2 ^ k * \<parallel>g\<parallel>\<^sup>2 ^ n) < (real_of_int m)\<^sup>2"
        by (metis of_int_less_iff of_int_power short)
    qed
    finally show "\<bar>resultant f g\<bar> < m" using of_int_less_iff by blast 
    qed
  have "\<not> coprime f g" 
    by (rule resultant_zero_imp_common_factor, auto simp add: deg_f res0)
  thus ?thesis
    using res0 resultant_0_gcd by auto
qed  

subsection \<open>Properties of the computed lattice and its connection with Sylvester matrices\<close>

lemma factorization_lattice_as_sylvester:
  fixes p :: "'a :: semidom poly"
  assumes dj: "d \<le> j" and d: "degree p = d"   
  shows "mat_of_rows j (factorization_lattice p (j-d) m) = sylvester_mat_sub d (j-d) p [:m:]"
proof (cases "p=0")
  case True 
  have deg_p: "d = 0" using True d by simp
  show ?thesis
    by (auto simp add: factorization_lattice_def True deg_p mat_of_rows_def d)
next
  case p0: False
  note 1 = degree_mult_eq[OF p0, of "monom _ _", unfolded monom_eq_0_iff, OF one_neq_zero]
  from dj show ?thesis
    apply (cases "m = 0")
    apply (auto simp: mat_eq_iff d[symmetric] 1 coeff_mult_monom
 sylvester_mat_sub_index mat_of_rows_index nth_factorization_lattice vec_index_of_poly_n
 degree_monom_eq coeff_const)
    done
qed


context inj_comm_semiring_hom begin

lemma map_poly_hom_mult_monom [hom_distribs]:
  "map_poly hom (p * monom a n) = map_poly hom p * monom (hom a) n"
  by (auto intro!: poly_eqI simp:coeff_mult_monom hom_mult)

lemma hom_vec_of_poly_n [hom_distribs]:
  "map_vec hom (vec_of_poly_n p n) = vec_of_poly_n (map_poly hom p) n"
  by (auto simp: vec_index_of_poly_n)

lemma hom_factorization_lattice [hom_distribs]:
  shows "map (map_vec hom) (factorization_lattice u k m) = factorization_lattice (map_poly hom u) k (hom m)"
  by (auto intro!:arg_cong[of _ _ "\<lambda>p. vec_of_poly_n p _"] simp: list_eq_iff_nth_eq nth_factorization_lattice hom_vec_of_poly_n map_poly_hom_mult_monom)

end

subsection \<open>Proving that @{const factorization_lattice} returns a basis of the lattice\<close>

context LLL
begin

sublocale idom_vec n "TYPE(int)".

(*In this context, "n" is fixed by the locale and corresponds to "j" in the book*)
lemma upper_triangular_factorization_lattice:
  fixes u :: "'a :: semidom poly" and d :: nat
  assumes d: "d \<le> n" and du: "d = degree u"
  shows "upper_triangular (mat_of_rows n (factorization_lattice u (n-d) k))"
    (is "upper_triangular ?M")
proof (intro upper_triangularI, unfold mat_of_rows_carrier length_factorization_lattice)
  fix i j
  assume ji: "j < i" and i: "i < degree u + (n - d)"
  with d du have jn: "j < n" by auto
  show "?M $$ (i,j) = 0"
  proof (cases "u=0")
    case True with ji i show ?thesis
      by (auto simp: factorization_lattice_def mat_of_rows_def)
next
  case False
  then show ?thesis
    using d ji i
    apply (simp add: du mat_of_rows_index nth_factorization_lattice)
    apply (auto simp: vec_index_of_poly_n[OF jn] degree_mult_eq degree_monom_eq)
    done
  qed
qed

lemma factorization_lattice_diag_nonzero:
  fixes u :: "'a :: semidom poly" and d
  assumes d: "d=degree u" 
    and dn: "d\<le>n"
    and u: "u\<noteq>0" 
    and m0: "k\<noteq>0"
    and i: "i<n"
  shows "(factorization_lattice u (n-d) k) ! i $ i \<noteq> 0"
proof-
  have 1: "monom (1::'a) (n - Suc (degree u + i)) \<noteq> 0" using m0 by auto
  have 2: "i < degree u + (n - d)" using i d by auto
  let ?p = "u * monom 1 (n - Suc (degree u + i))"
  have 3: "i < n - degree u \<Longrightarrow> degree (?p) = n - Suc i"
    using assms by (auto simp: degree_mult_eq[OF _ 1] degree_monom_eq)
  show ?thesis
    apply (unfold nth_factorization_lattice[OF 2] vec_index_of_poly_n[OF 2])
    using assms leading_coeff_0_iff[of ?p]
    apply (cases "i < n - degree u", auto simp: d 3 degree_monom_eq)
    done
qed

corollary factorization_lattice_diag_nonzero_RAT: fixes d
  assumes "d=degree u" 
    and "d\<le>n"
    and "u\<noteq>0" 
    and "k\<noteq>0"
    and "i<n"
  shows "RAT (factorization_lattice u (n-d) k) ! i $ i \<noteq> 0"
  using factorization_lattice_diag_nonzero[OF assms] assms
  by (auto simp: nth_factorization_lattice)

sublocale gs: vec_space "TYPE(rat)" n.

lemma lin_indpt_list_factorization_lattice: fixes d
  assumes d: "d = degree u" and dn: "d \<le> n" and u: "u \<noteq> 0" and k: "k \<noteq> 0"
  shows "gs.lin_indpt_list (RAT (factorization_lattice u (n-d) k))" (is "gs.lin_indpt_list (RAT ?vs)")
proof-
  have 1: "rows (mat_of_rows n (map (map_vec rat_of_int) ?vs)) = map (map_vec rat_of_int) ?vs"
    using dn d
    by (subst rows_mat_of_rows, auto dest!: subsetD[OF set_factorization_lattice_in_carrier])
  note 2 = factorization_lattice_diag_nonzero_RAT[OF d dn u k]
  show ?thesis
    apply (intro gs.upper_triangular_imp_lin_indpt_list[of "mat_of_rows n (RAT ?vs)", unfolded 1])
    using assms 2 by (auto simp: diag_mat_def mat_of_rows_index hom_distribs intro!:upper_triangular_factorization_lattice)
 qed
  
end

subsection \<open>Being in the lattice is being a multiple modulo\<close>

lemma (in semiring_hom) hom_poly_of_vec: "map_poly hom (poly_of_vec v) = poly_of_vec (map_vec hom v)"
  by (auto simp add: coeff_poly_of_vec poly_eq_iff)

abbreviation "of_int_vec \<equiv> map_vec of_int"

context LLL
begin

lemma lincomb_to_dvd_modulo:
  fixes u d
  defines "d \<equiv> degree u"
  assumes d: "d \<le> n"
      and lincomb: "lincomb_list c (factorization_lattice u (n-d) k) = g" (is "?l = ?r")
  shows "poly_mod.dvdm k u (poly_of_vec g)"
proof- 
  let ?S = "sylvester_mat_sub d (n - d) u [:k:]"
  define q where "q \<equiv> poly_of_vec (vec_first (vec n c) (n - d))"
  define r where "r \<equiv> poly_of_vec (vec_last (vec n c) d)"
  have "?l = ?S\<^sup>T *\<^sub>v vec n c"
    apply (subst lincomb_list_as_mat_mult)
    using d d_def apply (force simp:factorization_lattice_def)
    apply (fold transpose_mat_of_rows)
    using d d_def by (simp add: factorization_lattice_as_sylvester)
  also have "poly_of_vec \<dots> = q * u + smult k r"
    apply (subst sylvester_sub_poly) using d_def d q_def r_def by auto
  finally have "\<dots> = poly_of_vec g"
    unfolding lincomb of_int_hom.hom_poly_of_vec by auto
  then have "poly_of_vec g = q * u + Polynomial.smult k r" by auto
  then have "poly_mod.Mp k (poly_of_vec g) =  poly_mod.Mp k (q * u + Polynomial.smult k r)" by auto
  also have "... = poly_mod.Mp k (q * u + poly_mod.Mp k (Polynomial.smult k r))"
    using poly_mod.plus_Mp(2) by auto
  also have "... =  poly_mod.Mp k (q * u)" 
     using poly_mod.plus_Mp(2) unfolding poly_mod.Mp_smult_m_0 by simp
  also have "... = poly_mod.Mp k (u * q)" by (simp add: mult.commute)
  finally show ?thesis unfolding poly_mod.dvdm_def by auto
qed

(*
  There is a typo in the textbook (page 476). The book states q' = q'' * u + r'' and 
  the correct fact is r' = q'' * u+r'' 
*)
lemma dvd_modulo_to_lincomb:
  fixes u :: "int poly" and d
  defines "d \<equiv> degree u"
  assumes d: "d < n"
      and dvd: "poly_mod.dvdm k u (poly_of_vec g)"
      and k_not0: "k\<noteq>0"
      and monic_u: "monic u"
      and dim_g: "dim_vec g = n"
      and deg_u: "degree u > 0"      
  shows "\<exists>c. lincomb_list c (factorization_lattice u (n-d) k) = g"
proof -
  interpret p: poly_mod k .
  have u_not0: "u \<noteq> 0" using monic_u by auto
  hence n[simp]: "0 < n" using d by auto
  obtain q' r' where g: "poly_of_vec g = q' * u + smult k r'"
    using p.dvdm_imp_div_mod[OF dvd] by auto
  obtain q'' r'' where r': "r' = q'' * u + r''" and deg_r'': "degree r''<degree u"
    using monic_imp_div_mod_int_poly_degree2[OF monic_u deg_u, of r'] by auto
  (*The following fact is explained in the paragraph below equation (6) in page 476 of the textbook*)
  have g1: "poly_of_vec g = (q' + smult k q'') * u + smult k r''" 
    unfolding g r'
    by (metis (no_types, lifting) combine_common_factor mult_smult_left smult_add_right)
  define q where q: "q = (q' + smult k q'')"
  define r where r: "r = r''"
  have degree_q: "q = 0 \<or> degree (q' + smult k q'') < n - d"
  proof (cases "q = 0",auto, rule degree_div_mod_smult[OF _ _ _ g1])
    show "degree (poly_of_vec g) < n" by (rule degree_poly_of_vec_less, auto simp add: dim_g)
    show "degree r'' < d" using deg_r'' unfolding d_def .
    assume "q\<noteq>0" thus "q' + smult k q'' \<noteq> 0" unfolding q .
    show "k \<noteq> 0" by fact
    show "degree u = d" using d_def by auto
  qed
  have g2: "(vec_of_poly_n (q*u) n) + (vec_of_poly_n (smult k r) n) = g" 
  proof -
    have "g = vec_of_poly_n (poly_of_vec g) n"
      by (rule vec_of_poly_n_poly_of_vec[symmetric], auto simp add: dim_g)
    also have "\<dots> = vec_of_poly_n ((q' + smult k q'') * u + smult k r'') n" 
      using g1 by auto
    also have "... = vec_of_poly_n (q * u + smult k r'') n" unfolding q by auto
    also have "... = vec_of_poly_n (q * u) n + vec_of_poly_n (smult k r'') n"
      by (rule vec_of_poly_n_add)
    finally show ?thesis unfolding r by simp
  qed
  let ?c = "\<lambda>i. if i < n - d then coeff q  (n - d - 1 - i) else coeff r (n - Suc i)"
  let ?c1 = "\<lambda>i. ?c i \<cdot>\<^sub>v factorization_lattice u (n-d) k ! i"
  show ?thesis
  proof (rule exI[of _ ?c]) 
    let ?part1 = "map (\<lambda>i. vec_of_poly_n (u * monom 1 i) n) [n-d>..0]"  
    let ?part2 = "map (\<lambda>i. vec_of_poly_n (monom k i) n) [d>..0]"
    have [simp]: "dim_vec (M.sumlist (map ?c1 [0..<n - d])) = n" 
      by (rule dim_sumlist, auto simp add: dim_factorization_lattice d_def)
    have [simp]: "dim_vec (M.sumlist (map ?c1 [n-d..<n])) = n"
      by (rule dim_sumlist, insert d, auto simp add: dim_factorization_lattice d_def)
    have [simp]: "factorization_lattice u (n-d) k ! x \<in> carrier_vec n" if x: "x < n" for x 
      using x dim_factorization_lattice_element nth_factorization_lattice[of x u "n-d"] d
      by (auto simp: d_def)
    have "[0..<length (factorization_lattice u (n-d) k)] = [0..<n]"
      using d by (simp add: d_def less_imp_le_nat)
    also have "... = [0..<n - d] @ [n-d..<n]"
      by (rule upt_minus_eq_append, auto)
    finally have list_rw: "[0..<length (factorization_lattice u (n-d) k)] = [0..<n - d] @ [n-d..<n]" . 
    have qu1: "poly_of_vec (M.sumlist (map ?c1 [0..<n - d])) = q*u" 
    proof -
      have "poly_of_vec (M.sumlist (map ?c1 [0..<n - d])) = poly_of_vec (\<Oplus>\<^bsub>V\<^esub>i\<in>{0..<n-d}. ?c1 i)" 
        by (subst sumlist_map_as_finsum, auto)
      also have "... = poly_of_vec (\<Oplus>\<^bsub>V\<^esub>i\<in>set [0..<n-d]. ?c1 i)" by auto
      also have "... = sum (\<lambda>i. poly_of_vec (?c1 i)) (set [0..<n-d])" 
        by (auto simp:poly_of_vec_finsum)
      also have "... = sum (\<lambda>i. poly_of_vec (?c1 i)) {0..<n-d}" by auto
      also have "... = q*u"
      proof -
        have deg: "degree (u * monom 1 (n - Suc (d + i))) < n" if i: "i < n - d" for i
        proof -
          let ?m="monom (1::int) (n - Suc (d + i))"
          have monom_not0: "?m \<noteq> 0" using i by auto
          have deg_m: "degree ?m = n - Suc (d + i)" by (rule degree_monom_eq, auto)
          have "degree (u * ?m) = d + (n - Suc (d + i))"
            using degree_mult_eq[OF u_not0 monom_not0] d_def deg_m by auto
          also have "... < n" using i by auto
          finally show ?thesis .
        qed
        have lattice_rw: "factorization_lattice u (n-d) k ! i = vec_of_poly_n (u * monom 1 (n - Suc (d + i))) n" 
          if i: "i< n - d" for i apply (subst nth_factorization_lattice) using i by (auto simp:d_def)
        have q_rw: "q = (\<Sum>i = 0..<n - d. (smult (coeff q (n - Suc (d + i))) (monom 1 (n - Suc (d + i)))))"          
        proof (auto simp add: poly_eq_iff coeff_sum)
          fix j 
          let ?m = "n-d-1-j"
          let ?f = "\<lambda>x. coeff q (n - Suc (d + x)) * (if n - Suc (d + x) = j then 1 else 0)"          
          have set_rw: "{0..<n-d} = insert ?m ({0..<n-d} - {?m})" using d by auto
          have sum0: "(\<Sum>x \<in> {0..<n-d} - {?m}. ?f x) = 0" by (rule sum.neutral, auto)
          have "(\<Sum>x = 0..<n - d. ?f x) = (\<Sum>x \<in> insert ?m ({0..<n-d} - {?m}). ?f x)" 
            using set_rw by presburger
          also have "... = ?f ?m + (\<Sum>x \<in> {0..<n-d} - {?m}. ?f x)" by (rule sum.insert, auto)
          also have "... = ?f ?m" unfolding sum0 by auto
          also have "... = coeff q j"
          proof (cases "j < n - d")
            case True
            then show ?thesis by auto
          next
            case False
            have "j>degree q" using degree_q q False d by auto
            then show ?thesis using coeff_eq_0 by auto
          qed            
          finally show "coeff q j = (\<Sum>i = 0..<n - d. coeff q (n - Suc (d + i)) 
            * (if n - Suc (d + i) = j then 1 else 0))" ..
        qed
        have "sum (\<lambda>i. poly_of_vec (?c1 i)) {0..<n-d} 
        = (\<Sum>i = 0..<n - d. poly_of_vec (coeff q (n - Suc (d + i)) \<cdot>\<^sub>v factorization_lattice u (n-d) k ! i))"
          by (rule sum.cong, auto)
        also have "...  = (\<Sum>i = 0..<n - d. (poly_of_vec (coeff q (n - Suc (d + i)) 
          \<cdot>\<^sub>v (vec_of_poly_n (u * monom 1 (n - Suc (d + i))) n))))"
          by (rule sum.cong, auto simp add: lattice_rw)
        also have "... = (\<Sum>i = 0..<n - d. smult (coeff q (n - Suc (d + i))) (u * monom 1 (n - Suc (d + i))))"
          by (rule sum.cong, auto simp add: poly_of_vec_scalar_mult[OF deg])
        also have "... = (\<Sum>i = 0..<n - d. u*(smult (coeff q (n - Suc (d + i))) (monom 1 (n - Suc (d + i)))))" 
          by auto
        also have "... = u *(\<Sum>i = 0..<n - d. (smult (coeff q (n - Suc (d + i))) (monom 1 (n - Suc (d + i)))))" 
          by (rule sum_distrib_left[symmetric])
        also have "... = u * q" using q_rw by auto
        also have "... = q*u" by auto
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed
    have qu: "M.sumlist (map ?c1 [0..<n - d]) = vec_of_poly_n (q*u) n"
    proof -
      have "vec_of_poly_n (q*u) n = vec_of_poly_n (poly_of_vec (M.sumlist (map ?c1 [0..<n - d]))) n" 
        using qu1 by auto
      also have "vec_of_poly_n (poly_of_vec (M.sumlist (map ?c1 [0..<n - d]))) n 
        = M.sumlist (map ?c1 [0..<n - d])"
        by (rule vec_of_poly_n_poly_of_vec, auto)
      finally show ?thesis ..
    qed
    have rm1: "poly_of_vec (M.sumlist (map ?c1 [n-d..<n])) = smult k r"
    proof -      
      have "poly_of_vec (M.sumlist (map ?c1 [n-d..<n])) = poly_of_vec (\<Oplus>\<^bsub>V\<^esub>i\<in>{n-d..<n}. ?c1 i)" 
        by (subst sumlist_map_as_finsum, auto)
      also have "... = poly_of_vec (\<Oplus>\<^bsub>V\<^esub>i\<in>set [n-d..<n]. ?c1 i)" by auto
      also have "... = sum (\<lambda>i. poly_of_vec (?c1 i)) {n-d..<n}" 
        by (auto simp: poly_of_vec_finsum)
      also have "... = smult k r"
      proof -
        have deg: "degree (monom k (n - Suc i)) < n" if i: "n-d\<le>i" and i2: "i<n" for i 
          using degree_monom_le i i2
          by (simp add: degree_monom_eq k_not0)
        have lattice_rw: "factorization_lattice u (n-d) k ! i = vec_of_poly_n (monom k (n - Suc i)) n" 
          if i: "n - d \<le> i" and i2: "i<n" for i
          using i2 i d d_def
          by (subst nth_factorization_lattice, auto)
        have r_rw: "r = (\<Sum>i \<in> {n-d..<n}. (monom (coeff r (n - Suc i)) (n - Suc i)))"
        proof (auto simp add: poly_eq_iff coeff_sum)
          fix j
          show "coeff r j = (\<Sum>i = n - d..<n. if n - Suc i = j then coeff r (n - Suc i) else 0)"
          proof (cases "j<d")
            case True
            have j_eq: "n - Suc (n - 1 - j) = j" using d True by auto
            let ?i = "n-1-j"
            let ?f ="\<lambda>i. if n - Suc i = j then coeff r (n - Suc i) else 0"
            have sum0: "sum ?f ({n-d..<n} - {?i}) = 0" by (rule sum.neutral, auto)
            have "{n-d..<n} = insert ?i ({n-d..<n} - {?i})" using True by auto
            hence "sum ?f {n - d..<n} = sum ?f (insert ?i ({n-d..<n} - {?i}))" by auto
            also have "... = ?f ?i + sum ?f ({n-d..<n} - {?i})"
              by (rule sum.insert, auto)
            also have "... = coeff r j" unfolding sum0 j_eq by simp
            finally show ?thesis ..
          next
            case False
            hence "(\<Sum>i = n - d..<n. if n - Suc i = j then coeff r (n - Suc i) else 0) = 0"
              by (intro sum.neutral ballI, insert False, simp, linarith) 
            also have "... = coeff r j" 
              by (rule coeff_eq_0[symmetric], insert False deg_r'' r d_def, auto)
            finally show ?thesis ..
          qed 
        qed
        have "sum (\<lambda>i. poly_of_vec (?c1 i)) {n-d..<n} 
        = (\<Sum>i \<in> {n-d..<n}. poly_of_vec (coeff r (n - Suc i) \<cdot>\<^sub>v factorization_lattice u (n-d) k ! i))"
          by (rule sum.cong, auto)
        also have "...  = (\<Sum>i \<in> {n-d..<n}. (poly_of_vec (coeff r (n - Suc i) 
          \<cdot>\<^sub>v vec_of_poly_n (monom k (n - Suc i)) n)))"
          by (rule sum.cong, auto simp add: lattice_rw)
        also have "... = (\<Sum>i \<in> {n-d..<n}. smult (coeff r (n - Suc i)) (monom k (n - Suc i)))"
          by (rule sum.cong, auto simp add: poly_of_vec_scalar_mult[OF deg])
        also have "... = (\<Sum>i \<in> {n-d..<n}. smult k (monom (coeff r (n - Suc i)) (n - Suc i)))"
          by (rule sum.cong, auto simp add: smult_monom smult_sum2)
        also have "... = smult k (\<Sum>i \<in> {n-d..<n}. (monom (coeff r (n - Suc i)) (n - Suc i)))"
          by (simp add: smult_sum2)
        also have "... = smult k r" using r_rw by auto
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed
    have rm: "(M.sumlist (map ?c1 [n-d..<n])) = vec_of_poly_n (smult k r) n"
    proof -
      have "vec_of_poly_n (smult k r) n 
        = vec_of_poly_n (poly_of_vec (M.sumlist (map ?c1 [n-d..<n]))) n" 
        using rm1 by auto
      also have "vec_of_poly_n (poly_of_vec (M.sumlist (map ?c1 [n-d..<n]))) n 
        = M.sumlist (map ?c1 [n-d..<n])"
        by (rule vec_of_poly_n_poly_of_vec, auto)
      finally show ?thesis ..        
    qed
    have "lincomb_list ?c (factorization_lattice u (n-d) k) = M.sumlist (map ?c1 ([0..<n - d] @ [n-d..<n]))"
      unfolding lincomb_list_def list_rw by auto
    also have "... = M.sumlist (map ?c1 [0..<n - d] @ map ?c1 [n-d..<n])" by auto
    also have "... = M.sumlist (map ?c1 [0..<n - d]) + M.sumlist (map ?c1 [n-d..<n])" 
      using d by (auto simp add: d_def nth_factorization_lattice intro!: M.sumlist_append)
    also have "... = vec_of_poly_n (q*u) n + vec_of_poly_n (smult k r) n" 
      unfolding qu rm by auto
    also have "... = g" using g2 by simp
    finally show "lincomb_list ?c (factorization_lattice u (n-d) k) = g" .
  qed
qed

text \<open>The factorization lattice precisely characterises the polynomials of a certain
  degree which divide $u$ modulo $M$.\<close>

lemma factorization_lattice: fixes M assumes  
  deg_u: "degree u \<noteq> 0"  and M: "M \<noteq> 0" 
shows "degree u \<le> n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> f \<in> poly_of_vec ` lattice_of (factorization_lattice u (n - degree u) M) \<Longrightarrow> 
  degree f < n \<and> poly_mod.dvdm M u f" 
  "monic u \<Longrightarrow> degree u < n \<Longrightarrow> 
  degree f < n \<Longrightarrow> poly_mod.dvdm M u f \<Longrightarrow> f \<in> poly_of_vec ` lattice_of (factorization_lattice u (n - degree u) M)" 
proof -
  from deg_u have deg_u: "degree u > 0" by auto
  let ?L = "factorization_lattice u (n - degree u) M" 
  {
    assume deg: "degree f < n" and dvd: "poly_mod.dvdm M u f" and mon: "monic u" 
      and deg_u_lt: "degree u < n"
    define fv where "fv = vec n (\<lambda> i. (coeff f (n - Suc i)))" 
    have f: "f = poly_of_vec fv" unfolding fv_def poly_of_vec_def Let_def using deg 
      by (auto intro!: poly_eqI coeff_eq_0 simp: coeff_sum) 
    have dim_fv: "dim_vec fv = n" unfolding fv_def by simp
    from dvd_modulo_to_lincomb[OF deg_u_lt _ M mon _ deg_u(1), of fv, folded f, OF dvd dim_fv]
    obtain c where gv: "fv = lincomb_list c ?L" by auto
    have "fv \<in> lattice_of ?L" unfolding gv lattice_is_span by (auto simp: in_span_listI)
    thus "f \<in> poly_of_vec ` lattice_of ?L" unfolding f by auto
  }
  moreover
  {
    assume "f \<in> poly_of_vec ` lattice_of ?L" and deg_u: "degree u \<le> n" and n: "n \<noteq> 0" 
    then obtain fv where f: "f = poly_of_vec fv" and fv: "fv \<in> lattice_of ?L" by auto
    from in_span_listE[OF fv[unfolded lattice_is_span]] 
    obtain c where fv: "fv = lincomb_list c ?L" by auto    
    from lincomb_to_dvd_modulo[OF _ fv[symmetric]] deg_u f
    have dvd: "poly_mod.dvdm M u f" by auto
    have "set ?L \<subseteq> carrier_vec n" unfolding factorization_lattice_def using deg_u by auto
    hence "fv \<in> carrier_vec n" unfolding fv by (metis lincomb_list_carrier)
    hence "degree f < n" unfolding f using degree_poly_of_vec_less[of fv n] using n by auto
    with dvd show "degree f < n \<and> poly_mod.dvdm M u f" by auto
  }
qed
end

subsection \<open>Soundness of the LLL factorization algorithm\<close>

lemma LLL_short_polynomial: assumes deg_u_0: "degree u \<noteq> 0" and deg_le: "degree u \<le> n" 
  and pl1: "pl > 1" 
  and monic: "monic u" 
shows "degree (LLL_short_polynomial pl n u) < n" 
  and "LLL_short_polynomial pl n u \<noteq> 0"
  and "poly_mod.dvdm pl u (LLL_short_polynomial pl n u)" 
  and "degree u < n \<Longrightarrow> f \<noteq> 0 \<Longrightarrow>
    poly_mod.dvdm pl u f \<Longrightarrow> degree f < n \<Longrightarrow> \<parallel>LLL_short_polynomial pl n u\<parallel>\<^sup>2 \<le> 2 ^ (n - 1) * \<parallel>f\<parallel>\<^sup>2" 
proof -
  interpret poly_mod_2 pl 
    by (unfold_locales, insert pl1, auto)
  from pl1 have pl0: "pl \<noteq> 0" by auto
  let ?d = "degree u"
  let ?u = "Mp u" 
  let ?iu = "inv_Mp ?u" 
  from Mp_inv_Mp_id[of ?u] have "?iu =m ?u" .
  also have "\<dots> =m u" by simp
  finally have iu_u: "?iu =m u" by simp
  have degu[simp]: "degree ?u = degree u" using monic by simp
  have mon: "monic ?u" using monic by (rule monic_Mp)
  have "degree ?iu = degree ?u" unfolding inv_Mp_def
    by (rule degree_map_poly, unfold mon, insert mon pl1, auto simp: inv_M_def)
  with degu have deg_iu: "degree ?iu = degree u" by simp
  have mon_iu: "monic ?iu" unfolding deg_iu unfolding inv_Mp_def Mp_def inv_M_def M_def
    by (insert pl1, auto simp: coeff_map_poly monic)
  let ?L = "factorization_lattice ?iu (n - ?d) pl" 
  let ?sv = "short_vector_hybrid 2 ?L" 
  from deg_u_0 deg_le have n: "n \<noteq> 0" by auto
  from deg_u_0 have u0: "u \<noteq> 0" by auto
  have id: "LLL_short_polynomial pl n u = poly_of_vec ?sv" 
    unfolding LLL_short_polynomial_def by blast
  have id': "\<parallel>?sv\<parallel>\<^sup>2 = \<parallel>LLL_short_polynomial pl n u\<parallel>\<^sup>2" unfolding id by simp
  interpret vec_module "TYPE(int)" n.
  interpret L: LLL n n "?L" 2 .
  from deg_le deg_iu have deg_iu_le: "degree ?iu \<le> n" by simp
  have len: "length ?L = n" 
    unfolding factorization_lattice_def using deg_le deg_iu by auto
  from deg_u_0 deg_iu have deg_iu0: "degree ?iu \<noteq> 0" by auto
  hence iu0: "?iu \<noteq> 0" by auto
  from L.lin_indpt_list_factorization_lattice[OF refl deg_iu_le iu0 pl0]
  have *: "4/3 \<le> (2 :: rat)" "L.gs.lin_indpt_list (L.RAT ?L)" by (auto simp: deg_iu)
  interpret L: LLL_with_assms n n ?L 2
    by (unfold_locales, insert *, auto simp: deg_iu deg_le)
  note short = L.short_vector_hybrid[OF refl n, unfolded id' L.L_def]
  from short(2) have mem: "LLL_short_polynomial pl n u \<in> poly_of_vec ` lattice_of ?L" 
    unfolding id by auto
  note fact = L.factorization_lattice(1)[OF deg_iu0 pl0 deg_iu_le n, unfolded deg_iu, OF mem]
  show "degree (LLL_short_polynomial pl n u) < n" using fact by auto
  from fact have "?iu dvdm (LLL_short_polynomial pl n u)" by auto
  then obtain h where "LLL_short_polynomial pl n u =m ?iu * h" unfolding dvdm_def by auto
  also have "?iu * h =m Mp ?iu * h" unfolding mult_Mp by simp
  also have "Mp ?iu * h =m u * h" unfolding iu_u unfolding mult_Mp by simp
  finally show "u dvdm (LLL_short_polynomial pl n u)" unfolding dvdm_def by auto
  from short have sv1: "?sv \<in> carrier_vec n" by auto  
  from short have "?sv \<noteq> 0\<^sub>v j" for j by auto
  thus "LLL_short_polynomial pl n u \<noteq> 0" unfolding id by simp
  assume degu: "degree u < n" and dvd: "u dvdm f" 
    and degf: "degree f < n" and f0: "f \<noteq> 0" 
  from dvd obtain h where "f =m u * h" unfolding dvdm_def by auto
  also have "u * h =m Mp u * h" unfolding mult_Mp by simp
  also have "Mp u * h =m Mp ?iu * h" unfolding iu_u by simp
  also have "Mp ?iu * h =m ?iu * h" unfolding mult_Mp by simp
  finally have dvd: "?iu dvdm f" unfolding dvdm_def by auto
  from degu deg_iu have deg_iun: "degree ?iu < n" by auto
  from L.factorization_lattice(2)[OF deg_iu0 pl0 mon_iu deg_iun degf dvd]
  have "f \<in> poly_of_vec ` lattice_of ?L" using deg_iu by auto 
  then obtain fv where f: "f = poly_of_vec fv" and fv: "fv \<in> lattice_of ?L" by auto
  have norm: "\<parallel>fv\<parallel>\<^sup>2 = \<parallel>f\<parallel>\<^sup>2" unfolding f by simp
  have fv0: "fv \<noteq> 0\<^sub>v n" using f0 unfolding f by auto
  with fv have fvL: "fv \<in> lattice_of ?L - {0\<^sub>v n}" by auto
  from short(3)[OF this, unfolded norm]
  have "rat_of_int \<parallel>LLL_short_polynomial pl n u\<parallel>\<^sup>2 \<le> rat_of_int (2 ^ (n - 1) * \<parallel>f\<parallel>\<^sup>2)" by simp
  thus "\<parallel>LLL_short_polynomial pl n u\<parallel>\<^sup>2 \<le> 2 ^ (n - 1) * \<parallel>f\<parallel>\<^sup>2" by linarith
qed

context LLL_implementation
begin

lemma LLL_reconstruction: assumes "LLL_reconstruction f us = fs"
  and "degree f \<noteq> 0"
  and "poly_mod.unique_factorization_m pl f (lead_coeff f, mset us)"
  and "f dvd F" 
  and "\<And> ui. ui \<in> set us \<Longrightarrow> poly_mod.Mp pl ui = ui" 
  and F0: "F \<noteq> 0" 
  and cop: "coprime (lead_coeff F) p" 
  and sf: "poly_mod.square_free_m p F" 
  and pl1: "pl > 1" 
  and plp: "pl = p^l" 
  and p: "prime p" 
  and large: "2^(5 * (degree F - 1) * (degree F - 1)) * \<parallel>F\<parallel>\<^sup>2^(2 * (degree F - 1)) < pl\<^sup>2"
shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)" 
proof -
  interpret p: poly_mod_prime p by (standard, rule p)
  interpret pl: poly_mod_2 "pl" by (standard, rule pl1)
  from pl1 plp have l0: "l \<noteq> 0" by (cases l, auto)
  show ?thesis using assms(1-5)
  proof (induct f us arbitrary: fs rule: LLL_reconstruction.induct)
    case (1 f us fs)
    define u where "u = choose_u us" 
    define g where "g = LLL_short_polynomial pl (degree f) u" 
    define k where "k = gcd f g" 
    note res = 1(3)
    note degf = 1(4)
    note uf = 1(5)
    note fF = 1(6)
    note norm = 1(7)
    note to_fact = pl.unique_factorization_m_imp_factorization
    note fact = to_fact[OF uf]
    have mon_gs: "ui \<in> set us \<Longrightarrow> monic ui" for ui using norm fact
      unfolding pl.factorization_m_def by auto
    from p.coprime_lead_coeff_factor[OF p.prime] fF cop 
    have cop: "coprime (lead_coeff f) p" unfolding dvd_def by blast
    have plf0: "pl.Mp f \<noteq> 0" 
      using fact pl.factorization_m_lead_coeff pl.unique_factorization_m_zero uf by fastforce
    have "degree f = pl.degree_m f" 
      by (rule sym, rule poly_mod.degree_m_eq[OF _ pl.m1], 
          insert cop p, simp add: l0 p.coprime_exp_mod plp)
    also have "\<dots> =  sum_mset (image_mset pl.degree_m (mset us))"
      unfolding pl.factorization_m_degree[OF fact plf0] ..
    also have "\<dots> = sum_list (map pl.degree_m us)" 
      unfolding sum_mset_sum_list[symmetric] by auto
    also have "\<dots> = sum_list (map degree us)" 
      by (rule arg_cong[OF map_cong, OF refl], rule pl.monic_degree_m, insert mon_gs, auto)
    finally have degf_gs: "degree f = sum_list (map degree us)" by auto
    hence gs: "us \<noteq> []" using degf by (cases us, auto)
    from choose_u_member[OF gs] have u_gs: "u \<in> set us" unfolding u_def by auto
    from fact u_gs have irred: "pl.irreducible\<^sub>d_m u" unfolding pl.factorization_m_def by auto
    hence deg_u: "degree u \<noteq> 0" unfolding pl.irreducible\<^sub>d_m_def norm[OF u_gs] by auto
    have deg_uf: "degree u \<le> degree f" unfolding degf_gs using split_list[OF u_gs] by auto
    from mon_gs[OF u_gs] have mon_u: "monic u" and u0: "u \<noteq> 0" by auto
    have f0: "f \<noteq> 0" using degf by auto
    from norm have norm': "image_mset pl.Mp (mset us) = mset us" by (induct us, auto)
    have pl0: "pl \<noteq> 0" using pl1 by auto
    note short_main = LLL_short_polynomial[OF deg_u deg_uf pl1 mon_u]
    from short_main(1-2)[folded g_def] 
    have "degree k < degree f" unfolding k_def
      by (smt Suc_leI Suc_less_eq degree_gcd1 gcd.commute le_imp_less_Suc le_trans) 
    hence deg_fk: "(degree k = 0 \<or> degree f \<le> degree k) = (degree k = 0)" by auto
    note res = res[unfolded LLL_reconstruction.simps[of f us] Let_def, folded u_def, 
        folded g_def, folded k_def, unfolded deg_fk]
    show ?case
    proof (cases "degree k = 0")
      case True
      with res have fs: "fs = [f]" by auto
      from sf fF have sf: "p.square_free_m f" 
        using p.square_free_m_factor(1)[of f] unfolding dvd_def by auto
      have irr: "irreducible\<^sub>d f" 
      proof (rule ccontr)
        assume "\<not> irreducible\<^sub>d f" 
        from reducible\<^sub>dE[OF this] degf obtain f1 f2 where 
          f: "f = f1 * f2" and
          deg12: "degree f1 \<noteq> 0" "degree f2 \<noteq> 0" "degree f1 < degree f" "degree f2 < degree f" 
          by (simp, metis)
        from pl.unique_factorization_m_factor[OF p uf[unfolded f], folded f, OF cop sf l0 plp]
        obtain us1 us2 where 
          uf12: "pl.unique_factorization_m f1 (lead_coeff f1, us1)"
            "pl.unique_factorization_m f2 (lead_coeff f2, us2)"
          and gs: "mset us = us1 + us2"
          and norm12: "image_mset pl.Mp us2 = us2" "image_mset pl.Mp us1 = us1"
          unfolding pl.Mf_def norm' split by (auto simp: pl.Mf_def)
        note norm_u = norm[OF u_gs]
        from u_gs have u_gs': "u \<in># mset us" by auto
        with pl.factorization_m_mem_dvdm[OF fact, of u] 
        have u_f: "pl.dvdm u f" by auto
        from u_gs'[unfolded gs] have "u \<in># us1 \<or> u \<in># us2" by auto
        with pl.factorization_m_mem_dvdm[OF to_fact[OF uf12(1)], of u] 
             pl.factorization_m_mem_dvdm[OF to_fact[OF uf12(2)], of u] 
        have "pl.dvdm u f1 \<or> pl.dvdm u f2" unfolding norm12 norm_u by auto
        from this have "\<exists> f1 f2. f = f1 * f2 \<and> 
          degree f1 \<noteq> 0 \<and> degree f2 \<noteq> 0 \<and> degree f1 < degree f \<and> degree f2 < degree f \<and> 
          pl.dvdm u f1" 
        proof 
          assume "pl.dvdm u f1" thus ?thesis using f deg12 by auto
        next
          from f have f: "f = f2 * f1" by auto
          assume "pl.dvdm u f2" thus ?thesis using f deg12 by auto
        qed
        then obtain f1 f2 where prod: "f = f1 * f2" 
          and deg: "degree f1 \<noteq> 0" "degree f2 \<noteq> 0" "degree f1 < degree f" "degree f2 < degree f" 
          and uf1: "pl.dvdm u f1" by auto
        from pl.unique_factorization_m_factor[OF p uf[unfolded prod], folded prod, OF cop sf l0 plp]
        obtain us1 where fact_f1: "pl.unique_factorization_m f1 (lead_coeff f1, us1)" by auto
        have plf1: "pl.Mp f1 \<noteq> 0" 
          using to_fact[OF fact_f1] pl.factorization_m_lead_coeff 
            pl.unique_factorization_m_zero fact_f1 by fastforce
        have "degree u \<le> degree f1"
          by (rule pl.dvdm_degree[OF mon_u uf1 plf1])
        with deg have deg_uf: "degree u < degree f" by auto
        have pl0: "pl \<noteq> 0" using pl.m1 plp by linarith
        let ?n = "degree f"
        let ?n1 = "degree f1" 
        let ?d = "degree u" 
        from prod fF have f1F: "f1 dvd F" unfolding dvd_def by auto
        from deg_uf have deg_uf': "?d \<le> ?n" by auto
        from deg have f1_0: "f1 \<noteq> 0" by auto
        have ug: "pl.dvdm u g" using short_main(3) unfolding g_def .
        have g0: "g \<noteq> 0" using short_main(2) unfolding g_def .
        have deg_gf: "degree g < degree f" using short_main(1) unfolding g_def .
        let ?N = "degree F" 
        from fF prod have f1F: "f1 dvd F" unfolding dvd_def by auto
        have "\<parallel>g\<parallel>\<^sup>2 \<le> 2 ^ (?n - 1) * \<parallel>f1\<parallel>\<^sup>2" unfolding g_def
          by (rule short_main(4)[OF deg_uf _ uf1], insert deg, auto)
        also have "\<dots> \<le> 2 ^ (?n - 1) * (2 ^ (2 * degree f1) * \<parallel>F\<parallel>\<^sup>2)" 
          by (rule mult_left_mono[OF sq_norm_factor_bound[OF f1F F0]], simp)
        also have "\<dots> = 2 ^ ((?n - 1) + 2 * degree f1) * \<parallel>F\<parallel>\<^sup>2" 
          unfolding power_add by simp
        also have "\<dots> \<le> 2 ^ ((?n - 1) + 2 * (?n - 1)) * \<parallel>F\<parallel>\<^sup>2" 
          by (rule mult_right_mono, insert deg(3), auto)
        also have "\<dots> = 2 ^ (3 * (?n - 1)) * \<parallel>F\<parallel>\<^sup>2" by simp
        finally have ineq_g: "\<parallel>g\<parallel>\<^sup>2 \<le> 2 ^ (3 * (?n - 1)) * \<parallel>F\<parallel>\<^sup>2" .
        from power_mono[OF this, of ?n1]
        have ineq1: "\<parallel>g\<parallel>\<^sup>2 ^ ?n1 \<le> (2 ^ (3 * (?n - 1)) * \<parallel>F\<parallel>\<^sup>2)^?n1" by auto
        from F0 have normF: "\<parallel>F\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of F] by presburger
        from g0 have normg: "\<parallel>g\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of g] by presburger
        from f0 have normf: "\<parallel>f\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of f] by presburger
        from f1_0 have normf1: "\<parallel>f1\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of f1] by presburger
        from power_mono[OF sq_norm_factor_bound[OF f1F F0], of "degree g"]
        have ineq2: "\<parallel>f1\<parallel>\<^sup>2 ^ degree g \<le> (2 ^ (2 * ?n1) * \<parallel>F\<parallel>\<^sup>2) ^ degree g" by auto
        also have "\<dots> \<le> (2 ^ (2 * ?n1) * \<parallel>F\<parallel>\<^sup>2) ^ (?n - 1)"
          by (rule pow_mono_exp, insert deg_gf normF, auto)          
        finally have ineq2: "\<parallel>f1\<parallel>\<^sup>2 ^ degree g \<le> (2 ^ (2 * ?n1) * \<parallel>F\<parallel>\<^sup>2) ^ (?n - 1)" .
        have nN: "?n \<le> ?N" using fF F0 by (metis dvd_imp_degree_le)
        from deg nN have n1N: "?n1 \<le> ?N - 1" by auto
        have "\<parallel>f1\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ ?n1 \<le> 
          (2 ^ (2 * ?n1) * \<parallel>F\<parallel>\<^sup>2) ^ (?n - 1) * (2 ^ (3 * (?n - 1)) * \<parallel>F\<parallel>\<^sup>2)^?n1" 
          by (rule mult_mono[OF ineq2 ineq1], force+)
        also have "\<dots> \<le> (2 ^ (2 * (?N - 1)) * \<parallel>F\<parallel>\<^sup>2) ^ (?N - 1) *
          (2 ^ (3 * (?N - 1)) * \<parallel>F\<parallel>\<^sup>2) ^ (?N - 1)"
          by (rule mult_mono[OF power_both_mono[OF _ _ mult_mono] 
          power_both_mono], insert normF n1N nN, auto intro: power_both_mono mult_mono) 
        also have "\<dots> = 2 ^ (2 * (?N -1) * (?N - 1) + 3 * (?N - 1) * (?N - 1)) 
            * (\<parallel>F\<parallel>\<^sup>2)^((?N - 1) + (?N - 1))" 
          unfolding power_mult_distrib power_add power_mult by simp
        also have "2 * (?N - 1) * (?N - 1) + 3 * (?N - 1) * (?N - 1) = 5 * (?N - 1) * (?N - 1)" by simp
        also have "?N - 1 + (?N - 1) = 2 * (?N - 1)" by simp
        also have "2^(5 * (?N - 1) * (?N - 1)) * \<parallel>F\<parallel>\<^sup>2^(2 * (?N - 1)) < pl^2" by (rule large)
        finally have large: "\<parallel>f1\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree f1 < pl\<^sup>2" .
        have deg_ug: "degree u \<le> degree g" 
        proof (rule pl.dvdm_degree[OF mon_u ug], standard)
          assume "pl.Mp g = 0" 
          from arg_cong[OF this, of "\<lambda> p. coeff p (degree g)"]
          have "pl.M (coeff g (degree g)) = 0" by (auto simp: pl.Mp_def coeff_map_poly)
          from this[unfolded pl.M_def] obtain c where lg: "lead_coeff g = pl * c" by auto
          with g0 have c0: "c \<noteq> 0" by auto
          hence "pl^2 \<le> (lead_coeff g)^2" unfolding lg abs_le_square_iff[symmetric]
            by (rule aux_abs_int)
          also have "\<dots> \<le> \<parallel>g\<parallel>\<^sup>2 ^ 1" using coeff_le_sq_norm[of g] by auto 
          also have "\<dots> \<le> \<parallel>g\<parallel>\<^sup>2 ^ degree f1" 
            by (rule pow_mono_exp, insert deg normg, auto)
          also have "\<dots> = 1 * \<dots>" by simp
          also have "\<dots> \<le> \<parallel>f1\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree f1" 
            by (rule mult_right_mono, insert normf1, auto)
          also have "\<dots> < pl\<^sup>2" by (rule large) 
          finally show False by auto
        qed
        from deg deg_u deg_ug have "degree f1 > 0" "degree g > 0" by auto
        from common_factor_via_short[OF this mon_u _ uf1 ug large] deg_u pl.m1
        have "0 < degree (gcd f1 g)" by auto
        moreover from True[unfolded k_def] have "degree (gcd f g) = 0" .
        moreover have dvd: "gcd f1 g dvd gcd f g" using f0 unfolding prod by simp
        ultimately show False using divides_degree[OF dvd] using f0 by simp 
      qed
      show ?thesis unfolding fs using irr by auto
    next
      case False
      define f1 where "f1 = f div k" 
      have f: "f = f1 * k" unfolding f1_def k_def by auto
      with arg_cong[OF this, of degree] f0 have deg_f1k: "degree f = degree f1 + degree k" 
        by (auto simp: degree_mult_eq)
      from f fF have dvd: "f1 dvd F" "k dvd F" unfolding dvd_def by auto
      obtain gs1 gs2 where part: "List.partition (\<lambda>gi. p.dvdm gi f1) us = (gs1, gs2)" by force  
      note IH = 1(1-2)[OF refl u_def g_def k_def refl, unfolded deg_fk, OF False f1_def part[symmetric] refl]
      obtain fs1 where fs1: "LLL_reconstruction f1 gs1 = fs1" by auto
      obtain fs2 where fs2: "LLL_reconstruction k gs2 = fs2" by auto
      from False res[folded f1_def, unfolded part split fs1 fs2] 
      have fs: "fs = fs1 @ fs2" by auto
      from short_main(1)
      have deg_gf: "degree g < degree f" unfolding g_def by auto
      from short_main(2) 
      have g0: "g \<noteq> 0" unfolding g_def by auto
      have deg_kg: "degree k \<le> degree g" unfolding k_def gcd.commute[of f g]
        by (rule degree_gcd1[OF g0])
      from deg_gf deg_kg have deg_kf: "degree k < degree f" by auto
      with deg_f1k have deg_f1: "degree f1 \<noteq> 0" by auto
      have sf_f: "p.square_free_m f" using sf fF p.square_free_m_factor unfolding dvd_def by blast
      from p.unique_factorization_m_factor_partition[OF l0 uf[unfolded plp] f cop sf_f part]
      have uf: "pl.unique_factorization_m f1 (lead_coeff f1, mset gs1)"  
          "pl.unique_factorization_m k (lead_coeff k, mset gs2)" by (auto simp: plp)
      have "set us = set gs1 \<union> set gs2" using part by auto
      with norm have norm_12: "gi \<in> set gs1 \<or> gi \<in> set gs2 \<Longrightarrow> pl.Mp gi = gi" for gi by auto
      note IH1 = IH(1)[OF fs1 deg_f1 uf(1) dvd(1) norm_12]
      note IH2 = IH(2)[OF fs2 False uf(2) dvd(2) norm_12]
      show ?thesis unfolding fs f using IH1 IH2 by auto
    qed
  qed
qed

lemma LLL_many_reconstruction: assumes "LLL_many_reconstruction f us = fs"
  and "degree f \<noteq> 0"
  and "poly_mod.unique_factorization_m pl f (lead_coeff f, mset us)"
  and "f dvd F" 
  and "\<And> ui. ui \<in> set us \<Longrightarrow> poly_mod.Mp pl ui = ui" 
  and F0: "F \<noteq> 0" 
  and cop: "coprime (lead_coeff F) p" 
  and sf: "poly_mod.square_free_m p F" 
  and pl1: "pl > 1" 
  and plp: "pl = p^l" 
  and p: "prime p" 
  and large: "2^(5 * (degree F div 2) * (degree F div 2)) * \<parallel>F\<parallel>\<^sup>2^(2 * (degree F div 2)) < pl\<^sup>2"
shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)" 
proof -
  interpret p: poly_mod_prime p by (standard, rule p)
  interpret pl: poly_mod_2 "pl" by (standard, rule pl1)
  from pl1 plp have l0: "l \<noteq> 0" by (cases l, auto)
  show ?thesis using assms(1-5)
  proof (induct f us arbitrary: fs rule: LLL_many_reconstruction.induct)
    case (1 f us fs)
    note res = 1(3)
    note degf = 1(4)
    note uf = 1(5)
    note fF = 1(6)
    note norm = 1(7)
    note to_fact = pl.unique_factorization_m_imp_factorization
    note fact = to_fact[OF uf]
    have mon_gs: "ui \<in> set us \<Longrightarrow> monic ui" for ui using norm fact
      unfolding pl.factorization_m_def by auto
    from p.coprime_lead_coeff_factor[OF p.prime] fF cop 
    have cop: "coprime (lead_coeff f) p" unfolding dvd_def by blast
    have plf0: "pl.Mp f \<noteq> 0" 
      using fact pl.factorization_m_lead_coeff pl.unique_factorization_m_zero uf by fastforce
    have "degree f = pl.degree_m f" 
      by (rule sym, rule poly_mod.degree_m_eq[OF _ pl.m1], 
          insert cop p, simp add: l0 p.coprime_exp_mod plp)
    also have "\<dots> =  sum_mset (image_mset pl.degree_m (mset us))"
      unfolding pl.factorization_m_degree[OF fact plf0] ..
    also have "\<dots> = sum_list (map pl.degree_m us)" 
      unfolding sum_mset_sum_list[symmetric] by auto
    also have "\<dots> = sum_list (map degree us)" 
      by (rule arg_cong[OF map_cong, OF refl], rule pl.monic_degree_m, insert mon_gs, auto)
    finally have degf_gs: "degree f = sum_list (map degree us)" by auto
    hence gs: "us \<noteq> []" using degf by (cases us, auto)
    from 1(4) have f0: "f \<noteq> 0" and df0: "degree f \<noteq> 0" by auto
    from norm have norm': "image_mset pl.Mp (mset us) = mset us" by (induct us, auto)
    have pl0: "pl \<noteq> 0" using pl1 by auto

    let ?D2 = "degree F div 2" 
    let ?d2 = "degree f div 2" 
    define gg where "gg = LLL_short_polynomial pl (Suc ?d2)" 
    let ?us = "filter (\<lambda>u. degree u \<le> ?d2) us" 
    note res = res[unfolded LLL_many_reconstruction.simps[of f us], unfolded Let_def,
        folded gg_def]
    let ?f2_opt = "find_map_filter (\<lambda>u. gcd f (gg u)) 
      (\<lambda>f2. 0 < degree f2 \<and> degree f2 < degree f) ?us" 
    show ?case
    proof (cases ?f2_opt)
      case (Some f2)
      from find_map_filter_Some[OF this]
      obtain g where deg_f2: "degree f2 \<noteq> 0" "degree f2 < degree f"
        and dvd: "f2 dvd f" and gcd: "f2 = gcd f g" by auto
      note res = res[unfolded Some option.simps]

      define f1 where "f1 = f div f2" 
      have f: "f = f1 * f2" unfolding f1_def using dvd by auto
      with arg_cong[OF this, of degree] f0 have deg_sum: "degree f = degree f1 + degree f2" 
        by (auto simp: degree_mult_eq)
      with deg_f2 have deg_f1: "degree f1 \<noteq> 0" "degree f1 < degree f" by auto
      from f fF have dvd: "f1 dvd F" "f2 dvd F" unfolding dvd_def by auto
      obtain gs1 gs2 where part: "List.partition (\<lambda>gi. p.dvdm gi f1) us = (gs1, gs2)" by force  
      note IH = 1(1-2)[OF refl refl refl, unfolded Let_def, folded gg_def, OF Some f1_def part[symmetric] refl] 
      obtain fs1 where fs1: "LLL_many_reconstruction f1 gs1 = fs1" by blast
      obtain fs2 where fs2: "LLL_many_reconstruction f2 gs2 = fs2" by blast
      from res[folded f1_def, unfolded part split fs1 fs2] 
      have fs: "fs = fs1 @ fs2" by auto
      have sf_f: "p.square_free_m f" using sf fF p.square_free_m_factor unfolding dvd_def by blast
      from p.unique_factorization_m_factor_partition[OF l0 uf[unfolded plp] f cop sf_f part]
      have uf: "pl.unique_factorization_m f1 (lead_coeff f1, mset gs1)"  
          "pl.unique_factorization_m f2 (lead_coeff f2, mset gs2)" by (auto simp: plp)
      have "set us = set gs1 \<union> set gs2" using part by auto
      with norm have norm_12: "gi \<in> set gs1 \<or> gi \<in> set gs2 \<Longrightarrow> pl.Mp gi = gi" for gi by auto
      note IH1 = IH(1)[OF fs1 deg_f1(1) uf(1) dvd(1) norm_12]
      note IH2 = IH(2)[OF fs2 deg_f2(1) uf(2) dvd(2) norm_12]
      show ?thesis unfolding fs f using IH1 IH2 by auto
    next
      case None
      from res[unfolded None option.simps] have fs_f: "fs = [f]" by simp
      from sf fF have sf: "p.square_free_m f" 
        using p.square_free_m_factor(1)[of f] unfolding dvd_def by auto
      have "irreducible\<^sub>d f" 
      proof (rule ccontr)
        assume "\<not> irreducible\<^sub>d f"
        from reducible\<^sub>dE[OF this] degf obtain f1 f2 where 
          f: "f = f1 * f2" and
          deg12: "degree f1 \<noteq> 0" "degree f2 \<noteq> 0" "degree f1 < degree f" "degree f2 < degree f" 
          by (simp, metis)
        from f0 have "degree f = degree f1 + degree f2" unfolding f
          by (auto simp: degree_mult_eq)
        hence "degree f1 \<le> degree f div 2 \<or> degree f2 \<le> degree f div 2" by auto
        then obtain f1 f2 where 
          f: "f = f1 * f2" and
          deg12: "degree f1 \<noteq> 0" "degree f2 \<noteq> 0" "degree f1 \<le> degree f div 2" "degree f2 < degree f" 
        proof (standard, goal_cases) 
          case 1
          from 1(1)[of f1 f2] 1(2) f deg12 show ?thesis by auto
        next  
          case 2
          from 2(1)[of f2 f1] 2(2) f deg12 show ?thesis by auto
        qed
        from f0 f have f10: "f1 \<noteq> 0" by auto
        from sf f have sf1: "p.square_free_m f1" 
          using p.square_free_m_factor(1)[of f1] by auto
        from p.coprime_lead_coeff_factor[OF p.prime cop[unfolded f]] 
        have cop1: "coprime (lead_coeff f1) p" by auto
        have deg_m1: "pl.degree_m f1 = degree f1" 
          by (rule poly_mod.degree_m_eq[OF _ pl.m1], 
            insert cop1 p, simp add: l0 p.coprime_exp_mod plp)
        from pl.unique_factorization_m_factor[OF p uf[unfolded f], folded f, OF cop sf l0 plp]
        obtain us1 us2 where 
          uf12: "pl.unique_factorization_m f1 (lead_coeff f1, us1)"
            "pl.unique_factorization_m f2 (lead_coeff f2, us2)"
          and gs: "mset us = us1 + us2"
          and norm12: "image_mset pl.Mp us2 = us2" "image_mset pl.Mp us1 = us1"
          unfolding pl.Mf_def norm' split by (auto simp: pl.Mf_def)
        from gs have "x \<in># us1 \<Longrightarrow> x \<in># mset us" for x by auto
        hence sub1: "x \<in># us1 \<Longrightarrow> x \<in> set us" for x by auto
        from to_fact[OF uf12(1)]
        have fact1: "pl.factorization_m f1 (lead_coeff f1, us1)" .
        have plf10: "pl.Mp f1 \<noteq> 0" 
          using fact1 pl.factorization_m_lead_coeff pl.unique_factorization_m_zero uf12(1) by fastforce
        have "degree f1 = pl.degree_m f1" using deg_m1 by simp
        also have "\<dots> = sum_mset (image_mset pl.degree_m us1)"
          unfolding pl.factorization_m_degree[OF fact1 plf10] ..
        also have "\<dots> = sum_mset (image_mset degree us1)"
          by (rule arg_cong[of _ _ sum_mset], rule image_mset_cong,
            rule pl.monic_degree_m, rule mon_gs, rule sub1) 
        finally have degf1_sum: "degree f1 = sum_mset (image_mset degree us1)" by auto
        with deg12 have "us1 \<noteq> {#}" by auto
        then obtain u us11 where us1: "us1 = {#u#} + us11" 
          by (cases us1, auto)        
        hence u1: "u \<in># us1" by auto
        hence u: "u \<in> set us" by (rule sub1)
        let ?g = "gg u" 
        from pl.factorization_m_mem_dvdm[OF fact1, of u] u1 have u_f1: "pl.dvdm u f1" by auto
        note norm_u = norm[OF u]
        from fact u have irred: "pl.irreducible\<^sub>d_m u" unfolding pl.factorization_m_def by auto
        hence deg_u: "degree u \<noteq> 0" unfolding pl.irreducible\<^sub>d_m_def norm[OF u] by auto
        have "degree u \<le> degree f1" unfolding degf1_sum unfolding us1 by simp
        also have "\<dots> \<le> degree f div 2" by fact
        finally have deg_uf: "degree u \<le> degree f div 2" .
        hence deg_uf': "degree u \<le> Suc (degree f div 2)" "degree u < Suc (degree f div 2)" by auto
        from mon_gs[OF u] have mon_u: "monic u" .

        note short = LLL_short_polynomial[OF deg_u deg_uf'(1) pl1 mon_u, folded gg_def]
        note short = short(1-3) short(4)[OF deg_uf'(2)]
        from short(1,2) deg12(1,3) f10 have "degree (gcd f ?g) \<le> degree f div 2"
          by (metis Suc_leI Suc_le_mono degree_gcd1 gcd.commute le_trans)
        also have "\<dots> < degree f" using degf by simp
        finally have "degree (gcd f ?g) < degree f" by simp
        with find_map_filter_None[OF None, simplified, rule_format, of u] deg_uf u
        have deg_gcd: "degree (gcd f (?g)) = 0" by (auto simp: gcd.commute)
        have "gcd f1 (?g) dvd gcd f (?g)" using f0 unfolding f by simp
        from divides_degree[OF this, unfolded deg_gcd] f0
        have deg_gcd1: "degree (gcd f1 (?g)) = 0" by auto
        from F0 have normF: "\<parallel>F\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of F] by presburger
        have g0: "?g \<noteq> 0" using short(2) .
        from g0 have normg: "\<parallel>?g\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of "?g"] by presburger
        from f10 have normf1: "\<parallel>f1\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of f1] by presburger
        from fF f have f1F: "f1 dvd F" unfolding dvd_def by auto
        have pl_ge0: "pl \<ge> 0" using pl.poly_mod_2_axioms poly_mod_2_def by auto
        from fF have "degree f \<le> degree F" using F0 f0 by (metis dvd_imp_degree_le)
        hence d2D2: "?d2 \<le> ?D2" by simp
        with deg12(3) have df1_D2: "degree f1 \<le> ?D2" by linarith
        from short(1) d2D2 have dg_D2: "degree (gg u) \<le> ?D2" by linarith
        have "\<parallel>f1\<parallel>\<^sup>2 ^ degree (gg u) * \<parallel>gg u\<parallel>\<^sup>2 ^ degree f1
          \<le> \<parallel>f1\<parallel>\<^sup>2 ^ ?D2 * \<parallel>gg u\<parallel>\<^sup>2 ^ ?D2" 
          by (rule mult_mono[OF pow_mono_exp pow_mono_exp], 
              insert normf1 normg, auto intro: df1_D2 dg_D2)
        also have "\<dots> = (\<parallel>f1\<parallel>\<^sup>2 * \<parallel>gg u\<parallel>\<^sup>2)^?D2" 
          by (simp add: power_mult_distrib)
        also have "\<dots> \<le> (\<parallel>f1\<parallel>\<^sup>2 * (2^?D2 * \<parallel>f1\<parallel>\<^sup>2))^?D2" 
          by (rule power_mono[OF mult_left_mono[OF order.trans[OF short(4)[OF f10 u_f1]]]],
            insert deg12 d2D2, auto intro!: mult_mono)
        also have "\<dots> = \<parallel>f1\<parallel>\<^sup>2 ^ (?D2 + ?D2) * 2^(?D2 * ?D2)"
          unfolding power_add power_mult_distrib power_mult by simp
        also have "\<dots> \<le> (2 ^ (2 * ?D2) * \<parallel>F\<parallel>\<^sup>2) ^ (?D2 + ?D2) * 2^(?D2 * ?D2)" 
          by (rule mult_right_mono[OF order.trans[OF power_mono[OF sq_norm_factor_bound[OF f1F F0]]]], 
            auto intro!: power_mono mult_right_mono df1_D2)
        also have "\<dots> = 2 ^ (2 * ?D2 * (?D2 + ?D2) + ?D2 * ?D2) * \<parallel>F\<parallel>\<^sup>2 ^ (?D2 + ?D2)" 
          unfolding power_mult_distrib power_mult power_add by simp
        also have "2 * ?D2 * (?D2 + ?D2) + ?D2 * ?D2 = 5 * ?D2 * ?D2" by simp
        also have "?D2 + ?D2 = 2 * ?D2" by simp
        finally have large: 
          "\<parallel>f1\<parallel>\<^sup>2 ^ degree (gg u) * \<parallel>gg u\<parallel>\<^sup>2 ^ degree f1 < pl^2" using large by simp
        have "degree u \<le> degree (?g)" 
        proof (rule pl.dvdm_degree[OF mon_u short(3)], standard)
          assume "pl.Mp (?g) = 0" 
          from arg_cong[OF this, of "\<lambda> p. coeff p (degree ?g)"]
          have "pl.M (coeff ?g (degree ?g)) = 0" by (auto simp: pl.Mp_def coeff_map_poly)
          from this[unfolded pl.M_def] obtain c where lg: "lead_coeff ?g = pl * c" by auto
          with g0 have c0: "c \<noteq> 0" by auto
          hence "pl^2 \<le> (lead_coeff ?g)^2" unfolding lg abs_le_square_iff[symmetric]
            by (rule aux_abs_int)
          also have "\<dots> \<le> \<parallel>?g\<parallel>\<^sup>2" using coeff_le_sq_norm[of ?g] by auto 
          also have "\<dots> = \<parallel>?g\<parallel>\<^sup>2 ^ 1" by simp
          also have "\<dots> \<le> \<parallel>?g\<parallel>\<^sup>2 ^ degree f1" 
            by (rule pow_mono_exp, insert deg12 normg, auto)
          also have "\<dots> = 1 * \<dots>" by simp
          also have "\<dots> \<le> \<parallel>f1\<parallel>\<^sup>2 ^ degree ?g * \<parallel>?g\<parallel>\<^sup>2 ^ degree f1" 
            by (rule mult_right_mono, insert normf1, auto)
          also have "\<dots> < pl\<^sup>2" by (rule large) 
          finally show False by auto
        qed
        with deg_u have deg_g: "0 < degree (gg u)" by auto
        have pl_ge0: "pl \<ge> 0" using pl.poly_mod_2_axioms poly_mod_2_def by auto
        from fF have "degree f \<le> degree F" using F0 f0 by (metis dvd_imp_degree_le)
        hence d2D2: "?d2 \<le> ?D2" by simp
        with deg12(3) have df1_D2: "degree f1 \<le> ?D2" by linarith
        from short(1) d2D2 have dg_D2: "degree (gg u) \<le> ?D2" by linarith
        have "0 < degree f1" "0 < degree u" using deg12 deg_u by auto
        from common_factor_via_short[of f1 "gg u", OF this(1) deg_g mon_u this(2) u_f1 short(3) _ pl_ge0] deg_gcd1
        have "pl^2 \<le> \<parallel>f1\<parallel>\<^sup>2 ^ degree (gg u) * \<parallel>gg u\<parallel>\<^sup>2 ^ degree f1" by linarith
        also have "\<dots> < pl^2" by (rule large)
        finally show False by simp
      qed
      thus ?thesis using fs_f by simp
    qed
  qed
qed

end

lemma LLL_factorization:
  assumes res: "LLL_factorization f = gs"
  and sff: "square_free f"
  and deg: "degree f \<noteq> 0" 
  shows "f = prod_list gs \<and> (\<forall>g\<in>set gs. irreducible\<^sub>d g)"
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where fff: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded LLL_factorization_def Let_def, folded p_def,
    unfolded fff split, folded]
  from suitable_prime_bz[OF sff refl]
  have prime: "prime p" and cop: "coprime ?lc p" and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  note res
  from prime interpret p: poly_mod_prime p by unfold_locales
  define K where "K = 2^(5 * (degree f - 1) * (degree f - 1)) * \<parallel>f\<parallel>\<^sup>2^(2 * (degree f - 1))"
  define N where "N = sqrt_int_ceiling K" 
  have K0: "K \<ge> 0" unfolding K_def by fastforce
  have N0: "N \<ge> 0" unfolding N_def sqrt_int_ceiling using K0 
    by (smt of_int_nonneg real_sqrt_ge_0_iff zero_le_ceiling)
  define n where "n = find_exponent p N" 
  note res = res[folded n_def[unfolded N_def K_def]]
  note n = find_exponent[OF p.m1, of N, folded n_def]
  note bh = p.berlekamp_and_hensel_separated(1)[OF cop sf refl fff n(2)]
  from deg have f0: "f \<noteq> 0" by auto
  from n p.m1 have pn1: "p ^ n > 1" by auto
  note res = res[folded bh(1)]
  note * = p.berlekamp_hensel_unique[OF cop sf bh n(2)] 
  note ** = p.berlekamp_hensel_main[OF n(2) bh cop sf fff]
  from res * **
  have uf: "poly_mod.unique_factorization_m (p ^ n) f (lead_coeff f, mset (berlekamp_hensel p n f))" 
    and norm: "\<And>ui. ui \<in> set (berlekamp_hensel p n f) \<Longrightarrow> poly_mod.Mp (p ^ n) ui = ui" 
    unfolding berlekamp_hensel_def fff split by auto
  have K: "K < (p ^ n)\<^sup>2" using n sqrt_int_ceiling_bound[OF K0] 
    by (smt N0 N_def n(1) power2_le_imp_le)
  show ?thesis
    by (rule LLL_implementation.LLL_reconstruction[OF res deg uf dvd_refl norm f0 cop sf pn1 
          refl prime K[unfolded K_def]]) 
qed

lemma LLL_many_factorization:
  assumes res: "LLL_many_factorization f = gs"
  and sff: "square_free f"
  and deg: "degree f \<noteq> 0" 
  shows "f = prod_list gs \<and> (\<forall>g\<in>set gs. irreducible\<^sub>d g)"
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where fff: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded LLL_many_factorization_def Let_def, folded p_def,
    unfolded fff split, folded]
  from suitable_prime_bz[OF sff refl]
  have prime: "prime p" and cop: "coprime ?lc p" and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  note res
  from prime interpret p: poly_mod_prime p by unfold_locales
  define K where "K = 2^(5 * (degree f div 2) * (degree f div 2)) * \<parallel>f\<parallel>\<^sup>2^(2 * (degree f div 2))"
  define N where "N = sqrt_int_ceiling K" 
  have K0: "K \<ge> 0" unfolding K_def by fastforce
  have N0: "N \<ge> 0" unfolding N_def sqrt_int_ceiling using K0 
    by (smt of_int_nonneg real_sqrt_ge_0_iff zero_le_ceiling)
  define n where "n = find_exponent p N" 
  note res = res[folded n_def[unfolded N_def K_def]]
  note n = find_exponent[OF p.m1, of N, folded n_def]
  note bh = p.berlekamp_and_hensel_separated(1)[OF cop sf refl fff n(2)]
  from deg have f0: "f \<noteq> 0" by auto
  from n p.m1 have pn1: "p ^ n > 1" by auto
  note res = res[folded bh(1)]
  note * = p.berlekamp_hensel_unique[OF cop sf bh n(2)] 
  note ** = p.berlekamp_hensel_main[OF n(2) bh cop sf fff]
  from res * **
  have uf: "poly_mod.unique_factorization_m (p ^ n) f (lead_coeff f, mset (berlekamp_hensel p n f))" 
    and norm: "\<And>ui. ui \<in> set (berlekamp_hensel p n f) \<Longrightarrow> poly_mod.Mp (p ^ n) ui = ui" 
    unfolding berlekamp_hensel_def fff split by auto
  have K: "K < (p ^ n)\<^sup>2" using n sqrt_int_ceiling_bound[OF K0] 
    by (smt N0 N_def n(1) power2_le_imp_le)
  show ?thesis
    by (rule LLL_implementation.LLL_many_reconstruction[OF res deg uf dvd_refl norm f0 cop sf pn1 
          refl prime K[unfolded K_def]]) 
qed

lift_definition one_lattice_LLL_factorization :: int_poly_factorization_algorithm
  is LLL_factorization using LLL_factorization by auto

lift_definition many_lattice_LLL_factorization :: int_poly_factorization_algorithm
  is LLL_many_factorization using LLL_many_factorization by auto

lemma LLL_factorization_primitive: assumes "LLL_factorization f = fs"
  "square_free f" 
  "0 < degree f" 
  "primitive f" 
shows "f = prod_list fs \<and> (\<forall>fi\<in>set fs. irreducible fi \<and> 0 < degree fi \<and> primitive fi)" 
  using assms(1)
  by (intro int_poly_factorization_algorithm_irreducible[of one_lattice_LLL_factorization, 
      OF _ assms(2-)], transfer, auto)
 
thm factorize_int_poly[of one_lattice_LLL_factorization]
thm factorize_int_poly[of many_lattice_LLL_factorization]
end
