(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Factor bound\<close>

text \<open>This theory extends the work about factor bounds which was carried out 
  in the Berlekamp-Zassenhaus development.\<close> 

theory Factor_Bound_2
imports Berlekamp_Zassenhaus.Factor_Bound
   LLL_Basis_Reduction.Norms
begin

lemma norm_1_bound_mignotte: "norm1 f \<le> 2^(degree f) * mahler_measure f"
proof (cases "f = 0")
  case f0: False
  have cf: "coeffs f = map (\<lambda> i. coeff f i) [0 ..< Suc( degree f)]" unfolding coeffs_def 
    using f0 by auto
  have "real_of_int (sum_list (map abs (coeffs f))) 
    = (\<Sum>i\<le>degree f. real_of_int \<bar>poly.coeff f i\<bar>)"
    unfolding cf of_int_hom.hom_sum_list unfolding sum_list_sum_nth 
    by (rule sum.cong, force, auto simp: o_def nth_append)
  also have "\<dots> \<le> (\<Sum>i\<le>degree f. real (degree f choose i) * mahler_measure f)"
    by (rule sum_mono, rule Mignotte_bound)
  also have "\<dots> = real (sum (\<lambda> i. (degree f choose i)) {..degree f}) * mahler_measure f" 
    unfolding sum_distrib_right[symmetric] by auto
  also have "\<dots> = 2^(degree f) * mahler_measure f" unfolding choose_row_sum by auto
  finally show ?thesis unfolding norm1_def .
qed (auto simp: mahler_measure_ge_0 norm1_def)

lemma mahler_measure_l2norm: "mahler_measure f \<le> sqrt (of_int \<parallel>f\<parallel>\<^sup>2)" 
  using Landau_inequality_mahler_measure[of f] unfolding sq_norm_poly_def
  by (auto simp: power2_eq_square)

lemma sq_norm_factor_bound: 
  fixes f h :: "int poly"
  assumes dvd: "h dvd f" and f0: "f \<noteq> 0" 
  shows "\<parallel>h\<parallel>\<^sup>2 \<le> 2 ^ (2 * degree h) * \<parallel>f\<parallel>\<^sup>2" 
proof - 
  let ?r = real_of_int
  have h21: "?r \<parallel>h\<parallel>\<^sup>2 \<le> (?r (norm1 h))^2" using norm2_le_norm1_int[of h]
    by (metis of_int_le_iff of_int_power)
  also have "\<dots> \<le> (2^(degree h) * mahler_measure h)^2" 
    using power_mono[OF norm_1_bound_mignotte[of h], of 2] 
    by (auto simp: norm1_ge_0)
  also have "\<dots> = 2^(2 * degree h) * (mahler_measure h)^2"
    by (simp add: power_even_eq power_mult_distrib)
  also have "\<dots> \<le> 2^(2 * degree h) * (mahler_measure f)^2" 
    by (rule mult_left_mono[OF power_mono], auto simp: mahler_measure_ge_0
    mahler_measure_dvd[OF f0 dvd])
  also have "\<dots> \<le> 2^(2 * degree h) * ?r (\<parallel>f\<parallel>\<^sup>2)"
  proof (rule mult_left_mono)
    have "?r (\<parallel>f\<parallel>\<^sup>2) \<ge> 0" by auto
    from real_sqrt_pow2[OF this]
    show "(mahler_measure f)\<^sup>2 \<le> ?r (\<parallel>f\<parallel>\<^sup>2)" 
      using power_mono[OF mahler_measure_l2norm[of f], of 2]
      by (auto simp: mahler_measure_ge_0)
  qed auto
  also have "\<dots> = ?r (2^(2*degree h) * \<parallel>f\<parallel>\<^sup>2)" 
    by (simp add: ac_simps)
  finally show "\<parallel>h\<parallel>\<^sup>2 \<le> 2 ^ (2 * degree h) * \<parallel>f\<parallel>\<^sup>2" unfolding of_int_le_iff .
qed

end
