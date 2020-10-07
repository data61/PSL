(*
    Authors:    Ralph Bottesch
                Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Gram-Schmidt Implementation for Integer Vectors\<close>

text \<open>This theory implements the Gram-Schmidt algorithm on integer vectors
  using purely integer arithmetic. The formalization is based on \cite{GS_EKM}.\<close>

theory Gram_Schmidt_Int
  imports 
    Gram_Schmidt_2
    More_IArray
begin

context fixes
  fs :: "int vec iarray" and m :: nat
begin 
fun sigma_array where
  "sigma_array dmus dmusi dmusj dll l = (if l = 0 then dmusi !! l * dmusj !! l
      else let l1 = l - 1; dll1 = dmus !! l1 !! l1 in
      (dll * sigma_array dmus dmusi dmusj dll1 l1 + dmusi !! l * dmusj !! l) div 
          dll1)"

declare sigma_array.simps[simp del]

partial_function(tailrec) dmu_array_row_main where
  [code]: "dmu_array_row_main fi i dmus j = (if j = i then dmus
     else let sj = Suc j; 
       dmus_i = dmus !! i;
       djj = dmus !! j !! j;
       dmu_ij = djj * (fi \<bullet> fs !! sj) - sigma_array dmus dmus_i (dmus !! sj) djj j;
       dmus' = iarray_update dmus i (iarray_append dmus_i dmu_ij)
      in dmu_array_row_main fi i dmus' sj)" 

definition dmu_array_row where
  "dmu_array_row dmus i = (let fi = fs !! i in 
      dmu_array_row_main fi i (iarray_append dmus (IArray [fi \<bullet> fs !! 0])) 0)" 

partial_function (tailrec) dmu_array where 
  [code]: "dmu_array dmus i = (if i = m then dmus else 
    let dmus' = dmu_array_row dmus i 
      in dmu_array dmus' (Suc i))"
end

definition d\<mu>_impl :: "int vec list \<Rightarrow> int iarray iarray" where
  "d\<mu>_impl fs = dmu_array (IArray fs) (length fs) (IArray []) 0" 


definition (in gram_schmidt) \<beta> where "\<beta> fs l = Gramian_determinant fs (Suc l) / Gramian_determinant fs l"

context gram_schmidt_fs_lin_indpt
begin

lemma Gramian_beta:
  assumes "i < m"
  shows "\<beta> fs i = \<parallel>fs ! i\<parallel>\<^sup>2 - (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * \<beta> fs j)"
proof -
  let ?S = "M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
  have S: "?S \<in> carrier_vec n"
    using assms by (auto intro!: M.sumlist_carrier gso_carrier)
  have fi: "fs ! i \<in> carrier_vec n" using assms by auto
  have "\<beta> fs i = gso i \<bullet> gso i"
    unfolding \<beta>_def
    using assms dist by (auto simp add: Gramian_determinant_div sq_norm_vec_as_cscalar_prod)
  also have "\<dots> = (fs ! i + ?S) \<bullet> (fs ! i + ?S)"
    by (subst gso.simps, subst (2) gso.simps) auto
  also have "\<dots> = fs ! i \<bullet> fs ! i + ?S \<bullet> fs ! i + fs ! i \<bullet> ?S + ?S \<bullet> ?S"
    using assms S by (auto simp add: add_scalar_prod_distrib[of _ n] scalar_prod_add_distrib[of _ n])
  also have "fs ! i \<bullet> ?S = ?S \<bullet> fs ! i" 
    by (rule comm_scalar_prod[OF fi S])
  also have "?S \<bullet> fs ! i = ?S \<bullet> gso i - ?S \<bullet> ?S"
  proof -
    have "fs ! i = gso i - M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
       using assms S by (subst gso.simps) auto
    then show ?thesis
      using assms S by (auto simp add: minus_scalar_prod_distrib[of _ n] scalar_prod_minus_distrib[of _ n])
  qed
  also have "?S \<bullet> gso i = 0"
    using assms orthogonal
    by(subst scalar_prod_left_sum_distrib)
      (auto intro!: sum_list_neutral M.sumlist_carrier gso_carrier)
  also have "?S \<bullet> ?S = (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * (gso j \<bullet> gso j))"
    using assms dist by (subst scalar_prod_lincomb_gso)
       (auto simp add: power2_eq_square interv_sum_list_conv_sum_set_nat)
  also have "\<dots> =  (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * \<beta> fs j)"
    using assms dist
    by (auto simp add: \<beta>_def Gramian_determinant_div sq_norm_vec_as_cscalar_prod
        intro!: sum.cong)
  finally show ?thesis
    by (auto simp add: sq_norm_vec_as_cscalar_prod)
qed

lemma gso_norm_beta:
  assumes "j < m"
  shows "\<beta> fs j = sq_norm (gso j)"
  unfolding \<beta>_def
  using assms dist by (auto simp add: Gramian_determinant_div sq_norm_vec_as_cscalar_prod)

lemma mu_Gramian_beta_def:
  assumes "j < i" "i < m"
  shows "\<mu> i j = (fs ! i \<bullet> fs ! j - (\<Sum>k = 0..<j. \<mu> j k * \<mu> i k * \<beta> fs k)) / \<beta> fs j"
proof -
  let ?list = "map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [0..<i]" 
  let ?neg_sum = "M.sumlist (map (\<lambda>ja. - \<mu> j ja \<cdot>\<^sub>v gso ja) [0..<j])"
  have list: "set ?list \<subseteq> carrier_vec n" using gso_carrier assms by auto
  define fi where "fi = fs ! i"
  have list_id: "[0..<i] = [0..<j] @ [j..<i]" 
    using assms by (metis append.simps(1) neq0_conv upt.simps(1) upt_append)
  have "\<mu> i j = (fs ! i) \<bullet> (gso j) / sq_norm (gso j) "
    unfolding \<mu>.simps using assms by auto
  also have " ... = fs ! i \<bullet> (fs ! j + ?neg_sum) / sq_norm (gso j)" 
    by (subst gso.simps, simp)
  also have " ... = (fi \<bullet> fs ! j + fs ! i \<bullet> ?neg_sum) / sq_norm (gso j)"
    using assms unfolding fi_def
    by (subst scalar_prod_add_distrib [of _ n]) (auto intro!: M.sumlist_carrier gso_carrier)
  also have "fs ! i = gso i + M.sumlist ?list "
    by (rule fs_by_gso_def[OF assms(2)])
  also have "... \<bullet> ?neg_sum = gso i \<bullet> ?neg_sum + M.sumlist ?list \<bullet> ?neg_sum"
    using assms by (subst add_scalar_prod_distrib [of _ n]) (auto intro!: M.sumlist_carrier gso_carrier)
  also have " M.sumlist ?list = M.sumlist (map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [0..<j]) 
     + M.sumlist (map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [j..<i]) " (is "_ = ?sumj + ?sumi")
    unfolding list_id
    by (subst M.sumlist_append[symmetric], insert gso_carrier assms, auto)
  also have "gso i \<bullet> ?neg_sum = 0"
    by (rule orthogonal_sumlist, insert gso_carrier dist assms orthogonal, auto)
  also have " (?sumj + ?sumi) \<bullet> ?neg_sum = ?sumj \<bullet> ?neg_sum + ?sumi \<bullet> ?neg_sum"
    using assms
    by (subst add_scalar_prod_distrib [of _ n], auto intro!: M.sumlist_carrier gso_carrier)
  also have " ?sumj \<bullet> ?neg_sum = (\<Sum>l = 0..<j. (\<mu> i l) * (-\<mu> j l) * (gso l \<bullet> gso l)) "
    using assms
    by (subst scalar_prod_lincomb_gso) (auto simp add: interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = - (\<Sum>l = 0..<j. (\<mu> i l) * (\<mu> j l) * (gso l \<bullet> gso l)) " (is "_ = - ?sum")
    by (auto simp add: sum_negf)
  also have "?sum = (\<Sum>l = 0..<j. (\<mu> j l) * (\<mu> i l) * \<beta> fs l)" 
    using assms
    by (intro sum.cong, auto simp: gso_norm_beta sq_norm_vec_as_cscalar_prod)
  also have "?sumi \<bullet> ?neg_sum = 0"
    apply (rule orthogonal_sumlist, insert gso_carrier assms orthogonal, auto intro!: M.sumlist_carrier gso_carrier)
    apply (subst comm_scalar_prod[of _ n], auto intro!: M.sumlist_carrier)
    by (rule orthogonal_sumlist, use dist in auto)
  also have "sq_norm (gso j) = \<beta> fs j"
    using assms
    by (subst gso_norm_beta, auto)
  finally show ?thesis unfolding fi_def by simp
qed

end

lemma (in gram_schmidt) Gramian_matrix_alt_alt_alt_def:
  assumes "k \<le> length fs" "set fs \<subseteq> carrier_vec n"
  shows "Gramian_matrix fs k = mat k k (\<lambda>(i,j). fs ! i \<bullet> fs ! j)"
proof -
  have *: "vec n (($) (fs ! i)) = fs ! i" if "i < length fs" for i
    using that assms
    by (metis carrier_vecD dim_vec eq_vecI index_vec nth_mem subsetCE)
  then show ?thesis
    unfolding Gramian_matrix_def using  assms
    by (intro eq_matI) (auto simp add: Let_def)
qed

lemma (in gram_schmidt_fs_Rn) Gramian_determinant_1 [simp]:
  assumes "0 < length fs"
  shows "Gramian_determinant fs (Suc 0) = \<parallel>fs ! 0\<parallel>\<^sup>2"
proof -
  have "Gramian_determinant fs (Suc 0) = fs ! 0 \<bullet> fs ! 0"
    using assms unfolding Gramian_determinant_def 
    by (subst det_def') (auto simp add: Gramian_matrix_def Let_def scalar_prod_def)
  then show ?thesis
    by (subst sq_norm_vec_as_cscalar_prod) simp
qed


context gram_schmidt_fs_lin_indpt
begin


definition \<mu>' where "\<mu>' i j \<equiv> d (Suc j) * \<mu> i j" 


fun \<sigma> where 
  "\<sigma> 0 i j = 0" 
| "\<sigma> (Suc l) i j = (d (Suc l) * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / d l" 

lemma d_Suc: "d (Suc i) = \<mu>' i i" unfolding \<mu>'_def by (simp add: \<mu>.simps)
lemma d_0: "d 0 = 1" by (rule Gramian_determinant_0)

lemma \<sigma>: assumes lj: "l \<le> m" 
  shows "\<sigma> l i j = d l * (\<Sum>k < l. \<mu> i k * \<mu> j k * \<beta> fs k)"
  using lj
proof (induct l)
  case (Suc l)
  from Suc(2-) have lj: "l \<le> m" by auto
  note IH = Suc(1)[OF lj]
  let ?f = "\<lambda> k. \<mu> i k * \<mu> j k * \<beta> fs k" 
  have dl0: "d l > 0" using lj Gramian_determinant dist unfolding lin_indpt_list_def by auto
  have "\<sigma> (Suc l) i j = (d (Suc l) * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / d l" by simp
  also have "\<dots> = (d (Suc l) * \<sigma> l i j) / d l + (\<mu>' i l * \<mu>' j l) / d l" using dl0 
    by (simp add: field_simps)
  also have "(\<mu>' i l * \<mu>' j l) / d l = d (Suc l) * ?f l" (is "_ = ?one")
    unfolding \<beta>_def \<mu>'_def by auto
  also have "(d (Suc l) * \<sigma> l i j) / d l = d (Suc l) * (\<Sum>k < l. ?f k)" (is "_ = ?sum")
    using dl0 unfolding IH by simp
  also have "?sum + ?one = d (Suc l) * (?f l + (\<Sum>k < l. ?f k))" by (simp add: field_simps)
  also have "?f l + (\<Sum>k < l. ?f k) = (\<Sum>k < Suc l. ?f k)" by simp
  finally show ?case .
qed auto

lemma \<mu>': assumes j: "j \<le> i" and i: "i < m" 
  shows "\<mu>' i j = d j * (fs ! i \<bullet> fs ! j) - \<sigma> j i j" 
proof (cases "j < i")
  case j: True
  have dsj: "d (Suc j) > 0"
    using j i Gramian_determinant dist unfolding lin_indpt_list_def
    by (meson less_trans_Suc nat_less_le)
  let ?sum = " (\<Sum>k = 0..<j. \<mu> j k * \<mu> i k * \<beta> fs k)" 
  have "\<mu>' i j = (fs ! i \<bullet> fs ! j - ?sum) * (d (Suc j) / \<beta> fs j)"     
    unfolding mu_Gramian_beta_def[OF j i] \<mu>'_def by simp
  also have "d (Suc j) / \<beta> fs j = d j" unfolding \<beta>_def using dsj by auto
  also have "(fs ! i \<bullet> fs ! j - ?sum) * d j = (fs ! i \<bullet> fs ! j) * d j - d j * ?sum" 
    by (simp add: ring_distribs)
  also have "d j * ?sum = \<sigma> j i j" 
    by (subst \<sigma>, (insert j i, force), intro arg_cong[of _ _ "\<lambda> x. _ * x"] sum.cong, auto)
  finally show ?thesis by simp
next
  case False
  with j have j: "j = i" by auto
  have dsi: "d (Suc i) > 0" "d i > 0"
    using i Suc_leI dist  unfolding lin_indpt_list_def
    by (simp_all add: Suc_leI Gramian_determinant(2))
  let ?sum = " (\<Sum>k = 0..<i. \<mu> i k * \<mu> i k * \<beta> fs k)" 
  have bzero: "\<beta> fs i \<noteq> 0" unfolding \<beta>_def using dsi by auto
  have "\<mu>' i i = d (Suc i)" by (simp add: \<mu>.simps \<mu>'_def)
  also have "\<dots> = \<beta> fs i * (d (Suc i)  / \<beta> fs i)" using bzero by simp 
  also have "d (Suc i) / \<beta> fs i = d i" unfolding \<beta>_def using dsi by auto
  also have "\<beta> fs i = (fs ! i \<bullet> fs ! i - ?sum)" 
    unfolding Gramian_beta[OF i]
    by (rule arg_cong2[of _ _ _ _ "(-)", OF _ sum.cong], 
        auto simp: power2_eq_square sq_norm_vec_as_cscalar_prod)
  also have "(fs ! i \<bullet> fs ! i - ?sum) * d i = (fs ! i \<bullet> fs ! i) * d i - d i * ?sum" 
    by (simp add: ring_distribs)
  also have "d i * ?sum = \<sigma> i i i" 
    by (subst \<sigma>, (insert i i, force), intro arg_cong[of _ _ "\<lambda> x. _ * x"] sum.cong, auto)
  finally show ?thesis using j by simp
qed

lemma \<sigma>_via_\<mu>': "\<sigma> (Suc l) i j = 
  (if l = 0 then \<mu>' i 0 * \<mu>' j 0 else (\<mu>' l l * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / \<mu>' (l - 1) (l - 1))"
  by (cases l, auto simp: d_Suc)

lemma \<mu>'_via_\<sigma>: assumes j: "j \<le> i" and i: "i < m" 
  shows "\<mu>' i j = 
    (if j = 0 then fs ! i \<bullet> fs ! j else \<mu>' (j - 1) (j - 1) * (fs ! i \<bullet> fs ! j) - \<sigma> j i j)"
  unfolding \<mu>'[OF assms] by (cases j, auto simp: d_Suc)

lemma fs_i_sumlist_\<kappa>:
  assumes "i < m" "l \<le> i" "j < l"
  shows "(fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])) \<bullet> fs ! j = 0"
proof -
  have "fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])
        = fs ! i - M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l])"
    using assms gso_carrier assms 
    by (subst \<kappa>_def[symmetric]) (auto simp add: dim_sumlist sumlist_nth sum_negf)
  also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
  proof -
    have "fs ! i = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<Suc i])"
      using assms by (intro fi_is_sum_of_mu_gso) auto
    also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) +
                  M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    proof -
      have *: "[0..<Suc i] = [0..<l] @ [l..<Suc i]"
        using assms by (metis diff_zero le_imp_less_Suc length_upt list_trisect upt_conv_Cons)
      show ?thesis
        by (subst *, subst map_append, subst sumlist_append) (use gso_carrier assms in auto)
    qed
    finally show ?thesis
      using assms gso_carrier assms by (auto simp add: algebra_simps dim_sumlist)
  qed
  finally have "fs ! i + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) =
                M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    by simp
  moreover have "\<dots> \<bullet> (fs ! j) = 0"
    using assms gso_carrier assms unfolding lin_indpt_list_def
    by (subst scalar_prod_left_sum_distrib)
       (auto simp add: algebra_simps dim_sumlist gso_scalar_zero intro!: sum_list_zero)
  ultimately show ?thesis using assms by auto
qed


end (* gram_schmidt_fs_lin_indpt *)

context gram_schmidt_fs_int
begin


lemma \<beta>_pos : "i < m \<Longrightarrow> \<beta> fs i > 0" 
  using Gramian_determinant(2) unfolding lin_indpt_list_def \<beta>_def by auto

lemma \<beta>_zero : "i < m \<Longrightarrow> \<beta> fs i \<noteq> 0" 
  using \<beta>_pos[of i] by simp

lemma \<sigma>_integer:  
  assumes l: "l \<le> j" and j: "j \<le> i" and i: "i < m"
  shows "\<sigma> l i j \<in> \<int>" 
proof -
  from assms have ll: "l \<le> m" by auto
  have fs_carr: "j < m \<Longrightarrow> fs ! j \<in> carrier_vec n" for j using assms fs_carrier unfolding set_conv_nth by force
  with assms have fs_carr_j: "fs ! j \<in> carrier_vec n" by auto
  have dim_gso: "i < m \<Longrightarrow> dim_vec (gso i) = n" for i using gso_carrier by auto
  have dim_fs: "k < m \<Longrightarrow> dim_vec (fs ! k) = n" for k using smult_carrier_vec fs_carr by auto
  have i_l_m: "i < l \<Longrightarrow> i < m" for i using assms by auto
  have smult: "\<And> i j . j < n \<Longrightarrow> i < l \<Longrightarrow> (c \<cdot>\<^sub>v fs ! i) $ j = c * (fs ! i $ j)" for c
    using i_l_m dim_fs by auto
  have "\<sigma> l i j = d l * (\<Sum>k < l. \<mu> i k * \<mu> j k * \<beta> fs k)"
    unfolding \<sigma>[OF ll] by simp
  also have " ... = d l * (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) /  sq_norm (gso k)) * \<beta> fs k)" (is "_ = _ * ?sum")
    unfolding \<mu>.simps using assms by auto
  also have "?sum =  (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) /  \<beta> fs k) * \<beta> fs k)"
    using assms by (auto simp add: gso_norm_beta[symmetric] intro!: sum.cong)

  also have "... = (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) ))"
    using \<beta>_zero assms by (auto intro!: sum.cong)

  also have " ... = (fs ! j) \<bullet> M.sumlist (map (\<lambda>k. (\<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l] )"
    using assms fs_carr[of j] gso_carrier
    by (subst scalar_prod_right_sum_distrib) (auto intro!: gso_carrier fs_carr sum.cong simp: sum_list_sum_nth)

  also have "d l * \<dots> = (fs ! j) \<bullet> (d l \<cdot>\<^sub>v M.sumlist (map (\<lambda>k. (\<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l]))" (is "_ = _ \<bullet> (_ \<cdot>\<^sub>v ?sum2)")
    apply (rule scalar_prod_smult_distrib[symmetric])
     apply (rule fs_carr)
    using assms gso_carrier
    by (auto intro!: sumlist_carrier)

	  also have "?sum2 = - sumlist (map (\<lambda>k. (- \<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l])"
	    apply(rule eq_vecI)
	    using fs_carr gso_carrier assms i_l_m
	    by(auto simp: sum_negf[symmetric] dim_sumlist sumlist_nth dim_gso intro!: sum.cong)

	  also have "\<dots> = - sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])"
	    using assms gso_carrier assms 
	    apply (subst \<kappa>_def)
	    by (auto)

	  also have "(d l \<cdot>\<^sub>v - sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])) =
		     (- sumlist (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l]))"
	    apply(rule eq_vecI)
	    using fs_carr smult_carrier_vec dim_fs
	    using dim_fs i_l_m 
	    by (auto simp: smult dim_sumlist sumlist_nth sum_distrib_left intro!: sum.cong)

	  finally have id: " \<sigma> l i j = fs ! j \<bullet> - M.sumlist (map (\<lambda>k. d l * \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l]) " .
	  (* now we are able to apply d_\<kappa>_int *)
	  show "\<sigma> l i j \<in> \<int>" unfolding id
	    using i_l_m fs_carr assms fs_int d_\<kappa>_Ints
	    by (auto simp: dim_sumlist sumlist_nth smult 
	        intro!: sumlist_carrier Ints_minus Ints_sum Ints_mult[of _ "fs ! _ $ _"]  Ints_scalar_prod[OF fs_carr])
	qed

end (* gram_schmidt_fs_int *)



context fs_int_indpt
begin

fun \<sigma>s and \<mu>' where 
  "\<sigma>s 0 i j = \<mu>' i 0 * \<mu>' j 0" 
| "\<sigma>s (Suc l) i j = (\<mu>' (Suc l) (Suc l) * \<sigma>s l i j + \<mu>' i (Suc l) * \<mu>' j (Suc l)) div \<mu>' l l" 
| "\<mu>' i j = (if j = 0 then fs ! i \<bullet> fs ! j else \<mu>' (j - 1) (j - 1) * (fs ! i \<bullet> fs ! j) - \<sigma>s (j - 1) i j)"

declare \<mu>'.simps[simp del]

lemma \<sigma>s_\<mu>': "l < j \<Longrightarrow> j \<le> i \<Longrightarrow> i < m \<Longrightarrow> of_int (\<sigma>s l i j) = gs.\<sigma> (Suc l) i j" 
  "i < m \<Longrightarrow> j \<le> i \<Longrightarrow> of_int (\<mu>'  i j) = gs.\<mu>' i j" 
proof (induct l i j and i j rule: \<sigma>s_\<mu>'.induct)
  case (1 i j)                          
  thus ?case by (simp add: gs.\<sigma>.simps)
next
  case (2 l i j)
  have "gs.\<sigma>(Suc (Suc l)) i j \<in> \<int>" 
    by (rule gs.\<sigma>_integer, insert 2 gs.fs_carrier, auto)
  then have "rat_of_int (\<mu>' (Suc l) (Suc l) * \<sigma>s l i j + \<mu>' i (Suc l) * \<mu>' j (Suc l)) / rat_of_int (\<mu>' l l) \<in> \<int>"
    using 2 gs.d_Suc by (auto)
  then have "rat_of_int (\<sigma>s (Suc l) i j) = 
             of_int (\<mu>' (Suc l) (Suc l) * \<sigma>s l i j + \<mu>' i (Suc l) * \<mu>' j (Suc l)) / of_int (\<mu>' l l)"
    by (subst \<sigma>s.simps, subst exact_division) auto
  also have "\<dots> = gs.\<sigma> (Suc (Suc l)) i j"
    using 2 gs.d_Suc by (auto)
  finally show ?case
    by simp
next
  case (3 i j)
  have "dim_vec (fs ! j) = dim_vec (fs ! i)"
    using 3 f_carrier[of i] f_carrier[of j] carrier_vec_def by auto
  then have "of_int_hom.vec_hom (fs ! i) $ k = rat_of_int (fs ! i $ k)" if "k < dim_vec (fs ! j)" for k
    using that by simp
  then have *: "of_int_hom.vec_hom (fs ! i) \<bullet> of_int_hom.vec_hom (fs ! j) = rat_of_int (fs ! i \<bullet> fs ! j)"
    using 3 by (auto simp add: scalar_prod_def)
  show ?case
  proof (cases "j = 0")
    case True
    have "dim_vec (fs ! 0) = dim_vec (fs ! i)"
      using 3 f_carrier[of i] f_carrier[of 0] carrier_vec_def by fastforce
    then have 1: "of_int_hom.vec_hom (fs ! i) $ k = rat_of_int (fs ! i $ k)" if "k < dim_vec (fs ! 0)" for k
      using that by simp
    have "(\<mu>' i j) = fs ! i \<bullet> fs ! j"
      using True by (simp add: \<mu>'.simps)
    also note *[symmetric]
    also have  "of_int_hom.vec_hom (fs ! j) = map of_int_hom.vec_hom fs ! j"
      using 3 by auto
    finally show ?thesis
      using 3 True by (subst gs.\<mu>'_via_\<sigma>) (auto)
  next
    case False
    then have "gs.\<mu>' i j = gs.\<mu>' (j - Suc 0) (j - Suc 0) * (rat_of_int (fs ! i \<bullet> fs ! j)) - gs.\<sigma> j i j"
      using * False 3 by (subst gs.\<mu>'_via_\<sigma>) (auto)
    then show ?thesis
      using False 3 by (subst \<mu>'.simps) (auto)
	qed
qed


lemma \<mu>': assumes "i < m" "j \<le> i"
  shows "\<mu>' i j = d\<mu> i j"
    "j = i \<Longrightarrow> \<mu>' i j = d fs (Suc i)"  
proof -
  let ?r = rat_of_int
  from assms have "j < m" by auto
  note d\<mu> = d\<mu>[OF this assms(1)]
  have "?r (\<mu>' i j) = gs.\<mu>' i j" 
    using \<sigma>s_\<mu>' assms by auto
  also have "\<dots> = ?r (d\<mu> i j)"
    unfolding gs.\<mu>'_def d\<mu>
    by (subst of_int_Gramian_determinant, insert assms fs_carrier, auto simp: d_def subset_eq)
  finally show 1: "\<mu>' i j = d\<mu> i j"
    by simp
  assume j: "j = i"
  have "?r (\<mu>' i j) = ?r (d\<mu> i j)"
    unfolding 1 ..
  also have "\<dots> = ?r (d fs (Suc i))"
    unfolding d\<mu> unfolding j by (simp add: gs.\<mu>.simps)
  finally show "\<mu>' i j = d fs (Suc i)"
    by simp
qed

lemma sigma_array: assumes mm: "mm \<le> m" and j: "j < mm" 
  shows "l \<le> j \<Longrightarrow> sigma_array (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (if i = mm then Suc j else Suc i)) (Suc mm))
	     (IArray.of_fun (\<mu>' mm) (Suc j)) (IArray.of_fun (\<mu>' (Suc j)) (if Suc j = mm then Suc j else Suc (Suc j))) (\<mu>' l l) l =
	    \<sigma>s l mm (Suc j)"
proof (induct l)
  case 0
  show ?case unfolding \<sigma>s.simps sigma_array.simps[of _ _ _ _ 0]
    using mm j by (auto simp: nth_append)
next
  case (Suc l)
  hence l: "l < j" "l \<le> j" by auto
  have id: "(Suc l = 0) = False" "Suc l - 1 = l" by auto
  have ineq: "Suc l < Suc mm" "l < Suc mm" 
    "Suc l < (if Suc l = mm then Suc j else Suc (Suc l))" 
    "Suc l < (if Suc j = mm then Suc j else Suc (Suc j))" 
    "l < (if l = mm then Suc j else Suc l)" 
    "Suc l < Suc j" 
    using mm l j by auto
  note IH = Suc(1)[OF l(2)]
  show ?case unfolding sigma_array.simps[of _ _ _ _ "Suc l"] id if_False Let_def IH
	    of_fun_nth[OF ineq(1)] of_fun_nth[OF ineq(2)] of_fun_nth[OF ineq(3)] 
	    of_fun_nth[OF ineq(4)] of_fun_nth[OF ineq(5)] of_fun_nth[OF ineq(6)]
	  unfolding \<sigma>s.simps by simp
qed

lemma dmu_array_row_main: assumes mm: "mm \<le> m" shows
  "j \<le> mm \<Longrightarrow> dmu_array_row_main (IArray fs) (IArray fs !!  mm) mm
	    (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (if i = mm then Suc j else Suc i)) (Suc mm))    
	     j = IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) (Suc mm)" 
proof (induct "mm - j" arbitrary: j)
  case 0
  thus ?case unfolding dmu_array_row_main.simps[of _ _ _ _ j] by simp
next
  case (Suc x j)
  hence prems: "x = mm - Suc j" "Suc j \<le> mm" and j: "j < mm" by auto
  note IH = Suc(1)[OF prems]
  have id: "(j = mm) = False" "(mm = mm) = True" using Suc(2-) by auto
  have id2: "IArray.of_fun (\<mu>' mm) (Suc j) = IArray (map (\<mu>' mm) [0..<Suc j])" 
    by simp
  have id3: "IArray fs !! mm = fs ! mm" "IArray fs !! Suc j = fs ! Suc j" by auto
  have le: "j < Suc j" "Suc j < Suc mm" "mm < Suc mm" "j < Suc mm" 
    "j < (if j = mm then Suc j else Suc j)" using j by auto
  show ?case unfolding dmu_array_row_main.simps[of _ _ _ _ j] 
      IH[symmetric] Let_def id if_True if_False id3
      of_fun_nth[OF le(1)] of_fun_nth[OF le(2)]
      of_fun_nth[OF le(3)] of_fun_nth[OF le(4)]
      of_fun_nth[OF le(5)]  
      sigma_array[OF mm j le_refl, folded id2]
      iarray_length_of_fun iarray_update_of_fun iarray_append_of_fun
  proof (rule arg_cong[of _ _ "\<lambda> x. dmu_array_row_main _ _ _ x _"], rule iarray_cong', goal_cases)
    case (1 i)
    show ?case unfolding of_fun_nth[OF 1] using j 1
      by (cases "i = mm", auto simp: \<mu>'.simps[of _ "Suc j"])
  qed
qed

lemma dmu_array_row: assumes mm: "mm \<le> m" shows
  "dmu_array_row (IArray fs) (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) mm) mm =
	    IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) (Suc mm)" 
proof -
  have 0: "0 \<le> mm" by auto
  show ?thesis unfolding dmu_array_row_def Let_def dmu_array_row_main[OF assms 0, symmetric]
    unfolding iarray_append.simps IArray.of_fun_def id map_append list.simps
    by (rule arg_cong[of _ _ "\<lambda> x. dmu_array_row_main _ _ _ (IArray x) _"], rule nth_equalityI, 
	      auto simp: nth_append \<mu>'.simps[of _ 0])
qed

lemma dmu_array: assumes "mm \<le> m" 
  shows "dmu_array (IArray fs) m (IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. \<mu>' i j) (Suc i)) mm) mm 
	  = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. \<mu>' i j) (Suc i)) m" 
	using assms
proof (induct mm rule: wf_induct[OF wf_measure[of "\<lambda> mm. m - mm"]])
  case (1 mm)
  show ?case
  proof (cases "mm = m")
    case True
    thus ?thesis unfolding dmu_array.simps[of _ _ _ mm] by simp
  next
    case False
    with 1(2-)
    have mm: "mm \<le> m" and id: "(Suc mm = 0) = False" "Suc mm - 1 = mm" "(mm = m) = False"
      and prems: "(Suc mm, mm) \<in> measure ((-) m)" "Suc mm \<le> m" by auto
    have list: "[0..<Suc mm] = [0..< mm] @ [mm]" by auto
    note IH = 1(1)[rule_format, OF prems]
    show ?thesis unfolding dmu_array.simps[of _ _ _ mm] id if_False Let_def 
      unfolding dmu_array_row[OF mm] IH[symmetric]
      by (rule arg_cong[of _ _ "\<lambda> x. dmu_array _ _ x _"], rule iarray_cong, auto)
  qed
qed

lemma d\<mu>_impl: "d\<mu>_impl fs = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. d\<mu> i j) (Suc i)) m" 
  unfolding d\<mu>_impl_def using dmu_array[of 0] by (auto simp: \<mu>')

end (* fs_int_indpt *)

context gram_schmidt_fs_int
begin

lemma N_\<mu>':
  assumes "i < m" "j \<le> i"
  shows "(\<mu>' i j)\<^sup>2 \<le> N ^ (3 * Suc j)"
proof -
  have 1: "1 \<le> N * N ^ j"
    using assms N_1 one_le_power[of _ "Suc j"] by fastforce
  have "0 < d (Suc j)"
     using assms by (intro Gramian_determinant) auto
  then have [simp]: "0 \<le> d (Suc j)"
    by arith
  have N_d: "d (Suc j) \<le> N ^ (Suc j)"
    using assms by (intro N_d) auto
  have "(\<mu>' i j)\<^sup>2 = (d (Suc j)) * (d (Suc j)) * (\<mu> i j)\<^sup>2"
    unfolding \<mu>'_def by (auto simp add: power2_eq_square)
  also have "\<dots> \<le> (d (Suc j)) * (d (Suc j)) * N ^ (Suc j)"
  proof -
    have "(\<mu> i j)\<^sup>2 \<le> N ^ (Suc j)" if "i = j"
      using that 1 by (auto simp add: \<mu>.simps)
    moreover have "(\<mu> i j)\<^sup>2 \<le> N ^ (Suc j)" if "i \<noteq> j"
      using N_mu assms that by (auto)
    ultimately have "(\<mu> i j)\<^sup>2 \<le> N ^ (Suc j)"
      by fastforce
    then show ?thesis
      by (intro mult_mono[of _ _ "(\<mu> i j)\<^sup>2"]) (auto)
  qed
  also have "\<dots> \<le> N ^ (Suc j) * N ^ (Suc j) * N ^ (Suc j)"
    using assms 1 N_d by (auto intro!: mult_mono)
  also have "N ^ (Suc j) * N ^ (Suc j) * N ^ (Suc j) = N ^ (3 * (Suc j))"
    using nat_pow_distrib nat_pow_pow power3_eq_cube by metis
  finally show ?thesis
    by simp
qed

lemma N_\<sigma>:
  assumes "i < m" "j \<le> i" "l \<le> j"
  shows "\<bar>\<sigma> l i j\<bar> \<le> of_nat l * N ^ (2 * l + 2)"
proof -
  have 1: "\<bar>d l\<bar> = d l"
    using Gramian_determinant(2) assms by (intro abs_of_pos) auto
  then have "\<bar>\<sigma> l i j\<bar> = d l * \<bar>\<Sum>k<l. \<mu> i k * \<mu> j k * \<beta> fs k\<bar>"
    using assms by (subst \<sigma>, fastforce, subst abs_mult) auto
  also have "\<dots> \<le> N ^ l * (of_nat l * N ^ (l + 2))"
  proof -
    have "\<bar>\<Sum>k<l. \<mu> i k * \<mu> j k * \<beta> fs k\<bar> \<le> of_nat l * N ^ (l + 2)"
    proof -
      have [simp]: "0 \<le> \<beta> fs k" "\<parallel>gso k\<parallel>\<^sup>2 \<le> N" if "k < l" for k
        using that assms N_gso \<beta>_pos[of k] by auto
      have [simp]: "0 \<le> N * N ^ k" for k
        using N_ge_0 assms by fastforce
      have "\<bar>(\<Sum>k < l. \<mu> i k * \<mu> j k * \<beta> fs k)\<bar> \<le> (\<Sum>k < l. \<bar>\<mu> i k * \<mu> j k * \<beta> fs k\<bar>)"
        using sum_abs by blast
      also have "\<dots> = (\<Sum>k < l. \<bar>\<mu> i k * \<mu> j k\<bar> * \<beta> fs k)"
        using assms by (auto intro!: sum.cong simp add: gso_norm_beta abs_mult_pos sq_norm_vec_ge_0)
      also have "\<dots> = (\<Sum>k < l. \<bar>\<mu> i k\<bar> * \<bar>\<mu> j k\<bar> * \<beta> fs k)"
        using abs_mult by (fastforce intro!: sum.cong)
      also have "\<dots> \<le> (\<Sum>k < l. (max \<bar>\<mu> i k\<bar> \<bar>\<mu> j k\<bar>) * (max \<bar>\<mu> i k\<bar> \<bar>\<mu> j k\<bar>) * \<beta> fs k)"
        by (auto intro!: sum_mono mult_mono)
      also have "\<dots> = (\<Sum>k < l. (max \<bar>\<mu> i k\<bar> \<bar>\<mu> j k\<bar>)\<^sup>2 * \<beta> fs k)"
        by (auto simp add: power2_eq_square)
      also have "\<dots> \<le> (\<Sum>k < l. N ^ (Suc k) * \<beta> fs k)"
        using assms N_mu[of i] N_mu[of j] assms
        by (auto intro!: sum_mono mult_right_mono simp add: max_def)
      also have "\<dots> \<le> (\<Sum>k < l. N ^ (Suc k) * N)"
        using assms by (auto simp add: gso_norm_beta intro!: sum_mono mult_left_mono)
      also have "\<dots> \<le> (\<Sum>k < l. N ^ (Suc l) * N)"
        using assms N_1 N_ge_0 assms by (fastforce intro!: sum_mono mult_right_mono power_increasing)
      also have "\<dots> = of_nat l * N ^ (l + 2)"
        by auto
      finally show ?thesis
        by auto
    qed
    then show ?thesis
      using assms N_d N_ge_0 by (fastforce intro!: mult_mono zero_le_power)
  qed
  also have "\<dots> = of_nat l * N ^ (2 * l + 2)"
    by (auto simp add: field_simps mult_2_right simp flip: power_add)
  finally show ?thesis
    by simp
qed

lemma leq_squared: "(z::int) \<le> z\<^sup>2"
proof (cases "0 < z")
  case True
  then show ?thesis
    by (auto intro!: self_le_power)
next
  case False
  then have "z \<le> 0"
    by (simp)
  also have "0 \<le> z\<^sup>2"
    by (auto)
  finally show ?thesis
    by simp
qed

lemma abs_leq_squared: "\<bar>z::int\<bar> \<le> z\<^sup>2"
  using leq_squared[of "\<bar>z\<bar>"] by auto

end (* gram_schmidt_fs_int *)

context gram_schmidt_fs_int
begin

definition gso' where "gso' i = d i \<cdot>\<^sub>v (gso i)"

fun a where
  "a i 0 = fs ! i" |
  "a i (Suc l) = (1 / d l) \<cdot>\<^sub>v ((d (Suc l) \<cdot>\<^sub>v (a i l)) - ( \<mu>' i l) \<cdot>\<^sub>v gso' l)"

lemma gso'_carrier_vec: 
  assumes "i < m"
  shows "gso' i \<in> carrier_vec n"
  using assms by (auto simp add: gso'_def)

lemma a_carrier_vec: 
  assumes "l \<le> i" "i < m"
  shows "a i l \<in> carrier_vec n"
  using assms by (induction l arbitrary: i) (auto simp add: gso'_def)

lemma a_l: 
  assumes "l \<le> i" "i < m"
  shows "a i l = d l \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]))"
using assms proof (induction l)
  case 0
  then show ?case by auto
next
  case (Suc l)
  have fsi: "fs ! i \<in> carrier_vec n" using f_carrier[of i] assms by auto
  have l_i_m: "l \<le> i \<Longrightarrow> l < m" using assms by auto
  let ?a = "fs ! i"
  let ?sum = "M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l])" 
  let ?term = "(- \<mu> i l \<cdot>\<^sub>v gso l)" 
  have carr: "{?a,?sum,?term} \<subseteq> carrier_vec n" 
    using gso_dim l_i_m Suc(2) sumlist_dim assms
    by (auto intro!: sumlist_carrier)
  have "a i (Suc l) = 
        (1 / d l) \<cdot>\<^sub>v ((d (Suc l) \<cdot>\<^sub>v (d l \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]))))
        - ( \<mu>' i l) \<cdot>\<^sub>v gso' l)" using a.simps Suc by auto
  also have "\<dots> = (1 / d l) \<cdot>\<^sub>v ((d (Suc l) \<cdot>\<^sub>v (d l \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]))))
        + -d (Suc l) * \<mu> i l * d l \<cdot>\<^sub>v gso l )"  (is "_ = _ \<cdot>\<^sub>v (?t1 + ?t2)")
    unfolding \<mu>'_def gso'_def by auto
  also have "?t2 = d l \<cdot>\<^sub>v (-d (Suc l) * \<mu> i l \<cdot>\<^sub>v gso l )" (is "_ = d l \<cdot>\<^sub>v ?tt2")
    using smult_smult_assoc by (auto)
  also have "?t1 = d l \<cdot>\<^sub>v ((d (Suc l) \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]))))" (is "_ = d l \<cdot>\<^sub>v ?tt1")
    using smult_smult_assoc smult_smult_assoc[symmetric] by (auto)
  also have "d l \<cdot>\<^sub>v ?tt1 + d l \<cdot>\<^sub>v ?tt2 = d l \<cdot>\<^sub>v (?tt1 + ?tt2)"
    using gso_carrier l_i_m Suc fsi 
    by (auto intro!: smult_add_distrib_vec[symmetric, of _ n] add_carrier_vec sumlist_carrier)
  also have "(1 / d l) \<cdot>\<^sub>v \<dots> = (d l / d l) \<cdot>\<^sub>v (?tt1 + ?tt2)"
    by (intro eq_vecI, auto)
  also have "d l / d l = 1" 
     using Gramian_determinant(2)[of l] l_i_m Suc by(auto simp: field_simps)
  also have  "1 \<cdot>\<^sub>v (?tt1 + ?tt2) = ?tt1 + ?tt2"  by simp
  also have "?tt2 = d (Suc l) \<cdot>\<^sub>v (- \<mu> i l \<cdot>\<^sub>v gso l)" by auto
  also have "d (Suc l) \<cdot>\<^sub>v (fs ! i + ?sum) + \<dots> =
             d (Suc l) \<cdot>\<^sub>v (fs ! i + ?sum + ?term)"
    using carr by (subst smult_add_distrib_vec) (auto)
  also have "(?a + ?sum) + ?term = ?a + (?sum + ?term)"
    using carr by auto
  also have "?term = M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc l])"
    using gso_carrier Suc l_i_m by auto
  also have "?sum + ... = M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<Suc l])"
    apply(subst sumlist_append[symmetric])
    using fsi l_i_m Suc sumlist_carrier gso_carrier by (auto intro!: sumlist_carrier)
  finally show ?case by auto
qed

lemma a_l': 
  assumes "i < m"
  shows "a i i = gso' i"
proof -
  have "a i i = d i \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]))"
    using a_l assms by auto
  also have "\<dots> = d i \<cdot>\<^sub>v gso i"
    by (subst gso.simps, auto)
  finally have "a i i = gso' i" using gso'_def by auto
  from this show ?thesis by auto
qed

lemma 
  assumes "i < m" "l' \<le> i"
  shows "a i l' = (case l' of
         0 \<Rightarrow> fs ! i |
         Suc l \<Rightarrow> (1 / d l) \<cdot>\<^sub>v (d (Suc l) \<cdot>\<^sub>v (a i l) - (\<mu>' i l) \<cdot>\<^sub>v a l l))"
proof (cases l')
  case (Suc l)
  have "a i (Suc l) = (1 / d l) \<cdot>\<^sub>v ((d (Suc l) \<cdot>\<^sub>v (a i l)) - ( \<mu>' i l) \<cdot>\<^sub>v a l l)" 
    using assms a_l Suc by(subst a_l', auto)
  from this Suc show ?thesis by auto
qed auto

lemma a_Ints:
  assumes "i < m" "l \<le> i" "k < n"
  shows "a i l $ k \<in> \<int>"
proof -
  have fsi: "fs ! i \<in> carrier_vec n" using f_carrier[of i] assms by auto
  have "a i l = d l \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]))" 
    (is "_ = _ \<cdot>\<^sub>v (_ + ?sum)")
    using assms by (subst a_l, auto)
  also have "?sum = sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])"
    using assms gso_carrier
    by (subst \<kappa>_def, auto)
  also have "d l \<cdot>\<^sub>v (fs ! i + sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])) 
           = d l \<cdot>\<^sub>v fs ! i + d l \<cdot>\<^sub>v sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])"
    (is "_ = _ + ?sum")
    using sumlist_carrier fsi apply
      (subst smult_add_distrib_vec[symmetric])
      apply force
    using assms fsi by (subst sumlist_carrier, auto) 
  also have "?sum = sumlist  (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l])"
    apply(subst eq_vecI sumlist_nth)
    using fsi assms
    by (auto simp: dim_sumlist sum_distrib_left sumlist_nth smult_smult_assoc algebra_simps)
  finally have "a i l = d l \<cdot>\<^sub>v fs ! i + sumlist  (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l])"
    by auto
  
  hence "a i l $ k = (d l \<cdot>\<^sub>v fs ! i + sumlist (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l])) $ k" by simp
  also have "\<dots> = (d l \<cdot>\<^sub>v fs ! i) $ k + (sumlist (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l])) $ k" 
    apply (subst index_add_vec)
    using assms fsi by (subst sumlist_dim, auto)
  finally have id: "a i l $ k = (d l \<cdot>\<^sub>v fs ! i) $ k + (sumlist (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l])) $ k".
  
  show ?thesis unfolding id
    using fsi assms d_\<kappa>_Ints fs_int
    by (auto simp: dim_sumlist sumlist_nth
      intro!: Gramian_determinant_Ints sumlist_carrier Ints_minus Ints_add Ints_sum Ints_mult[of _ "fs ! _ $ _"]  Ints_scalar_prod[OF fsi])
qed

lemma a_alt_def:
  assumes "l < length fs"
  shows "a i (Suc l) = (let v = \<mu>' l l \<cdot>\<^sub>v (a i l) - ( \<mu>' i l) \<cdot>\<^sub>v a l l in
                       (if l = 0 then v else (1 / \<mu>' (l - 1) (l - 1)) \<cdot>\<^sub>v v))"
proof -
  have [simp]: "\<mu>' (l - Suc 0) (l - Suc 0) = d l" if "0 < l"
    using that unfolding \<mu>'_def by (auto simp add: \<mu>.simps)
  have [simp]: "\<mu>' l l = d (Suc l)"
    unfolding \<mu>'_def by (auto simp add: \<mu>.simps)
  show ?thesis
    using assms by (auto simp add: Let_def a_l')
qed

end (* gram_schmidt_fs_int *)


context fs_int_indpt
begin


fun gso_int :: "nat \<Rightarrow> nat \<Rightarrow> int vec" where
  "gso_int i 0 = fs ! i" |
  "gso_int i (Suc l) = (let v = \<mu>' l l \<cdot>\<^sub>v (gso_int i l) - \<mu>' i l \<cdot>\<^sub>v gso_int l l in
                         (if l = 0 then v else map_vec (\<lambda>k. k div \<mu>' (l - 1) (l - 1)) v))"

lemma gso_int_carrier_vec:
  assumes "i < length fs" "l \<le> i"
  shows "gso_int i l \<in> carrier_vec n"
  using assms by (induction l arbitrary: i) (fastforce simp add: Let_def)+

lemma gso_int:
  assumes "i < length fs" "l \<le> i"
  shows "of_int_hom.vec_hom (gso_int i l) = gs.a i l"
proof -
  have "dim_vec (gso_int i l) = n" "dim_vec (gs.a i l) = n"
    using gs.a_carrier_vec assms gso_int_carrier_vec carrier_dim_vec by auto
  moreover have "of_int_hom.vec_hom (gso_int i l) $ k = gs.a i l $ k" if k: "k < n" for k
    using assms proof (induction l arbitrary: i)
    case (Suc l)
    note IH = Suc(1)
    have [simp]: "dim_vec (gso_int i l) = n" "dim_vec (gs.a i l) = n" "dim_vec (gso_int l l) = n"
      "dim_vec (gs.a l l) = n"
      using Suc gs.a_carrier_vec gso_int_carrier_vec carrier_dim_vec gs.gso'_carrier_vec by auto
    have "rat_of_int (gso_int i l $ k) = gs.a i l $ k" "rat_of_int (gso_int l l $ k) = gs.a l l $ k"
      using that Suc(1)[of l] Suc(1)[of i] Suc by auto
    then have ?case if "l = 0"
    proof -
      have [simp]: "fs \<noteq> []"
        using Suc by auto
      have [simp]: "dim_vec (gso_int i 0) = n" "dim_vec (gso_int 0 0) = n" "dim_vec (gs.a i 0) = n"
        "dim_vec (gs.a 0 0) = n"
        using Suc fs_carrier carrier_dim_vec gs.a_carrier_vec f_carrier by auto
      have [simp]: "rat_of_int (\<mu>' i 0) = gs.\<mu>' i 0" "rat_of_int (\<mu>' 0 0) = gs.\<mu>' 0 0"
        using Suc \<sigma>s_\<mu>' by (auto intro!: \<sigma>s_\<mu>')
      then show ?thesis
        using that k Suc IH[of i ] Suc(1)[of 0]
        by (subst gso_int.simps, subst gs.a_alt_def) (auto simp del: gso_int.simps gs.a.simps)
    qed
    moreover have ?case if "0 < l"
    proof -
      have *: "rat_of_int (\<mu>' l l * gso_int i l $ k - \<mu>' i l * gso_int l l $ k) / rat_of_int (\<mu>' (l - Suc 0) (l - Suc 0))
     = gs.a i (Suc l) $ k"
        using Suc IH[of l] IH[of i] \<sigma>s_\<mu>' k that by (subst gs.a_alt_def) (auto simp add: Let_def )
      have "of_int_hom.vec_hom (gso_int i (Suc l)) $ k =
            rat_of_int ((\<mu>' l l * gso_int i l $ k - \<mu>' i l * gso_int l l $ k) 
                        div \<mu>' (l - Suc 0) (l - Suc 0))"
        using that gso_int_carrier_vec k by (auto)
      also have "\<dots> = rat_of_int (\<mu>' l l * gso_int i l $ k - \<mu>' i l * gso_int l l $ k) / rat_of_int (\<mu>' (l - Suc 0) (l - Suc 0))"
        using gs.a_Ints k Suc by (intro exact_division, subst *, force)
      also note *
      finally show ?thesis
        by (auto)
    qed
    ultimately show ?case
      by blast
  qed (auto)
  ultimately show ?thesis
    by auto
qed

function gso_int_tail' :: "nat \<Rightarrow> nat \<Rightarrow> int vec \<Rightarrow> int vec" where
  "gso_int_tail' i l acc = (if l \<ge> i then acc
    else (let v = \<mu>' l l \<cdot>\<^sub>v acc - \<mu>' i l \<cdot>\<^sub>v gso_int l l;
              acc' = (map_vec (\<lambda>k. k div \<mu>' (l - 1) (l - 1)) v)
        in gso_int_tail' i (l + 1) acc'))"
  by pat_completeness auto
termination
  by  (relation "(\<lambda>(i,l,acc). i - l)  <*mlex*> {}",  goal_cases) (auto intro!: mlex_less wf_mlex)

fun gso_int_tail :: "nat \<Rightarrow> int vec" where
  "gso_int_tail i = (if i = 0 then fs ! 0 else
     let acc = \<mu>' 0 0 \<cdot>\<^sub>v fs ! i - \<mu>' i 0 \<cdot>\<^sub>v fs ! 0 in
     gso_int_tail' i 1 acc)"

lemma gso_int_tail':
  assumes "acc = gso_int i l" "0 < i" "0 < l" "l \<le> i"
  shows "gso_int_tail' i l acc = gso_int i i"
  using assms proof (induction i l acc rule: gso_int_tail'.induct)
  case (1 i l acc)
  { assume li: "l < i"
    then have "gso_int_tail' i l acc =
        gso_int_tail' i (l + 1) (map_vec (\<lambda>k. k div \<mu>' (l - 1) (l - 1)) (\<mu>' l l \<cdot>\<^sub>v acc - \<mu>' i l \<cdot>\<^sub>v gso_int l l))"  
      using 1 by (auto simp add: Let_def)
    also have "\<dots> = gso_int i i"
      using 1 li by (intro 1) (auto)
  }
  then show ?case
    using 1 by fastforce
qed

lemma gso_int_tail: "gso_int_tail i = gso_int i i"
proof (cases "0 < i")
  assume i: "0 < i"
  then have "gso_int_tail i = gso_int_tail' i (Suc 0) (gso_int i 1)"
    by (subst gso_int_tail.simps) (auto)
  also have "\<dots> = gso_int i i"
    using i by (intro gso_int_tail') (auto intro!: gso_int_tail')
  finally show "gso_int_tail i = gso_int i i"
    by simp
qed (auto)

end

locale gso_array
begin

function while :: "nat \<Rightarrow> nat \<Rightarrow> int vec iarray \<Rightarrow> int iarray iarray \<Rightarrow> int vec \<Rightarrow> int vec" where
  "while i l gsa dmusa acc =  (if l \<ge> i then acc
    else (let v = dmusa !! l !! l \<cdot>\<^sub>v acc - dmusa !! i !! l \<cdot>\<^sub>v gsa !! l;
              acc' = (map_vec (\<lambda>k. k div dmusa !! (l - 1) !! (l - 1)) v)
        in while i (l + 1) gsa dmusa acc'))"
  by pat_completeness auto
termination
  by  (relation "(\<lambda>(i,l,acc). i - l)  <*mlex*> {}",  goal_cases) (auto intro!: mlex_less wf_mlex)

declare while.simps[simp del]

definition gso' where
  "gso' i fsa gsa dmusa = (if i = 0 then fsa !! 0 else
     let acc = dmusa !! 0 !! 0 \<cdot>\<^sub>v fsa !! i - dmusa !! i !! 0 \<cdot>\<^sub>v fsa !! 0 in
     while i 1 gsa dmusa acc)"

function gsos' where
  "gsos' i n dmusa fsa gsa = (if i \<ge> n then gsa else
    gsos' (i + 1) n dmusa fsa (iarray_append gsa (gso' i fsa gsa dmusa)))"
  by pat_completeness auto
termination
  by  (relation "(\<lambda>(i,n,dmusa,fsa,gsa). n - i)  <*mlex*> {}",  goal_cases) (auto intro!: mlex_less wf_mlex)

declare gsos'.simps[simp del]

definition gso'_array where
  "gso'_array dmusa fs = gsos' 0 (length fs) dmusa (IArray fs) (IArray [])"

definition gso_array where
  "gso_array fs = (let dmusa = d\<mu>_impl fs; gsa = gso'_array dmusa fs
                   in IArray.of_fun (\<lambda>i. (if i = 0 then 1 else inverse (rat_of_int (dmusa !! (i - 1) !! (i - 1))))
                      \<cdot>\<^sub>v of_int_hom.vec_hom (gsa !! i)) (length fs))"

end

declare gso_array.gso_array_def[code]
declare gso_array.gso'_array_def[code]
declare gso_array.gsos'.simps[code]
declare gso_array.gso'_def[code]
declare gso_array.while.simps[code]

lemma map_vec_id[simp]: "map_vec id = id"
  by (auto intro!: eq_vecI)

context fs_int_indpt
begin

lemma "gso_array.gso'_array (d\<mu>_impl fs) fs = IArray (map (\<lambda>k. gso_int k k) [0..<length fs])"
proof -
  have a[simp]: "IArray (IArray.list_of a) = a" for a:: "'a iarray"
    by (metis iarray.exhaust list_of.simps)
  have [simp]: "length (IArray.list_of (iarray_append xs x)) = Suc (IArray.length xs)" for x xs
    unfolding iarray_append_code by (simp)
  have [simp]: "map_iarray f as = IArray (map f (IArray.list_of as))" for f as
    by (metis a iarray.simps(4))
  have d[simp]: "IArray.list_of (IArray.list_of (d\<mu>_impl fs) ! i) ! j = \<mu>' i j"
    if "i < length fs" "j \<le> i" for j i
    using that by (auto simp add: \<mu>' d\<mu>_impl nth_append)
  let ?rat_vec = "of_int_hom.vec_hom"
  have *: "gso_array.while i j gsa (d\<mu>_impl fs) acc = gso_int_tail' i j acc'"
      if "i < length fs" "j \<le> i" "acc = acc'"
         "\<And>k. k < i \<Longrightarrow> gsa !! k = gso_int k k" for i j gsa acc acc'
    using that apply (induction i j acc arbitrary: acc' rule: gso_int_tail'.induct)
    by (subst gso_array.while.simps, subst gso_int_tail'.simps, auto)
  then have *: "gso_array.gso' i (IArray fs) gsa (d\<mu>_impl fs) = gso_int i i"
    if assms: "i < length fs" "\<And>k. k < i \<Longrightarrow> gsa !! k = gso_int k k" for i gsa
  proof -
    have "IArray.list_of (IArray.list_of (d\<mu>_impl fs) ! 0) ! 0 = \<mu>' 0 0"
      using that by (subst d) (auto)
    then have "gso_array.gso' i (IArray fs) gsa (d\<mu>_impl fs) = gso_int_tail i"
      unfolding gso_array.gso'_def gso_int_tail.simps Let_def
      using that * by (auto simp del: gso_int_tail'.simps)
    then show ?thesis
      using gso_int_tail by simp
  qed
  then have *: "gso_array.gsos' i n (d\<mu>_impl fs) (IArray fs) gsa =
         IArray (IArray.list_of gsa @ (map (\<lambda>k. gso_int k k) [i..<n]))"
    if "n \<le> length fs"
       "gsa = IArray.of_fun (\<lambda>k. gso_int k k) i" for i n gsa
    using that proof (induction i n "(d\<mu>_impl fs)" "(IArray fs)" gsa rule: gso_array.gsos'.induct)
    case (1 i n gsa)
    { assume i_n: "i < n"
      have [simp]: "gso_array.gso' i (IArray fs) gsa (d\<mu>_impl fs) = gso_int i i"
        using 1 i_n by (intro *) auto
      have "gso_array.gsos' i n (d\<mu>_impl fs) (IArray fs) gsa = gso_array.gsos' (i + 1) n (d\<mu>_impl fs) (IArray fs) (iarray_append gsa (gso_array.gso' i (IArray fs) gsa (d\<mu>_impl fs)))"
        using i_n by (simp add: gso_array.gsos'.simps)
      also have "\<dots> = IArray (IArray.list_of gsa @ gso_int i i # map (\<lambda>k. gso_int k k) [Suc i..<n])"
        using 1 i_n by (subst 1) (auto simp add: iarray_append_code)
      also have "\<dots> = IArray (IArray.list_of gsa @ map (\<lambda>k. gso_int k k) [i..<n])"
        using i_n by (auto simp add: upt_conv_Cons)
      finally have ?case
        by simp }
    then show ?case
      by (auto simp add: gso_array.gsos'.simps)
  qed
  then show ?thesis
    unfolding gso_array.gso'_array_def by (subst *) auto
qed

end

subsection \<open>Lemmas Summarizing All Bounds During GSO Computation\<close>

context gram_schmidt_fs_int
begin

lemma combined_size_bound_integer:  
  assumes x: "x \<in> {fs ! i $ j | i j. i < m \<and> j < n} 
    \<union> {\<mu>' i j | i j. j \<le> i \<and> i < m}
    \<union> {\<sigma> l i j | i j l. i < m \<and> j \<le> i \<and> l \<le> j}" 
    (is "x \<in> ?fs \<union> ?\<mu>' \<union> ?\<sigma>")
    and m: "m \<noteq> 0"
  shows "\<bar>x\<bar> \<le> of_nat m * N ^ (3 * Suc m)"
proof -
  let ?m = "(of_nat m)::'a::trivial_conjugatable_linordered_field"
  have [simp]: "1 \<le> ?m"
    using m by (metis Num.of_nat_simps One_nat_def Suc_leI neq0_conv of_nat_mono)
  have [simp]: "\<bar>(of_int z)::'a::trivial_conjugatable_linordered_field\<bar> \<le> (of_int z)\<^sup>2" for z
    using abs_leq_squared by (metis of_int_abs of_int_le_iff of_int_power)
  have "\<bar>fs ! i $ j\<bar> \<le> of_nat m * N ^ (3 * Suc m)" if "i < m" "j < n" for i j
  proof -
    have "\<bar>fs ! i $ j\<bar> \<le> \<bar>fs ! i $ j\<bar>\<^sup>2"
      by (rule Ints_cases[of "fs ! i $ j"]) (use fs_int that in auto)
    also have "\<bar>fs ! i $ j\<bar>\<^sup>2 \<le> \<parallel>fs ! i\<parallel>\<^sup>2"
      using that by (intro vec_le_sq_norm) (auto)
    also have "... \<le> 1 * N"
      using N_fs that by auto
    also have "\<dots> \<le> of_nat m * N ^ (3 * Suc m)"
      using m N_1 by (intro mult_mono) (auto intro!: mult_mono self_le_power)
    finally show ?thesis
      by (auto)
  qed
  then have "\<bar>x\<bar> \<le> of_nat m * N ^ (3 * Suc m)" if "x \<in> ?fs"
    using that by auto
  moreover have "\<bar>x\<bar> \<le> of_nat m * N ^ (3 * Suc m)" if "x \<in> ?\<mu>'"
  proof -
    have "\<bar>\<mu>' i j\<bar> \<le> of_nat m * N ^ (3 + 3 * m)" if "j \<le> i" "i < m" for i j
    proof -
      have "\<mu>' i j \<in> \<int>"
        unfolding \<mu>'_def using that d_mu_Ints by auto
      then have "\<bar>\<mu>' i j\<bar> \<le> (\<mu>' i j)\<^sup>2"
        by (rule Ints_cases[of "\<mu>' i j"]) auto
      also have "\<dots> \<le> N ^ (3 * Suc j)"
        using that N_\<mu>' by auto
      also have "\<dots> \<le> 1 * N ^ (3 * Suc m)"
        using that assms N_1 by (auto intro!: power_increasing)
      also have "\<dots> \<le> of_nat m * N ^ (3 * Suc m)"
        using N_ge_0 assms zero_le_power by (intro mult_mono) auto
      finally show ?thesis
        by auto
    qed
    then show ?thesis
      using that by auto
  qed
  moreover have "\<bar>x\<bar> \<le> of_nat m * N ^ (3 * Suc m)" if "x \<in> ?\<sigma>"
  proof -
    have "\<bar>\<sigma> l i j\<bar> \<le> of_nat m * N ^ (3 + 3 * m)" if "i < m" "j \<le> i" "l \<le> j" for i j l
    proof -
      have "\<bar>\<sigma> l i j\<bar> \<le> of_nat l * N ^ (2 * l + 2)"
        using that N_\<sigma> by auto
      also have "\<dots> \<le> of_nat m * N ^ (2 * l + 2)"
        using that N_ge_0 assms zero_le_power by (intro mult_mono) auto
      also have "\<dots> \<le> of_nat m * N ^ (3 * Suc m)"
      proof -
        have "N ^ (2 * l + 2) \<le> N ^ (3 * Suc m)"
          using that assms N_1 by (intro power_increasing) (auto intro!: power_increasing)
        then show ?thesis
          using that assms N_1 by (intro mult_mono) (auto)
      qed
      finally show ?thesis
        by simp
    qed
    then show ?thesis
      using that by (auto)
  qed
  ultimately show ?thesis
    using assms by auto
qed

end (* gram_schmidt_fs_int *)

 (* "x \<noteq> 0 \<Longrightarrow> log 2 \<bar>x\<bar> \<le> 2 * m * log 2 N       + m + log 2 m" (is "_ \<Longrightarrow> ?l1 \<le> ?b1")
  "x \<noteq> 0 \<Longrightarrow> log 2 \<bar>x\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m" (is "_ \<Longrightarrow> _ \<le> ?b2") *)

context fs_int_indpt
begin


lemma combined_size_bound_rat_log:  
  assumes x: "x \<in> {gs.\<mu>' i j | i j. j \<le> i \<and> i < m}
    \<union> {gs.\<sigma> l i j | i j l. i < m \<and> j \<le> i \<and> l \<le> j}" 
    (is "x \<in> ?\<mu>' \<union> ?\<sigma>")
    and m: "m \<noteq> 0" "x \<noteq> 0"
  shows "log 2 \<bar>real_of_rat x\<bar> \<le> log 2 m + (3 + 3 * m) * log 2 (real_of_rat gs.N)"
proof -
  let ?r_fs = "map of_int_hom.vec_hom fs::rat vec list"
  have 1: "map of_int_hom.vec_hom fs ! i $ j = of_int (fs ! i $ j)" if "i < m" "j < n" for i j
    using that by auto
  then have "{?r_fs ! i $ j |i j. i < length ?r_fs \<and> j < n} = 
             {rat_of_int (fs ! i $ j) |i j. i < length fs \<and> j < n}"
    by (metis (mono_tags, hide_lams) length_map)
  then have "x \<in> {?r_fs ! i $ j |i j. i < length (map of_int_hom.vec_hom fs) \<and> j < n}
                 \<union> {gs.\<mu>' i j |i j. j \<le> i \<and> i < length ?r_fs}
                 \<union> {gs.\<sigma> l i j |i j l. i < length ?r_fs \<and> j \<le> i \<and> l \<le> j}"
    using assms by auto
  then have 1: "\<bar>x\<bar> \<le> rat_of_nat (length ?r_fs) * gs.N ^ (3 * Suc (length ?r_fs))" (is "?ax \<le> ?t")
    using assms by (intro gs.combined_size_bound_integer) auto
  then have 1: "real_of_rat ?ax \<le> real_of_rat ?t"
    using of_rat_less_eq 1 by auto
  have 2: "\<bar>real_of_rat x\<bar> = real_of_rat \<bar>x\<bar>"
    by auto
  have "log 2 \<bar>real_of_rat x\<bar> \<le> log 2 (real_of_rat ?t)"
  proof -
    have "0 < rat_of_nat (length fs) * gs.N ^ (3 + 3 * length fs)"
      using assms gs.N_1 by (auto)
    then show ?thesis
      using 1 assms by (subst log_le_cancel_iff) (auto)
  qed
  also have "real_of_rat ?t = real m * real_of_rat gs.N ^ (3 + 3 * m)"
    by (auto simp add: of_rat_mult of_rat_power)
  also have "log 2 (m * real_of_rat gs.N ^ (3 + 3 * m)) = log 2 m + log 2 (real_of_rat gs.N ^ (3 + 3 * m))"
    using gs.N_1 assms by (subst log_mult) auto
  also have "log 2 (real_of_rat gs.N ^ (3 + 3 * m)) = real (3 + 3 * length fs) * log 2 (real_of_rat gs.N)"
    using gs.N_1 assms by (subst log_nat_power) auto
  finally show ?thesis
    by (auto)
qed

lemma combined_size_bound_integer_log:  
  assumes x: "x \<in> {\<mu>' i j | i j. j \<le> i \<and> i < m}
    \<union> {\<sigma>s l i j | i j l. i < m \<and> j \<le> i \<and> l < j}" 
    (is "x \<in> ?\<mu>' \<union> ?\<sigma>")
    and m: "m \<noteq> 0" "x \<noteq> 0"
  shows "log 2 \<bar>real_of_int x\<bar> \<le> log 2 m + (3 + 3 * m) * log 2 (real_of_rat gs.N)"
proof -
  let ?x = "rat_of_int x" 
  from m have m: "m \<noteq> 0" "?x \<noteq> 0" by auto
  show ?thesis
  proof (rule order_trans[OF _ combined_size_bound_rat_log[OF _ m]], force)
    from x consider (1) i j where "x = \<mu>' i j" "j \<le> i" "i < m" 
      | (2) l i j where "x = \<sigma>s l i j" "i < m" "j \<le> i" "l < j" by blast
    thus "?x \<in> {gs.\<mu>' i j |i j. j \<le> i \<and> i < m} \<union> {gs.\<sigma> l i j |i j l. i < m \<and> j \<le> i \<and> l \<le> j}" 
    proof (cases)
      case (1 i j)
      with \<sigma>s_\<mu>'(2) show ?thesis by blast
    next
      case (2 l i j)
      hence "Suc l \<le> j" by auto
      from \<sigma>s_\<mu>'(1) 2 this show ?thesis by blast
    qed
  qed
qed

end
end
