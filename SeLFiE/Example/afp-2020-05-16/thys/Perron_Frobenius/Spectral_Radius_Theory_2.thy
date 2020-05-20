(* Author: Thiemann *)
section \<open>Combining Spectral Radius Theory with Perron Frobenius theorem\<close>

theory Spectral_Radius_Theory_2
imports
  Spectral_Radius_Largest_Jordan_Block
  Hom_Gauss_Jordan
begin

hide_const(open) Coset.order

lemma jnf_complexity_generic: fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat n n"
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x \<le> 1"
  and 1: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x = 1 \<Longrightarrow>
    order x (char_poly A) > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A x). bsize \<le> d + 1)"
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)"
proof -
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])"
    and lenn: "length as = n" by auto
  from jordan_nf_exists[OF A cA] obtain n_xs where jnf: "jordan_nf A n_xs" ..
  have dd: "x ^ d = x ^((d + 1) - 1)" for x by simp
  show ?thesis unfolding dd
  proof (rule jordan_nf_matrix_poly_bound[OF A _ _ jnf])
    fix n x
    assume nx: "(n,x) \<in> set n_xs"
    from jordan_nf_block_size_order_bound[OF jnf nx]
    have no: "n \<le> order x (char_poly A)" by auto
    {
      assume "0 < n"
      with no have "order x (char_poly A) \<noteq> 0" by auto
      hence rt: "poly (char_poly A) x = 0" unfolding order_root by auto
      from sr[OF this] show "cmod x \<le> 1" .
      note rt
    } note sr = this
    assume c1: "cmod x = 1"
    show "n \<le> d + 1"
    proof (rule ccontr)
      assume "\<not> n \<le> d + 1"
      hence lt: "n > d + 1" by auto
      with sr have rt: "poly (char_poly A) x = 0" by auto
      from lt no have ord: "d + 1 < order x (char_poly A)" by auto
      from 1[OF rt c1 ord, unfolded compute_set_of_jordan_blocks[OF jnf]] nx lt
      show False by force
    qed
  qed
qed

lemma norm_bound_complex_to_real: fixes A :: "real mat"
  assumes A: "A \<in> carrier_mat n n"
    and bnd: "\<exists>c1 c2. \<forall>k. norm_bound ((map_mat complex_of_real A) ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)"
proof -
  let ?B = "map_mat complex_of_real A"
  from bnd obtain c1 c2 where nb: "\<And> k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ d)" by auto
  show ?thesis
  proof (rule exI[of _ c1], rule exI[of _ c2], intro allI impI)
    fix k a
    assume "a \<in> elements_mat (A ^\<^sub>m k)"
    with pow_carrier_mat[OF A] obtain i j where a: "a = (A ^\<^sub>m k) $$ (i,j)" and ij: "i < n" "j < n"
      unfolding elements_mat by force
    from ij nb[of k] A have "norm ((?B ^\<^sub>m k) $$ (i,j)) \<le> c1 + c2 * real k ^ d"
      unfolding norm_bound_def by auto
    also have "(?B ^\<^sub>m k) $$ (i,j) = of_real a"
      unfolding of_real_hom.mat_hom_pow[OF A, symmetric] a using ij A by auto
    also have "norm (complex_of_real a) = abs a" by auto
    finally show "abs a \<le> (c1 + c2 * real k ^ d)" .
  qed
qed

lemma dim_gen_eigenspace_max_jordan_block: assumes jnf: "jordan_nf A n_as" 
  shows "dim_gen_eigenspace A l d = order l (char_poly A) \<longleftrightarrow> 
    (\<forall> n. (n,l) \<in> set n_as \<longrightarrow> n \<le> d)" 
proof -
  let ?list = "[(n, e)\<leftarrow>n_as . e = l]"   
  define list where "list = [na\<leftarrow>n_as . snd na = l]" 
  have list: "?list = list" unfolding list_def by (induct n_as, force+)
  have id: "(\<forall>n. (n, l) \<in> set n_as \<longrightarrow> n \<le> d) = (\<forall> n \<in> set (map fst list). n \<le> d)" 
    unfolding list_def by auto
  define ns where "ns = map fst list" 
  show ?thesis
    unfolding dim_gen_eigenspace[OF jnf] jordan_nf_order[OF jnf] list list_def[symmetric] id
    unfolding ns_def[symmetric]
  proof (induct ns)
    case (Cons n ns)
    show ?case
    proof (cases "n \<le> d")
      case True
      thus ?thesis using Cons by auto
    next
      case False
      hence "n > d" by auto
      moreover have "sum_list (map (min d) ns) \<le> sum_list ns" by (induct ns, auto)
      ultimately show ?thesis by auto
    qed
  qed auto
qed

lemma jnf_complexity_1_complex: fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "real_nonneg_mat A" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x \<le> 1" 
  and 1: "poly (char_poly A) 1 = 0 \<Longrightarrow>  
    order 1 (char_poly A) > d + 1 \<Longrightarrow> 
    dim_gen_eigenspace A 1 (d+1) = order 1 (char_poly A)" 
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)" 
proof - 
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and lenn: "length as = n" by auto 
  from jordan_nf_exists[OF A cA] obtain n_as where jnf: "jordan_nf A n_as" ..
  have dd: "x ^ d = x ^((d + 1) - 1)" for x by simp
  let ?n = n
  show ?thesis unfolding dd
  proof (rule jordan_nf_matrix_poly_bound[OF A _ _ jnf])
    fix n a
    assume na: "(n,a) \<in> set n_as" 
    from jordan_nf_root_char_poly[OF jnf na]
    have rt: "poly (char_poly A) a = 0" by auto
    with degree_monic_char_poly[OF A] have n0: "?n > 0" 
      by (cases ?n, auto dest: degree0_coeffs)
    from sr[OF rt] show "cmod a \<le> 1" .
    assume a: "cmod a = 1" 
    from rt have "a \<in> spectrum A" using A spectrum_root_char_poly by auto
    hence 11: "1 \<in> cmod ` spectrum A" using a by auto
    note spec = spectral_radius_mem_max[OF A n0]
    from spec(2)[OF 11] have le: "1 \<le> spectral_radius A" .
    from spec(1)[unfolded spectrum_root_char_poly[OF A]] sr have "spectral_radius A \<le> 1" by auto
    with le have sr: "spectral_radius A = 1" by auto
    show "n \<le> d + 1" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence nd: "n > d + 1" by auto
      from real_nonneg_mat_spectral_radius_largest_jordan_block[OF nonneg jnf na, unfolded sr a]
      obtain N where N: "N \<ge> n" and mem: "(N, 1) \<in> set n_as" by auto
      from jordan_nf_root_char_poly[OF jnf mem] have rt: "poly (char_poly A) 1 = 0" .
      from jordan_nf_block_size_order_bound[OF jnf mem] have "N \<le> order 1 (char_poly A)" .
      with N nd have "d + 1 < order 1 (char_poly A)" by simp
      from 1[OF rt this, unfolded dim_gen_eigenspace_max_jordan_block[OF jnf]] mem N nd 
      show False by force
    qed
  qed
qed

lemma jnf_complexity_1_real: fixes A :: "real mat"
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and jb: "poly (char_poly A) 1 = 0 \<Longrightarrow>  
    order 1 (char_poly A) > d + 1 \<Longrightarrow> 
    dim_gen_eigenspace A 1 (d+1) = order 1 (char_poly A)" 
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> \<bar>a\<bar> \<le> c1 + c2 * real k ^ d"
proof -
  let ?c = "complex_of_real" 
  let ?A = "map_mat ?c A"
  have A': "?A \<in> carrier_mat n n" using A by auto
  have nn: "real_nonneg_mat ?A" using nonneg A unfolding nonneg_mat_def real_nonneg_mat_def 
    by (force simp: elements_mat)
  have 1: "1 = ?c 1" by auto
  note cp = of_real_hom.char_poly_hom[OF A]
  have hom: "map_poly_inj_idom_divide_hom complex_of_real" ..
  show ?thesis
  proof (rule norm_bound_complex_to_real[OF A jnf_complexity_1_complex[OF A' nn]],
      unfold cp of_real_hom.poly_map_poly_1, unfold 1
      of_real_hom.hom_dim_gen_eigenspace[OF A]
      map_poly_inj_idom_divide_hom.order_hom[OF hom], goal_cases)
    case 2 
    thus ?case using jb by auto
  next
    case (1 x)
    let ?cp = "char_poly A" 
    assume rt: "poly (map_poly ?c ?cp) x = 0" 
    with degree_monic_char_poly[OF A', unfolded cp] have n0: "n \<noteq> 0" 
      using degree0_coeffs[of ?cp] by (cases n, auto)
    from perron_frobenius_nonneg[OF A nonneg n0]
    obtain sr ks f where sr0: "0 \<le> sr" and ks: "0 \<notin> set ks" "ks \<noteq> []"
      and cp: "?cp = (\<Prod>k\<leftarrow>ks. monom 1 k - [:sr ^ k:]) * f" 
      and rtf: "poly (map_poly ?c f) x = 0 \<Longrightarrow> cmod x < sr" by auto
    have sr_rt: "poly ?cp sr = 0" unfolding cp poly_prod_list_zero_iff poly_mult_zero_iff using ks
      by (cases ks, auto simp: poly_monom)
    from sr[OF sr_rt] have sr1: "sr \<le> 1" .
    interpret c: map_poly_comm_ring_hom ?c ..
    from rt[unfolded cp c.hom_mult c.hom_prod_list poly_mult_zero_iff poly_prod_list_zero_iff]   
    show "cmod x \<le> 1" 
    proof (standard, goal_cases)
      case 2
      with rtf sr1 show ?thesis by auto
    next
      case 1
      from this ks obtain p where p: "p \<in> set ks" 
        and rt: "poly (map_poly ?c (monom 1 p - [:sr ^ p:])) x = 0" by auto
      from p ks(1) have p: "p \<noteq> 0" by metis
      from rt have "x^p = (?c sr)^p" unfolding c.hom_minus 
        by (simp add: poly_monom of_real_hom.map_poly_pCons_hom)
      hence "cmod x = cmod (?c sr)" using p power_eq_imp_eq_norm by blast
      with sr0 sr1 show "cmod x \<le> 1" by auto
    qed
  qed
qed
end