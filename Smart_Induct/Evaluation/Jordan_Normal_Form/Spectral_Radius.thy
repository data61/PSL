(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Spectral Radius Theory\<close>

text \<open>The following results show that the spectral radius characterize polynomial growth
  of matrix powers.\<close>

theory Spectral_Radius
imports
  Jordan_Normal_Form_Existence
begin

definition "spectrum A = Collect (eigenvalue A)"

lemma spectrum_root_char_poly: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n"
  shows "spectrum A = {k. poly (char_poly A) k = 0}"
  unfolding spectrum_def eigenvalue_root_char_poly[OF A, symmetric] by auto

lemma card_finite_spectrum: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n"
  shows "finite (spectrum A)" "card (spectrum A) \<le> n"
proof -
  define CP where "CP = char_poly A"
  from spectrum_root_char_poly[OF A] have id: "spectrum A = { k. poly CP k = 0}"
    unfolding CP_def by auto
  from degree_monic_char_poly[OF A] have d: "degree CP = n" and c: "coeff CP n = 1"
    unfolding CP_def by auto
  from c have "CP \<noteq> 0" by auto
  from poly_roots_finite[OF this]
  show "finite (spectrum A)" unfolding id .
  from poly_roots_degree[OF \<open>CP \<noteq> 0\<close>]
  show "card (spectrum A) \<le> n" unfolding id using d by simp
qed

lemma spectrum_non_empty: assumes A: "(A :: complex mat) \<in> carrier_mat n n"
  and n: "n > 0"
  shows "spectrum A \<noteq> {}"
proof - 
  define CP where "CP = char_poly A"
  from spectrum_root_char_poly[OF A] have id: "spectrum A = { k. poly CP k = 0}"
    unfolding CP_def by auto
  from degree_monic_char_poly[OF A] have d: "degree CP > 0" using n
    unfolding CP_def by auto
  hence "\<not> constant (poly CP)" by (simp add: constant_degree)
  from fundamental_theorem_of_algebra[OF this] show ?thesis unfolding id by auto
qed

definition spectral_radius :: "complex mat \<Rightarrow> real" where 
  "spectral_radius A = Max (norm ` spectrum A)"

lemma spectral_radius_mem_max: assumes A: "A \<in> carrier_mat n n"
  and n: "n > 0"
  shows "spectral_radius A \<in> norm ` spectrum A" (is ?one)
  "a \<in> norm ` spectrum A \<Longrightarrow> a \<le> spectral_radius A"
proof -
  define SA where "SA = norm ` spectrum A"
  from card_finite_spectrum[OF A]
  have fin: "finite SA" unfolding SA_def by auto
  from spectrum_non_empty[OF A n] have ne: "SA \<noteq> {}" unfolding SA_def by auto
  note d = spectral_radius_def SA_def[symmetric] Sup_fin_Max[symmetric]
  show ?one unfolding d
    by (rule Sup_fin.closed[OF fin ne], auto simp: sup_real_def)
  assume "a \<in> norm ` spectrum A"
  thus "a \<le> spectral_radius A" unfolding d
    by (intro Sup_fin.coboundedI[OF fin])
qed

text \<open>If spectral radius is at most 1, and JNF exists, then we have polynomial growth.\<close>

lemma spectral_radius_jnf_norm_bound_le_1: assumes A: "A \<in> carrier_mat n n"
  and sr_1: "spectral_radius A \<le> 1"
  and jnf_exists: "\<exists> n_as. jordan_nf A n_as"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (n - 1))"
proof -
  let ?p = "char_poly A"
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and len: "length as = n" by auto  
  show ?thesis
  proof (rule factored_char_poly_norm_bound[OF A cA jnf_exists])
    fix a
    show "length (filter ((=) a) as) \<le> n" using len by auto
    assume "a \<in> set as"
    from linear_poly_root[OF this]
    have "poly ?p a = 0" unfolding cA by simp
    with spectrum_root_char_poly[OF A] 
    have mem: "norm a \<in> norm ` spectrum A" by auto
    with card_finite_spectrum[OF A] have "n > 0" by (cases n, auto)
    from spectral_radius_mem_max(2)[OF A this mem] sr_1 
    show "norm a \<le> 1" by auto
  qed
qed

text \<open>If spectral radius is smaller than 1, and JNF exists, then we have a constant bound.\<close>

lemma spectral_radius_jnf_norm_bound_less_1: assumes A: "A \<in> carrier_mat n n"
  and sr_1: "spectral_radius A < 1"
  and jnf_exists: "\<exists> n_as. jordan_nf A n_as" 
  shows "\<exists> c. \<forall> k. norm_bound (A ^\<^sub>m k) c"
proof -
  let ?p = "char_poly A"
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
  have "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (0 - 1))"
  proof (rule factored_char_poly_norm_bound[OF A cA jnf_exists])
    fix a
    assume "a \<in> set as"
    from linear_poly_root[OF this]
    have "poly ?p a = 0" unfolding cA by simp
    with spectrum_root_char_poly[OF A] 
    have mem: "norm a \<in> norm ` spectrum A" by auto
    with card_finite_spectrum[OF A] have "n > 0" by (cases n, auto)
    from spectral_radius_mem_max(2)[OF A this mem] sr_1 
    have lt: "norm a < 1" by auto
    thus "norm a \<le> 1" by auto
    from lt show "norm a = 1 \<Longrightarrow> length (filter ((=) a) as) \<le> 0" by auto
  qed
  thus ?thesis by auto
qed

text \<open>If spectral radius is larger than 1, than we have exponential growth.\<close>

lemma spectral_radius_gt_1: assumes A: "A \<in> carrier_mat n n"
  and n: "n > 0"
  and sr_1: "spectral_radius A > 1"
  shows "\<exists> v c. v \<in> carrier_vec n \<and> norm c > 1 \<and> v \<noteq> 0\<^sub>v n \<and> A ^\<^sub>m k *\<^sub>v v = c^k \<cdot>\<^sub>v v"
proof -
  from sr_1 spectral_radius_mem_max[OF A n] obtain ev 
    where ev: "ev \<in> spectrum A" and gt: "norm ev > 1" by auto
  from ev[unfolded spectrum_def eigenvalue_def[abs_def]] 
    obtain v where ev: "eigenvector A v ev" by auto
  from eigenvector_pow[OF A this] this[unfolded eigenvector_def] A gt
  show ?thesis
    by (intro exI[of _ v], intro exI[of _ ev], auto)
qed


text \<open>If spectral radius is at most 1 for a complex matrix, then we have polynomial growth.\<close>

lemma spectral_radius_jnf_norm_bound_le_1_upper_triangular: assumes A: "(A :: complex mat) \<in> carrier_mat n n"
  and sr_1: "spectral_radius A \<le> 1"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (n - 1))"
  by (rule spectral_radius_jnf_norm_bound_le_1[OF A sr_1],
    insert char_poly_factorized[OF A] jordan_nf_exists[OF A], blast)

text \<open>If spectral radius is less than 1 for a complex matrix, then we have a constant bound.\<close>

lemma spectral_radius_jnf_norm_bound_less_1_upper_triangular: assumes A: "(A :: complex mat) \<in> carrier_mat n n"
  and sr_1: "spectral_radius A < 1"
  shows "\<exists> c. \<forall> k. norm_bound (A ^\<^sub>m k) c"
  by (rule spectral_radius_jnf_norm_bound_less_1[OF A sr_1],
    insert char_poly_factorized[OF A] jordan_nf_exists[OF A], blast)

text \<open>And we can also get a quantative approximation via the multiplicity of the eigenvalues.\<close>

lemma spectral_radius_poly_bound: fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat n n" 
  and sr_1: "spectral_radius A \<le> 1"
  and eq_1: "\<And> ev k. poly (char_poly A) ev = 0 \<Longrightarrow> norm ev = 1 \<Longrightarrow> Polynomial.order ev (char_poly A) \<le> d"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))"
proof -
  {
    fix ev
    assume "poly (char_poly A) ev = 0"
    with eigenvalue_root_char_poly[OF A] have ev: "eigenvalue A ev" by simp
    hence "norm ev \<in> norm ` spectrum A" unfolding spectrum_def by auto
    from spectral_radius_mem_max(2)[OF A eigenvalue_imp_nonzero_dim[OF A ev] this] sr_1    
    have "norm ev \<le> 1" by auto
  } note le_1 = this
  let ?p = "char_poly A"
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and lenn: "length as = n" by auto 
  from degree_monic_char_poly[OF A] have deg: "degree (char_poly A) = n" by auto
  show ?thesis
  proof (rule factored_char_poly_norm_bound[OF A cA jordan_nf_exists[OF A]], rule cA) 
    fix ev
    assume "ev \<in> set as"
    hence root: "poly (char_poly A) ev = 0" unfolding cA by (rule linear_poly_root)
    from le_1[OF root] show "norm ev \<le> 1" .
    let ?k = "length (filter ((=) ev) as)"
    have len: "length (filter ((=) (- ev)) (map uminus as)) = length (filter ((=) ev) as)"
      by (induct as, auto)
    have prod: "(\<Prod>a\<leftarrow>map uminus as. [:a, 1:]) = (\<Prod>a\<leftarrow>as. [:- a, 1:])"
      by (induct as, auto)
    have dvd: "[:- ev, 1:] ^ ?k dvd char_poly A" unfolding cA using 
      poly_linear_exp_linear_factors_rev[of "- ev" "map uminus as"] 
      unfolding len prod .
    from \<open>ev \<in> set as\<close> deg lenn
    have "degree (char_poly A) \<noteq> 0" by (cases as, auto)
    hence "char_poly A \<noteq> 0" by auto
    from order_max[OF dvd this] have k: "?k \<le> Polynomial.order ev (char_poly A)" .
    assume "norm ev = 1"
    from eq_1[OF root this] k
    show "?k \<le> d" by simp
  qed
qed

end
