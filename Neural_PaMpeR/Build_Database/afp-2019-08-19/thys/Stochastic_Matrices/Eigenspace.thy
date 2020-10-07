section \<open>Eigenspaces\<close>

text \<open>Using results on Jordan-Normal forms, we prove that the geometric
  multiplicity of an eigenvalue (i.e., the dimension of the eigenspace)
  is bounded by the algebraic multiplicity of an eigenvalue (i.e., the
  multiplicity as root of the characteristic polynomial.).
  As a consequence we derive that any two eigenvectors of some
  eigenvalue with multiplicity 1 must be scalar multiples of each other.\<close>

theory Eigenspace
imports 
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
  Perron_Frobenius.Perron_Frobenius_Aux
begin
hide_const (open) Coset.order

text \<open>The dimension of every generalized eigenspace is bounded by the
  algebraic multiplicity of an eigenvalue. Hence, in particular the
  geometric multiplicity is smaller than the algebraic multiplicity.\<close>

lemma dim_gen_eigenspace_order_char_poly: assumes jnf: "jordan_nf A n_as"
  shows "dim_gen_eigenspace A lam k \<le> order lam (char_poly A)" 
  unfolding jordan_nf_order[OF jnf]  dim_gen_eigenspace[OF jnf]
  by (induct n_as, auto)

text \<open>Every eigenvector is contained in the eigenspace.\<close>
lemma eigenvector_mat_kernel_char_matrix: assumes A: "A \<in> carrier_mat n n" 
  and ev: "eigenvector A v lam" 
shows "v \<in> mat_kernel (char_matrix A lam)" 
  using ev[unfolded eigenvector_char_matrix[OF A]] A
  unfolding mat_kernel_def by (auto simp: char_matrix_def)

text \<open>If the algebraic multiplicity is one, then every two eigenvectors are
  scalar multiples of each other.\<close>
lemma unique_eigenvector_jnf: assumes jnf: "jordan_nf (A :: 'a :: field mat) n_as" 
  and ord: "order lam (char_poly A) = 1" 
  and ev: "eigenvector A v lam" "eigenvector A w lam" 
shows "\<exists> a. v = a \<cdot>\<^sub>v w" 
proof -
  let ?cA = "char_matrix A lam" 
  from similar_matD jnf[unfolded jordan_nf_def] obtain n where 
    A: "A \<in> carrier_mat n n" by auto
  from dim_gen_eigenspace_order_char_poly[OF jnf, of lam 1, unfolded ord]
  have dim: "kernel_dim ?cA \<le> 1" 
    unfolding dim_gen_eigenspace_def by auto
  from eigenvector_mat_kernel_char_matrix[OF A ev(1)]
  have vk: "v \<in> mat_kernel ?cA" .
  from eigenvector_mat_kernel_char_matrix[OF A ev(2)]
  have wk: "w \<in> mat_kernel ?cA" .
  from ev[unfolded eigenvector_def] A have 
    v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" and
    w: "w \<in> carrier_vec n" "w \<noteq> 0\<^sub>v n" by auto
  have cA: "?cA \<in> carrier_mat n n" using A
    unfolding char_matrix_def by auto
  interpret kernel n n ?cA
    by (unfold_locales, rule cA)
  from kernel_basis_exists[OF A] obtain B where B: "finite B" "basis B" by auto
  from this[unfolded Ker.basis_def] have basis: "mat_kernel ?cA = span B" by auto
  {
    assume "card B = 0" 
    with B basis have bas: "mat_kernel ?cA = local.span {}" by auto
    also have "\<dots> = {0\<^sub>v n}" unfolding Ker.span_def by auto
    finally have False using v vk by auto
  }
  with Ker.dim_basis[OF B] dim have "card B = Suc 0" by (cases "card B", auto)
  hence "\<exists> b. B = {b}" using card_eq_SucD by blast
  then obtain b where Bb: "B = {b}" by blast
  from B(2)[unfolded Bb Ker.basis_def] have bk: "b \<in> mat_kernel ?cA" by auto
  hence b: "b \<in> carrier_vec n" using cA mat_kernelD(1) by blast
  from Bb basis have "mat_kernel ?cA = span {b}" by auto
  also have "\<dots> = NC.span {b}" 
    by (rule span_same, insert bk, auto)
  also have "\<dots> \<subseteq> { a \<cdot>\<^sub>v b | a. True}"
  proof -
    {
      fix x
      assume "x \<in> NC.span {b}" 
      from this[unfolded NC.span_def] obtain a A 
        where x: "x = NC.lincomb a A" and A: "A \<subseteq> {b}" by auto
      hence "A = {} \<or> A = {b}" by auto
      hence "\<exists> a. x = a \<cdot>\<^sub>v b" 
      proof
        assume "A = {}" thus ?thesis unfolding x using b by (intro exI[of _ 0], auto)
      next
        assume "A = {b}" thus ?thesis unfolding x using b 
          by (intro exI[of _ "a b"], auto simp: NC.lincomb_def)
      qed
    }
    thus ?thesis by auto
  qed
  finally obtain vv ww where vb: "v = vv \<cdot>\<^sub>v b" and wb: "w = ww \<cdot>\<^sub>v b" using vk wk by force+
  from wb w b have ww: "ww \<noteq> 0" by auto
  from arg_cong[OF wb, of "\<lambda> x. inverse ww \<cdot>\<^sub>v x"] w ww b have "b = inverse ww \<cdot>\<^sub>v w" 
    by (auto simp: smult_smult_assoc)
  from vb[unfolded this smult_smult_assoc] show ?thesis by auto
qed  

text \<open>Getting rid of the JNF-assumption for complex matrices.\<close>
lemma unique_eigenvector_complex: assumes A: "A \<in> carrier_mat n n" 
  and ord: "order lam (char_poly A :: complex poly) = 1" 
  and ev: "eigenvector A v lam" "eigenvector A w lam" 
shows "\<exists> a. v = a \<cdot>\<^sub>v w" 
proof -
  from jordan_nf_exists[OF A] char_poly_factorized[OF A] obtain n_as
    where "jordan_nf A n_as" by auto
  from unique_eigenvector_jnf[OF this ord ev] show ?thesis .
qed

text \<open>Convert the result to real matrices via homomorphisms.\<close>

lemma unique_eigenvector_real: assumes A: "A \<in> carrier_mat n n" 
  and ord: "order lam (char_poly A :: real poly) = 1" 
  and ev: "eigenvector A v lam" "eigenvector A w lam" 
shows "\<exists> a. v = a \<cdot>\<^sub>v w" 
proof -
  let ?c = complex_of_real
  let ?A = "map_mat ?c A" 
  from A have cA: "?A \<in> carrier_mat n n" by auto
  have ord: "order (?c lam) (char_poly ?A) = 1" 
    unfolding of_real_hom.char_poly_hom[OF A]
    by (subst map_poly_inj_idom_divide_hom.order_hom, unfold_locales, rule ord)
  note evc = of_real_hom.eigenvector_hom[OF A]
  from unique_eigenvector_complex[OF cA ord evc evc, OF ev] obtain a :: complex 
    where id: "map_vec ?c v = a \<cdot>\<^sub>v map_vec ?c w" by auto
  (* now prove that a is real *)
  from ev[unfolded eigenvector_def] A have carr: "v \<in> carrier_vec n" "w \<in> carrier_vec n" 
    "v \<noteq> 0\<^sub>v n" by auto
  then obtain i where i: "i < n" "v $ i \<noteq> 0" unfolding Matrix.vec_eq_iff by auto
  from arg_cong[OF id, of "\<lambda> x. x $ i"] carr i 
  have "?c (v $ i) = a * ?c (w $ i)"
    by auto
  with i(2) have "a \<in> Reals"
    by (metis Reals_cnj_iff complex_cnj_complex_of_real complex_cnj_mult mult_cancel_right
        mult_eq_0_iff of_real_hom.hom_zero of_real_hom.injectivity)
  then obtain b where a: "a = ?c b" by (rule Reals_cases)
  from id[unfolded a] have "map_vec ?c v = map_vec ?c (b \<cdot>\<^sub>v w)" by auto
  hence "v = b \<cdot>\<^sub>v w" by (rule of_real_hom.vec_hom_inj)
  thus ?thesis by auto
qed

text \<open>Finally, the statement converted to HMA-world.\<close>
lemma unique_eigen_vector_real: assumes ord: "order lam (charpoly A :: real poly) = 1" 
  and ev: "eigen_vector A v lam" "eigen_vector A w lam" 
shows "\<exists> a. v = a *s w" using assms
proof (transfer, goal_cases)
  case (1 lam A v w)
  show ?case
    by (rule unique_eigenvector_real[OF 1(1-2,4,6)])
qed

end

