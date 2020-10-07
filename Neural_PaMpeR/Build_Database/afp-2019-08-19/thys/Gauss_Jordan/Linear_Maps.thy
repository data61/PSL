(*  
    Title:      Linear_Maps.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section\<open>Linear Maps\<close>

theory Linear_Maps
imports
    Gauss_Jordan
begin

lemma "((\<lambda>(x, y). (x::real , - y::real)) has_derivative (\<lambda>h. (fst h, - snd h))) (at x)"
  apply (rule has_derivative_eq_rhs)
   apply (rule has_derivative_split)

  apply (rule has_derivative_Pair)
  by (auto intro!: derivative_eq_intros)


subsection\<open>Properties about ranks and linear maps\<close>

lemma rank_matrix_dim_range:
assumes lf: "linear ((*s)) ((*s)) f"
shows "rank (matrix f::'a::{field}^'cols::{mod_type}^'rows::{mod_type}) = vec.dim (range f)"
unfolding rank_col_rank[of "matrix f"] col_rank_def
unfolding col_space_eq' using matrix_works[OF lf] by metis

text\<open>The following two lemmas are the demonstration of theorem 2.11 that appears the book "Advanced Linear Algebra" by Steven Roman.\<close>

lemma linear_injective_rank_eq_ncols:
  assumes lf: "linear ((*s)) ((*s)) f"
  shows "inj f \<longleftrightarrow> rank (matrix f::'a::{field}^'cols::{mod_type}^'rows::{mod_type}) = ncols (matrix f)"
proof (rule)
  interpret lf: Vector_Spaces.linear "((*s))" "((*s))" f using lf by simp
  assume inj: "inj f"
  hence "{x. f x = 0} = {0}" using lf.linear_injective_ker_0 by blast
  hence "vec.dim {x. f x = 0} = 0" using vec.dim_zero_eq' by blast
  thus "rank (matrix f) = ncols (matrix f)" using vec.rank_nullity_theorem unfolding ncols_def
    using rank_matrix_dim_range[OF lf]
    by (metis add.left_neutral lf.linear_axioms vec.dim_UNIV vec.dimension_def vec_dim_card)
next
  assume eq: "rank (matrix f::'a::{field}^'cols::{mod_type}^'rows::{mod_type}) = ncols (matrix f)"
  have "vec.dim {x. f x = 0} = 0"
    unfolding ncols_def
    using rank_matrix_dim_range[OF lf] eq
    by (metis cancel_comm_monoid_add_class.diff_cancel dim_null_space lf ncols_def
        null_space_eq_ker vec.dim_UNIV vec.dimension_def vec_dim_card)
  hence "{x. f x = 0} = {0}" using vec.dim_zero_eq
    using lf vec.linear_0 by auto
  thus "inj f" using vec.linear_injective_ker_0[of "matrix f"] 
    unfolding matrix_vector_mul(1)[OF lf] by simp
qed

lemma linear_surjective_rank_eq_ncols:
  assumes lf: "linear ((*s)) ((*s)) f"
  shows "surj f \<longleftrightarrow> rank (matrix f::'a::{field}^'cols::{mod_type}^'rows::{mod_type}) = nrows (matrix f)"
proof (rule)
  assume surj: "surj f"
  have "nrows (matrix f) = CARD ('rows)" unfolding nrows_def ..
  also have "... = vec.dim (range f)" by (metis surj vec_dim_card)
  also have "... = rank (matrix f)" unfolding rank_matrix_dim_range[OF lf] ..
  finally show "rank (matrix f) = nrows (matrix f)" ..
next
  assume "rank (matrix f) = nrows (matrix f)"
  hence "vec.dim (range f) = CARD ('rows)" unfolding rank_matrix_dim_range[OF lf] nrows_def .
  thus "surj f"
    using vec.basis_exists independent_is_basis is_basis_def lf
      vec.subspace_UNIV vec.subspace_image
    by (metis col_space_eq' col_space_eq_range vec.span_subspace)
qed

lemma linear_bij_rank_eq_ncols:
  fixes f::"('a::{field}^'n::{mod_type})=>('a::{field}^'n::{mod_type})"
  assumes lf: "linear ((*s)) ((*s)) f"
  shows "bij f \<longleftrightarrow> rank (matrix f) = ncols (matrix f)"
  unfolding bij_def
  using lf linear_injective_rank_eq_ncols vec.linear_inj_imp_surj by auto


subsection\<open>Invertible linear maps\<close>

locale invertible_lf = Vector_Spaces.linear +
  assumes invertible: "(\<exists>g. g \<circ> f = id \<and> f \<circ> g = id)"
begin

lemma invertible_lf: "(\<exists>g. linear ((*b)) ((*a)) g \<and> (g \<circ> f = id) \<and> (f \<circ> g = id))"
proof -
  have "inj_on f UNIV"
    using invertible by (auto simp: o_def id_def inj_on_def fun_eq_iff) metis
  from linear_exists_left_inverse_on[OF linear_axioms vs1.subspace_UNIV this] obtain g where
    g: "linear (*b) (*a) g" "g o f = id"
    by (auto simp: fun_eq_iff id_def module_hom_iff_linear)
  then have "f o g = id"
    using invertible
    by (auto simp: inj_on_def fun_eq_iff) metis
  with g show ?thesis by auto
qed

end

lemma (in Vector_Spaces.linear) invertible_lf_intro[intro]:
  assumes "(g \<circ> f = id)"  and "(f \<circ> g = id)"
  shows "invertible_lf ((*a)) ((*b)) f"
  using assms
  by unfold_locales auto

lemma invertible_imp_bijective:
  assumes "invertible_lf scaleB scaleC f"
  shows "bij f"
  using assms unfolding invertible_lf_def invertible_lf_axioms_def
  by (metis bij_betw_comp_iff bij_betw_imp_surj inj_on_imageI2 inj_on_imp_bij_betw inv_id surj_id surj_imp_inj_inv)

lemma invertible_matrix_imp_invertible_lf:
  fixes A::"'a::{field}^'n^'n"
  assumes invertible_A: "invertible A"
  shows "invertible_lf ((*s)) ((*s)) (\<lambda>x. A *v x)"
proof -
  obtain B where AB: "A**B=mat 1" and BA: "B**A=mat 1" using invertible_A unfolding invertible_def by blast
  show ?thesis 
  proof (rule vec.invertible_lf_intro [of "(\<lambda>x. B *v x)"]) 
    show id1: "(*v) B \<circ> (*v) A = id" by (metis (hide_lams, no_types) AB BA isomorphism_expand matrix_vector_mul_assoc matrix_vector_mul_lid) 
    show "(*v) A \<circ> (*v) B = id" by (metis (hide_lams, no_types) AB BA isomorphism_expand matrix_vector_mul_assoc matrix_vector_mul_lid) 
  qed
qed

lemma invertible_lf_imp_invertible_matrix:
  fixes f::"'a::{field}^'n\<Rightarrow>'a^'n"
  assumes invertible_f: "invertible_lf ((*s)) ((*s)) f"
  shows "invertible (matrix f)"
proof -
  interpret i: invertible_lf "((*s))" "((*s))" f using invertible_f .
  obtain g where linear_g: "linear ((*s)) ((*s))  g" and gf: "(g \<circ> f = id)" and fg: "(f \<circ> g = id)"
    by (metis invertible_f invertible_lf.invertible_lf)
  show ?thesis
  proof (unfold invertible_def, rule exI[of _ "matrix g"], rule conjI)
    show "matrix f ** matrix g = mat 1"
      unfolding matrix_eq matrix_vector_mul_assoc[symmetric]
      by (metis i.linear_axioms matrix_vector_mul_lid pointfree_idE fg linear_g matrix_vector_mul)
    show "matrix g ** matrix f = mat 1"
      by (metis \<open>matrix f ** matrix g = mat 1\<close> matrix_left_right_inverse)
  qed
qed

lemma invertible_matrix_iff_invertible_lf:
  fixes A::"'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> invertible_lf ((*s)) ((*s)) (\<lambda>x. A *v x)" 
  by (metis invertible_lf_imp_invertible_matrix invertible_matrix_imp_invertible_lf matrix_of_matrix_vector_mul)

lemma invertible_matrix_iff_invertible_lf':
  fixes  f::"'a::{field}^'n\<Rightarrow>'a^'n"
  assumes linear_f: "linear ((*s)) ((*s)) f"
  shows "invertible (matrix f) \<longleftrightarrow> invertible_lf ((*s)) ((*s)) f"
  by (metis (lifting) assms invertible_matrix_iff_invertible_lf matrix_vector_mul) 


lemma invertible_matrix_mult_right_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" 
    and Q::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  assumes invertible_Q: "invertible Q"
  shows "rank (A**Q) = rank A"
proof -
  define TQ where "TQ x = Q *v x" for x
  define TA where "TA x = A *v x" for x
  define TAQ where "TAQ x = (A**Q) *v x" for x
  have "invertible_lf ((*s)) ((*s)) TQ" using invertible_matrix_imp_invertible_lf[OF invertible_Q] unfolding TQ_def .
  hence bij_TQ: "bij TQ" using invertible_imp_bijective by auto
  have "range TAQ = range (TA \<circ> TQ)" unfolding TQ_def TA_def TAQ_def o_def matrix_vector_mul_assoc ..
  also have "... = TA `(range TQ)" unfolding fun.set_map ..
  also have "... = TA ` (UNIV)" using bij_is_surj[OF bij_TQ] by simp
  finally have "range TAQ = range TA" .
  thus ?thesis unfolding rank_eq_dim_image using TAQ_def [abs_def] TA_def [abs_def] by auto
qed

lemma subspace_image_invertible_mat:
  fixes P::"'a::{field}^'m^'m"
  assumes inv_P: "invertible P"
    and sub_W: "vec.subspace W"
  shows "vec.subspace ((\<lambda>x. P *v x)` W)"
  using assms by (intro vec.subspace_image)

lemma dim_image_invertible_mat:
  fixes P::"'a::{field}^'m^'m"
  assumes inv_P: "invertible P"
  and sub_W: "vec.subspace W"
  shows "vec.dim ((\<lambda>x. P *v x)` W) = vec.dim W"
proof -
  obtain B where B_in_W: "B\<subseteq>W" and ind_B: "vec.independent B" 
    and W_in_span_B: "W \<subseteq> vec.span B" and card_B_eq_dim_W: "card B = vec.dim W"
    using vec.basis_exists by blast
  define L where "L = (\<lambda>x. P *v x)"
  define C where "C = L`B"
  have finite_B: "finite B" using vec.indep_card_eq_dim_span[OF ind_B] by simp
  interpret L: Vector_Spaces.linear "(*s)" "(*s)" L  using matrix_vector_mul_linear_gen unfolding L_def .
  have finite_C: "finite C" using vec.indep_card_eq_dim_span[OF ind_B] unfolding C_def by simp
  have inv_TP: "invertible_lf ((*s)) ((*s)) (\<lambda>x. P *v x)" using invertible_matrix_imp_invertible_lf[OF inv_P] .
  have inj_on_LW: "inj_on L W" using invertible_imp_bijective[OF inv_TP] unfolding bij_def L_def unfolding inj_on_def 
    by blast
  hence inj_on_LB: "inj_on L B" unfolding inj_on_def using B_in_W by auto  
  have ind_D: "vec.independent C"
  proof (rule vec.independent_if_scalars_zero[OF finite_C])
    fix f x
    assume sum: "(\<Sum>x\<in>C. f x *s x) = 0" and x: "x \<in> C"
    obtain y where Ly_eq_x: "L y = x" and y: "y \<in> B" using x unfolding C_def L_def by auto    
    have "(\<Sum>x\<in>C. f x *s x) = sum ((\<lambda>x. f x *s x) \<circ> L) B" unfolding C_def by (rule sum.reindex[OF inj_on_LB])
    also have "... = sum (\<lambda>x. f (L x) *s L x) B" unfolding o_def .. 
    also have "... =  sum (\<lambda>x. ((f \<circ> L) x) *s L x) B" using o_def by auto
    also have "... = L (sum (\<lambda>x. ((f \<circ> L) x) *s x) B)"
      by (simp add: L.sum L.scale)
    finally have rw: " (\<Sum>x\<in>C. f x *s x) = L (\<Sum>x\<in>B. (f \<circ> L) x *s x)" .
    have "(\<Sum>x\<in>B. (f \<circ> L) x *s x) \<in> W"
      by (rule vec.subspace_sum[OF sub_W])
        (simp add: B_in_W rev_subsetD sub_W vec.subspace_scale)
    hence "(\<Sum>x\<in>B. (f \<circ> L) x *s x)=0"
      using sum rw
      using vec.linear_inj_on_iff_eq_0[OF L.linear_axioms sub_W] using inj_on_LW
      by (auto simp: L_def)
    hence "(f \<circ> L) y = 0"
      using vec.scalars_zero_if_independent[OF finite_B ind_B, of "(f \<circ> L)"] 
      using y by auto
    thus "f x = 0" unfolding o_def Ly_eq_x .
  qed
  have "L` W \<subseteq> vec.span C"
  proof (unfold vec.span_finite[OF finite_C], clarify)
    fix xa assume xa_in_W: "xa \<in> W"
    obtain g where sum_g: "sum (\<lambda>x. g x *s x) B = xa"
      using vec.span_finite[OF finite_B] W_in_span_B xa_in_W by force
    show "L xa \<in> range (\<lambda>u. (\<Sum>v\<in>C. u v *s v))"
    proof (rule image_eqI[where x="\<lambda>x. g (THE y. y \<in> B \<and> x=L y)"])
      have "L xa = L (sum (\<lambda>x. g x *s x) B)" using sum_g by simp
      also have "... = sum (\<lambda>x. g x *s L x) B" by (simp add: L.sum L.scale)
      also have "... = sum (\<lambda>x. g (THE y. y \<in> B \<and> x=L y) *s x) (L`B)"
      proof (unfold sum.reindex[OF inj_on_LB], unfold o_def, rule sum.cong)
        fix x assume x_in_B: "x\<in>B"
        have x_eq_the:"x = (THE y. y \<in> B \<and> L x = L y)"
        proof (rule the_equality[symmetric])
          show "x \<in> B \<and> L x = L x" using x_in_B by auto
          show "\<And>y. y \<in> B \<and> L x = L y \<Longrightarrow> y = x" using inj_on_LB x_in_B unfolding inj_on_def by fast
        qed
        show "g x *s L x = g (THE y. y \<in> B \<and> L x = L y) *s L x" using x_eq_the by simp
      qed rule
      finally show "L xa = (\<Sum>v\<in>C. g (THE y. y \<in> B \<and> v = L y) *s v)" unfolding C_def by simp
    qed rule
  qed
  have "card C = card B" using card_image[OF inj_on_LB] unfolding C_def .
  thus ?thesis
    by (metis B_in_W C_def L.span_image W_in_span_B \<open>L \<equiv> (*v) P\<close> card_B_eq_dim_W ind_D sub_W
        vec.indep_card_eq_dim_span vec.span_subspace)
qed


lemma invertible_matrix_mult_left_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" 
  and P::"'a::{field}^'m::{mod_type}^'m::{mod_type}"
  assumes invertible_P: "invertible P"
  shows "rank (P**A) = rank A"
proof -
  define TP where "TP = (\<lambda>x. P *v x)"
  define TA where "TA = (\<lambda>x. A *v x)"
  define TPA where "TPA = (\<lambda>x. (P**A) *v x)"
  have sub: "vec.subspace (range ((*v) A))"
    by (metis vec.subspace_UNIV vec.subspace_image)
  have "vec.dim (range TPA) = vec.dim (range (TP \<circ> TA))"
    unfolding TP_def TA_def TPA_def o_def matrix_vector_mul_assoc ..
  also have "... = vec.dim (range TA)" using dim_image_invertible_mat[OF invertible_P sub] 
    unfolding TP_def TA_def o_def fun.set_map[symmetric] .
  finally show ?thesis unfolding rank_eq_dim_image TPA_def TA_def . 
qed

corollary invertible_matrices_mult_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" 
  and P::"'a^'m::{mod_type}^'m::{mod_type}" and Q::"'a^'n::{mod_type}^'n::{mod_type}"
  assumes invertible_P: "invertible P" 
  and invertible_Q: "invertible Q"
  shows "rank (P**A**Q) = rank A"
  using invertible_matrix_mult_right_rank[OF invertible_Q] using invertible_matrix_mult_left_rank[OF invertible_P] by metis


lemma invertible_matrix_mult_left_rank':
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" and P::"'a^'m::{mod_type}^'m::{mod_type}"
  assumes invertible_P: "invertible P" and B_eq_PA: "B=P**A"
  shows "rank B = rank A"
proof -
  have "rank B = rank (P**A)" using B_eq_PA by auto
  also have "... = rank A" using invertible_matrix_mult_left_rank[OF invertible_P] by auto
  finally show ?thesis .
qed

lemma invertible_matrix_mult_right_rank':
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" 
  and Q::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  assumes invertible_Q: "invertible Q" and B_eq_PA: "B=A**Q"
  shows "rank B = rank A" by (metis B_eq_PA invertible_Q invertible_matrix_mult_right_rank)

lemma invertible_matrices_rank':
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" 
  and P::"'a^'m::{mod_type}^'m::{mod_type}" and Q::"'a^'n::{mod_type}^'n::{mod_type}"
  assumes invertible_P: "invertible P" and invertible_Q: "invertible Q" and B_eq_PA: "B = P**A**Q"
  shows "rank B = rank A" by (metis B_eq_PA invertible_P invertible_Q invertible_matrices_mult_rank)

subsection\<open>Definition and properties of the set of a vector\<close>

text\<open>Some definitions:\<close>

text\<open>In the file \<open>Generalizations.thy\<close> there exists the following definition: 
  @{thm "cart_basis_def"}.\<close>
  
text\<open>\<open>cart_basis\<close> returns a set which is a basis and it works properly in my development.
  But in this file, I need to know the order of the elements of the basis, because is very important
  for the coordenates of a vector and the matrices of change of bases. So, I have defined a new
  \<open>cart_basis'\<close>, which will be a matrix. The columns of this matrix are the elements of
  the basis.\<close>

definition set_of_vector :: "'a^'n \<Rightarrow> 'a set"
  where "set_of_vector A = {A $ i |i. i \<in> UNIV}"

definition cart_basis' :: " 'a::{field}^'n^'n"
  where "cart_basis' = (\<chi> i. axis i 1)"

lemma cart_basis_eq_set_of_vector_cart_basis': 
  "cart_basis = set_of_vector (cart_basis')"
  unfolding cart_basis_def cart_basis'_def set_of_vector_def by auto

lemma basis_image_linear:
  fixes f::"'b::{field}^'n => 'b^'n"
  assumes invertible_lf: "invertible_lf ((*s)) ((*s)) f"
  and basis_X: "is_basis (set_of_vector X)"
  shows "is_basis (f` (set_of_vector X))"
proof (rule iffD1[OF independent_is_basis], rule conjI)
    have "card (f ` set_of_vector X) = card (set_of_vector X)"
    by (rule card_image[of f "set_of_vector X"], metis invertible_imp_bijective[OF invertible_lf] bij_def inj_eq inj_on_def)
  also have "... = card (UNIV::'n set)" using basis_X unfolding independent_is_basis[symmetric] by auto
  finally show "card (f ` set_of_vector X) = card (UNIV::'n set)" .
  interpret Vector_Spaces.linear "(*s)" "(*s)" f using invertible_lf unfolding invertible_lf_def by simp
  show "vec.independent (f ` set_of_vector X)"
  proof (rule independent_injective_image)
    show "vec.independent (set_of_vector X)" using basis_X unfolding is_basis_def by simp
    show "inj_on f (vec.span (set_of_vector X))"
      by (metis bij_def injD inj_onI invertible_imp_bijective invertible_lf)
  qed
qed


text\<open>Properties about @{thm "cart_basis'_def"}\<close>

lemma set_of_vector_cart_basis': 
  shows "(set_of_vector cart_basis') = {axis i 1 :: 'a::{field}^'n | i. i \<in> (UNIV :: 'n set)}"
  unfolding set_of_vector_def cart_basis'_def by auto

lemma cart_basis'_i: "cart_basis' $ i = axis i 1" unfolding cart_basis'_def by simp

lemma finite_set_of_vector[intro,simp]: "finite (set_of_vector X)"
  unfolding set_of_vector_def using finite_Atleast_Atmost_nat[of "\<lambda>i. X $ i"] .

lemma is_basis_cart_basis': "is_basis (set_of_vector cart_basis')"
  unfolding cart_basis_eq_set_of_vector_cart_basis'[symmetric]
  by (metis Miscellaneous.is_basis_def independent_cart_basis span_cart_basis)

lemma basis_expansion_cart_basis':"sum (\<lambda>i. x$i *s cart_basis' $ i) UNIV = x"
  unfolding cart_basis'_def using basis_expansion by auto

lemma basis_expansion_unique:
  "sum (\<lambda>i. f i *s axis (i::'n::finite) 1) UNIV = (x::('a::comm_ring_1) ^'n) \<longleftrightarrow> (\<forall>i. f i = x$i)"
proof (auto simp add: basis_expansion)
  fix i::"'n" 
  have univ_rw: "UNIV = (UNIV - {i}) \<union> {i}" by fastforce
  have "(\<Sum>x\<in>UNIV. f x * axis x 1 $ i) = sum (\<lambda>x.  f x * axis x 1 $ i) (UNIV - {i} \<union> {i})" using univ_rw by simp
  also have "... = sum (\<lambda>x.  f x * axis x 1 $ i) (UNIV - {i}) +  sum (\<lambda>x.  f x * axis x 1 $ i) {i}" by (rule sum.union_disjoint, auto)
  also have "... = f i" unfolding axis_def by auto
  finally show "f i = (\<Sum>x\<in>UNIV. f x * axis x 1 $ i)" ..
qed


lemma basis_expansion_cart_basis'_unique: "sum (\<lambda>i. f (cart_basis' $ i) *s cart_basis' $ i) UNIV = x \<longleftrightarrow> (\<forall>i. f (cart_basis' $ i) = x$i)"
  using basis_expansion_unique unfolding cart_basis'_def
  by (simp add: vec_eq_iff if_distrib cong del: if_weak_cong)

lemma basis_expansion_cart_basis'_unique': "sum (\<lambda>i. f i *s cart_basis' $ i) UNIV = x \<longleftrightarrow> (\<forall>i. f i = x$i)"
  using basis_expansion_unique unfolding cart_basis'_def
  by (simp add: vec_eq_iff if_distrib cong del: if_weak_cong)

text\<open>Properties of @{thm "is_basis_def"}.\<close>

lemma sum_basis_eq:
  fixes X::"'a::{field}^'n^'n"
  assumes is_basis:"is_basis  (set_of_vector X)"
  shows "sum (\<lambda>x. f x *s x) (set_of_vector X) = sum (\<lambda>i. f (X$i) *s (X$i)) UNIV"
proof -
have card_set_of_vector:"card(set_of_vector X) = CARD('n)" 
  using independent_is_basis[of "set_of_vector X"] using is_basis by auto
have fact_1: "set_of_vector X = range (($) X)" unfolding set_of_vector_def by auto
have inj: "inj (($) X)"
  proof (rule eq_card_imp_inj_on) 
    show "finite (UNIV::'n set)" using finite_class.finite_UNIV .
    show "card (range (($) X)) = card (UNIV::'n set)" 
      using card_set_of_vector using fact_1 unfolding set_of_vector_def by simp
  qed
show ?thesis using sum.reindex[OF inj, of "(\<lambda>x. f x *s x)", unfolded o_def] unfolding fact_1 .
qed

corollary sum_basis_eq2:
  fixes X::"'a::{field}^'n^'n"
  assumes is_basis:"is_basis  (set_of_vector X)"
  shows "sum (\<lambda>x. f x *s x) (set_of_vector X) = sum (\<lambda>i. (f \<circ> ($) X) i *s (X$i)) UNIV" 
  using sum_basis_eq[OF is_basis] by simp

lemma inj_op_nth:
  fixes X::"'a::{field}^'n^'n"
  assumes is_basis: "is_basis (set_of_vector X)"
  shows "inj (($) X)"
proof -
  have fact_1: "set_of_vector X = range (($) X)" unfolding set_of_vector_def by auto
  have card_set_of_vector:"card(set_of_vector X) = CARD('n)" using independent_is_basis[of "set_of_vector X"] using is_basis by auto
  show "inj (($) X)"
  proof (rule eq_card_imp_inj_on) 
    show "finite (UNIV::'n set)" using finite_class.finite_UNIV .
    show "card (range (($) X)) = card (UNIV::'n set)" using card_set_of_vector using fact_1 unfolding set_of_vector_def by simp
  qed
qed

lemma basis_UNIV:
  fixes X::"'a::{field}^'n^'n"
  assumes is_basis: "is_basis (set_of_vector X)"
  shows "UNIV = {x. \<exists>g. (\<Sum>i\<in>UNIV. g i *s X$i) = x}"
proof -
  have "UNIV = {x. \<exists>g. (\<Sum>i\<in>(set_of_vector X). g i *s i) = x}"
    using vec.span_finite[OF basis_finite[OF is_basis]]
    using is_basis unfolding is_basis_def
    by (auto simp: set_eq_iff
        intro!: vec.sum_representation_eq exI[where x="vec.representation (set_of_vector X) x" for x])
  also have "... \<subseteq> {x. \<exists>g. (\<Sum>i\<in>UNIV. g i *s X$i) = x}"
  proof (clarify)
    fix f
    show "\<exists>g. (\<Sum>i\<in>UNIV. g i *s X $ i) = (\<Sum>i\<in>set_of_vector X. f i *s i)"
    proof (rule exI[of _ "(\<lambda>i. (f \<circ> ($) X) i)"], unfold o_def)
      have fact_1: "set_of_vector X = range (($) X)" unfolding set_of_vector_def by auto
      have card_set_of_vector:"card(set_of_vector X) = CARD('n)" using independent_is_basis[of "set_of_vector X"] using is_basis by auto
      have inj: "inj (($) X)" using inj_op_nth[OF is_basis] .
      show " (\<Sum>i\<in>UNIV. f (X $ i) *s X $ i) = (\<Sum>i\<in>set_of_vector X. f i *s i)" 
        using sum.reindex[symmetric, OF inj, of "\<lambda>i. f i *s i"] unfolding fact_1 by simp
    qed
  qed
  finally show ?thesis by auto
qed

lemma scalars_zero_if_basis:
  fixes X::"'a::{field}^'n^'n"
  assumes is_basis: "is_basis (set_of_vector X)" and sum: "(\<Sum>i\<in>(UNIV::'n set). f i *s X$i) = 0"
  shows "\<forall>i\<in>(UNIV::'n set). f i = 0" 
proof -
  have ind_X: "vec.independent (set_of_vector X)" using is_basis unfolding is_basis_def by simp
  have finite_X:"finite (set_of_vector X)" using basis_finite[OF is_basis] .
  have 1: "(\<forall>g. (\<Sum>v\<in>(set_of_vector X). g v *s v) = 0 \<longrightarrow> (\<forall>v\<in>(set_of_vector X). g v = 0))"
    using ind_X unfolding vec.independent_explicit using finite_X by auto
  define g where "g v = f (THE i. X $ i = v)" for v
  have "(\<Sum>v\<in>(set_of_vector X). g v *s v) = 0"
  proof -
    have "(\<Sum>v\<in>(set_of_vector X). g v *s v)  = (\<Sum>i\<in>(UNIV::'n set). f i *s X$i)"
    proof -
      have inj: "inj (($) X)" using inj_op_nth[OF is_basis] .
      have rw: "set_of_vector X = range (($) X)" unfolding set_of_vector_def by auto
      {
        fix a
        have "f a = g (X $ a)"
          unfolding g_def using inj_op_nth[OF is_basis]
          by (metis (lifting, mono_tags) injD the_equality) 
       }
      thus ?thesis using sum.reindex[OF inj, of "\<lambda>v. g v *s v"] unfolding rw o_def by auto
    qed
    thus ?thesis unfolding sum .
  qed
  hence 2: "\<forall>v\<in>(set_of_vector X). g v = 0" using 1 by auto
  show ?thesis
  proof (clarify)
    fix a
    have "g (X$a) = 0" using 2 unfolding set_of_vector_def by auto
    thus "f a = 0" unfolding g_def using inj_op_nth[OF is_basis]
      by (metis (lifting, mono_tags) injD the_equality)
  qed
qed

lemma basis_combination_unique:
  fixes X::"'a::{field}^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" and sum_eq: "(\<Sum>i\<in>UNIV. g i *s X$i) = (\<Sum>i\<in>UNIV. f i *s X$i)"
  shows "f=g"
proof (rule ccontr)
  assume "f\<noteq>g"
  from this obtain x where fx_gx: "f x \<noteq> g x" by fast
  have "0=(\<Sum>i\<in>UNIV. g i *s X$i) - (\<Sum>i\<in>UNIV. f i *s X$i)" using sum_eq by simp
  also have "... = (\<Sum>i\<in>UNIV. g i *s X$i - f i *s X$i)" unfolding sum_subtractf[symmetric] ..
  also have "... = (\<Sum>i\<in>UNIV. (g i - f i) *s X$i)"  by (rule sum.cong, auto simp add: scaleR_diff_left) 
  also have "... = (\<Sum>i\<in>UNIV. (g - f) i *s X$i)" by simp
  finally have sum_eq_1: "0 = (\<Sum>i\<in>UNIV. (g - f) i *s X$i)" by simp
  have "\<forall>i\<in>UNIV. (g - f) i = 0" by (rule scalars_zero_if_basis[OF basis_X sum_eq_1[symmetric]])
  hence "(g - f) x = 0" by simp
  hence "f x = g x" by simp
  thus False using fx_gx by contradiction
qed


subsection\<open>Coordinates of a vector\<close>

text\<open>Definition and properties of the coordinates of a vector (in terms of a particular ordered basis).\<close>

definition coord :: "'a::{field}^'n^'n\<Rightarrow>'a::{field}^'n\<Rightarrow>'a::{field}^'n"
where "coord X v = (\<chi> i. (THE f. v = sum (\<lambda>x. f x *s X$x) UNIV) i)"

text\<open>@{term "coord X v"} are the coordinates of vector @{term "v"} with respect to the basis @{term "X"}\<close>

lemma bij_coord:
  fixes X::"'a::{field}^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)"
  shows "bij (coord X)"
proof (unfold bij_def, auto)
  show inj: "inj (coord X)"
  proof (unfold inj_on_def, auto)
    fix x y assume coord_eq: "coord X x = coord X y"
    obtain f where f: "(\<Sum>x\<in>UNIV. f x *s X $ x) = x"  using basis_UNIV[OF basis_X] by blast
    obtain g where g:  "(\<Sum>x\<in>UNIV. g x *s X $ x) = y" using basis_UNIV[OF basis_X] by blast    
    have the_f: "(THE f. x = (\<Sum>x\<in>UNIV. f x *s X $ x)) = f"
    proof (rule the_equality)
      show "x = (\<Sum>x\<in>UNIV. f x *s X $ x)" using f by simp
      show "\<And>fa. x = (\<Sum>x\<in>UNIV. fa x *s X $ x) \<Longrightarrow> fa = f" using basis_combination_unique[OF basis_X] f by simp
    qed
    have the_g: "(THE g. y = (\<Sum>x\<in>UNIV. g x *s X $ x)) = g"
    proof (rule the_equality)
      show "y = (\<Sum>x\<in>UNIV. g x *s X $ x)" using g by simp
      show "\<And>ga. y = (\<Sum>x\<in>UNIV. ga x *s X $ x) \<Longrightarrow> ga = g" using basis_combination_unique[OF basis_X] g by simp
    qed    
    have "(THE f. x = (\<Sum>x\<in>UNIV. f x *s X $ x)) = (THE g. y = (\<Sum>x\<in>UNIV. g x *s X $ x))" 
      using coord_eq unfolding coord_def 
      using vec_lambda_inject[of "(THE f. x = (\<Sum>x\<in>UNIV. f x *s X $ x)) "  "(THE f. y = (\<Sum>x\<in>UNIV. f x *s X $ x))"]
      by auto
    hence "f = g" unfolding the_f the_g .
    thus "x=y" using f g by simp
  qed
next
  fix x::"('a, 'n) vec"
  show "x \<in> range (coord X)"
  proof (unfold image_def, auto, rule exI[of _ "sum (\<lambda>i. x$i *s X$i) UNIV"], unfold coord_def)
    define f where "f i = x$i" for i
    have the_f: " (THE f. (\<Sum>i\<in>UNIV. x $ i *s X $ i) = (\<Sum>x\<in>UNIV. f x *s X $ x)) = f"
    proof (rule the_equality)
      show "(\<Sum>i\<in>UNIV. x $ i *s X $ i) = (\<Sum>x\<in>UNIV. f x *s X $ x)" unfolding f_def ..
      fix g assume sum_eq:"(\<Sum>i\<in>UNIV. x $ i *s X $ i) = (\<Sum>x\<in>UNIV. g x *s X $ x)"
      show "g = f" using  basis_combination_unique[OF basis_X] using sum_eq unfolding f_def by simp
    qed
    show " x = vec_lambda (THE f. (\<Sum>i\<in>UNIV. x $ i *s X $ i) = (\<Sum>x\<in>UNIV. f x *s X $ x))" unfolding the_f unfolding f_def using vec_lambda_eta[of x] by simp
  qed
qed

lemma linear_coord:
  fixes X::"'a::{field}^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)"
  shows "linear ((*s)) ((*s)) (coord X)"
proof unfold_locales
  fix x y::"('a, 'n) vec"
  show  "coord X (x + y) = coord X x + coord X y"
  proof -
    obtain f where f: "(\<Sum>a\<in>(UNIV::'n set). f a *s X $ a) = x + y" using basis_UNIV[OF basis_X] by blast
    obtain g where g: " (\<Sum>x\<in>UNIV. g x *s X $ x) = x" using basis_UNIV[OF basis_X] by blast
    obtain h where h: "(\<Sum>x\<in>UNIV. h x *s X $ x) = y" using basis_UNIV[OF basis_X] by blast
    define t where "t i = g i + h i" for i
    have the_f: "(THE f. x + y = (\<Sum>x\<in>UNIV. f x *s X $ x)) = f"
    proof (rule the_equality)
      show " x + y = (\<Sum>x\<in>UNIV. f x *s X $ x)" using f by simp
      show "\<And>fa. x + y = (\<Sum>x\<in>UNIV. fa x *s X $ x) \<Longrightarrow> fa = f" using basis_combination_unique[OF basis_X] f by simp
    qed
    have the_g: "(THE g. x = (\<Sum>x\<in>UNIV. g x *s X $ x)) = g"
    proof (rule the_equality)
      show "x = (\<Sum>x\<in>UNIV. g x *s X $ x)" using g by simp
      show "\<And>ga. x = (\<Sum>x\<in>UNIV. ga x *s X $ x) \<Longrightarrow> ga = g"  using basis_combination_unique[OF basis_X] g by simp
    qed
    have the_h: "(THE h. y = (\<Sum>x\<in>UNIV. h x *s X $ x)) = h" 
    proof (rule the_equality)
      show "y = (\<Sum>x\<in>UNIV. h x *s X $ x)" using h ..
      show "\<And>ha. y = (\<Sum>x\<in>UNIV. ha x *s X $ x) \<Longrightarrow> ha = h"  using basis_combination_unique[OF basis_X] h by simp
    qed    
    have "(\<Sum>a\<in>(UNIV::'n set). f a *s X $ a) =  (\<Sum>x\<in>UNIV. g x *s X $ x) + (\<Sum>x\<in>UNIV. h x *s X $ x)" using f g h by simp
    also have "... = (\<Sum>x\<in>UNIV. g x *s X $ x + h x *s X $ x)" unfolding sum.distrib[symmetric] ..
    also have "... = (\<Sum>x\<in>UNIV. (g x + h x) *s X $ x)" by (rule sum.cong, auto simp add: scaleR_left_distrib)
    also have "... = (\<Sum>x\<in>UNIV. t x *s X $ x)" unfolding t_def ..
    finally have "(\<Sum>a\<in>UNIV. f a *s X $ a) = (\<Sum>x\<in>UNIV. t x *s X $ x)" .
    hence "f=t" using basis_combination_unique[OF basis_X] by auto
    thus ?thesis
      by (unfold coord_def the_f the_g the_h, vector, auto, unfold f g h t_def, simp)
  qed
next
  fix c::'a and x::"'a^'n"
  show "coord X (c *s x) = c *s coord X x"
  proof -
    obtain f where f: "(\<Sum>x\<in>UNIV. f x *s X $ x) = c *s x" using basis_UNIV[OF basis_X] by blast
    obtain g where g: "(\<Sum>x\<in>UNIV. g x *s X $ x) = x" using basis_UNIV[OF basis_X] by blast
    define t where "t i = c * g i" for i
    have the_f: "(THE f. c *s x = (\<Sum>x\<in>UNIV. f x *s X $ x)) = f"
    proof (rule the_equality)
      show " c *s x = (\<Sum>x\<in>UNIV. f x *s X $ x)" using f ..
      show "\<And>fa. c *s x = (\<Sum>x\<in>UNIV. fa x *s X $ x) \<Longrightarrow> fa = f" using basis_combination_unique[OF basis_X] f by simp
    qed
    have the_g: "(THE g. x = (\<Sum>x\<in>UNIV. g x *s X $ x)) = g"proof (rule the_equality)
      show " x = (\<Sum>x\<in>UNIV. g x *s X $ x)" using g ..
      show "\<And>ga. x = (\<Sum>x\<in>UNIV. ga x *s X $ x) \<Longrightarrow> ga = g" using basis_combination_unique[OF basis_X] g by simp
    qed    
    have "(\<Sum>x\<in>UNIV. f x *s X $ x) = c *s (\<Sum>x\<in>UNIV. g x *s X $ x)" using f g by simp
    also have "... = (\<Sum>x\<in>UNIV. c *s (g x *s X $ x))" by (rule vec.scale_sum_right)
    also have "... =  (\<Sum>x\<in>UNIV. t x *s X $ x)" unfolding t_def by simp
    finally have " (\<Sum>x\<in>UNIV. f x *s X $ x) = (\<Sum>x\<in>UNIV. t x *s X $ x)" .
    hence "f=t" using basis_combination_unique[OF basis_X] by auto
    thus ?thesis
      by (unfold coord_def the_f the_g, vector, auto, unfold t_def, auto)
  qed
qed


lemma coord_eq:
  assumes basis_X:"is_basis (set_of_vector X)"
  and coord_eq: "coord X v = coord X w"
  shows "v = w"
proof -
  have "\<forall>i. (THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) i = (THE f. \<forall>i. w $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) i"  using coord_eq
    unfolding coord_eq coord_def vec_eq_iff by simp
  hence the_eq: "(THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) = (THE f. \<forall>i. w $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i))" by auto
  obtain f where  f: "(\<Sum>x\<in>UNIV. f x *s X $ x)= v" using basis_UNIV[OF basis_X] by blast
  obtain g where  g: "(\<Sum>x\<in>UNIV. g x *s X $ x)= w" using basis_UNIV[OF basis_X] by blast
  have the_f: "(THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) = f"
  proof (rule the_equality)
    show " \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)" using f by auto
    fix fa assume "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x * X $ x $ i)"
    hence "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x *s X $ x) $ i" unfolding sum_component by simp
    hence fa:" v = (\<Sum>x\<in>UNIV. fa x *s X $ x)"  unfolding vec_eq_iff .
    show "fa = f" using basis_combination_unique[OF basis_X] f fa by simp
  qed
  have the_g: "(THE g. \<forall>i. w $ i = (\<Sum>x\<in>UNIV. g x * X $ x $ i)) = g" 
  proof (rule the_equality)
    show " \<forall>i. w $ i = (\<Sum>x\<in>UNIV. g x * X $ x $ i)" using g by auto
    fix fa assume "\<forall>i. w $ i = (\<Sum>x\<in>UNIV. fa x * X $ x $ i)"
    hence "\<forall>i. w $ i = (\<Sum>x\<in>UNIV. fa x *s X $ x) $ i" unfolding sum_component by simp
    hence fa:" w = (\<Sum>x\<in>UNIV. fa x *s X $ x)"  unfolding vec_eq_iff .
    show "fa = g" using basis_combination_unique[OF basis_X] g fa by simp
  qed
  have "f=g" using the_eq unfolding the_f the_g .
  thus "v=w" using f g by blast
qed


subsection\<open>Matrix of change of basis and coordinate matrix of a linear map\<close>

text\<open>Definitions of matrix of change of basis and matrix of a linear transformation with respect to two bases:\<close>

definition matrix_change_of_basis :: "'a::{field}^'n^'n \<Rightarrow>'a^'n^'n\<Rightarrow>'a^'n^'n"
  where "matrix_change_of_basis X Y = (\<chi> i j. (coord Y (X$j)) $ i)"

text\<open>There exists in the library the definition @{thm "matrix_def"}, which is the coordinate matrix of a linear map with respect to the standard bases.
      Now we generalise that concept to the coordinate matrix of a linear map with respect to any two bases.\<close>

definition matrix' :: "'a::{field}^'n^'n \<Rightarrow> 'a^'m^'m \<Rightarrow> ('a^'n => 'a^'m) \<Rightarrow> 'a^'n^'m"
  where "matrix' X Y f= (\<chi> i j. (coord Y (f(X$j))) $ i)"

text\<open>Properties of @{thm "matrix'_def"}\<close>

lemma matrix'_eq_matrix:
  defines cart_basis_Rn: "cart_basis_Rn == (cart_basis')::'a::{field}^'n^'n" 
  and cart_basis_Rm:"cart_basis_Rm == (cart_basis')::'a^'m^'m"  
  shows "matrix' (cart_basis_Rn) (cart_basis_Rm) f = matrix f"
proof (unfold matrix_def matrix'_def coord_def, vector, auto)
  fix i j
  have basis_Rn:"is_basis (set_of_vector cart_basis_Rn)" using is_basis_cart_basis' unfolding cart_basis_Rn .  
  have basis_Rm:"is_basis (set_of_vector cart_basis_Rm)" using is_basis_cart_basis' unfolding cart_basis_Rm .
  obtain g where sum_g: "(\<Sum>x\<in>UNIV. g x *s (cart_basis_Rm $ x)) = f (cart_basis_Rn $ j)" using basis_UNIV[OF basis_Rm] by blast  
  have the_g: "(THE g. \<forall>a. f (cart_basis_Rn $ j) $ a = (\<Sum>x\<in>UNIV. g x * cart_basis_Rm $ x $ a)) = g"
  proof (rule the_equality, clarify)
    fix a 
    have "f (cart_basis_Rn $ j) $ a = (\<Sum>i\<in>UNIV. g i *s (cart_basis_Rm $ i)) $ a" using sum_g by simp
    also have "... = (\<Sum>x\<in>UNIV. g x * cart_basis_Rm $ x $ a)" unfolding sum_component by simp
    finally show "f (cart_basis_Rn $ j) $ a = (\<Sum>x\<in>UNIV. g x * cart_basis_Rm $ x $ a)" .  
    fix ga assume "\<forall>a. f (cart_basis_Rn $ j) $ a = (\<Sum>x\<in>UNIV. ga x * cart_basis_Rm $ x $ a)"
    hence sum_ga: "f (cart_basis_Rn $ j) = (\<Sum>i\<in>UNIV. ga i *s cart_basis_Rm $ i)" by (vector, auto)
    show "ga = g" 
    proof (rule basis_combination_unique)
      show "is_basis (set_of_vector (cart_basis_Rm))" using basis_Rm .
      show " (\<Sum>i\<in>UNIV. g i *s cart_basis_Rm $ i) = (\<Sum>i\<in>UNIV. ga i *s cart_basis_Rm $ i)" using sum_g sum_ga by simp
    qed
  qed
  show " (THE fa. \<forall>i. f (cart_basis_Rn $ j) $ i = (\<Sum>x\<in>UNIV. fa x * cart_basis_Rm $ x $ i)) i = f (axis j 1) $ i"
    unfolding the_g using sum_g unfolding cart_basis_Rm cart_basis_Rn cart_basis'_def   using basis_expansion_unique[of g "f (axis j 1)"]
    unfolding scalar_mult_eq_scaleR by auto
qed

lemma matrix':
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  shows "f (X$i) = sum (\<lambda>j. (matrix' X Y f) $ j $ i *s (Y$j)) UNIV" 
proof (unfold matrix'_def coord_def matrix_mult_sum column_def, vector, auto)
  fix j
  obtain g where  g: "(\<Sum>x\<in>UNIV. g x *s Y $ x) = f (X $ i)" using basis_UNIV[OF basis_Y] by blast
  have the_g: "(THE fa. \<forall>ia. f (X $ i) $ ia = (\<Sum>x\<in>UNIV. fa x * Y $ x $ ia)) = g"
  proof (rule the_equality, clarify)
    fix a
    have "f (X $ i) $ a = (\<Sum>x\<in>UNIV. g x *s Y $ x) $ a" using g by simp
    also have "... = (\<Sum>x\<in>UNIV. g x * Y $ x $ a)" unfolding sum_component by auto
    finally show "f (X $ i) $ a = (\<Sum>x\<in>UNIV. g x * Y $ x $ a)" .
    fix fa
    assume  "\<forall>ia. f (X $ i) $ ia = (\<Sum>x\<in>UNIV. fa x * Y $ x $ ia)" 
    hence " \<forall>ia. f (X $ i) $ ia =  (\<Sum>x\<in>UNIV. fa x *s Y $ x) $ ia" unfolding sum_component by simp
    hence fa:"f (X $ i) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)" unfolding vec_eq_iff .
    show "fa = g" by (rule basis_combination_unique[OF basis_Y], simp add: fa g)
  qed
  show " f (X $ i) $ j = (\<Sum>x\<in>UNIV. (THE fa. \<forall>j. f (X $ i) $ j = (\<Sum>x\<in>UNIV. fa x * Y $ x $ j)) x * Y $ x $ j)"
    unfolding the_g unfolding g[symmetric] sum_component by simp
qed


corollary matrix'2:
  assumes  basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  and eq_f: "\<forall>i. f (X$i) = sum (\<lambda>j. A $ j $ i *s (Y$j)) UNIV"
  shows "matrix' X Y f = A"
proof -
  have eq_f': "\<forall>i. f (X$i) = sum (\<lambda>j. (matrix' X Y f) $ j $ i *s (Y$j)) UNIV" using matrix'[OF basis_X basis_Y] by auto
  show ?thesis
  proof (vector, auto)
    fix i j
    define a where "a x = (matrix' X Y f) $ x $ i" for x
    define b where "b x = A $ x $ i" for x
    have  fxi_1:"f (X$i) = sum (\<lambda>j. a j *s (Y$j)) UNIV" using eq_f' unfolding a_def by simp
    have  fxi_2: "f (X$i) = sum (\<lambda>j. b j *s(Y$j)) UNIV" using eq_f unfolding b_def by simp    
    have "a=b" using basis_combination_unique[OF basis_Y] fxi_1 fxi_2  by auto    
    thus "(matrix' X Y f) $ j $ i = A $ j $ i" unfolding a_def b_def by metis
  qed
qed

text\<open>This is the theorem 2.14 in the book "Advanced Linear Algebra" by Steven Roman.\<close>
lemma coord_matrix':
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'m^'m"
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  and linear_f: "linear ((*s)) ((*s)) f"
  shows "coord Y (f v) = (matrix' X Y f) *v (coord X v)"  
proof (unfold matrix_mult_sum matrix'_def column_def coord_def, vector, auto)
  fix i
  interpret Vector_Spaces.linear "(*s)" "(*s)" f by fact
  obtain g where g: "(\<Sum>x\<in>UNIV. g x *s Y $ x) = f v" using basis_UNIV[OF basis_Y] by auto
  obtain s where s: "(\<Sum>x\<in>UNIV. s x *s X $ x) = v" using basis_UNIV[OF basis_X] by auto
  have the_g: "(THE fa. \<forall>a. f v $ a = (\<Sum>x\<in>UNIV. fa x * Y $ x $ a)) = g"
  proof (rule the_equality)
    have "\<forall>a. f v $ a = (\<Sum>x\<in>UNIV. g x  *s Y $ x) $ a" using g by simp
    thus " \<forall>a. f v $ a = (\<Sum>x\<in>UNIV. g x * Y $ x $ a)" unfolding sum_component by simp
    fix fa assume " \<forall>a. f v $ a = (\<Sum>x\<in>UNIV. fa x * Y $ x $ a)" 
    hence  fa: "f v = (\<Sum>x\<in>UNIV. fa x *s Y $ x)" by (vector, auto)
    show "fa=g" by (rule basis_combination_unique[OF basis_Y], simp add: fa g)
  qed
  have the_s: "(THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i))=s"
  proof (rule the_equality)
    have " \<forall>i. v $ i = (\<Sum>x\<in>UNIV. s x *s X $ x) $ i" using s by simp
    thus " \<forall>i. v $ i = (\<Sum>x\<in>UNIV. s x * X $ x $ i)"unfolding sum_component by simp
    fix fa assume "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x * X $ x $ i)"
    hence fa: "v=(\<Sum>x\<in>UNIV. fa x *s X $ x)" by (vector, auto)
    show "fa=s"by (rule basis_combination_unique[OF basis_X], simp add: fa s)
  qed
  define t where "t x = (\<Sum>i\<in>UNIV. (s i * (THE fa. f (X $ i) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)) x))" for x
  have "(\<Sum>x\<in>UNIV. g x *s Y $ x) = f v" using g by simp
  also have "... = f (\<Sum>x\<in>UNIV. s x *s X $ x)" using s by simp
  also have "... = (\<Sum>x\<in>UNIV. s x *s f (X $ x))" by (simp add: sum scale)
  also have "... = (\<Sum>i\<in>UNIV. s i *s sum (\<lambda>j. (matrix' X Y f)$j$i *s (Y$j)) UNIV)" using matrix'[OF basis_X basis_Y] by auto
  also have "... =  (\<Sum>i\<in>UNIV. \<Sum>x\<in>UNIV. s i *s (matrix' X Y f $ x $ i *s Y $ x))" unfolding vec.scale_sum_right ..
  also have "... = (\<Sum>i\<in>UNIV. \<Sum>x\<in>UNIV. (s i * (THE fa. f (X $ i) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)) x) *s Y $ x)" unfolding matrix'_def unfolding coord_def by auto
  also have "... = (\<Sum>x\<in>UNIV. (\<Sum>i\<in>UNIV. (s i * (THE fa. f (X $ i) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)) x) *s Y $ x))"
    by (rule sum.swap)
  also have "... =  (\<Sum>x\<in>UNIV. (\<Sum>i\<in>UNIV. (s i * (THE fa. f (X $ i) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)) x)) *s Y $ x)" unfolding vec.scale_sum_left ..
  also have "... =  (\<Sum>x\<in>UNIV. t x *s Y $ x)" unfolding t_def ..
  finally have "(\<Sum>x\<in>UNIV. g x *s Y $ x) = (\<Sum>x\<in>UNIV. t x *s Y $ x)" .  
  hence "g=t" using basis_combination_unique[OF basis_Y] by simp
  thus "(THE fa. \<forall>i. f v $ i = (\<Sum>x\<in>UNIV. fa x * Y $ x $ i)) i =
    (\<Sum>x\<in>UNIV. (THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) x * (THE fa. \<forall>i. f (X $ x) $ i = (\<Sum>x\<in>UNIV. fa x * Y $ x $ i)) i)"
  proof (unfold  the_g the_s t_def, auto)
    have " (\<Sum>x\<in>UNIV. s x * (THE fa. \<forall>i. f (X $ x) $ i = (\<Sum>x\<in>UNIV. fa x * Y $ x $ i)) i) = 
      (\<Sum>x\<in>UNIV. s x * (THE fa. \<forall>i. f (X $ x) $ i = (\<Sum>x\<in>UNIV. fa x  *s Y $ x) $ i) i)" unfolding sum_component by simp
    also have "... = (\<Sum>x\<in>UNIV. s x * (THE fa. f (X $ x) = (\<Sum>x\<in>UNIV. fa x  *s Y $ x)) i)" by (rule sum.cong, auto simp add: vec_eq_iff) 
    finally show " (\<Sum>ia\<in>UNIV. s ia * (THE fa. f (X $ ia) = (\<Sum>x\<in>UNIV. fa x *s Y $ x)) i) = (\<Sum>x\<in>UNIV. s x * (THE fa. \<forall>i. f (X $ x) $ i = (\<Sum>x\<in>UNIV. fa x * Y $ x $ i)) i)"
      by auto
  qed
qed

text\<open>This is the second part of the theorem 2.15 in the book "Advanced Linear Algebra" by Steven Roman.\<close>
lemma matrix'_compose:
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'m^'m" and Z::"'a^'p^'p"
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"  and basis_Z: "is_basis (set_of_vector Z)"
  and linear_f: "linear ((*s)) ((*s)) f" and linear_g: "linear ((*s)) ((*s)) g"
  shows "matrix' X Z (g \<circ> f) = (matrix' Y Z g) ** (matrix' X Y f)"
proof (unfold matrix_eq, clarify)
  fix a::"('a, 'n) vec"
  obtain v where v: "a = coord X v" using bij_coord[OF basis_X]
    by (meson bij_pointE)
  have linear_gf: "linear ((*s)) ((*s)) (g \<circ> f)"
    using Vector_Spaces.linear_compose[OF linear_f linear_g] .
  have "matrix' X Z (g \<circ> f) *v a = matrix' X Z (g \<circ> f) *v (coord X v)" unfolding v ..
  also have "... = coord Z ((g \<circ> f) v)" unfolding coord_matrix'[OF basis_X basis_Z linear_gf, symmetric] ..
  also have "... = coord Z (g (f v))" unfolding o_def ..
  also have "... = (matrix' Y Z g) *v (coord Y (f v))" unfolding coord_matrix'[OF basis_Y basis_Z linear_g] ..
  also have "... = (matrix' Y Z g) *v ((matrix' X Y f) *v (coord X v))" unfolding coord_matrix'[OF basis_X basis_Y linear_f] ..
  also have "... = ((matrix' Y Z g) ** (matrix' X Y f)) *v (coord X v)" unfolding matrix_vector_mul_assoc ..
  finally show "matrix' X Z (g \<circ> f) *v a = matrix' Y Z g ** matrix' X Y f *v a" unfolding v .
qed


lemma exists_linear_eq_matrix':
  fixes A::"'a::{field}^'m^'n" and X::"'a^'m^'m" and Y::"'a^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  shows "\<exists>f. matrix' X Y f = A \<and> linear ((*s)) ((*s)) f" 
proof -
  define f where "f v = sum (\<lambda>j. A $ j $ (THE k. v = X $ k) *s Y $ j) UNIV" for v
  have indep: "vec.independent (set_of_vector X)"
    using basis_X unfolding is_basis_def by auto
  define g where "g = vec.construct (set_of_vector X) f"
  have linear_g: "linear ((*s)) ((*s)) g" and f_eq_g: "(\<forall>x \<in> (set_of_vector X). g x = f x)"
    using vec.linear_construct[OF indep] vec.construct_basis[OF indep]
    unfolding g_def module_hom_iff_linear
    by auto
  show ?thesis
  proof (rule exI[of _ g], rule conjI)
    show "matrix' X Y g = A"
    proof (rule matrix'2)
      show "is_basis (set_of_vector X)" using basis_X .
      show "is_basis (set_of_vector Y)" using basis_Y .
      show "\<forall>i. g (X $ i) = (\<Sum>j\<in>UNIV. A $ j $ i *s Y $ j)" 
      proof (clarify)
        fix i
        have the_k_eq_i: "(THE k. X $ i = X $ k) = i"
        proof (rule the_equality)
          show "X $ i = X $ i" ..
          fix k assume Xi_Xk: "X $ i = X $ k"  show "k = i" using Xi_Xk basis_X inj_eq inj_op_nth by metis
        qed      
        have Xi_in_X:"X$i \<in> (set_of_vector X)" unfolding set_of_vector_def by auto
        have "g (X$i) = f (X$i)" using f_eq_g Xi_in_X by simp
        also have "... = (\<Sum>j\<in>UNIV. A $ j $ (THE k. X $ i = X $ k) *s Y $ j)" unfolding f_def ..
        also have "... = (\<Sum>j\<in>UNIV. A $ j $ i *s Y $ j)" unfolding the_k_eq_i ..
        finally show "g (X $ i) = (\<Sum>j\<in>UNIV. A $ j $ i *s  Y $ j)" .
      qed
    qed
    show "linear ((*s)) ((*s)) g" using linear_g .
  qed
qed


lemma matrix'_surj: 
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  shows "surj (matrix' X Y)"
proof (unfold surj_def, clarify)
  fix A
  show "\<exists>f. A = matrix' X Y f"
    using exists_linear_eq_matrix'[OF basis_X basis_Y, of A] unfolding matrix'_def by auto
qed


text\<open>Properties of @{thm "matrix_change_of_basis_def"}.\<close>

text\<open>This is the first part of the theorem 2.12 in the book "Advanced Linear Algebra" by Steven Roman.\<close>

lemma matrix_change_of_basis_works:
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" 
  and basis_Y: "is_basis (set_of_vector Y)"
  shows "(matrix_change_of_basis X Y) *v (coord X v) = (coord Y v)"
proof (unfold matrix_mult_sum matrix_change_of_basis_def column_def coord_def, vector, auto)
  fix i
  obtain f where f: "(\<Sum>x\<in>UNIV. f x *s Y $ x) = v" using basis_UNIV[OF basis_Y] by blast
  obtain g where g: "(\<Sum>x\<in>UNIV. g x *s X $ x) = v" using basis_UNIV[OF basis_X] by blast
  define t where "t x = (THE f. X $ x= (\<Sum>a\<in>UNIV. f a *s Y $ a))" for x
  define w where "w i = (\<Sum>x\<in>UNIV. g x * t x i)" for i
  have the_f:"(THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * Y $ x $ i)) = f"
  proof (rule the_equality)
    show "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * Y $ x $ i)" using f by auto
    fix fa assume "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x * Y $ x $ i)"
    hence "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x *s Y $ x) $ i" unfolding sum_component by simp
    hence fa: " v = (\<Sum>x\<in>UNIV. fa x *s Y $ x)" unfolding vec_eq_iff .
    show "fa = f"
      using basis_combination_unique[OF basis_Y] fa f by simp
  qed
  have the_g: "(THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) = g"
  proof (rule the_equality)
    show "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. g x * X $ x $ i)" using g by auto
    fix fa assume "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x * X $ x $ i)"
    hence "\<forall>i. v $ i = (\<Sum>x\<in>UNIV. fa x *s X $ x) $ i" unfolding sum_component by simp
    hence fa: " v = (\<Sum>x\<in>UNIV. fa x *s X $ x)" unfolding vec_eq_iff .
    show "fa = g"
      using basis_combination_unique[OF basis_X] fa g by simp
  qed  
  have "(\<Sum>x\<in>UNIV. f x *s Y $ x) = (\<Sum>x\<in>UNIV. g x *s X $ x)" unfolding f g ..
  also have "... = (\<Sum>x\<in>UNIV. g x *s (sum  (\<lambda>i. (t x i) *s Y $ i) UNIV))" unfolding t_def
  proof (rule sum.cong)
    fix x
    obtain h where h: "(\<Sum>a\<in>UNIV. h a *s Y $ a) = X$x" using basis_UNIV[OF basis_Y] by blast
    have the_h: "(THE f. X $ x = (\<Sum>a\<in>UNIV. f a *s Y $ a))=h" 
    proof (rule the_equality)
      show " X $ x = (\<Sum>a\<in>UNIV. h a *s Y $ a)" using h by simp
      fix f assume f: "X $ x = (\<Sum>a\<in>UNIV. f a *s Y $ a)"
      show "f = h" using basis_combination_unique[OF basis_Y] f h by simp
    qed
    show " g x *s X $ x = g x *s (\<Sum>i\<in>UNIV. (THE f. X $ x = (\<Sum>a\<in>UNIV. f a *s Y $ a)) i *s Y $ i)" unfolding the_h h ..
  qed rule
  also have "... = (\<Sum>x\<in>UNIV. (sum  (\<lambda>i. g x *s ((t x i) *s Y $ i)) UNIV))" unfolding vec.scale_sum_right ..
  also have "... = (\<Sum>i\<in>UNIV. \<Sum>x\<in>UNIV. g x *s (t x i *s Y $ i))" by (rule sum.swap)
  also have "... =  (\<Sum>i\<in>UNIV. (\<Sum>x\<in>UNIV. g x * t x i) *s Y $ i)" unfolding vec.scale_sum_left by auto
  finally have "(\<Sum>x\<in>UNIV. f x *s Y $ x) = (\<Sum>i\<in>UNIV. (\<Sum>x\<in>UNIV. g x * t x i) *s Y $ i) " .  
  hence "f=w" using basis_combination_unique[OF basis_Y] unfolding w_def by auto  
  thus "(\<Sum>x\<in>UNIV. (THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) x * (THE f. \<forall>i. X $ x $ i = (\<Sum>x\<in>UNIV. f x * Y $ x $ i)) i) =
    (THE f. \<forall>i. v $ i = (\<Sum>x\<in>UNIV. f x * Y $ x $ i)) i" unfolding the_f the_g unfolding w_def t_def unfolding vec_eq_iff by auto
qed



lemma matrix_change_of_basis_mat_1:
  fixes X::"'a::{field}^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)"
  shows "matrix_change_of_basis X X = mat 1"
proof (unfold matrix_change_of_basis_def coord_def mat_def, vector, auto)
  fix j::"'n" 
  define f :: "'n \<Rightarrow> 'a" where "f i = (if i=j then 1 else 0)" for i
  have UNIV_rw: "UNIV = insert j (UNIV-{j})" by auto
  have "(\<Sum>x\<in>UNIV. f x *s X $ x) = (\<Sum>x\<in>(insert j (UNIV-{j})). f x *s X $ x)" using UNIV_rw by simp
  also have "... = (\<lambda>x. f x *s X $ x) j + (\<Sum>x\<in>(UNIV-{j}). f x *s X $ x)" by (rule sum.insert, simp+)
  also have "... = X$j + (\<Sum>x\<in>(UNIV-{j}). f x *s X $ x)" unfolding f_def by simp
  also have "... = X$j + 0" unfolding add_left_cancel f_def by (rule sum.neutral, simp)
  finally have f: "(\<Sum>x\<in>UNIV. f x *s X $ x) = X$j" by simp
  have the_f: "(THE f. \<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) = f"
  proof (rule the_equality)
    show "\<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)"  using f unfolding vec_eq_iff unfolding sum_component by simp
    fix fa assume "\<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. fa x * X $ x $ i)"
    hence "\<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. fa x *s X $ x) $ i" unfolding sum_component by simp
    hence fa: "X $ j =  (\<Sum>x\<in>UNIV. fa x *s X $ x)" unfolding vec_eq_iff .
    show "fa = f" using basis_combination_unique[OF basis_X] fa f by simp
  qed
  show "(THE f. \<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) j = 1" unfolding the_f f_def by simp
  fix i assume i_not_j: "i \<noteq> j"
  show "(THE f. \<forall>i. X $ j $ i = (\<Sum>x\<in>UNIV. f x * X $ x $ i)) i = 0" unfolding the_f f_def using i_not_j by simp
qed


text\<open>Relationships between @{thm "matrix'_def"} and @{thm "matrix_change_of_basis_def"}.
      This is the theorem 2.16 in the book "Advanced Linear Algebra" by Steven Roman.\<close>

lemma matrix'_matrix_change_of_basis:
  fixes B::"'a::{field}^'n^'n" and B'::"'a^'n^'n" and C::"'a^'m^'m" and C'::"'a^'m^'m"
  assumes basis_B: "is_basis (set_of_vector B)" and basis_B': "is_basis (set_of_vector B')"
  and basis_C: "is_basis (set_of_vector C)" and basis_C': "is_basis (set_of_vector C')"
  and linear_f: "linear ((*s)) ((*s)) f"
  shows "matrix' B' C' f = matrix_change_of_basis C C' ** matrix' B C f ** matrix_change_of_basis B' B"
proof (unfold matrix_eq, clarify)
  fix x
  obtain v where v: "x=coord B' v" using bij_coord[OF basis_B'] by (meson bij_pointE)
  have "matrix_change_of_basis C C' ** matrix' B C f** matrix_change_of_basis B' B *v (coord B' v) 
    = matrix_change_of_basis C C' ** matrix' B C f *v (matrix_change_of_basis B' B *v (coord B' v)) " unfolding matrix_vector_mul_assoc .. 
  also have "... = matrix_change_of_basis C C' ** matrix' B C f *v (coord B v)" unfolding matrix_change_of_basis_works[OF basis_B' basis_B] ..
  also have "... = matrix_change_of_basis C C' *v (matrix' B C f *v (coord B v))" unfolding matrix_vector_mul_assoc ..
  also have "... = matrix_change_of_basis C C' *v (coord C (f v))" unfolding coord_matrix'[OF basis_B basis_C linear_f] ..
  also have "... = coord C' (f v)" unfolding matrix_change_of_basis_works[OF basis_C basis_C'] ..
  also have "... = matrix' B' C' f *v coord B' v"  unfolding coord_matrix'[OF basis_B' basis_C' linear_f] ..
  finally show " matrix' B' C' f *v x = matrix_change_of_basis C C' ** matrix' B C f ** matrix_change_of_basis B' B *v x" unfolding v ..
qed

lemma matrix'_id_eq_matrix_change_of_basis:
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  shows "matrix' X Y (id) = matrix_change_of_basis X Y"
  unfolding matrix'_def matrix_change_of_basis_def unfolding id_def ..

text\<open>Relationships among @{thm "invertible_lf_def"}, @{thm "matrix_change_of_basis_def"}, @{thm "matrix'_def"} and @{thm "invertible_def"}.\<close>

text\<open>This is the second part of the theorem 2.12 in the book "Advanced Linear Algebra" by Steven Roman.\<close>

lemma matrix_inv_matrix_change_of_basis:
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
  shows"matrix_change_of_basis Y X = matrix_inv (matrix_change_of_basis X Y)"
proof (rule matrix_inv_unique[symmetric])
  have linear_id: "linear ((*s)) ((*s)) id" by (metis vec.linear_id)
  have "(matrix_change_of_basis Y X) ** (matrix_change_of_basis X Y) = (matrix' Y X id) ** (matrix' X Y id)"
    unfolding matrix'_id_eq_matrix_change_of_basis[OF basis_X basis_Y]
    unfolding matrix'_id_eq_matrix_change_of_basis[OF basis_Y basis_X] ..
  also have "... = matrix' X X (id \<circ> id)" using matrix'_compose[OF basis_X basis_Y basis_X linear_id linear_id] ..
  also have "... = matrix_change_of_basis X X" using  matrix'_id_eq_matrix_change_of_basis[OF basis_X basis_X] unfolding o_def id_def .
  also have "... = mat 1" using matrix_change_of_basis_mat_1[OF basis_X] .
  finally show "matrix_change_of_basis Y X ** matrix_change_of_basis X Y = mat 1" .  
  have "(matrix_change_of_basis X Y) ** (matrix_change_of_basis Y X) = (matrix' X Y id) ** (matrix' Y X id)"
    unfolding matrix'_id_eq_matrix_change_of_basis[OF basis_X basis_Y]
    unfolding matrix'_id_eq_matrix_change_of_basis[OF basis_Y basis_X] ..
  also have "... = matrix' Y Y (id \<circ> id)" using matrix'_compose[OF basis_Y basis_X basis_Y linear_id linear_id] ..
  also have "... = matrix_change_of_basis Y Y" using  matrix'_id_eq_matrix_change_of_basis[OF basis_Y basis_Y] unfolding o_def id_def .
  also have "... = mat 1" using matrix_change_of_basis_mat_1[OF basis_Y] . 
  finally show "matrix_change_of_basis X Y ** matrix_change_of_basis Y X = mat 1" .
qed

text\<open>The following four lemmas are the proof of the theorem 2.13 in the book "Advanced Linear Algebra" by Steven Roman.\<close>

corollary invertible_matrix_change_of_basis:
  fixes X::"'a::{field}^'n^'n" and Y::"'a^'n^'n"
  assumes basis_X: "is_basis (set_of_vector X)" and  basis_Y: "is_basis (set_of_vector Y)"
  shows "invertible (matrix_change_of_basis X Y)"
  by (metis basis_X basis_Y invertible_left_inverse vec.linear_id 
    matrix'_id_eq_matrix_change_of_basis matrix'_matrix_change_of_basis 
    matrix_change_of_basis_mat_1)

lemma invertible_lf_imp_invertible_matrix':
fixes f:: "'a::{field}^'b \<Rightarrow> 'a^'b"
assumes "invertible_lf ((*s)) ((*s)) f" and basis_X: "is_basis (set_of_vector X)" and basis_Y: "is_basis (set_of_vector Y)"
shows "invertible (matrix' X Y f)"
  by (metis (lifting) assms(1) basis_X basis_Y invertible_lf_def invertible_lf_imp_invertible_matrix
    invertible_matrix_change_of_basis invertible_mult is_basis_cart_basis' matrix'_eq_matrix matrix'_matrix_change_of_basis)

lemma invertible_matrix'_imp_invertible_lf:
fixes f:: "'a::{field}^'b \<Rightarrow> 'a^'b"
  assumes "invertible (matrix' X Y f)"  and basis_X: "is_basis (set_of_vector X)" 
  and linear_f: "linear ((*s)) ((*s)) f" and basis_Y: "is_basis (set_of_vector Y)"
  shows "invertible_lf ((*s)) ((*s)) f"
  unfolding invertible_matrix_iff_invertible_lf'[OF linear_f, symmetric]
  by (metis assms(1) basis_X basis_Y id_o invertible_matrix_change_of_basis 
     invertible_mult is_basis_cart_basis' linear_f vec.linear_id 
    matrix'_compose matrix'_eq_matrix matrix'_id_eq_matrix_change_of_basis matrix'_matrix_change_of_basis)

lemma invertible_matrix_is_change_of_basis:
  assumes invertible_P: "invertible P" and basis_X: "is_basis (set_of_vector X)" 
  shows "\<exists>!Y. matrix_change_of_basis Y X = P \<and> is_basis (set_of_vector Y)"
proof (auto)
  show "\<exists>Y. matrix_change_of_basis Y X = P \<and> is_basis (set_of_vector Y)"
  proof -
    fix i j
    obtain f where P: "P = matrix' X X f" and linear_f: "linear ((*s)) ((*s)) f"
      using exists_linear_eq_matrix'[OF basis_X basis_X, of P] by blast
    show ?thesis    
    proof (rule exI[of _ "\<chi> j. f (X$j)"], rule conjI) 
      show "matrix_change_of_basis (\<chi> j. f (X $ j)) X = P" unfolding matrix_change_of_basis_def P matrix'_def by vector
      have invertible_f: "invertible_lf ((*s)) ((*s)) f" using invertible_matrix'_imp_invertible_lf[OF _ basis_X linear_f basis_X] using invertible_P unfolding P by simp
      have rw: "set_of_vector (\<chi> j. f (X $ j)) = f`(set_of_vector X)" unfolding set_of_vector_def by auto
      show "is_basis (set_of_vector (\<chi> j. f (X $ j)))" unfolding rw using basis_image_linear[OF invertible_f basis_X] .
    qed
  qed 
  fix Y Z
  assume basis_Y:"is_basis (set_of_vector Y)" and eq: "matrix_change_of_basis Z X = matrix_change_of_basis Y X" and basis_Z: "is_basis (set_of_vector Z)"
  have ZY_coord: "\<forall>i. coord X (Z$i) = coord X (Y$i)" using eq unfolding matrix_change_of_basis_def unfolding vec_eq_iff by vector
  show "Y=Z" by (vector, metis ZY_coord coord_eq[OF basis_X])
qed


subsection\<open>Equivalent Matrices\<close>

text\<open>Next definition follows the one presented in Modern Algebra by Seth Warner.\<close>

definition "equivalent_matrices A B = (\<exists>P Q. invertible P \<and> invertible Q \<and> B = (matrix_inv P)**A**Q)"

lemma exists_basis: "\<exists>X::'a::{field}^'n^'n. is_basis (set_of_vector X)"
  using is_basis_cart_basis' by auto

lemma equivalent_implies_exist_matrix':
  assumes equivalent: "equivalent_matrices A B"
  shows "\<exists>X Y X' Y' f::'a::{field}^'n\<Rightarrow>'a^'m. 
  linear ((*s)) ((*s)) f \<and> matrix' X Y f = A \<and> matrix' X' Y' f = B \<and> is_basis (set_of_vector X) 
  \<and> is_basis (set_of_vector Y) \<and> is_basis (set_of_vector X') \<and> is_basis (set_of_vector Y')"
proof -
  obtain X::"'a^'n^'n" where X: "is_basis (set_of_vector X)" using exists_basis by blast
  obtain Y::"'a^'m^'m" where Y: "is_basis (set_of_vector Y)" using exists_basis by blast
  obtain P Q where B_PAQ: "B=(matrix_inv P)**A**Q" and inv_P: "invertible P" and inv_Q: "invertible Q" 
    using equivalent unfolding equivalent_matrices_def by auto
  obtain f where f_A: "matrix' X Y f = A" and linear_f: "linear ((*s)) ((*s)) f" 
    using exists_linear_eq_matrix'[OF X Y] by auto   
  obtain X'::"'a^'n^'n" where X': "is_basis (set_of_vector X')" and Q:"matrix_change_of_basis X' X = Q" 
    using invertible_matrix_is_change_of_basis[OF inv_Q X] by fast
  obtain Y'::"'a^'m^'m" where Y': "is_basis (set_of_vector Y')" and P: "matrix_change_of_basis Y' Y = P" 
    using invertible_matrix_is_change_of_basis[OF inv_P Y] by fast
  have matrix_inv_P: "matrix_change_of_basis Y Y' = matrix_inv P"
    using matrix_inv_matrix_change_of_basis[OF Y' Y] P by simp
  have "matrix' X' Y' f = matrix_change_of_basis Y Y' ** matrix' X Y f ** matrix_change_of_basis X' X" 
    using matrix'_matrix_change_of_basis[OF X X' Y Y' linear_f] .
  also have "... = (matrix_inv P) ** A ** Q" unfolding matrix_inv_P f_A Q ..
  also have "... = B" using B_PAQ ..
  finally show ?thesis using f_A X X' Y Y' linear_f by fast
qed


lemma exist_matrix'_implies_equivalent:
  assumes A: "matrix' X Y f = A"
  and B: "matrix' X' Y' f = B"
  and X: "is_basis (set_of_vector X)"
  and Y: "is_basis (set_of_vector Y)" 
  and X': "is_basis (set_of_vector X')"
  and Y': "is_basis (set_of_vector Y')"
  and linear_f: "linear ((*s)) ((*s)) f"
  shows "equivalent_matrices A B"
proof (unfold equivalent_matrices_def, rule exI[of _ "matrix_change_of_basis Y' Y"], rule exI[of _ "matrix_change_of_basis X' X"], auto)
  have inv: "matrix_change_of_basis Y Y' = matrix_inv (matrix_change_of_basis Y' Y)" using matrix_inv_matrix_change_of_basis[OF Y' Y] .
  show "invertible (matrix_change_of_basis Y' Y)" using invertible_matrix_change_of_basis[OF Y' Y] .
  show "invertible (matrix_change_of_basis X' X)" using invertible_matrix_change_of_basis[OF X' X] .
  have "B = matrix' X' Y' f" using B ..
  also have "... =  matrix_change_of_basis Y Y' ** matrix' X Y f ** matrix_change_of_basis X' X" using matrix'_matrix_change_of_basis[OF X X' Y Y' linear_f] .
  finally show "B = matrix_inv (matrix_change_of_basis Y' Y) ** A ** matrix_change_of_basis X' X" unfolding inv unfolding A .
qed

text\<open>This is the proof of the theorem 2.18 in the book "Advanced Linear Algebra" by Steven Roman.\<close>
corollary equivalent_iff_exist_matrix':
  shows "equivalent_matrices A B \<longleftrightarrow> (\<exists>X Y X' Y' f::'a::{field}^'n\<Rightarrow>'a^'m. 
  linear ((*s)) ((*s)) f \<and> matrix' X Y f = A \<and> matrix' X' Y' f = B 
  \<and> is_basis (set_of_vector X) \<and> is_basis (set_of_vector Y) 
  \<and> is_basis (set_of_vector X') \<and> is_basis (set_of_vector Y'))"
  by (rule, auto simp add: exist_matrix'_implies_equivalent equivalent_implies_exist_matrix')


subsection\<open>Similar matrices\<close>

definition similar_matrices :: "'a::{semiring_1}^'n^'n \<Rightarrow> 'a::{semiring_1}^'n^'n \<Rightarrow> bool"
  where "similar_matrices A B = (\<exists>P. invertible P \<and> B=(matrix_inv P)**A**P)"

lemma similar_implies_exist_matrix':
  fixes A B::"'a::{field}^'n^'n"
  assumes similar: "similar_matrices A B"
  shows "\<exists>X Y f. linear ((*s)) ((*s)) f \<and> matrix' X X f = A \<and> matrix' Y Y f = B 
    \<and> is_basis (set_of_vector X) \<and> is_basis (set_of_vector Y)"
proof -
 obtain P where inv_P: "invertible P" and B_PAP: "B=(matrix_inv P)**A**P" using similar unfolding similar_matrices_def by blast
 obtain X::"'a^'n^'n" where X: "is_basis (set_of_vector X)" using exists_basis by blast
 obtain f where linear_f: "linear ((*s)) ((*s)) f" and A: "matrix' X X f = A" using exists_linear_eq_matrix'[OF X X] by blast
 obtain Y::"'a^'n^'n" where Y: "is_basis (set_of_vector Y)" and P: "P = matrix_change_of_basis Y X"
  using invertible_matrix_is_change_of_basis[OF inv_P X] by fast 
 have P': "matrix_inv P = matrix_change_of_basis X Y" by (metis (lifting) P X Y matrix_inv_matrix_change_of_basis)
 have "B = (matrix_inv P)**A**P" using B_PAP .
 also have "... =  matrix_change_of_basis X Y ** matrix' X X f ** P " unfolding P' A ..
 also have "... = matrix_change_of_basis X Y ** matrix' X X f ** matrix_change_of_basis Y X" unfolding P ..
 also have "... = matrix' Y Y f" using matrix'_matrix_change_of_basis[OF X Y X Y linear_f] by simp
 finally show ?thesis using X Y A linear_f by fast
qed


lemma exist_matrix'_implies_similar:
  fixes A B::"'a::{field}^'n^'n"
  assumes linear_f: "linear ((*s)) ((*s)) f" and A: "matrix' X X f = A" and B: "matrix' Y Y f = B"
  and X: "is_basis (set_of_vector X)" and Y: "is_basis (set_of_vector Y)"
  shows "similar_matrices A B"
proof (unfold similar_matrices_def, rule exI[of _ "matrix_change_of_basis Y X"], rule conjI)
  have "B=matrix' Y Y f" using B ..
  also have "... = matrix_change_of_basis X Y ** matrix' X X f ** matrix_change_of_basis Y X" using matrix'_matrix_change_of_basis[OF X Y X Y linear_f] by simp
  also have "... =  matrix_inv (matrix_change_of_basis Y X) ** A ** matrix_change_of_basis Y X" unfolding A matrix_inv_matrix_change_of_basis[OF Y X] ..
  finally show "B = matrix_inv (matrix_change_of_basis Y X) ** A ** matrix_change_of_basis Y X" .
  show "invertible (matrix_change_of_basis Y X)" using invertible_matrix_change_of_basis[OF Y X] .
qed

text\<open>This is the proof of the theorem 2.19 in the book "Advanced Linear Algebra" by Steven Roman.\<close>
corollary similar_iff_exist_matrix':
  fixes A B::"'a::{field}^'n^'n"
  shows "similar_matrices A B \<longleftrightarrow> (\<exists>X Y f. linear ((*s)) ((*s)) f \<and> matrix' X X f = A 
    \<and> matrix' Y Y f = B \<and> is_basis (set_of_vector X) \<and> is_basis (set_of_vector Y))"
  by (rule, auto simp add: exist_matrix'_implies_similar similar_implies_exist_matrix')

end
