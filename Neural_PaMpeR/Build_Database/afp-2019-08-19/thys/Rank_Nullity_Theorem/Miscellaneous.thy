(* 
    Title:      Miscellaneous.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Miscellaneous\<close>

theory Miscellaneous
  imports
  "HOL-Analysis.Determinants"
  Mod_Type
  "HOL-Library.Function_Algebras"
begin

context Vector_Spaces.linear begin
sublocale vector_space_pair by unfold_locales\<comment>\<open>TODO: (re)move?\<close>
end

hide_const (open) Real_Vector_Spaces.linear
abbreviation "linear \<equiv> Vector_Spaces.linear"

text\<open>In this file, we present some basic definitions and lemmas about linear algebra and matrices.\<close>

subsection\<open>Definitions of number of rows and columns of a matrix\<close>

definition nrows :: "'a^'columns^'rows => nat"
  where "nrows A = CARD('rows)"

definition ncols :: "'a^'columns^'rows => nat"
  where "ncols A = CARD('columns)"
  
definition matrix_scalar_mult :: "'a::ab_semigroup_mult => 'a ^'n^'m => 'a ^'n^'m"
    (infixl "*k" 70)
  where "k *k A \<equiv> (\<chi> i j. k * A $ i $ j)"

subsection\<open>Basic properties about matrices\<close>

lemma nrows_not_0[simp]:
  shows "0 \<noteq> nrows A" unfolding nrows_def by simp

lemma ncols_not_0[simp]:
  shows "0 \<noteq> ncols A" unfolding ncols_def by simp

lemma nrows_transpose: "nrows (transpose A) = ncols A"
  unfolding nrows_def ncols_def ..

lemma ncols_transpose: "ncols (transpose A) = nrows A"
  unfolding nrows_def ncols_def ..

lemma finite_rows: "finite (rows A)"
  using finite_Atleast_Atmost_nat[of "\<lambda>i. row i A"] unfolding rows_def .

lemma finite_columns: "finite (columns A)"
  using finite_Atleast_Atmost_nat[of "\<lambda>i. column i A"] unfolding columns_def .

lemma transpose_vector: "x v* A = transpose A *v x"
  by simp

lemma transpose_zero[simp]: "(transpose A = 0) = (A = 0)"
  unfolding transpose_def zero_vec_def vec_eq_iff by auto


subsection\<open>Theorems obtained from the AFP\<close>

text\<open>The following theorems and definitions have been obtained from the AFP 
@{url "http://isa-afp.org/browser_info/current/HOL/Tarskis_Geometry/Linear_Algebra2.html"}.
I have removed some restrictions over the type classes.\<close>


lemma vector_scalar_matrix_ac:
  fixes k :: "'a::{field}" and x :: "'a::{field}^'n" and A :: "'a^'m^'n"
  shows "x v* (k *k A) = k *s (x v* A)"
  using scalar_vector_matrix_assoc 
  unfolding vector_matrix_mult_def matrix_scalar_mult_def vec_eq_iff
  by (auto simp add: sum_distrib_left vector_space_over_itself.scale_scale)

lemma transpose_scalar: "transpose (k *k A) = k *k transpose A"
  unfolding transpose_def 
  by (vector, simp add: matrix_scalar_mult_def)

lemma scalar_matrix_vector_assoc:
  fixes A :: "'a::{field}^'m^'n"
  shows "k *s (A *v v) = k *k A *v v"
  by (metis transpose_scalar vector_scalar_matrix_ac vector_transpose_matrix)

lemma matrix_scalar_vector_ac:
  fixes A :: "'a::{field}^'m^'n"
  shows "A *v (k *s v) = k *k A *v v"
  by (simp add: Miscellaneous.scalar_matrix_vector_assoc vec.scale)


definition
  is_basis :: "('a::{field}^'n) set => bool" where
  "is_basis S \<equiv> vec.independent S \<and> vec.span S = UNIV"

lemma card_finite:
  assumes "card S = CARD('n::finite)"
  shows "finite S"
proof -
  from \<open>card S = CARD('n)\<close> have "card S \<noteq> 0" by simp
  with card_eq_0_iff [of S] show "finite S" by simp
qed

lemma independent_is_basis:
  fixes B :: "('a::{field}^'n) set"
  shows "vec.independent B \<and> card B = CARD('n) \<longleftrightarrow> is_basis B"
proof
  assume "vec.independent B \<and> card B = CARD('n)"
  hence "vec.independent B" and "card B = CARD('n)" by simp+
  from card_finite [of B, where 'n = 'n] and \<open>card B = CARD('n)\<close>
  have "finite B" by simp
  from \<open>card B = CARD('n)\<close>
  have "card B = vec.dim (UNIV :: (('a^'n) set))" unfolding vec_dim_card .
  with vec.card_eq_dim [of B UNIV] and \<open>finite B\<close> and \<open>vec.independent B\<close>
  have "vec.span B = UNIV" by auto
  with \<open>vec.independent B\<close> show "is_basis B" unfolding is_basis_def ..
next
  assume "is_basis B"
  hence "vec.independent B" unfolding is_basis_def ..
  moreover have "card B = CARD('n)"
  proof -
    have "B \<subseteq> UNIV" by simp
    moreover
    { from \<open>is_basis B\<close> have "UNIV \<subseteq> vec.span B" and "vec.independent B"
        unfolding is_basis_def
        by simp+ }
    ultimately have "card B = vec.dim (UNIV::((real^'n) set))"
      using vec.basis_card_eq_dim [of B UNIV]
      unfolding vec_dim_card
      by simp
    then show "card B = CARD('n)"
      by (metis vec_dim_card)
  qed
  ultimately show "vec.independent B \<and> card B = CARD('n)" ..
qed

lemma basis_finite:
  fixes B :: "('a::{field}^'n) set"
  assumes "is_basis B"
  shows "finite B"
proof -
  from independent_is_basis [of B] and \<open>is_basis B\<close> have "card B = CARD('n)"
    by simp
  with card_finite [of B, where 'n = 'n] show "finite B" by simp
qed

text\<open>Here ends the statements obtained from AFP: 
  @{url "http://isa-afp.org/browser_info/current/HOL/Tarskis_Geometry/Linear_Algebra2.html"}
  which have been generalized.\<close>

subsection\<open>Basic properties involving span, linearity and dimensions\<close>

context finite_dimensional_vector_space
begin

text\<open>This theorem is the reciprocal theorem of @{thm "indep_card_eq_dim_span"}\<close>

lemma card_eq_dim_span_indep:
  assumes "dim (span A) = card A" and "finite A"
  shows "independent A" 
  by (metis assms card_le_dim_spanning dim_subset equalityE span_superset)

lemma dim_zero_eq:
  assumes dim_A: "dim A = 0"
  shows "A = {} \<or> A = {0}"
  using dim_A local.card_ge_dim_independent local.independent_empty by force

lemma dim_zero_eq': 
  assumes A: "A = {} \<or> A = {0}"
  shows "dim A = 0"
using assms local.dim_span local.indep_card_eq_dim_span local.independent_empty by fastforce

lemma dim_zero_subspace_eq:
  assumes subs_A: "subspace A"
  shows "(dim A = 0) = (A = {0})" 
  by (metis dim_zero_eq dim_zero_eq' subspace_0[OF subs_A] empty_iff)

lemma span_0_imp_set_empty_or_0:
  assumes "span A = {0}"
  shows "A = {} \<or> A = {0}" by (metis assms span_superset subset_singletonD)

end

context Vector_Spaces.linear
begin

lemma linear_injective_ker_0:
  shows "inj f = ({x. f x = 0} = {0})"
  using inj_iff_eq_0 by auto

end

lemma snd_if_conv:
  shows "snd (if P then (A,B) else (C,D))=(if P then B else D)" by simp

subsection\<open>Basic properties about matrix multiplication\<close>

lemma row_matrix_matrix_mult:
  fixes A::"'a::{comm_ring_1}^'n^'m"
  shows "(P $ i) v* A = (P ** A) $ i"
  unfolding vec_eq_iff
  unfolding vector_matrix_mult_def unfolding matrix_matrix_mult_def
  by (auto intro!: sum.cong)

corollary row_matrix_matrix_mult':
  fixes A::"'a::{comm_ring_1}^'n^'m"
  shows "(row i P) v* A = row i (P ** A)"
  using row_matrix_matrix_mult unfolding row_def vec_nth_inverse .

lemma column_matrix_matrix_mult:
  shows "column i (P**A) = P *v (column i A)"
  unfolding column_def matrix_vector_mult_def matrix_matrix_mult_def by fastforce

lemma matrix_matrix_mult_inner_mult:
  shows "(A ** B) $ i $ j = row i A \<bullet> column j B"
  unfolding inner_vec_def matrix_matrix_mult_def row_def column_def by auto


lemma matrix_vmult_column_sum:
  fixes A::"'a::{field}^'n^'m"
  shows "\<exists>f. A *v x = sum (\<lambda>y. f y *s y) (columns A)"
proof (rule exI[of _ "\<lambda>y. sum (\<lambda>i. x $ i) {i. y = column i A}"])
  let ?f="\<lambda>y. sum (\<lambda>i. x $ i) {i. y = column i A}"  
  let ?g="(\<lambda>y. {i. y=column i (A)})"
  have inj: "inj_on ?g (columns (A))" unfolding inj_on_def unfolding columns_def by auto
  have union_univ: "\<Union> (?g`(columns (A))) = UNIV" unfolding columns_def by auto
  have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)" unfolding matrix_mult_sum ..
  also have "... = sum (\<lambda>i.  x $ i *s column i A) (\<Union>(?g`(columns A)))" unfolding union_univ ..
  also have "... = sum (sum ((\<lambda>i.  x $ i *s column i A)))  (?g`(columns A))"
    by (rule sum.Union_disjoint[unfolded o_def], auto) 
  also have "... = sum ((sum ((\<lambda>i.  x $ i *s column i A))) \<circ> ?g)  (columns A)" 
    by (rule sum.reindex, simp add: inj)
  also have "... =  sum (\<lambda>y. ?f y *s y) (columns A)"
  proof (rule sum.cong, unfold o_def)
    fix xa
    have "sum (\<lambda>i. x $ i *s column i A) {i. xa = column i A} 
      = sum (\<lambda>i. x $ i *s xa) {i. xa = column i A}" by simp
    also have "... = sum (\<lambda>i. x $ i) {i. xa = column i A} *s xa" 
      using vec.scale_sum_left[of "(\<lambda>i. x $ i)" "{i. xa = column i A}" xa] ..
    finally show "(\<Sum>i | xa = column i A. x $ i *s column i A) = (\<Sum>i | xa = column i A. x $ i) *s xa" . 
  qed rule
  finally show "A *v x = (\<Sum>y\<in>columns A. (\<Sum>i | y = column i A. x $ i) *s y)" .
qed


subsection\<open>Properties about invertibility\<close>

lemma matrix_inv:
  assumes "invertible M"
  shows matrix_inv_left: "matrix_inv M ** M = mat 1"
    and matrix_inv_right: "M ** matrix_inv M = mat 1"
  using \<open>invertible M\<close> and someI_ex [of "\<lambda> N. M ** N = mat 1 \<and> N ** M = mat 1"]
  unfolding invertible_def and matrix_inv_def
  by simp_all


text\<open>In the library, @{thm "matrix_inv_def"} allows the use of non squary matrices.
  The following lemma can be also proved fixing @{term "A::'a::{semiring_1}^'n^'m"}\<close>

lemma matrix_inv_unique:
  fixes A::"'a::{semiring_1}^'n^'n"
  assumes AB: "A ** B = mat 1" and BA: "B ** A = mat 1"
  shows "matrix_inv A = B"
  by (metis AB BA invertible_def matrix_inv_right matrix_mul_assoc matrix_mul_lid) 


lemma matrix_vector_mult_zero_eq:
  assumes P: "invertible P"
  shows "((P**A)*v x = 0) = (A *v x = 0)"
proof (rule iffI)
  assume "P ** A *v x = 0" 
  hence "matrix_inv P *v (P ** A *v x) = matrix_inv P *v 0" by simp
  hence "matrix_inv P *v (P ** A *v x) =  0" by (metis matrix_vector_mult_0_right)
  hence "(matrix_inv P ** P ** A) *v x =  0" by (metis matrix_vector_mul_assoc)
  thus "A *v x =  0" by (metis assms matrix_inv_left matrix_mul_lid)
next
  assume "A *v x = 0" 
  thus "P ** A *v x = 0" by (metis matrix_vector_mul_assoc matrix_vector_mult_0_right)
qed

lemma independent_image_matrix_vector_mult:
  fixes P::"'a::{field}^'n^'m"
  assumes ind_B: "vec.independent B" and inv_P: "invertible P"
  shows "vec.independent (((*v) P)` B)"
proof (rule vec.independent_injective_image)
  show "vec.independent B" using ind_B .
  show "inj_on ((*v) P) (vec.span B)" 
    using inj_matrix_vector_mult[OF inv_P] unfolding inj_on_def by simp
qed

lemma independent_preimage_matrix_vector_mult:
fixes P::"'a::{field}^'n^'n"
assumes ind_B: "vec.independent (((*v) P)` B)" and inv_P: "invertible P"
shows "vec.independent B"
proof -
have "vec.independent (((*v) (matrix_inv P))` (((*v) P)` B))"
  proof (rule independent_image_matrix_vector_mult)
    show "vec.independent ((*v) P ` B)" using ind_B .
    show "invertible (matrix_inv P)"
      by (metis matrix_inv_left matrix_inv_right inv_P invertible_def)
    qed
moreover have "((*v) (matrix_inv P))` (((*v) P)` B) = B"
    proof (auto)
      fix x assume x: "x \<in> B" show "matrix_inv P *v (P *v x) \<in> B" 
      by (metis (full_types) x inv_P matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
      thus "x \<in> (*v) (matrix_inv P) ` (*v) P ` B" 
      unfolding image_def 
      by (auto, metis  inv_P matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
     qed
ultimately show ?thesis by simp
qed

subsection\<open>Properties about the dimension of vectors\<close>

lemma dimension_vector[code_unfold]: "vec.dimension TYPE('a::{field}) TYPE('rows::{mod_type})=CARD('rows)"
proof -
let ?f="\<lambda>x. axis (from_nat x) 1::'a^'rows::{mod_type}"
have "vec.dimension TYPE('a::{field}) TYPE('rows::{mod_type}) = card (cart_basis::('a^'rows::{mod_type}) set)"
  unfolding vec.dimension_def ..
also have "... = card{..<CARD('rows)}" unfolding cart_basis_def 
  proof (rule bij_betw_same_card[symmetric, of ?f], unfold bij_betw_def, unfold inj_on_def axis_eq_axis, auto)
     fix x y assume x: "x < CARD('rows)" and y: "y < CARD('rows)" and eq: "from_nat x = (from_nat y::'rows)"
     show "x = y" using from_nat_eq_imp_eq[OF eq x y] .
     next
     fix i show "axis i 1 \<in> (\<lambda>x. axis (from_nat x::'rows) 1) ` {..<CARD('rows)}" unfolding image_def
     by (auto, metis lessThan_iff to_nat_from_nat to_nat_less_card)
  qed
also have "... = CARD('rows)" by (metis card_lessThan)
finally show ?thesis .
qed

subsection\<open>Instantiations and interpretations\<close>

text\<open>Functions between two real vector spaces form a real vector\<close>
instantiation "fun" :: (real_vector, real_vector) real_vector
begin

definition "scaleR_fun a f = (\<lambda>i. a *\<^sub>R f i )"

instance 
  by (intro_classes, auto simp add: fun_eq_iff scaleR_fun_def scaleR_left.add scaleR_right.add)
end


instantiation vec :: (type, finite) equal
begin
definition equal_vec :: "('a, 'b::finite) vec => ('a, 'b::finite) vec => bool" 
  where "equal_vec x y = (\<forall>i. x$i = y$i)"
instance 
proof (intro_classes)
  fix x y::"('a, 'b::finite) vec"
  show "equal_class.equal x y = (x = y)" unfolding equal_vec_def using vec_eq_iff by auto
qed
end

interpretation matrix: vector_space "((*k))::'a::{field}=>'a^'cols^'rows=>'a^'cols^'rows"
proof (unfold_locales)
fix a::'a and x y::"'a^'cols^'rows"
show "a *k (x + y) = a *k x + a *k y"
  unfolding matrix_scalar_mult_def vec_eq_iff
  by (simp add: vector_space_over_itself.scale_right_distrib)
next
fix a b::'a and x::"'a^'cols^'rows"
show "(a + b) *k x = a *k x + b *k x"
unfolding matrix_scalar_mult_def vec_eq_iff
  by (simp add: comm_semiring_class.distrib)
show "a *k (b *k x) = a * b *k x"
  unfolding matrix_scalar_mult_def vec_eq_iff by auto
show"1 *k x = x" unfolding matrix_scalar_mult_def vec_eq_iff by auto
qed

end
