(*  
    Title:      Generalizations2.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Generalization of the Second Part of the Fundamental Theorem of Linear Algebra\<close>

theory Generalizations2
  imports
    Rank_Nullity_Theorem.Fundamental_Subspaces
begin

subsection\<open>Conjugate class\<close>

class cnj = field +
  fixes cnj :: "'a\<Rightarrow>'a"
  assumes cnj_idem[simp]: "cnj (cnj a) = a"
  and cnj_add: "cnj (a+b) = cnj a + cnj b"
  and cnj_mult: "cnj (a * b) = cnj a * cnj b"
begin

lemma two_not_one: "2 \<noteq> (1::'a)"
proof (rule ccontr, simp)
  assume "2 = (1::'a)"
  hence "2 - 1 = 1 - (1::'a)" by auto
  hence "1 = (0::'a)" by auto
  thus False using one_neq_zero by contradiction
qed

lemma cnj_0[simp]: "cnj 0 = 0"
  proof -
    have "cnj 0 = cnj (0 + 0)" by auto
    also have "... = cnj 0 + cnj 0" unfolding cnj_add ..
    also have "... = 2 * (cnj 0)" by (simp add: local.mult_2)
    finally have "cnj 0 = 2 * cnj 0" .
    thus ?thesis by (auto simp add: two_not_one)
  qed

lemma cnj_0_eq[simp]: "(cnj a = 0) = (a = 0)"
proof auto
  assume cnj_rw: "0 = cnj a"
  have "cnj (cnj a) = a" using cnj_idem by simp
  hence "cnj 0 = a" unfolding cnj_rw .
  hence "a = 0" by simp
  thus "a = cnj a" using cnj_rw by simp
qed

lemma a_cnj_a_0: "(a*cnj a = 0) = (a = 0)"
  by simp
  
end

lemma cnj_sum: "cnj (\<Sum>xa\<in>A. ((f xa))) = (\<Sum>xa\<in>A. cnj (f xa))"
    by (cases "finite A", induct set: finite, auto simp add: cnj_add)

instantiation real :: cnj
begin

definition "(cnj_real :: real\<Rightarrow>real)= id"

instance
by (intro_classes, auto simp add: cnj_real_def)
end


instantiation complex :: cnj
begin

definition "(cnj_complex :: complex\<Rightarrow>complex)= Complex.cnj"

instance
by (intro_classes, auto simp add: cnj_complex_def)
end

subsection\<open>Real\_of\_extended class\<close>

class real_of_extended = real_vector + cnj +
 fixes real_of :: "'a \<Rightarrow> real"
 assumes real_add:"real_of ((a::'a) + b) = real_of a + real_of b"
  and real_uminus: "real_of (-a) = - real_of a"
  and real_scalar_mult: "real_of (c *\<^sub>R a) = c * (real_of a)"
  and real_a_cnj_ge_0: "real_of (a*cnj a)\<ge>0"
begin

lemma real_minus: "real_of (a - b) = real_of a - real_of b"
proof -
  have "real_of (a - b) = real_of (a + - b)" by simp
  also have "... = real_of a + real_of (- b)" unfolding real_add ..
  also have "... = real_of a + - real_of b" unfolding real_uminus ..
  also have "... = real_of a - real_of b" by simp
  finally show ?thesis .
qed

lemma real_0[simp]: "real_of 0 = 0"
proof -
    have "real_of 0 = real_of (0+0)" by auto
    also have "... = real_of 0 + real_of 0" unfolding real_add ..
    also have "... = 2*(real_of 0)" by auto
    finally have "real_of 0 = 2* real_of 0" .
    thus ?thesis by (auto simp add: two_not_one)
qed


lemma real_sum:
  "real_of (sum (\<lambda>i. f i) A) = sum (\<lambda>i. real_of (f i)) A"
proof (cases "finite A")
  case False thus ?thesis by auto
next
  case True
  thus ?thesis
  by (induct, auto simp add: real_add)
qed   

end

instantiation real :: real_of_extended
begin

definition real_of_real :: "real \<Rightarrow> real" where "real_of_real = id"

instance
  by (intro_classes, auto simp add: real_of_real_def cnj_real_def)
end

instantiation complex :: real_of_extended
begin

definition real_of_complex :: "complex \<Rightarrow> real" where "real_of_complex = Re"

instance
  by (intro_classes, auto simp add: real_of_complex_def cnj_complex_def)
end

subsection\<open>Generalizing HMA\<close>

subsubsection\<open>Inner product spaces\<close>

text\<open>We generalize the \<open>real_inner class\<close> to more general inner product spaces.\<close>

locale inner_product_space = vector_space scale
  for scale :: "('a::{field, cnj, real_of_extended} => 'b::ab_group_add => 'b)" +
  fixes inner :: "'b \<Rightarrow> 'b \<Rightarrow> 'a"
  assumes inner_commute: "inner x y = cnj (inner y x)"
  and inner_add_left: "inner (x+y) z = inner x z + inner y z"
  and inner_scaleR_left [simp]:"inner (scale r x) y = r * inner x y"
  and inner_ge_zero [simp]:"0 \<le> real_of (inner x x)"
  and inner_eq_zero_iff [simp]: "inner x x = 0 \<longleftrightarrow> x=0"
  (*Properties related to real and inner that must be assumed.*)
  and real_scalar_mult2: "real_of (inner x x) *\<^sub>R A = inner x x * A"
  and inner_gt_zero_iff: "0 < real_of (inner x x) \<longleftrightarrow> x \<noteq> 0" 


interpretation RV_inner: inner_product_space scaleR inner
  by (unfold_locales) (auto simp: cnj_real_def inner_add_left real_of_real_def algebra_simps inner_commute)

interpretation RR_inner: inner_product_space scaleR "(*)"
by (unfold_locales, auto simp add: cnj_real_def distrib_right real_of_real_def) 
   (metis not_real_square_gt_zero)

interpretation CC_inner: inner_product_space "((*)::complex\<Rightarrow>complex\<Rightarrow>complex)" "\<lambda>x y. x*cnj y"
  apply (unfold_locales) 
  apply (auto simp add: real_of_complex_def cnj_complex_def distrib_left distrib_right complex_mult_cnj complex_neq_0 cmod_power2 complex_norm_square)
  apply (metis Re_complex_of_real complex_neq_0 less_numeral_extra(3) of_real_add of_real_power zero_complex.simps(1))
  by (simp add: distrib_left mult.commute scaleR_conv_of_real)
  
context inner_product_space
begin

lemma inner_zero_left [simp]: "inner 0 x = 0"
  using inner_add_left [of 0 0 x] by (auto simp add: two_not_one)

lemma inner_minus_left [simp]: "inner (- x) y = - inner x y"
  using inner_add_left [of x "- x" y] using add_eq_0_iff by force

lemma inner_diff_left: "inner (x - y) z = inner x z - inner y z"
  using inner_add_left [of x "- y" z] by simp

lemma inner_sum_left: "inner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. inner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: inner_add_left)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma inner_add_right: "inner x (y + z) = inner x y + inner x z"
proof -
  have "inner x (y + z) = cnj (inner (y + z) x)" using inner_commute by blast
  also have "... = cnj ((inner y x) +(inner z x))" using inner_add_left by simp
  also have "... = cnj (inner y x) + cnj (inner z x)" using cnj_add by blast
  also have "... = inner x y + inner x z" 
  using inner_commute[of x y] using inner_commute[of x z] by simp
  finally show ?thesis .
qed


lemma inner_scaleR_right [simp]: "inner x (scale r y) = (cnj r) * (inner x y)"
  using inner_scaleR_left [of r y x]
  by (metis (no_types) cnj_mult local.inner_commute)


lemma inner_zero_right [simp]: "inner x 0 = 0"
  using inner_zero_left [of x]
  by (metis local.inner_commute local.inner_eq_zero_iff)


lemma inner_minus_right [simp]: "inner x (- y) = - inner x y"
  using inner_minus_left [of y x]
  by (metis (no_types) add_eq_0_iff local.inner_add_right local.inner_zero_right)


lemma inner_diff_right: "inner x (y - z) = inner x y - inner x z"
  using inner_diff_left [of y z x]
  by (metis add_uminus_conv_diff local.inner_add_right local.inner_minus_right) 


lemma inner_sum_right: "inner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. inner x (f y))"
proof -
  have "inner x (\<Sum>y\<in>A. f y) = cnj (inner (\<Sum>y\<in>A. f y) x)" using inner_commute by blast
  also have "... = cnj (\<Sum>xa\<in>A. inner (f xa) x)" unfolding inner_sum_left [of f A x] ..
  also have "... = (\<Sum>xa\<in>A. cnj (inner (f xa) x))" unfolding cnj_sum ..
  also have "... = (\<Sum>xa\<in>A. inner x (f xa))" by (rule sum.cong, simp, metis inner_commute)
  finally show ?thesis .
qed
  
lemmas inner_add [algebra_simps] = inner_add_left inner_add_right
lemmas inner_diff [algebra_simps]  = inner_diff_left inner_diff_right
lemmas inner_scaleR = inner_scaleR_left inner_scaleR_right

text \<open>Legacy theorem names\<close>
lemmas inner_left_distrib = inner_add_left
lemmas inner_right_distrib = inner_add_right
lemmas inner_distrib = inner_left_distrib inner_right_distrib


lemma aux_Cauchy:
shows "0 \<le> real_of (inner x x + (cnj a) * (inner x y) + a * ((cnj (inner x y)) + (cnj a) * (inner y y)))"
proof -
  have "(inner (x+scale a y) (x+scale a y)) = (inner (x+scale a y) x) + (inner (x+scale a y) (scale a y))" 
    unfolding inner_add_right ..
  also have "... = inner x x + (cnj a) * (inner x y) + a * ((cnj (inner x y)) + (cnj a) * (inner y y))"
    unfolding inner_add_left
    unfolding inner_scaleR_left
    unfolding inner_scaleR_right
    unfolding inner_commute[of y x]
    unfolding distrib_left
    by auto
  finally show ?thesis by (metis inner_ge_zero)
qed

lemma real_inner_inner: "real_of (inner x x * inner y y) = real_of (inner x x) * real_of (inner y y)"
  by (metis real_scalar_mult real_scalar_mult2) 

lemma Cauchy_Schwarz_ineq:
  "real_of (cnj (inner x y) * inner x y) \<le> real_of (inner x x) * real_of (inner y y)"
proof -
  define cnj_a where "cnj_a = - cnj (inner x y)/ (inner y y)"
  define a where "a = cnj (cnj_a)"
  have cnj_rw: "(cnj a) = cnj_a" 
    unfolding a_def by (simp)
  have rw_0: "(cnj (inner x y)) + (cnj a) * (inner y y) = 0"
    unfolding cnj_rw cnj_a_def by auto
  have "0 \<le> real_of (inner x x + (cnj a) * (inner x y) + a * ((cnj (inner x y)) + (cnj a) * (inner y y)))"
    using aux_Cauchy by auto
  also have "... = real_of (inner x x + (cnj a) * (inner x y))" unfolding rw_0 by auto
  also have "... = real_of (inner x x - cnj (inner x y) * inner x y / inner y y)" 
  unfolding cnj_rw cnj_a_def by auto
  finally have " 0 \<le> real_of (inner x x - cnj (inner x y) * inner x y / inner y y) " .
  hence "0 \<le> real_of (inner y y)  * real_of (inner x x - cnj (inner x y) * inner x y / inner y y)" by auto
  also have "... = real_of (real_of (inner y y)*\<^sub>R(inner x x - cnj (inner x y) * inner x y / inner y y))"
    unfolding real_scalar_mult ..
  also have "... = real_of ((inner y y) * (inner x x - cnj (inner x y) * inner x y / inner y y))"
    unfolding real_scalar_mult2 ..
  also have "... = real_of ((inner x x - cnj (inner x y) * inner x y / inner y y)*(inner y y))" 
    by (simp add: mult.commute)
  also have "... = real_of (((inner x x)*(inner y y) - cnj (inner x y) * inner x y))"
  by (simp add: left_diff_distrib)
  also have "... = real_of ((inner x x)*(inner y y)) - real_of (cnj (inner x y) * inner x y)"
    unfolding real_minus ..
  finally have "real_of (cnj (inner x y) * inner x y) \<le> real_of ((inner x x)*(inner y y))" by auto 
  thus ?thesis unfolding real_inner_inner .
qed
end

hide_const (open) norm

context inner_product_space
begin

definition "norm x = (sqrt (real_of (inner x x)))"

lemmas norm_eq_sqrt_inner = norm_def

lemma inner_cnj_ge_zero[simp]: "real_of ((inner x y) * cnj (inner x y)) \<ge> 0"
  using real_a_cnj_ge_0 by auto

lemma power2_norm_eq_inner: "(norm x)\<^sup>2 = real_of (inner x x)"
  by (simp add: norm_def)

lemma Cauchy_Schwarz_ineq2:
  "sqrt (real_of (cnj (inner x y) * inner x y)) \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have eq: "0 \<le> real_of (cnj (inner x y) * inner x y)" 
    by (simp add: mult.commute)
  have "real_of (cnj (inner x y) * inner x y) \<le> real_of (inner x x) * real_of (inner y y)"
    using Cauchy_Schwarz_ineq .
  thus "(sqrt (real_of (cnj (inner x y) * inner x y)))\<^sup>2 \<le> (norm x * norm y)\<^sup>2" 
  unfolding power_mult_distrib
  unfolding power2_norm_eq_inner unfolding real_sqrt_pow2[OF eq] .
  show "0 \<le> norm x * norm y"
    unfolding norm_eq_sqrt_inner
    by (intro mult_nonneg_nonneg real_sqrt_ge_zero inner_ge_zero)
qed

end

subsubsection\<open>Orthogonality\<close>

hide_const (open) orthogonal

context inner_product_space
begin

definition "orthogonal x y \<longleftrightarrow> inner x y = 0"

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (scale c x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (- x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (scale c x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (- x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  unfolding orthogonal_def inner_add inner_diff by auto

lemma inner_commute_zero: "(inner xa x = 0) = (inner x xa = 0)"
  by (metis cnj_0 local.inner_commute)

lemma vector_sub_project_orthogonal: 
  "inner b (x - scale (inner x b / (inner b b)) b) = 0"
proof -
  have f1: "\<And>b a ba. inner b (scale a ba) = cnj (a * inner ba b)"
    by (metis local.inner_commute local.inner_scaleR_left)
  { assume "b \<noteq> 0"
    hence "cnj (inner x b) = inner b x \<and> inner b b \<noteq> 0"
      by (metis (no_types) local.inner_commute local.inner_eq_zero_iff)
    hence "inner b (x - scale (inner x b / inner b b) b) = 0"
      using f1 local.inner_diff_right by force }
  thus ?thesis by fastforce
qed

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  unfolding orthogonal_def using inner_commute_zero by auto

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
  and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  using assms unfolding pairwise_def
  by (auto simp add: orthogonal_commute)

end

lemma sum_0_all:
  assumes a: "\<forall>a\<in>A. f a \<ge> (0 :: real)" 
  and s0: "sum f A = 0" and f: "finite A"
  shows "\<forall>a\<in>A. f a = 0" 
  using a f s0 sum_nonneg_eq_0_iff by blast


subsection\<open>Vecs as inner product spaces\<close>

locale vec_real_inner = F?: inner_product_space "((*) :: 'a\<Rightarrow>'a\<Rightarrow>'a)" inner_field 
 for inner_field :: "'a\<Rightarrow>'a\<Rightarrow>'a::{field,cnj,real_of_extended}" 
 + fixes inner :: "'a^'n \<Rightarrow> 'a^'n \<Rightarrow>'a" 
 assumes inner_vec_def: "inner x y = sum (\<lambda>i. inner_field (x$i) (y$i)) UNIV"
begin

lemma inner_ge_zero [simp]: "0 \<le> real_of (inner x x)"
  by (auto simp add: inner_vec_def real_sum sum_nonneg)

lemma real_scalar_mult2: "real_of (inner x x) *\<^sub>R A = inner x x * A"
by (auto simp add: inner_vec_def)
  (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux 
  real_scalar_mult2 real_sum scaleR_left.sum scale_sum_left)

lemma i1: "inner x y = cnj (inner y x)"
by (auto simp add: inner_vec_def cnj_sum cnj_mult mult.commute)
   (meson local.inner_commute)

lemma i2: "inner (x + y) z = inner x z + inner y z"
using local.inner_left_distrib sum.distrib inner_vec_def by force

lemma i3: "inner (r *s x) y = r * inner x y"
by (auto simp add: inner_vec_def scale_sum_right)

lemma i4: assumes "inner x x = 0"
shows "x = 0"
proof (unfold vec_eq_iff, clarify, simp)
  fix a
  have "0 = real_of (\<Sum>i\<in>UNIV. inner_field (x $ i) (x $ i))"
    using assms by (simp add: inner_vec_def) 
  also have "... = (\<Sum>i\<in>UNIV. real_of (inner_field (x $ i) (x $ i)))" 
    using real_sum by auto
  finally have "0 = (\<Sum>i\<in>UNIV. real_of (inner_field (x $ i) (x $ i)))" .  
  hence "real_of (inner_field (x $ a) (x $ a)) = 0"
    using sum_0_all F.inner_ge_zero 
    by (metis (no_types, lifting) finite iso_tuple_UNIV_I)
  then show "x $ a = 0"
    by (metis F.inner_eq_zero_iff F.inner_gt_zero_iff real_0)
qed

lemma inner_0_0[simp]: "inner 0 0 = 0"
  unfolding inner_vec_def by auto

sublocale v?: inner_product_space "((*s) :: 'a \<Rightarrow> 'a^'n \<Rightarrow> 'a^'n)" "inner"
proof (unfold_locales, auto simp add: real_scalar_mult2)
  fix x y z::"'a^'n" and r
  show "inner x y = cnj (inner y x)" using i1[of x y] by simp
  show "inner (x + y) z = inner x z + inner y z" using i2 by blast
  show "inner (r *s x) y = r * inner x y" using i3 by blast
  show i: "inner x x = 0 \<Longrightarrow> x = 0" using i4 by blast
  assume "x \<noteq> 0"
  thus "0 < real_of (inner x x)" by (metis i \<open>x \<noteq> 0\<close> inner_0_0 local.inner_ge_zero 
    local.real_scalar_mult2 mult.commute mult_1_left order.not_eq_order_implies_strict real_0)
qed
end


subsection\<open>Matrices and inner product\<close>

locale matrix = 
    COLS?: vec_real_inner "\<lambda>x y. x * cnj y" inner_cols
  + ROWS?: vec_real_inner "\<lambda>x y. x * cnj y" inner_rows
 for inner_cols :: "'a^'cols::{finite, wellorder} \<Rightarrow> 'a^'cols::{finite, wellorder} \<Rightarrow> 'a::{field, cnj, real_of_extended}" 
 and inner_rows :: "'a^'rows::{finite, wellorder} \<Rightarrow> 'a^'rows::{finite, wellorder} \<Rightarrow> 'a" 
begin


lemma dot_lmul_matrix: "inner_rows (x v* A) y = inner_cols x ((\<chi> i j. cnj (A $ i $ j)) *v y)"
 apply (simp add: COLS.inner_vec_def ROWS.inner_vec_def matrix_vector_mult_def 
       vector_matrix_mult_def sum_distrib_right cnj_sum ac_simps)
 proof (unfold sum_distrib_left, subst sum.swap, rule sum.cong, simp)
  fix xa::'cols
  show "(\<Sum>i\<in>UNIV. cnj (y $ i) * (x $ xa * A $ xa $ i)) 
    = (\<Sum>n\<in>UNIV. x $ xa * cnj (y $ n * cnj (A $ xa $ n)))"
  proof (rule sum.cong, simp)
    fix xb:: 'rows
    show "cnj_class.cnj (y $ xb) * (x $ xa * A $ xa $ xb) 
      = x $ xa * cnj_class.cnj (y $ xb * cnj_class.cnj (A $ xa $ xb))"
    unfolding cnj_mult cnj_idem unfolding mult.assoc
    unfolding mult.commute[of "A $ xa $ xb"] by auto
  qed
qed

end

subsection\<open>Orthogonal complement generalized\<close>

context inner_product_space
begin

definition "orthogonal_complement W = {x. \<forall>y \<in> W. orthogonal y x}"

lemma subspace_orthogonal_complement: "subspace (orthogonal_complement W)"
  unfolding subspace_def orthogonal_complement_def
  by (auto simp add: orthogonal_def local.inner_right_distrib)


lemma orthogonal_complement_mono:
  assumes A_in_B: "A \<subseteq> B"
  shows "orthogonal_complement B \<subseteq> orthogonal_complement A"
proof
  fix x assume x: "x \<in> orthogonal_complement B"
  show "x \<in> orthogonal_complement A" using x unfolding orthogonal_complement_def
    by (simp add: orthogonal_def, metis A_in_B in_mono)
qed


lemma B_in_orthogonal_complement_of_orthogonal_complement:
  shows "B \<subseteq> orthogonal_complement (orthogonal_complement B)"
  by (auto simp add: orthogonal_complement_def orthogonal_def inner_commute_zero)

end


subsection\<open>Generalizing projections\<close>

context inner_product_space
begin

text\<open>Projection of two vectors: v onto u\<close>

definition "proj v u = scale (inner v u / inner u u) u"

text\<open>Projection of a onto S\<close>

definition "proj_onto a S = (sum (\<lambda>x. proj a x) S)"

lemma vector_sub_project_orthogonal_proj:
  shows "inner b (x - proj x b) = 0"
using vector_sub_project_orthogonal unfolding proj_def by simp

lemma orthogonal_proj_set:
  assumes yC: "y\<in>C" and C: "finite C" and p: "pairwise orthogonal C"
  shows "orthogonal (a - proj_onto a C) y"
proof -
  have Cy: "C = insert y (C - {y})" using yC
    by blast
  have fth: "finite (C - {y})"
    using C by simp
  show "orthogonal (a - proj_onto a C) y"
    unfolding orthogonal_def unfolding proj_onto_def unfolding proj_def[abs_def]
    unfolding inner_diff
    unfolding inner_sum_left 
    unfolding right_minus_eq
    unfolding sum.remove[OF C yC]
    apply (clarsimp simp add: inner_commute[of y a])
    apply (rule sum.neutral)
    apply clarsimp
    apply (rule p[unfolded pairwise_def orthogonal_def, rule_format])
    using yC by auto
qed

lemma pairwise_orthogonal_proj_set:
  assumes C: "finite C" and p: "pairwise orthogonal C"
  shows "pairwise orthogonal (insert (a - proj_onto a C) C)"
  by (rule pairwise_orthogonal_insert[OF p], auto simp add: orthogonal_proj_set C p)
end

lemma orthogonal_real_eq: "RV_inner.orthogonal = real_inner_class.orthogonal"
  unfolding RV_inner.orthogonal_def[abs_def]
  unfolding real_inner_class.orthogonal_def[abs_def] ..


subsection\<open>Second Part of the Fundamental Theorem of Linear Algebra generalized\<close>

context matrix
begin

lemma cnj_cnj_matrix[simp]: "(\<chi> i j. cnj ((\<chi> i j. cnj (A $ i $ j)) $ i $ j)) = A"
  unfolding vec_eq_iff by auto

lemma cnj_transpose[simp]: "(\<chi> i j. cnj (transpose A $ i $ j)) = transpose (\<chi> i j. cnj (A $ i $ j))"
  unfolding vec_eq_iff transpose_def by auto

lemma null_space_orthogonal_complement_row_space:
  fixes A::"'a^'cols::{finite, wellorder}^'rows::{finite, wellorder}"
  shows "null_space A = COLS.v.orthogonal_complement (row_space (\<chi> i j. cnj (A $ i $ j)))"
proof -
 interpret m: matrix inner_rows inner_cols by unfold_locales
  let ?A="(\<chi> i j. cnj (A $ i $ j))"
  show ?thesis
  proof (unfold null_space_def COLS.v.orthogonal_complement_def, auto) 
    fix x xa assume Ax: "A *v x = 0" and xa: "xa \<in> row_space (\<chi> i j. cnj (A $ i $ j))"
    obtain y where y: "xa = transpose (\<chi> i j. cnj (A $ i $ j)) *v y" using xa unfolding row_space_eq by blast
    have y2: "y v* (\<chi> i j. cnj (A $ i $ j)) = xa"
      using transpose_vector y by fastforce
    show "COLS.v.orthogonal xa x" 
      using m.dot_lmul_matrix[of y ?A x] 
      unfolding cnj_cnj_matrix Ax ROWS.v.inner_zero_right
      unfolding y2 
      unfolding COLS.v.orthogonal_def .
next
   fix x assume xa: "\<forall>xa\<in>row_space (\<chi> i j. cnj (A $ i $ j)). COLS.v.orthogonal xa x"
  show "A *v x = 0"
    using xa unfolding row_space_eq COLS.v.orthogonal_def using COLS.v.inner_eq_zero_iff
    using m.dot_lmul_matrix[of _ ?A] 
    unfolding transpose_vector
    by auto 
       (metis ROWS.i4 m.cnj_cnj_matrix m.dot_lmul_matrix transpose_vector)
  qed
qed



lemma left_null_space_orthogonal_complement_col_space:
  fixes A::"'a^'cols::{finite, wellorder}^'rows::{finite, wellorder}"
  shows "left_null_space A = ROWS.v.orthogonal_complement (col_space (\<chi> i j. cnj (A $ i $ j)))"
proof -
  interpret m: matrix inner_rows inner_cols by unfold_locales
  show ?thesis
  using m.null_space_orthogonal_complement_row_space[of "transpose A"] 
  unfolding left_null_space_eq_null_space_transpose
  unfolding col_space_eq_row_space_transpose by auto
qed

end

text\<open>We can get the explicit results for complex and real matrices\<close>

interpretation real_matrix: matrix "\<lambda>x y::real^'cols::{finite,wellorder}. 
  sum (\<lambda>i. (x$i) * (y$i)) UNIV" "\<lambda>x y. sum (\<lambda>i. (x$i) * (y$i)) UNIV"
  apply (unfold_locales, auto simp add: cnj_real_def real_of_real_def distrib_right)
  using not_real_square_gt_zero by blast

interpretation complex_matrix: matrix "\<lambda>x y::complex^'cols::{finite,wellorder}. 
  sum (\<lambda>i. (x$i) * cnj (y$i)) UNIV" "\<lambda>x y. sum (\<lambda>i. (x$i) * cnj (y$i)) UNIV"
  by (unfold_locales, auto simp add: distrib_right)

lemma null_space_orthogonal_complement_row_space_complex:
  fixes A::"complex^'cols::{finite,wellorder}^'rows::{finite,wellorder}"
  shows "null_space A = complex_matrix.orthogonal_complement (row_space (\<chi> i j. cnj (A $ i $ j)))"
  using complex_matrix.null_space_orthogonal_complement_row_space .

lemma left_null_space_orthogonal_complement_col_space_complex:
  fixes A::"complex^'cols::{finite, wellorder}^'rows::{finite, wellorder}"
  shows "left_null_space A = complex_matrix.orthogonal_complement (col_space (\<chi> i j. cnj (A $ i $ j)))"
  using complex_matrix.left_null_space_orthogonal_complement_col_space .

lemma null_space_orthogonal_complement_row_space_reals:
  fixes A::"real^'cols::{finite,wellorder}^'rows::{finite,wellorder}"
  shows "null_space A = real_matrix.orthogonal_complement (row_space A)"
  using real_matrix.null_space_orthogonal_complement_row_space[of A]
  unfolding cnj_real_def by (simp add: vec_lambda_eta)

lemma left_null_space_orthogonal_complement_col_space_real:
  fixes A::"real^'cols::{finite, wellorder}^'rows::{finite, wellorder}"
  shows "left_null_space A = real_matrix.orthogonal_complement (col_space A)"
  using real_matrix.left_null_space_orthogonal_complement_col_space[of A]
  by (simp add: cnj_real_def vec_lambda_eta)

end
