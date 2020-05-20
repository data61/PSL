(*  Title:       Mathematical Preliminaries
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Mathematical Preliminaries \<close>

text \<open>This section adds useful syntax, abbreviations and theorems to the Isabelle distribution. \<close>

theory MTX_Preliminaries
  imports "Hybrid_Systems_VCs.HS_Preliminaries"

begin


subsection \<open> Syntax \<close>

abbreviation "\<e> k \<equiv> axis k 1"

syntax
  "_ivl_integral" :: "real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> pttrn \<Rightarrow> bool" ("(3\<integral>\<^sub>_\<^sup>_ (_)\<partial>/_)" [0, 0, 10] 10)

translations
  "\<integral>\<^sub>a\<^sup>b f \<partial>x" \<rightleftharpoons> "CONST ivl_integral a b (\<lambda>x. f)"

notation matrix_inv ("_\<^sup>-\<^sup>1" [90])

abbreviation "entries (A::'a^'n^'m) \<equiv> {A $ i $ j | i j. i \<in> UNIV \<and> j \<in> UNIV}"


subsection \<open> Topology and sets \<close>

lemmas compact_imp_bdd_above = compact_imp_bounded[THEN bounded_imp_bdd_above]

lemma comp_cont_image_spec: "continuous_on T f \<Longrightarrow> compact T \<Longrightarrow> compact {f t |t. t \<in> T}"
  using compact_continuous_image by (simp add: Setcompr_eq_image)

lemmas bdd_above_cont_comp_spec = compact_imp_bdd_above[OF comp_cont_image_spec]

lemmas bdd_above_norm_cont_comp = continuous_on_norm[THEN bdd_above_cont_comp_spec]

lemma open_cballE: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>e>0. cball t\<^sub>0 e \<subseteq> T"
  using open_contains_cball by blast

lemma open_ballE: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>e>0. ball t\<^sub>0 e \<subseteq> T"
  using open_contains_ball by blast

lemma funcset_UNIV: "f \<in> A \<rightarrow> UNIV"
  by auto

lemma finite_image_of_finite[simp]:
  fixes f::"'a::finite \<Rightarrow> 'b"
  shows "finite {x. \<exists>i. x = f i}"
  using finite_Atleast_Atmost_nat by force

lemma finite_image_of_finite2:
  fixes f :: "'a::finite \<Rightarrow> 'b::finite \<Rightarrow> 'c"
  shows "finite {f x y |x y. P x y}"
proof-
  have "finite (\<Union>x. {f x y|y. P x y})"
    by simp
  moreover have "{f x y|x y. P x y} = (\<Union>x. {f x y|y. P x y})"
    by auto
  ultimately show ?thesis 
    by simp
qed


subsection \<open> Functions \<close>

lemma finite_sum_univ_singleton: "(sum g UNIV) = sum g {i::'a::finite} + sum g (UNIV - {i})"
  by (metis add.commute finite_class.finite_UNIV sum.subset_diff top_greatest)

lemma suminfI:
  fixes f :: "nat \<Rightarrow> 'a::{t2_space,comm_monoid_add}"
  shows "f sums k \<Longrightarrow> suminf f = k"
  unfolding sums_iff by simp

lemma suminf_eq_sum:
  fixes f :: "nat \<Rightarrow> ('a::real_normed_vector)"
  assumes "\<And>n. n > m \<Longrightarrow> f n = 0"
  shows "(\<Sum>n. f n) = (\<Sum>n \<le> m. f n)"
  using assms by (meson atMost_iff finite_atMost not_le suminf_finite)

lemma suminf_multr: "summable f \<Longrightarrow> (\<Sum>n. f n * c) = (\<Sum>n. f n) * c" for c::"'a::real_normed_algebra"
  by (rule bounded_linear.suminf [OF bounded_linear_mult_left, symmetric])

lemma sum_if_then_else_simps[simp]:
  fixes q :: "('a::semiring_0)" and i :: "'n::finite"
  shows "(\<Sum>j\<in>UNIV. f j * (if j = i then q else 0)) = f i * q"
    and "(\<Sum>j\<in>UNIV. f j * (if i = j then q else 0)) = f i * q"
    and "(\<Sum>j\<in>UNIV. (if i = j then q else 0) * f j) = q * f i"
    and "(\<Sum>j\<in>UNIV. (if j = i then q else 0) * f j) = q * f i"
  by (auto simp: finite_sum_univ_singleton[of _ i])


subsection \<open> Suprema \<close>

lemma le_max_image_of_finite[simp]:
  fixes f::"'a::finite \<Rightarrow> 'b::linorder"
  shows "(f i) \<le> Max {x. \<exists>i. x = f i}"
  by (rule Max.coboundedI, simp_all) (rule_tac x=i in exI, simp)

lemma cSup_eq:
  fixes c::"'a::conditionally_complete_lattice"
  assumes "\<forall>x \<in> X. x \<le> c" and "\<exists>x \<in> X. c \<le> x"
  shows "Sup X = c"
  by (metis assms cSup_eq_maximum order_class.order.antisym)

lemma cSup_mem_eq: 
  "c \<in> X \<Longrightarrow> \<forall>x \<in> X. x \<le> c \<Longrightarrow> Sup X = c" for c::"'a::conditionally_complete_lattice"
  by (rule cSup_eq, auto)

lemma cSup_finite_ex:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x\<in>X. Sup X = x" for X::"'a::conditionally_complete_linorder set"
  by (metis (full_types) bdd_finite(1) cSup_upper finite_Sup_less_iff order_less_le)

lemma cMax_finite_ex:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x\<in>X. Max X = x" for X::"'a::conditionally_complete_linorder set"
  apply(subst cSup_eq_Max[symmetric])
  using cSup_finite_ex by auto

lemma finite_nat_minimal_witness:
  fixes P :: "('a::finite) \<Rightarrow> nat \<Rightarrow> bool"
  assumes "\<forall>i. \<exists>N::nat. \<forall>n \<ge> N. P i n"
  shows "\<exists>N. \<forall>i. \<forall>n \<ge> N. P i n" 
proof-
  let "?bound i" = "(LEAST N. \<forall>n \<ge> N. P i n)"
  let ?N = "Max {?bound i |i. i \<in> UNIV}"
  {fix n::nat and i::'a 
    assume "n \<ge> ?N" 
    obtain M where "\<forall>n \<ge> M. P i n" 
      using assms by blast
    hence obs: "\<forall> m \<ge> ?bound i. P i m"
      using LeastI[of "\<lambda>N. \<forall>n \<ge> N. P i n"] by blast
    have "finite {?bound i |i. i \<in> UNIV}"
      by simp
    hence "?N \<ge> ?bound i"
      using Max_ge by blast
    hence "n \<ge> ?bound i" 
      using \<open>n \<ge> ?N\<close> by linarith
    hence "P i n" 
      using obs by blast}
  thus "\<exists>N. \<forall>i n. N \<le> n \<longrightarrow> P i n" 
    by blast
qed


subsection \<open> Real numbers \<close>

named_theorems field_power_simps "simplification rules for powers to the nth"

declare semiring_normalization_rules(18) [field_power_simps]
    and semiring_normalization_rules(26) [field_power_simps]
    and semiring_normalization_rules(27) [field_power_simps]
    and semiring_normalization_rules(28) [field_power_simps]
    and semiring_normalization_rules(29) [field_power_simps]

text \<open>WARNING: Adding @{thm semiring_normalization_rules(27)} to our tactic makes 
its combination with simp to loop infinitely in some proofs.\<close>

lemma sq_le_cancel:
  shows "(a::real) \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a^2 \<le> b * a \<Longrightarrow> a \<le> b"
  and "(a::real) \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a^2 \<le> a * b \<Longrightarrow> a \<le> b"
   apply (metis less_eq_real_def mult.commute mult_le_cancel_left semiring_normalization_rules(29))
  by (metis less_eq_real_def mult_le_cancel_left semiring_normalization_rules(29))

lemma frac_diff_eq1: "a \<noteq> b \<Longrightarrow> a / (a - b) - b / (a - b) = 1" for a::real
  by (metis (no_types, hide_lams) ab_left_minus add.commute add_left_cancel 
      diff_divide_distrib diff_minus_eq_add div_self)

lemma exp_add: "x * y - y * x = 0 \<Longrightarrow> exp (x + y) = exp x * exp y" 
  by (rule exp_add_commuting) (simp add: ac_simps)

lemmas mult_exp_exp = exp_add[symmetric]


subsection \<open> Vectors and matrices \<close>

lemma sum_axis[simp]:
  fixes q :: "('a::semiring_0)"
  shows "(\<Sum>j\<in>UNIV. f j * axis i q $ j) = f i * q"
    and "(\<Sum>j\<in>UNIV. axis i q $ j * f j) = q * f i"
  unfolding axis_def by(auto simp: vec_eq_iff)

lemma sum_scalar_nth_axis: "sum (\<lambda>i. (x $ i) *s \<e> i) UNIV = x" for x :: "('a::semiring_1)^'n"
  unfolding vec_eq_iff axis_def by simp

lemma scalar_eq_scaleR[simp]: "c *s x = c *\<^sub>R x"
  unfolding vec_eq_iff by simp

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma vec_mult_inner: "(A *v v) \<bullet> w = v \<bullet> (transpose A *v w)" for A :: "real ^'n^'n"
  unfolding matrix_vector_mult_def transpose_def inner_vec_def
  apply(simp add: sum_distrib_right sum_distrib_left)
  apply(subst sum.swap)
  apply(subgoal_tac "\<forall>i j. A $ i $ j * v $ j * w $ i = v $ j * (A $ i $ j * w $ i)")
  by presburger simp

lemma uminus_axis_eq[simp]: "- axis i k = axis i (-k)" for k :: "'a::ring"
  unfolding axis_def by(simp add: vec_eq_iff)

lemma norm_axis_eq[simp]: "\<parallel>axis i k\<parallel> = \<parallel>k\<parallel>"
proof(simp add: axis_def norm_vec_def L2_set_def)
  let "?\<delta>\<^sub>K" = "\<lambda>i j k. if i = j then k else 0" 
  have "(\<Sum>j\<in>UNIV. (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) = (\<Sum>j\<in>{i}. (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) + (\<Sum>j\<in>(UNIV-{i}). (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2)"
    using finite_sum_univ_singleton by blast 
  also have "... = (\<parallel>k\<parallel>)\<^sup>2" 
    by simp
  finally show "sqrt (\<Sum>j\<in>UNIV. (norm (if j = i then k else 0))\<^sup>2) = norm k" 
    by simp
qed

lemma matrix_axis_0: 
  fixes A :: "('a::idom)^'n^'m"
  assumes "k \<noteq> 0 " and h:"\<forall>i. (A *v (axis i k)) = 0"
  shows "A = 0"  
proof-
  {fix i::'n
    have "0 = (\<Sum>j\<in>UNIV. (axis i k) $ j *s column j A)" 
      using h matrix_mult_sum[of A "axis i k"] by simp
    also have "... = k *s column i A" 
      by (simp add: axis_def vector_scalar_mult_def column_def vec_eq_iff mult.commute)
    finally have "k *s column i A = 0"
      unfolding axis_def by simp
    hence "column i A = 0" 
      using vector_mul_eq_0 \<open>k \<noteq> 0\<close> by blast}
  thus "A = 0" 
    unfolding column_def vec_eq_iff by simp
qed

lemma scaleR_norm_sgn_eq: "(\<parallel>x\<parallel>) *\<^sub>R sgn x = x"
  by (metis divideR_right norm_eq_zero scale_eq_0_iff sgn_div_norm)

lemma vector_scaleR_commute: "A *v c *\<^sub>R x = c *\<^sub>R (A *v x)" for x :: "('a::real_normed_algebra_1)^'n"
  unfolding scaleR_vec_def matrix_vector_mult_def by(auto simp: vec_eq_iff scaleR_right.sum)

lemma scaleR_vector_assoc: "c *\<^sub>R (A *v x) = (c *\<^sub>R A) *v x" for x :: "('a::real_normed_algebra_1)^'n"
  unfolding matrix_vector_mult_def by(auto simp: vec_eq_iff scaleR_right.sum)

lemma mult_norm_matrix_sgn_eq:
  fixes x :: "('a::real_normed_algebra_1)^'n"
  shows "(\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>) = \<parallel>A *v x\<parallel>"
proof-
  have "\<parallel>A *v x\<parallel> = \<parallel>A *v ((\<parallel>x\<parallel>) *\<^sub>R sgn x)\<parallel>"
    by(simp add: scaleR_norm_sgn_eq)
  also have "... = (\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>)"
    by(simp add: vector_scaleR_commute)
  finally show ?thesis ..
qed


subsection\<open> Diagonalization \<close>

lemma invertibleI: "A ** B = mat 1 \<Longrightarrow> B ** A = mat 1 \<Longrightarrow> invertible A"
  unfolding invertible_def by auto

lemma invertibleD[simp]:
  assumes "invertible A" 
  shows "A\<^sup>-\<^sup>1 ** A = mat 1" and "A ** A\<^sup>-\<^sup>1 = mat 1"
  using assms unfolding matrix_inv_def invertible_def
  by (simp_all add: verit_sko_ex')

lemma matrix_inv_unique:
  assumes "A ** B = mat 1" and "B ** A = mat 1"
  shows "A\<^sup>-\<^sup>1 = B"
  by (metis assms invertibleD(2) invertibleI matrix_mul_assoc matrix_mul_lid)

lemma invertible_matrix_inv: "invertible A \<Longrightarrow> invertible (A\<^sup>-\<^sup>1)"
  using invertibleD invertibleI by blast

lemma matrix_inv_idempotent[simp]: "invertible A \<Longrightarrow> A\<^sup>-\<^sup>1\<^sup>-\<^sup>1 = A"
  using invertibleD matrix_inv_unique by blast
  
lemma matrix_inv_matrix_mul:
  assumes "invertible A" and "invertible B"
  shows "(A ** B)\<^sup>-\<^sup>1 = B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1"
proof(rule matrix_inv_unique)
  have "A ** B ** (B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1) = A ** (B ** B\<^sup>-\<^sup>1) ** A\<^sup>-\<^sup>1"
    by (simp add: matrix_mul_assoc)
  also have "... = mat 1"
    using assms by simp
  finally show "A ** B ** (B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1) = mat 1" .
next
  have "B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1 ** (A ** B) = B\<^sup>-\<^sup>1 ** (A\<^sup>-\<^sup>1 ** A) ** B"
    by (simp add: matrix_mul_assoc)
  also have "... = mat 1"
    using assms by simp
  finally show "B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1 ** (A ** B) = mat 1" .
qed

lemma mat_inverse_simps[simp]:
  fixes c :: "'a::division_ring"
  assumes "c \<noteq> 0"
  shows "mat (inverse c) ** mat c = mat 1" 
    and "mat c ** mat (inverse c) = mat 1"
  unfolding matrix_matrix_mult_def mat_def by (auto simp: vec_eq_iff assms)

lemma matrix_inv_mat[simp]: "c \<noteq> 0 \<Longrightarrow> (mat c)\<^sup>-\<^sup>1 = mat (inverse c)" for c :: "'a::division_ring"
  by (simp add: matrix_inv_unique)

lemma invertible_mat[simp]: "c \<noteq> 0 \<Longrightarrow> invertible (mat c)" for c :: "'a::division_ring"
  using invertibleI mat_inverse_simps(1) mat_inverse_simps(2) by blast

lemma matrix_inv_mat_1: "(mat (1::'a::division_ring))\<^sup>-\<^sup>1 = mat 1"
  by simp

lemma invertible_mat_1: "invertible (mat (1::'a::division_ring))"
  by simp

definition similar_matrix :: "('a::semiring_1)^'m^'m \<Rightarrow> ('a::semiring_1)^'n^'n \<Rightarrow> bool" (infixr "\<sim>" 25)
  where "similar_matrix A B \<longleftrightarrow> (\<exists> P. invertible P \<and> A = P\<^sup>-\<^sup>1 ** B ** P)"

lemma similar_matrix_refl[simp]: "A \<sim> A" for A :: "'a::division_ring^'n^'n"
  by (unfold similar_matrix_def, rule_tac x="mat 1" in exI, simp)

lemma similar_matrix_simm: "A \<sim> B \<Longrightarrow> B \<sim> A" for A B :: "('a::semiring_1)^'n^'n"
  apply(unfold similar_matrix_def, clarsimp)
  apply(rule_tac x="P\<^sup>-\<^sup>1" in exI, simp add: invertible_matrix_inv)
  by (metis invertible_def matrix_inv_unique matrix_mul_assoc matrix_mul_lid matrix_mul_rid)

lemma similar_matrix_trans: "A \<sim> B \<Longrightarrow> B \<sim> C \<Longrightarrow> A \<sim> C" for A B C :: "('a::semiring_1)^'n^'n"
proof(unfold similar_matrix_def, clarsimp)
  fix P Q
  assume "A = P\<^sup>-\<^sup>1 ** (Q\<^sup>-\<^sup>1 ** C ** Q) ** P" and "B = Q\<^sup>-\<^sup>1 ** C ** Q"
  let ?R = "Q ** P"
  assume inverts: "invertible Q" "invertible P"
  hence "?R\<^sup>-\<^sup>1 = P\<^sup>-\<^sup>1 ** Q\<^sup>-\<^sup>1"
    by (rule matrix_inv_matrix_mul)
  also have "invertible ?R"
    using inverts invertible_mult by blast 
  ultimately show "\<exists>R. invertible R \<and> P\<^sup>-\<^sup>1 ** (Q\<^sup>-\<^sup>1 ** C ** Q) ** P = R\<^sup>-\<^sup>1 ** C ** R"
    by (metis matrix_mul_assoc)
qed

lemma mat_vec_nth_simps[simp]:
  "i = j \<Longrightarrow> mat c $ i $ j = c" 
  "i \<noteq> j \<Longrightarrow> mat c $ i $ j = 0"
  by (simp_all add: mat_def)

definition "diag_mat f = (\<chi> i j. if i = j then f i else 0)"

lemma diag_mat_vec_nth_simps[simp]:
  "i = j \<Longrightarrow> diag_mat f $ i $ j = f i"
  "i \<noteq> j \<Longrightarrow> diag_mat f $ i $ j = 0"
  unfolding diag_mat_def by simp_all

lemma diag_mat_const_eq[simp]: "diag_mat (\<lambda>i. c) = mat c"
  unfolding mat_def diag_mat_def by simp

lemma matrix_vector_mul_diag_mat: "diag_mat f *v s = (\<chi> i. f i * s$i)"
  unfolding diag_mat_def matrix_vector_mult_def by simp

lemma matrix_vector_mul_diag_axis[simp]: "diag_mat f *v (axis i k) = axis i (f i * k)"
  by (simp add: matrix_vector_mul_diag_mat axis_def fun_eq_iff)

lemma matrix_mul_diag_matl: "diag_mat f ** A = (\<chi> i j. f i * A$i$j)"
  unfolding diag_mat_def matrix_matrix_mult_def by simp

lemma matrix_matrix_mul_diag_matr: "A ** diag_mat f = (\<chi> i j. A$i$j * f j)"
  unfolding diag_mat_def matrix_matrix_mult_def apply(clarsimp simp: fun_eq_iff)
  subgoal for i j 
    by (auto simp: finite_sum_univ_singleton[of _ j])
  done

lemma matrix_mul_diag_diag: "diag_mat f ** diag_mat g = diag_mat (\<lambda>i. f i * g i)"
  unfolding diag_mat_def matrix_matrix_mult_def vec_eq_iff by simp

lemma compow_matrix_mul_diag_mat_eq: "((**) (diag_mat f) ^^ n) (mat 1) = diag_mat (\<lambda>i. f i^n)"
  apply(induct n, simp_all add: matrix_mul_diag_matl)
  by (auto simp: vec_eq_iff diag_mat_def)

lemma compow_similar_diag_mat_eq:
  assumes "invertible P" 
      and "A = P\<^sup>-\<^sup>1 ** (diag_mat f) ** P"
    shows "((**) A ^^ n) (mat 1) = P\<^sup>-\<^sup>1 ** (diag_mat (\<lambda>i. f i^n)) ** P"
proof(induct n, simp_all add: assms)
  fix n::nat
  have "P\<^sup>-\<^sup>1 ** diag_mat f ** P ** (P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i ^ n) ** P) = 
  P\<^sup>-\<^sup>1 ** diag_mat f ** diag_mat (\<lambda>i. f i ^ n) ** P" (is "?lhs = _")
    by (metis (no_types, lifting) assms(1) invertibleD(2) matrix_mul_rid matrix_mul_assoc) 
  also have "... = P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i * f i ^ n) ** P" (is "_ = ?rhs")
    by (metis (full_types) matrix_mul_assoc matrix_mul_diag_diag)
  finally show "?lhs = ?rhs" .
qed

lemma compow_similar_diag_mat:
  assumes "A \<sim> (diag_mat f)"
  shows "((**) A ^^ n) (mat 1) \<sim> diag_mat (\<lambda>i. f i^n)"
proof(unfold similar_matrix_def)
  obtain P where "invertible P" and "A = P\<^sup>-\<^sup>1 ** (diag_mat f) ** P"
    using assms unfolding similar_matrix_def by blast
  thus "\<exists>P. invertible P \<and> ((**) A ^^ n) (mat 1) = P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i ^ n) ** P"
    using compow_similar_diag_mat_eq by blast
qed

no_notation matrix_inv ("_\<^sup>-\<^sup>1" [90])
        and similar_matrix (infixr "\<sim>" 25)


end