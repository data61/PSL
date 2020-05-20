(*  Title:       Matrix norms
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Matrix norms \<close>

text \<open> Here, we explore some properties about the operator and the maximum norms for matrices. \<close>

theory MTX_Norms
  imports MTX_Preliminaries

begin


subsection\<open> Matrix operator norm \<close>

abbreviation op_norm :: "('a::real_normed_algebra_1)^'n^'m \<Rightarrow> real" ("(1\<parallel>_\<parallel>\<^sub>o\<^sub>p)" [65] 61)
  where "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<equiv> onorm (\<lambda>x. A *v x)"

lemma norm_matrix_bound:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
proof-
  fix x :: "('a, 'n) vec" assume "\<parallel>x\<parallel> = 1"
  hence xi_le1:"\<And>i. \<parallel>x $ i\<parallel> \<le> 1" 
    by (metis Finite_Cartesian_Product.norm_nth_le) 
  {fix j::'m 
    have "\<parallel>(\<Sum>i\<in>UNIV. A $ j $ i * x $ i)\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>A $ j $ i * x $ i\<parallel>)"
      using norm_sum by blast
    also have "... \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * (\<parallel>x $ i\<parallel>))"
      by (simp add: norm_mult_ineq sum_mono)
    also have "... \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * 1)"
      using xi_le1 by (simp add: sum_mono mult_left_le)
    finally have "\<parallel>(\<Sum>i\<in>UNIV. A $ j $ i * x $ i)\<parallel> \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * 1)" by simp}
  hence "\<And>j. \<parallel>(A *v x) $ j\<parallel> \<le> ((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j"
    unfolding matrix_vector_mult_def by simp
  hence "(\<Sum>j\<in>UNIV. (\<parallel>(A *v x) $ j\<parallel>)\<^sup>2) \<le> (\<Sum>j\<in>UNIV. (\<parallel>((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j\<parallel>)\<^sup>2)"
    by (metis (mono_tags, lifting) norm_ge_zero power2_abs power_mono real_norm_def sum_mono) 
  thus "\<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
    unfolding norm_vec_def L2_set_def by simp
qed

lemma onorm_set_proptys:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "bounded (range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>)))"
    and "bdd_above (range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>)))"
    and "(range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>))) \<noteq> {}"
  unfolding bounded_def bdd_above_def image_def dist_real_def 
    apply(rule_tac x=0 in exI)
  by (rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI, clarsimp,
      subst mult_norm_matrix_sgn_eq[symmetric], clarsimp,
      rule_tac x="sgn _" in norm_matrix_bound, simp add: norm_sgn)+ force

lemma op_norm_set_proptys:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "bounded {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "bdd_above {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "{\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<noteq> {}"
  unfolding bounded_def bdd_above_def apply safe
    apply(rule_tac x=0 in exI, rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI)
    apply(force simp: norm_matrix_bound dist_real_def)
   apply(rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI, force simp: norm_matrix_bound)
  using ex_norm_eq_1 by blast

lemma op_norm_def: "\<parallel>A\<parallel>\<^sub>o\<^sub>p = Sup {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
  apply(rule antisym[OF onorm_le cSup_least[OF op_norm_set_proptys(3)]])
   apply(case_tac "x = 0", simp)
   apply(subst mult_norm_matrix_sgn_eq[symmetric], simp)
   apply(rule cSup_upper[OF _ op_norm_set_proptys(2)])
   apply(force simp: norm_sgn)
  unfolding onorm_def 
  apply(rule cSup_upper[OF _ onorm_set_proptys(2)])
  by (simp add: image_def, clarsimp) (metis div_by_1)

lemma norm_matrix_le_op_norm: "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  apply(unfold onorm_def, rule cSup_upper[OF _ onorm_set_proptys(2)])
  unfolding image_def by (clarsimp, rule_tac x=x in exI) simp

lemma op_norm_ge_0: "0 \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  using ex_norm_eq_1 norm_ge_zero norm_matrix_le_op_norm basic_trans_rules(23) by blast

lemma norm_sgn_le_op_norm: "\<parallel>A *v sgn x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  by (cases "x=0", simp_all add: norm_sgn norm_matrix_le_op_norm op_norm_ge_0)

lemma norm_matrix_le_mult_op_norm: "\<parallel>A *v x\<parallel> \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)"
proof-
  have "\<parallel>A *v x\<parallel> = (\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>)"
    by(simp add: mult_norm_matrix_sgn_eq)
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)"
    using norm_sgn_le_op_norm[of A] by (simp add: mult_mono')
  finally show ?thesis by simp
qed

lemma blin_matrix_vector_mult: "bounded_linear ((*v) A)" for A :: "('a::real_normed_algebra_1)^'n^'m"
  by (unfold_locales) (auto intro: norm_matrix_le_mult_op_norm simp: 
      mult.commute matrix_vector_right_distrib vector_scaleR_commute)

lemma op_norm_eq_0: "(\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0) = (A = 0)" for A :: "('a::real_normed_field)^'n^'m"
  unfolding onorm_eq_0[OF blin_matrix_vector_mult] using matrix_axis_0[of 1 A] by fastforce

lemma op_norm0: "\<parallel>(0::('a::real_normed_field)^'n^'m)\<parallel>\<^sub>o\<^sub>p = 0"
  using op_norm_eq_0[of 0] by simp
                  
lemma op_norm_triangle: "\<parallel>A + B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) + (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
  using onorm_triangle[OF blin_matrix_vector_mult[of A] blin_matrix_vector_mult[of B]]
    matrix_vector_mult_add_rdistrib[symmetric, of A _ B] by simp

lemma op_norm_scaleR: "\<parallel>c *\<^sub>R A\<parallel>\<^sub>o\<^sub>p = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
  unfolding onorm_scaleR[OF blin_matrix_vector_mult, symmetric] scaleR_vector_assoc ..

lemma op_norm_matrix_matrix_mult_le: "\<parallel>A ** B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
proof(rule onorm_le)
  have "0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
    by(rule onorm_pos_le[OF blin_matrix_vector_mult])
  fix x have "\<parallel>A ** B *v x\<parallel> = \<parallel>A *v (B *v x)\<parallel>"
    by (simp add: matrix_vector_mul_assoc)
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B *v x\<parallel>)"
    by (simp add: norm_matrix_le_mult_op_norm[of _ "B *v x"])
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * ((\<parallel>B\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>))"
    using norm_matrix_le_mult_op_norm[of B x] \<open>0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)\<close> mult_left_mono by blast
  finally show "\<parallel>A ** B *v x\<parallel> \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" 
    by simp
qed

lemma norm_matrix_vec_mult_le_transpose:
  "\<parallel>x\<parallel> = 1 \<Longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" for A :: "real^'n^'n"
proof-
  assume "\<parallel>x\<parallel> = 1"
  have "(\<parallel>A *v x\<parallel>)\<^sup>2 = (A *v x) \<bullet> (A *v x)"
    using dot_square_norm[of "(A *v x)"] by simp
  also have "... = x \<bullet> (transpose A *v (A *v x))"
    using vec_mult_inner by blast
  also have "... \<le> (\<parallel>x\<parallel>) * (\<parallel>transpose A *v (A *v x)\<parallel>)"
    using norm_cauchy_schwarz by blast
  also have "... \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    apply(subst matrix_vector_mul_assoc) 
    using norm_matrix_le_mult_op_norm[of "transpose A ** A" x]
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close>) 
  finally have "((\<parallel>A *v x\<parallel>))^2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    by linarith
  thus "(\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close> real_le_rsqrt)
qed

lemma op_norm_le_sum_column: "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)" for A :: "real^'n^'m"  
proof(unfold op_norm_def, rule cSup_least[OF op_norm_set_proptys(3)], clarsimp)
  fix x :: "real^'n" assume x_def:"\<parallel>x\<parallel> = 1" 
  hence x_hyp:"\<And>i. \<parallel>x $ i\<parallel> \<le> 1"
    by (simp add: norm_bound_component_le_cart)
  have "(\<parallel>A *v x\<parallel>) = \<parallel>(\<Sum>i\<in>UNIV. x $ i *s column i A)\<parallel>"
    by(subst matrix_mult_sum[of A], simp)
  also have "... \<le> (\<Sum>i\<in>UNIV. \<parallel>x $ i *s column i A\<parallel>)"
    by (simp add: sum_norm_le)
  also have "... = (\<Sum>i\<in>UNIV. (\<parallel>x $ i\<parallel>) * (\<parallel>column i A\<parallel>))"
    by (simp add: mult_norm_matrix_sgn_eq)
  also have "... \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)"
    using x_hyp by (simp add: mult_left_le_one_le sum_mono) 
  finally show "\<parallel>A *v x\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)" .
qed

lemma op_norm_le_transpose: "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> \<parallel>transpose A\<parallel>\<^sub>o\<^sub>p" for A :: "real^'n^'n"  
proof-
  have obs:"\<forall>x. \<parallel>x\<parallel> = 1 \<longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    using norm_matrix_vec_mult_le_transpose by blast
  have "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p))"
    using obs apply(unfold op_norm_def)
    by (rule cSup_least[OF op_norm_set_proptys(3)]) clarsimp
  hence "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)"
    using power_mono[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)" _ 2] op_norm_ge_0
    by (metis not_le real_less_lsqrt)
  also have "... \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
    using op_norm_matrix_matrix_mult_le by blast
  finally have "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
    by linarith
  thus "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p)"
    using sq_le_cancel[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)"] op_norm_ge_0 by metis
qed


subsection\<open> Matrix maximum norm \<close>

abbreviation max_norm :: "real^'n^'m \<Rightarrow> real" ("(1\<parallel>_\<parallel>\<^sub>m\<^sub>a\<^sub>x)" [65] 61)
  where "\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x \<equiv> Max (abs ` (entries A))"

lemma max_norm_def: "\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x = Max {\<bar>A $ i $ j\<bar>|i j. i\<in>UNIV \<and> j\<in>UNIV}"
  by (simp add: image_def, rule arg_cong[of _ _ Max], blast)

lemma max_norm_set_proptys: "finite {\<bar>A $ i $ j\<bar> |i j. i \<in> UNIV \<and> j \<in> UNIV}" (is "finite ?X")
proof-
  have "\<And>i. finite {\<bar>A $ i $ j\<bar> | j. j \<in> UNIV}"
    using finite_Atleast_Atmost_nat by fastforce
  hence "finite (\<Union>i\<in>UNIV. {\<bar>A $ i $ j\<bar> | j. j \<in> UNIV})" (is "finite ?Y")
    using finite_class.finite_UNIV by blast
  also have "?X \<subseteq> ?Y" 
    by auto
  ultimately show ?thesis 
    using finite_subset by blast
qed

lemma max_norm_ge_0: "0 \<le> \<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x"
  unfolding max_norm_def 
  apply(rule order.trans[OF abs_ge_zero[of "A $ _ $ _"] Max_ge])
  using max_norm_set_proptys by auto

lemma op_norm_le_max_norm:
  fixes A :: "real^('n::finite)^('m::finite)"
  shows "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> real CARD('m) * real CARD('n) * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
  apply(rule onorm_le_matrix_component)
  unfolding max_norm_def by(rule Max_ge[OF max_norm_set_proptys]) force

lemma sqrt_Sup_power2_eq_Sup_abs:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> sqrt (Sup {(f i)\<^sup>2 |i. i \<in> A}) = Sup {\<bar>f i\<bar> |i. i \<in> A}"
proof(rule sym)
  assume assms: "finite A" "A \<noteq> {}"
  then obtain i where i_def: "i \<in> A \<and> Sup {(f i)\<^sup>2|i. i \<in> A} = (f i)^2"
    using cSup_finite_ex[of "{(f i)\<^sup>2|i. i \<in> A}"] by auto
  hence lhs: "sqrt (Sup {(f i)\<^sup>2 |i. i \<in> A}) = \<bar>f i\<bar>"
    by simp
  have "finite {(f i)\<^sup>2|i. i \<in> A}"
    using assms by simp
  hence "\<forall>j\<in>A. (f j)\<^sup>2 \<le> (f i)\<^sup>2"
    using i_def cSup_upper[of _ "{(f i)\<^sup>2 |i. i \<in> A}"] by force
  hence "\<forall>j\<in>A. \<bar>f j\<bar> \<le> \<bar>f i\<bar>"
    using abs_le_square_iff by blast
  also have "\<bar>f i\<bar> \<in> {\<bar>f i\<bar> |i. i \<in> A}"
    using i_def by auto
  ultimately show "Sup {\<bar>f i\<bar> |i. i \<in> A} = sqrt (Sup {(f i)\<^sup>2 |i. i \<in> A})"
    using cSup_mem_eq[of "\<bar>f i\<bar>" "{\<bar>f i\<bar> |i. i \<in> A}"] lhs by auto
qed

lemma sqrt_Max_power2_eq_max_abs:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> sqrt (Max {(f i)\<^sup>2|i. i \<in> A}) = Max {\<bar>f i\<bar> |i. i \<in> A}"
  apply(subst cSup_eq_Max[symmetric], simp_all)+
  using sqrt_Sup_power2_eq_Sup_abs .

lemma op_norm_diag_mat_eq: "\<parallel>diag_mat f\<parallel>\<^sub>o\<^sub>p = Max {\<bar>f i\<bar> |i. i \<in> UNIV}" (is "_ = Max ?A")
proof(unfold op_norm_def)
  have obs: "\<And>x i. (f i)\<^sup>2 * (x $ i)\<^sup>2 \<le> Max {(f i)\<^sup>2|i. i \<in> UNIV} * (x $ i)\<^sup>2"
    apply(rule mult_right_mono[OF _ zero_le_power2])
    using le_max_image_of_finite[of "\<lambda>i. (f i)^2"] by simp
  {fix r assume "r \<in> {\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}"
    then obtain x where x_def: "\<parallel>diag_mat f *v x\<parallel> = r \<and> \<parallel>x\<parallel> = 1"
      by blast
    hence "r\<^sup>2 = (\<Sum>i\<in>UNIV. (f i)\<^sup>2 * (x $ i)\<^sup>2)"
      unfolding norm_vec_def L2_set_def matrix_vector_mul_diag_mat 
      apply (simp add: power_mult_distrib)
      by (metis (no_types, lifting) x_def norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
    also have "... \<le> (Max {(f i)\<^sup>2|i. i \<in> UNIV}) * (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
      using obs[of _ x] by (simp add: sum_mono sum_distrib_left)
    also have "... = Max {(f i)\<^sup>2|i. i \<in> UNIV}"
      using x_def by (simp add: norm_vec_def L2_set_def)
    finally have "r \<le> sqrt (Max {(f i)\<^sup>2|i. i \<in> UNIV})"
      using x_def real_le_rsqrt by blast 
    hence "r \<le> Max ?A"
      by (subst (asm) sqrt_Max_power2_eq_max_abs[of UNIV f], simp_all)}
  hence 1: "\<forall>x\<in>{\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}. x \<le> Max ?A"
    unfolding diag_mat_def by blast
  obtain i where i_def: "Max ?A = \<parallel>diag_mat f *v \<e> i\<parallel>"
    using cMax_finite_ex[of ?A] by force
  hence 2: "\<exists>x\<in>{\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}. Max ?A \<le> x"
    by (metis (mono_tags, lifting) abs_1 mem_Collect_eq norm_axis_eq order_refl real_norm_def)
  show "Sup {\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1} = Max ?A"
    by (rule cSup_eq[OF 1 2])
qed

lemma op_max_norms_eq_at_diag: "\<parallel>diag_mat f\<parallel>\<^sub>o\<^sub>p = \<parallel>diag_mat f\<parallel>\<^sub>m\<^sub>a\<^sub>x"
proof(rule antisym)
  have "{\<bar>f i\<bar> |i. i \<in> UNIV} \<subseteq> {\<bar>diag_mat f $ i $ j\<bar> |i j. i \<in> UNIV \<and> j \<in> UNIV}"
    by (smt Collect_mono diag_mat_vec_nth_simps(1))
  thus "\<parallel>diag_mat f\<parallel>\<^sub>o\<^sub>p \<le> \<parallel>diag_mat f\<parallel>\<^sub>m\<^sub>a\<^sub>x"
    unfolding op_norm_diag_mat_eq max_norm_def
    by (rule Max.subset_imp) (blast, simp only: finite_image_of_finite2)
next
  have "Sup {\<bar>diag_mat f $ i $ j\<bar> |i j. i \<in> UNIV \<and> j \<in> UNIV} \<le> Sup {\<bar>f i\<bar> |i. i \<in> UNIV}"
    apply(rule cSup_least, blast, clarify, case_tac "i = j", simp)
    by (rule cSup_upper, blast, simp_all) (rule cSup_upper2, auto)
  thus "\<parallel>diag_mat f\<parallel>\<^sub>m\<^sub>a\<^sub>x \<le> \<parallel>diag_mat f\<parallel>\<^sub>o\<^sub>p"
    unfolding op_norm_diag_mat_eq max_norm_def
    apply (subst cSup_eq_Max[symmetric], simp only: finite_image_of_finite2, blast)
    by (subst cSup_eq_Max[symmetric], simp, blast)
qed


end