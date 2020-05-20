section \<open>Grover's algorithm\<close>

theory Grover
  imports Partial_State Gates Quantum_Hoare
begin

subsection \<open>Basic definitions\<close>

locale grover_state =
  fixes n :: nat  (* number of qubits *)
    and f :: "nat \<Rightarrow> bool"  (* characteristic function, only need values in [0,N). *)
  assumes n: "n > 1"
    and dimM: "card {i. i < (2::nat) ^ n \<and> f i} > 0"
              "card {i. i < (2::nat) ^ n \<and> f i} < (2::nat) ^ n"
begin

definition N where
  "N = (2::nat) ^ n"

definition M where
  "M = card {i. i < N \<and> f i}"

lemma N_ge_0 [simp]: "0 < N" by (simp add: N_def)

lemma M_ge_0 [simp]: "0 < M" by (simp add: M_def dimM N_def)

lemma M_neq_0 [simp]: "M \<noteq> 0" by simp

lemma M_le_N [simp]: "M < N" by (simp add: M_def dimM N_def)

lemma M_not_ge_N [simp]: "\<not> M \<ge> N" using M_le_N by arith

definition \<psi> :: "complex vec" where
  "\<psi> = Matrix.vec N (\<lambda>i. 1 / sqrt N)"

lemma \<psi>_dim [simp]:
  "\<psi> \<in> carrier_vec N"
  "dim_vec \<psi> = N"
  by (simp add: \<psi>_def)+

lemma \<psi>_eval:
  "i < N \<Longrightarrow> \<psi> $ i = 1 / sqrt N"
  by (simp add: \<psi>_def)

lemma \<psi>_inner:
  "inner_prod \<psi> \<psi> = 1"
  apply (simp add: \<psi>_eval scalar_prod_def)
  by (smt of_nat_less_0_iff of_real_mult of_real_of_nat_eq real_sqrt_mult_self)
 
lemma \<psi>_norm:
  "vec_norm \<psi> = 1"
  by (simp add: \<psi>_eval vec_norm_def scalar_prod_def)

definition \<alpha> :: "complex vec" where
  "\<alpha> = Matrix.vec N (\<lambda>i. if f i then 0 else 1 / sqrt (N - M))"

lemma \<alpha>_dim [simp]:
  "\<alpha> \<in> carrier_vec N"
  "dim_vec \<alpha> = N"
  by (simp add: \<alpha>_def)+

lemma \<alpha>_eval:
  "i < N \<Longrightarrow> \<alpha> $ i = (if f i then 0 else 1 / sqrt (N - M))"
  by (simp add: \<alpha>_def)

lemma \<alpha>_inner:
  "inner_prod \<alpha> \<alpha> = 1"
  apply (simp add: scalar_prod_def \<alpha>_eval)
  apply (subst sum.mono_neutral_cong_right[of "{0..<N}" "{0..<N}-{i. i < N \<and> f i}"])
   apply auto
  apply (subgoal_tac "card ({0..<N} - {i. i < N \<and> f i}) = N - M")
  subgoal by (metis of_nat_0_le_iff of_real_of_nat_eq of_real_power power2_eq_square real_sqrt_pow2)
  unfolding N_def M_def 
  by (metis (no_types, lifting) atLeastLessThan_iff card.infinite card_Diff_subset card_atLeastLessThan diff_zero dimM(1) mem_Collect_eq neq0_conv subsetI zero_order(1))

definition \<beta> :: "complex vec" where
  "\<beta> = Matrix.vec N (\<lambda>i. if f i then 1 / sqrt M else 0)"

lemma \<beta>_dim [simp]:
  "\<beta> \<in> carrier_vec N"
  "dim_vec \<beta> = N"
  by (simp add: \<beta>_def)+

lemma \<beta>_eval:
  "i < N \<Longrightarrow> \<beta> $ i = (if f i then 1 / sqrt M else 0)"
  by (simp add: \<beta>_def)

lemma \<beta>_inner:
  "inner_prod \<beta> \<beta> = 1"  
  apply (simp add: scalar_prod_def \<beta>_eval)
  apply (subst sum.mono_neutral_cong_right[of "{0..<N}" "{i. i < N \<and> f i}"])
   apply auto
  apply (fold M_def)
  by (metis of_nat_0_le_iff of_real_of_nat_eq of_real_power power2_eq_square real_sqrt_pow2)

lemma alpha_beta_orth:
  "inner_prod \<alpha> \<beta> = 0"
  unfolding \<alpha>_def \<beta>_def by (simp add: scalar_prod_def)

lemma beta_alpha_orth:
  "inner_prod \<beta> \<alpha> = 0"
  unfolding \<alpha>_def \<beta>_def by (simp add: scalar_prod_def)

definition \<theta> :: real where
  "\<theta> = 2 * arccos (sqrt ((N - M) / N))"

lemma cos_theta_div_2:
  "cos (\<theta> / 2) = sqrt ((N - M) / N)"
proof -
  have "\<theta> / 2 = arccos (sqrt ((N - M) / N))" using \<theta>_def by simp
  then show "cos (\<theta> / 2) = sqrt ((N - M) / N)" 
    by (simp add: cos_arccos_abs)
qed

lemma sin_theta_div_2:
  "sin (\<theta> / 2) = sqrt (M / N)"
proof -
  have a: "\<theta> / 2 = arccos (sqrt ((N - M) / N))" using \<theta>_def by simp
  have N: "N > 0" using N_def by auto
  have M: "M < N" using M_def dimM N_def by auto
  then show "sin (\<theta> / 2) = sqrt (M / N)"
    unfolding a
    apply (simp add: sin_arccos_abs)
  proof -
    have eq: "real (N - M) = real N - real M" using N M 
      using M_not_ge_N nat_le_linear of_nat_diff by blast
    have "1 - real (N - M) / real N = (real N - (real N - real M)) / real N" 
      unfolding eq using N 
      by (metis diff_divide_distrib divide_self_if eq gr_implies_not0 of_nat_0_eq_iff)
    then show "1 - real (N - M) / real N = real M / real N" by auto
  qed
qed

lemma \<theta>_neq_0:
  "\<theta> \<noteq> 0"
proof -
  {
  assume "\<theta> = 0"
  then have "\<theta> / 2 = 0" by auto
  then have "sin (\<theta> / 2) = 0" by auto
  }
  note z = this
  have "sin (\<theta> / 2) = sqrt (M / N)" using sin_theta_div_2 by auto
  moreover have "M > 0" unfolding M_def N_def using dimM by auto
  ultimately have "sin (\<theta> / 2) > 0" by auto
  with z show ?thesis by auto
qed

abbreviation ccos where "ccos \<phi> \<equiv> complex_of_real (cos \<phi>)"
abbreviation csin where "csin \<phi> \<equiv> complex_of_real (sin \<phi>)"

lemma \<psi>_eq:
  "\<psi> = ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha> + csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>"
  apply (simp add: cos_theta_div_2 sin_theta_div_2)
  apply (rule eq_vecI)
  by (auto simp add: \<alpha>_def \<beta>_def \<psi>_def real_sqrt_divide)

lemma psi_inner_alpha:
  "inner_prod \<psi> \<alpha> = ccos (\<theta> / 2)"
  unfolding \<psi>_eq
proof -
  have "inner_prod (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha>) \<alpha> = ccos (\<theta> / 2)"
    apply (subst inner_prod_smult_right[of _ N])
    using \<alpha>_dim \<alpha>_inner by auto
  moreover have "inner_prod (csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>) \<alpha> = 0"
    apply (subst inner_prod_smult_right[of _ N])
    using \<alpha>_dim \<beta>_dim beta_alpha_orth by auto
  ultimately show "inner_prod (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha> + csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>) \<alpha> = ccos (\<theta> / 2)"
    apply (subst inner_prod_distrib_left[of _ N])
    using \<alpha>_dim \<beta>_dim by auto
qed

lemma psi_inner_beta:
  "inner_prod \<psi> \<beta> = csin (\<theta> / 2)"
  unfolding \<psi>_eq
proof -
  have "inner_prod (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha>) \<beta> = 0"
    apply (subst inner_prod_smult_right[of _ N])
    using \<alpha>_dim \<beta>_dim alpha_beta_orth by auto
  moreover have "inner_prod (csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>) \<beta> = csin (\<theta> / 2)"
    apply (subst inner_prod_smult_right[of _ N])
    using \<beta>_dim \<beta>_inner by auto
  ultimately show "inner_prod (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha> + csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>) \<beta> = csin (\<theta> / 2)"
    apply (subst inner_prod_distrib_left[of _ N])
    using \<alpha>_dim \<beta>_dim by auto
qed

definition alpha_l :: "nat \<Rightarrow> complex" where
  "alpha_l l = ccos ((l + 1 / 2) * \<theta>)"

lemma alpha_l_real:
  "alpha_l l \<in> Reals"
  unfolding alpha_l_def by auto

lemma cnj_alpha_l:
  "conjugate (alpha_l l) = alpha_l l"
  using alpha_l_real Reals_cnj_iff by auto

definition beta_l :: "nat \<Rightarrow> complex" where
  "beta_l l = csin ((l + 1 / 2) * \<theta>)"

lemma beta_l_real:
  "beta_l l \<in> Reals"
  unfolding beta_l_def by auto

lemma cnj_beta_l:
  "conjugate (beta_l l) = beta_l l"
  using beta_l_real Reals_cnj_iff by auto

lemma csin_ccos_squared_add:
  "ccos (a::real) * ccos a + csin a * csin a = 1"
  by (smt cos_diff cos_zero of_real_add of_real_hom.hom_one of_real_mult)

lemma alpha_l_beta_l_add_norm:
  "alpha_l l * alpha_l l + beta_l l * beta_l l = 1"
  using alpha_l_def beta_l_def csin_ccos_squared_add by auto

definition psi_l where
  "psi_l l = (alpha_l l) \<cdot>\<^sub>v \<alpha> + (beta_l l) \<cdot>\<^sub>v \<beta>"

lemma psi_l_dim:
  "psi_l l \<in> carrier_vec N"
  unfolding psi_l_def \<alpha>_def \<beta>_def by auto

lemma inner_psi_l:
  "inner_prod (psi_l l) (psi_l l) = 1"
proof -
  have eq0: "inner_prod (psi_l l) (psi_l l) 
    = inner_prod ((alpha_l l) \<cdot>\<^sub>v \<alpha>) (psi_l l) + inner_prod ((beta_l l) \<cdot>\<^sub>v \<beta>) (psi_l l)"
    unfolding psi_l_def
    apply (subst inner_prod_distrib_left)
    using \<alpha>_def \<beta>_def by auto
  have "inner_prod ((alpha_l l) \<cdot>\<^sub>v \<alpha>) (psi_l l) 
    = inner_prod ((alpha_l l) \<cdot>\<^sub>v \<alpha>) ((alpha_l l) \<cdot>\<^sub>v \<alpha>) + inner_prod ((alpha_l l) \<cdot>\<^sub>v \<alpha>) ((beta_l l) \<cdot>\<^sub>v \<beta>)"
    unfolding psi_l_def
    apply (subst inner_prod_distrib_right)
    using \<alpha>_def \<beta>_def by auto
  also have "\<dots> = (conjugate (alpha_l l)) * (alpha_l l) * inner_prod \<alpha> \<alpha> 
                + (conjugate (alpha_l l)) * (beta_l l) * inner_prod \<alpha> \<beta>"
    apply (subst (1 2) inner_prod_smult_left_right) using \<alpha>_def \<beta>_def by auto
  also have "\<dots> = conjugate (alpha_l l) * (alpha_l l) "
    by (simp add: alpha_beta_orth \<alpha>_inner)
  also have "\<dots> = (alpha_l l) * (alpha_l l)" using cnj_alpha_l by simp
  finally have eq1: "inner_prod (alpha_l l \<cdot>\<^sub>v \<alpha>) (psi_l l) = alpha_l l * alpha_l l".

  have "inner_prod ((beta_l l) \<cdot>\<^sub>v \<beta>) (psi_l l) 
    = inner_prod ((beta_l l) \<cdot>\<^sub>v \<beta>) ((alpha_l l) \<cdot>\<^sub>v \<alpha>) + inner_prod ((beta_l l) \<cdot>\<^sub>v \<beta>) ((beta_l l) \<cdot>\<^sub>v \<beta>)"
    unfolding psi_l_def
    apply (subst inner_prod_distrib_right)
    using \<alpha>_def \<beta>_def by auto
  also have "\<dots> = (conjugate (beta_l l)) * (alpha_l l) * inner_prod \<beta> \<alpha> 
                + (conjugate (beta_l l)) * (beta_l l) * inner_prod \<beta> \<beta>"
    apply (subst (1 2) inner_prod_smult_left_right) using \<alpha>_def \<beta>_def by auto
  also have "\<dots> = (conjugate (beta_l l)) * (beta_l l)"  using \<beta>_inner beta_alpha_orth by auto
  also have "\<dots> = (beta_l l) * (beta_l l)" using cnj_beta_l by auto
  finally have eq2: "inner_prod (beta_l l \<cdot>\<^sub>v \<beta>) (psi_l l) = beta_l l * beta_l l".

  show ?thesis unfolding eq0 eq1 eq2 using alpha_l_beta_l_add_norm by auto
qed

abbreviation proj :: "complex vec \<Rightarrow> complex mat" where
  "proj v \<equiv> outer_prod v v"

definition psi'_l where
  "psi'_l l = (alpha_l l) \<cdot>\<^sub>v \<alpha> - (beta_l l) \<cdot>\<^sub>v \<beta>"

lemma psi'_l_dim:
  "psi'_l l \<in> carrier_vec N"
  unfolding psi'_l_def \<alpha>_def \<beta>_def by auto

definition proj_psi'_l where
  "proj_psi'_l l = proj (psi'_l l)"

lemma proj_psi'_dim:
  "proj_psi'_l l \<in> carrier_mat N N"
  unfolding proj_psi'_l_def using psi'_l_dim by auto

lemma psi_inner_psi'_l:
  "inner_prod \<psi> (psi'_l l) = (alpha_l l * ccos (\<theta> / 2) - beta_l l * csin (\<theta> / 2))"
proof -
  have "inner_prod \<psi> (psi'_l l) = inner_prod \<psi> (alpha_l l \<cdot>\<^sub>v \<alpha>) - inner_prod \<psi> (beta_l l \<cdot>\<^sub>v \<beta>)"
    unfolding psi'_l_def apply (subst inner_prod_minus_distrib_right[of _ N]) by auto
  also have "\<dots> = alpha_l l * (inner_prod \<psi> \<alpha>) - beta_l l * (inner_prod \<psi> \<beta>)"
    using \<psi>_dim \<alpha>_dim \<beta>_dim by auto
  also have "\<dots> = alpha_l l * (ccos (\<theta> / 2)) - beta_l l * (csin (\<theta> / 2))"
    using psi_inner_alpha psi_inner_beta by auto
  finally show ?thesis by auto
qed

lemma double_ccos_square:
  "2 * ccos (a::real) * ccos a = ccos (2 * a) + 1"
proof -
  have eq: "ccos (2 * a) = ccos a * ccos a - csin a * csin a"
    using cos_add[of a a] by auto
  have "csin a * csin a = 1 - ccos a * ccos a"
    using csin_ccos_squared_add[of a]
    by (metis add_diff_cancel_left')
  then have "ccos a * ccos a - csin a * csin a = 2 * ccos a * ccos a - 1"
    by simp
  with eq show ?thesis by simp 
qed

lemma double_csin_square:
  "2 * csin (a::real) * csin a = 1 - ccos (2 * a)"
proof -
  have eq: "ccos (2 * a) = ccos a * ccos a - csin a * csin a"
    using cos_add[of a a] by auto
  have "ccos a * ccos a = 1 - csin a * csin a"
    using csin_ccos_squared_add[of a]
      cancel_comm_monoid_add_class.add_implies_diff by auto
  then have "ccos a * ccos a - csin a * csin a = 1 - 2 * csin (a::real) * csin a"
    by simp
  with eq show ?thesis by simp
qed

lemma csin_double:
  "2 * csin (a::real) * ccos a = csin(2 * a)"
  using sin_add[of a a] by simp

lemma ccos_add:
  "ccos (x + y) = ccos x * ccos y - csin x * csin y"
  using cos_add[of x y] by simp

lemma alpha_l_Suc_l_derive:
  "2 * (alpha_l l * ccos (\<theta> / 2) - beta_l l * csin (\<theta> / 2)) * ccos (\<theta> / 2) - alpha_l l = alpha_l (l + 1)"
  (is "?lhs = ?rhs")
proof -
  have "2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) * ccos (\<theta> / 2)
    = (alpha_l l) * (2 * ccos (\<theta> / 2)* ccos (\<theta> / 2)) - (beta_l l) * (2 * csin (\<theta> / 2) * ccos (\<theta> / 2))" 
    by (simp add: left_diff_distrib)

  also have "\<dots> = (alpha_l l) * (ccos (\<theta>) + 1) - (beta_l l) * csin \<theta>"
    using double_ccos_square csin_double by auto
  finally have "2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) * ccos (\<theta> / 2) 
    = (alpha_l l) * (ccos (\<theta>) + 1) - (beta_l l) * csin \<theta>".
  then have "?lhs = (alpha_l l) * ccos (\<theta>) - (beta_l l) * csin \<theta>" by (simp add: algebra_simps)
  also have "\<dots> = (alpha_l (l + 1))"
    unfolding alpha_l_def beta_l_def 
    apply (subst ccos_add[of "(real l + 1 / 2) * \<theta>" "\<theta>", symmetric])
    by (simp add: algebra_simps)
  finally show ?thesis by auto
qed

lemma csin_add:
  "csin (x + y) = ccos x * csin y + csin x * ccos y"
  using sin_add[of x y] by simp

lemma beta_l_Suc_l_derive:
  "2 * (alpha_l l * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) * csin (\<theta> / 2) + beta_l l = beta_l (l + 1)"
  (is "?lhs = ?rhs")
proof -
  have "2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) * csin (\<theta> / 2)
    = (alpha_l l) * (2 * csin (\<theta> / 2)* ccos (\<theta> / 2)) - (beta_l l) * (2 * csin (\<theta> / 2) * csin (\<theta> / 2))" 
    by (simp add: left_diff_distrib)
  also have "\<dots> = (alpha_l l) * (csin \<theta>) - (beta_l l) * (1 - ccos (\<theta>))"
    using double_csin_square csin_double by auto
  finally have "2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) * csin (\<theta> / 2)
    = (alpha_l l) * (csin \<theta>) - (beta_l l) * (1 - ccos (\<theta>))".
  then have "?lhs = (alpha_l l) * (csin \<theta>) + (beta_l l) * ccos \<theta>" by (simp add: algebra_simps)
  also have "\<dots> = (beta_l (l + 1))"
    unfolding alpha_l_def beta_l_def 
    apply (subst csin_add[of "(real l + 1 / 2) * \<theta>" "\<theta>", symmetric])
    by (simp add: algebra_simps)
  finally show ?thesis by auto
qed

lemma psi_l_Suc_l_derive:
  "2 * (alpha_l l * ccos (\<theta> / 2) - beta_l l * csin (\<theta> / 2)) \<cdot>\<^sub>v \<psi> - psi'_l l = psi_l (l + 1)"
  (is "?lhs = ?rhs")
proof -
  let ?l = "2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2))"
  have "?l \<cdot>\<^sub>v \<psi> = ?l \<cdot>\<^sub>v (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha> + csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>)" unfolding \<psi>_eq by auto
  also have "\<dots> = ?l \<cdot>\<^sub>v (ccos (\<theta> / 2) \<cdot>\<^sub>v \<alpha>) + ?l \<cdot>\<^sub>v (csin (\<theta> / 2) \<cdot>\<^sub>v \<beta>)" 
    apply (subst smult_add_distrib_vec[of _ N]) using \<alpha>_dim \<beta>_dim by auto
  also have "\<dots> = (?l * ccos (\<theta> / 2)) \<cdot>\<^sub>v \<alpha> + (?l * csin (\<theta> / 2)) \<cdot>\<^sub>v \<beta>" by auto
  finally have "?l \<cdot>\<^sub>v \<psi>  = (?l * ccos (\<theta> / 2)) \<cdot>\<^sub>v \<alpha> + (?l * csin (\<theta> / 2)) \<cdot>\<^sub>v \<beta>".
  then have "?l \<cdot>\<^sub>v \<psi> - (psi'_l l) = ((?l * ccos (\<theta> / 2)) \<cdot>\<^sub>v \<alpha> - (alpha_l l) \<cdot>\<^sub>v \<alpha>) + ((?l * csin (\<theta> / 2)) \<cdot>\<^sub>v \<beta> + (beta_l l) \<cdot>\<^sub>v \<beta>)"
    unfolding psi'_l_def by auto
  also have "\<dots> = (?l * ccos (\<theta> / 2) - alpha_l l) \<cdot>\<^sub>v \<alpha> + (?l * csin (\<theta> / 2) + beta_l l) \<cdot>\<^sub>v \<beta>"
    apply (subst minus_smult_vec_distrib) apply (subst add_smult_distrib_vec) by auto
  also have "\<dots> = (alpha_l (l + 1)) \<cdot>\<^sub>v \<alpha> + (beta_l (l + 1)) \<cdot>\<^sub>v \<beta>"
    using alpha_l_Suc_l_derive beta_l_Suc_l_derive by auto
  finally have "?l \<cdot>\<^sub>v \<psi> - (psi'_l l) = (alpha_l (l + 1)) \<cdot>\<^sub>v \<alpha> + (beta_l (l + 1)) \<cdot>\<^sub>v \<beta>".
  then show ?thesis unfolding psi_l_def by auto
qed

subsection \<open>Grover operator\<close>

text \<open>Oracle O\<close>

definition proj_O :: "complex mat" where
  "proj_O = mat N N (\<lambda>(i, j). if i = j then (if f i then 1 else 0) else 0)"

lemma proj_O_dim:
  "proj_O \<in> carrier_mat N N"
  unfolding proj_O_def by auto

lemma proj_O_mult_alpha:
  "proj_O *\<^sub>v \<alpha> = zero_vec N"
  by (auto simp add: proj_O_def \<alpha>_def scalar_prod_def)

lemma proj_O_mult_beta:
  "proj_O *\<^sub>v \<beta> = \<beta>"
  by (auto simp add: proj_O_def \<beta>_def scalar_prod_def sum_only_one_neq_0)

definition mat_O :: "complex mat" where
  "mat_O = mat N N (\<lambda>(i,j). if i = j then (if f i then -1 else 1) else 0)"

lemma mat_O_dim:
  "mat_O \<in> carrier_mat N N"
  unfolding mat_O_def by auto

lemma mat_O_mult_alpha:
  "mat_O *\<^sub>v \<alpha> = \<alpha>"
  by (auto simp add: mat_O_def \<alpha>_def scalar_prod_def sum_only_one_neq_0)

lemma mat_O_mult_beta:
  "mat_O *\<^sub>v \<beta> = - \<beta>"
  by (auto simp add: mat_O_def \<beta>_def scalar_prod_def sum_only_one_neq_0)

lemma hermitian_mat_O:
  "hermitian mat_O"
  by (auto simp add: hermitian_def mat_O_def adjoint_eval)

lemma unitary_mat_O:
  "unitary mat_O"
proof -
  have "mat_O \<in> carrier_mat N N" unfolding mat_O_def by auto
  moreover have "mat_O * adjoint mat_O = mat_O * mat_O" using hermitian_mat_O unfolding hermitian_def by auto
  moreover have "mat_O * mat_O = 1\<^sub>m N"
    apply (rule eq_matI)
    unfolding mat_O_def
      apply (simp add: scalar_prod_def)
    subgoal for i j apply (rule)
      subgoal apply (subst sum_only_one_neq_0[of "{0..<N}" "j"]) by auto
        apply (subst sum_only_one_neq_0[of "{0..<N}" "j"]) by auto
    by auto
  ultimately show ?thesis unfolding unitary_def inverts_mat_def by auto
qed

definition mat_Ph :: "complex mat" where
  "mat_Ph = mat N N (\<lambda>(i,j). if i = j then if i = 0 then 1 else -1 else 0)"

lemma hermitian_mat_Ph:
  "hermitian mat_Ph"
  unfolding hermitian_def mat_Ph_def
  apply (rule eq_matI)
  by (auto simp add: adjoint_eval)

lemma unitary_mat_Ph:
  "unitary mat_Ph"
proof -
  have "mat_Ph \<in> carrier_mat N N" unfolding mat_Ph_def by auto
  moreover have "mat_Ph * adjoint mat_Ph = mat_Ph * mat_Ph" using hermitian_mat_Ph unfolding hermitian_def by auto
  moreover have "mat_Ph * mat_Ph = 1\<^sub>m N"
    apply (rule eq_matI)
    unfolding mat_Ph_def
      apply (simp add: scalar_prod_def)
    subgoal for i j apply (rule)
      subgoal apply (subst sum_only_one_neq_0[of "{0..<N}" "0"]) by auto
        apply (subst sum_only_one_neq_0[of "{0..<N}" "j"]) by auto
    by auto
  ultimately show ?thesis unfolding unitary_def inverts_mat_def by auto
qed

definition mat_G' :: "complex mat" where
  "mat_G' = mat N N (\<lambda>(i,j). if i = j then 2 / N - 1 else 2 / N)"

text \<open>Geometrically, the Grover operator G is a rotation\<close>
definition mat_G :: "complex mat" where
  "mat_G = mat_G' * mat_O"

end

subsection \<open>State of Grover's algorithm\<close>

text \<open>The dimensions are [2, 2, ..., 2, n]. We work with a very special
  case as in the paper\<close>
locale grover_state_sig = grover_state + state_sig +
  fixes R :: nat
  fixes K :: nat
  assumes dims_def: "dims = replicate n 2 @ [K]"
  assumes R: "R = pi / (2 * \<theta>) - 1 / 2"
  assumes K: "K > R"

begin

lemma K_gt_0:
  "K > 0"
  using K by auto

text \<open>Bits q0 to q\_(n-1)\<close>
definition vars1 :: "nat set" where
  "vars1 = {0 ..< n}"

text \<open>Bit r\<close>
definition vars2 :: "nat set" where
  "vars2 = {n}"

lemma length_dims:
  "length dims = n + 1"
  unfolding dims_def by auto

lemma dims_nth_lt_n:
  "l < n \<Longrightarrow> nth dims l = 2" 
  unfolding dims_def by (simp add: nth_append)

lemma nths_Suc_n_dims:
  "nths dims {0..<(Suc n)} = dims" 
  using length_dims nths_upt_eq_take
  by (metis add_Suc_right add_Suc_shift lessThan_atLeast0 less_add_eq_less less_numeral_extra(4)
            not_less plus_1_eq_Suc take_all)

interpretation ps2_P: partial_state2 dims vars1 vars2
   apply unfold_locales unfolding vars1_def vars2_def by auto

interpretation ps_P: partial_state ps2_P.dims0 ps2_P.vars1'.

abbreviation tensor_P where
"tensor_P A B \<equiv> ps2_P.ptensor_mat A B"

lemma tensor_P_dim:
  "tensor_P A B \<in> carrier_mat d d"
proof -
  have "ps2_P.d0 = prod_list (nths dims ({0..<n} \<union> {n}))" unfolding ps2_P.d0_def ps2_P.dims0_def ps2_P.vars0_def 
    by (simp add: vars1_def vars2_def)
  also have "\<dots> = prod_list (nths dims ({0..<Suc n}))"
    apply (subgoal_tac "{0..<n} \<union> {n} = {0..<(Suc n)}") by auto
  also have "\<dots> = prod_list dims" using nths_Suc_n_dims by auto
  also have "\<dots> = d" unfolding d_def by auto
  finally show ?thesis  using ps2_P.ptensor_mat_carrier by auto
qed

lemma dims_nths_le_n:
  assumes "l \<le> n"
  shows "nths dims {0..<l} = replicate l 2"
proof (rule nth_equalityI, auto)
  have "l \<le> n \<Longrightarrow> (i < Suc n \<and> i < l) = (i < l)" for i
    using less_trans by fastforce
  then show l: "length (nths dims {0..<l}) = l" using assms
    by (auto simp add: length_nths length_dims)

  have llt: "l < length dims" using length_dims assms by auto
  have v1: "\<And>i. i < l \<Longrightarrow> {a. a < i \<and> a \<in> {0..<l}} = {0..<i}" unfolding vars1_def by auto
  then have "\<And>i. i < l \<Longrightarrow> card {j. j < i \<and> j \<in> {0..<l}} = i" by auto 
  then have "nths dims {0..<l} ! i = dims ! i" if "i < l" for i
    using nth_nths_card[of i dims "{0..<l}"] that llt by auto
  moreover have "dims ! i = replicate n 2 ! i" if "i < n" for i unfolding dims_def 
    by (auto simp add: nth_append that)
  moreover have "replicate n 2 ! i = replicate l 2 ! i" if "i < l" for i using assms that by auto
  ultimately show "nths dims {0..<l} ! i = replicate l 2 ! i" if "i < length (nths dims {0..<l})" for i
    using l that assms by auto 
qed

lemma dims_nths_one_lt_n: 
  assumes "l < n"
  shows "nths dims {l} = [2]"
proof -
  have "{i. i < length dims \<and> i \<in> {l}} = {l}" using assms length_dims by auto
  then have "nths dims {l} = [dims ! l]" using nths_only_one[of dims "{l}" l] by auto
  moreover have "dims ! l = 2" unfolding dims_def using assms by (simp add: nth_append)
  ultimately show ?thesis by auto
qed

lemma dims_vars1:
  "nths dims vars1 = replicate n 2"
proof (rule nth_equalityI, auto)
  show l: "length (nths dims vars1) = n"
    apply (auto simp add: length_nths vars1_def length_dims)
    by (metis (no_types, lifting) Collect_cong Suc_lessD card_Collect_less_nat not_less_eq)

  have v1: "\<And>i. i < n \<Longrightarrow> {a. a < i \<and> a \<in> vars1} = {0..<i}" unfolding vars1_def by auto
  then have "\<And>i. i < n \<Longrightarrow> card {j. j < i \<and> j \<in> vars1} = i" by auto 
  then have "nths dims vars1 ! i = dims ! i" if "i < n" for i
    using nth_nths_card[of i dims vars1] that length_dims vars1_def by auto
  moreover have "dims ! i = replicate n 2 ! i" if "i < n" for i unfolding dims_def 
    by (simp add: nth_append that)
  ultimately show "nths dims vars1 ! i = replicate n 2 ! i" if "i < length (nths dims vars1)" for i
    using l that by auto 
qed

lemma nths_rep_2_n:
  "nths (replicate n 2) {n} = []"
  by (metis (no_types, lifting) Collect_empty_eq card_empty length_0_conv length_replicate less_Suc_eq not_less_eq nths_replicate singletonD)

lemma dims_vars2:
  "nths dims vars2 = [K]"
  unfolding dims_def vars2_def
  apply (subst nths_append)
  apply (subst nths_rep_2_n)
  by simp

lemma d_vars1:
  "prod_list (nths dims vars1) = N"
proof -
  have eq: "{0..<n} = {..<n}"  by auto
  have "nths (replicate n 2 @ [K]) {0..<n} = (replicate n 2)"
    apply (subst eq)
    using nths_upt_eq_take by simp
  then show ?thesis unfolding dims_def vars1_def N_def by auto
qed

lemma ps2_P_dims0:
  "ps2_P.dims0 = dims"
proof -
  have "vars1 \<union> vars2 = {0..<Suc n}" unfolding vars1_def vars2_def by auto
  then have dims: "nths dims (vars1 \<union> vars2) = dims" unfolding vars1_def vars2_def using nths_Suc_n_dims by auto
  then show ?thesis unfolding ps2_P.dims0_def ps2_P.vars0_def apply (subst dims) by auto
qed

lemma ps2_P_vars1':
  "ps2_P.vars1' = vars1"
  unfolding ps2_P.vars1'_def ps2_P.vars0_def  
proof -
  have eq: "vars1 \<union> vars2 = {0..<(Suc n)}" unfolding vars1_def vars2_def by auto
  have "x < Suc n \<Longrightarrow> {i \<in> {0..<Suc n}. i < x} = {i. i < x}" for x by auto
  then have "x < Suc n \<Longrightarrow> ind_in_set {0..<(Suc n)} x = x" for x unfolding ind_in_set_def by auto
  then have "x \<in> vars1 \<Longrightarrow> ind_in_set {0..<(Suc n)} x = x" for x unfolding vars1_def by auto
  then have "ind_in_set {0..<(Suc n)} ` vars1 = vars1" by force
  with eq show "ind_in_set (vars1 \<union> vars2) ` vars1 = vars1" by auto
qed

lemma ps2_P_d0:
  "ps2_P.d0 = d"
  unfolding ps2_P.d0_def using ps2_P_dims0 d_def by auto

lemma ps2_P_d1:
  "ps2_P.d1 = N"
  unfolding ps2_P.d1_def ps2_P.dims1_def by (simp add: dims_vars1 N_def)

lemma ps2_P_d2:
  "ps2_P.d2 = K"
  unfolding ps2_P.d2_def ps2_P.dims2_def by (simp add: dims_vars2)

lemma ps_P_d:
  "ps_P.d = d"
  unfolding ps_P.d_def ps2_P_dims0 by auto

lemma ps_P_d1:
  "ps_P.d1 = N"
  unfolding ps_P.d1_def ps_P.dims1_def ps2_P.nths_vars1' using ps2_P_d1 unfolding ps2_P.d1_def by auto

lemma ps_P_d2:
  "ps_P.d2 = K"
  unfolding ps_P.d2_def ps_P.dims2_def ps2_P.nths_vars2' using ps2_P_d2 unfolding ps2_P.d2_def by auto

lemma nths_uminus_vars1:
  "nths dims (- vars1) = nths dims vars2"
  using ps2_P.nths_vars2' unfolding ps2_P_dims0 ps2_P_vars1' ps2_P.dims2_def by auto

lemma tensor_P_mult:
  assumes "m1 \<in> carrier_mat (2^n) (2^n)"
    and "m2 \<in> carrier_mat (2^n) (2^n)"
    and "m3 \<in> carrier_mat K K"
    and "m4 \<in> carrier_mat K K"
  shows "(tensor_P m1 m3) * (tensor_P m2 m4) = tensor_P (m1 * m2) (m3 * m4)"
proof -
  have eq:"{0..<n} = {..<n}" by auto
  have "(nths dims vars1) = replicate n 2"
    unfolding dims_def vars1_def apply (subst eq)
    by (simp add: nths_upt_eq_take[of "(replicate n 2 @ [K])" n]) 

  have "ps2_P.d1 = 2^n" unfolding ps2_P.d1_def ps2_P.dims1_def using d_vars1 N_def by auto
  moreover have "ps2_P.d2 = K" unfolding ps2_P.d2_def ps2_P.dims2_def using dims_vars2 by auto

  ultimately show ?thesis apply (subst ps2_P.ptensor_mat_mult) using assms by auto
qed

lemma mat_ext_vars1:
  shows "mat_extension dims vars1 A = tensor_P A (1\<^sub>m K)"
  unfolding Utrans_P_def ps2_P.ptensor_mat_def partial_state.mat_extension_def
    partial_state.d2_def partial_state.dims2_def ps2_P.nths_vars2'[simplified ps2_P_dims0 ps2_P_vars1'] 
  using ps2_P_d2 unfolding ps2_P.d2_def using ps2_P_dims0 ps2_P_vars1' by auto

lemma Utrans_P_is_tensor_P1:
  "Utrans_P vars1 A = Utrans (tensor_P A (1\<^sub>m K))"
  unfolding Utrans_P_def ps2_P.ptensor_mat_def partial_state.mat_extension_def
    partial_state.d2_def partial_state.dims2_def ps2_P.nths_vars2'[simplified ps2_P_dims0 ps2_P_vars1'] 
  using ps2_P_d2 unfolding ps2_P.d2_def using ps2_P_dims0 ps2_P_vars1' by auto

lemma nths_dims_uminus_vars2:
  "nths dims (-vars2) = nths dims vars1"
proof -
  have "nths dims (-vars2) = nths dims ({0..<length dims} - vars2)"
    using nths_minus_eq by auto
  also have "\<dots> = nths dims vars1" unfolding vars1_def vars2_def length_dims
    apply (subgoal_tac "{0..<n + 1} - {n} = {0..<n}") by auto
  finally show ?thesis by auto
qed

lemma mat_ext_vars2:
  assumes "A \<in> carrier_mat K K"
  shows "mat_extension dims vars2 A = tensor_P (1\<^sub>m N) A"
proof -
  have "mat_extension dims vars2 A = tensor_mat dims vars2 A (1\<^sub>m N)"
    unfolding Utrans_P_def partial_state.mat_extension_def
      partial_state.d2_def partial_state.dims2_def
      nths_dims_uminus_vars2 dims_vars1 N_def by auto
  also have "\<dots> = tensor_mat dims vars1 (1\<^sub>m N) A" 
    apply (subst tensor_mat_comm[of vars1 vars2])
    subgoal unfolding vars1_def vars2_def by auto
    subgoal unfolding length_dims vars1_def vars2_def by auto
    subgoal unfolding dims_vars1 N_def by auto
    unfolding dims_vars2 using assms by auto
  finally show "mat_extension dims vars2 A = tensor_P (1\<^sub>m N) A"
    unfolding ps2_P.ptensor_mat_def ps2_P_dims0 ps2_P_vars1' by auto
qed

lemma Utrans_P_is_tensor_P2:
  assumes "A \<in> carrier_mat K K"
  shows "Utrans_P vars2 A = Utrans (tensor_P (1\<^sub>m N) A)"
  unfolding Utrans_P_def using mat_ext_vars2 assms by auto


subsection \<open>Grover's algorithm\<close>

text \<open>Apply hadamard operator to first n variables\<close>
definition hadamard_on_i :: "nat \<Rightarrow> complex mat" where
  "hadamard_on_i i = pmat_extension dims {i} (vars1 - {i}) hadamard"
declare hadamard_on_i_def [simp]

fun hadamard_n :: "nat \<Rightarrow> com" where
  "hadamard_n 0 = SKIP"
| "hadamard_n (Suc i) = hadamard_n i ;; Utrans (tensor_P (hadamard_on_i i) (1\<^sub>m K))"

text \<open>Body of the loop\<close>
definition D :: com where
  "D = Utrans_P vars1 mat_O ;;
       hadamard_n n ;;
       Utrans_P vars1 mat_Ph ;;
       hadamard_n n ;;
       Utrans_P vars2 (mat_incr K)"

lemma unitary_ex_mat_O:
  "unitary (tensor_P mat_O (1\<^sub>m K))"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_unitary)
  subgoal using ps_P_d1 mat_O_def by auto
  subgoal using ps_P_d2 by auto
  subgoal using unitary_mat_O by auto
  using unitary_one by auto

lemma unitary_ex_mat_Ph:
  "unitary (tensor_P mat_Ph (1\<^sub>m K))"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_unitary)
  subgoal using ps_P_d1 mat_Ph_def by auto
  subgoal using ps_P_d2 by auto
  subgoal using unitary_mat_Ph by auto
  using unitary_one by auto

lemma unitary_hadamard_on_i:
  assumes "k < n"
  shows "unitary (hadamard_on_i k)"
proof -
  interpret st2: partial_state2 dims "{k}" "vars1 - {k}"
    apply unfold_locales by auto
  show ?thesis unfolding hadamard_on_i_def st2.pmat_extension_def st2.ptensor_mat_def
    apply (rule partial_state.tensor_mat_unitary)
    subgoal unfolding partial_state.d1_def partial_state.dims1_def st2.nths_vars1' st2.dims1_def
      using dims_nths_one_lt_n assms hadamard_dim by auto
    subgoal unfolding st2.d2_def st2.dims2_def partial_state.d2_def partial_state.dims2_def st2.nths_vars2' st2.dims1_def
      by auto
    subgoal using unitary_hadamard by auto
    subgoal using unitary_one by auto
    done
qed

lemma unitary_exhadamard_on_i:
  assumes "k < n"
  shows "unitary (tensor_P (hadamard_on_i k) (1\<^sub>m K))"
proof -
  interpret st2: partial_state2 dims "{k}" "vars1 - {k}"
    apply unfold_locales by auto
  have d1: "st2.d0 = partial_state.d1 ps2_P.dims0 ps2_P.vars1'"
    unfolding partial_state.d1_def partial_state.dims1_def ps2_P.nths_vars1' ps2_P.dims1_def
      st2.d0_def st2.dims0_def st2.vars0_def using assms
    apply (subgoal_tac "{k} \<union> (vars1 - {k}) = vars1") apply simp
    unfolding vars1_def by auto
  show ?thesis
  unfolding ps2_P.ptensor_mat_def
  apply (rule partial_state.tensor_mat_unitary)
  subgoal unfolding hadamard_on_i_def st2.pmat_extension_def 
    using st2.ptensor_mat_carrier[of hadamard "1\<^sub>m st2.d2"]
    using d1 by auto
  subgoal unfolding partial_state.d2_def partial_state.dims2_def ps2_P.nths_vars2' ps2_P.dims2_def dims_vars2 by auto
  using unitary_hadamard_on_i unitary_one assms by auto
qed

lemma hadamard_on_i_dim:
  assumes "k < n"
  shows "hadamard_on_i k \<in> carrier_mat N N"
proof -
  interpret st: partial_state2 dims "{k}" "(vars1 - {k})"
    apply unfold_locales by auto
  have vars1: "{k} \<union> (vars1 - {k}) = vars1" unfolding vars1_def using assms by auto
  show ?thesis unfolding hadamard_on_i_def N_def using st.pmat_extension_carrier unfolding st.d0_def st.dims0_def st.vars0_def
    using vars1 dims_vars1 by auto
qed

lemma well_com_hadamard_k:
  "k \<le> n \<Longrightarrow> well_com (hadamard_n k)"
proof (induct k)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have "well_com (hadamard_n n)" by auto
  then show ?case unfolding hadamard_n.simps well_com.simps using tensor_P_dim unitary_exhadamard_on_i Suc by auto
qed

lemma well_com_hadamard_n:
  "well_com (hadamard_n n)"
  using well_com_hadamard_k by auto

lemma well_com_mat_O:
  "well_com (Utrans_P vars1 mat_O)"
  apply (subst Utrans_P_is_tensor_P1)
  apply simp using tensor_P_dim unitary_ex_mat_O by auto

lemma well_com_mat_Ph:
  "well_com (Utrans_P vars1 mat_Ph)"
  apply (subst Utrans_P_is_tensor_P1)
  apply simp using tensor_P_dim unitary_ex_mat_Ph by auto

lemma unitary_exmat_incr:
  "unitary (tensor_P (1\<^sub>m N) (mat_incr K))"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_unitary)
  using  unitary_mat_incr K unitary_one by (auto simp add: ps_P_d1 ps_P_d2 mat_incr_def)

lemma well_com_mat_incr:
  "well_com (Utrans_P vars2 (mat_incr K))"
  apply (subst Utrans_P_is_tensor_P2)
  apply (simp add: mat_incr_def) using tensor_P_dim unitary_exmat_incr by auto

lemma well_com_D: "well_com D"
  unfolding D_def apply auto
  using well_com_hadamard_n well_com_mat_incr well_com_mat_O well_com_mat_Ph 
  by auto

text \<open>Test at while loop\<close>

definition M0 :: "complex mat" where
  "M0 = mat K K (\<lambda>(i,j). if i = j \<and> i \<ge> R then 1 else 0)"

lemma hermitian_M0:
  "hermitian M0"
  by (auto simp add: hermitian_def M0_def adjoint_eval)

lemma M0_dim:
  "M0 \<in> carrier_mat K K"
  unfolding M0_def by auto

lemma M0_mult_M0:
  "M0 * M0 = M0"
  by (auto simp add: M0_def scalar_prod_def sum_only_one_neq_0)

definition M1 :: "complex mat" where
  "M1 = mat K K (\<lambda>(i,j). if i = j \<and> i < R then 1 else 0)"

lemma M1_dim:
  "M1 \<in> carrier_mat K K"
  unfolding M1_def by auto

lemma hermitian_M1:
  "hermitian M1"
  by (auto simp add: hermitian_def M1_def adjoint_eval)

lemma M1_mult_M1:
  "M1 * M1 = M1"
  by (auto simp add: M1_def scalar_prod_def sum_only_one_neq_0)

lemma M1_add_M0:
  "M1 + M0 = 1\<^sub>m K"
  unfolding M0_def M1_def by auto

text \<open>Test at the end\<close>

definition testN :: "nat \<Rightarrow> complex mat" where
  "testN k = mat N N (\<lambda>(i,j). if i = k \<and> j = k then 1 else 0)"

lemma hermitian_testN:
  "hermitian (testN k)"
  unfolding hermitian_def testN_def
  by (auto simp add: scalar_prod_def adjoint_eval)

lemma testN_mult_testN:
  "testN k * testN k = testN k"
  unfolding testN_def
  by (auto simp add: scalar_prod_def sum_only_one_neq_0)

lemma testN_dim:
  "testN k \<in> carrier_mat N N"
  unfolding testN_def by auto

definition test_fst_k :: "nat \<Rightarrow> complex mat" where
  "test_fst_k k = mat N N (\<lambda>(i, j). if (i = j \<and> i < k) then 1 else 0)"

lemma sum_test_k:
  assumes "m \<le> N"
  shows "matrix_sum N (\<lambda>k. testN k) m = test_fst_k m"
proof -
  have "m \<le> N \<Longrightarrow> matrix_sum N (\<lambda>k. testN k) m = mat N N (\<lambda>(i, j). if (i = j \<and> i < m) then 1 else 0)" for m
  proof (induct m)
    case 0
    then show ?case apply simp apply (rule eq_matI) by auto
  next
    case (Suc m)
    then have m: "m < N" by auto
    then have m': "m \<le> N" by auto
    have "matrix_sum N testN (Suc m) = testN m + matrix_sum N testN m" by simp
    also have "\<dots> = mat N N (\<lambda>(i, j). if (i = j \<and> i < (Suc m)) then 1 else 0)"
      unfolding testN_def Suc(1)[OF m'] apply (rule eq_matI) by auto
    finally show ?case by auto
  qed
  then show ?thesis unfolding test_fst_k_def using assms by auto
qed

lemma test_fst_kN:
  "test_fst_k N = 1\<^sub>m N"
  apply (rule eq_matI)
  unfolding test_fst_k_def by auto

lemma matrix_sum_tensor_P1:
  "(\<And>k. k < m \<Longrightarrow> g k \<in> carrier_mat N N) \<Longrightarrow> (A \<in> carrier_mat K K) \<Longrightarrow>
   matrix_sum d (\<lambda>k. tensor_P (g k) A) m = tensor_P (matrix_sum N g m) A"
proof (induct m)
  case 0
  show ?case apply (simp) unfolding ps2_P.ptensor_mat_def 
    using ps_P.tensor_mat_zero1[simplified ps_P_d ps_P_d1, of A] by auto
next
  case (Suc m)
  then have ind: "matrix_sum d (\<lambda>k. tensor_P (g k) A) m = tensor_P (matrix_sum N g m) A" 
    and dk: "\<And>k. k < m \<Longrightarrow> g k \<in> carrier_mat N N" and "A \<in> carrier_mat K K" by auto
  have ds: "matrix_sum N g m \<in> carrier_mat N N" apply (subst matrix_sum_dim)
    using dk by auto
  show ?case apply simp
    apply (subst ind)
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_add1)
    unfolding ps_P_d1 ps_P_d2 using Suc ds by auto
qed

text \<open>Grover's algorithm. Assume we start in the zero state\<close>
definition Grover :: com where
  "Grover = hadamard_n n ;;
            While_P vars2 M0 M1 D ;;
            Measure_P vars1 N testN (replicate N SKIP)"

lemma well_com_if:
  "well_com (Measure_P vars1 N testN (replicate N SKIP))"
  unfolding Measure_P_def apply auto
proof -
  have eq0: "\<And>n. mat_extension dims vars1 (testN n) = tensor_P (testN n) (1\<^sub>m K)"
    unfolding mat_ext_vars1 by auto 
  have eq1: "adjoint (tensor_P (testN j) (1\<^sub>m K)) * tensor_P (testN j) (1\<^sub>m K) = tensor_P (testN j) (1\<^sub>m K)" for j
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_adjoint)
      apply (auto simp add: ps_P_d1 ps_P_d2 testN_dim hermitian_testN[unfolded hermitian_def] hermitian_one[unfolded hermitian_def])
    apply (subst ps_P.tensor_mat_mult[symmetric])
    by (auto simp add: ps_P_d1 ps_P_d2 testN_dim testN_mult_testN)
  have "measurement d N (\<lambda>n. tensor_P (testN n) (1\<^sub>m K))"
    unfolding measurement_def
    apply (simp add: tensor_P_dim)
    apply (subst eq1)
    apply (subst matrix_sum_tensor_P1)
      apply (auto simp add: testN_dim)
    apply (subst sum_test_k, simp)
    apply (subst test_fst_kN)
    unfolding ps2_P.ptensor_mat_def
    using ps_P.tensor_mat_id ps_P_d ps_P_d1 ps_P_d2 by auto
  then show "measurement d N (\<lambda>n. mat_extension dims vars1 (testN n))" using eq0 by auto

  show "list_all well_com (replicate N SKIP)" 
    apply (subst list_all_length) by simp
qed

lemma well_com_while:
  "well_com (While_P vars2 M0 M1 D)"
  unfolding While_P_def apply auto
   apply (subst (1 2) mat_ext_vars2)
  apply (auto simp add: M1_dim M0_dim)
proof -
  have 2: "2 = Suc (Suc 0)" by auto
  have ad0: "adjoint (tensor_P (1\<^sub>m N) M0) = (tensor_P (1\<^sub>m N) M0)"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_adjoint)
    unfolding ps_P_d1 ps_P_d2 by (auto simp add: M0_dim adjoint_one hermitian_M0[unfolded hermitian_def])
  have ad1: "adjoint (tensor_P (1\<^sub>m N) M1) = (tensor_P (1\<^sub>m N) M1)"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_adjoint)
    unfolding ps_P_d1 ps_P_d2 by (auto simp add: M1_dim adjoint_one hermitian_M1[unfolded hermitian_def])
  have m0: "tensor_P (1\<^sub>m N) M0 * tensor_P (1\<^sub>m N) M0 = tensor_P (1\<^sub>m N) M0"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_mult[symmetric])
    unfolding ps_P_d1 ps_P_d2 using M0_dim M0_mult_M0 by auto
  have m1: "tensor_P (1\<^sub>m N) M1 * tensor_P (1\<^sub>m N) M1 = tensor_P (1\<^sub>m N) M1"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_mult[symmetric])
    unfolding ps_P_d1 ps_P_d2 using M1_dim M1_mult_M1 by auto
  have s: "tensor_P (1\<^sub>m N) M1 + tensor_P (1\<^sub>m N) M0 = 1\<^sub>m d"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_add2[symmetric])
    unfolding ps_P_d1 ps_P_d2 
    by (auto simp add: M1_dim M0_dim M1_add_M0 ps_P.tensor_mat_id[simplified ps_P_d1 ps_P_d2 ps_P_d])
  show "measurement d 2 (\<lambda>n. if n = 0 then tensor_P (1\<^sub>m N) M0 else if n = 1 then tensor_P (1\<^sub>m N) M1 else undefined)"
    unfolding measurement_def apply (auto simp add: tensor_P_dim) apply (subst 2)
    apply (simp add: ad0 ad1 m0 m1)
    apply (subst assoc_add_mat[symmetric, of _ d d]) using tensor_P_dim s by auto
  show "well_com D" using well_com_D by auto
qed

lemma well_com_Grover:
  "well_com Grover"
  unfolding Grover_def apply auto
  using well_com_hadamard_n well_com_if well_com_while by auto

subsection \<open>Correctness\<close>

text \<open>Pre-condition: assume in the zero state\<close>

definition ket_pre :: "complex vec" where
  "ket_pre = Matrix.vec N (\<lambda>k. if k = 0 then 1 else 0)"

lemma ket_pre_dim:
  "ket_pre \<in> carrier_vec N" using ket_pre_def by auto

definition pre :: "complex mat" where
  "pre = proj ket_pre"

lemma pre_dim:
  "pre \<in> carrier_mat N N"
  using pre_def ket_pre_def by auto

lemma norm_pre:
  "inner_prod ket_pre ket_pre = 1"
  unfolding ket_pre_def scalar_prod_def
  using sum_only_one_neq_0[of "{0..<N}" 0 "\<lambda>i. (if i = 0 then 1 else 0) * cnj (if i = 0 then 1 else 0)"] by auto

lemma pre_trace:
  "trace pre = 1"
  unfolding pre_def
  apply (subst trace_outer_prod[of _ N])
  subgoal unfolding ket_pre_def by auto using norm_pre by auto

lemma positive_pre:
  "positive pre"
  using positive_same_outer_prod unfolding pre_def ket_pre_def by auto

lemma pre_le_one:
  "pre \<le>\<^sub>L 1\<^sub>m N"
  unfolding pre_def using outer_prod_le_one norm_pre ket_pre_def by auto

text \<open>Post-condition: should be in a state i with f i = 1\<close>

definition post :: "complex mat" where
  "post = mat N N (\<lambda>(i, j). if (i = j \<and> f i) then 1 else 0)"

lemma post_dim:
  "post \<in> carrier_mat N N"
  unfolding post_def by auto

lemma hermitian_post:
  "hermitian post"
  unfolding hermitian_def post_def
  by (auto simp add: adjoint_eval)

text \<open>Hoare triples of initialization\<close>

definition ket_zero :: "complex vec" where
  "ket_zero = Matrix.vec 2 (\<lambda>k. if k = 0 then 1 else 0)"

lemma ket_zero_dim:
  "ket_zero \<in> carrier_vec 2" unfolding ket_zero_def by auto

definition proj_zero where
  "proj_zero = proj ket_zero"

definition ket_one where
  "ket_one = Matrix.vec 2 (\<lambda>k. if k = 1 then 1 else 0)"

definition proj_one where
  "proj_one = proj ket_one"

definition ket_plus where
  "ket_plus = Matrix.vec 2 (\<lambda>k.1 / csqrt 2) "

lemma ket_plus_dim:
  "ket_plus \<in> carrier_vec 2" unfolding ket_plus_def by auto

lemma ket_plus_eval [simp]:
  "i < 2 \<Longrightarrow> ket_plus $ i = 1 / csqrt 2"
  apply (simp only: ket_plus_def)
  using index_vec less_2_cases by force

lemma csqrt_2_sq [simp]:
  "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
  by (smt of_real_add of_real_hom.hom_one of_real_power one_add_one power2_eq_square real_sqrt_pow2)

lemma ket_plus_tensor_n:
  "partial_state.tensor_vec [2, 2] {0} ket_plus ket_plus = Matrix.vec 4 (\<lambda>k. 1 / 2)"
  unfolding partial_state.tensor_vec_def state_sig.d_def
proof (rule eq_vecI, auto)
  fix i :: nat assume i: "i < 4"
  interpret st: partial_state "[2, 2]" "{0}" .
  have d1_eq: "st.d1 = 2"
    by (simp add: st.d1_def st.dims1_def nths_def)
  have "st.encode1 i < st.d1"
    by (simp add: st.d_def i)
  then have i1_lt: "st.encode1 i < 2"
    using d1_eq by auto
  have d2_eq: "st.d2 = 2"
    by (simp add: st.d2_def st.dims2_def nths_def)
  have "st.encode2 i < st.d2"
    by (simp add: st.d_def i)
  then have i2_lt: "st.encode2 i < 2"
    using d2_eq by auto
  show "ket_plus $ st.encode1 i * ket_plus $ st.encode2 i * 2 = 1"
    by (auto simp add: i1_lt i2_lt)
qed

definition proj_plus where
  "proj_plus = proj ket_plus"

lemma hadamard_on_zero:
  "hadamard *\<^sub>v ket_zero = ket_plus"
  unfolding hadamard_def ket_zero_def ket_plus_def mat_of_rows_list_def  
  apply (rule eq_vecI, auto simp add: scalar_prod_def)
  subgoal for i
    apply (drule less_2_cases)
    apply (drule disjE, auto)
    by (subst sum_le_2, auto)+.

fun exH_k :: "nat \<Rightarrow> complex mat" where
  "exH_k 0 = hadamard_on_i 0"
| "exH_k (Suc k) = exH_k k * hadamard_on_i (Suc k)"

fun H_k :: "nat \<Rightarrow> complex mat" where
  "H_k 0 = hadamard"
| "H_k (Suc k) = ptensor_mat dims {0..<Suc k} {Suc k} (H_k k) hadamard"

lemma H_k_dim:
  "k < n \<Longrightarrow> H_k k \<in> carrier_mat (2^(Suc k)) (2^(Suc k))"
proof (induct k)
  case 0
  then show ?case using hadamard_dim by auto
next
  case (Suc k)
  interpret st: partial_state2 dims "{0..<(Suc k)}" "{Suc k}"
    apply unfold_locales by auto
  have "Suc (Suc k) \<le> n" using Suc by auto
  then have "nths dims ({0..<Suc (Suc k)}) = replicate (Suc (Suc k)) 2" using dims_nths_le_n by auto
  moreover have "prod_list (replicate l 2) = 2^l" for l by simp
  moreover have "{0..<Suc k} \<union> {Suc k} = {0..<(Suc (Suc k))}" by auto
  ultimately have plssk: "prod_list (nths dims ({0..<Suc k} \<union> {Suc k})) = 2^(Suc (Suc k))" by auto
  have "dim_col (H_k (Suc k)) = 2^(Suc (Suc k))" using st.ptensor_mat_dim_col unfolding st.d0_def st.dims0_def st.vars0_def using plssk by auto
  moreover have "dim_row (H_k (Suc k)) = 2^(Suc (Suc k))" using st.ptensor_mat_dim_row unfolding st.d0_def st.dims0_def st.vars0_def using plssk by auto
  ultimately show ?case by auto
qed

lemma exH_k_eq_H_k:
  "k < n \<Longrightarrow> exH_k k = pmat_extension dims {0..<(Suc k)} {(Suc k)..<n} (H_k k)"
proof(induct k)
  case 0
  have "{(Suc 0)..<n} = vars1 - {0..<(Suc 0)}" using vars1_def by fastforce
  then show ?case unfolding exH_k.simps using vars1_def by auto
next
  case (Suc k)
  interpret st: partial_state2 dims "{0..<Suc k}" "{(Suc k)..<n}"
    apply unfold_locales by auto
  interpret st1: partial_state2 dims "{Suc k}" "{(Suc (Suc k))..<n}"
    apply unfold_locales by auto
  interpret st2: partial_state2 dims "{Suc k}" "vars1 - {Suc k}"
    apply unfold_locales by auto
  interpret st3: partial_state2 dims "{0..<Suc k}" "{Suc (Suc k)..<n}"
    apply unfold_locales by auto
  interpret st4: partial_state2 dims "{0..<Suc (Suc k)}" "{Suc (Suc k)..<n}"
    apply unfold_locales by auto

  from Suc have eq0: "exH_k (Suc k) 
    = (st.pmat_extension (H_k k)) * (st2.pmat_extension hadamard)" by auto
  have "vars1 - {0..<Suc k} = {(Suc k)..<n}" using vars1_def by auto

  then have eql1: "st.pmat_extension (H_k k) = st.ptensor_mat (H_k k) (1\<^sub>m st.d2)"
    using st.pmat_extension_def by auto

  from dims_nths_one_lt_n[OF Suc(2)] have st1d1: "st1.d1 = 2" unfolding st1.d1_def st1.dims1_def by fastforce
  have "{Suc k} \<union> {Suc (Suc k)..<n} = {Suc k..<n}" using Suc by auto
  then have "st1.d0 = st.d2" unfolding st1.d0_def st1.dims0_def st1.vars0_def st.d2_def st.dims2_def by fastforce
  then have eql2: "st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2) = 1\<^sub>m st.d2"
    using st1.ptensor_mat_id st1d1 by auto
  have eql3: "st.ptensor_mat (H_k k) (1\<^sub>m st.d2) = st.ptensor_mat (H_k k) (st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2))"
    apply (subst eql2[symmetric]) by auto

  have eqr1: "(st2.pmat_extension hadamard) = st2.ptensor_mat hadamard (1\<^sub>m st2.d2)" using st2.pmat_extension_def by auto
  have splitset: "{0..<Suc k} \<union> {Suc (Suc k)..<n} = vars1 - {Suc k}" unfolding vars1_def using Suc(2) by auto

  have Sksplit: "{Suc k} \<union> {Suc (Suc k)..<n} = {Suc k..<n}" using Suc(2) by auto
  have Sksplit1: "{0..<Suc k}\<union>{Suc k} = {0..<Suc (Suc k)}" by auto
  have "st.ptensor_mat (H_k k) (st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2)) 
    = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {0..<Suc k} {Suc k} (H_k k) (1\<^sub>m 2)) (1\<^sub>m st1.d2)"
    apply (subst ptensor_mat_assoc[symmetric, of "{0..<Suc k}" "{Suc k}" "{Suc (Suc k)..<n}" "H_k k" "1\<^sub>m 2" "1\<^sub>m st1.d2", simplified Sksplit])
    using Suc length_dims by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {Suc k} {0..<Suc k} (1\<^sub>m 2) (H_k k)) (1\<^sub>m st1.d2)"
    using ptensor_mat_comm[of "{0..<Suc k}" "{Suc k}"] by auto
  also have "\<dots> = ptensor_mat dims {Suc k} ({0..<Suc k} \<union> {Suc (Suc k)..<n})
                  (1\<^sub>m 2) 
                  (ptensor_mat dims {0..<Suc k} {Suc (Suc k)..<n} (H_k k) (1\<^sub>m st1.d2))"
    apply (subst sup_commute)
    apply (subst ptensor_mat_assoc[of "{Suc k}" "{0..<Suc k}" "{Suc (Suc k)..<n}" "(1\<^sub>m 2)" "H_k k" "1\<^sub>m st1.d2"])
    using Suc length_dims by auto
  finally have eql4: "st.pmat_extension (H_k k) 
    = st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))" using eql1 eql3 splitset by auto

  have "st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2)) * st2.ptensor_mat hadamard (1\<^sub>m st2.d2)
        = st2.ptensor_mat ((1\<^sub>m 2)*hadamard) ((st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))*(1\<^sub>m st2.d2))"
    apply (rule st2.ptensor_mat_mult[symmetric, of "1\<^sub>m 2" "hadamard" "(st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))" "(1\<^sub>m st2.d2)"])
    subgoal unfolding st2.d1_def st2.dims1_def
      by (simp add: dims_nths_one_lt_n Suc(2))
    subgoal unfolding st2.d1_def st2.dims1_def
      apply (simp add: dims_nths_one_lt_n Suc(2)) using hadamard_dim by auto
    subgoal unfolding st2.d2_def[unfolded st2.dims2_def]
      using st3.ptensor_mat_dim_col[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset]
        st3.ptensor_mat_dim_row[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset] by auto
    by auto
  also have "\<dots> = st2.ptensor_mat (hadamard) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))"
    unfolding st2.d2_def[unfolded st2.dims2_def]
    using hadamard_dim st3.ptensor_mat_dim_col[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset]
        st3.ptensor_mat_dim_row[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset] by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {Suc k} {0..<Suc k} hadamard (H_k k)) (1\<^sub>m st3.d2)"
    apply (subst ptensor_mat_assoc[symmetric, of "{Suc k}" "{0..<Suc k}" "{Suc (Suc k)..<n}" "hadamard" "H_k k" "1\<^sub>m st3.d2", simplified splitset]) 
    using Suc length_dims by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (H_k (Suc k)) (1\<^sub>m st3.d2)"
    using ptensor_mat_comm[of "{Suc k}"] Sksplit1 by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc (Suc k)}) {Suc (Suc k)..<n} (H_k (Suc k)) (1\<^sub>m st3.d2)" using Sksplit1 by auto
  also have "\<dots> = pmat_extension dims {0..<Suc (Suc k)} {Suc (Suc k)..<n} (H_k (Suc k))" 
    unfolding st4.pmat_extension_def by auto
  finally show ?case using eq0 eql4 eqr1 by auto
qed

lemma mult_exH_k_left:
  assumes "Suc k < n"
  shows "hadamard_on_i (Suc k) * exH_k k = exH_k (Suc k)"
proof -
  interpret st: partial_state2 dims "{0..<Suc k}" "{(Suc k)..<n}"
    apply unfold_locales by auto
  interpret st1: partial_state2 dims "{Suc k}" "{(Suc (Suc k))..<n}"
    apply unfold_locales by auto
  interpret st2: partial_state2 dims "{Suc k}" "vars1 - {Suc k}"
    apply unfold_locales by auto
  interpret st3: partial_state2 dims "{0..<Suc k}" "{Suc (Suc k)..<n}"
    apply unfold_locales by auto
  interpret st4: partial_state2 dims "{0..<Suc (Suc k)}" "{Suc (Suc k)..<n}"
    apply unfold_locales by auto

  from exH_k_eq_H_k assms have eq0: "exH_k (Suc k) 
    = (st.pmat_extension (H_k k)) * (st2.pmat_extension hadamard)" by auto
  have "vars1 - {0..<Suc k} = {(Suc k)..<n}" using vars1_def by auto

  then have eql1: "st.pmat_extension (H_k k) = st.ptensor_mat (H_k k) (1\<^sub>m st.d2)"
    using st.pmat_extension_def by auto

  from dims_nths_one_lt_n[OF assms] have st1d1: "st1.d1 = 2" unfolding st1.d1_def st1.dims1_def by fastforce
  have "{Suc k} \<union> {Suc (Suc k)..<n} = {Suc k..<n}" using assms by auto
  then have "st1.d0 = st.d2" unfolding st1.d0_def st1.dims0_def st1.vars0_def st.d2_def st.dims2_def by fastforce
  then have eql2: "st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2) = 1\<^sub>m st.d2"
    using st1.ptensor_mat_id st1d1 by auto
  have eql3: "st.ptensor_mat (H_k k) (1\<^sub>m st.d2) = st.ptensor_mat (H_k k) (st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2))"
    apply (subst eql2[symmetric]) by auto

  have eqr1: "(st2.pmat_extension hadamard) = st2.ptensor_mat hadamard (1\<^sub>m st2.d2)" using st2.pmat_extension_def by auto
  have splitset: "{0..<Suc k} \<union> {Suc (Suc k)..<n} = vars1 - {Suc k}" unfolding vars1_def using assms by auto

  have Sksplit: "{Suc k} \<union> {Suc (Suc k)..<n} = {Suc k..<n}" using assms by auto
  have Sksplit1: "{0..<Suc k}\<union>{Suc k} = {0..<Suc (Suc k)}" by auto
  have "st.ptensor_mat (H_k k) (st1.ptensor_mat (1\<^sub>m 2) (1\<^sub>m st1.d2)) 
    = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {0..<Suc k} {Suc k} (H_k k) (1\<^sub>m 2)) (1\<^sub>m st1.d2)"
    apply (subst ptensor_mat_assoc[symmetric, of "{0..<Suc k}" "{Suc k}" "{Suc (Suc k)..<n}" "H_k k" "1\<^sub>m 2" "1\<^sub>m st1.d2", simplified Sksplit])
    using assms length_dims by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {Suc k} {0..<Suc k} (1\<^sub>m 2) (H_k k)) (1\<^sub>m st1.d2)"
    using ptensor_mat_comm[of "{0..<Suc k}" "{Suc k}"] by auto
  also have "\<dots> = ptensor_mat dims {Suc k} ({0..<Suc k} \<union> {Suc (Suc k)..<n})
                  (1\<^sub>m 2) 
                  (ptensor_mat dims {0..<Suc k} {Suc (Suc k)..<n} (H_k k) (1\<^sub>m st1.d2))"
    apply (subst sup_commute)
    apply (subst ptensor_mat_assoc[of "{Suc k}" "{0..<Suc k}" "{Suc (Suc k)..<n}" "(1\<^sub>m 2)" "H_k k" "1\<^sub>m st1.d2"]) using assms length_dims by auto
  finally have "st.pmat_extension (H_k k) 
    = st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))" using eql1 eql3 splitset by auto
  moreover have "st.pmat_extension (H_k k) = exH_k k" using exH_k_eq_H_k assms by auto
  ultimately have eql4: "exH_k k = st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))" by auto

  have "st2.ptensor_mat hadamard (1\<^sub>m st2.d2) * st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))
        = st2.ptensor_mat (hadamard*(1\<^sub>m 2)) ((1\<^sub>m st2.d2)* (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2)))"
    apply (rule st2.ptensor_mat_mult[symmetric, of "hadamard" "1\<^sub>m 2" "(1\<^sub>m st2.d2)" "(st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))"])
    subgoal unfolding st2.d1_def st2.dims1_def apply (simp add: dims_nths_one_lt_n assms) using hadamard_dim by auto
    subgoal unfolding st2.d1_def st2.dims1_def by (simp add: dims_nths_one_lt_n assms) 
    subgoal by auto
    subgoal unfolding st2.d2_def[unfolded st2.dims2_def] using st3.ptensor_mat_dim_col[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset]
        st3.ptensor_mat_dim_row[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset] by auto
    done
  also have "\<dots> = st2.ptensor_mat (hadamard) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2))"
    unfolding st2.d2_def[unfolded st2.dims2_def]
    using hadamard_dim st3.ptensor_mat_dim_col[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset]
        st3.ptensor_mat_dim_row[unfolded st3.d0_def st3.dims0_def st3.vars0_def, simplified splitset] by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (ptensor_mat dims {Suc k} {0..<Suc k} hadamard (H_k k)) (1\<^sub>m st3.d2)"
    apply (subst ptensor_mat_assoc[symmetric, of "{Suc k}" "{0..<Suc k}" "{Suc (Suc k)..<n}" "hadamard" "H_k k" "1\<^sub>m st3.d2", simplified splitset]) 
    using assms length_dims by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc k}\<union>{Suc k}) {Suc (Suc k)..<n} (H_k (Suc k)) (1\<^sub>m st3.d2)"
    using ptensor_mat_comm[of "{Suc k}"] Sksplit1 by auto
  also have "\<dots> = ptensor_mat dims ({0..<Suc (Suc k)}) {Suc (Suc k)..<n} (H_k (Suc k)) (1\<^sub>m st3.d2)" using Sksplit1 by auto
  also have "\<dots> = pmat_extension dims {0..<Suc (Suc k)} {Suc (Suc k)..<n} (H_k (Suc k))" 
    unfolding st4.pmat_extension_def by auto
  also have "\<dots> = exH_k (Suc k)" using exH_k_eq_H_k[of "Suc k"] assms by auto
  finally have "st2.ptensor_mat hadamard (1\<^sub>m st2.d2) * st2.ptensor_mat (1\<^sub>m 2) (st3.ptensor_mat (H_k k) (1\<^sub>m st3.d2)) 
    =exH_k (Suc k)".
  then show ?thesis unfolding hadamard_on_i_def
    using eql4 eqr1 by auto 
qed

lemma exH_eq_H:
  "exH_k (n - 1) = H_k (n - 1)"
proof -
  have "\<exists>m. n = Suc (Suc m)" using n by presburger
  then obtain m where m: "n = Suc (Suc m)" using n by auto
  then have "exH_k m = pmat_extension dims {0..<(Suc m)} {(Suc m)..<n} (H_k m)" using exH_k_eq_H_k by auto
  then have "exH_k (Suc m) = pmat_extension dims {0..<(Suc m)} {(Suc m)..<n} (H_k m) 
                            * (pmat_extension dims {Suc m} (vars1 - {Suc m}) hadamard)" by auto
  moreover have "{(Suc m)..<n} = {Suc m}" using m by auto
  moreover have "vars1 - {Suc m} = {0..<Suc m}" unfolding vars1_def using m by auto
  ultimately have eqSm: "exH_k (Suc m) = pmat_extension dims {0..<(Suc m)} {Suc m} (H_k m) 
                            * (pmat_extension dims {Suc m} {0..<Suc m} hadamard)" by auto

  interpret stm1: partial_state2 dims "{Suc m}" "{0..<Suc m}" 
    apply unfold_locales by auto
  interpret stm2: partial_state2 dims "{0..<Suc m}" "{Suc m}"
    apply unfold_locales by auto
  have "nths dims {0..<Suc m} = replicate (Suc m) 2" using dims_nths_le_n m by auto
  then have stm2d1: "stm2.d1 = 2^(Suc m)" unfolding stm2.d1_def stm2.dims1_def by auto
  have stm2d2: "stm2.d2 = 2" unfolding stm2.d2_def stm2.dims2_def using dims_nths_one_lt_n m by auto

  have "m < n" using m by auto
  then have "H_k m \<in> carrier_mat (2^(Suc m)) (2^(Suc m))" using H_k_dim by auto
  then have Hkm1: "(H_k m) * (1\<^sub>m stm2.d1) = (H_k m)" unfolding stm2d1 by auto

  have eqd12: "stm1.d2 = stm2.d1" unfolding stm1.d2_def stm1.dims2_def stm2.d1_def stm2.dims1_def by auto
  have "pmat_extension dims {Suc m} {0..<Suc m} hadamard = stm1.ptensor_mat hadamard (1\<^sub>m stm1.d2)" using stm1.pmat_extension_def by auto
  also have "\<dots> = stm2.ptensor_mat (1\<^sub>m stm2.d1) hadamard" using ptensor_mat_comm eqd12 by auto
  finally have eqr: "(pmat_extension dims {Suc m} {0..<Suc m} hadamard) = stm2.ptensor_mat (1\<^sub>m stm2.d1) hadamard".
  then have "exH_k (Suc m) = stm2.ptensor_mat (H_k m) (1\<^sub>m stm2.d2) * stm2.ptensor_mat (1\<^sub>m stm2.d1) hadamard" 
    using eqSm unfolding stm2.pmat_extension_def by auto
  also have "\<dots> = stm2.ptensor_mat ((H_k m) * (1\<^sub>m stm2.d1)) (1\<^sub>m stm2.d2 * hadamard)" 
    apply (rule stm2.ptensor_mat_mult[symmetric, of "H_k m" "1\<^sub>m stm2.d1" "1\<^sub>m stm2.d2" "hadamard"])
    unfolding stm2d1 stm2d2 using H_k_dim m hadamard_dim by auto
  also have "\<dots> = stm2.ptensor_mat (H_k m) (hadamard)" using H_k_dim hadamard_dim stm2d1 stm2d2 Hkm1 by auto
  also have "\<dots> = H_k (Suc m)" unfolding stm2.ptensor_mat_def H_k.simps by auto
  finally have  "exH_k (Suc m) = H_k (Suc m)" by auto
  moreover have "Suc m = n - 1" using m by auto
  ultimately show ?thesis by auto
qed

fun ket_zero_k :: "nat \<Rightarrow> complex vec" where
  "ket_zero_k 0 = ket_zero"
| "ket_zero_k (Suc k) = ptensor_vec dims {0..<(Suc k)} {Suc k} (ket_zero_k k) ket_zero"

lemma ket_zero_k_dim:
  assumes "k < n"
  shows "ket_zero_k k \<in> carrier_vec (2^(Suc k))"
proof (cases k)
  case 0
  show ?thesis using ket_zero_dim 0 by auto
next
  case (Suc k)
  interpret st: partial_state2 dims "{0..<(Suc k)}" "{Suc k}"
    apply unfold_locales by auto
  have "Suc (Suc k) \<le> n" using assms Suc by auto
  then have "nths dims ({0..<Suc (Suc k)}) = replicate (Suc (Suc k)) 2" using dims_nths_le_n by auto
  moreover have "prod_list (replicate l 2) = 2^l" for l by simp
  moreover have "{0..<Suc k} \<union> {Suc k} = {0..<(Suc (Suc k))}" by auto
  ultimately have plssk: "prod_list (nths dims ({0..<Suc k} \<union> {Suc k})) = 2^(Suc (Suc k))" by auto
  show ?thesis apply (rule carrier_vecI) unfolding ket_zero_k.simps Suc
    using st.ptensor_vec_dim[of "ket_zero_k k" ket_zero] plssk unfolding st.d0_def st.dims0_def st.vars0_def by auto
qed

fun ket_plus_k where
  "ket_plus_k 0 = ket_plus"
| "ket_plus_k (Suc k) = ptensor_vec dims {0..<(Suc k)} {Suc k} (ket_plus_k k) ket_plus"

lemma ket_plus_k_dim:
  assumes "k < n"
  shows "ket_plus_k k \<in> carrier_vec (2^(Suc k))"
proof (cases k)
  case 0
  show ?thesis using ket_plus_dim 0 by auto
next
  case (Suc k)
  interpret st: partial_state2 dims "{0..<(Suc k)}" "{Suc k}"
    apply unfold_locales by auto
  have "Suc (Suc k) \<le> n" using assms Suc by auto
  then have "nths dims ({0..<Suc (Suc k)}) = replicate (Suc (Suc k)) 2" using dims_nths_le_n by auto
  moreover have "prod_list (replicate l 2) = 2^l" for l by simp
  moreover have "{0..<Suc k} \<union> {Suc k} = {0..<(Suc (Suc k))}" by auto
  ultimately have plssk: "prod_list (nths dims ({0..<Suc k} \<union> {Suc k})) = 2^(Suc (Suc k))" by auto
  show ?thesis apply (rule carrier_vecI) unfolding ket_zero_k.simps Suc
    using st.ptensor_vec_dim plssk unfolding st.d0_def st.dims0_def st.vars0_def by auto
qed


lemma H_k_ket_zero_k:
  "k < n \<Longrightarrow> (H_k k) *\<^sub>v (ket_zero_k k) = (ket_plus_k k)"
proof (induct k)
  case 0
  show ?case using hadamard_on_zero unfolding H_k.simps ket_zero_k.simps ket_plus_k.simps by auto
next
  case (Suc k)
  then have k: "k < n" by auto
  interpret st: partial_state2 dims "{0..<(Suc k)}" "{Suc k}"
    apply unfold_locales by auto
  have "nths dims {0..<Suc k} = replicate (Suc k) 2" using dims_nths_le_n Suc by auto
  then have std1: "st.d1 = 2^(Suc k)" unfolding st.d1_def st.dims1_def by auto
  have std2: "st.d2 = 2" unfolding st.d2_def st.dims2_def using dims_nths_one_lt_n Suc by auto
  have "H_k (Suc k) *\<^sub>v ket_zero_k (Suc k) = st.ptensor_mat (H_k k) hadamard *\<^sub>v st.ptensor_vec (ket_zero_k k) ket_zero" by auto
  also have "\<dots> = st.ptensor_vec ((H_k k) *\<^sub>v (ket_zero_k k)) (hadamard *\<^sub>v ket_zero)" 
    using st.ptensor_mat_mult_vec[unfolded std1 std2, OF H_k_dim[OF k] ket_zero_k_dim[OF k] hadamard_dim ket_zero_dim] by auto
  also have "\<dots> = st.ptensor_vec (ket_plus_k k) ket_plus" using Suc hadamard_on_zero by auto
  finally show ?case by auto
qed


lemma encode1_replicate_2:
  "partial_state.encode1 (replicate (Suc k) 2) {0..<k} i = i mod (2 ^ k)"
proof -
  have take_Suc: "take k (replicate (Suc k) 2) = replicate k 2"
    apply (subst take_replicate) by auto
  have take_encode: "take k (digit_encode (replicate (Suc k) 2) i) = digit_encode (replicate k 2) i"
    apply (subst digit_encode_take) using take_Suc by metis
  show ?thesis
    unfolding partial_state.encode1_def partial_state.dims1_def
      nths_upt_eq_take[simplified lessThan_atLeast0] take_Suc take_encode
      digit_decode_encode prod_list_replicate ..
qed

lemma encode2_replicate_2:
  assumes "i < 2 ^ Suc k"
  shows "partial_state.encode2 (replicate (Suc k) 2) {0..<k} i = i div (2 ^ k)"
proof -
  have drop_Suc: "drop k (replicate (Suc k) 2) = [2]"
    apply (subst drop_replicate) by auto
  have drop_encode: "drop k (digit_encode (replicate (Suc k) 2) i) = digit_encode [2] (i div (2 ^ k))"
    unfolding digit_encode_drop drop_Suc take_replicate prod_list_replicate
    by (metis lessI min.strict_order_iff)
  have le2: "i div 2 ^ k < 2"
    using assms by (auto simp add: less_mult_imp_div_less)
  have prod_list_2: "prod_list [2] = 2" by simp
  show ?thesis
    unfolding partial_state.encode2_def partial_state.dims2_def
      nths_minus_upt_eq_drop[simplified lessThan_atLeast0] drop_Suc drop_encode
      digit_decode_encode prod_list_2
    using le2 by auto
qed

lemma ket_zero_k_decode:
  "k < n \<Longrightarrow> ket_zero_k k = Matrix.vec (2^(Suc k)) (\<lambda>k. if k = 0 then 1 else 0)"
proof (induct k)
  case 0                            
  show ?case apply (rule eq_vecI) by (auto simp add: ket_zero_def)
next
  case (Suc k)
  then have k: "k < n" by auto
  have kzkk: "ket_zero_k k = Matrix.vec (2 ^ Suc k) (\<lambda>k. if (k = 0) then 1 else 0)" using Suc(1)[OF k] by auto

  have dSk: "ket_zero_k (Suc k) \<in> carrier_vec (2^(Suc (Suc k)))" using ket_zero_k_dim[OF Suc(2)] by auto

  interpret st: partial_state "replicate (Suc (Suc k)) 2" "{0..<Suc k}".
  interpret st2: partial_state2 dims "{0..<Suc k}" "{Suc k}" by (unfold_locales, auto)

  have splitset: "({0..<Suc k} \<union> {Suc k}) = {0..<Suc (Suc k)}" by auto
  then have st2dims0: "st2.dims0 = replicate (Suc (Suc k)) 2" unfolding st2.dims0_def st2.vars0_def 
    using dims_nths_le_n[of "Suc (Suc k)"] Suc by auto
  have "\<And>x. (x \<in> {0..<Suc k} \<Longrightarrow> {y \<in> {0..<Suc (Suc k)}. y < x} = {0..<x})" by auto
  then have cardeq: "\<And>x. (x \<in> {0..<Suc k} \<Longrightarrow> card {y \<in> {0..<Suc (Suc k)}. y < x} = card {0..<x})" by auto
  have setcong: "\<And>g h I. (\<And>x. (x \<in> I \<Longrightarrow> g x = h x)) \<Longrightarrow> {g x | x. x \<in> I} = {h x | x. x \<in> I}" by metis
  have "{card {y \<in> {0..<Suc (Suc k)}. y < x} |x. x \<in> {0..<Suc k}} = {card {0..<x} |x. x \<in> {0..<Suc k}} "
    using setcong[OF cardeq, of "{0..<Suc k}"] by auto
  also have "\<dots> = {0..<Suc k}" by auto
  finally have st2vars1': "st2.vars1' = {0..<Suc k}" unfolding st2.vars1'_def st2.vars0_def splitset ind_in_set_def by fastforce
  have st2pvsttv: "st2.ptensor_vec = st.tensor_vec" unfolding st2.ptensor_vec_def using st2dims0 st2vars1' by auto
  have "st.encode1 0 = 0" using encode1_replicate_2[of "Suc k" 0] by auto
  moreover have "st.encode2 0 = 0" using encode2_replicate_2[of 0 "Suc k"] by auto
  moreover have  std: "st.d = 2^(Suc (Suc k))" unfolding st.d_def by auto
  ultimately have kzkk0: "ket_zero_k (Suc k) $ 0 = 1" 
    unfolding ket_zero_k.simps st2pvsttv st.tensor_vec_def ket_zero_def using kzkk by auto

  have kzkki: "ket_zero_k (Suc k) $ i = 0" if ine0: "i \<noteq> 0" and ile: "i < 2^(Suc (Suc k))" for i
  proof (cases "i mod (2 ^ Suc k) \<noteq> 0")
    case True
    then have "ket_zero_k k $ st.encode1 i = 0" unfolding kzkk using encode1_replicate_2[of "Suc k" i] ile by auto
    then show ?thesis unfolding ket_zero_k.simps st2pvsttv st.tensor_vec_def ket_zero_def std using ile by auto
  next
    case False
    have "i div (2 ^ Suc k) \<noteq> 0 \<or> i mod (2 ^ Suc k) \<noteq> 0" using ine0 by fastforce
    then have "i div (2 ^ Suc k) \<noteq> 0" using False by auto
    moreover have "i div (2 ^ Suc k) < 2" using ile less_mult_imp_div_less by auto
    ultimately have "i div (2 ^ Suc k) = 1" by auto
    then have "st.encode2 i = 1" using encode2_replicate_2[of i "Suc k"] ile by auto
    then have "Matrix.vec 2 (\<lambda>k. if k = 0 then 1 else 0) $ st.encode2 i = 0" 
      unfolding kzkk by fastforce
    then show ?thesis unfolding ket_zero_k.simps st2pvsttv st.tensor_vec_def ket_zero_def std using ile by auto
  qed

  show ?case apply (rule eq_vecI)
    subgoal for i using kzkk0 kzkki by auto
    using carrier_vecD[OF dSk] by auto
qed

lemma ket_plus_k_decode:
  "k < n \<Longrightarrow> ket_plus_k k = Matrix.vec (2^(Suc k)) (\<lambda>l. 1 / csqrt (2^(Suc k)))"
proof (induct k)
  case 0
  then show ?case unfolding ket_plus_k.simps ket_plus_def by auto
next
  case (Suc k)
  then have kpkk: "ket_plus_k k = Matrix.vec (2 ^ Suc k) (\<lambda>l. 1 / csqrt (2 ^ Suc k))" by auto

  have dSk: "ket_plus_k (Suc k) \<in> carrier_vec (2^(Suc (Suc k)))" using ket_plus_k_dim[OF Suc(2)] by auto

  interpret st: partial_state "replicate (Suc (Suc k)) 2" "{0..<Suc k}".
  interpret st2: partial_state2 dims "{0..<Suc k}" "{Suc k}" by (unfold_locales, auto)

  have splitset: "({0..<Suc k} \<union> {Suc k}) = {0..<Suc (Suc k)}" by auto
  then have st2dims0: "st2.dims0 = replicate (Suc (Suc k)) 2" unfolding st2.dims0_def st2.vars0_def 
    using dims_nths_le_n[of "Suc (Suc k)"] Suc by auto
  have "\<And>x. (x \<in> {0..<Suc k} \<Longrightarrow> {y \<in> {0..<Suc (Suc k)}. y < x} = {0..<x})" by auto
  then have cardeq: "\<And>x. (x \<in> {0..<Suc k} \<Longrightarrow> card {y \<in> {0..<Suc (Suc k)}. y < x} = card {0..<x})" by auto
  have setcong: "\<And>g h I. (\<And>x. (x \<in> I \<Longrightarrow> g x = h x)) \<Longrightarrow> {g x | x. x \<in> I} = {h x | x. x \<in> I}" by metis
  have "{card {y \<in> {0..<Suc (Suc k)}. y < x} |x. x \<in> {0..<Suc k}} = {card {0..<x} |x. x \<in> {0..<Suc k}} "
    using setcong[OF cardeq, of "{0..<Suc k}"] by auto
  also have "\<dots> = {0..<Suc k}" by auto
  finally have st2vars1': "st2.vars1' = {0..<Suc k}" unfolding st2.vars1'_def st2.vars0_def splitset ind_in_set_def by blast
  have st2pvsttv: "st2.ptensor_vec = st.tensor_vec" unfolding st2.ptensor_vec_def using st2dims0 st2vars1' by auto

  have "csqrt (2 ^ (Suc k)) = complex_of_real (sqrt (2 ^ (Suc k)))" by simp
  moreover have "complex_of_real (sqrt (2 ^ (Suc k))) * complex_of_real (sqrt 2) = complex_of_real (sqrt (2 ^ (Suc (Suc k))))"
    by (metis of_real_mult power_Suc power_commutes real_sqrt_power)
  ultimately have "csqrt (2 ^ (Suc k)) * csqrt 2 = csqrt (2 ^ (Suc (Suc k)))" by auto
  moreover have "1 / csqrt (2 ^ Suc k) * 1 / csqrt 2 = 1 / (csqrt (2 ^ (Suc k)) * csqrt 2)" by simp
  ultimately have csqrt2p :"1 / csqrt (2 ^ Suc k) * 1 / csqrt 2 = 1 / (csqrt (2 ^ (Suc (Suc k))))" by simp

  have std: "st.d = 2^(Suc (Suc k))" unfolding st.d_def by auto

  have nthsSSk2: "nths (replicate (Suc (Suc k)) 2) {0..<Suc k} = replicate (Suc k) 2" 
    unfolding nths_replicate[of "Suc (Suc k)" 2 "{0..<Suc k}"]
    by (smt Collect_cong \<open>{card {0..<x} |x. x \<in> {0..<Suc k}} = {0..<Suc k}\<close> atLeastLessThan_iff card_atLeastLessThan diff_zero less_SucI)
  then have std1: "st.d1 = 2^(Suc k)" unfolding st.d1_def st.dims1_def nthsSSk2 by auto
  have "{i. i < Suc (Suc k) \<and> i \<in> {Suc k..}} = {Suc k}" by auto
  then have "nths (replicate (Suc (Suc k)) 2) ({Suc k..}) = replicate 1 2" unfolding nths_replicate by auto
  moreover have "(- {0..<Suc k}) = {Suc k..}" by auto
  ultimately have nthsSSk2c: "nths (replicate (Suc (Suc k)) 2) (- {0..<Suc k}) = replicate 1 2" by auto
  have std2: "st.d2 = 2" unfolding st.d2_def st.dims2_def apply (subst nthsSSk2c) by auto

  have "st.encode1 i < st.d1" if "i < st.d" for i using that st.encode1_lt[OF that] by auto
  then have kpkki: "ket_plus_k k $ st.encode1 i = 1 / csqrt (2^(Suc k))" if "i < st.d" for i unfolding kpkk std1 using that by auto
  have "st.encode2 i < st.d2" if "i < st.d" for i using that st.encode2_lt[OF that] by auto
  then have kpi: "ket_plus $ st.encode2 i = 1 / csqrt 2" if "i < st.d" for i unfolding ket_plus_def std2 using that by auto
  have kzkki: "ket_plus_k (Suc k) $ i = 1 / (csqrt (2 ^ (Suc (Suc k))))" if "i < st.d" for i
    unfolding ket_plus_k.simps st2pvsttv st.tensor_vec_def using csqrt2p kpkki kpi that  by auto
  show ?case apply (rule eq_vecI)
    subgoal for i using kzkki unfolding std by auto
    using carrier_vecD[OF dSk] by auto
qed

lemma exH_k_mult_pre_is_psi:
  "exH_k (n - 1) *\<^sub>v ket_pre = \<psi>"
proof -
  have "exH_k (n - 1) = H_k (n - 1)" using exH_eq_H by auto
  moreover have "ket_zero_k (n - 1) = ket_pre" using ket_zero_k_decode[of "n - 1"] ket_pre_def N_def n by auto
  moreover have "ket_plus_k (n - 1) = \<psi>" using ket_plus_k_decode[of "n - 1"] \<psi>_def N_def n by auto
  moreover have "H_k (n - 1) *\<^sub>v ket_zero_k (n - 1) = ket_plus_k (n - 1)" using H_k_ket_zero_k n by auto
  ultimately show ?thesis by auto
qed

definition ket_k :: "nat \<Rightarrow> complex vec" where
  "ket_k x = Matrix.vec K (\<lambda>k. if k = x then 1 else 0)"

lemma ket_k_dim:
  "ket_k k \<in> carrier_vec K"
  unfolding ket_k_def by auto

lemma mat_incr_mult_ket_k:
  "k < K \<Longrightarrow> (mat_incr K) *\<^sub>v (ket_k k) = (ket_k ((k + 1) mod K))"
  apply (rule eq_vecI)
  unfolding mat_incr_def ket_k_def
   apply (simp add: scalar_prod_def)
   apply (case_tac "k = K - 1")
  subgoal for i apply auto by (simp add: sum_only_one_neq_0[of _ "K - 1"])
  subgoal for i apply auto by (simp add: sum_only_one_neq_0[of _ "i - 1"])
  by auto

definition proj_k where
  "proj_k x = proj (ket_k x)"

lemma proj_k_dim:
  "proj_k k \<in> carrier_mat K K"
  unfolding proj_k_def using ket_k_dim by auto

lemma norm_ket_k_lt_K:
  "k < K \<Longrightarrow> inner_prod (ket_k k) (ket_k k) = 1"
  unfolding ket_k_def apply (simp add: scalar_prod_def)
  using sum_only_one_neq_0[of "{0..<K}" k "\<lambda>i. (if i = k then 1 else 0) * cnj (if i = k then 1 else 0)"] by auto

lemma norm_ket_k_ge_K:
  "k \<ge> K \<Longrightarrow> inner_prod (ket_k k) (ket_k k) = 0"
  unfolding ket_k_def by (simp add: scalar_prod_def)

lemma norm_ket_k:
  "inner_prod (ket_k k) (ket_k k) \<le> 1"
  apply (case_tac "k < K")
  using norm_ket_k_lt_K norm_ket_k_ge_K by auto

lemma proj_k_mat:
  assumes "k < K"
  shows "proj_k k = mat K K (\<lambda>(i, j). if (i = j \<and> i = k) then 1 else 0)" 
  apply (rule eq_matI)
    apply (simp add: proj_k_def ket_k_def index_outer_prod) 
  using proj_k_dim by auto

lemma positive_proj_k:
  "positive (proj_k k)"
  using positive_same_outer_prod unfolding proj_k_def ket_k_def by auto 

lemma proj_k_le_one:
  "(proj_k k) \<le>\<^sub>L 1\<^sub>m K"
  unfolding proj_k_def using outer_prod_le_one norm_ket_k ket_k_def by auto

definition proj_psi where
  "proj_psi = proj \<psi>"

lemma proj_psi_dim:
  "proj_psi \<in> carrier_mat N N"
  unfolding proj_psi_def \<psi>_def by auto

lemma norm_psi:
  "inner_prod \<psi> \<psi> = 1"
  apply (simp add: \<psi>_eval scalar_prod_def)
  by (metis norm_of_nat norm_of_real of_real_mult of_real_of_nat_eq real_sqrt_mult_self)

lemma proj_psi_mat:
  "proj_psi = mat N N (\<lambda>k. 1 / N)"
  unfolding proj_psi_def
  apply (rule eq_matI, simp_all)
    apply (simp add: \<psi>_def index_outer_prod)
    apply (smt of_nat_less_0_iff of_real_of_nat_eq of_real_power power2_eq_square real_sqrt_pow2)
   by (auto simp add: carrier_matD[OF outer_prod_dim[OF \<psi>_dim(1) \<psi>_dim(1)]])

lemma hermitian_proj_psi:
  "hermitian proj_psi" 
  unfolding hermitian_def proj_psi_mat apply (rule eq_matI)
  by (auto simp add: adjoint_eval)

lemma hermitian_exproj_psi:
  "hermitian (tensor_P proj_psi (1\<^sub>m K))"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_hermitian)
  using proj_psi_dim ps_P_d1 ps_P_d2 hermitian_proj_psi hermitian_one by auto

lemma proj_psi_is_projection:
  "proj_psi * proj_psi = proj_psi"
proof -
  have "proj_psi * proj_psi = inner_prod \<psi> \<psi> \<cdot>\<^sub>m proj_psi"
    unfolding proj_psi_def 
    apply (subst outer_prod_mult_outer_prod) using  \<psi>_def by auto
  also have "\<dots> = proj_psi"
    using \<psi>_inner by auto
  finally show ?thesis.
qed

lemma proj_psi_trace:
  "trace (proj_psi) = 1"
  unfolding proj_psi_def
  apply (subst trace_outer_prod[of _ N]) 
  subgoal unfolding \<psi>_def by auto using norm_psi by auto

lemma positive_proj_psi:
  "positive (proj_psi)"
  using positive_same_outer_prod unfolding proj_psi_def \<psi>_def by auto 

lemma proj_psi_le_one:
  "(proj_psi) \<le>\<^sub>L 1\<^sub>m N"
  unfolding proj_psi_def using outer_prod_le_one norm_psi \<psi>_def by auto

lemma hermitian_hadamard_on_k:
  assumes "k < n"
  shows "hermitian (hadamard_on_i k)"
proof -
  interpret st2: partial_state2 dims "{k}" "(vars1 - {k})"
    apply unfold_locales by auto
  have st2d1: "st2.dims1 = [2]" unfolding st2.dims1_def dims_def
    using assms dims_nths_one_lt_n local.dims_def st2.dims1_def by auto
  show "hermitian (hadamard_on_i k)" unfolding hadamard_on_i_def st2.pmat_extension_def st2.ptensor_mat_def
    apply (rule partial_state.tensor_mat_hermitian)
    subgoal unfolding partial_state.d1_def partial_state.dims1_def st2.nths_vars1' hadamard_def by (simp add: st2d1)
    subgoal unfolding partial_state.d2_def partial_state.dims2_def st2.nths_vars2' st2.d2_def by auto
    subgoal unfolding hermitian_def hadamard_def apply (rule eq_matI) by (auto simp add: adjoint_dim adjoint_eval)
    using hermitian_one by auto
qed

lemma hermitian_H_k:
  "k < n \<Longrightarrow> hermitian (H_k k)"
proof (induct k)
  case 0
  show ?case unfolding H_k.simps hermitian_def hadamard_def apply (rule eq_matI) by (auto simp add: adjoint_dim adjoint_eval)
next
  case (Suc k)
  interpret st2: partial_state2 dims "{0..<Suc k}" "{Suc k}"
    apply unfold_locales by auto
  have st2d1: "prod_list st2.dims1 = (2^(Suc k))" unfolding st2.dims1_def dims_def using Suc(2)
    using dims_nths_le_n local.dims_def st2.dims1_def by auto
  have st2d2: "st2.dims2 = [2]" unfolding st2.dims2_def dims_def using Suc(2)
    using dims_nths_one_lt_n local.dims_def st2.dims2_def by auto
  show ?case unfolding H_k.simps st2.ptensor_mat_def
    apply (rule partial_state.tensor_mat_hermitian)
    subgoal unfolding partial_state.d1_def partial_state.dims1_def st2.nths_vars1' using st2d1 H_k_dim Suc by auto
    subgoal unfolding partial_state.d2_def partial_state.dims2_def st2.nths_vars2' st2.d2_def using st2d2 by (simp add: hadamard_def)
    subgoal using Suc by auto
    using hermitian_hadamard by auto
qed

lemma unitary_H_k:
  "k < n \<Longrightarrow> unitary (H_k k)"
proof (induct k)
  case 0
  show ?case using unitary_hadamard by auto
next
  case (Suc k)
  then have k: "k < n" by auto
  interpret st2: partial_state2 dims "{0..<Suc k}" "{Suc k}" by (unfold_locales, auto)

  have st2d1: "prod_list st2.dims1 = (2^(Suc k))" unfolding st2.dims1_def dims_def using Suc(2)
    using dims_nths_le_n local.dims_def st2.dims1_def by auto
  have st2d2: "st2.dims2 = [2]" unfolding st2.dims2_def dims_def using Suc(2)
    using dims_nths_one_lt_n local.dims_def st2.dims2_def by auto
  show ?case unfolding H_k.simps st2.ptensor_mat_def
    apply (rule partial_state.tensor_mat_unitary[of "H_k k" st2.dims0 st2.vars1' hadamard]  )
    unfolding partial_state.d1_def partial_state.dims1_def st2.nths_vars1' partial_state.d2_def partial_state.dims2_def
      st2.nths_vars2'
       apply (auto simp add: st2d1 st2d2 )
    subgoal using H_k_dim[OF k] by auto
    subgoal using hadamard_dim by auto
    subgoal using Suc by auto
    using unitary_hadamard by auto
qed

lemma exH_k_dim:
  shows "k < n \<Longrightarrow> exH_k k \<in> carrier_mat N N"
  apply (induct k)
  using hadamard_on_i_dim by auto

lemma exH_n_dim:
  shows "exH_k (n - 1) \<in> carrier_mat N N"
  using exH_k_dim n by auto

lemma unitary_exH_k:
  shows "k < n \<Longrightarrow> unitary (exH_k k)" 
proof (induct k)
  case 0
  then show ?case unfolding exH_k.simps using unitary_hadamard_on_i 0 by auto 
next
  case (Suc k)
  show ?case unfolding exH_k.simps apply (subst unitary_times_unitary[of _ N])
    subgoal using exH_k_dim Suc by auto
    subgoal using hadamard_on_i_dim Suc by auto
    subgoal using Suc by auto
    using unitary_hadamard_on_i Suc by auto
qed

lemma hermitian_exH_n:
  "hermitian (exH_k (n - 1))"
  using hermitian_H_k exH_eq_H n by auto

lemma exH_k_mult_psi_is_pre:
  "exH_k (n - 1) *\<^sub>v \<psi> = ket_pre"
proof -
  let ?H = "exH_k (n - 1)"
  have "hermitian ?H" using hermitian_H_k exH_eq_H n by auto
  then have eqad: "adjoint ?H = ?H" unfolding hermitian_def by auto
  have d: "?H \<in> carrier_mat N N" using exH_k_dim n by auto
  have "unitary ?H" using unitary_exH_k n by auto
  then have id: "?H * ?H = 1\<^sub>m N"
    unfolding unitary_def inverts_mat_def
    using d apply (subst (2) eqad[symmetric]) by auto
  have "?H *\<^sub>v \<psi> = ?H *\<^sub>v (?H *\<^sub>v ket_pre)"
    using exH_k_mult_pre_is_psi by auto
  also have "\<dots> = (?H * ?H) *\<^sub>v ket_pre"
    using d ket_pre_def by auto
  also have "\<dots> = ket_pre"
    using id ket_pre_def by auto
  finally show ?thesis by auto
qed

fun exexH_k :: "nat \<Rightarrow> complex mat" where
  "exexH_k k = tensor_P (exH_k k) (1\<^sub>m K)"

lemma unitary_exexH_k:
  "k < n \<Longrightarrow> unitary (exexH_k k)" 
  unfolding exexH_k.simps ps2_P.ptensor_mat_def 
  apply (subst partial_state.tensor_mat_unitary)
  subgoal using exH_k_dim unfolding partial_state.d1_def partial_state.dims1_def ps2_P.nths_vars1' ps2_P.dims1_def dims_vars1 N_def by auto
  subgoal unfolding partial_state.d2_def partial_state.dims2_def ps2_P.nths_vars2' ps2_P.dims2_def dims_vars2 by auto
  using unitary_exH_k unitary_one by auto

lemma exexH_k_dim:
  "k < n \<Longrightarrow> exexH_k k \<in> carrier_mat d d"
  unfolding exexH_k.simps using ps2_P.ptensor_mat_carrier ps2_P_d0 by auto

lemma hoare_seq_utrans:
  fixes P :: "complex mat"
  assumes "unitary U1" and "unitary U2" and "is_quantum_predicate P"
    and dU1: "U1 \<in> carrier_mat d d" and dU2: "U2 \<in> carrier_mat d d"
  shows "
   \<turnstile>\<^sub>p 
   {adjoint (U2 * U1) * P * (U2 * U1)} 
   Utrans U1;; Utrans U2
   {P}"
proof -
  have hp0: "\<turnstile>\<^sub>p {adjoint (U2) * P * (U2)} Utrans U2 {P}"
    using assms hoare_partial.intros by auto
  have qp: "is_quantum_predicate (adjoint (U2) * P * (U2))"
    using qp_close_under_unitary_operator assms by auto
  then have hp1: "\<turnstile>\<^sub>p {adjoint U1 * (adjoint (U2) * P * (U2)) * U1} Utrans U1 {adjoint (U2) * P * (U2)}"
    using hoare_partial.intros by auto
  have dP: "P \<in> carrier_mat d d" using assms is_quantum_predicate_def by auto
  have eq: "adjoint U1 * (adjoint U2 * P * U2) * U1 = adjoint (U2 * U1) * P * (U2 * U1)"
    using dU1 dU2 dP by (mat_assoc d)
  with hp1 have hp2: "\<turnstile>\<^sub>p {adjoint (U2 * U1) * P * (U2 * U1)} Utrans U1 {adjoint (U2) * P * (U2)}" by auto

  have "is_quantum_predicate (adjoint U1 * (adjoint U2 * P * U2) * U1)" using qp qp_close_under_unitary_operator assms by auto
  then have "is_quantum_predicate (adjoint (U2 * U1) * P * (U2 * U1))" using eq by auto
  then show ?thesis using hoare_partial.intros(3)[OF _ qp assms(3)] hp0 hp2 by auto
qed

lemma qp_close_after_exexH_k:
  fixes P :: "complex mat"
  assumes "is_quantum_predicate P"
  shows "k < n \<Longrightarrow> is_quantum_predicate (adjoint (exexH_k k) * P * exexH_k k)"
  apply (subst qp_close_under_unitary_operator)
  subgoal using exexH_k_dim by auto
  subgoal using unitary_exexH_k by auto
  using assms by auto

lemma hoare_hadamard_n:
  fixes P :: "complex mat"
  shows "is_quantum_predicate P \<Longrightarrow> k < n \<Longrightarrow> 
   \<turnstile>\<^sub>p 
   {adjoint (exexH_k k) * P * exexH_k k} 
   hadamard_n (Suc k)
   {P}"
proof (induct k arbitrary: P)
  case 0
  have qp: "is_quantum_predicate (adjoint (exexH_k 0) * P * exexH_k 0)"
    using qp_close_under_unitary_operator[OF _ unitary_exhadamard_on_i[of 0]] tensor_P_dim 0 by auto
  then have "\<turnstile>\<^sub>p {adjoint (exexH_k 0) * P * exexH_k 0} SKIP {adjoint (exexH_k 0) * P * exexH_k 0}"
    using hoare_partial.intros(1) by auto
  moreover have "\<turnstile>\<^sub>p {adjoint (exexH_k 0) * P * exexH_k 0} Utrans (tensor_P (hadamard_on_i 0) (1\<^sub>m K)) {P}"
    using hoare_partial.intros(2) 0 by auto
  ultimately have "\<turnstile>\<^sub>p {adjoint (exexH_k 0) * P * exexH_k 0} SKIP;; Utrans (tensor_P (hadamard_on_i 0) (1\<^sub>m K)) {P}"
    using hoare_partial.intros(3) qp 0 by auto
  then show ?case using qp by auto
next
  case (Suc k)
  have h1: "\<turnstile>\<^sub>p 
    {adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K))} 
    Utrans (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) 
    {P}"
    using hoare_partial.intros Suc by auto
  have qp: "is_quantum_predicate (adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)))"
    apply (subst qp_close_under_unitary_operator)
    subgoal using ps2_P.ptensor_mat_carrier ps2_P_d0 by auto
    subgoal unfolding ps2_P.ptensor_mat_def apply (subst partial_state.tensor_mat_unitary ) 
      subgoal unfolding partial_state.d1_def partial_state.dims1_def ps2_P.nths_vars1' ps2_P.dims1_def d_vars1 using hadamard_on_i_dim Suc by auto
      subgoal unfolding partial_state.d2_def partial_state.dims2_def ps2_P.nths_vars2' ps2_P.dims2_def using dims_vars2 by auto
      using unitary_hadamard_on_i unitary_one Suc by auto
    using Suc by auto
  then have h2: "\<turnstile>\<^sub>p 
    {adjoint (exexH_k k) * (adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K))) * exexH_k k} 
    hadamard_n (Suc k)
    {adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K))}"
    using Suc by auto
  have "(tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * exexH_k k
    = (tensor_P (hadamard_on_i (Suc k) * (exH_k k)) (1\<^sub>m K * (1\<^sub>m K)))"
    apply (subst ps2_P.ptensor_mat_mult)
    subgoal using hadamard_on_i_dim ps2_P_d1 Suc by auto
    subgoal using exH_k_dim ps2_P_d1 Suc by auto
    using ps2_P_d2 by auto
  also have "\<dots> = exexH_k (Suc k)" using mult_exH_k_left Suc by auto
  finally have eq1: "(tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * exexH_k k = exexH_k (Suc k)".
  then have eq2: "adjoint (exexH_k k) * adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) = adjoint (exexH_k (Suc k))"
    apply (subst adjoint_mult[symmetric, of _ d d _ d])
    subgoal using tensor_P_dim by auto
    using exexH_k_dim Suc by auto
  have dP: "P \<in> carrier_mat d d" using is_quantum_predicate_def Suc by auto
  moreover have dH: "exexH_k k \<in> carrier_mat d d" using exexH_k_dim Suc by auto
  moreover have dHi: "tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K) \<in> carrier_mat d d" using tensor_P_dim by auto
  ultimately have eq3: "adjoint (exexH_k k) * (adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * exexH_k k
    = (adjoint (exexH_k k) * adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K))) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K) * exexH_k k)"
    by (mat_assoc d)
  show ?case apply (subst hadamard_n.simps) 
    apply (subst hoare_partial.intros(3)[of _ "adjoint (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K)) * P * (tensor_P (hadamard_on_i (Suc k)) (1\<^sub>m K))"])
    subgoal using qp_close_after_exexH_k[of P "Suc k"] Suc by auto
    subgoal using qp by auto
    subgoal using Suc by auto
    subgoal using h2[simplified eq3 eq1 eq2] by auto
    using h1 by auto
qed

lemma qp_pre:
  "is_quantum_predicate (tensor_P pre (proj_k 0))"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "tensor_P pre (proj_k 0) \<in> carrier_mat d d" using tensor_P_dim by auto
  interpret st: partial_state dims vars1 .
  have d1: "st.d1 = N" unfolding st.d1_def st.dims1_def using d_vars1 by auto
  have d2: "st.d2 = K" unfolding st.d2_def st.dims2_def nths_uminus_vars1 dims_vars2 by auto
  show "positive (tensor_P pre (proj_k 0))"
    unfolding ps2_P.ptensor_mat_def ps2_P_dims0  ps2_P_vars1' 
    apply (subst st.tensor_mat_positive)
    subgoal unfolding pre_def using outer_prod_dim ket_pre_def d1 by auto
    subgoal unfolding proj_k_def using outer_prod_dim ket_k_def d2 by auto
    subgoal using positive_pre by auto
    using positive_proj_k[of 0] K_gt_0 by auto
  show "tensor_P pre (proj_k 0) \<le>\<^sub>L 1\<^sub>m d"
    unfolding ps2_P.ptensor_mat_def ps2_P_dims0  ps2_P_vars1' 
    apply (subst st.tensor_mat_le_one)
    subgoal using pre_def ket_pre_def outer_prod_dim d1 by auto
    subgoal using proj_k_def K_gt_0 ket_k_def outer_prod_dim d2 by auto
    using d1 d2  K_gt_0 outer_prod_dim positive_pre positive_proj_k pre_le_one proj_k_le_one by auto
qed

lemma qp_init_post:
  "is_quantum_predicate (tensor_P proj_psi (proj_k 0))"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "tensor_P proj_psi (proj_k 0) \<in> carrier_mat d d" using tensor_P_dim by auto
  interpret st: partial_state dims vars1 .
  have d1: "st.d1 = N" unfolding st.d1_def st.dims1_def using d_vars1 by auto
  have d2: "st.d2 = K" unfolding st.d2_def st.dims2_def nths_uminus_vars1 dims_vars2 by auto
  show "positive (tensor_P proj_psi (proj_k 0))"
    unfolding ps2_P.ptensor_mat_def ps2_P_dims0  ps2_P_vars1' 
    apply (subst st.tensor_mat_positive)
    subgoal unfolding proj_psi_def using outer_prod_dim \<psi>_def d1 by auto
    subgoal unfolding proj_k_def using outer_prod_dim ket_k_def d2 by auto
    subgoal using positive_proj_psi by auto
    using positive_proj_k[of 0] K_gt_0 by auto
  show "tensor_P proj_psi (proj_k 0) \<le>\<^sub>L 1\<^sub>m d"
    unfolding ps2_P.ptensor_mat_def ps2_P_dims0  ps2_P_vars1' 
    apply (subst st.tensor_mat_le_one)
    subgoal using proj_psi_def outer_prod_dim d1 by auto
    subgoal using proj_k_def K_gt_0 ket_k_def outer_prod_dim d2 by auto
    using d1 d2  K_gt_0 outer_prod_dim positive_proj_psi positive_proj_k proj_psi_le_one proj_k_le_one by auto
qed

lemma tensor_P_adjoint_left_right:
  assumes "m1 \<in> carrier_mat N N" and "m2 \<in> carrier_mat K K" and "m3 \<in> carrier_mat N N" and "m4 \<in> carrier_mat K K"
  shows "adjoint (tensor_P m1 m2) * tensor_P m3 m4 * tensor_P m1 m2 = tensor_P (adjoint m1 * m3 * m1) (adjoint m2 * m4 * m2)"
proof -
  have eq1: "adjoint (tensor_P m1 m2) = tensor_P (adjoint m1) (adjoint m2)"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_adjoint)
    using ps_P_d1 ps_P_d2 assms by auto
  have eq2: "adjoint (tensor_P m1 m2) * tensor_P m3 m4 = tensor_P (adjoint m1 * m3) (adjoint m2 * m4)"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_mult)
    using ps_P_d1 ps_P_d2 assms eq1 unfolding ps2_P.ptensor_mat_def by (auto simp add: adjoint_dim)
  have eq3: "tensor_P (adjoint m1 * m3) (adjoint m2 * m4) * (tensor_P m1 m2) = tensor_P (adjoint m1 * m3 * m1) (adjoint m2 * m4 * m2)"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_mult[of "adjoint m1 * m3"])
    using ps_P_d1 ps_P_d2 assms by (auto simp add: adjoint_dim)
  show ?thesis using eq1 eq2 eq3 by auto
qed

abbreviation exH_n where
  "exH_n \<equiv> exH_k (n - 1)"

lemma hoare_triple_init:
  "\<turnstile>\<^sub>p 
   {tensor_P pre (proj_k 0)} 
   hadamard_n n
   {tensor_P proj_psi (proj_k 0)}"
proof -
  have h: "\<turnstile>\<^sub>p 
   {adjoint (exexH_k (n - 1)) * (tensor_P proj_psi (proj_k 0)) * (exexH_k (n - 1))} 
   hadamard_n n
   {tensor_P proj_psi (proj_k 0)}"
    using hoare_hadamard_n[OF qp_init_post, of "n - 1"] qp_init_post n by auto
  have "adjoint (exexH_k (n - 1)) * tensor_P proj_psi (proj_k 0) * exexH_k (n - 1) =
        tensor_P (adjoint exH_n * proj_psi * exH_n) (adjoint (1\<^sub>m K) * proj_k 0 * 1\<^sub>m K)"
    unfolding exexH_k.simps
    apply (subst tensor_P_adjoint_left_right)
    using exH_k_dim proj_psi_def \<psi>_def  proj_k_def ket_k_def n by (auto)
  moreover have "adjoint exH_n * proj_psi * exH_n = pre"
    unfolding proj_psi_def pre_def
    apply (subst outer_prod_left_right_mat[of _ N _ N _ N _ N])
    subgoal using \<psi>_def by auto
    subgoal using exH_k_dim n by (simp add: adjoint_dim)
    subgoal using exH_k_dim n by simp
    apply (subst (1 2) hermitian_exH_n[simplified hermitian_def])
    apply (subst (1 2) exH_k_mult_psi_is_pre)
    by auto
  moreover have "adjoint (1\<^sub>m K) * (proj_k 0) * (1\<^sub>m K) = proj_k 0"
    apply (subst adjoint_one) using proj_k_dim[of 0] K_gt_0 by auto
  ultimately have "adjoint (exexH_k (n - 1)) * tensor_P proj_psi (proj_k 0) * exexH_k (n - 1) = tensor_P pre (proj_k 0)"
    by auto
  with h show ?thesis by auto
qed

text \<open>Hoare triples of while loop\<close>

definition proj_psi_l where
  "proj_psi_l l = proj (psi_l l)"

lemma positive_psi_l:
  "k < K \<Longrightarrow> positive (proj_psi_l k)"
  unfolding proj_psi_l_def
  apply (subst positive_same_outer_prod)
  using psi_l_dim by auto

lemma hermitian_proj_psi_l:
  "k < K \<Longrightarrow> hermitian (proj_psi_l k)"
  using positive_psi_l positive_is_hermitian by auto

definition P' where
  "P' = tensor_P (proj_psi_l R) (proj_k R)"

lemma proj_psi_l_dim:
  "proj_psi_l l \<in> carrier_mat N N"
  unfolding proj_psi_l_def using psi_l_def by auto

definition Q :: "complex mat" where
  "Q = matrix_sum d (\<lambda>l. tensor_P (proj_psi_l l) (proj_k l)) R"

lemma psi_l_le_id:
  shows "proj_psi_l l \<le>\<^sub>L 1\<^sub>m N"
proof -
  have "inner_prod (psi_l l) (psi_l l) = 1"
    using inner_psi_l by auto
  then show ?thesis using outer_prod_le_one psi_l_def proj_psi_l_def by auto
qed

lemma positive_proj_psi_l:
  shows "positive (proj_psi_l l)"
  using positive_same_outer_prod proj_psi_l_def psi_l_dim by auto

definition proj_fst_k :: "nat \<Rightarrow> complex mat" where
  "proj_fst_k k = mat K K (\<lambda>(i, j). if (i = j \<and> i < k) then 1 else 0)"

lemma hermitian_proj_fst_k:
  "adjoint (proj_fst_k k) = proj_fst_k k"
  by (auto simp add: proj_fst_k_def adjoint_eval)

lemma proj_fst_k_is_projection:
  "proj_fst_k k * proj_fst_k k = proj_fst_k k"
  by (auto simp add: proj_fst_k_def scalar_prod_def sum_only_one_neq_0)

lemma positive_proj_fst_k:
  "positive (proj_fst_k k)"
proof -
  have "(proj_fst_k k) * adjoint (proj_fst_k k) = (proj_fst_k k)"
    using hermitian_proj_fst_k proj_fst_k_is_projection by auto
  then have "\<exists>M. M * adjoint M = (proj_fst_k k)" by auto
  then show ?thesis apply (subst positive_if_decomp) using proj_fst_k_def by auto
qed

lemma proj_fst_k_le_one:
  "proj_fst_k k \<le>\<^sub>L 1\<^sub>m K"
proof -
  define M where "M l = mat K K (\<lambda>(i, j). if (i = j \<and> i \<ge> l) then (1::complex) else 0)" for l
  have eq: "1\<^sub>m K - proj_fst_k k = M k" unfolding M_def proj_fst_k_def
    apply (rule eq_matI) by auto
  have "M k * M k = M k" unfolding M_def
    apply (rule eq_matI) apply (simp add: scalar_prod_def)
      apply (subst sum_only_one_neq_0[of _ j]) by auto
  moreover have "adjoint (M k) = M k" unfolding M_def
    apply (rule eq_matI) by (auto simp add: adjoint_eval)
  ultimately have "M k * adjoint (M k) = M k" by auto
  then have "\<exists>M. M * adjoint M = 1\<^sub>m K - proj_fst_k k" using eq by auto
  then have "positive (1\<^sub>m K - proj_fst_k k)" 
    apply (subst positive_if_decomp) using proj_fst_k_def by auto
  then show ?thesis unfolding lowner_le_def using proj_fst_k_def by auto
qed

lemma sum_proj_k:
  assumes "m \<le> K"
  shows "matrix_sum K (\<lambda>k. proj_k k) m = proj_fst_k m"
proof -
  have "m \<le> K \<Longrightarrow> matrix_sum K (\<lambda>k. proj_k k) m = mat K K (\<lambda>(i, j). if (i = j \<and> i < m) then 1 else 0)" for m
  proof (induct m)
    case 0
    then show ?case apply simp apply (rule eq_matI) by auto
  next
    case (Suc m)
    then have m: "m < K" by auto
    then have m': "m \<le> K" by auto
    have "matrix_sum K proj_k (Suc m) = proj_k m + matrix_sum K proj_k m" by simp
    also have "\<dots> = mat K K (\<lambda>(i, j). if (i = j \<and> i < (Suc m)) then 1 else 0)"
      unfolding proj_k_mat[OF m] Suc(1)[OF m'] apply (rule eq_matI) by auto
    finally show ?case by auto
  qed
  then show ?thesis unfolding proj_fst_k_def using assms by auto
qed

lemma proj_psi_proj_k_le_exproj_k:
  shows "tensor_P (proj_psi_l k) (proj_k l) \<le>\<^sub>L tensor_P (1\<^sub>m N) (proj_k l)"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_positive_le) 
  subgoal using proj_psi_l_def psi_l_dim ps_P_d1 by auto
  subgoal using proj_k_def ket_k_def ps_P_d2 by auto
  subgoal using positive_proj_psi_l by auto
  subgoal using positive_same_outer_prod proj_k_def ket_k_def by auto
  subgoal using psi_l_le_id by auto
  apply (subst lowner_le_refl[of _ K]) by (auto simp add: proj_k_def ket_k_def)

definition Q1 :: "complex mat" where
  "Q1 = matrix_sum d (\<lambda>l. tensor_P (proj_psi'_l l) (proj_k l)) R"

lemma tensor_P_left_right_partial1:
  assumes "m1 \<in> carrier_mat N N" and "m2 \<in> carrier_mat N N" and "m3 \<in> carrier_mat K K" and "m4 \<in> carrier_mat N N"
  shows "tensor_P m1 (1\<^sub>m K) * tensor_P m2 m3 * tensor_P m4 (1\<^sub>m K) = tensor_P (m1 * m2 * m4) m3"
proof -
  have "tensor_P m1 (1\<^sub>m K) * tensor_P m2 m3 = tensor_P (m1 * m2) m3"
    unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_mult[symmetric])
    using assms ps_P_d1 ps_P_d2 by auto
  moreover have "tensor_P (m1 * m2) m3 * tensor_P m4 (1\<^sub>m K) = tensor_P (m1 * m2 * m4) m3"
    unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_mult[symmetric])
    using assms ps_P_d1 ps_P_d2 by auto
  ultimately show ?thesis by auto
qed

lemma tensor_P_left_right_partial2:
  assumes "m1 \<in> carrier_mat K K" and "m2 \<in> carrier_mat K K" and "m3 \<in> carrier_mat N N" and "m4 \<in> carrier_mat K K"
  shows "tensor_P (1\<^sub>m N) m1 * tensor_P m3 m2 * tensor_P (1\<^sub>m N) m4 = tensor_P m3 (m1 * m2 * m4)"
proof -
  have "tensor_P (1\<^sub>m N) m1 * tensor_P m3 m2 = tensor_P m3 (m1 * m2)"
    unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_mult[symmetric])
    using assms ps_P_d1 ps_P_d2 by auto
  moreover have "tensor_P m3 (m1 * m2) * tensor_P (1\<^sub>m N) m4 = tensor_P m3 (m1 * m2 * m4)"
    unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_mult[symmetric])
    using assms ps_P_d1 ps_P_d2 by auto
  ultimately show ?thesis by auto
qed

lemma matrix_sum_mult_left_right:
  fixes A B :: "complex mat"
  assumes dg: "(\<And>k. k < l \<Longrightarrow> g k \<in> carrier_mat m m) "
    and dA: "A \<in> carrier_mat m m" and dB: "B \<in> carrier_mat m m"
  shows "matrix_sum m (\<lambda>k. A * g k * B) l = A * matrix_sum m g l * B"
proof -
  have eq: "A * matrix_sum m g l = matrix_sum m (\<lambda>k. A * g k) l" 
    using matrix_sum_distrib_left assms by auto
  have "A * matrix_sum m g l * B = matrix_sum m (\<lambda>k. A * g k * B) l"
    apply (subst eq)
    using matrix_sum_mult_right[of l "\<lambda>k. A * g k"] assms by auto
  then show ?thesis by auto
qed

lemma mat_O_split:
  "mat_O = 1\<^sub>m N - 2 \<cdot>\<^sub>m proj_O"
  apply (rule eq_matI)
  unfolding mat_O_def proj_O_def by auto

lemma mat_O_mult_psi'_l:
  "mat_O *\<^sub>v (psi'_l l) = psi_l l"
proof -
  have "mat_O *\<^sub>v (psi'_l l) = mat_O *\<^sub>v ((alpha_l l) \<cdot>\<^sub>v \<alpha>) - mat_O *\<^sub>v ((beta_l l) \<cdot>\<^sub>v \<beta>)"
    unfolding psi'_l_def apply (subst mult_minus_distrib_mat_vec)
    using mat_O_dim \<alpha>_dim \<beta>_dim by auto
  also have "\<dots> = (alpha_l l) \<cdot>\<^sub>v (mat_O *\<^sub>v  \<alpha>) - (beta_l l) \<cdot>\<^sub>v (mat_O *\<^sub>v \<beta>)"
    using mult_mat_vec_smult_vec_assoc[of mat_O N N] mat_O_dim \<alpha>_dim \<beta>_dim by auto
  also have "\<dots> = (alpha_l l) \<cdot>\<^sub>v \<alpha> - (beta_l l) \<cdot>\<^sub>v (- \<beta>)"
    using mat_O_mult_alpha mat_O_mult_beta by auto
  also have "\<dots> = (alpha_l l) \<cdot>\<^sub>v \<alpha> + (beta_l l) \<cdot>\<^sub>v \<beta>"
    by auto
  finally show ?thesis unfolding psi_l_def by auto
qed

lemma mat_O_times_Q1:
  "adjoint (tensor_P mat_O (1\<^sub>m K)) * Q1 * (tensor_P mat_O (1\<^sub>m K)) = Q"
proof -
  let ?m1 = "tensor_P mat_O (1\<^sub>m K)"
  have eq:"adjoint ?m1 = ?m1"
    unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_adjoint)
      apply (auto simp add: mat_O_dim ps_P_d1 ps_P_d2)
    by (simp add: hermitian_mat_O[unfolded hermitian_def] hermitian_one[unfolded hermitian_def])
  {
    fix l
    let ?m2 = "tensor_P (proj_psi'_l l) (proj_k l)"
    have "?m1 * ?m2 * ?m1 = tensor_P (mat_O * (proj_psi'_l l) * mat_O) (proj_k l)"
      apply (subst tensor_P_left_right_partial1)
      using mat_O_dim proj_psi'_dim proj_k_dim by auto
    moreover have "mat_O * (proj_psi'_l l) * mat_O = outer_prod (psi_l l) (psi_l l)"
      unfolding proj_psi'_l_def apply (subst outer_prod_left_right_mat[of _ N _ N  _ N _ N])
      using psi'_l_dim mat_O_dim mat_O_mult_psi'_l hermitian_mat_O[unfolded hermitian_def] by auto
    ultimately have "?m1 * ?m2 * ?m1 = tensor_P (proj_psi_l l) (proj_k l)" unfolding proj_psi_l_def by auto
  }
  note p1 = this
  have "adjoint (tensor_P mat_O (1\<^sub>m K)) * Q1 * (tensor_P mat_O (1\<^sub>m K)) = ?m1 * Q1 * ?m1"
    using eq by auto
  also have "\<dots> = matrix_sum d (\<lambda>l. ?m1 * (tensor_P (proj_psi'_l l) (proj_k l)) * ?m1) R"
    unfolding Q1_def
    apply (subst matrix_sum_mult_left_right) using tensor_P_dim by auto
  also have "\<dots> = Q"
    unfolding Q_def using p1 by auto
  finally show ?thesis by auto
qed

definition Q2 where
  "Q2 = matrix_sum d (\<lambda>l. tensor_P (proj_psi_l (l + 1)) (proj_k l)) R"

lemma Q2_dim:
  "Q2 \<in> carrier_mat d d"
  unfolding Q2_def apply (subst matrix_sum_dim) using tensor_P_dim by auto

lemma Q2_le_one:
  "Q2 \<le>\<^sub>L 1\<^sub>m d" 
proof -
  have leq: "Q2 \<le>\<^sub>L matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) R"
    unfolding Q2_def
    apply (subst lowner_le_matrix_sum)
    subgoal using tensor_P_dim by auto
    subgoal using tensor_P_dim by auto
    using proj_psi_proj_k_le_exproj_k by auto
  have "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) R
      = tensor_P (1\<^sub>m N) (matrix_sum K proj_k R)"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_matrix_sum2[simplified ps_P_d ps_P_d2])
    subgoal using ps_P_d1 by auto
    using proj_k_dim by auto
  also have "\<dots> = tensor_P (1\<^sub>m N) (proj_fst_k R)" using sum_proj_k K by auto
  also have "\<dots> \<le>\<^sub>L tensor_P (1\<^sub>m N) (1\<^sub>m K)" unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive_le)
    subgoal using ps_P_d1 by auto
    subgoal using ps_P_d2 proj_fst_k_def by auto
    subgoal using positive_one by auto
    subgoal using positive_proj_fst_k  by auto
    subgoal using lowner_le_refl[of "1\<^sub>m N" N] by auto
    using proj_fst_k_le_one by auto
  also have "\<dots> = 1\<^sub>m d" unfolding ps2_P.ptensor_mat_def
    using ps_P.tensor_mat_id ps_P_d1 ps_P_d2 ps_P_d by auto
  finally have leq2: "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) R \<le>\<^sub>L 1\<^sub>m d" by auto
  have ds: "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) R \<in> carrier_mat d d"
    apply (subst matrix_sum_dim) using tensor_P_dim by auto
  then show ?thesis using leq leq2 lowner_le_trans[OF Q2_dim ds, of "1\<^sub>m d"] by auto
qed

lemma qp_Q2:
  "is_quantum_predicate Q2"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "Q2 \<in> carrier_mat d d" unfolding Q2_def 
    apply (subst matrix_sum_dim) using tensor_P_dim by auto
next
  show "positive Q2" unfolding Q2_def
    apply (subst matrix_sum_positive)
    subgoal using tensor_P_dim by auto
    subgoal for k unfolding ps2_P.ptensor_mat_def 
      apply (subst ps_P.tensor_mat_positive)
      subgoal using proj_psi_l_def psi_l_dim ps_P_d1 by auto
      subgoal using proj_k_dim ps_P_d2 K by auto
      subgoal using positive_proj_psi_l by auto
       using positive_proj_k K by auto
    by auto
next
  show "Q2 \<le>\<^sub>L 1\<^sub>m d" using Q2_le_one by auto
qed

lemma pre_mat:
  "pre = mat N N (\<lambda>(i, j). if i = j \<and> i = 0 then 1 else 0)"
  apply (rule eq_matI)
  subgoal for i j  unfolding pre_def apply (subst index_outer_prod[OF ket_pre_dim ket_pre_dim])
      apply simp_all
    unfolding ket_pre_def by auto
  using outer_prod_dim[OF ket_pre_dim ket_pre_dim, folded pre_def] by auto

lemma mat_Ph_split:
  "mat_Ph = 2 \<cdot>\<^sub>m pre - 1\<^sub>m N"
  unfolding mat_Ph_def pre_mat
  apply (rule eq_matI) by auto
  
lemma H_Ph_H:
  "exexH_k (n-1) * tensor_P mat_Ph (1\<^sub>m K) * exexH_k (n - 1) = 2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d"
  unfolding mat_Ph_split exexH_k.simps
  apply (subst tensor_P_left_right_partial1)
  subgoal using exH_k_dim[of "n - 1"] n by auto
  subgoal using pre_dim by auto
  subgoal by auto
proof -
  have eq1: "exH_n * exH_n = 1\<^sub>m N"
    using unitary_exH_k[of "n - 1"]
    unfolding unitary_def inverts_mat_def
    using n hermitian_exH_n[simplified hermitian_def] exH_n_dim by auto
  have eq2: "exH_n * pre * exH_n = proj_psi"
    unfolding pre_def proj_psi_def
    apply (subst outer_prod_left_right_mat[of _ N _ N _ N _ N])
    subgoal using ket_pre_dim by auto
    subgoal using exH_n_dim by auto
    apply (subst hermitian_exH_n[simplified hermitian_def])
    using exH_k_mult_pre_is_psi by auto
  have eq3: "exH_n * (2 \<cdot>\<^sub>m pre) * exH_n = 2 \<cdot>\<^sub>m (exH_n * pre * exH_n)"
    using pre_dim exH_n_dim by (mat_assoc N)
  have "exH_n * (2 \<cdot>\<^sub>m pre - 1\<^sub>m N) * exH_n = exH_n * (2 \<cdot>\<^sub>m pre) * exH_n - exH_n * exH_n"
    using pre_dim exH_n_dim apply (mat_assoc N) by auto
  also have "\<dots> = 2 \<cdot>\<^sub>m (exH_n * pre * exH_n) - 1\<^sub>m N"
    using eq1 eq3 by auto
  finally have eq4: "exH_n * (2 \<cdot>\<^sub>m pre - 1\<^sub>m N) * exH_n = 2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N" using eq2 by auto
  show "tensor_P (exH_n * (2 \<cdot>\<^sub>m pre - 1\<^sub>m N) * exH_n) (1\<^sub>m K) = 2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d"
    unfolding eq4 unfolding ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_minus1)
    unfolding ps_P_d1 ps_P_d2 apply (auto simp add: proj_psi_dim)
    apply (subst ps_P.tensor_mat_scale1)
    unfolding ps_P_d1 ps_P_d2 apply (auto simp add: proj_psi_dim)
    apply (subst ps_P.tensor_mat_id[simplified ps_P_d1 ps_P_d2 ps_P_d]) by auto
qed

lemma hermitian_proj_psi_minus_1:
  "hermitian (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N)"
  unfolding hermitian_def
  apply (subst adjoint_minus[of _ N N])
    apply (auto simp add: proj_psi_dim)
  apply (subst adjoint_scale)
  using hermitian_proj_psi[simplified hermitian_def] hermitian_def adjoint_one by auto

lemma unitary_proj_psi_minus_1:
  "unitary (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N)"
proof -
  have a: "adjoint (2 \<cdot>\<^sub>m proj_psi) = 2 \<cdot>\<^sub>m proj_psi" 
    apply (subst adjoint_scale) using hermitian_proj_psi[simplified hermitian_def] by simp
  have eq: "adjoint (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) = 2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N"
    apply (subst adjoint_minus) using proj_psi_dim a adjoint_one by auto
  have "(2 \<cdot>\<^sub>m proj_psi) * (2 \<cdot>\<^sub>m proj_psi) = 4 \<cdot>\<^sub>m (proj_psi * proj_psi)"
    using proj_psi_dim by auto
  also have "\<dots> = 4 \<cdot>\<^sub>m proj_psi" using proj_psi_is_projection by auto
  finally have sq: "(2 \<cdot>\<^sub>m proj_psi) * (2 \<cdot>\<^sub>m proj_psi) = 4 \<cdot>\<^sub>m proj_psi".
  have l: "(2 \<cdot>\<^sub>m proj_psi) * (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) = 4 \<cdot>\<^sub>m proj_psi - (2 \<cdot>\<^sub>m proj_psi)"
    apply (subst mult_minus_distrib_mat) using proj_psi_dim sq by auto

  have "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) * adjoint (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N)
    = (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) * (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N)" using eq by auto
  also have "\<dots> = (2 \<cdot>\<^sub>m proj_psi) * (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) - 2 \<cdot>\<^sub>m proj_psi + 1\<^sub>m N"
    apply (subst minus_mult_distrib_mat[of _ N N]) using proj_psi_dim by auto
  also have "\<dots> = 4 \<cdot>\<^sub>m proj_psi - (2 \<cdot>\<^sub>m proj_psi) - 2 \<cdot>\<^sub>m proj_psi + 1\<^sub>m N"
    using l by auto
  also have "\<dots> = 1\<^sub>m N" using proj_psi_dim by auto
  finally have "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) * adjoint (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) = 1\<^sub>m N".
  then show ?thesis unfolding unitary_def inverts_mat_def using proj_psi_dim by auto
qed

lemma proj_psi_minus_1_mult_psi'_l:
  "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi'_l l = psi_l (l + 1)"
proof -
  have eq1: "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi'_l l = 2 \<cdot>\<^sub>m proj_psi *\<^sub>v psi'_l l - psi'_l l"
    apply (subst minus_mult_distrib_mat_vec)
    using psi'_l_dim proj_psi'_dim proj_psi_dim by auto
  have eq2: "2 \<cdot>\<^sub>m proj_psi *\<^sub>v (psi'_l l) = 2 \<cdot>\<^sub>v (proj_psi *\<^sub>v (psi'_l l))"
    apply (subst smult_mat_mult_mat_vec_assoc) 
    using proj_psi_dim psi'_l_dim by auto
  have "proj_psi *\<^sub>v (psi'_l l) = inner_prod \<psi> (psi'_l l) \<cdot>\<^sub>v \<psi>"
    unfolding proj_psi_def
    apply (subst outer_prod_mult_vec[of _ N _ N])
    using \<psi>_dim psi'_l_dim  by auto
  also have "\<dots> = ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) \<cdot>\<^sub>v \<psi>"
    using psi_inner_psi'_l by auto
  finally have "proj_psi *\<^sub>v (psi'_l l) = ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) \<cdot>\<^sub>v \<psi>" by auto
  then have eq3: "2 \<cdot>\<^sub>v (proj_psi *\<^sub>v (psi'_l l)) = 2 * ((alpha_l l) * ccos (\<theta> / 2) - (beta_l l) * csin (\<theta> / 2)) \<cdot>\<^sub>v \<psi>" by auto
  then show "(2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) *\<^sub>v (psi'_l l) = psi_l (l + 1)"
    using eq1 eq2 eq3 psi_l_Suc_l_derive by simp
qed

lemma proj_psi_minus_1_mult_psi_Suc_l:
  "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi_l (l + 1) = psi'_l l"
proof -
  have id: "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) * (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) = 1\<^sub>m N"
    using unitary_proj_psi_minus_1 unfolding unitary_def hermitian_proj_psi_minus_1[simplified hermitian_def]
    unfolding inverts_mat_def by auto
  have "(2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi_l (l + 1) = (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v ((2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi'_l l)"
    using proj_psi_minus_1_mult_psi'_l by auto
  also have "\<dots> = ((2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) * (2 \<cdot>\<^sub>m proj_psi - 1\<^sub>m N) *\<^sub>v psi'_l l)"
    apply (subst assoc_mult_mat_vec) using proj_psi_dim psi'_l_dim by auto
  also have "\<dots> = psi'_l l" using psi'_l_dim id by auto
  finally show ?thesis by auto
qed

lemma exproj_psi_minus_1_tensor:
  "(2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K)) - 1\<^sub>m d = tensor_P (2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) (1\<^sub>m K)"
  unfolding ps2_P.ptensor_mat_def
  apply (subst ps_P.tensor_mat_id[symmetric, simplified ps_P_d])
  apply (auto simp add: ps_P_d1 ps_P_d2)
  apply (subst ps_P.tensor_mat_scale1[symmetric])
    apply (auto simp add: ps_P_d1 ps_P_d2 proj_psi_dim)
  apply (subst ps_P.tensor_mat_minus1)
  by (auto simp add: ps_P_d1 ps_P_d2 proj_psi_dim)

lemma unitary_exproj_psi_minus_1:
  "unitary (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d)"
  unfolding exproj_psi_minus_1_tensor
  unfolding ps2_P.ptensor_mat_def 
  apply (subst ps_P.tensor_mat_unitary)
  using ps_P_d1 ps_P_d2 unitary_proj_psi_minus_1 unitary_one by auto

lemma proj_psi_minus_1_Q2:
  "adjoint (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) * Q2 * (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) = Q1"
proof -
  have eq1: "adjoint (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) = 2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d"
    apply (subst adjoint_minus[of _ d d])
    subgoal using tensor_P_dim[of proj_psi] by auto
    subgoal by auto
    apply (subst adjoint_one) apply (subst adjoint_scale) 
    using hermitian_exproj_psi[simplified hermitian_def] by auto
  let ?m1 = "tensor_P (2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) (1\<^sub>m K)"
  {
    fix l
    let ?m2 = "tensor_P (proj_psi_l (l + 1)) (proj_k l)"
    have 121: "?m1 * ?m2 * ?m1 
        = tensor_P ((2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) * (proj_psi_l (l + 1)) * (2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)))
            (proj_k l)"
      apply (subst tensor_P_left_right_partial1)
      using proj_psi_dim proj_psi_l_dim proj_k_dim by auto
    have "(2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) * (proj_psi_l (l + 1)) * (2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N))
      = outer_prod ((2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) *\<^sub>v (psi_l (l + 1))) ((2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) *\<^sub>v (psi_l (l + 1)))"
      unfolding proj_psi_l_def apply (subst outer_prod_left_right_mat[of _ N _ N _ N _ N])
      using proj_psi_dim psi_l_dim hermitian_proj_psi_minus_1[simplified hermitian_def] by auto
    also have "\<dots> = outer_prod (psi'_l l) (psi'_l l)"
      using proj_psi_minus_1_mult_psi_Suc_l by auto
    finally have "(2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) * (proj_psi_l (l + 1)) * (2 \<cdot>\<^sub>m proj_psi - (1\<^sub>m N)) 
      = outer_prod (psi'_l l) (psi'_l l)".
    then have "?m1 * ?m2 * ?m1 = tensor_P (proj_psi'_l l) (proj_k l)"
      using 121 proj_psi'_l_def by auto
  }
  note p1 = this
  have "adjoint (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) * Q2 * (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d)
    = (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) * Q2 * (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d)"
    using eq1 by auto
  also have "\<dots> = matrix_sum d
    (\<lambda>l. (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d) * tensor_P (proj_psi_l (l + 1)) (proj_k l) * (2 \<cdot>\<^sub>m tensor_P proj_psi (1\<^sub>m K) - 1\<^sub>m d))
    R" unfolding Q2_def apply (subst matrix_sum_mult_left_right)
    using tensor_P_dim by auto
  also have "\<dots> = matrix_sum d (\<lambda>l. tensor_P (proj_psi'_l l) (proj_k l)) R"
    using p1 exproj_psi_minus_1_tensor by auto
  also have "\<dots> = Q1" unfolding Q1_def by auto
  finally show ?thesis using eq1 by auto
qed

lemma qp_Q1:
  "is_quantum_predicate Q1"
  unfolding proj_psi_minus_1_Q2[symmetric]
  apply (subst qp_close_under_unitary_operator)
  using tensor_P_dim unitary_exproj_psi_minus_1 qp_Q2 by auto

lemma qp_Q:
  "is_quantum_predicate Q"
proof -
  have u: "unitary (tensor_P mat_O (1\<^sub>m K))"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_unitary)
    subgoal unfolding ps_P_d1 mat_O_def by auto
    subgoal unfolding ps_P_d2 by auto
    subgoal using unitary_mat_O by auto
    using unitary_one by auto
  then show ?thesis using tensor_P_dim qp_Q1 
    using qp_close_under_unitary_operator[OF tensor_P_dim u qp_Q1]
    by (simp add: mat_O_times_Q1 )
qed

lemma hoare_triple_D1:
  "\<turnstile>\<^sub>p 
   {Q} 
   Utrans_P vars1 mat_O
   {Q1}"
  unfolding Utrans_P_is_tensor_P1
    mat_O_times_Q1[symmetric]
  apply (subst hoare_partial.intros(2))
  using qp_Q1 by auto

lemma hoare_triple_D2:
  "\<turnstile>\<^sub>p 
   {Q1}
   hadamard_n n ;;
   Utrans_P vars1 mat_Ph ;;
   hadamard_n n 
   {Q2}"
proof -
  let ?H = "exexH_k (n - 1)"
  let ?Ph = "tensor_P mat_Ph (1\<^sub>m K)"
  let ?O = "tensor_P mat_O (1\<^sub>m K)"
  have h1: "\<turnstile>\<^sub>p 
    {adjoint ?H * Q2 * ?H} 
    hadamard_n n 
    {Q2}"
    using hoare_hadamard_n[OF qp_Q2, of "n - 1"] n by auto
  have qp1: "is_quantum_predicate ((adjoint ?H) * Q2 * ?H)"
    using qp_close_under_unitary_operator unitary_exexH_k n exexH_k_dim qp_Q2 by auto
  then have h2: "\<turnstile>\<^sub>p 
    {adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph} 
    Utrans_P vars1 mat_Ph 
    {adjoint ?H * Q2 * ?H}"
    using qp1 Utrans_P_is_tensor_P1 hoare_partial.intros by auto
  have qp2: "is_quantum_predicate (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph)"
    using qp_close_under_unitary_operator[of "tensor_P mat_Ph (1\<^sub>m K)"] ps2_P.ptensor_mat_carrier ps2_P_d0 unitary_ex_mat_Ph qp1 by auto
  then have  h3: "\<turnstile>\<^sub>p 
    {adjoint ?H * (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph) * ?H} 
    hadamard_n n 
    {adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph}"
    using hoare_hadamard_n[OF qp2, of "n - 1"] n by auto
  have qp3: "is_quantum_predicate (adjoint ?H * (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph) * ?H)"
    using qp_close_under_unitary_operator[of "?H"] exexH_k_dim unitary_exexH_k qp2 n by auto
  have h4: "\<turnstile>\<^sub>p 
    {adjoint ?H * (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph) * ?H} 
    hadamard_n n ;;
    Utrans_P vars1 mat_Ph
    {adjoint ?H * Q2 * ?H}"
    using h2 h3 qp1 qp2 qp3 hoare_partial.intros by auto
  then have h5: "\<turnstile>\<^sub>p 
   {adjoint ?H * (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph) * ?H}
   hadamard_n n ;;
   Utrans_P vars1 mat_Ph ;;
   hadamard_n n 
   {Q2}"
    using h1 qp_Q2 qp3 qp1 hoare_partial.intros(3)[OF qp3 qp1 qp_Q2 h4 h1] by auto

  have "adjoint ?H * (adjoint ?Ph * (adjoint ?H * Q2 * ?H) * ?Ph) * ?H =
        adjoint (?H * ?Ph * ?H) * Q2 * (?H * ?Ph * ?H)"
    apply (mat_assoc d) using exexH_k_dim n tensor_P_dim Q2_dim by auto
  also have "\<dots> = Q1" using H_Ph_H proj_psi_minus_1_Q2 by auto
  finally show ?thesis using h5 by auto 
qed

definition exM0 where
  "exM0 = tensor_P (1\<^sub>m N) M0"

lemma M0_mult_ket_k_R:
  "M0 *\<^sub>v ket_k R = ket_k R"
  apply (rule eq_vecI)
  unfolding M0_def ket_k_def
  by (auto simp add: scalar_prod_def sum_only_one_neq_0)

lemma exP0_P':
  "adjoint exM0 * P' * exM0 = P'"
proof -
  have eq: "adjoint exM0 = exM0"
    unfolding exM0_def ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_adjoint)
    unfolding ps_P_d1 ps_P_d2 using M0_dim adjoint_one hermitian_M0[unfolded hermitian_def] by auto
  have eq2: "M0 * (proj_k R) * M0 = (proj_k R)"
    unfolding proj_k_def
    apply (subst outer_prod_left_right_mat[of _ K _ K _ K _ K])
    unfolding hermitian_M0[unfolded hermitian_def] M0_mult_ket_k_R
    using ket_k_dim M0_dim by auto
  show ?thesis unfolding eq unfolding exM0_def P'_def
    apply (subst tensor_P_left_right_partial2)
    using M0_dim proj_k_dim eq2 proj_psi_l_dim by auto
qed
 
definition exM1 where
  "exM1 = tensor_P (1\<^sub>m N) M1"

lemma M1_mult_ket_k:
  assumes "k < R"
  shows "M1 *\<^sub>v ket_k k = ket_k k"
  apply (rule eq_vecI)
  unfolding M1_def ket_k_def
  by (auto simp add: scalar_prod_def assms R sum_only_one_neq_0)

lemma exP1_Q:
  "adjoint exM1 * Q * exM1 = Q"
proof -
  have eq: "adjoint exM1 = exM1"
    unfolding exM1_def ps2_P.ptensor_mat_def 
    apply (subst ps_P.tensor_mat_adjoint)
    unfolding ps_P_d1 ps_P_d2 using M1_dim adjoint_one hermitian_M1[unfolded hermitian_def] by auto
  {
    fix k assume k: "k < R"
    let ?m = "tensor_P (proj_psi_l k) (proj_k k)"
    have "exM1 * ?m * exM1 = tensor_P (proj_psi_l k) (M1 * (proj_k k) * M1)"
      unfolding exM1_def apply (subst tensor_P_left_right_partial2)
      using M1_dim proj_k_dim proj_psi_l_dim by auto
    also have "\<dots> = tensor_P (proj_psi_l k) (outer_prod (M1 *\<^sub>v ket_k k) (M1 *\<^sub>v ket_k k))"
      unfolding proj_k_def apply (subst outer_prod_left_right_mat[of _ K _ K _ K _ K])
      unfolding hermitian_M1[unfolded hermitian_def]
      using ket_k_dim M1_dim by auto
    finally have "exM1 * ?m * exM1 = ?m" unfolding proj_k_def using k M1_mult_ket_k by auto
  }
  note p1 = this
  have "adjoint exM1 * Q * exM1 = exM1 * Q * exM1" using eq by auto
  also have "\<dots> = matrix_sum d (\<lambda>k. exM1 * (tensor_P (proj_psi_l k) (proj_k k)) * exM1) R"
    unfolding Q_def
    apply (subst matrix_sum_mult_left_right)
    using tensor_P_dim exM1_def by auto
  also have "\<dots> = matrix_sum d (\<lambda>k. tensor_P (proj_psi_l k) (proj_k k)) R"
    apply (subst matrix_sum_cong)
    using p1 by auto
  finally show ?thesis using Q_def by auto
qed
         
lemma qp_P':
  "is_quantum_predicate P'"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "P' \<in> carrier_mat d d" unfolding P'_def using tensor_P_dim by auto
  show "positive P'" unfolding P'_def ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive)
        apply (auto simp add: ps_P_d1 ps_P_d2 proj_O_dim proj_k_dim)
    using proj_psi_l_dim positive_proj_psi_l positive_proj_k K by auto
  show "P' \<le>\<^sub>L 1\<^sub>m d" unfolding P'_def ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_le_one[simplified ps_P_d])
    by (auto simp add: ps_P_d1 ps_P_d2 proj_psi_l_dim K proj_k_dim positive_proj_psi_l positive_proj_k proj_k_le_one psi_l_le_id)
qed

lemma P'_add_Q:
  "P' + Q = matrix_sum d (\<lambda>l. tensor_P (proj_psi_l l) (proj_k l)) (R + 1)"
  apply simp unfolding P'_def Q_def by auto

lemma positive_Qk:
  "positive (tensor_P (proj_psi_l l) (proj_k l))"
  unfolding ps2_P.ptensor_mat_def 
  apply (subst ps_P.tensor_mat_positive)
  unfolding ps_P_d1 ps_P_d2
  using proj_psi_l_dim proj_k_dim positive_proj_psi_l positive_proj_k by auto

lemma P'_Q_dim:
  "P' + Q \<in> carrier_mat d d"
  unfolding P'_add_Q
  apply (subst matrix_sum_dim)
  using tensor_P_dim by auto

lemma P'_add_Q_le_one:
  "P' + Q \<le>\<^sub>L 1\<^sub>m d" 
proof -
  have leq: "matrix_sum d (\<lambda>l. tensor_P (proj_psi_l l) (proj_k l)) (R + 1) 
      \<le>\<^sub>L matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) (R + 1)"
    unfolding Q2_def
    apply (subst lowner_le_matrix_sum)
    subgoal using tensor_P_dim by auto
    subgoal using tensor_P_dim by auto
    using proj_psi_proj_k_le_exproj_k by auto
  have "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) (R + 1)
      = tensor_P (1\<^sub>m N) (matrix_sum K proj_k (R + 1))"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_matrix_sum2[simplified ps_P_d ps_P_d2])
    subgoal using ps_P_d1 by auto
    using proj_k_dim by auto
  also have "\<dots> = tensor_P (1\<^sub>m N) (proj_fst_k (R + 1))" using sum_proj_k[of "R + 1"] K by auto
  also have "\<dots> \<le>\<^sub>L tensor_P (1\<^sub>m N) (1\<^sub>m K)" unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive_le)
    subgoal using ps_P_d1 by auto
    subgoal using ps_P_d2 proj_fst_k_def by auto
    subgoal using positive_one by auto
    subgoal using positive_proj_fst_k  by auto
    subgoal using lowner_le_refl[of "1\<^sub>m N" N] by auto
    using proj_fst_k_le_one by auto
  also have "\<dots> = 1\<^sub>m d" unfolding ps2_P.ptensor_mat_def
    using ps_P.tensor_mat_id ps_P_d1 ps_P_d2 ps_P_d by auto
  finally have leq2: "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) (R + 1) \<le>\<^sub>L 1\<^sub>m d" by auto
  have ds: "matrix_sum d (\<lambda>k. tensor_P (1\<^sub>m N) (proj_k k)) (R + 1) \<in> carrier_mat d d"
    apply (subst matrix_sum_dim) using tensor_P_dim by auto
  then show ?thesis 
   using leq leq2 lowner_le_trans[OF P'_Q_dim ds, of "1\<^sub>m d"] unfolding P'_add_Q by auto
qed

lemma qp_P'_Q:
  "is_quantum_predicate (P' + Q)"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "P' + Q \<in> carrier_mat d d"
    unfolding P'_add_Q apply (subst matrix_sum_dim)
    using tensor_P_dim by auto
  show "positive (P' + Q)" unfolding P'_add_Q
    apply (subst matrix_sum_positive)
    using tensor_P_dim positive_Qk by auto
  show " P' + Q \<le>\<^sub>L 1\<^sub>m d" using P'_add_Q_le_one by auto
qed

lemma Q2_leq_lemma:
  "tensor_P (1\<^sub>m N) (mat_incr K) * Q2 * adjoint (tensor_P (1\<^sub>m N) (mat_incr K)) \<le>\<^sub>L P' + Q"
proof -
  have ad: "adjoint (tensor_P (1\<^sub>m N) (mat_incr K)) = tensor_P (1\<^sub>m N) (adjoint (mat_incr K))"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_adjoint)
    using ps_P_d1 ps_P_d2 mat_incr_dim adjoint_one by auto
  let ?m1 = "tensor_P (1\<^sub>m N) (mat_incr K)"
  let ?m3 = "tensor_P (1\<^sub>m N) (adjoint (mat_incr K))"
  {
    fix l assume "l < R"
    then have "l < K - 1" using K by auto
    then have m: "(mat_incr K) *\<^sub>v (ket_k l) = (ket_k (l + 1))"
      using mat_incr_mult_ket_k by auto
    let ?m2 = "tensor_P (proj_psi_l (l + 1)) (proj_k l)"
    have eq: "?m1 * ?m2 * ?m3 = tensor_P (proj_psi_l (l + 1)) ((mat_incr K) * (proj_k l) * adjoint (mat_incr K))"
      apply (subst tensor_P_left_right_partial2)
      using proj_k_dim proj_psi_l_dim mat_incr_dim adjoint_dim[OF mat_incr_dim] by auto
    have "(mat_incr K) * (proj_k l) * adjoint (mat_incr K) = outer_prod ((mat_incr K) *\<^sub>v (ket_k l)) ((mat_incr K) *\<^sub>v (ket_k l))"
      unfolding proj_k_def apply (subst outer_prod_left_right_mat[of _ K _ K _ K _ K])
      using ket_k_dim mat_incr_dim adjoint_dim[OF mat_incr_dim] adjoint_adjoint[of "mat_incr K"] by auto
    also have "\<dots> = proj_k (l + 1)" unfolding proj_k_def using m by auto
    finally have "?m1 * ?m2 * ?m3 = tensor_P (proj_psi_l (l + 1)) (proj_k (l + 1))" using eq by auto
  }
  note p1 = this
  have "?m1 * Q2 * ?m3
    = matrix_sum d (\<lambda>l. ?m1 * (tensor_P (proj_psi_l (l + 1)) (proj_k l)) * ?m3) R"
    unfolding Q2_def apply(subst matrix_sum_mult_left_right)
    using tensor_P_dim by auto
  also have "\<dots> = matrix_sum d (\<lambda>l. tensor_P (proj_psi_l (l + 1)) (proj_k (l + 1))) R"
    apply (subst matrix_sum_cong) using p1 by auto
  finally have eq1: "?m1 * Q2 * ?m3 = matrix_sum d (\<lambda>l. tensor_P (proj_psi_l (l + 1)) (proj_k (l + 1))) R" (is "_=?r") . 
  have eq2: "P' + Q = tensor_P (proj_psi_l 0) (proj_k 0) + ?r"
    unfolding P'_add_Q
    apply (subst matrix_sum_Suc_remove_head) using tensor_P_dim by auto
  have "tensor_P (proj_psi_l 0) (proj_k 0) + ?r \<le>\<^sub>L P' + Q"
    unfolding eq2[symmetric] apply (subst lowner_le_refl) using P'_Q_dim by auto
  moreover have "positive (tensor_P (proj_psi_l 0) (proj_k 0))"
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_positive)
    unfolding ps_P_d1 ps_P_d2 using proj_psi_l_dim proj_k_dim positive_proj_psi_l positive_proj_k by auto
  moreover have "matrix_sum d (\<lambda>l. tensor_P (proj_psi_l (l + 1)) (proj_k (l + 1))) R \<in> carrier_mat d d"
    apply (subst matrix_sum_dim) using tensor_P_dim by auto
  ultimately have "?r \<le>\<^sub>L P' + Q"
    apply (subst add_positive_le_reduce2[of ?r d "tensor_P (proj_psi_l 0) (proj_k 0)" "P' + Q"])
    using tensor_P_dim P'_Q_dim by auto
  then show ?thesis using eq1 ad by auto
qed

lemma Q2_leq:
  "Q2 \<le>\<^sub>L adjoint (tensor_P (1\<^sub>m N) (mat_incr K)) * (P' + Q) * tensor_P (1\<^sub>m N) (mat_incr K)"
proof -
  let ?m1 = "tensor_P (1\<^sub>m N) (mat_incr K)"
  let ?m2 = "adjoint (tensor_P (1\<^sub>m N) (mat_incr K))"
  have "?m1 * ?m2 = 1\<^sub>m d"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_adjoint)
    unfolding ps_P_d1 ps_P_d2 apply (auto simp add: mat_incr_dim adjoint_one)
    apply (subst ps_P.tensor_mat_mult[symmetric])
    unfolding ps_P_d1 ps_P_d2 apply (auto simp add: mat_incr_dim adjoint_dim mat_incr_mult_adjoint_mat_incr)
    using ps_P.tensor_mat_id ps_P_d ps_P_d1 ps_P_d2 by auto
  then have inv: "?m2 * ?m1 = 1\<^sub>m d"
    using mat_mult_left_right_inverse[of ?m1 d ?m2] 
        tensor_P_dim adjoint_dim by auto
  have d: "?m1 * Q2 * ?m2 \<in> carrier_mat d d" using tensor_P_dim adjoint_dim[OF tensor_P_dim] Q2_dim by fastforce
  have le: "?m2 * (?m1 * Q2 * ?m2) * ?m1 \<le>\<^sub>L ?m2 * (P' + Q) * ?m1" (is "lowner_le ?l ?r")
    apply (subst lowner_le_keep_under_measurement[of _ d])
    using Q2_leq_lemma tensor_P_dim P'_Q_dim d by auto
  have "?l = (?m2 * ?m1) * Q2 * (?m2 * ?m1)"
    apply (mat_assoc d) using tensor_P_dim Q2_dim by auto
  also have "\<dots> = 1\<^sub>m d * Q2 * 1\<^sub>m d" using inv by auto
  also have "\<dots> = Q2" using Q2_dim by auto
  finally have eq: "?l = Q2".
  show ?thesis using eq le by auto
qed

lemma hoare_triple_D3:
  "\<turnstile>\<^sub>p 
   {Q2}
   Utrans_P vars2 (mat_incr K)
   {adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1}"
  unfolding exP0_P' exP1_Q 
proof -
  let ?m = "tensor_P (1\<^sub>m N) (mat_incr K)"
  have h1: "\<turnstile>\<^sub>p 
    {adjoint ?m * (P' + Q) * ?m} 
    Utrans ?m
    {P' + Q}"
    using qp_P'_Q hoare_partial.intros by auto
  have qp: "is_quantum_predicate (adjoint ?m * (P' + Q) * ?m)"
    using qp_close_under_unitary_operator tensor_P_dim qp_P'_Q unitary_exmat_incr by auto
  then have "\<turnstile>\<^sub>p 
    {Q2} 
    Utrans ?m
    {P' + Q}"
    using hoare_partial.intros(6)[OF qp_Q2 qp_P'_Q qp qp_P'_Q] Q2_leq h1 lowner_le_refl[OF P'_Q_dim] by auto
  moreover have "Utrans ?m = Utrans_P vars2 (mat_incr K)"
    apply (subst Utrans_P_is_tensor_P2) unfolding mat_incr_def by auto
  ultimately show "\<turnstile>\<^sub>p {Q2} Utrans_P vars2 (mat_incr K) {P' + Q}" by auto
qed

lemma qp_D3_post:
  "is_quantum_predicate (adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1)"
  unfolding exP0_P' exP1_Q using qp_P'_Q by auto

lemma hoare_triple_D:
  "\<turnstile>\<^sub>p 
   {Q} 
   D
   {adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1}"
proof -
  have "\<turnstile>\<^sub>p {Q1} hadamard_n n;; (Utrans_P vars1 mat_Ph;; hadamard_n n) {Q2}"
    using  well_com_hadamard_n well_com_mat_Ph hoare_triple_D2 qp_Q1 qp_Q2 by (auto simp add: hoare_patial_seq_assoc)
  then have "\<turnstile>\<^sub>p {Q} Utrans_P vars1 mat_O;; (hadamard_n n;; (Utrans_P vars1 mat_Ph;; hadamard_n n)) {Q2}"
    using hoare_triple_D1 qp_Q qp_Q1 qp_Q2 hoare_partial.intros(3) by auto
  moreover have "well_com (Utrans_P vars1 mat_Ph;; hadamard_n n)" using well_com_hadamard_n well_com_mat_Ph by auto
  ultimately have "\<turnstile>\<^sub>p {Q} (Utrans_P vars1 mat_O;; hadamard_n n);; (Utrans_P vars1 mat_Ph;; hadamard_n n) {Q2}"
    using well_com_hadamard_n well_com_mat_O qp_Q qp_Q2 by (auto simp add: hoare_patial_seq_assoc)
  moreover have "well_com (Utrans_P vars1 mat_O;; hadamard_n n)"
    using well_com_mat_O well_com_hadamard_n by auto
  ultimately have "\<turnstile>\<^sub>p {Q} Utrans_P vars1 mat_O;; hadamard_n n;; Utrans_P vars1 mat_Ph;; hadamard_n n {Q2}"
    using well_com_hadamard_n well_com_mat_Ph qp_Q qp_Q2 by (auto simp add: hoare_patial_seq_assoc)
  with qp_Q qp_Q2 qp_D3_post hoare_triple_D3 show "\<turnstile>\<^sub>p 
   {Q} 
   D
   {adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1}"
    unfolding D_def using hoare_partial.intros(3) by auto
qed

lemma psi_is_psi_l0:
  "\<psi> = psi_l 0"
  unfolding \<psi>_eq psi_l_def alpha_l_def beta_l_def by auto

lemma proj_psi_is_proj_psi_l0:
  "proj_psi = proj_psi_l 0"
  unfolding proj_psi_def psi_is_psi_l0 proj_psi_l_def by auto

lemma lowner_le_Q:
  "tensor_P proj_psi (proj_k 0) \<le>\<^sub>L adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1"
proof -
  let ?r = "matrix_sum d (\<lambda>l. tensor_P (proj_psi_l l) (proj_k l)) (R + 1)"
  let ?l = "tensor_P (proj_psi_l 0) (proj_k 0)"
  have eq: "?r = ?l + matrix_sum d (\<lambda>l. tensor_P (proj_psi_l (l + 1)) (proj_k (l + 1))) R" (is "_ = _ + ?s")
    apply (subst matrix_sum_Suc_remove_head)
    using tensor_P_dim by auto
  have d: "?s \<in> carrier_mat d d"
    apply (subst matrix_sum_dim) using tensor_P_dim by auto
  have pt: "positive (tensor_P (proj_psi_l l) (proj_k l))" for l
    unfolding ps2_P.ptensor_mat_def apply (subst ps_P.tensor_mat_positive)
    unfolding ps_P_d1 ps_P_d2 using proj_psi_l_dim proj_k_dim positive_proj_psi_l positive_proj_k by auto
  have ps: "positive ?s"
    apply (subst matrix_sum_positive) 
    subgoal using tensor_P_dim by auto
    using pt by auto
  have "?l \<le>\<^sub>L ?r"
    unfolding eq
    apply (subst add_positive_le_reduce1[of ?l d ?s])
    subgoal using tensor_P_dim by auto
    subgoal using d by auto
    subgoal using tensor_P_dim d by auto
    subgoal using ps by auto
     apply (subst lowner_le_refl[of _ d])
    using tensor_P_dim d by auto
  then show ?thesis unfolding exP0_P' exP1_Q P'_add_Q proj_psi_is_proj_psi_l0  by auto
qed

lemma hoare_triple_while:
  "\<turnstile>\<^sub>p 
   {adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1} 
   While_P vars2 M0 M1 D
   {P'}"
proof -
  let ?m = "\<lambda>(n::nat). if n = 0 then mat_extension dims vars2 M0 else
                       if n = 1 then mat_extension dims vars2 M1 else undefined"
  have dM0: "M0 \<in> carrier_mat K K" unfolding M0_def by auto
  have dM1: "M1 \<in> carrier_mat K K" unfolding M1_def by auto
  have m0: "?m 0 = exM0" apply (simp) unfolding exM0_def ps2_P.ptensor_mat_def mat_ext_vars2[OF dM0] by auto
  have m1: "?m 1 = exM1" unfolding exM1_def ps2_P.ptensor_mat_def mat_ext_vars2[OF dM1] by auto
  have "\<turnstile>\<^sub>p {Q} D {adjoint (?m 0) * P' * (?m 0) + adjoint (?m 1) * Q * (?m 1)}"
    using hoare_triple_D m0 m1 by auto
  then show ?thesis unfolding While_P_def using qp_D3_post qp_P' hoare_partial.intros(5)[OF qp_P' qp_Q, of D ?m] m0 m1 by auto
qed

lemma R_and_a_half_\<theta>:
  "(R + 1/2) * \<theta> = pi / 2"
  using R \<theta>_neq_0 by auto

lemma psi_lR_is_beta:
  "psi_l R = \<beta>"
  unfolding psi_l_def alpha_l_def beta_l_def R_and_a_half_\<theta> by auto

lemma post_mult_beta:
  "post *\<^sub>v \<beta> = \<beta>"
  by (auto simp add: post_def \<beta>_def scalar_prod_def sum_only_one_neq_0)

lemma post_mult_post:
  "post * post = post"
  by (auto simp add: post_def scalar_prod_def sum_only_one_neq_0)

lemma post_mult_proj_psi_lR:
  "post * proj_psi_l R = proj_psi_l R"
proof -
  let ?R = "proj_psi_l R"
  have "post * ?R = post * ?R * 1\<^sub>m N"
    using post_dim proj_psi_l_dim[of R] by auto
  also have "\<dots> = outer_prod (post *\<^sub>v psi_l R) ((1\<^sub>m N) *\<^sub>v psi_l R)"
    unfolding proj_psi_l_def
    apply (subst outer_prod_left_right_mat[of _ N _ N _ N _ N])
    by (auto simp add: psi_l_dim post_dim adjoint_one)
  also have "\<dots> = ?R" unfolding proj_psi_l_def unfolding psi_lR_is_beta unfolding post_mult_beta
    using \<beta>_dim by auto
  finally show "post * ?R = ?R".
qed

lemma proj_psi_lR_mult_post:
  "proj_psi_l R * post = proj_psi_l R"
proof -
  let ?R = "proj_psi_l R"
  have "?R * post = 1\<^sub>m N * ?R * post"
    using post_dim proj_psi_l_dim[of R] by auto
  also have "\<dots> = outer_prod ((1\<^sub>m N) *\<^sub>v psi_l R) (post *\<^sub>v psi_l R)"
    unfolding proj_psi_l_def
    apply (subst outer_prod_left_right_mat[of _ N _ N _ N _ N])
    by (auto simp add: psi_l_dim post_dim hermitian_post[unfolded hermitian_def])
  also have "\<dots> = ?R" unfolding proj_psi_l_def unfolding psi_lR_is_beta unfolding post_mult_beta
    using \<beta>_dim by auto
  finally show "?R * post = ?R".
qed

lemma proj_psi_lR_mult_proj_psi_lR:
  "proj_psi_l R * proj_psi_l R = proj_psi_l R"
  unfolding proj_psi_l_def psi_lR_is_beta
  apply (subst outer_prod_mult_outer_prod[of _ N _ N _ _ N])
  by (auto simp add: \<beta>_inner)

lemma proj_psi_lR_le_post:
  "proj_psi_l R \<le>\<^sub>L post"
proof -
  let ?R = "proj_psi_l R"
  let ?s = "post - ?R"
  have eq1: "post * (post - ?R) = post - ?R"
    apply (subst mult_minus_distrib_mat[of _ N N _ N])
      apply (auto simp add: post_dim proj_psi_l_dim[of R])
    using post_mult_post post_mult_proj_psi_lR by auto
  have eq2: "?R * (post - ?R) = 0\<^sub>m N N"
    apply (subst mult_minus_distrib_mat[of _ N N _ N])
      apply (auto simp add: post_dim proj_psi_l_dim[of R])
    unfolding proj_psi_lR_mult_post proj_psi_lR_mult_proj_psi_lR 
    using proj_psi_l_dim[of R] by auto
  have "adjoint ?s = ?s"
    apply (subst adjoint_minus[of _ N N])
    using post_dim proj_psi_l_dim hermitian_post hermitian_proj_psi_l K by (auto simp add: hermitian_def)
  then have "?s * adjoint ?s = ?s * ?s" by auto
  also have "\<dots> = post * (post - ?R) - ?R * (post - ?R)"
    using post_dim proj_psi_l_dim[of R] by (mat_assoc N)
  also have "\<dots> = post - ?R"
    unfolding eq1 eq2 using post_dim proj_psi_l_dim[of R] by auto
  finally have "?s * adjoint ?s = ?s". 
  then have "\<exists>M. M * adjoint M = ?s" by auto
  then have "positive ?s" apply (subst positive_if_decomp[of ?s N]) using post_dim proj_psi_l_dim[of R] by auto
  then show ?thesis unfolding lowner_le_def using post_dim proj_psi_l_dim[of R] by auto
qed

lemma P'_le_post_R:
  "P' \<le>\<^sub>L (tensor_P post (proj_k R))"
proof -
  let ?r = "tensor_P post (proj_k R)"
  have "?r - P' = tensor_P (post - proj_psi_l R) (proj_k R)"
    unfolding P'_def ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_minus1)
    unfolding ps_P_d1 ps_P_d2
    using post_dim proj_psi_l_dim proj_k_dim by auto
  moreover have "positive (tensor_P (post - proj_psi_l R) (proj_k R))"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive)
    unfolding ps_P_d1 ps_P_d2 
    using proj_psi_lR_le_post[unfolded lowner_le_def]
      post_dim proj_psi_l_dim[of R] proj_k_dim positive_proj_k
    by auto
  ultimately show "P' \<le>\<^sub>L ?r"
    unfolding lowner_le_def P'_def
    using tensor_P_dim by auto
qed

lemma positive_post:
  "positive post"
proof -
  have ad: "adjoint post = post" using hermitian_post[unfolded hermitian_def] by auto
  then have "post * adjoint post = post"
    unfolding ad post_mult_post by auto
  then have "\<exists>M. M * adjoint M = post" by auto
  then show ?thesis using positive_if_decomp post_dim by auto
qed

lemma lowner_le_P':
  "P' \<le>\<^sub>L tensor_P post (1\<^sub>m K)"
proof -
  let ?r = "tensor_P post (1\<^sub>m K)"
  let ?m = "tensor_P post (proj_k R)"
  have "?m \<le>\<^sub>L ?r"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive_le)
    unfolding ps_P_d1 ps_P_d2
    using post_dim proj_k_dim positive_post positive_proj_k
      lowner_le_refl[of post] proj_k_le_one by auto
  then show "P' \<le>\<^sub>L ?r"
    using lowner_le_trans[of P' d ?m ?r] P'_le_post_R
    unfolding P'_def using tensor_P_dim by auto
qed

lemma post_mult_testNk:
  assumes "f k"
  shows "post * (testN k) = testN k"
  using assms by (auto simp add: post_def testN_def scalar_prod_def sum_only_one_neq_0)

lemma post_mult_testNk_neg:
  assumes "\<not> f k"
  shows "post * testN k = 0\<^sub>m N N"
  using assms by (auto simp add: post_def testN_def scalar_prod_def sum_only_one_neq_0)

lemma testN_post1:
  "f k \<Longrightarrow> adjoint (testN k) * post * testN k = testN k"
  apply (subst assoc_mult_mat[of _ N N _ N _ N])
     apply (auto simp add: adjoint_dim testN_dim post_dim)
  apply (subst post_mult_testNk, simp)
  unfolding hermitian_testN[unfolded hermitian_def]
  using testN_mult_testN by auto

lemma testN_post2:
  "\<not> f k \<Longrightarrow> adjoint (testN k) * post * testN k = 0\<^sub>m N N"
  apply (subst assoc_mult_mat[of _ N N _ N _ N])
     apply (auto simp add: adjoint_dim testN_dim post_dim)
  apply (subst post_mult_testNk_neg, simp)
  unfolding hermitian_testN[unfolded hermitian_def]
  using testN_dim[of k] by auto

definition post_fst_k :: "nat \<Rightarrow> complex mat" where
  "post_fst_k k = mat N N (\<lambda>(i, j). if (i = j \<and> f i \<and> i < k) then 1 else 0)"

lemma post_fst_kN:
  "post_fst_k N = post"
  unfolding post_fst_k_def post_def by auto

lemma post_fst_k_Suc:
  "f i \<Longrightarrow> post_fst_k (Suc i) = testN i + post_fst_k i"
  apply (rule eq_matI)
  unfolding post_fst_k_def testN_def by auto

lemma post_fst_k_Suc_neg:
  "\<not> f i \<Longrightarrow> post_fst_k (Suc i) = post_fst_k i"
  apply (rule eq_matI)
  unfolding post_fst_k_def
    apply auto
  using less_antisym by fastforce

lemma testN_sum:
  "matrix_sum N (\<lambda>k. adjoint (testN k) * post * testN k) N = post"
proof -
  have "m \<le> N \<Longrightarrow> matrix_sum N (\<lambda>k. adjoint (testN k) * post * testN k) m = post_fst_k m" for m
  proof (induct m)
    case 0
    then show ?case apply simp unfolding post_fst_k_def by auto
  next
    case (Suc m) 
    then have m: "m \<le> N" by auto
    show ?case
    proof (cases "f m")
      case True
      show ?thesis apply simp
        apply (subst testN_post1[OF True])
        apply (subst Suc(1)[OF m])
        using post_fst_k_Suc True by auto
    next
      case False
      show ?thesis apply simp
        apply (subst testN_post2[OF False])
        apply (subst Suc(1)[OF m])
        using post_fst_k_Suc_neg False post_fst_k_def by auto
    qed
  qed
  then show ?thesis using post_fst_kN by auto
qed

lemma tensor_P_testN_sum:
  "matrix_sum d (\<lambda>k. adjoint (tensor_P (testN k) (1\<^sub>m K)) * tensor_P post (1\<^sub>m K) * tensor_P (testN k) (1\<^sub>m K)) N =
   tensor_P post (1\<^sub>m K)"
proof -
  have eq: "adjoint (tensor_P (testN k) (1\<^sub>m K)) * tensor_P post (1\<^sub>m K) * tensor_P (testN k) (1\<^sub>m K) =
            tensor_P (adjoint (testN k) * post * (testN k)) (1\<^sub>m K)" for k
    apply (subst tensor_P_adjoint_left_right)
    subgoal unfolding testN_def by auto
    subgoal by auto
    subgoal using post_dim by auto
    using adjoint_one by auto
  moreover have "matrix_sum N (\<lambda>k. adjoint (testN k) * post * testN k) N = post"
    using testN_sum by auto
  show ?thesis unfolding eq
    apply (subst matrix_sum_tensor_P1)
    subgoal unfolding testN_def by auto
    subgoal by auto
    using testN_sum by auto
qed

lemma post_le_one:
  "post \<le>\<^sub>L 1\<^sub>m N"
proof -
  let ?s = "1\<^sub>m N - post"
  have eq1: "1\<^sub>m N * (1\<^sub>m N - post) = 1\<^sub>m N - post"
    apply (mat_assoc N) using post_dim by auto
  have eq2: "post * (1\<^sub>m N - post) = 0\<^sub>m N N"
    apply (subst mult_minus_distrib_mat[of _ N N])
    using post_dim by (auto simp add: post_mult_post)

  have "adjoint ?s = ?s" 
    apply (subst adjoint_minus)
      apply (auto simp add: post_dim adjoint_dim)
    using adjoint_one hermitian_post[unfolded hermitian_def] by auto
  then have "?s * adjoint ?s = ?s * ?s" by auto
  also have "\<dots> = 1\<^sub>m N * (1\<^sub>m N - post) - post * (1\<^sub>m N - post)"
    apply (mat_assoc N) using post_dim by auto
  also have "\<dots> = ?s" unfolding eq1 eq2 using post_dim by auto
  finally have "?s * adjoint ?s = ?s".
  then have "\<exists>M. M * adjoint M = ?s" by auto
  then have "positive ?s" apply (subst positive_if_decomp[of ?s N]) using post_dim by auto
  then show ?thesis unfolding lowner_le_def using post_dim by auto
qed

lemma qp_post:
  "is_quantum_predicate (tensor_P post (1\<^sub>m K))"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "tensor_P post (1\<^sub>m K) \<in> carrier_mat d d"
    using tensor_P_dim by auto
  show "positive (tensor_P post (1\<^sub>m K))"
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive)
    by (auto simp add: ps_P_d1 ps_P_d2 post_dim positive_post positive_one)
  show "tensor_P post (1\<^sub>m K) \<le>\<^sub>L 1\<^sub>m d"
    unfolding ps_P.tensor_mat_id[symmetric, unfolded ps_P_d ps_P_d1 ps_P_d2]
    unfolding ps2_P.ptensor_mat_def
    apply (subst ps_P.tensor_mat_positive_le)
    unfolding ps_P_d1 ps_P_d2 using post_dim positive_post positive_one post_le_one lowner_le_refl[of "1\<^sub>m K" K]
    by auto
qed

lemma hoare_triple_if:
  "\<turnstile>\<^sub>p 
   {tensor_P post (1\<^sub>m K)} 
   Measure_P vars1 N testN (replicate N SKIP)
   {tensor_P post (1\<^sub>m K)}"
proof -
  define M where "M = (\<lambda>n. mat_extension dims vars1 (testN n))"
  define Post where "Post = (\<lambda>(k::nat). tensor_P post (1\<^sub>m K))"
  have M: "M = (\<lambda>n. tensor_P (testN n) (1\<^sub>m K))"
    unfolding M_def using mat_ext_vars1 by auto
  have skip: "\<And>k. k < N \<Longrightarrow> (replicate N SKIP) ! k = SKIP" by simp
  have h: "\<And>k. k < N \<Longrightarrow> \<turnstile>\<^sub>p {Post k} replicate N SKIP ! k {tensor_P post (1\<^sub>m K)}"
    unfolding Post_def skip using qp_post hoare_partial.intros by auto
  moreover have "\<And>k. k < N \<Longrightarrow> is_quantum_predicate (Post k)" unfolding Post_def using qp_post by auto
  ultimately show ?thesis
    unfolding Measure_P_def apply (fold M_def) 
    using hoare_partial.intros(4)[of N Post "tensor_P post (1\<^sub>m K)" "replicate N SKIP" M]
    unfolding M Post_def using tensor_P_testN_sum qp_post by auto
qed

theorem grover_partial_deduct:
  "\<turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    Grover
   {tensor_P post (1\<^sub>m K)}"
  unfolding Grover_def
proof -
  have "\<turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    hadamard_n n
   {adjoint exM0 * P' * exM0 + adjoint exM1 * Q * exM1}"
    using hoare_partial.intros(6)[OF qp_pre qp_D3_post qp_pre qp_init_post]
    hoare_triple_init lowner_le_refl[OF tensor_P_dim] lowner_le_Q by auto
  then have "\<turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    hadamard_n n;;
    While_P vars2 M0 M1 D
   {P'}"
    using hoare_triple_while hoare_partial.intros(3) qp_pre qp_D3_post qp_P' by auto
  then have "\<turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    hadamard_n n;;
    While_P vars2 M0 M1 D
   {tensor_P post (1\<^sub>m K)}"
    using lowner_le_P' hoare_partial.intros(6)[OF qp_pre qp_post qp_pre qp_P'] 
      lowner_le_P' lowner_le_refl[OF tensor_P_dim] by auto
  then show " \<turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    hadamard_n n;;
    While_P vars2 M0 M1 D;;
    Measure_P vars1 N testN (replicate N SKIP)
   {tensor_P post (1\<^sub>m K)}"
    using hoare_triple_if qp_pre qp_post hoare_partial.intros(3) by auto
qed

theorem grover_partial_correct:
  "\<Turnstile>\<^sub>p
   {tensor_P pre (proj_k 0)}
    Grover
   {tensor_P post (1\<^sub>m K)}"
  using grover_partial_deduct well_com_Grover qp_pre qp_post hoare_partial_sound by auto
end

end
