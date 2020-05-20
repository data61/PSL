(*  Title:       Affine systems of ODEs
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Affine systems of ODEs \<close>

text \<open>Affine systems of ordinary differential equations (ODEs) are those whose vector 
fields are linear operators. Broadly speaking, if there are functions $A$ and $B$ such that the 
system of ODEs $X'\, t = f\, (X\, t)$ turns into $X'\, t = (A\, t)\cdot (X\, t)+(B\, t)$, then it
is affine. The end goal of this section is to prove that every affine system of ODEs has a unique 
solution, and to obtain a characterization of said solution. \<close>

theory MTX_Flows
  imports SQ_MTX "Hybrid_Systems_VCs.HS_ODEs"

begin


subsection \<open> Existence and uniqueness for affine systems \<close>

definition matrix_continuous_on :: "real set \<Rightarrow> (real \<Rightarrow> ('a::real_normed_algebra_1)^'n^'m) \<Rightarrow> bool" 
  where "matrix_continuous_on T A = (\<forall>t \<in> T. \<forall>\<epsilon> > 0. \<exists> \<delta> > 0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p \<le> \<epsilon>)"

lemma continuous_on_matrix_vector_multl:
  assumes "matrix_continuous_on T A"
  shows "continuous_on T (\<lambda>t. A t *v s)"
proof(rule continuous_onI, simp add: dist_norm)
  fix e t::real assume "0 < e" and "t \<in> T"
  let ?\<epsilon> = "e/(\<parallel>(if s = 0 then 1 else s)\<parallel>)"
  have "?\<epsilon> > 0"
    using \<open>0 < e\<close> by simp 
  then obtain \<delta> where dHyp: "\<delta> > 0 \<and> (\<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p \<le> ?\<epsilon>)"
    using assms \<open>t \<in> T\<close> unfolding dist_norm matrix_continuous_on_def by fastforce
  {fix \<tau> assume "\<tau> \<in> T" and "\<bar>\<tau> - t\<bar> < \<delta>"
    have obs: "?\<epsilon> * (\<parallel>s\<parallel>) = (if s = 0 then 0 else e)"
      by auto
    have "\<parallel>A \<tau> *v s - A t *v s\<parallel> = \<parallel>(A \<tau> - A t) *v s\<parallel>"
      by (simp add: matrix_vector_mult_diff_rdistrib)      
    also have "... \<le> (\<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p) * (\<parallel>s\<parallel>)"
      using norm_matrix_le_mult_op_norm by blast
    also have "... \<le> ?\<epsilon> * (\<parallel>s\<parallel>)"
      using dHyp \<open>\<tau> \<in> T\<close> \<open>\<bar>\<tau> - t\<bar> < \<delta>\<close> mult_right_mono norm_ge_zero by blast 
    finally have "\<parallel>A \<tau> *v s - A t *v s\<parallel> \<le> e"
      by (subst (asm) obs) (metis (mono_tags, hide_lams) \<open>0 < e\<close> less_eq_real_def order_trans)}
  thus "\<exists>d>0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < d \<longrightarrow> \<parallel>A \<tau> *v s - A t *v s\<parallel> \<le> e"
    using dHyp by blast
qed

lemma lipschitz_cond_affine:
  fixes A :: "real \<Rightarrow> 'a::real_normed_algebra_1^'n^'m" and T::"real set"
  defines "L \<equiv> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
  assumes "t \<in> T" and "bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
  shows "\<parallel>A t *v x - A t *v y\<parallel> \<le> L * (\<parallel>x - y\<parallel>)"
proof-
  have obs: "\<parallel>A t\<parallel>\<^sub>o\<^sub>p \<le> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
    apply(rule cSup_upper)
    using continuous_on_subset assms by (auto simp: dist_norm)
  have "\<parallel>A t *v x - A t *v y\<parallel> = \<parallel>A t *v (x - y)\<parallel>"
    by (simp add: matrix_vector_mult_diff_distrib)
  also have "... \<le> (\<parallel>A t\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x - y\<parallel>)"
    using norm_matrix_le_mult_op_norm by blast
  also have "... \<le> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T} * (\<parallel>x - y\<parallel>)"
    using obs mult_right_mono norm_ge_zero by blast 
  finally show "\<parallel>A t *v x - A t *v y\<parallel> \<le> L * (\<parallel>x - y\<parallel>)"
    unfolding assms .
qed

lemma local_lipschitz_affine:
  fixes A :: "real \<Rightarrow> 'a::real_normed_algebra_1^'n^'m"
  assumes "open T" and "open S" 
    and Ahyp: "\<And>\<tau> \<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> cball \<tau> \<epsilon>}"
  shows "local_lipschitz T S (\<lambda>t s. A t *v s + B t)"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp)
  fix s t assume "s \<in> S" and "t \<in> T"
  then obtain e1 e2 where "cball t e1 \<subseteq> T" and "cball s e2 \<subseteq> S" and "min e1 e2 > 0"
    using open_cballE[OF _ \<open>open T\<close>] open_cballE[OF _ \<open>open S\<close>] by force
  hence obs: "cball t (min e1 e2) \<subseteq> T"
    by auto
  let ?L = "Sup {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
  have "\<parallel>A t\<parallel>\<^sub>o\<^sub>p \<in> {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
    using \<open>min e1 e2 > 0\<close> by auto
  moreover have bdd: "bdd_above {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
    by (rule Ahyp, simp only: \<open>min e1 e2 > 0\<close>, simp_all add: \<open>t \<in> T\<close> obs)
  moreover have "Sup {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)} \<ge> 0"
    apply(rule order.trans[OF op_norm_ge_0[of "A t"]])
    by (rule cSup_upper[OF calculation])
  moreover have "\<forall>x\<in>cball s (min e1 e2) \<inter> S. \<forall>y\<in>cball s (min e1 e2) \<inter> S. 
    \<forall>\<tau>\<in>cball t (min e1 e2) \<inter> T. dist (A \<tau> *v x) (A \<tau> *v y) \<le> ?L * dist x y"
    apply(clarify, simp only: dist_norm, rule lipschitz_cond_affine)
    using \<open>min e1 e2 > 0\<close> bdd by auto
  ultimately show "\<exists>e>0. \<exists>L. \<forall>t\<in>cball t e \<inter> T. 0 \<le> L \<and> 
    (\<forall>x\<in>cball s e \<inter> S. \<forall>y\<in>cball s e \<inter> S. dist (A t *v x) (A t *v y) \<le> L * dist x y)"
    using \<open>min e1 e2 > 0\<close> by blast
qed

lemma picard_lindeloef_affine:
  fixes A :: "real \<Rightarrow> 'a::{banach,real_normed_algebra_1,heine_borel}^'n^'n"
  assumes Ahyp: "matrix_continuous_on T A"
      and "\<And>\<tau> \<epsilon>. \<tau> \<in> T \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. dist \<tau> t \<le> \<epsilon>}"
      and Bhyp: "continuous_on T B" and "open S" 
      and "t\<^sub>0 \<in> T" and Thyp: "open T" "is_interval T" 
    shows "picard_lindeloef (\<lambda> t s. A t *v s + B t) T S t\<^sub>0"
  apply (unfold_locales, simp_all add: assms, clarsimp)
   apply (rule continuous_on_add[OF continuous_on_matrix_vector_multl[OF Ahyp] Bhyp])
  by (rule local_lipschitz_affine) (simp_all add: assms)

lemma picard_lindeloef_autonomous_affine: 
  fixes A :: "'a::{banach,real_normed_field,heine_borel}^'n^'n"
  shows "picard_lindeloef (\<lambda> t s. A *v s + B) UNIV UNIV t\<^sub>0"
  using picard_lindeloef_affine[of _ "\<lambda>t. A" "\<lambda>t. B"] 
  unfolding matrix_continuous_on_def by (simp only: diff_self op_norm0, auto)

lemma picard_lindeloef_autonomous_linear:
  fixes A :: "'a::{banach,real_normed_field,heine_borel}^'n^'n"
  shows "picard_lindeloef (\<lambda> t. (*v) A) UNIV UNIV t\<^sub>0"
  using picard_lindeloef_autonomous_affine[of A 0] by force

lemmas unique_sol_autonomous_affine = picard_lindeloef.unique_solution[OF 
    picard_lindeloef_autonomous_affine _ _ funcset_UNIV UNIV_I _ _ funcset_UNIV UNIV_I]

lemmas unique_sol_autonomous_linear = picard_lindeloef.unique_solution[OF 
    picard_lindeloef_autonomous_linear _ _ funcset_UNIV UNIV_I _ _ funcset_UNIV UNIV_I]


subsection \<open> Flow for affine systems \<close>


subsubsection \<open> Derivative rules for square matrices \<close>

lemma has_derivative_exp_scaleRl[derivative_intros]:
  fixes f::"real \<Rightarrow> real" (* by Fabian Immler and Johannes Hölzl *)
  assumes "D f \<mapsto> f' at t within T"
  shows "D (\<lambda>t. exp (f t *\<^sub>R A)) \<mapsto> (\<lambda>h. f' h *\<^sub>R (exp (f t *\<^sub>R A) * A)) at t within T"
proof -
  have "bounded_linear f'" 
    using assms by auto
  then obtain m where obs: "f' = (\<lambda>h. h * m)"
    using real_bounded_linear by blast
  thus ?thesis
    using vector_diff_chain_within[OF _ exp_scaleR_has_vector_derivative_right] 
      assms obs by (auto simp: has_vector_derivative_def comp_def)
qed

lemma has_vderiv_on_exp_scaleRl:
  assumes "D f = f' on T"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) = (\<lambda>x. f' x *\<^sub>R exp (f x *\<^sub>R A) * A) on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  by (rule has_derivative_exp_scaleRl, auto simp: fun_eq_iff)

lemma vderiv_on_exp_scaleRlI[poly_derivatives]:
  assumes "D f = f' on T" and "g' = (\<lambda>x. f' x *\<^sub>R exp (f x *\<^sub>R A) * A)"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) = g' on T"
  using has_vderiv_on_exp_scaleRl assms by simp

lemma has_derivative_mtx_ith[derivative_intros]:
  fixes t::real and T :: "real set"
  defines "t\<^sub>0 \<equiv> netlimit (at t within T)"
  assumes "D A \<mapsto> (\<lambda>h. h *\<^sub>R A' t) at t within T"
  shows "D (\<lambda>t. A t $$ i) \<mapsto> (\<lambda>h. h *\<^sub>R A' t $$ i) at t within T"
  using assms unfolding has_derivative_def apply safe
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  apply(rule_tac F="\<lambda>\<tau>. (A \<tau> - A t\<^sub>0 - (\<tau> - t\<^sub>0) *\<^sub>R A' t) /\<^sub>R (\<parallel>\<tau> - t\<^sub>0\<parallel>)" in tendsto_zero_norm_bound)
  by (clarsimp, rule mult_left_mono, metis (no_types, lifting) norm_column_le_norm 
      sq_mtx_minus_ith sq_mtx_scaleR_ith) simp_all

lemmas has_derivative_mtx_vec_mult[derivative_intros] = 
  bounded_bilinear.FDERIV[OF bounded_bilinear_sq_mtx_vec_mult]

lemma vderiv_mtx_vec_mult_intro[poly_derivatives]:
  assumes "D u = u' on T" and "D A = A' on T"
      and "g = (\<lambda>t. A t *\<^sub>V u' t + A' t *\<^sub>V u t )"
    shows "D (\<lambda>t. A t *\<^sub>V u t) = g on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  apply(erule_tac x=x in ballE, simp_all)+
  apply(rule derivative_eq_intros(142))
  by (auto simp: fun_eq_iff mtx_vec_scaleR_commute pth_6 scaleR_mtx_vec_assoc)

lemmas has_vderiv_on_ivl_integral = ivl_integral_has_vderiv_on[OF vderiv_on_continuous_on]

declare has_vderiv_on_ivl_integral [poly_derivatives]

lemma has_derivative_mtx_vec_multl[derivative_intros]:
  assumes "\<And> i j. D (\<lambda>t. (A t) $$ i $ j) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) $$ i $ j) (at t within T)"
  shows "D (\<lambda>t. A t *\<^sub>V x) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) *\<^sub>V x) at t within T"
  unfolding sq_mtx_vec_mult_sum_cols
  apply(rule_tac f'1="\<lambda>i \<tau>. \<tau> *\<^sub>R  (x $ i *\<^sub>R \<c>\<o>\<l> i (A' t))" in derivative_eq_intros(10))
   apply(simp_all add: scaleR_right.sum)
  apply(rule_tac g'1="\<lambda>\<tau>. \<tau> *\<^sub>R \<c>\<o>\<l> i (A' t)" in derivative_eq_intros(4), simp_all add: mult.commute)
  using assms unfolding sq_mtx_col_def column_def apply(transfer, simp)
  apply(rule has_derivative_vec_lambda)
  by (simp add: scaleR_vec_def)

lemma continuous_on_mtx_vec_multr: "continuous_on S ((*\<^sub>V) A)"
  by transfer (simp add: matrix_vector_mult_linear_continuous_on)

\<comment> \<open>Automatically generated derivative rules from this subsubsection \<close>

thm derivative_eq_intros(140,141,142,143)


subsubsection \<open> Existence and uniqueness with square matrices \<close>

text \<open>Finally, we can use the @{term exp} operation to characterize the general solutions for affine 
systems of ODEs. We show that they satisfy the @{term "local_flow"} locale.\<close>

lemma continuous_on_sq_mtx_vec_multl:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "continuous_on T A"
  shows "continuous_on T (\<lambda>t. A t *\<^sub>V s)"
proof-
  have "matrix_continuous_on T (\<lambda>t. to_vec (A t))"
    using assms by (force simp: continuous_on_iff dist_norm norm_sq_mtx_def matrix_continuous_on_def)
  hence "continuous_on T (\<lambda>t. to_vec (A t) *v s)"
    by (rule continuous_on_matrix_vector_multl)
  thus ?thesis
    by transfer
qed

lemmas continuous_on_affine = continuous_on_add[OF continuous_on_sq_mtx_vec_multl]

lemma local_lipschitz_sq_mtx_affine:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "continuous_on T A" "open T" "open S"
  shows "local_lipschitz T S (\<lambda>t s. A t *\<^sub>V s + B t)"
proof-
  have obs: "\<And>\<tau> \<epsilon>. 0 < \<epsilon> \<Longrightarrow>  \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>A t\<parallel> |t. t \<in> cball \<tau> \<epsilon>}"
    by (rule bdd_above_norm_cont_comp, rule continuous_on_subset[OF assms(1)], simp_all)
  hence "\<And>\<tau> \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>to_vec (A t)\<parallel>\<^sub>o\<^sub>p |t. t \<in> cball \<tau> \<epsilon>}"
    by (simp add: norm_sq_mtx_def)
  hence "local_lipschitz T S (\<lambda>t s. to_vec (A t) *v s + B t)"
    using local_lipschitz_affine[OF assms(2,3), of "\<lambda>t. to_vec (A t)"] by force
  thus ?thesis
    by transfer 
qed

lemma picard_lindeloef_sq_mtx_affine:
  assumes "continuous_on T A" and "continuous_on T B" 
    and "t\<^sub>0 \<in> T" "is_interval T" "open T" and "open S"
  shows "picard_lindeloef (\<lambda>t s. A t *\<^sub>V s + B t) T S t\<^sub>0"
  apply(unfold_locales, simp_all add: assms, clarsimp)
  using continuous_on_affine assms apply blast
  by (rule local_lipschitz_sq_mtx_affine, simp_all add: assms)

lemmas sq_mtx_unique_sol_autonomous_affine = picard_lindeloef.unique_solution[OF 
    picard_lindeloef_sq_mtx_affine[OF 
      continuous_on_const 
      continuous_on_const 
      UNIV_I is_interval_univ 
      open_UNIV open_UNIV] 
    _ _ funcset_UNIV UNIV_I _ _ funcset_UNIV UNIV_I]

lemma has_vderiv_on_sq_mtx_linear:
  "D (\<lambda>t. exp ((t - t\<^sub>0) *\<^sub>R A) *\<^sub>V s) = (\<lambda>t. A *\<^sub>V (exp ((t - t\<^sub>0) *\<^sub>R A) *\<^sub>V s)) on {t\<^sub>0--t}"
  by (rule poly_derivatives)+ (auto simp: exp_times_scaleR_commute sq_mtx_times_vec_assoc)

lemma has_vderiv_on_sq_mtx_affine:
  fixes t\<^sub>0::real and A :: "('a::finite) sq_mtx"
  defines "lSol c t \<equiv> exp ((c * (t - t\<^sub>0)) *\<^sub>R A)"
  shows "D (\<lambda>t. lSol 1 t *\<^sub>V s + lSol 1 t *\<^sub>V (\<integral>\<^sub>t\<^sub>0\<^sup>t (lSol (-1) \<tau> *\<^sub>V B) \<partial>\<tau>)) = 
  (\<lambda>t. A *\<^sub>V (lSol 1 t *\<^sub>V s + lSol 1 t *\<^sub>V (\<integral>\<^sub>t\<^sub>0\<^sup>t (lSol (-1) \<tau> *\<^sub>V B) \<partial>\<tau>)) + B) on {t\<^sub>0--t}"
  unfolding assms apply(simp only: mult.left_neutral mult_minus1)
  apply(rule poly_derivatives, (force)?, (force)?, (force)?, (force)?)+
  by (simp add: mtx_vec_mult_add_rdistl sq_mtx_times_vec_assoc[symmetric] 
      exp_minus_inverse exp_times_scaleR_commute mult_exp_exp  scale_left_distrib[symmetric])

lemma autonomous_linear_sol_is_exp:
  assumes "D X = (\<lambda>t. A *\<^sub>V X t) on {t\<^sub>0--t}" and "X t\<^sub>0 = s" 
  shows "X t = exp ((t - t\<^sub>0) *\<^sub>R A) *\<^sub>V s"
  apply(rule sq_mtx_unique_sol_autonomous_affine[of X A 0, OF _ \<open>X t\<^sub>0 = s\<close>])
  using assms has_vderiv_on_sq_mtx_linear by force+

lemma autonomous_affine_sol_is_exp_plus_int:
  assumes "D X = (\<lambda>t. A *\<^sub>V X t + B) on {t\<^sub>0--t}" and "X t\<^sub>0 = s" 
  shows "X t = exp ((t - t\<^sub>0) *\<^sub>R A) *\<^sub>V s + exp ((t - t\<^sub>0) *\<^sub>R A) *\<^sub>V (\<integral>\<^sub>t\<^sub>0\<^sup>t(exp (- (\<tau> - t\<^sub>0) *\<^sub>R A) *\<^sub>V B)\<partial>\<tau>)"
  apply(rule sq_mtx_unique_sol_autonomous_affine[OF assms])
  using has_vderiv_on_sq_mtx_affine by force+

lemma local_flow_sq_mtx_linear: "local_flow ((*\<^sub>V) A) UNIV UNIV (\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx_affine[of _ "\<lambda>t. A" "\<lambda>t. 0"] apply force
  using has_vderiv_on_sq_mtx_linear[of 0] by auto

lemma local_flow_sq_mtx_affine: "local_flow (\<lambda>s. A *\<^sub>V s + B) UNIV UNIV 
  (\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s + exp (t *\<^sub>R A) *\<^sub>V (\<integral>\<^sub>0\<^sup>t(exp (- \<tau> *\<^sub>R A) *\<^sub>V B)\<partial>\<tau>))"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx_affine[of _ "\<lambda>t. A" "\<lambda>t. B"] apply force
  using has_vderiv_on_sq_mtx_affine[of 0 A] by auto


end