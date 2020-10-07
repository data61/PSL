theory Paths
  imports Derivs General_Utils Integrals
begin
(*This has everything related to paths purely*)

lemma reverse_subpaths_join:
  shows " subpath 1 (1 / 2) p +++ subpath (1 / 2) 0 p = reversepath p"
  using reversepath_subpath join_subpaths_middle pathfinish_subpath pathstart_subpath reversepath_joinpaths
  by (metis (no_types, lifting))


(*Below F cannot be from 'a \<Rightarrow> 'b because the dot product won't work.
  We have that g returns 'a and then F takes the output of g, so F should start from 'a
  Then we have to compute the dot product of the vector b with both the derivative of g, and F.
  Since the derivative of g returns the same type as g, accordingly F should return the same type as g, i.e. 'a.
 *)
definition line_integral:: "('a::euclidean_space \<Rightarrow> 'a::euclidean_space) \<Rightarrow> (('a) set) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real" where
"line_integral F basis g \<equiv> integral {0 .. 1} (\<lambda>x. \<Sum>b\<in>basis. (F(g x) \<bullet> b) * (vector_derivative g (at x within {0..1}) \<bullet> b))"

definition line_integral_exists where
  "line_integral_exists F basis \<gamma> \<equiv> (\<lambda>x. \<Sum>b\<in>basis. F(\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"

lemma line_integral_on_pair_straight_path:
  fixes F::"('a::euclidean_space) \<Rightarrow> 'a" and g :: "real \<Rightarrow> real" and \<gamma>
  assumes gamma_const: "\<forall>x. \<gamma>(x)\<bullet> i = a"
      and gamma_smooth: "\<forall>x \<in> {0 .. 1}. \<gamma> differentiable at x"          
  shows "(line_integral F {i} \<gamma>) = 0" "(line_integral_exists F {i} \<gamma>)"
proof (simp add: line_integral_def)
  have *: "F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i) = 0"
    if "0 \<le> x \<and> x \<le> 1" for x
  proof -
    have "((\<lambda>x. \<gamma>(x)\<bullet> i) has_vector_derivative 0) (at x)"
      using vector_derivative_const_at[of "a" "x"] and gamma_const
      by auto
    then have "(vector_derivative \<gamma> (at x) \<bullet> i) = 0"
      using derivative_component_fun_component[ of "\<gamma>" "x" "i"]
        and gamma_smooth and that
      by (simp add: vector_derivative_at)
    then have "(vector_derivative \<gamma> (at x within {0 .. 1}) \<bullet> i) = 0"
      using has_vector_derivative_at_within vector_derivative_at_within_ivl that
      by (metis atLeastAtMost_iff gamma_smooth vector_derivative_works zero_less_one)
    then show ?thesis
      by auto
  qed
  then have "((\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) has_integral 0) {0..1}"
    using has_integral_is_0[of "{0 .. 1}" "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i))"]
    by auto
  then have "((\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) integrable_on {0..1})"
    by auto
  then show "line_integral_exists F {i} \<gamma>" by (auto simp add:line_integral_exists_def)
  show "integral {0..1} (\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) = 0"
    using * has_integral_is_0[of "{0 .. 1}" "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i))"]
    by auto
qed

lemma line_integral_on_pair_path_strong:
  fixes F::"('a::euclidean_space) \<Rightarrow> ('a)" and
    g::"real \<Rightarrow> 'a" and
    \<gamma>::"(real \<Rightarrow> 'a)" and
    i::'a 
  assumes i_norm_1: "norm i = 1" and
    g_orthogonal_to_i: "\<forall>x. g(x) \<bullet> i = 0" and  
    gamma_is_in_terms_of_i: "\<gamma> = (\<lambda>x. f(x) *\<^sub>R i + g(f(x)))" and
    gamma_smooth: "\<gamma> piecewise_C1_differentiable_on {0 .. 1}" and
    g_continuous_on_f: "continuous_on (f ` {0..1}) g" and
    path_start_le_path_end: "(pathstart \<gamma>) \<bullet> i \<le> (pathfinish \<gamma>) \<bullet> i" and
    field_i_comp_cont: "continuous_on (path_image \<gamma>) (\<lambda>x. F x \<bullet> i)"
  shows "line_integral F {i} \<gamma> 
         = integral (cbox ((pathstart \<gamma>) \<bullet> i) ((pathfinish \<gamma>) \<bullet> i)) (\<lambda>f_var. (F (f_var *\<^sub>R i + g(f_var)) \<bullet> i))"
    "line_integral_exists F {i} \<gamma>"
proof (simp add: line_integral_def)
  obtain s where gamma_differentiable: "finite s" "(\<forall>x \<in> {0 .. 1} - s. \<gamma> differentiable at x)"
    using gamma_smooth
    by (auto simp add: C1_differentiable_on_eq piecewise_C1_differentiable_on_def)
  then have gamma_i_component_smooth: "\<forall>x \<in> {0 .. 1} - s. (\<lambda>x. \<gamma> x \<bullet> i) differentiable at x"
    by auto
  have field_cont_on_path: "continuous_on ((\<lambda>x. \<gamma> x \<bullet> i) ` {0..1}) (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"
  proof - 
    have 0: "(\<lambda>x. \<gamma> x \<bullet> i) = f"
    proof 
      fix x
      show "\<gamma> x \<bullet> i = f x"
        using g_orthogonal_to_i i_norm_1
        by (simp only: gamma_is_in_terms_of_i  real_inner_class.inner_add_left g_orthogonal_to_i inner_scaleR_left inner_same_Basis norm_eq_1)
    qed
    show ?thesis 
      unfolding 0 
      apply (rule continuous_on_compose2 [of _ "(\<lambda>x. F(x)  \<bullet> i)" "f ` { 0..1}" "(\<lambda>x. x *\<^sub>R i + g x)"]
          field_i_comp_cont g_continuous_on_f field_i_comp_cont continuous_intros)+
      by (auto simp add: gamma_is_in_terms_of_i path_image_def)
  qed
  have path_start_le_path_end': "\<gamma> 0 \<bullet> i \<le> \<gamma> 1 \<bullet> i" using path_start_le_path_end by (auto simp add: pathstart_def pathfinish_def)
  have gamm_cont: "continuous_on {0..1} (\<lambda>a. \<gamma> a \<bullet> i)"
    apply(rule continuous_on_inner)
    using gamma_smooth 
     apply (simp add: piecewise_C1_differentiable_on_def)
    using continuous_on_const by auto
  then obtain c d where cd: "c \<le> d" "(\<lambda>a. \<gamma> a \<bullet> i) ` {0..1} = {c..d}"
    by (meson continuous_image_closed_interval zero_le_one)
  then have subset_cd: "(\<lambda>a. \<gamma> a \<bullet> i) ` {0..1} \<subseteq> {c..d}" by auto
  have field_cont_on_path_cd:
    "continuous_on {c..d} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"
    using field_cont_on_path cd by auto
  have path_vector_deriv_line_integrals:
    "\<forall>x\<in>{0..1} - s. ((\<lambda>x. \<gamma> x \<bullet> i) has_vector_derivative 
                                          vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x))
                                                  (at x)"
    using gamma_i_component_smooth and derivative_component_fun_component and
      vector_derivative_works
    by blast       
  then have "\<forall>x\<in>{0..1} - s. ((\<lambda>x. \<gamma> x \<bullet> i) has_vector_derivative 
                                          vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within ({0..1})))
                                                  (at x within ({0..1}))"
    using has_vector_derivative_at_within vector_derivative_at_within_ivl
    by fastforce
  then have has_int:"((\<lambda>x. vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}) *\<^sub>R (F ((\<gamma> x \<bullet> i) *\<^sub>R i + g (\<gamma> x \<bullet> i)) \<bullet> i)) has_integral
           integral {\<gamma> 0 \<bullet> i..\<gamma> 1 \<bullet> i} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)) {0..1}"
    using has_integral_substitution_strong[OF gamma_differentiable(1) rel_simps(44)
        path_start_le_path_end' subset_cd field_cont_on_path_cd gamm_cont,
        of "(\<lambda>x. vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within ({0..1})))"]
      gamma_is_in_terms_of_i
    by (auto simp only: has_field_derivative_iff_has_vector_derivative)
  then have has_int':"((\<lambda>x. (F(\<gamma>(x)) \<bullet> i)*(vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within ({0..1})))) has_integral
           integral {((pathstart \<gamma>) \<bullet> i)..((pathfinish \<gamma>) \<bullet> i)} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)) {0..1}"
    using  gamma_is_in_terms_of_i i_norm_1
    apply (auto simp add: pathstart_def pathfinish_def)
    apply (simp only:  real_inner_class.inner_add_left inner_not_same_Basis g_orthogonal_to_i inner_scaleR_left norm_eq_1)
    by (auto simp add: algebra_simps)
  have substitute:
    "integral ({((pathstart \<gamma>) \<bullet> i)..((pathfinish \<gamma>) \<bullet> i)}) (\<lambda>f_var. (F (f_var *\<^sub>R i + g(f_var)) \<bullet> i)) 
                 = integral ({0..1}) (\<lambda>x. (F(\<gamma>(x)) \<bullet> i)*(vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within ({0..1}))))"
    using gamma_is_in_terms_of_i integral_unique[OF has_int] i_norm_1
    apply (auto simp add: pathstart_def pathfinish_def)
    apply (simp only:  real_inner_class.inner_add_left inner_not_same_Basis g_orthogonal_to_i inner_scaleR_left norm_eq_1)
    by (auto simp add: algebra_simps)
  have comp_in_eq_comp_out: "\<forall>x \<in> {0..1} - s.
            (vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1}))
                = (vector_derivative \<gamma> (at x within {0..1})) \<bullet> i"
  proof
    fix x:: real
    assume ass:"x \<in> {0..1} -s"
    then have x_bounds:"x \<in> {0..1}" by auto
    have "\<gamma> differentiable at x" using ass gamma_differentiable by auto
    then have dotprod_in_is_out:
      "vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x)
                         = (vector_derivative \<gamma> (at x)) \<bullet> i"
      using derivative_component_fun_component 
      by force
    then have 0: "(vector_derivative \<gamma> (at x)) \<bullet> i = (vector_derivative \<gamma> (at x within {0..1})) \<bullet> i"
    proof -
      have "(\<gamma> has_vector_derivative vector_derivative \<gamma> (at x)) (at x)"
        using \<open>\<gamma> differentiable at x\<close> vector_derivative_works by blast
      moreover have "0 \<le> x \<and> x \<le> 1"
        using x_bounds by presburger
      ultimately show ?thesis
        by (simp add: vector_derivative_at_within_ivl)
    qed
    have 1: "vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x) = vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1})"
      using path_vector_deriv_line_integrals and vector_derivative_at_within_ivl and
        x_bounds
      by (metis ass atLeastAtMost_iff zero_less_one)
    show "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}) = vector_derivative \<gamma> (at x within {0..1}) \<bullet> i"
      using 0 and 1 and dotprod_in_is_out
      by auto
  qed
  show "integral {0..1} (\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) =
                   integral {pathstart \<gamma> \<bullet> i..pathfinish \<gamma> \<bullet> i} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"
    using substitute and comp_in_eq_comp_out and negligible_finite
      Henstock_Kurzweil_Integration.integral_spike
      [of "s" "{0..1}" "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i))"
        "(\<lambda>x. F (\<gamma> x) \<bullet> i * vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))"]
    by (metis (no_types, lifting) gamma_differentiable(1))
  have "((\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) has_integral
                   integral {pathstart \<gamma> \<bullet> i..pathfinish \<gamma> \<bullet> i} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)) {0..1}"
    using has_int' and comp_in_eq_comp_out and negligible_finite
      Henstock_Kurzweil_Integration.has_integral_spike
      [of "s" "{0..1}" "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i))"
        "(\<lambda>x. F (\<gamma> x) \<bullet> i * vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))"
        "integral {pathstart \<gamma> \<bullet> i..pathfinish \<gamma> \<bullet> i} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"]
    by (metis (no_types, lifting) gamma_differentiable(1))
  then have "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) integrable_on {0..1}"
    using integrable_on_def by auto
  then show "line_integral_exists F {i} \<gamma>"
    by (auto simp add: line_integral_exists_def)
qed

lemma line_integral_on_pair_path:
  fixes F::"('a::euclidean_space) \<Rightarrow> ('a)" and
    g::"real \<Rightarrow> 'a" and
    \<gamma>::"(real \<Rightarrow> 'a)" and
    i::'a 
  assumes i_norm_1: "norm i = 1" and
    g_orthogonal_to_i: "\<forall>x. g(x) \<bullet> i = 0" and  
    gamma_is_in_terms_of_i: "\<gamma> = (\<lambda>x. f(x) *\<^sub>R i + g(f(x)))" and
    gamma_smooth: "\<gamma> C1_differentiable_on {0 .. 1}" and
    g_continuous_on_f: "continuous_on (f ` {0..1}) g" and
    path_start_le_path_end: "(pathstart \<gamma>) \<bullet> i \<le> (pathfinish \<gamma>) \<bullet> i" and
    field_i_comp_cont: "continuous_on (path_image \<gamma>) (\<lambda>x. F x \<bullet> i)"
  shows "(line_integral F {i} \<gamma>) 
                 = integral (cbox ((pathstart \<gamma>) \<bullet> i) ((pathfinish \<gamma>) \<bullet> i)) (\<lambda>f_var. (F (f_var *\<^sub>R i + g(f_var)) \<bullet> i))"
proof (simp add: line_integral_def)
  have gamma_differentiable: "\<forall>x \<in> {0 .. 1}. \<gamma> differentiable at x"
    using gamma_smooth  C1_differentiable_on_eq by blast
  then have gamma_i_component_smooth:
    "\<forall>x \<in> {0 .. 1}. (\<lambda>x. \<gamma> x \<bullet> i) differentiable at x"
    by auto
  have vec_deriv_i_comp_cont:
    "continuous_on {0..1} (\<lambda>x. vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))"
  proof -
    have "continuous_on {0..1} (\<lambda>x. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}))"
      using gamma_smooth C1_differentiable_on_eq
      by (smt C1_differentiable_on_def atLeastAtMost_iff continuous_on_eq vector_derivative_at_within_ivl)
    then have deriv_comp_cont:
      "continuous_on {0..1} (\<lambda>x. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) \<bullet> i)"
      by (simp add: continuous_intros)
    show ?thesis
      using derivative_component_fun_component_at_within[OF gamma_differentiable, of "i"]                    
        continuous_on_eq[OF deriv_comp_cont, of "(\<lambda>x. vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))"]
      by fastforce
  qed
  have field_cont_on_path:
    "continuous_on ((\<lambda>x. \<gamma> x \<bullet> i) ` {0..1}) (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"
  proof - 
    have 0: "(\<lambda>x. \<gamma> x \<bullet> i) = f"
    proof 
      fix x
      show "\<gamma> x \<bullet> i = f x"
        using g_orthogonal_to_i i_norm_1
        by (simp only: gamma_is_in_terms_of_i  real_inner_class.inner_add_left g_orthogonal_to_i inner_scaleR_left inner_same_Basis norm_eq_1)
    qed
    show ?thesis 
      unfolding 0 
      apply (rule continuous_on_compose2 [of _ "(\<lambda>x. F(x)  \<bullet> i)" "f ` { 0..1}" "(\<lambda>x. x *\<^sub>R i + g x)"]
          field_i_comp_cont g_continuous_on_f field_i_comp_cont continuous_intros)+
      by (auto simp add: gamma_is_in_terms_of_i path_image_def)
  qed
  have path_vector_deriv_line_integrals:
    "\<forall>x\<in>{0..1}. ((\<lambda>x. \<gamma> x \<bullet> i) has_vector_derivative 
                                          vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x))
                                                  (at x)"
    using gamma_i_component_smooth and derivative_component_fun_component and
      vector_derivative_works
    by blast       
  then have "\<forall>x\<in>{0..1}. ((\<lambda>x. \<gamma> x \<bullet> i) has_vector_derivative 
                                          vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))
                                                  (at x within {0..1})"
    using has_vector_derivative_at_within vector_derivative_at_within_ivl
    by fastforce
  then have substitute:
    "integral (cbox ((pathstart \<gamma>) \<bullet> i) ((pathfinish \<gamma>) \<bullet> i)) (\<lambda>f_var. (F (f_var *\<^sub>R i + g(f_var)) \<bullet> i)) 
                 = integral (cbox 0 1) (\<lambda>x. (F(\<gamma>(x)) \<bullet> i)*(vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1})))"
    using gauge_integral_by_substitution
      [of "0" "1" "(\<lambda>x. (\<gamma> x) \<bullet> i)"
        "(\<lambda>x. vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1}))"
        "(\<lambda>f_var. (F (f_var *\<^sub>R i + g(f_var)) \<bullet> i))"] and
      path_start_le_path_end and vec_deriv_i_comp_cont and field_cont_on_path and 
      gamma_is_in_terms_of_i i_norm_1
    apply (auto simp add: pathstart_def pathfinish_def)
    apply (simp only:  real_inner_class.inner_add_left inner_not_same_Basis g_orthogonal_to_i inner_scaleR_left norm_eq_1)
    by (auto)
      (*integration by substitution*)
  have comp_in_eq_comp_out: "\<forall>x \<in> {0..1}.
            (vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1}))
                = (vector_derivative \<gamma> (at x within {0..1})) \<bullet> i"
  proof
    fix x:: real
    assume x_bounds: "x \<in> {0..1}"
    then have "\<gamma> differentiable at x" using gamma_differentiable by auto
    then have dotprod_in_is_out:
      "vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x)
                         = (vector_derivative \<gamma> (at x)) \<bullet> i"
      using derivative_component_fun_component 
      by force
    then have 0: "(vector_derivative \<gamma> (at x)) \<bullet> i
                         = (vector_derivative \<gamma> (at x within {0..1})) \<bullet> i"
      using has_vector_derivative_at_within and x_bounds and vector_derivative_at_within_ivl
      by (smt atLeastAtMost_iff gamma_differentiable inner_commute vector_derivative_works)
    have 1: "vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x) = vector_derivative (\<lambda>x. \<gamma>(x) \<bullet> i) (at x within {0..1})"
      using path_vector_deriv_line_integrals and vector_derivative_at_within_ivl and
        x_bounds
      by fastforce
    show "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}) = vector_derivative \<gamma> (at x within {0..1}) \<bullet> i"
      using 0 and 1 and dotprod_in_is_out
      by auto
  qed
  show "integral {0..1} (\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i)) =
                   integral {pathstart \<gamma> \<bullet> i..pathfinish \<gamma> \<bullet> i} (\<lambda>f_var. F (f_var *\<^sub>R i + g f_var) \<bullet> i)"
    using substitute and comp_in_eq_comp_out and 
      Henstock_Kurzweil_Integration.integral_cong
      [of "{0..1}" "(\<lambda>x. F (\<gamma> x) \<bullet> i * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> i))"
        "(\<lambda>x. F (\<gamma> x) \<bullet> i * vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1}))"]
    by auto
qed

lemma content_box_cases:
  "content (box a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then prod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by (simp add: measure_lborel_box_eq inner_diff)

lemma content_box_cbox:
  shows "content (box a b) = content (cbox a b)"
  by (simp add: content_box_cases content_cbox_cases)

lemma content_eq_0: "content (box a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by (auto simp: content_box_cases not_le intro: less_imp_le antisym eq_refl)

lemma content_pos_lt_eq: "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  by (auto simp add: content_cbox_cases less_le prod_nonneg)

lemma content_lt_nz: "0 < content (box a b) \<longleftrightarrow> content (box a b) \<noteq> 0"
  using Paths.content_eq_0 zero_less_measure_iff by blast

lemma content_subset: "cbox a b \<subseteq> box c d \<Longrightarrow> content (cbox a b) \<le> content (box c d)"
  unfolding measure_def
  by (intro enn2real_mono emeasure_mono) (auto simp: emeasure_lborel_cbox_eq emeasure_lborel_box_eq)

lemma sum_content_null:
  assumes "content (box a b) = 0"
    and "p tagged_division_of (box a b)"
  shows "sum (\<lambda>(x,k). content k *\<^sub>R f x) p = (0::'a::real_normed_vector)"
proof (rule sum.neutral, rule)
  fix y
  assume y: "y \<in> p"
  obtain x k where xk: "y = (x, k)"
    using surj_pair[of y] by blast
  note assm = tagged_division_ofD(3-4)[OF assms(2) y[unfolded xk]]
  from this(2) obtain c d where k: "k = cbox c d" by blast
  have "(\<lambda>(x, k). content k *\<^sub>R f x) y = content k *\<^sub>R f x"
    unfolding xk by auto
  also have "\<dots> = 0"
    using content_subset[OF assm(1)[unfolded k]] content_pos_le[of "cbox c d"]
    unfolding assms(1) k
    by auto
  finally show "(\<lambda>(x, k). content k *\<^sub>R f x) y = 0" .
qed


lemma has_integral_null [intro]: "content(box a b) = 0 \<Longrightarrow> (f has_integral 0) (box a b)"
  by (simp add: content_box_cbox content_eq_0_interior)

lemma line_integral_distrib:
  assumes "line_integral_exists f basis g1"
    "line_integral_exists f basis g2"
    "valid_path g1" "valid_path g2"
  shows "line_integral f basis (g1 +++ g2) = line_integral f basis g1 + line_integral f basis g2"
    "line_integral_exists f basis (g1 +++ g2)"
proof -
  obtain s1 s2
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
      and s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  obtain i1 i2
    where 1: "((\<lambda>x. \<Sum>b\<in>basis. f (g1 x) \<bullet> b * (vector_derivative g1 (at x within {0..1}) \<bullet> b)) has_integral i1) {0..1}"
      and 2: "((\<lambda>x. \<Sum>b\<in>basis. f (g2 x) \<bullet> b * (vector_derivative g2 (at x within {0..1}) \<bullet> b)) has_integral i2) {0..1}"
    using assms
    by (auto simp: line_integral_exists_def)
  have i1: "((\<lambda>x. 2 * (\<Sum>b\<in>basis. f (g1 (2 * x)) \<bullet> b * (vector_derivative g1 (at (2 * x) within {0..1}) \<bullet> b))) has_integral i1) {0..1/2}"
   and i2: "((\<lambda>x. 2 * (\<Sum>b\<in>basis. f (g2 (2 * x - 1)) \<bullet> b * (vector_derivative g2 (at ((2 * x) - 1) within {0..1}) \<bullet> b))) has_integral i2) {1/2..1}"
    using has_integral_affinity01 [OF 1, where m= 2 and c=0, THEN has_integral_cmul [where c=2]]
      has_integral_affinity01 [OF 2, where m= 2 and c="-1", THEN has_integral_cmul [where c=2]]
    by (simp_all only: image_affinity_atLeastAtMost_div_diff, simp_all add: scaleR_conv_of_real mult_ac)
  have g1: "\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z within {0..1}) =
            2 *\<^sub>R vector_derivative g1 (at (z*2) within {0..1})" for z
  proof -
    have i:"\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
              vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2))" for z
    proof-
      have g1_at_z:"\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
                         ((\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) has_vector_derivative
                         2 *\<^sub>R vector_derivative g1 (at (z*2))) (at z)" for z
        apply (rule has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g1(2*x))"])
          apply (simp_all add: dist_real_def abs_if split: if_split_asm)
        apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x" 2 _ g1, simplified o_def])
         apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
        using s1
        apply (auto simp: algebra_simps vector_derivative_works)
        done
      assume ass: "0 \<le> z" "z*2 < 1" "z*2 \<notin> s1"
      then have z_ge: "z\<le> 1" by auto
      show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2))"
        using Derivative.vector_derivative_at_within_ivl[OF g1_at_z[OF ass] ass(1) z_ge]
        by auto
    qed
    assume ass: "0 \<le> z" "z*2 < 1" "z*2 \<notin> s1"
    then have "(g1 has_vector_derivative ((vector_derivative g1 (at (z*2))))) (at (z*2))"
      using s1 by (auto simp: algebra_simps vector_derivative_works)
    then have ii: "(vector_derivative g1 (at (z*2) within {0..1})) = (vector_derivative g1 (at (z*2)))"
      using Derivative.vector_derivative_at_within_ivl ass
      by force
    show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2) within {0..1})"
      using i[OF ass] ii
      by auto
  qed
  have g2: "\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z within {0..1}) =
            2 *\<^sub>R vector_derivative g2 (at (z*2 - 1) within {0..1})" for z       proof -
    have i:"\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
              vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1})
                   = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1))" for z
    proof-
      have g2_at_z:"\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
                      ((\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) has_vector_derivative 2 *\<^sub>R vector_derivative g2 (at (z*2 - 1))) (at z)" for z
        apply (rule has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g2 (2*x - 1))"])
          apply (simp_all add: dist_real_def abs_if split: if_split_asm)
        apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x - 1" 2 _ g2, simplified o_def])
         apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
        using s2
        apply (auto simp: algebra_simps vector_derivative_works)
        done
      assume ass: "1 < z*2" "z \<le> 1" "z*2 - 1 \<notin> s2"
      then have z_le: "z\<le> 1" by auto
      have z_ge: "0 \<le> z" using ass by auto
      show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1})
                                = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1))"
        using Derivative.vector_derivative_at_within_ivl[OF g2_at_z[OF ass] z_ge z_le]
        by auto
    qed
    assume ass: "1 < z*2" "z \<le> 1" "z*2 - 1 \<notin> s2"
    then have "(g2 has_vector_derivative ((vector_derivative g2 (at (z*2 - 1))))) (at (z*2 - 1))"
      using s2 by (auto simp: algebra_simps vector_derivative_works)
    then have ii: "(vector_derivative g2 (at (z*2 - 1) within {0..1})) = (vector_derivative g2 (at (z*2 - 1)))"
      using Derivative.vector_derivative_at_within_ivl ass
      by force
    show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1) within {0..1})"
      using i[OF ass] ii
      by auto
  qed
  have lem1: "((\<lambda>x. \<Sum>b\<in>basis. f ((g1+++g2) x) \<bullet> b * (vector_derivative (g1+++g2) (at x within {0..1}) \<bullet> b)) has_integral i1) {0..1/2}"
    apply (rule has_integral_spike_finite [OF _ _ i1, of "insert (1/2) ((*)2 -` s1)"])
    using s1
     apply (force intro: finite_vimageI [where h = "(*)2"] inj_onI)
    apply (clarsimp simp add: joinpaths_def scaleR_conv_of_real mult_ac g1)
    by (simp add: sum_distrib_left)
  moreover have lem2: "((\<lambda>x. \<Sum>b\<in>basis. f ((g1+++g2) x) \<bullet> b * (vector_derivative (g1+++g2) (at x within {0..1}) \<bullet> b)) has_integral i2) {1/2..1}"
    apply (rule has_integral_spike_finite [OF _ _ i2, of "insert (1/2) ((\<lambda>x. 2*x-1) -` s2)"])
    using s2
     apply (force intro: finite_vimageI [where h = "\<lambda>x. 2*x-1"] inj_onI)
    apply (clarsimp simp add: joinpaths_def scaleR_conv_of_real mult_ac g2)
    by (simp add: sum_distrib_left)
  ultimately
  show "line_integral f basis (g1 +++ g2) = line_integral f basis g1 + line_integral f basis g2"
    apply (simp add: line_integral_def)
    apply (rule integral_unique [OF has_integral_combine [where c = "1/2"]])
    using 1 2 integral_unique apply auto
    done
  show "line_integral_exists f basis (g1 +++ g2)"
  proof (simp add: line_integral_exists_def integrable_on_def)
    have "(1::real) \<le> 1 * 2 \<and> (0::real) \<le> 1 / 2"
      by simp
    then show "\<exists>r. ((\<lambda>r. \<Sum>a\<in>basis. f ((g1 +++ g2) r) \<bullet> a * (vector_derivative (g1 +++ g2) (at r within {0..1}) \<bullet> a)) has_integral r) {0..1}"
    using has_integral_combine [where c = "1/2"] 1 2 divide_le_eq_numeral1(1) lem1 lem2 by blast
  qed
qed

lemma line_integral_exists_joinD1:
  assumes "line_integral_exists f basis (g1 +++ g2)" "valid_path g1"
  shows "line_integral_exists f basis g1"
proof -
  obtain s1
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. \<Sum>b\<in>basis. f ((g1 +++ g2) (x/2)) \<bullet> b * (vector_derivative (g1 +++ g2) (at (x/2) within {0..1}) \<bullet> b)) integrable_on {0..1}"
    using assms
    apply (auto simp: line_integral_exists_def)
    apply (drule integrable_on_subcbox [where a=0 and b="1/2"])
     apply (auto intro: integrable_affinity [of _ 0 "1/2::real" "1/2" 0, simplified])
    done
  then have *:"(\<lambda>x. \<Sum>b\<in>basis. ((f ((g1 +++ g2) (x/2)) \<bullet> b) / 2)* (vector_derivative (g1 +++ g2) (at (x/2) within {0..1}) \<bullet> b)) integrable_on {0..1}"
    by (auto simp: Groups_Big.sum_distrib_left dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g1: "\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z within {0..1}) =
            2 *\<^sub>R vector_derivative g1 (at (z*2) within {0..1})" for z
  proof -
    have i:"\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
              vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2))" for z
    proof-
      have g1_at_z:"\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
                         ((\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) has_vector_derivative
                         2 *\<^sub>R vector_derivative g1 (at (z*2))) (at z)" for z
        apply (rule has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g1(2*x))"])
          apply (simp_all add: dist_real_def abs_if split: if_split_asm)
        apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x" 2 _ g1, simplified o_def])
         apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
        using s1
        apply (auto simp: algebra_simps vector_derivative_works)
        done
      assume ass: "0 \<le> z" "z*2 < 1" "z*2 \<notin> s1"
      then have z_ge: "z\<le> 1" by auto
      show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2))"
        using Derivative.vector_derivative_at_within_ivl[OF g1_at_z[OF ass] ass(1) z_ge]
        by auto
    qed
    assume ass: "0 \<le> z" "z*2 < 1" "z*2 \<notin> s1"
    then have "(g1 has_vector_derivative ((vector_derivative g1 (at (z*2))))) (at (z*2))"
      using s1 by (auto simp: algebra_simps vector_derivative_works)
    then have ii: "(vector_derivative g1 (at (z*2) within {0..1})) = (vector_derivative g1 (at (z*2)))"
      using Derivative.vector_derivative_at_within_ivl ass by force
    show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g1 (at (z * 2) within {0..1})"
      using i[OF ass] ii by auto
  qed
  show ?thesis
    using s1
    apply (auto simp: line_integral_exists_def)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s1", OF _ _ *])
     apply (auto simp: joinpaths_def scaleR_conv_of_real g1)
    done
qed

lemma line_integral_exists_joinD2:
  assumes "line_integral_exists f basis (g1 +++ g2)" "valid_path g2"
  shows "line_integral_exists f basis g2"
proof -
  obtain s2
    where s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. \<Sum>b\<in>basis. f ((g1 +++ g2) (x/2 + 1/2)) \<bullet> b * (vector_derivative (g1 +++ g2) (at (x/2 + 1/2) within {0..1}) \<bullet> b)) integrable_on {0..1}"
    using assms
    apply (auto simp: line_integral_exists_def)
    apply (drule integrable_on_subcbox [where a="1/2" and b=1], auto)
    apply (drule integrable_affinity [of _ "1/2::real" 1 "1/2" "1/2", simplified])
    apply (simp add: image_affinity_atLeastAtMost_diff)
    done
  then have *:"(\<lambda>x. \<Sum>b\<in>basis. ((f ((g1 +++ g2) (x/2 + 1/2)) \<bullet> b) / 2)* (vector_derivative (g1 +++ g2) (at (x/2 + 1/2) within {0..1}) \<bullet> b)) integrable_on {0..1}"
    by (auto simp: Groups_Big.sum_distrib_left dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g2: "\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z within {0..1}) =
            2 *\<^sub>R vector_derivative g2 (at (z*2 - 1) within {0..1})" for z       proof -
    have i:"\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
              vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1})
                   = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1))" for z
    proof-
      have g2_at_z:"\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
                      ((\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) has_vector_derivative 2 *\<^sub>R vector_derivative g2 (at (z*2 - 1))) (at z)" for z
        apply (rule has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g2 (2*x - 1))"])
          apply (simp_all add: dist_real_def abs_if split: if_split_asm)
        apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x - 1" 2 _ g2, simplified o_def])
         apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
        using s2
        apply (auto simp: algebra_simps vector_derivative_works)
        done
      assume ass: "1 < z*2" "z \<le> 1" "z*2 - 1 \<notin> s2"
      then have z_le: "z\<le> 1" by auto
      have z_ge: "0 \<le> z" using ass by auto
      show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1})
                                = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1))"
        using Derivative.vector_derivative_at_within_ivl[OF g2_at_z[OF ass] z_ge z_le]
        by auto
    qed
    assume ass: "1 < z*2" "z \<le> 1" "z*2 - 1 \<notin> s2"
    then have "(g2 has_vector_derivative ((vector_derivative g2 (at (z*2 - 1))))) (at (z*2 - 1))"
      using s2 by (auto simp: algebra_simps vector_derivative_works)
    then have ii: "(vector_derivative g2 (at (z*2 - 1) within {0..1})) = (vector_derivative g2 (at (z*2 - 1)))"
      using Derivative.vector_derivative_at_within_ivl ass
      by force
    show "vector_derivative (\<lambda>x. if x * 2 \<le> 1 then g1 (2 * x) else g2 (2 * x - 1)) (at z within {0..1}) = 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1) within {0..1})"
      using i[OF ass] ii
      by auto
  qed
  show ?thesis
    using s2
    apply (auto simp: line_integral_exists_def)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s2", OF _ _ *])
     apply (auto simp: joinpaths_def scaleR_conv_of_real g2)
    done
qed

lemma has_line_integral_on_reverse_path:
  assumes g: "valid_path g" and int:
    "((\<lambda>x. \<Sum>b\<in>basis. F (g x) \<bullet> b * (vector_derivative g (at x within {0..1}) \<bullet> b)) has_integral c){0..1}"
  shows  "((\<lambda>x. \<Sum>b\<in>basis. F ((reversepath g) x) \<bullet> b * (vector_derivative (reversepath g) (at x within {0..1}) \<bullet> b)) has_integral -c){0..1}"
proof -
  { fix s x
    assume xs: "g C1_differentiable_on ({0..1} - s)" "x \<notin> (-) 1 ` s" "0 \<le> x" "x \<le> 1"
    have "vector_derivative (\<lambda>x. g (1 - x)) (at x within {0..1}) =
                - vector_derivative g (at (1 - x) within {0..1})"
    proof -
      obtain f' where f': "(g has_vector_derivative f') (at (1 - x))"
        using xs
        by (force simp: has_vector_derivative_def C1_differentiable_on_def)
      have "(g o (\<lambda>x. 1 - x) has_vector_derivative -1 *\<^sub>R f') (at x)"
        apply (rule vector_diff_chain_within)
         apply (intro vector_diff_chain_within derivative_eq_intros | simp)+
        apply (rule has_vector_derivative_at_within [OF f'])
        done
      then have mf': "((\<lambda>x. g (1 - x)) has_vector_derivative -f') (at x)"
        by (simp add: o_def)
      show ?thesis
        using xs
        by (auto simp: vector_derivative_at_within_ivl [OF mf'] vector_derivative_at_within_ivl [OF f'])
    qed
  } note * = this
  obtain S where "continuous_on {0..1} g" "finite S" "g C1_differentiable_on {0..1} - S"
    using g
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  then show ?thesis 
    using has_integral_affinity01 [OF int, where m= "-1" and c=1]
    unfolding reversepath_def
    by (rule_tac S = "(\<lambda>x. 1 - x) ` S" in has_integral_spike_finite) (auto simp: * has_integral_neg Groups_Big.sum_negf)
qed

lemma line_integral_on_reverse_path:
  assumes "valid_path \<gamma>" "line_integral_exists F basis \<gamma>"
  shows "line_integral F basis \<gamma> = - (line_integral F basis (reversepath \<gamma>))"
        "line_integral_exists F basis (reversepath \<gamma>)"
proof -
  obtain i where
    0: "((\<lambda>x. \<Sum>b\<in>basis. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) has_integral i){0..1}"
    using assms unfolding integrable_on_def line_integral_exists_def by auto
  then have 1: "((\<lambda>x. \<Sum>b\<in>basis. F ((reversepath \<gamma>) x) \<bullet> b * (vector_derivative (reversepath \<gamma>) (at x within {0..1}) \<bullet> b)) has_integral -i){0..1}"
    using has_line_integral_on_reverse_path assms
    by auto
  then have rev_line_integral:"line_integral F basis (reversepath \<gamma>) = -i"
    using line_integral_def Henstock_Kurzweil_Integration.integral_unique
    by (metis (no_types))
  have line_integral: "line_integral F basis \<gamma> = i"
    using line_integral_def 0 Henstock_Kurzweil_Integration.integral_unique
    by blast
  show "line_integral F basis \<gamma> = - (line_integral F basis (reversepath \<gamma>))"
    using line_integral rev_line_integral
    by auto
  show "line_integral_exists F basis (reversepath \<gamma>)"
    using 1 line_integral_exists_def
    by auto
qed

lemma line_integral_exists_on_degenerate_path:
  assumes "finite basis"
  shows "line_integral_exists F basis (\<lambda>x. c)"
proof-
  have every_component_integrable:
    "\<forall>b\<in>basis. (\<lambda>x. F ((\<lambda>x. c) x) \<bullet> b * (vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
  proof
    fix b
    assume b_in_basis: "b \<in> basis"
    have cont_field_zero_one: "continuous_on {0..1} (\<lambda>x. F ((\<lambda>x. c) x) \<bullet> b)"
      using continuous_on_const by fastforce
    have cont_path_zero_one:
      "continuous_on {0..1} (\<lambda>x. (vector_derivative (\<lambda>x. c) (at x within {0..1})) \<bullet> b)"
    proof -
      have "((vector_derivative (\<lambda>x. c) (at x within {0..1})) \<bullet> b) = 0" if "x \<in> {0..1}" for x
      proof -
        have "vector_derivative (\<lambda>x. c) (at x within {0..1}) = 0"
          using that gamma_deriv_at_within[of "0" "1"] differentiable_const vector_derivative_const_at
          by fastforce
        then show "vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b = 0"
          by auto
      qed
      then show "continuous_on {0..1} (\<lambda>x. (vector_derivative (\<lambda>x. c) (at x within {0..1})) \<bullet> b)"
        using continuous_on_const[of "{0..1}" "0"] continuous_on_eq[of "{0..1}" "\<lambda>x. 0" "(\<lambda>x. (vector_derivative (\<lambda>x. c) (at x within {0..1})) \<bullet> b)"]
        by auto
    qed
    show "(\<lambda>x. F (c) \<bullet> b * (vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
      using cont_field_zero_one cont_path_zero_one continuous_on_mult integrable_continuous_real
      by blast
  qed
  have integrable_sum': "\<And>t f s. finite t \<Longrightarrow>
                \<forall>a\<in>t. f a integrable_on s \<Longrightarrow> (\<lambda>x. \<Sum>a\<in>t. f a x) integrable_on s"
    using integrable_sum by metis
  have field_integrable_on_basis:
    "(\<lambda>x. \<Sum>b\<in>basis. F (c) \<bullet> b * (vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
    using integrable_sum'[OF assms(1) every_component_integrable]
    by auto
  then show ?thesis
    using line_integral_exists_def by auto
qed

lemma degenerate_path_is_valid_path: "valid_path (\<lambda>x. c)"
  by (auto simp add: valid_path_def piecewise_C1_differentiable_on_def continuous_on_const)

lemma line_integral_degenerate_path:
  assumes "finite basis"
  shows "line_integral F basis (\<lambda>x. c) = 0"
proof (simp add: line_integral_def)
  have "((vector_derivative (\<lambda>x. c) (at x within {0..1})) \<bullet> b) = 0" if "x \<in> {0..1}" for x b
  proof -
    have "vector_derivative (\<lambda>x. c) (at x within {0..1}) = 0"
      using that gamma_deriv_at_within[of "0" "1"] differentiable_const vector_derivative_const_at
      by fastforce
    then show "vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b = 0"
      by auto
  qed
  then have 0: "\<And>x. x \<in> {0..1} \<Longrightarrow> (\<lambda>x. \<Sum>b\<in>basis. F c \<bullet> b * (vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b)) x = (\<lambda>x. 0) x"
    by auto
  then show "integral {0..1} (\<lambda>x. \<Sum>b\<in>basis. F c \<bullet> b * (vector_derivative (\<lambda>x. c) (at x within {0..1}) \<bullet> b)) = 0"
    using integral_cong[of "{0..1}", OF 0] integral_0 by auto
qed

definition point_path where
    "point_path \<gamma> \<equiv> \<exists>c. \<gamma> = (\<lambda>x. c)"

lemma line_integral_point_path:
  assumes "point_path \<gamma>"
  assumes "finite basis"
  shows "line_integral F basis \<gamma> = 0"
  using assms(1) point_path_def line_integral_degenerate_path[OF assms(2)]
  by force

lemma line_integral_exists_point_path:
  assumes "finite basis" "point_path \<gamma>"
  shows "line_integral_exists F basis \<gamma>"
  using assms
  apply(simp add: point_path_def)
  using line_integral_exists_on_degenerate_path by auto

lemma line_integral_exists_subpath:
  assumes f: "line_integral_exists f basis g" and g: "valid_path g"
    and uv: "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
  shows "(line_integral_exists f basis (subpath u v g))"
proof (cases "v=u")
  case tr: True
  have zero: "(\<Sum>b\<in>basis. f (g u) \<bullet> b * (vector_derivative (\<lambda>x. g u) (at x within {0..1}) \<bullet> b)) = 0" if "x \<in> {0..1}" for x::real
  proof -
    have "(vector_derivative (\<lambda>x. g u) (at x within {0..1})) = 0"
      using Deriv.has_vector_derivative_const that Derivative.vector_derivative_at_within_ivl
      by fastforce
    then show "(\<Sum>b\<in>basis. f (g u) \<bullet> b * (vector_derivative (\<lambda>x. g u) (at x within {0..1}) \<bullet> b)) = 0"
      by auto
  qed
  then have "((\<lambda>x. \<Sum>b\<in>basis. f (g u)  \<bullet> b * (vector_derivative (\<lambda>x. g u) (at x within {0..1})  \<bullet> b)) has_integral 0) {0..1}"
    by (meson has_integral_is_0)
  then show ?thesis
    using f tr by (auto simp add: line_integral_def line_integral_exists_def subpath_def)
next
  case False
  obtain s where s: "\<And>x. x \<in> {0..1} - s \<Longrightarrow> g differentiable at x" and fs: "finite s"
    using g unfolding piecewise_C1_differentiable_on_def C1_differentiable_on_eq valid_path_def by blast
  have *: "((\<lambda>x. \<Sum>b\<in>basis. f (g ((v - u) * x + u))  \<bullet> b * (vector_derivative g (at ((v - u) * x + u) within {0..1})  \<bullet> b))
            has_integral (1 / (v - u)) * integral {u..v} (\<lambda>x. \<Sum>b\<in>basis. f (g (x))  \<bullet> b * (vector_derivative g (at x within {0..1})  \<bullet> b)))
           {0..1}"
    using f uv
    apply (simp add: line_integral_exists_def subpath_def)
    apply (drule integrable_on_subcbox [where a=u and b=v, simplified])
     apply (simp_all add: has_integral_integral)
    apply (drule has_integral_affinity [where m="v-u" and c=u, simplified])
     apply (simp_all add: False image_affinity_atLeastAtMost_div_diff scaleR_conv_of_real)
    apply (simp add: divide_simps False)
    done
  have vd:"\<And>x. x \<in> {0..1} \<Longrightarrow>
           x \<notin> (\<lambda>t. (v-u) *\<^sub>R t + u) -` s \<Longrightarrow>
           vector_derivative (\<lambda>x. g ((v-u) * x + u)) (at x within {0..1}) = (v-u) *\<^sub>R vector_derivative g (at ((v-u) * x + u) within {0..1})"
    using test2[OF s fs uv]
    by auto
  have arg:"\<And>x. (\<Sum>n\<in>basis. (v - u) * (f (g ((v - u) * x + u)) \<bullet> n) * (vector_derivative g (at ((v - u) * x + u) within {0..1}) \<bullet> n))
              =    (\<Sum>b\<in>basis. f (g ((v - u) * x + u)) \<bullet> b * (v - u) * (vector_derivative g (at ((v - u) * x + u) within {0..1}) \<bullet> b))"
    by (simp add: mult.commute)
  have"((\<lambda>x. \<Sum>b\<in>basis. f (g ((v - u) * x + u))  \<bullet> b * (vector_derivative (\<lambda>x. g ((v - u) * x + u)) (at x within {0..1})  \<bullet> b)) has_integral
          (integral {u..v} (\<lambda>x. \<Sum>b\<in>basis. f (g (x))  \<bullet> b * (vector_derivative g (at x within {0..1}) \<bullet> b)))) {0..1}"
    apply (cut_tac Henstock_Kurzweil_Integration.has_integral_mult_right [OF *, where c = "v-u"])
    using fs assms
    apply (simp add: False subpath_def line_integral_exists_def)
    apply (rule_tac S = "(\<lambda>t. ((v-u) *\<^sub>R t + u)) -` s" in has_integral_spike_finite)
      apply (auto simp: inj_on_def False vd finite_vimageI scaleR_conv_of_real Groups_Big.sum_distrib_left
        mult.assoc[symmetric] arg)
    done
  then show "(line_integral_exists f basis (subpath u v g))"
    by(auto simp add: line_integral_exists_def subpath_def integrable_on_def)
qed

(*This should have everything that has to do with onecubes*)

   type_synonym path = "real \<Rightarrow> (real * real)"
   type_synonym one_cube = "(real \<Rightarrow> (real * real))"
   type_synonym one_chain = "(int * path) set"
   type_synonym two_cube = "(real * real) \<Rightarrow> (real * real)"
   type_synonym two_chain = "two_cube set"


definition one_chain_line_integral :: "((real * real) \<Rightarrow> (real * real)) => ((real*real) set) \<Rightarrow> one_chain \<Rightarrow> real" where
    "one_chain_line_integral F b C \<equiv> (\<Sum>(k,g)\<in>C. k * (line_integral F b g))"

definition boundary_chain where
    "boundary_chain s \<equiv> (\<forall>(k, \<gamma>) \<in> s. k = 1 \<or> k = -1)"

fun coeff_cube_to_path::"(int * one_cube) \<Rightarrow> path" 
  where "coeff_cube_to_path (k, \<gamma>) = (if k = 1 then \<gamma> else (reversepath \<gamma>))"

fun rec_join :: "(int*path) list \<Rightarrow> path" where   
  "rec_join [] = (\<lambda>x.0)" |
  "rec_join [oneC] = coeff_cube_to_path oneC" |
  "rec_join (oneC # xs) = coeff_cube_to_path oneC +++ (rec_join xs)"

fun valid_chain_list where
  "valid_chain_list [] = True" |
  "valid_chain_list [oneC] = True" |
  "valid_chain_list (oneC#l) = (pathfinish (coeff_cube_to_path (oneC)) = pathstart (rec_join l) \<and> valid_chain_list l)"

lemma joined_is_valid:
  assumes boundary_chain: "boundary_chain (set l)" and
    valid_path: "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_path \<gamma>" and
    valid_chain_list_ass: "valid_chain_list l"
  shows "valid_path (rec_join l)"
  using assms
proof(induction l)
  case Nil
  then show ?case
    using C1_differentiable_imp_piecewise[OF C1_differentiable_on_const[of "0" "{0..1}"]]
    by (auto simp add: valid_path_def)
next
  case (Cons a l)
  have *: "valid_path (rec_join ((k::int, \<gamma>) # l))"
    if "boundary_chain (set (l))"
      "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set l \<Longrightarrow> valid_path \<gamma>')"
      "valid_chain_list l"
      "valid_path (rec_join l) "
      "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set ((k, \<gamma>) # l) \<Longrightarrow> valid_path \<gamma>')"
      "valid_chain_list ((k, \<gamma>) # l)"
      "boundary_chain (set ((k,\<gamma>) # l))" for k \<gamma> l
  proof (cases "l = []")
    case True
    with that show "valid_path (rec_join ((k, \<gamma>) # l))"
      by auto
  next
    case False
    then obtain h l' where l_nempty: "l = h#l'"
      by (meson rec_join.elims)
    then show "valid_path (rec_join ((k, \<gamma>) # l))"
    proof (simp, intro conjI impI)
      assume k_eq_1: "k = 1"
      have 0:"valid_path \<gamma>"
        using that by auto
      have 1:"pathfinish \<gamma> = pathstart (rec_join (h#l'))"
        using that(6) k_eq_1 l_nempty by auto
      show "valid_path (\<gamma> +++ rec_join (h#l'))"
        using 0 1 valid_path_join that(4) l_nempty by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg_1: "k = -1"
        using that(7)
        by (auto simp add: boundary_chain_def)
      have "valid_path \<gamma>"
        using that by auto
      then have 0: "valid_path (reversepath \<gamma>)"
        using Cauchy_Integral_Theorem.valid_path_imp_reverse
        by auto
      have 1: "pathfinish (reversepath \<gamma>) = pathstart (rec_join (h#l'))"
        using that(6) k_eq_neg_1 l_nempty by auto
      show "valid_path ((reversepath \<gamma>) +++ rec_join (h#l'))"
        using 0 1 Cauchy_Integral_Theorem.valid_path_join that(4) l_nempty by blast
    qed
  qed
  have "\<forall>ps. valid_chain_list ps \<or> (\<exists>i f p psa. ps = (i, f) # p # psa \<and> ((i = 1 \<and> pathfinish f \<noteq> pathstart (rec_join (p # psa)) \<or> i \<noteq> 1 \<and> pathfinish (reversepath f) \<noteq> pathstart (rec_join (p # psa))) \<or> \<not> valid_chain_list (p # psa)))"
    by (smt coeff_cube_to_path.elims valid_chain_list.elims(3)) 
  moreover have "boundary_chain (set l)"
    by (meson Cons.prems(1) boundary_chain_def set_subset_Cons subset_eq)
  ultimately show ?case
    using * Cons by (metis (no_types) list.set_intros(2) prod.collapse valid_chain_list.simps(3))
qed

lemma pathstart_rec_join_1:
  "pathstart (rec_join ((1, \<gamma>) # l)) = pathstart \<gamma>"
proof (cases "l = []")
  case True
  then show "pathstart (rec_join ((1, \<gamma>) # l)) = pathstart \<gamma>"
    by simp
next
  case False
  then obtain h l' where "l = h#l'"
    by (meson rec_join.elims)
  then show "pathstart (rec_join ((1, \<gamma>) # l)) = pathstart \<gamma>"
    by simp
qed

lemma pathstart_rec_join_2:
  "pathstart (rec_join ((-1, \<gamma>) # l)) = pathstart (reversepath \<gamma>)"
proof cases
  assume "l = []"
  then show "pathstart (rec_join ((- 1, \<gamma>) # l)) = pathstart (reversepath \<gamma>)"
    by simp
next
  assume "l \<noteq> [] "
  then obtain h l' where "l = h#l'"
    by (meson rec_join.elims)
  then show "pathstart (rec_join ((- 1, \<gamma>) # l)) = pathstart (reversepath \<gamma>)"
    by simp
qed

lemma pathstart_rec_join:
  "pathstart (rec_join ((1, \<gamma>) # l)) = pathstart \<gamma>"
  "pathstart (rec_join ((-1, \<gamma>) # l)) = pathstart (reversepath \<gamma>)"
  using pathstart_rec_join_1 pathstart_rec_join_2
  by auto

lemma line_integral_exists_on_rec_join:
  assumes boundary_chain: "boundary_chain (set l)" and
    valid_chain_list: "valid_chain_list l" and
    valid_path: "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_path \<gamma>" and
    line_integral_exists: "\<forall>(k, \<gamma>) \<in> set l. line_integral_exists F basis \<gamma>"
  shows "line_integral_exists F basis (rec_join l)"
  using assms
proof (induction l)
  case Nil
  then show ?case
  proof (simp add: line_integral_exists_def)
    have "\<forall>x. (vector_derivative (\<lambda>x. 0) (at x)) = 0"
      using Derivative.vector_derivative_const_at
      by auto
    then have "\<forall>x. ((\<lambda>x. 0) has_vector_derivative 0) (at x)"
      using Derivative.vector_derivative_const_at
      by auto
    then have "\<forall>x. ((\<lambda>x. 0) has_vector_derivative 0) (at x within {0..1})"
      using Derivative.vector_derivative_const_at
      by auto
    then have 0: "\<forall>x\<in>{0..1}. (vector_derivative (\<lambda>x. 0) (at x within{0..1})) = 0"
      by (simp add: gamma_deriv_at_within)
    have "(\<forall>x\<in>{0..1}. (\<Sum>b\<in>basis. F 0 \<bullet> b * (vector_derivative (\<lambda>x. 0) (at x within {0..1}) \<bullet> b)) = 0)"
      by (simp add: 0)
    then have " ((\<lambda>x. \<Sum>b\<in>basis. F 0 \<bullet> b * (vector_derivative (\<lambda>x. 0) (at x within {0..1}) \<bullet> b)) has_integral 0) {0..1}"
      by (meson has_integral_is_0)
    then show "(\<lambda>x. \<Sum>b\<in>basis. F 0 \<bullet> b * (vector_derivative (\<lambda>x. 0) (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
      by auto
  qed
next
  case (Cons a l)
  obtain k \<gamma> where aeq: "a = (k,\<gamma>)"
    by force
  show ?case
    unfolding aeq
  proof cases
    assume l_empty: "l = []"
    then show "line_integral_exists F basis (rec_join ((k, \<gamma>) # l))"
      using Cons.prems aeq line_integral_on_reverse_path(2) by fastforce
  next
    assume "l \<noteq> []"
    then obtain h l' where l_nempty: "l = h#l'"
      by (meson rec_join.elims)
    show "line_integral_exists F basis (rec_join ((k, \<gamma>) # l))"
    proof (auto simp add: l_nempty)
      assume k_eq_1: "k = 1"
      have 0: "line_integral_exists F basis \<gamma>"
        using Cons.prems(4) aeq by auto
      have 1: "line_integral_exists F basis (rec_join l)"
        by (metis (mono_tags) Cons boundary_chain_def list.set_intros(2) valid_chain_list.elims(3) valid_chain_list.simps(3))
      have 2: "valid_path \<gamma>"
        using Cons aeq by auto
      have 3:"valid_path (rec_join l)"
        by (metis (no_types) Cons.prems boundary_chain_def joined_is_valid l_nempty set_subset_Cons subsetCE valid_chain_list.simps(3))
      show "line_integral_exists F basis (\<gamma> +++ rec_join (h#l'))"
        using line_integral_distrib(2)[OF 0 1 2 3] assms l_nempty by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg_1: "k = -1"
        using Cons aeq by (simp add: boundary_chain_def)
      have gamma_valid: "valid_path \<gamma>"
        using Cons aeq by auto
      then have 2: "valid_path (reversepath \<gamma>)"
        using Cauchy_Integral_Theorem.valid_path_imp_reverse by auto
      have "line_integral_exists F basis \<gamma>"
        using Cons aeq by auto
      then have 0: "line_integral_exists F basis (reversepath \<gamma>)"
        using line_integral_on_reverse_path(2) gamma_valid
        by auto
      have 1: "line_integral_exists F basis (rec_join l)"
        using Cons aeq
        by (metis (mono_tags) boundary_chain_def insert_iff list.set(2) list.set_intros(2) valid_chain_list.elims(3) valid_chain_list.simps(3))
      have 3:"valid_path (rec_join l)"
        by (metis (no_types) Cons.prems(1) Cons.prems(2) Cons.prems(3) boundary_chain_def joined_is_valid l_nempty set_subset_Cons subsetCE valid_chain_list.simps(3))
      show "line_integral_exists F basis ((reversepath \<gamma>) +++ rec_join (h#l'))"
        using line_integral_distrib(2)[OF 0 1 2 3] assms l_nempty
        by auto
    qed
  qed
qed

lemma line_integral_exists_rec_join_cons:
  assumes "line_integral_exists F basis (rec_join ((1,\<gamma>) # l))"
    "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set ((1,\<gamma>) # l) \<Longrightarrow> valid_path \<gamma>')"
    "finite basis"
  shows "line_integral_exists F basis (\<gamma> +++ (rec_join l))"
proof cases
  assume l_empty: "l = []"
  show "line_integral_exists F basis (\<gamma> +++ rec_join l)"
    using assms(2) line_integral_distrib(2)[OF assms(1) line_integral_exists_on_degenerate_path[OF assms(3)], of "0"]
    using degenerate_path_is_valid_path
    by (fastforce simp add: l_empty)
next
  assume "l \<noteq> []"
  then obtain h l' where "l = h#l'"
    by (meson rec_join.elims)
  then show "line_integral_exists F basis (\<gamma> +++ rec_join l)"
    using assms by auto
qed

lemma line_integral_exists_rec_join_cons_2:
  assumes "line_integral_exists F basis (rec_join ((-1,\<gamma>) # l))"
    "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set ((1,\<gamma>) # l) \<Longrightarrow> valid_path \<gamma>')"
    "finite basis"
  shows "line_integral_exists F basis ((reversepath \<gamma>) +++ (rec_join l))"
proof cases
  assume l_empty: "l = []"
  show "line_integral_exists F basis ((reversepath \<gamma>) +++ rec_join l)"
    using assms(2) line_integral_distrib(2)[OF assms(1) line_integral_exists_on_degenerate_path[OF assms(3)], of "0"]
    using degenerate_path_is_valid_path
    by (auto simp add: l_empty)
next
  assume "l \<noteq> []"
  then obtain h l' where  "l = h#l'"
    by (meson rec_join.elims)
  with assms show "line_integral_exists F basis ((reversepath \<gamma>) +++ rec_join l)"
    using assms by auto
qed

lemma line_integral_exists_on_rec_join':
  assumes boundary_chain: "boundary_chain (set l)" and
    valid_chain_list: "valid_chain_list l" and
    valid_path: "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_path \<gamma>" and
    line_integral_exists: "line_integral_exists F basis (rec_join l)" and
    finite_basis: "finite basis"
  shows "\<forall>(k, \<gamma>) \<in> set l. line_integral_exists F basis \<gamma>"
  using assms
proof (induction l)
  case Nil
  show ?case
    by (simp add: line_integral_exists_def)
next
  case ass: (Cons a l)          
  obtain k \<gamma> where k_gamma:"a = (k,\<gamma>)"
    by fastforce
  show ?case
    apply (auto simp add: k_gamma)
  proof -
    show "line_integral_exists F basis \<gamma>"
    proof(cases "k = 1")
      assume k_eq_1: "k = 1"
      have 0: "line_integral_exists F basis (\<gamma> +++ (rec_join l))"
        using line_integral_exists_rec_join_cons k_eq_1 k_gamma ass(4) ass(5) ass(6)
        by auto
      have 2: "valid_path \<gamma>"
        using ass k_gamma by auto
      show "line_integral_exists F basis \<gamma>"
        using line_integral_exists_joinD1[OF 0 2]
        by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg_1: "k = -1"
        using ass k_gamma
        by (simp add: boundary_chain_def)
      have 0: "line_integral_exists F basis ((reversepath \<gamma>) +++ (rec_join l))"
        using line_integral_exists_rec_join_cons_2[OF ] k_eq_neg_1 k_gamma ass(4) ass(5) ass(6)
        by fastforce
      have gamma_valid:
        "valid_path \<gamma>"
        using ass k_gamma by auto
      then have 2: "valid_path (reversepath \<gamma>)"
        using Cauchy_Integral_Theorem.valid_path_imp_reverse by auto
      have "line_integral_exists F basis (reversepath \<gamma>)"
        using line_integral_exists_joinD1[OF 0 2] by auto
      then show "line_integral_exists F basis (\<gamma>)"
        using line_integral_on_reverse_path(2)[OF 2] reversepath_reversepath
        by auto
    qed
  next
    have 0:"boundary_chain (set l)"
      using ass(2)
      by (auto simp add: boundary_chain_def)
    have 1:"valid_chain_list l"
      using ass(3)
      apply (auto simp add: k_gamma)
      by (metis valid_chain_list.elims(3) valid_chain_list.simps(3))
    have 2:"(\<And>k \<gamma>. (k, \<gamma>) \<in> set (l) \<Longrightarrow> valid_path \<gamma>)"
      using ass(4) by auto
    have 3: "valid_path (rec_join l)"
      using joined_is_valid[OF 0] 1 2 by auto
    have 4: "line_integral_exists F basis (rec_join l)"
    proof(cases "k = 1")
      assume k_eq_1: "k = 1"
      have 0: "line_integral_exists F basis (\<gamma> +++ (rec_join l))"
        using line_integral_exists_rec_join_cons k_eq_1 k_gamma ass(4) ass(5) ass(6) by auto
      show "line_integral_exists F basis (rec_join l)"
        using line_integral_exists_joinD2[OF 0 3] by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg_1: "k = -1"
        using ass k_gamma
        by (simp add: boundary_chain_def)
      have 0: "line_integral_exists F basis ((reversepath \<gamma>) +++ (rec_join l))"
        using line_integral_exists_rec_join_cons_2[OF ] k_eq_neg_1 k_gamma ass(4) ass(5) ass(6)
        by fastforce
      show "line_integral_exists F basis (rec_join l)"
        using line_integral_exists_joinD2[OF 0 3]
        by auto
    qed
    show "\<And>a b. (a, b) \<in> set l \<Longrightarrow> line_integral_exists F basis b"
      using 0 1 2 3 4 ass(1)[OF 0 1 2] ass(6)
      by fastforce
  qed
qed

inductive chain_subdiv_path
  where I: "chain_subdiv_path \<gamma> (set l)" if "distinct l" "rec_join l = \<gamma>" "valid_chain_list l"

lemma valid_path_equiv_valid_chain_list:
  assumes path_eq_chain: "chain_subdiv_path \<gamma> one_chain" 
    and "boundary_chain one_chain" "\<forall>(k, \<gamma>) \<in> one_chain. valid_path \<gamma>"
  shows "valid_path \<gamma>"
proof -
  obtain l where l_props: "set l = one_chain" "distinct l" "rec_join l = \<gamma>" "valid_chain_list l"
    using chain_subdiv_path.cases path_eq_chain by force
  show "valid_path \<gamma>"
    using joined_is_valid assms l_props by blast
qed

lemma line_integral_rec_join_cons:
  assumes "line_integral_exists F basis \<gamma>"
    "line_integral_exists F basis (rec_join ((l)))"
    "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set ((1,\<gamma>) # l) \<Longrightarrow> valid_path \<gamma>')"
    "finite basis"
  shows "line_integral F basis (rec_join ((1,\<gamma>) # l)) = line_integral F basis (\<gamma> +++ (rec_join l))"
proof cases
  assume l_empty: "l = []"
  show "line_integral F basis (rec_join ((1,\<gamma>) # l)) = line_integral F basis (\<gamma> +++ (rec_join l))"
    using assms line_integral_distrib(1)[OF assms(1) line_integral_exists_on_degenerate_path[OF assms(4)], of "0"]
    apply (auto simp add: l_empty)
    using degenerate_path_is_valid_path line_integral_degenerate_path
    by fastforce
next
  assume "l \<noteq> []"
  then obtain h l' where l_nempty: "l = h#l'"
    by (meson rec_join.elims)
  show "line_integral F basis (rec_join ((1,\<gamma>) # l)) = line_integral F basis (\<gamma> +++ (rec_join l))"
    using assms  by (auto simp add: l_nempty)
qed

lemma line_integral_rec_join_cons_2:
  assumes "line_integral_exists F basis \<gamma>"
    "line_integral_exists F basis (rec_join ((l)))"
    "(\<And>k' \<gamma>'. (k', \<gamma>') \<in> set ((-1,\<gamma>) # l) \<Longrightarrow> valid_path \<gamma>')"
    "finite basis"
  shows "line_integral F basis (rec_join ((-1,\<gamma>) # l)) = line_integral F basis ((reversepath \<gamma>) +++ (rec_join l))"
proof cases
  assume l_empty: "l = []"
  have 0: "line_integral_exists F basis (reversepath \<gamma>)"
    using assms line_integral_on_reverse_path(2) by fastforce
  have 1: "valid_path (reversepath \<gamma>)"
    using assms  by fastforce
  show "line_integral F basis (rec_join ((-1,\<gamma>) # l)) = line_integral F basis ((reversepath \<gamma>) +++ (rec_join l))"
    using assms line_integral_distrib(1)[OF 0 line_integral_exists_on_degenerate_path[OF assms(4)], of "0"]
    apply (auto simp add: l_empty)
    using degenerate_path_is_valid_path line_integral_degenerate_path
    by fastforce
next
  assume "l \<noteq> []"
  then obtain h l' where l_nempty: "l = h#l'"
    by (meson rec_join.elims)
  show "line_integral F basis (rec_join ((-1,\<gamma>) # l)) = line_integral F basis ((reversepath \<gamma>) +++ (rec_join l))"
    using assms  by (auto simp add: l_nempty)
qed

lemma one_chain_line_integral_rec_join:
  assumes l_props: "set l = one_chain" "distinct l" "valid_chain_list l" and
    boundary_chain: "boundary_chain one_chain" and
    line_integral_exists: "\<forall>(k::int, \<gamma>) \<in> one_chain. line_integral_exists F basis \<gamma>" and
    valid_path: "\<forall>(k::int, \<gamma>) \<in> one_chain. valid_path \<gamma>" and
    finite_basis: "finite basis"
  shows "line_integral F basis (rec_join l) = one_chain_line_integral F basis one_chain"
proof -
  have 0: "sum_list (map (\<lambda>((k::int), \<gamma>). (k::int) * (line_integral F basis \<gamma>)) l) = one_chain_line_integral F basis one_chain"
    unfolding one_chain_line_integral_def
    using l_props Groups_List.comm_monoid_add_class.sum.distinct_set_conv_list[OF l_props(2), of "(\<lambda>(k, \<gamma>). (k::int) * (line_integral F basis \<gamma>))"]
    by auto
  have "valid_chain_list l \<Longrightarrow>
                    boundary_chain (set l) \<Longrightarrow>
                    (\<forall>(k::int, \<gamma>) \<in> set l. line_integral_exists F basis \<gamma>) \<Longrightarrow>
                    (\<forall>(k::int, \<gamma>) \<in> set l. valid_path \<gamma>) \<Longrightarrow>
                    line_integral F basis (rec_join l) = sum_list (map (\<lambda>(k::int, \<gamma>). k * (line_integral F basis \<gamma>)) l)"
  proof (induction l)
    case Nil
    show ?case
      unfolding line_integral_def boundary_chain_def
      apply (auto)
    proof
      have "\<forall>x. (vector_derivative (\<lambda>x. 0) (at x)) = 0"
        using Derivative.vector_derivative_const_at
        by auto
      then have "\<forall>x. ((\<lambda>x. 0) has_vector_derivative 0) (at x)"
        using Derivative.vector_derivative_const_at
        by auto
      then have "\<forall>x. ((\<lambda>x. 0) has_vector_derivative 0) (at x within {0..1})"
        using Derivative.vector_derivative_const_at
        by auto
      then have 0: "\<forall>x\<in>{0..1}. (vector_derivative (\<lambda>x. 0) (at x within{0..1})) = 0"
        by (metis (no_types) box_real(2) vector_derivative_within_cbox zero_less_one)
      have "(\<forall>x\<in>{0..1}. (\<Sum>b\<in>basis. F 0 \<bullet> b * (vector_derivative (\<lambda>x. 0) (at x within {0..1}) \<bullet> b)) = 0)"
        by (simp add: 0)
      then show "((\<lambda>x. \<Sum>b\<in>basis. F 0 \<bullet> b * (vector_derivative (\<lambda>x. 0) (at x within {0..1}) \<bullet> b)) has_integral 0) {0..1}"
        by (meson has_integral_is_0)
    qed
  next
    case ass: (Cons a l)
    obtain k::"int" and
      \<gamma>::"one_cube" where props: "a = (k,\<gamma>)"
    proof
      let ?k2 = "fst a"
      let ?\<gamma>2 = "snd a"
      show "a = (?k2, ?\<gamma>2)"
        by auto
    qed
    have "line_integral_exists F basis (rec_join (a # l))"
      using line_integral_exists_on_rec_join[OF ass(3) ass(2)] ass(5) ass(4)
      by blast
    have "boundary_chain (set l)"
      by (meson ass.prems(2) boundary_chain_def list.set_intros(2))
    have val_l: "\<And>f i. (i,f) \<in> set l \<Longrightarrow> valid_path f"
      using ass.prems(4) by fastforce
    have vcl_l: "valid_chain_list l"
      by (metis (no_types) ass.prems(1) valid_chain_list.elims(3) valid_chain_list.simps(3))
    have line_integral_exists_on_joined:
      "line_integral_exists F basis (rec_join l)"
      by (metis \<open>boundary_chain (set l)\<close> \<open>line_integral_exists F basis (rec_join (a # l))\<close> emptyE val_l vcl_l joined_is_valid line_integral_exists_joinD2 line_integral_exists_on_rec_join list.set(1) neq_Nil_conv rec_join.simps(3))
    have "valid_path (rec_join (a # l))"
      using joined_is_valid ass(5) ass(3) ass(2) by blast
    then have joined_is_valid: "valid_path (rec_join l)"
      using \<open>boundary_chain (set l)\<close> val_l vcl_l joined_is_valid by blast
    show ?case
    proof (clarsimp, cases)
      assume k_eq_1: "(k::int) = 1"
      have line_integral_exists_on_gamma: "line_integral_exists F basis \<gamma>"
        using ass props by auto
      have gamma_is_valid: "valid_path \<gamma>"
        using ass props by auto
      have line_int_rw: "line_integral F basis (rec_join ((k, \<gamma>) # l)) = line_integral F basis (\<gamma> +++ rec_join l)"
      proof -
        have gam_int: "line_integral_exists F basis \<gamma>" using ass props by auto
        have rec_join_int: "line_integral_exists F basis (rec_join l)"
          using line_integral_exists_on_rec_join
          using line_integral_exists_on_joined by blast
        show ?thesis
          using line_integral_rec_join_cons[OF gam_int rec_join_int] ass k_eq_1 finite_basis props by force
      qed
      show "line_integral F basis (rec_join (a # l)) =
            (case a of (x, \<gamma>) \<Rightarrow> real_of_int x * line_integral F basis \<gamma>) + (\<Sum>(x, \<gamma>)\<leftarrow>l. real_of_int x * line_integral F basis \<gamma>)"
        apply (simp add: props line_int_rw)
        using line_integral_distrib[OF line_integral_exists_on_gamma line_integral_exists_on_joined gamma_is_valid joined_is_valid]
          ass k_eq_1 vcl_l
        by (auto simp: boundary_chain_def props)
    next
      assume "k \<noteq> 1"
      then have k_eq_neg_1: "k = -1"
        using ass props
        by (auto simp add: boundary_chain_def)
      have line_integral_exists_on_gamma:
        "line_integral_exists F basis (reversepath \<gamma>)"
        using line_integral_on_reverse_path ass props
        by auto
      have gamma_is_valid: "valid_path (reversepath \<gamma>)"
        using Cauchy_Integral_Theorem.valid_path_imp_reverse ass props by auto
      have line_int_rw: "line_integral F basis (rec_join ((k, \<gamma>) # l)) = line_integral F basis ((reversepath \<gamma>) +++ rec_join l)"
      proof -
        have gam_int: "line_integral_exists F basis \<gamma>" using ass props by auto
        have rec_join_int: "line_integral_exists F basis (rec_join l)"
          using line_integral_exists_on_rec_join
          using line_integral_exists_on_joined by blast
        show ?thesis
          using line_integral_rec_join_cons_2[OF gam_int rec_join_int]
          using ass k_eq_neg_1
          using finite_basis props by blast
      qed
      show "line_integral F basis (rec_join (a # l)) =
            (case a of (x, \<gamma>) \<Rightarrow> real_of_int x * line_integral F basis \<gamma>) + (\<Sum>(x, \<gamma>)\<leftarrow>l. real_of_int x * line_integral F basis \<gamma>)"
        apply (simp add: props line_int_rw)
        using line_integral_distrib[OF line_integral_exists_on_gamma line_integral_exists_on_joined gamma_is_valid joined_is_valid]
          props ass line_integral_on_reverse_path(1)[of "\<gamma>" "F" "basis"] k_eq_neg_1
        using \<open>boundary_chain (set l)\<close> vcl_l by auto
    qed
  qed
  then have 1:"line_integral F basis (rec_join l) = sum_list (map (\<lambda>(k::int, \<gamma>). k * (line_integral F basis \<gamma>)) l)"
    using l_props assms by auto
  then show ?thesis
    using 0 1 by auto
qed

lemma line_integral_on_path_eq_line_integral_on_equiv_chain:
  assumes path_eq_chain: "chain_subdiv_path \<gamma> one_chain" and
    boundary_chain: "boundary_chain one_chain" and
    line_integral_exists: "\<forall>(k::int, \<gamma>) \<in> one_chain. line_integral_exists F basis \<gamma>" and
    valid_path: "\<forall>(k::int, \<gamma>) \<in> one_chain. valid_path \<gamma>" and
    finite_basis: "finite basis"
  shows "one_chain_line_integral F basis one_chain = line_integral F basis \<gamma>"
    "line_integral_exists F basis \<gamma>"
    "valid_path \<gamma>"
proof -
  obtain l where l_props: "set l = one_chain" "distinct l" "rec_join l = \<gamma>" "valid_chain_list l"
    using chain_subdiv_path.cases path_eq_chain by force
  show "line_integral_exists F basis \<gamma>"
    using line_integral_exists_on_rec_join assms l_props
    by blast
  show "valid_path \<gamma>"
    using joined_is_valid assms l_props
    by blast
  have "line_integral F basis (rec_join l) = one_chain_line_integral F basis one_chain"
    using one_chain_line_integral_rec_join l_props assms by auto
  then show "one_chain_line_integral F basis one_chain = line_integral F basis \<gamma>"
    using l_props
    by auto
qed

lemma line_integral_on_path_eq_line_integral_on_equiv_chain':
  assumes path_eq_chain: "chain_subdiv_path \<gamma> one_chain" and
    boundary_chain: "boundary_chain one_chain" and
    line_integral_exists: "line_integral_exists F basis \<gamma>" and
    valid_path: "\<forall>(k, \<gamma>) \<in> one_chain. valid_path \<gamma>" and
    finite_basis: "finite basis"
  shows "one_chain_line_integral F basis one_chain = line_integral F basis \<gamma>"
    "\<forall>(k, \<gamma>) \<in> one_chain. line_integral_exists F basis \<gamma>"
proof -
  obtain l where l_props: "set l = one_chain" "distinct l" "rec_join l = \<gamma>" "valid_chain_list l"
    using chain_subdiv_path.cases path_eq_chain by force
  show 0: "\<forall>(k, \<gamma>) \<in> one_chain. line_integral_exists F basis \<gamma>"
    using line_integral_exists_on_rec_join' assms l_props
    by blast
  show "one_chain_line_integral F basis one_chain = line_integral F basis \<gamma>"
    using line_integral_on_path_eq_line_integral_on_equiv_chain(1)[OF assms(1) assms(2) 0 assms(4) assms(5)] by auto
qed

definition chain_subdiv_chain where
  "chain_subdiv_chain one_chain1 subdiv
        \<equiv> \<exists>f. (\<Union>(f ` one_chain1)) = subdiv \<and>
              (\<forall>c\<in>one_chain1. chain_subdiv_path (coeff_cube_to_path c) (f c)) \<and>
              pairwise (\<lambda> p p'. f p \<inter> f p' = {}) one_chain1 \<and>
              (\<forall>x \<in> one_chain1. finite (f x))"

lemma chain_subdiv_chain_character:
  shows "chain_subdiv_chain one_chain1 subdiv \<longleftrightarrow>
        (\<exists>f. \<Union>(f ` one_chain1) = subdiv \<and>
             (\<forall>(k, \<gamma>)\<in>one_chain1.
                 if k = 1
                 then chain_subdiv_path \<gamma> (f (k, \<gamma>))
                 else chain_subdiv_path (reversepath \<gamma>) (f (k, \<gamma>))) \<and>
             (\<forall>p\<in>one_chain1.
                 \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {}) \<and>
             (\<forall>x\<in>one_chain1. finite (f x)))"  
  unfolding chain_subdiv_chain_def
  by (safe; intro exI conjI iffI; fastforce simp add: pairwise_def)

lemma chain_subdiv_chain_imp_finite_subdiv:
  assumes "finite one_chain1"
    "chain_subdiv_chain one_chain1 subdiv"
  shows "finite subdiv"
  using assms by(auto simp add: chain_subdiv_chain_def)

lemma valid_subdiv_imp_valid_one_chain:
  assumes chain1_eq_chain2: "chain_subdiv_chain one_chain1 subdiv" and
    boundary_chain1: "boundary_chain one_chain1" and
    boundary_chain2: "boundary_chain subdiv" and
    valid_path: "\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>"
  shows "\<forall>(k, \<gamma>) \<in> one_chain1. valid_path \<gamma>"
proof -
  obtain f where f_props:
    "((\<Union>(f ` one_chain1)) = subdiv)"
    "(\<forall>(k,\<gamma>)\<in>one_chain1. if k = 1 then chain_subdiv_path \<gamma> (f(k,\<gamma>)) else chain_subdiv_path (reversepath \<gamma>) (f(k,\<gamma>)))"
    "(\<forall>p\<in>one_chain1. \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {})"
    using chain1_eq_chain2 chain_subdiv_chain_character by auto
  have "\<And> k \<gamma>. (k,\<gamma>) \<in> one_chain1\<Longrightarrow> valid_path \<gamma>"
  proof-
    fix k \<gamma>
    assume ass: "(k,\<gamma>) \<in> one_chain1"
    show "valid_path \<gamma>"
    proof (cases "k = 1")
      assume k_eq_1: "k = 1"
      then have i:"chain_subdiv_path \<gamma> (f(k,\<gamma>))"
        using f_props(2) ass by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms
        apply (simp add: boundary_chain_def)
        by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms
        by blast
      show ?thesis
        using valid_path_equiv_valid_chain_list[OF i ii iv]
        by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg1: "k = -1"
        using ass boundary_chain1
        by (auto simp add: boundary_chain_def)
      then have i:"chain_subdiv_path (reversepath \<gamma>) (f(k,\<gamma>))"
        using f_props(2) ass using \<open>k \<noteq> 1\<close> by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms by (auto simp add: boundary_chain_def)
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms
        by blast
      have "valid_path (reversepath \<gamma>)"
        using valid_path_equiv_valid_chain_list[OF i ii iv]
        by auto
      then show ?thesis
        using  reversepath_reversepath Cauchy_Integral_Theorem.valid_path_imp_reverse
        by force
    qed
  qed
  then show valid_path1: "\<forall>(k, \<gamma>) \<in> one_chain1. valid_path \<gamma>"
    by auto
qed

lemma one_chain_line_integral_eq_line_integral_on_sudivision:
  assumes chain1_eq_chain2: "chain_subdiv_chain one_chain1 subdiv" and
    boundary_chain1: "boundary_chain one_chain1" and
    boundary_chain2: "boundary_chain subdiv" and
    line_integral_exists_on_chain2: "\<forall>(k, \<gamma>) \<in> subdiv. line_integral_exists F basis \<gamma>" and
    valid_path: "\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>" and
    finite_chain1: "finite one_chain1" and
    finite_basis: "finite basis"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv"
    "\<forall>(k, \<gamma>) \<in> one_chain1. line_integral_exists F basis \<gamma>"
proof -
  obtain f where f_props:
    "((\<Union>(f ` one_chain1)) = subdiv)"
    "(\<forall>(k,\<gamma>)\<in>one_chain1. if k = 1 then chain_subdiv_path \<gamma> (f(k,\<gamma>)) else chain_subdiv_path (reversepath \<gamma>) (f(k,\<gamma>)))"
    "(\<forall>p\<in>one_chain1. \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {})"
    "(\<forall>x \<in> one_chain1. finite (f x))"
    using chain1_eq_chain2 chain_subdiv_chain_character by (auto simp add: pairwise_def chain_subdiv_chain_def)
  then have 0: "one_chain_line_integral F basis subdiv = one_chain_line_integral F basis (\<Union>(f ` one_chain1))"
    by auto
  have finite_chain2: "finite subdiv"
    using finite_chain1 f_props(1) f_props(4)
    apply (simp add: image_def)
    using f_props(1) by auto
  have "\<And> k \<gamma>. (k,\<gamma>) \<in> one_chain1\<Longrightarrow> line_integral_exists F basis \<gamma>"
  proof-
    fix k \<gamma>
    assume ass: "(k,\<gamma>) \<in> one_chain1"
    show "line_integral_exists F basis \<gamma>"
    proof (cases "k = 1")
      assume k_eq_1: "k = 1"
      then have i:"chain_subdiv_path \<gamma> (f(k,\<gamma>))"
        using f_props(2) ass by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms by (auto simp add: boundary_chain_def)
      have iii:"\<forall>(k, \<gamma>)\<in>f (k, \<gamma>). line_integral_exists F basis \<gamma>"
        using f_props(1) ass assms
        by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms
        by blast
      show ?thesis
        using line_integral_on_path_eq_line_integral_on_equiv_chain(2)[OF i ii iii iv finite_basis]
        by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg1: "k = -1"
        using ass boundary_chain1
        by (auto simp add: boundary_chain_def)
      then have i:"chain_subdiv_path (reversepath \<gamma>) (f(k,\<gamma>))"
        using f_props(2) ass by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms by (auto simp add: boundary_chain_def)
      have iii:"\<forall>(k, \<gamma>)\<in>f (k, \<gamma>). line_integral_exists F basis \<gamma>"
        using f_props(1) ass assms
        by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms
        by blast
      have x:"line_integral_exists F basis (reversepath \<gamma>)"
        using line_integral_on_path_eq_line_integral_on_equiv_chain(2)[OF i ii iii iv finite_basis]
        by auto
      have "valid_path (reversepath \<gamma>)"
        using line_integral_on_path_eq_line_integral_on_equiv_chain(3)[OF i ii iii iv finite_basis]
        by auto
      then show ?thesis
        using line_integral_on_reverse_path(2) reversepath_reversepath x
        by fastforce
    qed
  qed
  then show line_integral_exists_on_chain1: "\<forall>(k, \<gamma>) \<in> one_chain1. line_integral_exists F basis \<gamma>"
    by auto
  have 1: "one_chain_line_integral F basis (\<Union>(f ` one_chain1)) = one_chain_line_integral F basis one_chain1"
  proof -
    have 0:"one_chain_line_integral F basis (\<Union>(f ` one_chain1)) =
                           (\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain)"
    proof -
      have finite: "\<forall>chain \<in> (f ` one_chain1). finite chain"
        using f_props(1) finite_chain2
        by (meson Sup_upper finite_subset)
      have disj: " \<forall>A\<in>f ` one_chain1. \<forall>B\<in>f ` one_chain1. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
        by (metis (no_types, hide_lams) f_props(3) image_iff)
      show "one_chain_line_integral F basis (\<Union>(f ` one_chain1)) =
                                (\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain)"
        using Groups_Big.comm_monoid_add_class.sum.Union_disjoint[OF finite disj]
          one_chain_line_integral_def
        by auto
    qed
    have 1:"(\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain) =
                            one_chain_line_integral F basis one_chain1"
    proof -
      have "(\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain) =
                                     (\<Sum>(k,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>))"
      proof -
        have i:"(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                       (\<Sum>(k,\<gamma>)\<in>one_chain1 - {p. f p = {}}. k*(line_integral F basis \<gamma>))"
        proof -
          have "inj_on f (one_chain1 - {p. f p = {}})"
            unfolding inj_on_def using f_props(3) by blast
          then have 0: "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain)
                                                       = (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). one_chain_line_integral F basis (f (k, \<gamma>)))"
            using Groups_Big.comm_monoid_add_class.sum.reindex
            by auto
          have "\<And> k \<gamma>. (k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}) \<Longrightarrow>
                        one_chain_line_integral F basis (f(k, \<gamma>)) = k* (line_integral F basis \<gamma>)"
          proof-
            fix k \<gamma>
            assume ass: "(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}})"
            have bchain: "boundary_chain (f(k,\<gamma>))"
              using f_props(1) boundary_chain2 ass
              by (auto simp add: boundary_chain_def)
            have wexist: "\<forall>(k, \<gamma>)\<in>(f(k,\<gamma>)). line_integral_exists F basis \<gamma>"
              using f_props(1) line_integral_exists_on_chain2 ass
              by blast
            have vpath: " \<forall>(k, \<gamma>)\<in>(f(k, \<gamma>)). valid_path \<gamma>"
              using f_props(1) assms ass
              by blast
            show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
            proof(cases "k = 1")
              assume k_eq_1: "k = 1"
              have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis \<gamma>"
                using f_props(2) k_eq_1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
                by auto
              then show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
                using k_eq_1  by auto
            next
              assume "k \<noteq> 1"
              then have k_eq_neg1: "k = -1"
                using ass boundary_chain1
                by (auto simp add: boundary_chain_def)
              have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis (reversepath \<gamma>)"
                using f_props(2) k_eq_neg1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
                by auto
              then have "one_chain_line_integral F basis (f (k, \<gamma>)) = - (line_integral F basis \<gamma>)"
                using line_integral_on_reverse_path(1) ass line_integral_exists_on_chain1
                  valid_subdiv_imp_valid_one_chain[OF chain1_eq_chain2 boundary_chain1 boundary_chain2 valid_path]
                by force
              then show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
                using k_eq_neg1 by auto
            qed
          qed
          then have "(\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). one_chain_line_integral F basis (f (k, \<gamma>)))
                   = (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). k* (line_integral F basis \<gamma>))"
            by (auto intro!: Finite_Cartesian_Product.sum_cong_aux)
          then show "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                     (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). k* (line_integral F basis \<gamma>))"
            using 0  by auto
        qed
        have "\<And> (k::int) \<gamma>. (k, \<gamma>) \<in> one_chain1 \<Longrightarrow> (f (k, \<gamma>) = {}) \<Longrightarrow> (k, \<gamma>) \<in> {(k',\<gamma>'). k'* (line_integral F basis \<gamma>') = 0}"
        proof-
          fix k::"int"
          fix \<gamma>::"one_cube"
          assume ass:"(k, \<gamma>) \<in> one_chain1"
            "(f (k, \<gamma>) = {})"
          then have zero_line_integral:"one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
            using one_chain_line_integral_def
            by auto
          have bchain: "boundary_chain (f(k,\<gamma>))"
            using f_props(1) boundary_chain2 ass
            by (auto simp add: boundary_chain_def)
          have wexist: "\<forall>(k, \<gamma>)\<in>(f(k,\<gamma>)). line_integral_exists F basis \<gamma>"
            using f_props(1) line_integral_exists_on_chain2 ass
            by blast
          have vpath: " \<forall>(k, \<gamma>)\<in>(f(k, \<gamma>)). valid_path \<gamma>"
            using f_props(1) assms ass by blast
          have "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
          proof(cases "k = 1")
            assume k_eq_1: "k = 1"
            have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis \<gamma>"
              using f_props(2) k_eq_1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
              by auto
            then show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
              using k_eq_1
              by auto
          next
            assume "k \<noteq> 1"
            then have k_eq_neg1: "k = -1"
              using ass boundary_chain1
              by (auto simp add: boundary_chain_def)
            have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis (reversepath \<gamma>)"
              using f_props(2) k_eq_neg1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
              by auto
            then have "one_chain_line_integral F basis (f (k, \<gamma>)) = - (line_integral F basis \<gamma>)"
              using line_integral_on_reverse_path(1)  ass line_integral_exists_on_chain1
                valid_subdiv_imp_valid_one_chain[OF chain1_eq_chain2 boundary_chain1 boundary_chain2 valid_path]
              by force
            then show "one_chain_line_integral F basis (f (k::int, \<gamma>)) = k * line_integral F basis \<gamma>"
              using k_eq_neg1  by auto
          qed
          then show "(k, \<gamma>) \<in> {(k'::int, \<gamma>'). k' * line_integral F basis \<gamma>' = 0}"
            using zero_line_integral by auto
        qed
        then have ii:"(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                          (\<Sum>one_chain \<in> (f ` (one_chain1)). one_chain_line_integral F basis one_chain)"
        proof -
          have "\<And>one_chain. one_chain \<in> (f ` (one_chain1)) - (f ` (one_chain1 - {p. f p = {}})) \<Longrightarrow>
                                                         one_chain_line_integral F basis one_chain = 0"
          proof -
            fix one_chain
            assume "one_chain \<in> (f ` (one_chain1)) - (f ` (one_chain1 - {p. f p = {}}))"
            then show "one_chain_line_integral F basis one_chain = 0"
              by (auto simp add: one_chain_line_integral_def)
          qed
          then have 0:"(\<Sum>one_chain \<in> f ` (one_chain1) - (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain)
                                                       = 0"
            using comm_monoid_add_class.sum.neutral by auto
          then have "(\<Sum>one_chain \<in> f ` (one_chain1). one_chain_line_integral F basis one_chain)
                                                      - (\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain)
                                                       = 0"
          proof -
            have finte: "finite (f ` one_chain1)" using finite_chain1 by auto
            show ?thesis
              using Groups_Big.sum_diff[OF finte, of " (f ` (one_chain1 - {p. f p = {}}))"
                  "one_chain_line_integral F basis"]
                0
              by auto
          qed
          then show "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                          (\<Sum>one_chain \<in> (f ` (one_chain1)). one_chain_line_integral F basis one_chain)"
            by auto
        qed
        have "\<And> (k::int) \<gamma>. (k, \<gamma>) \<in> one_chain1 \<Longrightarrow> (f (k, \<gamma>) = {}) \<Longrightarrow> f (k, \<gamma>) \<in> {chain. one_chain_line_integral F basis chain = 0}"
        proof-
          fix k::"int"
          fix \<gamma>::"one_cube"
          assume ass:"(k, \<gamma>) \<in> one_chain1" "(f (k, \<gamma>) = {})"
          then have "one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
            using one_chain_line_integral_def  by auto
          then show "f (k, \<gamma>) \<in> {p'. (one_chain_line_integral F basis p' = 0)}"
            by auto
        qed
        then have iii:"(\<Sum>(k::int,\<gamma>)\<in>one_chain1 - {p. f p = {}}. k*(line_integral F basis \<gamma>))
                                                 = (\<Sum>(k::int,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>))"
        proof-
          have "\<And> k \<gamma>. (k,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}})
                                                    \<Longrightarrow> k* (line_integral F basis \<gamma>) = 0"
          proof-
            fix k \<gamma>
            assume ass: "(k,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}})"
            then have "f(k, \<gamma>) = {}"
              by auto
            then have "one_chain_line_integral F basis (f(k, \<gamma>)) = 0"
              by (auto simp add: one_chain_line_integral_def)
            then have zero_line_integral:"one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
              using one_chain_line_integral_def by auto
            have bchain: "boundary_chain (f(k,\<gamma>))"
              using f_props(1) boundary_chain2 ass
              by (auto simp add: boundary_chain_def)
            have wexist: "\<forall>(k, \<gamma>)\<in>(f(k,\<gamma>)). line_integral_exists F basis \<gamma>"
              using f_props(1) line_integral_exists_on_chain2 ass
              by blast
            have vpath: " \<forall>(k, \<gamma>)\<in>(f(k, \<gamma>)). valid_path \<gamma>"
              using f_props(1) assms ass
              by blast
            have "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
            proof(cases "k = 1")
              assume k_eq_1: "k = 1"
              have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis \<gamma>"
                using f_props(2) k_eq_1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
                by auto
              then show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
                using k_eq_1
                by auto
            next
              assume "k \<noteq> 1"
              then have k_eq_neg1: "k = -1"
                using ass boundary_chain1
                by (auto simp add: boundary_chain_def)
              have "one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis (reversepath \<gamma>)"
                using f_props(2) k_eq_neg1 line_integral_on_path_eq_line_integral_on_equiv_chain bchain wexist vpath ass finite_basis
                by auto
              then have "one_chain_line_integral F basis (f (k, \<gamma>)) = - (line_integral F basis \<gamma>)"
                using line_integral_on_reverse_path(1)  ass line_integral_exists_on_chain1
                  valid_subdiv_imp_valid_one_chain[OF chain1_eq_chain2 boundary_chain1 boundary_chain2 valid_path]
                by force
              then show "one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
                using k_eq_neg1
                by auto
            qed
            then show "k* (line_integral F basis \<gamma>) = 0"
              using zero_line_integral
              by auto
          qed
          then have "\<forall>(k::int,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}).
                                                      k* (line_integral F basis \<gamma>) = 0" by auto
          then have "(\<Sum>(k::int,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}). k*(line_integral F basis \<gamma>)) = 0"
            using Groups_Big.comm_monoid_add_class.sum.neutral
              [of "one_chain1 - (one_chain1 - {p. f p = {}})" "(\<lambda>(k::int,\<gamma>). k* (line_integral F basis \<gamma>))"]
            by (simp add: split_beta)
          then have "(\<Sum>(k::int,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>)) -
                     (\<Sum>(k::int,\<gamma>)\<in> (one_chain1 - {p. f p = {}}). k*(line_integral F basis \<gamma>)) = 0"
            using Groups_Big.sum_diff[OF finite_chain1]
            by (metis (no_types) Diff_subset \<open>(\<Sum>(k, \<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}). k * line_integral F basis \<gamma>) = 0\<close> \<open>\<And>f B. B \<subseteq> one_chain1 \<Longrightarrow> sum f (one_chain1 - B) = sum f one_chain1 - sum f B\<close>)
          then show ?thesis by auto
        qed
        show ?thesis using i ii iii by auto
      qed
      then show ?thesis using one_chain_line_integral_def by auto
    qed
    show ?thesis using 0 1 by auto
  qed
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv" using 0 1 by auto
qed

lemma one_chain_line_integral_eq_line_integral_on_sudivision':
  assumes chain1_eq_chain2: "chain_subdiv_chain one_chain1 subdiv" and
    boundary_chain1: "boundary_chain one_chain1" and
    boundary_chain2: "boundary_chain subdiv" and
    line_integral_exists_on_chain1: "\<forall>(k, \<gamma>) \<in> one_chain1. line_integral_exists F basis \<gamma>" and
    valid_path: "\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>" and
    finite_chain1: "finite one_chain1" and
    finite_basis: "finite basis"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv"
    "\<forall>(k, \<gamma>) \<in> subdiv. line_integral_exists F basis \<gamma>"
proof -
  obtain f where f_props:
    "((\<Union>(f ` one_chain1)) = subdiv)"
    "(\<forall>(k,\<gamma>)\<in>one_chain1. if k = 1 then chain_subdiv_path \<gamma> (f(k,\<gamma>)) else chain_subdiv_path (reversepath \<gamma>) (f(k,\<gamma>)))"
    "(\<forall>p\<in>one_chain1. \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {})"
    "(\<forall>x \<in> one_chain1. finite (f x))"
    using chain1_eq_chain2 chain_subdiv_chain_character by (auto simp add: pairwise_def chain_subdiv_chain_def)
  have finite_chain2: "finite subdiv"
    using finite_chain1 f_props(1) f_props(4) by blast
  have "\<And>k \<gamma>. (k, \<gamma>) \<in> subdiv \<Longrightarrow> line_integral_exists F basis \<gamma>"
  proof -
    fix k \<gamma>
    assume ass: "(k, \<gamma>) \<in> subdiv"
    then obtain k' \<gamma>' where kp_gammap: "(k',\<gamma>') \<in> one_chain1" "(k,\<gamma>) \<in> f(k',\<gamma>')"
      using f_props(1) by fastforce
    show "line_integral_exists F basis \<gamma>"
    proof (cases "k' = 1")
      assume k_eq_1: "k' = 1"
      then have i:"chain_subdiv_path \<gamma>' (f(k',\<gamma>'))"
        using f_props(2) kp_gammap ass  by auto
      have ii:"boundary_chain (f(k',\<gamma>'))"
        using f_props(1) ass assms kp_gammap  by (meson UN_I boundary_chain_def)
      have iii:"line_integral_exists F basis \<gamma>'"
        using assms kp_gammap by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k', \<gamma>'). valid_path \<gamma>"
        using f_props(1) ass assms kp_gammap by blast
      show ?thesis
        using line_integral_on_path_eq_line_integral_on_equiv_chain'(2)[OF i ii iii iv finite_basis] kp_gammap
        by auto
    next
      assume "k' \<noteq> 1"
      then have k_eq_neg1: "k' = -1"
        using boundary_chain1 kp_gammap
        by (auto simp add: boundary_chain_def)
      then have i:"chain_subdiv_path (reversepath \<gamma>') (f(k',\<gamma>'))"
        using f_props(2) kp_gammap by auto
      have ii:"boundary_chain (f(k',\<gamma>'))"
        using f_props(1) assms kp_gammap  by (meson UN_I boundary_chain_def)
      have iii: " \<forall>(k, \<gamma>)\<in>f (k', \<gamma>'). valid_path \<gamma>"
        using f_props(1) ass assms kp_gammap by blast
      have iv: "valid_path (reversepath \<gamma>')"
        using valid_path_equiv_valid_chain_list[OF i ii iii]
        by force
      have "line_integral_exists F basis \<gamma>'"
        using assms kp_gammap  by blast
      then have x: "line_integral_exists F basis (reversepath \<gamma>')"
        using iv line_integral_on_reverse_path(2) valid_path_reversepath
        by fastforce
      show ?thesis
        using line_integral_on_path_eq_line_integral_on_equiv_chain'(2)[OF i ii x iii finite_basis] kp_gammap
        by auto
    qed
  qed
  then show "\<forall>(k, \<gamma>)\<in>subdiv. line_integral_exists F basis \<gamma>" by auto
  then show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv"
    using one_chain_line_integral_eq_line_integral_on_sudivision(1) assms
    by auto
qed

lemma line_integral_sum_gen:
  assumes finite_basis:
    "finite basis" and
    line_integral_exists:
    "line_integral_exists F basis1 \<gamma>"
    "line_integral_exists F basis2 \<gamma>" and
    basis_partition:
    "basis1 \<union> basis2 = basis" "basis1 \<inter> basis2 = {}"
  shows "line_integral F basis \<gamma> = (line_integral F  basis1 \<gamma>) + (line_integral F basis2 \<gamma>)"
    "line_integral_exists F basis \<gamma>"
   apply (simp add: line_integral_def)
proof -
  have 0: "integral {0..1} (\<lambda>x. (\<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                                       (\<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))) =
                    integral {0..1} (\<lambda>x. \<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                           integral {0..1} (\<lambda>x. \<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))"
    using Henstock_Kurzweil_Integration.integral_add line_integral_exists
    by (auto simp add: line_integral_exists_def)
  have 1: "integral {0..1} (\<lambda>x. \<Sum>b\<in>basis. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) =
                       integral {0..1} (\<lambda>x. (\<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                                            (\<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)))"
    by (metis (mono_tags, lifting) basis_partition finite_Un finite_basis sum.union_disjoint)
  show "integral {0..1} (\<lambda>x. \<Sum>b\<in>basis. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) =
                  integral {0..1} (\<lambda>x. \<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                  integral {0..1} (\<lambda>x. \<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))"
    using 0 1
    by auto
  have 2: "((\<lambda>x. (\<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                                       (\<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))) has_integral
                    integral {0..1} (\<lambda>x. \<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                           integral {0..1} (\<lambda>x. \<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))) {0..1}"
    using Henstock_Kurzweil_Integration.has_integral_add line_integral_exists has_integral_integral
    apply (auto simp add: line_integral_exists_def)
    by blast
  have 3: "(\<lambda>x. \<Sum>b\<in>basis. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) =
                       (\<lambda>x. (\<Sum>b\<in>basis1. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) +
                                            (\<Sum>b\<in>basis2. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)))"
    by (metis (mono_tags, lifting) basis_partition finite_Un finite_basis sum.union_disjoint)
  show "line_integral_exists F basis \<gamma>"
    apply(auto simp add: line_integral_exists_def has_integral_integral)
    using 2 3
    using has_integral_integrable_integral by fastforce
qed

definition common_boundary_sudivision_exists where
    "common_boundary_sudivision_exists one_chain1 one_chain2 \<equiv>
             \<exists>subdiv. chain_subdiv_chain one_chain1 subdiv \<and>
                      chain_subdiv_chain one_chain2 subdiv \<and>
                      (\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>)\<and>
                      boundary_chain subdiv"

lemma common_boundary_sudivision_commutative:
  "(common_boundary_sudivision_exists one_chain1 one_chain2) = (common_boundary_sudivision_exists one_chain2 one_chain1)"
  apply (simp add: common_boundary_sudivision_exists_def)
  by blast

lemma common_subdivision_imp_eq_line_integral:
  assumes "(common_boundary_sudivision_exists one_chain1 one_chain2)"
    "boundary_chain one_chain1"
    "boundary_chain one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    "finite one_chain1"
    "finite one_chain2"
    "finite basis"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain2. line_integral_exists F basis \<gamma>"
proof -
  obtain subdiv where subdiv_props:
    "chain_subdiv_chain one_chain1 subdiv"
    "chain_subdiv_chain one_chain2 subdiv"
    "(\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>)"
    "(boundary_chain subdiv)"
    using assms
    by (auto simp add: common_boundary_sudivision_exists_def)
  have i: "\<forall>(k, \<gamma>)\<in>subdiv. line_integral_exists F basis \<gamma>"
    using one_chain_line_integral_eq_line_integral_on_sudivision'(2)[OF subdiv_props(1) assms(2) subdiv_props(4) assms(4) subdiv_props(3) assms(5) assms(7)]
    by auto
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    using one_chain_line_integral_eq_line_integral_on_sudivision'(1)[OF subdiv_props(1) assms(2) subdiv_props(4) assms(4) subdiv_props(3) assms(5) assms(7)]
      one_chain_line_integral_eq_line_integral_on_sudivision(1)[OF subdiv_props(2) assms(3) subdiv_props(4) i subdiv_props(3) assms(6) assms(7)]
    by auto
  show "\<forall>(k, \<gamma>)\<in>one_chain2. line_integral_exists F basis \<gamma>"
    using one_chain_line_integral_eq_line_integral_on_sudivision(2)[OF subdiv_props(2) assms(3) subdiv_props(4) i subdiv_props(3) assms(6) assms(7)]
    by auto
qed

definition common_sudiv_exists where
    "common_sudiv_exists one_chain1 one_chain2 \<equiv>
        \<exists>subdiv ps1 ps2. chain_subdiv_chain (one_chain1 - ps1) subdiv \<and>
                  chain_subdiv_chain (one_chain2 - ps2) subdiv \<and>
                  (\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>) \<and>
                  (boundary_chain subdiv) \<and>
                  (\<forall>(k, \<gamma>) \<in> ps1. point_path \<gamma>) \<and>
                  (\<forall>(k, \<gamma>) \<in> ps2. point_path \<gamma>)"

lemma common_sudiv_exists_comm:
  shows "common_sudiv_exists C1 C2 = common_sudiv_exists C2 C1"
  by (auto simp add: common_sudiv_exists_def)

lemma line_integral_degenerate_chain:
  assumes "(\<forall>(k, \<gamma>) \<in> chain. point_path \<gamma>)"
  assumes "finite basis"
  shows "one_chain_line_integral F basis chain = 0"
proof (simp add: one_chain_line_integral_def)
  have "\<forall>(k,g)\<in>chain. line_integral F basis g = 0"
    using assms line_integral_point_path
    by blast
  then have "\<forall>(k,g)\<in>chain. real_of_int k * line_integral F basis g = 0" by auto
  then have "\<And>p. p \<in> chain \<Longrightarrow> (case p of (i, f) \<Rightarrow> real_of_int i * line_integral F basis f) = 0"
    by fastforce
  then show "(\<Sum>x\<in>chain. case x of (k, g) \<Rightarrow> real_of_int k * line_integral F basis g) = 0"
    by simp
qed

lemma gen_common_subdiv_imp_common_subdiv:
  shows "(common_sudiv_exists one_chain1 one_chain2) = (\<exists>ps1 ps2. (common_boundary_sudivision_exists (one_chain1 - ps1) (one_chain2 - ps2)) \<and> (\<forall>(k, \<gamma>)\<in>ps1. point_path \<gamma>) \<and> (\<forall>(k, \<gamma>)\<in>ps2. point_path \<gamma>))"
  by (auto simp add: common_sudiv_exists_def common_boundary_sudivision_exists_def)

lemma common_subdiv_imp_gen_common_subdiv:
  assumes "(common_boundary_sudivision_exists one_chain1 one_chain2)"
  shows "(common_sudiv_exists one_chain1 one_chain2)"
  using assms
  apply (auto simp add: common_sudiv_exists_def common_boundary_sudivision_exists_def)
  by (metis Diff_empty all_not_in_conv)

lemma one_chain_line_integral_point_paths:
  assumes "finite one_chain"
  assumes "finite basis"
  assumes "(\<forall>(k, \<gamma>)\<in>ps. point_path \<gamma>)"
  shows "one_chain_line_integral F basis (one_chain - ps) = one_chain_line_integral F basis (one_chain)"
proof-
  have 0:"(\<forall>x\<in>ps. case x of (k, g) \<Rightarrow>  (real_of_int k * line_integral F basis g) = 0)"
    using line_integral_point_path assms
    by force
  show "one_chain_line_integral F basis (one_chain - ps) = one_chain_line_integral F basis one_chain"
    unfolding one_chain_line_integral_def using 0 \<open>finite one_chain\<close>
    by (force simp add:  intro: comm_monoid_add_class.sum.mono_neutral_left)
qed

lemma boundary_chain_diff:
  assumes "boundary_chain one_chain"
  shows "boundary_chain (one_chain - s)"
  using assms
  by (auto simp add: boundary_chain_def)

lemma gen_common_subdivision_imp_eq_line_integral:
  assumes "(common_sudiv_exists one_chain1 one_chain2)"
    "boundary_chain one_chain1"
    "boundary_chain one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    "finite one_chain1"
    "finite one_chain2"
    "finite basis"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain2. line_integral_exists F basis \<gamma>"
proof -
  obtain ps1 ps2 where gen_subdiv: "(common_boundary_sudivision_exists (one_chain1 - ps1) (one_chain2 - ps2))" "(\<forall>(k, \<gamma>)\<in>ps1. point_path \<gamma>)" " (\<forall>(k, \<gamma>)\<in>ps2. point_path \<gamma>)"
    using assms(1) gen_common_subdiv_imp_common_subdiv
    by blast
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    using one_chain_line_integral_point_paths gen_common_subdiv_imp_common_subdiv
      assms(2-7) gen_subdiv
      common_subdivision_imp_eq_line_integral(1)[OF gen_subdiv(1) boundary_chain_diff[OF assms(2)] boundary_chain_diff[OF assms(3)]]
    by auto
  show "\<forall>(k, \<gamma>)\<in>one_chain2. line_integral_exists F basis \<gamma>"
  proof-
    obtain subdiv where subdiv_props:
      "chain_subdiv_chain (one_chain1-ps1) subdiv"
      "chain_subdiv_chain (one_chain2-ps2) subdiv"
      "(\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>)"
      "(boundary_chain subdiv)"
      using gen_subdiv(1)
      by (auto simp add: common_boundary_sudivision_exists_def)
    have "\<forall>(k, \<gamma>)\<in>subdiv. line_integral_exists F basis \<gamma>"
      using one_chain_line_integral_eq_line_integral_on_sudivision'(2)[OF subdiv_props(1) boundary_chain_diff[OF assms(2)] subdiv_props(4)] assms(4) subdiv_props(3) assms(5) assms(7)
      by blast
    then have i: "\<forall>(k, \<gamma>)\<in>one_chain2-ps2. line_integral_exists F basis \<gamma>"
      using one_chain_line_integral_eq_line_integral_on_sudivision(2)[OF subdiv_props(2) boundary_chain_diff[OF assms(3)] subdiv_props(4)] subdiv_props(3) assms(6) assms(7)
      by blast
    then show ?thesis
      using  gen_subdiv(3) line_integral_exists_point_path[OF assms(7)]
      by blast
  qed      
qed

lemma common_sudiv_exists_refl:
      assumes "common_sudiv_exists C1 C2"
      shows "common_sudiv_exists C2 C1"
      using assms
      apply(simp add: common_sudiv_exists_def)
      by auto

lemma chain_subdiv_path_singleton:
  shows "chain_subdiv_path \<gamma> {(1,\<gamma>)}" 
proof -
  have "rec_join [(1,\<gamma>)] = \<gamma>"
    by (simp add: joinpaths_def)
  then have "set [(1,\<gamma>)] = {(1, \<gamma>)}" "distinct [(1,\<gamma>)]" "rec_join [(1,\<gamma>)] = \<gamma>" "valid_chain_list [(1,\<gamma>)]"
    by auto
  then show ?thesis
    by (metis (no_types) chain_subdiv_path.intros)
qed

lemma chain_subdiv_path_singleton_reverse:
  shows "chain_subdiv_path (reversepath \<gamma>) {(-1,\<gamma>)}"
proof -
  have "rec_join [(-1,\<gamma>)] = reversepath \<gamma>"
    by (simp add: joinpaths_def)
  then have "set [(-1,\<gamma>)] = {(- 1, \<gamma>)}" "distinct [(-1,\<gamma>)]" 
             "rec_join [(-1,\<gamma>)] = reversepath \<gamma>" "valid_chain_list [(-1,\<gamma>)]"
    by auto
  then  have "chain_subdiv_path (reversepath \<gamma>) (set [(- 1, \<gamma>)])"
    using chain_subdiv_path.intros by blast
  then show ?thesis
    by simp
qed

lemma chain_subdiv_chain_refl:
  assumes "boundary_chain C"
  shows "chain_subdiv_chain C C"
  using chain_subdiv_path_singleton chain_subdiv_path_singleton_reverse assms
  unfolding chain_subdiv_chain_def boundary_chain_def pairwise_def using case_prodI2 coeff_cube_to_path.simps 
  by (rule_tac x="\<lambda>x. {x}" in exI) auto

(*path reparam_weaketrization*)

definition reparam_weak where
  "reparam_weak \<gamma>1 \<gamma>2 \<equiv> \<exists>\<phi>. (\<forall>x\<in>{0..1}. \<gamma>1 x = (\<gamma>2 o \<phi>) x) \<and> \<phi> piecewise_C1_differentiable_on {0..1} \<and> \<phi>(0) = 0 \<and> \<phi>(1) = 1 \<and> \<phi> ` {0..1} = {0..1}"

definition reparam where
  "reparam \<gamma>1 \<gamma>2 \<equiv> \<exists>\<phi>. (\<forall>x\<in>{0..1}. \<gamma>1 x = (\<gamma>2 o \<phi>) x) \<and> \<phi> piecewise_C1_differentiable_on {0..1} \<and> \<phi>(0) = 0 \<and> \<phi>(1) = 1 \<and> bij_betw \<phi> {0..1} {0..1} \<and> \<phi> -` {0..1} \<subseteq> {0..1} \<and> (\<forall>x\<in>{0..1}. finite (\<phi> -` {x}))"

lemma reparam_weak_eq_refl:
  shows "reparam_weak \<gamma>1 \<gamma>1"
  unfolding reparam_weak_def
  apply (rule_tac x="id" in exI)
  by (auto simp add: id_def piecewise_C1_differentiable_on_def C1_differentiable_on_def continuous_on_id)

lemma line_integral_exists_smooth_one_base:
  assumes "\<gamma> C1_differentiable_on {0..1}" (*To generalise this to valid_path we need a version of has_integral_substitution_strong that allows finite discontinuities of f*)
    "continuous_on (path_image \<gamma>) (\<lambda>x. F x \<bullet> b)"
  shows "line_integral_exists F {b} \<gamma>"
proof-
  have gamma2_differentiable: "(\<forall>x \<in> {0 .. 1}. \<gamma> differentiable at x)"
    using assms(1) 
    by (auto simp add: valid_path_def C1_differentiable_on_eq)
  then have gamma2_b_component_differentiable: "(\<forall>x \<in> {0 .. 1}. (\<lambda>x. (\<gamma> x) \<bullet> b) differentiable at x)"
    by auto
  then have "(\<lambda>x. (\<gamma> x) \<bullet> b) differentiable_on {0..1}"
    using differentiable_at_withinI
    by (auto simp add: differentiable_on_def)
  then have gama2_cont_comp: "continuous_on {0..1} (\<lambda>x. (\<gamma> x) \<bullet> b)"
    using differentiable_imp_continuous_on
    by auto
  have gamma2_cont:"continuous_on {0..1} \<gamma>"
    using assms(1) C1_differentiable_imp_continuous_on
    by (auto simp add: valid_path_def)
  have iii: "continuous_on {0..1} (\<lambda>x. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b))"
  proof-
    have 0: "continuous_on {0..1} (\<lambda>x. F (\<gamma> x) \<bullet> b)"
      using assms(2) continuous_on_compose[OF gamma2_cont]
      by (auto simp add: path_image_def) 
    obtain D where D: "(\<forall>x\<in>{0..1}. (\<gamma> has_vector_derivative D x) (at x)) \<and> continuous_on {0..1} D"
      using assms(1)
      by (auto simp add: C1_differentiable_on_def)
    then have *:"\<forall>x\<in>{0..1}. vector_derivative \<gamma> (at x within{0..1}) = D x"
      using vector_derivative_at vector_derivative_at_within_ivl
      by fastforce
    then have "continuous_on {0..1} (\<lambda>x. vector_derivative \<gamma> (at x within{0..1}))"
      using continuous_on_eq D by force
    then have 1: "continuous_on {0..1} (\<lambda>x. (vector_derivative \<gamma> (at x within{0..1})) \<bullet> b)"
      by(auto intro!: continuous_intros)
    show ?thesis
      using continuous_on_mult[OF 0 1]  by auto
  qed
  then have "(\<lambda>x. F (\<gamma> x) \<bullet> b * (vector_derivative \<gamma> (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
    using integrable_continuous_real
    by auto
  then show "line_integral_exists F {b} \<gamma>"
    by(auto simp add: line_integral_exists_def)
qed

lemma contour_integral_primitive_lemma:
  fixes f :: "complex \<Rightarrow> complex" and g :: "real \<Rightarrow> complex"
  assumes "a \<le> b"
      and "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "g piecewise_differentiable_on {a..b}"  "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s"
    shows "((\<lambda>x. f'(g x) * vector_derivative g (at x within {a..b}))
             has_integral (f(g b) - f(g a))) {a..b}"
proof -
  obtain k where k: "finite k" "\<forall>x\<in>{a..b} - k. g differentiable (at x within {a..b})" and cg: "continuous_on {a..b} g"
    using assms by (auto simp: piecewise_differentiable_on_def)
  have cfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    apply (rule continuous_on_compose [OF cg, unfolded o_def])
    using assms
    apply (metis field_differentiable_def field_differentiable_imp_continuous_at continuous_on_eq_continuous_within continuous_on_subset image_subset_iff)
    done
  { fix x::real
    assume a: "a < x" and b: "x < b" and xk: "x \<notin> k"
    then have "g differentiable at x within {a..b}"
      using k by (simp add: differentiable_at_withinI)
    then have "(g has_vector_derivative vector_derivative g (at x within {a..b})) (at x within {a..b})"
      by (simp add: vector_derivative_works has_field_derivative_def scaleR_conv_of_real)
    then have gdiff: "(g has_derivative (\<lambda>u. u * vector_derivative g (at x within {a..b}))) (at x within {a..b})"
      by (simp add: has_vector_derivative_def scaleR_conv_of_real)
    have "(f has_field_derivative (f' (g x))) (at (g x) within g ` {a..b})"
      using assms by (metis a atLeastAtMost_iff b DERIV_subset image_subset_iff less_eq_real_def)
    then have fdiff: "(f has_derivative (*) (f' (g x))) (at (g x) within g ` {a..b})"
      by (simp add: has_field_derivative_def)
    have "((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {a..b})) (at x within {a..b})"
      using diff_chain_within [OF gdiff fdiff]
      by (simp add: has_vector_derivative_def scaleR_conv_of_real o_def mult_ac)
  } note * = this
  show ?thesis
    apply (rule fundamental_theorem_of_calculus_interior_strong)
    using k assms cfg *
    apply (auto simp: at_within_Icc_at)
    done
qed

lemma line_integral_primitive_lemma: (*Only for real normed fields, i.e. vectors with products*)
  fixes f :: "'a::{euclidean_space,real_normed_field} \<Rightarrow> 'a::{euclidean_space,real_normed_field}" and
        g :: "real \<Rightarrow> 'a"
  assumes "\<And>(a::'a). a \<in> s \<Longrightarrow> (f has_field_derivative (f' a)) (at a within s)"
      and "g piecewise_differentiable_on {0::real..1}"  "\<And>x. x \<in> {0..1} \<Longrightarrow> g x \<in> s"
      and "base_vec \<in> Basis"
    shows "((\<lambda>x. ((f'(g x)) * (vector_derivative g (at x within {0..1}))) \<bullet> base_vec)
             has_integral (((f(g 1)) \<bullet> base_vec - (f(g 0)) \<bullet> base_vec))) {0..1}"
proof -
  obtain k where k: "finite k" "\<forall>x\<in>{0..1} - k. g differentiable (at x within {0..1})" and cg: "continuous_on {0..1} g"
    using assms by (auto simp: piecewise_differentiable_on_def)
  have cfg: "continuous_on {0..1} (\<lambda>x. f (g x))"
    apply (rule continuous_on_compose [OF cg, unfolded o_def])
    using assms
    apply (metis field_differentiable_def field_differentiable_imp_continuous_at continuous_on_eq_continuous_within continuous_on_subset image_subset_iff)
    done
  { fix x::real
    assume a: "0 < x" and b: "x < 1" and xk: "x \<notin> k"
    then have "g differentiable at x within {0..1}"
      using k by (simp add: differentiable_at_withinI)
    then have "(g has_vector_derivative vector_derivative g (at x within {0..1})) (at x within {0..1})"
      by (simp add: vector_derivative_works has_field_derivative_def scaleR_conv_of_real)
    then have gdiff: "(g has_derivative (\<lambda>u. of_real u * vector_derivative g (at x within {0..1}))) (at x within {0..1})"
      by (simp add: has_vector_derivative_def scaleR_conv_of_real)
    have "(f has_field_derivative (f' (g x))) (at (g x) within g ` {0..1})"
      using assms by (metis a atLeastAtMost_iff b DERIV_subset image_subset_iff less_eq_real_def)
    then have fdiff: "(f has_derivative (*) (f' (g x))) (at (g x) within g ` {0..1})"
      by (simp add: has_field_derivative_def)
    have "((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {0..1})) (at x within {0..1})"
      using diff_chain_within [OF gdiff fdiff]
      by (simp add: has_vector_derivative_def scaleR_conv_of_real o_def mult_ac)
  }
  then have *: "\<And>x. x\<in>{0<..<1} - k \<Longrightarrow> ((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {0..1})) (at x within {0..1})"
       by auto
  have "((\<lambda>x. ((f'(g x))) * ((vector_derivative g (at x within {0..1}))))
             has_integral (((f(g 1)) - (f(g 0))))) {0..1}"
    using fundamental_theorem_of_calculus_interior_strong[OF k(1) zero_le_one _ cfg]
    using k assms cfg * by (auto simp: at_within_Icc_at)
  then have "((\<lambda>x. (((f'(g x))) * ((vector_derivative g (at x within {0..1})))) \<bullet> base_vec)
             has_integral (((f(g 1)) - (f(g 0)))) \<bullet> base_vec) {0..1}"
       using has_integral_componentwise_iff assms(4)
       by fastforce
  then show ?thesis using inner_mult_left'
       by (simp add: inner_mult_left' inner_diff_left)
qed

lemma reparam_eq_line_integrals:
  assumes reparam: "reparam \<gamma>1 \<gamma>2" and
    pw_smooth: "\<gamma>2 piecewise_C1_differentiable_on {0..1}" and (*To generalise this to valid_path we need a version of has_integral_substitution_strong that allows finite discontinuities of f*)
    cont: "continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)" and
    line_integral_ex: "line_integral_exists F {b} \<gamma>2" (*We need to remove this and work on special cases like conservative fields and field/line combinations that satisfy the improper integrals theorem assumptions*)
  shows "line_integral F {b} \<gamma>1 = line_integral F {b} \<gamma>2"
    "line_integral_exists F {b} \<gamma>1"
proof-
  obtain \<phi> where phi: "(\<forall>x\<in>{0..1}. \<gamma>1 x = (\<gamma>2 o \<phi>) x)"" \<phi> piecewise_C1_differentiable_on {0..1}"" \<phi>(0) = 0"" \<phi>(1) = 1""bij_betw \<phi> {0..1} {0..1}" "\<phi> -` {0..1} \<subseteq> {0..1}" "\<forall>x\<in>{0..1}. finite (\<phi> -` {x})"
    using reparam
    by (auto simp add: reparam_def)
  obtain s where s: "finite s" "\<phi> C1_differentiable_on {0..1} - s"
    using phi
    by(auto simp add: reparam_def piecewise_C1_differentiable_on_def)
  let ?s = "s \<inter> {0..1}"
  have s_inter: "finite ?s" "\<phi> C1_differentiable_on {0..1} - ?s"
    using s
     apply blast
    by (metis Diff_Compl Diff_Diff_Int Diff_eq inf.commute s(2))
  have cont_phi: "continuous_on {0..1} \<phi>"
    using phi
    by(auto simp add: reparam_def piecewise_C1_differentiable_on_imp_continuous_on)
  obtain s' D where s'_D: "finite s'" "(\<forall>x \<in> {0 .. 1} - s'. \<gamma>2 differentiable at x)" "(\<forall>x\<in>{0..1} - s'. (\<gamma>2 has_vector_derivative D x) (at x)) \<and> continuous_on ({0..1} - s') D"
    using pw_smooth 
    apply (auto simp add: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    by (simp add: vector_derivative_works)
  let ?s' = "s' \<inter> {0..1}"
  have gamma2_differentiable: "finite ?s'" "(\<forall>x \<in> {0 .. 1} - ?s'. \<gamma>2 differentiable at x)" "(\<forall>x\<in>{0..1} - ?s'. (\<gamma>2 has_vector_derivative D x) (at x)) \<and> continuous_on ({0..1} - ?s') D"
    using s'_D
      apply blast
    using s'_D(2) apply auto[1]
    by (metis Diff_Int2 inf_top.left_neutral s'_D(3))
  then have gamma2_b_component_differentiable: "(\<forall>x \<in> {0 .. 1} - ?s'. (\<lambda>x. (\<gamma>2 x) \<bullet> b) differentiable at x)"
    using differentiable_inner by force
  then have "(\<lambda>x. (\<gamma>2 x) \<bullet> b) differentiable_on {0..1} - ?s'"
    using differentiable_at_withinI
    by (auto simp add: differentiable_on_def)
  then have gama2_cont_comp: "continuous_on ({0..1} - ?s') (\<lambda>x. (\<gamma>2 x) \<bullet> b)"
    using differentiable_imp_continuous_on
    by auto
      (**********Additional needed assumptions ************)
  have s_in01: "?s \<subseteq> {0..1}" by auto
  have s'_in01: "?s' \<subseteq> {0..1}" by auto
  have phi_backimg_s': "\<phi> -` {0..1} \<subseteq> {0..1}" using phi by auto
  have "inj_on \<phi> {0..1}" using phi(5) by (auto simp add: bij_betw_def)
  have bij_phi: "bij_betw \<phi> {0..1} {0..1}" using phi(5) by auto
  have finite_bck_img_single: "\<forall>x\<in>{0..1}. finite (\<phi> -` {x})" using phi by auto
  then have finite_bck_img_single_s': " \<forall>x\<in>?s'. finite (\<phi> -` {x})" by auto
  have gamma2_line_integrable: "(\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)) integrable_on {0..1}"
    using line_integral_ex
    by (simp add: line_integral_exists_def)
      (****************************************************************)
  have finite_neg_img: "finite (\<phi> -` ?s')"
    using finite_bck_img_single
    by (metis Int_iff finite_Int gamma2_differentiable(1) image_vimage_eq inf_img_fin_dom')
  have gamma2_cont:"continuous_on ({0..1} - ?s') \<gamma>2"
    using  gamma2_differentiable
    by (meson continuous_at_imp_continuous_on differentiable_imp_continuous_within)
  have iii: "continuous_on ({0..1} - ?s') (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
  proof-
    have 0: "continuous_on ({0..1} - ?s') (\<lambda>x. F (\<gamma>2 x) \<bullet> b)"
      using cont continuous_on_compose[OF gamma2_cont] continuous_on_compose2 gamma2_cont
      unfolding path_image_def  by fastforce
    have D: "(\<forall>x\<in>{0..1} - ?s'. (\<gamma>2 has_vector_derivative D x) (at x)) \<and> continuous_on ({0..1} - ?s') D"
      using gamma2_differentiable
      by auto                       
    then have *:"\<forall>x\<in>{0..1} - ?s'. vector_derivative \<gamma>2 (at x within{0..1}) = D x"
      using vector_derivative_at vector_derivative_at_within_ivl
      by fastforce
    then have "continuous_on ({0..1} - ?s') (\<lambda>x. vector_derivative \<gamma>2 (at x within{0..1}))"
      using continuous_on_eq D
      by metis
    then have 1: "continuous_on ({0..1} - ?s') (\<lambda>x. (vector_derivative \<gamma>2 (at x within{0..1})) \<bullet> b)"
      by (auto intro!: continuous_intros)
    show ?thesis
      using continuous_on_mult[OF 0 1]
      by auto
  qed
  have iv: "\<phi>(0) \<le> \<phi>(1)"
    using phi(3) phi(4)
    by (simp add: reparam_def)
  have v: "\<phi>`{0..1} \<subseteq> {0..1}"
    using phi
    by (auto simp add: reparam_def bij_betw_def)
  obtain D where D_props: "(\<forall>x\<in>{0..1} - ?s. (\<phi> has_vector_derivative D x) (at x))"
    using s
    by (auto simp add: C1_differentiable_on_def)
  then have "(\<And>x. x \<in> ({0..1} - ?s) \<Longrightarrow> (\<phi> has_vector_derivative D x) (at x within {0..1}))"
    using has_vector_derivative_at_within
    by blast
  then have vi: "(\<And>x. x \<in> ({0..1} - ?s) \<Longrightarrow> (\<phi> has_real_derivative D x) (at x within {0..1}))"
    using has_field_derivative_iff_has_vector_derivative
    by blast
  have a:"((\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) has_integral
              integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
              ({0..1})"
  proof-
    have a: "integral {\<phi> 1..\<phi> 0} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)) = 0" using integral_singleton integral_empty iv
      by (simp add: phi(3) phi(4))
    have b: "((\<lambda>x. D x *\<^sub>R (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) has_integral
                       integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)) - integral {\<phi> 1..\<phi> 0} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
                           {0..1}"
      apply(rule  has_integral_substitution_general_'[OF s_inter(1) zero_le_one gamma2_differentiable(1) v gamma2_line_integrable iii cont_phi finite_bck_img_single_s'])
    proof-
      have "surj_on {0..1} \<phi>"
        using bij_phi
        by (metis (full_types) bij_betw_def image_subsetI rangeI)
      then show "surj_on ?s' \<phi>" using bij_phi s'_in01
        by blast
      show "inj_on \<phi> ({0..1} \<union> (?s \<union> \<phi> -` ?s'))"
      proof-
        have i: "inj_on \<phi> {0..1}" using  bij_phi 
          using bij_betw_def by blast
        have ii: "({0..1} \<union> (?s \<union> \<phi> -` ?s')) = {0..1}" using phi_backimg_s' s_in01 s'_in01
          by blast
        show ?thesis using i ii by auto
      qed
      show "\<And>x. x \<in> {0..1} - ?s \<Longrightarrow> (\<phi> has_real_derivative D x) (at x within {0..1})"
        using vi by blast
    qed
    show ?thesis using a b by auto
  qed
  then have b: "integral {0..1} (\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) = 
                       integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
    by auto
  have gamma2_vec_diffable: "\<And>x::real. x \<in> {0..1} - ((\<phi> -` ?s') \<union> ?s) \<Longrightarrow> ((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
  proof-
    fix x::real 
    assume ass: "x \<in> {0..1} -   ((\<phi> -` ?s') \<union> ?s)"
    have zer_le_x_le_1:"0\<le> x \<and> x \<le> 1" using ass
      by simp
    show "((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
    proof-
      have **: "\<gamma>2 differentiable at (\<phi> x)"
        using  gamma2_differentiable(2) ass v 
        by blast
      have ***: " \<phi> differentiable at x"
        using s ass
        by (auto simp add: C1_differentiable_on_eq)
      then show "((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
        using differentiable_chain_at[OF *** **] 
        by (auto simp add: vector_derivative_works)
    qed
  qed
  then have gamma2_vec_deriv_within: "\<And>x::real. x \<in> {0..1} - ((\<phi> -` ?s') \<union> ?s) \<Longrightarrow> vector_derivative (\<gamma>2 \<circ> \<phi>) (at x) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
    using vector_derivative_at_within_ivl[OF gamma2_vec_diffable]
    by auto
  have "\<forall>x\<in>{0..1} - ((\<phi> -` ?s') \<union> ?s). D x * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b) = (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
  proof
    fix x::real
    assume ass: "x \<in> {0..1} -((\<phi> -` ?s') \<union> ?s)"
    then have 0: "\<phi> differentiable (at x)"
      using s by (auto simp add: C1_differentiable_on_def differentiable_def has_vector_derivative_def)
    obtain D2 where "(\<phi> has_vector_derivative D2) (at x)"
      using D_props ass  by blast
    have "\<phi> x \<in> {0..1} - ?s'"
      using phi(5) ass by (metis Diff_Un Diff_iff Int_iff bij_betw_def image_eqI vimageI)
    then have 1: "\<gamma>2 differentiable (at (\<phi> x))"
      using gamma2_differentiable
      by auto
    have 3:" vector_derivative \<gamma>2 (at (\<phi> x)) =  vector_derivative \<gamma>2 (at (\<phi> x) within {0..1})"
    proof-
      have *:"0\<le> \<phi> x \<and> \<phi> x \<le> 1" using phi(5) ass
        using \<open>\<phi> x \<in> {0..1} - s' \<inter> {0..1}\<close> by auto
      then have **:"(\<gamma>2 has_vector_derivative (vector_derivative \<gamma>2 (at (\<phi> x)))) (at (\<phi> x))"
        using 1 vector_derivative_works  by auto
      show ?thesis
        using * vector_derivative_at_within_ivl[OF **]  by auto
    qed
    show "D x * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b"
      using vector_derivative_chain_at[OF 0 1]
      apply (auto simp add: gamma2_vec_deriv_within[OF ass, symmetric] 3[symmetric])
      using D_props ass vector_derivative_at
      by fastforce
  qed
  then have c:"\<And>x.  x\<in>({0..1} -((\<phi> -` ?s') \<union> ?s)) \<Longrightarrow> D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b)) = 
                                    F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
    by auto
  then have d: "integral ({0..1}) (\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) = 
                                            integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b))"
  proof-
    have "negligible ((\<phi> -` ?s') \<union> ?s)" using finite_neg_img s(1) by auto
    then show ?thesis
      using c integral_spike  by (metis(no_types,lifting))
  qed
  have phi_in_int: "(\<And>x. x \<in> {0..1} \<Longrightarrow> \<phi> x \<in> {0..1})" using phi
    using v by blast
  then have e: "((\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) has_integral
                             integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))){0..1}"
  proof-
    have "negligible ?s" using s_inter(1) by auto
    have 0: "negligible ((\<phi> -` ?s') \<union> ?s)" using finite_neg_img s(1) by auto
    have c':"\<forall> x\<in> {0..1} - ((\<phi> -` ?s') \<union> ?s). D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b)) = 
                                    F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
      using c  by blast
    have has_integral_spike_eq': "\<And>s t f g y. negligible s \<Longrightarrow>
                                                       \<forall>x\<in>t - s. g x = f x \<Longrightarrow> (f has_integral y) t = (g has_integral y) t"
      using has_integral_spike_eq by metis
    show ?thesis
      using a has_integral_spike_eq'[OF 0 c']  by blast
  qed
  then have f: "((\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative  \<gamma>1 (at x within {0..1}) \<bullet> b)) has_integral
                     integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
                       {0..1}"
  proof-
    assume ass: "((\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) has_integral
                            integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
                             {0..1}"
    have *:"\<forall>x\<in>{0..1} - ( ((\<phi> -` ?s') \<union> ?s) \<union> {0,1}). (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) x =
                                                  (\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative \<gamma>1 (at x within {0..1}) \<bullet> b)) x"
    proof-
      have "\<forall>x\<in>{0<..<1}  - (\<phi> -` ?s' \<union> ?s). (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b) = (vector_derivative  (\<gamma>1) (at x within {0..1}) \<bullet> b)"
      proof
        have i: "open ({0<..<1}  - ((\<phi> -` ?s') \<union> ?s))" using open_diff s(1) open_greaterThanLessThan finite_neg_img
          by (simp add: open_diff)
        have ii: "\<forall>x\<in>{0<..<1::real}  - (\<phi> -` ?s' \<union> ?s). (\<gamma>2 \<circ> \<phi>) x = \<gamma>1 x" using phi(1)
          by auto                              
        fix x::real
        assume ass: " x \<in> {0<..<1::real} -  ((\<phi> -` ?s') \<union> ?s)"
        then have iii: "(\<gamma>2 \<circ> \<phi> has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})) (at x)"
            by (metis (no_types) Diff_iff add.commute add_strict_mono ass atLeastAtMost_iff gamma2_vec_deriv_within gamma2_vec_diffable greaterThanLessThan_iff less_irrefl not_le)
            (*Most crucial but annoying step*)
        then have iv:"(\<gamma>1 has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})) (at x)"
          using has_derivative_transform_within_open i ii ass
          apply(auto simp add: has_vector_derivative_def)
            apply (meson ass has_derivative_transform_within_open i ii)
           apply (meson ass has_derivative_transform_within_open i ii)
          by (meson ass has_derivative_transform_within_open i ii)
        have v: "0 \<le> x" "x \<le> 1" using ass by auto
        have 0: "vector_derivative \<gamma>1 (at x within {0..1}) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
          using vector_derivative_at_within_ivl[OF iv v(1) v(2) zero_less_one]
          by force
        have 1: "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
          using vector_derivative_at_within_ivl[OF iii v(1) v(2) zero_less_one]
          by force
        then have "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) = vector_derivative \<gamma>1 (at x within {0..1})"
          using 0 1 by auto
        then show "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b = vector_derivative \<gamma>1 (at x within {0..1}) \<bullet> b" by auto
      qed
      then have i: "\<forall>x\<in>{0..1} - ( ((\<phi> -` ?s') \<union> ?s)\<union>{0,1}). (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b) = (vector_derivative  (\<gamma>1) (at x within {0..1}) \<bullet> b)"
        by auto
      have ii: "\<forall>x\<in>{0..1} - (((\<phi> -` ?s') \<union> ?s)\<union>{0,1}).  F (\<gamma>1 x) \<bullet> b =  F (\<gamma>2 (\<phi> x)) \<bullet> b"
        using phi(1)
        by auto
      show ?thesis 
        using i ii  by metis
    qed
    have **: "negligible ((\<phi> -` ?s') \<union> ?s \<union> {0, 1})" using s(1) finite_neg_img by auto
    have has_integral_spike_eq': "\<And>s t g f y. negligible s \<Longrightarrow>
                                \<forall>x\<in>t - s. g x = f x \<Longrightarrow> (f has_integral y) t = (g has_integral y) t"
      using has_integral_spike_eq by metis
    show ?thesis
      using has_integral_spike_eq'[OF ** *] ass
      by blast
  qed
  then show "line_integral_exists F {b} \<gamma>1"
    using phi  by(auto simp add: line_integral_exists_def)
  have "integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) =
                      integral ({0..1}) (\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative \<gamma>1  (at x within {0..1}) \<bullet> b))"
    using integral_unique[OF e] integral_unique[OF f]
    by metis
  moreover have "integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) =
                         integral ({0..1}) (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
    using b d phi by (auto simp add:)
  ultimately show "line_integral F {b} \<gamma>1 = line_integral F {b} \<gamma>2"
    using phi  by(auto simp add: line_integral_def)
qed

lemma reparam_weak_eq_line_integrals:
  assumes "reparam_weak \<gamma>1 \<gamma>2"
    "\<gamma>2 C1_differentiable_on {0..1}" (*To generalise this to valid_path we need a version of has_integral_substitution_strong that allows finite discontinuities of f*)
    "continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
  shows "line_integral F {b} \<gamma>1 = line_integral F {b} \<gamma>2"
    "line_integral_exists F {b} \<gamma>1"
proof-
  obtain \<phi> where phi: "(\<forall>x\<in>{0..1}. \<gamma>1 x = (\<gamma>2 o \<phi>) x)"" \<phi> piecewise_C1_differentiable_on {0..1}"" \<phi>(0) = 0"" \<phi>(1) = 1"" \<phi> ` {0..1} = {0..1}"
    using assms(1)
    by (auto simp add: reparam_weak_def)
  obtain s where s: "finite s" "\<phi> C1_differentiable_on {0..1} - s"
    using phi
    by(auto simp add: reparam_weak_def piecewise_C1_differentiable_on_def)
  have cont_phi: "continuous_on {0..1} \<phi>"
    using phi
    by(auto simp add: reparam_weak_def piecewise_C1_differentiable_on_imp_continuous_on)
  have gamma2_differentiable: "(\<forall>x \<in> {0 .. 1}. \<gamma>2 differentiable at x)"
    using assms(2) 
    by (auto simp add: valid_path_def C1_differentiable_on_eq)
  then have gamma2_b_component_differentiable: "(\<forall>x \<in> {0 .. 1}. (\<lambda>x. (\<gamma>2 x) \<bullet> b) differentiable at x)"
    by auto
  then have "(\<lambda>x. (\<gamma>2 x) \<bullet> b) differentiable_on {0..1}"
    using differentiable_at_withinI
    by (auto simp add: differentiable_on_def)
  then have gama2_cont_comp: "continuous_on {0..1} (\<lambda>x. (\<gamma>2 x) \<bullet> b)"
    using differentiable_imp_continuous_on
    by auto
  have gamma2_cont:"continuous_on {0..1} \<gamma>2"
    using assms(2) C1_differentiable_imp_continuous_on
    by (auto simp add: valid_path_def)
  have iii: "continuous_on {0..1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
  proof-
    have 0: "continuous_on {0..1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b)"
      using assms(3) continuous_on_compose[OF gamma2_cont]
      by (auto simp add: path_image_def) 
    obtain D where D: "(\<forall>x\<in>{0..1}. (\<gamma>2 has_vector_derivative D x) (at x)) \<and> continuous_on {0..1} D"
      using assms(2)  by (auto simp add: C1_differentiable_on_def)
    then have *:"\<forall>x\<in>{0..1}. vector_derivative \<gamma>2 (at x within{0..1}) = D x"
      using vector_derivative_at vector_derivative_at_within_ivl
      by fastforce
    then have "continuous_on {0..1} (\<lambda>x. vector_derivative \<gamma>2 (at x within{0..1}))"
      using continuous_on_eq D  by force
    then have 1: "continuous_on {0..1} (\<lambda>x. (vector_derivative \<gamma>2 (at x within{0..1})) \<bullet> b)"
      by (auto intro!: continuous_intros)
    show ?thesis
      using continuous_on_mult[OF 0 1]  by auto
  qed
  have iv: "\<phi>(0) \<le> \<phi>(1)"
    using phi(3) phi(4)  by (simp add: reparam_weak_def)
  have v: "\<phi>`{0..1} \<subseteq> {0..1}"
    using phi(5)  by (simp add: reparam_weak_def)
  obtain D where D_props: "(\<forall>x\<in>{0..1} - s. (\<phi> has_vector_derivative D x) (at x))"
    using s
    by (auto simp add: C1_differentiable_on_def)
  then have "(\<And>x. x \<in> ({0..1} -s) \<Longrightarrow> (\<phi> has_vector_derivative D x) (at x within {0..1}))"
    using has_vector_derivative_at_within  by blast
  then have vi: "(\<And>x. x \<in> ({0..1} - s) \<Longrightarrow> (\<phi> has_real_derivative D x) (at x within {0..1}))"
    using has_field_derivative_iff_has_vector_derivative
    by blast
  have a:"((\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) has_integral
              integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
              {0..1}"
    using has_integral_substitution_strong[OF s(1) zero_le_one iv v iii cont_phi vi]
    by simp
  then have b: "integral {0..1} (\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) = 
                       integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
    by auto
  have gamma2_vec_diffable: "\<And>x::real. x \<in> {0..1} -s \<Longrightarrow> ((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
  proof-
    fix x::real 
    assume ass: "x \<in> {0..1} -s"
    have zer_le_x_le_1:"0\<le> x \<and> x \<le> 1" using ass by auto
    show "((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
    proof-
      have **: "\<gamma>2 differentiable at (\<phi> x)"
        using phi gamma2_differentiable
        by (auto simp add: zer_le_x_le_1)
      have ***: " \<phi> differentiable at x"
        using s ass
        by (auto simp add: C1_differentiable_on_eq)
      then show "((\<gamma>2 o \<phi>) has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x)) (at x)"
        using differentiable_chain_at[OF *** **] 
        by (auto simp add: vector_derivative_works)
    qed
  qed
  then have gamma2_vec_deriv_within: "\<And>x::real. x \<in> {0..1} -s \<Longrightarrow> vector_derivative (\<gamma>2 \<circ> \<phi>) (at x) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
    using vector_derivative_at_within_ivl[OF gamma2_vec_diffable]
    by auto
  have "\<forall>x\<in>{0..1} - s. D x * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b) = (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
  proof
    fix x::real
    assume ass: "x \<in> {0..1} -s"
    then have 0: "\<phi> differentiable (at x)"
      using s
      by (auto simp add: C1_differentiable_on_def differentiable_def has_vector_derivative_def)
    obtain D2 where "(\<phi> has_vector_derivative D2) (at x)"
      using D_props ass
      by blast
    have "\<phi> x \<in> {0..1}"
      using phi(5) ass 
      by (auto simp add: reparam_weak_def)
    then have 1: "\<gamma>2 differentiable (at (\<phi> x))"
      using gamma2_differentiable
      by auto
    have 3:" vector_derivative \<gamma>2 (at (\<phi> x)) =  vector_derivative \<gamma>2 (at (\<phi> x) within {0..1})"
    proof-
      have *:"0\<le> \<phi> x \<and> \<phi> x \<le> 1" using phi(5) ass by auto
      then have **:"(\<gamma>2 has_vector_derivative (vector_derivative \<gamma>2 (at (\<phi> x)))) (at (\<phi> x))"
        using 1 vector_derivative_works
        by auto
      show ?thesis
        using * vector_derivative_at_within_ivl[OF **]
        by auto
    qed
    show "D x * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b"
      using vector_derivative_chain_at[OF 0 1]
      apply (auto simp add: gamma2_vec_deriv_within[OF ass, symmetric] 3[symmetric])
      using D_props ass vector_derivative_at
      by fastforce
  qed
  then have c:"\<And>x.  x\<in>({0..1} -s) \<Longrightarrow> D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b)) = 
                                    F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
    by auto
  then have d: "integral ({0..1}) (\<lambda>x. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b))) = 
                                            integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b))"
  proof-
    have "negligible s" using s(1) by auto
    then show ?thesis
      using c integral_spike  by (metis(no_types,lifting))
  qed
  have phi_in_int: "(\<And>x. x \<in> {0..1} \<Longrightarrow> \<phi> x \<in> {0..1})" using phi
    by(auto simp add:)
  then have e: "((\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) has_integral
                             integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))){0..1}"
  proof-
    have 0:"negligible s" using s(1) by auto
    have c':"\<forall> x\<in> {0..1} -s. D x * (F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative \<gamma>2 (at (\<phi> x) within {0..1}) \<bullet> b)) = 
                                    F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)"
      using c by auto
    have has_integral_spike_eq': "\<And>s t f g y. negligible s \<Longrightarrow>
                                               \<forall>x\<in>t - s. g x = f x \<Longrightarrow> (f has_integral y) t = (g has_integral y) t"
      using has_integral_spike_eq by metis
    show ?thesis
      using a has_integral_spike_eq'[OF 0 c']  by blast
  qed
  then have f: "((\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative  \<gamma>1 (at x within {0..1}) \<bullet> b)) has_integral
                     integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
                       {0..1}"
  proof-
    assume ass: "((\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) has_integral
                            integral {\<phi> 0..\<phi> 1} (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b)))
                             {0..1}"
    have *:"\<forall>x\<in>{0..1} - (s\<union>{0,1}). (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) x =
                                                  (\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative \<gamma>1 (at x within {0..1}) \<bullet> b)) x"
    proof-
      have "\<forall>x\<in>{0<..<1} - s. (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b) = (vector_derivative  (\<gamma>1) (at x within {0..1}) \<bullet> b)"
      proof
        have i: "open ({0<..<1} - s)" using open_diff s open_greaterThanLessThan by blast
        have ii: "\<forall>x\<in>{0<..<1::real} - s. (\<gamma>2 \<circ> \<phi>) x = \<gamma>1 x" using phi(1)
          by auto                              
        fix x::real
        assume ass: " x \<in> {0<..<1::real} - s"
        then have iii: "(\<gamma>2 \<circ> \<phi> has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})) (at x)"
          using has_vector_derivative_at_within gamma2_vec_deriv_within gamma2_vec_diffable
          by auto
            (*Most crucial but annoying step*)
        then have iv:"(\<gamma>1 has_vector_derivative vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})) (at x)"
          using has_derivative_transform_within_open i ii ass
          apply(auto simp add: has_vector_derivative_def)
          by force
        have v: "0 \<le> x" "x \<le> 1" using ass by auto
        have 0: "vector_derivative \<gamma>1 (at x within {0..1}) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
          using vector_derivative_at_within_ivl[OF iv v(1) v(2) zero_less_one]
          by force
        have 1: "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) = vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1})"
          using vector_derivative_at_within_ivl[OF iii v(1) v(2) zero_less_one]
          by force
        then have "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) = vector_derivative \<gamma>1 (at x within {0..1})"
          using 0 1 by auto
        then show "vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b = vector_derivative \<gamma>1 (at x within {0..1}) \<bullet> b" by auto
      qed
      then have i: "\<forall>x\<in>{0..1} - (s\<union>{0,1}). (vector_derivative  (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b) = (vector_derivative  (\<gamma>1) (at x within {0..1}) \<bullet> b)"
        by auto
      have ii: "\<forall>x\<in>{0..1} - (s\<union>{0,1}).  F (\<gamma>1 x) \<bullet> b =  F (\<gamma>2 (\<phi> x)) \<bullet> b"
        using phi(1)  by auto
      show ?thesis 
        using i ii by auto
    qed
    have **: "negligible (s\<union>{0,1})" using s(1) by auto
    have has_integral_spike_eq': "\<And>s t g f y. negligible s \<Longrightarrow>
                                \<forall>x\<in>t - s. g x = f x \<Longrightarrow> (f has_integral y) t = (g has_integral y) t"
      using has_integral_spike_eq by metis
    show ?thesis
      using has_integral_spike_eq'[OF ** *] ass
      by blast
  qed
  then show "line_integral_exists F {b} \<gamma>1"
    using phi  by(auto simp add: line_integral_exists_def)
  have "integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) =
                      integral ({0..1}) (\<lambda>x. F (\<gamma>1 x) \<bullet> b * (vector_derivative \<gamma>1  (at x within {0..1}) \<bullet> b))"
    using integral_unique[OF e] integral_unique[OF f]
    by metis
  moreover have "integral ({0..1}) (\<lambda>x. F (\<gamma>2 (\<phi> x)) \<bullet> b * (vector_derivative (\<gamma>2 \<circ> \<phi>) (at x within {0..1}) \<bullet> b)) =
                         integral ({0..1}) (\<lambda>x. F (\<gamma>2 x) \<bullet> b * (vector_derivative \<gamma>2 (at x within {0..1}) \<bullet> b))"
    using b d phi  by (auto simp add:)
  ultimately show "line_integral F {b} \<gamma>1 = line_integral F {b} \<gamma>2"
    using phi by(auto simp add: line_integral_def)
qed

lemma line_integral_sum_basis:
  assumes "finite (basis::('a::euclidean_space) set)"  "\<forall>b\<in>basis. line_integral_exists F {b} \<gamma>"
  shows "line_integral F basis \<gamma> = (\<Sum>b\<in>basis. line_integral F {b} \<gamma>)"
        "line_integral_exists F basis \<gamma>"
  using assms
proof(induction basis)
  show "line_integral F {} \<gamma> = (\<Sum>b\<in>{}. line_integral F {b} \<gamma>)"
    by(auto simp add: line_integral_def)
  show "\<forall>b\<in>{}. line_integral_exists F {b} \<gamma> \<Longrightarrow> line_integral_exists F {} \<gamma>"
    by(simp add: line_integral_exists_def integrable_0)
next
  fix basis::"('a::euclidean_space) set"
  fix x::"'a::euclidean_space"
  fix  \<gamma>
  assume ind_hyp: "(\<forall>b\<in>basis. line_integral_exists F {b} \<gamma> \<Longrightarrow> line_integral_exists F basis \<gamma>)"
    "(\<forall>b\<in>basis. line_integral_exists F {b} \<gamma> \<Longrightarrow> line_integral F basis \<gamma> = (\<Sum>b\<in>basis. line_integral F {b} \<gamma>))"
  assume step: "finite basis"
    "x \<notin> basis"
    "\<forall>b\<in>insert x basis. line_integral_exists F {b} \<gamma>"
  then have 0: "line_integral_exists F {x} \<gamma>" by auto
  have 1:"line_integral_exists F basis \<gamma>"
    using ind_hyp step by auto
  then show "line_integral_exists F (insert x basis) \<gamma>"
    using step(1) step(2) line_integral_sum_gen(2)[OF _ 0 1] by simp
  have 3: "finite (insert x basis)" using step(1) by auto
  have "line_integral F basis \<gamma> = (\<Sum>b\<in>basis. line_integral F {b} \<gamma>)"
    using ind_hyp step by auto
  then show "line_integral F (insert x basis) \<gamma> = (\<Sum>b\<in>insert x basis. line_integral F {b} \<gamma>)"
    using step(1) step(2) line_integral_sum_gen(1)[OF 3 0 1]
    by force
qed

lemma reparam_weak_eq_line_integrals_basis:
  assumes "reparam_weak \<gamma>1 \<gamma>2"
    "\<gamma>2 C1_differentiable_on {0..1}" (*To generalise this to valid_path we need a version of has_integral_substitution_strong that allows finite discontinuities*)
    "\<forall>b\<in>basis. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "finite basis"
  shows "line_integral F basis \<gamma>1 = line_integral F basis \<gamma>2"
    "line_integral_exists F basis \<gamma>1"
proof- 
  show "line_integral_exists F basis \<gamma>1"
    using reparam_weak_eq_line_integrals(2)[OF assms(1) assms(2)] assms(3-4) line_integral_sum_basis(2)[OF assms(4)]
    by(simp add: subset_iff)
  show "line_integral F basis \<gamma>1 = line_integral F basis \<gamma>2"
    using reparam_weak_eq_line_integrals[OF assms(1) assms(2)] assms(3-4) line_integral_sum_basis(1)[OF assms(4)]
      line_integral_exists_smooth_one_base[OF assms(2)]
    by(simp add: subset_iff)
qed

lemma reparam_eq_line_integrals_basis:
  assumes "reparam \<gamma>1 \<gamma>2"
    "\<gamma>2 piecewise_C1_differentiable_on {0..1}" 
    "\<forall>b\<in>basis. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "finite basis"
    "\<forall>b\<in>basis. line_integral_exists F {b} \<gamma>2" (*We need to remove this and work on special cases like conservative fields and field/line combinations that satisfy the improper integrals theorem assumptions*)
  shows "line_integral F basis \<gamma>1 = line_integral F basis \<gamma>2"
    "line_integral_exists F basis \<gamma>1"
proof- 
  show "line_integral_exists F basis \<gamma>1"
    using reparam_eq_line_integrals(2)[OF assms(1) assms(2)] assms(3-5) line_integral_sum_basis(2)[OF assms(4)]
    by(simp add: subset_iff)
  show "line_integral F basis \<gamma>1 = line_integral F basis \<gamma>2"
    using reparam_eq_line_integrals[OF assms(1) assms(2)] assms(3-5) line_integral_sum_basis(1)[OF assms(4)]
    by(simp add: subset_iff)
qed

lemma line_integral_exists_smooth:
  assumes "\<gamma> C1_differentiable_on {0..1}" (*To generalise this to valid_path we need a version of has_integral_substitution_strong that allows finite discontinuities*)
    "\<forall>(b::'a::euclidean_space) \<in>basis. continuous_on (path_image \<gamma>) (\<lambda>x. F x \<bullet> b)"
    "finite basis"
  shows "line_integral_exists F basis \<gamma>"
  using reparam_weak_eq_line_integrals_basis(2)[OF reparam_weak_eq_refl[where ?\<gamma>1.0 = \<gamma>]] assms
  by fastforce

lemma smooth_path_imp_reverse:
  assumes "g C1_differentiable_on {0..1}"
  shows "(reversepath g) C1_differentiable_on {0..1}"
  using assms continuous_on_const
  apply (auto simp: reversepath_def)
  apply (rule C1_differentiable_compose [of "\<lambda>x::real. 1-x" _ g, unfolded o_def])
    apply (auto simp: C1_differentiable_on_eq)
  apply (simp add: finite_vimageI inj_on_def)
  done

lemma piecewise_smooth_path_imp_reverse:
  assumes "g piecewise_C1_differentiable_on {0..1}"
  shows "(reversepath g) piecewise_C1_differentiable_on {0..1}"
  using assms valid_path_reversepath
  using valid_path_def by blast

definition chain_reparam_weak_chain where
  "chain_reparam_weak_chain one_chain1 one_chain2 \<equiv>
      \<exists>f. bij f \<and> f ` one_chain1 = one_chain2 \<and> (\<forall>(k,\<gamma>)\<in>one_chain1. if k = fst (f(k,\<gamma>)) then reparam_weak \<gamma> (snd (f(k,\<gamma>))) else reparam_weak \<gamma> (reversepath (snd (f(k,\<gamma>)))))"

lemma chain_reparam_weak_chain_line_integral:
  assumes "chain_reparam_weak_chain one_chain1 one_chain2"
    "\<forall>(k2,\<gamma>2)\<in>one_chain2. \<gamma>2 C1_differentiable_on {0..1}"
    "\<forall>(k2,\<gamma>2)\<in>one_chain2.\<forall>b\<in>basis. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "finite basis"                                                                     
  and bound1: "boundary_chain one_chain1"
  and bound2: "boundary_chain one_chain2"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
proof-
  obtain f where f: "bij f"
    "(\<forall>(k,\<gamma>)\<in>one_chain1. if k = fst (f(k,\<gamma>)) then reparam_weak \<gamma> (snd (f(k,\<gamma>))) else reparam_weak \<gamma> (reversepath (snd (f(k,\<gamma>)))))"
    "f ` one_chain1 = one_chain2"
    using assms(1)
    by (auto simp add: chain_reparam_weak_chain_def)
  have 0:" \<forall>x\<in>one_chain1. (case x of (k, \<gamma>) \<Rightarrow> (real_of_int k * line_integral F basis \<gamma>) = (case f x of (k, \<gamma>) \<Rightarrow> real_of_int k * line_integral F basis \<gamma>) \<and>
                                                        line_integral_exists F basis \<gamma>)"
  proof
    {fix k1 \<gamma>1
      assume ass1: "(k1,\<gamma>1) \<in>one_chain1"
      have "real_of_int k1 * line_integral F basis \<gamma>1 = (case (f (k1,\<gamma>1)) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                      line_integral_exists F basis \<gamma>1"
      proof(cases)
        assume ass2: "k1 = 1"
        let ?k2 = "fst (f (k1, \<gamma>1))"
        let ?\<gamma>2 = "snd (f (k1, \<gamma>1))"
        have "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2\<and>
                              line_integral_exists F basis \<gamma>1"
        proof(cases)
          assume ass3: "?k2 = 1"
          then have 0: "reparam_weak \<gamma>1 ?\<gamma>2"
            using ass1 ass2 f(2)
            by auto
          have 1: "?\<gamma>2 C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image ?\<gamma>2) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1
            by force
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_weak_eq_line_integrals_basis[OF 0 1 2 assms(4)]
              ass2 ass3
            by auto
        next
          assume "?k2 \<noteq> 1"
          then have ass3: "?k2 = -1"
            using bound2 ass1 f(3) unfolding boundary_chain_def by force
          then have 0: "reparam_weak \<gamma>1 (reversepath ?\<gamma>2)"
            using ass1 ass2 f(2)
            by auto
          have 1: "(reversepath ?\<gamma>2) C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1 smooth_path_imp_reverse
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image (reversepath ?\<gamma>2)) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1 path_image_reversepath
            by force
          have 3: "line_integral F basis ?\<gamma>2 = - line_integral F basis (reversepath ?\<gamma>2)"
          proof-
            have i:"valid_path (reversepath ?\<gamma>2) "
              using 1 C1_differentiable_imp_piecewise
              by (auto simp add: valid_path_def)
            show ?thesis 
              using line_integral_on_reverse_path(1)[OF i line_integral_exists_smooth[OF 1 2 ]] assms
              by auto
          qed
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_weak_eq_line_integrals_basis[OF 0 1 2 assms(4)]
              ass2 ass3 3
            by auto
        qed
        then show "real_of_int k1 * line_integral F basis \<gamma>1 = (case f (k1, \<gamma>1) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                                   line_integral_exists F basis \<gamma>1"
          by (simp add: case_prod_beta')
      next
        assume "k1 \<noteq> 1"
        then have ass2: "k1 = -1"
          using bound1 ass1 f(3) unfolding boundary_chain_def by force
        let ?k2 = "fst (f (k1, \<gamma>1))"
        let ?\<gamma>2 = "snd (f (k1, \<gamma>1))"
        have "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                              line_integral_exists F basis \<gamma>1"
        proof(cases)
          assume ass3: "?k2 = 1"
          then have 0: "reparam_weak \<gamma>1 (reversepath ?\<gamma>2)"
            using ass1 ass2 f(2)
            by auto
          have 1: "(reversepath ?\<gamma>2) C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1 smooth_path_imp_reverse
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image (reversepath ?\<gamma>2)) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1 path_image_reversepath
            by force
          have 3: "line_integral F basis ?\<gamma>2 = - line_integral F basis (reversepath ?\<gamma>2)"
          proof-
            have i:"valid_path (reversepath ?\<gamma>2) "
              using 1 C1_differentiable_imp_piecewise
              by (auto simp add: valid_path_def)
            show ?thesis 
              using line_integral_on_reverse_path(1)[OF i line_integral_exists_smooth[OF 1 2 assms(4)]]
              by auto
          qed
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_weak_eq_line_integrals_basis[OF 0 1 2 assms(4)]
              ass2 ass3 3
            by auto
        next
          assume "?k2 \<noteq> 1"
          then have ass3: "?k2 = -1"
            using bound2 ass1 f(3) unfolding boundary_chain_def by force
          then have 0: "reparam_weak \<gamma>1 ?\<gamma>2"
            using ass1 ass2 f(2)  by auto
          have 1: "?\<gamma>2 C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1  by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image ?\<gamma>2) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1  by force
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_weak_eq_line_integrals_basis[OF 0 1 2 assms(4)]  ass2 ass3
            by auto
        qed
        then show "real_of_int k1 * line_integral F basis \<gamma>1 = (case f (k1, \<gamma>1) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                                   line_integral_exists F basis \<gamma>1"
          by (simp add: case_prod_beta')
      qed
    }
    then show "\<And>x. x \<in> one_chain1 \<Longrightarrow>
                                (case x of (k, \<gamma>) \<Rightarrow> (real_of_int k * line_integral F basis \<gamma>) = (case f x of (k, \<gamma>) \<Rightarrow> real_of_int k * line_integral F basis \<gamma>) \<and>
                                                        line_integral_exists F basis \<gamma>)"
      by (auto simp add: case_prod_beta')
  qed
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    using 0 by(simp add: one_chain_line_integral_def sum_bij[OF f(1) _ f(3)] split_beta)
  show "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    using 0 by blast
qed

definition chain_reparam_chain where
  "chain_reparam_chain one_chain1 one_chain2 \<equiv>
      \<exists>f. bij f \<and> f ` one_chain1 = one_chain2 \<and> (\<forall>(k,\<gamma>)\<in>one_chain1. if k = fst (f(k,\<gamma>)) then reparam \<gamma> (snd (f(k,\<gamma>))) else reparam \<gamma> (reversepath (snd (f(k,\<gamma>)))))"

definition chain_reparam_weak_path::"((real) \<Rightarrow> (real * real)) \<Rightarrow> ((int * ((real) \<Rightarrow> (real * real))) set) \<Rightarrow> bool" where
  "chain_reparam_weak_path \<gamma> one_chain
           \<equiv> \<exists>l. set l = one_chain \<and> distinct l \<and> reparam \<gamma> (rec_join l) \<and> valid_chain_list l \<and> l \<noteq> []"

lemma chain_reparam_chain_line_integral:
  assumes "chain_reparam_chain one_chain1 one_chain2"
    "\<forall>(k2,\<gamma>2)\<in>one_chain2. \<gamma>2 piecewise_C1_differentiable_on {0..1}"
    "\<forall>(k2,\<gamma>2)\<in>one_chain2.\<forall>b\<in>basis. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "finite basis"                                                                     
  and bound1: "boundary_chain one_chain1"
  and bound2: "boundary_chain one_chain2"
  and line: "\<forall>(k2,\<gamma>2)\<in>one_chain2. (\<forall>b\<in>basis. line_integral_exists F {b} \<gamma>2)"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
proof-
  obtain f where f: "bij f"
    "(\<forall>(k,\<gamma>)\<in>one_chain1. if k = fst (f(k,\<gamma>)) then reparam \<gamma> (snd (f(k,\<gamma>))) else reparam \<gamma> (reversepath (snd (f(k,\<gamma>)))))"
    "f ` one_chain1 = one_chain2"
    using assms(1)
    by (auto simp add: chain_reparam_chain_def)
  have integ_exist_b: "\<forall>(k1,\<gamma>1)\<in>one_chain1. \<forall>b\<in>basis. line_integral_exists F {b} (snd (f (k1, \<gamma>1)))"
    using line f by fastforce
  have valid_cubes: "\<forall>(k1,\<gamma>1)\<in>one_chain1. valid_path (snd (f (k1, \<gamma>1)))"
    using assms(2) f(3) valid_path_def by fastforce
  have integ_rev_exist_b: "\<forall>(k1,\<gamma>1)\<in>one_chain1. \<forall>b\<in>basis. line_integral_exists F {b} (reversepath (snd (f (k1, \<gamma>1))))"
    using line_integral_on_reverse_path(2) integ_exist_b valid_cubes
    by blast                             
  have 0:" \<forall>x\<in>one_chain1. (case x of (k, \<gamma>) \<Rightarrow> (real_of_int k * line_integral F basis \<gamma>) = (case f x of (k, \<gamma>) \<Rightarrow> real_of_int k * line_integral F basis \<gamma>) \<and>
                                                        line_integral_exists F basis \<gamma>)"
  proof
    {fix k1 \<gamma>1
      assume ass1: "(k1,\<gamma>1) \<in>one_chain1"
      have "real_of_int k1 * line_integral F basis \<gamma>1 = (case (f (k1,\<gamma>1)) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                      line_integral_exists F basis \<gamma>1"
      proof(cases)
        assume ass2: "k1 = 1"
        let ?k2 = "fst (f (k1, \<gamma>1))"
        let ?\<gamma>2 = "snd (f (k1, \<gamma>1))"
        have "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2\<and>
                              line_integral_exists F basis \<gamma>1"
        proof(cases)
          assume ass3: "?k2 = 1"
          then have 0: "reparam \<gamma>1 ?\<gamma>2"
            using ass1 ass2 f(2)
            by auto
          have 1: "?\<gamma>2 piecewise_C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image ?\<gamma>2) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1
            by force
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_eq_line_integrals_basis[OF 0 1 2 assms(4)] integ_exist_b
              ass1 ass2 ass3
            by auto
        next
          assume "?k2 \<noteq> 1"
          then have ass3: "?k2 = -1"
            using bound2 ass1 f(3) unfolding boundary_chain_def by force
          then have 0: "reparam \<gamma>1 (reversepath ?\<gamma>2)"
            using ass1 ass2 f(2)
            by auto
          have 1: "(reversepath ?\<gamma>2) piecewise_C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1 piecewise_smooth_path_imp_reverse
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image (reversepath ?\<gamma>2)) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1 path_image_reversepath
            by force
          have 3: "line_integral F basis ?\<gamma>2 = - line_integral F basis (reversepath ?\<gamma>2)"
          proof-
            have i:"valid_path (reversepath ?\<gamma>2) "
              using 1 C1_differentiable_imp_piecewise
              by (auto simp add: valid_path_def)
            have ii: "line_integral_exists F basis (snd (f (k1, \<gamma>1)))"
              using assms(4) line_integral_sum_basis(2) integ_exist_b ass1
              by fastforce
            show ?thesis                                            
              using i ii line_integral_on_reverse_path(1) valid_path_reversepath by blast
          qed
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_eq_line_integrals_basis[OF 0 1 2 assms(4)] integ_rev_exist_b
              ass1 ass2 ass3 3 
            by auto
        qed
        then show "real_of_int k1 * line_integral F basis \<gamma>1 = (case f (k1, \<gamma>1) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                                   line_integral_exists F basis \<gamma>1"
          by (simp add: case_prod_beta')
      next
        assume "k1 \<noteq> 1"
        then have ass2: "k1 = -1"
          using bound1 ass1 f(3) unfolding boundary_chain_def by force
        let ?k2 = "fst (f (k1, \<gamma>1))"
        let ?\<gamma>2 = "snd (f (k1, \<gamma>1))"
        have "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                              line_integral_exists F basis \<gamma>1"
        proof(cases)
          assume ass3: "?k2 = 1"
          then have 0: "reparam \<gamma>1 (reversepath ?\<gamma>2)"
            using ass1 ass2 f(2)
            by auto
          have 1: "(reversepath ?\<gamma>2) piecewise_C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1 piecewise_smooth_path_imp_reverse
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image (reversepath ?\<gamma>2)) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1 path_image_reversepath
            by force
          have 3: "line_integral F basis ?\<gamma>2 = - line_integral F basis (reversepath ?\<gamma>2)"
          proof-
            have i:"valid_path (reversepath ?\<gamma>2) "
              using 1 C1_differentiable_imp_piecewise
              by (auto simp add: valid_path_def)
            show ?thesis 
              using line_integral_on_reverse_path(1)[OF i] integ_rev_exist_b
              using ass1 assms(4) line_integral_sum_basis(2) by fastforce
          qed
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_eq_line_integrals_basis[OF 0 1 2 assms(4)]
              ass2 ass3 3
            using ass1 integ_rev_exist_b by auto
        next
          assume "?k2 \<noteq> 1"
          then have ass3: "?k2 = -1"
            using bound2 ass1 f(3) unfolding boundary_chain_def by force
          then have 0: "reparam \<gamma>1 ?\<gamma>2"
            using ass1 ass2 f(2) by auto
          have 1: "?\<gamma>2 piecewise_C1_differentiable_on {0..1}"
            using f(3) assms(2) ass1
            by force
          have 2: "\<forall>b\<in>basis. continuous_on (path_image ?\<gamma>2) (\<lambda>x. F x \<bullet> b)"
            using f(3) assms(3) ass1
            by force
          show "real_of_int k1 * line_integral F basis \<gamma>1 = real_of_int ?k2 * line_integral F basis ?\<gamma>2 \<and>
                                     line_integral_exists F basis \<gamma>1"
            using assms reparam_eq_line_integrals_basis[OF 0 1 2 assms(4)]
              ass2 ass3
            using ass1 integ_exist_b by auto
        qed
        then show "real_of_int k1 * line_integral F basis \<gamma>1 = (case f (k1, \<gamma>1) of (k2, \<gamma>2) \<Rightarrow> real_of_int k2 * line_integral F basis \<gamma>2) \<and>
                                   line_integral_exists F basis \<gamma>1"
          by (simp add: case_prod_beta')
      qed
    }
    then show "\<And>x. x \<in> one_chain1 \<Longrightarrow>
                                (case x of (k, \<gamma>) \<Rightarrow> (real_of_int k * line_integral F basis \<gamma>) = (case f x of (k, \<gamma>) \<Rightarrow> real_of_int k * line_integral F basis \<gamma>) \<and>
                                                        line_integral_exists F basis \<gamma>)"
      by (auto simp add: case_prod_beta')
  qed
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    using 0 by (simp add: one_chain_line_integral_def sum_bij[OF f(1) _ f(3)] prod.case_eq_if)
  show "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    using 0 by blast
qed

lemma path_image_rec_join:
  fixes \<gamma>::"real \<Rightarrow> (real \<times> real)"
  fixes k::int
  fixes l
  shows "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_chain_list l \<Longrightarrow> path_image \<gamma> \<subseteq> path_image (rec_join l)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case ass: (Cons a l)
  obtain k' \<gamma>' where a: "a = (k',\<gamma>')" by force
  have "path_image \<gamma> \<subseteq> path_image (rec_join ((k',\<gamma>') # l))"
  proof(cases)
    assume "l=[]"
    then show "path_image \<gamma> \<subseteq> path_image (rec_join ((k',\<gamma>') # l))"
      using ass(2-3) a
      by(auto simp add:)
  next
    assume "l\<noteq>[]"
    then obtain b l' where b_l: "l = b # l'"
      by (meson rec_join.elims)
    obtain k'' \<gamma>'' where b: "b = (k'',\<gamma>'')" by force
    show ?thesis
      using ass path_image_reversepath b_l path_image_join
      by(fastforce simp add: a)
  qed
  then show ?case
    using a  by auto
qed

lemma path_image_rec_join_2:
  fixes l
  shows "l \<noteq> [] \<Longrightarrow> valid_chain_list l \<Longrightarrow> path_image (rec_join l) \<subseteq> (\<Union>(k, \<gamma>) \<in> set l. path_image \<gamma>)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case ass: (Cons a l)
  obtain k' \<gamma>' where a: "a = (k',\<gamma>')" by force
  have "path_image (rec_join (a # l)) \<subseteq> (\<Union>(k, y)\<in>set (a # l). path_image y)"
  proof(cases)
    assume "l=[]"
    then show "path_image (rec_join (a # l)) \<subseteq> (\<Union>(k, y)\<in>set (a # l). path_image y)"
      using step a  by(auto simp add:)
  next
    assume "l\<noteq>[]"
    then obtain b l' where b_l: "l = b # l'"
      by (meson rec_join.elims)
    obtain k'' \<gamma>'' where b: "b = (k'',\<gamma>'')" by force
    show ?thesis
      using ass
        path_image_reversepath b_l path_image_join
      apply(auto simp add: a) (*Excuse the ugliness of the next script*)
       apply blast
      by fastforce
  qed
  then show ?case
    using a by auto
qed

lemma continuous_on_closed_UN:
  assumes "finite S"
  shows "((\<And>s. s \<in> S \<Longrightarrow> closed s) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> continuous_on s f) \<Longrightarrow> continuous_on (\<Union>S) f)"
  using assms
proof(induction S)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case using continuous_on_closed_Un closed_Union
    by (simp add: closed_Union continuous_on_closed_Un)
qed

lemma chain_reparam_weak_path_line_integral:
  assumes path_eq_chain: "chain_reparam_weak_path \<gamma> one_chain" and
    boundary_chain: "boundary_chain one_chain" and
    line_integral_exists: "\<forall>b\<in>basis. \<forall>(k::int, \<gamma>) \<in> one_chain. line_integral_exists F {b} \<gamma>" and
    valid_path: "\<forall>(k::int, \<gamma>) \<in> one_chain. valid_path \<gamma>" and
    finite_basis: "finite basis" and 
    cont: "\<forall>b\<in>basis. \<forall>(k,\<gamma>2)\<in>one_chain. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)" and
    finite_one_chain: "finite one_chain"
  shows "line_integral F basis \<gamma> = one_chain_line_integral F basis one_chain"
    "line_integral_exists F basis \<gamma>"
    (*"valid_path \<gamma>" This cannot be proven, see the crappy assumption of derivs/eq_pw_smooth :( *)
proof -
  obtain l where l_props: "set l = one_chain" "distinct l" "reparam \<gamma> (rec_join l)" "valid_chain_list l" "l \<noteq> []"
    using chain_reparam_weak_path_def assms
    by auto
  have bchain_l: "boundary_chain (set l)"
    using l_props boundary_chain
    by (simp add: boundary_chain_def)
  have cont_forall: "\<forall>b\<in>basis. continuous_on (\<Union>(k, \<gamma>)\<in>one_chain. path_image \<gamma>) (\<lambda>x. F x \<bullet> b)"
  proof
    fix b
    assume ass: "b \<in> basis"
    have "continuous_on (\<Union>((path_image \<circ> snd) ` one_chain))  (\<lambda>x. F x \<bullet> b)"
      apply(rule continuous_on_closed_UN[where ?S = "(path_image o snd) ` one_chain" ])
    proof
      show "finite one_chain" using finite_one_chain by auto
      show "\<And>s. s \<in> (path_image \<circ> snd) ` one_chain \<Longrightarrow> closed s"
        using  closed_valid_path_image[OF] valid_path  
        by fastforce
      show "\<And>s. s \<in> (path_image \<circ> snd) ` one_chain \<Longrightarrow> continuous_on s (\<lambda>x. F x \<bullet> b)"
        using cont ass by force
    qed
    then show "continuous_on (\<Union>(k, \<gamma>)\<in>one_chain. path_image \<gamma>) (\<lambda>x. F x \<bullet> b)"
      by (auto simp add: Union_eq case_prod_beta)
  qed
  show "line_integral_exists F basis \<gamma>"
  proof (rule reparam_eq_line_integrals_basis[OF l_props(3) _ _  finite_basis])
    let ?\<gamma>2.0="rec_join l"
    show "?\<gamma>2.0 piecewise_C1_differentiable_on {0..1}"
      apply(simp only: valid_path_def[symmetric])
      apply(rule joined_is_valid)
      using assms l_props by auto
    show "\<forall>b\<in>basis. continuous_on (path_image (rec_join l)) (\<lambda>x. F x \<bullet> b)" using path_image_rec_join_2[OF l_props(5) l_props(4)] l_props(1)
      using cont_forall continuous_on_subset by blast
    show "\<forall>b\<in>basis. line_integral_exists F {b} (rec_join l)"
    proof
      fix b
      assume ass: "b\<in>basis"
      show "line_integral_exists F {b} (rec_join l)"
      proof (rule line_integral_exists_on_rec_join)
        show "boundary_chain (set l)"
          using l_props boundary_chain by auto
        show "valid_chain_list l" using l_props by auto
        show "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_path \<gamma>" using l_props assms by auto
        show "\<forall>(k, \<gamma>)\<in>set l. line_integral_exists F {b} \<gamma>" using l_props line_integral_exists ass by blast
      qed
    qed
  qed
  show "line_integral F basis \<gamma> = one_chain_line_integral F basis one_chain"
  proof-
    have i: "line_integral F basis (rec_join l) = one_chain_line_integral F basis one_chain"
    proof (rule one_chain_line_integral_rec_join)
      show "set l = one_chain" "distinct l" "valid_chain_list l" using l_props by auto
      show "boundary_chain one_chain" using boundary_chain by auto
      show "\<forall>(k, \<gamma>)\<in>one_chain. line_integral_exists F basis \<gamma>"
        using line_integral_sum_basis(2)[OF finite_basis] line_integral_exists by blast
      show "\<forall>(k, \<gamma>)\<in>one_chain. valid_path \<gamma>" using valid_path by auto
      show "finite basis" using finite_basis by auto
    qed
    have ii: "line_integral F basis \<gamma> = line_integral F basis (rec_join l)"
    proof (rule reparam_eq_line_integrals_basis[OF l_props(3) _ _  finite_basis])
      let ?\<gamma>2.0="rec_join l"
      show "?\<gamma>2.0 piecewise_C1_differentiable_on {0..1}"
        apply(simp only: valid_path_def[symmetric])
        apply(rule joined_is_valid)
        using assms l_props by auto
      show "\<forall>b\<in>basis. continuous_on (path_image (rec_join l)) (\<lambda>x. F x \<bullet> b)" using path_image_rec_join_2[OF l_props(5) l_props(4)] l_props(1)
        using cont_forall continuous_on_subset by blast
      show "\<forall>b\<in>basis. line_integral_exists F {b} (rec_join l)"
      proof
        fix b
        assume ass: "b\<in>basis"
        show "line_integral_exists F {b} (rec_join l)"
        proof (rule line_integral_exists_on_rec_join)
          show "boundary_chain (set l)"
            using l_props boundary_chain by auto
          show "valid_chain_list l" using l_props by auto
          show "\<And>k \<gamma>. (k, \<gamma>) \<in> set l \<Longrightarrow> valid_path \<gamma>" using l_props assms by auto
          show "\<forall>(k, \<gamma>)\<in>set l. line_integral_exists F {b} \<gamma>" using l_props line_integral_exists ass by blast
        qed
      qed
    qed
    show "line_integral F basis \<gamma> = one_chain_line_integral F basis one_chain" using i ii by auto
  qed
qed

definition chain_reparam_chain' where
  "chain_reparam_chain' one_chain1 subdiv
       \<equiv> \<exists>f. ((\<Union>(f ` one_chain1)) = subdiv) \<and>
              (\<forall>cube \<in> one_chain1. chain_reparam_weak_path (rec_join [cube]) (f cube)) \<and>
              (\<forall>p\<in>one_chain1. \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {}) \<and>
              (\<forall>x \<in> one_chain1. finite (f x))"

lemma chain_reparam_chain'_imp_finite_subdiv:
  assumes "finite one_chain1"
    "chain_reparam_chain' one_chain1 subdiv"
  shows "finite subdiv"
  using assms
  by(auto simp add: chain_reparam_chain'_def)

lemma chain_reparam_chain'_line_integral:
  assumes chain1_eq_chain2: "chain_reparam_chain' one_chain1 subdiv" and
    boundary_chain1: "boundary_chain one_chain1" and
    boundary_chain2: "boundary_chain subdiv" and
    line_integral_exists_on_chain2: "\<forall>b\<in>basis. \<forall>(k::int, \<gamma>) \<in> subdiv. line_integral_exists F {b} \<gamma>" and
    valid_path: "\<forall>(k, \<gamma>) \<in> subdiv. valid_path \<gamma>" and
    valid_path_2: "\<forall>(k, \<gamma>) \<in> one_chain1. valid_path \<gamma>" and
    finite_chain1: "finite one_chain1" and
    finite_basis: "finite basis" and
    cont_field: " \<forall>b\<in>basis. \<forall>(k, \<gamma>2)\<in>subdiv. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv"
    "\<forall>(k, \<gamma>) \<in> one_chain1. line_integral_exists F basis \<gamma>"
proof -
  obtain f where f_props:
    "((\<Union>(f ` one_chain1)) = subdiv)"
    "(\<forall>cube \<in> one_chain1. chain_reparam_weak_path (rec_join [cube]) (f cube))"
    "(\<forall>p\<in>one_chain1. \<forall>p'\<in>one_chain1. p \<noteq> p' \<longrightarrow> f p \<inter> f p' = {})"
    "(\<forall>x \<in> one_chain1. finite (f x))"
    using chain1_eq_chain2 
    by (auto simp add: chain_reparam_chain'_def)
  then have 0: "one_chain_line_integral F basis subdiv = one_chain_line_integral F basis (\<Union>(f ` one_chain1))"
    by auto
  {fix k \<gamma>
    assume ass:"(k, \<gamma>) \<in> one_chain1"
    have "line_integral_exists F basis \<gamma> \<and>
               one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
    proof(cases "k = 1")
      assume k_eq_1: "k = 1"
      then have i:"chain_reparam_weak_path \<gamma> (f(k,\<gamma>))"
        using f_props(2) ass by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms  unfolding boundary_chain_def
        by blast
      have iii:"\<forall>b\<in>basis. \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). line_integral_exists F {b} \<gamma>"
        using f_props(1) ass assms
        by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms
        by blast
      have v: "\<forall>b\<in>basis. \<forall>(k, \<gamma>2)\<in>f (k, \<gamma>). continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
        using f_props(1) ass assms
        by blast        
      have "line_integral_exists F basis \<gamma> \<and> one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis \<gamma>"
        using chain_reparam_weak_path_line_integral[OF i ii iii iv finite_basis v] ass f_props(4)
        by (auto)
      then show "line_integral_exists F basis \<gamma> \<and> one_chain_line_integral F basis (f (k, \<gamma>)) = k * line_integral F basis \<gamma>"
        using k_eq_1  by auto
    next
      assume "k \<noteq> 1"
      then have k_eq_neg1: "k = -1"
        using ass boundary_chain1
        by (auto simp add: boundary_chain_def) 
      then have i:"chain_reparam_weak_path (reversepath \<gamma>) (f(k,\<gamma>))"
        using f_props(2) ass by auto
      have ii:"boundary_chain (f(k,\<gamma>))"
        using f_props(1) ass assms unfolding boundary_chain_def
        by blast
      have iii:"\<forall>b\<in>basis. \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). line_integral_exists F {b} \<gamma>"
        using f_props(1) ass assms
        by blast
      have "iv": " \<forall>(k, \<gamma>)\<in>f (k, \<gamma>). valid_path \<gamma>"
        using f_props(1) ass assms by blast
      have v: "\<forall>b\<in>basis. \<forall>(k, \<gamma>2)\<in>f (k, \<gamma>). continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
        using f_props(1) ass assms  by blast        
      have x:"line_integral_exists F basis (reversepath \<gamma>) \<and> one_chain_line_integral F basis (f (k, \<gamma>)) = line_integral F basis (reversepath \<gamma>)"
        using chain_reparam_weak_path_line_integral[OF i ii iii iv finite_basis v] ass f_props(4)
        by auto
      have "valid_path (reversepath \<gamma>)"
        using f_props(1) ass assms  by auto
      then have "line_integral_exists F basis \<gamma> \<and> one_chain_line_integral F basis (f (k, \<gamma>)) = - (line_integral F basis \<gamma>)"
        using line_integral_on_reverse_path reversepath_reversepath x ass
        by metis
      then show "line_integral_exists F basis \<gamma> \<and> one_chain_line_integral F basis (f (k::int, \<gamma>)) = k * line_integral F basis \<gamma>"
        using k_eq_neg1  by auto
    qed}
  note cube_line_integ = this
  have finite_chain2: "finite subdiv" 
    using finite_chain1 f_props(1) f_props(4) by auto
  show line_integral_exists_on_chain1: "\<forall>(k, \<gamma>) \<in> one_chain1. line_integral_exists F basis \<gamma>"
    using cube_line_integ by auto
  have 1: "one_chain_line_integral F basis (\<Union>(f ` one_chain1)) = one_chain_line_integral F basis one_chain1"
  proof -
    have 0:"one_chain_line_integral F basis (\<Union>(f ` one_chain1)) = 
                           (\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain)"
    proof -
      have finite: "\<forall>chain \<in> (f ` one_chain1). finite chain"
        using f_props(1) finite_chain2 
        by (meson Sup_upper finite_subset)
      have disj: " \<forall>A\<in>f ` one_chain1. \<forall>B\<in>f ` one_chain1. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
        apply(simp add:image_def)
        using f_props(3)
        by metis
      show "one_chain_line_integral F basis (\<Union>(f ` one_chain1)) = 
                                (\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain)"
        using Groups_Big.comm_monoid_add_class.sum.Union_disjoint[OF finite disj]
          one_chain_line_integral_def
        by auto
    qed
    have 1:"(\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain) = 
                            one_chain_line_integral F basis one_chain1"
    proof -
      have "(\<Sum>one_chain \<in> (f ` one_chain1). one_chain_line_integral F basis one_chain) = 
                                     (\<Sum>(k,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>))"
      proof -
        have i:"(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) = 
                                       (\<Sum>(k,\<gamma>)\<in>one_chain1 - {p. f p = {}}. k*(line_integral F basis \<gamma>))"
        proof -
          have "inj_on f (one_chain1 - {p. f p = {}})"
            unfolding inj_on_def
            using f_props(3) by force
          then have 0: "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain)
                                                       = (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). one_chain_line_integral F basis (f (k, \<gamma>)))"
            using Groups_Big.comm_monoid_add_class.sum.reindex
            by auto
          have "\<And> k \<gamma>. (k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}) \<Longrightarrow>
                                                     one_chain_line_integral F basis (f(k, \<gamma>)) = k* (line_integral F basis \<gamma>)"
            using cube_line_integ by auto
          then have "(\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). one_chain_line_integral F basis (f (k, \<gamma>)))
                   = (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). k* (line_integral F basis \<gamma>))"
            by (auto intro!: Finite_Cartesian_Product.sum_cong_aux)
          then show "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                     (\<Sum>(k, \<gamma>) \<in> (one_chain1 - {p. f p = {}}). k* (line_integral F basis \<gamma>))"
            using 0  by auto
        qed
        have "\<And> (k::int) \<gamma>. (k, \<gamma>) \<in> one_chain1 \<Longrightarrow> (f (k, \<gamma>) = {}) \<Longrightarrow> (k, \<gamma>) \<in> {(k',\<gamma>'). k'* (line_integral F basis \<gamma>') = 0}"
        proof-
          fix k::"int"
          fix \<gamma>::"real\<Rightarrow>real*real"
          assume ass:"(k, \<gamma>) \<in> one_chain1"
            "(f (k, \<gamma>) = {})"
          then have zero_line_integral:"one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
            using one_chain_line_integral_def
            by auto
          show "(k, \<gamma>) \<in> {(k'::int, \<gamma>'). k' * line_integral F basis \<gamma>' = 0}"
            using zero_line_integral cube_line_integ ass
            by force
        qed
        then have ii:"(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                          (\<Sum>one_chain \<in> (f ` (one_chain1)). one_chain_line_integral F basis one_chain)"
        proof -
          have "\<And>one_chain. one_chain \<in> (f ` (one_chain1)) - (f ` (one_chain1 - {p. f p = {}})) \<Longrightarrow>
                                                         one_chain_line_integral F basis one_chain = 0"
          proof -
            fix one_chain
            assume "one_chain \<in> (f ` (one_chain1)) - (f ` (one_chain1 - {p. f p = {}}))"
            then have "one_chain = {}"
              by auto
            then show "one_chain_line_integral F basis one_chain = 0"
              by (auto simp add: one_chain_line_integral_def)
          qed
          then have 0:"(\<Sum>one_chain \<in> f ` (one_chain1) - (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) 
                                                       = 0"
            using Groups_Big.comm_monoid_add_class.sum.neutral
            by auto
          then have "(\<Sum>one_chain \<in> f ` (one_chain1). one_chain_line_integral F basis one_chain)
                                                      - (\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) 
                                                       = 0"
          proof -
            have finte: "finite (f ` one_chain1)" using finite_chain1 by auto
            show ?thesis
              using Groups_Big.sum_diff[OF finte, of " (f ` (one_chain1 - {p. f p = {}}))"
                  "one_chain_line_integral F basis"]
                0
              by auto
          qed                                           
          then show "(\<Sum>one_chain \<in> (f ` (one_chain1 - {p. f p = {}})). one_chain_line_integral F basis one_chain) =
                                                          (\<Sum>one_chain \<in> (f ` (one_chain1)). one_chain_line_integral F basis one_chain)"
            by auto
        qed
        have "\<And> (k::int) \<gamma>. (k, \<gamma>) \<in> one_chain1 \<Longrightarrow> (f (k, \<gamma>) = {}) \<Longrightarrow> f (k, \<gamma>) \<in> {chain. one_chain_line_integral F basis chain = 0}"
        proof-
          fix k::"int"
          fix \<gamma>::"real\<Rightarrow>real*real"
          assume ass:"(k, \<gamma>) \<in> one_chain1"  "(f (k, \<gamma>) = {})"
          then have "one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
            using one_chain_line_integral_def
            by auto
          then show "f (k, \<gamma>) \<in> {p'. (one_chain_line_integral F basis p' = 0)}"
            by auto
        qed
        then have iii:"(\<Sum>(k::int,\<gamma>)\<in>one_chain1 - {p. f p = {}}. k*(line_integral F basis \<gamma>))
                                                 = (\<Sum>(k::int,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>))"
        proof-
          have "\<And> k \<gamma>. (k,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}})
                                                    \<Longrightarrow> k* (line_integral F basis \<gamma>) = 0"
          proof-
            fix k \<gamma>
            assume ass: "(k,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}})"
            then have "f(k, \<gamma>) = {}"
              by auto
            then have "one_chain_line_integral F basis (f(k, \<gamma>)) = 0"
              by (auto simp add: one_chain_line_integral_def)
            then have zero_line_integral:"one_chain_line_integral F basis (f (k, \<gamma>)) = 0"
              using one_chain_line_integral_def
              by auto
            then show "k* (line_integral F basis \<gamma>) = 0"
              using zero_line_integral cube_line_integ ass
              by force
          qed
          then have "\<forall>(k::int,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}).
                       k* (line_integral F basis \<gamma>) = 0" by auto
          then have "(\<Sum>(k::int,\<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}). k*(line_integral F basis \<gamma>)) = 0"
            using Groups_Big.comm_monoid_add_class.sum.neutral
              [of "one_chain1 - (one_chain1 - {p. f p = {}})" "(\<lambda>(k::int,\<gamma>). k* (line_integral F basis \<gamma>))"]
            by (simp add: split_beta)
          then have "(\<Sum>(k::int,\<gamma>)\<in>one_chain1. k*(line_integral F basis \<gamma>)) -
                                                    (\<Sum>(k::int,\<gamma>)\<in> (one_chain1 - {p. f p = {}}). k*(line_integral F basis \<gamma>))  = 0"
            using Groups_Big.sum_diff[OF finite_chain1]
            by (metis (no_types) Diff_subset \<open>(\<Sum>(k, \<gamma>)\<in>one_chain1 - (one_chain1 - {p. f p = {}}). k * line_integral F basis \<gamma>) = 0\<close> \<open>\<And>f B. B \<subseteq> one_chain1 \<Longrightarrow> sum f (one_chain1 - B) = sum f one_chain1 - sum f B\<close>)
          then show ?thesis by auto
        qed
        show ?thesis using i ii iii by auto
      qed
      then show ?thesis using one_chain_line_integral_def by auto
    qed                    
    show ?thesis using 0 1 by auto
  qed
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis subdiv" using 0 1 by auto
qed

lemma chain_reparam_chain'_line_integral_smooth_cubes:
  assumes "chain_reparam_chain' one_chain1 one_chain2"
    "\<forall>(k2,\<gamma>2)\<in>one_chain2. \<gamma>2 C1_differentiable_on {0..1}"
    "\<forall>b\<in>basis.\<forall>(k2,\<gamma>2)\<in>one_chain2. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "finite basis"                                                                     
    "finite one_chain1"
    "boundary_chain one_chain1"
    "boundary_chain one_chain2"
    "\<forall>(k,\<gamma>)\<in>one_chain1. valid_path \<gamma>"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
proof-
  {fix b
    assume "b \<in> basis"
    fix k \<gamma>
    assume "(k, \<gamma>)\<in>one_chain2"
    have "line_integral_exists F {b} \<gamma>"
      apply(rule line_integral_exists_smooth)
      using \<open>(k, \<gamma>) \<in> one_chain2\<close> assms(2) apply blast
      using assms
      using \<open>(k, \<gamma>) \<in> one_chain2\<close> \<open>b \<in> basis\<close> apply blast
      using \<open>b \<in> basis\<close> by blast}
  then have a: "\<forall>b\<in>basis. \<forall>(k, \<gamma>)\<in>one_chain2. line_integral_exists F {b} \<gamma>"
    by auto
  have b: "\<forall>(k2,\<gamma>2)\<in>one_chain2. valid_path \<gamma>2"
    using assms(2)
    by (simp add: C1_differentiable_imp_piecewise case_prod_beta valid_path_def)              
  show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    by (rule chain_reparam_chain'_line_integral[OF assms(1) assms(6) assms(7) a b assms(8) assms(5) assms(4) assms(3)])
  show "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    by (rule chain_reparam_chain'_line_integral[OF assms(1) assms(6) assms(7) a b assms(8) assms(5) assms(4) assms(3)])
qed

lemma chain_subdiv_path_pathimg_subset:
  assumes "chain_subdiv_path \<gamma> subdiv"
  shows "\<forall>(k',\<gamma>')\<in>subdiv. (path_image \<gamma>') \<subseteq> path_image \<gamma>"
  using assms chain_subdiv_path.simps path_image_rec_join
  by(auto simp add: chain_subdiv_path.simps)

lemma reparam_path_image:
  assumes "reparam \<gamma>1 \<gamma>2"
  shows "path_image \<gamma>1 = path_image \<gamma>2"
  using assms
  apply (auto simp add: reparam_def path_image_def image_def bij_betw_def)
  apply (force dest!: equalityD2)
  done

lemma chain_reparam_weak_path_pathimg_subset:
  assumes "chain_reparam_weak_path \<gamma> subdiv"
  shows "\<forall>(k',\<gamma>')\<in>subdiv. (path_image \<gamma>') \<subseteq> path_image \<gamma>"
  using assms
  apply(auto simp add: chain_reparam_weak_path_def)
  using path_image_rec_join reparam_path_image by blast

lemma chain_subdiv_chain_pathimg_subset':
  assumes "chain_subdiv_chain one_chain subdiv"
  assumes "(k,\<gamma>)\<in> subdiv"
  shows " \<exists>k' \<gamma>'. (k',\<gamma>')\<in> one_chain \<and> path_image \<gamma> \<subseteq> path_image \<gamma>'"
  using assms unfolding chain_subdiv_chain_def  pairwise_def
  apply auto
  by (metis chain_subdiv_path.cases coeff_cube_to_path.simps path_image_rec_join path_image_reversepath)

lemma chain_subdiv_chain_pathimg_subset:
  assumes "chain_subdiv_chain one_chain subdiv"
  shows "\<Union> (path_image ` {\<gamma>. \<exists>k. (k,\<gamma>)\<in> subdiv}) \<subseteq> \<Union> (path_image ` {\<gamma>. \<exists>k. (k,\<gamma>)\<in> one_chain})"
  using assms unfolding chain_subdiv_chain_def pairwise_def
  apply auto
  by (metis UN_iff assms chain_subdiv_chain_pathimg_subset' subsetCE case_prodI2) 

lemma chain_reparam_chain'_pathimg_subset':
  assumes "chain_reparam_chain' one_chain subdiv"
  assumes "(k,\<gamma>)\<in> subdiv"
  shows " \<exists>k' \<gamma>'. (k',\<gamma>')\<in> one_chain \<and> path_image \<gamma> \<subseteq> path_image \<gamma>'"
  using assms chain_reparam_weak_path_pathimg_subset
  apply(auto simp add: chain_reparam_chain'_def set_eq_iff)
  using  path_image_reversepath case_prodE case_prodD old.prod.exhaust
  apply (simp add: list.distinct(1) list.inject rec_join.elims)
  by (smt case_prodD coeff_cube_to_path.simps rec_join.simps(2) reversepath_simps(2) surj_pair)

 definition common_reparam_exists:: "(int \<times> (real \<Rightarrow> real \<times> real)) set \<Rightarrow> (int \<times> (real \<Rightarrow> real \<times> real)) set \<Rightarrow> bool" where
    "common_reparam_exists one_chain1 one_chain2 \<equiv>
    (\<exists>subdiv ps1 ps2.
    chain_reparam_chain' (one_chain1 - ps1) subdiv \<and>
    chain_reparam_chain' (one_chain2 - ps2) subdiv \<and>
    (\<forall>(k, \<gamma>)\<in>subdiv.  \<gamma> C1_differentiable_on {0..1}) \<and>
    boundary_chain subdiv \<and>
    (\<forall>(k, \<gamma>)\<in>ps1. point_path \<gamma>) \<and>
    (\<forall>(k, \<gamma>)\<in>ps2. point_path \<gamma>))"

lemma common_reparam_exists_imp_eq_line_integral:
  assumes finite_basis: "finite basis" and 
    "finite one_chain1"
    "finite one_chain2"
    "boundary_chain (one_chain1::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
    "boundary_chain (one_chain2::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
    " \<forall>(k2, \<gamma>2)\<in>one_chain2. \<forall>b\<in>basis. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    "(common_reparam_exists one_chain1 one_chain2)"
    "(\<forall>(k, \<gamma>)\<in>one_chain1.  valid_path \<gamma>)"
    "(\<forall>(k, \<gamma>)\<in>one_chain2.  valid_path \<gamma>)"
  shows "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
proof-
  obtain subdiv ps1 ps2 where props:
    "chain_reparam_chain' (one_chain1 - ps1) subdiv"
    "chain_reparam_chain' (one_chain2 - ps2) subdiv "
    "(\<forall>(k, \<gamma>)\<in>subdiv.  \<gamma> C1_differentiable_on {0..1})"
    "boundary_chain subdiv"
    "(\<forall>(k, \<gamma>)\<in>ps1. point_path \<gamma>)"
    "(\<forall>(k, \<gamma>)\<in>ps2. point_path \<gamma>)"
    using assms
    by (auto simp add: common_reparam_exists_def)
  have subdiv_valid: "(\<forall>(k, \<gamma>)\<in>subdiv.  valid_path \<gamma>)"
    apply(simp add: valid_path_def)
    using props(3)
    using C1_differentiable_imp_piecewise by blast
  have onechain_boundary1: "boundary_chain (one_chain1 - ps1)" using assms(4) by (auto simp add: boundary_chain_def)
  have onechain_boundary2: "boundary_chain (one_chain2 - ps1)" using assms(5) by (auto simp add: boundary_chain_def)
  {fix k2 \<gamma>2 b
    assume ass: "(k2, \<gamma>2)\<in>subdiv "" b\<in>basis"
    have "\<And> k \<gamma>. (k, \<gamma>) \<in> subdiv \<Longrightarrow> \<exists>k' \<gamma>'. (k', \<gamma>') \<in> one_chain2 \<and> path_image \<gamma> \<subseteq> path_image \<gamma>'"
      by (meson chain_reparam_chain'_pathimg_subset' props Diff_subset subsetCE)
    then have "continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
      using assms(6) continuous_on_subset[where ?f = " (\<lambda>x. F x \<bullet> b)"] ass
      apply(auto simp add:  subset_iff)
      by (metis (mono_tags, lifting) case_prodD)}
  then have cont_field: "\<forall>b\<in>basis. \<forall>(k2, \<gamma>2)\<in>subdiv. continuous_on (path_image \<gamma>2) (\<lambda>x. F x \<bullet> b)"
    by auto
  have one_chain1_ps_valid: "(\<forall>(k, \<gamma>)\<in>one_chain1 - ps1.  valid_path \<gamma>)" using assms by auto
  have one_chain2_ps_valid: "(\<forall>(k, \<gamma>)\<in>one_chain2 - ps1.  valid_path \<gamma>)" using assms by auto
  have 0: "one_chain_line_integral F basis (one_chain1 - ps1) = one_chain_line_integral F basis subdiv"
    apply(rule chain_reparam_chain'_line_integral_smooth_cubes[OF props(1) props(3) cont_field finite_basis])
    using props assms
    apply blast
    using props assms
    using onechain_boundary1 apply blast
    using props assms
    apply blast
    using one_chain1_ps_valid by blast
  have 1:"\<forall>(k, \<gamma>)\<in>(one_chain1 - ps1). line_integral_exists F basis \<gamma>"
    apply(rule chain_reparam_chain'_line_integral_smooth_cubes[OF props(1) props(3) cont_field finite_basis])
    using props assms
    apply blast
    using props assms
    using onechain_boundary1 apply blast
    using props assms
    apply blast
    using one_chain1_ps_valid by blast
  have 2: "one_chain_line_integral F basis (one_chain2 - ps2) = one_chain_line_integral F basis subdiv"
    apply(rule chain_reparam_chain'_line_integral_smooth_cubes[OF props(2) props(3) cont_field finite_basis])
    using props assms
    apply blast
    apply (simp add: assms(5) boundary_chain_diff)
    apply (simp add: props(4))
    by (simp add: assms(9))
  have 3:"\<forall>(k, \<gamma>)\<in>(one_chain2 - ps2). line_integral_exists F basis \<gamma>"
    apply(rule chain_reparam_chain'_line_integral_smooth_cubes[OF props(2) props(3) cont_field finite_basis])
    using props assms
    apply blast
    apply (simp add: assms(5) boundary_chain_diff)
    apply (simp add: props(4))
    by (simp add: assms(9))
  show line_int_ex_chain1: "\<forall>(k, \<gamma>)\<in>one_chain1. line_integral_exists F basis \<gamma>"
    using 0 
    using "1" finite_basis line_integral_exists_point_path props(5) by fastforce
  then show "one_chain_line_integral F basis one_chain1 = one_chain_line_integral F basis one_chain2"
    using 0 1 2 3
    using assms(2-3) finite_basis one_chain_line_integral_point_paths props(5) props(6) by auto
qed

definition subcube :: "real \<Rightarrow> real \<Rightarrow> (int \<times> (real \<Rightarrow> real \<times> real)) \<Rightarrow> (int \<times> (real \<Rightarrow> real \<times> real))" where
  "subcube a b cube = (fst cube, subpath a b (snd cube))"

lemma subcube_valid_path:
  assumes "valid_path (snd cube)" "a \<in> {0..1}" "b \<in> {0..1}"
  shows "valid_path (snd (subcube a b cube))"
  using valid_path_subpath[OF assms] by (auto simp add: subcube_def)

end
