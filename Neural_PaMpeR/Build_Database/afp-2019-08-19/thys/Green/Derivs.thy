theory Derivs
  imports General_Utils
begin

lemma field_simp_has_vector_derivative [derivative_intros]:
  "(f has_field_derivative y) F \<Longrightarrow> (f has_vector_derivative y) F"
  by (simp add: has_field_derivative_iff_has_vector_derivative)

lemma continuous_on_cases_empty [continuous_intros]:
  "\<lbrakk>closed S; continuous_on S f; \<And>x. \<lbrakk>x \<in> S; \<not> P x\<rbrakk> \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow>
    continuous_on S (\<lambda>x. if P x then f x else g x)"
  using continuous_on_cases [of _ "{}"] by force

lemma inj_on_cases:
  assumes "inj_on f (Collect P \<inter> S)" "inj_on g (Collect (Not \<circ> P) \<inter> S)"
    "f ` (Collect P \<inter> S) \<inter> g ` (Collect (Not \<circ> P) \<inter> S) = {}"
  shows "inj_on (\<lambda>x. if P x then f x else g x) S"
  using assms by (force simp: inj_on_def)

lemma inj_on_arccos: "S \<subseteq> {-1..1} \<Longrightarrow> inj_on arccos S"
  by (metis atLeastAtMost_iff cos_arccos inj_onI subsetCE)

lemma has_vector_derivative_componentwise_within:
  "(f has_vector_derivative f') (at a within S) \<longleftrightarrow>
    (\<forall>i \<in> Basis. ((\<lambda>x. f x \<bullet> i) has_vector_derivative (f' \<bullet> i)) (at a within S))"
  apply (simp add: has_vector_derivative_def)
  apply (subst has_derivative_componentwise_within)
  apply simp
  done

lemma has_vector_derivative_pair_within:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "\<And>u. u \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> u) has_vector_derivative f' \<bullet> u) (at x within S)"
    "\<And>u. u \<in> Basis \<Longrightarrow> ((\<lambda>x. g x \<bullet> u) has_vector_derivative g' \<bullet> u) (at x within S)"
  shows "((\<lambda>x. (f x, g x)) has_vector_derivative (f',g')) (at x within S)"
  apply (subst has_vector_derivative_componentwise_within)
  apply (auto simp: assms Basis_prod_def)
  done

lemma piecewise_C1_differentiable_const:
  shows "(\<lambda>x. c) piecewise_C1_differentiable_on s"
  using continuous_on_const
  by (auto simp add: piecewise_C1_differentiable_on_def)

declare piecewise_C1_differentiable_const [simp, derivative_intros]
declare piecewise_C1_differentiable_neg [simp, derivative_intros]
declare piecewise_C1_differentiable_add [simp, derivative_intros]
declare piecewise_C1_differentiable_diff [simp, derivative_intros]

(*move to Cauchy_Integral_Theorem*)

lemma piecewise_C1_differentiable_on_ident [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "(\<lambda>x. x) piecewise_C1_differentiable_on S"
  unfolding piecewise_C1_differentiable_on_def using C1_differentiable_on_ident
  by (blast intro: continuous_on_id C1_differentiable_on_ident)

lemma piecewise_C1_differentiable_on_mult [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a::real_normed_algebra"
  assumes "f piecewise_C1_differentiable_on S" "g piecewise_C1_differentiable_on S"
  shows "(\<lambda>x. f x * g x) piecewise_C1_differentiable_on S"
  using assms
  unfolding piecewise_C1_differentiable_on_def
  apply safe
   apply (blast intro: continuous_intros)
  apply (rename_tac A B)
  apply (rule_tac x="A \<union> B" in exI)
  apply (auto intro: C1_differentiable_on_mult C1_differentiable_on_subset)
  done

lemma C1_differentiable_on_cdiv [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a :: real_normed_field"
  shows "f C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x / c) C1_differentiable_on S"
  by (simp add: divide_inverse)

lemma piecewise_C1_differentiable_on_cdiv [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "f piecewise_C1_differentiable_on S"
  shows "(\<lambda>x. f x / c) piecewise_C1_differentiable_on S"
  by (simp add: divide_inverse piecewise_C1_differentiable_const piecewise_C1_differentiable_on_mult assms)

lemma sqrt_C1_differentiable [simp, derivative_intros]:
  assumes f: "f C1_differentiable_on S" and fim: "f ` S \<subseteq> {0<..}"
  shows "(\<lambda>x. sqrt (f x)) C1_differentiable_on S"
proof -
  have contf: "continuous_on S f"
    by (simp add: C1_differentiable_imp_continuous_on f)
  show ?thesis
    using assms
    unfolding C1_differentiable_on_def has_field_derivative_iff_has_vector_derivative [symmetric]
    by (fastforce intro!: contf continuous_intros derivative_intros)
qed

lemma sqrt_piecewise_C1_differentiable [simp, derivative_intros]:
  assumes f: "f piecewise_C1_differentiable_on S" and fim: "f ` S \<subseteq> {0<..}"
  shows "(\<lambda>x. sqrt (f x)) piecewise_C1_differentiable_on S"
  using assms
  unfolding piecewise_C1_differentiable_on_def
  by (fastforce intro!: continuous_intros derivative_intros)

lemma
  fixes f :: "real \<Rightarrow> 'a::{banach,real_normed_field}"
  assumes f: "f C1_differentiable_on S"
  shows sin_C1_differentiable [simp, derivative_intros]: "(\<lambda>x. sin (f x)) C1_differentiable_on S"
  and   cos_C1_differentiable [simp, derivative_intros]: "(\<lambda>x. cos (f x)) C1_differentiable_on S"
proof -
  have contf: "continuous_on S f"
    by (simp add: C1_differentiable_imp_continuous_on f)
  note df_sin = field_vector_diff_chain_at [where g=sin, unfolded o_def]
  note df_cos = field_vector_diff_chain_at [where g=cos, unfolded o_def]
  show  "(\<lambda>x. sin (f x)) C1_differentiable_on S" "(\<lambda>x. cos (f x)) C1_differentiable_on S"
    using assms
    unfolding C1_differentiable_on_def has_field_derivative_iff_has_vector_derivative [symmetric]
    apply auto
    by (rule contf continuous_intros df_sin df_cos derivative_intros exI conjI ballI | force)+
qed

lemma has_derivative_abs:
  fixes a::real
  assumes "a \<noteq> 0"
  shows "(abs has_derivative ((*) (sgn a))) (at a)"
proof -
  have [simp]: "norm = abs"
    using real_norm_def by force
  show ?thesis
    using has_derivative_norm [where 'a=real, simplified] assms
    by (simp add: mult_commute_abs)
qed

lemma abs_C1_differentiable [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f C1_differentiable_on S" and "0 \<notin> f ` S"
  shows "(\<lambda>x. abs (f x)) C1_differentiable_on S"
proof -
  have contf: "continuous_on S f"
    by (simp add: C1_differentiable_imp_continuous_on f)
  note df = DERIV_chain [where f=abs and g=f, unfolded o_def]
  show ?thesis
    using assms
    unfolding C1_differentiable_on_def has_field_derivative_iff_has_vector_derivative [symmetric]
    apply clarify
    apply (rule df exI conjI ballI)+
      apply (force simp: has_field_derivative_def intro: has_derivative_abs continuous_intros contf)+
    done
qed

lemma C1_differentiable_on_pair [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "f C1_differentiable_on S" "g C1_differentiable_on S"
  shows "(\<lambda>x. (f x, g x)) C1_differentiable_on S"
  using assms unfolding C1_differentiable_on_def
  apply safe
  apply (rename_tac A B)
  apply (intro exI ballI conjI)
   apply (rule_tac f'="A x" and g'="B x" in has_vector_derivative_pair_within)
  using  has_vector_derivative_componentwise_within
  by (blast intro: continuous_on_Pair)+

lemma piecewise_C1_differentiable_on_pair [simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "f piecewise_C1_differentiable_on S" "g piecewise_C1_differentiable_on S"
  shows "(\<lambda>x. (f x, g x)) piecewise_C1_differentiable_on S"
  using assms unfolding piecewise_C1_differentiable_on_def
  by (blast intro!: continuous_intros C1_differentiable_on_pair del: continuous_on_discrete
      intro: C1_differentiable_on_subset)

lemma test2:
  assumes s: "\<And>x. x \<in> {0..1} - s \<Longrightarrow> g differentiable at x"
    and fs: "finite s" and uv: "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    and "x \<in> {0..1}" "x \<notin> (\<lambda>t. (v-u) *\<^sub>R t + u) -` s"
  shows "vector_derivative (\<lambda>x. g ((v-u) * x + u)) (at x within {0..1}) = (v-u) *\<^sub>R vector_derivative g (at ((v-u) * x + u) within{0..1})"
proof -
  have i:"(g has_vector_derivative vector_derivative g (at ((v - u) * x + u))) (at ((v-u) * x + u))"
    using assms s [of "(v - u) * x + u"] uv mult_left_le [of x "v-u"]
    by (auto simp:  vector_derivative_works)
  have ii:"((\<lambda>x. g ((v - u) * x + u)) has_vector_derivative (v - u) *\<^sub>R vector_derivative g (at ((v - u) * x + u))) (at x)"
    by (intro vector_diff_chain_at [simplified o_def] derivative_eq_intros | simp add: i)+
  have 0: "0 \<le> (v - u) * x + u"
    using assms uv by auto
  have 1: "(v - u) * x + u \<le> 1"
    using assms uv
    by simp (metis add.commute atLeastAtMost_iff atLeastatMost_empty_iff diff_ge_0_iff_ge empty_iff le_diff_eq mult_left_le)
  have iii: "vector_derivative g (at ((v - u) * x + u) within {0..1}) = vector_derivative g (at ((v - u) * x + u))"
    using Derivative.vector_derivative_at_within_ivl[OF i, of "0" "1", OF 0 1]
    by auto
  have iv: "vector_derivative (\<lambda>x. g ((v - u) * x + u)) (at x within {0..1}) = (v - u) *\<^sub>R vector_derivative g (at ((v - u) * x + u))"
    using Derivative.vector_derivative_at_within_ivl[OF ii, of "0" "1"] assms
    by auto
  show ?thesis
    using iii iv by auto
qed

lemma C1_differentiable_on_components:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> i) C1_differentiable_on s"
  shows "f C1_differentiable_on s"
proof (clarsimp simp add: C1_differentiable_on_def has_vector_derivative_def)
  have *:"\<forall>f i x. x *\<^sub>R (f \<bullet> i) = (x *\<^sub>R f) \<bullet> i" by auto
  have "\<exists>f'. \<forall>i\<in>Basis. \<forall>x\<in>s. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>z. z *\<^sub>R f' x \<bullet> i)) (at x) \<and> continuous_on s f'"
    using assms lambda_skolem_euclidean[of "\<lambda>i D. (\<forall>x\<in>s. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>z. z *\<^sub>R D x)) (at x)) \<and> continuous_on s D"]
    apply (simp only: C1_differentiable_on_def has_vector_derivative_def *)
    using continuous_on_componentwise[of "s"]
    by metis
  then obtain f' where f': "\<forall>i\<in>Basis. \<forall>x\<in>s. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>z. z *\<^sub>R f' x \<bullet> i)) (at x) \<and> continuous_on s f'"
    by auto
  then have 0: "(\<forall>x\<in>s. (f has_derivative (\<lambda>z. z *\<^sub>R f' x)) (at x)) \<and> continuous_on s f'"
    using f' has_derivative_componentwise_within[of "f", where S= UNIV]
    by auto
  then show "\<exists>D. (\<forall>x\<in>s. (f has_derivative (\<lambda>z. z *\<^sub>R D x)) (at x)) \<and> continuous_on s D" by metis
qed

lemma piecewise_C1_differentiable_on_components:
  assumes "finite t"
    "\<And>i. i \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> i) C1_differentiable_on s - t"
    "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on s (\<lambda>x. f x \<bullet> i)"
  shows "f piecewise_C1_differentiable_on s"
  using C1_differentiable_on_components assms continuous_on_componentwise piecewise_C1_differentiable_on_def by blast

lemma all_components_smooth_one_pw_smooth_is_pw_smooth:
  assumes "\<And>i. i \<in> Basis - {j} \<Longrightarrow> (\<lambda>x. f x \<bullet> i) C1_differentiable_on s"
  assumes "(\<lambda>x. f x \<bullet> j) piecewise_C1_differentiable_on s"
  shows "f piecewise_C1_differentiable_on s"
proof -
  have is_cont: "\<forall>i\<in>Basis. continuous_on s (\<lambda>x. f x \<bullet> i)"
    using assms C1_differentiable_imp_continuous_on piecewise_C1_differentiable_on_def
    by fastforce
  obtain t where t:"(finite t \<and> (\<lambda>x. f x \<bullet> j) C1_differentiable_on s - t)" using assms(2) piecewise_C1_differentiable_on_def by auto
  show ?thesis
    using piecewise_C1_differentiable_on_components[where ?f = "f"]
    using assms(2) piecewise_C1_differentiable_on_def
      C1_differentiable_on_subset[OF assms(1) Diff_subset, where ?B1 ="t"] t is_cont
    by fastforce
qed

lemma derivative_component_fun_component:
  fixes i::"'a::euclidean_space"
  assumes "f differentiable (at x)"
  shows "((vector_derivative f (at x)) \<bullet> i) = ((vector_derivative (\<lambda>x. (f x) \<bullet> i) (at x)) )"
proof -
  have "((\<lambda>x. f x \<bullet> i) has_vector_derivative vector_derivative f (at x) \<bullet> i) (at x)"
    using assms and bounded_linear.has_vector_derivative[of "(\<lambda>x. x \<bullet> i)" "f" "(vector_derivative f (at x))" "(at x)"] and
      bounded_linear_inner_left[of "i"] and vector_derivative_works[of "f" "(at x)"]
    by blast
  then show "((vector_derivative f (at x)) \<bullet> i) = ((vector_derivative (\<lambda>x. (f x) \<bullet> i) (at x)) )"
    using vector_derivative_works[of "(\<lambda>x. (f x) \<bullet> i)" "(at x)"] and
      differentiableI_vector[of "(\<lambda>x. (f x) \<bullet> i)" "(vector_derivative f (at x) \<bullet> i)" "(at x)"] and
      Derivative.vector_derivative_at
    by force
qed

lemma gamma_deriv_at_within:
  assumes a_leq_b: "a < b"  and
    x_within_bounds: "x \<in> {a..b}" and
    gamma_differentiable: "\<forall>x \<in> {a .. b}. \<gamma> differentiable at x"
  shows  "vector_derivative \<gamma> (at x within {a..b}) =  vector_derivative \<gamma> (at x)"
  using Derivative.vector_derivative_at_within_ivl[of "\<gamma>" "vector_derivative \<gamma> (at x)" "x" "a" "b"]
    gamma_differentiable x_within_bounds a_leq_b
  by (auto simp add: vector_derivative_works)

lemma islimpt_diff_finite:
  assumes "finite (t::'a::t1_space set)"
  shows "x islimpt s - t = x islimpt s"
proof-
  have iii: "s - t = s - (t \<inter> s)" by auto
  have "(t \<inter> s) \<subseteq> s" by auto
  have ii:"finite (t \<inter> s)" using assms(1) by auto
  have i: "(t \<inter> s) \<union> (s - (t \<inter> s)) = ( s)"
    using assms by auto
  then have "x islimpt s - (t \<inter> s) = x islimpt s"
    using islimpt_Un_finite[OF ii,where ?t = "s - (t \<inter> s)"] i assms(1)
    by force
  then show ?thesis using iii by auto
qed

lemma ivl_limpt_diff:
  assumes "finite s" "a < b"  "(x::real) \<in> {a..b} - s"
  shows "x islimpt {a..b} - s"
proof-
  have "x islimpt {a..b}"
  proof (cases "x \<in>{a,b}")
    have i: "finite {a,b}" and ii:  "{a, b} \<union> {a<..<b} = {a..b}" using assms by auto
    assume "x \<in>{a,b}"
    then show ?thesis
      using islimpt_Un_finite[OF i, where ?t= "{a<..<b}"]
      by (metis assms(2) empty_iff ii insert_iff islimpt_greaterThanLessThan1 islimpt_greaterThanLessThan2)
  next
    assume "x \<notin>{a,b}"
    then show "x islimpt {a..b}" using assms by auto
  qed
  then show "x islimpt {a..b} - s" using islimpt_diff_finite[OF assms(1)] assms
    by fastforce
qed

lemma ivl_closure_diff_del:
  assumes "finite s" "a < b"  "(x::real) \<in> {a..b} - s"
  shows "x \<in> closure (({a..b} - s) - {x})"
  using ivl_limpt_diff islimpt_in_closure assms by blast

lemma ivl_not_trivial_limit_within:
  assumes "finite s"
    "a < b"
    "(x::real) \<in> {a..b} - s"
  shows "at x within {a..b} - s \<noteq> bot"
  using assms ivl_closure_diff_del not_trivial_limit_within
  by blast

lemma vector_derivative_at_within_non_trivial_limit:
  "at x within s \<noteq> bot \<and> (f has_vector_derivative f') (at x) \<Longrightarrow>
     vector_derivative f (at x within s) = f'"
  using has_vector_derivative_at_within vector_derivative_within by fastforce

lemma vector_derivative_at_within_ivl_diff:
  "finite s \<and> a < b \<and> (x::real) \<in> {a..b} - s \<and> (f has_vector_derivative f') (at x) \<Longrightarrow>
     vector_derivative f (at x within {a..b} - s) = f'"
  using vector_derivative_at_within_non_trivial_limit ivl_not_trivial_limit_within by fastforce

lemma gamma_deriv_at_within_diff:
  assumes a_leq_b: "a < b"  and
    x_within_bounds: "x \<in> {a..b} - s" and
    gamma_differentiable: "\<forall>x \<in> {a .. b} - s. \<gamma> differentiable at x" and
    s_subset: "s \<subseteq> {a..b}" and
    finite_s: "finite s"
  shows "vector_derivative \<gamma> (at x within {a..b} - s)
                           =  vector_derivative \<gamma> (at x)"
  using vector_derivative_at_within_ivl_diff [of "s" "a" "b" "x" "\<gamma>" "vector_derivative \<gamma> (at x)"]
    gamma_differentiable
    x_within_bounds a_leq_b s_subset finite_s
  by (auto simp add: vector_derivative_works)

lemma gamma_deriv_at_within_gen:
  assumes a_leq_b: "a < b"  and
    x_within_bounds: "x \<in> s" and
    s_subset: "s \<subseteq> {a..b}" and
    gamma_differentiable: "\<forall>x \<in> s. \<gamma> differentiable at x"
  shows "vector_derivative \<gamma> (at x within ({a..b})) =  vector_derivative \<gamma> (at x)"
  using Derivative.vector_derivative_at_within_ivl[of "\<gamma>" "vector_derivative \<gamma> (at x)" "x" "a" "b"]
    gamma_differentiable  x_within_bounds a_leq_b s_subset
  by (auto simp add: vector_derivative_works)

lemma derivative_component_fun_component_at_within_gen:
  assumes gamma_differentiable: "\<forall>x \<in> s. \<gamma> differentiable at x" and s_subset: "s \<subseteq> {0..1}"
  shows "\<forall>x \<in> s. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) \<bullet> (i::'a:: euclidean_space)
           =  vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
proof -
  have gamma_i_component_smooth:
    "\<forall>x \<in> s. (\<lambda>x. \<gamma> x \<bullet> i) differentiable at x"
    using gamma_differentiable
    by auto
  show "\<forall>x \<in> s. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) \<bullet> i
                                  =  vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
  proof
    fix x::real
    assume x_within_bounds: "x \<in> s"
    have gamma_deriv_at_within:
        "vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) = vector_derivative (\<lambda>x. \<gamma> x) (at x)"
      using gamma_deriv_at_within_gen[of "0" "1"] x_within_bounds
        gamma_differentiable s_subset
      by (auto simp add: vector_derivative_works)
    then have gamma_component_deriv_at_within:
      "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x)
       = vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
      using gamma_deriv_at_within_gen[of "0" "1", where \<gamma> = "(\<lambda>x. \<gamma> x \<bullet> i)"] x_within_bounds
        gamma_i_component_smooth s_subset
      by (auto simp add: vector_derivative_works)
    have gamma_component_deriv_eq_gamma_deriv_component:
      "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x) = vector_derivative (\<lambda>x. \<gamma> x) (at x) \<bullet> i"
      using derivative_component_fun_component[of "\<gamma>" "x" "i"] gamma_differentiable x_within_bounds
      by auto
    show "vector_derivative \<gamma> (at x within {0..1}) \<bullet> i = vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
      using gamma_component_deriv_eq_gamma_deriv_component gamma_component_deriv_at_within gamma_deriv_at_within
      by auto
  qed
qed

lemma derivative_component_fun_component_at_within:
  assumes gamma_differentiable: "\<forall>x \<in> {0 .. 1}. \<gamma> differentiable at x"
  shows "\<forall>x \<in> {0..1}. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) \<bullet> (i::'a:: euclidean_space)
                                       =  vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
proof -
  have gamma_i_component_smooth:
    "\<forall>x \<in> {0 .. 1}. (\<lambda>x. \<gamma> x \<bullet> i) differentiable at x"
    using gamma_differentiable by auto
  show "\<forall>x \<in> {0..1}. vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) \<bullet> i
                                  =  vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
  proof
    fix x::real
    assume x_within_bounds: "x \<in> {0..1}"
    have gamma_deriv_at_within:
      "vector_derivative (\<lambda>x. \<gamma> x) (at x within {0..1}) =  vector_derivative (\<lambda>x. \<gamma> x) (at x)"
      using gamma_deriv_at_within[of "0" "1"] x_within_bounds
        gamma_differentiable
      by (auto simp add: vector_derivative_works)
    have gamma_component_deriv_at_within:
      "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x) = vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
      using Derivative.vector_derivative_at_within_ivl[of "(\<lambda>x. (\<gamma> x) \<bullet> i)" "vector_derivative (\<lambda>x. (\<gamma> x)  \<bullet> i) (at x)" "x" "0" "1"]
        has_vector_derivative_at_within[of "(\<lambda>x. \<gamma> x \<bullet> i)" "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x)" "x" "{0..1}"]
        gamma_i_component_smooth x_within_bounds
      by (simp add: vector_derivative_works)
    have gamma_component_deriv_eq_gamma_deriv_component:
      "vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x) = vector_derivative (\<lambda>x. \<gamma> x) (at x) \<bullet> i"
      using derivative_component_fun_component[of "\<gamma>" "x" "i"] gamma_differentiable x_within_bounds
      by auto
    show "vector_derivative \<gamma> (at x within {0..1}) \<bullet> i = vector_derivative (\<lambda>x. \<gamma> x \<bullet> i) (at x within {0..1})"
      using gamma_component_deriv_eq_gamma_deriv_component gamma_component_deriv_at_within gamma_deriv_at_within
      by auto
  qed
qed

lemma straight_path_diffrentiable_x:
  fixes b :: "real" and y1 ::"real"
  assumes gamma_def: "\<gamma> = (\<lambda>x. (b, y2 + y1 * x))"
  shows "\<forall>x. \<gamma> differentiable at x"
  unfolding gamma_def differentiable_def
  by (fast intro!: derivative_intros)

lemma straight_path_diffrentiable_y:
  fixes b :: "real" and
    y1 y2 ::"real"
  assumes gamma_def: "\<gamma> = (\<lambda>x. (y2 + y1 * x , b))"
  shows "\<forall>x. \<gamma> differentiable at x"
  unfolding gamma_def differentiable_def
  by (fast intro!: derivative_intros)

lemma piecewise_C1_differentiable_on_imp_continuous_on:
  assumes "f piecewise_C1_differentiable_on s"
  shows "continuous_on s f"
  using assms
  by (auto simp add: piecewise_C1_differentiable_on_def)

lemma boring_lemma1:
  fixes f :: "real\<Rightarrow>real"
  assumes "(f has_vector_derivative D) (at x)"
  shows "((\<lambda>x. (f x, 0)) has_vector_derivative ((D,0::real))) (at x)"
proof-
  have *: "((\<lambda>x. (f x) *\<^sub>R (1,0)) has_vector_derivative (D *\<^sub>R (1,0))) (at x)"
    using bounded_linear.has_vector_derivative[OF Real_Vector_Spaces.bounded_linear_scaleR_left assms(1),
        of "(1,0)"] by auto
  have "((\<lambda>x. (f x) *\<^sub>R (1,0)) has_vector_derivative (D,0)) (at x)"
  proof -
    have "(D, 0::'a) = D *\<^sub>R (1, 0)"
      by simp
    then show ?thesis
      by (metis (no_types) *)
  qed
  then show ?thesis by auto
qed

lemma boring_lemma2:
  fixes f :: "real\<Rightarrow>real"
  assumes "(f has_vector_derivative D) (at x)"
  shows "((\<lambda>x. (0, f x)) has_vector_derivative (0, D)) (at x)"
proof-
  have *: "((\<lambda>x. (f x) *\<^sub>R (0,1)) has_vector_derivative (D *\<^sub>R (0,1))) (at x)"
    using bounded_linear.has_vector_derivative[OF Real_Vector_Spaces.bounded_linear_scaleR_left assms(1),
        of "(0,1)"] by auto
  then have "((\<lambda>x. (f x) *\<^sub>R (0,1)) has_vector_derivative ((0,D))) (at x)"
    using scaleR_Pair Real_Vector_Spaces.real_scaleR_def
  proof -
    have "(0::'b, D) = D *\<^sub>R (0, 1)"
      by auto
    then show ?thesis
      by (metis (no_types) *)
  qed
  then show ?thesis by auto
qed

lemma pair_prod_smooth_pw_smooth:
  assumes "(f::real\<Rightarrow>real) C1_differentiable_on s" "(g::real\<Rightarrow>real) piecewise_C1_differentiable_on s"
  shows "(\<lambda>x. (f x, g x)) piecewise_C1_differentiable_on s"
proof -
  have f_cont: "continuous_on s f"
    using assms(1) C1_differentiable_imp_continuous_on
    by fastforce
  have g_cont: "continuous_on s g"
    using assms(2)  by (auto simp add: piecewise_C1_differentiable_on_def)
  obtain t where t:"(finite t \<and> g C1_differentiable_on s - t)" using assms(2) piecewise_C1_differentiable_on_def by auto
  show ?thesis
    using piecewise_C1_differentiable_on_components[where ?f = "(\<lambda>x. (f x, g x))"]
    apply (simp add: real_pair_basis)
    using assms(2) piecewise_C1_differentiable_on_def
      C1_differentiable_on_subset[OF assms(1) Diff_subset, where ?B1 ="t"] t
      f_cont g_cont
    by fastforce
qed

lemma scale_shift_smooth:
  shows "(\<lambda>x. a + b * x) C1_differentiable_on s"
proof -
  show "(\<lambda>x. a + b * x) C1_differentiable_on s"
    using Cauchy_Integral_Theorem.C1_differentiable_on_mult
      Cauchy_Integral_Theorem.C1_differentiable_on_add
      Cauchy_Integral_Theorem.C1_differentiable_on_const
      Cauchy_Integral_Theorem.C1_differentiable_on_ident
    by auto
qed

lemma open_diff:
  assumes "finite (t::'a::t1_space set)"
    "open (s::'a set)"
  shows "open (s -t)"
  using assms
proof(induction "t")
  show "open s \<Longrightarrow> open (s - {})" by auto
next
  fix x::"'a::t1_space"
  fix F::"'a::t1_space set"
  assume step: "finite F " " x \<notin> F" "open s"
  then have i: "(s - insert x F) = (s - F) - {x}" by auto
  assume ind_hyp: " (open s \<Longrightarrow> open (s - F))"
  show "open (s - insert x F)"
    apply (simp only: i)
    using open_delete[of "s -F"] ind_hyp[OF step(3)] by auto
qed

lemma has_derivative_transform_within:
  assumes "0 < d"
    and "x \<in> s"
    and "\<forall>x'\<in>s. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms
  unfolding has_derivative_within
  by (force simp add: intro: Lim_transform_within)

lemma has_derivative_transform_within_ivl:
  assumes "(0::real) < b"
    and     "\<forall>x\<in>{a..b} -s. f x = g x"
    and "x \<in> {a..b} -s"
    and "(f has_derivative f') (at x within {a..b} - s)"
  shows "(g has_derivative f') (at x within {a..b} - s)"
  using has_derivative_transform_within[of "b" "x" "{a..b} - s"] assms
  by auto

lemma has_vector_derivative_transform_within_ivl:
  assumes "(0::real) < b"
    and     "\<forall>x\<in>{a..b} -s . f x = g x"
    and "x \<in> {a..b} - s"
    and "(f has_vector_derivative f') (at x within {a..b} - s)"
  shows "(g has_vector_derivative f') (at x within {a..b} - s)"
  using assms has_derivative_transform_within_ivl
  apply (auto simp add: has_vector_derivative_def)
  by blast

lemma has_derivative_transform_at:
  assumes "0 < d"
    and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using has_derivative_transform_within [of d x UNIV f g f'] assms
  by simp

lemma has_vector_derivative_transform_at:
  assumes "0 < d"
    and "\<forall>x'. dist x' x < d \<longrightarrow> f x' = g x'"
    and "(f has_vector_derivative f') (at x)"
  shows "(g has_vector_derivative f') (at x)"
  using assms
  unfolding has_vector_derivative_def
  by (rule has_derivative_transform_at)

lemma C1_diff_components_2:
  assumes "b \<in> Basis"
  assumes "f C1_differentiable_on s"
  shows "(\<lambda>x. f x \<bullet> b) C1_differentiable_on s"
proof -
  obtain D where D:"(\<forall>x\<in>s. (f has_derivative (\<lambda>z. z *\<^sub>R D x)) (at x))" "continuous_on s D"
    using assms(2) by (fastforce simp add: C1_differentiable_on_def has_vector_derivative_def)
  show ?thesis
  proof (simp add: C1_differentiable_on_def has_vector_derivative_def, intro exI conjI)
    show "continuous_on s (\<lambda>x. D x \<bullet> b)" using D continuous_on_componentwise assms(1) by fastforce
    show "(\<forall>x\<in>s. ((\<lambda>x. f x \<bullet> b) has_derivative (\<lambda>y. y * (\<lambda>x. D x \<bullet> b) x)) (at x))"
      using has_derivative_inner_left D(1) by fastforce
  qed
qed

lemma eq_smooth:
  assumes "0 < d"
    "\<forall>x\<in>s. \<forall>y. dist x y < d \<longrightarrow> f y = g y" (*This crappy condition cannot be loosened :( *)
    "f C1_differentiable_on s"
  shows "g C1_differentiable_on s"
proof (simp add: C1_differentiable_on_def)
  obtain D where D: "(\<forall>x\<in>s. (f has_vector_derivative D x) (at x)) \<and> continuous_on s D"
    using assms by (auto simp add: C1_differentiable_on_def)
  then have f: "(\<forall>x\<in>s. (g has_vector_derivative D x) (at x))"
    using assms(1-2)
    by (metis dist_commute has_vector_derivative_transform_at)
  have "(\<forall>x\<in>s. (g has_vector_derivative D x) (at x)) \<and> continuous_on s D" using D f by auto
  then show "\<exists>D. (\<forall>x\<in>s. (g has_vector_derivative D x) (at x)) \<and> continuous_on s D" by metis
qed

lemma eq_pw_smooth:
  assumes "0 < d"
    "\<forall>x\<in>s. \<forall>y. dist x y < d \<longrightarrow> f y = g y" (*This crappy condition cannot be loosened :( *)
    "\<forall>x\<in>s. f x = g x"
    "f piecewise_C1_differentiable_on s"
  shows "g piecewise_C1_differentiable_on s"
proof (simp add: piecewise_C1_differentiable_on_def)
  have g_cont: "continuous_on s g" using assms piecewise_C1_differentiable_const
    by (simp add: piecewise_C1_differentiable_on_def)
  obtain t where t: "finite t \<and> f C1_differentiable_on s - t"
    using assms by (auto simp add: piecewise_C1_differentiable_on_def)
  then have "g C1_differentiable_on s - t" using assms eq_smooth by blast
  then show "continuous_on s g \<and> (\<exists>t. finite t \<and> g C1_differentiable_on s - t)"
    using t g_cont by metis
qed

lemma scale_piecewise_C1_differentiable_on:
  assumes "f piecewise_C1_differentiable_on s"
  shows "(\<lambda>x. (c::real) * (f x)) piecewise_C1_differentiable_on s"
proof (simp add: piecewise_C1_differentiable_on_def, intro conjI)
  show "continuous_on s (\<lambda>x. c * f x)"
    using assms continuous_on_mult_left
    by (auto simp add: piecewise_C1_differentiable_on_def)
  show "\<exists>t. finite t \<and> (\<lambda>x. c * f x) C1_differentiable_on s - t"
    using assms continuous_on_mult_left
    by (auto simp add: piecewise_C1_differentiable_on_def)
qed

lemma eq_smooth_gen:
  assumes "f C1_differentiable_on s"
    "\<forall>x. f x = g x"
  shows "g C1_differentiable_on s"
  using assms unfolding C1_differentiable_on_def
  by (metis (no_types, lifting) has_vector_derivative_weaken UNIV_I top_greatest)

lemma subpath_compose:
  shows "(subpath a b \<gamma>) = \<gamma> o (\<lambda>x.  (b - a) * x + a)"
  by (auto simp add: subpath_def)

lemma subpath_smooth:
  assumes "\<gamma> C1_differentiable_on {0..1}" "0 \<le> a" "a < b" "b \<le> 1"
  shows "(subpath a b \<gamma>) C1_differentiable_on {0..1}"
proof-
  have "\<gamma> C1_differentiable_on {a..b}"
    apply (rule C1_differentiable_on_subset)
    using assms by auto
  then have "\<gamma> C1_differentiable_on (\<lambda>x. (b - a) * x + a) ` {0..1}"
    using \<open>a < b\<close> closed_segment_eq_real_ivl closed_segment_real_eq by auto
  moreover have "finite ({0..1} \<inter> (\<lambda>x. (b - a) * x + a) -` {x})" for x
  proof -
    have "((\<lambda>x. (b - a) * x + a) -` {x}) = {(x -a) /(b-a)}"
      using assms by (auto simp add: divide_simps)
    then show ?thesis
      by auto
  qed
  ultimately show ?thesis
    by (force simp add: subpath_compose intro: C1_differentiable_compose derivative_intros)
qed

lemma has_vector_derivative_divide[derivative_intros]:
  fixes a :: "'a::real_normed_field"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. f x / a) has_vector_derivative (x / a)) F"
  unfolding divide_inverse by (fact has_vector_derivative_mult_left)

end
