theory
  Vector_Derivative_On
imports
  "HOL-Analysis.Analysis"
begin

subsection \<open>Vector derivative on a set\<close>
  \<comment> \<open>TODO: also for the other derivatives?!\<close>
  \<comment> \<open>TODO: move to repository and rewrite assumptions of common lemmas?\<close>

definition
  has_vderiv_on :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> bool"
  (infix "(has'_vderiv'_on)" 50)
where
  "(f has_vderiv_on f') S \<longleftrightarrow> (\<forall>x \<in> S. (f has_vector_derivative f' x) (at x within S))"

lemma has_vderiv_on_empty[intro, simp]: "(f has_vderiv_on f') {}"
  by (auto simp: has_vderiv_on_def)

lemma has_vderiv_on_subset:
  assumes "(f has_vderiv_on f') S"
  assumes "T \<subseteq> S"
  shows "(f has_vderiv_on f') T"
  by (meson assms(1) assms(2) contra_subsetD has_vderiv_on_def has_vector_derivative_within_subset)

lemma has_vderiv_on_compose:
  assumes "(f has_vderiv_on f') (g ` T)"
  assumes "(g has_vderiv_on g') T"
  shows "(f o g has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using assms
  unfolding has_vderiv_on_def
  by (auto intro!: vector_diff_chain_within)

lemma has_vderiv_on_open:
  assumes "open T"
  shows "(f has_vderiv_on f') T \<longleftrightarrow> (\<forall>t \<in> T. (f has_vector_derivative f' t) (at t))"
  by (auto simp: has_vderiv_on_def at_within_open[OF _ \<open>open T\<close>])

lemma has_vderiv_on_eq_rhs:\<comment> \<open>TODO: integrate intro \<open>derivative_eq_intros\<close>\<close>
  "(f has_vderiv_on g') T \<Longrightarrow> (\<And>x. x \<in> T \<Longrightarrow> g' x = f' x) \<Longrightarrow> (f has_vderiv_on f') T"
  by (auto simp: has_vderiv_on_def)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  shows has_vderiv_on_id: "((\<lambda>x. x) has_vderiv_on (\<lambda>x. 1)) T"
    and has_vderiv_on_const: "((\<lambda>x. c) has_vderiv_on (\<lambda>x. 0)) T"
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  shows has_vderiv_on_uminus: "((\<lambda>x. - f x) has_vderiv_on (\<lambda>x. - f' x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f g::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_add: "((\<lambda>x. f x + g x) has_vderiv_on (\<lambda>x. f' x + g' x)) T"
   and has_vderiv_on_diff: "((\<lambda>x. f x - g x) has_vderiv_on (\<lambda>x. f' x - g' x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f::"real \<Rightarrow> real" and g::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_scaleR: "((\<lambda>x. f x *\<^sub>R g x) has_vderiv_on (\<lambda>x. f x *\<^sub>R g' x + f' x *\<^sub>R g x)) T"
  using assms
  by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative
    intro!: derivative_eq_intros)

lemma [THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes f g::"real \<Rightarrow> 'a::real_normed_algebra"
  assumes "(f has_vderiv_on f') T"
  assumes "(g has_vderiv_on g') T"
  shows has_vderiv_on_mult: "((\<lambda>x. f x * g x) has_vderiv_on (\<lambda>x. f x * g' x + f' x * g x)) T"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma has_vderiv_on_ln[THEN has_vderiv_on_eq_rhs, derivative_intros]:
  fixes g::"real \<Rightarrow> real"
  assumes "\<And>x. x \<in> s \<Longrightarrow> 0 < g x"
  assumes "(g has_vderiv_on g') s"
  shows "((\<lambda>x. ln (g x)) has_vderiv_on (\<lambda>x. g' x / g x)) s"
  using assms
  unfolding has_vderiv_on_def
  by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative[symmetric]
    intro!: derivative_eq_intros)


lemma fundamental_theorem_of_calculus':
  fixes f :: "real \<Rightarrow> 'a::banach"
  shows "a \<le> b \<Longrightarrow> (f has_vderiv_on f') {a .. b} \<Longrightarrow> (f' has_integral (f b - f a)) {a .. b}"
  by (auto intro!: fundamental_theorem_of_calculus simp: has_vderiv_on_def)

lemma has_vderiv_on_If:
  assumes "U = S \<union> T"
  assumes "(f has_vderiv_on f') (S \<union> (closure T \<inter> closure S))"
  assumes "(g has_vderiv_on g') (T \<union> (closure T \<inter> closure S))"
  assumes "\<And>x. x \<in> closure T \<Longrightarrow> x \<in> closure S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> closure T \<Longrightarrow> x \<in> closure S \<Longrightarrow> f' x = g' x"
  shows "((\<lambda>t. if t \<in> S then f t else g t) has_vderiv_on (\<lambda>t. if t \<in> S then f' t else g' t)) U"
  using assms
  by (auto simp: has_vderiv_on_def ac_simps
      intro!: has_vector_derivative_If_within_closures
      split del: if_split)

lemma mvt_very_simple_closed_segmentE:
  fixes f::"real\<Rightarrow>real"
  assumes "(f has_vderiv_on f') (closed_segment a b)"
  obtains y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
proof cases
  assume "a \<le> b"
  with mvt_very_simple[of a b f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
    by (auto simp: has_vector_derivative_def closed_segment_eq_real_ivl has_vderiv_on_def)
  thus ?thesis ..
next
  assume "\<not> a \<le> b"
  with mvt_very_simple[of b a f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> closed_segment a b"  "f b - f a = (b - a) * f' y"
    by (force simp: has_vector_derivative_def has_vderiv_on_def closed_segment_eq_real_ivl algebra_simps)
  thus ?thesis ..
qed

lemma mvt_simple_closed_segmentE:
  fixes f::"real\<Rightarrow>real"
  assumes "(f has_vderiv_on f') (closed_segment a b)"
  assumes "a \<noteq> b"
  obtains y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
proof cases
  assume "a \<le> b"
  with assms have "a < b" by simp
  with mvt_simple[of a b f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
    by (auto simp: has_vector_derivative_def closed_segment_eq_real_ivl has_vderiv_on_def
        open_segment_eq_real_ivl)
  thus ?thesis ..
next
  assume "\<not> a \<le> b"
  then have "b < a" by simp
  with mvt_simple[of b a f "\<lambda>x i. i *\<^sub>R f' x"] assms
  obtain y where "y \<in> open_segment a b"  "f b - f a = (b - a) * f' y"
    by (force simp: has_vector_derivative_def has_vderiv_on_def closed_segment_eq_real_ivl algebra_simps
      open_segment_eq_real_ivl)
  thus ?thesis ..
qed

lemma differentiable_bound_general_open_segment:
  fixes a :: "real"
    and b :: "real"
    and f :: "real \<Rightarrow> 'a::real_normed_vector"
    and f' :: "real \<Rightarrow> 'a"
  assumes "continuous_on (closed_segment a b) f"
  assumes "continuous_on (closed_segment a b) g"
    and "(f has_vderiv_on f') (open_segment a b)"
    and "(g has_vderiv_on g') (open_segment a b)"
    and "\<And>x. x \<in> open_segment a b \<Longrightarrow> norm (f' x) \<le> g' x"
  shows "norm (f b - f a) \<le> abs (g b - g a)"
proof -
  {
    assume "a = b"
    hence ?thesis by simp
  } moreover {
    assume "a < b"
    with assms
    have "continuous_on {a .. b} f"
      and "continuous_on {a .. b} g"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      and "\<And>x. x\<in>{a<..<b} \<Longrightarrow> norm (f' x) \<le> g' x"
      by (auto simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl has_vderiv_on_def
        at_within_open[where S="{a<..<b}"])
    from differentiable_bound_general[OF \<open>a < b\<close> this]
    have ?thesis by auto
  } moreover {
    assume "b < a"
    with assms
    have "continuous_on {b .. a} f"
      and "continuous_on {b .. a} g"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      and "\<And>x. x\<in>{b<..<a} \<Longrightarrow> norm (f' x) \<le> g' x"
      by (auto simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl has_vderiv_on_def
        at_within_open[where S="{b<..<a}"])
    from differentiable_bound_general[OF \<open>b < a\<close> this]
    have "norm (f a - f b) \<le> g a - g b" by simp
    also have "\<dots> \<le> abs (g b - g a)" by simp
    finally have ?thesis by (simp add: norm_minus_commute)
  } ultimately show ?thesis by arith
qed

lemma has_vderiv_on_union:
  assumes "(f has_vderiv_on g) (s \<union> closure s \<inter> closure t)"
  assumes "(f has_vderiv_on g) (t \<union> closure s \<inter> closure t)"
  shows "(f has_vderiv_on g) (s \<union> t)"
  unfolding has_vderiv_on_def
proof
  fix x assume "x \<in> s \<union> t"
  with has_vector_derivative_If_within_closures[of x s t "s \<union> t" f g f g] assms
  show "(f has_vector_derivative g x) (at x within s \<union> t)"
    by (auto simp: has_vderiv_on_def)
qed

lemma has_vderiv_on_union_closed:
  assumes "(f has_vderiv_on g) s"
  assumes "(f has_vderiv_on g) t"
  assumes "closed s" "closed t"
  shows "(f has_vderiv_on g) (s \<union> t)"
  using has_vderiv_on_If[OF refl, of f g s t f g] assms
  by (auto simp: has_vderiv_on_subset)

lemma vderiv_on_continuous_on: "(f has_vderiv_on f') S \<Longrightarrow> continuous_on S f"
  by (auto intro!: continuous_on_vector_derivative simp: has_vderiv_on_def)

lemma has_vderiv_on_cong[cong]:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f' x = g' x"
  assumes "S = T"
  shows "(f has_vderiv_on f') S = (g has_vderiv_on g') T"
  using assms
  by (metis has_vector_derivative_transform has_vderiv_on_def)

lemma has_vderiv_eq:
  assumes "(f has_vderiv_on f') S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f' x = g' x"
  assumes "S = T"
  shows "(g has_vderiv_on g') T"
  using assms by simp

lemma has_vderiv_on_compose':
  assumes "(f has_vderiv_on f') (g ` T)"
  assumes "(g has_vderiv_on g') T"
  shows "((\<lambda>x. f (g x)) has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using has_vderiv_on_compose[OF assms]
  by simp

lemma has_vderiv_on_compose2:
  assumes "(f has_vderiv_on f') S"
  assumes "(g has_vderiv_on g') T"
  assumes "\<And>t. t \<in> T \<Longrightarrow> g t \<in> S"
  shows "((\<lambda>x. f (g x)) has_vderiv_on (\<lambda>x. g' x *\<^sub>R f' (g x))) T"
  using has_vderiv_on_compose[OF has_vderiv_on_subset[OF assms(1)] assms(2)] assms(3)
  by force

lemma has_vderiv_on_singleton: "(y has_vderiv_on y') {t0}"
  by (auto simp: has_vderiv_on_def has_vector_derivative_def has_derivative_within_singleton_iff
      bounded_linear_scaleR_left)

lemma
  has_vderiv_on_zero_constant:
  assumes "convex s"
  assumes "(f has_vderiv_on (\<lambda>h. 0)) s"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_vector_derivative_zero_constant[of s f] assms
  by (auto simp: has_vderiv_on_def)

lemma bounded_vderiv_on_imp_lipschitz:
  assumes "(f has_vderiv_on f') X"
  assumes convex: "convex X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> norm (f' x) \<le> C" "0 \<le> C"
  shows "C-lipschitz_on X f"
  using assms
  by (auto simp: has_vderiv_on_def has_vector_derivative_def onorm_scaleR_left onorm_id
    intro!: bounded_derivative_imp_lipschitz[where f' = "\<lambda>x d. d *\<^sub>R f' x"])

end
