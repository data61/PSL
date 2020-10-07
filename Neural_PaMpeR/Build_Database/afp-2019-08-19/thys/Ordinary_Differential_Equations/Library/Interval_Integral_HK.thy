theory Interval_Integral_HK
imports Vector_Derivative_On
begin

subsection \<open>interval integral\<close>
  \<comment> \<open>TODO: move to repo ?!\<close>
  \<comment> \<open>TODO: replace with Bochner Integral?!
           But FTC for Bochner requires continuity and euclidean space!\<close>

definition has_ivl_integral ::
    "(real \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"\<comment> \<open>TODO: generalize?\<close>
  (infixr "has'_ivl'_integral" 46)
  where "(f has_ivl_integral y) a b \<longleftrightarrow> (if a \<le> b then (f has_integral y) {a .. b} else (f has_integral - y) {b .. a})"

definition ivl_integral::"real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> 'a::real_normed_vector"
  where "ivl_integral a b f = integral {a .. b} f - integral {b .. a} f"

lemma integral_emptyI[simp]:
  fixes a b::real
  shows  "a \<ge> b \<Longrightarrow> integral {a..b} f = 0" "a > b \<Longrightarrow> integral {a..b} f = 0"
  by (cases "a = b") auto

lemma ivl_integral_unique: "(f has_ivl_integral y) a b \<Longrightarrow> ivl_integral a b f = y"
  using integral_unique[of f y "{a .. b}"] integral_unique[of f "- y" "{b .. a}"]
  unfolding ivl_integral_def has_ivl_integral_def
  by (auto split: if_split_asm)

lemma fundamental_theorem_of_calculus_ivl_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  shows "(f has_vderiv_on f') (closed_segment a b) \<Longrightarrow> (f' has_ivl_integral f b - f a) a b"
  by (auto simp: has_ivl_integral_def closed_segment_eq_real_ivl intro!: fundamental_theorem_of_calculus')

lemma
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  shows indefinite_ivl_integral_continuous:
    "continuous_on (closed_segment a b) (\<lambda>x. ivl_integral a x f)"
    "continuous_on (closed_segment b a) (\<lambda>x. ivl_integral a x f)"
  using assms
  by (auto simp: ivl_integral_def closed_segment_eq_real_ivl split: if_split_asm
    intro!: indefinite_integral_continuous_1 indefinite_integral_continuous_1'
      continuous_intros intro: continuous_on_eq)

lemma
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  assumes "c \<in> closed_segment a b"
  shows indefinite_ivl_integral_continuous_subset:
    "continuous_on (closed_segment a b) (\<lambda>x. ivl_integral c x f)"
proof -
  from assms have "f integrable_on (closed_segment c a)" "f integrable_on (closed_segment c b)"
     by (auto simp: closed_segment_eq_real_ivl integrable_on_subinterval
      integrable_on_insert_iff split: if_splits)
  then have "continuous_on (closed_segment a c \<union> closed_segment c b) (\<lambda>x. ivl_integral c x f)"
    by (auto intro!: indefinite_ivl_integral_continuous continuous_on_closed_Un)
  also have "closed_segment a c \<union> closed_segment c b = closed_segment a b"
    using assms by (auto simp: closed_segment_eq_real_ivl)
  finally show ?thesis .
qed

lemma real_Icc_closed_segment: fixes a b::real shows "a \<le> b \<Longrightarrow> {a .. b} = closed_segment a b"
  by (auto simp: closed_segment_eq_real_ivl)

lemma ivl_integral_zero[simp]: "ivl_integral a a f = 0"
  by (auto simp: ivl_integral_def)

lemma ivl_integral_cong:
  assumes "\<And>x. x \<in> closed_segment a b \<Longrightarrow> g x = f x"
  assumes "a = c" "b = d"
  shows "ivl_integral a b f = ivl_integral c d g"
  using assms integral_spike[of "{}" "closed_segment a b" f g]
  by (auto simp: ivl_integral_def closed_segment_eq_real_ivl split: if_split_asm)

lemma ivl_integral_diff:
  "f integrable_on (closed_segment s t) \<Longrightarrow> g integrable_on (closed_segment s t) \<Longrightarrow>
    ivl_integral s t (\<lambda>x. f x - g x) = ivl_integral s t f - ivl_integral s t g"
  using Henstock_Kurzweil_Integration.integral_diff[of f "closed_segment s t" g]
  by (auto simp: ivl_integral_def closed_segment_eq_real_ivl split: if_split_asm)

lemma ivl_integral_norm_bound_ivl_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<And>x. x \<in> closed_segment a b \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (ivl_integral a b f) \<le> abs (ivl_integral a b g)"
  using integral_norm_bound_integral[OF assms]
  by (auto simp: ivl_integral_def closed_segment_eq_real_ivl split: if_split_asm)

lemma ivl_integral_norm_bound_integral:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<And>x. x \<in> closed_segment a b \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (ivl_integral a b f) \<le> integral (closed_segment a b) g"
  using integral_norm_bound_integral[OF assms]
  by (auto simp: ivl_integral_def closed_segment_eq_real_ivl split: if_split_asm)

lemma norm_ivl_integral_le:
  fixes f :: "real \<Rightarrow> real"
  assumes "f integrable_on (closed_segment a b)"
    and "g integrable_on (closed_segment a b)"
    and "\<And>x. x \<in> closed_segment a b \<Longrightarrow> f x \<le> g x"
    and "\<And>x. x \<in> closed_segment a b \<Longrightarrow> 0 \<le> f x"
  shows "abs (ivl_integral a b f) \<le> abs (ivl_integral a b g)"
proof (cases "a = b")
  case True then show ?thesis
    by simp
next
  case False
  have "0 \<le> integral {a..b} f" "0 \<le> integral {b..a} f"
    by (metis le_cases Henstock_Kurzweil_Integration.integral_nonneg assms(1) assms(4) closed_segment_eq_real_ivl integral_emptyI(1))+
  then show ?thesis
    using integral_le[OF assms(1-3)]
    unfolding ivl_integral_def closed_segment_eq_real_ivl
    by (simp split: if_split_asm)
qed

lemma ivl_integral_const [simp]:
  shows "ivl_integral a b (\<lambda>x. c) = (b - a) *\<^sub>R c"
  by (auto simp: ivl_integral_def algebra_simps)

lemma ivl_integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "x \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral a u f) has_vector_derivative f x) (at x within closed_segment a b)"
proof -
  have "((\<lambda>x. integral {x..a} f) has_vector_derivative 0) (at x within {a..b})" if "a \<le> x" "x \<le> b"
    by (rule has_vector_derivative_transform) (auto simp: that)
  moreover
  have "((\<lambda>x. integral {a..x} f) has_vector_derivative 0) (at x within {b..a})" if "b \<le> x" "x \<le> a"
    by (rule has_vector_derivative_transform) (auto simp: that)
  ultimately
  show ?thesis
    using assms
    by (auto simp: ivl_integral_def closed_segment_eq_real_ivl
        intro!: derivative_eq_intros
        integral_has_vector_derivative[of a b f] integral_has_vector_derivative[of b a "-f"]
        integral_has_vector_derivative'[of b a f])
qed

lemma ivl_integral_has_vderiv_on:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  shows "((\<lambda>u. ivl_integral a u f) has_vderiv_on f) (closed_segment a b)"
  using ivl_integral_has_vector_derivative[OF assms]
  by (auto simp: has_vderiv_on_def)

lemma ivl_integral_has_vderiv_on_subset_segment:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "c \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) (closed_segment a b)"
proof -
  have "(closed_segment c a) \<subseteq> (closed_segment a b)" "(closed_segment c b) \<subseteq> (closed_segment a b)"
    using assms by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  then have "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) ((closed_segment c a) \<union> (closed_segment c b))"
    by (auto intro!: has_vderiv_on_union_closed ivl_integral_has_vderiv_on assms
      intro: continuous_on_subset)
  also have "(closed_segment c a) \<union> (closed_segment c b) = (closed_segment a b)"
    using assms by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  finally show ?thesis .
qed

lemma ivl_integral_has_vector_derivative_subset:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
    and "x \<in> closed_segment a b"
    and "c \<in> closed_segment a b"
  shows "((\<lambda>u. ivl_integral c u f) has_vector_derivative f x) (at x within closed_segment a b)"
  using ivl_integral_has_vderiv_on_subset_segment[OF assms(1)] assms(2-)
  by (auto simp: has_vderiv_on_def)

lemma
  compact_interval_eq_Inf_Sup:
  fixes A::"real set"
  assumes "is_interval A" "compact A" "A \<noteq> {}"
  shows "A = {Inf A .. Sup A}"
  apply (auto simp: closed_segment_eq_real_ivl
      intro!: cInf_lower cSup_upper bounded_imp_bdd_below bounded_imp_bdd_above
      compact_imp_bounded assms)
  by (metis assms(1) assms(2) assms(3) cInf_eq_minimum cSup_eq_maximum compact_attains_inf
      compact_attains_sup mem_is_interval_1_I)

lemma ivl_integral_has_vderiv_on_compact_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on A f"
    and "c \<in> A" "is_interval A" "compact A"
  shows "((\<lambda>u. ivl_integral c u f) has_vderiv_on f) A"
proof -
  have "A = {Inf A .. Sup A}"
    by (rule compact_interval_eq_Inf_Sup) (use assms in auto)
  also have "\<dots> = closed_segment (Inf A) (Sup A)" using assms
    by (auto simp add: closed_segment_eq_real_ivl
        intro!: cInf_le_cSup bounded_imp_bdd_below bounded_imp_bdd_above compact_imp_bounded)
  finally have *: "A = closed_segment (Inf A) (Sup A)" .
  show ?thesis
    apply (subst *)
    apply (rule ivl_integral_has_vderiv_on_subset_segment)
    unfolding *[symmetric]
    by fact+
qed

lemma ivl_integral_has_vector_derivative_compact_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on A f"
    and "is_interval A" "compact A" "x \<in> A" "c \<in> A"
  shows "((\<lambda>u. ivl_integral c u f) has_vector_derivative f x) (at x within A)"
  using ivl_integral_has_vderiv_on_compact_interval[OF assms(1)] assms(2-)
  by (auto simp: has_vderiv_on_def)

lemma ivl_integral_combine:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on (closed_segment a b)"
  assumes "f integrable_on (closed_segment b c)"
  assumes "f integrable_on (closed_segment a c)"
  shows "ivl_integral a b f + ivl_integral b c f = ivl_integral a c f"
proof -
  show ?thesis
    using assms
      integral_combine[of a b c f]
      integral_combine[of a c b f]
      integral_combine[of b a c f]
      integral_combine[of b c a f]
      integral_combine[of c a b f]
      integral_combine[of c b a f]
    by (cases "a \<le> b"; cases "b \<le> c"; cases "a \<le> c")
       (auto simp: algebra_simps ivl_integral_def closed_segment_eq_real_ivl)
qed

lemma integral_equation_swap_initial_value:
  fixes x::"real\<Rightarrow>'a::banach"
  assumes "\<And>t. t \<in> closed_segment t0 t1 \<Longrightarrow> x t = x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))"
  assumes t: "t \<in> closed_segment t0 t1"
  assumes int: "(\<lambda>t. f t (x t)) integrable_on closed_segment t0 t1"
  shows "x t = x t1 + ivl_integral t1 t (\<lambda>t. f t (x t))"
proof -
  from t int have "(\<lambda>t. f t (x t)) integrable_on closed_segment t0 t"
    "(\<lambda>t. f t (x t)) integrable_on closed_segment t t1"
    by (auto intro: integrable_on_subinterval simp: closed_segment_eq_real_ivl split: if_split_asm)
  with assms(1)[of t] assms(2-)
  have "x t - x t0 = ivl_integral t0 t1 (\<lambda>t. f t (x t)) + ivl_integral t1 t (\<lambda>t. f t (x t))"
    by (subst ivl_integral_combine) (auto simp: closed_segment_commute)
  then have "x t + x t1 - (x t0 + ivl_integral t0 t1 (\<lambda>t. f t (x t))) =
    x t1 + ivl_integral t1 t (\<lambda>t. f t (x t))"
    by (simp add: algebra_simps)
  also have "x t0 + ivl_integral t0 t1 (\<lambda>t. f t (x t)) = x t1"
    by (auto simp: assms(1)[symmetric])
  finally show ?thesis  by simp
qed

lemma has_integral_nonpos:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "\<forall>x\<in>s. f x \<le> 0"
  shows "i \<le> 0"
  by (rule has_integral_nonneg[of "-f" "-i" s, simplified])
    (auto intro!: has_integral_neg simp: fun_Compl_def assms)

lemma has_ivl_integral_nonneg:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_ivl_integral i) a b"
    and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> 0 \<le> f x"
    and "\<And>x. b \<le> x \<Longrightarrow> x \<le> a \<Longrightarrow> f x \<le> 0"
  shows "0 \<le> i"
  using assms has_integral_nonneg[of f i "{a .. b}"] has_integral_nonpos[of f "-i" "{b .. a}"]
  by (auto simp: has_ivl_integral_def Ball_def not_le split: if_split_asm)

lemma has_ivl_integral_ivl_integral:
  "f integrable_on (closed_segment a b) \<longleftrightarrow> (f has_ivl_integral (ivl_integral a b f)) a b"
  by (auto simp: closed_segment_eq_real_ivl has_ivl_integral_def ivl_integral_def)

lemma ivl_integral_nonneg:
  fixes f :: "real \<Rightarrow> real"
  assumes "f integrable_on (closed_segment a b)"
    and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> 0 \<le> f x"
    and "\<And>x. b \<le> x \<Longrightarrow> x \<le> a \<Longrightarrow> f x \<le> 0"
  shows "0 \<le> ivl_integral a b f"
  by (rule has_ivl_integral_nonneg[OF assms(1)[unfolded has_ivl_integral_ivl_integral] assms(2-3)])

lemma ivl_integral_bound:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  assumes "\<And>t. t \<in> (closed_segment a b) \<Longrightarrow> norm (f t) \<le> B"
  shows "norm (ivl_integral a b f) \<le> B * abs (b - a)"
  using integral_bound[of a b f B]
    integral_bound[of b a f B]
    assms
  by (auto simp: closed_segment_eq_real_ivl has_ivl_integral_def ivl_integral_def split: if_splits)

lemma ivl_integral_minus_sets:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "f integrable_on (closed_segment c a) \<Longrightarrow> f integrable_on (closed_segment c b) \<Longrightarrow> f integrable_on (closed_segment a b) \<Longrightarrow>
    ivl_integral c a f - ivl_integral c b f = ivl_integral b a f"
  using ivl_integral_combine[of f c b a]
  by (auto simp: algebra_simps closed_segment_commute)

lemma ivl_integral_minus_sets':
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "f integrable_on (closed_segment a c) \<Longrightarrow> f integrable_on (closed_segment b c) \<Longrightarrow> f integrable_on (closed_segment a b) \<Longrightarrow>
    ivl_integral a c f - ivl_integral b c f = ivl_integral a b f"
  using ivl_integral_combine[of f a b c]
  by (auto simp: algebra_simps closed_segment_commute)

end