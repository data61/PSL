section\<open>Runge-Kutta methods\<close>
theory Runge_Kutta
imports
  "HOL-Analysis.Analysis"
  One_Step_Method
  "HOL-Library.Float"
  Affine_Arithmetic.Executable_Euclidean_Space
  Ordinary_Differential_Equations.Multivariate_Taylor
begin

subsection \<open>aux\<close>

lemma scale_back: "(r, r *\<^sub>R x) = r *\<^sub>R (1, x)" "(0, r *\<^sub>R x) = r *\<^sub>R (0, x)"
  by simp_all

lemma integral_normalize_bounds:
  fixes s t::real
  assumes "t \<le> s"
  assumes "f integrable_on {t .. s}"
  shows [symmetric]: "(s - t) *\<^sub>R integral {0 .. 1} (\<lambda>x. f ((s - t) *\<^sub>R x + t)) = integral {t..s} f"
proof cases
  assume "s > t"
  hence "s - t \<noteq> 0" "0 \<le> s - t" by simp_all
  from assms have "(f has_integral integral {t .. s} f) (cbox t s)"
    by (auto simp: integrable_integral)
  from has_integral_affinity[OF this \<open>s - t \<noteq> 0\<close>, of t]
  have "((\<lambda>x. f ((s - t) * x + t)) has_integral (1 / \<bar>s - t\<bar>) *\<^sub>R integral {t..s} f)
    ((\<lambda>x. (x - t) / (s - t)) ` {t..s})"
    using \<open>s > t\<close>
    by (simp add: divide_simps)
  also
  have "t < s \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> x * (s - t) + t \<le> s" for x
    by (auto simp add: algebra_simps dest: mult_left_le_one_le[OF \<open>0 \<le> s - t\<close>])
  then have "((\<lambda>x. (x - t) / (s - t)) ` {t..s}) = {0 .. 1}"
    using \<open>s > t\<close>
    by (auto intro!: image_eqI[where x="x * (s - t) + t" for x]
      simp: divide_simps)
  finally
  have "integral {0..1} (\<lambda>x. f ((s - t) * x + t)) = (1 / \<bar>s - t\<bar>) *\<^sub>R integral {t..s} f"
    by (rule integral_unique)
  then show ?thesis
    using \<open>s > t\<close> by simp
qed (insert assms, simp)

lemma
  has_integral_integral_eqI:
  "f integrable_on s \<Longrightarrow> integral s f = k \<Longrightarrow> (f has_integral k) s"
  by (simp add:  has_integral_integral)

lemma convex_scaleR_sum2:
  assumes "x \<in> G" "y \<in> G" "convex G"
  assumes "a \<ge> 0" "b \<ge> 0" "a + b \<noteq> 0"
  shows "(a *\<^sub>R x + b *\<^sub>R y) /\<^sub>R (a + b) \<in> G"
proof -
  have "(a / (a + b)) *\<^sub>R x + (b / (a + b)) *\<^sub>R y \<in> G"
    using assms
    by (intro convexD) (auto simp: divide_simps)
  then show ?thesis
    by (auto simp: algebra_simps divide_simps)
qed

lemma sum_by_parts_ivt:
  assumes "finite X"
  assumes "convex G"
  assumes "\<And>i. i \<in> X \<Longrightarrow> g i \<in> G"
  assumes "\<And>i. i \<in> X \<Longrightarrow> 0 \<le> c i"
  obtains y where "y \<in> G" "(\<Sum>x\<in>X. c x *\<^sub>R g x) = sum c X *\<^sub>R y" | "G = {}"
proof (atomize_elim, cases "sum c X = 0", goal_cases)
  case pos: 2
  let ?y = "(\<Sum>x\<in>X. (c x / sum c X) *\<^sub>R g x)"
  have "?y \<in> G" using pos
    by (intro convex_sum)
      (auto simp: sum_divide_distrib[symmetric]
        intro!: divide_nonneg_nonneg assms sum_nonneg)
  thus ?case
    by (auto intro!: exI[where x = ?y] simp: scaleR_right.sum pos)
qed (insert assms, auto simp: sum_nonneg_eq_0_iff)

lemma
  integral_by_parts_near_bounded_convex_set:
  assumes f: "(f has_integral I) (cbox a b)"
  assumes s: "((\<lambda>x. f x *\<^sub>R g x) has_integral P) (cbox a b)"
  assumes G: "\<And>x. x \<in> cbox a b \<Longrightarrow> g x \<in> G"
  assumes nonneg: "\<And>x. x \<in> cbox a b \<Longrightarrow> f x \<ge> 0"
  assumes convex: "convex G"
  assumes bounded: "bounded G"
  shows "infdist P ((*\<^sub>R) I ` G) = 0"
proof (rule dense_eq0_I, cases)
  fix e'::real assume e0: "0 < e'"
  assume "G \<noteq> {}"
  from bounded obtain bnd where bnd: "\<And>y. y \<in> G \<Longrightarrow> norm y < bnd" "bnd > 0"
    by (meson bounded_pos gt_ex le_less_trans norm_ge_zero)
  define e where "e = min (e' / 2) (e' / 2 / bnd)"
  have e: "e > 0" using e0
    by (auto simp add: e_def intro!: divide_pos_pos \<open>bnd > 0\<close>)
  from
    has_integral[of f I a b,                THEN iffD1, OF f, rule_format, OF e]
    has_integral[of "\<lambda>x. f x *\<^sub>R g x" P a b, THEN iffD1, OF s, rule_format, OF e]
  obtain d1 d3
  where d1: "gauge d1"
    "\<And>p. p tagged_division_of cbox a b \<Longrightarrow> d1 fine p \<Longrightarrow>
      norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - I) < e"
  and d3: "gauge d3"
    "\<And>p. p tagged_division_of cbox a b \<Longrightarrow> d3 fine p \<Longrightarrow>
      norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x *\<^sub>R g x) - P) < e"
    by auto
  define d where "d x = d1 x \<inter> d3 x" for x
  from d1(1) d3(1)
  have "gauge d" by (auto simp add: d_def [abs_def])
  from fine_division_exists[OF this, of a b]
  obtain p where p: "p tagged_division_of cbox a b" "d fine p"
    by metis
  from tagged_division_of_finite[OF p(1)]
  have "finite p" .

  from \<open>d fine p\<close> have "d1 fine p" "d3 fine p"
    by (auto simp: d_def [abs_def] fine_Int)
  have f_less: "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - I) < e"
    (is "norm (?f - I) < _")
    by (rule d1(2)[OF p(1)]) fact
  have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x *\<^sub>R g x) - P) < e"
    (is "norm (?s - P) < _")
    by (rule d3(2)[OF p(1)]) fact

  hence "dist (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x *\<^sub>R g x) P < e"
    by (simp add: dist_norm)
  also
  let ?h = "(\<lambda>x k y. (content k * f x) *\<^sub>R y)"
  let ?s' = "\<lambda>y. sum (\<lambda>(x, k). ?h x k y) p"
  let ?g = "\<lambda>(x, k). g x"
  let ?c = "\<lambda>(x, k). content k * f x"
  have Pi: "\<And>x. x \<in> p \<Longrightarrow> ?g x \<in> G" "\<And>x. x \<in> p \<Longrightarrow> ?c x \<ge> 0"
    using nonneg G p
    using tag_in_interval[OF p(1)]
    by (auto simp: intro!: mult_nonneg_nonneg)
  obtain y where y: "y \<in> G" "?s = ?s' y"
    by (rule sum_by_parts_ivt[OF \<open>finite p\<close> \<open>convex G\<close> Pi])
      (auto simp: split_beta' scaleR_sum_left \<open>G \<noteq> {}\<close>)
  note this(2)
  also have "(\<Sum>(x, k)\<in>p. (content k * f x) *\<^sub>R y) = ?f *\<^sub>R y"
    by (auto simp: scaleR_left.sum intro!: sum.cong)
  finally have "dist P ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) *\<^sub>R y) \<le> e"
    by (simp add: dist_commute)
  moreover have "dist (I *\<^sub>R y) ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) *\<^sub>R y) \<le> norm y * e"
    using f_less
    by (auto simp add: dist_real_def mult.commute [of _ "norm y"]
      intro!: mult_left_mono)
  ultimately
  have "dist P (I *\<^sub>R y) \<le> e + norm y * e"
    by (rule dist_triangle_le[OF add_mono])
  with _ have "infdist P ((*\<^sub>R) I ` G) \<le> e + norm y * e"
    using y(1)
    by (intro infdist_le2) auto
  also have "norm y * e < bnd * e"
    by (rule mult_strict_right_mono)
      (auto simp: \<open>e > 0\<close> less_imp_le intro!: bnd \<open>y \<in> G\<close>)
  also have "bnd * e \<le> e' / 2"
    using \<open>e' > 0\<close> \<open>bnd > 0\<close>
    by (auto simp: e_def min_def divide_simps)
  also have "e \<le> e' / 2" by (simp add: e_def)
  also have "e' / 2 + e' / 2 = e'" by simp
  finally show "\<bar>infdist P ((*\<^sub>R) I ` G)\<bar> \<le> e'"
    by (auto simp: infdist_nonneg)
qed (simp add: infdist_def)

lemma
  integral_by_parts_in_bounded_closed_convex_set:
  assumes f: "(f has_integral I) (cbox a b)"
  assumes s: "((\<lambda>x. f x *\<^sub>R g x) has_integral P) (cbox a b)"
  assumes G: "\<And>x. x \<in> cbox a b \<Longrightarrow> g x \<in> G"
  assumes nonneg: "\<And>x. x \<in> cbox a b \<Longrightarrow> f x \<ge> 0"
  assumes bounded: "bounded G"
  assumes closed: "closed G"
  assumes convex: "convex G"
  assumes nonempty: "cbox a b \<noteq> {}"
  shows "P \<in> (*\<^sub>R) I ` G"
proof -
  let ?IG = "(*\<^sub>R) I ` G"
  from bounded closed have "bounded ?IG" "closed ?IG"
    by (simp_all add: bounded_scaling closed_scaling)
  have "G \<noteq> {}" using nonempty G by auto
  then show ?thesis
    using \<open>closed ?IG\<close>
    by (subst in_closed_iff_infdist_zero)
      (auto intro!: assms compact_imp_bounded integral_by_parts_near_bounded_convex_set)
qed

lemma
  integral_by_parts_in_bounded_set:
  assumes f: "(f has_integral I) (cbox a b)"
  assumes s: "((\<lambda>x. f x *\<^sub>R g x) has_integral P) (cbox a b)"
  assumes nonneg: "\<And>x. x \<in> cbox a b \<Longrightarrow> f x \<ge> 0"
  assumes bounded: "bounded (g ` cbox a b)"
  assumes nonempty: "cbox a b \<noteq> {}"
  shows "P \<in> (*\<^sub>R) I ` closure (convex hull (g ` cbox a b))"
proof -
  have "x \<in> cbox a b \<Longrightarrow> g x \<in> closure (convex hull g ` cbox a b)" for x
    by (meson closure_subset hull_subset imageI subsetCE)
  then show ?thesis
    by (intro integral_by_parts_in_bounded_closed_convex_set[OF f s _ nonneg _ _ _ nonempty])
      (auto intro!: bounded_closure bounded_convex_hull bounded convex_closure
        simp: convex_convex_hull)
qed

lemma snd_imageI: "(a, b) \<in> R \<Longrightarrow> b \<in> snd ` R"
  by force

lemma in_minus_Collect: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> a - b \<in> {x - y|x y. x \<in> A \<and> y \<in> B}"
  by blast

lemma closure_minus_Collect:
  fixes A B::"'a::real_normed_vector set"
  shows
  "{x - y|x y. x \<in> closure A \<and> y \<in> closure B} \<subseteq> closure {x - y|x y. x \<in> A \<and> y \<in> B}"
proof -
  have image: "(\<lambda>(x, y). x - y) ` (A \<times> B) = {x - y|x y. x \<in> A \<and> y \<in> B}" for A B::"'a set"
    by auto
  have "{x - y|x y. x \<in> closure A \<and> y \<in> closure B} = (\<lambda>(x, y). x - y) ` closure (A \<times> B)"
    unfolding closure_Times
    by (rule image[symmetric])
  also have "\<dots> \<subseteq> closure ((\<lambda>(x, y). x - y) ` (A \<times> B))"
    by (rule image_closure_subset)
      (auto simp: split_beta' intro!: subsetD[OF closure_subset]
        continuous_at_imp_continuous_on)
  also note image
  finally show ?thesis .
qed

lemma convex_hull_minus_Collect:
  fixes A B::"'a::real_normed_vector set"
  shows
  "{x - y|x y. x \<in> convex hull A \<and> y \<in> convex hull B} = convex hull {x - y|x y. x \<in> A \<and> y \<in> B}"
proof -
  have image: "(\<lambda>(x, y). x - y) ` (A \<times> B) = {x - y|x y. x \<in> A \<and> y \<in> B}" for A B::"'a set"
    by auto
  have "{x - y|x y. x \<in> convex hull A \<and> y \<in> convex hull B} = (\<lambda>(x, y). x - y) ` (convex hull (A \<times> B))"
    unfolding convex_hull_Times
    by (rule image[symmetric])
  also have "\<dots> = convex hull ((\<lambda>(x, y). x - y) ` (A \<times> B))"
    apply (rule convex_hull_linear_image)
    by unfold_locales (auto simp: algebra_simps)
  also note image
  finally show ?thesis .
qed

lemma set_minus_subset:
  "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> {a - b |a b. a \<in> A \<and> b \<in> B} \<subseteq> {a - b |a b. a \<in> C \<and> b \<in> D}"
  by auto

lemma (in bounded_bilinear) bounded_image:
  assumes "bounded (f ` s)"
  assumes "bounded (g ` s)"
  shows "bounded ((\<lambda>x. prod (f x) (g x)) ` s)"
proof -
  from nonneg_bounded obtain K
  where K: "\<And>a b. norm (prod a b) \<le> norm a * norm b * K" and "0 \<le> K"
    by auto
  from assms obtain F G
  where F: "\<And>x. x \<in> s \<Longrightarrow> norm (f x) \<le> F"
    and G: "\<And>x. x \<in> s \<Longrightarrow> norm (g x) \<le> G"
    and nonneg: "0 \<le> F" "0 \<le> G"
    by (auto simp: bounded_pos intro: less_imp_le)
  have "norm (prod (f x) (g x)) \<le> F * G * K" if x: "x \<in> s" for x
    using F[OF x] G[OF x] nonneg \<open>0 \<le> K\<close>
    by (auto intro!: mult_mono mult_nonneg_nonneg order_trans[OF K])
  thus ?thesis
    by (auto simp: bounded_iff)
qed

lemmas bounded_scaleR_image = bounded_bilinear.bounded_image[OF bounded_bilinear_scaleR]
  and bounded_blinfun_apply_image = bounded_bilinear.bounded_image[OF bounded_bilinear_blinfun_apply]

lemma bounded_plus_image:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` s)"
  assumes "bounded (g ` s)"
  shows "bounded ((\<lambda>x. f x + g x) ` s)"
proof -
  from assms obtain F G
  where F: "\<And>x. x \<in> s \<Longrightarrow> norm (f x) \<le> F"
    and G: "\<And>x. x \<in> s \<Longrightarrow> norm (g x) \<le> G"
    by (auto simp: bounded_iff)
  have "norm (f x + g x) \<le> F + G" if x: "x \<in> s" for x
    using F[OF x] G[OF x]
    by norm
  thus ?thesis
    by (auto simp: bounded_iff)
qed

lemma bounded_uminus_image[simp]:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  shows "bounded ((\<lambda>x. - f x) ` s) \<longleftrightarrow> bounded (f ` s)"
  apply (subst (2) bounded_uminus[symmetric])
  unfolding image_image
  by simp

lemma bounded_minus_image:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` s)"
  assumes "bounded (g ` s)"
  shows "bounded ((\<lambda>x. f x - g x) ` s)"
  using bounded_plus_image[of f s "\<lambda>x. - g x"] assms
  by simp

lemma bounded_Pair_image:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  fixes g::"'a \<Rightarrow> 'c::real_normed_vector"
  assumes "bounded (f ` s)"
  assumes "bounded (g ` s)"
  shows "bounded ((\<lambda>x. (f x, g x)) ` s)"
proof -
  from assms obtain F G
  where F: "\<And>x. x \<in> s \<Longrightarrow> norm (f x) \<le> F"
    and G: "\<And>x. x \<in> s \<Longrightarrow> norm (g x) \<le> G"
    by (auto simp: bounded_iff)
  have "norm (f x, g x) \<le> F + G" if x: "x \<in> s" for x
    using F[OF x] G[OF x]
    by (intro order_trans[OF norm_Pair_le]) norm
  thus ?thesis
    by (auto simp: bounded_iff)
qed

lemma closed_scaleR_image_iff:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  shows "closed ((\<lambda>x. r *\<^sub>R (f x)) ` R) \<longleftrightarrow> (r = 0 \<or> closed (f ` R))" (is "?l \<longleftrightarrow> _ \<or> ?r")
proof safe
  assume ?r
  from closed_scaling[OF this] show ?l
    by (auto simp: image_image)
next
  assume l: ?l
  {
    assume "r \<noteq> 0"
    with closed_scaling[OF l, of "inverse r"]
    have "?r"
      by (auto simp: image_image)
  } then show "\<not> ?r \<Longrightarrow> r = 0" by blast
qed (simp add: image_constant_conv)

lemma closed_translation_iff[simp]:
  fixes y::"'a::real_normed_vector"
  shows "closed ((\<lambda>x. f x + y) ` S) \<longleftrightarrow> closed (f ` S)"
    "closed ((\<lambda>x. y + f x) ` S) \<longleftrightarrow> closed (f ` S)"
  using closed_translation[of "f ` S" y] closed_translation[of "(+) y ` f ` S" "- y"]
  by (auto simp: add.commute image_image cong: image_cong)

lemma closed_minus_translation_iff[simp]:
  fixes y::"'a::real_normed_vector"
  shows "closed ((\<lambda>x. f x - y) ` S) \<longleftrightarrow> closed (f ` S)"
  using closed_translation_iff(1)[of f "- y" S]
  by simp

lemma convex_scaleR_image_iff:
  fixes f::"'a \<Rightarrow> 'b::real_normed_vector"
  shows "convex ((\<lambda>x. r *\<^sub>R (f x)) ` R) \<longleftrightarrow> (r = 0 \<or> convex (f ` R))" (is "?l \<longleftrightarrow> _ \<or> ?r")
proof safe
  assume ?r
  from convex_scaling[OF this] show ?l
    by (auto simp: image_image)
next
  assume l: ?l
  {
    assume "r \<noteq> 0"
    with convex_scaling[OF l, of "inverse r"]
    have "?r"
      by (auto simp: image_image)
  } then show "\<not> ?r \<Longrightarrow> r = 0" by blast
qed (simp add: image_constant_conv)

lemma convex_translation_iff[simp]:
  fixes y::"'a::real_normed_vector"
  shows "convex ((\<lambda>x. f x + y) ` S) \<longleftrightarrow> convex (f ` S)"
    "convex ((\<lambda>x. y + f x) ` S) \<longleftrightarrow> convex (f ` S)"
  using convex_translation[of "f ` S" y] convex_translation[of "(+) y ` f ` S" "- y"]
  by (auto simp: add.commute image_image cong: image_cong)

lemma convex_minus_translation_iff[simp]:
  fixes y::"'a::real_normed_vector"
  shows "convex ((\<lambda>x. f x - y) ` S) \<longleftrightarrow> convex (f ` S)"
  using convex_translation_iff(1)[of f "- y" S]
  by simp


text\<open>\label{sec:rk}\<close>

subsection \<open>Definitions\<close>
text\<open>\label{sec:rk-definition}\<close>

declare sum.cong[fundef_cong]
fun rk_eval :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real \<Rightarrow> 'a::real_vector \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "rk_eval A c f t h x j =
  f (t + h * c j) (x + h *\<^sub>R (\<Sum>l=1 ..< j. A j l *\<^sub>R rk_eval A c f t h x l))"

primrec rk_eval_dynamic :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real\<times>'a::{comm_monoid_add, scaleR} \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "rk_eval_dynamic A c f t h x 0 = (\<lambda>i. 0)"
| "rk_eval_dynamic A c f t h x (Suc j) =
  (let K = rk_eval_dynamic A c f t h x j in
  K(Suc j:=f (t + h * c (Suc j), x + h *\<^sub>R (\<Sum>l=1..j. A (Suc j) l *\<^sub>R K l))))"

definition rk_increment where
  "rk_increment f s A b c h t x = (\<Sum>j=1..s. b j *\<^sub>R rk_eval A c f t h x j)"

definition rk_increment' where
  "rk_increment' error f s A b c h t x =
  eucl_down error (\<Sum>j=1..s. b j *\<^sub>R rk_eval A c f t h x j)"

definition euler_increment where
  "euler_increment f = rk_increment f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler where
  "euler f = grid_function (discrete_evolution (euler_increment f))"

definition euler_increment' where
"euler_increment' e f = rk_increment' e f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler' where
  "euler' e f = grid_function (discrete_evolution (euler_increment' e f))"

definition rk2_increment where
  "rk2_increment x f = rk_increment f 2 (\<lambda>i j. if i = 2 \<and> j = 1 then x else 0)
    (\<lambda>i. if i = 1 then 1 - 1 / (2 * x) else 1 / (2 * x)) (\<lambda>i. if i = 2 then x else 0)"

definition rk2 where
  "rk2 x f = grid_function (discrete_evolution (rk2_increment x f))"

subsection \<open>Euler method is consistent \label{sec:rk-euler-cons}\<close>

lemma euler_increment:
  shows "euler_increment f h t x = f t x"
  unfolding euler_increment_def rk_increment_def
  by (subst rk_eval.simps) (simp del: rk_eval.simps)

lemma euler_float_increment:
  shows "euler_increment' e f h t x = eucl_down e (f t x)"
  unfolding euler_increment'_def rk_increment'_def
  by (subst rk_eval.simps) (simp del: rk_eval.simps)

lemma euler_lipschitz:
  assumes t: "t \<in> {t0..T}"
  assumes lipschitz: "\<forall>t\<in>{t0..T}. L-lipschitz_on D' (\<lambda>x. f t x)"
  shows "L-lipschitz_on D' (euler_increment f h t)"
  using t lipschitz
  by (simp add: lipschitz_on_def euler_increment del: One_nat_def)

lemma rk2_increment:
  shows "rk2_increment p f h t x =
    (1 - 1 / (p * 2)) *\<^sub>R f t x +
    (1 / (p * 2)) *\<^sub>R f (t + h * p) (x + (h * p) *\<^sub>R f t x)"
  unfolding rk2_increment_def rk_increment_def
  apply (subst rk_eval.simps)
  apply (simp del: rk_eval.simps add: numeral_2_eq_2)
  apply (subst rk_eval.simps)
  apply (simp del: rk_eval.simps add:  field_simps)
  done

subsection \<open>Set-Based Consistency of Euler Method \label{sec:setconsistent}\<close>

context derivative_on_prod
begin

lemma euler_consistent_traj_set:
  fixes t
  assumes ht: "0 \<le> h" "t + h \<le> u"
  assumes T: "{t..u} \<subseteq> T"
  assumes x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f s (x s)) (at s within {t..u})"
  assumes x: "\<And>s. s \<in> {t..u} \<Longrightarrow> x s \<in> X"
  assumes R: "\<And>s. s \<in> {t..u} \<Longrightarrow>
    discrete_evolution (euler_increment f) (t + h) t (x t) + (h\<^sup>2 / 2) *\<^sub>R (f' (s, x s)) (1, f s (x s)) \<in> R"
  assumes bcc: "bounded R" "closed R" "convex R"
  shows "x (t + h) \<in> R"
proof cases
  assume "h = 0"
  with assms show ?thesis
    by (auto simp: discrete_evolution_def)
next
  assume "h \<noteq> 0"
  from this ht have "t < u" by simp
  from ht have line_subset: "(\<lambda>ta. t + ta * h) ` {0..1} \<subseteq> {t..u}"
    by (auto intro!: order_trans[OF add_left_mono[OF mult_left_le_one_le]])
  hence line_in: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> 1 \<Longrightarrow> t + s * h \<in> {t..u}"
    by (rule subsetD) auto
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  let ?T = "{t..u}"
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  from \<open>t < u\<close> have "t \<in> ?T" by auto
  from \<open>t < u\<close> have tx: "t \<in> T" "x t \<in> X" using assms by auto
  from tx assms have "0 \<le> norm (f t (x t))" by simp
  have x_diff: "\<And>s. s \<in> ?T \<Longrightarrow> x differentiable at s within ?T"
    by (rule differentiableI, rule x'[simplified has_vector_derivative_def])

  note [continuous_intros] =
    continuous_on_compose2[OF has_derivative_continuous_on[OF f'] continuous_on_Pair, simplified]
    continuous_on_compose2[OF has_derivative_continuous_on[OF x'[unfolded has_vector_derivative_def]], simplified]

  let ?p = "(\<lambda>t. f' (t, x t) (1, f t (x t)))"
  define diff where "diff \<equiv> \<lambda>n::nat. if n = 0 then x else if n = 1 then \<lambda>t. f t (x t) else ?p"
  have diff_0[simp]: "diff 0 = x" by (simp add: diff_def)
  have diff: "(diff m has_vector_derivative diff (Suc m) ta) (at ta within {t..t + h})"
    if mta: "m < 2" "t \<le> ta" "ta \<le> t + h" for m::nat and ta::real
  proof -
    have image_subset: "(\<lambda>xa. (xa, x xa)) ` {t..u} \<subseteq> {t..u} \<times> X"
      using assms by auto
    note has_derivative_subset[OF _ image_subset, derivative_intros]
    note f'[derivative_intros]
    note x'[simplified has_vector_derivative_def, derivative_intros]
    have [simp]: "\<And>c x'. c *\<^sub>R f' (ta, x ta) x' = f' (ta, x ta) (c *\<^sub>R x')"
      using mta ht assms
      by (force intro!: f' linear_cmul[symmetric] has_derivative_linear)
    have f_comp': "((\<lambda>t. f t (x t)) has_vector_derivative f' (ta, x ta) (1, f ta (x ta))) (at ta within {t..u})"
      unfolding has_vector_derivative_def
      using assms ht mta by (auto intro!: derivative_eq_intros)
    then show ?thesis
      using mta ht
      by (auto simp: diff_def intro!: has_vector_derivative_within_subset[OF _ subset] x')
  qed

  from Taylor_has_integral[of 2 diff x t "t + h", OF _ _ diff] \<open>0 \<le> h\<close>
  have Taylor: "((\<lambda>xa. (t + h - xa) *\<^sub>R f' (xa, x xa) (1, f xa (x xa))) has_integral x (t + h) - (x t + h *\<^sub>R f t (x t))) {t..t + h}"
    by (simp add: eval_nat_numeral diff_def)

  have *: "h\<^sup>2 / 2 = content {t..t + h} *\<^sub>R (t + h) - (if t \<le> t + h then (t + h)\<^sup>2 / 2 - t\<^sup>2 / 2 else 0)"
    using \<open>0 \<le> h\<close>
    by (simp add: algebra_simps power2_eq_square divide_simps)
  have integral: "((-) (t + h) has_integral h\<^sup>2 / 2) (cbox t (t + h))"
    unfolding * cbox_interval
    using \<open>0 \<le> h\<close>
    by (auto intro!: has_integral_diff ident_has_integral[THEN has_integral_eq_rhs]
        has_integral_const_real[THEN has_integral_eq_rhs])
  from Taylor_has_integral[of 2 diff x t "t + h", OF _ _ diff] \<open>0 \<le> h\<close>
  have Taylor: "((\<lambda>xa. (t + h - xa) *\<^sub>R f' (xa, x xa) (1, f xa (x xa))) has_integral x (t + h) - (x t + h *\<^sub>R f t (x t))) {t..t + h}"
    by (simp add: eval_nat_numeral diff_def)

  define F' where "F' \<equiv> (\<lambda>y. (2 / h\<^sup>2) *\<^sub>R (y - discrete_evolution (euler_increment f) (t + h) t (x t))) ` R"
  have "x (t + h) - (x t + h *\<^sub>R f t (x t)) \<in> (*\<^sub>R) (h\<^sup>2 / 2) ` F'"
    apply (rule integral_by_parts_in_bounded_closed_convex_set[OF integral Taylor[unfolded interval_cbox]])
    subgoal using R \<open>h \<noteq> 0\<close> \<open>0 \<le> h\<close> subset by (force simp: F'_def)
    by (auto intro!: bounded_scaleR_image bounded_minus_image closed_injective_image_subspace bcc \<open>0 \<le> h\<close>
      simp: F'_def image_constant_conv closed_scaleR_image_iff convex_scaleR_image_iff \<open>h \<noteq> 0\<close>)
  then show ?thesis
    using \<open>h \<noteq> 0\<close>
    by (auto simp add: discrete_evolution_def euler_increment F'_def)
qed

end

lemma numeral_6_eq_6: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by linarith

context begin

interpretation blinfun_syntax .

definition "heun_remainder1 x f f' f'' t h s
  = (h ^ 3 / 6) *\<^sub>R (f'' (h * s + t, x (h * s + t)) $ (1::real, f (h * s + t, x (h * s + t))) $ (1::real, f (h * s + t, x (h * s + t))) +
                    f' (h * s + t, x (h * s + t)) $ (0::real, f' (h * s + t, x (h * s + t)) $ (1, f (h * s + t, x (h * s + t)))))"

definition "heun_remainder2 p x f f'' t h s =
  (h ^ 3 * p / 4) *\<^sub>R f'' (t + s * h * p, x t + (s * h * p) *\<^sub>R f (t, (x t))) $ (1::real, f (t, (x t))) $ (1::real, f (t, (x t)))"

lemma rk2_consistent_traj_set:
  fixes x ::"real \<Rightarrow> 'a::banach" and t
    and f' :: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow>\<^sub>L 'a"
    and g' :: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow> 'a"
    and f'' :: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow>\<^sub>L (real \<times> 'a) \<Rightarrow>\<^sub>L 'a"
    and g'' :: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow> (real \<times> 'a) \<Rightarrow>\<^sub>L 'a"
  assumes ht: "0 \<le> h" "t + h \<le> u"
  assumes T: "{t..u} \<subseteq> T" and X_nonempty: "X \<noteq> {}" and convex_X: "convex X"
  assumes x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within {t..u})"
  assumes f': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow> (f has_derivative g' tx) (at tx)"
  assumes f'': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow>  (f' has_derivative g'' tx) (at tx)"
  assumes g': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow> g' tx = f' tx"
  assumes g'': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow>  g'' tx = f'' tx"
  assumes f''_bounded: "bounded (f'' ` (T \<times> X))"
  assumes x: "\<And>s. s \<in> {t..u} \<Longrightarrow> x s \<in> X"
  assumes p: "0 < p" "p \<le> 1"
  assumes step_in: "x t + (h * p) *\<^sub>R f (t, (x t)) \<in> X"
  assumes ccR: "convex R" "closed R"
  assumes R: "\<And>s1 s2. 0 \<le> s1 \<Longrightarrow> s1 \<le> 1 \<Longrightarrow> 0 \<le> s2 \<Longrightarrow> s2 \<le> 1 \<Longrightarrow>
    discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) +
      heun_remainder1   x f f' f'' t h s1 -
      heun_remainder2 p x f    f'' t h s2 \<in> R"
  shows "x (t + h) \<in> R"
proof cases
  assume "h = 0"
  with R[of 0 0]
  show ?thesis
    by (auto simp: discrete_evolution_def heun_remainder1_def heun_remainder2_def)
next
  have f': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow> (f has_derivative blinfun_apply (f' tx)) (at tx)"
    using f' g'
    by simp
  have f'': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow>  (f' has_derivative blinfun_apply (f'' tx)) (at tx)"
    using f'' g''
    by simp
  assume "h \<noteq> 0"
  from this ht have "t < u" by simp
  have [simp]: "p \<noteq> 0" using p by simp
  from \<open>h \<ge> 0\<close> \<open>h \<noteq> 0\<close> have "h > 0" by simp

  let ?r = "\<lambda>a. f'' (t + a, x t + a *\<^sub>R f (t, x t)) (1, f (t, x t))
      (1, f (t, x t))"
  let ?q = "\<lambda>s. f'' (s, x s) (1, f (s, x s)) (1, f (s, x s)) +
     f' (s, x s) (0, f' (s, x s) (1, f (s, x s)))"

  let ?d = "\<lambda>tq tr. (h^3) *\<^sub>R ((1/6)*\<^sub>R ?q tq - (p / 4) *\<^sub>R ?r tr)"

  from ht have line_subset: "(\<lambda>ta. t + ta * h) ` {0..1} \<subseteq> {t..u}"
    by (auto intro!: order_trans[OF add_left_mono[OF mult_left_le_one_le]])
  hence line_in: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> 1 \<Longrightarrow> t + s * h \<in> {t..u}"
    by (rule subsetD) auto
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  let ?T = "{t..u}"
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  from \<open>t < u\<close> have "t \<in> ?T" by auto
  from \<open>t < u\<close> have tx: "t \<in> T" "x t \<in> X" using T ht x by auto

  from tx assms have "0 \<le> norm (f (t, x t))" by simp
  have x_diff: "\<And>s. s \<in> ?T \<Longrightarrow> x differentiable at s within ?T"
    by (rule differentiableI, rule x'[simplified has_vector_derivative_def])
  let ?p = "(\<lambda>t. f' (t, x t) (1, f (t, x t)))"
  note f'[derivative_intros]
  note f''[derivative_intros]
  note x'[simplified has_vector_derivative_def, derivative_intros]

  have x_cont: "continuous_on {t..u} x"
    by (rule continuous_on_vector_derivative) (rule x')
  have f_cont: "continuous_on (T \<times> X) f"
    apply (rule has_derivative_continuous_on)
    apply (rule has_derivative_at_withinI)
    by (rule assms)
  have f'_cont: "continuous_on (T \<times> X) f'"
    apply (rule has_derivative_continuous_on)
    apply (rule has_derivative_at_withinI)
    by (rule assms)
  note [continuous_intros] =
    continuous_on_compose2[OF x_cont]
    continuous_on_compose2[OF f_cont]
    continuous_on_compose2[OF f'_cont]

  from f' f''
  have f'_within: "tx \<in> T \<times> X \<Longrightarrow> (f has_derivative f' tx) (at tx within T \<times> X)"
    and f''_within: "tx \<in> T \<times> X \<Longrightarrow> (f' has_derivative f'' tx) (at tx within T \<times> X)" for tx
    by (auto intro: has_derivative_at_withinI)

  from f'' have f''_within: "tx \<in> T \<times> X \<Longrightarrow> (f' has_derivative ($) (f'' tx)) (at tx within T \<times> X)" for tx
    by (auto intro: has_derivative_at_withinI)
  note [derivative_intros] =
    has_derivative_in_compose2[OF f'_within]
    has_derivative_in_compose2[OF f''_within]
  have p': "\<And>s. s \<in> {t .. u} \<Longrightarrow> (?p has_vector_derivative ?q s) (at s within ?T)"
    unfolding has_vector_derivative_def
    using T x
    by (auto intro!: derivative_eq_intros
      simp: scale_back blinfun.bilinear_simps algebra_simps
      simp del: scaleR_Pair)
  define diff where "diff n =
    (if n = 0 then x else if n = 1 then \<lambda>t. f (t, x t) else if n = 2 then ?p else ?q)" for n :: nat
  have diff_0[simp]: "diff 0 = x" by (simp add: diff_def)
  have diff: "(diff m has_vector_derivative diff (Suc m) ta) (at ta within {t..t + h})"
    if mta: "m < 3" "t \<le> ta" "ta \<le> t + h" for m::nat and ta::real
  proof -
    have image_subset: "(\<lambda>xa. (xa, x xa)) ` {t..u} \<subseteq> {t..u} \<times> X"
      using assms by auto
    note has_derivative_in_compose[where f="(\<lambda>xa. (xa, x xa))" and g = f, derivative_intros]
    note has_derivative_subset[OF _ image_subset, derivative_intros]
    note f'[derivative_intros]
    note x'[simplified has_vector_derivative_def, derivative_intros]
    have [simp]: "\<And>c x'. c *\<^sub>R f' (ta, x ta) x' = f' (ta, x ta) (c *\<^sub>R x')"
      using mta ht assms T x
      by (force intro!: f' linear_cmul[symmetric] has_derivative_linear)
    have "((\<lambda>t. f (t, x t)) has_vector_derivative f' (ta, x ta) (1, f (ta, x ta))) (at ta within {t..u})"
      unfolding has_vector_derivative_def
      using assms ht mta T x
      by (force intro!: derivative_eq_intros has_derivative_within_subset[OF f'])
    then show ?thesis
      using mta ht
      by (auto simp: diff_def intro!: has_vector_derivative_within_subset[OF _ subset] x' p')
  qed

  from Taylor_has_integral[of 3 diff x t "t + h", OF _ _ diff]
  have
    "((\<lambda>x. ((t + h - x) ^ 2 / 2) *\<^sub>R diff 3 x)
      has_integral
      x (t + h) - x t - h *\<^sub>R (f (t, x t)) - (h ^ 2 / (2::nat)) *\<^sub>R (?p t))
    (cbox t (t + h))"
    using ht \<open>h\<noteq>0\<close>
    by (auto simp: field_simps of_nat_Suc Pi_iff numeral_2_eq_2 numeral_3_eq_3
      numeral_6_eq_6 power2_eq_square diff_def scaleR_sum_right)
  from has_integral_affinity[OF this \<open>h \<noteq> 0\<close>, of t, simplified]
  have "((\<lambda>x. ((h - h * x)\<^sup>2 / 2) *\<^sub>R diff 3 (h * x + t)) has_integral
     (1 / \<bar>h\<bar>) *\<^sub>R (x (t + h) - x t - h *\<^sub>R f (t, x t) - (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) $ (1, f (t, x t))))
     ((\<lambda>x. x / h - t / h) ` {t..t + h})"
    by simp
  also have "((\<lambda>x. x / h - t / h) ` {t..t + h}) = {0 .. 1}"
    using \<open>h \<noteq> 0\<close> \<open>h \<ge> 0\<close>
    by (auto simp: divide_simps intro!: image_eqI[where x="x * h + t" for x])
  finally have "((\<lambda>x. ((h - h * x)\<^sup>2 / 2) *\<^sub>R diff 3 (h * x + t)) has_integral
   (1 / \<bar>h\<bar>) *\<^sub>R (x (t + h) - x t - h *\<^sub>R f (t, x t) - (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) $ (1, f (t, x t))))
    {0..1}" .
  from has_integral_cmul[OF this, of h]
  have Taylor: "((\<lambda>x. (1 - x)\<^sup>2 *\<^sub>R ((h^3 / 2) *\<^sub>R ?q (h * x + t))) has_integral
   (x (t + h) - x t - h *\<^sub>R f (t, x t) - (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) $ (1, f (t, x t))))
    {0..1}" (is "(?i_Taylor has_integral _) _")
    using \<open>h \<ge> 0\<close> \<open>h \<noteq> 0\<close>
    by (simp add: diff_def divide_simps algebra_simps power2_eq_square power3_eq_cube)
  have line_in': "h * y + t \<in> T"
    "x (h * y + t) \<in> X"
    "t \<le> h * y + t" "h * y + t \<le> u"
    if "y \<in> cbox 0 1" for y
    using line_in[of y] that T
    by (auto simp: algebra_simps x)
  let ?integral = "\<lambda>x. x^3/3 - x^2 + x"
  have intsquare: "((\<lambda>x. (1 - x)\<^sup>2) has_integral ?integral 1 - ?integral 0) (cbox 0 (1::real))"
    unfolding cbox_interval
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: derivative_eq_intros
        simp: has_vector_derivative_def power2_eq_square algebra_simps)
  have f_Taylor: "((\<lambda>s. (1 - s) *\<^sub>R f'' (x + s *\<^sub>R h) h h) has_integral f (x + h) - f x - f' x $ h) {0..1}"
    if line_in: "(\<lambda>s. x + s *\<^sub>R h) ` {0..1} \<subseteq> T \<times> X" for x h::"real*'a"
  proof -
    from that have *: "y \<in> T \<times> X" if "y \<in> closed_segment x (x + h)" for y
      using that
      by (force simp: closed_segment_def algebra_simps
        intro: image_eqI[where x = "1 - x" for x])
    define Df where "Df x i h1 h2 = (if i = 0 then f x else if i = 1 then f' x h2 else f'' x h2 h1)"
      for x h1 h2 and i::nat
    have "((\<lambda>y. ((1 - y) ^ (2 - 1) / fact (2 - 1)) *\<^sub>R Df (x + y *\<^sub>R h) 2 h h) has_integral
     f (x + h) - (\<Sum>i<2. (1 / fact i) *\<^sub>R Df x i h h)) {0..1}"
      apply (rule multivariate_Taylor_has_integral[of 2 Df h f x "T \<times> X"])
      subgoal by simp
      subgoal by (simp add: Df_def)
      subgoal premises prems for a i d
      proof -
        consider "i = 0" | "i = 1" | "i = 2" using prems by arith
        then show ?thesis
          by cases
            (use prems in \<open>auto simp: Df_def[abs_def] blinfun.bilinear_simps
                intro!: derivative_eq_intros intro: *\<close>)
      qed
      subgoal using "*" by blast
      done
    then show ?thesis
      by (simp add: Df_def eval_nat_numeral algebra_simps)
  qed

  let ?k = "\<lambda>t. f ((t, x t) + (h * p) *\<^sub>R (1, f (t, x t)))"

  have line_in: "(\<lambda>s. (t, x t) + s *\<^sub>R ((h * p) *\<^sub>R (1, f (t, x t)))) ` {0..1} \<subseteq> T \<times> X"
  proof (clarsimp, safe)
    fix s::real assume s: "0 \<le> s" "s \<le> 1"
    have "t + s * (h * p) = t + s * p * h"
      by (simp add: ac_simps)
    also have "\<dots> \<in> {t .. u}"
      using \<open>0 < p\<close> \<open>p \<le> 1\<close> s
      by (intro line_in) (auto intro!: mult_nonneg_nonneg mult_left_le_one_le mult_le_one)
    also note \<open>\<dots> \<subseteq> T\<close>
    finally show "t + s * (h * p) \<in> T" .
    show "x t + (s * (h * p)) *\<^sub>R f (t, x t) \<in> X"
      using convexD_alt[OF \<open>convex X\<close> tx(2) step_in s]
      by (simp add: algebra_simps)
  qed
  from f_Taylor[OF line_in, simplified]
  have k: "((\<lambda>s. (1 - s) *\<^sub>R ((h\<^sup>2 * p\<^sup>2) *\<^sub>R
          f'' (t + s * (h * p), x t + (s * (h * p)) *\<^sub>R f (t, x t)) $
            (1, f (t, x t)) $
            (1, f (t, x t))))
      has_integral ?k t - f (t, x t) - f' (t, x t) $ (h * p, (h * p) *\<^sub>R f (t, x t))) {0..1}"
    (is "(?i has_integral _) _")
    unfolding scale_back blinfun.bilinear_simps
    by (simp add: power2_eq_square algebra_simps)
  have rk2: "discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) =
    x t + h *\<^sub>R f (t, x t) -
    (h / (2 * p)) *\<^sub>R f (t, x t) +
    (h / (p * 2)) *\<^sub>R ?k t"
    (is "_ = ?rk2 t")
    unfolding rk2_increment_def discrete_evolution_def rk_increment_def
    apply (subst rk_eval.simps)
    supply rk_eval.simps[simp del]
    apply (simp add: eval_nat_numeral)
    apply (subst rk_eval.simps)
    apply (simp add: algebra_simps)
    done
  also have "\<dots> =
    x t + h *\<^sub>R f (t, x t) + (h / (2 * p)) *\<^sub>R (f' (t, x t) ((h * p), (h * p) *\<^sub>R f (t, x t)))
      + (h / (p * 2)) *\<^sub>R integral {0 .. 1} ?i"
    unfolding integral_unique[OF k]
    by (simp add: algebra_simps)
  also have "(h / (2 * p)) *\<^sub>R f' (t, x t) (h * p, (h * p) *\<^sub>R f (t, x t)) = (h\<^sup>2 / 2) *\<^sub>R ?p t"
    by (simp add: scale_back blinfun.bilinear_simps power2_eq_square
      del: scaleR_Pair)
  finally
  have "integral {0 .. 1} ?i =
      (discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) -
        x t - h *\<^sub>R f (t, x t) -
        (h\<^sup>2 / 2) *\<^sub>R ?p t) /\<^sub>R (h / (p * 2))"
    by (simp add: blinfun.bilinear_simps zero_prod_def[symmetric])
  with _ have "(?i has_integral
    (discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) -
      x t - h *\<^sub>R f (t, x t) -
      (h\<^sup>2 / 2) *\<^sub>R ?p t) /\<^sub>R
    (h / (p * 2))) {0 .. 1}"
    using k
    by (intro has_integral_integral_eqI) (rule has_integral_integrable)
  from has_integral_cmul[OF this, of "h / (p * 2)"]
  have discrete_Taylor:
    "((\<lambda>s. (1 - s) *\<^sub>R ((h^3 * p / 2) *\<^sub>R
          f'' (t + s * (h * p), x t + (s * (h * p)) *\<^sub>R f (t, x t)) $
            (1, f (t, x t)) $
            (1, f (t, x t)))) has_integral
    (discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) -
      x t - h *\<^sub>R f (t, x t) -
      (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) (1, f (t, x t)))) {0 .. 1}"
    (is "(?i_dTaylor has_integral _) _")
    using \<open>h > 0\<close>
    by (simp add: algebra_simps diff_divide_distrib power2_eq_square power3_eq_cube)
  have integral_minus: "((-) 1 has_integral 1/2) (cbox 0 (1::real))"
    by (auto intro!: has_integral_eq_rhs[OF has_integral_diff] ident_has_integral)

  have bounded_f: "bounded ((\<lambda>xa. f (h * xa + t, x (h * xa + t))) ` {0..1})"
    using \<open>0 \<le> h\<close>
    by (auto intro!: compact_imp_bounded compact_continuous_image continuous_intros mult_nonneg_nonneg
      simp: line_in')
  have bounded_f': "bounded ((\<lambda>xa. f' (h * xa + t, x (h * xa + t))) ` {0..1})"
    using \<open>0 \<le> h\<close>
    by (auto intro!: compact_imp_bounded compact_continuous_image continuous_intros
      simp: line_in')
  have bounded_f'': "bounded ((\<lambda>xa. f'' (h * xa + t, x (h * xa + t))) ` {0..1})"
    apply (subst o_def[of f'', symmetric])
    apply (subst image_comp[symmetric])
    apply (rule bounded_subset[OF f''_bounded])
    by (auto intro!: image_eqI line_in')
  have bounded_f''_2:
    "bounded ((\<lambda>xa. f'' (t + xa * (h * p), x t + (xa * (h * p)) *\<^sub>R f (t, x t))) ` {0..1})"
    apply (subst o_def[of f'', symmetric])
    apply (subst image_comp[symmetric])
    apply (rule bounded_subset[OF f''_bounded])
    using line_in
    by auto
  have 1: "x (t + h) - x t - h *\<^sub>R f (t, x t) - (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) $ (1, f (t, x t))
    \<in> (*\<^sub>R) (1 / 3) `
   closure
    (convex hull
     (\<lambda>xa. (h ^ 3 / 2) *\<^sub>R
            (f'' (h * xa + t, x (h * xa + t)) $
             (1,
              f (h * xa + t, x (h * xa + t))) $
             (1,
              f (h * xa + t, x (h * xa + t))) +
             f' (h * xa + t, x (h * xa + t)) $
             (0,
              f' (h * xa + t, x (h * xa + t)) $
              (1,
               f (h * xa + t,
                  x (h * xa + t)))))) `
     cbox 0 1)"
     by (rule rev_subsetD[OF integral_by_parts_in_bounded_set[OF intsquare Taylor[unfolded interval_cbox]]])
        (auto intro!: bounded_scaleR_image bounded_plus_image
         bounded_blinfun_apply_image bounded_Pair_image
         bounded_f'' bounded_f' bounded_f
         simp: image_constant[of 0])
  have 2: "discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) -
      x t - h *\<^sub>R f (t, x t) - (h\<^sup>2 / 2) *\<^sub>R f' (t, x t) $ (1, f (t, x t)) \<in>
    (*\<^sub>R) (1 / 2) ` closure (convex hull
       (\<lambda>s. (h ^ 3 * p / 2) *\<^sub>R
             f''
              (t + s * (h * p),
               x t +
               (s * (h * p)) *\<^sub>R f (t, x t)) $
             (1, f (t, x t)) $
             (1, f (t, x t))) `
       cbox 0 1)"
    by (rule integral_by_parts_in_bounded_set[OF integral_minus discrete_Taylor[unfolded interval_cbox]])
       (auto intro!: bounded_scaleR_image bounded_blinfun_apply_image
         bounded_f''_2 simp: image_constant[of 0])
  have "x (t + h) - discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t) \<in>
    {a - b|a b.
   a \<in>
   closure
    (convex hull (*\<^sub>R) (1/3) `
     (\<lambda>xa. (h ^ 3 / 2) *\<^sub>R
            (f'' (h * xa + t, x (h * xa + t)) $
             (1,
              f (h * xa + t, x (h * xa + t))) $
             (1,
              f (h * xa + t, x (h * xa + t))) +
             f' (h * xa + t, x (h * xa + t)) $
             (0,
              f' (h * xa + t, x (h * xa + t)) $
              (1,
               f (h * xa + t,
                  x (h * xa + t)))))) `
     cbox 0 1) \<and>
   b \<in> closure (convex hull (*\<^sub>R) (1 / 2) `
       (\<lambda>s. (h ^ 3 * p / 2) *\<^sub>R
             f''
              (t + s * (h * p),
               x t +
               (s * (h * p)) *\<^sub>R f (t, x t)) $
             (1, f (t, x t)) $
             (1, f (t, x t))) `
       cbox 0 1)}"
    using in_minus_Collect[OF 1 2]
    unfolding closure_scaleR convex_hull_scaling
    by auto
  also note closure_minus_Collect
  also note convex_hull_minus_Collect
  also
  define F' where "F' \<equiv> (\<lambda>y. y - discrete_evolution (rk2_increment p (\<lambda>t x. f (t, x))) (t + h) t (x t)) ` R"
  have "closure
    (convex hull
     {xa - y |xa y.
      xa \<in> (*\<^sub>R) (1 / 3) `
            (\<lambda>xa. (h ^ 3 / 2) *\<^sub>R
                   (f'' (h * xa + t, x (h * xa + t)) $
                    (1, f (h * xa + t, x (h * xa + t))) $
                    (1, f (h * xa + t, x (h * xa + t))) +
                    f' (h * xa + t, x (h * xa + t)) $
                    (0, f' (h * xa + t, x (h * xa + t)) $
                        (1, f (h * xa + t, x (h * xa + t)))))) `
            cbox 0 1 \<and>
      y \<in> (*\<^sub>R) (1 / 2) `
           (\<lambda>s. (h ^ 3 * p / 2) *\<^sub>R
                 f'' (t + s * (h * p), x t + (s * (h * p)) *\<^sub>R f (t, x t)) $
                 (1, f (t, x t)) $
                 (1, f (t, x t))) `
           cbox 0 1}) \<subseteq> F'"
    apply (rule closure_minimal)
    apply (rule hull_minimal)
    apply (safe)
    subgoal for _ _ _ _ _ s1 s2
      using R[of s1 s2]
      by (force simp: F'_def heun_remainder1_def heun_remainder2_def algebra_simps)
    by (auto intro!: ccR simp: F'_def)
  finally
  show "x (t + h) \<in> R"
    by (auto simp: F'_def)
qed

end

locale derivative_norm_bounded = derivative_on_prod T X f f' for T and X::"'a::euclidean_space set" and f f' +
  fixes B B'
  assumes nonempty: "T \<noteq> {}" "X \<noteq> {}"
  assumes X_bounded: "bounded X"
  assumes convex: "convex T" "convex X"
  assumes f_bounded: "\<And>t x. t\<in>T \<Longrightarrow> x\<in>X \<Longrightarrow> norm (f t x) \<le> B"
  assumes f'_bounded: "\<And>t x. t\<in>T \<Longrightarrow> x\<in>X \<Longrightarrow> onorm (f' (t,x)) \<le> B'"
begin

lemma f_bound_nonneg: "0 \<le> B"
proof -
  from nonempty obtain t x where "t \<in> T" "x \<in> X" by auto
  have "0 \<le> norm (f t x)" by simp
  also have "\<dots> \<le> B" by (rule f_bounded) fact+
  finally show ?thesis .
qed

lemma f'_bound_nonneg: "0 \<le> B'"
proof -
  from nonempty f_bounded ex_norm_eq_1[where 'a="real*'a"]
    obtain t x and d::"real*'a" where tx: "t \<in> T" "x \<in> X" "norm d = 1" by auto
  have "0 \<le> norm (f' (t, x) d)" by simp
  also have "... \<le> B'"
    using tx
    by (intro order_trans[OF onorm[OF has_derivative_bounded_linear[OF f']]])
      (auto intro!: f'_bounded f' has_derivative_linear)
  finally show ?thesis .
qed

sublocale g?: global_lipschitz _ _ _ B'
proof
  fix t assume "t \<in> T"
  show "B'-lipschitz_on X (f t)"
  proof (rule lipschitz_onI)
    show "0 \<le> B'" using f'_bound_nonneg .
    fix x y
    let ?I = "T \<times> X"
    have "convex ?I" by (intro convex convex_Times)
    moreover have "\<And>x. x \<in> ?I \<Longrightarrow> ((\<lambda>(t, x). f t x) has_derivative f' x) (at x within ?I)" 
                  "\<And>x. x \<in> ?I \<Longrightarrow> onorm (f' x) \<le> B'"
      using f' f'_bounded  by (auto simp add: intro!: f'_bounded has_derivative_linear)
    moreover assume "x \<in> X" "y \<in> X"
    with \<open>t \<in> T\<close> have "(t, x) \<in> ?I" "(t, y) \<in> ?I" by simp_all
    ultimately have "norm ((\<lambda>(t, x). f t x) (t, x) - (\<lambda>(t, x). f t x) (t, y)) \<le> B' * norm ((t, x) - (t, y))"
      by (rule differentiable_bound)
    then show "dist (f t x) (f t y) \<le> B' * dist x y"
      by (simp add: dist_norm norm_Pair)
  qed
qed

definition euler_C::"'a itself \<Rightarrow> real" where "euler_C (TYPE('a)) = (sqrt DIM('a) * (B' * (B + 1) / 2))"

lemma euler_C_nonneg: "euler_C TYPE('a) \<ge> 0"
 using f_bounded f_bound_nonneg f'_bound_nonneg
 by (simp add: euler_C_def)

lemma euler_consistent_traj:
  fixes t
  assumes T: "{t..u} \<subseteq> T"
  assumes x': "(x has_vderiv_on (\<lambda>s. f s (x s))) {t..u}"
  assumes x: "\<And>s. s \<in> {t..u} \<Longrightarrow> x s \<in> X"
  shows "consistent x t u (euler_C (TYPE('a))) 1 (euler_increment f)"
proof
  from x' have x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f s (x s)) (at s within {t..u})"
    by (simp add: has_vderiv_on_def)
  fix h::real
  assume ht: "0 < h" "t + h \<le> u" hence "t < u" "0 < h\<^sup>2 / 2" by simp_all
  let ?d = "discrete_evolution (euler_increment f) (t + h) t (x t)"
  have "x (t + h) \<in> (\<lambda>b. ?d + (h\<^sup>2 / 2) *\<^sub>R b) ` cbox (- (B' * (B + 1)) *\<^sub>R One) ((B' * (B + 1)) *\<^sub>R One)"
  proof (rule euler_consistent_traj_set[OF _ \<open>t + h \<le> u\<close> T x' x])
    fix s
    assume "s \<in> {t .. u}"
    then have "?d + (h\<^sup>2 / 2) *\<^sub>R (f' (s, x s)) (1, f s (x s)) \<in>
      (\<lambda>b. ?d + (h\<^sup>2 / 2) *\<^sub>R b) ` ((\<lambda>s. (f' (s, x s)) (1, f s (x s)))` {t .. u})"
      by auto
    also have "\<dots> \<subseteq> (\<lambda>b. ?d + (h\<^sup>2 / 2) *\<^sub>R b) ` cbox (- (B' * (B + 1)) *\<^sub>R One) ((B' * (B + 1)) *\<^sub>R One)"
    proof (rule image_mono, safe)
      fix s assume "s \<in> {t .. u}"
      with T have "norm (f' (s, x s) (1, f s (x s))) \<le> onorm (f' (s, x s)) * norm (1::real, f s (x s))"
        by (force intro!: onorm has_derivative_bounded_linear f' x)
      also have "\<dots> \<le> B' * (B + 1)"
        using T \<open>s \<in> _\<close>
        by (force intro!: mult_mono f'_bounded f_bounded f'_bound_nonneg x order_trans[OF norm_Pair_le])
      finally have "f' (s, x s) (1, f s (x s)) \<in> cball 0 (B' * (B + 1))"
        by (auto simp: dist_norm mem_cball)
      also note cball_in_cbox
      finally show "f' (s, x s) (1, f s (x s)) \<in> cbox (- (B' * (B + 1)) *\<^sub>R One) ((B' * (B + 1)) *\<^sub>R One)"
        by simp
    qed
    finally
    show "?d + (h\<^sup>2 / 2) *\<^sub>R (f' (s, x s)) (1, f s (x s))
         \<in> (\<lambda>b. ?d + (h\<^sup>2 / 2) *\<^sub>R b) ` cbox (- (B' * (B + 1)) *\<^sub>R One) ((B' * (B + 1)) *\<^sub>R One)" .
  qed (auto intro!: less_imp_le[OF \<open>0 < h\<close>] bounded_plus_image bounded_scaleR_image bounded_cbox
    closed_scaling convex_scaling convex_box simp: image_constant_conv closed_translation_iff)
  then have "x (t + h) - discrete_evolution (euler_increment f) (t + h) t (x t) \<in>
      (*\<^sub>R) (h\<^sup>2 / 2) ` cbox (- (B' * (B + 1)) *\<^sub>R One) ((B' * (B + 1)) *\<^sub>R One)"
    by auto
  also have "\<dots> = cbox (- ((h\<^sup>2 / 2) * (B' * (B + 1))) *\<^sub>R One) (((h\<^sup>2 / 2) * (B' * (B + 1))) *\<^sub>R One)"
    using f_bound_nonneg f'_bound_nonneg
    by (auto simp add: image_smult_cbox box_eq_empty mult_less_0_iff)
  also
  note centered_cbox_in_cball
  finally show "dist (x (t + h)) (discrete_evolution (euler_increment f) (t + h) t (x t))
      \<le> euler_C(TYPE('a)) * h ^ (1 + 1)"
    by (auto simp: euler_C_def dist_norm algebra_simps norm_minus_commute power2_eq_square mem_cball)
qed

lemma derivative_norm_bounded_subset:
  assumes X'_ne: "X' \<noteq> {}" and X'_subset: "X' \<subseteq> X" and  "convex X'"
  shows "derivative_norm_bounded T X' f f' B B'"
proof -
  interpret derivative_on_prod T X' f f'
    using X'_subset
    by (rule derivative_on_prod_subset)
  show ?thesis
    using X'_subset
    by unfold_locales
      (auto intro!: nonempty X'_ne bounded_subset[OF X_bounded X'_subset] convex f_bounded f'_bounded
        \<open>convex X'\<close>)
qed

end

locale grid_from = grid +
  fixes t0
  assumes grid_min: "t0 = t 0"

locale euler_consistent =
  derivative_norm_bounded T X' f f' B B'
  for T f X X' B f' B' +
  fixes solution t0 x0 r e
  assumes sol: "(solution solves_ode f) T X" and sol_iv: "solution t0 = x0" and iv_defined: "t0 \<in> T"
  assumes domain_subset: "X \<subseteq> X'"
  assumes interval: "T = {t0 - e .. t0 + e}"
  assumes lipschitz_area: "\<And>t. t \<in> T \<Longrightarrow> cball (solution t) \<bar>r\<bar> \<subseteq> X'"
begin

lemma euler_consistent_solution:
  fixes t'
  assumes t': "t' \<in> {t0 .. t0 + e}"
  shows "consistent solution t' (t0 + e) (euler_C(TYPE('a))) 1 (euler_increment f)"
proof (rule euler_consistent_traj)
  show "{t'..t0 + e} \<subseteq> T" using t' interval by simp
  with solves_odeD(1)[OF sol] show "(solution has_vderiv_on (\<lambda>s. f s (solution s))) {t'..t0 + e}"
    by (rule has_vderiv_on_subset)
  fix s
  assume "s \<in> {t'..t0 + e}" with solves_odeD(2)[OF sol, of s]
  show "solution s \<in> X'" using domain_subset \<open>{t' .. t0 + e} \<subseteq> T\<close>
    by (auto simp: subset_iff)
qed

end

subsection \<open>Euler method is convergent\<close>
text\<open>\label{sec:rk-euler-conv}\<close>

locale max_step1 = grid +
  fixes t1 L B r
  assumes max_step: "\<And>j. t j \<le> t1 \<Longrightarrow> max_stepsize j \<le> \<bar>r\<bar> * L / B / (exp (L * (t1 - t 0) + 1) - 1)"

sublocale max_step1 < max_step?: max_step t t1 1 L B r
using max_step by unfold_locales simp_all

locale euler_convergent =
  euler_consistent T f "X::'a::euclidean_space set" + max_step1 t "t0 + e" B' "euler_C(TYPE('a))" r for T f X t +
  assumes grid_from: "t0 = t 0"

subsection \<open>Euler method on Rectangle is convergent\<close>
text\<open>\label{sec:rk-euler-conv-on-rect}\<close>

locale ivp_rectangle_bounded_derivative =
  solution_in_cylinder t0 T x0 b f X B +
  outer?: derivative_norm_bounded T "cball x0 r" f f' B B' for t0 T x0 b f X B f' B' r e +
  assumes T_def: "T \<equiv> cball t0 e"
  assumes subset_cylinders: "b < r"
  assumes positive_time: "0 < e"

sublocale ivp_rectangle_bounded_derivative \<subseteq> unique_on_cylinder t0 T x0 b X f B B'
  by unfold_locales (insert subset_cylinders positive_time,
      auto intro!: lipschitz_on_subset[OF lipschitz] simp: mem_cball)

sublocale ivp_rectangle_bounded_derivative \<subseteq> euler_consistent T f X "cball x0 r" B f' B' solution t0 x0 "r - b" e
proof -
  interpret derivative_norm_bounded T X f f' B B'
    using b_pos subset_cylinders
    by (intro outer.derivative_norm_bounded_subset) (auto simp: X_def mem_cball)
  show "euler_consistent T f X (cball x0 r) B f' B' solution t0 x0 (r - b) e"
    apply unfold_locales
    subgoal by (rule solution_solves_ode)
    subgoal by (rule solution_iv)
    subgoal by (rule initial_time_in)
    subgoal using subset_cylinders by (auto simp: X_def mem_cball)
    subgoal by (auto simp add: T_def dist_real_def mem_cball)
    subgoal premises prems for t
    proof safe
      fix x
      have "dist x x0 \<le> dist x (solution t) + dist x0 (solution t)"
        by (rule dist_triangle2)
      also
      assume "x \<in> cball (solution t) \<bar>r - b\<bar>"
      then have "dist x (solution t) \<le> r - b"
        using subset_cylinders
        by (simp add: dist_commute mem_cball)
      also
      have "{t0--t} \<subseteq> T" by (rule subset_T[OF prems])
      then have "dist x0 (solution t) \<le> B * \<bar>t - t0\<bar>"
        using subset_cylinders is_solution_in_cone[of t, OF prems solves_ode_on_subset[OF solution_solves_ode _ order_refl] solution_iv]
        by (simp add: mem_cball)
      also have "B * abs (t - t0) \<le> b"
        using e_bounded[OF prems] b_pos B_nonneg
        by (auto simp: dist_real_def divide_simps ac_simps split: if_splits)
      finally
      show "x \<in> cball x0 r" by (simp add: dist_commute mem_cball)
    qed
    done
qed

locale euler_on_rectangle =
  ivp_rectangle_bounded_derivative t0 T x0 b f X B f' B' r e +
  grid_from t t0 +
  max_step1 t "t0 + e" B' "outer.euler_C(TYPE('a::euclidean_space))" "r - b"
  for t0 T x0 f X t e b r B f' B'

sublocale euler_consistent \<subseteq>
  consistent_one_step t0 "t0 + e" solution "euler_increment f" 1 "euler_C(TYPE('a))" r B'
proof
  show "0 < (1::nat)" by simp
  show "0 \<le> euler_C(TYPE('a))" using euler_C_nonneg by simp
  show "0 \<le> B'" using lipschitz_on_nonneg[OF lipschitz] iv_defined by simp
  fix s x assume s: "s \<in> {t0 .. t0 + e}"
  show "consistent solution s (t0 + e) (euler_C(TYPE('a))) 1 (euler_increment f)"
    using interval s f_bounded f'_bounded f'
      strip
    by (intro euler_consistent_solution) auto
  fix h
  assume "h \<in> {0 .. t0 + e - s}"
  have "B'-lipschitz_on X' (euler_increment f h s)"
    using s lipschitz interval strip
    by (auto intro!: euler_lipschitz)
  thus "B'-lipschitz_on (cball (solution s) \<bar>r\<bar>) (euler_increment f h s)"
    using s interval
    by (auto intro: lipschitz_on_subset[OF _ lipschitz_area])
qed

sublocale euler_convergent \<subseteq>
  convergent_one_step t0 "t0 + e" solution "euler_increment f" 1 "euler_C(TYPE('a))" r B' t
  by unfold_locales (simp add: grid_from)

sublocale euler_on_rectangle \<subseteq> convergent?: euler_convergent "cball x0 r" B f' B' solution t0 x0 "r - b" e T f X t
proof unfold_locales
qed (rule grid_min)

lemma "B \<ge> (0::real) \<Longrightarrow> 0 \<le> (exp (B + 1) - 1)" by (simp add: algebra_simps)

context euler_on_rectangle begin

lemma convergence:
  assumes "t j \<le> t0 + e"
  shows "dist (solution (t j)) (euler f x0 t j)
    \<le> sqrt DIM('a) * (B + 1) / 2 * (exp (B' * e + 1) - 1) * max_stepsize j"
proof -
  have "dist (solution (t j)) (euler f x0 t j)
    \<le> sqrt DIM('a) * (B + 1) / 2 * B' / B' * ((exp (B' * e + 1) - 1) * max_stepsize j)"
    using assms convergence[OF assms] f'_bound_nonneg
    unfolding euler_C_def
    by (simp add: euler_def grid_min[symmetric] ac_simps)
  also have "\<dots> \<le> sqrt DIM('a) * (B + 1) / 2 * ((exp (B' * e + 1) - 1) * max_stepsize j)"
    using f_bound_nonneg f'_bound_nonneg
    by (auto intro!: mult_right_mono mult_nonneg_nonneg max_stepsize_nonneg add_nonneg_nonneg
      simp: le_diff_eq)
  finally show ?thesis by simp
qed

end

subsection \<open>Stability and Convergence of Approximate Euler \label{sec:rk-euler-stable}\<close>

locale euler_rounded_on_rectangle =
  ivp_rectangle_bounded_derivative t0 T x0 b f X B f' B' r e1' +
  grid?: grid_from t t0' +
  max_step_r_2?: max_step1 t "t0 + e2'" B' "euler_C(TYPE('a))" "(r - b)/2"
  for t0 T x0 f and X::"'a::executable_euclidean_space set" and t :: "nat \<Rightarrow> real" and t0' e1' e2'::real and x0' :: "'a"
  and b r B f' B' +
  fixes g::"real \<Rightarrow> 'a \<Rightarrow> 'a" and e::int
  assumes t0_float: "t0 = t0'"
  assumes ordered_bounds: "e1' \<le> e2'"
  assumes approx_f_e: "\<And>j x. t j \<le> t0 + e1' \<Longrightarrow> dist (f (t j) x) ((g (t j) x)) \<le> sqrt (DIM('a)) * 2 powr -e"
  assumes initial_error: "dist x0 (x0') \<le> euler_C(TYPE('a)) / B' * (exp 1 - 1) * stepsize 0"
  assumes rounding_error: "\<And>j. t j \<le> t0 + e1' \<Longrightarrow> sqrt (DIM('a)) * 2 powr -e \<le> euler_C(TYPE('a)) / 2 * stepsize j"
begin

lemma approx_f: "t j \<le> t0 +  e1' \<Longrightarrow> dist (f (t j) (x)) ((g (t j) (x)))
    \<le> euler_C(TYPE('a)) / 2 * stepsize j"
  using approx_f_e[of j x] rounding_error[of j] by auto

lemma t0_le: "t 0 \<le> t0 + e1'"
  unfolding grid_min[symmetric] t0_float[symmetric]
  by (metis atLeastAtMost_iff interval iv_defined(1))

end

sublocale euler_rounded_on_rectangle \<subseteq> grid'?: grid_from t t0'
  using grid t0_float grid_min by unfold_locales auto

sublocale euler_rounded_on_rectangle \<subseteq> max_step_r?: max_step1 t "t0 + e2'" B' "euler_C(TYPE('a))" "r - b"
proof unfold_locales
  fix j
  assume *: "(t j) \<le> t0 + e2'"
  moreover from * grid_mono[of 0 j] have "t 0 \<le> t0 + e2'" by (simp add: less_eq_float_def)
  ultimately show "max_stepsize j
        \<le> \<bar>r - b\<bar> * B' / euler_C(TYPE('a)) / (exp (B' * (t0 + e2' - (t 0)) + 1) - 1)"
    using max_step_mono_r lipschitz B_nonneg f'_bound_nonneg
    by (auto simp: less_eq_float_def euler_C_def)
qed

lemma max_step1_mono:
  assumes "t 0 \<le> t1"
  assumes "t1 \<le> t2"
  assumes "0 \<le> a"
  assumes "0 \<le> b"
  assumes ms2: "max_step1 t t2 a b c"
  shows "max_step1 t t1 a b c"
proof -
  interpret t2: max_step1 t t2 a b c using ms2 .
  show ?thesis
  proof
    fix j
    assume "t j \<le> t1" hence "t j \<le> t2" using assms by simp
    hence "t2.max_stepsize j \<le> \<bar>c\<bar> * a / b / (exp (a * (t2 - t 0) + 1) - 1)" (is "_ \<le> ?x t2")
      by (rule t2.max_step)
    also have "\<dots> \<le> ?x t1"
      using assms
      by (cases "b = 0") (auto intro!: divide_left_mono mult_mono abs_ge_zero add_increasing
        mult_pos_pos add_strict_increasing2 simp: le_diff_eq less_diff_eq)
    finally show "t2.max_stepsize j \<le> ?x t1" .
  qed
qed

sublocale euler_rounded_on_rectangle \<subseteq> max_step_r1?: max_step1 t "t0 + e1'" B' "euler_C(TYPE('a))" "r - b"
  by (rule max_step1_mono[of t, OF t0_le add_left_mono[OF ordered_bounds] f'_bound_nonneg euler_C_nonneg])
    unfold_locales

sublocale euler_rounded_on_rectangle \<subseteq> c?: euler_on_rectangle t0 T x0 f X t e1' b r B f' B'
  using t0_float grid_min by unfold_locales simp

sublocale euler_rounded_on_rectangle \<subseteq>
  consistent_one_step "t 0" "t0 + e1'" solution "euler_increment f" 1 "euler_C(TYPE('a))" "r - b" B'
  using consistent_nonneg consistent lipschitz_nonneg lipschitz_incr t0_float grid_min
  by unfold_locales simp_all

sublocale euler_rounded_on_rectangle \<subseteq> max_step1 t "t0 + e1'" B' "euler_C(TYPE('a))" "(r - b) / 2"
  by (rule max_step1_mono[of t, OF t0_le add_left_mono[OF ordered_bounds] f'_bound_nonneg euler_C_nonneg])
    unfold_locales

sublocale euler_rounded_on_rectangle \<subseteq>
  one_step?:
  rounded_one_step t "t0 + e1'" solution "euler_increment f" 1 "euler_C(TYPE('a))" "r - b" B' "euler_increment' e g" x0'
proof
  fix h j x assume "t j \<le> t0 + e1'"
  have "dist (euler_increment f (h) (t j) (x))
        ((euler_increment' e g h (t j) x)) =
    dist (f (t j) (x)) ((eucl_down e (g (t j) (x))))"
    by (simp add: euler_increment euler_float_increment)
  also
  have "... \<le>
    dist (f (t j) (x)) ((g (t j) (x))) +
    dist ((g (t j) (x))) ((eucl_down e (g (t j) (x))))"
    by (rule dist_triangle)
  also
  from approx_f[OF \<open>t j \<le> t0 + e1'\<close>]
  have "dist (f (t j) (x)) ((g (t j) (x))) \<le>
    euler_C(TYPE('a)) / 2 * stepsize j" .
  also
  from eucl_truncate_down_correct[of "g (t j) (x)" e]
  have "dist ((g (t j) (x))) ((eucl_down e (g (t j) (x)))) \<le> sqrt (DIM('a)) * 2 powr - e" by simp
  also
  have "sqrt (DIM('a)) * 2 powr -e \<le> euler_C(TYPE('a)) / 2 * stepsize j"
    using rounding_error \<open>t j \<le> t0 + e1'\<close> .
  finally
  have "dist (euler_increment f (h) (t j) (x)) ((euler_increment' e g h (t j) x)) \<le> euler_C(TYPE('a)) * stepsize j"
    by arith
  thus "dist (euler_increment f h (t j) (x)) ((euler_increment' e g h (t j) x)) \<le> euler_C(TYPE('a)) * stepsize j ^ 1"
    by simp
qed (insert initial_error, simp add: grid_min[symmetric])

context euler_rounded_on_rectangle begin

lemma stability:
  assumes "t j \<le> t0 + e1'"
  shows "dist (euler' e g x0' t j) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * e1' + 1) - 1) * max_stepsize j"
proof -
  have "dist ((euler' e g x0' t j)) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * B' / B' * (exp (B' * e1' + 1) - 1) * max_stepsize j"
    using assms stability[OF assms]
    unfolding grid_min[symmetric] euler_C_def sol_iv
    by (auto simp add: euler_def euler'_def)
  also have "\<dots> \<le> sqrt DIM('a) * (B + 1) / 2 * ((exp (B' * e1' + 1) - 1) * max_stepsize j)"
    using f_bound_nonneg f'_bound_nonneg
    by (auto intro!: mult_right_mono mult_nonneg_nonneg max_stepsize_nonneg add_nonneg_nonneg
      simp: le_diff_eq)
  finally show ?thesis by simp
qed

lemma convergence_float:
  assumes "t j \<le> t0 + e1'"
  shows "dist (solution (t j)) (euler' e g x0' t j) \<le>
    sqrt DIM('a) * (B + 1) * (exp (B' * e1' + 1) - 1) * max_stepsize j"
proof -
  have "dist (solution ((t j))) ((euler' e g x0' t j)) \<le>
    dist (solution ((t j)))
    (euler f x0 t j) +
    dist ((euler' e g x0' t j)) (euler f x0 t j)"
    by (rule dist_triangle2)
  also have "dist (solution ((t j)))
     (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * e1' + 1) - 1) * max_stepsize j"
    using assms convergence[OF assms] t0_float by simp
  also have "dist ((euler' e g x0' t j)) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * e1' + 1) - 1) * max_stepsize j"
    using assms stability by simp
  finally
  have "dist (solution ((t j))) ((euler' e g x0' t j))
     \<le> sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (e1') + 1) - 1) * max_stepsize j +
       sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (e1') + 1) - 1) * max_stepsize j" 
    by simp
  thus ?thesis by (simp add: field_simps)
qed

end

end
