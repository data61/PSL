(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Gromov hyperbolic spaces\<close>

theory Gromov_Hyperbolicity
  imports Isometries Metric_Completion
begin

subsection \<open>Definition, basic properties\<close>

text \<open>Although we will mainly work with type classes later on, we introduce the definition
of hyperbolicity on subsets of a metric space.

A set is $\delta$-hyperbolic if it satisfies the following inequality. It is very obscure at first sight,
but we will see several equivalent characterizations later on. For instance, a space is hyperbolic
(maybe for a different constant $\delta$) if all geodesic triangles are thin, i.e., every side is
close to the union of the two other sides. This definition captures the main features of negative
curvature at a large scale, and has proved extremely fruitful and influential.

Two important references on this topic are~\cite{ghys_hyperbolique} and~\cite{bridson_haefliger}.
We will sometimes follow them, sometimes depart from them.\<close>

definition Gromov_hyperbolic_subset::"real \<Rightarrow> ('a::metric_space) set \<Rightarrow> bool"
  where "Gromov_hyperbolic_subset delta A = (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. \<forall>t\<in>A. dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta)"

lemma Gromov_hyperbolic_subsetI [intro]:
  assumes "\<And>x y z t. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow> dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
  shows "Gromov_hyperbolic_subset delta A"
using assms unfolding Gromov_hyperbolic_subset_def by auto

text \<open>When the four points are not all distinct, the above inequality is always satisfied for
$\delta = 0$.\<close>

lemma Gromov_hyperbolic_ineq_not_distinct:
  assumes "x = y \<or> x = z \<or> x = t \<or> y = z \<or> y = t \<or> z = (t::'a::metric_space)"
  shows "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z)"
using assms by (auto simp add: dist_commute, simp add: dist_triangle add.commute, simp add: dist_triangle3)

text \<open>It readily follows from the definition that hyperbolicity passes to the closure of the set.\<close>

lemma Gromov_hyperbolic_closure:
  assumes "Gromov_hyperbolic_subset delta A"
  shows "Gromov_hyperbolic_subset delta (closure A)"
unfolding Gromov_hyperbolic_subset_def proof (auto)
  fix x y z t assume H: "x \<in> closure A" "y \<in> closure A" "z \<in> closure A" "t \<in> closure A"
  obtain X::"nat \<Rightarrow> 'a" where X: "\<And>n. X n \<in> A" "X \<longlonglongrightarrow> x"
    using H closure_sequential by blast
  obtain Y::"nat \<Rightarrow> 'a" where Y: "\<And>n. Y n \<in> A" "Y \<longlonglongrightarrow> y"
    using H closure_sequential by blast
  obtain Z::"nat \<Rightarrow> 'a" where Z: "\<And>n. Z n \<in> A" "Z \<longlonglongrightarrow> z"
    using H closure_sequential by blast
  obtain T::"nat \<Rightarrow> 'a" where T: "\<And>n. T n \<in> A" "T \<longlonglongrightarrow> t"
    using H closure_sequential by blast
  have *: "max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n) \<ge> 0" for n
    using assms X(1)[of n] Y(1)[of n] Z(1)[of n] T(1)[of n] unfolding Gromov_hyperbolic_subset_def
    by (auto simp add: algebra_simps)
  have **: "(\<lambda>n. max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n))
    \<longlonglongrightarrow> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t"
    apply (auto intro!: tendsto_intros) using X Y Z T by auto
  have "max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t \<ge> 0"
    apply (rule LIMSEQ_le_const[OF **]) using * by auto
  then show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
    by auto
qed

text \<open>A good formulation of hyperbolicity is in terms of Gromov products. Intuitively, the
Gromov product of $x$ and $y$ based at $e$ is the distance between $e$ and the geodesic between
$x$ and $y$. It is also the time after which the geodesics from $e$ to $x$ and from $e$ to $y$
stop travelling together.\<close>

definition Gromov_product_at::"('a::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where "Gromov_product_at e x y = (dist e x + dist e y - dist x y) / 2"

lemma Gromov_hyperbolic_subsetI2:
  fixes delta::real
  assumes "\<And>e x y z. e \<in> A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> Gromov_product_at (e::'a::metric_space) x z \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z) - delta"
  shows "Gromov_hyperbolic_subset delta A"
proof (rule Gromov_hyperbolic_subsetI)
  fix x y z t assume H: "x \<in> A" "z \<in> A" "y \<in> A" "t \<in> A"
  show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
    using assms[OF H] unfolding Gromov_product_at_def min_def max_def
    by (auto simp add: divide_simps algebra_simps dist_commute)
qed

lemma Gromov_product_nonneg [simp, mono_intros]:
  "Gromov_product_at e x y \<ge> 0"
unfolding Gromov_product_at_def by (simp add: dist_triangle3)

lemma Gromov_product_commute:
  "Gromov_product_at e x y = Gromov_product_at e y x"
unfolding Gromov_product_at_def by (auto simp add: dist_commute)

lemma Gromov_product_le_dist [simp, mono_intros]:
  "Gromov_product_at e x y \<le> dist e x"
  "Gromov_product_at e x y \<le> dist e y"
unfolding Gromov_product_at_def by (auto simp add: diff_le_eq dist_triangle dist_triangle2)

lemma Gromov_product_le_infdist [mono_intros]:
  assumes "geodesic_segment_between G x y"
  shows "Gromov_product_at e x y \<le> infdist e G"
proof -
  have [simp]: "G \<noteq> {}" using assms by auto
  have "Gromov_product_at e x y \<le> dist e z" if "z \<in> G" for z
  proof -
    have "dist e x + dist e y \<le> (dist e z + dist z x) + (dist e z + dist z y)"
      by (intro add_mono dist_triangle)
    also have "... = 2 * dist e z + dist x y"
      apply (auto simp add: dist_commute) using \<open>z \<in> G\<close> assms by (metis dist_commute geodesic_segment_dist)
    finally show ?thesis unfolding Gromov_product_at_def by auto
  qed
  then show ?thesis
    apply (subst infdist_notempty) by (auto intro: cINF_greatest)
qed

lemma Gromov_product_add:
  "Gromov_product_at e x y + Gromov_product_at x e y = dist e x"
unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps dist_commute)

lemma Gromov_product_geodesic_segment:
  assumes "geodesic_segment_between G x y" "t \<in> {0..dist x y}"
  shows "Gromov_product_at x y (geodesic_segment_param G x t) = t"
proof -
  have "dist x (geodesic_segment_param G x t) = t"
    using assms(1) assms(2) geodesic_segment_param(6) by auto
  moreover have "dist y (geodesic_segment_param G x t) = dist x y - t"
    by (metis \<open>dist x (geodesic_segment_param G x t) = t\<close> add_diff_cancel_left' assms(1) assms(2) dist_commute geodesic_segment_dist geodesic_segment_param(3))
  ultimately show ?thesis unfolding Gromov_product_at_def by auto
qed

lemma Gromov_product_e_x_x [simp]:
  "Gromov_product_at e x x = dist e x"
unfolding Gromov_product_at_def by auto

lemma Gromov_product_at_diff:
  "\<bar>Gromov_product_at x y z - Gromov_product_at a b c\<bar> \<le> dist x a + dist y b + dist z c"
unfolding Gromov_product_at_def abs_le_iff apply (auto simp add: divide_simps)
by (smt dist_commute dist_triangle4)+

lemma Gromov_product_at_diff1:
  "\<bar>Gromov_product_at a x y - Gromov_product_at b x y\<bar> \<le> dist a b"
using Gromov_product_at_diff[of a x y b x y] by auto

lemma Gromov_product_at_diff2:
  "\<bar>Gromov_product_at e x z - Gromov_product_at e y z\<bar> \<le> dist x y"
using Gromov_product_at_diff[of e x z e y z] by auto

lemma Gromov_product_at_diff3:
  "\<bar>Gromov_product_at e x y - Gromov_product_at e x z\<bar> \<le> dist y z"
using Gromov_product_at_diff[of e x y e x z] by auto

text \<open>The Gromov product is continuous in its three variables. We formulate it in terms of sequences,
as it is the way it will be used below (and moreover continuity for functions of several variables
is very poor in the library).\<close>

lemma Gromov_product_at_continuous:
  assumes "(u \<longlongrightarrow> x) F" "(v \<longlongrightarrow> y) F" "(w \<longlongrightarrow> z) F"
  shows "((\<lambda>n. Gromov_product_at (u n) (v n) (w n)) \<longlongrightarrow> Gromov_product_at x y z) F"
proof -
  have "((\<lambda>n. abs(Gromov_product_at (u n) (v n) (w n) - Gromov_product_at x y z)) \<longlongrightarrow> 0 + 0 + 0) F"
    apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. dist (u n) x + dist (v n) y + dist (w n) z", OF always_eventually always_eventually])
    apply (simp, simp add: Gromov_product_at_diff, simp, intro tendsto_intros)
    using assms tendsto_dist_iff by auto
  then show ?thesis
    apply (subst tendsto_dist_iff) unfolding dist_real_def by auto
qed


subsection \<open>Typeclass for Gromov hyperbolic spaces\<close>

text \<open>We could (should?) just derive \verb+Gromov_hyperbolic_space+ from \verb+metric_space+.
However, in this case, properties of metric spaces are not available when working in the locale!
It is more efficient to ensure that we have a metric space by putting a type class restriction
in the definition. The $\delta$ in Gromov-hyperbolicity type class is called \verb+deltaG+ to
avoid name clashes.
\<close>

class metric_space_with_deltaG = metric_space +
  fixes deltaG::"('a::metric_space) itself \<Rightarrow> real"

class Gromov_hyperbolic_space = metric_space_with_deltaG +
  assumes hyperb_quad_ineq0: "Gromov_hyperbolic_subset (deltaG(TYPE('a::metric_space))) (UNIV::'a set)"

class Gromov_hyperbolic_space_geodesic = Gromov_hyperbolic_space + geodesic_space

lemma (in Gromov_hyperbolic_space) hyperb_quad_ineq [mono_intros]:
  shows "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG(TYPE('a))"
using hyperb_quad_ineq0 unfolding Gromov_hyperbolic_subset_def by auto

text \<open>It readily follows from the definition that the completion of a $\delta$-hyperbolic
space is still $\delta$-hyperbolic.\<close>

instantiation metric_completion :: (Gromov_hyperbolic_space) Gromov_hyperbolic_space
begin
definition deltaG_metric_completion::"('a metric_completion) itself \<Rightarrow> real" where
  "deltaG_metric_completion _ = deltaG(TYPE('a))"

instance proof (standard, rule Gromov_hyperbolic_subsetI)
  have "Gromov_hyperbolic_subset (deltaG(TYPE('a))) (range (to_metric_completion::'a \<Rightarrow> _))"
    unfolding Gromov_hyperbolic_subset_def
    apply (auto simp add: isometry_onD[OF to_metric_completion_isometry])
    by (metis hyperb_quad_ineq)
  then have "Gromov_hyperbolic_subset (deltaG TYPE('a metric_completion)) (UNIV::'a metric_completion set)"
    unfolding deltaG_metric_completion_def to_metric_completion_dense'[symmetric]
    using Gromov_hyperbolic_closure by auto
  then show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG TYPE('a metric_completion)"
      for x y z t::"'a metric_completion"
    unfolding Gromov_hyperbolic_subset_def by auto
qed
end (*of instantiation metric_completion (of Gromov_hyperbolic_space) is Gromov_hyperbolic*)


context Gromov_hyperbolic_space
begin

lemma delta_nonneg [simp, mono_intros]:
  "deltaG(TYPE('a)) \<ge> 0"
proof -
  obtain x::'a where True by auto
  show ?thesis using hyperb_quad_ineq[of x x x x] by auto
qed

lemma hyperb_ineq [mono_intros]:
  "Gromov_product_at (e::'a) x z \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z) - deltaG(TYPE('a))"
using hyperb_quad_ineq[of e y x z] unfolding Gromov_product_at_def min_def max_def
by (auto simp add: divide_simps algebra_simps metric_space_class.dist_commute)

lemma hyperb_ineq' [mono_intros]:
  "Gromov_product_at (e::'a) x z + deltaG(TYPE('a)) \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z)"
using hyperb_ineq[of e x y z] by auto

lemma hyperb_ineq_4_points [mono_intros]:
  "Min {Gromov_product_at (e::'a) x y, Gromov_product_at e y z, Gromov_product_at e z t} - 2 * deltaG(TYPE('a)) \<le> Gromov_product_at e x t"
using hyperb_ineq[of e x y z] hyperb_ineq[of e x z t] apply auto using delta_nonneg by linarith

lemma hyperb_ineq_4_points' [mono_intros]:
  "Min {Gromov_product_at (e::'a) x y, Gromov_product_at e y z, Gromov_product_at e z t} \<le> Gromov_product_at e x t + 2 * deltaG(TYPE('a))"
using hyperb_ineq_4_points[of e x y z t] by auto

text \<open>In Gromov-hyperbolic spaces, geodesic triangles are thin, i.e., a point on one side of a
geodesic triangle is close to the union of the two other sides (where the constant in "close"
is $4\delta$, independent of the size of the triangle). We prove this basic property
(which, in fact, is a characterization of Gromov-hyperbolic spaces: a geodesic space in which
triangles are thin is hyperbolic).\<close>

lemma thin_triangles1:
  assumes "geodesic_segment_between G x y" "geodesic_segment_between H x (z::'a)"
          "t \<in> {0..Gromov_product_at x y z}"
  shows "dist (geodesic_segment_param G x t) (geodesic_segment_param H x t) \<le> 4 * deltaG(TYPE('a))"
proof -
  have *: "Gromov_product_at x z (geodesic_segment_param H x t) = t"
    apply (rule Gromov_product_geodesic_segment[OF assms(2)]) using assms(3) Gromov_product_le_dist(2)
    by (metis atLeastatMost_subset_iff subset_iff)
  have "Gromov_product_at x y (geodesic_segment_param H x t)
        \<ge> min (Gromov_product_at x y z) (Gromov_product_at x z (geodesic_segment_param H x t)) - deltaG(TYPE('a))"
    by (rule hyperb_ineq)
  then have I: "Gromov_product_at x y (geodesic_segment_param H x t) \<ge> t - deltaG(TYPE('a))"
    using assms(3) unfolding * by auto

  have *: "Gromov_product_at x (geodesic_segment_param G x t) y = t"
    apply (subst Gromov_product_commute)
    apply (rule Gromov_product_geodesic_segment[OF assms(1)]) using assms(3) Gromov_product_le_dist(1)
    by (metis atLeastatMost_subset_iff subset_iff)
  have "t - 2 * deltaG(TYPE('a)) = min t (t- deltaG(TYPE('a))) - deltaG(TYPE('a))"
    unfolding min_def using antisym by fastforce
  also have "... \<le> min (Gromov_product_at x (geodesic_segment_param G x t) y) (Gromov_product_at x y (geodesic_segment_param H x t)) - deltaG(TYPE('a))"
    using I * by auto
  also have "... \<le> Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t)"
    by (rule hyperb_ineq)
  finally have I: "Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t) \<ge> t - 2 * deltaG(TYPE('a))"
    by simp

  have A: "dist x (geodesic_segment_param G x t) = t"
    by (meson assms(1) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(1) subset_eq)
  have B: "dist x (geodesic_segment_param H x t) = t"
    by (meson assms(2) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(2) subset_eq)
  show ?thesis
    using I unfolding Gromov_product_at_def A B by auto
qed

theorem thin_triangles:
  assumes "geodesic_segment_between Gxy x y"
          "geodesic_segment_between Gxz x z"
          "geodesic_segment_between Gyz y z"
          "(w::'a) \<in> Gyz"
  shows "infdist w (Gxy \<union> Gxz) \<le> 4 * deltaG(TYPE('a))"
proof -
  obtain t where w: "t \<in> {0..dist y z}" "w = geodesic_segment_param Gyz y t"
    using geodesic_segment_param[OF assms(3)] assms(4) by (metis imageE)
  show ?thesis
  proof (cases "t \<le> Gromov_product_at y x z")
    case True
    have *: "dist w (geodesic_segment_param Gxy y t) \<le> 4 * deltaG(TYPE('a))" unfolding w(2)
      apply (rule thin_triangles1[of _ _ z _ x])
      using True assms(1) assms(3) w(1) by (auto simp add: geodesic_segment_commute Gromov_product_commute)
    show ?thesis
      apply (rule infdist_le2[OF _ *])
      by (metis True assms(1) box_real(2) geodesic_segment_commute geodesic_segment_param(3) Gromov_product_le_dist(1) mem_box_real(2) order_trans subset_eq sup.cobounded1 w(1))
  next
    case False
    define s where "s = dist y z - t"
    have s: "s \<in> {0..Gromov_product_at z y x}"
      unfolding s_def using Gromov_product_add[of y z x] w(1) False by (auto simp add: Gromov_product_commute)
    have w2: "w = geodesic_segment_param Gyz z s"
      unfolding s_def w(2) apply (rule geodesic_segment_reverse_param[symmetric]) using assms(3) w(1) by auto
    have *: "dist w (geodesic_segment_param Gxz z s) \<le> 4 * deltaG(TYPE('a))" unfolding w2
      apply (rule thin_triangles1[of _ _ y _ x])
      using s assms by (auto simp add: geodesic_segment_commute)
    show ?thesis
      apply (rule infdist_le2[OF _ *])
      by (metis Un_iff assms(2) atLeastAtMost_iff geodesic_segment_commute geodesic_segment_param(3) Gromov_product_commute Gromov_product_le_dist(1) order_trans s)
  qed
qed

text \<open>A consequence of the thin triangles property is that, although the geodesic between
two points is in general not unique in a Gromov-hyperbolic space, two such geodesics are
within $O(\delta)$ of each other.\<close>

lemma geodesics_nearby:
  assumes "geodesic_segment_between G x y" "geodesic_segment_between H x y"
          "(z::'a) \<in> G"
  shows "infdist z H \<le> 4 * deltaG(TYPE('a))"
using thin_triangles[OF geodesic_segment_between_x_x(1) assms(2) assms(1) assms(3)]
geodesic_segment_endpoints(1)[OF assms(2)] insert_absorb by fastforce

text \<open>A small variant of the property of thin triangles is that triangles are slim, i.e., there is
a point which is close to the three sides of the triangle (a "center" of the triangle, but
only defined up to $O(\delta)$). And one can take it on any side, and its distance to the corresponding
vertices is expressed in terms of a Gromov product.\<close>

lemma slim_triangle:
  assumes "geodesic_segment_between Gxy x y"
          "geodesic_segment_between Gxz x z"
          "geodesic_segment_between Gyz y (z::'a)"
  shows "\<exists>w. infdist w Gxy \<le> 4 * deltaG(TYPE('a)) \<and>
             infdist w Gxz \<le> 4 * deltaG(TYPE('a)) \<and>
             infdist w Gyz \<le> 4 * deltaG(TYPE('a)) \<and>
             dist w x = (Gromov_product_at x y z) \<and> w \<in> Gxy"
proof -
  define w where "w = geodesic_segment_param Gxy x (Gromov_product_at x y z)"
  have "w \<in> Gxy" unfolding w_def
    by (rule geodesic_segment_param(3)[OF assms(1)], auto)
  then have xy: "infdist w Gxy \<le> 4 * deltaG(TYPE('a))" by simp
  have *: "dist w x = (Gromov_product_at x y z)"
    unfolding w_def using assms(1)
    by (metis Gromov_product_le_dist(1) Gromov_product_nonneg atLeastAtMost_iff geodesic_segment_param(6) metric_space_class.dist_commute)

  define w2 where "w2 = geodesic_segment_param Gxz x (Gromov_product_at x y z)"
  have "w2 \<in> Gxz" unfolding w2_def
    by (rule geodesic_segment_param(3)[OF assms(2)], auto)
  moreover have "dist w w2 \<le> 4 * deltaG(TYPE('a))"
    unfolding w_def w2_def by (rule thin_triangles1[OF assms(1) assms(2)], auto)
  ultimately have xz: "infdist w Gxz \<le> 4 * deltaG(TYPE('a))"
    using infdist_le2 by blast

  have "w = geodesic_segment_param Gxy y (dist x y - Gromov_product_at x y z)"
    unfolding w_def by (rule geodesic_segment_reverse_param[OF assms(1), symmetric], auto)
  then have w: "w = geodesic_segment_param Gxy y (Gromov_product_at y x z)"
    using Gromov_product_add[of x y z] by (metis add_diff_cancel_left')

  define w3 where "w3 = geodesic_segment_param Gyz y (Gromov_product_at y x z)"
  have "w3 \<in> Gyz" unfolding w3_def
    by (rule geodesic_segment_param(3)[OF assms(3)], auto)
  moreover have "dist w w3 \<le> 4 * deltaG(TYPE('a))"
    unfolding w w3_def by (rule thin_triangles1[OF geodesic_segment_commute[OF assms(1)] assms(3)], auto)
  ultimately have yz: "infdist w Gyz \<le> 4 * deltaG(TYPE('a))"
    using infdist_le2 by blast

  show ?thesis using xy xz yz * \<open>w \<in> Gxy\<close> by force
qed

text \<open>The distance of a vertex of a triangle to the opposite side is essentially given by the
Gromov product, up to $2\delta$.\<close>

lemma dist_triangle_side_middle:
  assumes "geodesic_segment_between G x (y::'a)"
  shows "dist z (geodesic_segment_param G x (Gromov_product_at x z y)) \<le> Gromov_product_at z x y + 2 * deltaG(TYPE('a))"
proof -
  define m where "m = geodesic_segment_param G x (Gromov_product_at x z y)"
  have "m \<in> G"
    unfolding m_def using assms(1) by auto
  have A: "dist x m = Gromov_product_at x z y"
    unfolding m_def by (rule geodesic_segment_param(6)[OF assms(1)], auto)
  have B: "dist y m = dist x y - dist x m"
    using geodesic_segment_dist[OF assms \<open>m \<in> G\<close>] by (auto simp add: metric_space_class.dist_commute)
  have *: "dist x z + dist y m = Gromov_product_at z x y + dist x y"
          "dist x m + dist y z = Gromov_product_at z x y + dist x y"
    unfolding B A Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute divide_simps)

  have "dist x y + dist z m \<le> max (dist x z + dist y m) (dist x m + dist y z) + 2 * deltaG(TYPE('a))"
    by (rule hyperb_quad_ineq)
  then have "dist z m \<le> Gromov_product_at z x y + 2 * deltaG(TYPE('a))"
    unfolding * by auto
  then show ?thesis
    unfolding m_def by auto
qed

lemma infdist_triangle_side [mono_intros]:
  assumes "geodesic_segment_between G x (y::'a)"
  shows "infdist z G \<le> Gromov_product_at z x y + 2 * deltaG(TYPE('a))"
proof -
  have "infdist z G \<le> dist z (geodesic_segment_param G x (Gromov_product_at x z y))"
    using assms by (auto intro!: infdist_le)
  then show ?thesis
    using dist_triangle_side_middle[OF assms, of z] by auto
qed

text \<open>The distance of a point on a side of triangle to the opposite vertex is controlled by
the length of the opposite sides, up to $\delta$.\<close>

lemma dist_le_max_dist_triangle:
  assumes "geodesic_segment_between G x y"
          "m \<in> G"
  shows "dist m z \<le> max (dist x z) (dist y z) + deltaG(TYPE('a))"
proof -
  consider "dist m x \<le> deltaG(TYPE('a))" | "dist m y \<le> deltaG(TYPE('a))" |
           "dist m x \<ge> deltaG(TYPE('a)) \<and> dist m y \<ge> deltaG(TYPE('a)) \<and> Gromov_product_at z x m \<le> Gromov_product_at z m y" |
           "dist m x \<ge> deltaG(TYPE('a)) \<and> dist m y \<ge> deltaG(TYPE('a)) \<and> Gromov_product_at z m y \<le> Gromov_product_at z x m"
    by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "dist m z \<le> dist m x + dist x z"
      by (intro mono_intros)
    then show ?thesis using 1 by auto
  next
    case 2
    have "dist m z \<le> dist m y + dist y z"
      by (intro mono_intros)
    then show ?thesis using 2 by auto
  next
    case 3
    then have "Gromov_product_at z x m = min (Gromov_product_at z x m) (Gromov_product_at z m y)"
      by auto
    also have "... \<le> Gromov_product_at z x y + deltaG(TYPE('a))"
      by (intro mono_intros)
    finally have "dist z m \<le> dist z y + dist x m - dist x y + 2 * deltaG(TYPE('a))"
      unfolding Gromov_product_at_def by (auto simp add: divide_simps algebra_simps)
    also have "... = dist z y - dist m y + 2 * deltaG(TYPE('a))"
      using geodesic_segment_dist[OF assms] by auto
    also have "... \<le> dist z y + deltaG(TYPE('a))"
      using 3 by auto
    finally show ?thesis
      by (simp add: metric_space_class.dist_commute)
  next
    case 4
    then have "Gromov_product_at z m y = min (Gromov_product_at z x m) (Gromov_product_at z m y)"
      by auto
    also have "... \<le> Gromov_product_at z x y + deltaG(TYPE('a))"
      by (intro mono_intros)
    finally have "dist z m \<le> dist z x + dist m y - dist x y + 2 * deltaG(TYPE('a))"
      unfolding Gromov_product_at_def by (auto simp add: divide_simps algebra_simps)
    also have "... = dist z x - dist x m + 2 * deltaG(TYPE('a))"
      using geodesic_segment_dist[OF assms] by auto
    also have "... \<le> dist z x + deltaG(TYPE('a))"
      using 4 by (simp add: metric_space_class.dist_commute)
    finally show ?thesis
      by (simp add: metric_space_class.dist_commute)
  qed
qed

end (* of locale Gromov_hyperbolic_space *)

text \<open>A useful variation around the previous properties is that quadrilaterals are thin, in the
following sense: if one has a union of three geodesics from $x$ to $t$, then a geodesic from $x$
to $t$ remains within distance $8\delta$ of the union of these 3 geodesics. We formulate the
statement in geodesic hyperbolic spaces as the proof requires the construction of an additional
geodesic, but in fact the statement is true without this assumption, thanks to the Bonk-Schramm
extension theorem.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) thin_quadrilaterals:
  assumes "geodesic_segment_between Gxy x y"
          "geodesic_segment_between Gyz y z"
          "geodesic_segment_between Gzt z t"
          "geodesic_segment_between Gxt x t"
          "(w::'a) \<in> Gxt"
  shows "infdist w (Gxy \<union> Gyz \<union> Gzt) \<le> 8 * deltaG(TYPE('a))"
proof -
  have I: "infdist w ({x--z} \<union> Gzt) \<le> 4 * deltaG(TYPE('a))"
    apply (rule thin_triangles[OF _ assms(3) assms(4) assms(5)])
    by (simp add: geodesic_segment_commute)
  have "\<exists>u \<in> {x--z} \<union> Gzt. infdist w ({x--z} \<union> Gzt) = dist w u"
    apply (rule infdist_proper_attained, auto intro!: proper_Un simp add: geodesic_segment_topology(7))
    by (meson assms(3) geodesic_segmentI geodesic_segment_topology)
  then obtain u where u: "u \<in> {x--z} \<union> Gzt" "infdist w ({x--z} \<union> Gzt) = dist w u"
    by auto
  have "infdist u (Gxy \<union> Gyz \<union> Gzt) \<le> 4 * deltaG(TYPE('a))"
  proof (cases "u \<in> {x--z}")
    case True
    have "infdist u (Gxy \<union> Gyz \<union> Gzt) \<le> infdist u (Gxy \<union> Gyz)"
      apply (intro mono_intros) using assms(1) by auto
    also have "... \<le> 4 * deltaG(TYPE('a))"
      using thin_triangles[OF geodesic_segment_commute[OF assms(1)] assms(2) _ True] by auto
    finally show ?thesis
      by auto
  next
    case False
    then have *: "u \<in> Gzt" using u(1) by auto
    have "infdist u (Gxy \<union> Gyz \<union> Gzt) \<le> infdist u Gzt"
      apply (intro mono_intros) using assms(3) by auto
    also have "... = 0" using * by auto
    finally show ?thesis
      using local.delta_nonneg by linarith
  qed
  moreover have "infdist w (Gxy \<union> Gyz \<union> Gzt) \<le> infdist u (Gxy \<union> Gyz \<union> Gzt) + dist w u"
    by (intro mono_intros)
  ultimately show ?thesis
    using I u(2) by auto
qed

text \<open>There are converses to the above statements: if triangles are thin, or slim, then the space
is Gromov-hyperbolic, for some $\delta$. We prove these criteria here, following the proofs in
Ghys (with a simplification in the case of slim triangles.\<close>

text \<open>The basic result we will use twice below is the following: if points on sides of triangles
at the same distance of the basepoint are close to each other up to the Gromov product, then the
space is hyperbolic. The proof goes as follows. One wants to show that $(x,z)_e \geq
\min((x,y)_e, (y,z)_e) - \delta = t-\delta$. On $[ex]$, $[ey]$ and $[ez]$, consider points
$wx$, $wy$ and $wz$ at distance $t$ of $e$. Then $wx$ and $wy$ are $\delta$-close by assumption,
and so are $wy$ and $wz$. Then $wx$ and $wz$ are $2\delta$-close. One can use these two points
to express $(x,z)_e$, and the result follows readily.\<close>

lemma (in geodesic_space) controlled_thin_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z t Gxy Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> t \<in> {0..Gromov_product_at x y z}
      \<Longrightarrow> dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> delta"
  shows "Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof (rule Gromov_hyperbolic_subsetI2)
  fix e x y z::'a
  define t where "t = min (Gromov_product_at e x y) (Gromov_product_at e y z)"
  define wx where "wx = geodesic_segment_param {e--x} e t"
  define wy where "wy = geodesic_segment_param {e--y} e t"
  define wz where "wz = geodesic_segment_param {e--z} e t"
  have "dist wx wy \<le> delta"
    unfolding wx_def wy_def t_def by (rule assms[of _ _ x _ y], auto)
  have "dist wy wz \<le> delta"
    unfolding wy_def wz_def t_def by (rule assms[of _ _ y _ z], auto)

  have "t + dist wy x = dist e wx + dist wy x"
    unfolding wx_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
    unfolding t_def by (auto, meson Gromov_product_le_dist(1) min.absorb_iff2 min.left_idem order.trans)
  also have "... \<le> dist e wx + (dist wy wx + dist wx x)"
    by (intro mono_intros)
  also have "... \<le> dist e wx + (delta + dist wx x)"
    using \<open>dist wx wy \<le> delta\<close> by (auto simp add: metric_space_class.dist_commute)
  also have "... = delta + dist e x"
    apply auto apply (rule geodesic_segment_dist[of "{e--x}"])
    unfolding wx_def t_def by (auto simp add: geodesic_segment_param_in_segment)
  finally have *: "t + dist wy x - delta \<le> dist e x" by simp

  have "t + dist wy z = dist e wz + dist wy z"
    unfolding wz_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
    unfolding t_def by (auto, meson Gromov_product_le_dist(2) min.absorb_iff1 min.right_idem order.trans)
  also have "... \<le> dist e wz + (dist wy wz + dist wz z)"
    by (intro mono_intros)
  also have "... \<le> dist e wz + (delta + dist wz z)"
    using \<open>dist wy wz \<le> delta\<close> by (auto simp add: metric_space_class.dist_commute)
  also have "... = delta + dist e z"
    apply auto apply (rule geodesic_segment_dist[of "{e--z}"])
    unfolding wz_def t_def by (auto simp add: geodesic_segment_param_in_segment)
  finally have "t + dist wy z - delta \<le> dist e z" by simp

  then have "(t + dist wy x - delta) + (t + dist wy z - delta) \<le> dist e x + dist e z"
    using * by simp
  also have "... = dist x z + 2 * Gromov_product_at e x z"
    unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
  also have "... \<le> dist wy x + dist wy z + 2 * Gromov_product_at e x z"
    using metric_space_class.dist_triangle[of x z wy] by (auto simp add: metric_space_class.dist_commute)
  finally have "2 * t - 2 * delta \<le> 2 * Gromov_product_at e x z"
    by auto
  then show "min (Gromov_product_at e x y) (Gromov_product_at e y z) - delta \<le> Gromov_product_at e x z"
    unfolding t_def by auto
qed

text \<open>We prove that if triangles are thin, i.e., they satisfy the Rips condition, i.e., every side
of a triangle is included in the $\delta$-neighborhood of the union of the other triangles, then
the space is hyperbolic. If a point $w$ on $[xy]$ satisfies $d(x,w) < (y,z)_x - \delta$, then its
friend on $[xz] \cup [yz]$ has to be on $[xz]$, and roughly at the same distance of the origin.
Then it follows that the point on $[xz]$ with $d(x,w') = d(x,w)$ is close to $w$, as desired.
If $d(x,w) \in [(y,z)_x - \delta, (y,z)_x)$, we argue in the same way but for the point which
is closer to $x$ by an amount $\delta$. Finally, the last case $d(x,w) = (y,z)_x$ follows by
continuity.\<close>

proposition (in geodesic_space) thin_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z w Gxy Gyz Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> geodesic_segment_between Gyz y z
        \<Longrightarrow> w \<in> Gxy \<Longrightarrow> infdist w (Gxz \<union> Gyz) \<le> delta"
  shows "Gromov_hyperbolic_subset (4 * delta) (UNIV::'a set)"
proof -
  obtain x0::'a where True by auto
  have "infdist x0 ({x0} \<union> {x0}) \<le> delta"
    by (rule assms[of "{x0}" x0 x0 "{x0}" x0 "{x0}" x0], auto)
  then have [simp]: "delta \<ge> 0"
    using infdist_nonneg by auto

  have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> 4 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t \<in> {0..Gromov_product_at x y z}"
    for x y z t Gxy Gxz
  proof -
    have Main: "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u) \<le> 4 * delta"
      if "u \<in> {delta..<Gromov_product_at x y z}" for u
    proof -
      define wy where "wy = geodesic_segment_param Gxy x (u-delta)"
      have "dist wy (geodesic_segment_param Gxy x u) = abs((u-delta) - u)"
        unfolding wy_def apply (rule geodesic_segment_param(7)[OF H(1)]) using that apply auto
        using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0\<close> by linarith+
      then have I1: "dist wy (geodesic_segment_param Gxy x u) = delta" by auto

      have "infdist wy (Gxz \<union> {y--z}) \<le> delta"
        unfolding wy_def apply (rule assms[of Gxy x y _ z]) using H by (auto simp add: geodesic_segment_param_in_segment)
      moreover have "\<exists>wz \<in> Gxz \<union> {y--z}. infdist wy (Gxz \<union> {y--z}) = dist wy wz"
        apply (rule infdist_proper_attained, intro proper_Un)
        using H(2) by (auto simp add: geodesic_segment_topology)
      ultimately obtain wz where wz: "wz \<in> Gxz \<union> {y--z}" "dist wy wz \<le> delta"
        by force

      have "dist wz x \<le> dist wz wy + dist wy x"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> delta + (u-delta)"
        apply (intro add_mono) using wz(2) unfolding wy_def apply (auto simp add: metric_space_class.dist_commute)
        apply (intro eq_refl geodesic_segment_param(6)[OF H(1)])
        using that apply auto
        by (metis diff_0_right diff_mono dual_order.trans Gromov_product_le_dist(1) less_eq_real_def metric_space_class.dist_commute metric_space_class.zero_le_dist wy_def)
      finally have "dist wz x \<le> u" by auto
      also have "... < Gromov_product_at x y z"
        using that by auto
      also have "... \<le> infdist x {y--z}"
        by (rule Gromov_product_le_infdist, auto)
      finally have "dist x wz < infdist x {y--z}"
        by (simp add: metric_space_class.dist_commute)
      then have "wz \<notin> {y--z}"
        by (metis add.left_neutral infdist_triangle infdist_zero leD)
      then have "wz \<in> Gxz"
        using wz by auto

      have "u - delta = dist x wy"
        unfolding wy_def apply (rule geodesic_segment_param(6)[symmetric, OF H(1)])
        using that apply auto
        using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0\<close> by linarith
      also have "... \<le> dist x wz + dist wz wy"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> dist x wz + delta"
        using wz(2) by (simp add: metric_space_class.dist_commute)
      finally have "dist x wz \<ge> u - 2 * delta" by auto

      define dz where "dz = dist x wz"
      have *: "wz = geodesic_segment_param Gxz x dz"
        unfolding dz_def using \<open>wz \<in> Gxz\<close> H(2) by auto
      have "dist wz (geodesic_segment_param Gxz x u) = abs(dz - u)"
        unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
        unfolding dz_def using \<open>dist wz x \<le> u\<close> that apply (auto simp add: metric_space_class.dist_commute)
        using Gromov_product_le_dist(2)[of x y z] \<open>delta \<ge> 0\<close> by linarith+
      also have "... \<le> 2 * delta"
        unfolding dz_def using \<open>dist wz x \<le> u\<close> \<open>dist x wz \<ge> u - 2 * delta\<close>
        by (auto simp add: metric_space_class.dist_commute)
      finally have I3: "dist wz (geodesic_segment_param Gxz x u) \<le> 2 * delta"
        by simp

      have "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u)
              \<le> dist (geodesic_segment_param Gxy x u) wy + dist wy wz + dist wz (geodesic_segment_param Gxz x u)"
        by (rule dist_triangle4)
      also have "... \<le> delta + delta + (2 * delta)"
        using I1 wz(2) I3 by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis by simp
    qed
    have "t \<in> {0..dist x y}" "t \<in> {0..dist x z}" "t \<ge> 0"
      using \<open>t \<in> {0..Gromov_product_at x y z}\<close> apply auto
      using Gromov_product_le_dist[of x y z] by linarith+
    consider "t \<le> delta" | "t \<in> {delta..<Gromov_product_at x y z}" | "t = Gromov_product_at x y z \<and> t > delta"
      using \<open>t \<in> {0..Gromov_product_at x y z}\<close> by (auto, linarith)
    then show ?thesis
    proof (cases)
      case 1
      have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> dist x (geodesic_segment_param Gxy x t) + dist x (geodesic_segment_param Gxz x t)"
        by (rule metric_space_class.dist_triangle3)
      also have "... = t + t"
        using geodesic_segment_param(6)[OF H(1) \<open>t \<in> {0..dist x y}\<close>] geodesic_segment_param(6)[OF H(2) \<open>t \<in> {0..dist x z}\<close>]
        by auto
      also have "... \<le> 4 * delta" using 1 \<open>delta \<ge> 0\<close> by linarith
      finally show ?thesis by simp
    next
      case 2
      show ?thesis using Main[OF 2] by simp
    next
      case 3
      text \<open>In this case, we argue by approximating $t$ by a slightly smaller parameter, for which
      the result has already been proved above. We need to argue that all functions are continuous
      on the sets we are considering, which is straightforward but tedious.\<close>
      define u::"nat \<Rightarrow> real" where "u = (\<lambda>n. t-1/n)"
      have "u \<longlonglongrightarrow> t - 0"
        unfolding u_def by (intro tendsto_intros)
      then have "u \<longlonglongrightarrow> t" by simp
      then have *: "eventually (\<lambda>n. u n > delta) sequentially"
        using 3 by (auto simp add: order_tendsto_iff)
      have **: "eventually (\<lambda>n. u n \<ge> 0) sequentially"
        apply (rule eventually_elim2[OF *, of "(\<lambda>n. delta \<ge> 0)"]) apply auto
        using \<open>delta \<ge> 0\<close> by linarith
      have ***: "u n \<le> t" for n unfolding u_def by auto
      have A: "eventually (\<lambda>n. u n \<in> {delta..<Gromov_product_at x y z}) sequentially"
        apply (auto intro!: eventually_conj)
        apply (rule eventually_mono[OF *], simp)
        unfolding u_def using 3 by auto
      have B: "eventually (\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)) \<le> 4 * delta) sequentially"
        by (rule eventually_mono[OF A Main], simp)
      have C: "(\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)))
            \<longlonglongrightarrow> dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t)"
        apply (intro tendsto_intros)
        apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t\<close> \<open>t \<in> {0..dist x y}\<close>])
        apply (simp add: isometry_on_continuous H(1))
        using ** *** \<open>t \<in> {0..dist x y}\<close> apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
        apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t\<close> \<open>t \<in> {0..dist x z}\<close>])
        apply (simp add: isometry_on_continuous H(2))
        using ** *** \<open>t \<in> {0..dist x z}\<close> apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
        done
      show ?thesis
        using B unfolding eventually_sequentially using LIMSEQ_le_const2[OF C] by simp
    qed
  qed
  with controlled_thin_triangles_implies_hyperbolic[OF this]
  show ?thesis by auto
qed

text \<open>Then, we prove that if triangles are slim (i.e., there is a point that is $\delta$-close to
all sides), then the space is hyperbolic. Using the previous statement, we should show that points
on $[xy]$ and $[xz]$ at the same distance $t$ of the origin are close, if $t \leq (y,z)_x$.
There are two steps:
- for $t = (y,z)_x$, then the two points are in fact close to the middle of the triangle
(as this point satisfies $d(x,y) = d(x,w) + d(w,y) + O(\delta)$, and similarly for the other sides,
one gets readily $d(x,w) = (y,z)_w + O(\delta)$ by expanding the formula for the Gromov product).
Hence, they are close together.
- For $t < (y,z)_x$, we argue that there are points $y' \in [xy]$ and $z' \in [xz]$ for which
$t = (y',z')_x$, by a continuity argument and the intermediate value theorem.
Then the result follows from the first step in the triangle $xy'z'$.

The proof we give is simpler than the one in~\cite{ghys_hyperbolique}, and gives better constants.\<close>

proposition (in geodesic_space) slim_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z Gxy Gyz Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> geodesic_segment_between Gyz y z
        \<Longrightarrow> \<exists>w. infdist w Gxy \<le> delta \<and> infdist w Gxz \<le> delta \<and> infdist w Gyz \<le> delta"
  shows "Gromov_hyperbolic_subset (6 * delta) (UNIV::'a set)"
proof -
  text \<open>First step: the result is true for $t = (y,z)_x$.\<close>
  have Main: "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z)) \<le> 6 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z"
    for x y z Gxy Gxz
  proof -
    obtain w where w: "infdist w Gxy \<le> delta" "infdist w Gxz \<le> delta" "infdist w {y--z} \<le> delta"
      using assms[OF H, of "{y--z}"] by auto
    have "\<exists>wxy \<in> Gxy. infdist w Gxy = dist w wxy"
      apply (rule infdist_proper_attained) using H(1) by (auto simp add: geodesic_segment_topology)
    then obtain wxy where wxy: "wxy \<in> Gxy" "dist w wxy \<le> delta"
      using w by auto
    have "\<exists>wxz \<in> Gxz. infdist w Gxz = dist w wxz"
      apply (rule infdist_proper_attained) using H(2) by (auto simp add: geodesic_segment_topology)
    then obtain wxz where wxz: "wxz \<in> Gxz" "dist w wxz \<le> delta"
      using w by auto
    have "\<exists>wyz \<in> {y--z}. infdist w {y--z} = dist w wyz"
      apply (rule infdist_proper_attained) by (auto simp add: geodesic_segment_topology)
    then obtain wyz where wyz: "wyz \<in> {y--z}" "dist w wyz \<le> delta"
      using w by auto

    have I: "dist wxy wxz \<le> 2 * delta" "dist wxy wyz \<le> 2 * delta" "dist wxz wyz \<le> 2 * delta"
      using metric_space_class.dist_triangle[of wxy wxz w] metric_space_class.dist_triangle[of wxy wyz w] metric_space_class.dist_triangle[of wxz wyz w]
            wxy(2) wyz(2) wxz(2) by (auto simp add: metric_space_class.dist_commute)

    text \<open>We show that $d(x, wxy)$ is close to the Gromov product of $y$ and $z$ seen from $x$.
    This follows from the fact that $w$ is essentially on all geodesics, so that everything simplifies
    when one writes down the Gromov products, leaving only $d(x, w)$ up to $O(\delta)$.
    To get the right $O(\delta)$, one has to be a little bit careful, using the triangular inequality
    when possible. This means that the computations for the upper and lower bounds are different,
    making them a little bit tedious, although straightforward.\<close>
    have "dist y wxy -4 * delta + dist wxy z \<le> dist y wxy - dist wxy wyz + dist wxy z - dist wxy wyz"
      using I by simp
    also have "... \<le> dist wyz y + dist wyz z"
      using metric_space_class.dist_triangle[of y wxy wyz] metric_space_class.dist_triangle[of wxy z wyz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist y z"
      using wyz(1) by (metis geodesic_segment_dist local.some_geodesic_is_geodesic_segment(1) metric_space_class.dist_commute)
    finally have *: "dist y wxy + dist wxy z - 4 * delta \<le> dist y z" by simp
    have "2 * Gromov_product_at x y z = dist x y + dist x z - dist y z"
      unfolding Gromov_product_at_def by simp
    also have "... \<le> dist x wxy + dist wxy y + dist x wxy + dist wxy z - (dist y wxy + dist wxy z - 4 * delta)"
      using metric_space_class.dist_triangle[of x y wxy] metric_space_class.dist_triangle[of x z wxy] *
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = 2 * dist x wxy + 4 * delta"
      by (auto simp add: metric_space_class.dist_commute)
    finally have A: "Gromov_product_at x y z \<le> dist x wxy + 2 * delta" by simp

    have "dist x wxy -4 * delta + dist wxy z \<le> dist x wxy - dist wxy wxz + dist wxy z - dist wxy wxz"
      using I by simp
    also have "... \<le> dist wxz x + dist wxz z"
      using metric_space_class.dist_triangle[of x wxy wxz] metric_space_class.dist_triangle[of wxy z wxz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist x z"
      using wxz(1) H(2) by (metis geodesic_segment_dist metric_space_class.dist_commute)
    finally have *: "dist x wxy + dist wxy z - 4 * delta \<le> dist x z" by simp
    have "2 * dist x wxy - 4 * delta = (dist x wxy + dist wxy y) + (dist x wxy + dist wxy z - 4 * delta) - (dist y wxy + dist wxy z)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x y + dist x z - dist y z"
      using * metric_space_class.dist_triangle[of y z wxy] geodesic_segment_dist[OF H(1) wxy(1)] by auto
    also have "... = 2 * Gromov_product_at x y z"
      unfolding Gromov_product_at_def by simp
    finally have B: "Gromov_product_at x y z \<ge> dist x wxy - 2 * delta" by simp

    define dy where "dy = dist x wxy"
    have *: "wxy = geodesic_segment_param Gxy x dy"
      unfolding dy_def using \<open>wxy \<in> Gxy\<close> H(1) by auto
    have "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) = abs(dy - Gromov_product_at x y z)"
      unfolding * apply (rule geodesic_segment_param(7)[OF H(1)])
      unfolding dy_def using that geodesic_segment_dist_le[OF H(1) wxy(1), of x] by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> 2 * delta"
      using A B unfolding dy_def by auto
    finally have Iy: "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) \<le> 2 * delta"
      by simp

    text \<open>We need the same estimate for $wxz$. The proof is exactly the same, copied and pasted.
    It would be better to have a separate statement, but since its assumptions would be rather
    cumbersome I decided to keep the two proofs.\<close>
    have "dist z wxz -4 * delta + dist wxz y \<le> dist z wxz - dist wxz wyz + dist wxz y - dist wxz wyz"
      using I by simp
    also have "... \<le> dist wyz z + dist wyz y"
      using metric_space_class.dist_triangle[of z wxz wyz] metric_space_class.dist_triangle[of wxz y wyz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist z y"
      using \<open>dist wyz y + dist wyz z = dist y z\<close> by (auto simp add: metric_space_class.dist_commute)
    finally have *: "dist z wxz + dist wxz y - 4 * delta \<le> dist z y" by simp
    have "2 * Gromov_product_at x y z = dist x z + dist x y - dist z y"
      unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x wxz + dist wxz z + dist x wxz + dist wxz y - (dist z wxz + dist wxz y - 4 * delta)"
      using metric_space_class.dist_triangle[of x z wxz] metric_space_class.dist_triangle[of x y wxz] *
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = 2 * dist x wxz + 4 * delta"
      by (auto simp add: metric_space_class.dist_commute)
    finally have A: "Gromov_product_at x y z \<le> dist x wxz + 2 * delta" by simp

    have "dist x wxz -4 * delta + dist wxz y \<le> dist x wxz - dist wxz wxy + dist wxz y - dist wxz wxy"
      using I by (simp add: metric_space_class.dist_commute)
    also have "... \<le> dist wxy x + dist wxy y"
      using metric_space_class.dist_triangle[of x wxz wxy] metric_space_class.dist_triangle[of wxz y wxy]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist x y"
      using wxy(1) H(1) by (metis geodesic_segment_dist metric_space_class.dist_commute)
    finally have *: "dist x wxz + dist wxz y - 4 * delta \<le> dist x y" by simp
    have "2 * dist x wxz - 4 * delta = (dist x wxz + dist wxz z) + (dist x wxz + dist wxz y - 4 * delta) - (dist z wxz + dist wxz y)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x z + dist x y - dist z y"
      using * metric_space_class.dist_triangle[of z y wxz] geodesic_segment_dist[OF H(2) wxz(1)] by auto
    also have "... = 2 * Gromov_product_at x y z"
      unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
    finally have B: "Gromov_product_at x y z \<ge> dist x wxz - 2 * delta" by simp

    define dz where "dz = dist x wxz"
    have *: "wxz = geodesic_segment_param Gxz x dz"
      unfolding dz_def using \<open>wxz \<in> Gxz\<close> H(2) by auto
    have "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) = abs(dz - Gromov_product_at x y z)"
      unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
      unfolding dz_def using that geodesic_segment_dist_le[OF H(2) wxz(1), of x] by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> 2 * delta"
      using A B unfolding dz_def by auto
    finally have Iz: "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) \<le> 2 * delta"
      by simp

    have "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z))
      \<le> dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) wxy + dist wxy wxz + dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z))"
      by (rule dist_triangle4)
    also have "... \<le> 2 * delta + 2 * delta + 2 * delta"
      using Iy Iz I by (auto simp add: metric_space_class.dist_commute)
    finally show ?thesis by simp
  qed

  text \<open>Second step: the result is true for $t \leq (y,z)_x$, by a continuity argument and a
  reduction to the first step.\<close>
  have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> 6 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t \<in> {0..Gromov_product_at x y z}"
    for x y z t Gxy Gxz
  proof -
    define ys where "ys = (\<lambda>s. geodesic_segment_param Gxy x (s * dist x y))"
    define zs where "zs = (\<lambda>s. geodesic_segment_param Gxz x (s * dist x z))"
    define F where "F = (\<lambda>s. Gromov_product_at x (ys s) (zs s))"
    have "\<exists>s. 0 \<le> s \<and> s \<le> 1 \<and> F s = t"
    proof (rule IVT')
      show "F 0 \<le> t" "t \<le> F 1"
        unfolding F_def using that unfolding ys_def zs_def by (auto simp add: Gromov_product_e_x_x)
      show "continuous_on {0..1} F"
        unfolding F_def Gromov_product_at_def ys_def zs_def
        apply (intro continuous_intros continuous_on_compose2[of "{0..dist x y}" _ _ "\<lambda>t. t * dist x y"] continuous_on_compose2[of "{0..dist x z}" _ _ "\<lambda>t. t * dist x z"])
        apply (auto intro!: isometry_on_continuous geodesic_segment_param(4) that)
        using metric_space_class.zero_le_dist mult_left_le_one_le by blast+
    qed (simp)
    then obtain s where s: "s \<in> {0..1}" "t = Gromov_product_at x (ys s) (zs s)"
      unfolding F_def by auto

    have a: "x = geodesic_segment_param Gxy x 0" using H(1) by auto
    have b: "x = geodesic_segment_param Gxz x 0" using H(2) by auto
    have dy: "dist x (ys s) = s * dist x y"
      unfolding ys_def apply (rule geodesic_segment_param[OF H(1)]) using s(1) by (auto simp add: mult_left_le_one_le)
    have dz: "dist x (zs s) = s * dist x z"
      unfolding zs_def apply (rule geodesic_segment_param[OF H(2)]) using s(1) by (auto simp add: mult_left_le_one_le)

    define Gxy2 where "Gxy2 = geodesic_subsegment Gxy x 0 (s * dist x y)"
    define Gxz2 where "Gxz2 = geodesic_subsegment Gxz x 0 (s * dist x z)"

    have "dist (geodesic_segment_param Gxy2 x t) (geodesic_segment_param Gxz2 x t) \<le> 6 * delta"
    unfolding s(2) proof (rule Main)
      show "geodesic_segment_between Gxy2 x (ys s)"
        apply (subst a) unfolding Gxy2_def ys_def apply (rule geodesic_subsegment[OF H(1)])
        using s(1) by (auto simp add: mult_left_le_one_le)
      show "geodesic_segment_between Gxz2 x (zs s)"
        apply (subst b) unfolding Gxz2_def zs_def apply (rule geodesic_subsegment[OF H(2)])
        using s(1) by (auto simp add: mult_left_le_one_le)
    qed
    moreover have "geodesic_segment_param Gxy2 x (t-0) = geodesic_segment_param Gxy x t"
      apply (subst a) unfolding Gxy2_def apply (rule geodesic_subsegment(3)[OF H(1)])
      using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
      unfolding dy[symmetric] by (rule Gromov_product_le_dist)
    moreover have "geodesic_segment_param Gxz2 x (t-0) = geodesic_segment_param Gxz x t"
      apply (subst b) unfolding Gxz2_def apply (rule geodesic_subsegment(3)[OF H(2)])
      using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
      unfolding dz[symmetric] by (rule Gromov_product_le_dist)
    ultimately show ?thesis by simp
  qed
  with controlled_thin_triangles_implies_hyperbolic[OF this]
  show ?thesis by auto
qed



section \<open>Metric trees\<close>

text \<open>Metric trees have several equivalent definitions. The simplest one is probably that it
is a geodesic space in which the union of two geodesic segments intersecting only at one endpoint is
still a geodesic segment.

Metric trees are Gromov hyperbolic, with $\delta = 0$.\<close>

class metric_tree = geodesic_space +
  assumes geod_union: "geodesic_segment_between G x y \<Longrightarrow> geodesic_segment_between H y z \<Longrightarrow> G \<inter> H = {y} \<Longrightarrow> geodesic_segment_between (G \<union> H) x z"

text \<open>We will now show that the real line is a metric tree, by identifying its geodesic
segments, i.e., the compact intervals.\<close>

lemma geodesic_segment_between_real:
  assumes "x \<le> (y::real)"
  shows "geodesic_segment_between (G::real set) x y = (G = {x..y})"
proof
  assume H: "geodesic_segment_between G x y"
  then have "connected G" "x \<in> G" "y \<in> G"
    using geodesic_segment_topology(2) geodesic_segmentI geodesic_segment_endpoints by auto
  then have *: "{x..y} \<subseteq> G"
    by (simp add: connected_contains_Icc)
  moreover have "G \<subseteq> {x..y}"
  proof
    fix s assume "s \<in> G"
    have "abs(s-x) + abs(s-y) = abs(x-y)"
      using geodesic_segment_dist[OF H \<open>s \<in> G\<close>] unfolding dist_real_def by auto
    then show "s \<in> {x..y}" using \<open>x \<le> y\<close> by auto
  qed
  ultimately show "G = {x..y}" by auto
next
  assume H: "G = {x..y}"
  define g where "g = (\<lambda>t. t + x)"
  have "g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
    unfolding g_def isometry_on_def H using \<open>x \<le> y\<close> by (auto simp add: dist_real_def)
  then have "\<exists>g. g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
    by auto
  then show "geodesic_segment_between G x y" unfolding geodesic_segment_between_def by auto
qed

lemma geodesic_segment_between_real':
  "{x--y} = {min x y..max x (y::real)}"
by (metis geodesic_segment_between_real geodesic_segment_commute some_geodesic_is_geodesic_segment(1) max_def min.cobounded1 min_def)

lemma geodesic_segment_real:
  "geodesic_segment (G::real set) = (\<exists>x y. x \<le> y \<and> G = {x..y})"
proof
  assume "geodesic_segment G"
  then obtain x y where *: "geodesic_segment_between G x y" unfolding geodesic_segment_def by auto
  have "(x \<le> y \<and> G = {x..y}) \<or> (y \<le> x \<and> G = {y..x})"
    apply (rule le_cases[of x y])
    using geodesic_segment_between_real * geodesic_segment_commute apply simp
    using geodesic_segment_between_real * geodesic_segment_commute by metis
  then show "\<exists>x y. x \<le> y \<and> G = {x..y}" by auto
next
  assume "\<exists>x y. x \<le> y \<and> G = {x..y}"
  then show "geodesic_segment G"
    unfolding geodesic_segment_def using geodesic_segment_between_real by metis
qed

instance real::metric_tree
proof
  fix G H::"real set" and x y z::real assume GH: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y}"
  have G: "G = {min x y..max x y}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have H: "H = {min y z..max y z}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have *: "(x \<le> y \<and> y \<le> z) \<or> (z \<le> y \<and> y \<le> x)"
    using G H \<open>G \<inter> H = {y}\<close> unfolding min_def max_def
    apply auto
    apply (metis (mono_tags, hide_lams) min_le_iff_disj order_refl)
    by (metis (full_types) less_eq_real_def max_def)
  show "geodesic_segment_between (G \<union> H) x z"
    using * apply rule
    using \<open>G \<inter> H = {y}\<close> unfolding G H apply (metis G GH(1) GH(2) H geodesic_segment_between_real ivl_disj_un_two_touch(4) order_trans)
    using \<open>G \<inter> H = {y}\<close> unfolding G H
    by (metis (full_types) Un_commute geodesic_segment_between_real geodesic_segment_commute ivl_disj_un_two_touch(4) le_max_iff_disj max.absorb_iff2 max.commute min_absorb2)
qed

context metric_tree begin

text \<open>We show that a metric tree is uniquely geodesic.\<close>

subclass uniquely_geodesic_space
proof
  fix x y G H assume H: "geodesic_segment_between G x y" "geodesic_segment_between H x (y::'a)"
  show "G = H"
  proof (rule uniquely_geodesic_spaceI[OF _ H])
    fix G H x y assume "geodesic_segment_between G x y" "geodesic_segment_between H x y" "G \<inter> H = {x, (y::'a)}"
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      then have "dist x y > 0" by auto
      obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
        by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
      define G2 where "G2 = g`{0..dist x y/2}"
      have "G2 \<subseteq> G" unfolding G2_def g(4) by auto
      define z where "z = g(dist x y/2)"
      have "dist x z = dist x y/2"
        using isometry_onD[OF g(3), of 0 "dist x y/2"] g(1) z_def unfolding dist_real_def by auto
      have "dist y z = dist x y/2"
        using isometry_onD[OF g(3), of "dist x y" "dist x y/2"] g(2) z_def unfolding dist_real_def by auto

      have G2: "geodesic_segment_between G2 x z" unfolding \<open>g 0 = x\<close>[symmetric] z_def G2_def
        apply (rule geodesic_segmentI2) by (rule isometry_on_subset[OF g(3)], auto simp add: \<open>g 0 = x\<close>)
      have [simp]: "x \<in> G2" "z \<in> G2" using geodesic_segment_endpoints G2 by auto
      have "dist x a \<le> dist x z" if "a \<in> G2" for a
        apply (rule geodesic_segment_dist_le) using G2 that by auto
      also have "... < dist x y" unfolding \<open>dist x z = dist x y/2\<close> using \<open>dist x y > 0\<close> by auto
      finally have "y \<notin> G2" by auto

      then have "G2 \<inter> H = {x}"
        using \<open>G2 \<subseteq> G\<close> \<open>x \<in> G2\<close> \<open>G \<inter> H = {x, y}\<close> by auto
      have *: "geodesic_segment_between (G2 \<union> H) z y"
        apply (rule geod_union[of _ _ x])
        using \<open>G2 \<inter> H = {x}\<close> \<open>geodesic_segment_between H x y\<close> G2 by (auto simp add: geodesic_segment_commute)
      have "dist x y \<le> dist z x + dist x y" by auto
      also have "... = dist z y"
        apply (rule geodesic_segment_dist[OF *]) using \<open>G \<inter> H = {x, y}\<close> by auto
      also have "... = dist x y / 2"
        by (simp add: \<open>dist y z = dist x y / 2\<close> metric_space_class.dist_commute)
      finally show False using \<open>dist x y > 0\<close> by auto
    qed
  qed
qed

text \<open>An important property of metric trees is that any geodesic triangle is degenerate, i.e., the
three sides intersect at a unique point, the center of the triangle, that we introduce now.\<close>

definition center::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "center x y z = (SOME t. t \<in> {x--y} \<inter> {x--z} \<inter> {y--z})"

lemma center_as_intersection:
  "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "{x--y} = g`{0..dist x y}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))
  obtain h where h: "h 0 = x" "h (dist x z) = z" "isometry_on {0..dist x z} h" "{x--z} = h`{0..dist x z}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))

  define Z where "Z = {t \<in> {0..min (dist x y) (dist x z)}. g t = h t}"
  have "0 \<in> Z" unfolding Z_def using g(1) h(1) by auto
  have [simp]: "closed Z"
  proof -
    have *: "Z = (\<lambda>s. dist (g s) (h s))-`{0} \<inter> {0..min (dist x y) (dist x z)}"
      unfolding Z_def by auto
    show ?thesis
      unfolding * apply (rule closed_vimage_Int)
      using continuous_on_subset[OF isometry_on_continuous[OF g(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_subset[OF isometry_on_continuous[OF h(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_dist by auto
  qed
  define a where "a = Sup Z"
  have "a \<in> Z"
    unfolding a_def apply (rule closed_contains_Sup, auto) using \<open>0 \<in> Z\<close> Z_def by auto
  define c where "c = h a"
  then have a: "g a = c" "h a = c" "a \<ge> 0" "a \<le> dist x y" "a \<le> dist x z"
    using \<open>a \<in> Z\<close> unfolding Z_def c_def by auto

  define G2 where "G2 = g`{a..dist x y}"
  have G2: "geodesic_segment_between G2 (g a) (g (dist x y))"
    unfolding G2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF g(3)] \<open>a \<in> Z\<close> unfolding Z_def by auto
  define H2 where "H2 = h`{a..dist x z}"
  have H2: "geodesic_segment_between H2 (h a) (h (dist x z))"
    unfolding H2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF h(3)] \<open>a \<in> Z\<close> unfolding Z_def by auto
  have "G2 \<inter> H2 \<subseteq> {c}"
  proof
    fix w assume w: "w \<in> G2 \<inter> H2"
    obtain sg where sg: "w = g sg" "sg \<in> {a..dist x y}" using w unfolding G2_def by auto
    obtain sh where sh: "w = h sh" "sh \<in> {a..dist x z}" using w unfolding H2_def by auto
    have "dist w x = sg"
      unfolding g(1)[symmetric] sg(1) using isometry_onD[OF g(3), of 0 sg] sg(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    moreover have "dist w x = sh"
      unfolding h(1)[symmetric] sh(1) using isometry_onD[OF h(3), of 0 sh] sh(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    ultimately have "sg = sh" by simp
    have "sh \<in> Z" unfolding Z_def using sg sh \<open>a \<ge> 0\<close> unfolding \<open>sg = sh\<close> by auto
    then have "sh \<le> a"
      unfolding a_def apply (rule cSup_upper) unfolding Z_def by auto
    then have "sh = a" using sh(2) by auto
    then show "w \<in> {c}" unfolding sh(1) using a(2) by auto
  qed
  then have *: "G2 \<inter> H2 = {c}"
    unfolding G2_def H2_def using a by (auto simp add: image_iff, force)
  have "geodesic_segment_between (G2 \<union> H2) y z"
    apply (subst g(2)[symmetric], subst h(2)[symmetric]) apply(rule geod_union[of _ _ "h a"])
    using geodesic_segment_commute G2 H2 a * by force+
  then have "G2 \<union> H2 = {y--z}"
    using geodesic_segment_unique by auto
  then have "c \<in> {y--z}" using * by auto
  then have *: "c \<in> {x--y} \<inter> {x--z} \<inter> {y--z}"
    using g(4) h(4) c_def a by force
  have center: "center x y z \<in> {x--y} \<inter> {x--z} \<inter> {y--z}"
    unfolding center_def using someI[of "\<lambda>p. p \<in> {x--y} \<inter> {x--z} \<inter> {y--z}", OF *] by blast
  have *: "dist x d = Gromov_product_at x y z" if "d \<in> {x--y} \<inter> {x--z} \<inter> {y--z}" for d
  proof -
    have "dist x y = dist x d + dist d y"
         "dist x z = dist x d + dist d z"
         "dist y z = dist y d + dist d z"
      using that by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
    then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  qed
  have "d = center x y z" if "d \<in> {x--y} \<inter> {x--z} \<inter> {y--z}" for d
    apply (rule geodesic_segment_dist_unique[of "{x--y}" x y])
    using *[OF that] *[OF center] that center by auto
  then show "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}" using center by blast
qed

lemma center_on_geodesic [simp]:
  "center x y z \<in> {x--y}"
  "center x y z \<in> {x--z}"
  "center x y z \<in> {y--z}"
  "center x y z \<in> {y--x}"
  "center x y z \<in> {z--x}"
  "center x y z \<in> {z--y}"
using center_as_intersection by (auto simp add: some_geodesic_commute)

lemma center_commute:
  "center x y z = center x z y"
  "center x y z = center y x z"
  "center x y z = center y z x"
  "center x y z = center z x y"
  "center x y z = center z y x"
using center_as_intersection some_geodesic_commute by blast+

lemma center_dist:
  "dist x (center x y z) = Gromov_product_at x y z"
proof -
  have "dist x y = dist x (center x y z) + dist (center x y z) y"
       "dist x z = dist x (center x y z) + dist (center x y z) z"
       "dist y z = dist y (center x y z) + dist (center x y z) z"
    by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
  then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
qed

lemma geodesic_intersection:
  "{x--y} \<inter> {x--z} = {x--center x y z}"
proof -
  have "{x--y} = {x--center x y z} \<union> {center x y z--y}"
    using center_as_intersection geodesic_segment_split by blast
  moreover have "{x--z} = {x--center x y z} \<union> {center x y z--z}"
    using center_as_intersection geodesic_segment_split by blast
  ultimately have "{x--y} \<inter> {x--z} = {x--center x y z} \<union> ({center x y z--y} \<inter> {x--center x y z}) \<union> ({center x y z--y} \<inter> {x--center x y z}) \<union> ({center x y z--y} \<inter> {center x y z--z})"
    by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {center x y z--z} = {center x y z}"
    using geodesic_segment_split(2)[of "center x y z" y z] center_as_intersection[of x y z] by (auto simp add: some_geodesic_commute)
  ultimately show "{x--y} \<inter> {x--z} = {x--center x y z}" by auto
qed
end (*of context metric_tree*)

text \<open>We can now prove that a metric tree is Gromov hyperbolic, for $\delta = 0$. The simplest
proof goes through the slim triangles property: it suffices to show that, given a geodesic triangle,
there is a point at distance at most $0$ of each of its sides. This is the center we have
constructed above.\<close>

class metric_tree_with_delta = metric_tree + metric_space_with_deltaG +
  assumes delta0: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0 = Gromov_hyperbolic_space +
  assumes delta0 [simp]: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0_geodesic = Gromov_hyperbolic_space_0 + geodesic_space

text \<open>Isabelle does not accept cycles in the class graph. So, we will show that
\verb+metric_tree_with_delta+ is a subclass of \verb+Gromov_hyperbolic_space_0_geodesic+, and
conversely that \verb+Gromov_hyperbolic_space_0_geodesic+ is a subclass of \verb+metric_tree+.

In a tree, we have already proved that triangles are $0$-slim (the center is common to all sides
of the triangle). The $0$-hyperbolicity follows from one of the equivalent characterizations
of hyperbolicity (the other characterizations could be used as well, but the proofs would be
less immediate.)\<close>

subclass (in metric_tree_with_delta) Gromov_hyperbolic_space_0
proof (standard)
  show "deltaG TYPE('a) = 0" unfolding delta0 by auto
  have "Gromov_hyperbolic_subset (6 * 0) (UNIV::'a set)"
  proof (rule slim_triangles_implies_hyperbolic)
    fix x::'a and y z Gxy Gyz Gxz
    define w where "w = center x y z"
    assume "geodesic_segment_between Gxy x y"
        "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z"
    then have "Gxy = {x--y}" "Gyz = {y--z}" "Gxz = {x--z}"
      by (auto simp add: local.geodesic_segment_unique)
    then have "w \<in> Gxy" "w \<in> Gyz" "w \<in> Gxz"
      unfolding w_def by auto
    then have "infdist w Gxy \<le> 0 \<and> infdist w Gxz \<le> 0 \<and> infdist w Gyz \<le> 0"
      by auto
    then show "\<exists>w. infdist w Gxy \<le> 0 \<and> infdist w Gxz \<le> 0 \<and> infdist w Gyz \<le> 0"
      by blast
  qed
  then show "Gromov_hyperbolic_subset (deltaG TYPE('a)) (UNIV::'a set)" unfolding delta0 by auto
qed

text \<open>To use the fact that reals are Gromov hyperbolic, given that they are a metric tree,
we need to instantiate them as \verb+metric_tree_with_delta+.\<close>

instantiation real::metric_tree_with_delta
begin
definition deltaG_real::"real itself \<Rightarrow> real"
  where "deltaG_real _ = 0"
instance apply standard unfolding deltaG_real_def by auto
end

text \<open>Let us now prove the converse: a geodesic space which is $\delta$-hyperbolic for $\delta = 0$
is a metric tree. For the proof, we consider two geodesic segments $G = [x,y]$ and $H = [y,z]$ with a common
endpoint, and we have to show that their union is still a geodesic segment from $x$ to $z$. For
this, introduce a geodesic segment $L = [x,z]$. By the property of thin triangles, $G$ is included
in $H \cup L$. In particular, a point $Y$ close to $y$ but different from $y$ on $G$ is on $L$,
and therefore realizes the equality $d(x,z) = d(x, Y) + d(Y, z)$. Passing to the limit, $y$
also satisfies this equality. The conclusion readily follows thanks to Lemma
\verb+geodesic_segment_union+.
\<close>

subclass (in Gromov_hyperbolic_space_0_geodesic) metric_tree
proof
  fix G H x y z assume A: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y::'a}"
  show "geodesic_segment_between (G \<union> H) x z"
  proof (cases "x = y")
    case True
    then show ?thesis
      by (metis A Un_commute geodesic_segment_between_x_x(3) inf.commute sup_inf_absorb)
  next
    case False
    define D::"nat \<Rightarrow> real" where "D = (\<lambda>n. dist x y - (dist x y) * (1/(real(n+1))))"
    have D: "D n \<in> {0..< dist x y}" "D n \<in> {0..dist x y}" for n
      unfolding D_def by (auto simp add: False divide_simps algebra_simps)
    have Dlim: "D \<longlonglongrightarrow> dist x y - dist x y * 0"
      unfolding D_def by (intro tendsto_intros LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1])

    define Y::"nat \<Rightarrow> 'a" where "Y = (\<lambda>n. geodesic_segment_param G x (D n))"
    have *: "Y \<longlonglongrightarrow> y"
      unfolding Y_def apply (subst geodesic_segment_param(2)[OF A(1), symmetric])
      using isometry_on_continuous[OF geodesic_segment_param(4)[OF A(1)]]
      unfolding continuous_on_sequentially comp_def using D(2) Dlim by auto

    have "dist x z = dist x (Y n) + dist (Y n) z" for n
    proof -
      obtain L where L: "geodesic_segment_between L x z" using geodesic_subsetD[OF geodesic] by blast
      have "Y n \<in> G" unfolding Y_def
        apply (rule geodesic_segment_param(3)[OF A(1)]) using D[of n] by auto
      have "dist x (Y n) = D n"
        unfolding Y_def apply (rule geodesic_segment_param[OF A(1)]) using D[of n] by auto
      then have "Y n \<noteq> y"
        using D[of n] by auto
      then have "Y n \<notin> H" using A(3) \<open>Y n \<in> G\<close> by auto
      have "infdist (Y n) (H \<union> L) \<le> 4 * deltaG(TYPE('a))"
        apply (rule thin_triangles[OF geodesic_segment_commute[OF A(2)] geodesic_segment_commute[OF L] geodesic_segment_commute[OF A(1)]])
        using \<open>Y n \<in> G\<close> by simp
      then have "infdist (Y n) (H \<union> L) = 0"
        using infdist_nonneg[of "Y n" "H \<union> L"] unfolding delta0 by auto
      have "Y n \<in> H \<union> L"
      proof (subst in_closed_iff_infdist_zero)
        have "closed H"
          using A(2) geodesic_segment_topology geodesic_segment_def by fastforce
        moreover have "closed L"
          using L geodesic_segment_topology geodesic_segment_def by fastforce
        ultimately show "closed (H \<union> L)" by auto
        show "H \<union> L \<noteq> {}" using A(2) geodesic_segment_endpoints(1) by auto
      qed (fact)
      then have "Y n \<in> L" using \<open>Y n \<notin> H\<close> by simp
      show ?thesis using geodesic_segment_dist[OF L \<open>Y n \<in> L\<close>] by simp
    qed
    moreover have "(\<lambda>n. dist x (Y n) + dist (Y n) z) \<longlonglongrightarrow> dist x y + dist y z"
      by (intro tendsto_intros *)
    ultimately have "(\<lambda>n. dist x z) \<longlonglongrightarrow> dist x y + dist y z"
      using filterlim_cong eventually_sequentially by auto
    then have *: "dist x z = dist x y + dist y z"
      using LIMSEQ_unique by auto
    show "geodesic_segment_between (G \<union> H) x z"
      by (rule geodesic_segment_union[OF * A(1) A(2)])
  qed
qed

end (*of theory Gromov_Hyperbolic*)
