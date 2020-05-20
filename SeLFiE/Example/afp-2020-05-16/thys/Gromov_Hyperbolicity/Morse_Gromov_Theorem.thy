(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)


theory Morse_Gromov_Theorem
  imports "HOL-Decision_Procs.Approximation" Gromov_Hyperbolicity Hausdorff_Distance
begin

hide_const (open) Approximation.Min
hide_const (open) Approximation.Max

section \<open>Quasiconvexity\<close>

text \<open>In a Gromov-hyperbolic setting, convexity is not a well-defined notion as everything should
be coarse. The good replacement is quasi-convexity: A set $X$ is $C$-quasi-convex if any pair of
points in $X$ can be joined by a geodesic that remains within distance $C$ of $X$. One could also
require this for all geodesics, up to changing $C$, as two geodesics between the same endpoints
remain within uniformly bounded distance. We use the first definition to ensure that a geodesic is
$0$-quasi-convex.\<close>

definition quasiconvex::"real \<Rightarrow> ('a::metric_space) set \<Rightarrow> bool"
  where "quasiconvex C X = (C \<ge> 0 \<and> (\<forall>x\<in>X. \<forall>y\<in>X. \<exists>G. geodesic_segment_between G x y \<and> (\<forall>z\<in>G. infdist z X \<le> C)))"

lemma quasiconvexD:
  assumes "quasiconvex C X" "x \<in> X" "y \<in> X"
  shows "\<exists>G. geodesic_segment_between G x y \<and> (\<forall>z\<in>G. infdist z X \<le> C)"
using assms unfolding quasiconvex_def by auto

lemma quasiconvexC:
  assumes "quasiconvex C X"
  shows "C \<ge> 0"
using assms unfolding quasiconvex_def by auto

lemma quasiconvexI:
  assumes "C \<ge> 0"
          "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> (\<exists>G. geodesic_segment_between G x y \<and> (\<forall>z\<in>G. infdist z X \<le> C))"
  shows "quasiconvex C X"
using assms unfolding quasiconvex_def by auto

lemma quasiconvex_of_geodesic:
  assumes "geodesic_segment G"
  shows "quasiconvex 0 G"
proof (rule quasiconvexI, simp)
  fix x y assume *: "x \<in> G" "y \<in> G"
  obtain H where H: "H \<subseteq> G" "geodesic_segment_between H x y"
    using geodesic_subsegment_exists[OF assms(1) *] by auto
  have "infdist z G \<le> 0" if "z \<in> H" for z
    using H(1) that by auto
  then show "\<exists>H. geodesic_segment_between H x y \<and> (\<forall>z\<in>H. infdist z G \<le> 0)"
    using H(2) by auto
qed

lemma quasiconvex_empty:
  assumes "C \<ge> 0"
  shows "quasiconvex C {}"
unfolding quasiconvex_def using assms by auto

lemma quasiconvex_mono:
  assumes "C \<le> D"
          "quasiconvex C G"
  shows "quasiconvex D G"
using assms unfolding quasiconvex_def by (auto, fastforce)

text \<open>The $r$-neighborhood of a quasi-convex set is still quasi-convex in a hyperbolic space,
for a constant that does not depend on $r$.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) quasiconvex_thickening:
  assumes "quasiconvex C (X::'a set)" "r \<ge> 0"
  shows "quasiconvex (C + 8 *deltaG(TYPE('a))) (\<Union>x\<in>X. cball x r)"
proof (rule quasiconvexI)
  show "C + 8 *deltaG(TYPE('a)) \<ge> 0" using quasiconvexC[OF assms(1)] by simp
next
  fix y z assume *: "y \<in> (\<Union>x\<in>X. cball x r)" "z \<in> (\<Union>x\<in>X. cball x r)"
  have A: "infdist w (\<Union>x\<in>X. cball x r) \<le> C + 8 * deltaG TYPE('a)" if "w \<in> {y--z}" for w
  proof -
    obtain py where py: "py \<in> X" "y \<in> cball py r"
      using * by auto
    obtain pz where pz: "pz \<in> X" "z \<in> cball pz r"
      using * by auto
    obtain G where G: "geodesic_segment_between G py pz" "(\<forall>p\<in>G. infdist p X \<le> C)"
      using quasiconvexD[OF assms(1) \<open>py \<in> X\<close> \<open>pz \<in> X\<close>] by auto
    have A: "infdist w ({y--py} \<union> G \<union> {pz--z}) \<le> 8 * deltaG(TYPE('a))"
      by (rule thin_quadrilaterals[OF _ G(1) _ _ \<open>w \<in> {y--z}\<close>, where ?x = y and ?t = z], auto)
    have "\<exists>u \<in> {y--py} \<union> G \<union> {pz--z}. infdist w ({y--py} \<union> G \<union> {pz--z}) = dist w u"
      apply (rule infdist_proper_attained, auto intro!: proper_Un simp add: geodesic_segment_topology(7))
      by (meson G(1) geodesic_segmentI geodesic_segment_topology(7))
    then obtain u where u: "u \<in> {y--py} \<union> G \<union> {pz--z}" "infdist w ({y--py} \<union> G \<union> {pz--z}) = dist w u"
      by auto
    then consider "u \<in> {y--py}" | "u \<in> G" | "u \<in> {pz--z}" by auto
    then have "infdist u (\<Union>x\<in>X. cball x r) \<le> C"
    proof (cases)
      case 1
      then have "dist py u \<le> dist py y"
        using geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_commute some_geodesic_endpoints(1) by blast
      also have "... \<le> r"
        using py(2) by auto
      finally have "u \<in> cball py r"
        by auto
      then have "u \<in> (\<Union>x\<in>X. cball x r)"
        using py(1) by auto
      then have "infdist u (\<Union>x\<in>X. cball x r) = 0"
        by auto
      then show ?thesis
        using quasiconvexC[OF assms(1)] by auto
    next
      case 3
      then have "dist pz u \<le> dist pz z"
        using geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_commute some_geodesic_endpoints(1) by blast
      also have "... \<le> r"
        using pz(2) by auto
      finally have "u \<in> cball pz r"
        by auto
      then have "u \<in> (\<Union>x\<in>X. cball x r)"
        using pz(1) by auto
      then have "infdist u (\<Union>x\<in>X. cball x r) = 0"
        by auto
      then show ?thesis
        using quasiconvexC[OF assms(1)] by auto
    next
      case 2
      have "infdist u (\<Union>x\<in>X. cball x r) \<le> infdist u X"
        apply (rule infdist_mono) using assms(2) py(1) by auto
      then show ?thesis using 2 G(2) by auto
    qed
    moreover have "infdist w (\<Union>x\<in>X. cball x r) \<le> infdist u (\<Union>x\<in>X. cball x r) + dist w u"
      by (intro mono_intros)
    ultimately show ?thesis
      using A u(2) by auto
  qed
  show "\<exists>G. geodesic_segment_between G y z \<and> (\<forall>w\<in>G. infdist w (\<Union>x\<in>X. cball x r) \<le> C + 8 * deltaG TYPE('a))"
    apply (rule exI[of _ "{y--z}"]) using A by auto
qed

text \<open>If $x$ has a projection $p$ on a quasi-convex set $G$, then all segments from a point in $G$
to $x$ go close to $p$, i.e., the triangular inequality $d(x,y) \leq d(x,p) + d(p,y)$ is essentially
an equality, up to an additive constant.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) dist_along_quasiconvex:
  assumes "quasiconvex C G" "p \<in> proj_set x G" "y \<in> G"
  shows "dist x p + dist p y \<le> dist x y + 4 * deltaG(TYPE('a)) + 2 * C"
proof -
  have *: "p \<in> G"
    using assms proj_setD by auto
  obtain H where H: "geodesic_segment_between H p y" "\<And>q. q \<in> H \<Longrightarrow> infdist q G \<le> C"
    using quasiconvexD[OF assms(1) * assms(3)] by auto
  have "\<exists>m\<in>H. infdist x H = dist x m"
    apply (rule infdist_proper_attained[of H x]) using geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto
  then obtain m where m: "m \<in> H" "infdist x H = dist x m" by auto
  then have I: "dist x m \<le> Gromov_product_at x p y + 2 * deltaG(TYPE('a))"
    using infdist_triangle_side[OF H(1), of x] by auto
  have "dist x p - dist x m - C \<le> e" if "e > 0" for e
  proof -
    have "\<exists>r\<in>G. dist m r < infdist m G + e"
      apply (rule infdist_almost_attained) using \<open>e > 0\<close> assms(3) by auto
    then obtain r where r: "r \<in> G" "dist m r < infdist m G + e"
      by auto
    then have *: "dist m r \<le> C + e" using H(2)[OF \<open>m \<in> H\<close>] by auto
    have "dist x p \<le> dist x r"
      using \<open>r \<in> G\<close> assms(2) proj_set_dist_le by blast
    also have "... \<le> dist x m + dist m r"
      by (intro mono_intros)
    finally show ?thesis using * by (auto simp add: metric_space_class.dist_commute)
  qed
  then have "dist x p - dist x m - C \<le> 0"
    using dense_ge by blast
  then show ?thesis
    using I unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
qed

text \<open>The next lemma is~\cite[Proposition 10.2.1]{coornaert_delzant_papadopoulos} with better
constants. It states that the distance between the projections
on a quasi-convex set is controlled by the distance of the original points, with a gain given by the
distances of the points to the set.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) proj_along_quasiconvex_contraction:
  assumes "quasiconvex C G" "px \<in> proj_set x G" "py \<in> proj_set y G"
  shows "dist px py \<le> max (5 * deltaG(TYPE('a)) + 2 * C) (dist x y - dist px x - dist py y + 10 * deltaG(TYPE('a)) + 4 * C)"
proof -
  have "px \<in> G" "py \<in> G"
    using assms proj_setD by auto
  have "(dist x px + dist px py - 4 * deltaG(TYPE('a)) - 2 * C) + (dist y py + dist py px - 4 *deltaG(TYPE('a)) - 2 * C)
        \<le> dist x py + dist y px"
    apply (intro mono_intros)
    using dist_along_quasiconvex[OF assms(1) assms(2) \<open>py \<in> G\<close>] dist_along_quasiconvex[OF assms(1) assms(3) \<open>px \<in> G\<close>] by auto
  also have "... \<le> max (dist x y + dist py px) (dist x px + dist py y) + 2 * deltaG(TYPE('a))"
    by (rule hyperb_quad_ineq)
  finally have *: "dist x px + dist y py + 2 * dist px py
          \<le> max (dist x y + dist py px) (dist x px + dist py y) + 10 * deltaG(TYPE('a)) + 4 * C"
    by (auto simp add: metric_space_class.dist_commute)
  show ?thesis
  proof (cases "dist x y + dist py px \<ge> dist x px + dist py y")
    case True
    then have "dist x px + dist y py + 2 * dist px py \<le> dist x y + dist py px + 10 * deltaG(TYPE('a)) + 4 * C"
      using * by auto
    then show ?thesis by (auto simp add: metric_space_class.dist_commute)
  next
    case False
    then have "dist x px + dist y py + 2 * dist px py \<le> dist x px + dist py y + 10 * deltaG(TYPE('a)) + 4 * C"
      using * by auto
    then show ?thesis by (simp add: metric_space_class.dist_commute)
  qed
qed

text \<open>The projection on a quasi-convex set is $1$-Lipschitz up to an additive error.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) proj_along_quasiconvex_contraction':
  assumes "quasiconvex C G" "px \<in> proj_set x G" "py \<in> proj_set y G"
  shows "dist px py \<le> dist x y + 4 * deltaG(TYPE('a)) + 2 * C"
proof (cases "dist y py \<le> dist x px")
  case True
  have "dist x px + dist px py \<le> dist x py + 4 * deltaG(TYPE('a)) + 2 * C"
    by (rule dist_along_quasiconvex[OF assms(1) assms(2) proj_setD(1)[OF assms(3)]])
  also have "... \<le> (dist x y + dist y py) + 4 * deltaG(TYPE('a)) + 2 * C"
    by (intro mono_intros)
  finally show ?thesis using True by auto
next
  case False
  have "dist y py + dist py px \<le> dist y px + 4 * deltaG(TYPE('a)) + 2 * C"
    by (rule dist_along_quasiconvex[OF assms(1) assms(3) proj_setD(1)[OF assms(2)]])
  also have "... \<le> (dist y x + dist x px) + 4 * deltaG(TYPE('a)) + 2 * C"
    by (intro mono_intros)
  finally show ?thesis using False by (auto simp add: metric_space_class.dist_commute)
qed

text \<open>We can in particular specialize the previous statements to geodesics, which are
$0$-quasi-convex.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) dist_along_geodesic:
  assumes "geodesic_segment G" "p \<in> proj_set x G" "y \<in> G"
  shows "dist x p + dist p y \<le> dist x y + 4 * deltaG(TYPE('a))"
using dist_along_quasiconvex[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

lemma (in Gromov_hyperbolic_space_geodesic) proj_along_geodesic_contraction:
  assumes "geodesic_segment G" "px \<in> proj_set x G" "py \<in> proj_set y G"
  shows "dist px py \<le> max (5 * deltaG(TYPE('a))) (dist x y - dist px x - dist py y + 10 * deltaG(TYPE('a)))"
using proj_along_quasiconvex_contraction[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

lemma (in Gromov_hyperbolic_space_geodesic) proj_along_geodesic_contraction':
  assumes "geodesic_segment G" "px \<in> proj_set x G" "py \<in> proj_set y G"
  shows "dist px py \<le> dist x y + 4 * deltaG(TYPE('a))"
using proj_along_quasiconvex_contraction'[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

text \<open>If one projects a continuous curve on a quasi-convex set, the image does not have to be
connected (the projection is discontinuous), but since the projections of nearby points are within
uniformly bounded distance one can find in the projection a point with almost prescribed distance
to the starting point, say. For further applications, we also pick the first such point, i.e.,
all the previous points are also close to the starting point.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) quasi_convex_projection_small_gaps:
  assumes "continuous_on {a..(b::real)} f"
          "a \<le> b"
          "quasiconvex C G"
          "\<And>t. t \<in> {a..b} \<Longrightarrow> p t \<in> proj_set (f t) G"
          "delta > deltaG(TYPE('a))"
          "d \<in> {4 * delta + 2 * C..dist (p a) (p b)}"
  shows "\<exists>t \<in> {a..b}. (dist (p a) (p t) \<in> {d - 4 * delta - 2 * C .. d})
                    \<and> (\<forall>s \<in> {a..t}. dist (p a) (p s) \<le> d)"
proof -
  have "delta > 0"
    using assms(5) local.delta_nonneg by linarith
  moreover have "C \<ge> 0"
    using quasiconvexC[OF assms(3)] by simp
  ultimately have "d \<ge> 0" using assms by auto

  text \<open>The idea is to define the desired point as the last point $u$ for which there is a projection
  at distance at most $d$ of the starting point. Then the projection can not be much closer to
  the starting point, or one could point another such point further away by almost continuity, giving
  a contradiction. The technical implementation requires some care, as the "last point" may not
  satisfy the property, for lack of continuity. If it does, then fine. Otherwise, one should go just
  a little bit to its left to find the desired point.\<close>
  define I where "I = {t \<in> {a..b}. \<forall>s \<in> {a..t}. dist (p a) (p s) \<le> d}"
  have "a \<in> I"
    using \<open>a \<le> b\<close> \<open>d \<ge> 0\<close> unfolding I_def by auto
  have "bdd_above I"
    unfolding I_def by auto
  define u where "u = Sup I"
  have "a \<le> u"
    unfolding u_def apply (rule cSup_upper) using \<open>a \<in> I\<close> \<open>bdd_above I\<close> by auto
  have "u \<le> b"
    unfolding u_def apply (rule cSup_least) using \<open>a \<in> I\<close> apply auto unfolding I_def by auto
  have A: "dist (p a) (p s) \<le> d" if "s < u" "a \<le> s" for s
  proof -
    have "\<exists>t\<in>I. s < t"
      unfolding u_def apply (subst less_cSup_iff[symmetric])
      using \<open>a \<in> I\<close> \<open>bdd_above I\<close> using \<open>s < u\<close> unfolding u_def by auto
    then obtain t where t: "t \<in> I" "s < t" by auto
    then have "s \<in> {a..t}" using \<open>a \<le> s\<close> by auto
    then show ?thesis
      using t(1) unfolding I_def by auto
  qed
  have "continuous (at u within {a..b}) f"
    using assms(1) by (simp add: \<open>a \<le> u\<close> \<open>u \<le> b\<close> continuous_on_eq_continuous_within)
  then have "\<exists>i > 0. \<forall>s\<in>{a..b}. dist u s < i \<longrightarrow> dist (f u) (f s) < (delta - deltaG(TYPE('a)))"
    unfolding continuous_within_eps_delta using \<open>deltaG(TYPE('a)) < delta\<close> by (auto simp add: metric_space_class.dist_commute)
  then obtain e0 where e0: "e0 > 0" "\<And>s. s \<in> {a..b} \<Longrightarrow> dist u s < e0 \<Longrightarrow> dist (f u) (f s) < (delta - deltaG(TYPE('a)))"
    by auto

  show ?thesis
  proof (cases "dist (p a) (p u) > d")
    text \<open>First, consider the case where $u$ does not satisfy the defining property. Then the
    desired point $t$ is taken slightly to its left.\<close>
    case True
    then have "u \<noteq> a"
      using \<open>d \<ge> 0\<close> by auto
    then have "a < u" using \<open>a \<le> u\<close> by auto

    define e::real where "e = min (e0/2) ((u-a)/2)"
    then have "e > 0" using \<open>a < u\<close> \<open>e0 > 0\<close> by auto
    define t where "t = u - e"
    then have "t < u" using \<open>e > 0\<close> by auto
    have "u - b \<le> e" "e \<le> u - a"
      using \<open>e > 0\<close> \<open>u \<le> b\<close> unfolding e_def by (auto simp add: min_def)
    then have "t \<in> {a..b}" "t \<in> {a..t}"
      unfolding t_def by auto
    have "dist u t < e0"
      unfolding t_def e_def dist_real_def using \<open>e0 > 0\<close> \<open>a \<le> u\<close> by auto
    have *: "\<forall>s \<in> {a..t}. dist (p a) (p s) \<le> d"
      using A \<open>t < u\<close> by auto
    have "dist (p t) (p u) \<le> dist (f t) (f u) + 4 * deltaG(TYPE('a)) + 2 * C"
      apply (rule proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
      using assms (4) \<open>t \<in> {a..b}\<close> \<open>a \<le> u\<close> \<open>u \<le> b\<close> by auto
    also have "... \<le> (delta - deltaG(TYPE('a))) + 4 * deltaG(TYPE('a)) + 2 * C"
      apply (intro mono_intros)
      using e0(2)[OF \<open>t \<in> {a..b}\<close> \<open>dist u t < e0\<close>] by (auto simp add: metric_space_class.dist_commute)
    finally have I: "dist (p t) (p u) \<le> 4 * delta + 2 * C"
      using \<open>delta > deltaG(TYPE('a))\<close> by simp

    have "d \<le> dist (p a) (p u)"
      using True by auto
    also have "... \<le> dist (p a) (p t) + dist (p t) (p u)"
      by (intro mono_intros)
    also have "... \<le> dist (p a) (p t) + 4 * delta + 2 * C"
      using I by simp
    finally have **: "d - 4 * delta - 2 * C \<le> dist (p a) (p t)"
      by simp
    show ?thesis
      apply (rule bexI[OF _ \<open>t \<in> {a..b}\<close>]) using * ** \<open>t \<in> {a..b}\<close> by auto
  next
    text \<open>Next, consider the case where $u$ satisfies the defining property. Then we will take $t = u$.
    The only nontrivial point to check is that the distance of $f(u)$ to the starting point is not
    too small. For this, we need to separate the case where $u = b$ (in which case one argues directly)
    and the case where $u < b$, where one can use a point slightly to the right of $u$ which has a
    projection at distance $ > d$ of the starting point, and use almost continuity.\<close>
    case False
    have B: "dist (p a) (p s) \<le> d" if "s \<in> {a..u}" for s
    proof (cases "s = u")
      case True
      show ?thesis
        unfolding True using False by auto
    next
      case False
      then show ?thesis
        using that A by auto
    qed
    have C: "dist (p a) (p u) \<ge> d - 4 *delta - 2 * C"
    proof (cases "u = b")
      case True
      have "d \<le> dist (p a) (p b)"
        using assms by auto
      also have "... \<le> dist (p a) (p u) + dist (p u) (p b)"
        by (intro mono_intros)
      also have "... \<le> dist (p a) (p u) + (dist (f u) (f b) + 4 * deltaG TYPE('a) + 2 * C)"
        apply (intro mono_intros proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
        using assms \<open>a \<le> u\<close> \<open>u \<le> b\<close> by auto
      finally show ?thesis
        unfolding True using \<open>deltaG(TYPE('a)) < delta\<close> by auto
    next
      case False
      then have "u < b"
        using \<open>u \<le> b\<close> by auto
      define e::real where "e = min (e0/2) ((b-u)/2)"
      then have "e > 0" using \<open>u < b\<close> \<open>e0 > 0\<close> by auto
      define v where "v = u + e"
      then have "u < v"
        using \<open>e > 0\<close> by auto
      have "e \<le> b - u" "a - u \<le> e"
        using \<open>e > 0\<close> \<open>a \<le> u\<close> unfolding e_def by (auto simp add: min_def)
      then have "v \<in> {a..b}"
        unfolding v_def by auto
      moreover have "v \<notin> I"
        using \<open>u < v\<close> \<open>bdd_above I\<close> cSup_upper not_le unfolding u_def by auto
      ultimately have "\<exists>w \<in> {a..v}. dist (p a) (p w) > d"
        unfolding I_def by force
      then obtain w where w: "w \<in> {a..v}" "dist (p a) (p w) > d"
        by auto
      then have "w \<notin> {a..u}"
        using B by force
      then have "u < w"
        using w(1) by auto
      have "w \<in> {a..b}"
        using w(1) \<open>v \<in> {a..b}\<close> by auto
      have "dist u w = w - u"
        unfolding dist_real_def using \<open>u < w\<close> by auto
      also have "... \<le> v - u"
        using w(1) by auto
      also have "... < e0"
        unfolding v_def e_def min_def using \<open>e0 > 0\<close> by auto
      finally have "dist u w < e0" by simp
      have "dist (p u) (p w) \<le> dist (f u) (f w) + 4 * deltaG(TYPE('a)) + 2 * C"
        apply (rule proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
        using assms \<open>a \<le> u\<close> \<open>u \<le> b\<close> \<open>w \<in> {a..b}\<close> by auto
      also have "... \<le> (delta - deltaG(TYPE('a))) + 4 * deltaG(TYPE('a)) + 2 * C"
        apply (intro mono_intros)
        using e0(2)[OF \<open>w \<in> {a..b}\<close> \<open>dist u w < e0\<close>] by (auto simp add: metric_space_class.dist_commute)
      finally have I: "dist (p u) (p w) \<le> 4 * delta + 2 * C"
        using \<open>delta > deltaG(TYPE('a))\<close> by simp
      have "d \<le> dist (p a) (p u) + dist (p u) (p w)"
        using w(2) metric_space_class.dist_triangle[of "p a" "p w" "p u"] by auto
      also have "... \<le> dist (p a) (p u) + 4 * delta + 2 * C"
        using I by auto
      finally show ?thesis by simp
    qed
    show ?thesis
      apply (rule bexI[of _ u])
      using B \<open>a \<le> u\<close> \<open>u \<le> b\<close> C by auto
  qed
qed

text \<open>Same lemma, except that one exchanges the roles of the beginning and the end point.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) quasi_convex_projection_small_gaps':
  assumes "continuous_on {a..(b::real)} f"
          "a \<le> b"
          "quasiconvex C G"
          "\<And>x. x \<in> {a..b} \<Longrightarrow> p x \<in> proj_set (f x) G"
          "delta > deltaG(TYPE('a))"
          "d \<in> {4 * delta + 2 * C..dist (p a) (p b)}"
  shows "\<exists>t \<in> {a..b}. dist (p b) (p t) \<in> {d - 4 * delta - 2 * C .. d}
                    \<and> (\<forall>s \<in> {t..b}. dist (p b) (p s) \<le> d)"
proof -
  have *: "continuous_on {-b..-a} (\<lambda>t. f(-t))"
    using continuous_on_compose[of "{-b..-a}" "\<lambda>t. -t" f] using assms(1) continuous_on_minus[OF continuous_on_id] by auto
  define q where "q = (\<lambda>t. p(-t))"
  have "\<exists>t \<in> {-b..-a}. (dist (q (-b)) (q t) \<in> {d - 4 * delta - 2 * C .. d})
                    \<and> (\<forall>s \<in> {-b..t}. dist (q (-b)) (q s) \<le> d)"
    apply (rule quasi_convex_projection_small_gaps[where ?f = "\<lambda>t. f(-t)" and ?G = G])
    unfolding q_def using assms * by (auto simp add: metric_space_class.dist_commute)
  then obtain t where t: "t \<in> {-b..-a}" "dist (q (-b)) (q t) \<in> {d - 4 * delta - 2 * C .. d}"
                      "\<And>s. s \<in> {-b..t} \<Longrightarrow> dist (q (-b)) (q s) \<le> d"
    by blast
  have *: "dist (p b) (p s) \<le> d" if "s \<in> {-t..b}" for s
    using t(3)[of "-s"] that q_def by auto
  show ?thesis
    apply (rule bexI[of _ "-t"]) using t * q_def by auto
qed

section \<open>The Morse-Gromov Theorem\<close>

text \<open>The goal of this section is to prove a central basic result in the theory of hyperbolic spaces,
usually called the Morse Lemma. It is really
a theorem, and we add the name Gromov the avoid the confusion with the other Morse lemma
on the existence of good coordinates for $C^2$ functions with non-vanishing hessian.

It states that a quasi-geodesic remains within bounded distance of a geodesic with the same
endpoints, the error depending only on $\delta$ and on the parameters $(\lambda, C)$ of the
quasi-geodesic, but not on its length.

There are several proofs of this result. We will follow the one of Shchur~\cite{shchur}, which
gets an optimal dependency in terms of the parameters of the quasi-isometry, contrary to all
previous proofs. The price to pay is that the proof is more involved (relying in particular on
the fact that the closest point projection on quasi-convex sets is exponentially contracting).

We will also give afterwards for completeness the proof in~\cite{bridson_haefliger}, as it brings
up interesting tools, although the dependency it gives is worse.\<close>

text \<open>The next lemma (for $C = 0$, Lemma 2 in~\cite{shchur}) asserts that, if two points are not too far apart (at distance at most
$10 \delta$), and far enough from a given geodesic segment, then when one moves towards this
geodesic segment by a fixed amount (here $5 \delta$), then the two points become closer (the new
distance is at most $5 \delta$, gaining a factor of $2$). Later, we will iterate this lemma to
show that the projection on a geodesic segment is exponentially contracting. For the application,
we give a more general version involving an additional constant $C$.

This lemma holds for $\delta$ the hyperbolicity constant. We will want to apply it with $\delta > 0$,
so to avoid problems in the case $\delta = 0$ we formulate it not using the hyperbolicity constant of
the given type, but any constant which is at least the hyperbolicity constant (this is to work
around the fact that one can not say or use easily in Isabelle that a type with hyperbolicity
$\delta$ is also hyperbolic for any larger constant $\delta'$.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) geodesic_projection_exp_contracting_aux:
  assumes "geodesic_segment G"
          "px \<in> proj_set x G"
          "py \<in> proj_set y G"
          "delta \<ge> deltaG(TYPE('a))"
          "dist x y \<le> 10 * delta + C"
          "M \<ge> 15/2 * delta"
          "dist px x \<ge> M + 5 * delta + C/2"
          "dist py y \<ge> M + 5 * delta + C/2"
          "C \<ge> 0"
  shows "dist (geodesic_segment_param {px--x} px M)
              (geodesic_segment_param {py--y} py M) \<le> 5 * delta"
proof -
  have "dist px x \<le> dist py x"
    using proj_setD(2)[OF assms(2)] infdist_le[OF proj_setD(1)[OF assms(3)], of x] by (simp add: metric_space_class.dist_commute)
  have "dist py y \<le> dist px y"
    using proj_setD(2)[OF assms(3)] infdist_le[OF proj_setD(1)[OF assms(2)], of y] by (simp add: metric_space_class.dist_commute)

  have "delta \<ge> 0"
    using assms local.delta_nonneg by linarith
  then have M: "M \<ge> 0" "M \<le> dist px x" "M \<le> dist px y" "M \<le> dist py x" "M \<le> dist py y"
    using assms \<open>dist px x \<le> dist py x\<close> \<open>dist py y \<le> dist px y \<close>by auto
  have "px \<in> G" "py \<in> G"
    using assms proj_setD by auto

  define x' where "x' = geodesic_segment_param {px--x} px M"
  define y' where "y' = geodesic_segment_param {py--y} py M"

  text \<open>First step: the distance between $px$ and $py$ is at most $5\delta$.\<close>
  have "dist px py \<le> max (5 * deltaG(TYPE('a))) (dist x y - dist px x - dist py y + 10 * deltaG(TYPE('a)))"
    by (rule proj_along_geodesic_contraction[OF assms(1) assms(2) assms(3)])
  also have "... \<le> max (5 * deltaG(TYPE('a))) (5 * deltaG(TYPE('a)))"
    apply (intro mono_intros) using assms \<open>delta \<ge> 0\<close> by auto
  finally have "dist px py \<le> 5 * delta"
    using \<open>delta \<ge> deltaG(TYPE('a))\<close> by auto

  text \<open>Second step: show that all the interesting Gromov products at bounded below by $M$.\<close>
  have *: "x' \<in> {px--x}" unfolding x'_def
    by (simp add: geodesic_segment_param_in_segment)
  have "px \<in> proj_set x' G"
    by (rule proj_set_geodesic_same_basepoint[OF \<open>px \<in> proj_set x G\<close> _ *], auto)
  have "dist px x' = M"
    unfolding x'_def using M by auto
  have "dist px x' \<le> dist py x'"
    using proj_setD(2)[OF \<open>px \<in> proj_set x' G\<close>] infdist_le[OF proj_setD(1)[OF assms(3)], of x'] by (simp add: metric_space_class.dist_commute)
  have **: "dist px x = dist px x' + dist x' x"
    using geodesic_segment_dist[OF _ *, of px x] by auto
  have Ixx: "Gromov_product_at px x' x = M"
    unfolding Gromov_product_at_def ** x'_def using M by auto
  have "2 * M = dist px x' + dist px x - dist x' x"
    unfolding ** x'_def using M by auto
  also have "... \<le> dist py x' + dist py x - dist x' x"
    apply (intro mono_intros, auto) by fact+
  also have "... = 2 * Gromov_product_at py x x'"
    unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  finally have Iyx: "Gromov_product_at py x x' \<ge> M" by auto

  have *: "y' \<in> {py--y}" unfolding y'_def
    by (simp add: geodesic_segment_param_in_segment)
  have "py \<in> proj_set y' G"
    by (rule proj_set_geodesic_same_basepoint[OF \<open>py \<in> proj_set y G\<close> _ *], auto)
  have "dist py y' = M"
    unfolding y'_def using M by auto
  have "dist py y' \<le> dist px y'"
    using proj_setD(2)[OF \<open>py \<in> proj_set y' G\<close>] infdist_le[OF proj_setD(1)[OF assms(2)], of y'] by (simp add: metric_space_class.dist_commute)
  have **: "dist py y = dist py y' + dist y' y"
    using geodesic_segment_dist[OF _ *, of py y] by auto
  have Iyy: "Gromov_product_at py y' y = M"
    unfolding Gromov_product_at_def ** y'_def using M by auto
  have "2 * M = dist py y' + dist py y - dist y' y"
    unfolding ** y'_def using M by auto
  also have "... \<le> dist px y' + dist px y - dist y' y"
    apply (intro mono_intros, auto) by fact+
  also have "... = 2 * Gromov_product_at px y y'"
    unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  finally have Ixy: "Gromov_product_at px y y' \<ge> M" by auto

  have "2 * M \<le> dist px x + dist py y - dist x y"
    using assms by auto
  also have "... \<le> dist px x + dist px y - dist x y"
    by (intro mono_intros, fact)
  also have "... = 2 * Gromov_product_at px x y"
    unfolding Gromov_product_at_def by auto
  finally have Ix: "Gromov_product_at px x y \<ge> M"
    by auto
  have "2 * M \<le> dist px x + dist py y - dist x y"
    using assms by auto
  also have "... \<le> dist py x + dist py y - dist x y"
    by (intro mono_intros, fact)
  also have "... = 2 * Gromov_product_at py x y"
    unfolding Gromov_product_at_def by auto
  finally have Iy: "Gromov_product_at py x y \<ge> M"
    by auto

  text \<open>Third step: prove the estimate\<close>
  have "M - 2 * delta \<le> Min {Gromov_product_at px x' x, Gromov_product_at px x y, Gromov_product_at px y y'} - 2 * deltaG(TYPE('a))"
    using Ixx Ixy Ix \<open>delta \<ge> deltaG(TYPE('a))\<close> by auto
  also have "... \<le> Gromov_product_at px x' y'"
    by (intro mono_intros)
  finally have A: "M - 4 * delta + dist x' y' \<le> dist px y'"
    unfolding Gromov_product_at_def \<open>dist px x' = M\<close> by auto

  have "M - 2 * delta \<le> Min {Gromov_product_at py x' x, Gromov_product_at py x y, Gromov_product_at py y y'} - 2 * deltaG(TYPE('a))"
    using Iyx Iyy Iy \<open>delta \<ge> deltaG(TYPE('a))\<close> by (auto simp add: Gromov_product_commute)
  also have "... \<le> Gromov_product_at py x' y'"
    by (intro mono_intros)
  finally have B: "M - 4 * delta + dist x' y' \<le> dist py x'"
    unfolding Gromov_product_at_def \<open>dist py y' = M\<close> by auto

  have "dist px py \<le> 2 * M - 10 * delta"
    using assms \<open>dist px py \<le> 5 * delta\<close> by auto
  have "2 * M - 8 * delta + 2 * dist x' y' \<le> dist px y' + dist py x'"
    using A B by auto
  also have "... \<le> max (dist px py + dist y' x') (dist px x' + dist y' py) + 2 * deltaG TYPE('a)"
    by (rule hyperb_quad_ineq)
  also have "... \<le> max (dist px py + dist y' x') (dist px x' + dist y' py) + 2 * delta"
    using \<open>deltaG(TYPE('a)) \<le> delta\<close> by auto
  finally have "2 * M - 10 * delta + 2 * dist x' y' \<le> max (dist px py + dist y' x') (dist px x' + dist y' py)"
    by auto
  then have "2 * M - 10 * delta + 2 * dist x' y' \<le> dist px x' + dist py y'"
    apply (auto simp add: metric_space_class.dist_commute)
    using \<open>0 \<le> delta\<close> \<open>dist px py \<le> 2 * M - 10 * delta\<close> \<open>dist px x' = M\<close> \<open>dist py y' = M\<close> by auto
  then have "dist x' y' \<le> 5 * delta"
    unfolding \<open>dist px x' = M\<close> \<open>dist py y' = M\<close> by auto
  then show ?thesis
    unfolding x'_def y'_def by auto
qed

text \<open>The next lemma (Lemma 10 in~\cite{shchur} for $C = 0$) asserts that the projection on a geodesic segment is
an exponential contraction.
More precisely, if a path of length $L$ is at distance at least $D$ of a geodesic segment $G$,
then the projection of the path on $G$ has diameter at most $C L \exp(-c D/\delta)$, where $C$ and
$c$ are universal constants. This is not completely true at one can not go below a fixed size, as
always, so the correct bound is $K \max(\delta, L \exp(-c D/\delta))$. For the application, we
give a slightly more general statement involving an additional constant $C$.

This statement follows from the previous lemma: if one moves towards $G$ by $10 \delta$, then
the distance between points is divided by $2$. Then one iterates this statement as many times
as possible, gaining a factor $2$ each time and therefore an exponential factor in the end.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) geodesic_projection_exp_contracting:
  assumes "geodesic_segment G"
          "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> dist (f x) (f y) \<le> lambda * dist x y + C"
          "a \<le> b"
          "pa \<in> proj_set (f a) G"
          "pb \<in> proj_set (f b) G"
          "\<And>t. t \<in> {a..b} \<Longrightarrow> infdist (f t) G \<ge> D"
          "D \<ge> 15/2 * delta + C/2"
          "delta > deltaG(TYPE('a))"
          "C \<ge> 0"
          "lambda \<ge> 0"
  shows "dist pa pb \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (b-a) * exp(-(D-C/2) * ln 2 / (5 * delta)))"
proof -
  have "delta > 0" using assms
    using local.delta_nonneg by linarith
  have "exp(15/2/5 * ln 2) = exp(ln 2) * exp(1/2 * ln (2::real))"
    unfolding mult_exp_exp by simp
  also have "... = 2 * exp(1/2 * ln 2)"
    by auto
  finally have "exp(15/2/5 * ln 2) = 2 * exp(1/2 * ln (2::real))"
    by simp

  text \<open>The idea of the proof is to start with a sequence of points separated by $10 \delta + C$ along
  the original path, and push them by a fixed distance towards $G$ to bring them at distance at most
  $5 \delta$, thanks to the previous lemma. Then, discard half the points, and start again. This
  is possible while one is far enough from $G$. In the first step of the proof, we formalize this
  in the case where the process can be iterated long enough that, at the end, the projections on $G$
  are very close together. This is a simple induction, based on the previous lemma.\<close>

  have Main: "\<And>c g p. (\<forall>i \<in> {0..2^k}. p i \<in> proj_set (g i) G)
            \<Longrightarrow> (\<forall>i \<in> {0..2^k}. dist (p i) (g i) \<ge> 5 * delta * k + 15/2 * delta + c/2)
            \<Longrightarrow> (\<forall>i \<in> {0..<2^k}. dist (g i) (g (Suc i)) \<le> 10 * delta + c)
            \<Longrightarrow> c \<ge> 0
            \<Longrightarrow> dist (p 0) (p (2^k)) \<le> 5 * deltaG(TYPE('a))" for k
  proof (induction k)
    case 0
    then have H: "p 0 \<in> proj_set (g 0) G"
                 "p 1 \<in> proj_set (g 1) G"
                 "dist (g 0) (g 1) \<le> 10 * delta + c"
                 "dist (p 0) (g 0) \<ge> 15/2 * delta + c/2"
                 "dist (p 1) (g 1) \<ge> 15/2 * delta + c/2"
      by auto
    have "dist (p 0) (p 1) \<le> max (5 * deltaG(TYPE('a))) (dist (g 0) (g 1) - dist (p 0) (g 0) - dist (p 1) (g 1) + 10 * deltaG(TYPE('a)))"
      by (rule proj_along_geodesic_contraction[OF \<open>geodesic_segment G\<close> \<open>p 0 \<in> proj_set (g 0) G\<close> \<open>p 1 \<in> proj_set (g 1) G\<close>])
    also have "... \<le> max (5 * deltaG(TYPE('a))) (5 * deltaG(TYPE('a)))"
      apply (intro mono_intros) using H \<open>delta > deltaG(TYPE('a))\<close> by auto
    finally show "dist (p 0) (p (2^0)) \<le> 5 * deltaG(TYPE('a))"
      by auto
  next
    case (Suc k)
    have *: "5 * delta * real (k + 1) + 5 * delta = 5 * delta * real (Suc k + 1)"
      by (simp add: algebra_simps)
    define h where "h = (\<lambda>i. geodesic_segment_param {p i--g i} (p i) (5 * delta * k + 15/2 * delta))"
    have h_dist: "dist (h i) (h (Suc i)) \<le> 5 * delta" if "i \<in> {0..<2^(Suc k)}" for i
      unfolding h_def apply (rule geodesic_projection_exp_contracting_aux[OF \<open>geodesic_segment G\<close> _ _ less_imp_le[OF \<open>delta > deltaG(TYPE('a))\<close>]])
      unfolding * using Suc.prems that \<open>delta > 0\<close> by (auto simp add: algebra_simps divide_simps)
    define g' where "g' = (\<lambda>i. h (2 * i))"
    define p' where "p' = (\<lambda>i. p (2 * i))"
    have "dist (p' 0) (p' (2^k)) \<le> 5 * deltaG(TYPE('a))"
    proof (rule Suc.IH[where ?g = g' and ?c = 0])
      show "\<forall>i\<in>{0..2 ^ k}. p' i \<in> proj_set (g' i) G"
      proof
        fix i::nat assume "i \<in> {0..2^k}"
        then have *: "2 * i \<in> {0..2^(Suc k)}" by auto
        show "p' i \<in> proj_set (g' i) G"
          unfolding p'_def g'_def h_def apply (rule proj_set_geodesic_same_basepoint[of _ "g (2 * i)" _ "{p(2 * i)--g(2 * i)}"])
          using Suc * by (auto simp add: geodesic_segment_param_in_segment)
      qed
      show "\<forall>i\<in>{0..2 ^ k}. 5 * delta * k + 15/2 * delta + 0/2 \<le> dist (p' i) (g' i)"
      proof
        fix i::nat assume "i \<in> {0..2^k}"
        then have *: "2 * i \<in> {0..2^(Suc k)}" by auto
        have "5 * delta * k + 15/2 * delta \<le> 5 * delta * Suc k + 15/2 * delta + c/2"
          using \<open>delta > 0\<close> \<open>c \<ge> 0\<close> by (auto simp add: algebra_simps divide_simps)
        also have "... \<le> dist (p (2 * i)) (g (2 * i))"
          using Suc * by auto
        finally have *: "5 * delta * k + 15/2 * delta \<le> dist (p (2 * i)) (g (2 * i))" by simp
        have "dist (p' i) (g' i) = 5 * delta * k + 15/2 * delta"
          unfolding p'_def g'_def h_def apply (rule geodesic_segment_param_in_geodesic_spaces(6))
          using * \<open>delta > 0\<close> by auto
        then show "5 * delta * k + 15/2 * delta + 0/2 \<le> dist (p' i) (g' i)" by simp
      qed
      show "\<forall>i\<in>{0..<2 ^ k}. dist (g' i) (g' (Suc i)) \<le> 10 * delta + 0"
      proof
        fix i::nat assume *: "i \<in> {0..<2 ^ k}"
        have "dist (g' i) (g' (Suc i)) = dist (h (2 * i)) (h (Suc (Suc (2 * i))))"
          unfolding g'_def by auto
        also have "... \<le> dist (h (2 * i)) (h (Suc (2 * i))) + dist (h (Suc (2 * i))) (h (Suc (Suc (2 * i))))"
          by (intro mono_intros)
        also have "... \<le> 5 * delta + 5 * delta"
          apply (intro mono_intros h_dist) using * by auto
        finally show "dist (g' i) (g' (Suc i)) \<le> 10 * delta + 0" by simp
      qed
    qed (simp)
    then show "dist (p 0) (p (2 ^ Suc k)) \<le> 5 * deltaG(TYPE('a))"
      unfolding p'_def by auto
  qed

  text \<open>Now, we will apply the previous basic statement to points along our original path. We
  introduce $k$, the number of steps for which the pushing process can be done -- it only depends on
  the original distance $D$ to $G$. \<close>

  define k where "k = nat(floor((D - C/2 - 15/2 * delta)/(5 * delta)))"
  have "int k = floor((D - C/2 - 15/2 * delta)/(5 * delta))"
    unfolding k_def apply (rule nat_0_le) using \<open>D \<ge> 15/2 * delta + C/2\<close> \<open>delta > 0\<close> by auto
  then have "k \<le> (D - C/2 - 15/2 * delta)/(5 * delta)" "(D - C/2 - 15/2 * delta)/(5 * delta) \<le> k + 1"
    by linarith+
  then have k: "D \<ge> 5 * delta * k + 15/2 * delta + C/2" "D \<le> 5 * delta * (k+1) + 15/2 * delta + C/2"
    using \<open>delta > 0\<close> by (auto simp add: algebra_simps divide_simps)
  have "exp((D-C/2)/(5 * delta) * ln 2) * exp(-15/2/5 * ln 2) = exp(((D-C/2-15/2 * delta)/(5 * delta)) * ln 2)"
    unfolding mult_exp_exp using \<open>delta > 0\<close> by (simp add: algebra_simps divide_simps)
  also have "... \<le> exp((k+1) * ln 2)"
    apply (intro mono_intros) using k(2) \<open>delta > 0\<close> by (auto simp add: divide_simps algebra_simps)
  also have "... = 2^(k+1)"
    by (subst powr_realpow[symmetric], auto simp add: powr_def)
  also have "... = 2 * 2^k"
    by auto
  finally have k': "1/2^k \<le> 2 * exp(15/2/5 * ln 2) * exp(- ((D-C/2) * ln 2 / (5 * delta)))"
    by (auto simp add: algebra_simps divide_simps exp_minus)

  text \<open>We separate the proof into two cases. If the path is not too long, then it can be covered by
  $2^k$ points at distance at most $10 \delta + C$. By the basic statement, it follows that the diameter
  of the projection is at most $5 \delta$. Otherwise, we subdivide the path into $2^N$ points at
  distance at most $10 \delta + C$, with $N \geq k$, and apply the basic statement to blocks of $2^k$
  consecutive points. It follows that the projections of $g_0, g_{2^k}, g_{2\cdot 2^k},\dotsc$ are
  at distances at most $5 \delta$. Hence, the first and last projections are at distance at most
  $2^{N-k} \cdot 5 \delta$, which is the desired bound.\<close>

  show ?thesis
  proof (cases "lambda * (b-a) \<le> 10 * delta * 2^k")
    text \<open>First, treat the case where the path is rather short.\<close>
    case True
    define g::"nat \<Rightarrow> 'a" where "g = (\<lambda>i. f(a + (b-a) * i/2^k))"
    have "g 0 = f a" "g(2^k) = f b"
      unfolding g_def by auto
    have *: "a + (b-a) * i/2^k \<in> {a..b}" if "i \<in> {0..2^k}" for i::nat
    proof -
      have "a + (b - a) * (real i / 2 ^ k) \<le> a + (b-a) * (2^k/2^k)"
        apply (intro mono_intros) using that \<open>a \<le> b\<close> by auto
      then show ?thesis using \<open>a \<le> b\<close> by auto
    qed
    have A: "dist (g i) (g (Suc i)) \<le> 10 * delta + C" if "i \<in> {0..<2^k}" for i
    proof -
      have "dist (g i) (g (Suc i)) \<le> lambda * dist (a + (b-a) * i/2^k) (a + (b-a) * (Suc i)/2^k) + C"
        unfolding g_def apply (intro assms(2) *) using that by auto
      also have "... = lambda * (b-a)/2^k + C"
        unfolding dist_real_def using \<open>a \<le> b\<close> by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> 10 * delta + C"
        using True by (simp add: divide_simps algebra_simps)
      finally show ?thesis by simp
    qed
    define p where "p = (\<lambda>i. if i = 0 then pa else if i = 2^k then pb else SOME p. p \<in> proj_set (g i) G)"
    have B: "p i \<in> proj_set (g i) G" if "i \<in> {0..2^k}" for i
    proof (cases "i = 0 \<or> i = 2^k")
      case True
      then show ?thesis
        using \<open>pa \<in> proj_set (f a) G\<close> \<open>pb \<in> proj_set (f b) G\<close> unfolding p_def g_def by auto
    next
      case False
      then have "p i = (SOME p. p \<in> proj_set (g i) G)"
        unfolding p_def by auto
      moreover have "proj_set (g i) G \<noteq> {}"
        apply (rule proj_set_nonempty_of_proper) using geodesic_segment_topology[OF \<open>geodesic_segment G\<close>] by auto
      ultimately show ?thesis
        using some_in_eq by auto
    qed
    have C: "dist (p i) (g i) \<ge> 5 * delta * k + 15/2 * delta + C/2" if "i \<in> {0..2^k}" for i
    proof -
      have "5 * delta * k + 15/2 * delta + C/2 \<le> D"
        using k(1) by simp
      also have "... \<le> infdist (g i) G"
        unfolding g_def apply (rule \<open>\<And>t. t \<in> {a..b} \<Longrightarrow> infdist (f t) G \<ge> D\<close>) using * that by auto
      also have "... = dist (p i) (g i)"
        using that proj_setD(2)[OF B[OF that]] by (simp add: metric_space_class.dist_commute)
      finally show ?thesis by simp
    qed
    have "dist (p 0) (p (2^k)) \<le> 5 * deltaG(TYPE('a))"
      apply (rule Main[where ?g = g and ?c = C]) using A B C \<open>C \<ge> 0\<close> by auto
    then show ?thesis
      unfolding p_def by auto
  next
    text \<open>Now, the case where the path is long. We introduce $N$ such that it is roughly of length
    $2^N \cdot 10 \delta$.\<close>
    case False
    have *: "10 * delta * 2^k \<le> lambda * (b-a)" using False by simp
    have "lambda * (b-a) > 0"
      using \<open>delta > 0\<close> False \<open>0 \<le> lambda\<close> assms(3) less_eq_real_def mult_le_0_iff by auto
    then have "a < b" "lambda > 0"
      using \<open>a \<le> b\<close> \<open>lambda \<ge> 0\<close> less_eq_real_def by auto
    define n where "n = nat(floor(log 2 (lambda * (b-a)/(10 * delta))))"
    have "log 2 (lambda * (b-a)/(10 * delta)) \<ge> log 2 (2^k)"
      apply (subst log_le_cancel_iff)
      using * \<open>delta > 0\<close> \<open>a < b\<close> \<open>lambda > 0\<close> by (auto simp add: divide_simps algebra_simps)
    moreover have "log 2 (2^k) = k"
      by simp
    ultimately have A: "log 2 (lambda * (b-a)/(10 * delta)) \<ge> k" by auto
    have **: "int n = floor(log 2 (lambda * (b-a)/(10 * delta)))"
      unfolding n_def apply (rule nat_0_le) using A by auto
    then have "log 2 (2^n) \<le> log 2 (lambda * (b-a)/(10 * delta))"
      apply (subst log_nat_power, auto) by linarith
    then have I: "2^n \<le> lambda * (b-a)/(10 * delta)"
      using \<open>0 < lambda * (b - a)\<close> \<open>0 < delta\<close>
      by (simp add: le_log_iff powr_realpow)
    have "log 2 (lambda * (b-a)/(10 * delta)) \<le> log 2 (2^(n+1))"
      apply (subst log_nat_power, auto) using ** by linarith
    then have J: "lambda * (b-a)/(10 * delta) \<le> 2^(n+1)"
      using \<open>0 < lambda * (b - a)\<close> \<open>0 < delta\<close> by auto
    have K: "k \<le> n" using A ** by linarith
    define N where "N = n+1"
    have N: "k+1 \<le> N" "lambda * (b-a) / 2^N \<le> 10 *delta" "2 ^ N \<le> lambda * (b - a) / (5 * delta)"
      using I J K \<open>delta > 0\<close> unfolding N_def by (auto simp add: divide_simps algebra_simps)
    then have "2 ^ k \<noteq> (0::real)" "k \<le> N"
      by auto
    then have "(2^(N-k)::real) = 2^N/2^k"
      by (metis (no_types) add_diff_cancel_left' le_Suc_ex nonzero_mult_div_cancel_left power_add)

    text \<open>Define $2^N$ points along the path, separated by at most $10\delta$, and their projections.\<close>
    define g::"nat \<Rightarrow> 'a" where "g = (\<lambda>i. f(a + (b-a) * i/2^N))"
    have "g 0 = f a" "g(2^N) = f b"
      unfolding g_def by auto
    have *: "a + (b-a) * i/2^N \<in> {a..b}" if "i \<in> {0..2^N}" for i::nat
    proof -
      have "a + (b - a) * (real i / 2 ^ N) \<le> a + (b-a) * (2^N/2^N)"
        apply (intro mono_intros) using that \<open>a \<le> b\<close> by auto
      then show ?thesis using \<open>a \<le> b\<close> by auto
    qed
    have A: "dist (g i) (g (Suc i)) \<le> 10 * delta + C" if "i \<in> {0..<2^N}" for i
    proof -
      have "dist (g i) (g (Suc i)) \<le> lambda * dist (a + (b-a) * i/2^N) (a + (b-a) * (Suc i)/2^N) + C"
        unfolding g_def apply (intro assms(2) *)
        using that by auto
      also have "... = lambda * (b-a)/2^N + C"
        unfolding dist_real_def using \<open>a \<le> b\<close> by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> 10 * delta + C"
        using N by simp
      finally show ?thesis by simp
    qed
    define p where "p = (\<lambda>i. if i = 0 then pa else if i = 2^N then pb else SOME p. p \<in> proj_set (g i) G)"
    have B: "p i \<in> proj_set (g i) G" if "i \<in> {0..2^N}" for i
    proof (cases "i = 0 \<or> i = 2^N")
      case True
      then show ?thesis
        using \<open>pa \<in> proj_set (f a) G\<close> \<open>pb \<in> proj_set (f b) G\<close> unfolding p_def g_def by auto
    next
      case False
      then have "p i = (SOME p. p \<in> proj_set (g i) G)"
        unfolding p_def by auto
      moreover have "proj_set (g i) G \<noteq> {}"
        apply (rule proj_set_nonempty_of_proper) using geodesic_segment_topology[OF \<open>geodesic_segment G\<close>] by auto
      ultimately show ?thesis
        using some_in_eq by auto
    qed
    have C: "dist (p i) (g i) \<ge> 5 * delta * k + 15/2 * delta + C/2" if "i \<in> {0..2^N}" for i
    proof -
      have "5 * delta * k + 15/2 * delta + C/2 \<le> D"
        using k(1) by simp
      also have "... \<le> infdist (g i) G"
        unfolding g_def apply (rule \<open>\<And>t. t \<in> {a..b} \<Longrightarrow> infdist (f t) G \<ge> D\<close>) using * that by auto
      also have "... = dist (p i) (g i)"
        using that proj_setD(2)[OF B[OF that]] by (simp add: metric_space_class.dist_commute)
      finally show ?thesis by simp
    qed
    text \<open>Use the basic statement to show that, along packets of size $2^k$, the projections
    are within $5\delta$ of each other.\<close>
    have I: "dist (p (2^k * j)) (p (2^k * (Suc j))) \<le> 5 * delta" if "j \<in> {0..<2^(N-k)}" for j
    proof -
      have I: "i + 2^k * j \<in> {0..2^N}" if "i \<in> {0..2^k}" for i
      proof -
        have "i + 2 ^ k * j \<le> 2^k + 2^k * (2^(N-k)-1)"
          apply (intro mono_intros) using that \<open>j \<in> {0..<2^(N-k)}\<close> by auto
        also have "... = 2^N"
          using \<open>k +1 \<le> N\<close> by (auto simp add: algebra_simps semiring_normalization_rules(26))
        finally show ?thesis by auto
      qed
      have I': "i + 2^k * j \<in> {0..<2^N}" if "i \<in> {0..<2^k}" for i
      proof -
        have "i + 2 ^ k * j < 2^k + 2^k * (2^(N-k)-1)"
          apply (intro mono_intros) using that \<open>j \<in> {0..<2^(N-k)}\<close> by auto
        also have "... = 2^N"
          using \<open>k +1 \<le> N\<close> by (auto simp add: algebra_simps semiring_normalization_rules(26))
        finally show ?thesis by auto
      qed
      define g' where "g' = (\<lambda>i. g (i + 2^k * j))"
      define p' where "p' = (\<lambda>i. p (i + 2^k * j))"
      have "dist (p' 0) (p' (2^k)) \<le> 5 * deltaG(TYPE('a))"
        apply (rule Main[where ?g = g' and ?c = C]) unfolding p'_def g'_def using A B C I I' \<open>C \<ge> 0\<close> by auto
      also have "... \<le> 5 * delta"
        using \<open>deltaG(TYPE('a)) < delta\<close> by auto
      finally show ?thesis
        unfolding p'_def by auto
    qed
    text \<open>Control the total distance by adding the contributions of blocks of size $2^k$.\<close>
    have *: "dist (p 0) (p(2^k * j)) \<le> (\<Sum>i<j. dist (p (2^k * i)) (p (2^k * (Suc i))))" for j
    proof (induction j)
      case (Suc j)
      have "dist (p 0) (p(2^k * (Suc j))) \<le> dist (p 0) (p(2^k * j)) + dist (p(2^k * j)) (p(2^k * (Suc j)))"
        by (intro mono_intros)
      also have "... \<le> (\<Sum>i<j. dist (p (2^k * i)) (p (2^k * (Suc i)))) + dist (p(2^k * j)) (p(2^k * (Suc j)))"
        using Suc.IH by auto
      also have "... = (\<Sum>i<Suc j. dist (p (2^k * i)) (p (2^k * (Suc i))))"
        by auto
      finally show ?case by simp
    qed (auto)
    have "dist pa pb = dist (p 0) (p (2^N))"
      unfolding p_def by auto
    also have "... = dist (p 0) (p (2^k * 2^(N-k)))"
      using \<open>k +1 \<le> N\<close> by (auto simp add: semiring_normalization_rules(26))
    also have "... \<le> (\<Sum>i<2^(N-k). dist (p (2^k * i)) (p (2^k * (Suc i))))"
      using * by auto
    also have "... \<le> (\<Sum>(i::nat)<2^(N-k). 5 * delta)"
      apply (rule sum_mono) using I by auto
    also have "... = 5 * delta * 2^(N-k)"
      by auto
    also have "... = 5 * delta * 2^N * (1/ 2^k)"
      unfolding \<open>(2^(N-k)::real) = 2^N/2^k\<close> by simp
    also have "... \<le> 5 * delta * (2 * lambda * (b-a)/(10 * delta)) * (2 * exp(15/2/5 * ln 2) * exp(- ((D-C/2) * ln 2 / (5 * delta))))"
      apply (intro mono_intros) using \<open>delta > 0\<close> \<open>lambda > 0\<close> \<open>a < b\<close> k' N by auto
    also have "... = (2 * exp(15/2/5 * ln 2)) * lambda * (b-a) * exp(-(D-C/2) * ln 2 / (5 * delta))"
      using \<open>delta > 0\<close> by (auto simp add: algebra_simps divide_simps)
    finally show ?thesis
      unfolding \<open>exp(15/2/5 * ln 2) = 2 * exp(1/2 * ln (2::real))\<close> by auto
  qed
qed

text \<open>We deduce from the previous result that a projection on a quasiconvex set is also
exponentially contracting. To do this, one uses the contraction of a projection on a geodesic, and
one adds up the additional errors due to the quasi-convexity. In particular, the projections on the
original quasiconvex set or the geodesic do not have to coincide, but they are within distance at
most $C + 8 \delta$.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) quasiconvex_projection_exp_contracting:
  assumes "quasiconvex K G"
          "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> dist (f x) (f y) \<le> lambda * dist x y + C"
          "a \<le> b"
          "pa \<in> proj_set (f a) G"
          "pb \<in> proj_set (f b) G"
          "\<And>t. t \<in> {a..b} \<Longrightarrow> infdist (f t) G \<ge> D"
          "D \<ge> 15/2 * delta + K + C/2"
          "delta > deltaG(TYPE('a))"
          "C \<ge> 0"
          "lambda \<ge> 0"
  shows "dist pa pb \<le> 2 * K + 8 * delta + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (b-a) * exp(-(D - K - C/2) * ln 2 / (5 * delta)))"
proof -
  obtain H where H: "geodesic_segment_between H pa pb" "\<And>q. q \<in> H \<Longrightarrow> infdist q G \<le> K"
    using quasiconvexD[OF assms(1) proj_setD(1)[OF \<open>pa \<in> proj_set (f a) G\<close>] proj_setD(1)[OF \<open>pb \<in> proj_set (f b) G\<close>]] by auto
  obtain qa where qa: "qa \<in> proj_set (f a) H"
    using proj_set_nonempty_of_proper[of H "f a"] geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto
  obtain qb where qb: "qb \<in> proj_set (f b) H"
    using proj_set_nonempty_of_proper[of H "f b"] geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto

  have I: "infdist (f t) H \<ge> D - K" if "t \<in> {a..b}" for t
  proof -
    have *: "D - K \<le> dist (f t) h" if "h \<in> H" for h
    proof -
      have "D - K - dist (f t) h \<le> e" if "e > 0" for e
      proof -
        have *: "infdist h G < K + e" using H(2)[OF \<open>h \<in> H\<close>] \<open>e > 0\<close> by auto
        obtain g where g: "g \<in> G" "dist h g < K + e"
          using infdist_almost_attained[OF *] proj_setD(1)[OF \<open>pa \<in> proj_set (f a) G\<close>] by auto
        have "D \<le> dist (f t) g"
          using \<open>\<And>t. t \<in> {a..b} \<Longrightarrow> infdist (f t) G \<ge> D\<close>[OF \<open>t \<in> {a..b}\<close>] infdist_le[OF \<open>g \<in> G\<close>, of "f t"] by auto
        also have "... \<le> dist (f t) h + dist h g"
          by (intro mono_intros)
        also have "... \<le> dist (f t) h + K + e"
          using g(2) by auto
        finally show ?thesis by auto
      qed
      then have *: "D - K - dist (f t) h \<le> 0"
        using dense_ge by blast
      then show ?thesis by simp
    qed
    have "D - K \<le> Inf (dist (f t) ` H)"
      apply (rule cInf_greatest) using * H(1) by auto
    then show "D - K \<le> infdist (f t) H"
      apply (subst infdist_notempty) using H(1) by auto
  qed
  have Q: "dist qa qb \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (b-a) * exp(-((D - K)-C/2 ) * ln 2 / (5 * delta)))"
    apply (rule geodesic_projection_exp_contracting[OF geodesic_segmentI[OF \<open>geodesic_segment_between H pa pb\<close>] assms(2) assms(3)])
    using qa qb I assms by auto

  have A: "dist pa qa \<le> 4 * delta + K"
  proof -
    have "dist (f a) pa - dist (f a) qa - K \<le> e" if "e > 0" for e::real
    proof -
      have *: "infdist qa G < K + e" using H(2)[OF proj_setD(1)[OF qa]] \<open>e > 0\<close> by auto
      obtain g where g: "g \<in> G" "dist qa g < K + e"
        using infdist_almost_attained[OF *] proj_setD(1)[OF \<open>pa \<in> proj_set (f a) G\<close>] by auto
      have "dist (f a) pa \<le> dist (f a) g"
        unfolding proj_setD(2)[OF \<open>pa \<in> proj_set (f a) G\<close>] using infdist_le[OF \<open>g \<in> G\<close>, of "f a"] by simp
      also have "... \<le> dist (f a) qa + dist qa g"
        by (intro mono_intros)
      also have "... \<le> dist (f a) qa + K + e"
        using g(2) by auto
      finally show ?thesis by simp
    qed
    then have I: "dist (f a) pa - dist (f a) qa - K \<le> 0"
      using dense_ge by blast
    have "dist (f a) qa + dist qa pa \<le> dist (f a) pa + 4 * deltaG(TYPE('a))"
      apply (rule dist_along_geodesic[OF geodesic_segmentI[OF H(1)]]) using qa H(1) by auto
    also have "... \<le> dist (f a) qa + K + 4 * delta"
      using I assms by auto
    finally show ?thesis
      by (simp add: metric_space_class.dist_commute)
  qed
  have B: "dist qb pb \<le> 4 * delta + K"
  proof -
    have "dist (f b) pb - dist (f b) qb - K \<le> e" if "e > 0" for e::real
    proof -
      have *: "infdist qb G < K + e" using H(2)[OF proj_setD(1)[OF qb]] \<open>e > 0\<close> by auto
      obtain g where g: "g \<in> G" "dist qb g < K + e"
        using infdist_almost_attained[OF *] proj_setD(1)[OF \<open>pa \<in> proj_set (f a) G\<close>] by auto
      have "dist (f b) pb \<le> dist (f b) g"
        unfolding proj_setD(2)[OF \<open>pb \<in> proj_set (f b) G\<close>] using infdist_le[OF \<open>g \<in> G\<close>, of "f b"] by simp
      also have "... \<le> dist (f b) qb + dist qb g"
        by (intro mono_intros)
      also have "... \<le> dist (f b) qb + K + e"
        using g(2) by auto
      finally show ?thesis by simp
    qed
    then have I: "dist (f b) pb - dist (f b) qb - K \<le> 0"
      using dense_ge by blast
    have "dist (f b) qb + dist qb pb \<le> dist (f b) pb + 4 * deltaG(TYPE('a))"
      apply (rule dist_along_geodesic[OF geodesic_segmentI[OF H(1)]]) using qb H(1) by auto
    also have "... \<le> dist (f b) qb + K + 4 * delta"
      using I assms by auto
    finally show ?thesis
      by simp
  qed
  have "dist pa pb \<le> dist pa qa + dist qa qb + dist qb pb"
    by (intro mono_intros)
  then show ?thesis
    using Q A B by auto
qed

text \<open>The next statement is the main step in the proof of the Morse-Gromov theorem given by Shchur
in~\cite{shchur}, asserting that a quasi-geodesic and a geodesic with the same endpoints are close.
We show that a point on the quasi-geodesic is close to the geodesic -- the other inequality will
follow easily later on. We also assume that the quasi-geodesic is parameterized by a Lipschitz map
-- the general case will follow as any quasi-geodesic can be approximated by a Lipschitz map with
good controls.

Here is a sketch of the proof. Fix two large constants $L \leq D$ (that we will choose carefully
to optimize the values of the constants at the end of the proof). Consider a quasi-geodesic $f$
between two points $f(u^-)$ and $f(u^+)$, and a geodesic segment $G$ between the same points.
Fix $f(z)$. We want to find a bound on $d(f(z), G)$.
1 - If this distance is smaller than $L$, we are done (and the bound is $L$).
2 - Assume it is larger.
Let $\pi_z$ be a projection of $f(z)$ on $G$ (at distance $d(f(z),G)$ of $f(z)$), and $H$ a geodesic
between $z$ and $\pi_z$. The idea will be to project the image of $f$ on $H$, and record how much
progress is made towards $f(z)$. In this proof, we will construct several points before and after
$z$. When necessary, we put an exponent $-$ on the points before $z$, and $+$ on the points after
$z$. To ease the reading, the points are ordered following the alphabetical order, i.e., $u^- \leq v
\leq w \leq x \leq y^- \leq z$.

One can find two points $f(y^-)$ and $f(y^+)$ on the left and the right of $f(z)$ that project
on $H$ roughly at distance $L$ of $\pi_z$ (up to some $O(\delta)$ -- recall that the closest point
projection is not uniquely defined, and not continuous, so we make some choice here).
Let $d^-$ be the minimal distance of $f([u^-, y^-])$ to $H$, and let $d^+$ be the minimal distance
of $f([y^+, u^+)]$ to $H$.

2.1 If the two distances $d^-$ and $d^+$ are less than $D$, then the distance between two points
realizing the minimum (say $f(c^-)$ and $f(c^+)$) is at most $2D+L$, hence $c^+ - c^-$ is controlled
(by $\lambda \cdot (2D+L) + C$) thanks to the quasi-isometry property. Therefore, $f(z)$ is not far
away from $f(c^-)$ and $f(c^+)$ (again by the quasi-isometry property). Since the distance from
these points to $\pi_z$ is controlled (by $D+L$), we get a good control on $d(f(z),\pi_z)$, as
desired.

2.2 The interesting case is when $d^-$ and $d^+$ are both $ > D$. Assume also for instance $d^- \geq
d^+$, as the other case is analogous. We will construct two points $f(v)$ and $f(x)$ with $u^- \leq
v \leq x \leq y^-$ with the following property:
\begin{equation}
\label{eq:xvK}
  K_1 e^{K_2 d(f(v), H)} \leq x-v,
\end{equation}
where $K_1$ and $K_2$ are some explicit constants (depending on $\lambda$, $\delta$, $L$ and $D$).
Let us show how this will conclude the proof. The distance from $f(v)$ to $f(c^+)$ is at most
$d(f(v),H) + L + d^+ \leq 3 d(f(v), H)$. Therefore, $c^+ - v$ is also controlled by $K' d(f(v), H)$
by the quasi-isometry property. This gives
\begin{align*}
  K &\leq K (x - v) e^{-K (c^+ - v)} \leq (e^{K (x-v)} - 1) \cdot e^{-K(c^+ - v)}
    \\& = e^{-K (c^+ - x)} - e^{-K (c^+ - v)}
    \leq e^{-K(c^+ - x)} - e^{-K (u^+ - u^-)}.
\end{align*}
This shows that, when one goes from the original quasi-geodesic $f([u^-, u^+])$ to the restricted
quasi-geodesic $f([x, c^+])$, the quantity $e^{-K \cdot}$ decreases by a fixed amount. In particular,
this process can only happen a uniformly bounded number of times, say $n$.

Let $G'$ be a geodesic between $f(x)$ and $f(c^+)$. One checks geometrically that $d(f(z), G) \leq
d(f(z), G') + (L + O(\delta))$, as both projections of $f(x)$ and $f(c^+)$ on $H$ are within
distance $L$ of $\pi_z$. Iterating the process $n$ times, one gets finally $d(f(z), G) \leq O(1) + n
(L + O(\delta))$. This is the desired bound for $d(f(z), G)$.

To complete the proof, it remains to construct the points $f(v)$ and $f(x)$ satisfying~\eqref{eq:xvK}.
This will be done through an inductive process.

Assume first that there is a point $f(v)$ whose projection on $H$ is close to the projection of
$f(u^-)$, and with $d(f(v), H) \leq 2 d^-$. Then the projections of $f(v)$ and $f(y^-)$ are far away
(at distance at least $L + O(\delta)$). Since the portion of $f$ between $v$ and $y^-$ is everywhere
at distance at least $d^-$ of $H$, the projection on $H$ contracts by a factor $e^{-d^-}$. It
follows that this portion of $f$ has length at least $e^{d^-} \cdot (L+O(\delta))$. Therefore, by
the quasi-isometry property, one gets $x - v \geq K e^{d^-}$. On the other hand, $d(v, H)$ is
bounded above by $2 d^-$ by assumption. This gives the desired inequality~\eqref{eq:xvK} with $x =
y^-$.

Otherwise, all points $f(v)$ whose projection on $H$ is close to the projection of $f(u^-)$ are such
that $d(f(v), H) \geq 2 d^-$. Consider $f(w_1)$ a point whose projection on $H$ is at distance
roughly $10 \delta$ of the projection of $f(u^-)$. Let $V_1$ be the set of points at distance at
most $d^-$ of $H$, i.e., the $d_1$-neighborhood of $H$. Then the distance between the projections of
$f(u^-)$ and $f(w_1)$ on $V_1$ is very large (are there is an additional big contraction to go from
$V_1$ to $H$). And moreover all the intermediate points $f(v)$ are at distance at least $2 d^-$ of
$H$, and therefore at distance at least $d^-$ of $H$. Then one can play the same game as in the
first case, where $y^-$ replaced by $w_1$ and $H$ replaced by $V_1$. If there is a point $f(v)$
whose projection on $V_1$ is close to the projection of $f(u^-)$, then the pair of points $v$ and $x
= w_1$ works. Otherwise, one lifts everything to $V_2$, the neighborhood of size $2d^-$ of $V_1$,
and one argues again in the same way.

The induction goes on like this until one finds a suitable pair of points. The process has indeed to
stop at one time, as it can only go on while $f(u^-)$ is outside of $V_k$, the $(2^k-1) d^-$
neighborhood of $H$). This concludes the sketch of the proof, modulo the adjustment of constants.

Comments on the formalization below:
\begin{itemize}
\item The proof is written as an induction on $u^+ - u^-$. This makes it possible to either prove
the bound directly (in the cases 1 and 2.1 above), or to use the bound on $d(z, G')$ in case 2.2
using the induction assumption, and conclude the proof. Of course, $u^+ - u^-$ is not integer-valued,
but in the reduction to $G'$ it decays by a fixed amount, so one can easily write this down as
a genuine induction.
\item The main difficulty in the proof is to construct the pair $(v, x)$ in case 2.2. This is again
written as an induction over $k$: either the required bound is true, or one can find a point $f(w)$
whose projection on $V_k$ is far enough from the projection of $f(u^-)$. Then, either one can use
this point to prove the bound, or one can construct a point with the same property with respect to
$V_{k+1}$, concluding the induction.
\item Instead of writing $u^-$ and $u^+$ (which are not good variable names in Isabelle), we write
$um$ and $uM$. Similarly for other variables.
\item The proof only works when $\delta > 0$ (as one needs to divide by $\delta$
in the exponential gain). Hence, we formulate it for some $\delta$ which is
strictly larger than the hyperbolicity constant. In a subsequent application of
the lemma, we will deduce the same statement for the hyperbolicity constant
by a limiting argument.
\item To optimize the value of the constant in the end, there is an additional important trick with
respect to the above sketch: in case 2.2, there is an exponential gain. One can spare a fraction
$(1-\alpha)$ of this gain to improve the constants, and spend the remaining fraction $\alpha$ to
make the argument work. This makes it possible to reduce the value of the constant roughly from
$40000$ to $100$, so we do it in the proof below. The values of $L$, $D$ and $\alpha$ can be chosen
freely, and have been chosen to get the best possible constant in the end.
\item For another optimization, we do not induce in terms of the distance from $f(z)$ to the geodesic
$G$, but rather in terms of the Gromov product $(f(u^-), f(u^+))_{f(z)}$ (which is the same up to
$O(\delta)$. And we do not take for $H$ a geodesic from $f(z)$ to its projection on $G$, but rather
a geodesic from $f(z)$ to the point $m$ on $[f(u^-), f(u^+)]$ opposite to $f(z)$ in the tripod, i.e.,
at distance $(f(z), f(u^+))_{f(u^-)}$ of $f(u^-)$, and at distance $(f(z), f(u^-))_{f(u^+)}$ of
$f(u^+)$. Let $\pi_z$ denote the point on $[f(z), m]$ at distance $(f(u^-), f(u^+)_{f(z)}$ of $f(z)$.
(It is within distance $2 \delta$ of $m$).
In both approaches, what we want to control by induction is the distance from $f(z)$ to $\pi_z$.
However, in the first approach, the points $f(u^-)$ and $f(u^+)$ project on $H$ between $\pi_z$ and
$f(z)$, and since the location of their projection is only controlled up to $4\delta$ one loses
essentially a $4\delta$-length of $L$ for the forthcoming argument. In the second approach, the
projections on $H$ are on the other side of $\pi_z$ compared to $f(z)$, so one does not lose
anything, and in the end it gives genuinely better bounds (making it possible to gain roughly
$10 \delta$ in the final estimate).
\end{itemize}
\<close>

lemma (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem_aux1:
  fixes f::"real \<Rightarrow> 'a"
  assumes "continuous_on {a..b} f"
          "lambda C-quasi_isometry_on {a..b} f"
          "a \<le> b"
          "geodesic_segment_between G (f a) (f b)"
          "z \<in> {a..b}"
          "delta > deltaG(TYPE('a))"
  shows "infdist (f z) G \<le> lambda^2 * (11/2 * C + 91 * delta)"
proof -
  have "C \<ge> 0" "lambda \<ge> 1" using quasi_isometry_onD assms by auto
  have "delta > 0" using assms delta_nonneg order_trans by linarith

  text \<open>We give their values to the parameters $L$, $D$ and $\alpha$ that we will use in the proof.
  We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
  bounds. Their values have no precise meaning, they are just the outcome of the computation\<close>
  define alpha::real where "alpha = 12/100"
  have alphaaux:"alpha > 0" "alpha \<le> 1" unfolding alpha_def by auto
  define L::real where "L = 18 * delta"
  define D::real where "D = 55 * delta"
  define K where "K = alpha * ln 2 / (5 * (4 + (L + 2 * delta)/D) * delta * lambda)"
  have "K > 0" "L > 0" "D > 0" unfolding K_def L_def D_def using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> alpha_def by auto
  have Laux: "L \<ge> 18 * delta" "D \<ge> 50 * delta" "L \<le> D" "D \<le> 4 * L" unfolding L_def D_def using \<open>delta > 0\<close> by auto
  have Daux: "8 * delta \<le> (1 - alpha) * D" unfolding alpha_def D_def using \<open>delta > 0\<close> by auto
  define Kmult where "Kmult = ((L + 4 * delta)/(L - 13 * delta)) * ((4 * exp(1/2 * ln 2)) * lambda * exp (- (1 - alpha) * D * ln 2 / (5 * delta)) / K)"
  have "Kmult > 0" unfolding Kmult_def using Laux \<open>delta > 0\<close> \<open>K > 0\<close> \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)

  text \<open>We prove that, for any pair of points to the left and to the right of $f(z)$, the distance
  from $f(z)$ to a geodesic between these points is controlled. We prove this by reducing to a
  closer pair of points, i.e., this is an inductive argument over real numbers. However, we
  formalize it as an artificial induction over natural numbers, as this is how induction works
  best, and since in our reduction step the new pair of points is always significantly closer
  than the initial one, at least by an amount $\delta/\lambda$.

  The main inductive bound that we will prove is the following. In this bound, the first term is
  what comes from the trivial cases 1 and 2.1 in the description of the proof before the statement
  of the theorem, while the most interesting term is the second term, corresponding to the induction
  per se.\<close>
  have Main: "\<And>um uM. um \<in> {a..z} \<Longrightarrow> uM \<in> {z..b}
          \<Longrightarrow> uM - um \<le> n * (1/4) * delta / lambda
          \<Longrightarrow> Gromov_product_at (f z) (f um) (f uM) \<le> lambda^2 * (D + (3/2) * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um)))"
    for n::nat
  proof (induction n)
    text \<open>Trivial base case of the induction\<close>
    case 0
    then have *: "z = um" "z = uM" by auto
    then have "Gromov_product_at (f z) (f um) (f uM) = 0" by auto
    also have "... \<le> 1 * (D + (3/2) * L + delta + 11/2 * C) - 2 * delta + 0 * (1 - exp(- K * (uM - um)))"
      using Laux \<open>C \<ge> 0\<close> \<open>delta > 0\<close> by auto
    also have "... \<le> lambda^2 * (D + (3/2) * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um)))"
      apply (intro mono_intros)
      using \<open>C \<ge> 0\<close> \<open>delta > 0\<close> Laux \<open>D > 0\<close> \<open>K > 0\<close> "0.prems" \<open>lambda \<ge> 1\<close> \<open>Kmult > 0\<close> by auto
    finally show ?case by auto
  next
    case (Suc n)
    show ?case
    proof (cases "Gromov_product_at (f z) (f um) (f uM) \<le> L")
      text \<open>If $f(z)$ is already close to the geodesic, there is nothing to do, and we do not need
      the induction assumption. This is case 1 in the description above.\<close>
      case True
      have "L \<le> 1 * (D + (3/2) * L + delta + 11/2 * C) - 2 * delta + 0 * (1 - exp(- K * (uM - um)))"
        using Laux \<open>C \<ge> 0\<close> \<open>delta > 0\<close> by auto
      also have "... \<le> lambda^2 * (D + (3/2) * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um)))"
        apply (intro mono_intros)
        using \<open>C \<ge> 0\<close> \<open>delta > 0\<close> Laux \<open>D > 0\<close> "Suc.prems" \<open>K > 0\<close> \<open>lambda \<ge> 1\<close> \<open>Kmult > 0\<close> by auto
      finally show ?thesis using True by auto
    next
      text \<open>We come to the interesting case where $f(z)$ is far away from a geodesic between
      $f(um)$ and $f(uM)$. Let $m$ be close to a projection of $f(z)$ on such a geodesic (we use
      the opposite point of $f(z)$ on the corresponding tripod). On a geodesic between $f(z)$ and $m$,
      consider the point $pi_z$ at distance $(f(um), f(uM))_{f(z)}$ of $f(z)$. It is very close to
      $m$ (within distance $2 \delta$). We will push the points $f(um)$ and $f(uM)$
      towards $f(z)$ by considering points whose projection on a geodesic $H$ between $m$ and
      $z$ is roughly at distance $L$ of $pi_z$.\<close>
      case False
      define m where "m = geodesic_segment_param {f um--f uM} (f um) (Gromov_product_at (f um) (f z) (f uM))"
      have "dist (f z) m \<le> Gromov_product_at (f z) (f um) (f uM) + 2 * deltaG(TYPE('a))"
        unfolding m_def by (rule dist_triangle_side_middle, auto)
      then have *: "dist (f z) m \<le> Gromov_product_at (f z) (f um) (f uM) + 2 * delta"
        using \<open>deltaG(TYPE('a)) < delta\<close> by auto
      have "Gromov_product_at (f z) (f um) (f uM) \<le> infdist (f z) {f um--f uM}"
        by (intro mono_intros, auto)
      also have "... \<le> dist (f z) m"
        apply (rule infdist_le) unfolding m_def by auto
      finally have **: "Gromov_product_at (f z) (f um) (f uM) \<le> dist (f z) m"
        by auto

      define H where "H = {f z--m}"
      define pi_z where "pi_z = geodesic_segment_param H (f z) (Gromov_product_at (f z) (f um) (f uM))"
      have "pi_z \<in> H" "m \<in> H" "f z \<in> H"
        unfolding pi_z_def H_def by (auto simp add: geodesic_segment_param_in_segment)
      have H: "geodesic_segment_between H (f z) m"
        unfolding H_def by auto
      have Dpi_z: "dist (f z) pi_z = Gromov_product_at (f z) (f um) (f uM)"
        unfolding pi_z_def H_def by (rule geodesic_segment_param(6)[where ?y = m], auto simp add: **)
      moreover have "dist (f z) m = dist (f z) pi_z + dist pi_z m"
        apply (rule geodesic_segment_dist[of H, symmetric]) using \<open>pi_z \<in> H\<close> unfolding H_def by auto
      ultimately have "dist pi_z m \<le> 2 * delta"
        using * by auto

      text \<open>Introduce the notation $p$ for some projection on the geodesic $H$.\<close>
      define p where "p = (\<lambda>r. SOME x. x \<in> proj_set (f r) H)"
      have p: "p x \<in> proj_set (f x) H" for x
        unfolding p_def using proj_set_nonempty_of_proper[of H "f x"] geodesic_segment_topology[OF geodesic_segmentI[OF H]]
        by (simp add: some_in_eq)
      then have pH: "p x \<in> H" for x
        using proj_setD(1) by auto
      have pz: "p z = f z"
        using p[of z] H by auto

      text \<open>The projection of $f(um)$ on $H$ is close to $pi_z$ (but it does not have to be exactly
      $pi_z$). It is between $pi_z$ and $m$.\<close>
      have "dist (f um) (f z) \<le> dist (f um) (p um) + dist (p um) (f z)"
        by (intro mono_intros)
      also have "... \<le> dist (f um) m + dist (p um) (f z)"
        unfolding proj_setD(2)[OF p[of um]] H_def by (auto intro!: infdist_le)
      also have "... = Gromov_product_at (f um) (f z) (f uM) + dist (p um) (f z)"
        unfolding m_def by simp
      finally have A: "Gromov_product_at (f z) (f um) (f uM) \<le> dist (p um) (f z)"
        unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute divide_simps)
      have "dist (p um) pi_z = abs(dist (p um) (f z) - dist pi_z (f z))"
        apply (rule dist_along_geodesic_wrt_endpoint[of H _ m]) using pH \<open>pi_z \<in> H\<close> H_def by auto
      also have "... = dist (p um) (f z) - dist pi_z (f z)"
        using A Dpi_z by (simp add: metric_space_class.dist_commute)
      finally have Dum: "dist (p um) (f z) = dist (p um) pi_z + dist pi_z (f z)" by auto

      text \<open>Choose a point $f(ym)$ whose projection on $H$ is roughly at distance $L$ of $pi_z$.\<close>
      have "\<exists>ym \<in> {um..z}. (dist (p um) (p ym) \<in> {(L + dist pi_z (p um)) - 4 * delta - 2 * 0 .. L + dist pi_z (p um)})
                    \<and> (\<forall>r \<in> {um..ym}. dist (p um) (p r) \<le> L + dist pi_z (p um))"
      proof (rule quasi_convex_projection_small_gaps[where ?f = f and ?G = H])
        show "continuous_on {um..z} f"
          apply (rule continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>])
          using \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> by auto
        show "um \<le> z" using \<open>um \<in> {a..z}\<close> by auto
        show "quasiconvex 0 H" using quasiconvex_of_geodesic geodesic_segmentI H by auto
        show "deltaG TYPE('a) < delta" by fact
        have "L + dist pi_z (p um) \<le> dist (f z) pi_z + dist pi_z (p um)"
          using False Dpi_z by (simp add: metric_space_class.dist_commute)
        then have "L + dist pi_z (p um) \<le> dist (p um) (f z)"
          using Dum by (simp add: metric_space_class.dist_commute)
        then show "L + dist pi_z (p um) \<in> {4 * delta + 2 * 0..dist (p um) (p z)}"
          using \<open>delta > 0\<close> False L_def pz by auto
        show "p ym \<in> proj_set (f ym) H" for ym using p by simp
      qed
      then obtain ym where ym : "ym \<in> {um..z}"
                                "dist (p um) (p ym) \<in> {(L + dist pi_z (p um)) - 4 * delta - 2 * 0 .. L + dist pi_z (p um)}"
                                "\<And>r. r \<in> {um..ym} \<Longrightarrow> dist (p um) (p r) \<le> L + dist pi_z (p um)"
        by blast
      have *: "continuous_on {um..ym} (\<lambda>r. infdist (f r) H)"
        using continuous_on_infdist[OF continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>, of "{um..ym}"], of H]
        \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> by auto
      text \<open>Choose a point $cm$ between $f(um)$ and $f(ym)$ realizing the minimal distance to $H$.
      Call this distance $dm$.\<close>
      have "\<exists>closestm \<in> {um..ym}. \<forall>v \<in> {um..ym}. infdist (f closestm) H \<le> infdist (f v) H"
        apply (rule continuous_attains_inf) using ym(1) * by auto
      then obtain closestm where closestm: "closestm \<in> {um..ym}" "\<And>v. v \<in> {um..ym} \<Longrightarrow> infdist (f closestm) H \<le> infdist (f v) H"
        by auto
      define dm where "dm = infdist (f closestm) H"
      have [simp]: "dm \<ge> 0" unfolding dm_def using infdist_nonneg by auto

      text \<open>Same things but in the interval $[z, uM]$.\<close>
      have I: "dist m (f uM) = dist (f um) (f uM) - dist (f um) m"
              "dist (f um) m = Gromov_product_at (f um) (f z) (f uM)"
        using geodesic_segment_dist[of "{f um--f uM}" "f um" "f uM" m] m_def by auto
      have "dist (f uM) (f z) \<le> dist (f uM) (p uM) + dist (p uM) (f z)"
        by (intro mono_intros)
      also have "... \<le> dist (f uM) m + dist (p uM) (f z)"
        unfolding proj_setD(2)[OF p[of uM]] H_def by (auto intro!: infdist_le)
      also have "... = Gromov_product_at (f uM) (f z) (f um) + dist (p uM) (f z)"
        using I unfolding Gromov_product_at_def by (simp add: divide_simps algebra_simps metric_space_class.dist_commute)
      finally have A: "Gromov_product_at (f z) (f um) (f uM) \<le> dist (p uM) (f z)"
        unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute divide_simps)
      have "dist (p uM) pi_z = abs(dist (p uM) (f z) - dist pi_z (f z))"
        apply (rule dist_along_geodesic_wrt_endpoint[of H _ m]) using pH \<open>pi_z \<in> H\<close> H_def by auto
      also have "... = dist (p uM) (f z) - dist pi_z (f z)"
        using A Dpi_z by (simp add: metric_space_class.dist_commute)
      finally have DuM: "dist (p uM) (f z) = dist (p uM) pi_z + dist pi_z (f z)" by auto

      text \<open>Choose a point $f(yM)$ whose projection on $H$ is roughly at distance $L$ of $pi_z$.\<close>
      have "\<exists>yM \<in> {z..uM}. dist (p uM) (p yM) \<in> {(L + dist pi_z (p uM)) - 4* delta - 2 * 0 .. L + dist pi_z (p uM)}
                    \<and> (\<forall>r \<in> {yM..uM}. dist (p uM) (p r) \<le> L + dist pi_z (p uM))"
      proof (rule quasi_convex_projection_small_gaps'[where ?f = f and ?G = H])
        show "continuous_on {z..uM} f"
          apply (rule continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>])
          using \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> by auto
        show "z \<le> uM" using \<open>uM \<in> {z..b}\<close> by auto
        show "quasiconvex 0 H" using quasiconvex_of_geodesic geodesic_segmentI H by auto
        show "deltaG TYPE('a) < delta" by fact
        have "L + dist pi_z (p uM) \<le> dist (f z) pi_z + dist pi_z (p uM)"
          using False Dpi_z by (simp add: metric_space_class.dist_commute)
        then have "L + dist pi_z (p uM) \<le> dist (p uM) (f z)"
          using DuM by (simp add: metric_space_class.dist_commute)
        then show "L + dist pi_z (p uM) \<in> {4 * delta + 2 * 0..dist (p z) (p uM)}"
          using \<open>delta > 0\<close> False L_def pz by (auto simp add: metric_space_class.dist_commute)
        show "p yM \<in> proj_set (f yM) H" for yM using p by simp
      qed
      then obtain yM where yM: "yM \<in> {z..uM}"
                              "dist (p uM) (p yM) \<in> {(L + dist pi_z (p uM)) - 4* delta - 2 * 0 .. L + dist pi_z (p uM)}"
                              "\<And>r. r \<in> {yM..uM} \<Longrightarrow> dist (p uM) (p r) \<le> L + dist pi_z (p uM)"
        by blast
      have *: "continuous_on {yM..uM} (\<lambda>r. infdist (f r) H)"
        using continuous_on_infdist[OF continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>, of "{yM..uM}"], of H]
        \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> by auto
      have "\<exists>closestM \<in> {yM..uM}. \<forall>v \<in> {yM..uM}. infdist (f closestM) H \<le> infdist (f v) H"
        apply (rule continuous_attains_inf) using yM(1) * by auto
      then obtain closestM where closestM: "closestM \<in> {yM..uM}" "\<And>v. v \<in> {yM..uM} \<Longrightarrow> infdist (f closestM) H \<le> infdist (f v) H"
        by auto
      define dM where "dM = infdist (f closestM) H"
      have [simp]: "dM \<ge> 0" unfolding dM_def using infdist_nonneg by auto

      text \<open>Points between $f(um)$ and $f(ym)$, or between $f(yM)$ and $f(uM)$, project within
      distance at most $L$ of $pi_z$ by construction.\<close>
      have P0: "dist m (p x) \<le> dist m pi_z + L" if "x \<in> {um..ym} \<union> {yM..uM}" for x
      proof (cases "x \<in> {um..ym}")
        case True
        have "dist m (f z) = dist m (p um) + dist (p um) pi_z + dist pi_z (f z)"
          using geodesic_segment_dist[OF H pH[of um]] Dum by (simp add: metric_space_class.dist_commute)
        moreover have "dist m (f z) = dist m pi_z + dist pi_z (f z)"
          using geodesic_segment_dist[OF H \<open>pi_z \<in> H\<close>] by (simp add: metric_space_class.dist_commute)
        ultimately have *: "dist m pi_z = dist m (p um) + dist (p um) pi_z" by auto
        have "dist (p um) (p x) \<le> L + dist pi_z (p um)"
          using ym(3)[OF \<open>x \<in> {um..ym}\<close>] by blast
        then show ?thesis
          using metric_space_class.dist_triangle[of m "p x" "p um"] * by (auto simp add: metric_space_class.dist_commute)
      next
        case False
        then have "x \<in> {yM..uM}" using that by auto
        have "dist m (f z) = dist m (p uM) + dist (p uM) pi_z + dist pi_z (f z)"
          using geodesic_segment_dist[OF H pH[of uM]] DuM by (simp add: metric_space_class.dist_commute)
        moreover have "dist m (f z) = dist m pi_z + dist pi_z (f z)"
          using geodesic_segment_dist[OF H \<open>pi_z \<in> H\<close>] by (simp add: metric_space_class.dist_commute)
        ultimately have *: "dist m pi_z = dist m (p uM) + dist (p uM) pi_z" by auto
        have "dist (p uM) (p x) \<le> L + dist pi_z (p uM)"
          using yM(3)[OF \<open>x \<in> {yM..uM}\<close>] by blast
        then show ?thesis
          using metric_space_class.dist_triangle[of m "p x" "p uM"] * by (auto simp add: metric_space_class.dist_commute)
      qed
      have P: "dist pi_z (p x) \<le> L" if "x \<in> {um..ym} \<union> {yM..uM}" for x
      proof (cases "dist m (p x) \<le> dist pi_z m")
        case True
        have "dist pi_z (p x) \<le> dist pi_z m + dist m (p x)"
          by (intro mono_intros)
        also have "... \<le> 2 * delta + 2 * delta"
          using \<open>dist pi_z m \<le> 2 * delta\<close> True by auto
        finally show ?thesis
          using Laux \<open>delta > 0\<close> by auto
      next
        case False
        have "dist pi_z (p x) = abs(dist pi_z m - dist (p x) m)"
          apply (rule dist_along_geodesic_wrt_endpoint[OF geodesic_segment_commute[OF H]])
          using pH \<open>pi_z \<in> H\<close> by auto
        also have "... = dist (p x) m - dist pi_z m"
          using False by (simp add: metric_space_class.dist_commute)
        finally show ?thesis
          using P0[OF that] by (simp add: metric_space_class.dist_commute)
      qed
      text \<open>Auxiliary fact for later use:
      The distance between two points in $[um, ym]$ and $[yM, uM]$ can be controlled using
      the distances of their images under $f$ to $H$, thanks to the quasi-isometry property.\<close>
      have D: "dist rm rM \<le> lambda * (infdist (f rm) H + (L + C + 2 * delta) + infdist (f rM) H)"
        if "rm \<in> {um..ym}" "rM \<in> {yM..uM}" for rm rM
      proof -
        have *: "dist m (p rm) \<le> L + dist m pi_z" "dist m (p rM) \<le> L + dist m pi_z"
          using P0 that by force+
        have "dist (p rm) (p rM) = abs(dist (p rm) m - dist (p rM) m)"
          apply (rule dist_along_geodesic_wrt_endpoint[OF geodesic_segment_commute[OF H]])
          using pH by auto
        also have "... \<le> L + dist m pi_z"
          unfolding abs_le_iff using * apply (auto simp add: metric_space_class.dist_commute)
          by (metis diff_add_cancel le_add_same_cancel1 metric_space_class.zero_le_dist order_trans)+
        finally have *: "dist (p rm) (p rM) \<le> L + 2 * delta"
          using \<open>dist pi_z m \<le> 2 * delta\<close> by (simp add: metric_space_class.dist_commute)

        have "(1/lambda) * dist rm rM - C \<le> dist (f rm) (f rM)"
          apply (rule quasi_isometry_onD(2)[OF \<open>lambda C-quasi_isometry_on {a..b} f\<close>])
          using \<open>rm \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>rM \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> by auto
        also have "... \<le> dist (f rm) (p rm) + dist (p rm) (p rM) + dist (p rM) (f rM)"
          by (intro mono_intros)
        also have "... \<le> infdist (f rm) H + L + 2 * delta + infdist (f rM) H"
          using * proj_setD(2)[OF p] by (simp add: metric_space_class.dist_commute)
        finally show ?thesis
          using \<open>lambda \<ge> 1\<close> by (simp add: algebra_simps divide_simps)
      qed
      text \<open>Auxiliary fact for later use in the inductive argument:
      the distance from $f(z)$ to $pi_z$ is controlled by the distance from $f(z)$ to any
      intermediate geodesic between points in $f[um, ym]$ and $f[yM, uM]$, up to a constant
      essentially given by $L$. This is a variation around Lemma 5 in~\cite{shchur}.\<close>
      have Rec: "Gromov_product_at (f z) (f um) (f uM) \<le> Gromov_product_at (f z) (f rm) (f rM) + (L + 4 * delta)" if "rm \<in> {um..ym}" "rM \<in> {yM..uM}" for rm rM
      proof -
        have *: "dist (f rm) (p rm) + dist (p rm) (f z) \<le> dist (f rm) (f z) + 4 * deltaG(TYPE('a))"
          apply (rule dist_along_geodesic[of H]) using p H_def by auto
        have "dist (f z) pi_z \<le> dist (f z) (p rm) + dist (p rm) pi_z"
          by (intro mono_intros)
        also have "... \<le> (Gromov_product_at (f z) (f rm) (p rm) + 2 * deltaG(TYPE('a))) + L"
          apply (intro mono_intros) using * P \<open>rm \<in> {um..ym}\<close> unfolding Gromov_product_at_def
          by (auto simp add: metric_space_class.dist_commute algebra_simps divide_simps)
        finally have A: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) \<le> Gromov_product_at (f z) (f rm) (p rm)"
          by simp
        have *: "dist (f rM) (p rM) + dist (p rM) (f z) \<le> dist (f rM) (f z) + 4 * deltaG(TYPE('a))"
          apply (rule dist_along_geodesic[of H]) using p H_def by auto
        have "dist (f z) pi_z \<le> dist (f z) (p rM) + dist (p rM) pi_z"
          by (intro mono_intros)
        also have "... \<le> (Gromov_product_at (f z) (p rM) (f rM) + 2 * deltaG(TYPE('a))) + L"
          apply (intro mono_intros) using * P \<open>rM \<in> {yM..uM}\<close> unfolding Gromov_product_at_def
          by (auto simp add: metric_space_class.dist_commute algebra_simps divide_simps)
        finally have B: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) \<le> Gromov_product_at (f z) (p rM) (f rM)"
          by simp
        have C: "dist (f z) pi_z - L - 2 * deltaG(TYPE('a)) \<le> Gromov_product_at (f z) (p rm) (p rM)"
        proof (cases "dist (f z) (p rm) \<le> dist (f z) (p rM)")
          case True
          have "dist (p rm) (p rM) = abs(dist (f z) (p rm) - dist (f z) (p rM))"
            using proj_setD(1)[OF p] dist_along_geodesic_wrt_endpoint[OF H, of "p rm" "p rM"]
            by (simp add: metric_space_class.dist_commute)
          also have "... = dist (f z) (p rM) - dist (f z) (p rm)"
            using True by auto
          finally have *: "dist (f z) (p rm) = Gromov_product_at (f z) (p rm) (p rM)"
            unfolding Gromov_product_at_def by auto
          have "dist (f z) pi_z \<le> dist (f z) (p rm) + dist (p rm) pi_z"
            by (intro mono_intros)
          also have "... \<le> Gromov_product_at (f z) (p rm) (p rM) + L + 2 * deltaG(TYPE('a))"
            using * P[of rm] \<open>rm \<in> {um..ym}\<close> apply (simp add: metric_space_class.dist_commute)
            using local.delta_nonneg by linarith
          finally show ?thesis by simp
        next
          case False
          have "dist (p rm) (p rM) = abs(dist (f z) (p rm) - dist (f z) (p rM))"
            using proj_setD(1)[OF p] dist_along_geodesic_wrt_endpoint[OF H, of "p rm" "p rM"]
            by (simp add: metric_space_class.dist_commute)
          also have "... = dist (f z) (p rm) - dist (f z) (p rM)"
            using False by auto
          finally have *: "dist (f z) (p rM) = Gromov_product_at (f z) (p rm) (p rM)"
            unfolding Gromov_product_at_def by auto
          have "dist (f z) pi_z \<le> dist (f z) (p rM) + dist (p rM) pi_z"
            by (intro mono_intros)
          also have "... \<le> Gromov_product_at (f z) (p rm) (p rM) + L + 2 * deltaG(TYPE('a))"
            using * P[of rM] \<open>rM \<in> {yM..uM}\<close> apply (simp add: metric_space_class.dist_commute)
            using local.delta_nonneg by linarith
          finally show ?thesis by simp
        qed

        have "Gromov_product_at (f z) (f um) (f uM) - L - 2 * deltaG(TYPE('a)) \<le> Min {Gromov_product_at (f z) (f rm) (p rm), Gromov_product_at (f z) (p rm) (p rM), Gromov_product_at (f z) (p rM) (f rM)}"
          using A B C unfolding Dpi_z by auto
        also have "... \<le> Gromov_product_at (f z) (f rm) (f rM) + 2 * deltaG(TYPE('a))"
          by (intro mono_intros)
        finally show ?thesis
          using \<open>deltaG(TYPE('a)) < delta\<close> by auto
      qed

      text \<open>We have proved the basic facts we will need in the main argument. This argument starts
      here. It is divided in several cases.\<close>
      consider "dm \<le> D + 4 * C \<and> dM \<le> D + 4 * C" | "dm \<ge> D + 4 * C \<and> dM \<le> dm" | "dM \<ge> D + 4 * C \<and> dm \<le> dM"
        by linarith
      then show ?thesis
      proof (cases)
        text \<open>Case 2.1 of the description before the statement: there are points in $f[um, ym]$ and
        in $f[yM, uM]$ which are close to $H$. Then one can conclude directly, without relying
        on the inductive argument, thanks to the quasi-isometry property.\<close>
        case 1
        have I: "Gromov_product_at (f z) (f closestm) (f closestM) \<le> lambda^2 * (D + L / 2 + delta + 11/2 * C) - 6 * delta"
        proof (cases "dist (f closestm) (f closestM) \<le> 12 * delta")
          case True
          have "1/lambda * dist closestm closestM - C \<le> dist (f closestm) (f closestM)"
            using quasi_isometry_onD(2)[OF assms(2)] \<open>closestm \<in> {um..ym}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close>
            \<open>closestM \<in> {yM..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> by auto
          then have "dist closestm closestM \<le> lambda * dist (f closestm) (f closestM) + lambda * C"
            using \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
          also have "... \<le> lambda * (12 * delta) + lambda * C"
            apply (intro mono_intros True) using \<open>lambda \<ge> 1\<close> by auto
          finally have M: "dist closestm closestM \<le> lambda * (12 * delta + C)"
            by (auto simp add: algebra_simps)

          have "2 * Gromov_product_at (f z) (f closestm) (f closestM) \<le> dist (f closestm) (f z) + dist (f z) (f (closestM))"
            unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
          also have "... \<le> (lambda * dist closestm z + C) + (lambda * dist z closestM + C)"
            apply (intro mono_intros quasi_isometry_onD(1)[OF assms(2)])
            using \<open>closestm \<in> {um..ym}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close>
            \<open>closestM \<in> {yM..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> by auto
          also have "... = lambda * dist closestm closestM + 1 * 2 * C"
            unfolding dist_real_def using \<open>closestm \<in> {um..ym}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close>
            \<open>closestM \<in> {yM..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> by (auto simp add: algebra_simps)
          also have "... \<le> lambda * (lambda * (12 * delta + C)) + lambda^2 * 2 * C"
            apply (intro mono_intros M) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
          also have "... = lambda^2 * (24 * delta + 3 * C) - lambda^2 * 12 * delta"
            by (simp add: algebra_simps power2_eq_square)
          also have "... \<le> lambda^2 * ((2 * D + L + 2 * delta) + 11 * C) - 1 * 12 * delta"
            apply (intro mono_intros) using Laux \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>delta > 0\<close> by auto
          finally show ?thesis
            by (auto simp add: divide_simps algebra_simps)
        next
          case False
          have "dist closestm closestM \<le> lambda * (dm + dM + L + 2 * delta + C)"
            using D[OF \<open>closestm \<in> {um..ym}\<close> \<open>closestM \<in> {yM..uM}\<close>] dm_def dM_def by (auto simp add: algebra_simps)
          also have "... \<le> lambda * ((D + 4 * C) + (D + 4 * C) + L + 2 * delta + C)"
            apply (intro mono_intros) using 1 \<open>lambda \<ge> 1\<close> by auto
          also have "... \<le> lambda * (2 * D + L + 2 * delta + 9 * C)"
            using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
          finally have M: "dist closestm closestM \<le> lambda * (2 * D + L + 2 * delta + 9 * C)"
            by (auto simp add: algebra_simps divide_simps metric_space_class.dist_commute)

          have "dist (f closestm) (f z) + dist (f z) (f (closestM)) \<le> (lambda * dist closestm z + C) + (lambda * dist z closestM + C)"
            apply (intro mono_intros quasi_isometry_onD(1)[OF assms(2)])
            using \<open>closestm \<in> {um..ym}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close>
            \<open>closestM \<in> {yM..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> by auto
          also have "... = lambda * dist closestm closestM + 1 * 2 * C"
            unfolding dist_real_def using \<open>closestm \<in> {um..ym}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close>
            \<open>closestM \<in> {yM..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> by (auto simp add: algebra_simps)
          also have "... \<le> lambda * (lambda * (2 * D + L + 2 * delta + 9 * C)) + lambda^2 * 2 * C"
            apply (intro mono_intros M) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
          finally have "dist (f closestm) (f z) + dist (f z) (f closestM) \<le> lambda^2 * (2 * D + L + 2 * delta + 11 * C)"
            by (simp add: algebra_simps power2_eq_square)
          then show ?thesis
            unfolding Gromov_product_at_def using False by (simp add: metric_space_class.dist_commute algebra_simps divide_simps)
        qed
        have "Gromov_product_at (f z) (f um) (f uM) \<le> Gromov_product_at (f z) (f closestm) (f closestM) + 1 * L + 4 * delta + 0 * (1 - exp (- K * (uM - um)))"
          using Rec[OF \<open>closestm \<in> {um..ym}\<close> \<open>closestM \<in> {yM..uM}\<close>] by simp
        also have "... \<le> (lambda^2 * (D + L / 2 + delta + 11/2 * C) - 6 * delta) + lambda^2 * L + 4 * delta + Kmult * (1 - exp (- K * (uM - um)))"
          apply (intro mono_intros I)
          using Laux \<open>lambda \<ge> 1\<close> \<open>delta > 0\<close> \<open>Kmult > 0\<close> \<open>um \<in> {a..z}\<close> \<open>uM \<in> {z..b}\<close> \<open>K > 0\<close> by auto
        finally show ?thesis
          by (simp add: algebra_simps)
        text \<open>End of the easy case 2.1\<close>
      next
        text \<open>Case 2.2: $dm$ is large, i.e., all points in $f[um, ym]$ are far away from $H$. Moreover,
        assume that $dm \geq dM$. Then we will find a pair of points $v$ and $x$ with $um \leq v
        \leq x \leq ym$ satisfying the estimate~\eqref{eq:xvK}. We argue by induction: while we
        have not found such a pair, we can find a point $x_k$ whose projection on $V_k$, the
        neighborhood of size $(2^k-1) dm$ of $H$, is far enough from the projection of $um$, and
        such that all points in between are far enough from $V_k$ so that the corresponding
        projection will have good contraction properties.\<close>
        case 2
        then have I: "D + 4 * C \<le> dm" "dM \<le> dm" by auto
        define V where "V = (\<lambda>k::nat. (\<Union>g\<in>H. cball g ((2^k - 1) * dm)))"
        define QC where "QC = (\<lambda>k::nat. if k = 0 then 0 else 8 * delta)"
        have "QC k \<ge> 0" for k unfolding QC_def using \<open>delta > 0\<close> by auto
        have Q: "quasiconvex (0 + 8 * deltaG(TYPE('a))) (V k)" for k
          unfolding V_def apply (rule quasiconvex_thickening) using geodesic_segmentI[OF H]
          by (auto simp add: quasiconvex_of_geodesic)
        have "quasiconvex (QC k) (V k)" for k
          apply (cases "k = 0")
          apply (simp add: V_def QC_def quasiconvex_of_geodesic geodesic_segmentI[OF H])
          apply (rule quasiconvex_mono[OF _ Q[of k]]) using \<open>deltaG(TYPE('a)) < delta\<close> QC_def by auto
        text \<open>Define $q(k, x)$ to be the projection of $f(x)$ on $V_k$.\<close>
        define q::"nat \<Rightarrow> real \<Rightarrow> 'a" where "q = (\<lambda>k x. geodesic_segment_param {p x--f x} (p x) ((2^k - 1) * dm))"

        text \<open>The inductive argument\<close>
        have Ind_k: "(Gromov_product_at (f z) (f um) (f uM) \<le> lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um))))
              \<or> (\<exists>x \<in> {um..ym}. (\<forall>w \<in> {um..x}. dist (f w) (p w) \<ge> (2^(k+1)-1) * dm) \<and> dist (q k um) (q k x) \<ge> L - 4 * delta + 7 * QC k)" for k
        proof (induction k)
          text \<open>Base case: there is a point far enough from $q 0 um$ on $H$. This is just the point $ym$,
          by construction.\<close>
          case 0
          have *: "\<exists>x\<in> {um..ym}. (\<forall>w \<in> {um..x}. dist (f w) (p w) \<ge> (2^(0+1)-1) * dm) \<and> dist (q 0 um) (q 0 x) \<ge> L - 4 * delta + 7 * QC 0"
          proof (rule bexI[of _ ym], auto simp add: V_def q_def QC_def)
            show "um \<le> ym" using \<open>ym \<in> {um..z}\<close> by auto
            show "L - 4 * delta \<le> dist (p um) (p ym)"
              using ym(2) apply auto using metric_space_class.zero_le_dist[of pi_z "p um"] by linarith
            show "\<And>y. um \<le> y \<Longrightarrow> y \<le> ym \<Longrightarrow> dm \<le> dist (f y) (p y)"
              using dm_def closestm proj_setD(2)[OF p] by auto
          qed
          then show ?case
            by blast
        next
          text \<open>The induction. The inductive assumption claims that, either the desired inequality
          holds, or one can construct a point with good properties. If the desired inequality holds,
          there is nothing left to prove. Otherwise, we can start from this point at step $k$,
          say $x$, and either prove the desired inequality or construct a point with the good
          properties at step $k+1$.\<close>
          case Suck: (Suc k)
          show ?case
          proof (cases "Gromov_product_at (f z) (f um) (f uM) \<le> lambda\<^sup>2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp (- K * (uM - um)))")
            case True
            then show ?thesis by simp
          next
            case False
            then obtain x where x: "x \<in> {um..ym}" "dist (q k um) (q k x) \<ge> L - 4 * delta + 7 * QC k"
                                   "\<And>w. w \<in> {um..x} \<Longrightarrow> dist (f w) (p w) \<ge> (2^(k+1)-1) * dm"
              using Suck.IH by auto

            text \<open>Some auxiliary technical inequalities to be used later on.\<close>
            have aux: "(2 ^ k - 1) * dm \<le> (2*2^k-1) * dm" "0 \<le> 2 * 2 ^ k - (1::real)" "dm \<le> dm * 2 ^ k"
              apply (auto simp add: algebra_simps)
              apply (metis power.simps(2) two_realpow_ge_one)
              using \<open>0 \<le> dm\<close> less_eq_real_def by fastforce
            have "L + C = (L/D) * (D + (D/L) * C)"
              using \<open>L > 0\<close> \<open>D > 0\<close> by (simp add: algebra_simps divide_simps)
            also have "... \<le> (L/D) * (D + 4 * C)"
              apply (intro mono_intros)
              using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C \<ge> 0\<close> \<open>D \<le> 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
            also have "... \<le> (L/D) * dm"
              apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
            finally have "L + C \<le> (L/D) * dm"
              by simp
            moreover have "2 * delta \<le> (2 * delta)/D * dm"
              using I \<open>C \<ge> 0\<close> \<open>delta > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
            ultimately have aux2: "L + C + 2 * delta \<le> ((L + 2 * delta)/D) * dm"
              by (auto simp add: algebra_simps divide_simps)
            have aux3: "(1-alpha) * D + alpha * 2^k * dm \<le> dm * 2^k - C/2 - QC k"
            proof (cases "k = 0")
              case True
              show ?thesis
                 using I \<open>C \<ge> 0\<close> unfolding True QC_def alpha_def by auto
            next
              case False
              have "C/2 + QC k + (1-alpha) * D \<le> 2 * (1-alpha) * dm"
                using I \<open>C \<ge> 0\<close> unfolding QC_def alpha_def using False Laux by auto
              also have "... \<le> 2^k * (1-alpha) * dm"
                apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C \<ge> 0\<close> by auto
              finally show ?thesis
                by (simp add: algebra_simps)
            qed

            text \<open>Construct a point $w$ such that its projection on $V_k$ is close to that of $um$
            and therefore far away from that of $x$. This is just the intermediate value theorem
            (with some care as the closest point projection is not continuous).\<close>
            have "\<exists>w \<in> {um..x}. (dist (q k um) (q k w) \<in> {(9 * delta + 4 * QC k) - 4 * delta - 2 * QC k .. 9 * delta + 4 * QC k})
                    \<and> (\<forall>v \<in> {um..w}. dist (q k um) (q k v) \<le> 9 * delta + 4 * QC k)"
            proof (rule quasi_convex_projection_small_gaps[where ?f = f and ?G = "V k"])
              show "continuous_on {um..x} f"
                apply (rule continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>])
                using \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>ym \<in> {um..z}\<close> \<open>x \<in> {um..ym}\<close> by auto
              show "um \<le> x" using \<open>x \<in> {um..ym}\<close> by auto
              show "quasiconvex (QC k) (V k)" by fact
              show "deltaG TYPE('a) < delta" by fact
              show "9 * delta + 4 * QC k \<in> {4 * delta + 2 * QC k..dist (q k um) (q k x)}"
                using x(2) \<open>delta > 0\<close> \<open>QC k \<ge> 0\<close> Laux by auto
              show "q k w \<in> proj_set (f w) (V k)" if "w \<in> {um..x}" for w
                unfolding V_def q_def apply (rule proj_set_thickening)
                using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
            qed
            then obtain w where w: "w \<in> {um..x}"
                                   "dist (q k um) (q k w) \<in> {(9 * delta + 4 * QC k) - 4 * delta - 2 * QC k .. 9 * delta + 4 * QC k}"
                                   "\<And>v. v \<in> {um..w} \<Longrightarrow> dist (q k um) (q k v) \<le> 9 * delta + 4 * QC k"
              by auto
            text \<open>There are now two cases to be considered: either one can find a point $v$ between
            $um$ and $w$ which is close enough to $H$. Then this point will satisfy~\eqref{eq:xvK},
            and we will be able to prove the desired inequality. Or there is no such point,
            and then $w$ will have the good properties at step $k+1$\<close>
            show ?thesis
            proof (cases "\<exists>v \<in> {um..w}. dist (f v) (p v) \<le> (2^(k+2)-1) * dm")
              case True
              text \<open>First subcase: there is a good point $v$ between $um$ and $w$. This is the
              heart of the argument: we will show that the desired inequality holds.\<close>
              then obtain v where v: "v \<in> {um..w}" "dist (f v) (p v) \<le> (2^(k+2)-1) * dm"
                by auto
              text \<open>Auxiliary basic fact to be used later on.\<close>
              have aux4: "dm * 2 ^ k \<le> infdist (f r) (V k)" if "r \<in> {v..x}" for r
              proof -
                have *: "q k r \<in> proj_set (f r) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening)
                  using aux p[of r] x(3)[of r] that \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
                have "infdist (f r) (V k) = dist (geodesic_segment_param {p r--f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r--f r} (p r) ((2 ^ k - 1) * dm))"
                  using proj_setD(2)[OF *] unfolding q_def by auto
                also have "... = abs(dist (p r) (f r) - (2 ^ k - 1) * dm)"
                  apply (rule geodesic_segment_param(7)[where ?y = "f r"])
                  using x(3)[of r] \<open>r \<in> {v..x}\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
                also have "... = dist (f r) (p r) - (2 ^ k - 1) * dm"
                  using x(3)[of r] \<open>r \<in> {v..x}\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
                finally have "dist (f r) (p r) = infdist (f r) (V k) + (2 ^ k - 1) * dm" by simp
                moreover have "(2^(k+1) - 1) * dm \<le> dist (f r) (p r)"
                  apply (rule x(3)) using \<open>r \<in> {v..x}\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by auto
                ultimately have "(2^(k+1) - 1) * dm \<le> infdist (f r) (V k) + (2 ^ k - 1) * dm"
                  by simp
                then show ?thesis by (auto simp add: algebra_simps)
              qed

              text \<open>Substep 1: We can control the distance from $f(v)$ to $f(closestM)$ in terms of the distance
              of the distance of $f(v)$ to $H$, i.e., by $2^k dm$. The same control follows
              for $closestM - v$ thanks to the quasi-isometry property. Then, we massage this
              inequality to put it in the form we will need, as an upper bound on $(x-v) \exp(-2^k dm)$.\<close>
              have "infdist (f v) H \<le> (2^(k+2)-1) * dm"
                using v proj_setD(2)[OF p[of v]] by auto
              have "dist v closestM \<le> lambda * (infdist (f v) H + (L + C + 2 * delta) + infdist (f closestM) H)"
                apply (rule D)
                using \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> \<open>closestM \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> by auto
              also have "... \<le> lambda * ((2^(k+2)-1) * dm + 1 * (L + C + 2 * delta) + dM)"
                apply (intro mono_intros \<open>infdist (f v) H \<le> (2^(k+2)-1) * dm\<close>)
                using dM_def \<open>lambda \<ge> 1\<close> \<open>L > 0\<close> \<open>C \<ge> 0\<close> \<open>delta > 0\<close> by (auto simp add: metric_space_class.dist_commute)
              also have "... \<le> lambda * ((2^(k+2)-1) * dm + 2^k * (((L + 2 * delta)/D) * dm) + dm)"
                apply (intro mono_intros) using I \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>delta > 0\<close> \<open>L > 0\<close> aux2 by auto
              also have "... = lambda * 2^k * (4 + (L + 2 * delta)/D) * dm"
                by (simp add: algebra_simps)
              finally have *: "dist v closestM / (lambda * (4 + (L + 2 * delta)/D)) \<le> 2^k * dm"
                using \<open>lambda \<ge> 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>delta > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)
              text \<open>We reformulate this control inside of an exponential, as this is the form we
              will use later on.\<close>
              have "exp(- (alpha * (2^k * dm) * ln 2 / (5 * delta))) \<le> exp(-(alpha * (dist v closestM / (lambda * (4 + (L + 2 * delta)/D))) * ln 2 / (5 * delta)))"
                apply (intro mono_intros *) using alphaaux \<open>delta > 0\<close> by auto
              also have "... = exp(-K * dist v closestM)"
                unfolding K_def by (simp add: divide_simps)
              also have "... = exp(-K * (closestM - v))"
                unfolding dist_real_def using \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>yM \<in> {z..uM}\<close> \<open>closestM \<in> {yM..uM}\<close> \<open>K > 0\<close> by auto
              finally have "exp(- (alpha * (2^k * dm) * ln 2 / (5 * delta))) \<le> exp(-K * (closestM - v))"
                by simp
              text \<open>Plug in $x-v$ to get the final form of this inequality.\<close>
              then have "K * (x - v) * exp(- (alpha * (2^k * dm) * ln 2 / (5 * delta))) \<le> K * (x - v) * exp(-K * (closestM - v))"
                apply (rule mult_left_mono)
                using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>K > 0\<close> by auto
              also have "... = ((1 + K * (x - v)) - 1) * exp(- K * (closestM - v))"
                by (auto simp add: algebra_simps)
              also have "... \<le> (exp (K * (x - v)) - 1) * exp(-K * (closestM - v))"
                by (intro mono_intros, auto)
              also have "... = exp(-K * (closestM - x)) - exp(-K * (closestM - v))"
                by (simp add: algebra_simps mult_exp_exp)
              also have "... \<le> exp(-K * (closestM - x)) - exp(-K * (uM - um))"
                using \<open>K > 0\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>yM \<in> {z..uM}\<close> \<open>closestM \<in> {yM..uM}\<close> by auto
              finally have B: "(x - v) * exp(- alpha * 2^k * dm * ln 2 / (5 * delta)) \<le>
                                  (exp(-K * (closestM - x)) - exp(-K * (uM-um)))/K"
                using \<open>K > 0\<close> by (auto simp add: divide_simps algebra_simps)
              text \<open>End of substep 1\<close>

              text \<open>Substep 2: The projections of $f(v)$ and $f(x)$ on the cylinder $V_k$ are well separated,
              by construction. This implies that $v$ and $x$ themselves are well separated, thanks
              to the exponential contraction property of the projection on the quasi-convex set $V_k$.
              This leads to a uniform lower bound for $(x-v) \exp(-2^k dm)$, which has been upper bounded
              in Substep 1.\<close>
              have "L - 4 * delta + 7 * QC k \<le> dist (q k um) (q k x)"
                using x by simp
              also have "... \<le> dist (q k um) (q k v) + dist (q k v) (q k x)"
                by (intro mono_intros)
              also have "... \<le> (9 * delta + 4 * QC k) + dist (q k v) (q k x)"
                using w(3)[of v] \<open>v \<in> {um..w}\<close> by auto
              finally have "L - 13 * delta + 3 * QC k \<le> dist (q k v) (q k x)"
                by simp
              also have "... \<le> 3 * QC k + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * ln 2 / (5 * delta)))"
              proof (cases "k = 0")
                text \<open>We use different statements for the projection in the case $k = 0$ (projection on
                a geodesic) and $k > 0$ (projection on a quasi-convex set) as the bounds are better in
                the first case, which is the most important one for the final value of the constant.\<close>
                case True
                have "dist (q k v) (q k x) \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-(dm * 2^k - C/2) * ln 2 / (5 * delta)))"
                proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
                  show "geodesic_segment (V k)" unfolding True V_def using geodesic_segmentI[OF H] by auto
                  show "v \<le> x" using \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by auto
                  show "q k v \<in> proj_set (f v) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of v] x(3)[of v] \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "q k x \<in> proj_set (f x) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of x] x(3)[of x] \<open>w \<in> {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "15/2 * delta + C/2 \<le> dm * 2^k"
                    apply (rule order_trans[of _ dm])
                    using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux unfolding QC_def by auto
                  show "deltaG TYPE('a) < delta" by fact
                  show "\<And>t. t \<in> {v..x} \<Longrightarrow> dm * 2 ^ k \<le> infdist (f t) (V k)"
                    using aux4 by auto
                  show "0 \<le> C" "0 \<le> lambda" using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
                  show "dist (f x1) (f x2) \<le> lambda * dist x1 x2 + C" if "x1 \<in> {v..x}" "x2 \<in> {v..x}" for x1 x2
                    using quasi_isometry_onD(1)[OF assms(2)] that \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> by auto
                qed
                then show ?thesis unfolding QC_def True by auto
              next
                case False
                have "dist (q k v) (q k x) \<le> 2 * QC k + 8 * delta + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-(dm * 2^k - QC k -C/2) * ln 2 / (5 * delta)))"
                proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
                  show "quasiconvex (QC k) (V k)" by fact
                  show "v \<le> x" using \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by auto
                  show "q k v \<in> proj_set (f v) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of v] x(3)[of v] \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "q k x \<in> proj_set (f x) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of x] x(3)[of x] \<open>w \<in> {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "15/2 * delta + QC k + C/2 \<le> dm * 2^k"
                    apply (rule order_trans[of _ dm])
                    using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux unfolding QC_def by auto
                  show "deltaG TYPE('a) < delta" by fact
                  show "\<And>t. t \<in> {v..x} \<Longrightarrow> dm * 2 ^ k \<le> infdist (f t) (V k)"
                    using aux4 by auto
                  show "0 \<le> C" "0 \<le> lambda" using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
                  show "dist (f x1) (f x2) \<le> lambda * dist x1 x2 + C" if "x1 \<in> {v..x}" "x2 \<in> {v..x}" for x1 x2
                    using quasi_isometry_onD(1)[OF assms(2)] that \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>z \<in> {a..b}\<close> by auto
                qed
                then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
              qed
              finally have "L - 13 * delta \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * ln 2 / (5 * delta)))"
                by auto
              then have "L - 13 * delta \<le> (4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-(dm * 2^k - C/2 - QC k) * ln 2 / (5 * delta))"
                using \<open>delta > deltaG(TYPE('a))\<close> Laux by auto
              text \<open>We separate the exponential gain coming from the contraction into two parts, one
              to be spent to improve the constant, and one for the inductive argument.\<close>
              also have "... \<le> (4 * exp(1/2 * ln 2)) * lambda * (x - v) * exp(-((1-alpha) * D + alpha * 2^k * dm) * ln 2 / (5 * delta))"
                apply (intro mono_intros) using aux3 \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by auto
              also have "... = (4 * exp(1/2 * ln 2)) * lambda * (x - v) * (exp(-(1-alpha) * D * ln 2 / (5 * delta)) * exp(-alpha * 2^k * dm * ln 2 / (5 * delta)))"
                unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
              finally have A: "L - 13 * delta \<le> (4 * exp(1/2 * ln 2)) * lambda * exp(-(1-alpha) * D * ln 2 / (5 * delta)) * ((x - v) * exp(-alpha * 2^k * dm * ln 2 / (5 * delta)))"
                by (simp add: algebra_simps)
              text \<open>This is the end of the second substep.\<close>

              text \<open>Use the second substep to show that $x-v$ is bounded below, and therefore
              that $closestM - x$ (the endpoints of the new geodesic we want to consider in the
              inductive argument) are quantitatively closer than $uM - um$, which means that we
              will be able to use the inductive assumption over this new geodesic.\<close>
              also have "... \<le> (4 * exp(1/2 * ln 2)) * lambda * exp 0 * ((x - v) * exp 0)"
                apply (intro mono_intros) using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> alphaaux \<open>D > 0\<close> \<open>C \<ge> 0\<close> I
                by (auto simp add: divide_simps mult_nonpos_nonneg)
              also have "... = (4 * exp(1/2 * ln 2)) * lambda * (x-v)"
                by simp
              also have "... \<le> 20 * lambda * (x - v)"
                apply (intro mono_intros, approximation 10)
                using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {um..w}\<close> \<open>w \<in> {um..x}\<close> by auto
              finally have "x - v \<ge> (1/4) * delta / lambda"
                using \<open>lambda \<ge> 1\<close> L_def \<open>delta > 0\<close> by (simp add: divide_simps algebra_simps)
              then have "closestM - x + (1/4) * delta / lambda \<le> closestM - v"
                by simp
              also have "... \<le> uM - um"
                using \<open>closestM \<in> {yM..uM}\<close> \<open>v \<in> {um..w}\<close> by auto
              also have "... \<le> Suc n * (1/4) * delta / lambda" by fact
              finally have "closestM - x \<le> n * (1/4) * delta / lambda"
                unfolding Suc_eq_plus1 by (auto simp add: algebra_simps add_divide_distrib)

              text \<open>Conclusion of the proof: combine the lower bound of the second substep with
              the upper bound of the first substep to get a definite gain when one goes from
              the old geodesic to the new one. Then, apply the inductive assumption to the new one
              to conclude the desired inequality for the old one.\<close>
              have "L + 4 * delta = ((L + 4 * delta)/(L - 13 * delta)) * (L - 13 * delta)"
                using Laux \<open>delta > 0\<close> by (simp add: algebra_simps divide_simps)
              also have "... \<le> ((L + 4 * delta)/(L - 13 * delta)) * ((4 * exp(1/2 * ln 2)) * lambda * exp (- (1 - alpha) * D * ln 2 / (5 * delta)) * ((x - v) * exp (- alpha * 2 ^ k * dm * ln 2 / (5 * delta))))"
                apply (rule mult_left_mono) using A Laux \<open>delta > 0\<close> by (auto simp add: divide_simps)
              also have "... \<le> ((L + 4 * delta)/(L - 13 * delta)) * ((4 * exp(1/2 * ln 2)) * lambda * exp (- (1 - alpha) * D * ln 2 / (5 * delta)) * ((exp(-K * (closestM - x)) - exp(-K * (uM - um)))/K))"
                apply (intro mono_intros B) using Laux \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
              finally have C: "L + 4 * delta \<le> Kmult * (exp(-K * (closestM - x)) - exp(-K * (uM - um)))"
                unfolding Kmult_def by auto

              have "Gromov_product_at (f z) (f um) (f uM) \<le> Gromov_product_at (f z) (f x) (f closestM) + (L + 4 * delta)"
                apply (rule Rec) using \<open>closestM \<in> {yM..uM}\<close> \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> by auto
              also have "... \<le> (lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (closestM - x)))) + (Kmult * (exp(-K * (closestM - x)) - exp(-K * (uM-um))))"
                apply (intro mono_intros C Suc.IH)
                using \<open>x \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> \<open>closestM \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>closestM - x \<le> n * (1/4) * delta / lambda\<close> by auto
              also have "... = (lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um))))"
                unfolding K_def by (simp add: algebra_simps)
              finally show ?thesis by auto
              text \<open>End of the first subcase, when there is a good point $v$ between $um$ and $w$.\<close>
            next
              case False
              text \<open>Second subcase: between $um$ and $w$, all points are far away from $V_k$. We
              will show that this implies that $w$ is admissible for the step $k+1$.\<close>
              have "\<exists>w\<in>{um..ym}. (\<forall>v\<in>{um..w}. (2 ^ (Suc k + 1) - 1) * dm \<le> dist (f v) (p v)) \<and> L - 4 * delta + 7 * QC (Suc k) \<le> dist (q (Suc k) um) (q (Suc k) w)"
              proof (rule bexI[of _ w], auto)
                show "um \<le> w" "w \<le> ym" using \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> by auto
                show "(4 * 2 ^ k - 1) * dm \<le> dist (f x) (p x)" if "um \<le> x" "x \<le> w" for x
                  using False \<open>dm \<ge> 0\<close> that by force

                have "dist (q k um) (q (k+1) um) = 2^k * dm"
                  unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f um"])
                  using x(3)[of um] \<open>x \<in> {um..ym}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
                have "dist (q k w) (q (k+1) w) = 2^k * dm"
                  unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f w"])
                  using x(3)[of w] \<open>w \<in> {um..x}\<close> \<open>x \<in> {um..ym}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
                have i: "q k um \<in> proj_set (q (k+1) um) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f um"])
                  using p x(3)[of um] \<open>x \<in> {um..ym}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)
                have j: "q k w \<in> proj_set (q (k+1) w) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f w"])
                  using p x(3)[of w] \<open>x \<in> {um..ym}\<close> \<open>w \<in> {um..x}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)

                have "5 * delta + 2 * QC k \<le> dist (q k um) (q k w)" using w(2) by simp
                also have "... \<le> max (5 * deltaG(TYPE('a)) + 2 * QC k)
                                      (dist (q (k + 1) um) (q (k + 1) w) - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k)"
                  by (rule proj_along_quasiconvex_contraction[OF \<open>quasiconvex (QC k) (V k)\<close> i j])
                finally have "5 * delta + 2 * QC k \<le> dist (q (k + 1) um) (q (k + 1) w) - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                then have "0 \<le> dist (q (k + 1) um) (q (k + 1) w) + 5 * delta + 2 * QC k - dist (q k um) (q (k + 1) um) - dist (q k w) (q (k + 1) w)"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                also have "... = dist (q (k + 1) um) (q (k + 1) w) + 5 * delta + 2 * QC k - 2^(k+1) * dm"
                  by (simp only: \<open>dist (q k w) (q (k+1) w) = 2^k * dm\<close> \<open>dist (q k um) (q (k+1) um) = 2^k * dm\<close>, auto)
                finally have *: "2^(k+1) * dm - 5 * delta - 2 * QC k \<le> dist (q (k+1) um) (q (k+1) w)"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                have "L - 4 * delta + 7 * QC (k+1) \<le> 2 * dm - 5 * delta - 2 * QC k"
                  unfolding QC_def L_def using \<open>delta > 0\<close> Laux I \<open>C \<ge> 0\<close> by auto
                also have "... \<le> 2^(k+1) * dm - 5 * delta - 2 * QC k"
                  using aux by (auto simp add: algebra_simps)
                finally show "L - 4 * delta + 7 * QC (Suc k) \<le> dist (q (Suc k) um) (q (Suc k) w)"
                  using * by auto
              qed
              then show ?thesis
                by simp
            qed
          qed
        qed
        text \<open>This is the end of the main induction over $k$. To conclude, choose $k$ large enough
        so that the second alternative in this induction is impossible. It follows that the first
        alternative holds, i.e., the desired inequality is true.\<close>
        have "dm > 0" using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux by auto
        have "\<exists>k. 2^k > dist (f um) (p um)/dm + 1"
          by (simp add: real_arch_pow)
        then obtain k where "2^k > dist (f um) (p um)/dm + 1"
          by blast
        then have "dist (f um) (p um) < (2^k - 1) * dm"
          using \<open>dm > 0\<close> by (auto simp add: divide_simps algebra_simps)
        also have "... \<le> (2^(Suc k) - 1) * dm"
          by (intro mono_intros, auto)
        finally have "\<not>((2 ^ (k + 1) - 1) * dm \<le> dist (f um) (p um))"
          by simp
        then show "Gromov_product_at (f z) (f um) (f uM) \<le> lambda\<^sup>2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp (- K * (uM - um)))"
          using Ind_k[of k] by auto
        text \<open>end of the case where $D + 4 * C \leq dm$ and $dM \leq dm$.\<close>
      next
        case 3
        text \<open>This is the exact copy of the previous case, except that the roles of the points before
        and after $z$ are exchanged. In a perfect world, one would use a lemma subsuming both cases,
        but in practice copy-paste seems to work better here as there are two many details to be
        changed regarding the direction of inequalities.\<close>
        then have I: "D + 4 * C \<le> dM" "dm \<le> dM" by auto
        define V where "V = (\<lambda>k::nat. (\<Union>g\<in>H. cball g ((2^k - 1) * dM)))"
        define QC where "QC = (\<lambda>k::nat. if k = 0 then 0 else 8 * delta)"
        have "QC k \<ge> 0" for k unfolding QC_def using \<open>delta > 0\<close> by auto
        have Q: "quasiconvex (0 + 8 * deltaG(TYPE('a))) (V k)" for k
          unfolding V_def apply (rule quasiconvex_thickening) using geodesic_segmentI[OF H]
          by (auto simp add: quasiconvex_of_geodesic)
        have "quasiconvex (QC k) (V k)" for k
          apply (cases "k = 0")
          apply (simp add: V_def QC_def quasiconvex_of_geodesic geodesic_segmentI[OF H])
          apply (rule quasiconvex_mono[OF _ Q[of k]]) using \<open>deltaG(TYPE('a)) < delta\<close> QC_def by auto
        define q::"nat \<Rightarrow> real \<Rightarrow> 'a" where "q = (\<lambda>k x. geodesic_segment_param {p x--f x} (p x) ((2^k - 1) * dM))"

        have Ind_k: "(Gromov_product_at (f z) (f um) (f uM) \<le> lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um))))
              \<or> (\<exists>x \<in> {yM..uM}. (\<forall>y \<in> {x..uM}. dist (f y) (p y) \<ge> (2^(k+1)-1) * dM) \<and> dist (q k uM) (q k x) \<ge> L - 4 * delta + 7 * QC k)" for k
        proof (induction k)
          case 0
          have *: "\<exists>x\<in> {yM..uM}. (\<forall>y \<in> {x..uM}. dist (f y) (p y) \<ge> (2^(0+1)-1) * dM) \<and> dist (q 0 uM) (q 0 x) \<ge> L - 4 * delta + 7 * QC 0"
          proof (rule bexI[of _ yM], auto simp add: V_def q_def QC_def)
            show "yM \<le> uM" using \<open>yM \<in> {z..uM}\<close> by auto
            show "L -4 * delta \<le> dist (p uM) (p yM)"
              using yM(2) apply auto using metric_space_class.zero_le_dist[of pi_z "p uM"] by linarith
            show "\<And>y. y \<le> uM \<Longrightarrow> yM \<le> y \<Longrightarrow> dM \<le> dist (f y) (p y)"
              using dM_def closestM proj_setD(2)[OF p] by auto
          qed
          then show ?case
            by blast
        next
          case Suck: (Suc k)
          show ?case
          proof (cases "Gromov_product_at (f z) (f um) (f uM) \<le> lambda\<^sup>2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp (- K * (uM - um)))")
            case True
            then show ?thesis by simp
          next
            case False
            then obtain x where x: "x \<in> {yM..uM}" "dist (q k uM) (q k x) \<ge> L - 4 * delta + 7 * QC k"
                                   "\<And>w. w \<in> {x..uM} \<Longrightarrow> dist (f w) (p w) \<ge> (2^(k+1)-1) * dM"
              using Suck.IH by auto
            have aux: "(2 ^ k - 1) * dM \<le> (2*2^k-1) * dM" "0 \<le> 2 * 2 ^ k - (1::real)" "dM \<le> dM * 2 ^ k"
              apply (auto simp add: algebra_simps)
              apply (metis power.simps(2) two_realpow_ge_one)
              using \<open>0 \<le> dM\<close> less_eq_real_def by fastforce
            have "L + C = (L/D) * (D + (D/L) * C)"
              using \<open>L > 0\<close> \<open>D > 0\<close> by (simp add: algebra_simps divide_simps)
            also have "... \<le> (L/D) * (D + 4 * C)"
              apply (intro mono_intros)
              using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C \<ge> 0\<close> \<open>D \<le> 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
            also have "... \<le> (L/D) * dM"
              apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
            finally have "L + C \<le> (L/D) * dM"
              by simp
             moreover have "2 * delta \<le> (2 * delta)/D * dM"
              using I \<open>C \<ge> 0\<close> \<open>delta > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
            ultimately have aux2: "L + C + 2 * delta \<le> ((L + 2 * delta)/D) * dM"
              by (auto simp add: algebra_simps divide_simps)
            have aux3: "(1-alpha) * D + alpha * 2^k * dM \<le> dM * 2^k - C/2 - QC k"
            proof (cases "k = 0")
              case True
              show ?thesis
                 using I \<open>C \<ge> 0\<close> unfolding True QC_def alpha_def by auto
            next
              case False
              have "C/2 + QC k + (1-alpha) * D \<le> 2 * (1-alpha) * dM"
                using I \<open>C \<ge> 0\<close> unfolding QC_def alpha_def using False Laux by auto
              also have "... \<le> 2^k * (1-alpha) * dM"
                apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C \<ge> 0\<close> by auto
              finally show ?thesis
                by (simp add: algebra_simps)
            qed

            have "\<exists>w \<in> {x..uM}. (dist (q k uM) (q k w) \<in> {(9 * delta + 4 * QC k) - 4 * delta - 2 * QC k .. 9 * delta + 4 * QC k})
                    \<and> (\<forall>v \<in> {w..uM}. dist (q k uM) (q k v) \<le> 9 * delta + 4 * QC k)"
            proof (rule quasi_convex_projection_small_gaps'[where ?f = f and ?G = "V k"])
              show "continuous_on {x..uM} f"
                apply (rule continuous_on_subset[OF \<open>continuous_on {a..b} f\<close>])
                using \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>yM \<in> {z..uM}\<close> \<open>x \<in> {yM..uM}\<close> by auto
              show "x \<le> uM" using \<open>x \<in> {yM..uM}\<close> by auto
              show "quasiconvex (QC k) (V k)" by fact
              show "deltaG TYPE('a) < delta" by fact
              show "9 * delta + 4 * QC k \<in> {4 * delta + 2 * QC k..dist (q k x) (q k uM)}"
                using x(2) \<open>delta > 0\<close> \<open>QC k \<ge> 0\<close> Laux by (auto simp add: metric_space_class.dist_commute)
              show "q k w \<in> proj_set (f w) (V k)" if "w \<in> {x..uM}" for w
                unfolding V_def q_def apply (rule proj_set_thickening)
                using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
            qed
            then obtain w where w: "w \<in> {x..uM}"
                                   "dist (q k uM) (q k w) \<in> {(9 * delta + 4 * QC k) - 4 * delta - 2 * QC k .. 9 * delta + 4 * QC k}"
                                   "\<And>v. v \<in> {w..uM} \<Longrightarrow> dist (q k uM) (q k v) \<le> 9 * delta + 4 * QC k"
              by auto
            show ?thesis
            proof (cases "\<exists>v \<in> {w..uM}. dist (f v) (p v) \<le> (2^(k+2)-1) * dM")
              case True
              then obtain v where v: "v \<in> {w..uM}" "dist (f v) (p v) \<le> (2^(k+2)-1) * dM"
                by auto
              have aux4: "dM * 2 ^ k \<le> infdist (f r) (V k)" if "r \<in> {x..v}" for r
              proof -
                have *: "q k r \<in> proj_set (f r) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening)
                  using aux p[of r] x(3)[of r] that \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
                have "infdist (f r) (V k) = dist (geodesic_segment_param {p r--f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r--f r} (p r) ((2 ^ k - 1) * dM))"
                  using proj_setD(2)[OF *] unfolding q_def by auto
                also have "... = abs(dist (p r) (f r) - (2 ^ k - 1) * dM)"
                  apply (rule geodesic_segment_param(7)[where ?y = "f r"])
                  using x(3)[of r] \<open>r \<in> {x..v}\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
                also have "... = dist (f r) (p r) - (2 ^ k - 1) * dM"
                  using x(3)[of r] \<open>r \<in> {x..v}\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
                finally have "dist (f r) (p r) = infdist (f r) (V k) + (2 ^ k - 1) * dM" by simp
                moreover have "(2^(k+1) - 1) * dM \<le> dist (f r) (p r)"
                  apply (rule x(3)) using \<open>r \<in> {x..v}\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by auto
                ultimately have "(2^(k+1) - 1) * dM \<le> infdist (f r) (V k) + (2 ^ k - 1) * dM"
                  by simp
                then show ?thesis by (auto simp add: algebra_simps)
              qed

              have "infdist (f v) H \<le> (2^(k+2)-1) * dM"
                using v proj_setD(2)[OF p[of v]] by auto
              have "dist closestm v \<le> lambda * (infdist (f closestm) H + (L + C + 2 * delta) + infdist (f v) H)"
                apply (rule D)
                using \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> \<open>closestm \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>um \<in> {a..z}\<close> by auto
              also have "... \<le> lambda * (dm + 1 * (L + C + 2 * delta) + (2^(k+2)-1) * dM)"
                apply (intro mono_intros \<open>infdist (f v) H \<le> (2^(k+2)-1) * dM\<close>)
                using dm_def \<open>lambda \<ge> 1\<close> \<open>L > 0\<close> \<open>C \<ge> 0\<close> \<open>delta > 0\<close> by (auto simp add: metric_space_class.dist_commute)
              also have "... \<le> lambda * (dM + 2^k * (((L + 2 * delta)/D) * dM) + (2^(k+2)-1) * dM)"
                apply (intro mono_intros) using I \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>delta > 0\<close> \<open>L > 0\<close> aux2 by auto
              also have "... = lambda * 2^k * (4 + (L + 2 * delta)/D) * dM"
                by (simp add: algebra_simps)
              finally have *: "dist closestm v / (lambda * (4 + (L + 2 * delta)/D)) \<le> 2^k * dM"
                using \<open>lambda \<ge> 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>delta > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)

              have "exp(- (alpha * (2^k * dM) * ln 2 / (5 * delta))) \<le> exp(-(alpha * (dist closestm v / (lambda * (4 + (L + 2 * delta)/D))) * ln 2 / (5 * delta)))"
                apply (intro mono_intros *) using alphaaux \<open>delta > 0\<close> by auto
              also have "... = exp(-K * dist closestm v)"
                unfolding K_def by (simp add: divide_simps)
              also have "... = exp(-K * (v - closestm))"
                unfolding dist_real_def using \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>ym \<in> {um..z}\<close> \<open>closestm \<in> {um..ym}\<close> \<open>K > 0\<close> by auto
              finally have "exp(- (alpha * (2^k * dM) * ln 2 / (5 * delta))) \<le> exp(-K * (v - closestm))"
                by simp
              then have "K * (v - x) * exp(- (alpha * (2^k * dM) * ln 2 / (5 * delta))) \<le> K * (v - x) * exp(-K * (v - closestm))"
                apply (rule mult_left_mono)
                using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>K > 0\<close> by auto
              also have "... = ((1 + K * (v - x)) - 1) * exp(- K * (v - closestm))"
                by (auto simp add: algebra_simps)
              also have "... \<le> (exp (K * (v - x)) - 1) * exp(-K * (v - closestm))"
                by (intro mono_intros, auto)
              also have "... = exp(-K * (x - closestm)) - exp(-K * (v - closestm))"
                by (simp add: algebra_simps mult_exp_exp)
              also have "... \<le> exp(-K * (x - closestm)) - exp(-K * (uM - um))"
                using \<open>K > 0\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>ym \<in> {um..z}\<close> \<open>closestm \<in> {um..ym}\<close> by auto
              finally have B: "(v - x) * exp(- alpha * 2^k * dM * ln 2 / (5 * delta)) \<le>
                                  (exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K"
                using \<open>K > 0\<close> by (auto simp add: divide_simps algebra_simps)

              text \<open>The projections of $f(v)$ and $f(x)$ on the cylinder $V_k$ are well separated,
              by construction. This implies that $v$ and $x$ themselves are well separated.\<close>
              have "L - 4 * delta + 7 * QC k \<le> dist (q k uM) (q k x)"
                using x by simp
              also have "... \<le> dist (q k uM) (q k v) + dist (q k v) (q k x)"
                by (intro mono_intros)
              also have "... \<le> (9 * delta + 4 * QC k) + dist (q k v) (q k x)"
                using w(3)[of v] \<open>v \<in> {w..uM}\<close> by auto
              finally have "L - 13 * delta + 3 * QC k \<le> dist (q k x) (q k v)"
                by (simp add: metric_space_class.dist_commute)
              also have "... \<le> 3 * QC k + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * ln 2 / (5 * delta)))"
              proof (cases "k = 0")
                case True
                have "dist (q k x) (q k v) \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-(dM * 2^k - C/2) * ln 2 / (5 * delta)))"
                proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
                  show "geodesic_segment (V k)" unfolding V_def True using geodesic_segmentI[OF H] by auto
                  show "x \<le> v" using \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by auto
                  show "q k v \<in> proj_set (f v) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of v] x(3)[of v] \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "q k x \<in> proj_set (f x) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of x] x(3)[of x] \<open>w \<in> {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "15/2 * delta + C/2 \<le> dM * 2^k"
                    using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux unfolding QC_def True by auto
                  show "deltaG TYPE('a) < delta" by fact
                  show "\<And>t. t \<in> {x..v} \<Longrightarrow> dM * 2 ^ k \<le> infdist (f t) (V k)"
                    using aux4 by auto
                  show "0 \<le> C" "0 \<le> lambda" using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
                  show "dist (f x1) (f x2) \<le> lambda * dist x1 x2 + C" if "x1 \<in> {x..v}" "x2 \<in> {x..v}" for x1 x2
                    using quasi_isometry_onD(1)[OF assms(2)] that \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> by auto
                qed
                then show ?thesis unfolding QC_def True by auto
              next
                case False
                have "dist (q k x) (q k v) \<le> 2 * QC k + 8 * delta + max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-(dM * 2^k - QC k - C/2) * ln 2 / (5 * delta)))"
                proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
                  show "quasiconvex (QC k) (V k)" by fact
                  show "x \<le> v" using \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by auto
                  show "q k v \<in> proj_set (f v) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of v] x(3)[of v] \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "q k x \<in> proj_set (f x) (V k)"
                    unfolding q_def V_def apply (rule proj_set_thickening)
                    using aux p[of x] x(3)[of x] \<open>w \<in> {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
                  show "15/2 * delta + QC k + C/2 \<le> dM * 2^k"
                    apply (rule order_trans[of _ dM])
                    using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux unfolding QC_def by auto
                  show "deltaG TYPE('a) < delta" by fact
                  show "\<And>t. t \<in> {x..v} \<Longrightarrow> dM * 2 ^ k \<le> infdist (f t) (V k)"
                    using aux4 by auto
                  show "0 \<le> C" "0 \<le> lambda" using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
                  show "dist (f x1) (f x2) \<le> lambda * dist x1 x2 + C" if "x1 \<in> {x..v}" "x2 \<in> {x..v}" for x1 x2
                    using quasi_isometry_onD(1)[OF assms(2)] that \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>uM \<in> {z..b}\<close> \<open>z \<in> {a..b}\<close> by auto
                qed
                then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
              qed
              finally have "L - 13 * delta \<le> max (5 * deltaG(TYPE('a))) ((4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * ln 2 / (5 * delta)))"
                by auto
              then have "L - 13 * delta \<le> (4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * ln 2 / (5 * delta))"
                using \<open>delta > deltaG(TYPE('a))\<close> Laux by auto
              also have "... \<le> (4 * exp(1/2 * ln 2)) * lambda * (v - x) * exp(-((1-alpha) * D + alpha * 2^k * dM) * ln 2 / (5 * delta))"
                apply (intro mono_intros) using aux3 \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by auto
              also have "... = (4 * exp(1/2 * ln 2)) * lambda * (v - x) * (exp(-(1-alpha) * D * ln 2 / (5 * delta)) * exp(-alpha * 2^k * dM * ln 2 / (5 * delta)))"
                unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
              finally have A: "L - 13 * delta \<le> (4 * exp(1/2 * ln 2)) * lambda * exp(-(1-alpha) * D * ln 2 / (5 * delta)) * ((v - x) * exp(-alpha * 2^k * dM * ln 2 / (5 * delta)))"
                by (simp add: algebra_simps)

              also have "... \<le> (4 * exp(1/2 * ln 2)) * lambda * exp 0 * ((v - x) * exp 0)"
                apply (intro mono_intros) using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> alphaaux \<open>D > 0\<close> \<open>C \<ge> 0\<close> I
                by (auto simp add: divide_simps mult_nonpos_nonneg)
              also have "... = (4 * exp(1/2 * ln 2)) * lambda * (v - x)"
                by simp
              also have "... \<le> 20 * lambda * (v - x)"
                apply (intro mono_intros, approximation 10)
                using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> \<open>v \<in> {w..uM}\<close> \<open>w \<in> {x..uM}\<close> by auto
              finally have "v - x \<ge> (1/4) * delta / lambda"
                using \<open>lambda \<ge> 1\<close> L_def \<open>delta > 0\<close> by (simp add: divide_simps algebra_simps)
              then have "x - closestm + (1/4) * delta / lambda \<le> v - closestm"
                by simp
              also have "... \<le> uM - um"
                using \<open>closestm \<in> {um..ym}\<close> \<open>v \<in> {w..uM}\<close> by auto
              also have "... \<le> Suc n * (1/4) * delta / lambda" by fact
              finally have "x - closestm \<le> n * (1/4) * delta / lambda"
                unfolding Suc_eq_plus1 by (auto simp add: algebra_simps add_divide_distrib)

              have "L + 4 * delta = ((L + 4 * delta)/(L - 13 * delta)) * (L - 13 * delta)"
                using Laux \<open>delta > 0\<close> by (simp add: algebra_simps divide_simps)
              also have "... \<le> ((L + 4 * delta)/(L - 13 * delta)) * ((4 * exp(1/2 * ln 2)) * lambda * exp (- (1 - alpha) * D * ln 2 / (5 * delta)) * ((v - x) * exp (- alpha * 2 ^ k * dM * ln 2 / (5 * delta))))"
                apply (rule mult_left_mono) using A Laux \<open>delta > 0\<close> by (auto simp add: divide_simps)
              also have "... \<le> ((L + 4 * delta)/(L - 13 * delta)) * ((4 * exp(1/2 * ln 2)) * lambda * exp (- (1 - alpha) * D * ln 2 / (5 * delta)) * ((exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K))"
                apply (intro mono_intros B) using Laux \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
              finally have C: "L + 4 * delta \<le> Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM - um)))"
                unfolding Kmult_def by argo

              have "Gromov_product_at (f z) (f um) (f uM) \<le> Gromov_product_at (f z) (f closestm) (f x) + (L + 4 * delta)"
                apply (rule Rec) using \<open>closestm \<in> {um..ym}\<close> \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> by auto
              also have "... \<le> (lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (x - closestm)))) + (Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM-um))))"
                apply (intro mono_intros C Suc.IH)
                using \<open>x \<in> {yM..uM}\<close> \<open>yM \<in> {z..uM}\<close> \<open>um \<in> {a..z}\<close> \<open>closestm \<in> {um..ym}\<close> \<open>ym \<in> {um..z}\<close> \<open>uM \<in> {z..b}\<close> \<open>x - closestm \<le> n * (1/4) * delta / lambda\<close> by auto
              also have "... = (lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(- K * (uM - um))))"
                unfolding K_def by (simp add: algebra_simps)
              finally show ?thesis by auto
            next
              case False
              have "\<exists>w\<in>{yM..uM}. (\<forall>r\<in>{w..uM}. (2 ^ (Suc k + 1) - 1) * dM \<le> dist (f r) (p r)) \<and> L - 4 * delta + 7 * QC (Suc k) \<le> dist (q (Suc k) uM) (q (Suc k) w)"
              proof (rule bexI[of _ w], auto)
                show "w \<le> uM" "yM \<le> w" using \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> by auto
                show "(4 * 2 ^ k - 1) * dM \<le> dist (f x) (p x)" if "x \<le> uM" "w \<le> x" for x
                  using False \<open>dM \<ge> 0\<close> that by force

                have "dist (q k uM) (q (k+1) uM) = 2^k * dM"
                  unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f uM"])
                  using x(3)[of uM] \<open>x \<in> {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
                have "dist (q k w) (q (k+1) w) = 2^k * dM"
                  unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f w"])
                  using x(3)[of w] \<open>w \<in> {x..uM}\<close> \<open>x \<in> {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
                have i: "q k uM \<in> proj_set (q (k+1) uM) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f uM"])
                  using p x(3)[of uM] \<open>x \<in> {yM..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)
                have j: "q k w \<in> proj_set (q (k+1) w) (V k)"
                  unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f w"])
                  using p x(3)[of w] \<open>x \<in> {yM..uM}\<close> \<open>w \<in> {x..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)

                have "5 * delta + 2 * QC k \<le> dist (q k uM) (q k w)" using w(2) by simp
                also have "... \<le> max (5 * deltaG(TYPE('a)) + 2 * QC k)
                                      (dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k)"
                  by (rule proj_along_quasiconvex_contraction[OF \<open>quasiconvex (QC k) (V k)\<close> i j])
                finally have "5 * delta + 2 * QC k \<le> dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG(TYPE('a)) + 4 * QC k"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                then have "0 \<le> dist (q (k + 1) uM) (q (k + 1) w) + 5 * delta + 2 * QC k - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w)"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                also have "... = dist (q (k + 1) uM) (q (k + 1) w) + 5 * delta + 2 * QC k - 2^(k+1) * dM"
                  by (simp only: \<open>dist (q k w) (q (k+1) w) = 2^k * dM\<close> \<open>dist (q k uM) (q (k+1) uM) = 2^k * dM\<close>, auto)
                finally have *: "2^(k+1) * dM - 5 * delta - 2 * QC k \<le> dist (q (k+1) uM) (q (k+1) w)"
                  using \<open>deltaG(TYPE('a)) < delta\<close> by auto
                have "L - 4 * delta + 7 * QC (k+1) \<le> 2 * dM - 5 * delta - 2 * QC k"
                  unfolding QC_def L_def using \<open>delta > 0\<close> Laux I \<open>C \<ge> 0\<close> by auto
                also have "... \<le> 2^(k+1) * dM - 5 * delta - 2 * QC k"
                  using aux by (auto simp add: algebra_simps)
                finally show "L - 4 * delta + 7 * QC (Suc k) \<le> dist (q (Suc k) uM) (q (Suc k) w)"
                  using * by auto
              qed
              then show ?thesis
                by simp
            qed
          qed
        qed
        have "dM > 0" using I \<open>delta > 0\<close> \<open>C \<ge> 0\<close> Laux by auto
        have "\<exists>k. 2^k > dist (f uM) (p uM)/dM + 1"
          by (simp add: real_arch_pow)
        then obtain k where "2^k > dist (f uM) (p uM)/dM + 1"
          by blast
        then have "dist (f uM) (p uM) < (2^k - 1) * dM"
          using \<open>dM > 0\<close> by (auto simp add: divide_simps algebra_simps)
        also have "... \<le> (2^(Suc k) - 1) * dM"
          by (intro mono_intros, auto)
        finally have "\<not>((2 ^ (k + 1) - 1) * dM \<le> dist (f uM) (p uM))"
          by simp
        then show "Gromov_product_at (f z) (f um) (f uM) \<le> lambda\<^sup>2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp (- K * (uM - um)))"
          using Ind_k[of k] by auto
      qed
    qed
  qed
  text \<open>The main induction is over. To conclude, one should apply its result to the original
  geodesic segment joining the points $f(a)$ and $f(b)$.\<close>
  obtain n::nat where "(b - a)/((1/4) * delta / lambda) \<le> n"
    using real_arch_simple by blast
  then have "b - a \<le> n * (1/4) * delta / lambda"
    using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
  have "infdist (f z) G \<le> Gromov_product_at (f z) (f a) (f b) + 2 * deltaG(TYPE('a))"
    apply (intro mono_intros) using assms by auto
  also have "... \<le> (lambda^2 * (D + 3/2 * L + delta + 11/2 * C) - 2 * delta + Kmult * (1 - exp(-K * (b - a)))) + 2 * delta"
    apply (intro mono_intros Main[OF _ _ \<open>b - a \<le> n * (1/4) * delta / lambda\<close>]) using assms by auto
  also have "... = lambda^2 * (D + 3/2 * L + delta + 11/2 * C) + Kmult * (1 - exp(-K * (b - a)))"
    by simp
  also have "... \<le> lambda^2 * (D + 3/2 * L + delta + 11/2 * C) + Kmult * (1 - 0)"
    apply (intro mono_intros) using \<open>Kmult > 0\<close> by auto
  also have "... = lambda^2 * (11/2 * C + (3200*exp(-459/50*ln 2)/ln 2 + 83) * delta)"
    unfolding Kmult_def K_def L_def alpha_def D_def using \<open>delta > 0\<close> \<open>lambda \<ge> 1\<close> by (simp add: algebra_simps divide_simps power2_eq_square mult_exp_exp)
  also have "... \<le> lambda^2 * (11/2 * C + 91 * delta)"
    apply (intro mono_intros, simp add: divide_simps, approximation 14)
    using \<open>delta > 0\<close> by auto
  finally show ?thesis by (simp add: algebra_simps)
qed

text \<open>Still assuming that our quasi-isometry is Lipschitz, we will improve slightly on the previous
result, first going down to the hyperbolicity constant of the space, and also showing that,
conversely, the geodesic is contained in a neighborhood of the quasi-geodesic. The argument for this
last point goes as follows. Consider a point $x$ on the geodesic. Define two sets to
be the $D$-thickenings of $[a,x]$ and $[x,b]$ respectively, where $D$ is such that any point on the
quasi-geodesic is within distance $D$ of the geodesic (as given by the previous theorem). The union
of these two sets covers the quasi-geodesic, and they are both closed and nonempty. By connectedness,
there is a point $z$ in their intersection, $D$-close both to a point $x^-$ before $x$ and to a point
$x^+$ after $x$. Then $x$ belongs to a geodesic between $x^-$ and $x^+$, which is contained in a
$4\delta$-neighborhood of geodesics from $x^+$ to $z$ and from $x^-$ to $z$ by hyperbolicity. It
follows that $x$ is at distance at most $D + 4\delta$ of $z$, concluding the proof.\<close>

lemma (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem_aux2:
  fixes f::"real \<Rightarrow> 'a"
  assumes "continuous_on {a..b} f"
          "lambda C-quasi_isometry_on {a..b} f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`{a..b}) G \<le> lambda^2 * (11/2 * C + 92 * deltaG(TYPE('a)))"
proof (cases "a \<le> b")
  case True
  have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(2)] by auto
  have *: "infdist (f z) G \<le> lambda^2 * (11/2 * C + 91 * delta)" if "z \<in> {a..b}" "delta > deltaG(TYPE('a))" for z delta
    by (rule Morse_Gromov_theorem_aux1[OF assms(1) assms(2) True assms(3) that])
  define D where "D = lambda^2 * (11/2 * C + 91 * deltaG(TYPE('a)))"
  have "D \<ge> 0" unfolding D_def using \<open>C \<ge> 0\<close> by auto
  have I: "infdist (f z) G \<le> D" if "z \<in> {a..b}" for z
  proof -
    have "(infdist (f z) G/ lambda^2 - 11/2 * C)/91 \<le> delta" if "delta > deltaG(TYPE('a))" for delta
      using *[OF \<open>z \<in> {a..b}\<close> that] \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
    then have "(infdist (f z) G/ lambda^2 - 11/2 * C)/91 \<le> deltaG(TYPE('a))"
      using dense_ge by blast
    then show ?thesis unfolding D_def using \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  show ?thesis
  proof (rule hausdorff_distanceI)
    show "0 \<le> lambda\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))" using \<open>C \<ge> 0\<close> by auto
    fix x assume "x \<in> f`{a..b}"
    then obtain z where z: "x = f z" "z \<in> {a..b}" by blast
    show "infdist x G \<le> lambda\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding z(1) by (rule order_trans[OF I[OF \<open>z \<in> {a..b}\<close>]], auto simp add: algebra_simps D_def)
  next
    fix x assume "x \<in> G"
    have "infdist x (f`{a..b}) \<le> D + 1 * deltaG TYPE('a)"
    proof -
      define p where "p = geodesic_segment_param G (f a)"
      then have p: "p 0 = f a" "p (dist (f a) (f b)) = f b"
        unfolding p_def using assms(3) by auto
      obtain t where t: "x = p t" "t \<in> {0..dist (f a) (f b)}"
        unfolding p_def using \<open>x \<in> G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
      define Km where "Km = (\<Union>z \<in> p`{0..t}. cball z D)"
      define KM where "KM = (\<Union>z \<in> p`{t..dist (f a) (f b)}. cball z D)"
      have "f`{a..b} \<subseteq> Km \<union> KM"
      proof
        fix x assume x: "x \<in> f`{a..b}"
        have "\<exists>z \<in> G. infdist x G = dist x z"
          apply (rule infdist_proper_attained)
          using geodesic_segment_topology[OF geodesic_segmentI[OF assms(3)]] by auto
        then obtain z where z: "z \<in> G" "infdist x G = dist x z"
          by auto
        obtain tz where tz: "z = p tz" "tz \<in> {0..dist (f a) (f b)}"
          unfolding p_def using \<open>z \<in> G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
        have "infdist x G \<le> D"
          using I \<open>x \<in> f`{a..b}\<close> by auto
        then have "dist z x \<le> D"
          using z(2) by (simp add: metric_space_class.dist_commute)
        then show "x \<in> Km \<union> KM"
          unfolding Km_def KM_def using tz by force
      qed
      then have *: "f`{a..b} = (Km \<inter> f`{a..b}) \<union> (KM \<inter> f`{a..b})" by auto
      have "(Km \<inter> f`{a..b}) \<inter> (KM \<inter> f`{a..b}) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed (f ` {a..b})"
          apply (intro compact_imp_closed compact_continuous_image) using assms(1) by auto
        have "closed Km"
          unfolding Km_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t \<in> {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (Km \<inter> f`{a..b})"
          by (rule topological_space_class.closed_Int) fact

        have "closed KM"
          unfolding KM_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t \<in> {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (KM \<inter> f`{a..b})"
          by (rule topological_space_class.closed_Int) fact

        show "connected (f`{a..b})"
          apply (rule connected_continuous_image) using assms(1) by auto
        have "f a \<in> Km \<inter> f`{a..b}" using True apply auto
          unfolding Km_def apply auto apply (rule bexI[of _ 0])
          unfolding p using \<open>D \<ge> 0\<close> t(2) by auto
        then show "Km \<inter> f`{a..b} \<noteq> {}" by auto
        have "f b \<in> KM \<inter> f`{a..b}" apply auto
          unfolding KM_def apply auto apply (rule bexI[of _ "dist (f a) (f b)"])
          unfolding p using \<open>D \<ge> 0\<close> t(2) True by auto
        then show "KM \<inter> f`{a..b} \<noteq> {}" by auto
      qed
      then obtain y where y: "y \<in> f`{a..b}" "y \<in> Km" "y \<in> KM" by auto
      obtain tm where tm: "tm \<in> {0..t}" "dist (p tm) y \<le> D"
        using y(2) unfolding Km_def by auto
      obtain tM where tM: "tM \<in> {t..dist (f a) (f b)}" "dist (p tM) y \<le> D"
        using y(3) unfolding KM_def by auto
      define H where "H = p`{tm..tM}"
      have *: "geodesic_segment_between H (p tm) (p tM)"
        unfolding H_def p_def apply (rule geodesic_segmentI2)
        using assms(3) \<open>tm \<in> {0..t}\<close> \<open>tM \<in> {t..dist (f a) (f b)}\<close> isometry_on_subset
        using assms(3) geodesic_segment_param(4) by (auto) fastforce
      have "x \<in> H"
        unfolding t(1) H_def using \<open>tm \<in> {0..t}\<close> \<open>tM \<in> {t..dist (f a) (f b)}\<close> by auto
      have "infdist x (f ` {a..b}) \<le> dist x y"
        by (rule infdist_le[OF y(1)])
      also have "... \<le> max (dist (p tm) y) (dist (p tM) y) + deltaG(TYPE('a))"
        by (rule dist_le_max_dist_triangle[OF * \<open>x \<in> H\<close>])
      finally show ?thesis
        using tm(2) tM(2) by auto
    qed
    also have "... \<le> D + lambda^2 * deltaG TYPE('a)"
      apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> by auto
    finally show "infdist x (f ` {a..b}) \<le> lambda\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding D_def by (simp add: algebra_simps)
  qed
next
  case False
  then have "f`{a..b} = {}"
    by auto
  then have "hausdorff_distance (f ` {a..b}) G = 0"
    unfolding hausdorff_distance_def by auto
  then show ?thesis
    using quasi_isometry_onD(4)[OF assms(2)] by auto
qed

text \<open>The full statement of the Morse-Gromov Theorem, asserting that a quasi-geodesic is
within controlled distance of a geodesic with the same endpoints. It is given in the formulation
of Shchur~\cite{shchur}, with optimal control in terms of the parameters of the quasi-isometry.
This statement follows readily from the previous one and from the fact that quasi-geodesics can be
approximated by Lipschitz ones.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem:
  fixes f::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {a..b} f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`{a..b}) G \<le> 92 * lambda^2 * (C + deltaG(TYPE('a)))"
proof -
  have C: "C \<ge> 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms(1)] by auto
  consider "dist (f a) (f b) \<ge> 2 * C \<and> a \<le> b" | "dist (f a) (f b) \<le> 2 * C \<and> a \<le> b" | "b < a"
    by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "\<exists>d. continuous_on {a..b} d \<and> d a = f a \<and> d b = f b
                \<and> (\<forall>x\<in>{a..b}. dist (f x) (d x) \<le> 4 * C)
                \<and> lambda (4 * C)-quasi_isometry_on {a..b} d
                \<and> (2 * lambda)-lipschitz_on {a..b} d
                \<and> hausdorff_distance (f`{a..b}) (d`{a..b}) \<le> 2 * C"
      apply (rule quasi_geodesic_made_lipschitz[OF assms(1)]) using 1 by auto
    then obtain d where d: "d a = f a" "d b = f b"
                        "\<And>x. x \<in> {a..b} \<Longrightarrow> dist (f x) (d x) \<le> 4 * C"
                        "lambda (4 * C)-quasi_isometry_on {a..b} d"
                        "(2 * lambda)-lipschitz_on {a..b} d"
                        "hausdorff_distance (f`{a..b}) (d`{a..b}) \<le> 2 * C"
      by auto
    have a: "hausdorff_distance (d`{a..b}) G \<le> lambda^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a)))"
      apply (rule Morse_Gromov_theorem_aux2) using d assms lipschitz_on_continuous_on by auto

    have "hausdorff_distance (f`{a..b}) G \<le>
          hausdorff_distance (f`{a..b}) (d`{a..b}) + hausdorff_distance (d`{a..b}) G"
      apply (rule hausdorff_distance_triangle)
      using 1 apply simp
      by (rule quasi_isometry_on_bounded[OF d(4)], auto)
    also have "... \<le> lambda^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a))) + 1 * 2 * C"
      using a d by auto
    also have "... \<le> lambda^2 * ((11/2) * (4 * C) + 92 * deltaG(TYPE('a))) + lambda^2 * 2 * C"
      apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
    also have "... = lambda^2 * (24 * C + 92 * deltaG(TYPE('a)))"
      by (simp add: algebra_simps divide_simps)
    also have "... \<le> lambda^2 * (92 * C + 92 * deltaG(TYPE('a)))"
      apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
    finally show ?thesis by (auto simp add: algebra_simps)
  next
    case 2
    have "(1/lambda) * dist a b - C \<le> dist (f a) (f b)"
      apply (rule quasi_isometry_onD[OF assms(1)]) using 2 by auto
    also have "... \<le> 2 * C" using 2 by auto
    finally have "dist a b \<le> 3 * lambda * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "b - a \<le> 3 * lambda * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 92 * lambda\<^sup>2 * (C + deltaG TYPE('a))" using C by auto
      fix x assume "x \<in> f`{a..b}"
      then obtain t where t: "x = f t" "t \<in> {a..b}" by auto
      have "dist x (f a) \<le> lambda * dist t a + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms(1) t(2)] 2 by auto
      also have "... \<le> lambda * (b - a) + 1 * 1 * C + 0 * 0 * deltaG(TYPE('a))" using t(2) 2 C unfolding dist_real_def by auto
      also have "... \<le> lambda * (3 * lambda * C) + lambda^2 * (92-3) * C + lambda^2 * 92 * deltaG(TYPE('a))"
        apply (intro mono_intros *) using C by auto
      finally have *: "dist x (f a) \<le> 92 * lambda\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps power2_eq_square)
      show "\<exists>y\<in>G. dist x y \<le> 92 * lambda\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 assms(2) by auto
    next
      fix x assume "x \<in> G"
      then have "dist x (f a) \<le> dist (f a) (f b)"
        by (meson assms geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      also have "... \<le> 1 * 2 * C + lambda^2 * 0 * deltaG(TYPE('a))"
        using 2 by auto
      also have "... \<le> lambda^2 * 92 * C + lambda^2 * 92 * deltaG(TYPE('a))"
        apply (intro mono_intros) using C by auto
      finally have *: "dist x (f a) \<le> 92 * lambda\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps)
      show "\<exists>y\<in>f`{a..b}. dist x y \<le> 92 * lambda\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 by auto
    qed
  next
    case 3
    then have "hausdorff_distance (f ` {a..b}) G = 0"
      unfolding hausdorff_distance_def by auto
    then show ?thesis
      using C by auto
  qed
qed

text \<open>This theorem implies the same statement for two quasi-geodesics sharing their endpoints.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem2:
  fixes c d::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
          "lambda C-quasi_isometry_on {A..B} d"
          "c A = d A" "c B = d B"
  shows "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 184 * lambda^2 * (C + deltaG(TYPE('a)))"
proof (cases "A \<le> B")
  case False
  then have "hausdorff_distance (c`{A..B}) (d`{A..B}) = 0" by auto
  then show ?thesis using quasi_isometry_onD[OF assms(1)] delta_nonneg by auto
next
  case True
  have "hausdorff_distance (c`{A..B}) {c A--c B} \<le> 92 * lambda^2 * (C + deltaG(TYPE('a)))"
    by (rule Morse_Gromov_theorem[OF assms(1)], auto)
  moreover have "hausdorff_distance {c A--c B} (d`{A..B}) \<le> 92 * lambda^2 * (C + deltaG(TYPE('a)))"
    unfolding \<open>c A = d A\<close> \<open>c B = d B\<close> apply (subst hausdorff_distance_sym)
    by (rule Morse_Gromov_theorem[OF assms(2)], auto)
  moreover have "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> hausdorff_distance (c`{A..B}) {c A--c B} + hausdorff_distance {c A--c B} (d`{A..B})"
    apply (rule hausdorff_distance_triangle)
    using True compact_imp_bounded[OF some_geodesic_compact] by auto
  ultimately show ?thesis by auto
qed

text \<open>We deduce from the Morse lemma that hyperbolicity is invariant under quasi-isometry.\<close>

text \<open>First, we note that the image of a geodesic segment under a quasi-isometry is close to
a geodesic segment in Hausdorff distance, as it is a quasi-geodesic.\<close>

lemma geodesic_quasi_isometric_image:
  fixes f::"'a::metric_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_on UNIV f"
          "geodesic_segment_between G x y"
  shows "hausdorff_distance (f`G) {f x--f y} \<le> 92 * lambda^2 * (C + deltaG(TYPE('b)))"
proof -
  define c where "c = f o (geodesic_segment_param G x)"
  have *: "(1 * lambda) (0 * lambda + C)-quasi_isometry_on {0..dist x y} c"
    unfolding c_def by (rule quasi_isometry_on_compose[where Y = UNIV], auto intro!: isometry_quasi_isometry_on simp add: assms)
  have "hausdorff_distance (c`{0..dist x y}) {c 0--c (dist x y)} \<le> 92 * lambda^2 * (C + deltaG(TYPE('b)))"
    apply (rule Morse_Gromov_theorem) using * by auto
  moreover have "c`{0..dist x y} = f`G"
    unfolding c_def image_comp[symmetric] using assms(2) by auto
  moreover have "c 0 = f x" "c (dist x y) = f y"
    unfolding c_def using assms(2) by auto
  ultimately show ?thesis by auto
qed

text \<open>We deduce that hyperbolicity is invariant under quasi-isometry. The proof goes as follows:
we want to see that a geodesic triangle is delta-thin, i.e., a point on a side $Gxy$ is close to the
union of the two other sides $Gxz$ and $Gyz$. Pull everything back by the quasi-isometry: we obtain
three quasi-geodesic, each of which is close to the corresponding geodesic segment by the Morse lemma.
As the geodesic triangle is thin, it follows that the quasi-geodesic triangle is also thin, i.e.,
a point on $f^{-1}Gxy$ is close to $f^{-1}Gxz \cup f^{-1}Gyz$ (for some explicit, albeit large,
constant). Then push everything forward by $f$: as it is a quasi-isometry, it will again distort
distances by a bounded amount.\<close>

lemma Gromov_hyperbolic_invariant_under_quasi_isometry_explicit:
  fixes f::"'a::geodesic_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_hyperbolic_subset (752 * lambda^3 * (C + deltaG(TYPE('b)))) (UNIV::('a set))"
proof -
  have C: "lambda \<ge> 1" "C \<ge> 0"
    using quasi_isometry_onD[OF assms] by auto

  text \<open>The Morse lemma gives a control bounded by $K$ below. Following the proof, we deduce
  a bound on the thinness of triangles by an ugly constant $L$. We bound it by a more tractable
  (albeit still ugly) constant $M$.\<close>
  define K where "K = 92 * lambda^2 * (C + deltaG(TYPE('b)))"
  have HD: "hausdorff_distance (f`G) {f a--f b} \<le> K" if "geodesic_segment_between G a b" for G a b
    unfolding K_def by (rule geodesic_quasi_isometric_image[OF assms that])
  define L where "L = lambda * (4 * 1 * deltaG(TYPE('b)) + 1 * 1 * C + 2 * K)"
  define M where "M = 188 * lambda^3 * (C + deltaG(TYPE('b)))"

  have "L \<le> lambda * (4 * lambda^2 * deltaG(TYPE('b)) + 4 * lambda^2 * C + 2 * K)"
    unfolding L_def apply (intro mono_intros) using C by auto
  also have "... = M"
    unfolding M_def K_def by (auto simp add: algebra_simps power2_eq_square power3_eq_cube)
  finally have "L \<le> M" by simp

  text \<open>After these preliminaries, we start the real argument per se, showing that triangles
  are thin in the type b.\<close>
  have Thin: "infdist w (Gxz \<union> Gyz) \<le> M" if
    H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z" "w \<in> Gxy"
    for w x y z::'a and Gxy Gyz Gxz
  proof -
    obtain w2 where w2: "w2 \<in> {f x--f y}" "infdist (f w) {f x--f y} = dist (f w) w2"
      using infdist_proper_attained[OF proper_of_compact, of "{f x--f y}" "f w"] by auto
    have "dist (f w) w2 = infdist (f w) {f x-- f y}"
      using w2 by simp
    also have "... \<le> hausdorff_distance (f`Gxy) {f x-- f y}"
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]] infdist_le_hausdorff_distance)
    also have "... \<le> K" using HD[OF H(1)] by simp
    finally have *: "dist (f w) w2 \<le> K" by simp

    have "infdist w2 (f`Gxz \<union> f`Gyz) \<le> infdist w2 ({f x--f z} \<union> {f y--f z})
                + hausdorff_distance ({f x--f z} \<union> {f y--f z}) (f`Gxz \<union> f`Gyz)"
      apply (rule hausdorff_distance_infdist_triangle)
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]])
    also have "... \<le> 4 * deltaG(TYPE('b)) + hausdorff_distance ({f x--f z} \<union> {f y--f z}) (f`Gxz \<union> f`Gyz)"
      apply (simp, rule thin_triangles[of "{f x--f z}" "f z" "f x" "{f y--f z}" "f y" "{f x--f y}" w2])
      using w2 apply auto
      using geodesic_segment_commute some_geodesic_is_geodesic_segment(1) by blast+
    also have "... \<le> 4 * deltaG(TYPE('b)) + max (hausdorff_distance {f x--f z} (f`Gxz)) (hausdorff_distance {f y--f z} (f`Gyz))"
      apply (intro mono_intros) using H by auto
    also have "... \<le> 4 * deltaG(TYPE('b)) + K"
      using HD[OF H(2)] HD[OF H(3)] by (auto simp add: hausdorff_distance_sym)
    finally have **: "infdist w2 (f`Gxz \<union> f`Gyz) \<le> 4 * deltaG(TYPE('b)) + K" by simp

    have "infdist (f w) (f`Gxz \<union> f`Gyz) \<le> infdist w2 (f`Gxz \<union> f`Gyz) + dist (f w) w2"
      by (rule infdist_triangle)
    then have A: "infdist (f w) (f`(Gxz \<union> Gyz)) \<le> 4 * deltaG(TYPE('b)) + 2 * K"
      using * ** by (auto simp add: image_Un)

    have "infdist w (Gxz \<union> Gyz) \<le> L + epsilon" if "epsilon > 0" for epsilon
    proof -
      have *: "epsilon/lambda > 0" using that C by auto
      have "\<exists>z \<in> f`(Gxz \<union> Gyz). dist (f w) z < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        apply (rule infdist_almost_attained)
        using A * H(2) by auto
      then obtain z where z: "z \<in> Gxz \<union> Gyz" "dist (f w) (f z) < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        by auto

      have "infdist w (Gxz \<union> Gyz) \<le> dist w z"
        by (auto intro!: infdist_le z(1))
      also have "... \<le> lambda * dist (f w) (f z) + C * lambda"
        using quasi_isometry_onD[OF assms] by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> lambda * (4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda) + C * lambda"
        apply (intro mono_intros) using z(2) C by auto
      also have "... = L + epsilon"
        unfolding K_def L_def using C by (auto simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    then have "infdist w (Gxz \<union> Gyz) \<le> L"
      using field_le_epsilon by blast
    then show ?thesis
      using \<open>L \<le> M\<close> by auto
  qed
  then have "Gromov_hyperbolic_subset (4 * M) (UNIV::'a set)"
    using thin_triangles_implies_hyperbolic[OF Thin] by auto
  then show ?thesis unfolding M_def by (auto simp add: algebra_simps)
qed

text \<open>Most often, the precise value of the constant in the previous theorem is irrelevant,
it is used in the following form.\<close>

theorem Gromov_hyperbolic_invariant_under_quasi_isometry:
  assumes "quasi_isometric (UNIV::('a::geodesic_space) set) (UNIV::('b::Gromov_hyperbolic_space_geodesic) set)"
  shows "\<exists>delta. Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof -
  obtain C lambda f where f: "lambda C-quasi_isometry_between (UNIV::'a set) (UNIV::'b set) f"
    using assms unfolding quasi_isometric_def by auto
  show ?thesis
    using Gromov_hyperbolic_invariant_under_quasi_isometry_explicit[OF quasi_isometry_betweenD(1)[OF f]] by blast
qed


text \<open>A central feature of hyperbolic spaces is that a path from $x$ to $y$ can not deviate
too much from a geodesic from $x$ to $y$ unless it is extremely long (exponentially long in
terms of the distance from $x$ to $y$). This is useful both to ensure that short paths (for instance
quasi-geodesics) stay close to geodesics, see the Morse lemme below, and to ensure that paths
that avoid a given large ball of radius $R$ have to be exponentially long in terms of $R$ (this
is extremely useful for random walks). This proposition is the first non-trivial result
on hyperbolic spaces in~\cite{bridson_haefliger} (Proposition III.H.1.6). We follow their proof.

The proof is geometric, and uses the existence of geodesics and the fact that geodesic
triangles are thin. In fact, the result still holds if the space is not geodesic, as
it can be deduced by embedding the hyperbolic space in a geodesic hyperbolic space and using
the result there.\<close>

proposition (in Gromov_hyperbolic_space_geodesic) lipschitz_path_close_to_geodesic:
  fixes c::"real \<Rightarrow> 'a"
  assumes "M-lipschitz_on {A..B} c"
          "geodesic_segment_between G (c A) (c B)"
          "x \<in> G"
  shows "infdist x (c`{A..B}) \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (B-A)) + M"
proof -
  have "M \<ge> 0" by (rule lipschitz_on_nonneg[OF assms(1)])
  have Main: "a \<in> {A..B} \<Longrightarrow> b \<in> {A..B} \<Longrightarrow> a \<le> b \<Longrightarrow> b-a \<le> 2^(n+1) \<Longrightarrow> geodesic_segment_between H (c a) (c b)
        \<Longrightarrow> y \<in> H \<Longrightarrow> infdist y (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M" for a b H y n
  proof (induction n arbitrary: a b H y)
    case 0
    have "infdist y (c ` {A..B}) \<le> dist y (c b)"
      apply (rule infdist_le) using \<open>b \<in> {A..B}\<close> by auto
    moreover have "infdist y (c ` {A..B}) \<le> dist y (c a)"
      apply (rule infdist_le) using \<open>a \<in> {A..B}\<close> by auto
    ultimately have "2 * infdist y (c ` {A..B}) \<le> dist (c a) y + dist y (c b)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist (c a) (c b)"
      by (rule geodesic_segment_dist[OF \<open>geodesic_segment_between H (c a) (c b)\<close> \<open>y \<in> H\<close>])
    also have "... \<le> M * abs(b - a)"
      using lipschitz_onD(1)[OF assms(1) \<open>a \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close>] unfolding dist_real_def
      by (simp add: abs_minus_commute)
    also have "... \<le> M * 2"
      using \<open>a \<le> b\<close> \<open>b - a \<le> 2^(0 + 1)\<close> \<open>M \<ge> 0\<close> mult_left_mono by auto
    finally show ?case by simp
  next
    case (Suc n)
    define m where "m = (a + b)/2"
    have "m \<in> {A..B}" using \<open>a \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close> unfolding m_def by auto
    define Ha where "Ha = {c m--c a}"
    define Hb where "Hb = {c m--c b}"
    have I: "geodesic_segment_between Ha (c m) (c a)" "geodesic_segment_between Hb (c m) (c b)"
      unfolding Ha_def Hb_def by auto
    then have "Ha \<noteq> {}" "Hb \<noteq> {}" "compact Ha" "compact Hb"
      by (auto intro: geodesic_segment_topology)

    have *: "infdist y (Ha \<union> Hb) \<le> 4 * deltaG(TYPE('a))"
      by (rule thin_triangles[OF I \<open>geodesic_segment_between H (c a) (c b)\<close> \<open>y \<in> H\<close>])
    then have "infdist y Ha \<le> 4 * deltaG(TYPE('a)) \<or> infdist y Hb \<le> 4 * deltaG(TYPE('a))"
      unfolding infdist_union_min[OF \<open>Ha \<noteq> {}\<close> \<open>Hb \<noteq> {}\<close>] by auto
    then show ?case
    proof
      assume H: "infdist y Ha \<le> 4 * deltaG TYPE('a)"
      obtain z where z: "z \<in> Ha" "infdist y Ha = dist y z"
        using infdist_proper_attained[OF proper_of_compact[OF \<open>compact Ha\<close>] \<open>Ha \<noteq> {}\<close>] by auto
      have Iz: "infdist z (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      proof (rule Suc.IH[OF \<open>a \<in> {A..B}\<close> \<open>m \<in> {A..B}\<close>, of Ha])
        show "a \<le> m" unfolding m_def using \<open>a \<le> b\<close> by auto
        show "m - a \<le> 2^(n+1)" using \<open>b - a \<le> 2^(Suc n + 1)\<close> \<open>a \<le> b\<close> unfolding m_def by auto
        show "geodesic_segment_between Ha (c a) (c m)" by (simp add: I(1) geodesic_segment_commute)
        show "z \<in> Ha" using z by auto
      qed
      have "infdist y (c`{A..B}) \<le> dist y z + infdist z (c`{A..B})"
        by (metis add.commute infdist_triangle)
      also have "... \<le> 4 * deltaG TYPE('a) + (4 * deltaG(TYPE('a)) * n + M)"
        using H z Iz by (auto intro: add_mono)
      finally show "infdist y (c ` {A..B}) \<le> 4 * deltaG TYPE('a) * real (Suc n) + M"
        by (auto simp add: algebra_simps)
    next
      assume H: "infdist y Hb \<le> 4 * deltaG TYPE('a)"
      obtain z where z: "z \<in> Hb" "infdist y Hb = dist y z"
        using infdist_proper_attained[OF proper_of_compact[OF \<open>compact Hb\<close>] \<open>Hb \<noteq> {}\<close>] by auto
      have Iz: "infdist z (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      proof (rule Suc.IH[OF \<open>m \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close>, of Hb])
        show "m \<le> b" unfolding m_def using \<open>a \<le> b\<close> by auto
        show "b - m \<le> 2^(n+1)" using \<open>b - a \<le> 2^(Suc n + 1)\<close> \<open>a \<le> b\<close>
          unfolding m_def by (auto simp add: divide_simps)
        show "geodesic_segment_between Hb (c m) (c b)" by (simp add: I(2))
        show "z \<in> Hb" using z by auto
      qed
      have "infdist y (c`{A..B}) \<le> dist y z + infdist z (c`{A..B})"
        by (metis add.commute infdist_triangle)
      also have "... \<le> 4 * deltaG TYPE('a) + (4 * deltaG(TYPE('a)) * n + M)"
        using H z Iz by (auto intro: add_mono)
      finally show "infdist y (c ` {A..B}) \<le> 4 * deltaG TYPE('a) * real (Suc n) + M"
        by (auto simp add: algebra_simps)
    qed
  qed
  consider "B-A <0" | "B-A \<ge> 0 \<and> B-A \<le> 2" | "B-A > 2" by linarith
  then show ?thesis
  proof (cases)
    case 1
    then have "c`{A..B} = {}" by auto
    then show ?thesis unfolding infdist_def using \<open>M \<ge> 0\<close> by auto
  next
    case 2
    have "infdist x (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * real 0 + M"
      apply (rule Main[OF _ _ _ _ \<open>geodesic_segment_between G (c A) (c B)\<close> \<open>x \<in> G\<close>])
      using 2 by auto
    also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (B-A)) + M"
      using delta_nonneg by auto
    finally show ?thesis by auto
  next
    case 3
    define n::nat where "n = nat(floor (log 2 (B-A)))"
    have "log 2 (B-A) > 0" using 3 by auto
    then have n: "n \<le> log 2 (B-A)" "log 2 (B-A) < n+1"
      unfolding n_def by (auto simp add: floor_less_cancel)
    then have *: "B-A \<le> 2^(n+1)"
      by (meson le_log_of_power linear not_less one_less_numeral_iff semiring_norm(76))
    have "n \<le> ln (B-A) * (1/ln 2)" using n unfolding log_def by auto
    then have "n \<le> (1/ln 2) * max 0 (ln (B-A))"
      using 3 by (auto simp add: algebra_simps divide_simps)
    have "infdist x (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      apply (rule Main[OF _ _ _ _ \<open>geodesic_segment_between G (c A) (c B)\<close> \<open>x \<in> G\<close>])
      using * 3 by auto
    also have "... \<le> 4 * deltaG(TYPE('a)) * ((1/ln 2) * max 0 (ln (B-A))) + M"
      apply (intro mono_intros) using \<open>n \<le> (1/ln 2) * max 0 (ln (B-A))\<close> delta_nonneg by auto
    finally show ?thesis by auto
  qed
qed

text \<open>By rescaling coordinates at the origin, one obtains a variation around the previous
statement.\<close>

proposition (in Gromov_hyperbolic_space_geodesic) lipschitz_path_close_to_geodesic':
  fixes c::"real \<Rightarrow> 'a"
  assumes "M-lipschitz_on {A..B} c"
          "geodesic_segment_between G (c A) (c B)"
          "x \<in> G"
          "a > 0"
  shows "infdist x (c`{A..B}) \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a * (B-A))) + M/a"
proof -
  define d where "d = c o (\<lambda>t. (1/a) * t)"
  have *: "(M * ((1/a)* 1))-lipschitz_on {a * A..a * B} d"
    unfolding d_def apply (rule lipschitz_on_compose, intro lipschitz_intros) using assms by auto
  have "d`{a * A..a * B} = c`{A..B}"
    unfolding d_def image_comp[symmetric]
    apply (rule arg_cong[where ?f = "image c"]) using \<open>a > 0\<close> by auto
  then have "infdist x (c`{A..B}) = infdist x (d`{a * A..a * B})" by auto
  also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln ((a * B)- (a * A))) + M/a"
    apply (rule lipschitz_path_close_to_geodesic[OF _ _ \<open>x \<in> G\<close>])
    using * assms unfolding d_def by auto
  finally show ?thesis by (auto simp add: algebra_simps)
qed

text \<open>We can now give another proof of the Morse-Gromov Theorem, as described
in~\cite{bridson_haefliger}. It is more direct than the one we have given above, but it gives
a worse dependence in terms of the quasi-isometry constants. In particular, when $C = \delta = 0$,
it does not recover the fact that a quasi-geodesic has to coincide with a geodesic.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem_BH_proof:
  fixes c::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
  shows "hausdorff_distance (c`{A..B}) {c A--c B} \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
proof -
  have C: "C \<ge> 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms] by auto
  consider "B-A < 0" | "B-A \<ge> 0 \<and> dist (c A) (c B) \<le> 2 * C" | "B-A \<ge> 0 \<and> dist (c A) (c B) > 2 * C" by linarith
  then show ?thesis
  proof (cases)
    case 1
    then have "c`{A..B} = {}" by auto
    then show ?thesis unfolding hausdorff_distance_def using delta_nonneg C by auto
  next
    case 2
    have "(1/lambda) * dist A B - C \<le> dist (c A) (c B)"
      apply (rule quasi_isometry_onD[OF assms]) using 2 by auto
    also have "... \<le> 2 * C" using 2 by auto
    finally have "dist A B \<le> 3 * lambda * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "B - A \<le> 3 * lambda * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)" using C by auto
      fix x assume "x \<in> c`{A..B}"
      then obtain t where t: "x = c t" "t \<in> {A..B}" by auto
      have "dist x (c A) \<le> lambda * dist t A + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms t(2), of A] 2 by auto
      also have "... \<le> lambda * (B-A) + C" using t(2) 2 C unfolding dist_real_def by auto
      also have "... \<le> 3 * lambda * lambda * C + 1 * 1 * C" using * C by auto
      also have "... \<le> 3 * lambda * lambda * C + lambda * lambda * C"
        apply (intro mono_intros) using C by auto
      also have "... = 4 * lambda * lambda * (C + 0 + 0^2)"
        by auto
      also have "... \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a))^2)"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        unfolding power2_eq_square by simp
      show "\<exists>y\<in>{c A--c B}. dist x y \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) using * by auto
    next
      fix x assume "x \<in> {c A-- c B}"
      then have "dist x (c A) \<le> dist (c A) (c B)"
        by (meson geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      also have "... \<le> 2 * C"
        using 2 by auto
      also have "... \<le> 2 * 1 * 1 * (C + lambda + 0)" using 2 C unfolding dist_real_def by auto
      also have "... \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 72 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        by simp
      show "\<exists>y\<in>c`{A..B}. dist x y \<le> 72 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) unfolding power2_eq_square using * 2 by auto
    qed
  next
    case 3
    then obtain d where d: "continuous_on {A..B} d" "d A = c A" "d B = c B"
              "\<And>x. x \<in> {A..B} \<Longrightarrow> dist (c x) (d x) \<le> 4 *C"
              "lambda (4 * C)-quasi_isometry_on {A..B} d"
              "(2 * lambda)-lipschitz_on {A..B} d"
              "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 2 * C"
      using quasi_geodesic_made_lipschitz[OF assms] C(1) by fastforce

    have "A \<in> {A..B}" "B \<in> {A..B}" using 3 by auto

    text \<open>We show that the distance of any point in the geodesic from $c(A)$ to $c(B)$ is a bounded
    distance away from the quasi-geodesic $d$, by considering a point $x$ where the distance $D$ is
    maximal and arguing around this point.

    Consider the point $x_m$ on the geodesic $[c(A), c(B)]$ at distance $2D$ from $x$, and the closest
    point $y_m$ on the image of $d$. Then the distance between $x_m$ and $y_m$ is at most $D$. Hence
    a point on $[x_m,y_m]$ is at distance at least $2D - D = D$ of $x$. In the same way, define $x_M$
    and $y_M$ on the other side of $x$. Then the excursion from $x_m$ to $y_m$, then to $y_M$ along
    $d$, then to $x_M$, has length at most $D + (\lambda \cdot 6D + C) + D$ and is always at distance
    at least $D$ from $x$. It follows from the previous lemma that $D \leq \log(length)$, which
    implies a bound on $D$.

    This argument has to be amended if $x$ is at distance $ < 2D$ from $c(A)$ or $c(B)$. In this case,
    simply use $x_m = y_m = c(A)$ or $x_M = y_M = c(B)$, then everything goes through.\<close>

    have "\<exists>x \<in> {c A--c B}. \<forall>y \<in> {c A--c B}. infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by (rule continuous_attains_sup, auto intro: continuous_intros)
    then obtain x where x: "x \<in> {c A--c B}" "\<And>y. y \<in> {c A--c B} \<Longrightarrow> infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by auto
    define D where "D = infdist x (d`{A..B})"
    have "D \<ge> 0" unfolding D_def by (rule infdist_nonneg)
    have D_bound: "D \<le> 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
    proof (cases "D \<le> 1")
      case True
      have "1 * 1 + 1 * 0 + 0 * 0 \<le> 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
        apply (intro mono_intros) using C delta_nonneg by auto
      then show ?thesis using True by auto
    next
      case False
      then have "D \<ge> 1" by auto
      have ln2mult: "2 * ln t = ln (t * t)" if "t > 0" for t::real by (simp add: that ln_mult)
      have "infdist (c A) (d`{A..B}) = 0" using \<open>d A = c A\<close> by (metis \<open>A \<in> {A..B}\<close> image_eqI infdist_zero)
      then have "x \<noteq> c A" using \<open>D \<ge> 1\<close> D_def by auto

      define tx where "tx = dist (c A) x"
      then have "tx \<in> {0..dist (c A) (c B)}"
        using \<open>x \<in> {c A--c B}\<close>
        by (meson atLeastAtMost_iff geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) metric_space_class.zero_le_dist some_geodesic_endpoints(1))
      have "tx > 0" using \<open>x \<noteq> c A\<close> tx_def by auto
      have x_param: "x = geodesic_segment_param {c A--c B} (c A) tx"
        using \<open>x \<in> {c A--c B}\<close> geodesic_segment_param[OF some_geodesic_is_geodesic_segment(1)] tx_def by auto

      define tm where "tm = max (tx - 2 * D) 0"
      have "tm \<in> {0..dist (c A) (c B)}" unfolding tm_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      define xm where "xm = geodesic_segment_param {c A--c B} (c A) tm"
      have "xm \<in> {c A--c B}" using \<open>tm \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xm_def)
      have "dist xm x = abs((max (tx - 2 * D) 0) - tx)"
        unfolding xm_def tm_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" by (simp add: \<open>0 \<le> D\<close> tx_def)
      finally have "dist xm x \<le> 2 * D" by auto
      have "\<exists>ym\<in>d`{A..B}. infdist xm (d`{A..B}) = dist xm ym"
        apply (rule infdist_proper_attained) using 3 d(1) proper_of_compact compact_continuous_image by auto
      then obtain ym where ym: "ym \<in> d`{A..B}" "dist xm ym = infdist xm (d`{A..B})"
        by metis
      then obtain um where um: "um \<in> {A..B}" "ym = d um" by auto
      have "dist xm ym \<le> D"
        unfolding D_def using x ym by (simp add: \<open>xm \<in> {c A--c B}\<close>)
      have D1: "dist x z \<ge> D" if "z \<in> {xm--ym}" for z
      proof (cases "tx - 2 * D < 0")
        case True
        then have "tm = 0" unfolding tm_def by auto
        then have "xm = c A" unfolding xm_def
          by (meson geodesic_segment_param(1) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xm (d`{A..B}) = 0"
          using \<open>d A = c A\<close> \<open>A \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "ym = xm" using ym(2) by auto
        then have "z = xm" using \<open>z \<in> {xm--ym}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>ym = xm\<close> ym(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tm = tx - 2 * D" unfolding tm_def by auto
        have "dist xm x = abs((tx - 2 * D) - tx)"
          unfolding xm_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xm x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xm z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xm ym + dist x z"
          using \<open>z \<in> {xm--ym}\<close> by (auto, meson geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xm ym \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define tM where "tM = min (tx + 2 * D) (dist (c A) (c B))"
      have "tM \<in> {0..dist (c A) (c B)}" unfolding tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      have "tm \<le> tM"
        unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tx \<equiv> dist (c A) x\<close> tm_def by auto
      define xM where "xM = geodesic_segment_param {c A--c B} (c A) tM"
      have "xM \<in> {c A--c B}" using \<open>tM \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xM_def)
      have "dist xM x = abs((min (tx + 2 * D) (dist (c A) (c B))) - tx)"
        unfolding xM_def tM_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" using \<open>0 \<le> D\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
      finally have "dist xM x \<le> 2 * D" by auto
      have "\<exists>yM\<in>d`{A..B}. infdist xM (d`{A..B}) = dist xM yM"
        apply (rule infdist_proper_attained) using 3 d(1) proper_of_compact compact_continuous_image by auto
      then obtain yM where yM: "yM \<in> d`{A..B}" "dist xM yM = infdist xM (d`{A..B})"
        by metis
      then obtain uM where uM: "uM \<in> {A..B}" "yM = d uM" by auto
      have "dist xM yM \<le> D"
        unfolding D_def using x yM by (simp add: \<open>xM \<in> {c A--c B}\<close>)
      have D3: "dist x z \<ge> D" if "z \<in> {xM--yM}" for z
      proof (cases "tx + 2 * D > dist (c A) (c B)")
        case True
        then have "tM = dist (c A) (c B)" unfolding tM_def by auto
        then have "xM = c B" unfolding xM_def
          by (meson geodesic_segment_param(2) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xM (d`{A..B}) = 0"
          using \<open>d B = c B\<close> \<open>B \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "yM = xM" using yM(2) by auto
        then have "z = xM" using \<open>z \<in> {xM--yM}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>yM = xM\<close> yM(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tM = tx + 2 * D" unfolding tM_def by auto
        have "dist xM x = abs((tx + 2 * D) - tx)"
          unfolding xM_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xM x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xM z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xM yM + dist x z"
          using \<open>z \<in> {xM--yM}\<close> by (auto, meson geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xM yM \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define excursion:: "real\<Rightarrow>'a" where "excursion = (\<lambda>t.
        if t \<in> {0..dist xm ym} then (geodesic_segment_param {xm--ym} xm t)
        else if t \<in> {dist xm ym..dist xm ym + abs(uM - um)} then d (um + sgn(uM-um) * (t - dist xm ym))
        else geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um)))"
      define L where "L = dist xm ym + abs(uM - um) + dist yM xM"
      have E1: "excursion t = geodesic_segment_param {xm--ym} xm t" if "t \<in> {0..dist xm ym}" for t
        unfolding excursion_def using that by auto
      have E2: "excursion t = d (um + sgn(uM-um) * (t - dist xm ym))" if "t \<in> {dist xm ym..dist xm ym + abs(uM - um)}" for t
        unfolding excursion_def using that by (auto simp add: \<open>ym = d um\<close>)
      have E3: "excursion t = geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um))"
        if "t \<in> {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}" for t
        unfolding excursion_def using that \<open>yM = d uM\<close> \<open>ym = d um\<close> by (auto simp add: sgn_mult_abs)
      have E0: "excursion 0 = xm"
        unfolding excursion_def by auto
      have EL: "excursion L = xM"
        unfolding excursion_def L_def apply (auto simp add: uM(2) um(2) sgn_mult_abs)
        by (metis (mono_tags, hide_lams) add.left_neutral add_increasing2 add_le_same_cancel1 dist_real_def
              Gromov_product_e_x_x Gromov_product_nonneg metric_space_class.dist_le_zero_iff)
      have [simp]: "L \<ge> 0" unfolding L_def by auto
      have "L > 0"
      proof (rule ccontr)
        assume "\<not>(L > 0)"
        then have "L = 0" using \<open>L \<ge> 0\<close> by simp
        then have "xm = xM" using E0 EL by auto
        then have "tM = tm" unfolding xm_def xM_def
          using \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> local.geodesic_segment_param_in_geodesic_spaces(6) by fastforce
        also have "... < tx" unfolding tm_def using \<open>tx > 0\<close> \<open>D \<ge> 1\<close> by auto
        also have "... \<le> tM" unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
        finally show False by simp
      qed

      have "(1/lambda) * dist um uM - (4 * C) \<le> dist (d um) (d uM)"
        by (rule quasi_isometry_onD(2)[OF \<open>lambda (4 * C)-quasi_isometry_on {A..B} d\<close> \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close>])
      also have "... \<le> dist ym xm + dist xm x + dist x xM + dist xM yM"
        unfolding um(2)[symmetric] uM(2)[symmetric] by (rule dist_triangle5)
      also have "... \<le> D + (2*D) + (2*D) + D"
        using \<open>dist xm ym \<le> D\<close> \<open>dist xm x \<le> 2*D\<close> \<open>dist xM x \<le> 2*D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      finally have "(1/lambda) * dist um uM \<le> 6*D + 4*C" by auto
      then have "dist um uM \<le> 6*D*lambda + 4*C*lambda"
        using C by (auto simp add: divide_simps algebra_simps)
      then have "L \<le> D + (6*D*lambda + 4*C*lambda) + D"
        unfolding L_def dist_real_def using \<open>dist xm ym \<le> D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      also have "... \<le> 8 * D * lambda + 4*C*lambda"
        using C \<open>D \<ge> 0\<close> by (auto intro: mono_intros)
      finally have L_bound: "L \<le> lambda * (8 * D + 4 * C)"
        by (auto simp add: algebra_simps)

      have "1 * (1 * 1 + 0) \<le> lambda * (8 * D + 4 * C)"
        using C \<open>D \<ge> 1\<close> by (intro mono_intros, auto)

      consider "um < uM" | "um = uM" | "um > uM" by linarith
      then have "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {min um uM..max um uM}"
        by (cases, auto)
      also have "... \<subseteq> {A..B}" using \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close> by auto
      finally have middle: "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {A..B}"
        by simp

      have "(2 * lambda)-lipschitz_on {0..L} excursion"
      proof (unfold L_def, rule lipschitz_on_closed_Union[of "{{0..dist xm ym}, {dist xm ym..dist xm ym + abs(uM - um)}, {dist xm ym + abs(uM - um)..dist xm ym + abs(uM - um) + dist yM xM}}" _ "\<lambda> i. i"], auto)
        show "lambda \<ge> 0" using C by auto

        have *: "1-lipschitz_on {0..dist xm ym} (geodesic_segment_param {xm--ym} xm)"
          by (rule isometry_on_lipschitz, simp)
        have **: "1-lipschitz_on {0..dist xm ym} excursion"
          using lipschitz_on_transform[OF * E1] by simp
        show "(2 * lambda)-lipschitz_on {0..dist xm ym} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have *: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}
                ((geodesic_segment_param {yM--xM} yM) o (\<lambda>t. t - (dist xm ym + abs (uM -um))))"
          by (intro lipschitz_intros, rule isometry_on_lipschitz, auto)
        have **: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_transform[OF *]) using E3 unfolding comp_def by (auto simp add: algebra_simps)
        show "(2 * lambda)-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have **: "((2 * lambda) * (0 + abs(sgn (uM - um)) * (1 + 0)))-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (intro lipschitz_intros, rule lipschitz_on_subset[OF _ middle])
          using \<open>(2 * lambda)-lipschitz_on {A..B} d\<close> by simp
        have ***: "(2 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (rule lipschitz_on_mono[OF **]) using C by auto
        show "(2 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} excursion"
          apply (rule lipschitz_on_transform[OF ***]) using E2 by auto
      qed

      have *: "dist x z \<ge> D" if z: "z \<in> excursion`{0..L}" for z
      proof -
        obtain tz where tz: "z = excursion tz" "tz \<in> {0..dist xm ym + abs(uM - um) + dist yM xM}"
          using z L_def by auto
        consider "tz \<in> {0..dist xm ym}" | "tz \<in> {dist xm ym<..dist xm ym + abs(uM - um)}" | "tz \<in> {dist xm ym + abs(uM - um)<..dist xm ym + abs(uM - um) + dist yM xM}"
          using tz by force
        then show ?thesis
        proof (cases)
          case 1
          then have "z \<in> {xm--ym}" unfolding tz(1) excursion_def by auto
          then show ?thesis using D1 by auto
        next
          case 3
          then have "z \<in> {yM--xM}" unfolding tz(1) excursion_def using tz(2) by auto
          then show ?thesis using D3 by (simp add: some_geodesic_commute)
        next
          case 2
          then have "z \<in> d`{A..B}" unfolding tz(1) excursion_def using middle by force
          then show ?thesis unfolding D_def by (simp add: infdist_le)
        qed
      qed

      text \<open>Now comes the main point: the excursion is always at distance at least $D$ of $x$,
      but this distance is also bounded by the log of its length, i.e., essentially $\log D$. To
      have an efficient estimate, we use a rescaled version, to get rid of one term on the right
      hand side.\<close>
      have "1 * 1 * 1 * (1 + 0/1) \<le> 512 * lambda * lambda * (1+C/D)"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      then have "ln (512 * lambda * lambda * (1+C/D)) \<ge> 0"
        apply (subst ln_ge_zero_iff) by auto
      define a where "a = 64 * lambda/D"
      have "a > 0" unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by auto

      have "D \<le> infdist x (excursion`{0..L})"
        unfolding infdist_def apply auto apply (rule cInf_greatest) using * by auto
      also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a * (L-0))) + (2 * lambda) / a"
      proof (rule lipschitz_path_close_to_geodesic'[of _ _ _ _ "geodesic_subsegment {c A--c B} (c A) tm tM"])
        show "(2 * lambda)-lipschitz_on {0..L} excursion" by fact
        have *: "geodesic_subsegment {c A--c B} (c A) tm tM = geodesic_segment_param {c A--c B} (c A) ` {tm..tM} "
          apply (rule geodesic_subsegment(1)[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
        show "x \<in> geodesic_subsegment {c A--c B} (c A) tm tM"
          unfolding * unfolding x_param tm_def tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>0 \<le> D\<close> by simp
        show "geodesic_segment_between (geodesic_subsegment {c A--c B} (c A) tm tM) (excursion 0) (excursion L)"
          unfolding E0 EL xm_def xM_def apply (rule geodesic_subsegment[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
      qed (fact)
      also have "... = (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a *L)) + D/32"
        unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by (simp add: algebra_simps)
      finally have "(31 * ln 2 / 128) * D \<le> deltaG(TYPE('a)) * max 0 (ln (a * L))"
        by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((64 * lambda/D) * (lambda * (8 * D + 4 * C))))"
        unfolding a_def apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((64 * lambda/D) * (lambda * (8 * D + 8 * C))))"
        apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      also have "... = deltaG(TYPE('a)) * max 0 (ln (512 * lambda * lambda * (1+C/D)))"
        using \<open>D \<ge> 1\<close> by (auto simp add: algebra_simps)
      also have "... = deltaG(TYPE('a)) * ln (512 * lambda * lambda * (1+C/D))"
        using \<open>ln (512 * lambda * lambda * (1+C/D)) \<ge> 0\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * ln (512 * lambda * lambda * (1+C/1))"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>D \<ge> 1\<close>
        by (auto simp add: divide_simps mult_ge1_mono(1))
      text \<open>We have obtained a bound on $D$, of the form $D \leq M \delta \ln(M \lambda^2(1+C))$.
      This is a nice bound, but we tweak it a little bit to obtain something more manageable,
      without the logarithm.\<close>
      also have "... = deltaG(TYPE('a)) * (ln 512 + 2 * ln lambda + ln (1+C))"
        apply (subst ln2mult) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) apply simp using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... = (deltaG(TYPE('a)) * 1) * ln 512 + 2 * (deltaG(TYPE('a)) * ln lambda) + (deltaG(TYPE('a)) * ln (1+C))"
        by (auto simp add: algebra_simps)
      text \<open>For each term, of the form $\delta \ln c$, we bound it by $(\delta^2 + (\ln c)^2)/2$, and
      then bound $(\ln c)^2$ by $2c-2$. In fact, to get coefficients of the same order of
      magnitude on $\delta^2$ and $\lambda$, we tweak a little bit the inequality for the last two
      terms, using rather $uv \leq (u^2/2 + 2v^2)/2$. We also bound $\ln(32)$ by a good
      approximation $16/3$.\<close>
      also have "... \<le> (deltaG(TYPE('a))^2/2 + 1^2/2) * (25/4)
            + 2 * ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln lambda)^2 / 2) + ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln (1+C))^2 / 2)"
        by (intro mono_intros, auto, approximation 10)
      also have "... = (31/8) * deltaG(TYPE('a))^2 + 25/8 + 2 * (ln lambda)^2 + (ln (1+C))^2"
        by (auto simp add: algebra_simps)
      also have "... \<le> 4 * deltaG(TYPE('a))^2 + 4 + 2 * (2 * lambda - 2) + (2 * (1+C) - 2)"
        apply (intro mono_intros) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... \<le> 4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C"
        by auto
      finally have "D \<le> (128 / (31 * ln 2)) * (4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        by (auto simp add: divide_simps algebra_simps)
      also have "... \<le> 6 * (4 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        apply (intro mono_intros, approximation 10) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      also have "... \<le> 24 * deltaG(TYPE('a))^2 + 24 * lambda + 12 * C"
        using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      finally show ?thesis by simp
    qed
    define D0 where "D0 = 24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2"
    have first_step: "infdist y (d`{A..B}) \<le> D0" if "y \<in> {c A--c B}" for y
      using x(2)[OF that] D_bound unfolding D0_def D_def by auto
    have "1 * 1 + 4 * 0 + 24 * 0 \<le> D0"
      unfolding D0_def apply (intro mono_intros) using C delta_nonneg by auto
    then have "D0 > 0" by simp
    text \<open>This is the end of the first step, i.e., showing that $[c(A), c(B)]$ is included in
    the neighborhood of size $D0$ of the quasi-geodesic.\<close>

    text \<open>Now, we start the second step: we show that the quasi-geodesic is included in the
    neighborhood of size $D1$ of the geodesic, where $D1 \geq D0$ is the constant defined below.
    The argument goes as follows. Assume that a point $y$ on the quasi-geodesic is at distance $ > D0$
    of the geodesic. Consider the last point $y_m$ before $y$ which is at distance $D0$ of the
    geodesic, and the first point $y_M$ after $y$ likewise. On $(y_m, y_M)$, one is always at distance
    $ > D0$ of the geodesic. However, by the first step, the geodesic is covered by the balls of radius
    $D0$ centered at points on the quasi-geodesic -- and only the points before $y_m$ or after $y_M$
    can be used. Let $K_m$ be the points on the geodesics that are at distance $\leq D0$ of a point
    on the quasi-geodesic before $y_m$, and likewise define $K_M$. These are two closed subsets of
    the geodesic. By connectedness, they have to intersect. This implies that some points before $y_m$
    and after $y_M$ are at distance at most $2D0$. Since we are dealing with a quasi-geodesic, this
    gives a bound on the distance between $y_m$ and $y_M$, and therefore a bound between $y$ and the
    geodesic, as desired.\<close>

    define D1 where "D1 = lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)"
    have "1 * 1 * (24 * lambda + 12 * C + 24 * deltaG(TYPE('a))^2)
            \<le> lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)"
      apply (intro mono_intros) using C by auto
    then have "D0 \<le> D1" unfolding D0_def D1_def by auto
    have second_step: "infdist y {c A--c B} \<le> D1" if "y \<in> d`{A..B}" for y
    proof (cases "infdist y {c A--c B} \<le> D0")
      case True
      then show ?thesis using \<open>D0 \<le> D1\<close> by auto
    next
      case False
      obtain ty where "ty \<in> {A..B}" "y = d ty" using \<open>y \<in> d`{A..B}\<close> by auto

      define tm where "tm = Sup ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
      have tm: "tm \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
      unfolding tm_def proof (rule closed_contains_Sup)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "A \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d A = c A\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty} \<noteq> {}" by auto
        show "bdd_above ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {A..ty})" by auto
      qed
      have *: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..ty}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using that tm by auto
        have "t \<le> tm" unfolding tm_def apply (rule cSup_upper) using * by auto
        then show False using that by auto
      qed

      define tM where "tM = Inf ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
      have tM: "tM \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
      unfolding tM_def proof (rule closed_contains_Inf)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "B \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d B = c B\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B} \<noteq> {}" by auto
        show "bdd_below ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {ty..B})" by auto
      qed
      have "infdist (d t) {c A--c B} > D0" if "t \<in> {ty..<tM}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using that tM by auto
        have "t \<ge> tM" unfolding tM_def apply (rule cInf_lower) using * by auto
        then show False using that by auto
      qed
      then have lower_tm_tM: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..<tM}" for t
        using * that by (cases "t \<ge> ty", auto)

      define Km where "Km = (\<Union>z \<in> d`{A..tm}. cball z D0)"
      define KM where "KM = (\<Union>z \<in> d`{tM..B}. cball z D0)"
      have "{c A--c B} \<subseteq> Km \<union> KM"
      proof
        fix x assume "x \<in> {c A--c B}"
        have "\<exists>z \<in> d`{A..B}. infdist x (d`{A..B}) = dist x z"
          apply (rule infdist_proper_attained[OF proper_of_compact], rule compact_continuous_image[OF \<open>continuous_on {A..B} d\<close>])
          using that by auto
        then obtain tx where "tx \<in> {A..B}" "infdist x (d`{A..B}) = dist x (d tx)" by blast
        then have "dist x (d tx) \<le> D0"
          using first_step[OF \<open>x \<in> {c A--c B}\<close>] by auto
        then have "x \<in> cball (d tx) D0" by (auto simp add: metric_space_class.dist_commute)
        consider "tx \<in> {A..tm}" | "tx \<in> {tm<..<tM}" | "tx \<in> {tM..B}"
          using \<open>tx \<in> {A..B}\<close> by fastforce
        then show "x \<in> Km \<union> KM"
        proof (cases)
          case 1
          then have "x \<in> Km" unfolding Km_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 3
          then have "x \<in> KM" unfolding KM_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 2
          have "infdist (d tx) {c A--c B} \<le> dist (d tx) x" using \<open>x \<in> {c A--c B}\<close> by (rule infdist_le)
          also have "... \<le> D0" using \<open>x \<in> cball (d tx) D0\<close> by auto
          finally have False using lower_tm_tM[OF 2] by simp
          then show ?thesis by simp
        qed
      qed
      then have *: "{c A--c B} = (Km \<inter> {c A--c B}) \<union> (KM \<inter> {c A--c B})" by auto
      have "(Km \<inter> {c A--c B}) \<inter> (KM \<inter> {c A--c B}) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed Km"
          unfolding Km_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tm \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (Km \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        have "closed KM"
          unfolding KM_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tM \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (KM \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        show "connected {c A--c B}" by simp
        have "c A \<in> Km \<inter> {c A--c B}" apply auto
          unfolding Km_def using tm \<open>d A = c A\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ A], auto)
        then show "Km \<inter> {c A--c B} \<noteq> {}" by auto
        have "c B \<in> KM \<inter> {c A--c B}" apply auto
          unfolding KM_def using tM \<open>d B = c B\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ B], auto)
        then show "KM \<inter> {c A--c B} \<noteq> {}" by auto
      qed
      then obtain w where "w \<in> {c A--c B}" "w \<in> Km" "w \<in> KM" by auto
      then obtain twm twM where tw: "twm \<in> {A..tm}" "w \<in> cball (d twm) D0" "twM \<in> {tM..B}" "w \<in> cball (d twM) D0"
        unfolding Km_def KM_def by auto
      have "(1/lambda) * dist twm twM - (4*C) \<le> dist (d twm) (d twM)"
        apply (rule quasi_isometry_onD(2)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> dist (d twm) w + dist w (d twM)"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> 2 * D0" using tw by (auto simp add: metric_space_class.dist_commute)
      finally have "dist twm twM \<le> lambda * (4*C + 2*D0)"
        using C by (auto simp add: divide_simps algebra_simps)
      then have *: "dist twm ty \<le> lambda * (4*C + 2*D0)"
        using tw tm tM dist_real_def by auto

      have "dist (d ty) w \<le> dist (d ty) (d twm) + dist (d twm) w"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> (lambda * dist ty twm + (4*C)) + D0"
        apply (intro add_mono, rule quasi_isometry_onD(1)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> (lambda * (lambda * (4*C + 2*D0))) + (4*C) + D0"
        apply (intro mono_intros) using C * by (auto simp add: metric_space_class.dist_commute)
      also have "... = lambda * lambda * (4*C + 2*D0) + 1 * 1 * (4 * C) + 1 * 1 * D0"
        by simp
      also have "... \<le> lambda * lambda * (4*C + 2*D0) + lambda * lambda * (4 * C) + lambda * lambda * D0"
        apply (intro mono_intros) using C * \<open>D0 > 0\<close> by auto
      also have "... = lambda * lambda * (8 * C + 3 * D0)"
        by (auto simp add: algebra_simps)
      also have "... = lambda * lambda * (44 * C + 72 * lambda + 72 * deltaG(TYPE('a))^2)"
        unfolding D0_def by auto
      finally have "dist y w \<le> D1" unfolding D1_def \<open>y = d ty\<close> by (auto simp add: algebra_simps)
      then show "infdist y {c A--c B} \<le> D1" using infdist_le[OF \<open>w \<in> {c A--c B}\<close>, of y] by auto
    qed
    text \<open>This concludes the second step.\<close>

    text \<open>Putting the two steps together, we deduce that the Hausdorff distance between the
    geodesic and the quasi-geodesic is bounded by $D1$. A bound between the geodesic and
    the original (untamed) quasi-geodesic follows.\<close>

    have a: "hausdorff_distance (d`{A..B}) {c A--c B} \<le> D1"
    proof (rule hausdorff_distanceI)
      show "D1 \<ge> 0" unfolding D1_def using C delta_nonneg by auto
      fix x assume "x \<in> d ` {A..B}"
      then show "infdist x {c A--c B} \<le> D1" using second_step by auto
    next
      fix x assume "x \<in> {c A--c B}"
      then show "infdist x (d`{A..B}) \<le> D1" using first_step \<open>D0 \<le> D1\<close> by force
    qed

    have "hausdorff_distance (c`{A..B}) {c A--c B} \<le>
        hausdorff_distance (c`{A..B}) (d`{A..B}) + hausdorff_distance (d`{A..B}) {c A--c B}"
      apply (rule hausdorff_distance_triangle)
      using \<open>A \<in> {A..B}\<close> apply blast
      by (rule quasi_isometry_on_bounded[OF d(5)], auto)
    also have "... \<le> D1 + 2*C" using a d by auto
    also have "... = lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2) + 1 * 1 * (2 * C)"
      unfolding D1_def by auto
    also have "... \<le> lambda * lambda * (72 * lambda + 44 * C + 72 * deltaG(TYPE('a))^2)
                      + lambda * lambda * (28 * C)"
      apply (intro mono_intros) using C delta_nonneg by auto
    also have "... = 72 * lambda^2 * (lambda + C + deltaG(TYPE('a))^2)"
      by (auto simp add: algebra_simps power2_eq_square)
    finally show ?thesis by (auto simp add: algebra_simps)
  qed
qed

end (*of theory Morse_Gromov_Theorem*)
