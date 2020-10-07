(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Isometries\<close>

theory Isometries
  imports Library_Complements Hausdorff_Distance
begin

text \<open>Isometries, i.e., functions that preserve distances, show up very often in mathematics.
We introduce a dedicated definition, and show its basic properties.\<close>

definition isometry_on::"('a::metric_space) set \<Rightarrow> ('a \<Rightarrow> ('b::metric_space)) \<Rightarrow> bool"
  where "isometry_on X f = (\<forall>x \<in> X. \<forall>y \<in> X. dist (f x) (f y) = dist x y)"

definition isometry :: "('a::metric_space \<Rightarrow> 'b::metric_space) \<Rightarrow> bool"
  where "isometry f \<equiv> isometry_on UNIV f \<and> range f = UNIV"

lemma isometry_on_subset:
  assumes "isometry_on X f"
          "Y \<subseteq> X"
  shows "isometry_on Y f"
using assms unfolding isometry_on_def by auto

lemma isometry_onI [intro?]:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) = dist x y"
  shows "isometry_on X f"
using assms unfolding isometry_on_def by auto

lemma isometry_onD:
  assumes "isometry_on X f"
          "x \<in> X" "y \<in> X"
  shows "dist (f x) (f y) = dist x y"
using assms unfolding isometry_on_def by auto

lemma isometryI [intro?]:
  assumes "\<And>x y. dist (f x) (f y) = dist x y"
          "range f = UNIV"
  shows "isometry f"
unfolding isometry_def isometry_on_def using assms by auto

lemma
  assumes "isometry_on X f"
  shows isometry_on_lipschitz: "1-lipschitz_on X f"
    and isometry_on_uniformly_continuous: "uniformly_continuous_on X f"
    and isometry_on_continuous: "continuous_on X f"
proof -
  show "1-lipschitz_on X f" apply (rule lipschitz_onI) using isometry_onD[OF assms] by auto
  then show "uniformly_continuous_on X f" "continuous_on X f"
    using lipschitz_on_uniformly_continuous lipschitz_on_continuous_on by auto
qed

lemma isometryD:
  assumes "isometry f"
  shows "isometry_on UNIV f"
        "dist (f x) (f y) = dist x y"
        "range f = UNIV"
        "1-lipschitz_on UNIV f"
        "uniformly_continuous_on UNIV f"
        "continuous_on UNIV f"
using assms unfolding isometry_def isometry_on_def apply auto
using isometry_on_lipschitz isometry_on_uniformly_continuous isometry_on_continuous assms unfolding isometry_def by blast+

lemma isometry_on_injective:
  assumes "isometry_on X f"
  shows "inj_on f X"
using assms inj_on_def isometry_on_def by force

lemma isometry_on_compose:
  assumes "isometry_on X f"
          "isometry_on (f`X) g"
  shows "isometry_on X (\<lambda>x. g(f x))"
using assms unfolding isometry_on_def by auto

lemma isometry_on_cong:
  assumes "isometry_on X f"
          "\<And>x. x \<in> X \<Longrightarrow> g x = f x"
  shows "isometry_on X g"
using assms unfolding isometry_on_def by auto

lemma isometry_on_inverse:
  assumes "isometry_on X f"
  shows "isometry_on (f`X) (inv_into X f)"
        "\<And>x. x \<in> X \<Longrightarrow> (inv_into X f) (f x) = x"
        "\<And>y. y \<in> f`X \<Longrightarrow> f (inv_into X f y) = y"
        "bij_betw f X (f`X)"
proof -
  show *: "bij_betw f X (f`X)"
    using assms unfolding bij_betw_def inj_on_def isometry_on_def by force
  show "isometry_on (f`X) (inv_into X f)"
    using assms unfolding isometry_on_def
    by (auto) (metis (mono_tags, lifting) dist_eq_0_iff inj_on_def inv_into_f_f)
  fix x assume "x \<in> X"
  then show "(inv_into X f) (f x) = x"
    using * by (simp add: bij_betw_def)
next
  fix y assume "y \<in> f`X"
  then show "f (inv_into X f y) = y"
    by (simp add: f_inv_into_f)
qed

lemma isometry_inverse:
  assumes "isometry f"
  shows "isometry (inv f)"
        "bij f"
using isometry_on_inverse[OF isometryD(1)[OF assms]] isometryD(3)[OF assms]
unfolding isometry_def by (auto simp add: bij_imp_bij_inv bij_is_surj)

lemma isometry_on_homeomorphism:
  assumes "isometry_on X f"
  shows "homeomorphism X (f`X) f (inv_into X f)"
        "homeomorphism_on X f"
        "X homeomorphic f`X"
proof -
  show *: "homeomorphism X (f`X) f (inv_into X f)"
    apply (rule homeomorphismI) using uniformly_continuous_imp_continuous[OF isometry_on_uniformly_continuous]
    isometry_on_inverse[OF assms] assms by auto
  then show "X homeomorphic f`X"
    unfolding homeomorphic_def by auto
  show "homeomorphism_on X f"
    unfolding homeomorphism_on_def using * by auto
qed

lemma isometry_homeomorphism:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::metric_space)"
  assumes "isometry f"
  shows "homeomorphism UNIV UNIV f (inv f)"
        "(UNIV::'a set) homeomorphic (UNIV::'b set)"
using isometry_on_homeomorphism[OF isometryD(1)[OF assms]] isometryD(3)[OF assms] by auto

lemma isometry_on_closure:
  assumes "isometry_on X f"
          "continuous_on (closure X) f"
  shows "isometry_on (closure X) f"
proof (rule isometry_onI)
  fix x y assume "x \<in> closure X" "y \<in> closure X"
  obtain u v::"nat \<Rightarrow> 'a" where *: "\<And>n. u n \<in> X" "u \<longlonglongrightarrow> x"
                                   "\<And>n. v n \<in> X" "v \<longlonglongrightarrow> y"
    using \<open>x \<in> closure X\<close> \<open>y \<in> closure X\<close> unfolding closure_sequential by blast
  have "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f x"
    using *(1) *(2) \<open>x \<in> closure X\<close> \<open>continuous_on (closure X) f\<close>
    unfolding comp_def continuous_on_closure_sequentially[of X f] by auto
  moreover have "(\<lambda>n. f (v n)) \<longlonglongrightarrow> f y"
    using *(3) *(4) \<open>y \<in> closure X\<close> \<open>continuous_on (closure X) f\<close>
    unfolding comp_def continuous_on_closure_sequentially[of X f] by auto
  ultimately have "(\<lambda>n. dist (f (u n)) (f (v n))) \<longlonglongrightarrow> dist (f x) (f y)"
    by (simp add: tendsto_dist)
  then have "(\<lambda>n. dist (u n) (v n)) \<longlonglongrightarrow> dist (f x) (f y)"
    using assms(1) *(1) *(3) unfolding isometry_on_def by auto
  moreover have "(\<lambda>n. dist (u n) (v n)) \<longlonglongrightarrow> dist x y"
    using *(2) *(4) by (simp add: tendsto_dist)
  ultimately show "dist (f x) (f y) = dist x y" using LIMSEQ_unique by auto
qed

lemma isometry_extend_closure:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "isometry_on X f"
  shows "\<exists>g. isometry_on (closure X) g \<and> (\<forall>x\<in>X. g x = f x)"
proof -
  obtain g where g: "\<And>x. x \<in> X \<Longrightarrow> g x = f x" "uniformly_continuous_on (closure X) g"
    using uniformly_continuous_on_extension_on_closure[OF isometry_on_uniformly_continuous[OF assms]] by metis
  have "isometry_on (closure X) g"
    apply (rule isometry_on_closure, rule isometry_on_cong[OF assms])
    using g uniformly_continuous_imp_continuous[OF g(2)] by auto
  then show ?thesis using g(1) by auto
qed

lemma isometry_on_complete_image:
  assumes "isometry_on X f"
          "complete X"
  shows "complete (f`X)"
proof (rule completeI)
  fix u :: "nat \<Rightarrow> 'b" assume u: "\<forall>n. u n \<in> f`X" "Cauchy u"
  define v where "v = (\<lambda>n. inv_into X f (u n))"
  have "v n \<in> X" for n
    unfolding v_def by (simp add: inv_into_into u(1))
  have "dist (v n) (v m) = dist (u n) (u m)" for m n
    using u(1) isometry_on_inverse[OF \<open>isometry_on X f\<close>] unfolding isometry_on_def v_def by (auto simp add: inv_into_into)
  then have "Cauchy v"
    using u(2) unfolding Cauchy_def by auto
  obtain l where "l \<in> X" "v \<longlonglongrightarrow> l"
    apply (rule completeE[OF \<open>complete X\<close> _ \<open>Cauchy v\<close>]) using \<open>\<And>n. v n \<in> X\<close> by auto
  have "(\<lambda>n. f (v n)) \<longlonglongrightarrow> f l"
    apply (rule continuous_on_tendsto_compose[OF isometry_on_continuous[OF \<open>isometry_on X f\<close>]])
    using \<open>\<And>n. v n \<in> X\<close> \<open>l \<in> X\<close> \<open>v \<longlonglongrightarrow> l\<close> by auto
  moreover have "f(v n) = u n" for n
    unfolding v_def by (simp add: f_inv_into_f u(1))
  ultimately have "u \<longlonglongrightarrow> f l" by auto
  then show "\<exists>m \<in> f`X. u \<longlonglongrightarrow> m" using \<open>l \<in> X\<close> by auto
qed

lemma isometry_on_id [simp]:
  "isometry_on A (\<lambda>x. x)"
  "isometry_on A id"
unfolding isometry_on_def by auto

lemma isometry_on_add [simp]:
  "isometry_on A (\<lambda>x. x + (t::'a::real_normed_vector))"
unfolding isometry_on_def by auto

lemma isometry_on_minus [simp]:
  "isometry_on A (\<lambda>(x::'a::real_normed_vector). -x)"
unfolding isometry_on_def by (auto simp add: dist_minus)

lemma isometry_on_diff [simp]:
  "isometry_on A (\<lambda>x. (t::'a::real_normed_vector) - x)"
unfolding isometry_on_def by (auto, metis add_uminus_conv_diff dist_add_cancel dist_minus)

lemma isometry_preserves_bounded:
  assumes "isometry_on X f"
          "A \<subseteq> X"
  shows "bounded (f`A) \<longleftrightarrow> bounded A"
unfolding bounded_two_points using assms(2) isometry_onD[OF assms(1)] by auto (metis assms(2) rev_subsetD)+

lemma isometry_preserves_infdist:
  "infdist (f x) (f`A) = infdist x A"
  if "isometry_on X f" "A \<subseteq> X" "x \<in> X"
  using that by (simp add: infdist_def image_comp isometry_on_def subset_iff)

lemma isometry_preserves_hausdorff_distance:
  "hausdorff_distance (f`A) (f`B) = hausdorff_distance A B"
  if "isometry_on X f" "A \<subseteq> X" "B \<subseteq> X"
  using that isometry_preserves_infdist [OF that(1) that(2)]
  isometry_preserves_infdist [OF that(1) that(3)]
  isometry_preserves_bounded [OF that(1) that(2)]
  isometry_preserves_bounded [OF that(1) that(3)]
  by (simp add: hausdorff_distance_def image_comp subset_eq)

lemma isometry_on_UNIV_iterates:
  fixes f::"('a::metric_space) \<Rightarrow> 'a"
  assumes "isometry_on UNIV f"
  shows "isometry_on UNIV (f^^n)"
by (induction n, auto, rule isometry_on_compose[of _ _ f], auto intro: isometry_on_subset[OF assms])

lemma isometry_iterates:
  fixes f::"('a::metric_space) \<Rightarrow> 'a"
  assumes "isometry f"
  shows "isometry (f^^n)"
using isometry_on_UNIV_iterates[OF isometryD(1)[OF assms], of n] bij_fn[OF isometry_inverse(2)[OF assms], of n]
unfolding isometry_def by (simp add: bij_is_surj)

section \<open>Geodesic spaces\<close>

text \<open>A geodesic space is a metric space in which any pair of points can be joined by a geodesic segment,
i.e., an isometrically embedded copy of a segment in the real line. Most spaces in geometry are
geodesic. We introduce in this section the corresponding class of metric spaces. First, we study
properties of general geodesic segments in metric spaces.\<close>

subsection \<open>Geodesic segments in general metric spaces\<close>

definition geodesic_segment_between::"('a::metric_space) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "geodesic_segment_between G x y = (\<exists>g::(real \<Rightarrow> 'a). g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g`{0..dist x y})"

definition geodesic_segment::"('a::metric_space) set \<Rightarrow> bool"
  where "geodesic_segment G = (\<exists>x y. geodesic_segment_between G x y)"

text \<open>We also introduce the parametrization of a geodesic segment. It is convenient to use the
following definition, which guarantees that the point is on $G$ even without checking that $G$
is a geodesic segment or that the parameter is in the reasonable range: this shortens some
arguments below.\<close>

definition geodesic_segment_param::"('a::metric_space) set \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "geodesic_segment_param G x t = (if \<exists>w. w \<in> G \<and> dist x w = t then SOME w. w \<in> G \<and> dist x w = t else SOME w. w \<in> G)"

lemma geodesic_segment_betweenI:
  assumes "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
  shows "geodesic_segment_between G x y"
unfolding geodesic_segment_between_def apply (rule exI[of _ g]) using assms by auto

lemma geodesic_segmentI [intro, simp]:
  assumes "geodesic_segment_between G x y"
  shows "geodesic_segment G"
unfolding geodesic_segment_def using assms by auto

lemma geodesic_segmentI2 [intro]:
  assumes "isometry_on {a..b} g" "a \<le> (b::real)"
  shows "geodesic_segment_between (g`{a..b}) (g a) (g b)"
        "geodesic_segment (g`{a..b})"
proof -
  define h where "h = (\<lambda>t. g (t+a))"
  have *: "isometry_on {0..b-a} h"
    apply (rule isometry_onI)
    using \<open>isometry_on {a..b} g\<close> \<open>a \<le> b\<close> by (auto simp add: isometry_on_def h_def)
  have **: "dist (h 0) (h (b-a)) = b-a"
    using isometry_onD[OF \<open>isometry_on {0..b-a} h\<close>, of 0 "b-a"] \<open>a \<le> b\<close> unfolding dist_real_def by auto
  have "geodesic_segment_between (h`{0..b-a}) (h 0) (h (b-a))"
    unfolding geodesic_segment_between_def apply (rule exI[of _ h]) unfolding ** using * by auto
  moreover have "g`{a..b} = h`{0..b-a}"
    unfolding h_def apply (auto simp add: image_iff)
    by (metis add.commute atLeastAtMost_iff diff_ge_0_iff_ge diff_right_mono le_add_diff_inverse)
  moreover have "h 0 = g a" "h (b-a) = g b" unfolding h_def by auto
  ultimately show "geodesic_segment_between (g`{a..b}) (g a) (g b)" by auto
  then show "geodesic_segment (g`{a..b})" unfolding geodesic_segment_def by auto
qed

lemma geodesic_segmentD:
  assumes "geodesic_segment_between G x y"
  shows "\<exists>g::(real \<Rightarrow> _). (g t = x \<and> g (t + dist x y) = y \<and> isometry_on {t..t+dist x y} g \<and> G = g`{t..t+dist x y})"
proof -
  obtain h where h: "h 0 = x" "h (dist x y) = y" "isometry_on {0..dist x y} h" "G = h`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  have * [simp]: "(\<lambda>x. x - t) ` {t..t + dist x y} = {0..dist x y}" by auto
  define g where "g = (\<lambda>s. h (s - t))"
  have "g t = x" "g (t + dist x y) = y" using h assms(1) unfolding g_def by auto
  moreover have "isometry_on {t..t+dist x y} g"
    unfolding g_def apply (rule isometry_on_compose[of _ _ h])
    by (simp add: dist_real_def isometry_on_def, simp add: h(3))
  moreover have "g` {t..t + dist x y} = G" unfolding g_def h(4) using * by (metis image_image)
  ultimately show ?thesis by auto
qed

lemma geodesic_segment_endpoints [simp]:
  assumes "geodesic_segment_between G x y"
  shows "x \<in> G" "y \<in> G" "G \<noteq> {}"
using assms unfolding geodesic_segment_between_def
  by (auto, metis atLeastAtMost_iff image_eqI less_eq_real_def zero_le_dist)

lemma geodesic_segment_commute:
  assumes "geodesic_segment_between G x y"
  shows "geodesic_segment_between G y x"
proof -
  obtain g::"real\<Rightarrow>'a" where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  define h::"real\<Rightarrow>'a" where "h = (\<lambda>t. g(dist x y-t))"
  have "(\<lambda>t. dist x y -t)`{0..dist x y} = {0..dist x y}" by auto
  then have "h`{0..dist x y} = G" unfolding g(4) h_def by (metis image_image)
  moreover have "h 0 = y" "h (dist x y) = x" unfolding h_def using g by auto
  moreover have "isometry_on {0..dist x y} h"
    unfolding h_def apply (rule isometry_on_compose[of _ _ g]) using g(3) by auto
  ultimately show ?thesis
    unfolding geodesic_segment_between_def by (auto simp add: dist_commute)
qed

lemma geodesic_segment_dist:
  assumes "geodesic_segment_between G x y" "a \<in> G"
  shows "dist x a + dist a y = dist x y"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain t where t: "t \<in> {0..dist x y}" "a = g t"
    using g(4) assms by auto
  have "dist x a = t" using isometry_onD[OF g(3) _ t(1), of 0]
    unfolding g(1) dist_real_def t(2) using t(1) by auto
  moreover have "dist a y = dist x y - t" using isometry_onD[OF g(3) _ t(1), of "dist x y"]
    unfolding g(2) dist_real_def t(2) using t(1) by (auto simp add: dist_commute)
  ultimately show ?thesis by auto
qed

lemma geodesic_segment_dist_unique:
  assumes "geodesic_segment_between G x y" "a \<in> G" "b \<in> G" "dist x a = dist x b"
  shows "a = b"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain ta where ta: "ta \<in> {0..dist x y}" "a = g ta"
    using g(4) assms by auto
  have *: "dist x a = ta"
    unfolding g(1)[symmetric] ta(2) using isometry_onD[OF g(3), of 0 ta]
    unfolding dist_real_def using ta(1) by auto
  obtain tb where tb: "tb \<in> {0..dist x y}" "b = g tb"
    using g(4) assms by auto
  have "dist x b = tb"
    unfolding g(1)[symmetric] tb(2) using isometry_onD[OF g(3), of 0 tb]
    unfolding dist_real_def using tb(1) by auto
  then have "ta = tb" using * \<open>dist x a = dist x b\<close> by auto
  then show "a = b" using ta(2) tb(2) by auto
qed

lemma geodesic_segment_union:
  assumes "dist x z = dist x y + dist y z"
          "geodesic_segment_between G x y" "geodesic_segment_between H y z"
  shows "geodesic_segment_between (G \<union> H) x z"
        "G \<inter> H = {y}"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain h where h: "h (dist x y) = y" "h (dist x z) = z" "isometry_on {dist x y..dist x z} h" "H = h`{dist x y..dist x z}"
    unfolding \<open>dist x z = dist x y + dist y z\<close>
    using geodesic_segmentD[OF \<open>geodesic_segment_between H y z\<close>, of "dist x y"] by auto
  define f where "f = (\<lambda>t. if t \<le> dist x y then g t else h t)"
  have fg: "f t = g t" if "t \<le> dist x y" for t
    unfolding f_def using that by auto
  have fh: "f t = h t" if "t \<ge> dist x y" for t
    unfolding f_def apply (cases "t > dist x y") using that g(2) h(1) by auto

  have "f 0 = x" "f (dist x z) = z" using fg fh g(1) h(2) assms(1) by auto

  have "f`{0..dist x z} = f`{0..dist x y} \<union> f`{dist x y..dist x z}"
    unfolding assms(1) image_Un[symmetric] by (simp add: ivl_disj_un_two_touch(4))
  moreover have "f`{0..dist x y} = G"
    unfolding g(4) using fg image_cong by force
  moreover have "f`{dist x y..dist x z} = H"
    unfolding h(4) using fh image_cong by force
  ultimately have "f`{0..dist x z} = G \<union> H" by simp

  have Ifg: "dist (f s) (f t) = s-t" if "0 \<le> t" "t \<le> s" "s \<le> dist x y" for s t
    using that fg[of s] fg[of t] isometry_onD[OF g(3), of s t] unfolding dist_real_def by auto
  have Ifh: "dist (f s) (f t) = s-t" if "dist x y \<le> t" "t \<le> s" "s \<le> dist x z" for s t
    using that fh[of s] fh[of t] isometry_onD[OF h(3), of s t] unfolding dist_real_def by auto

  have I: "dist (f s) (f t) = s-t" if "0 \<le> t" "t \<le> s" "s \<le> dist x z" for s t
  proof -
    consider "t \<le> dist x y \<and> s \<ge> dist x y" | "s \<le> dist x y" | "t \<ge> dist x y" by fastforce
    then show ?thesis
    proof (cases)
      case 1
      have "dist (f t) (f s) \<le> dist (f t) (f (dist x y)) + dist (f (dist x y)) (f s)"
        using dist_triangle by auto
      also have "... \<le> (dist x y - t) + (s - dist x y)"
        using that 1 Ifg[of t "dist x y"] Ifh[of "dist x y" s] by (auto simp add: dist_commute intro: mono_intros)
      finally have *: "dist (f t) (f s) \<le> s - t" by simp

      have "dist x z \<le> dist (f 0) (f t) + dist (f t) (f s) + dist (f s) (f (dist x z))"
        unfolding \<open>f 0 = x\<close> \<open>f (dist x z) = z\<close> using dist_triangle4 by auto
      also have "... \<le> t + dist (f t) (f s) + (dist x z - s)"
        using that 1 Ifg[of 0 t] Ifh[of s "dist x z"] by (auto simp add: dist_commute intro: mono_intros)
      finally have "s - t \<le> dist (f t) (f s)" by auto
      then show "dist (f s) (f t) = s-t" using * dist_commute by auto
    next
      case 2
      then show ?thesis using Ifg that by auto
    next
      case 3
      then show ?thesis using Ifh that by auto
    qed
  qed
  have "isometry_on {0..dist x z} f"
    unfolding isometry_on_def dist_real_def using I
    by (auto, metis abs_of_nonneg dist_commute dist_real_def le_cases zero_le_dist)
  then show "geodesic_segment_between (G \<union> H) x z"
    unfolding geodesic_segment_between_def
    using \<open>f 0 = x\<close> \<open>f (dist x z) = z\<close> \<open>f`{0..dist x z} = G \<union> H\<close> by auto
  have "G \<inter> H \<subseteq> {y}"
  proof (auto)
    fix a assume a: "a \<in> G" "a \<in> H"
    obtain s where s: "s \<in> {0..dist x y}" "a = g s" using a g(4) by auto
    obtain t where t: "t \<in> {dist x y..dist x z}" "a = h t" using a h(4) by auto
    have "a = f s" using fg s by auto
    moreover have "a = f t" using fh t by auto
    ultimately have "s = t" using isometry_onD[OF \<open>isometry_on {0..dist x z} f\<close>, of s t] s(1) t(1) by auto
    then have "s = dist x y" using s t by auto
    then show "a = y" using s(2) g by auto
  qed
  then show "G \<inter> H = {y}" using assms by auto
qed

lemma geodesic_segment_dist_le:
  assumes "geodesic_segment_between G x y" "a \<in> G" "b \<in> G"
  shows "dist a b \<le> dist x y"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain s t where st: "s \<in> {0..dist x y}" "t \<in> {0..dist x y}" "a = g s" "b = g t"
    using g(4) assms by auto
  have "dist a b = abs(s-t)" using isometry_onD[OF g(3) st(1) st(2)]
    unfolding st(3) st(4) dist_real_def by simp
  then show "dist a b \<le> dist x y" using st(1) st(2) unfolding dist_real_def by auto
qed

lemma geodesic_segment_param [simp]:
  assumes "geodesic_segment_between G x y"
  shows "geodesic_segment_param G x 0 = x"
        "geodesic_segment_param G x (dist x y) = y"
        "t \<in> {0..dist x y} \<Longrightarrow> geodesic_segment_param G x t \<in> G"
        "isometry_on {0..dist x y} (geodesic_segment_param G x)"
        "(geodesic_segment_param G x)`{0..dist x y} = G"
        "t \<in> {0..dist x y} \<Longrightarrow> dist x (geodesic_segment_param G x t) = t"
        "s \<in> {0..dist x y} \<Longrightarrow> t \<in> {0..dist x y} \<Longrightarrow> dist (geodesic_segment_param G x s) (geodesic_segment_param G x t) = abs(s-t)"
        "z \<in> G \<Longrightarrow> z = geodesic_segment_param G x (dist x z)"
proof -
  obtain g::"real\<Rightarrow>'a" where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  have *: "g t \<in> G \<and> dist x (g t) = t" if "t \<in> {0..dist x y}" for t
    using isometry_onD[OF g(3), of 0 t] that g(1) g(4) unfolding dist_real_def by auto
  have G: "geodesic_segment_param G x t = g t" if "t \<in> {0..dist x y}" for t
  proof -
    have A: "geodesic_segment_param G x t \<in> G \<and> dist x (geodesic_segment_param G x t) = t"
      using *[OF that] unfolding geodesic_segment_param_def apply auto
      using *[OF that] by (metis (mono_tags, lifting) someI)+
    obtain s where s: "geodesic_segment_param G x t = g s" "s \<in> {0..dist x y}"
      using A g(4) by auto
    have "s = t" using *[OF \<open>s \<in> {0..dist x y}\<close>] A unfolding s(1) by auto
    then show ?thesis using s by auto
  qed
  show "geodesic_segment_param G x 0 = x"
       "geodesic_segment_param G x (dist x y) = y"
       "t \<in> {0..dist x y} \<Longrightarrow> geodesic_segment_param G x t \<in> G"
       "isometry_on {0..dist x y} (geodesic_segment_param G x)"
       "(geodesic_segment_param G x)`{0..dist x y} = G"
       "t \<in> {0..dist x y} \<Longrightarrow> dist x (geodesic_segment_param G x t) = t"
       "s \<in> {0..dist x y} \<Longrightarrow> t \<in> {0..dist x y} \<Longrightarrow> dist (geodesic_segment_param G x s) (geodesic_segment_param G x t) = abs(s-t)"
       "z \<in> G \<Longrightarrow> z = geodesic_segment_param G x (dist x z)"
    using G g apply (auto simp add: rev_image_eqI)
    using G isometry_on_cong * atLeastAtMost_iff apply blast
    using G isometry_on_cong * atLeastAtMost_iff apply blast
    by (auto simp add: * dist_real_def isometry_onD)
qed

lemma geodesic_segment_param_in_segment:
  assumes "G \<noteq> {}"
  shows "geodesic_segment_param G x t \<in> G"
unfolding geodesic_segment_param_def
apply (auto, metis (mono_tags, lifting) someI)
using assms some_in_eq by fastforce

lemma geodesic_segment_reverse_param:
  assumes "geodesic_segment_between G x y"
          "t \<in> {0..dist x y}"
  shows "geodesic_segment_param G y (dist x y - t) = geodesic_segment_param G x t"
proof -
  have * [simp]: "geodesic_segment_between G y x"
    using geodesic_segment_commute[OF assms(1)] by simp
  have "geodesic_segment_param G y (dist x y - t) \<in> G"
    apply (rule geodesic_segment_param(3)[of _ _ x])
    using assms(2) by (auto simp add: dist_commute)
  moreover have "dist (geodesic_segment_param G y (dist x y - t)) x = t"
    using geodesic_segment_param(2)[OF *] geodesic_segment_param(7)[OF *, of "dist x y -t" "dist x y"] assms(2) by (auto simp add: dist_commute)
  moreover have "geodesic_segment_param G x t \<in> G"
    apply (rule geodesic_segment_param(3)[OF assms(1)])
    using assms(2) by auto
  moreover have "dist (geodesic_segment_param G x t) x = t"
    using geodesic_segment_param(6)[OF assms] by (simp add: dist_commute)
  ultimately show ?thesis
    using geodesic_segment_dist_unique[OF assms(1)] by (simp add: dist_commute)
qed

lemma dist_along_geodesic_wrt_endpoint:
  assumes "geodesic_segment_between G x y"
          "u \<in> G" "v \<in> G"
  shows "dist u v = abs(dist u x - dist v x)"
proof -
  have *: "u = geodesic_segment_param G x (dist x u)" "v = geodesic_segment_param G x (dist x v)"
    using assms by auto
  have "dist u v = dist (geodesic_segment_param G x (dist x u)) (geodesic_segment_param G x (dist x v))"
    using * by auto
  also have "... = abs(dist x u - dist x v)"
    apply (rule geodesic_segment_param(7)[OF assms(1)]) using assms apply auto
    using geodesic_segment_dist_le geodesic_segment_endpoints(1) by blast+
  finally show ?thesis by (simp add: dist_commute)
qed

text \<open>One often needs to restrict a geodesic segment to a subsegment. We introduce the tools
to express this conveniently.\<close>
definition geodesic_subsegment::"('a::metric_space) set \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set"
  where "geodesic_subsegment G x s t = G \<inter> {z. dist x z \<ge> s \<and> dist x z \<le> t}"

text \<open>A subsegment is always contained in the original segment.\<close>
lemma geodesic_subsegment_subset:
  "geodesic_subsegment G x s t \<subseteq> G"
unfolding geodesic_subsegment_def by simp

text \<open>A subsegment is indeed a geodesic segment, and its endpoints and parametrization can be
expressed in terms of the original segment.\<close>
lemma geodesic_subsegment:
  assumes "geodesic_segment_between G x y"
          "0 \<le> s" "s \<le> t" "t \<le> dist x y"
  shows "geodesic_subsegment G x s t = (geodesic_segment_param G x)`{s..t}"
        "geodesic_segment_between (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (geodesic_segment_param G x t)"
        "\<And>u. s \<le> u \<Longrightarrow> u \<le> t \<Longrightarrow> geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) = geodesic_segment_param G x u"
proof -
  show A: "geodesic_subsegment G x s t = (geodesic_segment_param G x)`{s..t}"
  proof (auto)
    fix y assume y: "y \<in> geodesic_subsegment G x s t"
    have "y = geodesic_segment_param G x (dist x y)"
      apply (rule geodesic_segment_param(8)[OF assms(1)])
      using y geodesic_subsegment_subset by force
    moreover have "dist x y \<ge> s \<and> dist x y \<le> t"
      using y unfolding geodesic_subsegment_def by auto
    ultimately show "y \<in> geodesic_segment_param G x ` {s..t}" by auto
  next
    fix u assume H: "s \<le> u" "u \<le> t"
    have *: "dist x (geodesic_segment_param G x u) = u"
      apply (rule geodesic_segment_param(6)[OF assms(1)]) using H assms by auto
    show "geodesic_segment_param G x u \<in> geodesic_subsegment G x s t"
      unfolding geodesic_subsegment_def
      using geodesic_segment_param_in_segment[OF geodesic_segment_endpoints(3)[OF assms(1)]] by (auto simp add: * H)
  qed

  have *: "isometry_on {s..t} (geodesic_segment_param G x)"
    by (rule isometry_on_subset[of "{0..dist x y}"]) (auto simp add: assms)
  show B: "geodesic_segment_between (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (geodesic_segment_param G x t)"
    unfolding A apply (rule geodesic_segmentI2) using * assms by auto

  fix u assume u: "s \<le> u" "u \<le> t"
  show "geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) = geodesic_segment_param G x u"
  proof (rule geodesic_segment_dist_unique[OF B])
    show "geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) \<in> geodesic_subsegment G x s t"
      by (rule geodesic_segment_param_in_segment[OF geodesic_segment_endpoints(3)[OF B]])
    show "geodesic_segment_param G x u \<in> geodesic_subsegment G x s t"
      unfolding A using u by auto
    have "dist (geodesic_segment_param G x s) (geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s)) = u - s"
      using B assms u by auto
    moreover have "dist (geodesic_segment_param G x s) (geodesic_segment_param G x u) = u -s"
      using assms u by auto
    ultimately show "dist (geodesic_segment_param G x s) (geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s)) =
        dist (geodesic_segment_param G x s) (geodesic_segment_param G x u)"
      by simp
  qed
qed

text \<open>The parameterizations of a segment and a subsegment sharing an endpoint coincide where defined.\<close>
lemma geodesic_segment_subparam:
  assumes "geodesic_segment_between G x z" "geodesic_segment_between H x y" "H \<subseteq> G" "t \<in> {0..dist x y}"
  shows "geodesic_segment_param G x t = geodesic_segment_param H x t"
proof -
  have "geodesic_segment_param H x t \<in> G"
    using assms(3) geodesic_segment_param(3)[OF assms(2) assms(4)] by auto
  then have "geodesic_segment_param H x t = geodesic_segment_param G x (dist x (geodesic_segment_param H x t))"
    using geodesic_segment_param(8)[OF assms(1)] by auto
  then show ?thesis using geodesic_segment_param(6)[OF assms(2) assms(4)] by auto
qed

text \<open>A segment contains a subsegment between any of its points\<close>
lemma geodesic_subsegment_exists:
  assumes "geodesic_segment G" "x \<in> G" "y \<in> G"
  shows "\<exists>H. H \<subseteq> G \<and> geodesic_segment_between H x y"
proof -
  obtain a0 b0 where Ga0b0: "geodesic_segment_between G a0 b0"
    using assms(1) unfolding geodesic_segment_def by auto
  text \<open>Permuting the endpoints if necessary, we can ensure that the first endpoint $a$ is closer
  to $x$ than $y$.\<close>
  have "\<exists> a b. geodesic_segment_between G a b \<and> dist x a \<le> dist y a"
  proof (cases "dist x a0 \<le> dist y a0")
    case True
    show ?thesis
      apply (rule exI[of _ a0], rule exI[of _ b0]) using True Ga0b0 by auto
  next
    case False
    show ?thesis
      apply (rule exI[of _ b0], rule exI[of _ a0])
      using Ga0b0 geodesic_segment_commute geodesic_segment_dist[OF Ga0b0 \<open>x \<in> G\<close>] geodesic_segment_dist[OF Ga0b0 \<open>y \<in> G\<close>] False
      by (auto simp add: dist_commute)
  qed
  then obtain a b where Gab: "geodesic_segment_between G a b" "dist x a \<le> dist y a"
    by auto
  have *: "0 \<le> dist x a" "dist x a \<le> dist y a" "dist y a \<le> dist a b"
    using Gab assms by (meson geodesic_segment_dist_le geodesic_segment_endpoints(1) zero_le_dist)+
  have **: "x = geodesic_segment_param G a (dist x a)" "y = geodesic_segment_param G a (dist y a)"
    using Gab \<open>x \<in> G\<close> \<open>y \<in> G\<close> by (metis dist_commute geodesic_segment_param(8))+
  define H where "H = geodesic_subsegment G a (dist x a) (dist y a)"
  have "H \<subseteq> G"
    unfolding H_def by (rule geodesic_subsegment_subset)
  moreover have "geodesic_segment_between H x y"
    unfolding H_def using geodesic_subsegment(2)[OF Gab(1) *] ** by auto
  ultimately show ?thesis by auto
qed

text \<open>A geodesic segment is homeomorphic to an interval.\<close>
lemma geodesic_segment_homeo_interval:
  assumes "geodesic_segment_between G x y"
  shows "{0..dist x y} homeomorphic G"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  show ?thesis using isometry_on_homeomorphism(3)[OF g(3)] unfolding g(4) by simp
qed

text \<open>Just like an interval, a geodesic segment is compact, connected, path connected, bounded,
closed, nonempty, and proper.\<close>
lemma geodesic_segment_topology:
  assumes "geodesic_segment G"
  shows "compact G" "connected G" "path_connected G" "bounded G" "closed G" "G \<noteq> {}" "proper G"
proof -
  show "compact G"
    using assms geodesic_segment_homeo_interval homeomorphic_compactness
    unfolding geodesic_segment_def by force
  show "path_connected G"
    using assms is_interval_path_connected geodesic_segment_homeo_interval homeomorphic_path_connectedness
    unfolding geodesic_segment_def
    by (metis is_interval_cc)
  then show "connected G"
    using path_connected_imp_connected by auto
  show "bounded G"
    by (rule compact_imp_bounded, fact)
  show "closed G"
    by (rule compact_imp_closed, fact)
  show "G \<noteq> {}"
    using assms geodesic_segment_def geodesic_segment_endpoints(3) by auto
  show "proper G"
    using proper_of_compact \<open>compact G\<close> by auto
qed

lemma geodesic_segment_between_x_x [simp]:
  "geodesic_segment_between {x} x x"
  "geodesic_segment {x}"
  "geodesic_segment_between G x x \<longleftrightarrow> G = {x}"
proof -
  show *: "geodesic_segment_between {x} x x"
    unfolding geodesic_segment_between_def apply (rule exI[of _ "\<lambda>_. x"]) unfolding isometry_on_def by auto
  then show "geodesic_segment {x}" by auto
  show "geodesic_segment_between G x x \<longleftrightarrow> G = {x}"
    using geodesic_segment_dist_le geodesic_segment_endpoints(2) * by fastforce
qed

lemma geodesic_segment_disconnection:
  assumes "geodesic_segment_between G x y" "z \<in> G"
  shows "(connected (G - {z})) = (z = x \<or> z = y)"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain t where t: "t \<in> {0..dist x y}" "z = g t" using \<open>z \<in> G\<close> g(4) by auto
  have "({0..dist x y} - {t}) homeomorphic (G - {g t})"
  proof -
    have *: "isometry_on ({0..dist x y} - {t}) g"
      apply (rule isometry_on_subset[OF g(3)]) by auto
    have "({0..dist x y} - {t}) homeomorphic g`({0..dist x y} - {t})"
      by (rule isometry_on_homeomorphism(3)[OF *])
    moreover have "g`({0..dist x y} - {t}) = G - {g t}"
      unfolding g(4) using isometry_on_injective[OF g(3)] t by (auto simp add: inj_onD)
    ultimately show ?thesis by auto
  qed
  moreover have "connected({0..dist x y} - {t}) = (t = 0 \<or> t = dist x y)"
    using t(1) by (auto simp add: connected_iff_interval, fastforce)
  ultimately have "connected (G - {z}) = (t = 0 \<or> t = dist x y)"
    unfolding \<open>z = g t\<close>[symmetric]using homeomorphic_connectedness by blast
  moreover have "(t = 0 \<or> t = dist x y) = (z = x \<or> z = y)"
    using t g apply auto
    by (metis atLeastAtMost_iff isometry_on_inverse(2) order_refl zero_le_dist)+
  ultimately show ?thesis by auto
qed

lemma geodesic_segment_unique_endpoints:
  assumes "geodesic_segment_between G x y"
          "geodesic_segment_between G a b"
  shows "{x, y} = {a, b}"
by (metis geodesic_segment_disconnection assms(1) assms(2) doubleton_eq_iff geodesic_segment_endpoints(1) geodesic_segment_endpoints(2))

lemma geodesic_segment_subsegment:
  assumes "geodesic_segment G" "H \<subseteq> G" "compact H" "connected H" "H \<noteq> {}"
  shows "geodesic_segment H"
proof -
  obtain x y where "geodesic_segment_between G x y"
    using assms unfolding geodesic_segment_def by auto
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  define L where "L = (inv_into {0..dist x y} g)`H"
  have "L \<subseteq> {0..dist x y}"
    unfolding L_def using isometry_on_inverse[OF \<open>isometry_on {0..dist x y} g\<close>] assms(2) g(4) by auto
  have "isometry_on G (inv_into {0..dist x y} g)"
    using isometry_on_inverse[OF \<open>isometry_on {0..dist x y} g\<close>] g(4) by auto
  then have "isometry_on H (inv_into {0..dist x y} g)"
    using \<open>H \<subseteq> G\<close> isometry_on_subset by auto
  then have "H homeomorphic L" unfolding L_def using isometry_on_homeomorphism(3) by auto
  then have "compact L \<and> connected L"
    using assms homeomorphic_compactness homeomorphic_connectedness by blast
  then obtain a b where "L = {a..b}"
    using connected_compact_interval_1[of L] by auto
  have "a \<le> b" using \<open>H \<noteq> {}\<close> \<open>L = {a..b}\<close> unfolding L_def by auto
  then have "0 \<le> a" "b \<le> dist x y" using \<open>L \<subseteq> {0..dist x y}\<close> \<open>L = {a..b}\<close> by auto
  have *: "H = g`{a..b}"
    by (metis L_def \<open>L = {a..b}\<close> assms(2) g(4) image_inv_into_cancel)
  show "geodesic_segment H"
    unfolding * apply (rule geodesic_segmentI2[OF _ \<open>a \<le> b\<close>])
    apply (rule isometry_on_subset[OF g(3)]) using \<open>0 \<le> a\<close> \<open>b \<le> dist x y\<close> by auto
qed

text \<open>The image under an isometry of a geodesic segment is still obviously a geodesic segment.\<close>
lemma isometry_preserves_geodesic_segment_between:
  assumes "isometry_on X f"
          "G \<subseteq> X" "geodesic_segment_between G x y"
  shows "geodesic_segment_between (f`G) (f x) (f y)"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  then have *: "f`G = (f o g) `{0..dist x y}" "f x = (f o g) 0" "f y = (f o g) (dist x y)"
    by auto
  show ?thesis
    unfolding * apply (intro geodesic_segmentI2(1))
    unfolding comp_def apply (rule isometry_on_compose[of _ g])
    using g(3) g(4) assms by (auto intro: isometry_on_subset)
qed

text \<open>The sum of distances $d(w, x) + d(w, y)$ can be controlled using the distance from $w$
to a geodesic segment between $x$ and $y$.\<close>
lemma geodesic_segment_distance:
  assumes "geodesic_segment_between G x y"
  shows "dist w x + dist w y \<le> dist x y + 2 * infdist w G"
proof -
  have "\<exists>z \<in> G. infdist w G = dist w z"
    apply (rule infdist_proper_attained) using assms by (auto simp add: geodesic_segment_topology)
  then obtain z where z: "z \<in> G" "infdist w G = dist w z" by auto
  have "dist w x + dist w y \<le> (dist w z + dist z x) + (dist w z + dist z y)"
    by (intro mono_intros)
  also have "... = dist x z + dist z y + 2 * dist w z"
    by (auto simp add: dist_commute)
  also have "... = dist x y + 2 * infdist w G"
    using z(1) assms geodesic_segment_dist unfolding z(2) by auto
  finally show ?thesis by auto
qed

text \<open>If a point $y$ is on a geodesic segment between $x$ and its closest projection $p$ on a set $A$,
then $p$ is also a closest projection of $y$, and the closest projection set of $y$ is contained in
that of $x$.\<close>

lemma proj_set_geodesic_same_basepoint:
  assumes "p \<in> proj_set x A" "geodesic_segment_between G p x" "y \<in> G"
  shows "p \<in> proj_set y A"
proof (rule proj_setI)
  show "p \<in> A"
    using assms proj_setD by auto
  have *: "dist y p \<le> dist y q" if "q \<in> A" for q
  proof -
    have "dist p y + dist y x = dist p x"
      using assms geodesic_segment_dist by blast
    also have "... \<le> dist q x"
      using proj_set_dist_le[OF \<open>q \<in> A\<close> assms(1)] by (simp add: dist_commute)
    also have "... \<le> dist q y + dist y x"
      by (intro mono_intros)
    finally show ?thesis
      by (simp add: dist_commute)
  qed
  have "dist y p \<le> Inf (dist y ` A)"
    apply (rule cINF_greatest) using \<open>p \<in> A\<close> * by auto
  then show "dist y p \<le> infdist y A"
    unfolding infdist_def using \<open>p \<in> A\<close> by auto
qed

lemma proj_set_subset:
  assumes "p \<in> proj_set x A" "geodesic_segment_between G p x" "y \<in> G"
  shows "proj_set y A \<subseteq> proj_set x A"
proof -
  have "z \<in> proj_set x A" if "z \<in> proj_set y A" for z
  proof (rule proj_setI)
    show "z \<in> A" using that proj_setD by auto
    have "dist x z \<le> dist x y + dist y z"
      by (intro mono_intros)
    also have "... \<le> dist x y + dist y p"
      using proj_set_dist_le[OF proj_setD(1)[OF \<open>p \<in> proj_set x A\<close>] that] by auto
    also have "... = dist x p"
      using assms geodesic_segment_commute geodesic_segment_dist by blast
    also have "... = infdist x A"
      using proj_setD(2)[OF assms(1)] by simp
    finally show "dist x z \<le> infdist x A"
      by simp
  qed
  then show ?thesis by auto
qed

lemma proj_set_thickening:
  assumes "p \<in> proj_set x Z"
          "0 \<le> D"
          "D \<le> dist p x"
          "geodesic_segment_between G p x"
  shows "geodesic_segment_param G p D \<in> proj_set x (\<Union>z\<in>Z. cball z D)"
proof (rule proj_setI')
  have "dist p (geodesic_segment_param G p D) = D"
    using geodesic_segment_param(7)[OF assms(4), of 0 D]
    unfolding geodesic_segment_param(1)[OF assms(4)] using assms by simp
  then show "geodesic_segment_param G p D \<in> (\<Union>z\<in>Z. cball z D)"
    using proj_setD(1)[OF \<open>p \<in> proj_set x Z\<close>] by force
  show "dist x (geodesic_segment_param G p D) \<le> dist x y" if "y \<in> (\<Union>z\<in>Z. cball z D)" for y
  proof -
    obtain z where y: "y \<in> cball z D" "z \<in> Z" using \<open>y \<in> (\<Union>z\<in>Z. cball z D)\<close> by auto
    have "dist (geodesic_segment_param G p D) x + D = dist p x"
      using geodesic_segment_param(7)[OF assms(4), of D "dist p x"]
      unfolding geodesic_segment_param(2)[OF assms(4)] using assms by simp
    also have "... \<le> dist z x"
      using proj_setD(2)[OF \<open>p \<in> proj_set x Z\<close>] infdist_le[OF \<open>z \<in> Z\<close>, of x] by (simp add: dist_commute)
    also have "... \<le> dist z y + dist y x"
      by (intro mono_intros)
    also have "... \<le> D + dist y x"
      using y by simp
    finally show ?thesis by (simp add: dist_commute)
  qed
qed

lemma proj_set_thickening':
  assumes "p \<in> proj_set x Z"
          "0 \<le> D"
          "D \<le> E"
          "E \<le> dist p x"
          "geodesic_segment_between G p x"
  shows "geodesic_segment_param G p D \<in> proj_set (geodesic_segment_param G p E) (\<Union>z\<in>Z. cball z D)"
proof -
  define H where "H = geodesic_subsegment G p D (dist p x)"
  have H1: "geodesic_segment_between H (geodesic_segment_param G p D) x"
    apply (subst geodesic_segment_param(2)[OF \<open>geodesic_segment_between G p x\<close>, symmetric])
    unfolding H_def apply (rule geodesic_subsegment(2)) using assms by auto
  have H2: "geodesic_segment_param G p E \<in> H"
    unfolding H_def using assms geodesic_subsegment(1) by force
  have "geodesic_segment_param G p D \<in> proj_set x (\<Union>z\<in>Z. cball z D)"
    apply (rule proj_set_thickening) using assms by auto
  then show ?thesis
    by (rule proj_set_geodesic_same_basepoint[OF _ H1 H2])
qed

text \<open>It is often convenient to use \emph{one} geodesic between $x$ and $y$, even if it is not unique.
We introduce a notation for such a choice of a geodesic, denoted \verb+{x--S--y}+ for such a geodesic
that moreover remains in the set $S$. We also enforce
the condition \verb+{x--S--y} = {y--S--x}+. When there is no such geodesic, we simply take
\verb+{x--S--y} = {x, y}+ for definiteness. It would be even better to enforce that, if
$a$ is on \verb+{x--S--y}+, then \verb+{x--S--y}+ is the union of \verb+{x--S--a}+ and \verb+{a--S--y}+, but
I do not know if such a choice is always possible -- such a choice of geodesics is
called a geodesic bicombing.
We also write \verb+{x--y}+ for \verb+{x--UNIV--y}+.\<close>

definition some_geodesic_segment_between::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--_--_})")
  where "some_geodesic_segment_between = (SOME f. \<forall> x y S. f x S y = f y S x
    \<and> (if (\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S) then (geodesic_segment_between (f x S y) x y \<and> (f x S y \<subseteq> S))
        else f x S y = {x, y}))"

abbreviation some_geodesic_segment_between_UNIV::"'a::metric_space \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--_})")
  where "some_geodesic_segment_between_UNIV x y \<equiv> {x--UNIV--y}"

text \<open>We prove that there is such a choice of geodesics, compatible with direction reversal. What
we do is choose arbitrarily a geodesic between $x$ and $y$ if it exists, and then use the geodesic
between $\min(x, y)$ and $\max(x,y)$, for any total order on the space, to ensure that we get the
same result from $x$ to $y$ or from $y$ to $x$.\<close>

lemma some_geodesic_segment_between_exists:
  "\<exists>f. \<forall> x y S. f x S y = f y S x
    \<and> (if (\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S) then (geodesic_segment_between (f x S y) x y \<and> (f x S y \<subseteq> S))
        else f x S y = {x, y})"
proof -
  define g::"'a \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "g = (\<lambda>x S y. if (\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S) then (SOME G. geodesic_segment_between G x y \<and> G \<subseteq> S) else {x, y})"
  have g1: "geodesic_segment_between (g x S y) x y \<and> (g x S y \<subseteq> S)" if "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S" for x y S
    unfolding g_def using someI_ex[OF that] by auto
  have g2: "g x S y = {x, y}" if "\<not>(\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S)" for x y S
    unfolding g_def using that by auto
  obtain r::"'a rel" where r: "well_order_on UNIV r"
    using well_order_on by auto
  have A: "x = y" if "(x, y) \<in> r" "(y, x) \<in> r" for x y
    using r that unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def by auto
  have B: "(x, y) \<in> r \<or> (y, x) \<in> r" for x y
    using r unfolding well_order_on_def linear_order_on_def total_on_def partial_order_on_def preorder_on_def refl_on_def by force

  define f where "f = (\<lambda>x S y. if (x, y) \<in> r then g x S y else g y S x)"
  have "f x S y = f y S x" for x y S unfolding f_def using r A B by auto
  moreover have "geodesic_segment_between (f x S y) x y \<and> (f x S y \<subseteq> S)" if "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S" for x y S
    unfolding f_def using g1 geodesic_segment_commute that by smt
  moreover have "f x S y = {x, y}" if "\<not>(\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S)" for x y S
    unfolding f_def using g2 that geodesic_segment_commute doubleton_eq_iff by metis
  ultimately show ?thesis by metis
qed

lemma some_geodesic_commute:
  "{x--S--y} = {y--S--x}"
unfolding some_geodesic_segment_between_def by (auto simp add: someI_ex[OF some_geodesic_segment_between_exists])

lemma some_geodesic_segment_description:
  "(\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S) \<Longrightarrow> geodesic_segment_between {x--S--y} x y"
  "(\<not>(\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S)) \<Longrightarrow> {x--S--y} = {x, y}"
unfolding some_geodesic_segment_between_def by (simp add: someI_ex[OF some_geodesic_segment_between_exists])+

text \<open>Basic topological properties of our chosen set of geodesics.\<close>

lemma some_geodesic_compact [simp]:
  "compact {x--S--y}"
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S")
using some_geodesic_segment_description[of x y] geodesic_segment_topology[of "{x--S--y}"] geodesic_segment_def apply auto
  by blast

lemma some_geodesic_closed [simp]:
  "closed {x--S--y}"
by (rule compact_imp_closed[OF some_geodesic_compact[of x S y]])

lemma some_geodesic_bounded [simp]:
  "bounded {x--S--y}"
by (rule compact_imp_bounded[OF some_geodesic_compact[of x S y]])

lemma some_geodesic_endpoints [simp]:
  "x \<in> {x--S--y}" "y \<in> {x--S--y}" "{x--S--y} \<noteq> {}"
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S") using some_geodesic_segment_description[of x y S] apply auto
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S") using some_geodesic_segment_description[of x y S] apply auto
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S") using geodesic_segment_endpoints(3) by (auto, blast)

lemma some_geodesic_subsegment:
  assumes "H \<subseteq> {x--S--y}" "compact H" "connected H" "H \<noteq> {}"
  shows "geodesic_segment H"
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S")
using some_geodesic_segment_description[of x y] geodesic_segment_subsegment[OF _ assms] geodesic_segment_def apply auto[1]
using some_geodesic_segment_description[of x y] assms
by (metis connected_finite_iff_sing finite.emptyI finite.insertI finite_subset geodesic_segment_between_x_x(2))

lemma some_geodesic_in_subset:
  assumes "x \<in> S" "y \<in> S"
  shows "{x--S--y} \<subseteq> S"
apply (cases "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S")
unfolding some_geodesic_segment_between_def by (simp add: assms someI_ex[OF some_geodesic_segment_between_exists])+

lemma some_geodesic_same_endpoints [simp]:
  "{x--S--x} = {x}"
apply (cases "\<exists>G. geodesic_segment_between G x x \<and> G \<subseteq> S")
apply (meson geodesic_segment_between_x_x(3) some_geodesic_segment_description(1))
by (simp add: some_geodesic_segment_description(2))

subsection \<open>Geodesic subsets\<close>

text \<open>A subset is \emph{geodesic} if any two of its points can be joined by a geodesic segment.
We prove basic properties of such a subset in this paragraph -- notably connectedness. A basic
example is given by convex subsets of vector spaces, as closed segments are geodesic.\<close>

definition geodesic_subset::"('a::metric_space) set \<Rightarrow> bool"
  where "geodesic_subset S = (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S)"

lemma geodesic_subsetD:
  assumes "geodesic_subset S" "x \<in> S" "y \<in> S"
  shows "geodesic_segment_between {x--S--y} x y"
using assms some_geodesic_segment_description(1) unfolding geodesic_subset_def by blast

lemma geodesic_subsetI:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> \<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S"
  shows "geodesic_subset S"
using assms unfolding geodesic_subset_def by auto

lemma geodesic_subset_empty:
  "geodesic_subset {}"
using geodesic_subsetI by auto

lemma geodesic_subset_singleton:
  "geodesic_subset {x}"
by (auto intro!: geodesic_subsetI geodesic_segment_between_x_x(1))

lemma geodesic_subset_path_connected:
  assumes "geodesic_subset S"
  shows "path_connected S"
proof -
  have "\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y" if "x \<in> S" "y \<in> S" for x y
  proof -
    define G where "G = {x--S--y}"
    have *: "geodesic_segment_between G x y" "G \<subseteq> S" "x \<in> G" "y \<in> G"
      using assms that by (auto simp add: G_def geodesic_subsetD some_geodesic_in_subset that(1) that(2))
    then have "path_connected G"
      using geodesic_segment_topology(3) unfolding geodesic_segment_def by auto
    then have "\<exists>g. path g \<and> path_image g \<subseteq> G \<and> pathstart g = x \<and> pathfinish g = y"
      using * unfolding path_connected_def by auto
    then show ?thesis using \<open>G \<subseteq> S\<close> by auto
  qed
  then show ?thesis
    unfolding path_connected_def by auto
qed

text \<open>To show that a segment in a normed vector space is geodesic, we will need to use its
length parametrization, which is given in the next lemma.\<close>

lemma closed_segment_as_isometric_image:
  "((\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))`{0..dist x y}) = closed_segment x y"
proof (auto simp add: closed_segment_def image_iff)
  fix t assume H: "0 \<le> t" "t \<le> dist x y"
  show "\<exists>u. x + (t / dist x y) *\<^sub>R (y - x) = (1 - u) *\<^sub>R x + u *\<^sub>R y \<and> 0 \<le> u \<and> u \<le> 1"
    apply (rule exI[of _ "t/dist x y"]) using H apply (auto simp add: algebra_simps divide_simps)
    by (metis add_diff_cancel_left' add_divide_distrib dist_not_less_zero dist_pos_lt divide_eq_1_iff linordered_field_class.sign_simps(29) scaleR_left.add scaleR_one)
next
  fix u::real assume H: "0 \<le> u" "u \<le> 1"
  show "\<exists>t\<in>{0..dist x y}. (1 - u) *\<^sub>R x + u *\<^sub>R y = x + (t / dist x y) *\<^sub>R (y - x)"
    apply (rule bexI[of _ "u * dist x y"])
    using H by (auto simp add: algebra_simps mult_left_le_one_le)
qed

proposition closed_segment_is_geodesic:
  fixes x y::"'a::real_normed_vector"
  shows "isometry_on {0..dist x y} (\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))"
        "geodesic_segment_between (closed_segment x y) x y"
        "geodesic_segment (closed_segment x y)"
proof -
  show *: "isometry_on {0..dist x y} (\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))"
    unfolding isometry_on_def dist_norm
    apply (cases "x = y")
    by (auto simp add: scaleR_diff_left[symmetric] diff_divide_distrib[symmetric] norm_minus_commute)
  show "geodesic_segment_between (closed_segment x y) x y"
    unfolding closed_segment_as_isometric_image[symmetric]
    apply (rule geodesic_segment_betweenI[OF _ _ *]) by auto
  then show "geodesic_segment (closed_segment x y)"
    by auto
qed

text \<open>We deduce that a convex set is geodesic.\<close>

proposition convex_is_geodesic:
  assumes "convex (S::'a::real_normed_vector set)"
  shows "geodesic_subset S"
proof (rule geodesic_subsetI)
  fix x y assume H: "x \<in> S" "y \<in> S"
  show "\<exists>G. geodesic_segment_between G x y \<and> G \<subseteq> S"
    apply (rule exI[of _ "closed_segment x y"])
    apply (auto simp add: closed_segment_is_geodesic)
    using H assms convex_contains_segment by blast
qed


subsection \<open>Geodesic spaces\<close>

text \<open>In this subsection, we define geodesic spaces (metric spaces in which there is a geodesic
segment joining any pair of points). We specialize the previous statements on geodesic segments to
these situations.\<close>

class geodesic_space = metric_space +
  assumes geodesic: "geodesic_subset (UNIV::('a::metric_space) set)"

text \<open>The simplest example of a geodesic space is a real normed vector space. Significant examples
also include graphs (with the graph distance), Riemannian manifolds, and $CAT(\kappa)$ spaces.\<close>

instance real_normed_vector \<subseteq> geodesic_space
by (standard, simp add: convex_is_geodesic)

lemma (in geodesic_space) some_geodesic_is_geodesic_segment [simp]:
  "geodesic_segment_between {x--y} x (y::'a)"
  "geodesic_segment {x--y}"
using some_geodesic_segment_description(1)[of x y] geodesic_subsetD[OF geodesic] by (auto, blast)

lemma (in geodesic_space) some_geodesic_connected [simp]:
  "connected {x--y}" "path_connected {x--y}"
by (auto intro!: geodesic_segment_topology)

text \<open>In geodesic spaces, we restate as simp rules all properties of the geodesic segment
parametrizations.\<close>

lemma (in geodesic_space) geodesic_segment_param_in_geodesic_spaces [simp]:
  "geodesic_segment_param {x--y} x 0 = x"
  "geodesic_segment_param {x--y} x (dist x y) = y"
  "t \<in> {0..dist x y} \<Longrightarrow> geodesic_segment_param {x--y} x t \<in> {x--y}"
  "isometry_on {0..dist x y} (geodesic_segment_param {x--y} x)"
  "(geodesic_segment_param {x--y} x)`{0..dist x y} = {x--y}"
  "t \<in> {0..dist x y} \<Longrightarrow> dist x (geodesic_segment_param {x--y} x t) = t"
  "s \<in> {0..dist x y} \<Longrightarrow> t \<in> {0..dist x y} \<Longrightarrow> dist (geodesic_segment_param {x--y} x s) (geodesic_segment_param {x--y} x t) = abs(s-t)"
  "z \<in> {x--y} \<Longrightarrow> z = geodesic_segment_param {x--y} x (dist x z)"
using geodesic_segment_param[OF some_geodesic_is_geodesic_segment(1)[of x y]] by auto


subsection \<open>Uniquely geodesic spaces\<close>

text \<open>In this subsection, we define uniquely geodesic spaces, i.e., geodesic spaces in which,
additionally, there is a unique geodesic between any pair of points.\<close>

class uniquely_geodesic_space = geodesic_space +
  assumes uniquely_geodesic: "\<And>x y G H. geodesic_segment_between G x y \<Longrightarrow> geodesic_segment_between H x y \<Longrightarrow> G = H"

text \<open>To prove that a geodesic space is uniquely geodesic, it suffices to show that there is no loop,
i.e., if two geodesic segments intersect only at their endpoints, then they coincide.

Indeed, assume this holds, and consider two geodesics with the same endpoints. If they differ at
some time $t$, then consider the last time $a$ before $t$ where they coincide, and the first time
$b$ after $t$ where they coincide. Then the restrictions of the two geodesics to $[a,b]$ give
a loop, and a contradiction.\<close>

lemma (in geodesic_space) uniquely_geodesic_spaceI:
  assumes "\<And>G H x (y::'a). geodesic_segment_between G x y \<Longrightarrow> geodesic_segment_between H x y \<Longrightarrow> G \<inter> H = {x, y} \<Longrightarrow> x = y"
          "geodesic_segment_between G x y" "geodesic_segment_between H x (y::'a)"
  shows "G = H"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
  obtain h where h: "h 0 = x" "h (dist x y) = y" "isometry_on {0..dist x y} h" "H = h`{0..dist x y}"
    by (meson \<open>geodesic_segment_between H x y\<close> geodesic_segment_between_def)
  have "g t = h t" if "t \<in> {0..dist x y}" for t
  proof (rule ccontr)
    assume "g t \<noteq> h t"
    define Z where "Z = {s \<in> {0..dist x y}. g s = h s}"
    have "0 \<in> Z" "dist x y \<in> Z" unfolding Z_def using g h by auto
    have "t \<notin> Z" unfolding Z_def using \<open>g t \<noteq> h t\<close> by auto
    have [simp]: "closed Z"
    proof -
      have *: "Z = (\<lambda>s. dist (g s) (h s))-`{0} \<inter> {0..dist x y}"
        unfolding Z_def by auto
      show ?thesis
        unfolding * apply (rule closed_vimage_Int)
        using isometry_on_continuous[OF g(3)] isometry_on_continuous[OF h(3)] continuous_on_dist by auto
    qed
    define a where "a = Sup (Z \<inter> {0..t})"
    have a: "a \<in> Z \<inter> {0..t}"
      unfolding a_def apply (rule closed_contains_Sup, auto)
      using \<open>0 \<in> Z\<close> that by auto
    then have "h a = g a" unfolding Z_def by auto
    define b where "b = Inf (Z \<inter> {t..dist x y})"
    have b: "b \<in> Z \<inter> {t..dist x y}"
      unfolding b_def apply (rule closed_contains_Inf, auto)
      using \<open>dist x y \<in> Z\<close> that by auto
    then have "h b = g b" unfolding Z_def by auto
    have notZ: "s \<notin> Z" if "s \<in> {a<..<b}" for s
    proof (rule ccontr, auto, cases "s \<le> t")
      case True
      assume "s \<in> Z"
      then have *: "s \<in> Z \<inter> {0..t}" using that a True by auto
      have "s \<le> a" unfolding a_def apply (rule cSup_upper) using * by auto
      then show False using that by auto
    next
      case False
      assume "s \<in> Z"
      then have *: "s \<in> Z \<inter> {t..dist x y}" using that b False by auto
      have "s \<ge> b" unfolding b_def apply (rule cInf_lower) using * by auto
      then show False using that by auto
    qed
    have "t \<in> {a<..<b}" using a b \<open>t \<notin> Z\<close> less_eq_real_def by auto
    then have "a \<le> b" by auto
    then have "dist (h a) (h b) = b-a"
      using isometry_onD[OF h(3), of a b] a b that unfolding dist_real_def by auto
    then have "dist (h a) (h b) > 0" using \<open>t \<in> {a<..<b}\<close> by auto
    then have "h a \<noteq> h b" by auto

    define G2 where "G2 = g`{a..b}"
    define H2 where "H2 = h`{a..b}"
    have "G2 \<inter> H2 \<subseteq> {h a, h b}"
    proof
      fix z assume z: "z \<in> G2 \<inter> H2"
      obtain sg where sg: "z = g sg" "sg \<in> {a..b}" using z unfolding G2_def by auto
      obtain sh where sh: "z = h sh" "sh \<in> {a..b}" using z unfolding H2_def by auto
      have "sg = dist x z"
        using isometry_onD[OF g(3), of 0 sg] a b sg(2) unfolding sg(1) g(1)[symmetric] dist_real_def by auto
      moreover have "sh = dist x z"
        using isometry_onD[OF h(3), of 0 sh] a b sh(2) unfolding sh(1) h(1)[symmetric] dist_real_def by auto
      ultimately have "sg = sh" by auto
      then have "sh \<in> Z" using sg(1) sh(1) a b sh(2) unfolding Z_def by auto
      then have "sh \<in> {a, b}" using notZ sh(2)
        by (metis IntD2 atLeastAtMost_iff atLeastAtMost_singleton greaterThanLessThan_iff inf_bot_left insertI2 insert_inter_insert not_le)
      then show "z \<in> {h a, h b}" using sh(1) by auto
    qed
    then have "G2 \<inter> H2 = {h a, h b}"
      using \<open>h a = g a\<close> \<open>h b = g b\<close> \<open>a \<le> b\<close> unfolding H2_def G2_def apply auto
      unfolding \<open>h a = g a\<close>[symmetric] \<open>h b = g b\<close>[symmetric] by auto
    moreover have "geodesic_segment_between G2 (h a) (h b)"
      unfolding G2_def \<open>h a = g a\<close> \<open>h b = g b\<close>
      apply (rule geodesic_segmentI2) apply (rule isometry_on_subset[OF g(3)])
      using a b that by auto
    moreover have "geodesic_segment_between H2 (h a) (h b)"
      unfolding H2_def apply (rule geodesic_segmentI2) apply (rule isometry_on_subset[OF h(3)])
      using a b that by auto
    ultimately have "h a = h b" using assms(1) by auto
    then show False using \<open>h a \<noteq> h b\<close> by simp
  qed
  then show "G = H" using g(4) h(4) by (simp add: image_def)
qed

context uniquely_geodesic_space
begin

lemma geodesic_segment_unique:
  "geodesic_segment_between G x y = (G = {x--(y::'a)})"
using uniquely_geodesic[of _ x y] by (meson some_geodesic_is_geodesic_segment)

lemma geodesic_segment_dist':
  assumes "dist x z = dist x y + dist y z"
  shows "y \<in> {x--z}" "{x--z} = {x--y} \<union> {y--z}"
proof -
  have "geodesic_segment_between ({x--y} \<union> {y--z}) x z"
    using geodesic_segment_union[OF assms] by auto
  then show "{x--z} = {x--y} \<union> {y--z}"
    using geodesic_segment_unique by auto
  then show "y \<in> {x--z}" by auto
qed

lemma geodesic_segment_expression:
  "{x--z} = {y. dist x z = dist x y + dist y z}"
using geodesic_segment_dist'(1) geodesic_segment_dist[OF some_geodesic_is_geodesic_segment(1)] by auto

lemma geodesic_segment_split:
  assumes "(y::'a) \<in> {x--z}"
  shows "{x--z} = {x--y} \<union> {y--z}"
        "{x--y} \<inter> {y--z} = {y}"
apply (metis assms geodesic_segment_dist geodesic_segment_dist'(2) some_geodesic_is_geodesic_segment(1))
apply (rule geodesic_segment_union(2)[of x z], auto simp add: assms)
using assms geodesic_segment_expression by blast

lemma geodesic_segment_subparam':
  assumes "y \<in> {x--z}" "t \<in> {0..dist x y}"
  shows "geodesic_segment_param {x--z} x t = geodesic_segment_param {x--y} x t"
apply (rule geodesic_segment_subparam[of _ _ z _ y]) using assms apply auto
using geodesic_segment_split(1)[OF assms(1)] by auto

end (*of context uniquely_geodesic_space*)


subsection \<open>A complete metric space with middles is geodesic.\<close>

text \<open>A complete space in which every pair of points has a middle (i.e., a point $m$ which
is half distance of $x$ and $y$) is geodesic: to construct a geodesic between $x_0$
and $y_0$, first choose a middle $m$, then middles of the pairs $(x_0,m)$ and $(m, y_0)$, and so
on. This will define the geodesic on dyadic points (and this is indeed an isometry on these dyadic
points. Then, extend it by uniform continuity to the whole segment $[0, dist x0 y0]$.

The formal proof will be done in a locale where $x_0$ and $y_0$ are fixed, for notational simplicity.
We define inductively the sequence of middles, in a function \verb+geod+ of two natural variables:
$geod n m$ corresponds to the image of the dyadic point $m/2^n$. It is defined inductively, by
$geod (n+1) (2m) = geod n m$, and $geod (n+1) (2m+1)$ is a middle of $geod n m$ and $geod n (m+1)$.
This is not a completely classical inductive definition, so one has to use \verb+function+ to define
it. Then, one checks inductively that it has all the properties we want, and use it to define the
geodesic segment on dyadic points. We will not use a canonical
representative for a dyadic point, but any representative (i.e., numerator and denominator
will not have to be coprime) -- this will not create problems as $geod$ does not depend on the choice
of the representative, by construction.\<close>

locale complete_space_with_middle =
  fixes x0 y0::"'a::complete_space"
  assumes middles: "\<And>x y::'a. \<exists>z. dist x z = (dist x y)/2 \<and> dist z y = (dist x y)/2"
begin

definition middle::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "middle x y = (SOME z. dist x z = (dist x y)/2 \<and> dist z y = (dist x y)/2)"

lemma middle:
  "dist x (middle x y) = (dist x y)/2"
  "dist (middle x y) y = (dist x y)/2"
unfolding middle_def using middles[of x y] by (metis (mono_tags, lifting) someI_ex)+

function geod::"nat \<Rightarrow> nat \<Rightarrow> 'a" where
 "geod 0 0 = x0"
|"geod 0 (Suc m) = y0"
|"geod (Suc n) (2 * m) = geod n m"
|"geod (Suc n) (Suc (2*m)) = middle (geod n m) (geod n (Suc m))"
apply (auto simp add: double_not_eq_Suc_double)
by (metis One_nat_def dvd_mult_div_cancel list_decode.cases odd_Suc_minus_one odd_two_times_div_two_nat)
termination by lexicographic_order

text \<open>By induction, the distance between successive points is $D/2^n$.\<close>

lemma geod_distance_successor:
  "\<forall>a < 2^n. dist (geod n a) (geod n (Suc a)) = dist x0 y0 / 2^n"
proof (induction n)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case
  proof (auto)
    fix a::nat assume a: "a < 2 * 2^n"
    obtain m where m: "a = 2 * m \<or> a = Suc (2 * m)" by (metis geod.elims)
    then have "m < 2^n" using a by auto
    consider "a = 2 * m" | "a = Suc(2*m)" using m by auto
    then show "dist (geod (Suc n) a) (geod (Suc n) (Suc a)) = dist x0 y0 / (2 * 2 ^ n)"
    proof (cases)
      case 1
      show ?thesis
        unfolding 1 apply auto
        unfolding middle using Suc.IH \<open>m < 2^n\<close> by auto
    next
      case 2
      have *: "Suc (Suc (2 * m)) = 2 * (Suc m)" by auto
      show ?thesis
        unfolding 2 apply auto
        unfolding * geod.simps(3) middle using Suc.IH \<open>m < 2^n\<close> by auto
    qed
  qed
qed

lemma geod_mult:
  "geod n a = geod (n + k) (a * 2^k)"
apply (induction k, auto) using geod.simps(3) by (metis mult.left_commute)

lemma geod_0:
  "geod n 0 = x0"
by (induction n, auto, metis geod.simps(3) semiring_normalization_rules(10))

lemma geod_end:
  "geod n (2^n) = y0"
by (induction n, auto)

text \<open>By the triangular inequality, the distance between points separated by $(b-a)/2^n$ is at
most $D * (b-a)/2^n$.\<close>

lemma geod_upper:
  assumes "a \<le> b" "b \<le> 2^n"
  shows "dist (geod n a) (geod n b) \<le> (b-a) * dist x0 y0 / 2^n"
proof -
  have *: "a+k > 2^n \<or> dist (geod n a) (geod n (a+k)) \<le> k * dist x0 y0 / 2^n" for k
  proof (induction k)
    case 0 then show ?case by auto
  next
    case (Suc k)
    show ?case
    proof (cases "2 ^ n < a + Suc k")
      case True then show ?thesis by auto
    next
      case False
      then have *: "a + k < 2 ^ n" by auto
      have "dist (geod n a) (geod n (a + Suc k)) \<le> dist (geod n a) (geod n (a+k)) + dist (geod n (a+k)) (geod n (a+Suc k))"
        using dist_triangle by auto
      also have "... \<le> k * dist x0 y0 / 2^n + dist x0 y0 / 2^n"
        using Suc.IH * geod_distance_successor by auto
      finally show ?thesis
        by (simp add: add_divide_distrib distrib_left mult.commute)
    qed
  qed
  show ?thesis using *[of "b-a"] assms by (simp add: of_nat_diff)
qed

text \<open>In fact, the distance is exactly $D * (b-a)/2^n$, otherwise the extremities of the interval
would be closer than $D$, a contradiction.\<close>

lemma geod_dist:
  assumes "a \<le> b" "b \<le> 2^n"
  shows "dist (geod n a) (geod n b) = (b-a) * dist x0 y0 / 2^n"
proof -
  have "dist (geod n a) (geod n b) \<le> (real b-a) * dist x0 y0 / 2^n"
    using geod_upper[of a b n] assms by auto
  moreover have "\<not> (dist (geod n a) (geod n b) < (real b-a) * dist x0 y0 / 2^n)"
  proof (rule ccontr, simp)
    assume *: "dist (geod n a) (geod n b) < (real b-a) * dist x0 y0 / 2^n"
    have "dist x0 y0 = dist (geod n 0) (geod n (2^n))"
      using geod_0 geod_end by auto
    also have "... \<le> dist (geod n 0) (geod n a) + dist (geod n a) (geod n b) + dist (geod n b) (geod n (2^n))"
      using dist_triangle4 by auto
    also have "... < a * dist x0 y0 / 2^n + (real b-a) * dist x0 y0 / 2^n + (2^n - real b) * dist x0 y0 / 2^n"
      using * assms geod_upper[of 0 a n] geod_upper[of b "2^n" n] by (auto intro: mono_intros)
    also have "... = dist x0 y0"
      using assms by (auto simp add: algebra_simps divide_simps)
    finally show "False" by auto
  qed
  ultimately show ?thesis by auto
qed

text \<open>We deduce the same statement but for points that are not on the same level, by putting
them on a common multiple level.\<close>

lemma geod_dist2:
  assumes "a \<le> 2^n" "b \<le> 2^p" "a/2^n \<le> b / 2^p"
  shows "dist (geod n a) (geod p b) = (b/2^p - a/2^n) * dist x0 y0"
proof -
  define r where "r = max n p"
  define ar where "ar = a * 2^(r - n)"
  have a: "ar / 2^r = a / 2^n"
    unfolding ar_def r_def by (auto simp add: divide_simps semiring_normalization_rules(26))
  have A: "geod r ar = geod n a"
    unfolding ar_def r_def using geod_mult[of n a "max n p - n"] by auto
  define br where "br = b * 2^(r - p)"
  have b: "br / 2^r = b / 2^p"
    unfolding br_def r_def by (auto simp add: divide_simps semiring_normalization_rules(26))
  have B: "geod r br = geod p b"
    unfolding br_def r_def using geod_mult[of p b "max n p - p"] by auto

  have "dist (geod n a) (geod p b) = dist (geod r ar) (geod r br)"
    using A B by auto
  also have "... = (real br - ar) * dist x0 y0 / 2 ^r"
    apply (rule geod_dist)
    using \<open>a/2^n \<le> b / 2^p\<close> unfolding a[symmetric] b[symmetric] apply (auto simp add: divide_simps)
    using \<open>b \<le> 2^p\<close> b apply (auto simp add: divide_simps)
    by (metis br_def le_add_diff_inverse2 max.cobounded2 mult.commute mult_le_mono2 r_def semiring_normalization_rules(26))
  also have "... = (real br / 2^r - real ar / 2^r) * dist x0 y0"
    by (auto simp add: algebra_simps divide_simps)
  finally show ?thesis using a b by auto
qed

text \<open>Same thing but without a priori ordering of the points.\<close>

lemma geod_dist3:
  assumes "a \<le> 2^n" "b \<le> 2^p"
  shows "dist (geod n a) (geod p b) = abs(b/2^p - a/2^n) * dist x0 y0"
apply (cases "a /2^n \<le> b/2^p", auto)
apply (rule geod_dist2[OF assms], auto)
apply (subst dist_commute, rule geod_dist2[OF assms(2) assms(1)], auto)
done

text \<open>Finally, we define a geodesic by extending what we have already defined on dyadic points,
thanks to the result of isometric extension of isometries taking their values
in complete spaces.\<close>

lemma geod:
  shows "\<exists>g. isometry_on {0..dist x0 y0} g \<and> g 0 = x0 \<and> g (dist x0 y0) = y0"
proof (cases "x0 = y0")
  case True
  show ?thesis apply (rule exI[of _ "\<lambda>_. x0"]) unfolding isometry_on_def using True by auto
next
  case False
  define A where "A = {(real k/2^n) * dist x0 y0 |k n. k \<le> 2^n}"
  have "{0..dist x0 y0} \<subseteq> closure A"
  proof (auto simp add: closure_approachable dist_real_def)
    fix t::real assume t: "0 \<le> t" "t \<le> dist x0 y0"
    fix e:: real assume "e > 0"
    then obtain n::nat where n: "dist x0 y0/e < 2^n"
      using one_less_numeral_iff real_arch_pow semiring_norm(76) by blast
    define k where "k = floor (2^n * t/ dist x0 y0)"
    have "k \<le> 2^n * t/ dist x0 y0" unfolding k_def by auto
    also have "... \<le> 2^n" using t False by (auto simp add: algebra_simps divide_simps)
    finally have "k \<le> 2^n" by auto
    have "k \<ge> 0" using t False unfolding k_def by auto
    define l where "l = nat k"
    have "k = int l" "l \<le> 2^n" using \<open>k \<ge> 0\<close> \<open>k \<le> 2^n\<close> nat_le_iff unfolding l_def by auto

    have "abs (2^n * t/dist x0 y0 - k) \<le> 1" unfolding k_def by linarith
    then have "abs(t - k/2^n * dist x0 y0) \<le> dist x0 y0 / 2^n"
      by (auto simp add: algebra_simps divide_simps False)
    also have "... < e" using n \<open>e > 0\<close> by (auto simp add: algebra_simps divide_simps)
    finally have "abs(t - k/2^n * dist x0 y0) < e" by auto
    then have "abs(t - l/2^n * dist x0 y0) < e" using \<open>k = int l\<close> by auto
    moreover have "l/2^n * dist x0 y0 \<in> A" unfolding A_def using \<open>l \<le> 2^n\<close> by auto
    ultimately show "\<exists>u\<in>A. abs(u - t) < e" by force
  qed

  text \<open>For each dyadic point, we choose one representation of the form $K/2^N$, it is not important
  for us that it is the minimal one.\<close>
  define index where "index = (\<lambda>t. SOME i. t = real (fst i)/2^(snd i) * dist x0 y0 \<and> (fst i) \<le> 2^(snd i))"
  define K where "K = (\<lambda>t. fst (index t))"
  define N where "N = (\<lambda>t. snd (index t))"
  have t: "t = K t/ 2^(N t) * dist x0 y0 \<and> K t \<le> 2^(N t)" if "t \<in> A" for t
  proof -
    obtain n k::nat where "t = k/2^n * dist x0 y0" "k \<le> 2^n" using \<open>t\<in> A\<close> unfolding A_def by auto
    then have *: "\<exists>i. t = real (fst i)/2^(snd i) * dist x0 y0 \<and> (fst i) \<le> 2^(snd i)" by auto
    show ?thesis unfolding K_def N_def index_def using someI_ex[OF *] by auto
  qed

  text \<open>We can now define our function on dyadic points.\<close>
  define f where "f = (\<lambda>t. geod (N t) (K t))"
  have "0 \<in> A" unfolding A_def by auto
  have "f 0 = x0"
  proof -
    have "0 = K 0 /2^(N 0) * dist x0 y0" using t \<open>0 \<in> A\<close> by auto
    then have "K 0 = 0" using False by auto
    then show ?thesis unfolding f_def using geod_0 by auto
  qed
  have "dist x0 y0 = (real 1/2^0) * dist x0 y0" by auto
  then have "dist x0 y0 \<in> A" unfolding A_def by force
  have "f (dist x0 y0) = y0"
  proof -
    have "dist x0 y0 = K (dist x0 y0) / 2^(N (dist x0 y0)) * dist x0 y0"
      using t \<open>dist x0 y0 \<in> A\<close> by auto
    then have "K (dist x0 y0) = 2^(N(dist x0 y0))" using False by (auto simp add: divide_simps)
    then show ?thesis unfolding f_def using geod_end by auto
  qed
  text \<open>By construction, it is an isometry on dyadic points.\<close>
  have "isometry_on A f"
  proof (rule isometry_onI)
    fix s t assume inA: "s \<in> A" "t \<in> A"
    have "dist (f s) (f t) = abs (K t/2^(N t) - K s/2^(N s)) * dist x0 y0"
      unfolding f_def apply (rule geod_dist3) using t inA by auto
    also have "... = abs(K t/2^(N t) * dist x0 y0 - K s/2^(N s) * dist x0 y0)"
      by (auto simp add: abs_mult_pos left_diff_distrib)
    also have "... = abs(t - s)"
      using t inA by auto
    finally show "dist (f s) (f t) = dist s t" unfolding dist_real_def by auto
  qed
  text \<open>We can thus extend it to an isometry on the closure of dyadic points.
  It is the desired geodesic.\<close>
  then obtain g where g: "isometry_on (closure A) g" "\<And>t. t \<in> A \<Longrightarrow> g t = f t"
    using isometry_extend_closure by metis
  have "isometry_on {0..dist x0 y0} g"
    by (rule isometry_on_subset[OF \<open>isometry_on (closure A) g\<close> \<open>{0..dist x0 y0} \<subseteq> closure A\<close>])
  moreover have "g 0 = x0"
    using g(2)[OF \<open>0 \<in> A\<close>] \<open>f 0 = x0\<close> by simp
  moreover have "g (dist x0 y0) = y0"
    using g(2)[OF \<open>dist x0 y0 \<in> A\<close>] \<open>f (dist x0 y0) = y0\<close> by simp
  ultimately show ?thesis by auto
qed

end

text \<open>We can now complete the proof that a complete space with middles is in fact geodesic:
all the work has been done in the locale \verb+complete_space_with_middle+, in Lemma~\verb+geod+.\<close>

theorem complete_with_middles_imp_geodesic:
  assumes "\<And>x y::('a::complete_space). \<exists>m. dist x m = dist x y /2 \<and> dist m y = dist x y /2"
  shows "OFCLASS('a, geodesic_space_class)"
proof (standard, rule geodesic_subsetI)
  fix x0 y0::'a
  interpret complete_space_with_middle x0 y0
    apply standard using assms by auto
  have "\<exists>g. g 0 = x0 \<and> g (dist x0 y0) = y0 \<and> isometry_on {0..dist x0 y0} g"
    using geod by auto
  then show "\<exists>G. geodesic_segment_between G x0 y0 \<and> G \<subseteq> UNIV"
    unfolding geodesic_segment_between_def by auto
qed


section \<open>Quasi-isometries\<close>

text \<open>A $(\lambda, C)$ quasi-isometry is a function which behaves like an isometry, up to
an additive error $C$ and a multiplicative error $\lambda$. It can be very different from an
isometry on small scales (for instance, the function integer part is a quasi-isometry between
$\mathbb{R}$ and $\mathbb{Z}$), but on large scales it captures many important features of
isometries.

When the space is unbounded, one checks easily that $C \geq 0$ and $\lambda \geq 1$. As this
is the only case of interest (any two bounded sets are quasi-isometric), we incorporate
this requirement in the definition.\<close>

definition quasi_isometry_on::"real \<Rightarrow> real \<Rightarrow> ('a::metric_space) set \<Rightarrow> ('a \<Rightarrow> ('b::metric_space)) \<Rightarrow> bool"
  ("_ _ -quasi'_isometry'_on" [1000, 999])
  where "lambda C-quasi_isometry_on X f = ((lambda \<ge> 1) \<and> (C \<ge> 0) \<and>
    (\<forall>x \<in> X. \<forall>y \<in> X. (dist (f x) (f y) \<le> lambda * dist x y + C \<and> dist (f x) (f y) \<ge> (1/lambda) * dist x y - C)))"

abbreviation quasi_isometry :: "real \<Rightarrow> real \<Rightarrow> ('a::metric_space \<Rightarrow> 'b::metric_space) \<Rightarrow> bool"
  ("_ _ -quasi'_isometry" [1000, 999])
  where "quasi_isometry lambda C f \<equiv> lambda C-quasi_isometry_on UNIV f"

subsection \<open>Basic properties of quasi-isometries\<close>

lemma quasi_isometry_onD:
  assumes "lambda C-quasi_isometry_on X f"
  shows "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> lambda * dist x y + C"
        "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<ge> (1/lambda) * dist x y - C"
        "lambda \<ge> 1" "C \<ge> 0"
using assms unfolding quasi_isometry_on_def by auto

lemma quasi_isometry_onI [intro]:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> lambda * dist x y + C"
          "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<ge> (1/lambda) * dist x y - C"
          "lambda \<ge> 1" "C \<ge> 0"
  shows "lambda C-quasi_isometry_on X f"
using assms unfolding quasi_isometry_on_def by auto

lemma isometry_quasi_isometry_on:
  assumes "isometry_on X f"
  shows "1 0-quasi_isometry_on X f"
using assms unfolding isometry_on_def quasi_isometry_on_def by auto

lemma quasi_isometry_on_change_params:
  assumes "lambda C-quasi_isometry_on X f" "mu \<ge> lambda" "D \<ge> C"
  shows "mu D-quasi_isometry_on X f"
proof (rule quasi_isometry_onI)
  have P1: "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
  then show P2: "mu \<ge> 1" "D \<ge> 0" using assms by auto
  fix x y assume inX: "x \<in> X" "y \<in> X"
  have "dist (f x) (f y) \<le> lambda * dist x y + C"
    using quasi_isometry_onD[OF assms(1)] inX by auto
  also have "... \<le> mu * dist x y + D"
    using assms by (auto intro!: mono_intros)
  finally show "dist (f x) (f y) \<le> mu * dist x y + D" by simp
  have "dist (f x) (f y) \<ge> (1/lambda) * dist x y - C"
    using quasi_isometry_onD[OF assms(1)] inX by auto
  moreover have "(1/lambda) * dist x y + (- C) \<ge> (1/mu) * dist x y + (- D)"
    apply (intro mono_intros)
    using P1 P2 assms by (auto simp add: divide_simps)
  ultimately show "dist (f x) (f y) \<ge> (1/mu) * dist x y - D" by simp
qed

lemma quasi_isometry_on_subset:
  assumes "lambda C-quasi_isometry_on X f"
          "Y \<subseteq> X"
  shows "lambda C-quasi_isometry_on Y f"
using assms unfolding quasi_isometry_on_def by auto

lemma quasi_isometry_on_perturb:
  assumes "lambda C-quasi_isometry_on X f"
          "D \<ge> 0"
          "\<And>x. x \<in> X \<Longrightarrow> dist (f x) (g x) \<le> D"
  shows "lambda (C + 2 * D)-quasi_isometry_on X g"
proof (rule quasi_isometry_onI)
  show "lambda \<ge> 1" "C + 2 * D \<ge> 0" using \<open>D \<ge> 0\<close> quasi_isometry_onD[OF assms(1)] by auto
  fix x y assume *: "x \<in> X" "y \<in> X"
  have "dist (g x) (g y) \<le> dist (f x) (f y) + 2 * D"
    using assms(3)[OF *(1)] assms(3)[OF *(2)] dist_triangle4[of "g x" "g y" "f x" "f y"] by (simp add: dist_commute)
  then show "dist (g x) (g y) \<le> lambda * dist x y + (C + 2 * D)"
    using quasi_isometry_onD(1)[OF assms(1) *] by auto
  have "dist (g x) (g y) \<ge> dist (f x) (f y) - 2 * D"
    using assms(3)[OF *(1)] assms(3)[OF *(2)] dist_triangle4[of "f x" "f y" "g x" "g y"] by (simp add: dist_commute)
  then show "dist (g x) (g y) \<ge> (1/lambda) * dist x y - (C + 2 * D)"
    using quasi_isometry_onD(2)[OF assms(1) *] by auto
qed

lemma quasi_isometry_on_compose:
  assumes "lambda C-quasi_isometry_on X f"
          "mu D-quasi_isometry_on Y g"
          "f`X \<subseteq> Y"
  shows "(lambda * mu) (C * mu + D)-quasi_isometry_on X (g o f)"
proof (rule quasi_isometry_onI)
  have I: "lambda \<ge> 1" "C \<ge> 0" "mu \<ge> 1" "D \<ge> 0"
    using quasi_isometry_onD[OF assms(1)] quasi_isometry_onD[OF assms(2)] by auto
  then show "lambda * mu \<ge> 1" "C * mu + D \<ge> 0"
    by (auto, metis dual_order.order_iff_strict le_numeral_extra(2) mult_le_cancel_right1 order.strict_trans1)
  fix x y assume inX: "x \<in> X" "y \<in> X"
  then have inY: "f x \<in> Y" "f y \<in> Y" using \<open>f`X \<subseteq> Y\<close> by auto
  have "dist ((g o f) x) ((g o f) y) \<le> mu * dist (f x) (f y) + D"
    using quasi_isometry_onD(1)[OF assms(2) inY] by simp
  also have "... \<le> mu * (lambda * dist x y + C) + D"
    using \<open>mu \<ge> 1\<close> quasi_isometry_onD(1)[OF assms(1) inX] by auto
  finally show "dist ((g o f) x) ((g o f) y) \<le> (lambda * mu) * dist x y + (C * mu + D)"
    by (auto simp add: algebra_simps)

  have "(1/(lambda * mu)) * dist x y - (C * mu + D) \<le> (1/(lambda * mu)) * dist x y - (C/mu + D)"
    using \<open>mu \<ge> 1\<close> \<open>C \<ge> 0\<close> apply (auto, auto simp add: divide_simps)
    by (metis eq_iff less_eq_real_def mult.commute mult_eq_0_iff mult_le_cancel_right1 order.trans)
  also have "... = (1/mu) * ((1/lambda) * dist x y - C) - D"
    by (auto simp add: algebra_simps)
  also have "... \<le> (1/mu) * dist (f x) (f y) - D"
    using \<open>mu \<ge> 1\<close> quasi_isometry_onD(2)[OF assms(1) inX] by (auto simp add: divide_simps)
  also have "... \<le> dist ((g o f) x) ((g o f) y)"
    using quasi_isometry_onD(2)[OF assms(2) inY] by auto
  finally show "1 / (lambda * mu) * dist x y - (C * mu + D) \<le> dist ((g \<circ> f) x) ((g \<circ> f) y)"
    by auto
qed

lemma quasi_isometry_on_bounded:
  assumes "lambda C-quasi_isometry_on X f"
          "bounded X"
  shows "bounded (f`X)"
proof (cases "X = {}")
  case True
  then show ?thesis by auto
next
  case False
  obtain x where "x \<in> X" using False by auto
  obtain e where e: "\<And>z. z \<in> X \<Longrightarrow> dist x z \<le> e"
    using bounded_any_center assms(2) by metis
  have "dist (f x) y \<le> C + lambda * e" if "y \<in> f`X" for y
  proof -
    obtain z where *: "z \<in> X" "y = f z" using \<open>y \<in> f`X\<close> by auto
    have "dist (f x) y \<le> lambda * dist x z + C"
      unfolding \<open>y = f z\<close> using * quasi_isometry_onD(1)[OF assms(1) \<open>x \<in> X\<close> \<open>z \<in> X\<close>] by (auto simp add: add_mono)
    also have "... \<le> C + lambda * e" using e[OF \<open>z \<in> X\<close>] quasi_isometry_onD(3)[OF assms(1)] by auto
    finally show ?thesis by simp
  qed
  then show ?thesis unfolding bounded_def by auto
qed

lemma quasi_isometry_on_empty:
  assumes "C \<ge> 0" "lambda \<ge> 1"
  shows "lambda C-quasi_isometry_on {} f"
using assms unfolding quasi_isometry_on_def by auto

text \<open>Quasi-isometries change the distance to a set by at most $\lambda \cdot + C$, this follows
readily from the fact that this inequality holds pointwise.\<close>

lemma quasi_isometry_on_infdist:
  assumes "lambda C-quasi_isometry_on X f"
          "w \<in> X"
          "S \<subseteq> X"
  shows "infdist (f w) (f`S) \<le> lambda * infdist w S + C"
        "infdist (f w) (f`S) \<ge> (1/lambda) * infdist w S - C"
proof -
  have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
  show "infdist (f w) (f`S) \<le> lambda * infdist w S + C"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using \<open>C \<ge> 0\<close> unfolding infdist_def by auto
  next
    case False
    then have "(INF x\<in>S. dist (f w) (f x)) \<le> (INF x\<in>S. lambda * dist w x + C)"
      apply (rule cINF_superset_mono)
        apply (meson bdd_belowI2 zero_le_dist) using assms by (auto intro!: quasi_isometry_onD(1)[OF assms(1)])
    also have "... = (INF t\<in>(dist w)`S. lambda * t + C)"
      by (auto simp add: image_comp)
    also have "... = lambda * Inf ((dist w)`S) + C"
      apply (rule continuous_at_Inf_mono[symmetric])
      unfolding mono_def using \<open>lambda \<ge> 1\<close> False by (auto intro!: continuous_intros)
    finally show ?thesis unfolding infdist_def using False by (auto simp add: image_comp)
  qed
  show "1 / lambda * infdist w S - C \<le> infdist (f w) (f ` S)"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using \<open>C \<ge> 0\<close> unfolding infdist_def by auto
  next
    case False
    then have "(1/lambda) * infdist w S - C = (1/lambda) * Inf ((dist w)`S) - C"
      unfolding infdist_def by auto
    also have "... = (INF t\<in>(dist w)`S. (1/lambda) * t - C)"
      apply (rule continuous_at_Inf_mono)
      unfolding mono_def using \<open>lambda \<ge> 1\<close> False by (auto simp add: divide_simps intro!: continuous_intros)
    also have "... = (INF x\<in>S. (1/lambda) * dist w x - C)"
      by (auto simp add: image_comp)
    also have "... \<le> (INF x\<in>S. dist (f w) (f x))"
      apply (rule cINF_superset_mono[OF False]) apply (rule bdd_belowI2[of _ "-C"])
      using assms \<open>lambda \<ge> 1\<close> apply simp apply simp apply (rule quasi_isometry_onD(2)[OF assms(1)])
      using assms by auto
    finally show ?thesis unfolding infdist_def using False by (auto simp add: image_comp)
  qed
qed

subsection \<open>Quasi-isometric isomorphisms\<close>

text \<open>The notion of isomorphism for quasi-isometries is not that it should be a bijection, as it is
a coarse notion, but that it is a bijection up to a bounded displacement. For instance, the
inclusion of $\mathbb{Z}$ in $\mathbb{R}$ is a quasi-isometric isomorphism between these spaces,
whose (quasi)-inverse (which is non-unique) is given by the function integer part. This is
formalized in the next definition.\<close>

definition quasi_isometry_between::"real \<Rightarrow> real \<Rightarrow> ('a::metric_space) set \<Rightarrow> ('b::metric_space) set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  ("_ _ -quasi'_isometry'_between" [1000, 999])
  where "lambda C-quasi_isometry_between X Y f = ((lambda C-quasi_isometry_on X f) \<and> (f`X \<subseteq> Y) \<and> (\<forall>y\<in>Y. \<exists>x\<in>X. dist (f x) y \<le> C))"

definition quasi_isometric::"('a::metric_space) set \<Rightarrow> ('b::metric_space) set \<Rightarrow> bool"
  where "quasi_isometric X Y = (\<exists>lambda C f. lambda C-quasi_isometry_between X Y f)"

lemma quasi_isometry_betweenD:
  assumes "lambda C-quasi_isometry_between X Y f"
  shows "lambda C-quasi_isometry_on X f"
        "f`X \<subseteq> Y"
        "\<And>y. y \<in> Y \<Longrightarrow> \<exists>x\<in>X. dist (f x) y \<le> C"
        "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> lambda * dist x y + C"
        "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<ge> (1/lambda) * dist x y - C"
        "lambda \<ge> 1" "C \<ge> 0"
using assms unfolding quasi_isometry_between_def quasi_isometry_on_def by auto

lemma quasi_isometry_betweenI:
  assumes "lambda C-quasi_isometry_on X f"
          "f`X \<subseteq> Y"
          "\<And>y. y \<in> Y \<Longrightarrow> \<exists>x\<in>X. dist (f x) y \<le> C"
  shows "lambda C-quasi_isometry_between X Y f"
using assms unfolding quasi_isometry_between_def by auto

lemma quasi_isometry_on_between:
  assumes "lambda C-quasi_isometry_on X f"
  shows "lambda C-quasi_isometry_between X (f`X) f"
using assms unfolding quasi_isometry_between_def quasi_isometry_on_def by force

lemma quasi_isometry_between_change_params:
  assumes "lambda C-quasi_isometry_between X Y f" "mu \<ge> lambda" "D \<ge> C"
  shows "mu D-quasi_isometry_between X Y f"
proof (rule quasi_isometry_betweenI)
  show "mu D-quasi_isometry_on X f"
    by (rule quasi_isometry_on_change_params[OF quasi_isometry_betweenD(1)[OF assms(1)] assms(2) assms(3)])
  show "f`X \<subseteq> Y" using quasi_isometry_betweenD[OF assms(1)] by auto
  fix y assume "y \<in> Y"
  show "\<exists>x\<in>X. dist (f x) y \<le> D" using quasi_isometry_betweenD(3)[OF assms(1) \<open>y \<in> Y\<close>] \<open>D \<ge> C\<close> by force
qed

lemma quasi_isometry_subset:
  assumes "X \<subseteq> Y" "\<And>y. y \<in> Y \<Longrightarrow> \<exists>x\<in>X. dist x y \<le> C" "C \<ge> 0"
  shows "1 C-quasi_isometry_between X Y (\<lambda>x. x)"
unfolding quasi_isometry_between_def using assms by auto

lemma isometry_quasi_isometry_between:
  assumes "isometry f"
  shows "1 0-quasi_isometry_between UNIV UNIV f"
using assms unfolding quasi_isometry_between_def quasi_isometry_on_def isometry_def isometry_on_def surj_def by (auto) metis

proposition quasi_isometry_inverse:
  assumes "lambda C-quasi_isometry_between X Y f"
  shows "\<exists>g. lambda (3 * C * lambda)-quasi_isometry_between Y X g
          \<and> (\<forall>x\<in>X. dist x (g (f x)) \<le> 3 * C * lambda)
          \<and> (\<forall>y\<in>Y. dist y (f (g y)) \<le> 3 * C * lambda)"
proof -
  define g where "g = (\<lambda>y. SOME x. x \<in> X \<and> dist (f x) y \<le> C)"
  have *: "g y \<in> X \<and> dist (f (g y)) y \<le> C" if "y \<in> Y" for y
    unfolding g_def using quasi_isometry_betweenD(3)[OF assms that] by (metis (no_types, lifting) someI_ex)
  have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_betweenD[OF assms] by auto

  have "C \<le> 3 * C * lambda" using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close>
    by (metis linordered_field_class.sign_simps(24) mult_le_cancel_left1 not_less numeral_le_iff one_eq_numeral_iff order.trans semiring_norm(68))
  then have A: "dist y (f (g y)) \<le> 3 * C * lambda" if "y \<in> Y" for y
    using *[OF that] by (simp add: dist_commute)

  have B: "dist x (g (f x)) \<le> 3 * C * lambda" if "x \<in> X" for x
  proof -
    have "f x \<in> Y" using that quasi_isometry_betweenD(2)[OF assms] by auto
    have "(1/lambda) * dist x (g (f x)) - C \<le> dist (f x) (f (g (f x)))"
      apply (rule quasi_isometry_betweenD(5)[OF assms]) using that *[OF \<open>f x \<in> Y\<close>] by auto
    also have "... \<le> C" using *[OF \<open>f x \<in> Y\<close>] by (simp add: dist_commute)
    finally have "dist x (g (f x)) \<le> 2 * C * lambda"
      using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by (simp add: divide_simps)
    also have "... \<le> 3 * C * lambda"
      using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by (simp add: divide_simps)
    finally show ?thesis by auto
  qed

  have "lambda (3 * C * lambda)-quasi_isometry_on Y g"
  proof (rule quasi_isometry_onI)
    show "lambda \<ge> 1" "3 * C * lambda \<ge> 0" using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
    fix y1 y2 assume inY: "y1 \<in> Y" "y2 \<in> Y"
    then have inX: "g y1 \<in> X" "g y2 \<in> X" using * by auto
    have "dist y1 y2 \<le> dist y1 (f (g y1)) + dist (f (g y1)) (f (g y2)) + dist (f (g y2)) y2"
      using dist_triangle4 by auto
    also have "... \<le> C + dist (f (g y1)) (f (g y2)) + C"
      using *[OF inY(1)] *[OF inY(2)] by (auto simp add: dist_commute intro: add_mono)
    also have "... \<le> C + (lambda * dist (g y1) (g y2) + C) + C"
      using quasi_isometry_betweenD(4)[OF assms inX] by (auto intro: add_mono)
    finally have "dist y1 y2 - 3 * C \<le> lambda * dist (g y1) (g y2)" by auto
    then have "dist (g y1) (g y2) \<ge> (1/lambda) * dist y1 y2 - 3 * C / lambda"
      using \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps mult.commute)
    moreover have "3 * C / lambda \<le> 3 * C * lambda"
      using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> apply (auto simp add: divide_simps mult_le_cancel_left1)
      by (metis dual_order.order_iff_strict less_1_mult mult.left_neutral)
    ultimately show "dist (g y1) (g y2) \<ge> (1/lambda) * dist y1 y2 - 3 * C * lambda"
      by auto

    have "(1/lambda) * dist (g y1) (g y2) - C \<le> dist (f (g y1)) (f (g y2))"
      using quasi_isometry_betweenD(5)[OF assms inX] by auto
    also have "... \<le> dist (f (g y1)) y1 + dist y1 y2 + dist y2 (f (g y2))"
      using dist_triangle4 by auto
    also have "... \<le> C + dist y1 y2 + C"
      using *[OF inY(1)] *[OF inY(2)] by (auto simp add: dist_commute intro: add_mono)
    finally show "dist (g y1) (g y2) \<le> lambda * dist y1 y2 + 3 * C * lambda"
      using \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  then have "lambda (3 * C * lambda)-quasi_isometry_between Y X g"
  proof (rule quasi_isometry_betweenI)
    show "g ` Y \<subseteq> X" using * by auto
    fix x assume "x \<in> X"
    have "f x \<in> Y" "dist (g (f x)) x \<le> 3 * C * lambda"
      using B[OF \<open>x \<in> X\<close>] quasi_isometry_betweenD(2)[OF assms] \<open>x \<in> X\<close> by (auto simp add: dist_commute)
    then show "\<exists>y\<in>Y. dist (g y) x \<le> 3 * C * lambda" by blast
  qed
  then show ?thesis using A B by blast
qed

proposition quasi_isometry_compose:
  assumes "lambda C-quasi_isometry_between X Y f"
          "mu D-quasi_isometry_between Y Z g"
  shows "(lambda * mu) (C * mu + 2 * D)-quasi_isometry_between X Z (g o f)"
proof (rule quasi_isometry_betweenI)
  have "(lambda * mu) (C * mu + D)-quasi_isometry_on X (g \<circ> f)"
    by (rule quasi_isometry_on_compose[OF quasi_isometry_betweenD(1)[OF assms(1)]
        quasi_isometry_betweenD(1)[OF assms(2)] quasi_isometry_betweenD(2)[OF assms(1)]])
  then show "(lambda * mu) (C * mu + 2 * D)-quasi_isometry_on X (g \<circ> f)"
    apply (rule quasi_isometry_on_change_params) using quasi_isometry_betweenD(7)[OF assms(2)] by auto

  show "(g \<circ> f) ` X \<subseteq> Z"
    using quasi_isometry_betweenD(2)[OF assms(1)] quasi_isometry_betweenD(2)[OF assms(2)]
    by auto
  fix z assume "z \<in> Z"
  obtain y where y: "y \<in> Y" "dist (g y) z \<le> D"
    using quasi_isometry_betweenD(3)[OF assms(2) \<open>z \<in> Z\<close>] by auto
  obtain x where x: "x \<in> X" "dist (f x) y \<le> C"
    using quasi_isometry_betweenD(3)[OF assms(1) \<open>y \<in> Y\<close>] by auto
  have "dist ((g o f) x) z \<le> dist (g (f x)) (g y) + dist (g y) z"
    using dist_triangle by auto
  also have "... \<le> (mu * dist (f x) y + D) + D"
    apply (rule add_mono, rule quasi_isometry_betweenD(4)[OF assms(2)])
    using x y quasi_isometry_betweenD(2)[OF assms(1)] by auto
  also have "... \<le> C * mu + 2 * D"
    using x(2) quasi_isometry_betweenD(6)[OF assms(2)] by auto
  finally show "\<exists>x\<in>X. dist ((g \<circ> f) x) z \<le> C * mu + 2 * D"
    using x(1) by auto
qed

theorem quasi_isometric_equiv_rel:
  "quasi_isometric X X"
  "quasi_isometric X Y \<Longrightarrow> quasi_isometric Y Z \<Longrightarrow> quasi_isometric X Z"
  "quasi_isometric X Y \<Longrightarrow> quasi_isometric Y X"
proof -
  show "quasi_isometric X X"
    unfolding quasi_isometric_def using quasi_isometry_subset[of X X 0] by auto
  assume H: "quasi_isometric X Y"
  then show "quasi_isometric Y X"
    unfolding quasi_isometric_def using quasi_isometry_inverse by blast
  assume "quasi_isometric Y Z"
  then show "quasi_isometric X Z"
    using H unfolding quasi_isometric_def using quasi_isometry_compose by blast
qed

text \<open>Many interesting properties in geometric group theory are invariant under quasi-isometry.
We prove the most basic ones here.\<close>

lemma quasi_isometric_empty:
  assumes "X = {}" "quasi_isometric X Y"
  shows "Y = {}"
using assms unfolding quasi_isometric_def quasi_isometry_between_def quasi_isometry_on_def by blast

lemma quasi_isometric_bounded:
  assumes "bounded X" "quasi_isometric X Y"
  shows "bounded Y"
proof (cases "X = {}")
  case True
  show ?thesis using quasi_isometric_empty[OF True assms(2)] by auto
next
  case False
  obtain lambda C f where QI: "lambda C-quasi_isometry_between X Y f"
    using assms(2) unfolding quasi_isometric_def by auto
  obtain x where "x \<in> X" using False by auto
  obtain e where e: "\<And>z. z \<in> X \<Longrightarrow> dist x z \<le> e"
    using bounded_any_center assms(1) by metis
  have "dist (f x) y \<le> 2 * C + lambda * e" if "y \<in> Y" for y
  proof -
    obtain z where *: "z \<in> X" "dist (f z) y \<le> C"
      using quasi_isometry_betweenD(3)[OF QI \<open>y \<in> Y\<close>] by auto
    have "dist (f x) y \<le> dist (f x) (f z) + dist (f z) y" using dist_triangle by auto
    also have "... \<le> (lambda * dist x z + C) + C"
      using * quasi_isometry_betweenD(4)[OF QI \<open>x \<in> X\<close> \<open>z \<in> X\<close>] by (auto simp add: add_mono)
    also have "... \<le> 2 * C + lambda * e"
      using quasi_isometry_betweenD(6)[OF QI] e[OF \<open>z \<in> X\<close>] by (auto simp add: algebra_simps)
    finally show ?thesis by simp
  qed
  then show ?thesis unfolding bounded_def by auto
qed

lemma quasi_isometric_bounded_iff:
  assumes "bounded X" "X \<noteq> {}" "bounded Y" "Y \<noteq> {}"
  shows "quasi_isometric X Y"
proof -
  obtain x y where "x \<in> X" "y \<in> Y" using assms by auto
  obtain C where C: "\<And>z. z \<in> Y \<Longrightarrow> dist y z \<le> C"
    using \<open>bounded Y\<close> bounded_any_center by metis
  have "C \<ge> 0" using C[OF \<open>y \<in> Y\<close>] by auto
  obtain D where D: "\<And>z. z \<in> X \<Longrightarrow> dist x z \<le> D"
    using \<open>bounded X\<close> bounded_any_center by metis
  have "D \<ge> 0" using D[OF \<open>x \<in> X\<close>] by auto

  define f::"'a \<Rightarrow> 'b" where "f = (\<lambda>_. y)"
  have "1 (C + 2 * D)-quasi_isometry_between X Y f"
  proof (rule quasi_isometry_betweenI)
    show "f`X \<subseteq> Y" unfolding f_def using \<open>y \<in> Y\<close> by auto
    show "1 (C + 2 * D)-quasi_isometry_on X f"
    proof (rule quasi_isometry_onI, auto simp add: \<open>C \<ge> 0\<close> \<open>D \<ge> 0\<close> f_def)
      fix a b assume "a \<in> X" "b \<in> X"
      have "dist a b \<le> dist a x + dist x b"
        using dist_triangle by auto
      also have "... \<le> D + D"
        using D[OF \<open>a \<in> X\<close>] D[OF \<open>b \<in> X\<close>] by (auto simp add: dist_commute)
      finally show "dist a b \<le> C + 2 * D" using \<open>C \<ge> 0\<close> by auto
    qed
    show "\<exists>a\<in>X. dist (f a) z \<le> C + 2 * D" if "z \<in> Y" for z
      unfolding f_def using \<open>x \<in> X\<close> C[OF \<open>z \<in> Y\<close>] \<open>D \<ge> 0\<close> by auto
  qed
  then show ?thesis unfolding quasi_isometric_def by auto
qed

subsection \<open>Quasi-isometries of Euclidean spaces.\<close>

text \<open>A less trivial fact is that the dimension of euclidean spaces is invariant under
quasi-isometries. It is proved below using growth argument, as quasi-isometries preserve the
growth rate.

The growth of the space is asymptotic behavior of the number of well-separated points that
fit in a ball of radius $R$, when $R$ tends to infinity. Up to a suitable equivalence, it is
clearly a quasi-isometry invariance. We show below that, in a Euclidean space of dimension $d$,
the growth is like $R^d$: the upper bound is obtained by using the fact that we have disjoint balls
inside a big ball, hence volume controls conclude the argument, while the lower bound is obtained
by considering integer points.\<close>

text \<open>First, we show that the growth rate of a Euclidean space of dimension $d$ is bounded
from above by $R^d$, using the control on measure of disjoint balls and a volume argument.\<close>

proposition growth_rate_euclidean_above:
  fixes D::real
  assumes "D > (0::real)"
      and H: "F \<subseteq> cball (0::'a::euclidean_space) R" "R \<ge> 0"
          "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> dist x y \<ge> D"
  shows "finite F \<and> card F \<le> 1 + ((6/D)^(DIM('a))) * R^(DIM('a))"
proof -
  define C::real where "C = ((6/D)^(DIM('a)))"
  have "C \<ge> 0" unfolding C_def using \<open>D > 0\<close> by auto
  have "D/3 \<ge> 0" using assms by auto
  have "finite F \<and> card F \<le> 1 + C * R^(DIM('a))"
  proof (cases "R < D/2")
    case True
    have "x = y" if "x \<in> F" "y \<in> F" for x y
    proof (rule ccontr)
      assume "\<not>(x = y)"
      then have "D \<le> dist x y" using H \<open>x \<in> F\<close> \<open>y \<in> F\<close> by auto
      also have "... \<le> dist x 0 + dist 0 y" by (rule dist_triangle)
      also have "... \<le> R + R"
        using H(1) \<open>x \<in> F\<close> \<open>y \<in> F\<close> by (intro add_mono, auto)
      also have "... < D" using \<open>R < D/2\<close> by auto
      finally show False by simp
    qed
    then have "finite F \<and> card F \<le> 1" using finite_at_most_singleton by auto
    moreover have "1 + 0 * R^(DIM('a)) \<le> 1 + C * R^(DIM('a))"
      using \<open>C \<ge> 0\<close> \<open>R \<ge> 0\<close> by (auto intro: mono_intros)
    ultimately show ?thesis by auto
  next
    case False
    have "card G \<le> 1 + C * R^(DIM('a))" if "G \<subseteq> F" "finite G" for G
    proof -
      have "norm y \<le> 2*R" if "y \<in> cball x (D/3)" "x \<in> G" for x y
      proof -
        have "norm y = dist 0 y" by auto
        also have "... \<le> dist 0 x + dist x y" by (rule dist_triangle)
        also have "... \<le> R + D/3"
          using \<open>x \<in> G\<close> \<open>G \<subseteq> F\<close> \<open>y \<in> cball x (D/3)\<close> \<open>F \<subseteq> cball 0 R\<close> by (auto intro: add_mono)
        finally show ?thesis using False \<open>D > 0\<close> by auto
      qed
      then have I: "(\<Union>x\<in>G. cball x (D/3)) \<subseteq> cball 0 (2*R)"
        by auto
      have "disjoint_family_on (\<lambda>x. cball x (D/3)) G"
        unfolding disjoint_family_on_def proof (auto)
        fix a b x assume *: "a \<in> G" "b \<in> G" "a \<noteq> b" "dist a x * 3 \<le> D" "dist b x * 3 \<le> D"
        then have "D \<le> dist a b" using H \<open>G \<subseteq> F\<close> by auto
        also have "... \<le> dist a x + dist x b" by (rule dist_triangle)
        also have "... \<le> D/3 + D/3"
          using * by (auto simp add: dist_commute intro: mono_intros)
        also have "... < D" using \<open>D > 0\<close> by auto
        finally show False by simp
      qed

      have "2 * R \<ge> 0" using \<open>R \<ge> 0\<close> by auto
      define A where "A = measure lborel (cball (0::'a) 1)"
      have "A > 0" unfolding A_def using lebesgue_measure_ball_pos by auto
      have "card G * ((D/3)^(DIM('a)) * A) = (\<Sum>x\<in>G. ((D/3)^(DIM('a)) * A))"
        by auto
      also have "... = (\<Sum>x\<in>G. measure lborel (cball x (D/3)))"
        unfolding lebesgue_measure_ball[OF \<open>D/3 \<ge> 0\<close>] A_def by auto
      also have "... = measure lborel (\<Union>x\<in>G. cball x (D/3))"
        apply (rule measure_finite_Union[symmetric, OF \<open>finite G\<close> _ \<open>disjoint_family_on (\<lambda>x. cball x (D/3)) G\<close>])
        apply auto using emeasure_bounded_finite less_imp_neq by auto
      also have "... \<le> measure lborel (cball (0::'a) (2*R))"
        apply (rule measure_mono_fmeasurable) using I \<open>finite G\<close> emeasure_bounded_finite
        unfolding fmeasurable_def by auto
      also have "... = (2*R)^(DIM('a)) * A"
        unfolding A_def using lebesgue_measure_ball[OF \<open>2*R \<ge> 0\<close>] by auto
      finally have "card G * (D/3)^(DIM('a)) \<le> (2*R)^(DIM('a))"
        using \<open>A > 0\<close> by (auto simp add: divide_simps)
      then have "card G \<le> C * R^(DIM('a))"
        unfolding C_def using \<open>D > 0\<close> apply (auto simp add: algebra_simps divide_simps)
        by (metis numeral_times_numeral power_mult_distrib semiring_norm(12) semiring_norm(14))
      then show ?thesis by auto
    qed
    then show "finite F \<and> card F \<le> 1 + C * R^(DIM('a))"
      by (rule finite_finite_subset_caract')
  qed
  then show ?thesis unfolding C_def by blast
qed

text \<open>Then, we show that the growth rate of a Euclidean space of dimension $d$ is bounded
from below by $R^d$, using integer points.\<close>

proposition growth_rate_euclidean_below:
  fixes D::real
  assumes "R \<ge> 0"
  shows "\<exists>F. (F \<subseteq> cball (0::'a::euclidean_space) R
            \<and> (\<forall>x\<in>F. \<forall>y\<in>F. x = y \<or> dist x y \<ge> D) \<and> finite F \<and> card F \<ge> (1/((max D 1) * DIM('a)))^(DIM('a)) * R^(DIM('a)))"
proof -
  define E where "E = max D 1"
  have "E > 0" unfolding E_def by auto
  define c where "c = (1/(E * DIM('a)))^(DIM('a))"
  have "c > 0" unfolding c_def using \<open>E > 0\<close> by auto

  define n where "n = nat (floor (R/(E * DIM('a)))) + 1"
  then have "n > 0" using \<open>R \<ge> 0\<close> by auto

  have "R/(E * DIM('a)) \<le> n" unfolding n_def by linarith
  then have "c * R^(DIM('a)) \<le> n^(DIM('a))"
    unfolding c_def power_mult_distrib[symmetric] by (auto simp add: \<open>0 < E\<close> \<open>0 \<le> R\<close> less_imp_le power_mono)
  have "n-1 \<le> R/(E * DIM('a))"
    unfolding n_def using \<open>R \<ge> 0\<close> \<open>E > 0\<close> by auto
  then have "E * DIM('a) * (n-1) \<le> R"
    using \<open>R \<ge> 0\<close> \<open>E > 0\<close> by (simp add: mult.commute pos_le_divide_eq)

  text \<open>We want to consider the set of linear combinations of basis elements with integer
  coefficients bounded by $n$ (multiplied by $E$ to guarantee the $D$ separation).
  The formal way to write these elements is to consider all
  the functions from the basis to $\{0,\dotsc, n-1\}$, and associate to such a function
  $f$ the point $\sum E f(i) \cdot i$ where the sum is over all basis elements $i$. This is
  what the next definition does.\<close>
  define F::"'a set" where "F = (\<lambda>f. (\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i))`((Basis::('a set)) \<rightarrow>\<^sub>E {0..<n})"

  have "f = g" if "f \<in> (Basis::('a set)) \<rightarrow>\<^sub>E {0..<n}" "g \<in> Basis \<rightarrow>\<^sub>E {0..<n}"
                  "(\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (E * real (g i)) *\<^sub>R i)" for f g
  proof (rule ext)
    fix i show "f i = g i"
    proof (cases "i \<in> Basis")
      case True
      then have "E * real(f i) = E * real(g i)"
        using inner_sum_left_Basis[OF True, of "\<lambda>i. E * real(f i)"] inner_sum_left_Basis[OF True, of "\<lambda>i. E * real(g i)"] that(3)
        by auto
      then show "f i = g i" using \<open>E > 0\<close> by auto
    next
      case False
      then have "f i = undefined" "g i = undefined" using that by auto
      then show "f i = g i" by auto
    qed
  qed
  then have "inj_on (\<lambda>f. (\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i)) ((Basis::('a set)) \<rightarrow>\<^sub>E {0..<n})"
    by (simp add: inj_onI)
  then have "card F = card ((Basis::('a set)) \<rightarrow>\<^sub>E {0..<n})" unfolding F_def
    using card_image by blast
  also have "... = n^(DIM('a))"
    unfolding card_PiE[OF finite_Basis] by (auto simp add: prod_constant)
  finally have "card F = n^(DIM('a))" by auto
  then have "finite F" using \<open>n > 0\<close>
    using card_infinite by force
  have "card F \<ge> c * R^(DIM('a))"
    using \<open>c * R^(DIM('a)) \<le> n^(DIM('a))\<close> \<open>card F = n^(DIM('a))\<close> by auto

  have separation: "dist x y \<ge> D" if "x \<in> F" "y \<in> F" "x \<noteq> y" for x y
  proof -
    obtain f where x: "f \<in> (Basis::('a set)) \<rightarrow>\<^sub>E {0..<n}" "x = (\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i)"
      using \<open>x \<in> F\<close> unfolding F_def by auto
    obtain g where y: "g \<in> (Basis::('a set)) \<rightarrow>\<^sub>E {0..<n}" "y = (\<Sum>i\<in>Basis. (E * real (g i)) *\<^sub>R i)"
      using \<open>y \<in> F\<close> unfolding F_def by auto
    obtain i where "f i \<noteq> g i" using x y \<open>x \<noteq>y\<close> by force
    moreover have "f j = g j" if "j \<notin> Basis" for j
      using x(1) y(1) that by fastforce
    ultimately have "i \<in> Basis" by auto
    have "D \<le> E" unfolding E_def by auto
    also have "... \<le> abs(E * (real (f i) - real (g i)))" using \<open>E > 0\<close>
      using \<open>f i \<noteq> g i\<close> by (auto simp add: divide_simps abs_mult)
    also have "... = abs(inner x i - inner y i)"
      unfolding x(2) y(2) inner_sum_left_Basis[OF \<open>i \<in> Basis\<close>] by (auto simp add: algebra_simps)
    also have "... = abs(inner (x-y) i)"
      by (simp add: inner_diff_left)
    also have "... \<le> norm (x-y)" using Basis_le_norm[OF \<open>i \<in> Basis\<close>] by blast
    finally show "dist x y \<ge> D" by (simp add: dist_norm)
  qed

  have "norm x \<le> R" if "x \<in> F" for x
  proof -
    obtain f where x: "f \<in> (Basis::('a set)) \<rightarrow>\<^sub>E {0..<n}" "x = (\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i)"
      using \<open>x \<in> F\<close> unfolding F_def by auto
    then have "norm x = norm (\<Sum>i\<in>Basis. (E * real (f i)) *\<^sub>R i)" by simp
    also have "... \<le> (\<Sum>i\<in>Basis. norm((E * real (f i)) *\<^sub>R i))"
      by (rule norm_sum)
    also have "... = (\<Sum>i\<in>Basis. abs(E * real (f i)))" by auto
    also have "... = (\<Sum>i\<in>Basis. E * real (f i))" using \<open>E > 0\<close> by auto
    also have "... \<le> (\<Sum>i\<in>(Basis::'a set). E * (n-1))"
      apply (rule sum_mono) using PiE_mem[OF x(1)] \<open>E > 0\<close> apply (auto simp add: divide_simps)
      using \<open>n > 0\<close> by fastforce
    also have "... = DIM('a) * E * (n-1)"
      by auto
    finally show "norm x \<le> R" using \<open>E * DIM('a) * (n-1) \<le> R\<close> by (auto simp add: algebra_simps)
  qed
  then have "F \<subseteq> cball 0 R" by auto
  then show ?thesis using \<open>card F \<ge> c * R^(DIM('a))\<close> \<open>finite F\<close> separation c_def E_def by blast
qed

text \<open>As the growth is invariant under quasi-isometries, we deduce that it is impossible
to map quasi-isometrically a Euclidean space in a space of strictly smaller dimension.\<close>

proposition quasi_isometry_on_euclidean:
  fixes f::"'a::euclidean_space\<Rightarrow>'b::euclidean_space"
  assumes "lambda C-quasi_isometry_on UNIV f"
  shows "DIM('a) \<le> DIM('b)"
proof -
  have C: "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms] by auto
  define D where "D = lambda * (C+1)"
  define Ca where "Ca = (1/((max D 1) * DIM('a)))^(DIM('a))"
  have "Ca > 0" unfolding Ca_def by auto
  have A: "\<And>R::real. R \<ge> 0 \<Longrightarrow> (\<exists>F. (F \<subseteq> cball (0::'a::euclidean_space) R
        \<and> (\<forall>x\<in>F. \<forall>y\<in>F. x = y \<or> dist x y \<ge> D) \<and> finite F \<and> card F \<ge> Ca * R^(DIM('a))))"
    using growth_rate_euclidean_below[of _ D] unfolding Ca_def by blast
  define Cb::real where "Cb = ((6/1)^(DIM('b)))"
  have B: "\<And>F (R::real). (F \<subseteq> cball (0::'b::euclidean_space) R \<Longrightarrow> R \<ge> 0 \<Longrightarrow> (\<forall>x\<in>F. \<forall>y\<in>F. x = y \<or> dist x y \<ge> 1) \<Longrightarrow> (finite F \<and> card F \<le> 1 + Cb * R^(DIM('b))))"
    using growth_rate_euclidean_above[of 1] unfolding Cb_def by fastforce

  have M: "Ca * R^(DIM('a)) \<le> 1 + Cb * (lambda * R + C + norm(f 0))^(DIM('b))" if "R \<ge> 0" for R::real
  proof -
    obtain F::"'a set" where F: "F \<subseteq> cball 0 R" "\<forall>x\<in>F. \<forall>y\<in>F. x = y \<or> dist x y \<ge> D"
                                "finite F" "card F \<ge> Ca * R^(DIM('a))"
      using A[OF \<open>R \<ge> 0\<close>] by auto
    define G where "G = f`F"
    have *: "dist (f x) (f y) \<ge> 1" if "x \<noteq> y" "x \<in> F" "y \<in> F" for x y
    proof -
      have "dist x y \<ge> D" using that F(2) by auto
      have "1 = (1/lambda) * D - C" using \<open>lambda \<ge> 1\<close> unfolding D_def by auto
      also have "... \<le> (1/lambda) * dist x y - C"
        using \<open>dist x y \<ge> D\<close> \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
      also have "... \<le> dist (f x) (f y)"
        using quasi_isometry_onD[OF assms] by auto
      finally show ?thesis by simp
    qed
    then have "inj_on f F" unfolding inj_on_def by force
    then have "card G = card F" unfolding G_def by (simp add: card_image)
    then have "card G \<ge> Ca * R^(DIM('a))" using F by auto

    moreover have "finite G \<and> card G \<le> 1 + Cb * (lambda * R + C + norm(f 0))^(DIM('b))"
    proof (rule B)
      show "0 \<le> lambda * R + C + norm (f 0)" using \<open>R \<ge> 0\<close> \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      show "\<forall>x\<in>G. \<forall>y\<in>G. x = y \<or> 1 \<le> dist x y" using * unfolding G_def by (auto, metis)
      show "G \<subseteq> cball 0 (lambda * R + C + norm (f 0))"
      unfolding G_def proof (auto)
        fix x assume "x \<in> F"
        have "norm (f x) \<le> norm (f 0) + dist (f x) (f 0)"
          by (metis dist_0_norm dist_triangle2)
        also have "... \<le> norm (f 0) + (lambda * dist x 0 + C)"
          by (intro mono_intros quasi_isometry_onD(1)[OF assms]) auto
        also have "... \<le> norm (f 0) + lambda * R + C"
          using \<open>x \<in> F\<close> \<open>F \<subseteq> cball 0 R\<close> \<open>lambda \<ge> 1\<close> by auto
        finally show "norm (f x) \<le> lambda * R + C + norm (f 0)" by auto
      qed
    qed
    ultimately show "Ca * R^(DIM('a)) \<le> 1 + Cb * (lambda * R + C + norm(f 0))^(DIM('b))"
      by auto
  qed
  define CB where "CB = max Cb 0"
  have "CB \<ge> 0" "CB \<ge> Cb" unfolding CB_def by auto
  define D::real where "D = (1 + CB * (lambda + C + norm(f 0))^(DIM('b)))/Ca"
  have Rineq: "R^(DIM('a)) \<le> D * R^(DIM('b))" if "R \<ge> 1" for R::real
  proof -
    have "Ca * R^(DIM('a)) \<le> 1 + Cb * (lambda * R + C + norm(f 0))^(DIM('b))"
      using M \<open>R \<ge> 1\<close> by auto
    also have "... \<le> 1 + CB * (lambda * R + C + norm(f 0))^(DIM('b))"
      using \<open>CB \<ge> Cb\<close> \<open>lambda \<ge> 1\<close> \<open>R \<ge> 1\<close> \<open>C \<ge> 0\<close> by (auto intro!: mult_right_mono)
    also have "... \<le> R^(DIM('b)) + CB * (lambda * R + C * R + norm(f 0) * R)^(DIM('b))"
      using \<open>lambda \<ge> 1\<close> \<open>R \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>CB \<ge> 0\<close> by (auto intro!: mono_intros)
    also have "... = (1 + CB * (lambda + C + norm(f 0))^(DIM('b))) * R^(DIM('b))"
      by (auto simp add: algebra_simps power_mult_distrib[symmetric])
    finally show ?thesis
      using \<open>Ca > 0\<close> unfolding D_def by (auto simp add: divide_simps algebra_simps)
  qed
  show "DIM('a) \<le> DIM('b)"
  proof (rule ccontr)
    assume "\<not>(DIM('a) \<le> DIM('b))"
    then obtain n where "DIM('a) = DIM('b) + n" "n > 0"
      by (metis less_imp_add_positive not_le)
    have "D \<ge> 1" using Rineq[of 1] by auto
    define R where "R = 2 * D"
    then have "R \<ge> 1" using \<open>D \<ge> 1\<close> by auto
    have "R^n * R^(DIM('b)) = R^(DIM('a))"
      unfolding \<open>DIM('a) = DIM('b) + n\<close> by (auto simp add: power_add)
    also have "... \<le> D * R^(DIM('b))" using Rineq[OF \<open>R \<ge> 1\<close>] by auto
    finally have "R^n \<le> D" using \<open>R \<ge> 1\<close> by auto
    moreover have "2 * D \<le> R^n" unfolding R_def using \<open>D \<ge> 1\<close> \<open>n > 0\<close>
      by (metis One_nat_def Suc_leI \<open>1 \<le> R\<close> \<open>R \<equiv> 2 * D\<close> less_eq_real_def power_increasing_iff power_one power_one_right)
    ultimately show False using \<open>D \<ge> 1\<close> by auto
  qed
qed

text \<open>As a particular case, we deduce that two quasi-isometric Euclidean spaces have the
same dimension.\<close>

theorem quasi_isometric_euclidean:
  assumes "quasi_isometric (UNIV::'a::euclidean_space set) (UNIV::'b::euclidean_space set)"
  shows "DIM('a) = DIM('b)"
proof -
  obtain lambda C and f::"'a \<Rightarrow>'b" where "lambda C-quasi_isometry_on UNIV f"
    using assms unfolding quasi_isometric_def quasi_isometry_between_def by auto
  then have *: "DIM('a) \<le> DIM('b)" using quasi_isometry_on_euclidean by auto

  have "quasi_isometric (UNIV::'b::euclidean_space set) (UNIV::'a::euclidean_space set)"
    using quasi_isometric_equiv_rel(3)[OF assms] by auto
  then obtain lambda C and f::"'b \<Rightarrow>'a" where "lambda C-quasi_isometry_on UNIV f"
    unfolding quasi_isometric_def quasi_isometry_between_def by auto
  then have "DIM('b) \<le> DIM('a)" using quasi_isometry_on_euclidean by auto
  then show ?thesis using * by auto
qed

text \<open>A different (and important) way to prove the above statement would be to use asymptotic
cones. Here, it can be done in an elementary way: start with a quasi-isometric map $f$, and
consider a limit (defined with a ultrafilter) of $x\mapsto f(n x)/n$. This is a map which
contracts and expands the distances by at most $\lambda$. In particular, it is a homeomorphism
on its image. No such map exists if the dimension of the target is smaller than the dimension
of the source (invariance of domain theorem, already available in the library).

The above argument using growth is more elementary to write, though.\<close>


subsection \<open>Quasi-geodesics\<close>

text \<open>A quasi-geodesic is a quasi-isometric embedding of a real segment into a metric space. As the
embedding need not be continuous, a quasi-geodesic does not have to be compact, nor connected, which
can be a problem. However, in a geodesic space, it is always possible to deform a quasi-geodesic
into a continuous one (at the price of worsening the quasi-isometry constants). This is the content
of the proposition \verb+quasi_geodesic_made_lipschitz+ below, which is a variation around Lemma
III.H.1.11 in~\cite{bridson_haefliger}. The strategy of the proof is simple: assume that the
quasi-geodesic $c$ is defined on $[a,b]$. Then, on the points $a$, $a+C/\lambda$, $\cdots$,
$a+ N \cdot C/\lambda$, $b$, take $d$ equal to $c$, where $N$ is chosen so that the distance
between the last point and $b$ is in $[C/\lambda, 2C/\lambda)$. In the intervals, take $d$ to
be geodesic.\<close>

proposition (in geodesic_space) quasi_geodesic_made_lipschitz:
  fixes c::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {a..b} c" "dist (c a) (c b) \<ge> 2 * C"
  shows "\<exists>d. continuous_on {a..b} d \<and> d a = c a \<and> d b = c b
              \<and> (\<forall>x\<in>{a..b}. dist (c x) (d x) \<le> 4 * C)
              \<and> lambda (4 * C)-quasi_isometry_on {a..b} d
              \<and> (2 * lambda)-lipschitz_on {a..b} d
              \<and> hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C"
proof -
  consider "C = 0" | "C > 0 \<and> b \<le> a" | "C > 0 \<and> a < b \<and> b \<le> a + 2 * C/lambda" | "C > 0 \<and> a +2 * C/lambda < b"
    using quasi_isometry_onD(4)[OF assms(1)] by fastforce
  then show ?thesis
  proof (cases)
    text \<open>If the original function is Lipschitz, we can use it directly.\<close>
    case 1
    have "lambda-lipschitz_on {a..b} c"
      apply (rule lipschitz_onI) using 1 quasi_isometry_onD[OF assms(1)] by auto
    then have a: "(2 * lambda)-lipschitz_on {a..b} c"
      apply (rule lipschitz_on_mono) using quasi_isometry_onD[OF assms(1)] assms by (auto simp add: divide_simps)
    then have b: "continuous_on {a..b} c"
      using lipschitz_on_continuous_on by blast
    have "continuous_on {a..b} c \<and> c a = c a \<and> c b = c b
                \<and> (\<forall>x\<in>{a..b}. dist (c x) (c x) \<le> 4 * C)
                \<and> lambda (4 * C)-quasi_isometry_on {a..b} c
                \<and> (2 * lambda)-lipschitz_on {a..b} c
                \<and> hausdorff_distance (c`{a..b}) (c`{a..b}) \<le> 2 * C"
      using 1 a b assms(1) by auto
    then show ?thesis by blast
  next
    text \<open>If the original interval is empty, anything will do.\<close>
    case 2
    then have "b < a" using assms(2) less_eq_real_def by auto
    then have *: "{a..b} = {}" by auto
    have a: "(2 * lambda)-lipschitz_on {a..b} c"
      unfolding * apply (rule lipschitz_intros) using quasi_isometry_onD[OF assms(1)] assms by (auto simp add: divide_simps)
    then have b: "continuous_on {a..b} c"
      using lipschitz_on_continuous_on by blast
    have "continuous_on {a..b} c \<and> c a = c a \<and> c b = c b
                \<and> (\<forall>x\<in>{a..b}. dist (c x) (c x) \<le> 4 * C)
                \<and> lambda (4 * C)-quasi_isometry_on {a..b} c
                \<and> (2 * lambda)-lipschitz_on {a..b} c
                \<and> hausdorff_distance (c`{a..b}) (c`{a..b}) \<le> 2 * C"
      using a b quasi_isometry_on_empty assms(1) quasi_isometry_onD[OF assms(1)] * assms by auto
    then show ?thesis by blast
  next
    text \<open>If the original interval is short, we can use a direct geodesic interpolation between
    its endpoints\<close>
    case 3
    then have C: "C > 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms(1)] by auto
    have [mono_intros]: "1/lambda \<le> lambda" using C by (simp add: divide_simps mult_ge1_powers(1))
    have "a < b" using 3 by simp
    have "2 * C \<le> dist (c a) (c b)" using assms by auto
    also have "... \<le> lambda * dist a b + C"
      using quasi_isometry_onD[OF assms(1)] \<open>a < b\<close> by auto
    also have "... = lambda * (b-a) + C"
      using \<open>a < b\<close> dist_real_def by auto
    finally have *: "C \<le> (b-a) * lambda" by (auto simp add: algebra_simps)
    define d where "d = (\<lambda>x. geodesic_segment_param {(c a)--(c b)} (c a) ((dist (c a) (c b) /(b-a)) * (x-a)))"
    have dend: "d a = c a" "d b = c b" unfolding d_def using \<open>a < b\<close> by auto

    have Lip: "(2 * lambda)-lipschitz_on {a..b} d"
    proof -
      have "(1 * (((2 * lambda)) * (1+0)))-lipschitz_on {a..b} (\<lambda>x. geodesic_segment_param {(c a)--(c b)} (c a) ((dist (c a) (c b) /(b-a)) * (x-a)))"
      proof (rule lipschitz_on_compose2[of _ _ "\<lambda>x. ((dist (c a) (c b) /(b-a)) * (x-a))"], intro lipschitz_intros)
        have "(\<lambda>x. dist (c a) (c b) / (b-a) * (x - a)) ` {a..b} \<subseteq> {0..dist (c a) (c b)}"
          apply auto using \<open>a < b\<close> by (auto simp add: algebra_simps divide_simps intro: mult_right_mono)
        moreover have "1-lipschitz_on {0..dist (c a) (c b)} (geodesic_segment_param {c a--c b} (c a))"
          by (rule isometry_on_lipschitz, simp)
        ultimately show "1-lipschitz_on ((\<lambda>x. dist (c a) (c b) / (b-a) * (x - a)) ` {a..b}) (geodesic_segment_param {c a--c b} (c a))"
          using lipschitz_on_subset by auto

        have "dist (c a) (c b) \<le> lambda * dist a b + C"
          apply (rule quasi_isometry_onD(1)[OF assms(1)])
          using \<open>a < b\<close> by auto
        also have "... = lambda * (b - a) + C"
          unfolding dist_real_def using \<open>a < b\<close> by auto
        also have "... \<le> 2 * lambda * (b-a)"
          using * by (auto simp add: algebra_simps)
        finally show "\<bar>dist (c a) (c b) / (b - a)\<bar> \<le> 2 * lambda"
          using \<open>a < b\<close> by (auto simp add: divide_simps)
      qed
      then show ?thesis unfolding d_def by auto
    qed
    have dist_c_d: "dist (c x) (d x) \<le> 4 * C" if H: "x \<in> {a..b}" for x
    proof -
      have "(x-a) + (b - x) \<le> 2 * C/lambda"
        using that 3 by auto
      then consider "x-a \<le> C/lambda" | "b - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>{a,b}. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 H by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 H by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v \<in> {a,b}" "dist x v \<le> C/lambda" by auto
      have "dist (c x) (d x) \<le> dist (c x) (c v) + dist (c v) (d v) + dist (d v) (d x)"
        by (intro mono_intros)
      also have "... \<le> (lambda * dist x v + C) + 0 + ((2 * lambda) * dist v x)"
        apply (intro mono_intros quasi_isometry_onD(1)[OF assms(1)] that lipschitz_onD[OF Lip])
        using v \<open>a < b\<close> dend by auto
      also have "... \<le> (lambda * (C/lambda) + C) + 0 + ((2 * lambda) * (C/lambda))"
        apply (intro mono_intros) using C v by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis
        using C by (auto simp add: algebra_simps divide_simps)
    qed
    text \<open>A similar argument shows that the Hausdorff distance between the images is bounded by $2C$.\<close>
    have "hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C"
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 2 * C" using C by auto
      fix z assume "z \<in> c`{a..b}"
      then obtain x where x: "x \<in> {a..b}" "z = c x" by auto
      have "(x-a) + (b - x) \<le> 2 * C/lambda"
        using x 3 by auto
      then consider "x-a \<le> C/lambda" | "b - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>{a,b}. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 x by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 x by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v \<in> {a,b}" "dist x v \<le> C/lambda" by auto
      have "dist z (d v) = dist (c x) (c v)" unfolding x(2) using v dend by auto
      also have "... \<le> lambda * dist x v + C"
        apply (rule quasi_isometry_onD(1)[OF assms(1)]) using v(1) x(1) by auto
      also have "... \<le> lambda * (C/lambda) + C"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (d v) \<le> 2 * C" by simp
      show "\<exists>y\<in>d ` {a..b}. dist z y \<le> 2 * C"
        apply (rule bexI[of _ "d v"]) using * v(1) \<open>a < b\<close> by auto
    next
      fix z assume "z \<in> d`{a..b}"
      then obtain x where x: "x \<in> {a..b}" "z = d x" by auto
      have "(x-a) + (b - x) \<le> 2 * C/lambda"
        using x 3 by auto
      then consider "x-a \<le> C/lambda" | "b - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>{a,b}. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 x by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 x by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v \<in> {a,b}" "dist x v \<le> C/lambda" by auto
      have "dist z (c v) = dist (d x) (d v)" unfolding x(2) using v dend by auto
      also have "... \<le> 2 * lambda * dist x v"
        apply (rule lipschitz_onD(1)[OF Lip]) using v(1) x(1) by auto
      also have "... \<le> 2 * lambda * (C/lambda)"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (c v) \<le> 2 * C" by simp
      show "\<exists>y\<in>c`{a..b}. dist z y \<le> 2 * C"
        apply (rule bexI[of _ "c v"]) using * v(1) \<open>a < b\<close> by auto
    qed
    have "lambda (4 * C)-quasi_isometry_on {a..b} d"
    proof
      show "1 \<le> lambda" using C by auto
      show "0 \<le> 4 * C" using C by auto
      show "dist (d x) (d y) \<le> lambda * dist x y + 4 * C" if "x \<in> {a..b}" "y \<in> {a..b}" for x y
      proof -
        have "dist (d x) (d y) \<le> 2 * lambda * dist x y"
          apply (rule lipschitz_onD[OF Lip]) using that by auto
        also have "... = lambda * dist x y + lambda * dist x y"
          by auto
        also have "... \<le> lambda * dist x y + lambda * (2 * C/lambda)"
          apply (intro mono_intros) using 3 that C unfolding dist_real_def by auto
        also have "... = lambda * dist x y + 2 * C"
          using C by (simp add: algebra_simps divide_simps)
        finally show ?thesis using C by auto
      qed
      show "1 / lambda * dist x y - 4 * C \<le> dist (d x) (d y)" if "x \<in> {a..b}" "y \<in> {a..b}" for x y
      proof -
        have "1/lambda * dist x y - 4 * C \<le> lambda * dist x y - 2 * C"
          apply (intro mono_intros) using C by auto
        also have "... \<le> lambda * (2 * C/lambda) - 2 * C"
          apply (intro mono_intros) using that 3 C unfolding dist_real_def by auto
        also have "... = 0"
          using C by (auto simp add: algebra_simps divide_simps)
        also have "... \<le> dist (d x) (d y)" by auto
        finally show ?thesis by simp
      qed
    qed

    then have "continuous_on {a..b} d \<and> d a = c a \<and> d b = c b
          \<and> lambda (4 * C)-quasi_isometry_on {a..b} d
          \<and> (\<forall>x\<in>{a..b}. dist (c x) (d x) \<le> 4 *C)
          \<and> (2*lambda)-lipschitz_on {a..b} d
          \<and> hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C"
      using dist_c_d \<open>d a = c a\<close> \<open>d b = c b\<close> \<open>(2*lambda)-lipschitz_on {a..b} d\<close>
            \<open>hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C\<close> lipschitz_on_continuous_on by auto
    then show ?thesis by auto
  next
    text \<open>Now, for the only nontrivial case, we use geodesic interpolation between the points
    $a$, $a + C/\lambda$, $\cdots$, $a+N\cdot C/\lambda$, $b'$, $b$ where $N$ is chosen so that
    the distance between $a+N C/\lambda$ and $b$ belongs to $[2C/\lambda, 3C/\lambda)$, and
    $b'$ is the middle of this interval. This gives a decomposition into intervals of length
    at most $3/2\cdot C/\lambda$.\<close>
    case 4
    then have C: "C > 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms(1)] by auto
    have "a < b" using 4 C by (smt divide_pos_pos)

    have [mono_intros]: "1/lambda \<le> lambda" using C by (simp add: divide_simps mult_ge1_powers(1))
    define N where "N = floor((b-a)/(C/lambda)) - 2"
    have N: "N \<le> (b-a)/(C/lambda)-2" "(b-a)/(C/lambda) \<le> N + (3::real)"
      unfolding N_def by linarith+

    have "2 < (b-a)/(C/lambda)"
      using C 4 by (auto simp add: divide_simps algebra_simps)
    then have N0 : "0 \<le> N" unfolding N_def by auto
    define p where "p = (\<lambda>t::int. a + (C/lambda) * t)"
    have pmono: "p i \<le> p j" if "i \<le> j" for i j
      unfolding p_def using that C by (auto simp add: algebra_simps divide_simps)
    have pmono': "p i < p j" if "i < j" for i j
      unfolding p_def using that C by (auto simp add: algebra_simps divide_simps)
    have "p (N+1) \<le> b"
      unfolding p_def using C N by (auto simp add: algebra_simps divide_simps)
    then have pb: "p i \<le> b" if "i \<in> {0..N}" for i
      using that pmono by (meson atLeastAtMost_iff linear not_le order_trans zle_add1_eq_le)
    have bpN: "b - p N \<in> {2 * C/lambda .. 3 * C/lambda}"
      unfolding p_def using C N apply (auto simp add: divide_simps)
      by (auto simp add: algebra_simps)
    have "p N < b" using pmono'[of N "N+1"] \<open>p (N+1) \<le> b\<close> by auto
    define b' where "b' = (b + p N)/2"
    have b': "p N < b'" "b' < b" using \<open>p N < b\<close> unfolding b'_def by auto
    have pb': "p i \<le> b'" if "i \<in> {0..N}" for i
      using pmono[of i N] b' that by auto

    text \<open>Introduce the set $A$ along which one will discretize.\<close>
    define A where "A = p`{0..N} \<union> {b', b}"
    have "finite A" unfolding A_def by auto
    have "b \<in> A" unfolding A_def by auto
    have "p 0 \<in> A" unfolding A_def using \<open>0 \<le> N\<close> by auto
    moreover have pa: "p 0 = a" unfolding p_def by auto
    ultimately have "a \<in> A" by auto
    have "A \<subseteq> {a..b}"
      unfolding A_def using \<open>a < b\<close> b' pa pb pmono N0 by fastforce
    then have "b' \<in> {a..<b}" unfolding A_def using \<open>b' < b\<close> by auto

    have A : "finite A" "A \<subseteq> {a..b}" "a \<in> A" "b \<in> A" "a < b" by fact+

    have nx: "next_in A x = x + C/lambda" if "x \<in> A" "x \<noteq> b" "x \<noteq> b'" "x \<noteq> p N" for x
    proof (rule next_inI[OF A])
      show "x \<in> {a..<b}" using \<open>x \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> \<open>x \<noteq> b\<close> by auto
      obtain i where i: "x = p i" "i \<in> {0..N}"
        using \<open>x \<in> A\<close> \<open>x \<noteq> b\<close> \<open>x \<noteq> b'\<close> unfolding A_def by auto
      have *: "p (i+1) = x + C/lambda" unfolding i(1) p_def by (auto simp add: algebra_simps)
      have "i \<noteq> N" using that i by auto
      then have "i + 1 \<in> {0..N}" using \<open>i \<in> {0..N}\<close> by auto
      then have "p (i+1) \<in> A" unfolding A_def by fastforce
      then show "x + C/lambda \<in> A" unfolding * by auto
      show "x < x + C / lambda" using C by auto
      show "{x<..<x + C / lambda} \<inter> A = {}"
      proof (auto)
        fix y assume y: "y \<in> A" "x < y" "y < x + C/lambda"
        consider "y = b" | "y = b'" | "\<exists>j\<le>i. y = p j" | "\<exists>j>i. y = p j"
          using \<open>y \<in> A\<close> not_less unfolding A_def by auto
        then show False
        proof (cases)
          case 1
          have "x + C/lambda \<le> b" unfolding *[symmetric] using \<open>i + 1 \<in> {0..N}\<close> pb by auto
          then show False using y(3) unfolding 1 i(1) by auto
        next
          case 2
          have "x + C/lambda \<le> b'" unfolding *[symmetric] using \<open>i + 1 \<in> {0..N}\<close> pb' by auto
          then show False using y(3) unfolding 2 i(1) by auto
        next
          case 3
          then obtain j where j: "j \<le> i" "y = p j" by auto
          have "y \<le> x" unfolding j(2) i(1) using pmono[OF \<open>j \<le> i\<close>] by simp
          then show False using \<open>x < y\<close> by auto
        next
          case 4
          then obtain j where j: "j > i" "y = p j" by auto
          then have "i+1 \<le> j" by auto
          have "x + C/lambda \<le> y" unfolding j(2) *[symmetric] using pmono[OF \<open>i+1 \<le> j\<close>] by auto
          then show False using \<open>y < x + C/lambda\<close> by auto
        qed
      qed
    qed
    have npN: "next_in A (p N) = b'"
    proof (rule next_inI[OF A])
      show "p N \<in> {a..<b}" using pa pmono \<open>0 \<le> N\<close> \<open>p N < b\<close> by auto
      show "p N < b'" by fact
      show "b' \<in> A" unfolding A_def by auto
      show "{p N<..<b'} \<inter> A = {}"
        unfolding A_def using pmono b' by force
    qed
    have nb': "next_in A (b') = b"
    proof (rule next_inI[OF A])
      show "b' \<in> {a..<b}" using A_def A \<open>b' < b\<close> by auto
      show "b' < b" by fact
      show "b \<in> A" by fact
      show "{b'<..<b} \<inter> A = {}"
        unfolding A_def using pmono b' by force
    qed
    have gap: "next_in A x - x \<in> {C/lambda.. 3/2 * C/lambda}" if "x \<in> A - {b}" for x
    proof (cases "x = p N \<or> x = b'")
      case True
      then show ?thesis using npN nb' bpN b'_def by force
    next
      case False
      have *: "next_in A x = x + C/lambda"
        apply (rule nx) using that False by auto
      show ?thesis unfolding * using C by (auto simp add: algebra_simps divide_simps)
    qed

    text \<open>We can now define the function $d$, by geodesic interpolation between points in $A$.\<close>
    define d where "d x = (if x \<in> A then c x
        else geodesic_segment_param {c (prev_in A x) -- c (next_in A x)} (c (prev_in A x))
            ((x - prev_in A x)/(next_in A x - prev_in A x) * dist (c(prev_in A x)) (c(next_in A x))))" for x
    have "d a = c a" "d b = c b" unfolding d_def using \<open>a \<in> A\<close> \<open>b \<in> A\<close> by auto

    text \<open>To prove the Lipschitz continuity, we argue that $d$ is Lipschitz on finitely many intervals,
    that cover the interval $[a,b]$, the intervals between points in $A$.
    There is a formula for $d$ on them (the nontrivial point is that the above formulas for $d$
    match at the boundaries).\<close>

    have *: "d x = geodesic_segment_param {(c u)--(c v)} (c u) ((dist (c u) (c v) /(v-u)) * (x-u))"
      if "u \<in> A - {b}" "v = next_in A u" "x \<in> {u..v}" for x u v
    proof -
      have "u \<in> {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have H: "u \<in> A" "v \<in> A" "u < v" "A \<inter> {u<..<v} = {}" using that next_in_basics[OF A \<open>u \<in> {a..<b}\<close>] by auto
      consider "x = u" | "x = v" | "x \<in> {u<..<v}" using \<open>x \<in> {u..v}\<close> by fastforce
      then show ?thesis
      proof (cases)
        case 1
        then have "d x = c u" unfolding d_def using \<open>u \<in> A- {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        then show ?thesis unfolding 1 by auto
      next
        case 2
        then have "d x = c v" unfolding d_def using \<open>v \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        then show ?thesis unfolding 2 using \<open>u < v\<close> by auto
      next
        case 3
        have *: "prev_in A x = u"
          apply (rule prev_inI[OF A]) using 3 H \<open>A \<subseteq> {a..b}\<close> by auto
        have **: "next_in A x = v"
          apply (rule next_inI[OF A]) using 3 H \<open>A \<subseteq> {a..b}\<close> by auto
        show ?thesis unfolding d_def * ** using 3 H \<open>A \<inter> {u<..<v} = {}\<close> \<open>A \<subseteq> {a..b}\<close>
          by (auto simp add: algebra_simps)
      qed
    qed

    text \<open>From the above formula, we deduce that $d$ is Lipschitz on those intervals.\<close>
    have lip0: "(lambda + C / (next_in A u - u))-lipschitz_on {u..next_in A u} d" if "u \<in> A - {b}" for u
    proof -
      define v where "v = next_in A u"
      have "u \<in> {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have "u \<in> A" "v \<in> A" "u < v" "A \<inter> {u<..<v} = {}"
        unfolding v_def using that next_in_basics[OF A \<open>u \<in> {a..<b}\<close>] by auto

      have "(1 * (((lambda + C / (next_in A u - u))) * (1+0)))-lipschitz_on {u..v} (\<lambda>x. geodesic_segment_param {(c u)--(c v)} (c u) ((dist (c u) (c v) /(v-u)) * (x-u)))"
      proof (rule lipschitz_on_compose2[of _ _ "\<lambda>x. ((dist (c u) (c v) /(v-u)) * (x-u))"], intro lipschitz_intros)
        have "(\<lambda>x. dist (c u) (c v) / (v - u) * (x - u)) ` {u..v} \<subseteq> {0..dist (c u) (c v)}"
          apply auto using \<open>u < v\<close> by (auto simp add: algebra_simps divide_simps intro: mult_right_mono)
        moreover have "1-lipschitz_on {0..dist (c u) (c v)} (geodesic_segment_param {c u--c v} (c u))"
          by (rule isometry_on_lipschitz, simp)
        ultimately show "1-lipschitz_on ((\<lambda>x. dist (c u) (c v) / (v - u) * (x - u)) ` {u..v}) (geodesic_segment_param {c u--c v} (c u))"
          using lipschitz_on_subset by auto

        have "dist (c u) (c v) \<le> lambda * dist u v + C"
          apply (rule quasi_isometry_onD(1)[OF assms(1)])
          using \<open>u \<in> A\<close> \<open>v \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        also have "... = lambda * (v - u) + C"
          unfolding dist_real_def using \<open>u < v\<close> by auto
        finally show "\<bar>dist (c u) (c v) / (v - u)\<bar> \<le> lambda + C / (next_in A u - u)"
          using \<open>u < v\<close> unfolding v_def by (auto simp add: divide_simps)
      qed
      then show ?thesis
        using *[OF \<open>u \<in> A -{b}\<close> \<open>v = next_in A u\<close>] unfolding v_def
        by (auto intro: lipschitz_on_transform)
    qed
    have lip: "(2 * lambda)-lipschitz_on {u..next_in A u} d" if "u \<in> A - {b}" for u
    proof (rule lipschitz_on_mono[OF lip0[OF that]], auto)
      define v where "v = next_in A u"
      have "u \<in> {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have "u \<in> A" "v \<in> A" "u < v" "A \<inter> {u<..<v} = {}"
        unfolding v_def using that next_in_basics[OF A \<open>u \<in> {a..<b}\<close>] by auto
      have Duv: "v - u \<in> {C/lambda .. 2 * C/lambda}"
        unfolding v_def using gap[OF \<open>u \<in> A - {b}\<close>] by simp
      then show " C / (next_in A u - u) \<le> lambda"
        using \<open>u < v\<close> C unfolding v_def by (auto simp add: algebra_simps divide_simps)
    qed

    text \<open>The Lipschitz continuity of $d$ now follows from its Lipschitz continuity on each
    subinterval in $I$.\<close>
    have Lip: "(2 * lambda)-lipschitz_on {a..b} d"
      apply (rule lipschitz_on_closed_Union[of "{{u..next_in A u} |u. u \<in> A - {b}}" _ "\<lambda>x. x"])
      using lip \<open>finite A\<close> C intervals_decomposition[OF A] using assms by auto
    then have "continuous_on {a..b} d"
      using lipschitz_on_continuous_on by auto

    text \<open>$d$ has good upper controls on each basic interval.\<close>
    have QI0: "dist (d x) (d y) \<le> lambda * dist x y + C"
      if H: "u \<in> A - {b}" "x \<in> {u..next_in A u}" "y \<in> {u..next_in A u}" for u x y
    proof -
      have "u < next_in A u" using H(1) A next_in_basics(2)[OF A] by auto
      moreover have "dist x y \<le> next_in A u - u" unfolding dist_real_def using H by auto
      ultimately have *: "dist x y / (next_in A u - u) \<le> 1" by (simp add: divide_simps)
      have "dist (d x) (d y) \<le> (lambda + C / (next_in A u - u)) * dist x y"
        by (rule lipschitz_onD[OF lip0[OF H(1)] H(2) H(3)])
      also have "... = lambda * dist x y + C * (dist x y / (next_in A u - u))"
        by (simp add: algebra_simps)
      also have "... \<le> lambda * dist x y + C * 1"
        apply (intro mono_intros) using C * by auto
      finally show ?thesis by simp
    qed

    text \<open>We can now show that $c$ and $d$ are pointwise close. This follows from the fact that they
    coincide on $A$ and are well controlled in between (for $c$, this is a consequence of the choice
    of $A$. For $d$, it follows from the fact that it is geodesic in the intervals).\<close>

    have dist_c_d: "dist (c x) (d x) \<le> 4 * C" if "x \<in> {a..b}" for x
    proof -
      obtain u where u: "u \<in> A - {b}" "x \<in> {u..next_in A u}"
        using \<open>x \<in> {a..b}\<close> intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) \<le> 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u \<le> C/lambda" | "next_in A u - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>A. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v \<in> A" "dist x v \<le> C/lambda" by auto
      have "dist (c x) (d x) \<le> dist (c x) (c v) + dist (c v) (d v) + dist (d v) (d x)"
        by (intro mono_intros)
      also have "... \<le> (lambda * dist x v + C) + 0 + ((2 * lambda) * dist v x)"
        apply (intro mono_intros quasi_isometry_onD(1)[OF assms(1)] that lipschitz_onD[OF Lip])
        using A(2) \<open>v \<in> A\<close> apply blast
        using \<open>v \<in> A\<close> d_def apply auto[1]
        using A(2) \<open>v \<in> A\<close> by blast
      also have "... \<le> (lambda * (C/lambda) + C) + 0 + ((2 * lambda) * (C/lambda))"
        apply (intro mono_intros) using v(2) C by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis
        using C by (auto simp add: algebra_simps divide_simps)
    qed
    text \<open>A similar argument shows that the Hausdorff distance between the images is bounded by $2C$.\<close>
    have "hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C"
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 2 * C" using C by auto
      fix z assume "z \<in> c`{a..b}"
      then obtain x where x: "x \<in> {a..b}" "z = c x" by auto
      then obtain u where u: "u \<in> A - {b}" "x \<in> {u..next_in A u}"
        using intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) \<le> 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u \<le> C/lambda" | "next_in A u - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>A. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v \<in> A" "dist x v \<le> C/lambda" by auto
      have "dist z (d v) = dist (c x) (c v)" unfolding x(2) d_def using \<open>v \<in> A\<close> by auto
      also have "... \<le> lambda * dist x v + C"
        apply (rule quasi_isometry_onD(1)[OF assms(1)]) using v(1) A(2) x(1) by auto
      also have "... \<le> lambda * (C/lambda) + C"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (d v) \<le> 2 * C" by simp
      show "\<exists>y\<in>d ` {a..b}. dist z y \<le> 2 * C"
        apply (rule bexI[of _ "d v"]) using * v(1) A(2) by auto
    next
      fix z assume "z \<in> d`{a..b}"
      then obtain x where x: "x \<in> {a..b}" "z = d x" by auto
      then obtain u where u: "u \<in> A - {b}" "x \<in> {u..next_in A u}"
        using intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) \<le> 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u \<le> C/lambda" | "next_in A u - x \<le> C/lambda" by linarith
      then have "\<exists>v\<in>A. dist x v \<le> C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v \<in> A" "dist x v \<le> C/lambda" by auto
      have "dist z (c v) = dist (d x) (d v)" unfolding x(2) d_def using \<open>v \<in> A\<close> by auto
      also have "... \<le> 2 * lambda * dist x v"
        apply (rule lipschitz_onD(1)[OF Lip]) using v(1) A(2) x(1) by auto
      also have "... \<le> 2 * lambda * (C/lambda)"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (c v) \<le> 2 * C" by simp
      show "\<exists>y\<in>c`{a..b}. dist z y \<le> 2 * C"
        apply (rule bexI[of _ "c v"]) using * v(1) A(2) by auto
    qed

    text \<open>From the above controls, we check that $d$ is a quasi-isometry, with explicit constants.\<close>
    have "lambda (4 * C)-quasi_isometry_on {a..b} d"
    proof
      show "1 \<le> lambda" using C by auto
      show "0 \<le> 4 * C" using C by auto
      have I : "dist (d x) (d y) \<le> lambda * dist x y + 4 * C" if H: "x \<in> {a..b}" "y \<in> {a..b}" "x < y" for x y
      proof -
        obtain u where u: "u \<in> A - {b}" "x \<in> {u..next_in A u}"
          using intervals_decomposition[OF A] H(1) by force
        have "u \<in> {a..<b}" using u(1) A by auto
        have "next_in A u \<in> A" using next_in_basics(1)[OF A \<open>u \<in> {a..<b}\<close>] by auto
        obtain v where v: "v \<in> A - {b}" "y \<in> {v..next_in A v}"
          using intervals_decomposition[OF A] H(2) by force
        have "v \<in> {a..<b}" using v(1) A by auto
        have "u < next_in A v" using H(3) u(2) v(2) by auto
        then have "u \<le> v"
          using u(1) next_in_basics(3)[OF A, OF \<open>v \<in> {a..<b}\<close>] by auto
        show ?thesis
        proof (cases "u = v")
          case True
          have "dist (d x) (d y) \<le> lambda * dist x y + C"
            apply (rule QI0[OF u]) using v(2) True by auto
          also have "... \<le> lambda * dist x y + 4 * C"
            using C by auto
          finally show ?thesis by simp
        next
          case False
          then have "u < v" using \<open>u \<le> v\<close> by auto
          then have "next_in A u \<le> v" using v(1) next_in_basics(3)[OF A, OF \<open>u \<in> {a..<b}\<close>] by auto
          have d1: "d (next_in A u) = c (next_in A u)"
            using \<open>next_in A u \<in> A\<close> unfolding d_def by auto
          have d2: "d v = c v"
            using v(1) unfolding d_def by auto
          have "dist (d x) (d y) \<le> dist (d x) (d (next_in A u)) + dist (d (next_in A u)) (d v) + dist (d v) (d y)"
            by (intro mono_intros)
          also have "... \<le> (lambda * dist x (next_in A u) + C) + (lambda * dist (next_in A u) v + C)
                            + (lambda * dist v y + C)"
            apply (intro mono_intros)
              apply (rule QI0[OF u]) using u(2) apply simp
             apply (simp add: d1 d2) apply (rule quasi_isometry_onD(1)[OF assms(1)])
            using \<open>next_in A u \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> apply auto[1]
            using \<open>v \<in> A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> apply auto[1]
            apply (rule QI0[OF v(1)]) using v(2) by auto
          also have "... = lambda * dist x y + 3 * C"
            unfolding dist_real_def
            using \<open>x \<in> {u..next_in A u}\<close> \<open>y \<in> {v..next_in A v}\<close> \<open>x < y\<close> \<open>next_in A u \<le> v\<close>
            by (auto simp add: algebra_simps)
          finally show ?thesis using C by simp
        qed
      qed
      show "dist (d x) (d y) \<le> lambda * dist x y + 4 * C" if H: "x \<in> {a..b}" "y \<in> {a..b}" for x y
      proof -
        consider "x < y" | "x = y" | "x > y" by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis using I[OF H(1) H(2) 1] by simp
        next
          case 2
          show ?thesis unfolding 2 using C by auto
        next
          case 3
          show ?thesis using I [OF H(2) H(1) 3] by (simp add: metric_space_class.dist_commute)
        qed
      qed
      text \<open>The lower bound is more tricky. We separate the case where $x$ and $y$ are in the same
      interval, when they are in different nearby intervals, and when they are in different
      separated intervals. The latter case is more difficult. In this case, one of the intervals
      has length $C/\lambda$ and the other one has length at most $3/2\cdot C/\lambda$. There,
      we approximate $dist (d x) (d y)$ by $dist (d u') (d v')$ where $u'$ and $v'$ are suitable
      endpoints of the intervals containing respectively $x$ and $y$. We use the inner endpoint
      (between $x$ and $y$) if the distance between $x$ or $y$ and this point is less than $2/5$
      of the length of the interval, and the outer endpoint otherwise. The reason is that, with
      the outer endpoints, we get right away an upper bound for the distance between $x$ and $y$,
      while this is not the case with the inner endpoints where there is an additional error.
      The equilibrium is reached at proportion $2/5$. \<close>
      have J : "dist (d x) (d y) \<ge> (1/lambda) * dist x y - 4 * C" if H: "x \<in> {a..b}" "y \<in> {a..b}" "x < y" for x y
      proof -
        obtain u where u: "u \<in> A - {b}" "x \<in> {u..next_in A u}"
          using intervals_decomposition[OF A] H(1) by force
        have "u \<in> {a..<b}" using u(1) A by auto
        have "next_in A u \<in> A" using next_in_basics(1)[OF A \<open>u \<in> {a..<b}\<close>] by auto
        obtain v where v: "v \<in> A - {b}" "y \<in> {v..next_in A v}"
          using intervals_decomposition[OF A] H(2) by force
        have "v \<in> {a..<b}" using v(1) A by auto
        have "next_in A v \<in> A" using next_in_basics(1)[OF A \<open>v \<in> {a..<b}\<close>] by auto
        have "u < next_in A v" using H(3) u(2) v(2) by auto
        then have "u \<le> v"
          using u(1) next_in_basics(3)[OF A, OF \<open>v \<in> {a..<b}\<close>] by auto
        consider "v = u" | "v = next_in A u" | "v \<noteq> u \<and> v \<noteq> next_in A u" by auto
        then show ?thesis
        proof (cases)
          case 1
          have "(1/lambda) * dist x y - 4 * C \<le> lambda * dist x y - 4 * C"
            apply (intro mono_intros) by auto
          also have "... \<le> lambda * (3/2 * C/lambda) - 3/2 * C"
            apply (intro mono_intros)
            using u(2) v(2) unfolding 1 using C gap[OF u(1)] dist_real_def \<open>x < y\<close> by auto
          also have "... = 0"
            using C by auto
          also have "... \<le> dist (d x) (d y)"
            by auto
          finally show ?thesis by simp
        next
          case 2
          have "dist x y \<le> dist x (next_in A u) + dist v y"
            unfolding 2 by (intro mono_intros)
          also have "... \<le> 3/2 * C/lambda + 3/2 * C/lambda"
            apply (intro mono_intros)
            unfolding dist_real_def using u(2) v(2) gap[OF u(1)] gap[OF v(1)] by auto
          finally have *: "dist x y \<le> 3 * C/lambda" by auto
          have "(1/lambda) * dist x y - 4 * C \<le> lambda * dist x y - 4 * C"
            apply (intro mono_intros) by auto
          also have "... \<le> lambda * (3 * C/lambda) - 3 * C"
            apply (intro mono_intros)
            using * C by auto
          also have "... = 0"
            using C by auto
          also have "... \<le> dist (d x) (d y)"
            by auto
          finally show ?thesis by simp
        next
          case 3
          then have "u < v" using \<open>u \<le> v\<close> by auto
          then have *: "next_in A u < v" using v(1) next_in_basics(3)[OF A \<open>u \<in> {a..<b}\<close>] 3 by auto
          have nu: "next_in A u = u + C/lambda"
          proof (rule nx)
            show "u \<in> A" using u(1) by auto
            show "u \<noteq> b" using u(1) by auto
            show "u \<noteq> b'"
            proof
              assume H: "u = b'"
              have "b < v" using * unfolding H nb' by simp
              then show False using \<open>v \<in> {a..<b}\<close> by auto
            qed
            show "u \<noteq> p N"
            proof
              assume H: "u = p N"
              have "b' < v" using * unfolding H npN by simp
              then have "next_in A b' \<le> v" using next_in_basics(3)[OF A \<open>b' \<in> {a..<b}\<close>] v by force
              then show False unfolding nb' using \<open>v \<in> {a..<b}\<close> by auto
            qed
          qed
          have nv: "next_in A v \<le> v + 3/2 * C/lambda" using gap[OF v(1)] by auto

          have d: "d u = c u" "d (next_in A u) = c (next_in A u)" "d v = c v" "d (next_in A v) = c (next_in A v)"
            using \<open>u \<in> A - {b}\<close> \<open>next_in A u \<in> A\<close> \<open>v \<in> A - {b}\<close> \<open>next_in A v \<in> A\<close> unfolding d_def by auto

          text \<open>The interval containing $x$ has length $C/\lambda$, while the interval containing
          $y$ has length at most $\leq 3/2 C/\lambda$. Therefore, $x$ is at proportion $2/5$ of the inner point
          if $x > u + (3/5) C/\lambda$, and $y$ is at proportion $2/5$ of the inner point if
          $y < v + (2/5) \cdot 3/2 \cdot C/\lambda = v + (3/5)C/\lambda$.\<close>
          consider "x \<le> u + (3/5) * C/lambda \<and> y \<le> v + (3/5) * C/lambda"
                 | "x \<ge> u + (3/5) * C/lambda \<and> y \<le> v + (3/5) * C/lambda"
                 | "x \<le> u + (3/5) * C/lambda \<and> y \<ge> v + (3/5) * C/lambda"
                 | "x \<ge> u + (3/5) * C/lambda \<and> y \<ge> v + (3/5) * C/lambda"
            by linarith
          then show ?thesis
          proof (cases)
            case 1
            have "(1/lambda) * dist u v - C \<le> dist (c u) (c v)"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>u \<in> A - {b}\<close> \<open>v \<in> A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d u) (d v)"
              using d by auto
            also have "... \<le> dist (d u) (d x) + dist (d x) (d y) + dist (d y) (d v)"
              by (intro mono_intros)
            also have "... \<le> (2 * lambda * dist u x) + dist (d x) (d y) + (2 * lambda * dist y v)"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... \<le> (2 * lambda * (3/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 1 u v C by auto
            also have "... = 12/5 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist u v \<le> dist (d x) (d y) + 17/5 * C" by auto

            have "(1/lambda) * dist x y \<le> (1/lambda) * (dist u v + dist v y)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... \<le> (1/lambda) * (dist u v + 3/5 * C/lambda)"
              apply (intro mono_intros)
              unfolding dist_real_def using 1 v(2) C by auto
            also have "... = (1/lambda) * dist u v + 3/5 * C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... \<le> (1/lambda) * dist u v + 3/5 * C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... \<le> (dist (d x) (d y) + 17/5 * C) + 3/5 * C * 1"
              using * by auto
            finally show ?thesis by auto
          next
            case 2
            have "(1/lambda) * dist (next_in A u) v - C \<le> dist (c (next_in A u)) (c v)"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>next_in A u \<in> A\<close> \<open>v \<in> A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d (next_in A u)) (d v)"
              using d by auto
            also have "... \<le> dist (d (next_in A u)) (d x) + dist (d x) (d y) + dist (d y) (d v)"
              by (intro mono_intros)
            also have "... \<le> (2 * lambda * dist (next_in A u) x) + dist (d x) (d y) + (2 * lambda * dist y v)"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... \<le> (2 * lambda * (2/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 2 u v C nu by auto
            also have "... = 2 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist (next_in A u) v \<le> dist (d x) (d y) + 3 * C" by auto

            have "(1/lambda) * dist x y \<le> (1/lambda) * (dist x (next_in A u) + dist (next_in A u) v + dist v y)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... \<le> (1/lambda) * ((2/5 * C/lambda) + dist (next_in A u) v  + (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 2 u(2) v(2) C nu by auto
            also have "... = (1/lambda) * dist (next_in A u) v + C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... \<le> (1/lambda) * dist (next_in A u) v + C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... \<le> (dist (d x) (d y) + 3 * C) + C * 1"
              using * by auto
            finally show ?thesis by auto
          next
            case 3
            have "(1/lambda) * dist u (next_in A v) - C \<le> dist (c u) (c (next_in A v))"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>u \<in> A - {b}\<close> \<open>next_in A v \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d u) (d (next_in A v))"
              using d by auto
            also have "... \<le> dist (d u) (d x) + dist (d x) (d y) + dist (d y) (d (next_in A v))"
              by (intro mono_intros)
            also have "... \<le> (2 * lambda * dist u x) + dist (d x) (d y) + (2 * lambda * dist y (next_in A v))"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... \<le> (2 * lambda * (3/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (9/10 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 3 u v C nv by auto
            also have "... = 3 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist u (next_in A v) \<le> dist (d x) (d y) + 4 * C" by auto

            have "(1/lambda) * dist x y \<le> (1/lambda) * dist u (next_in A v)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... \<le> dist (d x) (d y) + 4 * C"
              using * by auto
            finally show ?thesis by auto
          next
            case 4
            have "(1/lambda) * dist (next_in A u) (next_in A v) - C \<le> dist (c (next_in A u)) (c (next_in A v))"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>next_in A u \<in> A\<close> \<open>next_in A v \<in> A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d (next_in A u)) (d (next_in A v))"
              using d by auto
            also have "... \<le> dist (d (next_in A u)) (d x) + dist (d x) (d y) + dist (d y) (d (next_in A v))"
              by (intro mono_intros)
            also have "... \<le> (2 * lambda * dist (next_in A u) x) + dist (d x) (d y) + (2 * lambda * dist y (next_in A v))"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... \<le> (2 * lambda * (2/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (9/10 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 4 u v C nu nv by auto
            also have "... = 13/5 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist (next_in A u) (next_in A v) \<le> dist (d x) (d y) + 18/5 * C" by auto

            have "(1/lambda) * dist x y \<le> (1/lambda) * (dist x (next_in A u) + dist (next_in A u) (next_in A v))"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... \<le> (1/lambda) * ((2/5 *C/lambda) + dist (next_in A u) (next_in A v))"
              apply (intro mono_intros)
              unfolding dist_real_def using 4 u(2) v(2) C nu by auto
            also have "... = (1/lambda) * dist (next_in A u) (next_in A v) + 2/5 * C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... \<le> (1/lambda) * dist (next_in A u) (next_in A v) + 2/5 * C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... \<le> (dist (d x) (d y) + 18/5 * C) + 2/5 * C * 1"
              using * by auto
            finally show ?thesis by auto
          qed
        qed
      qed
      show "dist (d x) (d y) \<ge> (1/lambda) * dist x y - 4 * C" if H: "x \<in> {a..b}" "y \<in> {a..b}" for x y
      proof -
        consider "x < y" | "x = y" | "x > y" by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis using J[OF H(1) H(2) 1] by simp
        next
          case 2
          show ?thesis unfolding 2 using C by auto
        next
          case 3
          show ?thesis using J[OF H(2) H(1) 3] by (simp add: metric_space_class.dist_commute)
        qed
      qed
    qed

    text \<open>We have proved that $d$ has all the properties we wanted.\<close>
    then have "continuous_on {a..b} d \<and> d a = c a \<and> d b = c b
          \<and> lambda (4 * C)-quasi_isometry_on {a..b} d
          \<and> (\<forall>x\<in>{a..b}. dist (c x) (d x) \<le> 4 *C)
          \<and> (2*lambda)-lipschitz_on {a..b} d
          \<and> hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C"
      using dist_c_d \<open>continuous_on {a..b} d\<close> \<open>d a = c a\<close> \<open>d b = c b\<close> \<open>(2*lambda)-lipschitz_on {a..b} d\<close>
            \<open>hausdorff_distance (c`{a..b}) (d`{a..b}) \<le> 2 * C\<close> by auto
    then show ?thesis by auto
  qed
qed

end (*of theory Isometries*)
