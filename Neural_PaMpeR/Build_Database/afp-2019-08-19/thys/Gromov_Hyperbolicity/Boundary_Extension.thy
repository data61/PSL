(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Boundary_Extension
  imports Morse_Gromov_Theorem Gromov_Boundary
begin

section \<open>Extension of quasi-isometries to the boundary\<close>

text \<open>In this section, we show that a quasi-isometry between geodesic Gromov hyperbolic spaces
extends to a homeomorphism between their boundaries.\<close>

text \<open>Applying a quasi-isometry on a geodesic triangle essentially sends it to a geodesic triangle,
in hyperbolic spaces. It follows that, up to an additive constant, the Gromov product, which is the
distance to the center of the triangle, is multiplied by a constant between $\lambda^{-1}$ and
$\lambda$ when one applies a quasi-isometry. This argument is given in the next lemma. This implies
that two points are close in the Gromov completion if and only if their images are also close in the
Gromov completion of the image. Essentially, this lemma implies that a quasi-isometry has a
continuous extension to the Gromov boundary, which is a homeomorphism.\<close>

lemma Gromov_product_at_quasi_isometry:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_product_at (f x) (f y) (f z) \<ge> Gromov_product_at x y z / lambda - 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
        "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
proof -
  have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
  define D where "D = 92 * lambda^2 * (C + deltaG(TYPE('b)))"
  have Dxy: "hausdorff_distance (f`{x--y}) {f x--f y} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto
  have Dyz: "hausdorff_distance (f`{y--z}) {f y--f z} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto
  have Dxz: "hausdorff_distance (f`{x--z}) {f x--f z} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto

  define E where "E = (lambda * (4 * deltaG(TYPE('a))) + C) + D"
  have "E \<ge> 0" unfolding E_def D_def using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
  obtain w where w: "infdist w {x--y} \<le> 4 * deltaG(TYPE('a))"
                    "infdist w {x--z} \<le> 4 * deltaG(TYPE('a))"
                    "infdist w {y--z} \<le> 4 * deltaG(TYPE('a))"
                    "dist w x = Gromov_product_at x y z"
    using slim_triangle[of "{x--y}" x y "{x--z}" z "{y--z}"] by auto
  have "infdist (f w) {f x--f y} \<le> infdist (f w) (f`{x--y}) + hausdorff_distance (f`{x--y}) {f x--f y}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{x--y}"], auto)
  also have "... \<le> (lambda * infdist w {x--y} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dxy by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Exy: "infdist (f w) {f x--f y} \<le> E" unfolding E_def by auto

  have "infdist (f w) {f y--f z} \<le> infdist (f w) (f`{y--z}) + hausdorff_distance (f`{y--z}) {f y--f z}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{y--z}"], auto)
  also have "... \<le> (lambda * infdist w {y--z} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dyz by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Eyz: "infdist (f w) {f y--f z} \<le> E" unfolding E_def by auto

  have "infdist (f w) {f x--f z} \<le> infdist (f w) (f`{x--z}) + hausdorff_distance (f`{x--z}) {f x--f z}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{x--z}"], auto)
  also have "... \<le> (lambda * infdist w {x--z} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dxz by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Exz: "infdist (f w) {f x--f z} \<le> E" unfolding E_def by auto

  have "2 * ((1/lambda * dist w x - C)) \<le> 2 * dist (f w) (f x)"
    using quasi_isometry_onD(2)[OF assms(1), of w x] by auto
  also have "... = (dist (f w) (f x) + dist (f w) (f y)) + (dist (f w) (f x) + dist (f w) (f z)) - (dist (f w) (f y) + dist (f w) (f z))"
    by auto
  also have "... \<le> (dist (f x) (f y) + 2 * infdist (f w) {f x--f y}) + (dist (f x) (f z) + 2 * infdist (f w) {f x--f z}) - dist (f y) (f z)"
    by (intro geodesic_segment_distance mono_intros, auto)
  also have "... \<le> 2 * Gromov_product_at (f x) (f y) (f z) + 4 * E"
    unfolding Gromov_product_at_def using Exy Exz by (auto simp add: algebra_simps divide_simps)
  finally have *: "Gromov_product_at x y z / lambda - C - 2 * E \<le> Gromov_product_at (f x) (f y) (f z)"
    unfolding w(4) by simp

  have "2 * Gromov_product_at (f x) (f y) (f z) - 2 * E \<le> 2 * Gromov_product_at (f x) (f y) (f z) - 2 * infdist (f w) {f y--f z}"
    using Eyz by auto
  also have "... = dist (f x) (f y) + dist (f x) (f z) - (dist (f y) (f z) + 2 * infdist (f w) {f y--f z})"
    unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
  also have "... \<le> (dist (f w) (f x) + dist (f w) (f y)) + (dist (f w) (f x) + dist (f w) (f z)) - (dist (f w) (f y) + dist (f w) (f z))"
    by (intro geodesic_segment_distance mono_intros, auto)
  also have "... = 2 * dist (f w) (f x)"
    by auto
  also have "... \<le> 2 * (lambda * dist w x + C)"
    using quasi_isometry_onD(1)[OF assms(1), of w x] by auto
  finally have "Gromov_product_at (f x) (f y) (f z) \<le> lambda * dist w x + C + E"
    by auto
  then have **: "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + C + 2 * E"
    unfolding w(4) using \<open>E \<ge> 0\<close> by auto

  have "C + 2 * E = 3 * 1 * C + 8 * lambda * deltaG(TYPE('a)) + 184 * lambda^2 * C + 184 * lambda^2 * deltaG(TYPE('b))"
    unfolding E_def D_def by (auto simp add: algebra_simps)
  also have "... \<le> 3 * lambda^2 * C + 187 * lambda^2 * deltaG(TYPE('a)) + 184 * lambda^2 * C + 187 * lambda^2 * deltaG(TYPE('b))"
    apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
  finally have I: "C + 2 * E \<le> 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
    by (auto simp add: algebra_simps)

  show "Gromov_product_at (f x) (f y) (f z) \<ge> Gromov_product_at x y z / lambda - 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
    using * I by auto
  show "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
    using ** I by auto
qed

lemma Gromov_converging_at_infinity_quasi_isometry:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_converging_at_boundary (\<lambda>n. f (u n)) \<longleftrightarrow> Gromov_converging_at_boundary u"
proof
  assume "Gromov_converging_at_boundary u"
  show "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
  proof (rule Gromov_converging_at_boundaryI[of "f (basepoint)"])
    have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
    define D where "D = 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
    fix M::real
    obtain M2::real where M2: "M = M2/lambda - D"
      using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at basepoint (u m) (u n) \<ge> M2"
      using \<open>Gromov_converging_at_boundary u\<close> unfolding Gromov_converging_at_boundary_def by blast
    have "Gromov_product_at (f basepoint) (f (u m)) (f (u n)) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
    proof -
      have "M \<le> Gromov_product_at basepoint (u m) (u n)/lambda - D"
        unfolding M2 using N[OF that] \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
      also have "... \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
        unfolding D_def by (rule Gromov_product_at_quasi_isometry[OF assms(1)])
      finally show ?thesis by simp
    qed
    then show "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. M \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
      unfolding comp_def by auto
  qed
next
  assume "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
  show "Gromov_converging_at_boundary u"
  proof (rule Gromov_converging_at_boundaryI[of "basepoint"])
    have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
    define D where "D = 187 * lambda^2 * (C + deltaG(TYPE('a)) + deltaG(TYPE('b)))"
    fix M::real
    define M2 where "M2 = lambda * M + D"
    have M2: "M = (M2 - D)/lambda" unfolding M2_def using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at (f basepoint) (f (u m)) (f (u n)) \<ge> M2"
      using \<open>Gromov_converging_at_boundary (\<lambda>n. f (u n))\<close> unfolding Gromov_converging_at_boundary_def by blast
    have "Gromov_product_at basepoint (u m) (u n) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
    proof -
      have "M2 \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
        using N[OF that] by auto
      also have "... \<le> lambda * Gromov_product_at basepoint (u m) (u n) + D"
        unfolding D_def by (rule Gromov_product_at_quasi_isometry[OF assms(1)])
      finally show "M \<le> Gromov_product_at basepoint (u m) (u n)"
        unfolding M2 using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    qed
    then show "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. Gromov_product_at basepoint (u m) (u n) \<ge> M"
      by auto
  qed
qed

text \<open>We define the extension to the completion of a function $f: X \to Y$ where $X$ and $Y$
are geodesic Gromov-hyperbolic spaces, as a function from $X \cup \partial X$ to $Y\cup \partial Y$,
as follows. If $x$ is in the space, we just use $f(x)$ (with the suitable coercions for the
definition). Otherwise, we wish to define $f(x)$ as the limit of $f(u_n)$ for all sequences tending
to $x$. For the definition, we use one such sequence chosen arbitrarily (this is the role of
\verb+rep_Gromov_completion x+ below, it is indeed a sequence in the space tending to $x$), and
we use the limit of $f(u_n)$ (if it exists, otherwise the framework will choose some point for us
but it will make no sense whatsoever).

For quasi-isometries, we have indeed that $f(u_n)$ converges if $u_n$ converges to a boundary point,
by \verb+Gromov_converging_at_infinity_quasi_isometry+, so this definition is meaningful. Moreover,
continuity of the extension follows readily from this (modulo a suitable criterion for continuity
based on sequences convergence, established in \verb+continuous_at_extension_sequentially'+).\<close>

definition Gromov_extension::"('a::Gromov_hyperbolic_space \<Rightarrow> 'b::Gromov_hyperbolic_space) \<Rightarrow> ('a Gromov_completion \<Rightarrow> 'b Gromov_completion)"
  where "Gromov_extension f x = (if x \<in> Gromov_boundary then lim (to_Gromov_completion o f o (rep_Gromov_completion x))
                                 else to_Gromov_completion (f (from_Gromov_completion x)))"

lemma Gromov_extension_inside_space [simp]:
  "Gromov_extension f (to_Gromov_completion x) = to_Gromov_completion (f x)"
unfolding Gromov_extension_def by auto

lemma Gromov_extension_id [simp]:
  "Gromov_extension (id::'a::Gromov_hyperbolic_space \<Rightarrow> 'a) = id"
  "Gromov_extension (\<lambda>x::'a. x) = (\<lambda>x. x)"
proof -
  have "Gromov_extension id x = id x" for x::"'a Gromov_completion"
    unfolding Gromov_extension_def comp_def
    using limI rep_Gromov_completion_limit by (auto simp add: to_from_Gromov_completion)
  then show "Gromov_extension (id::'a \<Rightarrow> 'a) = id"
    by auto
  then show "Gromov_extension (\<lambda>x::'a. x) = (\<lambda>x. x)"
    unfolding id_def by auto
qed

text \<open>The Gromov extension of a quasi-isometric map sends the boundary to the boundary.\<close>

lemma Gromov_extension_quasi_isometry_boundary_to_boundary:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "x \<in> Gromov_boundary"
  shows "(Gromov_extension f) x \<in> Gromov_boundary"
proof -
  have *: "Gromov_converging_at_boundary (\<lambda>n. f (rep_Gromov_completion x n))"
    by (simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)] Gromov_boundary_rep_converging assms(2))
  show ?thesis
    unfolding Gromov_extension_def using assms(2) unfolding comp_def apply auto
    by (metis Gromov_converging_at_boundary_converges * limI)
qed

text \<open>If the original function is continuous somewhere inside the space, then its Gromov extension
is continuous at the corresponding point inside the completion. This is clear as the original space
is open in the Gromov completion, but the proof requires to go back and forth between one space
and the other.\<close>

lemma Gromov_extension_continuous_inside:
  fixes f::"'a::Gromov_hyperbolic_space \<Rightarrow> 'b::Gromov_hyperbolic_space"
  assumes "continuous (at x within S) f"
  shows "continuous (at (to_Gromov_completion x) within (to_Gromov_completion`S)) (Gromov_extension f)"
proof -
  have *: "continuous (at (to_Gromov_completion x) within (to_Gromov_completion`S)) (to_Gromov_completion o f o from_Gromov_completion)"
    apply (intro continuous_within_compose, auto)
    using from_Gromov_completion_continuous(3) continuous_at_imp_continuous_within apply blast
    using assms apply (simp add: continuous_within_topological)
    using continuous_at_imp_continuous_within continuous_on_eq_continuous_within to_Gromov_completion_continuous by blast
  have "(to_Gromov_completion o f o from_Gromov_completion) y = Gromov_extension f y"
    if "y \<in> range to_Gromov_completion" for y
    unfolding comp_def using that by auto
  moreover have "eventually (\<lambda>y. y \<in> range to_Gromov_completion) (at (to_Gromov_completion x) within (to_Gromov_completion`S))"
    using to_Gromov_completion_range_open eventually_at_topological by blast
  ultimately have **: "eventually (\<lambda>y. (to_Gromov_completion o f o from_Gromov_completion) y = Gromov_extension f y)
                        (at (to_Gromov_completion x) within (to_Gromov_completion`S))"
    by (rule eventually_mono[rotated])
  show ?thesis
    by (rule continuous_within_cong[OF * **], auto)
qed

text \<open>The extension to the boundary of a quasi-isometry is continuous. This is a nontrivial
statement, but it follows readily from the fact we have already proved that sequences converging
at the boundary are mapped to sequences converging to the boundary. The proof is expressed using
a convenient continuity criterion for which we only need to control what happens for sequences
inside the space.\<close>

proposition Gromov_extension_continuous:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "x \<in> Gromov_boundary"
  shows "continuous (at x) (Gromov_extension f)"
proof -
  have "continuous (at x within (range to_Gromov_completion \<union> Gromov_boundary)) (Gromov_extension f)"
  proof (rule continuous_at_extension_sequentially'[OF \<open>x \<in> Gromov_boundary\<close>])
    fix b::"'a Gromov_completion" assume "b \<in> Gromov_boundary"
    show "\<exists>u. (\<forall>n. u n \<in> range to_Gromov_completion) \<and> u \<longlonglongrightarrow> b \<and> (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f b"
      apply (rule exI[of _ "to_Gromov_completion o (rep_Gromov_completion b)"], auto simp add: comp_def)
      unfolding Gromov_completion_converge_to_boundary[OF \<open>b \<in> Gromov_boundary\<close>]
      using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] apply auto[1]
      unfolding Gromov_extension_def using \<open>b \<in> Gromov_boundary\<close> unfolding comp_def
      by (auto simp add: convergent_LIMSEQ_iff[symmetric] Gromov_boundary_rep_converging Gromov_converging_at_infinity_quasi_isometry[OF assms(1)]
               intro!: Gromov_converging_at_boundary_converges')
  next
    fix u and b::"'a Gromov_completion"
    assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "b \<in> Gromov_boundary" "u \<longlonglongrightarrow> b"
    define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
    have v: "u n = to_Gromov_completion (v n)" for n
      using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)

    show "convergent (\<lambda>n. Gromov_extension f (u n))"
      using u unfolding v
      apply (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)])
      using Gromov_boundary_abs_converging Gromov_completion_converge_to_boundary by blast
  qed
  then show ?thesis by (simp add: Gromov_boundary_def)
qed

text \<open>Combining the two previous statements on continuity inside the space and continuity at the
boundary, we deduce that a continuous quasi-isometry extends to a continuous map everywhere.\<close>

proposition Gromov_extension_continuous_everywhere:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "continuous_on UNIV f"
  shows "continuous_on UNIV (Gromov_extension f)"
using Gromov_extension_continuous_inside Gromov_extension_continuous[OF assms(1)]
by (metis UNIV_I assms(2) continuous_on_eq_continuous_within continuous_within_open not_in_Gromov_boundary rangeI to_Gromov_completion_range_open)

text \<open>The extension to the boundary is functorial on the category of quasi-isometries, i.e., the
composition of extensions is the extension of the composition. This is clear inside the space, and
it follows from the continuity at boundary points.\<close>

lemma Gromov_extension_composition:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
    and g::"'b::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'c::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "mu D-quasi_isometry g"
  shows "Gromov_extension (g o f) = Gromov_extension g o Gromov_extension f"
proof -
  have In: "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" if H: "x \<in> range to_Gromov_completion" for x
  proof -
    obtain y where *: "x = to_Gromov_completion y"
      using H by auto
    show ?thesis
      unfolding * comp_def by auto
  qed
  moreover have "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" if H: "x \<in> Gromov_boundary" for x
  proof -
    obtain u where u: "\<And>n. u n \<in> range to_Gromov_completion" "u \<longlonglongrightarrow> x"
      using closure_sequential to_Gromov_completion_range_dense by blast
    have "(\<lambda>n. Gromov_extension (g o f) (u n)) \<longlonglongrightarrow> Gromov_extension (g o f) x"
      using continuous_within_tendsto_compose[OF Gromov_extension_continuous[OF quasi_isometry_on_compose[OF assms(1) assms(2), simplified] H] _ u(2)] by simp
    then have A: "(\<lambda>n. (Gromov_extension g) ((Gromov_extension f) (u n))) \<longlonglongrightarrow> Gromov_extension (g o f) x"
      unfolding In[OF u(1)] unfolding comp_def by auto

    have *: "(\<lambda>n. (Gromov_extension f) (u n)) \<longlonglongrightarrow> (Gromov_extension f) x"
      using continuous_within_tendsto_compose[OF Gromov_extension_continuous[OF assms(1) H] _ u(2)] by simp
    have "(\<lambda>n. (Gromov_extension g) ((Gromov_extension f) (u n))) \<longlonglongrightarrow> Gromov_extension g ((Gromov_extension f) x)"
      using continuous_within_tendsto_compose[OF Gromov_extension_continuous[OF assms(2)] _ *]
      H Gromov_extension_quasi_isometry_boundary_to_boundary assms(1) by auto
    then show ?thesis using LIMSEQ_unique A comp_def by auto
  qed
  ultimately have "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" for x
    using not_in_Gromov_boundary by force
  then show ?thesis by auto
qed

text \<open>Now, we turn to the same kind of statement, but for homeomorphisms. We claim that if a
quasi-isometry $f$ is a homeomorphism on a subset $X$ of the space, then its extension is a
homeomorphism on $X$ union the boundary of the space.
For the proof, we have to show that a sequence $u_n$ tends to a point $x$
if and only if $f(u_n)$ tends to $f(x)$. We separate the cases $x$ in the boundary, and $x$ inside
the space. For $x$ in the boundary, we use a homeomorphism criterion expressed solely in terms
of sequences converging to the boundary, for which we already know everything.
For $x$ in the space, the proof is straightforward, but tedious.
We argue that eventually $u_n$ is in the space for the direct implication, or $f(u_n)$ is in the
space for the second implication, and then we use that $f$ is a homeomorphism inside the space to
conclude.\<close>

lemma Gromov_extension_homeomorphism:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "homeomorphism_on X f"
  shows "homeomorphism_on (to_Gromov_completion`X \<union> Gromov_boundary) (Gromov_extension f)"
proof (rule homeomorphism_on_sequentially)
  fix x u assume H0: "x \<in> to_Gromov_completion ` X \<union> Gromov_boundary"
                    "\<forall>n::nat. u n \<in> to_Gromov_completion ` X \<union> Gromov_boundary"
  then consider "x \<in> Gromov_boundary" | "x \<in> to_Gromov_completion`X" by auto
  then show "u \<longlonglongrightarrow> x = (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
  proof (cases)
    text \<open>First, consider the case where the limit point $x$ is in the boundary. We use a good
    criterion expressing everything in terms of sequences inside the space.\<close>
    case 1
    show ?thesis
    proof (rule homeomorphism_on_extension_sequentially_precise[of "range to_Gromov_completion" Gromov_boundary])
      show "x \<in> Gromov_boundary" by fact
      fix n::nat show "u n \<in> range to_Gromov_completion \<union> Gromov_boundary"
        unfolding Gromov_boundary_def by auto
    next
      fix u and b::"'a Gromov_completion"
      assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "b \<in> Gromov_boundary" "u \<longlonglongrightarrow> b"
      define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
      have v: "u n = to_Gromov_completion (v n)" for n
        using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)
      show "convergent (\<lambda>n. Gromov_extension f (u n))"
        using u unfolding v apply auto
        apply (rule Gromov_converging_at_boundary_converges')
        by (auto simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)] lim_imp_Gromov_converging_at_boundary)
    next
      fix u c
      assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "c \<in> Gromov_extension f ` Gromov_boundary" "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> c"
      then have "c \<in> Gromov_boundary" using Gromov_extension_quasi_isometry_boundary_to_boundary[OF assms(1)] by auto
      define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
      have v: "u n = to_Gromov_completion (v n)" for n
        using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)
      have "Gromov_converging_at_boundary (\<lambda>n. f (v n))"
        apply (rule lim_imp_Gromov_converging_at_boundary[OF _ \<open>c \<in> Gromov_boundary\<close>])
        using u(3) unfolding v by auto
      then show "convergent u"
        using u unfolding v
        by (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1), symmetric])
    next
      fix b::"'a Gromov_completion" assume "b \<in> Gromov_boundary"
      show "\<exists>u. (\<forall>n. u n \<in> range to_Gromov_completion) \<and> u \<longlonglongrightarrow> b \<and> (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f b"
        apply (rule exI[of _ "to_Gromov_completion o (rep_Gromov_completion b)"], auto simp add: comp_def)
        unfolding Gromov_completion_converge_to_boundary[OF \<open>b \<in> Gromov_boundary\<close>]
        using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] apply auto[1]
        unfolding Gromov_extension_def using \<open>b \<in> Gromov_boundary\<close> unfolding comp_def
        by (auto simp add: convergent_LIMSEQ_iff[symmetric] Gromov_boundary_rep_converging Gromov_converging_at_infinity_quasi_isometry[OF assms(1)]
                 intro!: Gromov_converging_at_boundary_converges')
    qed
  next
    text \<open>Next, consider the case where $x$ is inside the space. Then we show everything by going
    back and forth between the original space and its copy in the completion, and arguing that $f$
    is a homeomorphism on the original space.\<close>
    case 2
    then have fx: "Gromov_extension f x \<in> range to_Gromov_completion"
      using Gromov_extension_inside_space by blast
    have x: "x \<in> range to_Gromov_completion"
      using "2" by blast
    show ?thesis
    proof
      assume H: "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
      then have fu_in: "eventually (\<lambda>n. Gromov_extension f (u n) \<in> range to_Gromov_completion) sequentially"
        using fx to_Gromov_completion_range_open H topological_tendstoD by fastforce
      have u_in: "eventually (\<lambda>n. u n \<in> range to_Gromov_completion) sequentially"
        using Gromov_extension_quasi_isometry_boundary_to_boundary[OF assms(1)] eventually_mono[OF fu_in]
        by (metis DiffE DiffI Gromov_boundary_def iso_tuple_UNIV_I)

      have B: "from_Gromov_completion (Gromov_extension f y) = f (from_Gromov_completion y)" if "Gromov_extension f y \<in> range to_Gromov_completion" for y
        by (metis Gromov_extension_quasi_isometry_boundary_to_boundary Gromov_extension_def assms(1) from_to_Gromov_completion not_in_Gromov_boundary' rangeE that)
      have "(\<lambda>n. from_Gromov_completion (Gromov_extension f (u n))) \<longlonglongrightarrow> from_Gromov_completion (Gromov_extension f x)"
        by (rule continuous_on_tendsto_compose[OF from_Gromov_completion_continuous(2) H fx fu_in])
      then have C: "(\<lambda>n. f (from_Gromov_completion (u n))) \<longlonglongrightarrow> f (from_Gromov_completion x)"
        unfolding B[OF fx, symmetric] apply (rule Lim_transform_eventually[rotated]) using eventually_mono[OF fu_in B] by auto
      have "(\<lambda>n. from_Gromov_completion (u n)) \<longlonglongrightarrow> from_Gromov_completion x"
        apply (rule iffD2[OF homeomorphism_on_compose[OF assms(2)] C])
        using 2 apply auto
        by (metis (no_types, lifting) eventually_mono[OF u_in] H0(2) Un_iff f_inv_into_f from_to_Gromov_completion inv_into_into not_in_Gromov_boundary')
      then have L: "(\<lambda>n. to_Gromov_completion (from_Gromov_completion (u n))) \<longlonglongrightarrow> to_Gromov_completion (from_Gromov_completion x)"
        using continuous_on_tendsto_compose[OF to_Gromov_completion_continuous] by auto

      have **: "to_Gromov_completion (from_Gromov_completion y) = y" if "y \<in> range to_Gromov_completion" for y::"'a Gromov_completion"
        using Gromov_extension_quasi_isometry_boundary_to_boundary assms(1) that to_from_Gromov_completion by fastforce
      then have "eventually (\<lambda>n. to_Gromov_completion (from_Gromov_completion (u n)) = u n) sequentially"
        using u_in eventually_mono by force
      then have "u \<longlonglongrightarrow> to_Gromov_completion (from_Gromov_completion x)"
        by (rule Lim_transform_eventually[OF _ L])
      then show "u \<longlonglongrightarrow> x"
        using ** by (simp add: x)
    next
      assume "u \<longlonglongrightarrow> x"
      then have u_in: "eventually (\<lambda>n. u n \<in> range to_Gromov_completion) sequentially"
        using x to_Gromov_completion_range_open topological_tendstoD by fastforce
      define y where "y = from_Gromov_completion x"
      have "y \<in> X" unfolding y_def using 2 by auto
      then have *: "continuous (at y within X) f"
        using homeomorphism_on_continuous[OF assms(2)] continuous_on_eq_continuous_within by blast
      have **: "continuous (at x within to_Gromov_completion`X) (Gromov_extension f)"
        using Gromov_extension_continuous_inside[OF *] y_def 2 by auto

      show "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
        apply (rule continuous_within_tendsto_compose[OF ** _ \<open>u \<longlonglongrightarrow> x\<close>])
        using u_in H0(2) by (metis (mono_tags, lifting) UnE eventually_mono f_inv_into_f not_in_Gromov_boundary')
    qed
  qed
qed

text \<open>In particular, it follows that the extension to the boundary of a quasi-isometry is always
a homeomorphism, regardless of the continuity properties of the original map.\<close>

proposition Gromov_extension_boundary_homeomorphism:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "homeomorphism_on Gromov_boundary (Gromov_extension f)"
using Gromov_extension_homeomorphism[OF assms, of "{}"] by auto

text \<open>When the quasi-isometric embedding is a quasi-isometric isomorphism, i.e., it is onto up
to a bounded distance $C$, then its Gromov extension is onto on the boundary. Indeed, a point
in the image boundary is a limit of a sequence inside the space. Perturbing by a bounded distance
(which does not change the asymptotic behavior), it is the limit of a sequence inside the image of
$f$. Then the preimage under $f$ of this sequence does converge, and its limit is sent by the
extension on the original point, proving the surjectivity.\<close>

lemma Gromov_extension_onto:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
          "y \<in> Gromov_boundary"
  shows "\<exists>x \<in> Gromov_boundary. Gromov_extension f x = y"
proof -
  define u where "u = rep_Gromov_completion y"
  have *: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> y"
    unfolding u_def using rep_Gromov_completion_limit by fastforce
  have "\<exists>v. \<forall>n. dist (f (v n)) (u n) \<le> C"
    apply (intro choice) using quasi_isometry_betweenD(3)[OF assms(1)] by auto
  then obtain v where v: "\<And>n. dist (f (v n)) (u n) \<le> C" by auto
  have *: "(\<lambda>n. to_Gromov_completion (f (v n))) \<longlonglongrightarrow> y"
    apply (rule Gromov_converging_at_boundary_bounded_perturbation[OF * \<open>y \<in> Gromov_boundary\<close>])
    using v by (simp add: dist_commute)
  then have "Gromov_converging_at_boundary (\<lambda>n. f (v n))"
    using assms(2) lim_imp_Gromov_converging_at_boundary by force
  then have "Gromov_converging_at_boundary v"
    using Gromov_converging_at_infinity_quasi_isometry[OF quasi_isometry_betweenD(1)[OF assms(1)]] by auto
  then obtain x where "x \<in> Gromov_boundary" "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> x"
    using Gromov_converging_at_boundary_converges by blast
  then have "(\<lambda>n. (Gromov_extension f) (to_Gromov_completion (v n))) \<longlonglongrightarrow> Gromov_extension f x"
    using isCont_tendsto_compose[OF Gromov_extension_continuous[OF quasi_isometry_betweenD(1)[OF assms(1)] \<open>x \<in> Gromov_boundary\<close>]] by fastforce
  then have "y = Gromov_extension f x"
    using * LIMSEQ_unique by auto
  then show ?thesis using \<open>x \<in> Gromov_boundary\<close> by auto
qed

lemma Gromov_extension_onto':
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
  shows "(Gromov_extension f)`Gromov_boundary = Gromov_boundary"
using Gromov_extension_onto[OF assms] Gromov_extension_quasi_isometry_boundary_to_boundary[OF quasi_isometry_betweenD(1)[OF assms]] by auto

text \<open>Finally, we obtain that a quasi-isometry between two Gromov hyperbolic spaces induces a
homeomorphism of their boundaries.\<close>

theorem Gromov_boundaries_homeomorphic:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
  shows "(Gromov_boundary::'a Gromov_completion set) homeomorphic (Gromov_boundary::'b Gromov_completion set)"
using Gromov_extension_boundary_homeomorphism[OF quasi_isometry_betweenD(1)[OF assms]] Gromov_extension_onto'[OF assms]
unfolding homeomorphic_def homeomorphism_on_def by auto



section \<open>Extensions of isometries to the boundary\<close>

text \<open>The results of the previous section can be improved for isometries, as there is no need for
geodesicity any more. We follow the same proofs as in the previous section\<close>

text \<open>An isometry preserves the Gromov product.\<close>

lemma Gromov_product_isometry:
  assumes "isometry_on UNIV f"
  shows "Gromov_product_at (f x) (f y) (f z) = Gromov_product_at x y z"
unfolding Gromov_product_at_def by (simp add: isometry_onD[OF assms])

text \<open>An isometry preserves convergence at infinity.\<close>

lemma Gromov_converging_at_infinity_isometry:
  fixes f::"'a::Gromov_hyperbolic_space \<Rightarrow> 'b::Gromov_hyperbolic_space"
  assumes "isometry_on UNIV f"
  shows "Gromov_converging_at_boundary (\<lambda>n. f (u n)) \<longleftrightarrow> Gromov_converging_at_boundary u"
proof
  assume *: "Gromov_converging_at_boundary u"
  show "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
    apply (rule Gromov_converging_at_boundaryI[of "f (basepoint)"])
    using * unfolding Gromov_converging_at_boundary_def Gromov_product_isometry[OF assms] by auto
next
  assume *: "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
  have **: "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. M \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))" for M
    using * unfolding Gromov_converging_at_boundary_def by auto
  show "Gromov_converging_at_boundary u"
    apply (rule Gromov_converging_at_boundaryI[of "basepoint"])
    using ** unfolding Gromov_converging_at_boundary_def Gromov_product_isometry[OF assms] by auto
qed

text \<open>The Gromov extension of an isometry sends the boundary to the boundary.\<close>

lemma Gromov_extension_isometry_boundary_to_boundary:
  fixes f::"'a::Gromov_hyperbolic_space \<Rightarrow> 'b::Gromov_hyperbolic_space"
  assumes "isometry_on UNIV f"
          "x \<in> Gromov_boundary"
  shows "(Gromov_extension f) x \<in> Gromov_boundary"
proof -
  have *: "Gromov_converging_at_boundary (\<lambda>n. f (rep_Gromov_completion x n))"
    by (simp add: Gromov_converging_at_infinity_isometry[OF assms(1)] Gromov_boundary_rep_converging assms(2))
  show ?thesis
    unfolding Gromov_extension_def using assms(2) unfolding comp_def apply auto
    by (metis Gromov_converging_at_boundary_converges * limI)
qed

text \<open>The Gromov extension of an isometry is a homeomorphism. (We copy the proof for
quasi-isometries, with some simplifications.)\<close>

lemma Gromov_extension_isometry_homeomorphism:
  fixes f::"'a::Gromov_hyperbolic_space \<Rightarrow> 'b::Gromov_hyperbolic_space"
  assumes "isometry_on UNIV f"
  shows "homeomorphism_on UNIV (Gromov_extension f)"
proof (rule homeomorphism_on_sequentially)
  fix x u
  show "u \<longlonglongrightarrow> x = (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
  proof (cases x)
    text \<open>First, consider the case where the limit point $x$ is in the boundary. We use a good
    criterion expressing everything in terms of sequences inside the space.\<close>
    case boundary
    show ?thesis
    proof (rule homeomorphism_on_extension_sequentially_precise[of "range to_Gromov_completion" Gromov_boundary])
      show "x \<in> Gromov_boundary" by fact
      fix n::nat show "u n \<in> range to_Gromov_completion \<union> Gromov_boundary"
        unfolding Gromov_boundary_def by auto
    next
      fix u and b::"'a Gromov_completion"
      assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "b \<in> Gromov_boundary" "u \<longlonglongrightarrow> b"
      define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
      have v: "u n = to_Gromov_completion (v n)" for n
        using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)
      show "convergent (\<lambda>n. Gromov_extension f (u n))"
        using u unfolding v apply auto
        apply (rule Gromov_converging_at_boundary_converges')
        by (auto simp add: Gromov_converging_at_infinity_isometry[OF assms(1)] lim_imp_Gromov_converging_at_boundary)
    next
      fix u c
      assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "c \<in> Gromov_extension f ` Gromov_boundary" "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> c"
      then have "c \<in> Gromov_boundary" using Gromov_extension_isometry_boundary_to_boundary[OF assms(1)] by auto
      define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
      have v: "u n = to_Gromov_completion (v n)" for n
        using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)
      have "Gromov_converging_at_boundary (\<lambda>n. f (v n))"
        apply (rule lim_imp_Gromov_converging_at_boundary[OF _ \<open>c \<in> Gromov_boundary\<close>])
        using u(3) unfolding v by auto
      then show "convergent u"
        using u unfolding v
        by (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_isometry[OF assms(1), symmetric])
    next
      fix b::"'a Gromov_completion" assume "b \<in> Gromov_boundary"
      show "\<exists>u. (\<forall>n. u n \<in> range to_Gromov_completion) \<and> u \<longlonglongrightarrow> b \<and> (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f b"
        apply (rule exI[of _ "to_Gromov_completion o (rep_Gromov_completion b)"], auto simp add: comp_def)
        unfolding Gromov_completion_converge_to_boundary[OF \<open>b \<in> Gromov_boundary\<close>]
        using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] apply auto[1]
        unfolding Gromov_extension_def using \<open>b \<in> Gromov_boundary\<close> unfolding comp_def
        by (auto simp add: convergent_LIMSEQ_iff[symmetric] Gromov_boundary_rep_converging Gromov_converging_at_infinity_isometry[OF assms(1)]
                 intro!: Gromov_converging_at_boundary_converges')
    qed
  next
    text \<open>Next, consider the case where $x$ is inside the space. Then we show everything by going
    back and forth between the original space and its copy in the completion, and arguing that $f$
    is a homeomorphism on the original space.\<close>
    case (to_Gromov_completion xin)
    then have fx: "Gromov_extension f x \<in> range to_Gromov_completion"
      using Gromov_extension_inside_space by blast
    have x: "x \<in> range to_Gromov_completion"
      using to_Gromov_completion by blast
    show ?thesis
    proof
      assume H: "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
      then have fu_in: "eventually (\<lambda>n. Gromov_extension f (u n) \<in> range to_Gromov_completion) sequentially"
        using fx to_Gromov_completion_range_open H topological_tendstoD by fastforce
      have u_in: "eventually (\<lambda>n. u n \<in> range to_Gromov_completion) sequentially"
        using Gromov_extension_isometry_boundary_to_boundary[OF assms(1)] eventually_mono[OF fu_in]
        by (metis DiffE DiffI Gromov_boundary_def iso_tuple_UNIV_I)

      have B: "from_Gromov_completion (Gromov_extension f y) = f (from_Gromov_completion y)" if "Gromov_extension f y \<in> range to_Gromov_completion" for y
        by (metis Gromov_extension_isometry_boundary_to_boundary Gromov_extension_def assms(1) from_to_Gromov_completion not_in_Gromov_boundary' rangeE that)
      have "(\<lambda>n. from_Gromov_completion (Gromov_extension f (u n))) \<longlonglongrightarrow> from_Gromov_completion (Gromov_extension f x)"
        by (rule continuous_on_tendsto_compose[OF from_Gromov_completion_continuous(2) H fx fu_in])
      then have C: "(\<lambda>n. f (from_Gromov_completion (u n))) \<longlonglongrightarrow> f (from_Gromov_completion x)"
        unfolding B[OF fx, symmetric] apply (rule Lim_transform_eventually[rotated]) using eventually_mono[OF fu_in B] by auto
      have "(\<lambda>n. from_Gromov_completion (u n)) \<longlonglongrightarrow> from_Gromov_completion x"
        apply (rule iffD2[OF homeomorphism_on_compose[OF isometry_on_homeomorphism(2)[OF assms]] C])
        using to_Gromov_completion by auto
      then have L: "(\<lambda>n. to_Gromov_completion (from_Gromov_completion (u n))) \<longlonglongrightarrow> to_Gromov_completion (from_Gromov_completion x)"
        using continuous_on_tendsto_compose[OF to_Gromov_completion_continuous] by auto

      have **: "to_Gromov_completion (from_Gromov_completion y) = y" if "y \<in> range to_Gromov_completion" for y::"'a Gromov_completion"
        using Gromov_extension_isometry_boundary_to_boundary assms(1) that to_from_Gromov_completion by fastforce
      then have "eventually (\<lambda>n. to_Gromov_completion (from_Gromov_completion (u n)) = u n) sequentially"
        using u_in eventually_mono by force
      then have "u \<longlonglongrightarrow> to_Gromov_completion (from_Gromov_completion x)"
        by (rule Lim_transform_eventually[OF _ L])
      then show "u \<longlonglongrightarrow> x"
        using ** by (simp add: x)
    next
      assume "u \<longlonglongrightarrow> x"
      then have u_in: "eventually (\<lambda>n. u n \<in> range to_Gromov_completion) sequentially"
        using x to_Gromov_completion_range_open topological_tendstoD by fastforce
      define y where "y = from_Gromov_completion x"
      then have *: "continuous (at y) f"
        using homeomorphism_on_continuous[OF isometry_on_homeomorphism(2)[OF assms]] continuous_on_eq_continuous_within by blast
      have **: "continuous (at x within to_Gromov_completion`UNIV) (Gromov_extension f)"
        using Gromov_extension_continuous_inside[OF *] y_def to_Gromov_completion by auto

      show "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f x"
        apply (rule continuous_within_tendsto_compose[OF ** _ \<open>u \<longlonglongrightarrow> x\<close>])
        using u_in by auto
    qed
  qed
qed

text \<open>The composition of the Gromov extension of two isometries is the Gromov extension of the
composition.\<close>

lemma Gromov_extension_isometry_on_composition:
  assumes "isometry_on UNIV f"
          "isometry_on UNIV g"
  shows "Gromov_extension (g o f) = Gromov_extension g o Gromov_extension f"
proof -
  have In: "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" if H: "x \<in> range to_Gromov_completion" for x
  proof -
    obtain y where *: "x = to_Gromov_completion y"
      using H by auto
    show ?thesis
      unfolding * comp_def by auto
  qed
  moreover have "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" if H: "x \<in> Gromov_boundary" for x
  proof -
    obtain u where u: "\<And>n. u n \<in> range to_Gromov_completion" "u \<longlonglongrightarrow> x"
      using closure_sequential to_Gromov_completion_range_dense by blast
    have "(\<lambda>n. Gromov_extension (g o f) (u n)) \<longlonglongrightarrow> Gromov_extension (g o f) x"
      apply (rule continuous_within_tendsto_compose[OF _ _ u(2), of UNIV])
      using homeomorphism_on_continuous[OF Gromov_extension_isometry_homeomorphism[OF isometry_on_compose[OF assms(1) isometry_on_subset[OF assms(2)]]]] unfolding comp_def
      by (auto simp add: continuous_on_eq_continuous_within)
    then have A: "(\<lambda>n. (Gromov_extension g) ((Gromov_extension f) (u n))) \<longlonglongrightarrow> Gromov_extension (g o f) x"
      unfolding In[OF u(1)] unfolding comp_def by auto

    have *: "(\<lambda>n. (Gromov_extension f) (u n)) \<longlonglongrightarrow> (Gromov_extension f) x"
      apply (rule continuous_within_tendsto_compose[OF _ _ u(2), of UNIV])
      using homeomorphism_on_continuous[OF Gromov_extension_isometry_homeomorphism[OF assms(1)]] unfolding comp_def
      by (auto simp add: continuous_on_eq_continuous_within)
    have "(\<lambda>n. (Gromov_extension g) ((Gromov_extension f) (u n))) \<longlonglongrightarrow> Gromov_extension g ((Gromov_extension f) x)"
      apply (rule continuous_within_tendsto_compose[OF _ _ *, of UNIV])
      using homeomorphism_on_continuous[OF Gromov_extension_isometry_homeomorphism[OF assms(2)]] unfolding comp_def
      by (auto simp add: continuous_on_eq_continuous_within)
    then show ?thesis using LIMSEQ_unique A comp_def by auto
  qed
  ultimately have "Gromov_extension (g o f) x = (Gromov_extension g o Gromov_extension f) x" for x
    using not_in_Gromov_boundary by force
  then show ?thesis by auto
qed

text \<open>We specialize the previous results to bijective isometries, as this is the setting where they
will be used most of the time.\<close>

lemma Gromov_extension_isometry:
  assumes "isometry f"
  shows "homeomorphism_on UNIV (Gromov_extension f)"
        "continuous_on UNIV (Gromov_extension f)"
        "continuous (at x) (Gromov_extension f)"
using Gromov_extension_isometry_homeomorphism[OF isometryD(1)[OF assms]] homeomorphism_on_continuous apply auto
using \<open>homeomorphism_on UNIV (Gromov_extension f)\<close> continuous_on_eq_continuous_within homeomorphism_on_continuous by blast

lemma Gromov_extension_isometry_composition:
  assumes "isometry f"
          "isometry g"
  shows "Gromov_extension (g o f) = Gromov_extension g o Gromov_extension f"
using Gromov_extension_isometry_on_composition[OF isometryD(1)[OF assms(1)] isometryD(1)[OF assms(2)]] by simp

lemma Gromov_extension_isometry_iterates:
  fixes f::"'a \<Rightarrow> ('a::Gromov_hyperbolic_space)"
  assumes "isometry f"
  shows "Gromov_extension (f^^n) = (Gromov_extension f)^^n"
apply (induction n) using Gromov_extension_isometry_composition[OF isometry_iterates[OF assms] assms] unfolding comp_def by auto

lemma Gromov_extension_isometry_inv:
  assumes "isometry f"
  shows "inv (Gromov_extension f) = Gromov_extension (inv f)"
        "bij (Gromov_extension f)"
proof -
  have *: "(inv f) o f = id"
    using isometry_inverse(2)[OF assms] by (simp add: bij_is_inj)
  have "Gromov_extension ((inv f) o f) = Gromov_extension (inv f) o Gromov_extension f"
    by (rule Gromov_extension_isometry_composition[OF assms isometry_inverse(1)[OF assms]])
  then have A: "Gromov_extension (inv f) o Gromov_extension f = id"
    unfolding * by auto
  have *: "f o (inv f) = id"
    using isometry_inverse(2)[OF assms] by (meson bij_is_surj surj_iff)
  have "Gromov_extension (f o (inv f)) = Gromov_extension f o Gromov_extension (inv f)"
    by (rule Gromov_extension_isometry_composition[OF isometry_inverse(1)[OF assms] assms])
  then have B: "Gromov_extension f o Gromov_extension (inv f) = id"
    unfolding * by auto
  show "bij (Gromov_extension f)"
    using A B unfolding bij_def apply auto
    by (metis inj_on_id inj_on_imageI2, metis B comp_apply id_def rangeI)
  show "inv (Gromov_extension f) = Gromov_extension (inv f)"
    using B \<open>bij (Gromov_extension f)\<close> bij_is_inj inv_o_cancel left_right_inverse_eq by blast
qed

text \<open>We will especially use fixed points on the boundary. We note that if a point is fixed by
(the Gromov extension of) a map, then it is fixed by (the Gromov extension of) its inverse.\<close>

lemma Gromov_extension_inv_fixed_point:
  assumes "isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "Gromov_extension f xi = xi"
  shows "Gromov_extension (inv f) xi = xi"
by (metis Gromov_extension_isometry_inv(1) Gromov_extension_isometry_inv(2) assms(1) assms(2) bij_betw_def inv_f_f)

text \<open>The extended Gromov product is invariant under isometries. This follows readily from the
definition, but still the proof is not fully automatic, unfortunately.\<close>

lemma Gromov_extension_preserves_extended_Gromov_product:
  assumes "isometry f"
  shows "extended_Gromov_product_at (f x) (Gromov_extension f xi) (Gromov_extension f eta) = extended_Gromov_product_at x xi eta"
proof -
  have "{liminf (\<lambda>n. ereal (Gromov_product_at (f x) (u n) (v n))) |u v.
          (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> Gromov_extension f xi \<and> (\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f eta} =
        {liminf (\<lambda>n. ereal (Gromov_product_at x (u n) (v n))) |u v.
          (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi \<and> (\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> eta}"
  proof (auto)
    fix u v assume H: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> Gromov_extension f xi"
                      "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f eta"
    define u' where "u' = (\<lambda>n. (inv f) (u n))"
    define v' where "v' = (\<lambda>n. (inv f) (v n))"
    have "(\<lambda>n. to_Gromov_completion (u' n)) \<longlonglongrightarrow> Gromov_extension (inv f) (Gromov_extension f xi)"
      unfolding u'_def Gromov_extension_inside_space[symmetric]
      apply (rule iffD1[OF homeomorphism_on_compose[OF Gromov_extension_isometry_homeomorphism[OF isometryD(1)[OF isometry_inverse(1)[OF assms]]]]])
      using H(1) by auto
    moreover have "Gromov_extension (inv f) (Gromov_extension f xi) = xi"
      using Gromov_extension_isometry_composition[OF assms isometry_inverse(1)[OF assms], symmetric] unfolding comp_def
      using bij_is_inj[OF isometry_inverse(2)[OF assms]]
      by (simp add: \<open>Gromov_extension (inv f) \<circ> Gromov_extension f = Gromov_extension (inv f \<circ> f)\<close> pointfree_idE)
    ultimately have U: "(\<lambda>n. to_Gromov_completion (u' n)) \<longlonglongrightarrow> xi" by simp
    have "(\<lambda>n. to_Gromov_completion (v' n)) \<longlonglongrightarrow> Gromov_extension (inv f) (Gromov_extension f eta)"
      unfolding v'_def Gromov_extension_inside_space[symmetric]
      apply (rule iffD1[OF homeomorphism_on_compose[OF Gromov_extension_isometry_homeomorphism[OF isometryD(1)[OF isometry_inverse(1)[OF assms]]]]])
      using H(2) by auto
    moreover have "Gromov_extension (inv f) (Gromov_extension f eta) = eta"
      using Gromov_extension_isometry_composition[OF assms isometry_inverse(1)[OF assms], symmetric] unfolding comp_def
      using bij_is_inj[OF isometry_inverse(2)[OF assms]]
      by (simp add: \<open>Gromov_extension (inv f) \<circ> Gromov_extension f = Gromov_extension (inv f \<circ> f)\<close> pointfree_idE)
    ultimately have V: "(\<lambda>n. to_Gromov_completion (v' n)) \<longlonglongrightarrow> eta" by simp
    have uv: "u n = f (u' n)" "v n = f (v' n)" for n
      unfolding u'_def v'_def by (auto simp add: assms isometryD(3) surj_f_inv_f)
    have "Gromov_product_at (f x) (u n) (v n) = Gromov_product_at x (u' n) (v' n)" for n
      unfolding uv using assms by (simp add: Gromov_product_isometry isometry_def)
    then have "liminf (\<lambda>n. ereal (Gromov_product_at (f x) (u n) (v n))) = liminf (\<lambda>n. ereal (Gromov_product_at x (u' n) (v' n)))"
      by auto
    then show "\<exists>u' v'.
              liminf (\<lambda>n. ereal (Gromov_product_at (f x) (u n) (v n))) = liminf (\<lambda>n. ereal (Gromov_product_at x (u' n) (v' n))) \<and>
              (\<lambda>n. to_Gromov_completion (u' n)) \<longlonglongrightarrow> xi \<and> (\<lambda>n. to_Gromov_completion (v' n)) \<longlonglongrightarrow> eta"
      using U V by blast
  next
    fix u v assume H: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
                      "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> eta"
    define u' where "u' = (\<lambda>n. f (u n))"
    define v' where "v' = (\<lambda>n. f (v n))"
    have U: "(\<lambda>n. to_Gromov_completion (u' n)) \<longlonglongrightarrow> Gromov_extension f xi"
      unfolding u'_def Gromov_extension_inside_space[symmetric]
      apply (rule iffD1[OF homeomorphism_on_compose[OF Gromov_extension_isometry_homeomorphism[OF isometryD(1)[OF assms]]]])
      using H(1) by auto
    have V: "(\<lambda>n. to_Gromov_completion (v' n)) \<longlonglongrightarrow> Gromov_extension f eta"
      unfolding v'_def Gromov_extension_inside_space[symmetric]
      apply (rule iffD1[OF homeomorphism_on_compose[OF Gromov_extension_isometry_homeomorphism[OF isometryD(1)[OF assms]]]])
      using H(2) by auto
    have "Gromov_product_at (f x) (u' n) (v' n) = Gromov_product_at x (u n) (v n)" for n
      unfolding u'_def v'_def using assms by (simp add: Gromov_product_isometry isometry_def)
    then have "liminf (\<lambda>n. ereal (Gromov_product_at x (u n) (v n))) = liminf (\<lambda>n. ereal (Gromov_product_at (f x) (u' n) (v' n)))"
      by auto
    then show "\<exists>u' v'.
              liminf (\<lambda>n. ereal (Gromov_product_at x (u n) (v n))) = liminf (\<lambda>n. ereal (Gromov_product_at (f x) (u' n) (v' n))) \<and>
              (\<lambda>n. to_Gromov_completion (u' n)) \<longlonglongrightarrow> Gromov_extension f xi \<and> (\<lambda>n. to_Gromov_completion (v' n)) \<longlonglongrightarrow> Gromov_extension f eta"
      using U V by auto
  qed
  then show ?thesis
    unfolding extended_Gromov_product_at_topological by auto
qed

end (*of theory Boundary_Extension*)
