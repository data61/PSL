(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Busemann functions\<close>

theory Busemann_Function
  imports Boundary_Extension Ergodic_Theory.Fekete
begin

text \<open>The Busemann function $B_\xi(x,y)$ measures the difference $d(\xi, x) - d(\xi, y)$, where $\xi$
is a point at infinity and $x$ and $y$ are inside a Gromov hyperbolic space. This is not well defined
in this way, as we are subtracting two infinities, but one can make sense of this difference by
considering the behavior along a sequence tending to $\xi$. The limit may depend on the sequence, but
as usual in Gromov hyperbolic spaces it only depends on the sequence up to a uniform constant. Thus,
we may define the Busemann function using for instance the supremum of the limsup over all possible
sequences -- other choices would give rise to equivalent definitions, up to some multiple of
$\delta$.\<close>

definition Busemann_function_at::"('a::Gromov_hyperbolic_space) Gromov_completion \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where "Busemann_function_at xi x y = real_of_ereal (
    Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi})"

text \<open>Since limsups are only defined for complete orders currently, the definition goes through
ereals, and we go back to reals afterwards. However, there is no real difficulty here, as eveything
is bounded above and below (by $d(x,y)$ and $-d(x,y)$ respectively.\<close>

lemma Busemann_function_ereal:
  "ereal(Busemann_function_at xi x y) = Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
proof -
  have A: "Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi} \<le> dist x y"
    by (rule Sup_least, auto intro!: Limsup_bounded always_eventually mono_intros simp add: algebra_simps)
  have B: "Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi} \<ge> -dist x y"
  proof -
    obtain u where *: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
      using rep_Gromov_completion_limit[of xi] by blast
    have "ereal(-dist x y) \<le> limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n)))"
      by (rule le_Limsup, auto intro!: always_eventually mono_intros simp add: algebra_simps)
    also have "... \<le> Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
      apply (rule Sup_upper) using * by auto
    finally show ?thesis by simp
  qed
  show ?thesis
    unfolding Busemann_function_at_def apply (rule ereal_real') using A B by auto
qed

text \<open>If $\xi$ is not at infinity, then the Busemann function is simply the difference of the
distances.\<close>

lemma Busemann_function_inner:
  "Busemann_function_at (to_Gromov_completion z) x y = dist x z - dist y z"
proof -
  have L: "limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) = dist x z - dist y z" if "u \<longlonglongrightarrow> z" for u
    by (rule lim_imp_Limsup, simp, intro tendsto_intros that)
  have "Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. u \<longlonglongrightarrow> z}
      = dist x z - dist y z"
  proof -
    obtain u where u: "u \<longlonglongrightarrow> z"
      by auto
    show ?thesis
      apply (rule order.antisym)
      apply (subst Sup_le_iff) using L apply auto[1]
      apply (subst L[OF u, symmetric]) apply (rule Sup_upper) using u by auto
  qed
  then have "ereal (Busemann_function_at (to_Gromov_completion z) x y) = dist x z - dist y z"
    unfolding Busemann_function_ereal by auto
  then show ?thesis by auto
qed

text \<open>The Busemann function measured at the same points vanishes.\<close>

lemma Busemann_function_xx [simp]:
  "Busemann_function_at xi x x = 0"
proof -
  have *: "{limsup (\<lambda>n. ereal(dist x (u n) - dist x (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi} = {0}"
    by (auto simp add: zero_ereal_def[symmetric] intro!: lim_imp_Limsup rep_Gromov_completion_limit[of xi])
  have "ereal (Busemann_function_at xi x x) = ereal 0"
    unfolding Busemann_function_ereal * by auto
  then show ?thesis
    by auto
qed

text \<open>Perturbing the points gives rise to a variation of the Busemann function bounded by the
size of the variations. This is obvious for inner Busemann functions, and everything passes
readily to the limit.\<close>

lemma Busemann_function_mono [mono_intros]:
  "Busemann_function_at xi x y \<le> Busemann_function_at xi x' y' + dist x x' + dist y y'"
proof -
  have A: "limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n)))
          \<le> ereal(Busemann_function_at xi x' y') + ereal (dist x x' + dist y y')"
    if "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi" for u
  proof -
    have *: "dist x z + dist y' z \<le> dist x x' + (dist y y' + (dist x' z + dist y z))" for z
      using add_mono[OF dist_triangle[of x z x'] dist_triangle[of y' z y]] dist_commute[of y y'] by auto
    have "limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n))) + (- ereal (dist x x' + dist y y'))
      = limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n)) + (- ereal (dist x x' + dist y y')))"
      by (rule Limsup_add_ereal_right[symmetric], auto)
    also have "... \<le> limsup (\<lambda>n. ereal (dist x' (u n) - dist y' (u n)))"
      by (auto intro!: Limsup_mono always_eventually simp: algebra_simps *)
    also have "... \<le> Sup {limsup (\<lambda>n. ereal (dist x' (u n) - dist y' (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
      apply (rule Sup_upper) using that by auto
    finally have "limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n))) + (- ereal (dist x x' + dist y y'))
          \<le> ereal(Busemann_function_at xi x' y')"
      unfolding Busemann_function_ereal by auto
    then show ?thesis
      unfolding minus_ereal_def[symmetric] by (subst ereal_minus_le[symmetric], auto)
  qed
  have "ereal (Busemann_function_at xi x y) \<le> ereal(Busemann_function_at xi x' y') + dist x x' + dist y y'"
    unfolding Busemann_function_ereal[of xi x y] using A by (auto intro!: Sup_least simp: algebra_simps)
  then show ?thesis by simp
qed

text \<open>In particular, it follows that the Busemann function $B_\xi(x,y)$ is bounded in absolute value
by $d(x,y)$.\<close>

lemma Busemann_function_le_dist [mono_intros]:
  "abs(Busemann_function_at xi x y) \<le> dist x y"
using Busemann_function_mono[of xi x y y y] Busemann_function_mono[of xi x x x y] by auto

lemma Busemann_function_Lipschitz [mono_intros]:
  "abs(Busemann_function_at xi x y - Busemann_function_at xi x' y') \<le> dist x x' + dist y y'"
using Busemann_function_mono[of xi x y x' y'] Busemann_function_mono[of xi x' y' x y] by (simp add: dist_commute)

text \<open>By the very definition of the Busemann function, the difference of distance functions is
bounded above by the Busemann function when one converges to $\xi$.\<close>

lemma Busemann_function_limsup:
  assumes "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
  shows "limsup (\<lambda>n. dist x (u n) - dist y (u n)) \<le> Busemann_function_at xi x y"
unfolding Busemann_function_ereal apply (rule Sup_upper) using assms by auto

text \<open>There is also a corresponding bound below, but with the loss of a constant. This follows
from the hyperbolicity of the space and a simple computation.\<close>

lemma Busemann_function_liminf:
  assumes "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
  shows "Busemann_function_at xi x y \<le> liminf (\<lambda>n. dist (x::'a::Gromov_hyperbolic_space) (u n) - dist y (u n)) + 2 * deltaG(TYPE('a))"
proof (cases xi)
  case (to_Gromov_completion z)
  have *: "liminf (\<lambda>n. dist x (u n) - dist y (u n)) = dist x z - dist y z"
    apply (rule lim_imp_Liminf, simp, intro tendsto_intros)
    using assms unfolding to_Gromov_completion by auto
  show ?thesis
    unfolding to_Gromov_completion plus_ereal.simps(1)[symmetric] Busemann_function_inner * by auto
next
  case boundary
  have I: "limsup (\<lambda>n. ereal(dist x (v n) - dist y (v n))) \<le> liminf (\<lambda>n. ereal(dist x (u n) - dist y (u n))) + 2 * deltaG(TYPE('a))"
    if v: "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> xi" for v
  proof -
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at x (u m) (v n) \<ge> dist x y"
      using same_limit_imp_Gromov_product_tendsto_infinity[OF boundary assms v] by blast
    have A: "dist x (v n) - dist y (v n) - 2 * deltaG(TYPE('a)) \<le> dist x (u m) - dist y (u m)" if "m \<ge> N" "n \<ge> N" for m n
    proof -
      have "Gromov_product_at x (v n) y \<le> dist x y"
        by (intro mono_intros)
      then have "min (Gromov_product_at x (u m) (v n)) (Gromov_product_at x (v n) y) = Gromov_product_at x (v n) y"
        using N[OF \<open>m \<ge> N\<close> \<open>n \<ge> N\<close>] by linarith
      moreover have "Gromov_product_at x (u m) y \<ge> min (Gromov_product_at x (u m) (v n)) (Gromov_product_at x (v n) y) - deltaG(TYPE('a))"
        by (intro mono_intros)
      ultimately have "Gromov_product_at x (u m) y \<ge> Gromov_product_at x (v n) y - deltaG(TYPE('a))"
        by auto
      then show ?thesis
        unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps dist_commute)
    qed
    have B: "dist x (v n) - dist y (v n) - 2 * deltaG(TYPE('a)) \<le> liminf (\<lambda>m. dist x (u m) - dist y (u m))" if "n \<ge> N" for n
      apply (rule Liminf_bounded) using A[OF _ that] unfolding eventually_sequentially by auto
    have C: "dist x (v n) - dist y (v n) \<le> liminf (\<lambda>m. dist x (u m) - dist y (u m)) + 2 * deltaG(TYPE('a))" if "n \<ge> N" for n
      using B[OF that] by (subst ereal_minus_le[symmetric], auto)
    show ?thesis
      apply (rule Limsup_bounded) unfolding eventually_sequentially apply (rule exI[of _ N]) using C by auto
  qed
  show ?thesis
    unfolding Busemann_function_ereal apply (rule Sup_least) using I by auto
qed

text \<open>To avoid formulating things in terms of liminf and limsup on ereal, the following formulation
of the two previous lemmas is useful.\<close>

lemma Busemann_function_inside_approx:
  assumes "e > (0::real)" "(\<lambda>n. to_Gromov_completion (t n::'a::Gromov_hyperbolic_space)) \<longlonglongrightarrow> xi"
  shows "eventually (\<lambda>n. Busemann_function_at (to_Gromov_completion (t n)) x y \<le> Busemann_function_at xi x y + e
              \<and> Busemann_function_at (to_Gromov_completion (t n)) x y \<ge> Busemann_function_at xi x y - 2 * deltaG(TYPE('a)) - e) sequentially"
proof -
  have A: "eventually (\<lambda>n. Busemann_function_at (to_Gromov_completion (t n)) x y < Busemann_function_at xi x y + ereal e) sequentially"
    apply (rule Limsup_lessD)
    unfolding Busemann_function_inner using le_less_trans[OF Busemann_function_limsup[OF assms(2)]] \<open>e > 0\<close> by auto
  have B: "eventually (\<lambda>n. Busemann_function_at (to_Gromov_completion (t n)) x y > Busemann_function_at xi x y -2 * deltaG(TYPE('a)) - ereal e) sequentially"
    apply (rule less_LiminfD)
    unfolding Busemann_function_inner using less_le_trans[OF _ Busemann_function_liminf[OF assms(2)], of "ereal(Busemann_function_at xi x y) - ereal e" x y] \<open>e > 0\<close> apply auto
    apply (unfold ereal_minus(1)[symmetric], subst ereal_minus_less_iff, simp)+
    unfolding ereal_minus(1)[symmetric] by (simp only: ereal_minus_less_iff, auto simp add: algebra_simps)
  show ?thesis
    by (rule eventually_mono[OF eventually_conj[OF A B]], auto)
qed

text \<open>The Busemann function is essentially a morphism, i.e., it should satisfy $B_\xi(x,z) =
B_\xi(x,y) + B_\xi(y,z)$, as it is defined as a difference of distances. This is not exactly
the case as there is a choice in the definition, but it is the case up to a uniform constant,
as we show in the next few lemmas. One says that it is a~\emph{quasi-morphism}.\<close>

lemma Busemann_function_triangle [mono_intros]:
  "Busemann_function_at xi x z \<le> Busemann_function_at xi x y + Busemann_function_at xi y z"
proof -
  have "limsup (\<lambda>n. dist x (u n) - dist z (u n)) \<le> Busemann_function_at xi x y + Busemann_function_at xi y z"
    if "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi" for u
  proof -
    have "limsup (\<lambda>n. dist x (u n) - dist z (u n)) = limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n)) + (dist y (u n) - dist z (u n)))"
      by auto
    also have "... \<le> limsup (\<lambda>n. dist x (u n) - dist y (u n)) + limsup (\<lambda>n. dist y (u n) - dist z (u n))"
      by (rule ereal_limsup_add_mono)
    also have "... \<le> ereal(Busemann_function_at xi x y) + Busemann_function_at xi y z"
      unfolding Busemann_function_ereal using that by (auto intro!: add_mono Sup_upper)
    finally show ?thesis by auto
  qed
  then have "ereal (Busemann_function_at xi x z) \<le> Busemann_function_at xi x y + Busemann_function_at xi y z"
    unfolding Busemann_function_ereal[of xi x z] by (auto intro!: Sup_least)
  then show ?thesis
    by auto
qed

lemma Busemann_function_xy_yx [mono_intros]:
  "Busemann_function_at xi x y + Busemann_function_at xi y (x::'a::Gromov_hyperbolic_space) \<le> 2 * deltaG(TYPE('a))"
proof -
  have *: "- liminf (\<lambda>n. ereal (dist y (u n) - dist x (u n))) \<le> ereal (2 * deltaG TYPE('a) - Busemann_function_at xi y x)"
    if "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi" for u
    using Busemann_function_liminf[of _ xi y x, OF that] ereal_minus_le_minus_plus unfolding ereal_minus(1)[symmetric]
    by fastforce

  have "ereal (Busemann_function_at xi x y) = Sup {limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
    unfolding Busemann_function_ereal by auto
  also have "... = Sup {limsup (\<lambda>n. - ereal(dist y (u n) - dist x (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
    by auto
  also have "... = Sup {- liminf (\<lambda>n. ereal(dist y (u n) - dist x (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}"
    unfolding ereal_Limsup_uminus by auto
  also have "... \<le> 2 * deltaG(TYPE('a)) - ereal(Busemann_function_at xi y x)"
    by (auto intro!: Sup_least *)
  finally show ?thesis
    by simp
qed

theorem Busemann_function_quasi_morphism [mono_intros]:
  "\<bar>Busemann_function_at xi x y + Busemann_function_at xi y z - Busemann_function_at xi x (z::'a::Gromov_hyperbolic_space)\<bar> \<le> 2 * deltaG(TYPE('a))"
using Busemann_function_triangle[of xi x z y] Busemann_function_triangle[of xi x y z] Busemann_function_xy_yx[of xi y z] by auto

text \<open>The extended Gromov product can be bounded from below by the Busemann function.\<close>

lemma Busemann_function_le_Gromov_product:
  "- Busemann_function_at xi y x/2 \<le> extended_Gromov_product_at x xi (to_Gromov_completion y)"
proof -
  have A: "-ereal(Busemann_function_at xi y x/2) \<le> liminf (\<lambda>n. Gromov_product_at x (u n) y)"
    if "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi" for u
  proof -
    have *: "limsup (\<lambda>n. - ereal (Gromov_product_at x (u n) y) * 2) \<le> limsup (\<lambda>n. ereal (dist y (u n) - dist x (u n)))"
      by (auto intro!: Limsup_mono always_eventually simp: algebra_simps Gromov_product_at_def divide_simps dist_commute)
    also have "... \<le> ereal(Busemann_function_at xi y x)"
      unfolding Busemann_function_ereal using that by (auto intro!: Sup_upper)
    finally have "-ereal(Busemann_function_at xi y x) \<le> liminf (\<lambda>n. Gromov_product_at x (u n) y) * ereal 2"
      apply (subst ereal_uminus_le_reorder, subst ereal_mult_minus_left[symmetric], subst ereal_Limsup_uminus[symmetric])
      by (subst limsup_ereal_mult_right[symmetric], auto)
    moreover have "-ereal(z/2) \<le> t" if "-ereal z \<le> t * ereal 2" for z t
    proof -
      have *: "-ereal(z/2) = -ereal z / ereal 2"
        unfolding ereal_divide by auto
      have "0 < ereal 2"
        by auto
      then show ?thesis unfolding * using that
        by (metis (no_types) PInfty_neq_ereal(2) ereal_divide_le_posI ereal_uminus_eq_iff mult.commute that)
    qed
    ultimately show ?thesis by auto
  qed
  show ?thesis
  unfolding extended_Gromov_product_at_def proof (rule Inf_greatest, auto)
    fix u v assume uv: "xi = abs_Gromov_completion u" "abs_Gromov_completion v = to_Gromov_completion y" "Gromov_completion_rel u u" "Gromov_completion_rel v v"
    then have L: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
      using abs_Gromov_completion_limit by auto
    have *: "v n = y" for n
      using uv by (metis (mono_tags, hide_lams) Gromov_completion_rel_def Quotient3_Gromov_completion Quotient3_rep_abs abs_Gromov_completion_in_Gromov_boundary not_in_Gromov_boundary' rep_Gromov_completion_to_Gromov_completion)
    show "ereal (- (Busemann_function_at (abs_Gromov_completion u) y x / 2)) \<le> liminf (\<lambda>n. ereal (Gromov_product_at x (u n) (v n)))"
      unfolding uv(1)[symmetric] * using A[OF L] by simp
  qed
qed

text \<open>It follows that, if the Busemann function tends to minus infinity, i.e., the distance to
$\xi$ becomes smaller and smaller in a suitable sense, then the sequence is converging to $\xi$.
This is only an implication: one can have sequences tending to $\xi$ for which the Busemann function
does not tend to $-\infty$. This is in fact a stronger notion of convergence, sometimes called
radial convergence.\<close>

proposition Busemann_function_minus_infinity_imp_convergent:
  assumes "((\<lambda>n. Busemann_function_at xi (u n) x) \<longlongrightarrow> -\<infinity>) F"
  shows "((\<lambda>n. to_Gromov_completion (u n)) \<longlongrightarrow> xi) F"
proof (cases "trivial_limit F")
  case True
  then show ?thesis by auto
next
  case False
  have "xi \<in> Gromov_boundary"
  proof (cases xi)
    case (to_Gromov_completion z)
    then have "ereal(Busemann_function_at xi (u n) x) \<ge> - dist x z" for n
      unfolding to_Gromov_completion Busemann_function_inner by auto
    then have "-\<infinity> \<ge> -dist x z"
      using tendsto_lowerbound[OF assms always_eventually False] by metis
    then have False
      by auto
    then show ?thesis by auto
  qed
  have "((\<lambda>n. - ereal (Busemann_function_at xi (u n) x) / 2) \<longlongrightarrow> (- (-\<infinity>)/2)) F"
    apply (intro tendsto_intros) using assms by auto
  then have *: "((\<lambda>n. - ereal (Busemann_function_at xi (u n) x) / 2) \<longlongrightarrow> \<infinity>) F"
    by auto
  have **: "((\<lambda>n. extended_Gromov_product_at x xi (to_Gromov_completion (u n))) \<longlongrightarrow> \<infinity>) F"
    apply (rule tendsto_sandwich[of "\<lambda>n. - ereal (Busemann_function_at xi (u n) x) / 2" _ _ "\<lambda>n. \<infinity>", OF always_eventually always_eventually])
    using Busemann_function_le_Gromov_product[of xi _ x] * by auto
  show ?thesis
    using extended_Gromov_product_tendsto_PInf_a_b[OF **, of basepoint]
    by (auto simp add: Gromov_completion_boundary_limit[OF \<open>xi \<in> Gromov_boundary\<close>] extended_Gromov_product_at_commute)
qed

text \<open>Busemann functions are invariant under isometries. This is trivial as everything is defined
in terms of the distance, but the definition in terms of supremum and limsups makes the proof
tedious.\<close>

lemma Busemann_function_isometry:
  assumes "isometry f"
  shows "Busemann_function_at (Gromov_extension f xi) (f x) (f y) = Busemann_function_at xi x y"
proof -
  have "{limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n))) |u. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi}
        = {limsup (\<lambda>n. ereal(dist (f x) (v n) - dist (f y) (v n))) |v. (\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f xi}"
  proof (auto)
    fix u assume u: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
    define v where "v = f o u"
    have "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f xi"
      unfolding v_def comp_def Gromov_extension_inside_space[symmetric] using u Gromov_extension_isometry(2)[OF \<open>isometry f\<close>]
      by (metis continuous_on filterlim_compose iso_tuple_UNIV_I tendsto_at_iff_tendsto_nhds)
    moreover have "limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n))) = limsup (\<lambda>n. ereal (dist (f x) (v n) - dist (f y) (v n)))"
      unfolding v_def comp_def isometryD(2)[OF \<open>isometry f\<close>] by simp
    ultimately show "\<exists>v. limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n))) = limsup (\<lambda>n. ereal (dist (f x) (v n) - dist (f y) (v n))) \<and>
              (\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f xi"
      by blast
  next
    fix v assume v: "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> Gromov_extension f xi"
    define u where "u = (inv f) o v"
    have "isometry (inv f)"
      using isometry_inverse(1)[OF \<open>isometry f\<close>] by simp
    have *: "inv f (f z) = z" for z
      using isometry_inverse(2)[OF \<open>isometry f\<close>] by (simp add: bij_betw_def)
    have **: "(Gromov_extension (inv f) (Gromov_extension f xi)) = xi"
      using Gromov_extension_isometry_composition[OF \<open>isometry f\<close> \<open>isometry (inv f)\<close>]
      unfolding comp_def using isometry_inverse(2)[OF \<open>isometry f\<close>] by (auto simp: *, metis)
    have "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> Gromov_extension (inv f) (Gromov_extension f xi)"
      unfolding u_def comp_def Gromov_extension_inside_space[symmetric] using v Gromov_extension_isometry(2)[OF \<open>isometry (inv f)\<close>]
      by (metis continuous_on filterlim_compose iso_tuple_UNIV_I tendsto_at_iff_tendsto_nhds)
    then have "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
      using ** by auto
    moreover have "limsup (\<lambda>n. ereal (dist ((inv f) (f x)) (u n) - dist ((inv f) (f y)) (u n))) = limsup (\<lambda>n. ereal (dist (f x) (v n) - dist (f y) (v n)))"
      unfolding u_def comp_def isometryD(2)[OF \<open>isometry (inv f)\<close>] by simp
    ultimately show "\<exists>u. limsup (\<lambda>n. ereal (dist (f x) (v n) - dist (f y) (v n))) = limsup (\<lambda>n. ereal (dist x (u n) - dist y (u n))) \<and> (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi"
      by (simp add: *, force)
  qed
  then have "ereal (Busemann_function_at xi x y) = ereal (Busemann_function_at (Gromov_extension f xi) (f x) (f y))"
    unfolding Busemann_function_ereal by auto
  then show ?thesis by auto
qed

lemma dist_le_max_Busemann_functions [mono_intros]:
  assumes "xi \<noteq> eta"
  shows "dist x (y::'a::Gromov_hyperbolic_space) \<le> 2 * real_of_ereal (extended_Gromov_product_at y xi eta)
            + max (Busemann_function_at xi x y) (Busemann_function_at eta x y) + 2 * deltaG(TYPE('a))"
proof -
  have A: "ereal(dist x y - 2 * deltaG(TYPE('a)) - max (Busemann_function_at xi x y) (Busemann_function_at eta x y)) / ereal 2 \<le>
                    liminf (\<lambda>n. ereal(Gromov_product_at y (u n) (v n)))"
    if uv: "abs_Gromov_completion u = xi" "abs_Gromov_completion v = eta" "Gromov_completion_rel u u" "Gromov_completion_rel v v" for u v
  proof -
    have C: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> xi" "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> eta"
      using uv abs_Gromov_completion_limit by auto
    have "ereal(dist x y) \<le> ereal(2 * Gromov_product_at y (u n) (v n)) + 2 * deltaG(TYPE('a)) + max (ereal(dist x (u n) - dist y (u n))) (ereal(dist x (v n) - dist y (v n)))" for n
    proof -
      have "min (Gromov_product_at y (u n) x) (Gromov_product_at y x (v n)) \<le> Gromov_product_at y (u n) (v n) + deltaG(TYPE('a))"
        by (intro mono_intros)
      then consider "Gromov_product_at y (u n) x \<le> Gromov_product_at y (u n) (v n) + deltaG(TYPE('a))"|"Gromov_product_at y x (v n) \<le> Gromov_product_at y (u n) (v n) + deltaG(TYPE('a))"
        by linarith
      then have "dist x y \<le> 2 * Gromov_product_at y (u n) (v n) + 2 * deltaG(TYPE('a)) + max (dist x (u n) - dist y (u n)) (dist x (v n) - dist y (v n))"
        unfolding Gromov_product_at_def[of _ x] Gromov_product_at_def[of _ _ x] apply (cases)
        by (auto simp add: algebra_simps divide_simps dist_commute)
      then show ?thesis
        unfolding ereal_max[symmetric] plus_ereal.simps(1) by auto
    qed
    then have "ereal (dist x y) \<le> liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n)) + 2 * deltaG(TYPE('a)) + max (ereal(dist x (u n) - dist y (u n))) (ereal(dist x (v n) - dist y (v n))))"
      by (intro Liminf_bounded always_eventually, auto)
    also have "... \<le> liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n)) + 2 * deltaG(TYPE('a))) + limsup (\<lambda>n. max (ereal(dist x (u n) - dist y (u n))) (ereal(dist x (v n) - dist y (v n))))"
      by (rule ereal_liminf_limsup_add)
    also have "... = liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n))) + 2 * deltaG(TYPE('a)) + max (limsup (\<lambda>n. ereal(dist x (u n) - dist y (u n)))) (limsup (\<lambda>n. ereal(dist x (v n) - dist y (v n))))"
      apply (subst Liminf_add_ereal_right) by (auto simp add: Limsup_max_eq_max_Limsup)
    also have "... \<le> liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n))) + 2 * deltaG(TYPE('a)) + max (ereal(Busemann_function_at xi x y)) (Busemann_function_at eta x y)"
      unfolding Busemann_function_ereal apply (intro mono_intros Sup_upper) using C by auto
    finally have "ereal(dist x y) - ereal(2 * deltaG(TYPE('a)) + max (Busemann_function_at xi x y) (Busemann_function_at eta x y)) \<le>
                    liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n)))"
      unfolding ereal_max[symmetric] add.assoc plus_ereal.simps(1) by (subst ereal_minus_le, auto)
    then have "ereal(dist x y - 2 * deltaG(TYPE('a)) - max (Busemann_function_at xi x y) (Busemann_function_at eta x y)) \<le>
                    liminf (\<lambda>n. ereal(2 * Gromov_product_at y (u n) (v n)))"
      unfolding ereal_minus(1) by (auto simp add: algebra_simps)
    also have "... = ereal 2 * liminf (\<lambda>n. ereal(Gromov_product_at y (u n) (v n)))"
      unfolding times_ereal.simps(1)[symmetric] by (subst Liminf_ereal_mult_left, auto)
    finally show ?thesis
      by (subst ereal_divide_le_pos, auto)
  qed
  have "ereal(dist x y - 2 * deltaG(TYPE('a)) - max (Busemann_function_at xi x y) (Busemann_function_at eta x y)) / ereal 2 \<le>
                    extended_Gromov_product_at y xi eta"
    unfolding extended_Gromov_product_at_def apply (rule Inf_greatest) using A by auto
  also have "... = ereal(real_of_ereal(extended_Gromov_product_at y xi eta))"
    using assms by simp
  finally show ?thesis
    by simp
qed

lemma dist_minus_Busemann_max_ineq:
  "dist (x::'a::Gromov_hyperbolic_space) z - Busemann_function_at xi z x \<le> max (dist x y - Busemann_function_at xi y x) (dist y z - Busemann_function_at xi z y - 2 * Busemann_function_at xi y x) + 8 * deltaG(TYPE('a))"
proof -
  have I: "dist x z - Busemann_function_at (to_Gromov_completion t) z x \<le> max (dist x y - Busemann_function_at (to_Gromov_completion t) y x)
                      (dist y z - Busemann_function_at (to_Gromov_completion t) z y - 2 * Busemann_function_at (to_Gromov_completion t) y x)
                        + 2 * deltaG(TYPE('a))" for t
  proof -
    have "2 * dist x t + - max (dist x y - Busemann_function_at (to_Gromov_completion t) y x) (dist y z - Busemann_function_at (to_Gromov_completion t) z y - 2 * Busemann_function_at (to_Gromov_completion t) y x)
          = min (2 * dist x t - (dist x y - Busemann_function_at (to_Gromov_completion t) y x)) (2 * dist x t - (dist y z - Busemann_function_at (to_Gromov_completion t) z y - 2 * Busemann_function_at (to_Gromov_completion t) y x))"
      unfolding minus_max_eq_min min_add_distrib_right by auto
    also have "... = min (2 * Gromov_product_at t x y) (2 * Gromov_product_at t y z)"
      apply (rule cong[of "min _" "min _"], rule cong [of min min])
      unfolding Gromov_product_at_def Busemann_function_inner by (auto simp add: algebra_simps dist_commute divide_simps)
    also have "... = 2 * (min (Gromov_product_at t x y) (Gromov_product_at t y z))"
      by auto
    also have "... \<le> 2 * (Gromov_product_at t x z + deltaG(TYPE('a)))"
      by (intro mono_intros, auto)
    also have "... = 2 * dist x t - (dist x z - Busemann_function_at (to_Gromov_completion t) z x) + 2 * deltaG(TYPE('a))"
      unfolding Gromov_product_at_def Busemann_function_inner by (auto simp add: algebra_simps dist_commute divide_simps)
    finally show ?thesis
      by auto
  qed
  have "dist x z - Busemann_function_at xi z x \<le> max (dist x y - Busemann_function_at xi y x) (dist y z - Busemann_function_at xi z y - 2 * Busemann_function_at xi y x) + 8 * deltaG(TYPE('a)) + d"
    if "d > 0" for d
  proof -
    define e where "e = d/4"
    have "e > 0" unfolding e_def using that by auto
    obtain t where t: "(\<lambda>n. to_Gromov_completion (t n)) \<longlonglongrightarrow> xi"
      using rep_Gromov_completion_limit by auto
    have A: "eventually (\<lambda>n. Busemann_function_at xi y x \<le> Busemann_function_at (to_Gromov_completion (t n)) y x + 2 * deltaG(TYPE('a)) + e) sequentially"
      by (rule eventually_mono[OF Busemann_function_inside_approx[OF \<open>e > 0\<close> t, of y x]], auto)
    have B: "eventually (\<lambda>n. Busemann_function_at xi z y \<le> Busemann_function_at (to_Gromov_completion (t n)) z y + 2 * deltaG(TYPE('a)) + e) sequentially"
      by (rule eventually_mono[OF Busemann_function_inside_approx[OF \<open>e > 0\<close> t, of z y]], auto)
    have C: "eventually (\<lambda>n. Busemann_function_at xi z x \<ge> Busemann_function_at (to_Gromov_completion (t n)) z x - e) sequentially"
      by (rule eventually_mono[OF Busemann_function_inside_approx[OF \<open>e > 0\<close> t, of z x]], auto)
    obtain n where H: "Busemann_function_at xi y x \<le> Busemann_function_at (to_Gromov_completion (t n)) y x + 2 * deltaG(TYPE('a)) + e"
                      "Busemann_function_at xi z y \<le> Busemann_function_at (to_Gromov_completion (t n)) z y + 2 * deltaG(TYPE('a)) + e"
                      "Busemann_function_at xi z x \<ge> Busemann_function_at (to_Gromov_completion (t n)) z x - e"
      using eventually_conj[OF A eventually_conj[OF B C]] eventually_sequentially by auto
    have "dist x z - Busemann_function_at xi z x - e \<le> dist x z - Busemann_function_at (to_Gromov_completion (t n)) z x"
      using H by auto
    also have "... \<le> max (dist x y - Busemann_function_at (to_Gromov_completion (t n)) y x)
                      (dist y z - Busemann_function_at (to_Gromov_completion (t n)) z y - 2 * Busemann_function_at (to_Gromov_completion (t n)) y x)
                        + 2 * deltaG(TYPE('a))"
      using I by auto
    also have "... \<le> max (dist x y - (Busemann_function_at xi y x - 2 * deltaG(TYPE('a)) - e))
                      (dist y z - (Busemann_function_at xi z y - 2 * deltaG(TYPE('a)) - e) - 2 * (Busemann_function_at xi y x - 2 * deltaG(TYPE('a)) - e))
                        + 2 * deltaG(TYPE('a))"
      apply (intro mono_intros) using H by auto
    also have "... \<le> max (dist x y - Busemann_function_at xi y x + 6 * deltaG(TYPE('a)) + 3 * e)
                      (dist y z - Busemann_function_at xi z y - 2 * Busemann_function_at xi y x + 6 * deltaG(TYPE('a)) + 3 * e)
                        + 2 * deltaG(TYPE('a))"
      apply (intro add_mono max.mono) using \<open>e > 0\<close> by auto
    also have "... = max (dist x y - Busemann_function_at xi y x) (dist y z - Busemann_function_at xi z y - 2 * Busemann_function_at xi y x) + 8 * deltaG(TYPE('a)) + 3 * e"
      by auto
    finally show ?thesis unfolding e_def by auto
  qed
  then show ?thesis by (rule field_le_epsilon)
qed

end (*of theory Busemann_Function*)
