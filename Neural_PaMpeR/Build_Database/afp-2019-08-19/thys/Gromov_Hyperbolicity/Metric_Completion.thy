(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>The metric completion of a metric space\<close>

theory Metric_Completion
  imports Isometries
begin

text \<open>Any metric space can be completed, by adding the missing limits of Cauchy sequences.
Formally, there exists an isometric embedding of the space in a complete space, with dense image.
In this paragraph, we construct this metric completion. This is exactly the same construction
as the way in which real numbers are constructed from rational numbers.\<close>

subsection \<open>Definition of the metric completion\<close>

quotient_type (overloaded) 'a metric_completion =
  "nat \<Rightarrow> ('a::metric_space)" / partial: "\<lambda>u v. (Cauchy u) \<and> (Cauchy v) \<and> (\<lambda>n. dist (u n) (v n)) \<longlonglongrightarrow> 0"
unfolding part_equivp_def proof(auto intro!: ext)
  show "\<exists>x. Cauchy x"
    by (rule exI[of _ "\<lambda>_. undefined"]) (simp add: convergent_Cauchy convergent_const)
  fix x y z::"nat \<Rightarrow> 'a" assume H: "(\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0"
                                   "(\<lambda>n. dist (x n) (z n)) \<longlonglongrightarrow> 0"
  have *: "(\<lambda>n. dist (x n) (y n) + dist (x n) (z n)) \<longlonglongrightarrow> 0 + 0"
    by (rule tendsto_add) (auto simp add: H)
  show "(\<lambda>n. dist (y n) (z n)) \<longlonglongrightarrow> 0"
    apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. dist (x n) (y n) + dist (x n) (z n)"])
    using * by (auto simp add: dist_triangle3)
next
  fix x y z::"nat \<Rightarrow> 'a" assume H: "(\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0"
                                   "(\<lambda>n. dist (y n) (z n)) \<longlonglongrightarrow> 0"
  have *: "(\<lambda>n. dist (x n) (y n) + dist (y n) (z n)) \<longlonglongrightarrow> 0 + 0"
    by (rule tendsto_add) (auto simp add: H)
  show "(\<lambda>n. dist (x n) (z n)) \<longlonglongrightarrow> 0"
    apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. dist (x n) (y n) + dist (y n) (z n)"])
    using * by (auto simp add: dist_triangle)
next
  fix x y::"nat \<Rightarrow> 'a" assume H: "Cauchy x"
    "(\<lambda>v. Cauchy v \<and> (\<lambda>n. dist (x n) (v n)) \<longlonglongrightarrow> 0) = (\<lambda>v. Cauchy v \<and> (\<lambda>n. dist (y n) (v n)) \<longlonglongrightarrow> 0)"
  have "Cauchy x \<and> (\<lambda>n. dist (x n) (x n)) \<longlonglongrightarrow> 0" using H by auto
  then have "(\<lambda>n. dist (y n) (x n))\<longlonglongrightarrow> 0" using H by meson
  moreover have "dist (x n) (y n) = dist (y n) (x n)" for n using dist_commute by auto
  ultimately show "(\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0" by auto
qed

text \<open>We have to show that the metric completion is indeed a metric space, that
the original space embeds isometrically into it, and that it is complete. Before we prove these
statements, we start with two simple lemmas that will be needed later on.\<close>

lemma convergent_Cauchy_dist:
  fixes u v::"nat \<Rightarrow> ('a::metric_space)"
  assumes "Cauchy u" "Cauchy v"
  shows "convergent (\<lambda>n. dist (u n) (v n))"
proof (rule real_Cauchy_convergent, intro CauchyI)
  fix e::real assume "e > 0"
  obtain Nu where Nu: "\<forall>n \<ge> Nu. \<forall>m \<ge> Nu. dist (u n) (u m) < e/2" using assms(1)
    by (metis \<open>0 < e\<close> less_divide_eq_numeral1(1) metric_CauchyD mult_zero_left)
  obtain Nv where Nv: "\<forall>n \<ge> Nv. \<forall>m \<ge> Nv. dist (v n) (v m) < e/2" using assms(2)
    by (metis \<open>0 < e\<close> less_divide_eq_numeral1(1) metric_CauchyD mult_zero_left)
  define M where "M = max Nu Nv"
  {
    fix n m assume H: "n \<ge> M" "m \<ge> M"
    have *: "dist (u n) (u m) < e/2" "dist (v n) (v m) < e/2"
      using Nu Nv H unfolding M_def by auto
    have "dist (u m) (v m) - dist (u n) (v n) \<le> dist (u m) (u n) + dist (v n) (v m)"
      by (metis add.commute add.left_commute add_left_mono dist_commute dist_triangle2 dist_triangle_le linordered_field_class.sign_simps(42))
    also have "... < e/2 + e/2"
      using * by (simp add: dist_commute)
    finally have A: "dist (u m) (v m) - dist (u n) (v n) < e" by simp

    have "dist (u n) (v n) - dist (u m) (v m) \<le> dist (u m) (u n) + dist (v n) (v m)"
      by (metis add.commute add.left_commute add_left_mono dist_commute dist_triangle2 dist_triangle_le linordered_field_class.sign_simps(42))
    also have "... < e/2 + e/2"
      using * by (simp add: dist_commute)
    finally have "dist (u n) (v n) - dist (u m) (v m) < e" by simp
    then have "norm(dist (u m) (v m) - dist (u n) (v n)) < e" using A by auto
  }
  then show "\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. norm (dist (u m) (v m) - dist (u n) (v n)) < e"
    by auto
qed

lemma convergent_add_null:
  fixes u v::"nat \<Rightarrow> ('a::real_normed_vector)"
  assumes "convergent u"
          "(\<lambda>n. v n - u n) \<longlonglongrightarrow> 0"
  shows "convergent v" "lim v = lim u"
proof -
  have "(\<lambda>n. u n + (v n - u n)) \<longlonglongrightarrow> lim u + 0"
    apply (rule tendsto_add) using assms convergent_LIMSEQ_iff by auto
  then have *: "v \<longlonglongrightarrow> lim u" by auto
  show "convergent v" using * by (simp add: Lim_def convergentI)
  show "lim v = lim u" using * by (simp add: limI)
qed

text \<open>Let us now prove that the metric completion is a metric space: the distance between two
Cauchy sequences is the limit of the distances of points in the sequence. The convergence follows
from Lemma~\verb+convergent_Cauchy_dist+ above.\<close>

instantiation metric_completion :: (metric_space) metric_space
begin

lift_definition dist_metric_completion::"('a::metric_space) metric_completion \<Rightarrow> 'a metric_completion \<Rightarrow> real"
  is "\<lambda>x y. lim (\<lambda>n. dist (x n) (y n))"
proof -
  fix x y z t::"nat \<Rightarrow> 'a" assume H: "Cauchy x \<and> Cauchy y \<and> (\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0"
                                     "Cauchy z \<and> Cauchy t \<and> (\<lambda>n. dist (z n) (t n)) \<longlonglongrightarrow> 0"
  show "lim (\<lambda>n. dist (x n) (z n)) = lim (\<lambda>n. dist (y n) (t n))"
  proof (rule convergent_add_null(2))
    show "convergent (\<lambda>n. dist (y n) (t n))"
      apply (rule convergent_Cauchy_dist) using H by auto

    have a: "(\<lambda>n. - dist (t n) (z n) - dist (x n) (y n)) \<longlonglongrightarrow> -0 -0"
      apply (intro tendsto_intros) using H by (auto simp add: dist_commute)
    have b:"(\<lambda>n. dist (t n) (z n) + dist (x n) (y n)) \<longlonglongrightarrow> 0 + 0"
      apply (rule tendsto_add) using H by (auto simp add: dist_commute)
    have I: "dist (x n) (z n) \<le> dist (t n) (y n) + (dist (t n) (z n) + dist (x n) (y n))" for n
      using dist_triangle[of "x n" "z n" "y n"] dist_triangle[of "y n" "z n" "t n"]
      by (auto simp add: dist_commute add.commute)
    show "(\<lambda>n. dist (x n) (z n) - dist (y n) (t n)) \<longlonglongrightarrow> 0"
      apply (rule tendsto_sandwich[of "\<lambda>n. -(dist (x n) (y n) + dist (z n) (t n))" _ _ "\<lambda>n. dist (x n) (y n) + dist (z n) (t n)"])
      apply (auto intro!: always_eventually simp add: algebra_simps dist_commute I)
      apply (meson add_left_mono dist_triangle3 dist_triangle_le)
      using a b by auto
  qed
qed

lemma dist_metric_completion_limit:
  fixes x y::"'a metric_completion"
  shows "(\<lambda>n. dist (rep_metric_completion x n) (rep_metric_completion y n)) \<longlonglongrightarrow> dist x y"
proof -
  have C: "Cauchy (rep_metric_completion x)" "Cauchy (rep_metric_completion y)"
    using Quotient3_metric_completion Quotient3_rep_reflp by fastforce+
  show ?thesis
    unfolding dist_metric_completion_def using C apply auto
    using convergent_Cauchy_dist[OF C] convergent_LIMSEQ_iff by force
qed

lemma dist_metric_completion_limit':
  fixes x y::"nat \<Rightarrow> 'a"
  assumes "Cauchy x" "Cauchy y"
  shows "(\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> dist (abs_metric_completion x) (abs_metric_completion y)"
apply (subst dist_metric_completion.abs_eq)
using assms convergent_Cauchy_dist[OF assms] by (auto simp add: convergent_LIMSEQ_iff)

text \<open>To define a metric space in the current library of Isabelle/HOL, one should also introduce
a uniformity structure and a topology, as follows (they are prescribed by the distance):\<close>

definition uniformity_metric_completion::"(('a metric_completion) \<times> ('a metric_completion)) filter"
  where "uniformity_metric_completion = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_metric_completion :: "'a metric_completion set \<Rightarrow> bool"
  where "open_metric_completion U = (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance proof
  fix x y::"'a metric_completion"
  have C: "Cauchy (rep_metric_completion x)" "Cauchy (rep_metric_completion y)"
    using Quotient3_metric_completion Quotient3_rep_reflp by fastforce+
  show "(dist x y = 0) = (x = y)"
    apply (subst Quotient3_rel_rep[OF Quotient3_metric_completion, symmetric])
    unfolding dist_metric_completion_def using C apply auto
    using convergent_Cauchy_dist[OF C] convergent_LIMSEQ_iff apply force
    by (simp add: limI)
next
  fix x y z::"'a metric_completion"
  have a: "(\<lambda>n. dist (rep_metric_completion x n) (rep_metric_completion y n)) \<longlonglongrightarrow> dist x y"
    using dist_metric_completion_limit by auto
  have b: "(\<lambda>n. dist (rep_metric_completion x n) (rep_metric_completion z n) + dist (rep_metric_completion y n) (rep_metric_completion z n))
      \<longlonglongrightarrow> dist x z + dist y z"
    apply (rule tendsto_add) using dist_metric_completion_limit by auto
  show "dist x y \<le> dist x z + dist y z"
    by (rule LIMSEQ_le[OF a b], rule exI[of _ 0], auto simp add: dist_triangle2)
qed (auto simp add: uniformity_metric_completion_def open_metric_completion_def)
end

text \<open>Let us now show that the distance thus defined on the metric completion is indeed complete.
This is essentially by design.\<close>

instance metric_completion :: (metric_space) complete_space
proof
  fix X::"nat \<Rightarrow> 'a metric_completion" assume "Cauchy X"
  have *: "\<exists>N. \<forall>n \<ge> N. dist (rep_metric_completion (X k) N) (rep_metric_completion (X k) n) < (1/Suc k)" for k
  proof -
    have "Cauchy (rep_metric_completion (X k))"
      using Quotient3_metric_completion Quotient3_rep_reflp by fastforce+
    then have "\<exists>N. \<forall>m \<ge> N. \<forall>n \<ge> N. dist (rep_metric_completion (X k) m) (rep_metric_completion (X k) n) < (1/Suc k)"
      unfolding Cauchy_def by auto
    then show ?thesis by auto
  qed
  have "\<exists>N. \<forall>k. \<forall>n \<ge> N k. dist (rep_metric_completion (X k) (N k)) (rep_metric_completion (X k) n) < (1/Suc k)"
    apply (rule choice) using * by auto
  then obtain N::"nat \<Rightarrow> nat" where
    N: "dist (rep_metric_completion (X k) (N k)) (rep_metric_completion (X k) n) < (1/Suc k)" if "n \<ge> N k" for n k
    by auto
  define u where "u = (\<lambda>k. rep_metric_completion (X k) (N k))"

  have "Cauchy u"
  proof (rule metric_CauchyI)
    fix e::real assume "e > 0"
    obtain K::nat where "K > 4/e" using reals_Archimedean2 by blast
    obtain L::nat where L: "\<forall>m \<ge> L. \<forall>n \<ge> L. dist (X m) (X n) < e/2"
      using metric_CauchyD[OF \<open>Cauchy X\<close>, of "e/2"] \<open>e > 0\<close> by auto
    {
      fix m n assume "m \<ge> max K L" "n \<ge> max K L"
      then have "dist (X m) (X n) < e/2" using L by auto
      then have "eventually (\<lambda>p. dist (rep_metric_completion (X m) p) (rep_metric_completion (X n) p) < e/2) sequentially"
        using dist_metric_completion_limit[of "X m" "X n"] by (metis order_tendsto_iff)
      then obtain p where p: "p \<ge> max (N m) (N n)" "dist (rep_metric_completion (X m) p) (rep_metric_completion (X n) p) < e/2"
        using eventually_False_sequentially eventually_elim2 eventually_ge_at_top by blast
      have "dist (u m) (rep_metric_completion (X m) p) < 1 / real (Suc m)"
        unfolding u_def using N[of m p] p(1) by auto
      also have "... < e/4"
        using \<open>m \<ge> max K L\<close> \<open>K > 4/e\<close> \<open>e > 0\<close> apply (auto simp add: divide_simps algebra_simps)
        by (metis leD le_less_trans less_add_same_cancel2 linear of_nat_le_iff real_mult_le_cancel_iff2)
      finally have Im: "dist (u m) (rep_metric_completion (X m) p) < e/4" by simp
      have "dist (u n) (rep_metric_completion (X n) p) < 1 / real (Suc n)"
        unfolding u_def using N[of n p] p(1) by auto
      also have "... < e/4"
        using \<open>n \<ge> max K L\<close> \<open>K > 4/e\<close> \<open>e > 0\<close> apply (auto simp add: divide_simps algebra_simps)
        by (metis leD le_less_trans less_add_same_cancel2 linear of_nat_le_iff real_mult_le_cancel_iff2)
      finally have In: "dist (u n) (rep_metric_completion (X n) p) < e/4" by simp

      have "dist (u m) (u n) \<le> dist (u m) (rep_metric_completion (X m) p)
          + dist (rep_metric_completion (X m) p) (rep_metric_completion (X n) p) + dist (rep_metric_completion (X n) p) (u n)"
        by (metis add.commute add_left_mono dist_commute dist_triangle_le dist_triangle)
      also have "... < e/4 + e/2 + e/4"
        using In Im p(2) by (simp add: dist_commute)
      also have "... = e" by auto
      finally have "dist (u m) (u n) < e" by auto
    }
    then show "\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (u m) (u n) < e" by meson
  qed
  have *: "(\<lambda>n. dist (abs_metric_completion u) (X n)) \<longlonglongrightarrow> 0"
  proof (rule order_tendstoI, auto simp add: less_le_trans eventually_sequentially)
    fix e::real assume "e > 0"
    obtain K::nat where "K > 4/e" using reals_Archimedean2 by blast
    obtain L::nat where L: "\<forall>m \<ge> L. \<forall>n \<ge> L. dist (u m) (u n) < e/4"
      using metric_CauchyD[OF \<open>Cauchy u\<close>, of "e/4"] \<open>e > 0\<close> by auto
    {
      fix n assume n: "n \<ge> max K L"
      {
        fix p assume p: "p \<ge> max (N n) L"
        have "dist (u n) (rep_metric_completion (X n) p) < 1/(Suc n)"
          unfolding u_def using N p by simp
        also have "... < e/4"
          using \<open>n \<ge> max K L\<close> \<open>K > 4/e\<close> \<open>e > 0\<close> apply (auto simp add: divide_simps algebra_simps)
          by (metis leD le_less_trans less_add_same_cancel2 linear of_nat_le_iff real_mult_le_cancel_iff2)
        finally have *: "dist (u n) (rep_metric_completion (X n) p) < e/4"
          by fastforce

        have "dist (u p) (rep_metric_completion (X n) p) \<le> dist (u p) (u n) + dist (u n) (rep_metric_completion (X n) p)"
          using dist_triangle by auto
        also have "... < e/4 + e/4" using * L n p by force
        finally have "dist (u p) (rep_metric_completion (X n) p) \<le> e/2" by auto
      }
      then have A: "eventually (\<lambda>p. dist (u p) (rep_metric_completion (X n) p) \<le> e/2) sequentially"
        using eventually_at_top_linorder by blast
      have B: "(\<lambda>p. dist (u p) (rep_metric_completion (X n) p)) \<longlonglongrightarrow> dist (abs_metric_completion u) (X n)"
        using dist_metric_completion_limit'[OF \<open>Cauchy u\<close>, of "rep_metric_completion (X n)"]
        unfolding Quotient3_abs_rep[OF Quotient3_metric_completion, of "X n"]
        using Quotient3_rep_reflp[OF Quotient3_metric_completion] by auto
      have "dist (abs_metric_completion u) (X n) \<le> e/2"
        apply (rule LIMSEQ_le_const2[OF B]) using A unfolding eventually_sequentially by auto
      then have "dist (abs_metric_completion u) (X n) < e" using \<open>e > 0\<close> by auto
    }
    then show "\<exists>N. \<forall>n \<ge> N. dist (abs_metric_completion u) (X n) < e"
      by blast
  qed
  have "X \<longlonglongrightarrow> abs_metric_completion u"
    apply (rule tendstoI) using * by (auto simp add: order_tendsto_iff dist_commute)
  then show "convergent X" unfolding convergent_def by auto
qed

subsection \<open>Isometric embedding of a space in its metric completion\<close>

text \<open>The canonical embedding of a space into its metric completion is obtained by taking
the Cauchy sequence which is constant, equal to the given point. This is indeed an isometric
embedding with dense image, as we prove in the lemmas below.\<close>

definition to_metric_completion::"('a::metric_space) \<Rightarrow> 'a metric_completion"
  where "to_metric_completion x = abs_metric_completion (\<lambda>n. x)"

lemma to_metric_completion_isometry:
  "isometry_on UNIV to_metric_completion"
proof (rule isometry_onI)
  fix x y::'a
  have "(\<lambda>n. dist (x) (y)) \<longlonglongrightarrow> dist (to_metric_completion x) (to_metric_completion y)"
    unfolding to_metric_completion_def apply (rule dist_metric_completion_limit')
    unfolding Cauchy_def by auto
  then show "dist (to_metric_completion x) (to_metric_completion y) = dist x y"
    by (simp add: LIMSEQ_const_iff)
qed

lemma to_metric_completion_dense:
  assumes "open U" "U \<noteq> {}"
  shows "\<exists>x. to_metric_completion x \<in> U"
proof -
  obtain y where "y \<in> U" using \<open>U \<noteq> {}\<close> by auto
  obtain e::real where e: "e > 0" "\<And>z. dist z y < e \<Longrightarrow> z \<in> U"
    using \<open>y \<in> U\<close> \<open>open U\<close> by (metis open_dist)
  have *: "Cauchy (rep_metric_completion y)"
    using Quotient3_metric_completion Quotient3_rep_reflp by fastforce
  then obtain N where N: "\<forall>n \<ge> N. \<forall>m \<ge> N. dist (rep_metric_completion y n) (rep_metric_completion y m) < e/2"
    using \<open>e > 0\<close> unfolding Cauchy_def by (meson divide_pos_pos zero_less_numeral)
  define x where "x = rep_metric_completion y N"
  have "(\<lambda>n. dist x (rep_metric_completion y n)) \<longlonglongrightarrow> dist (to_metric_completion x) (abs_metric_completion (rep_metric_completion y))"
    unfolding to_metric_completion_def apply (rule dist_metric_completion_limit')
    using * unfolding Cauchy_def by auto
  then have "(\<lambda>n. dist x (rep_metric_completion y n)) \<longlonglongrightarrow> dist (to_metric_completion x) y"
    unfolding Quotient3_abs_rep[OF Quotient3_metric_completion] by simp
  moreover have "eventually (\<lambda>n. dist x (rep_metric_completion y n) \<le> e/2) sequentially"
    unfolding eventually_sequentially x_def apply (rule exI[of _ N]) using N less_imp_le by auto
  ultimately have "dist (to_metric_completion x) y \<le> e/2"
    using LIMSEQ_le_const2 unfolding eventually_sequentially by metis
  then have "to_metric_completion x \<in> U"
    using e by auto
  then show ?thesis by auto
qed

lemma to_metric_completion_dense':
  "closure (range to_metric_completion) = UNIV"
apply (auto simp add: closure_iff_nhds_not_empty) using to_metric_completion_dense by fastforce

text \<open>The main feature of the completion is that a uniformly continuous function on the original space can be extended
to a uniformly continuous function on the completion, i.e., it can be written as the composition of
a new function and of the inclusion \verb+to_metric_completion+.\<close>

lemma lift_to_metric_completion:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "uniformly_continuous_on UNIV f"
  shows "\<exists>g. (uniformly_continuous_on UNIV g)
            \<and> (f = g o to_metric_completion)
            \<and> (\<forall>x \<in> range to_metric_completion. g x = f (inv to_metric_completion x))"
proof -
  define I::"'a metric_completion \<Rightarrow> 'a" where "I = inv to_metric_completion"
  have "uniformly_continuous_on (range to_metric_completion) I"
    using isometry_on_uniformly_continuous[OF isometry_on_inverse(1)[OF to_metric_completion_isometry]] I_def
    by auto
  then have UC: "uniformly_continuous_on (range to_metric_completion) (\<lambda>x. f (I x))"
    using assms uniformly_continuous_on_compose
    by (metis I_def bij_betw_imp_surj_on bij_betw_inv_into isometry_on_inverse(4) to_metric_completion_isometry)
  obtain g where g: "uniformly_continuous_on (closure(range to_metric_completion)) g"
                    "\<And>x. x \<in> range to_metric_completion \<Longrightarrow> f (I x) = g x"
    using uniformly_continuous_on_extension_on_closure[OF UC] by metis
  have "uniformly_continuous_on UNIV g"
    using to_metric_completion_dense' g(1) by metis
  moreover have "f x = g (to_metric_completion x)" for x
    using g(2) by (metis I_def UNIV_I isometry_on_inverse(2) range_eqI to_metric_completion_isometry)
  moreover have "g x = f (inv to_metric_completion x)" if "x \<in> range to_metric_completion" for x
    using I_def g(2) that by auto
  ultimately show ?thesis unfolding comp_def by auto
qed

text \<open>When the function is an isometry, the lifted function is also an isometry (and its range is
the closure of the range of the original function).
This shows that the metric completion is unique, up to isometry:\<close>

lemma lift_to_metric_completion_isometry:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "isometry_on UNIV f"
  shows "\<exists>g. isometry_on UNIV g
          \<and> range g = closure(range f)
          \<and> f = g o to_metric_completion
          \<and> (\<forall>x \<in> range to_metric_completion. g x = f (inv to_metric_completion x))"
proof -
  have *: "uniformly_continuous_on UNIV f" using assms isometry_on_uniformly_continuous by force
  obtain g where g: "uniformly_continuous_on UNIV g"
                    "f = g o to_metric_completion"
                    "\<And>x. x \<in> range to_metric_completion \<Longrightarrow> g x = f (inv to_metric_completion x)"
    using lift_to_metric_completion[OF *] by blast
  have *: "isometry_on (range to_metric_completion) g"
    apply (rule isometry_on_cong[OF _ g(3)], rule isometry_on_compose[of _ _ f])
    using assms isometry_on_inverse[OF to_metric_completion_isometry] isometry_on_subset by (auto) (fastforce)
  then have "isometry_on UNIV g"
    unfolding to_metric_completion_dense'[symmetric] apply (rule isometry_on_closure)
    using continuous_on_subset[OF uniformly_continuous_imp_continuous[OF g(1)]] by auto

  have "g`(range to_metric_completion) \<subseteq> range f"
    using g unfolding comp_def by auto
  moreover have "g`(closure (range to_metric_completion)) \<subseteq> closure (g`(range to_metric_completion))"
    using uniformly_continuous_imp_continuous[OF g(1)]
    by (meson closed_closure closure_subset continuous_on_subset image_closure_subset top_greatest)
  ultimately have "range g \<subseteq> closure (range f)"
    unfolding to_metric_completion_dense' by (simp add: g(2) image_comp)

  have "range f \<subseteq> range g"
    using g(2) by auto
  moreover have "closed (range g)"
    using isometry_on_complete_image[OF \<open>isometry_on UNIV g\<close>] by (simp add: complete_eq_closed)
  ultimately have "closure (range f) \<subseteq> range g"
    by (simp add: closure_minimal)
  then have "range g = closure (range f)"
    using \<open>range g \<subseteq> closure (range f)\<close> by auto
  then show ?thesis using \<open>isometry_on UNIV g\<close> g by metis
qed

subsection \<open>The metric completion of a second countable space is second countable\<close>

text \<open>We want to show that the metric completion of a second countable space is still
second countable. This is most easily expressed using the fact that a metric
space is second countable if and only if there exists a dense countable subset. We prove
the equivalence in the next lemma, and use it then to prove that the metric completion is
still second countable.\<close>

lemma second_countable_iff_dense_countable_subset:
  "(\<exists>B::'a::metric_space set set. countable B \<and> topological_basis B)
    \<longleftrightarrow> (\<exists>A::'a set. countable A \<and> closure A = UNIV)"
proof
  assume "\<exists>B::'a set set. countable B \<and> topological_basis B"
  then obtain B::"'a set set" where "countable B" "topological_basis B" by auto
  define A where "A = (\<lambda>U. SOME x. x \<in> U)`B"
  have "countable A" unfolding A_def using \<open>countable B\<close> by auto
  moreover have "closure A = UNIV"
  proof (auto simp add: closure_approachable)
    fix x::'a and e::real assume "e > 0"
    obtain U where "U \<in> B" "x \<in> U" "U \<subseteq> ball x e"
      by (rule topological_basisE[OF \<open>topological_basis B\<close>, of "ball x e" x], auto simp add: \<open>e > 0\<close>)
    define y where "y = (\<lambda>U. SOME x. x \<in> U) U"
    have "y \<in> U" unfolding y_def using \<open>x \<in> U\<close> some_in_eq by fastforce
    then have "dist y x < e"
      using \<open>U \<subseteq> ball x e\<close> by (metis dist_commute mem_ball subset_iff)
    moreover have "y \<in> A" unfolding A_def y_def using \<open>U \<in> B\<close> by auto
    ultimately show "\<exists>y\<in>A. dist y x < e" by auto
  qed
  ultimately show "\<exists>A::'a set. countable A \<and> closure A = UNIV" by auto
next
  assume "\<exists>A::'a set. countable A \<and> closure A = UNIV"
  then obtain A::"'a set" where "countable A" "closure A = UNIV" by auto
  define B where "B = (\<lambda>(x, (n::nat)). ball x (1/n))`(A \<times> UNIV)"
  have "countable B" unfolding B_def using \<open>countable A\<close> by auto
  moreover have "topological_basis B"
  proof (rule topological_basisI)
    fix x::'a and U assume "x \<in> U" "open U"
    then obtain e where "e > 0" "ball x e \<subseteq> U"
      using openE by blast
    obtain n::nat where "n > 2/e" using reals_Archimedean2 by auto
    then have "n > 0" using \<open>e > 0\<close> not_less by fastforce
    then have "1/n > 0" using zero_less_divide_iff by fastforce
    then obtain y where y: "y \<in> A" "dist x y < 1/n"
      by (metis \<open>closure A = UNIV\<close> UNIV_I closure_approachable dist_commute)
    then have "ball y (1/n) \<in> B" unfolding B_def by auto
    moreover have "x \<in> ball y (1/n)" using y(2) by (auto simp add: dist_commute)
    moreover have "ball y (1/n) \<subseteq> U"
    proof (auto)
      fix z assume z: "dist y z < 1/n"
      have "dist z x \<le> dist z y + dist y x" using dist_triangle by auto
      also have "... < 1/n + 1/n" using z y(2) by (auto simp add: dist_commute)
      also have "... < e"
        using \<open>n > 2/e\<close> \<open>e > 0\<close> \<open>n > 0\<close> by (auto simp add: divide_simps mult.commute)
      finally have "z \<in> ball x e" by (auto simp add: dist_commute)
      then show "z \<in> U" using \<open>ball x e \<subseteq> U\<close> by auto
    qed
    ultimately show "\<exists>V\<in>B. x \<in> V \<and> V \<subseteq> U" by metis
  qed (auto simp add: B_def)
  ultimately show "\<exists>B::'a set set. countable B \<and> topological_basis B" by auto
qed

lemma second_countable_metric_dense_subset:
  "\<exists>A::'a::{metric_space, second_countable_topology} set. countable A \<and> closure A = UNIV"
using ex_countable_basis by (auto simp add: second_countable_iff_dense_countable_subset[symmetric])

instance metric_completion::("{metric_space, second_countable_topology}") second_countable_topology
proof
  obtain A::"'a set" where "countable A" "closure A = UNIV"
    using second_countable_metric_dense_subset by auto
  define Ab where "Ab = to_metric_completion`A"
  have "range to_metric_completion \<subseteq> closure Ab"
    unfolding Ab_def
    by (metis \<open>closure A = UNIV\<close> isometry_on_continuous[OF to_metric_completion_isometry] closed_closure closure_subset image_closure_subset)
  then have "closure Ab = UNIV"
    by (metis (no_types) to_metric_completion_dense'[symmetric] \<open>range to_metric_completion \<subseteq> closure Ab\<close> closure_closure closure_mono top.extremum_uniqueI)
  moreover have "countable Ab" unfolding Ab_def using \<open>countable A\<close> by auto
  ultimately have "\<exists>Ab::'a metric_completion set. countable Ab \<and> closure Ab = UNIV"
    by auto
  then show "\<exists>B::'a metric_completion set set. countable B \<and> open = generate_topology B"
    using second_countable_iff_dense_countable_subset topological_basis_imp_subbasis by auto
qed

instance metric_completion::("{metric_space, second_countable_topology}") polish_space
by standard

end (*of theory Metric_Completion*)
