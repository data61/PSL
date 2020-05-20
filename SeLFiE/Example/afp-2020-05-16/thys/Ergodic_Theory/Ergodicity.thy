(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Ergodicity\<close>

theory Ergodicity
  imports Invariants
begin

text \<open>A transformation is \emph{ergodic} if any invariant set has zero measure or full measure.
Ergodic transformations are, in a sense, extremal among measure preserving transformations.
Hence, any transformation can be seen as an average of ergodic ones. This can be made precise
by the notion of ergodic decomposition, only valid on standard measure spaces.

Many statements get nicer in the ergodic case, hence we will reformulate many
of the previous results in this setting.\<close>

subsection \<open>Ergodicity locales\<close>

locale ergodic_qmpt = qmpt +
  assumes ergodic: "\<And>A. A \<in> sets Invariants \<Longrightarrow> (A \<in> null_sets M \<or> space M - A \<in> null_sets M)"

locale ergodic_mpt = mpt + ergodic_qmpt

locale ergodic_fmpt = ergodic_qmpt + fmpt

locale ergodic_pmpt = ergodic_qmpt + pmpt

locale ergodic_conservative = ergodic_qmpt + conservative

locale ergodic_conservative_mpt = ergodic_qmpt + conservative_mpt

sublocale ergodic_fmpt \<subseteq> ergodic_mpt
  by unfold_locales

sublocale ergodic_pmpt \<subseteq> ergodic_fmpt
  by unfold_locales

sublocale ergodic_fmpt \<subseteq> ergodic_conservative_mpt
  by unfold_locales

sublocale ergodic_conservative_mpt \<subseteq> ergodic_conservative
  by unfold_locales

subsection \<open>Behavior of sets in ergodic transformations\<close>

text \<open>The main property of an ergodic transformation, essentially equivalent to the definition,
is that a set which is almost invariant under the dynamics is null or conull.\<close>

lemma (in ergodic_qmpt) AE_equal_preimage_then_null_or_conull:
  assumes [measurable]: "A \<in> sets M" and "A \<Delta> T--`A \<in> null_sets M"
  shows "A \<in> null_sets M \<or> space M - A \<in> null_sets M"
proof -
  obtain B where B: "B \<in> sets Invariants" "A \<Delta> B \<in> null_sets M"
    by (metis Un_commute Invariants_quasi_Invariants_sets[OF assms(1)] assms(2))
  have [measurable]: "B \<in> sets M" using B(1) using Invariants_in_sets by blast
  have *: "B \<in> null_sets M \<or> space M - B \<in> null_sets M" using ergodic B(1) by blast
  show ?thesis
  proof (cases)
    assume "B \<in> null_sets M"
    then have "A \<in> null_sets M" by (metis Un_commute B(2) Delta_null_of_null_is_null[OF assms(1), where ?A = B])
    then show ?thesis by simp
  next
    assume "\<not>(B \<in> null_sets M)"
    then have i: "space M - B \<in> null_sets M" using * by simp
    have "(space M - B) \<Delta> (space M - A) = A \<Delta> B"
      using sets.sets_into_space[OF \<open>A \<in> sets M\<close>] sets.sets_into_space[OF \<open>B \<in> sets M\<close>] by blast
    then have "(space M - B) \<Delta> (space M - A) \<in> null_sets M" using B(2) by auto
    then have "space M - A \<in> null_sets M"
      using Delta_null_of_null_is_null[where ?A = "space M - B" and ?B = "space M - A"] i by auto
    then show ?thesis by simp
  qed
qed

text \<open>The inverse of an ergodic transformation is also ergodic.\<close>

lemma (in ergodic_qmpt) ergodic_Tinv:
  assumes "invertible_qmpt"
  shows "ergodic_qmpt M Tinv"
unfolding ergodic_qmpt_def ergodic_qmpt_axioms_def
proof
  show "qmpt M Tinv" using Tinv_qmpt[OF assms] by simp
  show "\<forall>A. A \<in> sets (qmpt.Invariants M Tinv) \<longrightarrow> A \<in> null_sets M \<or> space M - A \<in> null_sets M"
  proof (intro allI impI)
    fix A assume "A \<in> sets (qmpt.Invariants M Tinv)"
    then have "A \<in> sets Invariants" using Invariants_Tinv[OF assms] by simp
    then show "A \<in> null_sets M \<or> space M - A \<in> null_sets M" using ergodic by auto
  qed
qed

text \<open>In the conservative case, instead of the almost invariance of a set, it suffices to
assume that the preimage is contained in the set, or contains the set, to deduce that it is null
or conull.\<close>

lemma (in ergodic_conservative) preimage_included_then_null_or_conull:
  assumes "A \<in> sets M" "T--`A \<subseteq> A"
  shows "A \<in> null_sets M \<or> space M - A \<in> null_sets M"
proof -
  have "A \<Delta> T--`A \<in> null_sets M" using preimage_included_then_almost_invariant[OF assms] by auto
  then show ?thesis using AE_equal_preimage_then_null_or_conull assms(1) by auto
qed

lemma (in ergodic_conservative) preimage_includes_then_null_or_conull:
  assumes "A \<in> sets M" "T--`A \<supseteq> A"
  shows "A \<in> null_sets M \<or> space M - A \<in> null_sets M"
proof -
  have "A \<Delta> T--`A \<in> null_sets M" using preimage_includes_then_almost_invariant[OF assms] by auto
  then show ?thesis using AE_equal_preimage_then_null_or_conull assms(1) by auto
qed

lemma (in ergodic_conservative) preimages_conull:
  assumes [measurable]: "A \<in> sets M" and "emeasure M A > 0"
  shows "space M - (\<Union>n. (T^^n)--`A) \<in> null_sets M"
        "space M \<Delta> (\<Union>n. (T^^n)--`A) \<in> null_sets M"
proof -
  define B where "B = (\<Union>n. (T^^n)--`A)"
  then have [measurable]: "B \<in> sets M" by auto
  have "T--`B = (\<Union>n. (T^^(n+1))--`A)" unfolding B_def using T_vrestr_composed(2) by auto
  then have "T--`B \<subseteq> B" using B_def by blast
  then have *: "B \<in> null_sets M \<or> space M - B \<in> null_sets M"
    using preimage_included_then_null_or_conull by auto
  have "A \<subseteq> B" unfolding B_def using T_vrestr_0 assms(1) by blast
  then have "emeasure M B > 0" using assms(2)
    by (metis \<open>B \<in> sets M\<close> emeasure_eq_0 zero_less_iff_neq_zero)
  then have "B \<notin> null_sets M" by auto
  then have i: "space M - B \<in> null_sets M" using * by auto
  then show "space M - (\<Union>n. (T^^n)--`A) \<in> null_sets M" using B_def by auto

  have "B \<subseteq> space M" using sets.sets_into_space[OF \<open>B \<in> sets M\<close>] by auto
  then have "space M \<Delta> B \<in> null_sets M" using i by (simp add: Diff_mono sup.absorb1)
  then show "space M \<Delta> (\<Union>n. (T^^n)--`A) \<in> null_sets M" using B_def by auto
qed

subsection \<open>Behavior of functions in ergodic transformations\<close>

text \<open>In the same way that invariant sets are null or conull, invariant functions are almost
everywhere constant in an ergodic transformation. For real functions, one can consider
the set where $\{f x \geq d \}$, it has measure $0$ or $1$ depending on $d$.
Then $f$ is almost surely equal to the maximal $d$ such that this set has measure $1$. For functions
taking values in a general space, the argument is essentially the same, replacing intervals by
a basis of the topology.\<close>

lemma (in ergodic_qmpt) Invariant_func_is_AE_constant:
  fixes f::"_\<Rightarrow> 'b::{second_countable_topology, t1_space}"
  assumes "f \<in> borel_measurable Invariants"
  shows "\<exists>y. AE x in M. f x = y"
proof (cases)
  assume "space M \<in> null_sets M"
  obtain y::'b where "True" by auto
  have "AE x in M. f x = y" using \<open>space M \<in> null_sets M\<close> AE_I' by blast
  then show ?thesis by auto
next
  assume *: "\<not>(space M \<in> null_sets M)"
  obtain B::"'b set set" where B: "countable B" "topological_basis B" using ex_countable_basis by auto
  define C where "C = {b \<in> B. space M - f-`b \<in> null_sets M}"
  then have "countable C" using \<open>countable B\<close> by auto
  define Y where "Y = \<Inter> C"
  have "space M - f-`Y = (\<Union> b\<in> C. space M - f-`b)" unfolding Y_def by auto
  moreover have "\<And>b. b \<in> C \<Longrightarrow> space M - f-`b \<in> null_sets M" unfolding C_def by blast
  ultimately have i: "space M - f-`Y \<in> null_sets M" using \<open>countable C\<close> by (metis null_sets_UN')
  then have "f-`Y \<noteq> {}" using * by auto
  then have "Y \<noteq> {}" by auto
  then obtain y where "y \<in> Y" by auto
  define D where "D = {b \<in> B. y\<notin>b \<and> f-`b \<inter> space M \<in> null_sets M}"
  have "countable D" using \<open>countable B\<close> D_def by auto
  {
    fix z assume "z \<noteq> y"
    obtain U where U: "open U" "z \<in> U" "y \<notin> U"
      using t1_space[OF \<open>z \<noteq> y\<close>] by blast
    obtain V where "V \<in> B" "V \<subseteq> U" "z \<in> V" by (rule topological_basisE[OF \<open>topological_basis B\<close> \<open>open U\<close> \<open>z \<in> U\<close>])
    then have "y \<notin> V" using U by blast
    then have "V \<notin> C" using \<open>y \<in> Y\<close> Y_def by auto
    then have "space M - f-`V \<inter> space M \<notin> null_sets M" unfolding C_def using \<open>V \<in> B\<close>
      by (metis (no_types, lifting) Diff_Int2 inf.idem mem_Collect_eq)
    moreover have "f-`V \<inter> space M \<in> sets Invariants"
      using measurable_sets[OF assms borel_open[OF topological_basis_open[OF B(2) \<open>V \<in> B\<close>]]] subalgebra_def Invariants_is_subalg by metis
    ultimately have "f-`V \<inter> space M \<in> null_sets M" using ergodic by auto
    then have "V \<in> D" unfolding D_def using \<open>V \<in> B\<close> \<open>y \<notin> V\<close> by auto
    then have "\<exists>b \<in> D. z \<in> b" using \<open>z \<in> V\<close> by auto
  }
  then have *: "\<Union>D = UNIV - {y}"
    apply auto unfolding D_def by auto
  have "space M - f-`{y} = f-`(UNIV -{y}) \<inter> space M" by blast
  also have "... = (\<Union>b\<in>D. f-`b \<inter> space M)" using * by auto
  also have "... \<in> null_sets M" using D_def \<open>countable D\<close>
    by (metis (no_types, lifting) mem_Collect_eq null_sets_UN')
  finally have "space M - f-`{y} \<in> null_sets M" by blast
  with AE_not_in[OF this] have "AE x in M. x \<in> f-`{y}" by auto
  then show ?thesis by auto
qed

text \<open>The same goes for functions which are only almost invariant, as they coindice almost
everywhere with genuine invariant functions.\<close>

lemma (in ergodic_qmpt) AE_Invariant_func_is_AE_constant:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, t2_space}"
  assumes "f \<in> borel_measurable M" "AE x in M. f(T x) = f x"
  shows "\<exists>y. AE x in M. f x = y"
proof -
  obtain g where g: "g \<in> borel_measurable Invariants" "AE x in M. f x = g x"
    using Invariants_quasi_Invariants_functions[OF assms(1)] assms(2) by auto
  then obtain y where y: "AE x in M. g x = y" using Invariant_func_is_AE_constant by auto
  have "AE x in M. f x = y" using g(2) y by auto
  then show ?thesis by auto
qed

text \<open>In conservative systems, it suffices to have an inequality between $f$ and $f \circ T$,
since such a function is almost invariant.\<close>

lemma (in ergodic_conservative) AE_decreasing_func_is_AE_constant:
  fixes f::"_ \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  assumes "AE x in M. f(T x) \<le> f x"
    and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>y. AE x in M. f x = y"
proof -
  have "AE x in M. f(T x) = f x" using AE_decreasing_then_invariant[OF assms] by auto
  then show ?thesis using AE_Invariant_func_is_AE_constant[OF assms(2)] by auto
qed

lemma (in ergodic_conservative) AE_increasing_func_is_AE_constant:
  fixes f::"_ \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  assumes "AE x in M. f(T x) \<ge> f x"
    and [measurable]: "f \<in> borel_measurable M"
  shows "\<exists>y. AE x in M. f x = y"
proof -
  have "AE x in M. f(T x) = f x" using AE_increasing_then_invariant[OF assms] by auto
  then show ?thesis using AE_Invariant_func_is_AE_constant[OF assms(2)] by auto
qed

text \<open>When the function takes values in a Banach space, the value of the invariant (hence constant)
function can be recovered by integrating the function.\<close>

lemma (in ergodic_fmpt) Invariant_func_integral:
  fixes f::"_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "f \<in> borel_measurable Invariants"
  shows "integrable M f"
        "AE x in M. f x = (\<integral>x. f x \<partial>M)/\<^sub>R (measure M (space M))"
proof -
  have [measurable]: "f \<in> borel_measurable M" using assms Invariants_measurable_func by blast
  obtain y where y: "AE x in M. f x = y" using Invariant_func_is_AE_constant[OF assms] by auto
  moreover have "integrable M (\<lambda>x. y)" by auto
  ultimately show "integrable M f" by (subst integrable_cong_AE[where ?g = "\<lambda>x. y"], auto)

  have "(\<integral>x. f x \<partial>M) = (\<integral>x. y \<partial>M)" by (subst integral_cong_AE[where ?g = "\<lambda>x. y"], auto simp add: y)
  also have "... = measure M (space M) *\<^sub>R y" by auto
  finally have *: "(\<integral>x. f x \<partial>M) = measure M (space M) *\<^sub>R y" by simp
  show "AE x in M. f x = (\<integral>x. f x \<partial>M)/\<^sub>R (measure M (space M))"
  proof (cases)
    assume "emeasure M (space M) = 0"
    then have "space M \<in> null_sets M" by auto
    then show ?thesis using AE_I' by blast
  next
    assume "\<not>(emeasure M (space M) = 0)"
    then have "measure M (space M) > 0" using emeasure_eq_measure measure_le_0_iff by fastforce
    then have "y = (\<integral>x. f x \<partial>M)/\<^sub>R (measure M (space M))" using * by auto
    then show ?thesis using y by auto
  qed
qed

text \<open>As the conditional expectation of a function and the original function have the same
integral, it follows that the conditional expectation of a function with respect to the
invariant sigma algebra is given by the average of the function.\<close>

lemma (in ergodic_fmpt) Invariants_cond_exp_is_integral_fmpt:
  fixes f::"_ \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. real_cond_exp M Invariants f x = (\<integral>x. f x \<partial>M) / measure M (space M)"
proof -
  have "AE x in M. real_cond_exp M Invariants f x = (\<integral>x. real_cond_exp M Invariants f x \<partial>M)/\<^sub>R (measure M (space M))"
    by (rule Invariant_func_integral(2), simp add: borel_measurable_cond_exp)
  moreover have "(\<integral>x. real_cond_exp M Invariants f x \<partial>M) = (\<integral>x. f x \<partial>M)"
    by (simp add: assms real_cond_exp_int(2))
  ultimately show ?thesis by (simp add: divide_real_def mult.commute)
qed

lemma (in ergodic_pmpt) Invariants_cond_exp_is_integral:
  fixes f::"_ \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. real_cond_exp M Invariants f x = (\<integral>x. f x \<partial>M)"
by (metis div_by_1 prob_space Invariants_cond_exp_is_integral_fmpt[OF assms])


subsection \<open>Kac formula\<close>

text \<open>We reformulate the different versions of Kac formula. They simplify as, for any set $A$
with positive measure, the union $\bigcup T^{-n} A$ (which appears in all these statements)
almost coincides with the whole space.\<close>

lemma (in ergodic_conservative_mpt) local_time_unbounded:
  assumes [measurable]: "A \<in> sets M" "B \<in> sets M"
      and "emeasure M A < \<infinity>" "emeasure M B > 0"
  shows "(\<lambda>n. emeasure M {x \<in> (T^^n)--`A. local_time B n x < k}) \<longlonglongrightarrow> 0"
proof (rule local_time_unbounded3)
  have "A - (\<Union>i. (T ^^ i) --` B) \<in> sets M" by auto
  moreover have "A - (\<Union>i. (T ^^ i) --` B) \<subseteq> space M - (\<Union>i. (T ^^ i) --` B)" using sets.sets_into_space[OF assms(1)] by blast
  ultimately show "A - (\<Union>i. (T ^^ i) --` B) \<in> null_sets M" by (metis null_sets_subset preimages_conull(1)[OF assms(2) assms(4)])
  show "emeasure M A < \<infinity>" using assms(3) by simp
qed (simp_all add: assms)

theorem (in ergodic_conservative_mpt) kac_formula:
  assumes [measurable]: "A \<in> sets M" and "emeasure M A > 0"
  shows "(\<integral>\<^sup>+y. return_time_function A y \<partial>M) = emeasure M (space M)"
proof -
  have a [measurable]: "(\<Union>n. (T^^n)--`A) \<in> sets M" by auto
  then have "space M = (\<Union>n. (T^^n)--`A) \<union> (space M - (\<Union>n. (T^^n)--`A))" using sets.sets_into_space by blast
  then have "emeasure M (space M) = emeasure M (\<Union>n. (T^^n)--`A)"
    by (metis a preimages_conull(1)[OF assms] emeasure_Un_null_set)
  moreover have "(\<integral>\<^sup>+y. return_time_function A y \<partial>M) = emeasure M (\<Union>n. (T^^n)--`A)"
    using kac_formula_nonergodic[OF assms(1)] by simp
  ultimately show ?thesis by simp
qed

lemma (in ergodic_conservative_mpt) induced_function_integral:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "A \<in> sets M" "integrable M f" and "emeasure M A > 0"
  shows "integrable M (induced_function A f)"
        "(\<integral>y. induced_function A f y \<partial>M) = (\<integral> x. f x \<partial>M)"
proof -
  show "integrable M (induced_function A f)"
    using induced_function_integral_nonergodic(1)[OF assms(1) assms(2)] by auto
  have "(\<integral>y. induced_function A f y \<partial>M) = (\<integral> x \<in> (\<Union>n. (T^^n)--`A). f x \<partial>M)"
    using induced_function_integral_nonergodic(2)[OF assms(1) assms(2)] by auto
  also have "... = (\<integral> x \<in> space M. f x \<partial>M)"
    using set_integral_null_delta[OF assms(2), where ?A = "space M" and ?B = "(\<Union>n. (T^^n)--`A)"]
    preimages_conull(2)[OF assms(1) assms(3)] by auto
  also have "... = (\<integral> x. f x \<partial>M)" using set_integral_space[OF assms(2)] by auto
  finally show "(\<integral>y. induced_function A f y \<partial>M) = (\<integral> x. f x \<partial>M)" by simp
qed

lemma (in ergodic_conservative_mpt) induced_function_integral_restr:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "A \<in> sets M" "integrable M f" and "emeasure M A > 0"
  shows "integrable (restrict_space M A) (induced_function A f)"
        "(\<integral>y. induced_function A f y \<partial>(restrict_space M A)) = (\<integral> x. f x \<partial>M)"
proof -
  show "integrable (restrict_space M A) (induced_function A f)"
    using induced_function_integral_restr_nonergodic(1)[OF assms(1) assms(2)] by auto
  have "(\<integral>y. induced_function A f y \<partial>(restrict_space M A)) = (\<integral> x \<in> (\<Union>n. (T^^n)--`A). f x \<partial>M)"
    using induced_function_integral_restr_nonergodic(2)[OF assms(1) assms(2)] by auto
  also have "... = (\<integral> x \<in> space M. f x \<partial>M)"
    using set_integral_null_delta[OF assms(2), where ?A = "space M" and ?B = "(\<Union>n. (T^^n)--`A)"]
    preimages_conull(2)[OF assms(1) assms(3)] by auto
  also have "... = (\<integral> x. f x \<partial>M)" using set_integral_space[OF assms(2)] by auto
  finally show "(\<integral>y. induced_function A f y \<partial>(restrict_space M A)) = (\<integral> x. f x \<partial>M)" by simp
qed

subsection \<open>Birkhoff theorem\<close>

text \<open>The general versions of Birkhoff theorem are formulated in terms of conditional expectations.
In ergodic probability measure preserving transformations (the most common setting), they
reduce to simpler versions that we state now, as the conditional expectations are simply the
averages of the functions.\<close>

theorem (in ergodic_pmpt) birkhoff_theorem_AE:
  fixes f::"'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> (\<integral> x. f x \<partial>M)"
proof -
  have "AE x in M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    using birkhoff_theorem_AE_nonergodic[OF assms] by simp
  moreover have "AE x in M. real_cond_exp M Invariants f x = (\<integral> x. f x \<partial>M)"
    using Invariants_cond_exp_is_integral[OF assms] by auto
  ultimately show ?thesis by auto
qed

theorem (in ergodic_pmpt) birkhoff_theorem_L1:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "(\<lambda>n. \<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - (\<integral> x. f x \<partial>M)) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  {
    fix n::nat
    have "AE x in M. real_cond_exp M Invariants f x = (\<integral> x. f x \<partial>M)"
      using Invariants_cond_exp_is_integral[OF assms] by auto
    then have *: "AE x in M. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x)
                = norm(birkhoff_sum f n x / n - (\<integral> x. f x \<partial>M))"
      by auto
    have "(\<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M)
                = (\<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - (\<integral> x. f x \<partial>M)) \<partial>M)"
      apply (rule nn_integral_cong_AE) using * by auto
  }
  moreover have "(\<lambda>n. \<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<longlonglongrightarrow> 0"
    using birkhoff_theorem_L1_nonergodic[OF assms] by auto
  ultimately show ?thesis by simp
qed

theorem (in ergodic_pmpt) birkhoff_sum_small_asymp_pos:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" and "e>0"
  shows "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) .. n * (\<integral>x. f x \<partial>M) + e}}"
proof -
  have "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x .. n * real_cond_exp M Invariants f x + e}}"
    using birkhoff_sum_small_asymp_pos_nonergodic[OF assms] by simp
  moreover have "AE x in M. real_cond_exp M Invariants f x = (\<integral>x. f x \<partial>M)"
    using Invariants_cond_exp_is_integral[OF assms(1)] by auto
  ultimately show ?thesis by auto
qed

theorem (in ergodic_pmpt) birkhoff_sum_small_asymp_neg:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" and "e>0"
  shows "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) - e .. n * (\<integral>x. f x \<partial>M)}}"
proof -
  have "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x - e .. n * real_cond_exp M Invariants f x}}"
    using birkhoff_sum_small_asymp_neg_nonergodic[OF assms] by simp
  moreover have "AE x in M. real_cond_exp M Invariants f x = (\<integral>x. f x \<partial>M)"
    using Invariants_cond_exp_is_integral[OF assms(1)] by auto
  ultimately show ?thesis by auto
qed

lemma (in ergodic_pmpt) birkhoff_positive_average:
      fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" and "AE x in M. (\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> \<infinity>"
  shows "(\<integral> x. f x \<partial>M) > 0"
proof (rule ccontr)
  assume "\<not>((\<integral> x. f x \<partial>M) > 0)"
  then have *: "(\<integral> x. f x \<partial>M) \<le> 0" by simp

  have "AE x in M. (\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> \<infinity> \<and> infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) - 1 .. n* (\<integral>x. f x \<partial>M)}}"
    using assms(2) birkhoff_sum_small_asymp_neg[OF assms(1)] by auto
  then obtain x where x: "(\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> \<infinity>" "infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) - 1 .. n* (\<integral>x. f x \<partial>M)}}"
    using AE_False eventually_elim2 by blast
  {
    fix n assume "birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) - 1 .. n * (\<integral>x. f x \<partial>M)}"
    then have "birkhoff_sum f n x \<le> n * (\<integral>x. f x \<partial>M)" by simp
    also have "... \<le> 0" using * by (simp add: mult_nonneg_nonpos)
    finally have "birkhoff_sum f n x \<le> 0" by simp
  }
  then have "{n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) - 1 .. n* (\<integral>x. f x \<partial>M)}} \<subseteq> {n. birkhoff_sum f n x \<le> 0}" by auto
  then have inf: "infinite {n. birkhoff_sum f n x \<le> 0}" using x(2) finite_subset by blast

  have "0 < (\<infinity>::ereal)" by auto
  then have "eventually (\<lambda>n. birkhoff_sum f n x > (0::ereal)) sequentially" using x(1) order_tendsto_iff by metis
  then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> birkhoff_sum f n x > (0::ereal)" by (meson eventually_at_top_linorder)
  then have "\<And>n. n \<ge> N \<Longrightarrow> birkhoff_sum f n x > 0" by auto
  then have "{n. birkhoff_sum f n x \<le> 0} \<subseteq> {..<N}" by (metis (mono_tags, lifting) lessThan_iff linorder_not_less mem_Collect_eq subsetI)
  then have "finite {n. birkhoff_sum f n x \<le> 0}" using finite_nat_iff_bounded by blast

  then show "False" using inf by simp
qed

lemma (in ergodic_pmpt) birkhoff_negative_average:
      fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" and "AE x in M. (\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> -\<infinity>"
  shows "(\<integral> x. f x \<partial>M) < 0"
proof (rule ccontr)
  assume "\<not>((\<integral> x. f x \<partial>M) < 0)"
  then have *: "(\<integral> x. f x \<partial>M) \<ge> 0" by simp

  have "AE x in M. (\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> -\<infinity> \<and> infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) .. n* (\<integral>x. f x \<partial>M) + 1}}"
    using assms(2) birkhoff_sum_small_asymp_pos[OF assms(1)] by auto
  then obtain x where x: "(\<lambda>n. birkhoff_sum f n x) \<longlonglongrightarrow> -\<infinity>" "infinite {n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) .. n* (\<integral>x. f x \<partial>M) + 1}}"
    using AE_False eventually_elim2 by blast
  {
    fix n assume "birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) .. n * (\<integral>x. f x \<partial>M) + 1}"
    then have "birkhoff_sum f n x \<ge> n * (\<integral>x. f x \<partial>M)" by simp
    moreover have "n * (\<integral>x. f x \<partial>M) \<ge> 0" using * by simp
    ultimately have "birkhoff_sum f n x \<ge> 0" by simp
  }
  then have "{n. birkhoff_sum f n x \<in> {n * (\<integral>x. f x \<partial>M) .. n* (\<integral>x. f x \<partial>M) + 1}} \<subseteq> {n. birkhoff_sum f n x \<ge> 0}" by auto
  then have inf: "infinite {n. birkhoff_sum f n x \<ge> 0}" using x(2) finite_subset by blast

  have "0 > (-\<infinity>::ereal)" by auto
  then have "eventually (\<lambda>n. birkhoff_sum f n x < (0::ereal)) sequentially" using x(1) order_tendsto_iff by metis
  then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> birkhoff_sum f n x < (0::ereal)" by (meson eventually_at_top_linorder)
  then have "\<And>n. n \<ge> N \<Longrightarrow> birkhoff_sum f n x < 0" by auto
  then have "{n. birkhoff_sum f n x \<ge> 0} \<subseteq> {..<N}" by (metis (mono_tags, lifting) lessThan_iff linorder_not_less mem_Collect_eq subsetI)
  then have "finite {n. birkhoff_sum f n x \<ge> 0}" using finite_nat_iff_bounded by blast

  then show "False" using inf by simp
qed

lemma (in ergodic_pmpt) birkhoff_nonzero_average:
      fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" and "AE x in M. (\<lambda>n. abs(birkhoff_sum f n x)) \<longlonglongrightarrow> \<infinity>"
  shows "(\<integral> x. f x \<partial>M) \<noteq> 0"
proof (rule ccontr)
  assume "\<not>((\<integral> x. f x \<partial>M) \<noteq> 0)"
  then have *: "(\<integral> x. f x \<partial>M) = 0" by simp

  have "AE x in M. (\<lambda>n. abs(birkhoff_sum f n x)) \<longlonglongrightarrow> \<infinity> \<and> infinite {n. birkhoff_sum f n x \<in> {0 .. 1}}"
    using assms(2) birkhoff_sum_small_asymp_pos[OF assms(1)] * by auto
  then obtain x where x: "(\<lambda>n. abs(birkhoff_sum f n x)) \<longlonglongrightarrow> \<infinity>" "infinite {n. birkhoff_sum f n x \<in> {0 .. 1}}"
    using AE_False eventually_elim2 by blast

  have "1 < (\<infinity>::ereal)" by auto
  then have "eventually (\<lambda>n. abs(birkhoff_sum f n x) > (1::ereal)) sequentially" using x(1) order_tendsto_iff by metis
  then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> abs(birkhoff_sum f n x) > (1::ereal)" by (meson eventually_at_top_linorder)
  then have *: "\<And>n. n \<ge> N \<Longrightarrow> abs(birkhoff_sum f n x) > 1" by auto
  have "{n. birkhoff_sum f n x \<in> {0..1}} \<subseteq> {..<N}" by (auto, metis (full_types) * abs_of_nonneg not_less)
  then have "finite {n. birkhoff_sum f n x \<in> {0..1}}" using finite_nat_iff_bounded by blast

  then show "False" using x(2) by simp
qed

end (*of Ergodicity.thy*)
