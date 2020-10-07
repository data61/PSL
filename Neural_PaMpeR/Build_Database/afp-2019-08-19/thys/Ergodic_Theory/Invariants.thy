(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>The invariant sigma-algebra, Birkhoff theorem\<close>

theory Invariants
  imports Recurrence "HOL-Probability.Conditional_Expectation"
begin

subsection \<open>The sigma-algebra of invariant subsets\<close>

text \<open>The invariant sigma-algebra of a qmpt is made of those sets that are invariant under the
dynamics. When the transformation is ergodic, it is made of sets of zero or full measure. In
general, the Birkhoff theorem is expressed in terms of the conditional expectation of an integrable
function with respect to the invariant sigma-algebra.\<close>

context qmpt begin

text \<open>We define the invariant sigma-algebra, as the sigma algebra of sets which are invariant
under the dynamics, i.e., they coincide with their preimage under $T$.\<close>

definition Invariants where "Invariants = sigma (space M) {A \<in> sets M. T-`A \<inter> space M = A}"

text \<open>For this definition to make sense, we need to check that it really defines a sigma-algebra:
otherwise, the \verb+sigma+ operation would make garbage out of it. This is the content of the next
lemma.\<close>

lemma Invariants_sets: "sets Invariants = {A \<in> sets M. T-`A \<inter> space M = A}"
proof -
  have "sigma_algebra (space M) {A \<in> sets M. T-`A \<inter> space M = A}"
  proof -
    define I where "I = {A. T-`A \<inter> space M = A}"
    have i: "\<And>A. A \<in> I \<Longrightarrow> A \<subseteq> space M" unfolding I_def by auto
    have "algebra (space M) I"
    proof (subst algebra_iff_Un)
      have a: "I \<subseteq> Pow (space M)" using i by auto
      have b: "{} \<in> I" unfolding I_def by auto
      {
        fix A assume *: "A \<in> I"
        then have "T-`(space M - A) = T-`(space M) - T-`A" by auto
        then have "T-`(space M - A) \<inter> space M = T-`(space M) \<inter> (space M) - T-`A \<inter> (space M)" by auto
        also have "... = space M - A" using * I_def by (simp add: inf_absorb2 subsetI)
        finally have "space M - A \<in> I" unfolding I_def by simp
      }
      then have c: "(\<forall>a\<in>I. space M - a \<in> I)" by simp
      have d: "(\<forall>a\<in>I. \<forall>b\<in>I. a \<union> b \<in> I)" unfolding I_def by auto
      show "I \<subseteq> Pow (space M) \<and> {} \<in> I \<and> (\<forall>a\<in>I. space M - a \<in> I) \<and> (\<forall>a\<in>I. \<forall>b\<in>I. a \<union> b \<in> I)"
        using a b c d by blast
    qed
    moreover have "(\<forall>F. range F \<subseteq> I \<longrightarrow> (\<Union>i::nat. F i) \<in> I)" unfolding I_def by auto
    ultimately have "sigma_algebra (space M) I" using sigma_algebra_iff by auto
    moreover have "sigma_algebra (space M) (sets M)" using measure_space measure_space_def by auto
    ultimately have "sigma_algebra (space M) (I \<inter> (sets M))" using sigma_algebra_intersection by auto
    moreover have "I \<inter> sets M = {A \<in> sets M. T-`A \<inter> space M = A}" unfolding I_def by auto
    ultimately show ?thesis by simp
  qed
  then show ?thesis unfolding Invariants_def using sigma_algebra.sets_measure_of_eq by blast
qed

text \<open>By definition, the invariant subalgebra is a subalgebra of the original algebra. This is
expressed in the following lemmas.\<close>

lemma Invariants_is_subalg: "subalgebra M Invariants"
  unfolding subalgebra_def
  using Invariants_sets Invariants_def by (simp add: space_measure_of_conv)

lemma Invariants_in_sets:
  assumes "A \<in> sets Invariants"
  shows "A \<in> sets M"
using Invariants_sets assms by blast

lemma Invariants_measurable_func:
  assumes "f \<in> measurable Invariants N"
  shows "f \<in> measurable M N"
using Invariants_is_subalg measurable_from_subalg assms by auto

text \<open>We give several trivial characterizations of invariant sets or functions.\<close>

lemma Invariants_vrestr:
  assumes "A \<in> sets Invariants"
  shows "T--`A = A"
using assms Invariants_sets Invariants_in_sets[OF assms] by auto

lemma Invariants_points:
  assumes "A \<in> sets Invariants" "x \<in> A"
  shows "T x \<in> A"
using assms Invariants_sets by auto

lemma Invariants_func_is_invariant:
  fixes f::"_ \<Rightarrow> 'b::t2_space"
  assumes "f \<in> borel_measurable Invariants" "x \<in> space M"
  shows "f (T x) = f x"
proof -
  have "{f x} \<in> sets borel" by simp
  then have "f-`({f x}) \<inter> space M \<in> Invariants" using assms(1)
    by (metis (no_types, lifting) Invariants_def measurable_sets space_measure_of_conv)
  moreover have "x \<in> f-`({f x}) \<inter> space M" using assms(2) by blast
  ultimately have "T x \<in> f-`({f x}) \<inter> space M" by (rule Invariants_points)
  then show ?thesis by simp
qed

lemma Invariants_func_is_invariant_n:
  fixes f::"_ \<Rightarrow> 'b::t2_space"
  assumes "f \<in> borel_measurable Invariants" "x \<in> space M"
  shows "f ((T^^n) x) = f x"
by (induction n, auto simp add: assms Invariants_func_is_invariant)

lemma Invariants_func_charac:
  assumes [measurable]: "f \<in> measurable M N"
      and "\<And>x. x \<in> space M \<Longrightarrow> f(T x) = f x"
  shows "f \<in> measurable Invariants N"
proof (rule measurableI)
  fix A assume "A \<in> sets N"
  have "space Invariants = space M" using Invariants_is_subalg subalgebra_def by force
  show "f -` A \<inter> space Invariants \<in> sets Invariants"
    apply (subst Invariants_sets)
    apply (auto simp add: assms \<open>A \<in> sets N\<close> \<open>space Invariants = space M\<close>)
    using \<open>A \<in> sets N\<close> assms(1) measurable_sets by blast
next
  fix x assume "x \<in> space Invariants"
  have "space Invariants = space M" using Invariants_is_subalg subalgebra_def by force
  then show "f x \<in> space N" using assms(1) \<open>x \<in> space Invariants\<close> by (metis measurable_space)
qed

lemma birkhoff_sum_of_invariants:
  fixes f::" _ \<Rightarrow> real"
  assumes "f \<in> borel_measurable Invariants" "x \<in> space M"
  shows "birkhoff_sum f n x = n * f x"
unfolding birkhoff_sum_def using Invariants_func_is_invariant_n[OF assms] by auto

text \<open>There are two possible definitions of the invariant sigma-algebra, competing in the
literature: one could also use the sets such that $T^{-1}A$ coincides with $A$ up to
a measure $0$ set. It turns out that this is equivalent to being invariant (in our sense) up
to a measure $0$ set. Therefore, for all interesting purposes, the two definitions would
give the same results.

For the proof, we start from an almost invariant set, and build a genuinely invariant set that
coincides with it by adding or throwing away null parts.
\<close>

proposition Invariants_quasi_Invariants_sets:
  assumes [measurable]: "A \<in> sets M"
  shows "(\<exists>B \<in> sets Invariants. A \<Delta> B \<in> null_sets M) \<longleftrightarrow> (T--`A \<Delta> A \<in> null_sets M)"
proof
  assume "\<exists>B \<in> sets Invariants. A \<Delta> B \<in> null_sets M"
  then obtain B where "B \<in> sets Invariants" "A \<Delta> B \<in> null_sets M" by auto
  then have [measurable]: "B \<in> sets M" using Invariants_in_sets by simp

  have "B = T--` B" using Invariants_vrestr \<open>B \<in> sets Invariants\<close> by simp
  then have "T--`A \<Delta> B = T--`(A \<Delta> B)" by simp
  moreover have "T--`(A \<Delta> B) \<in> null_sets M"
    by (rule T_quasi_preserves_null2(1)[OF \<open>A \<Delta> B \<in> null_sets M\<close>])
  ultimately have "T--`A \<Delta> B \<in> null_sets M" by simp
  then show "T--`A \<Delta> A \<in> null_sets M"
    by (rule null_sym_diff_transitive) (auto simp add: \<open>A \<Delta> B \<in> null_sets M\<close> Un_commute)
next
  assume H: "T --` A \<Delta> A \<in> null_sets M"
  have [measurable]: "\<And>n. (T^^n)--`A \<in> sets M" by simp
  {
    fix K assume [measurable]: "K \<in> sets M" and "T--`K \<Delta> K \<in> null_sets M"
    fix n::nat
    have "(T^^n)--`K \<Delta> K \<in> null_sets M"
    proof (induction n)
      case 0
      have "(T^^0)--` K = K" using T_vrestr_0 by simp
      then show ?case using Diff_cancel sup.idem by (metis null_sets.empty_sets)
    next
      case (Suc n)
      have "T--`((T^^n)--`K \<Delta> K) \<in> null_sets M"
        using Suc.IH T_quasi_preserves_null(1)[of "((T^^n)--`K \<Delta> K)"] by simp
      then have *: "(T^^(Suc n))--`K \<Delta> T--`K \<in> null_sets M" using T_vrestr_composed(2)[OF \<open>K \<in> sets M\<close>] by simp
      then show ?case
        by (rule null_sym_diff_transitive, simp add: \<open>T--`K \<Delta> K \<in> null_sets M\<close> \<open>K \<in> sets M\<close>, measurable)
    qed
  } note * = this

  define C where "C = (\<Inter>n. (T^^n)--`A)"
  have [measurable]: "C \<in> sets M" unfolding C_def by simp
  have "C \<Delta> A \<subseteq> (\<Union>n. (T^^n)--`A \<Delta> A)" unfolding C_def by auto
  moreover have "(\<Union>n. (T^^n)--`A \<Delta> A) \<in> null_sets M"
    using * null_sets_UN assms \<open>T --` A \<Delta> A \<in> null_sets M\<close> by auto
  ultimately have CA: "C \<Delta> A \<in> null_sets M" by (meson \<open>C \<in> sets M\<close> assms sets.Diff sets.Un null_sets_subset)
  then have "T--`(C \<Delta> A) \<in> null_sets M" by (rule T_quasi_preserves_null2(1))
  then have "T--`C \<Delta> T--`A \<in> null_sets M" by simp
  then have "T--`C \<Delta> A \<in> null_sets M"
    by (rule null_sym_diff_transitive, auto simp add: H)
  then have TCC: "T--`C \<Delta> C \<in> null_sets M"
    apply (rule null_sym_diff_transitive) using CA by (auto simp add: Un_commute)

  have "C \<subseteq> (\<Inter>n\<in>{1..}. (T^^n)--`A)" unfolding C_def by auto
  moreover have "T--`C = (\<Inter>n\<in>{1..}. (T^^n)--`A)"
    using T_vrestr_composed(2)[OF assms] by (simp add: C_def atLeast_Suc_greaterThan greaterThan_0)
  ultimately have "C \<subseteq> T--`C" by blast
  then have "(T^^0)--`C \<subseteq> (T^^1)--`C" using T_vrestr_0 by auto
  moreover have "(T^^1)--`C \<subseteq> (\<Union>n\<in>{1..}. (T^^n)--`C)" by auto
  ultimately have "(T^^0)--`C \<subseteq> (\<Union>n\<in>{1..}. (T^^n)--`C)" by auto
  then have "(T^^0)--`C \<union> (\<Union>n\<in>{1..}. (T^^n)--`C) = (\<Union>n\<in>{1..}. (T^^n)--`C)" by auto
  moreover have "(\<Union>n. (T^^n)--`C) = (T^^0)--`C \<union> (\<Union>n\<in>{1..}. (T^^n)--`C)" by (rule union_insert_0)
  ultimately have C2: "(\<Union>n. (T^^n)--`C) = (\<Union>n\<in>{1..}. (T^^n)--`C)" by simp

  define B where "B = (\<Union>n. (T^^n)--`C)"
  have [measurable]: "B \<in> sets M" unfolding B_def by simp
  have "B \<Delta> C \<subseteq> (\<Union>n. (T^^n)--`C \<Delta> C)" unfolding B_def by auto
  moreover have "(\<Union>n. (T^^n)--`C \<Delta> C) \<in> null_sets M"
    using * null_sets_UN assms TCC by auto
  ultimately have "B \<Delta> C \<in> null_sets M" by (meson \<open>B \<in> sets M\<close> \<open>C \<in> sets M\<close> assms sets.Diff sets.Un null_sets_subset)
  then have "B \<Delta> A \<in> null_sets M"
    by (rule null_sym_diff_transitive, auto simp add: CA)
  then have a: "A \<Delta> B \<in> null_sets M" by (simp add: Un_commute)

  have "T--`B = (\<Union>n\<in>{1..}. (T^^n)--`C)"
    using T_vrestr_composed(2)[OF \<open>C \<in> sets M\<close>] by (simp add: B_def atLeast_Suc_greaterThan greaterThan_0)
  then have "T--`B = B" unfolding B_def using C2 by simp
  then have "B \<in> sets Invariants" using Invariants_sets vimage_restr_def by auto

  then show "\<exists>B \<in> sets Invariants. A \<Delta> B \<in> null_sets M" using a by blast
qed

text \<open>In a conservative setting, it is enough to be included in its image or its preimage to be
almost invariant: otherwise, since the difference set has disjoint preimages, and is therefore
null by conservativity.\<close>

lemma (in conservative) preimage_included_then_almost_invariant:
  assumes [measurable]: "A \<in> sets M" and "T--`A \<subseteq> A"
  shows "A \<Delta> (T--`A) \<in> null_sets M"
proof -
  define B where "B = A - T--`A"
  then have [measurable]: "B \<in> sets M" by simp
  have "(T^^(Suc n))--`A \<subseteq> (T^^n)--`A" for n using T_vrestr_composed(3)[OF assms(1)] vrestr_inclusion[OF assms(2)] by auto
  then have "disjoint_family (\<lambda>n. (T^^n)--`A - (T^^(Suc n))--`A)" by (rule disjoint_family_Suc2[where ?A = "\<lambda>n. (T^^n)--`A"])
  moreover have "(T^^n)--`A - (T^^(Suc n))--`A = (T^^n)--`B" for n unfolding B_def Suc_eq_plus1 using T_vrestr_composed(3)[OF assms(1)] by auto
  ultimately have "disjoint_family (\<lambda>n. (T^^n)--` B)" by simp
  then have "\<And>n. n \<noteq> 0 \<Longrightarrow> ((T^^n)--`B) \<inter> B = {}" unfolding disjoint_family_on_def by (metis UNIV_I T_vrestr_0(1)[OF \<open>B \<in> sets M\<close>])
  then have "\<And>n. n > 0 \<Longrightarrow> (T^^n)-`B \<inter> B = {}" unfolding vimage_restr_def by (simp add: Int_assoc)
  then have "B \<in> null_sets M" using disjoint_then_null[OF \<open>B \<in> sets M\<close>] Int_commute by auto
  then show ?thesis unfolding B_def using assms(2) by (simp add: Diff_mono Un_absorb2)
qed

lemma (in conservative) preimage_includes_then_almost_invariant:
  assumes [measurable]: "A \<in> sets M" and "A \<subseteq> T--`A"
  shows "A \<Delta> (T--`A) \<in> null_sets M"
proof -
  define B where "B = T--`A - A"
  then have [measurable]: "B \<in> sets M" by simp
  have "\<And>n. (T^^(Suc n))--`A \<supseteq> (T^^n)--`A" using T_vrestr_composed(3)[OF assms(1)] vrestr_inclusion[OF assms(2)] by auto
  then have "disjoint_family (\<lambda>n. (T^^(Suc n))--`A - (T^^n)--`A)" by (rule disjoint_family_Suc[where ?A = "\<lambda>n. (T^^n)--`A"])
  moreover have "\<And>n. (T^^(Suc n))--`A - (T^^n)--`A = (T^^n)--`B" unfolding B_def Suc_eq_plus1 using T_vrestr_composed(3)[OF assms(1)] by auto
  ultimately have "disjoint_family (\<lambda>n. (T^^n)--` B)" by simp
  then have "\<And>n. n \<noteq> 0 \<Longrightarrow> ((T^^n)--`B) \<inter> B = {}" unfolding disjoint_family_on_def by (metis UNIV_I T_vrestr_0(1)[OF \<open>B \<in> sets M\<close>])
  then have "\<And>n. n > 0 \<Longrightarrow> (T^^n)-`B \<inter> B = {}" unfolding vimage_restr_def by (simp add: Int_assoc)
  then have "B \<in> null_sets M" using disjoint_then_null[OF \<open>B \<in> sets M\<close>] Int_commute by auto
  then show ?thesis unfolding B_def using assms(2) by (simp add: Diff_mono Un_absorb1)
qed

text \<open>The above properties for sets are also true for functions: if $f$ and $f \circ T$
coincide almost everywhere, i.e., $f$ is almost invariant, then $f$ coincides almost everywhere
with a true invariant function.

The idea of the proof is straightforward: throw away the orbits on
which $f$ is not really invariant (say this is the complement of the good set),
and replace it by $0$ there. However, this does not work
directly: the good set is not invariant, some points may have a non-constant value of $f$ on their
orbit but reach the good set eventually. One can however define $g$ to be equal to the
eventual value of $f$ along the orbit, if the orbit reaches the good set, and $0$ elsewhere.\<close>

proposition Invariants_quasi_Invariants_functions:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, t2_space}"
  assumes f_meas [measurable]: "f \<in> borel_measurable M"
  shows "(\<exists>g \<in> borel_measurable Invariants. AE x in M. f x = g x) \<longleftrightarrow> (AE x in M. f(T x) = f x)"
proof
  assume "\<exists>g\<in>borel_measurable Invariants. AE x in M. f x = g x"
  then obtain g where g:"g\<in>borel_measurable Invariants" "AE x in M. f x = g x" by blast
  then have [measurable]: "g \<in> borel_measurable M" using Invariants_measurable_func by auto
  define A where "A = {x \<in> space M. f x = g x}"
  have [measurable]: "A \<in> sets M" unfolding A_def by simp
  define B where "B = space M - A"
  have [measurable]: "B \<in> sets M" unfolding B_def by simp
  moreover have "AE x in M. x \<notin> B" unfolding B_def A_def using g(2) by auto
  ultimately have "B \<in> null_sets M" using AE_iff_null_sets by blast
  then have "T--`B \<in> null_sets M" by (rule T_quasi_preserves_null2(1))
  then have "B \<union> T--`B \<in> null_sets M" using \<open>B \<in> null_sets M\<close> by auto
  then have "AE x in M. x \<notin> (B \<union> T--`B)" using AE_iff_null_sets null_setsD2 by blast
  then have i: "AE x in M. x \<in> space M - (B \<union> T--`B)" by auto
  {
    fix x assume *: "x \<in> space M - (B \<union> T--`B)"
    then have "x \<in> A" unfolding B_def by blast
    then have "f x = g x" unfolding A_def by blast
    have "T x \<in> A" using * B_def by auto
    then have "f(T x) = g(T x)" unfolding A_def by blast
    moreover have "g(T x) = g x"
      apply (rule Invariants_func_is_invariant) using * by (auto simp add: assms \<open>g\<in>borel_measurable Invariants\<close>)
    ultimately have "f(T x) = f x" using \<open>f x = g x\<close> by simp
  }
  then show "AE x in M. f(T x) = f x" using i by auto
next
  assume *: "AE x in M. f (T x) = f x"
  text \<open>\verb+good_set+ is the set of points for which $f$ is constant on their orbit. Here, we define
  $g = f$. If a point ever enters \verb+good_set+, then we take $g$ to be the value of $f$ there. Otherwise,
  $g$ takes an arbitrary value, say $y_0$.\<close>
  define good_set where "good_set = {x \<in> space M. \<forall>n. f((T^^(Suc n)) x) = f((T^^n) x)}"
  define good_time where "good_time = (\<lambda>x. Inf {n. (T^^n) x \<in> good_set})"
  have "AE x in M. x \<in> good_set" using T_AE_iterates[OF *] by (simp add: good_set_def)
  have [measurable]: "good_set \<in> sets M" unfolding good_set_def by auto
  obtain y0::'b where True by auto
  define g where "g = (\<lambda>x. if (\<exists>n. (T^^n) x \<in> good_set) then f((T^^(good_time x)) x) else y0)"
  have [measurable]: "good_time \<in> measurable M (count_space UNIV)" unfolding good_time_def by measurable
  have [measurable]: "g \<in> borel_measurable M" unfolding g_def by measurable

  have "f x = g x" if "x \<in> good_set" for x
  proof -
    have a: "0 \<in> {n. (T^^n) x \<in> good_set}" using that by simp
    have "good_time x = 0"
      unfolding good_time_def apply (intro cInf_eq_non_empty) using a by blast+
    moreover have "{n. (T^^n) x \<in> good_set} \<noteq> {}" using a by blast
    ultimately show "f x = g x" unfolding g_def by auto
  qed
  then have "AE x in M. f x = g x" using \<open>AE x in M. x \<in> good_set\<close> by auto

  have *: "f((T^^(Suc 0)) x) = f((T^^0) x)" if "x \<in> good_set" for x
    using that unfolding good_set_def by blast
  have good_1: "T x \<in> good_set \<and> f(T x) = f x" if "x \<in> good_set" for x
    using *[OF that] that unfolding good_set_def apply (auto)
    unfolding T_Tn_T_compose by blast
  then have good_k: "\<And>x. x \<in> good_set \<Longrightarrow> (T^^k) x \<in> good_set \<and> f((T^^k) x) = f x" for k
      by (induction k, auto)

  have "g(T x) = g x" if "x \<in> space M" for x
  proof (cases)
    assume *: "\<exists>n. (T^^n) (T x) \<in> good_set"
    define n where "n = Inf {n. (T^^n) (T x) \<in> good_set}"
    have "(T^^n)(T x) \<in> good_set" using * Inf_nat_def1 by (metis empty_iff mem_Collect_eq n_def)
    then have a: "(T^^(n+1)) x \<in> good_set" by (metis Suc_eq_plus1 comp_eq_dest_lhs funpow.simps(2) funpow_swap1)
    then have **: "\<exists>m. (T^^m) x \<in> good_set" by blast
    define m where "m = Inf {m. (T^^m) x \<in> good_set}"
    then have "(T^^m) x \<in> good_set" using ** Inf_nat_def1 by (metis empty_iff mem_Collect_eq)
    have "n+1 \<in> {m. (T^^m) x \<in> good_set}" using a by simp
    then have "m \<le> n+1" using m_def by (simp add: Inf_nat_def Least_le)
    then obtain k where "n+1 = m + k" using le_iff_add by blast
    have "g x = f((T^^m) x)" unfolding g_def good_time_def using ** m_def by simp
    also have "... = f((T^^k) ((T^^m) x))" using \<open>(T^^m) x \<in> good_set\<close> good_k by simp
    also have "... = f((T^^(n+1))x)" using \<open>n+1 = m + k\<close>[symmetric] funpow_add by (metis add.commute comp_apply)
    also have "... = f((T^^n) (T x))" using funpow_Suc_right by (metis Suc_eq_plus1 comp_apply)
    also have "... = g(T x)" unfolding g_def good_time_def using * n_def by simp
    finally show "g(T x) = g x" by simp
  next
    assume *: "\<not>(\<exists>n. (T^^n) (T x) \<in> good_set)"
    then have "g(T x) = y0" unfolding g_def by simp
    have **: "\<not>(\<exists>n. (T^^(Suc n)) x \<in> good_set)" using funpow_Suc_right * by (metis comp_apply)
    have "T x \<notin> good_set" using good_k * by blast
    then have "x \<notin> good_set" using good_1 by auto
    then have "\<not>(\<exists>n. (T^^n) x \<in> good_set)" using ** using good_1 by fastforce
    then have "g x = y0" unfolding g_def by simp
    then show "g(T x) = g x" using \<open>g(T x) = y0\<close> by simp
  qed
  then have "g \<in> borel_measurable Invariants" by (rule Invariants_func_charac[OF \<open>g \<in> borel_measurable M\<close>])
  then show "\<exists>g\<in>borel_measurable Invariants. AE x in M. f x = g x" using \<open>AE x in M. f x = g x\<close> by blast
qed

text \<open>In a conservative setting, it suffices to have an almost everywhere inequality to get
an almost everywhere equality, as the set where there is strict inequality has $0$ measure
as its iterates are disjoint, by conservativity.\<close>

proposition (in conservative) AE_decreasing_then_invariant:
  fixes f::"_ \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  assumes "AE x in M. f(T x) \<le> f x"
    and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f(T x) = f x"
proof -
  obtain D::"'b set" where D: "countable D" "(\<forall>x y. x < y \<longrightarrow> (\<exists>d \<in> D. x \<le> d \<and> d < y))"
    using countable_separating_set_linorder2 by blast

  define A where "A = {x \<in> space M. f(T x) \<le> f x}"
  then have [measurable]: "A \<in> sets M" by simp
  define B where "B = {x \<in> space M. \<forall>n. f((T^^(n+1)) x) \<le> f((T^^n)x)}"
  then have [measurable]: "B \<in> sets M" by simp

  have "space M - A \<in> null_sets M" unfolding A_def using assms by (simp add: assms(1) AE_iff_null_sets)
  then have "(\<Union>n. (T^^n)--`(space M - A)) \<in> null_sets M" by (metis null_sets_UN T_quasi_preserves_null2(2))
  moreover have "space M - B = (\<Union>n. (T^^n)--`(space M - A))"
    unfolding B_def A_def by auto
  ultimately have "space M - B \<in> null_sets M" by simp

  have *: "B = (\<Inter>n. (T^^n)--`A)"
    unfolding B_def A_def by auto
  then have "T--`B = (\<Inter>n. T--` (T^^n)--`A)" by auto
  also have "... = (\<Inter>n. (T^^(n+1))--`A)" using T_vrestr_composed(2)[OF \<open>A \<in> sets M\<close>] by simp
  also have "... \<supseteq> (\<Inter>n. (T^^n)--`A)" by blast
  finally have B1: "B \<subseteq> T--`B" using * by simp
  have "B \<subseteq> A" using * T_vrestr_0[OF \<open>A \<in> sets M\<close>] by blast
  then have B2: "\<And>x. x \<in> B \<Longrightarrow> f(T x) \<le> f x" unfolding A_def by auto

  define C where "C = (\<lambda>t. {x \<in> B. f x \<le> t})"
  {
    fix t
    have "C t = B \<inter> f-`{..t} \<inter> space M" unfolding C_def using sets.sets_into_space[OF \<open>B \<in> sets M\<close>] by auto
    then have [measurable]: "C t \<in> sets M" using assms(2) by simp
    have "C t \<subseteq> T--`(C t)" using B1 unfolding C_def vimage_restr_def apply auto using B2 order_trans by blast
    then have "T--`(C t) - C t \<in> null_sets M" by (metis Diff_mono Un_absorb1 preimage_includes_then_almost_invariant[OF \<open>C t \<in> sets M\<close>])
  }
  then have "(\<Union>d\<in>D. T--`(C d) - C d) \<in> null_sets M" using \<open>countable D\<close> by (simp add: null_sets_UN')
  then have "(space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d) \<in> null_sets M" using \<open>space M - B \<in> null_sets M\<close> by auto
  then have "AE x in M. x \<notin> (space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d)" using AE_not_in by blast
  moreover
  {
    fix x assume x: "x \<in> space M" "x \<notin> (space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d)"
    then have "x \<in> B" by simp
    then have "T x \<in> B" using B1 by auto
    have "f(T x) = f x"
    proof (rule ccontr)
      assume "f(T x) \<noteq> f x"
      then have "f(T x) < f x" using B2[OF \<open>x \<in> B\<close>] by simp
      then obtain d where d: "d \<in> D" "f(T x) \<le> d \<and> d < f x" using D by auto
      then have "T x \<in> C d" using \<open>T x \<in> B\<close> unfolding C_def by simp
      then have "x \<in> T--`(C d)" using \<open>x \<in> space M\<close> by simp
      then have "x \<in> C d" using x \<open>d \<in> D\<close> by simp
      then have "f x \<le> d" unfolding C_def by simp
      then show False using d by auto
    qed
  }
  ultimately show ?thesis by auto
qed

proposition (in conservative) AE_increasing_then_invariant:
  fixes f::"_ \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  assumes "AE x in M. f(T x) \<ge> f x"
    and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. f(T x) = f x"
proof -
  obtain D::"'b set" where D: "countable D" "(\<forall>x y. x < y \<longrightarrow> (\<exists>d \<in> D. x < d \<and> d \<le> y))"
    using countable_separating_set_linorder1 by blast

  define A where "A = {x \<in> space M. f(T x) \<ge> f x}"
  then have [measurable]: "A \<in> sets M" by simp
  define B where "B = {x \<in> space M. \<forall>n. f((T^^(n+1)) x) \<ge> f((T^^n)x)}"
  then have [measurable]: "B \<in> sets M" by simp

  have "space M - A \<in> null_sets M" unfolding A_def using assms by (simp add: assms(1) AE_iff_null_sets)
  then have "(\<Union>n. (T^^n)--`(space M - A)) \<in> null_sets M" by (metis null_sets_UN T_quasi_preserves_null2(2))
  moreover have "space M - B = (\<Union>n. (T^^n)--`(space M - A))"
    unfolding B_def A_def by auto
  ultimately have "space M - B \<in> null_sets M" by simp

  have *: "B = (\<Inter>n. (T^^n)--`A)"
    unfolding B_def A_def by auto
  then have "T--`B = (\<Inter>n. T--` (T^^n)--`A)" by auto
  also have "... = (\<Inter>n. (T^^(n+1))--`A)" using T_vrestr_composed(2)[OF \<open>A \<in> sets M\<close>] by simp
  also have "... \<supseteq> (\<Inter>n. (T^^n)--`A)" by blast
  finally have B1: "B \<subseteq> T--`B" using * by simp
  have "B \<subseteq> A" using * T_vrestr_0[OF \<open>A \<in> sets M\<close>] by blast
  then have B2: "\<And>x. x \<in> B \<Longrightarrow> f(T x) \<ge> f x" unfolding A_def by auto

  define C where "C = (\<lambda>t. {x \<in> B. f x \<ge> t})"
  {
    fix t
    have "C t = B \<inter> f-`{t..} \<inter> space M" unfolding C_def using sets.sets_into_space[OF \<open>B \<in> sets M\<close>] by auto
    then have [measurable]: "C t \<in> sets M" using assms(2) by simp
    have "C t \<subseteq> T--`(C t)" using B1 unfolding C_def vimage_restr_def apply auto using B2 order_trans by blast
    then have "T--`(C t) - C t \<in> null_sets M" by (metis Diff_mono Un_absorb1 preimage_includes_then_almost_invariant[OF \<open>C t \<in> sets M\<close>])
  }
  then have "(\<Union>d\<in>D. T--`(C d) - C d) \<in> null_sets M" using \<open>countable D\<close> by (simp add: null_sets_UN')
  then have "(space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d) \<in> null_sets M" using \<open>space M - B \<in> null_sets M\<close> by auto
  then have "AE x in M. x \<notin> (space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d)" using AE_not_in by blast
  moreover
  {
    fix x assume x: "x \<in> space M" "x \<notin> (space M - B) \<union> (\<Union>d\<in>D. T--`(C d) - C d)"
    then have "x \<in> B" by simp
    then have "T x \<in> B" using B1 by auto
    have "f(T x) = f x"
    proof (rule ccontr)
      assume "f(T x) \<noteq> f x"
      then have "f(T x) > f x" using B2[OF \<open>x \<in> B\<close>] by simp
      then obtain d where d: "d \<in> D" "f(T x) \<ge> d \<and> d > f x" using D by auto
      then have "T x \<in> C d" using \<open>T x \<in> B\<close> unfolding C_def by simp
      then have "x \<in> T--`(C d)" using \<open>x \<in> space M\<close> by simp
      then have "x \<in> C d" using x \<open>d \<in> D\<close> by simp
      then have "f x \<ge> d" unfolding C_def by simp
      then show False using d by auto
    qed
  }
  ultimately show ?thesis by auto
qed

text \<open>For an invertible map, the invariants of $T$ and $T^{-1}$ are the same.\<close>

lemma Invariants_Tinv:
  assumes "invertible_qmpt"
  shows "qmpt.Invariants M Tinv = Invariants"
proof -
  interpret I: qmpt M Tinv using Tinv_qmpt[OF assms] by auto
  have "(T -` A \<inter> space M = A) \<longleftrightarrow> (Tinv -` A \<inter> space M = A)" if "A \<in> sets M" for A
  proof
    assume "T -` A \<inter> space M = A"
    then show "Tinv -` A \<inter> space M = A"
      using assms that unfolding Tinv_def invertible_qmpt_def
      apply auto
      apply (metis IntE UNIV_I bij_def imageE inv_f_f vimageE)
      apply (metis I.T_spaceM_stable(1) Int_iff Tinv_def bij_inv_eq_iff vimageI)
      done
  next
    assume "Tinv -` A \<inter> space M = A"
    then show "T -` A \<inter> space M = A"
      using assms that unfolding Tinv_def invertible_qmpt_def
      apply auto
      apply (metis IntE bij_def inv_f_f vimageE)
      apply (metis T_Tinv_of_set T_meas Tinv_def assms qmpt.vrestr_of_set qmpt_axioms vrestr_image(3))
      done
  qed
  then have "{A \<in> sets M. Tinv -` A \<inter> space M = A} = {A \<in> sets M. T -` A \<inter> space M = A}"
    by blast
  then show ?thesis unfolding Invariants_def I.Invariants_def by auto
qed

end

sublocale fmpt \<subseteq> finite_measure_subalgebra M Invariants
  unfolding finite_measure_subalgebra_def finite_measure_subalgebra_axioms_def
  using Invariants_is_subalg by (simp add: finite_measureI)

context fmpt
begin

text \<open>The conditional expectation with respect to the invariant sigma-algebra is the same
for $f$ or $f \circ T$, essentially by definition.\<close>

lemma Invariants_of_foTn:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. real_cond_exp M Invariants (f o (T^^n)) x = real_cond_exp M Invariants f x"
proof (rule real_cond_exp_charact)
  fix A assume [measurable]: "A \<in> sets Invariants"
  then have [measurable]: "A \<in> sets M" using Invariants_in_sets by blast
  then have ind_meas [measurable]: "((indicator A)::('a \<Rightarrow> real)) \<in> borel_measurable Invariants" by auto

  have "set_lebesgue_integral M A (f \<circ> (T^^n)) = (\<integral>x. indicator A x * f((T^^n) x) \<partial>M)"
    by (auto simp: comp_def set_lebesgue_integral_def)
  also have "... = (\<integral>x. indicator A ((T^^n) x) * f ((T^^n) x) \<partial>M)"
    by (rule Bochner_Integration.integral_cong, auto simp add: Invariants_func_is_invariant_n[OF ind_meas])
  also have "... = (\<integral>x. indicator A x * f x \<partial>M)"
    apply (rule Tn_integral_preserving(2)) using integrable_mult_indicator[OF \<open>A \<in> sets M\<close> assms] by auto
  also have "... = (\<integral>x. indicator A x * real_cond_exp M Invariants f x \<partial>M)"
    apply (rule real_cond_exp_intg(2)[symmetric]) using integrable_mult_indicator[OF \<open>A \<in> sets M\<close> assms] by auto
  also have "... = set_lebesgue_integral M A (real_cond_exp M Invariants f)"
    by (auto simp: set_lebesgue_integral_def)
  finally show "set_lebesgue_integral M A (f \<circ> (T^^n)) = set_lebesgue_integral M A (real_cond_exp M Invariants f)"
    by simp
qed (auto simp add: assms real_cond_exp_int Tn_integral_preserving(1)[OF assms] comp_def)

lemma Invariants_of_foT:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. real_cond_exp M Invariants f x = real_cond_exp M Invariants (f o T) x"
using Invariants_of_foTn[OF assms, where ?n = 1] by auto

lemma birkhoff_sum_Invariants:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. real_cond_exp M Invariants (birkhoff_sum f n) x = n * real_cond_exp M Invariants f x"
proof -
  define F where "F = (\<lambda>i. f o (T^^i))"
  have [measurable]: "\<And>i. F i \<in> borel_measurable M" unfolding F_def by auto
  have *: "integrable M (F i)" for i unfolding F_def
    by (subst comp_def, rule Tn_integral_preserving(1)[OF assms, of i])

  have "AE x in M. n * real_cond_exp M Invariants f x = (\<Sum>i\<in>{..<n}. real_cond_exp M Invariants f x)" by auto
  moreover have "AE x in M. (\<Sum>i\<in>{..<n}. real_cond_exp M Invariants f x) = (\<Sum>i\<in>{..<n}. real_cond_exp M Invariants (F i) x)"
    apply (rule AE_symmetric[OF AE_equal_sum]) unfolding F_def using Invariants_of_foTn[OF assms] by simp
  moreover have "AE x in M. (\<Sum>i\<in>{..<n}. real_cond_exp M Invariants (F i) x) = real_cond_exp M Invariants (\<lambda>x. \<Sum>i\<in>{..<n}. F i x) x"
    by (rule AE_symmetric[OF real_cond_exp_sum [OF *]])
  moreover have "AE x in M. real_cond_exp M Invariants (\<lambda>x. \<Sum>i\<in>{..<n}. F i x) x = real_cond_exp M Invariants (birkhoff_sum f n) x"
    apply (rule real_cond_exp_cong) unfolding F_def using birkhoff_sum_def[symmetric] by auto
  ultimately show ?thesis by auto
qed

end (* of context fmpt *)

subsection \<open>Birkhoff theorem\<close>

subsubsection \<open>Almost everywhere version of Birkhoff theorem\<close>

text \<open>This paragraph is devoted to the proof of Birkhoff theorem, arguably
the most fundamental result of ergodic theory.
This theorem asserts that Birkhoff averages of an integrable function $f$ converge almost surely,
to the conditional expectation of $f$ with respect to the invariant sigma algebra.

This result implies for instance the strong law of large numbers (in probability theory).

There are numerous proofs of this statement, but none is really easy. We follow the very efficient
argument given in Katok-Hasselblatt. To help the reader, here is the same proof informally. The
first part of the proof is formalized in \verb+birkhoff_lemma1+, the second one in
\verb+birkhoff_lemma+, and the conclusion in \verb+birkhoff_theorem+.

Start with an integrable function $g$. let $G_n(x) = \max_{k\leq n} S_k g(x)$. Then $\limsup S_n g/n
\leq 0$ outside of $A$, the set where $G_n$ tends to infinity. Moreover, $G_{n+1} - G_n \circ T$ is
bounded by $g$, and tends to $g$ on $A$. It follows from the dominated convergence theorem that
$\int_A G_{n+1} - G_n \circ T \to \int_A g$. As $\int_A G_{n+1} - G_n \circ T = \int_A G_{n+1} - G_n
\geq 0$, we obtain $\int_A g \geq 0$.

Apply now this result to the function $g = f - E(f | I) - \epsilon$, where $\epsilon>0$ is fixed.
Then $\int_A g = -\epsilon \mu(A)$, then have $\mu(A) = 0$. Thus, almost surely, $\limsup S_n
g/n\leq 0$, i.e., $\limsup S_n f/n \leq E(f|I)+\epsilon$. Letting $\epsilon$ tend to $0$ gives
$\limsup S_n f/n \leq E(f|I)$.

Applying the same result to $-f$ gives $S_n f/n \to E(f|I)$.
\<close>

context fmpt
begin

lemma birkhoff_aux1:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  defines "A \<equiv> {x \<in> space M. limsup (\<lambda>n. ereal(birkhoff_sum f n x)) = \<infinity>}"
    shows "A \<in> sets Invariants" "(\<integral>x. f x * indicator A x \<partial>M) \<ge> 0"
proof -
  let ?bsf = "birkhoff_sum f"
  have [measurable]: "A \<in> sets M" unfolding A_def by simp
  have Ainv: "x \<in> A \<longleftrightarrow> T x \<in> A" if "x \<in> space M" for x
  proof -
    have "ereal(?bsf (1 + n) x) = ereal(f x) + ereal(?bsf n (T x))" for n
      unfolding birkhoff_sum_cocycle birkhoff_sum_1 by simp
    moreover have "limsup (\<lambda>n. ereal(f x) + ereal(?bsf n (T x)))
                    = ereal(f x) + limsup(\<lambda>n. ereal(?bsf n (T x)))"
      by (rule ereal_limsup_lim_add, auto)
    moreover have "limsup (\<lambda>n. ereal(?bsf (n+1) x)) = limsup (\<lambda>n. ereal(?bsf n x))" using limsup_shift by simp
    ultimately have "limsup (\<lambda>n. ereal(birkhoff_sum f n x)) = ereal(f x) + limsup (\<lambda>n. ereal(?bsf n (T x)))" by simp
    then have "limsup (\<lambda>n. ereal(?bsf n x)) = \<infinity> \<longleftrightarrow> limsup (\<lambda>n. ereal(?bsf n (T x))) = \<infinity>" by simp
    then show "x \<in> A \<longleftrightarrow> T x \<in> A" using \<open>x \<in> space M\<close> A_def by simp
  qed
  then show "A \<in> sets Invariants" using assms(2) Invariants_sets by auto

  define F where "F = (\<lambda>n x. MAX k \<in>{0..n}. ?bsf k x)"
  have [measurable]: "\<And>n. F n \<in> borel_measurable M" unfolding F_def by measurable
  have intFn: "integrable M (F n)" for n
    unfolding F_def by (rule integrable_MAX, auto simp add: birkhoff_sum_integral(1)[OF assms(1)])

  have Frec: "F (n+1) x - F n (T x) = max (-F n (T x)) (f x)" for n x
  proof -
    have "{0..n+1} = {0} \<union> {1..n+1}" by auto
    then have "(\<lambda>k. ?bsf k x) ` {0..n+1} = (\<lambda>k. ?bsf k x) ` {0} \<union> (\<lambda>k. ?bsf k x) ` {1..n+1}" by blast
    then have *: "(\<lambda>k. ?bsf k x) ` {0..n+1} = {0} \<union> (\<lambda>k. ?bsf k x) ` {1..n+1}" using birkhoff_sum_1(1) by simp
    have b: "F (n+1) x = max (Max {0}) (MAX k \<in>{1..n+1}. ?bsf k x)"
      by (subst F_def, subst *, rule Max.union, auto)

    have "(\<lambda>k. ?bsf k x) ` {1..n+1} = (\<lambda>k. ?bsf (1+k) x) ` {0..n}" using Suc_le_D by fastforce
    also have "... = (\<lambda>k. f x + ?bsf k (T x)) ` {0..n}"
      by (subst birkhoff_sum_cocycle, subst birkhoff_sum_1(2), auto)
    finally have c: "F (n+1) x = max 0 (MAX k \<in>{0..n}. ?bsf k (T x) + f x)" using b by (simp add: add_ac)

    have "{f x + birkhoff_sum f k (T x) |k. k \<in>{0..n}} = (+) (f x) ` {birkhoff_sum f k (T x) |k. k \<in>{0..n}}" by blast
    have "(MAX k \<in>{0..n}. ?bsf k (T x) + f x) = (MAX k \<in>{0..n}. ?bsf k (T x)) + f x"
      by (rule Max_add_commute) auto
    also have "... = F n (T x) + f x" unfolding F_def by simp
    finally have "(MAX k \<in>{0..n}. ?bsf k (T x) + f x) = f x + F n (T x)" by simp
    then have "F (n+1) x = max 0 (f x + F n (T x))" using c by simp
    then show "F (n+1) x - F n (T x) = max (-F n (T x)) (f x)" by auto
  qed

  have a: "abs((F (n+1) x - F n (T x)) * indicator A x) \<le> abs(f x)" for n x
  proof -
    have "F (n+1) x -F n (T x) \<ge> f x" using Frec by simp
    then have *: "F (n+1) x -F n (T x) \<ge> - abs(f x)" by simp

    have "F n (T x) \<ge> birkhoff_sum f 0 (T x)"
      unfolding F_def apply (rule Max_ge, simp) using atLeastAtMost_iff by blast
    then have "F n (T x) \<ge> 0" using birkhoff_sum_1(1) by simp
    then have "-F n (T x) \<le> abs (f x)" by simp
    moreover have "f x \<le> abs(f x)" by simp
    ultimately have "F (n+1) x -F n (T x) \<le> abs(f x)" using Frec by simp
    then have "abs(F (n+1) x - F n (T x)) \<le> abs(f x)" using * by simp
    then show "abs((F (n+1) x - F n (T x)) * indicator A x) \<le> abs(f x)" unfolding indicator_def by auto
  qed
  have b: "(\<lambda>n. (F (n+1) x - F n (T x)) * indicator A x) \<longlonglongrightarrow> f x * indicator A x" for x
  proof (rule Lim_eventually, cases)
    assume "x \<in> A"
    then have "T x \<in> A" using Ainv A_def by auto
    then have "limsup (\<lambda>n. ereal(birkhoff_sum f n (T x))) > ereal(-f x)" unfolding A_def by simp
    then obtain N where "ereal(?bsf N (T x)) > ereal(-f x)" using Limsup_obtain by blast
    then have *: "?bsf N (T x) > -f x" by simp
    {
      fix n assume "n\<ge>N"
      then have "?bsf N (T x) \<in> (\<lambda>k. ?bsf k (T x)) ` {0..n}" by auto
      then have "F n (T x) \<ge> ?bsf N (T x)" unfolding F_def by simp
      then have "F n (T x) \<ge> -f x" using * by simp
      then have "max (-F n (T x)) (f x) = f x" by simp
      then have "F (n+1) x - F n (T x) = f x" using Frec by simp
      then have "(F (n+1) x - F n (T x)) * indicator A x = f x * indicator A x" by simp
    }
    then show "eventually (\<lambda>n. (F (n+1) x - F n (T x)) * indicator A x = f x * indicator A x) sequentially"
      using eventually_sequentially by blast
  next
    assume "\<not>(x \<in> A)"
    then have "indicator A x = (0::real)" by simp
    then show "eventually (\<lambda>n. (F (n+1) x - F n (T x)) * indicator A x = f x * indicator A x) sequentially" by auto
  qed
  have lim: "(\<lambda>n. (\<integral>x. (F (n+1) x - F n (T x)) * indicator A x \<partial>M)) \<longlonglongrightarrow> (\<integral>x. f x * indicator A x \<partial>M)"
  proof (rule integral_dominated_convergence[where ?w = "(\<lambda>x. abs(f x))"])
    show "integrable M (\<lambda>x. \<bar>f x\<bar>)" using assms(1) by auto
    show "AE x in M. (\<lambda>n. (F (n + 1) x - F n (T x)) * indicator A x) \<longlonglongrightarrow> f x * indicator A x" using b by auto
    show "\<And>n. AE x in M. norm ((F (n + 1) x - F n (T x)) * indicator A x) \<le> \<bar>f x\<bar>" using a by auto
  qed (simp_all)

  have "(\<integral>x. (F (n+1) x - F n (T x)) * indicator A x \<partial>M) \<ge> 0" for n
  proof -
    have "(\<integral>x. F n (T x) * indicator A x \<partial>M) = (\<integral>x. (\<lambda>x. F n x * indicator A x) (T x) \<partial>M)"
      by (rule Bochner_Integration.integral_cong, auto simp add: Ainv indicator_def)
    also have "... = (\<integral>x. F n x * indicator A x \<partial>M)"
      by (rule T_integral_preserving, auto simp add: intFn integrable_real_mult_indicator)
    finally have i: "(\<integral>x. F n (T x) * indicator A x \<partial>M) = (\<integral>x. F n x * indicator A x \<partial>M)" by simp

    have "(\<integral>x. (F (n+1) x - F n (T x)) * indicator A x \<partial>M) = (\<integral>x. F (n+1) x * indicator A x - F n (T x) * indicator A x \<partial>M)"
      by (simp add: mult.commute right_diff_distrib)
    also have "... = (\<integral>x. F (n+1) x * indicator A x \<partial>M) - (\<integral>x. F n (T x) * indicator A x \<partial>M)"
      by (rule Bochner_Integration.integral_diff, auto simp add: intFn integrable_real_mult_indicator T_meas T_integral_preserving(1))
    also have "... = (\<integral>x. F (n+1) x * indicator A x \<partial>M) - (\<integral>x. F n x * indicator A x \<partial>M)"
      using i by simp
    also have "... = (\<integral>x. F (n+1) x * indicator A x - F n x * indicator A x \<partial>M)"
      by (rule Bochner_Integration.integral_diff[symmetric], auto simp add: intFn integrable_real_mult_indicator)
    also have "... = (\<integral>x. (F (n+1) x - F n x) * indicator A x \<partial>M)"
      by (simp add: mult.commute right_diff_distrib)
    finally have *: "(\<integral>x. (F (n+1) x - F n (T x)) * indicator A x \<partial>M) = (\<integral>x. (F (n+1) x - F n x) * indicator A x \<partial>M)"
      by simp

    have "F n x \<le> F (n+1) x" for x unfolding F_def by (rule Max_mono, auto)
    then have "(F (n+1) x - F n x) * indicator A x \<ge> 0" for x by simp
    then have "integral\<^sup>L M (\<lambda>x. 0) \<le> integral\<^sup>L M (\<lambda>x. (F (n+1) x - F n x) * indicator A x)"
      by (auto simp add: intFn integrable_real_mult_indicator intro: integral_mono)
    then have "(\<integral>x. (F (n+1) x - F n x) * indicator A x \<partial>M) \<ge> 0" by simp
    then show "(\<integral>x. (F (n+1) x - F n (T x)) * indicator A x \<partial>M) \<ge> 0" using * by simp
  qed
  then show "(\<integral>x. f x * indicator A x \<partial>M) \<ge> 0" using lim by (simp add: LIMSEQ_le_const)
qed

lemma birkhoff_aux2:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. limsup (\<lambda>n. ereal(birkhoff_sum f n x / n)) \<le> real_cond_exp M Invariants f x"
proof -
  {
    fix \<epsilon> assume "\<epsilon> > (0::real)"
    define g where "g = (\<lambda>x. f x - real_cond_exp M Invariants f x - \<epsilon>)"
    then have intg: "integrable M g" using assms real_cond_exp_int(1) assms by auto
    define A where "A = {x \<in> space M. limsup (\<lambda>n. ereal(birkhoff_sum g n x)) = \<infinity>}"
    have Ag: "A \<in> sets Invariants" "(\<integral>x. g x * indicator A x \<partial>M) \<ge> 0"
      unfolding A_def by (rule birkhoff_aux1[where ?f = g, OF intg])+
    then have [measurable]: "A \<in> sets M" by (simp add: Invariants_in_sets)

    have eq: "(\<integral>x. indicator A x * real_cond_exp M Invariants f x \<partial>M) = (\<integral>x. indicator A x * f x \<partial>M)"
    proof (rule real_cond_exp_intg[where ?f = "\<lambda>x. (indicator A x)::real" and ?g = f])
      have "(\<lambda>x. indicator A x * f x) = (\<lambda>x. f x * indicator A x)" by auto
      then show "integrable M (\<lambda>x. indicator A x * f x)"
        using integrable_real_mult_indicator[OF \<open>A \<in> sets M\<close> assms] by simp
      show "indicator A \<in> borel_measurable Invariants" using \<open>A \<in> sets Invariants\<close> by measurable
    qed (simp)

    have "0 \<le> (\<integral>x. g x * indicator A x \<partial>M)" using Ag by simp
    also have "... = (\<integral>x. f x * indicator A x - real_cond_exp M Invariants f x * indicator A x - \<epsilon> * indicator A x \<partial>M)"
      unfolding g_def by (simp add: left_diff_distrib)
    also have "... = (\<integral>x. f x * indicator A x \<partial>M) - (\<integral>x. real_cond_exp M Invariants f x * indicator A x \<partial>M) - (\<integral>x. \<epsilon> * indicator A x \<partial>M)"
      using assms real_cond_exp_int(1)[OF assms] integrable_real_mult_indicator[OF \<open>A \<in> sets M\<close>] by auto
    also have "... = - (\<integral>x. \<epsilon> * indicator A x \<partial>M)"
      by (auto simp add: eq mult.commute)
    also have "... = - \<epsilon> * measure M A" by auto
    finally have "0 \<le> - \<epsilon> * measure M A" by simp
    then have "measure M A = 0" using \<open>\<epsilon> > 0\<close> by (simp add: measure_le_0_iff mult_le_0_iff)
    then have "A \<in> null_sets M" by (simp add: emeasure_eq_measure null_setsI)
    then have "AE x in M. x \<in> space M - A" by (metis (no_types, lifting) AE_cong Diff_iff AE_not_in)
    moreover
    {
      fix x assume "x \<in> space M - A"
      then have "limsup (\<lambda>n. ereal(birkhoff_sum g n x)) < \<infinity>" unfolding A_def by auto
      then obtain C where C: "\<And>n. birkhoff_sum g n x \<le> C" using limsup_finite_then_bounded by presburger
      {
        fix n::nat assume "n > 0"
        have "birkhoff_sum g n x = birkhoff_sum f n x - birkhoff_sum (real_cond_exp M Invariants f) n x - birkhoff_sum (\<lambda>x. \<epsilon>) n x"
          unfolding g_def using birkhoff_sum_add birkhoff_sum_diff by auto
        moreover have "birkhoff_sum (real_cond_exp M Invariants f) n x = n * real_cond_exp M Invariants f x"
          using birkhoff_sum_of_invariants using \<open>x \<in> space M - A\<close> by auto
        moreover have "birkhoff_sum (\<lambda>x. \<epsilon>) n x = n * \<epsilon>" unfolding birkhoff_sum_def by auto
        ultimately have "birkhoff_sum g n x = birkhoff_sum f n x - n * real_cond_exp M Invariants f x - n * \<epsilon>"
          by simp
        then have "birkhoff_sum f n x = birkhoff_sum g n x + n * real_cond_exp M Invariants f x + n * \<epsilon>"
          by simp
        then have "birkhoff_sum f n x / n = birkhoff_sum g n x / n + real_cond_exp M Invariants f x + \<epsilon>"
          using \<open>n > 0\<close> by (simp add: add_divide_eq_iff linordered_field_class.sign_simps(27))
        then have "birkhoff_sum f n x / n \<le> C/n + real_cond_exp M Invariants f x + \<epsilon>"
          using C[of n] \<open>n > 0\<close> by (simp add: divide_right_mono)
        then have "ereal(birkhoff_sum f n x / n) \<le> ereal(C/n + real_cond_exp M Invariants f x + \<epsilon>)"
          by simp
      }
      then have "eventually (\<lambda>n. ereal(birkhoff_sum f n x / n) \<le> ereal(C/n + real_cond_exp M Invariants f x + \<epsilon>)) sequentially"
        by (simp add: eventually_at_top_dense)
      then have b: "limsup (\<lambda>n. ereal(birkhoff_sum f n x / n)) \<le> limsup (\<lambda>n. ereal(C/n + real_cond_exp M Invariants f x + \<epsilon>))"
        by (simp add: Limsup_mono)

      have "(\<lambda>n. ereal(C*(1/real n) + real_cond_exp M Invariants f x + \<epsilon>)) \<longlonglongrightarrow> ereal(C * 0 + real_cond_exp M Invariants f x + \<epsilon>)"
        by (intro tendsto_intros)
      then have "limsup (\<lambda>n. ereal(C/real n + real_cond_exp M Invariants f x + \<epsilon>)) = real_cond_exp M Invariants f x + \<epsilon>"
        using sequentially_bot tendsto_iff_Liminf_eq_Limsup by force
      then have "limsup (\<lambda>n. ereal(birkhoff_sum f n x / n)) \<le> real_cond_exp M Invariants f x + \<epsilon>"
        using b by simp
    }
    ultimately have "AE x in M. limsup (\<lambda>n. ereal(birkhoff_sum f n x / n)) \<le> real_cond_exp M Invariants f x + \<epsilon>"
      by auto
    then have "AE x in M. limsup (\<lambda>n. ereal(birkhoff_sum f n x / n)) \<le> ereal(real_cond_exp M Invariants f x) + \<epsilon>"
      by auto
  }
  then show ?thesis
    by (rule AE_upper_bound_inf_ereal)
qed

theorem birkhoff_theorem_AE_nonergodic:
  fixes f::"'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "AE x in M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
proof -
  {
    fix x assume i: "limsup (\<lambda>n. ereal(birkhoff_sum f n x /n)) \<le> real_cond_exp M Invariants f x"
             and ii: "limsup (\<lambda>n. ereal(birkhoff_sum (\<lambda>x. -f x) n x / n)) \<le> real_cond_exp M Invariants (\<lambda>x. -f x) x"
             and iii: "real_cond_exp M Invariants (\<lambda>x. -f x) x = - real_cond_exp M Invariants f x"
    have "\<And>n. birkhoff_sum (\<lambda>x. -f x) n x = - birkhoff_sum f n x"
      using birkhoff_sum_cmult[where ?c = "-1" and ?f = f] by auto
    then have "\<And>n. ereal(birkhoff_sum (\<lambda>x. -f x) n x / n) = - ereal(birkhoff_sum f n x / n)" by auto
    moreover have "limsup (\<lambda>n. - ereal(birkhoff_sum f n x / n)) = - liminf (\<lambda>n. ereal(birkhoff_sum f n x /n))"
      by (rule ereal_Limsup_uminus)
    ultimately have "-liminf (\<lambda>n. ereal(birkhoff_sum f n x /n)) = limsup (\<lambda>n. ereal(birkhoff_sum (\<lambda>x. -f x) n x / n))"
      by simp
    then have "-liminf (\<lambda>n. ereal(birkhoff_sum f n x /n)) \<le> - real_cond_exp M Invariants f x"
      using ii iii by simp
    then have "liminf (\<lambda>n. ereal(birkhoff_sum f n x /n)) \<ge> real_cond_exp M Invariants f x"
      by (simp add: ereal_uminus_le_reorder)
    then have "(\<lambda>n. birkhoff_sum f n x /n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
      using i by (simp add: limsup_le_liminf_real)
  } note * = this
  moreover have "AE x in M. limsup (\<lambda>n. ereal(birkhoff_sum f n x /n)) \<le> real_cond_exp M Invariants f x"
    using birkhoff_aux2 assms by simp
  moreover have "AE x in M. limsup (\<lambda>n. ereal(birkhoff_sum (\<lambda>x. -f x) n x / n)) \<le> real_cond_exp M Invariants (\<lambda>x. -f x) x"
    using birkhoff_aux2 assms by simp
  moreover have "AE x in M. real_cond_exp M Invariants (\<lambda>x. -f x) x = - real_cond_exp M Invariants f x"
    using real_cond_exp_cmult[where ?c = "-1"] assms by force
  ultimately show ?thesis by auto
qed

text \<open>If a function $f$ is integrable, then $E(f\circ T - f | I) = E(f\circ T | I) - E(f|I) = 0$.
Hence, $S_n(f \circ T - f) / n$ converges almost everywhere to $0$, i.e., $f(T^n x)/n \to 0$.
It is remarkable (and sometimes useful) that this holds under the weaker condition that
$f\circ T - f$ is integrable (but not necessarily $f$), where this naive argument fails.

The reason is that the Birkhoff sum of $f \circ T - f$ is $f\circ T^n - f$. If $n$ is such that $x$
and $T^n(x)$ belong to a set where $f$ is bounded, it follows that this Birkhoff sum is also
bounded. Along such a sequence of times, $S_n(f\circ T - f)/n$ tends to $0$.
By Poincare recurrence theorem, there are such times for almost every points. As it also converges
to $E(f \circ T - f | I)$, it follows that this function is almost everywhere $0$. Then
$f (T^n x)/n = S_n(f\circ T^n - f)/n - f/n$ tends almost surely to $E(f\circ T-f |I) = 0$.
\<close>

lemma limit_foTn_over_n:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable M"
      and "integrable M (\<lambda>x. f(T x) - f x)"
  shows "AE x in M. real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x = 0"
        "AE x in M. (\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> 0"
proof -
  define E::"nat \<Rightarrow> 'a set" where "E k = {x \<in> space M. \<bar>f x\<bar> \<le> k}" for k
  have [measurable]: "E k \<in> sets M" for k unfolding E_def by auto
  have *: "(\<Union>k. E k) = space M" unfolding E_def by (auto simp add: real_arch_simple)
  define F::"nat \<Rightarrow> 'a set" where "F k = recurrent_subset_infty (E k)" for k
  have [measurable]: "F k \<in> sets M" for k unfolding F_def by auto
  have **: "E k - F k \<in> null_sets M" for k unfolding F_def using Poincare_recurrence_thm by auto
  have "space M - (\<Union>k. F k) \<in> null_sets M"
    apply (rule null_sets_subset[of "(\<Union>k. E k - F k)"]) unfolding *[symmetric] using ** by auto
  with AE_not_in[OF this] have "AE x in M. x \<in> (\<Union>k. F k)" by auto
  moreover have "AE x in M. (\<lambda>n. birkhoff_sum (\<lambda>x. f(T x) - f x) n x / n)
      \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x"
    by (rule birkhoff_theorem_AE_nonergodic[OF assms(2)])
  moreover have "real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x = 0 \<and> (\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> 0"
    if H: "(\<lambda>n. birkhoff_sum (\<lambda>x. f(T x) - f x) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x"
          "x \<in> (\<Union>k. F k)" for x
  proof -
    have "f((T^^n) x) = birkhoff_sum (\<lambda>x. f(T x) - f x) n x + f x" for n
      unfolding birkhoff_sum_def by (induction n, auto)
    then have "f((T^^n) x) / n = birkhoff_sum (\<lambda>x. f(T x) - f x) n x / n + f x * (1/n)" for n
      by (auto simp add: divide_simps)
    moreover have "(\<lambda>n. birkhoff_sum (\<lambda>x. f(T x) - f x) n x / n + f x * (1/n)) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x + f x * 0"
      by (intro tendsto_intros H(1))
    ultimately have lim: "(\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x"
      by auto

    obtain k where "x \<in> F k" using H(2) by auto
    then have "infinite {n. (T^^n) x \<in> E k}"
      unfolding F_def recurrent_subset_infty_inf_returns by auto
    with infinite_enumerate[OF this] obtain r :: "nat \<Rightarrow> nat"
      where r: "strict_mono r" "\<And>n. r n \<in> {n. (T^^n) x \<in> E k}"
      by auto
    have A: "(\<lambda>n. k * (1/r n)) \<longlonglongrightarrow> real k * 0"
      apply (intro tendsto_intros)
      using LIMSEQ_subseq_LIMSEQ[OF lim_1_over_n \<open>strict_mono r\<close>] unfolding comp_def by auto
    have B: "\<bar>f((T^^(r n)) x) / r n\<bar> \<le> k / (r n)" for n
      using r(2) unfolding E_def by (auto simp add: divide_simps)
    have "(\<lambda>n. f((T^^(r n)) x) / r n) \<longlonglongrightarrow> 0"
      apply (rule tendsto_rabs_zero_cancel, rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. k * (1/r n)"])
      using A B by auto
    moreover have "(\<lambda>n. f((T^^(r n)) x) / r n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x"
      using LIMSEQ_subseq_LIMSEQ[OF lim \<open>strict_mono r\<close>] unfolding comp_def by auto
    ultimately have *: "real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x = 0"
      using LIMSEQ_unique by auto
    then have "(\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> 0" using lim by auto
    then show ?thesis using * by auto
  qed
  ultimately show "AE x in M. real_cond_exp M Invariants (\<lambda>x. f(T x) - f x) x = 0"
                  "AE x in M. (\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> 0"
    by auto
qed

text \<open>We specialize the previous statement to the case where $f$ itself is integrable.\<close>

lemma limit_foTn_over_n':
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "AE x in M. (\<lambda>n. f((T^^n) x) / n) \<longlonglongrightarrow> 0"
by (rule limit_foTn_over_n, simp, rule Bochner_Integration.integrable_diff)
   (auto intro: assms T_integral_preserving(1))

text \<open>It is often useful to show that a function is cohomologous to a nicer function, i.e., to
prove that a given $f$ can be written as $f = g + u - u \circ T$ where $g$ is nicer than $f$. We
show below that any integrable function is cohomologous to a function which is arbitrarily close to
$E(f|I)$. This is an improved version of Lemma 2.1 in [Benoist-Quint, Annals of maths, 2011]. Note
that the function $g$ to which $f$ is cohomologous is very nice (and, in particular, integrable),
but the transfer function is only measurable in this argument. The fact that the control on
conditional expectation is nevertheless preserved throughout the argument follows from
Lemma~\verb+limit_foTn_over_n+ above.\<close>

text \<open>We start with the lemma (and the proof) of [BQ2011]. It shows that, if a function has a
conditional expectation with respect to invariants which is positive, then it is cohomologous to a
nonnegative function. The argument is the clever remark that $g = \max (0, \inf_n S_n f)$ and $u =
\min (0, \inf_n S_n f)$ work (where these expressions are well defined as $S_n f$ tends to infinity
thanks to our assumption).\<close>

lemma cohomologous_approx_cond_exp_aux:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
      and "AE x in M. real_cond_exp M Invariants f x > 0"
    shows "\<exists>u g. u \<in> borel_measurable M \<and> (integrable M g) \<and> (AE x in M. g x \<ge> 0 \<and> g x \<le> max 0 (f x)) \<and> (\<forall>x. f x = g x + u x - u (T x))"
proof -
  define h::"'a \<Rightarrow> real" where "h = (\<lambda>x. (INF n\<in>{1..}. birkhoff_sum f n x))"
  define u where "u = (\<lambda>x. min (h x) 0)"
  define g where "g = (\<lambda>x. f x - u x + u (T x))"
  have [measurable]: "h \<in> borel_measurable M" "u \<in> borel_measurable M" "g \<in> borel_measurable M"
    unfolding g_def h_def u_def by auto
  have "f x = g x + u x - u (T x)" for x unfolding g_def by auto
  {
    fix x assume H: "real_cond_exp M Invariants f x > 0"
                    "(\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    have "eventually (\<lambda>n. ereal(birkhoff_sum f n x / n) * ereal n = ereal(birkhoff_sum f n x)) sequentially"
      unfolding eventually_sequentially by (rule exI[of _ 1], auto)
    moreover have "(\<lambda>n. ereal(birkhoff_sum f n x / n) * ereal n) \<longlonglongrightarrow> ereal(real_cond_exp M Invariants f x) * \<infinity>"
      apply (intro tendsto_intros) using H by auto
    ultimately have "(\<lambda>n. ereal(birkhoff_sum f n x)) \<longlonglongrightarrow> ereal(real_cond_exp M Invariants f x) * \<infinity>"
      by (rule Lim_transform_eventually)
    then have "(\<lambda>n. ereal(birkhoff_sum f n x)) \<longlonglongrightarrow> \<infinity>"
      using H by auto
    then have B: "\<exists>C. \<forall>n. C \<le> birkhoff_sum f n x"
      by (intro liminf_finite_then_bounded_below, simp add: liminf_PInfty)

    have "h x \<le> f x"
      unfolding h_def apply (rule cInf_lower) using B by force+

    have "{birkhoff_sum f n (T x) |n. n \<in> {1..}} = {birkhoff_sum f (1+n) (x) - f x |n. n \<in> {1..}}"
      unfolding birkhoff_sum_cocycle by auto
    also have "... = {birkhoff_sum f n x - f x |n. n \<in> {2..}}"
      by (metis (no_types, hide_lams) Suc_1 Suc_eq_plus1_left Suc_le_D Suc_le_mono atLeast_iff)
    finally have *: "{birkhoff_sum f n (T x) |n. n \<in> {1..}} = (\<lambda>t. t - (f x))`{birkhoff_sum f n x |n. n \<in> {2..}}"
      by auto

    have "h(T x) = Inf {birkhoff_sum f n (T x) |n. n \<in> {1..}}"
      unfolding h_def by (metis Setcompr_eq_image)
    also have "... =  (\<Sqinter>t\<in>{birkhoff_sum f n x |n. n \<in> {2..}}. t - f x)"
      by (simp only: *)
    also have "... = (\<lambda>t. t - (f x)) (Inf {birkhoff_sum f n x |n. n \<in> {2..}})"
      using B by (auto intro!: monoI bijI mono_bij_cInf [symmetric])
    finally have I: "Inf {birkhoff_sum f n x |n. n \<in> {2..}} = f x + h (T x)" by auto
    have "max 0 (h x) + u x = h x"
      unfolding u_def by auto
    also have "... = Inf {birkhoff_sum f n x |n. n \<in> {1..}}"
      unfolding h_def by (metis Setcompr_eq_image)
    also have "... = Inf ({birkhoff_sum f n x |n. n \<in> {1}} \<union> {birkhoff_sum f n x |n. n \<in> {2..}})"
      by (auto intro!: arg_cong[of _ _ Inf], metis One_nat_def Suc_1 antisym birkhoff_sum_1(2) not_less_eq_eq, force)
    also have "Inf ({birkhoff_sum f n x |n. n \<in> {1}} \<union> {birkhoff_sum f n x |n. n \<in> {2..}})
      = min (Inf {birkhoff_sum f n x |n. n \<in> {1}}) (Inf {birkhoff_sum f n x |n. n \<in> {2..}})"
      unfolding inf_min[symmetric] apply (intro cInf_union_distrib) using B by auto
    also have "... = min (f x) (f x + h (T x))" using I by auto
    also have "... = f x + u (T x)" unfolding u_def by auto
    finally have "max 0 (h x) = f x + u (T x) - u x" by auto
    then have "g x = max 0 (h x)" unfolding g_def by auto
    then have "g x \<ge> 0 \<and> g x \<le> max 0 (f x)" using \<open>h x \<le> f x\<close> by auto
  }
  then have *: "AE x in M. g x \<ge> 0 \<and> g x \<le> max 0 (f x)"
    using assms(2) birkhoff_theorem_AE_nonergodic[OF assms(1)] by auto
  moreover have "integrable M g"
    apply (rule Bochner_Integration.integrable_bound[of _ f]) using * by (auto simp add: assms)
  ultimately have "u \<in> borel_measurable M \<and> integrable M g \<and> (AE x in M. 0 \<le> g x \<and> g x \<le> max 0 (f x)) \<and> (\<forall>x. f x = g x + u x - u (T x))"
    using \<open>\<And>x. f x = g x + u x - u (T x)\<close> \<open>u \<in> borel_measurable M\<close> by auto
  then show ?thesis by blast
qed

text \<open>To deduce the stronger version that $f$ is cohomologous to an arbitrarily good approximation
of $E(f|I)$, we apply the previous lemma twice, to control successively the negative and the
positive side. The sign control in the conclusion of the previous lemma implies that the second step
does not spoil the first one.\<close>

lemma cohomologous_approx_cond_exp:
  fixes f::"'a \<Rightarrow> real" and B::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f" "B \<in> borel_measurable M"
      and "AE x in M. B x > 0"
    shows "\<exists>g u. u \<in> borel_measurable M
              \<and> integrable M g
              \<and> (\<forall>x. f x = g x + u x - u (T x))
              \<and> (AE x in M. abs(g x - real_cond_exp M Invariants f x) \<le> B x)"
proof -
  define C where "C = (\<lambda>x. min (B x) 1)"
  have [measurable]: "integrable M C"
    apply (rule Bochner_Integration.integrable_bound[of _ "\<lambda>_. (1::real)"], auto)
    unfolding C_def using assms(3) by auto
  have "C x \<le> B x" for x unfolding C_def by auto
  have "AE x in M. C x > 0" unfolding C_def using assms(3) by auto
  have AECI: "AE x in M. real_cond_exp M Invariants C x > 0"
    by (intro real_cond_exp_gr_c \<open>integrable M C\<close> \<open>AE x in M. C x > 0\<close>)

  define f1 where "f1 = (\<lambda>x. f x - real_cond_exp M Invariants f x)"
  have "integrable M f1"
    unfolding f1_def by (intro Bochner_Integration.integrable_diff \<open>integrable M f\<close> real_cond_exp_int(1))
  have "AE x in M. real_cond_exp M Invariants f1 x = real_cond_exp M Invariants f x - real_cond_exp M Invariants (real_cond_exp M Invariants f) x"
    unfolding f1_def apply (rule real_cond_exp_diff) by (intro Bochner_Integration.integrable_diff
                \<open>integrable M f\<close> \<open>integrable M C\<close> real_cond_exp_int(1))+
  moreover have "AE x in M. real_cond_exp M Invariants (real_cond_exp M Invariants f) x = real_cond_exp M Invariants f x"
    by (intro real_cond_exp_nested_subalg subalg \<open>integrable M f\<close>, auto)
  ultimately have AEf1: "AE x in M. real_cond_exp M Invariants f1 x = 0" by auto

  have A [measurable]: "integrable M (\<lambda>x. f1 x + C x)"
    by (intro Bochner_Integration.integrable_add \<open>integrable M f1\<close> \<open>integrable M C\<close>)
  have "AE x in M. real_cond_exp M Invariants (\<lambda>x. f1 x + C x) x = real_cond_exp M Invariants f1 x + real_cond_exp M Invariants C x"
    by (intro real_cond_exp_add \<open>integrable M f1\<close> \<open>integrable M C\<close>)
  then have B: "AE x in M. real_cond_exp M Invariants (\<lambda>x. f1 x + C x) x > 0"
    using AECI AEf1 by auto

  obtain u2 g2 where H2: "u2 \<in> borel_measurable M" "integrable M g2" "AE x in M. g2 x \<ge> 0 \<and> g2 x \<le> max 0 (f1 x + C x)" "\<And>x. f1 x + C x = g2 x + u2 x - u2 (T x)"
    using cohomologous_approx_cond_exp_aux[OF A B] by blast

  define f2 where "f2 = (\<lambda>x. (g2 x - C x))"
  have *: "u2(T x) - u2 x = f2 x -f1 x" for x unfolding f2_def using H2(4)[of x] by auto
  have "AE x in M. f2 x \<ge> - C x" using H2(3) unfolding f2_def by auto
  have "integrable M f2"
    unfolding f2_def by (intro Bochner_Integration.integrable_diff \<open>integrable M g2\<close> \<open>integrable M C\<close>)
  have "AE x in M. real_cond_exp M Invariants (\<lambda>x. u2(T x) - u2 x) x = 0"
  proof (rule limit_foTn_over_n)
    show "integrable M (\<lambda>x. u2(T x) - u2 x)"
      unfolding * by (intro Bochner_Integration.integrable_diff \<open>integrable M f1\<close> \<open>integrable M f2\<close>)
  qed (simp add: \<open>u2 \<in> borel_measurable M\<close>)
  then have "AE x in M. real_cond_exp M Invariants (\<lambda>x. f2 x - f1 x) x = 0"
    unfolding * by simp
  moreover have "AE x in M. real_cond_exp M Invariants (\<lambda>x. f2 x - f1 x) x = real_cond_exp M Invariants f2 x - real_cond_exp M Invariants f1 x"
    by (intro real_cond_exp_diff \<open>integrable M f2\<close> \<open>integrable M f1\<close>)
  ultimately have AEf2: "AE x in M. real_cond_exp M Invariants f2 x = 0"
    using AEf1 by auto

  have A [measurable]: "integrable M (\<lambda>x. C x - f2 x)"
    by (intro Bochner_Integration.integrable_diff \<open>integrable M f2\<close> \<open>integrable M C\<close>)
  have "AE x in M. real_cond_exp M Invariants (\<lambda>x. C x - f2 x) x = real_cond_exp M Invariants C x - real_cond_exp M Invariants f2 x"
    by (intro real_cond_exp_diff \<open>integrable M f2\<close> \<open>integrable M C\<close>)
  then have B: "AE x in M. real_cond_exp M Invariants (\<lambda>x. C x - f2 x) x > 0"
    using AECI AEf2 by auto

  obtain u3 g3 where H3: "u3 \<in> borel_measurable M" "integrable M g3" "AE x in M. g3 x \<ge> 0 \<and> g3 x \<le> max 0 (C x - f2 x)" "\<And>x. C x - f2 x = g3 x + u3 x - u3 (T x)"
    using cohomologous_approx_cond_exp_aux[OF A B] by blast

  define f3 where "f3 = (\<lambda>x. C x - g3 x)"
  have "AE x in M. f3 x \<ge> min (C x) (f2 x)" unfolding f3_def using H3(3) by auto
  then have "AE x in M. f3 x \<ge> -C x" using \<open>AE x in M. f2 x \<ge> - C x\<close> \<open>AE x in M. C x > 0\<close> by auto
  moreover have "AE x in M. f3 x \<le> C x" unfolding f3_def using H3(3) by auto
  ultimately have "AE x in M. abs(f3 x) \<le> C x" by auto
  then have *: "AE x in M. abs(f3 x) \<le> B x" using order_trans[OF _ \<open>\<And>x. C x \<le> B x\<close>] by auto

  define g where "g = (\<lambda>x. f3 x + real_cond_exp M Invariants f x)"
  define u where "u = (\<lambda>x. u2 x - u3 x)"
  have "AE x in M. abs (g x - real_cond_exp M Invariants f x) \<le> B x"
    unfolding g_def using * by auto
  moreover have "f x = g x + u x - u(T x)" for x
    using H3(4)[of x] H2(4)[of x] unfolding u_def g_def f3_def f2_def f1_def by auto
  moreover have "u \<in> borel_measurable M"
    unfolding u_def using \<open>u2 \<in> borel_measurable M\<close> \<open>u3 \<in> borel_measurable M\<close> by auto
  moreover have "integrable M g"
    unfolding g_def f3_def by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff
    \<open>integrable M C\<close> \<open>integrable M g3\<close> \<open>integrable M f\<close> real_cond_exp_int(1))
  ultimately show ?thesis by auto
qed


subsubsection \<open>$L^1$ version of Birkhoff theorem\<close>

text \<open>The $L^1$ convergence in Birkhoff theorem follows from the almost everywhere convergence and
general considerations on $L^1$ convergence (Scheffe's lemma) explained
in \verb+AE_and_int_bound_implies_L1_conv2+.
This argument works neatly for nonnegative functions, the general case reduces to this one by taking
the positive and negative parts of a given function.

One could also prove it by truncation: for bounded functions, the $L^1$ convergence follows
from the boundedness and almost sure convergence. The general case follows by density, but it
is a little bit tedious to write as one need to make sure that the conditional expectation
of the truncation converges to the conditional expectation of the original function. This is true
in $L^1$ as the conditional expectation is a contraction in $L^1$, it follows almost everywhere
after taking a subsequence. All in all, the argument based on Scheffe's lemma seems more
economical.\<close>

lemma birkhoff_lemma_L1:
  fixes f::"'a \<Rightarrow> real"
  assumes "\<And>x. f x \<ge> 0"
      and [measurable]: "integrable M f"
  shows "(\<lambda>n. \<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<longlonglongrightarrow> 0"
proof (rule Scheffe_lemma2)
  show i: "integrable M (real_cond_exp M Invariants f)" using assms by (simp add: real_cond_exp_int(1))
  show "AE x in M. (\<lambda>n. birkhoff_sum f n x / real n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    using birkhoff_theorem_AE_nonergodic assms by simp
  fix n
  have [measurable]: "(\<lambda>x. ennreal \<bar>birkhoff_sum f n x\<bar>) \<in> borel_measurable M" by measurable
  show [measurable]: "(\<lambda>x. birkhoff_sum f n x / real n) \<in> borel_measurable M" by measurable

  have "AE x in M. real_cond_exp M Invariants f x \<ge> 0" using assms(1) real_cond_exp_pos by simp
  then have *: "AE x in M. norm (real_cond_exp M Invariants f x) = real_cond_exp M Invariants f x" by auto
  have **: "(\<integral> x. norm (real_cond_exp M Invariants f x) \<partial>M) = (\<integral> x. real_cond_exp M Invariants f x \<partial>M)"
    apply (rule integral_cong_AE) using * by auto

  have "(\<integral>\<^sup>+x. ennreal (norm (real_cond_exp M Invariants f x)) \<partial>M) = (\<integral> x. norm (real_cond_exp M Invariants f x) \<partial>M)"
    by (rule nn_integral_eq_integral) (auto simp add: i)
  also have "... = (\<integral> x. real_cond_exp M Invariants f x \<partial>M)"
    using ** by simp
  also have "... = (\<integral> x. f x \<partial>M)"
    using real_cond_exp_int(2) assms(2) by auto
  also have "... = (\<integral>x. norm(f x) \<partial>M)" using assms by auto
  also have "... = (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by (rule nn_integral_eq_integral[symmetric], auto simp add: assms(2))
  finally have eq: "(\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M) = (\<integral>\<^sup>+ x. norm(f x) \<partial>M)" by simp

  {
    fix x
    have "norm(birkhoff_sum f n x) \<le> birkhoff_sum (\<lambda>x. norm(f x)) n x"
      using birkhoff_sum_abs by fastforce
    then have "norm(birkhoff_sum f n x) \<le> birkhoff_sum (\<lambda>x. ennreal(norm(f x))) n x"
      unfolding birkhoff_sum_def by auto
  }
  then have "(\<integral>\<^sup>+x. norm(birkhoff_sum f n x) \<partial>M) \<le> (\<integral>\<^sup>+x. birkhoff_sum (\<lambda>x. ennreal(norm(f x))) n x \<partial>M)"
    by (simp add: nn_integral_mono)
  also have "... = n * (\<integral>\<^sup>+x. norm(f x) \<partial>M)"
    by (rule birkhoff_sum_nn_integral, auto)
  also have "... = n * (\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M)"
    using eq by simp
  finally have *: "(\<integral>\<^sup>+x. norm(birkhoff_sum f n x) \<partial>M) \<le> n * (\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M)"
    by simp

  show "(\<integral>\<^sup>+ x. ennreal (norm (birkhoff_sum f n x / real n)) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M)"
  proof (cases)
    assume "n = 0"
    then show ?thesis by auto
  next
    assume "\<not>(n = 0)"
    then have "n > 0" by simp
    then have "1/ennreal(real n) \<ge> 0" by simp
    have "(\<integral>\<^sup>+ x. ennreal (norm (birkhoff_sum f n x / real n)) \<partial>M) = (\<integral>\<^sup>+ x. ennreal (norm (birkhoff_sum f n x)) / ennreal(real n) \<partial>M)"
      using \<open>n > 0\<close> by (auto simp: divide_ennreal)
    also have "... = (\<integral>\<^sup>+ x. (1/ennreal(real n)) * ennreal (norm (birkhoff_sum f n x)) \<partial>M)"
      by (simp add: \<open>0 < n\<close> divide_ennreal_def mult.commute)
    also have "... = (1/ennreal(real n) * (\<integral>\<^sup>+ x. ennreal (norm (birkhoff_sum f n x)) \<partial>M))"
      by (subst nn_integral_cmult) auto
    also have "... \<le> (1/ennreal(real n)) * (ennreal(real n) * (\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M))"
      using * by (intro mult_mono) (auto simp: ennreal_of_nat_eq_real_of_nat)
    also have "... = (\<integral>\<^sup>+ x. norm (real_cond_exp M Invariants f x) \<partial>M)"
      using \<open>n > 0\<close>
      by (auto simp del: ennreal_1 simp add: ennreal_1[symmetric] divide_ennreal ennreal_mult[symmetric] mult.assoc[symmetric])
        simp
    finally show ?thesis by simp
  qed
qed

theorem birkhoff_theorem_L1_nonergodic:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
  shows "(\<lambda>n. \<integral>\<^sup>+x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  define g where "g = (\<lambda>x. max (f x) 0)"
  have g_int [measurable]: "integrable M g" unfolding g_def using assms by auto
  define h where "h = (\<lambda>x. max (-f x) 0)"
  have h_int [measurable]: "integrable M h" unfolding h_def using assms by auto
  have "f = (\<lambda>x. g x - h x)" unfolding g_def h_def by auto
  {
    fix n::nat assume "n > 0"
    have "\<And>x. birkhoff_sum f n x = birkhoff_sum g n x - birkhoff_sum h n x" using birkhoff_sum_diff \<open>f = (\<lambda>x. g x - h x)\<close> by auto
    then have "\<And>x. birkhoff_sum f n x / n = birkhoff_sum g n x / n - birkhoff_sum h n x / n" using \<open>n > 0\<close> by (simp add: diff_divide_distrib)
    moreover have "AE x in M. real_cond_exp M Invariants g x - real_cond_exp M Invariants h x = real_cond_exp M Invariants f x"
      using AE_symmetric[OF real_cond_exp_diff] g_int h_int \<open>f = (\<lambda>x. g x - h x)\<close> by auto
    ultimately have "AE x in M. birkhoff_sum f n x / n - real_cond_exp M Invariants f x =
        (birkhoff_sum g n x / n - real_cond_exp M Invariants g x) - (birkhoff_sum h n x / n - real_cond_exp M Invariants h x)"
      by auto
    then have *: "AE x in M. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<le>
      norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) + norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x)"
      by auto
    have "(\<integral>\<^sup>+ x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<le>
      (\<integral>\<^sup>+ x. ennreal(norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x)) + norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M)"
      apply (rule nn_integral_mono_AE) using * by (simp add: ennreal_plus[symmetric] del: ennreal_plus)
    also have "... = (\<integral>\<^sup>+ x. norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) \<partial>M) + (\<integral>\<^sup>+ x. norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M)"
      apply (rule nn_integral_add) apply auto using real_cond_exp_F_meas borel_measurable_cond_exp2 by measurable
    finally have "(\<integral>\<^sup>+ x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<le>
      (\<integral>\<^sup>+ x. norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) \<partial>M) + (\<integral>\<^sup>+ x. norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M)"
      by simp
  }
  then have *: "eventually (\<lambda>n. (\<integral>\<^sup>+ x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<le>
      (\<integral>\<^sup>+ x. norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) \<partial>M) + (\<integral>\<^sup>+ x. norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M))
      sequentially"
    using eventually_at_top_dense by auto
  have **: "eventually (\<lambda>n. (\<integral>\<^sup>+ x. norm(birkhoff_sum f n x / n - real_cond_exp M Invariants f x) \<partial>M) \<ge> 0) sequentially"
    by simp

  have "(\<lambda>n. (\<integral>\<^sup>+ x. norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) \<partial>M)) \<longlonglongrightarrow> 0"
    apply (rule birkhoff_lemma_L1, auto simp add: g_int) unfolding g_def by auto
  moreover have "(\<lambda>n. (\<integral>\<^sup>+ x. norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M)) \<longlonglongrightarrow> 0"
    apply (rule birkhoff_lemma_L1, auto simp add: h_int) unfolding h_def by auto
  ultimately have "(\<lambda>n. (\<integral>\<^sup>+ x. norm(birkhoff_sum g n x / n - real_cond_exp M Invariants g x) \<partial>M) + (\<integral>\<^sup>+ x. norm(birkhoff_sum h n x / n - real_cond_exp M Invariants h x) \<partial>M)) \<longlonglongrightarrow> 0"
    using tendsto_add[of _ 0 _ _ 0] by auto
  then show ?thesis
    using tendsto_sandwich[OF ** *] by auto
qed


subsubsection \<open>Conservativity of skew products\<close>

text \<open>The behaviour of skew-products of the form $(x, y) \mapsto (Tx, y + f x)$ is directly related
to Birkhoff theorem, as the iterates involve the Birkhoff sums in the fiber. Birkhoff theorem
implies that such a skew product is conservative when the function $f$ has vanishing conditional
expectation.

To prove the theorem, assume by contradiction that a set $A$ with positive measure does not
intersect its preimages. Replacing $A$ with a smaller set $C$, we can assume that $C$ is bounded in
the $y$-direction, by a constant $N$, and also that all its nonempty vertical fibers, above the
projection $Cx$, have a measure bounded from below. Then, by Birkhoff theorem, for any $r>0$, most
of the first $n$ preimages of $C$ are contained in the set $\{|y| \leq r n+N\}$, of measure $O(r
n)$. Hence, they can not be disjoint if $r < \mu(C)$. To make this argument rigorous, one should
only consider the preimages whose $x$-component belongs to a set $Dx$ where the Birkhoff sums are
small. This condition has a positive measure if $\mu(Cx) + \mu(Dx) > \mu(M)$, which one can ensure
by taking $Dx$ large enough.\<close>

theorem (in fmpt) skew_product_conservative:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "integrable M f"
    and "AE x in M. real_cond_exp M Invariants f x = 0"
  shows "conservative_mpt (M \<Otimes>\<^sub>M lborel) (\<lambda>(x,y). (T x, y + f x))"
proof (rule conservative_mptI)
  let ?TS = "(\<lambda>(x,y). (T x, y + f x))"
  let ?MS = "M \<Otimes>\<^sub>M (lborel::real measure)"

  have f_meas [measurable]: "f \<in> borel_measurable M" by auto
  have "mpt M T" by (simp add: mpt_axioms)
  with mpt_skew_product_real[OF this f_meas] show "mpt ?MS ?TS" by simp
  then interpret TS: mpt ?MS ?TS by auto

  fix A::"('a \<times> real) set"
  assume A1 [measurable]: "A \<in> sets ?MS" and A2: "emeasure ?MS A > 0"
  have "A = (\<Union>N::nat. A \<inter> {(x,y). abs(y) \<le> N})" by (auto simp add: real_arch_simple)
  then have *: "emeasure ?MS (\<Union>N::nat. A \<inter> {(x,y). abs(y) \<le> N}) > 0"
    using A2 by simp

  have "space ?MS = space M \<times> space (lborel::real measure)" using space_pair_measure by auto
  then have A_inc: "A \<subseteq> space M \<times> space (lborel::real measure)" using sets.sets_into_space[OF A1] by auto

  {
    fix N::nat
    have "{(x, y). abs(y) \<le> real N \<and> x \<in> space M} = space M \<times> {-(real N)..(real N)}" by auto
    then have "{(x, y). \<bar>y\<bar> \<le> real N \<and> x \<in> space M} \<in> sets ?MS" by auto
    then have "A \<inter> {(x, y). \<bar>y\<bar> \<le> real N \<and> x \<in> space M} \<in> sets ?MS" using A1 by auto
    moreover have "A \<inter> {(x,y). abs(y) \<le> real N} = A \<inter> {(x, y). \<bar>y\<bar> \<le> real N \<and> x \<in> space M}"
      using A_inc by blast
    ultimately have "A \<inter> {(x,y). abs(y) \<le> real N} \<in> sets ?MS" by auto
  }
  then have [measurable]: "\<And>N::nat. A \<inter> {(x, y). \<bar>y\<bar> \<le> real N} \<in> sets (M \<Otimes>\<^sub>M borel)" by auto

  have "\<exists>N::nat. emeasure ?MS (A \<inter> {(x,y). abs(y) \<le> N}) > 0"
    apply (rule emeasure_pos_unionE) using * by auto
  then obtain N::nat where N: "emeasure ?MS (A \<inter> {(x,y). abs(y) \<le> N}) > 0"
    by auto

  define B where "B = A \<inter> {(x,y). abs(y) \<le> N}"
  have B_meas [measurable]: "B \<in> sets (M \<Otimes>\<^sub>M lborel)" unfolding B_def by auto
  have "0 < emeasure (M \<Otimes>\<^sub>M lborel) B" unfolding B_def using N by auto
  also have "... = (\<integral>\<^sup>+x. emeasure lborel (Pair x -` B) \<partial>M)"
    apply (rule sigma_finite_measure.emeasure_pair_measure_alt)
    using B_meas by (auto simp add: lborel.sigma_finite_measure_axioms)
  finally have *: "(\<integral>\<^sup>+x. emeasure lborel (Pair x -` B) \<partial>M) > 0" by simp

  have "\<exists>Cx\<in>sets M. \<exists>e::real>0. emeasure M Cx > 0 \<and> (\<forall>x \<in> Cx. emeasure lborel (Pair x -` B) \<ge> e)"
    by (rule not_AE_zero_int_ennreal_E, auto simp add: *)
  then obtain Cx e where [measurable]: "Cx \<in> sets M" and Cxe: "e>(0::real)" "emeasure M Cx > 0" "\<And>x. x \<in> Cx \<Longrightarrow> emeasure lborel (Pair x -` B) \<ge> e"
    by blast
  define C where "C = B \<inter> (Cx \<times> (UNIV::real set))"
  have C_meas [measurable]: "C \<in> sets (M \<Otimes>\<^sub>M lborel)" unfolding C_def using B_meas by auto
  have Cx_fibers: "\<And>x. x \<in> Cx \<Longrightarrow> emeasure lborel (Pair x -` C) \<ge> e" using Cxe(3) C_def by auto

  define c where "c = (measure M Cx)/2"
  have "c > 0" unfolding c_def using Cxe(2) by (simp add: emeasure_eq_measure)

  text \<open>We will apply Birkhoff theorem to show that most preimages of $C$ at time $n$ are contained in a cylinder
  of height roughly $r n$, for some suitably small $r$. How small $r$ should be to get a
  contradiction can be determined at the end of the proof. It turns out that the good condition
  is the following one -- this is by no means obvious now.\<close>

  define r where "r = (if measure M (space M) = 0 then 1 else e * c / (4 * measure M (space M)))"
  have "r > 0" using \<open>e > 0\<close> \<open>c > 0\<close> unfolding r_def
    apply auto using measure_le_0_iff by fastforce
  have pos: "e*c-2*r*measure M (space M) > 0" using \<open>e > 0\<close> \<open>c > 0\<close> unfolding r_def by auto

  define Bgood where "Bgood = {x \<in> space M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> 0}"
  have [measurable]: "Bgood \<in> sets M" unfolding Bgood_def by auto
  have *: "AE x in M. x \<in> Bgood" unfolding Bgood_def using birkhoff_theorem_AE_nonergodic[OF assms(1)] assms(2) by auto
  then have "emeasure M Bgood = emeasure M (space M)"
    by (intro emeasure_eq_AE) auto

  {
    fix x assume "x \<in> Bgood"
    then have "x \<in> space M" unfolding Bgood_def by auto
    have "(\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> 0" using \<open>x \<in> Bgood\<close> unfolding Bgood_def by auto
    moreover have "0 \<in> {-r<..<r}" "open {-r<..<r}" using \<open>r>0\<close> by auto
    ultimately have "eventually (\<lambda>n. birkhoff_sum f n x / n \<in> {-r<..<r}) sequentially"
      using topological_tendstoD by blast
    then obtain n0 where n0: "n0>0" "\<And>n. n \<ge> n0 \<Longrightarrow> birkhoff_sum f n x / n \<in> {-r<..<r}"
      using eventually_sequentially by (metis (mono_tags, lifting) le0 le_simps(3) neq0_conv)
    {
      fix n assume "n \<ge> n0"
      then have "n>0" using \<open>n0>0\<close> by auto
      with n0(2)[OF \<open>n \<ge> n0\<close>] have "abs(birkhoff_sum f n x / n) \<le> r" by auto
      then have "abs(birkhoff_sum f n x) \<le> r * n" using \<open>n>0\<close> by (simp add: divide_le_eq)
    }
    then have "x \<in> (\<Union>n0. {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n})" using \<open>x \<in> space M\<close> by blast
  }
  then have "AE x in M. x \<notin> space M - (\<Union>n0. {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n})"
    using * by auto
  then have eqM: "emeasure M (\<Union>n0. {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n}) = emeasure M (space M)"
    by (intro emeasure_eq_AE) auto

  have "(\<lambda>n0. emeasure M {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n} + c)
          \<longlonglongrightarrow> emeasure M (\<Union>n0. {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n}) + c"
    by (intro tendsto_intros Lim_emeasure_incseq) (auto simp add: incseq_def)
  moreover have "emeasure M (\<Union>n0. {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n}) + c > emeasure M (space M)"
    using eqM \<open>c > 0\<close> emeasure_eq_measure by auto
  ultimately have "eventually (\<lambda>n0. emeasure M {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n} + c > emeasure M (space M)) sequentially"
    unfolding order_tendsto_iff by auto
  then obtain n0 where n0: "emeasure M {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n} + c > emeasure M (space M)"
    using eventually_sequentially by auto

  define Dx where "Dx = {x \<in> space M. \<forall>n\<in>{n0..}. abs(birkhoff_sum f n x) \<le> r * n}"
  have Dx_meas [measurable]: "Dx \<in> sets M" unfolding Dx_def by auto
  have "emeasure M Dx + c \<ge> emeasure M (space M)" using n0 Dx_def by auto

  obtain n1::nat where n1: "n1 > max n0 ((measure M (space M) * 2 * N + e*c*n0 - e*c) / (e*c-2*r*measure M (space M)))"
    by (metis mult.commute mult.left_neutral numeral_One reals_Archimedean3 zero_less_numeral)
  then have "n1 > n0" by auto
  have n1_ineq: "n1 * (e*c-2*r*measure M (space M)) > (measure M (space M) * 2 * N + e*c*n0 - e*c)"
    using n1 pos by (simp add: pos_divide_less_eq)

  define D where "D = (\<lambda>n. Dx \<times> {-r*n1-N..r*n1+N} \<inter> (?TS^^n)-`C)"
  have Dn_meas [measurable]: "D n \<in> sets (M \<Otimes>\<^sub>M lborel)" for n
    unfolding D_def apply (rule TS.T_intersec_meas(2)) using C_meas by auto

  have "emeasure ?MS (D n) \<ge> e * c" if "n \<in> {n0..n1}" for n
  proof -
    have "n \<ge> n0" "n \<le> n1" using that by auto
    {
      fix x assume [simp]: "x \<in> space M"

      define F where "F = {y \<in> {-r*n1-N..r*n1+N}. y + birkhoff_sum f n x \<in> Pair ((T^^n)x) -`C}"
      have [measurable]: "F \<in> sets lborel" unfolding F_def by measurable
      {
        fix y::real
        have "(?TS^^n)(x,y) = ((T^^n)x, y + birkhoff_sum f n x)"
          using skew_product_real_iterates by simp
        then have "(indicator C ((?TS^^n) (x,y))::ennreal) = indicator Cx ((T^^n)x) * indicator (Pair ((T^^n)x) -`C) (y + birkhoff_sum f n x)"
          using C_def by (simp add: indicator_def)
        moreover have "(indicator (D n) (x, y)::ennreal) = indicator Dx x * indicator {-r*n1-N..r*n1+N} y * indicator C ((?TS^^n) (x,y))"
          unfolding D_def by (simp add: indicator_def)
        ultimately have "(indicator (D n) (x, y)::ennreal) = indicator Dx x * indicator {-r*n1-N..r*n1+N} y
            * indicator Cx ((T^^n)x) * indicator (Pair ((T^^n)x) -`C) (y + birkhoff_sum f n x)"
          by (simp add: mult.assoc)
        then have "(indicator (D n) (x, y)::ennreal) = indicator (Dx \<inter> (T^^n)-`Cx) x * indicator F y"
          unfolding F_def by (simp add: indicator_def)
      }
      then have "(\<integral>\<^sup>+y. indicator (D n) (x, y) \<partial>lborel) = (\<integral>\<^sup>+y. indicator (Dx \<inter> (T^^n)-`Cx) x * indicator F y \<partial>lborel)"
        by auto
      also have "... = indicator (Dx \<inter> (T^^n)-`Cx) x * (\<integral>\<^sup>+y. indicator F y \<partial>lborel)"
        by (rule nn_integral_cmult, auto)
      also have "... = indicator (Dx \<inter> (T^^n)-`Cx) x * emeasure lborel F" using \<open>F \<in> sets lborel\<close> by auto
      finally have A: "(\<integral>\<^sup>+y. indicator (D n) (x, y) \<partial>lborel) = indicator (Dx \<inter> (T^^n)-`Cx) x * emeasure lborel F"
        by simp

      have "(\<integral>\<^sup>+y. indicator (D n) (x, y) \<partial>lborel) \<ge> ennreal e * indicator (Dx \<inter> (T^^n)-`Cx) x"
      proof (cases)
        assume "indicator (Dx \<inter> (T^^n)-`Cx) x = (0::ennreal)"
        then show ?thesis by auto
      next
        assume "\<not>(indicator (Dx \<inter> (T^^n)-`Cx) x = (0::ennreal))"
        then have "x \<in> Dx \<inter> (T^^n)-`Cx" by (simp add: indicator_eq_0_iff)
        then have "x \<in> Dx" "(T^^n) x \<in> Cx" by auto
        then have "abs(birkhoff_sum f n x) \<le> r * n" using \<open>n \<in> {n0..n1}\<close> Dx_def by auto
        then have *: "abs(birkhoff_sum f n x) \<le> r * n1" using \<open>n \<le> n1\<close> \<open>r>0\<close>
          by (meson of_nat_le_iff order_trans real_mult_le_cancel_iff2)

        have F_expr: "F = {-r*n1-N..r*n1+N} \<inter> (+)(birkhoff_sum f n x) -` (Pair ((T^^n)x) -`C)"
          unfolding F_def by (auto simp add: add.commute)
        have "(Pair ((T^^n)x) -`C) \<subseteq> {real_of_int (- int N)..real N}" unfolding C_def B_def by auto
        then have "((+)(birkhoff_sum f n x)) -` (Pair ((T^^n)x) -`C) \<subseteq> {-N-birkhoff_sum f n x..N-birkhoff_sum f n x}"
          by auto
        also have "... \<subseteq> {-r * n1 - N .. r * n1 + N}" using * by auto
        finally have "F = ((+)(birkhoff_sum f n x)) -` (Pair ((T^^n)x) -`C)" unfolding F_expr by auto

        then have "emeasure lborel F = emeasure lborel ((+)(birkhoff_sum f n x) -` (Pair ((T^^n)x) -`C))" by auto
        also have "... = emeasure lborel (((+)(birkhoff_sum f n x) -` (Pair ((T^^n)x) -`C)) \<inter> space lborel)" by simp
        also have "... = emeasure (distr lborel borel ((+) (birkhoff_sum f n x))) (Pair ((T^^n)x) -`C)"
          apply (rule emeasure_distr[symmetric]) using C_meas by auto
        also have "... = emeasure lborel (Pair ((T^^n)x) -`C)" using lborel_distr_plus[of "birkhoff_sum f n x"] by simp
        also have "... \<ge> e" using Cx_fibers \<open>(T^^n) x \<in> Cx\<close> by auto
        finally have "emeasure lborel F \<ge> e" by auto
        then show ?thesis using A by (simp add: indicator_def)
      qed
    }
    moreover have "emeasure ?MS (D n) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator (D n) (x, y) \<partial>lborel) \<partial>M)"
      using Dn_meas lborel.emeasure_pair_measure by blast
    ultimately have "emeasure ?MS (D n) \<ge> (\<integral>\<^sup>+x. ennreal e * indicator (Dx \<inter> (T ^^ n) -` Cx) x \<partial>M)"
      by (simp add: nn_integral_mono)
    also have "(\<integral>\<^sup>+x. ennreal e * indicator (Dx \<inter> (T ^^ n) -` Cx) x \<partial>M) = e * (\<integral>\<^sup>+x. indicator (Dx \<inter> (T ^^ n) -` Cx) x \<partial>M)"
      apply (rule nn_integral_cmult) using \<open>e>0\<close> by auto
    also have "... = ennreal e * emeasure M (Dx \<inter> (T ^^ n) -` Cx)" by simp
    finally have *: "emeasure ?MS (D n) \<ge> ennreal e * emeasure M (Dx \<inter> (T ^^ n) -` Cx)" by auto

    have "c + emeasure M (space M) \<le> emeasure M Dx + emeasure M Cx"
      using \<open>emeasure M Dx + c \<ge> emeasure M (space M)\<close> unfolding c_def
      by (auto simp: emeasure_eq_measure ennreal_plus[symmetric] simp del: ennreal_plus)
    also have "... = emeasure M Dx + emeasure M ((T^^n)--`Cx)"
      by (simp add: T_vrestr_same_emeasure(2))
    also have "... = emeasure M (Dx \<union> ((T^^n)--`Cx)) + emeasure M (Dx \<inter> ((T^^n)--`Cx))"
      by (rule emeasure_union_inter, auto)
    also have "... \<le> emeasure M (space M) + emeasure M (Dx \<inter> ((T^^n)-`Cx))"
    proof -
      have "emeasure M (Dx \<union> ((T^^n)--`Cx)) \<le> emeasure M (space M)"
        by (rule emeasure_mono, auto simp add: sets.sets_into_space)
      moreover have "Dx \<inter> ((T^^n)--`Cx) = Dx \<inter> ((T^^n)-`Cx)"
        by (simp add: vrestr_intersec_in_space)
      ultimately show ?thesis by (metis add.commute add_left_mono)
    qed
    finally have "emeasure M (Dx \<inter> ((T^^n)-`Cx)) \<ge> c" by (simp add: emeasure_eq_measure)
    then have "ennreal e * emeasure M (Dx \<inter> ((T^^n)-`Cx)) \<ge> ennreal e * c" using \<open>e > 0\<close>
      using mult_left_mono by fastforce
    with * show "emeasure ?MS (D n) \<ge> e * c"
      using \<open>0<c\<close> \<open>0<e\<close> by (auto simp: ennreal_mult[symmetric])
  qed

  have "\<not>(disjoint_family_on D {n0..n1})"
  proof
    assume D: "disjoint_family_on D {n0..n1}"
    have "emeasure lborel {-r*n1-N..r*n1+N} = (r * real n1 + real N) - (- r * real n1 - real N)"
      apply (rule emeasure_lborel_Icc) using \<open>r>0\<close> by auto
    then have *: "emeasure lborel {-r*n1-N..r*n1+N} = ennreal(2 * r * real n1 + 2 * real N)"
      by (auto simp: ac_simps)

    have "ennreal(e * c) * (real n1 - real n0 + 1) = ennreal(e*c) * card {n0..n1}"
      using \<open>n1 > n0\<close> by (auto simp: ennreal_of_nat_eq_real_of_nat Suc_diff_le ac_simps of_nat_diff)
    also have "... = (\<Sum>n\<in>{n0..n1}. ennreal(e*c))"
      by (simp add: ac_simps)
    also have "... \<le> (\<Sum>n\<in>{n0..n1}. emeasure ?MS (D n))"
      using \<open>\<And>n. n \<in> {n0..n1} \<Longrightarrow> emeasure ?MS (D n) \<ge> e * c\<close> by (meson sum_mono)
    also have "... = emeasure ?MS (\<Union>n\<in>{n0..n1}. D n)"
      apply (rule sum_emeasure) using Dn_meas by (auto simp add: D)
    also have "... \<le> emeasure ?MS (space M \<times> {-r*n1-N..r*n1+N})"
      apply (rule emeasure_mono) unfolding D_def using sets.sets_into_space[OF Dx_meas] by auto
    also have "... = emeasure M (space M) * emeasure lborel {-r*n1-N..r*n1+N}"
      by (rule sigma_finite_measure.emeasure_pair_measure_Times, auto simp add: lborel.sigma_finite_measure_axioms)
    also have "... = emeasure M (space M) * ennreal(2 * r * real n1 + 2 * real N)"
      using * by auto
    finally have "ennreal(e * c) * (real n1- real n0+1) \<le> emeasure M (space M) * ennreal(2 * r * real n1 + 2 * real N)" by simp
    then have "e*c * (real n1- real n0 + 1) \<le> measure M (space M) * (2 * r * real n1 + 2 * real N)"
      using \<open>0<r\<close> \<open>0<e\<close> \<open>0<c\<close> \<open>n0 < n1\<close> emeasure_eq_measure by (auto simp: ennreal_mult'[symmetric] simp del: ennreal_plus)
    then have "0 \<le> measure M (space M) * (2 * r * real n1 + 2 * real N) - e*c * (real n1- real n0 + 1)" by auto
    also have "... = (measure M (space M) * 2 * N + e*c*n0 - e*c) - n1 * (e*c-2*r*measure M (space M))"
      by algebra
    finally have "n1 * (e*c-2*r*measure M (space M)) \<le> measure M (space M) * 2 * N + e*c*n0 - e*c"
      by linarith
    then show False using n1_ineq by auto
  qed
  then obtain n m where nm: "n<m" "D m \<inter> D n \<noteq> {}" unfolding disjoint_family_on_def by (metis inf_sup_aci(1) linorder_cases)
  define k where "k = m-n"
  then have "k>0" "D (n+k) \<inter> D n \<noteq> {}" using nm by auto
  then have "((?TS^^(n+k))-`A) \<inter> ((?TS^^n)-`A) \<noteq> {}" unfolding D_def C_def B_def by auto
  moreover have "((?TS^^(n+k))-`A) \<inter> ((?TS^^n)-`A) = (?TS^^n)-`(((?TS^^k)-`A) \<inter> A)"
    using funpow_add by (simp add: add.commute funpow_add set.compositionality)
  ultimately have "((?TS^^k)-`A) \<inter> A \<noteq> {}" by auto
  then show "\<exists>k>0. ((?TS^^k)-`A) \<inter> A \<noteq> {}" using \<open>k>0\<close> by auto
qed



subsubsection \<open>Oscillations around the limit in Birkhoff theorem\<close>

text \<open>In this paragraph, we prove that, in Birkhoff theorem with vanishing limit, the Birkhoff sums
are infinitely many times arbitrarily close to $0$, both on the positive and the negative side.

In the ergodic case, this statement implies for instance that if the Birkhoff sums of an integrable
function tend to infinity almost everywhere, then the integral of the function can not vanish, it
has to be strictly positive (while Birkhoff theorem per se does not exclude the convergence to
infinity, at a rate slower than linear). This converts a qualitative information (convergence to
infinity at an unknown rate) to a quantitative information (linear convergence to infinity). This
result (sometimes known as Atkinson's Lemma) has been reinvented many times, for instance by Kesten
and by Guivarch. It plays an important role in the study of random products of matrices.

This is essentially a consequence of the conservativity of the corresponding skew-product, proved in
\verb+skew_product_conservative+. Indeed, this implies that, starting from a small set $X \times
[-e/2, e/2]$, the skew-product comes back infinitely often to itself, which implies that the
Birkhoff sums at these times are bounded by $e$.

To show that the Birkhoff sums come back to $[0,e]$ is a little bit more tricky. Argue by
contradiction, and induce on $A \times [0,e/2]$ where $A$ is the set of points where the Birkhoff
sums don't come back to $[0,e]$. Then the second coordinate decreases strictly when one iterates the
skew product, which is not compatible with conservativity.\<close>

lemma birkhoff_sum_small_asymp_lemma:
  assumes [measurable]: "integrable M f"
    and "AE x in M. real_cond_exp M Invariants f x = 0" "e>(0::real)"
  shows "AE x in M. infinite {n. birkhoff_sum f n x \<in> {0..e}}"
proof -
  have [measurable]: "f \<in> borel_measurable M" by auto
  have [measurable]: "\<And>N. {x \<in> space M. \<exists>N. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}} \<in> sets M" by auto

  {
    fix N assume "N>(0::nat)"
    define Ax where "Ax = {x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}}"
    then have [measurable]: "Ax \<in> sets M" by auto
    define A where "A = Ax \<times> {0..e/2}"
    then have A_meas [measurable]: "A \<in> sets (M \<Otimes>\<^sub>M lborel)" by auto

    define TN where "TN = T^^N"
    interpret TN: fmpt M TN
      unfolding TN_def using fmpt_power by auto
    define fN where "fN = birkhoff_sum f N"
    have "TN.birkhoff_sum fN n x = birkhoff_sum f (n*N) x" for n x
    proof (induction n)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      have "TN.birkhoff_sum fN (Suc n) x = TN.birkhoff_sum fN n x + fN ((TN^^n) x)"
        using TN.birkhoff_sum_cocycle[of fN n 1] by auto
      also have "... = birkhoff_sum f (n*N) x + birkhoff_sum f N ((TN^^n) x)"
        using Suc.IH fN_def by auto
      also have "... = birkhoff_sum f (n*N+N) x" unfolding TN_def
        by (subst funpow_mult, subst mult.commute[of N n], rule birkhoff_sum_cocycle[of f "n*N" N x, symmetric])
      finally show ?case by (simp add: add.commute)
    qed
    then have not0e: "\<And>x n. x \<in> Ax \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> TN.birkhoff_sum fN n x \<notin> {0..e}" unfolding Ax_def by auto

    let ?TS = "(\<lambda>(x,y). (T x, y + f x))"
    let ?MS = "M \<Otimes>\<^sub>M (lborel::real measure)"
    interpret TS: conservative_mpt ?MS ?TS
      by (rule skew_product_conservative, auto simp add: assms)

    let ?TSN = "(\<lambda>(x,y). (TN x, y + fN x))"
    have *:"?TSN = ?TS^^N" unfolding TN_def fN_def using skew_product_real_iterates by auto
    interpret TSN: conservative_mpt ?MS ?TSN
      using * TS.conservative_mpt_power by auto

    define MA TA where "MA = restrict_space ?MS A" and "TA = TSN.induced_map A"
    interpret TA: conservative_mpt MA TA unfolding MA_def TA_def
      by (rule TSN.induced_map_conservative_mpt, measurable)
    have *: "\<And> x y. snd (TA (x,y)) = snd (x,y) + TN.birkhoff_sum fN (TSN.return_time_function A (x,y)) x"
      unfolding TA_def TSN.induced_map_def using TN.skew_product_real_iterates Pair_def by auto
    have [measurable]: "snd \<in> borel_measurable ?MS" by auto
    then have [measurable]: "snd \<in> borel_measurable MA" unfolding MA_def using measurable_restrict_space1 by blast

    have "AE z in MA. z \<in> TSN.recurrent_subset A"
      unfolding MA_def using TSN.induced_map_recurrent_typical(1)[OF A_meas].
    moreover
    {
      fix z assume z: "z \<in> TSN.recurrent_subset A"
      define x y where "x = fst z" and "y = snd z"
      then have "z = (x,y)" by simp
      have "z \<in> A" using z "TSN.recurrent_subset_incl"(1) by auto
      then have "x \<in> Ax" "y \<in> {0..e/2}" unfolding A_def x_def y_def by auto
      define y2 where "y2 = y + TN.birkhoff_sum fN (TSN.return_time_function A (x,y)) x"
      have "y2 = snd (TA z)" unfolding y2_def using * \<open>z = (x, y)\<close> by force
      moreover have "TA z \<in> A" unfolding TA_def using \<open>z \<in> A\<close> TSN.induced_map_stabilizes_A by auto
      ultimately have "y2 \<in> {0..e/2}" unfolding A_def by auto

      have "TSN.return_time_function A (x,y) \<noteq> 0"
        using \<open>z = (x,y)\<close> \<open>z \<in> TSN.recurrent_subset A\<close> TSN.return_time0[of A] by fast
      then have "TN.birkhoff_sum fN (TSN.return_time_function A (x,y)) x \<notin> {0..e}"
        using not0e[OF \<open>x \<in> Ax\<close>] by auto
      moreover have "TN.birkhoff_sum fN (TSN.return_time_function A (x,y)) x \<in> {-e..e}"
        using \<open>y \<in> {0..e/2}\<close> \<open>y2 \<in> {0..e/2}\<close> y2_def by auto
      ultimately have "TN.birkhoff_sum fN (TSN.return_time_function A (x,y)) x \<in> {-e..<0}"
        by auto
      then have "y2 < y" using y2_def by auto
      then have "snd(TA z) < snd z" unfolding y_def using \<open>y2 = snd (TA z)\<close> by auto
    }
    ultimately have a: "AE z in MA. snd(TA z) < snd z" by auto
    then have "AE z in MA. snd(TA z) \<le> snd z" by auto
    then have "AE z in MA. snd(TA z) = snd z" using TA.AE_decreasing_then_invariant[of snd] by auto
    then have "AE z in MA. False" using a by auto
    then have "space MA \<in> null_sets MA" by (simp add: AE_iff_null_sets)
    then have "emeasure MA A = 0" by (metis A_meas MA_def null_setsD1 space_restrict_space2)
    then have "emeasure ?MS A = 0" unfolding MA_def
      by (metis A_meas emeasure_restrict_space sets.sets_into_space sets.top space_restrict_space space_restrict_space2)
    moreover have "emeasure ?MS A = emeasure M Ax * emeasure lborel {0..e/2}"
      unfolding A_def by (intro lborel.emeasure_pair_measure_Times) auto
    ultimately have "emeasure M {x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}} = 0" using \<open>e>0\<close> Ax_def by simp
    then have "{x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}} \<in> null_sets M" by auto
  }
  then have "(\<Union>N\<in>{0<..}. {x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}}) \<in> null_sets M" by (auto simp: greaterThan_0)
  moreover have "{x \<in> space M. \<not>(infinite {n. birkhoff_sum f n x \<in> {0..e}})} \<subseteq> (\<Union>N\<in>{0<..}. {x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}})"
  proof
    fix x assume H: "x \<in> {x \<in> space M. \<not>(infinite {n. birkhoff_sum f n x \<in> {0..e}})}"
    then have "x \<in> space M" by auto
    have *: "finite {n. birkhoff_sum f n x \<in> {0..e}}" using H by auto
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> n \<notin> {n. birkhoff_sum f n x \<in> {0..e}}"
      by (metis finite_nat_set_iff_bounded not_less)
    then have "x \<in> {x \<in> space M. \<forall>n\<in>{N+1..}. birkhoff_sum f n x \<notin> {0..e}}" using \<open>x \<in> space M\<close> by auto
    moreover have "N+1>0" by auto
    ultimately show "x \<in> (\<Union>N\<in>{0<..}. {x \<in> space M. \<forall>n\<in>{N..}. birkhoff_sum f n x \<notin> {0..e}})" by auto
  qed
  ultimately show ?thesis unfolding eventually_ae_filter by auto
qed

theorem birkhoff_sum_small_asymp_pos_nonergodic:
  assumes [measurable]: "integrable M f" and "e > (0::real)"
  shows "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x .. n * real_cond_exp M Invariants f x + e}}"
proof -
  define g where "g = (\<lambda>x. f x - real_cond_exp M Invariants f x)"
  have g_meas [measurable]: "integrable M g" unfolding g_def using real_cond_exp_int(1)[OF assms(1)] assms(1) by auto
  have "AE x in M. real_cond_exp M Invariants (real_cond_exp M Invariants f) x = real_cond_exp M Invariants f x"
    by (rule real_cond_exp_F_meas, auto simp add: real_cond_exp_int(1)[OF assms(1)])
  then have *: "AE x in M. real_cond_exp M Invariants g x = 0"
    unfolding g_def using real_cond_exp_diff[OF assms(1) real_cond_exp_int(1)[OF assms(1)]] by auto
  have "AE x in M. infinite {n. birkhoff_sum g n x \<in> {0..e}}"
    by (rule birkhoff_sum_small_asymp_lemma, auto simp add: \<open>e>0\<close> * g_meas)
  moreover
  {
    fix x assume "x \<in> space M" "infinite {n. birkhoff_sum g n x \<in> {0..e}}"
    {
      fix n assume H: "birkhoff_sum g n x \<in> {0..e}"
      have "birkhoff_sum g n x = birkhoff_sum f n x - birkhoff_sum (real_cond_exp M Invariants f) n x"
        unfolding g_def using birkhoff_sum_diff by auto
      also have "... = birkhoff_sum f n x - n * real_cond_exp M Invariants f x"
        using birkhoff_sum_of_invariants \<open>x \<in> space M\<close> by auto
      finally have "birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x .. n * real_cond_exp M Invariants f x + e}" using H by simp
    }
    then have "{n. birkhoff_sum g n x \<in> {0..e}} \<subseteq> {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x .. n * real_cond_exp M Invariants f x + e}}"
      by auto
    then have "infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x .. n * real_cond_exp M Invariants f x + e}}"
      using \<open>infinite {n. birkhoff_sum g n x \<in> {0..e}}\<close> finite_subset by blast
  }
  ultimately show ?thesis by auto
qed

theorem birkhoff_sum_small_asymp_neg_nonergodic:
  assumes [measurable]: "integrable M f" and "e > (0::real)"
  shows "AE x in M. infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x - e .. n * real_cond_exp M Invariants f x}}"
proof -
  define g where "g = (\<lambda>x. real_cond_exp M Invariants f x - f x)"
  have g_meas [measurable]: "integrable M g" unfolding g_def using real_cond_exp_int(1)[OF assms(1)] assms(1) by auto
  have "AE x in M. real_cond_exp M Invariants (real_cond_exp M Invariants f) x = real_cond_exp M Invariants f x"
    by (rule real_cond_exp_F_meas, auto simp add: real_cond_exp_int(1)[OF assms(1)])
  then have *: "AE x in M. real_cond_exp M Invariants g x = 0"
    unfolding g_def using real_cond_exp_diff[OF real_cond_exp_int(1)[OF assms(1)] assms(1)] by auto
  have "AE x in M. infinite {n. birkhoff_sum g n x \<in> {0..e}}"
    by (rule birkhoff_sum_small_asymp_lemma, auto simp add: \<open>e>0\<close> * g_meas)
  moreover
  {
    fix x assume "x \<in> space M" "infinite {n. birkhoff_sum g n x \<in> {0..e}}"
    {
      fix n assume H: "birkhoff_sum g n x \<in> {0..e}"
      have "birkhoff_sum g n x = birkhoff_sum (real_cond_exp M Invariants f) n x - birkhoff_sum f n x"
        unfolding g_def using birkhoff_sum_diff by auto
      also have "... = n * real_cond_exp M Invariants f x - birkhoff_sum f n x"
        using birkhoff_sum_of_invariants \<open>x \<in> space M\<close> by auto
      finally have "birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x - e .. n * real_cond_exp M Invariants f x}" using H by simp
    }
    then have "{n. birkhoff_sum g n x \<in> {0..e}} \<subseteq> {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x - e .. n * real_cond_exp M Invariants f x}}"
      by auto
    then have "infinite {n. birkhoff_sum f n x \<in> {n * real_cond_exp M Invariants f x - e .. n * real_cond_exp M Invariants f x}}"
      using \<open>infinite {n. birkhoff_sum g n x \<in> {0..e}}\<close> finite_subset by blast
  }
  ultimately show ?thesis by auto
qed


subsubsection \<open>Conditional expectation for the induced map\<close>

text \<open>Thanks to Birkhoff theorem, one can relate conditional expectations with respect to the invariant
sigma algebra, for a map and for a corresponding induced map, as follows.\<close>

proposition Invariants_cond_exp_induced_map:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "A \<in> sets M" "integrable M f"
  defines "MA \<equiv> restrict_space M A" and "TA \<equiv> induced_map A" and "fA \<equiv> induced_function A f"
  shows "AE x in MA. real_cond_exp MA (qmpt.Invariants MA TA) fA x
      = real_cond_exp M Invariants f x * real_cond_exp MA (qmpt.Invariants MA TA) (return_time_function A) x"
proof -
  interpret A: fmpt MA TA unfolding MA_def TA_def by (rule induced_map_fmpt[OF assms(1)])

  have "integrable M fA" unfolding fA_def using induced_function_integral_nonergodic(1) assms by auto
  then have "integrable MA fA" unfolding MA_def
    by (metis assms(1) integrable_mult_indicator integrable_restrict_space sets.Int_space_eq2)
  then have a: "AE x in MA. (\<lambda>n. A.birkhoff_sum fA n x / n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants fA x"
    using A.birkhoff_theorem_AE_nonergodic by auto

  have "AE x in M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    using birkhoff_theorem_AE_nonergodic assms(2) by auto
  then have b: "AE x in MA. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    unfolding MA_def by (metis (mono_tags, lifting) AE_restrict_space_iff assms(1) eventually_mono sets.Int_space_eq2)

  define phiA where "phiA = (\<lambda>x. return_time_function A x)"
  have "integrable M phiA" unfolding phiA_def using return_time_integrable by auto
  then have "integrable MA phiA" unfolding MA_def
    by (metis assms(1) integrable_mult_indicator integrable_restrict_space sets.Int_space_eq2)
  then have c: "AE x in MA. (\<lambda>n. A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x"
    using A.birkhoff_theorem_AE_nonergodic by auto

  have "A-recurrent_subset A \<in> null_sets M" using Poincare_recurrence_thm(1)[OF assms(1)] by auto
  then have "A - recurrent_subset A \<in> null_sets MA" unfolding MA_def
    by (metis Diff_subset assms(1) emeasure_restrict_space null_setsD1 null_setsD2 null_setsI sets.Int_space_eq2 sets_restrict_space_iff)
  then have "AE x in MA. x \<in> recurrent_subset A"
    by (simp add: AE_iff_null MA_def null_setsD2 set_diff_eq space_restrict_space2)
  moreover have "\<And>x. x \<in> recurrent_subset A \<Longrightarrow> phiA x > 0" unfolding phiA_def using return_time0 by fastforce
  ultimately have *: "AE x in MA. phiA x > 0" by auto
  have d: "AE x in MA. real_cond_exp MA A.Invariants phiA x > 0"
    by (rule A.real_cond_exp_gr_c, auto simp add: * \<open>integrable MA phiA\<close>)

  {
    fix x
    assume A: "(\<lambda>n. A.birkhoff_sum fA n x / n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants fA x"
       and B: "(\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
       and C: "(\<lambda>n. A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x"
       and D: "real_cond_exp MA A.Invariants phiA x > 0"
    define R where "R = (\<lambda>n. A.birkhoff_sum phiA n x)"

    have D2: "ereal(real_cond_exp MA A.Invariants phiA x) > 0" using D by simp
    have "\<And>n. real(R n)/ n = A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n" unfolding R_def A.birkhoff_sum_def by auto
    moreover have "(\<lambda>n. A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x" using C by auto
    ultimately have Rnn: "(\<lambda>n. real(R n)/n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x" by presburger

    have "\<And>n. ereal(real(R n))/ n = ereal(A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n)" unfolding R_def A.birkhoff_sum_def by auto
    moreover have "(\<lambda>n. ereal(A.birkhoff_sum (\<lambda>x. real(phiA x)) n x / n)) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x" using C by auto
    ultimately have i: "(\<lambda>n. ereal(real(R n))/n) \<longlonglongrightarrow> real_cond_exp MA A.Invariants phiA x" by auto
    have ii: "(\<lambda>n. real n) \<longlonglongrightarrow> \<infinity>" by (rule id_nat_ereal_tendsto_PInf)
    have iii: "(\<lambda>n. ereal(real(R n))/n * real n) \<longlonglongrightarrow> \<infinity>" using tendsto_mult_ereal_PInf[OF i D2 ii] by simp
    have "\<And>n. n > 0 \<Longrightarrow> ereal(real(R n))/n * real n = R n" by auto
    then have "eventually (\<lambda>n. ereal(real(R n))/n * real n = R n) sequentially" using eventually_at_top_dense by auto
    then have "(\<lambda>n. real(R n)) \<longlonglongrightarrow> \<infinity>" using iii by (simp add: filterlim_cong)
    then have "(\<lambda>n. birkhoff_sum f (R n) x / (R n)) \<longlonglongrightarrow> real_cond_exp M Invariants f x" using limit_along_weak_subseq B by auto
    then have l: "(\<lambda>n. (birkhoff_sum f (R n) x / (R n)) * ((R n)/n)) \<longlonglongrightarrow> real_cond_exp M Invariants f x * real_cond_exp MA A.Invariants phiA x"
      by (rule tendsto_mult, simp add: Rnn)
    obtain N where N: "\<And>n. n > N \<Longrightarrow> R n > 0" using \<open>(\<lambda>n. real(R n)) \<longlonglongrightarrow> \<infinity>\<close>
      by (metis (full_types) eventually_at_top_dense filterlim_iff filterlim_weak_subseq)
    then have "\<And>n. n > N \<Longrightarrow> (birkhoff_sum f (R n) x / (R n)) * ((R n)/n) = birkhoff_sum f (R n) x / n"
      by auto
    then have "eventually (\<lambda>n. (birkhoff_sum f (R n) x / (R n)) * ((R n)/n) = birkhoff_sum f (R n) x / n) sequentially"
      by simp
    with tendsto_cong[OF this] have main_limit: "(\<lambda>n. birkhoff_sum f (R n) x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x * real_cond_exp MA A.Invariants phiA x"
      using l by auto
    have "\<And>n. birkhoff_sum f (R n) x = A.birkhoff_sum fA n x"
      unfolding R_def fA_def phiA_def TA_def using induced_function_birkhoff_sum[OF assms(1)] by simp
    then have "\<And>n. birkhoff_sum f (R n) x /n = A.birkhoff_sum fA n x / n" by simp
    then have "(\<lambda>n. A.birkhoff_sum fA n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x * real_cond_exp MA A.Invariants phiA x"
      using main_limit by presburger
    then have "real_cond_exp MA A.Invariants fA x = real_cond_exp M Invariants f x * real_cond_exp MA A.Invariants phiA x"
      using A LIMSEQ_unique by auto
  }
  then show ?thesis using a b c d unfolding phiA_def by auto
qed

corollary Invariants_cond_exp_induced_map_0:
  fixes f::"'a \<Rightarrow> real"
  assumes [measurable]: "A \<in> sets M" "integrable M f" and "AE x in M. real_cond_exp M Invariants f x = 0"
  defines "MA \<equiv> restrict_space M A" and "TA \<equiv> induced_map A" and "fA \<equiv> induced_function A f"
  shows "AE x in MA. real_cond_exp MA (qmpt.Invariants MA TA) fA x = 0"
proof -
  have "AE x in MA. real_cond_exp M Invariants f x = 0" unfolding MA_def
    apply (subst AE_restrict_space_iff) using assms(3) by auto
  then show ?thesis unfolding MA_def TA_def fA_def using Invariants_cond_exp_induced_map[OF assms(1) assms(2)]
    by auto
qed

end (*of locale fmpt*)
end (*of Invariants.thy*)

