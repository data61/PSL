section \<open>Helpers\<close>

theory Helpers imports Main begin

text \<open>
  First, we will prove a few lemmas unrelated to graphs or Menger's Theorem.  These lemmas
  will simplify some of the other proof steps.
\<close>

text \<open>
  If two finite sets have different cardinality, then there exists an element in the larger set
  that is not in the smaller set.
\<close>
lemma card_finite_less_ex:
  assumes finite_A: "finite A"
      and finite_B: "finite B"
      and card_AB: "card A < card B"
  shows "\<exists>b \<in> B. b \<notin> A"
proof-
  have "card (B - A) > 0" using finite_A finite_B card_AB
    by (meson Diff_eq_empty_iff card_eq_0_iff card_mono finite_Diff gr0I leD)
  then show ?thesis using finite_B
    by (metis Diff_eq_empty_iff card_0_eq finite_Diff neq_iff subsetI)
qed

text \<open>
  The cardinality of the union of two disjoint finite sets is the sum of their cardinalities
  even if we intersect everything with a fixed set @{term X}.
\<close>
lemma card_intersect_sum_disjoint:
  assumes "finite B" "finite C" "A = B \<union> C" "B \<inter> C = {}"
    shows "card (A \<inter> X) = card (B \<inter> X) + card (C \<inter> X)"
  by (metis (no_types, lifting) Un_Diff_Int assms card_Un_disjoint finite_Int inf.commute
      inf_sup_distrib2 sup_eq_bot_iff)

text \<open>
  If @{term x} is in a list @{term xs} but is not its last element, then it is also in
  @{term "butlast xs"}.
\<close>
lemma set_butlast: "\<lbrakk> x \<in> set xs; x \<noteq> last xs \<rbrakk> \<Longrightarrow> x \<in> set (butlast xs)"
  by (metis butlast.simps(2) in_set_butlast_appendI last.simps last_appendR
      list.set_intros(1) split_list_first)

text \<open>
  If a property @{term P} is satisfiable and if we have a weight measure mapping into the natural
  numbers, then there exists an element of minimum weight satisfying @{term P} because the
  natural numbers are well-ordered.
\<close>
lemma arg_min_ex:
  fixes P :: "'a \<Rightarrow> bool" and weight :: "'a \<Rightarrow> nat"
  assumes "\<exists>x. P x"
  obtains x where "P x" "\<And>y. P y \<Longrightarrow> weight x \<le> weight y"
proof (cases "\<exists>x. P x \<and> weight x = 0")
  case True then show ?thesis using that by auto
next
  case False then show ?thesis
    using that ex_least_nat_le[of "\<lambda>n. \<exists>x. P x \<and> weight x = n"] assms by (metis not_le_imp_less)
qed

end
