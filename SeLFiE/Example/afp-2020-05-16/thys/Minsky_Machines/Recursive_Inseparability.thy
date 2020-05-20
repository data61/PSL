section \<open>Recursive inseperability\<close>

theory Recursive_Inseparability
  imports "Recursion-Theory-I.RecEnSet"
begin

text \<open>Two sets $A$ and $B$ are recursively inseparable if there is no computable set that
contains $A$ and is disjoint from $B$. In particular, a set is computable if the set and its
complement are recursively inseparable. The terminology was introduced by Smullyan~@{cite R58}.
The underlying idea can be traced back to Rosser, who essentially showed that provable and
disprovable sentences are \emph{arithmetically} inseparable in Peano Arithmetic~@{cite R36};
see also Kleene's symmetric version of Gödel's incompleteness theorem~@{cite K52}.

Here we formalize recursive inseparability on top of the \texttt{Recursion-Theory-I} AFP
entry~@{cite RTI}. Our main result is a version of Rice' theorem that states that the index
sets of any two given recursively enumerable sets are recursively inseparable.\<close>

subsection \<open>Definition and basic facts\<close>

text \<open>Two sets $A$ and $B$ are recursively inseparable if there are no decidable sets $X$ such
that $A$ is a subset of $X$ and $X$ is disjoint from $B$.\<close>

definition rec_inseparable where
  "rec_inseparable A B \<equiv> \<forall>X. A \<subseteq> X \<and> B \<subseteq> - X \<longrightarrow> \<not> computable X"

lemma rec_inseparableI:
  "(\<And>X. A \<subseteq> X \<Longrightarrow> B \<subseteq> - X \<Longrightarrow> computable X \<Longrightarrow> False) \<Longrightarrow> rec_inseparable A B"
  unfolding rec_inseparable_def by blast

lemma rec_inseparableD:
  "rec_inseparable A B \<Longrightarrow> A \<subseteq> X \<Longrightarrow> B \<subseteq> - X \<Longrightarrow> computable X \<Longrightarrow> False"
  unfolding rec_inseparable_def by blast

text \<open>Recursive inseperability is symmetric and enjoys a monotonicity property.\<close>

lemma rec_inseparable_symmetric:
  "rec_inseparable A B \<Longrightarrow> rec_inseparable B A"
  unfolding rec_inseparable_def computable_def by (metis double_compl)

lemma rec_inseparable_mono:
  "rec_inseparable A B \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> rec_inseparable A' B'"
  unfolding rec_inseparable_def by (meson subset_trans)

text \<open>Many-to-one reductions apply to recursive inseparability as well.\<close>

lemma rec_inseparable_many_reducible:
  assumes "total_recursive f" "rec_inseparable (f -` A) (f -` B)"
  shows "rec_inseparable A B"
proof (intro rec_inseparableI)
  fix X assume "A \<subseteq> X" "B \<subseteq> - X" "computable X"
  moreover have "many_reducible_to (f -` X) X" using assms(1)
    by (auto simp: many_reducible_to_def many_reducible_to_via_def)
  ultimately have "computable (f -` X)" and "(f -` A) \<subseteq> (f -` X)" and "(f -` B) \<subseteq> - (f -` X)"
    by (auto dest!: m_red_to_comp)
  then show "False" using assms(2) unfolding rec_inseparable_def by blast
qed

text \<open>Recursive inseparability of $A$ and $B$ holds vacuously if $A$ and $B$ are not disjoint.\<close>

lemma rec_inseparable_collapse:
  "A \<inter> B \<noteq> {} \<Longrightarrow> rec_inseparable A B"
  by (auto simp: rec_inseparable_def)

text \<open>Recursive inseparability is intimately connected to non-computability.\<close>

lemma rec_inseparable_non_computable:
  "A \<inter> B = {} \<Longrightarrow> rec_inseparable A B \<Longrightarrow> \<not> computable A"
  by (auto simp: rec_inseparable_def)

lemma computable_rec_inseparable_conv:
  "computable A \<longleftrightarrow> \<not> rec_inseparable A (- A)"
  by (auto simp: computable_def rec_inseparable_def)

subsection \<open>Rice's theorem\<close>

text \<open>We provide a stronger version of Rice's theorem compared to @{cite RTI}.
Unfolding the definition of recursive inseparability, it states that there are no decidable
sets $X$ such that
\begin{itemize}
\item there is a r.e.\ set such that all its indices are elements of $X$; and
\item there is a r.e.\ set such that none of its indices are elements of $X$.
\end{itemize}
This is true even if $X$ is not an index set (i.e., if an index of a r.e.\ set is an element
of $X$, then $X$ contains all indices of that r.e.\ set), which is a requirement of Rice's
theorem in @{cite RTI}.\<close>

lemma c_pair_inj':
  "c_pair x1 y1 = c_pair x2 y2 \<longleftrightarrow> x1 = x2 \<and> y1 = y2"
  by (metis c_fst_of_c_pair c_snd_of_c_pair)

lemma Rice_rec_inseparable:
  "rec_inseparable {k. nat_to_ce_set k = nat_to_ce_set n} {k. nat_to_ce_set k = nat_to_ce_set m}"
proof (intro rec_inseparableI, goal_cases)
  case (1 X)
  text \<open>Note that @{thm Rice_2} is not applicable because X may not be an index set.\<close>
  let ?Q = "{q. s_ce q q \<in> X} \<times> nat_to_ce_set m \<union> {q. s_ce q q \<in> - X} \<times> nat_to_ce_set n"
  have "?Q \<in> ce_rels"
    using 1(3) ce_set_lm_5 comp2_1[OF s_ce_is_pr id1_1 id1_1] unfolding computable_def
    by (intro ce_union[of "ce_rel_to_set _" "ce_rel_to_set _", folded ce_rel_lm_32 ce_rel_lm_8]
      ce_rel_lm_29 nat_to_ce_set_into_ce) blast+
  then obtain q where "nat_to_ce_set q = {c_pair q x |q x. (q, x) \<in> ?Q}"
    unfolding ce_rel_lm_8 ce_rel_to_set_def by (metis (no_types, lifting) nat_to_ce_set_srj)
  from eqset_imp_iff[OF this, of "c_pair q _"]
  have "nat_to_ce_set (s_ce q q) = (if s_ce q q \<in> X then nat_to_ce_set m else nat_to_ce_set n)"
    by (auto simp: s_lm c_pair_inj' nat_to_ce_set_def fn_to_set_def pr_conv_1_to_2_def)
  then show ?case using 1(1,2)[THEN subsetD, of "s_ce q q"] by (auto split: if_splits)
qed

end