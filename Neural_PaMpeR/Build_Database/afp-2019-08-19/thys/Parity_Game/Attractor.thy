section \<open>Attractor Sets\<close>
text \<open>\label{sec:attractor}\<close>

theory Attractor
imports
  Main
  AttractingStrategy
begin

text \<open>Here we define the @{term p}-attractor of a set of nodes.\<close>

context ParityGame begin

text \<open>We define the conditions for a node to be directly attracted from a given set.\<close>
definition directly_attracted :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "directly_attracted p S \<equiv> {v \<in> V - S. \<not>deadend v \<and>
      (v \<in> VV p   \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> S))
    \<and> (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> S))}"

abbreviation "attractor_step p W S \<equiv> W \<union> S \<union> directly_attracted p S"

text \<open>The \<open>p\<close>-attractor set of \<open>W\<close>, defined as a least fixed point.\<close>
definition attractor :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "attractor p W = lfp (attractor_step p W)"

subsection \<open>@{const directly_attracted}\<close>

text \<open>Show a few basic properties of @{const directly_attracted}.\<close>
lemma directly_attracted_disjoint     [simp]: "directly_attracted p W \<inter> W = {}"
  and directly_attracted_empty        [simp]: "directly_attracted p {} = {}"
  and directly_attracted_V_empty      [simp]: "directly_attracted p V = {}"
  and directly_attracted_bounded_by_V [simp]: "directly_attracted p W \<subseteq> V"
  and directly_attracted_contains_no_deadends [elim]: "v \<in> directly_attracted p W \<Longrightarrow> \<not>deadend v"
  unfolding directly_attracted_def by blast+

subsection \<open>\<open>attractor_step\<close>\<close>

lemma attractor_step_empty: "attractor_step p {} {} = {}"
  and attractor_step_bounded_by_V: "\<lbrakk> W \<subseteq> V; S \<subseteq> V \<rbrakk> \<Longrightarrow> attractor_step p W S \<subseteq> V"
  by simp_all

text \<open>
  The definition of @{const attractor} uses @{const lfp}.  For this to be well-defined, we
  need show that \<open>attractor_step\<close> is monotone.
\<close>

lemma attractor_step_mono: "mono (attractor_step p W)"
  unfolding directly_attracted_def by (rule monoI) auto

subsection \<open>Basic Properties of an Attractor\<close>

lemma attractor_unfolding: "attractor p W = attractor_step p W (attractor p W)"
  unfolding attractor_def using attractor_step_mono lfp_unfold by blast
lemma attractor_lowerbound: "attractor_step p W S \<subseteq> S \<Longrightarrow> attractor p W \<subseteq> S"
  unfolding attractor_def using attractor_step_mono by (simp add: lfp_lowerbound)
lemma attractor_set_non_empty: "W \<noteq> {} \<Longrightarrow> attractor p W \<noteq> {}"
  and attractor_set_base: "W \<subseteq> attractor p W"
  using attractor_unfolding by auto
lemma attractor_in_V: "W \<subseteq> V \<Longrightarrow> attractor p W \<subseteq> V"
  using attractor_lowerbound attractor_step_bounded_by_V by auto

subsection \<open>Attractor Set Extensions\<close>

lemma attractor_set_VVp:
  assumes "v \<in> VV p" "v\<rightarrow>w" "w \<in> attractor p W"
  shows "v \<in> attractor p W"
  apply (subst attractor_unfolding) unfolding directly_attracted_def using assms by auto

lemma attractor_set_VVpstar:
  assumes "\<not>deadend v" "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> attractor p W"
  shows "v \<in> attractor p W"
  apply (subst attractor_unfolding) unfolding directly_attracted_def using assms by auto

subsection \<open>Removing an Attractor\<close>

lemma removing_attractor_induces_no_deadends:
  assumes "v \<in> S - attractor p W" "v\<rightarrow>w" "w \<in> S" "\<And>w. \<lbrakk> v \<in> VV p**; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<in> S"
  shows "\<exists>w \<in> S - attractor p W. v\<rightarrow>w"
proof-
  have "v \<in> V" using \<open>v\<rightarrow>w\<close> by blast
  thus ?thesis proof (cases rule: VV_cases)
    assume "v \<in> VV p"
    thus ?thesis using attractor_set_VVp assms by blast
  next
    assume "v \<in> VV p**"
    thus ?thesis using attractor_set_VVpstar assms by (metis Diff_iff edges_are_in_V(2))
  qed
qed

text \<open>Removing the attractor sets of deadends leaves a subgame without deadends.\<close>

lemma subgame_without_deadends:
  assumes V'_def: "V' = V - attractor p (deadends p**) - attractor p** (deadends p****)"
    (is "V' = V - ?A - ?B")
    and v: "v \<in> V\<^bsub>subgame V'\<^esub>"
  shows "\<not>Digraph.deadend (subgame V') v"
proof (cases)
  assume "deadend v"
  have v: "v \<in> V - ?A - ?B" using v unfolding V'_def subgame_def by simp
  { fix p' assume "v \<in> VV p'**"
    hence "v \<in> attractor p' (deadends p'**)"
      using \<open>deadend v\<close> attractor_set_base[of "deadends p'**" p']
      unfolding deadends_def by blast
    hence False using v by (cases p'; cases p) auto
  }
  thus ?thesis using v by blast
next
  assume "\<not>deadend v"
  have v: "v \<in> V - ?A - ?B" using v unfolding V'_def subgame_def by simp
  define G' where "G' = subgame V'"
  interpret G': ParityGame G' unfolding G'_def using subgame_ParityGame .
  show ?thesis proof
    assume "Digraph.deadend (subgame V') v"
    hence "G'.deadend v" unfolding G'_def .
    have all_in_attractor: "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> ?A \<or> w \<in> ?B" proof (rule ccontr)
      fix w
      assume "v\<rightarrow>w" "\<not>(w \<in> ?A \<or> w \<in> ?B)"
      hence "w \<in> V'" unfolding V'_def by blast
      hence "w \<in> V\<^bsub>G'\<^esub>" unfolding G'_def subgame_def using \<open>v\<rightarrow>w\<close> by auto
      hence "v \<rightarrow>\<^bsub>G'\<^esub> w" using \<open>v\<rightarrow>w\<close> assms(2) unfolding G'_def subgame_def by auto
      thus False using \<open>G'.deadend v\<close> using \<open>w \<in> V\<^bsub>G'\<^esub>\<close> by blast
    qed
    { fix p' assume "v \<in> VV p'"
      { assume "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p' (deadends p'**)"
        hence "v \<in> attractor p' (deadends p'**)" using \<open>v \<in> VV p'\<close> attractor_set_VVp by blast
        hence False using v by (cases p'; cases p) auto
      }
      hence "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> attractor p'** (deadends p'****)"
        using all_in_attractor by (cases p'; cases p) auto
      hence "v \<in> attractor p'** (deadends p'****)"
        using \<open>\<not>deadend v\<close> \<open>v \<in> VV p'\<close> attractor_set_VVpstar by auto
      hence False using v by (cases p'; cases p) auto
    }
    thus False using v by blast
  qed
qed

subsection \<open>Attractor Set Induction\<close>

lemma mono_restriction_is_mono: "mono f \<Longrightarrow> mono (\<lambda>S. f (S \<inter> V))"
  unfolding mono_def by (meson inf_mono monoD subset_refl)

text \<open>
  Here we prove a powerful induction schema for @{term attractor}.  Being able to prove this is the
  only reason why we do not use \texttt{inductive\_set} to define the attractor set.

  See also \url{https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2015-October/msg00123.html}
\<close>
lemma attractor_set_induction [consumes 1, case_names step union]:
  assumes "W \<subseteq> V"
    and step: "\<And>S. S \<subseteq> V \<Longrightarrow> P S \<Longrightarrow> P (attractor_step p W S)"
    and union: "\<And>M. \<forall>S \<in> M. S \<subseteq> V \<and> P S \<Longrightarrow> P (\<Union>M)"
  shows "P (attractor p W)"
proof-
  let ?P = "\<lambda>S. P (S \<inter> V)"
  let ?f = "\<lambda>S. attractor_step p W (S \<inter> V)"
  let ?A = "lfp ?f"
  let ?B = "lfp (attractor_step p W)"
  have f_mono: "mono ?f"
    using mono_restriction_is_mono[of "attractor_step p W"] attractor_step_mono by simp
  have P_A: "?P ?A" proof (rule lfp_ordinal_induct_set)
    show "\<And>S. ?P S \<Longrightarrow> ?P (W \<union> (S \<inter> V) \<union> directly_attracted p (S \<inter> V))"
      by (metis assms(1) attractor_step_bounded_by_V inf.absorb1 inf_le2 local.step)
    show "\<And>M. \<forall>S \<in> M. ?P S \<Longrightarrow> ?P (\<Union>M)" proof-
      fix M
      let ?M = "{S \<inter> V | S. S \<in> M}"
      assume "\<forall>S\<in>M. ?P S"
      hence "\<forall>S \<in> ?M. S \<subseteq> V \<and> P S" by auto
      hence *: "P (\<Union>?M)" by (simp add: union)
      have "\<Union>?M = (\<Union>M) \<inter> V" by blast
      thus "?P (\<Union>M)" using * by auto
    qed
  qed (insert f_mono)

  have *: "W \<union> (V \<inter> V) \<union> directly_attracted p (V \<inter> V) \<subseteq> V"
    using \<open>W \<subseteq> V\<close> attractor_step_bounded_by_V by auto
  have "?A \<subseteq> V" "?B \<subseteq> V" using * by (simp_all add: lfp_lowerbound)

  have "?A = ?f ?A" using f_mono lfp_unfold by blast
  hence "?A = W \<union> (?A \<inter> V) \<union> directly_attracted p (?A \<inter> V)" using \<open>?A \<subseteq> V\<close> by simp
  hence *: "attractor_step p W ?A \<subseteq> ?A" using \<open>?A \<subseteq> V\<close> inf.absorb1 by fastforce

  have "?B = attractor_step p W ?B" using attractor_step_mono lfp_unfold by blast
  hence "?f ?B \<subseteq> ?B" using \<open>?B \<subseteq> V\<close> by (metis (no_types, lifting) equalityD2 le_iff_inf)

  have "?A = ?B" proof
    show "?A \<subseteq> ?B" using \<open>?f ?B \<subseteq> ?B\<close> by (simp add: lfp_lowerbound)
    show "?B \<subseteq> ?A" using * by (simp add: lfp_lowerbound)
  qed
  hence "?P ?B" using P_A by (simp add: attractor_def)
  thus ?thesis using \<open>?B \<subseteq> V\<close> by (simp add: attractor_def le_iff_inf)
qed

end \<comment> \<open>context ParityGame\<close>

end
