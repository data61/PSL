(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Syntactic Fragments and Stability\<close>

theory Syntactic_Fragments_and_Stability
imports
  LTL.LTL "HOL-Library.Sublist"
begin

\<comment> \<open>We use prefix and suffix on infinite words.\<close>
hide_const Sublist.prefix Sublist.suffix

subsection \<open>The fragments @{term \<mu>LTL} and @{term \<nu>LTL}\<close>

fun is_\<mu>LTL :: "'a ltln \<Rightarrow> bool"
where
  "is_\<mu>LTL true\<^sub>n = True"
| "is_\<mu>LTL false\<^sub>n = True"
| "is_\<mu>LTL prop\<^sub>n(_) = True"
| "is_\<mu>LTL nprop\<^sub>n(_) = True"
| "is_\<mu>LTL (\<phi> and\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (\<phi> or\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (X\<^sub>n \<phi>) = is_\<mu>LTL \<phi>"
| "is_\<mu>LTL (\<phi> U\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (\<phi> M\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL _ = False"

fun is_\<nu>LTL :: "'a ltln \<Rightarrow> bool"
where
  "is_\<nu>LTL true\<^sub>n = True"
| "is_\<nu>LTL false\<^sub>n = True"
| "is_\<nu>LTL prop\<^sub>n(_) = True"
| "is_\<nu>LTL nprop\<^sub>n(_) = True"
| "is_\<nu>LTL (\<phi> and\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (\<phi> or\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (X\<^sub>n \<phi>) = is_\<nu>LTL \<phi>"
| "is_\<nu>LTL (\<phi> W\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (\<phi> R\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL _ = False"

definition \<mu>LTL :: "'a ltln set" where
  "\<mu>LTL = {\<phi>. is_\<mu>LTL \<phi>}"

definition \<nu>LTL :: "'a ltln set" where
  "\<nu>LTL = {\<phi>. is_\<nu>LTL \<phi>}"

lemma \<mu>LTL_simp[simp]:
  "\<phi> \<in> \<mu>LTL \<longleftrightarrow> is_\<mu>LTL \<phi>"
  unfolding \<mu>LTL_def by simp

lemma \<nu>LTL_simp[simp]:
  "\<phi> \<in> \<nu>LTL \<longleftrightarrow> is_\<nu>LTL \<phi>"
  unfolding \<nu>LTL_def by simp



subsubsection \<open>Subformulas in @{term \<mu>LTL} and @{term \<nu>LTL}\<close>

fun subformulas\<^sub>\<mu> :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subformulas\<^sub>\<mu> (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (X\<^sub>n \<phi>) = subformulas\<^sub>\<mu> \<phi>"
| "subformulas\<^sub>\<mu> (\<phi> U\<^sub>n \<psi>) = {\<phi> U\<^sub>n \<psi>} \<union> subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> R\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> W\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> M\<^sub>n \<psi>) = {\<phi> M\<^sub>n \<psi>} \<union> subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> _ = {}"

fun subformulas\<^sub>\<nu> :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subformulas\<^sub>\<nu> (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (X\<^sub>n \<phi>) = subformulas\<^sub>\<nu> \<phi>"
| "subformulas\<^sub>\<nu> (\<phi> U\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> R\<^sub>n \<psi>) = {\<phi> R\<^sub>n \<psi>} \<union> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> W\<^sub>n \<psi>) = {\<phi> W\<^sub>n \<psi>} \<union> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> M\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> _ = {}"

lemma subformulas\<^sub>\<mu>_semantics:
  "subformulas\<^sub>\<mu> \<phi> = {\<psi> \<in> subfrmlsn \<phi>. \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi> = \<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2 \<or> \<psi> = \<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2}"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_semantics:
  "subformulas\<^sub>\<nu> \<phi> = {\<psi> \<in> subfrmlsn \<phi>. \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi> = \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<or> \<psi> = \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2}"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_subfrmlsn:
  "subformulas\<^sub>\<mu> \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_subfrmlsn:
  "subformulas\<^sub>\<nu> \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_finite:
  "finite (subformulas\<^sub>\<mu> \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_finite:
  "finite (subformulas\<^sub>\<nu> \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subformulas\<^sub>\<mu> \<psi> \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subformulas\<^sub>\<nu> \<psi> \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsn_\<mu>LTL:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> subfrmlsn \<phi> \<subseteq> \<mu>LTL"
  by (induction \<phi>) auto

lemma subfrmlsn_\<nu>LTL:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> subfrmlsn \<phi> \<subseteq> \<nu>LTL"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>\<^sub>\<nu>_disjoint:
  "subformulas\<^sub>\<mu> \<phi> \<inter> subformulas\<^sub>\<nu> \<phi> = {}"
  unfolding subformulas\<^sub>\<mu>_semantics subformulas\<^sub>\<nu>_semantics
  by fastforce

lemma subformulas\<^sub>\<mu>\<^sub>\<nu>_subfrmlsn:
  "subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<nu> \<phi> \<subseteq> subfrmlsn \<phi>"
  using subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<nu>_subfrmlsn by blast

lemma subformulas\<^sub>\<mu>\<^sub>\<nu>_card:
  "card (subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<nu> \<phi>) = card (subformulas\<^sub>\<mu> \<phi>) + card (subformulas\<^sub>\<nu> \<phi>)"
  by (simp add: subformulas\<^sub>\<mu>\<^sub>\<nu>_disjoint subformulas\<^sub>\<mu>_finite subformulas\<^sub>\<nu>_finite card_Un_disjoint)


subsection \<open>Stability\<close>

definition "GF_singleton w \<phi> \<equiv> if w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>) then {\<phi>} else {}"
definition "F_singleton w \<phi> \<equiv> if w \<Turnstile>\<^sub>n F\<^sub>n \<phi> then {\<phi>} else {}"

declare GF_singleton_def [simp] F_singleton_def [simp]

fun \<G>\<F> :: "'a ltln \<Rightarrow> 'a set word \<Rightarrow> 'a ltln set"
where
  "\<G>\<F> (\<phi> and\<^sub>n \<psi>) w = \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> (\<phi> or\<^sub>n \<psi>) w = \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> (X\<^sub>n \<phi>) w = \<G>\<F> \<phi> w"
| "\<G>\<F> (\<phi> U\<^sub>n \<psi>) w = GF_singleton w (\<phi> U\<^sub>n \<psi>) \<union> \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> (\<phi> R\<^sub>n \<psi>) w = \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> (\<phi> W\<^sub>n \<psi>) w = \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> (\<phi> M\<^sub>n \<psi>) w = GF_singleton w (\<phi> M\<^sub>n \<psi>) \<union> \<G>\<F> \<phi> w \<union> \<G>\<F> \<psi> w"
| "\<G>\<F> _ _ = {}"

fun \<F> :: "'a ltln \<Rightarrow> 'a set word \<Rightarrow> 'a ltln set"
where
  "\<F> (\<phi> and\<^sub>n \<psi>) w = \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> (\<phi> or\<^sub>n \<psi>) w = \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> (X\<^sub>n \<phi>) w = \<F> \<phi> w"
| "\<F> (\<phi> U\<^sub>n \<psi>) w = F_singleton w (\<phi> U\<^sub>n \<psi>) \<union> \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> (\<phi> R\<^sub>n \<psi>) w = \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> (\<phi> W\<^sub>n \<psi>) w = \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> (\<phi> M\<^sub>n \<psi>) w = F_singleton w (\<phi> M\<^sub>n \<psi>) \<union> \<F> \<phi> w \<union> \<F> \<psi> w"
| "\<F> _ _ = {}"


lemma \<G>\<F>_semantics:
  "\<G>\<F> \<phi> w = {\<psi>. \<psi> \<in> subformulas\<^sub>\<mu> \<phi> \<and> w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)}"
  by (induction \<phi>) force+

lemma \<F>_semantics:
  "\<F> \<phi> w = {\<psi>. \<psi> \<in> subformulas\<^sub>\<mu> \<phi> \<and> w \<Turnstile>\<^sub>n F\<^sub>n \<psi>}"
  by (induction \<phi>) force+

lemma \<G>\<F>_semantics':
  "\<G>\<F> \<phi> w = subformulas\<^sub>\<mu> \<phi> \<inter> {\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)}"
  unfolding \<G>\<F>_semantics by auto

lemma \<F>_semantics':
  "\<F> \<phi> w = subformulas\<^sub>\<mu> \<phi> \<inter> {\<psi>. w \<Turnstile>\<^sub>n F\<^sub>n \<psi>}"
  unfolding \<F>_semantics by auto

lemma \<G>\<F>_\<F>_subset:
  "\<G>\<F> \<phi> w \<subseteq> \<F> \<phi> w"
  unfolding \<G>\<F>_semantics \<F>_semantics by force


lemma \<G>\<F>_finite:
  "finite (\<G>\<F> \<phi> w)"
  by (induction \<phi>) auto

lemma \<G>\<F>_subformulas\<^sub>\<mu>:
  "\<G>\<F> \<phi> w \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  unfolding \<G>\<F>_semantics by force

lemma \<G>\<F>_subfrmlsn:
  "\<G>\<F> \<phi> w \<subseteq> subfrmlsn \<phi>"
  using \<G>\<F>_subformulas\<^sub>\<mu> subformulas\<^sub>\<mu>_subfrmlsn by blast

lemma \<G>\<F>_elim:
  "\<psi> \<in> \<G>\<F> \<phi> w \<Longrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)"
  unfolding \<G>\<F>_semantics by simp

lemma \<G>\<F>_suffix(* [simp] *):
  "\<G>\<F> \<phi> (suffix i w) = \<G>\<F> \<phi> w"
proof
  show "\<G>\<F> \<phi> w \<subseteq> \<G>\<F> \<phi> (suffix i w)"
    unfolding \<G>\<F>_semantics by auto
next
  show "\<G>\<F> \<phi> (suffix i w) \<subseteq> \<G>\<F> \<phi> w"
    unfolding \<G>\<F>_semantics GF_Inf_many
  proof auto
    fix \<psi>
    assume "\<exists>\<^sub>\<infinity>j. suffix (i + j) w \<Turnstile>\<^sub>n \<psi>"
    then have "\<exists>\<^sub>\<infinity>j. suffix (j + i) w \<Turnstile>\<^sub>n \<psi>"
      by (simp add: algebra_simps)
    then show "\<exists>\<^sub>\<infinity>j. suffix j w \<Turnstile>\<^sub>n \<psi>"
      using INFM_nat_add by blast
  qed
qed

lemma \<G>\<F>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<G>\<F> \<psi> w \<subseteq> \<G>\<F> \<phi> w"
  unfolding \<G>\<F>_semantics using subformulas\<^sub>\<mu>_subset by blast


lemma \<F>_finite:
  "finite (\<F> \<phi> w)"
  by (induction \<phi>) auto

lemma \<F>_subformulas\<^sub>\<mu>:
  "\<F> \<phi> w \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  unfolding \<F>_semantics by force

lemma \<F>_subfrmlsn:
  "\<F> \<phi> w \<subseteq> subfrmlsn \<phi>"
  using \<F>_subformulas\<^sub>\<mu> subformulas\<^sub>\<mu>_subfrmlsn by blast

lemma \<F>_elim:
  "\<psi> \<in> \<F> \<phi> w \<Longrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
  unfolding \<F>_semantics by simp

lemma \<F>_suffix:
  "\<F> \<phi> (suffix i w) \<subseteq> \<F> \<phi> w"
  unfolding \<F>_semantics by auto

lemma \<F>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<F> \<psi> w \<subseteq> \<F> \<phi> w"
  unfolding \<F>_semantics using subformulas\<^sub>\<mu>_subset by blast


definition "\<mu>_stable \<phi> w \<longleftrightarrow> \<G>\<F> \<phi> w = \<F> \<phi> w"

lemma suffix_\<mu>_stable:
  "\<forall>\<^sub>\<infinity>i. \<mu>_stable \<phi> (suffix i w)"
proof -
  have "\<forall>\<psi> \<in> subformulas\<^sub>\<mu> \<phi>. \<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
    using Alm_all_GF_F by blast

  then have "\<forall>\<^sub>\<infinity>i. \<forall>\<psi> \<in> subformulas\<^sub>\<mu> \<phi>. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
    using subformulas\<^sub>\<mu>_finite eventually_ball_finite by fast

  then have "\<forall>\<^sub>\<infinity>i. {\<psi> \<in> subformulas\<^sub>\<mu> \<phi>. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} = {\<psi> \<in> subformulas\<^sub>\<mu> \<phi>. suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>}"
    by (rule MOST_mono) (blast intro: Collect_cong)

  then show ?thesis
    unfolding \<mu>_stable_def \<G>\<F>_semantics \<F>_semantics
    by (rule MOST_mono) simp
qed

lemma \<mu>_stable_subfrmlsn:
  "\<mu>_stable \<phi> w \<Longrightarrow> \<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<mu>_stable \<psi> w"
proof -
  assume a1: "\<psi> \<in> subfrmlsn \<phi>" and a2: "\<mu>_stable \<phi> w"
  have "subformulas\<^sub>\<mu> \<psi> \<subseteq> subformulas\<^sub>\<mu> \<phi>"
    using a1 by (simp add: subformulas\<^sub>\<mu>_subset)
  moreover
  have "\<G>\<F> \<phi> w = \<F> \<phi> w"
    using a2 by (meson \<mu>_stable_def)
  ultimately show ?thesis
    by (metis (no_types) Un_commute \<F>_semantics' \<G>\<F>_semantics' \<mu>_stable_def inf_left_commute inf_sup_absorb sup.orderE)
qed

lemma \<mu>_stable_suffix:
  "\<mu>_stable \<phi> w \<Longrightarrow> \<mu>_stable \<phi> (suffix i w)"
  by (metis \<F>_suffix \<G>\<F>_\<F>_subset \<G>\<F>_suffix \<mu>_stable_def subset_antisym)


definition "FG_singleton w \<phi> \<equiv> if w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) then {\<phi>} else {}"
definition "G_singleton w \<phi> \<equiv> if w \<Turnstile>\<^sub>n G\<^sub>n \<phi> then {\<phi>} else {}"

declare FG_singleton_def [simp] G_singleton_def [simp]

fun \<F>\<G> :: "'a ltln \<Rightarrow> 'a set word \<Rightarrow> 'a ltln set"
where
  "\<F>\<G> (\<phi> and\<^sub>n \<psi>) w = \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> (\<phi> or\<^sub>n \<psi>) w = \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> (X\<^sub>n \<phi>) w = \<F>\<G> \<phi> w"
| "\<F>\<G> (\<phi> U\<^sub>n \<psi>) w = \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> (\<phi> R\<^sub>n \<psi>) w = FG_singleton w (\<phi> R\<^sub>n \<psi>) \<union> \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> (\<phi> W\<^sub>n \<psi>) w = FG_singleton w (\<phi> W\<^sub>n \<psi>) \<union> \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> (\<phi> M\<^sub>n \<psi>) w = \<F>\<G> \<phi> w \<union> \<F>\<G> \<psi> w"
| "\<F>\<G> _ _ = {}"

fun \<G> :: "'a ltln \<Rightarrow> 'a set word \<Rightarrow> 'a ltln set"
where
  "\<G> (\<phi> and\<^sub>n \<psi>) w = \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> (\<phi> or\<^sub>n \<psi>) w = \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> (X\<^sub>n \<phi>) w = \<G> \<phi> w"
| "\<G> (\<phi> U\<^sub>n \<psi>) w = \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> (\<phi> R\<^sub>n \<psi>) w = G_singleton w (\<phi> R\<^sub>n \<psi>) \<union> \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> (\<phi> W\<^sub>n \<psi>) w = G_singleton w (\<phi> W\<^sub>n \<psi>) \<union> \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> (\<phi> M\<^sub>n \<psi>) w = \<G> \<phi> w \<union> \<G> \<psi> w"
| "\<G> _ _ = {}"


lemma \<F>\<G>_semantics:
  "\<F>\<G> \<phi> w = {\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)}"
  by (induction \<phi>) force+

lemma \<G>_semantics:
  "\<G> \<phi> w \<equiv> {\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. w \<Turnstile>\<^sub>n G\<^sub>n \<psi>}"
  by (induction \<phi>) force+

lemma \<F>\<G>_semantics':
  "\<F>\<G> \<phi> w = subformulas\<^sub>\<nu> \<phi> \<inter> {\<psi>. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)}"
  unfolding \<F>\<G>_semantics by auto

lemma \<G>_semantics':
  "\<G> \<phi> w = subformulas\<^sub>\<nu> \<phi> \<inter> {\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n \<psi>}"
  unfolding \<G>_semantics by auto

lemma \<G>_\<F>\<G>_subset:
  "\<G> \<phi> w \<subseteq> \<F>\<G> \<phi> w"
  unfolding \<G>_semantics \<F>\<G>_semantics by force

lemma \<F>\<G>_finite:
  "finite (\<F>\<G> \<phi> w)"
  by (induction \<phi>) auto

lemma \<F>\<G>_subformulas\<^sub>\<nu>:
  "\<F>\<G> \<phi> w \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  unfolding \<F>\<G>_semantics by force

lemma \<F>\<G>_subfrmlsn:
  "\<F>\<G> \<phi> w \<subseteq> subfrmlsn \<phi>"
  using \<F>\<G>_subformulas\<^sub>\<nu> subformulas\<^sub>\<nu>_subfrmlsn by blast

lemma \<F>\<G>_elim:
  "\<psi> \<in> \<F>\<G> \<phi> w \<Longrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)"
  unfolding \<F>\<G>_semantics by simp

lemma \<F>\<G>_suffix:
  "\<F>\<G> \<phi> (suffix i w) = \<F>\<G> \<phi> w"
proof
  show "\<F>\<G> \<phi> (suffix i w) \<subseteq> \<F>\<G> \<phi> w"
    unfolding \<F>\<G>_semantics by auto
next
  show "\<F>\<G> \<phi> w \<subseteq> \<F>\<G> \<phi> (suffix i w)"
    unfolding \<F>\<G>_semantics FG_Alm_all
  proof auto
    fix \<psi>
    assume "\<forall>\<^sub>\<infinity>j. suffix j w \<Turnstile>\<^sub>n \<psi>"
    then have "\<forall>\<^sub>\<infinity>j. suffix (j + i) w \<Turnstile>\<^sub>n \<psi>"
      using MOST_nat_add by meson
    then show "\<forall>\<^sub>\<infinity>j. suffix (i + j) w \<Turnstile>\<^sub>n \<psi>"
      by (simp add: algebra_simps)
  qed
qed

lemma \<F>\<G>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<F>\<G> \<psi> w \<subseteq> \<F>\<G> \<phi> w"
  unfolding \<F>\<G>_semantics using subformulas\<^sub>\<nu>_subset by blast


lemma \<G>_finite:
  "finite (\<G> \<phi> w)"
  by (induction \<phi>) auto

lemma \<G>_subformulas\<^sub>\<nu>:
  "\<G> \<phi> w \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  unfolding \<G>_semantics by force

lemma \<G>_subfrmlsn:
  "\<G> \<phi> w \<subseteq> subfrmlsn \<phi>"
  using \<G>_subformulas\<^sub>\<nu> subformulas\<^sub>\<nu>_subfrmlsn by blast

lemma \<G>_elim:
  "\<psi> \<in> \<G> \<phi> w \<Longrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
  unfolding \<G>_semantics by simp

lemma \<G>_suffix:
  "\<G> \<phi> w \<subseteq> \<G> \<phi> (suffix i w)"
  unfolding \<G>_semantics by auto

lemma \<G>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<G> \<psi> w \<subseteq> \<G> \<phi> w"
  unfolding \<G>_semantics using subformulas\<^sub>\<nu>_subset by blast


definition "\<nu>_stable \<phi> w \<longleftrightarrow> \<F>\<G> \<phi> w = \<G> \<phi> w"

lemma suffix_\<nu>_stable:
  "\<forall>\<^sub>\<infinity>j. \<nu>_stable \<phi> (suffix j w)"
proof -
  have "\<forall>\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. \<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using Alm_all_FG_G by blast

  then have "\<forall>\<^sub>\<infinity>i. \<forall>\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using subformulas\<^sub>\<nu>_finite eventually_ball_finite by fast

  then have "\<forall>\<^sub>\<infinity>i. {\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)} = {\<psi> \<in> subformulas\<^sub>\<nu> \<phi>. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>}"
    by (rule MOST_mono) (blast intro: Collect_cong)

  then show ?thesis
    unfolding \<nu>_stable_def \<F>\<G>_semantics \<G>_semantics
    by (rule MOST_mono) simp
qed

lemma \<nu>_stable_subfrmlsn:
  "\<nu>_stable \<phi> w \<Longrightarrow> \<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> \<nu>_stable \<psi> w"
proof -
  assume a1: "\<psi> \<in> subfrmlsn \<phi>" and a2: "\<nu>_stable \<phi> w"
  have "subformulas\<^sub>\<nu> \<psi> \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    using a1 by (simp add: subformulas\<^sub>\<nu>_subset)
  moreover
  have "\<F>\<G> \<phi> w = \<G> \<phi> w"
    using a2 by (meson \<nu>_stable_def)
  ultimately show ?thesis
    by (metis (no_types) Un_commute \<G>_semantics' \<F>\<G>_semantics' \<nu>_stable_def inf_left_commute inf_sup_absorb sup.orderE)
qed

lemma \<nu>_stable_suffix:
  "\<nu>_stable \<phi> w \<Longrightarrow> \<nu>_stable \<phi> (suffix i w)"
  by (metis \<F>\<G>_suffix \<G>_\<F>\<G>_subset \<G>_suffix \<nu>_stable_def antisym_conv)


subsection \<open>Definitions with Lists for Code Export\<close>

text \<open>The \<open>\<mu>\<close>- and \<open>\<nu>\<close>-subformulas as lists:\<close>

fun subformulas\<^sub>\<mu>_list :: "'a ltln \<Rightarrow> 'a ltln list"
where
  "subformulas\<^sub>\<mu>_list (\<phi> and\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>)"
| "subformulas\<^sub>\<mu>_list (\<phi> or\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>)"
| "subformulas\<^sub>\<mu>_list (X\<^sub>n \<phi>) = subformulas\<^sub>\<mu>_list \<phi>"
| "subformulas\<^sub>\<mu>_list (\<phi> U\<^sub>n \<psi>) = List.insert (\<phi> U\<^sub>n \<psi>) (List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>))"
| "subformulas\<^sub>\<mu>_list (\<phi> R\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>)"
| "subformulas\<^sub>\<mu>_list (\<phi> W\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>)"
| "subformulas\<^sub>\<mu>_list (\<phi> M\<^sub>n \<psi>) = List.insert (\<phi> M\<^sub>n \<psi>) (List.union (subformulas\<^sub>\<mu>_list \<phi>) (subformulas\<^sub>\<mu>_list \<psi>))"
| "subformulas\<^sub>\<mu>_list _ = []"

fun subformulas\<^sub>\<nu>_list :: "'a ltln \<Rightarrow> 'a ltln list"
where
  "subformulas\<^sub>\<nu>_list (\<phi> and\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>)"
| "subformulas\<^sub>\<nu>_list (\<phi> or\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>)"
| "subformulas\<^sub>\<nu>_list (X\<^sub>n \<phi>) = subformulas\<^sub>\<nu>_list \<phi>"
| "subformulas\<^sub>\<nu>_list (\<phi> U\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>)"
| "subformulas\<^sub>\<nu>_list (\<phi> R\<^sub>n \<psi>) = List.insert (\<phi> R\<^sub>n \<psi>) (List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>))"
| "subformulas\<^sub>\<nu>_list (\<phi> W\<^sub>n \<psi>) = List.insert (\<phi> W\<^sub>n \<psi>) (List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>))"
| "subformulas\<^sub>\<nu>_list (\<phi> M\<^sub>n \<psi>) = List.union (subformulas\<^sub>\<nu>_list \<phi>) (subformulas\<^sub>\<nu>_list \<psi>)"
| "subformulas\<^sub>\<nu>_list _ = []"

lemma subformulas\<^sub>\<mu>_list_set:
  "set (subformulas\<^sub>\<mu>_list \<phi>) = subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_list_set:
  "set (subformulas\<^sub>\<nu>_list \<phi>) = subformulas\<^sub>\<nu> \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_list_distinct:
  "distinct (subformulas\<^sub>\<mu>_list \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_list_distinct:
  "distinct (subformulas\<^sub>\<nu>_list \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_list_length:
  "length (subformulas\<^sub>\<mu>_list \<phi>) = card (subformulas\<^sub>\<mu> \<phi>)"
  by (metis subformulas\<^sub>\<mu>_list_set subformulas\<^sub>\<mu>_list_distinct distinct_card)

lemma subformulas\<^sub>\<nu>_list_length:
  "length (subformulas\<^sub>\<nu>_list \<phi>) = card (subformulas\<^sub>\<nu> \<phi>)"
  by (metis subformulas\<^sub>\<nu>_list_set subformulas\<^sub>\<nu>_list_distinct distinct_card)


text \<open>
  We define the list of advice sets as the product of all subsequences
  of the \<open>\<mu>\<close>- and \<open>\<nu>\<close>-subformulas of a formula.
\<close>

definition advice_sets :: "'a ltln \<Rightarrow> ('a ltln list \<times> 'a ltln list) list"
where
  "advice_sets \<phi> = List.product (subseqs (subformulas\<^sub>\<mu>_list \<phi>)) (subseqs (subformulas\<^sub>\<nu>_list \<phi>))"

lemma subset_subseq:
  "X \<subseteq> set ys \<longleftrightarrow> (\<exists>xs. X = set xs \<and> subseq xs ys)"
  by (metis (no_types, lifting) Pow_iff image_iff in_set_subseqs subseqs_powset)

lemma subseqs_subformulas\<^sub>\<mu>_list:
  "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<longleftrightarrow> (\<exists>xs. X = set xs \<and> xs \<in> set (subseqs (subformulas\<^sub>\<mu>_list \<phi>)))"
  by (metis subset_subseq subformulas\<^sub>\<mu>_list_set in_set_subseqs)

lemma subseqs_subformulas\<^sub>\<nu>_list:
  "Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<longleftrightarrow> (\<exists>ys. Y = set ys \<and> ys \<in> set (subseqs (subformulas\<^sub>\<nu>_list \<phi>)))"
  by (metis subset_subseq subformulas\<^sub>\<nu>_list_set in_set_subseqs)

lemma advice_sets_subformulas:
  "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<longleftrightarrow> (\<exists>xs ys. X = set xs \<and> Y = set ys \<and> (xs, ys) \<in> set (advice_sets \<phi>))"
  unfolding advice_sets_def set_product subseqs_subformulas\<^sub>\<mu>_list subseqs_subformulas\<^sub>\<nu>_list by blast

(* TODO add to HOL/List.thy *)
lemma subseqs_not_empty:
  "subseqs xs \<noteq> []"
  by (metis empty_iff list.set(1) subseqs_refl)

(* TODO add to HOL/List.thy *)
lemma product_not_empty:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> List.product xs ys \<noteq> []"
  by (induction xs) simp_all

lemma advice_sets_not_empty:
  "advice_sets \<phi> \<noteq> []"
  unfolding advice_sets_def using subseqs_not_empty product_not_empty by blast

lemma advice_sets_length:
  "length (advice_sets \<phi>) \<le> 2 ^ card (subfrmlsn \<phi>)"
  unfolding advice_sets_def length_product length_subseqs subformulas\<^sub>\<mu>_list_length subformulas\<^sub>\<nu>_list_length power_add[symmetric]
  by (metis Suc_1 card_mono lessI power_increasing_iff subformulas\<^sub>\<mu>\<^sub>\<nu>_card subformulas\<^sub>\<mu>\<^sub>\<nu>_subfrmlsn subfrmlsn_finite)

lemma advice_sets_element_length:
  "(xs, ys) \<in> set (advice_sets \<phi>) \<Longrightarrow> length xs \<le> card (subfrmlsn \<phi>)"
  "(xs, ys) \<in> set (advice_sets \<phi>) \<Longrightarrow> length ys \<le> card (subfrmlsn \<phi>)"
  unfolding advice_sets_def set_product
  by (metis SigmaD1 card_mono in_set_subseqs list_emb_length order_trans subformulas\<^sub>\<mu>_list_length subformulas\<^sub>\<mu>_subfrmlsn subfrmlsn_finite)
     (metis SigmaD2 card_mono in_set_subseqs list_emb_length order_trans subformulas\<^sub>\<nu>_list_length subformulas\<^sub>\<nu>_subfrmlsn subfrmlsn_finite)

lemma advice_sets_element_subfrmlsn:
  "(xs, ys) \<in> set (advice_sets \<phi>) \<Longrightarrow> set xs \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  "(xs, ys) \<in> set (advice_sets \<phi>) \<Longrightarrow> set ys \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  unfolding advice_sets_def set_product
  by (meson SigmaD1 subseqs_subformulas\<^sub>\<mu>_list)
     (meson SigmaD2 subseqs_subformulas\<^sub>\<nu>_list)

end
