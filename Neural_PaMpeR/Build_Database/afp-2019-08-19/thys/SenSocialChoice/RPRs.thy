(*
 * Rational Preference Relations (RPRs).
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced July 2006.
 * License: BSD
 *)

(*<*)
theory RPRs

imports FSext

begin
(*>*)

(* **************************************** *)

section\<open>Preliminaries\<close>

text\<open>

The auxiliary concepts defined here are standard \cite{Routley:79, Sen:70a,
Taylor:2005}. Throughout we make use of a fixed set @{term "A"} of
alternatives, drawn from some arbitrary type @{typ "'a"} of suitable
size. Taylor \cite{Taylor:2005} terms this set an \emph{agenda}. Similarly
we have a type @{typ "'i"} of individuals and a population @{term "Is"}.

\<close>

(* **************************************** *)

subsection\<open>Rational Preference Relations (RPRs)\<close>

text\<open>

Definitions for rational preference relations (RPRs), which represent
indifference or strict preference amongst some set of alternatives.  These
are also called \emph{weak orders} or (ambiguously) \emph{ballots}.

Unfortunately Isabelle's standard ordering operators and lemmas are
typeclass-based, and as introducing new types is painful and we need several
orders per type, we need to repeat some things.

\<close>

type_synonym 'a RPR = "('a * 'a) set"

abbreviation rpr_eq_syntax :: "'a \<Rightarrow> 'a RPR \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<^bsub>_\<^esub>\<preceq> _" [50, 1000, 51] 50) where
  "x \<^bsub>r\<^esub>\<preceq> y == (x, y) \<in> r"

definition indifferent_pref :: "'a \<Rightarrow> 'a RPR \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<^bsub>_\<^esub>\<approx> _" [50, 1000, 51] 50) where
  "x \<^bsub>r\<^esub>\<approx> y \<equiv> (x \<^bsub>r\<^esub>\<preceq> y \<and> y \<^bsub>r\<^esub>\<preceq> x)"

lemma indifferent_prefI[intro]: "\<lbrakk> x \<^bsub>r\<^esub>\<preceq> y; y \<^bsub>r\<^esub>\<preceq> x \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<approx> y"
  unfolding indifferent_pref_def by simp

lemma indifferent_prefD[dest]: "x \<^bsub>r\<^esub>\<approx> y \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<and> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding indifferent_pref_def by simp

definition strict_pref :: "'a \<Rightarrow> 'a RPR \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<^bsub>_\<^esub>\<prec> _" [50, 1000, 51] 50) where
  "x \<^bsub>r\<^esub>\<prec> y \<equiv> (x \<^bsub>r\<^esub>\<preceq> y \<and> \<not>(y \<^bsub>r\<^esub>\<preceq> x))"

lemma strict_pref_def_irrefl[simp]: "\<not> (x \<^bsub>r\<^esub>\<prec> x)" unfolding strict_pref_def by blast

lemma strict_prefI[intro]: "\<lbrakk> x \<^bsub>r\<^esub>\<preceq> y; \<not>(y \<^bsub>r\<^esub>\<preceq> x) \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> y"
  unfolding strict_pref_def by simp

text\<open>

Traditionally, @{term "x \<^bsub>r\<^esub>\<preceq> y"} would be written $x\ R\ y$,
@{term "x \<^bsub>r\<^esub>\<approx> y"} as $x\ I\ y$ and @{term "x
\<^bsub>r\<^esub>\<prec> y"} as $x\ P\ y$, where the relation $r$ is implicit, and
profiles are indexed by subscripting.

\<close>

text\<open>

\emph{Complete} means that every pair of distinct alternatives is
ranked. The "distinct" part is a matter of taste, as it makes sense to
regard an alternative as as good as itself. Here I take reflexivity
separately.

\<close>

definition complete :: "'a set \<Rightarrow> 'a RPR \<Rightarrow> bool" where
  "complete A r \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A - {x}. x \<^bsub>r\<^esub>\<preceq> y \<or> y \<^bsub>r\<^esub>\<preceq> x)"

lemma completeI[intro]:
  "(\<And>x y. \<lbrakk> x \<in> A; y \<in> A; x \<noteq> y \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<or> y \<^bsub>r\<^esub>\<preceq> x) \<Longrightarrow> complete A r"
  unfolding complete_def by auto

lemma completeD[dest]:
  "\<lbrakk> complete A r; x \<in> A; y \<in> A; x \<noteq> y \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<or> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding complete_def by auto

lemma complete_less_not: "\<lbrakk> complete A r; hasw [x,y] A; \<not> x \<^bsub>r\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding complete_def strict_pref_def by auto

lemma complete_indiff_not: "\<lbrakk> complete A r; hasw [x,y] A; \<not> x \<^bsub>r\<^esub>\<approx> y \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> y \<or> y \<^bsub>r\<^esub>\<prec> x"
  unfolding complete_def indifferent_pref_def strict_pref_def by auto

lemma complete_exh:
  assumes "complete A r"
      and "hasw [x,y] A"
  obtains (xPy) "x \<^bsub>r\<^esub>\<prec> y"
    | (yPx) "y \<^bsub>r\<^esub>\<prec> x"
    | (xIy) "x \<^bsub>r\<^esub>\<approx> y"
  using assms unfolding complete_def strict_pref_def indifferent_pref_def by auto

text\<open>

Use the standard @{term "refl"}. Also define \emph{irreflexivity}
analogously to how @{term "refl"} is defined in the standard library.

\<close>

declare refl_onI[intro] refl_onD[dest]

lemma complete_refl_on:
  "\<lbrakk> complete A r; refl_on A r; x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<or> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding complete_def by auto

definition irrefl :: "'a set \<Rightarrow> 'a RPR \<Rightarrow> bool" where
  "irrefl A r \<equiv> r \<subseteq> A \<times> A \<and> (\<forall>x \<in> A. \<not> x \<^bsub>r\<^esub>\<preceq> x)"

lemma irreflI[intro]: "\<lbrakk> r \<subseteq> A \<times> A; \<And>x. x \<in> A \<Longrightarrow> \<not> x \<^bsub>r\<^esub>\<preceq> x \<rbrakk> \<Longrightarrow> irrefl A r"
  unfolding irrefl_def by simp

lemma irreflD[dest]: "\<lbrakk> irrefl A r; (x, y) \<in> r \<rbrakk> \<Longrightarrow> hasw [x,y] A"
  unfolding irrefl_def by auto

lemma irreflD'[dest]:
  "\<lbrakk> irrefl A r; r \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x y. hasw [x,y] A \<and> (x, y) \<in> r"
  unfolding irrefl_def by auto

text\<open>Rational preference relations, also known as weak orders and (I
guess) complete pre-orders.\<close>

definition rpr :: "'a set \<Rightarrow> 'a RPR \<Rightarrow> bool" where
  "rpr A r \<equiv> complete A r \<and> refl_on A r \<and> trans r"

lemma rprI[intro]: "\<lbrakk> complete A r; refl_on A r; trans r \<rbrakk> \<Longrightarrow> rpr A r"
  unfolding rpr_def by simp

lemma rprD: "rpr A r \<Longrightarrow> complete A r \<and> refl_on A r \<and> trans r"
  unfolding rpr_def by simp

lemma rpr_in_set[dest]: "\<lbrakk> rpr A r; x \<^bsub>r\<^esub>\<preceq> y \<rbrakk> \<Longrightarrow> {x,y} \<subseteq> A"
  unfolding rpr_def refl_on_def by auto

lemma rpr_refl[dest]: "\<lbrakk> rpr A r; x \<in> A \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> x"
  unfolding rpr_def by blast

lemma rpr_less_not: "\<lbrakk> rpr A r; hasw [x,y] A; \<not> x \<^bsub>r\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding rpr_def by (auto simp add: complete_less_not)

lemma rpr_less_imp_le[simp]: "\<lbrakk> x \<^bsub>r\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y"
  unfolding strict_pref_def by simp

lemma rpr_less_imp_neq[simp]: "\<lbrakk> x \<^bsub>r\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<noteq> y"
  unfolding strict_pref_def by blast

lemma rpr_less_trans[trans]: "\<lbrakk> x \<^bsub>r\<^esub>\<prec> y; y \<^bsub>r\<^esub>\<prec> z; rpr A r \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> z"
  unfolding rpr_def strict_pref_def trans_def by blast

lemma rpr_le_trans[trans]: "\<lbrakk> x \<^bsub>r\<^esub>\<preceq> y; y \<^bsub>r\<^esub>\<preceq> z; rpr A r \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> z"
  unfolding rpr_def trans_def by blast

lemma rpr_le_less_trans[trans]: "\<lbrakk> x \<^bsub>r\<^esub>\<preceq> y; y \<^bsub>r\<^esub>\<prec> z; rpr A r \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> z"
  unfolding rpr_def strict_pref_def trans_def by blast

lemma rpr_less_le_trans[trans]: "\<lbrakk> x \<^bsub>r\<^esub>\<prec> y; y \<^bsub>r\<^esub>\<preceq> z; rpr A r \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<prec> z"
  unfolding rpr_def strict_pref_def trans_def by blast

lemma rpr_complete: "\<lbrakk> rpr A r; x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> x \<^bsub>r\<^esub>\<preceq> y \<or> y \<^bsub>r\<^esub>\<preceq> x"
  unfolding rpr_def by (blast dest: complete_refl_on)

(* **************************************** *)

subsection\<open>Profiles\<close>

text \<open>A \emph{profile} (also termed a collection of \emph{ballots}) maps
each individual to an RPR for that individual.\<close>

type_synonym ('a, 'i) Profile = "'i \<Rightarrow> 'a RPR"

definition profile :: "'a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool" where
  "profile A Is P \<equiv> Is \<noteq> {} \<and> (\<forall>i \<in> Is. rpr A (P i))"

lemma profileI[intro]: "\<lbrakk> \<And>i. i \<in> Is \<Longrightarrow> rpr A (P i); Is \<noteq> {} \<rbrakk> \<Longrightarrow> profile A Is P"
  unfolding profile_def by simp

lemma profile_rprD[dest]: "\<lbrakk> profile A Is P; i \<in> Is \<rbrakk> \<Longrightarrow> rpr A (P i)"
  unfolding profile_def by simp

lemma profile_non_empty: "profile A Is P \<Longrightarrow> Is \<noteq> {}"
  unfolding profile_def by simp

(*<*)
end
(*>*)
