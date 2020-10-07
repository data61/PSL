(*  Author:     Stefan Berghofer, TU Muenchen, 2005
*)

theory Basis
imports Main
begin

section \<open>General Utilities\<close>

text \<open>
This section introduces some general utilities that will be useful later on in
the formalization of System \fsub{}.

The following rewrite rules are useful for simplifying mutual induction rules.
\<close>

lemma True_simps:
  "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  "(PROP P \<Longrightarrow> True) \<equiv> PROP Trueprop True"
  "(\<And>x. True) \<equiv> PROP Trueprop True"
  apply -
  apply rule
  apply (erule meta_mp)
  apply (rule TrueI)
  apply assumption
  apply rule
  apply (rule TrueI)
  apply assumption
  apply rule
  apply (rule TrueI)+
  done

text \<open>
Unfortunately, the standard introduction and elimination rules for bounded
universal and existential quantifier do not work properly for sets of pairs.
\<close>

lemma ballpI: "(\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x, y) \<in> A. P x y"
  by blast

lemma bpspec: "\<forall>(x, y) \<in> A. P x y \<Longrightarrow> (x, y) \<in> A \<Longrightarrow> P x y"
  by blast

lemma ballpE: "\<forall>(x, y) \<in> A. P x y \<Longrightarrow> (P x y \<Longrightarrow> Q) \<Longrightarrow>
  ((x, y) \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by blast

lemma bexpI: "P x y \<Longrightarrow> (x, y) \<in> A \<Longrightarrow> \<exists>(x, y) \<in> A. P x y"
  by blast

lemma bexpE: "\<exists>(x, y) \<in> A. P x y \<Longrightarrow>
  (\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by blast

lemma ball_eq_sym: "\<forall>(x, y) \<in> S. f x y = g x y \<Longrightarrow> \<forall>(x, y) \<in> S. g x y = f x y"
  by auto

lemma wf_measure_size: "wf (measure size)" by simp

notation
  Some ("\<lfloor>_\<rfloor>")

notation
  None ("\<bottom>")

notation
  length ("\<parallel>_\<parallel>")

notation
  Cons ("_ \<Colon>/ _" [66, 65] 65)

text \<open>
The following variant of the standard \<open>nth\<close> function returns
\<open>\<bottom>\<close> if the index is out of range.
\<close>

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>" [90, 0] 91)
where
  "[]\<langle>i\<rangle> = \<bottom>"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> \<lfloor>x\<rfloor> | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

lemma [simp]: "i < \<parallel>xs\<parallel> \<Longrightarrow> (xs @ ys)\<langle>i\<rangle> = xs\<langle>i\<rangle>"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
  done

lemma [simp]: "\<parallel>xs\<parallel> \<le> i \<Longrightarrow> (xs @ ys)\<langle>i\<rangle> = ys\<langle>i - \<parallel>xs\<parallel>\<rangle>"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
  done

text \<open>Association lists\<close>

primrec assoc :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" ("_\<langle>_\<rangle>\<^sub>?" [90, 0] 91)
where
  "[]\<langle>a\<rangle>\<^sub>? = \<bottom>"
| "(x # xs)\<langle>a\<rangle>\<^sub>? = (if fst x = a then \<lfloor>snd x\<rfloor> else xs\<langle>a\<rangle>\<^sub>?)"

primrec unique :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "unique [] = True"
| "unique (x # xs) = (xs\<langle>fst x\<rangle>\<^sub>? = \<bottom> \<and> unique xs)"

lemma assoc_set: "ps\<langle>x\<rangle>\<^sub>? = \<lfloor>y\<rfloor> \<Longrightarrow> (x, y) \<in> set ps"
  by (induct ps) (auto split: if_split_asm)

lemma map_assoc_None [simp]:
  "ps\<langle>x\<rangle>\<^sub>? = \<bottom> \<Longrightarrow> map (\<lambda>(x, y). (x, f x y)) ps\<langle>x\<rangle>\<^sub>? = \<bottom>"
  by (induct ps) auto

no_syntax
  "_Map" :: "maplets => 'a \<rightharpoonup> 'b"  ("(1[_])")


end
