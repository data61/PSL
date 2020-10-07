(*  Title:      SmallStep.thy
    Author:     Peter Gammie
*)

section \<open>A small-step (reduction) operational semantics for PCF\<close>
(*<*)

theory SmallStep
imports
  OpSem
begin

(*>*)
text\<open>

A small-step semantics allows us to express more things, like the
progress of well-typed programs.

FIXME adjust: This relation is non-deterministic, but only \<open>\<beta>\<close>-reduces terms where the argument is a value. Moreover if we
start with a closed term then our values are also closed. So while in
general (i.e., for open terms) our substitution operation is wrong and
this relation is too big, we show that things work out if we start
reducing from a closed term (i.e., a program).

FIXME following Tolmach @{url
"https://www.cis.upenn.edu/~bcpierce/sf/current/Norm.html"} we make
this relation deterministic. Eases the normalization proof.

\<close>

inductive
  reduction :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>v _" [50, 50] 50)
where
  betaN: "DBApp (DBAbsN u) v \<rightarrow>\<^sub>v u<v/0>"
| betaV: "val v \<Longrightarrow> DBApp (DBAbsV u) v \<rightarrow>\<^sub>v u<v/0>"
| "f \<rightarrow>\<^sub>v f' \<Longrightarrow> DBApp f x \<rightarrow>\<^sub>v DBApp f' x"
| "\<lbrakk>f = DBAbsV u; x \<rightarrow>\<^sub>v x'\<rbrakk> \<Longrightarrow> DBApp f x \<rightarrow>\<^sub>v DBApp f x'"
| "DBFix f \<rightarrow>\<^sub>v f<DBFix f/0>"
| "DBCond DBtt t e \<rightarrow>\<^sub>v t"
| "DBCond DBff t e \<rightarrow>\<^sub>v e"
| "DBSucc (DBNum n) \<rightarrow>\<^sub>v DBNum (Suc n)"
| "DBPred (DBNum (Suc n)) \<rightarrow>\<^sub>v DBNum n"
| "DBIsZero (DBNum 0) \<rightarrow>\<^sub>v DBtt"
| "0 < n \<Longrightarrow> DBIsZero (DBNum n) \<rightarrow>\<^sub>v DBff"

abbreviation \<comment> \<open>The transitive, reflexive closure of the reduction relation.\<close>
  reduction_trc :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>v\<^sup>* _" [100, 100] 100)
where
  "reduction_trc \<equiv> rtranclp reduction"

declare reduction.intros[intro!]

inductive_cases reduction_inv:
  "DBVar v \<rightarrow>\<^sub>v t'"
  "DBApp f x \<rightarrow>\<^sub>v t'"
  "DBAbsN u \<rightarrow>\<^sub>v t'"
  "DBAbsV u \<rightarrow>\<^sub>v t'"
  "DBFix f \<rightarrow>\<^sub>v t'"
  "DBCond i t e \<rightarrow>\<^sub>v t'"
  "DBff \<rightarrow>\<^sub>v t'"
  "DBtt \<rightarrow>\<^sub>v t'"
  "DBNum n \<rightarrow>\<^sub>v t'"
  "DBSucc n \<rightarrow>\<^sub>v t'"
  "DBPred n \<rightarrow>\<^sub>v t'"
  "DBIsZero n \<rightarrow>\<^sub>v t'"

lemma reduction_val:
  assumes "val v"
  assumes "v \<rightarrow>\<^sub>v v'"
  shows False
using assms by (auto elim: val.cases reduction_inv)

lemma reduction_deterministic:
  assumes "t \<rightarrow>\<^sub>v t'"
  assumes "t \<rightarrow>\<^sub>v t''"
  shows "t'' = t'"
using assms by (induct arbitrary: t'') (blast dest: reduction_val elim: reduction_inv)+


subsubsection\<open> Reduction is consistent with evaluation \<close>

lemma reduction_eval:
  assumes "t \<rightarrow>\<^sub>v t'"
  assumes "t' \<Down> v"
  shows "t \<Down> v"
using assms by (induct arbitrary: v) (auto elim!: evalOP_inv val.cases intro: eval_val)

lemma reduction_trc_eval:
  assumes "t \<rightarrow>\<^sub>v\<^sup>* t'"
  assumes "t' \<Down> v"
  shows "t \<Down> v"
using assms by induct (auto simp: reduction_eval)

theorem reduction_trc_val_eval:
  assumes "t \<rightarrow>\<^sub>v\<^sup>* v"
  assumes "val v"
  shows "t \<Down> v"
using assms by (induct rule: converse_rtranclp_induct) (auto intro: eval_val reduction_trc_eval)

text\<open>

We show the converse (of sorts) using the frame stack machinery of the
next section.

\<close>

(*<*)

end
(*>*)
