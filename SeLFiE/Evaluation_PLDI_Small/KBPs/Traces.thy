(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Traces
imports Main
begin
(*>*)

section\<open>Traces\<close>

text\<open>

A \emph{trace} is a non-empty sequence of states. This custom type has
the advantage over the standard HOL list type of providing a more
suitable induction rule. We use these to give a semantics to
knowledge-based programs in \S\ref{sec:kbps-theory-kbps-semantics}.

\<close>

datatype 's Trace = tInit "'s"
                  | tStep "'s Trace" "'s" (infixl "\<leadsto>" 65)

fun tFirst :: "'s Trace \<Rightarrow> 's" where
    "tFirst (tInit s) = s"
  | "tFirst (t \<leadsto> s) = tFirst t"

fun tLast :: "'s Trace \<Rightarrow> 's" where
    "tLast (tInit s) = s"
  | "tLast (t \<leadsto> s) = s"
(*<*)

lemma tLast_tInit_comp[simp]: "tLast \<circ> tInit = id"
  by (rule ext) simp
(*>*)

text\<open>

We provide a few of the standard list operations: @{term "tLength"},
@{term "tMap"} and @{term "tZip"}. Our later ease hinges on taking the
length of a trace to be zero-based.

\<close>

fun tLength :: "'s Trace \<Rightarrow> nat" where
    "tLength (tInit s) = 0"
  | "tLength (t \<leadsto> s) = 1 + tLength t"

(*<*)
lemma tLength_0_conv:
  "(tLength t = 0) \<longleftrightarrow> (\<exists>s. t = tInit s)"
  by (cases t) simp_all

lemma tLength_g0_conv:
  "(tLength t > 0) \<longleftrightarrow> (\<exists>s t'. t = t' \<leadsto> s \<and> tLength t = Suc (tLength t'))"
  by (cases t) simp_all

lemma tLength_Suc:
  "tLength t = Suc n \<Longrightarrow> (\<exists>s t'. t = t' \<leadsto> s \<and> tLength t' = n)"
  by (cases t) simp_all

lemma trace_induct2[consumes 1, case_names tInit tStep]:
  assumes tLen: "tLength t = tLength t'"
      and tI: "\<And>s s'. P (tInit s) (tInit s')"
      and tS: "\<And>s s' t t'. \<lbrakk> tLength t = tLength t'; P t t' \<rbrakk>
               \<Longrightarrow> P (t \<leadsto> s) (t' \<leadsto> s')"
  shows "P t t'"
using tLen
proof (induct t arbitrary: t')
  case (tInit s t') with tI show ?case by (auto iff: tLength_0_conv)
next
  case (tStep t s t') with tS show ?case by (cases t') simp_all
qed
(*>*)

fun tMap where
  "tMap f (tInit x) = tInit (f x)"
| "tMap f (xs \<leadsto> x) = tMap f xs \<leadsto> f x"

(*<*)
lemma tLength_tMap[iff]: "tLength (tMap f t) = tLength t"
  by (induct t) simp_all

lemma tMap_is_tInit[iff]: "(tMap f t = tInit s) \<longleftrightarrow> (\<exists>s'. t = tInit s' \<and> f s' = s)"
  by (cases t) simp_all

lemma tInit_is_tMap[iff]: "(tInit s = tMap f t) \<longleftrightarrow> (\<exists>s'. t = tInit s' \<and> f s' = s)"
  by (cases t) auto

lemma tStep_is_tMap_conv[iff]:
 "(tp \<leadsto> s = tMap f t) \<longleftrightarrow> (\<exists>tp' s'. t = tp' \<leadsto> s' \<and> s = f s' \<and> tp = tMap f tp')"
  by (cases t) auto

lemma tMap_is_tStep_conv[iff]:
 "(tMap f t = tp \<leadsto> s) \<longleftrightarrow> (\<exists>tp' s'. t = tp' \<leadsto> s' \<and> s = f s' \<and> tMap f tp' = tp)"
  by (cases t) auto

lemma tMap_eq_imp_tLength_eq:
  assumes "tMap f t = tMap f' t'"
  shows "tLength t = tLength t'"
using assms
proof (induct t arbitrary: t')
  case (tStep tp s t')
  then obtain tp' s' where t': "t' = tp' \<leadsto> s'" by fastforce
  moreover with tStep have "tLength tp' = tLength tp" by simp
  with t' show ?case by simp
qed auto

lemma tMap_tFirst[iff]:
  "tFirst (tMap f t) = f (tFirst t)"
  by (induct t) simp_all

lemma tMap_tLast[iff]:
  "tLast (tMap f t) = f (tLast t)"
  by (induct t) simp_all

lemma tMap_tFirst_inv:
  assumes M: "tMap f t = tMap f' t'"
  shows "f (tFirst t) = f' (tFirst t')"
proof -
  from M have L: "tLength t = tLength t'" by (rule tMap_eq_imp_tLength_eq)
  from L M show ?thesis by (induct rule: trace_induct2, simp_all)
qed

lemma tMap_tLast_inv:
  assumes M: "tMap f t = tMap f' t'"
  shows "f (tLast t) = f' (tLast t')"
proof -
  from M have L: "tLength t = tLength t'" by (rule tMap_eq_imp_tLength_eq)
  from L M show ?thesis by (induct rule: trace_induct2, simp_all)
qed
(*>*)

fun tZip where
  "tZip f (tInit x) (tInit y) = tInit (f x y)"
| "tZip f (xs \<leadsto> x) (ys \<leadsto> y) = tZip f xs ys \<leadsto> f x y"
(*<*)

lemma tLength_tZip[iff]: "tLength xs = tLength ys \<Longrightarrow> tLength (tZip f xs ys) = tLength xs"
  by (induct rule: trace_induct2) simp_all

(*>*)
(*<*)
end
(*>*)
