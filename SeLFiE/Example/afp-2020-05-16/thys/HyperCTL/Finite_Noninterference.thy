section \<open>Noninterference for models with finitely many users, commands and outputs\<close>

(*<*)
theory Finite_Noninterference
imports Noninterference Deep
begin
(*>*)


text\<open>In the Noninterference section, we showed how to express Goguen-Meseguer
noninterference as a shallow HyperCTL* formula.  Here we show that, if one assumes
finiteness of the sets of users, commands and outputs,
then one can express the property as (the denotation of) a syntactic formula.
Note that we do {\em not} need to assume the state space finite -- this is
important for a potential application to infinite-state systems.\<close>


text\<open>The Goguen-Meseguer security model with finiteness assumptions\<close>

locale GM_sec_model_finite = GM_sec_model st0 do out
  for st0 :: 'St
  and do :: "'St \<Rightarrow> 'U \<Rightarrow> 'C \<Rightarrow> 'St"
  and out :: "'St \<Rightarrow> 'U \<Rightarrow> 'Out"
  +
  assumes finite_U: "finite (UNIV :: 'U set)"
  and finite_C: "finite (UNIV :: 'C set)"
  and finite_Out: "finite (UNIV :: 'Out set)"
begin

lemma finite_UminusGH: "finite (UNIV - GH)"
by (metis finite_Diff finite_U)

lemma finite_GL: "finite GL"
by (metis Diff_UNIV finite_Diff2 finite_U)

definition EqOnUC ::
"pvar \<Rightarrow> pvar \<Rightarrow> 'U \<Rightarrow> 'C \<Rightarrow> ('U,'C,'Out) aprop dfmla"
where
"EqOnUC p p' u c \<equiv> Eq (Atom (Last u c) p) (Atom (Last u c) p')"

lemma EqOnUC_eqOnUC[simp]:
assumes "env p = i" and "env p' = i'"
shows "sem (EqOnUC p p' u c) env = eqOnUC i i' u c"
using assms unfolding EqOnUC_def eqOnUC_def by simp

definition EqButGH ::
"pvar \<Rightarrow> pvar \<Rightarrow> ('U,'C,'Out) aprop dfmla"
where
"EqButGH p p' \<equiv> Scon {EqOnUC p p' u c | u c. (u,c) \<in> (UNIV - GH) \<times> UNIV}"

lemma finite_EqButGH:
"finite {EqOnUC p p' u c | u c. (u,c) \<in> (UNIV - GH) \<times> UNIV}" (is "finite ?K")
proof-
  have 1: "?K = (\<lambda> (u,c). EqOnUC p p' u c) ` ((UNIV - GH) \<times> UNIV)" by auto
  show ?thesis unfolding 1 apply(rule finite_imageI)
  by (metis finite_C finite_SigmaI finite_UminusGH)
qed

lemma EqButGH_eqButGH[simp]:
assumes "env p = i" and "env p' = i'"
shows "sem (EqButGH p p') env = eqButGH i i'"
using assms finite_EqButGH
unfolding EqButGH_def eqButGH_def sem_Scon[OF finite_EqButGH] image_def
by simp (metis (hide_lams, no_types) EqOnUC_eqOnUC)

lemma FV_EqButGH: "FV (EqButGH p p') \<subseteq> {p,p'}" (is "?L \<subseteq> ?R")
proof-
  have "?L = \<Union> {FV (EqOnUC p p' u c) | u c. (u,c) \<in> (UNIV - GH) \<times> UNIV}"
  unfolding EqButGH_def FV_Scon[OF finite_EqButGH] by auto
  also have "... \<subseteq> ?R" unfolding EqOnUC_def der_Op_defs by auto
  finally show ?thesis .
qed

definition EqOnUOut ::
"pvar \<Rightarrow> pvar \<Rightarrow> 'U \<Rightarrow> 'Out \<Rightarrow> ('U,'C,'Out) aprop dfmla"
where
"EqOnUOut p p' u ou \<equiv> Eq (Atom (Obs u ou) p) (Atom (Obs u ou) p')"

lemma EqOnUOut_eqOnUOut[simp]:
assumes "env p = i" and "env p' = i'"
shows "sem (EqOnUOut p p' u ou) env = eqOnUOut i i' u ou"
using assms unfolding EqOnUOut_def eqOnUOut_def by simp

definition EqOnGL ::
"pvar \<Rightarrow> pvar \<Rightarrow> ('U,'C,'Out) aprop dfmla"
where
"EqOnGL p p' \<equiv> Scon {EqOnUOut p p' u ou | u ou. (u,ou) \<in> GL \<times> UNIV}"

lemma finite_EqOnGL:
"finite {EqOnUOut p p' u ou | u ou. (u,ou) \<in> GL \<times> UNIV}" (is "finite ?K")
proof-
  have 1: "?K = (\<lambda> (u,ou). EqOnUOut p p' u ou) ` (GL \<times> UNIV)" by auto
  show ?thesis unfolding 1 apply(rule finite_imageI)
  by (metis finite_Out finite_SigmaI finite_GL)
qed

lemma EqOnGL_eqOnGL[simp]:
assumes "env p = i" and "env p' = i'"
shows "sem (EqOnGL p p') env = eqOnGL i i'"
using assms finite_EqOnGL
unfolding EqOnGL_def eqOnGL_def sem_Scon[OF finite_EqOnGL] image_def
by simp (metis (hide_lams, no_types) EqOnUOut_eqOnUOut)

lemma FV_EqOnGL: "FV (EqOnGL p p') \<subseteq> {p,p'}" (is "?L \<subseteq> ?R")
proof-
  have "?L = \<Union> {FV (EqOnUOut p p' u ou) | u ou. (u,ou) \<in> GL \<times> UNIV}"
  unfolding EqOnGL_def FV_Scon[OF finite_EqOnGL] by auto
  also have "... \<subseteq> ?R" unfolding EqOnUOut_def der_Op_defs by auto
  finally show ?thesis .
qed

definition "p0 = getFresh {}"
definition "p1 = getFresh {p0}"

lemma p0p1[simp]: "p0 \<noteq> p1" unfolding p1_def
by (metis Diff_cancel getFresh infinite_imp_nonempty infinite_remove insertI1)

definition nonintDfmla :: "('U,'C,'Out) aprop dfmla" where
"nonintDfmla \<equiv>
 Fall2 p0 p1 (Imp (Alw (EqButGH p0 p1)) (Alw (EqOnGL p0 p1)))"

lemma sem_nonintDfmla: "sem nonintDfmla env = nonintSfmla"
unfolding nonintDfmla_def nonintSfmla_def by simp

lemma wff_nonintDfmla[simp]: "wff nonintDfmla"
unfolding nonintDfmla_def Fall2_def Fall_def by simp

lemma closed_nonintDfmla[simp]: "FV nonintDfmla = {}"
unfolding nonintDfmla_def Fall2_def Fall_def der_Op_defs
using FV_EqButGH FV_EqOnGL by fastforce

text\<open>In the end, we obtain that the semantics of the closed (syntactic) formula
nonintDfmla expresses noninterference faithfully:\<close>

theorem semClosed_nonintDfmla: "semClosed nonintDfmla = nonint"
unfolding nonintSfmla_iff_nonint[symmetric]
apply(subst sem_nonintDfmla[symmetric]) apply(rule semClosed_Nil) by auto



(*<*)
end (* context GM_sec_model_finite  *)
(*>*)

text\<open>end-of-context GM-sec-model-finite\<close>

(*<*)
end
(*>*)
