(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

section \<open>Syntax of $\lambda\bullet$\<close>

(*<*)
theory Syntax
  imports Nominal2_Lemmas
begin
(*>*)

typedecl hash
instantiation hash :: pure
begin
definition permute_hash :: "perm \<Rightarrow> hash \<Rightarrow> hash" where
  "permute_hash \<pi> h = h"
instance proof qed (simp_all add: permute_hash_def)
end

atom_decl var

nominal_datatype "term" =
  Unit |
  Var var |
  Lam x::var t::"term" binds x in t |
  Rec x::var t::"term" binds x in t |
  Inj1 "term" |
  Inj2 "term" |
  Pair "term" "term" |
  Let "term" x::var t::"term" binds x in t |
  App "term" "term" |
  Case "term" "term" "term" |
  Prj1 "term" |
  Prj2 "term" |
  Roll "term" |
  Unroll "term" |
  Auth "term" |
  Unauth "term" |
  Hash hash |
  Hashed hash "term"

atom_decl tvar

nominal_datatype ty =
  One |
  Fun ty ty |
  Sum ty ty |
  Prod ty ty |
  Mu \<alpha>::tvar \<tau>::ty binds \<alpha> in \<tau> |
  Alpha tvar |
  AuthT ty

lemma no_tvars_in_term[simp]: "atom (x :: tvar) \<sharp> (t :: term)"
  by (induct t rule: term.induct) auto

lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (\<tau> :: ty)"
  by (induct \<tau> rule: ty.induct) auto

inductive "value" :: "term \<Rightarrow> bool" where
  "value Unit" |
  "value (Var _)" |
  "value (Lam _ _)" |
  "value (Rec _ _)" |
  "value v \<Longrightarrow> value (Inj1 v)" |
  "value v \<Longrightarrow> value (Inj2 v)" |
  "\<lbrakk> value v\<^sub>1; value v\<^sub>2 \<rbrakk> \<Longrightarrow> value (Pair v\<^sub>1 v\<^sub>2)" |
  "value v \<Longrightarrow> value (Roll v)" |
  "value (Hash _)" |
  "value v \<Longrightarrow> value (Hashed _ v)"

declare value.intros[simp]
declare value.intros[intro]

equivariance "value"

lemma value_inv[simp]:
  "\<not> value (Let e\<^sub>1 x e\<^sub>2)"
  "\<not> value (App v v')"
  "\<not> value (Case v v\<^sub>1 v\<^sub>2)"
  "\<not> value (Prj1 v)"
  "\<not> value (Prj2 v)"
  "\<not> value (Unroll v)"
  "\<not> value (Auth v)"
  "\<not> value (Unauth v)"
  using value.cases by fastforce+

inductive_cases value_Inj1_inv[elim]: "value (Inj1 e)"
inductive_cases value_Inj2_inv[elim]: "value (Inj2 e)"
inductive_cases value_Pair_inv[elim]: "value (Pair e\<^sub>1 e\<^sub>2)"
inductive_cases value_Roll_inv[elim]: "value (Roll e)"
inductive_cases value_Hashed_inv[elim]: "value (Hashed h e)"

abbreviation closed :: "term \<Rightarrow> bool" where
  "closed t \<equiv> (\<forall>x::var. atom x \<sharp> t)"

(*<*)
end
(*>*)
