(*  Title:       An Encoding of Lambdas in Lambda-Free Higher-Order Logic
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2019
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>An Encoding of Lambdas in Lambda-Free Higher-Order Logic\<close>

theory Lambda_Encoding
imports Lambda_Free_Term
begin

text \<open>
This theory defines an encoding of \<open>\<lambda>\<close>-expressions as \<open>\<lambda>\<close>-free higher-order terms.
\<close>

locale lambda_encoding =
  fixes
    lam :: 's and
    db :: "nat \<Rightarrow> 's"
begin

definition is_db :: "'s \<Rightarrow> bool" where
  "is_db f \<longleftrightarrow> (\<exists>i. f = db i)"

fun subst_db :: "nat \<Rightarrow> 'v \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm" where
  "subst_db i x (Hd \<zeta>) = Hd (if \<zeta> = Var x then Sym (db i) else \<zeta>)"
| "subst_db i x (App s t) =
   App (subst_db i x s) (subst_db (if head s = Sym lam then i + 1 else i) x t)"

definition raw_db_subst :: "nat \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('s, 'v) tm" where
  "raw_db_subst i x = (\<lambda>y. Hd (if y = x then Sym (db i) else Var y))"

lemma vars_mset_subst_db: "vars_mset (subst_db i x s) = {#y \<in># vars_mset s. y \<noteq> x#}"
  by (induct s arbitrary: i) (auto elim: hd.set_cases)

lemma head_subst_db: "head (subst_db i x s) = head (subst (raw_db_subst i x) s)"
  by (induct s arbitrary: i) (auto simp: raw_db_subst_def split: hd.split)

lemma args_subst_db:
  "args (subst_db i x s) = map (subst_db (if head s = Sym lam then i + 1 else i) x) (args s)"
  by (induct s arbitrary: i) auto

lemma var_mset_subst_db_subseteq:
  "vars_mset s \<subseteq># vars_mset t \<Longrightarrow> vars_mset (subst_db i x s) \<subseteq># vars_mset (subst_db i x t)"
  by (simp add: vars_mset_subst_db multiset_filter_mono)

end

end
