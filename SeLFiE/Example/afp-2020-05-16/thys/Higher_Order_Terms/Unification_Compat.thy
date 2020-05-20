chapter \<open>Instantiation for \<open>HOL-ex.Unification\<close> from session \<open>HOL-ex\<close>\<close>

theory Unification_Compat
imports
  "HOL-ex.Unification"
  Term_Class
begin

text \<open>
  The Isabelle library provides a unification algorithm on lambda-free terms. To illustrate
  flexibility of the term algebra, I instantiate my class with that term type. The major issue is
  that those terms are parameterized over the constant and variable type, which cannot easily be
  supported by the classy approach, where those types are fixed to @{typ name}. As a workaround, I
  introduce a class that requires the constant and variable type to be isomorphic to @{typ name}.
\<close>

hide_const (open) Unification.subst

class is_name =
  fixes of_name :: "name \<Rightarrow> 'a"
  assumes bij: "bij of_name"
begin

definition to_name :: "'a \<Rightarrow> name" where
"to_name = inv of_name"

lemma to_of_name[simp]: "to_name (of_name a) = a"
unfolding to_name_def using bij by (metis bij_inv_eq_iff)

lemma of_to_name[simp]: "of_name (to_name a) = a"
unfolding to_name_def using bij by (meson bij_inv_eq_iff)

lemma of_name_inj: "of_name name\<^sub>1 = of_name name\<^sub>2 \<Longrightarrow> name\<^sub>1 = name\<^sub>2"
using bij by (metis to_of_name)

end

instantiation name :: is_name begin

definition of_name_name :: "name \<Rightarrow> name" where
[code_unfold]: "of_name_name x = x"

instance by standard (auto simp: of_name_name_def bij_betw_def inj_on_def)

end

lemma [simp, code_unfold]: "(to_name :: name \<Rightarrow> name) = id"
unfolding to_name_def of_name_name_def by auto

instantiation trm :: (is_name) "pre_term" begin

definition app_trm where
"app_trm = Comb"

definition unapp_trm where
"unapp_trm t = (case t of Comb t u \<Rightarrow> Some (t, u) | _ \<Rightarrow> None)"

definition const_trm where
"const_trm n = trm.Const (of_name n)"

definition unconst_trm where
"unconst_trm t = (case t of trm.Const a \<Rightarrow> Some (to_name a) | _ \<Rightarrow> None)"

definition free_trm where
"free_trm n = Var (of_name n)"

definition unfree_trm where
"unfree_trm t = (case t of Var a \<Rightarrow> Some (to_name a) | _ \<Rightarrow> None)"

primrec consts_trm :: "'a trm \<Rightarrow> name fset" where
"consts_trm (Var _) = {||}" |
"consts_trm (trm.Const c) = {| to_name c |}" |
"consts_trm (M \<cdot> N) = consts_trm M |\<union>| consts_trm N"

context
  includes fset.lifting
begin

lift_definition frees_trm :: "'a trm \<Rightarrow> name fset" is "\<lambda>t. to_name ` vars_of t"
  by auto

end

lemma frees_trm[code, simp]:
  "frees (Var v) = {| to_name v |}"
  "frees (trm.Const c) = {||}"
  "frees (M \<cdot> N) = frees M |\<union>| frees N"
including fset.lifting
by (transfer; auto)+

primrec subst_trm :: "'a trm \<Rightarrow> (name, 'a trm) fmap \<Rightarrow> 'a trm" where
"subst_trm (Var v) env = (case fmlookup env (to_name v) of Some v' \<Rightarrow> v' | _ \<Rightarrow> Var v)" |
"subst_trm (trm.Const c) _ = trm.Const c" |
"subst_trm (M \<cdot> N) env = subst_trm M env \<cdot> subst_trm N env"

instance
by standard
   (auto
      simp: app_trm_def unapp_trm_def const_trm_def unconst_trm_def free_trm_def unfree_trm_def of_name_inj
      split: trm.splits option.splits)

end

instantiation trm :: (is_name) "term" begin

definition abs_pred_trm :: "('a trm \<Rightarrow> bool) \<Rightarrow> 'a trm \<Rightarrow> bool" where
"abs_pred_trm P t \<longleftrightarrow> True"

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    proof (induction t)
      case Var
      then show ?case
        unfolding free_trm_def
        by (metis of_to_name)
    next
      case Const
      then show ?case
        unfolding const_trm_def
        by (metis of_to_name)
    qed (auto simp: app_trm_def)
qed (auto simp: abs_pred_trm_def)

end

lemma assoc_alt_def[simp]:
  "assoc x y t = (case map_of t x of Some y' \<Rightarrow> y' | _ \<Rightarrow> y)"
by (induction t) auto

lemma subst_eq: "Unification.subst t s = subst t (fmap_of_list s)"
by (induction t) (auto split: option.splits simp: fmlookup_of_list)

end
