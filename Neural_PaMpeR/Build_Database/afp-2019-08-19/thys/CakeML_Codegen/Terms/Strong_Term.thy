section \<open>Term algebra extended with wellformedness\<close>

theory Strong_Term
imports Consts
begin

class pre_strong_term = "term" +
  fixes wellformed :: "'a \<Rightarrow> bool"
  fixes all_frees :: "'a \<Rightarrow> name fset"
  assumes wellformed_const[simp]: "wellformed (const name)"
  assumes wellformed_free[simp]: "wellformed (free name)"
  assumes wellformed_app[simp]: "wellformed (app u\<^sub>1 u\<^sub>2) \<longleftrightarrow> wellformed u\<^sub>1 \<and> wellformed u\<^sub>2"
  assumes all_frees_const[simp]: "all_frees (const name) = fempty"
  assumes all_frees_free[simp]: "all_frees (free name) = {| name |}"
  assumes all_frees_app[simp]: "all_frees (app u\<^sub>1 u\<^sub>2) = all_frees u\<^sub>1 |\<union>| all_frees u\<^sub>2"
begin

abbreviation wellformed_env :: "(name, 'a) fmap \<Rightarrow> bool" where
"wellformed_env \<equiv> fmpred (\<lambda>_. wellformed)"

end

context pre_constants begin

definition shadows_consts :: "'a::pre_strong_term \<Rightarrow> bool" where
"shadows_consts t \<longleftrightarrow> \<not> fdisjnt all_consts (all_frees t)"

sublocale shadows: simple_syntactic_or shadows_consts
  by standard (auto simp: shadows_consts_def fdisjnt_alt_def)

abbreviation not_shadows_consts_env :: "(name, 'a::pre_strong_term) fmap \<Rightarrow> bool" where
"not_shadows_consts_env \<equiv> fmpred (\<lambda>_ s. \<not> shadows_consts s)"

end

declare pre_constants.shadows_consts_def[code]

class strong_term = pre_strong_term +
  assumes raw_frees_all_frees: "abs_pred (\<lambda>t. frees t |\<subseteq>| all_frees t) t"
  assumes raw_subst_wellformed: "abs_pred (\<lambda>t. wellformed t \<longrightarrow> (\<forall>env. wellformed_env env \<longrightarrow> wellformed (subst t env))) t"
begin

lemma frees_all_frees: "frees t |\<subseteq>| all_frees t"
proof (induction t rule: raw_induct)
  case (abs t)
  show ?case
    by (rule raw_frees_all_frees)
qed auto

lemma subst_wellformed: "wellformed t \<Longrightarrow> wellformed_env env \<Longrightarrow> wellformed (subst t env)"
proof (induction t arbitrary: env rule: raw_induct)
  case (abs t)
  show ?case
    by (rule raw_subst_wellformed)
qed (auto split: option.splits)

end

global_interpretation wellformed: subst_syntactic_and "wellformed :: 'a::strong_term \<Rightarrow> bool"
by standard (auto simp: subst_wellformed)

instantiation "term" :: strong_term begin

fun all_frees_term :: "term \<Rightarrow> name fset" where
"all_frees_term (Free x) = {| x |}" |
"all_frees_term (t\<^sub>1 $ t\<^sub>2) = all_frees_term t\<^sub>1 |\<union>| all_frees_term t\<^sub>2" |
"all_frees_term (\<Lambda> t) = all_frees_term t" |
"all_frees_term _ = {||}"

lemma frees_all_frees_term[simp]: "all_frees t = frees (t::term)"
by (induction t) auto

definition wellformed_term :: "term \<Rightarrow> bool" where
[simp]: "wellformed_term t \<longleftrightarrow> Term.wellformed t"

instance proof (standard, goal_cases)
  case 8

  (* FIXME move upstream *)
  have *: "abs_pred P t" if "P t" for P and t :: "term"
    unfolding abs_pred_term_def using that
    by auto

  show ?case
    apply (rule *)
    unfolding wellformed_term_def
    by (auto simp: Term.subst_wellformed)
qed (auto simp: const_term_def free_term_def app_term_def abs_pred_term_def)

end

instantiation nterm :: strong_term begin

definition wellformed_nterm :: "nterm \<Rightarrow> bool" where
[simp]: "wellformed_nterm t \<longleftrightarrow> True"

fun all_frees_nterm :: "nterm \<Rightarrow> name fset" where
"all_frees_nterm (Nvar x) = {| x |}" |
"all_frees_nterm (t\<^sub>1 $\<^sub>n t\<^sub>2) = all_frees_nterm t\<^sub>1 |\<union>| all_frees_nterm t\<^sub>2" |
"all_frees_nterm (\<Lambda>\<^sub>n x. t) = finsert x (all_frees_nterm t)" |
"all_frees_nterm (Nconst _) = {||}"

instance proof (standard, goal_cases)
  case (7 t)
  show ?case
    unfolding abs_pred_nterm_def
    by auto
qed (auto simp: const_nterm_def free_nterm_def app_nterm_def abs_pred_nterm_def)

end

lemma (in pre_constants) shadows_consts_frees:
  fixes t :: "'a::strong_term"
  shows "\<not> shadows_consts t \<Longrightarrow> fdisjnt all_consts (frees t)"
unfolding fdisjnt_alt_def shadows_consts_def
using frees_all_frees
  by auto

abbreviation wellformed_clauses :: "_ \<Rightarrow> bool" where
"wellformed_clauses cs \<equiv> list_all (\<lambda>(pat, t). linear pat \<and> wellformed t) cs \<and> distinct (map fst cs) \<and> cs \<noteq> []"

end