(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>First-Order Terms\<close>

theory Term
  imports Main
begin

datatype (funs_term : 'f, vars_term : 'v) "term" =
  is_Var: Var (the_Var: 'v) |
  Fun 'f (args : "('f, 'v) term list")
where
  "args (Var _) = []"

abbreviation "is_Fun t \<equiv> \<not> is_Var t"

lemma is_VarE [elim]:
  "is_Var t \<Longrightarrow> (\<And>x. t = Var x \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) auto

lemma is_FunE [elim]:
  "is_Fun t \<Longrightarrow> (\<And>f ts. t = Fun f ts \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) auto

text \<open>Reorient equations of the form @{term "Var x = t"} and @{term "Fun f ss = t"} to facilitate
  simplification.\<close>
setup \<open>
  Reorient_Proc.add
    (fn Const (@{const_name Var}, _) $ _ => true | _ => false)
  #> Reorient_Proc.add
    (fn Const (@{const_name Fun}, _) $ _ $ _ => true | _ => false)
\<close>

simproc_setup reorient_Var ("Var x = t") = Reorient_Proc.proc
simproc_setup reorient_Fun ("Fun f ss = t") = Reorient_Proc.proc

text \<open>The \emph{root symbol} of a term is defined by:\<close>
fun root :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) option"
where
  "root (Var x) = None" |
  "root (Fun f ts) = Some (f, length ts)"

lemma finite_vars_term [simp]:
  "finite (vars_term t)"
  by (induct t) simp_all

lemma finite_Union_vars_term:
  "finite (\<Union>t \<in> set ts. vars_term t)"
  by auto

text \<open>A substitution is a mapping \<open>\<sigma>\<close> from variables to terms. We call a substitution that
  alters the type of variables a generalized substitution, since it does not have all properties
  that are expected of (standard) substitutions (e.g., there is no empty substitution).\<close>
type_synonym ('f, 'v, 'w) gsubst = "'v \<Rightarrow> ('f, 'w) term"
type_synonym ('f, 'v) subst  = "('f, 'v, 'v) gsubst"

fun subst_apply_term :: "('f, 'v) term \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term" (infixl "\<cdot>" 67)
  where
    "Var x \<cdot> \<sigma> = \<sigma> x"
  | "Fun f ss \<cdot> \<sigma> = Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ss)"

definition
  subst_compose :: "('f, 'u, 'v) gsubst \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'u, 'w) gsubst"
  (infixl "\<circ>\<^sub>s" 75)
  where
    "\<sigma> \<circ>\<^sub>s \<tau> = (\<lambda>x. (\<sigma> x) \<cdot> \<tau>)"

lemma subst_subst_compose [simp]:
  "t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>) = t \<cdot> \<sigma> \<cdot> \<tau>"
  by (induct t \<sigma> rule: subst_apply_term.induct) (simp_all add: subst_compose_def)

lemma subst_compose_assoc:
  "\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu> = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)"
proof (rule ext)
  fix x show "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = (\<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)) x"
  proof -
    have "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = \<sigma>(x) \<cdot> \<tau> \<cdot> \<mu>" by (simp add: subst_compose_def)
    also have "\<dots> = \<sigma>(x) \<cdot> (\<tau> \<circ>\<^sub>s \<mu>)" by simp
    finally show ?thesis by (simp add: subst_compose_def)
  qed
qed

lemma subst_apply_term_empty [simp]:
  "t \<cdot> Var = t"
proof (induct t)
  case (Fun f ts)
  from map_ext [rule_format, of ts _ id, OF Fun] show ?case by simp
qed simp

interpretation subst_monoid_mult: monoid_mult "Var" "(\<circ>\<^sub>s)"
  by (unfold_locales) (simp add: subst_compose_assoc, simp_all add: subst_compose_def)

lemma term_subst_eq:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "t \<cdot> \<sigma> = t \<cdot> \<tau>"
  using assms by (induct t) (auto)

lemma term_subst_eq_rev:
  "t \<cdot> \<sigma> = t \<cdot> \<tau> \<Longrightarrow> \<forall>x \<in> vars_term t. \<sigma> x = \<tau> x"
  by (induct t) simp_all

lemma term_subst_eq_conv:
  "t \<cdot> \<sigma> = t \<cdot> \<tau> \<longleftrightarrow> (\<forall>x \<in> vars_term t. \<sigma> x = \<tau> x)"
  using term_subst_eq [of t \<sigma> \<tau>] and term_subst_eq_rev [of t \<sigma> \<tau>] by auto

lemma subst_term_eqI:
  assumes "(\<And>t. t \<cdot> \<sigma> = t \<cdot> \<tau>)"
  shows "\<sigma> = \<tau>"
  using assms [of "Var x" for x] by (intro ext) simp

definition subst_domain :: "('f, 'v) subst \<Rightarrow> 'v set"
  where
    "subst_domain \<sigma> = {x. \<sigma> x \<noteq> Var x}"

fun subst_range :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set"
  where
    "subst_range \<sigma> = \<sigma> ` subst_domain \<sigma>"

text \<open>The variables introduced by a substitution.\<close>
definition range_vars :: "('f, 'v) subst \<Rightarrow> 'v set"
where
  "range_vars \<sigma> = \<Union>(vars_term ` subst_range \<sigma>)"

definition is_renaming :: "('f, 'v) subst \<Rightarrow> bool"
  where
    "is_renaming \<sigma> \<longleftrightarrow> (\<forall>x. is_Var (\<sigma> x)) \<and> inj_on \<sigma> (subst_domain \<sigma>)"

lemma vars_term_subst:
  "vars_term (t \<cdot> \<sigma>) = \<Union>(vars_term ` \<sigma> ` vars_term t)"
  by (induct t) simp_all

lemma range_varsE [elim]:
  assumes "x \<in> range_vars \<sigma>"
    and "\<And>t. x \<in> vars_term t \<Longrightarrow> t \<in> subst_range \<sigma> \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: range_vars_def)

lemma range_vars_subst_compose_subset:
  "range_vars (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> (range_vars \<sigma> - subst_domain \<tau>) \<union> range_vars \<tau>" (is "?L \<subseteq> ?R")
proof
  fix x
  assume "x \<in> ?L"
  then obtain y where "y \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<tau>)"
    and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)" by (auto simp: range_vars_def)
  then show "x \<in> ?R"
  proof (cases)
    assume "y \<in> subst_domain \<sigma>" and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)"
    moreover then obtain v where "v \<in> vars_term (\<sigma> y)"
      and "x \<in> vars_term (\<tau> v)" by (auto simp: subst_compose_def vars_term_subst)
    ultimately show ?thesis
      by (cases "v \<in> subst_domain \<tau>") (auto simp: range_vars_def subst_domain_def)
  qed (auto simp: range_vars_def subst_compose_def subst_domain_def)
qed

definition "subst x t = Var (x := t)"

lemma subst_simps [simp]:
  "subst x t x = t"
  "subst x (Var x) = Var"
  by (auto simp: subst_def)

lemma subst_subst_domain [simp]:
  "subst_domain (subst x t) = (if t = Var x then {} else {x})"
proof -
  { fix y
    have "y \<in> {y. subst x t y \<noteq> Var y} \<longleftrightarrow> y \<in> (if t = Var x then {} else {x})"
      by (cases "x = y", auto simp: subst_def) }
  then show ?thesis by (simp add: subst_domain_def)
qed

lemma subst_subst_range [simp]:
  "subst_range (subst x t) = (if t = Var x then {} else {t})"
  by (cases "t = Var x") (auto simp: subst_domain_def subst_def)

lemma subst_apply_left_idemp [simp]:
  assumes "\<sigma> x = t \<cdot> \<sigma>"
  shows "s \<cdot> subst x t \<cdot> \<sigma> = s \<cdot> \<sigma>"
  using assms by (induct s) (auto simp: subst_def)

lemma subst_compose_left_idemp [simp]:
  assumes "\<sigma> x = t \<cdot> \<sigma>"
  shows "subst x t \<circ>\<^sub>s \<sigma> = \<sigma>"
  by (rule subst_term_eqI) (simp add: assms)

lemma subst_ident [simp]:
  assumes "x \<notin> vars_term t"
  shows "t \<cdot> subst x u = t"
proof -
  have "t \<cdot> subst x u = t \<cdot> Var"
    by (rule term_subst_eq) (auto simp: assms subst_def)
  then show ?thesis by simp
qed

lemma subst_self_idemp [simp]:
  "x \<notin> vars_term t \<Longrightarrow> subst x t \<circ>\<^sub>s subst x t = subst x t"
  by (metis subst_simps(1) subst_compose_left_idemp subst_ident)

type_synonym ('f, 'v) terms = "('f, 'v) term set"

text \<open>Applying a substitution to every term of a given set.\<close>
abbreviation
  subst_apply_set :: "('f, 'v) terms \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) terms" (infixl "\<cdot>\<^sub>s\<^sub>e\<^sub>t" 60)
  where
    "T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<equiv> (\<lambda>t. t \<cdot> \<sigma>) ` T"

text \<open>Composition of substitutions\<close>
lemma subst_compose: "(\<sigma> \<circ>\<^sub>s \<tau>) x = \<sigma> x \<cdot> \<tau>" by (auto simp: subst_compose_def)

lemmas subst_subst = subst_subst_compose [symmetric]

lemma subst_domain_Var [simp]:
  "subst_domain Var = {}"
  by (simp add: subst_domain_def)

lemma subst_apply_eq_Var:
  assumes "s \<cdot> \<sigma> = Var x"
  obtains y where "s = Var y" and "\<sigma> y = Var x"
  using assms by (induct s) auto

lemma subst_domain_subst_compose:
  "subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) =
    (subst_domain \<sigma> - {x. \<exists>y. \<sigma> x = Var y \<and> \<tau> y = Var x}) \<union>
    (subst_domain \<tau> - subst_domain \<sigma>)"
  by (auto simp: subst_domain_def subst_compose_def elim: subst_apply_eq_Var)


text \<open>A substitution is idempotent iff the variables in its range are disjoint from its domain.
  (See also "Term Rewriting and All That" \cite[Lemma 4.5.7]{AllThat}.)\<close>
lemma subst_idemp_iff:
  "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma> \<longleftrightarrow> subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
proof
  assume "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
  then have "\<And>x. \<sigma> x \<cdot> \<sigma> = \<sigma> x \<cdot> Var" by simp (metis subst_compose_def)
  then have *: "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
    unfolding term_subst_eq_conv by simp
  { fix x y
    assume "\<sigma> x \<noteq> Var x" and "x \<in> vars_term (\<sigma> y)"
    with * [of y] have False by simp }
  then show "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
    by (auto simp: subst_domain_def range_vars_def)
next
  assume "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
  then have *: "\<And>x y. \<sigma> x = Var x \<or> \<sigma> y = Var y \<or> x \<notin> vars_term (\<sigma> y)"
    by (auto simp: subst_domain_def range_vars_def)
  have "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
  proof
    fix x y
    assume "y \<in> vars_term (\<sigma> x)"
    with * [of y x] show "\<sigma> y = Var y" by auto
  qed
  then show "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
    by (simp add: subst_compose_def term_subst_eq_conv [symmetric])
qed

fun num_funs :: "('f, 'v) term \<Rightarrow> nat"
  where
    "num_funs (Var x) = 0" |
    "num_funs (Fun f ts) = Suc (sum_list (map num_funs ts))"

lemma num_funs_0:
  assumes "num_funs t = 0"
  obtains x where "t = Var x"
  using assms by (induct t) auto

lemma num_funs_subst:
  "num_funs (t \<cdot> \<sigma>) \<ge> num_funs t"
  by (induct t) (simp_all, metis comp_apply sum_list_mono)

lemma sum_list_map_num_funs_subst:
  assumes "sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) = sum_list (map num_funs ts)"
  shows "\<forall>i < length ts. num_funs (ts ! i \<cdot> \<sigma>) = num_funs (ts ! i)"
  using assms
proof (induct ts)
  case (Cons t ts)
  then have "num_funs (t \<cdot> \<sigma>) + sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)
    = num_funs t + sum_list (map num_funs ts)" by (simp add: o_def)
  moreover have "num_funs (t \<cdot> \<sigma>) \<ge> num_funs t" by (metis num_funs_subst)
  moreover have "sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) \<ge> sum_list (map num_funs ts)"
    using num_funs_subst [of _ \<sigma>] by (induct ts) (auto intro: add_mono)
  ultimately show ?case using Cons by (auto) (case_tac i, auto)
qed simp

lemma is_Fun_num_funs_less:
  assumes "x \<in> vars_term t" and "is_Fun t"
  shows "num_funs (\<sigma> x) < num_funs (t \<cdot> \<sigma>)"
  using assms
proof (induct t)
  case (Fun f ts)
  then obtain u where u: "u \<in> set ts" "x \<in> vars_term u" by auto
  then have "num_funs (u \<cdot> \<sigma>) \<le> sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)"
    by (intro member_le_sum_list) simp
  moreover have "num_funs (\<sigma> x) \<le> num_funs (u \<cdot> \<sigma>)"
    using Fun.hyps [OF u] and u  by (cases u; simp)
  ultimately show ?case by simp
qed simp

lemma finite_subst_domain_subst:
  "finite (subst_domain (subst x y))"
  by simp

lemma subst_domain_compose:
  "subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> subst_domain \<sigma> \<union> subst_domain \<tau>"
  by (auto simp: subst_domain_def subst_compose_def)

lemma vars_term_disjoint_imp_unifier:
  fixes \<sigma> :: "('f, 'v, 'w) gsubst"
  assumes "vars_term s \<inter> vars_term t = {}"
    and "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu> :: ('f, 'v, 'w) gsubst. s \<cdot> \<mu> = t \<cdot> \<mu>"
proof -
  let ?\<mu> = "\<lambda>x. if x \<in> vars_term s then \<sigma> x else \<tau> x"
  have "s \<cdot> \<sigma> = s \<cdot> ?\<mu>"
    unfolding term_subst_eq_conv
    by (induct s) (simp_all)
  moreover have "t \<cdot> \<tau> = t \<cdot> ?\<mu>"
    using assms(1)
    unfolding term_subst_eq_conv
    by (induct s arbitrary: t) (auto)
  ultimately have "s \<cdot> ?\<mu> = t \<cdot> ?\<mu>" using assms(2) by simp
  then show ?thesis by blast
qed

lemma vars_term_subset_subst_eq:
  assumes "vars_term t \<subseteq> vars_term s"
    and "s \<cdot> \<sigma> = s \<cdot> \<tau>"
  shows "t \<cdot> \<sigma> = t \<cdot> \<tau>"
  using assms by (induct t) (induct s, auto)

end
