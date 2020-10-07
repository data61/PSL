chapter \<open>Terms\<close>

theory Term_Class
imports
  Datatype_Order_Generator.Order_Generator
  Name
  Term_Utils
  Disjoint_Sets
begin

hide_type (open) "term"

section \<open>A simple term type, modelled after Pure's \<open>term\<close> type\<close>

datatype "term" =
  Const name |
  Free name |
  Abs "term" ("\<Lambda> _" [71] 71) |
  Bound nat |
  App "term" "term" (infixl "$" 70)

derive linorder "term"

section \<open>A type class describing terms\<close>

text \<open>
  The type class is split into two parts, \<^emph>\<open>pre-terms\<close> and \<^emph>\<open>terms\<close>. The only difference is that
  terms assume more axioms about substitution (see below).

  A term must provide the following generic constructors that behave like regular free constructors:

  \<^item> \<open>const :: name \<Rightarrow> \<tau>\<close>
  \<^item> \<open>free :: name \<Rightarrow> \<tau>\<close>
  \<^item> \<open>app :: \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>\<close>
\<close>

text \<open>
  Conversely, there are also three corresponding destructors that could be defined in terms of
  Hilbert's choice operator. However, I have instead opted to let instances define destructors
  directly, which is simpler for execution purposes.

  Besides the generic constructors, terms may also contain other constructors. Those are abstractly
  called \<^emph>\<open>abstractions\<close>, even though that name is not entirely accurate (bound variables may also
  fall under this).

  Additionally, there must be operations that compute the list of all free variables (\<open>frees\<close>),
  constants (\<open>consts\<close>), and substitutions (\<open>subst\<close>). Pre-terms only assume some basic properties of
  substitution on the generic constructors.

  Most importantly, substitution is not specified for environments containing terms with free
  variables. Term types are not required to implement \<open>\<alpha>\<close>-renaming to prevent capturing of
  variables.
\<close>

class pre_term = size +
  fixes
    frees :: "'a \<Rightarrow> name fset" and
    subst :: "'a \<Rightarrow> (name, 'a) fmap \<Rightarrow> 'a" and
    "consts" :: "'a \<Rightarrow> name fset"
  fixes
    app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and unapp :: "'a \<Rightarrow> ('a \<times> 'a) option"
  fixes
    const :: "name \<Rightarrow> 'a" and unconst :: "'a \<Rightarrow> name option"
  fixes
    free :: "name \<Rightarrow> 'a" and unfree :: "'a \<Rightarrow> name option"
  assumes unapp_app[simp]: "unapp (app u\<^sub>1 u\<^sub>2) = Some (u\<^sub>1, u\<^sub>2)"
  assumes app_unapp[dest]: "unapp u = Some (u\<^sub>1, u\<^sub>2) \<Longrightarrow> u = app u\<^sub>1 u\<^sub>2"
  assumes app_size[simp]: "size (app u\<^sub>1 u\<^sub>2) = size u\<^sub>1 + size u\<^sub>2 + 1"
  assumes unconst_const[simp]: "unconst (const name) = Some name"
  assumes const_unconst[dest]: "unconst u = Some name \<Longrightarrow> u = const name"
  assumes unfree_free[simp]: "unfree (free name) = Some name"
  assumes free_unfree[dest]: "unfree u = Some name \<Longrightarrow> u = free name"
  assumes app_const_distinct: "app u\<^sub>1 u\<^sub>2 \<noteq> const name"
  assumes app_free_distinct: "app u\<^sub>1 u\<^sub>2 \<noteq> free name"
  assumes free_const_distinct: "free name\<^sub>1 \<noteq> const name\<^sub>2"
  assumes frees_const[simp]: "frees (const name) = fempty"
  assumes frees_free[simp]: "frees (free name) = {| name |}"
  assumes frees_app[simp]: "frees (app u\<^sub>1 u\<^sub>2) = frees u\<^sub>1 |\<union>| frees u\<^sub>2"
  assumes consts_free[simp]: "consts (free name) = fempty"
  assumes consts_const[simp]: "consts (const name) = {| name |}"
  assumes consts_app[simp]: "consts (app u\<^sub>1 u\<^sub>2) = consts u\<^sub>1 |\<union>| consts u\<^sub>2"
  assumes subst_app[simp]: "subst (app u\<^sub>1 u\<^sub>2) env = app (subst u\<^sub>1 env) (subst u\<^sub>2 env)"
  assumes subst_const[simp]: "subst (const name) env = const name"
  assumes subst_free[simp]: "subst (free name) env = (case fmlookup env name of Some t \<Rightarrow> t | _ \<Rightarrow> free name)"
  assumes free_inject: "free name\<^sub>1 = free name\<^sub>2 \<Longrightarrow> name\<^sub>1 = name\<^sub>2"
  assumes const_inject: "const name\<^sub>1 = const name\<^sub>2 \<Longrightarrow> name\<^sub>1 = name\<^sub>2"
  assumes app_inject: "app u\<^sub>1 u\<^sub>2 = app u\<^sub>3 u\<^sub>4 \<Longrightarrow> u\<^sub>1 = u\<^sub>3 \<and> u\<^sub>2 = u\<^sub>4"

instantiation "term" :: pre_term begin

definition app_term where
"app_term t u = t $ u"

fun unapp_term where
"unapp_term (t $ u) = Some (t, u)" |
"unapp_term _ = None"

definition const_term where
"const_term = Const"

fun unconst_term where
"unconst_term (Const name) = Some name" |
"unconst_term _ = None"

definition free_term where
"free_term = Free"

fun unfree_term where
"unfree_term (Free name) = Some name" |
"unfree_term _ = None"

fun frees_term :: "term \<Rightarrow> name fset" where
"frees_term (Free x) = {| x |}" |
"frees_term (t\<^sub>1 $ t\<^sub>2) = frees_term t\<^sub>1 |\<union>| frees_term t\<^sub>2" |
"frees_term (\<Lambda> t) = frees_term t" |
"frees_term _ = {||}"

fun subst_term :: "term \<Rightarrow> (name, term) fmap \<Rightarrow> term" where
"subst_term (Free s) env = (case fmlookup env s of Some t \<Rightarrow> t | None \<Rightarrow> Free s)" |
"subst_term (t\<^sub>1 $ t\<^sub>2) env = subst_term t\<^sub>1 env $ subst_term t\<^sub>2 env" |
"subst_term (\<Lambda> t) env = \<Lambda> subst_term t env" |
"subst_term t env = t"

fun consts_term :: "term \<Rightarrow> name fset" where
"consts_term (Const x) = {| x |}" |
"consts_term (t\<^sub>1 $ t\<^sub>2) = consts_term t\<^sub>1 |\<union>| consts_term t\<^sub>2" |
"consts_term (\<Lambda> t) = consts_term t" |
"consts_term _ = {||}"

instance
  by standard
      (auto
        simp: app_term_def const_term_def free_term_def
        elim: unapp_term.elims unconst_term.elims unfree_term.elims
        split: option.splits)

end

context pre_term begin

definition freess :: "'a list \<Rightarrow> name fset" where
"freess = ffUnion \<circ> fset_of_list \<circ> map frees"

lemma freess_cons[simp]: "freess (x # xs) = frees x |\<union>| freess xs"
unfolding freess_def by simp

lemma freess_single: "freess [x] = frees x"
unfolding freess_def by simp

lemma freess_empty[simp]: "freess [] = {||}"
unfolding freess_def by simp

lemma freess_app[simp]: "freess (xs @ ys) = freess xs |\<union>| freess ys"
unfolding freess_def by simp

lemma freess_subset: "set xs \<subseteq> set ys \<Longrightarrow> freess xs |\<subseteq>| freess ys"
unfolding freess_def comp_apply
by (intro ffunion_mono fset_of_list_subset) auto

abbreviation id_env :: "(name, 'a) fmap \<Rightarrow> bool" where
"id_env \<equiv> fmpred (\<lambda>x y. y = free x)"

definition closed_except :: "'a \<Rightarrow> name fset \<Rightarrow> bool" where
"closed_except t S \<longleftrightarrow> frees t |\<subseteq>| S"

abbreviation closed :: "'a \<Rightarrow> bool" where
"closed t \<equiv> closed_except t {||}"

lemmas term_inject = free_inject const_inject app_inject

lemmas term_distinct[simp] =
  app_const_distinct app_const_distinct[symmetric]
  app_free_distinct app_free_distinct[symmetric]
  free_const_distinct free_const_distinct[symmetric]

lemma app_size1: "size u\<^sub>1 < size (app u\<^sub>1 u\<^sub>2)"
by simp

lemma app_size2: "size u\<^sub>2 < size (app u\<^sub>1 u\<^sub>2)"
by simp

lemma unx_some_lemmas:
  "unapp u = Some x \<Longrightarrow> unconst u = None"
  "unapp u = Some x \<Longrightarrow> unfree u = None"
  "unconst u = Some y \<Longrightarrow> unapp u = None"
  "unconst u = Some y \<Longrightarrow> unfree u = None"
  "unfree u = Some z \<Longrightarrow> unconst u = None"
  "unfree u = Some z \<Longrightarrow> unapp u = None"
subgoal by (metis app_unapp const_unconst app_const_distinct not_None_eq surj_pair)
subgoal by (metis app_free_distinct app_unapp free_unfree option.exhaust surj_pair)
subgoal by (metis app_unapp const_unconst app_const_distinct old.prod.exhaust option.distinct(1) option.expand option.sel)
subgoal by (metis const_unconst free_const_distinct free_unfree option.exhaust)
subgoal by (metis const_unconst free_const_distinct free_unfree option.exhaust)
subgoal by (metis app_free_distinct app_unapp free_unfree not_Some_eq surj_pair)
done

lemma unx_none_simps[simp]:
  "unapp (const name) = None"
  "unapp (free name) = None"
  "unconst (app t u) = None"
  "unconst (free name) = None"
  "unfree (const name) = None"
  "unfree (app t u) = None"
subgoal by (metis app_unapp app_const_distinct not_None_eq surj_pair)
subgoal by (metis app_free_distinct app_unapp option.exhaust surj_pair)
subgoal by (metis const_unconst app_const_distinct option.distinct(1) option.expand option.sel)
subgoal by (metis const_unconst free_const_distinct option.exhaust)
subgoal by (metis free_const_distinct free_unfree option.exhaust)
subgoal by (metis app_free_distinct free_unfree not_Some_eq)
done

lemma term_cases:
  obtains (free) name where "t = free name"
        | (const) name where "t = const name"
        | (app) u\<^sub>1 u\<^sub>2 where "t = app u\<^sub>1 u\<^sub>2"
        | (other) "unfree t = None" "unapp t = None" "unconst t = None"
apply (cases "unfree t")
apply (cases "unconst t")
apply (cases "unapp t")
subgoal by auto
subgoal for x by (cases x) auto
subgoal by auto
subgoal by auto
done

definition is_const where
"is_const t \<longleftrightarrow> (unconst t \<noteq> None)"

definition const_name where
"const_name t = (case unconst t of Some name \<Rightarrow> name)"

lemma is_const_simps[simp]:
  "is_const (const name)"
  "\<not> is_const (app t u)"
  "\<not> is_const (free name)"
unfolding is_const_def by simp+

lemma const_name_simps[simp]:
  "const_name (const name) = name"
  "is_const t \<Longrightarrow> const (const_name t) = t"
unfolding const_name_def is_const_def by auto

definition is_free where
"is_free t \<longleftrightarrow> (unfree t \<noteq> None)"

definition free_name where
"free_name t = (case unfree t of Some name \<Rightarrow> name)"

lemma is_free_simps[simp]:
  "is_free (free name)"
  "\<not> is_free (const name)"
  "\<not> is_free (app t u)"
unfolding is_free_def by simp+

lemma free_name_simps[simp]:
  "free_name (free name) = name"
  "is_free t \<Longrightarrow> free (free_name t) = t"
unfolding free_name_def is_free_def by auto

definition is_app where
"is_app t \<longleftrightarrow> (unapp t \<noteq> None)"

definition left where
"left t = (case unapp t of Some (l, _) \<Rightarrow> l)"

definition right where
"right t = (case unapp t of Some (_, r) \<Rightarrow> r)"

lemma app_simps[simp]:
  "\<not> is_app (const name)"
  "\<not> is_app (free name)"
  "is_app (app t u)"
unfolding is_app_def by simp+

lemma left_right_simps[simp]:
  "left (app l r) = l"
  "right (app l r) = r"
  "is_app t \<Longrightarrow> app (left t) (right t) = t"
unfolding is_app_def left_def right_def by auto

definition ids :: "'a \<Rightarrow> name fset" where
"ids t = frees t |\<union>| consts t"

lemma closed_except_const[simp]: "closed_except (const name) S"
unfolding closed_except_def by auto

abbreviation closed_env :: "(name, 'a) fmap \<Rightarrow> bool" where
"closed_env \<equiv> fmpred (\<lambda>_. closed)"

lemma closed_except_self: "closed_except t (frees t)"
unfolding closed_except_def by simp

end

class "term" = pre_term + size +
  fixes
    abs_pred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    raw_induct[case_names const free app abs]:
      "(\<And>name. P (const name)) \<Longrightarrow>
        (\<And>name. P (free name)) \<Longrightarrow>
        (\<And>t\<^sub>1 t\<^sub>2. P t\<^sub>1 \<Longrightarrow> P t\<^sub>2 \<Longrightarrow> P (app t\<^sub>1 t\<^sub>2)) \<Longrightarrow>
        (\<And>t. abs_pred P t) \<Longrightarrow>
        P t"
  assumes
    raw_subst_id: "abs_pred (\<lambda>t. \<forall>env. id_env env \<longrightarrow> subst t env = t) t" and
    raw_subst_drop: "abs_pred (\<lambda>t. x |\<notin>| frees t \<longrightarrow> (\<forall>env. subst t (fmdrop x env) = subst t env)) t" and
    raw_subst_indep: "abs_pred (\<lambda>t. \<forall>env\<^sub>1 env\<^sub>2. closed_env env\<^sub>2 \<longrightarrow> fdisjnt (fmdom env\<^sub>1) (fmdom env\<^sub>2) \<longrightarrow> subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst (subst t env\<^sub>2) env\<^sub>1) t" and
    raw_subst_frees: "abs_pred (\<lambda>t. \<forall>env. closed_env env \<longrightarrow> frees (subst t env) = frees t |-| fmdom env) t" and
    raw_subst_consts': "abs_pred (\<lambda>a. \<forall>x. consts (subst a x) = consts a |\<union>| ffUnion (consts |`| fmimage x (frees a))) t" and
    abs_pred_trivI: "P t \<Longrightarrow> abs_pred P t"
begin

lemma subst_id: "id_env env \<Longrightarrow> subst t env = t"
proof (induction t arbitrary: env rule: raw_induct)
  case (abs t)
  show ?case
    by (rule raw_subst_id)
qed (auto split: option.splits)

lemma subst_drop: "x |\<notin>| frees t \<Longrightarrow> subst t (fmdrop x env) = subst t env"
proof (induction t arbitrary: env rule: raw_induct)
  case (abs t)
  show ?case
    by (rule raw_subst_drop)
qed (auto split: option.splits)

lemma subst_frees: "fmpred (\<lambda>_. closed) env \<Longrightarrow> frees (subst t env) = frees t |-| fmdom env"
proof (induction t arbitrary: env rule: raw_induct)
  case (abs t)
  show ?case
    by (rule raw_subst_frees)
qed (auto split: option.splits simp: closed_except_def)

lemma subst_consts': "consts (subst t env) = consts t |\<union>| ffUnion (consts |`| fmimage env (frees t))"
proof (induction t arbitrary: env rule: raw_induct)
  case (free name)
  then show ?case
    by (auto
          split: option.splits
          simp: ffUnion_alt_def fmlookup_ran_iff fmlookup_image_iff fmlookup_dom_iff
          intro!: fBexI)
next
  case (abs t)
  show ?case
    by (rule raw_subst_consts')
qed (auto simp: funion_image_bind_eq finter_funion_distrib fbind_funion)

fun match :: "term \<Rightarrow> 'a \<Rightarrow> (name, 'a) fmap option" where
"match (t\<^sub>1 $ t\<^sub>2) u = do {
  (u\<^sub>1, u\<^sub>2) \<leftarrow> unapp u;
  env\<^sub>1 \<leftarrow> match t\<^sub>1 u\<^sub>1;
  env\<^sub>2 \<leftarrow> match t\<^sub>2 u\<^sub>2;
  Some (env\<^sub>1 ++\<^sub>f env\<^sub>2)
}" |
"match (Const name) u =
  (case unconst u of
    None \<Rightarrow> None
  | Some name' \<Rightarrow> if name = name' then Some fmempty else None)" |
"match (Free name) u = Some (fmap_of_list [(name, u)])" |
"match (Bound n) u = None" |
"match (Abs t) u = None"

lemma match_simps[simp]:
  "match (t\<^sub>1 $ t\<^sub>2) (app u\<^sub>1 u\<^sub>2) = do {
    env\<^sub>1 \<leftarrow> match t\<^sub>1 u\<^sub>1;
    env\<^sub>2 \<leftarrow> match t\<^sub>2 u\<^sub>2;
    Some (env\<^sub>1 ++\<^sub>f env\<^sub>2)
  }"
  "match (Const name) (const name') = (if name = name' then Some fmempty else None)"
by auto

lemma match_some_induct[consumes 1, case_names app const free]:
  assumes "match t u = Some env"
  assumes "\<And>t\<^sub>1 t\<^sub>2 u\<^sub>1 u\<^sub>2 env\<^sub>1 env\<^sub>2. P t\<^sub>1 u\<^sub>1 env\<^sub>1 \<Longrightarrow> match t\<^sub>1 u\<^sub>1 = Some env\<^sub>1 \<Longrightarrow> P t\<^sub>2 u\<^sub>2 env\<^sub>2 \<Longrightarrow> match t\<^sub>2 u\<^sub>2 = Some env\<^sub>2 \<Longrightarrow> P (t\<^sub>1 $ t\<^sub>2) (app u\<^sub>1 u\<^sub>2) (env\<^sub>1 ++\<^sub>f env\<^sub>2)"
  assumes "\<And>name. P (Const name) (const name) fmempty"
  assumes "\<And>name u. P (Free name) u (fmupd name u fmempty)"
  shows "P t u env"
using assms
by (induction t u arbitrary: env rule: match.induct)
   (auto split: option.splits if_splits elim!: option_bindE)

lemma match_dom: "match p t = Some env \<Longrightarrow> fmdom env = frees p"
by (induction p arbitrary: t env)
   (fastforce split: option.splits if_splits elim: option_bindE)+

lemma match_vars: "match p t = Some env \<Longrightarrow> fmpred (\<lambda>_ u. frees u |\<subseteq>| frees t) env"
proof (induction p t env rule: match_some_induct)
  case (app t\<^sub>1 t\<^sub>2 u\<^sub>1 u\<^sub>2 env\<^sub>1 env\<^sub>2)
  show ?case
    apply rule
    using app
    by (fastforce intro: fmpred_mono_strong)+
qed auto

lemma match_appE_split:
  assumes "match (t\<^sub>1 $ t\<^sub>2) u = Some env"
  obtains u\<^sub>1 u\<^sub>2 env\<^sub>1 env\<^sub>2 where
    "u = app u\<^sub>1 u\<^sub>2" "match t\<^sub>1 u\<^sub>1 = Some env\<^sub>1" "match t\<^sub>2 u\<^sub>2 = Some env\<^sub>2" "env = env\<^sub>1 ++\<^sub>f env\<^sub>2"
using assms
by (auto split: option.splits elim!: option_bindE)

lemma subst_consts:
  assumes "consts t |\<subseteq>| S" "fmpred (\<lambda>_ u. consts u |\<subseteq>| S) env"
  shows "consts (subst t env) |\<subseteq>| S"
apply (subst subst_consts')
using assms by (auto intro!: ffUnion_least)

lemma subst_empty[simp]: "subst t fmempty = t"
by (auto simp: subst_id)

lemma subst_drop_fset: "fdisjnt S (frees t) \<Longrightarrow> subst t (fmdrop_fset S env) = subst t env"
by (induct S) (auto simp: subst_drop fdisjnt_alt_def)

lemma subst_restrict:
  assumes "frees t |\<subseteq>| M"
  shows "subst t (fmrestrict_fset M env) = subst t env"
proof -
  have *: "fmrestrict_fset M env = fmdrop_fset (fmdom env - M) env"
    by (rule fmap_ext) auto

  show ?thesis
    apply (subst *)
    apply (subst subst_drop_fset)
    unfolding fdisjnt_alt_def
    using assms by auto
qed

corollary subst_restrict'[simp]: "subst t (fmrestrict_fset (frees t) env) = subst t env"
by (simp add: subst_restrict)

corollary subst_cong:
  assumes "\<And>x. x |\<in>| frees t \<Longrightarrow> fmlookup \<Gamma>\<^sub>1 x = fmlookup \<Gamma>\<^sub>2 x"
  shows "subst t \<Gamma>\<^sub>1 = subst t \<Gamma>\<^sub>2"
proof -
  have "fmrestrict_fset (frees t) \<Gamma>\<^sub>1 = fmrestrict_fset (frees t) \<Gamma>\<^sub>2"
    apply (rule fmap_ext)
    using assms by simp
  thus ?thesis
    by (metis subst_restrict')
qed

corollary subst_add_disjnt:
  assumes "fdisjnt (frees t) (fmdom env\<^sub>1)"
  shows "subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst t env\<^sub>2"
proof -
  have "subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst t (fmrestrict_fset (frees t) (env\<^sub>1 ++\<^sub>f env\<^sub>2))"
    by (metis subst_restrict')
  also have "\<dots> = subst t (fmrestrict_fset (frees t) env\<^sub>1 ++\<^sub>f fmrestrict_fset (frees t) env\<^sub>2)"
    by simp
  also have "\<dots> = subst t (fmempty ++\<^sub>f fmrestrict_fset (frees t) env\<^sub>2)"
    unfolding fmfilter_alt_defs
    apply (subst fmfilter_false)
    using assms
    by (auto simp: fdisjnt_alt_def intro: fmdomI)
  also have "\<dots> = subst t (fmrestrict_fset (frees t) env\<^sub>2)"
    by simp
  also have "\<dots> = subst t env\<^sub>2"
    by simp
  finally show ?thesis .
qed

corollary subst_add_shadowed_env:
  assumes "frees t |\<subseteq>| fmdom env\<^sub>2"
  shows "subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst t env\<^sub>2"
proof -
  have "subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst t (fmdrop_fset (fmdom env\<^sub>2) env\<^sub>1 ++\<^sub>f env\<^sub>2)"
    by (subst fmadd_drop_left_dom) rule
  also have "\<dots> = subst t (fmrestrict_fset (frees t) (fmdrop_fset (fmdom env\<^sub>2) env\<^sub>1 ++\<^sub>f env\<^sub>2))"
    by (metis subst_restrict')
  also have "\<dots> = subst t (fmrestrict_fset (frees t) (fmdrop_fset (fmdom env\<^sub>2) env\<^sub>1) ++\<^sub>f fmrestrict_fset (frees t) env\<^sub>2)"
    by simp
  also have "\<dots> = subst t (fmempty ++\<^sub>f fmrestrict_fset (frees t) env\<^sub>2)"
    unfolding fmfilter_alt_defs
    using fsubsetD[OF assms]
    by auto
  also have "\<dots> = subst t env\<^sub>2"
    by simp
  finally show ?thesis .
qed

corollary subst_restrict_closed: "closed_except t S \<Longrightarrow> subst t (fmrestrict_fset S env) = subst t env"
by (metis subst_restrict closed_except_def)

lemma subst_closed_except_id:
  assumes "closed_except t S" "fdisjnt (fmdom env) S"
  shows "subst t env = t"
using assms
by (metis fdisjnt_subset_right fmdom_drop_fset fminus_cancel fmrestrict_fset_dom
          fmrestrict_fset_null closed_except_def subst_drop_fset subst_empty)

lemma subst_closed_except_preserved:
  assumes "closed_except t S" "fdisjnt (fmdom env) S"
  shows "closed_except (subst t env) S"
using assms
by (metis subst_closed_except_id)

corollary subst_closed_id: "closed t \<Longrightarrow> subst t env = t"
by (simp add: subst_closed_except_id fdisjnt_alt_def)

corollary subst_closed_preserved: "closed t \<Longrightarrow> closed (subst t env)"
by (simp add: subst_closed_except_preserved fdisjnt_alt_def)


context begin

private lemma subst_indep0:
  assumes "closed_env env\<^sub>2" "fdisjnt (fmdom env\<^sub>1) (fmdom env\<^sub>2)"
  shows "subst t (env\<^sub>1 ++\<^sub>f env\<^sub>2) = subst (subst t env\<^sub>2) env\<^sub>1"
using assms proof (induction t arbitrary: env\<^sub>1 env\<^sub>2 rule: raw_induct)
  case (free name)
  show ?case
    using \<open>closed_env env\<^sub>2\<close>
    by (cases rule: fmpred_cases[where x = name]) (auto simp: subst_closed_id)
next
  case (abs t)
  show ?case
    by (rule raw_subst_indep)
qed auto

lemma subst_indep:
  assumes "closed_env \<Gamma>'"
  shows "subst t (\<Gamma> ++\<^sub>f \<Gamma>') = subst (subst t \<Gamma>') \<Gamma>"
proof -
  have "subst t (\<Gamma> ++\<^sub>f \<Gamma>') = subst t (fmrestrict_fset (frees t) (\<Gamma> ++\<^sub>f \<Gamma>'))"
    by (metis subst_restrict')
  also have "\<dots> = subst t (fmrestrict_fset (frees t) \<Gamma> ++\<^sub>f \<Gamma>')"
    by (smt fmlookup_add fmlookup_restrict_fset subst_cong)
  also have "\<dots> = subst t (fmrestrict_fset (frees t |-| fmdom \<Gamma>') \<Gamma> ++\<^sub>f \<Gamma>')"
    by (rule subst_cong) (simp add: fmfilter_alt_defs(5))
  also have "\<dots> = subst (subst t \<Gamma>') (fmrestrict_fset (frees t |-| fmdom \<Gamma>') \<Gamma>)"
    apply (rule subst_indep0[OF assms])
    using fmdom_restrict_fset
    unfolding fdisjnt_alt_def
    by auto
  also have "\<dots> = subst (subst t \<Gamma>') (fmrestrict_fset (frees (subst t \<Gamma>')) \<Gamma>)"
    using assms by (auto simp: subst_frees)
  also have "\<dots> = subst (subst t \<Gamma>') \<Gamma>"
    by simp
  finally show ?thesis .
qed

lemma subst_indep':
  assumes "closed_env \<Gamma>'" "fdisjnt (fmdom \<Gamma>') (fmdom \<Gamma>)"
  shows "subst t (\<Gamma>' ++\<^sub>f \<Gamma>) = subst (subst t \<Gamma>') \<Gamma>"
using assms by (metis subst_indep fmadd_disjnt)

lemma subst_twice:
  assumes "\<Gamma>' \<subseteq>\<^sub>f \<Gamma>" "closed_env \<Gamma>'"
  shows "subst (subst t \<Gamma>') \<Gamma> = subst t \<Gamma>"
proof -
  have "subst (subst t \<Gamma>') \<Gamma> = subst t (\<Gamma> ++\<^sub>f \<Gamma>')"
    apply (rule subst_indep[symmetric])
    apply fact
    done
  also have "\<dots> = subst t \<Gamma>"
    apply (rule subst_cong)
    using \<open>\<Gamma>' \<subseteq>\<^sub>f \<Gamma>\<close> unfolding fmsubset_alt_def
    by fastforce
  finally show ?thesis .
qed

end

fun matchs :: "term list \<Rightarrow> 'a list \<Rightarrow> (name, 'a) fmap option" where
"matchs [] [] = Some fmempty" |
"matchs (t # ts) (u # us) = do { env\<^sub>1 \<leftarrow> match t u; env\<^sub>2 \<leftarrow> matchs ts us; Some (env\<^sub>1 ++\<^sub>f env\<^sub>2) }" |
"matchs _ _ = None"

lemmas matchs_induct = matchs.induct[case_names empty cons]

context begin

private lemma matchs_alt_def0:
  assumes "length ps = length vs"
  shows "map_option (\<lambda>env. m ++\<^sub>f env) (matchs ps vs) = map_option (foldl (++\<^sub>f) m) (those (map2 match ps vs))"
using assms proof (induction arbitrary: m rule: list_induct2)
  case (Cons x xs y ys)
  show ?case
    proof (cases "match x y")
      case x_y: Some
      show ?thesis
        proof (cases "matchs xs ys")
          case None
          with x_y Cons show ?thesis
            by simp
        next
          case Some
          with x_y show ?thesis
            apply simp
            using Cons(2) apply simp
            apply (subst option.map_comp)
            by (auto cong: map_option_cong)
        qed
    qed simp
qed simp

lemma matchs_alt_def:
  assumes "length ps = length vs"
  shows "matchs ps vs = map_option (foldl (++\<^sub>f) fmempty) (those (map2 match ps vs))"
by (subst matchs_alt_def0[where m = fmempty, simplified, symmetric, OF assms])
   (simp add: option.map_ident)

end

lemma matchs_neq_length_none[simp]: "length xs \<noteq> length ys \<Longrightarrow> matchs xs ys = None"
by (induct xs ys rule: matchs.induct) fastforce+

corollary matchs_some_eq_length: "matchs xs ys = Some env \<Longrightarrow> length xs = length ys"
by (metis option.distinct(1) matchs_neq_length_none)

lemma matchs_app[simp]:
  assumes "length xs\<^sub>2 = length ys\<^sub>2"
  shows "matchs (xs\<^sub>1 @ xs\<^sub>2) (ys\<^sub>1 @ ys\<^sub>2) =
          matchs xs\<^sub>1 ys\<^sub>1 \<bind> (\<lambda>env\<^sub>1. matchs xs\<^sub>2 ys\<^sub>2 \<bind> (\<lambda>env\<^sub>2. Some (env\<^sub>1 ++\<^sub>f env\<^sub>2)))"
using assms
by (induct xs\<^sub>1 ys\<^sub>1 rule: matchs.induct) fastforce+

corollary matchs_appI:
  assumes "matchs xs ys = Some env\<^sub>1" "matchs xs' ys' = Some env\<^sub>2"
  shows "matchs (xs @ xs') (ys @ ys') = Some (env\<^sub>1 ++\<^sub>f env\<^sub>2)"
using assms
by (metis (no_types, lifting) Option.bind_lunit matchs_app matchs_some_eq_length)

corollary matchs_dom:
  assumes "matchs ps ts = Some env"
  shows "fmdom env = freess ps"
using assms
by (induction ps ts arbitrary: env rule: matchs_induct)
   (auto simp: match_dom elim!: option_bindE)

fun find_match :: "(term \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> ((name, 'a) fmap \<times> term \<times> 'a) option" where
"find_match [] _ = None" |
"find_match ((pat, rhs) # cs) t =
  (case match pat t of
    Some env \<Rightarrow> Some (env, pat, rhs)
  | None \<Rightarrow> find_match cs t)"

lemma find_match_map:
  "find_match (map (\<lambda>(pat, t). (pat, f pat t)) cs) t =
    map_option (\<lambda>(env, pat, rhs). (env, pat, f pat rhs)) (find_match cs t)"
by (induct cs) (auto split: option.splits)

lemma find_match_elem:
  assumes "find_match cs t = Some (env, pat, rhs)"
  shows "(pat, rhs) \<in> set cs" "match pat t = Some env"
using assms
by (induct cs) (auto split: option.splits)

lemma match_subst_closed:
  assumes "match pat t = Some env" "closed_except rhs (frees pat)" "closed t"
  shows "closed (subst rhs env)"
using assms
by (smt fminusE fmpred_iff fset_mp fsubsetI closed_except_def match_vars match_dom subst_frees)

fun rewrite_step :: "(term \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"rewrite_step (t\<^sub>1, t\<^sub>2) u = map_option (subst t\<^sub>2) (match t\<^sub>1 u)"

abbreviation rewrite_step' :: "(term \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_/ \<turnstile>/ _ \<rightarrow>/ _" [50,0,50] 50) where
"r \<turnstile> t \<rightarrow> u \<equiv> rewrite_step r t = Some u"

lemma rewrite_step_closed:
  assumes "frees t\<^sub>2 |\<subseteq>| frees t\<^sub>1" "(t\<^sub>1, t\<^sub>2) \<turnstile> u \<rightarrow> u'" "closed u"
  shows "closed u'"
proof -
  from assms obtain env where *: "match t\<^sub>1 u = Some env"
    by auto
  then have "closed (subst t\<^sub>2 env)"
    apply (rule match_subst_closed[where pat = t\<^sub>1 and t = u])
    using assms unfolding closed_except_def by auto
  with * show ?thesis
    using assms by auto
qed

definition matches :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<lesssim>" 50) where
"t \<lesssim> u \<longleftrightarrow> (\<exists>env. subst t env = u)"

lemma matchesI[intro]: "subst t env = u \<Longrightarrow> t \<lesssim> u"
unfolding matches_def by auto

lemma matchesE[elim]:
  assumes "t \<lesssim> u"
  obtains env where "subst t env = u"
using assms unfolding matches_def by blast

definition overlapping :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"overlapping s t \<longleftrightarrow> (\<exists>u. s \<lesssim> u \<and> t \<lesssim> u)"

lemma overlapping_refl: "overlapping t t"
unfolding overlapping_def matches_def by blast

lemma overlapping_sym: "overlapping t u \<Longrightarrow> overlapping u t"
unfolding overlapping_def by auto

lemma overlappingI[intro]: "s \<lesssim> u \<Longrightarrow> t \<lesssim> u \<Longrightarrow> overlapping s t"
unfolding overlapping_def by auto

lemma overlappingE[elim]:
  assumes "overlapping s t"
  obtains u where "s \<lesssim> u" "t \<lesssim> u"
using assms unfolding overlapping_def by blast

abbreviation "non_overlapping s t \<equiv> \<not> overlapping s t"

corollary non_overlapping_implies_neq: "non_overlapping t u \<Longrightarrow> t \<noteq> u"
by (metis overlapping_refl)

end

inductive rewrite_first :: "(term \<times> 'a::term) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
match: "match pat t = Some env \<Longrightarrow> rewrite_first ((pat, rhs) # _) t (subst rhs env)" |
nomatch: "match pat t = None \<Longrightarrow> rewrite_first cs t t' \<Longrightarrow> rewrite_first ((pat, _) # cs) t t'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) rewrite_first .

lemma rewrite_firstE:
  assumes "rewrite_first cs t t'"
  obtains pat rhs env where "(pat, rhs) \<in> set cs" "match pat t = Some env" "t' = subst rhs env"
using assms by induction auto

text \<open>
  This doesn't follow from @{thm [source] find_match_elem}, because @{const rewrite_first} requires
  the first match, not just any.
\<close>

lemma find_match_rewrite_first:
  assumes "find_match cs t = Some (env, pat, rhs)"
  shows "rewrite_first cs t (subst rhs env)"
using assms proof (induction cs)
  case (Cons c cs)
  obtain pat0 rhs0 where "c = (pat0, rhs0)"
    by fastforce
  thus ?case
    using Cons
    by (cases "match pat0 t") (auto intro: rewrite_first.intros)
qed simp

definition term_cases :: "(name \<Rightarrow> 'b) \<Rightarrow> (name \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a::term \<Rightarrow> 'b" where
"term_cases if_const if_free if_app otherwise t =
  (case unconst t of
    Some name \<Rightarrow> if_const name |
    None \<Rightarrow> (case unfree t of
      Some name \<Rightarrow> if_free name |
      None \<Rightarrow>
        (case unapp t of
          Some (t, u) \<Rightarrow> if_app t u
        | None \<Rightarrow> otherwise)))"

lemma term_cases_cong[fundef_cong]:
  assumes "t = u" "otherwise1 = otherwise2"
  assumes "(\<And>name. t = const name \<Longrightarrow> if_const1 name = if_const2 name)"
  assumes "(\<And>name. t = free name \<Longrightarrow> if_free1 name = if_free2 name)"
  assumes "(\<And>u\<^sub>1 u\<^sub>2. t = app u\<^sub>1 u\<^sub>2 \<Longrightarrow> if_app1 u\<^sub>1 u\<^sub>2 = if_app2 u\<^sub>1 u\<^sub>2)"
  shows "term_cases if_const1 if_free1 if_app1 otherwise1 t = term_cases if_const2 if_free2 if_app2 otherwise2 u"
using assms
unfolding term_cases_def
by (auto split: option.splits)

lemma term_cases[simp]:
  "term_cases if_const if_free if_app otherwise (const name) = if_const name"
  "term_cases if_const if_free if_app otherwise (free name) = if_free name"
  "term_cases if_const if_free if_app otherwise (app t u) = if_app t u"
unfolding term_cases_def
by (auto split: option.splits)

lemma term_cases_template:
  assumes "\<And>x. f x = term_cases if_const if_free if_app otherwise x"
  shows "f (const name) = if_const name"
    and "f (free name) = if_free name"
    and "f (app t u) = if_app t u"
unfolding assms by (rule term_cases)+

context "term" begin

function (sequential) strip_comb :: "'a \<Rightarrow> 'a \<times> 'a list" where
[simp del]: "strip_comb t =
  (case unapp t of
    Some (t, u) \<Rightarrow>
      (let (f, args) = strip_comb t in (f, args @ [u]))
  | None \<Rightarrow> (t, []))"
by pat_completeness auto

(* FIXME why is this not automatic? *)
termination
  apply (relation "measure size")
  apply rule
  apply auto
  done

lemma strip_comb_simps[simp]:
  "strip_comb (app t u) = (let (f, args) = strip_comb t in (f, args @ [u]))"
  "unapp t = None \<Longrightarrow> strip_comb t = (t, [])"
by (subst strip_comb.simps; auto)+

lemma strip_comb_induct[case_names app no_app]:
  assumes "\<And>x y. P x \<Longrightarrow> P (app x y)"
  assumes "\<And>t. unapp t = None \<Longrightarrow> P t"
  shows "P t"
proof (rule strip_comb.induct, goal_cases)
  case (1 t)
  show ?case
    proof (cases "unapp t")
      case None
      with assms show ?thesis by metis
    next
      case (Some a)
      then show ?thesis
        apply (cases a)
        using 1 assms by auto
    qed
qed

lemma strip_comb_size: "t' \<in> set (snd (strip_comb t)) \<Longrightarrow> size t' < size t"
by (induction t rule: strip_comb_induct) (auto split: prod.splits)

lemma sstrip_comb_termination[termination_simp]:
  "(f, ts) = strip_comb t \<Longrightarrow> t' \<in> set ts \<Longrightarrow> size t' < size t"
by (metis snd_conv strip_comb_size)

lemma strip_comb_empty: "snd (strip_comb t) = [] \<Longrightarrow> fst (strip_comb t) = t"
by (induction t rule: strip_comb_induct) (auto split: prod.splits)

lemma strip_comb_app: "fst (strip_comb (app t u)) = fst (strip_comb t)"
by (simp split: prod.splits)

primrec list_comb :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a" where
"list_comb f [] = f" |
"list_comb f (t # ts) = list_comb (app f t) ts"

lemma list_comb_app[simp]: "list_comb f (xs @ ys) = list_comb (list_comb f xs) ys"
by (induct xs arbitrary: f) auto

corollary list_comb_snoc: "app (list_comb f xs) y = list_comb f (xs @ [y])"
by simp

lemma list_comb_size[simp]: "size (list_comb f xs) = size f + size_list size xs"
by (induct xs arbitrary: f) auto

lemma subst_list_comb: "subst (list_comb f xs) env = list_comb (subst f env) (map (\<lambda>t. subst t env) xs)"
by (induct xs arbitrary: f) auto

abbreviation const_list_comb :: "name \<Rightarrow> 'a list \<Rightarrow> 'a" (infixl "$$" 70) where
"const_list_comb name \<equiv> list_comb (const name)"

lemma list_strip_comb[simp]: "list_comb (fst (strip_comb t)) (snd (strip_comb t)) = t"
by (induction t rule: strip_comb_induct) (auto split: prod.splits)

lemma strip_list_comb: "strip_comb (list_comb f ys) = (fst (strip_comb f), snd (strip_comb f) @ ys)"
by (induct ys arbitrary: f) (auto simp: split_beta)

lemma strip_list_comb_const: "strip_comb (name $$ xs) = (const name, xs)"
by (simp add: strip_list_comb)

lemma frees_list_comb[simp]: "frees (list_comb t xs) = frees t |\<union>| freess xs"
by (induct xs arbitrary: t) (auto simp: freess_def)

lemma consts_list_comb: "consts (list_comb f xs) = consts f |\<union>| ffUnion (fset_of_list (map consts xs))"
by (induct xs arbitrary: f) auto

lemma ids_list_comb: "ids (list_comb f xs) = ids f |\<union>| ffUnion (fset_of_list (map ids xs))"
unfolding ids_def frees_list_comb consts_list_comb freess_def
apply auto
apply (smt fbind_iff finsert_absorb finsert_fsubset funion_image_bind_eq inf_sup_ord(3))
apply (metis fbind_iff funionCI funion_image_bind_eq)
by (smt fbind_iff funionE funion_image_bind_eq)

lemma frees_strip_comb: "frees t = frees (fst (strip_comb t)) |\<union>| freess (snd (strip_comb t))"
by (metis list_strip_comb frees_list_comb)

lemma list_comb_cases':
  obtains (app) "is_app (list_comb f xs)"
        | (empty) "list_comb f xs = f" "xs = []"
by (induction xs arbitrary: f) auto

(* FIXME case names? *)
lemma list_comb_cases[consumes 1]:
  assumes "t = list_comb f xs"
  obtains (head) "t = f" "xs = []"
        | (app) u v where "t = app u v"
using assms by (metis list_comb_cases' left_right_simps(3))

end

fun left_nesting :: "'a::term \<Rightarrow> nat" where
[simp del]: "left_nesting t = term_cases (\<lambda>_. 0) (\<lambda>_. 0) (\<lambda>t u. Suc (left_nesting t)) 0 t"

lemmas left_nesting_simps[simp] = term_cases_template[OF left_nesting.simps]

lemma list_comb_nesting[simp]: "left_nesting (list_comb f xs) = left_nesting f + length xs"
by (induct xs arbitrary: f) auto

lemma list_comb_cond_inj:
  assumes "list_comb f xs = list_comb g ys" "left_nesting f = left_nesting g"
  shows "xs = ys" "f = g"
using assms proof (induction xs arbitrary: f g ys)
  case Nil
  fix f g :: 'a
  fix ys
  assume prems: "list_comb f [] = list_comb g ys" "left_nesting f = left_nesting g"

  hence "left_nesting f = left_nesting g + length ys"
    by simp
  with prems show "[] = ys" "f = g"
    by simp+
next
  case (Cons x xs)
  fix f g ys
  assume prems: "list_comb f (x # xs) = list_comb g ys" "left_nesting f = left_nesting g"

  hence "left_nesting (list_comb f (x # xs)) = left_nesting (list_comb g ys)"
    by simp
  hence "Suc (left_nesting f + length xs) = left_nesting g + length ys"
    by simp
  with prems have "length ys = Suc (length xs)"
    by linarith
  then obtain z zs where "ys = z # zs"
    by (metis length_Suc_conv)

  thus "x # xs = ys" "f = g"
    using prems Cons[where ys = zs and f = "app f x" and g = "app g z"]
    by (auto dest: app_inject)
qed

lemma list_comb_inj_second: "inj (list_comb f)"
by (metis injI list_comb_cond_inj)

lemma list_comb_semi_inj:
  assumes "length xs = length ys"
  assumes "list_comb f xs = list_comb g ys"
  shows "xs = ys" "f = g"
proof -
  from assms have "left_nesting (list_comb f xs) = left_nesting (list_comb g ys)"
    by simp
  with assms have "left_nesting f = left_nesting g"
    unfolding list_comb_nesting by simp
  with assms show "xs = ys" "f = g"
    by (metis list_comb_cond_inj)+
qed

fun no_abs :: "'a::term \<Rightarrow> bool" where
[simp del]: "no_abs t = term_cases (\<lambda>_. True) (\<lambda>_. True) (\<lambda>t u. no_abs t \<and> no_abs u) False t"

lemmas no_abs_simps[simp] = term_cases_template[OF no_abs.simps]

lemma no_abs_induct[consumes 1, case_names free const app, induct pred: no_abs]:
  assumes "no_abs t"
  assumes "\<And>name. P (free name)"
  assumes "\<And>name. P (const name)"
  assumes "\<And>t\<^sub>1 t\<^sub>2. P t\<^sub>1 \<Longrightarrow> no_abs t\<^sub>1 \<Longrightarrow> P t\<^sub>2 \<Longrightarrow> no_abs t\<^sub>2 \<Longrightarrow> P (app t\<^sub>1 t\<^sub>2)"
  shows "P t"
using assms(1) proof (induction rule: no_abs.induct)
  case (1 t)
  show ?case
    proof (cases rule: pre_term_class.term_cases[where t = t])
      case (free name)
      then show ?thesis
        using assms by auto
    next
      case (const name)
      then show ?thesis
        using assms by auto
    next
      case (app u\<^sub>1 u\<^sub>2)
      with assms have "P u\<^sub>1" "P u\<^sub>2"
        using 1 by auto
      with assms \<open>no_abs t\<close> show ?thesis
        unfolding \<open>t = _\<close> by auto
    next
      case other
      then show ?thesis
        using \<open>no_abs t\<close>
        apply (subst (asm) no_abs.simps)
        apply (subst (asm) term_cases_def)
        by simp
    qed
qed

lemma no_abs_cases[consumes 1, cases pred: no_abs]:
  assumes "no_abs t"
  obtains (free) name where "t = free name"
        | (const) name where "t = const name"
        | (app) t\<^sub>1 t\<^sub>2 where "t = app t\<^sub>1 t\<^sub>2" "no_abs t\<^sub>1" "no_abs t\<^sub>2"
proof (cases rule: pre_term_class.term_cases[where t = t])
  case (app u\<^sub>1 u\<^sub>2)
  show ?thesis
    apply (rule that(3))
    apply fact
    using \<open>no_abs t\<close> unfolding \<open>t = _\<close> by auto
next
  case other
  then have False
    using \<open>no_abs t\<close>
    apply (subst (asm) no_abs.simps)
    by (auto simp: term_cases_def)
  then show ?thesis ..
qed

definition is_abs :: "'a::term \<Rightarrow> bool" where
"is_abs t = term_cases (\<lambda>_. False) (\<lambda>_. False) (\<lambda>_ _. False) True t"

lemmas is_abs_simps[simp] = term_cases_template[OF is_abs_def]

definition abs_ish :: "term list \<Rightarrow> 'a::term \<Rightarrow> bool" where
"abs_ish pats rhs \<longleftrightarrow> pats \<noteq> [] \<or> is_abs rhs"

locale simple_syntactic_and =
  fixes P :: "'a::term \<Rightarrow> bool"
  assumes app: "P (app t u) \<longleftrightarrow> P t \<and> P u"
begin

context
  notes app[simp]
begin

lemma list_comb: "P (list_comb f xs) \<longleftrightarrow> P f \<and> list_all P xs"
by (induction xs arbitrary: f) auto

corollary list_combE:
  assumes "P (list_comb f xs)"
  shows "P f" "x \<in> set xs \<Longrightarrow> P x"
using assms
by (auto simp: list_comb list_all_iff)

lemma match:
  assumes "match pat t = Some env" "P t"
  shows "fmpred (\<lambda>_. P) env"
using assms
by (induction pat t env rule: match_some_induct) auto

lemma matchs:
  assumes "matchs pats ts = Some env" "list_all P ts"
  shows "fmpred (\<lambda>_. P) env"
using assms
by (induction pats ts arbitrary: env rule: matchs.induct) (auto elim!: option_bindE intro: match)

end

end

locale subst_syntactic_and = simple_syntactic_and +
  assumes subst: "P t \<Longrightarrow> fmpred (\<lambda>_. P) env \<Longrightarrow> P (subst t env)"
begin

lemma rewrite_step:
  assumes "(lhs, rhs) \<turnstile> t \<rightarrow> t'" "P t" "P rhs"
  shows "P t'"
using assms by (auto intro: match subst)

end

locale simple_syntactic_or =
  fixes P :: "'a::term \<Rightarrow> bool"
  assumes app: "P (app t u) \<longleftrightarrow> P t \<or> P u"
begin

context
  notes app[simp]
begin

lemma list_comb: "P (list_comb f xs) \<longleftrightarrow> P f \<or> list_ex P xs"
by (induction xs arbitrary: f) auto

lemma match:
  assumes "match pat t = Some env" "\<not> P t"
  shows "fmpred (\<lambda>_ t. \<not> P t) env"
using assms
by (induction pat t env rule: match_some_induct) auto

end

sublocale neg: simple_syntactic_and "\<lambda>t. \<not> P t"
by standard (auto simp: app)

end

global_interpretation no_abs: simple_syntactic_and no_abs
by standard simp

global_interpretation closed: simple_syntactic_and "\<lambda>t. closed_except t S" for S
by standard (simp add: closed_except_def)

global_interpretation closed: subst_syntactic_and closed
by standard (rule subst_closed_preserved)

corollary closed_list_comb: "closed (name $$ args) \<longleftrightarrow> list_all closed args"
by (simp add: closed.list_comb)

locale term_struct_rel =
  fixes P :: "'a::term \<Rightarrow> 'b::term \<Rightarrow> bool"
  assumes P_t_const: "P t (const name) \<Longrightarrow> t = const name"
  assumes P_const_const: "P (const name) (const name)"
  assumes P_t_app: "P t (app u\<^sub>1 u\<^sub>2) \<Longrightarrow> \<exists>t\<^sub>1 t\<^sub>2. t = app t\<^sub>1 t\<^sub>2 \<and> P t\<^sub>1 u\<^sub>1 \<and> P t\<^sub>2 u\<^sub>2"
  assumes P_app_app: "P t\<^sub>1 u\<^sub>1 \<Longrightarrow> P t\<^sub>2 u\<^sub>2 \<Longrightarrow> P (app t\<^sub>1 t\<^sub>2) (app u\<^sub>1 u\<^sub>2)"
begin

abbreviation P_env :: "('k, 'a) fmap \<Rightarrow> ('k, 'b) fmap \<Rightarrow> bool" where
"P_env \<equiv> fmrel P"

lemma related_match:
  assumes "match x u = Some env" "P t u"
  obtains env' where "match x t = Some env'" "P_env env' env"
using assms proof (induction x u env arbitrary: t thesis rule: match_some_induct)
  case (app v\<^sub>1 v\<^sub>2 w\<^sub>1 w\<^sub>2 env\<^sub>1 env\<^sub>2)
  obtain u\<^sub>1 u\<^sub>2 where "t = app u\<^sub>1 u\<^sub>2" "P u\<^sub>1 w\<^sub>1" "P u\<^sub>2 w\<^sub>2"
    using P_t_app[OF \<open>P t (app w\<^sub>1 w\<^sub>2)\<close>] by auto
  with app obtain env\<^sub>1' env\<^sub>2'
    where "match v\<^sub>1 u\<^sub>1 = Some env\<^sub>1'" "P_env env\<^sub>1' env\<^sub>1"
      and "match v\<^sub>2 u\<^sub>2 = Some env\<^sub>2'" "P_env env\<^sub>2' env\<^sub>2"
    by metis
  hence "match (v\<^sub>1 $ v\<^sub>2) (app u\<^sub>1 u\<^sub>2) = Some (env\<^sub>1' ++\<^sub>f env\<^sub>2')"
    by simp

  show ?case
    proof (rule app.prems)
      show "match (v\<^sub>1 $ v\<^sub>2) t = Some (env\<^sub>1' ++\<^sub>f env\<^sub>2')"
        unfolding \<open>t = _\<close> by fact
    next
      show "P_env (env\<^sub>1' ++\<^sub>f env\<^sub>2') (env\<^sub>1 ++\<^sub>f env\<^sub>2)"
        by rule fact+
    qed
qed (auto split: option.splits if_splits dest: P_t_const)

lemma list_combI:
  assumes "list_all2 P us\<^sub>1 us\<^sub>2" "P t\<^sub>1 t\<^sub>2"
  shows "P (list_comb t\<^sub>1 us\<^sub>1) (list_comb t\<^sub>2 us\<^sub>2)"
using assms
by (induction arbitrary: t\<^sub>1 t\<^sub>2 rule: list.rel_induct) (auto intro: P_app_app)

lemma list_combE:
  assumes "P t (name $$ args)"
  obtains args' where "t = name $$ args'" "list_all2 P args' args"
using assms proof (induction args arbitrary: t thesis rule: rev_induct)
  case Nil
  hence "P t (const name)"
    by simp
  hence "t = const name"
    using P_t_const by auto
  with Nil show ?case
    by simp
next
  case (snoc x xs)
  hence "P t (app (name $$ xs) x)"
    by simp
  obtain t' y where "t = app t' y" "P t' (name $$ xs)" "P y x"
    using P_t_app[OF \<open>P t (app (name $$ xs) x)\<close>] by auto
  with snoc obtain ys where "t' = name $$ ys" "list_all2 P ys xs"
    by blast
  show ?case
    proof (rule snoc.prems)
      show "t = name $$ (ys @ [y])"
        unfolding \<open>t = app t' y\<close> \<open>t' = name $$ ys\<close>
        by simp
    next
      have "list_all2 P [y] [x]"
        using \<open>P y x\<close> by simp
      thus "list_all2 P (ys @ [y]) (xs @ [x])"
        using \<open>list_all2 P ys xs\<close>
        by (metis list_all2_appendI)
    qed
qed

end

locale term_struct_rel_strong = term_struct_rel +
  assumes P_const_t: "P (const name) t \<Longrightarrow> t = const name"
  assumes P_app_t: "P (app u\<^sub>1 u\<^sub>2) t \<Longrightarrow> \<exists>t\<^sub>1 t\<^sub>2. t = app t\<^sub>1 t\<^sub>2 \<and> P u\<^sub>1 t\<^sub>1 \<and> P u\<^sub>2 t\<^sub>2"
begin

lemma unconst_rel: "P t u \<Longrightarrow> unconst t = unconst u"
by (metis P_const_t P_t_const const_name_simps(2) is_const_def unconst_const)

lemma unapp_rel: "P t u \<Longrightarrow> rel_option (rel_prod P P) (unapp t) (unapp u)"
by (smt P_app_t P_t_app is_app_def left_right_simps(3) option.rel_sel option.sel option.simps(3) rel_prod_inject unapp_app)

lemma match_rel:
  assumes "P t u"
  shows "rel_option P_env (match p t) (match p u)"
using assms proof (induction p arbitrary: t u)
  case (Const name)
  thus ?case
    by (auto split: option.splits simp: unconst_rel)
next
  case (App p1 p2)
  hence "rel_option (rel_prod P P) (unapp t) (unapp u)"
    by (metis unapp_rel)
  thus ?case
    using App
    by cases (auto split: option.splits intro!: rel_option_bind)
qed auto

lemma find_match_rel:
  assumes "list_all2 (rel_prod (=) P) cs cs'" "P t t'"
  shows "rel_option (rel_prod P_env (rel_prod (=) P)) (find_match cs t) (find_match cs' t')"
using assms proof induction
  case (Cons x xs y ys)
  moreover obtain px tx py ty where "x = (px, tx)" "y = (py, ty)"
    by (cases x, cases y) auto
  moreover note match_rel[OF Cons(4), where p = px]
  ultimately show ?case
    by (auto elim: option.rel_cases)
qed auto

end

fun convert_term :: "'a::term \<Rightarrow> 'b::term" where
[simp del]: "convert_term t = term_cases const free (\<lambda>t u. app (convert_term t) (convert_term u)) undefined t"

lemmas convert_term_simps[simp] = term_cases_template[OF convert_term.simps]

lemma convert_term_id:
  assumes "no_abs t"
  shows "convert_term t = t"
using assms by induction auto

lemma convert_term_no_abs:
  assumes "no_abs t"
  shows "no_abs (convert_term t)"
using assms by induction auto

lemma convert_term_inj:
  assumes "no_abs t" "no_abs t'" "convert_term t = convert_term t'"
  shows "t = t'"
using assms proof (induction t arbitrary: t')
  case (free name)
  then show ?case
    by cases (auto dest: term_inject)
next
  case (const name)
  then show ?case
    by cases (auto dest: term_inject)
next
  case (app t\<^sub>1 t\<^sub>2)
  from \<open>no_abs t'\<close> show ?case
    apply cases
    using app by (auto dest: term_inject)
qed

lemma convert_term_idem:
  assumes "no_abs t"
  shows "convert_term (convert_term t) = convert_term t"
using assms by (induction t) auto

lemma convert_term_frees[simp]:
  assumes "no_abs t"
  shows "frees (convert_term t) = frees t"
using assms by induction auto

lemma convert_term_consts[simp]:
  assumes "no_abs t"
  shows "consts (convert_term t) = consts t"
using assms by induction auto

text \<open>
  The following lemma does not generalize to when @{prop \<open>match t u = None\<close>}. Assume matching
  return @{const None}, because the pattern is an application and the object is a term satisfying
  @{const is_abs}. Now, @{const convert_term} applied to the object will produce @{const undefined}.
  Of course we don't know anything about that and whether or not that matches. A workaround would
  be to require implementations of @{class term} to prove @{prop \<open>\<exists>t. is_abs t\<close>}, such that
  @{const convert_term} could use that instead of @{const undefined}. This seems to be too much of a
  special case in order to be useful.
\<close>

lemma convert_term_match:
  assumes "match t u = Some env"
  shows "match t (convert_term u) = Some (fmmap convert_term env)"
using assms by (induction t u env rule: match_some_induct) auto

section \<open>Related work\<close>

text \<open>
  Schmidt-Schauß and Siekmann @{cite schmidt1988unification} discuss the concept of
  \<^emph>\<open>unification algebras\<close>. They generalize terms to \<^emph>\<open>objects\<close> and substitutions to \<^emph>\<open>mappings\<close>.
  A unification problem can be rephrased to finding a mapping such that a set of objects are mapped
  to the same object. The advantage of this generalization is that other -- superficially unrelated
  -- problems like solving algebraic equations or querying logic programs can be seen as unification
  problems.

  In particular, the authors note that among the similarities of such problems are that ``objects
  [have] variables'' whose ``names do not matter'' and ``there exists an operation like substituting
  objects into variables''. The major difference between this formalization and their work is that I
  use concrete types for variables and mappings. Otherwise, some similarities to here can be found.

  Eder @{cite eder1985properties} discusses properties of substitutions with a special focus on a
  partial ordering between substitutions. However, Eder constructs and uses a concrete type of
  first-order terms, similarly to Sternagel and Thiemann @{cite sternagel2018terms}.

  Williams @{cite williams1991instantiation} defines substitutions as elements in a monoid.
  In this setting, instantiations can be represented as \<^emph>\<open>monoid actions\<close>. Williams then proceeds to
  define -- for arbitrary sets of terms and variables -- the notion of \<^emph>\<open>instantiation systems,\<close>
  heavily drawing on notation from Schmidt-Schauß and Siekmann. Some of the presented axioms
  are also present in this formalization, as are some theorems that have a direct correspondence.
\<close>

end