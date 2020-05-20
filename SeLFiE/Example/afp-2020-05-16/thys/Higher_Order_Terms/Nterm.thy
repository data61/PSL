chapter \<open>Terms with explicit bound variable names\<close>

theory Nterm
imports Term_Class
begin

text \<open>
  The \<open>nterm\<close> type is similar to @{typ term}, but removes the distinction between bound and free
  variables. Instead, there are only named variables.
\<close>

datatype nterm =
  Nconst name |
  Nvar name |
  Nabs name nterm ("\<Lambda>\<^sub>n _. _" [0, 50] 50) |
  Napp nterm nterm (infixl "$\<^sub>n" 70)

derive linorder nterm

instantiation nterm :: pre_term begin

definition app_nterm where
"app_nterm t u = t $\<^sub>n u"

fun unapp_nterm where
"unapp_nterm (t $\<^sub>n u) = Some (t, u)" |
"unapp_nterm _ = None"

definition const_nterm where
"const_nterm = Nconst"

fun unconst_nterm where
"unconst_nterm (Nconst name) = Some name" |
"unconst_nterm _ = None"

definition free_nterm where
"free_nterm = Nvar"

fun unfree_nterm where
"unfree_nterm (Nvar name) = Some name" |
"unfree_nterm _ = None"

fun frees_nterm :: "nterm \<Rightarrow> name fset" where
"frees_nterm (Nvar x) = {| x |}" |
"frees_nterm (t\<^sub>1 $\<^sub>n t\<^sub>2) = frees_nterm t\<^sub>1 |\<union>| frees_nterm t\<^sub>2" |
"frees_nterm (\<Lambda>\<^sub>n x. t) = frees_nterm t - {| x |}" |
"frees_nterm (Nconst _) = {||}"

fun subst_nterm :: "nterm \<Rightarrow> (name, nterm) fmap \<Rightarrow> nterm" where
"subst_nterm (Nvar s) env = (case fmlookup env s of Some t \<Rightarrow> t | None \<Rightarrow> Nvar s)" |
"subst_nterm (t\<^sub>1 $\<^sub>n t\<^sub>2) env = subst_nterm t\<^sub>1 env $\<^sub>n subst_nterm t\<^sub>2 env" |
"subst_nterm (\<Lambda>\<^sub>n x. t) env = (\<Lambda>\<^sub>n x. subst_nterm t (fmdrop x env))" |
"subst_nterm t env = t"

fun consts_nterm :: "nterm \<Rightarrow> name fset" where
"consts_nterm (Nconst x) = {| x |}" |
"consts_nterm (t\<^sub>1 $\<^sub>n t\<^sub>2) = consts_nterm t\<^sub>1 |\<union>| consts_nterm t\<^sub>2" |
"consts_nterm (Nabs _ t) = consts_nterm t" |
"consts_nterm (Nvar _) = {||}"

instance
by standard
   (auto
      simp: app_nterm_def const_nterm_def free_nterm_def
      elim: unapp_nterm.elims unconst_nterm.elims unfree_nterm.elims
      split: option.splits)

end

instantiation nterm :: "term" begin

definition abs_pred_nterm :: "(nterm \<Rightarrow> bool) \<Rightarrow> nterm \<Rightarrow> bool" where
[code del]: "abs_pred P t \<longleftrightarrow> (\<forall>t' x. t = (\<Lambda>\<^sub>n x. t') \<longrightarrow> P t' \<longrightarrow> P t)"

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    by (induction t) (auto simp: abs_pred_nterm_def const_nterm_def free_nterm_def app_nterm_def)
next
  case 3
  show ?case
    unfolding abs_pred_nterm_def
    apply auto
    apply (subst fmdrop_comm)
    by auto
next
  case 4
  show ?case
    unfolding abs_pred_nterm_def
    apply auto
    apply (erule_tac x = "fmdrop x env\<^sub>1" in allE)
    apply (erule_tac x = "fmdrop x env\<^sub>2" in allE)
    by (auto simp: fdisjnt_alt_def)
next
  case 5
  show ?case
    unfolding abs_pred_nterm_def
    apply clarify
    subgoal for t' x env
      apply (erule allE[where x = "fmdrop x env"])
      by auto
    done
next
  case 6
  show ?case
    unfolding abs_pred_nterm_def
    apply clarify
    subgoal premises prems[rule_format] for t x env
      unfolding consts_nterm.simps subst_nterm.simps frees_nterm.simps
      apply (subst prems)
      unfolding fmimage_drop fmdom_drop
      apply (rule arg_cong[where f = "(|\<union>|) (consts t)"])
      apply (rule arg_cong[where f = ffUnion])
      apply (rule arg_cong[where f = "\<lambda>x. consts |`| fmimage env x"])
      by auto
    done
qed (auto simp: abs_pred_nterm_def)

end

lemma no_abs_abs[simp]: "\<not> no_abs (\<Lambda>\<^sub>n x. t)"
by (subst no_abs.simps) (auto simp: term_cases_def)

end