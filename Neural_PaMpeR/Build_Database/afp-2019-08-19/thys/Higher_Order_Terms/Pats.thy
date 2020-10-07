chapter \<open>Wellformedness of patterns\<close>

theory Pats
imports Term
begin

text \<open>
  The @{class term} class already defines a generic definition of \<^emph>\<open>matching\<close> a \<^emph>\<open>pattern\<close> with a
  term. Importantly, the type of patterns is neither generic, nor a dedicated pattern type; instead,
  it is @{typ term} itself.

  Patterns are a proper subset of terms, with the restriction that no abstractions may occur and
  there must be at most a single occurrence of any variable (usually known as \<^emph>\<open>linearity\<close>).
  The first restriction can be modelled in a datatype, the second cannot. Consequently, I define a
  predicate that captures both properties.

  Using linearity, many more generic properties can be proved, for example that substituting the
  environment produced by matching yields the matched term.
\<close>

fun linear :: "term \<Rightarrow> bool" where
"linear (Free _) \<longleftrightarrow> True" |
"linear (Const _) \<longleftrightarrow> True" |
"linear (t\<^sub>1 $ t\<^sub>2) \<longleftrightarrow> linear t\<^sub>1 \<and> linear t\<^sub>2 \<and> \<not> is_free t\<^sub>1 \<and> fdisjnt (frees t\<^sub>1) (frees t\<^sub>2)" |
"linear _ \<longleftrightarrow> False"

lemmas linear_simps[simp] =
  linear.simps(2)[folded const_term_def]
  linear.simps(3)[folded app_term_def]

lemma linear_implies_no_abs: "linear t \<Longrightarrow> no_abs t"
proof induction
  case Const
  then show ?case
    by (fold const_term_def free_term_def app_term_def) auto
next
  case Free
  then show ?case
    by (fold const_term_def free_term_def app_term_def) auto
next
  case App
  then show ?case
    by (fold const_term_def free_term_def app_term_def) auto
qed auto

fun linears :: "term list \<Rightarrow> bool" where
"linears [] \<longleftrightarrow> True" |
"linears (t # ts) \<longleftrightarrow> linear t \<and> fdisjnt (frees t) (freess ts) \<and> linears ts"

lemma linears_butlastI[intro]: "linears ts \<Longrightarrow> linears (butlast ts)"
proof (induction ts)
  case (Cons t ts)
  hence "linear t" "linears (butlast ts)"
    by simp+
  moreover have " fdisjnt (frees t) (freess (butlast ts))"
    proof (rule fdisjnt_subset_right)
      show "freess (butlast ts) |\<subseteq>| freess ts"
        by (rule freess_subset) (auto dest: in_set_butlastD)
    next
      show "fdisjnt (frees t) (freess ts)"
        using Cons by simp
    qed
  ultimately show ?case
    by simp
qed simp

lemma linears_appI[intro]:
  assumes "linears xs" "linears ys" "fdisjnt (freess xs) (freess ys)"
  shows "linears (xs @ ys)"
using assms proof (induction xs)
  case (Cons z zs)
  hence "linears zs"
    by simp+

  have "fdisjnt (frees z) (freess zs |\<union>| freess ys)"
    proof (rule fdisjnt_union_right)
      show "fdisjnt (frees z) (freess zs)"
        using \<open>linears (z # zs)\<close> by simp
    next
      have "frees z |\<subseteq>| freess (z # zs)"
        unfolding freess_def by simp
      thus "fdisjnt (frees z) (freess ys)"
        by (rule fdisjnt_subset_left) fact
    qed

  moreover have "linears (zs @ ys)"
    proof (rule Cons)
      show "fdisjnt (freess zs) (freess ys)"
        using Cons
        by (auto intro: freess_subset fdisjnt_subset_left)
    qed fact+

  ultimately show ?case
    using Cons by auto
qed simp

lemma linears_linear: "linears ts \<Longrightarrow> t \<in> set ts \<Longrightarrow> linear t"
by (induct ts) auto

lemma linears_singleI[intro]: "linear t \<Longrightarrow> linears [t]"
by (simp add: freess_def fdisjnt_alt_def)

lemma linear_strip_comb: "linear t \<Longrightarrow> linear (fst (strip_comb t))"
by (induction t rule: strip_comb_induct) (auto simp: split_beta)

lemma linears_strip_comb: "linear t \<Longrightarrow> linears (snd (strip_comb t))"
proof (induction t rule: strip_comb_induct)
  case (app t\<^sub>1 t\<^sub>2)
  have "linears (snd (strip_comb t\<^sub>1) @ [t\<^sub>2])"
    proof (intro linears_appI linears_singleI)
      have "freess (snd (strip_comb t\<^sub>1)) |\<subseteq>| frees t\<^sub>1"
        by (subst frees_strip_comb) auto
      moreover have "fdisjnt (frees t\<^sub>1) (frees t\<^sub>2)"
        using app by auto
      ultimately have "fdisjnt (freess (snd (strip_comb t\<^sub>1))) (frees t\<^sub>2)"
        by (rule fdisjnt_subset_left)
      thus "fdisjnt (freess (snd (strip_comb t\<^sub>1))) (freess [t\<^sub>2])"
        by simp
    next
      show "linear t\<^sub>2" "linears (snd (strip_comb t\<^sub>1))"
        using app by auto
    qed
  thus ?case
    by (simp add: split_beta)
qed auto

lemma linears_appendD:
  assumes "linears (xs @ ys)"
  shows "linears xs" "linears ys" "fdisjnt (freess xs) (freess ys)"
using assms proof (induction xs)
  case (Cons x xs)
  assume "linears ((x # xs) @ ys)"

  hence "linears (x # (xs @ ys))"
    by simp
  hence "linears (xs @ ys)" "linear x" "fdisjnt (frees x) (freess (xs @ ys))"
    by auto
  hence "linears xs"
    using Cons by simp
  moreover have "fdisjnt (frees x) (freess xs)"
    proof (rule fdisjnt_subset_right)
      show "freess xs |\<subseteq>| freess (xs @ ys)" by simp
    qed fact
  ultimately show "linears (x # xs)"
    using \<open>linear x\<close> by auto

  have "fdisjnt (freess xs) (freess ys)"
    by (rule Cons) fact
  moreover have "fdisjnt (frees x) (freess ys)"
    proof (rule fdisjnt_subset_right)
      show "freess ys |\<subseteq>| freess (xs @ ys)" by simp
    qed fact
  ultimately show "fdisjnt (freess (x # xs)) (freess ys)"
    unfolding fdisjnt_alt_def
    by auto
qed (auto simp: fdisjnt_alt_def)

lemma linear_list_comb:
  assumes "linear f" "linears xs" "fdisjnt (frees f) (freess xs)" "\<not> is_free f"
  shows "linear (list_comb f xs)"
using assms
proof (induction xs arbitrary: f)
  case (Cons x xs)

  hence *: "fdisjnt (frees f) (frees x |\<union>| freess xs)"
    by simp

  have "linear (list_comb (f $ x) xs)"
    proof (rule Cons)
      have "linear x"
        using Cons by simp
      moreover have "fdisjnt (frees f) (frees x)"
        using * by (auto intro: fdisjnt_subset_right)
      ultimately show "linear (f $ x)"
        using assms Cons by simp
    next
      show "linears xs"
        using Cons by simp
    next
      have "fdisjnt (frees f) (freess xs)"
        using * by (auto intro: fdisjnt_subset_right)
      moreover have "fdisjnt (frees x) (freess xs)"
        using Cons by simp
      ultimately show "fdisjnt (frees (f $ x)) (freess xs)"
        by (auto intro: fdisjnt_union_left)
    qed auto
  thus ?case
    by (simp add: app_term_def)
qed auto

corollary linear_list_comb': "linears xs \<Longrightarrow> linear (name $$ xs)"
by (auto intro: linear_list_comb simp: fdisjnt_alt_def)

lemma linear_strip_comb_cases[consumes 1]:
  assumes "linear pat"
  obtains (comb) s args where "strip_comb pat = (Const s, args)" "pat = s $$ args"
        | (free) s where "strip_comb pat = (Free s, [])" "pat = Free s"
using assms
proof (induction pat rule: strip_comb_induct)
  case (app t\<^sub>1 t\<^sub>2)
  show ?case
    proof (rule "app.IH")
      show "linear t\<^sub>1"
        using app by simp
    next
      fix s
      assume "strip_comb t\<^sub>1 = (Free s, [])"
      hence "t\<^sub>1 = Free s"
        by (metis fst_conv snd_conv strip_comb_empty)
      hence False
        using app by simp
      thus thesis
        by simp
    next
      fix s args
      assume "strip_comb t\<^sub>1 = (Const s, args)"
      with app show thesis
        by (fastforce simp add: strip_comb_app)
    qed
next
  case (no_app t)
  thus ?case
    by (cases t) (auto simp: const_term_def)
qed

lemma wellformed_linearI: "linear t \<Longrightarrow> wellformed' n t"
by (induct t) auto

lemma pat_cases:
  obtains (free) s where "t = Free s"
        | (comb) name args where "linears args" "t = name $$ args"
        | (nonlinear) "\<not> linear t"
proof (cases t)
  case Free
  thus thesis using free by simp
next
  case Bound
  thus thesis using nonlinear by simp
next
  case Abs
  thus thesis using nonlinear by simp
next
  case (Const name)
  have "linears []" by simp
  moreover have "t = name $$ []" unfolding Const by (simp add: const_term_def)
  ultimately show thesis
    by (rule comb)
next
  case (App u v)
  show thesis
    proof (cases "linear t")
      case False
      thus thesis using nonlinear by simp
    next
      case True
      thus thesis
        proof (cases rule: linear_strip_comb_cases)
          case free
          thus thesis using that by simp
        next
          case (comb name args)
          moreover hence "linears (snd (strip_comb t))"
            using True by (blast intro: linears_strip_comb)
          ultimately have "linears args"
            by simp
          thus thesis using that comb by simp
        qed
    qed
qed

corollary linear_pat_cases[consumes 1]:
  assumes "linear t"
  obtains (free) s where "t = Free s"
        | (comb) name args where "linears args" "t = name $$ args"
using assms
by (metis pat_cases)

lemma linear_pat_induct[consumes 1, case_names free comb]:
  assumes "linear t"
  assumes "\<And>s. P (Free s)"
  assumes "\<And>name args. linears args \<Longrightarrow> (\<And>arg. arg \<in> set args \<Longrightarrow> P arg) \<Longrightarrow> P (name $$ args)"
  shows "P t"
using wf_measure[of size] \<open>linear t\<close>
proof (induction t)
  case (less t)

  show ?case
    using \<open>linear t\<close>
    proof (cases rule: linear_pat_cases)
      case (free name)
      thus ?thesis
        using assms by simp
    next
      case (comb name args)
      show ?thesis
        proof (cases "args = []")
          case True
          thus ?thesis
            using assms comb by fastforce
        next
          case False
          show ?thesis
            unfolding \<open>t = _\<close>
            proof (rule assms)
              fix arg
              assume "arg \<in> set args"

              then have "(arg, t) \<in> measure size"
                unfolding \<open>t = _\<close>
                by (induction args) auto

              moreover have "linear arg"
                using \<open>arg \<in> set args\<close> \<open>linears args\<close>
                by (auto dest: linears_linear)

              ultimately show "P arg"
                using less by auto
            qed fact
        qed
    qed
qed

context begin

private lemma match_subst_correctness0:
  assumes "linear t"
  shows "case match t u of
          None \<Rightarrow> (\<forall>env. subst (convert_term t) env \<noteq> u) |
          Some env \<Rightarrow> subst (convert_term t) env = u"
using assms proof (induction t arbitrary: u)
  case Free
  show ?case
    unfolding match.simps
    by (fold free_term_def) auto
next
  case Const
  show ?case
    unfolding match.simps
    by (fold const_term_def) (auto split: option.splits)
next
  case (App t\<^sub>1 t\<^sub>2)
  hence linear: "linear t\<^sub>1" "linear t\<^sub>2" "fdisjnt (frees t\<^sub>1) (frees t\<^sub>2)"
    by simp+

  show ?case
    proof (cases "unapp u")
      case None
      then show ?thesis
        apply simp
        apply (fold app_term_def)
        apply simp
        using app_simps(3) is_app_def by blast
    next
      case (Some u')
      then obtain u\<^sub>1 u\<^sub>2 where u: "unapp u = Some (u\<^sub>1, u\<^sub>2)" by (cases u') auto
      hence "u = app u\<^sub>1 u\<^sub>2" by auto

      note 1 = App(1)[OF \<open>linear t\<^sub>1\<close>, of u\<^sub>1]
      note 2 = App(2)[OF \<open>linear t\<^sub>2\<close>, of u\<^sub>2]

      show ?thesis
        proof (cases "match t\<^sub>1 u\<^sub>1")
          case None
          then show ?thesis
            using u
            apply simp
            apply (fold app_term_def)
            using 1 by auto
        next
          case (Some env\<^sub>1)
          with 1 have s1: "subst (convert_term t\<^sub>1) env\<^sub>1 = u\<^sub>1" by simp
          show ?thesis
            proof (cases "match t\<^sub>2 u\<^sub>2")
              case None
              then show ?thesis
                using u
                apply simp
                apply (fold app_term_def)
                using 2 by auto
            next
              case (Some env\<^sub>2)
              with 2 have s2: "subst (convert_term t\<^sub>2) env\<^sub>2 = u\<^sub>2" by simp

              note match = \<open>match t\<^sub>1 u\<^sub>1 = Some env\<^sub>1\<close> \<open>match t\<^sub>2 u\<^sub>2 = Some env\<^sub>2\<close>

              let ?env = "env\<^sub>1 ++\<^sub>f env\<^sub>2"
              from match have "frees t\<^sub>1 = fmdom env\<^sub>1" "frees t\<^sub>2 = fmdom env\<^sub>2"
                by (auto simp: match_dom)
              with linear have "env\<^sub>1 = fmrestrict_fset (frees t\<^sub>1) ?env" "env\<^sub>2 = fmrestrict_fset (frees t\<^sub>2) ?env"
                apply auto
                apply (auto simp: fmfilter_alt_defs)
                apply (subst fmfilter_false; auto simp: fdisjnt_alt_def intro: fmdomI)+
                done
              with s1 s2 have "subst (convert_term t\<^sub>1) ?env = u\<^sub>1" "subst (convert_term t\<^sub>2) ?env = u\<^sub>2"
                using linear
                by (metis subst_restrict' convert_term_frees linear_implies_no_abs)+

              then show ?thesis
                using match unfolding \<open>u = _\<close>
                apply simp
                apply (fold app_term_def)
                by simp
            qed
        qed
    qed
qed auto

lemma match_subst_some[simp]:
  "match t u = Some env \<Longrightarrow> linear t \<Longrightarrow> subst (convert_term t) env = u"
by (metis (mono_tags) match_subst_correctness0 option.simps(5))

lemma match_subst_none:
  "match t u = None \<Longrightarrow> linear t \<Longrightarrow> subst (convert_term t) env = u \<Longrightarrow> False"
by (metis (mono_tags, lifting) match_subst_correctness0 option.simps(4))

end

(* FIXME inverse direction? *)

lemma match_matches: "match t u = Some env \<Longrightarrow> linear t \<Longrightarrow> t \<lesssim> u"
by (metis match_subst_some linear_implies_no_abs convert_term_id matchesI)

lemma overlapping_var1I: "overlapping (Free name) t"
proof (intro overlappingI matchesI)
  show "subst (Free name) (fmap_of_list [(name, t)]) = t"
    by simp
next
  show "subst t fmempty = t"
    by simp
qed

lemma overlapping_var2I: "overlapping t (Free name)"
proof (intro overlappingI matchesI)
  show "subst (Free name) (fmap_of_list [(name, t)]) = t"
    by simp
next
  show "subst t fmempty = t"
    by simp
qed

lemma non_overlapping_appI1: "non_overlapping t\<^sub>1 u\<^sub>1 \<Longrightarrow> non_overlapping (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2)"
unfolding overlapping_def matches_def by auto

lemma non_overlapping_appI2: "non_overlapping t\<^sub>2 u\<^sub>2 \<Longrightarrow> non_overlapping (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2)"
unfolding overlapping_def matches_def by auto

lemma non_overlapping_app_constI: "non_overlapping (t\<^sub>1 $ t\<^sub>2) (Const name)"
unfolding overlapping_def matches_def by simp

lemma non_overlapping_const_appI: "non_overlapping (Const name) (t\<^sub>1 $ t\<^sub>2)"
unfolding overlapping_def matches_def by simp

lemma non_overlapping_const_constI: "x \<noteq> y \<Longrightarrow> non_overlapping (Const x) (Const y)"
unfolding overlapping_def matches_def by simp

lemma match_overlapping:
  assumes "linear t\<^sub>1" "linear t\<^sub>2"
  assumes "match t\<^sub>1 u = Some env\<^sub>1" "match t\<^sub>2 u = Some env\<^sub>2"
  shows "overlapping t\<^sub>1 t\<^sub>2"
proof -
  define env\<^sub>1' where "env\<^sub>1' = (fmmap convert_term env\<^sub>1 :: (name, term) fmap)"
  define env\<^sub>2' where "env\<^sub>2' = (fmmap convert_term env\<^sub>2 :: (name, term) fmap)"
  from assms have "match t\<^sub>1 (convert_term u :: term) = Some env\<^sub>1'" "match t\<^sub>2 (convert_term u :: term) = Some env\<^sub>2'"
    unfolding env\<^sub>1'_def env\<^sub>2'_def
    by (metis convert_term_match)+
  with assms show ?thesis
    by (metis overlappingI match_matches)
qed

end