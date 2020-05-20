section \<open>Instantiation of class \<open>term\<close> for type \<open>term\<close>\<close>

theory Term
imports Term_Class
begin

instantiation "term" :: "term" begin

text \<open>
  All of these definitions need to be marked as \<open>code del\<close>; otherwise the code generator will
  attempt to generate these, which will fail because they are not executable.
\<close>

definition abs_pred_term :: "(term \<Rightarrow> bool) \<Rightarrow> term \<Rightarrow> bool" where
[code del]: "abs_pred P t \<longleftrightarrow>
  (\<forall>x. t = Bound x \<longrightarrow> P t) \<and>
  (\<forall>t'. t = \<Lambda> t' \<longrightarrow> P t' \<longrightarrow> P t)"

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    by (induction t) (auto simp: abs_pred_term_def const_term_def free_term_def app_term_def)
qed (auto simp: abs_pred_term_def)

end

lemma is_const_free[simp]: "\<not> is_const (Free name)"
unfolding is_const_def by simp

lemma is_free_app[simp]: "\<not> is_free (t $ u)"
unfolding is_free_def by simp

lemma is_free_free[simp]: "is_free (Free name)"
unfolding is_free_def by simp

lemma is_const_const[simp]: "is_const (Const name)"
unfolding is_const_def by simp

lemma list_comb_free: "is_free (list_comb f xs) \<Longrightarrow> is_free f"
apply (induction xs arbitrary: f)
apply auto
subgoal premises prems
  apply (insert prems(1)[OF prems(2)])
  unfolding app_term_def
  by simp
done

lemma const_list_comb_free[simp]: "\<not> is_free (name $$ args)"
by (fastforce dest: list_comb_free simp: const_term_def)

corollary const_list_comb_neq_free[simp]: "name $$ args \<noteq> free name'"
by (metis const_list_comb_free is_free_simps(1))

declare const_list_comb_neq_free[symmetric, simp]

lemma match_list_comb_list_comb_eq_lengths[simp]:
  assumes "length ps = length vs"
  shows "match (list_comb f ps) (list_comb g vs) =
    (case match f g of
      Some env \<Rightarrow>
        (case those (map2 match ps vs) of
          Some envs \<Rightarrow> Some (foldl (++\<^sub>f) env envs)
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
using assms
by (induction ps vs arbitrary: f g rule: list_induct2) (auto split: option.splits simp: app_term_def)

lemma matchs_match_list_comb[simp]: "match (name $$ xs) (name $$ ys) = matchs xs ys"
proof (induction xs arbitrary: ys rule: rev_induct)
  case Nil
  show ?case
    by (cases ys rule: rev_cases) (auto simp: const_term_def)
next
  case (snoc x xs)
  note snoc0 = snoc
  have "match (name $$ xs $ x) (name $$ ys) = matchs (xs @ [x]) ys"
    proof (cases ys rule: rev_cases)
      case (snoc zs z)
      show ?thesis
        unfolding snoc using snoc0
        by simp
    qed auto
  thus ?case
    by (simp add: app_term_def)
qed

fun bounds :: "term \<Rightarrow> nat fset" where
"bounds (Bound i) = {| i |}" |
"bounds (t\<^sub>1 $ t\<^sub>2) = bounds t\<^sub>1 |\<union>| bounds t\<^sub>2" |
"bounds (\<Lambda> t) = (\<lambda>i. i - 1) |`| (bounds t - {| 0 |})" |
"bounds _ = {||}"

definition shift_nat :: "nat \<Rightarrow> int \<Rightarrow> nat" where
[simp]: "shift_nat n k = (if k \<ge> 0 then n + nat k else n - nat \<bar>k\<bar>)"

fun incr_bounds :: "int \<Rightarrow> nat \<Rightarrow> term \<Rightarrow> term" where
"incr_bounds inc lev (Bound i) = (if i \<ge> lev then Bound (shift_nat i inc) else Bound i)" |
"incr_bounds inc lev (\<Lambda> u) = \<Lambda> incr_bounds inc (lev + 1) u" |
"incr_bounds inc lev (t\<^sub>1 $ t\<^sub>2) = incr_bounds inc lev t\<^sub>1 $ incr_bounds inc lev t\<^sub>2" |
"incr_bounds _ _ t = t"

lemma incr_bounds_frees[simp]: "frees (incr_bounds n k t) = frees t"
by (induction n k t rule: incr_bounds.induct) auto

lemma incr_bounds_zero[simp]: "incr_bounds 0 i t = t"
by (induct t arbitrary: i) auto

fun replace_bound :: "nat \<Rightarrow> term \<Rightarrow> term \<Rightarrow> term" where
"replace_bound lev (Bound i) t = (if i < lev then Bound i else if i = lev then incr_bounds (int lev) 0 t else Bound (i - 1))" |
"replace_bound lev (t\<^sub>1 $ t\<^sub>2) t = replace_bound lev t\<^sub>1 t $ replace_bound lev t\<^sub>2 t" |
"replace_bound lev (\<Lambda> u) t = \<Lambda> replace_bound (lev + 1) u t" |
"replace_bound _ t _ = t"

abbreviation \<beta>_reduce :: "term \<Rightarrow> term \<Rightarrow> term" ("_ [_]\<^sub>\<beta>") where
"t [u]\<^sub>\<beta> \<equiv> replace_bound 0 t u"

lemma replace_bound_frees: "frees (replace_bound n t t') |\<subseteq>| frees t |\<union>| frees t'"
by (induction n t t' rule: replace_bound.induct) auto

lemma replace_bound_eq:
  assumes "i |\<notin>| bounds t"
  shows "replace_bound i t t' = incr_bounds (-1) (i + 1) t"
using assms
by (induct t arbitrary: i) force+

fun wellformed' :: "nat \<Rightarrow> term \<Rightarrow> bool" where
"wellformed' n (t\<^sub>1 $ t\<^sub>2) \<longleftrightarrow> wellformed' n t\<^sub>1 \<and> wellformed' n t\<^sub>2" |
"wellformed' n (Bound n') \<longleftrightarrow> n' < n" |
"wellformed' n (\<Lambda> t) \<longleftrightarrow> wellformed' (n + 1) t" |
"wellformed' _ _ \<longleftrightarrow> True"

lemma wellformed_inc:
  assumes "wellformed' k t" "k \<le> n"
  shows "wellformed' n t"
using assms
by (induct t arbitrary: k n) auto

abbreviation wellformed :: "term \<Rightarrow> bool" where
"wellformed \<equiv> wellformed' 0"

lemma wellformed'_replace_bound_eq:
  assumes "wellformed' n t" "k \<ge> n"
  shows "replace_bound k t u = t"
using assms
by (induction t arbitrary: n k) auto

lemma wellformed_replace_bound_eq: "wellformed t \<Longrightarrow> replace_bound k t u = t"
by (rule wellformed'_replace_bound_eq) simp+

lemma incr_bounds_eq: "n \<ge> k \<Longrightarrow> wellformed' k t \<Longrightarrow> incr_bounds i n t = t"
by (induct t arbitrary: k n) force+

lemma incr_bounds_subst:
  assumes "\<And>t. t \<in> fmran' env \<Longrightarrow> wellformed t"
  shows "incr_bounds i n (subst t env) = subst (incr_bounds i n t) env"
proof (induction t arbitrary: n)
  case (Free name)
  show ?case
    proof (cases "fmlookup env name")
      case (Some t)
      hence "wellformed t"
        using assms by (auto intro: fmran'I)
      hence "incr_bounds i n t = t"
        by (subst incr_bounds_eq) auto
      with Some show ?thesis
        by simp
    qed auto
qed auto

lemma incr_bounds_wellformed:
  assumes "wellformed' m u"
  shows "wellformed' (k + m) (incr_bounds (int k) n u)"
using assms
by (induct u arbitrary: n m) force+

lemma replace_bound_wellformed:
  assumes "wellformed u" "wellformed' (Suc k) t" "i \<le> k"
  shows "wellformed' k (replace_bound i t u)"
using assms
apply (induction t arbitrary: i k)
apply auto
using incr_bounds_wellformed[where m = 0, simplified]
using wellformed_inc by blast

lemma subst_wellformed:
  assumes "wellformed' n t" "fmpred (\<lambda>_. wellformed) env"
  shows "wellformed' n (subst t env)"
using assms
by (induction t arbitrary: n) (auto split: option.splits intro: wellformed_inc)

global_interpretation wellformed: simple_syntactic_and "wellformed' n" for n
by standard (auto simp: app_term_def)

global_interpretation wellformed: subst_syntactic_and wellformed
by standard (auto intro: subst_wellformed)

lemma match_list_combE:
  assumes "match (name $$ xs) t = Some env"
  obtains ys where "t = name $$ ys" "matchs xs ys = Some env"
proof -
  from assms that show thesis
    proof (induction xs arbitrary: t env thesis rule: rev_induct)
      case Nil
      from Nil(1) show ?case
        apply (auto simp: const_term_def split: option.splits if_splits)
        using Nil(2)[where ys = "[]"]
        by auto
    next
      case (snoc x xs)
      obtain t' y where "t = app t' y"
        using \<open>match _ t = Some env\<close>
        by (auto simp: app_term_def elim!: option_bindE)
      from snoc(2) obtain env\<^sub>1 env\<^sub>2
        where "match (name $$ xs) t' = Some env\<^sub>1" "match x y = Some env\<^sub>2" "env = env\<^sub>1 ++\<^sub>f env\<^sub>2"
        unfolding \<open>t = _\<close> by (fastforce simp: app_term_def elim: option_bindE)

      with snoc obtain ys where "t' = name $$ ys" "matchs xs ys = Some env\<^sub>1"
        by blast

      show ?case
        proof (rule snoc(3))
          show "t = name $$ (ys @ [y])"
            unfolding \<open>t = _\<close> \<open>t' = _\<close>
            by simp
        next
          have "matchs [x] [y] = Some env\<^sub>2"
            using \<open>match x y = _\<close> by simp
          thus "matchs (xs @ [x]) (ys @ [y]) = Some env"
            unfolding \<open>env = _\<close> using \<open>matchs xs ys = _\<close>
            by simp
        qed
    qed
qed

lemma left_nesting_neq_match:
  "left_nesting f \<noteq> left_nesting g \<Longrightarrow> is_const (fst (strip_comb f)) \<Longrightarrow> match f g = None"
proof (induction f arbitrary: g)
  case (Const x)
  then show ?case
    apply (auto split: option.splits)
    apply (fold const_term_def)
    apply auto
    done
next
  case (App f1 f2)
  then have f1_g: "Suc (left_nesting f1) \<noteq> left_nesting g" and f1: "is_const (fst (strip_comb f1))"
    apply (fold app_term_def)
    by (auto split: prod.splits)
  show ?case
    proof (cases "unapp g")
      case (Some g')
      obtain g1 g2 where "g' = (g1, g2)"
        by (cases g') auto
      with Some have "g = app g1 g2"
        by auto
      with f1_g have "left_nesting f1 \<noteq> left_nesting g1"
        by simp
      with f1 App have "match f1 g1 = None"
        by simp
      then show ?thesis
        unfolding \<open>g' = _\<close> \<open>g = _\<close>
        by simp
    qed simp
qed auto

context begin

private lemma match_list_comb_list_comb_none_structure:
  assumes "length ps = length vs" "left_nesting f \<noteq> left_nesting g"
  assumes "is_const (fst (strip_comb f))"
  shows "match (list_comb f ps) (list_comb g vs) = None"
using assms
by (induction ps vs arbitrary: f g rule: list_induct2) (auto simp: split_beta left_nesting_neq_match)

lemma match_list_comb_list_comb_some:
  assumes "match (list_comb f ps) (list_comb g vs) = Some env" "left_nesting f = left_nesting g"
  assumes "is_const (fst (strip_comb f))"
  shows "match f g \<noteq> None" "length ps = length vs"
proof -
  have "match f g \<noteq> None \<and> length ps = length vs"
    proof (cases rule: linorder_cases[where y = "length vs" and x = "length ps"])
      assume "length ps = length vs"
      thus ?thesis
        using assms
        proof (induction ps vs arbitrary: f g env rule: list_induct2)
          case (Cons p ps v vs)
          have "match (app f p) (app g v) \<noteq> None \<and> length ps = length vs"
            proof (rule Cons)
              show "is_const (fst (strip_comb (app f p)))"
                using Cons by (simp add: split_beta)
            next
              show "left_nesting (app f p) = left_nesting (app g v)"
                using Cons by simp
            next
              show "match (list_comb (app f p) ps) (list_comb (app g v) vs) = Some env"
                using Cons by simp
            qed
          thus ?case
            unfolding app_term_def
            by (auto elim: match.elims option_bindE)
        qed auto
    next
      assume "length ps < length vs"
      then obtain vs\<^sub>1 vs\<^sub>2 where "vs = vs\<^sub>1 @ vs\<^sub>2" "length ps = length vs\<^sub>2" "0 < length vs\<^sub>1"
        by (auto elim: list_split)

      have "match (list_comb f ps) (list_comb (list_comb g vs\<^sub>1) vs\<^sub>2) = None"
        proof (rule match_list_comb_list_comb_none_structure)
          show "left_nesting f \<noteq> left_nesting (list_comb g vs\<^sub>1)"
            using assms(2) \<open>0 < length vs\<^sub>1\<close> by simp
        qed fact+
      hence "match (list_comb f ps) (list_comb g vs) = None"
        unfolding \<open>vs = _\<close> by simp
      hence False
        using assms by auto
      thus ?thesis ..
    next
      assume "length vs < length ps"
      then obtain ps\<^sub>1 ps\<^sub>2 where "ps = ps\<^sub>1 @ ps\<^sub>2" "length ps\<^sub>2 = length vs" "0 < length ps\<^sub>1"
        by (auto elim: list_split)

      have "match (list_comb (list_comb f ps\<^sub>1) ps\<^sub>2) (list_comb g vs) = None"
        proof (rule match_list_comb_list_comb_none_structure)
          show "left_nesting (list_comb f ps\<^sub>1) \<noteq> left_nesting g"
            using assms \<open>0 < length ps\<^sub>1\<close> by simp
        next
          show "is_const (fst (strip_comb (list_comb f ps\<^sub>1)))"
            using assms by (simp add: strip_list_comb)
        qed fact
      hence "match (list_comb f ps) (list_comb g vs) = None"
        unfolding \<open>ps = _\<close> by simp
      hence False
        using assms by auto
      thus ?thesis ..
    qed
  thus "match f g \<noteq> None" "length ps = length vs"
    by simp+
qed

end

lemma match_list_comb_list_comb_none_name[simp]:
  assumes "name \<noteq> name'"
  shows "match (name $$ ps) (name' $$ vs) = None"
proof (rule ccontr)
  assume "match (name $$ ps) (name' $$ vs) \<noteq> None"
  then obtain env where *: "match (name $$ ps) (name' $$ vs) = Some env"
    by blast
  hence "match (const name) (const name' :: 'a) \<noteq> None"
    by (rule match_list_comb_list_comb_some) (simp add: is_const_def)+
  hence "name = name'"
    unfolding const_term_def
    by (simp split: if_splits)
  thus False
    using assms by blast
qed

lemma match_list_comb_list_comb_none_length[simp]:
  assumes "length ps \<noteq> length vs"
  shows "match (name $$ ps) (name' $$ vs) = None"
proof (rule ccontr)
  assume "match (name $$ ps) (name' $$ vs) \<noteq> None"
  then obtain env where "match (name $$ ps) (name' $$ vs) = Some env"
    by blast
  hence "length ps = length vs"
    by (rule match_list_comb_list_comb_some) (simp add: is_const_def)+
  thus False
    using assms by blast
qed

context term_struct_rel begin

corollary related_matchs:
  assumes "matchs ps ts\<^sub>2 = Some env\<^sub>2" "list_all2 P ts\<^sub>1 ts\<^sub>2"
  obtains env\<^sub>1 where "matchs ps ts\<^sub>1 = Some env\<^sub>1" "P_env env\<^sub>1 env\<^sub>2"
proof -
  fix name \<comment> \<open>dummy\<close>

  from assms have "match (name $$ ps) (name $$ ts\<^sub>2) = Some env\<^sub>2"
    by simp
  moreover have "P (name $$ ts\<^sub>1) (name $$ ts\<^sub>2)"
    using assms by (auto intro: P_const_const list_combI)
  ultimately obtain env\<^sub>1 where "match (name $$ ps) (name $$ ts\<^sub>1) = Some env\<^sub>1" "P_env env\<^sub>1 env\<^sub>2"
    by (metis related_match)
  hence "matchs ps ts\<^sub>1 = Some env\<^sub>1"
    by simp

  show thesis
    by (rule that) fact+
qed

end

end