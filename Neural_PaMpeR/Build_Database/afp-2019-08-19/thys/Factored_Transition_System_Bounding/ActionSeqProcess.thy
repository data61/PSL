theory ActionSeqProcess
  imports Main "HOL-Library.Sublist" FactoredSystemLib FactoredSystem FSSublist
begin

section "Action Sequence Process"

text \<open> This section defines the preconditions satisfied predicate for action sequences and shows
relations between the execution of action sequnences and their projections some. The preconditions
satisfied predicate (`sat\_precond\_as`) states that in each recursion step, the given state and the
next action are compatible, i.e. the actions preconditions are met by the state. This is used as
premise to propositions on projections of action sequences to avoid that an invalid unprojected
sequence is suddenly valid after projection. [Abdulaziz et al., p.13] \<close>

\<comment> \<open>NOTE curried.\<close>
\<comment> \<open>NOTE 'fun' because of multiple defining equations.\<close>
fun sat_precond_as where
  "sat_precond_as s [] = True"
| "sat_precond_as s (a # as) = (fst a \<subseteq>\<^sub>f s \<and> sat_precond_as (state_succ s a) as)"


\<comment> \<open>NOTE added lemma.\<close>
lemma sat_precond_as_pair:
  "sat_precond_as s ((p, e) # as) = (p \<subseteq>\<^sub>f s \<and> sat_precond_as (state_succ s (p, e)) as)"
  by simp


\<comment> \<open>NOTE 'fun' because of multiple defining equations.\<close>
fun rem_effectless_act where
  "rem_effectless_act [] = []"
| "rem_effectless_act (a # as) = (if fmdom' (snd a) \<noteq> {}
  then (a # rem_effectless_act as)
  else rem_effectless_act as
)"


\<comment> \<open>NOTE 'fun' because of multiple defining equations.\<close>
fun no_effectless_act where
  "no_effectless_act [] = True"
| "no_effectless_act (a # as) = ((fmdom' (snd a) \<noteq> {}) \<and> no_effectless_act as)"


lemma graph_plan_lemma_4:
  fixes s s' as vs P
  assumes "(\<forall>a. (ListMem a as \<and> P a) \<longrightarrow> ((fmdom' (snd a) \<inter> vs) = {}))" "sat_precond_as s as"
    "sat_precond_as s' (filter (\<lambda>a. \<not>(P a)) as)" "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "
    (fmrestrict_set vs (exec_plan s as)
    = fmrestrict_set vs (exec_plan s' (filter (\<lambda> a. \<not>(P a)) as)))
  "
  using assms
  unfolding exec_plan.simps
proof(induction as arbitrary: s s' vs P)
  case (Cons a as)
  then have 1: "fst a \<subseteq>\<^sub>f s" "sat_precond_as (state_succ s a) as"
    by auto
  then have 2: "\<forall>a'. ListMem a' as \<and> P a' \<longrightarrow> fmdom' (snd a') \<inter> vs = {}"
    by (simp add: Cons.prems(1) insert)
  then show ?case
  proof (cases "P a")
    case True
    {
      then have "filter (\<lambda>a. \<not>(P a)) (a # as) = filter (\<lambda>a. \<not>(P a)) as"
        by simp
      then have "sat_precond_as s' (filter (\<lambda>a. \<not>(P a)) as)"
        using Cons.prems(3) True
        by argo
    }
    note a = this
    {
      then have "ListMem a (a # as)"
        using elem
        by fast
      then have "(fmdom' (snd a) \<inter> vs) = {}"
        using Cons.prems(1) True
        by blast
      then have "fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s"
        using disj_imp_eq_proj_exec[symmetric]
        by fast
    }
    then show ?thesis
      unfolding exec_plan.simps
      using Cons.prems(4) 1(2) 2 True a Cons.IH[where s="state_succ s a" and s'=s']
      by fastforce
  next
    case False
    {
      have "filter (\<lambda>a. \<not>(P a)) (a # as) = a # filter (\<lambda>a. \<not>(P a)) as"
        using False
        by auto
      then have "fst a \<subseteq>\<^sub>f s'" "sat_precond_as (state_succ s' a) (filter (\<lambda>a. \<not>(P a)) as)"
        using Cons.prems(3) False
        by force+
    }
    note b = this
    then have "fmrestrict_set vs (state_succ s a) = fmrestrict_set vs (state_succ s' a)"
      using proj_eq_proj_exec_eq
      using Cons.prems(4) 1(1)
      by blast
    then show ?thesis
      unfolding exec_plan.simps
      using 1(2) 2 False b Cons.IH[where s="state_succ s a" and s'="state_succ s' a"]
      by force
  qed
qed simp


\<comment> \<open>NOTE curried instead of triples.\<close>
\<comment> \<open>NOTE 'fun' because of multiple defining equations.\<close>
fun rem_condless_act where
  "rem_condless_act s pfx_a [] = pfx_a"
| "rem_condless_act s pfx_a (a # as) = (if fst a \<subseteq>\<^sub>f exec_plan s pfx_a
    then rem_condless_act s (pfx_a @ [a]) as
    else rem_condless_act s pfx_a as
  )"


lemma rem_condless_act_pair: "
    rem_condless_act s pfx_a ((p, e) # as) = (if p \<subseteq>\<^sub>f exec_plan s pfx_a
      then rem_condless_act s (pfx_a @ [(p,e)]) as
      else rem_condless_act s pfx_a as
    )
  "
  "(rem_condless_act s pfx_a [] = pfx_a)"
  by simp+


lemma exec_remcondless_cons:
  fixes s h as pfx
  shows "
    exec_plan s (rem_condless_act s (h # pfx) as)
    = exec_plan (state_succ s h) (rem_condless_act (state_succ s h) pfx as)
  "
  by (induction as arbitrary: s h pfx) auto


lemma rem_condless_valid_1:
  fixes as s
  shows "(exec_plan s as = exec_plan s (rem_condless_act s [] as))"
  by (induction as arbitrary: s)
    (auto simp add: exec_remcondless_cons FDOM_state_succ state_succ_def)


lemma rem_condless_act_cons:
  fixes h' pfx as s
  shows "(rem_condless_act s (h' # pfx) as) = (h' # rem_condless_act (state_succ s h') pfx as)"
  by (induction as arbitrary: h' pfx s) auto


lemma rem_condless_act_cons_prefix:
  fixes h h' as as' s
  assumes "prefix (h' # as') (rem_condless_act s [h] as)"
  shows "(
    (prefix as' (rem_condless_act (state_succ s h) [] as))
    \<and> h' = h
  )"
  using assms
proof (induction as arbitrary: h h' as' s)
  case Nil
  then have "rem_condless_act s [h] [] = [h]"
    by simp
  then have 1: "as' = []"
    using Nil.prems
    by simp
  then have "rem_condless_act (state_succ s h) [] [] = []"
    by simp
  then have 2: "prefix as' (rem_condless_act (state_succ s h) [] [])"
    using 1
    by simp
  then have "h = h'"
    using Nil.prems
    by force
  then show ?case
    using 2
    by blast
next
  case (Cons a as)
  {
    have "rem_condless_act s [h] (a # as) = h # rem_condless_act (state_succ s h) [] (a # as)"
      using rem_condless_act_cons
      by fast
    then have "h = h'"
      using Cons.prems
      by simp
  }
  moreover {
    obtain l where "(h' # as') @ l = (h # rem_condless_act (state_succ s h) [] (a # as))"
      using Cons.prems rem_condless_act_cons prefixE
      by metis
    then have "prefix (as' @ l) (rem_condless_act (state_succ s h) [] (a # as))"
      by simp
    then have "prefix as' (rem_condless_act (state_succ s h) [] (a # as))"
      using append_prefixD
      by blast
  }
  ultimately show ?case
    by fastforce
qed


lemma rem_condless_valid_2:
  fixes as s
  shows "sat_precond_as s (rem_condless_act s [] as)"
  by (induction as arbitrary: s) (auto simp: rem_condless_act_cons)


lemma rem_condless_valid_3:
  fixes as s
  shows "length (rem_condless_act s [] as) \<le> length as"
  by (induction as arbitrary: s)
    (auto simp: rem_condless_act_cons le_SucI)


lemma rem_condless_valid_4:
  fixes as A s
  assumes "(set as \<subseteq> A)"
  shows "(set (rem_condless_act s [] as) \<subseteq> A)"
  using assms
  by (induction as arbitrary: A s) (auto simp: rem_condless_act_cons)


lemma rem_condless_valid_6:
  fixes as s P
  shows "length (filter P (rem_condless_act s [] as)) \<le> length (filter P as)"
proof (induction as arbitrary: P s)
  case (Cons a as)
  then show ?case
    by (simp add: rem_condless_act_cons le_SucI)
qed simp


lemma rem_condless_valid_7:
  fixes s P as as2
  assumes "(list_all P as \<and> list_all P as2)"
  shows "list_all P (rem_condless_act s as2 as)"
  using assms
  by (induction as arbitrary: P s as2) auto


lemma rem_condless_valid_8:
  fixes s as
  shows "subseq (rem_condless_act s [] as) as"
  by (induction as arbitrary: s) (auto simp: sublist_cons_4 rem_condless_act_cons)


lemma rem_condless_valid_10:
  fixes PROB as
  assumes "as \<in> (valid_plans PROB)"
  shows "(rem_condless_act s [] as \<in> valid_plans PROB)"
  using assms valid_plans_def rem_condless_valid_1 rem_condless_valid_4
  by blast


lemma rem_condless_valid:
  fixes as A s
  assumes "(exec_plan s as = exec_plan s (rem_condless_act s [] as))"
    "(sat_precond_as s (rem_condless_act s [] as))"
    "(length (rem_condless_act s [] as) \<le> length as)"
    "((set as \<subseteq> A) \<longrightarrow> (set (rem_condless_act s [] as) \<subseteq> A))"
  shows "(\<forall>P. (length (filter P (rem_condless_act s [] as)) \<le> length (filter P as)))"
  using rem_condless_valid_1  rem_condless_valid_2 rem_condless_valid_3 rem_condless_valid_6
    rem_condless_valid_4
  by fast


\<comment> \<open>NOTE type of `as` had to be fixed for lemma submap\_imp\_state\_succ\_submap.\<close>
lemma submap_sat_precond_submap:
  fixes as :: "'a action list"
  assumes "(s1  \<subseteq>\<^sub>f s2)" "(sat_precond_as s1 as)"
  shows "(sat_precond_as s2 as)"
  using assms
proof (induction as arbitrary: s1 s2)
  case (Cons a as)
  {
    have "fst a \<subseteq>\<^sub>f s1"
      using Cons.prems(2)
      by simp
    then have "fst a \<subseteq>\<^sub>f s2"
      using Cons.prems(1) submap_imp_state_succ_submap_a
      by blast
  }
  note 1 = this
  {
    have 2: "fst a \<subseteq>\<^sub>f s1" "sat_precond_as (state_succ s1 a) as"
      using Cons.prems(2)
      by simp+
    then have "state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a"
      using Cons.prems(1) submap_imp_state_succ_submap
      by blast
    then have 3: "sat_precond_as (state_succ s2 a) as"
      using 2(2) Cons.IH
      by blast
  }
  then show ?case
    using 1
    by auto
qed auto


\<comment> \<open>NOTE added lemma.\<close>
lemma submap_init_submap_exec_i:
  fixes s1 s2
  assumes "(s1 \<subseteq>\<^sub>f s2)" "(sat_precond_as s1 (a # as))"
  shows "state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a"
  using assms
proof (cases "fst a \<subseteq>\<^sub>f s1")
  case true: True
  then show ?thesis
  proof (cases "fst a \<subseteq>\<^sub>f s2")
    case True
    then show ?thesis
      unfolding state_succ_def
      using assms submap_imp_state_succ_submap_b state_succ_def true
      by auto
  next
    case False
    then show ?thesis
      using assms submap_imp_state_succ_submap_a true
      by blast
  qed
next
  case false: False
  then show ?thesis
  proof (cases "fst a \<subseteq>\<^sub>f s2")
    case True
    then show ?thesis
      using assms false
      by auto
  next
    case False
    then show ?thesis
      unfolding state_succ_def
      using false assms
      by simp
  qed
qed

lemma submap_init_submap_exec:
  fixes s1 s2
  assumes "(s1 \<subseteq>\<^sub>f s2)" "(sat_precond_as s1 as)"
  shows "(exec_plan s1 as \<subseteq>\<^sub>f exec_plan s2 as)"
  using assms
proof (induction as arbitrary: s1 s2)
  case (Cons a as)
  have "state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a"
    using Cons.prems submap_init_submap_exec_i
    by blast
  moreover have "sat_precond_as (state_succ s1 a) as"
    using Cons.prems(2)
    by simp
  ultimately have "exec_plan (state_succ s1 a) as \<subseteq>\<^sub>f exec_plan (state_succ s2 a) as"
    using Cons.IH
    by blast
  then show ?case
    by simp
qed simp


\<comment> \<open>NOTE type of `as` had to be fixed for `submap\_sat\_precond\_submap`.\<close>
lemma sat_precond_drest_sat_precond:
  fixes vs s and as :: "'a action list"
  assumes "sat_precond_as (fmrestrict_set vs s) as"
  shows "(sat_precond_as s as)"
proof -
  have "fmrestrict_set vs s \<subseteq>\<^sub>f s"
    by simp
  then show "(sat_precond_as s as)"
    using assms submap_sat_precond_submap
    by blast
qed


\<comment> \<open>NOTE name shortened to 'varset\_action'.\<close>
definition varset_action where
  "varset_action a varset \<equiv> (fmdom' (snd a) \<subseteq> varset)"
for a :: "'a action"


lemma varset_action_pair: "(varset_action (p, e) vs) = (fmdom' e \<subseteq> vs)"
  unfolding varset_action_def
  by auto


lemma eq_effect_eq_vset:
  fixes x y
  assumes "(snd x = snd y)"
  shows "((\<lambda>a. varset_action a vs) x = (\<lambda>a. varset_action a vs) y)"
  unfolding varset_action_def
  using assms
  by presburger


lemma rem_effectless_works_1:
  fixes s as
  shows "(exec_plan s as = exec_plan s (rem_effectless_act as))"
  by (induction as arbitrary: s) (auto simp: empty_eff_exec_eq)


lemma rem_effectless_works_2:
  fixes as s
  assumes "(sat_precond_as s as)"
  shows "(sat_precond_as s (rem_effectless_act as))"
  using assms
  by (induction as arbitrary: s) (auto simp: empty_eff_exec_eq)


lemma rem_effectless_works_3:
  fixes as
  shows "length (rem_effectless_act as) \<le> length as"
  by (induction as) auto


lemma rem_effectless_works_4:
  fixes A as
  assumes "(set as \<subseteq> A)"
  shows "(set (rem_effectless_act as) \<subseteq> A)"
  using assms
  by (induction as arbitrary: A)  auto


lemma rem_effectless_works_4':
  fixes A as
  assumes "(as \<in> valid_plans A)"
  shows "(rem_effectless_act as \<in> valid_plans A)"
  using assms
  by (induction as arbitrary: A) (auto simp: valid_plans_def)


\<comment> \<open>NOTE added lemma.\<close>
lemma rem_effectless_works_5_i:
  shows "subseq (rem_effectless_act as) as"
  by (induction as) auto

lemma rem_effectless_works_5:
  fixes P as
  shows "length (filter P (rem_effectless_act as)) \<le> length (filter P as)"
  using rem_effectless_works_5_i sublist_imp_len_filter_le
  by blast


lemma rem_effectless_works_6:
  fixes as
  shows "no_effectless_act (rem_effectless_act as)"
  by (induction as) auto


lemma rem_effectless_works_7:
  fixes as
  shows "no_effectless_act as =  list_all (\<lambda>a. fmdom' (snd a) \<noteq> {}) as"
  by (induction as) auto


lemma rem_effectless_works_8:
  fixes P as
  assumes "(list_all P as)"
  shows "list_all P (rem_effectless_act as)"
  using assms
  by (induction as arbitrary: P) auto


\<comment> \<open>TODO move and replace `rem\_effectless\_works\_5\_i`.\<close>
lemma rem_effectless_works_9:
  fixes as
  shows "subseq (rem_effectless_act as) as"
  by (induction as) auto


lemma rem_effectless_works_10:
  fixes as P
  assumes "(no_effectless_act as)"
  shows "(no_effectless_act (filter P as))"
  using assms
  by (auto simp: rem_effectless_works_7) (metis Ball_set filter_set member_filter)


lemma rem_effectless_works_11:
  fixes as1 as2
  assumes "subseq as1 (rem_effectless_act as2)"
  shows "(subseq as1 as2)"
  using assms rem_effectless_works_9 sublist_trans
  by blast


lemma rem_effectless_works_12:
  fixes as1 as2
  shows "(no_effectless_act (as1 @ as2)) = (no_effectless_act as1 \<and> no_effectless_act(as2))"
  by (induction as1) auto


\<comment> \<open>TODO refactor into 'List\_Utils.thy'.\<close>
lemma rem_effectless_works_13_i:
  fixes x l
  assumes "ListMem x l" "list_all P l"
  shows "P x"
  using assms proof (induction l)
  case (insert x xs y)
  have 1: "P y"
    using insert.prems list.pred_inject
    by simp
  then have 2: "list_all P l"
    using assms(2) list.pred_inject
    by force
  then show ?case
    using 1
  proof (cases "y = x")
    case False
    then show ?thesis
      using insert 2
      by fastforce
  qed simp
qed simp

lemma rem_effectless_works_13:
  fixes as1 as2
  assumes "(subseq as1 as2)" "(no_effectless_act as2)"
  shows "(no_effectless_act as1)"
  using assms
proof (induction as1 arbitrary: as2)
  case (Cons a as1)
  {
    have "subseq as1 as2"
      using Cons.prems(1) sublist_CONS1_E
      by metis
    then have "no_effectless_act as1"
      using Cons.prems(2) Cons.IH
      by blast
  }
  moreover
  {
    have "list_all (\<lambda>a. fmdom' (snd a) \<noteq> {}) as2"
      using Cons.prems(2) rem_effectless_works_7
      by blast
    moreover have "ListMem a as2"
      using Cons.prems(1) sublist_MEM
      by fast
    ultimately have "fmdom' (snd a) \<noteq> {}"
      using rem_effectless_works_13_i
      by fastforce
  }
  ultimately show ?case
    by simp
qed simp


lemma rem_effectless_works_14:
  fixes PROB as
  shows "exec_plan s as = exec_plan s (rem_effectless_act as)"
  using rem_effectless_works_1
  by blast


lemma rem_effectless_works:
  fixes s A as
  assumes "(exec_plan s as = exec_plan s (rem_effectless_act as))"
    "(sat_precond_as s as \<longrightarrow> sat_precond_as s (rem_effectless_act as))"
    "(length (rem_effectless_act as) \<le> length as)"
    "((set as \<subseteq> A) \<longrightarrow> (set (rem_effectless_act as) \<subseteq> A))"
    "(no_effectless_act (rem_effectless_act as))"
  shows "(\<forall>P. length (filter P (rem_effectless_act as)) \<le> length (filter P as))"
  using assms rem_effectless_works_5
  by blast


\<comment> \<open>NOTE name shortened.\<close>
definition rem_effectless_act_set where
  "rem_effectless_act_set A \<equiv> {a \<in> A. fmdom' (snd a) \<noteq> {}}"


lemma rem_effectless_act_subset_rem_effectless_act_set_thm:
  fixes as A
  assumes "(set as \<subseteq> A)"
  shows "(set (rem_effectless_act as) \<subseteq> rem_effectless_act_set A)"
  unfolding rem_effectless_act_set_def
  using assms
  by (induction as) auto


lemma rem_effectless_act_set_no_empty_actions_thm:
  fixes A
  shows "rem_effectless_act_set A \<subseteq> {a. fmdom' (snd a) \<noteq> {}}"
  unfolding rem_effectless_act_set_def
  by blast


\<comment> \<open>NOTE proof required additional lemmas 'rem\_effectless\_works\_7' and 'rem\_condless\_valid\_7'.\<close>
lemma rem_condless_valid_9:
  fixes s as
  assumes "no_effectless_act as"
  shows "no_effectless_act (rem_condless_act s [] as)"
  using assms
proof (induction as arbitrary: s)
  case (Cons a as)
  then show ?case
    using Cons
  proof (cases " fst a \<subseteq>\<^sub>f exec_plan s []")
    case True
    then have "rem_condless_act s [] (a # as) = a # rem_condless_act (state_succ s a) [] as"
      using rem_condless_act_cons
      by fastforce
    moreover
    {
      have "fmdom' (snd a) \<noteq> {}"  "no_effectless_act as"
        using Cons.prems
        by simp+
      then have "no_effectless_act (rem_condless_act (state_succ s a) [] as)"
        using Cons.IH
        by blast
    }
    moreover have "no_effectless_act [a]"
      using Cons.prems
      by simp
    ultimately show ?thesis
      using rem_effectless_works_12
      by force
  qed simp
qed simp


lemma graph_plan_lemma_17:
  fixes as_1 as_2 as s
  assumes "(as_1 @ as_2 = as)" "(sat_precond_as s as)"
  shows "((sat_precond_as s as_1) \<and> sat_precond_as (exec_plan s as_1) as_2)"
  using assms
proof (induction as arbitrary: as_1 as_2 s)
  case (Cons a as)
  then show ?case proof(cases "as_1")
    case Nil
    then show ?thesis
      using Cons.prems(1, 2)
      by auto
  next
    case (Cons a list)
    then show ?thesis
      using Cons.prems(1, 2) Cons.IH hd_append2  list.distinct(1) list.sel(1, 3) tl_append2
      by auto
  qed
qed auto


lemma nempty_eff_every_nempty_act:
  fixes as
  assumes "(no_effectless_act as)" "(\<forall>x. \<not>(fmdom' (snd (f x)) = {}))"
  shows "(list_all (\<lambda>a. \<not>(f a = (fmempty, fmempty))) as)"
  using assms
proof (induction as arbitrary: f)
  case (Cons a as)
  then show ?case using fmdom'_empty snd_conv
    by (metis (mono_tags, lifting) Ball_set)
qed simp


lemma empty_replace_proj_dual7:
  fixes s as as'
  assumes "sat_precond_as s (as @ as')"
  shows "sat_precond_as (exec_plan s as) as'"
  using assms
  by (induction as arbitrary: as' s) auto


lemma not_vset_not_disj_eff_prod_dom_diff:
  fixes PROB a vs
  assumes "(a \<in> PROB)" "(\<not>varset_action a vs)"
  shows "\<not>((fmdom' (snd a) \<inter> ((prob_dom PROB) - vs)) = {})"
proof -
  have 1: "fmdom' (snd a) \<noteq> {}"
    using assms(2) varset_action_def
    by blast
  {
    have "fmdom' (snd a) \<subseteq> prob_dom PROB"
      using assms(1) FDOM_eff_subset_prob_dom_pair
      by metis
    then have "
      fmdom' (snd a) \<inter> (prob_dom PROB - vs)
      = (fmdom' (snd a)) - (fmdom' (snd a) \<inter> vs)"
      using Diff_Int_distrib
      by blast
  }
  note 2 = this
  then show ?thesis
    using 1 2
  proof (cases "fmdom' (snd a) \<inter> vs = {}")
    case False
    {
      have "\<not>(fmdom' (snd a) \<subseteq> vs)"
        using assms(2) varset_action_def
        by fast
      then have "(fmdom' (snd a) \<inter> vs \<noteq> fmdom' (snd a))"
        by auto
      then have "(fmdom' (snd a) \<inter> vs) \<subset> fmdom' (snd a)"
        by blast
    }
    then show ?thesis using 2
      by auto
  qed force
qed


lemma vset_disj_dom_eff_diff:
  fixes PROB a vs
  assumes "(varset_action a vs)"
  shows "(((fmdom' (snd a)) \<inter> (prob_dom PROB - vs)) = {})"
  using assms
  unfolding varset_action_def
  by auto


lemma vset_diff_disj_eff_vs:
  fixes PROB a vs
  assumes "(varset_action a (prob_dom PROB - vs))"
  shows "(((fmdom' (snd a)) \<inter> vs) = {})"
  using assms
  unfolding varset_action_def
  by blast


lemma vset_nempty_efff_not_disj_eff_vs:
  fixes PROB a vs
  assumes "(varset_action a vs)" "(fmdom' (snd a) \<noteq> {})"
  shows "\<not>((fmdom' (snd a) \<inter> vs)) = {}"
  using assms
  unfolding varset_action_def
  by auto


lemma vset_disj_eff_diff:
  fixes s a vs
  assumes "(varset_action a vs)"
  shows "((fmdom' (snd a) \<inter> (s - vs)) = {})"
proof -
  have 1: "fmdom' (snd a) \<subseteq> vs"
    using assms
    by (simp add: varset_action_def)
  moreover {
    have "fmdom' (snd a) \<inter> (s - vs) = (fmdom' (snd a) \<inter> s) - (fmdom' (snd a) \<inter> vs)"
      using Diff_Int_distrib
      by fast
    also have " \<dots> = (fmdom' (snd a) \<inter> s) - (fmdom' (snd a))"
      using 1
      by auto
    finally have "fmdom' (snd a) \<inter> (s - vs) = {}"
      by simp
  }
  ultimately show ?thesis
    by blast
qed


\<comment> \<open>NOTE added lemma.\<close>
lemma list_all_list_mem:
  fixes P and l :: "'a list"
  shows "list_all P l \<longleftrightarrow> (\<forall>e. ListMem e l \<longrightarrow> P e)"
proof -
  {
    assume P1: "list_all P l"
    {
      fix e
      assume P11: "ListMem e l"
      then have "P e"
        using P1 P11
      proof (induction l arbitrary: P)
        case (insert x xs y)
        then show ?case proof (cases "y = x")
          case False
          then have "list_all P xs" "ListMem x xs"
            using insert.prems(1) insert.hyps
            by fastforce+
          then show ?thesis
            using insert.IH
            by blast
        qed simp
      qed simp
    }
  }
  moreover
  {
    assume P2: "(\<forall>e. ListMem e l \<longrightarrow> P e)"
    then have "list_all P l"
    proof(induction l arbitrary: P)
      case (Cons a l)
      {
        have "\<forall>e. ListMem e l \<longrightarrow> P e"
          using Cons.prems insert
          by fast
        then have "list_all P l"
          using Cons.IH
          by blast
      }
      moreover have "P a"
        using Cons.prems elem
        by fast
      ultimately show ?case
        by simp
    qed simp
  }
  ultimately show ?thesis
    by blast
qed


lemma every_vset_imp_drestrict_exec_eq:
  fixes PROB vs as s
  assumes "(list_all (\<lambda>a. varset_action a ((prob_dom PROB) - vs)) as)"
  shows "(fmrestrict_set vs s = fmrestrict_set vs (exec_plan s as))"
proof -
  have 1: "\<forall>e. ListMem e as \<longrightarrow> varset_action e ((prob_dom PROB) - vs)"
    using assms list_all_list_mem
    by metis
  {
    fix a
    assume "ListMem a as"
    then have "varset_action a (prob_dom PROB - vs)"
      using 1
      by blast
    then have "disjnt (fmdom' (snd a)) vs"
      unfolding disjnt_def
      using vset_diff_disj_eff_vs
      by blast
  }
  then have "list_all (\<lambda>a. disjnt (fmdom' (snd a)) vs) as"
    using list_all_list_mem
    by blast
  then have "list_all (\<lambda>a. disjnt (fmdom' (snd a)) vs) (rem_condless_act s [] as)"
    by (simp add: rem_condless_valid_7)
  then have "exec_plan s as = exec_plan s (rem_condless_act s [] as)"
    using rem_condless_valid_1
    by blast
  then have"sat_precond_as s (rem_condless_act s [] as)"
    using rem_condless_valid_2
    by blast
  then have "sat_precond_as s [a\<leftarrow>as . \<not> varset_action a (prob_dom PROB - vs)]"
    by (simp add: 1 ListMem_iff)
  then have "fmrestrict_set vs s = fmrestrict_set vs s" by simp
  then have "
    fmrestrict_set vs (exec_plan s as) =
    fmrestrict_set vs (exec_plan s [a\<leftarrow>as . \<not> varset_action a (prob_dom PROB - vs)])
  "
    using 1 graph_plan_lemma_4[where
        s = s and s' = s and as = "rem_condless_act s [] as" and vs = vs and
        P = "\<lambda>a. varset_action a (prob_dom PROB - vs)"
        ] filter_empty_every_not vset_diff_disj_eff_vs 1disjoint_effects_no_effects
      exec_plan.simps(1) fmdom'_restrict_set_precise list_all_list_mem
    by smt
  then have "list_all (\<lambda>a. varset_action a (prob_dom PROB - vs)) (rem_condless_act s [] as)"
    using assms(1) rem_condless_valid_7 list.pred_inject(1)
    by blast
  then have "filter (\<lambda>a. \<not>(varset_action a (prob_dom PROB - vs))) (rem_condless_act s [] as) = []"
    using filter_empty_every_not
    by fastforce
  then have "
    sat_precond_as s (filter (\<lambda>a. \<not>(varset_action a (prob_dom PROB - vs)))
    (rem_condless_act s []as))
  "
    by fastforce
  then show ?thesis
    using 1 vset_diff_disj_eff_vs disjoint_effects_no_effects fmdom'_restrict_set_precise
    by metis
qed


lemma no_effectless_act_works:
  fixes as
  assumes "(no_effectless_act as)"
  shows "(filter (\<lambda>a. \<not>(fmdom' (snd a) = {})) as = as)"
  using assms
  by (simp add: Ball_set rem_effectless_works_7)


lemma varset_act_diff_un_imp_varset_diff:
  fixes a vs vs' vs''
  assumes "(varset_action a (vs'' -  (vs' \<union> vs)))"
  shows "(varset_action a (vs'' - vs))"
  using assms
  unfolding varset_action_def
  by blast


lemma vset_diff_union_vset_diff:
  fixes s vs vs' a
  assumes "(varset_action a (s - (vs \<union> vs')))"
  shows "(varset_action a (s - vs'))"
  using assms
  unfolding varset_action_def
  by blast


lemma valid_filter_vset_dom_idempot:
  fixes PROB as
  assumes "(as \<in> valid_plans PROB)"
  shows "(filter (\<lambda>a. varset_action a (prob_dom PROB)) as = as)"
  using assms
proof (induction as)
  case (Cons a as)
  {
    have "as \<in> valid_plans PROB"
      using Cons.prems valid_plan_valid_tail
      by fast
    then have "(filter (\<lambda>a. varset_action a (prob_dom PROB)) as = as)"
      using Cons.IH
      by blast
  }
  moreover {
    have "a \<in> PROB"
      using Cons.prems valid_plan_valid_head
      by fast
    then have "varset_action a (prob_dom PROB)"
      unfolding varset_action_def
      using FDOM_eff_subset_prob_dom_pair
      by metis
  }
  ultimately show ?case
    by simp
qed fastforce


lemma n_replace_proj_le_n_as_1:
  fixes a vs vs'
  assumes "(vs \<subseteq> vs')" "(varset_action a vs)"
  shows "(varset_action a vs')"
  using assms
  unfolding varset_action_def
  by simp


lemma sat_precond_as_pfx:
  fixes s
  assumes "(sat_precond_as s (as @ as'))"
  shows "(sat_precond_as s as)"
  using assms
proof (induction as arbitrary: s as')
  case (Cons a as)
  have "fst a \<subseteq>\<^sub>f s"
    using Cons.prems
    by fastforce
  moreover have "sat_precond_as (state_succ s a) (as @ as')"
    using Cons.prems
    by simp
  ultimately show ?case
    using Cons.IH sat_precond_as.simps(2)
    by blast
qed simp


end