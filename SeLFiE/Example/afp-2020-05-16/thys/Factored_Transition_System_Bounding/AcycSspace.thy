theory AcycSspace
  imports
    FactoredSystem
    ActionSeqProcess
    SystemAbstraction
    Acyclicity
    FmapUtils
begin


section "Acyclic State Spaces"


\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE type for `max` had to be fixed to natural number maximum (due to problem with loose
typing).\<close>
value "(state_successors (prob_proj PROB vs))"
definition S
  where "S vs lss PROB s \<equiv> wlp
    (\<lambda>x y. y \<in> (state_successors (prob_proj PROB vs) x))
    (\<lambda>s. problem_plan_bound (snapshot PROB s))
    (max :: nat \<Rightarrow> nat \<Rightarrow> nat) (\<lambda>x y. x + y + 1) s lss
  "

\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE using `fun` because of multiple defining equations.\<close>
fun vars_change where
  "vars_change [] vs s = []"
| "vars_change (a # as) vs s = (if fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s
    then state_succ s a # vars_change as vs (state_succ s a)
    else vars_change as vs (state_succ s a)
  )"


lemma vars_change_cat:
  fixes s
  shows "
    vars_change (as1 @ as2) vs s
    = (vars_change as1 vs s @ vars_change as2 vs (exec_plan s as1))
  "
  by (induction as1 arbitrary: s as2 vs) auto


lemma empty_change_no_change:
  fixes s
  assumes "(vars_change as vs s = [])"
  shows "(fmrestrict_set vs (exec_plan s as) = fmrestrict_set vs s)"
  using assms
proof (induction as arbitrary: s vs)
  case (Cons a as)
  then show ?case
  proof (cases "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s")
    case True
      \<comment> \<open>NOTE This case violates the induction premise @{term "vars_change (a # as) vs s = []"} since the
        empty list is impossible.\<close>
    then have "state_succ s a # vars_change as vs (state_succ s a) = []"
      using Cons.prems True
      by simp
    then show "fmrestrict_set vs (exec_plan s (a # as)) = fmrestrict_set vs s"
      by blast
  next
    case False
    then have "vars_change as vs (state_succ s a) = []"
      using Cons.prems False
      by force
    then have
      "fmrestrict_set vs (exec_plan (state_succ s a) as) = fmrestrict_set vs (state_succ s a)"
      using Cons.IH[of vs "(state_succ s a)"]
      by blast
    then show "fmrestrict_set vs (exec_plan s (a # as)) = fmrestrict_set vs s"
      using False
      by simp
  qed
qed auto


\<comment> \<open>NOTE renamed variable `a` to `b` to not conflict with naming for list head in induction step.\<close>
lemma zero_change_imp_all_effects_submap:
  fixes s s'
  assumes "(vars_change as vs s = [])" "(sat_precond_as s as)" "(ListMem b as)"
    "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "(fmrestrict_set vs (snd b) \<subseteq>\<^sub>f fmrestrict_set vs s')"
  using assms
proof (induction as arbitrary: s s' vs b)
  case (Cons a as)
    \<comment> \<open>NOTE Having either @{term "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s"} or
    @{term "\<not>ListMem b as"} leads to simpler propositions so we split here.\<close>
  then show "(fmrestrict_set vs (snd b) \<subseteq>\<^sub>f fmrestrict_set vs s')"
    using Cons.prems(1)
  proof (cases "fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s \<and> ListMem b as")
    case True
    let ?s="state_succ s a"
    have "vars_change as vs ?s = []"
      using True Cons.prems(1)
      by auto
    moreover have "sat_precond_as ?s as"
      using Cons.prems(2) sat_precond_as.simps(2)
      by blast
    ultimately show ?thesis
      using True Cons.prems(4) Cons.IH
      by auto
  next
    case False
    then consider
      (i) "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s"
      | (ii) "\<not>ListMem b as"
      by blast
    then show ?thesis
      using Cons.prems(1)
    proof (cases)
      case ii
      then have "a = b"
        using Cons.prems(3) ListMem_iff set_ConsD
        by metis
          \<comment> \<open>NOTE Mysteriously sledgehammer finds a proof here while the premises of
            `no\_change\_vs\_eff\_submap` cannot be proven individually.\<close>
      then show ?thesis
        using Cons.prems(1, 2, 4) no_change_vs_eff_submap
        by (metis list.distinct(1) sat_precond_as.simps(2) vars_change.simps(2))
    qed simp
  qed
qed (simp add: ListMem_iff)


lemma zero_change_imp_all_preconds_submap:
  fixes s s'
  assumes "(vars_change as vs s = [])" "(sat_precond_as s as)" "(ListMem b as)"
    "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "(fmrestrict_set vs (fst b) \<subseteq>\<^sub>f fmrestrict_set vs s')"
  using assms
proof (induction as arbitrary: vs s s')
  case (Cons a as)
    \<comment> \<open>NOTE Having either @{term "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s"} or
    @{term "\<not>ListMem b as"} leads to simpler propositions so we split here.\<close>
  then show "(fmrestrict_set vs (fst b) \<subseteq>\<^sub>f fmrestrict_set vs s')"
    using Cons.prems(1)
  proof (cases "fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s \<and> ListMem b as")
    case True
    let ?s="state_succ s a"
    have "vars_change as vs ?s = []"
      using True Cons.prems(1)
      by auto
    moreover have "sat_precond_as ?s as"
      using Cons.prems(2) sat_precond_as.simps(2)
      by blast
    ultimately show ?thesis
      using True Cons.prems(4) Cons.IH
      by auto
  next
    case False
    then consider
      (i) "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s"
      | (ii) "\<not>ListMem b as"
      by blast
    then show ?thesis
      using Cons.prems(1)
    proof (cases)
      case ii
      then have "a = b"
        using Cons.prems(3) ListMem_iff set_ConsD
        by metis
      then show ?thesis
        using Cons.prems(2, 4) fmsubset_restrict_set_mono
        by (metis sat_precond_as.simps(2))
    qed simp
  qed
qed (simp add: ListMem_iff)


lemma no_vs_change_valid_in_snapshot:
  assumes "(as \<in> valid_plans PROB)" "(sat_precond_as s as)" "(vars_change as vs s = [])"
  shows "(as \<in> valid_plans (snapshot PROB (fmrestrict_set vs s)))"
proof -
  {
    fix a
    assume P: "ListMem a as"
    then have "agree (fst a) (fmrestrict_set vs s)"
      by (metis agree_imp_submap assms(2) assms(3) fmdom'_restrict_set
          restricted_agree_imp_agree zero_change_imp_all_preconds_submap)
    moreover have "agree (snd a) (fmrestrict_set vs s)"
      by (metis (no_types) P agree_imp_submap assms(2) assms(3) fmdom'_restrict_set
          restricted_agree_imp_agree zero_change_imp_all_effects_submap)
    ultimately have "agree (fst a) (fmrestrict_set vs s)" "agree (snd a) (fmrestrict_set vs s)"
      by simp+
  }
  then show ?thesis
    using assms(1) as_mem_agree_valid_in_snapshot
    by blast
qed


\<comment> \<open>NOTE type of `PROB` had to be fixed for `problem\_plan\_bound\_works`.\<close>
lemma no_vs_change_obtain_snapshot_bound_1st_step:
  fixes PROB :: "'a problem"
  assumes "finite PROB" "(vars_change as vs s = [])" "(sat_precond_as s as)"
    "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (
      exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as
      = exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as'
    )
    \<and> (subseq as' as)
    \<and> (length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s)))
  )"
proof -
  let ?s="(fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s)"
  let ?PROB="(snapshot PROB (fmrestrict_set vs s))"
  {
    have "finite (snapshot PROB (fmrestrict_set vs s))"
      using assms(1) FINITE_snapshot
      by blast
  }
  moreover {
    have "
      fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s
      \<in> valid_states (snapshot PROB (fmrestrict_set vs s))"
      using assms(4) graph_plan_not_eq_last_diff_paths valid_states_snapshot
      by blast
  }
  moreover {
    have "as \<in> valid_plans (snapshot PROB (fmrestrict_set vs s))"
      using assms(2, 3, 5) no_vs_change_valid_in_snapshot
      by blast
  }
  ultimately show ?thesis
    using problem_plan_bound_works[of ?PROB ?s as]
    by blast
qed


\<comment> \<open>NOTE type of `PROB` had to be fixed for `no\_vs\_change\_obtain\_snapshot\_bound\_1st\_step`.\<close>
lemma no_vs_change_obtain_snapshot_bound_2nd_step:
  fixes PROB :: "'a problem"
  assumes "finite PROB" "(vars_change as vs s = [])" "(sat_precond_as s as)"
    "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (
      exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s)))  s) as
      = exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as'
    )
    \<and> (subseq as' as)
    \<and> (sat_precond_as s as')
    \<and> (length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s)))
  )"
proof -
  obtain as'' where 1:
    "
      exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as
      = exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as''"
    "subseq as'' as" "length as'' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
    using assms no_vs_change_obtain_snapshot_bound_1st_step
    by blast
  let ?s'="(fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s)"
  let ?as'="rem_condless_act ?s' [] as''"
  have "exec_plan ?s' as = exec_plan ?s' as''"
    using 1(1) rem_condless_valid_1
    by blast
  moreover have "subseq ?as' as"
    using 1(2) rem_condless_valid_8 sublist_trans
    by blast
  moreover have "sat_precond_as s ?as'"
    using sat_precond_drest_sat_precond rem_condless_valid_2
    by fast
  moreover have "(length ?as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s)))"
    using 1 rem_condless_valid_3 le_trans
    by blast
  ultimately show ?thesis
    using 1 rem_condless_valid_1
    by auto
qed


lemma no_vs_change_obtain_snapshot_bound_3rd_step:
  assumes "finite (PROB :: 'a problem)" "(vars_change as vs s = [])" "(no_effectless_act as)"
    "(sat_precond_as s as)" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (
      fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as)
      = fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as')
    )
    \<and> (subseq as' as)
    \<and> (length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s)))
  )"
proof -
  obtain as' :: "(('a, bool) fmap \<times> ('a, bool) fmap) list" where
    "(
      exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as
      = exec_plan (fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) s) as'
    )" "subseq as' as" "sat_precond_as s as'"
    "length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
    using assms(1, 2, 4, 5, 6) no_vs_change_obtain_snapshot_bound_2nd_step
    by blast
  moreover have
    "exec_plan (fmrestrict_set vs s) (as_proj as vs) = fmrestrict_set vs (exec_plan s as)"
    using assms(4) sat_precond_exec_as_proj_eq_proj_exec
    by blast
  moreover have "as_proj as (prob_dom (snapshot PROB (fmrestrict_set vs s))) = as"
    using assms(2, 3, 4, 6) as_proj_eq_as no_vs_change_valid_in_snapshot
    by blast
  ultimately show ?thesis
    using sublist_as_proj_eq_as proj_exec_proj_eq_exec_proj'
    by metis
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO remove unused assumptions.\<close>
lemma no_vs_change_snapshot_s_vs_is_valid_bound_i:
  fixes PROB :: "'a problem"
  assumes  "finite PROB" "(vars_change as vs s = [])" "(no_effectless_act as)"
    "(sat_precond_as s as)" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as) =
        fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as')"
    "subseq as' as" "length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
  shows
    "fmrestrict_set (fmdom' (exec_plan s as) - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        (exec_plan s as)
      = fmrestrict_set (fmdom' (exec_plan s as) - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        s
    \<and> fmrestrict_set (fmdom' (exec_plan s as') - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        (exec_plan s as')
      = fmrestrict_set (fmdom' (exec_plan s as') - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        s"
proof -
  let ?vs="(prob_dom (snapshot PROB (fmrestrict_set vs s)))"
  let ?vs'="(fmdom' (exec_plan s as) - prob_dom (snapshot PROB (fmrestrict_set vs s)))"
  let ?vs''="(fmdom' (exec_plan s as') - prob_dom (snapshot PROB (fmrestrict_set vs s)))"
  let ?s="(exec_plan s as)"
  let ?s'="(exec_plan s as')"
  have 1: "as \<in> valid_plans (snapshot PROB (fmrestrict_set vs s))"
    using assms(2, 4, 6) no_vs_change_valid_in_snapshot
    by blast
  {
    {
      fix a
      assume "ListMem a as"
      then have "fmdom' (snd a) \<subseteq> prob_dom (snapshot PROB (fmrestrict_set vs s))"
        using 1 FDOM_eff_subset_prob_dom_pair valid_plan_mems
        by metis
      then have "fmdom' (fmrestrict_set (fmdom' (exec_plan s as)
          - prob_dom (snapshot PROB (fmrestrict_set vs s))) (snd a))
        = {}"
        using subset_inter_diff_empty[of "fmdom' (snd a)"
            "prob_dom (snapshot PROB (fmrestrict_set vs s))"] fmdom'_restrict_set_precise
        by metis
    }
    then have
      "fmrestrict_set ?vs' (exec_plan s as) = fmrestrict_set ?vs' s"
      using disjoint_effects_no_effects[of as ?vs' s]
      by blast
  }
  moreover {
    {
      fix a
      assume P: "ListMem a as'"
      moreover have \<alpha>: "as' \<in> valid_plans (snapshot PROB (fmrestrict_set vs s))"
        using assms(8) 1 sublist_valid_plan
        by blast
      moreover have "a \<in> PROB"
        using P \<alpha> snapshot_subset subsetCE valid_plan_mems
        by fast
      ultimately have "fmdom' (snd a) \<subseteq> prob_dom (snapshot PROB (fmrestrict_set vs s))"
        using FDOM_eff_subset_prob_dom_pair valid_plan_mems
        by metis
      then have "fmdom' (fmrestrict_set (fmdom' (exec_plan s as')
          - prob_dom (snapshot PROB (fmrestrict_set vs s))) (snd a))
        = {}"
        using subset_inter_diff_empty[of "fmdom' (snd a)"
            "prob_dom (snapshot PROB (fmrestrict_set vs s))"] fmdom'_restrict_set_precise
        by metis
    }
    then have
      "fmrestrict_set ?vs'' (exec_plan s as') = fmrestrict_set ?vs'' s"
      using disjoint_effects_no_effects[of as' ?vs'' s]
      by blast
  }
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>NOTE type for `PROB` had to be fixed.\<close>
lemma no_vs_change_snapshot_s_vs_is_valid_bound:
  fixes PROB :: "'a problem"
  assumes "finite PROB" "(vars_change as vs s = [])" "(no_effectless_act as)"
    "(sat_precond_as s as)" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (exec_plan s as = exec_plan s as')
    \<and> (subseq as' as)
    \<and> (length as' <= problem_plan_bound (snapshot PROB (fmrestrict_set vs s)))
  )"
proof -
  obtain as' where 1:
    "fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as) =
      fmrestrict_set (prob_dom (snapshot PROB (fmrestrict_set vs s))) (exec_plan s as')"
    "subseq as' as" "length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
    using assms no_vs_change_obtain_snapshot_bound_3rd_step
    by blast
  {

    have a: "fmrestrict_set (fmdom' (exec_plan s as) - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        (exec_plan s as)
      = fmrestrict_set (fmdom' (exec_plan s as) - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        s "
      "fmrestrict_set (fmdom' (exec_plan s as') - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        (exec_plan s as')
      = fmrestrict_set (fmdom' (exec_plan s as') - prob_dom (snapshot PROB (fmrestrict_set vs s)))
        s"
      using assms 1 no_vs_change_snapshot_s_vs_is_valid_bound_i
      by blast+
    moreover have "as' \<in> valid_plans (snapshot PROB (fmrestrict_set vs s))"
      using "1"(2) assms(2) assms(4) assms(6) no_vs_change_valid_in_snapshot sublist_valid_plan
      by blast
    moreover have "(exec_plan s as) \<in> valid_states PROB"
      using assms(5, 6) valid_as_valid_exec
      by blast
    moreover have "(exec_plan s as') \<in> valid_states PROB"
      using assms(5, 6) 1 valid_as_valid_exec sublist_valid_plan
      by blast
    ultimately have "exec_plan s as = exec_plan s as'"
      using assms
      unfolding valid_states_def
      using graph_plan_lemma_5[where vs="prob_dom (snapshot PROB (fmrestrict_set vs s))", OF _ 1(1)]
      by force
  }
  then show ?thesis
    using 1
    by blast
qed


\<comment> \<open>TODO showcase (problems with stronger typing: Isabelle requires strict typing for `max`; whereas
in HOL4 this is not required, possible because 'MAX' is natural number specific.\<close>
lemma snapshot_bound_leq_S:
  shows "
    problem_plan_bound (snapshot PROB (fmrestrict_set vs s))
    \<le> S vs lss PROB (fmrestrict_set vs s)
  "
proof -
  have "geq_arg (max :: nat \<Rightarrow> nat \<Rightarrow> nat)"
    unfolding geq_arg_def
    using max.cobounded1
    by simp
  then show ?thesis
    unfolding S_def
    using individual_weight_less_eq_lp[where
        g="max :: nat \<Rightarrow> nat \<Rightarrow> nat"
        and x="(fmrestrict_set vs s)" and R="(\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x)"
        and w="(\<lambda>s. problem_plan_bound (snapshot PROB s))" and f="(\<lambda>x y. x + y + 1)" and l=lss]
    by blast
qed


\<comment> \<open>NOTE first argument of `top\_sorted\_abs` had to be wrapped into lambda.\<close>
\<comment> \<open>NOTE the type of `1` had to be restricted to `nat` to ensure the proofs for `geq\_arg` work.\<close>
lemma S_geq_S_succ_plus_ell:
  assumes "(s \<in> valid_states PROB)"
    "(top_sorted_abs (\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x) lss)"
    "(s' \<in> state_successors (prob_proj PROB vs) s)" "(set lss = valid_states (prob_proj PROB vs))"
  shows "(
    problem_plan_bound (snapshot PROB (fmrestrict_set vs s))
      + S vs lss PROB (fmrestrict_set vs s')
      + (1 :: nat)
    \<le> S vs lss PROB (fmrestrict_set vs s)
  )"
proof -
  let ?f="\<lambda>x y. x + y + (1 :: nat)"
  let ?R="(\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x)"
  let ?w="(\<lambda>s. problem_plan_bound (snapshot PROB s))"
  let ?g="max :: nat \<Rightarrow> nat \<Rightarrow> nat"
  let ?vtx1="(fmrestrict_set vs s')"
  let ?G="lss"
  let ?vtx2="(fmrestrict_set vs s)"
  have "geq_arg ?f"
    unfolding geq_arg_def
    by simp
  moreover have "geq_arg ?g"
    unfolding geq_arg_def
    by simp
  moreover have "\<forall>x. ListMem x lss \<longrightarrow> \<not>?R x x"
    unfolding state_successors_def
    by blast
  moreover have "?R ?vtx2 ?vtx1"
    unfolding state_successors_def
    using assms(3) state_in_successor_proj_in_state_in_successor state_successors_def
    by blast
  moreover have
    "ListMem ?vtx1 ?G"
    using assms(1, 3, 4)
    by (metis ListMem_iff contra_subsetD graph_plan_not_eq_last_diff_paths proj_successors_of_valid_are_valid)
  moreover have "top_sorted_abs ?R ?G"
    using assms(2)
    by simp
  ultimately show ?thesis
    unfolding S_def
    using lp_geq_lp_from_successor[of ?f ?g ?G ?R ?vtx2 ?vtx1 ?w]
    by blast
qed


lemma vars_change_cons:
  fixes s s'
  assumes "(vars_change as vs s = (s' # ss))"
  shows "(\<exists>as1 act as2.
    (as = as1 @ (act # as2))
    \<and> (vars_change as1 vs s = [])
    \<and> (state_succ (exec_plan s as1) act = s')
    \<and> (vars_change as2 vs (state_succ (exec_plan s as1) act) = ss)
  )"
  using assms
proof (induction as arbitrary: s s' vs ss)
  case (Cons a as)
  then show ?case
  proof (cases "fmrestrict_set vs (state_succ s a) \<noteq> fmrestrict_set vs s")
    case True
    then have "state_succ s a = s'" "vars_change as vs (state_succ s a) = ss"
      using Cons.prems
      by simp+
    then show ?thesis
      by fastforce
  next
    case False
    then have "vars_change as vs (state_succ s a) = s' # ss"
      using Cons.prems
      by simp
    then obtain as1 act as2 where
      "as = as1 @ act # as2" "vars_change as1 vs (state_succ s a) = []"
      "state_succ (exec_plan (state_succ s a) as1) act = s'"
      "vars_change as2 vs (state_succ (exec_plan (state_succ s a) as1) act) = ss"
      using Cons.IH
      by blast
    then show ?thesis
      by (metis False append_Cons exec_plan.simps(2) vars_change.simps(2))
  qed
qed simp


lemma vars_change_cons_2:
  fixes s s'
  assumes "(vars_change as vs s = (s' # ss))"
  shows "(fmrestrict_set vs s' \<noteq> fmrestrict_set vs s)"
  using assms
  apply(induction as arbitrary: s s' vs ss)
  apply(auto)
  by (metis list.inject)


\<comment> \<open>NOTE first argument of `top\_sorted\_abs had to be wrapped into lambda.\<close>
lemma problem_plan_bound_S_bound_1st_step:
  fixes PROB :: "'a problem"
  assumes "finite PROB" "(top_sorted_abs (\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x) lss)"
    "(set lss = valid_states (prob_proj PROB vs))" "(s \<in> valid_states PROB)"
    "(as \<in> valid_plans PROB)" "(no_effectless_act as)" "(sat_precond_as s as)"
  shows "(\<exists>as'.
      (exec_plan s as' = exec_plan s as)
      \<and> (subseq as' as)
      \<and> (length as' <= S vs lss PROB (fmrestrict_set vs s))
    )"
  using assms
proof (induction "vars_change as vs s" arbitrary: PROB as vs s lss)
  case Nil
  then obtain as' where
    "exec_plan s as = exec_plan s as'" "subseq as' as"
    "length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
    using Nil(1) Nil.prems(1,4,5,6,7) no_vs_change_snapshot_s_vs_is_valid_bound
    by metis
  moreover have "
      problem_plan_bound (snapshot PROB (fmrestrict_set vs s))
      \<le> S vs lss PROB (fmrestrict_set vs s)
    "
    using snapshot_bound_leq_S le_trans
    by fast
  ultimately show ?case
    using le_trans
    by fastforce
next
  case (Cons s' ss)
  then obtain as1 act as2 where 1:
    "as = as1 @ act # as2" "vars_change as1 vs s = []" "state_succ (exec_plan s as1) act = s'"
    "vars_change as2 vs (state_succ (exec_plan s as1) act) = ss"
    using vars_change_cons
    by smt
  text\<open> Obtain conclusion of induction hypothesis for 'as2' and
      '(state\_succ (exec\_plan s as1) act)'. \<close>
  {
    {
      have "as1 \<in> valid_plans PROB"
        using Cons.prems(5) 1(1) valid_append_valid_pref
        by blast
      moreover have "act \<in> PROB"
        using Cons.prems(5) 1 valid_append_valid_suff valid_plan_valid_head
        by fast
      ultimately have "state_succ (exec_plan s as1) act \<in> valid_states PROB"
        using Cons.prems(4) valid_as_valid_exec lemma_1_i
        by blast
    }
    moreover have "as2 \<in> valid_plans PROB"
      using Cons.prems(5) 1(1) valid_append_valid_suff valid_plan_valid_tail
      by fast
    moreover have "no_effectless_act as2"
      using Cons.prems(6) 1(1) rem_effectless_works_13 sublist_append_back
      by blast
    moreover have "sat_precond_as (state_succ (exec_plan s as1) act) as2"
      using Cons.prems(7) 1(1) graph_plan_lemma_17 sat_precond_as.simps(2)
      by blast
    ultimately have "\<exists>as'.
          exec_plan (state_succ (exec_plan s as1) act) as'
          = exec_plan (state_succ (exec_plan s as1) act) as2
        \<and> subseq as' as2
        \<and> length as' \<le> S vs lss PROB (fmrestrict_set vs (state_succ (exec_plan s as1) act))"
      using Cons.prems(1, 2, 3) 1(4)
        Cons(1)[where as="as2" and s="(state_succ (exec_plan s as1) act)"]
      by blast
  }
  note a=this
  {
    have "no_effectless_act as1"
      using Cons.prems(6) 1(1) rem_effectless_works_12
      by blast
    moreover have "sat_precond_as s as1"
      using Cons.prems(7) 1(1) sat_precond_as_pfx
      by blast
    moreover have "as1 \<in> valid_plans PROB"
      using Cons.prems(5) 1(1) valid_append_valid_pref
      by blast
    ultimately have "\<exists>as'. exec_plan s as1 = exec_plan s as' \<and>
        subseq as' as1 \<and> length as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
      using no_vs_change_snapshot_s_vs_is_valid_bound[of _ as1]
      using Cons.prems(1, 4) 1(2)
      by blast
  }
  then obtain as'' where b:
    "exec_plan s as1 = exec_plan s as''" "subseq as'' as1"
    "length as'' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))"
    by blast
  {
    obtain as' where i:
      "exec_plan (state_succ (exec_plan s as1) act) as'
          = exec_plan (state_succ (exec_plan s as1) act) as2"
      "subseq as' as2"
      "length as' \<le> S vs lss PROB (fmrestrict_set vs (state_succ (exec_plan s as1) act))"
      using a
      by blast
    let ?as'="as'' @ act # as'"
    have "exec_plan s ?as' = exec_plan s as"
      using 1(1) b(1) i(1) exec_plan_Append exec_plan.simps(2)
      by metis
    moreover have "subseq ?as' as"
      using 1(1) b(2) i(2) subseq_append_iff
      by blast
    moreover
    {
      {
        \<comment> \<open>NOTE this is proved earlier in the original proof script. Moved here to improve
            transparency.\<close>
        have "sat_precond_as (exec_plan s as1) (act # as2)"
          using empty_replace_proj_dual7
          using 1(1) Cons.prems(7)
          by blast
        then have "fst act \<subseteq>\<^sub>f (exec_plan s as1)"
          by simp
      }
      note A = this
      {
        have
          "fmrestrict_set vs (state_succ (exec_plan s as1) act)
              = (state_succ (fmrestrict_set vs (exec_plan s as'')) (action_proj act vs))"
          using b(1) A drest_succ_proj_eq_drest_succ[where s="exec_plan s as1", symmetric]
          by simp
        also have "\<dots> = (state_succ (fmrestrict_set vs s) (action_proj act vs))"
          using 1(2) b(1) empty_change_no_change
          by fastforce
        finally have "\<dots> = fmrestrict_set  vs (state_succ s (action_proj act vs))"
          using  succ_drest_eq_drest_succ
          by blast
      }
      note B = this
      have C: "fmrestrict_set vs (exec_plan s as'') = fmrestrict_set vs s"
        using 1(2) b(1) empty_change_no_change
        by fastforce
      {
        have "act \<in> PROB"
          using Cons.prems(5) 1 valid_append_valid_suff valid_plan_valid_head
          by fast
        then have \<aleph>: "action_proj act vs \<in> prob_proj PROB vs"
          using action_proj_in_prob_proj
          by blast
        then have "(state_succ s (action_proj act vs)) \<in> (state_successors (prob_proj PROB vs) s)"
        proof (cases "fst (action_proj act vs) \<subseteq>\<^sub>f s")
          case True
          then show ?thesis
            unfolding state_successors_def
            using Cons.hyps(2) 1(3) b(1) A B C \<aleph> DiffI imageI singletonD vars_change_cons_2
              drest_succ_proj_eq_drest_succ
            by metis
        next
          case False
          then show ?thesis
            unfolding state_successors_def
            using Cons.hyps(2) 1(3) b(1) A B C \<aleph> DiffI imageI singletonD
              drest_succ_proj_eq_drest_succ vars_change_cons_2
            by metis
        qed
      }
      then have D:
        "problem_plan_bound (snapshot PROB (fmrestrict_set vs s))
                + S vs lss PROB (fmrestrict_set vs (state_succ s (action_proj act vs)))
                + 1
              \<le> S vs lss PROB (fmrestrict_set vs s)"
        using Cons.prems(2, 3, 4) S_geq_S_succ_plus_ell[where s'="state_succ s (action_proj act vs)"]
        by blast
      {
        have
          "length ?as' \<le> problem_plan_bound (snapshot PROB (fmrestrict_set vs s))
                + 1 + S vs lss PROB (fmrestrict_set vs (state_succ (exec_plan s as1) act))"
          using b i
          by fastforce
        then have "length ?as' \<le> S vs lss PROB (fmrestrict_set vs s)"
          using b(1) A B C D drest_succ_proj_eq_drest_succ
          by (smt Suc_eq_plus1 add_Suc dual_order.trans)
      }
    }
    ultimately have ?case
      by blast
  }
  then show ?case
    by blast
qed


\<comment> \<open>NOTE first argument of `top\_sorted\_abs` had to be wrapped into lambda.\<close>
lemma problem_plan_bound_S_bound_2nd_step:
  assumes "finite (PROB :: 'a problem)"
    "(top_sorted_abs (\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x) lss)"
    "(set lss = valid_states (prob_proj PROB vs))" "(s \<in> valid_states PROB)"
    "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (exec_plan s as' = exec_plan s as)
    \<and> (subseq as' as)
    \<and> (length as' \<le> S vs lss PROB (fmrestrict_set vs s))
  )"
proof -
  \<comment> \<open>NOTE Proof premises and obtain conclusion of `problem\_plan\_bound\_S\_bound\_1st\_step`.\<close>
  {
    have a: "rem_condless_act s [] (rem_effectless_act as) \<in> valid_plans PROB"
      using assms(5) rem_effectless_works_4' rem_condless_valid_10
      by blast
    then have b: "no_effectless_act (rem_condless_act s [] (rem_effectless_act as))"
      using assms rem_effectless_works_6 rem_condless_valid_9
      by fast
    then have "sat_precond_as s (rem_condless_act s [] (rem_effectless_act as))"
      using assms rem_condless_valid_2
      by blast
    then have "\<exists>as'.
      exec_plan s as' = exec_plan s (rem_condless_act s [] (rem_effectless_act as))
      \<and> subseq as' (rem_condless_act s [] (rem_effectless_act as))
      \<and> length as' \<le> S vs lss PROB (fmrestrict_set vs s)
    "
      using assms a b problem_plan_bound_S_bound_1st_step
      by blast
  }
  then obtain as' where 1:
    "exec_plan s as' = exec_plan s (rem_condless_act s [] (rem_effectless_act as))"
    "subseq as' (rem_condless_act s [] (rem_effectless_act as))"
    "length as' \<le> S vs lss PROB (fmrestrict_set vs s)"
    by blast
  then have 2: "exec_plan s as' = exec_plan s as"
    using rem_condless_valid_1 rem_effectless_works_14
    by metis
  then have "subseq as' as"
    using 1(2) rem_condless_valid_8 rem_effectless_works_9 sublist_trans
    by metis
  then show ?thesis
    using 1(3) 2
    by blast
qed


\<comment> \<open>NOTE first argument of `top\_sorted\_abs` had to be wrapped into lambda.\<close>
lemma S_in_MPLS_leq_2_pow_n:
  assumes "finite (PROB :: 'a problem)"
    "(top_sorted_abs (\<lambda> x y. y \<in> state_successors (prob_proj PROB vs) x) lss)"
    "(set lss = valid_states (prob_proj PROB vs))" "(s \<in> valid_states PROB)"
    "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
      (exec_plan s as' = exec_plan s as)
      \<and> (subseq as' as)
      \<and> (length as' \<le> Sup {S vs lss PROB s' | s'. s' \<in> valid_states (prob_proj PROB  vs)})
    )"
proof -
  obtain as' where
    "exec_plan s as' = exec_plan s as" "subseq as' as"
    "length as' \<le> S vs lss PROB (fmrestrict_set vs s)"
    using assms problem_plan_bound_S_bound_2nd_step
    by blast
  moreover {
    \<comment> \<open>NOTE Derive sufficient conditions for inferring that `S vs lss PROB` is smaller or equal to
    the supremum of the set @{term "{S vs lss PROB s' | s'. s' \<in> valid_states (prob_proj PROB vs)}"}: i.e.
    being contained and that the supremum is contained as well.\<close>
    let ?S="{S vs lss PROB s' | s'. s' \<in> valid_states (prob_proj PROB vs)}"
    {
      have "fmrestrict_set vs s \<in> valid_states (prob_proj PROB vs)"
        using assms(4) graph_plan_not_eq_last_diff_paths
        by blast
      then have "S vs lss PROB (fmrestrict_set vs s) \<in> ?S"
        using calculation(1)
        by blast
    }
    note 1 = this
    {
      have "finite (prob_proj PROB vs)"
        unfolding prob_proj_def valid_states_def
        using assms(1)
        by simp
      then have "finite ?S"
        using Setcompr_eq_image assms(3)
        by (metis List.finite_set finite_imageI)
    }
    then have "S vs lss PROB (fmrestrict_set vs s) \<le> Max ?S"
      using 1 Max.coboundedI
      by blast
    then have "S vs lss PROB (fmrestrict_set vs s) \<le> Sup ?S"
      using Sup_nat_def
      by presburger
  }
  ultimately show ?thesis
    using le_trans
    by blast
qed


\<comment> \<open>NOTE first argument of `top\_sorted\_abs` had to be wrapped into lambda.\<close>
lemma problem_plan_bound_S_bound:
  fixes PROB :: "'a problem"
  assumes "finite PROB" "(top_sorted_abs (\<lambda>x y. y \<in> state_successors (prob_proj PROB vs) x) lss)"
    "(set lss = valid_states (prob_proj PROB vs))"
  shows "
    problem_plan_bound PROB
    \<le> Sup {S vs lss PROB (s' :: 'a state) | s'. s' \<in> valid_states (prob_proj PROB vs)}
  "
proof -
  let ?f="\<lambda>PROB.
    Sup {S vs lss PROB (s' :: 'a state) | s'. s' \<in> valid_states (prob_proj PROB vs)} + 1"
  {
    fix as and s :: "'a state"
    assume "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
    then obtain as' where a:
      "exec_plan s as' = exec_plan s as" "subseq as' as"
      "length as' \<le> Sup {S vs lss PROB s' |s'. s' \<in> valid_states (prob_proj PROB vs)}"
      using assms S_in_MPLS_leq_2_pow_n
      by blast
    then have "length as' < ?f PROB"
      by linarith
    moreover have "exec_plan s as = exec_plan s as'"
      using a(1)
      by simp
    ultimately have
      "\<exists>as'. exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' < ?f PROB"
      using a(2)
      by blast
  }
  then show ?thesis
    using assms(1) problem_plan_bound_UBound[where f="?f"]
    by fastforce
qed

subsection "State Space Acyclicity"

text \<open> State space acyclicity is again formalized using graphs to model the state space. However
the relation inducing the graph is the successor relation on states. [Abdulaziz et al.,
Definition 15, HOL4 Definition 15, p.27]

With this, the acyclic system compositional bound `S` can be shown to be an upper bound on the
sublist diameter (lemma `problem\_plan\_bound\_S\_bound\_thesis`). [Abdulaziz et al., p.29] \<close>

\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE first argument of 'top\_sorted\_abs' had to be wrapped into lambda.\<close>
definition sspace_DAG where
  "sspace_DAG PROB lss \<equiv> (
    (set lss = valid_states PROB)
    \<and> (top_sorted_abs (\<lambda>x y. y \<in> state_successors PROB x) lss)
  )"


lemma problem_plan_bound_S_bound_2nd_step_thesis:
  assumes "finite (PROB :: 'a problem)" "(sspace_DAG (prob_proj PROB vs) lss)"
    "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.   (exec_plan s as' = exec_plan s as)
    \<and> (subseq as' as)
    \<and> (length as' \<le> S vs lss PROB (fmrestrict_set vs s))
  )"
  using assms problem_plan_bound_S_bound_2nd_step sspace_DAG_def
  by fast


text \<open>And finally, this is the main lemma about the upper bounding algorithm.\<close>

theorem problem_plan_bound_S_bound_thesis:
  assumes "finite (PROB :: 'a problem)" "(sspace_DAG (prob_proj PROB vs) lss)"
  shows "(
    problem_plan_bound PROB
    \<le> Sup {S vs lss PROB s' | s'. s' \<in> valid_states (prob_proj PROB vs)}
  )"
  using assms problem_plan_bound_S_bound sspace_DAG_def
  by fast


end