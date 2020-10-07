theory SystemAbstraction
  imports
    Main
    "HOL-Library.Sublist"
    "HOL-Library.Finite_Map"
    FactoredSystem
    FactoredSystemLib
    ActionSeqProcess
    Dependency
    TopologicalProps
    FmapUtils
    ListUtils

begin


\<comment> \<open>NOTE  hide 'Map.map\_add' because of conflicting notation with 'FactoredSystemLib.map\_add\_ltr'.\<close>
hide_const (open) Map.map_add
no_notation Map.map_add (infixl "++" 100)


section "System Abstraction"

text \<open> Projection of an object (state, action, sequence of action or factored representation)
to a variable set `vs` restricts the domain of the object or its components---in case of composite
objects---to `vs`. [Abdulaziz et al., p.12]

This section presents the relevant definitions (`action\_proj`, `as\_proj`, `prob\_proj` and `ss\_proj`)
as well as their characterization. \<close>


subsection "Projection of Actions, Sequences of Actions and Factored Representations."


definition action_proj where
  "action_proj a vs \<equiv> (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a))"


lemma action_proj_pair: "action_proj (p, e) vs = (fmrestrict_set vs p, fmrestrict_set vs e)"
  unfolding action_proj_def
  by simp


definition prob_proj where
  "prob_proj PROB vs \<equiv> (\<lambda>a. action_proj a vs) ` PROB"


\<comment> \<open>NOTE  using 'fun' due to multiple defining equations.\<close>
\<comment> \<open>NOTE  name shortened.\<close>
fun as_proj where
  "as_proj [] _ = []"
| "as_proj (a # as) vs = (if fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}
    then action_proj a vs # as_proj as vs
    else as_proj as vs
  )"


\<comment> \<open>TODO the lemma might be superfluous (follows directly from 'as\_proj.simps').\<close>
lemma as_proj_pair:
  "as_proj ((p, e) # as) vs = (if (fmdom' (fmrestrict_set vs e) \<noteq> {})
    then action_proj (p, e) vs # as_proj as vs
    else as_proj as vs
  )"
  "as_proj [] vs = []"
  by (simp)+


lemma proj_state_succ:
  fixes s a vs
  assumes "(fst a \<subseteq>\<^sub>f s)"
  shows  "(state_succ (fmrestrict_set vs s) (action_proj a vs) = fmrestrict_set vs (state_succ s a))"
proof -
  have "
    fmrestrict_set vs (if fst a \<subseteq>\<^sub>f s then snd a ++ s else s)
    = fmrestrict_set vs (snd a ++ s)
  "
    using assms
    by simp
  moreover
  {
    assume "fst (action_proj a vs) \<subseteq>\<^sub>f fmrestrict_set vs s"
    then have "
      (state_succ (fmrestrict_set vs s) (action_proj a vs)
       = fmrestrict_set vs (snd a ++ s))
    "
      unfolding state_succ_def action_proj_def fmap_add_ltr_def
      by force
  }
  moreover {
    assume "\<not>(fst (action_proj a vs) \<subseteq>\<^sub>f fmrestrict_set vs s)"
    then have "
      (state_succ (fmrestrict_set vs s) (action_proj a vs)
       = fmrestrict_set vs (snd a ++ s))
    "
      unfolding state_succ_def  action_proj_def
      using assms fmsubset_restrict_set_mono
      by auto
  }
  ultimately show ?thesis
    unfolding state_succ_def
    by argo
qed


lemma graph_plan_lemma_1:
  fixes s vs as
  assumes "sat_precond_as s as"
  shows "(exec_plan (fmrestrict_set vs s) (as_proj as vs) = (fmrestrict_set vs (exec_plan s as)))"
  using assms
proof (induction as arbitrary: s vs)
  case (Cons a as)
  then show ?case
  proof (cases "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}")
    case True
    then have
      "state_succ (fmrestrict_set vs s) (action_proj a vs) = fmrestrict_set vs (state_succ s a)"
      using Cons.prems proj_state_succ
      by fastforce
    then show ?thesis
      unfolding exec_plan.simps sat_precond_as.simps as_proj.simps
      using Cons.IH Cons.prems True
      by simp
  next
    case False
    then have "(fmdom' (snd a) \<inter> vs = {})"
      using False fmdom'_restrict_set_precise[of vs "snd a"]
      by argo
    then have "fmrestrict_set vs s = fmrestrict_set vs (state_succ s a)"
      using disj_imp_eq_proj_exec
      by blast
    then show ?thesis
      unfolding exec_plan.simps sat_precond_as.simps as_proj.simps
      using Cons.IH Cons.prems False
      by simp
  qed
qed simp


\<comment> \<open>TODO the proofs are inefficient (detailed proofs?).\<close>
lemma  proj_action_dom_eq_inter:
  shows "
    action_dom (fst (action_proj a vs)) (snd (action_proj a vs))
    = (action_dom (fst a) (snd a) \<inter> vs)
  "
unfolding action_dom_def action_proj_def
by (auto simp: fmdom'_restrict_set_precise)


lemma graph_plan_neq_mems_state_set_neq_len:
  shows "prob_dom (prob_proj PROB vs) = (prob_dom PROB \<inter> vs)"
proof -
  have "
      prob_dom (prob_proj PROB vs)
      = (
        \<Union>(s1, s2)\<in>(\<lambda>a. (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a)))
        `  PROB. action_dom s1 s2
      )
    "
    unfolding prob_dom_def prob_proj_def action_proj_def
    by blast
  moreover
  {
    have "
    (prob_dom PROB \<inter> vs)
    = (\<Union>a\<in>PROB. action_dom (fst a) (snd a)  \<inter> vs)
  "
      unfolding prob_dom_def prob_proj_def
      using SUP_cong
      by auto
    also have "\<dots> = (\<Union>a\<in>PROB. action_dom (fst (action_proj a vs)) (snd (action_proj a vs)))"
      using proj_action_dom_eq_inter[symmetric]
      by fast
    finally have "
      (prob_dom PROB \<inter> vs)
      = (\<Union>a\<in>PROB. fmdom' (fmrestrict_set vs (fst a)) \<union> fmdom' (fmrestrict_set vs (snd a)))
    "
      unfolding action_dom_def action_proj_def
      by simp
  }
  ultimately show ?thesis
    by (metis (mono_tags, lifting) SUP_cong UN_simps(10) action_dom_def case_prod_beta' prod.sel(1)
        snd_conv)
qed


\<comment> \<open>TODO more detailed proof.\<close>
lemma graph_plan_not_eq_last_diff_paths:
  fixes PROB vs
  assumes "(s \<in> valid_states PROB)"
  shows "((fmrestrict_set vs s) \<in> valid_states (prob_proj PROB vs))"

  unfolding valid_states_def
  using graph_plan_neq_mems_state_set_neq_len
  by (metis (mono_tags, lifting)
      assms fmdom'.rep_eq fmlookup_fmrestrict_set_dom inf_commute mem_Collect_eq valid_states_def)


lemma dom_eff_subset_imp_dom_succ_eq_proj:
  fixes h s vs
  assumes "(fmdom' (snd h) \<subseteq> fmdom' s)"
  shows "(fmdom' (state_succ s (action_proj h vs)) = fmdom' (state_succ s h))"
proof (cases "fst (fmrestrict_set vs (fst h), fmrestrict_set vs (snd h)) \<subseteq>\<^sub>f s")
  case true: True
  then show ?thesis
  proof (cases "fst h \<subseteq>\<^sub>f s")
    case True
    then show ?thesis
      unfolding state_succ_def action_proj_def
      using true True
      by simp (smt assms fmap_add_ltr_def fmdom'.rep_eq fmdom'_add fmlookup_fmrestrict_set_dom
          inf.absorb_iff2 inf.left_commute sup.absorb_iff1)
  next
    case False
    then show ?thesis
      unfolding state_succ_def action_proj_def
      using true False
      by simp (metis (no_types) assms dual_order.trans fmap_add_ltr_def fmdom'.rep_eq fmdom'_add
          fmlookup_fmrestrict_set_dom inf_le2 sup.absorb_iff1)
  qed
next
  case False
  then have "fmdom' s = fmdom' (if fst h \<subseteq>\<^sub>f s then snd h ++ s else s)"
    using sat_precond_as_proj_4
    by auto
  then show ?thesis
    unfolding state_succ_def action_proj_def
    using False
    by presburger
qed


lemma drest_proj_succ_eq_drest_succ:
  fixes h s vs
  assumes "fst h \<subseteq>\<^sub>f s" "(fmdom' (snd h) \<subseteq> fmdom' s)"
  shows "(fmrestrict_set vs (state_succ s (action_proj h vs)) = fmrestrict_set vs (state_succ s h))"
proof -
  {
    have 1: "fmrestrict_set vs (fst h) \<subseteq>\<^sub>f s"
      using assms(1) submap_imp_state_succ_submap_a
      by (simp add: sat_precond_as_proj_4)
    then have "
      fmrestrict_set vs (state_succ s (action_proj h vs))
      = fmrestrict_set vs (fmrestrict_set vs (snd h) ++ s)
    "
      unfolding state_succ_def action_proj_def
      by simp
    also have "\<dots> = fmrestrict_set vs s ++\<^sub>f fmrestrict_set vs (fmrestrict_set vs (snd h))"
      unfolding fmap_add_ltr_def
      by simp
        \<comment> \<open>TODO
      refactor the step 'fmrestrict\_set ?X (fmrestrict\_set ?X ?f) = fmrestrict\_set ?X ?f' into
      own lemma in 'FmapUtils.thy'.\<close>
    also have "\<dots> = fmrestrict_set vs s ++\<^sub>f fmrestrict_set vs (snd h)"
      using fmfilter_alt_defs(4) fmfilter_cong fmlookup_filter fmrestrict_set_dom option.simps(3)
      by metis
    finally have "
      fmrestrict_set vs (state_succ s (action_proj h vs))
      = fmrestrict_set vs (snd h ++ s)
    "
      unfolding fmap_add_ltr_def
      by simp
  }
  moreover have "fmrestrict_set vs (state_succ s h) = fmrestrict_set vs ((snd h) ++ s)"
    unfolding state_succ_def
    using assms(1)
    by simp
  ultimately show ?thesis
    by simp
qed


\<comment> \<open>TODO remove? This is equivalent to 'proj\_state\_succ'.\<close>
lemma drest_succ_proj_eq_drest_succ:
  fixes s vs as
  assumes "(fst a \<subseteq>\<^sub>f s)"
  shows "(state_succ (fmrestrict_set vs s) (action_proj a vs) = fmrestrict_set vs (state_succ s a))"
  using assms proj_state_succ
  by blast


lemma exec_drest_cons_proj_eq_succ:
  fixes as PROB vs a
  assumes "fst a \<subseteq>\<^sub>f s"
  shows "(
    exec_plan (fmrestrict_set vs s) (action_proj a vs # as)
    = exec_plan (fmrestrict_set vs (state_succ s a)) as
  )"
proof -
  have "exec_plan (state_succ (fmrestrict_set vs s) (action_proj a vs)) as =
  exec_plan (fmrestrict_set vs (state_succ s a)) as"
    using assms drest_succ_proj_eq_drest_succ
    by metis
  then show ?thesis
    unfolding prob_proj_def
    by simp
qed


lemma exec_drest:
  fixes as a vs
  assumes "(fst a \<subseteq>\<^sub>f s)"
  shows "(
    exec_plan (fmrestrict_set vs (state_succ s a)) as
    = exec_plan (fmrestrict_set vs s) (action_proj a vs # as)
  )"
  using assms proj_state_succ
  by fastforce


lemma not_empty_eff_in_as_proj:
  fixes as a vs
  assumes "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
  shows "(as_proj (a # as) vs = (action_proj a vs # as_proj as vs))"
  unfolding action_proj_def as_proj.simps
  using assms
  by argo

lemma empty_eff_not_in_as_proj:
  fixes as a vs
  assumes "(fmdom' (fmrestrict_set vs (snd a)) = {})"
  shows "(as_proj (a # as) vs = as_proj as vs)"
  unfolding action_proj_def
  using assms
  by simp


lemma empty_eff_drest_no_eff:
  fixes s and a and vs
  assumes "(fmdom' (fmrestrict_set vs (snd a)) = {})"
  shows "(fmrestrict_set vs (state_succ s (action_proj a vs)) = fmrestrict_set vs s)"
proof -
  have "fmdom' (snd (action_proj a vs)) = {}"
    unfolding action_proj_def
    using assms
    by simp
  then have "state_succ s (action_proj a vs) = s"
    using empty_eff_exec_eq
    by fast
  then show ?thesis
    by simp
qed


lemma sat_precond_exec_as_proj_eq_proj_exec:
  fixes as vs s
  assumes "(sat_precond_as s as)"
  shows "(exec_plan (fmrestrict_set vs s) (as_proj as vs) = fmrestrict_set vs (exec_plan s as))"
  using assms
proof (induction as)
  case (Cons a as)
  then show ?case
    using Cons.prems graph_plan_lemma_1
    by blast
qed auto


lemma action_proj_in_prob_proj:
  assumes "(a \<in> PROB)"
  shows "(action_proj a vs \<in> prob_proj PROB vs)"
  unfolding action_proj_def prob_proj_def
  using assms
  by simp


lemma valid_as_valid_as_proj:
  fixes PROB vs
  assumes "(as \<in> valid_plans PROB)"
  shows "(as_proj as vs \<in> valid_plans (prob_proj PROB vs))"
  using assms
proof (induction "as" arbitrary: PROB vs)
  case (Cons a as)
  then show ?case
    using assms Cons
  proof(cases "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}")
    case True
    then have 1: "as_proj (a # as) vs = action_proj a vs # as_proj as vs"
      using True
      by simp
    then have "as \<in> valid_plans PROB"
      using Cons.prems valid_plan_valid_tail
      by fast
    then  have "as_proj as vs \<in> valid_plans (prob_proj PROB vs)"
      using Cons.IH 1
      by simp
    then have "action_proj a vs # as_proj as vs \<in> valid_plans (prob_proj PROB vs)"
      using Cons.prems action_proj_in_prob_proj valid_head_and_tail_valid_plan valid_plan_valid_head
      by metis
    then show ?thesis
      using 1
      by argo
  next
    case False
    then have "as_proj (a # as) vs = as_proj as vs"
      using False
      by auto
    then have "as_proj (a # as) vs \<in> valid_plans (prob_proj PROB vs)"
      using assms Cons valid_plan_valid_tail
      by metis
    then show ?thesis
      using assms Cons.IH(1)
      by blast
  qed
qed (simp add: valid_plans_def)


lemma finite_imp_finite_prob_proj:
  fixes PROB
  assumes "finite PROB"
  shows "(finite (prob_proj PROB vs))"
  unfolding prob_proj_def
  using assms
  by simp


\<comment> \<open>NOTE Base 2 in 5th assumption had to be explicitely fixed to 'nat' type to be able to use the
linearity lemma for powers of natural numbers.\<close>
lemma
  fixes PROB vs as and s :: "'a state"
  assumes "finite PROB" "s \<in> valid_states PROB" "as \<in> (valid_plans PROB)" "finite vs"
    "length (as_proj as vs) > ((2 :: nat) ^ card vs) - 1" "sat_precond_as s as"
  shows "(\<exists>as1 as2 as3.
    (as1 @ as2 @ as3 = as_proj as vs)
    \<and> (exec_plan (fmrestrict_set vs s) (as1 @ as2) = exec_plan (fmrestrict_set vs s) as1)
    \<and> (as2 \<noteq> [])
  )"
proof -
  {
    have "card (fmdom' (fmrestrict_set vs s)) \<le> card vs"
      using assms(4) graph_plan_card_state_set
      by fast
    then have "(2 :: nat) ^ (card (fmdom' (fmrestrict_set vs s))) - 1 \<le> 2 ^ (card vs) - 1"
      using power_increasing diff_le_mono
      by force
    also have "... < length (as_proj as vs)"
      using assms(5)
      by blast
    finally have "2 ^ card (fmdom' (fmrestrict_set vs s)) - 1 < length (as_proj as vs)"
      by blast
  }
  note 1 = this
  moreover have "fmrestrict_set vs s \<in> valid_states (prob_proj PROB vs)"
    using assms(2) graph_plan_not_eq_last_diff_paths
    by blast
  moreover have "as_proj as vs \<in> valid_plans (prob_proj PROB vs)"
    using assms(3) valid_as_valid_as_proj
    by blast
  moreover have "finite (prob_proj PROB vs)"
    using assms(1) finite_imp_finite_prob_proj
    by blast
  ultimately show ?thesis
    using lemma_2[where PROB="prob_proj PROB vs" and as="as_proj as vs" and s="fmrestrict_set vs s"]
    by blast
qed


lemma as_proj_eq_filter_action_proj:
  fixes as vs
  shows "as_proj as vs = filter (\<lambda>a. fmdom' (snd a) \<noteq> {}) (map (\<lambda>a. action_proj a vs) as)"
  by (induction as) (auto simp add: action_proj_def)


lemma append_eq_as_proj:
  fixes as1 as2 as3 p vs
  assumes "(as1 @ as2 @ as3 = as_proj p vs)"
  shows "(\<exists>p_1 p_2 p_3.
    (p_1 @ p_2 @ p_3 = p)
    \<and> (as2 = as_proj p_2 vs)
    \<and> (as1 = as_proj p_1 vs)
  )"
  using assms append_eq_as_proj_1 as_proj_eq_filter_action_proj
  by (metis (no_types, lifting))


lemma succ_drest_eq_drest_succ:
  fixes a s vs
  shows "
    state_succ (fmrestrict_set vs s) (action_proj a vs)
    = fmrestrict_set vs (state_succ s (action_proj a vs))
  "
proof -
  let ?lhs = "state_succ (fmrestrict_set vs s) (action_proj a vs)"
  let ?rhs = "fmrestrict_set vs (state_succ s (action_proj a vs))"
    \<comment> \<open>NOTE Show lhs and rhs equality by splitting on the cases introduced by the if-then branching
    of 'state\_succ'.\<close>
  {
    assume P1: "fst (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a)) \<subseteq>\<^sub>f fmrestrict_set vs s"
    then have a: "fst (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a)) \<subseteq>\<^sub>f s"
      using drest_smap_drest_smap_drest
      by auto
    then have "?lhs = fmrestrict_set vs (snd a) ++ fmrestrict_set vs s"
      unfolding state_succ_def action_proj_def
      using P1
      by simp
    moreover {
      have rhs: "?rhs = fmrestrict_set vs (fmrestrict_set vs (snd a) ++ s)"
        unfolding state_succ_def action_proj_def
        using a
        by auto
      also have "\<dots> = (fmrestrict_set vs (fmrestrict_set vs (snd a)) ++ fmrestrict_set vs s)"
        unfolding fmap_add_ltr_def
        by simp
      finally have "?rhs = (fmrestrict_set vs (snd a) ++ fmrestrict_set vs s)"
        unfolding fmfilter_alt_defs(4)
        by fastforce
    }
    ultimately have "?lhs = ?rhs"
      by argo
  }
  moreover {
    assume P2: "\<not>(fst (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a)) \<subseteq>\<^sub>f fmrestrict_set vs s)"
    then have a: "\<not>(fst (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a)) \<subseteq>\<^sub>f s)"
      using drest_smap_drest_smap_drest
      by auto
    then have "?lhs = fmrestrict_set vs s"
      unfolding state_succ_def action_proj_def
      using P2
      by argo
    moreover have "?rhs = fmrestrict_set vs s"
      unfolding state_succ_def action_proj_def
      using a
      by presburger
    ultimately have "?lhs = ?rhs"
      by simp
  }
  ultimately show "?lhs = ?rhs"
    by blast
qed


lemma proj_exec_proj_eq_exec_proj:
  fixes s as vs
  shows "
    fmrestrict_set vs (exec_plan (fmrestrict_set vs s) (as_proj as vs))
    = exec_plan (fmrestrict_set vs s) (as_proj as vs)
  "
proof (induction as arbitrary: s vs)
  case (Cons a as)
  then show ?case
    by (simp add: succ_drest_eq_drest_succ)
qed (simp add: fmfilter_alt_defs(4))


lemma proj_exec_proj_eq_exec_proj':
  fixes s as vs
  shows "
    fmrestrict_set vs (exec_plan (fmrestrict_set vs s) (as_proj as vs))
     = fmrestrict_set vs (exec_plan s (as_proj as vs))
  "
proof (induction as arbitrary: s vs)
  case (Cons a as)
  then show ?case
    by (simp add: succ_drest_eq_drest_succ)
qed (simp add: fmfilter_alt_defs(4))


lemma graph_plan_lemma_9:
  fixes s as vs
  shows "
    fmrestrict_set vs (exec_plan s (as_proj as vs))
    = exec_plan (fmrestrict_set vs s) (as_proj as vs)
  "
  by (metis proj_exec_proj_eq_exec_proj' proj_exec_proj_eq_exec_proj)


lemma act_dom_proj_eff_subset_act_dom_eff:
  fixes a vs
  shows "fmdom' (snd (action_proj a vs)) \<subseteq> fmdom' (snd a)"
proof -
  have "snd (action_proj a vs) = fmrestrict_set vs (snd a)"
    unfolding action_proj_def
    by simp
  then have "fmlookup (fmrestrict_set vs (snd a)) \<subseteq>\<^sub>m fmlookup (snd a)"
    by (simp add: map_le_def fmdom'_restrict_set_precise)
  then have "dom (fmlookup (fmrestrict_set vs (snd a))) \<subseteq> dom (fmlookup (snd a))"
    using map_le_implies_dom_le
    by blast
  then have "fmdom' (fmrestrict_set vs (snd a)) \<subseteq> fmdom' (snd a)"
    using fmdom'.rep_eq
    by metis
  then show ?thesis
    unfolding action_proj_def
    by simp
qed


lemma exec_as_proj_valid:
  fixes as s PROB vs
  assumes "s \<in> valid_states PROB" "(as \<in> valid_plans PROB)"
  shows  "(exec_plan s (as_proj as vs) \<in> valid_states PROB)"
  using assms
proof (induction as arbitrary: s PROB vs)
  case (Cons a as)
  then have 1: "as \<in> valid_plans PROB"
    using Cons.prems(2) valid_plan_valid_tail
    by fast
  then have 2: "exec_plan s (as_proj as vs) \<in> valid_states PROB"
    using Cons.prems(1) Cons.IH(1)
    by blast
      \<comment> \<open>NOTE split on the if-then branch introduced by 'as\_proj'.\<close>
  moreover {
    assume P: "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
    then have "
      exec_plan s (as_proj (a # as) vs)
      = exec_plan (state_succ s (action_proj a vs)) (as_proj as vs)
    "
      by simp
        \<comment> \<open>NOTE split on the if-then branch introduced by 'state\_succ'\<close>
    moreover
    {
      assume "fst (action_proj a vs) \<subseteq>\<^sub>f s"
      then have 3: "
        exec_plan (state_succ s (action_proj a vs)) (as_proj as vs)
        = exec_plan (snd (action_proj a vs) ++ s) (as_proj as vs)
      "
        unfolding state_succ_def
        using calculation
        by simp
      {
        \<comment> \<open>TODO Unsure why this proof step is necessary at all, but it should be refactored into a
          dedicated lemma @{term "s \<in> valid_states PROB \<Longrightarrow> fmdom' s = prob_dom PROB"}.\<close>
        {
          have "s \<in> valid_states PROB"
            using Cons.prems
            by simp
          then have "s \<in> {s'. fmdom' s' = prob_dom PROB}"
            unfolding valid_states_def
            by simp
          then obtain s' where "s' = s" "fmdom' s' = prob_dom PROB"
            by auto
          then have "fmdom' s = prob_dom PROB"
            by simp
        }
          \<comment> \<open>TODO Refactor this step ('also ...' for subset chain; replace fact
        `fmdom' s = prob\_dom PROB` in last step with MP step from lemma refactored above.\<close>
        moreover {
          have "(snd (action_proj a vs) ++ s) = (s ++\<^sub>f fmrestrict_set vs (snd a))"
            unfolding action_proj_def fmap_add_ltr_def
            by simp
          then have a: "a \<in> PROB"
            using Cons.prems(2) valid_plan_valid_head
            by fast
          then have "action_dom (fst a) (snd a) \<subseteq> prob_dom PROB"
            using exec_as_proj_valid_2
            by blast
          then have "fmdom' (snd a) \<subseteq> action_dom (fst a) (snd a)"
            unfolding action_dom_def
            by simp
          then have "fmdom' (fmrestrict_set vs (snd a)) \<subseteq> fmdom' (snd a)"
            using action_proj_def act_dom_proj_eff_subset_act_dom_eff snd_conv
            by metis
          then have "fmdom' (fmrestrict_set vs (snd a)) \<subseteq> prob_dom PROB"
            using FDOM_eff_subset_prob_dom_pair a
            by blast
          then have "fmdom' (s ++\<^sub>f fmrestrict_set vs (snd a)) = fmdom' s"
            by (simp add: calculation sup.absorb_iff1)
        }
        ultimately have "(snd (action_proj a vs) ++ s) \<in> valid_states PROB"
          unfolding action_proj_def fmap_add_ltr_def valid_states_def
          by simp
      }
      then have "exec_plan s (as_proj (a # as) vs) \<in> valid_states PROB"
        using 1 3 calculation(1) Cons.IH[where s = "snd (action_proj a vs) ++ s"]
        by presburger
    }
    moreover {
      assume "\<not>(fst (action_proj a vs) \<subseteq>\<^sub>f s)"
      then have "
        exec_plan (state_succ s (action_proj a vs)) (as_proj as vs)
        = exec_plan s (as_proj as vs)
      "
        unfolding state_succ_def
        by simp
      then have "exec_plan s (as_proj (a # as) vs) \<in> valid_states PROB"
        using 2
        by force
    }
    ultimately have "exec_plan s (as_proj (a # as) vs) \<in> valid_states PROB"
      by blast
  }
  moreover
  {
    assume "fmdom' (fmrestrict_set vs (snd a)) = {}"
    then have "
      exec_plan s (as_proj (a # as) vs) =
      exec_plan s (as_proj as vs)
    "
      by simp
    then have "exec_plan s (as_proj (a # as) vs) \<in> valid_states PROB"
      using 2
      by argo
  }
  ultimately show ?case
    by blast
qed simp


lemma drest_exec_as_proj_eq_drest_exec:
  fixes s as vs
  assumes "sat_precond_as s as"
  shows "(fmrestrict_set vs (exec_plan s (as_proj as vs)) = fmrestrict_set vs (exec_plan s as))"
proof -
  have 1: "
    (fmrestrict_set vs (exec_plan s (as_proj as vs))
    = exec_plan (fmrestrict_set vs s) (as_proj as vs))
  "
    using graph_plan_lemma_9 by auto
  then obtain s' where 2: "exec_plan (fmrestrict_set vs s) (as_proj as vs) = fmrestrict_set vs s'"
    using 1
    by metis
  then have "fmrestrict_set vs s' = fmrestrict_set vs (exec_plan s as)"
    using assms sat_precond_exec_as_proj_eq_proj_exec
    by metis
  then show
    "fmrestrict_set vs (exec_plan s (as_proj as vs)) = fmrestrict_set vs (exec_plan s as)"
    using 1 2
    by argo
qed


lemma action_proj_idempot:
  fixes a vs
  shows "action_proj (action_proj a vs) vs = (action_proj a vs)"
  unfolding action_proj_def
  by (simp add: fmfilter_alt_defs(4))


lemma  action_proj_idempot':
  fixes a vs
  assumes "(action_dom (fst a) (snd a) \<subseteq> vs)"
  shows "(action_proj a vs = a)"
  using assms
proof -
  have 1: "action_proj a vs = (fmrestrict_set vs (fst a), fmrestrict_set vs (snd a))"
    by (simp add: action_proj_def)
  then have 2: "(fmdom' (fst a) \<union> fmdom' (snd a)) \<subseteq> vs"
    unfolding action_dom_def
    using assms
    by (auto simp add: action_dom_def)
      \<comment> \<open>NOTE Show that both components of 'a' remain unchanged.\<close>
  {
    then have "fmdom' (fst a) \<subseteq> vs"
      by blast
    then have "fmrestrict_set vs (fst a) = (fst a)"
      using exec_drest_5
      by auto
  }
  moreover {
    have "fmdom' (snd a) \<subseteq> vs"
      using 2
      by auto
    then have "fmrestrict_set vs (snd a) = (snd a)"
      using exec_drest_5
      by blast
  }
  ultimately show ?thesis
    using 1
    by simp
qed


lemma action_proj_idempot'':
  fixes P vs
  assumes "prob_dom P \<subseteq> vs"
  shows "prob_proj P vs = P"
  using assms
proof -
  \<comment> \<open>TODO refactor.\<close>
  {
    fix a
    assume "a \<in> P"
    then have "action_dom (fst a) (snd a) \<subseteq> vs"
      using assms exec_as_proj_valid_2
      by fast
    then have "action_proj a vs = a"
      using action_proj_idempot'
      by fast
  }
  then have "prob_proj P vs = P"
    unfolding prob_proj_def
    by force
  then show ?thesis
    unfolding prob_proj_def
    by simp
qed


lemma sat_precond_as_proj:
  fixes as s s' vs
  assumes "(sat_precond_as s as)" "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "(sat_precond_as s' (as_proj as vs))"
  using assms
proof (induction as arbitrary: s s' vs)
  case (Cons a as)
  then have 1:
    "fst a \<subseteq>\<^sub>f s" "sat_precond_as (state_succ s a) as"
    using Cons.prems(1)
    by simp+
  then have 2: "fmrestrict_set vs (fst a) \<subseteq>\<^sub>f s"
    using assms(1) sat_precond_as_proj_4
    by blast
  moreover
  {
    assume "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
    then have "
      sat_precond_as s' (as_proj (a # as) vs)
      = (
        fst (action_proj a vs) \<subseteq>\<^sub>f s'
        \<and> sat_precond_as (state_succ s' (action_proj a vs)) (as_proj as vs)
      )
    "
      using calculation
      by simp
    moreover
    {
      have "fst (action_proj a vs) \<subseteq>\<^sub>f s' = (fmrestrict_set vs (fst a) \<subseteq>\<^sub>f s')"
        unfolding action_proj_def
        by simp
      moreover have "(fmrestrict_set vs (fst a) \<subseteq>\<^sub>f s) = (fmrestrict_set vs (fst a) \<subseteq>\<^sub>f s')"
        using Cons.prems(2) sat_precond_as_proj_1
        by blast
      ultimately have "fst (action_proj a vs) \<subseteq>\<^sub>f s'"
        using 2
        by blast
    }
      \<comment> \<open>TODO detailled proof for this sledgehammered step.\<close>
    moreover have "sat_precond_as (state_succ s' (action_proj a vs)) (as_proj as vs)"
      using 1 Cons.IH Cons.prems(2) drest_succ_proj_eq_drest_succ succ_drest_eq_drest_succ
      by metis
    ultimately have "(sat_precond_as s' (as_proj (a # as) vs))"
      by blast
  }
  moreover
  {
    assume P1: "\<not>(fmdom' (fmrestrict_set vs (snd a)) \<noteq> {})"
    then have "sat_precond_as s' (as_proj (a # as) vs)"
    proof (cases "as_proj (a # as) vs")
      case Cons2: (Cons a' list)
        \<comment> \<open>TODO unfold the sledgehammered metis steps.\<close>
      then have a: "
          sat_precond_as s' (as_proj (a # as) vs)
          = (fst a' \<subseteq>\<^sub>f s') \<and> sat_precond_as (state_succ s' a') list
        "
        using P1 Cons.IH Cons.prems(1, 2) Cons2
        by (metis sat_precond_as_proj_3 empty_eff_not_in_as_proj sat_precond_as.simps(2))
      then have b: "fst a' \<subseteq>\<^sub>f s'"
        unfolding sat_precond_as.simps(2)
        using P1 Cons.IH Cons.prems(1, 2) sat_precond_as_proj_3 empty_eff_not_in_as_proj
        by (metis sat_precond_as.simps(2))
      then have "sat_precond_as (state_succ s' a') list"
        using a
        by blast
      then show ?thesis
        using a b
        by blast
    qed fastforce
  }
  ultimately show ?case
    by blast
qed simp


lemma sat_precond_drest_as_proj:
  fixes as s s' vs
  assumes "(sat_precond_as s as)" "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "(sat_precond_as (fmrestrict_set vs s') (as_proj as vs))"
  using assms
proof (induction as arbitrary: s s' vs)
  case (Cons a as)
  then have 1: "fst a \<subseteq>\<^sub>f s" "sat_precond_as (state_succ s a) as"
    using Cons.prems
    by auto+
  then have "fmrestrict_set vs (fst a) \<subseteq>\<^sub>f fmrestrict_set vs s"
    using fmsubset_restrict_set_mono
    by blast
  then have "fst (action_proj a vs) \<subseteq>\<^sub>f fmrestrict_set vs s'"
    unfolding action_proj_def
    using Cons.prems(2) sat_precond_as_proj_1
    by simp
  then have "fmrestrict_set vs (snd a) = fmrestrict_set vs (snd (action_proj a vs))"
    unfolding action_proj_def
    by (simp add: fmfilter_alt_defs(4))
  then have "fst (action_proj a vs) \<subseteq>\<^sub>f s"
    unfolding action_proj_def
    using 1(1) fst_conv sat_precond_as_proj_4
    by auto
      \<comment> \<open>TODO unfold these sledgehammered steps.\<close>
  then have "
    fmrestrict_set vs (state_succ s a)
    = fmrestrict_set vs (state_succ (fmrestrict_set vs s') (action_proj a vs))
  "
    using 1(1) Cons.prems(2)
    by (metis fmfilter_alt_defs(4) fmfilter_true fmlookup_restrict_set
        drest_succ_proj_eq_drest_succ option.simps(3))
  then show ?case
    using Cons.prems(1, 2)
    by (metis fmfilter_alt_defs(4) fmfilter_true fmlookup_restrict_set sat_precond_as_proj
        option.simps(3))
qed simp


lemma as_proj_eq_as:
  assumes "(no_effectless_act as)" "(as \<in> valid_plans PROB)" "(prob_dom PROB \<subseteq> vs)"
  shows "(as_proj as vs = as)"
  using assms
proof (induction as arbitrary: PROB vs)
  case (Cons a as)
    \<comment> \<open>NOTE We only need to look at the first branch of 'as\_proj'.\<close>
    \<comment> \<open>TODO step should be refactored and proven explicitely because it's so pivotal.\<close>
  then have "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
    unfolding fmdom'_restrict_set_precise
    by (metis
        FDOM_eff_subset_prob_dom_pair dual_order.trans inf.orderE
        no_effectless_act.simps(2) valid_plan_valid_head)
      \<comment> \<open>NOTE Proof 'action\_proj a vs = a' for the first branch of 'as\_proj'.\<close>
  moreover {
    assume "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
      \<comment> \<open>NOTE show 'action\_proj a vs = a'.\<close>
    moreover {
      have "as_proj (a # as) vs = action_proj a vs # as_proj as vs"
        using calculation
        by force
      then have "a \<in> PROB"
        using Cons.prems(2) valid_plan_valid_head
        by fast
      then have "action_dom (fst a) (snd a) \<subseteq> prob_dom PROB"
        using exec_as_proj_valid_2
        by fast
      then have "action_dom (fst a) (snd a) \<subseteq> vs"
        using Cons.prems(3)
        by fast
      then have "action_proj a vs = a"
        using action_proj_idempot'
        by fast
    }
      \<comment> \<open>NOTE show that 'as\_proj as vs = as'.\<close>
    moreover {
      have 1: "no_effectless_act as"
        using Cons.prems(1)
        by simp
      then have "as \<in> valid_plans PROB"
        using Cons.prems(2) valid_plan_valid_tail
        by fast
      then have "as_proj as vs = as"
        using Cons.prems(3) Cons.IH 1
        by blast
    }
    ultimately have "as_proj (a # as) vs = a # as"
      by simp
  }
  ultimately show ?case
    by fast
qed simp


lemma exec_rem_effless_as_proj_eq_exec_as_proj:
  fixes s
  shows "exec_plan s (as_proj (rem_effectless_act as) vs) = exec_plan s (as_proj as vs)"
proof (induction as arbitrary: s vs)
  case (Cons a as)
    \<comment> \<open>Split cases on the branching introduced by `remove\_effectless\_act` and `as\_proj`.\<close>
  then show ?case
  proof (cases "fmdom' (snd a) \<noteq> {}")
    case true1: True
    then show ?thesis
    proof (cases "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}")
      case False
      then show ?thesis by (simp add: Cons true1)
    qed (simp add: Cons true1)
  next
    case False
    then show ?thesis
    proof (cases "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}")
      case true2: True
      then have 1: "fmdom' (snd a) \<inter> vs = {}"
        using False Int_empty_left
        by force
          \<comment> \<open>NOTE This step shows that the case for @{term "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"} is
            impossible.\<close>
          \<comment> \<open>TODO could be refactored into a (simp) lemma (`as\_proj\_eq\_as` also uses this?).\<close>
      then have "fmdom' (fmrestrict_set vs (snd a)) = {}"
        by (simp add: fmdom'_restrict_set_precise)
      then show ?thesis
        using true2
        by blast
    qed (simp add: Cons)
  qed
qed simp


lemma exec_as_proj_eq_exec_as:
  fixes PROB as vs s
  assumes "(as \<in> valid_plans PROB)" "(prob_dom PROB \<subseteq> vs)"
  shows "(exec_plan s (as_proj as vs) = exec_plan s as)"
  using assms as_proj_eq_as exec_rem_effless_as_proj_eq_exec_as_proj rem_effectless_works_1 rem_effectless_works_6
    rem_effectless_works_9 sublist_valid_plan
  by metis


lemma dom_prob_proj: "prob_dom (prob_proj PROB vs) \<subseteq> vs"
  using graph_plan_neq_mems_state_set_neq_len
  by fast


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into `FmapUtils.thy`.\<close>
lemma subset_proj_absorb_1_a:
  fixes f vs1 vs2
  assumes "(vs1 \<subseteq> vs2)"
  shows "fmrestrict_set vs1 (fmrestrict_set vs2 f) = fmrestrict_set vs1 f"
  using assms
proof -
  {
    fix v
    have "fmlookup (fmrestrict_set vs1 (fmrestrict_set vs2 f)) v = fmlookup (fmrestrict_set vs1 f) v"
      using assms
    proof (cases "v \<in> vs1")
      case False
      then show ?thesis
      proof (cases "v \<in> vs2")
        case False
        then have "v \<notin> vs1"
          using False assms
          by blast
        then have
          "fmlookup (fmrestrict_set vs1 (fmrestrict_set vs2 f)) v = None"
          "fmlookup (fmrestrict_set vs1 f) v = None"
          by simp+
        then show ?thesis
          by argo
      qed simp
    qed auto
  }
  then show ?thesis
    using fmap_ext
    by blast
qed

lemma subset_proj_absorb_1:
  assumes "(vs1 \<subseteq> vs2)"
  shows "(action_proj (action_proj a vs2) vs1 = action_proj a vs1)"
  using assms
proof -
  have
    "fmrestrict_set vs1 (fmrestrict_set vs2 (fst a)) = fmrestrict_set vs1 (fst a)"
    "fmrestrict_set vs1 (fmrestrict_set vs2 (snd a)) = fmrestrict_set vs1 (snd a)"
    using assms subset_proj_absorb_1_a
    by blast+
  then show ?thesis
    unfolding action_proj_def
    by simp
qed


lemma subset_proj_absorb:
  fixes PROB vs1 vs2
  assumes "vs1 \<subseteq> vs2"
  shows "prob_proj (prob_proj PROB vs2) vs1 = prob_proj PROB vs1"
proof -
  {
    have "
      prob_proj (prob_proj PROB vs2) vs1
      = ((\<lambda>a. action_proj a vs1) \<circ> (\<lambda>a. action_proj a vs2)) ` PROB
    "
      unfolding prob_proj_def
      by fastforce
    also have "\<dots> = (\<lambda>a. action_proj (action_proj a vs2) vs1) ` PROB"
      by fastforce
    also have "\<dots> = (\<lambda>a. action_proj a vs1) ` PROB"
      using assms subset_proj_absorb_1
      by metis
    also have "\<dots> = prob_proj PROB vs1"
      unfolding prob_proj_def
      by simp
    finally have "prob_proj (prob_proj PROB vs2) vs1 = prob_proj PROB vs1"
      by simp
  }
  then show ?thesis
    by simp
qed


lemma union_proj_absorb:
  fixes PROB vs vs'
  shows "prob_proj (prob_proj PROB (vs \<union> vs')) vs = prob_proj PROB vs"
  by (simp add: subset_proj_absorb)


lemma NOT_VS_IN_DOM_PROJ_PRE_EFF:
  fixes ROB vs v a
  assumes "\<not>(v \<in> vs)" "(a \<in> PROB)"
  shows "(
    ((v \<in> fmdom' (fst a)) \<longrightarrow> (v \<in> fmdom' (fst (action_proj a (prob_dom PROB - vs)))))
    \<and> ((v \<in> fmdom' (snd a)) \<longrightarrow> (v \<in> fmdom' (snd (action_proj a (prob_dom PROB - vs)))))
  )"
  unfolding action_proj_def
  using assms
  by (simp add: IN_FDOM_DRESTRICT_DIFF FDOM_pre_subset_prob_dom_pair
      FDOM_eff_subset_prob_dom_pair)


lemma IN_DISJ_DEP_IMP_DEP_DIFF:
  fixes PROB vs vs' v v'
  assumes "(v \<in> vs')" "(v' \<in> vs')" "(disjnt vs vs')"
  shows "(dep PROB v v' \<longrightarrow> dep (prob_proj PROB (prob_dom PROB - vs)) v v')"
  using assms
proof (cases "v = v'")
  case False
  {
    assume P: "dep PROB v v'"
    then obtain a where a:
      "(v \<in> fmdom' (fst a) \<and> v' \<in> fmdom' (snd a) \<or> v \<in> fmdom' (snd a) \<and> v' \<in> fmdom' (snd a))"
      "a \<in> PROB"
      unfolding dep_def
      using False
      by blast
    {
      have "v \<notin> vs"
        using assms(1, 3)
        unfolding disjnt_def
        by blast
      then have "(v \<in> fmdom' (fst a) \<longrightarrow> v \<in> fmdom' (fst (action_proj a (prob_dom PROB - vs))))"
        "(v \<in> fmdom' (snd a) \<longrightarrow> v \<in> fmdom' (snd (action_proj a (prob_dom PROB - vs))))"
        using a NOT_VS_IN_DOM_PROJ_PRE_EFF
        by metis+
    }
    note b = this
    then consider (i) "v \<in> fmdom' (fst a) \<and> v' \<in> fmdom' (snd a)"
      | (ii) "v \<in> fmdom' (snd a) \<and> v' \<in> fmdom' (snd a)"
      using a
      by blast
    then have "dep (prob_proj PROB (prob_dom PROB - vs)) v v'"
    proof (cases)
      case i
      then show ?thesis
        using assms(2, 3) a(2) b(1)
        by (meson dep_def disjnt_iff action_proj_in_prob_proj NOT_VS_IN_DOM_PROJ_PRE_EFF)
    next
      case ii
      then show ?thesis
        using assms(2, 3) a(2) b(2)
        by (meson dep_def disjnt_iff action_proj_in_prob_proj NOT_VS_IN_DOM_PROJ_PRE_EFF)
    qed
  }
  then show ?thesis
    by blast
qed (auto simp: dep_def prob_proj_def disjnt_def)


lemma  PROB_DOM_PROJ_DIFF:
  fixes P vs
  shows "prob_dom (prob_proj PROB (prob_dom PROB - vs)) = (prob_dom PROB) - vs"
  using graph_plan_neq_mems_state_set_neq_len
  by fastforce


lemma  two_children_parent_mems_le_finite:
  fixes PROB vs
  assumes "(vs \<subseteq> prob_dom PROB)"
  shows "(prob_dom (prob_proj PROB vs) = vs)"
  using assms graph_plan_neq_mems_state_set_neq_len
  by fast


\<comment> \<open>TODO showcase (non-trivial proof).\<close>
\<comment> \<open>TODO find explicit proof.\<close>
lemma PROJ_DOM_PRE_EFF_SUBSET_DOM:
  fixes a vs
  shows "
    (fmdom' (fst (action_proj a vs)) \<subseteq> fmdom' (fst a))
    \<and> (fmdom' (snd (action_proj a vs)) \<subseteq> fmdom' (snd a))
  "
  unfolding action_proj_def
  by (auto simp: fmdom'_restrict_set_precise)


lemma NOT_IN_PRE_EFF_NOT_IN_PRE_EFF_PROJ:
  fixes a v vs
  shows "
    (\<not>(v \<in> fmdom' (fst a)) \<longrightarrow> \<not>(v \<in> fmdom' (fst (action_proj a vs))))
    \<and> (\<not>(v \<in> fmdom' (snd a)) \<longrightarrow> \<not>(v \<in> fmdom' (snd (action_proj a vs))))
  "
  using PROJ_DOM_PRE_EFF_SUBSET_DOM rev_subsetD
  by metis


lemma dep_proj_dep:
  assumes "dep (prob_proj PROB vs) v v'"
  shows "dep PROB v v'"
  using assms
  unfolding dep_def prob_proj_def action_proj_def image_def
  apply (auto simp: fmdom'_restrict_set_precise)
  by auto


lemma NDEP_PROJ_NDEP:
  fixes PROB vs vs' vs''
  assumes "(\<not>dep_var_set PROB vs vs')"
  shows "(\<not>dep_var_set (prob_proj PROB vs'') vs vs')"
  using assms dep_proj_dep
  unfolding dep_var_set_def
  by metis


lemma SUBSET_PROJ_DOM_DISJ:
  fixes PROB vs vs'
  assumes "(vs \<subseteq> (prob_dom (prob_proj PROB (prob_dom PROB - vs'))))"
  shows "disjnt vs vs'"
  using assms
  by (auto simp add: PROB_DOM_PROJ_DIFF subset_iff disjnt_iff)


\<comment> \<open>TODO showcase (lemma which is solved effortlessly by automation).\<close>
lemma NOT_VS_DEP_IMP_DEP_PROJ:
  fixes PROB vs v v'
  assumes "\<not>(v \<in> vs)" "\<not>(v' \<in> vs)" "(dep PROB v v')"
  shows "(dep (prob_proj PROB (prob_dom PROB - vs)) v v')"
  using assms
  by (metis Diff_disjoint Diff_iff disjnt_def insertCI IN_DISJ_DEP_IMP_DEP_DIFF)


lemma DISJ_PROJ_NDEP_IMP_NDEP:
  fixes PROB vs vs' vs''
  assumes
    "(disjnt vs vs'')" "disjnt vs vs'"
    "\<not>(dep_var_set (prob_proj PROB (prob_dom PROB - vs)) vs' vs'')"
  shows "\<not>(dep_var_set PROB vs' vs'')"
proof -
  {
    assume C: "dep_var_set PROB vs' vs''"
    then obtain v1 v2 where "v1 \<in> vs'" "v2 \<in> vs''" "disjnt vs' vs''" "dep PROB v1 v2"
      unfolding dep_var_set_def
      by blast
    then have "\<exists>v1 v2.
      v1 \<in> vs' \<and> v2 \<in> vs'' \<and> disjnt vs' vs'' \<and> dep (prob_proj PROB (prob_dom PROB - vs)) v1 v2
    "
      using assms(1, 2) IntI disjnt_def empty_iff NOT_VS_DEP_IMP_DEP_PROJ
      by metis
    then have False
      using assms
      unfolding dep_var_set_def
      by blast
  }
  then show ?thesis
    using assms
    unfolding dep_var_set_def
    by argo
qed


lemma PROJ_DOM_IDEMPOT:
  fixes PROB
  shows "prob_proj PROB (prob_dom PROB) = PROB"
  using action_proj_idempot''
  by blast


lemma prob_proj_idempot:
  fixes vs vs'
  assumes "(vs \<subseteq> vs')"
  shows "(prob_proj PROB vs = prob_proj (prob_proj PROB vs') vs)"
  using assms subset_proj_absorb
  by blast


lemma prob_proj_dom_diff_eq_prob_proj_prob_proj_dom_diff:
  fixes vs vs'
  shows "
    prob_proj PROB (prob_dom PROB - (vs \<union> vs'))
    = prob_proj
      (prob_proj PROB (prob_dom PROB - vs))
      (prob_dom (prob_proj PROB (prob_dom PROB - vs)) - vs')
"
  using PROB_DOM_PROJ_DIFF subset_proj_absorb
  by (metis Compl_Diff_eq Diff_subset compl_eq_compl_iff sup_assoc)


lemma PROJ_DEP_IMP_DEP:
  fixes PROB vs v v'
  assumes "dep (prob_proj PROB (prob_dom PROB - vs)) v v'"
  shows "dep PROB v v'"
  using assms
  unfolding dep_def prob_proj_def
proof (cases "v = v'")
  case False
  then show "(\<exists>a.
      a \<in> PROB
      \<and> (v \<in> fmdom' (fst a) \<and> v' \<in> fmdom' (snd a) \<or> v \<in> fmdom' (snd a) \<and> v' \<in> fmdom' (snd a)))
    \<or> v = v'"
    using assms
    unfolding dep_def prob_proj_def
    by (smt image_iff NOT_IN_PRE_EFF_NOT_IN_PRE_EFF_PROJ)
qed blast


lemma PROJ_NDEP_TC_IMP_NDEP_TC_OR:
  fixes PROB vs v v'
  assumes "\<not>((\<lambda>v1' v2'. dep (prob_proj PROB (prob_dom PROB - vs)) v1' v2')\<^sup>+\<^sup>+ v v')"
  shows "(
    (\<not>((\<lambda>v1' v2'. dep PROB v1' v2')\<^sup>+\<^sup>+ v v'))
    \<or> (\<exists>v''.
      v'' \<in> vs
      \<and> ((\<lambda>v1' v2'. dep PROB v1' v2')\<^sup>+\<^sup>+ v v'')
      \<and> ((\<lambda>v1' v2'. dep PROB v1' v2')\<^sup>+\<^sup>+ v'' v')
    )
  )"
  using assms NOT_VS_DEP_IMP_DEP_PROJ DEP_REFL REFL_TC_CONJ[of
      "\<lambda>v v'. dep PROB v  v'" "\<lambda>v. \<not>(v \<in> vs)" "\<lambda>v v'. dep (prob_proj PROB (prob_dom PROB- vs)) v v'"
      v v']
  by fastforce


lemma every_action_proj_eq_as_proj:
  fixes as vs
  shows "list_all (\<lambda> a. action_proj a vs = a) (as_proj as vs)"
  by (induction as) (auto simp add: action_proj_idempot)


lemma empty_eff_not_in_as_proj_2:
  fixes a as vs
  assumes "fmdom' (snd (action_proj a vs)) = {}"
  shows "(as_proj as vs = as_proj (a # as) vs)"
  using assms
  by (auto simp add: action_proj_def)

declare[[smt_timeout=100]]

lemma sublist_as_proj_eq_as:
  fixes as' as vs
  assumes "subseq as' (as_proj as vs)"
  shows "(as_proj as' vs = as')"
  using assms
proof (induction as arbitrary: as' vs)
  case Nil
  moreover have "as' = []"
    using Nil.prems sublist_NIL
    by force
  then show ?case
    by simp
next
  case cons: (Cons a as)
  then show ?case
  proof (cases "as'")
    case (Cons aa list)
    then show ?thesis
    proof (cases "fmdom' (fmrestrict_set vs (snd aa)) \<noteq> {}")
      case True
      then have "as_proj as' vs = action_proj aa vs # as_proj list vs"
        using Cons True
        by auto
      then show ?thesis
        by (metis as_proj.simps(2) cons.IH cons.prems action_proj_idempot local.Cons
            subseq_Cons2_iff)
    next
      case False
      then have "as_proj as' vs = as_proj list vs"
        using Cons False
        by simp
      then show ?thesis using cons False
        unfolding Cons
        by (smt action_proj_def action_proj_idempot as_proj.simps(2) prod.inject subseq_Cons2_neq)
    qed
  qed simp
qed


lemma DISJ_EFF_DISJ_PROJ_EFF:
  fixes a s vs
  assumes "fmdom' (snd a) \<inter> s = {}"
  shows "(fmdom' (snd (action_proj a vs)) \<inter> s = {})
"
proof -
  have 1: "snd (action_proj a vs) = fmrestrict_set vs (snd a)"
    unfolding action_proj_def
    by simp
  then have "fmdom' (fmrestrict_set vs (snd a)) \<subseteq> fmdom' (snd a)"
    using act_dom_proj_eff_subset_act_dom_eff
    by metis
  then show ?thesis
    using assms 1
    by auto
qed


\<comment> \<open>NOTE showcase (the step using `graph\_plan\_lemma\_5`--- labelled by '[1]'--- is non-trivial proof
due to missing premises and the last six proof steps are redundant).\<close>
lemma state_succ_proj_eq_state_succ:
  fixes a s vs
  assumes "(varset_action a vs)" "(fst a \<subseteq>\<^sub>f s)" "(fmdom' (snd a) \<subseteq> fmdom' s)"
  shows "(state_succ s (action_proj a vs) = state_succ s a)"
proof -
  have 1: "fmdom' (snd a) \<inter> (fmdom' s - vs) = {}"
    using assms(1) vset_disj_eff_diff
    by blast
  then have  2:
    "fmrestrict_set (fmdom' s - vs) s = fmrestrict_set (fmdom' s - vs) (state_succ s a)"
    using disj_imp_eq_proj_exec[where vs = "fmdom' s - vs"]
    by blast
  then have "fmdom' (snd (action_proj a vs)) \<inter> (fmdom' s - vs) = {}"
    using 1 DISJ_EFF_DISJ_PROJ_EFF[where s = "(fmdom' s - vs)"]
    by blast
  then have "
    fmrestrict_set (fmdom' s - vs) s
    = fmrestrict_set (fmdom' s - vs) (state_succ s (action_proj a vs))
  "
    using disj_imp_eq_proj_exec[where a = "(action_proj a vs)" and vs = "fmdom' s - vs"]
    by blast
  then have "fmdom' (snd (action_proj a vs)) \<inter> (fmdom' s - vs) = {}"
    using 1 DISJ_EFF_DISJ_PROJ_EFF[where s = "(fmdom' s - vs)"]
    by blast
  then have "
    fmrestrict_set (fmdom' s - vs) s =
    fmrestrict_set (fmdom' s - vs) (state_succ s (action_proj a vs))
  "
    using disj_imp_eq_proj_exec[of "action_proj a vs" "fmdom' s - vs"]
    by fast
      \<comment> \<open>[1]\<close>
      \<comment> \<open>TODO unwrap this step.\<close>
  then show ?thesis
    using 2 FDOM_state_succ graph_plan_lemma_5[where s = "state_succ s (action_proj a vs)"
        and s' = "state_succ s a" and vs = vs] assms(2, 3) dom_eff_subset_imp_dom_succ_eq_proj
      drest_proj_succ_eq_drest_succ
    by metis
qed


\<comment> \<open>NOTE duplicate declaration of lemma `state\_succ\_proj\_eq\_state\_succ` removed.\<close>


lemma no_effectless_proj:
  fixes vs as
  shows "no_effectless_act (as_proj as vs)"
  by (induction as arbitrary: vs) (auto simp add: action_proj_def)


\<comment> \<open>NOTE duplicate (this is identical to `valid\_as\_valid\_as\_proj`).\<close>
lemma as_proj_valid_in_prob_proj:
  fixes PROB vs as
  assumes "(as \<in> valid_plans PROB)"
  shows "(as_proj as vs \<in> valid_plans (prob_proj PROB vs))"
  using assms valid_as_valid_as_proj
  by blast


\<comment> \<open>TODO Unwrap the smt proof.\<close>
lemma prob_proj_comm:
  fixes PROB vs vs'
  shows "prob_proj (prob_proj PROB vs) vs' = prob_proj (prob_proj PROB vs') vs"
  by (smt graph_plan_neq_mems_state_set_neq_len inf_commute inf_le2 PROJ_DOM_IDEMPOT prob_proj_idempot)


\<comment> \<open>TODO Unwrap the metis proof.\<close>
lemma vset_proj_imp_vset:
  fixes vs vs' a
  assumes "(varset_action a vs')" "(varset_action (action_proj a vs') vs)"
  shows "(varset_action a vs)"
  unfolding varset_action_def action_proj_def
  using assms
  by (metis action_proj_def exec_drest_5 snd_conv varset_action_def)


lemma  vset_imp_vset_act_proj_diff:
  fixes PROB vs vs' a
  assumes "(varset_action a vs)"
  shows "(varset_action (action_proj a (prob_dom PROB - vs')) vs)"
proof -
  have 1: "(fmdom' (snd a) \<subseteq> vs)"
    using assms varset_action_def
    by metis
  moreover
  {
    \<comment> \<open>TODO refactor and put into `Fmap\_Utils`.\<close>
    have "
      fmdom' (snd (
        fmrestrict_set (prob_dom PROB - vs') (fst a)
        , fmrestrict_set (prob_dom PROB - vs') (snd a)
      ))
      = (fmdom' (snd a) \<inter> (prob_dom PROB - vs'))
    "
      by (simp add: Int_def Set.filter_def fmfilter_alt_defs(4))
    also have "\<dots> \<subseteq> fmdom' (snd a)"
      by simp
    finally have "fmdom' (snd (
        fmrestrict_set (prob_dom PROB - vs') (fst a)
        , fmrestrict_set (prob_dom PROB - vs') (snd a)
      ))
      \<subseteq> vs
    "
      using 1 by simp
  }
  ultimately show ?thesis
    unfolding varset_action_def dep_var_set_def dep_def action_proj_def
    by blast
qed


lemma action_proj_disj_diff:
  assumes "(action_dom (fst a) (snd a) \<subseteq> vs1)" "(vs2 \<inter> vs3 = {})"
  shows "(action_proj (action_proj a (vs1 - vs2)) vs3 = action_proj a vs3)"
proof -
  have "\<forall>f fa fb p.
    action_proj (action_proj (action_proj p f) fb) fa = action_proj (action_proj p f) fb
    \<or> \<not> action_dom (fst p::('a, 'b) fmap) (snd p::(_, 'c) fmap) \<inter> (f \<inter> fb) \<subseteq> fa
  "
    by (metis (no_types) action_proj_idempot' proj_action_dom_eq_inter inf_assoc)
  then have "\<forall>f fa p.
    action_proj (action_proj (p::('a, 'b) fmap \<times> (_, 'c) fmap) f) fa
    = action_proj p (f \<inter> fa)
  "
    by (metis (no_types) inf.cobounded2 inf_commute subset_proj_absorb_1)
  then show ?thesis
    using assms
    by (metis Diff_Int_distrib2 Diff_empty action_proj_idempot')
qed


lemma disj_proj_proj_eq_proj:
  fixes PROB vs vs'
  assumes "(vs \<inter> vs' = {})"
  shows "prob_proj (prob_proj PROB (prob_dom PROB - vs')) vs = prob_proj PROB vs"
proof -
  {
    fix a
    assume P: "a \<in> PROB"
    moreover have "action_dom (fst a) (snd a) \<subseteq> prob_dom PROB"
      using P exec_as_proj_valid_2
      by blast
    ultimately have "action_proj (action_proj a (prob_dom PROB - vs')) vs = action_proj a vs"
      using assms action_proj_disj_diff[of a "prob_dom PROB" vs' vs]
      by blast
  }
  then show ?thesis
    unfolding prob_proj_def
    by (smt image_cong image_image)
qed


lemma n_replace_proj_le_n_as_2:
  fixes a vs vs'
  assumes "(vs \<subseteq> vs')" "(varset_action a vs')"
  shows "(varset_action (action_proj a vs') vs \<longleftrightarrow> varset_action a vs)"
  unfolding varset_action_def action_proj_def
  using assms
  by (simp add: exec_drest_5 varset_action_def)


\<comment> \<open>NOTE type of `PROB` had to be fixed for use of `empty\_problem\_bound`.\<close>
lemma empty_problem_proj_bound:
  fixes PROB :: "'a problem"
  shows "problem_plan_bound (prob_proj PROB {}) = 0"
proof -
  \<comment> \<open>TODO refactor?\<close>
  {
    have "prob_proj {} {} = {}"
      unfolding prob_proj_def action_proj_def
      using image_empty
      by simp
    moreover {
      assume P: "PROB \<noteq> {}"
      have "\<forall>a. (fmrestrict_set {} (fst a), fmrestrict_set {} (snd a)) = (fmempty, fmempty)"
        using fmrestrict_set_null
        by simp
      then have "prob_proj PROB {} = {(fmempty, fmempty)}"
        unfolding prob_proj_def action_proj_def
        using P
        by auto
    }
    ultimately consider
      (i) "prob_proj PROB {} = {}"
      | (ii) "prob_proj PROB {} = {(fmempty, fmempty)}"
      by (cases "PROB = {}") force+
    then have "prob_dom (prob_proj PROB {}) = {}"
      unfolding prob_dom_def action_dom_def using fmdom'_empty
      by (cases) force+
  }
  then show ?thesis
    using empty_problem_bound[where PROB="prob_proj PROB {}"]
    by blast
qed


lemma problem_plan_bound_works_proj:
  fixes PROB :: "'a problem" and s as vs
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" "(sat_precond_as s as)"
  shows "(\<exists>as'.
    (exec_plan (fmrestrict_set vs s) as' = exec_plan (fmrestrict_set vs s) (as_proj as vs))
    \<and> (length as' \<le> problem_plan_bound (prob_proj PROB vs))
    \<and> (subseq as' (as_proj as vs))
    \<and> (sat_precond_as s as')
    \<and> (no_effectless_act as')
  )"
proof -
  {
    have "exec_plan (fmrestrict_set vs s) (as_proj as vs) = fmrestrict_set vs (exec_plan s as)"
      using assms(4) sat_precond_exec_as_proj_eq_proj_exec
      by blast
    moreover have "fmrestrict_set vs s \<in> valid_states (prob_proj PROB vs)"
      using assms(2) graph_plan_not_eq_last_diff_paths
      by auto
    moreover have "as_proj as vs \<in> valid_plans (prob_proj PROB vs)"
      using assms(3) valid_as_valid_as_proj
      by blast
    moreover have "finite (prob_proj PROB vs)"
      unfolding prob_proj_def
      using assms(1)
      by simp
    ultimately have "\<exists>as'.
      exec_plan (fmrestrict_set vs s) (as_proj as vs) = exec_plan (fmrestrict_set vs s) as'
      \<and> subseq as' (as_proj as vs) \<and> length as' \<le> problem_plan_bound (prob_proj PROB vs)
    "
      using problem_plan_bound_works[of "prob_proj PROB vs"
          "fmrestrict_set vs s" "as_proj as vs"]
      by blast
  }
  then obtain as' where
    "exec_plan (fmrestrict_set vs s) (as_proj as vs) = exec_plan (fmrestrict_set vs s) as'"
    "subseq as' (as_proj as vs) \<and> length as' \<le> problem_plan_bound (prob_proj PROB vs)"
    by fast
  moreover {
    have "
      exec_plan (fmrestrict_set vs s) as
      = exec_plan (fmrestrict_set vs s) (rem_condless_act (fmrestrict_set vs s) [] as)
    "
      using rem_condless_valid_1[of "fmrestrict_set vs s" as]
      by blast
    then have "subseq (rem_condless_act (fmrestrict_set vs s) [] as') as'"
      using rem_condless_valid_8 [of "fmrestrict_set vs s" as']
      by blast
  }
  moreover have "length (rem_condless_act (fmrestrict_set vs s) [] as') \<le> length as'"
    using rem_condless_valid_3[of "fmrestrict_set vs s"]
    by fast
  moreover have 4:
    "sat_precond_as (fmrestrict_set vs s) (rem_condless_act (fmrestrict_set vs s) [] as')"
    using rem_condless_valid_2[of "fmrestrict_set vs s" as']
    by blast
  moreover have "
    exec_plan (fmrestrict_set vs s) (rem_condless_act (fmrestrict_set vs s) [] as')
    = exec_plan (fmrestrict_set vs s)
      (rem_effectless_act (rem_condless_act (fmrestrict_set vs s) [] as'))
  "
    using rem_effectless_works_1[of "fmrestrict_set vs s"
        "rem_condless_act (fmrestrict_set vs s) [] as'"]
    by blast
  moreover {
    have "
      subseq (rem_effectless_act (rem_condless_act (fmrestrict_set vs s) [] as))
     (rem_condless_act (fmrestrict_set vs s) [] as)
    "
      using rem_effectless_works_9[of
          "(rem_condless_act (fmrestrict_set vs s) [] (as :: 'a action list))"]
      by blast
    then have "
      length (rem_effectless_act (rem_condless_act (fmrestrict_set vs s) [] as'))
      \<le> length (rem_condless_act (fmrestrict_set vs s) [] as')
    "
      using rem_effectless_works_3[of
          "(rem_condless_act (fmrestrict_set vs s) [] (as' :: 'a action list))"]
      by simp
    then have "
      sat_precond_as (fmrestrict_set vs s)
      (rem_effectless_act (rem_condless_act (fmrestrict_set vs s) [] as'))
    "
      using 4 rem_effectless_works_2[of "fmrestrict_set vs s"
          "(rem_condless_act (fmrestrict_set vs s) [] as')"]
      by blast
    then have
      "no_effectless_act (rem_effectless_act (rem_condless_act (fmrestrict_set vs s) [] as'))"
      using rem_effectless_works_6[of "(rem_condless_act (fmrestrict_set vs s) [] (as' ::'a action list))"]
      by simp
  }
  ultimately show ?thesis
    using rem_effectless_works_13 rem_condless_valid_1 order_trans
      no_effectless_proj sat_precond_drest_sat_precond subseq_order.order_trans
    by (metis (no_types, lifting))
qed


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into `Fmap\_Utils`.\<close>
lemma action_proj_inter_i: "fmrestrict_set V (fmrestrict_set W f) = fmrestrict_set (V \<inter> W) f"
  unfolding fmfilter_alt_defs(4)
  by simp

lemma action_proj_inter: "action_proj (action_proj a vs1) vs2 = action_proj a (vs1 \<inter> vs2)"
proof -
  have
    "fmrestrict_set vs2 (fmrestrict_set vs1 (fst a)) = fmrestrict_set (vs1 \<inter> vs2) (fst a)"
    "fmrestrict_set vs2 (fmrestrict_set vs1 (snd a)) = fmrestrict_set (vs1 \<inter> vs2) (snd a)"
    using inf_commute action_proj_inter_i
    by metis+
  then show ?thesis
    unfolding action_proj_def
    by simp
qed

lemma prob_proj_inter: "prob_proj (prob_proj PROB vs1) vs2 = prob_proj PROB (vs1 \<inter> vs2)"
  unfolding prob_proj_def
  using set_eq_iff image_iff action_proj_inter
  supply[[smt_timeout=100]]
  by (smt image_cong image_image)


subsection "Snapshotting"

text \<open> A snapshot is an abstraction concept of the system in which the assignment of a set of
variables is fixed and actions whose preconditions or effects violate the fixed assignments are
eliminated. [Abdulaziz et al., p.28]

Formally this notion is build on the definition of agreement of states (`agree`), which
states that variables `v`, `v'`in the shared domain of two states must be assigned to the same
value. A snapshot w.r.t to a state `s` is then defined as the set of actions of a problem where the
precondition and the effect agree. [Abdulaziz et al., Definition 16, HOL4 Definition 16, p.28] \<close>


\<comment> \<open>NOTE  name shortened.\<close>
definition agree where
  "agree s1 s2 \<equiv> (\<forall>v. (v \<in> fmdom' s1) \<and> (v \<in> fmdom' s2) \<longrightarrow> (fmlookup s1 v = fmlookup s2 v))"


\<comment> \<open>NOTE added lemma.\<close>
lemma state_succ_fixpoint_if:
  fixes a s PROB
  assumes "a \<in> PROB" "(s \<in> valid_states PROB)" "fst a \<subseteq>\<^sub>f s" "agree (snd a) s"
  shows "state_succ s a = s"
proof -
  {
    have "fmdom' (snd a) \<subseteq> fmdom' s"
      using assms(1, 2) FDOM_eff_subset_FDOM_valid_states_pair
      by blast
    moreover have "\<forall>x. x \<in> fmdom' (snd a) \<longrightarrow> fmlookup (snd a) x = fmlookup s x"
      using assms(4) calculation(1) agree_def subsetCE
      by metis
    moreover have "s ++\<^sub>f snd a = s"
      using calculation(2)
      by (metis fmap_ext fmdom'_notD fmdom_notI fmlookup_add)
  }
  then show ?thesis
    using fmap_add_ltr_def state_succ_def
    by metis
qed


lemma agree_state_succ_idempot:
  assumes "(a \<in> PROB)" "(s \<in> valid_states PROB)" "(agree (snd a) s)"
  shows "(state_succ s a = s)"
proof (cases "fst a \<subseteq>\<^sub>f s")
  case True
  then show ?thesis
    using assms state_succ_fixpoint_if
    by blast
next
  case False
  then show ?thesis
    unfolding state_succ_def fmap_add_ltr_def
    by simp
qed


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into `Fmap\_Utils`.\<close>
lemma fmdom'_fmrestrict_set:
  fixes X f
  shows "fmdom' (fmrestrict_set X f) = X \<inter> (fmdom' f)"
  unfolding fmdom'_alt_def fmfilter_alt_defs(4)
  by auto

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into 'Fmap\_Utils'.\<close>
lemma fmdom'_fmrestrict_set_fmadd:
  fixes X f g
  shows "fmdom' (fmrestrict_set X (f ++\<^sub>f g)) = X \<inter> (fmdom' f \<union> fmdom' g)"
proof -
  have "fmrestrict_set X (f ++\<^sub>f g) = fmrestrict_set X f ++\<^sub>f fmrestrict_set X g"
    using fmrestrict_set_add_distrib
    by fast
  then show ?thesis
    using fmdom'_fmrestrict_set fmdom'_add
    by metis
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into 'Fmap\_Utils'.\<close>
lemma fmrestrict_agree:
  fixes X x f g
  assumes "agree (fmrestrict_set X f) (fmrestrict_set X g)" "x \<in> X \<inter> fmdom' f \<inter> fmdom' g"
  shows "fmlookup (fmrestrict_set X f) x = fmlookup (fmrestrict_set X g) x"
proof -
  {
    fix v
    assume "v \<in> X \<inter> fmdom' f \<inter> fmdom' g"
    then have "v \<in> fmdom' (fmrestrict_set X f) \<and> v \<in> fmdom' (fmrestrict_set X g)"
      using fmdom'_fmrestrict_set
      by force
    then have "fmlookup (fmrestrict_set X f) v = fmlookup (fmrestrict_set X g) v"
      using assms(1)
      unfolding agree_def
      by blast
  }
  then show ?thesis
    using assms
    by blast
qed

lemma agree_restrict_state_succ_idempot:
  assumes "(a \<in> PROB)" "(s \<in> valid_states PROB)"
    "(agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s))"
  shows "(fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s)"
proof (cases "fst a \<subseteq>\<^sub>f s")
  case True
  then have "state_succ s a = s ++\<^sub>f snd a"
    unfolding state_succ_def fmap_add_ltr_def
    by simp
  {
    fix v
    have "fmlookup (fmrestrict_set vs (s ++\<^sub>f snd a)) v = fmlookup (fmrestrict_set vs s) v"
    proof (cases "v \<in> fmdom' (snd a)")
      case True
      then have 1: "fmdom' (fmrestrict_set vs (s ++\<^sub>f snd a)) = vs \<inter> (fmdom' s \<union> fmdom' (snd a))"
        unfolding fmap_add_ltr_def
        using fmdom'_fmrestrict_set_fmadd
        by metis
      then have 2: "fmdom' (fmrestrict_set vs (snd a)) = vs \<inter> fmdom' (snd a)"
        using fmdom'_fmrestrict_set
        by metis
      then show ?thesis
        using 1 2
      proof (cases "v \<in> vs")
        case true: True
        then show ?thesis
        proof (cases "v \<in> (fmdom' s \<inter> fmdom' (snd a))")
          case True
          then have "v \<in> vs \<inter> fmdom' s \<inter> fmdom' (snd a)"
            using true
            by blast
          then have "fmlookup (fmrestrict_set vs (snd a)) v = fmlookup (fmrestrict_set vs s) v"
            using assms(3) fmrestrict_agree
            by fast
          then show ?thesis
            by fastforce
        next
          case False
          then have "fmdom' (snd a) \<subseteq> fmdom' s"
            using assms(1, 2) FDOM_eff_subset_FDOM_valid_states_pair
            by metis
          then have "v \<notin> fmdom' (snd a)"
            using true False
            by blast
          then show ?thesis
            by fastforce
        qed
      qed auto
    qed fastforce
  }
  then show ?thesis
    unfolding state_succ_def fmap_add_ltr_def
    using fmap_ext
    by metis
next
  case False
  then show ?thesis
    unfolding state_succ_def
    by simp
qed


lemma agree_exec_idempot:
  assumes "(as \<in> valid_plans PROB)" "(s \<in> valid_states PROB)"
    "(\<forall>a. ListMem a as \<longrightarrow> agree (snd a) s)"
  shows "(exec_plan s as = s)"
  using assms
proof (induction as arbitrary: PROB s)
  case (Cons a as)
  then have 1: "a \<in> PROB"
    using Cons.prems(1) valid_plan_valid_head
    by fast
  then have 2: "as \<in> valid_plans PROB"
    using Cons.prems(1) valid_plan_valid_tail
    by fast
  then have 3: "\<forall>a. ListMem a as \<longrightarrow> agree (snd a) s"
    using Cons.prems(3) ListMem.simps
    by metis
  then have "ListMem a (a # as)"
    using elem
    by fast
  then have "agree (snd a) s"
    using Cons.prems(3)
    by blast
  then have 4: "state_succ s a = s"
    using Cons.prems(1, 2) 1 agree_state_succ_idempot
    by blast
  then have "exec_plan s as = s"
    using Cons.IH Cons.prems(2) 2 3
    by blast
  then show ?case
    using 4
    by simp
qed simp


lemma agree_restrict_exec_idempot:
  fixes s s'
  assumes "(as \<in> valid_plans PROB)" "(s' \<in> valid_states PROB)" "(s \<in> valid_states PROB)"
    "(\<forall>a. ListMem a as \<longrightarrow> agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s))"
    "(fmrestrict_set vs s' = fmrestrict_set vs s)"
  shows  "(fmrestrict_set vs (exec_plan s' as) = fmrestrict_set vs s)"
  using assms
proof (induction as arbitrary: PROB s s' vs)
  case (Cons a as)
  have 1: "as \<in> valid_plans PROB"
    using Cons.prems(1) valid_plan_valid_tail
    by fast
  then have 2: "\<forall>a. ListMem a as \<longrightarrow> agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s)"
    using Cons.prems(4) ListMem.simps
    by metis
  then have 3: "a \<in> PROB"
    using Cons.prems(1) valid_plan_valid_head
    by metis
  moreover
  {
    have "ListMem a (a # as)"
      using elem
      by fast
    then have "agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s)"
      using Cons.prems(4) calculation(1)
      by blast
    then  have "agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s')"
      using Cons.prems(5)
      by simp
  }
  ultimately show ?case
    using assms
  proof (cases "fst a \<subseteq>\<^sub>f s'")
    case True
    {
      have a: "s' \<in> valid_states PROB"
        using Cons.prems(2)
        by simp
      moreover have "state_succ s' a \<in> valid_states PROB"
        using 3 a lemma_1_i
        by blast
      moreover have
        " \<forall>a. ListMem a as \<longrightarrow> agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s)"
        using 2
        by blast
      moreover {
        have "ListMem a (a # as)"
          using elem
          by fast
        then have "agree (fmrestrict_set vs (snd a)) (fmrestrict_set vs s)"
          using Cons.prems(4) calculation(1)
          by blast
        then have "fmrestrict_set vs (state_succ s' a) = fmrestrict_set vs s"
          using Cons.prems(5) 3 a agree_restrict_state_succ_idempot
          by metis
      }
      ultimately have "fmrestrict_set vs (exec_plan (state_succ s' a) as) = fmrestrict_set vs s"
        using assms(3) 1 Cons.IH[where s'="state_succ s' a"]
        by auto
    }
    then show ?thesis
      by simp
  next case False
    moreover have "exec_plan s' (a # as) = exec_plan s' as"
      using False
      by (simp add: state_succ_def)
    ultimately show ?thesis
      using Cons.IH Cons.prems(2, 3, 5) 1 2
      by presburger
  qed
qed simp


lemma agree_restrict_exec_idempot_pair:
  fixes s s'
  assumes "(as \<in> valid_plans PROB)" "(s' \<in> valid_states PROB)" "(s \<in> valid_states PROB)"
    "(\<forall>p e. ListMem (p, e) as \<longrightarrow> agree (fmrestrict_set vs e) (fmrestrict_set vs s))"
    "(fmrestrict_set vs s' = fmrestrict_set vs s)"
  shows "(fmrestrict_set vs (exec_plan s' as) = fmrestrict_set vs s)"
  using assms agree_restrict_exec_idempot
  by fastforce


lemma agree_comm: "agree x x' = agree x' x"
  unfolding agree_def
  by fastforce


lemma restricted_agree_imp_agree:
  assumes "(fmdom' s2 \<subseteq> vs)" "(agree (fmrestrict_set vs s1) s2)"
  shows "(agree s1 s2)"
  using assms contra_subsetD fmlookup_restrict_set Int_iff fmdom'_fmrestrict_set
  unfolding agree_def
  by metis


lemma agree_imp_submap:
  assumes "f1 \<subseteq>\<^sub>f f2"
  shows "agree f1 f2"
  using assms
  unfolding agree_def
  by (simp add: as_needed_asses_submap_exec_ii)


lemma agree_FUNION:
  assumes "(agree fm fm1)" "(agree fm fm2)"
  shows "(agree fm (fm1 ++ fm2))"
  unfolding agree_def fmap_add_ltr_def
  using assms
  by (metis agree_def fmlookup_add fmlookup_dom'_iff)


lemma agree_fm_list_union:
  fixes fm
  assumes "(\<forall>fm'. ListMem fm' fmList \<longrightarrow> agree fm fm')"
  shows "(agree fm (foldr fmap_add_ltr fmList fmempty))"
  using assms proof (induction "fmList" arbitrary: fm)
  case Nil
  then have "foldr fmap_add_ltr [] fmempty = fmempty"
    using Nil
    by simp
  then show ?case
    unfolding agree_def
    by auto
next
  case (Cons a fmList)
  then have "\<forall>fm'. ListMem fm' fmList \<longrightarrow> agree fm fm'"
    using Cons.prems insert
    by fast
  then have 1: "agree fm (foldr fmap_add_ltr fmList fmempty)"
    using Cons.IH
    by blast
  then have "agree fm a"
    using Cons.prems elem
    by fast
  then have "agree fm (a ++ foldr fmap_add_ltr fmList fmempty)"
    using 1 agree_FUNION
    by blast
  then show ?case
    by simp
qed


lemma DRESTRICT_EQ_AGREE:
  assumes "(fmdom' s2 \<subseteq> vs2)" "(fmdom' s1 \<subseteq> vs1)"
  shows "((fmrestrict_set vs2 s1 = fmrestrict_set vs1 s2) \<longrightarrow> agree s1 s2)"
  using assms fmdom'_restrict_set restricted_agree_imp_agree
  by (metis agree_def)


lemma  SUBMAPS_AGREE: "(s1 \<subseteq>\<^sub>f s) \<and> (s2 \<subseteq>\<^sub>f s) \<Longrightarrow> (agree s1 s2)"
  unfolding agree_def
  by (metis as_needed_asses_submap_exec_ii)


\<comment> \<open>NOTE name shortened.\<close>
definition snapshot where
  "snapshot PROB s = {a | a. a \<in> PROB \<and> agree (fst a) s \<and> agree (snd a) s}"


lemma snapshot_pair: "snapshot PROB s = {(p, e). (p, e) \<in> PROB \<and> agree p s \<and> agree e s}"
  unfolding snapshot_def
  by fastforce

lemma action_agree_valid_in_snapshot:
  assumes "(a \<in> PROB)" "(agree (fst a) s)" "(agree (snd a) s)"
  shows "(a \<in> snapshot PROB s)"
  unfolding snapshot_def
  using assms
  by blast

lemma as_mem_agree_valid_in_snapshot:
  assumes "(\<forall>a. ListMem a as \<longrightarrow> agree (fst a) s \<and> agree (snd a) s)" "(as \<in> valid_plans PROB)"
  shows "(as \<in> valid_plans (snapshot PROB s))"
  using assms
proof (induction as)
  case Nil
  then show ?case
    using empty_plan_is_valid
    by blast
next
  case (Cons a as)
  {
    have "\<forall>a. ListMem a as \<longrightarrow> agree (fst a) s \<and> agree (snd a) s"
      using Cons.prems(1) insert
      by fast
    moreover have "(as \<in> valid_plans PROB)"
      using Cons.prems(2) valid_plan_valid_tail
      by fast
    ultimately have "set as \<subseteq> snapshot PROB s"
      using Cons.IH valid_plans_def
      by fast
  }
  note 1 = this
  {
    have a: "a \<in> PROB"
      using Cons.prems(2) valid_plan_valid_head
      by metis
    then have "ListMem a (a # as)"
      using elem
      by fast
    then have "agree (fst a) s \<and> agree (snd a) s"
      using Cons.prems(1)
      by blast
    then have "a \<in> snapshot PROB s"
      using a snapshot_def
      by auto
  }
  then have "set (a # as) \<subseteq> snapshot PROB s"
    using 1 set_simps(2)
    by simp
  then show ?case using valid_plans_def
    by blast
qed

lemma fmrestrict_agree_monotonous:
  fixes f g X
  assumes "agree f g"
  shows "agree (fmrestrict_set X f) (fmrestrict_set X g)"
proof -
  let ?F="fmdom' (fmrestrict_set X f)"
  let ?G="fmdom' (fmrestrict_set X g)"
  have 1: "?F = X \<inter> fmdom' f" "?G = X \<inter> fmdom' g"
    using fmdom'_fmrestrict_set
    by metis+
  {
    fix v
    assume "v \<in> ?F" "v \<in> ?G"
    then have "v \<in> fmdom' f" "v \<in> fmdom' g"
      using 1
      by blast+
    then have "fmlookup f v = fmlookup g v"
      using assms
      unfolding agree_def
      by blast
    then have "fmlookup (fmrestrict_set X f) v = fmlookup (fmrestrict_set X g) v"
      unfolding fmlookup_restrict_set
      by argo
  }
  then show ?thesis
    using assms
    unfolding agree_def
    by blast
qed

\<comment> \<open>TODO remove if not used.\<close>
lemma SUBMAP_FUNION_DRESTRICT_i:
  fixes v vsa vsb f g
  assumes "v \<in> vsa"
  shows "
    fmlookup (fmrestrict_set ((vsa \<union> vsb) \<inter> vs) f) v
    = fmlookup (fmrestrict_set (vsa \<inter> vs) f) v
  "
  unfolding fmlookup_restrict_set
  using assms
  by auto


lemma SUBMAP_FUNION_DRESTRICT':
  assumes "(agree fma fmb)" "(vsa \<subseteq> fmdom' fma)" "(vsb \<subseteq> fmdom' fmb)"
    "(fmrestrict_set vsa fm  = fmrestrict_set (vsa \<inter> vs) fma)"
    "(fmrestrict_set vsb fm = fmrestrict_set (vsb \<inter> vs) fmb)"
  shows "(fmrestrict_set (vsa \<union> vsb) fm = fmrestrict_set ((vsa \<union> vsb) \<inter> vs) (fma ++ fmb))"
proof -
  let ?f="fmrestrict_set (vsa \<union> vsb) fm"
  let ?g="fmrestrict_set ((vsa \<union> vsb) \<inter> vs) (fma ++ fmb)"
  have 1: "?g = fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fmb ++\<^sub>f fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fma"
    unfolding fmap_add_ltr_def fmrestrict_set_add_distrib
    by simp
  have 2: "agree (fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fma) (fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fmb)"
    using assms(1) fmrestrict_agree_monotonous
    by blast
  have 3:
    "fmdom' (fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fma) = ((vsa \<union> vsb) \<inter> vs) \<inter> fmdom' fma"
    "fmdom' (fmrestrict_set ((vsa \<union> vsb) \<inter> vs) fmb) = ((vsa \<union> vsb) \<inter> vs) \<inter> fmdom' fmb"
    using fmdom'_fmrestrict_set
    by metis+
  {
    fix v
    have "fmlookup ?f v = fmlookup ?g v"
    proof (cases "v \<in> ((vsa \<union> vsb) \<inter> vs)")
      case True
        \<comment> \<open>TODO unwrap smt proof.\<close>
      then show ?thesis
        using assms(1, 2, 3, 4, 5) 1
        by (smt IntD1 SUBMAP_FUNION_DRESTRICT_i UnE agree_def domIff fmdom'.rep_eq fmdom'_alt_def
            fmdom'_fmrestrict_set fmlookup_add fmlookup_restrict_set inf_sup_distrib2 notin_fset
            subset_iff sup_commute)
    next
      case False
      then show ?thesis
      proof -
        have "v \<notin> vsa \<union> vsb \<or> v \<notin> vs"
          using False
          by blast
        then have "fmlookup (fmrestrict_set (vsa \<union> vsb) fm) v = None"
          using assms(4, 5)
          by (metis Int_iff Un_iff fmlookup_restrict_set)
        then show ?thesis
          using False
          by auto
      qed
    qed
  }
  then show ?thesis
    using 1 fmap_ext
    by blast
qed

lemma UNION_FUNION_DRESTRICT_SUBMAP:
  assumes "(vs1 \<subseteq> fmdom' fma)" "(vs2 \<subseteq> fmdom' fmb)" "(agree fma fmb)"
    "(fmrestrict_set vs1 fma \<subseteq>\<^sub>f s)" "(fmrestrict_set vs2 fmb \<subseteq>\<^sub>f s)"
  shows "(fmrestrict_set (vs1 \<union> vs2) (fma ++ fmb) \<subseteq>\<^sub>f s)"
proof -
  {
    let ?f="fmrestrict_set (vs1 \<union> vs2) (fma ++ fmb)"
    fix v
    assume P: "v \<in> fmdom' ?f"
    {
      have "v \<in> (vs1 \<union> vs2) \<inter> (fmdom' fma \<union> fmdom' fmb)"
        using P
        unfolding fmap_add_ltr_def fmdom'_fmrestrict_set fmdom'_add
        by force
      then have "v \<in> vs1 \<union> vs2" "v \<in> fmdom' fma \<union> fmdom' fmb"
        by fast+
    }
    note 1 = this
    then have 2: "fmlookup ?f v = fmlookup (fmb ++\<^sub>f fma) v"
      unfolding fmlookup_restrict_set fmap_add_ltr_def
      by argo
    then consider
      (i) "v \<in> vs1"
      | (ii) "v \<in> vs2"
      | (iii) "\<not>v\<in> vs1 \<and> \<not>v\<in>vs2"
      by blast
    then have "fmlookup ?f v = fmlookup s v"
    proof (cases)
      case i
      then have "v \<in> fmdom' fma"
        using assms(1)
        by blast
      then have "fmlookup ?f v = fmlookup fma v"
        unfolding 2 fmlookup_add
        by (simp add: fmdom'_alt_def notin_fset)
      also have "\<dots> = fmlookup (fmrestrict_set vs1 fma) v"
        unfolding fmlookup_restrict_set
        using i
        by simp
      finally show ?thesis
        using assms(4)
        by (metis (mono_tags, lifting) P domIff fmdom'_notI fmsubset.rep_eq map_le_def)
    next
      \<comment> \<open>TODO unwrap smt proof.\<close>
      case ii
      then show ?thesis
        using assms(2, 3, 5) 2 P
        by (smt SUBMAP_FUNION_DRESTRICT_i agree_def
            fmdom'.rep_eq fmdom'_fmrestrict_set fmdom'_notD fmdom'_notI fmlookup_add
            fmrestrict_set_dom fmsubset.rep_eq inf.orderE map_le_def subset_Un_eq)
    next
      case iii
      then show ?thesis
        using 1
        by blast
    qed
  }
  then show ?thesis
    by (simp add: as_needed_asses_submap_exec_vii)
qed

\<comment> \<open>TODO unwrap sledgehammered metis proof.\<close>
(* TODO duplicate lemma? *)
lemma agree_DRESTRICT:
  assumes "agree s1 s2"
  shows "agree (fmrestrict_set vs s1) (fmrestrict_set vs s2)"
  using assms by (fact fmrestrict_agree_monotonous)

lemma agree_DRESTRICT_2:
  assumes "(fmdom' s1 \<subseteq> vs1)" "(fmdom' s2 \<subseteq> vs2)" "(agree s1 s2)"
  shows "(agree (fmrestrict_set vs2 s1) (fmrestrict_set vs1 s2))"
  using assms
  unfolding agree_def fmdom'_restrict_set_precise
  by auto

\<comment> \<open>NOTE added lemma.\<close>
lemma snapshot_eq_filter:
  shows "snapshot PROB s = Set.filter (\<lambda>a. agree (fst a) s \<and> agree (snd a) s) PROB"
  unfolding snapshot_def Set.filter_def
  by presburger

\<comment> \<open>NOTE moved up.\<close>
corollary snapshot_subset:
  shows "snapshot PROB s \<subseteq> PROB"
  unfolding snapshot_def
  using snapshot_eq_filter
  by blast

lemma FINITE_snapshot:
  assumes "finite PROB"
  shows "finite (snapshot PROB s)"
proof -
  have "snapshot PROB s \<subseteq> PROB"
    using snapshot_subset
    by blast
  then show ?thesis
    using assms finite_subset[of "snapshot PROB s" PROB]
    by blast
qed

\<comment> \<open>NOTE moved up (declared above the previous lemma).
lemma snapshot\_subset\<close>

\<comment> \<open>TODO unwrap metis proof.\<close>
lemma dom_proj_snapshot:
  "prob_dom (prob_proj PROB (prob_dom (snapshot PROB s))) = prob_dom (snapshot PROB s)"
  by (metis snapshot_subset two_children_parent_mems_le_finite prob_subset_dom_subset)

lemma valid_states_snapshot:
  "valid_states (prob_proj PROB (prob_dom (snapshot PROB s))) = valid_states (snapshot PROB s)"
  by (metis dom_proj_snapshot valid_states_def)

lemma valid_proj_neq_succ_restricted_neq_succ:
  assumes "(x' \<in> prob_proj PROB vs)" "(state_succ s x' \<noteq> s)"
  shows "(fmrestrict_set vs (state_succ s x') \<noteq> fmrestrict_set vs s)"
  unfolding state_succ_def
  using FDOM_eff_subset_prob_dom_pair dom_prob_proj limited_dom_neq_restricted_neq
  using assms(1, 2)
  by (smt dual_order.trans state_succ_def)

lemma proj_successors: "
  ((\<lambda>s. fmrestrict_set vs s) ` (state_successors (prob_proj PROB vs) s))
   \<subseteq> (state_successors (prob_proj PROB vs) (fmrestrict_set vs s))
"
proof -
  let ?A="((\<lambda>s. fmrestrict_set vs s) ` (state_successors (prob_proj PROB vs) s))"
  let ?B="(state_successors (prob_proj PROB vs) (fmrestrict_set vs s))"
  {
    fix x
    assume P: "x \<in> ?A"
    then obtain x' x'' where a:
      "x'' \<in> prob_proj PROB vs" "x' = state_succ s x''" "x' \<noteq> s" "x = fmrestrict_set vs x'"
      unfolding state_successors_def subset_iff
      by blast
    moreover {
      have "(\<exists>x''.
        x'' \<in> prob_proj PROB vs \<and> x = state_succ (fmrestrict_set vs s) x''
        \<and> x \<noteq> fmrestrict_set vs s)"
      proof (cases "fst x'' \<subseteq>\<^sub>f s")
        case true: True
        then show ?thesis
        proof (cases "fst x'' \<subseteq>\<^sub>f fmrestrict_set vs s")
          case True
          {
            have "fmdom' (snd x'') \<subseteq> vs"
              using a(1) FDOM_eff_subset_prob_dom_pair dom_prob_proj dual_order.trans
              by metis
            then have "fmrestrict_set vs (snd x'') = snd x''"
              using exec_drest_5
              by fast
          }
          note i = this
          {
            have "x = fmrestrict_set vs (snd x'' ++ s)"
              using a(2, 4) true
              unfolding state_succ_def
              by simp
            then have "x = fmrestrict_set vs (snd x'') ++ fmrestrict_set vs s"
              unfolding fmap_add_ltr_def
              using fmrestrict_set_add_distrib
              by simp
            then have "x = snd x'' ++ fmrestrict_set vs s"
              using i
              by simp
            then have "x = state_succ (fmrestrict_set vs s) x''"
              unfolding state_succ_def
              using True
              by argo
          }
          moreover have  "x \<noteq> fmrestrict_set vs s"
            using a valid_proj_neq_succ_restricted_neq_succ
            by fast
          ultimately show ?thesis
            using a(1)
            by blast
        next
          case False
          then show ?thesis
          proof -
            have "x'' \<in> (\<lambda>p. action_proj p vs) ` PROB"
              using calculation(1) prob_proj_def
              by auto
            then have "action_proj x'' vs = x''"
              using action_proj_idempot
              by blast
            then show ?thesis
              by (metis (no_types) False action_proj_pair fmsubset_restrict_set_mono fstI
                  surjective_pairing true)
          qed
        qed
      next
        case False
        then show ?thesis
        proof (cases "fst x'' \<subseteq>\<^sub>f fmrestrict_set vs s")
          case True
          then have "fmdom' (snd x'') \<subseteq> vs"
            using FDOM_eff_subset_prob_dom_pair dom_prob_proj
            using a(1) dual_order.trans
            by metis
          then have "fmrestrict_set vs (snd x'') = snd x''"
            using exec_drest_5
            by fast
          then show ?thesis
            unfolding state_succ_def fmap_add_ltr_def
            using False True sublist_as_proj_eq_as_1
            by fast
        next
          case False
          then have "fmdom' (fst x'') \<subseteq> vs"
            using FDOM_pre_subset_prob_dom_pair dom_prob_proj
            using a(1) dual_order.trans
            by metis
          then have "fmrestrict_set vs (fst x'') = fst x''"
            by (simp add: exec_drest_5)
          then show ?thesis
            unfolding state_succ_def fmap_add_ltr_def
            using a False fmsubset_restrict_set_mono
            by (metis state_succ_def)
        qed
      qed
    }
    then obtain x'' where "x'' \<in> prob_proj PROB vs" "x = state_succ (fmrestrict_set vs s) x''"
      "x \<noteq> fmrestrict_set vs s"
      by blast
    then have "x \<in> ?B" unfolding state_successors_def
      by blast
  }
  then show ?thesis
    by blast
qed

lemma  state_in_successor_proj_in_state_in_successor: "
  (s' \<in> state_successors (prob_proj PROB vs) s)
  \<Longrightarrow> (fmrestrict_set vs s'  \<in> state_successors (prob_proj PROB vs) (fmrestrict_set vs s))"
  using proj_successors
  by force

lemma proj_FDOM_eff_subset_FDOM_valid_states:
  fixes p e s
  assumes "((p, e) \<in> prob_proj PROB vs)" "(s \<in> valid_states PROB)"
  shows "(fmdom' e \<subseteq> fmdom' s)"
  using assms
proof -
  {
    obtain p' e' where "(p', e') \<in> PROB" "(p, e) = action_proj (p', e') vs"
      using assms(1)
      unfolding prob_proj_def
      by fast
    then have "fmdom' e \<subseteq> prob_dom (prob_proj PROB vs)"
      using assms FDOM_eff_subset_prob_dom
      by blast
    also have "\<dots> = prob_dom PROB \<inter> vs"
      using graph_plan_neq_mems_state_set_neq_len
      by fast
    finally have "fmdom' e \<subseteq> prob_dom PROB"
      by simp
  }
  moreover have "fmdom' s = prob_dom PROB"
    using assms(2)
    unfolding valid_states_def
    by simp
  ultimately show ?thesis
    by simp
qed

lemma valid_proj_action_valid_succ:
  assumes "(h \<in> prob_proj PROB vs)" "(s \<in> valid_states PROB)"
  shows "(state_succ s h \<in> valid_states PROB)"
proof -
  have "fmdom' (snd h) \<subseteq> fmdom' s"
    using assms proj_FDOM_eff_subset_FDOM_valid_states surjective_pairing
    by metis
  moreover have "fmdom' (state_succ s h) = fmdom' s"
    using calculation(1) FDOM_state_succ
    by metis
  ultimately show ?thesis
    using assms(2) valid_states_def
    by blast
qed

lemma proj_successors_of_valid_are_valid:
  assumes "(s \<in> valid_states PROB)"
  shows "(state_successors (prob_proj PROB vs) s \<subseteq> (valid_states PROB))"
  unfolding state_successors_def
  using assms valid_proj_action_valid_succ
  by blast

subsection "State Space Projection"

\<comment> \<open>NOTE  name shortened.\<close>
definition ss_proj where
  "ss_proj ss vs \<equiv> (\<lambda>s. fmrestrict_set vs s) ` ss"

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into 'Fmap\_Utils'.\<close>
lemma fmrestrict_set_inter_img:
  fixes A X Y
  shows "fmrestrict_set (X \<inter> Y) ` A = (fmrestrict_set X \<circ> fmrestrict_set Y) ` A"
proof -
  \<comment> \<open>NOTE Proof by mutual inclusion.\<close>
  let ?lhs = "fmrestrict_set (X \<inter> Y) ` A"
  let ?rhs = "(fmrestrict_set X \<circ> fmrestrict_set Y) ` A"
  {
    fix a
    assume "a \<in> A"
    have "(fmrestrict_set X \<circ> fmrestrict_set Y) a = fmrestrict_set X (fmrestrict_set Y a)"
      by auto
    also have "\<dots> = fmrestrict_set (X \<inter> Y) a"
      using action_proj_inter_i
      by fast
    finally have "(fmrestrict_set X \<circ> fmrestrict_set Y) a = fmrestrict_set (X \<inter> Y) a"
      by auto
  }
  note 1 = this
  {
    fix a
    assume P: "a \<in> A"
    then have "fmrestrict_set (X \<inter> Y) a \<in> ?lhs"
      by simp
    moreover have "(fmrestrict_set X \<circ> fmrestrict_set Y) a \<in> ?rhs"
      using P
      by blast
    ultimately have
      "fmrestrict_set (X \<inter> Y) a \<in> ?rhs" "(fmrestrict_set X \<circ> fmrestrict_set Y) a \<in> ?lhs"
      using P 1
      by metis+
  }
  then show ?thesis
    by blast
qed

lemma invariantStateSpace_thm_9:
  fixes ss vs1 vs2
  shows "ss_proj ss (vs1 \<inter> vs2) = ss_proj (ss_proj ss vs2) vs1"
proof -
  {
    have "
      ss_proj ss (vs1 \<inter> vs2)
      = fmrestrict_set (vs1 \<inter> vs2) ` ss
    "
      unfolding ss_proj_def
      by simp
    also have "\<dots> = (fmrestrict_set vs1 \<circ> fmrestrict_set vs2) ` ss"
      using fmrestrict_set_inter_img
      by metis
    finally have "ss_proj ss (vs1 \<inter> vs2) = ss_proj (ss_proj ss vs2) vs1"
      unfolding ss_proj_def
      by force
  }
  then show ?thesis
    by simp
qed

lemma FINITE_ss_proj:
  fixes ss vs
  assumes "finite ss"
  shows "finite (ss_proj ss vs)"
  unfolding ss_proj_def
  using assms
  by simp

lemma nempty_stateSpace_nempty_ss_proj:
  assumes "(ss \<noteq> {})"
  shows "(ss_proj ss vs \<noteq> {})"
  unfolding ss_proj_def
  using assms
  by simp

lemma invariantStateSpace_thm_5:
  fixes ss vs domain
  assumes "(stateSpace ss domain)"
  shows "(stateSpace (ss_proj ss vs) (domain \<inter> vs))"
  using assms
  unfolding stateSpace_def ss_proj_def
  by (metis (no_types, lifting) fmdom'_fmrestrict_set imageE inf_commute)

lemma dom_subset_ssproj_eq_ss:
  fixes ss domain vs
  assumes "(stateSpace ss domain)" "(domain \<subseteq> vs)"
  shows "(ss_proj ss vs = ss)"
  unfolding ss_proj_def stateSpace_def
  using assms exec_drest_5
  by (metis (mono_tags, lifting) image_cong image_ident stateSpace_def)

\<comment> \<open>TODO refactor duplicate proof steps in case split.\<close>
lemma  neq_vs_neq_ss_proj:
  fixes vs
  assumes "(ss \<noteq> {})" "(stateSpace ss vs)" "(vs1 \<subseteq> vs)" "(vs2 \<subseteq> vs)" "(vs1 \<noteq> vs2)"
  shows "(ss_proj ss vs1 \<noteq> ss_proj ss vs2)"
proof -
  {
    have 1: "\<exists>f. f \<in> ss"
      using assms(1)
      by blast
    then obtain x where " (x \<in> vs1 \<and> x \<notin> vs2) \<or> (x \<in> vs2 \<and> x \<notin> vs1)"
      using assms(5)
      by blast
    then consider (i) "x \<in> vs1 \<and> x \<notin> vs2" | (ii) "x \<in> vs2 \<and> x \<notin> vs1"
      by blast
    then have "fmrestrict_set vs1 ` ss \<noteq>  fmrestrict_set vs2 ` ss" proof (cases)
      case i
      {
        fix s' t'
        assume "s' \<in> fmrestrict_set vs1 ` ss" "t' \<in> fmrestrict_set vs2 ` ss"
        then obtain s t where a:
          "s \<in> ss" "s' = fmrestrict_set vs1 s" "t \<in> ss" "t' = fmrestrict_set vs2 t"
          by blast
        then have "fmdom' s = vs"
          using assms(2)
          by (simp add: stateSpace_def)
        then have b: "fmdom' s' = vs1"
          using assms(3) a fmdom'_fmrestrict_set inf.order_iff
          by metis
        then have "fmdom' t = vs"
          using assms(2) a(3)
          by (simp add: stateSpace_def)
        then have "fmdom' t' = vs2"
          using assms(4) a(4) fmdom'_fmrestrict_set inf.order_iff
          by metis
        then have "fmlookup s' x \<noteq> None" "fmlookup t' x = None"
          using i b domIff fmdom'_alt_def fmdom.rep_eq
          by metis+
        then have "s' \<noteq> t'"
          by blast
      }
      then show ?thesis
        using 1 neq_funs_neq_images
        by blast
    next
      case ii
      {
        fix s' t'
        assume "s' \<in> fmrestrict_set vs1 ` ss" "t' \<in> fmrestrict_set vs2 ` ss"
        then obtain s t where c:
          "s \<in> ss" "s' = fmrestrict_set vs1 s" "t \<in> ss" "t' = fmrestrict_set vs2 t"
          by blast
        then have "fmdom' s = vs"
          using assms(2)
          by (simp add: stateSpace_def)
        then have d: "fmdom' s' = vs1"
          using assms(3) c(2) fmdom'_fmrestrict_set inf.order_iff
          by metis
        then have  "fmdom' t = vs"
          using assms(2) c(3)
          by (simp add: stateSpace_def)
        then have "fmdom' t' = vs2"
          using assms(4) c(4) fmdom'_fmrestrict_set inf.order_iff
          by metis
        then have "fmlookup s' x = None" "fmlookup t' x \<noteq> None"
          using ii d domIff fmdom'_alt_def fmdom.rep_eq
          by metis+
        then have "s' \<noteq> t'"
          by blast
      }
      then show ?thesis
        using 1 neq_funs_neq_images
        by blast
    qed
  }
  then show ?thesis
    unfolding ss_proj_def
    by blast
qed

lemma subset_dom_stateSpace_ss_proj:
  fixes vs1 vs2
  assumes "(vs1 \<subseteq> vs2)" "(stateSpace ss vs2)"
  shows "(stateSpace (ss_proj ss vs1) vs1)"
  using assms
  by (metis inf.absorb_iff2 invariantStateSpace_thm_5)

lemma card_proj_leq:
  assumes "finite PROB"
  shows "card (prob_proj PROB vs) \<le> card PROB"
  unfolding prob_proj_def
  using assms card_image_le
  by blast

end