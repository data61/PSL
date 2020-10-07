theory TopologicalProps
  imports Main FactoredSystem ActionSeqProcess SetUtils
begin 


section "Topological Properties"
subsection "Basic Definitions and Properties"

definition PLS_charles where
  "PLS_charles s as PROB \<equiv> {length as' | as'. 
    (as' \<in> valid_plans PROB) \<and> (exec_plan s as' = exec_plan s as)}"


definition MPLS_charles where
  "MPLS_charles PROB \<equiv> {Inf (PLS_charles (fst p) (snd p) PROB) | p. 
    ((fst p) \<in> valid_states PROB) 
    \<and> ((snd p) \<in> valid_plans PROB)
  }"


\<comment> \<open>NOTE name shortened to 'problem\_plan\_bound\_charles'.\<close>
definition problem_plan_bound_charles where
  "problem_plan_bound_charles PROB \<equiv> Sup (MPLS_charles PROB)"


\<comment> \<open>NOTE name shortened to 'PLS\_state'.\<close>  
definition PLS_state_1 where
  "PLS_state_1 s as \<equiv> length ` {as'. (exec_plan s as' = exec_plan s as)}"


\<comment> \<open>NOTE name shortened to 'MPLS\_stage\_1'.\<close>
definition MPLS_stage_1 where
  "MPLS_stage_1 PROB \<equiv> 
    (\<lambda> (s, as). Inf (PLS_state_1 s as)) 
    ` {(s, as). (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)}
  "


\<comment> \<open>NOTE name shortened to 'problem\_plan\_bound\_stage\_1'.\<close>
definition problem_plan_bound_stage_1 where
  "problem_plan_bound_stage_1 PROB \<equiv> Sup (MPLS_stage_1 PROB)"
for PROB :: "'a problem"


\<comment> \<open>NOTE name shortened.\<close>
definition PLS where
  "PLS s as \<equiv> length ` {as'. (exec_plan s as' = exec_plan s as) \<and> (subseq as' as)}"


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>NOTE proof finite PLS for use in 'proof in\_MPLS\_leq\_2\_pow\_n\_i'\<close> 
lemma finite_PLS: "finite (PLS s as)"
proof -
  let ?S = "{as'. (exec_plan s as' = exec_plan s as) \<and> (subseq as' as)}"
  let ?S1 = "length ` {as'. (exec_plan s as' = exec_plan s as) }" 
  let ?S2 = "length ` {as'. (subseq as' as)}"
  let ?n = "length as + 1"
  have "finite ?S2"
    using bounded_nat_set_is_finite[where n = ?n and N = ?S2]
    by fastforce
  moreover have "length ` ?S \<subseteq> (?S1 \<inter> ?S2)"
    by blast
  ultimately have "finite (length ` ?S)"
    using infinite_super 
    by auto 
  then show ?thesis 
    unfolding PLS_def 
    by blast
qed


\<comment> \<open>NOTE name shortened.\<close>
definition MPLS where
  "MPLS PROB \<equiv>
    (\<lambda> (s, as). Inf (PLS s as)) 
    ` {(s, as). (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)}
  "


\<comment> \<open>NOTE name shortened.\<close>
definition problem_plan_bound where
  "problem_plan_bound PROB \<equiv> Sup (MPLS PROB)"


lemma expanded_problem_plan_bound_thm_1: 
  fixes PROB
  shows " 
    (problem_plan_bound PROB) = Sup (
      (\<lambda>(s,as). Inf (PLS s as)) `
      {(s, as). (s \<in> (valid_states PROB)) \<and> (as \<in> valid_plans PROB)}
    )  
  "
  unfolding problem_plan_bound_def MPLS_def 
  by blast

lemma expanded_problem_plan_bound_thm: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set"
  shows "
    problem_plan_bound PROB = Sup ({Inf (PLS s as) | s as. 
      (s \<in> valid_states PROB) 
      \<and> (as \<in> valid_plans PROB)
    })
  "
proof -
  {
    have "(
        {Inf (PLS s as) | s as. (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)}
      ) = ((\<lambda>(s, as). Inf (PLS s as)) ` {(s, as).
        (s \<in> valid_states PROB) 
        \<and> (as \<in> valid_plans PROB)
      })
    "
      by fast
    also have "\<dots> = 
      (\<lambda>(s, as). Inf (PLS s as)) ` 
      ({s. fmdom' s = prob_dom PROB} \<times> {as. set as \<subseteq> PROB})
    "
      unfolding valid_states_def valid_plans_def
      by simp
    finally have "
      Sup ({Inf (PLS s as) | s as. (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)})
      = Sup (
        (\<lambda>(s, as). Inf (PLS s as)) ` 
        ({s. fmdom' s = prob_dom PROB} \<times> {as. set as \<subseteq> PROB})
      )
    "
      by argo
  }
  moreover have "
    problem_plan_bound PROB 
    = 
      Sup ((\<lambda>(s, as). Inf (PLS s as)) ` 
      ({s. fmdom' s = prob_dom PROB} \<times> {as. set as \<subseteq> PROB}))
    " 
    unfolding problem_plan_bound_def MPLS_def valid_states_def valid_plans_def
    by fastforce
  ultimately show "
    problem_plan_bound PROB 
    = Sup ({Inf (PLS s as) | s as. 
      (s \<in> valid_states PROB) 
      \<and> (as \<in> valid_plans PROB)
    })
  "
    by argo 
qed


subsection "Recurrence Diameter" 

text \<open> The recurrence diameter---defined as the longest simple path in the digraph modelling the
state space---provides a loose upper bound on the system diameter. [Abdulaziz et al., Definition 9, 
p.15] \<close>

\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE 'fun' because of multiple defining equations, pattern matches.\<close>
fun valid_path where
  "valid_path Pi [] = True"
| "valid_path Pi [s] = (s \<in> valid_states Pi)"
| "valid_path Pi (s1 # s2 # rest) = (
  (s1 \<in> valid_states Pi) 
  \<and> (\<exists>a. (a \<in> Pi) \<and> (exec_plan s1 [a] = s2))
  \<and> (valid_path Pi (s2 # rest))
)"


lemma valid_path_ITP2015: "
  (valid_path Pi [] \<longleftrightarrow> True)
  \<and> (valid_path Pi [s] \<longleftrightarrow> (s \<in> valid_states Pi))
  \<and> (valid_path Pi (s1 # s2 # rest) \<longleftrightarrow>
      (s1 \<in> valid_states Pi) 
      \<and> (\<exists>a. 
        (a \<in> Pi)
        \<and> (exec_plan s1 [a] = s2)
      ) 
      \<and> (valid_path Pi (s2 # rest))
  )
"
  using valid_states_def
  by simp


\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE second declaration skipped (declared twice in source).\<close>
definition RD where
  "RD Pi \<equiv> (Sup {length p - 1 | p. valid_path Pi p \<and> distinct p})"
for Pi :: "'a problem"


lemma in_PLS_leq_2_pow_n: 
  fixes PROB :: "'a problem" and s :: "'a state" and as
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" 
  shows "(\<exists>x. 
    (x \<in> PLS s as) 
    \<and> (x \<le> (2 ^ card (prob_dom PROB)) - 1)
  )"
proof -
  obtain as' where 1:
    "exec_plan s as = exec_plan s as'" "subseq as' as" "length as' \<le> 2 ^ card (prob_dom PROB) - 1" 
    using assms main_lemma 
    by blast
  let ?x="length as'"
  have "?x \<in> PLS s as" 
    unfolding PLS_def
    using 1
    by simp
  moreover have "?x \<le> 2 ^ card (prob_dom PROB) - 1"
    using 1(3)
    by blast
  ultimately show "(\<exists>x. 
    (x \<in> PLS s as) 
    \<and> (x \<le> (2 ^ card (prob_dom PROB)) - 1)
  )" 
    unfolding PLS_def
    by blast
qed


lemma in_MPLS_leq_2_pow_n: 
  fixes PROB :: "'a problem" and x
  assumes "finite PROB" "(x \<in> MPLS PROB)"
  shows "(x \<le> 2 ^ card (prob_dom PROB) - 1)" 
proof -
  let ?mpls = "MPLS PROB"
    \<comment> \<open>NOTE obtain p = (s, as) where 'x = Inf (PLS s as)' from premise.\<close>
  have "?mpls = 
    (\<lambda> (s, as). Inf (PLS s as)) ` 
    {(s, as).  (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)}
  "
    using MPLS_def 
    by blast
  then obtain s :: "('a, bool) fmap" and as :: "(('a, bool) fmap \<times> ('a, bool) fmap) list" 
    where obtain_s_as: "x \<in> 
      ((\<lambda> (s, as). Inf (PLS s as)) ` 
      {(s, as). (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB)})
    "
    using assms(2) 
    by blast
  then have 
    "x \<in> {Inf (PLS (fst p) (snd p)) | p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)}" 
    using assms(1) obtain_s_as 
    by auto
  then have 
    "\<exists> p. x = Inf (PLS (fst p) (snd p)) \<and> (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)" 
    by blast
  then obtain p :: "('a, bool) fmap \<times> (('a, bool) fmap \<times> ('a, bool) fmap) list" where obtain_p:
    "x = Inf (PLS (fst p) (snd p))" "(fst p \<in> valid_states PROB)" "(snd p \<in> valid_plans PROB)" 
    by blast 
  then have "fst p \<in> valid_states PROB" "snd p \<in> valid_plans PROB"
    using obtain_p 
    by blast+    
  then obtain x' :: nat where obtain_x':
    "x' \<in> PLS (fst p) (snd p) \<and> x' \<le> 2 ^ card (prob_dom PROB) - 1" 
    using assms(1) in_PLS_leq_2_pow_n[where s = "fst p" and as = "snd p"]
    by blast
  then have 1: "x' \<le> 2 ^ card (prob_dom PROB) - 1" "x' \<in> PLS (fst p) (snd p)" 
    "x = Inf (PLS (fst p) (snd p))" "finite (PLS (fst p) (snd p))"
    using obtain_x' obtain_p finite_PLS 
    by blast+
  moreover have "x \<le> x'" 
    using 1(2, 4) obtain_p(1) cInf_le_finite
    by blast
  ultimately show "(x \<le> 2 ^ card (prob_dom PROB) - 1)"
    by linarith
qed


lemma FINITE_MPLS: 
  assumes "finite (Pi :: 'a problem)"
  shows "finite (MPLS Pi)"
proof -
  have "\<forall>x \<in> MPLS Pi. x \<le> 2 ^ card (prob_dom Pi) - 1"
    using assms in_MPLS_leq_2_pow_n
    by blast
  then show "finite (MPLS Pi)" 
    using mems_le_finite[of "MPLS Pi" "2 ^ card (prob_dom Pi) - 1"]
    by blast
qed


\<comment> \<open>NOTE 'fun' because of multiple defining equations.\<close>
fun statelist' where
  "statelist' s [] = [s]"
| "statelist' s (a # as) = (s # statelist' (state_succ s a) as)"


lemma LENGTH_statelist': 
  fixes as s
  shows "length (statelist' s as) = (length as + 1)"
  by (induction as arbitrary: s) auto


lemma valid_path_statelist': 
  fixes as and s :: "('a, 'b) fmap"
  assumes "(as \<in> valid_plans Pi)" "(s \<in> valid_states Pi)"
  shows "(valid_path Pi (statelist' s as))"
  using assms 
proof (induction as arbitrary: s Pi)
  case cons: (Cons a as)
  then have 1: "a \<in> Pi" "as \<in> valid_plans Pi"
    using valid_plan_valid_head valid_plan_valid_tail 
    by metis+
  then show ?case     
  proof (cases as)
    case Nil
    {
      have "state_succ s a \<in> valid_states Pi"
        using 1 cons.prems(2) valid_action_valid_succ
        by blast
      then have "valid_path Pi [state_succ s a]"
        using 1 cons.prems(2) cons.IH
        by force
      moreover have "(\<exists>aa. aa \<in> Pi \<and> exec_plan s [aa] = state_succ s a)"
        using 1(1) 
        by fastforce
      ultimately have "valid_path Pi (statelist' s [a])" 
        using cons.prems(2)
        by simp
    }
    then show ?thesis 
      using Nil
      by blast
  next
    case (Cons b list)
    {
      have "s \<in> valid_states Pi" 
        using cons.prems(2)
        by simp
          \<comment> \<open>TODO this step is inefficient (~5s).\<close>
      then have 
        "valid_path Pi (state_succ s a # statelist' (state_succ (state_succ s a) b) list)"
        using 1 cons.IH cons.prems(2) Cons lemma_1_i
        by fastforce
      moreover have 
        "(\<exists>aa b. (aa, b) \<in> Pi \<and> state_succ s (aa, b) = state_succ s a)"
        using 1(1) surjective_pairing
        by metis
      ultimately have "valid_path Pi (statelist' s (a # b # list))" 
        using cons.prems(2)
        by auto
    }
    then show ?thesis 
      using Cons
      by blast
  qed
qed simp


\<comment> \<open>TODO explicit proof.\<close>
lemma statelist'_exec_plan: 
  fixes a s p
  assumes "(statelist' s as = p)"
  shows "(exec_plan s as = last p)"
  using assms 
  apply(induction as arbitrary: s p)
   apply(auto)
  apply(cases "as")
  by 
    (metis LENGTH_statelist' One_nat_def add_Suc_right list.size(3) nat.simps(3))
    (metis (no_types) LENGTH_statelist' One_nat_def add_Suc_right list.size(3) nat.simps(3))


lemma statelist'_EQ_NIL: "statelist' s as \<noteq> []"
  by (cases as) auto


\<comment> \<open>NOTE added lemma.\<close>
lemma statelist'_TAKE_i:
  assumes "Suc m \<le> length (a # as)"
  shows "m \<le> length as"
  using assms 
  by (induction as arbitrary: a m) auto

lemma statelist'_TAKE: 
  fixes as s p
  assumes "(statelist' s as = p)"
  shows "(\<forall>n. n \<le> length as \<longrightarrow> (exec_plan s (take n as)) = (p ! n))" 
  using assms
proof (induction as arbitrary: s p)
  case Nil
  {
    fix n
    assume P1: "n \<le> length []"
    then have "exec_plan s (take n []) = s" 
      by simp
    moreover have "p ! 0 = s" 
      using Nil.prems 
      by force
    ultimately have "exec_plan s (take n []) = p ! n" 
      using P1
      by simp
  }
  then show ?case by blast
next
  case (Cons a as)
  {
    fix n
    assume P2: "n \<le> length (a # as)"
    then have "exec_plan s (take n (a # as)) = p ! n" 
      using Cons.prems 
    proof (cases "n = 0")
      case False
      then obtain m where a: "n = Suc m"
        using not0_implies_Suc
        by presburger
      moreover have b: "statelist' s (a # as) ! n = statelist' (state_succ s a) as ! m"
        using a nth_Cons_Suc
        by simp
      moreover have c: "exec_plan s (take n (a # as)) = exec_plan (state_succ s a) (take m as)"
        using a
        by force
      moreover have "m \<le> length as" 
        using a P2 statelist'_TAKE_i
        by simp
      moreover have 
        "exec_plan (state_succ s a) (take m as) = statelist' (state_succ s a) as ! m"
        using calculation(2, 3, 4) Cons.IH
        by blast
      ultimately show ?thesis 
        using Cons.prems
        by argo
    qed fastforce
  }
  then show ?case by blast
qed


lemma MPLS_nempty: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set" 
  assumes "finite PROB"
  shows "MPLS PROB \<noteq> {}"
proof -
  let ?S="{(s, as). s \<in> valid_states PROB \<and> as \<in> valid_plans PROB}"
    \<comment> \<open>NOTE type of 's' had to be fixed for 'valid\_states\_nempty'.\<close>
  obtain s :: "('a, 'b) fmap"  where "s \<in> valid_states PROB"
    using assms valid_states_nempty
    by blast
  moreover have "[] \<in> valid_plans PROB"
    using empty_plan_is_valid
    by auto
  ultimately have "(s, []) \<in> ?S" 
    by blast
  then show ?thesis 
    unfolding MPLS_def
    by blast
qed


theorem bound_main_lemma: 
  fixes PROB :: "'a problem" 
  assumes "finite PROB"
  shows "(problem_plan_bound PROB \<le> (2 ^ (card (prob_dom PROB))) - 1)"
proof -
  have "MPLS PROB \<noteq> {}"
    using assms MPLS_nempty
    by auto
  moreover have "(\<forall>x. x \<in> MPLS PROB \<longrightarrow> x \<le> 2 ^ card (prob_dom PROB) - 1)"
    using assms in_MPLS_leq_2_pow_n
    by blast
  ultimately show ?thesis
    unfolding problem_plan_bound_def
    using cSup_least 
    by blast
qed


\<comment> \<open>NOTE types in premise had to be fixed to be able to match `valid\_as\_valid\_exec`.\<close>
lemma bound_child_parent_card_state_set_cons: 
  fixes P f
  assumes "(\<forall>(PROB :: 'a problem) as (s :: 'a state). 
    (P PROB) 
    \<and> (as \<in> valid_plans PROB) 
    \<and> (s \<in> valid_states PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as) 
      \<and> (length as' < f PROB)
    )
  )"
  shows "(\<forall>PROB s as. 
    (P PROB)
    \<and> (as \<in> valid_plans PROB)
    \<and> (s \<in> (valid_states PROB))
    \<longrightarrow> (\<exists>x. 
      (x \<in> PLS s as) 
      \<and> (x < f PROB)
    )
  )"
proof -
  {
    fix PROB :: "'a problem" and as and s :: "'a state"
    assume P1: "(P PROB)" 
      "(as \<in> valid_plans PROB)"
      "(s \<in> valid_states PROB)" 
      "(\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> (subseq as' as) 
        \<and> (length as' < f PROB)
      )"
    have "(exec_plan s as \<in> valid_states PROB)"
      using assms P1 valid_as_valid_exec
      by blast
    then have "(P PROB)
      \<and> (as \<in> valid_plans PROB)
      \<and> (s \<in> (valid_states PROB))
      \<longrightarrow> (\<exists>x. 
        (x \<in> PLS s as) 
        \<and> (x < f PROB)
      )
    "
      unfolding PLS_def 
      using P1 
      by force
  }
  then show "(\<forall>PROB s as. 
    (P PROB)
    \<and> (as \<in> valid_plans PROB)
    \<and> (s \<in> (valid_states PROB))
    \<longrightarrow> (\<exists>x. 
      (x \<in> PLS s as) 
      \<and> (x < f PROB)
    )
  )"
    using assms
    by simp
qed


\<comment> \<open>NOTE types of premise had to be fixed to be able to use lemma `bound\_child\_parent\_card\_state\_set\_cons`.\<close>
lemma bound_on_all_plans_bounds_MPLS: 
  fixes P f
  assumes "(\<forall>(PROB :: 'a problem) as (s :: 'a state).
    (P PROB) 
    \<and> (s \<in> valid_states PROB) 
    \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as) 
      \<and> (length as' < f PROB)
    )
  )"
  shows "(\<forall>PROB x. P PROB
    \<longrightarrow> (x \<in> MPLS(PROB)) 
    \<longrightarrow> (x < f PROB)
  )"
proof -
  {
    fix PROB :: "'a problem" and as and s :: "'a state"
    assume "(P PROB)"
      "(s \<in> valid_states PROB)"
      "(as \<in> valid_plans PROB)"
      "(\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> (subseq as' as) 
        \<and> (length as' < f PROB)
      )"
    then have "(\<exists>x. x \<in> PLS s as \<and> x < f PROB)"
      using assms(1) bound_child_parent_card_state_set_cons[where P = P and f = f]
      by presburger
  }
  note 1 = this
  {
    fix PROB x
    assume P1: "P PROB" "x \<in> MPLS PROB"
      \<comment> \<open>TODO refactor 'x\_in\_MPLS\_if' and use here.\<close>
    then obtain s as where a:
      "x = Inf (PLS s as)" "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
      unfolding MPLS_def
      by auto
    moreover have "(\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as) 
      \<and> (length as' < f PROB)
    )"
      using P1(1) assms calculation(2, 3) 
      by blast
    ultimately obtain x' where "x' \<in> PLS s as" "x' < f PROB"
      using P1 1
      by blast
    then have "x < f PROB"
      using a(1) mem_lt_imp_MIN_lt
      by fastforce
  }
  then show ?thesis
    by blast
qed


lemma bound_child_parent_card_state_set_cons_finite: 
  fixes P f
  assumes "(\<forall>PROB as s.
    P PROB \<and> finite PROB \<and> as \<in> (valid_plans PROB) \<and> s \<in> (valid_states PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> subseq as' as 
      \<and> length as' < f(PROB)
    )
  )"
  shows "(\<forall>PROB s as. 
    P PROB \<and> finite PROB \<and> as \<in> (valid_plans PROB) \<and> (s \<in> (valid_states PROB))
    \<longrightarrow> (\<exists>x. (x \<in> PLS s as) \<and> x < f PROB)
  )"
proof -
  {
    fix PROB s as
    assume "P PROB" "finite PROB" "as \<in> (valid_plans PROB)" "s \<in> (valid_states PROB)"
      " (\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> subseq as' as 
        \<and> length as' < f PROB
      )"
      (* NOTE[1]
        moreover have "exec_plan s as \<in> valid_states PROB" 
          using calculation valid_as_valid_exec by blast
    *)
    then obtain as' where 
      "(exec_plan s as = exec_plan s as')" "subseq as' as" "length as' < f PROB"
      by blast
    moreover have "length as' \<in> PLS s as" 
      unfolding PLS_def
      using calculation
      by fastforce
    ultimately have "(\<exists>x. (x \<in> PLS s as) \<and> x < f PROB)"
      by blast
  }
  then show "(\<forall>PROB s as. 
    P PROB  
    \<and> finite PROB
    \<and> as \<in> (valid_plans PROB)
    \<and> (s \<in> (valid_states PROB))
    \<longrightarrow> (\<exists>x. (x \<in> PLS s as) \<and> x < f PROB)
  )" 
    using assms
    by auto
qed


lemma bound_on_all_plans_bounds_MPLS_finite: 
  fixes P f
  assumes "(\<forall>PROB as s. 
    P PROB \<and> finite PROB \<and> s \<in> (valid_states PROB) \<and> as \<in> (valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> subseq as' as 
      \<and> length as' < f(PROB)
    )
  )"
  shows "(\<forall>PROB x. 
    P PROB \<and> finite PROB 
    \<longrightarrow> (x \<in> MPLS PROB)
    \<longrightarrow> x < f PROB
  )"
proof -
  {
    fix PROB x
    assume P1: "P PROB" "finite PROB" "x \<in> MPLS PROB"
      \<comment> \<open>TODO refactor 'x\_in\_MPLS\_if' and use here.\<close>
    then obtain s as where a:
      "x = Inf (PLS s as)" "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
      unfolding MPLS_def
      by auto
    moreover have "(\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as) 
      \<and> (length as' < f PROB)
    )"
      using P1(1, 2) assms calculation(2, 3)
      by blast
    moreover obtain x' where "x' \<in> PLS s as" "x' < f PROB"
      using PLS_def calculation(4)
      by fastforce 
    then have "x < f PROB" 
      using a(1) mem_lt_imp_MIN_lt 
      by fastforce
  }
  then show ?thesis
    using assms
    by blast
qed


lemma bound_on_all_plans_bounds_problem_plan_bound: 
  fixes P f
  assumes "(\<forall>PROB as s. 
    (P PROB) 
    \<and> finite PROB
    \<and> (s \<in> valid_states PROB) 
    \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as')
      \<and> (subseq as' as)
      \<and> (length as' < f PROB)
    )
  )"
  shows "(\<forall>PROB. 
    (P PROB) 
    \<and> finite PROB
    \<longrightarrow> (problem_plan_bound PROB < f PROB)
  )"
proof -
  have 1: "\<forall>PROB x. 
    P PROB 
    \<and> finite PROB 
    \<longrightarrow> x \<in> MPLS PROB   
    \<longrightarrow> x < f PROB
  "
    using assms bound_on_all_plans_bounds_MPLS_finite
    by blast
  {
    fix PROB x
    assume "P PROB \<and> finite PROB 
      \<longrightarrow> x \<in> MPLS PROB   
      \<longrightarrow> x < f PROB
    "
    then have "\<forall>PROB.
      P PROB \<and> finite PROB 
      \<longrightarrow> problem_plan_bound PROB < f PROB
    " 
      unfolding problem_plan_bound_def
      using 1 bound_child_parent_not_eq_last_diff_paths 1 MPLS_nempty
      by metis
    then have "\<forall>PROB.
      P PROB \<and> finite PROB 
      \<longrightarrow> problem_plan_bound PROB < f PROB
    " 
      using MPLS_nempty
      by blast 

  }
  then show "(\<forall>PROB. 
    (P PROB) 
    \<and> finite PROB
    \<longrightarrow> (problem_plan_bound PROB < f PROB)
  )"
    using 1
    by blast
qed


lemma bound_child_parent_card_state_set_cons_thesis: 
  assumes "finite PROB" "(\<forall>as s. 
    as \<in> (valid_plans PROB) 
    \<and> s \<in> (valid_states PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as')
      \<and> subseq as' as 
      \<and> length as' < k
    ) 
  )" "as \<in> (valid_plans PROB)" "(s \<in> (valid_states PROB))" 
  shows "(\<exists>x. (x \<in> PLS s as) \<and> x < k)"
  unfolding PLS_def 
  using assms
  by fastforce


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor/move up.\<close>
lemma x_in_MPLS_if: 
  fixes x PROB 
  assumes "x \<in> MPLS PROB"  
  shows "\<exists>s as. s \<in> valid_states PROB \<and> as \<in> valid_plans PROB \<and> x = Inf (PLS s as)" 
  using assms
  unfolding MPLS_def
  by fast

lemma bound_on_all_plans_bounds_MPLS_thesis: 
  assumes "finite PROB" "(\<forall>as s. 
    (s \<in> valid_states PROB) 
    \<and> (as \<in> valid_plans PROB)
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' < k)
    )
  )" "(x \<in> MPLS PROB)" 
  shows "(x < k)" 
proof -
  obtain s as where 1: "s \<in> valid_states PROB" "as \<in> valid_plans PROB" "x = Inf (PLS s as)"
    using assms(3) x_in_MPLS_if 
    by blast
  then obtain x' :: nat where "x' \<in> PLS s as" "x' < k" 
    using assms(1, 2) bound_child_parent_card_state_set_cons_thesis 
    by blast
  then have "Inf (PLS s as) < k"
    using mem_lt_imp_MIN_lt 
    by blast
  then show "x < k" 
    using 1
    by simp
qed


\<comment> \<open>NOTE added lemma.\<close>
lemma bounded_MPLS_contains_supremum: 
  fixes PROB
  assumes "finite PROB" "(\<exists>k. \<forall>x \<in> MPLS PROB. x < k)" 
  shows "Sup (MPLS PROB) \<in> MPLS PROB" 
proof -
  obtain k where "\<forall>x \<in> MPLS PROB. x < k" 
    using assms(2)
    by blast
  moreover have "finite (MPLS PROB)"
    using assms(2) finite_nat_set_iff_bounded
    by presburger
  moreover have "MPLS PROB \<noteq> {}" 
    using assms(1) MPLS_nempty
    by auto
  ultimately show "Sup (MPLS PROB) \<in> MPLS PROB"
    unfolding Sup_nat_def
    by simp
qed

lemma bound_on_all_plans_bounds_problem_plan_bound_thesis': 
  assumes "finite PROB" "(\<forall>as s. 
      s \<in> (valid_states PROB) 
      \<and> as \<in> (valid_plans PROB)
      \<longrightarrow> (\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> subseq as' as 
        \<and> length as' < k
      )
    )"
  shows "problem_plan_bound PROB < k" 
proof -
  have 1: "\<forall>x \<in> MPLS PROB. x < k" 
    using assms(1, 2) bound_on_all_plans_bounds_MPLS_thesis 
    by blast
  then have "Sup (MPLS PROB) \<in> MPLS PROB" 
    using assms(1) bounded_MPLS_contains_supremum 
    by auto
  then have "Sup (MPLS PROB) < k" 
    using 1
    by blast
  then show ?thesis 
    unfolding problem_plan_bound_def
    by simp
qed


lemma bound_on_all_plans_bounds_problem_plan_bound_thesis: 
  assumes "finite PROB" "(\<forall>as s. 
      (s \<in> valid_states PROB) 
      \<and> (as \<in> valid_plans PROB) 
      \<longrightarrow> (\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> (subseq as' as)
        \<and> (length as' \<le> k)
      )
    )"
  shows "(problem_plan_bound PROB \<le> k)" 
proof -
  have 1: "\<forall>x\<in>MPLS PROB. x < k + 1" 
    using assms(1, 2) bound_on_all_plans_bounds_MPLS_thesis[where k = "k + 1"] Suc_eq_plus1 
      less_Suc_eq_le
    by metis
  then have "Sup (MPLS PROB) \<in> MPLS PROB" 
    using assms(1) bounded_MPLS_contains_supremum 
    by fast
  then show "(problem_plan_bound PROB \<le> k)"
    unfolding problem_plan_bound_def 
    using 1
    by fastforce
qed


lemma  bound_on_all_plans_bounds_problem_plan_bound_: 
  fixes P f PROB
  assumes "(\<forall>PROB' as s. 
      finite PROB \<and> (P PROB') \<and> (s \<in> valid_states PROB') \<and> (as \<in> valid_plans PROB') 
      \<longrightarrow> (\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> (subseq as' as)
        \<and> (length as' < f PROB')
      )
    )" "(P PROB)" "finite PROB" 
  shows "(problem_plan_bound PROB < f PROB)"
  unfolding problem_plan_bound_def MPLS_def
  using assms bound_on_all_plans_bounds_problem_plan_bound_thesis' expanded_problem_plan_bound_thm_1
  by metis


lemma S_VALID_AS_VALID_IMP_MIN_IN_PLS: 
  fixes PROB s as
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" 
  shows "(Inf (PLS s as) \<in> (MPLS PROB))" 
  unfolding MPLS_def
  using assms
  by fast


\<comment> \<open>NOTE type of `s` had to be fixed (type mismatch in goal).\<close>
\<comment> \<open>NOTE premises rewritten to implications for proof set up.\<close>
lemma problem_plan_bound_ge_min_pls: 
  fixes PROB :: "'a problem" and s :: "'a state" and as k
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" 
    "(problem_plan_bound PROB \<le> k)"
  shows "(Inf (PLS s as) \<le> problem_plan_bound PROB)"
proof -
  have "Inf (PLS s as) \<in> MPLS PROB" 
    using assms(2, 3) S_VALID_AS_VALID_IMP_MIN_IN_PLS 
    by blast
  moreover have "finite (MPLS PROB)" 
    using assms(1) FINITE_MPLS 
    by blast
  ultimately have "Inf (PLS s as) \<le> Sup (MPLS PROB)"
    using le_cSup_finite
    by blast 
  then show ?thesis 
    unfolding problem_plan_bound_def
    by simp
qed


lemma  PLS_NEMPTY: 
  fixes s as 
  shows "PLS s as \<noteq> {}"
  unfolding PLS_def
  by blast


lemma  PLS_nempty_and_has_min: 
  fixes s as 
  shows "(\<exists>x. (x \<in> PLS s as) \<and> (x = Inf (PLS s as)))"
proof -
  have "PLS s as \<noteq> {}" 
    using PLS_NEMPTY 
    by blast
  then have "Inf (PLS s as) \<in> PLS s as"
    unfolding Inf_nat_def
    using LeastI_ex Max_in finite_PLS
    by metis 
  then show ?thesis 
    by blast
qed


lemma  PLS_works: 
  fixes x s as
  assumes "(x \<in> PLS s as)" 
  shows"(\<exists>as'. 
      (exec_plan s as = exec_plan s as')
      \<and> (length as' = x) 
      \<and> (subseq as' as)
    )"
  using assms
  unfolding PLS_def
  by (smt imageE mem_Collect_eq)


\<comment> \<open>NOTE type of `s` had to be fixed (type mismatch in goal).\<close>
lemma problem_plan_bound_works: 
  fixes PROB :: "'a problem" and as and s :: "'a state"
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" 
  shows "(\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' \<le> problem_plan_bound PROB)
    )"
proof -
  have "problem_plan_bound PROB \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms(1) bound_main_lemma 
    by blast
  then have 1: "Inf (PLS s as) \<le> problem_plan_bound PROB"
    using 
      assms(1, 2, 3)
      problem_plan_bound_ge_min_pls
    by blast
  then have "\<exists>x. x \<in> PLS s as \<and> x = Inf (PLS s as)" 
    using PLS_nempty_and_has_min
    by blast 
  then have "Inf (PLS s as) \<in> (PLS s as)"
    by blast 
  then obtain as' where 2:
    "exec_plan s as = exec_plan s as'" "length as' = Inf (PLS s as)" "subseq as' as"
    using PLS_works
    by blast
  then have "length as' \<le> problem_plan_bound PROB" 
    using 1
    by argo
  then show "(\<exists>as'. 
    (exec_plan s as = exec_plan s as') 
    \<and> (subseq as' as)
    \<and> (length as' \<le> problem_plan_bound PROB)
  )"  
    using 2(1) 2(3)
    by blast
qed


\<comment> \<open>NOTE name shortened.\<close>
definition MPLS_s where
  "MPLS_s PROB s \<equiv> (\<lambda> (s, as). Inf (PLS s as)) ` {(s, as) | as. as \<in> valid_plans PROB}"


\<comment> \<open>NOTE type of `PROB` had to be fixed (type mismatch in goal).\<close>
lemma bound_main_lemma_s_3: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set" and s
  shows "MPLS_s PROB s \<noteq> {}"
proof -
  \<comment> \<open>TODO @{term "(s, []) \<in> {}"} could be refactored (this is used in 'MPLS\_nempty' too).\<close>
  have "[] \<in> valid_plans PROB" 
    using empty_plan_is_valid 
    by blast
  then have "(s, []) \<in> {(s, as). as \<in> valid_plans PROB}" 
    by simp
  then show "MPLS_s PROB s \<noteq> {}"
    unfolding MPLS_s_def
    by blast
qed


\<comment> \<open>NOTE name shortened.\<close>
definition problem_plan_bound_s where
  "problem_plan_bound_s PROB s = Sup (MPLS_s PROB s)"


\<comment> \<open>NOTE removed typing from assumption due to matching problems in later proofs.\<close>
lemma  bound_on_all_plans_bounds_PLS_s: 
  fixes P f 
  assumes "(\<forall>PROB as s.  
    finite PROB \<and> (P PROB) \<and> (as \<in> valid_plans PROB) \<and> (s \<in> valid_states PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as')
      \<and> (subseq as' as)
      \<and> (length as' < f PROB s)
    )
  )"
  shows "(\<forall>PROB s as. 
    finite PROB \<and> (P PROB) \<and> (as \<in> valid_plans PROB) \<and> (s \<in> valid_states PROB)
    \<longrightarrow> (\<exists>x. 
      (x \<in> PLS s as) 
      \<and> (x < f PROB s)
    )
  )"

  using assms 
  unfolding PLS_def
  by fastforce


\<comment> \<open>NOTE added lemma.\<close>
lemma bound_on_all_plans_bounds_MPLS_s_i:
  fixes PROB s x
  assumes "s \<in> valid_states PROB" "x \<in> MPLS_s PROB s" 
  shows "\<exists>as. x = Inf (PLS s as) \<and> as \<in> valid_plans PROB" 
proof -
  let ?S="{(s, as) | as. as \<in> valid_plans PROB}"
  obtain x' where 1: 
    "x' \<in> ?S"
    "x = (\<lambda> (s, as). Inf (PLS s as)) x'"
    using assms 
    unfolding MPLS_s_def
    by blast
  let ?as="snd x'"
  let ?s="fst x'"
  have "?as \<in> valid_plans PROB"
    using 1(1) 
    by auto
  moreover have "?s = s"
    using 1(1)
    by fastforce
  moreover have "x = Inf (PLS ?s ?as)"
    using 1(2)
    by (simp add: case_prod_unfold)
  ultimately show ?thesis 
    by blast
qed

lemma bound_on_all_plans_bounds_MPLS_s: 
  fixes P f
  assumes "(\<forall>PROB as s.
    finite PROB \<and> (P PROB) \<and> (as \<in> valid_plans PROB)  \<and> (s \<in> valid_states PROB)
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' < f PROB s)
    )
  )"
  shows "(\<forall>PROB x s. 
    finite PROB \<and> (P PROB) \<and> (s \<in> valid_states PROB) \<longrightarrow> (x \<in> MPLS_s PROB s) 
     \<longrightarrow> (x < f PROB s)
  )"
  using assms
  unfolding MPLS_def

proof -
  have 1: "\<forall>PROB s as.
     finite PROB \<and> P PROB \<and> as \<in> valid_plans PROB \<and> s \<in> valid_states PROB \<longrightarrow>
     (\<exists>x. x \<in> PLS s as \<and> x < f PROB s)"
    using bound_on_all_plans_bounds_PLS_s[OF assms] .
  {
    fix PROB x and s :: "('a, 'b) fmap"
    assume P1: "finite PROB" "(P PROB)" "(s \<in> valid_states PROB)" 
    {
      assume "(x \<in> MPLS_s PROB s)"
      then obtain as where i: "x = Inf (PLS s as)" "as \<in> valid_plans PROB"
        using P1 bound_on_all_plans_bounds_MPLS_s_i
        by blast
      then obtain x' where "x' \<in> PLS s as" "x' < f PROB s"
        using P1 i 1
        by blast
      then have "x < f PROB s"
        using mem_lt_imp_MIN_lt i(1) 
        by blast 
    }
    then have "(x \<in> MPLS_s PROB s) \<longrightarrow> (x < f PROB s)" 
      by blast
  }
  then show ?thesis
    by blast
qed


\<comment> \<open>NOTE added lemma.\<close>
lemma Sup_MPLS_s_lt_if: 
  fixes PROB s k
  assumes "(\<forall>x\<in>MPLS_s PROB s. x < k)"
  shows "Sup (MPLS_s PROB s) < k"
proof -
  have "MPLS_s PROB s \<noteq> {}" 
    using bound_main_lemma_s_3
    by fast
  then have "Sup (MPLS_s PROB s) \<in> MPLS_s PROB s"
    using assms Sup_nat_def bounded_nat_set_is_finite
    by force
  then show "Sup (MPLS_s PROB s) < k"
    using assms
    by blast
qed

\<comment> \<open>NOTE type of `P` had to be fixed (type mismatch in goal).\<close>
lemma bound_child_parent_lemma_s_2: 
  fixes PROB :: "'a problem" and P :: "'a problem \<Rightarrow> bool" and s f
  assumes "(\<forall>(PROB :: 'a problem) as s. 
    finite PROB \<and> (P PROB) \<and> (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' < f PROB s)
    )
  )"
  shows "(
    finite PROB \<and> (P PROB) \<and> (s \<in> valid_states PROB)
    \<longrightarrow> problem_plan_bound_s PROB s < f PROB s
  )"
proof -
  \<comment> \<open>NOTE manual instantiation is required (automation fails otherwise).\<close>
  have "\<forall>(PROB :: 'a problem) x s. 
    finite PROB \<and> P PROB \<and> s \<in> valid_states PROB 
    \<longrightarrow> x \<in> MPLS_s PROB s 
    \<longrightarrow> x < f PROB s
  "
    using assms bound_on_all_plans_bounds_MPLS_s[of P f]
    by simp
  then show
    "finite PROB \<and> (P PROB) \<and> (s \<in> valid_states PROB) \<longrightarrow> (problem_plan_bound_s PROB s < f PROB s)"
    unfolding problem_plan_bound_s_def 
    using Sup_MPLS_s_lt_if problem_plan_bound_s_def
    by metis
qed


theorem bound_main_lemma_reachability_s: 
  fixes PROB :: "'a problem" and s
  assumes "finite PROB" "s \<in> valid_states PROB" 
  shows "(problem_plan_bound_s PROB s < card (reachable_s PROB s))"
proof -
  \<comment> \<open>NOTE derive premise for MP of 'bound\_child\_parent\_lemma\_s\_2'.\<close>
  \<comment> \<open>NOTE type of `s` had to be fixed (warning in assumption declaration).\<close>
  {
    fix PROB :: "'a problem" and s :: "'a state" and as
    assume P1: "finite PROB" "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
    then obtain as' where a: "exec_plan s as = exec_plan s as'" "subseq as' as" 
      "length as' \<le> card (reachable_s PROB s) - 1"
      using P1 main_lemma_reachability_s
      by blast
    then have "length as' < card (reachable_s PROB s)"
      using P1(1, 2) card_reachable_s_non_zero
      by fastforce
    then have "(\<exists>as'. 
      exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' < card (reachable_s PROB s))
    "
      using a 
      by blast
  }
  then have "
    finite PROB \<and> True \<and> s \<in> valid_states PROB 
    \<longrightarrow> problem_plan_bound_s PROB s < card (reachable_s PROB s)
  "
    using bound_child_parent_lemma_s_2[where PROB = PROB and P = "\<lambda>_. True" and s = s
        and f = "\<lambda>PROB s. card (reachable_s PROB s)"]
    by blast
  then show ?thesis 
    using assms(1, 2)
    by blast
qed


lemma  problem_plan_bound_s_LESS_EQ_problem_plan_bound_thm: 
  fixes PROB :: "'a problem" and s :: "'a state"
  assumes "finite PROB" "(s \<in> valid_states PROB)"
  shows "(problem_plan_bound_s PROB s < problem_plan_bound PROB + 1)"
proof - 
  {
    fix PROB :: "'a problem" and s :: "'a state" and as
    assume "finite PROB" "s \<in> valid_states PROB" "as \<in> valid_plans PROB" 
    then obtain as' where a: "exec_plan s as = exec_plan s as'" "subseq as' as" 
      "length as' \<le> problem_plan_bound PROB"
      using problem_plan_bound_works
      by blast
    then have "length as' < problem_plan_bound PROB + 1"
      by linarith
    then have "\<exists>as'. 
      exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' \<le> problem_plan_bound PROB + 1
    "
      using a 
      by fastforce
  }
    \<comment> \<open>TODO unsure why a proof is needed at all here.\<close>
  then have "\<forall>(PROB :: 'a problem) as s.
   finite PROB \<and> True \<and> s \<in> valid_states PROB \<and> as \<in> valid_plans PROB 
   \<longrightarrow> (\<exists>as'. 
    exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' < problem_plan_bound PROB + 1)
  "
    by (metis Suc_eq_plus1 problem_plan_bound_works le_imp_less_Suc)
  then show "(problem_plan_bound_s PROB s < problem_plan_bound PROB + 1)" 
    using assms bound_child_parent_lemma_s_2[where PROB = PROB and s = s and P = "\<lambda>_. True" 
        and f = "\<lambda>PROB s. problem_plan_bound PROB + 1"]
    by fast
qed


\<comment> \<open>NOTE lemma `bound\_main\_lemma\_s\_1` skipped (this is being equivalently redeclared later).\<close>


lemma AS_VALID_MPLS_VALID: 
  fixes PROB as 
  assumes "(as \<in> valid_plans PROB)" 
  shows "(Inf (PLS s as) \<in> MPLS_s PROB s)"
  using assms
  unfolding MPLS_s_def
  by fast


\<comment> \<open>NOTE moved up because it's used in the following lemma.\<close>
\<comment> \<open>NOTE type of `s` had to be fixed for 'in\_PLS\_leq\_2\_pow\_n'.\<close>
lemma bound_main_lemma_s_1: 
  fixes PROB :: "'a problem" and s :: "'a state" and x
  assumes "finite PROB" "s \<in> (valid_states PROB)" "x \<in> MPLS_s PROB s"
  shows "(x \<le> (2 ^ card (prob_dom PROB)) - 1)"
proof -
  obtain as :: "(('a, bool) fmap \<times> ('a, bool) fmap) list" where "as \<in> valid_plans PROB"
    using empty_plan_is_valid 
    by blast
  then obtain x where 1: "x \<in> PLS s as" "x \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms in_PLS_leq_2_pow_n
    by blast
  then have "Inf (PLS s as) \<le> 2 ^ card (prob_dom PROB) - 1" 
    using mem_le_imp_MIN_le[where s = "PLS s as" and k = "2 ^ card (prob_dom PROB) - 1"]
    by blast
  then have "x \<le> 2 ^ card (prob_dom PROB) - 1" 
    using assms(3) 1
    by blast
      \<comment> \<open>TODO unsure why a proof is needed here (typing problem?).\<close>
  then show ?thesis
    using assms(1, 2, 3) S_VALID_AS_VALID_IMP_MIN_IN_PLS bound_on_all_plans_bounds_MPLS_s_i 
      in_MPLS_leq_2_pow_n
    by metis
qed


lemma problem_plan_bound_s_ge_min_pls: 
  fixes PROB :: "'a problem" and as k s
  assumes "finite PROB" "s \<in> (valid_states PROB)" "as \<in> (valid_plans PROB)" 
    "problem_plan_bound_s PROB s \<le> k"
  shows "(Inf (PLS s as) \<le> problem_plan_bound_s PROB s)"
proof -
  have "\<forall>x\<in>MPLS_s PROB s. x \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms(1, 2) bound_main_lemma_s_1 by blast
  then have 1: "finite (MPLS_s PROB s)"
    using mems_le_finite[where s = "MPLS_s PROB s" and k = "2 ^ card (prob_dom PROB) - 1"]
    by blast
  then have "MPLS_s PROB s \<noteq> {}" 
    using bound_main_lemma_s_3 
    by fast
  then have "Inf (PLS s as) \<in> MPLS_s PROB s" 
    using assms AS_VALID_MPLS_VALID 
    by blast 
  then show "(Inf (PLS s as) \<le> problem_plan_bound_s PROB s)"
    unfolding problem_plan_bound_s_def 
    using 1 le_cSup_finite 
    by blast
qed


theorem bound_main_lemma_s:
  fixes PROB :: "'a problem" and s
  assumes "finite PROB" "(s \<in> valid_states PROB)"
  shows "(problem_plan_bound_s PROB s \<le> 2 ^ (card (prob_dom PROB)) - 1)"
proof -
  have 1: "\<forall>x\<in>MPLS_s PROB s. x \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms bound_main_lemma_s_1
    by metis 
  then have "MPLS_s PROB s \<noteq> {}" 
    using bound_main_lemma_s_3 
    by fast
  then have "Sup (MPLS_s PROB s) \<le> 2 ^ card (prob_dom PROB) - 1"
    using 1 bound_main_lemma_2[where s = "MPLS_s PROB s" and k = "2 ^ card (prob_dom PROB) - 1"]
    by blast
  then show "problem_plan_bound_s PROB s \<le> 2 ^ card (prob_dom PROB) - 1"
    unfolding problem_plan_bound_s_def
    by blast
qed


lemma problem_plan_bound_s_works:
  fixes PROB :: "'a problem" and as s
  assumes "finite PROB" "(as \<in> valid_plans PROB)" "(s \<in> valid_states PROB)"
  shows "(\<exists>as'. 
    (exec_plan s as = exec_plan s as') 
    \<and> (subseq as' as) 
    \<and> (length as' \<le> problem_plan_bound_s PROB s)
  )"
proof -
  have "problem_plan_bound_s PROB s \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms(1, 3) bound_main_lemma_s 
    by blast
  then have 1: "Inf (PLS s as) \<le> problem_plan_bound_s PROB s"
    using assms problem_plan_bound_s_ge_min_pls[of PROB s as " 2 ^ card (prob_dom PROB) - 1"]
    by blast
  then obtain x where obtain_x: "x \<in> PLS s as \<and> x = Inf (PLS s as)"
    using PLS_nempty_and_has_min
    by blast
  then have "\<exists>as'. exec_plan s as = exec_plan s as' \<and> length as' = Inf (PLS s as) \<and> subseq as' as"
    using PLS_works[where s = s and as = as and x = "Inf (PLS s as)"]
      obtain_x 
    by fastforce
  then show "(\<exists>as'. 
    (exec_plan s as = exec_plan s as') \<and> (subseq as' as) 
    \<and> (length as' \<le> problem_plan_bound_s PROB s)
  )" 
    using 1
    by metis
qed


\<comment> \<open>NOTE skipped second declaration (declared twice in source).\<close>
lemma PLS_def_ITP2015: 
  fixes s as
  shows "PLS s as = {length as' | as'. (exec_plan s as' = exec_plan s as) \<and> (subseq as' as)}"
  using PLS_def 
  by blast


\<comment> \<open>NOTE Set comprehension had to be rewritten to image (there is no pattern matching in the part 
left of the pipe symbol).\<close>
lemma expanded_problem_plan_bound_charles_thm: 
  fixes PROB :: "'a problem" 
  shows " 
    problem_plan_bound_charles PROB 
    = Sup (
      {
        Inf (PLS_charles (fst p) (snd p) PROB) 
        | p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)})
  "
  unfolding problem_plan_bound_charles_def MPLS_charles_def
  by blast


lemma bound_main_lemma_charles_3:
  fixes PROB :: "'a problem"
  assumes "finite PROB"
  shows "MPLS_charles PROB \<noteq> {}"
proof -
  have 1: "[] \<in> valid_plans PROB" 
    using empty_plan_is_valid
    by auto
  then obtain s :: "'a state" where obtain_s: "s \<in> valid_states PROB"
    using assms valid_states_nempty
    by auto
  then  have "Inf (PLS_charles s [] PROB) \<in> MPLS_charles PROB" 
    unfolding MPLS_charles_def
    using 1
    by auto
  then show "MPLS_charles PROB \<noteq> {}"
    by blast
qed


lemma in_PLS_charles_leq_2_pow_n: 
  fixes PROB :: "'a problem" and s as
  assumes "finite PROB" "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
  shows "(\<exists>x. 
    (x \<in> PLS_charles s as PROB) 
    \<and> (x \<le> 2 ^ card (prob_dom PROB) - 1))
  "
proof -
  obtain as' where 1:
    "exec_plan s as = exec_plan s as'" "subseq as' as" "length as' \<le> 2 ^ card (prob_dom PROB) - 1" 
    using assms main_lemma
    by blast
  then have "as' \<in> valid_plans PROB"
    using assms(3) sublist_valid_plan 
    by blast 
  then have "length as' \<in> PLS_charles s as PROB"
    unfolding PLS_charles_def
    using 1
    by auto
  then show ?thesis 
    using 1(3)
    by fast
qed


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>NOTE this lemma retrieves `s`, `as` for a given @{term "x \<in> MPLS_charles PROB"} and characterizes it as
the minimum of 'PLS\_charles s as PROB'.\<close>
lemma x_in_MPLS_charles_then: 
  fixes PROB s as
  assumes "x \<in> MPLS_charles PROB"
  shows "\<exists>s as. 
    s \<in> valid_states PROB \<and> as \<in> valid_plans PROB \<and> x = Inf (PLS_charles s as PROB)
  "
proof -
  have "\<exists>p \<in> {p. (fst p) \<in> valid_states PROB \<and> (snd p) \<in> valid_plans PROB}. x = Inf (PLS_charles (fst p) (snd p) PROB)"
    using MPLS_charles_def assms 
    by fast
  then obtain p where 1:
    "p \<in> {p. (fst p) \<in> valid_states PROB \<and> (snd p) \<in> valid_plans PROB}" 
    "x = Inf (PLS_charles (fst p) (snd p) PROB)"
    by blast
  then have "fst p \<in> valid_states PROB" "snd p \<in> valid_plans PROB" 
    by blast+
  then show ?thesis 
    using 1 
    by fast
qed

lemma in_MPLS_charles_leq_2_pow_n:
  fixes PROB :: "'a problem" and x
  assumes "finite PROB" "x \<in> MPLS_charles PROB"
  shows "x \<le> 2 ^ card (prob_dom PROB) - 1"
proof -
  obtain s as where 1:
    "s \<in> valid_states PROB" "as \<in> valid_plans PROB" "x = Inf (PLS_charles s as PROB)"
    using assms(2) x_in_MPLS_charles_then
    by blast
  then obtain x' where 2: "x' \<in> PLS_charles s as PROB""x' \<le> 2 ^ card (prob_dom PROB) - 1"
    using assms(1) in_PLS_charles_leq_2_pow_n 
    by blast
  then have "x \<le> x'" 
    using 1(3) mem_le_imp_MIN_le
    by blast
  then show ?thesis 
    using 1 2
    by linarith
qed


lemma bound_main_lemma_charles:
  fixes PROB :: "'a problem"
  assumes "finite PROB"
  shows "problem_plan_bound_charles PROB \<le> 2 ^ (card (prob_dom PROB)) - 1"
proof -
  have 1: "\<forall>x\<in>MPLS_charles PROB. x \<le> 2 ^ (card (prob_dom PROB)) - 1"
    using assms in_MPLS_charles_leq_2_pow_n
    by blast
  then have "MPLS_charles PROB \<noteq> {}"
    using assms bound_main_lemma_charles_3
    by blast
  then have "Sup (MPLS_charles PROB) \<le> 2 ^ (card (prob_dom PROB)) - 1"
    using 1 bound_main_lemma_2 
    by meson
  then show ?thesis 
    using problem_plan_bound_charles_def
    by metis
qed


lemma bound_on_all_plans_bounds_PLS_charles:
  fixes P and f
  assumes "\<forall>(PROB :: 'a problem) as s.
    (P PROB) \<and> finite PROB \<and> (as \<in> valid_plans PROB) \<and> (s \<in> valid_states PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') \<and> (subseq as' as)\<and> (length as' < f PROB))
  "
  shows "(\<forall>PROB s as. 
    (P PROB) \<and> finite PROB \<and> (as \<in> valid_plans PROB)  \<and> (s \<in> valid_states PROB)
    \<longrightarrow> (\<exists>x. 
      (x \<in> PLS_charles s as PROB) 
      \<and> (x < f PROB)))
  "
proof -
  {
    \<comment> \<open>NOTE type for 's' had to be fixed (type mismatch in first proof step.\<close>
    fix PROB :: "'a problem" and as and s :: "'a state"
    assume P: 
      "P PROB" "finite PROB" "as \<in> valid_plans PROB" "s \<in> valid_states PROB"
      "(\<exists>as'. 
        (exec_plan s as = exec_plan s as') 
        \<and> (subseq as' as)
        \<and> (length as' < f PROB)
      )"
    then obtain as' where 1:
      "(exec_plan s as = exec_plan s as')" "(subseq as' as)" "(length as' < f PROB)"
      using P(5) 
      by blast
    then have 2: "as' \<in> valid_plans PROB"
      using P(3) sublist_valid_plan 
      by blast 
    let ?x = "length as'"
    have "?x \<in> PLS_charles s as PROB"
      unfolding PLS_charles_def
      using 1 2
      by auto
    then have "\<exists>x. x \<in> PLS_charles s as PROB \<and> x < f PROB"
      using 1 2 
      by blast
  }
  then show ?thesis 
    using assms 
    by auto
qed


\<comment> \<open>NOTE added lemma (refactored from `bound\_on\_all\_plans\_bounds\_MPLS\_charles`).\<close>
lemma bound_on_all_plans_bounds_MPLS_charles_i:
  assumes "\<forall>(PROB :: 'a problem) s as.
    (P PROB) \<and> finite PROB \<and> (as \<in> valid_plans PROB) \<and> (s \<in> valid_states PROB)
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') \<and> (subseq as' as) \<and> (length as' < f PROB))
  "
  shows "\<forall>(PROB :: 'a problem) s as.
    P PROB \<and> finite PROB \<and> as \<in> valid_plans PROB \<and> s \<in> valid_states PROB
    \<longrightarrow> Inf {n. n \<in> PLS_charles s as PROB} < f PROB
  "
proof -
  {
    fix PROB :: "'a problem" and s as
    have "P PROB \<and> finite PROB \<and> as \<in> valid_plans PROB \<and> s \<in> valid_states PROB
     \<longrightarrow> (\<exists>x. x \<in> PLS_charles s as PROB \<and> x < f PROB)
    "
      using assms bound_on_all_plans_bounds_PLS_charles[of P f]
      by blast
    then have "
      P PROB \<and> finite PROB \<and> as \<in> valid_plans PROB \<and> s \<in> valid_states PROB
      \<longrightarrow> Inf {n. n \<in> PLS_charles s as PROB} < f PROB
    "
      using mem_lt_imp_MIN_lt CollectI
      by metis
  }
  then show ?thesis
    by blast
qed

lemma bound_on_all_plans_bounds_MPLS_charles:
  fixes P f
  assumes "(\<forall>(PROB :: 'a problem) as s. 
    (P PROB) \<and> finite PROB \<and> (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' < f PROB)
    )
  )"
  shows "(\<forall>PROB x. 
    (P PROB) \<and> finite PROB
    \<longrightarrow> (x \<in> MPLS_charles PROB) 
    \<longrightarrow> (x < f PROB)
  )"
proof -
  have 1: "\<forall>(PROB :: 'a problem) s as. 
    P PROB \<and> finite PROB \<and> as \<in> valid_plans PROB \<and> s \<in> valid_states PROB
    \<longrightarrow> Inf {n. n \<in> PLS_charles s as PROB} < f PROB
  " 
    using assms bound_on_all_plans_bounds_MPLS_charles_i
    by blast
  moreover
  {
    fix PROB :: "'a problem" and x
    assume P1: "(P PROB)" "finite PROB" "x \<in> MPLS_charles PROB" 
    then obtain s as where a:
      "as \<in> valid_plans PROB" "s \<in> valid_states PROB" "x = Inf (PLS_charles s as PROB)"
      using x_in_MPLS_charles_then 
      by blast
    then have "Inf {n. n \<in> PLS_charles s as PROB} < f PROB"
      using 1 P1
      by blast
    then have "x < f PROB" 
      using a
      by simp
  }
  ultimately show ?thesis
    by blast
qed


\<comment> \<open>NOTE added lemma (refactored from 'bound\_on\_all\_plans\_bounds\_problem\_plan\_bound\_charles').\<close>
lemma bound_on_all_plans_bounds_problem_plan_bound_charles_i: 
  fixes PROB :: "'a problem"
  assumes "finite PROB" "\<forall>x \<in> MPLS_charles PROB. x < k"
  shows "Sup (MPLS_charles PROB) \<in> MPLS_charles PROB"
proof -
  have 1: "MPLS_charles PROB \<noteq> {}" 
    using assms(1) bound_main_lemma_charles_3 
    by auto
  then have "finite (MPLS_charles PROB)"
    using assms(2) finite_nat_set_iff_bounded
    by blast
  then show ?thesis 
    unfolding Sup_nat_def
    using 1
    by simp
qed

lemma bound_on_all_plans_bounds_problem_plan_bound_charles: 
  fixes P f
  assumes "(\<forall>(PROB :: 'a problem) as s. 
    (P PROB) \<and> finite PROB \<and> (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (\<exists>as'. 
      (exec_plan s as = exec_plan s as') 
      \<and> (subseq as' as)
      \<and> (length as' < f PROB)))
  "
  shows "(\<forall>PROB. 
    (P PROB) \<and> finite PROB \<longrightarrow> (problem_plan_bound_charles PROB < f PROB))
  "
proof -
  have 1: "\<forall>PROB x. P PROB \<and> finite PROB \<longrightarrow> x \<in> MPLS_charles PROB \<longrightarrow> x < f PROB"
    using assms bound_on_all_plans_bounds_MPLS_charles
    by blast
  moreover
  {
    fix PROB
    assume P: "P PROB" "finite PROB" 
    moreover have 2: "\<forall>x. x \<in> MPLS_charles PROB \<longrightarrow> x < f PROB" 
      using 1 P 
      by blast
    moreover
    {
      fix x
      assume P1: "x \<in> MPLS_charles PROB" 
      moreover have "x < f PROB"
        using P(1, 2) P1 1
        by presburger
      moreover have "MPLS_charles PROB \<noteq> {}" 
        using P1
        by blast
      moreover have "Sup (MPLS_charles PROB) < f PROB"
        using calculation(3) 2 bound_child_parent_not_eq_last_diff_paths[of "MPLS_charles PROB" "f PROB"] 
        by blast
      ultimately have "(problem_plan_bound_charles PROB < f PROB)"
        unfolding problem_plan_bound_charles_def 
        by blast
    }
    moreover have "Sup (MPLS_charles PROB) \<in> MPLS_charles PROB" 
      using P(2) 2 bound_on_all_plans_bounds_problem_plan_bound_charles_i
      by blast
    ultimately have "problem_plan_bound_charles PROB < f PROB"
      unfolding problem_plan_bound_charles_def 
      by blast
  }
  ultimately show ?thesis
    by blast
qed

subsection "The Relation between Diameter, Sublist Diameter and Recurrence Diameter Bounds."

text \<open> The goal of this subsection is to verify the relation between diameter, sublist diameter
and recurrence diameter bounds given by HOL4 Theorem 1, i.e.

  @{term "\<d>(\<delta>) \<le> \<l>(\<delta>) \<and> \<l>(\<delta>) \<le> \<r>\<d>(\<delta>)"}

where @{term "\<d>(\<delta>)"}, @{term "\<l>(\<delta>)"} and @{term "\<r>\<d>(\<delta>)"} denote the diameter, sublist diameter and recurrence diameter bounds.
[Abdualaziz et al., p.20]

The relevant lemmas are `sublistD\_bounds\_D` and `RD\_bounds\_sublistD` which culminate in 
theorem `sublistD\_bounds\_D\_and\_RD\_bounds\_sublistD`. \<close>

lemma sublistD_bounds_D:  
  fixes PROB :: "'a problem"
  assumes "finite PROB"
  shows "problem_plan_bound_charles PROB \<le> problem_plan_bound PROB"
proof -
  \<comment> \<open>NOTE obtain the premise needed for MP of 'bound\_on\_all\_plans\_bounds\_problem\_plan\_bound\_charles'.\<close>
  {
    fix PROB :: "'a problem" and s :: "'a state" and as
    assume P: "finite PROB" "s \<in> valid_states PROB" "as \<in> valid_plans PROB" 
    then have "\<exists>as'. 
      exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' \<le> problem_plan_bound PROB
    " 
      using problem_plan_bound_works
      by blast
    then have "\<exists>as'. 
      exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' < problem_plan_bound PROB + 1
    " 
      by force
  }
  then have "problem_plan_bound_charles PROB < problem_plan_bound PROB + 1"
    using assms bound_on_all_plans_bounds_problem_plan_bound_charles[where f = "\<lambda>PROB. problem_plan_bound PROB + 1"
        and P = "\<lambda>_. True"]
    by blast
  then show ?thesis
    by simp
qed


\<comment> \<open>NOTE added lemma (this was adapted from pred\_setScript.sml:4887 with exlusion of the premise for 
the empty set since `Max {}` is undefined in Isabelle/HOL.)\<close>
lemma MAX_SET_ELIM':
  fixes P Q
  assumes "finite P" "P \<noteq> {}" "(\<forall>x. (\<forall>y. y \<in> P \<longrightarrow> y \<le> x) \<and> x \<in> P \<longrightarrow> R x)"
  shows "R (Max P)" 
  using assms
  by force

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>NOTE adapted from pred\_setScript.sml:4895 (premise `finite P` was added).\<close>
lemma MIN_SET_ELIM':
  fixes P Q
  assumes "finite P" "P \<noteq> {}" "\<forall>x. (\<forall>y. y \<in> P \<longrightarrow> x \<le> y) \<and> x \<in> P \<longrightarrow> Q x"
  shows "Q (Min P)"
proof -
  let ?x="Min P" 
  have "Min P \<in> P" 
    using Min_in[OF assms(1) assms(2)]
    by simp
  moreover {
    fix y
    assume P: "y \<in> P"
    then have "?x \<le> y"
      using Min.coboundedI[OF assms(1)]
      by blast
    then have "Q ?x" using P assms
      by auto
  }
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma (refactored from `RD\_bounds\_sublistD`).\<close>
lemma RD_bounds_sublistD_i_a:
  fixes Pi :: "'a problem" 
  assumes "finite Pi"
  shows "finite {length p - 1 |p. valid_path Pi p \<and> distinct p}" 
proof -
  {
    let ?ss="{length p - 1 |p. valid_path Pi p \<and> distinct p}"
    let ?ss'="{p. valid_path Pi p \<and> distinct p}"
    have 1: "?ss = (\<lambda>x. length x - 1) ` ?ss'"
      by blast
    {
      \<comment> \<open>NOTE type of `valid\_states Pi` had to be asserted to match `FINITE\_valid\_states`.\<close>
      let ?S="{p. distinct p \<and> set p \<subseteq> (valid_states Pi :: 'a state set)}"
      {
        from assms have "finite (valid_states Pi :: 'a state set)" 
          using FINITE_valid_states[of Pi]
          by simp
        then have "finite ?S"
          using FINITE_ALL_DISTINCT_LISTS
          by blast
      }
      moreover {
        {
          fix x
          assume "x \<in> ?ss'"
          then have "x \<in> ?S" 
          proof (induction x)
            case (Cons a x)
            then have a: "valid_path Pi (a # x)" "distinct (a # x)"
              by blast+
            moreover {
              fix x' 
              assume P: "x' \<in> set (a # x)" 
              then have "x' \<in> valid_states Pi" 
              proof (cases "x")
                case Nil
                from a(1) Nil 
                have "a \<in> valid_states Pi"
                  by simp
                moreover from P Nil 
                have "x' = a" 
                  by force
                ultimately show ?thesis
                  by simp
              next
                case (Cons a' list)
                {
                  {
                    from Cons.prems have "valid_path Pi (a # x)"
                      by simp
                    then have "a \<in> valid_states Pi" "valid_path Pi (a' # list)"
                      using Cons 
                      by fastforce+
                  }
                  note a = this
                  moreover {
                    from Cons.prems have "distinct (a # x)"
                      by blast
                    then have "distinct (a' # list)" 
                      using Cons
                      by simp
                  }
                  ultimately 
                  have "(a' # list) \<in> ?ss'" 
                    by blast
                  then have "(a' # list) \<in> ?S" 
                    using Cons Cons.IH 
                    by argo
                }
                then show ?thesis
                  using P a(1) local.Cons set_ConsD
                  by fastforce
              qed
            }
            ultimately show ?case
              by blast
          qed simp
        }
        then have "?ss' \<subseteq> ?S"
          by blast
      }
      ultimately have "finite ?ss'"
        using rev_finite_subset 
        by auto
    }
    note 2 = this
    from 1 2 have "finite ?ss" 
      using finite_imageI
      by auto
  }
  then show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma (refactored from `RD\_bounds\_sublistD`).\<close>
lemma RD_bounds_sublistD_i_b:
  fixes Pi :: "'a problem" 
  shows "{length p - 1 |p. valid_path Pi p \<and> distinct p} \<noteq> {}"
proof -
  let ?Q="{length p - 1 |p. valid_path Pi p \<and> distinct p}"
  let ?Q'="{p. valid_path Pi p \<and> distinct p}"
  {
    have "valid_path Pi []"
      by simp
    moreover have "distinct []"
      by simp
    ultimately have "[] \<in> ?Q'"
      by simp
  }
  note 1 = this
  have "?Q = (\<lambda>p. length p - 1) ` ?Q'" 
    by blast
  then have "length [] - 1 \<in> ?Q"
    using 1
    by (metis (mono_tags, lifting) image_iff list.size(3))
  then show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma (refactored from `RD\_bounds\_sublistD`).\<close>
lemma RD_bounds_sublistD_i_c:
  fixes Pi :: "'a problem" and as :: "(('a, bool) fmap \<times> ('a, bool) fmap) list" and x 
    and s :: "('a, bool) fmap" 
  assumes "s \<in> valid_states Pi" "as \<in> valid_plans Pi" 
    "(\<forall>y. y \<in> {length p - 1 |p. valid_path Pi p \<and> distinct p} \<longrightarrow> y \<le> x)" 
    "x \<in> {length p - 1 |p. valid_path Pi p \<and> distinct p}"
  shows "Min (PLS s as) \<le> Max {length p - 1 |p. valid_path Pi p \<and> distinct p}" 
proof -
  let ?P="(PLS s as)"
  let ?Q="{length p - 1 |p. valid_path Pi p \<and> distinct p}"
  from assms(4) obtain p where 1:
    "x = length p - 1" "valid_path Pi p" "distinct p"
    by blast
  {
    fix p'
    assume "valid_path Pi p'" "distinct p'" 
    then obtain y where "y \<in> ?Q" "y = length p' - 1" 
      by blast
        \<comment> \<open>NOTE we cannot infer @{term "length p' - 1 \<le> length p - 1"} since `length p' = 0` might be true.\<close>
    then have a: "length p' - 1 \<le> length p - 1" 
      using assms(3) 1(1) 
      by meson
  }
  note 2 = this
  {
    from finite_PLS PLS_NEMPTY
    have "finite (PLS s as)" "PLS s as \<noteq> {}"
      by blast+
    moreover {
      fix n
      assume P: "(\<forall>y. y \<in> PLS s as \<longrightarrow> n \<le> y)" "n \<in> PLS s as"
      from P(2) obtain as' where i: 
        "n = length as'" "exec_plan s as' = exec_plan s as" "subseq as' as"
        unfolding PLS_def
        by blast
      let ?p'="statelist' s as'"
      {
        have "length as' = length ?p' - 1" 
          by (simp add: LENGTH_statelist')        
            \<comment> \<open>MARKER (topologicalPropsScript.sml:195)\<close>
        have "1 + (length p - 1) = length p - 1 + 1" 
          by presburger
            \<comment> \<open>MARKER (topologicalPropsScript.sml:200)\<close>
        {
          from assms(2) i(3) sublist_valid_plan
          have "as' \<in> valid_plans Pi" 
            by blast
          then have "valid_path Pi ?p'"
            using assms(1) valid_path_statelist'
            by auto
        }
        moreover {
          {
            assume C: "\<not>distinct ?p'"
              \<comment> \<open>NOTE renamed variable `drop` to `drop'` to avoid shadowing of the function by the 
            same name in Isabelle/HOL.\<close>
            then obtain rs pfx drop' tail where C_1: "?p' = pfx @ [rs] @ drop' @ [rs] @ tail" 
              using not_distinct_decomp[OF C]
              by fast
            let ?pfxn="length pfx"
            have C_2: "?p' ! ?pfxn = rs"
              by (simp add: C_1) 
            from LENGTH_statelist'
            have C_3: "length as' + 1 = length ?p'" 
              by metis
            then have "?pfxn \<le> length as'"
              using C_1
              by fastforce
            then have C_4: "exec_plan s (take ?pfxn as') = rs" 
              using C_2 statelist'_TAKE
              by blast
            let ?prsd = "length (pfx @ [rs] @ drop')"
            let ?ap1 = "take ?pfxn as'" 
              \<comment> \<open>MARKER (topologicalPropsScript.sml:215)\<close>
            from C_1 
            have C_5: "?p' ! ?prsd = rs"
              by (metis append_Cons length_append nth_append_length nth_append_length_plus)
            from C_1 C_3 
            have C_6: "?prsd \<le> length as'" 
              by simp
            then have C_7: "exec_plan s (take ?prsd as') = rs" 
              using C_5 statelist'_TAKE
              by auto
            let ?ap2="take ?prsd as'"
            let ?asfx="drop ?prsd as'" 
            have C_8: "as' = ?ap2 @ ?asfx"
              by force
            then have "exec_plan s as' = exec_plan (exec_plan s ?ap2) ?asfx"
              using exec_plan_Append
              by metis
            then have C_9: "exec_plan s as' = exec_plan s (?ap1 @ ?asfx)"
              using C_4 C_7 exec_plan_Append
              by metis
            from C_6 
            have C_10: "(length ?ap1 = ?pfxn) \<and> (length ?ap2 = ?prsd)" 
              by fastforce
            then have C_11: "length (?ap1 @ ?asfx) < length (?ap2 @ ?asfx)"
              by auto
            {         
              from C_10 
              have "?pfxn + length ?asfx = length (?ap1 @ ?asfx)"   
                by simp
              from C_9 i(2)
              have C_12: "exec_plan s (?ap1 @ ?asfx) = exec_plan s as" 
                by argo
              {
                {
                  {
                    have "prefix ?ap1 ?ap2"
                      by (metis (no_types) length_append prefix_def take_add) 
                    then have "subseq ?ap1 ?ap2"
                      using isPREFIX_sublist
                      by blast
                  }
                  moreover have "sublist ?asfx ?asfx"
                    using sublist_refl
                    by blast
                  ultimately have "subseq (?ap1 @ ?asfx) as'"
                    using C_8 subseq_append
                    by metis
                }
                moreover from i(3)
                have "subseq as' as"
                  by simp
                ultimately have "subseq (?ap1 @ ?asfx) as"
                  using sublist_trans
                  by blast
              }
              then have "length (?ap1 @ ?asfx) \<in> PLS s as"
                unfolding PLS_def 
                using C_12 
                by blast
            }
            then have False 
              using P(1) i(1) C_10
              by auto
          }
          hence "distinct ?p'" 
            by auto
        }
        ultimately have "length ?p' - 1 \<le> length p - 1" 
          using 2 
          by blast
      }
      note ii = this
      {
        from i(1) have "n + 1 = length ?p'"
          using LENGTH_statelist'[symmetric]
          by blast
        also have "\<dots> \<le> 1 + (length p - 1)"
          using ii
          by linarith
        finally have "n \<le> length p - 1" 
          by fastforce
      }
      then have "n \<le> length p - 1"
        by blast
    }
    ultimately have "Min ?P \<le> length p - 1" 
      using MIN_SET_ELIM'[where P="?P" and Q="\<lambda>x. x \<le> length p - 1"]
      by blast
  }
  note 3 = this
  {
    have "length p - 1 \<le> Max {length p - 1 |p. valid_path Pi p \<and> distinct p}" 
      using assms(3, 4) 1(1)
      by (metis (no_types, lifting) Sup_nat_def assms(3) cSup_eq_maximum)  
    moreover 
    have "Min (PLS s as) \<le> length p - 1"
      using 3
      by blast
    ultimately 
    have "Min (PLS s as) \<le> Max {length p - 1 |p. valid_path Pi p \<and> distinct p}"
      by linarith
  }
  then show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma (refactored from `RD\_bounds\_sublistD`).\<close>
lemma RD_bounds_sublistD_i:
  fixes Pi :: "'a problem" and x
  assumes "finite Pi" "(\<forall>y. y \<in> MPLS Pi \<longrightarrow> y \<le> x)" "x \<in> MPLS Pi" 
  shows "x \<le> Max {length p - 1 |p. valid_path Pi p \<and> distinct p}" 
proof -
  {
    let ?P="MPLS Pi"
    let ?Q="{length p - 1 |p. valid_path Pi p \<and> distinct p}"
    from assms(3) 
    obtain s as where 1:
      "s \<in> valid_states Pi" "as \<in> valid_plans Pi" "x = Inf (PLS s as)"
      unfolding MPLS_def
      by fast
    have "x \<le> Max ?Q" proof -
      text \<open> Show that `x` is not only the infimum but also the minimum of `PLS s as`.\<close>
      {
        have "finite (PLS s as)" 
          using finite_PLS 
          by auto
        moreover 
        have "PLS s as \<noteq> {}" 
          using PLS_NEMPTY
          by auto
        ultimately 
        have a: "Inf (PLS s as) = Min (PLS s as)" 
          using cInf_eq_Min[of "PLS s as"]
          by blast
        from 1(3) a have "x = Min (PLS s as)"
          by blast
      }
      note a = this
      {
        let ?limit="Min (PLS s as)"
        from assms(1) 
        have a: "finite ?Q" 
          using RD_bounds_sublistD_i_a
          by blast
        have b: "?Q \<noteq> {}"
          using RD_bounds_sublistD_i_b 
          by fast
        from 1(1, 2) 
        have c: "\<forall>x. (\<forall>y. y \<in> ?Q \<longrightarrow> y \<le> x) \<and> x \<in> ?Q \<longrightarrow> ?limit \<le> Max ?Q" 
          using RD_bounds_sublistD_i_c
          by blast
        have "?limit \<le> Max ?Q" 
          using MAX_SET_ELIM'[where P="?Q" and R="\<lambda>x. ?limit \<le> Max ?Q", OF a b c]
          by blast
      }
      note b = this
      from a b show "x \<le> Max ?Q"
        by blast
    qed
  }
  then show ?thesis
    using assms
    unfolding MPLS_def
    by blast
qed

\<comment> \<open>NOTE type of `Pi` had to be fixed for use of `FINITE\_valid\_states`.\<close>
lemma RD_bounds_sublistD: 
  fixes Pi :: "'a problem"
  assumes "finite Pi"
  shows "problem_plan_bound Pi \<le> RD Pi"
proof -
  let ?P="MPLS Pi"
  let ?Q="{length p - 1 |p. valid_path Pi p \<and> distinct p}"
  {
    from assms 
    have 1: "finite ?P" 
      using FINITE_MPLS
      by blast
    from assms 
    have 2: "?P \<noteq> {}"
      using MPLS_nempty
      by blast
    from assms 
    have 3: "\<forall>x. (\<forall>y. y \<in> ?P \<longrightarrow> y \<le> x) \<and> x \<in> ?P \<longrightarrow> x \<le> Max ?Q"
      using RD_bounds_sublistD_i 
      by blast
    have "Max ?P \<le> Max ?Q"
      using MAX_SET_ELIM'[OF 1 2 3]
      by blast
  }
  then show ?thesis 
    unfolding problem_plan_bound_def RD_def Sup_nat_def
    by blast
qed


\<comment> \<open>NOTE type for `PROB` had to be fixed in order to be able to match `sublistD\_bounds\_D`.\<close>
theorem sublistD_bounds_D_and_RD_bounds_sublistD: 
  fixes PROB :: "'a problem"
  assumes "finite PROB"
  shows "
    problem_plan_bound_charles PROB \<le> problem_plan_bound PROB 
    \<and> problem_plan_bound PROB \<le> RD PROB
  "
  using assms sublistD_bounds_D RD_bounds_sublistD 
  by auto


\<comment> \<open>NOTE type of `PROB` had to be fixed for MP of lemmas.\<close>
lemma empty_problem_bound: 
  fixes PROB :: "'a problem"
  assumes "(prob_dom PROB = {})"
  shows "(problem_plan_bound PROB = 0)"
proof -
  {
    fix PROB' and as :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) list" and s :: "('a, 'b) fmap"
    assume 
      "finite PROB" "prob_dom PROB' = {}" "s \<in> valid_states PROB'" "as \<in> valid_plans PROB'"
    then have "exec_plan s [] = exec_plan s as"
      using empty_prob_dom_imp_empty_plan_always_good
      by blast
    then have "(\<exists>as'. exec_plan s as = exec_plan s as' \<and> subseq as' as \<and> length as' < 1)"
      by force
  }
  then show ?thesis 
    using bound_on_all_plans_bounds_problem_plan_bound_[where P="\<lambda>P. prob_dom P = {}" and f="\<lambda>P. 1", of PROB]
    using assms empty_prob_dom_finite 
    by blast 
qed


lemma problem_plan_bound_works':
  fixes PROB :: "'a problem" and as s
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'. 
    (exec_plan s as' = exec_plan s as) 
    \<and> (subseq as' as)
    \<and> (length as' \<le> problem_plan_bound PROB) 
    \<and> (sat_precond_as s as')
  )"
proof -
  obtain as' where 1:
    "exec_plan s as = exec_plan s as'" "subseq as' as" "length as' \<le> problem_plan_bound PROB"
    using assms problem_plan_bound_works 
    by blast
      \<comment> \<open>NOTE this step seems to be handled implicitely in original proof.\<close>
  moreover have "rem_condless_act s [] as' \<in> valid_plans PROB"
    using assms(3) 1(2) rem_condless_valid_10 sublist_valid_plan
    by blast
  moreover have "subseq (rem_condless_act s [] as') as'" 
    using rem_condless_valid_8 
    by blast
  moreover have "length (rem_condless_act s [] as') \<le> length as'" 
    using rem_condless_valid_3
    by blast
  moreover have "sat_precond_as s (rem_condless_act s [] as')"
    using rem_condless_valid_2
    by blast
  moreover have "exec_plan s as' = exec_plan s (rem_condless_act s [] as')"
    using rem_condless_valid_1
    by blast
  ultimately show ?thesis
    by fastforce
qed


\<comment> \<open>TODO remove? Can be solved directly with 'TopologicalProps.bound\_on\_all\_plans\_bounds\_problem\_plan\_bound\_thesis'.\<close>
lemma problem_plan_bound_UBound: 
  assumes "(\<forall>as s.
    (s \<in> valid_states PROB) 
    \<and> (as \<in> valid_plans PROB)
    \<longrightarrow> (\<exists>as'.
      (exec_plan s as = exec_plan s as') 
      \<and> subseq as' as 
      \<and> (length as' < f PROB)
    )
  )" "finite PROB"
  shows "(problem_plan_bound PROB < f PROB)"
proof -
  let ?P = "\<lambda>Pr. PROB = Pr"
  have "?P PROB" by simp
  then show ?thesis
    using assms bound_on_all_plans_bounds_problem_plan_bound_[where P = ?P] 
    by force
qed 

subsection "Traversal Diameter"


\<comment> \<open>NOTE name shortened.\<close>
definition traversed_states where
  "traversed_states s as \<equiv> set (state_list s as)" 


lemma finite_traversed_states: "finite (traversed_states s as)"
  unfolding traversed_states_def
  by simp


lemma traversed_states_nempty: "traversed_states s as \<noteq> {}"
  unfolding traversed_states_def 
  by (induction as) auto


lemma traversed_states_geq_1: 
  fixes s
  shows "1 \<le> card (traversed_states s as)"
proof -
  have "card (traversed_states s as) \<noteq> 0"
    using traversed_states_nempty finite_traversed_states card_0_eq
    by blast
  then show "1 \<le> card (traversed_states s as)"
    by linarith 
qed


lemma init_is_traversed: "s \<in> traversed_states s as"
  unfolding traversed_states_def
  by (induction as) auto


\<comment> \<open>NOTE name shortened.\<close>
definition td where
  "td PROB \<equiv> Sup {
    (card (traversed_states (fst p) (snd p))) - 1 
    | p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)}
  "


lemma traversed_states_rem_condless_act: "\<And>s. 
  traversed_states s (rem_condless_act s [] as) = traversed_states s as
"
  apply(induction as)
  apply(auto simp add: traversed_states_def rem_condless_act_cons)
  subgoal by (simp add: state_succ_pair)
  subgoal using init_is_traversed traversed_states_def by blast
  subgoal by (simp add: state_succ_pair) 
  done

\<comment> \<open>NOTE added lemma.\<close>
lemma td_UBound_i: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set"
  assumes "finite PROB" 
  shows "
  {
    (card (traversed_states (fst p) (snd p))) - 1 
    | p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)}
  \<noteq> {}
  "
proof -
  let ?S="{p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)}"
  obtain s :: "'a state" where "s \<in> valid_states PROB" 
    using assms valid_states_nempty
    by blast
  moreover have "[] \<in> valid_plans PROB"
    using empty_plan_is_valid
    by auto
  ultimately have "?S \<noteq> {}"
    using assms valid_states_nempty 
    by auto  
  then show ?thesis
    by blast 
qed

lemma td_UBound: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set" 
  assumes "finite PROB" "(\<forall>s as. 
    (sat_precond_as s as) \<and> (s \<in> valid_states PROB) \<and> (as \<in> valid_plans PROB) 
    \<longrightarrow> (card (traversed_states s as) \<le> k)
  )"
  shows "(td PROB \<le> k - 1)"
proof -
  let ?S="{
    (card (traversed_states (fst p) (snd p))) - 1 
    | p. (fst p \<in> valid_states PROB) \<and> (snd p \<in> valid_plans PROB)}
  "
  {
    fix x
    assume "x \<in> ?S"
    then obtain p where 1:
      "x = card (traversed_states (fst p) (snd p)) - 1" "fst p \<in> valid_states PROB" 
      "snd p \<in> valid_plans PROB"
      by blast
    let ?s="fst p"
    let ?as="snd p" 
    {
      let ?as'="(rem_condless_act ?s [] ?as)"
      have 2: "traversed_states ?s ?as = traversed_states ?s ?as'"
        using traversed_states_rem_condless_act
        by blast
      moreover have "sat_precond_as ?s ?as'"
        using rem_condless_valid_2
        by blast
      moreover have "?as' \<in> valid_plans PROB"
        using 1(3) rem_condless_valid_10
        by blast
      ultimately have "card (traversed_states ?s ?as') \<le> k"
        using assms(2) 1(2)
        by blast 
      then have "card (traversed_states ?s ?as) \<le> k"
        using 2
        by argo
    }
    then have "x \<le> k - 1" 
      using 1
      by linarith
  }
  moreover have "?S \<noteq> {}"
    using assms td_UBound_i
    by fast
  ultimately show ?thesis
    unfolding td_def
    using td_UBound_i bound_main_lemma_2[of ?S "k - 1"]
    by presburger
qed


end