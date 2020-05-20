section \<open>Iterating a Commutative Computation Concurrently\<close>

theory Parallel_Multiset_Fold
  imports "HOL-Library.Multiset"
begin

text \<open>
This theory formalizes a deep embedding of a simple parallel computation model.
In this model, we formalize a computation scheme to execute a fold-function over a
commutative operation concurrently, and prove it correct.
\<close>

subsection \<open>Misc\<close>

(* TODO: Move *)
lemma (in comp_fun_commute) fold_mset_rewr: "fold_mset f a (mset l) = fold f l a" 
  by (induction l arbitrary: a; clarsimp; metis fold_mset_fun_left_comm)

lemma finite_set_of_finite_maps:
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "finite A"
    and "finite B"
  shows "finite {m. dom m \<subseteq> A \<and> ran m \<subseteq> B}"
proof -
  have "{m. dom m \<subseteq> A \<and> ran m \<subseteq> B} \<subseteq> (\<Union> S \<in> {S. S \<subseteq> A}. {m. dom m = S \<and> ran m \<subseteq> B})"
    by auto
  moreover have "finite \<dots>"
    using assms by (auto intro!: finite_set_of_finite_maps intro: finite_subset)
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma wf_rtranclp_ev_induct[consumes 1, case_names step]:
  assumes "wf {(x, y). R y x}" and step: "\<And> x. R\<^sup>*\<^sup>* a x \<Longrightarrow> P x \<or> (\<exists> y. R x y)"
  shows "\<exists>x. P x \<and> R\<^sup>*\<^sup>* a x"
proof -
  have "\<exists>y. P y \<and> R\<^sup>*\<^sup>* x y" if "R\<^sup>*\<^sup>* a x" for x
    using assms(1) that
  proof induction
    case (less x)
    from step[OF \<open>R\<^sup>*\<^sup>* a x\<close>] have "P x \<or> (\<exists>y. R x y)" .
    then show ?case
    proof
      assume "P x"
      then show ?case
        by auto
    next
      assume "\<exists>y. R x y"
      then obtain y where "R x y" ..
      with less(1)[of y] less(2) show ?thesis
        by simp (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_into_rtrancl)
    qed
  qed
  then show ?thesis
    by blast
qed

subsection \<open>The Concurrent System\<close>
text \<open>
  A state of our concurrent systems consists of a list of tasks,
  a partial map from threads to the task they are currently working on,
  and the current computation result.\<close>
type_synonym ('a, 's) state = "'a list \<times> (nat \<rightharpoonup> 'a) \<times> 's"

context comp_fun_commute
begin

context
  fixes n :: nat \<comment> \<open>The number of threads.\<close>
  assumes n_gt_0[simp, intro]: "n > 0"
begin

text \<open>
  A state is \<^emph>\<open>final\<close> if there are no remaining tasks and if all workers have finished their work.\<close>
definition
  "final \<equiv> \<lambda>(ts, ws, r). ts = [] \<and> dom ws \<inter> {0..<n} = {}"

text \<open>At any point a thread can:
  \<^item> pick a new task from the queue if it is currently not busy
  \<^item> or execute its current task.\<close>
inductive step :: "('a, 'b) state \<Rightarrow> ('a, 'b) state \<Rightarrow> bool" where
  pick: "step (t # ts, ws, s) (ts, ws(i := Some t), s)"   if "ws i = None"   and "i < n"
| exec: "step (ts, ws, s)     (ts, ws(i := None), f a s)" if "ws i = Some a" and "i < n"

lemma no_deadlock:
  assumes "\<not> final cfg"
  shows "\<exists>cfg'. step cfg cfg'"
  using assms
  apply (cases cfg)
  apply safe
  subgoal for ts ws s
    by (cases ts; cases "ws 0") (auto 4 5 simp: final_def intro: step.intros)
  done

lemma wf_step:
  "wf {((ts', ws', r'), (ts, ws, r)).
    step (ts, ws, r) (ts', ws', r') \<and> set ts' \<subseteq> S \<and> dom ws \<subseteq> {0..<n} \<and> ran ws \<subseteq> S}"
  if "finite S"
proof -
  let ?R1 = "{(x, y). dom x \<subset> dom y \<and> ran x \<subseteq> S \<and> dom y \<subseteq> {0..<n} \<and> ran y \<subseteq> S}"
  have "?R1 \<subseteq> {y. dom y \<subseteq> {0..<n} \<and> ran y \<subseteq> S} \<times> {y. dom y \<subseteq> {0..<n} \<and> ran y \<subseteq> S}"
    by auto
  then have "finite ?R1"
    using \<open>finite S\<close> by - (erule finite_subset, auto intro: finite_set_of_finite_maps)
  then have [intro]: "wf ?R1"
    apply (rule finite_acyclic_wf)
    apply (rule preorder_class.acyclicI_order[where f = "\<lambda>x. n - card (dom x)"])
    apply clarsimp
    by (metis (full_types) 
        cancel_ab_semigroup_add_class.diff_right_commute diff_diff_cancel domD domI
        psubsetI psubset_card_mono subset_eq_atLeast0_lessThan_card
        subset_eq_atLeast0_lessThan_finite zero_less_diff)
  let ?R = "measure length <*lex*> ?R1 <*lex*> {}"
  have "wf ?R"
    by auto
  then show ?thesis
    apply (rule wf_subset)
    apply clarsimp
    apply (erule step.cases; clarsimp)
    by (smt
        Diff_iff domIff fun_upd_apply mem_Collect_eq option.simps(3) psubsetI ran_def
        singletonI subset_iff)
qed

context
  fixes ts :: "'a list" and start :: "'b"
begin

definition
  "s\<^sub>0 = (ts, \<lambda>_. None, start)"

definition "reachable \<equiv> (step\<^sup>*\<^sup>*) s\<^sub>0"

lemma reachable0[simp]: "reachable s\<^sub>0"
  unfolding reachable_def by auto

definition "is_invar I \<equiv> I s\<^sub>0 \<and> (\<forall>s s'. reachable s \<and> I s \<and> step s s' \<longrightarrow> I s')"

lemma is_invarI[intro?]: 
  "\<lbrakk> I s\<^sub>0; \<And>s s'. \<lbrakk> reachable s; I s; step s s'\<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> is_invar I"
  by (auto simp: is_invar_def)

lemma invar_reachable: "is_invar I \<Longrightarrow> reachable s \<Longrightarrow> I s"  
  unfolding reachable_def
  by rotate_tac (induction rule: rtranclp_induct, auto simp: is_invar_def reachable_def)

definition
  "invar \<equiv> \<lambda>(ts2, ws, r).
    (\<exists>ts1.
      mset ts = ts1 + {# the (ws i). i \<in># mset_set (dom ws \<inter> {0..<n}) #} + mset ts2
    \<and> r = fold_mset f start ts1
    \<and> set ts2 \<subseteq> set ts \<and> ran ws \<subseteq> set ts \<and> dom ws \<subseteq> {0..<n})"

lemma invariant:
  "is_invar invar"
  apply rule
  subgoal
    unfolding s\<^sub>0_def unfolding invar_def by simp
  subgoal
    unfolding invar_def
    apply (elim step.cases)
     apply (clarsimp split: option.split_asm)
    subgoal for ws i t ts ts1
      apply (rule exI[where x = ts1])
       apply (subst mset_set.insert)
         apply (auto intro!: multiset.map_cong0)
      done
    apply (clarsimp split!: prod.splits)
    subgoal for ws i a ts ts1
      apply (rule exI[where x = "add_mset a ts1"])
         apply (subst Diff_Int_distrib2)
         apply (subst mset_set.remove)
           apply (auto intro!: multiset.map_cong0 split: if_split_asm simp: ran_def)
      done
    done
  done

lemma final_state_correct1:
  assumes "invar (ts', ms, r)" "final (ts', ms, r)"
  shows "r = fold_mset f start (mset ts)"
  using assms unfolding invar_def final_def by auto

lemma final_state_correct2:
  assumes "reachable (ts', ms, r)" "final (ts', ms, r)"
  shows "r = fold_mset f start (mset ts)"
  using assms by - (rule final_state_correct1, rule invar_reachable[OF invariant])

text \<open>Soundness: whenever we reach a final state, the computation result is correct.\<close>
theorem final_state_correct:
  assumes "reachable (ts', ms, r)" "final (ts', ms, r)"
  shows "r = fold f ts start"
  using final_state_correct2[OF assms] by (simp add: fold_mset_rewr)

text \<open>Termination: at any point during the program execution, we can continue to a final state.
That is, the computation always terminates.
\<close>
theorem "termination":
  assumes "reachable s"
  shows "\<exists>s'. final s' \<and> step\<^sup>*\<^sup>* s s'"
proof -
  have "{(s', s). step s s' \<and> reachable s} \<subseteq> {(s', s). step s s' \<and> reachable s \<and> reachable s'}"
    unfolding reachable_def by auto
  also have "\<dots> \<subseteq> {((ts', ws', r'), (ts1, ws, r)).
    step (ts1, ws, r) (ts', ws', r') \<and> set ts' \<subseteq> set ts \<and> dom ws \<subseteq> {0..<n} \<and> ran ws \<subseteq> set ts}"
    by (force dest!: invar_reachable[OF invariant] simp: invar_def)
  finally have "wf {(s', s). step s s' \<and> reachable s}"
    by (elim wf_subset[OF wf_step, rotated]) simp
  then have "\<exists>s'. final s' \<and> (\<lambda>s s'. step s s' \<and> reachable s)\<^sup>*\<^sup>* s s'"
  proof (induction rule: wf_rtranclp_ev_induct)
    case (step x)
    then have "(\<lambda>s s'. step s s')\<^sup>*\<^sup>* s x"
      by (elim mono_rtranclp[rule_format, rotated] conjE)
    with \<open>reachable s\<close> have "reachable x"
      unfolding reachable_def by auto
    then show ?case
      using no_deadlock[of x] by auto
  qed
  then show ?thesis
    apply clarsimp
    apply (intro exI conjI, assumption)
    apply (rule mono_rtranclp[rule_format])
     apply auto
    done
qed

end (* Fixed task list *)

end (* Fixed number of workers *)

end (* Commutative function *)

text \<open>The main theorems outside the locale:\<close>
thm comp_fun_commute.final_state_correct comp_fun_commute.termination

end (* End of theory *)