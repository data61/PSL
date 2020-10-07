(* Authors: Lammich, Wimmer *)
section \<open>Generic Worklist Algorithm with Subsumption\<close>
theory Worklist_Subsumption
  imports "../Sepref"
begin

subsection \<open>Utilities\<close>
definition take_from_set where
  "take_from_set s = ASSERT (s \<noteq> {}) \<then> SPEC (\<lambda> (x, s'). x \<in> s \<and> s' = s - {x})"

lemma take_from_set_correct:
  assumes "s \<noteq> {}"
  shows "take_from_set s \<le> SPEC (\<lambda> (x, s'). x \<in> s \<and> s' = s - {x})"
using assms unfolding take_from_set_def by simp

lemmas [refine_vcg] = take_from_set_correct[THEN order.trans]



definition take_from_mset where
  "take_from_mset s = ASSERT (s \<noteq> {#}) \<then> SPEC (\<lambda> (x, s'). x \<in># s \<and> s' = s - {#x#})"

lemma take_from_mset_correct:
  assumes "s \<noteq> {#}"
  shows "take_from_mset s \<le> SPEC (\<lambda> (x, s'). x \<in># s \<and> s' = s - {#x#})"
using assms unfolding take_from_mset_def by simp

lemmas [refine_vcg] = take_from_mset_correct[THEN order.trans]


lemma set_mset_mp: "set_mset m \<subseteq> s \<Longrightarrow> n < count m x \<Longrightarrow> x\<in>s" 
  by (meson count_greater_zero_iff le_less_trans subsetCE zero_le)

lemma pred_not_lt_is_zero: "(\<not> n - Suc 0 < n) \<longleftrightarrow> n=0" by auto


subsection \<open>Search Spaces\<close>
text \<open>
  A search space consists of a step relation, a start state, 
  a final state predicate, and a subsumption preorder.
\<close>
locale Search_Space_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>Step relation\<close>
    and a\<^sub>0 :: 'a                \<comment> \<open>Start state\<close> 
    and F :: "'a \<Rightarrow> bool"      \<comment> \<open>Final states\<close>
    and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) \<comment> \<open>Subsumption preorder\<close>
begin
  definition reachable where
    "reachable = E\<^sup>*\<^sup>* a\<^sub>0"

  definition "F_reachable \<equiv> \<exists>a. reachable a \<and> F a"

end

text \<open>The set of reachable states must be finite, 
  subsumption must be a preorder, and be compatible with steps and final states.\<close>
locale Search_Space = Search_Space_Defs +
  assumes finite_reachable: "finite {a. reachable a}"

  assumes refl[intro!, simp]: "a \<preceq> a"
      and trans[trans]: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"

  assumes mono: "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> \<exists> b'. E b b' \<and> a' \<preceq> b'"
      and F_mono: "a \<preceq> a' \<Longrightarrow> F a \<Longrightarrow> F a'"
begin

  lemma start_reachable[intro!, simp]:
    "reachable a\<^sub>0"
  unfolding reachable_def by simp

  lemma step_reachable:
    assumes "reachable a" "E a a'"
    shows "reachable a'"
  using assms unfolding reachable_def by simp


  lemma finitely_branching:
    assumes "reachable a"  
    shows "finite (Collect (E a))"
    by (metis assms finite_reachable finite_subset mem_Collect_eq step_reachable subsetI)
    


end

subsection \<open>Worklist Algorithm\<close>

term card

context Search_Space_Defs begin
  definition "worklist_var = inv_image (finite_psupset (Collect reachable) <*lex*> measure size) (\<lambda> (a, b,c). (a,b))"
  
  definition "worklist_inv_frontier passed wait = 
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b'))"
  
  definition "start_subsumed passed wait = (\<exists> a \<in> passed \<union> set_mset wait. a\<^sub>0 \<preceq> a)"

  definition "worklist_inv \<equiv> \<lambda> (passed, wait, brk).
    passed \<subseteq> Collect reachable \<and>
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow> 
      worklist_inv_frontier passed wait 
    \<and> (\<forall> a \<in> passed \<union> set_mset wait. \<not> F a) 
    \<and> start_subsumed passed wait
    \<and> set_mset wait \<subseteq> Collect reachable)
    "

  definition "add_succ_spec wait a \<equiv> SPEC (\<lambda>(wait',brk). 
    if \<exists>a'. E a a' \<and> F a' then 
      brk
    else set_mset wait' = set_mset wait \<union> {a' . E a a'} \<and> \<not>brk
  )"

  definition worklist_algo where
    "worklist_algo = do
      { 
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = {#a\<^sub>0#};
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              { 
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ_spec wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

end

subsubsection \<open>Correctness Proof\<close>

context Search_Space begin

  lemma wf_worklist_var:
    "wf worklist_var"
  unfolding worklist_var_def by (auto simp: finite_reachable)

  context
  begin
  
  private lemma aux1:
    assumes "\<forall>x\<in>passed. \<not> a \<preceq> x"
        and "passed \<subseteq> Collect reachable"
        and "reachable a"
    shows "
    ((insert a passed, wait', brk'),
     passed, wait, brk)
    \<in> worklist_var"
  proof -
    from assms have "a \<notin> passed" by auto
    with assms(2,3) show ?thesis
    by (auto simp: worklist_inv_def worklist_var_def finite_psupset_def)
  qed

  private lemma aux2:
    assumes
      "a' \<in> passed"
      "a \<preceq> a'"
      "a \<in># wait"
      "worklist_inv_frontier passed wait"
    shows "worklist_inv_frontier passed (wait - {#a#})"
    using assms unfolding worklist_inv_frontier_def 
    using trans 
    apply clarsimp
    by (metis (no_types, lifting) Un_iff count_eq_zero_iff count_single mset_contains_eq mset_un_cases)

  private lemma aux5:
    assumes
      "a' \<in> passed"
      "a \<preceq> a'"
      "a \<in># wait"
      "start_subsumed passed wait"
    shows "start_subsumed passed (wait - {#a#})"
    using assms unfolding start_subsumed_def apply clarsimp
    by (metis Un_iff insert_DiffM2 local.trans mset_right_cancel_elem)

  private lemma aux3:
    assumes
      "set_mset wait \<subseteq> Collect reachable"
      "a \<in># wait"
      "set_mset wait' = set_mset (wait - {#a#}) \<union> Collect (E a)"
      "worklist_inv_frontier passed wait"
    shows "worklist_inv_frontier (insert a passed) wait'"
  proof -
    from assms(1,2) have "reachable a"
      by (simp add: subset_iff) 
    with finitely_branching have [simp, intro!]: "finite (Collect (E a))" . 

    from assms(2,3,4) show ?thesis unfolding worklist_inv_frontier_def
      by (metis Un_iff insert_DiffM insert_iff local.refl mem_Collect_eq set_mset_add_mset_insert)
  qed    

  private lemma aux6:
    assumes
      "a \<in># wait"
      "start_subsumed passed wait"
      "set_mset wait' = set_mset (wait - {#a#}) \<union> Collect (E a)"
    shows "start_subsumed (insert a passed) wait'"
    using assms unfolding start_subsumed_def
    by (metis Un_iff insert_DiffM insert_iff set_mset_add_mset_insert)

  lemma aux4:
    assumes "worklist_inv_frontier passed {#}" "reachable x" "start_subsumed passed {#}"
            "passed \<subseteq> Collect reachable"
    shows "\<exists> x' \<in> passed. x \<preceq> x'"
  proof -
    from \<open>reachable x\<close> have "E\<^sup>*\<^sup>* a\<^sub>0 x" by (simp add: reachable_def)
    from assms(3) obtain b where "a\<^sub>0 \<preceq> b" "b \<in> passed" unfolding start_subsumed_def by auto
    have "\<exists>x'. \<exists> x''. E\<^sup>*\<^sup>* b x' \<and> x \<preceq> x' \<and> x' \<preceq> x'' \<and> x'' \<in> passed" if
                      "E\<^sup>*\<^sup>* a x" "a \<preceq> b"    "b \<preceq> b'"  "b' \<in> passed"
                      "reachable a" "reachable b" for a b b'
    using that proof (induction arbitrary: b b' rule: converse_rtranclp_induct)
      case base
      then show ?case by auto
    next
      case (step a a1 b b')
      from \<open>E a a1\<close> \<open>a \<preceq> b\<close> \<open>reachable a\<close> \<open>reachable b\<close> obtain b1 where
        "E b b1" "a1 \<preceq> b1"
      using mono by blast
      then obtain b1' where "E b' b1'" "b1 \<preceq> b1'" using assms(4) mono step.prems by blast
      with \<open>b' \<in> passed\<close> assms(1) obtain b1'' where "b1'' \<in> passed" "b1' \<preceq> b1''"
      unfolding worklist_inv_frontier_def by auto
      with \<open>b1 \<preceq> _\<close> have "b1 \<preceq> b1''" using trans by blast
      with step.IH[OF \<open>a1 \<preceq> b1\<close> this \<open>b1'' \<in> passed\<close>] \<open>reachable a\<close> \<open>E a a1\<close> \<open>reachable b\<close> \<open>E b b1\<close>
      obtain x' x'' where
        "E\<^sup>*\<^sup>* b1 x'" "x \<preceq> x'" "x' \<preceq> x''" "x'' \<in> passed"
      by (auto intro: step_reachable)
      moreover from \<open>E b b1\<close> \<open>E\<^sup>*\<^sup>* b1 x'\<close> have "E\<^sup>*\<^sup>* b x'" by auto
      ultimately show ?case by auto
    qed
    from this[OF \<open>E\<^sup>*\<^sup>* a\<^sub>0 x\<close> \<open>a\<^sub>0 \<preceq> b\<close> refl \<open>b \<in> _\<close>] assms(4) \<open>b \<in> passed\<close> show ?thesis
    by (auto intro: trans)
  qed

  theorem worklist_algo_correct:
    "worklist_algo \<le> SPEC (\<lambda> brk. brk \<longleftrightarrow> F_reachable)"
  proof - 
    note [simp] = size_Diff_submset pred_not_lt_is_zero
    note [dest] = set_mset_mp
    show ?thesis
    unfolding worklist_algo_def add_succ_spec_def F_reachable_def
      apply (refine_vcg wf_worklist_var)
      (* F a\<^sub>0*)
      apply (auto; fail) []
      (* Invar start*)
      apply (auto simp: worklist_inv_def worklist_inv_frontier_def start_subsumed_def; fail)
      (* Precondition for take-from-set *)
      apply (simp; fail)
      (* State is subsumed by passed*)
        (* Assertion *)
        apply (auto simp: worklist_inv_def; fail)
        (*Invariant*)
        apply (auto simp: worklist_inv_def aux2 aux5 
              dest: in_diffD
              split: if_split_asm; fail) []
        (*Variant*)
        apply (auto simp: worklist_inv_def worklist_var_def intro: finite_subset[OF _ finite_reachable]; fail)

      (* Insert successors to wait *)  
        (*Invariant*)
        apply (clarsimp split: if_split_asm) (* Split on F in successors *)
          (* Found final state *)
          apply (clarsimp simp: worklist_inv_def; blast intro: step_reachable; fail)
          (* No final state *)
      apply (auto 
        simp: worklist_inv_def step_reachable aux3 aux6 finitely_branching
        dest: in_diffD; fail)[]
        (*Variant*)
        apply (auto simp: worklist_inv_def aux1; fail)
      (* I \<and> \<not>b \<Longrightarrow> post *)  
      using F_mono apply (fastforce simp: worklist_inv_def dest!: aux4)
      done
  qed  

  lemmas [refine_vcg] = worklist_algo_correct[THEN order_trans]

  end \<comment> \<open>Context\<close>

end \<comment> \<open>Search Space\<close>


subsection \<open>Towards an Implementation\<close>
locale Worklist1_Defs = Search_Space_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"

locale Worklist1 = Worklist1_Defs + Search_Space +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = Collect (E a)"
begin

  definition "add_succ1 wait a \<equiv> nfoldli (succs a) (\<lambda>(_,brk). \<not>brk) (\<lambda>a (wait,brk). if F a then RETURN (wait,True) else RETURN (wait + {#a#},False)) (wait, False)"

  lemma add_succ1_ref[refine]: "\<lbrakk>(wait,wait')\<in>Id; (a,a')\<in>b_rel Id reachable\<rbrakk> \<Longrightarrow> add_succ1 wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ_spec wait' a')"
    apply simp
    unfolding add_succ_spec_def add_succ1_def
    apply (refine_vcg nfoldli_rule[where I = "\<lambda>l1 _ (wait',brk). if brk then \<exists>a'. E a a' \<and> F a' else set_mset wait' = set_mset wait \<union> set l1 \<and> set l1 \<inter> Collect F = {}"])
    apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    done

  definition worklist_algo1 where
    "worklist_algo1 = do
      { 
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = {#a\<^sub>0#};
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              { 
                (a, wait) \<leftarrow> take_from_mset wait;
                if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ1 wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

  lemma worklist_algo1_ref[refine]: "worklist_algo1 \<le> \<Down>Id worklist_algo"  
    unfolding worklist_algo1_def worklist_algo_def
    apply (refine_rcg)
    apply refine_dref_type
    unfolding worklist_inv_def
    apply auto
    done

end


end \<comment> \<open>Theory\<close>
