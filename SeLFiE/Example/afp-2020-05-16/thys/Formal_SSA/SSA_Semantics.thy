(*  Title:      SSA_Semantics.thy
    Author:     Sebastian Ullrich
*)

section \<open>Proof of Semantic Equivalence\<close>

theory SSA_Semantics imports Construct_SSA begin

type_synonym ('node, 'var) state = "'var \<rightharpoonup> 'node"

context CFG_SSA_Transformed
begin
  declare invar[intro!]

  definition step ::
    "'g \<Rightarrow> 'node \<Rightarrow> ('node, 'var) state \<Rightarrow> ('node, 'var) state"
  where
    "step g m s v \<equiv> if v \<in> oldDefs g m then Some m else s v"

  inductive bs :: "'g \<Rightarrow> 'node list \<Rightarrow> ('node, 'var) state \<Rightarrow> bool" ("_ \<turnstile> _\<Down>_" [50, 50, 50] 50)
  where
    "g \<turnstile> Entry g-ns\<rightarrow>last ns \<Longrightarrow> g \<turnstile> ns\<Down>(fold (step g) ns Map.empty)"


  definition ssaStep ::
    "'g \<Rightarrow> 'node \<Rightarrow> nat \<Rightarrow> ('node, 'val) state \<Rightarrow> ('node, 'val) state"
  where
    "ssaStep g m i s v \<equiv>
      if v \<in> defs g m then
        Some m
      else
        case phis g (m,v) of
          Some phiParams \<Rightarrow> s (phiParams ! i)
        | None \<Rightarrow> s v"

  inductive ssaBS :: "'g \<Rightarrow> 'node list \<Rightarrow> ('node, 'val) state \<Rightarrow> bool" ("_ \<turnstile> _\<Down>\<^sub>s _" [50, 50, 50] 50)
  for
    g :: 'g
  where
    empty: "g \<turnstile> [Entry g]\<Down>\<^sub>s(ssaStep g (Entry g) 0 Map.empty)"
  | snoc: "\<lbrakk>g \<turnstile> ns\<Down>\<^sub>ss; last ns = old.predecessors g m ! i; m \<in> set (\<alpha>n g); i < length (old.predecessors g m)\<rbrakk> \<Longrightarrow>
            g \<turnstile> (ns@[m])\<Down>\<^sub>s(ssaStep g m i s)"

  lemma ssaBS_I:
    assumes "g \<turnstile> Entry g-ns\<rightarrow>n"
    obtains s where "g \<turnstile> ns\<Down>\<^sub>ss"
  using assms
  proof (atomize_elim, induction rule:old.path2_rev_induct)
    case (snoc ns m' m)
    then obtain s where s: "g \<turnstile> ns\<Down>\<^sub>ss" by auto
    from snoc.hyps(2) obtain i where "m' = old.predecessors g m ! i" "i < length (old.predecessors g m)" by (auto simp:in_set_conv_nth)
    with snoc.hyps snoc.prems s show ?case by -(rule exI, erule ssaBS.snoc, auto dest:old.path2_last)
  qed (auto intro: ssaBS.empty)

  lemma ssaBS_nonempty[simp]: "\<not> (g \<turnstile> []\<Down>\<^sub>ss)"
  by (rule notI, cases rule: ssaBS.cases, auto)

  lemma ssaBS_hd[simp]: "g \<turnstile> ns\<Down>\<^sub>ss \<Longrightarrow> hd ns = Entry g"
  by (induction rule: ssaBS.induct, auto simp: hd_append)


  lemma equiv_aux:
    assumes "g \<turnstile> ns\<Down>s" "g \<turnstile> ns\<Down>\<^sub>ss'" "g \<turnstile> last ns-ms\<rightarrow>m" "v \<in> allUses g m" "\<forall>n \<in> set (tl ms). var g v \<notin> var g ` allDefs g n"
    shows "s (var g v) = s' v"
  using assms(2) assms(1,3-) proof (induction arbitrary: v s ms m)
    case empty
    have "v \<in> defs g (Entry g)"
    proof-
      from empty.prems(2,3) have "defAss g m v" by - (rule allUses_def_ass, auto)
      with empty.prems(2) obtain n where n: "n \<in> set ms" "v \<in> allDefs g n" by - (drule defAssD, auto)
      with empty.prems(4) have "n \<notin> set (tl ms)" by auto
      with empty.prems(2) n have "n = Entry g" by (cases ms, auto dest: old.path2_hd)
      with n(2) show ?thesis by (auto simp: allDefs_def)
    qed
    with empty.prems(1) show ?case
      by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def split: option.split)
  next
    case (snoc ns s' n i)
    from snoc.prems(2) have[simp]: "n \<in> set (\<alpha>n g)" "m \<in> set (\<alpha>n g)" by auto
    from snoc.prems(2,3) have[simp]: "v \<in> allVars g" by - (rule allUses_in_allVars, auto)
    from snoc.hyps(4) have[simp]: "n \<noteq> Entry g" by (auto simp: Entry_no_predecessor)

    show ?case
    proof (cases "var g v \<in> var g ` allDefs g n")
      case True

      have[simp]: "defNode g v = n" (is "?n\<^sub>v = _")
      proof-
        from True obtain v' where v': "v' \<in> allDefs g n" "var g v' = var g v" by auto
        from snoc.prems(3) have "defAss g m v" by - (rule allUses_def_ass, auto)
        moreover from snoc.prems(1) obtain ns' where ns': "g \<turnstile> Entry g-ns'\<rightarrow>n" "set ns' \<subseteq> set (ns@[n])" "distinct ns'"
          by (auto elim!: bs.cases intro: old.simple_path2)
        ultimately have "?n\<^sub>v \<in> set (ns'@tl ms)"
          using snoc.prems(2) by - (drule defAss_defNode, auto elim!: bs.cases dest: old.path2_app)
        moreover {
          let ?n'' = "last (butlast ns')"
          assume asm: "?n\<^sub>v \<in> set (butlast ns')"
          with ns'(1,3) have[simp]: "?n\<^sub>v \<noteq> n" by (cases ns' rule: rev_cases, auto dest!: old.path2_last)
          from ns'(1) have "length ns' \<ge> 2" by auto
          with ns' have bns': "g \<turnstile> Entry g-butlast ns'\<rightarrow>?n''" "?n'' \<in> set (old.predecessors g n)"
            by (auto elim: old.path2_unsnoc)
          with asm obtain ns'' where ns'': "g \<turnstile> ?n\<^sub>v-ns''\<rightarrow>?n''" "suffix ns'' (butlast ns')" "?n\<^sub>v \<notin> set (tl ns'')"
            by - (rule old.path2_split_first_last, auto)
          with bns' snoc.prems(2) have "g \<turnstile> ?n\<^sub>v-(ns''@[n])@tl ms\<rightarrow>m" by - (rule old.path2_app, auto)
          hence "defNode g v' \<notin> set (tl (ns''@[n]@tl ms))"
            using v' snoc.prems(3,4) bns'(2) ns''(1,3)
            by - (rule conventional''[of g v _ m], auto intro!: old.path2_app simp: old.path2_not_Nil)
          with ns' ns''(1) v'(1) have False by (auto simp: old.path2_not_Nil)
        } 
        ultimately show ?thesis using snoc.prems(4) ns'(1) by (cases ns' rule: rev_cases, auto dest: old.path2_last)
      qed
      from \<open>v \<in> allVars g\<close> show ?thesis
      proof (cases rule: defNode_cases)
        case simpleDef
        thus ?thesis using snoc.prems(1) by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def)
      next
        case phi
        {
          fix v'
          assume asm: "v' \<in> defs g n" "var g v = var g v'"
          with phi have "v' = v" using allDefs_var_disjoint[of n g v' v]
            by (cases, auto dest!: phi_phiDefs)
          with asm(1) phi have False using simpleDefs_phiDefs_disjoint[of n g]
            by (auto dest!: phi_phiDefs)
        }
        note 1 = this
        {
          fix vs
          assume asm: "g \<turnstile> Entry g-ns @ [n]\<rightarrow>n" "phis g (n, v) = Some vs" "var g v \<notin> var g ` defs g n"
          let ?n' = "last ns"
          from asm(1) have "length ns \<ge> 1" by (cases ns, auto simp: old.path2_def)
          hence "g \<turnstile> Entry g-ns\<rightarrow>?n'"
            by - (rule old.path2_unsnoc[OF asm(1)], auto)
          moreover have "vs ! i \<in> phiUses g ?n'" using snoc.hyps(2,4) phis_wf[OF asm(2)]
            by - (rule phiUsesI[OF _ asm(2)], auto simp: set_zip)
          ultimately have "fold (step g) ns Map.empty (var g (vs ! i)) = s' (vs ! i)"
          by - (rule snoc.IH[where ms1="[?n']" and m1="?n'"], auto intro!: bs.intros)
          hence "fold (step g) ns Map.empty (var g v) = s' (vs ! i)" using phis_same_var[OF asm(2), of "vs ! i"] snoc.hyps(4) phis_wf[OF asm(2)]
            by auto
        }
        thus ?thesis using phi snoc.prems(1)
          by - (erule bs.cases, auto dest!: 1 simp: step_def ssaStep_def oldDefs_def phi_def)
      qed
    next
      case False
      hence "phis g (n, v) = None" by (auto simp: allDefs_def phiDefs_def)
      moreover have "fold (step g) ns Map.empty (var g v) = s' v"
      proof-
        from snoc.hyps(1) have "length ns \<ge> 1" by (cases ns, auto)
        moreover from snoc.prems(2,4) False have "\<forall>n \<in> set ms. var g v \<notin> var g ` allDefs g n"
          by (cases ms, auto simp: phiDefs_def dest: old.path2_hd)
        ultimately show ?thesis
          using snoc.prems(1,2,3) by - (rule snoc.IH[where ms1="last ns#ms"], auto elim!: bs.cases intro!: bs.intros elim: old.path2_unsnoc intro!: old.Cons_path2)
      qed
      ultimately show ?thesis
        using snoc.prems(1) False by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def)
    qed
  qed

  theorem equiv:
    assumes "g \<turnstile> ns\<Down>s" "g \<turnstile> ns\<Down>\<^sub>ss'" "v \<in> uses g (last ns)"
    shows "s (var g v) = s' v"
  using assms by - (rule equiv_aux[where ms="[last ns]"], auto elim!: bs.cases)
end

end
