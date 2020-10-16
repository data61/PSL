theory DFS_Framework_Refine_Aux
imports DFS_Framework_Misc Refine_Monadic.Refine_Monadic
begin


definition GHOST :: "'a \<Rightarrow> 'a" 
  \<comment> \<open>Ghost tag to mark ghost variables in let-expressions\<close>
  where [simp]: "GHOST \<equiv> \<lambda>x. x"
lemma GHOST_elim_Let: \<comment> \<open>Unfold rule to inline GHOST-Lets\<close>
  shows "(let x=GHOST m in f x) = f m" by simp


lemma "WHILEI I b f s \<le> 
  do {ASSERT (I s); WHILE b (\<lambda>s. do {s \<leftarrow> f s; ASSERT (I s); RETURN s}) s}"
  unfolding WHILEI_def WHILE_def WHILEI_body_def
  apply (rule refine_IdD)
  apply refine_rcg
  apply (rule introR[where R="br id I"])
  apply (simp_all add: br_def)
  apply (rule intro_prgR[where R="br id I"])
  apply (simp_all add: br_def)
  apply (auto simp: pw_le_iff refine_pw_simps)  
  done

(* TODO: Move to RefineG_While *)
lemma WHILET_eq_WHILE:
  assumes "WHILET b f s0 \<noteq> top"
  shows "WHILET b f s0 = WHILE b f s0"
  using assms
  unfolding WHILET_def WHILE_def WHILEIT_def WHILEI_def
  by (rule RECT_eq_REC)

lemma WHILEIT_eq_WHILEI:
  assumes "WHILEIT I b f s0 \<noteq> top"
  shows "WHILEIT I b f s0 = WHILEI I b f s0"
  using assms
  unfolding WHILEIT_def WHILEI_def
  by (rule RECT_eq_REC)

(* TODO: Move to refinement framework! *)
lemma WHILEIT_le_WHILEI:
  assumes "wf V"
  assumes VAR: "\<And>s. \<lbrakk> I s; b s; f s \<le> SPEC I \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. (s',s)\<in>V)"
  shows "WHILEIT I b f s \<le> WHILEI I b f s"
  using \<open>wf V\<close>
  apply (induction s rule: wf_induct[consumes 1])
  apply (subst WHILEIT_unfold) 
  apply (subst WHILEI_unfold)
proof (clarsimp)
  fix x
  assume A: "I x" "b x"
  assume IH: "\<forall>y. (y, x) \<in> V \<longrightarrow> WHILE\<^sub>T\<^bsup>I\<^esup> b f y \<le> WHILE\<^bsup>I\<^esup> b f y"

  show "f x \<bind> WHILE\<^sub>T\<^bsup>I\<^esup> b f \<le> f x \<bind> WHILE\<^bsup>I\<^esup> b f"
  proof cases
    assume B: "f x \<le> SPEC I"
    show "?thesis"
      apply (rule Refine_Basic.bind_mono(1)[OF order_refl])
      using IH VAR[OF A B]
      by (auto simp: pw_le_iff)
  next
    assume B: "\<not>(f x \<le> SPEC I)"
    hence "f x \<bind> WHILE\<^bsup>I\<^esup> b f = FAIL"
      apply (subst WHILEI_unfold[abs_def])
      apply (auto simp: pw_eq_iff pw_le_iff refine_pw_simps)
      done
    thus ?thesis by simp  
  qed
qed

lemmas WHILEIT_refine_WHILEI = order_trans[OF WHILEIT_le_WHILEI WHILEI_refine]


lemma WHILET_eq_WHILE_tproof:
  assumes "wf V"
  assumes "I s0"
  assumes "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and> (s',s)\<in>V)"
  shows "WHILET b f s0 = WHILE b f s0"
proof -
  have "WHILET b f s0 \<le> SPEC I"
    by (rule WHILET_rule[where I=I], fact+)
  hence "WHILET b f s0 \<noteq> top" by auto 

  thus ?thesis
    unfolding WHILE_def WHILEI_def WHILET_def WHILEIT_def
    by (subst RECT_eq_REC) auto
qed  


lemma WHILEIT_eq_WHILEI_tproof:
  assumes "wf V"
  assumes "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. (s',s)\<in>V)"
  shows "WHILEIT I b f s0 = WHILEI I b f s0"
  apply (rule antisym)
    subgoal by (rule WHILEIT_le_WHILEI[OF assms])
    subgoal by (rule WHILEI_le_WHILEIT)
  done  



end

