section \<open>While-Loops\<close>
theory Refine_While
imports 
  Refine_Basic Refine_Leof "Generic/RefineG_While"
begin

definition WHILEIT ("WHILE\<^sub>T\<^bsup>_\<^esup>") where 
  "WHILEIT \<equiv> iWHILEIT bind RETURN"
definition WHILEI ("WHILE\<^bsup>_\<^esup>") where "WHILEI \<equiv> iWHILEI bind RETURN"
definition WHILET ("WHILE\<^sub>T") where "WHILET \<equiv> iWHILET bind RETURN"
definition WHILE where "WHILE \<equiv> iWHILE bind RETURN"

interpretation while?: generic_WHILE_rules bind RETURN SPEC
  WHILEIT WHILEI WHILET WHILE
  apply unfold_locales
  apply (simp_all add: WHILEIT_def WHILEI_def WHILET_def WHILE_def)
  apply refine_mono
  apply refine_mono

  apply (subst RES_Sup_RETURN[symmetric]) 
  apply (rule_tac f=Sup in arg_cong) apply auto []
  apply (erule bind_rule)
  done

lemmas [refine_vcg] = WHILEI_rule
lemmas [refine_vcg] = WHILEIT_rule

subsection \<open>Data Refinement Rules\<close>

lemma ref_WHILEI_invarI:
  assumes "I s \<Longrightarrow> M \<le> \<Down>R (WHILEI I b f s)"
  shows "M \<le> \<Down>R (WHILEI I b f s)"
  apply (subst WHILEI_unfold)
  apply (cases "I s")
  apply (subst WHILEI_unfold[symmetric])
  apply (erule assms)
  apply simp
  done

lemma ref_WHILEIT_invarI:
  assumes "I s \<Longrightarrow> M \<le> \<Down>R (WHILEIT I b f s)"
  shows "M \<le> \<Down>R (WHILEIT I b f s)"
  apply (subst WHILEIT_unfold)
  apply (cases "I s")
  apply (subst WHILEIT_unfold[symmetric])
  apply (erule assms)
  apply simp
  done


lemma WHILEI_le_rule:
  assumes R0: "(s,s')\<in>R"
  assumes RS: "\<And>W s s'. \<lbrakk>\<And>s s'. (s,s')\<in>R \<Longrightarrow> W s \<le> M s'; (s,s')\<in>R\<rbrakk> \<Longrightarrow> 
    do {ASSERT (I s); if b s then bind (f s) W else RETURN s} \<le> M s'"
  shows "WHILEI I b f s \<le> M s'"
  unfolding WHILEI_def
  apply (rule REC_le_rule[where M=M])
  apply (simp add: WHILEI_body_def, refine_mono)
  apply (rule R0)
  apply (erule (1) order_trans[rotated,OF RS])
  unfolding WHILEI_body_def
  apply auto
  done


text \<open>WHILE-refinement rule with invisible concrete steps.
  Intuitively, a concrete step may either refine an abstract step, or
  must not change the corresponding abstract state.\<close>
lemma WHILEI_invisible_refine_genR:
  assumes R0: "I' s' \<Longrightarrow> (s,s')\<in>R'"
  assumes RI: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s' \<rbrakk> \<Longrightarrow> I s"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s'; I s; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; I' s'; I s; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R' (do {ASSUME (b' s'); f' s'})) (\<Down>R' (RETURN s'))"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEI I b f s \<le> \<Down>R (WHILEI I' b' f' s')"
  apply (rule ref_WHILEI_invarI)
  apply (rule WHILEI_le_rule[where R=R'])
  apply (erule R0)
  apply (rule ref_WHILEI_invarI)
  apply (frule (1) RI)
  apply (case_tac "b s=False")
  apply (subst WHILEI_unfold)
  apply (auto dest: RB intro: RETURN_refine R_REF) []

  apply simp
  apply (rule order_trans[OF monoD[OF bind_mono1 RS]], assumption+)
  apply (simp only: bind_distrib_sup1)
  apply (rule sup_least)
    apply (subst WHILEI_unfold)
    apply (simp add: RB, intro impI)
    apply (rule bind_refine)
    apply (rule order_refl)
    apply simp

    apply (simp add: pw_le_iff refine_pw_simps, blast)
  done


lemma WHILEI_refine_genR:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')" 
  apply (rule WHILEI_invisible_refine_genR[OF R0])
  apply assumption
  apply (erule (1) IREF)
  apply (simp add: COND_REF)
  apply (rule le_supI1)
  apply (simp add: COND_REF STEP_REF)
  apply (rule R_REF, assumption+)
  done

lemma WHILE_invisible_refine_genR:
  assumes R0: "(s,s')\<in>R'"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R'; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R' (do {ASSUME (b' s'); f' s'})) (\<Down>R' (RETURN s'))"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f s \<le> \<Down>R (WHILE b' f' s')"
  unfolding WHILE_def
  apply (rule WHILEI_invisible_refine_genR)
  apply (rule assms, (assumption+)?)+
  done

lemma WHILE_refine_genR:
  assumes R0: "(x,x')\<in>R'"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f x \<le>\<Down>R (WHILE b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine_genR)
  apply (rule assms, (assumption+)?)+
  done

lemma WHILE_refine_genR':
  assumes R0: "(x,x')\<in>R'"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILE b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine_genR)
  apply (rule assms TrueI, (assumption+)?)+
  done

text \<open>WHILE-refinement rule with invisible concrete steps.
  Intuitively, a concrete step may either refine an abstract step, or
  must not change the corresponding abstract state.\<close>
lemma WHILEI_invisible_refine:
  assumes R0: "I' s' \<Longrightarrow> (s,s')\<in>R"
  assumes RI: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s' \<rbrakk> \<Longrightarrow> I s"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R; I' s'; I s; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R (do {ASSUME (b' s'); f' s'})) (\<Down>R (RETURN s'))"
  shows "WHILEI I b f s \<le> \<Down>R (WHILEI I' b' f' s')"
  apply (rule WHILEI_invisible_refine_genR[where R'=R])
  apply (rule assms, (assumption+)?)+
  done

lemma WHILEI_refine[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')" 
  apply (rule WHILEI_invisible_refine[OF R0])
  apply assumption
  apply (erule (1) IREF)
  apply (simp add: COND_REF)
  apply (rule le_supI1)
  apply (simp add: COND_REF STEP_REF)
  done

lemma WHILE_invisible_refine:
  assumes R0: "(s,s')\<in>R"
  assumes RB: "\<And>s s'. \<lbrakk> (s,s')\<in>R; b' s' \<rbrakk> \<Longrightarrow> b s"
  assumes RS: "\<And>s s'. \<lbrakk> (s,s')\<in>R; b s \<rbrakk> 
    \<Longrightarrow> f s \<le> sup (\<Down>R (do {ASSUME (b' s'); f' s'})) (\<Down>R (RETURN s'))"
  shows "WHILE b f s \<le> \<Down>R (WHILE b' f' s')"
  unfolding WHILE_def
  apply (rule WHILEI_invisible_refine)
  using assms by auto

lemma WHILE_le_rule:
  assumes R0: "(s,s')\<in>R"
  assumes RS: "\<And>W s s'. \<lbrakk>\<And>s s'. (s,s')\<in>R \<Longrightarrow> W s \<le> M s'; (s,s')\<in>R\<rbrakk> \<Longrightarrow> 
    do {if b s then bind (f s) W else RETURN s} \<le> M s'"
  shows "WHILE b f s \<le> M s'"
  unfolding WHILE_def
  apply (rule WHILEI_le_rule[OF R0])
  apply (simp add: RS)
  done

lemma WHILE_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILE b f x \<le>\<Down>R (WHILE b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine)
  using assms by auto

lemma WHILE_refine'[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILE b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  unfolding WHILE_def
  apply (rule WHILEI_refine)
  using assms by auto

lemma AIF_leI: "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> S\<le>S'\<rbrakk> \<Longrightarrow> (if \<Phi> then S else FAIL) \<le> S'"
  by auto
lemma ref_AIFI: "\<lbrakk>\<Phi> \<Longrightarrow> S\<le>\<Down>R S'\<rbrakk> \<Longrightarrow> S \<le> \<Down>R (if \<Phi> then S' else FAIL)"
  by (cases \<Phi>) auto

text \<open>Refinement with generalized refinement relation. Required to exploit
  the fact that the condition does not hold at the end of the loop.\<close>
lemma WHILEIT_refine_genR:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')" 
  apply (rule ref_WHILEIT_invarI)
  unfolding WHILEIT_def
  apply (rule RECT_refine[OF WHILEI_body_trimono R0])
  apply assumption
  unfolding WHILEI_body_def
  apply (rule ref_AIFI)
  apply (rule AIF_leI)
  apply (blast intro: IREF)
  apply (rule if_refine)
  apply (simp add: COND_REF)
  apply (rule bind_refine)
  apply (rule STEP_REF, assumption+) []
  apply assumption

  apply (rule RETURN_refine)
  apply (simp add: R_REF)
  done


lemma WHILET_refine_genR:
  assumes R0: "(x,x')\<in>R'"
  assumes COND_REF: "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILET b f x \<le>\<Down>R (WHILET b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine_genR[OF R0])
  apply (rule TrueI)
  apply (rule assms, assumption+)+
  done

lemma WHILET_refine_genR':
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R'"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R' (f' x')"
  assumes R_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R'; \<not>b x; \<not>b' x'; I' x' \<rbrakk> \<Longrightarrow> (x,x')\<in>R"
  shows "WHILET b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine_genR[OF R0])
  apply assumption
  apply (rule TrueI)
  apply (rule assms, assumption+)+
  done

lemma WHILEIT_refine[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')" 
  using WHILEIT_refine_genR[where R=R and R'=R, OF assms] .

lemma WHILET_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILET b f x \<le>\<Down>R (WHILET b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine)
  using assms by auto

lemma WHILET_refine'[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILET b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  unfolding WHILET_def
  apply (rule WHILEIT_refine)
  using assms by auto


lemma WHILEI_refine_new_invar:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes INV0: "\<lbrakk> I' x'; (x,x')\<in>R \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  assumes STEP_INV: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x'; nofail (f x) \<rbrakk> \<Longrightarrow> f x \<le> SPEC I"
  shows "WHILEI I b f x \<le>\<Down>R (WHILEI I' b' f' x')"
  apply (rule WHILEI_refine_genR[where 
    I=I and I'=I' and x'=x' and x=x and R=R and b=b and b'=b' and f'=f' and f=f
    and R'="{ (c,a). (c,a)\<in>R \<and> I c }"
    ])
  using assms
  by (auto intro: add_invar_refineI)

lemma WHILEIT_refine_new_invar:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes INV0: "\<lbrakk> I' x'; (x,x')\<in>R \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  assumes STEP_INV: 
    "\<And>x x'. \<lbrakk> nofail (f x); (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> SPEC I"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  apply (rule WHILEIT_refine_genR[where 
    I=I and I'=I' and x'=x' and x=x and R=R and b=b and b'=b' and f'=f' and f=f
    and R'="{ (c,a). (c,a)\<in>R \<and> I c }"
    ])
  using assms
  by (auto intro: add_invar_refineI)


subsection \<open>Autoref Setup\<close>

(*lemma id_WHILE[autoref_id_self]: "ID_LIST 
  (l (WHILET,3) (WHILEIT I,3) (WHILE,3) (WHILEI I,3))"
  by simp_all*)

context begin interpretation autoref_syn .

lemma [autoref_op_pat_def]:
  "WHILEIT I \<equiv> OP (WHILEIT I)"
  "WHILEI I \<equiv> OP (WHILEI I)"
  by auto

lemma autoref_WHILET[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "(s,s')\<in>R"
  shows "(WHILET c f s,
    (OP WHILET:::(R\<rightarrow>Id)\<rightarrow>(R\<rightarrow>\<langle>R\<rangle>nres_rel)\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel)$c'$f'$s')
   \<in> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILET_refine)

lemma autoref_WHILEIT[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk>REMOVE_INTERNAL c' x'; I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow>(f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "I s' \<Longrightarrow> (s,s')\<in>R"
  shows "(WHILET c f s,
      (OP (WHILEIT I) ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'$s'
    )\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILET_refine')

lemma autoref_WHILEIT'[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x'\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R; I x'\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  shows "(WHILET c f,
      (OP (WHILEIT I) ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'
    )\<in>R \<rightarrow> \<langle>R\<rangle>nres_rel"
    unfolding autoref_tag_defs
    by (parametricity 
      add: autoref_WHILEIT[unfolded autoref_tag_defs]
      assms[unfolded autoref_tag_defs])

lemma autoref_WHILE[autoref_rules]: (** TODO: obsolete ? **)
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "(s,s')\<in>R"
  shows "(WHILE c f s,
      (OP WHILE ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'$s'
    )\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILE_refine)

lemma autoref_WHILE'[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  shows "(WHILE c f,
      (OP WHILE ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'
    )\<in>R \<rightarrow> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILE_refine)


lemma autoref_WHILEI[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk>I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk>REMOVE_INTERNAL c' x'; I x'; (x,x')\<in>R\<rbrakk> \<Longrightarrow>(f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  assumes "I s' \<Longrightarrow> (s,s')\<in>R"
  shows "(WHILE c f s,
      (OP (WHILEI I) ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'$s'
    )\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp add: nres_rel_def fun_rel_def intro!: WHILE_refine')

lemma autoref_WHILEI'[autoref_rules]:
  assumes "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x'\<rbrakk> \<Longrightarrow> (c x,c'$x') \<in> Id"
  assumes "\<And>x x'. \<lbrakk> REMOVE_INTERNAL c' x'; (x,x')\<in>R; I x'\<rbrakk> 
    \<Longrightarrow> (f x,f'$x') \<in> \<langle>R\<rangle>nres_rel"
  shows "(WHILE c f,
      (OP (WHILEI I) ::: (R\<rightarrow>Id) \<rightarrow> (R\<rightarrow>\<langle>R\<rangle>nres_rel) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>nres_rel)$c'$f'
    )\<in>R \<rightarrow> \<langle>R\<rangle>nres_rel"
    unfolding autoref_tag_defs
    by (parametricity 
      add: autoref_WHILEI[unfolded autoref_tag_defs]
      assms[unfolded autoref_tag_defs])



end

subsection \<open>Invariants\<close>
subsubsection \<open>Tail Recursion\<close>
context begin
  private lemma tailrec_transform_aux1:
    assumes "RETURN s \<le> m"
    shows "REC (\<lambda>D s. sup (a s \<bind> D) (b s)) s \<le> lfp (\<lambda>x. sup m (x\<bind>a)) \<bind> b"
    (is "REC ?F s \<le> lfp ?f \<bind> b")
  proof (rule REC_rule[where pre = "\<lambda>s. RETURN s \<le> lfp ?f"], refine_mono)
    show "RETURN s \<le> lfp (\<lambda>x. sup m (x \<bind> a))"
      apply (subst lfp_unfold, tagged_solver)
      using assms apply (simp add: le_supI1)
      done
  next
    fix f x
    assume IH: "\<And>x. RETURN x \<le> lfp ?f \<Longrightarrow>
                  f x \<le> lfp ?f \<bind> b"
    and PRE: "RETURN x \<le> lfp ?f"
  
    show " sup (a x \<bind> f) (b x) \<le> lfp ?f \<bind> b"
    proof (rule sup_least)  
      show "b x \<le> lfp ?f \<bind> b"
      using PRE
        by (simp add: pw_le_iff refine_pw_simps) blast
    next
      from PRE have "a x \<le> lfp ?f \<bind> a"
        by (simp add: pw_le_iff refine_pw_simps) blast
      also have "\<dots> \<le> lfp ?f"
        apply (subst (2) lfp_unfold, tagged_solver)
        apply (simp add: le_supI2)
        done
      finally show "a x \<bind> f \<le> lfp ?f \<bind> b"
        using IH
        by (simp add: pw_le_iff refine_pw_simps) blast
    qed
  qed  
  
  private corollary tailrec_transform1: 
    fixes m :: "'a nres"
    shows "m\<bind>REC (\<lambda>D s. sup (a s \<bind> D) (b s)) \<le> lfp (\<lambda>x. sup m (x\<bind>a)) \<bind> b"
    apply (cases "nofail m")
    apply (erule bind_le_nofailI)
    apply (erule tailrec_transform_aux1)
    apply (simp add: not_nofail_iff lfp_const)
    done
  
            
  private lemma tailrec_transform_aux2:
    fixes m :: "'a nres"
    shows "lfp (\<lambda>x. sup m (x\<bind>a)) 
      \<le> m \<bind> REC (\<lambda>D s. sup (a s \<bind> D) (RETURN s))"
    (is "lfp ?f \<le> m \<bind> REC ?F")
    apply (subst gen_kleene_lfp)
    apply (simp add: cont_def pw_eq_iff refine_pw_simps, blast)
    apply (rule SUP_least, simp)
  proof -
    fix i
    show "((\<lambda>x. x \<bind> a) ^^ i) m \<le> m \<bind> REC (\<lambda>D s. sup (a s \<bind> D) (RETURN s))"
      apply (induction i arbitrary: m)
      apply simp
      apply (subst REC_unfold, refine_mono)
      apply (simp add: pw_le_iff refine_pw_simps, blast)
      
      apply (subst funpow_Suc_right)
      apply simp
      apply (rule order_trans)
      apply rprems
      apply simp
  
      apply (subst (2) REC_unfold, refine_mono)
      apply (simp add: bind_distrib_sup2)
      done
  qed
  
  
  private lemma tailrec_transform_aux3: "REC (\<lambda>D s. sup (a s \<bind> D) (RETURN s)) s \<bind> b 
    \<le> REC (\<lambda>D s. sup (a s \<bind> D) (b s)) s"
    apply (subst bind_le_shift)
    apply (rule REC_rule, refine_mono)
    apply (rule TrueI)
    apply auto
      apply (subst (asm) (4) REC_unfold, refine_mono)
      apply (rule order_trans[OF bind_mono(1)[OF order_refl]])
      apply rprems
      apply (subst (3) REC_unfold, refine_mono)
      apply (simp add: refine_pw_simps pw_le_iff, blast)
  
      apply (subst REC_unfold, refine_mono, simp)
    done
  
  private lemma tailrec_transform2:
    "lfp (\<lambda>x. sup m (bind x a)) \<bind> b \<le> m \<bind> REC (\<lambda>D s. sup (a s \<bind> D) (b s))"
  proof -
    from bind_mono(1)[OF tailrec_transform_aux2 order_refl]
    have "lfp (\<lambda>x. sup m (bind x a)) \<bind> b 
      \<le> m \<bind> (\<lambda>x. REC (\<lambda>D s. sup (a s \<bind> D) (RETURN s)) x \<bind> b)"
      by simp
    also from bind_mono(1)[OF order_refl tailrec_transform_aux3]
    have "\<dots> \<le> m \<bind> REC (\<lambda>D s. sup (a s \<bind> D) (b s))" .
    finally show ?thesis .
  qed  
  
  definition "tailrec_body a b \<equiv> (\<lambda>D s. sup (bind (a s) D) (b s))"
  
  theorem tailrec_transform: 
    "m \<bind> REC (\<lambda>D s. sup (a s \<bind> D) (b s)) = lfp (\<lambda>x. sup m (bind x a)) \<bind> b"
    apply (rule antisym)
    apply (rule tailrec_transform1)  
    apply (rule tailrec_transform2)  
    done
  
  theorem tailrec_transform': 
    "m \<bind> REC (tailrec_body a b) = lfp (\<lambda>x. sup m (bind x a)) \<bind> b"
    unfolding tailrec_body_def
    by (rule tailrec_transform)
  
  lemma "WHILE c f = 
    REC (tailrec_body 
      (\<lambda>s. do {ASSUME (c s); f s}) 
      (\<lambda>s. do {ASSUME (\<not>c s); RETURN s})
    )"
    unfolding WHILE_def WHILEI_def WHILEI_body_def tailrec_body_def
    apply (fo_rule fun_cong arg_cong)+ apply (intro ext)
    apply auto
    done
  
  lemma WHILEI_tailrec_conv: "WHILEI I c f = 
    REC (tailrec_body 
      (\<lambda>s. do {ASSERT (I s); ASSUME (c s); f s}) 
      (\<lambda>s. do {ASSERT (I s); ASSUME (\<not>c s); RETURN s})
    )"
    unfolding WHILEI_def WHILEI_body_def tailrec_body_def
    apply (fo_rule fun_cong arg_cong)+ apply (intro ext)
    apply auto
    done
  
  lemma WHILEIT_tailrec_conv: "WHILEIT I c f = 
    RECT (tailrec_body 
      (\<lambda>s. do {ASSERT (I s); ASSUME (c s); f s}) 
      (\<lambda>s. do {ASSERT (I s); ASSUME (\<not>c s); RETURN s})
    )"
    unfolding WHILEIT_def WHILEI_body_def tailrec_body_def
    apply (fo_rule fun_cong arg_cong)+ apply (intro ext)
    apply auto
    done
  
  
  definition "WHILEI_lfp_body I m c f \<equiv> 
    (\<lambda>x. sup m (do {
       s \<leftarrow> x;
       _ \<leftarrow> ASSERT (I s);
       _ \<leftarrow> ASSUME (c s);
       f s
     }))"
    
  lemma WHILEI_lfp_conv: "m \<bind> WHILEI I c f = 
    do { 
      s \<leftarrow> lfp (WHILEI_lfp_body I m c f); 
      ASSERT (I s); 
      ASSUME (\<not>c s); 
      RETURN s 
    }"
    unfolding WHILEI_lfp_body_def
    apply (subst WHILEI_tailrec_conv)
    apply (subst tailrec_transform')
    ..

end

subsubsection \<open>Most Specific Invariant\<close>
  
definition msii \<comment> \<open>Most specific invariant for WHILE-loop\<close>
  where "msii I m c f \<equiv> lfp (WHILEI_lfp_body I m c f)"

lemma [simp, intro!]: "mono (WHILEI_lfp_body I m c f)"
  unfolding WHILEI_lfp_body_def by tagged_solver

definition "filter_ASSUME c m \<equiv> do {x\<leftarrow>m; ASSUME (c x); RETURN x}"
definition "filter_ASSERT c m \<equiv> do {x\<leftarrow>m; ASSERT (c x); RETURN x}"

lemma [refine_pw_simps]: "nofail (filter_ASSUME c m) \<longleftrightarrow> nofail m"
  unfolding filter_ASSUME_def
  by (simp add: refine_pw_simps)

lemma [refine_pw_simps]: "inres (filter_ASSUME c m) x 
  \<longleftrightarrow> (nofail m \<longrightarrow> inres m x \<and> c x)"
  unfolding filter_ASSUME_def
  by (simp add: refine_pw_simps)

lemma msii_is_invar:
  "m \<le> msii I m c f"
  "m \<le> msii I m c f \<Longrightarrow> bind (filter_ASSUME c (filter_ASSERT I m)) f \<le> msii I m c f"
  unfolding  msii_def
  apply -
  apply (subst lfp_unfold, simp)
  apply (simp add: WHILEI_lfp_body_def)

  unfolding filter_ASSUME_def filter_ASSERT_def
  apply (subst lfp_unfold, simp)
  apply (simp add: WHILEI_lfp_body_def)
  apply (simp only: refine_pw_simps pw_le_iff) apply blast
  done

lemma WHILE_msii_conv: "m \<bind> WHILEI I c f 
  = filter_ASSUME (Not o c) (filter_ASSERT I (msii I m c f))"
  unfolding WHILEI_lfp_conv filter_ASSERT_def filter_ASSUME_def msii_def
  by simp

lemma msii_induct: 
  assumes I0: "m0 \<le> P"
  assumes IS: "\<And>m. \<lbrakk>m \<le> msii I m0 c f; m \<le> P;
    filter_ASSUME c (filter_ASSERT I m) \<bind> f \<le> msii I m0 c f
      \<rbrakk> \<Longrightarrow> filter_ASSUME c (filter_ASSERT I m) \<bind> f \<le> P"
  shows "msii I m0 c f \<le> P"
  unfolding msii_def WHILEI_lfp_body_def
  apply (rule lfp_gen_induct, tagged_solver)
  unfolding msii_def[symmetric] WHILEI_lfp_body_def[symmetric]
  apply (rule I0)
  apply (drule IS, assumption)
  unfolding filter_ASSERT_def filter_ASSUME_def
  apply simp_all
  done

subsubsection \<open>Reachable without fail\<close>
text \<open>Reachable states in a while loop, ignoring failing states\<close>

  (* (R)eachable states (w)ith(o)ut (f)ail. All non-fail states reachable
    in a while-loop. *)
  inductive rwof :: "'a nres \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> bool"
    for m0 cond step 
    where
      init: "\<lbrakk> m0=RES X; x\<in>X \<rbrakk> \<Longrightarrow> rwof m0 cond step x"
    | step: "\<lbrakk> rwof m0 cond step x; cond x; step x = RES Y; y\<in>Y \<rbrakk> 
      \<Longrightarrow> rwof m0 cond step y"

  (* This lemma establishes consequences of rwof as invariants. *)
  lemma establish_rwof_invar:
    assumes I: "m0 \<le>\<^sub>n SPEC I"
    assumes S: "\<And>s. \<lbrakk> rwof m0 cond step s; I s; cond s \<rbrakk> 
      \<Longrightarrow> step s \<le>\<^sub>n SPEC I"
    assumes "rwof m0 cond step s"
    shows "I s"
    using assms(3)
    apply induct
    using I apply auto []
    using S apply fastforce []
    done

  (* Predicate to express an rwof-invariant *)
  definition "is_rwof_invar m0 cond step I \<equiv> 
      (m0 \<le>\<^sub>n SPEC I)
    \<and> (\<forall>s. rwof m0 cond step s \<and> I s \<and> cond s 
        \<longrightarrow> step s \<le>\<^sub>n SPEC I )"

  lemma is_rwof_invarI[intro?]:
    assumes I: "m0 \<le>\<^sub>n SPEC I"
    assumes S: "\<And>s. \<lbrakk> rwof m0 cond step s; I s; cond s \<rbrakk> 
      \<Longrightarrow> step s \<le>\<^sub>n SPEC I"
    shows "is_rwof_invar m0 cond step I"
    using assms unfolding is_rwof_invar_def by blast

  lemma rwof_cons: "\<lbrakk>is_rwof_invar m0 cond step I; rwof m0 cond step s\<rbrakk> \<Longrightarrow> I s"
    unfolding is_rwof_invar_def
    using establish_rwof_invar[of m0 I cond step s]
    by blast
    

  (* This lemma proves a specification for the while loop, based on rwof
    and a nofail-proof. *)
  lemma rwof_WHILE_rule:
    assumes I0: "m0 \<le> SPEC I"
    assumes S: "\<And>s. \<lbrakk> rwof m0 cond step s; I s; cond s \<rbrakk> \<Longrightarrow> step s \<le> SPEC I"
    shows "m0 \<bind> WHILE cond step \<le> SPEC (\<lambda>s. rwof m0 cond step s \<and> \<not>cond s \<and> I s)"
  proof -
    from I0 obtain M0 where [simp]: "m0 = RES M0" and "M0 \<subseteq> Collect I"
      by (cases m0) auto

    show ?thesis 
      apply simp
      apply refine_vcg
      apply (rule WHILE_rule[where I="\<lambda>s. I s \<and> rwof m0 cond step s"])
    proof -
      fix s assume "s\<in>M0" thus "I s \<and> rwof m0 cond step s"
        using I0 by (auto intro: rwof.init) []

    next
      fix s
      assume A: "I s \<and> rwof m0 cond step s" and C: "cond s"
      hence "step s \<le> SPEC I" by - (rule S, simp_all)
      also then obtain S' where "step s = RES S'" by (cases "step s") auto
      from rwof.step[OF conjunct2[OF A] C this] this 
      have "step s \<le> SPEC (rwof m0 cond step)" by auto
      finally (SPEC_rule_conjI) 
      show "step s \<le> SPEC (\<lambda>s. I s \<and> rwof m0 cond step s)" .
    qed auto
  qed

subsubsection \<open>Filtering out states that satisfy the loop condition\<close>
  (* A shortcut definition for filtering out all results that satisfy
    the loop condition. Intuitively, filtering out these results from the 
    best invariant gives the results of the while loop. *)
  definition filter_nb :: "('a \<Rightarrow> bool) \<Rightarrow> 'a nres \<Rightarrow> 'a nres" where 
    "filter_nb b I \<equiv> do {s\<leftarrow>I; ASSUME (\<not>b s); RETURN s}"
  
  lemma pw_filter_nb[refine_pw_simps]:
    "nofail (filter_nb b I) \<longleftrightarrow> nofail I"
    "inres (filter_nb b I) x \<longleftrightarrow> (nofail I \<longrightarrow> inres I x \<and> \<not>b x)"
    unfolding filter_nb_def
    by (simp_all add: refine_pw_simps)

  lemma filter_nb_mono: "m\<le>m' \<Longrightarrow> filter_nb cond m \<le> filter_nb cond m'"
    unfolding filter_nb_def
    by refine_mono

  lemma filter_nb_cont: 
    "filter_nb cond (Sup M) = Sup {filter_nb cond m | m. m \<in> M}"
    apply (rule antisym)
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (auto intro: not_nofail_inres simp: refine_pw_simps) []
    
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (auto intro: not_nofail_inres simp: refine_pw_simps) []
    done

  lemma filter_nb_FAIL[simp]: "filter_nb cond FAIL = FAIL"
    by (simp add: filter_nb_def)

  lemma filter_nb_RES[simp]: "filter_nb cond (RES X) = RES {x\<in>X. \<not>cond x}"
    by (simp add: pw_eq_iff refine_pw_simps)

subsubsection \<open>Bounded while-loop\<close>

  (* A while rule that establishes an inductive invariant,
    and then filters out the results satisfying the condition. *)
  lemma WHILE_rule_gen_le:
    assumes I0: "m0 \<le> I"
    assumes ISTEP: "\<And>s. \<lbrakk>RETURN s \<le> I; b s\<rbrakk> \<Longrightarrow> f s \<le> I"
    shows "m0 \<bind> WHILE b f \<le> filter_nb b I"
      apply (unfold WHILE_def WHILEI_def)
      apply (refine_rcg order_trans[OF I0] refine_vcg pw_bind_leI)
      using I0 apply (simp add: pw_le_iff refine_pw_simps)

      apply (rule REC_rule[OF WHILEI_body_trimono, where pre="\<lambda>s. RETURN s \<le> I"])
        using I0 apply (simp add: pw_le_iff refine_pw_simps)
      
        unfolding WHILEI_body_def
        apply (split if_split)+
        apply (intro impI conjI)
        apply (simp_all)
        using ISTEP
        apply (simp (no_asm_use) only: pw_le_iff refine_pw_simps) apply blast
        apply (simp only: pw_le_iff refine_pw_simps) apply metis 
    done


  primrec bounded_WHILE' 
    :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a nres \<Rightarrow> 'a nres" 
  where
    "bounded_WHILE' 0 cond step m = m"
  | "bounded_WHILE' (Suc n) cond step m = do {
      x \<leftarrow> m;
      if cond x then bounded_WHILE' n cond step (step x)
      else RETURN x
    }"

  primrec bounded_WHILE
    :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a nres \<Rightarrow> 'a nres" 
  where
    "bounded_WHILE 0 cond step m = m"
  | "bounded_WHILE (Suc n) cond step m = do {
      x \<leftarrow> bounded_WHILE n cond step m;
      if cond x then step x
      else RETURN x
    }"

  lemma bounded_WHILE_shift: "do {
             x \<leftarrow> m;
             if cond x then bounded_WHILE n cond step (step x) else RETURN x
           } = do {
             x \<leftarrow> bounded_WHILE n cond step m;
             if cond x then step x else RETURN x
           }"
  proof (induction n arbitrary: m)
    case 0 thus ?case by (simp cong: if_cong)
  next
    case (Suc n) 

    have aux1: "do {
      x \<leftarrow> m;
      if cond x then do {
                       x \<leftarrow> bounded_WHILE n cond step (step x);
                       if cond x then step x else RETURN x
                     }
      else RETURN x
    } = do {
      x \<leftarrow> do {
        x \<leftarrow> m; 
        if cond x then bounded_WHILE n cond step (step x) else RETURN x
      };
      if cond x then step x else RETURN x
    }"
    by (simp add: pw_eq_iff refine_pw_simps)

    show ?case
      apply (simp cong: if_cong)
      apply (subst aux1)
      apply (subst Suc.IH)
      apply (simp add: pw_eq_iff refine_pw_simps)
      done
  qed


  lemma bounded_WHILE'_eq: 
    "bounded_WHILE' n cond step m = bounded_WHILE n cond step m"
    apply (induct n arbitrary: m)
    apply (auto cong: if_cong simp: bounded_WHILE_shift)
    done

  lemma mWHILE_unfold: "m \<bind> WHILE cond step = do {
      x \<leftarrow> m;
      if cond x then step x \<bind> WHILE cond step
      else RETURN x
    }"
    by (subst WHILE_unfold[abs_def]) (rule refl)

  lemma WHILE_bounded_aux1: 
    "filter_nb cond (bounded_WHILE n cond step m) \<le> m \<bind> WHILE cond step"
    unfolding bounded_WHILE'_eq[symmetric]
    apply (induct n arbitrary: m)
    apply simp
    apply (subst mWHILE_unfold)
    apply (simp add: pw_le_iff refine_pw_simps, blast)
    
    apply simp
    apply (subst mWHILE_unfold)
    apply (auto simp add: pw_le_iff refine_pw_simps)
    done

  lemma WHILE_bounded_aux2:
    "m \<bind> WHILE cond step 
      \<le> filter_nb cond (Sup {bounded_WHILE n cond step m | n. True})"
    apply (rule WHILE_rule_gen_le)
    apply (metis (mono_tags, lifting) Sup_upper bounded_WHILE.simps(1) 
      mem_Collect_eq)
  proof - 
    fix s
    assume "RETURN s \<le> Sup {bounded_WHILE n cond step m |n. True}"
    then obtain n where "RETURN s \<le> bounded_WHILE n cond step m"
      by (fold inres_def) (auto simp: refine_pw_simps)
    moreover assume "cond s"
    ultimately have "step s \<le> bounded_WHILE (Suc n) cond step m"
      by (simp add: pw_le_iff refine_pw_simps, blast)
    thus "step s \<le> Sup {bounded_WHILE n cond step m |n. True}"
      by (metis (mono_tags, lifting) Sup_upper2 mem_Collect_eq)
  qed

   
  lemma WHILE_bounded: 
    "m \<bind> WHILE cond step 
    = filter_nb cond (Sup {bounded_WHILE n cond step m | n. True})"
    apply (rule antisym)
    apply (rule WHILE_bounded_aux2)

    apply (simp add: filter_nb_cont)
    apply (rule Sup_least)
    apply (auto simp: WHILE_bounded_aux1)
    done

  subsubsection \<open>Relation to rwof\<close>

  lemma rwof_in_bounded_WHILE:
    assumes "rwof m0 cond step s" 
    shows "\<exists>n. RETURN s \<le> (bounded_WHILE n cond step m0)"
    using assms
    apply induction
    apply (rule_tac x=0 in exI)
    apply simp

    apply clarsimp
    apply (rule_tac x="Suc n" in exI)
    apply (auto simp add: pw_le_iff refine_pw_simps) []
    done

  lemma bounded_WHILE_FAIL_rwof:
    assumes "bounded_WHILE n cond step m0 = FAIL"
    assumes M0: "m0 \<noteq> FAIL"
    shows "\<exists>n'<n. \<exists>x X. 
        bounded_WHILE n' cond step m0 = RES X 
      \<and> x\<in>X \<and> cond x \<and> step x = FAIL"
    using assms
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    assume "bounded_WHILE (Suc n) cond step m0 = FAIL"
    hence "bounded_WHILE n cond step m0 = FAIL 
      \<or> (\<exists>X x. bounded_WHILE n cond step m0 = RES X 
          \<and> x\<in>X \<and> cond x \<and> step x = FAIL)"
      (is "?C1 \<or> ?C2")
      apply (cases "bounded_WHILE n cond step m0")
      apply simp
      apply (simp add: pw_eq_iff refine_pw_simps split: if_split_asm)
      apply (auto intro: not_nofail_inres simp: refine_pw_simps)
      done
    moreover {
      assume ?C1
      from Suc.IH[OF this M0] obtain n' x X where "n' < n" and
        1: "bounded_WHILE n' cond step m0 = RES X \<and> x\<in>X \<and> cond x \<and> step x = FAIL"
        by blast
      hence 2: "n' < Suc n" by simp
      from 1 2 have ?case by blast
    } moreover {
      assume ?C2
      hence ?case by blast
    } ultimately show ?case by blast
  qed

  lemma bounded_WHILE_RES_rwof:
    assumes "bounded_WHILE n cond step m0 = RES X"
    assumes "x\<in>X"
    shows "rwof m0 cond step x"
    using assms
  proof (induction n arbitrary: x X)
    case 0 thus ?case by (simp add: rwof.init)
  next
    case (Suc n)

    from Suc.prems(1) obtain Xh where
      BWN: "bounded_WHILE n cond step m0 = RES Xh"
      and "\<forall>x\<in>Xh. cond x \<longrightarrow> nofail (step x)"
      and "X = {x'. \<exists>x\<in>Xh. cond x \<and> inres (step x) x'} \<union> {x. x\<in>Xh \<and> \<not>cond x} "
      apply (cases "bounded_WHILE n cond step m0")
      apply simp
      apply (rule that, assumption)
      apply (force simp: refine_pw_simps pw_eq_iff) []
      apply (auto simp add: refine_pw_simps pw_eq_iff split: if_split_asm)
      done
    with Suc.prems(2) obtain xh X' where 
        "xh\<in>Xh" and
      C: "cond xh \<longrightarrow> step xh = RES X' \<and> x\<in>X'" and NC:  "\<not>cond xh \<longrightarrow> x=xh"
      by (auto simp: nofail_RES_conv)
    
    show ?case  
      apply (cases "cond xh")
        apply (rule rwof.step[where Y=X'])
          apply (rule Suc.IH[OF BWN \<open>xh\<in>Xh\<close>])
          apply assumption
          apply (simp_all add: C) [2]
        
        apply (rule Suc.IH[OF BWN])
        apply (simp add: NC \<open>xh\<in>Xh\<close>)
      done
  qed
      

  lemma rwof_FAIL_imp_WHILE_FAIL:
    assumes RW: "rwof m0 cond step s" 
    and C: "cond s" 
    and S: "step s = FAIL"
    shows "m0 \<bind> WHILE cond step = FAIL"
  proof -
    from rwof_in_bounded_WHILE[OF RW] obtain n where 
      "RETURN s \<le> bounded_WHILE n cond step m0" ..
    with C have "step s \<le> bounded_WHILE (Suc n) cond step m0"
      by (auto simp add: pw_le_iff refine_pw_simps)
    with S have "bounded_WHILE (Suc n) cond step m0 = FAIL" by simp
    with WHILE_bounded_aux1[of cond "Suc n" step m0] show ?thesis
      by (simp del: bounded_WHILE.simps)
  qed

  lemma pw_bounded_WHILE_RES_rwof: "\<lbrakk> nofail (bounded_WHILE n cond step m0); 
    inres (bounded_WHILE n cond step m0) x \<rbrakk> \<Longrightarrow> rwof m0 cond step x"
    using bounded_WHILE_RES_rwof[of n cond step m0 _ x]
    by (auto simp add: pw_eq_iff)
    
  corollary WHILE_nofail_imp_rwof_nofail:
    assumes "nofail (m0 \<bind> WHILE cond step)"
    assumes RW: "rwof m0 cond step s" 
    assumes C: "cond s"
    shows "nofail (step s)"
    apply (rule ccontr) apply (simp add: nofail_def)
    using assms rwof_FAIL_imp_WHILE_FAIL[OF RW C]
    by auto

  (* TODO: Move *)
  lemma WHILE_le_WHILEI: "WHILE b f s \<le> WHILEI I b f s"
    unfolding WHILE_def
    by (rule WHILEI_weaken) simp

  corollary WHILEI_nofail_imp_rwof_nofail:
    assumes NF: "nofail (m0 \<bind> WHILEI I cond step)"
    assumes RW: "rwof m0 cond step s" 
    assumes C: "cond s"
    shows "nofail (step s)"
  proof -
    from NF have "nofail (m0 \<bind> WHILE cond step)"
      using WHILE_le_WHILEI 
      by (fastforce simp: pw_le_iff refine_pw_simps)
    from WHILE_nofail_imp_rwof_nofail[OF this RW C] show ?thesis .
  qed

  corollary WHILET_nofail_imp_rwof_nofail:
    assumes NF: "nofail (m0 \<bind> WHILET cond step)"
    assumes RW: "rwof m0 cond step s" 
    assumes C: "cond s"
    shows "nofail (step s)"
  proof -
    from NF have "nofail (m0 \<bind> WHILE cond step)"
      using WHILEI_le_WHILEIT unfolding WHILE_def WHILET_def 
      by (fastforce simp: pw_le_iff refine_pw_simps)
    from WHILE_nofail_imp_rwof_nofail[OF this RW C] show ?thesis .
  qed

  corollary WHILEIT_nofail_imp_rwof_nofail:
    assumes NF: "nofail (m0 \<bind> WHILEIT I cond step)"
    assumes RW: "rwof m0 cond step s" 
    assumes C: "cond s"
    shows "nofail (step s)"
  proof -
    from NF have "nofail (m0 \<bind> WHILE cond step)"
      using WHILE_le_WHILEI WHILEI_le_WHILEIT unfolding WHILE_def
      by (fastforce simp: pw_le_iff refine_pw_simps)
    from WHILE_nofail_imp_rwof_nofail[OF this RW C] show ?thesis .
  qed

  lemma pw_rwof_in_bounded_WHILE:
    "rwof m0 cond step x \<Longrightarrow> \<exists>n. inres (bounded_WHILE n cond step m0) x"
    using rwof_in_bounded_WHILE[of m0 cond step x]
    by (auto simp add: pw_le_iff intro: not_nofail_inres)

subsubsection \<open>WHILE-loops in the nofail-case\<close>
  lemma nofail_WHILE_eq_rwof: 
    assumes NF: "nofail (m0 \<bind> WHILE cond step)"
    shows "m0 \<bind> WHILE cond step = SPEC (\<lambda>s. rwof m0 cond step s \<and> \<not>cond s)"
  proof -
    from NF WHILE_bounded[of m0 cond step] have NF': 
      "nofail (Sup {filter_nb cond m |m. \<exists>n. m = bounded_WHILE n cond step m0})"
      by (auto simp: filter_nb_cont)

    (*from NF WHILE_bounded[of m0 cond step] obtain X 
      where FR:
        "Sup {filter_nb cond m |m. \<exists>n. m = bounded_WHILE n cond step m0} = RES X"
      by (auto simp: nofail_RES_conv filter_nb_cont)*)
    
    show ?thesis
      unfolding WHILE_bounded[of m0 cond step] filter_nb_cont
      apply simp
    proof (rule antisym)
      show "Sup {filter_nb cond m |m. \<exists>n. m = bounded_WHILE n cond step m0}
        \<le> SPEC (\<lambda>s. rwof m0 cond step s \<and> \<not> cond s)"
        using NF' pw_bounded_WHILE_RES_rwof[of _ cond step m0]
        by (fastforce simp: pw_le_iff refine_pw_simps)
    next
      show "SPEC (\<lambda>s. rwof m0 cond step s \<and> \<not> cond s)
        \<le> Sup {filter_nb cond m |m. \<exists>n. m = bounded_WHILE n cond step m0}"      
        using NF' pw_rwof_in_bounded_WHILE[of m0 cond step]
        by (fastforce simp: pw_le_iff refine_pw_simps)
    qed
  qed

  lemma WHILE_refine_rwof:
    assumes "nofail (m \<bind> WHILE c f) \<Longrightarrow> mi \<le> SPEC (\<lambda>s. rwof m c f s \<and> \<not>c s)"
    shows "mi \<le> m \<bind> WHILE c f"
    apply (cases "nofail (m \<bind> WHILE c f)")
    apply (subst nofail_WHILE_eq_rwof, simp, fact)
    apply (simp add: pw_le_iff)
    done


  lemma pw_rwof_init:
    assumes NF: "nofail (m0 \<bind> WHILE cond step)"
    shows "inres m0 s \<Longrightarrow> rwof m0 cond step s" and "nofail m0"
    apply -
    using NF apply (cases m0, simp)
    apply (rule rwof.init, assumption)
    apply auto []
    
    using NF apply (simp add: refine_pw_simps)
    done

  lemma rwof_init:
    assumes NF: "nofail (m0 \<bind> WHILE cond step)" 
    shows "m0 \<le> SPEC (rwof m0 cond step)"
    using pw_rwof_init[OF NF]
    by (simp add: pw_le_iff refine_pw_simps)
  
  lemma pw_rwof_step':
    assumes NF: "nofail (step s)"
    assumes R: "rwof m0 cond step s"
    assumes C: "cond s"
    shows "inres (step s) s' \<Longrightarrow> rwof m0 cond step s'"
    using NF
    apply (clarsimp simp: nofail_RES_conv)
    apply (rule rwof.step[OF R C])
    apply (assumption)
    by simp

  lemma rwof_step': 
    "\<lbrakk> nofail (step s); rwof m0 cond step s; cond s \<rbrakk>
    \<Longrightarrow> step s \<le> SPEC (rwof m0 cond step)"
    using pw_rwof_step'[of step s m0 cond]
    by (simp add: pw_le_iff refine_pw_simps)

  lemma pw_rwof_step:
    assumes NF: "nofail (m0 \<bind> WHILE cond step)"
    assumes R: "rwof m0 cond step s"
    assumes C: "cond s"
    shows "inres (step s) s' \<Longrightarrow> rwof m0 cond step s'"
      and "nofail (step s)"
    using WHILE_nofail_imp_rwof_nofail[OF NF R C] pw_rwof_step'[OF _ assms(2-)]
    by simp_all

  lemma rwof_step: 
    "\<lbrakk> nofail (m0 \<bind> WHILE cond step); rwof m0 cond step s; cond s \<rbrakk>
    \<Longrightarrow> step s \<le> SPEC (rwof m0 cond step)"
    using pw_rwof_step[of m0 cond step s]
    by (simp add: pw_le_iff refine_pw_simps)

  lemma (in -) rwof_leof_init: "m \<le>\<^sub>n SPEC (rwof m c f)"
    apply rule
    using rwof.init
    apply (fastforce simp: nofail_RES_conv)
    done

  lemma (in -) rwof_leof_step: "\<lbrakk>rwof m c f s; c s\<rbrakk> \<Longrightarrow> f s \<le>\<^sub>n SPEC (rwof m c f)"
    apply rule
    using rwof.step
    apply (fastforce simp: nofail_RES_conv)
    done


  lemma (in -) rwof_step_refine:
    assumes NF: "nofail (m0 \<bind> WHILE cond step)"  
    assumes A: "rwof m0 cond step' s"
    assumes FR: "\<And>s. \<lbrakk> rwof m0 cond step s; cond s \<rbrakk> \<Longrightarrow> step' s \<le>\<^sub>n step s"
    shows "rwof m0 cond step s"
    apply (rule establish_rwof_invar[OF _ _ A])
      apply (rule rwof_leof_init)

      apply (rule leof_trans_nofail[OF FR], assumption+)
        apply (rule WHILE_nofail_imp_rwof_nofail[OF NF], assumption+)

        apply (simp add: rwof_leof_step)
    done

subsubsection \<open>Adding Invariants\<close>
  lemma WHILE_eq_I_rwof: "m \<bind> WHILE c f = m \<bind> WHILEI (rwof m c f) c f"
  proof (rule antisym)
    have "m \<bind> WHILEI (rwof m c f) c f
      \<le> \<Down>{(s,s) | s. rwof m c f s} 
        (m \<bind> WHILE c f)"
      unfolding WHILE_def
      apply (rule bind_refine)
      apply (rule intro_prgR[where R="{(s,s) | s. rwof m c f s}"])
      apply (auto simp: pw_le_iff refine_pw_simps) []
      apply (cases m, simp, rule rwof.init, simp_all) []
    
      apply (rule WHILEI_refine)
      apply (auto simp: pw_le_iff refine_pw_simps pw_rwof_step')
      done
    thus "m \<bind> WHILEI (rwof m c f) c f \<le> m \<bind> WHILE c f"
      by (simp add: pw_le_iff refine_pw_simps)
  next
    show "m \<bind> WHILE c f \<le> m \<bind> WHILEI (rwof m c f) c f"
      unfolding WHILE_def 
      apply (rule bind_mono)
      apply (rule order_refl)
      apply (rule WHILEI_weaken)
      ..
  qed

  lemma WHILET_eq_I_rwof: "m \<bind> WHILET c f = m \<bind> WHILEIT (rwof m c f) c f"
  proof (rule antisym)
    have "m \<bind> WHILEIT (rwof m c f) c f
      \<le> \<Down>{(s,s) | s. rwof m c f s} 
        (m \<bind> WHILET c f)"
      unfolding WHILET_def
      apply (rule bind_refine)
      apply (rule intro_prgR[where R="{(s,s) | s. rwof m c f s}"])
      apply (auto simp: pw_le_iff refine_pw_simps) []
      apply (cases m, simp, rule rwof.init, simp_all) []
    
      apply (rule WHILEIT_refine)
      apply (auto simp: pw_le_iff refine_pw_simps pw_rwof_step')
      done
    thus "m \<bind> WHILEIT (rwof m c f) c f \<le> m \<bind> WHILET c f"
      by (simp add: pw_le_iff refine_pw_simps)
  next
    show "m \<bind> WHILET c f \<le> m \<bind> WHILEIT (rwof m c f) c f"
      unfolding WHILET_def 
      apply (rule bind_mono)
      apply (rule order_refl)
      apply (rule WHILEIT_weaken)
      ..
  qed


subsubsection \<open>Refinement\<close>
lemma rwof_refine:
  assumes RW: "rwof m c f s"
  assumes NF: "nofail (m' \<bind> WHILE c' f')"
  assumes M: "m \<le>\<^sub>n \<Down>R m'"
  assumes C: "\<And>s s'. \<lbrakk>(s,s')\<in>R; rwof m c f s; rwof m' c' f' s'\<rbrakk> \<Longrightarrow> c s = c' s'"
  assumes S: "\<And>s s'. \<lbrakk>(s,s')\<in>R; rwof m c f s; rwof m' c' f' s'; c s; c' s'\<rbrakk> \<Longrightarrow> f s \<le>\<^sub>n \<Down>R (f' s')"
  shows "\<exists>s'. (s,s')\<in>R \<and> rwof m' c' f' s'"
  using RW
  apply (induction rule: establish_rwof_invar[rotated -1,consumes 1])
  using M rwof_init[OF NF] 
  apply (simp only: pw_leof_iff pw_le_iff refine_pw_simps, blast) []

  using C S rwof_step[OF NF] 
  apply (simp only: pw_leof_iff pw_le_iff refine_pw_simps, blast) []
  done

subsubsection \<open>Total Correct Loops\<close>
text \<open>In this theory, we show that every non-failing total-correct 
  while loop gives rise to a compatible well-founded relation\<close>


definition rwof_rel 
  \<comment> \<open>Transitions in a while-loop as relation\<close>
  where "rwof_rel init cond step 
    \<equiv> {(s,s'). rwof init cond step s \<and> cond s \<and> inres (step s) s'}"

lemma rwof_rel_spec: "\<lbrakk>rwof init cond step s; cond s\<rbrakk> 
  \<Longrightarrow> step s \<le>\<^sub>n SPEC (\<lambda>s'. (s,s')\<in>rwof_rel init cond step)"
  unfolding rwof_rel_def
  by (auto simp: pw_leof_iff refine_pw_simps)  


lemma rwof_reachable:
  assumes "rwof init cond step s"
  shows "\<exists>s0. inres init s0 \<and> (s0,s)\<in>(rwof_rel init cond step)\<^sup>*"
  using assms
  apply (induction)
  unfolding rwof_rel_def
  apply (auto intro: rwof.intros) []
  apply clarsimp
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl, assumption)
  apply (auto intro: rwof.intros) []
  done
  
theorem nofail_WHILEIT_wf_rel: 
  assumes NF: "nofail (init \<bind> WHILEIT I cond step)"
  shows "wf ((rwof_rel init cond step)\<inverse>)"
proof (rule ccontr)
  assume "\<not>wf ((rwof_rel init cond step)\<inverse>)"
  then obtain f where IP: "\<And> i. (f i, f (Suc i)) \<in> rwof_rel init cond step"
    unfolding wf_iff_no_infinite_down_chain by auto
  hence "rwof init cond step (f 0)" by (auto simp: rwof_rel_def)
  then obtain s0 sn where "(s0, sn) \<in> (rwof_rel init cond step)\<^sup>*" "inres init s0" "sn = f 0"
    using rwof_reachable by metis
  then obtain f where P: "\<And> i. (f i, f (Suc i)) \<in> rwof_rel init cond step" and I: "inres init (f 0)"
  using IP
  proof (induct arbitrary: f)
    case (step sk sn)
    let ?f = "case_nat sk f"
    have "sk = ?f 0" "\<And> i. (?f i, ?f (Suc i)) \<in> rwof_rel init cond step"
      using step by (auto split: nat.splits)
    then show ?case using step by blast
  qed auto

  from P have [simp]: "\<And>i. cond (f i)"
    unfolding rwof_rel_def by auto

  from P have SIR: "\<And>i. inres (step (f i)) (f (Suc i))"
    unfolding rwof_rel_def by auto

  define F where "F = (WHILEI_body (\<bind>) RETURN I cond step)"

  {
    assume M: "trimono F"
    define f' where "f' x = (if x\<in>range f then FAIL else gfp F x)" for x

    have "f' \<le> F f'"
      unfolding f'_def
      apply (rule le_funI)
      apply (case_tac "x\<in>range f")
      apply simp_all
      defer
      apply (subst gfp_unfold)
      using M apply (simp add: trimono_def)
      apply (unfold F_def WHILEI_body_def) []
      apply (auto simp: pw_le_iff refine_pw_simps) []      

      apply (unfold F_def WHILEI_body_def not_nofail_iff[symmetric]) []
      using SIR
      apply (auto simp: pw_le_iff refine_pw_simps) []      
      done  
    from gfp_upperbound[of f' F,OF this] have "\<And>x. f' x \<le> gfp F x"
      by (auto dest: le_funD)
    from this[of "f 0"] have "gfp F (f 0) = FAIL"
      unfolding f'_def
      by auto

  } note aux=this

  have "FAIL \<le> WHILEIT I cond step (f 0)" 
    unfolding WHILET_def WHILEIT_def RECT_def
    apply clarsimp
    apply (subst gfp_eq_flatf_gfp[symmetric])
    apply (simp_all add: trimono_def) [2]
    apply (unfold F_def[symmetric])
    by (rule aux)
  with NF I show False by (auto simp: refine_pw_simps)
qed


subsection \<open>Convenience\<close>

subsubsection \<open>Iterate over range of list\<close>
lemma range_set_WHILE:
  assumes CEQ: "\<And>i s. c (i,s) \<longleftrightarrow> i<u"
  assumes F0: "F {} s0 = s0"
  assumes Fs: "\<And>s i X. \<lbrakk>l\<le>i; i<u\<rbrakk> 
    \<Longrightarrow> f (i, (F X s)) \<le> SPEC (\<lambda>(i',r). i'=i+1 \<and> r=F (insert (list!i) X) s)"
  shows "WHILET c f (l,s0) 
    \<le> SPEC (\<lambda>(_,r). r=F {list!i | i. l\<le>i \<and> i<u} s0)"
  apply (cases "\<not>(l<u)")
  apply (subst WHILET_unfold)
  using F0 apply (simp add: CEQ)
  apply (rule subst, assumption)
  apply ((fo_rule cong refl)+, auto) []

  apply (simp)
  apply (rule WHILET_rule[
    where R = "measure (\<lambda>(i,_). u-i)"
    and I = "\<lambda>(i,s). l\<le>i \<and> i\<le>u \<and> s = F {list!j | j. l\<le>j \<and> j<i} s0"
    ])
  apply rule

  apply simp
  apply (subst F0[symmetric])
  apply ((fo_rule cong refl)+, auto) []

  apply (clarsimp simp: CEQ)
  apply (rule order_trans[OF Fs], simp_all) []
  apply (auto
    intro!: fun_cong[OF arg_cong[of _ _ F]]
    elim: less_SucE) []

  apply (auto simp: CEQ) []
  done


end
