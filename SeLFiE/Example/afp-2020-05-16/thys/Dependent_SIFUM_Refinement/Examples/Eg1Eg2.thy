theory Eg1Eg2
imports Eg1
        Eg2
        "../CompositionalRefinement"
begin

locale sifum_refinement_eg1_eg2 =
  A: sifum_example +
  C: sifum_example2

primrec Eg2_var\<^sub>C_of_Eg1 :: "Eg1.var \<Rightarrow> Eg2.var\<^sub>C"
where
  "Eg2_var\<^sub>C_of_Eg1 control_var = control_var\<^sub>C" |
  "Eg2_var\<^sub>C_of_Eg1 buffer = buffer\<^sub>C" |
  "Eg2_var\<^sub>C_of_Eg1 high_var = high_var\<^sub>C" |
  "Eg2_var\<^sub>C_of_Eg1 low_var = low_var\<^sub>C" |
  "Eg2_var\<^sub>C_of_Eg1 temp = temp\<^sub>C"

sublocale sifum_refinement_eg1_eg2 \<subseteq> sifum_refinement dma dma\<^sub>C \<C>_vars \<C>_vars\<^sub>C \<C> \<C>\<^sub>C A.eval\<^sub>w C.eval\<^sub>w undefined Eg2_var\<^sub>C_of_Eg1
  supply image_cong_simp [cong del] INF_cong_simp [cong] SUP_cong_simp [cong]
  apply(unfold_locales)
           apply(erule C.eval_det, simp)
          apply(rule C.Var_finite)
         apply(simp add:\<C>_vars\<^sub>C_def split:if_splits)
        apply(simp add:\<C>_vars\<^sub>C_def dma\<^sub>C_def)
       apply(simp add:\<C>_vars\<^sub>C_def dma\<^sub>C_def)
      apply(rule inj_onI, simp)
      apply(case_tac x)
          apply(case_tac y, simp+)
         apply(case_tac y, simp+)
        apply(case_tac y, simp+)
       apply(case_tac y, simp+)
      apply(case_tac y, simp+)
     apply(case_tac x\<^sub>A)
         apply(clarsimp simp:dma\<^sub>C_def dma_def dma_control_var_def dma_control_var\<^sub>C_def)+
    apply(case_tac x\<^sub>A)
        apply(clarsimp simp:\<C>_vars\<^sub>C_def \<C>_vars_def)+
   apply(rule set_eqI, clarsimp)
   apply(case_tac x, clarsimp)
        apply(rule_tac x=control_var in rev_image_eqI, clarsimp+)
       apply(case_tac xa, clarsimp+)
          apply(case_tac xb, clarsimp+)
      apply(case_tac xa, clarsimp+)
         apply(case_tac xb, clarsimp+)
     apply(case_tac xa, clarsimp+)
        apply(case_tac xb, clarsimp+)
    apply(case_tac xa, clarsimp+)
       apply(case_tac xb, clarsimp+)
   apply(case_tac xa, clarsimp+)
  apply(simp add:\<C>\<^sub>C_def)
  done

context sifum_refinement_eg1_eg2
begin


lemma bisim_simple_\<R>:
  "bisim_simple (A.\<R> \<Gamma> \<S> P)"
  unfolding bisim_simple_def
  apply clarsimp
  apply(drule_tac lc="\<langle>c\<^sub>1\<^sub>A, mds, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A" and lc'="\<langle>c\<^sub>2\<^sub>A, mds, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A" in A.bisim_simple_\<R>\<^sub>u)
  by simp

(* Don't know to what extent these helpers can be made generic enough to go into any parent theories.
   Again, mightn't be able to (or bother to) make some generic considering the aexp evaluator
   is going to be specific to each language. *)

lemma conc_only_vars_not_visible_abs:
  "(\<forall>v\<^sub>C. v\<^sub>C \<in> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> mem\<^sub>C v\<^sub>C = mem\<^sub>C' v\<^sub>C) \<Longrightarrow> mem\<^sub>A_of mem\<^sub>C = mem\<^sub>A_of mem\<^sub>C'"
  by (simp add: mem\<^sub>A_of_def)

lemma conc_only_var_assign_not_visible_abs:
  "\<forall>v\<^sub>C e. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> mem\<^sub>A_of mem\<^sub>C = mem\<^sub>A_of (mem\<^sub>C(v\<^sub>C := e))"
  using conc_only_vars_not_visible_abs
  by simp

lemma reg\<^sub>C_is_not_the_var\<^sub>C_of_anything:
  "reg\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> False"
  by (induct x, clarsimp+)

lemma reg\<^sub>C_not_visible_abs:
  "reg\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1"
  using reg\<^sub>C_is_not_the_var\<^sub>C_of_anything
  by blast

(* This one's pretty specific to this refinement... *)
lemma reg\<^sub>C_the_only_concrete_only_var:
  "v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<Longrightarrow> v\<^sub>C = reg\<^sub>C"
  apply(case_tac v\<^sub>C)
       apply(erule rev_notE, clarsimp, rule_tac x=control_var in range_eqI, clarsimp)
      apply(erule rev_notE, clarsimp, rule_tac x=buffer in range_eqI, clarsimp)
     apply(erule rev_notE, clarsimp, rule_tac x=high_var in range_eqI, clarsimp)
    apply(erule rev_notE, clarsimp, rule_tac x=low_var in range_eqI, clarsimp)
   apply(erule rev_notE, clarsimp, rule_tac x=temp in range_eqI, clarsimp)
  apply clarsimp
  done

lemma NoRW\<^sub>A_implies_NoRW\<^sub>C:
  "x \<in> mds\<^sub>A_of mds\<^sub>C AsmNoReadOrWrite \<Longrightarrow>
   Eg2_var\<^sub>C_of_Eg1 x \<in> mds\<^sub>C AsmNoReadOrWrite"
  unfolding mds\<^sub>A_of_def
  apply clarsimp
  apply (simp only: Eg2_var\<^sub>C_of_Eg1_def)
  apply clarsimp
  apply (simp add: f_inv_into_f)
  done

lemma NoWrite\<^sub>A_implies_NoWrite\<^sub>C:
  "x \<in> mds\<^sub>A_of mds\<^sub>C AsmNoWrite \<Longrightarrow>
   Eg2_var\<^sub>C_of_Eg1 x \<in> mds\<^sub>C AsmNoWrite"
  unfolding mds\<^sub>A_of_def
  apply clarsimp
  apply (simp only: Eg2_var\<^sub>C_of_Eg1_def)
  apply clarsimp
  apply (simp add: f_inv_into_f)
  done

lemma assign_eval\<^sub>w_load\<^sub>A:
  shows "(\<langle>x \<leftarrow> Eg1.Load y, mds, mem\<rangle>\<^sub>A, \<langle>Stop, mds, mem (x := mem y)\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
  by (metis A.assign_eval\<^sub>w ev\<^sub>A.simps(2))

lemma assign_eval\<^sub>w_load\<^sub>C:
  shows "(\<langle>x \<leftarrow> Load y, mds, mem\<rangle>\<^sub>C, \<langle>Stop, mds, mem (x := mem y)\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.unannotated[OF C.assign, where E="[]", simplified]
  apply(drule_tac x=x in meta_spec)
  apply(drule_tac x="Load y" in meta_spec)
  apply(drule_tac x=mds in meta_spec)
  apply(drule_tac x=mem in meta_spec)
  apply clarsimp
  done

lemma assign_eval\<^sub>w_const\<^sub>A:
  shows "(\<langle>x \<leftarrow> Eg1.Const c, mds, mem\<rangle>, \<langle>Stop, mds, mem (x := c)\<rangle>) \<in> A.eval\<^sub>w"
  by (metis A.assign_eval\<^sub>w ev\<^sub>A.simps(1))

lemma assign_eval\<^sub>w_const\<^sub>C:
  shows "(\<langle>x \<leftarrow> Const c, mds, mem\<rangle>, \<langle>Stop, mds, mem (x := c)\<rangle>) \<in> C.eval\<^sub>w"
  using C.unannotated[OF C.assign, where E="[]", simplified]
  apply(drule_tac x=x in meta_spec)
  apply(drule_tac x="Const c" in meta_spec)
  apply(drule_tac x=mds in meta_spec)
  apply(drule_tac x=mem in meta_spec)
  apply clarsimp
  done

lemma if_seq_eval\<^sub>w_helper\<^sub>A:
  "(\<langle>If B T E, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B mem B then T else E, mds, mem\<rangle>\<^sub>A) \<in> A.eval\<^sub>w
    \<Longrightarrow>
   (\<langle>If B T E ;; TAIL, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B mem B then T ;; TAIL else E ;; TAIL, mds, mem\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
  using A.eval\<^sub>w.seq
  by auto

lemma if_seq_eval\<^sub>w_helper\<^sub>C:
  "(\<langle>If B T E, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B\<^sub>C mem B then T else E, mds, mem\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
    \<Longrightarrow>
   (\<langle>If B T E ;; TAIL, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B\<^sub>C mem B then T ;; TAIL else E ;; TAIL, mds, mem\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.eval\<^sub>w.seq
  by auto

lemma mem_assign_refinement_helper_var:
  "mem\<^sub>A_of (mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x := mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 y)))
       = (mem\<^sub>A_of mem\<^sub>C) (x := (mem\<^sub>A_of mem\<^sub>C) y)"
  apply(clarsimp simp: mem\<^sub>A_of_def)
  apply(rule ext, clarsimp)
  apply(cases x)
      apply(case_tac x\<^sub>A, clarsimp+)+
  done

lemma mem_assign_refinement_helper_const:
  "mem\<^sub>A_of (mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x := c))
       = (mem\<^sub>A_of mem\<^sub>C) (x := c)"
  apply(clarsimp simp: mem\<^sub>A_of_def)
  apply(rule ext, clarsimp)
  apply(cases x)
      apply(case_tac x\<^sub>A, clarsimp+)+
  done

lemma if_true_eval\<^sub>w\<^sub>C:
  shows "mem\<^sub>C x = 0 \<longrightarrow>
     (\<langle>(If (Eq x 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C,
      \<langle>(c\<^sub>C_then ;; c\<^sub>C_tail), mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.if_eval\<^sub>w C.eval\<^sub>w.seq ev\<^sub>B\<^sub>C.simps by presburger

lemma if_false_eval\<^sub>w\<^sub>C:
  shows "mem\<^sub>C x \<noteq> 0 \<longrightarrow>
     (\<langle>(If (Eq x 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C,
      \<langle>(c\<^sub>C_else ;; c\<^sub>C_tail), mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.if_eval\<^sub>w C.eval\<^sub>w.seq ev\<^sub>B\<^sub>C.simps by presburger


end

end
