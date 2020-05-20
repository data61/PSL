(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
text \<open>Helper lemmas for sequential reasoning about Seq and Catch\<close>
theory SeqCatch_decomp 
imports SmallStep
begin

lemma redex_size[rule_format] :
"\<forall>r. redex c = r \<longrightarrow> size r \<le> size c"
  by(induct_tac c, simp_all)

lemma Normal_pre[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>u. s' = Normal u \<longrightarrow> (\<exists>v. s = Normal v)"
  by(erule step_induct, simp_all)


lemma Normal_pre_star[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow> \<forall>p' t. cfg\<^sub>2 = (p', Normal t) \<longrightarrow>
 (\<exists>p s. cfg\<^sub>1 = (p, Normal s))"
  apply(erule converse_rtranclp_induct)
   apply simp
  apply clarsimp
  apply(drule Normal_pre)
  by force



lemma Seq_decomp_Skip[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>p\<^sub>2. p = Seq Skip p\<^sub>2 \<longrightarrow> s' = s \<and> p' = p\<^sub>2"
  apply(erule step_induct, simp_all)
    apply clarsimp
    apply(erule step.cases, simp_all)
   apply clarsimp+
 done

lemma Seq_decomp_Throw[rule_format, OF _ refl, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>p\<^sub>2 z. s = Normal z \<longrightarrow> p = Seq Throw p\<^sub>2 \<longrightarrow> s' = s \<and> p' = Throw"
  apply(erule step_induct, simp_all)
  apply clarsimp
  apply(erule step.cases, simp_all)
 done

lemma Throw_star[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow> \<forall>s. cfg\<^sub>1 = (Throw, Normal s) \<longrightarrow>
  cfg\<^sub>2 = cfg\<^sub>1"
  apply(erule converse_rtranclp_induct)
   apply simp
  apply clarsimp
  apply(erule step.cases, simp_all)
 done

lemma Seq_decomp[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>p\<^sub>1 p\<^sub>2. p = Seq p\<^sub>1 p\<^sub>2 \<longrightarrow> p\<^sub>1 \<noteq> Skip \<longrightarrow> p\<^sub>1 \<noteq> Throw \<longrightarrow>
  (\<exists>p\<^sub>1'. \<Gamma> \<turnstile> (p\<^sub>1, s) \<rightarrow> (p\<^sub>1', s') \<and> p' = Seq p\<^sub>1' p\<^sub>2)"
  apply(erule step_induct, simp_all)
   apply clarsimp
   apply(drule redex_size)
   apply simp
  apply clarsimp
  apply(drule redex_size)
  apply simp
 done

lemma Seq_decomp_relpow:
"\<Gamma> \<turnstile> (Seq p\<^sub>1 p\<^sub>2, Normal s) \<rightarrow>\<^sup>nn (p', Normal s') \<Longrightarrow>
 final (p', Normal s') \<Longrightarrow>
 (\<exists>n1<n. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Throw, Normal s')) \<and> p'=Throw \<or>
 (\<exists>t n1 n2. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Skip, Normal t) \<and> n1 < n \<and> n2 < n \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal t) \<rightarrow>\<^sup>nn2 (p', Normal s'))"
  apply (induct n arbitrary: p\<^sub>1 p\<^sub>2 s p' s')
   apply (clarsimp simp: final_def)
  apply (simp only: relpowp.simps)
  apply (subst (asm) relpowp_commute[symmetric])
  apply clarsimp
  apply (rename_tac n p\<^sub>1 p\<^sub>2 s p' s' a b)
  apply(case_tac "p\<^sub>1 = Skip")
   apply clarsimp
   apply(drule Seq_decomp_Skip)
   apply clarsimp
   apply(drule_tac x=s in spec)
   apply(drule_tac x=0 in spec)
   apply simp
  apply (rename_tac n p\<^sub>1 p\<^sub>2 s p' s' a b)
  apply(case_tac "p\<^sub>1 = Throw")
   apply clarsimp
   apply(drule Seq_decomp_Throw)
   apply clarsimp
   apply(frule relpowp_imp_rtranclp)
   apply(drule Throw_star)
   apply clarsimp
   apply(rule_tac x=n in exI, simp)
  apply(drule Seq_decomp)
    apply assumption+
  apply (rename_tac n p\<^sub>1 p\<^sub>2 s p' s' a b)
  apply clarsimp
  apply(frule relpowp_imp_rtranclp)
  apply(drule Normal_pre_star) 
  apply clarsimp
  apply(drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec, drule meta_spec, drule meta_mp, assumption)
  apply(drule meta_mp, assumption)
  apply(erule disjE, clarsimp)
   apply (rename_tac n1)
   apply(rule_tac x="Suc n1" in exI, simp)
   apply (subst relpowp_commute[symmetric])
   apply(rule_tac relcomppI, assumption+)
  apply clarsimp
  apply (rename_tac t n1 n2)
  apply(drule_tac x=t in spec)
  apply(drule_tac x="Suc n1" in spec)
  apply simp
  apply(drule mp)
  apply (subst relpowp_commute[symmetric])
  apply(rule_tac relcomppI, assumption+)
  apply simp
 done

lemma Seq_decomp_star:
"\<Gamma> \<turnstile> (Seq p\<^sub>1 p\<^sub>2, Normal s) \<rightarrow>\<^sup>* (p', Normal s') \<Longrightarrow> final (p', Normal s') \<Longrightarrow>
 \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s') \<and> p'=Throw \<or>
 (\<exists>t. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Normal t) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal t) \<rightarrow>\<^sup>* (p', Normal s'))"
  apply (drule rtranclp_imp_relpowp)
  apply clarsimp
  apply (drule (1) Seq_decomp_relpow)
  apply (erule disjE)
   apply clarsimp
   apply (drule (1) relpowp_imp_rtranclp)
  apply clarsimp
  apply (drule  relpowp_imp_rtranclp)+
  apply clarsimp
 done

lemma Seq_decomp_relpowp_Fault:
"\<Gamma> \<turnstile> (Seq p\<^sub>1 p\<^sub>2, Normal s) \<rightarrow>\<^sup>nn (Skip, Fault f) \<Longrightarrow>
 (\<exists>n1. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Skip, Fault f)) \<or>
 (\<exists>t n1 n2. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Skip, Normal t) \<and> n1 < n \<and> n2 < n  \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal t) \<rightarrow>\<^sup>nn2 (Skip, Fault f))"
  apply (induct n arbitrary: s p\<^sub>1)
   apply (clarsimp simp: final_def)
  apply (simp only: relpowp.simps)
  apply (subst (asm) relpowp_commute[symmetric])
  apply clarsimp
  apply (rename_tac n s p\<^sub>1 a b)
  apply (case_tac "p\<^sub>1 = Skip")
   apply simp
   apply (drule Seq_decomp_Skip)
   apply clarify
   apply (drule_tac x=s in spec)
   apply (drule spec[where x=0])
   apply simp
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (drule Seq_decomp_Throw)
   apply fastforce
  apply (frule Seq_decomp )
    apply simp+
  apply clarsimp
  apply (rename_tac s p1 t p1')  
  apply (case_tac "\<exists>v. Normal v = t")
   apply clarsimp
   apply (rename_tac v)
   apply (drule_tac x=v in meta_spec)
   apply (drule_tac x=p1' in meta_spec)
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (rename_tac n1)
    apply (rule_tac x="n1+1" in exI)
    apply (drule (1) relpowp_Suc_I2, fastforce)
   apply clarsimp
   apply (rename_tac t n1 n2)
   apply (drule_tac x=t in spec)
   apply (drule_tac x="n1+1" in spec)
   apply simp
   apply (subst (asm) relpowp_commute[symmetric])
   apply (drule mp)
   apply (erule relcomppI, assumption)
   apply clarsimp
  apply (case_tac "t = Stuck")
   apply clarsimp
   apply (drule relpowp_imp_rtranclp)
   apply (fastforce dest: steps_Stuck_prop)
  apply (case_tac t, simp_all)
  apply (rename_tac f')
  apply (frule steps_Fault_prop[where s'="Fault f", OF relpowp_imp_rtranclp, THEN sym], rule refl)
  apply clarify
  apply (cut_tac c=p1' in steps_Fault[where \<Gamma>=\<Gamma> and f=f])
  apply (drule rtranclp_imp_relpowp)
  apply clarsimp
  apply (rename_tac n')
  apply (rule_tac x="n'+1" in exI)
  apply simp
  apply (subst relpowp_commute[symmetric])
  apply (erule relcomppI, assumption)
 done

lemma Seq_decomp_star_Fault[rule_format, OF _ refl, OF _ refl, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow> \<forall>p s p' f. cfg\<^sub>1 = (p, Normal s) \<longrightarrow> cfg\<^sub>2 = (Skip, Fault f) \<longrightarrow> 
 (\<forall>p\<^sub>1 p\<^sub>2. p = Seq p\<^sub>1 p\<^sub>2 \<longrightarrow> 
 (\<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Fault f))
 \<or> (\<exists>s'. (\<Gamma> \<turnstile> (p\<^sub>1,  Normal s) \<rightarrow>\<^sup>* (Skip, Normal s')) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal s') \<rightarrow>\<^sup>* (Skip, Fault f)))"
  apply(erule converse_rtranclp_induct)
   apply clarsimp
  apply clarsimp
  apply (rename_tac c s' s f p\<^sub>1 p\<^sub>2)
  apply (case_tac "p\<^sub>1 = Skip")
   apply simp
   apply (drule Seq_decomp_Skip)
   apply simp
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (drule Seq_decomp_Throw)
   apply simp
  apply (drule Seq_decomp)
    apply simp+
  apply clarsimp
  apply (case_tac s')
    apply simp
    apply (erule disjE)
     apply (erule (1) converse_rtranclp_into_rtranclp)
    apply clarsimp
    apply (rename_tac s')
    apply (erule_tac x="s'" in allE)
    apply (drule (1) converse_rtranclp_into_rtranclp, fastforce)
   apply simp
   apply (frule steps_Fault_prop[THEN sym], rule refl)
   apply simp
   apply (cut_tac c=p\<^sub>1' and f=f in steps_Fault[where \<Gamma>=\<Gamma>])
   apply (drule (2)  converse_rtranclp_into_rtranclp)
  apply clarsimp
  apply (frule steps_Stuck_prop[THEN sym], rule refl)
  apply simp
 done


lemma Seq_decomp_relpowp_Stuck:
"\<Gamma> \<turnstile> (Seq p\<^sub>1 p\<^sub>2, Normal s) \<rightarrow>\<^sup>nn (Skip, Stuck) \<Longrightarrow>
 (\<exists>n1. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Skip, Stuck)) \<or>
 (\<exists>t n1 n2. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>nn1 (Skip, Normal t) \<and> n1 < n \<and> n2 < n  \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal t) \<rightarrow>\<^sup>nn2 (Skip, Stuck))"
  apply (induct n arbitrary: s p\<^sub>1)
   apply (clarsimp simp: final_def)
  apply (simp only: relpowp.simps)
  apply (subst (asm) relpowp_commute[symmetric])
  apply clarsimp
  apply (rename_tac n s p\<^sub>1 a b)
  apply (case_tac "p\<^sub>1 = Skip")
   apply simp
   apply (drule Seq_decomp_Skip)
   apply clarify
   apply (drule_tac x=s in spec)
   apply (drule spec[where x=0])
   apply simp
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (drule Seq_decomp_Throw)
   apply fastforce
  apply (frule Seq_decomp )
    apply simp+
  apply clarsimp
  apply (rename_tac s p1 t p1')  
  apply (case_tac "\<exists>v. Normal v = t")
   apply clarsimp
   apply (rename_tac v)
   apply (drule_tac x=v in meta_spec)
   apply (drule_tac x=p1' in meta_spec)
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (rename_tac n1)
    apply (rule_tac x="n1+1" in exI)
    apply (drule (1) relpowp_Suc_I2, fastforce)
   apply clarsimp
   apply (rename_tac t n1 n2)
   apply (drule_tac x=t in spec)
   apply (drule_tac x="n1+1" in spec)
   apply simp
   apply (subst (asm) relpowp_commute[symmetric])
   apply (drule mp)
   apply (erule relcomppI, assumption)
   apply clarsimp
  apply (case_tac "\<exists>v. t = Fault v")
   apply clarsimp
   apply (drule relpowp_imp_rtranclp)
   apply (fastforce dest: steps_Fault_prop)
  apply (case_tac t, simp_all)
  apply (rename_tac p1')
  apply clarify
  apply (cut_tac c=p1' in steps_Stuck[where \<Gamma>=\<Gamma>])
  apply (drule rtranclp_imp_relpowp)
  apply clarsimp
  apply (rename_tac n')
  apply (rule_tac x="n'+1" in exI)
  apply simp
  apply (subst relpowp_commute[symmetric])
  apply (erule relcomppI, assumption)
 done

lemma Seq_decomp_star_Stuck[rule_format, OF _ refl, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* (Skip, Stuck) \<Longrightarrow> \<forall>p s p'. cfg\<^sub>1 = (p, Normal s) \<longrightarrow> 
 (\<forall>p\<^sub>1 p\<^sub>2. p = Seq p\<^sub>1 p\<^sub>2 \<longrightarrow> 
 (\<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Stuck))
 \<or> (\<exists>s'. (\<Gamma> \<turnstile> (p\<^sub>1,  Normal s) \<rightarrow>\<^sup>* (Skip, Normal s')) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal s') \<rightarrow>\<^sup>* (Skip, Stuck)))"
  apply(erule converse_rtranclp_induct)
   apply clarsimp
  apply clarsimp
  apply (rename_tac c s' s p\<^sub>1 p\<^sub>2)
  apply (case_tac "p\<^sub>1 = Skip")
   apply simp
   apply (drule Seq_decomp_Skip)
   apply simp
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (drule Seq_decomp_Throw)
   apply simp
  apply (drule Seq_decomp)
    apply simp+
  apply clarsimp
  apply (rename_tac s' s p\<^sub>1 p\<^sub>2 p\<^sub>1')
  apply (case_tac s')
    apply simp
    apply (erule disjE)
     apply (erule (1) converse_rtranclp_into_rtranclp)
    apply clarsimp
    apply (rename_tac s')
    apply (erule_tac x="s'" in allE)
    apply (drule (1) converse_rtranclp_into_rtranclp, fastforce)
   apply simp
   apply (drule steps_Fault_prop, rule refl, fastforce)
   apply simp
   apply (cut_tac c=p\<^sub>1' in steps_Stuck[where \<Gamma>=\<Gamma>])
  apply (frule steps_Stuck_prop[THEN sym], rule refl)
  apply simp
 done


lemma Catch_decomp_star[rule_format, OF _ refl, OF _ refl, OF _ _ refl]:
" \<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow>
    \<forall>p s p' s'.
       cfg\<^sub>1 = (p, Normal s) \<longrightarrow>
       cfg\<^sub>2 = (p', Normal s') \<longrightarrow>
       final (p', Normal s') \<longrightarrow>
       (\<forall>p\<^sub>1 p\<^sub>2.
           p = Catch p\<^sub>1 p\<^sub>2 \<longrightarrow>
           (\<exists>t. \<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal t) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal t) \<rightarrow>\<^sup>* (p', Normal s')) \<or>
           (\<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Normal s') \<and> p' = Skip))"
  apply (erule converse_rtranclp_induct)
   apply (clarsimp simp: final_def)
  apply clarsimp
  apply (rename_tac a b s p' s' p\<^sub>1 p\<^sub>2)
  apply (case_tac b)
    apply clarsimp
    apply (rename_tac x)
    apply (erule step_Normal_elim_cases)
      apply clarsimp
      apply (erule disjE)
       apply clarsimp
       apply (rename_tac t)
       apply (rule_tac x=t in exI)
       apply fastforce
      apply (erule impE)
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (clarsimp simp: final_def)
     apply (erule disjE)
      apply fastforce
     apply clarsimp
     apply (fastforce dest: no_steps_final simp: final_def)
    apply (clarsimp simp: final_def)
    apply (erule disjE)
     apply clarsimp
     apply (rename_tac s s' p\<^sub>2)
     apply (rule_tac x=s in exI)
     apply fastforce
    apply fastforce
   apply (fastforce dest: steps_Fault_prop)
  apply (fastforce dest: steps_Stuck_prop)
 done

lemma Catch_decomp_Skip[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>p\<^sub>2. p = Catch Skip p\<^sub>2 \<longrightarrow> s' = s \<and> p' = Skip"
  apply(erule step_induct, simp_all)
  apply clarsimp
  apply(erule step.cases, simp_all)
 done

lemma Catch_decomp[rule_format, OF _ refl] :
"\<Gamma> \<turnstile> (p, s) \<rightarrow> (p', s') \<Longrightarrow> 
 \<forall>p\<^sub>1 p\<^sub>2. p = Catch p\<^sub>1 p\<^sub>2 \<longrightarrow> p\<^sub>1 \<noteq> Skip \<longrightarrow> p\<^sub>1 \<noteq> Throw \<longrightarrow>
  (\<exists>p\<^sub>1'. \<Gamma> \<turnstile> (p\<^sub>1, s) \<rightarrow> (p\<^sub>1', s') \<and> p' = Catch p\<^sub>1' p\<^sub>2)"
  apply(erule step_induct, simp_all)
   apply clarsimp
  apply(drule redex_size)
  apply simp
  apply clarsimp
  apply(drule redex_size)
  apply simp
 done

lemma Catch_decomp_star_Fault[rule_format, OF _ refl, OF _ refl, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow> \<forall>p s f. cfg\<^sub>1 = (p, Normal s) \<longrightarrow> cfg\<^sub>2 = (Skip, Fault f) \<longrightarrow> 
 (\<forall>p\<^sub>1 p\<^sub>2. p = Catch p\<^sub>1 p\<^sub>2 \<longrightarrow> 
 (\<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Fault f)) 
 \<or> (\<exists>s'. (\<Gamma> \<turnstile> (p\<^sub>1,  Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal s') \<rightarrow>\<^sup>* (Skip, Fault f)))"
  apply(erule converse_rtranclp_induct)
   apply clarsimp
  apply clarsimp
  apply (rename_tac c s' s f p\<^sub>1 p\<^sub>2)
  apply (case_tac "p\<^sub>1 = Skip")
   apply (fastforce dest: Catch_decomp_Skip)
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (case_tac s')
     apply clarsimp
     apply (erule step_Normal_elim_cases)
       apply clarsimp
       apply (erule disjE)
        apply fastforce
       apply (fastforce elim: no_step_final simp:final_def)
      apply fastforce
     apply fastforce
    apply clarsimp
    apply (drule_tac x=s in spec)
    apply clarsimp
    apply (erule step_elim_cases, simp_all)
    apply clarsimp
    apply (cut_tac c=c\<^sub>1' and f=f in steps_Fault[where \<Gamma>=\<Gamma>])
    apply (drule steps_Fault_prop, rule refl)
    apply fastforce
   apply (fastforce dest: steps_Stuck_prop)
  apply (drule (2) Catch_decomp)
  apply clarsimp
  apply (rename_tac p\<^sub>1')
  apply (case_tac s')
    apply simp
    apply (erule disjE)
     apply (erule (1) converse_rtranclp_into_rtranclp)
    apply clarsimp
    apply (rename_tac s')
    apply (erule_tac x="s'" in allE)
    apply (drule (1) converse_rtranclp_into_rtranclp, fastforce)
   apply simp
   apply (frule steps_Fault_prop[THEN sym], rule refl)
   apply simp
   apply (cut_tac c=p\<^sub>1' and f=f in steps_Fault[where \<Gamma>=\<Gamma>])
   apply (drule (2)  converse_rtranclp_into_rtranclp)
  apply (fastforce dest: steps_Stuck_prop)
 done

lemma Catch_decomp_star_Stuck[rule_format, OF _ refl, OF _ refl, OF _ refl] :
"\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow>\<^sup>* cfg\<^sub>2 \<Longrightarrow> \<forall>p s. cfg\<^sub>1 = (p, Normal s) \<longrightarrow> cfg\<^sub>2 = (Skip, Stuck) \<longrightarrow> 
 (\<forall>p\<^sub>1 p\<^sub>2. p = Catch p\<^sub>1 p\<^sub>2 \<longrightarrow> 
 (\<Gamma> \<turnstile> (p\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, Stuck)) 
 \<or> (\<exists>s'. (\<Gamma> \<turnstile> (p\<^sub>1,  Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')) \<and> \<Gamma> \<turnstile> (p\<^sub>2, Normal s') \<rightarrow>\<^sup>* (Skip, Stuck)))"
  apply(erule converse_rtranclp_induct)
   apply clarsimp
  apply clarsimp
  apply (rename_tac c s' s p\<^sub>1 p\<^sub>2)
  apply (case_tac "p\<^sub>1 = Skip")
   apply (fastforce dest: Catch_decomp_Skip)
  apply (case_tac "p\<^sub>1 = Throw")
   apply simp
   apply (case_tac s')
     apply clarsimp
     apply (erule step_Normal_elim_cases)
       apply clarsimp
       apply (erule disjE)
        apply fastforce
       apply (fastforce elim: no_step_final simp:final_def)
      apply fastforce
     apply fastforce
    apply clarsimp
    apply (drule_tac x=s in spec)
    apply clarsimp
    apply (erule step_elim_cases, simp_all)
    apply clarsimp
    apply (rename_tac c\<^sub>1') 
    apply (cut_tac c=c\<^sub>1' in steps_Fault[where \<Gamma>=\<Gamma>])
    apply (drule steps_Fault_prop, rule refl)
    apply fastforce

   apply (drule_tac x=s in spec)
   apply clarsimp
   apply (erule step_elim_cases, simp_all)
   apply clarsimp
   apply (cut_tac c=c\<^sub>1' in steps_Stuck[where \<Gamma>=\<Gamma>])
   apply (fastforce)

  apply (drule (2) Catch_decomp)
  apply clarsimp
  apply (rename_tac p\<^sub>1')
  apply (case_tac s')
    apply simp
    apply (erule disjE)
     apply (erule (1) converse_rtranclp_into_rtranclp)
    apply clarsimp
    apply (rename_tac s')
    apply (erule_tac x="s'" in allE)
    apply (drule (1) converse_rtranclp_into_rtranclp, fastforce)
   apply simp
   apply (frule steps_Fault_prop[THEN sym], rule refl)
   apply fastforce
  apply (cut_tac c=p\<^sub>1' in steps_Stuck[where \<Gamma>=\<Gamma>])
  apply fastforce
 done

end
