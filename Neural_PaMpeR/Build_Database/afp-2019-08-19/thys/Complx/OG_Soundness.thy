(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Soundness proof of Owicki-Gries w.r.t.
           COMPLX small-step semantics\<close>

theory OG_Soundness
imports
  OG_Hoare
  SeqCatch_decomp  
begin

lemma pre_weaken_pre:
 " x \<in> pre P  \<Longrightarrow> x \<in> pre (weaken_pre P P')"
 by (induct P, clarsimp+)

lemma oghoare_Skip[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = Skip \<longrightarrow> 
 (\<exists>P'. P = AnnExpr P' \<and> P' \<subseteq> Q)"
  apply (induct rule: oghoare_induct, simp_all)
  apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'')
  apply(case_tac P, simp_all)
  by force

lemma oghoare_Throw[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = Throw \<longrightarrow> 
 (\<exists>P'. P = AnnExpr P' \<and> P' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
  apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'')
  apply(case_tac P, simp_all)
  by force

lemma oghoare_Basic[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = Basic f \<longrightarrow> 
 (\<exists>P'. P = AnnExpr P' \<and> P' \<subseteq> {x. f x \<in> Q})"
  apply (induct rule: oghoare_induct, simp_all)
   apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'')
  apply(case_tac P, simp_all)
  by force

lemma oghoare_Spec[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = Spec r \<longrightarrow> 
 (\<exists>P'. P = AnnExpr P' \<and> P' \<subseteq> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)})"
  apply (induct rule: oghoare_induct, simp_all)
  apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'')
  apply(case_tac P, simp_all)
  by force

lemma oghoare_DynCom[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = (DynCom c') \<longrightarrow> 
 (\<exists>r ad. P = (AnnRec r ad) \<and> r \<subseteq> pre ad \<and> (\<forall>s\<in>r. \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> ad (c' s) Q,A))"
  apply (induct rule: oghoare_induct, simp_all)
   apply clarsimp
  apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'' x)
  apply(case_tac P, simp_all)
  apply clarsimp
  apply (rename_tac P s)
  apply (drule_tac x=s in bspec, simp)
  apply (rule Conseq)
  apply (rule_tac x="{}" in exI)
  apply (fastforce)
 done

lemma oghoare_Guard[rule_format, OF _ refl]: 
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> c = Guard f g d \<longrightarrow> 
 (\<exists>P' r . P = AnnRec r P' \<and> 
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' d Q,A \<and>
   r \<inter> g \<subseteq> pre P' \<and>
   (r \<inter> -g \<noteq> {} \<longrightarrow> f \<in> F))"
  apply (induct rule: oghoare_induct, simp_all)
   apply force
  apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P Q A P' Q' A' P'' r)
  apply (case_tac P, simp_all)
  apply clarsimp
  apply (rename_tac r)
  apply(rule conjI)
   apply (rule Conseq)
   apply (rule_tac x="{}" in exI)
   apply (rule_tac x="Q'" in exI)
   apply (rule_tac x="A'" in exI)
   apply (clarsimp)
  apply (case_tac "(r \<union> P') \<inter> g \<noteq> {}")
   apply fast
  apply clarsimp
  apply(drule equalityD1, force)
 done

lemma oghoare_Await[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta>\<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow> \<forall>b c. x = Await b c \<longrightarrow>
 (\<exists>r P' Q' A'. P = AnnRec r P' \<and> \<Gamma>, \<Theta>\<tturnstile>\<^bsub>/F\<^esub>(r \<inter> b) P' c Q',A' \<and> atom_com c 
                 \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
    apply (rename_tac \<Gamma> \<Theta> F r P Q A)
   apply (rule_tac x=Q in exI)
   apply (rule_tac x=A in exI)
   apply clarsimp
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp

  apply(case_tac P, simp_all)
  apply (rename_tac P'' Q'' A'' x y)
  apply (rule_tac x=Q'' in exI)
  apply (rule_tac x=A'' in exI)
  apply clarsimp
  apply (rule conjI[rotated])
   apply blast
  apply (erule SeqConseq[rotated])
    apply simp
   apply simp
  apply blast
 done

lemma oghoare_Seq[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow> \<forall>p1 p2. x = Seq p1 p2 \<longrightarrow>
 (\<exists> P\<^sub>1 P\<^sub>2 P' Q' A'. P = AnnComp P\<^sub>1 P\<^sub>2 \<and> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 p1 P', A' \<and> P' \<subseteq> pre P\<^sub>2 \<and>
         \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 p2 Q',A' \<and>
          Q' \<subseteq> Q \<and> A' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
   apply blast
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp
  apply (rename_tac P'' Q'' A'')
  apply(case_tac P, simp_all)
  apply clarsimp
  apply (rule_tac x="P''" in exI)
  apply (rule_tac x="Q''" in exI)
  apply (rule_tac x="A''" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule Conseq)
   apply (rule_tac x="P'" in exI)
   apply (rule_tac x="P''" in exI)
   apply (rule_tac x="A''" in exI)
   apply simp
  apply fastforce
 done

lemma oghoare_Catch[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow> \<forall>p1 p2. x = Catch p1 p2 \<longrightarrow>
 (\<exists> P\<^sub>1 P\<^sub>2 P' Q' A'. P = AnnComp P\<^sub>1 P\<^sub>2 \<and> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 p1 Q', P' \<and> P' \<subseteq> pre P\<^sub>2 \<and>
         \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 p2 Q',A' \<and>
          Q' \<subseteq> Q \<and> A' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
   apply blast
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp
  apply(case_tac P, simp_all)
  apply clarsimp
  apply (rename_tac P'' Q'' A'' x)
  apply (rule_tac x="P''" in exI)
  apply (rule_tac x="Q''" in exI)
  apply clarsimp
   apply (rule conjI)
   apply (rule Conseq)
   apply (rule_tac x=P' in exI)
   apply fastforce
  apply (rule_tac x="A''" in exI)
  apply clarsimp
  apply fastforce
 done

lemma oghoare_Cond[rule_format, OF _ refl]: 
 "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow>
\<forall>c\<^sub>1 c\<^sub>2 b. x = (Cond b c\<^sub>1 c\<^sub>2) \<longrightarrow>
(\<exists>P' P\<^sub>1 P\<^sub>2 Q' A'. P = (AnnBin P' P\<^sub>1 P\<^sub>2) \<and>
  P' \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>pre P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>pre P\<^sub>2)} \<and>
    \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q',A' \<and>
    \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q',A' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
   apply (rule conjI)
    apply fastforce
   apply (rename_tac  Q A P\<^sub>2 c\<^sub>2 r b)
   apply (rule_tac x=Q in exI)
   apply (rule_tac x=A in exI)
   apply fastforce
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp
  apply (case_tac P, simp_all)
  apply fastforce
done

lemma oghoare_While[rule_format, OF _ refl]:
  "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow>
    \<forall> b c. x = While b c \<longrightarrow>
    (\<exists> r i P' A' Q'. P = AnnWhile r i P' \<and>
     \<Gamma>, \<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c i,A' \<and>
     r \<subseteq> i \<and>
     i \<inter> b \<subseteq> pre P' \<and>
     i \<inter> -b \<subseteq> Q' \<and>
      Q' \<subseteq> Q \<and> A' \<subseteq> A)"
  apply (induct rule: oghoare_induct, simp_all)
   apply blast
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp
  apply (rename_tac P' Q' A' b ca r i P'' A'' Q'')
  apply (case_tac P; simp)
  apply (rule_tac x= A'' in exI)
  apply (rule conjI)
   apply blast
  apply clarsimp
  apply (rule_tac x= "Q'" in exI)
  by fast


lemma oghoare_Call:
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow>
  \<forall>p. x = Call p \<longrightarrow>
 (\<exists>r n.
 P = (AnnCall r n) \<and>
 (\<exists>as P' f b.
 \<Theta> p = Some as \<and>
 (as ! n) = P' \<and>
 r \<subseteq> pre P' \<and>
 \<Gamma> p = Some b \<and>
 n < length as \<and>
 \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P' b Q,A))"
  apply (induct rule: oghoare_induct, simp_all)
  apply (rename_tac \<Gamma> \<Theta> F P c Q A)
  apply clarsimp
  apply (case_tac P, simp_all)
  apply clarsimp
  apply (rule Conseq)
  apply (rule_tac x="{}" in exI)
  apply force
 done

lemma oghoare_Parallel[rule_format, OF _ refl]: 
"\<Gamma>, \<Theta>\<turnstile>\<^bsub>/F\<^esub> P x Q,A \<Longrightarrow> \<forall>cs. x = Parallel cs \<longrightarrow>
 (\<exists>as. P = AnnPar as \<and> 
   length as = length cs \<and>
   \<Inter>(set (map postcond as)) \<subseteq> Q \<and>
   \<Union>(set (map abrcond as)) \<subseteq> A \<and>
   (\<forall>i<length cs. \<exists>Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (pres (as!i)) (cs!i) Q', A' \<and>
            Q' \<subseteq> postcond (as!i) \<and> A' \<subseteq> abrcond (as!i)) \<and>
  interfree \<Gamma> \<Theta> F as cs)"
  apply (induct rule: oghoare_induct, simp_all)
   apply clarsimp
   apply (drule_tac x=i in spec)
   apply fastforce
  apply clarsimp
  apply (case_tac P, simp_all)
  apply blast
 done

lemma  ann_matches_weaken[OF _ refl]:
" ann_matches \<Gamma> \<Theta> X c \<Longrightarrow> X = (weaken_pre P P') \<Longrightarrow> ann_matches \<Gamma> \<Theta> P c"
  apply (induct arbitrary: P P' rule: ann_matches.induct)
   apply (case_tac P, simp_all, fastforce simp add: ann_matches.intros)+
done


lemma oghoare_seq_imp_ann_matches:
 " \<Gamma>,\<Theta>\<tturnstile>\<^bsub>/F\<^esub> P a c Q,A \<Longrightarrow> ann_matches \<Gamma> \<Theta> a c"
  apply (induct rule: oghoare_seq_induct, simp_all add: ann_matches.intros)
  apply (clarsimp, erule ann_matches_weaken)+
 done

lemma oghoare_imp_ann_matches:
 " \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> a c Q,A \<Longrightarrow> ann_matches \<Gamma> \<Theta> a c"
  apply (induct rule: oghoare_induct, simp_all add: ann_matches.intros oghoare_seq_imp_ann_matches)
  apply (clarsimp, erule ann_matches_weaken)+
 done

(* intros *)

lemma SkipRule: "P \<subseteq> Q \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr P) Skip Q, A"
  apply (rule Conseq, simp)
  apply (rule exI, rule exI, rule exI)
  apply (rule conjI, rule Skip, auto)
done

lemma ThrowRule: "P \<subseteq> A \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr P) Throw Q, A"
  apply (rule Conseq, simp)
  apply (rule exI, rule exI, rule exI)
  apply (rule conjI, rule Throw, auto)
done

lemma BasicRule: "P \<subseteq> {s. (f s) \<in> Q} \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr P) (Basic f) Q, A"
  apply (rule Conseq, simp, rule exI[where x="{s. (f s) \<in> Q}"])
  apply (rule exI[where x=Q], rule exI[where x=A])
  apply simp
  apply (subgoal_tac "(P \<union> {s. f s \<in> Q}) = {s. f s \<in> Q}")
  apply (auto intro: Basic)
done

lemma SpecRule:
  "P \<subseteq> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)}
    \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr P) (Spec r) Q, A"
  apply (rule Conseq, simp, rule exI[where x="{s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r) }"])
  apply (rule exI[where x=Q], rule exI[where x=A])
  apply simp
  apply (subgoal_tac "(P \<union> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)}) = {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)}")
   apply (auto intro: Spec)
done

lemma CondRule: 
 "\<lbrakk> P \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>pre P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>pre P\<^sub>2)};
    \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,A; 
    \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A  \<rbrakk> 
  \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnBin P P\<^sub>1 P\<^sub>2) (Cond b c\<^sub>1 c\<^sub>2) Q,A"
  by (auto intro: Cond)

lemma WhileRule: "\<lbrakk> r \<subseteq> I; I \<inter> b \<subseteq> pre P; (I \<inter> -b) \<subseteq> Q;
                    \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c I,A \<rbrakk>  
        \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnWhile r I P) (While b c) Q,A"
  by (simp add: While)

lemma AwaitRule:
 "\<lbrakk>atom_com c ; \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>P a c Q,A ; (r \<inter> b) \<subseteq> P\<rbrakk> \<Longrightarrow>
  \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r a) (Await b c) Q,A"
  apply (erule Await[rotated])
  apply (erule (1) SeqConseq, simp+)
 done

lemma rtranclp_1n_induct [consumes 1, case_names base step]:
  "\<lbrakk>r\<^sup>*\<^sup>* a b; P a; \<And>y z. \<lbrakk>r y z; r\<^sup>*\<^sup>* z b; P y\<rbrakk> \<Longrightarrow> P z\<rbrakk> \<Longrightarrow> P b" 
 by (induct rule: rtranclp.induct) 
    (simp add: rtranclp.rtrancl_into_rtrancl)+

lemmas rtranclp_1n_induct2[consumes 1, case_names base step] = 
  rtranclp_1n_induct[of _ "(ax,ay)" "(bx,by)", split_rule]

lemma oghoare_seq_valid:
 " \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c\<^sub>1 R,A \<Longrightarrow>
   \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> R c\<^sub>2 Q,A \<Longrightarrow>
   \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P Seq c\<^sub>1 c\<^sub>2 Q,A"
  apply (clarsimp simp add: valid_def)
  apply (rename_tac t c' s)
  apply (case_tac t)
    apply simp
    apply (drule (1) Seq_decomp_star)
    apply (erule disjE)
     apply fastforce
    apply clarsimp
    apply (rename_tac s1 t')
    apply (drule_tac x="Normal s" and y="Normal t'" in spec2)
    apply (erule_tac x="Skip" in allE)
    apply (fastforce simp: final_def)
   apply (clarsimp simp add: final_def)
   apply (drule Seq_decomp_star_Fault)
   apply (erule disjE)
    apply (rename_tac s2)
    apply (drule_tac x="Normal s" and y="Fault s2" in spec2)
    apply (erule_tac x="Skip" in allE)
    apply fastforce
   apply clarsimp
   apply (rename_tac s s2 s')
   apply (drule_tac x="Normal s" and y="Normal s'" in spec2)
   apply (erule_tac x="Skip" in allE)
   apply clarsimp
   apply (drule_tac x="Normal s'" and y="Fault s2" in spec2)
   apply (erule_tac x="Skip" in allE)
   apply clarsimp
  apply clarsimp
  apply (simp add: final_def)
  apply (drule Seq_decomp_star_Stuck)
  apply (erule disjE)
   apply fastforce
  apply clarsimp
  apply fastforce
 done

lemma oghoare_if_valid:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,A \<Longrightarrow>
  \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A \<Longrightarrow>
  r \<inter> b \<subseteq> P\<^sub>1 \<Longrightarrow> r \<inter> - b \<subseteq> P\<^sub>2 \<Longrightarrow>
  \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> r Cond b c\<^sub>1 c\<^sub>2 Q,A"
  apply (simp (no_asm) add: valid_def)
  apply (clarsimp)
  apply (erule converse_rtranclpE) 
   apply (clarsimp simp: final_def)
  apply (erule step_Normal_elim_cases)
   apply (fastforce simp: valid_def[where c=c\<^sub>1])
  apply (fastforce simp: valid_def[where c=c\<^sub>2])
 done

lemma Skip_normal_steps_end:
"\<Gamma> \<turnstile> (Skip, Normal s) \<rightarrow>\<^sup>* (c, s') \<Longrightarrow> c = Skip \<and> s' = Normal s"
  apply  (erule converse_rtranclpE)
   apply simp
  apply (erule step_Normal_elim_cases)
 done

lemma Throw_normal_steps_end:
"\<Gamma> \<turnstile> (Throw, Normal s) \<rightarrow>\<^sup>* (c, s') \<Longrightarrow> c = Throw \<and> s' = Normal s"
  apply  (erule converse_rtranclpE)
   apply simp
  apply (erule step_Normal_elim_cases)
 done

lemma while_relpower_induct:
 "\<And>t c' x .
       \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c i,A \<Longrightarrow>
       i \<inter> b \<subseteq> P \<Longrightarrow>
       i \<inter> - b \<subseteq> Q \<Longrightarrow>
       final (c', t) \<Longrightarrow>
       x \<in> i \<Longrightarrow>
       t \<notin> Fault ` F \<Longrightarrow>
       c' = Throw \<longrightarrow> t \<notin> Normal ` A \<Longrightarrow>
       (step \<Gamma> ^^ n) (While b c, Normal x) (c', t) \<Longrightarrow> c' = Skip \<and> t \<in> Normal ` Q"
  apply (induct n rule:less_induct)
  apply (rename_tac n t c' x)
  apply (case_tac n)
   apply (clarsimp simp: final_def)
  apply clarify
  apply (simp only: relpowp.simps)
  apply (subst (asm) relpowp_commute[symmetric])
  apply clarsimp
  apply (erule step_Normal_elim_cases)
   apply clarsimp
   apply (rename_tac t c' x v)
   apply(case_tac "t")
    apply clarsimp
    apply(drule Seq_decomp_relpow)
     apply(simp add: final_def)
     apply(erule disjE, erule conjE)
      apply clarify
      apply(drule relpowp_imp_rtranclp)
      apply (simp add: valid_def)
      apply (rename_tac x n t' n1)
      apply (drule_tac x="Normal x" in spec)
      apply (drule_tac x="Normal t'" in spec)
      apply (drule spec[where x=Throw])
      apply (fastforce simp add: final_def)
     apply clarsimp
     apply (rename_tac c' x n t' t n1 n2)
     apply (drule_tac x=n2 and y="Normal t'" in meta_spec2)
     apply (drule_tac x=c' and y="t" in meta_spec2)
     apply (erule meta_impE, fastforce)
     apply (erule meta_impE, fastforce)
     apply (erule meta_impE)
      apply(drule relpowp_imp_rtranclp)
      apply (simp add: valid_def)
      apply (drule_tac x="Normal x" and y="Normal t" in spec2)
      apply (drule spec[where x=Skip])
      apply (fastforce simp add: final_def)
     apply assumption
    apply clarsimp
    apply (rename_tac c' s n f)
    apply (subgoal_tac "c' = Skip", simp)
     prefer 2
     apply (case_tac c'; fastforce simp: final_def)
    apply (drule Seq_decomp_relpowp_Fault)
    apply (erule disjE)
     apply (clarsimp simp: valid_def)
     apply (drule_tac x="Normal s" and y="Fault f" in spec2)
     apply (drule spec[where x=Skip])
     apply(drule relpowp_imp_rtranclp)
     apply (fastforce simp: final_def)
    apply clarsimp
    apply (rename_tac t n1 n2)
    apply (subgoal_tac "t \<in> i")
     prefer 2
     apply (fastforce dest:relpowp_imp_rtranclp simp: final_def valid_def)
    apply (drule_tac x=n2 in meta_spec)
    apply (drule_tac x="Fault f" in meta_spec)
    apply (drule meta_spec[where x=Skip])
    apply (drule_tac x=t in meta_spec)
    apply (fastforce simp: final_def)
   apply clarsimp
   apply (rename_tac c' s n)
   apply (subgoal_tac "c' = Skip", simp)
    prefer 2
    apply (case_tac c'; fastforce simp: final_def)
    apply (drule Seq_decomp_relpowp_Stuck)
    apply clarsimp
    apply (erule disjE)
     apply (simp add:valid_def)
     apply (drule_tac x="Normal s" and y="Stuck" in spec2)
     apply clarsimp
     apply (drule spec[where x=Skip])
     apply(drule relpowp_imp_rtranclp)
     apply (fastforce)
    apply clarsimp
   apply (rename_tac t n1 n2)
   apply (subgoal_tac "t \<in> i")
    prefer 2
    apply (fastforce dest:relpowp_imp_rtranclp simp: final_def valid_def)
   apply (drule_tac x=n2 in meta_spec)
   apply (drule meta_spec[where x=Stuck])
   apply (drule meta_spec[where x=Skip])
   apply (drule_tac x=t in meta_spec)
   apply (fastforce simp: final_def)
  apply clarsimp
  apply (drule relpowp_imp_rtranclp)
  apply (drule Skip_normal_steps_end)
  apply fastforce
done

lemma valid_weaken_pre:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow>
  P' \<subseteq> P \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P' c Q,A"
 by (fastforce simp: valid_def)

lemma valid_strengthen_post:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow>
  Q \<subseteq> Q' \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q',A"
 by (fastforce simp: valid_def)

lemma valid_strengthen_abr:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow>
  A \<subseteq> A' \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A'"
 by (fastforce simp: valid_def)

lemma oghoare_while_valid:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c i,A \<Longrightarrow>
  i \<inter> b \<subseteq> P \<Longrightarrow>
  i \<inter> - b \<subseteq> Q \<Longrightarrow>
  \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> i While b c Q,A"
  apply (simp (no_asm) add: valid_def)
  apply (clarsimp simp add: )
  apply (drule rtranclp_imp_relpowp)
  apply (clarsimp)
  by (erule while_relpower_induct)

lemma oghoare_catch_valid:
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,P\<^sub>2 \<Longrightarrow>
  \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A \<Longrightarrow>
    \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P\<^sub>1 Catch c\<^sub>1 c\<^sub>2 Q,A"
  apply (clarsimp simp add: valid_def[where c="Catch _ _"])
  apply (rename_tac t c' s)
  apply (case_tac t)
    apply simp            
    apply (drule Catch_decomp_star)
     apply (fastforce simp: final_def)
    apply clarsimp
    apply (erule disjE)
     apply (clarsimp simp add: valid_def[where c="c\<^sub>1"])
     apply (rename_tac s x t)
     apply (drule_tac x="Normal s" in spec) 
     apply (drule_tac x="Normal t" in spec)
     apply (drule_tac x=Throw in spec)
     apply (fastforce simp: final_def valid_def)
    apply (clarsimp simp add: valid_def[where c="c\<^sub>1"])
    apply (rename_tac s t)
    apply (drule_tac x="Normal s" in spec)
    apply (drule_tac x="Normal t" in spec)
    apply (drule_tac x=Skip in spec)
    apply (fastforce simp: final_def)
   apply (rename_tac c' s t)
   apply (simp add: final_def)
   apply (drule Catch_decomp_star_Fault)
   apply clarsimp
   apply (erule disjE)
    apply (clarsimp simp: valid_def[where c=c\<^sub>1] final_def)
   apply (fastforce simp: valid_def final_def)
  apply (simp add: final_def)
  apply (drule Catch_decomp_star_Stuck)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: valid_def[where c=c\<^sub>1] final_def)
  apply (fastforce simp: valid_def final_def)
 done

lemma ann_matches_imp_assertionsR:
  "ann_matches \<Gamma> \<Theta> a c \<Longrightarrow> \<not> pre_par a \<Longrightarrow>
    assertionsR \<Gamma> \<Theta> Q A a c (pre a)"
  by (induct arbitrary: Q A  rule: ann_matches.induct , (fastforce intro:  assertionsR.intros )+)

lemma ann_matches_imp_assertionsR':
  "ann_matches \<Gamma> \<Theta> a c \<Longrightarrow> a' \<in> pre_set a \<Longrightarrow>
    assertionsR \<Gamma> \<Theta> Q A a c a'"
 apply (induct arbitrary: Q A  rule: ann_matches.induct)
  apply ((fastforce intro:  assertionsR.intros )+)[12]
  apply simp
  apply (erule bexE)
  apply (simp only: in_set_conv_nth)
  apply (erule exE)
  apply (drule_tac x=i in spec)
  apply clarsimp
  apply (erule AsParallelExprs)
  apply simp
done

lemma rtranclp_conjD:
  "(\<lambda>x1 x2. r1 x1 x2 \<and> r2 x1 x2)\<^sup>*\<^sup>* x1 x2 \<Longrightarrow>
  r1\<^sup>*\<^sup>* x1 x2 \<and> r2\<^sup>*\<^sup>* x1 x2"
by (metis (no_types, lifting) rtrancl_mono_proof)

lemma rtranclp_mono' :
"r\<^sup>*\<^sup>* a b \<Longrightarrow> r \<le> s \<Longrightarrow> s\<^sup>*\<^sup>* a b"
by (metis rtrancl_mono_proof sup.orderE sup2CI)

lemma state_upd_in_atomicsR[rule_format, OF _ refl refl]:
 "\<Gamma>\<turnstile> cf \<rightarrow> cf' \<Longrightarrow>
   cf = (c, Normal s) \<Longrightarrow>
   cf' = (c', Normal t) \<Longrightarrow>
       s \<noteq> t \<Longrightarrow> 
       ann_matches \<Gamma> \<Theta> a c \<Longrightarrow>
       s \<in> pre a \<Longrightarrow>
       (\<exists>p cm x. atomicsR \<Gamma> \<Theta> a c (p, cm) \<and> s \<in> p \<and>
       \<Gamma> \<turnstile> (cm, Normal s) \<rightarrow> (x, Normal t) \<and> final (x, Normal t))"
  apply (induct arbitrary: c c' s t a rule: step.induct, simp_all)
       apply clarsimp
       apply (erule  ann_matches.cases, simp_all)
       apply (rule exI)+
       apply (rule conjI)
        apply (rule atomicsR.intros)
        apply clarsimp
        apply (rule_tac x="Skip" in exI)
        apply (simp add: final_def)
        apply (rule step.Basic)
       apply clarsimp
       apply (erule  ann_matches.cases, simp_all)
       apply (rule exI)+
       apply (rule conjI)
        apply (rule atomicsR.intros)
        apply clarsimp
        apply (rule_tac x="Skip" in exI)
        apply (simp add: final_def)
        apply (erule step.Spec)
      apply clarsimp
      apply (erule  ann_matches.cases, simp_all)
      apply clarsimp        
      apply (drule meta_spec)+
      apply (erule meta_impE, rule conjI, (rule refl)+)+
      apply clarsimp
      apply (erule (1) meta_impE)
      apply (erule meta_impE, fastforce)
      apply clarsimp
      apply (rule exI)+
      apply (rule conjI)
      apply (erule AtSeqExpr1)
     apply fastforce
    apply clarsimp
    apply (erule  ann_matches.cases, simp_all)
    apply clarsimp        
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply clarsimp
    apply (erule (1) meta_impE)
    apply (erule meta_impE, fastforce)
    apply clarsimp
    apply (rule exI)+
    apply (rule conjI)
    apply (erule AtCatchExpr1)
    apply fastforce
    apply (erule  ann_matches.cases, simp_all)
    apply clarsimp
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply clarsimp
    apply (erule meta_impE)
     apply fastforce
    apply (erule meta_impE)
     apply (case_tac "i=0"; fastforce)
    apply clarsimp
    apply (rule exI)+
    apply (rule conjI)
     apply (erule AtParallelExprs)
    apply fastforce
   apply (drule_tac x=i in spec)
   apply clarsimp
   apply fastforce
  apply (erule ann_matches.cases, simp_all)
  apply clarsimp
  apply (rule exI)+
  apply (rule conjI)
   apply (rule AtAwait)
   apply clarsimp
   apply (rename_tac c' sa t aa e r ba)
   apply (rule_tac x=c' in exI)
   apply (rule conjI)
    apply (erule step.Await)
   apply (erule rtranclp_mono')
   apply clarsimp
   apply assumption+
   apply (simp add: final_def)
 done

lemma oghoare_atom_com_sound:
  "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>P a c Q,A \<Longrightarrow> atom_com c \<Longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q, A"
 unfolding valid_def 
  proof (induct rule: oghoare_seq_induct)
    case SeqSkip thus ?case 
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases(1))
  next
    case SeqThrow thus ?case
    by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases)
  next 
    case SeqBasic thus ?case 
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases 
            simp: final_def)
  next 
    case (SeqSpec \<Gamma> \<Theta> F r Q A) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE) 
     apply (clarsimp simp: final_def)
    apply (erule step_Normal_elim_cases)
     apply (fastforce elim!: converse_rtranclpE step_Normal_elim_cases)
    by clarsimp
  next
    case (SeqSeq \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 P\<^sub>2 A c\<^sub>2 Q) show ?case
     using SeqSeq
     by (fold valid_def) 
        (fastforce intro: oghoare_seq_valid simp: valid_weaken_pre)
   next 
    case (SeqCatch \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 Q P\<^sub>2 c\<^sub>2 A) thus ?case
    apply (fold valid_def)
    apply simp
    apply (fastforce elim:  oghoare_catch_valid)+
    done
   next 
    case (SeqCond \<Gamma> \<Theta> F P b c1 Q A c2) thus ?case
     by (fold valid_def)
        (fastforce intro:oghoare_if_valid)
   next 
    case (SeqWhile \<Gamma> \<Theta> F P c A b) thus ?case
     by (fold valid_def)
        (fastforce elim: valid_weaken_pre[rotated] oghoare_while_valid)
   next
    case (SeqGuard \<Gamma> \<Theta> F P c Q A r g f) thus ?case
    apply (fold valid_def)
    apply (simp (no_asm) add: valid_def)
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (fastforce simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply clarsimp
      apply (fastforce simp: valid_def)
     apply clarsimp
     apply (fastforce simp: valid_def)
    apply clarsimp
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply (fastforce dest: no_steps_final simp:final_def)
     apply (fastforce dest: no_steps_final simp:final_def)
   done
   next
    case (SeqCall \<Gamma> p f \<Theta> F P Q A) thus ?case
     by simp
   next

    case (SeqDynCom r fa \<Gamma> \<Theta> F P c Q A) thus ?case
    apply -
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
    apply clarsimp
    apply (rename_tac t c' x)

    apply (drule_tac x=x in spec)
    apply (drule_tac x=x in bspec, fastforce)
    apply clarsimp
    apply (drule_tac x="Normal x" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="c'" in spec)
    apply fastforce+
   done
   next 
    case (SeqConseq \<Gamma> \<Theta> F P c Q A) thus ?case 
     apply (clarsimp)
     apply (rename_tac t c' x)
     apply (erule_tac x="Normal x" in allE)
     apply (erule_tac x="t" in allE)
     apply (erule_tac x="c'" in allE)
     apply (clarsimp simp: pre_weaken_pre)
     apply force
    done
qed simp_all

lemma ParallelRuleAnn:
" length as = length cs \<Longrightarrow>
  \<forall>i<length cs. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F \<^esub>(pres (as ! i)) (cs ! i) (postcond (as ! i)),(abrcond (as ! i)) \<Longrightarrow>
  interfree \<Gamma> \<Theta> F as cs \<Longrightarrow>
  \<Inter>(set (map postcond as)) \<subseteq> Q \<Longrightarrow>
  \<Union>(set (map abrcond as)) \<subseteq> A \<Longrightarrow> \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F \<^esub>(AnnPar as) (Parallel cs) Q,A"
 apply (erule (3) Parallel)
 apply auto
done

lemma oghoare_step[rule_format, OF _ refl refl]:
shows
 "\<Gamma> \<turnstile> cf \<rightarrow> cf' \<Longrightarrow> cf = (c, Normal s) \<Longrightarrow> cf' = (c', Normal t) \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>a c Q,A \<Longrightarrow>
 s \<in> pre a \<Longrightarrow>
\<exists>a'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>a' c' Q,A \<and> t \<in> pre a' \<and>
        (\<forall>as. assertionsR \<Gamma> \<Theta> Q A a' c' as \<longrightarrow> assertionsR \<Gamma> \<Theta> Q A a c as) \<and>
        (\<forall>pm cm. atomicsR \<Gamma> \<Theta> a' c' (pm, cm) \<longrightarrow> atomicsR \<Gamma> \<Theta>  a c (pm, cm))"
 proof (induct arbitrary:c c' s a t Q A rule: step.induct)
  case (Parallel i cs s c' s' ca c'a sa a t Q A) thus ?case
     apply (clarsimp simp:)
     apply (drule oghoare_Parallel)
     apply clarsimp
     apply (rename_tac as)
     apply (frule_tac x=i in spec, erule (1) impE)
     apply (elim exE conjE)


     apply (drule meta_spec)+
     apply (erule meta_impE, rule conjI, (rule refl)+)+
     apply (erule meta_impE)
      apply (rule_tac P="(pres (as ! i))" in Conseq)
      apply (rule exI[where x="{}"])
      apply (rule_tac x="Q'" in exI)
      apply (rule_tac x="A'" in exI)
      apply (simp)
     apply (erule meta_impE, simp)
     apply clarsimp
     apply (rule_tac x="AnnPar (as[i:=(a',postcond(as!i), abrcond(as!i))])" in exI)
     apply (rule conjI)
      apply (rule ParallelRuleAnn, simp)
          apply clarsimp
          apply (rename_tac j)
          apply (drule_tac x=j in spec)
          apply clarsimp
          apply (case_tac "i = j")
           apply (clarsimp simp: )
           apply (rule Conseq)
           apply (rule exI[where x="{}"])
           apply (fastforce)
          apply (simp add: )
          apply (clarsimp simp: interfree_def)
          apply (rename_tac i' j')
          apply (drule_tac x=i' and y=j' in spec2)
          apply clarsimp
          apply (case_tac "i = i'")
           apply clarsimp
           apply (simp add: interfree_aux_def prod.case_eq_if )
          apply clarsimp
          apply (case_tac "j' = i")
           apply (clarsimp)
           apply (simp add: interfree_aux_def prod.case_eq_if)
           apply clarsimp
          apply (clarsimp)
         apply (erule subsetD)
         apply (clarsimp simp: in_set_conv_nth)
         apply (rename_tac a' x a b c i')
         apply (case_tac "i' = i")
          apply clarsimp
          apply (drule_tac x="(a', b, c)" in bspec, simp)
           apply (fastforce simp add: in_set_conv_nth)
          apply fastforce
         apply (drule_tac x="(a, b, c)" in bspec, simp)
          apply (simp add: in_set_conv_nth)
          apply (rule_tac x=i' in exI)
          apply clarsimp
         apply fastforce
     apply clarsimp
     apply (erule_tac A="(\<Union>x\<in>set as. abrcond x) " in  subsetD)
     apply (clarsimp simp: in_set_conv_nth)
     apply (rename_tac a b c j)
     apply (case_tac "j = i")
      apply clarsimp
      apply (rule_tac x="as!i" in bexI)
       apply simp
     apply clarsimp
    apply clarsimp
    apply (rule_tac x="(a,b,c)" in bexI)
     apply simp
    apply (clarsimp simp:in_set_conv_nth)
    apply (rule_tac x=j in exI)
    apply fastforce
   apply (rule conjI)
    apply (case_tac "s = Normal t")
     apply clarsimp
     apply (clarsimp simp: in_set_conv_nth)
     apply (rename_tac a b c j)
     apply (case_tac "j = i")
      apply clarsimp
     apply clarsimp
     apply (drule_tac x="as!j" in bspec)
      apply (clarsimp simp add: in_set_conv_nth)
      apply (rule_tac x=j in exI)
      apply fastforce
     apply clarsimp
    apply (frule state_upd_in_atomicsR, simp)
      apply (erule oghoare_imp_ann_matches)
     apply (clarsimp simp: in_set_conv_nth)
     apply fastforce
    apply (clarsimp simp: in_set_conv_nth)
    apply (rename_tac j)
    apply (case_tac "j = i")
     apply clarsimp
    apply clarsimp
    apply (thin_tac "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F \<^esub>a' c'  (postcond (as ! i)),(abrcond (as ! i))")
    apply (simp add: interfree_def interfree_aux_def)
    apply (drule_tac x="j" and y=i in spec2)
    apply (simp add: prod.case_eq_if)
    apply (drule spec2, drule (1) mp)
    apply clarsimp
    apply (case_tac "pre_par a")
     apply (subst pre_set)
     apply clarsimp
     apply (drule_tac x="as!j" in bspec) 
      apply (clarsimp simp: in_set_conv_nth)
      apply (rule_tac x=j in exI)
      apply fastforce
     apply clarsimp
     apply (frule (1) pre_imp_pre_set)
     apply (rename_tac as Q' A' a' a b c p cm x j X)
     apply (drule_tac x="X" in spec, erule_tac P="assertionsR \<Gamma> \<Theta> b c a (cs ! j) X" in impE)
      apply (rule ann_matches_imp_assertionsR')
       apply (drule_tac x=j in spec, clarsimp)
       apply (erule (1) oghoare_imp_ann_matches)
     apply (rename_tac a b c p cm x j X )
     apply (thin_tac "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (b \<inter> p) cm b,b")
     apply (thin_tac " \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (c \<inter> p) cm c,c")
     apply (simp add: valid_def)
     apply (drule_tac x="Normal sa" in spec)
     apply (drule_tac x="Normal t" in spec)
     apply (drule_tac x=x in spec)
     apply (erule impE, fastforce)
     apply force

   apply (drule_tac x=j in spec)
   apply clarsimp
   apply (rename_tac a b c p cm x j Q'' A'')
   apply (drule_tac x="pre a" in spec,erule impE, rule ann_matches_imp_assertionsR)
     apply (erule (1) oghoare_imp_ann_matches)
     apply (thin_tac " \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (b \<inter> p) cm b,b")
     apply (thin_tac " \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (c \<inter> p) cm c,c")
    apply (simp add: valid_def)
    apply (drule_tac x="Normal sa" in spec)
    apply (drule_tac x="Normal t" in spec)
    apply (drule_tac x=x in spec)
    apply (erule impE, fastforce)
    apply clarsimp
    apply (drule_tac x="as ! j" in bspec)
     apply (clarsimp simp: in_set_conv_nth)
     apply (rule_tac x=j in exI, fastforce)
    apply clarsimp
    apply fastforce
  apply (rule conjI)
    apply (clarsimp simp: )
    apply (erule assertionsR.cases ; simp)
      apply (clarsimp simp: )
      apply (rename_tac j a)
      apply (case_tac "j = i")
       apply clarsimp
       apply (drule_tac x=a in spec, erule (1) impE) 
       apply (erule (1)  AsParallelExprs)
      apply (subst (asm) nth_list_update_neq, simp)
      apply (erule_tac i=j in  AsParallelExprs)
      apply fastforce
     apply clarsimp
    apply (rule  AsParallelSkips)
    apply (clarsimp simp:)
    apply (rule equalityI)
     apply (clarsimp simp: in_set_conv_nth)
     apply (rename_tac a' x a b c j)
     apply (case_tac "j = i")
      apply (thin_tac "\<forall>a\<in>set as. sa \<in> precond a")
      apply clarsimp
      apply (drule_tac x="(a', b, c)" in bspec)
      apply (clarsimp simp: in_set_conv_nth)
      apply (rule_tac x="i" in exI)
      apply fastforce
     apply fastforce
    apply (drule_tac x="as ! j" in bspec)
     apply (clarsimp simp: in_set_conv_nth)
     apply (rule_tac x=j in exI)
     apply fastforce
   apply clarsimp
   apply (drule_tac x=" as ! j" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x=j in exI, fastforce)
    apply fastforce
   apply (clarsimp simp: in_set_conv_nth)
   apply (rename_tac x a b c j)
   apply (thin_tac "\<forall>a\<in>set as. sa \<in> precond a")
   apply (case_tac "j = i")
    apply clarsimp
    apply (drule_tac x="as!i" in bspec, fastforce)
    apply fastforce
   apply clarsimp
   apply (drule_tac x="as!j" in bspec)
   apply (clarsimp simp: in_set_conv_nth)
   apply (rule_tac x=j in exI, fastforce)
   apply fastforce
  apply clarsimp
  apply (erule atomicsR.cases ; simp)
  apply clarsimp
  apply (rename_tac j atc atp)
  apply (case_tac "j = i")
   apply clarsimp
   apply (drule_tac x=atc and y=atp in spec2, erule impE)
    apply (clarsimp)
   apply (erule (1)  AtParallelExprs)
  apply (subst (asm) nth_list_update_neq, simp)
  apply (erule_tac i=j in  AtParallelExprs)
  apply (clarsimp)
 done
next
 case (Basic f s c c' sa a t Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Basic)
  apply clarsimp
  apply (rule_tac x="AnnExpr Q" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule SkipRule)
   apply fastforce
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (drule assertionsR.cases, simp_all)
  apply (rule assertionsR.AsBasicSkip)
 done
next
  case (Spec s t r c c' sa a ta Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Spec)
  apply clarsimp
  apply (rule_tac x="AnnExpr Q" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule SkipRule)
   apply fastforce
  apply (rule conjI)
   apply force
  apply clarsimp
  apply (erule assertionsR.cases, simp_all)
  apply clarsimp
  apply (rule assertionsR.AsSpecSkip)
 done
next
  case (Guard s g f c ca c' sa a t Q A) thus ?case
  apply -
  apply clarsimp
  apply (drule oghoare_Guard)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
   by (fastforce dest: oghoare_Guard
                 intro:assertionsR.intros atomicsR.intros)
next
  case (GuardFault s g f c ca c' sa a t Q A) thus ?case
   by (fastforce dest: oghoare_Guard
                 intro:assertionsR.intros atomicsR.intros)
next
  case (Seq c\<^sub>1 s c\<^sub>1' s' c\<^sub>2 c c' sa a t A Q) thus ?case
    apply (clarsimp simp:)
    apply (drule oghoare_Seq)
    apply clarsimp
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply (erule meta_impE)
     apply (rule Conseq)
     apply (rule exI[where x="{}"])
     apply (rule exI)+
     apply (rule conjI)
      apply (simp)
     apply (erule (1) conjI)
    apply clarsimp
    apply (rule_tac x="AnnComp a' P\<^sub>2" in exI, rule conjI)
     apply (rule oghoare_oghoare_seq.Seq)
      apply (rule Conseq)
      apply (rule_tac x="{}" in exI)
      apply (fastforce)
     apply (rule Conseq)
     apply (rule_tac x="{}" in exI)
     apply (fastforce)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (erule assertionsR.cases, simp_all)
      apply clarsimp
      apply (drule_tac x=a in spec, simp)
      apply (erule AsSeqExpr1)
      apply clarsimp
     apply (erule AsSeqExpr2)
    apply clarsimp
    apply (erule atomicsR.cases, simp_all)
      apply clarsimp
      apply (drule_tac x="a" and y=b in spec2, simp)
      apply (erule AtSeqExpr1)
      apply clarsimp
     apply (erule AtSeqExpr2)
   done
next
  case (SeqSkip c\<^sub>2 s c c' sa a t Q A) thus ?case
   apply clarsimp
   apply (drule oghoare_Seq)
    apply clarsimp
    apply (rename_tac P\<^sub>1 P\<^sub>2 P' Q' A')
    apply (rule_tac x=P\<^sub>2 in exI)
    apply (rule conjI, rule Conseq)
     apply (rule_tac x="{}" in exI)
     apply (fastforce)
    apply (rule conjI)
     apply (drule oghoare_Skip)
     apply fastforce
    apply (rule conjI)
     apply clarsimp
    apply (erule assertionsR.AsSeqExpr2)
   apply clarsimp
   apply (fastforce intro: atomicsR.intros)
  done
next
  case (SeqThrow c\<^sub>2 s c c' sa a t Q A) thus ?case
   apply clarsimp
   apply (drule oghoare_Seq)
   apply clarsimp
   apply (rename_tac P\<^sub>1 P\<^sub>2 P' Q' A')
   apply (rule_tac x=P\<^sub>1 in exI)
   apply (drule oghoare_Throw)
   apply clarsimp
   apply (rename_tac P'')
   apply (rule conjI, rule Conseq)
    apply (rule_tac x="{}" in exI)
    apply (rule_tac x="Q'" in exI)
    apply (rule_tac x="P''" in exI)
    apply (fastforce intro: Throw)
   apply clarsimp
   apply (erule assertionsR.cases, simp_all)
   apply clarsimp
   apply (rule AsSeqExpr1)
   apply (rule AsThrow)
  done
next
  case (CondTrue s b c\<^sub>1 c\<^sub>2 c sa c' s' ann) thus ?case
   apply (clarsimp)
   apply (drule oghoare_Cond)
   apply clarsimp
   apply (rename_tac P' P\<^sub>1 P\<^sub>2 Q' A')
   apply (rule_tac x= P\<^sub>1 in exI)
   apply (rule conjI) 
    apply (rule Conseq, rule_tac x="{}" in exI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI)
    apply (fastforce elim: assertionsR.cases intro: AsCondExpr1)
   apply (fastforce elim: atomicsR.cases intro: AtCondExpr1)
  done
next
  case (CondFalse s b c\<^sub>1 c\<^sub>2 c sa c' s' ann) thus ?case
   apply (clarsimp)
   apply (drule oghoare_Cond)
   apply clarsimp
   apply (rename_tac P' P\<^sub>1 P\<^sub>2 Q' A')
   apply (rule_tac x= P\<^sub>2 in exI)
   apply (rule conjI) 
    apply (rule Conseq, rule_tac x="{}" in exI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI)
    apply (fastforce elim: assertionsR.cases intro: AsCondExpr2)
   apply (fastforce elim: atomicsR.cases intro: AtCondExpr2)
  done
next
  case (WhileTrue s b c ca sa c' s' ann) thus ?case
  apply clarsimp
  apply (frule oghoare_While)
  apply clarsimp
  apply (rename_tac r i P' A' Q')
  apply (rule_tac x="AnnComp P' (AnnWhile i i P')" in exI)
  apply (rule conjI)
   apply (rule Seq)
     apply (rule Conseq) 
     apply (rule_tac x="{}" in exI)
     apply (rule_tac x="i" in exI)
     apply (rule_tac x="A'" in exI)
     apply (subst weaken_pre_empty)
     apply clarsimp
    apply (rule While)
       apply (rule Conseq) 
       apply (rule_tac x="{}" in exI)
       apply (rule_tac x="i" in exI)
       apply (rule_tac x="A'" in exI)
       apply (subst weaken_pre_empty)
       apply clarsimp
      apply clarsimp
     apply force
    apply simp
   apply simp
  apply (rule conjI)
   apply blast
  apply (rule conjI)
   apply clarsimp
   apply (erule assertionsR.cases, simp_all)
    apply clarsimp
    apply (rule AsWhileExpr)
   apply clarsimp
   apply (erule assertionsR.cases,simp_all)
      apply clarsimp
      apply (erule AsWhileExpr)
     apply clarsimp
     apply (rule AsWhileInv)
    apply clarsimp
    apply (rule AsWhileInv)
   apply clarsimp
   apply (rule AsWhileSkip)
  apply clarsimp
  apply (erule atomicsR.cases, simp_all)
   apply clarsimp
   apply (rule AtWhileExpr)
  apply clarsimp+
  apply (erule atomicsR.cases, simp_all)
   apply clarsimp
  apply (erule AtWhileExpr)
  done
next
  case (WhileFalse s b c ca sa c' ann s' Q A) thus ?case
   apply clarsimp
   apply (drule oghoare_While)
   apply clarsimp
   apply (rule_tac x="AnnExpr Q" in exI)
   apply (rule conjI)
    apply (rule SkipRule)
    apply blast
   apply (rule conjI)
    apply fastforce
   apply clarsimp
   apply (erule assertionsR.cases, simp_all)
   apply (drule sym, simp, rule AsWhileSkip)
  done
next
  case (Call p bs s c c' sa a t Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Call)
  apply clarsimp
  apply (rename_tac n as)
  apply (rule_tac x="as ! n" in exI)
  apply clarsimp
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply clarsimp
   apply (erule (2) AsCallExpr)
   apply fastforce
  apply clarsimp
  apply (erule (2) AtCallExpr)
  apply simp
 done
next
  case (DynCom c s ca c' sa a t Q A) thus ?case
  apply -
  apply clarsimp
  apply (drule oghoare_DynCom)
  apply clarsimp
  apply (drule_tac x=t in bspec, assumption)
  apply (rule exI)
  apply (erule conjI)
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply clarsimp
   apply (erule (1) AsDynComExpr)
  apply (clarsimp)
  apply (erule (1) AtDynCom)
  done
next
  case (Catch c\<^sub>1 s c\<^sub>1' s' c\<^sub>2 c c' sa a t Q A) thus ?case
    apply (clarsimp simp:)
    apply (drule oghoare_Catch)
    apply clarsimp
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply (erule meta_impE)
     apply (rule Conseq)
     apply (rule exI[where x="{}"])
     apply (rule exI)+
     apply (rule conjI)
      apply (simp)
     apply (erule (1) conjI)
    apply clarsimp
    apply (rename_tac P\<^sub>1 P\<^sub>2 P' Q' A' a')
    apply (rule_tac x="AnnComp a' P\<^sub>2" in exI, rule conjI)
     apply (rule oghoare_oghoare_seq.Catch)
      apply (rule Conseq)
      apply (rule_tac x="{}" in exI)
      apply (fastforce)
     apply (rule Conseq)
     apply (rule_tac x="{}" in exI)
     apply (fastforce)
    apply clarsimp
   apply (rule conjI)
    apply clarsimp
     apply (erule assertionsR.cases, simp_all)
      apply clarsimp
      apply (rename_tac a)
      apply (drule_tac x=a in spec, simp)
      apply (erule AsCatchExpr1)
     apply clarsimp
     apply (erule AsCatchExpr2)
    apply clarsimp
    apply (erule atomicsR.cases, simp_all)
      apply clarsimp
      apply (rename_tac a b a2)
      apply (drule_tac x="a" and y=b in spec2, simp)
      apply (erule AtCatchExpr1)
      apply clarsimp
     apply (erule AtCatchExpr2)
   done
next
  case (CatchSkip c\<^sub>2 s c c' sa a t Q A) thus ?case
   apply clarsimp
   apply (drule oghoare_Catch, clarsimp)
   apply (rename_tac P\<^sub>1 P\<^sub>2 P' Q' A')
   apply (rule_tac x=P\<^sub>1 in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule Conseq)
    apply (rule_tac x="{}" in exI)
    apply (drule oghoare_Skip)
    apply clarsimp
    apply (rule_tac x=Q' in exI)
    apply (rule_tac x=A' in exI)
    apply (rule conjI, erule SkipRule)
    apply clarsimp
   apply clarsimp
   apply (rule AsCatchExpr1)
   apply (erule assertionsR.cases, simp_all)
   apply (rule assertionsR.AsSkip)
  done
next
  case (CatchThrow c\<^sub>2 s c c' sa a t Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Catch, clarsimp)
  apply (rename_tac P\<^sub>1 P\<^sub>2 P' Q' A')
  apply (rule_tac x=P\<^sub>2 in exI)
  apply (rule conjI)
   apply (rule Conseq)
   apply (rule_tac x="{}" in exI)
   apply (fastforce )
  apply (rule conjI)
   apply (drule oghoare_Throw)
   apply clarsimp
   apply fastforce
  apply (rule conjI)
   apply (clarsimp)
   apply (erule AsCatchExpr2)
  apply clarsimp
  apply (erule AtCatchExpr2)
 done
next
 case (ParSkip cs s c c' sa a t Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Parallel)
  apply clarsimp
  apply (rename_tac as)
    
  apply (rule_tac x="AnnExpr (\<Inter>x\<in>set as. postcond x)" in exI)
  apply (rule conjI, rule SkipRule)
   apply blast
  apply (rule conjI)
   apply simp
    apply clarsimp
    apply (simp only: in_set_conv_nth)
    apply clarsimp
    apply (drule_tac x="i" in spec)
    apply clarsimp
    apply (drule_tac x="cs!i" in bspec)
     apply clarsimp
    apply clarsimp
    apply (drule oghoare_Skip)
    apply clarsimp
    apply (drule_tac x="as!i" in bspec)
     apply (clarsimp simp: in_set_conv_nth)
     apply (rule_tac x=i in exI, fastforce)
     apply clarsimp
     apply blast
  apply clarsimp
  apply (erule assertionsR.cases; simp)
  apply clarsimp
  apply (rule AsParallelSkips; clarsimp)
 done
next
 case (ParThrow cs s c c' sa a t Q A) thus ?case
  apply clarsimp
  apply (drule oghoare_Parallel)
  apply (clarsimp simp: in_set_conv_nth)  
  apply (drule_tac x=i in spec)
  apply clarsimp
  apply (drule oghoare_Throw)
  apply clarsimp
  apply (rename_tac i as Q' A' P')
  apply (rule_tac x="AnnExpr P'" in exI)
  apply (rule conjI)
   apply (rule ThrowRule)
   apply clarsimp
   apply (erule_tac A="(\<Union>x\<in>set as. abrcond x)" in subsetD[where B=A], force)
  apply (rule conjI)
   apply (drule_tac x="as!i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x=i in exI, fastforce)
   apply (fastforce)
  apply clarsimp
  apply (erule AsParallelExprs)
  apply clarsimp
  apply (erule assertionsR.cases, simp_all)
  apply (rule AsThrow)
 done
next
 case (Await x b c c' x' c'' c''' x'' a x''' Q A) thus ?case
   apply (clarsimp)
   apply (drule oghoare_Await)
   apply clarsimp

   apply (drule rtranclp_conjD)
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (rename_tac P' Q' A')
    apply (rule_tac x="AnnExpr Q" in exI)
    apply clarsimp
    apply (rule conjI)
     apply (rule Skip)
    apply (rule conjI)
     apply (drule (1) oghoare_atom_com_sound)
     apply (fastforce simp: final_def valid_def)
    apply clarsimp
    apply (erule assertionsR.cases, simp_all)
    apply clarsimp
    apply (rule AsAwaitSkip)

   apply (rule_tac x="AnnExpr A" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule Throw)
    apply (rule conjI)
     apply (drule (1) oghoare_atom_com_sound)
     apply (fastforce simp: final_def valid_def)
    apply clarsimp
    apply (erule assertionsR.cases, simp_all)
    apply clarsimp
    apply (rule AsAwaitThrow)
  done
qed simp_all

lemma oghoare_steps[rule_format, OF _ refl refl]:
 "\<Gamma> \<turnstile> cf \<rightarrow>\<^sup>* cf' \<Longrightarrow> cf = (c, Normal s) \<Longrightarrow> cf' = (c', Normal t) \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>a c Q,A \<Longrightarrow>
 s \<in> pre a \<Longrightarrow>
\<exists>a'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>a' c' Q,A \<and> t \<in> pre a' \<and>
        (\<forall>as. assertionsR \<Gamma> \<Theta> Q A a' c' as \<longrightarrow> assertionsR \<Gamma> \<Theta> Q A a c as) \<and>
        (\<forall>pm cm. atomicsR \<Gamma> \<Theta> a' c' (pm, cm) \<longrightarrow> atomicsR \<Gamma> \<Theta> a c (pm, cm))"
  apply (induct arbitrary: a c s c' t rule: converse_rtranclp_induct)
   apply fastforce
  apply clarsimp
  apply (frule Normal_pre_star)
  apply clarsimp
  apply (drule (2) oghoare_step)
  apply clarsimp
  apply ((drule meta_spec)+, (erule meta_impE, rule conjI, (rule refl)+)+)
  apply (erule (1) meta_impE)+
  apply clarsimp
  apply (rule exI)
  apply (rule conjI, fastforce)+
  apply force
 done

lemma oghoare_sound_Parallel_Normal_case[rule_format, OF _ refl refl]:
 "\<Gamma> \<turnstile> (c, s) \<rightarrow>\<^sup>* (c', t) \<Longrightarrow>
   \<forall>P x y cs. c = Parallel cs  \<longrightarrow> s = Normal x \<longrightarrow>
      t = Normal y \<longrightarrow>
      \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<longrightarrow> final (c', t) \<longrightarrow>
       x \<in> pre P \<longrightarrow> t \<notin> Fault ` F \<longrightarrow> (c' = Throw \<and> t \<in> Normal ` A) \<or> (c' = Skip \<and> t \<in> Normal ` Q)"
  apply(erule converse_rtranclp_induct2)
   apply (clarsimp simp: final_def)
  apply(erule step.cases, simp_all)
\<comment> \<open>Parallel\<close>
    apply clarsimp
    apply (frule Normal_pre_star)
    apply (drule oghoare_Parallel)
    apply clarsimp
    apply (rename_tac i cs c1' x y  s' as)
    apply (subgoal_tac "\<Gamma>\<turnstile> (Parallel cs, Normal x) \<rightarrow> (Parallel (cs[i := c1']), Normal s')")
     apply (frule_tac c="Parallel cs" and
                      a="AnnPar as"  and
                      Q="(\<Inter>x\<in>set as. postcond x)" and A ="(\<Union>x\<in>set as. abrcond x)"
                   in oghoare_step[where \<Theta>=\<Theta> and F=F])
       apply(rule Parallel, simp)
          apply clarsimp
          apply (rule Conseq, rule exI[where x="{}"], fastforce)
         apply clarsimp
        apply force
       apply force
      apply clarsimp
     apply clarsimp
     apply (rename_tac a')
     apply (drule_tac x=a' in spec)
     apply (drule mp, rule Conseq)
      apply (rule_tac x="{}" in exI)
      apply (rule_tac x="(\<Inter>x\<in>set as. postcond x)" in exI)
      apply (rule_tac x="(\<Union>x\<in>set as. abrcond x)" in exI)
      apply (simp)
     apply clarsimp
    apply(erule (1) step.Parallel)
\<comment> \<open>ParSkip\<close>
   apply (frule no_steps_final, simp add: final_def)
   apply clarsimp
   apply (drule oghoare_Parallel)
   apply clarsimp
   apply (rule imageI)
   apply (erule subsetD)
   apply clarsimp
   apply (clarsimp simp: in_set_conv_nth)
   apply (rename_tac i)
   apply (frule_tac x="i" in spec)
   apply clarsimp
   apply (frule_tac x="cs!i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x="i" in exI)
    apply clarsimp
   apply clarsimp
   apply (drule_tac x="as ! i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply fastforce
   apply (drule oghoare_Skip)
   apply fastforce
\<comment> \<open>ParThrow\<close>
  apply clarsimp
  apply (frule no_steps_final, simp add: final_def)
  apply clarsimp
  apply (drule oghoare_Parallel)
  apply (clarsimp simp: in_set_conv_nth)
  apply (drule_tac x=i in spec)
  apply clarsimp
  apply (drule oghoare_Throw)
  apply clarsimp
  apply (rename_tac i as Q' A' P')
  apply (drule_tac x="as ! i" in bspec)
   apply (clarsimp simp: in_set_conv_nth)
   apply (rule_tac x=i in exI, fastforce)
  apply clarsimp
  apply (rule imageI)
  apply (erule_tac  A="(\<Union>x\<in>set as. abrcond x)" in subsetD)
  apply clarsimp
  apply (rule_tac x="as!i" in bexI)
   apply blast
  apply clarsimp
  done

lemma oghoare_step_Fault[rule_format, OF _ refl refl]:
 "\<Gamma>\<turnstile> cf \<rightarrow> cf' \<Longrightarrow>
   cf = (c, Normal x) \<Longrightarrow>
   cf' = (c', Fault f) \<Longrightarrow>
   x \<in> pre P \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<Longrightarrow> f \<in> F"
  apply (induct arbitrary: x c c' P Q A f rule: step.induct, simp_all)
       apply clarsimp
       apply (drule oghoare_Guard)
       apply clarsimp
       apply blast
      apply clarsimp
      apply (drule oghoare_Seq)
      apply clarsimp
     apply clarsimp
     apply (drule oghoare_Catch)
     apply clarsimp
    apply clarsimp
    apply (rename_tac i cs c' x P Q A f)
    apply (drule oghoare_Parallel)
    apply clarsimp
    apply (rename_tac i cs c' x Q A f as)
    apply (drule_tac x="i" in spec)
    apply clarsimp
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply (drule_tac x="as!i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x="i" in exI, fastforce)
   apply (erule (1) meta_impE)
   apply (erule (2) meta_impE)
  apply clarsimp
  apply (drule rtranclp_conjD[THEN conjunct1])
  apply (drule oghoare_Await)
  apply clarsimp
  apply (rename_tac b c c' x Q A f r P' Q' A')
  apply (drule (1) oghoare_atom_com_sound)
  apply (simp add: valid_def)
  apply (drule_tac x="Normal x" in spec)
  apply (drule_tac x="Fault f" in spec)
  apply (drule_tac x=Skip in spec)
  apply clarsimp
  apply (erule impE)
   apply (cut_tac f=f and c=c' in  steps_Fault[where \<Gamma>=\<Gamma>])
   apply fastforce
   apply (fastforce simp: final_def steps_Fault)
 done

lemma oghoare_step_Stuck[rule_format, OF _ refl refl]:
 "\<Gamma>\<turnstile> cf \<rightarrow> cf' \<Longrightarrow>
   cf = (c, Normal x) \<Longrightarrow>
   cf' = (c', Stuck) \<Longrightarrow>
   x \<in> pre P \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<Longrightarrow> P'"
  apply (induct arbitrary: x c c' P Q A  rule: step.induct, simp_all)
         apply clarsimp
         apply (drule oghoare_Spec)
         apply force
        apply clarsimp
       apply (drule oghoare_Seq)
       apply clarsimp
      apply clarsimp
      apply (drule oghoare_Call)
      apply clarsimp
     apply clarsimp
     apply (drule oghoare_Catch)
     apply clarsimp
    apply clarsimp
    apply (drule oghoare_Parallel)
    apply clarsimp
    apply (rename_tac i cs c' x Q A as)
    apply (drule_tac x="i" in spec)
    apply clarsimp
    apply (drule meta_spec)+
    apply (erule meta_impE, rule conjI, (rule refl)+)+
    apply (drule_tac x="as!i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x="i" in exI, fastforce)
    apply (erule  meta_impE[OF _ refl])
    apply (erule (1) meta_impE)
    apply (erule (2) meta_impE)
   apply clarsimp
   apply (drule rtranclp_conjD[THEN conjunct1])
   apply (drule oghoare_Await)
   apply clarsimp
   apply (rename_tac b c c' x Q A  r P'' Q' A')
  apply (drule (1) oghoare_atom_com_sound)
  apply (simp add: valid_def)
  apply (drule_tac x="Normal x" in spec)
  apply (drule_tac x=Stuck in spec)
  apply (drule_tac x=Skip in spec)
  apply clarsimp
  apply (erule impE)
   apply (cut_tac c=c' in  steps_Stuck[where \<Gamma>=\<Gamma>])
   apply fastforce
   apply (fastforce simp: final_def steps_Fault)
  apply clarsimp
  apply (drule oghoare_Await)
  apply clarsimp
 done

lemma oghoare_steps_Fault[rule_format, OF _ refl refl]:
 "\<Gamma>\<turnstile> cf \<rightarrow>\<^sup>* cf' \<Longrightarrow>
   cf = (c, Normal x) \<Longrightarrow>
   cf' = (c', Fault f) \<Longrightarrow>
   x \<in> pre P \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<Longrightarrow> f \<in> F"
  apply (induct arbitrary: x c c' f rule: rtranclp_induct)
   apply fastforce
  apply clarsimp
  apply (rename_tac b x c c' f)
  apply (case_tac b)
    apply clarsimp
    apply (drule (2) oghoare_steps)
    apply clarsimp
    apply (drule (3) oghoare_step_Fault)
   apply clarsimp
   apply (drule meta_spec)+
   apply (erule meta_impE, (rule conjI, (rule refl)+))+
    apply simp
   apply (drule step_Fault_prop ; simp)
   apply simp
  apply clarsimp
  apply (drule step_Stuck_prop ; simp)
 done

lemma oghoare_steps_Stuck[rule_format, OF _ refl refl]:
 "\<Gamma>\<turnstile> cf \<rightarrow>\<^sup>* cf' \<Longrightarrow>
   cf = (c, Normal x) \<Longrightarrow>
   cf' = (c', Stuck) \<Longrightarrow>
   x \<in> pre P \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<Longrightarrow> P'"
  apply (induct arbitrary: x c c' rule: rtranclp_induct)
   apply fastforce
  apply clarsimp
  apply (rename_tac b x c c')
  apply (case_tac b)
    apply clarsimp
    apply (drule (2) oghoare_steps)
    apply clarsimp
    apply (drule (3) oghoare_step_Stuck)
   apply clarsimp
   apply (drule meta_spec)+
   apply (erule meta_impE, (rule conjI, (rule refl)+))+
    apply simp
   apply (drule step_Fault_prop ; simp)
   apply simp
 done

lemma oghoare_sound_Parallel_Fault_case[rule_format, OF _ refl refl]:
 "\<Gamma> \<turnstile> (c, s) \<rightarrow>\<^sup>* (c', t) \<Longrightarrow>
   \<forall>P x f cs. c = Parallel cs  \<longrightarrow> s = Normal x \<longrightarrow>
      x \<in> pre P \<longrightarrow> t = Fault f \<longrightarrow>
      \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A \<longrightarrow> final (c', t) \<longrightarrow>
      f \<in> F"
  apply(erule converse_rtranclp_induct2)
   apply (clarsimp simp: final_def)
  apply clarsimp

  apply (rename_tac c s P x f cs)
  apply (case_tac s)
    apply clarsimp

    apply(erule step.cases, simp_all)
         apply (clarsimp simp: final_def)
         apply (drule oghoare_Parallel)
         apply clarsimp
         apply (rename_tac x f s' i cs c1' as)
         apply (subgoal_tac "\<Gamma>\<turnstile> (Parallel cs, Normal x) \<rightarrow> (Parallel (cs[i := c1']), Normal s')")
         apply (frule_tac c="Parallel cs" and a="AnnPar as"  and
                      Q="(\<Inter>x\<in>set as. postcond x)" and A="(\<Union>x\<in>set as. abrcond x)" 
                      in oghoare_step[where \<Theta>=\<Theta> and F=F])
          apply(rule Parallel)
               apply simp
              apply clarsimp
              apply (rule Conseq, rule exI[where x="{}"], fastforce)
             apply assumption
            apply clarsimp
           apply clarsimp
          apply simp
         apply clarsimp
        apply (rename_tac a')
        apply (drule_tac x=a' in spec)
        apply clarsimp
        apply (erule notE[where P="oghoare _ _ _ _ _ _ _"])
        apply (rule Conseq, rule exI[where x="{}"])
        apply (clarsimp)
        apply (rule_tac x="(\<Inter>x\<in>set as. postcond x)" in exI)
        apply (rule_tac x="(\<Union>x\<in>set as. abrcond x)" in exI ; simp)
       apply(erule (1) step.Parallel)
      apply clarsimp
      apply (fastforce dest: no_steps_final simp: final_def)+
   apply (clarsimp simp: final_def)
   apply (drule oghoare_Parallel)
   apply (erule step_Normal_elim_cases, simp_all)
    apply clarsimp
    apply (rename_tac f cs f' i c1' as)
   apply (drule_tac x="i" in spec)
   apply (erule  impE, fastforce)
   apply clarsimp
   apply (drule_tac x="as!i" in bspec)
    apply (clarsimp simp: in_set_conv_nth)
    apply (rule_tac x="i" in exI, fastforce)
   apply (drule_tac P="pres (as ! i)" in  oghoare_step_Fault[where \<Theta>=\<Theta> and F=F])
     apply assumption+
   apply (drule steps_Fault_prop ; simp)
   apply simp
  apply (drule steps_Stuck_prop ;simp)
 done

lemma oghoare_soundness:
  "(\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (pre P) c Q, A) \<and>
   (\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>P' P c Q,A \<longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P' c Q, A)"
  unfolding valid_def
  proof (induct rule: oghoare_oghoare_seq.induct)
    case SeqSkip thus ?case 
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases(1))
  next
    case SeqThrow thus ?case
    by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases)
  next 
    case SeqBasic thus ?case 
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases 
            simp: final_def)
  next 
    case (SeqSpec \<Gamma> \<Theta> F r Q A) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE) 
     apply (clarsimp simp: final_def)
    apply (erule step_Normal_elim_cases)
     apply (fastforce elim!: converse_rtranclpE step_Normal_elim_cases)
    by clarsimp
  next
    case (SeqSeq \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 P\<^sub>2 A c\<^sub>2 Q) show ?case
     using SeqSeq
     by (fold valid_def) 
        (fastforce intro: oghoare_seq_valid simp: valid_weaken_pre)
  next 
    case (SeqCatch \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 Q P\<^sub>2 c\<^sub>2 A) thus ?case
    by (fold valid_def)
       (fastforce elim:  oghoare_catch_valid)+
  next 
    case (SeqCond \<Gamma> \<Theta> F P b c1 Q A c2) thus ?case
     by (fold valid_def)
        (fastforce intro:oghoare_if_valid)
  next 
    case (SeqWhile \<Gamma> \<Theta> F P c A b) thus ?case
     by (fold valid_def)
        (fastforce elim: valid_weaken_pre[rotated] oghoare_while_valid)
  next
    case (SeqGuard \<Gamma> \<Theta> F P c Q A r g f) thus ?case
    apply (fold valid_def)
    apply (simp (no_asm) add: valid_def)
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (fastforce simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply clarsimp
      apply (fastforce simp: valid_def)
     apply clarsimp
     apply (fastforce simp: valid_def)
    apply clarsimp
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply (fastforce dest: no_steps_final simp:final_def)
     apply (fastforce dest: no_steps_final simp:final_def)
   done
  next
    case (SeqCall \<Gamma> p f \<Theta> F P Q A) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp add: final_def)
    apply (erule step_Normal_elim_cases)
     apply (clarsimp simp: final_def)
     apply fastforce
    apply fastforce
   done
  next
    case (SeqDynCom r P fa \<Gamma> \<Theta> F c Q A) thus ?case
    apply -
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
    apply clarsimp
    apply (rename_tac t c' x)
    apply (drule_tac x=x in bspec, fastforce)
    apply clarsimp
    apply (drule_tac x="Normal x" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="c'" in spec)
    apply fastforce+
   done
   next 
    case (SeqConseq \<Gamma> \<Theta> F P c Q A) thus ?case 
     apply (clarsimp)
     apply (rename_tac t c' x)
     apply (erule_tac x="Normal x" in allE)
     apply (erule_tac x="t" in allE)
     apply (erule_tac x="c'" in allE)
     apply (clarsimp simp: pre_weaken_pre)
     apply force
    done
  next
    case (SeqParallel as P \<Gamma> \<Theta> F cs Q A) thus ?case
    by (fold valid_def)
       (erule (1) valid_weaken_pre)
  next
    case (Call \<Theta> p as n P Q A r \<Gamma> f F) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp add: final_def)
    apply (erule step_Normal_elim_cases)
    apply (clarsimp simp: final_def)
     apply (erule disjE)
     apply clarsimp
      apply fastforce
     apply fastforce
    apply fastforce
   done
   next 
    case (Await \<Gamma> \<Theta> F P c Q A r b) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp add: final_def)
    apply (erule step_Normal_elim_cases)
       apply (erule converse_rtranclpE)
        apply (fastforce simp add: final_def )
       apply (force dest!:no_step_final simp: final_def)
      apply clarsimp
      apply (rename_tac x c'')
      apply (drule_tac x="Normal x" in spec)
      apply (drule_tac x="Stuck" in spec)
      apply (drule_tac x="Skip" in spec)
      apply (clarsimp simp: final_def)
      apply (erule impE[where P="rtranclp _ _ _"])
       apply (cut_tac c="c''" in  steps_Stuck[where \<Gamma>=\<Gamma>])
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (rename_tac x c'' f)
     apply (drule_tac x="Normal x" in spec)
     apply (drule_tac x="Fault f" in spec)
     apply (drule_tac x="Skip" in spec)
     apply (erule impE[where P="rtranclp _ _ _"])
      apply (cut_tac c="c''" and f=f in  steps_Fault[where \<Gamma>=\<Gamma>])
      apply fastforce
     apply clarsimp
     apply (erule converse_rtranclpE)
       apply fastforce
     apply (erule step_elim_cases)
    apply (fastforce)
   done
   next 
    case (Parallel as cs \<Gamma> \<Theta> F Q A ) thus ?case
    apply (fold valid_def)
    apply (simp only:pre.simps)
    apply (simp (no_asm) only: valid_def)
    apply clarsimp
    apply (rename_tac t c' x')
    apply (case_tac t)
      apply clarsimp
      apply (drule oghoare_sound_Parallel_Normal_case[where \<Theta>=\<Theta> and Q=Q and A=A and F=F and P="AnnPar as", OF _ refl])
          apply (rule oghoare_oghoare_seq.Parallel)
              apply simp
             apply clarsimp
            apply assumption
           apply (clarsimp)
          apply clarsimp
         apply (clarsimp simp: final_def)
        apply (clarsimp )
       apply clarsimp
      apply clarsimp
     apply (drule oghoare_sound_Parallel_Fault_case[where \<Theta>=\<Theta> and Q=Q and A=A and F=F and P="AnnPar as", OF _ ])
         apply clarsimp
        apply assumption
        apply (rule oghoare_oghoare_seq.Parallel)
            apply simp
           apply clarsimp
          apply assumption
         apply clarsimp
        apply clarsimp
       apply (simp add: final_def)
      apply (fastforce simp add: final_def)
     apply (clarsimp simp: final_def)
     apply (erule  oghoare_steps_Stuck[where \<Theta>=\<Theta> and F=F and Q=Q and A=A and P="AnnPar as"])
      apply simp
     apply (rule  oghoare_oghoare_seq.Parallel)
         apply simp
        apply simp
       apply simp
      apply clarsimp
     apply clarsimp
    done
  next
    case Skip thus ?case
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases(1))
  next 
    case Basic thus ?case 
      by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases 
            simp: final_def)
  next 
    case (Spec \<Gamma> \<Theta> F r Q A) thus ?case
    apply clarsimp
    apply (erule converse_rtranclpE) 
     apply (clarsimp simp: final_def)
    apply (erule step_Normal_elim_cases)
     apply (fastforce elim!: converse_rtranclpE step_Normal_elim_cases)
    by clarsimp
  next
    case (Seq \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 P\<^sub>2 A c\<^sub>2 Q) show ?case
     using Seq
     by (fold valid_def) 
        (fastforce intro: oghoare_seq_valid simp: valid_weaken_pre)
   next 
    case (Cond \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 Q A P\<^sub>2 c\<^sub>2 r b) thus ?case
     by (fold valid_def)
        (fastforce intro:oghoare_if_valid)
   next 
    case (While \<Gamma> \<Theta> F P c i A b Q r) thus ?case
     by (fold valid_def)
        (fastforce elim: valid_weaken_pre[rotated] oghoare_while_valid)
   next 
    case Throw thus ?case
    by (fastforce 
            elim: converse_rtranclpE step_Normal_elim_cases)
   next 
    case (Catch \<Gamma> \<Theta> F P\<^sub>1 c\<^sub>1 Q P\<^sub>2 c\<^sub>2 A) thus ?case
    apply (fold valid_def)
    apply (fastforce elim: oghoare_catch_valid)+
    done
   next 
    case (Guard \<Gamma> \<Theta> F P c Q A r g f) thus ?case
    apply (fold valid_def)
    apply (simp)
    apply (frule (1) valid_weaken_pre[rotated])
    apply (simp (no_asm) add: valid_def)
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (fastforce simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply clarsimp
      apply (fastforce simp: valid_def)
     apply clarsimp
     apply (fastforce simp: valid_def)
    apply clarsimp
     apply (case_tac "r \<inter> - g \<noteq> {}")
      apply clarsimp
      apply (fastforce dest: no_steps_final simp:final_def)
     apply (clarsimp simp: ex_in_conv[symmetric])
    done
   next 
    case (DynCom r \<Gamma> \<Theta> F P c Q A) thus ?case
   
    apply clarsimp
    apply (erule converse_rtranclpE)
     apply (clarsimp simp: final_def)
    apply clarsimp
    apply (erule step_Normal_elim_cases)
    apply clarsimp
    apply (rename_tac t c' x)
    apply (erule_tac x=x in ballE)
    apply clarsimp
    apply (drule_tac x="Normal x" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="c'" in spec)
    
    apply fastforce+
   done
   next 
    case (Conseq \<Gamma> \<Theta> F P c Q A) thus ?case 
     apply (clarsimp)
     apply (rename_tac P' Q' A' t c' x)
     apply (erule_tac x="Normal x" in allE)
     apply (erule_tac x="t" in allE)
     apply (erule_tac x="c'" in allE)
     apply (clarsimp simp: pre_weaken_pre)
     apply force
    done   
qed

lemmas oghoare_sound = oghoare_soundness[THEN conjunct1, rule_format]
lemmas oghoare_seq_sound = oghoare_soundness[THEN conjunct2, rule_format]

end
