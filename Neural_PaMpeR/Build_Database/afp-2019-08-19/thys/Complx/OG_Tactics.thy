(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Verfication Condition Generator for COMPLX OG\<close>
theory OG_Tactics
imports
 OG_Soundness
 "lib/Cache_Tactics"
begin

subsection \<open>Seq oghoare derivation\<close>


lemmas SeqSkipRule = SeqSkip
lemmas SeqThrowRule = SeqThrow
lemmas SeqBasicRule = SeqBasic
lemmas SeqSpecRule = SeqSpec
lemmas SeqSeqRule = SeqSeq

lemma SeqCondRule: 
 "\<lbrakk>  \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> C1 P\<^sub>1 c\<^sub>1 Q,A;
    \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> C2 P\<^sub>2 c\<^sub>2 Q,A \<rbrakk>
   \<Longrightarrow> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> {s. (s\<in>b \<longrightarrow> s\<in>C1) \<and> (s\<notin>b \<longrightarrow> s\<in>C2)} (AnnBin r P\<^sub>1 P\<^sub>2)
                   (Cond b c\<^sub>1 c\<^sub>2) Q,A"
  apply (rule SeqCond)
   apply (erule SeqConseq[rotated]; clarsimp)
  apply (erule SeqConseq[rotated]; clarsimp)
  done

lemma SeqWhileRule:
  "\<lbrakk> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> (i \<inter> b) a c i,A; i \<inter> - b \<subseteq> Q \<rbrakk>
   \<Longrightarrow> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> i (AnnWhile r i a) (While b c) Q,A"
  apply (rule SeqConseq[OF _ SeqWhile])
     prefer 2 apply assumption
    by simp+ 

lemma DynComRule:
 "\<lbrakk> r \<subseteq> pre a;  \<And>s. s\<in>r \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> a (c s) Q,A \<rbrakk> \<Longrightarrow> 
      \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r a) (DynCom c) Q,A"
  by (erule DynCom) clarsimp

lemma SeqDynComRule:
 "\<lbrakk>r \<subseteq> pre a;
   \<And>s. s\<in>r \<Longrightarrow> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>P a (c s) Q,A;
      P\<subseteq>r \<rbrakk> \<Longrightarrow> 
  \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnRec r a) (DynCom c) Q,A"
  by (erule SeqDynCom) clarsimp

lemma SeqCallRule:
  "\<lbrakk> P' \<subseteq> P; \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P P'' f Q,A; 
     n < length as; \<Gamma> p = Some f;
     as ! n = P''; \<Theta> p = Some as\<rbrakk>
   \<Longrightarrow> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P' (AnnCall r n) (Call p) Q,A"
  by (simp add: SeqCall SeqConseq)

lemma SeqGuardRule:
  "\<lbrakk> P \<inter> g \<subseteq> P'; P \<inter> -g \<noteq> {} \<Longrightarrow> f \<in> F;
     \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P' a c Q,A \<rbrakk> \<Longrightarrow>
   \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnRec r a) (Guard f g c) Q,A"
  by (simp add: SeqGuard SeqConseq)

subsection \<open>Parallel-mode rules\<close>

lemma GuardRule:
  "\<lbrakk> r \<inter> g \<subseteq> pre P; r \<inter> -g \<noteq> {} \<longrightarrow> f \<in> F;
     \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A \<rbrakk> \<Longrightarrow>
   \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r P) (Guard f g c) Q,A"
  by (simp add: Guard)

lemma CallRule:
  "\<lbrakk> r \<subseteq> pre P; \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P f Q,A;
     n < length as; \<Gamma> p = Some f;
     as ! n = P; \<Theta> p = Some as\<rbrakk>
   \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnCall r n) (Call p) Q,A"
  by (simp add: Call)

definition map_ann_hoare :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set
              \<Rightarrow> ('s, 'p, 'f) ann_triple list \<Rightarrow> ('s,'p,'f) com list \<Rightarrow> bool"
    ("(4_,_/[\<tturnstile>]\<^bsub>'/_ \<^esub>(_/ (_)))" [60,60,60,1000,20]60) where
  "\<Gamma>, \<Theta> [\<tturnstile>]\<^bsub>/F\<^esub> Ps Ts \<equiv> \<forall>i < length Ts. \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (pres (Ps!i)) (Ts!i) (postcond (Ps!i)), (abrcond (Ps!i))"

lemma MapAnnEmpty: "\<Gamma>, \<Theta> [\<tturnstile>]\<^bsub>/F\<^esub> [] []"
 by(simp add:map_ann_hoare_def)

lemma MapAnnList: "\<lbrakk> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q, A;
                     \<Gamma>, \<Theta>  [\<tturnstile>]\<^bsub>/F\<^esub> Ps Ts \<rbrakk> 
                \<Longrightarrow> \<Gamma>, \<Theta> [\<tturnstile>]\<^bsub>/F\<^esub> ((P, Q, A)#Ps) (c#Ts)"
  apply(simp add:map_ann_hoare_def)
  apply clarify
  apply (rename_tac i)
  apply(case_tac i,simp+)
 done

lemma MapAnnMap: 
   "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (P k) (c k) (Q k), (A k) 
\<Longrightarrow> \<Gamma>, \<Theta> [\<tturnstile>]\<^bsub>/F\<^esub> (map (\<lambda>k. (P k, Q k, A k)) [i..<j]) (map c [i..<j])"
 by (simp add: add.commute le_add1 map_ann_hoare_def)

lemma ParallelRule:
  "\<lbrakk>\<Gamma>, \<Theta> [\<tturnstile>]\<^bsub>/F\<^esub> Ps Cs;
    interfree \<Gamma> \<Theta> F Ps Cs;
    length Cs = length Ps
 \<rbrakk> \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnPar Ps) 
                    (Parallel Cs) 
                    (\<Inter>i\<in>{i. i<length Ps}. postcond (Ps!i)), (\<Union>i\<in>{i. i<length Ps}. abrcond (Ps!i))"
  apply (clarsimp simp add:neq_Nil_conv Parallel map_ann_hoare_def )+
  apply (rule Parallel)
      apply fastforce
     apply fastforce
    apply fastforce
   apply clarsimp
  apply (clarsimp simp: in_set_conv_nth)
  apply (rename_tac i)
  apply (rule_tac x=i in exI, fastforce)
 done

lemma ParallelConseqRule:
  "\<lbrakk> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnPar Ps) 
                    (Parallel Ts) 
                    (\<Inter>i\<in>{i. i<length Ps}. postcond (Ps!i)), (\<Union>i\<in>{i. i<length Ps}. abrcond (Ps!i));
     (\<Inter>i\<in>{i. i<length Ps}. postcond (Ps!i)) \<subseteq> Q;
     (\<Union>i\<in>{i. i<length Ps}. abrcond (Ps!i)) \<subseteq> A
 \<rbrakk> \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnPar Ps) (Parallel Ts) Q, A"
  apply (rule Conseq)
  apply (rule exI[where x="(\<Inter>i\<in>{i. i<length Ps}. precond (Ps!i))"])
  apply (rule exI[where x="(\<Inter>i\<in>{i. i<length Ps}. postcond (Ps!i))"])
  apply (rule exI[where x="(\<Union>i\<in>{i. i<length Ps}. abrcond (Ps!i))"])
  apply (clarsimp)
 done

text \<open>See Soundness.thy for the rest of Parallel-mode rules\<close>

subsection \<open>VCG tactic helper definitions and lemmas\<close>

definition interfree_aux_right :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set \<Rightarrow> ('s assn \<times> ('s,'p,'f) com \<times> ('s, 'p, 'f) ann) \<Rightarrow> bool" where
  "interfree_aux_right \<Gamma> \<Theta> F \<equiv> \<lambda>(q, cmd, ann). (\<forall>aa ac.  atomicsR \<Gamma> \<Theta> ann cmd (aa,ac) \<longrightarrow> (\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> (q \<inter> aa) ac q, q))"

lemma pre_strengthen: "\<not>pre_par a \<Longrightarrow> pre (strengthen_pre a a') = pre a \<inter> a'"
  by (induct a arbitrary: a', simp_all)

lemma Basic_inter_right: 
  "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr (q \<inter> r)) (Basic f) q, q \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Basic f, AnnExpr r)"
  by (auto simp: interfree_aux_right_def
           elim!: atomicsR.cases
           dest: oghoare_sound)

lemma Skip_inter_right:
  "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr (q \<inter> r)) Skip q, q \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Skip, AnnExpr r)"
  by (auto simp: interfree_aux_right_def
           elim!: atomicsR.cases
           dest: oghoare_sound)

lemma Throw_inter_right:
  "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr (q \<inter> r)) Throw q, q \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Throw, AnnExpr r)"
  by (auto simp: interfree_aux_right_def
           elim!: atomicsR.cases
           dest: oghoare_sound)

lemma Spec_inter_right: 
  "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr (q \<inter> r)) (Spec rel) q, q \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Spec rel, AnnExpr r)"
  by (auto simp: interfree_aux_right_def  
           elim!: atomicsR.cases
           dest: oghoare_sound)

lemma valid_Await:
 "atom_com c \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (P \<inter> b) c Q,A \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P Await b c Q,A"
  apply (clarsimp simp: valid_def)
  apply (erule converse_rtranclpE)
   apply (clarsimp simp: final_def)
  apply clarsimp
  apply (erule step_Normal_elim_cases)
      apply clarsimp
      apply (erule disjE)
       apply (fastforce dest: no_steps_final simp: final_def)
      apply (fastforce dest: no_steps_final simp: final_def)
     apply clarsimp
     apply (drule no_steps_final, simp add: final_def)
     apply clarsimp
     apply (rename_tac x c'')
     apply (drule_tac x="Normal x" in spec)
     apply (drule spec[where x=Stuck])
     apply (drule spec[where x=Skip])
     apply (erule impE)
     apply (cut_tac c=c'' in steps_Stuck[where \<Gamma>=\<Gamma>])
     apply fastforce
    apply clarsimp
   apply (drule no_steps_final, simp add: final_def)
   apply clarsimp
   apply (drule_tac x="Normal x" in spec)
   apply (drule_tac x="Fault f" in spec)
   apply (drule spec[where x=Skip])
   apply (erule impE)
    apply (rename_tac c'' f)
    apply (cut_tac c=c'' and f=f in steps_Fault[where \<Gamma>=\<Gamma>])
    apply fastforce
   apply clarsimp
  apply clarsimp
 done

lemma atomcom_imp_not_prepare:
 "ann_matches \<Gamma> \<Theta> a c \<Longrightarrow> atom_com c \<Longrightarrow> 
   \<not> pre_par a"
 by (induct rule:ann_matches.induct, simp_all)

lemma Await_inter_right: 
  "atom_com c \<Longrightarrow>
  \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P a c q,q \<Longrightarrow>
  q \<inter> r \<inter> b \<subseteq> P \<Longrightarrow>
  interfree_aux_right \<Gamma> \<Theta> F (q, Await b c, AnnRec r a)"
  apply (simp add: interfree_aux_right_def  )
  apply clarsimp
  apply (erule atomicsR.cases, simp_all)
  apply clarsimp
  apply (rule valid_Await, assumption)
  apply (drule oghoare_seq_sound)
  apply (erule valid_weaken_pre)
  apply blast
 done

lemma Call_inter_right:
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (q, f, P);
     n < length as; \<Gamma> p = Some f;
     as ! n = P; \<Theta> p = Some as\<rbrakk> \<Longrightarrow>
  interfree_aux_right \<Gamma> \<Theta> F (q, Call p, AnnCall r n)"
  by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma DynCom_inter_right:
  "\<lbrakk>\<And>s. s \<in> r \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, f s, P) \<rbrakk> \<Longrightarrow>
  interfree_aux_right \<Gamma> \<Theta> F (q, DynCom f, AnnRec r P)"
  by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma Guard_inter_right:
  "interfree_aux_right \<Gamma> \<Theta> F (q, c, a)
     \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Guard f g c, AnnRec r a)"
 by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma Parallel_inter_right_empty:
  "interfree_aux_right \<Gamma> \<Theta> F (q, Parallel [], AnnPar [])"
 by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma Parallel_inter_right_List:
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (q, c, a);
    interfree_aux_right \<Gamma> \<Theta> F (q, Parallel cs, AnnPar as)\<rbrakk>
     \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, Parallel (c#cs), AnnPar ((a, Q, A) #as))"
  apply (clarsimp simp: interfree_aux_right_def)
  apply (erule atomicsR.cases; clarsimp)
  apply (rename_tac i aa b)
  apply (case_tac i, simp)
  apply (fastforce intro: AtParallelExprs)
  done

lemma Parallel_inter_right_Map:
  "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, c k, a k)
     \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F
                (q, Parallel (map c [i..<j]), AnnPar (map (\<lambda>i. (a i, Q, A)) [i..<j]))"
  apply (clarsimp simp: interfree_aux_right_def)
  apply (erule atomicsR.cases; clarsimp)
  apply (rename_tac ia aa b)
  apply (drule_tac x="i+ia" in spec)
  by fastforce

lemma Seq_inter_right: 
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>1, a1); interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>2, a2) \<rbrakk>\<Longrightarrow> 
  interfree_aux_right \<Gamma> \<Theta> F (q, Seq c\<^sub>1 c\<^sub>2, AnnComp a1 a2)"
 by (auto simp add: interfree_aux_right_def elim: atomicsR.cases)

lemma Catch_inter_right:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>1, a1); interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>2, a2) \<rbrakk>\<Longrightarrow>
  interfree_aux_right \<Gamma> \<Theta> F (q, Catch c\<^sub>1 c\<^sub>2, AnnComp a1 a2)"
 by (auto simp add: interfree_aux_right_def elim: atomicsR.cases)

lemma While_inter_aux_any: "interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, abr), c, P) \<Longrightarrow>
  interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, abr), While b c, AnnWhile R I P)"
 by (auto simp add:  interfree_aux_def
          elim: atomicsR.cases[where ?a1.0="AnnWhile _ _ _"] )

lemma While_inter_right:
  "interfree_aux_right \<Gamma> \<Theta> F (q, c, a)
     \<Longrightarrow> interfree_aux_right \<Gamma> \<Theta> F (q, While b c, AnnWhile r i a)"
 by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma Cond_inter_aux_any:
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), c\<^sub>1, a1); interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), c\<^sub>2, a2) \<rbrakk>\<Longrightarrow> 
   interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), Cond b c\<^sub>1 c\<^sub>2, AnnBin r a1 a2)"
 by (fastforce simp add:  interfree_aux_def 
               elim: atomicsR.cases[where ?a1.0="AnnBin _ _ _"])

lemma Cond_inter_right:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>1, a1); interfree_aux_right \<Gamma> \<Theta> F (q, c\<^sub>2, a2) \<rbrakk>\<Longrightarrow> 
   interfree_aux_right \<Gamma> \<Theta> F (q, Cond b c\<^sub>1 c\<^sub>2, AnnBin r a1 a2)"
 by(auto simp: interfree_aux_right_def elim: atomicsR.cases)

lemma Basic_inter_aux: 
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (r, com, ann); 
    interfree_aux_right \<Gamma> \<Theta> F (q, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (a, com, ann) \<rbrakk> \<Longrightarrow> 
    interfree_aux \<Gamma> \<Theta> F (Basic f, (AnnExpr r, q, a), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Skip_inter_aux:
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (q, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (a, com, ann) \<rbrakk> \<Longrightarrow>
    interfree_aux \<Gamma> \<Theta> F (Skip, (AnnExpr r, q, a), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Throw_inter_aux:
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (q, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (a, com, ann) \<rbrakk> \<Longrightarrow>
    interfree_aux \<Gamma> \<Theta> F (Throw, (AnnExpr r, q, a), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Spec_inter_aux: 
  "\<lbrakk>interfree_aux_right \<Gamma> \<Theta> F (r, com, ann); 
    interfree_aux_right \<Gamma> \<Theta> F (q, com, ann);
    interfree_aux_right \<Gamma> \<Theta> F (a, com, ann) \<rbrakk> \<Longrightarrow> 
    interfree_aux \<Gamma> \<Theta> F (Spec rel, (AnnExpr r, q, a), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

(*lemma Seq_inter_aux_any: 
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), c\<^sub>1, a1);
    interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), c\<^sub>2, a2) \<rbrakk>\<Longrightarrow> 
  interfree_aux \<Gamma> \<Theta> F (Any, (AnyAnn, q, a), Seq c\<^sub>1 c\<^sub>2, AnnComp a1 a2)"
 by (fastforce simp add:  interfree_aux_def interfree_aux_right_def
               elim: atomicsR.cases[where ?a1.0="AnnComp _ _"])*)

lemma Seq_inter_aux:
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (c\<^sub>1, (r\<^sub>1, pre r\<^sub>2, A), com, ann);
     interfree_aux \<Gamma> \<Theta> F (c\<^sub>2, (r\<^sub>2, Q, A), com, ann) \<rbrakk>
   \<Longrightarrow> interfree_aux \<Gamma> \<Theta> F (Seq c\<^sub>1 c\<^sub>2, (AnnComp r\<^sub>1 r\<^sub>2, Q, A), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Catch_inter_aux:
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (c\<^sub>1, (r\<^sub>1, Q, pre r\<^sub>2), com, ann);
     interfree_aux \<Gamma> \<Theta> F (c\<^sub>2, (r\<^sub>2, Q, A), com, ann) \<rbrakk>
   \<Longrightarrow> interfree_aux \<Gamma> \<Theta> F (Catch c\<^sub>1 c\<^sub>2, (AnnComp r\<^sub>1 r\<^sub>2, Q, A), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Cond_inter_aux: 
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
    interfree_aux \<Gamma> \<Theta> F (c\<^sub>1, (r\<^sub>1, Q, A), com, ann); 
    interfree_aux \<Gamma> \<Theta> F (c\<^sub>2, (r\<^sub>2, Q, A), com, ann) \<rbrakk>
 \<Longrightarrow>  interfree_aux \<Gamma> \<Theta> F (Cond b c\<^sub>1 c\<^sub>2, (AnnBin r r\<^sub>1 r\<^sub>2, Q, A), com, ann)"
by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)


lemma While_inter_aux: 
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann); 
     interfree_aux_right \<Gamma> \<Theta> F (Q, com, ann);
     interfree_aux \<Gamma> \<Theta> F (c, (P, i, A), com, ann) \<rbrakk> \<Longrightarrow>
     interfree_aux \<Gamma> \<Theta> F (While b c, (AnnWhile r i P, Q, A), com, ann)"
by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Await_inter_aux: 
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann); 
     interfree_aux_right \<Gamma> \<Theta> F (Q, com, ann); 
     interfree_aux_right \<Gamma> \<Theta> F (A, com, ann) \<rbrakk>
  \<Longrightarrow> interfree_aux \<Gamma> \<Theta> F (Await b e, (AnnRec r ae, Q, A), com, ann)"
  by (auto simp: interfree_aux_def interfree_aux_right_def elim: assertionsR.cases)

lemma Call_inter_aux:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
     interfree_aux \<Gamma> \<Theta> F (f, (P, Q, A), com, ann);
     n < length as; \<Gamma> p = Some f;
     as ! n = P; \<Theta> p = Some as \<rbrakk> \<Longrightarrow>
     interfree_aux \<Gamma> \<Theta> F (Call p, (AnnCall r n, Q, A), com, ann)"
by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma DynCom_inter_aux:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
     interfree_aux_right \<Gamma> \<Theta> F (Q, com, ann); 
     interfree_aux_right \<Gamma> \<Theta> F (A, com, ann);
     \<And>s. s\<in>r \<Longrightarrow> interfree_aux \<Gamma> \<Theta> F (f s, (P, Q, A), com, ann) \<rbrakk> \<Longrightarrow>
     interfree_aux \<Gamma> \<Theta> F (DynCom f, (AnnRec r P, Q, A), com, ann)"
 by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

lemma Guard_inter_aux:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (r, com, ann);
     interfree_aux_right \<Gamma> \<Theta> F (Q, com, ann);
     interfree_aux \<Gamma> \<Theta> F (c, (P, Q, A), com, ann) \<rbrakk> \<Longrightarrow>
     interfree_aux \<Gamma> \<Theta> F (Guard f g c, (AnnRec r P, Q, A), com, ann)"
by (auto elim: assertionsR.cases simp: interfree_aux_def interfree_aux_right_def)

definition
  inter_aux_Par :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set \<Rightarrow>
                    (('s, 'p, 'f) com list \<times> (('s, 'p, 'f) ann_triple) list \<times> ('s, 'p, 'f) com \<times> ('s, 'p, 'f) ann) \<Rightarrow> bool" where
  "inter_aux_Par \<Gamma> \<Theta> F \<equiv>
     \<lambda>(cs, as, c, a). \<forall>i < length cs. interfree_aux \<Gamma> \<Theta> F (cs ! i, as ! i, c, a)"

lemma inter_aux_Par_Empty: "inter_aux_Par \<Gamma> \<Theta> F ([], [], c, a)"
by(simp add:inter_aux_Par_def)

lemma inter_aux_Par_List:
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (x, a, y, a');
  inter_aux_Par \<Gamma> \<Theta> F (xs, as, y, a')\<rbrakk> 
  \<Longrightarrow> inter_aux_Par \<Gamma> \<Theta> F (x#xs, a#as, y, a')"
  apply (simp add: inter_aux_Par_def)
  apply (rule allI)
  apply (rename_tac v)
  apply (case_tac v)
    apply simp_all
  done

lemma inter_aux_Par_Map: "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> interfree_aux \<Gamma> \<Theta> F (c k, Q k, x, a)
 \<Longrightarrow> inter_aux_Par \<Gamma> \<Theta> F (map c [i..<j], map Q [i..<j], x, a)"
  by(force simp add: inter_aux_Par_def less_diff_conv)

lemma Parallel_inter_aux:
  "\<lbrakk> interfree_aux_right \<Gamma> \<Theta> F (Q, com, ann);
     interfree_aux_right \<Gamma> \<Theta> F (A, com, ann);
     interfree_aux_right \<Gamma> \<Theta> F (\<Inter> (set (map postcond as)), com, ann);
     inter_aux_Par \<Gamma> \<Theta> F (cs, as, com, ann) \<rbrakk> \<Longrightarrow>
     interfree_aux \<Gamma> \<Theta> F (Parallel cs, (AnnPar as, Q, A), com, ann)"
  apply (clarsimp simp: interfree_aux_def interfree_aux_right_def inter_aux_Par_def)
  by (erule assertionsR.cases; fastforce)

definition interfree_swap :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set \<Rightarrow> (('s, 'p, 'f) com \<times> (('s, 'p, 'f) ann \<times> 's assn \<times> 's assn) \<times> ('s, 'p, 'f) com list \<times> (('s, 'p, 'f) ann \<times> 's assn \<times> 's assn) list) \<Rightarrow> bool" where
  "interfree_swap \<Gamma> \<Theta> F \<equiv> \<lambda>(x, a, xs, as). \<forall>y < length xs. interfree_aux \<Gamma> \<Theta> F (x, a, xs ! y, pres (as ! y))
  \<and> interfree_aux \<Gamma> \<Theta> F (xs ! y, as ! y, x, fst a)"

lemma interfree_swap_Empty: "interfree_swap  \<Gamma> \<Theta> F (x, a, [], [])"
by(simp add:interfree_swap_def)

lemma interfree_swap_List:  
  "\<lbrakk> interfree_aux \<Gamma> \<Theta> F (x, a, y, fst (a')); 
  interfree_aux \<Gamma> \<Theta> F (y, a', x, fst a);
  interfree_swap \<Gamma> \<Theta> F (x, a, xs, as)\<rbrakk> 
  \<Longrightarrow> interfree_swap \<Gamma> \<Theta> F (x, a, y#xs, a'#as)"
  apply (simp add: interfree_swap_def)
  apply (rule allI)
  apply (rename_tac v)
  apply (case_tac v)
    apply simp_all
  done

lemma interfree_swap_Map: "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> interfree_aux \<Gamma> \<Theta> F (x, a, c k, fst (Q k)) 
 \<and> interfree_aux \<Gamma> \<Theta> F (c k, (Q k), x, fst a)
 \<Longrightarrow> interfree_swap \<Gamma> \<Theta> F (x, a, map c [i..<j], map Q [i..<j])"
by(force simp add: interfree_swap_def less_diff_conv)

lemma interfree_Empty: "interfree \<Gamma> \<Theta> F [] []"
by(simp add:interfree_def)

lemma interfree_List: 
  "\<lbrakk> interfree_swap \<Gamma> \<Theta> F (x, a, xs, as); interfree \<Gamma> \<Theta> F as xs \<rbrakk> \<Longrightarrow> interfree \<Gamma> \<Theta> F (a#as) (x#xs)"
  apply (simp add: interfree_swap_def interfree_def)
  apply clarify
  apply (rename_tac i j)
  apply (case_tac i)
   apply (case_tac j)
    apply simp_all
  apply (case_tac j)
   apply simp_all
 done

lemma interfree_Map: 
  "(\<forall>i j. a\<le>i \<and> i<b \<and> a\<le>j \<and> j<b  \<and> i\<noteq>j \<longrightarrow> interfree_aux \<Gamma> \<Theta> F (c i, A i, c j, pres (A j)))  
  \<Longrightarrow> interfree \<Gamma> \<Theta> F (map (\<lambda>k. A k) [a..<b]) (map (\<lambda>k. c k) [a..<b])"
by (force simp add: interfree_def less_diff_conv)

lemma list_lemmas: "length []=0" "length (x#xs) = Suc(length xs)"
    "(x#xs) ! 0 = x" "(x#xs) ! Suc n = xs ! n"
  by simp_all

lemma le_Suc_eq_insert: "{i. i <Suc n} = insert n {i. i< n}"
  by auto

lemmas primrecdef_list = "pre.simps" strengthen_pre.simps
lemmas ParallelConseq_list = INTER_eq Collect_conj_eq length_map length_upt length_append
lemmas my_simp_list = list_lemmas fst_conv snd_conv
not_less0 refl le_Suc_eq_insert Suc_not_Zero Zero_not_Suc nat.inject
Collect_mem_eq ball_simps option.simps primrecdef_list

(* Push remaining subgoals into hyps to remove duplicates quickly *)
ML \<open>val hyp_tac = CSUBGOAL (fn (prem,i) => PRIMITIVE (fn thm =>
    let
      val thm' = Thm.permute_prems 0 (i-1) thm |> Goal.protect 1
      val asm = Thm.assume prem
    in
      case (try (fn thm' => (Thm.implies_elim thm' asm)) thm') of
      SOME thm => thm |> Goal.conclude |> Thm.permute_prems 0 (~(i-1))
     | NONE => error ("hyp_tac failed:" ^ (@{make_string} (thm',asm)))
    end
  ))
\<close>
ML \<open>

(*Remove a premise of the form 's \<in> _' if s is not referred to anywhere*)
fun remove_single_Bound_mem ctxt = SUBGOAL (fn (t, i) => let
    val prems = Logic.strip_assums_hyp t
    val concl = Logic.strip_assums_concl t
    fun bd_member t = (case HOLogic.dest_Trueprop t
        of Const (@{const_name "Set.member"}, _) $ Bound j $ _ => SOME j
        | _ => NONE) handle TERM _ => NONE
  in filter_prems_tac ctxt
    (fn prem => case bd_member prem of NONE => true
      | SOME j => let val xs = (filter (fn t => loose_bvar1 (t, j)) (concl :: prems))
        in length xs <> 1 end)
    i
  end handle Subscript => no_tac)
\<close>

named_theorems proc_simp
named_theorems oghoare_simps

lemmas guards.simps[oghoare_simps add]
       ann_guards.simps[oghoare_simps add]

ML \<open>

fun rt ctxt t i =
  resolve_tac ctxt [t] i

fun rts ctxt xs i =
  resolve_tac ctxt xs i

fun conjI_Tac ctxt tac i st = st |>
       ( (EVERY [rt ctxt conjI i,
          conjI_Tac ctxt tac (i+1),
          tac i]) ORELSE (tac i) )

fun get_oghoare_simps ctxt =
 Proof_Context.get_thms ctxt "oghoare_simps"

fun simp ctxt extra =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps extra)

fun simp_only ctxt simps =
  simp_tac ((clear_simpset ctxt) addsimps simps)

fun prod_sel_simp ctxt =
  simp_only ctxt @{thms prod.sel}

fun oghoare_simp ctxt =
   simp_only ctxt (get_oghoare_simps ctxt)

fun ParallelConseq ctxt =
  clarsimp_tac (put_simpset HOL_basic_ss ctxt addsimps (@{thms ParallelConseq_list} @ @{thms my_simp_list}))

val enable_trace = false;
fun trace str = if enable_trace then tracing str else ();

fun HoareRuleTac (ctxt' as (ctxt,args)) i st =
  (Cache_Tactics.SUBGOAL_CACHE (nth args 0)
  (fn (_,i) => (SUBGOAL (fn (_,i) =>
    (EVERY[rts ctxt @{thms Seq Catch SeqSeq SeqCatch} i,
        HoareRuleTac ctxt' (i+1),
        HoareRuleTac ctxt' i]
    ORELSE
    (FIRST[rts ctxt (@{thms SkipRule SeqSkipRule}) i,
         rts ctxt (@{thms BasicRule SeqBasicRule}) i,
         rts ctxt (@{thms ThrowRule SeqThrowRule}) i,
         rts ctxt (@{thms SpecRule SeqSpecRule}) i,
         EVERY[rt ctxt (@{thm SeqParallel}) i,
               HoareRuleTac ctxt' (i+1)],
         EVERY[rt ctxt  (@{thm ParallelConseqRule}) i,
               ParallelConseq ctxt (i+2),
               ParallelConseq ctxt (i+1),
               ParallelTac ctxt' i],
         EVERY[rt ctxt (@{thm CondRule}) i,
               HoareRuleTac ctxt' (i+2),
               HoareRuleTac ctxt' (i+1)],
         EVERY[rt ctxt @{thm SeqCondRule} i,
               HoareRuleTac ctxt' (i+1),
               HoareRuleTac ctxt' i],
         EVERY[rt ctxt  (@{thm WhileRule}) i,
               HoareRuleTac ctxt' (i+3)],
         EVERY[rt ctxt  (@{thm SeqWhileRule}) i,
               HoareRuleTac ctxt' i],
         EVERY[rt ctxt (@{thm AwaitRule}) i,
               HoareRuleTac ctxt' (i+1),
               simp ctxt (@{thms atom_com.simps}) i],
         EVERY[rts ctxt (@{thms CallRule SeqCallRule}) i,
               Call_asm_inst ctxt (i+2),
               HoareRuleTac ctxt' (i+1)],
         EVERY[rts ctxt (@{thms DynComRule SeqDynComRule}) i,
               HoareRuleTac ctxt' (i+1)],
         EVERY[rts ctxt (@{thms GuardRule}) i,
               HoareRuleTac ctxt' (i+2)],
         K all_tac i ])))
         THEN_ALL_NEW hyp_tac) i)) i st

and Call_asm_inst ctxt i = 
  let val proc_simps = Proof_Context.get_thms ctxt "proc_simp" @ @{thms list_lemmas} in
    EVERY[rts ctxt proc_simps (i+3),
         rts ctxt proc_simps (i+2),
         rts ctxt proc_simps (i+1),
        ParallelConseq ctxt i]
    end

and ParallelTac (ctxt' as (ctxt,args)) i =
          EVERY[rt ctxt (@{thm ParallelRule}) i,
                               ParallelConseq ctxt (i+2),
                               interfree_Tac ctxt' (i+1),
                               ParallelConseq ctxt i,
                               MapAnn_Tac ctxt' i]

and MapAnn_Tac (ctxt' as (ctxt,args)) i st = st |>
    (FIRST[rt ctxt (@{thm MapAnnEmpty}) i,
           EVERY[rt ctxt (@{thm MapAnnList}) i,
                 MapAnn_Tac ctxt' (i+1),
                 HoareRuleTac ctxt' i],
            EVERY[rt ctxt (@{thm MapAnnMap}) i,
                 rt ctxt (@{thm allI}) i, rt ctxt (@{thm impI}) i,
                 HoareRuleTac ctxt' i]])

and interfree_Tac (ctxt' as (ctxt,args)) i st = st |>
   (FIRST[rt ctxt (@{thm interfree_Empty}) i,
          EVERY[rt ctxt (@{thm interfree_List}) i,
                interfree_Tac ctxt' (i+1),
                interfree_swap_Tac ctxt' i],
          EVERY[rt ctxt (@{thm interfree_Map}) i,
                rt ctxt (@{thm allI}) i, rt ctxt (@{thm allI}) i, rt ctxt (@{thm impI}) i,
                interfree_aux_Tac ctxt' i ]])

and interfree_swap_Tac (ctxt' as (ctxt,args)) i st = st |>
    (FIRST[rt ctxt (@{thm interfree_swap_Empty}) i,
           EVERY[rt ctxt (@{thm interfree_swap_List}) i,
                 interfree_swap_Tac ctxt' (i+2),
                 interfree_aux_Tac ctxt' (i+1),
                 interfree_aux_Tac ctxt' i ],
           EVERY[rt ctxt (@{thm interfree_swap_Map}) i,
                 rt ctxt (@{thm allI}) i, rt ctxt (@{thm impI}) i,
                 conjI_Tac ctxt (interfree_aux_Tac ctxt') i]])

and inter_aux_Par_Tac (ctxt' as (ctxt,args)) i st = st |>
    (FIRST[rt ctxt (@{thm inter_aux_Par_Empty}) i,
           EVERY[rt ctxt (@{thm inter_aux_Par_List}) i,
                 inter_aux_Par_Tac ctxt' (i+1),
                 interfree_aux_Tac ctxt' i ],
           EVERY[rt ctxt (@{thm inter_aux_Par_Map}) i,
                 rt ctxt (@{thm allI}) i, rt ctxt (@{thm impI}) i,
                 interfree_aux_Tac ctxt' i]])

and interfree_aux_Tac ctxt' i = dest_inter_aux_Tac ctxt' i

and dest_inter_aux_Tac (ctxt' as (ctxt,args)) i st =
  (Cache_Tactics.SUBGOAL_CACHE (nth args 1)
  (fn (_,i) => (SUBGOAL (fn (_,i) =>
     (TRY (REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms prod.sel} i)) THEN
     FIRST[EVERY[rts ctxt (@{thms Skip_inter_aux Throw_inter_aux Basic_inter_aux Spec_inter_aux}) i,
                 dest_inter_right_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rts ctxt (@{thms Seq_inter_aux Catch_inter_aux}) i,
                 dest_inter_aux_Tac ctxt' (i+1),
                 dest_inter_aux_Tac ctxt' (i+0)],
           EVERY[rt ctxt (@{thm Cond_inter_aux}) i,
                 dest_inter_aux_Tac ctxt' (i+2),
                 dest_inter_aux_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm While_inter_aux}) i,
                 dest_inter_aux_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Await_inter_aux}) i,
                 dest_inter_right_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' (i+0)],
           EVERY[rt ctxt (@{thm Call_inter_aux}) i,
                 Call_asm_inst ctxt (i+2),
                 dest_inter_aux_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm DynCom_inter_aux}) i,
                 dest_inter_aux_Tac ctxt' (i+3),
                 dest_inter_right_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Guard_inter_aux}) i,
                 dest_inter_aux_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Parallel_inter_aux}) i,
                 inter_aux_Par_Tac ctxt' (i+3),
                 dest_inter_right_Tac ctxt' (i+2),
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           dest_inter_right_Tac ctxt' i]))
         THEN_ALL_NEW hyp_tac) i)) i st

and dest_inter_right_Tac (ctxt' as (ctxt,args)) i st =
  (Cache_Tactics.SUBGOAL_CACHE (nth args 2)
  (fn (_,i) =>
     FIRST[EVERY[rts ctxt (@{thms Skip_inter_right Throw_inter_right
                                  Basic_inter_right Spec_inter_right}) i,
                 HoareRuleTac ctxt' i],
           EVERY[rts ctxt (@{thms Seq_inter_right Catch_inter_right}) i,
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Cond_inter_right}) i,
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm While_inter_right}) i,
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Await_inter_right}) i,
                 HoareRuleTac ctxt' (i+1),
                 simp ctxt (@{thms atom_com.simps}) i],
           EVERY[rt ctxt (@{thm Call_inter_right}) i,
                   Call_asm_inst ctxt (i+1),
                   dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm DynCom_inter_right}) i,
                   dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Guard_inter_right}) i,
                   dest_inter_right_Tac ctxt' i],
           rt ctxt (@{thm Parallel_inter_right_empty}) i,
           EVERY[rt ctxt (@{thm Parallel_inter_right_List}) i,
                 dest_inter_right_Tac ctxt' (i+1),
                 dest_inter_right_Tac ctxt' i],
           EVERY[rt ctxt (@{thm Parallel_inter_right_Map}) i,
                 rt ctxt (@{thm allI}) i, rt ctxt (@{thm impI}) i,
                 dest_inter_right_Tac ctxt' i],
           K all_tac i])) i st
\<close>

ML \<open>

fun oghoare_tac ctxt =
   SUBGOAL (fn (_, i) =>
   TRY (prod_sel_simp ctxt i)
   THEN TRY (oghoare_simp ctxt i)
   THEN Cache_Tactics.cacheify_tactic 3 HoareRuleTac ctxt i)

(* oghoare_tac' fails if oghoare_tac does not do anything *)
fun oghoare_tac' ctxt i goal =
  let
    val results = oghoare_tac ctxt i goal;
  in
    if (Thm.eq_thm (results |> Seq.hd, goal) handle Option => false)
    then no_tac goal
    else results
  end;

fun oghoare_parallel_tac ctxt i = 
  TRY (oghoare_simp ctxt i) THEN
  Cache_Tactics.cacheify_tactic 3 ParallelTac ctxt i
fun oghoare_interfree_tac ctxt i =
  TRY (oghoare_simp ctxt i) THEN
  Cache_Tactics.cacheify_tactic 3 interfree_Tac ctxt i
fun oghoare_interfree_aux_tac ctxt i =
  TRY (oghoare_simp ctxt i) THEN
  Cache_Tactics.cacheify_tactic 3 interfree_aux_Tac ctxt i
\<close>

method_setup oghoare = \<open>
  Scan.succeed (SIMPLE_METHOD' o oghoare_tac')\<close>
  "verification condition generator for the oghoare logic"

method_setup oghoare_parallel = \<open>
  Scan.succeed (SIMPLE_METHOD' o oghoare_parallel_tac)\<close>
  "verification condition generator for the oghoare logic"

method_setup oghoare_interfree = \<open>
  Scan.succeed (SIMPLE_METHOD' o oghoare_interfree_tac)\<close>
  "verification condition generator for the oghoare logic"

method_setup oghoare_interfree_aux = \<open>
  Scan.succeed (SIMPLE_METHOD' o oghoare_interfree_aux_tac)\<close>
  "verification condition generator for the oghoare logic"

end
