(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>COMPLX small-step semantics\<close>
theory SmallStep
imports Language
begin

text \<open>The procedure environment\<close>
type_synonym ('s,'p,'f) body = "'p \<Rightarrow> ('s,'p,'f) com option"

text \<open>State types\<close>
datatype ('s,'f) xstate = Normal 's | Fault 'f | Stuck

lemma rtrancl_mono_proof[mono]:
   "(\<And>a b. x a b \<longrightarrow> y a b) \<Longrightarrow> rtranclp x a b \<longrightarrow> rtranclp y a b"
   apply (rule impI, rotate_tac, induct rule: rtranclp.induct)
    apply simp_all
   apply (metis rtranclp.intros)
   done


primrec redex:: "('s,'p,'f)com \<Rightarrow> ('s,'p,'f)com"
where
"redex Skip = Skip" |
"redex (Basic f) = (Basic f)" |
"redex (Spec r) = (Spec r)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Cond b c\<^sub>1 c\<^sub>2) = (Cond b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Call p) = (Call p)" |
"redex (DynCom d) = (DynCom d)" |
"redex (Guard f b c) = (Guard f b c)" |
"redex (Throw) = Throw" |
"redex (Catch c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Await b c) = Await b c" |
"redex (Parallel cs) = Parallel cs"

subsection \<open>Small-Step Computation: \<open>\<Gamma> \<turnstile>(c, s) \<rightarrow> (c', s')\<close>\<close>

text \<open>The final configuration is either of the form \<open>(Skip,_)\<close> for normal
termination, or @{term "(Throw,Normal s)"} in case the program was started in 
a @{term "Normal"} state and terminated abruptly. Explicit abrupt states are removed
from the language definition and thus do not need to be propogated.\<close>

type_synonym ('s,'p,'f) config = "('s,'p,'f)com  \<times> ('s,'f) xstate"

definition final:: "('s,'p,'f) config \<Rightarrow> bool" where
"final cfg = (fst cfg=Skip \<or> (fst cfg=Throw \<and> (\<exists>s. snd cfg=Normal s)))"

primrec atom_com :: "\<^cancel>\<open>('s,'p,'f) body \<Rightarrow>\<close> ('s, 'p, 'f) com \<Rightarrow> bool" where
  "atom_com Skip = True" | 
  "atom_com (Basic f) = True" | 
  "atom_com (Spec r) = True" | 
  "atom_com (Seq  c\<^sub>1 c\<^sub>2) = (atom_com c\<^sub>1 \<and> atom_com c\<^sub>2)" | 
  "atom_com (Cond b c\<^sub>1 c\<^sub>2) = (atom_com c\<^sub>1 \<and> atom_com c\<^sub>2)" | 
  "atom_com (While b c) = atom_com c" | 
 (* Change to  atom_com (Call p) = atom_com (\<Theta> p)
  Butow do we pass function body from step? *)
  "atom_com (Call p) = False" |
  "atom_com (DynCom f) = (\<forall>s::'s. atom_com (f s))" | 
  "atom_com (Guard f g c) = atom_com c" | 
  "atom_com Throw = True" | 
  "atom_com (Catch c\<^sub>1 c\<^sub>2) = (atom_com c\<^sub>1 \<and> atom_com c\<^sub>2)" | 
  "atom_com (Parallel cs) = False" | 
  "atom_com (Await b c) = False"


inductive
      "step"::"[('s,'p,'f) body, ('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>/ _)" [81,81,81] 100)
  and "step_rtrancl" :: "[('s,'p,'f) body, ('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_ \<turnstile> (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
  for \<Gamma>::"('s,'p,'f) body"
where
  "\<Gamma> \<turnstile> a \<rightarrow>\<^sup>* b \<equiv> (step \<Gamma>)\<^sup>*\<^sup>* a b"
| Basic: "\<Gamma> \<turnstile>(Basic f,Normal s) \<rightarrow> (Skip,Normal (f s))"

| Spec: "(s,t) \<in> r \<Longrightarrow> \<Gamma> \<turnstile>(Spec r,Normal s) \<rightarrow> (Skip,Normal t)"
| SpecStuck: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma> \<turnstile>(Spec r,Normal s) \<rightarrow> (Skip,Stuck)"

| Guard: "s\<in>g \<Longrightarrow> \<Gamma> \<turnstile>(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
  
| GuardFault: "s\<notin>g \<Longrightarrow> \<Gamma> \<turnstile>(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"


| Seq: "\<Gamma> \<turnstile>(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma> \<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkip: "\<Gamma> \<turnstile>(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrow: "\<Gamma> \<turnstile>(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"

| CondTrue:  "s\<in>b \<Longrightarrow> \<Gamma> \<turnstile>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
| CondFalse: "s\<notin>b \<Longrightarrow> \<Gamma> \<turnstile>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| WhileTrue: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma> \<turnstile>(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"

| WhileFalse: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma> \<turnstile>(While b c,Normal s) \<rightarrow> (Skip,Normal s)"

| Call: "\<Gamma> p=Some b \<Longrightarrow>
         \<Gamma> \<turnstile>(Call p,Normal s) \<rightarrow> (b,Normal s)"

| CallUndefined: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma> \<turnstile>(Call p,Normal s) \<rightarrow> (Skip,Stuck)"

| DynCom: "\<Gamma> \<turnstile>(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"

| Catch: "\<lbrakk>\<Gamma> \<turnstile>(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma> \<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchSkip: "\<Gamma> \<turnstile>(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"
| CatchThrow: "\<Gamma> \<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| FaultProp:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>(c,Fault f) \<rightarrow> (Skip,Fault f)"
| StuckProp:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>(c,Stuck) \<rightarrow> (Skip,Stuck)"


| Parallel: "\<lbrakk>  i < length cs; \<Gamma> \<turnstile> (cs!i, s) \<rightarrow> (c', s') \<rbrakk> 
            \<Longrightarrow> \<Gamma> \<turnstile> (Parallel cs, s) \<rightarrow> (Parallel (cs[i := c']), s')"

| ParSkip: "\<lbrakk> \<forall>c \<in> set cs. c = Skip \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Parallel cs, s) \<rightarrow> (Skip, s)"
(* If exception is thrown, the parallel execution may either abort
   immediately (rule ParThrow) or keep executing (rule Parallel) *)
| ParThrow: "\<lbrakk> Throw \<in> set cs \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Parallel cs, s) \<rightarrow> (Throw, s)"


| Await: "\<lbrakk> s \<in> b; \<Gamma> \<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (c', Normal s');
           atom_com c; c' = Skip \<or> c' = Throw \<rbrakk> 
          \<Longrightarrow> \<Gamma> \<turnstile> (Await b c, Normal s) \<rightarrow> (c', Normal s')"
| AwaitStuck: 
         "\<lbrakk> s \<in> b; \<Gamma> \<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (c', Stuck) ;
           atom_com c\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile> (Await b c, Normal s) \<rightarrow> (Skip, Stuck)" 
| AwaitFault: 
         "\<lbrakk> s \<in> b; \<Gamma> \<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (c', Fault f) ;
           atom_com c\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile> (Await b c, Normal s) \<rightarrow> (Skip, Fault f)" 
| AwaitNonAtom: 
         " \<not> atom_com c
          \<Longrightarrow> \<Gamma> \<turnstile> (Await b c, Normal s) \<rightarrow> (Skip, Stuck)"


lemmas step_induct = step.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
Basic Spec SpecStuck Guard GuardFault Seq SeqSkip SeqThrow CondTrue CondFalse
WhileTrue WhileFalse Call CallUndefined DynCom Catch CatchThrow CatchSkip
FaultProp StuckProp Parallel ParSkip Await, induct set]

text \<open>The execution of a command is blocked if it cannot make progress, but is not in a final
state. It is the intention that \<open>\<exists>cfg. \<Gamma> \<turnstile> (c, s) \<rightarrow> cfg) \<or> final (c, s) \<or> blocked \<Gamma> c s\<close>, but
we do not prove this.\<close>

function(sequential) blocked :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'f)xstate \<Rightarrow> bool" where
  "blocked \<Gamma> (Seq (Await b c\<^sub>1) c\<^sub>2) (Normal s) = (s \<notin> b)"
| "blocked \<Gamma> (Catch (Await b c\<^sub>1) c\<^sub>2) (Normal s) = (s \<notin> b)"
| "blocked \<Gamma> (Await b c) (Normal s) = (s \<notin> b \<or> (\<forall>c' s'. \<Gamma> \<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (c', Normal s') \<longrightarrow> \<not> final (c', Normal s')))"
| "blocked \<Gamma> (Parallel cs) (Normal s) = (\<forall>t \<in> set cs. blocked \<Gamma> t (Normal s) \<or> final (t, Normal s))"
| "blocked \<Gamma> _ _ = False"
by (pat_completeness, auto)

inductive_cases step_elim_cases [cases set]:
 "\<Gamma> \<turnstile>(Skip,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Guard f g c,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Basic f,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Spec r,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(While b c,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Call p,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(DynCom c,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Throw,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Catch c1 c2,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Parallel cs,s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Await b e,s) \<rightarrow> u"


inductive_cases step_Normal_elim_cases [cases set]:
 "\<Gamma> \<turnstile>(Skip,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Guard f g c,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Basic f,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Spec r,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Seq c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Cond b c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(While b c,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Call p,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(DynCom c,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Throw,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Catch c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Parallel cs,Normal s) \<rightarrow> u"
 "\<Gamma> \<turnstile>(Await b e,Normal s) \<rightarrow> u"


abbreviation 
 "step_trancl" :: "[('s,'p,'f) body, ('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma> \<turnstile>cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST step \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"

abbreviation 
 "step_n_trancl" :: "[('s,'p,'f) body, ('s,'p,'f) config,nat,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>n_/ _)" [81,81,81,81] 100)
 where
  "\<Gamma> \<turnstile>cf0 \<rightarrow>\<^sup>nn cf1 \<equiv> (CONST step \<Gamma> ^^ n) cf0 cf1"

lemma no_step_final: 
  assumes step: "\<Gamma> \<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
using step
by induct (auto simp add: final_def)

lemma no_step_final':
  assumes step: "\<Gamma> \<turnstile>cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
using step
  by (cases cfg, cases cfg') (auto intro: no_step_final)

lemma no_steps_final:
"\<Gamma> \<turnstile> v \<rightarrow>\<^sup>* w \<Longrightarrow> final v \<Longrightarrow> w = v"
  apply (cases v)
  apply simp
  apply  (erule converse_rtranclpE)
   apply simp
   apply (erule (1) no_step_final')
 done

lemma step_Fault: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step

by (induct) auto

lemma step_Stuck: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma SeqSteps: 
  assumes steps: "\<Gamma> \<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma> \<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have "\<Gamma> \<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma> \<turnstile> (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Seq)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma> \<turnstile> (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed


lemma CatchSteps: 
  assumes steps: "\<Gamma> \<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma> \<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma> \<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have s: "\<Gamma> \<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma> \<turnstile> (Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Catch)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma> \<turnstile> (Catch c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .      
qed


lemma steps_Fault: "\<Gamma> \<turnstile> (c, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma> \<turnstile> (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  have steps_c\<^sub>2: "\<Gamma> \<turnstile> (c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma> \<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma> \<turnstile> (Seq Skip c\<^sub>2, Fault f) \<rightarrow> (c\<^sub>2, Fault f)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma> \<turnstile> (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma> \<turnstile> (Catch c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma> \<turnstile> (Catch Skip c\<^sub>2, Fault f) \<rightarrow> (Skip, Fault f)" by (rule CatchSkip) 
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma steps_Stuck: "\<Gamma> \<turnstile> (c, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma> \<turnstile> (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  have steps_c\<^sub>2: "\<Gamma> \<turnstile> (c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma> \<turnstile> (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Stuck)".
  also
  have "\<Gamma> \<turnstile> (Seq Skip c\<^sub>2, Stuck) \<rightarrow> (c\<^sub>2, Stuck)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma> \<turnstile> (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma> \<turnstile> (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Stuck)" .
  also
  have "\<Gamma> \<turnstile> (Catch Skip c\<^sub>2, Stuck) \<rightarrow> (Skip, Stuck)" by (rule CatchSkip) 
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma step_Fault_prop: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Stuck_prop: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma steps_Fault_prop: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault f \<Longrightarrow> s'=Fault f"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Fault_prop)
qed

lemma steps_Stuck_prop: 
  assumes step: "\<Gamma> \<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Stuck_prop)
qed

end
