(*File: VDM_OBJ.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory VDM_OBJ imports OBJ begin

subsection\<open>Program logic\<close> 

text\<open>\label{sec:ObjLogic}Apart from the addition of proof rules for the three new
instructions, this section is essentially identical to Section
\ref{sec:VDM}.\<close>

subsubsection \<open>Assertions and their semantic validity\<close>

text\<open>Assertions are binary state predicates, as before.\<close>

type_synonym "Assn" = "State \<Rightarrow> State \<Rightarrow> bool"

definition VDM_validn :: "nat \<Rightarrow> OBJ \<Rightarrow> Assn \<Rightarrow> bool" 
                         (" \<Turnstile>\<^sub>_ _ : _ " 50)
where "(\<Turnstile>\<^sub>n c : A) = (\<forall> m . m \<le> n \<longrightarrow> (\<forall> s t . (s,c \<rightarrow>\<^sub>m t) \<longrightarrow> A s t))"

definition VDM_valid :: "OBJ \<Rightarrow> Assn \<Rightarrow> bool"
                         (" \<Turnstile> _ : _ " 50)
where "(\<Turnstile> c : A) = (\<forall> s t . (s,c \<Down> t) \<longrightarrow> A s t)"

lemma VDM_valid_validn: "\<Turnstile> c:A \<Longrightarrow> \<Turnstile>\<^sub>n c:A"
(*<*)
by (simp add: VDM_valid_def VDM_validn_def Sem_def, fastforce)
(*>*)

lemma VDM_validn_valid: "(\<forall> n . \<Turnstile>\<^sub>n c:A) \<Longrightarrow> \<Turnstile> c:A"
(*<*)
by (simp add: VDM_valid_def VDM_validn_def Sem_def, fastforce)
(*>*)

lemma VDM_lowerm: "\<lbrakk> \<Turnstile>\<^sub>n c:A; m < n \<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>m c:A"
(*<*)
apply (simp add: VDM_validn_def, clarsimp)
apply (erule_tac x="ma" in allE, simp)
done
(*>*)

definition Ctxt_validn :: "nat \<Rightarrow> (Assn set) \<Rightarrow> bool"
                       (" \<Turnstile>\<^sub>_ _  " 50)
where "(\<Turnstile>\<^sub>n G) = (\<forall> m . m \<le> n \<longrightarrow> (\<forall> A. A \<in> G \<longrightarrow> \<Turnstile>\<^sub>n Call : A))"

definition Ctxt_valid :: "Assn set \<Rightarrow> bool" (" \<Turnstile> _ " 50)
where "(\<Turnstile> G) = (\<forall> A . A \<in> G \<longrightarrow> \<Turnstile> Call : A)"

lemma Ctxt_valid_validn: "\<Turnstile> G \<Longrightarrow> \<Turnstile>\<^sub>n G"
(*<*)
apply (simp add: Ctxt_valid_def Ctxt_validn_def, clarsimp)
apply (rule VDM_valid_validn) apply fast
done
(*>*)

lemma Ctxt_validn_valid: "(\<forall> n . \<Turnstile>\<^sub>n G) \<Longrightarrow> \<Turnstile> G"
(*<*)
apply (simp add: Ctxt_valid_def Ctxt_validn_def, clarsimp)
apply (rule VDM_validn_valid) apply fast
done
(*>*)

lemma Ctxt_lowerm: "\<lbrakk> \<Turnstile>\<^sub>n G; m < n \<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>m G"
(*<*)
apply (simp add: Ctxt_validn_def, clarsimp)
apply (rule VDM_lowerm) prefer 2 apply assumption apply fast
done
(*>*)

definition valid :: "(Assn set) \<Rightarrow> OBJ \<Rightarrow> Assn \<Rightarrow> bool"
                      ("_ \<Turnstile> _ : _ " 50)
where "(G \<Turnstile> c : A) = (Ctxt_valid G \<longrightarrow> VDM_valid c A)"

definition validn :: "(Assn set) \<Rightarrow> nat \<Rightarrow> OBJ \<Rightarrow> Assn \<Rightarrow> bool"
                     ("_ \<Turnstile>\<^sub>_ _ : _" 50)
where "(G \<Turnstile>\<^sub>n c : A) = (\<Turnstile>\<^sub>n G \<longrightarrow> \<Turnstile>\<^sub>n c : A)"

lemma validn_valid: "(\<forall> n . G \<Turnstile>\<^sub>n c : A) \<Longrightarrow> G \<Turnstile> c : A"
(*<*)
apply (simp add: valid_def validn_def, clarsimp)
apply (rule VDM_validn_valid, clarsimp) 
apply (erule_tac x=n in allE, erule mp)
apply (erule Ctxt_valid_validn)
done
(*>*)

lemma ctxt_consn: "\<lbrakk> \<Turnstile>\<^sub>n G;  \<Turnstile>\<^sub>n Call:A \<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>n {A} \<union> G"
(*<*)
by (simp add: Ctxt_validn_def) 
(*>*)

subsubsection\<open>Proof system\<close>

inductive_set VDM_proof :: "(Assn set \<times> OBJ \<times> Assn) set"
where
VDMSkip: "(G, Skip, \<lambda> s t . t=s):VDM_proof"

| VDMAssign:
  "(G, Assign x e,
       \<lambda> s t . t = (update (fst s) x (evalE e (fst s)), snd s)):VDM_proof"

| VDMNew:
  "(G, New x C,
       \<lambda> s t . \<exists> l . l \<notin> Dom (snd s) \<and> 
                         t = (update (fst s) x (RVal (Loc l)),
                              (l,(C,[])) # (snd s))):VDM_proof"

| VDMGet:
  "(G, Get x y F,
       \<lambda> s t . \<exists> l C Flds v. (fst s) y = RVal(Loc l) \<and> 
                         lookup (snd s) l = Some(C,Flds) \<and> 
                         lookup Flds F = Some v \<and> 
                         t = (update (fst s) x v, snd s)):VDM_proof"

| VDMPut:
  "(G, Put x F e,
       \<lambda> s t . \<exists> l C Flds. (fst s) x = RVal(Loc l) \<and>
                         lookup (snd s) l = Some(C,Flds) \<and> 
                         t = (fst s, 
                              (l,(C,(F,evalE e (fst s)) # Flds))
                                           # (snd s))):VDM_proof"

| VDMComp:
  "\<lbrakk> (G, c, A):VDM_proof; (G, d, B):VDM_proof\<rbrakk> \<Longrightarrow>
  (G, Comp c d, \<lambda> s t . \<exists> r . A s r \<and> B r t):VDM_proof"

| VDMIff:
  "\<lbrakk> (G, c, A):VDM_proof; (G, d, B):VDM_proof\<rbrakk> \<Longrightarrow> 
  (G, Iff b c d,
     \<lambda> s t . (((evalB b (fst s)) \<longrightarrow> A s t) \<and> 
                      ((\<not> (evalB b (fst s))) \<longrightarrow> B s t))):VDM_proof"
(*VDMWhile:  "\<lbrakk>\<rhd> c : (\<lambda> s t . (evalB b s \<longrightarrow> I s t)); Trans I; Refl I\<rbrakk>
            \<Longrightarrow> \<rhd> (While b c) : (\<lambda> s t . I s t \<and> \<not> (evalB b t))"*)

| VDMWhile:
  "\<lbrakk> (G,c,B):VDM_proof;
        \<forall> s . (\<not> evalB b (fst s)) \<longrightarrow> A s s;
        \<forall> s r t. evalB b (fst s) \<longrightarrow> B s r \<longrightarrow> A r t \<longrightarrow> A s t \<rbrakk>
 \<Longrightarrow> (G, While b c, \<lambda> s t . A s t \<and> \<not> (evalB b (fst t))):VDM_proof"

| VDMCall:
  "({A} \<union> G, body, A):VDM_proof \<Longrightarrow> (G, Call, A):VDM_proof"

| VDMAx: "A \<in> G \<Longrightarrow>  (G, Call, A):VDM_proof"

| VDMConseq:
  "\<lbrakk> (G, c,A):VDM_proof; \<forall> s t. A s t \<longrightarrow> B s t\<rbrakk> \<Longrightarrow>
  (G, c, B):VDM_proof"

abbreviation VDM_deriv :: "[Assn set, OBJ, Assn] \<Rightarrow> bool" 
                   ("_ \<rhd> _ : _" [100,100] 50)
where "G \<rhd> c : A == (G,c,A) \<in> VDM_proof"

text\<open>The while-rule is in fact inter-derivable with the following rule.\<close>
lemma Hoare_While: 
 "G \<rhd> c : (\<lambda> s t . \<forall> r . evalB b (fst s) \<longrightarrow> I s r \<longrightarrow> I t r) \<Longrightarrow>
  G \<rhd> While b c : (\<lambda> s t. \<forall> r . I s r \<longrightarrow> (I t r \<and> \<not> evalB b (fst t)))"
apply (subgoal_tac "G \<rhd> (While b c) : 
           (\<lambda> s t . (\<lambda> s t . \<forall>r. I s r \<longrightarrow> I t r) s t \<and> \<not> (evalB b (fst t)))")
apply (erule VDMConseq)
apply simp
apply (rule VDMWhile) apply assumption apply simp apply simp
done

text\<open>Here's the proof in the opposite direction.\<close>


lemma VDMWhile_derivable:
  "\<lbrakk> G \<rhd> c : B; \<forall> s . (\<not> evalB b (fst s)) \<longrightarrow> A s s;
     \<forall> s r t. evalB b (fst s) \<longrightarrow> B s r \<longrightarrow> A r t \<longrightarrow> A s t \<rbrakk>
  \<Longrightarrow> G \<rhd> (While b c) : (\<lambda> s t . A s t \<and> \<not> (evalB b (fst t)))"
apply (rule VDMConseq)
apply (rule Hoare_While [of G c b "\<lambda> s r . \<forall> t . A s t \<longrightarrow> A r t"])
apply (erule VDMConseq) apply clarsimp
apply fast
done

subsubsection\<open>Soundness\<close>
(*<*)
lemma MAX:"Suc (max k m) \<le> n \<Longrightarrow> k \<le> n \<and> m \<le> n"
by (simp add: max_def, case_tac "k \<le> m", simp+)
(*>*)

text\<open>The following auxiliary lemma for loops is proven by induction
on $n$.\<close>

lemma SoundWhile[rule_format]:
 "(\<forall>n. G \<Turnstile>\<^sub>n c : B) 
    \<longrightarrow> (\<forall>s. (\<not> evalB b (fst s)) \<longrightarrow> A s s)
    \<longrightarrow> (\<forall>s. evalB b (fst s)
              \<longrightarrow> (\<forall>r. B s r \<longrightarrow> (\<forall>t. A r t \<longrightarrow> A s t)))
    \<longrightarrow> G \<Turnstile>\<^sub>n (While b c) : (\<lambda>s t. A s t \<and> \<not> evalB b (fst t))"
(*<*)
apply (induct n)
apply clarsimp apply (simp add: validn_def VDM_validn_def, clarsimp) 
  apply (drule Sem_no_zero_height_derivs) apply simp 
apply clarsimp apply (simp add: validn_def VDM_validn_def, clarsimp)  
  apply (erule Sem_eval_cases)
  prefer 2 apply clarsimp 
  apply clarsimp 
   apply (erule_tac x=n in allE, erule impE) apply (erule Ctxt_lowerm) apply simp
   apply (rotate_tac -1)
   apply (erule_tac x=ma in allE, clarsimp) 
   apply(erule impE) apply (erule Ctxt_lowerm) apply simp 
   apply (erule_tac x=na in allE, clarsimp) apply fast
done 
(*>*)

lemma SoundCall[rule_format]:
"\<lbrakk>\<forall>n. \<Turnstile>\<^sub>n ({A} \<union> G) \<longrightarrow> \<Turnstile>\<^sub>n body : A\<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>n G \<longrightarrow> \<Turnstile>\<^sub>n Call : A"
(*<*)
apply (induct_tac n)
apply (simp add: VDM_validn_def, clarsimp) 
  apply (drule Sem_no_zero_height_derivs) apply simp 
apply clarsimp
  apply (drule Ctxt_lowerm) apply (subgoal_tac "n < Suc n", assumption) apply simp apply clarsimp
  apply (drule ctxt_consn) apply assumption
  apply (simp add: VDM_validn_def, clarsimp)
  apply (erule Sem_eval_cases, clarsimp) 
done
(*>*)

lemma VDM_Sound_n: "G \<rhd> c: A \<Longrightarrow> (\<forall> n. G \<Turnstile>\<^sub>n c:A)"
(*<*)
apply (erule VDM_proof.induct)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, clarsimp)
  apply (drule MAX, clarsimp)
  apply (erule_tac x=n in allE, clarsimp, rotate_tac -1, erule_tac x=na in allE, clarsimp)
  apply (erule_tac x=n in allE, clarsimp, rotate_tac -1, erule_tac x=ma in allE, clarsimp)
  apply (rule_tac x=ab in exI, rule_tac x=bb in exI, fast)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, clarsimp)
   apply (erule thin_rl, rotate_tac 1, erule thin_rl, erule thin_rl)
     apply (erule_tac x=n in allE, clarsimp, erule_tac x=na in allE, clarsimp)
   apply (erule thin_rl, erule thin_rl)
     apply (erule_tac x=n in allE, clarsimp, erule_tac x=na in allE, clarsimp)
apply clarsimp
  apply (rule SoundWhile) apply fast
    apply (case_tac s, clarsimp)
    apply (case_tac s, clarsimp)
apply (simp add: validn_def, clarsimp)
  apply (rule SoundCall) prefer 2 apply assumption apply fastforce
apply (simp add: Ctxt_validn_def validn_def) apply fast
apply (simp add: validn_def VDM_validn_def) 
done
(*>*)

theorem VDM_Sound: "G \<rhd> c: A \<Longrightarrow> G \<Turnstile> c:A"
(*<*)
by (drule VDM_Sound_n, erule validn_valid) 
(*>*)

text\<open>A simple corollary is soundness w.r.t.~an empty context.\<close>

lemma VDM_Sound_emptyCtxt:"{} \<rhd> c : A \<Longrightarrow>  \<Turnstile> c : A"
(*<*)
apply (drule VDM_Sound)
apply (simp add: valid_def, erule mp) 
apply (simp add: Ctxt_valid_def)
done
(*>*)

subsubsection\<open>Derived rules\<close>

lemma WEAK[rule_format]:
  "G \<rhd> c : A \<Longrightarrow> (\<forall> H . G \<subseteq> H \<longrightarrow> H \<rhd> c :A)"
(*<*)
apply (erule VDM_proof.induct)
apply clarsimp apply (rule VDMSkip)
apply clarsimp apply (rule VDMAssign)
apply clarsimp apply (rule VDMNew)
apply (rule, rule) apply (rule VDMGet) 
apply (rule, rule) apply (rule VDMPut)
apply (rule, rule) apply (rule VDMComp) apply (erule_tac x=H in allE, simp) apply (erule_tac x=H in allE, simp) 
apply (rule,rule) apply (rule VDMIff)  apply (erule_tac x=H in allE, simp) apply (erule_tac x=H in allE, simp)  
apply (rule,rule) apply (rule VDMWhile) apply (erule_tac x=H in allE, simp)  apply (assumption) apply simp
apply (rule,rule) apply (rule VDMCall) apply (erule_tac x="({A} \<union> H)" in allE, simp) apply fast
apply (rule,rule) apply (rule VDMAx) apply fast
apply (rule,rule) apply (rule VDMConseq) apply (erule_tac x=H in allE, clarsimp) apply assumption apply assumption
done
(*>*)

lemma CutAux: 
 "(H \<rhd> c : A) \<Longrightarrow>
  (\<forall> G P D . (H = (insert P D) \<longrightarrow> G \<rhd> Call :P \<longrightarrow> (G \<subseteq> D) 
             \<longrightarrow> D \<rhd> c:A))"
(*<*)
apply (erule VDM_proof.induct)
apply clarify
apply (fast intro: VDMSkip)
apply (fast intro: VDMAssign)
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (rule VDMNew) 
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (rule VDMGet) 
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (rule VDMPut)
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (erule_tac x=Ga in allE) apply (erule_tac x=Ga in allE)
  apply (erule_tac x=P in allE) apply (erule_tac x=P in allE)
  apply (erule_tac x=D in allE, erule impE, assumption) 
  apply (erule_tac x=D in allE, erule impE, assumption)
  apply (rule VDMComp) apply simp apply simp 
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (erule_tac x=Ga in allE) apply (erule_tac x=Ga in allE)
  apply (erule_tac x=P in allE) apply (erule_tac x=P in allE)
  apply (erule_tac x=D in allE, erule impE, assumption) 
  apply (erule_tac x=D in allE, erule impE, assumption)
  apply (rule VDMIff) apply simp apply simp 
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (erule_tac x=Ga in allE) 
  apply (erule_tac x=P in allE) 
  apply (erule_tac x=D in allE, erule impE, assumption) 
  apply (rule VDMWhile) apply simp apply simp
  apply simp
apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply (erule_tac x=Ga in allE) 
  apply (erule_tac x=P in allE) 
  apply (erule_tac x="insert A D" in allE, erule impE, simp) 
  apply (rule VDMCall) apply fastforce
apply clarsimp
  apply (erule disjE)
  apply clarsimp apply (erule WEAK) apply assumption
  apply (erule VDMAx)
apply clarsimp
apply (subgoal_tac "D \<rhd>  c : A") 
apply (erule VDMConseq) apply simp
  apply simp
done
(*>*)

lemma Cut:"\<lbrakk> G \<rhd> Call : P ; (insert P G) \<rhd> c : A \<rbrakk> \<Longrightarrow> G \<rhd> c : A"
(*<*)by (drule CutAux , simp)(*>*)

definition verified::"Assn set \<Rightarrow> bool"
where "verified G = (\<forall> A . A:G \<longrightarrow> G \<rhd> body : A)"

lemma verified_preserved: "\<lbrakk>verified G; A:G\<rbrakk> \<Longrightarrow> verified (G - {A})"
(*<*)
apply (simp add: verified_def, (rule allI)+, rule)
apply (subgoal_tac "(G - {A}) \<rhd> Call:A")
(*now use the subgoal (G - {A}) \<rhd> Call:A to prove the goal*)
apply (subgoal_tac "G = insert A (G - {A})") prefer 2 apply fast
apply (erule_tac x=Aa in allE) 
apply (erule impE, simp)
apply (erule Cut)  apply simp
(* now prove the subgoal (G - {A}) \<rhd>  Call : A *)
  apply (erule_tac x=A in allE, clarsimp)
  apply (rule VDMCall) apply simp apply (erule WEAK) apply fast
done
(*>*)

(*<*)
lemma SetNonSingleton:
  "\<lbrakk>G \<noteq> {A}; A \<in> G\<rbrakk> \<Longrightarrow> \<exists>B. B \<noteq> A \<and> B \<in> G"
by auto

lemma MutrecAux[rule_format]: 
"\<forall> G . ((finite G \<and> card G = n \<and> verified G \<and> A : G) \<longrightarrow> {} \<rhd> Call:A)"
apply (induct n)
(*case n=0*)
apply clarsimp
(*Case n>0*)
apply clarsimp
apply (case_tac "G = {A}")
apply clarsimp
apply (erule_tac x="{A}" in allE)
apply (clarsimp, simp add:verified_def)
apply (rule VDMCall, clarsimp)
(*Case G has more entries than A*)
apply (drule SetNonSingleton, assumption) 
(* use the fact that there is another entry B:G*)
apply clarsimp
apply (subgoal_tac "(G - {B}) \<rhd> Call : B")
apply (erule_tac x="G - {B}" in allE)
apply (erule impE) apply (simp add: verified_preserved)
apply (erule impE) apply (simp add: card_Diff_singleton)
apply simp
(*the proof for (G - {B}) \<rhd>  Call : B *)
apply (simp add: verified_def)
apply (rotate_tac 3) apply (erule_tac x=B in allE, simp)
apply (rule VDMCall) apply simp apply (erule WEAK) apply fast
done
(*>*)

theorem Mutrec:
"\<lbrakk> finite G; card G = n; verified G; A : G \<rbrakk> \<Longrightarrow> {} \<rhd> Call:A"
(*<*) 
by (rule MutrecAux, fast)
(*>*)

subsubsection\<open>Completeness\<close>
definition SSpec::"OBJ \<Rightarrow> Assn"
where "SSpec c s t = (s,c \<Down> t)"

lemma SSpec_valid: "\<Turnstile> c : (SSpec c)"
(*<*)by (simp add: VDM_valid_def SSpec_def)(*>*)

lemma SSpec_strong: "\<Turnstile> c :A \<Longrightarrow> \<forall> s t . SSpec c s t \<longrightarrow> A s t"
(*<*)by (simp add: VDM_valid_def SSpec_def)(*>*)

lemma SSpec_derivable:"G \<rhd> Call : SSpec Call \<Longrightarrow> G \<rhd> c : SSpec c"
(*<*)
apply (induct c)
  apply (rule VDMConseq)
  apply (rule VDMSkip) apply (simp add: SSpec_def Sem_def, rule, rule, rule) apply (rule SemSkip) apply simp
  apply (rule VDMConseq)
  apply (rule VDMAssign) apply (simp add: SSpec_def Sem_def, rule, rule, rule) apply (rule SemAssign) apply simp
  apply (rule VDMConseq)
  apply (rule VDMNew) apply (simp only: SSpec_def Sem_def, rule, rule, rule, rule)
    apply (erule exE, erule conjE)
    apply (rule SemNew) apply assumption apply assumption
  apply (rule VDMConseq)
  apply (rule VDMGet) apply (simp only: SSpec_def Sem_def, rule, rule, rule, rule)
    apply (erule exE)+
    apply (erule conjE)+
    apply (rule SemGet) apply assumption apply assumption apply assumption apply assumption
  apply (rule VDMConseq)
  apply (rule VDMPut) apply (simp only: SSpec_def Sem_def, rule, rule, rule, rule)
    apply (erule exE)+
    apply (erule conjE)+
    apply (rule SemPut) apply assumption apply assumption apply assumption
apply clarsimp
  apply (rule VDMConseq)
  apply (rule VDMComp) apply assumption+ apply (simp add: SSpec_def Sem_def, clarsimp) 
  apply rule apply (rule SemComp) apply assumption+ apply simp
apply clarsimp
apply (rule VDMConseq)
  apply (erule VDMWhile) 
    prefer 3
    apply (rename_tac BExpr c)
    apply (subgoal_tac "\<forall>s t. SSpec (While BExpr c) s t \<and> \<not> evalB BExpr (fst t) \<longrightarrow> SSpec (While BExpr c) s t", assumption)
    apply simp
    apply (simp only: SSpec_def Sem_def) apply (rule, rule, rule) apply (erule SemWhileF) apply simp
    apply (simp only: SSpec_def Sem_def) apply (rule, rule, rule) 
      apply (rule, rule, rule) apply (erule exE)+ apply (rule, erule SemWhileT) apply assumption+ apply simp
apply clarsimp
apply (rule VDMConseq)
  apply (rule VDMIff) apply assumption+ apply (simp only: SSpec_def Sem_def)
  apply (erule thin_rl, erule thin_rl) 
  apply (rule, rule, rule)
  apply (erule conjE)
  apply (rename_tac BExpr c1 c2 s t)
  apply (case_tac "evalB BExpr (fst s)")
  apply (erule impE, assumption) apply (erule exE) apply (rule, rule SemTrue) apply assumption+ 
  apply (rotate_tac 2, erule impE, assumption) apply (erule exE) apply (rule, rule SemFalse) apply assumption+ 
done
(*>*)

definition StrongG :: "Assn set"
where "StrongG = {SSpec Call}"

lemma StrongG_Body: "StrongG \<rhd> body : SSpec Call"
(*<*)
apply (subgoal_tac "StrongG \<rhd> body : SSpec body")
  apply (erule VDMConseq) apply (simp add: SSpec_def Sem_def, clarsimp)
  apply (rule, erule SemCall)
apply (rule SSpec_derivable) apply (rule VDMAx) apply (simp add: StrongG_def)
done
(*>*)

lemma StrongG_verified: "verified StrongG"
(*<*)
apply (simp add: verified_def)
apply (rule allI)+
apply rule
apply (subgoal_tac "StrongG \<rhd> body : SSpec Call")
apply (simp add: StrongG_def)
apply (rule StrongG_Body)
done
(*>*)

lemma SSpec_derivable_empty:"{} \<rhd> c : SSpec c"
(*<*)
apply (rule Cut)
apply (rule Mutrec) apply (subgoal_tac "finite StrongG", assumption)
  apply (simp add: StrongG_def)
  apply (simp add: StrongG_def)
  apply (rule StrongG_verified)
  apply (simp add: StrongG_def)
  apply (rule SSpec_derivable) apply (rule VDMAx) apply simp
done
(*>*)

theorem VDM_Complete: "\<Turnstile> c : A \<Longrightarrow> {} \<rhd> c : A"
(*<*)
apply (rule VDMConseq)
apply (rule SSpec_derivable_empty)
apply (erule SSpec_strong)
done
(*>*)

(*<*)

lemma Ctxt_valid_verified: "\<Turnstile> G \<Longrightarrow> verified G"
(*<*)
apply (simp add: Ctxt_valid_def verified_def, clarsimp)
apply (erule_tac x=A in allE, simp)
apply (subgoal_tac "\<Turnstile> body : A")
apply (rotate_tac 1, erule thin_rl, drule VDM_Complete) apply (erule WEAK) apply fast
apply (simp only: VDM_valid_def Sem_def)
apply (rule, rule, rule)
apply (erule exE)
apply (erule_tac x=s in allE, erule_tac x=t in allE, erule mp)
apply (rule, erule SemCall)
done
(*>*)

lemma Ctxt_verified_valid: "\<lbrakk>verified G; finite G\<rbrakk> \<Longrightarrow> \<Turnstile> G"
(*<*)
apply (subgoal_tac "(\<forall> A . A:G \<longrightarrow> G \<rhd> body : A)")
prefer 2 apply (simp add: verified_def)
apply (simp add: Ctxt_valid_def, clarsimp)
apply (erule_tac x=A in allE, simp)
apply (rule VDM_Sound_emptyCtxt)
apply (rule Mutrec, assumption) 
  apply (insert card_def) apply fast
  apply assumption 
  apply assumption 
done
(*>*)

text\<open>End of theory VDM_Obj\<close>
end
