(*File: VDM.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory VDM imports IMP begin
section\<open>Program logic\<close>

text\<open>\label{sec:VDM} The program logic is a partial correctness logic
in (precondition-less) VDM style. This means that assertions are
binary predicates over states and relate the initial and final
states of a terminating execution.\<close>

subsection \<open>Assertions and their semantic validity\<close>

text\<open>Assertions are binary predicates over states, i.e.~are of type\<close>

type_synonym "VDMAssn" = "State \<Rightarrow> State \<Rightarrow> bool"

text\<open>Command $c$ satisfies assertion $A$ if all (terminating)
operational behaviours are covered by the assertion.\<close>

definition VDM_valid :: "IMP \<Rightarrow> VDMAssn \<Rightarrow> bool"
                       (" \<Turnstile> _ : _ " [100,100] 100)
where "\<Turnstile> c : A = (\<forall> s t . (s,c \<Down> t) \<longrightarrow> A s t)"

text\<open>A variation of this property for the height-indexed operational
semantics,\ldots\<close>

definition VDM_validn :: "nat \<Rightarrow> IMP \<Rightarrow> VDMAssn \<Rightarrow> bool"
                        (" \<Turnstile>\<^sub>_ _ : _ " [100,100,100] 100)
where "\<Turnstile>\<^sub>n c : A = (\<forall> m . m \<le> n --> (\<forall> s t . (s,c \<rightarrow>\<^sub>m t) --> A s t))"

text\<open>\ldots plus the obvious relationships.\<close>
lemma VDM_valid_validn: "\<Turnstile> c:A \<Longrightarrow> \<Turnstile>\<^sub>n c:A"
(*<*)
by (simp add: VDM_valid_def VDM_validn_def Sem_def, fastforce)
(*>*)

lemma VDM_validn_valid: "(\<forall> n . \<Turnstile>\<^sub>n c:A) \<Longrightarrow> \<Turnstile> c:A"
(*<*)
by (simp add: VDM_valid_def VDM_validn_def Sem_def, fastforce)
(*>*)

lemma VDM_lowerm: "\<lbrakk> \<Turnstile>\<^sub>n c:A; m \<le> n \<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>m c:A"
(*<*)
apply (simp add: VDM_validn_def, clarsimp)
apply (erule_tac x="ma" in allE, simp)
done
(*>*)

text\<open>Proof contexts are simply sets of assertions -- each entry
represents an assumption for the unnamed procedure. In particular, a
context is valid if each entry is satisfied by the method call
instruction.\<close>

definition Ctxt_valid :: "VDMAssn set \<Rightarrow> bool" (" \<Turnstile> _ " [100] 100)
where "\<Turnstile> G = (\<forall> A . A \<in> G \<longrightarrow> (\<Turnstile> Call : A))"

text\<open>Again, a relativised sibling \ldots\<close>

definition Ctxt_validn :: "nat \<Rightarrow> (VDMAssn set) \<Rightarrow> bool"
                         (" \<Turnstile>\<^sub>_ _  " [100,100] 100)
where "\<Turnstile>\<^sub>n G = (\<forall> m . m \<le> n \<longrightarrow> (\<forall> A. A \<in> G \<longrightarrow> ( \<Turnstile>\<^sub>m Call : A)))"

text\<open>satisfies the obvious properties.\<close>

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
by (simp add: Ctxt_validn_def)
(*>*)

text\<open>A judgement is valid if the validity of the context implies that
of the commmand-assertion pair.\<close>

definition valid :: "(VDMAssn set) \<Rightarrow> IMP \<Rightarrow> VDMAssn \<Rightarrow> bool"
                    ("_ \<Turnstile> _ : _ " [100,100,100] 100)
where "G \<Turnstile> c : A = (\<Turnstile> G \<longrightarrow> \<Turnstile> c : A)"

text\<open>And, again, a relatived notion of judgement validity.\<close>

definition validn :: 
 "(VDMAssn set) \<Rightarrow> nat \<Rightarrow> IMP \<Rightarrow> VDMAssn \<Rightarrow> bool"
  ("_ \<Turnstile>\<^sub>_ _ : _" [100,100,100,100] 100)
where "G \<Turnstile>\<^sub>n c : A = (\<Turnstile>\<^sub>n G \<longrightarrow> \<Turnstile>\<^sub>n c : A)"

lemma validn_valid: "(\<forall> n . G \<Turnstile>\<^sub>n c : A) \<Longrightarrow> G \<Turnstile> c : A"
(*<*)
apply (simp add: valid_def validn_def, clarsimp)
apply (rule VDM_validn_valid, clarsimp) 
apply (erule_tac x=n in allE, erule mp)
apply (erule Ctxt_valid_validn)
done
(*>*)

lemma ctxt_consn: "\<lbrakk> \<Turnstile>\<^sub>n G;  \<Turnstile>\<^sub>n Call:A \<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>n ({A} \<union> G)"
(*<*)
apply (simp add: Ctxt_validn_def)  apply clarsimp 
apply (erule_tac x=m in allE, clarsimp) 
apply (erule VDM_lowerm) apply assumption
done
(*>*)

subsection\<open>Proof system\<close>

inductive_set
  VDM_proof :: "(VDMAssn set \<times> IMP \<times> VDMAssn) set"
where

VDMSkip:   "(G, Skip, \<lambda> s t . t=s) : VDM_proof"

| VDMAssign:
  "(G, Assign x e, \<lambda> s t . t = (update s x (evalE e s))) : VDM_proof"

| VDMComp:
  "\<lbrakk> (G, c1, A1) : VDM_proof; (G, c2, A2) : VDM_proof\<rbrakk> \<Longrightarrow>
   (G, Comp c1 c2, \<lambda> s t . \<exists> r . A1 s r \<and> A2 r t) : VDM_proof"

| VDMIff:
  "\<lbrakk> (G, c1, A):VDM_proof; (G, c2, B):VDM_proof\<rbrakk> \<Longrightarrow>
   (G, Iff b c1 c2, \<lambda> s t . (((evalB b s) \<longrightarrow> A s t) \<and> 
                                    ((\<not> (evalB b s)) \<longrightarrow> B s t))) : VDM_proof"

(*VDMWhile:  "\<lbrakk>\<rhd> C : (\<lambda> s t . (evalB b s \<longrightarrow> I s t)); Trans I; Refl I\<rbrakk>
            \<Longrightarrow> \<rhd> (While b C) : (\<lambda> s t . I s t \<and> \<not> (evalB b t))"*)
| VDMWhile:
  "\<lbrakk> (G, c, B):VDM_proof;  \<forall> s . (\<not> evalB b s) \<longrightarrow> A s s;
             \<forall> s r t. evalB b s \<longrightarrow> B s r \<longrightarrow> A r t \<longrightarrow> A s t \<rbrakk> \<Longrightarrow>
   (G, While b c, \<lambda> s t . A s t \<and> \<not> (evalB b t)) : VDM_proof"

| VDMCall:
  "({A} \<union> G, body, A):VDM_proof \<Longrightarrow> (G, Call, A):VDM_proof"

| VDMAx: "A \<in> G \<Longrightarrow>  (G, Call, A):VDM_proof"

| VDMConseq:
  "\<lbrakk> (G, c, A):VDM_proof; \<forall> s t. A s t \<longrightarrow> B s t\<rbrakk> \<Longrightarrow>
   (G, c, B):VDM_proof"
(*
VDMSkip:   "G \<rhd> Skip : (\<lambda> s t . t=s)"
VDMAssign: "G \<rhd> (Assign x e) : (\<lambda> s t . t = (update s x (evalE e s)))"
VDMComp:   "\<lbrakk> G \<rhd> c1:A1; G \<rhd> c2:A2\<rbrakk> 
           \<Longrightarrow> G \<rhd> (Comp c1 c2) : (\<lambda> s t . \<exists> r . A1 s r \<and> A2 r t)"
VDMIff:    "\<lbrakk> G \<rhd> c1 : A; G \<rhd> c2 :B\<rbrakk>
            \<Longrightarrow> G \<rhd> (Iff b c1 c2) : (\<lambda> s t . (((evalB b s) \<longrightarrow> A s t) \<and> 
                                             ((\<not> (evalB b s)) \<longrightarrow> B s t)))"
(*VDMWhile:  "\<lbrakk>\<rhd> C : (\<lambda> s t . (evalB b s \<longrightarrow> I s t)); Trans I; Refl I\<rbrakk>
            \<Longrightarrow> \<rhd> (While b C) : (\<lambda> s t . I s t \<and> \<not> (evalB b t))"*)
VDMWhile:  "\<lbrakk> G \<rhd> c : B; 
              \<forall> s . (\<not> evalB b s) \<longrightarrow> A s s;
              \<forall> s r t. evalB b s \<longrightarrow> B s r \<longrightarrow> A r t \<longrightarrow> A s t \<rbrakk>
            \<Longrightarrow> G \<rhd> (While b c) : (\<lambda> s t . A s t \<and> \<not> (evalB b t))"
VDMCall: "({A} \<union> G) \<rhd> body : A \<Longrightarrow> G \<rhd> Call : A"
VDMAx: "A \<in> G \<Longrightarrow>  G \<rhd> Call : A"
VDMConseq: "\<lbrakk> G \<rhd> c : A; \<forall> s t. A s t \<longrightarrow> B s t\<rbrakk> \<Longrightarrow> G \<rhd> c : B"
*)

abbreviation
  VDM_deriv :: "[VDMAssn set, IMP, VDMAssn] \<Rightarrow> bool"
                ("_ \<rhd> _ : _" [100,100,100] 100)
where "G \<rhd> c : A == (G,c,A) \<in> VDM_proof"

text\<open>The while-rule is in fact inter-derivable with the following rule.\<close>

lemma Hoare_While: 
   "G \<rhd> c : (\<lambda> s s' . \<forall> r . evalB b s \<longrightarrow> I s r \<longrightarrow> I s' r) \<Longrightarrow>
    G \<rhd> While b c : (\<lambda> s s'. \<forall> r . I s r \<longrightarrow> (I s' r \<and> \<not> evalB b s'))"
apply (subgoal_tac "G \<rhd> (While b c) : 
           (\<lambda> s t . (\<lambda> s t . \<forall>r. I s r \<longrightarrow> I t r) s t \<and> \<not> (evalB b t))")
apply (erule VDMConseq)
apply simp
apply (rule VDMWhile) apply assumption apply simp apply simp
done

text\<open>Here's the proof in the opposite direction.\<close>

lemma VDMWhile_derivable:
  "\<lbrakk> G \<rhd> c : B; \<forall> s . (\<not> evalB b s) \<longrightarrow> A s s;
     \<forall> s r t. evalB b s \<longrightarrow> B s r \<longrightarrow> A r t \<longrightarrow> A s t \<rbrakk>
  \<Longrightarrow> G \<rhd> (While b c) : (\<lambda> s t . A s t \<and> \<not> (evalB b t))"
apply (rule VDMConseq)
apply (rule Hoare_While [of G c b "\<lambda> s r . \<forall> t . A s t \<longrightarrow> A r t"])
apply (erule VDMConseq) apply clarsimp
apply fast
done

subsection\<open>Soundness\<close>
(*<*)
lemma MAX:"Suc (max k m) \<le> n \<Longrightarrow> k \<le> n \<and> m \<le> n"
by (simp add: max_def, case_tac "k \<le> m", simp+)
(*>*)

(*<*)
definition SoundWhileProp::"nat \<Rightarrow> (VDMAssn set) \<Rightarrow> IMP \<Rightarrow> VDMAssn \<Rightarrow> BExpr \<Rightarrow> VDMAssn \<Rightarrow> bool"
where "SoundWhileProp n G c B b A =
   ((\<forall>m. G \<Turnstile>\<^sub>m c : B) \<longrightarrow> (\<forall>s. (\<not> evalB b s) \<longrightarrow> A s s) \<longrightarrow>
    (\<forall>s. evalB b s \<longrightarrow> (\<forall>r. B s r \<longrightarrow> (\<forall>t. A r t \<longrightarrow> A s t))) \<longrightarrow>
   G \<Turnstile>\<^sub>n (While b c) : (\<lambda>s t. A s t \<and> \<not> evalB b t))"

lemma SoundWhileAux[rule_format]: "SoundWhileProp n G c B b A"
apply (induct n)
apply (simp_all add: SoundWhileProp_def)
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

text\<open>An auxiliary lemma stating the soundness of the while rule. Its
proof is by induction on $n$.\<close>

lemma SoundWhile[rule_format]:
  "(\<forall>m. G \<Turnstile>\<^sub>m c : B) \<longrightarrow> (\<forall>s. (\<not> evalB b s) \<longrightarrow> A s s) \<longrightarrow>
    (\<forall>s. evalB b s \<longrightarrow> (\<forall>r. B s r \<longrightarrow> (\<forall>t. A r t \<longrightarrow> A s t))) \<longrightarrow>
   G \<Turnstile>\<^sub>n (While b c) : (\<lambda>s t. A s t \<and> \<not> evalB b t)"
(*<*)
apply (subgoal_tac "SoundWhileProp n G c B b A")
  apply (simp add: SoundWhileProp_def)
apply (rule SoundWhileAux)
done 
(*>*)

text\<open>Similarly, an auxiliary lemma for procedure invocations. Again,
the proof proceeds by induction on $n$.\<close>

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

text\<open>The heart of the soundness proof is the following lemma which is
proven by induction on the judgement $G \rhd c :A$.\<close>

lemma VDM_Sound_n: "G \<rhd> c: A \<Longrightarrow> (\<forall> n . G \<Turnstile>\<^sub>n c:A)"
(*<*)
apply (erule VDM_proof.induct)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, simp)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, clarsimp)
  apply (drule MAX, clarsimp)
  apply (erule_tac x=n in allE, clarsimp, rotate_tac -1, erule_tac x=na in allE, clarsimp)
  apply (erule_tac x=n in allE, clarsimp, rotate_tac -1, erule_tac x=ma in allE, clarsimp)
  apply (rule_tac x=r in exI, fast)
apply (simp add: validn_def VDM_validn_def)
  apply(clarsimp, erule Sem_eval_cases, clarsimp)
   apply (erule thin_rl, rotate_tac 1, erule thin_rl, erule thin_rl)
     apply (erule_tac x=n in allE, clarsimp, erule_tac x=na in allE, clarsimp)
   apply (erule thin_rl, erule thin_rl)
     apply (erule_tac x=n in allE, clarsimp, erule_tac x=na in allE, clarsimp)
apply clarsimp
  apply (rule SoundWhile) apply fast apply simp apply simp apply clarsimp
apply (simp add: validn_def, clarsimp)
  apply (rule SoundCall) prefer 2 apply assumption apply fastforce
apply (simp add: Ctxt_validn_def validn_def) 
apply (simp add: validn_def VDM_validn_def) 
done
(*>*)

text\<open>Combining this result with lemma \<open>validn_valid\<close>, we obtain soundness in contexts,\ldots\<close>

theorem VDM_Sound: "G \<rhd> c: A \<Longrightarrow> G \<Turnstile> c:A"
(*<*)
by (drule VDM_Sound_n, erule validn_valid) 
(*>*)

text\<open>\ldots and consequently soundness w.r.t.~empty
contexts.\<close>

lemma VDM_Sound_emptyCtxt:"{} \<rhd> c : A \<Longrightarrow> \<Turnstile> c : A"
(*<*)
apply (drule VDM_Sound)
apply (simp add: valid_def, erule mp) 
apply (simp add: Ctxt_valid_def)
done
(*>*)

subsection\<open>Admissible rules\<close>

text\<open>A weakening rule and some cut rules are easily derived.\<close>

lemma WEAK[rule_format]: 
  "G \<rhd> c : A \<Longrightarrow> (\<forall> H . G \<subseteq> H \<longrightarrow> H \<rhd> c :A)"
(*<*)
apply (erule VDM_proof.induct)
apply clarsimp apply (rule VDMSkip)
apply clarsimp apply (rule VDMAssign)
apply clarsimp apply (rule VDMComp) apply (erule_tac x=H in allE, simp) apply (erule_tac x=H in allE, simp) 
apply clarsimp apply (rule VDMIff)  apply (erule_tac x=H in allE, simp) apply (erule_tac x=H in allE, simp)  
apply clarsimp apply (rule VDMWhile) apply (erule_tac x=H in allE, simp)  apply (assumption) apply simp
apply clarsimp apply (rule VDMCall) apply (erule_tac x="({A} \<union> H)" in allE, simp) apply fast
apply clarsimp apply (rule VDMAx) apply fast
apply clarsimp apply (rule VDMConseq) apply (erule_tac x=H in allE, clarsimp) apply assumption apply assumption
done
(*>*)

(*<*)
definition CutAuxProp::"VDMAssn set \<Rightarrow> IMP \<Rightarrow> VDMAssn \<Rightarrow> bool"
where "CutAuxProp H c A =
  (\<forall> G P D . (H = (insert P D) \<longrightarrow> G \<rhd> Call :P \<longrightarrow> (G \<subseteq> D) \<longrightarrow> D \<rhd> c:A))"

lemma CutAux1:"(H \<rhd> c : A) \<Longrightarrow> CutAuxProp H c A"
apply (erule VDM_proof.induct)
apply (simp_all add: add: CutAuxProp_def)
apply clarify
apply (fast intro: VDMSkip)
apply (fast intro: VDMAssign)
apply clarsimp 
  apply (erule_tac x=Ga in allE) apply (erule_tac x=Ga in allE)
  apply (erule_tac x=P in allE) apply (erule_tac x=P in allE)
  apply (erule_tac x=D in allE, simp) apply (erule_tac x=D in allE, simp)
  apply (rule VDMComp) apply assumption+
apply clarsimp 
  apply (erule_tac x=Ga in allE) apply (erule_tac x=Ga in allE)
  apply (erule_tac x=P in allE) apply (erule_tac x=P in allE)
  apply (erule_tac x=D in allE, simp) apply (erule_tac x=D in allE, simp)
  apply (rule VDMIff) apply assumption+
apply clarsimp 
  apply (erule_tac x=Ga in allE) 
  apply (erule_tac x=P in allE) 
  apply (erule_tac x=D in allE, simp) 
  apply (rule VDMWhile) apply assumption+
  apply simp
apply clarsimp 
  apply (erule_tac x=Ga in allE) 
  apply (erule_tac x=P in allE) 
  apply (erule_tac x="insert A D" in allE, simp) 
  apply (rule VDMCall) apply fastforce
apply clarsimp
  apply (erule disjE)
  apply clarsimp apply (erule WEAK) apply assumption
  apply (erule VDMAx)
apply clarsimp
apply (subgoal_tac "D \<rhd>  c : A") 
apply (erule VDMConseq) apply assumption  
  apply simp
done
(*>*)

lemma CutAux: 
  "\<lbrakk>H \<rhd> c : A; H = insert P D; G \<rhd> Call :P; G \<subseteq> D\<rbrakk> \<Longrightarrow> D \<rhd> c:A"
(*<*)
by (drule CutAux1, simp add: CutAuxProp_def)
(*>*)

lemma Cut:"\<lbrakk> G \<rhd> Call : P ; (insert P G) \<rhd> c : A \<rbrakk> \<Longrightarrow> G \<rhd> c : A"
(*<*)
apply (rotate_tac -1, drule CutAux)
apply (fastforce, assumption)
apply (simp, assumption)
done
(*>*)

text\<open>We call context $G$ verified if all entries are justified by
derivations for the procedure body.\<close>

definition verified::"VDMAssn set \<Rightarrow> bool"
where "verified G = (\<forall> A . A:G \<longrightarrow> G \<rhd> body : A)"

text\<open>The property is preserved by sub-contexts\<close>

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

text\<open>The \<open>Mutrec\<close> rule allows us to eliminate verified (finite)
contexts. Its proof proceeds by induction on $n$.\<close>

theorem Mutrec:
"\<lbrakk> finite G; card G = n; verified G; A : G \<rbrakk> \<Longrightarrow> {} \<rhd> Call:A"
(*<*) 
by (rule MutrecAux, fast)
(*>*)

text\<open>In particular, \<open>Mutrec\<close> may be used to show that verified
finite contexts are valid.\<close>

lemma Ctxt_verified_valid: "\<lbrakk>verified G; finite G\<rbrakk> \<Longrightarrow> \<Turnstile> G"
(*<*)
apply (subgoal_tac "(\<forall> A . A:G \<longrightarrow> G \<rhd> body : A)")
prefer 2 apply (simp add: verified_def)
apply (simp add: Ctxt_valid_def, clarsimp)
apply (erule_tac x=A in allE, simp)
apply (rule VDM_Sound_emptyCtxt)
apply (subgoal_tac "card G = card G")
apply (rule Mutrec, assumption)  apply assumption+ apply simp
(*  apply (simp add: card_def)*)
done
(*>*)

subsection\<open>Completeness\<close>

text\<open>Strongest specifications, given precisely by the operational
behaviour.\<close>

definition SSpec::"IMP \<Rightarrow> VDMAssn"
where "SSpec c s t = s,c \<Down> t"

text\<open>Strongest specifications are valid \ldots\<close>
lemma SSpec_valid: "\<Turnstile> c : (SSpec c)"
(*<*)by (simp add: VDM_valid_def SSpec_def)(*>*)

text\<open>and imply any other valid assertion for the same program (hence
their name).\<close>

lemma SSpec_strong: "\<Turnstile> c :A \<Longrightarrow> \<forall> s t . SSpec c s t \<longrightarrow> A s t"
(*<*)by (simp add: VDM_valid_def SSpec_def)(*>*)

text\<open>By induction on $c$ we show the following.\<close>

lemma SSpec_derivable:"G \<rhd> Call : SSpec Call \<Longrightarrow> G \<rhd> c : SSpec c"
(*<*)
apply (induct c)
  apply (rule VDMConseq)
  apply (rule VDMSkip) apply (simp add: SSpec_def Sem_def, rule, rule) apply (rule SemSkip)
  apply (rule VDMConseq)
  apply (rule VDMAssign) apply (simp add: SSpec_def Sem_def, rule, rule) apply (rule SemAssign) apply simp
apply clarsimp
  apply (rule VDMConseq)
  apply (rule VDMComp) apply assumption+ apply (simp add: SSpec_def Sem_def, clarsimp) 
  apply rule apply (rule SemComp) apply assumption+ apply simp
apply clarsimp
apply (rename_tac BExpr c)
apply (rule VDMConseq)
  apply (erule VDMWhile) 
    prefer 3 apply (subgoal_tac "\<forall>s t. SSpec (While BExpr c) s t \<and> \<not> evalB BExpr t \<longrightarrow> SSpec (While BExpr c) s t", assumption)
    apply simp
    apply (simp add: SSpec_def Sem_def, clarsimp) apply (rule, erule SemWhileF) apply simp
    apply (simp add: SSpec_def Sem_def, clarsimp) apply (rule, erule SemWhileT) apply assumption+ apply simp
apply clarsimp
apply (rule VDMConseq)
  apply (rule VDMIff) apply assumption+ apply (simp add: SSpec_def Sem_def, clarsimp)
  apply (erule thin_rl, erule thin_rl)
  apply (rename_tac BExpr c1 c2 s t)
  apply (case_tac "evalB BExpr s")
  apply clarsimp apply (rule, rule SemTrue) apply assumption+ 
  apply clarsimp apply (rule, rule SemFalse) apply (assumption, assumption)
apply assumption 
done
(*>*)

text\<open>The (singleton) strong context contains the strongest
specification of the procedure.\<close>

definition StrongG :: "VDMAssn set"
where "StrongG = {SSpec Call}"

text\<open>By construction, the strongest specification of the procedure's
body can be verified with respect to this context.\<close>

lemma StrongG_Body: "StrongG \<rhd> body : SSpec Call"
(*<*)
apply (subgoal_tac "StrongG \<rhd> body : SSpec body")
  apply (erule VDMConseq) apply (simp add: SSpec_def Sem_def, clarsimp)
  apply (rule, erule SemCall)
apply (rule SSpec_derivable) apply (rule VDMAx) apply (simp add: StrongG_def)
done
(*>*)

text\<open>Thus, the strong context is verified.\<close>

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

text\<open>Using this result and the rules \<open>Cut\<close> and \<open>Mutrec\<close>, we
show that arbitrary commands satisfy their strongest specification
with respect to the empty context.\<close>

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

text\<open>From this, we easily obtain (relative) completeness.\<close>

theorem VDM_Complete: "\<Turnstile> c : A \<Longrightarrow> {} \<rhd> c : A"
(*<*)
apply (rule VDMConseq)
apply (rule SSpec_derivable_empty)
apply (erule SSpec_strong)
done
(*>*)

text\<open>Finally, it is easy to show that valid contexts are verified.\<close>

lemma Ctxt_valid_verified: "\<Turnstile> G \<Longrightarrow> verified G"
(*<*)
apply (simp add: Ctxt_valid_def verified_def, clarsimp)
apply (erule_tac x=A in allE, simp)
apply (subgoal_tac "\<Turnstile> body : A")
apply (rotate_tac 1, erule thin_rl, drule VDM_Complete) apply (erule WEAK) apply fast
apply (simp add: VDM_valid_def Sem_def, clarsimp)
apply (erule_tac x=s in allE, erule_tac x=t in allE, erule mp)
apply (rule, erule SemCall)
done
(*>*)
text\<open>End of theory VDM\<close>
end
