(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Type_System
imports Language_Composition
begin

locale Type_System = 
  SSP? : Strongly_Secure_Programs "E" "BMap" "DA" 
  for E :: "('exp, 'id, 'val) Evalfunction"
  and BMap :: "'val \<Rightarrow> bool"
  and DA :: "('id, 'd::order) DomainAssignment"
+
fixes
AssignSideCondition :: "'id \<Rightarrow> 'exp \<Rightarrow> bool"
and WhileSideCondition :: "'exp \<Rightarrow> bool"
and IfSideCondition :: 
  "'exp \<Rightarrow> ('exp,'id) MWLfCom \<Rightarrow> ('exp,'id) MWLfCom \<Rightarrow> bool" 
assumes semAssignSC: "AssignSideCondition x e \<Longrightarrow> e \<equiv>\<^bsub>DA x\<^esub> e"
and semWhileSC: "WhileSideCondition e \<Longrightarrow> \<forall>d. e \<equiv>\<^bsub>d\<^esub> e"
and semIfSC: "IfSideCondition e c1 c2 \<Longrightarrow> \<forall>d. e \<equiv>\<^bsub>d\<^esub> e \<or> [c1] \<approx>\<^bsub>d\<^esub> [c2]"
begin

\<comment> \<open>Security typing rules for the language commands\<close>
inductive
ComSecTyping :: "('exp, 'id) MWLfCom \<Rightarrow> bool"
  ("\<turnstile>\<^bsub>\<C>\<^esub> _")
and ComSecTypingL :: "('exp,'id) MWLfCom list \<Rightarrow> bool"
   ("\<turnstile>\<^bsub>\<V>\<^esub> _")
where
skip: "\<turnstile>\<^bsub>\<C>\<^esub> skip" |
Assign: "\<lbrakk> AssignSideCondition x e \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> x := e" |
Fork: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c; \<turnstile>\<^bsub>\<V>\<^esub> V \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> fork c V" |
Seq: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c1; \<turnstile>\<^bsub>\<C>\<^esub> c2 \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> c1;c2" |
While: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c; WhileSideCondition b \<rbrakk> 
     \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> while b do c od" |
If: "\<lbrakk> \<turnstile>\<^bsub>\<C>\<^esub> c1; \<turnstile>\<^bsub>\<C>\<^esub> c2; IfSideCondition b c1 c2 \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^bsub>\<C>\<^esub> if b then c1 else c2 fi" |
Parallel: "\<lbrakk> \<forall>i < length V. \<turnstile>\<^bsub>\<C>\<^esub> V!i \<rbrakk> \<Longrightarrow> \<turnstile>\<^bsub>\<V>\<^esub> V"

inductive_cases parallel_cases:
"\<turnstile>\<^bsub>\<V>\<^esub> V"

\<comment> \<open>soundness proof of abstract type system\<close>
theorem ComSecTyping_single_is_sound:
"\<turnstile>\<^bsub>\<C>\<^esub> c \<Longrightarrow> Strongly_Secure [c]"
by (induct rule: ComSecTyping_ComSecTypingL.inducts(1)
    [of _ _ "Strongly_Secure"],
  auto simp add: Strongly_Secure_def,
  metis Strongly_Secure_Skip,
  metis Strongly_Secure_Assign semAssignSC,
  metis Compositionality_Fork,
  metis Compositionality_Seq,
  metis Compositionality_While semWhileSC,
  metis Compositionality_If semIfSC,
  metis parallel_composition)

theorem ComSecTyping_list_is_sound:
"\<turnstile>\<^bsub>\<V>\<^esub> V \<Longrightarrow> Strongly_Secure V"
by (metis ComSecTyping_single_is_sound Strongly_Secure_def 
  parallel_composition parallel_cases)

end

end
