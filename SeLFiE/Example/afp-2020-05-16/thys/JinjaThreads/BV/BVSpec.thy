(*  Title:      JinjaThreads/BV/BVSpec.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler

    Based on the theory Jinja/BV/BVSpec
*)

section \<open>The Bytecode Verifier \label{sec:BVSpec}\<close>

theory BVSpec
imports
  Effect
begin

text \<open>
  This theory contains a specification of the BV. The specification
  describes correct typings of method bodies; it corresponds 
  to type \emph{checking}.
\<close>

\<comment> \<open>The method type only contains declared classes:\<close>
definition check_types :: "'m prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty\<^sub>i' err list \<Rightarrow> bool"
where  
  "check_types P mxs mxl \<tau>s \<equiv> set \<tau>s \<subseteq> states P mxs mxl"

\<comment> \<open>An instruction is welltyped if it is applicable and its effect\<close>
\<comment> \<open>is compatible with the type at all successor instructions:\<close>
definition wt_instr :: "['m prog,ty,nat,pc,ex_table,'addr instr,pc,ty\<^sub>m] \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> _,_ :: _" [60,0,0,0,0,0,0,61] 60)
where
  "P,T,mxs,mpc,xt \<turnstile> i,pc :: \<tau>s \<equiv>
  app i P mxs T pc mpc xt (\<tau>s!pc) \<and> 
  (\<forall>(pc',\<tau>') \<in> set (eff i P pc xt (\<tau>s!pc)). P \<turnstile> \<tau>' \<le>' \<tau>s!pc')"

\<comment> \<open>The type at @{text "pc=0"} conforms to the method calling convention:\<close>
definition wt_start :: "['m prog,cname,ty list,nat,ty\<^sub>m] \<Rightarrow> bool"
where
  "wt_start P C Ts mxl\<^sub>0 \<tau>s \<equiv>
  P \<turnstile> Some ([],OK (Class C)#map OK Ts@replicate mxl\<^sub>0 Err) \<le>' \<tau>s!0"

\<comment> \<open>A method is welltyped if the body is not empty,\<close>
\<comment> \<open>if the method type covers all instructions and mentions\<close>
\<comment> \<open>declared classes only, if the method calling convention is respected, and\<close>
\<comment> \<open>if all instructions are welltyped.\<close>
definition wt_method :: "['m prog,cname,ty list,ty,nat,nat,'addr instr list, ex_table,ty\<^sub>m] \<Rightarrow> bool"
where
  "wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s \<equiv>
  0 < size is \<and> size \<tau>s = size is \<and>
  check_types P mxs (1+size Ts+mxl\<^sub>0) (map OK \<tau>s) \<and>
  wt_start P C Ts mxl\<^sub>0 \<tau>s \<and>
  (\<forall>pc < size is. P,T\<^sub>r,mxs,size is,xt \<turnstile> is!pc,pc :: \<tau>s)"

\<comment> \<open>A program is welltyped if it is wellformed and all methods are welltyped\<close>
definition wf_jvm_prog_phi :: "ty\<^sub>P \<Rightarrow> 'addr jvm_prog \<Rightarrow> bool" ("wf'_jvm'_prog\<^bsub>_\<^esub>")
where
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> \<equiv>
    wf_prog (\<lambda>P C (M,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). 
      wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))"

definition wf_jvm_prog :: "'addr jvm_prog \<Rightarrow> bool"
where
  "wf_jvm_prog P \<equiv> \<exists>\<Phi>. wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"

lemma wt_jvm_progD:
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P \<Longrightarrow> \<exists>wt. wf_prog wt P"
(*<*) by (unfold wf_jvm_prog_phi_def, blast) (*>*)

lemma wt_jvm_prog_impl_wt_instr:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; 
      P \<turnstile> C sees M:Ts \<rightarrow> T = \<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; pc < size ins \<rbrakk> 
  \<Longrightarrow> P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def)
  done
(*>*)

lemma wt_jvm_prog_impl_wt_start:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; 
     P \<turnstile> C sees M:Ts \<rightarrow> T = \<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C \<rbrakk> \<Longrightarrow> 
  0 < size ins \<and> wt_start P C Ts mxl\<^sub>0 (\<Phi> C M)"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def)
  done
(*>*)

end
