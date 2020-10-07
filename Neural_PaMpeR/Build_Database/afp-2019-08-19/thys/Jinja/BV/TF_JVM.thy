(*  Title:      HOL/MicroJava/BV/JVM.thy

    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

section \<open>The Typing Framework for the JVM \label{sec:JVM}\<close>

theory TF_JVM
imports "../DFA/Typing_Framework_err" EffectMono BVSpec
begin

definition exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ex_table \<Rightarrow> instr list \<Rightarrow> ty\<^sub>i' err step_type"
where 
  "exec G maxs rT et bs \<equiv>
  err_step (size bs) (\<lambda>pc. app (bs!pc) G maxs rT pc (size bs) et) 
                     (\<lambda>pc. eff (bs!pc) G pc et)"

locale JVM_sl =
  fixes P :: jvm_prog and mxs and mxl\<^sub>0
  fixes Ts :: "ty list" and "is" and xt and T\<^sub>r

  fixes mxl and A and r and f and app and eff and step
  defines [simp]: "mxl \<equiv> 1+size Ts+mxl\<^sub>0"
  defines [simp]: "A   \<equiv> states P mxs mxl"
  defines [simp]: "r   \<equiv> JVM_SemiType.le P mxs mxl"
  defines [simp]: "f   \<equiv> JVM_SemiType.sup P mxs mxl"

  defines [simp]: "app \<equiv> \<lambda>pc. Effect.app (is!pc) P mxs T\<^sub>r pc (size is) xt"
  defines [simp]: "eff \<equiv> \<lambda>pc. Effect.eff (is!pc) P pc xt"
  defines [simp]: "step \<equiv> err_step (size is) app eff"


locale start_context = JVM_sl +
  fixes p and C
  assumes wf: "wf_prog p P"
  assumes C:  "is_class P C"
  assumes Ts: "set Ts \<subseteq> types P"

  fixes first :: ty\<^sub>i' and start
  defines [simp]: 
  "first \<equiv> Some ([],OK (Class C) # map OK Ts @ replicate mxl\<^sub>0 Err)"
  defines [simp]:
  "start \<equiv> OK first # replicate (size is - 1) (OK None)"



subsection \<open>Connecting JVM and Framework\<close>


lemma (in JVM_sl) step_def_exec: "step \<equiv> exec P mxs T\<^sub>r xt is" 
  by (simp add: exec_def)  

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemma ex_in_list [iff]:
  "(\<exists>n. ST \<in> list n A \<and> n \<le> mxs) = (set ST \<subseteq> A \<and> size ST \<le> mxs)"
  by (unfold list_def) auto

lemma singleton_list: 
  "(\<exists>n. [Class C] \<in> list n (types P) \<and> n \<le> mxs) = (is_class P C \<and> 0 < mxs)"
  by auto

lemma set_drop_subset:
  "set xs \<subseteq> A \<Longrightarrow> set (drop n xs) \<subseteq> A"
  by (auto dest: in_set_dropD)

lemma Suc_minus_minus_le:
  "n < mxs \<Longrightarrow> Suc (n - (n - b)) \<le> mxs"
  by arith

lemma in_listE:
  "\<lbrakk> xs \<in> list n A; \<lbrakk>size xs = n; set xs \<subseteq> A\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (unfold list_def) blast

declare is_relevant_entry_def [simp]
declare set_drop_subset [simp]

theorem (in start_context) exec_pres_type:
  "pres_type step (size is) A"
(*<*)
  apply (insert wf)
  apply simp
  apply (unfold JVM_states_unfold)
  apply (rule pres_type_lift)
  apply clarify
  apply (rename_tac s pc pc' s')
  apply (case_tac s)
   apply simp
   apply (drule effNone)
   apply simp  
  apply (simp add: Effect.app_def xcpt_app_def Effect.eff_def  
                   xcpt_eff_def norm_eff_def relevant_entries_def)
  apply (case_tac "is!pc")

  \<comment> \<open>Load\<close>
  apply clarsimp
  apply (frule listE_nth_in, assumption)
  apply fastforce

  \<comment> \<open>Store\<close>
  apply fastforce

  \<comment> \<open>Push\<close>
  apply (fastforce simp add: typeof_lit_is_type)

  \<comment> \<open>New\<close>
  apply fastforce

  \<comment> \<open>Getfield\<close>
  apply (fastforce dest: sees_field_is_type)

  \<comment> \<open>Putfield\<close>
  apply fastforce

  \<comment> \<open>Checkcast\<close>
  apply fastforce

  defer 
  
  \<comment> \<open>Return\<close>
  apply fastforce

  \<comment> \<open>Pop\<close>
  apply fastforce

  \<comment> \<open>IAdd\<close>
  apply fastforce
  
  \<comment> \<open>Goto\<close>
  apply fastforce

  \<comment> \<open>CmpEq\<close>
  apply fastforce

  \<comment> \<open>IfFalse\<close>
  apply fastforce

  \<comment> \<open>Throw\<close>
  apply fastforce

  \<comment> \<open>Invoke\<close>
  apply (clarsimp split!: if_splits)
   apply fastforce
  apply (erule disjE)
   prefer 2
   apply fastforce
  apply clarsimp
  apply (rule conjI)
   apply (drule (1) sees_wf_mdecl)
   apply (clarsimp simp add: wf_mdecl_def)
  apply arith
  done
(*>*)

declare is_relevant_entry_def [simp del]
declare set_drop_subset [simp del]

lemma lesubstep_type_simple:
  "xs [\<sqsubseteq>\<^bsub>Product.le (=) r\<^esub>] ys \<Longrightarrow> set xs {\<sqsubseteq>\<^bsub>r\<^esub>} set ys"
(*<*)
  apply (unfold lesubstep_type_def)
  apply clarify
  apply (simp add: set_conv_nth)
  apply clarify
  apply (drule le_listD, assumption)
  apply (clarsimp simp add: lesub_def Product.le_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI)
    apply (rule sym)
    apply assumption
   apply assumption
  apply assumption
  done
(*>*)

declare is_relevant_entry_def [simp del]


lemma conjI2: "\<lbrakk> A; A \<Longrightarrow> B \<rbrakk> \<Longrightarrow> A \<and> B" by blast
  
lemma (in JVM_sl) eff_mono:
  "\<lbrakk>wf_prog p P; pc < length is; s \<sqsubseteq>\<^bsub>sup_state_opt P\<^esub> t; app pc t\<rbrakk>
  \<Longrightarrow> set (eff pc s) {\<sqsubseteq>\<^bsub>sup_state_opt P\<^esub>} set (eff pc t)"
(*<*)
  apply simp
  apply (unfold Effect.eff_def)  
  apply (cases t)
   apply (simp add: lesub_def)
  apply (rename_tac a)
  apply (cases s)
   apply simp
  apply (rename_tac b)
  apply simp
  apply (rule lesubstep_union)
   prefer 2
   apply (rule lesubstep_type_simple)
   apply (simp add: xcpt_eff_def)
   apply (rule le_listI)
    apply (simp add: split_beta)
   apply (simp add: split_beta)
   apply (simp add: lesub_def fun_of_def)
   apply (case_tac a)
   apply (case_tac b)
   apply simp   
   apply (subgoal_tac "size ab = size aa")
     prefer 2
     apply (clarsimp simp add: list_all2_lengthD)
   apply simp
  apply (clarsimp simp add: norm_eff_def lesubstep_type_def lesub_def iff del: sup_state_conv)
  apply (rule exI)
  apply (rule conjI2)
   apply (rule imageI)
   apply (clarsimp simp add: Effect.app_def iff del: sup_state_conv)
   apply (drule (2) succs_mono)
   apply blast
  apply simp
  apply (erule eff\<^sub>i_mono)
     apply simp
    apply assumption   
   apply clarsimp
  apply clarsimp  
  done
(*>*)

lemma (in JVM_sl) bounded_step: "bounded step (size is)"
(*<*)
  apply simp
  apply (unfold bounded_def err_step_def Effect.app_def Effect.eff_def)
  apply (auto simp add: error_def map_snd_def split: err.splits option.splits)
  done
(*>*)

theorem (in JVM_sl) step_mono:
  "wf_prog wf_mb P \<Longrightarrow> mono r step (size is) A"
(*<*)
  apply (simp add: JVM_le_Err_conv)  
  apply (insert bounded_step)
  apply (unfold JVM_states_unfold)
  apply (rule mono_lift)
     apply blast
    apply (unfold app_mono_def lesub_def)
    apply clarsimp
    apply (erule (2) app_mono)
   apply simp
  apply clarify
  apply (drule eff_mono)
  apply (auto simp add: lesub_def)
  done
(*>*)


lemma (in start_context) first_in_A [iff]: "OK first \<in> A"
  using Ts C by (force intro!: list_appendI simp add: JVM_states_unfold)


lemma (in JVM_sl) wt_method_def2:
  "wt_method P C' Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s =
  (is \<noteq> [] \<and> 
   size \<tau>s = size is \<and>
   OK ` set \<tau>s \<subseteq> states P mxs mxl \<and>
   wt_start P C' Ts mxl\<^sub>0 \<tau>s \<and> 
   wt_app_eff (sup_state_opt P) app eff \<tau>s)"
(*<*)
  apply (unfold wt_method_def wt_app_eff_def wt_instr_def lesub_def check_types_def)
  apply auto
  done
(*>*)


end
