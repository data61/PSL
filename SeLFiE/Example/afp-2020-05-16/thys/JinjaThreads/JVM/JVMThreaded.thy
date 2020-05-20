(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Andreas Lochbihler
*)

section \<open>Instantiating the framework semantics with the JVM\<close>

theory JVMThreaded
imports
  JVMDefensive
  "../Common/ConformThreaded"
  "../Framework/FWLiftingSem"
  "../Framework/FWProgressAux"
begin

primrec JVM_final :: "'addr jvm_thread_state \<Rightarrow> bool"
where
  "JVM_final (xcp, frs) = (frs = [])"

text\<open>The aggressive JVM\<close>

context JVM_heap_base begin

abbreviation mexec :: 
  "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr jvm_thread_state \<times> 'heap)
  \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action \<Rightarrow> ('addr jvm_thread_state \<times> 'heap) \<Rightarrow> bool"
where
  "mexec P t \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P,t \<turnstile> (xcp, h, frstls) -ta-jvm\<rightarrow> (xcp', h', frstls'))"

lemma NewThread_memory_exec_instr:
  "\<lbrakk> (ta, s) \<in> exec_instr I P t h stk loc C M pc frs; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = fst (snd s)"
apply(cases I)
apply(auto split: if_split_asm simp add: split_beta ta_upd_simps)
apply(auto dest!: red_ext_aggr_new_thread_heap simp add: extRet2JVM_def split: extCallRet.split)
done

lemma NewThread_memory_exec:
  "\<lbrakk> P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = (fst (snd \<sigma>'))"
apply(erule exec_1.cases)
apply(clarsimp)
apply(case_tac bb, simp)
apply(case_tac ag, auto simp add: exception_step_def_raw split: list.split_asm)
apply(drule NewThread_memory_exec_instr, simp+)
done

lemma exec_instr_Wakeup_no_Lock_no_Join_no_Interrupt:
  "\<lbrakk> (ta, s) \<in> exec_instr I P t h stk loc C M pc frs; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
apply(cases I)
apply(auto split: if_split_asm simp add: split_beta ta_upd_simps dest: red_external_aggr_Wakeup_no_Join)
done

lemma mexec_instr_Wakeup_no_Join:
  "\<lbrakk> P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
apply(erule exec_1.cases)
apply(clarsimp)
apply(case_tac bb, simp)
apply(case_tac ag, clarsimp simp add: exception_step_def_raw split: list.split_asm del: disjE)
apply(drule exec_instr_Wakeup_no_Lock_no_Join_no_Interrupt)
apply auto
done

lemma mexec_final: 
  "\<lbrakk> mexec P t (x, m) ta (x', m'); JVM_final x \<rbrakk> \<Longrightarrow> False"
by(cases x)(auto simp add: exec_1_iff)

lemma exec_mthr: "multithreaded JVM_final (mexec P)"
apply(unfold_locales)
apply(clarsimp, drule NewThread_memory_exec, fastforce, simp)
apply(erule (1) mexec_final)
done

end

sublocale JVM_heap_base < exec_mthr: 
  multithreaded
    JVM_final
    "mexec P"
    convert_RA
  for P
by(rule exec_mthr)

context JVM_heap_base begin

abbreviation mexecT ::
  "'addr jvm_prog
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> 'thread_id \<times> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
where
  "mexecT P \<equiv> exec_mthr.redT P"

abbreviation mexecT_syntax1 ::
  "'addr jvm_prog \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
  ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecT_syntax1 P s t ta s' \<equiv> mexecT P s (t, ta) s'"


abbreviation mExecT_syntax1 :: 
  "'addr jvm_prog \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id, 'heap) jvm_thread_action) list
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
  ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvm\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' \<equiv> exec_mthr.RedT P s ttas s'"

text\<open>The defensive JVM\<close>

abbreviation mexecd :: 
  "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr jvm_thread_state \<times> 'heap 
  \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action \<Rightarrow> 'addr jvm_thread_state \<times> 'heap \<Rightarrow> bool"
where
  "mexecd P t \<equiv> (\<lambda>((xcp, frstls), h) ta ((xcp', frstls'), h'). P,t \<turnstile> Normal (xcp, h, frstls) -ta-jvmd\<rightarrow> Normal (xcp', h', frstls'))"

lemma execd_mthr: "multithreaded JVM_final (mexecd P)"
apply(unfold_locales)
 apply(fastforce dest: defensive_imp_aggressive_1 NewThread_memory_exec)
apply(auto elim: jvmd_NormalE)
done

end

sublocale JVM_heap_base < execd_mthr:
  multithreaded
    JVM_final
    "mexecd P"
    convert_RA
  for P
by(rule execd_mthr)

context JVM_heap_base begin

abbreviation mexecdT ::
  "'addr jvm_prog \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> 'thread_id \<times> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
where
  "mexecdT P \<equiv> execd_mthr.redT P"


abbreviation mexecdT_syntax1 ::
  "'addr jvm_prog \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
  ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub> _" [50,0,0,0,50] 80)
where
  "mexecdT_syntax1 P s t ta s' \<equiv> mexecdT P s (t, ta) s'"

abbreviation mExecdT_syntax1 ::
  "'addr jvm_prog \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id, 'heap) jvm_thread_action) list
  \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state \<Rightarrow> bool"
  ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>\<^bsub>jvmd\<^esub>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s' \<equiv> execd_mthr.RedT P s ttas s'"

lemma mexecd_Suspend_Invoke:
  "\<lbrakk> mexecd P t (x, m) ta (x', m'); Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>stk loc C M pc frs' n a T Ts Tr D. x' = (None, (stk, loc, C, M, pc) # frs') \<and> instrs_of P C M ! pc = Invoke wait n \<and> stk ! n = Addr a \<and> typeof_addr m a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees wait:Ts\<rightarrow>Tr = Native in D \<and> D\<bullet>wait(Ts) :: Tr"
apply(cases x')
apply(cases x)
apply(cases "fst x")
apply(auto elim!: jvmd_NormalE simp add: split_beta)
apply(rename_tac [!] stk loc C M pc frs)
apply(case_tac [!] "instrs_of P C M ! pc")
apply(auto split: if_split_asm simp add: split_beta check_def is_Ref_def has_method_def)
apply(frule red_external_aggr_Suspend_StaySame, simp, drule red_external_aggr_Suspend_waitD, simp, fastforce)+
done

end

context JVM_heap begin

lemma exec_instr_New_Thread_exists_thread_object:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     check_instr ins P h stk loc C M pc frs;
     NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(cases ins)
apply(fastforce simp add: split_beta ta_upd_simps split: if_split_asm intro: red_external_aggr_new_thread_exists_thread_object)+
done

lemma exec_New_Thread_exists_thread_object:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(cases xcp)
apply(case_tac [!] frs)
apply(auto simp add: check_def elim!: jvmd_NormalE dest!: exec_instr_New_Thread_exists_thread_object)
done

lemma exec_instr_preserve_tconf:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     check_instr ins P h stk loc C M pc frs;
     P,h \<turnstile> t' \<surd>t \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(cases ins)
apply(auto intro: tconf_hext_mono hext_allocate hext_heap_write red_external_aggr_preserves_tconf split: if_split_asm sum.split_asm simp add: split_beta has_method_def intro!: is_native.intros cong del: image_cong_simp)
done

lemma exec_preserve_tconf:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); P,h \<turnstile> t' \<surd>t \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
apply(cases xcp)
apply(case_tac [!] frs)
apply(auto simp add: check_def elim!: jvmd_NormalE elim!: exec_instr_preserve_tconf)
done

lemma lifting_wf_thread_conf: "lifting_wf JVM_final (mexecd P) (\<lambda>t x m. P,m \<turnstile> t \<surd>t)"
by(unfold_locales)(auto intro: exec_preserve_tconf dest: exec_New_Thread_exists_thread_object intro: tconfI)

end

sublocale JVM_heap < execd_tconf: lifting_wf JVM_final "mexecd P" convert_RA "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
by(rule lifting_wf_thread_conf)

context JVM_heap begin

lemma execd_hext:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s' \<Longrightarrow> shr s \<unlhd> shr s'"
by(auto elim!: execd_mthr.redT.cases dest!: exec_1_d_hext intro: hext_trans)

lemma Execd_hext:
  assumes "P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  shows "shr s \<unlhd> shr s'"
using assms unfolding execd_mthr.RedT_def
by(induct)(auto dest!: execd_hext intro: hext_trans simp add: execd_mthr.RedT_def)

end

end
