(*  Title:      JinjaThreads/MM/JMM_JVM_Typesafe.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM type safety for bytecode\<close>

theory JMM_JVM_Typesafe
imports
  JMM_Typesafe2
  DRF_JVM
begin

locale JVM_allocated_heap_conf' = 
  h: JVM_heap_conf 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write hconf
    P
  +
  h: JVM_allocated_heap 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
    allocated
    P
  +
  heap''
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr jvm_prog"

sublocale JVM_allocated_heap_conf' < h: JVM_allocated_heap_conf
  addr2thread_id thread_id2addr
  spurious_wakeups
  empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write hconf allocated
  P
by(unfold_locales)

context JVM_allocated_heap_conf' begin

lemma exec_instr_New_type_match:
  "\<lbrakk> (ta, s') \<in> h.exec_instr i P t h stk loc C M pc frs; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(cases i)(auto split: if_split_asm prod.split_asm dest: allocate_typeof_addr_SomeD red_external_aggr_New_type_match)

lemma mexecd_New_type_match:
  "\<lbrakk> h.mexecd P t (xcpfrs, h) ta (xcpfrs', h'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp add: split_beta)
apply(erule h.jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto 4 3 dest: exec_instr_New_type_match)
done

lemma mexecd_known_addrs_typing':
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ok: "h.start_heap_ok"
  shows "known_addrs_typing' addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated h.jvm_known_addrs JVM_final (h.mexecd P) (\<lambda>t (xcp, frs) h. h.correct_state \<Phi> t (xcp, h, frs)) P"
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr 
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
    allocated h.jvm_known_addrs
    JVM_final "h.mexecd P" "\<lambda>t (xcp, frs) h. h.correct_state \<Phi> t (xcp, h, frs)"
    P
    using assms by(rule h.mexecd_known_addrs_typing)

  show ?thesis by(unfold_locales)(erule mexecd_New_type_match)
qed

lemma JVM_weakly_legal_read_value_typeable:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and wf_start: "h.wf_start_state P C M vs"
  and legal: "weakly_legal_execution P (h.JVMd_\<E> P C M vs status) (E, ws)"
  and a: "enat a < llength E"
  and read: "action_obs E a = NormalAction (ReadMem ad al v)"
  shows "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
proof -
  note wf
  moreover from wf_start have "h.start_heap_ok" by cases
  moreover from wf wf_start
  have "ts_ok (\<lambda>t (xcp, frs) h. h.correct_state \<Phi> t (xcp, h, frs)) (thr (h.JVM_start_state P C M vs)) h.start_heap"
    using h.correct_jvm_state_initial[OF wf wf_start]
    by(simp add: h.correct_jvm_state_def h.start_state_def split_beta)
  moreover from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls) 
  ultimately show ?thesis using legal a read
    by(rule known_addrs_typing'.weakly_legal_read_value_typeable[OF mexecd_known_addrs_typing'])
qed

end


abbreviation jmm_JVMd_\<E>
  :: "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> status \<Rightarrow> (addr \<times> (addr, addr) obs_event action) llist set"
where 
  "jmm_JVMd_\<E> P \<equiv> 
  JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr jmm_spurious_wakeups jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_read jmm_heap_write P"

abbreviation jmm'_JVMd_\<E>
  :: "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> status \<Rightarrow> (addr \<times> (addr, addr) obs_event action) llist set"
where 
  "jmm'_JVMd_\<E> P \<equiv> 
  JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr jmm_spurious_wakeups jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write P"

abbreviation jmm_JVM_start_state
  :: "addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> (addr,thread_id,addr jvm_thread_state,JMM_heap,addr) state"
where "jmm_JVM_start_state \<equiv> JVM_heap_base.JVM_start_state addr2thread_id jmm_empty jmm_allocate"

lemma jmm_JVM_heap_conf:
  "JVM_heap_conf addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_write jmm_hconf P"
by(unfold_locales)

lemma jmm_JVMd_allocated_heap_conf':
  "JVM_allocated_heap_conf' addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr' P) jmm_heap_write jmm_hconf jmm_allocated P"
apply(rule JVM_allocated_heap_conf'.intro)
apply(unfold jmm_typeof_addr'_conv_jmm_typeof_addr)
apply(unfold_locales)
done


lemma exec_instr_heap_read_typed:
  "(ta, xcphfrs') \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write i P t h stk loc C M pc frs \<longleftrightarrow>
   (ta, xcphfrs') \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write i P t h stk loc C M pc frs \<and>
   (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
apply(cases i)
apply(simp_all add: JVM_heap_base.exec_instr.simps split_beta cong: conj_cong)

apply(auto dest: heap_base.heap_read_typed_into_heap_read del: disjCI)[5]
apply(blast dest:  heap_base.heap_read_typed_typed heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD1])
apply(auto dest: heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1] intro: heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base.heap_read_typedI)[1]
apply(blast dest:  heap_base.heap_read_typed_typed heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD1])
apply(auto dest: heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1] intro: heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base.heap_read_typedI)[1]
apply(blast dest:  heap_base.heap_read_typed_typed heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD1])
subgoal by(auto dest: heap_base.heap_read_typed_into_heap_read)
apply(blast dest:  heap_base.heap_read_typed_typed heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD1])
subgoal by(auto dest: heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1] intro: heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base.heap_read_typedI)[1]
subgoal by(auto 4 3 dest: heap_base.heap_read_typed_into_heap_read intro: heap_base.heap_read_typedI simp add: heap_base'.conf_conv_conf heap_base'.addr_loc_type_conv_addr_loc_type)

apply(subst red_external_aggr_heap_read_typed)
apply(fastforce)
apply auto
done

lemma exec_heap_read_typed:
  "(ta, xcphfrs') \<in> JVM_heap_base.exec addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_. typeof_addr) heap_read P) heap_write P t xcphfrs \<longleftrightarrow>
   (ta, xcphfrs') \<in> JVM_heap_base.exec addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t xcphfrs \<and>
   (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
apply(cases xcphfrs)
apply(cases "fst xcphfrs")
apply(case_tac [!] "snd (snd xcphfrs)")
apply(auto simp add: JVM_heap_base.exec.simps exec_instr_heap_read_typed)
done

lemma exec_1_d_heap_read_typed:
  "JVM_heap_base.exec_1_d addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_. typeof_addr) heap_read P) heap_write P t (Normal xcphfrs) ta (Normal xcphfrs') \<longleftrightarrow>
   JVM_heap_base.exec_1_d addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t (Normal xcphfrs) ta (Normal xcphfrs') \<and>
   (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(auto elim!: JVM_heap_base.jvmd_NormalE intro: JVM_heap_base.exec_1_d_NormalI simp add: exec_heap_read_typed JVM_heap_base.exec_d_def)

lemma mexecd_heap_read_typed:
  "JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P t xcpfrsh ta xcpfrsh' \<longleftrightarrow>
   JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t xcpfrsh ta xcpfrsh' \<and>
   (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(simp add: split_beta exec_1_d_heap_read_typed)

lemma if_mexecd_heap_read_typed:
  "multithreaded_base.init_fin JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P) t xh ta x'h' \<longleftrightarrow>
   if_heap_read_typed JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P) typeof_addr P t xh ta x'h'"
unfolding multithreaded_base.init_fin.simps
by(subst mexecd_heap_read_typed) fastforce

lemma JVMd_\<E>_heap_read_typedI:
  "\<lbrakk> E \<in> JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P C M vs status;
     \<And>ad al v T. \<lbrakk> NormalAction (ReadMem ad al v) \<in> snd ` lset E; heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<rbrakk> \<Longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T \<rbrakk>
  \<Longrightarrow> E \<in> JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P C M vs status"
apply(erule imageE, hypsubst)
apply(rule imageI)
apply(erule multithreaded_base.\<E>.cases, hypsubst)
apply(rule multithreaded_base.\<E>.intros)
apply(subst if_mexecd_heap_read_typed[abs_def])
apply(erule if_mthr_Runs_heap_read_typedI)
apply(auto simp add: image_Un lset_lmap[symmetric] lmap_lconcat llist.map_comp o_def split_def simp del: lset_lmap)
done

lemma jmm'_exec_instrI:
  "\<lbrakk> (ta, xcphfrs) \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write i P t h stk loc C M pc frs; 
     final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta xcphfrs. (ta, xcphfrs) \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write i P t h stk loc C M pc frs \<and> final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta"
apply(cases i)
apply(auto simp add: JVM_heap_base.exec_instr.simps split_beta final_thread.actions_ok_iff intro!: jmm_heap_read_typed_default_val rev_image_eqI simp del: split_paired_Ex split: if_split_asm)
subgoal for F D
  apply(cases "hd (tl stk) = (default_val (THE T. heap_base.addr_loc_type typeof_addr P h (the_Addr (hd (tl (tl stk)))) (CField D F) T))")
  subgoal by(auto simp add: JVM_heap_base.exec_instr.simps split_beta final_thread.actions_ok_iff intro!: jmm_heap_read_typed_default_val rev_image_eqI simp del: split_paired_Ex split: if_split_asm del: disjCI intro!: disjI1 exI)
  subgoal by(auto simp add: JVM_heap_base.exec_instr.simps split_beta final_thread.actions_ok_iff intro!: jmm_heap_read_typed_default_val rev_image_eqI simp del: split_paired_Ex split: if_split_asm del: disjCI intro!: disjI2 exI)
  done
subgoal for F D
  apply(cases "hd (tl stk) = (default_val (THE T. heap_base.addr_loc_type typeof_addr P h (the_Addr (hd (tl (tl stk)))) (CField D F) T))")
  subgoal by(auto simp add: JVM_heap_base.exec_instr.simps split_beta final_thread.actions_ok_iff intro!: jmm_heap_read_typed_default_val rev_image_eqI simp del: split_paired_Ex split: if_split_asm del: disjCI intro!: disjI1 exI jmm_heap_write.intros)
  subgoal by(rule exI conjI disjI2 refl jmm_heap_read_typed_default_val|assumption)+ auto
  done
subgoal by(drule red_external_aggr_heap_read_typedI)(fastforce simp add: final_thread.actions_ok_iff simp del: split_paired_Ex)+
done

lemma jmm'_execI:
  "\<lbrakk> (ta, xcphfrs') \<in> JVM_heap_base.exec addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t xcphfrs;
     final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta xcphfrs'. (ta, xcphfrs') \<in> JVM_heap_base.exec addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t xcphfrs \<and> final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta"
apply(cases xcphfrs)
apply(cases "snd (snd xcphfrs)")
 apply(simp add: JVM_heap_base.exec.simps)
apply(cases "fst xcphfrs")
apply(fastforce simp add: JVM_heap_base.exec.simps dest!: jmm'_exec_instrI)+
done

lemma jmm'_execdI:
  "\<lbrakk> JVM_heap_base.exec_1_d addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t (Normal xcphfrs) ta (Normal xcphfrs');
     final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta xcphfrs'. JVM_heap_base.exec_1_d addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t (Normal xcphfrs) ta (Normal xcphfrs') \<and> final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta"
apply(erule JVM_heap_base.jvmd_NormalE)
apply(drule (1) jmm'_execI)
apply(force intro: JVM_heap_base.exec_1_d_NormalI simp add: JVM_heap_base.exec_d_def)
done

lemma jmm'_mexecdI:
  "\<lbrakk> JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t xcpfrsh ta xcpfrsh';
     final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta xcpfrsh'. JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t xcpfrsh ta xcpfrsh' \<and> final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta"
by(simp add: split_beta)(drule (1) jmm'_execdI, auto 4 10)

lemma if_mexecd_heap_read_not_stuck:
  "\<lbrakk> multithreaded_base.init_fin JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P) t xh ta x'h';
     final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta x'h'. multithreaded_base.init_fin JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P) t xh ta x'h' \<and> final_thread.actions_ok (final_thread.init_fin_final JVM_final) s t ta"
apply(erule multithreaded_base.init_fin.cases)
  apply hypsubst
  apply(drule jmm'_mexecdI)
   apply(simp add: final_thread.actions_ok_iff)
  apply clarify
  apply(subst (2) split_paired_Ex)
  apply(subst (2) split_paired_Ex)
  apply(subst (2) split_paired_Ex)
  apply(rule exI conjI)+
   apply(rule multithreaded_base.init_fin.intros)
   apply simp
  apply(simp add: final_thread.actions_ok_iff)
 apply(blast intro: multithreaded_base.init_fin.intros)
apply(blast intro: multithreaded_base.init_fin.intros)
done

lemma if_mExecd_heap_read_not_stuck:
  "multithreaded_base.redT (final_thread.init_fin_final JVM_final) (multithreaded_base.init_fin JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P)) convert_RA' s tta s'
  \<Longrightarrow> \<exists>tta s'. multithreaded_base.redT (final_thread.init_fin_final JVM_final) (multithreaded_base.init_fin JVM_final (JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P)) convert_RA' s tta s'"
apply(erule multithreaded_base.redT.cases)
 apply hypsubst
 thm if_mexecd_heap_read_not_stuck
 apply(drule (1) if_mexecd_heap_read_not_stuck)
 apply(erule exE)+
 apply(rename_tac ta' x'h')
 apply(insert redT_updWs_total)
 apply(erule_tac x="t" in meta_allE)
 apply(erule_tac x="wset s" in meta_allE)
 apply(erule_tac x="\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" in meta_allE)
 apply clarsimp
 apply(rule exI)+
 apply(auto intro!: multithreaded_base.redT.intros)[1]
apply hypsubst
apply(rule exI conjI)+
apply(rule multithreaded_base.redT.redT_acquire)
apply assumption+
done

lemma JVM_legal_typesafe1:
  assumes wfP: "wf_jvm_prog P"
  and ok: "jmm_wf_start_state P C M vs"
  and legal: "legal_execution P (jmm_JVMd_\<E> P C M vs status) (E, ws)"
  shows "legal_execution P (jmm'_JVMd_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_JVMd_\<E> P C M vs status"
  let ?\<E>' = "jmm'_JVMd_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>"
    and E: "E \<in> ?\<E>" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  let ?J = "J(0 := \<lparr>committed = {}, justifying_exec = justifying_exec (J 1), justifying_ws = justifying_ws (J 1), action_translation = id\<rparr>)"

  from wfP obtain \<Phi> where \<Phi>: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by(auto simp add: wf_jvm_prog_def)
  hence wf_sys: "wf_syscls P" by(auto dest: wt_jvm_progD intro: wf_prog_wf_syscls)

  from justified have "P \<turnstile> (justifying_exec (J 1), justifying_ws (J 1)) \<surd>" by(simp add: justification_well_formed_def)
  with justified have "P \<turnstile> (E, ws) justified_by ?J" by(rule drop_0th_justifying_exec)
  moreover have "range (justifying_exec \<circ> ?J) \<subseteq> ?\<E>'"
  proof
    fix \<xi>
    assume "\<xi> \<in> range (justifying_exec \<circ> ?J)"
    then obtain n where "\<xi> = justifying_exec (?J n)" by auto
    then obtain n where \<xi>: "\<xi> = justifying_exec (J n)" and n: "n > 0" by(auto split: if_split_asm)
    from range \<xi> have "\<xi> \<in> ?\<E>" by auto
    thus "\<xi> \<in> ?\<E>'" unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
    proof(rule JVMd_\<E>_heap_read_typedI)
      fix ad al v T
      assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset \<xi>"
        and adal: "P \<turnstile>jmm ad@al : T"
      from read obtain a where a: "enat a < llength \<xi>" "action_obs \<xi> a = NormalAction (ReadMem ad al v)"
        unfolding lset_conv_lnth by(auto simp add: action_obs_def)

      have "ts_ok (\<lambda>t (xcp, frs) h. JVM_heap_conf_base.correct_state addr2thread_id jmm_empty jmm_allocate (\<lambda>_. jmm_typeof_addr' P) jmm_hconf P \<Phi> t (xcp, h, frs)) (thr (jmm_JVM_start_state P C M vs)) jmm.start_heap"

        using JVM_heap_conf.correct_jvm_state_initial[OF jmm_JVM_heap_conf \<Phi> ok]
        by(simp add: JVM_heap_conf_base.correct_jvm_state_def jmm_typeof_addr'_conv_jmm_typeof_addr heap_base.start_state_def split_beta)
      with JVM_allocated_heap_conf'.mexecd_known_addrs_typing'[OF jmm_JVMd_allocated_heap_conf' \<Phi> jmm_start_heap_ok]
      have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
        using wf_sys is_justified_by_imp_is_weakly_justified_by[OF justified wf] range n a
        unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def] \<xi>
        by(rule known_addrs_typing'.read_value_typeable_justifying)
      thus "P \<turnstile>jmm v :\<le> T" using adal
        by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
    qed
  qed
  moreover from E have "E \<in> ?\<E>'"
    unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
  proof(rule JVMd_\<E>_heap_read_typedI)
    fix ad al v T
    assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset E"
      and adal: "P \<turnstile>jmm ad@al : T"
    from read obtain a where a: "enat a < llength E" "action_obs E a = NormalAction (ReadMem ad al v)"
      unfolding lset_conv_lnth by(auto simp add: action_obs_def)
    with jmm_JVMd_allocated_heap_conf' \<Phi> ok legal_imp_weakly_legal_execution[OF legal]
    have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
      unfolding jmm_typeof_addr'_conv_jmm_typeof_addr[symmetric, abs_def]
      by(rule JVM_allocated_heap_conf'.JVM_weakly_legal_read_value_typeable)
    thus "P \<turnstile>jmm v :\<le> T" using adal
      by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
  qed
  ultimately show ?thesis using wf unfolding gen_legal_execution.simps by blast
qed

lemma JVM_weakly_legal_typesafe1:
  assumes wfP: "wf_jvm_prog P"
  and ok: "jmm_wf_start_state P C M vs"
  and legal: "weakly_legal_execution P (jmm_JVMd_\<E> P C M vs status) (E, ws)"
  shows "weakly_legal_execution P (jmm'_JVMd_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_JVMd_\<E> P C M vs status"
  let ?\<E>' = "jmm'_JVMd_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) weakly_justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>"
    and E: "E \<in> ?\<E>" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  let ?J = "J(0 := \<lparr>committed = {}, justifying_exec = justifying_exec (J 1), justifying_ws = justifying_ws (J 1), action_translation = id\<rparr>)"

  from wfP obtain \<Phi> where \<Phi>: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by(auto simp add: wf_jvm_prog_def)
  hence wf_sys: "wf_syscls P" by(auto dest: wt_jvm_progD intro: wf_prog_wf_syscls)

  from justified have "P \<turnstile> (justifying_exec (J 1), justifying_ws (J 1)) \<surd>" by(simp add: justification_well_formed_def)
  with justified have "P \<turnstile> (E, ws) weakly_justified_by ?J" by(rule drop_0th_weakly_justifying_exec)
  moreover have "range (justifying_exec \<circ> ?J) \<subseteq> ?\<E>'"
  proof
    fix \<xi>
    assume "\<xi> \<in> range (justifying_exec \<circ> ?J)"
    then obtain n where "\<xi> = justifying_exec (?J n)" by auto
    then obtain n where \<xi>: "\<xi> = justifying_exec (J n)" and n: "n > 0" by(auto split: if_split_asm)
    from range \<xi> have "\<xi> \<in> ?\<E>" by auto
    thus "\<xi> \<in> ?\<E>'" unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
    proof(rule JVMd_\<E>_heap_read_typedI)
      fix ad al v T
      assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset \<xi>"
        and adal: "P \<turnstile>jmm ad@al : T"
      from read obtain a where a: "enat a < llength \<xi>" "action_obs \<xi> a = NormalAction (ReadMem ad al v)"
        unfolding lset_conv_lnth by(auto simp add: action_obs_def)

      have "ts_ok (\<lambda>t (xcp, frs) h. JVM_heap_conf_base.correct_state addr2thread_id jmm_empty jmm_allocate (\<lambda>_. jmm_typeof_addr' P) jmm_hconf P \<Phi> t (xcp, h, frs)) (thr (jmm_JVM_start_state P C M vs)) jmm.start_heap"

        using JVM_heap_conf.correct_jvm_state_initial[OF jmm_JVM_heap_conf \<Phi> ok]
        by(simp add: JVM_heap_conf_base.correct_jvm_state_def jmm_typeof_addr'_conv_jmm_typeof_addr heap_base.start_state_def split_beta)
      with JVM_allocated_heap_conf'.mexecd_known_addrs_typing'[OF jmm_JVMd_allocated_heap_conf' \<Phi> jmm_start_heap_ok]
      have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
        using wf_sys justified range n a
        unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def] \<xi>
        by(rule known_addrs_typing'.read_value_typeable_justifying)
      thus "P \<turnstile>jmm v :\<le> T" using adal
        by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
    qed
  qed
  moreover from E have "E \<in> ?\<E>'"
    unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
  proof(rule JVMd_\<E>_heap_read_typedI)
    fix ad al v T
    assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset E"
      and adal: "P \<turnstile>jmm ad@al : T"
    from read obtain a where a: "enat a < llength E" "action_obs E a = NormalAction (ReadMem ad al v)"
      unfolding lset_conv_lnth by(auto simp add: action_obs_def)
    with jmm_JVMd_allocated_heap_conf' \<Phi> ok legal
    have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
      unfolding jmm_typeof_addr'_conv_jmm_typeof_addr[symmetric, abs_def]
      by(rule JVM_allocated_heap_conf'.JVM_weakly_legal_read_value_typeable)
    thus "P \<turnstile>jmm v :\<le> T" using adal
      by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
  qed
  ultimately show ?thesis using wf unfolding gen_legal_execution.simps by blast
qed

lemma JVMd_\<E>_heap_read_typedD:
  "E \<in> JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_. typeof_addr) (heap_base.heap_read_typed (\<lambda>_. typeof_addr) jmm_heap_read P) jmm_heap_write P C M vs status
  \<Longrightarrow> E \<in> JVM_heap_base.JVMd_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_. typeof_addr) jmm_heap_read jmm_heap_write P C M vs status"
apply(erule imageE, hypsubst)
apply(rule imageI)
apply(erule multithreaded_base.\<E>.cases, hypsubst)
apply(rule multithreaded_base.\<E>.intros)
apply(subst (asm) if_mexecd_heap_read_typed[abs_def])
apply(erule if_mthr_Runs_heap_read_typedD)
apply(erule if_mExecd_heap_read_not_stuck[where typeof_addr="\<lambda>_. typeof_addr", unfolded if_mexecd_heap_read_typed[abs_def]])
done

lemma JVMd_\<E>_typesafe_subset: "jmm'_JVMd_\<E> P C M vs status \<subseteq> jmm_JVMd_\<E> P C M vs status"
unfolding jmm_typeof_addr_def[abs_def]
by(rule subsetI)(erule JVMd_\<E>_heap_read_typedD)

lemma JVMd_legal_typesafe2:
  assumes legal: "legal_execution P (jmm'_JVMd_\<E> P C M vs status) (E, ws)"
  shows "legal_execution P (jmm_JVMd_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_JVMd_\<E> P C M vs status"
  let ?\<E>' = "jmm'_JVMd_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>'"
    and E: "E \<in> ?\<E>'" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  from range E have "range (justifying_exec \<circ> J) \<subseteq> ?\<E>" "E \<in> ?\<E>"
    using JVMd_\<E>_typesafe_subset[of P status C M vs] by blast+
  with justified wf
  show ?thesis by(auto simp add: gen_legal_execution.simps)
qed

theorem JVMd_weakly_legal_typesafe2:
  assumes legal: "weakly_legal_execution P (jmm'_JVMd_\<E> P C M vs status) (E, ws)"
  shows "weakly_legal_execution P (jmm_JVMd_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_JVMd_\<E> P C M vs status"
  let ?\<E>' = "jmm'_JVMd_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) weakly_justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>'"
    and E: "E \<in> ?\<E>'" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  from range E have "range (justifying_exec \<circ> J) \<subseteq> ?\<E>" "E \<in> ?\<E>"
    using JVMd_\<E>_typesafe_subset[of P status C M vs] by blast+
  with justified wf
  show ?thesis by(auto simp add: gen_legal_execution.simps)
qed

theorem JVMd_weakly_legal_typesafe:
  assumes "wf_jvm_prog P"
  and "jmm_wf_start_state P C M vs"
  shows "weakly_legal_execution P (jmm_JVMd_\<E> P C M vs status) = weakly_legal_execution P (jmm'_JVMd_\<E> P C M vs status)"
apply(rule ext iffI)+
 apply(clarify, erule JVM_weakly_legal_typesafe1[OF assms])
apply(clarify, erule JVMd_weakly_legal_typesafe2)
done

theorem JVMd_legal_typesafe:
  assumes "wf_jvm_prog P"
  and "jmm_wf_start_state P C M vs"
  shows "legal_execution P (jmm_JVMd_\<E> P C M vs status) = legal_execution P (jmm'_JVMd_\<E> P C M vs status)"
apply(rule ext iffI)+
 apply(clarify, erule JVM_legal_typesafe1[OF assms])
apply(clarify, erule JVMd_legal_typesafe2)
done

end
