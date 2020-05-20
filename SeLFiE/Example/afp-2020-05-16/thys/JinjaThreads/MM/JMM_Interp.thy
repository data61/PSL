(*  Title:      JinjaThreads/MM/JMM_Interp.thy
    Author:     Andreas Lochbihler

    Interpret the language specific heap locales with the Java memory model
*)

theory JMM_Interp imports
  JMM_Compiler
  "../J/Deadlocked"
  "../BV/JVMDeadlocked"
  JMM_Type2
  DRF_J
  DRF_JVM
begin

lemma jmm'_J_typesafe:
  "J_typesafe addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm_hconf P"
by unfold_locales

lemma jmm'_JVM_typesafe:
  "JVM_typesafe addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm_hconf P"
by unfold_locales

lemma jmm_typeof_addr_compP [simp]:
  "jmm_typeof_addr (compP f P) = jmm_typeof_addr P"
by(simp add: jmm_typeof_addr_def fun_eq_iff)

lemma compP2_compP1_convs:
  "is_type (compP2 (compP1 P)) = is_type P"
  "is_class (compP2 (compP1 P)) = is_class P"
  "jmm'_addr_loc_type (compP2 (compP1 P)) = jmm'_addr_loc_type P"
  "jmm'_conf (compP2 (compP1 P)) = jmm'_conf P"
by(simp_all add: compP2_def heap_base.compP_conf heap_base.compP_addr_loc_type fun_eq_iff split: addr_loc.splits)

lemma jmm'_J_JVM_conf_read:
  "J_JVM_conf_read addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm_hconf P"
apply(rule J_JVM_conf_read.intro)
apply(rule J1_JVM_conf_read.intro)
apply(rule JVM_conf_read.intro)
 prefer 2
 apply(rule JVM_heap_conf.intro)
 apply(rule JVM_heap_conf_base'.intro)
 apply(unfold compP2_def compP1_def compP_heap compP_heap_conf compP_heap_conf_read jmm_typeof_addr_compP)
 apply unfold_locales
done

lemma jmm_J_allocated_progress:
  "J_allocated_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_read jmm_heap_write jmm_hconf jmm_allocated P"
by unfold_locales

lemma jmm'_J_allocated_progress:
  "J_allocated_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm_hconf jmm_allocated P"
by(unfold_locales)

lemma jmm_JVM_allocated_progress:
  "JVM_allocated_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_read jmm_heap_write jmm_hconf jmm_allocated P"
by unfold_locales

lemma jmm'_JVM_allocated_progress:
  "JVM_allocated_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm_hconf jmm_allocated P"
by(unfold_locales)

end
