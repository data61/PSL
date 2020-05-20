(*  Title:      JinjaThreads/MM/SC_Interp.thy
    Author:     Andreas Lochbihler

    Interpret the language specific heap locales with the SC memory model
*)

theory SC_Interp
imports
  SC
  "../Compiler/Correctness" 
  "../J/Deadlocked"
  "../BV/JVMDeadlocked"
begin

text \<open>
  Do not interpret these locales, it just takes too long to generate all definitions and theorems.
\<close>

lemma sc_J_typesafe:
  "J_typesafe addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read sc_heap_write (sc_hconf P) P"
by unfold_locales

lemma sc_JVM_typesafe:
  "JVM_typesafe addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read sc_heap_write (sc_hconf P) P"
by unfold_locales

lemma compP2_compP1_convs:
  "is_type (compP2 (compP1 P)) = is_type P"
  "is_class (compP2 (compP1 P)) = is_class P"
  "sc.addr_loc_type (compP2 (compP1 P)) = sc.addr_loc_type P"
  "sc.conf (compP2 (compP1 P)) = sc.conf P"
by(simp_all add: compP2_def heap_base.compP_conf heap_base.compP_addr_loc_type fun_eq_iff split: addr_loc.splits)

lemma sc_J_JVM_conf_read:
  "J_JVM_conf_read addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read sc_heap_write (sc_hconf P) P"
apply(rule J_JVM_conf_read.intro)
apply(rule J1_JVM_conf_read.intro)
apply(rule JVM_conf_read.intro)
 prefer 2
 apply(rule JVM_heap_conf.intro)
 apply(rule JVM_heap_conf_base'.intro)
 apply(unfold compP2_def compP1_def compP_heap compP_heap_conf compP_heap_conf_read)
 apply unfold_locales
done

end
