(*  Title:      JinjaThreads/MM/JMM_Compiler_Type2.thy
    Author:     Andreas Lochbihler
*)

section \<open>Compiler correctness for JMM heap implementation 2\<close>

theory JMM_Compiler_Type2
imports
  JMM_Compiler
  JMM_J_Typesafe
  JMM_JVM_Typesafe
  JMM_Interp
begin

theorem J2JVM_jmm_correct:
  assumes wf: "wf_J_prog P"
  and wf_start: "jmm_wf_start_state P C M vs"
  shows "legal_execution P (jmm_J_\<E> P C M vs Running) (E, ws) \<longleftrightarrow> 
         legal_execution (J2JVM P) (jmm_JVMd_\<E> (J2JVM P) C M vs Running) (E, ws)"
using JVMd_legal_typesafe[OF wt_J2JVM[OF wf], of C M vs Running, symmetric] wf_start
by(simp only: J_legal_typesafe[OF assms] J_JVM_conf_read.red_\<E>_eq_mexecd_\<E>[OF jmm'_J_JVM_conf_read assms] J2JVM_def o_apply compP1_def compP2_def legal_execution_compP heap_base.wf_start_state_compP jmm_typeof_addr_compP heap_base.heap_read_typed_compP)

theorem J2JVM_jmm_correct_weak:
  assumes wf: "wf_J_prog P"
  and wf_start: "jmm_wf_start_state P C M vs"
  shows "weakly_legal_execution P (jmm_J_\<E> P C M vs Running) (E, ws) \<longleftrightarrow> 
         weakly_legal_execution (J2JVM P) (jmm_JVMd_\<E> (J2JVM P) C M vs Running) (E, ws)"
using JVMd_weakly_legal_typesafe[OF wt_J2JVM[OF wf], of C M vs Running, symmetric] wf_start
by(simp only: J_weakly_legal_typesafe[OF assms] J_JVM_conf_read.red_\<E>_eq_mexecd_\<E>[OF jmm'_J_JVM_conf_read assms] J2JVM_def o_apply compP1_def compP2_def weakly_legal_execution_compP heap_base.wf_start_state_compP jmm_typeof_addr_compP heap_base.heap_read_typed_compP)

theorem J2JVM_jmm_correctly_synchronized:
  assumes wf: "wf_J_prog P"
  and wf_start: "jmm_wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set jmm.start_addrs"
  shows "correctly_synchronized (J2JVM P) (jmm_JVMd_\<E> (J2JVM P) C M vs Running) \<longleftrightarrow> 
         correctly_synchronized P (jmm_J_\<E> P C M vs Running)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  show ?rhs unfolding correctly_synchronized_def
  proof(intro strip)
    fix E ws a a'
    assume E: "E \<in> jmm_J_\<E> P C M vs Running"
      and wf_exec: "P \<turnstile> (E, ws) \<surd>"
      and sc: "sequentially_consistent P (E, ws)"
      and actions: "a \<in> actions E" "a' \<in> actions E"
      and conflict: "P,E \<turnstile> a \<dagger> a'"

    from E wf_exec sc
    have "legal_execution P (jmm_J_\<E> P C M vs Running) (E, ws)"
      by(rule sc_legal.SC_is_legal[OF J_allocated_progress.J_sc_legal[OF jmm_J_allocated_progress wf jmm_heap_read_typeable wf_start ka]])
    hence "legal_execution (J2JVM P) (jmm_JVMd_\<E> (J2JVM P) C M vs Running) (E, ws)"
      by(simp only: J2JVM_jmm_correct[OF wf wf_start])
    hence "E \<in> jmm_JVMd_\<E> (J2JVM P) C M vs Running" "J2JVM P \<turnstile> (E, ws) \<surd>"
      by(simp_all add: gen_legal_execution.simps)
    moreover from sc have "sequentially_consistent (J2JVM P) (E, ws)"
      by(simp add: J2JVM_def compP2_def)
    moreover from conflict have "J2JVM P,E \<turnstile> a \<dagger> a'"
      by(simp add: J2JVM_def compP2_def)
    ultimately have "J2JVM P,E \<turnstile> a \<le>hb a' \<or> J2JVM P,E \<turnstile> a' \<le>hb a"
      using \<open>?lhs\<close> actions by(auto simp add: correctly_synchronized_def)
    thus "P,E \<turnstile> a \<le>hb a' \<or> P,E \<turnstile> a' \<le>hb a"
      by(simp add: J2JVM_def compP2_def)
  qed
next
  assume ?rhs
  show ?lhs unfolding correctly_synchronized_def
  proof(intro strip)
    fix E ws a a'
    assume E: "E \<in> jmm_JVMd_\<E> (J2JVM P) C M vs Running"
      and wf_exec: "J2JVM P \<turnstile> (E, ws) \<surd>"
      and sc: "sequentially_consistent (J2JVM P) (E, ws)"
      and actions: "a \<in> actions E" "a' \<in> actions E"
      and conflict: "J2JVM P,E \<turnstile> a \<dagger> a'"

    from wf have "wf_jvm_prog (J2JVM P)" by(rule wt_J2JVM)
    then obtain \<Phi> where wf': "wf_jvm_prog\<^bsub>\<Phi>\<^esub> (J2JVM P)"
      by(auto simp add: wf_jvm_prog_def)
    from wf_start have wf_start': "jmm_wf_start_state (J2JVM P) C M vs"
      by(simp add: J2JVM_def compP2_def heap_base.wf_start_state_compP)
    from E wf_exec sc
    have "legal_execution (J2JVM P) (jmm_JVMd_\<E> (J2JVM P) C M vs Running) (E, ws)"
      by(rule sc_legal.SC_is_legal[OF JVM_allocated_progress.JVM_sc_legal[OF jmm_JVM_allocated_progress wf' jmm_heap_read_typeable wf_start' ka]])
    hence "legal_execution P (jmm_J_\<E> P C M vs Running) (E, ws)"
      by(simp only: J2JVM_jmm_correct[OF wf wf_start])
    hence "E \<in> jmm_J_\<E> P C M vs Running" "P \<turnstile> (E, ws) \<surd>"
      by(simp_all add: gen_legal_execution.simps)
    moreover from sc have "sequentially_consistent P (E, ws)"
      by(simp add: J2JVM_def compP2_def)
    moreover from conflict have "P,E \<turnstile> a \<dagger> a'"
      by(simp add: J2JVM_def compP2_def)
    ultimately have "P,E \<turnstile> a \<le>hb a' \<or> P,E \<turnstile> a' \<le>hb a"
      using \<open>?rhs\<close> actions by(auto simp add: correctly_synchronized_def)
    thus "J2JVM P,E \<turnstile> a \<le>hb a' \<or> J2JVM P,E \<turnstile> a' \<le>hb a" 
      by(simp add: J2JVM_def compP2_def)
  qed
qed

end
