(*  Title:      JinjaThreads/Common/ConformThreaded.thy
    Author:     Andreas Lochbihler
*)

section \<open>Conformance for threads\<close>

theory ConformThreaded
imports
  "../Framework/FWLifting"
  "../Framework/FWWellform"
  Conform
begin

text \<open>Every thread must be represented as an object whose address is its thread ID\<close>

context heap_base begin

abbreviation thread_conf :: "'m prog \<Rightarrow> ('addr,'thread_id,'x) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where "thread_conf P \<equiv> ts_ok (\<lambda>t x m. P,m \<turnstile> t \<surd>t)"

lemma thread_confI:
  "(\<And>t xln. ts t = \<lfloor>xln\<rfloor> \<Longrightarrow> P,h \<turnstile> t \<surd>t) \<Longrightarrow> thread_conf P ts h"
by(blast intro: ts_okI)

lemma thread_confD:
  assumes "thread_conf P ts h" "ts t = \<lfloor>xln\<rfloor>"
  shows "P,h \<turnstile> t \<surd>t"
using assms by(cases xln)(auto dest: ts_okD)

lemma thread_conf_ts_upd_eq [simp]:
  assumes tst: "ts t = \<lfloor>xln\<rfloor>"
  shows "thread_conf P (ts(t \<mapsto> xln')) h \<longleftrightarrow> thread_conf P ts h"
proof
  assume tc: "thread_conf P (ts(t \<mapsto> xln')) h"
  show "thread_conf P ts h"
  proof(rule thread_confI)
    fix T XLN
    assume "ts T = \<lfloor>XLN\<rfloor>"
    with tc show "P,h \<turnstile> T \<surd>t"
      by(cases "T = t")(auto dest: thread_confD)
  qed
next
  assume tc: "thread_conf P ts h"
  show "thread_conf P (ts(t \<mapsto> xln')) h"
  proof(rule thread_confI)
    fix T XLN
    assume "(ts(t \<mapsto> xln')) T = \<lfloor>XLN\<rfloor>"
    with tst obtain XLN' where "ts T = \<lfloor>XLN'\<rfloor>"
      by(cases "T = t")(auto)
    with tc show "P,h \<turnstile> T \<surd>t"
      by(auto dest: thread_confD)
  qed
qed

end

context heap begin

lemma thread_conf_hext:
  "\<lbrakk> thread_conf P ts h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> thread_conf P ts h'"
by(blast intro: thread_confI tconf_hext_mono dest: thread_confD)

lemma thread_conf_start_state:
  "\<lbrakk> start_heap_ok; wf_syscls P \<rbrakk> \<Longrightarrow> thread_conf P (thr (start_state f P C M vs)) (shr (start_state f P C M vs))"
by(auto intro!: thread_confI simp add: start_state_def split_beta split: if_split_asm intro: tconf_start_heap_start_tid)

end

context heap_base begin 

lemma lock_thread_ok_start_state:
  "lock_thread_ok (locks (start_state f P C M vs)) (thr (start_state f P C M vs))"
by(rule lock_thread_okI)(simp add: start_state_def split_beta)

lemma wset_thread_ok_start_state:
  "wset_thread_ok (wset (start_state f P C M vs)) (thr (start_state f P C M vs))"
by(auto simp add: wset_thread_ok_def start_state_def split_beta)

lemma wset_final_ok_start_state:
  "final_thread.wset_final_ok final (wset (start_state f P C M vs)) (thr (start_state f P C M vs))"
by(rule final_thread.wset_final_okI)(simp add: start_state_def split_beta)

end

end
