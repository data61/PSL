(*  Title:      JinjaThreads/Compiler/J1JVMBisim.thy
    Author:     Andreas Lochbihler
*)

section \<open>The delay bisimulation between intermediate language and JVM\<close>

theory J1JVMBisim imports 
  Execs
  "../BV/BVNoTypeError"
  J1
begin

declare Listn.lesub_list_impl_same_size[simp del]

lemma (in JVM_heap_conf_base') \<tau>exec_1_\<tau>exec_1_d:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<tau>exec_1 P t \<sigma> \<sigma>'; \<Phi> |- t:\<sigma> [ok] \<rbrakk> \<Longrightarrow> \<tau>exec_1_d P t \<sigma> \<sigma>'"
by(auto simp add: \<tau>exec_1_def \<tau>exec_1_d_def welltyped_commute[symmetric] elim: jvmd_NormalE)

context JVM_conf_read begin

lemma \<tau>Exec_1r_preserves_correct_state:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and exec: "\<tau>Exec_1r P t \<sigma> \<sigma>'"
  shows "\<Phi> |- t:\<sigma> [ok] \<Longrightarrow> \<Phi> |- t:\<sigma>' [ok]"
using exec
by(induct)(blast intro: BV_correct_1[OF wf])+

lemma \<tau>Exec_1t_preserves_correct_state:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and exec: "\<tau>Exec_1t P t \<sigma> \<sigma>'"
  shows "\<Phi> |- t:\<sigma> [ok] \<Longrightarrow> \<Phi> |- t:\<sigma>' [ok]"
using exec
by(induct)(blast intro: BV_correct_1[OF wf])+

lemma \<tau>Exec_1r_\<tau>Exec_1_dr:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "\<lbrakk> \<tau>Exec_1r P t \<sigma> \<sigma>'; \<Phi> |- t:\<sigma> [ok] \<rbrakk> \<Longrightarrow> \<tau>Exec_1_dr P t \<sigma> \<sigma>'"
apply(induct rule: rtranclp_induct)
apply(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_1_\<tau>exec_1_d[OF wf] \<tau>Exec_1r_preserves_correct_state[OF wf])+
done

lemma \<tau>Exec_1t_\<tau>Exec_1_dt:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "\<lbrakk> \<tau>Exec_1t P t \<sigma> \<sigma>'; \<Phi> |- t:\<sigma> [ok] \<rbrakk> \<Longrightarrow> \<tau>Exec_1_dt P t \<sigma> \<sigma>'"
apply(induct rule: tranclp_induct)
apply(blast intro: tranclp.trancl_into_trancl \<tau>exec_1_\<tau>exec_1_d[OF wf] \<tau>Exec_1t_preserves_correct_state[OF wf])+
done

lemma \<tau>Exec_1_dr_preserves_correct_state:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and exec: "\<tau>Exec_1_dr P t \<sigma> \<sigma>'"
  shows "\<Phi> |- t: \<sigma> [ok] \<Longrightarrow> \<Phi> |- t: \<sigma>' [ok]"
using exec
by(induct)(blast intro: BV_correct_1[OF wf])+

lemma \<tau>Exec_1_dt_preserves_correct_state:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and exec: "\<tau>Exec_1_dt P t \<sigma> \<sigma>'"
  shows "\<Phi> |- t:\<sigma> [ok] \<Longrightarrow> \<Phi> |- t:\<sigma>' [ok]"
using exec
by(induct)(blast intro: BV_correct_1[OF wf])+

end

locale J1_JVM_heap_base =
  J1_heap_base +
  JVM_heap_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

inductive bisim1 ::
  "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 \<Rightarrow> ('addr expr1 \<times> 'addr locals1)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"

  and bisims1 :: 
  "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 list \<Rightarrow> ('addr expr1 list \<times> 'addr locals1)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
  
  and bisim1_syntax :: 
  "'m prog \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
  ("_,_,_ \<turnstile> _ \<leftrightarrow> _" [50, 0, 0, 0, 50] 100)

  and bisims1_syntax :: 
  "'m prog \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr locals1)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
  ("_,_,_ \<turnstile> _ [\<leftrightarrow>] _" [50, 0, 0, 0, 50] 100)
  for P :: "'m prog" and  h :: 'heap
where
  "P, e, h \<turnstile> exs \<leftrightarrow> s \<equiv> bisim1 P h e exs s"
| "P, es, h \<turnstile> esxs [\<leftrightarrow>] s \<equiv> bisims1 P h es esxs s"

| bisim1Val2:
  "pc = length (compE2 e) \<Longrightarrow> P, e, h \<turnstile> (Val v, xs) \<leftrightarrow> (v # [], xs, pc, None)"

| bisim1New:
  "P, new C, h \<turnstile> (new C, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1NewThrow:
  "P, new C, h \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1NewArray:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, h \<turnstile> (newA T\<lfloor>e'\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1NewArrayThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1NewArrayFail:
  "P, newA T\<lfloor>e\<rceil>, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>a\<rfloor>)"


| bisim1Cast:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, Cast T e, h \<turnstile> (Cast T e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CastThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, Cast T e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CastFail:
  "P, Cast T e, h \<turnstile> (THROW ClassCast, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"


| bisim1InstanceOf:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, e instanceof T, h \<turnstile> (e' instanceof T, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1InstanceOfThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, e instanceof T, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Val: "P, Val v, h \<turnstile> (Val v, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1Var: "P, Var V, h \<turnstile> (Var V, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1BinOp1:
  "P, e1, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, h \<turnstile> (e'\<guillemotleft>bop\<guillemotright>e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BinOp2:
  "P, e2, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e', xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"

| bisim1BinOpThrow1:
  "P, e1, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow2:
  "P, e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow:
  "P, e1\<guillemotleft>bop\<guillemotright>e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([v1, v2], xs, length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1LAss1:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, V:=e, h \<turnstile> (V:=e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1LAss2:
  "P, V:=e, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e)), None)"

| bisim1LAssThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, V:=e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1AAcc1:
  "P, a, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, h \<turnstile> (a'\<lfloor>i\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAcc2:
  "P, i, h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, h \<turnstile> (Val v\<lfloor>i'\<rceil>, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAccThrow1:
  "P, a, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccThrow2:
  "P, i, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccFail:
  "P, a\<lfloor>i\<rceil>, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([v, v'], xs, length (compE2 a) + length (compE2 i), \<lfloor>ad\<rfloor>)"


| bisim1AAss1:
  "P, a, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (a'\<lfloor>i\<rceil> := e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAss2:
  "P, i, h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Val v\<lfloor>i'\<rceil> := e, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAss3:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e', xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"

| bisim1AAssThrow1:
  "P, a, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow2:
  "P, i, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow3:
  "P, e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssFail:
  "P, a\<lfloor>i\<rceil> := e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([v', v, v''], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>ad\<rfloor>)"

| bisim1AAss4:
  "P, a\<lfloor>i\<rceil> := e, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"


| bisim1ALength: 
  "P, a, h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<bullet>length, h \<turnstile> (a'\<bullet>length, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1ALengthThrow:
  "P, a, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<bullet>length, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"


| bisim1ALengthNull:
  "P, a\<bullet>length, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAcc: 
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e\<bullet>F{D}, h \<turnstile> (e'\<bullet>F{D}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAccThrow:
  "P, e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e\<bullet>F{D}, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAccNull:
  "P, e\<bullet>F{D}, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAss1: 
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e\<bullet>F{D} := e2, h \<turnstile> (e'\<bullet>F{D} := e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAss2: 
  "P, e2, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e\<bullet>F{D} := e2, h \<turnstile> (Val v\<bullet>F{D} := e', xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, xcp)"

| bisim1FAssThrow1:
  "P, e, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e\<bullet>F{D} := e2, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssThrow2:
  "P, e2, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e\<bullet>F{D} := e2, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssNull:
  "P, e\<bullet>F{D} := e2, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 e) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1FAss3:
  "P, e\<bullet>F{D} := e2, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None)"


| bisim1CAS1:
  "P, e1, h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (e1'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CAS2:
  "P, e2, h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, e2', e3), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e1) + pc, xcp)"

| bisim1CAS3:
  "P, e3, h \<turnstile> (e3', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e3'), xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, xcp)"

| bisim1CASThrow1:
  "P, e1, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1CASThrow2:
  "P, e2, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e1) + pc, \<lfloor>ad\<rfloor>)"

| bisim1CASThrow3:
  "P, e3, h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, \<lfloor>ad\<rfloor>)"

| bisim1CASFail:
  "P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([v', v, v''], xs, length (compE2 e1) + length (compE2 e2) + length (compE2 e3), \<lfloor>ad\<rfloor>)"


| bisim1Call1:
  "P, obj, h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, obj\<bullet>M(ps), h \<turnstile> (obj'\<bullet>M(ps), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CallParams:
  "P, ps, h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)
  \<Longrightarrow> P, obj\<bullet>M(ps), h \<turnstile> (Val v\<bullet>M(ps'), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) +  pc, xcp)"

| bisim1CallThrowObj:
  "P, obj, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, obj\<bullet>M(ps), h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrowParams:
  "P, ps, h \<turnstile> (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, obj\<bullet>M(ps), h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrow:
  "length ps = length vs
  \<Longrightarrow> P, obj\<bullet>M(ps), h \<turnstile> (Throw a, xs) \<leftrightarrow> (vs @ [v], xs, length (compE2 obj) + length (compEs2 ps), \<lfloor>a\<rfloor>)"

| bisim1BlockSome1:
  "P, {V:T=\<lfloor>v\<rfloor>; e}, h \<turnstile> ({V:T=\<lfloor>v\<rfloor>; e}, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1BlockSome2:
  "P, {V:T=\<lfloor>v\<rfloor>; e}, h \<turnstile> ({V:T=\<lfloor>v\<rfloor>; e}, xs) \<leftrightarrow> ([v], xs, Suc 0, None)"

| bisim1BlockSome4:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, h \<turnstile> ({V:T=None; e'}, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockThrowSome:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), \<lfloor>a\<rfloor>)"

| bisim1BlockNone:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, {V:T=None; e}, h \<turnstile> ({V:T=None; e'}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BlockThrowNone:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
   \<Longrightarrow> P, {V:T=None; e}, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Sync1:
  "P, e1, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (sync\<^bsub>V\<^esub> (e') e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Sync2:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v, v], xs, Suc (length (compE2 e1)), None)"

| bisim1Sync3:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v], xs[V := v], Suc (Suc (length (compE2 e1))), None)"

| bisim1Sync4:
  "P, e2, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (insync\<^bsub>V\<^esub> (a) e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp)"

| bisim1Sync5:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Val v, xs) \<leftrightarrow> ([xs ! V, v], xs, 4 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync6:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync7:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 6 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync8:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
                         ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync9:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync10:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync11:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync12:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([v, v'], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync14:
  "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow>
        ([v, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1SyncThrow:
  "P, e1, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1InSync: \<comment> \<open>This rule only exists such that @{text "P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)"} holds for all @{text "e"}\<close> 
  "P, insync\<^bsub>V\<^esub> (a) e, h \<turnstile> (insync\<^bsub>V\<^esub> (a) e, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1Seq1:
  "P, e1, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, e1;;e2, h \<turnstile> (e';;e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1SeqThrow1:
  "P, e1, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, e1;;e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1Seq2:
  "P, e2, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e1;;e2, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (length (compE2 e1) + pc), xcp)"


| bisim1Cond1:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, if (e) e1 else e2, h \<turnstile> (if (e') e1 else e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CondThen:
  "P, e1, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, if (e) e1 else e2, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (length (compE2 e) + pc), xcp)"

| bisim1CondElse:
  "P, e2, h \<turnstile> exs \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, if (e) e1 else e2, h \<turnstile> exs \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) +  pc)), xcp)"

| bisim1CondThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, if (e) e1 else e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1While1:
  "P, while (c) e, h \<turnstile> (while (c) e, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1While3:
  "P, c, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, while (c) e, h \<turnstile> (if (e') (e;; while (c) e) else unit, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1While4:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, while (c) e, h  \<turnstile> (e';; while (c) e, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"

| bisim1While6:
  "P, while (c) e, h \<turnstile> (while (c) e, xs) \<leftrightarrow> ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"

| bisim1While7:
  "P, while (c) e, h \<turnstile> (unit, xs) \<leftrightarrow> ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"

| bisim1WhileThrow1:
  "P, c, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, while (c) e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1WhileThrow2:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
   \<Longrightarrow> P, while (c) e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"


| bisim1Throw1:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, throw e, h \<turnstile> (throw e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Throw2:
  "P, throw e, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 e), \<lfloor>a\<rfloor>)"

| bisim1ThrowNull:
  "P, throw e, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1ThrowThrow:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> P, throw e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Try:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
   \<Longrightarrow> P, try e catch(C V) e2, h \<turnstile> (try e' catch(C V) e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1TryCatch1:
  "\<lbrakk> P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); typeof_addr h a = \<lfloor>Class_type C'\<rfloor>; P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P, try e catch(C V) e2, h \<turnstile> ({V:Class C=None; e2}, xs[V := Addr a]) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e)), None)"

| bisim1TryCatch2:
  "P, e2, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
   \<Longrightarrow> P, try e catch(C V) e2, h \<turnstile> ({V:Class C=None; e'}, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"

| bisim1TryFail:
  "\<lbrakk> P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); typeof_addr h a = \<lfloor>Class_type C'\<rfloor>; \<not> P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk> 
  \<Longrightarrow> P, try e catch(C V) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1TryCatchThrow:
  "P, e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
   \<Longrightarrow> P, try e catch(C V) e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), \<lfloor>a\<rfloor>)"

| bisims1Nil: "P, [], h \<turnstile> ([], xs) [\<leftrightarrow>] ([], xs, 0, None)"

| bisims1List1:
  "P, e, h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> P, e#es, h \<turnstile> (e'#es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"

| bisims1List2:
  "P, es, h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)
  \<Longrightarrow> P, e#es, h \<turnstile> (Val v # es', xs) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, xcp)"


inductive_cases bisim1_cases:
  "P,e,h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, xcp)"


lemma bisim1_refl: "P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)"
  and bisims1_refl: "P,es,h \<turnstile> (es, xs) [\<leftrightarrow>] ([], xs, 0, None)"
apply(induct e and es rule: call.induct calls.induct)
apply(auto intro: bisim1_bisims1.intros simp add: nat_fun_sum_eq_conv)
apply(rename_tac option a)
apply(case_tac option)
apply(auto intro: bisim1_bisims1.intros split: if_split_asm)
done

lemma bisims1_lengthD: "P, es, h \<turnstile> (es', xs) [\<leftrightarrow>] s \<Longrightarrow> length es = length es'"
apply(induct es arbitrary: es' s)
apply(auto elim: bisims1.cases)
done

text \<open>
  Derive an alternative induction rule for @{term bisim1} such that
  (i) induction hypothesis are generated for all subexpressions and
  (ii) the number of surrounding blocks is passed through.
\<close>

inductive bisim1' :: 
  "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 \<Rightarrow> nat \<Rightarrow> ('addr expr1 \<times> 'addr locals1) 
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"

  and bisims1' :: 
  "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 list \<Rightarrow> nat \<Rightarrow> ('addr expr1 list \<times> 'addr locals1)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"

  and bisim1'_syntax :: 
  "'m prog \<Rightarrow> 'addr expr1 \<Rightarrow> nat \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 \<times> 'addr locals1) 
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile>'' _ \<leftrightarrow> _" [50, 0, 0, 0, 0, 50] 100)

  and bisims1'_syntax :: 
  "'m prog \<Rightarrow> 'addr expr1 list \<Rightarrow> nat \<Rightarrow> 'heap \<Rightarrow> ('addr expr1 list \<times> 'addr val list) 
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile>'' _ [\<leftrightarrow>] _" [50, 0, 0, 0, 0, 50] 100)
  for P :: "'m prog" and  h :: 'heap
where
  "P, e, n, h \<turnstile>' exs \<leftrightarrow> s \<equiv> bisim1' P h e n exs s"
| "P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s \<equiv> bisims1' P h es n esxs s"

| bisim1Val2':
  "P, e, n, h \<turnstile>' (Val v, xs) \<leftrightarrow> (v # [], xs, length (compE2 e), None)"

| bisim1New':
  "P, new C, n, h \<turnstile>' (new C, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1NewThrow':
  "P, new C, n, h \<turnstile>' (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"


| bisim1NewArray':
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (newA T\<lfloor>e'\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1NewArrayThrow':
  "P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1NewArrayFail':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, newA T\<lfloor>e\<rceil>, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>a\<rfloor>)"


| bisim1Cast':
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (Cast T e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CastThrow':
  "P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CastFail':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, Cast T e, n, h \<turnstile>' (THROW ClassCast, xs) \<leftrightarrow> ([v], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"


| bisim1InstanceOf':
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e instanceof T, n, h \<turnstile>' (e' instanceof T, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1InstanceOfThrow':
  "P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, e instanceof T, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Val': "P, Val v, n, h \<turnstile>' (Val v, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1Var': "P, Var V, n, h \<turnstile>' (Var V, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1BinOp1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (e'\<guillemotleft>bop\<guillemotright>e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BinOp2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Val v1 \<guillemotleft>bop\<guillemotright> e', xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"

| bisim1BinOpThrow1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)"

| bisim1BinOpThrow':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None); 
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([v1, v2], xs, length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1LAss1':
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, V:=e, n, h \<turnstile>' (V:=e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1LAss2':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
   \<Longrightarrow> P, V:=e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e)), None)"

| bisim1LAssThrow':
  "P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, V:=e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1AAcc1':
  "\<lbrakk> P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (a'\<lfloor>i\<rceil>, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAcc2':
  "\<lbrakk> P, i, n, h \<turnstile>' (i', xs) \<leftrightarrow> (stk, loc, pc, xcp); \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Val v\<lfloor>i'\<rceil>, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAccThrow1':
  "\<lbrakk> P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccThrow2':
  "\<lbrakk> P, i, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAccFail':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil>, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> ([v, v'], xs, length (compE2 a) + length (compE2 i), \<lfloor>ad\<rfloor>)"


| bisim1AAss1':
  "\<lbrakk> P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (a'\<lfloor>i\<rceil> := e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1AAss2':
  "\<lbrakk> P, i, n, h \<turnstile>' (i', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Val v\<lfloor>i'\<rceil> := e, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"

| bisim1AAss3':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Val v\<lfloor>Val v'\<rceil> := e', xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"

| bisim1AAssThrow1':
  "\<lbrakk> P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None); 
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow2':
  "\<lbrakk> P, i, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>); 
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssThrow3':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None); 
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, \<lfloor>ad\<rfloor>)"

| bisim1AAssFail':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None);  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> ([v', v, v''], xs, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>ad\<rfloor>)"

| bisim1AAss4':
  "\<lbrakk> \<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None);  
     \<And>xs. P, i, n, h \<turnstile>' (i, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, a\<lfloor>i\<rceil> := e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"


| bisim1ALength': 
  "P, a, n, h \<turnstile>' (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (a'\<bullet>length, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1ALengthThrow':
  "P, a, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"


| bisim1ALengthNull':
  "(\<And>xs. P, a, n, h \<turnstile>' (a, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, a\<bullet>length, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAcc': 
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (e'\<bullet>F{D}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAccThrow':
  "P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)
  \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAccNull':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
   \<Longrightarrow> P, e\<bullet>F{D}, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"


| bisim1FAss1': 
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (e'\<bullet>F{D} := e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1FAss2': 
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Val v\<bullet>F{D} := e', xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, xcp)"

| bisim1FAssThrow1':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssThrow2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>ad\<rfloor>)"

| bisim1FAssNull':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 e) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1FAss3':
  "\<lbrakk> \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None); 
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e\<bullet>F{D} := e2, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None)"


| bisim1CAS1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
    \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e3, n, h \<turnstile>' (e3, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (e1'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CAS2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
    \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e3, n, h \<turnstile>' (e3, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Val v\<bullet>compareAndSwap(D\<bullet>F, e2', e3), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e1) + pc, xcp)"

| bisim1CAS3':
  "\<lbrakk> P, e3, n, h \<turnstile>' (e3', xs) \<leftrightarrow> (stk, loc, pc, xcp);
    \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e3'), xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, xcp)"

| bisim1CASThrow1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
    \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e3, n, h \<turnstile>' (e3, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>)"

| bisim1CASThrow2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
    \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e3, n, h \<turnstile>' (e3, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 e1) + pc, \<lfloor>ad\<rfloor>)"

| bisim1CASThrow3':
  "\<lbrakk> P, e3, n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>ad\<rfloor>);
    \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, \<lfloor>ad\<rfloor>)"

| bisim1CASFail':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None); 
    \<And>xs. P, e3, n, h \<turnstile>' (e3, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), n, h \<turnstile>' (Throw ad, xs) \<leftrightarrow> ([v', v, v''], xs, length (compE2 e1) + length (compE2 e2) + length (compE2 e3), \<lfloor>ad\<rfloor>)"


| bisim1Call1':
  "\<lbrakk> P, obj, n, h \<turnstile>' (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (obj'\<bullet>M(ps), xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CallParams':
  "\<lbrakk> P, ps, n, h \<turnstile>' (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); ps \<noteq> [];
     \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Val v\<bullet>M(ps'), xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) +  pc, xcp)"

| bisim1CallThrowObj':
  "\<lbrakk> P, obj, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None)\<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrowParams':
  "\<lbrakk> P, ps, n, h \<turnstile>' (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"

| bisim1CallThrow':
  "\<lbrakk> length ps = length vs;
     \<And>xs. P, obj, n, h \<turnstile>' (obj, xs) \<leftrightarrow> ([], xs, 0, None); \<And>xs. P, ps, n, h \<turnstile>' (ps, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, obj\<bullet>M(ps), n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (vs @ [v], xs, length (compE2 obj) + length (compEs2 ps), \<lfloor>a\<rfloor>)"

| bisim1BlockSome1':
  "(\<And>xs. P, e, Suc n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, n, h \<turnstile>' ({V:T=\<lfloor>v\<rfloor>; e}, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1BlockSome2':
  "(\<And>xs. P, e, Suc n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, n, h \<turnstile>' ({V:T=\<lfloor>v\<rfloor>; e}, xs) \<leftrightarrow> ([v], xs, Suc 0, None)"

| bisim1BlockSome4':
  "P, e, Suc n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, n, h \<turnstile>' ({V:T=None; e'}, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"

| bisim1BlockThrowSome':
  "P, e, Suc n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, {V:T=\<lfloor>v\<rfloor>; e}, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), \<lfloor>a\<rfloor>)"

| bisim1BlockNone':
  "P, e, Suc n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, {V:T=None; e}, n, h \<turnstile>' ({V:T=None; e'}, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1BlockThrowNone':
  "P, e, Suc n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, {V:T=None; e}, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Sync1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
     \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (sync\<^bsub>V\<^esub> (e') e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Sync2':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v, v], xs, Suc (length (compE2 e1)), None)"

| bisim1Sync3':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (sync\<^bsub>V\<^esub> (Val v) e2, xs) \<leftrightarrow> ([v], xs[V := v], Suc (Suc (length (compE2 e1))), None)"

| bisim1Sync4':
  "\<lbrakk> P, e2, Suc n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); 
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp)"

| bisim1Sync5':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Val v, xs) \<leftrightarrow> ([xs ! V, v], xs, 4 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync6':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync7':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 6 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync8':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
        ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync9':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"

| bisim1Sync10':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync11':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1Sync12':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([v, v'], xs, 4 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1Sync14':
  "\<lbrakk> \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow>
        ([v, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"

| bisim1SyncThrow':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); 
    \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, sync\<^bsub>V\<^esub> (e1) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1InSync':
  "P, insync\<^bsub>V\<^esub> (a) e, n, h \<turnstile>' (insync\<^bsub>V\<^esub> (a) e, xs) \<leftrightarrow> ([], xs, 0, None)"


| bisim1Seq1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (e';;e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1SeqThrow1':
  "\<lbrakk> P, e1, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1Seq2':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e1;;e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 e1) + pc), xcp)"


| bisim1Cond1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (if (e') e1 else e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1CondThen':
  "\<lbrakk> P, e1, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 e) + pc), xcp)"

| bisim1CondElse':
  "\<lbrakk> P, e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) +  pc)), xcp)"

| bisim1CondThrow':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e1, n, h \<turnstile>' (e1, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e2, n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, if (e) e1 else e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1While1':
  "\<lbrakk> \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (while (c) e, xs) \<leftrightarrow> ([], xs, 0, None)"

| bisim1While3':
  "\<lbrakk> P, c, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (if (e') (e;; while (c) e) else unit, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1While4':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h  \<turnstile>' (e';; while (c) e, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"

| bisim1While6':
  "\<lbrakk> \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile>' (while (c) e, xs) \<leftrightarrow> ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"

| bisim1While7':
  "\<lbrakk> \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> \<Longrightarrow> 
  P, while (c) e, n, h \<turnstile>' (unit, xs) \<leftrightarrow> ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"

| bisim1WhileThrow1':
  "\<lbrakk> P, c, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1WhileThrow2':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); 
     \<And>xs. P, c, n, h \<turnstile>' (c, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, while (c) e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"


| bisim1Throw1':
  "P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (throw e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1Throw2':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 e), \<lfloor>a\<rfloor>)"

| bisim1ThrowNull':
  "(\<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None))
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (THROW NullPointer, xs) \<leftrightarrow> ([Null], xs, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"

| bisim1ThrowThrow':
  "P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> P, throw e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"


| bisim1Try':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, n, h \<turnstile>' (try e' catch(C V) e2, xs) \<leftrightarrow> (stk, loc, pc, xcp)"

| bisim1TryCatch1':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); typeof_addr h a = \<lfloor>Class_type C'\<rfloor>; P \<turnstile> C' \<preceq>\<^sup>* C;
     \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, try e catch(C V) e2, n, h \<turnstile>' ({V:Class C=None; e2}, xs[V := Addr a]) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e)), None)"

| bisim1TryCatch2':
  "\<lbrakk> P, e2, Suc n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, n, h \<turnstile>' ({V:Class C=None; e'}, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"

| bisim1TryFail':
  "\<lbrakk> P, e, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); typeof_addr h a = \<lfloor>Class_type C'\<rfloor>; \<not> P \<turnstile> C' \<preceq>\<^sup>* C;
     \<And>xs. P, e2, Suc n, h \<turnstile>' (e2, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk> 
  \<Longrightarrow> P, try e catch(C V) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

| bisim1TryCatchThrow':
  "\<lbrakk> P, e2, Suc n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
   \<Longrightarrow> P, try e catch(C V) e2, n, h \<turnstile>' (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), \<lfloor>a\<rfloor>)"

| bisims1Nil': "P, [], n, h \<turnstile>' ([], xs) [\<leftrightarrow>] ([], xs, 0, None)"

| bisims1List1':
  "\<lbrakk> P, e, n, h \<turnstile>' (e', xs) \<leftrightarrow> (stk, loc, pc, xcp);
     \<And>xs. P, es, n, h \<turnstile>' (es, xs) [\<leftrightarrow>] ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e#es, n, h \<turnstile>' (e'#es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"

| bisims1List2':
  "\<lbrakk> P, es, n, h \<turnstile>' (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp);
     \<And>xs. P, e, n, h \<turnstile>' (e, xs) \<leftrightarrow> ([], xs, 0, None) \<rbrakk>
  \<Longrightarrow> P, e#es, n, h \<turnstile>' (Val v # es', xs) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, xcp)"

lemma bisim1'_refl: "P,e,n,h \<turnstile>' (e,xs) \<leftrightarrow> ([],xs,0,None)"
  and bisims1'_refl: "P,es,n,h \<turnstile>' (es,xs) [\<leftrightarrow>] ([],xs,0,None)"
apply(induct e and es arbitrary: n xs and n xs rule: call.induct calls.induct)
apply(auto intro: bisim1'_bisims1'.intros simp add: nat_fun_sum_eq_conv)
apply(rename_tac option a b c)
apply(case_tac option)
apply(auto intro: bisim1'_bisims1'.intros simp add: fun_eq_iff split: if_split_asm)
done

lemma bisim1_imp_bisim1': "P, e, h \<turnstile> exs \<leftrightarrow> s \<Longrightarrow> P, e, n, h \<turnstile>' exs \<leftrightarrow> s"
  and bisims1_imp_bisims1': "P, es, h \<turnstile> esxs [\<leftrightarrow>] s \<Longrightarrow> P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s"
proof(induct arbitrary: n and n rule: bisim1_bisims1.inducts)
  case (bisim1CallParams ps ps' xs stk loc pc xcp obj M v)
  show ?case
  proof(cases "ps = []")
    case True
    with \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)\<close> have "ps' = []" "pc = 0" "stk = []" "loc = xs" "xcp = None"
      by(auto elim: bisims1.cases)
    moreover have "P,obj,n,h \<turnstile>' (Val v,xs) \<leftrightarrow> ([v],xs,length (compE2 obj),None)"
      by(blast intro: bisim1Val2' bisim1'_refl)
    hence "P,obj\<bullet>M([]),n,h \<turnstile>' (Val v\<bullet>M([]),xs) \<leftrightarrow> ([v],xs,length (compE2 obj),None)"
      by-(rule bisim1Call1', auto intro!: bisims1Nil' simp add: bsoks_def)
    ultimately show ?thesis using True by simp
  next
    case False with bisim1CallParams show ?thesis
      by(auto intro: bisim1CallParams' bisims1'_refl bisim1'_refl)
  qed
qed(auto intro: bisim1'_bisims1'.intros bisim1'_refl bisims1'_refl)

lemma bisim1'_imp_bisim1: "P, e, n, h \<turnstile>' exs \<leftrightarrow> s \<Longrightarrow> P, e, h \<turnstile> exs \<leftrightarrow> s"
  and bisims1'_imp_bisims1: "P, es, n, h \<turnstile>' esxs [\<leftrightarrow>] s \<Longrightarrow> P, es, h \<turnstile> esxs [\<leftrightarrow>] s"
apply(induct rule: bisim1'_bisims1'.inducts)
apply(blast intro: bisim1_bisims1.intros)+
done

lemma bisim1'_eq_bisim1: "bisim1' P h e n = bisim1 P h e"
  and bisims1'_eq_bisims1: "bisims1' P h es n = bisims1 P h es"
by(blast intro!: ext bisim1_imp_bisim1' bisims1_imp_bisims1' bisim1'_imp_bisim1 bisims1'_imp_bisims1)+

end

(* FIXME: Take lemmas out of locale to speed up opening the context *)

lemmas bisim1_bisims1_inducts = 
  J1_JVM_heap_base.bisim1'_bisims1'.inducts
  [simplified J1_JVM_heap_base.bisim1'_eq_bisim1 J1_JVM_heap_base.bisims1'_eq_bisims1, 
  consumes 1,
  case_names bisim1Val2 bisim1New bisim1NewThrow
  bisim1NewArray bisim1NewArrayThrow bisim1NewArrayFail bisim1Cast bisim1CastThrow bisim1CastFail
  bisim1InstanceOf bisim1InstanceOfThrow
  bisim1Val bisim1Var bisim1BinOp1 bisim1BinOp2 bisim1BinOpThrow1 bisim1BinOpThrow2 bisim1BinOpThrow
  bisim1LAss1 bisim1LAss2 bisim1LAssThrow
  bisim1AAcc1 bisim1AAcc2 bisim1AAccThrow1 bisim1AAccThrow2 bisim1AAccFail
  bisim1AAss1 bisim1AAss2 bisim1AAss3 bisim1AAssThrow1 bisim1AAssThrow2
  bisim1AAssThrow3 bisim1AAssFail bisim1AAss4
  bisim1ALength bisim1ALengthThrow bisim1ALengthNull
  bisim1FAcc bisim1FAccThrow bisim1FAccNull
  bisim1FAss1 bisim1FAss2 bisim1FAssThrow1 bisim1FAssThrow2 bisim1FAssNull bisim1FAss3
  bisim1CAS1 bisim1CAS2 bisim1CAS3 bisim1CASThrow1 bisim1CASThrow2
  bisim1CASThrow3 bisim1CASFail
  bisim1Call1 bisim1CallParams bisim1CallThrowObj bisim1CallThrowParams
  bisim1CallThrow
  bisim1BlockSome1 bisim1BlockSome2 bisim1BlockSome4 bisim1BlockThrowSome
  bisim1BlockNone bisim1BlockThrowNone
  bisim1Sync1 bisim1Sync2 bisim1Sync3 bisim1Sync4 bisim1Sync5 bisim1Sync6
  bisim1Sync7 bisim1Sync8 bisim1Sync9 bisim1Sync10 bisim1Sync11 bisim1Sync12
  bisim1Sync14 bisim1SyncThrow bisim1InSync
  bisim1Seq1 bisim1SeqThrow1 bisim1Seq2
  bisim1Cond1 bisim1CondThen bisim1CondElse bisim1CondThrow
  bisim1While1 bisim1While3 bisim1While4
  bisim1While6 bisim1While7 bisim1WhileThrow1 bisim1WhileThrow2
  bisim1Throw1 bisim1Throw2 bisim1ThrowNull bisim1ThrowThrow
  bisim1Try bisim1TryCatch1 bisim1TryCatch2 bisim1TryFail bisim1TryCatchThrow
  bisims1Nil bisims1List1 bisims1List2]

lemmas bisim1_bisims1_inducts_split = bisim1_bisims1_inducts[split_format (complete)]

context J1_JVM_heap_base begin

lemma bisim1_pc_length_compE2: "P,E,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> pc \<le> length (compE2 E)"
  and bisims1_pc_length_compEs2: "P,Es,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> pc \<le> length (compEs2 Es)"
apply(induct "(stk, loc, pc, xcp)" and "(stk, loc, pc, xcp)" 
  arbitrary: stk loc pc xcp and stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(auto)
done

lemma bisim1_pc_length_compE2D:
  "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk,loc,length (compE2 e),xcp)
  \<Longrightarrow> xcp = None \<and> call1 e' = None \<and> (\<exists>v. stk = [v] \<and> (is_val e' \<longrightarrow> e' = Val v \<and> xs = loc))"

  and bisims1_pc_length_compEs2D:
  "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk,loc,length (compEs2 es),xcp)
  \<Longrightarrow> xcp = None \<and> calls1 es' = None \<and> (\<exists>vs. stk = rev vs \<and> length vs = length es \<and> (is_vals es' \<longrightarrow> es' = map Val vs \<and> xs = loc))"
proof(induct "(e', xs)" "(stk, loc, length (compE2 e), xcp)"
        and "(es', xs)" "(stk, loc, length (compEs2 es), xcp)" 
 arbitrary: e' xs stk loc xcp and es' xs stk loc xcp rule: bisim1_bisims1.inducts)
  case (bisims1List2 es es' xs stk loc pc xcp e v)
  then obtain vs where "xcp = None" "calls1 es' = None" 
    "stk = rev vs" "length vs = length es" "is_vals es' \<longrightarrow> es' = map Val vs \<and> xs = loc" by auto
  thus ?case
    by(clarsimp)(rule_tac x="v#vs" in exI, auto)
qed(simp_all (no_asm_use), (fastforce dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2 split: bop.split_asm if_split_asm)+)

corollary bisim1_call_pcD: "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_calls_pcD: "\<lbrakk> P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp); calls1 es' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> pc < length (compEs2 es)"
proof -
  assume bisim: "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)"
    and call: "call1 e' = \<lfloor>aMvs\<rfloor>"

  { assume "pc = length (compE2 e)"
    with bisim call have False
      by(auto dest: bisim1_pc_length_compE2D) }
  moreover from bisim have "pc \<le> length (compE2 e)"
    by(rule bisim1_pc_length_compE2)
  ultimately show "pc < length (compE2 e)"
    by(cases "pc < length (compE2 e)")(auto)
next
  assume bisim: "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"
    and call: "calls1 es' = \<lfloor>aMvs\<rfloor>"
  { assume "pc = length (compEs2 es)"
    with bisim call have False
      by(auto dest: bisims1_pc_length_compEs2D) }
  moreover from bisim have "pc \<le> length (compEs2 es)"
    by(rule bisims1_pc_length_compEs2)
  ultimately show "pc < length (compEs2 es)"
    by(cases "pc < length (compEs2 es)")(auto)
qed

lemma bisim1_length_xs: "P,e,h \<turnstile> (e',xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> length xs = length loc"
  and bisims1_length_xs: "P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> length xs = length loc"
by(induct "(e',xs)" "(stk, loc, pc, xcp)" and "(es',xs)" "(stk, loc, pc, xcp)"
  arbitrary: e' xs stk loc pc xcp and es' xs stk loc pc xcp rule: bisim1_bisims1.inducts)
  auto

lemma bisim1_Val_length_compE2D:
  "P,e,h \<turnstile> (Val v,xs) \<leftrightarrow> (stk, loc, length (compE2 e), xcp) \<Longrightarrow> stk = [v] \<and> xs = loc \<and> xcp = None"

  and bisims1_Val_length_compEs2D:
  "P,es,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (stk, loc, length (compEs2 es), xcp) \<Longrightarrow> stk = rev vs \<and> xs = loc \<and> xcp = None"
by(auto dest: bisim1_pc_length_compE2D bisims1_pc_length_compEs2D)

lemma bisim_Val_loc_eq_xcp_None:
  "P, e, h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> xs = loc \<and> xcp = None"

  and bisims_Val_loc_eq_xcp_None:
  "P, es, h \<turnstile> (map Val vs, xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> xs = loc \<and> xcp = None"
apply(induct "(Val v :: 'addr expr1, xs)" "(stk, loc, pc, xcp)" 
  and "(map Val vs :: 'addr expr1 list, xs)" "(stk, loc, pc, xcp)"
  arbitrary: v xs stk loc pc xcp and vs xs stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(auto)
done

lemma bisim_Val_pc_not_Invoke: 
  "\<lbrakk> P,e,h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp); pc < length (compE2 e) \<rbrakk> \<Longrightarrow> compE2 e ! pc \<noteq> Invoke M n'"

  and bisims_Val_pc_not_Invoke: 
  "\<lbrakk> P,es,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (stk,loc,pc,xcp); pc < length (compEs2 es) \<rbrakk> \<Longrightarrow> compEs2 es ! pc \<noteq> Invoke M n'"
apply(induct "(Val v :: 'addr expr1, xs)" "(stk, loc, pc, xcp)"
         and "(map Val vs :: 'addr expr1 list, xs)" "(stk, loc, pc, xcp)"
  arbitrary: v xs stk loc pc xcp and vs xs stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(auto simp add: nth_append compEs2_map_Val dest: bisim1_pc_length_compE2)
done

lemma bisim1_VarD: "P, E, h \<turnstile> (Var V,xs) \<leftrightarrow> (stk,loc,pc,xcp) \<Longrightarrow> xs = loc"
  and "P, es, h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> True"
by(induct "(Var V :: 'addr expr1, xs)" "(stk, loc, pc, xcp)" and arbitrary: V xs stk loc pc xcp and rule: bisim1_bisims1.inducts) auto

lemma bisim1_ThrowD:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)
  \<Longrightarrow> pc < length (compE2 e) \<and> (xcp = \<lfloor>a\<rfloor> \<or> xcp = None) \<and> xs = loc"

  and bisims1_ThrowD:
  "P, es, h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)
  \<Longrightarrow> pc < length (compEs2 es) \<and> (xcp = \<lfloor>a\<rfloor> \<or> xcp = None) \<and> xs = loc"
apply(induct "(Throw a :: 'addr expr1, xs)" "(stk, loc, pc, xcp)"
         and "(map Val vs @ Throw a # es', xs)" "(stk, loc, pc, xcp)"
         arbitrary: xs stk loc pc xcp and vs es' xs stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(fastforce dest: bisim1_pc_length_compE2 bisim_Val_loc_eq_xcp_None simp add: Cons_eq_append_conv)+
done

lemma fixes P :: "'addr J1_prog"
  shows bisim1_Invoke_stkD:
  "\<lbrakk> P,e,h \<turnstile> exs \<leftrightarrow> (stk,loc,pc,None); pc < length (compE2 e); compE2 e ! pc = Invoke M n' \<rbrakk> 
  \<Longrightarrow> \<exists>vs v stk'. stk = vs @ v # stk' \<and> length vs = n'"

  and bisims1_Invoke_stkD: 
  "\<lbrakk> P,es,h \<turnstile> esxs [\<leftrightarrow>] (stk,loc,pc,None); pc < length (compEs2 es); compEs2 es ! pc = Invoke M n' \<rbrakk>
  \<Longrightarrow> \<exists>vs v stk'. stk = vs @ v # stk' \<and> length vs = n'"
proof(induct "(stk, loc, pc, None :: 'addr option)" and "(stk, loc, pc, None :: 'addr option)"
    arbitrary: stk loc pc and stk loc pc rule: bisim1_bisims1.inducts)
  case bisim1Call1
  thus ?case
    apply(clarsimp simp add: nth_append append_eq_append_conv2 neq_Nil_conv split: if_split_asm)
    apply(drule bisim1_pc_length_compE2, clarsimp simp add: neq_Nil_conv nth_append)
    apply(frule bisim1_pc_length_compE2, clarsimp)
    apply(drule bisim1_pc_length_compE2D, fastforce)
    done
next
  case bisim1CallParams thus ?case
    apply(clarsimp simp add: nth_append append_eq_Cons_conv split: if_split_asm)
    apply(fastforce simp add: append_eq_append_conv2 Cons_eq_append_conv)
    apply(frule bisims1_pc_length_compEs2, clarsimp)
    apply(drule bisims1_pc_length_compEs2D, fastforce simp add: append_eq_append_conv2)
    done
qed(fastforce simp add: nth_append append_eq_append_conv2 neq_Nil_conv split: if_split_asm bop.split_asm dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2)+

lemma fixes P :: "'addr J1_prog"
  shows bisim1_call_xcpNone: "P,e,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a\<rfloor>) \<Longrightarrow> call1 e' = None"
  and bisims1_calls_xcpNone: "P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,\<lfloor>a\<rfloor>) \<Longrightarrow> calls1 es' = None"
apply(induct "(e', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)" and "(es',xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
  arbitrary: e' xs stk loc pc and es' xs stk loc pc rule: bisim1_bisims1.inducts)
apply(auto dest: bisim_Val_loc_eq_xcp_None bisims_Val_loc_eq_xcp_None simp add: is_vals_conv)
done

lemma bisims1_map_Val_append:
  assumes bisim: "P, es', h \<turnstile> (es'', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)"
  shows "length es = length vs
          \<Longrightarrow> P, es @ es', h \<turnstile> (map Val vs @ es'', xs) [\<leftrightarrow>] (stk @ rev vs, loc, length (compEs2 es) + pc, xcp)"
proof(induction vs arbitrary: es)
  case Nil thus ?case using bisim by simp
next
  case (Cons v vs)
  from \<open>length es = length (v # vs)\<close> obtain e es''' where [simp]: "es = e # es'''" by(cases es, auto)
  with \<open>length es = length (v # vs)\<close> have len: "length es''' = length vs" by simp
  from Cons.IH[OF len]
  show ?case by(simp add: add.assoc append_assoc[symmetric] del: append_assoc)(rule bisims1List2, auto)
qed

lemma bisim1_hext_mono: "\<lbrakk> P,e,h \<turnstile> exs \<leftrightarrow> s; hext h h' \<rbrakk> \<Longrightarrow> P,e,h' \<turnstile> exs \<leftrightarrow> s" (is "PROP ?thesis1")
  and bisims1_hext_mono: "\<lbrakk> P,es,h \<turnstile> esxs [\<leftrightarrow>] s; hext h h' \<rbrakk> \<Longrightarrow> P,es,h' \<turnstile> esxs [\<leftrightarrow>] s" (is "PROP ?thesis2")
proof -
  assume hext: "hext h h'"
  have "P,e,h \<turnstile> exs \<leftrightarrow> s \<Longrightarrow> P,e,h' \<turnstile> exs \<leftrightarrow> s"
    and "P,es,h \<turnstile> esxs [\<leftrightarrow>] s \<Longrightarrow> P,es,h' \<turnstile> esxs [\<leftrightarrow>] s"
    apply(induct rule: bisim1_bisims1.inducts)
    apply(insert hext)
    apply(auto intro: bisim1_bisims1.intros dest: hext_objD)
    done
  thus "PROP ?thesis1" and "PROP ?thesis2" by auto
qed

declare match_ex_table_append_not_pcs [simp]
       match_ex_table_eq_NoneI[simp]
       outside_pcs_compxE2_not_matches_entry[simp]
       outside_pcs_compxEs2_not_matches_entry[simp]

lemma bisim1_xcp_Some_not_caught:
  "P, e, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None"

  and bisims1_xcp_Some_not_caught:
  "P, es, h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)
  \<Longrightarrow> match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxEs2 es pc' d) = None"
proof(induct "(Throw a :: 'addr expr1, xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)" 
    and "(map Val vs @ Throw a # es' :: 'addr expr1 list, xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
    arbitrary: xs stk loc pc pc' d and xs stk loc pc vs es' pc' d rule: bisim1_bisims1.inducts)
  case bisim1Sync10
  thus ?case by(simp add: matches_ex_entry_def)
next
  case bisim1Sync11
  thus ?case by(simp add: matches_ex_entry_def)
next
  case (bisim1SyncThrow e1 xs stk loc pc e2)
  note IH = \<open>match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e1 pc' d) = None\<close>
  from \<open>P,e1,h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a\<rfloor>)\<close> have "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  with IH show ?case
    by(auto simp add: match_ex_table_append matches_ex_entry_def dest: match_ex_table_pc_length_compE2 intro: match_ex_table_not_pcs_None)
next
  case bisims1List1 thus ?case
    by(auto simp add: Cons_eq_append_conv dest: bisim1_ThrowD bisim_Val_loc_eq_xcp_None)
next
  case (bisims1List2 es es'' xs stk loc pc e v)
  hence "\<And>pc' d. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxEs2 es pc' d) = None"
    by(auto simp add: Cons_eq_append_conv)
  from this[of "pc' + length (compE2 e)" "Suc d"] show ?case by(auto simp add: add.assoc)
next
  case (bisim1BlockThrowSome e xs stk loc pc T v)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  from this[of "2+pc'"] show ?case by(auto)
next
  case (bisim1Seq2 e2 stk loc pc e1 xs)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  from this[of "Suc (pc' + length (compE2 e1))"] show ?case by(simp add: add.assoc)
next
  case (bisim1CondThen e1 stk loc pc e e2 xs)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e1 pc' d) = None" by auto
  note this[of "Suc (pc' + length (compE2 e))"]
  moreover from \<open>P,e1,h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a\<rfloor>)\<close>
  have "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  ultimately show ?case by(simp add: add.assoc match_ex_table_eq_NoneI outside_pcs_compxE2_not_matches_entry)
next
  case (bisim1CondElse e2 stk loc pc e e1 xs)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  note this[of "Suc (Suc (pc' + (length (compE2 e) + length (compE2 e1))))"]
  thus ?case by(simp add: add.assoc)
next
  case (bisim1WhileThrow2 e xs stk loc pc c)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  from this[of "Suc (pc' + (length (compE2 c)))"]
  show ?case by(simp add: add.assoc)
next
  case (bisim1Throw1 e xs stk loc pc)
  thus ?case by(auto dest: bisim_Val_loc_eq_xcp_None)
next
  case (bisim1TryFail e xs stk loc pc C' C e2)
  hence "match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e pc' d) = None" by auto
  moreover from \<open>P,e,h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,\<lfloor>a\<rfloor>)\<close> have "pc < length (compE2 e)"
    by(auto dest: bisim1_ThrowD)
  ultimately show ?case using \<open>typeof_addr h a = \<lfloor>Class_type C'\<rfloor>\<close> \<open>\<not> P \<turnstile> C' \<preceq>\<^sup>* C\<close>
    by(simp add: matches_ex_entry_def cname_of_def)
next
  case (bisim1TryCatchThrow e2 xs stk loc pc e C)
  hence "\<And>pc'. match_ex_table (compP f P) (cname_of h a) (pc' + pc) (compxE2 e2 pc' d) = None" by auto
  from this[of "Suc (Suc (pc' + (length (compE2 e))))"]
  show ?case by(simp add: add.assoc matches_ex_entry_def)
next
  case bisim1Sync12 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append eval_nat_numeral, simp add: matches_ex_entry_def)
next
  case bisim1Sync14 thus ?case
    by(auto dest: bisim1_ThrowD simp add: match_ex_table_append eval_nat_numeral, simp add: matches_ex_entry_def)
qed(fastforce dest: bisim1_ThrowD simp add: add.assoc[symmetric])+

declare match_ex_table_append_not_pcs [simp del]
       match_ex_table_eq_NoneI[simp del]
       outside_pcs_compxE2_not_matches_entry[simp del]
       outside_pcs_compxEs2_not_matches_entry[simp del]

lemma bisim1_xcp_pcD: "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_xcp_pcD: "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compEs2 es)"
by(induct "(e', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)" and "(es', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
  arbitrary: e' xs stk loc pc and es' xs stk loc pc rule: bisim1_bisims1.inducts)
  auto

declare nth_Cons_subtract[simp]
declare nth_append [simp]

lemma bisim1_Val_\<tau>Exec_move:
  "\<lbrakk> P, E, h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, xcp); pc < length (compE2 E) \<rbrakk> 
  \<Longrightarrow> xs = loc \<and> xcp = None \<and>
     \<tau>Exec_mover_a P t E h (stk, xs, pc, None) ([v], xs, length (compE2 E), None)"

 and bisims1_Val_\<tau>Exec_moves:
  "\<lbrakk> P, Es, h \<turnstile> (map Val vs, xs) [\<leftrightarrow>] (stk, loc, pc, xcp); pc < length (compEs2 Es) \<rbrakk> 
  \<Longrightarrow> xs = loc \<and> xcp = None \<and>
    \<tau>Exec_movesr_a P t Es h (stk, xs, pc, None) (rev vs, xs, length (compEs2 Es), None)"
proof(induct "(Val v :: 'addr expr1, xs)" "(stk, loc, pc, xcp)" 
    and "(map Val vs :: 'addr expr1 list, xs)" "(stk, loc, pc, xcp)"
    arbitrary: v xs stk loc pc xcp and vs xs stk loc pc xcp rule: bisim1_bisims1.inducts)
  case bisim1Val thus ?case by(auto intro!: \<tau>Execr1step exec_instr \<tau>move2Val simp add: exec_move_def)
next
  case (bisim1LAss2 V e xs)
  have "\<tau>Exec_mover_a P t (V:=e) h ([], xs, Suc (length (compE2 e)), None) ([Unit], xs, Suc (Suc (length (compE2 e))), None)"
    by(auto intro!: \<tau>Execr1step exec_instr \<tau>move2LAssRed2 simp add: nth_append exec_move_def)
  with bisim1LAss2 show ?case by simp
next
  case (bisim1AAss4 a i e xs)
  have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([], xs, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None) ([Unit], xs, Suc (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))), None)"
    by(auto intro!: \<tau>Execr1step exec_instr \<tau>move2AAssRed simp add: nth_append exec_move_def)
  with bisim1AAss4 show ?case by(simp add: ac_simps)
next
  case (bisim1FAss3 e F D e2 xs)
  have "\<tau>Exec_mover_a P t (e\<bullet>F{D} := e2) h ([], xs, Suc (length (compE2 e) + length (compE2 e2)), None) ([Unit], xs, Suc (Suc (length (compE2 e) + length (compE2 e2))), None)"
    by(auto intro!: \<tau>Execr1step exec_instr \<tau>move2FAssRed simp add: nth_append exec_move_def)
  with bisim1FAss3 show ?case by simp
next
  case (bisim1Sync6 V e1 e2 v xs)
  have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)
                                        ([v], xs, 9 + length (compE2 e1) + length (compE2 e2), None)"
    by(rule \<tau>Execr1step)(auto intro: exec_instr \<tau>move2Sync6 simp add: exec_move_def)
  with bisim1Sync6 show ?case by(auto simp add: eval_nat_numeral)
next
  case (bisim1Seq2 e2 stk loc pc xcp e1 v xs)
  from \<open>Suc (length (compE2 e1) + pc) < length (compE2 (e1;; e2))\<close> have pc: "pc < length (compE2 e2)" by simp
  with \<open>pc < length (compE2 e2) \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_mover_a P t e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)\<close>
  have "xs = loc" "xcp = None"
    "\<tau>Exec_mover_a P t e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)" by auto
  moreover 
  hence "\<tau>Exec_mover_a P t (e1;;e2) h (stk, xs, Suc (length (compE2 e1) + pc), None) ([v], xs, Suc (length (compE2 e1) + length (compE2 e2)), None)"
    by -(rule Seq_\<tau>ExecrI2)
  ultimately show ?case by(simp)
next
  case (bisim1CondThen e1 stk loc pc xcp e e2 v xs)
  from \<open>P, e1, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close>
  have "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)

  have e: "\<tau>Exec_mover_a P t (if (e) e1 else e2) h
                     ([v], xs, Suc (length (compE2 e) + (length (compE2 e1))), None)
                     ([v], xs, length (compE2 (if (e) e1 else e2)), None)" 
    by(rule \<tau>Execr1step)(auto simp add: nth_append exec_move_def intro!: exec_instr \<tau>move2CondThenExit)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with \<open>pc < length (compE2 e1)
         \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_mover_a P t e1 h (stk, xs, pc, None) ([v], xs, length (compE2 e1), None)\<close>
    have s: "xs = loc" "xcp = None"
      and "\<tau>Exec_mover_a P t e1 h (stk, xs, pc, None) ([v], xs, length (compE2 e1), None)" by auto
    hence "\<tau>Exec_mover_a P t (if (e) e1 else e2) h
                     (stk, xs, Suc (length (compE2 e) + pc), None)
                     ([v], xs, Suc (length (compE2 e) + length (compE2 e1)), None)"
      by -(rule Cond_\<tau>ExecrI2)
    with e True s show ?thesis by(simp)
  next
    case False
    with \<open>pc \<le> length (compE2 e1)\<close> have pc: "pc = length (compE2 e1)" by auto
    with \<open>P, e1, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close>
    have "stk = [v]" "xs = loc" "xcp = None" by(auto dest: bisim1_Val_length_compE2D)
    with pc e show ?thesis by(simp)
  qed
next
  case (bisim1CondElse e2 stk loc pc xcp e e1 v xs)
  from \<open>P, e2, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close>
  have "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)

  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    with \<open>pc < length (compE2 e2)
         \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_mover_a P t e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)\<close>
    have s: "xs = loc" "xcp = None"
      and e: "\<tau>Exec_mover_a P t e2 h (stk, xs, pc, None) ([v], xs, length (compE2 e2), None)" by auto
    from e have "\<tau>Exec_mover_a P t (if (e) e1 else e2) h (stk, xs, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), None) ([v], xs, Suc (Suc (length (compE2 e) + length (compE2 e1) + length (compE2 e2))), None)"
      by(rule Cond_\<tau>ExecrI3)
    with True s show ?thesis by(simp add: add.assoc)
  next
    case False
    with \<open>pc \<le> length (compE2 e2)\<close> have pc: "pc = length (compE2 e2)" by auto
    with \<open>P, e2, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close>
    have "stk = [v]" "xs = loc" "xcp = None" by(auto dest: bisim1_Val_length_compE2D)
    with pc show ?thesis by(simp add: add.assoc)
  qed
next
  case (bisim1While7 c e xs)
  have "\<tau>Exec_mover_a P t (while (c) e) h
                   ([], xs, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)
                   ([Unit], xs, length (compE2 (while (c) e)), None)"
    by(auto intro!: \<tau>Execr1step exec_instr \<tau>move2While4 simp add: nth_append exec_move_def)
  thus ?case by(simp)
next
  case (bisims1List1 e e' xs stk loc pc xcp es)
  from \<open>e' # es = map Val vs\<close> obtain v vs' where [simp]: "vs = v # vs'" "e' = Val v" "es = map Val vs'" by auto
  from \<open>P,e,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close>
  have length: "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
  hence "xs = loc \<and> xcp = None \<and> \<tau>Exec_mover_a P t e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)"
  proof(cases "pc < length (compE2 e)")
    case True
    with \<open>\<lbrakk>e' = Val v; pc < length (compE2 e)\<rbrakk> \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_mover_a P t e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)\<close>
    show ?thesis by auto
  next
    case False
    with length have pc: "pc = length (compE2 e)" by auto
    with \<open>P,e,h \<turnstile> (e',xs) \<leftrightarrow> (stk,loc,pc,xcp)\<close> have "stk = [v]" "xs = loc" "xcp = None"
      by(auto dest: bisim1_Val_length_compE2D)
    with pc show ?thesis by(auto)
  qed
  hence s: "xs = loc" "xcp = None"
    and exec1: "\<tau>Exec_mover_a P t e h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)" by auto
  from exec1 have "\<tau>Exec_movesr_a P t (e # es) h (stk, xs, pc, None) ([v], xs, length (compE2 e), None)"
    by(auto intro: \<tau>Exec_mover_\<tau>Exec_movesr)
  moreover have "\<tau>Exec_movesr_a P t (map Val vs') h ([], xs, 0, None) (rev vs', xs, length (compEs2 (map Val vs')), None)"
    by(rule \<tau>Exec_movesr_map_Val)
  hence "\<tau>Exec_movesr_a P t ([e] @ map Val vs') h ([] @ [v], xs, length (compEs2 [e]) + 0, None) (rev vs' @ [v], xs, length (compEs2 [e]) + length (compEs2 (map Val vs')), None)"
    by -(rule append_\<tau>Exec_movesr, auto)
  ultimately show ?case using s by(auto)
next
  case (bisims1List2 es es' xs stk loc pc xcp e v)
  from \<open>Val v # es' = map Val vs\<close> obtain vs' where [simp]: "vs = v # vs'" "es' = map Val vs'" by auto
  from \<open>P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)\<close>
  have length: "pc \<le> length (compEs2 es)" by(auto dest: bisims1_pc_length_compEs2)
  hence "xs = loc \<and> xcp = None \<and> \<tau>Exec_movesr_a P t es h (stk, xs, pc, None) (rev vs', xs, length (compEs2 es), None)"
  proof(cases "pc < length (compEs2 es)")
    case True
    with \<open>\<lbrakk>es' = map Val vs'; pc < length (compEs2 es)\<rbrakk> \<Longrightarrow> xs = loc \<and> xcp = None \<and> \<tau>Exec_movesr_a P t es h (stk, xs, pc, None)
      (rev vs', xs, length (compEs2 es), None)\<close>
    show ?thesis by auto
  next
    case False
    with length have pc: "pc = length (compEs2 es)" by auto
    with \<open>P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)\<close> have "stk = rev vs'" "xs = loc" "xcp = None"
      by(auto dest: bisims1_Val_length_compEs2D)
    with pc show ?thesis by(auto)
  qed
  hence s: "xs = loc" "xcp = None"
    and exec1: "\<tau>Exec_movesr_a P t es h (stk, xs, pc, None) (rev vs', xs, length (compEs2 es), None)" by auto
  from exec1 have "\<tau>Exec_movesr_a P t ([e] @ es) h (stk @ [v], xs, length (compEs2 [e]) + pc, None) (rev vs' @ [v], xs, length (compEs2 [e]) + length (compEs2 es), None)"
    by -(rule append_\<tau>Exec_movesr, auto)
  thus ?case using s by(auto)
qed(auto)

lemma bisim1Val2D1:
  assumes bisim: "P, e, h \<turnstile> (Val v,xs) \<leftrightarrow> (stk,loc,pc,xcp)"
  shows "xcp = None \<and> xs = loc \<and> \<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([v], loc, length (compE2 e), None)"
proof -
  from bisim have "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
  moreover 
  have "\<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([v], loc, length (compE2 e), None)"
  proof(cases "pc < length (compE2 e)")
    case True
    from bisim1_Val_\<tau>Exec_move[OF bisim True] show ?thesis by auto
  next
    case False
    from bisim have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    with False have "pc = length (compE2 e)" by auto
    with bisim have "stk = [v]" "loc = xs" "xcp=None" by(auto dest: bisim1_Val_length_compE2D)
    with \<open>pc = length (compE2 e)\<close> show ?thesis by(auto)
  qed
  ultimately show ?thesis by simp
qed

lemma bisim1_Throw_\<tau>Exec_movet:
  "\<lbrakk> P, e, h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,None) \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_movet_a P t e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, e, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"

  and bisims1_Throw_\<tau>Exec_movest:
  "\<lbrakk> P, es, h \<turnstile>  (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (stk,loc,pc,None) \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_movest_a P t es h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, es, h \<turnstile> (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"
proof(induct e "n :: nat" "Throw a :: 'addr expr1" xs stk loc pc "None :: 'addr option"
    and es "n :: nat" "map Val vs @ Throw a # es' :: 'addr expr1 list" xs stk loc pc "None :: 'addr option"
    arbitrary: and vs rule: bisim1_bisims1_inducts_split)
  case (bisim1Sync9 e1 n e2 V xs)
  let ?pc = "8 + length (compE2 e1) + length (compE2 e2)"
  have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs, ?pc, None) ([Addr a], xs, ?pc, \<lfloor>a\<rfloor>)"
    by(rule \<tau>Exect1step)(auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: is_Ref_def exec_move_def)
  moreover
  have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],xs,?pc,\<lfloor>a\<rfloor>)" by(rule bisim1Sync10)
  ultimately show ?case by auto
next
  case (bisim1Seq2 e2 n xs stk loc pc e1)
  then obtain pc' where "\<tau>Exec_movet_a P t e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    "P, e2, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" "xs = loc" by auto
  thus ?case by(auto intro: Seq_\<tau>ExectI2 bisim1_bisims1.bisim1Seq2)
next
  case (bisim1CondThen e1 n xs stk loc pc e e2)
  then obtain pc' where exec: "\<tau>Exec_movet_a P t e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P, e1, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
  from exec have "\<tau>Exec_movet_a P t (if (e) e1 else e2) h (stk, loc, Suc (length (compE2 e) + pc), None) ([Addr a], loc, Suc (length (compE2 e) + pc'), \<lfloor>a\<rfloor>)"
    by(rule Cond_\<tau>ExectI2)
  moreover from bisim
  have "P, if (e) e1 else e2, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 e) + pc'), \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisim1CondThen)
  ultimately show ?case using s by(auto)
next
  case (bisim1CondElse e2 n xs stk loc pc e e1)
  then obtain pc' where exec: "\<tau>Exec_movet_a P t e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P, e2, h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
  let "?pc pc" = "Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))"
  from exec have "\<tau>Exec_movet_a P t (if (e) e1 else e2) h (stk, loc, (?pc pc), None) ([Addr a], loc, ?pc pc', \<lfloor>a\<rfloor>)"
    by(rule Cond_\<tau>ExectI3)
  moreover from bisim
  have "P, if (e) e1 else e2, h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, ?pc pc', \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisim1CondElse)
  ultimately show ?case using s by auto
next
  case (bisim1Throw1 e n xs stk loc pc)
  note bisim = \<open>P, e, h \<turnstile> (addr a, xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  hence s: "xs = loc" 
    and exec: "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([Addr a], loc, length (compE2 e), None)"
    by(auto dest: bisim1Val2D1)
  from exec have "\<tau>Exec_mover_a P t (throw e) h (stk, loc, pc, None) ([Addr a], loc, length (compE2 e), None)"
    by(rule Throw_\<tau>ExecrI)
  also have "\<tau>Exec_movet_a P t (throw e) h ([Addr a], loc, length (compE2 e), None) ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
    by(rule \<tau>Exect1step, auto intro: exec_instr \<tau>move2Throw2 simp add: is_Ref_def exec_move_def)
  also have "P, throw e, h \<turnstile> (Throw a, loc ) \<leftrightarrow> ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
    by(rule bisim1Throw2)
  ultimately show ?case using s by auto
next
  case (bisims1List1 e n e' xs stk loc pc es vs)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  show ?case
  proof(cases "is_val e'")
    case True
    with \<open>e' # es = map Val vs @ Throw a # es'\<close> obtain v vs' where "vs = v # vs'" "e' = Val v"
      and es: "es = map Val vs' @ Throw a # es'" by(auto simp add: Cons_eq_append_conv)
    with bisim have "P,e,h \<turnstile> (Val v, xs) \<leftrightarrow> (stk, loc, pc, None)" by simp
    from bisim1Val2D1[OF this] have [simp]: "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by auto
    from exec have "\<tau>Exec_movesr_a P t (e # es) h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by(rule \<tau>Exec_mover_\<tau>Exec_movesr)
    also from es \<open>es = map Val vs' @ Throw a # es'
         \<Longrightarrow> \<exists>pc'. \<tau>Exec_movest_a P t es h ([], loc, 0, None) (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>) \<and>
           P,es,h \<turnstile> (map Val vs' @ Throw a # es', loc) [\<leftrightarrow>] (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>) \<and> loc = loc\<close>
    obtain pc' where execes: "\<tau>Exec_movest_a P t es h ([], loc, 0, None) (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>)"
      and bisim': "P,es,h \<turnstile> (map Val vs' @ Throw a # es', loc) [\<leftrightarrow>] (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>)" by auto
    from append_\<tau>Exec_movest[OF _ execes, of "[v]" "[e]"]
    have "\<tau>Exec_movest_a P t (e # es) h ([v], loc, length (compE2 e), None) (Addr a # rev vs' @ [v], loc, length (compE2 e) + pc', \<lfloor>a\<rfloor>)" by simp
    also from bisims1List2[OF bisim', of e v] es \<open>e' = Val v\<close> \<open>vs = v # vs'\<close>
    have "P,e # es,h \<turnstile> (e' # es, xs) [\<leftrightarrow>] ((Addr a # rev vs), loc, length (compE2 e) + pc', \<lfloor>a\<rfloor>)" by simp
    ultimately show ?thesis using \<open>vs = v # vs'\<close> es \<open>e' = Val v\<close> by auto
  next
    case False
    with \<open>e' # es = map Val vs @ Throw a # es'\<close> have [simp]: "e' = Throw a" "es = es'" "vs = []"
      by(auto simp add: Cons_eq_append_conv)
    from \<open>e' = Throw a \<Longrightarrow> \<exists>pc'. \<tau>Exec_movet_a P t e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> P,e,h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc\<close>
    obtain pc' where "\<tau>Exec_movet_a P t e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
      and bisim: "P,e,h \<turnstile> (Throw a, xs ) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc" by auto
    hence "\<tau>Exec_movest_a P t (e # es) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
      by-(rule \<tau>Exec_movet_\<tau>Exec_movest)
    moreover from bisim
    have "P,e#es,h \<turnstile> (Throw a#es,xs) [\<leftrightarrow>] ([Addr a],loc,pc',\<lfloor>a\<rfloor>)" by(rule bisim1_bisims1.bisims1List1)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisims1List2 es n es'' xs stk loc pc e v)
  note IH = \<open>\<And>vs. es'' = map Val vs @ Throw a # es'
    \<Longrightarrow> \<exists>pc'. \<tau>Exec_movest_a P t es h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and>
           P,es,h \<turnstile> (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs,loc,pc',\<lfloor>a\<rfloor>) \<and> xs = loc\<close>
  from \<open>Val v # es'' = map Val vs @ Throw a # es'\<close>
  obtain vs' where [simp]: "vs = v # vs'" "es'' = map Val vs' @ Throw a # es'" by(auto simp add: Cons_eq_append_conv)
  from IH[OF \<open>es'' = map Val vs' @ Throw a # es'\<close>]
  obtain pc' where exec: "\<tau>Exec_movest_a P t es h (stk, loc, pc, None) (Addr a # rev vs', loc, pc', \<lfloor>a\<rfloor>)"
    and bisim: "P,es,h \<turnstile> (map Val vs' @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs',loc,pc',\<lfloor>a\<rfloor>)"
    and [simp]: "xs = loc" by auto
  from append_\<tau>Exec_movest[OF _ exec, of "[v]" "[e]"]
  have "\<tau>Exec_movest_a P t (e # es) h (stk @ [v], loc, length (compE2 e) + pc, None) (Addr a # rev vs, loc, length (compE2 e) + pc', \<lfloor>a\<rfloor>)" by simp
  moreover from bisim 
  have "P,e#es,h \<turnstile> (Val v # map Val vs' @ Throw a # es',xs) [\<leftrightarrow>] ((Addr a # rev vs')@[v],loc,length (compE2 e) + pc',\<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisims1List2)
  ultimately show ?case by(auto)
qed(auto)

lemma bisim1_Throw_\<tau>Exec_mover:
  "\<lbrakk> P, e, h \<turnstile> (Throw a,xs) \<leftrightarrow> (stk,loc,pc,None) \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, e, h \<turnstile> (Throw a,xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"
by(drule bisim1_Throw_\<tau>Exec_movet)(blast intro: tranclp_into_rtranclp)

lemma bisims1_Throw_\<tau>Exec_movesr:
  "\<lbrakk> P, es, h \<turnstile>  (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (stk,loc,pc,None) \<rbrakk>
  \<Longrightarrow> \<exists>pc'. \<tau>Exec_movesr_a P t es h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and>
      P, es, h \<turnstile> (map Val vs @ Throw a # es',xs) [\<leftrightarrow>] (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>) \<and> xs = loc"
by(drule bisims1_Throw_\<tau>Exec_movest)(blast intro: tranclp_into_rtranclp)

declare split_beta [simp]

lemma bisim1_inline_call_Throw:
  "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None); call1 e' = \<lfloor>(a, M, vs)\<rfloor>;
     compE2 e ! pc = Invoke M n0; pc < length (compE2 e) \<rbrakk>
  \<Longrightarrow> n0 = length vs \<and> P,e,h \<turnstile> (inline_call (Throw A) e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>A\<rfloor>)"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_inline_calls_Throw:
  "\<lbrakk> P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, None); calls1 es' = \<lfloor>(a, M, vs)\<rfloor>;
     compEs2 es ! pc = Invoke M n0; pc < length (compEs2 es) \<rbrakk>
  \<Longrightarrow> n0 = length vs \<and> P,es,h \<turnstile> (inline_calls (Throw A) es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>A\<rfloor>)"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct e "n :: nat" e' xs stk loc pc "None :: 'addr option"
        and es "n :: nat" es' xs stk loc pc "None :: 'addr option"
      rule: bisim1_bisims1_inducts_split)
  case (bisim1BinOp1 e1 n e' xs stk loc pc e2 bop)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M n0; pc < length (compE2 e1) \<rbrakk>
              \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! pc = Invoke M n0\<close>
  note call = \<open>call1 (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1BinOp1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1BinOp2 thus ?case
    by(auto split: if_split_asm bop.split_asm dest: bisim1_bisims1.bisim1BinOp2)
next
  case (bisim1AAcc1 A n a' xs stk loc pc i)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M n0; pc < length (compE2 A) \<rbrakk>
              \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil>) ! pc = Invoke M n0\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAcc1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1AAcc2 thus ?case
    by(auto split: if_split_asm dest: bisim1_bisims1.bisim1AAcc2)
next
  case (bisim1AAss1 A n a' xs stk loc pc i e)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M n0; pc < length (compE2 A) \<rbrakk>
              \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil> := e) ! pc = Invoke M n0\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAss1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    from call ins show ?thesis by simp
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc A e v)
  note IH1 = \<open>\<lbrakk>call1 i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M n0; pc < length (compE2 i) \<rbrakk>
              \<Longrightarrow> ?concl i n i' xs pc stk loc\<close>
  note bisim1 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil> := e) ! (length (compE2 A) + pc) = Invoke M n0\<close>
  note call = \<open>call1 (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val i'")
    case False
    with bisim1 call have "pc < length (compE2 i)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1AAss2)
  next
    case True
    then obtain v where [simp]: "i' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 i)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 i)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 i)" by(cases "pc < length (compE2 i)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1AAss3 thus ?case
    by(auto split: if_split_asm nat.split_asm simp add: nth_Cons dest: bisim1_bisims1.bisim1AAss3)
next
  case (bisim1FAss1 e n e' xs stk loc pc e2 F D)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M n0; pc < length (compE2 e) \<rbrakk>
              \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 (e\<bullet>F{D} := e2) ! pc = Invoke M n0\<close>
  note call = \<open>call1 (e'\<bullet>F{D} := e2) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1FAss1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    from call ins show ?thesis by simp
  qed
next
  case bisim1FAss2 thus ?case
    by(auto split: if_split_asm nat.split_asm simp add: nth_Cons dest: bisim1_bisims1.bisim1FAss2)
next
  case (bisim1CAS1 E n e' xs stk loc pc e2 e3 D F)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 E ! pc = Invoke M n0; pc < length (compE2 E) \<rbrakk>
              \<Longrightarrow> ?concl E n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,E,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 _ ! pc = Invoke M n0\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 E)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1CAS1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 E)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 E)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 E)" by(cases "pc < length (compE2 E)") auto
    from call ins show ?thesis by simp
  qed
next
  case (bisim1CAS2 e2 n e2' xs stk loc pc e1 e3 D F v)
  note IH1 = \<open>\<lbrakk>call1 e2' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M n0; pc < length (compE2 e2) \<rbrakk>
              \<Longrightarrow> ?concl e2 n e2' xs pc stk loc\<close>
  note bisim1 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note ins = \<open>compE2 _ ! (length (compE2 e1) + pc) = Invoke M n0\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(cases "is_val e2'")
    case False
    with bisim1 call have "pc < length (compE2 e2)"
      by(auto intro: bisim1_call_pcD)
    with call ins IH1 False show ?thesis
      by(auto simp add: nth_append intro: bisim1_bisims1.bisim1CAS2)
  next
    case True
    then obtain v where [simp]: "e2' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e2)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e2)"
      with bisim1 ins have False
        by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e2)" by(cases "pc < length (compE2 e2)") auto
    from call ins show ?thesis by simp
  qed
next
  case (bisim1Call1 obj n obj' xs stk loc pc ps M')
  note IH1 = \<open>\<lbrakk>call1 obj' = \<lfloor>(a, M, vs)\<rfloor>; compE2 obj ! pc = Invoke M n0;
              pc < length (compE2 obj) \<rbrakk>
              \<Longrightarrow> ?concl obj n obj' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>calls1 ps = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! 0 = Invoke M n0; 0 < length (compEs2 ps) \<rbrakk>
             \<Longrightarrow> ?concls ps n ps xs 0 [] xs\<close>
  note ins = \<open>compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M n0\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (obj'\<bullet>M'(ps)) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  thus ?case
  proof(cases rule: call1_callE)
    case CallObj
    with bisim1 call have "pc < length (compE2 obj)" by(auto intro: bisim1_call_pcD)
    with call ins CallObj IH1 show ?thesis
      by(auto intro: bisim1_bisims1.bisim1Call1)
  next
    case (CallParams v)
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins CallParams have False by(auto dest: bisim_Val_pc_not_Invoke) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with bisim1 CallParams have [simp]: "stk = [v]" "loc = xs" by(auto dest: bisim1_Val_length_compE2D)
    from IH2[of loc] CallParams ins
    show ?thesis
      apply(clarsimp simp add: compEs2_map_Val is_vals_conv split: if_split_asm)
      apply(drule bisim1_bisims1.bisim1CallParams)
      apply(auto simp add: neq_Nil_conv)
      done
  next
    case [simp]: Call
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with ins have [simp]: "vs = []" by(auto simp add: nth_append compEs2_map_Val split: if_split_asm)
    from bisim1 have [simp]: "stk = [Addr a]" "xs = loc" by(auto dest: bisim1_Val_length_compE2D)
    from ins show ?thesis by(auto intro: bisim1CallThrow[of "[]" "[]", simplified])
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc obj M' v)
  note IH2 = \<open>\<lbrakk>calls1 ps' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! pc = Invoke M n0; pc < length (compEs2 ps) \<rbrakk>
             \<Longrightarrow> ?concls ps n ps' xs pc stk loc\<close>
  note ins = \<open>compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M n0\<close>
  note bisim2 = \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v\<bullet>M'(ps')) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  thus ?case
  proof(cases rule: call1_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v')
    hence [simp]: "v' = v" and call': "calls1 ps' = \<lfloor>(a, M, vs)\<rfloor>" by auto
    from bisim2 call' have "pc < length (compEs2 ps)" by(auto intro: bisims1_calls_pcD)
    with IH2 CallParams ins show ?thesis
      by(auto simp add: is_vals_conv split: if_split_asm intro: bisim1_bisims1.bisim1CallParams)
  next
    case Call
    hence [simp]: "v = Addr a" "M' = M" "ps' = map Val vs" by auto
    from bisim2 have "pc \<le> length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
    moreover {
      assume pc: "pc < length (compEs2 ps)"
      with bisim2 ins have False by(auto dest: bisims_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compEs2 ps)" by(cases "pc < length (compEs2 ps)") auto
    from bisim2 have [simp]: "stk = rev vs" "xs = loc" by(auto dest: bisims1_Val_length_compEs2D)
    from bisim2 have "length ps = length vs" by(auto dest: bisims1_lengthD)
    with ins show ?thesis by(auto intro: bisim1CallThrow)
  qed
next
  case (bisims1List1 e n e' xs stk loc pc es)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M n0; pc < length (compE2 e) \<rbrakk>
              \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>calls1 es = \<lfloor>(a, M, vs)\<rfloor>; compEs2 es ! 0 = Invoke M n0; 0 < length (compEs2 es) \<rbrakk>
             \<Longrightarrow> ?concls es n es xs 0 [] xs\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>calls1 (e' # es) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compEs2 (e # es) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis
      by(auto simp add: nth_append split_beta intro: bisim1_bisims1.bisims1List1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    with bisim1 have [simp]: "stk = [v]" "loc = xs" by(auto dest: bisim1_Val_length_compE2D)
    from call have "es \<noteq> []" by(cases es) simp_all
    with IH2[of loc] call ins
    show ?thesis by(auto split: if_split_asm dest: bisims1List2)
  qed
qed(auto split: if_split_asm bop.split_asm intro: bisim1_bisims1.intros dest: bisim1_pc_length_compE2)

lemma bisim1_max_stack: "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> length stk \<le> max_stack e"
  and bisims1_max_stacks: "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp) \<Longrightarrow> length stk \<le> max_stacks es"
apply(induct "(e', xs)" "(stk, loc, pc, xcp)" and "(es', xs)" "(stk, loc, pc, xcp)"
  arbitrary: e' xs stk loc pc xcp and es' xs stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(auto simp add: max_stack1[simplified] max_def max_stacks_ge_length)
apply(drule sym, simp add: max_stacks_ge_length, drule sym, simp, rule le_trans[OF max_stacks_ge_length], simp)
done

inductive bisim1_fr :: "'addr J1_prog \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 \<times> 'addr locals1 \<Rightarrow> 'addr frame \<Rightarrow> bool"
for P :: "'addr J1_prog" and h :: 'heap
where
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D;
     P,blocks1 0 (Class D#Ts) body, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None);
     call1 e = \<lfloor>(a, M', vs)\<rfloor>;
     max_vars e \<le> length xs \<rbrakk>
  \<Longrightarrow> bisim1_fr P h (e, xs) (stk, loc, C, M, pc)"

declare bisim1_fr.intros [intro]
declare bisim1_fr.cases [elim]

lemma bisim1_fr_hext_mono:
  "\<lbrakk> bisim1_fr P h exs fr; hext h h' \<rbrakk> \<Longrightarrow>  bisim1_fr P h' exs fr"
by(auto intro: bisim1_hext_mono)

lemma bisim1_max_vars: "P,E,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp) \<Longrightarrow> max_vars E \<ge> max_vars e"
  and bisims1_max_varss: "P,Es,h \<turnstile> (es,xs) [\<leftrightarrow>] (stk,loc,pc,xcp) \<Longrightarrow> max_varss Es \<ge> max_varss es"
apply(induct E "(e, xs)" "(stk, loc, pc, xcp)" and Es "(es, xs)" "(stk, loc, pc, xcp)"
  arbitrary: e xs stk loc pc xcp and es xs stk loc pc xcp rule: bisim1_bisims1.inducts)
apply(auto)
done

lemma bisim1_call_\<tau>Exec_move:
  "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None); call1 e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<not> contains_insync e \<rbrakk>
  \<Longrightarrow> \<exists>pc' loc' stk'. \<tau>Exec_mover_a P t e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None) \<and>
                     pc' < length (compE2 e) \<and> compE2 e ! pc' = Invoke M' (length vs) \<and>
                     P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_calls_\<tau>Exec_moves:
  "\<lbrakk> P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk, loc, pc, None); calls1 es' = \<lfloor>(a, M', vs)\<rfloor>;
     n + max_varss es' \<le> length xs; \<not> contains_insyncs es \<rbrakk>
  \<Longrightarrow> \<exists>pc' stk' loc'. \<tau>Exec_movesr_a P t es h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None) \<and>
                     pc' < length (compEs2 es) \<and> compEs2 es ! pc' = Invoke M' (length vs) \<and>
                     P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (rev vs @ Addr a # stk', loc', pc', None)"
  (is "\<lbrakk>_; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct e "n :: nat" e' xs stk loc pc xcp\<equiv>"None :: 'addr option"
    and es "n :: nat" es' xs stk loc pc xcp\<equiv>"None :: 'addr option"
    rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by auto
next
  case bisim1New thus ?case by auto
next
  case bisim1NewArray thus ?case
    by auto (fastforce intro: bisim1_bisims1.bisim1NewArray elim!: NewArray_\<tau>ExecrI intro!: exI)
next
  case bisim1Cast thus ?case
    by(auto)(fastforce intro: bisim1_bisims1.bisim1Cast elim!: Cast_\<tau>ExecrI intro!: exI)+
next
  case bisim1InstanceOf thus ?case
    by(auto)(fastforce intro: bisim1_bisims1.bisim1InstanceOf elim!: InstanceOf_\<tau>ExecrI intro!: exI)+
next
  case bisim1Val thus ?case by auto
next
  case bisim1Var thus ?case by auto
next
  case (bisim1BinOp1 e1 n e' xs stk loc pc e2 bop)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<not> contains_insync e1 \<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 e2 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2 \<le> length xs; \<not> contains_insync e2 \<rbrakk> \<Longrightarrow> ?concl e2 n e2 xs 0 [] xs\<close>
  note call = \<open>call1 (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (e' \<guillemotleft>bop\<guillemotright> e2) \<le> length xs\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note cs = \<open>\<not> contains_insync (e1 \<guillemotleft>bop\<guillemotright> e2)\<close>
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      by-(rule BinOp_\<tau>ExecrI1)
    also from call IH2[of loc] len cs  obtain pc' stk' loc'
      where exec: "\<tau>Exec_mover_a P t e2 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e2 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e2)"
      and bisim': "P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from BinOp_\<tau>ExecrI2[OF exec, of e1 bop v]
    have "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h ([v], loc, length (compE2 e1), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e1) + pc', None)" by simp
    also (rtranclp_trans) from bisim'
    have "P,e1\<guillemotleft>bop\<guillemotright>e2,h \<turnstile> (Val v \<guillemotleft>bop\<guillemotright> e2, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e1) + pc', None)"
      by(rule bisim1BinOp2)
    ultimately show ?thesis using ins by fastforce
  next
    case False with IH1 len False call cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1BinOp1 elim!: BinOp_\<tau>ExecrI1 intro!: exI)
  qed
next
  case (bisim1BinOp2 e2 n e' xs stk loc pc e1 bop v1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
  from exec have "\<tau>Exec_mover_a P t (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None)
                                              ((rev vs @ Addr a # stk') @ [v1], loc', length (compE2 e1) + pc', None)"
    by(rule BinOp_\<tau>ExecrI2)
  moreover from bisim'
  have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e', xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v1], loc', length (compE2 e1) + pc', None)"
    by(rule bisim1_bisims1.bisim1BinOp2)
  ultimately show ?case using pc' by(fastforce)
next
  case bisim1LAss1 thus ?case
    by(auto)(fastforce intro: bisim1_bisims1.bisim1LAss1 elim!: LAss_\<tau>ExecrI intro!: exI)
next
  case bisim1LAss2 thus ?case by simp
next
  case (bisim1AAcc1 A n a' xs stk loc pc i)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars a' \<le> length xs; \<not> contains_insync A\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 i = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i \<le> length xs; \<not> contains_insync i\<rbrakk> \<Longrightarrow> ?concl i n i xs 0 [] xs\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (a'\<lfloor>i\<rceil>) \<le> length xs\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note cs = \<open>\<not> contains_insync (A\<lfloor>i\<rceil>)\<close>
  show ?case
  proof(cases "is_val a'")
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "\<tau>Exec_mover_a P t A h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      by-(rule AAcc_\<tau>ExecrI1)
    also from call IH2[of loc] len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_mover_a P t i h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 i ! pc' = Invoke M' (length vs)" "pc' < length (compE2 i)"
      and bisim': "P,i,h \<turnstile> (i, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from AAcc_\<tau>ExecrI2[OF exec, of A v]
    have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil>) h ([v], loc, length (compE2 A), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 A) + pc', None)" by simp
    also (rtranclp_trans) from bisim'
    have "P,A\<lfloor>i\<rceil>,h \<turnstile> (Val v\<lfloor>i\<rceil>, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
      by(rule bisim1AAcc2)
    ultimately show ?thesis using ins by fastforce
  next
    case False with IH1 len False call cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1AAcc1 elim!: AAcc_\<tau>ExecrI1 intro!: exI)
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc A v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 i)" "compE2 i ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t i h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,i,h \<turnstile> (i', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
  from exec have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil>) h (stk @ [v], loc, length (compE2 A) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
    by(rule AAcc_\<tau>ExecrI2)
  moreover from bisim'
  have "P,A\<lfloor>i\<rceil>,h \<turnstile> (Val v\<lfloor>i'\<rceil>, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
    by(rule bisim1_bisims1.bisim1AAcc2)
  ultimately show ?case using pc' by(fastforce)
next
  case (bisim1AAss1 A n a' xs stk loc pc i e)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars a' \<le> length xs; \<not> contains_insync A \<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 i = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i \<le> length xs; \<not> contains_insync i\<rbrakk> \<Longrightarrow> ?concl i n i xs 0 [] xs\<close>
  note IH3 = \<open>\<And>xs. \<lbrakk>call1 e = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e \<le> length xs; \<not> contains_insync e\<rbrakk> \<Longrightarrow> ?concl e n e xs 0 [] xs\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (a'\<lfloor>i\<rceil> := e) \<le> length xs\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note cs = \<open>\<not> contains_insync (A\<lfloor>i\<rceil> := e)\<close>
  show ?case
  proof(cases "is_val a'")
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "\<tau>Exec_mover_a P t A h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence exec: "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([v], loc, length (compE2 A), None)"
      by-(rule AAss_\<tau>ExecrI1)
    show ?thesis
    proof(cases "is_val i")
      case True
      then obtain v' where [simp]: "i = Val v'" by auto
      note exec also from bisim2
      have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([v'], loc, length (compE2 i), None)"
        by(auto dest!: bisim1Val2D1)
      from AAss_\<tau>ExecrI2[OF this, of A e v]
      have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h ([v], loc, length (compE2 A), None) ([v', v], loc, length (compE2 A) + length (compE2 i), None)" by simp
      also (rtranclp_trans) from call IH3[of loc] len cs obtain pc' stk' loc'
        where exec: "\<tau>Exec_mover_a P t e h ([], loc, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
        and ins: "compE2 e ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e)"
        and bisim': "P,e,h \<turnstile> (e, loc) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from AAss_\<tau>ExecrI3[OF exec, of A i v' v]
      have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h ([v', v], loc, length (compE2 A) + length (compE2 i), None)
                        ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)" by simp
      also (rtranclp_trans) from bisim'
      have "P,A\<lfloor>i\<rceil> := e,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
        by - (rule bisim1AAss3, simp)
      ultimately show ?thesis using ins by fastforce
    next
      case False
      note exec also from False call IH2[of loc] len cs obtain pc' stk' loc'
        where exec: "\<tau>Exec_mover_a P t i h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
        and ins: "compE2 i ! pc' = Invoke M' (length vs)" "pc' < length (compE2 i)"
        and bisim': "P,i,h \<turnstile> (i, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from AAss_\<tau>ExecrI2[OF exec, of A e v]
      have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h ([v], loc, length (compE2 A), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 A) + pc', None)" by simp
      also (rtranclp_trans) from bisim'
      have "P,A\<lfloor>i\<rceil> := e,h \<turnstile> (Val v\<lfloor>i\<rceil> := e, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
        by(rule bisim1AAss2)
      ultimately show ?thesis using ins False by(fastforce intro!: exI)
    qed
  next
    case False with IH1 len False call cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1AAss1 elim!: AAss_\<tau>ExecrI1 intro!: exI)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc A e v)
  note IH2 = \<open>\<lbrakk>call1 i' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars i' \<le> length xs; \<not> contains_insync i\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc\<close>
  note IH3 = \<open>\<And>xs. \<lbrakk>call1 e = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e \<le> length xs; \<not> contains_insync e\<rbrakk> \<Longrightarrow> ?concl e n e xs 0 [] xs\<close>
  note call = \<open>call1 (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (Val v\<lfloor>i'\<rceil> := e) \<le> length xs\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note cs = \<open>\<not> contains_insync (A\<lfloor>i\<rceil> := e)\<close>
  show ?case
  proof(cases "is_val i'")
    case True
    then obtain v' where [simp]: "i' = Val v'" by auto
    from bisim2 have exec: "\<tau>Exec_mover_a P t i h (stk, loc, pc, None) ([v'], loc, length (compE2 i), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    from AAss_\<tau>ExecrI2[OF exec, of A e v]
    have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h (stk @ [v], loc, length (compE2 A) + pc, None) ([v', v], loc, length (compE2 A) + length (compE2 i), None)" by simp
    also from call IH3[of loc] len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_mover_a P t e h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e)"
      and bisim': "P,e,h \<turnstile> (e, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from AAss_\<tau>ExecrI3[OF exec, of A i v' v]
    have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil> := e) h ([v', v], loc, length (compE2 A) + length (compE2 i), None)
                       ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)" by simp
    also (rtranclp_trans) from bisim'
    have "P,A\<lfloor>i\<rceil> := e,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
      by(rule bisim1AAss3)
    ultimately show ?thesis using ins by(fastforce intro!: exI)
  next
    case False
    with IH2 len call cs obtain pc' loc' stk'
      where ins: "pc' < length (compE2 i)" "compE2 i ! pc' = Invoke M' (length vs)"
      and exec: "\<tau>Exec_mover_a P t i h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and bisim': "P,i,h \<turnstile> (i', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
    from bisim' have "P,A\<lfloor>i\<rceil> := e,h \<turnstile> (Val v\<lfloor>i'\<rceil> := e, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 A) + pc', None)"
      by(rule bisim1_bisims1.bisim1AAss2)
    with AAss_\<tau>ExecrI2[OF exec, of A e v] ins False show ?thesis by(auto intro!: exI)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc A i v v')
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
  from exec have "\<tau>Exec_mover_a P t (A\<lfloor>i\<rceil>:=e) h (stk @ [v', v], loc, length (compE2 A) + length (compE2 i) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
    by(rule AAss_\<tau>ExecrI3)
  moreover from bisim'
  have "P,A\<lfloor>i\<rceil> := e,h \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e', xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 A) + length (compE2 i) + pc', None)"
    by(rule bisim1_bisims1.bisim1AAss3)
  ultimately show ?case using pc' by(fastforce intro!: exI)
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(auto)(fastforce intro: bisim1_bisims1.bisim1ALength elim!: ALength_\<tau>ExecrI intro!: exI)
next
  case bisim1FAcc thus ?case
    by(auto)(fastforce intro: bisim1_bisims1.bisim1FAcc elim!: FAcc_\<tau>ExecrI intro!: exI)
next
  case (bisim1FAss1 e n e' xs stk loc pc e2 F D)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<not> contains_insync e\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 e2 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2 \<le> length xs; \<not> contains_insync e2\<rbrakk> \<Longrightarrow> ?concl e2 n e2 xs 0 [] xs\<close>
  note call = \<open>call1 (e'\<bullet>F{D} := e2) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (e'\<bullet>F{D} := e2) \<le> length xs\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note cs = \<open>\<not> contains_insync (e\<bullet>F{D} := e2)\<close>
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e\<bullet>F{D} := e2) h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by-(rule FAss_\<tau>ExecrI1)
    also from call IH2[of loc] len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_mover_a P t e2 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e2 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e2)"
      and bisim': "P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from FAss_\<tau>ExecrI2[OF exec, of e F D v]
    have "\<tau>Exec_mover_a P t (e\<bullet>F{D} := e2) h ([v], loc, length (compE2 e), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e) + pc', None)" by simp
    also (rtranclp_trans) from bisim'
    have "P,e\<bullet>F{D} := e2,h \<turnstile> (Val v\<bullet>F{D} := e2, xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
      by(rule bisim1FAss2)
    ultimately show ?thesis using ins by fastforce
  next
    case False with IH1 len False call cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1FAss1 elim!: FAss_\<tau>ExecrI1 intro!: exI)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc e F D v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
  from exec have "\<tau>Exec_mover_a P t (e\<bullet>F{D} := e2) h (stk @ [v], loc, length (compE2 e) + pc, None)
                                       ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
    by(rule FAss_\<tau>ExecrI2)
  moreover from bisim'
  have "P,e\<bullet>F{D} := e2,h \<turnstile> (Val v\<bullet>F{D} := e', xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e) + pc', None)"
    by(rule bisim1_bisims1.bisim1FAss2)
  ultimately show ?case using pc' by(fastforce)
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1CAS1 e1 n e' xs stk loc pc e2 e3 D F)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<not> contains_insync e1 \<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 e2 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2 \<le> length xs; \<not> contains_insync e2\<rbrakk> \<Longrightarrow> ?concl e2 n e2 xs 0 [] xs\<close>
  note IH3 = \<open>\<And>xs. \<lbrakk>call1 e3 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e3 \<le> length xs; \<not> contains_insync e3\<rbrakk> \<Longrightarrow> ?concl e3 n e3 xs 0 [] xs\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars _ \<le> length xs\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note cs = \<open>\<not> contains_insync _\<close>
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence exec: "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h (stk, loc, pc, None) ([v], loc, length (compE2 e1), None)"
      by-(rule CAS_\<tau>ExecrI1)
    show ?thesis
    proof(cases "is_val e2")
      case True
      then obtain v' where [simp]: "e2 = Val v'" by auto
      note exec also from bisim2
      have "\<tau>Exec_mover_a P t e2 h ([], loc, 0, None) ([v'], loc, length (compE2 e2), None)"
        by(auto dest!: bisim1Val2D1)
      from CAS_\<tau>ExecrI2[OF this, of e1 D F e3]
      have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h ([v], loc, length (compE2 e1), None) ([v', v], loc, length (compE2 e1) + length (compE2 e2), None)" by simp
      also (rtranclp_trans) from call IH3[of loc] len cs obtain pc' stk' loc'
        where exec: "\<tau>Exec_mover_a P t e3 h ([], loc, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
        and ins: "compE2 e3 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e3)"
        and bisim': "P,e3,h \<turnstile> (e3, loc) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from CAS_\<tau>ExecrI3[OF exec, of e1 D F e2 v' v]
      have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h ([v', v], loc, length (compE2 e1) + length (compE2 e2), None)
                        ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)" by simp
      also (rtranclp_trans) from bisim'
      have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e3), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)"
        by - (rule bisim1CAS3, simp)
      ultimately show ?thesis using ins by fastforce
    next
      case False
      note exec also from False call IH2[of loc] len cs obtain pc' stk' loc'
        where exec: "\<tau>Exec_mover_a P t e2 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
        and ins: "compE2 e2 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e2)"
        and bisim': "P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
      from CAS_\<tau>ExecrI2[OF exec, of e1 D F e3 v]
      have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h ([v], loc, length (compE2 e1), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e1) + pc', None)" by simp
      also (rtranclp_trans) from bisim'
      have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e1) + pc', None)"
        by(rule bisim1CAS2)
      ultimately show ?thesis using ins False by(fastforce intro!: exI)
    qed
  next
    case False with IH1 len False call cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1CAS1 elim!: CAS_\<tau>ExecrI1 intro!: exI)
  qed
next
  case (bisim1CAS2 e2 n e2' xs stk loc pc e1 e3 D F v)
  note IH2 = \<open>\<lbrakk>call1 e2' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e2' \<le> length xs; \<not> contains_insync e2\<rbrakk> \<Longrightarrow> ?concl e2 n e2' xs pc stk loc\<close>
  note IH3 = \<open>\<And>xs. \<lbrakk>call1 e3 = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e3 \<le> length xs; \<not> contains_insync e3\<rbrakk> \<Longrightarrow> ?concl e3 n e3 xs 0 [] xs\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars _ \<le> length xs\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note cs = \<open>\<not> contains_insync _\<close>
  show ?case
  proof(cases "is_val e2'")
    case True
    then obtain v' where [simp]: "e2' = Val v'" by auto
    from bisim2 have exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) ([v'], loc, length (compE2 e2), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    from CAS_\<tau>ExecrI2[OF exec, of e1 D F e3 v]
    have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h (stk @ [v], loc, length (compE2 e1) + pc, None) ([v', v], loc, length (compE2 e1) + length (compE2 e2), None)" by simp
    also from call IH3[of loc] len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_mover_a P t e3 h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compE2 e3 ! pc' = Invoke M' (length vs)" "pc' < length (compE2 e3)"
      and bisim': "P,e3,h \<turnstile> (e3, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
    from CAS_\<tau>ExecrI3[OF exec, of e1 D F e2 v' v]
    have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h ([v', v], loc, length (compE2 e1) + length (compE2 e2), None)
                       ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)" by simp
    also (rtranclp_trans) from bisim'
    have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e3), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)"
      by(rule bisim1CAS3)
    ultimately show ?thesis using ins by(fastforce intro!: exI)
  next
    case False
    with IH2 len call cs obtain pc' loc' stk'
      where ins: "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
      and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and bisim': "P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
    from bisim' have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, e2', e3), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 e1) + pc', None)"
      by(rule bisim1_bisims1.bisim1CAS2)
    with CAS_\<tau>ExecrI2[OF exec, of e1 D F e3 v] ins False show ?thesis by(auto intro!: exI)
  qed
next
  case (bisim1CAS3 e3 n e3' xs stk loc pc e1 e2 D F v v')
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e3)" "compE2 e3 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e3 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e3,h \<turnstile> (e3', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by fastforce
  from exec have "\<tau>Exec_mover_a P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, None)
                                    ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)"
    by(rule CAS_\<tau>ExecrI3)
  moreover from bisim'
  have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e3'), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', None)"
    by(rule bisim1_bisims1.bisim1CAS3)
  ultimately show ?case using pc' by(fastforce intro!: exI)
next
  case (bisim1Call1 obj n obj' xs stk loc pc ps M)
  note IH1 = \<open>\<lbrakk>call1 obj' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars obj' \<le> length xs; \<not> contains_insync obj\<rbrakk> \<Longrightarrow> ?concl obj n obj' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>calls1 ps = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss ps \<le> length xs; \<not> contains_insyncs ps\<rbrakk> \<Longrightarrow> ?concls ps n ps xs 0 [] xs\<close>
  note len = \<open>n + max_vars (obj'\<bullet>M(ps)) \<le> length xs\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (obj'\<bullet>M(ps)) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note cs = \<open>\<not> contains_insync (obj\<bullet>M(ps))\<close>
  from call show ?case
  proof(cases rule: call1_callE)
    case CallObj
    hence "\<not> is_val obj'" by auto
    with CallObj IH1 len cs show ?thesis
      by(clarsimp)(fastforce intro: bisim1_bisims1.bisim1Call1 elim!: Call_\<tau>ExecrI1 intro!: exI)
  next
    case (CallParams v)
    with bisim1 have "\<tau>Exec_mover_a P t obj h (stk, loc, pc, None) ([v], loc, length (compE2 obj), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h (stk, loc, pc, None) ([v], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    also from IH2[of loc] CallParams len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_movesr_a P t ps h ([], loc, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compEs2 ps ! pc' = Invoke M' (length vs)" "pc' < length (compEs2 ps)"
      and bisim': "P,ps,h \<turnstile> (ps, xs) [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from Call_\<tau>ExecrI2[OF exec, of obj M v]
    have "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h ([v], loc, length (compE2 obj), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 obj) + pc', None)" by simp
    also (rtranclp_trans)
    have "P,obj\<bullet>M(ps),h \<turnstile> (Val v\<bullet>M(ps), xs) \<leftrightarrow> ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      using bisim' by(rule bisim1CallParams)
    ultimately show ?thesis using ins CallParams by fastforce
  next
    case [simp]: Call
    from bisim1 have "\<tau>Exec_mover_a P t obj h (stk, loc, pc, None) ([Addr a], loc, length (compE2 obj), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h (stk, loc, pc, None) ([Addr a], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    also have "\<tau>Exec_movesr_a P t ps h ([], xs, 0, None) (rev vs, xs, length (compEs2 ps), None)"
    proof(cases vs)
      case Nil with Call show ?thesis by(auto)
    next
      case Cons with Call bisims1_Val_\<tau>Exec_moves[OF bisims1_refl[of P h "map Val vs" loc]]
      show ?thesis by(auto simp add: bsoks_def)
    qed
    from Call_\<tau>ExecrI2[OF this, of obj M "Addr a"]
    have "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h ([Addr a], loc, length (compE2 obj), None) (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)" by simp
    also (rtranclp_trans)
    have "P,ps,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (rev vs,xs,length (compEs2 ps),None)"
      by(rule bisims1_map_Val_append[OF bisims1Nil, simplified])(simp_all add: bsoks_def)
    hence "P,obj\<bullet>M(ps),h \<turnstile> (addr a\<bullet>M(map Val vs), xs) \<leftrightarrow> (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)"
      by(rule bisim1CallParams)
    ultimately show ?thesis by fastforce
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc obj M v)
  note IH2 = \<open>\<lbrakk>calls1 ps' = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss ps' \<le> length xs; \<not> contains_insyncs ps\<rbrakk> \<Longrightarrow> ?concls ps n ps' xs pc stk loc\<close>
  note bisim2 = \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v\<bullet>M(ps')) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_vars (Val v\<bullet>M(ps')) \<le> length xs\<close>
  note cs = \<open>\<not> contains_insync (obj\<bullet>M(ps))\<close>
  from call show ?case
  proof(cases rule: call1_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v')
    with IH2 len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "pc' < length (compEs2 ps)" "compEs2 ps ! pc' = Invoke M' (length vs)"
      and bisim': "P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from exec have "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, None)
                                ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      by(rule Call_\<tau>ExecrI2)
    moreover have "P,obj\<bullet>M(ps),h \<turnstile> (Val v\<bullet>M(ps'), xs) \<leftrightarrow>
                                  ((rev vs @ Addr a # stk') @ [v], loc', length (compE2 obj) + pc', None)"
      using bisim' by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis using ins by fastforce
  next
    case Call
    hence [simp]: "v = Addr a" "ps' = map Val vs" "M' = M" by simp_all
    have "xs = loc \<and> \<tau>Exec_movesr_a P t ps h (stk, loc, pc, None) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True with bisim2 show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves)
    next
      case False
      from bisim2 have "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
      with False have "pc = length (compEs2 ps)" by simp
      with bisim2 show ?thesis by(auto dest: bisims1_Val_length_compEs2D)
    qed
    then obtain [simp]: "xs = loc"
      and exec: "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, None) (rev vs, loc, length (compEs2 ps), None)" ..
    from exec have "\<tau>Exec_mover_a P t (obj\<bullet>M(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, None)
                              (rev vs @ [v], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by(rule Call_\<tau>ExecrI2)
    moreover from bisim2 have len: "length ps = length ps'" by(auto dest: bisims1_lengthD)
    moreover have "P,ps,h \<turnstile> (map Val vs,xs) [\<leftrightarrow>] (rev vs,xs,length (compEs2 ps),None)" using len
      by-(rule bisims1_map_Val_append[OF bisims1Nil, simplified], simp_all)
    hence "P,obj\<bullet>M(ps),h \<turnstile> (addr a\<bullet>M(map Val vs), xs) \<leftrightarrow> (rev vs @ [Addr a], xs, length (compE2 obj) + length (compEs2 ps), None)" by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis by fastforce
  qed
next
  case bisim1BlockSome1 thus ?case by simp
next
  case bisim1BlockSome2 thus ?case by simp
next
  case (bisim1BlockSome4 e n e' xs stk loc pc V T v)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>ExecrI_Some[OF exec, of V T v]
  moreover from bisim' have "P,{V:T=\<lfloor>v\<rfloor>; e},h \<turnstile> ({V:T=None; e'}, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', Suc (Suc pc'), None)"
    by(rule bisim1_bisims1.bisim1BlockSome4)
  ultimately show ?case using pc' by fastforce
next  
 case (bisim1BlockNone e n e' xs stk loc pc V T)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e)" "compE2 e ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note Block_\<tau>ExecrI_None[OF exec, of V T]
  moreover from bisim' have "P,{V:T=None; e},h \<turnstile> ({V:T=None; e'}, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)"
    by(rule bisim1_bisims1.bisim1BlockNone)
  ultimately show ?case using pc' by fastforce
next
  case bisim1Sync1 thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1Sync1 elim!: Sync_\<tau>ExecrI intro!: exI)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1Sync4 elim!: Insync_\<tau>ExecrI intro!: exI)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1InSync thus ?case by simp
next
  case bisim1Seq1 thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1Seq1 elim!: Seq_\<tau>ExecrI1 intro!: exI)
next
  case (bisim1Seq2 e2 n e' xs stk loc pc e1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Seq_\<tau>ExecrI2[OF exec, of e1] pc' bisim'
  show ?case by(fastforce intro: bisim1_bisims1.bisim1Seq2 intro!: exI)
next
  case bisim1Cond1 thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1Cond1 elim!: Cond_\<tau>ExecrI1 intro!: exI)+
next
  case (bisim1CondThen e1 n e' xs stk loc pc e e2)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e1)" "compE2 e1 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Cond_\<tau>ExecrI2[OF exec] pc' bisim' show ?case
    by(fastforce intro: bisim1_bisims1.bisim1CondThen intro!: exI)
next
  case (bisim1CondElse e2 n e' xs stk loc pc e e1)
  then obtain pc' loc' stk' where pc': "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Cond_\<tau>ExecrI3[OF exec] pc' bisim' show ?case
    by (fastforce intro: bisim1_bisims1.bisim1CondElse intro!: exI)
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1While3 elim!: While_\<tau>ExecrI1 intro!: exI)+
next
  case bisim1While4 thus ?case
    by (auto)(fastforce intro!: While_\<tau>ExecrI2 bisim1_bisims1.bisim1While4 exI)+
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by (auto)(fastforce intro!: exI bisim1_bisims1.bisim1Throw1 elim!: Throw_\<tau>ExecrI)+
next
  case bisim1Try thus ?case
    by (auto)(fastforce intro: bisim1_bisims1.bisim1Try elim!: Try_\<tau>ExecrI1 intro!: exI)+
next
  case (bisim1TryCatch1 e n a' xs stk loc pc C' C e2 V)
  note IH2 = \<open>\<And>xs. \<lbrakk>call1 e2 = \<lfloor>(a, M', vs)\<rfloor>; Suc n + max_vars e2 \<le> length xs; \<not> contains_insync e2 \<rbrakk> \<Longrightarrow> ?concl e2 (Suc V) e2 xs 0 [] xs\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)\<close>
  note bisim2 = \<open>\<And>xs. P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note len = \<open>n + max_vars {V:Class C=None; e2} \<le> length (xs[V := Addr a'])\<close>
  note cs = \<open>\<not> contains_insync (try e catch(C V) e2)\<close>
  from bisim1 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from len have "\<tau>Exec_mover_a P t (try e catch(C V) e2) h ([Addr a'], loc, Suc (length (compE2 e)), None) ([], loc[V := Addr a'], Suc (Suc (length (compE2 e))), None)"
    by -(rule \<tau>Execr1step,auto simp add: exec_move_def intro: \<tau>move2_\<tau>moves2.intros exec_instr)
  also from IH2[of "loc[V := Addr a']"] len \<open>call1 {V:Class C=None; e2} = \<lfloor>(a, M', vs)\<rfloor>\<close> cs
  obtain pc' loc' stk'
    where exec: "\<tau>Exec_mover_a P t e2 h ([], loc[V := Addr a'], 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and ins: "pc' < length (compE2 e2)" "compE2 e2 ! pc' = Invoke M' (length vs)"
    and bisim': "P,e2,h \<turnstile> (e2, loc[V := Addr a']) \<leftrightarrow> (rev vs @ Addr a # stk', loc', pc', None)" by auto
  from Try_\<tau>ExecrI2[OF exec, of e C V]
  have "\<tau>Exec_mover_a P t (try e catch(C V) e2) h ([], loc[V := Addr a'], Suc (Suc (length (compE2 e))), None) (rev vs @ Addr a # stk', loc', Suc (Suc (length (compE2 e) + pc')), None)" by simp
  also from bisim'
  have "P,try e catch(C V) e2,h \<turnstile> ({V:Class C=None; e2}, loc[V := Addr a']) \<leftrightarrow> (rev vs @ Addr a # stk', loc', (Suc (Suc (length (compE2 e) + pc'))), None)"
    by(rule bisim1TryCatch2)
  ultimately show ?case using ins by fastforce
next
  case bisim1TryCatch2 thus ?case
    by (auto)(fastforce intro!: Try_\<tau>ExecrI2 bisim1_bisims1.bisim1TryCatch2 exI)+
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e n e' xs stk loc pc es)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M', vs)\<rfloor>; n + max_vars e' \<le> length xs; \<not> contains_insync e\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note IH2 = \<open>\<And>xs. \<lbrakk>calls1 es = \<lfloor>(a, M', vs)\<rfloor>; n + max_varss es \<le> length xs; \<not> contains_insyncs es\<rbrakk> \<Longrightarrow> ?concls es n es xs 0 [] xs\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>calls1 (e' # es) = \<lfloor>(a, M', vs)\<rfloor>\<close>
  note len = \<open>n + max_varss (e' # es) \<le> length xs\<close>
  note cs = \<open>\<not> contains_insyncs (e # es)\<close>
  show ?case
  proof(cases "is_val e'")
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    with bisim1 have "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      and [simp]: "xs = loc" by(auto dest!: bisim1Val2D1)
    hence "\<tau>Exec_movesr_a P t (e # es) h (stk, loc, pc, None) ([v], loc, length (compE2 e), None)"
      by-(rule \<tau>Exec_mover_\<tau>Exec_movesr)
    also from call IH2[of loc] len cs obtain pc' stk' loc'
      where exec: "\<tau>Exec_movesr_a P t es h ([], xs, 0, None) (rev vs @ Addr a # stk', loc', pc', None)"
      and ins: "compEs2 es ! pc' = Invoke M' (length vs)" "pc' < length (compEs2 es)"
      and bisim': "P,es,h \<turnstile> (es, xs) [\<leftrightarrow>] (rev vs @ Addr a # stk',loc',pc',None)" by auto
    from append_\<tau>Exec_movesr[OF _ exec, of "[v]" "[e]"]
    have "\<tau>Exec_movesr_a P t (e # es) h ([v], loc, length (compE2 e), None) (rev vs @ Addr a # (stk' @ [v]), loc', length (compE2 e) + pc', None)"
      by simp
    also (rtranclp_trans) from bisim'
    have "P,e # es,h \<turnstile> (Val v # es, xs) [\<leftrightarrow>]
                         ((rev vs @ Addr a # stk') @ [v],loc',length (compE2 e) + pc',None)"
      by(rule bisim1_bisims1.bisims1List2)
    ultimately show ?thesis using ins by fastforce
  next
    case False
    with call IH1 len cs show ?thesis
      by (auto)(fastforce intro!: \<tau>Exec_mover_\<tau>Exec_movesr bisim1_bisims1.bisims1List1 exI)+
  qed
next
  case (bisims1List2 es n es' xs stk loc pc e v)
  then obtain pc' stk' loc' where pc': "pc' < length (compEs2 es)" "compEs2 es ! pc' = Invoke M' (length vs)"
    and exec: "\<tau>Exec_movesr_a P t es h (stk, loc, pc, None) (rev vs @ Addr a # stk', loc', pc', None)"
    and bisim': "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (rev vs @ Addr a # stk', loc', pc', None)" by auto
  note append_\<tau>Exec_movesr[OF _ exec, of "[v]" "[e]"]
  moreover from bisim'
  have "P,e#es,h \<turnstile> (Val v# es', xs) [\<leftrightarrow>] ((rev vs @ Addr a # stk') @ [v],loc',length (compE2 e) + pc',None)"
    by(rule bisim1_bisims1.bisims1List2)
  ultimately show ?case using pc' by fastforce
qed 

lemma fixes P :: "'addr J1_prog"
  shows bisim1_inline_call_Val:
  "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None); call1 e' = \<lfloor>(a, M, vs)\<rfloor>;
     compE2 e ! pc = Invoke M n0 \<rbrakk>
    \<Longrightarrow> length stk \<ge> Suc (length vs) \<and> n0 = length vs \<and>
       P,e,h \<turnstile> (inline_call (Val v) e', xs) \<leftrightarrow> (v # drop (Suc (length vs)) stk, loc, Suc pc, None)"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc")

  and bisims1_inline_calls_Val:
  "\<lbrakk> P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,None); calls1 es' = \<lfloor>(a, M, vs)\<rfloor>;
     compEs2 es ! pc = Invoke M n0 \<rbrakk>
    \<Longrightarrow> length stk \<ge> Suc (length vs) \<and> n0 = length vs \<and>
       P,es,h \<turnstile> (inline_calls (Val v) es', xs) [\<leftrightarrow>] (v # drop (Suc (length vs)) stk,loc,Suc pc,None)"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc")
proof(induct "(e', xs)" "(stk, loc, pc, None :: 'addr option)"
    and "(es', xs)" "(stk, loc, pc, None :: 'addr option)"
    arbitrary: e' xs stk loc pc and es' xs stk loc pc rule: bisim1_bisims1.inducts)
  case bisim1Val2 thus ?case by simp
next
  case bisim1New thus ?case by simp
next
  case bisim1NewArray thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1NewArray)
next
  case bisim1Cast thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Cast)
next
  case bisim1InstanceOf thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1InstanceOf)
next
  case bisim1Val thus ?case by simp
next
  case bisim1Var thus ?case by simp
next
  case (bisim1BinOp1 e1 e' xs stk loc pc bop e2)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M n0 \<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (e' \<guillemotleft>bop\<guillemotright> e2) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis
      by(auto intro: bisim1_bisims1.bisim1BinOp1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1BinOp2 e2 e' xs stk loc pc e1 bop v1)
  note IH2 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e2 n e' xs pc stk loc\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v1 \<guillemotleft>bop\<guillemotright> e') = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! (length (compE2 e1) + pc) = Invoke M n0\<close>
  from call bisim2 have pc: "pc < length (compE2 e2)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e2 ! pc = Invoke M n0" by(simp)
  from IH2 ins' pc call show ?case by(auto dest: bisim1_bisims1.bisim1BinOp2)
next
  case bisim1LAss1 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1LAss1)
next
  case bisim1LAss2 thus ?case by simp
next
  case (bisim1AAcc1 A a' xs stk loc pc i)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil>) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis
      by(auto intro: bisim1_bisims1.bisim1AAcc1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAcc2 i i' xs stk loc pc A v)
  note IH2 = \<open>\<lbrakk>call1 i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v\<lfloor>i'\<rceil>) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil>) ! (length (compE2 A) + pc) = Invoke M n0\<close>
  from call bisim2 have pc: "pc < length (compE2 i)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 i ! pc = Invoke M n0" by(simp)
  from IH2 ins' pc call show ?case
    by(auto dest: bisim1_bisims1.bisim1AAcc2)
next
  case (bisim1AAss1 A a' xs stk loc pc i e)
  note IH1 = \<open>\<lbrakk>call1 a' = \<lfloor>(a, M, vs)\<rfloor>; compE2 A ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl A n a' xs pc stk loc\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (a'\<lfloor>i\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil> := e) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val a'")
    case False
    with bisim1 call have "pc < length (compE2 A)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis by(auto intro: bisim1_bisims1.bisim1AAss1)
  next
    case True
    then obtain v where [simp]: "a' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 A)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 A)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 A)" by(cases "pc < length (compE2 A)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAss2 i i' xs stk loc pc A e v)
  note IH2 = \<open>\<lbrakk>call1 i' = \<lfloor>(a, M, vs)\<rfloor>; compE2 i ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl i n i' xs pc stk loc\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v\<lfloor>i'\<rceil> := e) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (A\<lfloor>i\<rceil> := e) ! (length (compE2 A) + pc) = Invoke M n0\<close>
  show ?case
  proof(cases "is_val i'")
    case False
    with bisim2 call have pc: "pc < length (compE2 i)" by(auto intro: bisim1_call_pcD)
    with ins have ins': "compE2 i ! pc = Invoke M n0" by(simp)
    from IH2 ins' pc False call show ?thesis by(auto dest: bisim1_bisims1.bisim1AAss2)
  next
    case True
    then obtain v where [simp]: "i' = Val v" by auto
    from bisim2 have "pc \<le> length (compE2 i)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 i)"
      with bisim2 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 i)" by(cases "pc < length (compE2 i)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1AAss3 e e' xs stk loc pc i A v v')
  note IH2 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v\<lfloor>Val v'\<rceil> := e') = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (i\<lfloor>A\<rceil> := e) ! (length (compE2 i) + length (compE2 A) + pc) = Invoke M n0\<close>
  from call bisim3 have pc: "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e ! pc = Invoke M n0" by(simp)
  from IH2 ins' pc call show ?case by(auto dest: bisim1_bisims1.bisim1AAss3)
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1ALength)
next
  case bisim1FAcc thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1FAcc)
next
  case (bisim1FAss1 e1 e' xs stk loc pc F D e2)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (e'\<bullet>F{D} := e2) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (e1\<bullet>F{D} := e2) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis
      by(auto intro: bisim1_bisims1.bisim1FAss1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1FAss2 e2 e' xs stk loc pc e1 F D v1)
  note IH2 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e2 n e' xs pc stk loc\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v1\<bullet>F{D} := e') = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (e1\<bullet>F{D} := e2) ! (length (compE2 e1) + pc) = Invoke M n0\<close>
  from call bisim2 have pc: "pc < length (compE2 e2)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e2 ! pc = Invoke M n0" by(simp)
  from IH2 ins' pc call show ?case by(auto dest: bisim1_bisims1.bisim1FAss2)
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1CAS1 e1 e' xs stk loc pc D F e2 E3)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e1 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e1 n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 _ ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e1)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis by(auto intro: bisim1_bisims1.bisim1CAS1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e1)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e1)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e1)" by(cases "pc < length (compE2 e1)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1CAS2 e2 e2' xs stk loc pc e1 D F e3 v)
  note IH2 = \<open>\<lbrakk>call1 e2' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e2 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e2 n e2' xs pc stk loc\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 _ ! (length (compE2 e1) + pc) = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e2'")
    case False
    with bisim2 call have pc: "pc < length (compE2 e2)" by(auto intro: bisim1_call_pcD)
    with ins have ins': "compE2 e2 ! pc = Invoke M n0" by(simp)
    from IH2 ins' pc False call show ?thesis by(auto dest: bisim1_bisims1.bisim1CAS2)
  next
    case True
    then obtain v where [simp]: "e2' = Val v" by auto
    from bisim2 have "pc \<le> length (compE2 e2)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e2)"
      with bisim2 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e2)" by(cases "pc < length (compE2 e2)") auto
    with ins have False by(simp)
    thus ?thesis ..
  qed
next
  case (bisim1CAS3 e3 e3' xs stk loc pc e1 D F e2 v v')
  note IH2 = \<open>\<lbrakk>call1 e3' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e3 ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e3 n e3' xs pc stk loc\<close>
  note bisim3 = \<open>P,e3,h \<turnstile> (e3', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 _ = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 _ ! (length (compE2 e1) + length (compE2 e2) + pc) = Invoke M n0\<close>
  from call bisim3 have pc: "pc < length (compE2 e3)" by(auto intro: bisim1_call_pcD)
  with ins have ins': "compE2 e3 ! pc = Invoke M n0" by(simp)
  from IH2 ins' pc call show ?case by(auto dest: bisim1_bisims1.bisim1CAS3)
next
  case (bisim1Call1 obj obj' xs stk loc pc M' ps)
  note IH1 = \<open>\<lbrakk>call1 obj' = \<lfloor>(a, M, vs)\<rfloor>; compE2 obj ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl obj n obj' xs pc stk loc\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>call1 (obj'\<bullet>M'(ps)) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val obj'")
    case False
    with call bisim1 have "pc < length (compE2 obj)" by(auto intro: bisim1_call_pcD)
    with call False ins IH1 False show ?thesis
      by(auto intro: bisim1_bisims1.bisim1Call1)
  next
    case True
    then obtain v' where [simp]: "obj' = Val v'" by auto
    from bisim1 have "pc \<le> length (compE2 obj)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 obj)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 obj)" by(cases "pc < length (compE2 obj)") auto
    with ins have [simp]: "ps = []" "M' = M"
      by(auto simp add: nth_append split: if_split_asm)(auto simp add: neq_Nil_conv nth_append)
    from ins call have [simp]: "vs = []" by(auto split: if_split_asm)
    with bisim1 have [simp]: "stk = [v']" "xs = loc" by(auto dest: bisim1_pc_length_compE2D)
    from bisim1Val2[of "length (compE2 (obj\<bullet>M([])))" "obj\<bullet>M([])" P h v loc] call ins
    show ?thesis by(auto simp add: is_val_iff)
  qed
next
  case (bisim1CallParams ps ps' xs stk loc pc obj M' v')
  note IH2 = \<open>\<lbrakk>calls1 ps' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 ps ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concls ps n ps' xs pc stk loc\<close>
  note bisim = \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note call = \<open>call1 (Val v'\<bullet>M'(ps')) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M n0\<close>
  from call show ?case
  proof(cases rule: call1_callE)
    case CallObj thus ?thesis by simp
  next
    case (CallParams v'')
    hence [simp]: "v'' = v'" and call': "calls1 ps' = \<lfloor>(a, M, vs)\<rfloor>" by simp_all
    from bisim call' have pc: "pc < length (compEs2 ps)" by(rule bisims1_calls_pcD)
    with ins have ins': "compEs2 ps ! pc = Invoke M n0" by(simp add: nth_append)
    with IH2 call' ins pc
    have "P,ps,h \<turnstile> (inline_calls (Val v) ps', xs)
                [\<leftrightarrow>] (v # drop (Suc (length vs)) stk, loc, Suc pc, None)"
      and len: "Suc (length vs) \<le> length stk" and n0: "n0 = length vs" by auto
    hence "P,obj\<bullet>M'(ps),h \<turnstile> (Val v'\<bullet>M'(inline_calls (Val v) ps'), xs)
                           \<leftrightarrow> ((v # drop (Suc (length vs)) stk) @ [v'], loc, length (compE2 obj) + Suc pc, None)"
      by-(rule bisim1_bisims1.bisim1CallParams)
    thus ?thesis using call' len n0 by(auto simp add: is_vals_conv)
  next
    case Call
    hence [simp]: "v' = Addr a" "M' = M" "ps' = map Val vs" by auto
    from bisim have "pc \<le> length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
    moreover {
      assume pc: "pc < length (compEs2 ps)"
      with bisim ins have False by(auto dest: bisims_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compEs2 ps)" by(cases "pc < length (compEs2 ps)") auto
    from bisim have [simp]: "stk = rev vs" "xs = loc" by(auto dest: bisims1_Val_length_compEs2D)
    hence "P,obj\<bullet>M(ps),h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M(ps))), None)" by-(rule bisim1Val2, simp)
    moreover from bisim have "length ps = length ps'" by(rule bisims1_lengthD)
    ultimately show ?thesis using ins by(auto)
  qed
next
  case bisim1BlockSome1 thus ?case by simp
next
  case bisim1BlockSome2 thus ?case by simp
next
  case bisim1BlockSome4 thus ?case
    by(auto intro: bisim1_bisims1.bisim1BlockSome4)
next
  case bisim1BlockNone thus ?case
    by(auto intro: bisim1_bisims1.bisim1BlockNone)
next
  case bisim1Sync1 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Sync1)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 bisim1_bisims1.bisim1Sync4)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1InSync thus ?case by(simp)
next
  case bisim1Seq1 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Seq1)
next
  case bisim1Seq2 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)(fastforce dest: bisim1_bisims1.bisim1Seq2)
next
  case bisim1Cond1 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Cond1)
next
  case (bisim1CondThen e1 stk loc pc e e2 e' xs) thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
      (fastforce dest: bisim1_bisims1.bisim1CondThen[where e=e and ?e2.0=e2])
next
  case (bisim1CondElse e2 stk loc pc e e1 e' xs) thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
      (fastforce dest: bisim1_bisims1.bisim1CondElse[where e=e and ?e1.0=e1])
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1While3)
next
  case bisim1While4 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)(fastforce dest: bisim1_bisims1.bisim1While4)
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Throw1)
next
  case bisim1Try thus ?case
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2 intro: bisim1_bisims1.bisim1Try)
next
  case bisim1TryCatch1 thus ?case by simp
next
  case bisim1TryCatch2 thus ?case
    by(fastforce dest: bisim1_bisims1.bisim1TryCatch2)
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e e' xs stk loc pc es)
  note IH1 = \<open>\<lbrakk>call1 e' = \<lfloor>(a, M, vs)\<rfloor>; compE2 e ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concl e n e' xs pc stk loc\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  note call = \<open>calls1 (e' # es) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note ins = \<open>compEs2 (e # es) ! pc = Invoke M n0\<close>
  show ?case
  proof(cases "is_val e'")
    case False
    with bisim1 call have "pc < length (compE2 e)" by(auto intro: bisim1_call_pcD)
    with call ins False IH1 show ?thesis
      by(auto intro: bisim1_bisims1.bisims1List1)
  next
    case True
    then obtain v where [simp]: "e' = Val v" by auto
    from bisim1 have "pc \<le> length (compE2 e)" by(auto dest: bisim1_pc_length_compE2)
    moreover {
      assume pc: "pc < length (compE2 e)"
      with bisim1 ins have False by(auto dest: bisim_Val_pc_not_Invoke simp add: nth_append) }
    ultimately have [simp]: "pc = length (compE2 e)" by(cases "pc < length (compE2 e)") auto
    with ins call have False by(cases es)(auto)
    thus ?thesis ..
  qed
next
  case (bisims1List2 es es' xs stk loc pc e v')
  note IH = \<open>\<lbrakk>calls1 es' = \<lfloor>(a, M, vs)\<rfloor>; compEs2 es ! pc = Invoke M n0\<rbrakk> \<Longrightarrow> ?concls es n es' xs pc stk loc\<close>
  note call = \<open>calls1 (Val v' # es') = \<lfloor>(a, M, vs)\<rfloor>\<close>
  note bisim = \<open>P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note ins = \<open>compEs2 (e # es) ! (length (compE2 e) + pc) = Invoke M n0\<close>
  from call have call': "calls1 es' = \<lfloor>(a, M, vs)\<rfloor>" by simp
  with bisim have pc: "pc < length (compEs2 es)" by(rule bisims1_calls_pcD)
  with ins have ins': "compEs2 es ! pc = Invoke M n0" by(simp add: nth_append)
  from IH call ins pc show ?case
    by(auto split: if_split_asm dest: bisim1_bisims1.bisims1List2)
qed

lemma bisim1_fv: "P,e,h \<turnstile> (e', xs) \<leftrightarrow> s \<Longrightarrow> fv e' \<subseteq> fv e"
  and bisims1_fvs: "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] s \<Longrightarrow> fvs es' \<subseteq> fvs es"
apply(induct "(e', xs)" s and "(es', xs)" s arbitrary: e' xs and es' xs rule: bisim1_bisims1.inducts)
apply(auto)
done


lemma bisim1_syncvars: "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> s; syncvars e \<rbrakk> \<Longrightarrow> syncvars e'"
  and bisims1_syncvarss: "\<lbrakk> P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] s; syncvarss es \<rbrakk> \<Longrightarrow> syncvarss es'"
apply(induct "(e', xs)" s and "(es', xs)" s arbitrary: e' xs and es' xs rule: bisim1_bisims1.inducts)
apply(auto dest: bisim1_fv)
done

declare pcs_stack_xlift [simp]

lemma bisim1_Val_\<tau>red1r:
  "\<lbrakk> P, E, h \<turnstile> (e, xs) \<leftrightarrow> ([v], loc, length (compE2 E), None); n + max_vars e \<le> length xs; \<B> E n \<rbrakk> 
  \<Longrightarrow> \<tau>red1r P t h (e, xs) (Val v, loc)"

 and bisims1_Val_\<tau>Reds1r:
  "\<lbrakk> P, Es, h \<turnstile> (es, xs) [\<leftrightarrow>] (rev vs, loc, length (compEs2 Es), None); n + max_varss es \<le> length xs; \<B>s Es n \<rbrakk>
   \<Longrightarrow> \<tau>reds1r P t h (es, xs) (map Val vs, loc)"
proof(induct E n e xs stk\<equiv>"[v]" loc pc\<equiv>"length (compE2 E)" xcp\<equiv>"None::'addr option"
         and Es n es xs stk\<equiv>"rev vs" loc pc\<equiv>"length (compEs2 Es)" xcp\<equiv>"None::'addr option"
      arbitrary: v and vs rule: bisim1_bisims1_inducts_split)
  case bisim1BlockSome2 thus ?case by(simp (no_asm_use))
next
  case (bisim1BlockSome4 e n e' xs loc pc V T val)
  from \<open>\<B> {V:T=\<lfloor>val\<rfloor>; e} n\<close> have [simp]: "n = V" and "\<B> e (Suc n)" by auto
  note len = \<open>n + max_vars {V:T=None; e'} \<le> length xs\<close>
  hence V: "V < length xs" by simp
  from \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> ([v], loc, pc, None)\<close>
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = \<open>\<lbrakk>pc = length (compE2 e); Suc n + max_vars e' \<le> length xs; \<B> e (Suc n)\<rbrakk>
             \<Longrightarrow> \<tau>red1r P t h (e', xs) (Val v, loc)\<close>
  with len \<open>Suc (Suc pc) = length (compE2 {V:T=\<lfloor>val\<rfloor>; e})\<close> \<open>\<B> e (Suc n)\<close>
  have "\<tau>red1r P t h (e', xs) (Val v, loc)" by(simp)
  hence "\<tau>red1r P t h ({V:T=None; e'}, xs) ({V:T=None; Val v}, loc)"
    by(rule Block_None_\<tau>red1r_xt)
  thus ?case using V lenxs by(auto elim!: rtranclp.rtrancl_into_rtrancl intro: Red1Block \<tau>move1BlockRed)
next
  case (bisim1BlockNone e n e' xs loc V T)
  from \<open>\<B> {V:T=None; e} n\<close> have [simp]: "n = V" and "\<B> e (Suc n)" by auto
  note len = \<open>n + max_vars {V:T=None; e'} \<le> length xs\<close>
  hence V: "V < length xs" by simp
  from \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> ([v], loc, length (compE2 {V:T=None; e}), None)\<close>
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = \<open>\<lbrakk>length (compE2 {V:T=None; e}) = length (compE2 e); Suc n + max_vars e' \<le> length xs; \<B> e (Suc n) \<rbrakk>
              \<Longrightarrow> \<tau>red1r P t h (e', xs) (Val v, loc)\<close>
  with len \<open>\<B> e (Suc n)\<close> have "\<tau>red1r P t h (e', xs) (Val v, loc)" by(simp)
  hence "\<tau>red1r P t h ({V:T=None; e'}, xs) ({V:T=None; Val v}, loc)"
    by(rule Block_None_\<tau>red1r_xt)
  thus ?case using V lenxs by(auto elim!: rtranclp.rtrancl_into_rtrancl intro: Red1Block \<tau>move1BlockRed)
next
  case (bisim1TryCatch2 e2 n e' xs loc pc e C V)
  from \<open>\<B> (try e catch(C V) e2) n\<close> have [simp]: "n = V" and "\<B> e2 (Suc n)" by auto
  note len = \<open>n + max_vars {V:Class C=None; e'} \<le> length xs\<close>
  hence V: "V < length xs" by simp
  from \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> ([v], loc, pc, None)\<close>
  have lenxs: "length xs = length loc" by(auto dest: bisim1_length_xs)
  note IH = \<open>\<lbrakk>pc = length (compE2 e2); Suc n + max_vars e' \<le> length xs; \<B> e2 (Suc n)\<rbrakk>
             \<Longrightarrow> \<tau>red1r P t h (e', xs) (Val v, loc)\<close>
  with len \<open>Suc (Suc (length (compE2 e) + pc)) = length (compE2 (try e catch(C V) e2))\<close> \<open>\<B> e2 (Suc n)\<close>
  have "\<tau>red1r P t h (e', xs) (Val v, loc)" by(simp)
  hence "\<tau>red1r P t h ({V:Class C=None; e'}, xs) ({V:Class C=None; Val v}, loc)"
    by(rule Block_None_\<tau>red1r_xt)
  thus ?case using V lenxs by(auto elim!: rtranclp.rtrancl_into_rtrancl intro: Red1Block \<tau>move1BlockRed)
next
  case (bisims1List1 e n e' xs loc es)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs, loc, length (compEs2 (e # es)), None)\<close>
  then have es: "es = []" and pc: "length (compEs2 (e # es)) = length (compE2 e)"
    by(auto dest: bisim1_pc_length_compE2)
  with bisim obtain val where stk: "rev vs = [val]" and e': "is_val e' \<Longrightarrow> e' = Val val"
    by(auto dest: bisim1_pc_length_compE2D)
  with es pc bisims1List1 have "\<tau>red1r P t h (e', xs) (Val val, loc)" by simp
  with stk es show ?case by(auto intro: \<tau>red1r_inj_\<tau>reds1r)
next
  case (bisims1List2 es n es' xs stk loc pc e v)
  from \<open>stk @ [v] = rev vs\<close> obtain vs' where vs: "vs = v # vs'" by(cases vs) auto
  with bisims1List2 show ?case by(auto intro: \<tau>reds1r_cons_\<tau>reds1r)
qed(fastforce dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2)+

lemma exec_meth_stk_split:
  "\<lbrakk> P,E,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp);
     exec_meth_d (compP2 P) (compE2 E) (stack_xlift (length STK) (compxE2 E 0 0)) t
                h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<rbrakk>
  \<Longrightarrow> \<exists>stk''. stk' = stk'' @ STK \<and> exec_meth_d (compP2 P) (compE2 E) (compxE2 E 0 0) t
                                             h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
  (is "\<lbrakk> _; ?exec E stk STK loc pc xcp stk' loc' pc' xcp' \<rbrakk> \<Longrightarrow> ?concl E stk STK loc pc xcp stk' loc' pc' xcp'")

  and exec_meth_stk_splits:
  "\<lbrakk> P,Es,h \<turnstile> (es,xs) [\<leftrightarrow>] (stk,loc,pc,xcp);
     exec_meth_d (compP2 P) (compEs2 Es) (stack_xlift (length STK) (compxEs2 Es 0 0)) t
                h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<rbrakk>
  \<Longrightarrow> \<exists>stk''. stk' = stk'' @ STK \<and> exec_meth_d (compP2 P) (compEs2 Es) (compxEs2 Es 0 0) t
                                             h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
  (is "\<lbrakk> _; ?execs Es stk STK loc pc xcp stk' loc' pc' xcp' \<rbrakk> \<Longrightarrow> ?concls Es stk STK loc pc xcp stk' loc' pc' xcp'")
proof(induct E "n :: nat" e xs stk loc pc xcp and Es "n :: nat" es xs stk loc pc xcp
    arbitrary: stk' loc' pc' xcp' STK and stk' loc' pc' xcp' STK rule: bisim1_bisims1_inducts_split)
  case bisim1InSync thus ?case by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
next
  case bisim1Val2 thus ?case by(auto dest: exec_meth_length_compE2_stack_xliftD)
next
  case bisim1New thus ?case
    by (fastforce elim: exec_meth.cases intro: exec_meth.intros split: if_split_asm cong del: image_cong_simp)
next
  case bisim1NewThrow thus ?case by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1NewArray e n e' xs stk loc pc xcp T)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (newA T\<lfloor>e\<rceil>) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis
      apply simp
      apply (erule exec_meth.cases)
       apply (auto 4 4 intro: exec_meth.intros split: if_split_asm cong del: image_cong_simp)
      done
  qed
next
  case (bisim1NewArrayThrow e n a xs stk loc pc T)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (newA T\<lfloor>e\<rceil>) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1NewArrayFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1Cast e n e' xs stk loc pc xcp T)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (Cast T e) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case (bisim1CastThrow e n a xs stk loc pc T)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (Cast T e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1CastFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1InstanceOf e n e' xs stk loc pc xcp T)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e instanceof T) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case (bisim1InstanceOfThrow e n a xs stk loc pc T)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e instanceof T) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1Val thus ?case by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1Var thus ?case by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec e2 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e1)" by simp
    with exec have "pc' \<ge> length (compE2 e1)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto split: bop.splits elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 e1)"
      by -(rule_tac PC34="pc' - length (compE2 e1)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2)
   (stack_xlift (length STK) (compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0))) t h (stk @ STK, loc, length (compE2 e1) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec e2 [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e1)) xcp'"
      using \<open>stk = [v]\<close> \<open>xcp = None\<close>
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop])
        (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v]) (compxE2 e2 0 0))) t h
        ([] @ [v], loc, length (compE2 e1) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e1) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using \<open>stk = [v]\<close> \<open>xcp = None\<close> stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) STK loc (length (compE2 e1) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop])
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))) t
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e2 stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 e1)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e1), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e1) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop]) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e1) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 e1)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis 
      by(fastforce elim: exec_meth.cases split: sum.split_asm intro!: exec_meth.intros)
  qed
next
  case (bisim1BinOpThrow1 e1 n a xs stk loc pc e2 bop)
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e1 @ (compE2 e2 @ [BinOpInstr bop]))
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1BinOpThrow2 e2 n a xs stk loc pc e1 bop v1)
  note bisim2 = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) STK loc (length (compE2 e1) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop])
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))))
     t h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2)
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))) t
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec e2 stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e1)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop]) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e1)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1BinOpThrow thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1LAss1 e n e' xs stk loc pc xcp V)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (V := e) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros)
  qed
next
  case (bisim1LAss2 e n xs V)
  thus ?case by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1LAssThrow e n a xs stk loc pc V)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (V := e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec i [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec (a\<lfloor>i\<rceil>) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by simp
    with exec have "pc' \<ge> length (compE2 a)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 a)"
      by -(rule_tac PC34="pc' - length (compE2 a)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth_d (compP2 P) (compE2 a @ compE2 i)
   (stack_xlift (length STK) (compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0))) t h (stk @ STK, loc, length (compE2 a) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec i [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 a)) xcp'"
      using \<open>stk = [v]\<close> \<open>xcp = None\<close>
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ [ALoad])
        (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) t h
        ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 a) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using \<open>stk = [v]\<close> \<open>xcp = None\<close> stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v1)
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec (a\<lfloor>i\<rceil>) (stk @ [v1]) STK loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ [ALoad])
      (stack_xlift (length STK) (compxE2 a 0 0) @ shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i) (stack_xlift (length STK) (compxE2 a 0 0) @
      shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))) t
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec i stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 a)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) t h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) (compE2 a @ compE2 i) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v1]) (compxE2 i 0 0))) t h (stk @ [v1], loc, length (compE2 a) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v1]) (compxE2 i 0 0))) t h (stk @ [v1], loc, length (compE2 a) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis
      by(clarsimp)(erule exec_meth.cases, auto intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case (bisim1AAccThrow1 A n a xs stk loc pc i)
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (A\<lfloor>i\<rceil>) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 A)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 A @ (compE2 i @ [ALoad]))
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1AAccThrow2 i n a xs stk loc pc A v1)
  note bisim2 = \<open>P,i,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (A\<lfloor>i\<rceil>) (stk @ [v1]) STK loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc < length (compE2 i)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ [ALoad])
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth_d (compP2 P) (compE2 A @ compE2 i)
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))) t
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec i stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) t h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 A @ compE2 i) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) t h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ [ALoad]) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) t h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1AAccFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec i [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length STK) (compxE2 a 0 0) @ shift (length (compE2 a)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0) @ compxE2 e (length (compE2 i)) (Suc (Suc 0))))) t
    h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec' have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'" by(rule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by simp
    with exec' have "pc' \<ge> length (compE2 a)" by -(erule exec_meth_drop_xt_pc, auto)
    then obtain PC where PC: "pc' = PC + length (compE2 a)"
      by -(rule_tac PC34="pc' - length (compE2 a)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec PC pc
    have "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length STK) (compxE2 a 0 0 @ shift (length (compE2 a)) (compxE2 i 0 (Suc 0))) @ shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (length STK + Suc (Suc 0)))) t
    h (v # STK, loc, length (compE2 a) + 0, None) ta h' (stk', loc', length (compE2 a) + PC, xcp')" 
      by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
    hence "exec_meth_d (compP2 P) (compE2 a @ compE2 i)
   (stack_xlift (length STK) (compxE2 a 0 0 @ shift (length (compE2 a)) (compxE2 i 0 (Suc 0)))) t h (v # STK, loc, length (compE2 a) + 0, None) ta h' (stk', loc', length (compE2 a) + PC, xcp')"
      by(rule exec_meth_take_xt) simp
    hence "?exec i [] (v # STK) loc 0 None stk' loc' ((length (compE2 a) + PC) - length (compE2 a)) xcp'"
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ (compE2 e @ [AStore, Push Unit]))
        ((compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) @
         shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h
        ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 a) + PC, xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using \<open>stk = [v]\<close> \<open>xcp = None\<close> stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v)
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH3 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec e [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) (stk @ [v]) STK loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "\<And>v'. exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 (length STK) @ shift (length (compE2 a)) (stack_xlift (length (v # STK)) (compxE2 i 0 0))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v' # v # STK)) (compxE2 e 0 0))) t
    h (stk @ v # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True with exec'[of arbitrary]
    have exec'': "exec_meth_d (compP2 P) (compE2 a @ compE2 i) (compxE2 a 0 (length STK) @ shift (length (compE2 a)) (stack_xlift (length (v # STK)) (compxE2 i 0 0))) t h (stk @ v # STK, loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by-(erule exec_meth_take_xt, simp)
    hence "?exec i stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 a)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and exec''': "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')" by blast
    from exec''' have "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) @ shift (length (compE2 a @ compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    moreover from exec'' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using stk' by(auto simp add: shift_compxE2 stack_xlift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 i)" by simp
    with exec'[of arbitrary] have "pc' \<ge> length (compE2 a @ compE2 i)"
      by-(erule exec_meth_drop_xt_pc, auto simp add: shift_compxE2 stack_xlift_compxE2)
    then obtain PC where PC: "pc' = PC + length (compE2 a) + length (compE2 i)"
      by -(rule_tac PC34="pc' - length (compE2 a @ compE2 i)" in that, simp)
    from pc bisim2 obtain v' where stk: "stk = [v']" and xcp: "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    from exec'[of v'] 
    have "exec_meth_d (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length (v' # v # STK)) (compxE2 e 0 0)) t
                    h (v' # v # STK, loc, 0, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding stk pc append_Cons append_Nil
      by -(rule exec_meth_drop_xt, simp only: add_0_right length_append, auto simp add: shift_compxE2 stack_xlift_compxE2)
    with PC xcp have "?exec e [] (v' # v # STK) loc 0 None stk' loc' PC xcp'"
      by -(rule exec_meth_take,auto)
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v' # v # STK"
      and "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')"  by auto
    hence "exec_meth_d (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v', v]) (compxE2 e 0 0))) t h ([] @ [v', v], loc, length (compE2 a @ compE2 i) + 0, None) ta h' (stk'' @ [v', v], loc', length (compE2 a @ compE2 i) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    thus ?thesis using stk xcp stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc xcp a i v1 v2)
  note IH3 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) (stk @ [v2, v1]) STK loc (length (compE2 a) + length (compE2 i) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim3 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have "exec_meth_d (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit])
      ((compxE2 a 0 (length STK) @ compxE2 i (length (compE2 a)) (Suc (length STK))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0))) t
      h (stk @ v2 # v1 # STK, loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2)
    hence exec': "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e)
      ((compxE2 a 0 (length STK) @ compxE2 i (length (compE2 a)) (Suc (length STK))) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0))) t
      h (stk @ v2 # v1 # STK, loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "?exec e stk (v2 # v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 a @ compE2 i)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v2, v1]) (compxE2 e 0 0)) t h (stk @ [v2, v1], loc, pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) t
      h (stk @ [v2, v1], loc, length (compE2 a @ compE2 i) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 a @ compE2 i) + (pc' - length (compE2 a @ compE2 i)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) (((compE2 a @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) t
      h (stk @ [v2, v1], loc, length (compE2 a @ compE2 i) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 a @ compE2 i) + (pc' - length (compE2 a @ compE2 i)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with bisim3 obtain v3 where [simp]: "stk = [v3]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case (bisim1AAssThrow1 A n a xs stk loc pc i e)
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 A)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 A @ (compE2 i @ compE2 e @ [AStore, Push Unit]))
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0) @ compxE2 e (length (compE2 i)) (Suc (Suc 0))))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec A stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1AAssThrow2 i n a xs stk loc pc A e v1)
  note bisim2 = \<open>P,i,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl i stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) (stk @ [v1]) STK loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc < length (compE2 i)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ compE2 e @ [AStore, Push Unit])
     ((stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) @ (shift (length (compE2 A @ compE2 i)) (compxE2 e 0 (Suc (Suc (length STK)))))) t
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  hence exec': "exec_meth_d (compP2 P) (compE2 A @ compE2 i)
     (stack_xlift (length STK) (compxE2 A 0 0) @ shift (length (compE2 A)) (stack_xlift (length STK) (compxE2 i 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take_xt)(simp add: pc)
  hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length STK) (compxE2 i 0 (Suc 0))) t
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec i stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 i) (compxE2 i 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v1]) (compxE2 i 0 0)) t 
      h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 A), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 A @ compE2 i) (compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) t 
      h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 A 0 0 @ shift (length (compE2 A)) (stack_xlift (length [v1]) (compxE2 i 0 0))) @ (shift (length (compE2 A @ compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) t
      h (stk @ [v1], loc, length (compE2 A) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 A) + (pc' - length (compE2 A)), xcp')"
    by(rule exec_meth_append_xt)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case (bisim1AAssThrow3 e n a xs stk loc pc A i v2 v1)
  note bisim3 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH3 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) (stk @ [v2, v1]) STK loc (length (compE2 A) + length (compE2 i) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim3 have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (((compE2 A @ compE2 i) @ compE2 e) @ [AStore, Push Unit])
     ((stack_xlift (length STK) (compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0))) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0))) t
     h (stk @ v2 # v1 # STK, loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  hence exec': "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ compE2 e)
     ((stack_xlift (length STK) (compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0))) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e 0 0))) t
     h (stk @ v2 # v1 # STK, loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "?exec e stk (v2 # v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 A @ compE2 i)) xcp'"
    by(rule exec_meth_drop_xt) auto
  from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 A @ compE2 i), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v2, v1]) (compxE2 e 0 0)) t h (stk @ [v2, v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 A @ compE2 i), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) ((compE2 A @ compE2 i) @ compE2 e) ((compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0)) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) t h (stk @ [v2, v1], loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 A @ compE2 i) + (pc' - length (compE2 A @ compE2 i)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) (((compE2 A @ compE2 i) @ compE2 e) @ [AStore, Push Unit]) ((compxE2 A 0 0 @ compxE2 i (length (compE2 A)) (Suc 0)) @ shift (length (compE2 A @ compE2 i)) (stack_xlift (length [v2, v1]) (compxE2 e 0 0))) t h (stk @ [v2, v1], loc, length (compE2 A @ compE2 i) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 A @ compE2 i) + (pc' - length (compE2 A @ compE2 i)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 A @ compE2 i)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1AAssFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1AAss4 thus ?case
    by -(erule exec_meth.cases, auto intro!: exec_meth.exec_instr)
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note bisim = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec a stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl a stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (a\<bullet>length) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have "?exec a stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 a)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(auto intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case (bisim1ALengthThrow e n a xs stk loc pc)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e\<bullet>length) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1ALengthNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1FAcc e n e' xs stk loc pc xcp F D)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e\<bullet>F{D}) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where [simp]: "stk = [v]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec show ?thesis apply(simp)
      by(erule exec_meth.cases)(fastforce intro!: exec_meth.intros simp add: is_Ref_def split: if_split_asm)+
  qed
next
  case (bisim1FAccThrow e n a xs stk loc pc F D)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e\<bullet>F{D}) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp)(erule exec_meth_take[OF _ pc])
  from IH[OF this] show ?case by(auto)
next
  case bisim1FAccNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec e2 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec (e\<bullet>F{D} := e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxE2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with exec have "pc' \<ge> length (compE2 e)"
      by(simp add: compxE2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 e)"
      by -(rule_tac PC34="pc' - length (compE2 e)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have "exec_meth_d (compP2 P) (compE2 e @ compE2 e2)
      (stack_xlift (length STK) (compxE2 e 0 0 @ compxE2 e2 (length (compE2 e)) (Suc 0))) t 
      h (stk @ STK, loc, length (compE2 e) + 0, xcp) ta h' (stk', loc', pc', xcp')"
      by-(rule exec_meth_take, auto)
    hence "?exec e2 [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e)) xcp'"
      using \<open>stk = [v]\<close> \<open>xcp = None\<close>
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth_d (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
        (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) t h
        ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using \<open>stk = [v]\<close> \<open>xcp = None\<close> stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e F D v1)
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec (e\<bullet>F{D} := e2) (stk @ [v1]) STK loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have "exec_meth_d (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
      (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
    hence exec': "exec_meth_d (compP2 P) (compE2 e @ compE2 e2) (stack_xlift (length STK) (compxE2 e 0 0) @
      shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
      h (stk @ v1 # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))) t
      h (stk @ v1 # STK, loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e2 stk (v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 e)) xcp'"
      by(simp add: compxE2_stack_xlift_convs)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, xcp)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) (compE2 e @ compE2 e2) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e) + pc, xcp)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where [simp]: "stk = [v2]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(fastforce intro!: exec_meth.intros split: if_split_asm)+
  qed
next
  case (bisim1FAssThrow1 e n a xs stk loc pc e2 F D)
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e\<bullet>F{D} := e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 e)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e @ (compE2 e2 @ [Putfield F D, Push Unit]))
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1FAssThrow2 e2 n a xs stk loc pc e F D v1)
  note bisim2 = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e\<bullet>F{D} := e2) (stk @ [v1]) STK loc (length (compE2 e) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit])
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth_d (compP2 P) (compE2 e @ compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))) t
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec e2 stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 e @ compE2 e2) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) ((compE2 e @ compE2 e2) @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h (stk @ [v1], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1FAssNull thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1FAss3 thus ?case
    by -(erule exec_meth.cases, auto intro!: exec_meth.exec_instr)
next
  case (bisim1CAS1 e1 n e1' xs stk loc pc xcp e2 e3 D F)
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec e2 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec _ stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2 @ compE2 e3 @ [CAS F D]) (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0) @ compxE2 e3 (length (compE2 e2)) (Suc (Suc 0))))) t
    h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec' have "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'" by(rule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e1)" by simp
    with exec' have "pc' \<ge> length (compE2 e1)" by -(erule exec_meth_drop_xt_pc, auto)
    then obtain PC where PC: "pc' = PC + length (compE2 e1)"
      by -(rule_tac PC34="pc' - length (compE2 e1)" in that, simp)
    from pc bisim1 obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec PC pc
    have "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D]) (stack_xlift (length STK) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 0 (Suc 0))) @ shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (length STK + Suc (Suc 0)))) t
    h (v # STK, loc, length (compE2 e1) + 0, None) ta h' (stk', loc', length (compE2 e1) + PC, xcp')" 
      by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
    hence "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2)
   (stack_xlift (length STK) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 0 (Suc 0)))) t h (v # STK, loc, length (compE2 e1) + 0, None) ta h' (stk', loc', length (compE2 e1) + PC, xcp')"
      by(rule exec_meth_take_xt) simp
    hence "?exec e2 [] (v # STK) loc 0 None stk' loc' ((length (compE2 e1) + PC) - length (compE2 e1)) xcp'"
      by -(rule exec_meth_drop_xt, auto simp add: stack_xlift_compxE2 shift_compxE2)
    from IH2[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')" by auto
    hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ (compE2 e3 @ [CAS F D]))
        ((compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v]) (compxE2 e2 0 0))) @
         shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h
        ([] @ [v], loc, length (compE2 e1) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e1) + PC, xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by(auto)
    thus ?thesis using \<open>stk = [v]\<close> \<open>xcp = None\<close> stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1CAS2 e2 n e2' xs stk loc pc xcp e1 e3 D F v)
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH3 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?exec e3 [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e3 [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim3 = \<open>P,e3,h \<turnstile> (e3, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note exec = \<open>?exec _ (stk @ [v]) STK loc (length (compE2 e1) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  from exec have exec': "\<And>v'. exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D]) ((compxE2 e1 0 (length STK) @ shift (length (compE2 e1)) (stack_xlift (length (v # STK)) (compxE2 e2 0 0))) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length (v' # v # STK)) (compxE2 e3 0 0))) t
    h (stk @ v # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True with exec'[of undefined]
    have exec'': "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 (length STK) @ shift (length (compE2 e1)) (stack_xlift (length (v # STK)) (compxE2 e2 0 0))) t h (stk @ v # STK, loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by-(erule exec_meth_take_xt, simp)
    hence "?exec e2 stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 e1)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and exec''': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
    from exec''' have "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D]) ((compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v]) (compxE2 e2 0 0))) @ shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      apply -
      apply(rule exec_meth_append_xt)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    moreover from exec'' have "pc' \<ge> length (compE2 e1)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using stk' by(auto simp add: shift_compxE2 stack_xlift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e2)" by simp
    with exec'[of undefined] have "pc' \<ge> length (compE2 e1 @ compE2 e2)"
      by-(erule exec_meth_drop_xt_pc, auto simp add: shift_compxE2 stack_xlift_compxE2)
    then obtain PC where PC: "pc' = PC + length (compE2 e1) + length (compE2 e2)"
      by -(rule_tac PC34="pc' - length (compE2 e1 @ compE2 e2)" in that, simp)
    from pc bisim2 obtain v' where stk: "stk = [v']" and xcp: "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    from exec'[of v'] 
    have "exec_meth_d (compP2 P) (compE2 e3 @ [CAS F D]) (stack_xlift (length (v' # v # STK)) (compxE2 e3 0 0)) t
                    h (v' # v # STK, loc, 0, xcp) ta h' (stk', loc', pc' - length (compE2 e1 @ compE2 e2), xcp')"
      unfolding stk pc append_Cons append_Nil
      by -(rule exec_meth_drop_xt, simp only: add_0_right length_append, auto simp add: shift_compxE2 stack_xlift_compxE2)
    with PC xcp have "?exec e3 [] (v' # v # STK) loc 0 None stk' loc' PC xcp'"
      by -(rule exec_meth_take,auto)
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v' # v # STK"
      and "exec_meth_d (compP2 P) (compE2 e3) (compxE2 e3 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')"  by auto
    hence "exec_meth_d (compP2 P) (((compE2 e1 @ compE2 e2) @ compE2 e3) @ [CAS F D]) ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length [v', v]) (compxE2 e3 0 0))) t h ([] @ [v', v], loc, length (compE2 e1 @ compE2 e2) + 0, None) ta h' (stk'' @ [v', v], loc', length (compE2 e1 @ compE2 e2) + PC, xcp')"
      apply -
      apply(rule exec_meth_append)
      apply(rule append_exec_meth_xt)
      apply(erule exec_meth_stk_offer)
      by auto
    thus ?thesis using stk xcp stk' pc PC
      by(clarsimp simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  qed
next
  case (bisim1CAS3 e3 n e3' xs stk loc pc xcp e1 e2 D F v1 v2)
  note IH3 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e3 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e3 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim3 = \<open>P,e3,h \<turnstile> (e3', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec _ (stk @ [v2, v1]) STK loc (length (compE2 e1) + length (compE2 e2) + pc) xcp stk' loc' pc' xcp'\<close>
  from bisim3 have pc: "pc \<le> length (compE2 e3)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e3)")
    case True
    from exec have "exec_meth_d (compP2 P) (((compE2 e1 @ compE2 e2) @ compE2 e3) @ [CAS F D])
      ((compxE2 e1 0 (length STK) @ compxE2 e2 (length (compE2 e1)) (Suc (length STK))) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e3 0 0))) t
      h (stk @ v2 # v1 # STK, loc, length (compE2 e1 @ compE2 e2) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2)
    hence exec': "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3)
      ((compxE2 e1 0 (length STK) @ compxE2 e2 (length (compE2 e1)) (Suc (length STK))) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e3 0 0))) t
      h (stk @ v2 # v1 # STK, loc, length (compE2 e1 @ compE2 e2) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "?exec e3 stk (v2 # v1 # STK) loc pc xcp stk' loc' (pc' - length (compE2 e1 @ compE2 e2)) xcp'"
      by(rule exec_meth_drop_xt) auto
    from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e3) (compxE2 e3 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1 @ compE2 e2), xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 e3) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0)) t h (stk @ [v2, v1], loc, pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 e1 @ compE2 e2), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3) ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0))) t
      h (stk @ [v2, v1], loc, length (compE2 e1 @ compE2 e2) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 e1 @ compE2 e2) + (pc' - length (compE2 e1 @ compE2 e2)), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) (((compE2 e1 @ compE2 e2) @ compE2 e3) @ [CAS F D]) ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0))) t
      h (stk @ [v2, v1], loc, length (compE2 e1 @ compE2 e2) + pc, xcp)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 e1 @ compE2 e2) + (pc' - length (compE2 e1 @ compE2 e2)), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length (compE2 e1 @ compE2 e2)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(simp add: stack_xlift_compxE2 shift_compxE2)
  next
    case False
    with pc have pc: "pc = length (compE2 e3)" by simp
    with bisim3 obtain v3 where [simp]: "stk = [v3]" "xcp = None"
      by(auto dest: dest: bisim1_pc_length_compE2D)
    with exec pc show ?thesis apply(simp)
      by(erule exec_meth.cases)(fastforce intro!: exec_meth.intros split: if_split_asm)+
  qed
next
  case (bisim1CASThrow1 e1 n a xs stk loc pc e2 e3 D F)
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec _ stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e1 @ (compE2 e2 @ compE2 e3 @ [CAS F D]))
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0) @ compxE2 e3 (length (compE2 e2)) (Suc (Suc 0))))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'" by(rule exec_meth_take_xt)(rule pc)
  from IH1[OF this] show ?case by(auto)
next
  case (bisim1CASThrow2 e2 n a xs stk loc pc e1 e3 D F v1)
  note bisim2 = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH2 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec _ (stk @ [v1]) STK loc (length (compE2 e1) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D])
     ((stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) @ (shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc (length STK)))))) t
     h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  hence exec': "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2)
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0)))) t
     h (stk @ v1 # STK, loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take_xt)(simp add: pc)
  hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length STK) (compxE2 e2 0 (Suc 0))) t
     h (stk @ v1 # STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  hence "?exec e2 stk (v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e1)) xcp'"
    by(simp add: compxE2_stack_xlift_convs)
  from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t 
      h (stk @ [v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t 
      h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D]) ((compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) @ (shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0))))) t
      h (stk @ [v1], loc, length (compE2 e1) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
    by(rule exec_meth_append_xt)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e1)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case (bisim1CASThrow3 e3 n a xs stk loc pc e1 e2 D F v2 v1)
  note bisim3 = \<open>P,e3,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH3 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e3 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e3 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec _ (stk @ [v2, v1]) STK loc (length (compE2 e1) + length (compE2 e2) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim3 have pc: "pc < length (compE2 e3)" and [simp]: "xs = loc"
    by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (((compE2 e1 @ compE2 e2) @ compE2 e3) @ [CAS F D])
     ((stack_xlift (length STK) (compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0))) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e3 0 0))) t
     h (stk @ v2 # v1 # STK, loc, length (compE2 e1 @ compE2 e2) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  hence exec': "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3)
     ((stack_xlift (length STK) (compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0))) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length (v2 # v1 # STK)) (compxE2 e3 0 0))) t
     h (stk @ v2 # v1 # STK, loc, length (compE2 e1 @ compE2 e2) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "?exec e3 stk (v2 # v1 # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 e1 @ compE2 e2)) xcp'"
    by(rule exec_meth_drop_xt) auto
  from IH3[OF this] obtain stk'' where stk': "stk' = stk'' @ v2 # v1 # STK" and
    exec'': "exec_meth_d (compP2 P) (compE2 e3) (compxE2 e3 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 e1 @ compE2 e2), xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (compE2 e3) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0)) t h (stk @ [v2, v1], loc, pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', pc' - length (compE2 e1 @ compE2 e2), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3) ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0))) t h (stk @ [v2, v1], loc, length (compE2 e1 @ compE2 e2) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 e1 @ compE2 e2) + (pc' - length (compE2 e1 @ compE2 e2)), xcp')"
    by(rule append_exec_meth_xt)(auto)
  hence "exec_meth_d (compP2 P) (((compE2 e1 @ compE2 e2) @ compE2 e3) @ [CAS F D]) ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (stack_xlift (length [v2, v1]) (compxE2 e3 0 0))) t h (stk @ [v2, v1], loc, length (compE2 e1 @ compE2 e2) + pc, \<lfloor>a\<rfloor>)
      ta h' (stk'' @ [v2, v1], loc', length (compE2 e1 @ compE2 e2) + (pc' - length (compE2 e1 @ compE2 e2)), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have pc': "pc' \<ge> length (compE2 e1 @ compE2 e2)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: stack_xlift_compxE2 shift_compxE2)
next
  case bisim1CASFail thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note bisimObj = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IHobj = \<open>\<And>stk' loc' pc' xcp' STK. ?exec obj stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl obj stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IHparams = \<open>\<And>xs stk' loc' pc' xcp' STK. ?execs ps [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (obj\<bullet>M'(ps)) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisimObj have pc: "pc \<le> length (compE2 obj)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 obj)")
    case True
    from exec have "?exec obj stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxEs2_size_convs)(erule exec_meth_take_xt[OF _ True])
    from IHobj[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 obj)" by simp
    with exec have "pc' \<ge> length (compE2 obj)"
      by(simp add: compxEs2_size_convs stack_xlift_compxE2)(auto elim!: exec_meth_drop_xt_pc)
    then obtain PC where PC: "pc' = PC + length (compE2 obj)"
      by -(rule_tac PC34="pc' - length (compE2 obj)" in that, simp)
    from pc bisimObj obtain v where [simp]: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    show ?thesis
    proof(cases ps)
      case Cons
      with exec pc have "exec_meth_d (compP2 P) (compE2 obj @ compEs2 ps)
        (stack_xlift (length STK) (compxE2 obj 0 0 @ compxEs2 ps (length (compE2 obj)) (Suc 0))) t
        h (stk @ STK, loc, length (compE2 obj) + 0, xcp) ta h' (stk', loc', pc', xcp')"
        by -(rule exec_meth_take, auto)
      hence "?execs ps [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 obj)) xcp'"
        apply -
        apply(rule exec_meth_drop_xt)
        apply(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
        apply(auto simp add: stack_xlift_compxE2)
        done
      from IHparams[OF this] PC obtain stk'' where stk': "stk' = stk'' @ v # STK"
        and exec': "exec_meth_d (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', PC, xcp')"
        by auto
      from exec' have "exec_meth_d (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)]) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t h ([] @ [v], loc, length (compE2 obj) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 obj) + PC, xcp')"
        apply -
        apply(rule exec_meth_append)
        apply(rule append_exec_meth_xt)
        apply(erule exec_meth_stk_offer)
        by(auto)
      thus ?thesis using stk' PC by(clarsimp simp add: shift_compxEs2 stack_xlift_compxEs2 ac_simps)
    next
      case Nil
      with exec pc show ?thesis 
        apply(auto elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta split: if_split_asm)
        apply(auto split: extCallRet.split_asm intro!: exec_meth.intros)
        apply(force intro!: exI)
        apply(force intro!: exI)
        apply(force intro!: exI)
        done
    qed
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note bisimParam = \<open>P,ps,h \<turnstile> (ps',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)\<close>
  note IHparam = \<open>\<And>stk' loc' pc' xcp' STK. ?execs ps stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (obj\<bullet>M'(ps)) (stk @ [v]) STK loc (length (compE2 obj) + pc) xcp stk' loc' pc' xcp'\<close>
  show ?case
  proof(cases ps)
    case Nil
    with bisimParam have "pc = 0" "xcp = None" by(auto elim: bisims1.cases)
    with exec Nil show ?thesis 
      apply(auto elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta extRet2JVM_def split: if_split_asm)
      apply(auto split: extCallRet.split_asm simp add: neq_Nil_conv)
      apply(force intro!: exec_meth.intros)+
      done
  next
    case Cons
    from bisimParam have pc: "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
    show ?thesis
    proof(cases "pc < length (compEs2 ps)")
      case True
      from exec have "exec_meth_d (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
        (stack_xlift (length STK) (compxE2 obj 0 0) @ shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0))) t
        h (stk @ v # STK, loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
        by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
      hence exec': "exec_meth_d (compP2 P) (compE2 obj @ compEs2 ps) (stack_xlift (length STK) (compxE2 obj 0 0) @
        shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0))) t
        h (stk @ v # STK, loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
        by(rule exec_meth_take)(simp add: True)
      hence "?execs ps stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 obj)) xcp'"
        by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
      from IHparam[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
        and exec'': "exec_meth_d (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')" by blast
      from exec'' have "exec_meth_d (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk'' @ [v], loc', pc' - length (compE2 obj), xcp')"
        by(rule exec_meth_stk_offer)
      hence "exec_meth_d (compP2 P) (compE2 obj @ compEs2 ps) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t
 h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
        by(rule append_exec_meth_xt) auto
      hence "exec_meth_d (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t
 h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
        by(rule exec_meth_append)
      moreover from exec' have "pc' \<ge> length (compE2 obj)"
        by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
      ultimately show ?thesis using stk'
        by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
    next
      case False
      with pc have pc: "pc = length (compEs2 ps)" by simp
      with bisimParam obtain vs where "stk = vs" "length vs = length ps" "xcp = None"
        by(auto dest: bisims1_pc_length_compEs2D)
      with exec pc Cons show ?thesis
        apply(auto elim!: exec_meth.cases intro!: exec_meth.intros simp add: split_beta extRet2JVM_def split: if_split_asm)
        apply(auto simp add: neq_Nil_conv split: extCallRet.split_asm)
        apply(force intro!: exec_meth.intros)+
        done
    qed
  qed
next
  case (bisim1CallThrowObj obj n a xs stk loc pc ps M')
  note bisim = \<open>P,obj,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (obj\<bullet>M'(ps)) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have "pc < length (compE2 obj)" and [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  with exec have "?exec obj stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)(erule exec_meth_take_xt)
  from IH[OF this] show ?case by auto
next
  case (bisim1CallThrowParams ps n vs a ps' xs stk loc pc obj M' v)
  note bisim = \<open>P,ps,h \<turnstile> (map Val vs @ Throw a # ps',xs) [\<leftrightarrow>] (stk,loc,pc,\<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?execs ps stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concls ps stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (obj\<bullet>M'(ps)) (stk @ [v]) STK loc (length (compE2 obj) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compEs2 ps)" "loc = xs" by(auto dest: bisims1_ThrowD)
  from exec have "exec_meth_d (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (stack_xlift (length STK) (compxE2 obj 0 0) @ shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0))) t
     h (stk @ v # STK, loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence exec': "exec_meth_d (compP2 P) (compE2 obj @ compEs2 ps) (stack_xlift (length STK) (compxE2 obj 0 0) @
      shift (length (compE2 obj)) (stack_xlift (length (v # STK)) (compxEs2 ps 0 0))) t
     h (stk @ v # STK, loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  hence "?execs ps stk (v # STK) loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length (compE2 obj)) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
    and exec'': "exec_meth_d (compP2 P) (compEs2 ps) (compxEs2 ps 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t
     h (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>) ta h' (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
    apply - 
    apply(rule exec_meth_append)
    apply(rule append_exec_meth_xt)
    apply(erule exec_meth_stk_offer)
    apply auto
    done
  moreover from exec' have "pc' \<ge> length (compE2 obj)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
next
  case bisim1CallThrow thus ?case
    by(auto elim!: exec_meth.cases dest: match_ex_table_pcsD simp add: stack_xlift_compxEs2 stack_xlift_compxE2)
next
  case bisim1BlockSome1 thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1BlockSome2 thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1BlockSome4 e n e' xs stk loc pc xcp V T v)
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec {V:T=\<lfloor>v\<rfloor>; e} stk STK loc (Suc (Suc pc)) xcp stk' loc' pc' xcp'\<close>
  hence exec': "exec_meth_d (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (stack_xlift (length STK) (compxE2 e 0 0))) t h (stk @ STK, loc, length [Push v, Store V] + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc xcp stk' loc' (pc' - length [Push v, Store V]) xcp'"
    by(rule exec_meth_drop) auto
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta
      h' (stk'', loc', pc' - length [Push v, Store V], xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (compxE2 e 0 0)) t h (stk, loc, length [Push v, Store V] + pc, xcp) ta h' (stk'', loc', length [Push v, Store V] + (pc' - length [Push v, Store V]), xcp')"
    by(rule append_exec_meth) auto
  moreover from exec' have "pc' \<ge> length [Push v, Store V]"
    by(rule exec_meth_drop_pc)(auto simp add: stack_xlift_compxE2)
  hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by(simp)
  ultimately show ?case using stk' by(auto simp add: compxE2_size_convs)
next
  case (bisim1BlockThrowSome e n a xs stk loc pc V T v)
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec {V:T=\<lfloor>v\<rfloor>; e} stk STK loc (Suc (Suc pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  hence exec': "exec_meth_d (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (stack_xlift (length STK) (compxE2 e 0 0))) t h (stk @ STK, loc, length [Push v, Store V] + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length [Push v, Store V]) xcp'"
    by(rule exec_meth_drop) auto
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta
      h' (stk'', loc', pc' - length [Push v, Store V], xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) ([Push v, Store V] @ compE2 e)
     (shift (length [Push v, Store V]) (compxE2 e 0 0)) t h (stk, loc, length [Push v, Store V] + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length [Push v, Store V] + (pc' - length [Push v, Store V]), xcp')"
    by(rule append_exec_meth) auto
  moreover from exec' have "pc' \<ge> length [Push v, Store V]"
    by(rule exec_meth_drop_pc)(auto simp add: stack_xlift_compxE2)
  hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by(simp)
  ultimately show ?case using stk' by(auto simp add: compxE2_size_convs)
next
  case bisim1BlockNone thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case bisim1BlockThrowNone thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Sync1 e1 n e1' xs stk loc pc xcp e2 V)
  note bisim = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    from exec have "exec_meth_d (compP2 P)
      (compE2 e1 @ (Dup # Store V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc]))
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 3 0) @
       stack_xlift (length STK) [(3, 3 + length (compE2 e2), None, 6 + length (compE2 e2), 0)])) t
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
    hence "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec': "exec_meth_d (compP2 P) (compE2 e1) (compxE2 e1 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
      by blast
    from exec' have "exec_meth_d (compP2 P) (compE2 e1 @ (Dup # Store V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc]))
      (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 3 0 @ [(3, 3 + length (compE2 e2), None, 6 + length (compE2 e2), 0)])) t
      h (stk, loc, pc, xcp) ta h' (stk'', loc', pc', xcp')"
      by(rule exec_meth_append_xt)
    thus ?thesis using stk' by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    thus ?thesis using exec by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case bisim1Sync2 thus ?case
    by(fastforce elim!: exec_meth.cases intro!: exec_meth.intros)
next
  case bisim1Sync3 thus ?case
    by(fastforce elim!: exec_meth.cases intro!: exec_meth.intros split: if_split_asm)
next
  case (bisim1Sync4 e2 n e2' xs stk loc pc xcp e1 V a)
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    let ?pre = "compE2 e1 @ [Dup, Store V, MEnter]"
    from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e2 0 0) @
      [(0, length (compE2 e2), None, 3 + length (compE2 e2), length STK)])) t
     h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 eval_nat_numeral ac_simps)
    hence exec'': "exec_meth_d (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
      (stack_xlift (length STK) (compxE2 e2 0 0) @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), length STK)]) t
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_drop_xt[where n=1])(auto simp add: stack_xlift_compxE2)
    from exec' have pc': "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc[where n'=1])(auto simp add: stack_xlift_compxE2)
    hence pc'': "(Suc (Suc (Suc (pc' - Suc (Suc (Suc 0)))))) = pc'" by simp
    show ?thesis
    proof(cases xcp)
      case None
      from exec'' None True
      have "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
        apply -
        apply (erule exec_meth.cases)
        apply (cases "compE2 e2 ! pc")
                            apply (fastforce simp add: is_Ref_def intro: exec_meth.intros split: if_split_asm cong del: image_cong_simp)+
        done
      from IH[OF this] obtain stk'' where stk: "stk' = stk'' @ STK"
        and exec''': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length ?pre, xcp')" by blast
      from exec''' have "exec_meth_d (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
      (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)]) t
     h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')"
        by(rule exec_meth_append_xt)
      hence "exec_meth_d (compP2 P) (?pre @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
      (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)])) t
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
        by(rule append_exec_meth_xt[where n=1]) auto
      thus ?thesis using stk pc' pc'' by(simp add: eval_nat_numeral shift_compxE2 ac_simps)
    next
      case (Some a)
      with exec'' have [simp]: "h' = h" "xcp' = None" "loc' = loc" "ta = \<epsilon>"
        by(auto elim!: exec_meth.cases simp add: match_ex_table_append
           split: if_split_asm dest!: match_ex_table_stack_xliftD)
      show ?thesis
      proof(cases "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 e2 0 0)")
        case None
        with Some exec'' True have [simp]: "stk' = Addr a # STK"
          and pc': "pc' = length (compE2 e1) + length (compE2 e2) + 6"
          by(auto elim!: exec_meth.cases simp add: match_ex_table_append
                  split: if_split_asm dest!: match_ex_table_stack_xliftD)
        with exec'' Some None
        have "exec_meth_d (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
        (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)]) t
        h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc, pc' - length ?pre, None)"
          by -(rule exec_catch, auto elim!: exec_meth.cases simp add: match_ex_table_append matches_ex_entry_def
                                     split: if_split_asm dest!: match_ex_table_stack_xliftD)
        hence "exec_meth_d (compP2 P) (?pre @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
        (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)])) t
        h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc,
        length ?pre + (pc' - length ?pre), None)"
          by(rule append_exec_meth_xt[where n=1]) auto
        with pc' Some show ?thesis by(simp add: eval_nat_numeral shift_compxE2 ac_simps)
      next
        case (Some pcd)
        with \<open>xcp = \<lfloor>a\<rfloor>\<close> exec'' True
        have "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t
          h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc' - length ?pre, None)"
          apply -
          apply(rule exec_catch)
          apply(auto elim!: exec_meth.cases simp add: match_ex_table_append split: if_split_asm
                     dest!: match_ex_table_stack_xliftD)
          done
        hence "exec_meth_d (compP2 P) (compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc]) (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)]) t
   h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc' - length ?pre, None)"
          by(rule exec_meth_append_xt)
        hence "exec_meth_d (compP2 P) (?pre @ compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc]) 
              (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)])) t
   h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, length ?pre + (pc' - length ?pre), None)"
          by(rule append_exec_meth_xt[where n=1])(auto)
        moreover from Some \<open>xcp = \<lfloor>a\<rfloor>\<close> exec'' True pc'
        have "pc' = length (compE2 e1) + 3 + fst pcd" "stk' = Addr a # drop (length stk - snd pcd) stk @ STK"
          by(auto elim!: exec_meth.cases dest!: match_ex_table_stack_xliftD simp: match_ex_table_append split: if_split_asm)
        ultimately show ?thesis using \<open>xcp = \<lfloor>a\<rfloor>\<close> by(auto simp add: eval_nat_numeral shift_compxE2 ac_simps)
      qed
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with exec show ?thesis
      by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: if_split_asm simp add: match_ex_table_append_not_pcs eval_nat_numeral)(simp_all add: matches_ex_entry_def)
  qed
next
  case bisim1Sync5 thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros split: if_split_asm)
next
  case bisim1Sync6 thus ?case  
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros split: if_split_asm)     
next
  case bisim1Sync7 thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros split: if_split_asm)
next
  case bisim1Sync8 thus ?case
    by(fastforce elim: exec_meth.cases intro: exec_meth.intros split: if_split_asm)
next
  case (bisim1Sync9 e1 n e2 V a xs)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] STK xs (8 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  let ?pre = "compE2 e1 @ Dup # Store V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ [ThrowExc]) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) @ shift (length ?pre) []) t h (Addr a # STK, xs, length ?pre + 0, None) ta h' (stk', loc', pc', xcp')"
    by(simp add: eval_nat_numeral)
  hence "exec_meth_d (compP2 P) [ThrowExc] [] t h (Addr a # STK, xs, 0, None) ta h' (stk', loc', pc' - length ?pre, xcp')"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  moreover from exec' have "pc' = 8 + length (compE2 e1) + length (compE2 e2)" "stk' = Addr a # STK"
    by(auto elim!: exec_meth.cases)
  ultimately show ?case by(fastforce elim!: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Sync10 e1 n e2 V a xs)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] STK xs (8 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  hence "match_ex_table (compP2 P) (cname_of h a) (8 + length (compE2 e1) + length (compE2 e2)) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0)) \<noteq> None"
    by(rule exec_meth.cases) auto
  hence False by(auto split: if_split_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
  thus ?case ..
next
  case (bisim1Sync11 e1 n e2 V xs)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null] STK xs (Suc (Suc (length (compE2 e1)))) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  hence "match_ex_table (compP2 P) (cname_of h (addr_of_sys_xcpt NullPointer)) (2 + length (compE2 e1)) (stack_xlift (length STK) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0)) \<noteq> None"
    by(rule exec_meth.cases)(auto split: if_split_asm)
  hence False by(auto split: if_split_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
  thus ?case ..
next
  case (bisim1SyncThrow e1 n a xs stk loc pc e2 V)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e1)"
    and [simp]: "loc = xs" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e1 @ Dup # Store V # MEnter # compE2 e2 @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
     (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 3 0) @
      [(3, 3 + length (compE2 e2), None, 6 + length (compE2 e2), length STK)])) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1Seq1 e1 n e1' xs stk loc pc xcp e2)
  note bisim1 = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e1;;e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    from exec have "exec_meth_d (compP2 P) (compE2 e1 @ Pop # compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0))) t
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2)
    hence "?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim1 obtain v where "xcp = None" "stk = [v]" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
  qed
next
  case (bisim1SeqThrow1 e1 n a xs stk loc pc e2)
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e1;;e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e1 @ Pop # compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 stack_xlift_compxE2)
  hence "?exec e1 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by(fastforce elim: exec_meth.cases intro: exec_meth.intros)
next
  case (bisim1Seq2 e2 n e2' xs stk loc pc xcp e1)
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (e1;;e2) stk STK loc (Suc (length (compE2 e1) + pc)) xcp stk' loc' pc' xcp'\<close>
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    from bisim2 have "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec have False by(auto elim: exec_meth.cases)
    thus ?thesis ..
  next
    case True
    from exec have exec':
      "exec_meth_d (compP2 P) ((compE2 e1 @ [Pop]) @ compE2 e2) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1 @ [Pop])) (stack_xlift (length STK) (compxE2 e2 0 0))) t
     h (stk @ STK, loc, length ((compE2 e1) @ [Pop]) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ((compE2 e1) @ [Pop])) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length (compE2 e1 @ [Pop]), xcp')" by auto
    from exec'' have "exec_meth_d (compP2 P) ((compE2 e1 @ [Pop]) @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1 @ [Pop])) (compxE2 e2 0 0)) t
     h (stk, loc, length ((compE2 e1) @ [Pop]) + pc, xcp) ta h' (stk'', loc', length ((compE2 e1) @ [Pop]) + (pc' - length ((compE2 e1) @ [Pop])), xcp')"
      by(rule append_exec_meth_xt) auto
    moreover from exec' have "pc' \<ge> length ((compE2 e1) @ [Pop])"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk' by(auto simp add: shift_compxE2 stack_xlift_compxE2)
  qed
next
  case (bisim1Cond1 e n e' xs stk loc pc xcp e1 e2)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have "exec_meth_d (compP2 P) (compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e1 (Suc 0) 0) @
      stack_xlift (length STK) (compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0))) t
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 ac_simps)
    hence "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1CondThen e1 n e1' xs stk loc pc xcp e e2)
  note bisim = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e1 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e1 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk STK loc (Suc (length (compE2 e) + pc)) xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?pre = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
    from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e1 0 0) @
      shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0)))) t
     h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: stack_xlift_compxE2 shift_compxE2 ac_simps)
    hence "exec_meth_d (compP2 P) (compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (stack_xlift (length STK) (compxE2 e1 0 0) @ shift (length (compE2 e1)) (stack_xlift (length STK) (compxE2 e2 (Suc 0) 0))) t
     h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    hence "?exec e1 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e1) (compxE2 e1 0 0) t h (stk, loc, pc, xcp)
      ta h' (stk'', loc', pc' - length ?pre, xcp')" by blast
    from exec'' have "exec_meth_d (compP2 P) (compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0)) t
     h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_append_xt)
    hence "exec_meth_d (compP2 P) (?pre @ compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
      (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))) t
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule append_exec_meth_xt)(auto)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using stk'
      by(auto simp add: shift_compxE2 stack_xlift_compxE2 ac_simps)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1CondElse e2 n e2' xs stk loc pc xcp e e1)
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk STK loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  from bisim have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)

  let ?pre = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2)
    (stack_xlift (length STK) (compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @
     shift (length ?pre) (stack_xlift (length STK) (compxE2 e2 0 0))) t
    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: stack_xlift_compxE2 shift_compxE2 ac_simps)
  hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2 shift_compxEs2 ac_simps)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp)
    ta h' (stk'', loc', pc' - length ?pre, xcp')" by blast
  from exec'' have "exec_meth_d (compP2 P) (?pre @ compE2 e2)
    ((compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @ shift (length ?pre) (compxE2 e2 0 0)) t
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt)(auto)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk'
    by(auto simp add: shift_compxE2 stack_xlift_compxE2 ac_simps eval_nat_numeral)
next
  case (bisim1CondThrow e n a xs stk loc pc e1 e2)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e1 (Suc 0) 0) @
      stack_xlift (length STK) (compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: stack_xlift_compxE2 shift_compxE2 ac_simps)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1While1 c n e xs)
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec c [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (while (c) e) [] STK xs 0 None stk' loc' pc' xcp'\<close>
  hence "exec_meth_d (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0))) t
     h ([] @ STK, xs, 0, None) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec c [] STK xs 0 None stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt) simp
  from IH[OF this] show ?case by auto
next
  case (bisim1While3 c n c' xs stk loc pc xcp e)
  note bisim = \<open>P,c,h \<turnstile> (c', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec c stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (while (c) e) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 c)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 c)")
    case True
    from exec have "exec_meth_d (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0))) t
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence "?exec c stk STK loc pc xcp stk' loc' pc' xcp'"
      by(rule exec_meth_take_xt)(rule True)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 c)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1While4 e n e' xs stk loc pc xcp c)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (while (c) e) stk STK loc (Suc (length (compE2 c) + pc)) xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
    from exec have "exec_meth_d (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
                   (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0))) t
                    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    hence exec': "exec_meth_d (compP2 P) (?pre @ compE2 e) (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0))) t
                 h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(auto intro: True)
    hence "?exec e stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)      
    from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
      and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
    from exec'' have "exec_meth_d (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t
                     h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule append_exec_meth_xt) auto
    hence "exec_meth_d (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
           (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t
           h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
      by(rule exec_meth_append)
    moreover from exec' have "pc' \<ge> length ?pre"
     by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
   moreover have "-2 + (- int (length (compE2 e)) - int (length (compE2 c))) = - int (length (compE2 c)) + (-2 - int (length (compE2 e)))" by simp
   ultimately show ?thesis using stk'
     by(auto simp add: shift_compxE2 stack_xlift_compxE2 algebra_simps uminus_minus_left_commute)
 next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros)
  qed
next
  case (bisim1While6 c n e xs)
  note exec = \<open>?exec (while (c) e) [] STK xs (Suc (Suc (length (compE2 c) + length (compE2 e)))) None stk' loc' pc' xcp'\<close>
  thus ?case by(rule exec_meth.cases)(simp_all, auto intro!: exec_meth.intros)
next
  case (bisim1While7 c n e xs)
  note exec = \<open>?exec (while (c) e) [] STK xs (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None stk' loc' pc' xcp'\<close>
  thus ?case by(rule exec_meth.cases)(simp_all, auto intro!: exec_meth.intros)
next
  case (bisim1WhileThrow1 c n a xs stk loc pc e)
  note bisim = \<open>P,c,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (while (c) e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 c)" by(auto dest: bisim1_ThrowD)
  from exec have "exec_meth_d (compP2 P) (compE2 c @ IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length (compE2 c)) (stack_xlift (length STK) (compxE2 e (Suc 0) 0))) t
     h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence "?exec c stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(rule exec_meth_take_xt)(rule pc)
  from IH[OF this] show ?case by auto
next
  case (bisim1WhileThrow2 e n a xs stk loc pc c)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (while (c) e) stk STK loc (Suc (length (compE2 c) + pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
  from exec have "exec_meth_d (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
     (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0))) t
    h (stk @ STK, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs)
  hence exec': "exec_meth_d (compP2 P) (?pre @ compE2 e)
    (stack_xlift (length STK) (compxE2 c 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e 0 0))) t
    h (stk @ STK, loc, (length ?pre + pc), \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(auto intro: pc)
  hence "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)      
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t
    h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth_d (compP2 P) ((?pre @ compE2 e) @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit])
    (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t
    h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth_append)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover have "-2 + (- int (length (compE2 e)) - int (length (compE2 c))) = - int (length (compE2 c)) + (-2 - int (length (compE2 e)))" by simp
  ultimately show ?case using stk'
    by(auto simp add: shift_compxE2 stack_xlift_compxE2 algebra_simps uminus_minus_left_commute)
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (throw e) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'" by(auto elim: exec_meth_take)
    from IH[OF this] show ?thesis by auto
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case bisim1Throw2 thus ?case
    apply(auto elim!:exec_meth.cases intro: exec_meth.intros dest!: match_ex_table_stack_xliftD)
    apply(auto intro: exec_meth.intros dest!: match_ex_table_stack_xliftD intro!: exI)
    apply(auto simp add: le_Suc_eq)
    done
next
  case bisim1ThrowNull thus ?case
    apply(auto elim!:exec_meth.cases intro: exec_meth.intros dest!: match_ex_table_stack_xliftD)
    apply(auto intro: exec_meth.intros dest!: match_ex_table_stack_xliftD intro!: exI)
    apply(auto simp add: le_Suc_eq)
    done
next
  case (bisim1ThrowThrow e n a xs stk loc pc)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (throw e) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  with exec have "?exec e stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'"
    by(auto elim: exec_meth_take simp add: compxE2_size_convs)
  from IH[OF this] show ?case by auto
next
  case (bisim1Try e n e' xs stk loc pc xcp e2 C' V)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (try e catch(C' V) e2) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) (compE2 e @ Goto (int (length (compE2 e2)) + 2) # Store V # compE2 e2)
      (stack_xlift (length STK) (compxE2 e 0 0) @  shift (length (compE2 e)) (stack_xlift (length STK) (compxE2 e2 (Suc (Suc 0)) 0)) @ [(0, length (compE2 e), \<lfloor>C'\<rfloor>, Suc (length (compE2 e)), length STK)]) t
      h (stk @ STK, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs)
    show ?thesis
    proof(cases xcp)
      case None
      with exec' True have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
        apply -
        apply (erule exec_meth.cases)
        apply (cases "compE2 e ! pc")
        apply (fastforce simp add: is_Ref_def intro: exec_meth.intros split: if_split_asm cong del: image_cong_simp)+
        done
      from IH[OF this] show ?thesis by auto
    next
      case (Some a)
      with exec' have [simp]: "h' = h" "loc' = loc" "xcp' = None" "ta = \<epsilon>"
        by(auto elim: exec_meth.cases)
      show ?thesis
      proof(cases "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 e 0 0)")
        case (Some pcd)
        from exec \<open>xcp = \<lfloor>a\<rfloor>\<close> Some pc
        have stk': "stk' = Addr a # (drop (length stk - snd pcd) stk) @ STK"
          by(auto elim!: exec_meth.cases simp add: match_ex_table_append split: if_split_asm dest!: match_ex_table_stack_xliftD)
        from exec' \<open>xcp = \<lfloor>a\<rfloor>\<close> Some pc have "exec_meth_d (compP2 P)
          (compE2 e) (stack_xlift (length STK) (compxE2 e 0 0)) t h (stk @ STK, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # (drop (length (stk @ STK) - (snd pcd + length STK)) (stk @ STK)), loc, pc', None)"
          apply -
          apply(rule exec_meth.intros)
          apply(auto elim!: exec_meth.cases simp add: match_ex_table_append split: if_split_asm dest!: match_ex_table_shift_pcD match_ex_table_stack_xliftD)
          done
        from IH[unfolded \<open>ta = \<epsilon>\<close> \<open>xcp = \<lfloor>a\<rfloor>\<close> \<open>h' = h\<close>, OF this]
        have stk: "Addr a # drop (length stk - snd pcd) (stk @ STK) = Addr a # drop (length stk - snd pcd) stk @ STK"
          and exec'': "exec_meth_d (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - snd pcd) stk, loc, pc', None)" by auto
        thus ?thesis using Some stk' \<open>xcp = \<lfloor>a\<rfloor>\<close> by(auto)
      next
        case None
        with Some exec pc have stk': "stk' = Addr a # STK"
          and pc': "pc' = Suc (length (compE2 e))"
          and subcls: "compP2 P \<turnstile> cname_of h a \<preceq>\<^sup>* C'"
          by(auto elim!: exec_meth.cases split: if_split_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
        moreover from Some True None pc' subcls
        have "exec_meth_d (compP2 P) (compE2 (try e catch(C' V) e2)) (compxE2 (try e catch(C' V) e2) 0 0) t h
          (stk, loc, pc, \<lfloor>a\<rfloor>) \<epsilon> h (Addr a # drop (length stk - 0) stk, loc, pc', None)"
          by -(rule exec_catch,auto simp add: match_ex_table_append_not_pcs matches_ex_entry_def)
        ultimately show ?thesis using Some by auto
      qed
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    from bisim obtain v where "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec show ?thesis by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: if_split_asm)
  qed
next
  case bisim1TryCatch1 thus ?case
    by(auto elim!: exec_meth.cases intro!: exec_meth.intros split: if_split_asm)
next
  case (bisim1TryCatch2 e2 n e' xs stk loc pc xcp e C' V)
  note bisim = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (try e catch(C' V) e2) stk STK loc (Suc (Suc (length (compE2 e) + pc))) xcp stk' loc' pc' xcp'\<close>
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2)
    (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length ?pre) (stack_xlift (length STK) (compxE2 e2 0 0))) t
    h (stk @ STK, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
  proof(cases)
    case (exec_catch xcp'' d)
    let ?stk = "stk @ STK" and ?PC = "Suc (Suc (length (compE2 e) + pc))"
    note s = \<open>stk' = Addr xcp'' # drop (length ?stk - d) ?stk\<close>
      \<open>ta = \<epsilon>\<close> \<open>h' = h\<close> \<open>xcp' = None\<close> \<open>xcp = \<lfloor>xcp''\<rfloor>\<close> \<open>loc' = loc\<close>
    from \<open>match_ex_table (compP2 P) (cname_of h xcp'') ?PC (stack_xlift (length STK) (compxE2 (try e catch(C' V) e2) 0 0)) = \<lfloor>(pc', d)\<rfloor>\<close> \<open>d \<le> length ?stk\<close>
    show ?thesis unfolding s
      by -(rule exec_meth.exec_catch, simp_all add: shift_compxE2 stack_xlift_compxE2, simp add: match_ex_table_append add: matches_ex_entry_def)
  qed(auto intro: exec_meth.intros simp add: shift_compxE2 stack_xlift_compxE2)
  hence "?exec e2 stk STK loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), \<lfloor>C'\<rfloor>, Suc (length (compE2 e)), 0)]) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth.cases)(auto intro: exec_meth.intros simp add: match_ex_table_append_not_pcs)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk' by(auto simp add: shift_compxE2 eval_nat_numeral)
next
  case (bisim1TryFail e n a xs stk loc pc C' C'' e2 V)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note exec = \<open>?exec (try e catch(C'' V) e2) stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note a = \<open>typeof_addr h a = \<lfloor>Class_type C'\<rfloor>\<close> \<open>\<not> P \<turnstile> C' \<preceq>\<^sup>* C''\<close>
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  moreover from bisim have "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  ultimately have False using exec a
    apply(auto elim!: exec_meth.cases simp add: outside_pcs_compxE2_not_matches_entry outside_pcs_not_matches_entry split: if_split_asm)
    apply(auto simp add: compP2_def match_ex_entry match_ex_table_append_not_pcs cname_of_def split: if_split_asm)
    done
  thus ?case ..
next
  case (bisim1TryCatchThrow e2 n a xs stk loc pc e C' V)
  note bisim = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'
             \<Longrightarrow> ?concl e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note exec = \<open>?exec (try e catch(C' V) e2) stk STK loc (Suc (Suc (length (compE2 e) + pc))) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2) (stack_xlift (length STK) (compxE2 e 0 0) @
    shift (length ?pre) (stack_xlift (length STK)  (compxE2 e2 0 0))) t
    h (stk @ STK, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk', loc', pc', xcp')"
  proof(cases)
    case (exec_catch d)
    let ?stk = "stk @ STK" and ?PC = "Suc (Suc (length (compE2 e) + pc))"
    note s = \<open>stk' = Addr a # drop (length ?stk - d) ?stk\<close> \<open>loc' = loc\<close>
      \<open>ta = \<epsilon>\<close> \<open>h' = h\<close> \<open>xcp' = None\<close>
    from \<open>match_ex_table (compP2 P) (cname_of h a) ?PC (stack_xlift (length STK) (compxE2 (try e catch(C' V) e2) 0 0)) = \<lfloor>(pc', d)\<rfloor>\<close> \<open>d \<le> length ?stk\<close>
    show ?thesis unfolding s
      by -(rule exec_meth.exec_catch, simp_all add: shift_compxE2 stack_xlift_compxE2, simp add: match_ex_table_append add: matches_ex_entry_def)
  qed
  hence "?exec e2 stk STK loc pc \<lfloor>a\<rfloor> stk' loc' (pc' - length ?pre) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ STK"
    and exec'': "exec_meth_d (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', pc' - length ?pre, xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) t h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule append_exec_meth_xt) auto
  hence "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), \<lfloor>C'\<rfloor>, Suc (length (compE2 e)), 0)]) t h (stk, loc, length ?pre + pc, \<lfloor>a\<rfloor>) ta h' (stk'', loc', length ?pre + (pc' - length ?pre), xcp')"
    by(rule exec_meth.cases)(auto intro!: exec_meth.intros simp add: match_ex_table_append_not_pcs)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  moreover hence "(Suc (Suc (pc' - Suc (Suc 0)))) = pc'" by simp
  ultimately show ?case using stk' by(auto simp add: shift_compxE2 eval_nat_numeral)
next
  case bisims1Nil thus ?case by(auto elim: exec_meth.cases)
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs ) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note IH1 = \<open>\<And>stk' loc' pc' xcp' STK. ?exec e stk STK loc pc xcp stk' loc' pc' xcp'
              \<Longrightarrow> ?concl e stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note IH2 = \<open>\<And>xs stk' loc' pc' xcp' STK. ?execs es [] STK xs 0 None stk' loc' pc' xcp'
             \<Longrightarrow> ?concls es [] STK xs 0 None stk' loc' pc' xcp'\<close>
  note exec = \<open>?execs (e # es) stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have "?exec e stk STK loc pc xcp stk' loc' pc' xcp'"
      by(simp add: compxEs2_size_convs)(erule exec_meth_take_xt)
    from IH1[OF this] show ?thesis by auto
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where s: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with exec pc have exec': "exec_meth_d (compP2 P) (compE2 e @ compEs2 es)
      (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length (v # STK)) (compxEs2 es 0 0))) t
      h ([] @ v # STK, loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
    hence "?execs es [] (v # STK) loc 0 None stk' loc' (pc' - length (compE2 e)) xcp'"
      by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
    from IH2[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
      and exec'': "exec_meth_d (compP2 P) (compEs2 es) (compxEs2 es 0 0) t h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by auto
    from exec'' have "exec_meth_d (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk'' @ [v], loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_stk_offer)
    hence "exec_meth_d (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) t h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule append_exec_meth_xt) auto
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
    ultimately show ?thesis using s pc stk' by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
  qed
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  note bisim = \<open>P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc,xcp)\<close>
  note IH = \<open>\<And>stk' loc' pc' xcp' STK. ?execs es stk STK loc pc xcp stk' loc' pc' xcp'
             \<Longrightarrow> ?concls es stk STK loc pc xcp stk' loc' pc' xcp'\<close>
  note exec = \<open>?execs (e # es) (stk @ [v]) STK loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'\<close>
  from exec have exec': "exec_meth_d (compP2 P) (compE2 e @ compEs2 es)
     (stack_xlift (length STK) (compxE2 e 0 0) @ shift (length (compE2 e)) (stack_xlift (length (v # STK)) (compxEs2 es 0 0))) t
     h (stk @ v # STK, loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence "?execs es stk (v # STK) loc pc xcp stk' loc' (pc' - length (compE2 e)) xcp'"
    by(rule exec_meth_drop_xt)(auto simp add: stack_xlift_compxE2)
  from IH[OF this] obtain stk'' where stk': "stk' = stk'' @ v # STK"
    and exec'': "exec_meth_d (compP2 P) (compEs2 es) (compxEs2 es 0 0) t h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')" by auto
  from exec'' have "exec_meth_d (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk'' @ [v], loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_stk_offer)
  hence "exec_meth_d (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) t h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule append_exec_meth_xt) auto
  moreover from exec' have "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc)(auto simp add: stack_xlift_compxE2)
  ultimately show ?case using stk' by(auto simp add: shift_compxEs2 stack_xlift_compxEs2)
next
  case (bisim1Sync12 e1 n e2 V a xs v v')
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, v'] STK xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  thus ?case by(auto elim!: exec_meth.cases split: if_split_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
next
  case (bisim1Sync14 e1 n e2 V a xs v a')
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, Addr a'] STK xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  thus ?case by(auto elim!: exec_meth.cases split: if_split_asm simp add: match_ex_table_append_not_pcs)(simp add: matches_ex_entry_def)
qed

lemma shows bisim1_callD:
  "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp); call1 e' = \<lfloor>(a, M, vs)\<rfloor>;
     compE2 e ! pc = Invoke M' n0 \<rbrakk>
    \<Longrightarrow> M = M'"

  and bisims1_callD:
  "\<lbrakk> P,es,h \<turnstile> (es',xs) [\<leftrightarrow>] (stk,loc,pc, xcp); calls1 es' = \<lfloor>(a, M, vs)\<rfloor>;
     compEs2 es ! pc = Invoke M' n0 \<rbrakk>
    \<Longrightarrow> M = M'"
proof(induct e "n :: nat" e' xs stk loc pc xcp and es "n :: nat" es' xs stk loc pc xcp
    rule: bisim1_bisims1_inducts_split)
  case bisim1AAss1 thus ?case
    apply(simp (no_asm_use) split: if_split_asm add: is_val_iff)
    apply(fastforce dest: bisim_Val_pc_not_Invoke)
    apply(fastforce dest: bisim_Val_pc_not_Invoke)
    apply(fastforce dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)+
    done
next
  case bisim1Call1 thus ?case
    apply(clarsimp split: if_split_asm simp add: is_vals_conv)
    apply(drule bisim_Val_pc_not_Invoke, simp, fastforce)
    apply(drule bisim_Val_pc_not_Invoke, simp, fastforce)
    apply(drule bisim1_pc_length_compE2, clarsimp simp add: neq_Nil_conv)
    apply(drule bisim1_pc_length_compE2, simp)
    apply(drule bisim1_pc_length_compE2, simp)
    apply(drule bisim1_pc_length_compE2, simp)
    apply(drule bisim1_call_pcD, simp, simp)
    apply(drule bisim1_call_pcD, simp, simp)
    done
next
  case bisim1CallParams thus ?case
    apply(clarsimp split: if_split_asm simp add: is_vals_conv)
    apply(drule bisims_Val_pc_not_Invoke, simp, fastforce)
    apply(drule bisims1_pc_length_compEs2, simp)
    apply(drule bisims1_calls_pcD, simp, simp)
    done
qed(fastforce split: if_split_asm dest: bisim1_pc_length_compE2 bisims1_pc_length_compEs2 bisim1_call_pcD bisims1_calls_pcD bisim1_call_xcpNone bisims1_calls_xcpNone bisim_Val_pc_not_Invoke bisims_Val_pc_not_Invoke)+

lemma bisim1_xcpD: "P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_xcpD: "P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compEs2 es)"
by(induct "(e', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)" and "(es', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
  arbitrary: e' xs stk loc pc and es' xs stk loc pc rule: bisim1_bisims1.inducts)
  simp_all

lemma bisim1_match_Some_stk_length:
  "\<lbrakk> P,E,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP2 P) (cname_of h a) pc (compxE2 E 0 0) = \<lfloor>(pc', d)\<rfloor> \<rbrakk>
  \<Longrightarrow> d \<le> length stk"

  and bisims1_match_Some_stk_length:
  "\<lbrakk> P,Es,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP2 P) (cname_of h a) pc (compxEs2 Es 0 0) = \<lfloor>(pc', d)\<rfloor> \<rbrakk>
  \<Longrightarrow> d \<le> length stk"
proof(induct "(e, xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)" and "(es, xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
  arbitrary: pc' d e xs stk loc pc and pc' d es xs stk loc pc rule: bisim1_bisims1.inducts)
  case bisim1Call1 thus ?case
    by(fastforce dest: bisim1_xcpD simp add: match_ex_table_append match_ex_table_not_pcs_None)
next
  case bisim1CallThrowObj thus ?case
    by(fastforce dest: bisim1_xcpD simp add: match_ex_table_append match_ex_table_not_pcs_None)
next
  case bisim1Sync4 thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: if_split_asm)
    apply(fastforce simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisim1Try thus ?case
    by(fastforce simp add: match_ex_table_append matches_ex_entry_def match_ex_table_not_pcs_None dest: bisim1_xcpD split: if_split_asm)
next
  case bisim1TryCatch2 thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: if_split_asm)
    apply(fastforce simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisim1TryFail thus ?case
    by(fastforce simp add: match_ex_table_append matches_ex_entry_def match_ex_table_not_pcs_None dest: bisim1_xcpD split: if_split_asm)
next
  case bisim1TryCatchThrow thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: if_split_asm)
    apply(fastforce simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisims1List1 thus ?case
    by(fastforce simp add: match_ex_table_append split: if_split_asm dest: bisim1_xcpD match_ex_table_pcsD)
qed(fastforce simp add: match_ex_table_not_pcs_None match_ex_table_append match_ex_table_compxE2_shift_conv match_ex_table_compxEs2_shift_conv match_ex_table_compxE2_stack_conv match_ex_table_compxEs2_stack_conv matches_ex_entry_def dest: bisim1_xcpD)+

end

locale J1_JVM_heap_conf_base =
  J1_JVM_heap_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
  +
  J1_heap_conf_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf P 
  +
  JVM_heap_conf_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf "compP2 P"
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr J1_prog"
begin

inductive bisim1_list1 :: 
  "'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr expr1 \<times> 'addr locals1 \<Rightarrow> ('addr expr1 \<times> 'addr locals1) list
  \<Rightarrow> 'addr option \<Rightarrow> 'addr frame list \<Rightarrow> bool"
for t :: 'thread_id and h :: 'heap
where
  bl1_Normal:
  "\<lbrakk> compTP P \<turnstile> t:(xcp, h, (stk, loc, C, M, pc) # frs) \<surd>;
     P \<turnstile> C sees M : Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D;
     P,blocks1 0 (Class D#Ts) body, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp); max_vars e \<le> length xs;
     list_all2 (bisim1_fr P h) exs frs \<rbrakk>
  \<Longrightarrow> bisim1_list1 t h (e, xs) exs xcp ((stk, loc, C, M, pc) # frs)"

| bl1_finalVal:
  "\<lbrakk> hconf h; preallocated h \<rbrakk> \<Longrightarrow> bisim1_list1 t h (Val v, xs) [] None []"

| bl1_finalThrow:
  "\<lbrakk> hconf h; preallocated h \<rbrakk> \<Longrightarrow> bisim1_list1 t h (Throw a, xs) [] \<lfloor>a\<rfloor> []"

fun wbisim1 :: 
  "'thread_id
  \<Rightarrow> ((('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list) \<times> 'heap, 
      ('addr option \<times> 'addr frame list) \<times> 'heap) bisim"
where "wbisim1 t ((ex, exs), h) ((xcp, frs), h') \<longleftrightarrow> h = h' \<and> bisim1_list1 t h ex exs xcp frs"

lemma new_thread_conf_compTP:
  assumes hconf: "hconf h" "preallocated h"
  and ha: "typeof_addr h a = \<lfloor>Class_type C\<rfloor>"
  and sub: "typeof_addr h (thread_id2addr t) = \<lfloor>Class_type C'\<rfloor>" "P \<turnstile> C' \<preceq>\<^sup>* Thread"
  and sees: "P \<turnstile> C sees M: []\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
  shows "compTP P \<turnstile> t:(None, h, [([], Addr a # replicate (max_vars meth) undefined_value, D, M, 0)]) \<surd>"
proof -
  from ha sees_method_decl_above[OF sees]
  have "P,h \<turnstile> Addr a :\<le> Class D" by(simp add: conf_def)
  moreover
  hence "compP2 P,h \<turnstile> Addr a :\<le> Class D" by(simp add: compP2_def)
  hence "compP2 P,h \<turnstile> Addr a # replicate (max_vars meth) undefined_value [:\<le>\<^sub>\<top>] map (\<lambda>i. if i = 0 then OK ([Class D] ! i) else Err) [0..<max_vars meth] @ [Err]"
    by -(rule list_all2_all_nthI, simp_all)
  hence "conf_f (compP2 P) h ([], map (\<lambda>i. if i = 0 then OK ([Class D] ! i) else Err) [0..<max_vars meth] @ [Err])
                (compE2 meth @ [Return]) ([], Addr a # replicate (max_vars meth) undefined_value, D, M, 0)"
    unfolding conf_f_def2 by(simp add: compP2_def)
  ultimately have "conf_f (compP2 P) h ([], TC0.ty\<^sub>l (Suc (max_vars meth)) [Class D] {0}) (compE2 meth @ [Return])
                       ([], Addr a # replicate (max_vars meth) undefined_value, D, M, 0)"
    by(simp add: TC0.ty\<^sub>l_def conf_f_def2 compP2_def)
  with hconf ha sub sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"] sees_method_idemp[OF sees]
  show ?thesis
    by(auto simp add: TC0.ty\<^sub>i'_def correct_state_def compTP_def tconf_def)(fastforce simp add: compP2_def compMb2_def tconf_def intro: sees_method_idemp)+
qed

lemma ta_bisim12_extTA2J1_extTA2JVM:
  assumes nt: "\<And>n T C M a h. \<lbrakk> n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread T (C, M, a) h \<rbrakk> 
           \<Longrightarrow> typeof_addr h a = \<lfloor>Class_type C\<rfloor> \<and> (\<exists>C'. typeof_addr h (thread_id2addr T) = \<lfloor>Class_type C'\<rfloor> \<and> P \<turnstile> C' \<preceq>\<^sup>* Thread) \<and>
              (\<exists>T meth D. P \<turnstile> C sees M:[]\<rightarrow>T =\<lfloor>meth\<rfloor> in D) \<and> hconf h \<and> preallocated h"
  shows "ta_bisim wbisim1 (extTA2J1 P ta) (extTA2JVM (compP2 P) ta)"
proof -
  { fix n t C M a m
    assume "n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" and "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread t (C, M, a) m"
    from nt[OF this] obtain T meth D C'
      where ma: "typeof_addr m a = \<lfloor>Class_type C\<rfloor>"
      and sees: "P \<turnstile> C sees M: []\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
      and sub: "typeof_addr m (thread_id2addr t) = \<lfloor>Class_type C'\<rfloor>" "P \<turnstile> C' \<preceq>\<^sup>* Thread"
      and mconf: "hconf m" "preallocated m" by fastforce
    from sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"]
    have sees': "compP2 P \<turnstile> C sees M: []\<rightarrow>T = \<lfloor>(max_stack meth, max_vars meth, compE2 meth @ [Return], compxE2 meth 0 0)\<rfloor> in D"
      by(simp add: compMb2_def compP2_def)
    have "bisim1_list1 t m ({0:Class D=None; meth}, Addr a # replicate (max_vars meth) undefined_value) ([]) None [([], Addr a # replicate (max_vars meth) undefined_value, D, M, 0)]"
    proof
      from mconf ma sub sees
      show "compTP P \<turnstile> t:(None, m, [([], Addr a # replicate (max_vars meth) undefined_value, D, M, 0)]) \<surd>"
        by(rule new_thread_conf_compTP)

      from sees show "P \<turnstile> D sees M: []\<rightarrow>T = \<lfloor>meth\<rfloor> in D" by(rule sees_method_idemp)
      show "list_all2 (bisim1_fr P m) [] []" by simp
      show "P,blocks1 0 [Class D] meth,m \<turnstile> ({0:Class D=None; meth}, Addr a # replicate (max_vars meth) undefined_value) \<leftrightarrow>
                                                ([], Addr a # replicate (max_vars meth) undefined_value, 0, None)"
        by simp(rule bisim1_refl)
    qed simp
    with sees sees' have "bisim1_list1 t m ({0:Class (fst (method P C M))=None; the (snd (snd (snd (method P C M))))}, Addr a # replicate (max_vars (the (snd (snd (snd (method P C M)))))) undefined_value) [] None [([], Addr a # replicate (fst (snd (the (snd (snd (snd (method (compP2 P) C M))))))) undefined_value, fst (method (compP2 P) C M), M, 0)]" by simp }
  thus ?thesis
    apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
    apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n", auto simp add: extNTA2JVM_def)
    done
qed

end

definition no_call2 :: "'addr expr1 \<Rightarrow> pc \<Rightarrow> bool"
where "no_call2 e pc \<longleftrightarrow> (pc \<le> length (compE2 e)) \<and> (pc < length (compE2 e) \<longrightarrow> (\<forall>M n. compE2 e ! pc \<noteq> Invoke M n))"

definition no_calls2 :: "'addr expr1 list \<Rightarrow> pc \<Rightarrow> bool"
where "no_calls2 es pc \<longleftrightarrow> (pc \<le> length (compEs2 es)) \<and> (pc < length (compEs2 es) \<longrightarrow> (\<forall>M n. compEs2 es ! pc \<noteq> Invoke M n))"

locale J1_JVM_conf_read =
  J1_JVM_heap_conf_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    hconf P 
  +
  JVM_conf_read
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf "compP2 P"
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr J1_prog"

locale J1_JVM_heap_conf =
  J1_JVM_heap_conf_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf P 
  +
  JVM_heap_conf
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf "compP2 P"
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr J1_prog"
begin

lemma red_external_ta_bisim21: 
  "\<lbrakk> wf_prog wf_md P; P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; hconf h'; preallocated h' \<rbrakk>
  \<Longrightarrow> ta_bisim wbisim1 (extTA2J1 P ta) (extTA2JVM (compP2 P) ta)"
apply(rule ta_bisim12_extTA2J1_extTA2JVM)
apply(frule (1) red_external_new_thread_sees)
 apply(fastforce simp add: in_set_conv_nth)
apply(frule red_ext_new_thread_heap)
 apply(fastforce simp add: in_set_conv_nth)
apply(frule red_external_new_thread_exists_thread_object[unfolded compP2_def, simplified])
 apply(fastforce simp add: in_set_conv_nth)
apply simp
done

lemma ta_bisim_red_extTA2J1_extTA2JVM:
  assumes wf: "wf_prog wf_md P"
  and red: "uf,P,t' \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>"
  and hconf: "hconf (hp s')" "preallocated (hp s')"
  shows "ta_bisim wbisim1 (extTA2J1 P ta) (extTA2JVM (compP2 P) ta)"
proof -
  { fix n t C M a H
    assume len: "n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" and tan: "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread t (C, M, a) H"
    hence nt: "NewThread t (C, M, a) H \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" unfolding set_conv_nth by(auto intro!: exI)
    from red1_new_threadD[OF red nt] obtain ad M' vs va T C' Ts' Tr' D'
      where rede: "P,t' \<turnstile> \<langle>ad\<bullet>M'(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,hp s'\<rangle>"
      and ad: "typeof_addr (hp s) ad = \<lfloor>T\<rfloor>" by blast
    from red_ext_new_thread_heap[OF rede nt] have [simp]: "hp s' = H" by simp
    from red_external_new_thread_sees[OF wf rede nt] 
    obtain T body D where Ha: "typeof_addr H a = \<lfloor>Class_type C\<rfloor>"
      and sees: "P \<turnstile> C sees M:[]\<rightarrow>T=\<lfloor>body\<rfloor> in D" by auto
    have sees': "compP2 P \<turnstile> C sees M:[]\<rightarrow>T=\<lfloor>(max_stack body, max_vars body, compE2 body @ [Return], compxE2 body 0 0)\<rfloor> in D"
      using sees unfolding compP2_def compMb2_def Let_def by(auto dest: sees_method_compP)
    from red_external_new_thread_exists_thread_object[unfolded compP2_def, simplified, OF rede nt] hconf Ha sees
    have "compTP P \<turnstile> t:(None, H, [([], Addr a # replicate (max_vars body) undefined_value, D, M, 0)]) \<surd>"
      by(auto intro: new_thread_conf_compTP)
    hence "bisim1_list1 t H ({0:Class D=None; body}, Addr a # replicate (max_vars body) undefined_value) [] None [([], Addr a # replicate (max_vars body) undefined_value, D, M, 0)]"
    proof
      from sees show "P \<turnstile> D sees M:[]\<rightarrow>T=\<lfloor>body\<rfloor> in D" by(rule sees_method_idemp)

      show "P,blocks1 0 [Class D] body,H \<turnstile> ({0:Class D=None; body}, Addr a # replicate (max_vars body) undefined_value) \<leftrightarrow>
                                                ([], Addr a # replicate (max_vars body) undefined_value, 0, None)"
        by(auto intro: bisim1_refl)
    qed simp_all
    hence "bisim1_list1 t H ({0:Class (fst (method P C M))=None; the (snd (snd (snd (method P C M))))},
                               Addr a # replicate (max_vars (the (snd (snd (snd (method P C M)))))) undefined_value)
                              []
                              None [([], Addr a # replicate (fst (snd (the (snd (snd (snd (method (compP2 P) C M))))))) undefined_value,
                                    fst (method (compP2 P) C M), M, 0)]"
      using sees sees' by simp }
  thus ?thesis
    apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
    apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
    apply(auto simp add: extNTA2JVM_def extNTA2J1_def)
    done
qed

end

sublocale J1_JVM_conf_read < heap_conf?: J1_JVM_heap_conf
by(unfold_locales)

sublocale J1_JVM_conf_read < heap?: J1_heap
apply(rule J1_heap.intro)
apply(subst compP_heap[symmetric, where f="\<lambda>_ _ _ _. compMb2", folded compP2_def])
apply(unfold_locales)
done

end
