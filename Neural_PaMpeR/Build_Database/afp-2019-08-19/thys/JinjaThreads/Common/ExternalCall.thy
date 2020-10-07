(*  Title:      JinjaThreads/Common/ExternalCall.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of method calls that cannot be defined inside JinjaThreads\<close>

theory ExternalCall
imports
  "../Framework/FWSemantics"
  Conform
begin

type_synonym
  ('addr,'thread_id,'heap) external_thread_action = "('addr, 'thread_id, cname \<times> mname \<times> 'addr,'heap) Jinja_thread_action"

(* pretty printing for external_thread_action type *)
print_translation \<open>
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ Const (@{type_syntax "String.literal"}, _) $
           (Const (@{type_syntax "prod"}, _) $ Const (@{type_syntax "String.literal"}, _) $ a2)
       , h] =
      if a1 = a2 then Syntax.const @{type_syntax "external_thread_action"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "Jinja_thread_action"}, K tr')]
  end
\<close>
typ "('addr,'thread_id,'heap) external_thread_action"

subsection \<open>Typing of external calls\<close>

inductive external_WT_defs :: "cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> bool" ("(_\<bullet>_'(_')) :: _" [50, 0, 0, 50] 60)
where
  "Thread\<bullet>start([]) :: Void"
| "Thread\<bullet>join([]) :: Void"
| "Thread\<bullet>interrupt([]) :: Void"
| "Thread\<bullet>isInterrupted([]) :: Boolean"
| "Object\<bullet>wait([]) :: Void"
| "Object\<bullet>notify([]) :: Void"
| "Object\<bullet>notifyAll([]) :: Void"
| "Object\<bullet>clone([]) :: Class Object"
| "Object\<bullet>hashcode([]) :: Integer"
| "Object\<bullet>print([Integer]) :: Void"
| "Object\<bullet>currentThread([]) :: Class Thread"
| "Object\<bullet>interrupted([]) :: Boolean"
| "Object\<bullet>yield([]) :: Void"

inductive_cases external_WT_defs_cases:
  "a\<bullet>start(vs) :: T"
  "a\<bullet>join(vs) :: T"
  "a\<bullet>interrupt(vs) :: T"
  "a\<bullet>isInterrupted(vs) :: T"
  "a\<bullet>wait(vs) :: T"
  "a\<bullet>notify(vs) :: T"
  "a\<bullet>notifyAll(vs) :: T"
  "a\<bullet>clone(vs) :: T"
  "a\<bullet>hashcode(vs) :: T"
  "a\<bullet>print(vs) :: T"
  "a\<bullet>currentThread(vs) :: T"
  "a\<bullet>interrupted([]) :: T"
  "a\<bullet>yield(vs) :: T"

inductive is_native :: "'m prog \<Rightarrow> htype \<Rightarrow> mname \<Rightarrow> bool"
  for P :: "'m prog" and hT :: htype and M :: mname
where "\<lbrakk> P \<turnstile> class_type_of hT sees M:Ts\<rightarrow>T = Native in D; D\<bullet>M(Ts) :: T \<rbrakk> \<Longrightarrow> is_native P hT M"

lemma is_nativeD: "is_native P hT M \<Longrightarrow> \<exists>Ts T D. P \<turnstile> class_type_of hT sees M:Ts\<rightarrow>T = Native in D \<and> D\<bullet>M(Ts)::T"
by(simp add: is_native.simps)

inductive (in heap_base) external_WT' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)
for P :: "'m prog" and h :: 'heap and a :: 'addr and M :: mname and vs :: "'addr val list" and U :: ty
where 
  "\<lbrakk> typeof_addr h a = \<lfloor>hT\<rfloor>; map typeof\<^bsub>h\<^esub> vs = map Some Ts; P \<turnstile> class_type_of hT sees M:Ts'\<rightarrow>U = Native in D; 
     P \<turnstile> Ts [\<le>] Ts' \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> a\<bullet>M(vs) : U"

context heap_base begin

lemma external_WT'_iff:
  "P,h \<turnstile> a\<bullet>M(vs) : U \<longleftrightarrow> 
  (\<exists>hT Ts Ts' D. typeof_addr h a = \<lfloor>hT\<rfloor> \<and> map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> class_type_of hT sees M:Ts'\<rightarrow>U=Native in D \<and> P \<turnstile> Ts [\<le>] Ts')"
by(simp add: external_WT'.simps)

end

context heap begin

lemma external_WT'_hext_mono:
  "\<lbrakk> P,h \<turnstile> a\<bullet>M(vs) : T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> a\<bullet>M(vs) : T"
by(auto 5 2 simp add: external_WT'_iff dest: typeof_addr_hext_mono map_typeof_hext_mono)

end

subsection \<open>Semantics of external calls\<close>

datatype 'addr extCallRet = 
    RetVal "'addr val"
  | RetExc 'addr
  | RetStaySame

lemma rec_extCallRet [simp]: "rec_extCallRet = case_extCallRet"
by(auto simp add: fun_eq_iff split: extCallRet.split)

context heap_base begin

abbreviation RetEXC :: "cname \<Rightarrow> 'addr extCallRet"
where "RetEXC C \<equiv> RetExc (addr_of_sys_xcpt C)"

inductive heap_copy_loc :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'heap \<Rightarrow> ('addr, 'thread_id) obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: 'addr and a' :: 'addr and al :: addr_loc and h :: 'heap
where
  "\<lbrakk> heap_read h a al v; heap_write h a' al v h' \<rbrakk>
  \<Longrightarrow> heap_copy_loc a a' al h ([ReadMem a al v, WriteMem a' al v]) h'"

inductive heap_copies :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc list \<Rightarrow> 'heap \<Rightarrow> ('addr, 'thread_id) obs_event list \<Rightarrow> 'heap \<Rightarrow> bool"
for a :: 'addr and a' :: 'addr
where
  Nil: "heap_copies a a' [] h [] h"
| Cons:
  "\<lbrakk> heap_copy_loc a a' al h ob h'; heap_copies a a' als h' obs h'' \<rbrakk>
  \<Longrightarrow> heap_copies a a' (al # als) h (ob @ obs) h''"

inductive_cases heap_copies_cases:
  "heap_copies a a' [] h ops h'"
  "heap_copies a a' (al#als) h ops h'"

text \<open>
  Contrary to Sun's JVM 1.6.0\_07, cloning an interrupted thread does not yield an interrupted thread,
  because the interrupt flag is not stored inside the thread object.
  Starting a clone of a started thread with Sun JVM 1.6.0\_07 raises an illegal thread state exception,
  we just start another thread.
  The thread at @{url "http://mail.openjdk.java.net/pipermail/core-libs-dev/2010-August/004715.html"} discusses
  the general problem of thread cloning and argues against that.
  The bug report @{url "http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6968584"}
  changes the Thread class implementation
  such that \texttt{Object.clone()} can no longer be accessed for Thread and subclasses in Java 7.

  Array cells are never volatile themselves.
\<close>

inductive heap_clone :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'addr) option \<Rightarrow> bool"
for P :: "'m prog" and h :: 'heap and a :: 'addr 
where
  CloneFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>hT\<rfloor>; allocate h hT = {} \<rbrakk>
  \<Longrightarrow> heap_clone P h a h None"
| ObjClone:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; (h', a') \<in> allocate h (Class_type C);
     P \<turnstile> C has_fields FDTs; heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h' obs h'' \<rbrakk>
  \<Longrightarrow> heap_clone P h a h'' \<lfloor>(NewHeapElem a' (Class_type C) # obs, a')\<rfloor>"
| ArrClone:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; (h', a') \<in> allocate h (Array_type T n); P \<turnstile> Object has_fields FDTs;
     heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h' obs  h'' \<rbrakk>
  \<Longrightarrow> heap_clone P h a h'' \<lfloor>(NewHeapElem a' (Array_type T n) # obs, a')\<rfloor>"

inductive red_external ::
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list 
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  and red_external_syntax :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap 
  \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr extCallRet \<Rightarrow> 'heap \<Rightarrow> bool"
  ("_,_ \<turnstile> (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
for P :: "'m prog" and t :: 'thread_id and h :: 'heap and a :: 'addr
where
  "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> red_external P t h a M vs ta va h'"

| RedNewThread:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<lbrace>NewThread (addr2thread_id a) (C, run, a) h, ThreadStart (addr2thread_id a) \<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNewThreadFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>start([]), h\<rangle> -\<lbrace>ThreadExists (addr2thread_id a) True\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalThreadState, h\<rangle>"

| RedJoin:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<lbrace>Join (addr2thread_id a), IsInterrupted t False, ThreadJoin (addr2thread_id a)\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedJoinInterrupt:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>join([]), h\<rangle> -\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetEXC InterruptedException, h\<rangle>"

    \<comment> \<open>Interruption should produce inter-thread actions (JLS 17.4.4) for the synchronizes-with order.
    They should synchronize with the inter-thread actions that determine whether a thread has been interrupted.
    Hence, interruption generates an @{term "ObsInterrupt"} action.

    Although @{term WakeUp} causes the interrupted thread to raise an @{term InterruptedException}
    independent of the interrupt status, the interrupt flag must be set with @{term "Interrupt"} 
    such that other threads observe the interrupted thread as interrupted
    while it competes for the monitor lock again.

    Interrupting a thread which has not yet been started does not set the interrupt flag 
    (tested with Sun HotSpot JVM 1.6.0\_07).\<close>
  
| RedInterrupt:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>interrupt([]), h\<rangle> 
            -\<lbrace>ThreadExists (addr2thread_id a) True, WakeUp (addr2thread_id a), 
              Interrupt (addr2thread_id a), ObsInterrupt (addr2thread_id a)\<rbrace>\<rightarrow>ext
            \<langle>RetVal Unit, h\<rangle>"

| RedInterruptInexist:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>interrupt([]), h\<rangle> 
            -\<lbrace>ThreadExists (addr2thread_id a) False\<rbrace>\<rightarrow>ext
            \<langle>RetVal Unit, h\<rangle>"

| RedIsInterruptedTrue:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>isInterrupted([]), h\<rangle> -\<lbrace> IsInterrupted (addr2thread_id a) True, ObsInterrupted (addr2thread_id a)\<rbrace>\<rightarrow>ext
           \<langle>RetVal (Bool True), h\<rangle>"

| RedIsInterruptedFalse:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>isInterrupted([]), h\<rangle> -\<lbrace>IsInterrupted (addr2thread_id a) False\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool False), h\<rangle>"

    \<comment> \<open>The JLS leaves unspecified whether @{term wait} first checks for the monitor state
    (whether the thread holds a lock on the monitor) or for the interrupt flag of the current thread.
    Sun Hotspot JVM 1.6.0\_07 seems to check for the monitor state first, so we do it here, too.\<close>
| RedWaitInterrupt:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace> \<rightarrow>ext 
         \<langle>RetEXC InterruptedException, h\<rangle>"

| RedWait:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a \<rbrace>\<rightarrow>ext 
         \<langle>RetStaySame, h\<rangle>"

| RedWaitFail:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedWaitNotified:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Notified\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

    \<comment> \<open>This rule does NOT check that the interrupted flag is set, but still clears it.
    The semantics will be that only the executing thread clears its interrupt.\<close>
| RedWaitInterrupted:
  "P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetEXC InterruptedException, h\<rangle>"

    \<comment> \<open>Calls to wait may decide to immediately wake up spuriously. This is 
    indistinguishable from waking up spuriously any time before being 
    notified or interrupted. Spurious wakeups are configured by the
    @{term spurious_wakeup} parameter of the @{term heap_base} locale.\<close>
| RedWaitSpurious:
  "spurious_wakeups \<Longrightarrow> 
    P,t \<turnstile> \<langle>a\<bullet>wait([]), h\<rangle> -\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace> \<rightarrow>ext
          \<langle>RetVal Unit, h\<rangle>"

    \<comment> \<open>@{term notify} and @{term notifyAll} do not perform synchronization inter-thread actions
    because they only tests whether the thread holds a lock, but do not change the lock state.\<close>

| RedNotify:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyFail:
  "P,t \<turnstile> \<langle>a\<bullet>notify([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedNotifyAll:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedNotifyAllFail:
  "P,t \<turnstile> \<langle>a\<bullet>notifyAll([]), h\<rangle> -\<lbrace>UnlockFail\<rightarrow>a\<rbrace>\<rightarrow>ext \<langle>RetEXC IllegalMonitorState, h\<rangle>"

| RedClone:
  "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor> 
    \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -(K$ [], [], [], [], [], obs)\<rightarrow>ext \<langle>RetVal (Addr a'), h'\<rangle>"

| RedCloneFail:
  "heap_clone P h a h' None \<Longrightarrow> P,t \<turnstile> \<langle>a\<bullet>clone([]), h\<rangle> -\<epsilon>\<rightarrow>ext \<langle>RetEXC OutOfMemory, h'\<rangle>"

| RedHashcode:
  "P,t \<turnstile> \<langle>a\<bullet>hashcode([]), h\<rangle> -\<lbrace>\<rbrace>\<rightarrow>ext \<langle>RetVal (Intg (word_of_int (hash_addr a))), h\<rangle>"

| RedPrint:
  "P,t \<turnstile> \<langle>a\<bullet>print(vs), h\<rangle> -\<lbrace>ExternalCall a print vs Unit\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

| RedCurrentThread:
  "P,t \<turnstile> \<langle>a\<bullet>currentThread([]), h\<rangle> -\<lbrace>\<rbrace>\<rightarrow>ext \<langle>RetVal (Addr (thread_id2addr t)), h\<rangle>"

| RedInterruptedTrue:
  "P,t \<turnstile> \<langle>a\<bullet>interrupted([]), h\<rangle> -\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool True), h\<rangle>"

| RedInterruptedFalse:
  "P,t \<turnstile> \<langle>a\<bullet>interrupted([]), h\<rangle> -\<lbrace>IsInterrupted t False\<rbrace>\<rightarrow>ext \<langle>RetVal (Bool False), h\<rangle>"

| RedYield:
  "P,t \<turnstile> \<langle>a\<bullet>yield([]), h\<rangle> -\<lbrace>Yield\<rbrace>\<rightarrow>ext \<langle>RetVal Unit, h\<rangle>"

subsection \<open>Aggressive formulation for external cals\<close>

definition red_external_aggr :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap \<Rightarrow> 
  (('addr, 'thread_id, 'heap) external_thread_action \<times> 'addr extCallRet \<times> 'heap) set"
where
  "red_external_aggr P t a M vs h =
   (if M = wait then
      let ad_t = thread_id2addr t
      in {(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h),
          (\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetStaySame, h),
          (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h),
          (\<lbrace>Notified\<rbrace>, RetVal Unit, h),
          (\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h)} \<union>
         (if spurious_wakeups then {(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetVal Unit, h)} else {})
    else if M = notify then {(\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, RetVal Unit, h),
                             (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = notifyAll then {(\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
                                (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, RetEXC IllegalMonitorState, h)}
    else if M = clone then
       {((K$ [], [], [], [], [], obs), RetVal (Addr a'), h')|obs a' h'. heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>}
       \<union> {(\<lbrace>\<rbrace>, RetEXC OutOfMemory, h')|h'. heap_clone P h a h' None}
    else if M = hashcode then {(\<lbrace>\<rbrace>, RetVal (Intg (word_of_int (hash_addr a))), h)}
    else if M = print then {(\<lbrace>ExternalCall a M vs Unit\<rbrace>, RetVal Unit, h)}
    else if M = currentThread then {(\<lbrace>\<rbrace>, RetVal (Addr (thread_id2addr t)), h)}
    else if M = interrupted then {(\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetVal (Bool True), h),
                                  (\<lbrace>IsInterrupted t False\<rbrace>, RetVal (Bool False), h)}
    else if M = yield then {(\<lbrace>Yield\<rbrace>, RetVal Unit, h)}
    else
      let hT = the (typeof_addr h a)
      in if P \<turnstile> ty_of_htype hT \<le> Class Thread then
        let t_a = addr2thread_id a 
        in if M = start then 
             {(\<lbrace>NewThread t_a (the_Class (ty_of_htype hT), run, a) h, ThreadStart t_a\<rbrace>, RetVal Unit, h), 
              (\<lbrace>ThreadExists t_a True\<rbrace>, RetEXC IllegalThreadState, h)}
           else if M = join then 
             {(\<lbrace>Join t_a, IsInterrupted t False, ThreadJoin t_a\<rbrace>, RetVal Unit, h),
              (\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetEXC InterruptedException, h)}
           else if M = interrupt then 
             {(\<lbrace>ThreadExists t_a True, WakeUp t_a, Interrupt t_a, ObsInterrupt t_a\<rbrace>, RetVal Unit, h), 
              (\<lbrace>ThreadExists t_a False\<rbrace>, RetVal Unit, h)}
           else if M = isInterrupted then
             {(\<lbrace>IsInterrupted t_a False\<rbrace>, RetVal (Bool False), h),
              (\<lbrace>IsInterrupted t_a True, ObsInterrupted t_a\<rbrace>, RetVal (Bool True), h)}
         else {(\<lbrace>\<rbrace>, undefined)}
      else {(\<lbrace>\<rbrace>, undefined)})"

lemma red_external_imp_red_external_aggr:
  "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<Longrightarrow> (ta, va, h') \<in> red_external_aggr P t a M vs h"
unfolding red_external_aggr_def
by(auto elim!: red_external.cases split del: if_split simp add: split_beta)

end

context heap begin

lemma hext_heap_copy_loc:
  "heap_copy_loc a a' al h obs h' \<Longrightarrow> h \<unlhd> h'"
by(blast elim: heap_copy_loc.cases dest: hext_heap_ops)

lemma hext_heap_copies:
  assumes "heap_copies a a' als h obs h'"
  shows "h \<unlhd> h'"
using assms by induct(blast intro: hext_heap_copy_loc hext_trans)+

lemma hext_heap_clone:
  assumes "heap_clone P h a h' res"
  shows "h \<unlhd> h'"
using assms by(blast elim: heap_clone.cases dest: hext_heap_ops hext_heap_copies intro: hext_trans)

theorem red_external_hext: 
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "hext h h'"
using assms
by(cases)(blast intro: hext_heap_ops hext_heap_clone)+

lemma red_external_preserves_tconf:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; P,h \<turnstile> t' \<surd>t \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
by(drule red_external_hext)(rule tconf_hext_mono)

end

context heap_conf begin

lemma typeof_addr_heap_clone:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "hconf h"
  shows "typeof_addr h' a' = typeof_addr h a"
using assms
by cases (auto dest!: allocate_SomeD hext_heap_copies dest: typeof_addr_hext_mono typeof_addr_is_type is_type_ArrayD)

end

context heap_base begin 

lemma red_ext_new_thread_heap:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto elim: red_external.cases simp add: ta_upd_simps)

lemma red_ext_aggr_new_thread_heap:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewThread t' ex h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = h'"
by(auto simp add: red_external_aggr_def is_native.simps split_beta ta_upd_simps split: if_split_asm)

end

context addr_conv begin

lemma red_external_new_thread_exists_thread_object:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto elim!: red_external.cases dest!: Array_widen simp add: ta_upd_simps)

lemma red_external_aggr_new_thread_exists_thread_object:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; typeof_addr h a \<noteq> None;
     NewThread t' x h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr h' (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto simp add: red_external_aggr_def is_native.simps split_beta ta_upd_simps widen_Class split: if_split_asm dest!: Array_widen)

end

context heap begin

lemma red_external_aggr_hext: 
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
apply(auto simp add: red_external_aggr_def split_beta is_native.simps elim!: external_WT_defs_cases hext_heap_clone split: if_split_asm)
apply(auto elim!: external_WT_defs.cases dest!: sees_method_decl_above intro: widen_trans simp add: class_type_of_eq split: htype.split_asm)
done

lemma red_external_aggr_preserves_tconf:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M; P,h \<turnstile> t' \<surd>t \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> t' \<surd>t"
by(blast dest: red_external_aggr_hext intro: tconf_hext_mono)

end

context heap_base begin

lemma red_external_Wakeup_no_Join_no_Lock_no_Interrupt:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow>
  collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
by(auto elim!: red_external.cases simp add: ta_upd_simps collect_locks_def collect_interrupts_def)

lemma red_external_aggr_Wakeup_no_Join:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h;
     Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
by(auto simp add: red_external_aggr_def split_beta ta_upd_simps collect_locks_def collect_interrupts_def split: if_split_asm)

lemma red_external_Suspend_StaySame:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_StaySame:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> va = RetStaySame"
by(auto simp add: red_external_aggr_def split_beta ta_upd_simps split: if_split_asm)

lemma red_external_Suspend_waitD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
by(auto elim!: red_external.cases simp add: ta_upd_simps)

lemma red_external_aggr_Suspend_waitD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> M = wait"
by(auto simp add: red_external_aggr_def split_beta ta_upd_simps split: if_split_asm)

lemma red_external_new_thread_sub_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
by(auto elim!: red_external.cases simp add: widen_Class ta_upd_simps)

lemma red_external_aggr_new_thread_sub_thread:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; typeof_addr h a \<noteq> None;
     NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M' = run"
by(auto simp add: red_external_aggr_def split_beta ta_upd_simps widen_Class split: if_split_asm dest!: Array_widen)


lemma heap_copy_loc_length:
  assumes "heap_copy_loc a a' al h obs h'"
  shows "length obs = 2"
using assms by(cases) simp

lemma heap_copies_length:
  assumes "heap_copies a a' als h obs h'"
  shows "length obs = 2 * length als"
using assms by(induct)(auto dest!: heap_copy_loc_length)

end

subsection \<open>\<open>\<tau>\<close>-moves\<close>

inductive \<tau>external_defs :: "cname \<Rightarrow> mname \<Rightarrow> bool"
where
  "\<tau>external_defs Object hashcode"
| "\<tau>external_defs Object currentThread"

definition \<tau>external :: "'m prog \<Rightarrow> htype \<Rightarrow> mname \<Rightarrow> bool"
where "\<tau>external P hT M \<longleftrightarrow> (\<exists>Ts Tr D. P \<turnstile> class_type_of hT sees M:Ts\<rightarrow>Tr = Native in D \<and> \<tau>external_defs D M)"

context heap_base begin

definition \<tau>external' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> bool"
where "\<tau>external' P h a M \<longleftrightarrow> (\<exists>hT. typeof_addr h a = Some hT \<and> \<tau>external P hT M)"

lemma \<tau>external'_red_external_heap_unchanged:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: red_external.cases \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def)

lemma \<tau>external'_red_external_aggr_heap_unchanged:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def red_external_aggr_def)

lemma \<tau>external'_red_external_TA_empty:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: red_external.cases \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def)

lemma \<tau>external'_red_external_aggr_TA_empty:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external' P h a M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def \<tau>external'_def red_external_aggr_def)

lemma red_external_new_thread_addr_conf:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; NewThread t (C, M, a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> P,h' \<turnstile> Addr a :\<le> Class Thread"
by(auto elim!: red_external.cases simp add: conf_def ta_upd_simps)

lemma \<tau>external_red_external_aggr_heap_unchanged:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external P (the (typeof_addr h a)) M \<rbrakk> \<Longrightarrow> h' = h"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def red_external_aggr_def)

lemma \<tau>external_red_external_aggr_TA_empty:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; \<tau>external P (the (typeof_addr h a)) M \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
by(auto elim!: \<tau>external_defs.cases simp add: \<tau>external_def red_external_aggr_def)

end

subsection \<open>Code generation\<close>

code_pred 
  (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  external_WT_defs 
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify, skip_proof]
  is_native
.

declare heap_base.heap_copy_loc.intros[code_pred_intro]

code_pred
  (modes: (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) 
  heap_base.heap_copy_loc
proof -
  case heap_copy_loc
  from heap_copy_loc.prems show thesis
    by(rule heap_base.heap_copy_loc.cases)(rule heap_copy_loc.that[OF refl refl refl refl refl refl])
qed

declare heap_base.heap_copies.intros [code_pred_intro]

code_pred
  (modes: (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) => (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.heap_copies
proof -
  case heap_copies
  from heap_copies.prems show thesis
    by(rule heap_base.heap_copies.cases)(erule (3) heap_copies.that[OF refl refl refl refl]|assumption)+
qed

declare heap_base.heap_clone.intros [folded Predicate_Compile.contains_def, code_pred_intro]

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.heap_clone
proof -
  case heap_clone
  from heap_clone.prems show thesis
    by(rule heap_base.heap_clone.cases[folded Predicate_Compile.contains_def])(erule (3) heap_clone.that[OF refl refl refl refl refl refl refl]|assumption)+
qed

text \<open>
  code\_pred in Isabelle2012 cannot handle boolean parameters as premises properly, 
  so this replacement rule explicitly tests for @{term "True"}
\<close>

lemma (in heap_base) RedWaitSpurious_Code:
  "spurious_wakeups = True \<Longrightarrow> 
   P,t \<turnstile> \<langle>a\<bullet>wait([]),h\<rangle> -\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>\<rightarrow>ext \<langle>RetVal Unit,h\<rangle>"
by(rule RedWaitSpurious) simp

lemmas [code_pred_intro] =
  heap_base.RedNewThread heap_base.RedNewThreadFail 
  heap_base.RedJoin heap_base.RedJoinInterrupt
  heap_base.RedInterrupt heap_base.RedInterruptInexist heap_base.RedIsInterruptedTrue heap_base.RedIsInterruptedFalse
  heap_base.RedWaitInterrupt heap_base.RedWait heap_base.RedWaitFail heap_base.RedWaitNotified heap_base.RedWaitInterrupted
declare heap_base.RedWaitSpurious_Code [code_pred_intro RedWaitSpurious]
lemmas [code_pred_intro] =
  heap_base.RedNotify heap_base.RedNotifyFail heap_base.RedNotifyAll heap_base.RedNotifyAllFail 
  heap_base.RedClone heap_base.RedCloneFail
  heap_base.RedHashcode heap_base.RedPrint heap_base.RedCurrentThread 
  heap_base.RedInterruptedTrue heap_base.RedInterruptedFalse
  heap_base.RedYield

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  heap_base.red_external
proof -
  case red_external
  from red_external.prems show ?thesis
    apply(rule heap_base.red_external.cases)
    apply(erule (4) red_external.that[OF refl refl refl refl refl refl refl refl refl refl refl refl]|assumption|erule eqTrueI)+
    done
qed

end
