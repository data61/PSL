(*  Title:      JinjaThreads/Execute/ExternalCall_Execute.thy
    Author:     Andreas Lochbihler
*)

section \<open>Executable semantics for the JVM\<close>

theory ExternalCall_Execute
imports
  "../Common/ExternalCall"
  "../Basic/Set_without_equal"
begin

subsection \<open>Translated versions of external calls for the JVM\<close>

locale heap_execute = addr_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id" 
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr" 
  fixes spurious_wakeups :: bool
  and empty_heap :: "'heap" 
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set" 
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> htype option" 
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val set" 
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap set"

sublocale heap_execute < execute: heap_base
  addr2thread_id thread_id2addr 
  spurious_wakeups
  empty_heap allocate typeof_addr
  "\<lambda>h a ad v. v \<in> heap_read h a ad" "\<lambda>h a ad v h'. h' \<in> heap_write h a ad v"
.

context heap_execute begin

definition heap_copy_loc :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'heap) set"
where [simp]:
  "heap_copy_loc a a' al h = {(obs, h'). execute.heap_copy_loc a a' al h obs h'}"

lemma heap_copy_loc_code:
  "heap_copy_loc a a' al h =
   (do {
      v \<leftarrow> heap_read h a al;
      h' \<leftarrow> heap_write h a' al v;
      {([ReadMem a al v, WriteMem a' al v], h')}
   })"
by(auto simp add: execute.heap_copy_loc.simps)

definition heap_copies :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc list \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'heap) set"
where [simp]: "heap_copies a a' al h = {(obs, h'). execute.heap_copies a a' al h obs h'}"

lemma heap_copies_code:
  shows heap_copies_Nil: 
  "heap_copies a a' [] h = {([], h)}"
  and heap_copies_Cons:
  "heap_copies a a' (al # als) h =
  (do {
     (ob, h') \<leftarrow> heap_copy_loc a a' al h;
     (obs, h'') \<leftarrow> heap_copies a a' als h';
     {(ob @ obs, h'')}
  })"
by(fastforce elim!: execute.heap_copies_cases intro: execute.heap_copies.intros)+

definition heap_clone :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> ('heap \<times> (('addr, 'thread_id) obs_event list \<times> 'addr) option) set"
where [simp]: "heap_clone P h a = {(h', obsa). execute.heap_clone P h a h' obsa}"

lemma heap_clone_code:
  "heap_clone P h a =
  (case typeof_addr h a of
    \<lfloor>Class_type C\<rfloor> \<Rightarrow> 
      let HA = allocate h (Class_type C) 
      in if HA = {} then {(h, None)} else do {
          (h', a') \<leftarrow> HA;
          FDTs \<leftarrow> set_of_pred (Fields_i_i_o P C);
          (obs, h'') \<leftarrow> heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h';
          {(h'', \<lfloor>(NewHeapElem a' (Class_type C) # obs, a')\<rfloor>)}
        }
  | \<lfloor>Array_type T n\<rfloor> \<Rightarrow> 
      let HA = allocate h (Array_type T n)
      in if HA = {} then {(h, None)} else do {
        (h', a') \<leftarrow> HA;
        FDTs \<leftarrow> set_of_pred (Fields_i_i_o P Object);
        (obs, h'') \<leftarrow> heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h';
        {(h'', \<lfloor>(NewHeapElem a' (Array_type T n) # obs, a')\<rfloor>)}
      }
  | _ \<Rightarrow> {})"
  by (auto 4 3 elim!: execute.heap_clone.cases split: ty.splits
  prod.split_asm htype.splits intro: execute.heap_clone.intros
  simp add: eval_Fields_conv split_beta prod_eq_iff)
    (auto simp add: eval_Fields_conv Bex_def)

definition red_external_aggr :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap \<Rightarrow> 
  (('addr, 'thread_id, 'heap) external_thread_action \<times> 'addr extCallRet \<times> 'heap) set"
where [simp]:
  "red_external_aggr P t a M vs h = execute.red_external_aggr P t a M vs h"

lemma red_external_aggr_code:
  "red_external_aggr P t a M vs h =
   (if M = wait then
      let ad_t = thread_id2addr t
      in {(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h),
          (\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetStaySame, h),
          (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h),
          (\<lbrace>Notified\<rbrace>, RetVal Unit, h),
          (\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h)} \<union>
          (if spurious_wakeups then {(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetVal Unit, h)} else {})
    else if M = notify then
       {(\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, RetVal Unit, h),
        (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h)}
    else if M = notifyAll then 
       {(\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
        (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h)}
    else if M = clone then
       do {
         (h', obsa) \<leftarrow> heap_clone P h a;
         {case obsa of None \<Rightarrow> (\<epsilon>, execute.RetEXC OutOfMemory, h')
           | Some (obs, a') \<Rightarrow> ((K$ [], [], [], [], [], obs), RetVal (Addr a'), h')}
       }
    else if M = hashcode then {(\<epsilon>, RetVal (Intg (word_of_int (hash_addr a))), h)}
    else if M = print then {(\<lbrace>ExternalCall a M vs Unit\<rbrace>, RetVal Unit, h)}
    else if M = currentThread then {(\<epsilon>, RetVal (Addr (thread_id2addr t)), h)}
    else if M = interrupted then 
      {(\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetVal (Bool True), h),
       (\<lbrace>IsInterrupted t False\<rbrace>, RetVal (Bool False), h)}
    else if M = yield then {(\<lbrace>Yield\<rbrace>, RetVal Unit, h)}
    else
      let T = ty_of_htype (the (typeof_addr h a))
      in if P \<turnstile> T \<le> Class Thread then
        let t_a = addr2thread_id a 
        in if M = start then 
             {(\<lbrace>NewThread t_a (the_Class T, run, a) h, ThreadStart t_a\<rbrace>, RetVal Unit, h),
              (\<lbrace>ThreadExists t_a True\<rbrace>, execute.RetEXC IllegalThreadState, h)}
           else if M = join then
             {(\<lbrace>Join t_a, IsInterrupted t False, ThreadJoin t_a\<rbrace>, RetVal Unit, h),
              (\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h)}
           else if M = interrupt then
             {(\<lbrace>ThreadExists t_a True, WakeUp t_a, Interrupt t_a, ObsInterrupt t_a\<rbrace>, RetVal Unit, h),
              (\<lbrace>ThreadExists t_a False\<rbrace>, RetVal Unit, h)}
           else if M = isInterrupted then
             {(\<lbrace>IsInterrupted t_a False\<rbrace>, RetVal (Bool False), h),
              (\<lbrace>IsInterrupted t_a True, ObsInterrupted t_a\<rbrace>, RetVal (Bool True), h)}
         else {(\<lbrace>\<rbrace>, undefined)}
    else {(\<lbrace>\<rbrace>, undefined)})"
by (auto simp add: execute.red_external_aggr_def
  split del: option.splits) auto

end

lemmas [code] =
  heap_execute.heap_copy_loc_code
  heap_execute.heap_copies_code
  heap_execute.heap_clone_code
  heap_execute.red_external_aggr_code

end
