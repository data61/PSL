(*  Title:      JinjaThreads/Execute/Scheduler.thy
    Author:     Andreas Lochbihler
*)

section \<open>Abstract scheduler\<close>

theory Scheduler
imports
  State_Refinement
  "../Framework/FWProgressAux"
  "../Framework/FWLTS"
  (*"../../Collections/spec/SetSpec"
  "../../Collections/spec/MapSpec"
  "../../Collections/spec/ListSpec"*)
  "../Basic/JT_ICF"

begin

text \<open>
  Define an unfold operation that puts everything into one function to avoid duplicate evaluation.
\<close>

definition unfold_tllist' :: "('a \<Rightarrow> 'b \<times> 'a + 'c) \<Rightarrow> 'a \<Rightarrow> ('b, 'c) tllist"
where [code del]: 
  "unfold_tllist' f = 
   unfold_tllist (\<lambda>a. \<exists>c. f a = Inr c) (projr \<circ> f) (fst \<circ> projl \<circ> f) (snd \<circ> projl \<circ> f)"

lemma unfold_tllist' [code]:
  "unfold_tllist' f a =
  (case f a of Inr c \<Rightarrow> TNil c | Inl (b, a') \<Rightarrow> TCons b (unfold_tllist' f a'))"
by(rule tllist.expand)(auto simp add: unfold_tllist'_def split: sum.split_asm)


type_synonym
  ('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler = 
    "'s \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 's) option"

locale scheduler_spec_base =
  state_refine_base
    final r convert_RA
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar 
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"

locale scheduler_spec = 
  scheduler_spec_base
    final r convert_RA
    schedule \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar 
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  +
  fixes invariant :: "('l,'t,'x,'m,'w) state set"
  assumes schedule_NoneD:
  "\<lbrakk> schedule \<sigma> s = None; state_invar s; \<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s))); state_\<alpha> s \<in> invariant \<rbrakk>
  \<Longrightarrow> \<alpha>.active_threads (state_\<alpha> s) = {}"
  and schedule_Some_NoneD:
  "\<lbrakk> schedule \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>; state_invar s; \<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s))); state_\<alpha> s \<in> invariant \<rbrakk> 
  \<Longrightarrow> \<exists>x ln n. thr_\<alpha> (thr s) t = \<lfloor>(x, ln)\<rfloor> \<and> ln $ n > 0 \<and> \<not> waiting (ws_\<alpha> (wset s) t) \<and> may_acquire_all (locks s) t ln"
  and schedule_Some_SomeD:
  "\<lbrakk> schedule \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>; state_invar s; \<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s))); state_\<alpha> s \<in> invariant \<rbrakk> 
  \<Longrightarrow> \<exists>x. thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> Predicate.eval (r t (x, shr s)) (ta, x', m') \<and> 
         \<alpha>.actions_ok (state_\<alpha> s) t ta"
  and schedule_invar_None:
  "\<lbrakk> schedule \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>; state_invar s; \<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s))); state_\<alpha> s \<in> invariant \<rbrakk>
  \<Longrightarrow> \<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s)))"
  and schedule_invar_Some:
  "\<lbrakk> schedule \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>; state_invar s; \<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s))); state_\<alpha> s \<in> invariant \<rbrakk>
  \<Longrightarrow> \<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"

locale pick_wakeup_spec_base =
  state_refine_base
    final r convert_RA
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar 
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"

locale pick_wakeup_spec =
  pick_wakeup_spec_base 
    final r convert_RA
    pick_wakeup \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  +
  assumes pick_wakeup_NoneD:
  "\<lbrakk> pick_wakeup \<sigma> t w ws = None; ws_invar ws; \<sigma>_invar \<sigma> T; dom (ws_\<alpha> ws) \<subseteq> T; t \<in> T \<rbrakk> 
  \<Longrightarrow> InWS w \<notin> ran (ws_\<alpha> ws)"
  and pick_wakeup_SomeD:
  "\<lbrakk> pick_wakeup \<sigma> t w ws = \<lfloor>t'\<rfloor>; ws_invar ws; \<sigma>_invar \<sigma> T; dom (ws_\<alpha> ws) \<subseteq> T; t \<in> T \<rbrakk>
  \<Longrightarrow> ws_\<alpha> ws t' = \<lfloor>InWS w\<rfloor>"

locale scheduler_base_aux =
  state_refine_base
    final r convert_RA
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
begin

definition free_thread_id :: "'m_t \<Rightarrow> 't \<Rightarrow> bool"
where "free_thread_id ts t \<longleftrightarrow> thr_lookup t ts = None"

fun redT_updT :: "'m_t \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> 'm_t"
where
  "redT_updT ts (NewThread t' x m) = thr_update t' (x, no_wait_locks) ts"
| "redT_updT ts _ = ts"

definition redT_updTs :: "'m_t \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> 'm_t"
where "redT_updTs = foldl redT_updT"

primrec thread_ok :: "'m_t \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> bool"
where
  "thread_ok ts (NewThread t x m) = free_thread_id ts t"
| "thread_ok ts (ThreadExists t b) = (b \<noteq> free_thread_id ts t)"

text \<open>
  We use @{term "redT_updT"} in \<open>thread_ok\<close> instead of @{term "redT_updT'"} like in theory @{theory JinjaThreads.FWThread}.
  This fixes @{typ "'x"} in the @{typ "('t,'x,'m) new_thread_action list"} type, but avoids @{term "undefined"},
  which raises an exception during execution in the generated code.
\<close>

primrec thread_oks :: "'m_t \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> bool"
where
  "thread_oks ts [] = True"
| "thread_oks ts (ta#tas) = (thread_ok ts ta \<and> thread_oks (redT_updT ts ta) tas)"

definition wset_actions_ok :: "'m_w \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> bool"
where
  "wset_actions_ok ws t was \<longleftrightarrow>
   ws_lookup t ws = 
   (if Notified \<in> set was then \<lfloor>PostWS WSNotified\<rfloor>
    else if WokenUp \<in> set was then \<lfloor>PostWS WSWokenUp\<rfloor>
    else None)"

primrec cond_action_ok :: "('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't \<Rightarrow> 't conditional_action \<Rightarrow> bool" 
where
  "\<And>ln. cond_action_ok s t (Join T) = 
   (case thr_lookup T (thr s)
      of None \<Rightarrow> True 
    | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> t \<noteq> T \<and> final x \<and> ln = no_wait_locks \<and> ws_lookup T (wset s) = None)"
| "cond_action_ok s t Yield = True"

definition cond_action_oks :: "('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't \<Rightarrow> 't conditional_action list \<Rightarrow> bool" 
where
  "cond_action_oks s t cts = list_all (cond_action_ok s t) cts"

primrec redT_updI :: "'s_i \<Rightarrow> 't interrupt_action \<Rightarrow> 's_i"
where
  "redT_updI is (Interrupt t) = is_ins t is"
| "redT_updI is (ClearInterrupt t) = is_delete t is"
| "redT_updI is (IsInterrupted t b) = is"

primrec redT_updIs :: "'s_i \<Rightarrow> 't interrupt_action list \<Rightarrow> 's_i"
where
  "redT_updIs is [] = is"
| "redT_updIs is (ia # ias) = redT_updIs (redT_updI is ia) ias"

primrec interrupt_action_ok :: "'s_i \<Rightarrow> 't interrupt_action \<Rightarrow> bool"
where
  "interrupt_action_ok is (Interrupt t) = True"
| "interrupt_action_ok is (ClearInterrupt t) = True"
| "interrupt_action_ok is (IsInterrupted t b) = (b = (is_memb t is))"

primrec interrupt_actions_ok :: "'s_i \<Rightarrow> 't interrupt_action list \<Rightarrow> bool"
where
  "interrupt_actions_ok is [] = True"
| "interrupt_actions_ok is (ia # ias) \<longleftrightarrow> interrupt_action_ok is ia \<and> interrupt_actions_ok (redT_updI is ia) ias"

definition actions_ok :: "('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o') thread_action \<Rightarrow> bool"
where
  "actions_ok s t ta \<longleftrightarrow>
   lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> 
   thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and>
   cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and>
   wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
   interrupt_actions_ok (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"

end

locale scheduler_base =
  scheduler_base_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  scheduler_spec_base
    final r convert_RA
    schedule \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar 
    is_\<alpha> is_invar
  +
  pick_wakeup_spec_base
    final r convert_RA
    pick_wakeup \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler"
  and "output" :: "'s \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
begin

primrec exec_updW :: "'s \<Rightarrow> 't \<Rightarrow> 'm_w \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> 'm_w"
where
  "exec_updW \<sigma> t ws (Notify w) = 
   (case pick_wakeup \<sigma> t w ws
    of None  \<Rightarrow> ws
    | Some t \<Rightarrow> ws_update t (PostWS WSNotified) ws)"
| "exec_updW \<sigma> t ws (NotifyAll w) =
   ws_iterate ws (\<lambda>_. True) (\<lambda>(t, w') ws'. if w' = InWS w then ws_update t (PostWS WSNotified) ws' else ws') 
              ws"
| "exec_updW \<sigma> t ws (Suspend w) = ws_update t (InWS w) ws"
| "exec_updW \<sigma> t ws (WakeUp t') =
   (case ws_lookup t' ws of \<lfloor>InWS w\<rfloor> \<Rightarrow> ws_update t' (PostWS WSWokenUp) ws | _ \<Rightarrow> ws)"
| "exec_updW \<sigma> t ws Notified = ws_delete t ws"
| "exec_updW \<sigma> t ws WokenUp = ws_delete t ws"

definition exec_updWs :: "'s \<Rightarrow> 't \<Rightarrow> 'm_w \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> 'm_w"
where "exec_updWs \<sigma> t = foldl (exec_updW \<sigma> t)"

definition exec_upd ::
  "'s \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<Rightarrow> 'm
  \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine"
where [simp]:
  "exec_upd \<sigma> s t ta x' m' =
   (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>,
    (thr_update t (x', redT_updLns (locks s) t (snd (the (thr_lookup t (thr s)))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>), m'),
    exec_updWs \<sigma> t (wset s) \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>, redT_updIs (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>)"

definition execT :: 
  "'s \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine
  \<Rightarrow> ('s \<times> 't \<times> ('l,'t,'x,'m,'w,'o) thread_action \<times> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine) option"
where 
  "execT \<sigma> s =
  (do {
     (t, tax'm', \<sigma>') \<leftarrow> schedule \<sigma> s;
     case tax'm' of
       None \<Rightarrow> 
       (let (x, ln) = the (thr_lookup t (thr s));
            ta = (K$ [], [], [], [], [], convert_RA ln);
            s' = (acquire_all (locks s) t ln, (thr_update t (x, no_wait_locks) (thr s), shr s), wset s, interrupts s)
        in \<lfloor>(\<sigma>', t, ta, s')\<rfloor>)
     | \<lfloor>(ta, x', m')\<rfloor> \<Rightarrow> \<lfloor>(\<sigma>', t, ta, exec_upd \<sigma> s t ta x' m')\<rfloor>
   })"

primrec exec_step :: 
  "'s \<times> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 
   ('s \<times> 't \<times> ('l,'t,'x,'m,'w,'o) thread_action) \<times> 's \<times> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine + ('l,'t,'m,'m_t,'m_w,'s_i) state_refine"
where
  "exec_step (\<sigma>, s) =
   (case execT \<sigma> s of 
      None \<Rightarrow> Inr s
    | Some (\<sigma>', t, ta, s') \<Rightarrow> Inl ((\<sigma>, t, ta), \<sigma>', s'))"

declare exec_step.simps [simp del]

definition exec_aux ::
  "'s \<times> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine
  \<Rightarrow> ('s \<times> 't \<times> ('l,'t,'x,'m,'w,'o) thread_action, ('l,'t,'m,'m_t,'m_w,'s_i) state_refine) tllist"
where
  "exec_aux \<sigma>s = unfold_tllist' exec_step \<sigma>s"

definition exec :: "'s \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> ('q, ('l,'t,'m,'m_t,'m_w,'s_i) state_refine) tllist"
where 
  "exec \<sigma> s = tmap the id (tfilter undefined (\<lambda>q. q \<noteq> None) (tmap (\<lambda>(\<sigma>, t, ta). output \<sigma> t ta) id (exec_aux (\<sigma>, s))))"

end

text \<open>
  Implement \<open>pick_wakeup\<close> by \<open>map_sel'\<close>
\<close>

definition pick_wakeup_via_sel :: 
  "('m_w \<Rightarrow> ('t \<Rightarrow> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> 't \<times> 'w wait_set_status) 
  \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
where "pick_wakeup_via_sel ws_sel \<sigma> t w ws = map_option fst (ws_sel ws (\<lambda>t w'. w' = InWS w))"

lemma pick_wakeup_spec_via_sel:
  assumes sel: "map_sel' ws_\<alpha> ws_invar ws_sel"
  shows "pick_wakeup_spec (pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))) \<sigma>_invar ws_\<alpha> ws_invar"
proof -
  interpret ws: map_sel' ws_\<alpha> ws_invar ws_sel by(rule sel)
  show ?thesis
    by(unfold_locales)(auto simp add: pick_wakeup_via_sel_def ran_def dest: ws.sel'_noneD ws.sel'_SomeD)
qed

locale scheduler_ext_base =
  scheduler_base_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and thr_iterate :: "'m_t \<Rightarrow> ('t \<times> ('x \<times> 'l released_locks), 's_t) set_iterator"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  +
  fixes thr'_\<alpha> :: "'s_t \<Rightarrow> 't set"
  and thr'_invar :: "'s_t \<Rightarrow> bool"
  and thr'_empty :: "unit \<Rightarrow> 's_t"
  and thr'_ins_dj :: "'t \<Rightarrow> 's_t \<Rightarrow> 's_t"
begin

abbreviation pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
where "pick_wakeup \<equiv> pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))"

fun active_threads :: "('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 's_t"
where
  "active_threads (ls, (ts, m), ws, is) =
   thr_iterate ts (\<lambda>_. True)
      (\<lambda>(t, (x, ln)) ts'. if ln = no_wait_locks
                       then if Predicate.holds 
                               (do {
                                  (ta, _) \<leftarrow> r t (x, m);
                                  Predicate.if_pred (actions_ok (ls, (ts, m), ws, is) t ta)
                                })
                            then thr'_ins_dj t ts'
                            else ts'
                       else if \<not> waiting (ws_lookup t ws) \<and> may_acquire_all ls t ln then thr'_ins_dj t ts' else ts')
      (thr'_empty ())"

end

locale scheduler_aux =
  scheduler_base_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  thr: finite_map thr_\<alpha> thr_invar +
  thr: map_lookup thr_\<alpha> thr_invar thr_lookup +
  thr: map_update thr_\<alpha> thr_invar thr_update +
  ws: map ws_\<alpha> ws_invar +
  ws: map_lookup ws_\<alpha> ws_invar ws_lookup +
  "is": set is_\<alpha> is_invar +
  "is": set_memb is_\<alpha> is_invar is_memb +
  "is": set_ins is_\<alpha> is_invar is_ins +
  "is": set_delete is_\<alpha> is_invar is_delete
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
begin

lemma free_thread_id_correct [simp]:
  "thr_invar ts \<Longrightarrow> free_thread_id ts = FWThread.free_thread_id (thr_\<alpha> ts)"
by(auto simp add: free_thread_id_def fun_eq_iff thr.lookup_correct intro: free_thread_id.intros)

lemma redT_updT_correct [simp]:
  assumes "thr_invar ts"
  shows "thr_\<alpha> (redT_updT ts nta) = FWThread.redT_updT (thr_\<alpha> ts) nta"
  and "thr_invar (redT_updT ts nta)"
by(case_tac [!] nta)(simp_all add: thr.update_correct assms)

lemma redT_updTs_correct [simp]:
  assumes  "thr_invar ts"
  shows "thr_\<alpha> (redT_updTs ts ntas) = FWThread.redT_updTs (thr_\<alpha> ts) ntas"
  and "thr_invar (redT_updTs ts ntas)"
using assms
by(induct ntas arbitrary: ts)(simp_all add: redT_updTs_def)

lemma thread_ok_correct [simp]:
  "thr_invar ts \<Longrightarrow> thread_ok ts nta \<longleftrightarrow> FWThread.thread_ok (thr_\<alpha> ts) nta"
by(cases nta) simp_all

lemma thread_oks_correct [simp]:
  "thr_invar ts \<Longrightarrow> thread_oks ts ntas \<longleftrightarrow> FWThread.thread_oks (thr_\<alpha> ts) ntas"
by(induct ntas arbitrary: ts) simp_all

lemma wset_actions_ok_correct [simp]:
  "ws_invar ws \<Longrightarrow> wset_actions_ok ws t was \<longleftrightarrow> FWWait.wset_actions_ok (ws_\<alpha> ws) t was"
by(simp add: wset_actions_ok_def FWWait.wset_actions_ok_def ws.lookup_correct)

lemma cond_action_ok_correct [simp]:
  "state_invar s \<Longrightarrow> cond_action_ok s t cta \<longleftrightarrow> \<alpha>.cond_action_ok (state_\<alpha> s) t cta"
by(cases s,cases cta)(auto simp add: thr.lookup_correct ws.lookup_correct)

lemma cond_action_oks_correct [simp]:
  assumes "state_invar s"
  shows "cond_action_oks s t ctas \<longleftrightarrow> \<alpha>.cond_action_oks (state_\<alpha> s) t ctas"
by(induct ctas)(simp_all add: cond_action_oks_def assms)

lemma redT_updI_correct [simp]:
  assumes "is_invar is"
  shows "is_\<alpha> (redT_updI is ia) = FWInterrupt.redT_updI (is_\<alpha> is) ia"
  and "is_invar (redT_updI is ia)"
using assms
by(case_tac [!] ia)(auto simp add: is.ins_correct is.delete_correct)

lemma redT_updIs_correct [simp]:
  assumes "is_invar is"
  shows "is_\<alpha> (redT_updIs is ias) = FWInterrupt.redT_updIs (is_\<alpha> is) ias"
  and "is_invar (redT_updIs is ias)"
using assms
by(induct ias arbitrary: "is")(auto)

lemma interrupt_action_ok_correct [simp]:
  "is_invar is \<Longrightarrow> interrupt_action_ok is ia \<longleftrightarrow> FWInterrupt.interrupt_action_ok (is_\<alpha> is) ia"
by(cases ia)(auto simp add: is.memb_correct)

lemma interrupt_actions_ok_correct [simp]:
  "is_invar is \<Longrightarrow> interrupt_actions_ok is ias \<longleftrightarrow> FWInterrupt.interrupt_actions_ok (is_\<alpha> is) ias"
by(induct ias arbitrary:"is") simp_all

lemma actions_ok_correct [simp]:
  "state_invar s \<Longrightarrow> actions_ok s t ta \<longleftrightarrow> \<alpha>.actions_ok (state_\<alpha> s) t ta"
by(auto simp add: actions_ok_def)

end

locale scheduler =
  scheduler_base 
    final r convert_RA
    schedule "output" pick_wakeup \<sigma>_invar
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  scheduler_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  scheduler_spec
    final r convert_RA
    schedule \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
    invariant
  +
  pick_wakeup_spec
    final r convert_RA
    pick_wakeup \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
  +
  ws: map_update ws_\<alpha> ws_invar ws_update +
  ws: map_delete ws_\<alpha> ws_invar ws_delete +
  ws: map_iteratei ws_\<alpha> ws_invar ws_iterate 
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler"
  and "output" :: "'s \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and pick_wakeup :: "'s \<Rightarrow> 't \<Rightarrow> 'w \<Rightarrow> 'm_w \<Rightarrow> 't option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and invariant :: "('l,'t,'x,'m,'w) state set"
  +
  assumes invariant: "invariant3p \<alpha>.redT invariant"
begin

lemma exec_updW_correct:
  assumes invar: "ws_invar ws" "\<sigma>_invar \<sigma> T" "dom (ws_\<alpha> ws) \<subseteq> T" "t \<in> T"
  shows "redT_updW t (ws_\<alpha> ws) wa (ws_\<alpha> (exec_updW \<sigma> t ws wa))" (is "?thesis1")
  and "ws_invar (exec_updW \<sigma> t ws wa)" (is "?thesis2")
proof -
  from invar have "?thesis1 \<and> ?thesis2"
  proof(cases wa)
    case [simp]: (Notify w)
    show ?thesis
    proof(cases "pick_wakeup \<sigma> t w ws")
      case (Some t')
      hence "ws_\<alpha> ws t' = \<lfloor>InWS w\<rfloor>" using invar by(rule pick_wakeup_SomeD)
      with Some show ?thesis using invar by(auto simp add: ws.update_correct)
    next
      case None
      hence "InWS w \<notin> ran (ws_\<alpha> ws)" using invar by(rule pick_wakeup_NoneD)
      with None show ?thesis using invar by(auto simp add: ran_def)
    qed
  next
    case [simp]: (NotifyAll w)
    let ?f = "\<lambda>(t, w') ws'. if w' = InWS w then ws_update t (PostWS WSNotified) ws' else ws'"
    let ?I = "\<lambda>T ws'. (\<forall>k. if k\<notin>T \<and> ws_\<alpha> ws k = \<lfloor>InWS w\<rfloor> then ws_\<alpha> ws' k = \<lfloor>PostWS WSNotified\<rfloor> else ws_\<alpha> ws' k = ws_\<alpha> ws k) \<and> ws_invar ws'"
    from invar have "?I (dom (ws_\<alpha> ws)) ws" by(auto simp add: ws.lookup_correct)
    with \<open>ws_invar ws\<close> have "?I {} (ws_iterate ws (\<lambda>_. True) ?f ws)"
    proof(rule ws.iterate_rule_P[where I="?I"])
      fix t w' T ws'
      assume t: "t \<in> T" and w': "ws_\<alpha> ws t = \<lfloor>w'\<rfloor>"
        and T: "T \<subseteq> dom (ws_\<alpha> ws)" and I: "?I T ws'"
      { fix t'
        assume "t' \<notin> T - {t}" "ws_\<alpha> ws t' = \<lfloor>InWS w\<rfloor>"
        with t I w' invar have "ws_\<alpha> (?f (t, w') ws') t' = \<lfloor>PostWS WSNotified\<rfloor>"
          by(auto)(simp_all add: ws.update_correct) }
      moreover {
        fix t'
        assume "t' \<in> T - {t} \<or> ws_\<alpha> ws t' \<noteq> \<lfloor>InWS w\<rfloor>"
        with t I w' invar have "ws_\<alpha> (?f (t,w') ws') t' = ws_\<alpha> ws t'"
          by(auto simp add: ws.update_correct) }
      moreover
      have "ws_invar (?f (t, w') ws')" using I by(simp add: ws.update_correct)
      ultimately show "?I (T - {t}) (?f (t, w') ws')" by safe simp
    qed
    hence "ws_\<alpha> (ws_iterate ws (\<lambda>_. True) ?f ws) = (\<lambda>t. if ws_\<alpha> ws t = \<lfloor>InWS w\<rfloor> then \<lfloor>PostWS WSNotified\<rfloor> else ws_\<alpha> ws t)"
      and "ws_invar (ws_iterate ws (\<lambda>_. True) ?f ws)" by(simp_all add: fun_eq_iff)
    thus ?thesis by simp
  next
    case WakeUp thus ?thesis using assms
      by(auto simp add: ws.lookup_correct ws.update_correct split: wait_set_status.split)
  qed(simp_all add: ws.update_correct ws.delete_correct map_upd_eq_restrict)
  thus ?thesis1 ?thesis2 by simp_all
qed

lemma exec_updWs_correct:
  assumes "ws_invar ws" "\<sigma>_invar \<sigma> T" "dom (ws_\<alpha> ws) \<subseteq> T" "t \<in> T"
  shows "redT_updWs t (ws_\<alpha> ws) was (ws_\<alpha> (exec_updWs \<sigma> t ws was))" (is "?thesis1")
  and "ws_invar (exec_updWs \<sigma> t ws was)" (is "?thesis2")
proof -
  from \<open>ws_invar ws\<close> \<open>dom (ws_\<alpha> ws) \<subseteq> T\<close> 
  have "?thesis1 \<and> ?thesis2"
  proof(induct was arbitrary: ws)
    case Nil thus ?case by(auto simp add: exec_updWs_def redT_updWs_def)
  next
    case (Cons wa was)
    let ?ws' = "exec_updW \<sigma> t ws wa"
    from \<open>ws_invar ws\<close> \<open>\<sigma>_invar \<sigma> T\<close> \<open>dom (ws_\<alpha> ws) \<subseteq> T\<close> \<open>t \<in> T\<close>
    have invar': "ws_invar ?ws'" and red: "redT_updW t (ws_\<alpha> ws) wa (ws_\<alpha> ?ws')"
      by(rule exec_updW_correct)+
    have "dom (ws_\<alpha> ?ws') \<subseteq> T"
    proof
      fix t' assume "t' \<in> dom (ws_\<alpha> ?ws')"
      with red have "t' \<in> dom (ws_\<alpha> ws) \<or> t = t'"
        by(auto dest!: redT_updW_Some_otherD split: wait_set_status.split_asm)
      with \<open>dom (ws_\<alpha> ws) \<subseteq> T\<close> \<open>t \<in> T\<close> show "t' \<in> T" by auto
    qed
    with invar' have "redT_updWs t (ws_\<alpha> ?ws') was (ws_\<alpha> (exec_updWs \<sigma> t ?ws' was)) \<and> ws_invar (exec_updWs \<sigma> t ?ws' was)"
      by(rule Cons.hyps)
    thus ?case using red
      by(auto simp add: exec_updWs_def redT_updWs_def intro: rtrancl3p_step_converse)
  qed
  thus ?thesis1 ?thesis2 by simp_all
qed

lemma exec_upd_correct:
  assumes "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "t \<in> (dom (thr_\<alpha> (thr s)))"
  and "wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))"
  shows "redT_upd (state_\<alpha> s) t ta x' m' (state_\<alpha> (exec_upd \<sigma> s t ta x' m'))"
  and "state_invar (exec_upd \<sigma> s t ta x' m')"
using assms unfolding wset_thread_ok_conv_dom
by(auto simp add: thr.update_correct thr.lookup_correct intro: exec_updWs_correct)

lemma execT_None:
  assumes invar: "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_\<alpha> s \<in> invariant"
  and exec: "execT \<sigma> s = None"
  shows "\<alpha>.active_threads (state_\<alpha> s) = {}"
using assms
by(cases "schedule \<sigma> s")(fastforce simp add: execT_def thr.lookup_correct dest: schedule_Some_NoneD schedule_NoneD)+

lemma execT_Some:
  assumes invar: "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_\<alpha> s \<in> invariant"
  and wstok: "wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))"
  and exec: "execT \<sigma> s = \<lfloor>(\<sigma>', t, ta, s')\<rfloor>"
  shows "\<alpha>.redT (state_\<alpha> s) (t, ta) (state_\<alpha> s')" (is "?thesis1")
  and "state_invar s'" (is "?thesis2")
  and "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" (is "?thesis3")
proof -
  note [simp del] = redT_upd_simps exec_upd_def

  have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
  proof(cases "fst (snd (the (schedule \<sigma> s)))")
    case None
    with exec invar have schedule: "schedule \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
      and ta: "ta = (K$ [], [], [], [], [], convert_RA (snd (the (thr_\<alpha> (thr s) t))))"
      and s': "s' = (acquire_all (locks s) t (snd (the (thr_\<alpha> (thr s) t))), (thr_update t (fst (the (thr_\<alpha> (thr s) t)), no_wait_locks) (thr s), shr s), wset s, interrupts s)"
      by(auto simp add: execT_def Option_bind_eq_Some_conv thr.lookup_correct split_beta split del: option.split_asm)
    from schedule_Some_NoneD[OF schedule invar]

    obtain x ln n where t: "thr_\<alpha> (thr s) t = \<lfloor>(x, ln)\<rfloor>"
      and "0 < ln $ n" "\<not> waiting (ws_\<alpha> (wset s) t)" "may_acquire_all (locks s) t ln" by blast
    hence ?thesis1 using ta s' invar by(auto intro: \<alpha>.redT.redT_acquire simp add: thr.update_correct)
    moreover from invar s' have "?thesis2" by(simp add: thr.update_correct)
    moreover from t s' invar have "dom (thr_\<alpha> (thr s')) = dom (thr_\<alpha> (thr s))" by(auto simp add: thr.update_correct)
    hence "?thesis3" using invar schedule by(auto intro: schedule_invar_None)
    ultimately show ?thesis by simp
  next
    case (Some taxm)
    with exec invar obtain x' m' 
      where schedule: "schedule \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
      and s': "s' = exec_upd \<sigma> s t ta x' m'"
      by(cases taxm)(fastforce simp add: execT_def Option_bind_eq_Some_conv split del: option.split_asm)
    from schedule_Some_SomeD[OF schedule invar]
    obtain x where t: "thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor>" 
      and "Predicate.eval (r t (x, shr s)) (ta, x', m')" 
      and aok: "\<alpha>.actions_ok (state_\<alpha> s) t ta" by blast
    with s' have ?thesis1 using invar wstok
      by(fastforce intro: \<alpha>.redT.intros exec_upd_correct)
    moreover from invar s' t wstok have ?thesis2 by(auto intro: exec_upd_correct)
    moreover {
      from schedule invar
      have "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"
        by(rule schedule_invar_Some)
      also have "dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>} = dom (thr_\<alpha> (thr s'))"
        using invar s' aok t
        by(auto simp add: exec_upd_def thr.lookup_correct thr.update_correct simp del: split_paired_Ex)(fastforce dest: redT_updTs_new_thread intro: redT_updTs_Some1 redT_updTs_new_thread_ts simp del: split_paired_Ex)+
      finally have "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" . }
    ultimately show ?thesis by simp
  qed
  thus ?thesis1 ?thesis2 ?thesis3 by simp_all
qed

lemma exec_step_into_redT:
  assumes invar: "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_\<alpha> s \<in> invariant"
  and wstok: "wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))"
  and exec: "exec_step (\<sigma>, s) = Inl ((\<sigma>'', t, ta), \<sigma>', s')"
  shows "\<alpha>.redT (state_\<alpha> s) (t, ta) (state_\<alpha> s')" "\<sigma>'' = \<sigma>"
  and "state_invar s'" "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" "state_\<alpha> s' \<in> invariant"
proof -
  from exec have execT: "execT \<sigma> s = \<lfloor>(\<sigma>', t, ta, s')\<rfloor>" 
    and q: "\<sigma>'' = \<sigma>" by(auto simp add: exec_step.simps split_beta)
  from invar wstok execT show red: "\<alpha>.redT (state_\<alpha> s) (t, ta) (state_\<alpha> s')" 
    and invar': "state_invar s'" "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" "\<sigma>'' = \<sigma>"
    by(rule execT_Some)+(rule q)
  from invariant red \<open>state_\<alpha> s \<in> invariant\<close> 
  show "state_\<alpha> s' \<in> invariant" by(rule invariant3pD)
qed

lemma exec_step_InrD:
  assumes "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_\<alpha> s \<in> invariant"
  and "exec_step (\<sigma>, s) = Inr s'"
  shows "\<alpha>.active_threads (state_\<alpha> s) = {}"
  and "s' = s"
using assms
by(auto simp add: exec_step_def dest: execT_None)

lemma (in multithreaded_base) red_in_active_threads:
  assumes "s -t\<triangleright>ta\<rightarrow> s'"
  shows "t \<in> active_threads s"
using assms
by cases(auto intro: active_threads.intros)

lemma exec_aux_into_Runs:
  assumes "state_invar s" "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_\<alpha> s \<in> invariant"
  and "wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))"
  shows "\<alpha>.mthr.Runs (state_\<alpha> s) (lmap snd (llist_of_tllist (exec_aux (\<sigma>, s))))" (is ?thesis1)
  and "tfinite (exec_aux (\<sigma>, s)) \<Longrightarrow> state_invar (terminal (exec_aux (\<sigma>, s)))" (is "_ \<Longrightarrow> ?thesis2")
proof -
  from assms show ?thesis1
  proof(coinduction arbitrary: \<sigma> s) 
    case (Runs \<sigma> s)
    note invar = \<open>state_invar s\<close> \<open>\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))\<close> \<open>state_\<alpha> s \<in> invariant\<close>
      and wstok = \<open>wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))\<close>
    show ?case
    proof(cases "exec_aux (\<sigma>, s)")
      case (TNil s')
      hence "\<alpha>.active_threads (state_\<alpha> s) = {}" "s' = s"
        by(auto simp add: exec_aux_def unfold_tllist' split: sum.split_asm dest: exec_step_InrD[OF invar])
      hence ?Stuck using TNil by(auto dest: \<alpha>.red_in_active_threads)
      thus ?thesis ..
    next
      case (TCons \<sigma>tta ttls')
      then obtain t ta \<sigma>' s' \<sigma>''
        where [simp]: "\<sigma>tta = (\<sigma>'', t, ta)"
        and [simp]: "ttls' = exec_aux (\<sigma>', s')"
        and step: "exec_step (\<sigma>, s) = Inl ((\<sigma>'', t, ta), \<sigma>', s')"
        unfolding exec_aux_def by(subst (asm) (2) unfold_tllist')(fastforce split: sum.split_asm)
      from invar wstok step
      have redT: "\<alpha>.redT (state_\<alpha> s) (t, ta) (state_\<alpha> s')"
        and [simp]: "\<sigma>'' = \<sigma>"
        and invar': "state_invar s'" "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" "state_\<alpha> s' \<in> invariant"
        by(rule exec_step_into_redT)+
      from wstok \<alpha>.redT_preserves_wset_thread_ok[OF redT]
      have "wset_thread_ok (ws_\<alpha> (wset s')) (thr_\<alpha> (thr s'))" by simp
      with invar' redT TCons have ?Step by(auto simp del: split_paired_Ex)
      thus ?thesis ..
    qed
  qed
next
  assume "tfinite (exec_aux (\<sigma>, s))"
  thus "?thesis2" using assms
  proof(induct "exec_aux (\<sigma>, s)" arbitrary: \<sigma> s rule: tfinite_induct)
    case TNil thus ?case
      by(auto simp add: exec_aux_def unfold_tllist' split_beta split: sum.split_asm dest: exec_step_InrD)
  next
    case (TCons \<sigma>tta ttls)
    from \<open>TCons \<sigma>tta ttls = exec_aux (\<sigma>, s)\<close>
    obtain \<sigma>'' t ta \<sigma>' s' 
      where [simp]: "\<sigma>tta = (\<sigma>'', t, ta)"
      and ttls: "ttls = exec_aux (\<sigma>', s')"
      and step: "exec_step (\<sigma>, s) = Inl ((\<sigma>'', t, ta), \<sigma>', s')"
      unfolding exec_aux_def by(subst (asm) (2) unfold_tllist')(fastforce split: sum.split_asm)
    note ttls moreover
    from \<open>state_invar s\<close> \<open>\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))\<close> \<open>state_\<alpha> s \<in> invariant\<close> \<open>wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))\<close> step
    have [simp]: "\<sigma>'' = \<sigma>"
      and invar': "state_invar s'" "\<sigma>_invar \<sigma>' (dom (thr_\<alpha> (thr s')))" "state_\<alpha> s' \<in> invariant"
      and redT: "\<alpha>.redT (state_\<alpha> s) (t, ta) (state_\<alpha> s')"
      by(rule exec_step_into_redT)+
    note invar' moreover
    from \<alpha>.redT_preserves_wset_thread_ok[OF redT] \<open>wset_thread_ok (ws_\<alpha> (wset s)) (thr_\<alpha> (thr s))\<close>
    have "wset_thread_ok (ws_\<alpha> (wset s')) (thr_\<alpha> (thr s'))" by simp
    ultimately have "state_invar (terminal (exec_aux (\<sigma>', s')))" by(rule TCons)
    with \<open>TCons \<sigma>tta ttls = exec_aux (\<sigma>, s)\<close>[symmetric]
    show ?case unfolding ttls by simp
  qed
qed

end

locale scheduler_ext_aux =
  scheduler_ext_base
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update thr_iterate
    ws_\<alpha> ws_invar ws_lookup ws_update ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    thr'_\<alpha> thr'_invar thr'_empty thr'_ins_dj
  +
  scheduler_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  thr: map_iteratei thr_\<alpha> thr_invar thr_iterate +
  ws: map_update ws_\<alpha> ws_invar ws_update +
  ws: map_sel' ws_\<alpha> ws_invar ws_sel +
  thr': finite_set thr'_\<alpha> thr'_invar +
  thr': set_empty thr'_\<alpha> thr'_invar thr'_empty +
  thr': set_ins_dj thr'_\<alpha> thr'_invar thr'_ins_dj  
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and thr_iterate :: "'m_t \<Rightarrow> ('t \<times> ('x \<times> 'l released_locks), 's_t) set_iterator"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_sel :: "'m_w \<Rightarrow> (('t \<times> 'w wait_set_status) \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and thr'_\<alpha> :: "'s_t \<Rightarrow> 't set"
  and thr'_invar :: "'s_t \<Rightarrow> bool"
  and thr'_empty :: "unit \<Rightarrow> 's_t"
  and thr'_ins_dj :: "'t \<Rightarrow> 's_t \<Rightarrow> 's_t"
begin

lemma active_threads_correct [simp]:
  assumes "state_invar s"
  shows "thr'_\<alpha> (active_threads s) = \<alpha>.active_threads (state_\<alpha> s)" (is "?thesis1")
  and "thr'_invar (active_threads s)" (is "?thesis2")
proof -
  obtain ls ts m ws "is" where s: "s = (ls, (ts, m), ws, is)" by(cases s) fastforce
  let ?f = "\<lambda>(t, (x, ln)) TS. if ln = no_wait_locks
           then if Predicate.holds (do { (ta, _) \<leftarrow> r t (x, m); Predicate.if_pred (actions_ok (ls, (ts, m), ws, is) t ta) })
                then thr'_ins_dj t TS else TS
           else if \<not> waiting (ws_lookup t ws) \<and> may_acquire_all ls t ln then thr'_ins_dj t TS else TS"
  let ?I = "\<lambda>T TS. thr'_invar TS \<and> thr'_\<alpha> TS \<subseteq> dom (thr_\<alpha> ts) - T \<and> (\<forall>t. t \<notin> T \<longrightarrow> t \<in> thr'_\<alpha> TS \<longleftrightarrow> t \<in> \<alpha>.active_threads (state_\<alpha> s))"

  from assms s have "thr_invar ts" by simp
  moreover have "?I (dom (thr_\<alpha> ts)) (thr'_empty ())"
    by(auto simp add: thr'.empty_correct s elim: \<alpha>.active_threads.cases)
  ultimately have "?I {} (thr_iterate ts (\<lambda>_. True) ?f (thr'_empty ()))"
  proof(rule thr.iterate_rule_P[where I="?I"])
    fix t xln T TS
    assume tT: "t \<in> T" 
      and tst: "thr_\<alpha> ts t = \<lfloor>xln\<rfloor>"
      and Tdom: "T \<subseteq> dom (thr_\<alpha> ts)"
      and I: "?I T TS"
    obtain x ln where xln: "xln = (x, ln)" by(cases xln)
    from tT I have t: "t \<notin> thr'_\<alpha> TS" by blast

    from I have invar: "thr'_invar TS" ..
    hence "thr'_invar (?f (t, xln) TS)" using t
      unfolding xln by(auto simp add: thr'.ins_dj_correct)
    moreover from I have "thr'_\<alpha> TS \<subseteq> dom (thr_\<alpha> ts) - T" by blast
    hence "thr'_\<alpha> (?f (t, xln) TS) \<subseteq> dom (thr_\<alpha> ts) - (T - {t})"
      using invar tst t by(auto simp add: xln thr'.ins_dj_correct)
    moreover
    {
      fix t'
      assume t': "t' \<notin> T - {t}"
      have "t' \<in> thr'_\<alpha> (?f (t, xln) TS) \<longleftrightarrow> t' \<in> \<alpha>.active_threads (state_\<alpha> s)" (is "?lhs \<longleftrightarrow> ?rhs")
      proof(cases "t' = t")
        case True
        show ?thesis
        proof
          assume ?lhs
          with True xln invar tst \<open>state_invar s\<close> t show ?rhs
            by(fastforce simp add: holds_eq thr'.ins_dj_correct s split_beta ws.lookup_correct split: if_split_asm elim!: bindE if_predE intro: \<alpha>.active_threads.intros)
        next
          assume ?rhs
          with True xln invar tst \<open>state_invar s\<close> t show ?lhs
            by(fastforce elim!: \<alpha>.active_threads.cases simp add: holds_eq s thr'.ins_dj_correct ws.lookup_correct elim!: bindE if_predE intro: bindI if_predI)
        qed
      next
        case False
        with t' have "t' \<notin> T" by simp
        with I have "t' \<in> thr'_\<alpha> TS \<longleftrightarrow> t' \<in> \<alpha>.active_threads (state_\<alpha> s)" by blast
        thus ?thesis using xln False invar t by(auto simp add: thr'.ins_dj_correct)
      qed
    }
    ultimately show "?I (T - {t}) (?f (t, xln) TS)" by blast
  qed
  thus "?thesis1" "?thesis2" by(auto simp add: s)
qed

end

locale scheduler_ext =
  scheduler_ext_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update thr_iterate
    ws_\<alpha> ws_invar ws_lookup ws_update ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    thr'_\<alpha> thr'_invar thr'_empty thr'_ins_dj
  +
  scheduler_spec
    final r convert_RA
    schedule \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
    invariant
  +
  ws: map_delete ws_\<alpha> ws_invar ws_delete +
  ws: map_iteratei ws_\<alpha> ws_invar ws_iterate
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and schedule :: "('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'s) scheduler"
  and "output" :: "'s \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and \<sigma>_invar :: "'s \<Rightarrow> 't set \<Rightarrow> bool"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and thr_iterate :: "'m_t \<Rightarrow> ('t \<times> ('x \<times> 'l released_locks), 's_t) set_iterator"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_empty :: "unit \<Rightarrow> 'm_w"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and thr'_\<alpha> :: "'s_t \<Rightarrow> 't set"
  and thr'_invar :: "'s_t \<Rightarrow> bool"
  and thr'_empty :: "unit \<Rightarrow> 's_t"
  and thr'_ins_dj :: "'t \<Rightarrow> 's_t \<Rightarrow> 's_t"
  and invariant :: "('l,'t,'x,'m,'w) state set"
  +
  assumes invariant: "invariant3p \<alpha>.redT invariant"

sublocale scheduler_ext < 
  pick_wakeup_spec
    final r convert_RA
    pick_wakeup \<sigma>_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
by(rule pick_wakeup_spec_via_sel)(unfold_locales)

sublocale scheduler_ext < 
  scheduler
    final r convert_RA
    schedule "output" "pick_wakeup" \<sigma>_invar
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
    is_\<alpha> is_invar is_memb is_ins is_delete
    invariant
by(unfold_locales)(rule invariant)

subsection \<open>Schedulers for deterministic small-step semantics\<close>

text \<open>
  The default code equations for @{term Predicate.the} impose the type class constraint \<open>eq\<close>
  on the predicate elements. For the semantics, which contains the heap, there might be no such
  instance, so we use new constants for which other code equations can be used.
  These do not add the type class constraint, but may fail more often with non-uniqueness exception.
\<close>

definition singleton2 where [simp]: "singleton2 = Predicate.singleton"
definition the_only2 where [simp]: "the_only2 = Predicate.the_only"
definition the2 where [simp]: "the2 = Predicate.the"

context multithreaded_base begin

definition step_thread ::
  "(('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 's) \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> 't
  \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 's) option"
where
  "\<And>ln. step_thread update_state s t =
   (case thr s t of
      \<lfloor>(x, ln)\<rfloor> \<Rightarrow>
      if ln = no_wait_locks then
        if \<exists>ta x' m'. t \<turnstile> (x, shr s) -ta\<rightarrow> (x', m') \<and> actions_ok s t ta then
          let
            (ta, x', m') = THE (ta, x', m'). t \<turnstile> (x, shr s) -ta\<rightarrow> (x', m') \<and> actions_ok s t ta
          in
            \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, update_state ta)\<rfloor>
        else
          None
      else if may_acquire_all (locks s) t ln \<and> \<not> waiting (wset s t) then 
        \<lfloor>(t, None, update_state (K$ [], [], [], [], [], convert_RA ln))\<rfloor>
      else
        None
    | None \<Rightarrow> None)"

lemma step_thread_NoneD:
  "step_thread update_state s t = None \<Longrightarrow> t \<notin> active_threads s"
unfolding step_thread_def 
by(fastforce simp add: split_beta elim!: active_threads.cases split: if_split_asm)

lemma inactive_step_thread_eq_NoneI:
  "t \<notin> active_threads s \<Longrightarrow> step_thread update_state s t = None"
unfolding step_thread_def
by(fastforce simp add: split_beta split: if_split_asm intro: active_threads.intros)

lemma step_thread_eq_None_conv:
  "step_thread update_state s t = None \<longleftrightarrow> t \<notin> active_threads s"
by(blast dest: step_thread_NoneD intro: inactive_step_thread_eq_NoneI)

lemma step_thread_eq_Some_activeD:
  "step_thread update_state s t = \<lfloor>(t', taxm\<sigma>')\<rfloor> 
  \<Longrightarrow> t' = t \<and> t \<in> active_threads s"
unfolding step_thread_def 
by(fastforce split: if_split_asm simp add: split_beta intro: active_threads.intros)

declare actions_ok_iff [simp del]
declare actions_ok.cases [rule del]

lemma step_thread_Some_NoneD:
  "step_thread update_state s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>
  \<Longrightarrow> \<exists>x ln n. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> ln $ n > 0 \<and> \<not> waiting (wset s t) \<and> may_acquire_all (locks s) t ln \<and> \<sigma>' = update_state (K$ [], [], [], [], [], convert_RA ln)"
unfolding step_thread_def
by(auto split: if_split_asm simp add: split_beta elim!: neq_no_wait_locksE)

lemma step_thread_Some_SomeD:
  "\<lbrakk> deterministic I; step_thread update_state s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>; s \<in> I \<rbrakk>
  \<Longrightarrow> \<exists>x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta \<and> \<sigma>' = update_state ta"
unfolding step_thread_def
by(auto simp add: split_beta deterministic_THE split: if_split_asm)

end

context scheduler_base_aux begin

definition step_thread ::
  "(('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 's) \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't \<Rightarrow>
   ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 's) option"
where 
  "\<And>ln. step_thread update_state s t =
  (case thr_lookup t (thr s) of
      \<lfloor>(x, ln)\<rfloor> \<Rightarrow>
      if ln = no_wait_locks then
        let
          reds = do {
            (ta, x', m') \<leftarrow> r t (x, shr s);
            if actions_ok s t ta then Predicate.single (ta, x', m') else bot
          }
        in
          if Predicate.holds (reds \<bind> (\<lambda>_. Predicate.single ())) then
            let
              (ta, x', m') = the2 reds
            in 
              \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, update_state ta)\<rfloor>
          else
            None
      else if may_acquire_all (locks s) t ln \<and> \<not> waiting (ws_lookup t (wset s)) then 
        \<lfloor>(t, None, update_state (K$ [], [], [], [], [],convert_RA ln))\<rfloor>
      else
        None
    | None \<Rightarrow> None)"

end

context scheduler_aux begin

lemma deterministic_THE2:
  assumes "\<alpha>.deterministic I"
  and tst: "thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  and red: "Predicate.eval (r t (x, shr s)) (ta, x', m')"
  and aok: "\<alpha>.actions_ok (state_\<alpha> s) t ta"
  and I: "state_\<alpha> s \<in> I"
  shows "Predicate.the (r t (x, shr s) \<bind> (\<lambda>(ta, x', m'). if \<alpha>.actions_ok (state_\<alpha> s) t ta then Predicate.single (ta, x', m') else bot)) = (ta, x', m')"
proof -
  show ?thesis unfolding the_def
    apply(rule the_equality)
     apply(rule bindI[OF red])
     apply(simp add: singleI aok)
    apply(erule bindE)
    apply(clarsimp split: if_split_asm)
     apply(drule (1) \<alpha>.deterministicD[OF \<open>\<alpha>.deterministic I\<close>, where s="state_\<alpha> s", simplified, OF red _ tst aok])
      apply(rule I)
     apply simp
    done
qed

lemma step_thread_correct:
  assumes det: "\<alpha>.deterministic I"
  and invar: "\<sigma>_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  shows
  "map_option (apsnd (apsnd \<sigma>_\<alpha>)) (step_thread update_state s t) = \<alpha>.step_thread (\<sigma>_\<alpha> \<circ> update_state) (state_\<alpha> s) t" (is ?thesis1)
  and "(\<And>ta. FWThread.thread_oks (thr_\<alpha> (thr s)) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<Longrightarrow> \<sigma>_invar (update_state ta) (dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})) \<Longrightarrow> case_option True (\<lambda>(t, taxm, \<sigma>). \<sigma>_invar \<sigma> (case taxm of None \<Rightarrow> dom (thr_\<alpha> (thr s)) | Some (ta, x', m') \<Rightarrow> dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})) (step_thread update_state s t)"
  (is "(\<And>ta. ?tso ta \<Longrightarrow> ?inv ta) \<Longrightarrow> ?thesis2")
proof -
  have "?thesis1 \<and> ((\<forall>ta. ?tso ta \<longrightarrow> ?inv ta) \<longrightarrow> ?thesis2)"
  proof(cases "step_thread update_state s t")
    case None
    with invar show ?thesis
      apply (auto simp add: thr.lookup_correct \<alpha>.step_thread_def step_thread_def ws.lookup_correct
        split_beta holds_eq split: if_split_asm cong del: image_cong_simp)
       apply metis
      apply metis
      done
  next
    case (Some a)
    then obtain t' taxm \<sigma>' 
      where rrs: "step_thread update_state s t = \<lfloor>(t', taxm, \<sigma>')\<rfloor>" by(cases a) auto
    show ?thesis
    proof(cases "taxm")
      case None
      with rrs invar have ?thesis1
        by(auto simp add: thr.lookup_correct ws.lookup_correct \<alpha>.step_thread_def step_thread_def split_beta split: if_split_asm)
      moreover {
        let ?ta = "(K$ [], [], [], [], [], convert_RA (snd (the (thr_lookup t (thr s)))))"
        assume "?tso ?ta \<longrightarrow> ?inv ?ta"
        hence ?thesis2 using None rrs
          by(auto simp add: thr.lookup_correct ws.lookup_correct \<alpha>.step_thread_def step_thread_def split_beta split: if_split_asm) }
      ultimately show ?thesis by blast
    next
      case (Some a)
      with rrs obtain ta x' m'
        where rrs: "step_thread update_state s t =  \<lfloor>(t', \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
        by(cases a) fastforce
      with invar have ?thesis1 
        by (auto simp add: thr.lookup_correct ws.lookup_correct \<alpha>.step_thread_def step_thread_def
          split_beta \<alpha>.deterministic_THE [OF det, where s="state_\<alpha> s", simplified]
          deterministic_THE2[OF det] holds_eq split: if_split_asm
          cong del: image_cong_simp) blast+
      moreover {
        assume "?tso ta \<longrightarrow> ?inv ta"
        hence ?thesis2 using rrs invar
          by(auto simp add: thr.lookup_correct ws.lookup_correct \<alpha>.step_thread_def step_thread_def split_beta \<alpha>.deterministic_THE[OF det, where s="state_\<alpha> s", simplified] deterministic_THE2[OF det] holds_eq split: if_split_asm)(auto simp add: \<alpha>.actions_ok_iff) 
      }
      ultimately show ?thesis by blast
    qed
  qed
  thus ?thesis1 "(\<And>ta. ?tso ta \<Longrightarrow> ?inv ta) \<Longrightarrow> ?thesis2" by blast+
qed

lemma step_thread_eq_None_conv:
  assumes det: "\<alpha>.deterministic I"
  and invar: "state_invar s" "state_\<alpha> s \<in> I"
  shows "step_thread update_state s t = None \<longleftrightarrow> t \<notin> \<alpha>.active_threads (state_\<alpha> s)"
using assms step_thread_correct(1)[OF det _ invar(1), of "\<lambda>_ _. True", of id update_state t]
by(simp add: map_option.id \<alpha>.step_thread_eq_None_conv)

lemma step_thread_Some_NoneD:
  assumes det: "\<alpha>.deterministic I"
  and step: "step_thread update_state s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>"
  and invar: "state_invar s" "state_\<alpha> s \<in> I"
  shows "\<exists>x ln n. thr_\<alpha> (thr s) t = \<lfloor>(x, ln)\<rfloor> \<and> ln $ n > 0 \<and> \<not> waiting (ws_\<alpha> (wset s) t) \<and> may_acquire_all (locks s) t ln \<and> \<sigma>' = update_state (K$ [], [], [], [], [], convert_RA ln)"
using assms step_thread_correct(1)[OF det _ invar(1), of "\<lambda>_ _. True", of id update_state t']
by(fastforce simp add: map_option.id dest: \<alpha>.step_thread_Some_NoneD[OF sym])

lemma step_thread_Some_SomeD:
  assumes det: "\<alpha>.deterministic I"
  and step: "step_thread update_state s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
  and invar: "state_invar s" "state_\<alpha> s \<in> I"
  shows "\<exists>x. thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> Predicate.eval (r t (x, shr s)) (ta, x', m') \<and> actions_ok s t ta \<and> \<sigma>' = update_state ta"
using assms step_thread_correct(1)[OF det _ invar(1), of "\<lambda>_ _. True", of id update_state t']
by(auto simp add: map_option.id dest: \<alpha>.step_thread_Some_SomeD[OF det sym])

end

subsection \<open>Code Generator setup\<close>

lemmas [code] =
  scheduler_base_aux.free_thread_id_def
  scheduler_base_aux.redT_updT.simps
  scheduler_base_aux.redT_updTs_def
  scheduler_base_aux.thread_ok.simps
  scheduler_base_aux.thread_oks.simps
  scheduler_base_aux.wset_actions_ok_def
  scheduler_base_aux.cond_action_ok.simps
  scheduler_base_aux.cond_action_oks_def
  scheduler_base_aux.redT_updI.simps
  scheduler_base_aux.redT_updIs.simps
  scheduler_base_aux.interrupt_action_ok.simps
  scheduler_base_aux.interrupt_actions_ok.simps
  scheduler_base_aux.actions_ok_def
  scheduler_base_aux.step_thread_def

lemmas [code] =
  scheduler_base.exec_updW.simps
  scheduler_base.exec_updWs_def
  scheduler_base.exec_upd_def
  scheduler_base.execT_def
  scheduler_base.exec_step.simps
  scheduler_base.exec_aux_def
  scheduler_base.exec_def

lemmas [code] =
  scheduler_ext_base.active_threads.simps

lemma singleton2_code [code]:
  "singleton2 dfault (Predicate.Seq f) =
  (case f () of
    Predicate.Empty \<Rightarrow> dfault ()
  | Predicate.Insert x P \<Rightarrow> 
    if Predicate.is_empty P then x else Code.abort (STR ''singleton2 not unique'') (\<lambda>_. singleton2 dfault (Predicate.Seq f))
  | Predicate.Join P xq \<Rightarrow>
    if Predicate.is_empty P then 
      the_only2 dfault xq
    else if Predicate.null xq then singleton2 dfault P else Code.abort (STR ''singleton2 not unique'') (\<lambda>_. singleton2 dfault (Predicate.Seq f)))"
unfolding singleton2_def the_only2_def
by(auto simp only: singleton_code Code.abort_def split: seq.split if_split)

lemma the_only2_code [code]:
  "the_only2 dfault Predicate.Empty = Code.abort (STR ''the_only2 empty'') dfault"
  "the_only2 dfault (Predicate.Insert x P) = 
  (if Predicate.is_empty P then x else Code.abort (STR ''the_only2 not unique'') (\<lambda>_. the_only2 dfault (Predicate.Insert x P)))"
  "the_only2 dfault (Predicate.Join P xq) = 
  (if Predicate.is_empty P then 
     the_only2 dfault xq
   else if Predicate.null xq then 
     singleton2 dfault P 
   else
     Code.abort (STR ''the_only2 not unique'') (\<lambda>_. the_only2 dfault (Predicate.Join P xq)))"
unfolding singleton2_def the_only2_def by simp_all

lemma the2_eq [code]:
  "the2 A = singleton2 (\<lambda>x. Code.abort (STR ''not_unique'') (\<lambda>_. the2 A)) A"
unfolding the2_def singleton2_def by(rule the_eq)

end
