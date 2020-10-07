(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

chapter \<open>The generic multithreaded semantics\<close>

section \<open>State of the multithreaded semantics\<close>

theory FWState
imports 
  "../Basic/Auxiliary"
begin

datatype lock_action =
    Lock
  | Unlock
  | UnlockFail
  | ReleaseAcquire

datatype ('t,'x,'m) new_thread_action =
    NewThread 't 'x 'm
  | ThreadExists 't bool

datatype 't conditional_action = 
    Join 't
  | Yield

datatype ('t, 'w) wait_set_action =
    Suspend 'w
  | Notify 'w
  | NotifyAll 'w
  | WakeUp 't
  | Notified
  | WokenUp

datatype 't interrupt_action 
  = IsInterrupted 't bool
  | Interrupt 't
  | ClearInterrupt 't

type_synonym 'l lock_actions = "'l \<Rightarrow>f lock_action list"

translations
  (type) "'l lock_actions" <= (type) "'l \<Rightarrow>f lock_action list"

type_synonym
  ('l,'t,'x,'m,'w,'o) thread_action =
  "'l lock_actions \<times> ('t,'x,'m) new_thread_action list \<times>
   't conditional_action list \<times> ('t, 'w) wait_set_action list \<times> 
   't interrupt_action list \<times> 'o list"
(* pretty printing for thread_action type *)
print_translation \<open>
  let
    fun tr'
       [Const (@{type_syntax finfun}, _) $ l $
          (Const (@{type_syntax list}, _) $ Const (@{type_syntax lock_action}, _)),
        Const (@{type_syntax "prod"}, _) $
          (Const (@{type_syntax list}, _) $ (Const (@{type_syntax new_thread_action}, _) $ t1 $ x $ m)) $
          (Const (@{type_syntax "prod"}, _) $
            (Const (@{type_syntax list}, _) $ (Const (@{type_syntax conditional_action}, _) $ t2)) $
            (Const (@{type_syntax "prod"}, _) $
              (Const (@{type_syntax list}, _) $ (Const (@{type_syntax wait_set_action}, _) $ t3 $ w)) $ 
              (Const (@{type_syntax "prod"}, _) $
                 (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "interrupt_action"}, _) $ t4)) $
                 (Const (@{type_syntax "list"}, _) $ o1))))] =
      if t1 = t2 andalso t2 = t3 andalso t3 = t4 then Syntax.const @{type_syntax thread_action} $ l $ t1 $ x $ m $ w $ o1
      else raise Match;
  in [(@{type_syntax "prod"}, K tr')]
  end
\<close>
typ "('l,'t,'x,'m,'w,'o) thread_action"
 
definition locks_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'l lock_actions" ("\<lbrace>_\<rbrace>\<^bsub>l\<^esub>" [0] 1000) where
  "locks_a \<equiv> fst"

definition thr_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action list" ("\<lbrace>_\<rbrace>\<^bsub>t\<^esub>" [0] 1000) where
  "thr_a \<equiv> fst o snd"

definition cond_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action list" ("\<lbrace>_\<rbrace>\<^bsub>c\<^esub>" [0] 1000) where
  "cond_a = fst o snd o snd"

definition wset_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t, 'w) wait_set_action list" ("\<lbrace>_\<rbrace>\<^bsub>w\<^esub>" [0] 1000) where
  "wset_a = fst o snd o snd o snd" 

definition interrupt_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't interrupt_action list" ("\<lbrace>_\<rbrace>\<^bsub>i\<^esub>" [0] 1000) where
  "interrupt_a = fst o snd o snd o snd o snd"

definition obs_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'o list" ("\<lbrace>_\<rbrace>\<^bsub>o\<^esub>" [0] 1000) where
  "obs_a \<equiv> snd o snd o snd o snd o snd"

lemma locks_a_conv [simp]: "locks_a (ls, ntsjswss) = ls"
by(simp add:locks_a_def)

lemma thr_a_conv [simp]: "thr_a (ls, nts, jswss) = nts"
by(simp add: thr_a_def)

lemma cond_a_conv [simp]: "cond_a (ls, nts, js, wws) = js"
by(simp add: cond_a_def)

lemma wset_a_conv [simp]: "wset_a (ls, nts, js, wss, isobs) = wss"
by(simp add: wset_a_def)

lemma interrupt_a_conv [simp]: "interrupt_a (ls, nts, js, ws, is, obs) = is"
by(simp add: interrupt_a_def)

lemma obs_a_conv [simp]: "obs_a (ls, nts, js, wss, is, obs) = obs"
by(simp add: obs_a_def)

fun ta_update_locks :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> lock_action \<Rightarrow> 'l \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_locks (ls, nts, js, wss, obs) lta l = (ls(l $:= ls $ l @ [lta]), nts, js, wss, obs)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_NewThread (ls, nts, js, wss, is, obs) nt = (ls, nts @ [nt], js, wss, is, obs)"

fun ta_update_Conditional :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "ta_update_Conditional (ls, nts, js, wss, is, obs) j = (ls, nts, js @ [j], wss, is, obs)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t, 'w) wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_wait_set (ls, nts, js, wss, is, obs) ws = (ls, nts, js, wss @ [ws], is, obs)"

fun ta_update_interrupt :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't interrupt_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "ta_update_interrupt (ls, nts, js, wss, is, obs) i = (ls, nts, js, wss, is @ [i], obs)"

fun ta_update_obs :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'o \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "ta_update_obs (ls, nts, js, wss, is, obs) ob = (ls, nts, js, wss, is, obs @ [ob])"

abbreviation empty_ta :: "('l,'t,'x,'m,'w,'o) thread_action" where
  "empty_ta \<equiv> (K$ [], [], [], [], [], [])"

notation (input) empty_ta ("\<epsilon>")

text \<open>
  Pretty syntax for specifying thread actions:
  Write \<open>\<lbrace> Lock\<rightarrow>l, Unlock\<rightarrow>l, Suspend w, Interrupt t\<rbrace>\<close> instead of
  @{term "((K$ [])(l $:= [Lock, Unlock]), [], [Suspend w], [Interrupt t], [])"}.

  \<open>thread_action'\<close> is a type that contains of all basic thread actions.
  Automatically coerce basic thread actions into that type and then dispatch to the right
  update function by pattern matching.
  For coercion, adhoc overloading replaces the generic injection \<open>inject_thread_action\<close>
  by the specific ones, i.e. constructors.
  To avoid ambiguities with observable actions, the observable actions must be of sort \<open>obs_action\<close>,
  which the basic thread action types are not.
\<close>

class obs_action

datatype ('l,'t,'x,'m,'w,'o) thread_action' 
  = LockAction "lock_action \<times> 'l"
  | NewThreadAction "('t,'x,'m) new_thread_action"
  | ConditionalAction "'t conditional_action"
  | WaitSetAction "('t, 'w) wait_set_action"
  | InterruptAction "'t interrupt_action"
  | ObsAction 'o

setup \<open>
  Sign.add_const_constraint (@{const_name ObsAction}, SOME @{typ "'o :: obs_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action'"})
\<close>

fun thread_action'_to_thread_action :: 
  "('l,'t,'x,'m,'w,'o :: obs_action) thread_action' \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "thread_action'_to_thread_action (LockAction (la, l)) ta = ta_update_locks ta la l"
| "thread_action'_to_thread_action (NewThreadAction nt) ta = ta_update_NewThread ta nt"
| "thread_action'_to_thread_action (ConditionalAction ca) ta = ta_update_Conditional ta ca"
| "thread_action'_to_thread_action (WaitSetAction wa) ta = ta_update_wait_set ta wa"
| "thread_action'_to_thread_action (InterruptAction ia) ta = ta_update_interrupt ta ia"
| "thread_action'_to_thread_action (ObsAction ob) ta = ta_update_obs ta ob"

consts inject_thread_action :: "'a \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action'"

nonterminal ta_let and ta_lets
syntax
  "_ta_snoc" :: "ta_lets \<Rightarrow> ta_let \<Rightarrow> ta_lets" ("_,/ _")
  "_ta_block" :: "ta_lets \<Rightarrow> 'a" ("\<lbrace>_\<rbrace>" [0] 1000)
  "_ta_empty" :: "ta_lets" ("") 
  "_ta_single" :: "ta_let \<Rightarrow> ta_lets" ("_")
  "_ta_inject" :: "logic \<Rightarrow> ta_let" ("(_)")
  "_ta_lock" :: "logic \<Rightarrow> logic \<Rightarrow> ta_let" ("_\<rightarrow>_")

translations
  "_ta_block _ta_empty" == "CONST empty_ta"
  "_ta_block (_ta_single bta)" == "_ta_block (_ta_snoc _ta_empty bta)"
  "_ta_inject bta" == "CONST inject_thread_action bta"
  "_ta_lock la l" == "CONST inject_thread_action (CONST Pair la l)"
  "_ta_block (_ta_snoc btas bta)" == "CONST thread_action'_to_thread_action bta (_ta_block btas)"


adhoc_overloading
  inject_thread_action NewThreadAction ConditionalAction WaitSetAction InterruptAction ObsAction LockAction

lemma ta_upd_proj_simps [simp]:
  shows ta_obs_proj_simps:
  "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" 
  "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>" "\<lbrace>ta_update_obs ta obs\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> @ [obs]"
  and ta_lock_proj_simps:
  "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>l\<^esub> = (let ls = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> in ls(l $:= ls $ l @ [x]))"
  "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" 
  "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>" "\<lbrace>ta_update_locks ta x l\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_thread_proj_simps:
  "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> @ [t]" "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" 
  "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>" "\<lbrace>ta_update_NewThread ta t\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_wset_proj_simps:
  "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> @ [w]"
  "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>" "\<lbrace>ta_update_wait_set ta w\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_cond_proj_simps:
  "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> @ [c]" "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>" "\<lbrace>ta_update_Conditional ta c\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_interrupt_proj_simps:
  "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> @ [i]" "\<lbrace>ta_update_interrupt ta i\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(cases ta, simp)+

lemma thread_action'_to_thread_action_proj_simps [simp]:
  shows thread_action'_to_thread_action_proj_locks_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>l\<^esub>"
  and thread_action'_to_thread_action_proj_nt_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>t\<^esub>"
  and thread_action'_to_thread_action_proj_cond_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>c\<^esub>"
  and thread_action'_to_thread_action_proj_wset_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>w\<^esub>"
  and thread_action'_to_thread_action_proj_interrupt_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>i\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>i\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>i\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>i\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>i\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>i\<^esub>"
  and thread_action'_to_thread_action_proj_obs_simps:
  "\<lbrace>thread_action'_to_thread_action (LockAction (la, l)) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_locks ta la l\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (NewThreadAction nt) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_NewThread ta nt\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ConditionalAction ca) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_Conditional ta ca\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (WaitSetAction wa) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_wait_set ta wa\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (InterruptAction ia) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_interrupt ta ia\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>thread_action'_to_thread_action (ObsAction ob) ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta_update_obs ta ob\<rbrace>\<^bsub>o\<^esub>"
by(simp_all)

lemmas ta_upd_simps =
  ta_update_locks.simps ta_update_NewThread.simps ta_update_Conditional.simps
  ta_update_wait_set.simps ta_update_interrupt.simps ta_update_obs.simps
  thread_action'_to_thread_action.simps

declare ta_upd_simps [simp del]

hide_const (open)
  LockAction NewThreadAction ConditionalAction WaitSetAction InterruptAction ObsAction
  thread_action'_to_thread_action
hide_type (open) thread_action'

datatype wake_up_status =
  WSNotified
| WSWokenUp

datatype 'w wait_set_status =
  InWS 'w
| PostWS wake_up_status

type_synonym 't lock = "('t \<times> nat) option"
type_synonym ('l,'t) locks = "'l \<Rightarrow>f 't lock"
type_synonym 'l released_locks = "'l \<Rightarrow>f nat"
type_synonym ('l,'t,'x) thread_info = "'t \<rightharpoonup> ('x \<times> 'l released_locks)"
type_synonym ('w,'t) wait_sets = "'t \<rightharpoonup> 'w wait_set_status"
type_synonym 't interrupts = "'t set"
type_synonym ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('l,'t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets \<times> 't interrupts"

translations
  (type) "('l, 't) locks" <= (type) "'l \<Rightarrow>f ('t \<times> nat) option"
  (type) "('l, 't, 'x) thread_info" <= (type) "'t \<rightharpoonup> ('x \<times> ('l \<Rightarrow>f nat))"

(* pretty printing for state type *)
print_translation \<open>
  let
    fun tr'
       [Const (@{type_syntax finfun}, _) $ l1 $
        (Const (@{type_syntax option}, _) $
          (Const (@{type_syntax "prod"}, _) $ t1 $ Const (@{type_syntax nat}, _))),
        Const (@{type_syntax "prod"}, _) $
          (Const (@{type_syntax "prod"}, _) $
            (Const (@{type_syntax fun}, _) $ t2 $
              (Const (@{type_syntax option}, _) $
                (Const (@{type_syntax "prod"}, _) $ x $
                  (Const (@{type_syntax finfun}, _) $ l2 $ Const (@{type_syntax nat}, _))))) $
            m) $
          (Const (@{type_syntax prod}, _) $
            (Const (@{type_syntax fun}, _) $ t3 $ 
              (Const (@{type_syntax option}, _) $ (Const (@{type_syntax wait_set_status}, _) $ w))) $
            (Const (@{type_syntax fun}, _) $ t4 $ (Const (@{type_syntax bool}, _))))] =
      if t1 = t2 andalso t1 = t3 andalso t1 = t4 andalso l1 = l2
      then Syntax.const @{type_syntax state} $ l1 $ t1 $ x $ m $ w
      else raise Match;
  in [(@{type_syntax "prod"}, K tr')]
  end
\<close>
typ "('l,'t,'x,'m,'w) state"


abbreviation no_wait_locks :: "'l \<Rightarrow>f nat"
where "no_wait_locks \<equiv> (K$ 0)"

lemma neq_no_wait_locks_conv:
  "\<And>ln. ln \<noteq> no_wait_locks \<longleftrightarrow> (\<exists>l. ln $ l > 0)"
by(auto simp add: expand_finfun_eq fun_eq_iff)

lemma neq_no_wait_locksE:
  fixes ln assumes "ln \<noteq> no_wait_locks" obtains l where "ln $ l > 0"
using assms
by(auto simp add: neq_no_wait_locks_conv)

text \<open>
  Use type variables for components instead of @{typ "('l,'t,'x,'m,'w) state"} in types for state projections
  to allow to reuse them for refined state implementations for code generation.
\<close>

definition locks :: "('locks \<times> ('thread_info \<times> 'm) \<times> 'wsets \<times> 'interrupts) \<Rightarrow> 'locks" where
  "locks lstsmws \<equiv> fst lstsmws"

definition thr :: "('locks \<times> ('thread_info \<times> 'm) \<times> 'wsets \<times> 'interrupts) \<Rightarrow> 'thread_info" where
  "thr lstsmws \<equiv> fst (fst (snd lstsmws))"

definition shr :: "('locks \<times> ('thread_info \<times> 'm) \<times> 'wsets \<times> 'interrupts) \<Rightarrow> 'm" where
  "shr lstsmws \<equiv> snd (fst (snd lstsmws))"

definition wset :: "('locks \<times> ('thread_info \<times> 'm) \<times> 'wsets \<times> 'interrupts) \<Rightarrow> 'wsets" where
  "wset lstsmws \<equiv> fst (snd (snd lstsmws))"

definition interrupts :: "('locks \<times> ('thread_info \<times> 'm) \<times> 'wsets \<times> 'interrupts) \<Rightarrow> 'interrupts" where
  "interrupts lstsmws \<equiv> snd (snd (snd lstsmws))"

lemma locks_conv [simp]: "locks (ls, tsmws) = ls"
by(simp add: locks_def)

lemma thr_conv [simp]: "thr (ls, (ts, m), ws) = ts"
by(simp add: thr_def)

lemma shr_conv [simp]: "shr (ls, (ts, m), ws, is) = m"
by(simp add: shr_def)

lemma wset_conv [simp]: "wset (ls, (ts, m), ws, is) = ws"
by(simp add: wset_def)

lemma interrupts_conv [simp]: "interrupts (ls, (ts, m), ws, is) = is"
by(simp add: interrupts_def)

primrec convert_new_thread_action :: "('x \<Rightarrow> 'x') \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('t,'x','m) new_thread_action"
where
  "convert_new_thread_action f (NewThread t x m) = NewThread t (f x) m"
| "convert_new_thread_action f (ThreadExists t b) = ThreadExists t b"

lemma convert_new_thread_action_inv [simp]:
  "NewThread t x h = convert_new_thread_action f nta \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "ThreadExists t b = convert_new_thread_action f nta \<longleftrightarrow> nta = ThreadExists t b"
  "convert_new_thread_action f nta = NewThread t x h \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "convert_new_thread_action f nta = ThreadExists t b \<longleftrightarrow> nta = ThreadExists t b"
by(cases nta, auto)+

lemma convert_new_thread_action_eqI: 
  "\<lbrakk> \<And>t x m. nta = NewThread t x m \<Longrightarrow> nta' = NewThread t (f x) m;
     \<And>t b. nta = ThreadExists t b \<Longrightarrow> nta' = ThreadExists t b \<rbrakk>
  \<Longrightarrow> convert_new_thread_action f nta = nta'"
apply(cases nta)
apply fastforce+
done

lemma convert_new_thread_action_compose [simp]:
  "convert_new_thread_action f (convert_new_thread_action g ta) = convert_new_thread_action (f o g) ta"
apply(cases ta)
apply(simp_all add: convert_new_thread_action_def)
done

lemma inj_convert_new_thread_action [simp]: 
  "inj (convert_new_thread_action f) = inj f"
apply(rule iffI)
 apply(rule injI)
 apply(drule_tac x="NewThread undefined x undefined" in injD)
 apply auto[2]
apply(rule injI)
apply(case_tac x)
apply(auto dest: injD)
done

lemma convert_new_thread_action_id:
  "convert_new_thread_action id = (id :: ('t, 'x, 'm) new_thread_action \<Rightarrow> ('t, 'x, 'm) new_thread_action)" (is ?thesis1)
  "convert_new_thread_action (\<lambda>x. x) = (id :: ('t, 'x, 'm) new_thread_action \<Rightarrow> ('t, 'x, 'm) new_thread_action)" (is ?thesis2)
proof -
  show ?thesis1 by(rule ext)(case_tac x, simp_all)
  thus ?thesis2 by(simp add: id_def)
qed

definition convert_extTA :: "('x \<Rightarrow> 'x') \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action"
where "convert_extTA f ta = (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, snd (snd ta))"

lemma convert_extTA_simps [simp]:
  "convert_extTA f \<epsilon> = \<epsilon>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>t\<^esub> = map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
  "convert_extTA f (las, tas, was, cas, is, obs) = (las, map (convert_new_thread_action f) tas, was, cas, is, obs)"
apply(simp_all add: convert_extTA_def)
apply(cases ta, simp)+
done

lemma convert_extTA_eq_conv:
  "convert_extTA f ta = ta' \<longleftrightarrow>
   \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<and> length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = length \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> 
   (\<forall>n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>. convert_new_thread_action f (\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n) = \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> ! n)"
apply(cases ta, cases ta')
apply(auto simp add: convert_extTA_def map_eq_all_nth_conv)
done

lemma convert_extTA_compose [simp]:
  "convert_extTA f (convert_extTA g ta) = convert_extTA (f o g) ta"
by(simp add: convert_extTA_def)

lemma obs_a_convert_extTA [simp]: "obs_a (convert_extTA f ta) = obs_a ta"
by(cases ta) simp

text \<open>Actions for thread start/finish\<close>

datatype 'o action =
    NormalAction 'o
  | InitialThreadAction
  | ThreadFinishAction

instance action :: (type) obs_action
proof qed

definition convert_obs_initial :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x,'m,'w,'o action) thread_action"
where 
  "convert_obs_initial ta = (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>, map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"

lemma inj_NormalAction [simp]: "inj NormalAction"
by(rule injI) auto

lemma convert_obs_initial_inject [simp]:
  "convert_obs_initial ta = convert_obs_initial ta' \<longleftrightarrow> ta = ta'"
by(cases ta)(cases ta', auto simp add: convert_obs_initial_def)

lemma convert_obs_initial_empty_TA [simp]:
  "convert_obs_initial \<epsilon> = \<epsilon>"
by(simp add: convert_obs_initial_def)

lemma convert_obs_initial_eq_empty_TA [simp]:
  "convert_obs_initial ta = \<epsilon> \<longleftrightarrow> ta = \<epsilon>"
  "\<epsilon> = convert_obs_initial ta \<longleftrightarrow> ta = \<epsilon>"
by(case_tac [!] ta)(auto simp add: convert_obs_initial_def)

lemma convert_obs_initial_simps [simp]:
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  "\<lbrace>convert_obs_initial ta\<rbrace>\<^bsub>i\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
by(simp_all add: convert_obs_initial_def)

type_synonym
  ('l,'t,'x,'m,'w,'o) semantics =
    "'t \<Rightarrow> 'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

(* pretty printing for semantics *)
print_translation \<open>
  let
    fun tr'
       [t4,
        Const (@{type_syntax fun}, _) $
          (Const (@{type_syntax "prod"}, _) $ x1 $ m1) $
          (Const (@{type_syntax fun}, _) $
            (Const (@{type_syntax "prod"}, _) $
              (Const (@{type_syntax finfun}, _) $ l $
                (Const (@{type_syntax list}, _) $ Const (@{type_syntax lock_action}, _))) $
              (Const (@{type_syntax "prod"}, _) $
                (Const (@{type_syntax list}, _) $ (Const (@{type_syntax new_thread_action}, _) $ t1 $ x2 $ m2)) $
                (Const (@{type_syntax "prod"}, _) $
                  (Const (@{type_syntax list}, _) $ (Const (@{type_syntax conditional_action}, _) $ t2)) $
                  (Const (@{type_syntax "prod"}, _) $
                    (Const (@{type_syntax list}, _) $ (Const (@{type_syntax wait_set_action}, _) $ t3 $ w)) $ 
                    (Const (@{type_syntax prod}, _) $
                       (Const (@{type_syntax list}, _) $ (Const (@{type_syntax interrupt_action}, _) $ t5)) $
                       (Const (@{type_syntax list}, _) $ o1)))))) $
            (Const (@{type_syntax fun}, _) $ (Const (@{type_syntax "prod"}, _) $ x3 $ m3) $
              Const (@{type_syntax bool}, _)))] =
      if x1 = x2 andalso x1 = x3 andalso m1 = m2 andalso m1 = m3 
        andalso t1 = t2 andalso t2 = t3 andalso t3 = t4 andalso t4 = t5
      then Syntax.const @{type_syntax semantics} $ l $ t1 $ x1 $ m1 $ w $ o1
      else raise Match;
  in [(@{type_syntax fun}, K tr')]
  end
\<close>
typ "('l,'t,'x,'m,'w,'o) semantics"

end
