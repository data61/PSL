(*  Title:      JinjaThreads/Framework/FWSemantics.thy
    Author:     Andreas Lochbihler
*)

section \<open>The multithreaded semantics\<close>

theory FWSemantics
imports
  FWWellform
  FWLockingThread
  FWCondAction
  FWInterrupt
begin

inductive redT_upd :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
for s t ta x' m'
where
  "redT_updWs t (wset s) \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> ws'
  \<Longrightarrow> redT_upd s t ta x' m' (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, ((redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x', redT_updLns (locks s) t (snd (the (thr s t))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)), m'), ws', redT_updIs (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>)"

inductive_simps redT_upd_simps [simp]:
  "redT_upd s t ta x' m' s'"

definition redT_acq :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l \<Rightarrow>f nat) \<Rightarrow> ('l,'t,'x,'m,'w) state"
where
  "\<And>ln. redT_acq s t ln = (acquire_all (locks s) t ln, ((thr s)(t \<mapsto> (fst (the (thr s t)), no_wait_locks)), shr s), wset s, interrupts s)"

context final_thread begin

inductive actions_ok :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool"
  for s :: "('l,'t,'x,'m,'w) state" and t :: 't and ta :: "('l,'t,'x','m,'w,'o) thread_action"
  where
  "\<lbrakk> lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
     wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>; interrupt_actions_ok (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<rbrakk>
  \<Longrightarrow> actions_ok s t ta"

declare actions_ok.intros [intro!]
declare actions_ok.cases [elim!]

lemma actions_ok_iff [simp]:
  "actions_ok s t ta \<longleftrightarrow>
   lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and>
   wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> interrupt_actions_ok (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
by(auto)

lemma actions_ok_thread_oksD:
  "actions_ok s t ta \<Longrightarrow> thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(erule actions_ok.cases)

inductive actions_ok' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool" where
  "\<lbrakk> lock_ok_las' (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; cond_action_oks' s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
     wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>; interrupt_actions_ok' (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<rbrakk>
  \<Longrightarrow> actions_ok' s t ta"

declare actions_ok'.intros [intro!]
declare actions_ok'.cases [elim!]

lemma actions_ok'_iff:
  "actions_ok' s t ta \<longleftrightarrow>
   lock_ok_las' (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> cond_action_oks' s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and>
   wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> interrupt_actions_ok' (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
by auto

lemma actions_ok'_ta_upd_obs:
  "actions_ok' s t (ta_update_obs ta obs) \<longleftrightarrow> actions_ok' s t ta"
by(auto simp add: actions_ok'_iff lock_ok_las'_def ta_upd_simps wset_actions_ok_def)

lemma actions_ok'_empty: "actions_ok' s t \<epsilon> \<longleftrightarrow> wset s t = None"
by(simp add: actions_ok'_iff lock_ok_las'_def)

lemma actions_ok'_convert_extTA:
  "actions_ok' s t (convert_extTA f ta) = actions_ok' s t ta"
by(simp add: actions_ok'_iff)

inductive actions_subset :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action \<Rightarrow> bool"
where
 "\<lbrakk> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>; 
    collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
    collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<rbrakk>
  \<Longrightarrow> actions_subset ta' ta"

declare actions_subset.intros [intro!]
declare actions_subset.cases [elim!]

lemma actions_subset_iff:
  "actions_subset ta' ta \<longleftrightarrow> 
   collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
   collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and>
   collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
by auto

lemma actions_subset_refl [intro]:
  "actions_subset ta ta"
by(auto intro: actions_subset.intros collect_locks'_subset_collect_locks del: subsetI)

definition final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool" where
  "\<And>ln. final_thread s t \<equiv> (case thr s t of None \<Rightarrow> False | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

definition final_threads :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't set" 
where "final_threads s \<equiv> {t. final_thread s t}"

lemma [iff]: "t \<in> final_threads s = final_thread s t"
  by (simp add: final_threads_def)

lemma [pred_set_conv]: "final_thread s = (\<lambda>t. t \<in> final_threads s)"
  by simp

definition mfinal :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "mfinal s \<longleftrightarrow> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None)"

lemma final_threadI:
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; final x; wset s t = None \<rbrakk> \<Longrightarrow> final_thread s t"
by(simp add: final_thread_def)

lemma final_threadE:
  assumes "final_thread s t"
  obtains x where "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "final x" "wset s t = None"
using assms by(auto simp add: final_thread_def)

lemma mfinalI:
  "(\<And>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s t = None) \<Longrightarrow> mfinal s"
unfolding mfinal_def by blast

lemma mfinalD:
  fixes ln
  assumes "mfinal s" "thr s t = \<lfloor>(x, ln)\<rfloor>"
  shows "final x" "ln = no_wait_locks" "wset s t = None"
using assms unfolding mfinal_def by blast+

lemma mfinalE:
  fixes ln
  assumes "mfinal s" "thr s t = \<lfloor>(x, ln)\<rfloor>"
  obtains "final x" "ln = no_wait_locks" "wset s t = None"
using mfinalD[OF assms] by(rule that)

lemma mfinal_def2: "mfinal s \<longleftrightarrow> dom (thr s) \<subseteq> final_threads s"
by(fastforce elim: mfinalE final_threadE intro: mfinalI final_threadI)

end

locale multithreaded_base = final_thread +
  constrains final :: "'x \<Rightarrow> bool" 
  fixes r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
begin

abbreviation
  r_syntax :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
              ("_ \<turnstile> \<langle>_, _\<rangle> -_\<rightarrow> \<langle>_, _\<rangle>" [50,0,0,0,0,0] 80)
where
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<equiv> t \<turnstile> (x, m) -ta\<rightarrow> (x', m')"

inductive
  redT :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<times> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" and
  redT_syntax1 :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool" ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
where
  "s -t\<triangleright>ta\<rightarrow> s' \<equiv> redT s (t, ta) s'"

|  redT_normal:
  "\<lbrakk> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
     actions_ok s t ta;
     redT_upd s t ta x' m' s' \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>ta\<rightarrow> s'"

| redT_acquire:
  "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t);
     may_acquire_all (locks s) t ln; ln $ n > 0;
     s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s, interrupts s) \<rbrakk>
  \<Longrightarrow> s -t\<triangleright>((K$ []), [], [], [], [], convert_RA ln)\<rightarrow> s'"

abbreviation
  redT_syntax2 :: "('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> 't interrupts
                   \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action
                   \<Rightarrow> ('l,'t) locks \<Rightarrow> ('l,'t,'x) thread_info \<times> 'm \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> 't interrupts \<Rightarrow> bool"
                  ("\<langle>_, _, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _, _\<rangle>" [0,0,0,0,0,0,0,0,0] 80)
where
  "\<langle>ls, tsm, ws, is\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws', is'\<rangle> \<equiv> (ls, tsm, ws, is) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws', is')"


lemma redT_elims [consumes 1, case_names normal acquire]:
  assumes red: "s -t\<triangleright>ta\<rightarrow> s'"
  and normal: "\<And>x x' m' ws'.
    \<lbrakk> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
      thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
      lock_ok_las (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>;
      thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>;
      cond_action_oks s t \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>;
      wset_actions_ok (wset s) t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>;
      interrupt_actions_ok (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>;
      redT_updWs t (wset s) \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> ws';
      s' = (redT_updLs (locks s) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)), m'), ws', redT_updIs (interrupts s) \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>) \<rbrakk>
    \<Longrightarrow> thesis"
   and acquire: "\<And>x ln n.
    \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>;
      ta = (K$ [], [], [], [], [], convert_RA ln);
      \<not> waiting (wset s t);
      may_acquire_all (locks s) t ln; 0 < ln $ n;
      s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s, interrupts s) \<rbrakk>
    \<Longrightarrow> thesis"
  shows thesis
using red
proof cases
  case redT_normal
  thus ?thesis using normal by(cases s')(auto)
next
  case redT_acquire
  thus ?thesis by-(rule acquire, fastforce+)
qed

definition
  RedT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> ('l,'t,'x,'m,'w,'o) thread_action) list \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
          ("_ -\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
where
  "RedT \<equiv> rtrancl3p redT"

lemma RedTI:
  "rtrancl3p redT s ttas s' \<Longrightarrow> RedT s ttas s'"
by(simp add: RedT_def)

lemma RedTE:
  "\<lbrakk> RedT s ttas s'; rtrancl3p redT s ttas s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: RedT_def)

lemma RedTD:
  "RedT s ttas s' \<Longrightarrow> rtrancl3p redT s ttas s'"
by(simp add: RedT_def)

lemma RedT_induct [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     \<And>s. P s [] s;
     \<And>s ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
unfolding RedT_def
by(erule rtrancl3p.induct) auto

lemma RedT_induct' [consumes 1, case_names refl step]:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s';
     P s [] s;
     \<And>ttas s' t ta s''. \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; P s ttas s'; s' -t\<triangleright>ta\<rightarrow> s'' \<rbrakk> \<Longrightarrow> P s (ttas @ [(t, ta)]) s''\<rbrakk>
  \<Longrightarrow> P s ttas s'"
  unfolding RedT_def
apply(erule rtrancl3p_induct', blast)
apply(case_tac b, blast)
done

lemma RedT_lift_preserveD:
  assumes Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and P: "P s"
  and preserve: "\<And>s t tas s'. \<lbrakk> s -t\<triangleright>tas\<rightarrow> s'; P s \<rbrakk> \<Longrightarrow> P s'"
  shows "P s'"
  using Red P
  by(induct rule: RedT_induct)(auto intro: preserve)

lemma RedT_refl [intro, simp]:
  "s -\<triangleright>[]\<rightarrow>* s"
by(rule RedTI)(rule rtrancl3p_refl)

lemma redT_has_locks_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws, is\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws', is'\<rangle>; t \<noteq> t' \<rbrakk> \<Longrightarrow>
  has_locks (ls $ l) t' = has_locks (ls' $ l) t'"
by(auto elim!: redT.cases intro: redT_updLs_has_locks[THEN sym, simplified] may_acquire_all_has_locks_acquire_locks[symmetric])

lemma redT_has_lock_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws, is\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws', is'\<rangle>; t \<noteq> t' \<rbrakk>
  \<Longrightarrow> has_lock (ls' $ l) t' = has_lock (ls $ l) t'"
by(auto simp add: redT_has_locks_inv)

lemma redT_ts_Some_inv:
  "\<lbrakk> \<langle>ls, (ts, m), ws, is\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws', is'\<rangle>; t \<noteq> t'; ts t' = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> ts' t' = \<lfloor>x\<rfloor>"
by(fastforce elim!: redT.cases simp: redT_updTs_upd[THEN sym] intro: redT_updTs_Some)

lemma redT_thread_not_disappear:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s' t' = None\<rbrakk> \<Longrightarrow> thr s t' = None"
apply(cases "t \<noteq> t'")
apply(auto elim!: redT_elims simp add: redT_updTs_upd[THEN sym] intro: redT_updTs_None)
done

lemma RedT_thread_not_disappear:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; thr s' t' = None\<rbrakk> \<Longrightarrow> thr s t' = None"
apply(erule contrapos_pp[where Q="thr s' t' = None"])
apply(drule (1) RedT_lift_preserveD)
apply(erule_tac Q="thr sa t' = None" in contrapos_nn)
apply(erule redT_thread_not_disappear)
apply(auto)
done

lemma redT_preserves_wset_thread_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; wset_thread_ok (wset s) (thr s) \<rbrakk> \<Longrightarrow> wset_thread_ok (wset s') (thr s')"
by(fastforce elim!: redT.cases intro: wset_thread_ok_upd redT_updTs_preserves_wset_thread_ok redT_updWs_preserve_wset_thread_ok)

lemma RedT_preserves_wset_thread_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; wset_thread_ok (wset s) (thr s) \<rbrakk> \<Longrightarrow> wset_thread_ok (wset s') (thr s')"
by(erule (1) RedT_lift_preserveD)(erule redT_preserves_wset_thread_ok)

lemma redT_new_thread_ts_Some:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; wset_thread_ok (wset s) (thr s) \<rbrakk>
  \<Longrightarrow> thr s' t' = \<lfloor>(x, no_wait_locks)\<rfloor>"
by(erule redT_elims)(auto dest: thread_oks_new_thread elim: redT_updTs_new_thread_ts)

lemma RedT_new_thread_ts_not_None:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; NewThread t x m'' \<in> set (concat (map (thr_a \<circ> snd) ttas)); wset_thread_ok (wset s) (thr s) \<rbrakk>
   \<Longrightarrow> thr s' t \<noteq> None"
proof(induct rule: RedT_induct)
  case refl thus ?case by simp
next
  case (step S TTAS S' T TA S'')
  note Red = \<open>S -\<triangleright>TTAS\<rightarrow>* S'\<close>
  note IH = \<open>\<lbrakk> NewThread t x m'' \<in> set (concat (map (thr_a \<circ> snd) TTAS)); wset_thread_ok (wset S) (thr S) \<rbrakk> \<Longrightarrow> thr S' t \<noteq> None\<close>
  note red = \<open>S' -T\<triangleright>TA\<rightarrow> S''\<close>
  note ins = \<open>NewThread t x m'' \<in> set (concat (map (thr_a \<circ> snd) (TTAS @ [(T, TA)])))\<close>
  note wto = \<open>wset_thread_ok (wset S) (thr S)\<close>
  from Red wto have wto': "wset_thread_ok (wset S') (thr S')" by(auto dest: RedT_preserves_wset_thread_ok)  
  show ?case
  proof(cases "NewThread t x m'' \<in> set \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>")
    case True thus ?thesis using red wto'
      by(auto dest!: redT_new_thread_ts_Some)
  next
    case False
    hence "NewThread t x m'' \<in> set (concat (map (thr_a \<circ> snd) TTAS))" using ins by(auto)
    hence "thr S' t \<noteq> None" using wto by(rule IH)
    with red show ?thesis
      by -(erule contrapos_nn, auto dest: redT_thread_not_disappear)
  qed
qed

lemma redT_preserves_lock_thread_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
by(auto elim!: redT_elims intro: redT_upds_preserves_lock_thread_ok acquire_all_preserves_lock_thread_ok)

lemma RedT_preserves_lock_thread_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; lock_thread_ok (locks s) (thr s) \<rbrakk> \<Longrightarrow> lock_thread_ok (locks s') (thr s')"
by(erule (1) RedT_lift_preserveD)(erule redT_preserves_lock_thread_ok)

lemma redT_ex_new_thread:
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "wset_thread_ok (wset s) (thr s)" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None"
  shows "\<exists>m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> w = no_wait_locks"
using assms
by cases (fastforce split: if_split_asm dest: wset_thread_okD redT_updTs_new_thread)+

lemma redT_ex_new_thread':
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None"
  shows "\<exists>m x. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
using assms
by(cases)(fastforce split: if_split_asm dest!: redT_updTs_new_thread)+

definition deterministic :: "('l,'t,'x,'m,'w) state set \<Rightarrow> bool"
where
  "deterministic I \<longleftrightarrow> 
  (\<forall>s t x ta' x' m' ta'' x'' m''. 
    s \<in> I
    \<longrightarrow> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>
    \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle> 
    \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle> 
    \<longrightarrow> actions_ok s t ta' \<longrightarrow> actions_ok s t ta''
    \<longrightarrow> ta' = ta'' \<and> x' = x'' \<and> m' = m'') \<and> invariant3p redT I"

lemma determisticI:
  "\<lbrakk>\<And>s t x ta' x' m' ta'' x'' m''.
      \<lbrakk> s \<in> I; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; 
        t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>; t \<turnstile> \<langle>x, shr s\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>; 
        actions_ok s t ta'; actions_ok s t ta'' \<rbrakk>
      \<Longrightarrow> ta' = ta'' \<and> x' = x'' \<and> m' = m'';
    invariant3p redT I \<rbrakk>
  \<Longrightarrow> deterministic I"
unfolding deterministic_def by blast

lemma deterministicD:
  "\<lbrakk> deterministic I;
    t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>; t \<turnstile> \<langle>x, shr s\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>;
    thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; actions_ok s t ta'; actions_ok s t ta''; s \<in> I \<rbrakk>
  \<Longrightarrow> ta' = ta'' \<and> x' = x'' \<and> m' = m''"
unfolding deterministic_def by blast

lemma deterministic_invariant3p:
  "deterministic I \<Longrightarrow> invariant3p redT I"
unfolding deterministic_def by blast

lemma deterministic_THE:
  "\<lbrakk> deterministic I; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; actions_ok s t ta; s \<in> I \<rbrakk>
  \<Longrightarrow> (THE (ta, x', m'). t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta) = (ta, x', m')"
by(rule the_equality)(blast dest: deterministicD)+

end

locale multithreaded = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  assumes new_thread_memory: "\<lbrakk> t \<turnstile> s -ta\<rightarrow> s'; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> m = snd s'"
  and final_no_red: "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); final x \<rbrakk> \<Longrightarrow> False"
begin

lemma redT_new_thread_common:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; NewThread t' x m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = [] \<rbrakk> \<Longrightarrow> m'' = shr s'"
by(auto elim!: redT_elims rtrancl3p_cases dest: new_thread_memory)

lemma redT_new_thread:
  assumes "s -t'\<triangleright>ta\<rightarrow> s'" "thr s' t = \<lfloor>(x, w)\<rfloor>" "thr s t = None" "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []"
  shows "NewThread t x (shr s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<and> w = no_wait_locks"
using assms
apply(cases rule: redT_elims)
apply(auto split: if_split_asm del: conjI elim!: rtrancl3p_cases)
apply(drule (2) redT_updTs_new_thread)
apply(auto dest: new_thread_memory)
done

lemma final_no_redT: 
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"
by(auto elim!: redT_elims dest: final_no_red)

lemma mfinal_no_redT:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'" and mfinal: "mfinal s"
  shows False
using redT mfinalD[OF mfinal, of t]
by cases (metis final_no_red, metis neq_no_wait_locks_conv)

end

end
