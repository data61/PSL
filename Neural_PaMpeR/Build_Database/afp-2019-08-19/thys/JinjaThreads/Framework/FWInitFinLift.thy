(*  Title:      JinjaThreads/MM/FWInitFinLift.thy
    Author:     Andreas Lochbihler
*)

section \<open>Synthetic first and last actions for each thread\<close>

theory FWInitFinLift
imports
  FWLTS
  FWLiftingSem
begin

datatype status = 
  PreStart
| Running
| Finished

abbreviation convert_TA_initial :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,status \<times> 'x,'m,'w,'o) thread_action"
where "convert_TA_initial == convert_extTA (Pair PreStart)"

lemma convert_obs_initial_convert_TA_initial: 
  "convert_obs_initial (convert_TA_initial ta) = convert_TA_initial (convert_obs_initial ta)"
by(simp add: convert_obs_initial_def)

lemma convert_TA_initial_inject [simp]:
  "convert_TA_initial ta = convert_TA_initial ta' \<longleftrightarrow> ta = ta'"
by(cases ta)(cases ta', auto)

context final_thread begin

primrec init_fin_final :: "status \<times> 'x \<Rightarrow> bool"
where "init_fin_final (status, x) \<longleftrightarrow> status = Finished \<and> final x"

end

context multithreaded_base begin

inductive init_fin :: "('l,'t,status \<times> 'x,'m,'w,'o action) semantics" ("_ \<turnstile> _ -_\<rightarrow>i _" [50,0,0,51] 51)
where
  NormalAction:
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> 
  \<Longrightarrow> t \<turnstile> ((Running, x), m) -convert_TA_initial (convert_obs_initial ta)\<rightarrow>i ((Running, x'), m')"

| InitialThreadAction:
  "t \<turnstile> ((PreStart, x), m) -\<lbrace>InitialThreadAction\<rbrace>\<rightarrow>i ((Running, x), m)"

| ThreadFinishAction:
  "final x \<Longrightarrow> t \<turnstile> ((Running, x), m) -\<lbrace>ThreadFinishAction\<rbrace>\<rightarrow>i ((Finished, x), m)"

end

declare split_paired_Ex [simp del]

inductive_simps (in multithreaded_base) init_fin_simps [simp]:
  "t \<turnstile> ((Finished, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> ((PreStart, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> ((Running, x), m) -ta\<rightarrow>i xm'"
  "t \<turnstile> xm -ta\<rightarrow>i ((Finished, x'), m')"
  "t \<turnstile> xm -ta\<rightarrow>i ((Running, x'), m')"
  "t \<turnstile> xm -ta\<rightarrow>i ((PreStart, x'), m')"

declare split_paired_Ex [simp]

context multithreaded begin

lemma multithreaded_init_fin: "multithreaded init_fin_final init_fin"
by(unfold_locales)(fastforce simp add: init_fin.simps convert_obs_initial_def ta_upd_simps dest: new_thread_memory)+

end

locale if_multithreaded_base = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"

sublocale if_multithreaded_base < "if": multithreaded_base
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
.

locale if_multithreaded = if_multithreaded_base + multithreaded +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"

sublocale if_multithreaded < "if": multithreaded
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
by(rule multithreaded_init_fin)

context \<tau>multithreaded begin

inductive init_fin_\<tau>move :: "('l,'t,status \<times> 'x,'m,'w,'o action) \<tau>moves"
where
  "\<tau>move (x, m) ta (x', m') 
  \<Longrightarrow> init_fin_\<tau>move ((Running, x), m) (convert_TA_initial (convert_obs_initial ta)) ((Running, x'), m')"

lemma init_fin_\<tau>move_simps [simp]:
  "init_fin_\<tau>move ((PreStart, x), m) ta x'm' = False"
  "init_fin_\<tau>move xm ta ((PreStart, x'), m') = False"
  "init_fin_\<tau>move ((Running, x), m) ta ((s, x'), m') \<longleftrightarrow>
   (\<exists>ta'. ta = convert_TA_initial (convert_obs_initial ta') \<and> s = Running \<and> \<tau>move (x, m) ta' (x', m'))"
  "init_fin_\<tau>move ((s, x), m) ta ((Running, x'), m') \<longleftrightarrow> 
   s = Running \<and> (\<exists>ta'. ta = convert_TA_initial (convert_obs_initial ta') \<and> \<tau>move (x, m) ta' (x', m'))"
  "init_fin_\<tau>move ((Finished, x), m) ta x'm' = False"
  "init_fin_\<tau>move xm ta ((Finished, x'), m') = False"
by(simp_all add: init_fin_\<tau>move.simps)

lemma init_fin_silent_move_RunningI:
  assumes "silent_move t (x, m) (x', m')"
  shows "\<tau>trsys.silent_move (init_fin t) init_fin_\<tau>move ((Running, x), m) ((Running, x'), m')"
using assms by(cases)(auto intro: \<tau>trsys.silent_move.intros init_fin.NormalAction)

lemma init_fin_silent_moves_RunningI:
  assumes "silent_moves t (x, m) (x', m')"
  shows "\<tau>trsys.silent_moves (init_fin t) init_fin_\<tau>move ((Running, x), m) ((Running, x'), m')"
using assms
by(induct rule: rtranclp_induct2)(auto elim: rtranclp.rtrancl_into_rtrancl intro: init_fin_silent_move_RunningI)

lemma init_fin_silent_moveD:
  assumes "\<tau>trsys.silent_move (init_fin t) init_fin_\<tau>move ((s, x), m) ((s', x'), m')"
  shows "silent_move t (x, m) (x', m') \<and> s = s' \<and> s' = Running"
using assms by(auto elim!: \<tau>trsys.silent_move.cases init_fin.cases)

lemma init_fin_silent_movesD:
  assumes "\<tau>trsys.silent_moves (init_fin t) init_fin_\<tau>move ((s, x), m) ((s', x'), m')"
  shows "silent_moves t (x, m) (x', m') \<and> s = s'"
using assms
by(induct "((s, x), m)" "((s', x'), m')" arbitrary: s' x' m')
  (auto 7 2 simp only: dest!: init_fin_silent_moveD intro: rtranclp.rtrancl_into_rtrancl)

lemma init_fin_\<tau>divergeD:
  assumes "\<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move ((status, x), m)"
  shows "\<tau>diverge t (x, m) \<and> status = Running"
proof
  from assms show "status = Running"
    by(cases rule: \<tau>trsys.\<tau>diverge.cases[consumes 1])(auto dest: init_fin_silent_moveD)
  moreover define xm where "xm = (x, m)"
  ultimately have "\<exists>x m. xm = (x, m) \<and> \<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move ((Running, x), m)"
    using assms by blast
  thus "\<tau>diverge t xm"
  proof(coinduct)
    case (\<tau>diverge xm)
    then obtain x m 
      where diverge: "\<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move ((Running, x), m)" 
      and xm: "xm = (x, m)" by blast
    thus ?case
      by(cases rule:\<tau>trsys.\<tau>diverge.cases[consumes 1])(auto dest!: init_fin_silent_moveD)
  qed
qed

lemma init_fin_\<tau>diverge_RunningI:
  assumes "\<tau>diverge t (x, m)"
  shows "\<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move ((Running, x), m)"
proof -
  define sxm where "sxm = ((Running, x), m)"
  with assms have "\<exists>x m. \<tau>diverge t (x, m) \<and> sxm = ((Running, x), m)" by blast
  thus "\<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move sxm"
  proof(coinduct rule: \<tau>trsys.\<tau>diverge.coinduct[consumes 1, case_names \<tau>diverge])
    case (\<tau>diverge sxm)
    then obtain x m where "\<tau>diverge t (x, m)" and "sxm = ((Running, x), m)" by blast
    thus ?case by(cases)(auto intro: init_fin_silent_move_RunningI)
  qed
qed

lemma init_fin_\<tau>diverge_conv:
  "\<tau>trsys.\<tau>diverge (init_fin t) init_fin_\<tau>move ((status, x), m) \<longleftrightarrow>
   \<tau>diverge t (x, m) \<and> status = Running"
by(blast intro: init_fin_\<tau>diverge_RunningI dest: init_fin_\<tau>divergeD)

end

lemma init_fin_\<tau>moves_False:
  "\<tau>multithreaded.init_fin_\<tau>move (\<lambda>_ _ _. False) = (\<lambda>_ _ _. False)"
by(simp add: fun_eq_iff \<tau>multithreaded.init_fin_\<tau>move.simps)

locale if_\<tau>multithreaded = if_multithreaded_base + \<tau>multithreaded +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale if_\<tau>multithreaded < "if": \<tau>multithreaded
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
  "init_fin_\<tau>move"
.

locale if_\<tau>multithreaded_wf = if_multithreaded_base + \<tau>multithreaded_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale if_\<tau>multithreaded_wf < if_multithreaded
by unfold_locales

sublocale if_\<tau>multithreaded_wf < if_\<tau>multithreaded .

context \<tau>multithreaded_wf begin

lemma \<tau>multithreaded_wf_init_fin:
  "\<tau>multithreaded_wf init_fin_final init_fin init_fin_\<tau>move"
proof -
  interpret "if": multithreaded init_fin_final init_fin "map NormalAction \<circ> convert_RA"
    by(rule multithreaded_init_fin)
  show ?thesis
  proof(unfold_locales)
    fix t x m ta x' m'
    assume "init_fin_\<tau>move (x, m) ta (x', m')" "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" 
    thus "m = m'" by(cases)(auto dest: \<tau>move_heap)
  next
    fix s ta s'
    assume "init_fin_\<tau>move s ta s'"
    thus "ta = \<epsilon>" by(cases)(auto dest: silent_tl)
  qed
qed

end

sublocale if_\<tau>multithreaded_wf < "if": \<tau>multithreaded_wf
  "init_fin_final"
  "init_fin"
  "map NormalAction \<circ> convert_RA"
  "init_fin_\<tau>move"
by(rule \<tau>multithreaded_wf_init_fin)


primrec init_fin_lift_inv :: "('i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> 'i \<Rightarrow> 't \<Rightarrow> status \<times> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "init_fin_lift_inv P I t (s, x) = P I t x"

context lifting_inv begin

lemma lifting_inv_init_fin_lift_inv:
  "lifting_inv init_fin_final init_fin (init_fin_lift_inv P)"
proof -
  interpret "if": multithreaded init_fin_final init_fin "map NormalAction \<circ> convert_RA"
    by(rule multithreaded_init_fin)
  show ?thesis
    by(unfold_locales)(fastforce elim!: init_fin.cases dest: invariant_red invariant_NewThread invariant_other)+
qed

end

locale if_lifting_inv =
  if_multithreaded +
  lifting_inv +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"

sublocale if_lifting_inv < "if": lifting_inv
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  "init_fin_lift_inv P"
by(rule lifting_inv_init_fin_lift_inv)

primrec init_fin_lift :: "('t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> status \<times> 'x \<Rightarrow> 'm \<Rightarrow> bool"
where "init_fin_lift P t (s, x) = P t x"

context lifting_wf begin

lemma lifting_wf_init_fin_lift:
  "lifting_wf init_fin_final init_fin (init_fin_lift P)"
proof -
  interpret "if": multithreaded init_fin_final init_fin "map NormalAction \<circ> convert_RA"
    by(rule multithreaded_init_fin)
  show ?thesis
    by(unfold_locales)(fastforce elim!: init_fin.cases dest: dest: preserves_red preserves_other preserves_NewThread)+
qed

end

locale if_lifting_wf =
  if_multithreaded +
  lifting_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"

sublocale if_lifting_wf < "if": lifting_wf 
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  "init_fin_lift P"
by(rule lifting_wf_init_fin_lift)

lemma (in if_lifting_wf) if_lifting_inv:
  "if_lifting_inv final r (\<lambda>_::unit. P)"
proof -
  interpret lifting_inv final r convert_RA  "\<lambda>_ :: unit. P" by(rule lifting_inv)
  show ?thesis by unfold_locales
qed

locale \<tau>lifting_inv = \<tau>multithreaded_wf +
  lifting_inv +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"
  and P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma redT_silent_move_invariant:
  "\<lbrakk> \<tau>mredT s s'; ts_inv P Is (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_inv P Is (thr s') (shr s')"
by(auto dest!: redT_invariant m\<tau>move_silentD)

lemma redT_silent_moves_invariant:
  "\<lbrakk> mthr.silent_moves s s'; ts_inv P Is (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_inv P Is (thr s') (shr s')"
by(induct rule: rtranclp_induct)(auto dest: redT_silent_move_invariant)

lemma redT_\<tau>rtrancl3p_invariant:
  "\<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ts_inv P Is (thr s) (shr s) \<rbrakk>
  \<Longrightarrow> ts_inv P (upd_invs Is P (concat (map (thr_a \<circ> snd) ttas))) (thr s') (shr s')"
proof(induct arbitrary: Is rule: mthr.\<tau>rtrancl3p.induct)
  case \<tau>rtrancl3p_refl thus ?case by simp
next
  case (\<tau>rtrancl3p_step s s' tls s'' tl)
  thus ?case by(cases tl)(force dest: redT_invariant)
next
  case (\<tau>rtrancl3p_\<tau>step s s' tls s'' tl)
  thus ?case by(cases tl)(force dest: redT_invariant m\<tau>move_silentD)
qed

end

locale \<tau>lifting_wf = \<tau>multithreaded +
  lifting_wf +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"
  and P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
begin

lemma redT_silent_move_preserves:
  "\<lbrakk> \<tau>mredT s s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(auto dest: redT_preserves)

lemma redT_silent_moves_preserves:
  "\<lbrakk> mthr.silent_moves s s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(induct rule: rtranclp.induct)(auto dest: redT_silent_move_preserves)

lemma redT_\<tau>rtrancl3p_preserves:
  "\<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(induct rule: mthr.\<tau>rtrancl3p.induct)(auto dest: redT_silent_moves_preserves redT_preserves)

end

definition init_fin_lift_state :: "status \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,status \<times> 'x,'m,'w) state"
where "init_fin_lift_state s \<sigma> = (locks \<sigma>, (\<lambda>t. map_option (\<lambda>(x, ln). ((s, x), ln)) (thr \<sigma> t), shr \<sigma>), wset \<sigma>, interrupts \<sigma>)"

definition init_fin_descend_thr :: "('l,'t,'status \<times> 'x) thread_info \<Rightarrow> ('l,'t,'x) thread_info"
where "init_fin_descend_thr ts = map_option (\<lambda>((s, x), ln). (x, ln)) \<circ> ts"

definition init_fin_descend_state :: "('l,'t,'status \<times> 'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state"
where "init_fin_descend_state \<sigma> = (locks \<sigma>, (init_fin_descend_thr (thr \<sigma>), shr \<sigma>), wset \<sigma>, interrupts \<sigma>)"

lemma ts_ok_init_fin_lift_init_fin_lift_state [simp]:
  "ts_ok (init_fin_lift P) (thr (init_fin_lift_state s \<sigma>)) (shr (init_fin_lift_state s \<sigma>)) \<longleftrightarrow> ts_ok P (thr \<sigma>) (shr \<sigma>)"
by(auto simp add: init_fin_lift_state_def intro!: ts_okI dest: ts_okD)

lemma ts_inv_init_fin_lift_inv_init_fin_lift_state [simp]:
  "ts_inv (init_fin_lift_inv P) I (thr (init_fin_lift_state s \<sigma>)) (shr (init_fin_lift_state s \<sigma>)) \<longleftrightarrow> 
   ts_inv P I (thr \<sigma>) (shr \<sigma>)"
by(auto simp add: init_fin_lift_state_def intro!: ts_invI dest: ts_invD)

lemma init_fin_lift_state_conv_simps:
  shows shr_init_fin_lift_state: "shr (init_fin_lift_state s \<sigma>) = shr \<sigma>"
  and locks_init_fin_lift_state: "locks (init_fin_lift_state s \<sigma>) = locks \<sigma>"
  and wset_init_fin_lift_state: "wset (init_fin_lift_state s \<sigma>) = wset \<sigma>"
  and interrupts_init_fin_lift_stae: "interrupts (init_fin_lift_state s \<sigma>) = interrupts \<sigma>"
  and thr_init_fin_list_state: 
  "thr (init_fin_lift_state s \<sigma>) t = map_option (\<lambda>(x, ln). ((s, x), ln)) (thr \<sigma> t)"
by(simp_all add: init_fin_lift_state_def)

lemma thr_init_fin_list_state': 
  "thr (init_fin_lift_state s \<sigma>) = map_option (\<lambda>(x, ln). ((s, x), ln)) \<circ> thr \<sigma>"
by(simp add: fun_eq_iff thr_init_fin_list_state)

lemma init_fin_descend_thr_Some_conv [simp]:
  "\<And>ln. ts t = \<lfloor>((status, x), ln)\<rfloor> \<Longrightarrow> init_fin_descend_thr ts t = \<lfloor>(x, ln)\<rfloor>"
by(simp add: init_fin_descend_thr_def)

lemma init_fin_descend_thr_None_conv [simp]:
  "ts t = None \<Longrightarrow> init_fin_descend_thr ts t = None"
by(simp add: init_fin_descend_thr_def)

lemma init_fin_descend_thr_eq_None [simp]:
  "init_fin_descend_thr ts t = None \<longleftrightarrow> ts t = None"
by(simp add: init_fin_descend_thr_def)

lemma init_fin_descend_state_simps [simp]:
  "init_fin_descend_state (ls, (ts, m), ws, is) = (ls, (init_fin_descend_thr ts, m), ws, is)"
  "locks (init_fin_descend_state s) = locks s"
  "thr (init_fin_descend_state s) = init_fin_descend_thr (thr s)"
  "shr (init_fin_descend_state s) = shr s"
  "wset (init_fin_descend_state s) = wset s"
  "interrupts (init_fin_descend_state s) = interrupts s"
by(simp_all add: init_fin_descend_state_def)

lemma init_fin_descend_thr_update [simp]:
  "init_fin_descend_thr (ts(t := v)) = (init_fin_descend_thr ts)(t := map_option (\<lambda>((status, x), ln). (x, ln)) v)"
by(simp add: init_fin_descend_thr_def fun_eq_iff)

lemma ts_ok_init_fin_descend_state: 
  "ts_ok P (init_fin_descend_thr ts) = ts_ok (init_fin_lift P) ts"
by(rule ext)(auto 4 3 intro!: ts_okI dest: ts_okD simp add: init_fin_descend_thr_def)

lemma free_thread_id_init_fin_descend_thr [simp]: 
  "free_thread_id (init_fin_descend_thr ts) = free_thread_id ts"
by(simp add: free_thread_id.simps fun_eq_iff)

lemma redT_updT'_init_fin_descend_thr_eq_None [simp]:
  "redT_updT' (init_fin_descend_thr ts) nt t = None \<longleftrightarrow> redT_updT' ts nt t = None"
by(cases nt) simp_all

lemma thread_ok_init_fin_descend_thr [simp]: 
  "thread_ok (init_fin_descend_thr ts) nta = thread_ok ts nta"
by(cases nta) simp_all

lemma threads_ok_init_fin_descend_thr [simp]:
  "thread_oks (init_fin_descend_thr ts) ntas = thread_oks ts ntas"
by(induct ntas arbitrary: ts)(auto elim!: thread_oks_ts_change[THEN iffD1, rotated 1])

lemma init_fin_descend_thr_redT_updT [simp]:
  "init_fin_descend_thr (redT_updT ts (convert_new_thread_action (Pair status) nt)) =
   redT_updT (init_fin_descend_thr ts) nt"
by(cases nt) simp_all

lemma init_fin_descend_thr_redT_updTs [simp]:
  "init_fin_descend_thr (redT_updTs ts (map (convert_new_thread_action (Pair status)) nts)) =
   redT_updTs (init_fin_descend_thr ts) nts"
by(induct nts arbitrary: ts) simp_all

context final_thread begin

lemma cond_action_ok_init_fin_descend_stateI [simp]:
  "final_thread.cond_action_ok init_fin_final s t ct \<Longrightarrow> cond_action_ok (init_fin_descend_state s) t ct"
by(cases ct)(auto simp add: final_thread.cond_action_ok.simps init_fin_descend_thr_def)

lemma cond_action_oks_init_fin_descend_stateI [simp]:
  "final_thread.cond_action_oks init_fin_final s t cts \<Longrightarrow> cond_action_oks (init_fin_descend_state s) t cts"
by(induct cts)(simp_all add: final_thread.cond_action_oks.simps cond_action_ok_init_fin_descend_stateI)

end


definition lift_start_obs :: "'t \<Rightarrow> 'o list \<Rightarrow> ('t \<times> 'o action) list"
where "lift_start_obs t obs = (t, InitialThreadAction) # map (\<lambda>ob. (t, NormalAction ob)) obs"

lemma length_lift_start_obs [simp]: "length (lift_start_obs t obs) = Suc (length obs)"
by(simp add: lift_start_obs_def)

lemma set_lift_start_obs [simp]:
  "set (lift_start_obs t obs) =
   insert (t, InitialThreadAction) ((Pair t \<circ> NormalAction) ` set obs)"
by(auto simp add: lift_start_obs_def o_def)

lemma distinct_lift_start_obs [simp]: "distinct (lift_start_obs t obs) = distinct obs"
by(auto simp add: lift_start_obs_def distinct_map intro: inj_onI)

end
