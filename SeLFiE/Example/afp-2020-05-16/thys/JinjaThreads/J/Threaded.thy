(*  Title:      JinjaThreads/J/Threaded.thy
    Author:     Andreas Lochbihler
*)

section \<open>The source language as an instance of the framework\<close>

theory Threaded
imports
  SmallStep
  JWellForm
  "../Common/ConformThreaded"
  "../Common/ExternalCallWF"
  "../Framework/FWLiftingSem"
  "../Framework/FWProgressAux"
begin

context heap_base begin \<comment> \<open>Move to ?? - also used in BV\<close>

lemma wset_Suspend_ok_start_state:
  fixes final r convert_RA
  assumes "start_state f P C M vs \<in> I"
  shows "start_state f P C M vs \<in> multithreaded_base.wset_Suspend_ok final r convert_RA I"
using assms
by(rule multithreaded_base.wset_Suspend_okI)(simp add: start_state_def split_beta)

end

abbreviation final_expr :: "'addr expr \<times> 'addr locals \<Rightarrow> bool"where
  "final_expr \<equiv> \<lambda>(e, x). final e"

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

context J_heap_base begin

abbreviation mred
  :: "'addr J_prog \<Rightarrow> ('addr, 'thread_id, 'addr expr \<times> 'addr locals, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics"
where
  "mred P t \<equiv> (\<lambda>((e, l), h)  ta ((e', l'), h'). P,t \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>)"

lemma red_new_thread_heap:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' ex'' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
  and reds_new_thread_heap:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' ex'' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> h'' = hp s'"
apply(induct rule: red_reds.inducts)
apply(fastforce dest: red_ext_new_thread_heap simp add: ta_upd_simps)+
done

lemma red_ta_Wakeup_no_Join_no_Lock_no_Interrupt:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
  and reds_ta_Wakeup_no_Join_no_Lock_no_Interrupt:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {} \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = {} \<and> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = {}"
apply(induct rule: red_reds.inducts)
apply(auto simp add: ta_upd_simps dest: red_external_Wakeup_no_Join_no_Lock_no_Interrupt del: conjI)
done

lemma final_no_red:
  "final e \<Longrightarrow> \<not> P,t \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>"
by(auto elim: red.cases finalE)

lemma red_mthr: "multithreaded final_expr (mred P)"
by(unfold_locales)(auto dest: red_new_thread_heap)

end

sublocale J_heap_base < red_mthr: multithreaded
  "final_expr"
  "mred P"
  convert_RA
  for P
by(rule red_mthr)

context J_heap_base begin

abbreviation
  mredT :: 
  "'addr J_prog \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id, 'addr expr \<times> 'addr locals,'heap) Jinja_thread_action) 
  \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state \<Rightarrow> bool"
where
  "mredT P \<equiv> red_mthr.redT P"

abbreviation
  mredT_syntax1 :: "'addr J_prog \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state
                  \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'addr expr \<times> 'addr locals,'heap) Jinja_thread_action
                  \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow> _" [50,0,0,0,50] 80)
where
  "mredT_syntax1 P s t ta s' \<equiv> mredT P s (t, ta) s'"

abbreviation
  mRedT_syntax1 :: 
  "'addr J_prog
  \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id, 'addr expr \<times> 'addr locals,'heap) Jinja_thread_action) list
  \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals,'heap,'addr) state \<Rightarrow> bool"
  ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s' \<equiv> red_mthr.RedT P s ttas s'"

end

context J_heap begin

lemma redT_hext_incr:
  "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s' \<Longrightarrow> shr s \<unlhd> shr s'"
by(erule red_mthr.redT.cases)(auto dest!: red_hext_incr intro: hext_trans)

lemma RedT_hext_incr:
  assumes "P \<turnstile> s -\<triangleright>tta\<rightarrow>* s'"
  shows "shr s \<unlhd> shr s'"
using assms unfolding red_mthr.RedT_def
by(induct)(auto dest: redT_hext_incr intro: hext_trans)

end

subsection \<open>Lifting @{term "tconf"} to multithreaded states\<close>

context J_heap begin

lemma red_NewThread_Thread_Object:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>C. typeof_addr (hp s') (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
  and reds_NewThread_Thread_Object:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr (hp s') (thread_id2addr t') = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(induct rule: red_reds.inducts)
apply(fastforce dest: red_external_new_thread_exists_thread_object simp add: ta_upd_simps)+
done

lemma lifting_wf_tconf:
  "lifting_wf final_expr (mred P) (\<lambda>t ex h. P,h \<turnstile> t \<surd>t)"
by(unfold_locales)(fastforce dest: red_hext_incr red_NewThread_Thread_Object elim!: tconf_hext_mono intro: tconfI)+

end

sublocale J_heap < red_tconf: lifting_wf final_expr "mred P" convert_RA "\<lambda>t ex h. P,h \<turnstile> t \<surd>t"
by(rule lifting_wf_tconf)

subsection \<open>Towards agreement between the framework semantics' lock state and the locks stored in the expressions\<close>

primrec sync_ok :: "('a,'b,'addr) exp \<Rightarrow> bool"
  and sync_oks :: "('a,'b,'addr) exp list \<Rightarrow> bool"
where
  "sync_ok (new C) = True"
| "sync_ok (newA T\<lfloor>i\<rceil>) = sync_ok i"
| "sync_ok (Cast T e) = sync_ok e"
| "sync_ok (e instanceof T) = sync_ok e"
| "sync_ok (Val v) = True"
| "sync_ok (Var v) = True"
| "sync_ok (e \<guillemotleft>bop\<guillemotright> e') = (sync_ok e \<and> sync_ok e' \<and> (contains_insync e' \<longrightarrow> is_val e))"
| "sync_ok (V := e) = sync_ok e"
| "sync_ok (a\<lfloor>i\<rceil>) = (sync_ok a \<and> sync_ok i \<and> (contains_insync i \<longrightarrow> is_val a))"
| "sync_ok (AAss a i e) = (sync_ok a \<and> sync_ok i \<and> sync_ok e \<and> (contains_insync i \<longrightarrow> is_val a) \<and> (contains_insync e \<longrightarrow> is_val a \<and> is_val i))"
| "sync_ok (a\<bullet>length) = sync_ok a"
| "sync_ok (e\<bullet>F{D}) = sync_ok e"
| "sync_ok (FAss e F D e') = (sync_ok e \<and> sync_ok e' \<and> (contains_insync e' \<longrightarrow> is_val e))"
| "sync_ok (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (sync_ok e \<and> sync_ok e' \<and> sync_ok e'' \<and> (contains_insync e' \<longrightarrow> is_val e) \<and> (contains_insync e'' \<longrightarrow> is_val e \<and> is_val e'))"
| "sync_ok (e\<bullet>m(pns)) = (sync_ok e \<and> sync_oks pns \<and> (contains_insyncs pns \<longrightarrow> is_val e))"
| "sync_ok ({V : T=vo; e}) = sync_ok e"
| "sync_ok (sync\<^bsub>V\<^esub> (o') e) = (sync_ok o' \<and> \<not> contains_insync e)"
| "sync_ok (insync\<^bsub>V\<^esub> (a) e) = sync_ok e"
| "sync_ok (e;;e') = (sync_ok e \<and> \<not> contains_insync e')"
| "sync_ok (if (b) e else e') = (sync_ok b \<and> \<not> contains_insync e \<and> \<not> contains_insync e')"
| "sync_ok (while (b) e) = (\<not> contains_insync b \<and> \<not> contains_insync e)"
| "sync_ok (throw e) = sync_ok e"
| "sync_ok (try e catch(C v) e') = (sync_ok e \<and> \<not> contains_insync e')"
| "sync_oks [] = True"
| "sync_oks (x # xs) = (sync_ok x \<and> sync_oks xs \<and> (contains_insyncs xs \<longrightarrow> is_val x))"

lemma sync_oks_append [simp]:
  "sync_oks (xs @ ys) \<longleftrightarrow> sync_oks xs \<and> sync_oks ys \<and> (contains_insyncs ys \<longrightarrow> (\<exists>vs. xs = map Val vs))"
by(induct xs)(auto simp add: Cons_eq_map_conv)

lemma fixes e :: "('a,'b,'addr) exp" and es :: "('a,'b,'addr) exp list"
  shows not_contains_insync_sync_ok: "\<not> contains_insync e \<Longrightarrow> sync_ok e"
  and not_contains_insyncs_sync_oks: "\<not> contains_insyncs es \<Longrightarrow> sync_oks es"
by(induct e and es rule: sync_ok.induct sync_oks.induct)(auto)

lemma expr_locks_sync_ok: "(\<And>ad. expr_locks e ad = 0) \<Longrightarrow> sync_ok e"
  and expr_lockss_sync_oks: "(\<And>ad. expr_lockss es ad = 0) \<Longrightarrow> sync_oks es"
by(auto intro!: not_contains_insync_sync_ok not_contains_insyncs_sync_oks
        simp add: contains_insync_conv contains_insyncs_conv)

lemma sync_ok_extRet2J [simp, intro!]: "sync_ok e \<Longrightarrow> sync_ok (extRet2J e va)"
by(cases va) auto

abbreviation
  sync_es_ok :: "('addr,'thread_id,('a,'b,'addr) exp\<times>'c) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "sync_es_ok \<equiv> ts_ok (\<lambda>t (e, x) m. sync_ok e)"

lemma sync_es_ok_blocks [simp]:
  "\<lbrakk> length pns = length Ts; length Ts = length vs \<rbrakk> \<Longrightarrow> sync_ok (blocks pns Ts vs e) = sync_ok e"
by(induct pns Ts vs e rule: blocks.induct) auto

context J_heap_base begin

lemma assumes wf: "wf_J_prog P"
  shows red_preserve_sync_ok: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> sync_ok e'"
  and reds_preserve_sync_oks: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> sync_oks es'"
proof(induct rule: red_reds.inducts)
  case (RedCall s a U M Ts T pns body D vs)
  from wf \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close>
  have "wf_mdecl wf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,body)\<rfloor>)"
    by(rule sees_wf_mdecl)
  then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with \<open>length vs = length pns\<close> \<open>length Ts = length pns\<close> 
  have "expr_locks (blocks pns Ts vs body) = (\<lambda>ad. 0)"
    by(simp add: expr_locks_blocks)
  thus ?case by(auto intro: expr_locks_sync_ok)
qed(fastforce intro: not_contains_insync_sync_ok)+

lemma assumes wf: "wf_J_prog P"
  shows expr_locks_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> expr_locks e'' = (\<lambda>ad. 0)"

  and expr_locks_new_thread':
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> expr_locks e'' = (\<lambda>ad. 0)"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a U M Ts T D vs ta va h' ta' e' s')
  then obtain C fs a where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J P (C, run, a) = (e'', x'')"
    by(fastforce dest: red_external_new_thread_sub_thread)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = \<lfloor>(pns, body)\<rfloor> in D" by auto
  from sees_wf_mdecl[OF wf this] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
  with sees ext show ?case by(auto simp add: extNTA2J_def)
qed(auto simp add: ta_upd_simps)

lemma assumes wf: "wf_J_prog P"
  shows red_new_thread_sync_ok: "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> sync_ok e''"
  and reds_new_thread_sync_ok: "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> sync_ok e''"
by(auto dest!: expr_locks_new_thread[OF wf] expr_locks_new_thread'[OF wf] intro: expr_locks_sync_ok expr_lockss_sync_oks)

lemma lifting_wf_sync_ok: "wf_J_prog P \<Longrightarrow> lifting_wf final_expr (mred P) (\<lambda>t (e, x) m. sync_ok e)"
by(unfold_locales)(auto intro: red_preserve_sync_ok red_new_thread_sync_ok)

lemma redT_preserve_sync_ok:
  assumes red: "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
  shows "\<lbrakk> wf_J_prog P; sync_es_ok (thr s) (shr s) \<rbrakk> \<Longrightarrow> sync_es_ok (thr s') (shr s')"
by(rule lifting_wf.redT_preserves[OF lifting_wf_sync_ok red])

lemma RedT_preserves_sync_ok:
  "\<lbrakk>wf_J_prog P; P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s'; sync_es_ok (thr s) (shr s)\<rbrakk>
   \<Longrightarrow> sync_es_ok (thr s') (shr s')"
by(rule lifting_wf.RedT_preserves[OF lifting_wf_sync_ok])

lemma sync_es_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(pns, body)\<rfloor> in D; length Ts = length vs \<rbrakk>
  \<Longrightarrow> sync_es_ok (thr (J_start_state P C M vs)) m"
apply(rule ts_okI)
apply(clarsimp simp add: start_state_def split_beta split: if_split_asm)
apply(drule (1) sees_wf_mdecl)
apply(clarsimp simp add: wf_mdecl_def)
apply(drule WT_expr_locks)
apply(rule expr_locks_sync_ok)
apply simp
done

end

text \<open>Framework lock state agrees with locks stored in the expression\<close>

definition lock_ok :: "('addr,'thread_id) locks \<Rightarrow> ('addr,'thread_id,('a, 'b,'addr) exp \<times> 'x) thread_info \<Rightarrow> bool" where
  "\<And>ln. lock_ok ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls $ l) t = 0)
                                     | \<lfloor>((e, x), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls $ l) t + ln $ l = expr_locks e l))"

lemma lock_okI:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls $ l) t = 0; \<And>t e x ln l. ts t = \<lfloor>((e, x), ln)\<rfloor> \<Longrightarrow> has_locks (ls $ l) t + ln $ l= expr_locks e l \<rbrakk> \<Longrightarrow> lock_ok ls ts"
apply(fastforce simp add: lock_ok_def)
done

lemma lock_okE:
  "\<lbrakk> lock_ok ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls $ l) t = 0) \<Longrightarrow> Q;
     \<forall>t e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls $ l) t + ln $ l = expr_locks e l) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
by(fastforce simp add: lock_ok_def)

lemma lock_okD1:
  "\<lbrakk> lock_ok ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls $ l) t = 0"
apply(simp add: lock_ok_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_okD2:
  "\<And>ln. \<lbrakk> lock_ok ls ts; ts t = \<lfloor>((e, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls $ l) t + ln $ l = expr_locks e l"
apply(fastforce simp add: lock_ok_def)
done

lemma lock_ok_lock_thread_ok:
  assumes lock: "lock_ok ls ts"
  shows "lock_thread_ok ls ts"
proof(rule lock_thread_okI)
  fix l t
  assume lsl: "has_lock (ls $ l) t"
  show "\<exists>xw. ts t = \<lfloor>xw\<rfloor>"
  proof(cases "ts t")
    case None
    with lock have "has_locks (ls $ l) t = 0"
      by(auto dest: lock_okD1)
    with lsl show ?thesis by simp
  next
    case (Some a) thus ?thesis by blast
  qed
qed

lemma (in J_heap_base) lock_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(pns, body)\<rfloor> in D; length Ts = length vs \<rbrakk>
  \<Longrightarrow> lock_ok (locks (J_start_state P C M vs)) (thr (J_start_state P C M vs))"
apply(rule lock_okI)
apply(auto simp add: start_state_def split: if_split_asm)
apply(drule (1) sees_wf_mdecl)
apply(clarsimp simp add: wf_mdecl_def)
apply(drule WT_expr_locks)
apply(simp add: expr_locks_blocks)
done

subsection \<open>Preservation of lock state agreement\<close>

fun upd_expr_lock_action :: "int \<Rightarrow> lock_action \<Rightarrow> int"
where
  "upd_expr_lock_action i Lock = i + 1"
| "upd_expr_lock_action i Unlock = i - 1"
| "upd_expr_lock_action i UnlockFail = i"
| "upd_expr_lock_action i ReleaseAcquire = i"

fun upd_expr_lock_actions :: "int \<Rightarrow> lock_action list \<Rightarrow> int" where
  "upd_expr_lock_actions n [] = n"
| "upd_expr_lock_actions n (L # Ls) = upd_expr_lock_actions (upd_expr_lock_action n L) Ls"

lemma upd_expr_lock_actions_append [simp]:
  "upd_expr_lock_actions n (Ls @ Ls') = upd_expr_lock_actions (upd_expr_lock_actions n Ls) Ls'"
by(induct Ls arbitrary: n, auto)

definition upd_expr_locks :: "('l \<Rightarrow> int) \<Rightarrow> 'l lock_actions \<Rightarrow> 'l \<Rightarrow> int"
where "upd_expr_locks els las \<equiv> \<lambda>l. upd_expr_lock_actions (els l) (las $ l)"

lemma upd_expr_locks_iff [simp]:
  "upd_expr_locks els las l = upd_expr_lock_actions (els l) (las $ l)"
by(simp add: upd_expr_locks_def)

lemma upd_expr_lock_action_add [simp]:
  "upd_expr_lock_action (l + l') L = upd_expr_lock_action l L + l'"
by(cases L, auto)

lemma upd_expr_lock_actions_add [simp]:
  "upd_expr_lock_actions (l + l') Ls = upd_expr_lock_actions l Ls + l'"
by(induct Ls arbitrary: l, auto)

lemma upd_expr_locks_add [simp]:
  "upd_expr_locks (\<lambda>a. x a + y a) las = (\<lambda>a. upd_expr_locks x las a + y a)"
by(auto intro: ext)

lemma expr_locks_extRet2J [simp, intro!]: "expr_locks e = (\<lambda>ad. 0) \<Longrightarrow> expr_locks (extRet2J e va) = (\<lambda>ad. 0)"
by(cases va) auto

lemma (in J_heap_base)
  assumes wf: "wf_J_prog P"
  shows red_update_expr_locks:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> 
  \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
  and reds_update_expr_lockss:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk>
  \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
proof -
  have "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> 
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_locks e') ad - (int o expr_locks e) ad)"
    and "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_lockss es') ad - (int o expr_lockss es) ad)"
  proof(induct rule: red_reds.inducts)
    case (RedCall s a U M Ts T pns body D vs)
    from wf \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close>
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,body)\<rfloor>)"
      by(rule sees_wf_mdecl)
    then obtain T where "P,[this\<mapsto>Class D,pns[\<mapsto>]Ts] \<turnstile> body :: T"
      by(auto simp add: wf_mdecl_def)
    hence "expr_locks body = (\<lambda>ad. 0)" by(rule WT_expr_locks)
    with \<open>length vs = length pns\<close> \<open>length Ts = length pns\<close> 
    have "expr_locks (blocks pns Ts vs body) = (\<lambda>ad. 0)"
      by(simp add: expr_locks_blocks)
    thus ?case by(auto intro: expr_locks_sync_ok)
  next
    case RedCallExternal thus ?case
      by(auto simp add: fun_eq_iff contains_insync_conv contains_insyncs_conv finfun_upd_apply ta_upd_simps elim!: red_external.cases)
  qed(fastforce simp add: fun_eq_iff contains_insync_conv contains_insyncs_conv finfun_upd_apply ta_upd_simps)+
  hence "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_locks e) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'"
    and "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_lockss es) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_lockss es'"
    by(auto intro: ext simp only: upd_expr_locks_add)
  thus "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk>
       \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
    and "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk>
        \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
    by(auto simp add: o_def)
qed

definition lock_expr_locks_ok :: "'t FWState.lock \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "lock_expr_locks_ok l t n i \<equiv> (i = int (has_locks l t) + int n) \<and> i \<ge> 0"

lemma upd_lock_upd_expr_lock_action_preserve_lock_expr_locks_ok:
  assumes lao: "lock_action_ok l t L"
  and lelo: "lock_expr_locks_ok l t n i"
  shows "lock_expr_locks_ok (upd_lock l t L) t (upd_threadR n l t L) (upd_expr_lock_action i L)"
proof -
  from lelo have i: "i \<ge> 0"
    and hl: "i = int (has_locks l t) + int n"
    by(auto simp add: lock_expr_locks_ok_def)
  from lelo
  show ?thesis
  proof(cases L)
    case Lock
    with lao have "may_lock l t" by(simp)
    with hl have "has_locks (lock_lock l t) t = (Suc (has_locks l t))" by(auto)
    with Lock i hl show ?thesis
      by(simp add: lock_expr_locks_ok_def)
  next
    case Unlock
    with lao have "has_lock l t" by simp
    then obtain n' 
      where hl': "has_locks l t = Suc n'"
      by(auto dest: has_lock_has_locks_Suc)
    hence "has_locks (unlock_lock l) t = n'" by simp
    with Unlock i hl hl' show ?thesis
      by(simp add: lock_expr_locks_ok_def)
  qed(auto simp add: lock_expr_locks_ok_def)
qed

lemma upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok:
  "\<lbrakk> lock_actions_ok l t Ls; lock_expr_locks_ok l t n i \<rbrakk>
  \<Longrightarrow> lock_expr_locks_ok (upd_locks l t Ls) t (upd_threadRs n l t Ls) (upd_expr_lock_actions i Ls)"
by(induct Ls arbitrary: l i n)(auto intro: upd_lock_upd_expr_lock_action_preserve_lock_expr_locks_ok)


definition ls_els_ok :: "('addr,'thread_id) locks \<Rightarrow> 'thread_id \<Rightarrow> ('addr \<Rightarrow>f nat) \<Rightarrow> ('addr \<Rightarrow> int) \<Rightarrow> bool" where
  "\<And>ln. ls_els_ok ls t ln els \<equiv> \<forall>l. lock_expr_locks_ok (ls $ l) t (ln $ l) (els l)"

lemma ls_els_okI:
  "\<And>ln. (\<And>l. lock_expr_locks_ok (ls $ l) t (ln $ l) (els l)) \<Longrightarrow> ls_els_ok ls t ln els"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okE:
  "\<And>ln. \<lbrakk> ls_els_ok ls t ln els; \<forall>l. lock_expr_locks_ok (ls $ l) t (ln $ l) (els l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: ls_els_ok_def)

lemma ls_els_okD:
  "\<And>ln. ls_els_ok ls t ln els \<Longrightarrow> lock_expr_locks_ok (ls $ l) t (ln $ l) (els l)"
by(auto simp add: ls_els_ok_def)

lemma redT_updLs_upd_expr_locks_preserves_ls_els_ok:  
 "\<And>ln. \<lbrakk> ls_els_ok ls t ln els; lock_ok_las ls t las \<rbrakk>
  \<Longrightarrow> ls_els_ok (redT_updLs ls t las) t (redT_updLns ls t ln las) (upd_expr_locks els las)"
by(auto intro!: ls_els_okI upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok elim!: ls_els_okE simp add: redT_updLs_def lock_ok_las_def)

lemma sync_ok_redT_updT: 
  assumes "sync_es_ok ts h"
  and nt: "\<And>t e x h''. ta = NewThread t (e, x) h'' \<Longrightarrow> sync_ok e"
  shows "sync_es_ok (redT_updT ts ta) h'"
using assms
proof(cases ta)
  case (NewThread T x m)
  obtain E X where [simp]: "x = (E, X)" by (cases x, auto)
  with NewThread have "sync_ok E" by(simp)(rule nt)
  with NewThread \<open>sync_es_ok ts h\<close> show ?thesis
    apply -
    apply(rule ts_okI)
    apply(case_tac "t=T")
    by(auto dest: ts_okD)
qed(auto intro: ts_okI dest: ts_okD)


lemma sync_ok_redT_updTs: 
  "\<lbrakk> sync_es_ok ts h; \<And>t e x h. NewThread t (e, x) h \<in> set tas \<Longrightarrow> sync_ok e \<rbrakk>
  \<Longrightarrow> sync_es_ok (redT_updTs ts tas) h'"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by(auto intro: ts_okI dest: ts_okD)
next
  case (Cons TA TAS TS)
  note IH = \<open>\<And>ts. \<lbrakk>sync_es_ok ts h; \<And>t e x h''. NewThread t (e, x) h'' \<in> set TAS \<Longrightarrow> sync_ok e\<rbrakk> 
            \<Longrightarrow> sync_es_ok (redT_updTs ts TAS) h'\<close>
  note nt = \<open>\<And>t e x h. NewThread t (e, x) h \<in> set (TA # TAS) \<Longrightarrow> sync_ok e\<close>
  from \<open>sync_es_ok TS h\<close> nt
  have "sync_es_ok (redT_updT TS TA) h"
    by(auto elim!: sync_ok_redT_updT)
  hence "sync_es_ok (redT_updTs (redT_updT TS TA) TAS) h'"
    by(rule IH)(auto intro: nt)
  thus ?case by simp
qed

lemma lock_ok_thr_updI:
  "\<And>ln. \<lbrakk> lock_ok ls ts; ts t = \<lfloor>((e, xs), ln)\<rfloor>; expr_locks e = expr_locks e' \<rbrakk>
  \<Longrightarrow> lock_ok ls (ts(t \<mapsto> ((e', xs'), ln)))"
by(rule lock_okI)(auto split: if_split_asm dest: lock_okD2 lock_okD1)

context J_heap_base begin 

lemma redT_preserves_lock_ok:
  assumes wf: "wf_J_prog P"
  and "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
  and "lock_ok (locks s) (thr s)"
  and "sync_es_ok (thr s) (shr s)"
  shows "lock_ok (locks s') (thr s')"
proof -
  obtain ls ts h ws "is" where s [simp]: "s = (ls, (ts, h), ws, is)" by(cases s) fastforce
  obtain ls' ts' h' ws' is' where s' [simp]: "s' = (ls', (ts', h'), ws', is')" by(cases s') fastforce
  from assms have redT: "P \<turnstile> (ls, (ts, h), ws, is) -t\<triangleright>ta\<rightarrow> (ls', (ts', h'), ws', is')"
    and loes: "lock_ok ls ts"
    and aoes: "sync_es_ok ts h" by auto
  from redT have "lock_ok ls' ts'"
  proof(cases rule: red_mthr.redT_elims)
    case (normal a a' m')
    moreover obtain e x where "a = (e, x)" by (cases a, auto)
    moreover obtain e' x' where "a' = (e', x')" by (cases a', auto)
    ultimately have P: "P,t \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(m', x')\<rangle>"
      and est: "ts t = \<lfloor>((e, x), no_wait_locks)\<rfloor>"
      and lota: "lock_ok_las ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
      and cctta: "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      and ls': "ls' = redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
      and s': "ts' = redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> ((e', x'), redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"
      by auto
    let ?ts' = "redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> ((e', x'), redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"
    from est aoes have aoe: "sync_ok e" by(auto dest: ts_okD)
    from aoe P have aoe': "sync_ok e'" by(auto dest: red_preserve_sync_ok[OF wf])
    from aoes red_new_thread_sync_ok[OF wf P]
    have "sync_es_ok (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) h'"
      by(rule sync_ok_redT_updTs)
    with aoe' have aoes': "sync_es_ok ?ts' m'"
      by(auto intro!: ts_okI dest: ts_okD split: if_split_asm)
    have "lock_ok ls' ?ts'"
    proof(rule lock_okI)
      fix t'' l
      assume "?ts' t'' = None"
      hence "ts t'' = None"
        by(auto split: if_split_asm intro: redT_updTs_None)
      with loes have "has_locks (ls $ l) t'' = 0"
        by(auto dest: lock_okD1)
      moreover from \<open>?ts' t'' = None\<close> 
      have "t \<noteq> t''" by(simp split: if_split_asm)
      ultimately show "has_locks (ls' $ l) t'' = 0"
        by(simp add: red_mthr.redT_has_locks_inv[OF redT])
    next
      fix t'' e'' x'' l ln''
      assume ts't'': "?ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      with aoes' have aoe'': "sync_ok e''" by(auto dest: ts_okD)
      show "has_locks (ls' $ l) t'' + ln'' $ l = expr_locks e'' l"
      proof(cases "t = t''")
        case True
        note tt'' = \<open>t = t''\<close>
        with ts't'' have  e'': "e'' = e'" and x'': "x'' = x'"
          and ln'': "ln'' = redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by auto
        have "ls_els_ok ls t no_wait_locks (int o expr_locks e)"
        proof(rule ls_els_okI)
          fix l
          note lock_okD2[OF loes, OF est]
          thus "lock_expr_locks_ok (ls $ l) t (no_wait_locks $ l) ((int \<circ> expr_locks e) l)"
            by(simp add: lock_expr_locks_ok_def)
        qed
        hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) (upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)"
          by(rule redT_updLs_upd_expr_locks_preserves_ls_els_ok[OF _ lota])
        hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (redT_updLns ls t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) (int o expr_locks e')"
          by(simp only: red_update_expr_locks[OF wf P aoe])
        thus ?thesis using ls' e'' tt'' ln''
          by(auto dest: ls_els_okD[where l = l] simp: lock_expr_locks_ok_def)
      next
        case False
        note tt'' = \<open>t \<noteq> t''\<close>
        from lota have lao: "lock_actions_ok (ls $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)"
          by(simp add: lock_ok_las_def)
        show ?thesis
        proof(cases "ts t''")
          case None
          with est ts't'' tt'' cctta
          obtain m where "NewThread t'' (e'', x'') m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" and ln'': "ln'' = no_wait_locks"
            by(auto dest: redT_updTs_new_thread)
          moreover with P have "m' = m" by(auto dest: red_new_thread_heap)
          ultimately have "NewThread t'' (e'', x'') m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by simp
          with wf P ln'' have "expr_locks e'' = (\<lambda>ad. 0)"
            by -(rule expr_locks_new_thread)
          hence elel: "expr_locks e'' l = 0" by simp
          from loes None  have "has_locks (ls $ l) t'' = 0"
            by(auto dest: lock_okD1)
          moreover note lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF lao tt''[symmetric]]
          ultimately have "has_locks (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l) t'' = 0"
            by(auto simp add: fun_eq_iff)
          with elel ls' ln'' show ?thesis by(auto)
        next
          case (Some a)
          then obtain E X LN where est'': "ts t'' = \<lfloor>((E, X), LN)\<rfloor>" by(cases a, auto)
          with loes have IH: "has_locks (ls $ l) t'' + LN $ l = expr_locks E l"
            by(auto dest: lock_okD2)
          from est est'' tt'' cctta have "?ts' t'' = \<lfloor>((E, X), LN)\<rfloor>"
            by(simp)(rule redT_updTs_Some, simp_all)
          with ts't'' have e'': "E = e''" and x'': "X = x''"
            and ln'': "ln'' = LN" by(simp_all)
          with lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF lao tt''[symmetric]] IH ls'
          show ?thesis by(clarsimp simp add: redT_updLs_def fun_eq_iff)
        qed
      qed
    qed
    with s' show ?thesis by simp
  next
    case (acquire a ln n)
    hence [simp]: "ta = (K$ [], [], [], [], [], convert_RA ln)" "ws' = ws" "h' = h" 
      and ls': "ls' = acquire_all ls t ln"
      and ts': "ts' = ts(t \<mapsto> (a, no_wait_locks))"
      and "ts t = \<lfloor>(a, ln)\<rfloor>"
      and "may_acquire_all ls t ln"
      by auto
    obtain e x where [simp]: "a = (e, x)" by (cases a, auto)
    from ts' have ts': "ts' = ts(t \<mapsto> ((e, x), no_wait_locks))" by simp
    from \<open>ts t = \<lfloor>(a, ln)\<rfloor>\<close> have tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>" by simp
    show ?thesis
    proof(rule lock_okI)
      fix t'' l
      assume rtutes: "ts' t'' = None"
      with ts' have tst'': "ts t'' = None"
        by(simp split: if_split_asm)
      with tst have tt'': "t \<noteq> t''" by auto
      from tst'' loes have "has_locks (ls $ l) t'' = 0"
        by(auto dest: lock_okD1)
      thus "has_locks (ls' $ l) t'' = 0"
        by(simp add: red_mthr.redT_has_locks_inv[OF redT tt''])
    next
      fix t'' e'' x'' ln'' l
      assume ts't'': "ts' t'' = \<lfloor>((e'', x''), ln'')\<rfloor>"
      show "has_locks (ls' $ l) t'' + ln'' $ l = expr_locks e'' l"
      proof(cases "t = t''")
        case True
        note [simp] = this
        with ts't'' ts' tst
        have [simp]: "ln'' = no_wait_locks" "e = e''" by auto
        from tst loes have "has_locks (ls $ l) t + ln $ l = expr_locks e l"
          by(auto dest: lock_okD2)
        show ?thesis
        proof(cases "ln $ l > 0")
          case True
          with \<open>may_acquire_all ls t ln\<close> ls' have "may_lock (ls $ l) t"
            by(auto elim: may_acquire_allE)
          with ls'
          have "has_locks (ls' $ l) t = has_locks (ls $ l) t + ln $ l"
            by(simp add: has_locks_acquire_locks_conv)
          with \<open>has_locks (ls $ l) t + ln $ l = expr_locks e l\<close>
          show ?thesis by(simp)
        next
          case False
          hence "ln $ l = 0" by simp
          with ls' have "has_locks (ls' $ l) t = has_locks (ls $ l) t"
            by(simp)
          with \<open>has_locks (ls $ l) t + ln $ l = expr_locks e l\<close> \<open>ln $ l = 0\<close>
          show ?thesis by(simp)
        qed
      next
        case False
        with ts' ts't'' have tst'': "ts t'' = \<lfloor>((e'', x''), ln'')\<rfloor>" by(simp)
        with loes have "has_locks (ls $ l) t'' + ln'' $ l = expr_locks e'' l"
          by(auto dest: lock_okD2)
        show ?thesis
        proof(cases "ln $ l > 0")
          case False
          with \<open>t \<noteq> t''\<close> ls'
          have "has_locks (ls' $ l) t'' = has_locks (ls $ l) t''" by(simp)
          with \<open>has_locks (ls $ l) t'' + ln'' $ l = expr_locks e'' l\<close>
          show ?thesis by(simp)
        next
          case True
          with \<open>may_acquire_all ls t ln\<close> have "may_lock (ls $ l) t"
            by(auto elim: may_acquire_allE)
          with ls' \<open>t \<noteq> t''\<close> have "has_locks (ls' $ l) t'' = has_locks (ls $ l) t''"
            by(simp add: has_locks_acquire_locks_conv')
          with ls' \<open>has_locks (ls $ l) t'' + ln'' $ l = expr_locks e'' l\<close>
          show ?thesis by(simp)
        qed
      qed
    qed
  qed
  thus ?thesis by simp
qed

lemma invariant3p_sync_es_ok_lock_ok:
  assumes wf: "wf_J_prog P"
  shows "invariant3p (mredT P) {s. sync_es_ok (thr s) (shr s) \<and> lock_ok (locks s) (thr s)}"
apply(rule invariant3pI)
apply clarify
apply(rule conjI)
 apply(rule lifting_wf.redT_preserves[OF lifting_wf_sync_ok[OF wf]], blast)
 apply(assumption)
apply(erule (2) redT_preserves_lock_ok[OF wf])
done

lemma RedT_preserves_lock_ok:
  assumes wf: "wf_J_prog P"
  and Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s'"
  and ae: "sync_es_ok (thr s) (shr s)"
  and loes: "lock_ok (locks s) (thr s)"
  shows "lock_ok (locks s') (thr s')"
using invariant3p_rtrancl3p[OF invariant3p_sync_es_ok_lock_ok[OF wf] Red[unfolded red_mthr.RedT_def]] ae loes
by simp

end

subsection \<open>Determinism\<close>

context J_heap_base begin

lemma
  fixes final
  assumes det: "deterministic_heap_ops"
  shows red_deterministic:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     convert_extTA extTA,P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e'', s''\<rangle>;
     final_thread.actions_ok final s t ta; final_thread.actions_ok final s t ta' \<rbrakk> 
  \<Longrightarrow> ta = ta' \<and> e' = e'' \<and> s' = s''"
  and reds_deterministic:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; 
     convert_extTA extTA,P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta'\<rightarrow>] \<langle>es'', s''\<rangle>;
     final_thread.actions_ok final s t ta; final_thread.actions_ok final s t ta' \<rbrakk> 
  \<Longrightarrow> ta = ta' \<and> es' = es'' \<and> s' = s''"
proof(induct e "(shr s, xs)" ta e' s' and es "(shr s, xs)" ta es' s' arbitrary: e'' s'' xs and es'' s'' xs rule: red_reds.inducts)
  case RedNew
  thus ?case by(auto elim!: red_cases dest: deterministic_heap_ops_allocateD[OF det])
next
  case RedNewArray
  thus ?case by(auto elim!: red_cases dest: deterministic_heap_ops_allocateD[OF det])
next
  case RedCall thus ?case
    by(auto elim!: red_cases dest: sees_method_fun simp add: map_eq_append_conv)
next
  case RedCallExternal thus ?case
    by(auto elim!: red_cases dest: red_external_deterministic[OF det] simp add: final_thread.actions_ok_iff map_eq_append_conv dest: sees_method_fun)
next
  case RedCallNull thus ?case by(auto elim!: red_cases dest: sees_method_fun simp add: map_eq_append_conv)
next
  case CallThrowParams thus ?case
    by(auto elim!: red_cases dest: sees_method_fun simp add: map_eq_append_conv append_eq_map_conv append_eq_append_conv2 reds_map_Val_Throw Cons_eq_append_conv append_eq_Cons_conv)
qed(fastforce elim!: red_cases reds_cases dest: deterministic_heap_ops_readD[OF det] deterministic_heap_ops_writeD[OF det] iff: reds_map_Val_Throw)+

lemma red_mthr_deterministic:
  assumes det: "deterministic_heap_ops"
  shows "red_mthr.deterministic P UNIV"
proof(rule red_mthr.determisticI)
  fix s t x ta' x' m' ta'' x'' m''
  assume "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "mred P t (x, shr s) ta' (x', m')" "mred P t (x, shr s) ta'' (x'', m'')"
    and aok: "red_mthr.actions_ok s t ta'" "red_mthr.actions_ok s t ta''"
  moreover obtain e xs where [simp]: "x = (e, xs)" by(cases x)
  moreover obtain e' xs' where [simp]: "x' = (e', xs')" by(cases x')
  moreover obtain e'' xs'' where [simp]: "x'' = (e'', xs'')" by(cases x'')
  ultimately have "extTA2J P,P,t \<turnstile> \<langle>e,(shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e',(m', xs')\<rangle>"
    and "extTA2J P,P,t \<turnstile> \<langle>e,(shr s, xs)\<rangle> -ta''\<rightarrow> \<langle>e'',(m'', xs'')\<rangle>"
    by simp_all
  from red_deterministic[OF det this aok]
  show "ta' = ta'' \<and> x' = x'' \<and> m' = m''" by simp
qed simp

end

end
