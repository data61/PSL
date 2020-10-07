(*  Title:      JinjaThreads/J/ProgressThreaded.thy
    Author:     Andreas Lochbihler
*)

section \<open>Progress and type safety theorem for the multithreaded system\<close>

theory ProgressThreaded 
imports 
  Threaded
  TypeSafe
  "../Framework/FWProgress"
begin

lemma lock_ok_ls_Some_ex_ts_not_final:
  assumes lock: "lock_ok ls ts"
  and hl: "has_lock (ls $ l) t"
  shows "\<exists>e x ln. ts t = \<lfloor>((e, x), ln)\<rfloor> \<and> \<not> final e"
proof -
  from lock have "lock_thread_ok ls ts"
    by(rule lock_ok_lock_thread_ok)
  with hl obtain e x ln
    where tst: "ts t = \<lfloor>((e, x), ln)\<rfloor>"
    by(auto dest!: lock_thread_okD)
  { assume "final e"
    hence "expr_locks e l = 0" by(rule final_locks)
    with lock tst have "has_locks (ls $ l) t = 0"
      by(auto dest: lock_okD2[rule_format, where l=l])
    with hl have False by simp }
  with tst show ?thesis by auto
qed

subsection \<open>Preservation lemmata\<close>

subsection \<open>Definite assignment\<close>

abbreviation
  def_ass_ts_ok :: "('addr,'thread_id,'addr expr \<times> 'addr locals) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "def_ass_ts_ok \<equiv> ts_ok (\<lambda>t (e, x) h. \<D> e \<lfloor>dom x\<rfloor>)"

context J_heap_base begin

lemma assumes wf: "wf_J_prog P"
  shows red_def_ass_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
  
  and reds_def_ass_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') c'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<D> e'' \<lfloor>dom x''\<rfloor>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  then obtain C fs a where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J P (C, run, a) = (e'', x'')"
    by(fastforce dest: red_external_new_thread_sub_thread)
  from sub_Thread_sees_run[OF wf subThread] obtain D pns body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = \<lfloor>(pns, body)\<rfloor> in D" by auto
  from sees_wf_mdecl[OF wf this] have "\<D> body \<lfloor>{this}\<rfloor>"
    by(auto simp add: wf_mdecl_def)
  with sees ext show ?case by(clarsimp simp del: fun_upd_apply)
qed(auto simp add: ta_upd_simps)

lemma lifting_wf_def_ass: "wf_J_prog P \<Longrightarrow> lifting_wf final_expr (mred P) (\<lambda>t (e, x) m. \<D> e \<lfloor>dom x\<rfloor>)"
apply(unfold_locales)
apply(auto dest: red_preserves_defass red_def_ass_new_thread)
done

lemma def_ass_ts_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D; length vs = length Ts \<rbrakk> \<Longrightarrow>
  def_ass_ts_ok (thr (J_start_state P C M vs)) h"
apply(rule ts_okI)
apply(drule (1) sees_wf_mdecl)
apply(clarsimp simp add: wf_mdecl_def start_state_def split: if_split_asm)
done

end

subsection \<open>typeability\<close>

context J_heap_base begin

definition type_ok :: "'addr J_prog \<Rightarrow> env \<times> ty \<Rightarrow> 'addr expr \<Rightarrow> 'heap \<Rightarrow> bool"
where "type_ok P \<equiv> (\<lambda>(E, T) e c. (\<exists>T'. (P,E,c \<turnstile> e : T' \<and> P \<turnstile> T' \<le> T)))"

definition J_sconf_type_ET_start :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ('thread_id \<rightharpoonup> (env \<times> ty))"
where
  "J_sconf_type_ET_start P C M \<equiv>
   let (_, _, T, _) = method P C M
   in ([start_tid \<mapsto> (Map.empty, T)])"

lemma fixes E :: env
  assumes wf: "wf_J_prog P"
  shows red_type_newthread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
  and reds_type_newthread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; P,E,hp s \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow> \<exists>E T. P,E,hp s' \<turnstile> e'' : T \<and> P,hp s' \<turnstile> x'' (:\<le>) E"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedCallExternal s a U M Ts T' D vs ta va h' ta' e' s')
  from \<open>NewThread t'' (e'', x'') (hp s') \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>\<close> \<open>ta' = extTA2J P ta\<close>
  obtain C' M' a' where nt: "NewThread t'' (C', M', a') (hp s') \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
    and "extNTA2J P (C', M', a') = (e'', x'')" by fastforce
  from red_external_new_thread_sees[OF wf \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close> nt] \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close>
  obtain T pns body D where h'a': "typeof_addr h' a' = \<lfloor>Class_type C'\<rfloor>"
    and sees: " P \<turnstile> C' sees M': []\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D" by auto
  from sees_wf_mdecl[OF wf sees] obtain T where "P,[this \<mapsto> Class D] \<turnstile> body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "WTrt P (hp s') [this \<mapsto> Class D] body T" by(rule WT_implies_WTrt)
  moreover from sees have "P \<turnstile> C' \<preceq>\<^sup>* D" by(rule sees_method_decl_above)
  with h'a' have "P,h' \<turnstile> [this \<mapsto> Addr a'] (:\<le>) [this \<mapsto> Class D]" by(auto simp add: lconf_def conf_def)
  ultimately show ?case using h'a' sees \<open>s' = (h', lcl s)\<close>
    \<open>extNTA2J P (C', M', a') = (e'', x'')\<close> by(fastforce intro: sees_method_decl_above)
qed(fastforce simp add: ta_upd_simps)+

end

context J_heap_conf_base begin

definition sconf_type_ok :: "(env \<times> ty) \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr \<times> 'addr locals \<Rightarrow> 'heap \<Rightarrow> bool" 
where
  "sconf_type_ok ET t ex h \<equiv> fst ET \<turnstile> (h, snd ex) \<surd> \<and> type_ok P ET (fst ex) h \<and> P,h \<turnstile> t \<surd>t"

abbreviation sconf_type_ts_ok ::
  "('thread_id \<rightharpoonup> (env \<times> ty)) \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr locals) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "sconf_type_ts_ok \<equiv> ts_inv sconf_type_ok"

lemma ts_inv_ok_J_sconf_type_ET_start:
  "ts_inv_ok (thr (J_start_state P C M vs)) (J_sconf_type_ET_start P C M)"
by(rule ts_inv_okI)(simp add: start_state_def J_sconf_type_ET_start_def split_beta)

end

lemma (in J_heap) red_preserve_welltype:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; P,E,h \<turnstile> e'' : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e'' : T"
by(auto elim: WTrt_hext_mono dest!: red_hext_incr)

context J_heap_conf begin

lemma sconf_type_ts_ok_J_start_state:
  "\<lbrakk> wf_J_prog P; wf_start_state P C M vs \<rbrakk>
  \<Longrightarrow> sconf_type_ts_ok (J_sconf_type_ET_start P C M) (thr (J_start_state P C M vs)) (shr (J_start_state P C M vs))"
apply(erule wf_start_state.cases)
apply(rule ts_invI)
apply(simp add: start_state_def split: if_split_asm)
apply(frule (1) sees_wf_mdecl)
apply(auto simp add: wf_mdecl_def J_sconf_type_ET_start_def sconf_type_ok_def sconf_def type_ok_def)
   apply(erule hconf_start_heap)
  apply(erule preallocated_start_heap)
  apply(erule wf_prog_wf_syscls)
 apply(frule list_all2_lengthD)
 apply(auto simp add: wt_blocks confs_conv_map intro: WT_implies_WTrt)[1]
apply(erule tconf_start_heap_start_tid)
apply(erule wf_prog_wf_syscls)
done

lemma J_start_state_sconf_type_ok:
  assumes wf: "wf_J_prog P"
  and ok: "wf_start_state P C M vs"
  shows "ts_ok (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) (thr (J_start_state P C M vs)) start_heap"
using sconf_type_ts_ok_J_start_state[OF assms]
unfolding shr_start_state by(rule ts_inv_into_ts_ok_Ex)

end

context J_conf_read begin

lemma red_preserves_type_ok: 
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; wf_J_prog P; E \<turnstile> s \<surd>; type_ok P (E, T) e (hp s); P,hp s \<turnstile> t \<surd>t \<rbrakk> \<Longrightarrow> type_ok P (E, T) e' (hp s')"
apply(clarsimp simp add: type_ok_def)
apply(subgoal_tac "\<exists>T''. P,E,hp s' \<turnstile> e' : T'' \<and> P \<turnstile> T'' \<le> T'")
 apply(fast elim: widen_trans)
by(rule subject_reduction)

lemma lifting_inv_sconf_subject_ok:
  assumes wf: "wf_J_prog P"
  shows "lifting_inv final_expr (mred P) sconf_type_ok"
proof(unfold_locales)
  fix t x m ta x' m' i
  assume mred: "mred P t (x, m) ta (x', m')"
    and "sconf_type_ok i t x m"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  ultimately have sconf_type: "sconf_type_ok (E, T) t (e, l) m"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>" by auto
  from sconf_type have sconf: "E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m" and tconf: "P,m \<turnstile> t \<surd>t"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from \<open>E \<turnstile> (m, l) \<surd>\<close> \<open>P,E,m \<turnstile> e : T'\<close> red tconf
  have "E \<turnstile> (m', l') \<surd>" by(auto elim: red_preserves_sconf)
  moreover
  from red \<open>P,E,m \<turnstile> e : T'\<close> wf \<open>E \<turnstile> (m, l) \<surd>\<close> tconf
  obtain T'' where "P,E,m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T'"
    by(auto dest: subject_reduction)
  note \<open>P,E,m' \<turnstile> e' : T''\<close>
  moreover
  from \<open>P \<turnstile> T'' \<le> T'\<close> \<open>P \<turnstile> T' \<le> T\<close>
  have "P \<turnstile> T'' \<le> T" by(rule widen_trans)
  moreover from mred tconf have "P,m' \<turnstile> t \<surd>t" by(rule red_tconf.preserves_red)  
  ultimately have "sconf_type_ok (E, T) t (e', l') m'"
    by(auto simp add: sconf_type_ok_def type_ok_def)
  thus "sconf_type_ok i t x' m'" by simp
next
  fix t x m ta x' m' i t'' x''
  assume mred: "mred P t (x, m) ta (x', m')"
    and "sconf_type_ok i t x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto) 
  ultimately have sconf_type: "sconf_type_ok (E, T) t (e, l) m"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and nt: "NewThread t'' (e'', l'') m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
  from sconf_type have sconf: "E \<turnstile> (m, l) \<surd>" and "type_ok P (E, T) e m" and tconf: "P,m \<turnstile> t \<surd>t"
    by(auto simp add: sconf_type_ok_def)
  then obtain T' where "P,E,m \<turnstile> e : T'" "P \<turnstile> T' \<le> T" by(auto simp add: type_ok_def)
  from nt \<open>P,E,m \<turnstile> e : T'\<close> red have "\<exists>E T. P,E,m' \<turnstile> e'' : T \<and> P,m' \<turnstile> l'' (:\<le>) E"
    by(fastforce dest: red_type_newthread[OF wf])
  then obtain E'' T'' where "P,E'',m' \<turnstile> e'' : T''" "P,m' \<turnstile> l'' (:\<le>) E''" by blast
  moreover
  from sconf red \<open>P,E,m \<turnstile> e : T'\<close> tconf have "E \<turnstile> (m', l') \<surd>"
    by(auto intro: red_preserves_sconf)
  moreover from mred tconf \<open>NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<close> have "P,m' \<turnstile> t'' \<surd>t"
    by(rule red_tconf.preserves_NewThread)
  ultimately show "\<exists>i''. sconf_type_ok i'' t'' x'' m'"
    by(auto simp add: sconf_type_ok_def type_ok_def sconf_def)
next
  fix t x m ta x' m' i i'' t'' x''
  assume mred: "mred P t (x, m) ta (x', m')" 
    and "sconf_type_ok i t x m" 
    and "sconf_type_ok i'' t'' x'' m" 
  moreover obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
  moreover obtain e' l' where x' [simp]: "x' = (e', l')" by(cases x', auto)
  moreover obtain E T where i [simp]: "i = (E, T)" by(cases i, auto)
  moreover obtain e'' l'' where x'' [simp]: "x'' = (e'', l'')" by(cases x'', auto)
  moreover obtain E'' T'' where i'' [simp]: "i'' = (E'', T'')" by(cases i'', auto)
  ultimately have sconf_type: "sconf_type_ok (E, T) t (e, l) m"
    and red: "P,t \<turnstile> \<langle>e, (m, l)\<rangle> -ta\<rightarrow> \<langle>e', (m', l')\<rangle>"
    and sc: "sconf_type_ok (E'', T'') t'' (e'', l'') m" by auto
  from sconf_type obtain T' where "P,E,m \<turnstile> e : T'" and "P,m \<turnstile> t \<surd>t"
    by(auto simp add: sconf_type_ok_def type_ok_def)
  from sc have sconf: "E'' \<turnstile> (m, l'') \<surd>" and "type_ok P (E'', T'') e'' m" and "P,m \<turnstile> t'' \<surd>t"
    by(auto simp add: sconf_type_ok_def)
  then obtain T''' where "P,E'',m \<turnstile> e'' : T'''" "P \<turnstile> T''' \<le> T''" by(auto simp add: type_ok_def)
  moreover from red \<open>P,E'',m \<turnstile> e'' : T'''\<close> have "P,E'',m' \<turnstile> e'' : T'''"
    by(rule red_preserve_welltype)
  moreover from sconf red \<open>P,E,m \<turnstile> e : T'\<close> have "hconf m'"
    unfolding sconf_def by(auto dest: red_preserves_hconf)
  moreover {
    from red have "hext m m'" by(auto dest: red_hext_incr)
    moreover from sconf have "P,m \<turnstile> l'' (:\<le>) E''" "preallocated m"
      by(simp_all add: sconf_def)
    ultimately have "P,m' \<turnstile> l'' (:\<le>) E''" "preallocated m'"
      by(blast intro: lconf_hext preallocated_hext)+ }
  moreover from mred \<open>P,m \<turnstile> t \<surd>t\<close> \<open>P,m \<turnstile> t'' \<surd>t\<close>
  have "P,m' \<turnstile> t'' \<surd>t" by(rule red_tconf.preserves_other)
  ultimately have "sconf_type_ok (E'', T'') t'' (e'', l'') m'"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  thus "sconf_type_ok i'' t'' x'' m'" by simp
qed

end

subsection \<open>@{term "wf_red"}\<close>

context J_progress begin

context begin

declare red_mthr.actions_ok_iff [simp del]
declare red_mthr.actions_ok.cases [rule del]
declare red_mthr.actions_ok.intros [rule del]

lemma assumes wf: "wf_prog wf_md P"
  shows red_wf_red_aux:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; \<not> red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta; 
    sync_ok e; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
     \<forall>l. has_locks (ls $ l) t \<ge> expr_locks e l;
     ws t = None \<or> 
     (\<exists>a vs w T Ts Tr D. call e = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees wait: Ts\<rightarrow>Tr = Native in D \<and> ws t = \<lfloor>PostWS w\<rfloor>) \<rbrakk>
    \<Longrightarrow> \<exists>e'' s'' ta'. P,t \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e'',s''\<rangle> \<and> 
        (red_mthr.actions_ok (ls, (ts, m), ws, is) t ta' \<or> 
         red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta' \<and> red_mthr.actions_subset ta' ta)"
  (is "\<lbrakk> _; _; _; _; _; _; ?wakeup e s \<rbrakk> \<Longrightarrow> ?concl e s ta")
    and reds_wf_red_aux:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; \<not> red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta;
     sync_oks es; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
     \<forall>l. has_locks (ls $ l) t \<ge> expr_lockss es l;
     ws t = None \<or> 
     (\<exists>a vs w T Ts T Tr D. calls es = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees wait: Ts\<rightarrow>Tr = Native in D \<and> ws t = \<lfloor>PostWS w\<rfloor>) \<rbrakk>
    \<Longrightarrow> \<exists>es'' s'' ta'. P,t \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es'',s''\<rangle> \<and> 
        (red_mthr.actions_ok (ls, (ts, m), ws, is) t ta' \<or> 
         red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta' \<and> red_mthr.actions_subset ta' ta)"
proof(induct rule: red_reds.inducts)
  case (SynchronizedRed2 e s ta e' s' a)
  note IH = \<open>\<lbrakk>\<not> red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta; sync_ok e; hconf (hp s); P,hp s \<turnstile> t \<surd>t;
            \<forall>l. expr_locks e l \<le> has_locks (ls $ l) t; ?wakeup e s\<rbrakk>
            \<Longrightarrow> ?concl e s ta\<close>
  note \<open>\<not> red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta\<close>
  moreover from \<open>sync_ok (insync(a) e)\<close> have "sync_ok e" by simp
  moreover note \<open>hconf (hp s)\<close> \<open>P,hp s \<turnstile> t \<surd>t\<close>
  moreover from \<open>\<forall>l. expr_locks (insync(a) e) l \<le> has_locks (ls $ l) t\<close>
  have "\<forall>l. expr_locks e l \<le> has_locks (ls $ l) t" by(force split: if_split_asm)
  moreover from \<open>?wakeup (insync(a) e) s\<close> have "?wakeup e s" by auto
  ultimately have "?concl e s ta" by(rule IH)
  thus ?case by(fastforce intro: red_reds.SynchronizedRed2)
next
  case RedCall thus ?case
    by(auto simp add: is_val_iff contains_insync_conv contains_insyncs_conv red_mthr.actions_ok'_empty red_mthr.actions_ok'_ta_upd_obs dest: sees_method_fun)
next
  case (RedCallExternal s a U M Ts T D vs ta va h' ta' e' s')
  from \<open>?wakeup (addr a\<bullet>M(map Val vs)) s\<close>
  have "wset (ls, (ts, m), ws, is) t = None \<or> (M = wait \<and> (\<exists>w. wset (ls, (ts, m), ws, is) t = \<lfloor>PostWS w\<rfloor>))" by auto
  with wf  \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>\<close> \<open>P,hp s \<turnstile> t \<surd>t\<close> \<open>hconf (hp s)\<close>
  obtain ta'' va' h'' where red': "P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
    and aok: "red_mthr.actions_ok (ls, (ts, m), ws, is) t ta'' \<or>
              red_mthr.actions_ok' (ls, (ts, m), ws, is) t ta'' \<and> final_thread.actions_subset ta'' ta"
    by(rule red_external_wf_red)
  from aok \<open>ta' = extTA2J P ta\<close>
  have "red_mthr.actions_ok (ls, (ts, m), ws, is) t (extTA2J P ta'') \<or>
        red_mthr.actions_ok' (ls, (ts, m), ws, is) t (extTA2J P ta'') \<and> red_mthr.actions_subset (extTA2J P ta'') ta'"
    by(auto simp add: red_mthr.actions_ok'_convert_extTA red_mthr.actions_ok_iff elim: final_thread.actions_subset.cases del: subsetI)
  moreover from red' \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close> \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = Native in D\<close>
  obtain s'' e'' where "P,t \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta''\<rightarrow> \<langle>e'',s''\<rangle>"
    by(fastforce intro: red_reds.RedCallExternal)
  ultimately show ?case by blast
next
  case LockSynchronized
  hence False by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
next
  case (UnlockSynchronized a v s)
  from \<open>\<forall>l. expr_locks (insync(a) Val v) l \<le> has_locks (ls $ l) t\<close>
  have "has_lock (ls $ a) t" by(force split: if_split_asm)
  with UnlockSynchronized have False by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
next
  case (SynchronizedThrow2 a ad s)
  from \<open>\<forall>l. expr_locks (insync(a) Throw ad) l \<le> has_locks (ls $ l) t\<close>
  have "has_lock (ls $ a) t" by(force split: if_split_asm)
  with SynchronizedThrow2 have False
    by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
  thus ?case ..
next
  case BlockRed thus ?case by(simp)(blast intro: red_reds.intros)
qed
 (simp_all add: is_val_iff contains_insync_conv contains_insyncs_conv red_mthr.actions_ok'_empty
   red_mthr.actions_ok'_ta_upd_obs thread_action'_to_thread_action.simps red_mthr.actions_ok_iff
  split: if_split_asm del: split_paired_Ex,
  (blast intro: red_reds.intros elim: add_leE)+)

end

end

context J_heap_base begin

lemma shows red_ta_satisfiable:
  "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>s. red_mthr.actions_ok s t ta"
  and reds_ta_satisfiable:
  "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>s. red_mthr.actions_ok s t ta"
apply(induct rule: red_reds.inducts)
apply(fastforce simp add: lock_ok_las_def finfun_upd_apply intro: exI[where x="K$ None"] exI[where x="K$ \<lfloor>(t, 0)\<rfloor>"] may_lock.intros dest: red_external_ta_satisfiable[where final="final_expr :: ('addr expr \<times> 'addr locals) \<Rightarrow> bool"])+
done

end

context J_typesafe begin

lemma wf_progress: 
  assumes wf: "wf_J_prog P"
  shows "progress final_expr (mred P)
            (red_mthr.wset_Suspend_ok P ({s. sync_es_ok (thr s) (shr s) \<and> lock_ok (locks s) (thr s)} \<inter> {s. \<exists>Es. sconf_type_ts_ok Es (thr s) (shr s)} \<inter> {s. def_ass_ts_ok (thr s) (shr s)}))"
  (is "progress _ _ ?wf_state")
proof
  {
    fix s t x ta x' m' w
    assume "mred P t (x, shr s) ta (x', m')"
      and Suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    moreover obtain e xs where x: "x = (e, xs)" by(cases x)
    moreover obtain e' xs' where x': "x' = (e', xs')" by(cases x')
    ultimately have red: "P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', (m', xs')\<rangle>" by simp
    from red_Suspend_is_call[OF red Suspend]
    show "\<not> final_expr x'" by(auto simp add: x')
  }
  note Suspend_final = this
  {
    fix s
    assume s: "s \<in> ?wf_state"
    hence "lock_thread_ok (locks s) (thr s)"
      by(auto dest: red_mthr.wset_Suspend_okD1 intro: lock_ok_lock_thread_ok)
    moreover
    have "red_mthr.wset_final_ok (wset s) (thr s)"
    proof(rule red_mthr.wset_final_okI)
      fix t w
      assume "wset s t = \<lfloor>w\<rfloor>"
      from red_mthr.wset_Suspend_okD2[OF s this]
      obtain x0 ta x m1 w' ln'' and s0 :: "('addr, 'thread_id, 'heap) J_state"
        where mred: "mred P t (x0, shr s0) ta (x, m1)"
        and Suspend: "Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" 
        and tst: "thr s t = \<lfloor>(x, ln'')\<rfloor>" by blast
      from Suspend_final[OF mred Suspend] tst
      show " \<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> \<not> final_expr x" by blast
    qed
    ultimately show "lock_thread_ok (locks s) (thr s) \<and> red_mthr.wset_final_ok (wset s) (thr s)" ..
  }
next
  fix s t ex ta e'x' m'
  assume wfs: "s \<in> ?wf_state"
    and "thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>"
    and "mred P t (ex, shr s) ta (e'x', m')"
    and wait: "\<not> waiting (wset s t)"
  moreover obtain ls ts m ws "is" where s: "s = (ls, (ts, m), ws, is)" by(cases s) fastforce
  moreover obtain e x where ex: "ex = (e, x)" by(cases ex)
  moreover obtain e' x' where e'x': "e'x' = (e', x')" by(cases e'x')
  ultimately have tst: "ts t = \<lfloor>(ex, no_wait_locks)\<rfloor>" 
    and red: "P,t \<turnstile> \<langle>e, (m, x)\<rangle> -ta\<rightarrow> \<langle>e', (m', x')\<rangle>" by auto
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from wfs s obtain Es where aeos: "sync_es_ok ts m"
    and lockok: "lock_ok ls ts"
    and "sconf_type_ts_ok Es ts m"
    by(auto dest: red_mthr.wset_Suspend_okD1)
  with tst ex obtain E T where sconf: "sconf_type_ok (E, T) t (e, x) m"
    and aoe: "sync_ok e" by(fastforce dest: ts_okD ts_invD)
  then obtain T' where "hconf m" "P,E,m \<turnstile> e : T'" "preallocated m"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  from \<open>sconf_type_ts_ok Es ts m\<close> s have "thread_conf P (thr s) (shr s)"
    by(auto dest: ts_invD intro!: ts_okI simp add: sconf_type_ok_def)
  with \<open>thr s t = \<lfloor>(ex, no_wait_locks)\<rfloor>\<close> have "P,shr s \<turnstile> t \<surd>t" by(auto dest: ts_okD)

  show "\<exists>ta' x' m'. mred P t (ex, shr s) ta' (x', m') \<and> 
        (red_mthr.actions_ok s t ta' \<or> red_mthr.actions_ok' s t ta' \<and> red_mthr.actions_subset ta' ta)"
  proof(cases "red_mthr.actions_ok' s t ta")
    case True
    have "red_mthr.actions_subset ta ta" ..
    with True \<open>mred P t (ex, shr s) ta (e'x', m')\<close> show ?thesis by blast
  next
    case False
    from lock_okD2[OF lockok, OF tst[unfolded ex]]
    have locks: "\<forall>l. has_locks (ls $ l) t \<ge> expr_locks e l" by simp
    have "ws t = None \<or> (\<exists>a vs w T Ts Tr D. call e = \<lfloor>(a, wait, vs)\<rfloor> \<and> typeof_addr (hp (m, x)) a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees wait: Ts\<rightarrow>Tr = Native in D \<and> ws t = \<lfloor>PostWS w\<rfloor>)"
    proof(cases "ws t")
      case None thus ?thesis ..
    next
      case (Some w)
      with red_mthr.wset_Suspend_okD2[OF wfs, of t w] tst ex s
      obtain e0 x0 m0 ta0 w' s1 tta1 
        where red0: "P,t \<turnstile> \<langle>e0, (m0, x0)\<rangle> -ta0\<rightarrow> \<langle>e, (shr s1, x)\<rangle>"
        and Suspend: "Suspend w' \<in> set \<lbrace>ta0\<rbrace>\<^bsub>w\<^esub>"
        and s1: "P \<turnstile> s1 -\<triangleright>tta1\<rightarrow>* s" by auto 
      from red_Suspend_is_call[OF red0 Suspend] obtain a vs T Ts Tr D
        where call: "call e = \<lfloor>(a, wait, vs)\<rfloor>"
        and type: "typeof_addr m0 a = \<lfloor>T\<rfloor>" 
        and iec: "P \<turnstile> class_type_of T sees wait: Ts\<rightarrow>Tr = Native in D" by fastforce
      from red0 have "m0 \<unlhd> shr s1" by(auto dest: red_hext_incr)
      also from s1 have "shr s1 \<unlhd> shr s" by(rule RedT_hext_incr)
      finally have "typeof_addr (shr s) a = \<lfloor>T\<rfloor>" using type
        by(rule typeof_addr_hext_mono)
      moreover from Some wait s obtain w' where "ws t = \<lfloor>PostWS w'\<rfloor>"
        by(auto simp add: not_waiting_iff)
      ultimately show ?thesis using call iec s by auto
    qed
    from red_wf_red_aux[OF wf red False[unfolded s] aoe _ _ locks, OF _ _ this] \<open>hconf m\<close> \<open>P,shr s \<turnstile> t \<surd>t\<close> ex s
    show ?thesis by fastforce
  qed
next
  fix s t x
  assume wfs: "s \<in> ?wf_state"
    and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" 
    and nfin: "\<not> final_expr x"
  obtain e xs where x: "x = (e, xs)" by(cases x)
  from wfs have "def_ass_ts_ok (thr s) (shr s)" by(auto dest: red_mthr.wset_Suspend_okD1)
  with tst x have DA: "\<D> e \<lfloor>dom xs\<rfloor>" by(auto dest: ts_okD)
  from wfs obtain Es where "sconf_type_ts_ok Es (thr s) (shr s)"
    by(auto dest: red_mthr.wset_Suspend_okD1)
  with tst x obtain E T where "sconf_type_ok (E, T) t (e, xs) (shr s)" by(auto dest: ts_invD)
  then obtain T' where "hconf (shr s)" "P,E,shr s \<turnstile> e : T'"
    by(auto simp add: sconf_type_ok_def sconf_def type_ok_def)
  from red_progress(1)[OF wf_prog_wwf_prog[OF wf] this DA, where extTA="extTA2J P" and t=t] nfin x
  show "\<exists>ta x' m'. mred P t (x, shr s) ta (x', m')" by fastforce
next
  fix s t x xm ta xm'
  assume "s \<in> ?wf_state"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mred P t xm ta xm'"
    and "Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  thus "collect_waits ta = {}"
    by(auto dest: red_ta_Wakeup_no_Join_no_Lock_no_Interrupt simp: split_beta)
next
  fix s t x ta x' m'
  assume "s \<in> ?wf_state"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mred P t (x, shr s) ta (x', m')"
  thus "\<exists>s'. red_mthr.actions_ok s' t ta"
    by(fastforce simp add: split_beta dest!: red_ta_satisfiable)
qed

lemma redT_progress_deadlock:
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  and Red: "P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s"
  and ndead: "\<not> red_mthr.deadlock P s"
  shows "\<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
proof -
  let ?wf_state = "red_mthr.wset_Suspend_ok P ({s. sync_es_ok (thr s) (shr s) \<and> lock_ok (locks s) (thr s)} \<inter> {s. \<exists>Es. sconf_type_ts_ok Es (thr s) (shr s)} \<inter> {s. def_ass_ts_ok (thr s) (shr s)})"
  interpret red_mthr: progress
    final_expr "mred P" convert_RA ?wf_state
    using wf by(rule wf_progress)
  from wf_start obtain Ts T pns body D 
    where start: "start_heap_ok" "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D" "P,start_heap \<turnstile> vs [:\<le>] Ts"
    by(cases) auto
  from start have len: "length Ts = length vs" by(auto dest: list_all2_lengthD)

  have "invariant3p (mredT P) ?wf_state"
    by(rule red_mthr.invariant3p_wset_Suspend_ok) (intro invariant3p_IntI invariant3p_sync_es_ok_lock_ok[OF wf] lifting_inv.invariant3p_ts_inv[OF lifting_inv_sconf_subject_ok[OF wf]] lifting_wf.invariant3p_ts_ok[OF lifting_wf_def_ass[OF wf]])
  moreover note Red moreover
  have start': "J_start_state P C M vs \<in> ?wf_state"
    apply(rule red_mthr.wset_Suspend_okI)
     apply(blast intro: sconf_type_ts_ok_J_start_state sync_es_ok_J_start_state lock_ok_J_start_state def_ass_ts_ok_J_start_state start wf len len[symmetric] wf_start)
    apply(simp add: start_state_def split_beta)
    done
  ultimately have "s \<in> ?wf_state" unfolding red_mthr.RedT_def
    by(rule invariant3p_rtrancl3p)
  thus ?thesis using ndead by(rule red_mthr.redT_progress)
qed

lemma redT_progress_deadlocked:
  assumes wf: "wf_J_prog P" 
  and wf_start: "wf_start_state P C M vs"
  and Red: "P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s"
  and ndead:  "red_mthr.not_final_thread s t" "\<not> t \<in> red_mthr.deadlocked P s"
  shows "\<exists>t' ta' s'. P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
using wf wf_start Red
proof(rule redT_progress_deadlock)
  from ndead show "\<not> red_mthr.deadlock P s"
    unfolding red_mthr.deadlock_eq_deadlocked'
    by(auto simp add: red_mthr.deadlocked'_def)
qed

subsection \<open>Type safety proof\<close>

theorem TypeSafetyT:
  fixes C and M and ttas and Es
  defines "Es  == J_sconf_type_ET_start P C M"
  and     "Es' == upd_invs Es sconf_type_ok (concat (map (thr_a \<circ> snd) ttas))"
  assumes wf: "wf_J_prog P"
  and start_wf: "wf_start_state P C M vs"
  and RedT: "P \<turnstile> J_start_state P C M vs -\<triangleright>ttas\<rightarrow>* s'"
  and nored: "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow> s'')"
  shows "thread_conf P (thr s') (shr s')"
  and "thr s' t = \<lfloor>((e', x'), ln')\<rfloor> \<Longrightarrow>
       (\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,shr s' \<turnstile> v :\<le> T) \<and> ln' = no_wait_locks)
       \<or> (\<exists>a C. e' = Throw a \<and> typeof_addr (shr s') a = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable \<and> ln' = no_wait_locks)
       \<or> (t \<in> red_mthr.deadlocked P s' \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,shr s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)))"
     (is "_ \<Longrightarrow> ?thesis2")
  and "Es \<subseteq>\<^sub>m Es'"
proof -
  from start_wf obtain Ts T pns body D
    where start_heap: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
    by cases auto

  from RedT show "thread_conf P (thr s') (shr s')"
    by(rule red_tconf.RedT_preserves)(rule thread_conf_start_state[OF start_heap wf_prog_wf_syscls[OF wf]])

  show "Es \<subseteq>\<^sub>m Es'" using RedT ts_inv_ok_J_sconf_type_ET_start
    unfolding Es'_def Es_def by(rule red_mthr.RedT_upd_inv_ext)

  assume "thr s' t = \<lfloor>((e', x'), ln')\<rfloor>"
  moreover obtain ls' ts' m' ws' is' where s' [simp]: "s' = (ls', (ts', m'), ws', is')" by(cases s') fastforce
  ultimately have es't: "ts' t = \<lfloor>((e', x'), ln')\<rfloor>" by simp
  from wf have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog)
  from conf have len: "length vs = length Ts" by(rule list_all2_lengthD)
  from RedT def_ass_ts_ok_J_start_state[OF wf sees len] have defass': "def_ass_ts_ok ts' m'"
    by(fastforce dest: lifting_wf.RedT_preserves[OF lifting_wf_def_ass, OF wf])
  from RedT sync_es_ok_J_start_state[OF wf sees len[symmetric]] lock_ok_J_start_state[OF wf sees len[symmetric]]
  have lock': "lock_ok ls' ts'" by (fastforce dest: RedT_preserves_lock_ok[OF wf])
  from RedT sync_es_ok_J_start_state[OF wf sees len[symmetric]] have addr': "sync_es_ok ts' m'"
    by(fastforce dest: RedT_preserves_sync_ok[OF wf])
  from RedT sconf_type_ts_ok_J_start_state[OF wf start_wf]
  have sconf_subject': "sconf_type_ts_ok Es' ts' m'" unfolding Es'_def Es_def
    by(fastforce dest: lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok, OF wf] intro: thread_conf_start_state[OF _ wf_prog_wf_syscls[OF wf]])
  with es't obtain E T where ET: "Es' t = \<lfloor>(E, T)\<rfloor>" 
    and "sconf_type_ok (E, T) t (e', x') m'" by(auto dest!: ts_invD)
  { assume "final e'"
    have "ln' = no_wait_locks"
    proof(rule ccontr)
      assume "ln' \<noteq> no_wait_locks"
      then obtain l where "ln' $ l > 0"
        by(auto simp add: neq_no_wait_locks_conv)
      from lock' es't have "has_locks (ls' $ l) t + ln' $ l = expr_locks e' l"
        by(auto dest: lock_okD2)
      with \<open>ln' $ l > 0\<close> have "expr_locks e' l > 0" by simp
      moreover from \<open>final e'\<close> have "expr_locks e' l = 0" by(rule final_locks)
      ultimately show False by simp
    qed }
  note ln' = this
  { assume "\<exists>v. e' = Val v"
    then obtain v where v: "e' = Val v" by blast
    with sconf_subject' ET es't have "P,m' \<turnstile> v :\<le> T"
      by(auto dest: ts_invD simp add: type_ok_def sconf_type_ok_def conf_def)
    moreover from v ln' have "ln' = no_wait_locks" by(auto)
    ultimately have "\<exists>v. e' = Val v \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> P,m' \<turnstile> v :\<le> T \<and> ln' = no_wait_locks)"
      using ET v by blast }
  moreover
  { assume "\<exists>a. e' = Throw a"
    then obtain a where a: "e' = Throw a" by blast
    with sconf_subject' ET es't have "\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
      apply -
      apply(drule ts_invD, assumption)
      by(clarsimp simp add: type_ok_def sconf_type_ok_def)
    then obtain T' where "P,E,m' \<turnstile> e' : T'" and "P \<turnstile> T' \<le> T" by blast
    with a have "\<exists>C. typeof_addr m' a = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
      by(auto simp add: widen_Class)
    moreover from a ln' have "ln' = no_wait_locks" by(auto)
    ultimately have "\<exists>a C. e' = Throw a \<and> typeof_addr m' a = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable \<and> ln' = no_wait_locks"
      using a by blast }
  moreover
  { assume nfine': "\<not> final e'"
    with es't have "red_mthr.not_final_thread s' t"
      by(auto intro: red_mthr.not_final_thread.intros)
    with nored have "t \<in> red_mthr.deadlocked P s'"
      by -(erule contrapos_np, rule redT_progress_deadlocked[OF wf start_wf RedT])
    moreover 
    from \<open>sconf_type_ok (E, T) t (e', x') m'\<close>
    obtain T'' where "P,E,m' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T"
      by(auto simp add: sconf_type_ok_def type_ok_def)
    with ET have "\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
      by blast
    ultimately have "t \<in> red_mthr.deadlocked P s' \<and> (\<exists>E T. Es' t = \<lfloor>(E, T)\<rfloor> \<and> (\<exists>T'. P,E,m' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T))" .. }
  ultimately show ?thesis2 by simp(blast)
qed

end

end
