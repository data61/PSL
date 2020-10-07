(*  Title:      JinjaThreads/Framework/FWLiftingSem.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantic properties of lifted predicates\<close>

theory FWLiftingSem
imports
  FWSemantics
  FWLifting
begin

context multithreaded_base begin

lemma redT_preserves_ts_inv_ok:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; ts_inv_ok (thr s) I \<rbrakk>
  \<Longrightarrow> ts_inv_ok (thr s') (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>)"
by(erule redT.cases)(fastforce intro: ts_inv_ok_upd_invs ts_inv_ok_upd_ts redT_updTs_Some)+

lemma RedT_preserves_ts_inv_ok:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_inv_ok (thr s) I \<rbrakk>
  \<Longrightarrow> ts_inv_ok (thr s') (upd_invs I Q (concat (map (thr_a \<circ> snd) ttas)))"
by(induct rule: RedT_induct)(auto intro: redT_preserves_ts_inv_ok)

lemma redT_upd_inv_ext:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; ts_inv_ok (thr s) I \<rbrakk> \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(erule redT.cases, auto intro: ts_inv_ok_inv_ext_upd_invs)

lemma RedT_upd_inv_ext:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_inv_ok (thr s) I \<rbrakk>
         \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P (concat (map (thr_a \<circ> snd) ttas))"
proof(induct rule: RedT_induct)
  case refl thus ?case by simp
next
  case (step S TTAS S' T TA S'')
  hence "ts_inv_ok (thr S') (upd_invs I P (concat (map (thr_a \<circ> snd) TTAS)))"
    by -(rule RedT_preserves_ts_inv_ok)
  hence "upd_invs I P (concat (map (thr_a \<circ> snd) TTAS)) \<subseteq>\<^sub>m upd_invs (upd_invs I P (concat (map (thr_a \<circ> snd) TTAS))) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>" 
    using step by -(rule redT_upd_inv_ext)
  with step show ?case by(auto elim!: map_le_trans simp add: comp_def)
qed

end

locale lifting_inv = multithreaded final r convert_RA
  for final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  +
  fixes P :: "'i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes invariant_red: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m \<rbrakk> \<Longrightarrow> P i t x' m'"
  and invariant_NewThread: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> 
                            \<Longrightarrow> \<exists>i''. P i'' t'' x'' m'"
  and invariant_other: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P i t x m; P i'' t'' x'' m \<rbrakk> \<Longrightarrow> P i'' t'' x'' m'"
begin

lemma redT_updTs_invariant:
  fixes ln
  assumes tsiP: "ts_inv P I ts m"
  and red: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and tao: "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  and tst: "ts t = \<lfloor>(x, ln)\<rfloor>"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) m'"
proof(rule ts_invI)
  fix T X LN
  assume XLN: "(redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) T = \<lfloor>(X, LN)\<rfloor>"
  from tsiP \<open>ts t = \<lfloor>(x, ln)\<rfloor>\<close> obtain i where "I t = \<lfloor>i\<rfloor>" "P i t x m" 
    by(auto dest: ts_invD)
  show "\<exists>i. upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i\<rfloor> \<and> P i T X m'"
  proof(cases "T = t")
    case True
    from red \<open>P i t x m\<close> have "P i t x' m'" by(rule invariant_red)
    moreover from \<open>I t = \<lfloor>i\<rfloor>\<close> \<open>ts t = \<lfloor>(x, ln)\<rfloor>\<close> tao 
    have "upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>i\<rfloor>"
      by(simp add: upd_invs_Some)
    ultimately show ?thesis using True XLN by simp
  next
    case False
    show ?thesis
    proof(cases "ts T")
      case None
      with XLN tao False have "\<exists>m'. NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(auto dest: redT_updTs_new_thread)
      with red have nt: "NewThread T X m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by(auto dest: new_thread_memory)
      with red \<open>P i t x m\<close> have "\<exists>i''. P i'' T X m'" by(rule invariant_NewThread)
      hence "P (SOME i. P i T X m') T X m'" by(rule someI_ex)
      with nt tao show ?thesis by(auto intro: SOME_new_thread_upd_invs) 
    next
      case (Some a)
      obtain X' LN' where [simp]: "a = (X', LN')" by(cases a)
      with \<open>ts T = \<lfloor>a\<rfloor>\<close> have esT: "ts T = \<lfloor>(X', LN')\<rfloor>" by simp
      hence "redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(X', LN')\<rfloor>"
        using \<open>thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<close> by(auto intro: redT_updTs_Some)
      moreover from esT tsiP obtain i' where "I T = \<lfloor>i'\<rfloor>" "P i' T X' m"
        by(auto dest: ts_invD)
      from red \<open>P i t x m\<close> \<open>P i' T X' m\<close>
      have "P i' T X' m'" by(rule invariant_other)
      moreover from \<open>I T = \<lfloor>i'\<rfloor>\<close> esT tao have "upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>i'\<rfloor>"
        by(simp add: upd_invs_Some)
      ultimately show ?thesis using XLN False by simp
    qed
  qed
qed

theorem redT_invariant:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esinvP: "ts_inv P I (thr s) (shr s)"
  shows "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (thr s') (shr s')"
using redT
proof(cases rule: redT_elims)
  case acquire thus ?thesis using esinvP 
    by(auto intro!: ts_invI split: if_split_asm dest: ts_invD)
next
  case (normal x x' m')
  with esinvP
  have "ts_inv P (upd_invs I P \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) m'"
    by(auto intro: redT_updTs_invariant)
  thus ?thesis using normal by simp
qed

theorem RedT_invariant:
  assumes RedT: "s -\<triangleright>ttas\<rightarrow>* s'"
  and esinvQ: "ts_inv P I (thr s) (shr s)"
  shows "ts_inv P (upd_invs I P (concat (map (thr_a \<circ> snd) ttas))) (thr s') (shr s')"
using RedT esinvQ
proof(induct rule: RedT_induct)
  case refl thus ?case by(simp (no_asm))
next
  case (step S TTAS S' T TA S'')
  note IH = \<open>ts_inv P I (thr S) (shr S) \<Longrightarrow> ts_inv P (upd_invs I P (concat (map (thr_a \<circ> snd) TTAS))) (thr S') (shr S')\<close>
  with \<open>ts_inv P I (thr S) (shr S)\<close>
  have "ts_inv P (upd_invs I P (concat (map (thr_a \<circ> snd) TTAS))) (thr S') (shr S')" by blast
  with \<open>S' -T\<triangleright>TA\<rightarrow> S''\<close> 
  have "ts_inv P (upd_invs (upd_invs I P (concat (map (thr_a \<circ> snd) TTAS))) P \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) (thr S'') (shr S'')"
    by(rule redT_invariant)
  thus ?case by(simp add: comp_def)
qed

lemma invariant3p_ts_inv: "invariant3p redT {s. \<exists>I. ts_inv P I (thr s) (shr s)}"
by(auto intro!: invariant3pI dest: redT_invariant)

end

locale lifting_wf = multithreaded final r convert_RA
  for final :: "'x \<Rightarrow> bool" 
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  +
  fixes P :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool"
  assumes preserves_red: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m \<rbrakk> \<Longrightarrow> P t x' m'"
  and preserves_NewThread: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m; NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> 
                            \<Longrightarrow> P t'' x'' m'"
  and preserves_other: "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; P t x m; P t'' x'' m \<rbrakk> \<Longrightarrow> P t'' x'' m'"
begin

lemma lifting_inv: "lifting_inv final r (\<lambda>_ :: unit. P)"
by(unfold_locales)(blast intro: preserves_red preserves_NewThread preserves_other)+

lemma redT_updTs_preserves:
  fixes ln
  assumes esokQ: "ts_ok P ts m"
  and red: "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and "ts t = \<lfloor>(x, ln)\<rfloor>"
  and "thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "ts_ok P (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) m'"
proof -
  interpret lifting_inv final r convert_RA "\<lambda>_ :: unit. P" by(rule lifting_inv)
  from esokQ obtain I :: "'t \<rightharpoonup> unit" where "ts_inv (\<lambda>_. P) I ts m" by(rule ts_ok_into_ts_inv_const)
  hence "ts_inv (\<lambda>_. P) (upd_invs I (\<lambda>_. P) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', ln'))) m'"
    using red \<open>thread_oks ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<close> \<open>ts t = \<lfloor>(x, ln)\<rfloor>\<close> by(rule redT_updTs_invariant)
  thus ?thesis by(rule ts_inv_const_into_ts_ok)
qed

theorem redT_preserves:
  assumes redT: "s -t\<triangleright>ta\<rightarrow> s'"
  and esokQ: "ts_ok P (thr s) (shr s)"
  shows "ts_ok P (thr s') (shr s')"
proof -
  interpret lifting_inv final r convert_RA "\<lambda>_ :: unit. P" by(rule lifting_inv)
  from esokQ obtain I :: "'t \<rightharpoonup> unit" where "ts_inv (\<lambda>_. P) I (thr s) (shr s)" by(rule ts_ok_into_ts_inv_const)
  with redT have "ts_inv (\<lambda>_. P) (upd_invs I (\<lambda>_. P) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (thr s') (shr s')" by(rule redT_invariant)
  thus ?thesis by(rule ts_inv_const_into_ts_ok)
qed

theorem RedT_preserves:
  "\<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ts_ok P (thr s) (shr s) \<rbrakk> \<Longrightarrow> ts_ok P (thr s') (shr s')"
by(erule (1) RedT_lift_preserveD)(fastforce elim: redT_preserves)

lemma invariant3p_ts_ok: "invariant3p redT {s. ts_ok P (thr s) (shr s)}"
by(auto intro!: invariant3pI intro: redT_preserves)

end

lemma lifting_wf_Const [intro!]: 
  assumes "multithreaded final r"
  shows "lifting_wf final r (\<lambda>t x m. k)"
proof -
  interpret multithreaded final r using assms .
  show ?thesis by unfold_locales blast+
qed

end
