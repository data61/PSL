(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)

section \<open>Preservation of deadlock for the JVMs\<close>

theory JVMDeadlocked
imports
  BVProgressThreaded
begin

context JVM_progress begin

lemma must_sync_preserved_d:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ml: "execd_mthr.must_sync P t (xcp, frs) h" 
  and hext: "hext h h'"
  and hconf': "hconf h'"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  shows "execd_mthr.must_sync P t (xcp, frs) h'"
proof(rule execd_mthr.must_syncI)
  from ml obtain ta xcp' frs' m'
    where red: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    by(auto elim: execd_mthr.must_syncE)
  then obtain f Frs
    where check: "check P (xcp, h, frs)"
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h, frs)"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE)
  from cs hext hconf' have cs': "\<Phi> \<turnstile> t: (xcp, h', frs) \<surd>"
    by(rule correct_state_hext_mono)
  then obtain ta \<sigma>' where exec: "P,t \<turnstile> (xcp, h', frs) -ta-jvm\<rightarrow> \<sigma>'"
    by(auto dest: progress[OF wf])
  hence "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal \<sigma>'"
    unfolding welltyped_commute[OF wf cs'] .
  moreover from exec have "\<exists>s. exec_mthr.actions_ok s t ta" by(rule exec_ta_satisfiable)
  ultimately show "\<exists>ta x' m' s. mexecd P t ((xcp, frs), h') ta (x', m') \<and> exec_mthr.actions_ok s t ta"
    by(cases \<sigma>')(fastforce simp del: split_paired_Ex)
qed

lemma can_sync_devreserp_d:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and cl': "execd_mthr.can_sync P t (xcp, frs) h' L" 
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  and hext: "hext h h'"
  and hconf': "hconf h'"
  shows "\<exists>L'\<subseteq>L. execd_mthr.can_sync P t (xcp, frs) h L'"
proof -
  from cl' obtain ta xcp' frs' m'
    where red: "P,t \<turnstile> Normal (xcp, h', frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
    by -(erule execd_mthr.can_syncE, auto)
  then obtain f Frs
    where check: "check P (xcp, h', frs)"
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h', frs)"
    and [simp]: "frs = f # Frs"
    by(auto elim: jvmd_NormalE simp add: finfun_upd_apply)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by (cases f, blast)
  from cs obtain ST LT Ts T mxs mxl ins xt where
    hconf:  "hconf h" and
    tconf:  "P,h \<turnstile> t \<surd>t" and
    meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(mxs, mxl, ins, xt)\<rfloor> in C" and
    \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
    frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames: "conf_fs P h \<Phi> M (size Ts) T Frs" 
    by (fastforce simp add: correct_state_def dest: sees_method_fun)
  from cs have "exec P t (xcp, h, f # Frs) \<noteq> {}"
    by(auto dest!: progress[OF wf] simp add: exec_1_iff)
  with no_type_error[OF wf cs] have check': "check P (xcp, h, frs)"
    by(auto simp add: exec_d_def split: if_split_asm)
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  from tconf hext have tconf': "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
  show ?thesis
  proof(cases xcp)
    case [simp]: (Some a)
    with exec have [simp]: "m' = h'" by(auto)
    from \<open>\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>\<close> obtain D where D: "typeof_addr h a = \<lfloor>Class_type D\<rfloor>"
      by(auto simp add: correct_state_def)
    with hext have "cname_of h a = cname_of h' a" by(auto dest: hext_objD simp add: cname_of_def)
    with exec have "(ta, xcp', h, frs') \<in> exec P t (xcp, h, frs)" by auto
    moreover from check D hext have "check P (xcp, h, frs)"
      by(auto simp add: check_def check_xcpt_def dest: hext_objD)
    ultimately have "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h, frs')"
      by -(rule exec_1_d_NormalI, simp only: exec_d_def if_True)
    with L have "execd_mthr.can_sync P t (xcp, frs) h L"
      by(auto intro: execd_mthr.can_syncI)
    thus ?thesis by auto
  next
    case [simp]: None

    note [simp] = defs1 list_all2_Cons2

    from frame have ST: "P,h \<turnstile> stk [:\<le>] ST"
      and LT: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
      and pc: "pc < length ins" by simp_all
    from wf meth pc have wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
      by(rule wt_jvm_prog_impl_wt_instr)

    from \<open>\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>\<close>
    have "\<exists>ta \<sigma>'. P,t \<turnstile> (xcp, h, f # Frs) -ta-jvm\<rightarrow> \<sigma>'"
      by(auto dest: progress[OF wf] simp del: correct_state_def split_paired_Ex)
    with exec meth have "\<exists>ta' \<sigma>'. (ta', \<sigma>') \<in> exec P t (xcp, h, frs) \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
    proof(cases "ins ! pc")
      case (Invoke M' n)
      show ?thesis
      proof(cases "stk ! n = Null")
        case True with Invoke exec meth show ?thesis by simp
      next
        case False
        with check meth obtain a where a: "stk ! n = Addr a" and n: "n < length stk"
          by(auto simp add: check_def is_Ref_def Invoke)
        from frame have stk: "P,h \<turnstile> stk [:\<le>] ST" by(auto simp add: conf_f_def)
        hence "P,h \<turnstile> stk ! n :\<le> ST ! n" using n by(rule list_all2_nthD)
        with a obtain ao Ta where Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
          by(auto simp add: conf_def)
        from hext Ta have Ta': "typeof_addr h' a = \<lfloor>Ta\<rfloor>" by(rule typeof_addr_hext_mono)
        with check a meth Invoke False obtain D Ts' T' meth D'
          where C: "D = class_type_of Ta"
          and sees': "P \<turnstile> D sees M':Ts'\<rightarrow>T' = meth in D'"
          and params: "P,h' \<turnstile> rev (take n stk) [:\<le>] Ts'"
          by(auto simp add: check_def has_method_def)
        show ?thesis
        proof(cases "meth")
          case Some
          with exec meth a Ta Ta' Invoke n sees' C show ?thesis by(simp add: split_beta)
        next
          case None
          with exec meth a Ta Ta' Invoke n sees' C
          obtain ta' va h'' where ta': "ta = extTA2JVM P ta'"
            and va: "(xcp', m', frs') = extRet2JVM n h'' stk loc C M pc Frs va"
            and exec': "(ta', va, h'') \<in> red_external_aggr P t a M' (rev (take n stk)) h'"
            by(fastforce)
          from va have [simp]: "h'' = m'" by(cases va) simp_all
          note Ta moreover from None sees' wfp have "D'\<bullet>M'(Ts') :: T'" by(auto intro: sees_wf_native)
          with C sees' params Ta' None have "P,h' \<turnstile> a\<bullet>M'(rev (take n stk)) : T'"
            by(auto simp add: external_WT'_iff confs_conv_map)
          with wfp exec' tconf' have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h'\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
            by(simp add: WT_red_external_list_conv)

          from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
          then obtain Ts where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Ts"
            by(auto simp add: confs_conv_map)
          hence "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Ts)" by(simp only: rev_map[symmetric])
          moreover hence "map typeof\<^bsub>h'\<^esub> (rev (take n stk)) = map Some (rev Ts)" using hext by(rule map_typeof_hext_mono)
          with \<open>P,h' \<turnstile> a\<bullet>M'(rev (take n stk)) : T'\<close> \<open>D'\<bullet>M'(Ts') :: T'\<close> sees' C Ta' Ta
          have "P \<turnstile> rev Ts [\<le>] Ts'" by cases (auto dest: sees_method_fun)
          ultimately have "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : T'"
            using Ta C sees' params None \<open>D'\<bullet>M'(Ts') :: T'\<close>
            by(auto simp add: external_WT'_iff confs_conv_map)
          from red_external_wt_hconf_hext[OF wfp red hext this tconf hconf]
          obtain ta'' va' h''' where "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h'''\<rangle>"
            and ta'': "collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>" 
            "collect_cond_actions \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub> = collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>"
            "collect_interrupts \<lbrace>ta''\<rbrace>\<^bsub>i\<^esub> = collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub>"
            by auto
          with None a Ta Invoke meth Ta' n C sees'
          have "(extTA2JVM P ta'', extRet2JVM n h''' stk loc C M pc Frs va') \<in> exec P t (xcp, h, frs)"
            by(force intro: red_external_imp_red_external_aggr simp del: split_paired_Ex)
          with ta'' ta' show ?thesis by(fastforce simp del: split_paired_Ex)
        qed
      qed
    qed(auto 4 4 split: if_split_asm simp add: split_beta ta_upd_simps exec_1_iff intro: rev_image_eqI simp del: split_paired_Ex)
    with check' have "\<exists>ta' \<sigma>'. P,t \<turnstile> Normal (xcp, h, frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and>
      collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
      apply clarify
      apply(rule exI conjI)+
      apply(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      done
    with L show ?thesis
      apply -
      apply(erule exE conjE|rule exI conjI)+
      prefer 2
      apply(rule_tac x'="(fst \<sigma>', snd (snd \<sigma>'))" and m'="fst (snd \<sigma>')" in execd_mthr.can_syncI)
      apply auto
      done
  qed
qed

end

context JVM_typesafe begin

lemma execd_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "preserve_deadlocked JVM_final (mexecd P) convert_RA (correct_jvm_state \<Phi>)"
proof(unfold_locales)
  show "invariant3p (mexecdT P) (correct_jvm_state \<Phi>)"
    by(rule invariant3p_correct_jvm_state_mexecdT[OF wf])
next
  fix s t' ta' s' t x ln
  assume s: "s \<in> correct_jvm_state \<Phi>"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "execd_mthr.must_sync P t x (shr s)"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "execd_mthr.must_sync P t (xcp, frs) (shr s)" by simp
  moreover from s have cs': "correct_state_ts \<Phi> (thr s) (shr s)" by(simp add: correct_jvm_state_def)
  with tst have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')" by(rule execd_hext)
  moreover from wf red cs' have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(rule lifting_wf.redT_preserves[OF lifting_wf_correct_state_d])
  from red tst have "thr s' t \<noteq> None"
    by(cases s)(cases s', rule notI, auto dest: execd_mthr.redT_thread_not_disappear)
  with \<open>correct_state_ts \<Phi> (thr s') (shr s')\<close> have "hconf (shr s')"
    by(auto dest: ts_okD simp add: correct_state_def)
  ultimately have "execd_mthr.must_sync P t (xcp, frs) (shr s')"
    by-(rule must_sync_preserved_d[OF wf])
  thus "execd_mthr.must_sync P t x (shr s')" by simp
next
  fix s t' ta' s' t x ln L
  assume s: "s \<in> correct_jvm_state \<Phi>"
    and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    and "execd_mthr.can_sync P t x (shr s') L"
  moreover obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
  ultimately have ml: "execd_mthr.can_sync P t (xcp, frs) (shr s') L" by simp
  moreover from s have cs': "correct_state_ts \<Phi> (thr s) (shr s)" by(simp add: correct_jvm_state_def)
  with tst have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
  moreover from red have "hext (shr s) (shr s')" by(rule execd_hext)
  moreover from red tst have "thr s' t \<noteq> None"
    by(cases s)(cases s', rule notI, auto dest: execd_mthr.redT_thread_not_disappear)
  from red cs' have "correct_state_ts \<Phi> (thr s') (shr s')"
    by(rule lifting_wf.redT_preserves[OF lifting_wf_correct_state_d[OF wf]])
  with \<open>thr s' t \<noteq> None\<close> have "hconf (shr s')"
    by(auto dest: ts_okD simp add: correct_state_def)
  ultimately have "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t (xcp, frs) (shr s) L'"
    by-(rule can_sync_devreserp_d[OF wf])
  thus "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t x (shr s) L'" by simp
qed

end


text \<open>and now everything again for the aggresive VM\<close>

context JVM_heap_conf_base' begin

lemma must_lock_d_eq_must_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> execd_mthr.must_sync P t (xcp, frs) h = exec_mthr.must_sync P t (xcp, frs) h"
apply(rule iffI)
 apply(rule exec_mthr.must_syncI)
 apply(erule execd_mthr.must_syncE)
 apply(simp only: mexec_eq_mexecd)
 apply(blast)
apply(rule execd_mthr.must_syncI)
apply(erule exec_mthr.must_syncE)
apply(simp only: mexec_eq_mexecd[symmetric])
apply(blast)
done

lemma can_lock_d_eq_can_lock:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk>
  \<Longrightarrow> execd_mthr.can_sync P t (xcp, frs) h L = exec_mthr.can_sync P t (xcp, frs) h L"
apply(rule iffI)
 apply(erule execd_mthr.can_syncE)
 apply(rule exec_mthr.can_syncI)
   apply(simp only: mexec_eq_mexecd)
  apply(assumption)+
apply(erule exec_mthr.can_syncE)
apply(rule execd_mthr.can_syncI)
 by(simp only: mexec_eq_mexecd)

end

context JVM_typesafe begin

lemma exec_preserve_deadlocked:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "preserve_deadlocked JVM_final (mexec P) convert_RA (correct_jvm_state \<Phi>)"
proof -
  interpret preserve_deadlocked JVM_final "mexecd P" convert_RA "correct_jvm_state \<Phi>"
    by(rule execd_preserve_deadlocked) fact+

  { fix s t' ta' s' t x
    assume s: "s \<in> correct_jvm_state \<Phi>"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvm\<^esub> s'"
      and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from s have css: "correct_state_ts \<Phi> (thr s) (shr s)" by(simp add: correct_jvm_state_def)
    with red have redd: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow>\<^bsub>jvmd\<^esub> s'" by(simp add: mexecT_eq_mexecdT[OF wf])
    from css tst have cst: "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from redd have cst': "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
    proof(cases rule: execd_mthr.redT_elims)
      case acquire with cst show ?thesis by simp
    next
      case (normal X X' M' ws')
      obtain XCP FRS where X [simp]: "X = (XCP, FRS)" by(cases X, auto)
      obtain XCP' FRS' where X' [simp]: "X' = (XCP', FRS')" by(cases X', auto)
      from \<open>mexecd P t' (X, shr s) ta' (X', M')\<close>
      have "P,t' \<turnstile> Normal (XCP, shr s, FRS) -ta'-jvmd\<rightarrow> Normal (XCP', M', FRS')" by simp
      moreover from \<open>thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>\<close> css
      have "\<Phi> \<turnstile> t': (XCP, shr s, FRS) \<surd>" by(auto dest: ts_okD)
      ultimately have "\<Phi> \<turnstile> t': (XCP, M', FRS) \<surd>" by -(rule correct_state_heap_change[OF wf])
      moreover from lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] css, OF \<open>mexecd P t' (X, shr s) ta' (X', M')\<close> \<open>thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>\<close>, of no_wait_locks] \<open>thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>\<close>
      have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t' \<mapsto> (X', no_wait_locks))) M'" by simp
      ultimately have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>) M'"
        using \<open>thr s t' = \<lfloor>(X, no_wait_locks)\<rfloor>\<close> \<open>thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>\<close>
        apply(auto intro!: ts_okI dest: ts_okD)
        apply(case_tac "t=t'")
         apply(fastforce dest: redT_updTs_Some)
        apply(drule_tac t=t in ts_okD, fastforce+)
        done
      hence "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>) (shr s')" 
        using \<open>s' = (redT_updLs (locks s) t' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>, (redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>(t' \<mapsto> (X', redT_updLns (locks s) t' no_wait_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>)), M'), ws', redT_updIs (interrupts s) \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub>)\<close>
        by simp
      moreover from tst \<open>thread_oks (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>\<close>
      have "redT_updTs (thr s) \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> t = \<lfloor>(x, no_wait_locks)\<rfloor>" by(auto intro: redT_updTs_Some)
      ultimately show ?thesis by(auto dest: ts_okD)
    qed
    { assume "exec_mthr.must_sync P t x (shr s)"
      hence ml: "exec_mthr.must_sync P t (xcp, frs) (shr s)" by simp
      with cst have "execd_mthr.must_sync P t (xcp, frs) (shr s)"
        by(auto dest: must_lock_d_eq_must_lock[OF wf])
      with s redd tst have "execd_mthr.must_sync P t x (shr s')"
        unfolding x by(rule can_lock_preserved)
      with cst' have "exec_mthr.must_sync P t x (shr s')"
        by(auto dest: must_lock_d_eq_must_lock[OF wf]) }
    note ml = this
    { fix L
      assume "exec_mthr.can_sync P t x (shr s') L"
      hence cl: "exec_mthr.can_sync P t (xcp, frs) (shr s') L" by simp
      with cst' have "execd_mthr.can_sync P t (xcp, frs) (shr s') L"
        by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with s redd tst
      have "\<exists>L' \<subseteq> L. execd_mthr.can_sync P t x (shr s) L'"
        unfolding x by(rule can_lock_devreserp)
      then obtain L' where "execd_mthr.can_sync P t x (shr s) L'" 
        and L': "L'\<subseteq> L" by blast
      with cst have "exec_mthr.can_sync P t x (shr s) L'"
        by(auto dest: can_lock_d_eq_can_lock[OF wf])
      with L' have "\<exists>L' \<subseteq> L. exec_mthr.can_sync P t x (shr s) L'"
        by(blast) }
    note this ml }
  moreover have "invariant3p (mexecT P) (correct_jvm_state \<Phi>)" by(rule invariant3p_correct_jvm_state_mexecT[OF wf])
  ultimately show ?thesis by(unfold_locales)
qed

end

end

