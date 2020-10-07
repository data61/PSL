(*  Title:      JinjaThreads/BV/JVMDeadlocked.thy
    Author:     Andreas Lochbihler
*)

section \<open>Progress result for both of the multithreaded JVMs\<close>

theory BVProgressThreaded
imports
  "../Framework/FWProgress"
  "../Framework/FWLTS"
  BVNoTypeError
  "../JVM/JVMThreaded"
begin

lemma (in JVM_heap_conf_base') mexec_eq_mexecd:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: (xcp, h, frs) \<surd> \<rbrakk> \<Longrightarrow> mexec P t ((xcp, frs), h) = mexecd P t ((xcp, frs), h)"
apply(auto intro!: ext)
 apply(unfold exec_1_iff)
 apply(drule no_type_error)
  apply(assumption)
 apply(clarify)
 apply(rule exec_1_d_NormalI)
  apply(assumption)
 apply(simp add: exec_d_def split: if_split_asm)
apply(erule jvmd_NormalE, auto)
done

(* conformance lifted to multithreaded case *)

context JVM_heap_conf_base begin

abbreviation 
  correct_state_ts :: "ty\<^sub>P \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state) thread_info \<Rightarrow> 'heap \<Rightarrow> bool"
where
  "correct_state_ts \<Phi> \<equiv> ts_ok (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"

lemma correct_state_ts_thread_conf:
  "correct_state_ts \<Phi> (thr s) (shr s) \<Longrightarrow> thread_conf P (thr s) (shr s)"
by(erule ts_ok_mono)(auto simp add: correct_state_def)

lemma invoke_new_thread:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl0,ins,xt)\<rfloor> in C"
  and "ins ! pc = Invoke Type.start 0"
  and "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  and "\<Phi> \<turnstile> t: (None, h, (stk, loc, C, M, pc) # frs) \<surd>"
  and "typeof_addr h (thread_id2addr a) = \<lfloor>Class_type D\<rfloor>"
  and "P \<turnstile> D \<preceq>\<^sup>* Thread"
  and "P \<turnstile> D sees run:[]\<rightarrow>Void=\<lfloor>(mxs', mxl0', ins',xt')\<rfloor> in D'"
  shows "\<Phi> \<turnstile> a: (None, h, [([], Addr (thread_id2addr a) # replicate mxl0' undefined_value, D', run, 0)]) \<surd>"
proof -
  from \<open>\<Phi> \<turnstile> t: (None, h, (stk, loc, C, M, pc) # frs) \<surd>\<close>
  have "hconf h" and "preallocated h" by(simp_all add: correct_state_def)
  moreover
  from \<open>P \<turnstile> D sees run:[]\<rightarrow>Void=\<lfloor>(mxs', mxl0', ins',xt')\<rfloor> in D'\<close>
  have "P \<turnstile> D' sees run:[]\<rightarrow>Void=\<lfloor>(mxs', mxl0', ins',xt')\<rfloor> in D'"
    by(rule sees_method_idemp)
  with \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>
  have "wt_start P D' [] mxl0' (\<Phi> D' run)" and "ins' \<noteq> []"
    by(auto dest: wt_jvm_prog_impl_wt_start)
  then obtain LT' where LT': "\<Phi> D' run ! 0 = Some ([], LT')"
    by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
  moreover
  have "conf_f P h ([], LT') ins' ([], Addr (thread_id2addr a) # replicate mxl0' undefined_value, D', run, 0)"
  proof -
    let ?LT = "OK (Class D') # (replicate mxl0' Err)"
    have "P,h \<turnstile> replicate mxl0' undefined_value [:\<le>\<^sub>\<top>] replicate mxl0' Err" by simp
    also from \<open>P \<turnstile> D sees run:[]\<rightarrow>Void=\<lfloor>(mxs', mxl0', ins',xt')\<rfloor> in D'\<close>
    have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
    with \<open>typeof_addr h (thread_id2addr a) = \<lfloor>Class_type D\<rfloor>\<close>
    have "P,h \<turnstile> Addr (thread_id2addr a) :\<le> Class D'"
      by(simp add: conf_def)
    ultimately have "P,h \<turnstile> Addr (thread_id2addr a) # replicate mxl0' undefined_value [:\<le>\<^sub>\<top>] ?LT" by(simp)
    also from \<open>wt_start P D' [] mxl0' (\<Phi> D' run)\<close> LT'
    have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
    finally have "P,h \<turnstile> Addr (thread_id2addr a) # replicate mxl0' undefined_value [:\<le>\<^sub>\<top>] LT'" .
    with \<open>ins' \<noteq> []\<close> show ?thesis by(simp add: conf_f_def)
  qed
  moreover from \<open>typeof_addr h (thread_id2addr a) = \<lfloor>Class_type D\<rfloor>\<close> \<open>P \<turnstile> D \<preceq>\<^sup>* Thread\<close>
  have "P,h \<turnstile> a \<surd>t" by(rule tconfI)
  ultimately show ?thesis using \<open>P \<turnstile> D' sees run:[]\<rightarrow>Void=\<lfloor>(mxs', mxl0', ins',xt')\<rfloor> in D'\<close>
    by(fastforce simp add: correct_state_def)
qed

lemma exec_new_threadE:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and "\<Phi> \<turnstile> t: \<sigma> \<surd>"
  and "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []"
  obtains h frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n Ta ta' va  Us Us' U m' D'
  where "\<sigma> = (None, h, (stk, loc, C, M, pc) # frs)"
  and "(ta, \<sigma>') \<in> exec P t (None, h, (stk, loc, C, M, pc) # frs)"
  and "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl0, ins, xt)\<rfloor> in C"
  and "stk ! n = Addr a"
  and "ins ! pc = Invoke M' n"
  and "n < length stk"
  and "typeof_addr h a = \<lfloor>Ta\<rfloor>"
  and "is_native P Ta M'"
  and "ta = extTA2JVM P ta'"
  and "\<sigma>' = extRet2JVM n m' stk loc C M pc frs va"
  and "(ta', va, m') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
  and "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
  and "P \<turnstile> class_type_of Ta sees M':Us'\<rightarrow>U = Native in D'"
  and "D'\<bullet>M'(Us') :: U"
  and "P \<turnstile> Us [\<le>] Us'"
proof -
  from \<open>P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'\<close> obtain h f Frs xcp
    where check: "check P \<sigma>"
    and exec: "(ta, \<sigma>') \<in> exec P t \<sigma>"
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)"
    by(cases f, blast)
  from \<open>\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []\<close> exec have [simp]: "xcp = None" by(cases xcp) auto
  from \<open>\<Phi> \<turnstile> t: \<sigma> \<surd>\<close>
  obtain Ts T mxs mxl0 ins xt ST LT 
    where "hconf h" "preallocated h"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl0, ins, xt)\<rfloor> in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastforce simp add: correct_state_def)
  from check \<open>\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>\<close> sees
  have checkins: "check_instr (ins ! pc) P h stk loc C M pc Frs"
    by(clarsimp simp add: check_def)
  from sees \<open>\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []\<close> exec obtain M' n where [simp]: "ins ! pc = Invoke M' n"
    by(cases "ins ! pc", auto split: if_split_asm simp add: split_beta ta_upd_simps)
  from \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close> obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
  
  from checkins have "n < length stk" "is_Ref (stk ! n)" by auto
  moreover from exec sees \<open>\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []\<close> have "stk ! n \<noteq> Null" by auto
  with \<open>is_Ref (stk ! n)\<close> obtain a where "stk ! n = Addr a"
    by(auto simp add: is_Ref_def elim: is_AddrE)
  moreover with checkins obtain Ta where Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>" by(fastforce)
  moreover with checkins exec sees \<open>n < length stk\<close> \<open>\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []\<close> \<open>stk ! n = Addr a\<close>
  obtain Us Us' U D' where "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
    and "P \<turnstile> class_type_of Ta sees M':Us'\<rightarrow>U = Native in D'" and "D'\<bullet>M'(Us') :: U"
    and "P \<turnstile> Us [\<le>] Us'"
    by(auto simp add: confs_conv_map min_def split_beta has_method_def external_WT'_iff split: if_split_asm)
  moreover with \<open>typeof_addr h a = \<lfloor>Ta\<rfloor>\<close> \<open>n < length stk\<close> exec sees \<open>stk ! n = Addr a\<close>
  obtain ta' va h' where "ta = extTA2JVM P ta'" "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    "(ta', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
    by(fastforce simp add: min_def)
  ultimately show thesis using exec sees 
    by-(rule that, auto intro!: is_native.intros)
qed

end

context JVM_conf_read begin

lemma correct_state_new_thread:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and cs: "\<Phi> \<turnstile> t: \<sigma> \<surd>"
  and nt: "NewThread t'' (xcp, frs) h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<Phi> \<turnstile> t'': (xcp, h'', frs) \<surd>"
proof -
  from wf obtain wt where wfp: "wf_prog wt P" by(blast dest: wt_jvm_progD)
  from nt have "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<noteq> []" by auto
  with wf red cs
  obtain h Frs a stk loc C M pc Ts T mxs mxl0 ins xt M' n Ta ta' va h' Us Us' U D'
    where [simp]: "\<sigma> = (None, h, (stk, loc, C, M, pc) # Frs)"
    and exec: "(ta, \<sigma>') \<in> exec P t (None, h, (stk, loc, C, M, pc) # Frs)"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl0, ins, xt)\<rfloor> in C"
    and [simp]: "stk ! n = Addr a"
    and [simp]: "ins ! pc = Invoke M' n"
    and n: "n < length stk"
    and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
    and iec: "is_native P Ta M'"
    and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc Frs va"
    and rel: "(ta', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
    and Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Us"
    and wtext: "P \<turnstile> class_type_of Ta sees M':Us'\<rightarrow>U = Native in D'" "D'\<bullet>M'(Us') :: U"
    and sub: "P \<turnstile> Us [\<le>] Us'"
    by(rule exec_new_threadE)
  from cs have hconf: "hconf h" and preh: "preallocated h"
    and tconf: "P,h \<turnstile> t \<surd>t" by(auto simp add: correct_state_def)
  from Ta Us wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U"
    by(auto intro!: external_WT'.intros)
  from rel have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
    by(unfold WT_red_external_list_conv[OF wfp wtext' tconf])
  from ta nt obtain D M'' a' where nt': "NewThread t'' (D, M'', a') h'' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>"
    "(xcp, frs) = extNTA2JVM P (D, M'', a')" by auto
  with red have [simp]: "h'' = h'" by-(rule red_ext_new_thread_heap)
  from red_external_new_thread_sub_thread[OF red nt'(1)]
  have h't'': "typeof_addr h' a' = \<lfloor>Class_type D\<rfloor>" "P \<turnstile> D \<preceq>\<^sup>* Thread" and [simp]: "M'' = run" by auto
  from red_external_new_thread_exists_thread_object[OF red nt'(1)] 
  have tconf': "P,h' \<turnstile> t'' \<surd>t" by(auto intro: tconfI)
  from sub_Thread_sees_run[OF wfp \<open>P \<turnstile> D \<preceq>\<^sup>* Thread\<close>] obtain mxs' mxl0' ins' xt' D'
    where seesrun: "P \<turnstile> D sees run: []\<rightarrow>Void = \<lfloor>(mxs', mxl0', ins', xt')\<rfloor> in D'" by auto
  with nt' ta nt have "xcp = None" "frs = [([],Addr a' # replicate mxl0' undefined_value,D',run,0)]"
    by(auto simp add: extNTA2JVM_def split_beta)
  moreover
  have "\<Phi> \<turnstile> t'': (None, h', [([], Addr a' # replicate mxl0' undefined_value, D', run, 0)]) \<surd>"
  proof -
    from red wtext' \<open>hconf h\<close> have "hconf h'" 
      by(rule external_call_hconf)
    moreover from red have "h \<unlhd> h'" by(rule red_external_hext)
    with preh have "preallocated h'" by(rule preallocated_hext)
    moreover from seesrun
    have seesrun': "P \<turnstile> D' sees run: []\<rightarrow>Void = \<lfloor>(mxs', mxl0', ins', xt')\<rfloor> in D'"
      by(rule sees_method_idemp)
    moreover with \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>
    obtain "wt_start P D' [] mxl0' (\<Phi> D' run)" "ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)    
    then obtain LT' where "\<Phi> D' run ! 0 = Some ([], LT')"
      by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
    moreover
    have "conf_f P h' ([], LT') ins' ([], Addr a' # replicate mxl0' undefined_value, D', run, 0)"
    proof -
      let ?LT = "OK (Class D') # (replicate mxl0' Err)"
      from seesrun have "P \<turnstile> D \<preceq>\<^sup>* D'" by(rule sees_method_decl_above)
      hence "P,h' \<turnstile> Addr a' # replicate mxl0' undefined_value [:\<le>\<^sub>\<top>] ?LT"
        using h't'' by(simp add: conf_def)
      also from \<open>wt_start P D' [] mxl0' (\<Phi> D' run)\<close> \<open>\<Phi> D' run ! 0 = Some ([], LT')\<close>
      have "P \<turnstile> ?LT [\<le>\<^sub>\<top>] LT'" by(simp add: wt_start_def)
      finally have "P,h' \<turnstile> Addr a' # replicate mxl0' undefined_value [:\<le>\<^sub>\<top>] LT'" .
      with \<open>ins' \<noteq> []\<close> show ?thesis by(simp add: conf_f_def)
    qed
    ultimately show ?thesis using tconf' by(fastforce simp add: correct_state_def)
  qed
  ultimately show ?thesis by(clarsimp)
qed

lemma correct_state_heap_change:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and red: "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
  and cs'': "\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>"
  shows "\<Phi> \<turnstile> t'': (xcp'', h', frs'') \<surd>"
proof(cases xcp)
  case None
  from cs have "P,h \<turnstile> t \<surd>t" by(simp add: correct_state_def)
  with red have "hext h h'" by (auto intro: exec_1_d_hext simp add: tconf_def)
  from \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close> cs red have "\<Phi> \<turnstile> t: (xcp', h', frs') \<surd>"
    by(auto elim!: jvmd_NormalE intro: BV_correct_1 simp add: exec_1_iff)
  from cs'' have "P,h \<turnstile> t'' \<surd>t" by(simp add: correct_state_def)
  with \<open>h \<unlhd> h'\<close> have tconf': "P,h' \<turnstile> t'' \<surd>t" by-(rule tconf_hext_mono)

  from \<open>\<Phi> \<turnstile> t: (xcp', h', frs') \<surd>\<close>
  have hconf': "hconf h'" "preallocated h'" by(simp_all add: correct_state_def)

  show ?thesis
  proof(cases frs'')
    case Nil thus ?thesis using tconf' hconf' by(simp add: correct_state_def)
  next
    case (Cons f'' Frs'')
    obtain stk'' loc'' C0'' M0'' pc''
      where "f'' = (stk'', loc'', C0'', M0'', pc'')"
      by(cases f'', blast)
    with \<open>frs'' = f'' # Frs''\<close> cs''
    obtain Ts'' T'' mxs'' mxl\<^sub>0'' ins'' xt'' ST'' LT'' 
      where "hconf h"
      and sees'': "P \<turnstile> C0'' sees M0'': Ts''\<rightarrow>T'' = \<lfloor>(mxs'', mxl\<^sub>0'', ins'', xt'')\<rfloor> in C0''"
      and "\<Phi> C0'' M0'' ! pc'' = \<lfloor>(ST'', LT'')\<rfloor>"
      and "conf_f P h (ST'', LT'') ins'' (stk'', loc'', C0'', M0'', pc'')"
      and "conf_fs P h \<Phi> M0'' (length Ts'') T'' Frs''"
      by(fastforce simp add: correct_state_def)
    
    show ?thesis using Cons \<open>\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>\<close> \<open>hext h h'\<close> hconf' tconf'
      apply(cases xcp'')
      apply(auto simp add: correct_state_def)
      apply(blast dest: hext_objD intro: conf_fs_hext conf_f_hext)+
      done
  qed
next
  case (Some a)
  with \<open>P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')\<close>
  have "h = h'" by(auto elim!: jvmd_NormalE)
  with \<open>\<Phi> \<turnstile> t'': (xcp'', h, frs'') \<surd>\<close> show ?thesis by simp
qed

lemma lifting_wf_correct_state_d:
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P \<Longrightarrow> lifting_wf JVM_final (mexecd P) (\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>)"
by(unfold_locales)(auto intro: BV_correct_d_1 correct_state_new_thread correct_state_heap_change)

lemma lifting_wf_correct_state:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "lifting_wf JVM_final (mexec P) (\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>)"
proof(unfold_locales)
  fix t x m ta x' m'
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x' m'"
    by(cases x)(cases x', simp add: welltyped_commute[symmetric, OF \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>], rule BV_correct_d_1)
next
  fix t x m ta x' m' t'' x''
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
    and "NewThread t'' x'' m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m'"
    apply(cases x, cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>])
    by(rule correct_state_new_thread)
next
  fix t x m ta x' m' t'' x''
  assume "mexec P t (x, m) ta (x', m')"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>) x m"
    and "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m"
  with wf show "(\<lambda>(xcp, frs) h. \<Phi> \<turnstile> t'': (xcp, h, frs) \<surd>) x'' m'"
    by(cases x)(cases x', cases x'', clarify, unfold welltyped_commute[symmetric, OF \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>], rule correct_state_heap_change)
qed

lemmas preserves_correct_state = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state]
lemmas preserves_correct_state_d = FWLiftingSem.lifting_wf.RedT_preserves[OF lifting_wf_correct_state_d]

end

context JVM_heap_conf_base begin

definition correct_jvm_state :: "ty\<^sub>P \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state set"
where
  "correct_jvm_state \<Phi>
  = {s. correct_state_ts \<Phi> (thr s) (shr s) \<and> lock_thread_ok (locks s) (thr s)}"

end

context JVM_heap_conf begin

lemma correct_jvm_state_initial:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and wf_start: "wf_start_state P C M vs"
  shows "JVM_start_state P C M vs \<in> correct_jvm_state \<Phi>"
proof -
  from wf_start obtain Ts T m D 
    where "start_heap_ok" and "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in D"
    and "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases
  with wf BV_correct_initial[OF wf this] show ?thesis
    by(cases m)(auto simp add: correct_jvm_state_def start_state_def JVM_start_state'_def intro: lock_thread_okI ts_okI split: if_split_asm)
qed

end

context JVM_conf_read begin

lemma invariant3p_correct_jvm_state_mexecdT:
  assumes wf:  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "invariant3p (mexecdT P) (correct_jvm_state \<Phi>)"
unfolding correct_jvm_state_def
apply(rule invariant3pI)
apply safe
 apply(erule (1) lifting_wf.redT_preserves[OF lifting_wf_correct_state_d[OF wf]])
apply(erule (1) execd_mthr.redT_preserves_lock_thread_ok)
done

lemma invariant3p_correct_jvm_state_mexecT:
  assumes wf:  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "invariant3p (mexecT P) (correct_jvm_state \<Phi>)"
unfolding correct_jvm_state_def
apply(rule invariant3pI)
apply safe
 apply(erule (1) lifting_wf.redT_preserves[OF lifting_wf_correct_state[OF wf]])
apply(erule (1) exec_mthr.redT_preserves_lock_thread_ok)
done

lemma correct_jvm_state_preserved:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "s \<in> correct_jvm_state \<Phi>"
  and red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  shows "s' \<in> correct_jvm_state \<Phi>"
using wf red correct unfolding exec_mthr.RedT_def
by(rule invariant3p_rtrancl3p[OF invariant3p_correct_jvm_state_mexecT])

theorem jvm_typesafe:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and start: "wf_start_state P C M vs"
  and exec: "P \<turnstile> JVM_start_state P C M vs -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  shows "s' \<in> correct_jvm_state \<Phi>"
by(rule correct_jvm_state_preserved[OF wf _ exec])(rule correct_jvm_state_initial[OF wf start])

end


declare (in JVM_typesafe) split_paired_Ex [simp del]

context JVM_heap_conf_base' begin 

lemma execd_NewThread_Thread_Object:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and conf: "\<Phi> \<turnstile> t': \<sigma> \<surd>"
  and red: "P,t' \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  and nt: "NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "\<exists>C. typeof_addr (fst (snd \<sigma>')) (thread_id2addr t) = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> Class C \<le> Class Thread"
proof -
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(blast dest: wt_jvm_progD)
  from red obtain h f Frs xcp
    where check: "check P \<sigma>" 
    and exec: "(ta, \<sigma>') \<in> exec P t' \<sigma>" 
    and [simp]: "\<sigma> = (xcp, h, f # Frs)"
    by(rule jvmd_NormalE)
  obtain xcp' h' frs' where [simp]: "\<sigma>' = (xcp', h', frs')" by(cases \<sigma>', auto)
  obtain stk loc C M pc where [simp]: "f = (stk, loc, C, M, pc)" by(cases f, blast)
  from exec nt have [simp]: "xcp = None" by(cases xcp, auto)
  from \<open>\<Phi> \<turnstile> t': \<sigma> \<surd>\<close> obtain Ts T mxs mxl0 ins xt ST LT 
    where "hconf h"
    and "P,h \<turnstile> t' \<surd>t"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl0, ins, xt)\<rfloor> in C"
    and "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and "conf_fs P h \<Phi> M (length Ts) T Frs"
    by(fastforce simp add: correct_state_def)
  from wf red conf nt
  obtain h frs a stk loc C M pc M' n ta' va h'
    where ha: "typeof_addr h a \<noteq> None" and ta: "ta = extTA2JVM P ta'"
    and \<sigma>': "\<sigma>' = extRet2JVM n h' stk loc C M pc frs va"
    and rel: "(ta', va, h') \<in> red_external_aggr P t' a M' (rev (take n stk)) h"
    by -(erule (2) exec_new_threadE, fastforce+)
  from nt ta obtain x' where "NewThread t x' m \<in> set \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub>" by auto
  from red_external_aggr_new_thread_exists_thread_object[OF rel ha this] \<sigma>'
  show ?thesis by(cases va) auto
qed

lemma mexecdT_NewThread_Thread_Object:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; correct_state_ts \<Phi> (thr s) (shr s); P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'; NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>C. typeof_addr (shr s') (thread_id2addr t) = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
apply(frule correct_state_ts_thread_conf)
apply(erule execd_mthr.redT.cases)
 apply(hypsubst)
 apply(frule (2) execd_tconf.redT_updTs_preserves[where ln'="redT_updLns (locks s) t' no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"])
  apply clarsimp
 apply(clarsimp)
 apply(drule execd_NewThread_Thread_Object)
    apply(drule (1) ts_okD)
    apply(fastforce)
   apply(assumption)
  apply(fastforce)
 apply(clarsimp)
apply(simp)
done

end

context JVM_heap begin

lemma exec_ta_satisfiable:
  assumes "P,t \<turnstile> s -ta-jvm\<rightarrow> s'"
  shows "\<exists>s. exec_mthr.actions_ok s t ta"
proof -
  obtain xcp h frs where [simp]: "s = (xcp, h, frs)" by(cases s)
  from assms obtain stk loc C M pc frs' where [simp]: "frs = (stk, loc, C, M, pc) # frs'"
    by(cases frs)(auto simp add: exec_1_iff)
  show ?thesis
  proof(cases xcp)
    case Some with assms show ?thesis by(auto simp add: exec_1_iff lock_ok_las_def finfun_upd_apply split_paired_Ex)
  next
    case None
    with assms show ?thesis
      apply(cases "instrs_of P C M ! pc")
      apply(auto simp add: exec_1_iff lock_ok_las_def finfun_upd_apply split_beta final_thread.actions_ok_iff split: if_split_asm dest: red_external_aggr_ta_satisfiable[where final=JVM_final])
      apply(fastforce simp add: final_thread.actions_ok_iff lock_ok_las_def dest: red_external_aggr_ta_satisfiable[where final=JVM_final])
      apply(fastforce simp add: finfun_upd_apply intro: exI[where x="K$ None"] exI[where x="K$ \<lfloor>(t, 0)\<rfloor>"] may_lock.intros)+
      done
  qed
qed

end

context JVM_typesafe begin

lemma execd_wf_progress:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "progress JVM_final (mexecd P) (execd_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>))"
  (is "progress _ _ ?wf_state")
proof
  {
    fix s t x ta x' m' w
    assume mexecd: "mexecd P t (x, shr s) ta (x', m')"
      and Suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    from mexecd_Suspend_Invoke[OF mexecd Suspend]
    show "\<not> JVM_final x'" by auto
  }
  note Suspend_final = this
  {
    fix s
    assume s: "s \<in> ?wf_state"
    hence "lock_thread_ok (locks s) (thr s)"
      by(auto dest: execd_mthr.wset_Suspend_okD1 simp add: correct_jvm_state_def)
    moreover
    have "exec_mthr.wset_final_ok (wset s) (thr s)"
    proof(rule exec_mthr.wset_final_okI)
      fix t w
      assume "wset s t = \<lfloor>w\<rfloor>"
      from execd_mthr.wset_Suspend_okD2[OF s this]
      obtain x0 ta x m1 w' ln'' and s0 :: "('addr, 'thread_id, 'addr option \<times> 'addr frame list, 'heap, 'addr) state"
        where mexecd: "mexecd P t (x0, shr s0) ta (x, m1)"
        and Suspend: "Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" 
        and tst: "thr s t = \<lfloor>(x, ln'')\<rfloor>" by blast
      from Suspend_final[OF mexecd Suspend] tst
      show " \<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> \<not> JVM_final x" by blast
    qed
    ultimately show "lock_thread_ok (locks s) (thr s) \<and> exec_mthr.wset_final_ok (wset s) (thr s)" ..
  }
next
  fix s t x ta x' m'
  assume wfs: "s \<in> ?wf_state"
    and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "mexecd P t (x, shr s) ta (x', m')"
    and wait: "\<not> waiting (wset s t)"
  moreover obtain ls ts h ws "is" where s [simp]: "s = (ls, (ts, h), ws, is)" by(cases s) fastforce
  ultimately have "ts t = \<lfloor>(x, no_wait_locks)\<rfloor>" "mexecd P t (x, h) ta (x', m')" by auto
  from wfs have "correct_state_ts \<Phi> ts h" by(auto dest: execd_mthr.wset_Suspend_okD1 simp add: correct_jvm_state_def)
  from wf obtain wfmd where wfp: "wf_prog wfmd P" by(auto dest: wt_jvm_progD)
    
  from \<open>ts t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>mexecd P t (x, h) ta (x', m')\<close>
  obtain xcp frs xcp' frs'
    where "P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')"
    and [simp]: "x = (xcp, frs)" "x' = (xcp', frs')"
    by(cases x, auto)
  then obtain f Frs
    where check: "check P (xcp, h, f # Frs)"
    and [simp]: "frs = f # Frs"
    and exec: "(ta, xcp', m', frs') \<in> exec P t (xcp, h, f # Frs)"
    by(auto elim: jvmd_NormalE)
  with \<open>ts t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>correct_state_ts \<Phi> ts h\<close>
  have correct: "\<Phi> \<turnstile> t: (xcp, h, f # Frs) \<surd>" by(auto dest: ts_okD)
  obtain stk loc C M pc where f [simp]: "f = (stk, loc, C, M, pc)" by (cases f)
  from correct obtain Ts T mxs mxl0 ins xt ST LT
    where hconf: "hconf h"
    and tconf: "P, h \<turnstile> t \<surd>t"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(mxs, mxl0, ins, xt)\<rfloor> in C"
    and wt: "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and conf_f: "conf_f P h (ST, LT) ins (stk, loc, C, M, pc)"
    and confs: "conf_fs P h \<Phi> M (length Ts) T Frs"
    and confxcp: "conf_xcp P h xcp (ins ! pc)"
    and preh: "preallocated h"
    by(fastforce simp add: correct_state_def)
  
  have "\<exists>ta' \<sigma>'. P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -ta'-jvmd\<rightarrow> Normal \<sigma>' \<and>
                 (final_thread.actions_ok JVM_final (ls, (ts, h), ws, is) t ta' \<or>
                  final_thread.actions_ok' (ls, (ts, h), ws, is) t ta' \<and> final_thread.actions_subset ta' ta)"
  proof(cases "final_thread.actions_ok' (ls, (ts, h), ws, is) t ta")
    case True
    have "final_thread.actions_subset ta ta" ..
    with True \<open>P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', m', frs')\<close>
    show ?thesis by auto
  next
    case False
    note naok = this
    have ws: "wset s t = None \<or> 
              (\<exists>n a T w. ins ! pc = Invoke wait n \<and> stk ! n = Addr a \<and> typeof_addr h a = \<lfloor>T\<rfloor> \<and> is_native P T wait \<and> wset s t = \<lfloor>PostWS w\<rfloor> \<and> xcp = None)"
    proof(cases "wset s t")
      case None thus ?thesis ..
    next
      case (Some w)
      from execd_mthr.wset_Suspend_okD2[OF wfs this] \<open>ts t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
      obtain xcp0 frs0 h0 ta0 w' s1 tta1
        where red0: "mexecd P t ((xcp0, frs0), h0) ta0 ((xcp, frs), shr s1)"
        and Suspend: "Suspend w' \<in> set \<lbrace>ta0\<rbrace>\<^bsub>w\<^esub>"
        and s1: "P \<turnstile> s1 -\<triangleright>tta1\<rightarrow>\<^bsub>jvmd\<^esub>* s"
        by auto
      from mexecd_Suspend_Invoke[OF red0 Suspend] sees
      obtain n a T where [simp]: "ins ! pc = Invoke wait n" "xcp = None" "stk ! n = Addr a"
        and type: "typeof_addr h0 a = \<lfloor>T\<rfloor>"
        and iec: "is_native P T wait"
        by(auto simp add: is_native.simps) blast
      
      from red0 have "h0 \<unlhd> shr s1" by(auto dest: exec_1_d_hext)
      also from s1 have "shr s1 \<unlhd> shr s" by(rule Execd_hext)
      finally have "typeof_addr (shr s) a = \<lfloor>T\<rfloor>" using type
        by(rule typeof_addr_hext_mono)
      moreover from Some wait s obtain w' where "ws t = \<lfloor>PostWS w'\<rfloor>"
        by(auto simp add: not_waiting_iff)
      ultimately show ?thesis using iec s by auto
    qed

    from ws naok exec sees
    show ?thesis
    proof(cases "ins ! pc")
      case (Invoke M' n)
      from ws Invoke check exec sees naok obtain a Ts U Ta Us D D'
        where a: "stk ! n = Addr a"
        and n: "n < length stk"
        and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
        and wtext: "P \<turnstile> class_type_of Ta sees M':Us\<rightarrow>U = Native in D'" "D'\<bullet>M'(Us)::U"
        and sub: "P \<turnstile> Ts [\<le>] Us"
        and Ts: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some Ts"
        and [simp]: "xcp = None"
        apply(cases xcp)
        apply(simp add: is_Ref_def has_method_def external_WT'_iff check_def lock_ok_las'_def confs_conv_map split_beta split: if_split_asm option.splits)
        apply(auto simp add: lock_ok_las'_def)[2]
        apply(fastforce simp add: is_native.simps lock_ok_las'_def dest: sees_method_fun)+
        done
      from exec Ta n a sees Invoke wtext obtain ta' va m''
        where exec': "(ta', va, m'') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
        and ta: "ta = extTA2JVM P ta'"
        and va: "(xcp', m', frs') = extRet2JVM n m'' stk loc C M pc Frs va"
        by(auto)
      from va have [simp]: "m'' = m'" by(cases va) simp_all
      from Ta Ts wtext sub have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : U"
        by(auto intro!: external_WT'.intros simp add: is_native.simps)
      with wfp exec' tconf have red: "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)), h\<rangle> -ta'\<rightarrow>ext \<langle>va, m'\<rangle>"
        by(simp add: WT_red_external_list_conv)
      from ws Invoke have "wset s t = None \<or> M' = wait \<and> (\<exists>w. wset s t = \<lfloor>PostWS w\<rfloor>)" by auto
      with wfp red tconf hconf obtain ta'' va' h''
        where red': "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h''\<rangle>"
        and ok': "final_thread.actions_ok JVM_final s t ta'' \<or> final_thread.actions_ok' s t ta'' \<and> final_thread.actions_subset ta'' ta'"
        by(rule red_external_wf_red)
      from red' a n Ta Invoke sees wtext
      have "(extTA2JVM P ta'', extRet2JVM n h'' stk loc C M pc Frs va') \<in> exec P t (xcp, h, f # Frs)" 
        by(auto intro: red_external_imp_red_external_aggr)
      with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -extTA2JVM P ta''-jvmd\<rightarrow> Normal (extRet2JVM n h'' stk loc C M pc Frs va')"
        by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
      moreover from ok' ta
      have "final_thread.actions_ok JVM_final (ls, (ts, h), ws, is) t (extTA2JVM P ta'') \<or>
        final_thread.actions_ok' (ls, (ts, h), ws, is) t (extTA2JVM P ta'') \<and> final_thread.actions_subset (extTA2JVM P ta'') ta"
        by(auto simp add: final_thread.actions_ok'_convert_extTA elim: final_thread.actions_subset.cases del: subsetI)
      ultimately show ?thesis by blast
    next
      case MEnter
      with exec sees naok ws have False
        by(cases xcp)(auto split: if_split_asm simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
      thus ?thesis ..
    next
      case MExit
      with exec sees False check ws obtain a where [simp]: "hd stk = Addr a" "xcp = None" "ws t = None"
        and ta: "ta = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> \<or> ta = \<lbrace>UnlockFail\<rightarrow>a\<rbrace>"
        by(cases xcp)(fastforce split: if_split_asm simp add: lock_ok_las'_def finfun_upd_apply is_Ref_def check_def)+
      from ta show ?thesis
      proof(rule disjE)
        assume ta: "ta = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>"
        let ?ta' = "\<lbrace>UnlockFail\<rightarrow>a\<rbrace>"
        from ta exec sees MExit obtain \<sigma>'
          where "(?ta', \<sigma>') \<in> exec P t (xcp, h, f # Frs)" by auto
        with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
          by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
        moreover from False ta have "has_locks (ls $ a) t = 0"
          by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
        hence "final_thread.actions_ok' (ls, (ts, h), ws, is) t ?ta'"
          by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
          by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply ta_upd_simps)
        ultimately show ?thesis by(fastforce simp add: ta_upd_simps)
      next
        assume ta: "ta = \<lbrace>UnlockFail\<rightarrow>a\<rbrace>"
        let ?ta' = "\<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>"
        from ta exec sees MExit obtain \<sigma>'
          where "(?ta', \<sigma>') \<in> exec P t (xcp, h, f # Frs)" by auto
        with check have "P,t \<turnstile> Normal (xcp, h, (stk, loc, C, M, pc) # Frs) -?ta'-jvmd\<rightarrow> Normal \<sigma>'"
          by -(rule exec_1_d.exec_1_d_NormalI, auto simp add: exec_d_def)
        moreover from False ta have "has_lock (ls $ a) t"
          by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
        hence "final_thread.actions_ok' (ls, (ts, h), ws, is) t ?ta'"
          by(auto simp add: lock_ok_las'_def finfun_upd_apply ta_upd_simps)
        moreover from ta have "final_thread.actions_subset ?ta' ta"
          by(auto simp add: final_thread.actions_subset_iff collect_locks'_def finfun_upd_apply ta_upd_simps)
        ultimately show ?thesis by(fastforce simp add: ta_upd_simps)
      qed
    qed(case_tac [!] xcp, auto simp add: split_beta lock_ok_las'_def split: if_split_asm)
  qed
  thus "\<exists>ta' x' m'. mexecd P t (x, shr s) ta' (x', m') \<and> 
                   (final_thread.actions_ok JVM_final s t ta' \<or>
                    final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta)"
    by fastforce
next
  fix s t x
  assume wfs: "s \<in> ?wf_state"
    and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and "\<not> JVM_final x"
  from wfs have correct: "correct_state_ts \<Phi> (thr s) (shr s)"
    by(auto dest: execd_mthr.wset_Suspend_okD1 simp add: correct_jvm_state_def)
  obtain xcp frs where x: "x = (xcp, frs)" by (cases x, auto)
  with \<open>\<not> JVM_final x\<close> obtain f Frs where "frs = f # Frs"
    by(fastforce simp add: neq_Nil_conv)
  with tst correct x have "\<Phi> \<turnstile> t: (xcp, shr s, f # Frs) \<surd>" by(auto dest: ts_okD)
  with \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close>
  have "exec_d P t (xcp, shr s, f # Frs) \<noteq> TypeError" by(auto dest: no_type_error)
  then obtain \<Sigma> where "exec_d P t (xcp, shr s, f # Frs) = Normal \<Sigma>" by(auto)
  hence "exec P t (xcp, shr s, f # Frs) = \<Sigma>"
    by(auto simp add: exec_d_def check_def split: if_split_asm)
  with progress[OF wf \<open>\<Phi> \<turnstile> t: (xcp, shr s, f # Frs) \<surd>\<close>]
  obtain ta \<sigma> where "(ta, \<sigma>) \<in> \<Sigma>" unfolding exec_1_iff by blast
  with \<open>x = (xcp, frs)\<close> \<open>frs = f # Frs\<close> \<open>\<Phi> \<turnstile> t: (xcp, shr s, f # Frs) \<surd>\<close>
    \<open>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P\<close> \<open>exec_d P t (xcp, shr s, f # Frs) = Normal \<Sigma>\<close>
  show "\<exists>ta x' m'. mexecd P t (x, shr s) ta (x', m')"
    by(cases ta, cases \<sigma>)(fastforce simp add: split_paired_Ex intro: exec_1_d_NormalI)
qed(fastforce dest: defensive_imp_aggressive_1 mexec_instr_Wakeup_no_Join exec_ta_satisfiable)+

end

context JVM_conf_read begin

lemma mexecT_eq_mexecdT:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and cs: "correct_state_ts \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s' = P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
proof(rule iffI)
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  proof(cases rule: exec_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x' m')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> cs
    have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf \<open>\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>\<close>] \<open>mexec P t (x, shr s) ta (x', m')\<close>
    have *: "mexecd P t (x, shr s) ta (x', m')" by simp
    with lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] cs, OF this \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>] \<open>thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<close>
    have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) m'" by simp
    with * show ?thesis using normal 
      by(cases s')(erule execd_mthr.redT_normal, auto)
  next
    case acquire thus ?thesis
      apply(cases s', clarify)
      apply(rule execd_mthr.redT_acquire, assumption+)
      by(auto)
  qed
next
  assume "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
  thus "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'"
  proof(cases rule: execd_mthr.redT_elims[consumes 1, case_names normal acquire])
    case (normal x x' m')
    obtain xcp frs where x [simp]: "x = (xcp, frs)" by(cases x, auto)
    from \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> cs
    have "\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>" by(auto dest: ts_okD)
    from mexec_eq_mexecd[OF wf \<open>\<Phi> \<turnstile> t: (xcp, shr s, frs) \<surd>\<close>] \<open>mexecd P t (x, shr s) ta (x', m')\<close>
    have "mexec P t (x, shr s) ta (x', m')" by simp
    moreover from lifting_wf.redT_updTs_preserves[OF lifting_wf_correct_state_d[OF wf] cs, OF \<open>mexecd P t (x, shr s) ta (x', m')\<close> \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>] \<open>thread_oks (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>\<close>
    have "correct_state_ts \<Phi> (redT_updTs (thr s) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x', redT_updLns (locks s) t no_wait_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))) m'" by simp
    ultimately show ?thesis using normal
      by(cases s')(erule exec_mthr.redT_normal, auto)
  next
    case acquire thus ?thesis
      apply(cases s', clarify)
      apply(rule exec_mthr.redT_acquire, assumption+)
      by(auto)
  qed
qed

lemma mExecT_eq_mExecdT:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ct: "correct_state_ts \<Phi> (thr s) (shr s)"
  shows "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s' = P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
proof
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" using ct
  proof(induct rule: exec_mthr.RedT_induct[consumes 1, case_names refl step])
    case refl thus ?case by auto
  next
    case (step s ttas s' t ta s'')
    hence "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'" by blast
    moreover from \<open>correct_state_ts \<Phi> (thr s) (shr s)\<close> \<open>P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'\<close>
    have "correct_state_ts \<Phi> (thr s') (shr s')"
      by(auto dest: preserves_correct_state[OF wf])
    with \<open>P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''\<close> have "P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''"
      by(unfold mexecT_eq_mexecdT[OF wf])
    ultimately show ?case
      by(blast intro: execd_mthr.RedTI rtrancl3p_step elim: execd_mthr.RedTE)
  qed
next
  assume Red: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  thus "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" using ct
  proof(induct rule: execd_mthr.RedT_induct[consumes 1, case_names refl step])
    case refl thus ?case by auto
  next
    case (step s ttas s' t ta s'')
    hence "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'" by blast
    moreover from \<open>correct_state_ts \<Phi> (thr s) (shr s)\<close> \<open>P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'\<close>
    have "correct_state_ts \<Phi> (thr s') (shr s')"
      by(auto dest: preserves_correct_state_d[OF wf])
    with \<open>P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''\<close> have "P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''"
      by(unfold mexecT_eq_mexecdT[OF wf])
    ultimately show ?case
      by(blast intro: exec_mthr.RedTI rtrancl3p_step elim: exec_mthr.RedTE)
  qed
qed

lemma mexecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; correct_state_ts \<Phi> (thr s) (shr s);
    P \<turnstile> s -t'\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'; thread_conf P (thr s) (shr s) \<rbrakk> 
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mexecT_eq_mexecdT)(rule execd_tconf.redT_preserves)

lemma mExecT_preserves_thread_conf: 
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; correct_state_ts \<Phi> (thr s) (shr s);
    P \<turnstile> s -\<triangleright>tta\<rightarrow>\<^bsub>jvm\<^esub>* s'; thread_conf P (thr s) (shr s) \<rbrakk>
  \<Longrightarrow> thread_conf P (thr s') (shr s')"
by(simp only: mExecT_eq_mExecdT)(rule execd_tconf.RedT_preserves)

lemma wset_Suspend_ok_mexecd_mexec:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "exec_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>) = execd_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
apply(safe)
 apply(rule execd_mthr.wset_Suspend_okI)
  apply(erule exec_mthr.wset_Suspend_okD1)
 apply(drule (1) exec_mthr.wset_Suspend_okD2)
 apply(subst (asm) (2) split_paired_Ex)
 apply(elim bexE exE conjE)
 apply(subst (asm) mexec_eq_mexecd[OF wf])
  apply(simp add: correct_jvm_state_def)
  apply(blast dest: ts_okD)
 apply(subst (asm) mexecT_eq_mexecdT[OF wf])
  apply(simp add: correct_jvm_state_def)
 apply(subst (asm) mExecT_eq_mExecdT[OF wf])
  apply(simp add: correct_jvm_state_def)
 apply(rule bexI exI|erule conjI|assumption)+
apply(rule exec_mthr.wset_Suspend_okI)
 apply(erule execd_mthr.wset_Suspend_okD1)
apply(drule (1) execd_mthr.wset_Suspend_okD2)
apply(subst (asm) (2) split_paired_Ex)
apply(elim bexE exE conjE)
apply(subst (asm) mexec_eq_mexecd[OF wf, symmetric])
 apply(simp add: correct_jvm_state_def)
 apply(blast dest: ts_okD)
apply(subst (asm) mexecT_eq_mexecdT[OF wf, symmetric])
 apply(simp add: correct_jvm_state_def)
apply(subst (asm) mExecT_eq_mExecdT[OF wf, symmetric])
 apply(simp add: correct_jvm_state_def)
apply(rule bexI exI|erule conjI|assumption)+
done

end

context JVM_typesafe begin

lemma exec_wf_progress:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "progress JVM_final (mexec P) (exec_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>))"
  (is "progress _ _ ?wf_state")
proof -
  interpret progress: progress JVM_final "mexecd P" convert_RA ?wf_state
    using assms unfolding wset_Suspend_ok_mexecd_mexec[OF wf] by(rule execd_wf_progress)
  show ?thesis
  proof(unfold_locales)
    fix s
    assume "s \<in> ?wf_state"
    thus "lock_thread_ok (locks s) (thr s) \<and> exec_mthr.wset_final_ok (wset s) (thr s)"
      by(rule progress.wf_stateD)
  next
    fix s t x ta x' m'
    assume wfs: "s \<in> ?wf_state"
      and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and exec: "mexec P t (x, shr s) ta (x', m')"
      and wait: "\<not> waiting (wset s t)"
    from wfs tst have correct: "\<Phi> \<turnstile> t: (fst x, shr s, snd x) \<surd>"
      by(auto dest!: exec_mthr.wset_Suspend_okD1 ts_okD simp add: correct_jvm_state_def)
    with exec have "mexecd P t (x, shr s) ta (x', m')"
      by(cases x)(simp only: mexec_eq_mexecd[OF wf] fst_conv snd_conv)
    from progress.wf_red[OF wfs tst this wait] correct
    show "\<exists>ta' x' m'. mexec P t (x, shr s) ta' (x', m') \<and> 
                      (final_thread.actions_ok JVM_final s t ta' \<or>
                       final_thread.actions_ok' s t ta' \<and> final_thread.actions_subset ta' ta)"
      by(cases x)(simp only: fst_conv snd_conv mexec_eq_mexecd[OF wf])
  next
    fix s t x ta x' m' w
    assume wfs: "s \<in> ?wf_state"
      and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" 
      and exec: "mexec P t (x, shr s) ta (x', m')"
      and wait: "\<not> waiting (wset s t)"
      and Suspend: "Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    from wfs tst have correct: "\<Phi> \<turnstile> t: (fst x, shr s, snd x) \<surd>"
      by(auto dest!: exec_mthr.wset_Suspend_okD1 ts_okD simp add: correct_jvm_state_def)
    with exec have "mexecd P t (x, shr s) ta (x', m')"
      by(cases x)(simp only: mexec_eq_mexecd[OF wf] fst_conv snd_conv)
    with wfs tst show "\<not> JVM_final x'" using wait Suspend by(rule progress.red_wait_set_not_final)
  next
    fix s t x
    assume wfs: "s \<in> ?wf_state"
      and tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and "\<not> JVM_final x"
    from progress.wf_progress[OF this]
    show "\<exists>ta x' m'. mexec P t (x, shr s) ta (x', m')"
      by(auto dest: defensive_imp_aggressive_1 simp add: split_beta)
  qed(fastforce dest: mexec_instr_Wakeup_no_Join exec_ta_satisfiable)+
qed

theorem mexecd_TypeSafety:
  fixes ln :: "'addr \<Rightarrow>f nat"
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and s: "s \<in> execd_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
  and Exec: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')"
  and ts't: "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> t \<in> execd_mthr.deadlocked P s'"
  and "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
proof -
  interpret progress JVM_final "mexecd P" convert_RA "execd_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
    by(rule execd_wf_progress) fact+

  from Exec s have wfs': "s' \<in> execd_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
    unfolding execd_mthr.RedT_def
    by(blast intro: invariant3p_rtrancl3p execd_mthr.invariant3p_wset_Suspend_ok invariant3p_correct_jvm_state_mexecdT[OF wf])

  with ts't show cst: "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
    by(auto dest: ts_okD execd_mthr.wset_Suspend_okD1 simp add: correct_jvm_state_def)
  assume nfin: "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  from nfin \<open>thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>\<close> have "exec_mthr.not_final_thread s' t"
    by(auto simp: exec_mthr.not_final_thread_iff)
  from \<open>\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'')\<close>
  show "t \<in> execd_mthr.deadlocked P s'"
  proof(rule contrapos_np)
    assume "t \<notin> execd_mthr.deadlocked P s'"
    with \<open>exec_mthr.not_final_thread s' t\<close> have "\<not> execd_mthr.deadlocked' P s'"
      by(auto simp add: execd_mthr.deadlocked'_def)
    hence "\<not> execd_mthr.deadlock P s'" unfolding execd_mthr.deadlock_eq_deadlocked' .
    thus "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s''" by(rule redT_progress[OF wfs'])
  qed
qed

theorem mexec_TypeSafety:
  fixes ln :: "'addr \<Rightarrow>f nat"
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and s: "s \<in> exec_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
  and Exec: "P \<turnstile> s -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s'"
  and "\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')"
  and ts't: "thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>"
  shows "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks \<Longrightarrow> t \<in> multithreaded_base.deadlocked JVM_final (mexec P) s'"
  and "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
proof -
  interpret progress JVM_final "mexec P" convert_RA "exec_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
    by(rule exec_wf_progress) fact+

  from Exec s have wfs': "s' \<in> exec_mthr.wset_Suspend_ok P (correct_jvm_state \<Phi>)"
    unfolding exec_mthr.RedT_def
    by(blast intro: invariant3p_rtrancl3p exec_mthr.invariant3p_wset_Suspend_ok invariant3p_correct_jvm_state_mexecT[OF wf])

  with ts't show cst: "\<Phi> \<turnstile> t: (xcp, shr s', frs) \<surd>"
    by(auto dest: ts_okD exec_mthr.wset_Suspend_okD1 simp add: correct_jvm_state_def)

  assume nfin: "frs \<noteq> [] \<or> ln \<noteq> no_wait_locks"
  from nfin \<open>thr s' t = \<lfloor>((xcp, frs), ln)\<rfloor>\<close> have "exec_mthr.not_final_thread s' t"
    by(auto simp: exec_mthr.not_final_thread_iff)
  from \<open>\<not> (\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s'')\<close>
  show "t \<in> exec_mthr.deadlocked P s'"
  proof(rule contrapos_np)
    assume "t \<notin> exec_mthr.deadlocked P s'"
    with \<open>exec_mthr.not_final_thread s' t\<close> have "\<not> exec_mthr.deadlocked' P s'"
      by(auto simp add: exec_mthr.deadlocked'_def)
    hence "\<not> exec_mthr.deadlock P s'" unfolding exec_mthr.deadlock_eq_deadlocked' .
    thus "\<exists>t ta s''. P \<turnstile> s' -t\<triangleright>ta\<rightarrow>\<^bsub>jvm\<^esub> s''" by(rule redT_progress[OF wfs'])
  qed
qed

lemma start_mexec_mexecd_commute:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and start: "wf_start_state P C M vs"
  shows "P \<turnstile> JVM_start_state P C M vs -\<triangleright>ttas\<rightarrow>\<^bsub>jvmd\<^esub>* s \<longleftrightarrow> P \<turnstile> JVM_start_state P C M vs -\<triangleright>ttas\<rightarrow>\<^bsub>jvm\<^esub>* s"
using correct_jvm_state_initial[OF assms]
by(clarsimp simp add: correct_jvm_state_def)(rule mExecT_eq_mExecdT[symmetric, OF wf])

theorem mRtrancl_eq_mRtrancld:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ct: "correct_state_ts \<Phi> (thr s) (shr s)"
  shows "exec_mthr.mthr.Rtrancl3p P s ttas \<longleftrightarrow> execd_mthr.mthr.Rtrancl3p P s ttas" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?lhs if ?rhs using that ct
  proof(coinduction arbitrary: s ttas)
    case Rtrancl3p
    interpret lifting_wf "JVM_final" "mexecd P" convert_RA "\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
      using wf by(rule lifting_wf_correct_state_d)
    from Rtrancl3p(1) show ?case
    proof cases
      case stop: Rtrancl3p_stop
      then show ?thesis using mexecT_eq_mexecdT[OF wf Rtrancl3p(2)] by clarsimp
    next
      case (Rtrancl3p_into_Rtrancl3p s' ttas' tta)
      then show ?thesis using mexecT_eq_mexecdT[OF wf Rtrancl3p(2)] Rtrancl3p(2)
        by(cases tta; cases s')(fastforce simp add: split_paired_Ex dest: redT_preserves)
    qed
  qed
    
  show ?rhs if ?lhs using that ct
  proof(coinduction arbitrary: s ttas)
    case Rtrancl3p
    interpret lifting_wf "JVM_final" "mexec P" convert_RA "\<lambda>t (xcp, frs) h. \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>"
      using wf by(rule lifting_wf_correct_state)
    from Rtrancl3p(1) show ?case
    proof cases
      case stop: Rtrancl3p_stop
      then show ?thesis using mexecT_eq_mexecdT[OF wf Rtrancl3p(2)] by clarsimp
    next
      case (Rtrancl3p_into_Rtrancl3p s' ttas' tta)
      then show ?thesis using mexecT_eq_mexecdT[OF wf Rtrancl3p(2)] Rtrancl3p(2)
        by(cases tta; cases s')(fastforce simp add: split_paired_Ex dest: redT_preserves)
    qed
  qed
qed

lemma start_mRtrancl_mRtrancld_commute:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and start: "wf_start_state P C M vs"
  shows "exec_mthr.mthr.Rtrancl3p P (JVM_start_state P C M vs) ttas \<longleftrightarrow> execd_mthr.mthr.Rtrancl3p P (JVM_start_state P C M vs) ttas"
using correct_jvm_state_initial[OF assms] by(clarsimp simp add: correct_jvm_state_def mRtrancl_eq_mRtrancld[OF wf])
  
end

subsection \<open>Determinism\<close>

context JVM_heap_conf begin

lemma exec_instr_deterministic:
  assumes wf: "wf_prog wf_md P"
  and det: "deterministic_heap_ops"
  and exec1: "(ta', \<sigma>') \<in> exec_instr i P t (shr s) stk loc C M pc frs"
  and exec2: "(ta'', \<sigma>'') \<in> exec_instr i P t (shr s) stk loc C M pc frs"
  and check: "check_instr i P (shr s) stk loc C M pc frs"
  and aok1: "final_thread.actions_ok final s t ta'"
  and aok2: "final_thread.actions_ok final s t ta''"
  and tconf: "P,shr s \<turnstile> t \<surd>t"
  shows "ta' = ta'' \<and> \<sigma>' = \<sigma>''"
using exec1 exec2 aok1 aok2
proof(cases i)
  case (Invoke M' n)
  { fix T ta''' ta'''' va' va'' h' h''
    assume T: "typeof_addr (shr s) (the_Addr (stk ! n)) = \<lfloor>T\<rfloor>"
      and "method": "snd (snd (snd (method P (class_type_of T) M'))) = None" "P \<turnstile> class_type_of T has M'"
      and params: "P,shr s \<turnstile> rev (take n stk) [:\<le>] fst (snd (method P (class_type_of T) M'))"
      and red1: "(ta''', va', h') \<in> red_external_aggr P t (the_Addr (stk ! n)) M' (rev (take n stk)) (shr s)"
      and red2: "(ta'''', va'', h'') \<in> red_external_aggr P t (the_Addr (stk ! n)) M' (rev (take n stk)) (shr s)"
      and ta': "ta' = extTA2JVM P ta'''"
      and ta'': "ta'' = extTA2JVM P ta''''"
    from T "method" params obtain T' where "P,shr s \<turnstile> the_Addr (stk ! n)\<bullet>M'(rev (take n stk)) : T'"
      by(fastforce simp add: has_method_def confs_conv_map external_WT'_iff)
    hence "P,t \<turnstile> \<langle>the_Addr (stk ! n)\<bullet>M'(rev (take n stk)), shr s\<rangle> -ta'''\<rightarrow>ext \<langle>va', h'\<rangle>"
      and "P,t \<turnstile> \<langle>the_Addr (stk ! n)\<bullet>M'(rev (take n stk)), shr s\<rangle> -ta''''\<rightarrow>ext \<langle>va'', h''\<rangle>"
      using red1 red2 tconf
      by-(rule WT_red_external_aggr_imp_red_external[OF wf], assumption+)+
    moreover from aok1 aok2 ta' ta''
    have "final_thread.actions_ok final s t ta'''"
      and "final_thread.actions_ok final s t ta''''"
      by(auto simp add: final_thread.actions_ok_iff)
    ultimately have "ta''' = ta'''' \<and> va' = va'' \<and> h' = h''"
      by(rule red_external_deterministic[OF det]) }
  with assms Invoke show ?thesis
    by(clarsimp simp add: split_beta split: if_split_asm) blast
next
  case MExit
  { assume "final_thread.actions_ok final s t \<lbrace>UnlockFail\<rightarrow>the_Addr (hd stk)\<rbrace>"
    and "final_thread.actions_ok final s t \<lbrace>Unlock\<rightarrow>the_Addr (hd stk), SyncUnlock (the_Addr (hd stk))\<rbrace>"
    hence False 
      by(auto simp add: final_thread.actions_ok_iff lock_ok_las_def finfun_upd_apply elim!: allE[where x="the_Addr (hd stk)"]) }
  with assms MExit show ?thesis by(auto split: if_split_asm)
qed(auto simp add: split_beta split: if_split_asm dest: deterministic_heap_ops_readD[OF det] deterministic_heap_ops_writeD[OF det] deterministic_heap_ops_allocateD[OF det])

lemma exec_1_deterministic:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and det: "deterministic_heap_ops"
  and exec1: "P,t \<turnstile> (xcp, shr s, frs) -ta'-jvm\<rightarrow> \<sigma>'"
  and exec2: "P,t \<turnstile> (xcp, shr s, frs) -ta''-jvm\<rightarrow> \<sigma>''"
  and aok1: "final_thread.actions_ok final s t ta'"
  and aok2: "final_thread.actions_ok final s t ta''"
  and conf: "\<Phi> \<turnstile> t:(xcp, shr s, frs) \<surd>"
  shows "ta' = ta'' \<and> \<sigma>' = \<sigma>''"
proof -
  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  from conf have tconf: "P,shr s \<turnstile> t \<surd>t" by(simp add: correct_state_def)
  from exec1 conf have "P,t \<turnstile> Normal (xcp, shr s, frs) -ta'-jvmd\<rightarrow> Normal \<sigma>'"
    by(simp add: welltyped_commute[OF wf])
  hence "check P (xcp, shr s, frs)" by(rule jvmd_NormalE)
  with exec1 exec2 aok1 aok2 tconf show ?thesis
    by(cases xcp)(case_tac [!] frs, auto elim!: exec_1.cases dest: exec_instr_deterministic[OF wf' det] simp add: check_def split_beta)
qed

end

context JVM_conf_read begin

lemma invariant3p_correct_state_ts:
  assumes "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  shows "invariant3p (mexecT P) {s. correct_state_ts \<Phi> (thr s) (shr s)}"
using assms by(rule lifting_wf.invariant3p_ts_ok[OF lifting_wf_correct_state])

lemma mexec_deterministic:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and det: "deterministic_heap_ops"
  shows "exec_mthr.deterministic P {s. correct_state_ts \<Phi> (thr s) (shr s)}"
proof(rule exec_mthr.determisticI)
  fix s t x ta' x' m' ta'' x'' m''
  assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "mexec P t (x, shr s) ta' (x', m')" "mexec P t (x, shr s) ta'' (x'', m'')"
    and aok: "exec_mthr.actions_ok s t ta'" "exec_mthr.actions_ok s t ta''"
    and correct [simplified]: "s \<in> {s. correct_state_ts \<Phi> (thr s) (shr s)}"
  moreover obtain xcp frs where [simp]: "x = (xcp, frs)" by(cases x)
  moreover obtain xcp' frs' where [simp]: "x' = (xcp', frs')" by(cases x')
  moreover obtain xcp'' frs'' where [simp]: "x'' = (xcp'', frs'')" by(cases x'')
  ultimately have exec1: "P,t \<turnstile> (xcp, shr s, frs) -ta'-jvm\<rightarrow> (xcp', m', frs')"
    and exec1: "P,t \<turnstile> (xcp, shr s, frs) -ta''-jvm\<rightarrow> (xcp'', m'', frs'')"
    by simp_all
  moreover note aok
  moreover from correct tst have "\<Phi> \<turnstile> t:(xcp, shr s, frs)\<surd>"
    by(auto dest: ts_okD)
  ultimately have "ta' = ta'' \<and> (xcp', m', frs') = (xcp'', m'', frs'')"
    by(rule exec_1_deterministic[OF wf det])
  thus "ta' = ta'' \<and> x' = x'' \<and> m' = m''" by simp
qed(rule invariant3p_correct_state_ts[OF wf])

end

end
