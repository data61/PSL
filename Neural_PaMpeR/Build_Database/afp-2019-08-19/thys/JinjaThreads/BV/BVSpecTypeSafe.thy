(*  Title:      JinjaThreads/BV/BVSpecTypeSafe.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

section \<open>BV Type Safety Proof \label{sec:BVSpecTypeSafe}\<close>

theory BVSpecTypeSafe
imports
  BVConform
  "../Common/ExternalCallWF"
begin

declare listE_length [simp del]

text \<open>
  This theory contains proof that the specification of the bytecode
  verifier only admits type safe programs.  
\<close>

subsection \<open>Preliminaries\<close>

text \<open>
  Simp and intro setup for the type safety proof:
\<close>
context JVM_heap_conf_base begin

lemmas widen_rules [intro] = conf_widen confT_widen confs_widens confTs_widen

end
  
subsection \<open>Exception Handling\<close>


text \<open>
  For the \<open>Invoke\<close> instruction the BV has checked all handlers
  that guard the current \<open>pc\<close>.
\<close>
lemma Invoke_handlers:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set (relevant_entries P (Invoke n M) pc xt). 
   (case D of None \<Rightarrow> True | Some D' \<Rightarrow> P \<turnstile> C \<preceq>\<^sup>* D') \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
  by (induct xt) (auto simp add: relevant_entries_def matches_ex_entry_def 
                                 is_relevant_entry_def split: if_split_asm)

lemma match_is_relevant:
  assumes rv: "\<And>D'. P \<turnstile> D \<preceq>\<^sup>* D' \<Longrightarrow> is_relevant_class (ins ! i) P D'"
  assumes match: "match_ex_table P D pc xt = Some (pc',d')"
  shows "\<exists>(f,t,D',h,d) \<in> set (relevant_entries P (ins ! i) pc xt). (case D' of None \<Rightarrow> True | Some D'' \<Rightarrow> P \<turnstile> D \<preceq>\<^sup>* D'') \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
using rv match
by(fastforce simp add: relevant_entries_def is_relevant_entry_def matches_ex_entry_def dest: match_ex_table_SomeD)


context JVM_heap_conf_base begin

lemma exception_step_conform:
  fixes \<sigma>' :: "('addr, 'heap) jvm_state"
  assumes wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes correct: "\<Phi> \<turnstile> t:(\<lfloor>xcp\<rfloor>, h, fr # frs) \<surd>"
  shows "\<Phi> \<turnstile> t:exception_step P xcp h fr frs \<surd>"
proof -
  obtain stk loc C M pc where fr: "fr = (stk, loc, C, M, pc)" by(cases fr)
  from correct obtain Ts T mxs mxl\<^sub>0 ins xt 
    where meth: "P \<turnstile> C sees M:Ts \<rightarrow> T = \<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
    by (simp add: correct_state_def fr) blast

  from correct meth fr obtain D 
    where hxcp: "typeof_addr h xcp = \<lfloor>Class_type D\<rfloor>" and DsubThrowable: "P \<turnstile> D \<preceq>\<^sup>* Throwable"
    and rv: "\<And>D'. P \<turnstile> D \<preceq>\<^sup>* D' \<Longrightarrow> is_relevant_class (instrs_of P C M ! pc) P D'"
    by(fastforce simp add: correct_state_def dest: sees_method_fun)
  
  from meth have [simp]: "ex_table_of P C M = xt" by simp

  from correct have tconf: "P,h \<turnstile> t \<surd>t" by(simp add: correct_state_def)

  show ?thesis
  proof(cases "match_ex_table P D pc xt")
    case None
    with correct fr meth hxcp show ?thesis
      by(fastforce simp add: correct_state_def cname_of_def split: list.split)
  next
    case (Some pc_d)
    then obtain pc' d' where pcd: "pc_d = (pc', d')"
      and match: "match_ex_table P D pc xt = Some (pc',d')" by (cases pc_d) auto
    from match_is_relevant[OF rv match] meth obtain f t D'
      where rv: "(f, t, D', pc', d') \<in> set (relevant_entries P (ins ! pc) pc xt)"
      and DsubD': "(case D' of None \<Rightarrow> True | Some D'' \<Rightarrow> P \<turnstile> D \<preceq>\<^sup>* D'')" and pc: "pc \<in> {f..<t}" by(auto)

    from correct meth obtain ST LT
      where h_ok:  "hconf h"
      and \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)"
      and frame:  "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)"
      and frames: "conf_fs P h \<Phi> M (size Ts) T frs"
      and preh: "preallocated h"
      unfolding correct_state_def fr by(auto dest: sees_method_fun)

    from frame obtain stk: "P,h \<turnstile> stk [:\<le>] ST"
      and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and pc:  "pc < size ins" 
      by (unfold conf_f_def) auto
    
    from stk have [simp]: "size stk = size ST" ..

    from wtp meth correct fr have wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
      by (auto simp add: correct_state_def conf_f_def
                   dest: sees_method_fun
                   elim!: wt_jvm_prog_impl_wt_instr)

    from wt \<Phi>_pc have
      eff: "\<forall>(pc', s')\<in>set (xcpt_eff (ins!pc) P pc (ST,LT) xt).
             pc' < size ins \<and> P \<turnstile> s' \<le>' \<Phi> C M!pc'"
      by (auto simp add: defs1)

    let ?stk' = "Addr xcp # drop (length stk - d') stk"
    let ?f = "(?stk', loc, C, M, pc')"

    have conf: "P,h \<turnstile> Addr xcp :\<le> Class (case D' of None \<Rightarrow> Throwable | Some D'' \<Rightarrow> D'')"
      using DsubD' hxcp DsubThrowable by(auto simp add: conf_def)

    obtain ST' LT' where
      \<Phi>_pc': "\<Phi> C M ! pc' = Some (ST', LT')" and
      pc':   "pc' < size ins" and
      less:  "P \<turnstile> (Class D # drop (size ST - d') ST, LT) \<le>\<^sub>i (ST', LT')"
    proof(cases D')
      case Some
      thus ?thesis using eff rv DsubD' conf that
        by(fastforce simp add: xcpt_eff_def sup_state_opt_any_Some intro: widen_trans[OF widen_subcls])
    next
      case None
      with that eff rv conf DsubThrowable show ?thesis
        by(fastforce simp add: xcpt_eff_def sup_state_opt_any_Some intro: widen_trans[OF widen_subcls])
    qed

    with conf loc stk hxcp have "conf_f P h (ST',LT') ins ?f" 
      by (auto simp add: defs1 conf_def intro: list_all2_dropI)

    with meth h_ok frames \<Phi>_pc' fr match hxcp tconf preh
    show ?thesis unfolding correct_state_def
      by(fastforce dest: sees_method_fun simp add: cname_of_def)
  qed
qed

end

subsection \<open>Single Instructions\<close>

text \<open>
  In this subsection we prove for each single (welltyped) instruction
  that the state after execution of the instruction still conforms.
  Since we have already handled raised exceptions above, we can now assume that
  no exception has been raised in this step.
\<close>

context JVM_conf_read begin

declare defs1 [simp]

lemma Invoke_correct: 
  fixes \<sigma>' :: "('addr, 'heap) jvm_state"
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth_C: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:    "ins ! pc = Invoke M' n"
  assumes wti:    "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes approx: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes exec: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma> \<surd>"
proof -
  note split_paired_Ex [simp del]
  
  from wtprog obtain wfmb where wfprog: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)
      
  from ins meth_C approx obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (fastforce dest: sees_method_fun)

  from ins wti \<Phi>_pc
  have n: "n < size ST" by simp
  
  show ?thesis
  proof(cases "stk!n = Null")
    case True
    with ins heap_ok \<Phi>_pc frame frames exec meth_C tconf preh show ?thesis
      by(fastforce elim: wf_preallocatedE[OF wfprog, where C=NullPointer])
  next
    case False
    note Null = this
    have NT: "ST!n \<noteq> NT"
    proof
      assume "ST!n = NT"
      moreover from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with n have "P,h \<turnstile> stk!n :\<le> ST!n" by (simp add: list_all2_conv_all_nth)
      ultimately have "stk!n = Null" by simp
      with Null show False by contradiction
    qed

    from frame obtain 
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" by simp

    from NT ins wti \<Phi>_pc have pc': "pc+1 < size ins" by simp

    from NT ins wti \<Phi>_pc obtain ST' LT'
      where pc': "pc+1 < size ins"
      and \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')"
      and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
      by(auto simp add: neq_Nil_conv sup_state_opt_any_Some split: if_split_asm)
    with NT ins wti \<Phi>_pc obtain D D' TTs TT m
      where D: "class_type_of' (ST!n) = \<lfloor>D\<rfloor>"
      and m_D: "P \<turnstile> D sees M': TTs\<rightarrow>TT = m in D'"
      and Ts:  "P \<turnstile> rev (take n ST) [\<le>] TTs"
      and ST': "P \<turnstile> (TT # drop (n+1) ST) [\<le>] ST'" 
      by(auto)

    from n stk D have "P,h \<turnstile> stk!n :\<le> ST ! n"
      by (auto simp add: list_all2_conv_all_nth)
      
    from \<open>P,h \<turnstile> stk!n :\<le> ST ! n\<close> Null D
    obtain U a where
      Addr:   "stk!n = Addr a" and
      obj:    "typeof_addr h a = Some U" and
      UsubSTn: "P \<turnstile> ty_of_htype U \<le> ST ! n"
      by(cases "stk ! n")(auto simp add: conf_def widen_Class)

    from D UsubSTn obtain C' where
      C': "class_type_of' (ty_of_htype U) = \<lfloor>C'\<rfloor>" and C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
      by(rule widen_is_class_type_of) simp

    with wfprog m_D
    obtain Ts' T' D'' meth' where
      m_C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = meth' in D''" and
      T':   "P \<turnstile> T' \<le> TT" and
      Ts':  "P \<turnstile> TTs [\<le>] Ts'" 
      by (auto dest: sees_method_mono)

    from Ts n have [simp]: "size TTs = n" 
      by (auto dest: list_all2_lengthD simp: min_def)
    with Ts' have [simp]: "size Ts' = n" 
      by (auto dest: list_all2_lengthD)

    from m_C' wfprog
    obtain mD'': "P \<turnstile> D'' sees M':Ts'\<rightarrow>T'=meth' in D''"
      by (fast dest: sees_method_idemp)

    { fix mxs' mxl' ins' xt'
      assume [simp]: "meth' = \<lfloor>(mxs', mxl', ins', xt')\<rfloor>"
      let ?loc' = "Addr a # rev (take n stk) @ replicate mxl' undefined_value"
      let ?f' = "([], ?loc', D'', M', 0)"
      let ?f  = "(stk, loc, C, M, pc)"
      
      from Addr obj m_C' ins meth_C exec C' False
      have s': "\<sigma> = (None, h, ?f' # ?f # frs)" by(auto split: if_split_asm)
      
      moreover 
      from wtprog mD''
      obtain start: "wt_start P D'' Ts' mxl' (\<Phi> D'' M')" and ins': "ins' \<noteq> []"
        by (auto dest: wt_jvm_prog_impl_wt_start)
      then obtain LT\<^sub>0 where LT\<^sub>0: "\<Phi> D'' M' ! 0 = Some ([], LT\<^sub>0)"
        by (clarsimp simp add: wt_start_def defs1 sup_state_opt_any_Some)
      moreover
      have "conf_f P h ([], LT\<^sub>0) ins' ?f'"
      proof -
        let ?LT = "OK (Class D'') # (map OK Ts') @ (replicate mxl' Err)"
        
        from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
        hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" by simp
        also note Ts also note Ts' finally
        have "P,h \<turnstile> rev (take n stk) [:\<le>\<^sub>\<top>] map OK Ts'" by simp 
        also
        have "P,h \<turnstile> replicate mxl' undefined_value [:\<le>\<^sub>\<top>] replicate mxl' Err" by simp
        also from m_C' have "P \<turnstile> C' \<preceq>\<^sup>* D''" by (rule sees_method_decl_above)
        from obj heap_ok have "is_htype P U" by (rule typeof_addr_is_type)
        with C' have "P \<turnstile> ty_of_htype U \<le> Class C'" 
          by(cases U)(simp_all add: widen_array_object)
        with \<open>P \<turnstile> C' \<preceq>\<^sup>* D''\<close> obj C' have "P,h \<turnstile> Addr a :\<le> Class D''"
          by (auto simp add: conf_def intro: widen_trans)
        ultimately
        have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] ?LT" by simp
        also from start LT\<^sub>0 have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT\<^sub>0" by (simp add: wt_start_def)
        finally have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] LT\<^sub>0" .
        thus ?thesis using ins' by simp
      qed
      ultimately have ?thesis using s' \<Phi>_pc approx meth_C m_D T' ins D tconf C' mD''
        by (fastforce dest: sees_method_fun [of _ C]) }
    moreover
    { assume [simp]: "meth' = Native"
      with wfprog m_C' have "D''\<bullet>M'(Ts') :: T'" by(simp add: sees_wf_native)
      with C' m_C' have nec: "is_native P U M'" by(auto intro: is_native.intros)

      from ins n Addr obj exec m_C' C'
      obtain va h' tas' where va: "(tas', va, h') \<in> red_external_aggr P t a M' (rev (take n stk)) h"
        and \<sigma>: "\<sigma> = extRet2JVM n h' stk loc C M pc frs va" by(auto)
      from va nec obj have hext: "h \<unlhd> h'" by(auto intro: red_external_aggr_hext)
      with frames have frames': "conf_fs P h' \<Phi> M (length Ts) T frs" by(rule conf_fs_hext)
      from preh hext have preh': "preallocated h'" by(rule preallocated_hext)      
      from va nec obj tconf have tconf': "P,h' \<turnstile> t \<surd>t"
        by(auto dest: red_external_aggr_preserves_tconf)
      from hext obj have obj': "typeof_addr h' a = \<lfloor>U\<rfloor>" by(rule typeof_addr_hext_mono)

      from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
      then obtain Us where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Us" "P \<turnstile> Us [\<le>] take n ST"
        by(auto simp add: confs_conv_map)
      hence Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Us)" "P \<turnstile> rev Us [\<le>] rev (take n ST)"
        by- (simp only: rev_map[symmetric], simp)
      from \<open>P \<turnstile> rev Us [\<le>] rev (take n ST)\<close> Ts Ts'
      have "P \<turnstile> rev Us [\<le>] Ts'" by(blast intro: widens_trans)
      with obj \<open>map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Us)\<close> C' m_C' 
      have wtext': "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : T'" by(simp add: external_WT'.intros)
      from va have va': "P,t \<turnstile> \<langle>a\<bullet>M'(rev (take n stk)),h\<rangle> -tas'\<rightarrow>ext \<langle>va,h'\<rangle>"
        by(unfold WT_red_external_list_conv[OF wfprog wtext' tconf])
      with heap_ok wtext' tconf wfprog have heap_ok': "hconf h'" by(auto dest: external_call_hconf)

      have ?thesis
      proof(cases va)
        case (RetExc a')
        from frame hext have "conf_f P h' (ST, LT) ins (stk, loc, C, M, pc)" by(rule conf_f_hext)
        with \<sigma> tconf' heap_ok' meth_C \<Phi>_pc frames' RetExc red_external_conf_extRet[OF wfprog va' wtext' heap_ok preh tconf] ins preh'
        show ?thesis by(fastforce simp add: conf_def widen_Class)
      next
        case RetStaySame
        from frame hext have "conf_f P h' (ST, LT) ins (stk, loc, C, M, pc)" by(rule conf_f_hext)
        with \<sigma> heap_ok' meth_C \<Phi>_pc RetStaySame frames' tconf' preh' show ?thesis by fastforce
      next
        case (RetVal v)
        with \<sigma> have \<sigma>: "\<sigma> = (None, h', (v # drop (n+1) stk, loc, C, M, pc+1) # frs)" by simp
        from heap_ok wtext' va' RetVal preh tconf have "P,h' \<turnstile> v :\<le> T'"
          by(auto dest: red_external_conf_extRet[OF wfprog])
        from stk have "P,h \<turnstile> drop (n + 1) stk [:\<le>] drop (n+1) ST" by(rule list_all2_dropI)
        hence "P,h' \<turnstile> drop (n + 1) stk [:\<le>] drop (n+1) ST" using hext by(rule confs_hext)
        with \<open>P,h' \<turnstile> v :\<le> T'\<close> have "P,h' \<turnstile> v # drop (n + 1) stk [:\<le>] T' # drop (n+1) ST"
          by(auto simp add: conf_def intro: widen_trans)
        also
        with NT ins wti \<Phi>_pc \<Phi>' nec False D m_D T'
        have "P \<turnstile> (T' # drop (n + 1) ST) [\<le>] ST'"
          by(auto dest: sees_method_fun intro: widen_trans)
        also from loc hext have "P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT" by(rule confTs_hext)
        hence "P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" using LT' by(rule confTs_widen)
        ultimately show ?thesis using \<open>hconf h'\<close> \<sigma> meth_C \<Phi>' pc' frames' tconf' preh' by fastforce
      qed }
    ultimately show ?thesis by(cases meth') auto
  qed
qed

declare list_all2_Cons2 [iff]

lemma Return_correct:
  assumes wt_prog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins: "ins ! pc = Return"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes correct: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes s': "(tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs)"
  shows "\<Phi> \<turnstile> t:\<sigma>'\<surd>"
proof -
  from wt_prog 
  obtain wfmb where wf: "wf_prog wfmb P" by (simp add: wf_jvm_prog_phi_def)

  from meth ins s' correct
  have "frs = [] \<Longrightarrow> ?thesis" by (simp add: correct_state_def)
  moreover
  { fix f frs' assume frs': "frs = f#frs'"
    moreover obtain stk' loc' C' M' pc' where 
      f: "f = (stk',loc',C',M',pc')" by (cases f)
    moreover note meth ins s'
    ultimately
    have \<sigma>':
      "\<sigma>' = (None,h,(hd stk#(drop (1+size Ts) stk'),loc',C',M',pc'+1)#frs')"
      (is "\<sigma>' = (None,h,?f'#frs')")
      by simp
    
    from correct meth
    obtain ST LT where
      h_ok:   "hconf h" and
      tconf: "P,h \<turnstile> t \<surd>t" and
      \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)" and
      frame:  "conf_f P h (ST, LT) ins (stk,loc,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs" and
      preh: "preallocated h"
      by (auto dest: sees_method_fun)

    from \<Phi>_pc ins wt
    obtain U ST\<^sub>0 where "ST = U # ST\<^sub>0" "P \<turnstile> U \<le> T"
      by (simp add: wt_instr_def app_def) blast    
    with wf frame 
    have hd_stk: "P,h \<turnstile> hd stk :\<le> T" by (auto simp add: conf_f_def)

    from f frs' frames
    obtain ST' LT' Ts'' T'' mxs' mxl\<^sub>0' ins' xt' Ts' T' where
      \<Phi>': "\<Phi> C' M' ! pc' = Some (ST', LT')" and
      meth_C':  "P \<turnstile> C' sees M':Ts''\<rightarrow>T''=\<lfloor>(mxs',mxl\<^sub>0',ins',xt')\<rfloor> in C'" and
      ins': "ins' ! pc' = Invoke M (size Ts)" and
      D: "\<exists>D m D'. class_type_of' (ST' ! (size Ts)) = Some D \<and> P \<turnstile> D sees M: Ts'\<rightarrow>T' = m in D'" and
      T': "P \<turnstile> T \<le> T'" and
      frame':   "conf_f P h (ST',LT') ins' f" and
      conf_fs:  "conf_fs P h \<Phi> M' (size Ts'') T'' frs'"
      by clarsimp blast

    from f frame' obtain
      stk': "P,h \<turnstile> stk' [:\<le>] ST'" and
      loc': "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT'" and
      pc':  "pc' < size ins'"
      by (simp add: conf_f_def)
    
    from wt_prog meth_C' pc'  
    have wti: "P,T'',mxs',size ins',xt' \<turnstile> ins'!pc',pc' :: \<Phi> C' M'"
      by (rule wt_jvm_prog_impl_wt_instr)

    obtain aTs ST'' LT'' where
      \<Phi>_suc:   "\<Phi> C' M' ! Suc pc' = Some (ST'', LT'')" and
      less:    "P \<turnstile> (T' # drop (size Ts+1) ST', LT') \<le>\<^sub>i (ST'', LT'')" and
      suc_pc': "Suc pc' < size ins'"
      using ins' \<Phi>' D T' wti
      by(fastforce simp add: sup_state_opt_any_Some split: if_split_asm)

    from hd_stk T' have hd_stk': "P,h \<turnstile> hd stk :\<le> T'"  ..
        
    have frame'':
      "conf_f P h (ST'',LT'') ins' ?f'" 
    proof -
      from stk'
      have "P,h \<turnstile> drop (1+size Ts) stk' [:\<le>] drop (1+size Ts) ST'" ..
      moreover
      with hd_stk' less
      have "P,h \<turnstile> hd stk # drop (1+size Ts) stk' [:\<le>] ST''" by auto
      moreover
      from wf loc' less have "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT''" by auto
      moreover note suc_pc' 
      ultimately show ?thesis by (simp add: conf_f_def)
    qed

    with \<sigma>' frs' f meth h_ok hd_stk \<Phi>_suc frames meth_C' \<Phi>'  tconf preh
    have ?thesis by (fastforce dest: sees_method_fun [of _ C'])
  }
  ultimately
  show ?thesis by (cases frs) blast+
qed

declare sup_state_opt_any_Some [iff]
declare not_Err_eq [iff] 

lemma Load_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
    ins!pc = Load idx; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd> ;
    (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>' \<surd>"
  by (fastforce dest: sees_method_fun [of _ C] elim!: confTs_confT_sup)

declare [[simproc del: list_to_set_comprehension]]

lemma Store_correct:
"\<lbrakk> wf_prog wt P;
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C;
  ins!pc = Store idx;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M;
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply clarsimp
  apply (blast intro!: list_all2_update_cong)
  done

lemma Push_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
    ins!pc = Push v;
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>; 
    (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>" 
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply clarsimp
  apply (blast dest: typeof_lit_conf)
  done

declare [[simproc add: list_to_set_comprehension]]

lemma Checkcast_correct:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
    ins!pc = Checkcast D; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
    (tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs \<rbrakk> 
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma> \<surd>"
using wf_preallocatedD[of "\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M)" P h ClassCast]
apply (clarsimp simp add: wf_jvm_prog_phi_def split: if_split_asm)
 apply(drule (1) sees_method_fun)
 apply(fastforce simp add: conf_def intro: widen_trans)
apply (drule (1) sees_method_fun)
apply(fastforce simp add: conf_def intro: widen_trans)
done

lemma Instanceof_correct:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P;
    P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
    ins!pc = Instanceof Ty; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
    (tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs \<rbrakk> 
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma> \<surd>"
  apply (clarsimp simp add: wf_jvm_prog_phi_def split: if_split_asm)
  apply (drule (1) sees_method_fun)
  apply fastforce
  done

declare split_paired_All [simp del]

end

lemma widens_Cons [iff]:
  "P \<turnstile> (T # Ts) [\<le>] Us = (\<exists>z zs. Us = z # zs \<and> P \<turnstile> T \<le> z \<and> P \<turnstile> Ts [\<le>] zs)"
by(rule list_all2_Cons1)

context heap_conf_base begin


end

context JVM_conf_read begin

lemma Getfield_correct:
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes i:  "ins!pc = Getfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes cf: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes xc: "(tas, \<sigma>') \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"

  shows "\<Phi> \<turnstile> t:\<sigma>'\<surd>"
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "hconf h" and
    tconf: "P,h \<turnstile> t \<surd>t" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh: "preallocated h"
    by (fastforce dest: sees_method_fun)
       
  from i \<Phi> wt obtain oT ST'' vT ST' LT' vT' fm where 
    oT: "P \<turnstile> oT \<le> Class D" and
    ST: "ST = oT # ST''" and
    F:  "P \<turnstile> D sees F:vT (fm) in D" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (vT'#ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and  
    vT': "P \<turnstile> vT \<le> vT'"
    by fastforce                       

  from stk ST obtain ref stk' where 
    stk': "stk = ref#stk'" and
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  show ?thesis
  proof(cases "ref = Null")
    case True
    with tconf "h\<surd>" i xc stk' mC fs \<Phi> ST'' ref ST loc pc' 
      wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
    with False obtain a U' D' where a: "ref = Addr a"
      and h: "typeof_addr h a = Some U'"
      and U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
      by (blast dest: non_npD2)

    { fix v
      assume read: "heap_read h a (CField D F) v"
      from D' F have has_field: "P \<turnstile> D' has F:vT (fm) in D"
        by (blast intro: has_field_mono has_visible_field)
      with h have "P,h \<turnstile> a@CField D F : vT" unfolding U' .. 
      with read have v: "P,h \<turnstile> v :\<le> vT" using "h\<surd>"
        by(rule heap_read_conf)
      
      from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
      moreover
      from v vT' have "P,h \<turnstile> v :\<le> vT'" by blast
      moreover
      from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
      moreover
      note "h\<surd>" mC \<Phi>' pc' v fs tconf preh
      ultimately have "\<Phi> \<turnstile> t:(None, h, (v#stk',loc,C,M,pc+1)#frs) \<surd>" by fastforce }
    with a h i mC stk' xc
    show ?thesis by auto
  qed
qed

lemma Putfield_correct:
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes i:  "ins!pc = Putfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes cf: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes xc: "(tas, \<sigma>') \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma>' \<surd>"
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "hconf h" and    
    tconf: "P,h \<turnstile> t \<surd>t" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh: "preallocated h"
    by (fastforce dest: sees_method_fun)
  
  from i \<Phi> wt obtain vT vT' oT ST'' ST' LT' fm where 
    ST: "ST = vT # oT # ST''" and
    field: "P \<turnstile> D sees F:vT' (fm) in D" and
    oT: "P \<turnstile> oT \<le> Class D" and vT: "P \<turnstile> vT \<le> vT'" and
    pc': "pc+1 < size ins" and 
    \<Phi>': "\<Phi> C M!(pc+1) = Some (ST',LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
    by clarsimp

  from stk ST obtain v ref stk' where 
    stk': "stk = v#ref#stk'" and
    v:    "P,h \<turnstile> v :\<le> vT" and 
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  show ?thesis
  proof(cases "ref = Null")
    case True
    with tconf "h\<surd>" i xc stk' mC fs \<Phi> ST'' ref ST loc pc' v
      wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
    with False obtain a U' D' where 
      a: "ref = Addr a" and h: "typeof_addr h a = Some U'"
      and U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
      by (blast dest: non_npD2)
    
    from v vT have vT': "P,h \<turnstile> v :\<le> vT'" ..
    
    from field D' have has_field: "P \<turnstile> D' has F:vT' (fm) in D"
      by (blast intro: has_field_mono has_visible_field)
    with h have al: "P,h \<turnstile> a@CField D F : vT'" unfolding U' ..
    let ?f' = "(stk',loc,C,M,pc+1)"

    { fix h'
      assume "write": "heap_write h a (CField D F) v h'"
      hence hext: "h \<unlhd> h'" by(rule hext_heap_write)
      with preh have "preallocated h'" by(rule preallocated_hext)
      moreover
      from "write" "h\<surd>" al vT' have "hconf h'" by(rule hconf_heap_write_mono)
      moreover
      from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
      from this hext have "P,h' \<turnstile> stk' [:\<le>] ST'" by (rule confs_hext)
      moreover
      from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
      from this hext have "P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by (rule confTs_hext)
      moreover
      from fs hext
      have "conf_fs P h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
      moreover
      note mC \<Phi>' pc' 
      moreover
      from tconf hext have "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
      ultimately have "\<Phi> \<turnstile> t:(None, h', ?f'#frs) \<surd>" by fastforce }
    with a h i mC stk' xc show ?thesis by(auto simp del: correct_state_def)
  qed
qed

lemma CAS_correct:
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes i:  "ins!pc = CAS F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes cf: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes xc: "(tas, \<sigma>') \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma>' \<surd>"
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "hconf h" and    
    tconf: "P,h \<turnstile> t \<surd>t" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh: "preallocated h"
    by (fastforce dest: sees_method_fun)
  
  from i \<Phi> wt obtain T1 T2 T3 T' ST'' ST' LT' fm where 
    ST: "ST = T3 # T2 # T1 # ST''" and
    field: "P \<turnstile> D sees F:T' (fm) in D" and
    oT: "P \<turnstile> T1 \<le> Class D" and T2: "P \<turnstile> T2 \<le> T'" and T3: "P \<turnstile> T3 \<le> T'" and
    pc': "pc+1 < size ins" and 
    \<Phi>': "\<Phi> C M!(pc+1) = Some (Boolean # ST',LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
    by clarsimp

  from stk ST obtain v'' v' v stk' where 
    stk': "stk = v''#v'#v#stk'" and
    v:    "P,h \<turnstile> v :\<le> T1" and 
    v':  "P,h \<turnstile> v' :\<le> T2" and
    v'': "P,h \<turnstile> v'' :\<le> T3" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  show ?thesis
  proof(cases "v = Null")
    case True
    with tconf "h\<surd>" i xc stk' mC fs \<Phi> ST'' v ST loc pc' v' v''
      wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    from v oT have "P,h \<turnstile> v :\<le> Class D" ..
    with False obtain a U' D' where 
      a: "v = Addr a" and h: "typeof_addr h a = Some U'"
      and U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
      by (blast dest: non_npD2)
    
    from v' T2 have vT': "P,h \<turnstile> v' :\<le> T'" ..
    from v'' T3 have vT'': "P,h \<turnstile> v'' :\<le> T'" ..
    
    from field D' have has_field: "P \<turnstile> D' has F:T' (fm) in D"
      by (blast intro: has_field_mono has_visible_field)
    with h have al: "P,h \<turnstile> a@CField D F : T'" unfolding U' ..

    from ST'' ST' have stk'': "P,h \<turnstile> stk' [:\<le>] ST'" ..
    from loc LT' have loc': "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    { fix h'
      assume "write": "heap_write h a (CField D F) v'' h'"
      hence hext: "h \<unlhd> h'" by(rule hext_heap_write)
      with preh have "preallocated h'" by(rule preallocated_hext)
      moreover
      from "write" "h\<surd>" al vT'' have "hconf h'" by(rule hconf_heap_write_mono)
      moreover
      from stk'' hext have "P,h' \<turnstile> stk' [:\<le>] ST'" by (rule confs_hext)
      moreover
      from loc' hext have "P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by (rule confTs_hext)
      moreover
      from fs hext
      have "conf_fs P h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
      moreover
      note mC \<Phi>' pc' 
      moreover
      let ?f' = "(Bool True # stk',loc,C,M,pc+1)"
      from tconf hext have "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
      ultimately have "\<Phi> \<turnstile> t:(None, h', ?f'#frs) \<surd>" by fastforce 
    } moreover {
      let ?f' = "(Bool False # stk',loc,C,M,pc+1)"
      have "\<Phi> \<turnstile> t:(None, h, ?f'#frs) \<surd>" using tconf "h\<surd>" preh mC \<Phi>' stk'' loc' pc' fs
        by fastforce
    } ultimately show ?thesis using a h i mC stk' xc by(auto simp del: correct_state_def)
  qed
qed

lemma New_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = New X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from \<Phi>_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class P X" and
    mxs:       "size ST < mxs" and
    suc_pc:     "pc+1 < size ins" and
    \<Phi>_suc:      "\<Phi> C M!(pc+1) = Some (ST', LT')" and
    less:       "P \<turnstile> (Class X # ST, LT) \<le>\<^sub>i (ST', LT')"
    by auto
  show ?thesis
  proof(cases "allocate h (Class_type X) = {}")
    case True
    with frame frames tconf suc_pc no_x ins meth \<Phi>_pc
      wf_preallocatedD[OF wf, of h OutOfMemory] preh is_class_X heap_ok
    show ?thesis
      by(fastforce intro: tconf_hext_mono confs_hext confTs_hext conf_fs_hext)
  next
    case False
    with ins meth no_x obtain h' oref 
      where new: "(h', oref) \<in> allocate h (Class_type X)"
      and \<sigma>': "\<sigma> = (None, h', (Addr oref#stk,loc,C,M,pc+1)#frs)" (is "\<sigma> = (None, h', ?f # frs)")
      by auto

    from new have hext: "h \<unlhd> h'" by(rule hext_allocate)
    with preh have preh': "preallocated h'" by(rule preallocated_hext)
    from new heap_ok is_class_X have heap_ok': "hconf h'"
      by(auto intro: hconf_allocate_mono)

    with new is_class_X have h': "typeof_addr h' oref = \<lfloor>Class_type X\<rfloor>" by(auto dest: allocate_SomeD)
  
    note heap_ok' \<sigma>'
    moreover
    from frame less suc_pc wf h' hext
    have "conf_f P h' (ST', LT') ins ?f"
      apply (clarsimp simp add: fun_upd_apply conf_def split_beta)
      apply (auto intro: confs_hext confTs_hext)
      done
    moreover
    from frames hext have "conf_fs P h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
    moreover from tconf hext have "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
    ultimately
    show ?thesis using meth \<Phi>_suc preh' by fastforce
  qed
qed

lemma Goto_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = Goto branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>; 
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>' \<surd>"
apply clarsimp 
apply (drule (1) sees_method_fun)
apply fastforce
done

declare [[simproc del: list_to_set_comprehension]]

lemma IfFalse_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = IfFalse branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastforce
done

declare [[simproc add: list_to_set_comprehension]]

lemma BinOp_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = BinOpInstr bop;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
apply clarsimp
apply (drule (1) sees_method_fun)
apply(clarsimp simp add: conf_def)
apply(drule (2) WTrt_binop_widen_mono)
apply clarsimp
apply(frule (2) binop_progress)
apply(clarsimp split: sum.split_asm)
 apply(frule (5) binop_type)
 apply(fastforce intro: widen_trans simp add: conf_def)
apply(frule (5) binop_type)
apply(clarsimp simp add: conf_def)
apply(clarsimp simp add: widen_Class)
apply(fastforce intro: widen_trans dest: binop_relevant_class simp add: cname_of_def conf_def)
done

lemma Pop_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = Pop;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastforce
done

lemma Dup_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = Dup;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastforce
done

lemma Swap_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = Swap;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs) \<rbrakk>
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
apply clarsimp
apply (drule (1) sees_method_fun)
apply fastforce
done

declare [[simproc del: list_to_set_comprehension]]

lemma Throw_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C; 
  ins ! pc = ThrowExc; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  \<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>;
  (tas, \<sigma>') \<in> exec_instr (ins!pc) P t h stk loc C M pc frs \<rbrakk> 
\<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>'\<surd>"
using wf_preallocatedD[of wt P h NullPointer]
apply(clarsimp)
apply(drule (1) sees_method_fun)
apply(auto)
  apply fastforce
 apply fastforce
apply(drule (1) non_npD)
apply fastforce+
done

declare [[simproc add: list_to_set_comprehension]]

lemma NewArray_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = NewArray X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t:(None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf: "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins \<Phi>_pc wt obtain ST'' X' ST' LT' where 
    ST: "ST = Integer # ST''" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (X'#ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
    XX': "P \<turnstile> X\<lfloor>\<rceil> \<le> X'" and
    suc_pc:     "pc+1 < size ins" and
    is_type_X: "is_type P (X\<lfloor>\<rceil>)"
    by(fastforce dest: Array_widen)

  from stk ST obtain si stk' where si: "stk = Intg si # stk'"
    by(auto simp add: conf_def)

  show ?thesis
  proof(cases "si <s 0 \<or> allocate h (Array_type X (nat (sint si))) = {}")
    case True
    with frame frames tconf heap_ok suc_pc no_x ins meth \<Phi>_pc si preh
      wf_preallocatedD[OF wf, of h OutOfMemory] wf_preallocatedD[OF wf, of h NegativeArraySize]
    show ?thesis
      by(fastforce intro: tconf_hext_mono confs_hext confTs_hext conf_fs_hext split: if_split_asm)+
  next
    case False
    with ins meth si no_x obtain h' oref 
      where new: "(h', oref) \<in> allocate h (Array_type X (nat (sint si)))"
      and \<sigma>': "\<sigma> = (None, h', (Addr oref#tl stk,loc,C,M,pc+1)#frs)" (is "\<sigma> = (None, h', ?f # frs)")
      by(auto split: if_split_asm)
    from new have hext: "h \<unlhd> h'" by(rule hext_allocate)
    with preh have preh': "preallocated h'" by(rule preallocated_hext)
    from new heap_ok is_type_X have heap_ok': "hconf h'" by(auto intro: hconf_allocate_mono)
    from False have si': "0 <=s si" by auto
    with new is_type_X have h': "typeof_addr h' oref = \<lfloor>Array_type X (nat (sint si))\<rfloor>" 
      by(auto dest: allocate_SomeD)

    note \<sigma>' heap_ok'
    moreover
    from frame ST' ST LT' suc_pc wf XX' h' hext
    have "conf_f P h' (X' # ST', LT') ins ?f"
      by(clarsimp simp add: fun_upd_apply conf_def split_beta)(auto intro: confs_hext confTs_hext)
    moreover
    from frames hext have "conf_fs P h' \<Phi> M (size Ts) T frs" by (rule conf_fs_hext)
    moreover from tconf hext have "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
    ultimately
    show ?thesis using meth \<Phi>' preh' by fastforce
  qed 
qed

lemma ALoad_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = ALoad"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t:\<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 1" by(auto)

  show ?thesis
  proof(cases "hd (tl stk) = Null")
    case True
    with ins no_x heap_ok tconf \<Phi>_pc stk loc frame frames meth wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    note stkNN = this
    have STNN: "hd (tl ST) \<noteq> NT"
    proof
      assume "hd (tl ST) = NT"
      moreover 
      from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with lST have "P,h \<turnstile> hd (tl stk) :\<le> hd (tl ST)"
        by (cases ST, auto, case_tac list, auto)
      ultimately 
      have "hd (tl stk) = Null" by simp
      with stkNN show False by contradiction
    qed

    with stkNN ins \<Phi>_pc wt obtain ST'' X X' ST' LT' where 
      ST: "ST = Integer # X\<lfloor>\<rceil> # ST''" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (X'#ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      XX': "P \<turnstile> X \<le> X'" and
      suc_pc:     "pc+1 < size ins"
      by(fastforce)

    from stk ST obtain ref idx stk' where 
      stk': "stk = idx#ref#stk'" and
      idx: "P,h \<turnstile> idx :\<le> Integer" and
      ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" and
      ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel n
      where a: "ref = Addr a"
      and ha: "typeof_addr h a = \<lfloor>Array_type Xel n\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(cases ref)(fastforce simp add: conf_def widen_Array)+

    from idx obtain idxI where idxI: "idx = Intg idxI"
      by(auto simp add: conf_def)
    show ?thesis
    proof(cases "0 <=s idxI \<and> sint idxI < int n")
      case True
      hence si': "0 <=s idxI" "sint idxI < int n" by auto
      hence "nat (sint idxI) < n"
        by(metis nat_less_iff  sint_0 word_sle_def)
      with ha have al: "P,h \<turnstile> a@ACell (nat (sint idxI)) : Xel" ..

      { fix v
        assume read: "heap_read h a (ACell (nat (sint idxI))) v"
        hence v: "P,h \<turnstile> v :\<le> Xel" using al heap_ok by(rule heap_read_conf)

        let ?f = "(v # stk', loc, C, M, pc + 1)"
        
        from frame ST' ST LT' suc_pc wf XX' Xel idxI si' v ST''
        have "conf_f P h (X' # ST', LT') ins ?f"
          by(auto intro: widen_trans simp add: conf_def)
        hence "\<Phi> \<turnstile> t:(None, h, ?f # frs) \<surd>"
          using meth \<Phi>' heap_ok \<Phi>_pc frames tconf preh by fastforce }
      with ins meth si' stk' a ha no_x idxI idx 
      show ?thesis by(auto simp del: correct_state_def split: if_split_asm)
    next
      case False
      with stk' idxI ins no_x heap_ok tconf meth a ha Xel \<Phi>_pc frame frames
        wf_preallocatedD[OF wf, of h ArrayIndexOutOfBounds] preh
      show ?thesis by(fastforce split: if_split_asm)
    qed
  qed
qed


lemma AStore_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = AStore"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t: \<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf: "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 2" by(auto)
  
  show ?thesis
  proof(cases "hd (tl (tl stk)) = Null")
    case True
    with ins no_x heap_ok tconf \<Phi>_pc stk loc frame frames meth wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    note stkNN = this
    have STNN: "hd (tl (tl ST)) \<noteq> NT"       
    proof
      assume "hd (tl (tl ST)) = NT"
      moreover 
      from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with lST have "P,h \<turnstile> hd (tl (tl stk)) :\<le> hd (tl (tl ST))"
        by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
      ultimately 
      have "hd (tl (tl stk)) = Null" by simp
      with stkNN show False by contradiction
    qed

    with ins stkNN \<Phi>_pc wt obtain ST'' Y X ST' LT' where 
      ST: "ST = Y # Integer # X\<lfloor>\<rceil> # ST''" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastforce)

    from stk ST obtain ref e idx stk' where 
      stk': "stk = e#idx#ref#stk'" and
      idx: "P,h \<turnstile> idx :\<le> Integer" and
      ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" and
      e: "P,h \<turnstile> e :\<le> Y" and
      ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel n
      where a: "ref = Addr a"
      and ha: "typeof_addr h a = \<lfloor>Array_type Xel n\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(cases ref)(fastforce simp add: conf_def widen_Array)+

    from idx obtain idxI where idxI: "idx = Intg idxI"
      by(auto simp add: conf_def)
    
    show ?thesis
    proof(cases "0 <=s idxI \<and> sint idxI < int n")
      case True
      hence si': "0 <=s idxI" "sint idxI < int n" by simp_all

      from e obtain Te where Te: "typeof\<^bsub>h\<^esub> e = \<lfloor>Te\<rfloor>" "P \<turnstile> Te \<le> Y"
        by(auto simp add: conf_def)

      show ?thesis
      proof(cases "P \<turnstile> Te \<le> Xel")
        case True
        with Te have eXel: "P,h \<turnstile> e :\<le> Xel"
          by(auto simp add: conf_def intro: widen_trans)

        { fix h'
          assume "write": "heap_write h a (ACell (nat (sint idxI))) e h'"
          hence hext: "h \<unlhd> h'" by(rule hext_heap_write)
          with preh have preh': "preallocated h'" by(rule preallocated_hext)

          let ?f = "(stk', loc, C, M, pc + 1)"

          from si' have "nat (sint idxI) < n"
            by(metis nat_less_iff  sint_0 word_sle_def)
          with ha have "P,h \<turnstile> a@ACell (nat (sint idxI)) : Xel" ..
          with "write" heap_ok have heap_ok': "hconf h'" using eXel
            by(rule hconf_heap_write_mono)
          moreover
          from ST stk stk' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" by auto
          with hext have stk'': "P,h' \<turnstile> stk' [:\<le>] ST'"
            by- (rule confs_hext)
          moreover
          from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
          with hext have "P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by - (rule confTs_hext)
          moreover
          with frame ST' ST LT' suc_pc wf Xel idxI si' stk''
          have "conf_f P h' (ST', LT') ins ?f"
            by(clarsimp)
          with frames hext have "conf_fs P h' \<Phi> M (size Ts) T frs" by- (rule conf_fs_hext)
          moreover from tconf hext have "P,h' \<turnstile> t \<surd>t" by(rule tconf_hext_mono)
          ultimately have "\<Phi> \<turnstile> t:(None, h', ?f # frs) \<surd>" using meth \<Phi>' \<Phi>_pc suc_pc preh'
            by(fastforce) }
        with True si' ins meth stk' a ha no_x idxI idx Te
        show ?thesis
          by(auto split: if_split_asm simp del: correct_state_def intro: widen_trans)
      next
        case False
        with stk' idxI ins no_x heap_ok tconf meth a ha Xel Te \<Phi>_pc frame frames si' preh
          wf_preallocatedD[OF wf, of h ArrayStore]
        show ?thesis by(fastforce split: if_split_asm)
      qed
    next
      case False
      with stk' idxI ins no_x heap_ok tconf meth a ha Xel \<Phi>_pc frame frames preh
        wf_preallocatedD[OF wf, of h ArrayIndexOutOfBounds]
      show ?thesis by(fastforce split: if_split_asm)
    qed
  qed
qed

lemma ALength_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = ALength"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t: \<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 0" by(auto)
  
  show ?thesis
  proof(cases "hd stk = Null")
    case True
    with ins no_x heap_ok tconf \<Phi>_pc stk loc frame frames meth wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    note stkNN = this
    have STNN: "hd ST \<noteq> NT"
    proof
      assume "hd ST = NT"
      moreover 
      from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with lST have "P,h \<turnstile> hd stk :\<le> hd ST"
        by (cases ST, auto)
      ultimately 
      have "hd stk = Null" by simp
      with stkNN show False by contradiction
    qed

    with stkNN ins \<Phi>_pc wt obtain ST'' X ST' LT' where 
      ST: "ST = (X\<lfloor>\<rceil>) # ST''" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> (Integer # ST'') [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastforce)

    from stk ST obtain ref stk' where 
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" and
      ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    with ref obtain a Xel n
      where a: "ref = Addr a"
      and ha: "typeof_addr h a = \<lfloor>Array_type Xel n\<rfloor>"
      and Xel: "P \<turnstile> Xel \<le> X"
      by(cases ref)(fastforce simp add: conf_def widen_Array)+

    from ins meth stk' a ha no_x have \<sigma>':
      "\<sigma> = (None, h, (Intg (word_of_int (int n)) # stk', loc, C, M, pc + 1) # frs)"
      (is "\<sigma> = (None, h, ?f # frs)")
      by(auto)
    moreover
    from ST stk stk' ST' have "P,h \<turnstile> Intg si # stk' [:\<le>] ST'" by(auto)
    with frame ST' ST LT' suc_pc wf
    have "conf_f P h (ST', LT') ins ?f"
      by(fastforce intro: widen_trans)
    ultimately show ?thesis using meth \<Phi>' heap_ok \<Phi>_pc frames tconf preh by fastforce
  qed
qed


lemma MEnter_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = MEnter"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t: \<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 0" by(auto)

  show ?thesis
  proof(cases "hd stk = Null")
    case True
    with ins no_x heap_ok tconf \<Phi>_pc stk loc frame frames meth wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    note stkNN = this
    have STNN: "hd ST \<noteq> NT"
    proof
      assume "hd ST = NT"
      moreover 
      from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with lST have "P,h \<turnstile> hd stk :\<le> hd ST"
        by (cases ST, auto)
      ultimately 
      have "hd stk = Null" by simp
      with stkNN show False by contradiction
    qed

    with stkNN ins \<Phi>_pc wt obtain ST'' X ST' LT' where 
      ST: "ST = X # ST''" and
      refT: "is_refT X" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastforce)

    from stk ST obtain ref stk' where 
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> X"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    moreover
    from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    moreover
    from ST stk stk' ST'
    have "P,h \<turnstile> stk' [:\<le>] ST'" by(auto)
    ultimately show ?thesis using meth \<Phi>' heap_ok \<Phi>_pc suc_pc frames loc LT' no_x ins stk' ST' tconf preh
      by(fastforce)
  qed
qed

lemma MExit_correct:
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C"
  assumes ins:  "ins!pc = MExit"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes conf: "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd>"
  assumes no_x: "(tas, \<sigma>) \<in> exec_instr (ins!pc) P t h stk loc C M pc frs"
  shows "\<Phi> \<turnstile> t: \<sigma> \<surd>"
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "hconf h" and
    tconf:   "P,h \<turnstile> t \<surd>t" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:   "conf_f P h (ST,LT) ins (stk,loc,C,M,pc)" and
    frames:  "conf_fs P h \<Phi> M (size Ts) T frs" and
    preh:    "preallocated h"
    by (auto dest: sees_method_fun)

  from ins wt \<Phi>_pc have lST: "length ST > 0" by(auto)

  show ?thesis
  proof(cases "hd stk = Null")
    case True
    with ins no_x heap_ok tconf \<Phi>_pc stk loc frame frames meth wf_preallocatedD[OF wf, of h NullPointer] preh
    show ?thesis by(fastforce)
  next
    case False
    note stkNN = this
    have STNN: "hd ST \<noteq> NT"
    proof
      assume "hd ST = NT"
      moreover 
      from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
      with lST have "P,h \<turnstile> hd stk :\<le> hd ST"
        by (cases ST, auto)
      ultimately 
      have "hd stk = Null" by simp
      with stkNN show False by contradiction
    qed

    with stkNN ins \<Phi>_pc wt obtain ST'' X ST' LT' where 
      ST: "ST = X # ST''" and
      refT: "is_refT X" and
      pc': "pc+1 < size ins"  and
      \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      suc_pc:     "pc+1 < size ins"
      by(fastforce)

    from stk ST obtain ref stk' where 
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> X"
      by auto

    from stkNN stk' have "ref \<noteq> Null" by(simp)
    moreover
    from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
    moreover
    from ST stk stk' ST'
    have "P,h \<turnstile> stk' [:\<le>] ST'" by(auto)
    ultimately 
    show ?thesis using meth \<Phi>' heap_ok \<Phi>_pc suc_pc frames loc LT' no_x ins stk' ST' tconf frame preh
      wf_preallocatedD[OF wf, of h IllegalMonitorState]
      by(fastforce)
  qed
qed

text \<open>
  The next theorem collects the results of the sections above,
  i.e.~exception handling and the execution step for each 
  instruction. It states type safety for single step execution:
  in welltyped programs, a conforming state is transformed
  into another conforming state when one instruction is executed.
\<close>
theorem instr_correct:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P;
  P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> in C;
  (tas, \<sigma>') \<in> exec P t (None, h, (stk,loc,C,M,pc)#frs); 
  \<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> \<Phi> \<turnstile> t: \<sigma>'\<surd>"
apply (subgoal_tac "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M")
 prefer 2
 apply (erule wt_jvm_prog_impl_wt_instr, assumption)
 apply clarsimp
 apply (drule (1) sees_method_fun)
 apply simp
apply(unfold exec.simps Let_def set_map)
apply (frule wt_jvm_progD, erule exE)
apply (cases "ins ! pc")
apply (rule Load_correct, assumption+, fastforce)
apply (rule Store_correct, assumption+, fastforce)
apply (rule Push_correct, assumption+, fastforce)
apply (rule New_correct, assumption+, fastforce)
apply (rule NewArray_correct, assumption+, fastforce)
apply (rule ALoad_correct, assumption+, fastforce)
apply (rule AStore_correct, assumption+, fastforce)
apply (rule ALength_correct, assumption+, fastforce)
apply (rule Getfield_correct, assumption+, fastforce)
apply (rule Putfield_correct, assumption+, fastforce)
apply (rule CAS_correct, assumption+, fastforce)
apply (rule Checkcast_correct, assumption+, fastforce)
apply (rule Instanceof_correct, assumption+, fastforce)
apply (rule Invoke_correct, assumption+, fastforce)
apply (rule Return_correct, assumption+, fastforce simp add: split_beta)
apply (rule Pop_correct, assumption+, fastforce)
apply (rule Dup_correct, assumption+, fastforce)
apply (rule Swap_correct, assumption+, fastforce)
apply (rule BinOp_correct, assumption+, fastforce)
apply (rule Goto_correct, assumption+, fastforce)
apply (rule IfFalse_correct, assumption+, fastforce)
apply (rule Throw_correct, assumption+, fastforce)
apply (rule MEnter_correct, assumption+, fastforce)
apply (rule MExit_correct, assumption+, fastforce)
done

declare defs1 [simp del]

end

subsection \<open>Main\<close>

lemma (in JVM_conf_read) BV_correct_1 [rule_format]:
"\<And>\<sigma>. \<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t: \<sigma>\<surd>\<rbrakk> \<Longrightarrow> P,t \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>' \<longrightarrow> \<Phi> \<turnstile> t: \<sigma>'\<surd>"
apply (simp only: split_tupled_all exec_1_iff)
apply (rename_tac xp h frs)
apply (case_tac xp)
 apply (case_tac frs)
  apply simp
 apply (simp only: split_tupled_all)
 apply hypsubst
 apply (frule correct_state_impl_Some_method)
 apply clarify
 apply (rule instr_correct)
 apply assumption+
apply clarify
apply(case_tac frs)
 apply simp
apply(clarsimp simp only: exec.simps set_simps)
apply(erule (1) exception_step_conform)
done

theorem (in JVM_progress) progress:
  assumes wt: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and cs: "\<Phi> \<turnstile> t: (xcp, h, f # frs)\<surd>"
  shows "\<exists>ta \<sigma>'. P,t \<turnstile> (xcp, h, f # frs) -ta-jvm\<rightarrow> \<sigma>'"
proof -
  obtain stk loc C M pc where f: "f = (stk, loc, C, M, pc)" by(cases f)
  with cs obtain Ts T mxs mxl\<^sub>0 "is" xt ST LT
    where hconf: "hconf h"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl\<^sub>0, is, xt)\<rfloor> in C"
    and \<Phi>_pc: "\<Phi> C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    and ST: "P,h \<turnstile> stk [:\<le>] ST"
    and LT: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
    and pc: "pc < length is"
    by(auto simp add: defs1)
  show ?thesis
  proof(cases xcp)
    case Some thus ?thesis
      unfolding f exec_1_iff by auto
  next
    case [simp]: None
    note [simp del] = split_paired_Ex
    note [simp] = defs1 list_all2_Cons2


    from wt obtain wf_md where wf: "wf_prog wf_md P" by(auto dest: wt_jvm_progD)
    from wt sees pc have wt: "P,T,mxs,size is,xt \<turnstile> is!pc,pc :: \<Phi> C M"
      by(rule wt_jvm_prog_impl_wt_instr)


    have "\<exists>ta \<sigma>'. (ta, \<sigma>') \<in> exec_instr (is ! pc) P t h stk loc C M pc frs"
    proof(cases "is ! pc")
      case [simp]: ALoad
      with wt \<Phi>_pc have lST: "length ST > 1" by(auto)
      show ?thesis
      proof(cases "hd (tl stk) = Null")
        case True thus ?thesis by simp
      next
        case False
        have STNN: "hd (tl ST) \<noteq> NT"
        proof
          assume "hd (tl ST) = NT"
          moreover 
          from ST lST have "P,h \<turnstile> hd (tl stk) :\<le> hd (tl ST)"
            by (cases ST)(auto, case_tac list, auto)
          ultimately have "hd (tl stk) = Null" by simp
          with False show False by contradiction
        qed
        
        with False \<Phi>_pc wt obtain ST'' X where "ST = Integer # X\<lfloor>\<rceil> # ST''" by auto
        with ST obtain ref idx stk' where stk': "stk = idx#ref#stk'" and idx: "P,h \<turnstile> idx :\<le> Integer" 
          and ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" by(auto)

        from False stk' have "ref \<noteq> Null" by(simp)
        with ref obtain a Xel n where a: "ref = Addr a"
          and ha: "typeof_addr h a = \<lfloor>Array_type Xel n\<rfloor>"
          and Xel: "P \<turnstile> Xel \<le> X"
          by(cases ref)(fastforce simp add: conf_def widen_Array)+
        
        from idx obtain idxI where idxI: "idx = Intg idxI"
          by(auto simp add: conf_def)
        show ?thesis
        proof(cases "0 <=s idxI \<and> sint idxI < int n")
          case True
          hence si': "0 <=s idxI" "sint idxI < int n" by auto
          hence "nat (sint idxI) < n"
            by(metis nat_less_iff sint_0 word_sle_def)
          with ha have al: "P,h \<turnstile> a@ACell (nat (sint idxI)) : Xel" ..
          from heap_read_total[OF hconf this] True False ha stk' idxI a
          show ?thesis by auto
        next
          case False with ha stk' idxI a show ?thesis by auto
        qed
      qed
    next
      case [simp]: AStore
      from wt \<Phi>_pc have lST: "length ST > 2" by(auto)
      
      show ?thesis
      proof(cases "hd (tl (tl stk)) = Null")
        case True thus ?thesis by(fastforce)
      next
        case False
        note stkNN = this
        have STNN: "hd (tl (tl ST)) \<noteq> NT"       
        proof
          assume "hd (tl (tl ST)) = NT"
          moreover 
          from ST lST have "P,h \<turnstile> hd (tl (tl stk)) :\<le> hd (tl (tl ST))"
            by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
          ultimately have "hd (tl (tl stk)) = Null" by simp
          with stkNN show False by contradiction
        qed

        with stkNN \<Phi>_pc wt obtain ST'' Y X
          where "ST = Y # Integer # X\<lfloor>\<rceil> # ST''" by(fastforce)

        with ST obtain ref e idx stk' where stk': "stk = e#idx#ref#stk'" 
          and idx: "P,h \<turnstile> idx :\<le> Integer" and ref:  "P,h \<turnstile> ref :\<le> X\<lfloor>\<rceil>" 
          and e: "P,h \<turnstile> e :\<le> Y" by auto

        from stkNN stk' have "ref \<noteq> Null" by(simp)
        with ref obtain a Xel n where a: "ref = Addr a"
          and ha: "typeof_addr h a = \<lfloor>Array_type Xel n\<rfloor>"
          and Xel: "P \<turnstile> Xel \<le> X"
          by(cases ref)(fastforce simp add: conf_def widen_Array)+

        from idx obtain idxI where idxI: "idx = Intg idxI"
          by(auto simp add: conf_def)
        
        show ?thesis
        proof(cases "0 <=s idxI \<and> sint idxI < int n")
          case True
          hence si': "0 <=s idxI" "sint idxI < int n" by simp_all
          hence "nat (sint idxI) < n"
            by(metis nat_less_iff  sint_0 word_sle_def)
          with ha have adal: "P,h \<turnstile> a@ACell (nat (sint idxI)) : Xel" ..
          
          show ?thesis
          proof(cases "P \<turnstile> the (typeof\<^bsub>h\<^esub> e) \<le> Xel")
            case False
            with ha stk' idxI a show ?thesis by auto
          next
            case True
            hence "P,h \<turnstile> e :\<le> Xel" using e by(auto simp add: conf_def)
            from heap_write_total[OF hconf adal this] ha stk' idxI a show ?thesis by auto
          qed
        next
          case False with ha stk' idxI a show ?thesis by auto
        qed
      qed
    next
      case [simp]: (Getfield F D)

      from \<Phi>_pc wt obtain oT ST'' vT fm where oT: "P \<turnstile> oT \<le> Class D" 
        and "ST = oT # ST''" and F: "P \<turnstile> D sees F:vT (fm) in D" 
        by fastforce

      with ST obtain ref stk' where stk': "stk = ref#stk'" 
        and ref:  "P,h \<turnstile> ref :\<le> oT" by auto

      show ?thesis
      proof(cases "ref = Null")
        case True thus ?thesis using stk' by auto
      next
        case False
        from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
        with False obtain a U' D' where 
          a: "ref = Addr a" and h: "typeof_addr h a = Some U'"
          and U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
          by (blast dest: non_npD2)
    
        from D' F have has_field: "P \<turnstile> D' has F:vT (fm) in D"
          by (blast intro: has_field_mono has_visible_field)
        with h have "P,h \<turnstile> a@CField D F : vT" unfolding U' ..
        from heap_read_total[OF hconf this]
        show ?thesis using stk' a by auto
      qed
    next
      case [simp]: (Putfield F D)

      from \<Phi>_pc wt obtain vT vT' oT ST'' fm where "ST = vT # oT # ST''" 
        and field: "P \<turnstile> D sees F:vT' (fm) in D"
        and oT: "P \<turnstile> oT \<le> Class D"
        and vT': "P \<turnstile> vT \<le> vT'" by fastforce
      with ST obtain v ref stk' where stk': "stk = v#ref#stk'" 
        and ref:  "P,h \<turnstile> ref :\<le> oT" 
        and v: "P,h \<turnstile> v :\<le> vT" by auto

      show ?thesis
      proof(cases "ref = Null")
        case True with stk' show ?thesis by auto
      next
        case False
        from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
        with False obtain a U' D' where 
          a: "ref = Addr a" and h: "typeof_addr h a = Some U'" and
          U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
          by (blast dest: non_npD2)

        from field D' have has_field: "P \<turnstile> D' has F:vT' (fm) in D"
          by (blast intro: has_field_mono has_visible_field)
        with h have al: "P,h \<turnstile> a@CField D F : vT'" unfolding U' ..
        from v vT' have "P,h \<turnstile> v :\<le> vT'" by auto
        from heap_write_total[OF hconf al this] v a stk' h show ?thesis by auto
      qed
    next
      case [simp]: (CAS F D)
      from \<Phi>_pc wt obtain T' T1 T2 T3 ST'' fm where "ST = T3 # T2 # T1 # ST''" 
        and field: "P \<turnstile> D sees F:T' (fm) in D"
        and oT: "P \<turnstile> T1 \<le> Class D"
        and vT': "P \<turnstile> T2 \<le> T'" "P \<turnstile> T3 \<le> T'" by fastforce
      with ST obtain v v' v'' stk' where stk': "stk = v''#v'#v#stk'" 
        and v:  "P,h \<turnstile> v :\<le> T1" 
        and v': "P,h \<turnstile> v' :\<le> T2"
        and v'': "P,h \<turnstile> v'' :\<le> T3" by auto
      show ?thesis
      proof(cases "v= Null")
        case True with stk' show ?thesis by auto
      next
        case False
        from v oT have "P,h \<turnstile> v :\<le> Class D" ..
        with False obtain a U' D' where 
          a: "v = Addr a" and h: "typeof_addr h a = Some U'" and
          U': "D' = class_type_of U'" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
          by (blast dest: non_npD2)

        from field D' have has_field: "P \<turnstile> D' has F:T' (fm) in D"
          by (blast intro: has_field_mono has_visible_field)
        with h have al: "P,h \<turnstile> a@CField D F : T'" unfolding U' ..
        from v' vT' have "P,h \<turnstile> v' :\<le> T'" by auto
        from heap_read_total[OF hconf al] obtain v''' where v''': "heap_read h a (CField D F) v'''" by blast
        show ?thesis
        proof(cases "v''' = v'")
          case True
          from v'' vT' have "P,h \<turnstile> v'' :\<le> T'" by auto
          from heap_write_total[OF hconf al this] v a stk' h v''' True show ?thesis by auto
        next
          case False
          from v''' v a stk' h False show ?thesis by auto
        qed
      qed
    next
      case [simp]: (Invoke M' n)

      from wt \<Phi>_pc have n: "n < size ST" by simp
  
      show ?thesis
      proof(cases "stk!n = Null")
        case True thus ?thesis by simp
      next
        case False
        note Null = this
        have NT: "ST!n \<noteq> NT"
        proof
          assume "ST!n = NT"
          moreover from ST n have "P,h \<turnstile> stk!n :\<le> ST!n" by (simp add: list_all2_conv_all_nth)
          ultimately have "stk!n = Null" by simp
          with Null show False by contradiction
        qed

        from NT wt \<Phi>_pc obtain D D' Ts T m
          where D: "class_type_of' (ST!n) = Some D"
          and m_D: "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
          and Ts:  "P \<turnstile> rev (take n ST) [\<le>] Ts"
          by auto

        from n ST D have "P,h \<turnstile> stk!n :\<le> ST!n"
          by (auto simp add: list_all2_conv_all_nth)

        from \<open>P,h \<turnstile> stk!n :\<le> ST!n\<close> Null D
        obtain a T' where
          Addr:   "stk!n = Addr a" and
          obj:    "typeof_addr h a = Some T'" and
          T'subSTn: "P \<turnstile> ty_of_htype T' \<le> ST ! n"
          by(cases "stk ! n")(auto simp add: conf_def widen_Class)

        from D T'subSTn obtain C' where
          C': "class_type_of' (ty_of_htype T') = \<lfloor>C'\<rfloor>" and C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
          by(rule widen_is_class_type_of) simp

        from Call_lemma[OF m_D C'subD wf]
        obtain D' Ts' T' m' 
          where Call': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = m' in D'" "P \<turnstile> Ts [\<le>] Ts'"
            "P \<turnstile> T' \<le> T" "P \<turnstile> C' \<preceq>\<^sup>* D'" "is_type P T'" "\<forall>T\<in>set Ts'. is_type P T"
          by blast
        
        show ?thesis
        proof(cases m')
          case Some with Call' C' obj Addr C' C'subD show ?thesis by(auto)
        next
          case [simp]: None
          from ST have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
          then obtain Us where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Us" "P \<turnstile> Us [\<le>] take n ST"
            by(auto simp add: confs_conv_map)
          hence Us: "map typeof\<^bsub>h\<^esub> (rev (take n stk)) = map Some (rev Us)" "P \<turnstile> rev Us [\<le>] rev (take n ST)"
            by- (simp only: rev_map[symmetric], simp)
          with Ts \<open>P \<turnstile> Ts [\<le>] Ts'\<close> have "P \<turnstile> rev Us [\<le>] Ts'" by(blast intro: widens_trans)
          with obj Us Call' C' have "P,h \<turnstile> a\<bullet>M'(rev (take n stk)) : T'"
            by(auto intro!: external_WT'.intros)
          from external_call_progress[OF wf this hconf, of t] obj Addr Call' C'
          show ?thesis by(auto dest!: red_external_imp_red_external_aggr)
        qed
      qed
    qed(auto 4 4 simp add: split_beta split: if_split_asm)
    thus ?thesis using sees None
      unfolding f exec_1_iff by(simp del: split_paired_Ex)
  qed
qed

lemma (in JVM_heap_conf) BV_correct_initial:
  shows "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; start_heap_ok; P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in D; P,start_heap \<turnstile> vs [:\<le>] Ts \<rbrakk>
  \<Longrightarrow> \<Phi> \<turnstile> start_tid:JVM_start_state' P C M vs \<surd>"
  apply (cases m)
  apply (unfold JVM_start_state'_def)
  apply (unfold correct_state_def)
  apply (clarsimp)
  apply (frule wt_jvm_progD)
  apply (erule exE)
  apply (frule wf_prog_wf_syscls)
  apply (rule conjI)
   apply(erule (1) tconf_start_heap_start_tid)
  apply(rule conjI)
   apply (simp add: wf_jvm_prog_phi_def hconf_start_heap) 
  apply(frule sees_method_idemp)
  apply (frule wt_jvm_prog_impl_wt_start, assumption+)
  apply (unfold conf_f_def wt_start_def)
  apply(auto simp add: sup_state_opt_any_Some)
   apply(erule preallocated_start_heap)
  apply(rule exI conjI|assumption)+
  apply(auto simp add: list_all2_append1)
  apply(auto dest: list_all2_lengthD intro!: exI)
  done

end
