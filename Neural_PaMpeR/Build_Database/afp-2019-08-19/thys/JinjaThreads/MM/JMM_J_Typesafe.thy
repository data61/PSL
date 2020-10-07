(*  Title:      JinjaThreads/MM/JMM_J_Typesafe.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM type safety for source code\<close>

theory JMM_J_Typesafe imports
  JMM_Typesafe2
  DRF_J
begin

locale J_allocated_heap_conf' = 
  h: J_heap_conf 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write hconf
    P
  +
  h: J_allocated_heap 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
    allocated
    P
  +
  heap''
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr J_prog"

sublocale J_allocated_heap_conf' < h: J_allocated_heap_conf
  addr2thread_id thread_id2addr
  spurious_wakeups
  empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write hconf allocated
  P
by(unfold_locales)

context J_allocated_heap_conf' begin

lemma red_New_type_match:
  "\<lbrakk> h.red' P t e s ta e' s'; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>" 
  and reds_New_type_match:
  "\<lbrakk> h.reds' P t es s ta es' s'; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(induct rule: h.red_reds.inducts)(auto dest: allocate_typeof_addr_SomeD red_external_New_type_match)

lemma mred_known_addrs_typing':
  assumes wf: "wf_J_prog P"
  and ok: "h.start_heap_ok"
  shows "known_addrs_typing' addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated h.J_known_addrs final_expr (h.mred P) (\<lambda>t x h. \<exists>ET. h.sconf_type_ok ET t x h) P"
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr 
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
    allocated h.J_known_addrs
    final_expr "h.mred P" "\<lambda>t x h. \<exists>ET. h.sconf_type_ok ET t x h"
    P
    using assms by(rule h.mred_known_addrs_typing)

  show ?thesis by unfold_locales(auto dest: red_New_type_match)
qed

lemma J_legal_read_value_typeable:
  assumes wf: "wf_J_prog P"
  and wf_start: "h.wf_start_state P C M vs"
  and legal: "weakly_legal_execution P (h.J_\<E> P C M vs status) (E, ws)"
  and a: "enat a < llength E"
  and read: "action_obs E a = NormalAction (ReadMem ad al v)"
  shows "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
proof -
  note wf
  moreover from wf_start have "h.start_heap_ok" by cases
  moreover from wf wf_start
  have "ts_ok (\<lambda>t x h. \<exists>ET. h.sconf_type_ok ET t x h) (thr (h.J_start_state P C M vs)) h.start_heap"
    by(rule h.J_start_state_sconf_type_ok)
  moreover from wf have "wf_syscls P" by(rule wf_prog_wf_syscls)
  ultimately show ?thesis using legal a read
    by(rule known_addrs_typing'.weakly_legal_read_value_typeable[OF mred_known_addrs_typing'])
qed

end

subsection \<open>Specific part for JMM implementation 2\<close>

abbreviation jmm_J_\<E>
  :: "addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> status \<Rightarrow> (addr \<times> (addr, addr) obs_event action) llist set"
where 
  "jmm_J_\<E> P \<equiv> 
  J_heap_base.J_\<E> addr2thread_id thread_id2addr jmm_spurious_wakeups jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_read jmm_heap_write P"

abbreviation jmm'_J_\<E>
  :: "addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> status \<Rightarrow> (addr \<times> (addr, addr) obs_event action) llist set"
where 
  "jmm'_J_\<E> P \<equiv> 
  J_heap_base.J_\<E> addr2thread_id thread_id2addr jmm_spurious_wakeups jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write P"


lemma jmm_J_heap_conf:
  "J_heap_conf addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_write jmm_hconf P"
by(unfold_locales)

lemma jmm_J_allocated_heap_conf: "J_allocated_heap_conf addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_write jmm_hconf jmm_allocated P"
by(unfold_locales)


lemma jmm_J_allocated_heap_conf':
  "J_allocated_heap_conf' addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr' P) jmm_heap_write jmm_hconf jmm_allocated P"
apply(rule J_allocated_heap_conf'.intro)
apply(unfold jmm_typeof_addr'_conv_jmm_typeof_addr)
apply(unfold_locales)
done


lemma red_heap_read_typedD:
  "J_heap_base.red' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P t e s ta e' s' \<longleftrightarrow>
   J_heap_base.red' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t e s ta e' s' \<and>
  (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
  (is "?lhs1 \<longleftrightarrow> ?rhs1a \<and> ?rhs1b")
  and reds_heap_read_typedD:
  "J_heap_base.reds' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P t es s ta es' s' \<longleftrightarrow>
   J_heap_base.reds' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t es s ta es' s' \<and>
  (\<forall>ad al v T. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
  (is "?lhs2 \<longleftrightarrow> ?rhs2a \<and> ?rhs2b")
proof -
  have "(?lhs1 \<longrightarrow> ?rhs1a \<and> ?rhs1b) \<and> (?lhs2 \<longrightarrow> ?rhs2a \<and> ?rhs2b)"
    apply(induct rule: J_heap_base.red_reds.induct)
    prefer 50 (* RedCallExternal *)
    apply(subst (asm) red_external_heap_read_typed)
    apply(fastforce intro!: J_heap_base.red_reds.RedCallExternal simp add: convert_extTA_def)

    prefer 49 (* RedCall *)
    apply(fastforce dest: J_heap_base.red_reds.RedCall)

    apply(auto intro: J_heap_base.red_reds.intros dest: heap_base.heap_read_typed_into_heap_read heap_base.heap_read_typed_typed dest: heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2] heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD1])
    done
  moreover have "(?rhs1a \<longrightarrow> ?rhs1b \<longrightarrow> ?lhs1) \<and> (?rhs2a \<longrightarrow> ?rhs2b \<longrightarrow> ?lhs2)"
    apply(induct rule: J_heap_base.red_reds.induct)
    prefer 50 (* RedCallExternal *)
    apply simp
    apply(intro strip)
    apply(erule (1) J_heap_base.red_reds.RedCallExternal)
    apply(subst red_external_heap_read_typed, erule conjI)
    apply(blast+)[4]

    prefer 49 (* RedCall *)
    apply(fastforce dest: J_heap_base.red_reds.RedCall)

    apply(auto intro: J_heap_base.red_reds.intros intro!: heap_base.heap_read_typedI dest: heap_base'.addr_loc_type_conv_addr_loc_type[THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1] intro: heap_base'.conf_conv_conf[THEN fun_cong, THEN fun_cong, THEN iffD2])
    done
  ultimately show "?lhs1 \<longleftrightarrow> ?rhs1a \<and> ?rhs1b" "?lhs2 \<longleftrightarrow> ?rhs2a \<and> ?rhs2b" by blast+
qed

lemma if_mred_heap_read_typedD:
  "multithreaded_base.init_fin final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P) t xh ta x'h' \<longleftrightarrow>
   if_heap_read_typed final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P) typeof_addr P t xh ta x'h'"
unfolding multithreaded_base.init_fin.simps
by(subst red_heap_read_typedD) fastforce

lemma J_\<E>_heap_read_typedI:
  "\<lbrakk> E \<in> J_heap_base.J_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P C M vs status;
     \<And>ad al v T. \<lbrakk> NormalAction (ReadMem ad al v) \<in> snd ` lset E; heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<rbrakk> \<Longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T \<rbrakk>
  \<Longrightarrow> E \<in> J_heap_base.J_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P C M vs status"
apply(erule imageE, hypsubst)
apply(rule imageI)
apply(erule multithreaded_base.\<E>.cases, hypsubst)
apply(rule multithreaded_base.\<E>.intros)
apply(subst if_mred_heap_read_typedD[abs_def])
apply(erule if_mthr_Runs_heap_read_typedI)
apply(auto simp add: image_Un lset_lmap[symmetric] lmap_lconcat llist.map_comp o_def split_def simp del: lset_lmap)
done

lemma jmm'_redI:
  "\<lbrakk> J_heap_base.red' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t e s ta e' s'; 
     final_thread.actions_ok (final_thread.init_fin_final final_expr) S t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta e' s'. J_heap_base.red' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t e s ta e' s' \<and> final_thread.actions_ok (final_thread.init_fin_final final_expr) S t ta"
  (is "\<lbrakk> ?red'; ?aok \<rbrakk> \<Longrightarrow> ?concl")
  and jmm'_redsI:
  "\<lbrakk> J_heap_base.reds' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t es s ta es' s';
     final_thread.actions_ok (final_thread.init_fin_final final_expr) S t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta es' s'. J_heap_base.reds' addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t es s ta es' s' \<and> 
     final_thread.actions_ok (final_thread.init_fin_final final_expr) S t ta"
  (is "\<lbrakk> ?reds'; ?aoks \<rbrakk> \<Longrightarrow> ?concls")
proof -
  note [simp del] = split_paired_Ex
    and [simp add] = final_thread.actions_ok_iff heap_base.THE_addr_loc_type heap_base.defval_conf
    and [intro] = jmm_heap_read_typed_default_val

  let ?v = "\<lambda>h a al. default_val (THE T. heap_base.addr_loc_type typeof_addr P h a al T)"

  have "(?red' \<longrightarrow> ?aok \<longrightarrow> ?concl) \<and> (?reds' \<longrightarrow> ?aoks \<longrightarrow> ?concls)"
  proof(induct rule: J_heap_base.red_reds.induct)
    case (23 h a T n i v l) (* RedAAcc *)
    thus ?case by(auto 4 6 intro: J_heap_base.red_reds.RedAAcc[where v="?v h a (ACell (nat (sint i)))"])
  next
    case (35 h a D F v l) (* RedFAcc *)
    thus ?case by(auto 4 5 intro: J_heap_base.red_reds.RedFAcc[where v="?v h a (CField D F)"])
  next
    case RedCASSucceed: (45 h a D F v v' h') (* RedCASSucceed *)
    thus ?case
    proof(cases "v = ?v h a (CField D F)")
      case True
      with RedCASSucceed show ?thesis
        by(fastforce intro: J_heap_base.red_reds.RedCASSucceed[where v="?v h a (CField D F)"])
    next
      case False
      with RedCASSucceed show ?thesis
        by(fastforce intro: J_heap_base.red_reds.RedCASFail[where v''="?v h a (CField D F)"])
    qed
  next
    case RedCASFail: (46 h a D F v'' v v' l)
    thus ?case
    proof(cases "v = ?v h a (CField D F)")
      case True
      with RedCASFail show ?thesis
        by(fastforce intro: J_heap_base.red_reds.RedCASSucceed[where v="?v h a (CField D F)"] jmm_heap_write.intros)
    next
      case False
      with RedCASFail show ?thesis
        by(fastforce intro: J_heap_base.red_reds.RedCASFail[where v''="?v h a (CField D F)"])
    qed
  next
    case (50 s a hU M Ts T D vs ta va h' ta' e' s') (* RedCallExternal *)
    thus ?case
      apply clarify
      apply(drule jmm'_red_externalI, simp)
      apply(auto 4 4 intro: J_heap_base.red_reds.RedCallExternal)
      done
  next
    case (52 e h l V vo ta e' h' l' T) (* BlockRed *)
    thus ?case
      by(clarify)(iprover intro: J_heap_base.red_reds.BlockRed)
  qed(blast intro: J_heap_base.red_reds.intros)+
  thus "\<lbrakk> ?red'; ?aok \<rbrakk> \<Longrightarrow> ?concl" and "\<lbrakk> ?reds'; ?aoks \<rbrakk> \<Longrightarrow> ?concls" by blast+
qed

lemma if_mred_heap_read_not_stuck:
  "\<lbrakk> multithreaded_base.init_fin final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P) t xh ta x'h';
    final_thread.actions_ok (final_thread.init_fin_final final_expr) s t ta \<rbrakk>
  \<Longrightarrow>
  \<exists>ta x'h'. multithreaded_base.init_fin final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P) t xh ta x'h' \<and> final_thread.actions_ok (final_thread.init_fin_final final_expr) s t ta"
apply(erule multithreaded_base.init_fin.cases)
  apply hypsubst
  apply clarify
  apply(drule jmm'_redI)
   apply(simp add: final_thread.actions_ok_iff)
  apply clarify
  apply(subst (2) split_paired_Ex)
  apply(subst (2) split_paired_Ex)
  apply(subst (2) split_paired_Ex)
  apply(rule exI conjI)+
   apply(rule multithreaded_base.init_fin.intros)
   apply(simp)
  apply(simp add: final_thread.actions_ok_iff)
 apply(blast intro: multithreaded_base.init_fin.intros)
apply(blast intro: multithreaded_base.init_fin.intros)
done

lemma if_mredT_heap_read_not_stuck:
  "multithreaded_base.redT (final_thread.init_fin_final final_expr) (multithreaded_base.init_fin final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P)) convert_RA' s tta s'
  \<Longrightarrow> \<exists>tta s'. multithreaded_base.redT (final_thread.init_fin_final final_expr) (multithreaded_base.init_fin final_expr (J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P)) convert_RA' s tta s'"
apply(erule multithreaded_base.redT.cases)
 apply hypsubst
 apply(drule (1) if_mred_heap_read_not_stuck)
 apply(erule exE)+
 apply(rename_tac ta' x'h')
 apply(insert redT_updWs_total)
 apply(erule_tac x="t" in meta_allE)
 apply(erule_tac x="wset s" in meta_allE)
 apply(erule_tac x="\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" in meta_allE)
 apply clarsimp
 apply(rule exI)+
 apply(auto intro!: multithreaded_base.redT.intros)[1]
apply hypsubst
apply(rule exI conjI)+
apply(rule multithreaded_base.redT.redT_acquire)
apply assumption+
done

lemma J_\<E>_heap_read_typedD:
  "E \<in> J_heap_base.J_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_. typeof_addr) (heap_base.heap_read_typed (\<lambda>_. typeof_addr) jmm_heap_read P) jmm_heap_write P C M vs status
  \<Longrightarrow> E \<in> J_heap_base.J_\<E> addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_. typeof_addr) jmm_heap_read jmm_heap_write P C M vs status"
apply(erule imageE, hypsubst)
apply(rule imageI)
apply(erule multithreaded_base.\<E>.cases, hypsubst)
apply(rule multithreaded_base.\<E>.intros)
apply(subst (asm) if_mred_heap_read_typedD[abs_def])
apply(erule if_mthr_Runs_heap_read_typedD)
apply(erule if_mredT_heap_read_not_stuck[where typeof_addr="\<lambda>_. typeof_addr", unfolded if_mred_heap_read_typedD[abs_def]])
done

lemma J_\<E>_typesafe_subset: "jmm'_J_\<E> P C M vs status \<subseteq> jmm_J_\<E> P C M vs status"
unfolding jmm_typeof_addr_def[abs_def]
by(rule subsetI)(erule J_\<E>_heap_read_typedD)

lemma J_legal_typesafe1:
  assumes wfP: "wf_J_prog P"
  and ok: "jmm_wf_start_state P C M vs"
  and legal: "legal_execution P (jmm_J_\<E> P C M vs status) (E, ws)"
  shows "legal_execution P (jmm'_J_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_J_\<E> P C M vs status"
  let ?\<E>' = "jmm'_J_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>"
    and E: "E \<in> ?\<E>" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  let ?J = "J(0 := \<lparr>committed = {}, justifying_exec = justifying_exec (J 1), justifying_ws = justifying_ws (J 1), action_translation = id\<rparr>)"

  from wfP have wf_sys: "wf_syscls P" by(rule wf_prog_wf_syscls)

  from justified have "P \<turnstile> (justifying_exec (J 1), justifying_ws (J 1)) \<surd>"
    by(simp add: justification_well_formed_def)
  with justified have "P \<turnstile> (E, ws) justified_by ?J" by(rule drop_0th_justifying_exec)
  moreover have "range (justifying_exec \<circ> ?J) \<subseteq> ?\<E>'"
  proof
    fix \<xi>
    assume "\<xi> \<in> range (justifying_exec \<circ> ?J)"
    then obtain n where "\<xi> = justifying_exec (?J n)" by auto
    then obtain n where \<xi>: "\<xi> = justifying_exec (J n)" and n: "n > 0" by(auto split: if_split_asm)
    from range \<xi> have "\<xi> \<in> ?\<E>" by auto
    thus "\<xi> \<in> ?\<E>'" unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
    proof(rule J_\<E>_heap_read_typedI)
      fix ad al v T
      assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset \<xi>"
        and adal: "P \<turnstile>jmm ad@al : T"
      from read obtain a where a: "enat a < llength \<xi>" "action_obs \<xi> a = NormalAction (ReadMem ad al v)"
        unfolding lset_conv_lnth by(auto simp add: action_obs_def)
      with J_allocated_heap_conf'.mred_known_addrs_typing'[OF jmm_J_allocated_heap_conf' wfP jmm_start_heap_ok]
        J_heap_conf.J_start_state_sconf_type_ok[OF jmm_J_heap_conf wfP ok]
        wf_sys is_justified_by_imp_is_weakly_justified_by[OF justified wf] range n
      have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
        unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def] \<xi>
        by(rule known_addrs_typing'.read_value_typeable_justifying)
      thus "P \<turnstile>jmm v :\<le> T" using adal
        by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
    qed
  qed
  moreover from E have "E \<in> ?\<E>'"
    unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
  proof(rule J_\<E>_heap_read_typedI)
    fix ad al v T
    assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset E"
      and adal: "P \<turnstile>jmm ad@al : T"
    from read obtain a where a: "enat a < llength E" "action_obs E a = NormalAction (ReadMem ad al v)"
      unfolding lset_conv_lnth by(auto simp add: action_obs_def)
    with jmm_J_allocated_heap_conf' wfP ok legal_imp_weakly_legal_execution[OF legal]
    have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
      unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
      by(rule J_allocated_heap_conf'.J_legal_read_value_typeable)
    thus "P \<turnstile>jmm v :\<le> T" using adal
      by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
  qed
  ultimately show ?thesis using wf unfolding gen_legal_execution.simps by blast
qed

lemma J_weakly_legal_typesafe1:
  assumes wfP: "wf_J_prog P"
  and ok: "jmm_wf_start_state P C M vs"
  and legal: "weakly_legal_execution P (jmm_J_\<E> P C M vs status) (E, ws)"
  shows "weakly_legal_execution P (jmm'_J_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_J_\<E> P C M vs status"
  let ?\<E>' = "jmm'_J_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) weakly_justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>"
    and E: "E \<in> ?\<E>" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  let ?J = "J(0 := \<lparr>committed = {}, justifying_exec = justifying_exec (J 1), justifying_ws = justifying_ws (J 1), action_translation = id\<rparr>)"

  from wfP have wf_sys: "wf_syscls P" by(rule wf_prog_wf_syscls)

  from justified have "P \<turnstile> (justifying_exec (J 1), justifying_ws (J 1)) \<surd>"
    by(simp add: justification_well_formed_def)
  with justified have "P \<turnstile> (E, ws) weakly_justified_by ?J" by(rule drop_0th_weakly_justifying_exec)
  moreover have "range (justifying_exec \<circ> ?J) \<subseteq> ?\<E>'"
  proof
    fix \<xi>
    assume "\<xi> \<in> range (justifying_exec \<circ> ?J)"
    then obtain n where "\<xi> = justifying_exec (?J n)" by auto
    then obtain n where \<xi>: "\<xi> = justifying_exec (J n)" and n: "n > 0" by(auto split: if_split_asm)
    from range \<xi> have "\<xi> \<in> ?\<E>" by auto
    thus "\<xi> \<in> ?\<E>'" unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
    proof(rule J_\<E>_heap_read_typedI)
      fix ad al v T
      assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset \<xi>"
        and adal: "P \<turnstile>jmm ad@al : T"
      from read obtain a where a: "enat a < llength \<xi>" "action_obs \<xi> a = NormalAction (ReadMem ad al v)"
        unfolding lset_conv_lnth by(auto simp add: action_obs_def)
      with J_allocated_heap_conf'.mred_known_addrs_typing'[OF jmm_J_allocated_heap_conf' wfP jmm_start_heap_ok]
        J_heap_conf.J_start_state_sconf_type_ok[OF jmm_J_heap_conf wfP ok]
        wf_sys justified range n
      have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
        unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def] \<xi>
        by(rule known_addrs_typing'.read_value_typeable_justifying)
      thus "P \<turnstile>jmm v :\<le> T" using adal
        by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
    qed
  qed
  moreover from E have "E \<in> ?\<E>'"
    unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
  proof(rule J_\<E>_heap_read_typedI)
    fix ad al v T
    assume read: "NormalAction (ReadMem ad al v) \<in> snd ` lset E"
      and adal: "P \<turnstile>jmm ad@al : T"
    from read obtain a where a: "enat a < llength E" "action_obs E a = NormalAction (ReadMem ad al v)"
      unfolding lset_conv_lnth by(auto simp add: action_obs_def)
    with jmm_J_allocated_heap_conf' wfP ok legal
    have "\<exists>T. P \<turnstile>jmm ad@al : T \<and> P \<turnstile>jmm v :\<le> T"
      unfolding jmm_typeof_addr'_conv_jmm_type_addr[symmetric, abs_def]
      by(rule J_allocated_heap_conf'.J_legal_read_value_typeable)
    thus "P \<turnstile>jmm v :\<le> T" using adal
      by(auto dest: jmm.addr_loc_type_fun[unfolded jmm_typeof_addr_conv_jmm_typeof_addr', unfolded heap_base'.addr_loc_type_conv_addr_loc_type])
  qed
  ultimately show ?thesis using wf unfolding gen_legal_execution.simps by blast
qed

lemma J_legal_typesafe2:
  assumes legal: "legal_execution P (jmm'_J_\<E> P C M vs status) (E, ws)"
  shows "legal_execution P (jmm_J_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_J_\<E> P C M vs status"
  let ?\<E>' = "jmm'_J_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>'"
    and E: "E \<in> ?\<E>'" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  from range E have "range (justifying_exec \<circ> J) \<subseteq> ?\<E>" "E \<in> ?\<E>"
    using J_\<E>_typesafe_subset[of P status C M vs] by blast+
  with justified wf
  show ?thesis by(auto simp add: gen_legal_execution.simps)
qed

lemma J_weakly_legal_typesafe2:
  assumes legal: "weakly_legal_execution P (jmm'_J_\<E> P C M vs status) (E, ws)"
  shows "weakly_legal_execution P (jmm_J_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "jmm_J_\<E> P C M vs status"
  let ?\<E>' = "jmm'_J_\<E> P C M vs status"
  from legal obtain J 
    where justified: "P \<turnstile> (E, ws) weakly_justified_by J"
    and range: "range (justifying_exec \<circ> J) \<subseteq> ?\<E>'"
    and E: "E \<in> ?\<E>'" and wf: "P \<turnstile> (E, ws) \<surd>" by(auto simp add: gen_legal_execution.simps)
  from range E have "range (justifying_exec \<circ> J) \<subseteq> ?\<E>" "E \<in> ?\<E>"
    using J_\<E>_typesafe_subset[of P status C M vs] by blast+
  with justified wf
  show ?thesis by(auto simp add: gen_legal_execution.simps)
qed

theorem J_weakly_legal_typesafe:
  assumes "wf_J_prog P"
  and "jmm_wf_start_state P C M vs"
  shows "weakly_legal_execution P (jmm_J_\<E> P C M vs status) = weakly_legal_execution P (jmm'_J_\<E> P C M vs status)"
apply(rule ext iffI)+
 apply(clarify, erule J_weakly_legal_typesafe1[OF assms])
apply(clarify, erule J_weakly_legal_typesafe2)
done

theorem J_legal_typesafe:
  assumes "wf_J_prog P"
  and "jmm_wf_start_state P C M vs"
  shows "legal_execution P (jmm_J_\<E> P C M vs status) = legal_execution P (jmm'_J_\<E> P C M vs status)"
apply(rule ext iffI)+
 apply(clarify, erule J_legal_typesafe1[OF assms])
apply(clarify, erule J_legal_typesafe2)
done

end
