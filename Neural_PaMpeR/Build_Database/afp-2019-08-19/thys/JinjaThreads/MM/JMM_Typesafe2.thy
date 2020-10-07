(*  Title:      JinjaThreads/MM/JMM_Typesafe2.thy
    Author:     Andreas Lochbihler
*)

section \<open>Specialize type safety for JMM heap implementation 2\<close>

theory JMM_Typesafe2
imports
  JMM_Type2
  JMM_Common
begin

interpretation jmm: heap'
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr' P" jmm_heap_read jmm_heap_write
  for P
by(rule heap'.intro)(unfold jmm_typeof_addr'_conv_jmm_typeof_addr, unfold_locales)

abbreviation jmm_addr_loc_type' :: "'m prog \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>jmm _@_ : _" [50, 50, 50, 50] 51)
  where "jmm_addr_loc_type' P \<equiv> jmm.addr_loc_type TYPE('m) P P"

lemma jmm_addr_loc_type_conv_jmm_addr_loc_type' [simp, heap_independent]:
  "jmm_addr_loc_type P h = jmm_addr_loc_type' P"
by(metis jmm_typeof_addr'_conv_jmm_typeof_addr heap_base'.addr_loc_type_conv_addr_loc_type)

abbreviation jmm_conf' :: "'m prog \<Rightarrow> addr val \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>jmm _ :\<le> _"  [51,51,51] 50)
  where "jmm_conf' P \<equiv> jmm.conf TYPE('m) P P"

lemma jmm_conf_conv_jmm_conf' [simp, heap_independent]:
  "jmm_conf P h = jmm_conf' P"
by (metis jmm_typeof_addr'_conv_jmm_typeof_addr heap_base'.conf_conv_conf)

lemma jmm_heap'': "heap'' addr2thread_id thread_id2addr jmm_allocate (jmm_typeof_addr' P) jmm_heap_write P"
by(unfold_locales)(auto simp add: jmm_typeof_addr'_def jmm_allocate_def split: if_split_asm)

interpretation jmm: heap''
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr' P" jmm_heap_read jmm_heap_write
  for P
by(rule jmm_heap'')

interpretation jmm': heap''
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr' P" "jmm_heap_read_typed P" jmm_heap_write
  for P
by(rule jmm_heap'')

abbreviation jmm_wf_start_state :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> bool"
  where "jmm_wf_start_state P \<equiv> jmm.wf_start_state TYPE('m) P P"


abbreviation if_heap_read_typed ::
  "('x \<Rightarrow> bool) \<Rightarrow> ('l, 't, 'x, 'heap, 'w, ('addr :: addr, 'thread_id) obs_event) semantics
   \<Rightarrow> ('addr \<Rightarrow> htype option)
   \<Rightarrow> 'm prog \<Rightarrow> ('l, 't, status \<times> 'x, 'heap, 'w, ('addr, 'thread_id) obs_event action) semantics"
where
  "\<And>final. if_heap_read_typed final r typeof_addr P t xh ta x'h' \<equiv>
   multithreaded_base.init_fin final r t xh ta x'h' \<and>
  (\<forall>ad al v T. NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"

lemma if_mthr_Runs_heap_read_typedI:
  fixes final and r :: "('addr, 't, 'x, 'heap, 'w, ('addr :: addr, 'thread_id) obs_event) semantics"
  assumes "trsys.Runs (multithreaded_base.redT (final_thread.init_fin_final final) (multithreaded_base.init_fin final r) (map NormalAction \<circ> convert_RA)) s \<xi>"
  (is "trsys.Runs ?redT _ _")
  and "\<And>ad al v T. \<lbrakk> NormalAction (ReadMem ad al v) \<in> lset (lconcat (lmap (llist_of \<circ> obs_a \<circ> snd) \<xi>)); heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<rbrakk> \<Longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T"
  (is "\<And>ad al v T. \<lbrakk> ?obs \<xi> ad al v; ?adal ad al T \<rbrakk> \<Longrightarrow> ?conf v T")
  shows "trsys.Runs (multithreaded_base.redT (final_thread.init_fin_final final) (if_heap_read_typed final r typeof_addr P) (map NormalAction \<circ> convert_RA)) s \<xi>"
  (is "trsys.Runs ?redT' _ _")
using assms
proof(coinduction arbitrary: s \<xi> rule: trsys.Runs.coinduct[consumes 1, case_names Runs, case_conclusion Runs Stuck Step])
  case (Runs s \<xi>)
  let ?read = "\<lambda>\<xi>. (\<forall>ad al v T. ?obs \<xi> ad al v \<longrightarrow> ?adal ad al T \<longrightarrow> ?conf v T)"
  note read = Runs(2)
  from Runs(1) show ?case
  proof(cases rule: trsys.Runs.cases[consumes 1, case_names Stuck Step])
    case (Stuck S)
    { fix tta s'
      from \<open>\<not> ?redT S tta s'\<close> have "\<not> ?redT' S tta s'"
        by(rule contrapos_nn)(fastforce simp add: multithreaded_base.redT.simps) }
    hence ?Stuck using \<open>\<xi> = LNil\<close> unfolding \<open>s = S\<close> by blast
    thus ?thesis ..
  next
    case (Step S s' ttas tta)
    from \<open>\<xi> = LCons tta ttas\<close> read
    have read1: "\<And>ad al v T. \<lbrakk> NormalAction (ReadMem ad al v) \<in> set \<lbrace>snd tta\<rbrace>\<^bsub>o\<^esub>; ?adal ad al T \<rbrakk> \<Longrightarrow> ?conf v T"
      and read2: "?read ttas" by(auto simp add: o_def)
    from \<open>?redT S tta s'\<close> read1
    have "?redT' S tta s'" by(fastforce simp add: multithreaded_base.redT.simps)
    hence ?Step using Step read2 \<open>s = S\<close> by blast
    thus ?thesis ..
  qed
qed

lemma if_mthr_Runs_heap_read_typedD:
  fixes final and r :: "('addr, 't, 'x, 'heap, 'w, ('addr :: addr, 'thread_id) obs_event) semantics"
  assumes Runs': "trsys.Runs (multithreaded_base.redT (final_thread.init_fin_final final) (if_heap_read_typed final r typeof_addr P) (map NormalAction \<circ> convert_RA)) s \<xi>"
  (is "?Runs' s \<xi>")
  and stuck: "\<And>ttas s' tta s''. \<lbrakk>
    multithreaded_base.RedT (final_thread.init_fin_final final) (if_heap_read_typed final r typeof_addr P) (map NormalAction \<circ> convert_RA) s ttas s';
    multithreaded_base.redT (final_thread.init_fin_final final) (multithreaded_base.init_fin final r) (map NormalAction \<circ> convert_RA) s' tta s'' \<rbrakk>
  \<Longrightarrow> \<exists>tta s''. multithreaded_base.redT (final_thread.init_fin_final final) (if_heap_read_typed final r typeof_addr P) (map NormalAction \<circ> convert_RA) s' tta s''"
  (is "\<And>ttas s' tta s''. \<lbrakk> ?RedT' s ttas s'; ?redT s' tta s'' \<rbrakk> \<Longrightarrow> \<exists>tta s''. ?redT' s' tta s''")
  shows "trsys.Runs (multithreaded_base.redT (final_thread.init_fin_final final) (multithreaded_base.init_fin final r) (map NormalAction \<circ> convert_RA)) s \<xi>"
  (is "?Runs s \<xi>")
proof -
  define s' where "s' = s"
  with Runs' have "\<exists>ttas. ?RedT' s ttas s' \<and> ?Runs' s' \<xi>"
    by(auto simp add: multithreaded_base.RedT_def o_def)
  thus "?Runs s' \<xi>"
  proof(coinduct rule: trsys.Runs.coinduct[consumes 1, case_names Runs, case_conclusion Runs Stuck Step])
    case (Runs s' \<xi>)
    then obtain ttas where RedT': "?RedT' s ttas s'"
      and Runs': "?Runs' s' \<xi>" by blast
    from Runs' show ?case
    proof(cases rule: trsys.Runs.cases[consumes 1, case_names Stuck Step])
      case (Stuck S)
      have "\<And>tta s''. \<not> ?redT s' tta s''"
      proof
        fix tta s''
        assume "?redT s' tta s''"
        from stuck[OF RedT' this] 
        obtain tta s'' where "?redT' s' tta s''" by blast
        with Stuck(3)[of tta s''] show False
          unfolding \<open>s' = S\<close> by contradiction
      qed
      with Stuck(1-2) have ?Stuck by simp
      thus ?thesis by(rule disjI1)
    next
      case (Step S s'' \<xi>' tta)
      note Step = Step(2-)[folded \<open>s' = S\<close>]
      from \<open>?redT' s' tta s''\<close> have "?redT s' tta s''"
        by(fastforce simp add: multithreaded_base.redT.simps)
      moreover from RedT' \<open>?redT' s' tta s''\<close>
      have "?RedT' s (ttas @ [tta]) s''"
        unfolding multithreaded_base.RedT_def by(rule rtrancl3p_step)
      ultimately have ?Step using \<open>\<xi> = LCons tta \<xi>'\<close> \<open>?Runs' s'' \<xi>'\<close> by blast
      thus ?thesis by(rule disjI2)
    qed
  qed
qed

lemma heap_copy_loc_heap_read_typed:
  "heap_base.heap_copy_loc (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write a a' al h obs h' \<longleftrightarrow>
  heap_base.heap_copy_loc heap_read heap_write a a' al h obs h' \<and>
  (\<forall>ad al v T. ReadMem ad al v \<in> set obs \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(auto elim!: heap_base.heap_copy_loc.cases intro!: heap_base.heap_copy_loc.intros dest: heap_base.heap_read_typed_into_heap_read heap_base.heap_read_typed_typed intro: heap_base.heap_read_typedI simp add: heap_base'.addr_loc_type_conv_addr_loc_type heap_base'.conf_conv_conf)

lemma heap_copies_heap_read_typed:
  "heap_base.heap_copies (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write a a' als h obs h' \<longleftrightarrow>
  heap_base.heap_copies heap_read heap_write a a' als h obs h' \<and>
  (\<forall>ad al v T. ReadMem ad al v \<in> set obs \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    by(induct rule: heap_base.heap_copies.induct[consumes 1])(auto intro!: heap_base.heap_copies.intros simp add: heap_copy_loc_heap_read_typed)
next
  assume ?rhs thus ?lhs
    by(rule conjE)(induct rule: heap_base.heap_copies.induct[consumes 1], auto intro!: heap_base.heap_copies.intros simp add: heap_copy_loc_heap_read_typed)
qed

lemma heap_clone_heap_read_typed:
  "heap_base.heap_clone allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P a h h' obs \<longleftrightarrow>
  heap_base.heap_clone allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P a h h' obs \<and>
  (\<forall>ad al v T obs' a'. obs = \<lfloor>(obs', a')\<rfloor> \<longrightarrow> ReadMem ad al v \<in> set obs' \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(auto elim!: heap_base.heap_clone.cases intro: heap_base.heap_clone.intros simp add: heap_copies_heap_read_typed)

lemma red_external_heap_read_typed:
  "heap_base.red_external addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P t h a M vs ta va h' \<longleftrightarrow>
   heap_base.red_external addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t h a M vs ta va h' \<and>
  (\<forall>ad al v T obs' a'. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(auto elim!: heap_base.red_external.cases intro: heap_base.red_external.intros simp add: heap_clone_heap_read_typed)

lemma red_external_aggr_heap_read_typed:
  "(ta, va, h') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) (heap_base.heap_read_typed (\<lambda>_ :: 'heap. typeof_addr) heap_read P) heap_write P t h a M vs \<longleftrightarrow>
   (ta, va, h') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate (\<lambda>_ :: 'heap. typeof_addr) heap_read heap_write P t h a M vs \<and>
  (\<forall>ad al v T obs' a'. ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> heap_base'.addr_loc_type TYPE('heap) typeof_addr P ad al T \<longrightarrow> heap_base'.conf TYPE('heap) typeof_addr P v T)"
by(auto simp add: heap_base.red_external_aggr_def heap_clone_heap_read_typed split del: if_split split: if_split_asm)



lemma jmm'_heap_copy_locI: 
  "\<exists>obs h'. heap_base.heap_copy_loc (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write a a' al h obs h'"
by(auto intro!: heap_base.heap_copy_loc.intros jmm_heap_read_typed_default_val intro: jmm_heap_write.intros)

lemma jmm'_heap_copiesI:
  "\<exists>obs :: (addr, 'thread_id) obs_event list.
   \<exists>h'. heap_base.heap_copies (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write a a' als h obs h'"
proof(induction als arbitrary: h)
  case Nil
  thus ?case by(blast intro: heap_base.heap_copies.intros)
next
  case (Cons al als)
  from jmm'_heap_copy_locI[of typeof_addr P a a' al h]
  obtain ob :: "(addr, 'thread_id) obs_event list" and h'
    where "heap_base.heap_copy_loc (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write a a' al h ob h'" 
    by blast
  with Cons.IH[of h'] show ?case
    by(auto 4 4 intro: heap_base.heap_copies.intros)
qed

lemma jmm'_heap_cloneI:
  fixes obsa :: "((addr, 'thread_id) obs_event list \<times> addr) option"
  assumes "heap_base.heap_clone allocate typeof_addr jmm_heap_read jmm_heap_write P h a h' obsa"
  shows "\<exists>h'. \<exists>obsa :: ((addr, 'thread_id) obs_event list \<times> addr) option. 
       heap_base.heap_clone allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P h a h' obsa"
using assms
proof(cases rule: heap_base.heap_clone.cases[consumes 1, case_names Fail Obj Arr])
  case Fail
  thus ?thesis by(blast intro: heap_base.heap_clone.intros)
next
  case (Obj C h' a' FDTs obs h'')
  with jmm'_heap_copiesI[of typeof_addr P a a' "map (\<lambda>((F, D), Tfm). CField D F) FDTs" h']
  show ?thesis by(blast intro: heap_base.heap_clone.intros)
next
  case (Arr T n h' a' FDTs obs h'')
  with jmm'_heap_copiesI[of typeof_addr P a a' "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"]
  show ?thesis by(blast intro: heap_base.heap_clone.intros)
qed

lemma jmm'_red_externalI:
  "\<And>final.
  \<lbrakk> heap_base.red_external addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t h a M vs ta va h';
     final_thread.actions_ok final s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta va h'. heap_base.red_external addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t h a M vs ta va h' \<and> final_thread.actions_ok final s t ta"
proof(erule heap_base.red_external.cases, goal_cases)
  case 19 (* RedClone *)
  thus ?case apply -
    apply(drule jmm'_heap_cloneI, clarify)
    apply(rename_tac obsa', case_tac obsa')
    by(auto 4 4 intro: heap_base.red_external.intros simp add: final_thread.actions_ok_iff simp del: split_paired_Ex)
next
  case 20 (* RedCloneFail *)
  thus ?case apply -
    apply(drule jmm'_heap_cloneI, clarify)
    apply(rename_tac obsa', case_tac obsa')
    by(auto 4 4 intro: heap_base.red_external.intros simp add: final_thread.actions_ok_iff simp del: split_paired_Ex)
qed(blast intro: heap_base.red_external.intros)+

lemma red_external_aggr_heap_read_typedI:
  "\<And>final.
  \<lbrakk> (ta, vah') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr jmm_heap_read jmm_heap_write P t h a M vs;
    final_thread.actions_ok final s t ta
  \<rbrakk>
  \<Longrightarrow> \<exists>ta vah'. (ta, vah') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_base.heap_read_typed typeof_addr jmm_heap_read P) jmm_heap_write P t h a M vs \<and> final_thread.actions_ok final s t ta"
apply(simp add: heap_base.red_external_aggr_def split_beta split del: if_split split: if_split_asm del: split_paired_Ex)
apply(auto simp del: split_paired_Ex)
 apply(drule jmm'_heap_cloneI)
 apply(clarify)
 apply(rename_tac obsa, case_tac obsa)
  apply(force simp add: final_thread.actions_ok_iff del: disjCI intro: disjI1 disjI2 simp del: split_paired_Ex)
 apply(force simp add: final_thread.actions_ok_iff del: disjCI intro: disjI1 disjI2 simp del: split_paired_Ex)
apply(drule jmm'_heap_cloneI)
apply clarify
apply(rename_tac obsa, case_tac obsa)
 apply(force simp add: final_thread.actions_ok_iff del: disjCI intro: disjI1 disjI2 simp del: split_paired_Ex)
apply(force simp add: final_thread.actions_ok_iff del: disjCI intro: disjI1 disjI2 simp del: split_paired_Ex)
done

end
