theory JVMInterpretation imports JVMCFG "../StaticInter/CFGExit" begin

section \<open>Instatiation of the \<open>CFG\<close> locale\<close>

abbreviation sourcenode :: "cfg_edge \<Rightarrow> cfg_node"
  where "sourcenode e \<equiv> fst e"

abbreviation targetnode :: "cfg_edge \<Rightarrow> cfg_node"
  where "targetnode e \<equiv> snd(snd e)"

abbreviation kind :: "cfg_edge \<Rightarrow> (var, val, cname \<times> mname \<times> pc, cname \<times> mname) edge_kind"
  where "kind e \<equiv> fst(snd e)"

definition valid_edge :: "jvm_method \<Rightarrow> cfg_edge \<Rightarrow> bool"
  where "valid_edge P e \<equiv> P \<turnstile> (sourcenode e) -(kind e)\<rightarrow> (targetnode e)"

fun methods :: "cname \<Rightarrow> JVMInstructions.jvm_method mdecl list \<Rightarrow> ((cname \<times> mname) \<times> var list \<times> var list) list"
  where "methods C [] = []"
  | "methods C ((M, Ts, T, mb) # ms)
  = ((C, M), Heap # (map Local [0..<Suc (length Ts)]), [Heap, Stack 0, Exception]) # (methods C ms)"

fun procs :: "jvm_prog \<Rightarrow> ((cname \<times> mname) \<times> var list \<times> var list) list"
  where "procs [] = []"
  |"procs ((C, D, fs, ms) # P) = (methods C ms) @ (procs P)"

lemma in_set_methodsI: "map_of ms M = \<lfloor>(Ts, T, mxs, mxl\<^sub>0, is, xt)\<rfloor>
  \<Longrightarrow> ((C', M), Heap # map Local [0..<length Ts] @ [Local (length Ts)], [Heap, Stack 0, Exception])
  \<in> set (methods C' ms)"
  by (induct rule: methods.induct) (auto split: if_split_asm)

lemma in_methods_in_msD: "((C, M), ins, outs) \<in> set (methods D ms)
  \<Longrightarrow> M \<in> set (map fst ms) \<and> D = C"
  by (induct ms) auto

lemma in_methods_in_msD': "((C, M), ins, outs) \<in> set (methods D ms)
  \<Longrightarrow> \<exists>Ts T mb. (M, Ts, T, mb) \<in> set ms
  \<and> D = C
  \<and> ins = Heap # (map Local [0..<Suc (length Ts)])
  \<and> outs = [Heap, Stack 0, Exception]"
  by (induct rule: methods.induct) fastforce+

lemma in_set_methodsE:
  assumes "((C, M), ins, outs) \<in> set (methods D ms)"
  obtains Ts T mb
  where "(M, Ts, T, mb) \<in> set ms"
  and "D = C"
  and "ins = Heap # (map Local [0..<Suc (length Ts)])"
  and "outs = [Heap, Stack 0, Exception]"
using assms
by (induct ms) fastforce+

lemma in_set_procsI:
  assumes sees: "P \<turnstile> D sees M: Ts\<rightarrow>T = mb in D"
  and ins_def: "ins = Heap # map Local [0..<Suc (length Ts)]"
  and outs_def: "outs = [Heap, Stack 0, Exception]"
  shows "((D, M), ins, outs) \<in> set (procs P)"
proof -
  from sees obtain D' fs ms where "map_of P D = \<lfloor>(D', fs, ms)\<rfloor>" and "map_of ms M = \<lfloor>(Ts, T, mb)\<rfloor>"
    by (fastforce dest: visible_method_exists simp: class_def)
  hence "(D, D', fs, ms) \<in> set P"
    by -(drule map_of_SomeD)
  thus ?thesis
  proof (induct P)
    case Nil thus ?case by simp
  next
    case (Cons Class P)
    with ins_def outs_def \<open>map_of ms M = \<lfloor>(Ts, T, mb)\<rfloor>\<close> show ?case
      by (cases Class, cases mb) (auto intro: in_set_methodsI)
  qed
qed

lemma distinct_methods: "distinct (map fst ms) \<Longrightarrow> distinct (map fst (methods C ms))"
proof (induct ms)
  case Nil thus ?case by simp
next
  case (Cons M ms)
  thus ?case
    by (cases M) (auto dest: in_methods_in_msD)
qed

lemma in_set_procsD:
  "((C, M), ins, out) \<in> set (procs P) \<Longrightarrow> \<exists>D fs ms. (C, D, fs, ms) \<in> set P \<and> M \<in> set (map fst ms)"
proof (induct P)
  case Nil thus ?case by simp
next
  case (Cons Class P)
  thus ?case
    by (cases Class) (fastforce dest: in_methods_in_msD intro: rev_image_eqI)
qed

lemma in_set_procsE':
  assumes "((C, M), ins, outs) \<in> set (procs P)"
  obtains D fs ms Ts T mb 
  where "(C, D, fs, ms) \<in> set P"
  and "(M, Ts, T, mb) \<in> set ms"
  and "ins = Heap # (map (\<lambda>n. Local n) [0..<Suc (length Ts)])"
  and "outs = [Heap, Stack 0, Exception]"
  using assms
  by (induct P) (fastforce elim: in_set_methodsE)+
 
lemma distinct_Local_vars [simp]: "distinct (map Local [0..<n])"
  by (induct n) auto

lemma distinct_Stack_vars [simp]: "distinct (map Stack [0..<n])"
  by (induct n) auto

inductive_set get_return_edges :: "wf_jvmprog \<Rightarrow> cfg_edge \<Rightarrow> cfg_edge set"
  for P :: "wf_jvmprog" 
  and a :: "cfg_edge"
  where
  "kind a = Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D, M')\<^esub>paramDefs
  \<Longrightarrow> ((D, M', None, Return),
  (\<lambda>(s, ret). ret = (C, M, pc))\<hookleftarrow>\<^bsub>(D, M')\<^esub>(\<lambda>s s'. s'(Heap := s Heap, Exception := s Exception,
                                                Stack (stkLength (P, C, M) (Suc pc) - 1) := s (Stack 0))),
      (C, M, \<lfloor>pc\<rfloor>, Return)) \<in> (get_return_edges P a)"

lemma get_return_edgesE [elim!]:
  assumes "a \<in> get_return_edges P a'"
  obtains Q C M pc D M' paramDefs where
  "kind a' = Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D, M')\<^esub>paramDefs"
  and "a = ((D, M', None, Return),
  (\<lambda>(s, ret). ret = (C, M, pc))\<hookleftarrow>\<^bsub>(D, M')\<^esub>(\<lambda>s s'. s'(Heap := s Heap, Exception := s Exception,
  Stack (stkLength (P, C, M) (Suc pc) - 1) := s (Stack 0))),
  (C, M, \<lfloor>pc\<rfloor>, Return))"
  using assms
  by -(cases a, cases a', clarsimp, erule get_return_edges.cases, fastforce)

lemma distinct_class_names: "distinct_fst (PROG P)"
  using wf_jvmprog_is_wf_typ [of P]
  by (clarsimp simp: wf_jvm_prog_phi_def wf_prog_def)

lemma distinct_method_names:
  "class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor> \<Longrightarrow> distinct_fst ms"
  using wf_jvmprog_is_wf_typ [of P]
  unfolding wf_jvm_prog_phi_def
  by (fastforce dest: class_wf simp: wf_cdecl_def)

lemma distinct_fst_is_distinct_fst: "distinct_fst = BasicDefs.distinct_fst"
  by (simp add: distinct_fst_def BasicDefs.distinct_fst_def)

lemma ClassMain_not_in_set_PROG [dest!]: "(ClassMain P, D, fs, ms) \<in> set (PROG P) \<Longrightarrow> False"
  using distinct_class_names [of P] ClassMain_is_no_class [of P]
by (fastforce intro: map_of_SomeI simp: class_def)

lemma in_set_procsE:
  assumes "((C, M), ins, outs) \<in> set (procs (PROG P))"
  obtains D fs ms Ts T mb 
  where "class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>"
  and "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = mb in C"
  and "ins = Heap # (map (\<lambda>n. Local n) [0..<Suc (length Ts)])"
  and "outs = [Heap, Stack 0, Exception]"
proof -
  from \<open>((C, M), ins, outs) \<in> set (procs (PROG P))\<close>
  obtain D fs ms Ts T mxs mxl\<^sub>0 "is" xt
    where "(C, D, fs, ms) \<in> set (PROG P)"
    and "(M, Ts, T, mxs, mxl\<^sub>0, is, xt) \<in> set ms"
    and "ins = Heap # (map (\<lambda>n. Local n) [0..<Suc (length Ts)])"
    and "outs = [Heap, Stack 0, Exception]"
    by (fastforce elim: in_set_procsE')
  moreover from \<open>(C, D, fs, ms) \<in> set (PROG P)\<close> distinct_class_names [of P]
  have "class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>"
    by (fastforce intro: map_of_SomeI simp: class_def)
  moreover from wf_jvmprog_is_wf_typ [of P]
    \<open>(M, Ts, T, mxs, mxl\<^sub>0, is, xt) \<in> set ms\<close> \<open>(C, D, fs, ms) \<in> set (PROG P)\<close>
  have "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    by (fastforce intro: mdecl_visible simp: wf_jvm_prog_phi_def)
  ultimately show ?thesis using that by blast
qed

declare has_method_def [simp]

interpretation JVMCFG_Interpret:
  CFG "sourcenode" "targetnode" "kind" "valid_edge (P, C0, Main)"
  "(ClassMain P, MethodMain P, None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges P"
  "((ClassMain P, MethodMain P),[],[]) # procs (PROG P)" "(ClassMain P, MethodMain P)"
  for P C0 Main
proof (unfold_locales)
  fix e
  assume "valid_edge (P, C0, Main) e"
    and "targetnode e = (ClassMain P, MethodMain P, None, Enter)"
  thus False
    by (auto simp: valid_edge_def)(erule JVMCFG.cases, auto)+
next
  show "(\<lambda>(C, M, pc, type). (C, M)) (ClassMain P, MethodMain P, None, Enter) =
    (ClassMain P, MethodMain P)"
    by simp
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and "sourcenode a = (ClassMain P, MethodMain P, None, Enter)"
  thus False
    by (auto simp: valid_edge_def) (erule JVMCFG.cases, auto)
next
  fix a a'
  assume "valid_edge (P, C0, Main) a"
    and "valid_edge (P, C0, Main) a'"
    and "sourcenode a = sourcenode a'"
    and "targetnode a = targetnode a'"
  thus "a = a'"
    by (cases a, cases a') (fastforce simp: valid_edge_def dest: JVMCFG_edge_det)
next
  fix a Q r f
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>(ClassMain P, MethodMain P)\<^esub>f"
  thus False
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)    
next
  fix a Q' f'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q'\<hookleftarrow>\<^bsub>(ClassMain P, MethodMain P)\<^esub>f'"
  thus False
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)+
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  then obtain C M pc nt C' M' pc' nt'
    where "(P, C0, Main) \<turnstile> (C, M, pc, nt) -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> (C', M', pc', nt')"
    by (cases a) (clarsimp simp: valid_edge_def)
  thus "\<exists>ins outs.
    (p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
  proof cases
    case (Main_Call T mxs mxl0 "is" xt initParams)
    hence "((C', Main), [Heap, Local 0], [Heap, Stack 0, Exception]) \<in> set (procs (PROG P))"
      and "p = (C', Main)"
      by (auto intro: in_set_procsI dest: sees_method_idemp)
    thus ?thesis by fastforce
  next
    case (CFG_Invoke_Call _ n _ _ _ Ts)
    hence "((C', M'), Heap # map (\<lambda>n. Local n) [0..<Suc (length Ts)],
      [Heap, Stack 0, Exception]) \<in> set (procs (PROG P))"
      and "p = (C',M')"
      by (auto intro: in_set_procsI dest: sees_method_idemp)
    thus ?thesis by fastforce
  qed simp_all
next
  fix a
  assume "valid_edge (P, C0, Main) a" and "intra_kind (kind a)"
  thus "(\<lambda>(C, M, pc, type). (C, M)) (sourcenode a) =
    (\<lambda>(C, M, pc, type). (C, M)) (targetnode a)"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto simp: intra_kind_def)
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  thus "(\<lambda>(C, M, pc, type). (C, M)) (targetnode a) = p"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)
next
  fix a Q' p f'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  thus "(\<lambda>(C, M, pc, type). (C, M)) (sourcenode a) = p"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  thus "\<forall>a'. valid_edge (P, C0, Main) a' \<and> targetnode a' = targetnode a
    \<longrightarrow> (\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
    by (cases a, clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)+
next
  fix a Q' p f'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  thus "\<forall>a'. valid_edge (P, C0, Main) a' \<and> sourcenode a' = sourcenode a
    \<longrightarrow> (\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)"
    by (cases a, clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)+
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  then have "\<exists>a'. a' \<in> get_return_edges P a"
    by (cases p, cases r) (fastforce intro: get_return_edges.intros)
  then show "get_return_edges P a \<noteq> {}"
    by (simp only: ex_in_conv) simp
next
  fix a a'
  assume "valid_edge (P, C0, Main) a" "a' \<in> get_return_edges P a"
  then obtain Q C M pc D M' paramDefs
    where "(P, C0, Main) \<turnstile> sourcenode a -Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D, M')\<^esub>paramDefs\<rightarrow> targetnode a"
    and "kind a = Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D, M')\<^esub>paramDefs"
    and a'_def: "a' = ((D, M', None, nodeType.Return),
    \<lambda>(s, ret).
      ret = (C, M, pc)\<hookleftarrow>\<^bsub>(D, M')\<^esub>\<lambda>s s'. s'(Heap := s Heap, Exception := s Exception,
                           Stack (stkLength (P, C, M) (Suc pc) - 1) := s (Stack 0)),
    C, M, \<lfloor>pc\<rfloor>, nodeType.Return)"
    by (fastforce simp: valid_edge_def)
  thus "valid_edge (P, C0, Main) a'"
  proof cases
    case (Main_Call T mxs mxl0 "is" xt D')
    hence "D = D'" and "M' = Main"
      by simp_all
    with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)\<close>
      \<open>PROG P \<turnstile> C0 sees Main: []\<rightarrow>T = (mxs, mxl0, is, xt) in D'\<close>
    have "(P, C0, Main) \<turnstile> \<Rightarrow>(D, M', None, Enter)"
      by -(rule reachable_step, fastforce, fastforce intro: JVMCFG_reachable.Main_Call)
    hence "(P, C0, Main) \<turnstile> \<Rightarrow>(D, M', None, nodeType.Return)"
      by -(rule reachable_step, fastforce, fastforce intro: JVMCFG_reachable.Method_LFalse)
    with a'_def Main_Call show ?thesis
      by (fastforce intro: CFG_Return_from_Method JVMCFG_reachable.Main_Call simp: valid_edge_def)
  next
    case (CFG_Invoke_Call _ _ _ M'' _ _ _ _ _ _ _ _ _ _ D')
    hence "D = D'" and "M' = M''"
      by simp_all
    with CFG_Invoke_Call
    have "(P, C0, Main) \<turnstile> \<Rightarrow>(D, M', None, Enter)"
      by -(rule reachable_step, fastforce, fastforce intro: JVMCFG_reachable.CFG_Invoke_Call)
    hence "(P, C0, Main) \<turnstile> \<Rightarrow>(D, M', None, nodeType.Return)"
      by -(rule reachable_step, fastforce, fastforce intro: JVMCFG_reachable.Method_LFalse)
    with a'_def CFG_Invoke_Call show ?thesis
      by (fastforce intro: CFG_Return_from_Method JVMCFG_reachable.CFG_Invoke_Call
        simp: valid_edge_def)
  qed simp_all
next
  fix a a'
  assume "valid_edge (P, C0, Main) a" and "a' \<in> get_return_edges P a"
  thus "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    by clarsimp
next
  fix a Q r p fs a'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges P a"
  thus "\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by clarsimp
next
  fix a Q' p f'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  show "\<exists>!a'. valid_edge (P, C0, Main) a' \<and>
                (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges P a'"
  proof (rule ex_ex1I)
    from \<open>valid_edge (P, C0, Main) a\<close>
    have "(P, C0, Main) \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by (clarsimp simp: valid_edge_def)
    from this \<open>kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
    show "\<exists>a'. valid_edge (P, C0, Main) a' \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)
      \<and> a \<in> get_return_edges P a'"
      by cases (cases a, fastforce intro: get_return_edges.intros[simplified] simp: valid_edge_def)+
  next
    fix a' a''
    assume "valid_edge (P, C0, Main) a'
      \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges P a'"
       and "valid_edge (P, C0, Main) a''
      \<and> (\<exists>Q r fs. kind a'' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges P a''"
    thus "a' = a''"
      by (cases a', cases a'', clarsimp simp: valid_edge_def)
    (erule JVMCFG.cases, simp_all, clarsimp? )+
  qed
next
  fix a a'
  assume "valid_edge (P, C0, Main) a" and "a' \<in> get_return_edges P a"
  thus "\<exists>a''. valid_edge (P, C0, Main) a'' \<and>
    sourcenode a'' = targetnode a \<and>
    targetnode a'' = sourcenode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto intro: JVMCFG_reachable.intros)
next
  fix a a'
  assume "valid_edge (P, C0, Main) a" and "a' \<in> get_return_edges P a"
  thus "\<exists>a''. valid_edge (P, C0, Main) a'' \<and>
    sourcenode a'' = sourcenode a \<and>
    targetnode a'' = targetnode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto intro: JVMCFG_reachable.intros)
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  hence call: "(P, C0, Main) \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by (clarsimp simp: valid_edge_def)
  show "\<exists>!a'. valid_edge (P, C0, Main) a' \<and>
    sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
  proof (rule ex_ex1I)
    from call
    show "\<exists>a'. valid_edge (P, C0, Main) a' \<and> sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
      by cases (fastforce intro: JVMCFG_reachable.intros simp: intra_kind_def valid_edge_def)+
  next
    fix a' a''
    assume "valid_edge (P, C0, Main) a' \<and> sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
      and "valid_edge (P, C0, Main) a'' \<and> sourcenode a'' = sourcenode a \<and> intra_kind (kind a'')"
    with call show "a' = a''"
      by (cases a, cases a', cases a'', clarsimp simp: valid_edge_def intra_kind_def)
    (erule JVMCFG.cases, simp_all, clarsimp?)+
  qed
next
  fix a Q' p f'
  assume "valid_edge (P, C0, Main) a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  hence return: "(P, C0, Main) \<turnstile> sourcenode a -Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rightarrow> targetnode a"
    by (clarsimp simp: valid_edge_def)
  show "\<exists>!a'. valid_edge (P, C0, Main) a' \<and>
    targetnode a' = targetnode a \<and> intra_kind (kind a')"
  proof (rule ex_ex1I)
    from return
    show "\<exists>a'. valid_edge (P, C0, Main) a' \<and> targetnode a' = targetnode a \<and> intra_kind (kind a')"
    proof cases
      case (CFG_Return_from_Method C M C' M' pc' Q'' ps Q stateUpdate)
      hence [simp]: "Q = Q'" and [simp]: "p = (C, M)" and [simp]: "f' = stateUpdate"
        by simp_all
      from \<open>(P, C0, Main) \<turnstile> (C', M', \<lfloor>pc'\<rfloor>, Normal) -Q'':(C', M', pc')\<hookrightarrow>\<^bsub>(C, M)\<^esub>ps\<rightarrow> (C, M, None, Enter)\<close>
      have invoke_reachable: "(P, C0, Main) \<turnstile> \<Rightarrow>(C', M', \<lfloor>pc'\<rfloor>, Normal)"
        by -(drule sourcenode_reachable)
      show ?thesis
      proof (cases "C' = ClassMain P")
        case True
        with invoke_reachable CFG_Return_from_Method show ?thesis
          by -(erule JVMCFG.cases, simp_all,
            fastforce intro: Main_Call_LFalse simp: valid_edge_def intra_kind_def)
      next
        case False
        with invoke_reachable CFG_Return_from_Method show ?thesis
          by -(erule JVMCFG.cases, simp_all,
            fastforce intro: CFG_Invoke_False simp: valid_edge_def intra_kind_def)
      qed
    qed simp_all
  next
    fix a' a''
    assume "valid_edge (P, C0, Main) a' \<and> targetnode a' = targetnode a \<and> intra_kind (kind a')"
      and "valid_edge (P, C0, Main) a'' \<and> targetnode a'' = targetnode a \<and> intra_kind (kind a'')"
    with return show "a' = a''"
      by (cases, auto, cases a, cases a', cases a'', clarsimp simp: valid_edge_def intra_kind_def)
    (erule JVMCFG.cases, simp_all, clarsimp?)+
  qed
next
  fix a a' Q\<^sub>1 r\<^sub>1 p fs\<^sub>1 Q\<^sub>2 r\<^sub>2 fs\<^sub>2
  assume "valid_edge (P, C0, Main) a" and "valid_edge (P, C0, Main) a'"
    and "kind a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1" and "kind a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2"
  thus "targetnode a = targetnode a'"
    by (cases a, cases a', clarsimp simp: valid_edge_def)
  (erule JVMCFG.cases, simp_all, clarsimp?)+
next
  from distinct_method_names [of P] distinct_class_names [of P]
  have "\<And>C D fs ms. (C, D, fs, ms) \<in> set (PROG P) \<Longrightarrow> distinct_fst ms"
    by (fastforce intro: map_of_SomeI simp: class_def)
  moreover {
    fix P
    assume "distinct_fst (P :: jvm_prog)"
      and "\<And>C D fs ms. (C, D, fs, ms) \<in> set P \<Longrightarrow> distinct_fst ms"
    hence "distinct_fst (procs P)"
      by (induct P, simp)
    (fastforce intro: equals0I rev_image_eqI dest: in_methods_in_msD in_set_procsD
      simp: distinct_methods distinct_fst_def)
  }
  ultimately have "distinct_fst (procs (PROG P))" using distinct_class_names [of P]
    by blast
  hence "BasicDefs.distinct_fst (procs (PROG P))"
    by (simp add: distinct_fst_is_distinct_fst)
  thus "BasicDefs.distinct_fst (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
    by (fastforce elim: in_set_procsE)
next
  fix C M P p ins outs
  assume "(p, ins, outs) \<in> set (((C, M), [], []) # procs P)"
  thus "distinct ins"
  proof (induct P)
    case Nil
    thus ?case by simp
  next
    case (Cons Cl P)
    then obtain C D fs ms where "Cl = (C, D, fs, ms)"
      by (cases Cl) blast
    with Cons show ?case
      by hypsubst_thin (induct ms, auto)
  qed
next
  fix C M P p ins outs
  assume "(p, ins, outs) \<in> set (((C, M), [], []) # procs P)"
  thus "distinct outs"
  proof (induct "P")
    case Nil
    thus ?case by simp
  next
    case (Cons Cl P)
    then obtain C D fs ms where "Cl = (C, D, fs, ms)"
      by (cases Cl) blast
    with Cons show ?case
      by hypsubst_thin (induct ms, auto)
  qed
qed

interpretation JVMCFG_Exit_Interpret:
  CFGExit "sourcenode" "targetnode" "kind" "valid_edge (P, C0, Main)"
  "(ClassMain P, MethodMain P, None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges P"
  "((ClassMain P, MethodMain P),[],[]) # procs (PROG P)"
  "(ClassMain P, MethodMain P)" "(ClassMain P, MethodMain P, None, Return)"
  for P C0 Main
proof (unfold_locales)
  fix a
  assume "valid_edge (P, C0, Main) a"
    and "sourcenode a = (ClassMain P, MethodMain P, None, nodeType.Return)"
  thus False
    by (cases a, clarsimp simp: valid_edge_def) (erule JVMCFG.cases, simp_all, clarsimp)
next
  show "(\<lambda>(C, M, pc, type). (C, M)) (ClassMain P, MethodMain P, None, nodeType.Return) =
    (ClassMain P, MethodMain P)"
    by simp
next
  fix a Q p f
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
    and "targetnode a = (ClassMain P, MethodMain P, None, nodeType.Return)"
  thus False
    by (cases a, clarsimp simp: valid_edge_def) (erule JVMCFG.cases, simp_all)
next
  show "\<exists>a. valid_edge (P, C0, Main) a \<and>
    sourcenode a = (ClassMain P, MethodMain P, None, Enter) \<and>
    targetnode a = (ClassMain P, MethodMain P, None, nodeType.Return) \<and>
    kind a = (\<lambda>s. False)\<^sub>\<surd>"
    by (fastforce intro: JVMCFG_reachable.intros simp: valid_edge_def)
qed

end
