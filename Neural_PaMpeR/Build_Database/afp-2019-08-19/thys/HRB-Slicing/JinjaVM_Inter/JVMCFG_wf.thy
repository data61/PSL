theory JVMCFG_wf imports JVMInterpretation "../StaticInter/CFGExit_wf" begin

inductive_set Def :: "wf_jvmprog \<Rightarrow> cfg_node \<Rightarrow> var set"
  for P :: "wf_jvmprog"
  and n :: "cfg_node"
where
  Def_Main_Heap:
  "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)
  \<Longrightarrow> Heap \<in> Def P n"
| Def_Main_Exception:
  "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)
  \<Longrightarrow> Exception \<in> Def P n"
| Def_Main_Stack_0:
  "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)
  \<Longrightarrow> Stack 0 \<in> Def P n"
| Def_Load:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Load idx;
  i = stkLength (P, C, M) pc\<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Store:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Store idx \<rbrakk>
  \<Longrightarrow> Local idx \<in> Def P n"
| Def_Push:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Push v;
  i = stkLength (P, C, M) pc \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_IAdd:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = IAdd;
  i = stkLength (P, C, M) pc - 2 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_CmpEq:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = CmpEq;
  i = stkLength (P, C, M) pc - 2 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_New_Heap:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = New Cl \<rbrakk>
  \<Longrightarrow> Heap \<in> Def P n"
| Def_New_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = New Cl;
  i = stkLength (P, C, M) pc \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Exception:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Exceptional pco nt);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Exception \<in> Def P n"
| Def_Exception_handle:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
  C \<noteq> ClassMain P;
  i = stkLength (P, C, M) pc' - 1 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Exception_handle_return:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return);
  C \<noteq> ClassMain P;
  i = stkLength (P, C, M) pc' - 1 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Getfield:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Getfield Cl Fd;
  i = stkLength (P, C, M) pc - 1 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Putfield:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Putfield Cl Fd \<rbrakk>
  \<Longrightarrow> Heap \<in> Def P n"
| Def_Invoke_Return_Heap:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Invoke M' n' \<rbrakk>
  \<Longrightarrow> Heap \<in> Def P n"
| Def_Invoke_Return_Exception:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Invoke M' n' \<rbrakk>
  \<Longrightarrow> Exception \<in> Def P n"
| Def_Invoke_Return_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Invoke M' n';
  i = stkLength (P, C, M) (Suc pc) - 1 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Def P n"
| Def_Invoke_Call_Heap:
  "\<lbrakk> n = (C, M, None, Enter);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Heap \<in> Def P n"
| Def_Invoke_Call_Local:
  "\<lbrakk> n = (C, M, None, Enter);
  C \<noteq> ClassMain P;
  i < locLength (P, C, M) 0 \<rbrakk>
  \<Longrightarrow> Local i \<in> Def P n"
| Def_Return:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = instr.Return \<rbrakk>
  \<Longrightarrow> Stack 0 \<in> Def P n"

inductive_set Use :: "wf_jvmprog \<Rightarrow> cfg_node \<Rightarrow> var set"
  for P :: "wf_jvmprog"
  and n :: "cfg_node"
where
  Use_Main_Heap:
  "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Load:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Load idx \<rbrakk>
  \<Longrightarrow> Local idx \<in> Use P n"
| Use_Enter_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  case (instrs_of (PROG P) C M ! pc)
    of Store n' \<Rightarrow> d = 1
    | Getfield F Cl \<Rightarrow> d = 1
    | Putfield F Cl \<Rightarrow> d = 2
    | Checkcast Cl \<Rightarrow> d = 1
    | Invoke M' n' \<Rightarrow> d = Suc n'
    | IAdd \<Rightarrow> d \<in> {1, 2}
    | IfFalse i \<Rightarrow> d = 1
    | CmpEq \<Rightarrow> d \<in> {1 , 2}
    | Throw \<Rightarrow> d = 1
    | instr.Return \<Rightarrow> d = 1
    | _ \<Rightarrow> False;
  i = stkLength (P, C, M) pc - d \<rbrakk>
  \<Longrightarrow> Stack i \<in> Use P n"
| Use_Enter_Local:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  instrs_of (PROG P) C M ! pc = Load n' \<rbrakk>
  \<Longrightarrow> Local n' \<in> Use P n"
| Use_Enter_Heap:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Enter);
  C \<noteq> ClassMain P;
  case (instrs_of (PROG P) C M ! pc)
    of New Cl \<Rightarrow> True
    | Checkcast Cl \<Rightarrow> True
    | Throw \<Rightarrow> True
    | _ \<Rightarrow> False \<rbrakk>
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Normal_Heap:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  case (instrs_of (PROG P) C M ! pc)
    of New Cl \<Rightarrow> True
    | Getfield F Cl \<Rightarrow> True
    | Putfield F Cl \<Rightarrow> True
    | Invoke M' n' \<Rightarrow> True
    | _ \<Rightarrow> False \<rbrakk>
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Normal_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Normal);
  C \<noteq> ClassMain P;
  case (instrs_of (PROG P) C M ! pc)
    of Getfield F Cl \<Rightarrow> d = 1
    | Putfield F Cl \<Rightarrow> d \<in> {1, 2}
    | Invoke M' n' \<Rightarrow> d > 0 \<and> d \<le> Suc n'
    | _ \<Rightarrow> False;
  i = stkLength (P, C, M) pc - d \<rbrakk>
  \<Longrightarrow> Stack i \<in> Use P n"
| Use_Return_Heap:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  instrs_of (PROG P) C M ! pc = Invoke M' n' \<or> C = ClassMain P \<rbrakk>
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Return_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  (instrs_of (PROG P) C M ! pc = Invoke M' n' \<and> i = stkLength (P, C, M) (Suc pc) - 1) \<or>
  (C = ClassMain P \<and> i = 0) \<rbrakk>
  \<Longrightarrow> Stack i \<in> Use P n"
| Use_Return_Exception:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
  instrs_of (PROG P) C M ! pc = Invoke M' n' \<or> C = ClassMain P \<rbrakk>
  \<Longrightarrow> Exception \<in> Use P n"
| Use_Exceptional_Stack:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Exceptional opc' nt);
  case (instrs_of (PROG P) C M ! pc)
    of Throw \<Rightarrow> True
    | _ \<Rightarrow> False;
  i = stkLength (P, C, M) pc - 1 \<rbrakk>
  \<Longrightarrow> Stack i \<in> Use P n"
| Use_Exceptional_Exception:
  "\<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return);
  instrs_of (PROG P) C M ! pc = Invoke M' n' \<rbrakk>
  \<Longrightarrow> Exception \<in> Use P n"
| Use_Method_Leave_Exception:
  "\<lbrakk> n = (C, M, None, Return);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Exception \<in> Use P n"
| Use_Method_Leave_Heap:
  "\<lbrakk> n = (C, M, None, Return);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Method_Leave_Stack:
  "\<lbrakk> n = (C, M, None, Return);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Stack 0 \<in> Use P n"
| Use_Method_Entry_Heap:
  "\<lbrakk> n = (C, M, None, Enter);
  C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> Heap \<in> Use P n"
| Use_Method_Entry_Local:
  "\<lbrakk> n = (C, M, None, Enter);
  C \<noteq> ClassMain P;
  i < locLength (P, C, M) 0 \<rbrakk>
  \<Longrightarrow> Local i \<in> Use P n"

fun ParamDefs :: "wf_jvmprog \<Rightarrow> cfg_node \<Rightarrow> var list"
where
  "ParamDefs P (C, M, \<lfloor>pc\<rfloor>, Return) = [Heap, Stack (stkLength (P, C, M) (Suc pc) - 1), Exception]"
  | "ParamDefs P (C, M, opc, nt) = []"

function ParamUses :: "wf_jvmprog \<Rightarrow> cfg_node \<Rightarrow> var set list"
where
  "ParamUses P (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal) = [{Heap},{}]"
  |
  "M \<noteq> MethodMain P \<or> opc \<noteq> \<lfloor>0\<rfloor> \<or> nt \<noteq> Normal
  \<Longrightarrow> ParamUses P (ClassMain P, M, opc, nt) = []"
  |
  "C \<noteq> ClassMain P
  \<Longrightarrow> ParamUses P (C, M, opc, nt) = (case opc of None \<Rightarrow> []
  | \<lfloor>pc\<rfloor> \<Rightarrow> (case nt of Normal \<Rightarrow> (case (instrs_of (PROG P) C M ! pc) of
      Invoke M' n \<Rightarrow> (
          {Heap} # rev (map (\<lambda>n. {Stack (stkLength (P, C, M) pc - (Suc n))}) [0..<n + 1])
      )
      | _ \<Rightarrow> [])
    | _ \<Rightarrow> []
    )
  )"
  by atomize_elim auto
termination by lexicographic_order

lemma in_set_ParamDefsE:
  "\<lbrakk> V \<in> set (ParamDefs P n);
  \<And>C M pc. \<lbrakk> n = (C, M, \<lfloor>pc\<rfloor>, Return);
         V \<in> {Heap, Stack (stkLength (P, C, M) (Suc pc) - 1), Exception} \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
  by (cases "(P, n)" rule: ParamDefs.cases) auto

lemma in_set_ParamUsesE:
  assumes V_in_ParamUses: "V \<in> \<Union>(set (ParamUses P n))"
  obtains "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)" and "V = Heap"
  | C M pc M' n' i where "n = (C, M, \<lfloor>pc\<rfloor>, Normal)" and "instrs_of (PROG P) C M ! pc = Invoke M' n'"
    and "V = Heap \<or> V = Stack (stkLength (P, C, M) pc - Suc i)" and "i < Suc n'" and "C \<noteq> ClassMain P"
proof (cases "(P, n)" rule: ParamUses.cases)
  case 1 with V_in_ParamUses that show ?thesis by clarsimp
next
  case 2 with V_in_ParamUses that show ?thesis by clarsimp
next
  case (3 C P M pc nt)
  with V_in_ParamUses that show ?thesis
    using [[simproc del: list_to_set_comprehension]]
    by (cases nt, auto) (rename_tac a b, case_tac "instrs_of (PROG P) C M ! a", simp_all, fastforce)
qed

lemma sees_method_fun_wf:
  assumes "PROG P \<turnstile> D sees M': Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D"
  and "(D, D', fs, ms) \<in> set (PROG P)"
  and "(M', Ts', T', mxs', mxl\<^sub>0', is', xt') \<in> set ms"
  shows "Ts = Ts' \<and> T = T' \<and> mxs = mxs' \<and> mxl\<^sub>0 = mxl\<^sub>0' \<and> is = is' \<and> xt = xt'"
proof -
  from distinct_class_names [of P] \<open>(D, D', fs, ms) \<in> set (PROG P)\<close>
  have "class (PROG P) D = \<lfloor>(D', fs, ms)\<rfloor>"
    by (fastforce intro: map_of_SomeI simp: class_def)
  moreover with distinct_method_names have "distinct_fst ms"
    by fastforce
  ultimately show ?thesis using
    \<open>PROG P \<turnstile> D sees M': Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D\<close>
    \<open>(M', Ts', T', mxs', mxl\<^sub>0', is', xt') \<in> set ms\<close>
    by (fastforce dest: visible_method_exists map_of_SomeD distinct_fst_isin_same_fst
      simp: distinct_fst_is_distinct_fst)
qed

interpretation JVMCFG_wf:
  CFG_wf  "sourcenode" "targetnode" "kind" "valid_edge (P, C0, Main)"
  "(ClassMain P, MethodMain P, None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges P"
  "((ClassMain P, MethodMain P),[],[]) # procs (PROG P)"
  "(ClassMain P, MethodMain P)"
  "Def P" "Use P" "ParamDefs P" "ParamUses P"
  for P C0 Main
proof (unfold_locales)
  show "Def P (ClassMain P, MethodMain P, None, Enter) = {} \<and>
    Use P (ClassMain P, MethodMain P, None, Enter) = {}"
    by (fastforce elim: Def.cases Use.cases)
next
  fix a Q r p fs ins outs
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and params: "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
  hence "(P, C0, Main) \<turnstile> sourcenode a -Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by (simp add: valid_edge_def)
  from this params show "length (ParamUses P (sourcenode a)) = length ins"
  proof cases
    case Main_Call
    with params show ?thesis
      by auto (erule in_set_procsE, auto dest: sees_method_idemp sees_method_fun)
  next
    case (CFG_Invoke_Call C M pc M' n ST LT D' Ts T mxs mxl0 "is" xt D Q' paramDefs)
    hence [simp]: "Q' = Q" and [simp]: "r = (C, M, pc)" and [simp]: "p = (D, M')"
      and [simp]: "fs = paramDefs"
      by simp_all
    from CFG_Invoke_Call obtain T' mxs' mpc' xt' where
      "PROG P,T',mxs',mpc',xt' \<turnstile> instrs_of (PROG P) C M ! pc,pc :: TYPING P C M"
      by (blast dest: reachable_node_impl_wt_instr)
    moreover from \<open>PROG P \<turnstile> D' sees M': Ts\<rightarrow>T = (mxs, mxl0, is, xt) in D\<close>
    have "PROG P \<turnstile> D sees M': Ts\<rightarrow>T = (mxs, mxl0, is, xt) in D"
      by -(drule sees_method_idemp)
    with params have "PROG P \<turnstile> D sees M': Ts\<rightarrow>T=(mxs, mxl0, is, xt) in D"
      and "ins = Heap # map Local [0..<Suc (length Ts)]"
      by (fastforce elim: in_set_procsE dest: sees_method_fun)+
    ultimately show ?thesis using CFG_Invoke_Call
      by (fastforce dest: sees_method_fun list_all2_lengthD simp: min_def)
  qed simp_all
next
  fix a
  assume "valid_edge (P, C0, Main) a"
  thus "distinct (ParamDefs P (targetnode a))"
    by (clarsimp simp: valid_edge_def) (erule JVMCFG.cases, auto)
next
  fix a Q' p f' ins outs
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    and params: "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
  hence "(P, C0, Main) \<turnstile> sourcenode a -Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rightarrow> targetnode a"
    by (simp add: valid_edge_def)
  from this params
  show "length (ParamDefs P (targetnode a)) = length outs"
    by cases (auto elim: in_set_procsE)
next
  fix n V
  assume params: "V \<in> set (ParamDefs P n)"
    and vn: "CFG.valid_node sourcenode targetnode (valid_edge (P, C0, Main)) n"
  then obtain ek n'
    where ve:"valid_edge (P, C0, Main) (n, ek, n') \<or> valid_edge (P, C0, Main) (n', ek, n)"
    by (fastforce simp: JVMCFG_Interpret.valid_node_def)
  from params obtain C M pc where [simp]: "n = (C, M, \<lfloor>pc\<rfloor>, Return)"
    and V: "V \<in> {Heap, Stack (stkLength (P, C, M) (Suc pc) - 1), Exception}"
    by (blast elim: in_set_ParamDefsE)
  from ve show "V \<in> Def P n"
  proof
    assume "valid_edge (P, C0, Main) (n, ek, n')"
    thus ?thesis unfolding valid_edge_def
    proof cases
      case Main_Return_to_Exit with V show ?thesis
        by (auto intro: Def_Main_Heap Def_Main_Stack_0 Def_Main_Exception simp: stkLength_def)
    next
      case CFG_Invoke_Return_Check_Normal with V show ?thesis
        by (fastforce intro: Def_Invoke_Return_Heap
          Def_Invoke_Return_Stack Def_Invoke_Return_Exception)
    next
      case CFG_Invoke_Return_Check_Exceptional with V show ?thesis
        by (fastforce intro: Def_Invoke_Return_Heap
          Def_Invoke_Return_Stack Def_Invoke_Return_Exception)
    next
      case CFG_Invoke_Return_Exceptional_prop with V show ?thesis
        by (fastforce intro: Def_Invoke_Return_Heap
          Def_Invoke_Return_Stack Def_Invoke_Return_Exception)
    qed simp_all
  next
    assume "valid_edge (P, C0, Main) (n', ek, n)"
    thus ?thesis unfolding valid_edge_def
    proof cases
      case Main_Call_LFalse with V show ?thesis
        by (auto intro: Def_Main_Heap Def_Main_Stack_0 Def_Main_Exception simp: stkLength_def)
    next
      case CFG_Invoke_False with V show ?thesis
        by (fastforce intro: Def_Invoke_Return_Heap
          Def_Invoke_Return_Stack Def_Invoke_Return_Exception)
    next
      case CFG_Return_from_Method with V show ?thesis
        by (fastforce elim!: JVMCFG.cases intro!: Def_Main_Stack_0
          intro: Def_Main_Heap Def_Main_Exception Def_Invoke_Return_Heap
          Def_Invoke_Return_Exception Def_Invoke_Return_Stack simp: stkLength_def)
    qed simp_all
  qed
next
  fix a Q r p fs ins outs V
  assume ve: "valid_edge (P, C0, Main) a"
    and kind: "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and params: "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
    and V: "V \<in> set ins"
  from params V obtain D fs ms Ts T mb where "class (PROG P) (fst p) = \<lfloor>(D, fs, ms)\<rfloor>"
    and "method": "PROG P \<turnstile> (fst p) sees (snd p): Ts\<rightarrow>T = mb in (fst p)"
    and ins: "ins = Heap # map Local [0..<Suc (length Ts)]"
    by (cases p) (fastforce elim: in_set_procsE)
  from ve kind show "V \<in> Def P (targetnode a)" unfolding valid_edge_def
  proof cases
    case (Main_Call T' mxs mxl0 "is" xt D' initParams)
    with kind have "PROG P \<turnstile> D' sees Main: []\<rightarrow>T' = (mxs, mxl0, is, xt) in D'"
      and [simp]: "p = (D', Main)"
      by (auto dest: sees_method_idemp)
    with "method" have [simp]: "Ts = []" and [simp]: "T' = T" and [simp]: "mb = (mxs, mxl0, is, xt)"
      by (fastforce dest: sees_method_fun)+
    from Main_Call ins V show ?thesis
      by (fastforce intro!: Def_Invoke_Call_Heap Def_Invoke_Call_Local
        dest: sees_method_idemp wt_jvm_prog_impl_wt_start[OF wf_jvmprog_is_wf_typ]
        simp: locLength_def wt_start_def)
  next
    case (CFG_Invoke_Call C M pc M' n ST LT D' Ts' T' mxs mxl0 "is" xt D'')
    with kind have "PROG P \<turnstile> D'' sees M': Ts'\<rightarrow>T' = (mxs, mxl0, is, xt) in D''"
      and [simp]: "p = (D'', M')"
      by (auto dest: sees_method_idemp)
    with "method" have [simp]: "Ts' = Ts" and [simp]: "T' = T" and [simp]: "mb = (mxs, mxl0, is, xt)"
      by (fastforce dest: sees_method_fun)+
    from CFG_Invoke_Call ins V show ?thesis
      by (fastforce intro!: Def_Invoke_Call_Local Def_Invoke_Call_Heap
        dest: sees_method_idemp wt_jvm_prog_impl_wt_start[OF wf_jvmprog_is_wf_typ] list_all2_lengthD
        simp: locLength_def min_def wt_start_def)
  qed simp_all
next
  fix a Q r p fs
  assume "valid_edge (P, C0, Main) a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  thus "Def P (sourcenode a) = {}" unfolding valid_edge_def
    by cases (auto elim: Def.cases)
next
  fix n V
  assume "CFG.valid_node sourcenode targetnode (valid_edge (P, C0, Main)) n"
    and V: "V \<in> \<Union>(set (ParamUses P n))"
  then obtain ek n'
    where ve:"valid_edge (P, C0, Main) (n, ek, n') \<or> valid_edge (P, C0, Main) (n', ek, n)"
    by (fastforce simp: JVMCFG_Interpret.valid_node_def)
  from V obtain C M pc M' n'' i where
    V: "n = (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal) \<and> V = Heap \<or>
    n = (C, M, \<lfloor>pc\<rfloor>, Normal) \<and> instrs_of (PROG P) C M ! pc = Invoke M' n'' \<and>
      (V = Heap \<or> V = Stack (stkLength (P, C, M) pc - Suc i)) \<and> i < Suc n'' \<and> C \<noteq> ClassMain P"
    by -(erule in_set_ParamUsesE, fastforce+)
  from ve show "V \<in> Use P n"
  proof
    assume "valid_edge (P, C0, Main) (n, ek, n')"
    from this V show ?thesis unfolding valid_edge_def
    proof cases
      case Main_Call_LFalse with V show ?thesis by (fastforce intro: Use_Main_Heap)
    next
      case Main_Call with V show ?thesis by (fastforce intro: Use_Main_Heap)
    next
      case CFG_Invoke_Call with V show ?thesis
        by (fastforce intro: Use_Normal_Heap Use_Normal_Stack [where d="Suc i"])
    next
      case CFG_Invoke_False with V show ?thesis
        by (fastforce intro: Use_Normal_Heap Use_Normal_Stack [where d="Suc i"])
    qed simp_all
  next
    assume "valid_edge (P, C0, Main) (n', ek, n)"
    from this V show ?thesis unfolding valid_edge_def
    proof cases
      case Main_to_Call with V show ?thesis by (fastforce intro: Use_Main_Heap)
    next
      case CFG_Invoke_Check_NP_Normal with V show ?thesis
        by (fastforce intro: Use_Normal_Heap Use_Normal_Stack [where d="Suc i"])
    qed simp_all
  qed
next
  fix a Q p f ins outs V
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
    and "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
    and "V \<in> set outs"
  thus "V \<in> Use P (sourcenode a)" unfolding valid_edge_def
    by (cases, simp_all)
  (fastforce elim: in_set_procsE
    intro: Use_Method_Leave_Heap Use_Method_Leave_Stack Use_Method_Leave_Exception)
next
  fix a V s
  assume ve: "valid_edge (P, C0, Main) a"
    and V_notin_Def: "V \<notin> Def P (sourcenode a)"
    and ik: "intra_kind (kind a)"
    and pred: "JVMCFG_Interpret.pred (kind a) s"
  show "JVMCFG_Interpret.state_val
    (CFG.transfer (((ClassMain P, MethodMain P), [], []) # procs (PROG P)) (kind a) s) V
    = JVMCFG_Interpret.state_val s V"
  proof (cases s)
    case Nil
    thus ?thesis by simp
  next
    case [simp]: Cons
    with ve V_notin_Def ik pred show ?thesis unfolding valid_edge_def
    proof cases
      case CFG_Load with V_notin_Def show ?thesis by (fastforce intro: Def_Load)
    next case CFG_Store with V_notin_Def show ?thesis by (fastforce intro: Def_Store)
    next case CFG_Push with V_notin_Def show ?thesis by (fastforce intro: Def_Push)
    next case CFG_IAdd with V_notin_Def show ?thesis by (fastforce intro: Def_IAdd)
    next case CFG_CmpEq with V_notin_Def show ?thesis by (fastforce intro: Def_CmpEq)
    next case CFG_New_Update with V_notin_Def show ?thesis
        by (fastforce intro: Def_New_Heap Def_New_Stack)
    next case CFG_New_Exceptional_prop with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception)
    next case CFG_New_Exceptional_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Getfield_Update with V_notin_Def show ?thesis
        by (fastforce intro: Def_Getfield split: prod.split)
    next case CFG_Getfield_Exceptional_prop with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception)
    next case CFG_Getfield_Exceptional_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Putfield_Update with V_notin_Def show ?thesis
        by (fastforce intro: Def_Putfield split: prod.split)
    next case CFG_Putfield_Exceptional_prop with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception)
    next case CFG_Putfield_Exceptional_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Checkcast_Exceptional_prop with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception)
    next case CFG_Checkcast_Exceptional_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Throw_prop with V_notin_Def show ?thesis by (fastforce intro: Def_Exception)
    next case CFG_Throw_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Invoke_NP_prop with V_notin_Def show ?thesis by (fastforce intro: Def_Exception)
    next case CFG_Invoke_NP_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception Def_Exception_handle)
    next case CFG_Invoke_Return_Exceptional_handle with V_notin_Def show ?thesis
        by (fastforce intro: Def_Exception_handle_return Def_Exception)
    next case CFG_Return with V_notin_Def show ?thesis by (fastforce intro: Def_Return)
    qed (simp_all add: intra_kind_def)
  qed
next
  fix a s s'
  assume ve: "valid_edge (P, C0, Main) a"
    and use_Eq: "\<forall>V\<in>Use P (sourcenode a). JVMCFG_Interpret.state_val s V
    = JVMCFG_Interpret.state_val s' V"
    and ik: "intra_kind (kind a)"
    and pred_s: "JVMCFG_Interpret.pred (kind a) s"
    and pred_s': "JVMCFG_Interpret.pred (kind a) s'"
  then obtain cfs C M pc cs cfs' C' M' pc' cs' where [simp]: "s = (cfs, (C, M, pc)) # cs"
    and [simp]: "s' = (cfs', (C', M', pc')) # cs'"
    by (cases s, fastforce) (cases s', fastforce+)
  from ve show "\<forall>V\<in>Def P (sourcenode a).
             JVMCFG_Interpret.state_val
              (CFG.transfer (((ClassMain P, MethodMain P), [], []) # procs (PROG P)) (kind a) s) V =
             JVMCFG_Interpret.state_val
              (CFG.transfer (((ClassMain P, MethodMain P), [], []) # procs (PROG P)) (kind a) s') V"
    unfolding valid_edge_def
  proof cases
    case Main_Call with ik show ?thesis by (simp add: intra_kind_def)
  next case Main_Return_to_Exit with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Return_Heap Use_Return_Exception Use_Return_Stack)
  next case Method_LFalse with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Method_Entry_Heap Use_Method_Entry_Local) 
  next case Method_LTrue with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Method_Entry_Heap Use_Method_Entry_Local)
  next case CFG_Load with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Enter_Local)
  next case CFG_Store with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Enter_Stack)
  next case (CFG_IAdd C M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Stack (stkLength (P, C, M) pc - 2) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)+
    with use_Eq CFG_IAdd show ?thesis by (auto elim!: Def.cases)
  next case (CFG_CmpEq C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Stack (stkLength (P, C, M) pc - 2) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)+
    with use_Eq CFG_CmpEq show ?thesis by (auto elim!: Def.cases)
  next case CFG_New_Update
    hence "Heap \<in> Use P (sourcenode a)" by (fastforce intro: Use_Normal_Heap)
    with use_Eq CFG_New_Update show ?thesis by (fastforce elim: Def.cases)
  next case (CFG_Getfield_Update C  M pc)
    hence "Heap \<in> Use P (sourcenode a)"
      and "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Normal_Heap Use_Normal_Stack)+
    with use_Eq CFG_Getfield_Update show ?thesis by (auto elim!: Def.cases split: prod.split)
  next case (CFG_Putfield_Update C  M pc)
    hence "Heap \<in> Use P (sourcenode a)"
      and "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Stack (stkLength (P, C, M) pc - 2) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Normal_Heap Use_Normal_Stack)+
    with use_Eq CFG_Putfield_Update show ?thesis by (auto elim!: Def.cases split: prod.split)
  next case (CFG_Throw_prop C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Exceptional_Stack)
    with use_Eq CFG_Throw_prop show ?thesis by (fastforce elim: Def.cases)
  next case (CFG_Throw_handle C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Exceptional_Stack)
    with use_Eq CFG_Throw_handle show ?thesis by (fastforce elim: Def.cases)
  next case CFG_Invoke_Call with ik show ?thesis by (simp add: intra_kind_def)
  next case CFG_Invoke_Return_Check_Normal with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Return_Heap Use_Return_Exception Use_Return_Stack)
  next case CFG_Invoke_Return_Check_Exceptional with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Return_Heap Use_Return_Exception Use_Return_Stack)
  next case CFG_Invoke_Return_Exceptional_handle with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Exceptional_Exception)
  next case CFG_Invoke_Return_Exceptional_prop with use_Eq show ?thesis
      by (fastforce elim: Def.cases intro: Use_Return_Heap Use_Return_Exception Use_Return_Stack)
  next case CFG_Return with use_Eq show ?thesis
      by (fastforce elim!: Def.cases intro: Use_Enter_Stack)
  next case CFG_Return_from_Method with ik show ?thesis by (simp add: intra_kind_def)
  qed (fastforce elim: Def.cases)+
next
  fix a s s'
  assume ve: "valid_edge (P, C0, Main) a"
    and pred: "JVMCFG_Interpret.pred (kind a) s"
    and "snd (hd s) = snd (hd s')"
    and use_Eq: "\<forall>V\<in>Use P (sourcenode a).
           JVMCFG_Interpret.state_val s V = JVMCFG_Interpret.state_val s' V"
    and "length s = length s'"
  then obtain cfs C M pc cs cfs' cs' where [simp]: "s = (cfs, (C, M, pc)) # cs"
    and [simp]: "s' = (cfs', (C, M, pc)) # cs'" and length_cs: "length cs = length cs'"
    by (cases s, fastforce) (cases s', fastforce+)
  from ve pred show "JVMCFG_Interpret.pred (kind a) s'"
    unfolding valid_edge_def
  proof cases
    case Main_Call_LFalse with pred show ?thesis by simp
  next case Main_Call with pred use_Eq show ?thesis by simp
  next case Method_LTrue with pred use_Eq show ?thesis by simp
  next case CFG_Goto with pred use_Eq show ?thesis by simp
  next case (CFG_IfFalse_False C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with use_Eq CFG_IfFalse_False pred show ?thesis by fastforce
  next case (CFG_IfFalse_True C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_IfFalse_True show ?thesis by fastforce
  next case CFG_New_Check_Normal
    hence "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Heap)
    with pred use_Eq CFG_New_Check_Normal show ?thesis by fastforce
  next case CFG_New_Check_Exceptional 
    hence "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Heap)
    with pred use_Eq CFG_New_Check_Exceptional show ?thesis by fastforce
  next case (CFG_Getfield_Check_Normal C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Getfield_Check_Normal show ?thesis by fastforce
  next case (CFG_Getfield_Check_Exceptional C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Getfield_Check_Exceptional  show ?thesis by fastforce
  next case (CFG_Putfield_Check_Normal C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 2) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Putfield_Check_Normal show ?thesis by fastforce
  next case (CFG_Putfield_Check_Exceptional C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 2) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Putfield_Check_Exceptional show ?thesis by fastforce
  next case (CFG_Checkcast_Check_Normal C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack Use_Enter_Heap)+
    with pred use_Eq CFG_Checkcast_Check_Normal show ?thesis by fastforce
  next case (CFG_Checkcast_Check_Exceptional C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack Use_Enter_Heap)+
    with pred use_Eq CFG_Checkcast_Check_Exceptional show ?thesis by fastforce
  next case (CFG_Throw_Check C  M pc)
    hence "Stack (stkLength (P, C, M) pc - 1) \<in> Use P (sourcenode a)"
      and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack Use_Enter_Heap)+
    with pred use_Eq CFG_Throw_Check show ?thesis by fastforce
  next case (CFG_Invoke_Check_NP_Normal C  M pc M' n)
    hence "Stack (stkLength (P, C, M) pc - (Suc n)) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Invoke_Check_NP_Normal show ?thesis by fastforce
  next case (CFG_Invoke_Check_NP_Exceptional C  M pc M' n)
    hence "Stack (stkLength (P, C, M) pc - (Suc n)) \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Enter_Stack)
    with pred use_Eq CFG_Invoke_Check_NP_Exceptional show ?thesis by fastforce
  next case (CFG_Invoke_Call C  M pc M' n)
    hence "Stack (stkLength (P, C, M) pc - (Suc n)) \<in> Use P (sourcenode a)"
      and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Normal_Heap Use_Normal_Stack)+
    with pred use_Eq CFG_Invoke_Call show ?thesis by fastforce
  next case CFG_Invoke_Return_Check_Normal
    hence "Exception \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Return_Exception)
    with pred use_Eq CFG_Invoke_Return_Check_Normal show ?thesis by fastforce
  next case CFG_Invoke_Return_Check_Exceptional
    hence "Exception \<in> Use P (sourcenode a)" and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Return_Exception Use_Return_Heap)+
    with pred use_Eq CFG_Invoke_Return_Check_Exceptional show ?thesis by fastforce
  next case CFG_Invoke_Return_Exceptional_prop
    hence "Exception \<in> Use P (sourcenode a)" and "Heap \<in> Use P (sourcenode a)"
      by (fastforce intro: Use_Return_Exception Use_Return_Heap)+
    with pred use_Eq CFG_Invoke_Return_Exceptional_prop show ?thesis by fastforce
  next case CFG_Return_from_Method with pred length_cs show ?thesis by clarsimp
  qed auto
next
  fix a Q r p fs ins outs
  assume "valid_edge (P, C0, Main) a"
    and kind: "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and params: "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
  thus "length fs = length ins" unfolding valid_edge_def
  proof cases
    case (Main_Call  T mxs mxl0 "is" xt D)
    with kind params have [simp]: "p = (D, Main)"
      and "PROG P \<turnstile> D sees Main: []\<rightarrow>T = (mxs, mxl0, is, xt) in D"
      and "ins = Heap # map Local [0..<Suc 0]"
      by (auto elim!: in_set_procsE dest: sees_method_fun sees_method_idemp)
    with Main_Call kind show ?thesis
      by auto
  next
    case (CFG_Invoke_Call C  M pc M' n ST LT D' Ts T mxs mxl0 "is" xt D)
    with kind params have [simp]: "p = (D, M')"
      and "PROG P \<turnstile> D' sees M': Ts\<rightarrow>T = (mxs, mxl0, is, xt) in D"
      and "ins = Heap # map Local [0..<Suc (length Ts)]"
      by (auto elim!: in_set_procsE dest: sees_method_fun sees_method_idemp)
    moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close> \<open>C \<noteq> ClassMain P\<close>
      \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> \<open>TYPING P C M ! pc = \<lfloor>(ST, LT)\<rfloor>\<close>
      \<open>ST ! n = Class D'\<close> have "n = length Ts"
      by (fastforce dest!: reachable_node_impl_wt_instr dest: sees_method_fun list_all2_lengthD)
    ultimately show ?thesis using CFG_Invoke_Call kind by auto
  qed simp_all
next
  fix a Q r p fs a' Q' r' p' fs' s s'
  assume ve_a: "valid_edge (P, C0, Main) a"
    and kind_a: "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and ve_a': "valid_edge (P, C0, Main) a'"
    and kind_a': "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'"
    and src: "sourcenode a = sourcenode a'"
    and pred_s: "JVMCFG_Interpret.pred (kind a) s"
    and pred_s': "JVMCFG_Interpret.pred (kind a') s"
  then obtain cfs C M pc cs cfs' C' M' pc' cs' 
    where [simp]: "s = (cfs, (C, M, pc)) # cs" 
    by (cases s) fastforce+
  with ve_a kind_a show "a = a'" unfolding valid_edge_def
  proof cases
    case Main_Call with ve_a' kind_a' src pred_s pred_s' show ?thesis unfolding valid_edge_def
      by (cases a, cases a') (fastforce elim: JVMCFG.cases dest: sees_method_fun)
  next
    case CFG_Invoke_Call
    note invoke_call1 = this
    from ve_a' kind_a' show ?thesis unfolding valid_edge_def
    proof cases
      case Main_Call with CFG_Invoke_Call src have False by simp
      thus ?thesis by simp
    next
      case CFG_Invoke_Call with src invoke_call1 show ?thesis
        by clarsimp (cases a, cases a', fastforce dest: sees_method_fun)
    qed simp_all
  qed simp_all
next
  fix a Q r p fs i ins outs s s'
  assume ve: "valid_edge (P, C0, Main) a"
    and kind: "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and "i < length ins"
    and "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
    and "JVMCFG_Interpret.pred (kind a) s"
    and "JVMCFG_Interpret.pred (kind a) s'"
    and use_Eq: "\<forall>V\<in>ParamUses P (sourcenode a) ! i.
           JVMCFG_Interpret.state_val s V = JVMCFG_Interpret.state_val s' V"
  then obtain cfs C M pc cs cfs' C' M' pc' cs' where [simp]: "s = (cfs, (C, M, pc)) # cs"
    and [simp]: "s' = (cfs', (C', M', pc')) # cs'"
    by (cases s, fastforce) (cases s', fastforce+)
  from ve kind
  show "JVMCFG_Interpret.params fs (JVMCFG_Interpret.state_val s) ! i =
          JVMCFG_Interpret.params fs (JVMCFG_Interpret.state_val s') ! i"
    unfolding valid_edge_def
  proof cases
    case Main_Call with kind use_Eq \<open>i < length ins\<close> show ?thesis
      by (cases i) auto
  next
    case CFG_Invoke_Call
    { fix P C M pc n st st' i
      have "\<forall>V\<in>rev (map (\<lambda>n. {Stack (stkLength (P, C, M) pc - Suc n)}) [0..<n]) ! i. st V = st' V
        \<Longrightarrow> JVMCFG_Interpret.params
        (rev (map (\<lambda>i s. s (Stack (stkLength (P, C, M) pc - Suc i))) [0..<n])) st ! i =
        JVMCFG_Interpret.params
        (rev (map (\<lambda>i s. s (Stack (stkLength (P, C, M) pc - Suc i))) [0..<n])) st' ! i"
        by (induct n arbitrary: i) (simp, case_tac i, auto)
    }
    note stack_params = this
    from CFG_Invoke_Call kind use_Eq \<open>i < length ins\<close> show ?thesis
      by (cases i, auto) (case_tac nat, auto intro: stack_params)
  qed simp_all
next
  fix a Q' p f' ins outs vmap vmap'
  assume "valid_edge (P, C0, Main) a"
    and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    and "(p, ins, outs) \<in> set (((ClassMain P, MethodMain P), [], []) # procs (PROG P))"
  thus "f' vmap vmap' = vmap'(ParamDefs P (targetnode a) [:=] map vmap outs)"
    unfolding valid_edge_def
    by (cases, simp_all) (fastforce elim: in_set_procsE simp: fun_upd_twist)
next
  fix a a'
  { fix P n f n' e n''
    assume "P \<turnstile> n -\<Up>f\<rightarrow> n'" and "P \<turnstile> n -e\<rightarrow> n''"
    hence "e = \<Up>f \<and> n' = n''"
      by cases (simp_all, (fastforce elim: JVMCFG.cases)+)
  }
  note upd_det = this
  { fix P n Q n' Q' n'' s
    assume "P \<turnstile> n -(Q)\<^sub>\<surd>\<rightarrow> n'" and edge': "P \<turnstile> n -(Q')\<^sub>\<surd>\<rightarrow> n''" and trg: "n' \<noteq> n''"
    hence "(Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    proof cases
      case CFG_Throw_Check with edge' trg show ?thesis by cases fastforce+
    qed (simp_all, (fastforce elim: JVMCFG.cases)+)
  }
  note pred_det = this
  assume "valid_edge (P, C0, Main) a"
    and ve': "valid_edge (P, C0, Main) a'"
    and src: "sourcenode a = sourcenode a'"
    and trg: "targetnode a \<noteq> targetnode a'"
    and "intra_kind (kind a)"
    and "intra_kind (kind a')"
  thus "\<exists>Q Q'. kind a = (Q)\<^sub>\<surd> \<and> kind a' = (Q')\<^sub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
    unfolding valid_edge_def intra_kind_def
    by (auto dest: upd_det pred_det)
qed

interpretation JVMCFGExit_wf :
  CFGExit_wf "sourcenode" "targetnode" "kind" "valid_edge (P, C0, Main)"
  "(ClassMain P, MethodMain P, None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges P"
  "((ClassMain P, MethodMain P),[],[]) # procs (PROG P)"
  "(ClassMain P, MethodMain P)"
  "(ClassMain P, MethodMain P, None, Return)"
  "Def P" "Use P" "ParamDefs P" "ParamUses P"
proof
  show "Def P (ClassMain P, MethodMain P, None, nodeType.Return) = {} \<and>
    Use P (ClassMain P, MethodMain P, None, nodeType.Return) = {}"
    by (fastforce elim: Def.cases Use.cases)
qed

end
