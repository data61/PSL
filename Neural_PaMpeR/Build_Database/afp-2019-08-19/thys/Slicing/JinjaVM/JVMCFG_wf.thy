theory JVMCFG_wf imports JVMInterpretation "../Basic/CFGExit_wf" begin

section \<open>Instantiation of the \<open>CFG_wf\<close> locale\<close>

subsection \<open>Variables and Values\<close>

datatype jinja_var = HeapVar "addr" | Stk "nat" "nat" | Loc "nat" "nat"
datatype jinja_val = Object "obj option" | Primitive "val"

fun state_val :: "state \<Rightarrow> jinja_var \<Rightarrow> jinja_val"
where
  "state_val (h, stk, loc) (HeapVar a) = Object (h a)"
| "state_val (h, stk, loc) (Stk cd idx) = Primitive (stk (cd, idx))"
| "state_val (h, stk, loc) (Loc cd idx) = Primitive (loc (cd, idx))"


subsection \<open>The \<open>Def\<close> and \<open>Use\<close> sets\<close>

inductive_set Def :: "wf_jvmprog \<Rightarrow> j_node \<Rightarrow> jinja_var set"
  for P :: "wf_jvmprog"
  and n :: "j_node"
where
  Def_Load:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Load idx;
  cd = length cs;
  i = stkLength P C M pc\<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_Store:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Store idx;
  cd = length cs \<rbrakk>
  \<Longrightarrow> Loc cd idx \<in> Def P n"

| Def_Push:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Push v;
  cd = length cs;
  i = stkLength P C M pc \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_New_Normal_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = New Cl;
  cd = length cs;
  i = stkLength P C M pc \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_New_Normal_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = New Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Def P n"

| Def_Exc_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',True)\<rfloor> _);
  cs' \<noteq> [];
  cd = length cs' - 1;
  (C',M',pc') = hd cs';
  i = stkLength P C' M' pc' - 1\<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_Getfield_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Getfield Fd Cl;
  cd = length cs;
  i = stkLength P C M pc - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_Putfield_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Putfield Fd Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Def P n"

| Def_Invoke_Loc:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Invoke M' n';
  cs' \<noteq> [];
  hd cs' = (C',M',0);
  i < locLength P C' M' 0;
  cd = Suc (length cs) \<rbrakk>
  \<Longrightarrow> Loc cd i \<in> Def P n"

| Def_Return_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#(D,M',pc')#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Return;
  cd = length cs;
  i = stkLength P D M' (Suc pc') - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_IAdd_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = IAdd;
  cd = length cs;
  i = stkLength P C M pc - 2 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

| Def_CmpEq_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = CmpEq;
  cd = length cs;
  i = stkLength P C M pc - 2 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Def P n"

inductive_set Use :: "wf_jvmprog \<Rightarrow> j_node \<Rightarrow> jinja_var set"
  for P :: "wf_jvmprog"
  and n :: "j_node"
where
  Use_Load:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Load idx;
  cd = length cs \<rbrakk>
  \<Longrightarrow> (Loc cd idx) \<in> Use P n"

| Use_Store:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Store idx;
  cd = length cs;
  Suc i = (stkLength P C M pc) \<rbrakk>
  \<Longrightarrow> (Stk cd i) \<in> Use P n"

| Use_New:
  "\<lbrakk> n = (_ (C, M, pc)#cs,x _);
  x = None \<or> x = \<lfloor>(cs',False)\<rfloor>;
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = New Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

| Use_Getfield_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,x _);
  x = None \<or> x = \<lfloor>(cs',False)\<rfloor>;
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Getfield Fd Cl;
  cd = length cs;
  Suc i = stkLength P C M pc \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Getfield_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Getfield Fd Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

| Use_Putfield_Stk_Pred:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Putfield Fd Cl;
  cd = length cs;
  i = stkLength P C M pc - 2 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Putfield_Stk_Update:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Putfield Fd Cl;
  cd = length cs;
  i = stkLength P C M pc - 2 \<or> i = stkLength P C M pc - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Putfield_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Putfield Fd Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

| Use_Checkcast_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,x _);
  x = None \<or> x = \<lfloor>(cs',False)\<rfloor>;
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Checkcast Cl;
  cd = length cs;
  i = stkLength P C M pc - Suc 0 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Checkcast_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Checkcast Cl \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

| Use_Invoke_Stk_Pred:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Invoke M' n';
  cd = length cs;
  i = stkLength P C M pc - Suc n' \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Invoke_Heap_Pred:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Invoke M' n' \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

| Use_Invoke_Stk_Update:
  "\<lbrakk> n = (_ (C, M, pc)#cs,\<lfloor>(cs',False)\<rfloor> _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Invoke M' n';
  cd = length cs;
  i < stkLength P C M pc;
  i \<ge> stkLength P C M pc - Suc n' \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Return_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#(D,M',pc')#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Return;
  cd = Suc (length cs);
  i = stkLength P C M pc - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_IAdd_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = IAdd;
  cd = length cs;
  i = stkLength P C M pc - 1 \<or> i = stkLength P C M pc - 2 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_IfFalse_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = (IfFalse b);
  cd = length cs;
  i = stkLength P C M pc - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_CmpEq_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,None _);
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = CmpEq;
  cd = length cs;
  i = stkLength P C M pc - 1 \<or> i = stkLength P C M pc - 2 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Throw_Stk:
  "\<lbrakk> n = (_ (C, M, pc)#cs,x _);
  x = None \<or> x = \<lfloor>(cs',True)\<rfloor>;
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Throw;
  cd = length cs;
  i = stkLength P C M pc - 1 \<rbrakk>
  \<Longrightarrow> Stk cd i \<in> Use P n"

| Use_Throw_Heap:
  "\<lbrakk> n = (_ (C, M, pc)#cs,x _);
  x = None \<or> x = \<lfloor>(cs',True)\<rfloor>;
  instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Throw \<rbrakk>
  \<Longrightarrow> HeapVar a \<in> Use P n"

declare correct_state_def [simp del]

lemma edge_transfer_uses_only_Use:
  "\<lbrakk>valid_edge (P,C0,Main) a; \<forall>V \<in> Use P (sourcenode a). state_val s V = state_val s' V\<rbrakk>
  \<Longrightarrow> \<forall>V \<in> Def P (sourcenode a). state_val (BasicDefs.transfer (kind a) s) V =
                                  state_val (BasicDefs.transfer (kind a) s') V"
proof
  fix V
  assume ve: "valid_edge (P, C0, Main) a"
    and use_eq: "\<forall>V\<in>Use P (sourcenode a). state_val s V = state_val s' V"
    and v_in_def: "V \<in> Def P (sourcenode a)"
  obtain h stk loc where [simp]: "s = (h,stk,loc)" by (cases s, fastforce)
  obtain h' stk' loc' where [simp]: "s' = (h',stk',loc')" by (cases s', fastforce)
  note P_wf = wf_jvmprog_is_wf [of P]
  from ve
  have ex_edge: "(P,C0,Main) \<turnstile> (sourcenode a)-kind a\<rightarrow>(targetnode a)"
    and vn: "valid_node (P,C0,Main) (sourcenode a)"
    by simp_all
  show "state_val (transfer (kind a) s) V = state_val (transfer (kind a) s') V"
  proof (cases "sourcenode a")
    case [simp]: (Node cs x)
    from vn ex_edge have "cs \<noteq> []"
      by (cases x, auto elim: JVM_CFG.cases)
    then obtain C M pc cs' where [simp]: "cs = (C, M, pc)#cs'" by (cases cs, fastforce+)
    with vn obtain ST LT where wt: "((P\<^bsub>\<Phi>\<^esub>) C M ! pc) = \<lfloor>(ST,LT)\<rfloor>"
      by (cases cs', (cases x, auto)+)
    show ?thesis
    proof (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
      case [simp]: (Load n)
      from ex_edge have [simp]: "x = None"
        by (auto elim!: JVM_CFG.cases)
      hence "Loc (length cs') n \<in> Use P (sourcenode a)"
        by (auto intro!: Use_Load)
      with use_eq have "state_val s (Loc (length cs') n) = state_val s' (Loc (length cs') n)"
        by (simp del: state_val.simps)
      with v_in_def ex_edge show ?thesis
        by (auto elim!: Def.cases
                  elim: JVM_CFG.cases
                  simp: split_beta)
    next
      case [simp]: (Store n)
      from ex_edge have [simp]:"x = None"
        by (auto elim!: JVM_CFG.cases)
      have "ST \<noteq> []"
      proof -
        from vn
        obtain Ts T mxs mxl "is" xt
          where C_sees_M: "P\<^bsub>wf\<^esub> \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, is, xt) in C"
          by (cases cs', auto)
        with vn
        have "pc < length is"
          by (cases cs', auto dest: sees_method_fun)
        from P_wf C_sees_M
        have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Store C_sees_M wt \<open>pc < length is\<close>
        show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      then obtain ST1 STr where [simp]: "ST = ST1#STr"
        by (cases ST, fastforce+)
      from wt
        have "Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use_src")
          by -(rule Use_Store, fastforce+)
      with use_eq have "state_val s ?stk_top = state_val s' ?stk_top"
        by (simp del: state_val.simps)
      with v_in_def ex_edge wt show ?thesis
        by (auto elim!: Def.cases
                  elim: JVM_CFG.cases
                  simp: split_beta)
    next
      case [simp]: (Push val)
      from ex_edge have "x = None"
        by (auto elim!: JVM_CFG.cases)
      with v_in_def ex_edge show ?thesis
        by (auto elim!: Def.cases
                  elim: JVM_CFG.cases)
    next
      case [simp]: (New Cl)
      show ?thesis
      proof (cases x)
        case None
        with v_in_def have False
          by (auto elim: Def.cases)
        thus ?thesis by simp
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
          by (cases x', fastforce)
        have "\<not> xf \<longrightarrow> (\<forall>addr. HeapVar addr \<in> Use P (sourcenode a))"
          by (fastforce intro: Use_New)
        with use_eq
        have "\<not> xf \<longrightarrow> (\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr))"
          by (simp del: state_val.simps)
        hence "\<not> xf \<longrightarrow> h = h'"
          by (auto intro: ext)
        with v_in_def ex_edge show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Getfield Fd Cl)
      show ?thesis
      proof (cases x)
        case None
        with v_in_def have False
          by (auto elim: Def.cases)
        thus ?thesis by simp
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
          by (cases x', fastforce)
        have "ST \<noteq> []"
        proof -
          from vn obtain T Ts mxs mxl "is" xt
            where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
            by (cases cs', auto)
          with vn
          have "pc < length is"
            by (cases cs', auto dest: sees_method_fun)
          from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
            by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
          with Getfield sees_M wt \<open>pc < length is\<close> show ?thesis
            by (fastforce simp: wt_method_def)
        qed
        then obtain ST1 STr where [simp]: "ST = ST1#STr" by (cases ST, fastforce)
        from wt
        have "\<not> xf \<longrightarrow> (Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a))"
          (is "?xf \<longrightarrow> ?stk_top \<in> ?Use_src")
          by (auto intro!: Use_Getfield_Stk)
        with use_eq 
        have stk_top_eq: "\<not> xf \<longrightarrow> state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        have "\<not> xf \<longrightarrow> (\<forall>addr. HeapVar addr \<in> Use P (sourcenode a))"
          by (auto intro!: Use_Getfield_Heap)
        with use_eq
        have "\<not> xf \<longrightarrow> (\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr))"
          by (simp del: state_val.simps)
        hence "\<not> xf \<longrightarrow> h = h'"
          by (auto intro: ext)
        with ex_edge v_in_def stk_top_eq wt
        show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases
                    simp: split_beta)
      qed
    next
      case [simp]: (Putfield Fd Cl)
      show ?thesis
      proof (cases x)
        case None
        with v_in_def have False
          by (auto elim: Def.cases)
        thus ?thesis by simp
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>" 
          by (cases x', fastforce)
        have "length ST > 1"
        proof -
          from vn obtain T Ts mxs mxl "is" xt
            where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
            by (cases cs', auto)
          with vn
          have "pc < length is"
            by (cases cs', auto dest: sees_method_fun)
          from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
            by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
          with Putfield sees_M \<open>pc < length is\<close> wt show ?thesis
            by (fastforce simp: wt_method_def)
        qed
        then obtain ST1 STr' where "ST = ST1#STr' \<and> length STr' > 0"
          by (cases ST, fastforce+)
        then obtain ST2 STr where [simp]: "ST = ST1#ST2#STr"
          by (cases STr', fastforce+)
        from wt
        have "\<not> xf \<longrightarrow> (Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a))"
          (is "?xf \<longrightarrow> ?stk_top \<in> ?Use_src")
          by (fastforce intro: Use_Putfield_Stk_Update)
        with use_eq have stk_top:"(\<not> xf) \<longrightarrow> state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        from wt
        have "\<not> xf \<longrightarrow> (Stk (length cs') (length ST - 2) \<in> Use P (sourcenode a))"
          (is "?xf \<longrightarrow> ?stk_nxt \<in> ?Use_src")
          by (fastforce intro: Use_Putfield_Stk_Update)
        with use_eq
        have stk_nxt:"(\<not> xf) \<longrightarrow> state_val s ?stk_nxt = state_val s' ?stk_nxt"
          by (simp del: state_val.simps)
        have "\<not> xf \<longrightarrow> (\<forall>addr. HeapVar addr \<in> Use P (sourcenode a))"
          by (fastforce intro: Use_Putfield_Heap)
        with use_eq
        have "\<not> xf \<longrightarrow> (\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr))"
          by (simp del: state_val.simps)
        hence "\<not> xf \<longrightarrow> h = h'"
          by (auto intro: ext)
        with ex_edge v_in_def stk_top stk_nxt wt show ?thesis
          by (auto elim!: Def.cases
                   elim: JVM_CFG.cases
                   simp: split_beta)
      qed
    next
      case [simp]: (Checkcast Cl)
      show ?thesis
      proof (cases x)
        case None
        with v_in_def have False
          by (auto elim: Def.cases)
        thus ?thesis by simp
      next
        case (Some x')
        with ex_edge obtain cs''
          where "x = \<lfloor>(cs'',True)\<rfloor>"
          by (auto elim!: JVM_CFG.cases)
        with v_in_def ex_edge show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Invoke M' n')
      show ?thesis
      proof (cases x)
        case None
        with v_in_def have False
          by (auto elim: Def.cases)
        thus ?thesis by simp
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
          by (cases x', fastforce)
        show ?thesis
        proof (cases xf)
          case True
          with v_in_def ex_edge show ?thesis
            by (auto elim!: Def.cases
                      elim: JVM_CFG.cases)
        next
          case [simp]: False
          have "length ST > n'"
          proof -
            from vn obtain T Ts mxs mxl "is" xt
              where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
              by (cases cs', auto)
            with vn
            have "pc < length is"
              by (cases cs', auto dest: sees_method_fun)
            from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
              by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
            with Invoke sees_M \<open>pc < length is\<close> wt show ?thesis
              by (fastforce simp: wt_method_def)
          qed
          moreover obtain STn where "STn = take n' ST" by fastforce
          moreover obtain STs where "STs = ST ! n'" by fastforce
          moreover obtain STr where "STr = drop (Suc n') ST" by fastforce
          ultimately have [simp]:" ST = STn@STs#STr \<and> length STn = n'"
            by (auto simp: id_take_nth_drop)
          from wt
          have "\<forall>i. i \<le> n' \<longrightarrow> Stk (length cs') (length ST - Suc i) \<in> Use P (sourcenode a)"
            by (fastforce intro: Use_Invoke_Stk_Update)
          with use_eq
          have
            "\<forall>i. i \<le> n' \<longrightarrow> state_val s (Stk (length cs') (length ST - Suc i)) =
                           state_val s' (Stk (length cs') (length ST - Suc i))"
            by (simp del: state_val.simps)
          hence stk_eq:
            "\<forall>i. i \<le> n' \<longrightarrow> state_val s (Stk (length cs') (i + length STr)) =
                           state_val s' (Stk (length cs') (i + length STr))"
            by (clarsimp, erule_tac x="n' - i" in allE, auto simp: add.commute)
          from ex_edge obtain C'
            where trg: "targetnode a = (_ (C',M',0)#(C, M, pc)#cs',None _)"
            by (fastforce elim: JVM_CFG.cases)
          with ex_edge stk_eq v_in_def wt
          show ?thesis
            by (auto elim!: Def.cases) (erule JVM_CFG.cases, auto simp: split_beta add.commute)
        qed
      qed
    next
      case [simp]: Return
      show ?thesis
      proof (cases x)
        case [simp]: None
        show ?thesis
        proof (cases cs')
          case Nil
          with v_in_def show ?thesis
            by (auto elim!: Def.cases)
        next
          case (Cons aa list)
          then obtain C' M' pc' cs'' where [simp]: "cs' = (C',M',pc')#cs''"
            by (cases aa, fastforce)
          from wt
          have "Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a)"
            by (fastforce intro: Use_Return_Stk)
          with use_eq
          have "state_val s (Stk (length cs') (length ST - 1)) =
                state_val s' (Stk (length cs') (length ST - 1))"
            by (simp del: state_val.simps)
          with v_in_def ex_edge wt show ?thesis
            by (auto elim!: Def.cases
                      elim: JVM_CFG.cases
                      simp: split_beta)
        qed
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case Pop
      with v_in_def ex_edge show ?thesis
        by (auto elim!: Def.cases elim: JVM_CFG.cases)
    next
      case [simp]: IAdd
      show ?thesis
      proof (cases x)
        case [simp]: None
        from wt
        have "Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (auto intro!: Use_IAdd_Stk)
        with use_eq
        have stk_top:"state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        from wt
        have "Stk (length cs') (length ST - 2) \<in> Use P (sourcenode a)"
          (is "?stk_snd \<in> ?Use")
          by (auto intro!: Use_IAdd_Stk)
        with use_eq
        have stk_snd:"state_val s ?stk_snd = state_val s' ?stk_snd"
          by (simp del: state_val.simps)
        with v_in_def ex_edge stk_top wt show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases
                    simp: split_beta)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (IfFalse b)
      show ?thesis
      proof (cases x)
        case [simp]: None
        from wt
        have "Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (auto intro!: Use_IfFalse_Stk)
        with use_eq
        have stk_top:"state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with v_in_def ex_edge wt show ?thesis
          by (auto elim!: Def.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: CmpEq
      show ?thesis
      proof (cases x)
        case [simp]: None
        have "Stk (length cs') (stkLength P C M pc - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (auto intro!: Use_CmpEq_Stk)
        with use_eq
        have stk_top:"state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        have "Stk (length cs') (stkLength P C M pc - 2) \<in> Use P (sourcenode a)"
          (is "?stk_snd \<in> ?Use")
          by (auto intro!: Use_CmpEq_Stk)
        with use_eq
        have stk_snd:"state_val s ?stk_snd = state_val s' ?stk_snd"
          by (simp del: state_val.simps)
        with v_in_def ex_edge stk_top wt show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case (Goto i)
      with ex_edge v_in_def show ?thesis
        by (auto elim!: Def.cases
                  elim: JVM_CFG.cases)
    next
      case [simp]: Throw
      show ?thesis
      proof (cases x)
        case [simp]: None
        have "Stk (length cs') (stkLength P C M pc - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (auto intro!: Use_Throw_Stk)
        with use_eq
        have stk_top:"state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with v_in_def show ?thesis
          by (auto elim!: Def.cases)
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
          by (cases x', fastforce)
        hence "xf \<longrightarrow> Stk (length cs') (stkLength P C M pc - 1) \<in> Use P (sourcenode a)"
          (is "xf \<longrightarrow> ?stk_top \<in> ?Use")
          by (fastforce intro: Use_Throw_Stk)
        with use_eq
        have stk_top:"xf \<longrightarrow> state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with v_in_def ex_edge show ?thesis
          by (auto elim!: Def.cases
                    elim: JVM_CFG.cases)
      qed
    qed
  next
    case Entry
    with vn v_in_def show ?thesis
      by -(erule Def.cases, auto)
  qed
qed

lemma CFG_edge_Uses_pred_equal:
  "\<lbrakk> valid_edge (P,C0,Main) a;
  pred (kind a) s; 
  \<forall>V \<in> Use P (sourcenode a). state_val s V = state_val s' V\<rbrakk>
  \<Longrightarrow> pred (kind a) s'"
proof -
  assume ve: "valid_edge (P,C0,Main) a"
    and pred: "pred (kind a) s"
    and use_eq: "\<forall>V\<in>Use P (sourcenode a). state_val s V = state_val s' V"
  obtain h stk loc where [simp]: "s = (h,stk,loc)" by (cases s, blast)
  obtain h' stk' loc' where [simp]: "s' = (h',stk',loc')" by (cases s', blast)
  from ve
  have vn: "valid_node (P,C0,Main) (sourcenode a)"
    and ex_edge: "(P,C0,Main) \<turnstile> (sourcenode a)-kind a\<rightarrow>(targetnode a)"
    by simp_all
  note P_wf = wf_jvmprog_is_wf [of P]
  show "pred (kind a) s'"
  proof (cases "sourcenode a")
    case [simp]: (Node cs x)
    from ve have "cs \<noteq> []"
      by (cases x, auto elim: JVM_CFG.cases)
    then obtain C M pc cs' where [simp]: "cs = (C, M, pc)#cs'" by (cases cs, fastforce+)
    from vn obtain ST LT where wt: "((P\<^bsub>\<Phi>\<^esub>) C M ! pc) = \<lfloor>(ST,LT)\<rfloor>"
      by (cases cs', (cases x, auto)+)
    show ?thesis
    proof (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
      case (Load nat)
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case (Store nat)
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case (Push val)
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case [simp]: (New Cl)
      show ?thesis
      proof (cases x)
        case None
        hence "\<forall>addr. HeapVar addr \<in> Use P (sourcenode a)"
          by (auto intro!: Use_New)
        with use_eq have "\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr)"
          by (simp del: state_val.simps)
        hence "h = h'"
          by (auto intro: ext)
        with ex_edge pred show ?thesis
          by (auto elim!: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Getfield Fd Cl)
      have "ST \<noteq> []"
      proof -
        from vn obtain T Ts mxs mxl "is" xt
          where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
          by (cases cs', (cases x, auto)+)
        with vn
        have "pc < length is"
          by (cases cs', (cases x, auto dest: sees_method_fun)+)
        from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Getfield wt sees_M \<open>pc < length is\<close> show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      then obtain ST1 STr where [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases x)
        case [simp]: None
        from wt
        have "Stk (length cs') (length ST - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_Getfield_Stk)
        with use_eq have "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with ex_edge pred wt show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Putfield Fd Cl)
      have "length ST > 1"
      proof -
        from vn obtain T Ts mxs mxl "is" xt
          where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
          by (cases cs', (cases x, auto)+)
        with vn
        have "pc < length is"
          by (cases cs', (cases x, auto dest: sees_method_fun)+)
        from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Putfield wt sees_M \<open>pc < length is\<close> show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      then obtain ST1 STr' where "ST = ST1#STr' \<and> STr' \<noteq> []" by (cases ST, fastforce+)
      then obtain ST2 STr where [simp]: "ST = ST1#ST2#STr" by (cases STr', fastforce+)
      show ?thesis
      proof (cases x)
        case [simp]: None
        with wt
        have "Stk (length cs') (length ST - 2) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_Putfield_Stk_Pred)
        with use_eq have "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with ex_edge pred wt show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Checkcast Cl)
      have "ST \<noteq> []"
      proof -
        from vn obtain T Ts mxs mxl "is" xt
          where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
          by (cases cs', (cases x, auto)+)
        with vn
        have "pc < length is"
          by (cases cs', (cases x, auto dest: sees_method_fun)+)
        from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Checkcast wt sees_M \<open>pc < length is\<close> show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      then obtain ST1 STr where [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases x)
        case [simp]: None
        from wt
        have "Stk (length cs') (stkLength P C M pc - Suc 0) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_Checkcast_Stk)
        with use_eq
        have stk_top: "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        have "\<forall>addr. HeapVar addr \<in> Use P (sourcenode a)"
          by (fastforce intro: Use_Checkcast_Heap)
        with use_eq
        have "\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr)"
          by (simp del: state_val.simps)
        hence "h = h'"
          by (auto intro: ext)
        with ex_edge stk_top pred wt show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case [simp]: (Invoke M' n')
      have "length ST > n'"
      proof -
        from vn obtain T Ts mxs mxl "is" xt
          where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
          by (cases cs', (cases x, auto)+)
        with vn
        have "pc < length is"
          by (cases cs', (cases x, auto dest: sees_method_fun)+)
        from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Invoke wt sees_M \<open>pc < length is\<close> show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      moreover obtain STn where "STn = take n' ST" by fastforce
      moreover obtain STs where "STs = ST ! n'" by fastforce
      moreover obtain STr where "STr = drop (Suc n') ST" by fastforce
      ultimately have [simp]:" ST = STn@STs#STr \<and> length STn = n'"
        by (auto simp: id_take_nth_drop)
      show ?thesis
      proof (cases x)
        case [simp]: None
        with wt
        have "Stk (length cs') (stkLength P C M pc - Suc n') \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_Invoke_Stk_Pred)
        with use_eq
        have stk_top: "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        have "\<forall>addr. HeapVar addr \<in> Use P (sourcenode a)"
          by (fastforce intro: Use_Invoke_Heap_Pred)
        with use_eq
        have "\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr)"
          by (simp del: state_val.simps)
        hence "h = h'"
          by (auto intro: ext)
        with ex_edge stk_top pred wt show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case Return
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case Pop
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case IAdd
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case [simp]: (IfFalse b)
      show ?thesis
      proof (cases x)
        case [simp]: None
        have "Stk (length cs') (stkLength P C M pc - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_IfFalse_Stk)
        with use_eq
        have "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        with ex_edge pred wt show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    next
      case CmpEq
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case (Goto i)
      with ex_edge show ?thesis
        by (auto elim: JVM_CFG.cases)
    next
      case [simp]: Throw
      have "ST \<noteq> []"
      proof -
        from vn obtain T Ts mxs mxl "is" xt
          where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
          by (cases cs', (cases x, auto)+)
        with vn
        have "pc < length is"
          by (cases cs', (cases x, auto dest: sees_method_fun)+)
        from P_wf sees_M have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
          by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
        with Throw wt sees_M \<open>pc < length is\<close> show ?thesis
          by (fastforce simp: wt_method_def)
      qed
      then obtain ST1 STr where [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases x)
        case [simp]: None
        from wt
        have "Stk (length cs') (stkLength P C M pc - 1) \<in> Use P (sourcenode a)"
          (is "?stk_top \<in> ?Use")
          by (fastforce intro: Use_Throw_Stk)
        with use_eq
        have stk_top: "state_val s ?stk_top = state_val s' ?stk_top"
          by (simp del: state_val.simps)
        have "\<forall>addr. HeapVar addr \<in> Use P (sourcenode a)"
          by (fastforce intro: Use_Throw_Heap)
        with use_eq
        have "\<forall>addr. state_val s (HeapVar addr) = state_val s' (HeapVar addr)"
          by (simp del: state_val.simps)
        hence "h = h'"
          by (auto intro: ext)
        with ex_edge pred stk_top wt show ?thesis
          by (auto elim!: JVM_CFG.cases)
      next
        case (Some x')
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      qed
    qed
  next
    case Entry
    with ex_edge pred show ?thesis
      by (auto elim: JVM_CFG.cases)
  qed
qed


lemma edge_no_Def_equal:
  "\<lbrakk> valid_edge (P, C0, Main) a;
     V \<notin> Def P (sourcenode a) \<rbrakk>
  \<Longrightarrow> state_val (transfer (kind a) s) V = state_val s V"
proof -
  assume ve:"valid_edge (P, C0, Main) a"
    and v_not_def: "V \<notin> Def P (sourcenode a)"
  obtain h stk loc where [simp]: "(s::state) = (h, stk, loc)" by (cases s, blast)
  from ve have vn: "valid_node (P, C0, Main) (sourcenode a)"
    and ex_edge: "(P, C0, Main) \<turnstile> (sourcenode a)-kind a\<rightarrow>(targetnode a)"
    by simp_all
  show "state_val (transfer (kind a) s) V = state_val s V"
  proof (cases "sourcenode a")
    case [simp]: (Node cs x)
    with ve have "cs \<noteq> []"
      by (cases x, auto elim: JVM_CFG.cases)
    then obtain C M pc cs' where [simp]: "cs = (C, M, pc)#cs'" by (cases cs, fastforce+)
    with vn obtain ST LT where wt: "((P\<^bsub>\<Phi>\<^esub>) C M ! pc) = \<lfloor>(ST,LT)\<rfloor>"
      by (cases cs', (cases x, auto)+)
    show ?thesis
    proof (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
      case [simp]: (Load nat)
      from ex_edge have "x = None"
        by (auto elim: JVM_CFG.cases)
      with v_not_def have "V \<noteq> Stk (length cs') (stkLength P C M pc)"
        by (auto intro!: Def_Load)
      with ex_edge show ?thesis
        by (auto elim!: JVM_CFG.cases, cases V, auto)
    next
      case [simp]: (Store nat)
      with ex_edge have "x = None"
        by (auto elim: JVM_CFG.cases)
      with v_not_def have "V \<noteq> Loc (length cs') nat"
        by (auto intro!: Def_Store)
      with ex_edge show ?thesis
        by (auto elim!: JVM_CFG.cases, cases V, auto)
    next
      case [simp]: (Push val)
      with ex_edge have "x = None"
        by (auto elim: JVM_CFG.cases)
      with v_not_def have "V \<noteq> Stk (length cs') (stkLength P C M pc)"
        by (auto intro!: Def_Push)
      with ex_edge show ?thesis
        by (auto elim!: JVM_CFG.cases, cases V, auto)
    next
      case [simp]: (New Cl)
      show ?thesis
      proof (cases x)
        case None
        with ex_edge show ?thesis
          by (auto elim: JVM_CFG.cases)
      next
        case (Some x')
        then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
          by (cases x', fastforce)
        with ex_edge v_not_def show ?thesis
          apply (auto elim!: JVM_CFG.cases)
            apply (cases V, auto intro!: Def_New_Normal_Stk Def_New_Normal_Heap)
           by (cases V, auto intro!: Def_Exc_Stk)+
     qed
   next
     case [simp]: (Getfield F Cl)
     show ?thesis
     proof (cases x)
       case None
       with ex_edge show ?thesis
         by (auto elim: JVM_CFG.cases)
     next
       case (Some x')
       then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
         by (cases x', fastforce)
       with ex_edge v_not_def show ?thesis
         apply (auto elim!: JVM_CFG.cases simp: split_beta)
           apply (cases V, auto intro!: Def_Getfield_Stk)
          by (cases V, auto intro!: Def_Exc_Stk)+
     qed
   next
     case [simp]: (Putfield Fd Cl)
     show ?thesis
     proof (cases x)
       case None
       with ex_edge show ?thesis
         by (auto elim: JVM_CFG.cases)
     next
       case (Some x')
       then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
         by (cases x', fastforce)
       with ex_edge v_not_def show ?thesis
         apply (auto elim!: JVM_CFG.cases simp: split_beta)
           apply (cases V, auto intro!: Def_Putfield_Heap)
          by (cases V, auto intro!: Def_Exc_Stk)+
     qed
   next
     case [simp]: (Checkcast Cl)
     show ?thesis
     proof (cases x)
       case None
       with ex_edge show ?thesis
         by (auto elim: JVM_CFG.cases)
     next
       case (Some x')
       then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
         by (cases x', fastforce)
       with ex_edge v_not_def show ?thesis
         apply (auto elim!: JVM_CFG.cases)
          by (cases V, auto intro!: Def_Exc_Stk)+
     qed
   next
     case [simp]: (Invoke M' n')
     show ?thesis
     proof (cases x)
       case None
       with ex_edge show ?thesis
         by (auto elim: JVM_CFG.cases)
     next
       case (Some x')
       then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
         by (cases x', fastforce)
       from ex_edge v_not_def show ?thesis
         apply (auto elim!: JVM_CFG.cases)
           apply (cases V, auto intro!: Def_Invoke_Loc)
          by (cases V, auto intro!: Def_Exc_Stk)+
     qed
   next
     case Return
     with ex_edge v_not_def show ?thesis
       apply (auto elim!: JVM_CFG.cases)
       by (cases V, auto intro!: Def_Return_Stk)
   next
     case Pop
     with ex_edge show ?thesis
       by (auto elim: JVM_CFG.cases)
   next
     case IAdd
     with ex_edge v_not_def show ?thesis
       apply (auto elim!: JVM_CFG.cases)
       by (cases V, auto intro!: Def_IAdd_Stk)
   next
     case (IfFalse b)
     with ex_edge show ?thesis
       by (auto elim: JVM_CFG.cases)
   next
     case CmpEq
     with ex_edge v_not_def show ?thesis
       apply (auto elim!: JVM_CFG.cases)
       by (cases V, auto intro!: Def_CmpEq_Stk)
   next
     case (Goto i)
     with ex_edge show ?thesis
       by (auto elim: JVM_CFG.cases)
   next
     case [simp]: Throw
     show ?thesis
     proof (cases x)
       case None
       with ex_edge show ?thesis
         by (auto elim: JVM_CFG.cases)
     next
       case (Some x')
       then obtain cs'' xf where [simp]: "x = \<lfloor>(cs'',xf)\<rfloor>"
         by (cases x', fastforce)
       from ex_edge v_not_def show ?thesis
         apply (auto elim!: JVM_CFG.cases)
          by (cases V, auto intro!: Def_Exc_Stk)+
      qed
    qed
  next
    case Entry
    with ex_edge show ?thesis
      by (auto elim: JVM_CFG.cases)
  qed
qed

interpretation JVM_CFG_wf: CFG_wf
  "sourcenode" "targetnode" "kind" "valid_edge prog" "(_Entry_)"
  "Def (fst prog)" "Use (fst prog)" "state_val"
  for prog
proof (unfold_locales)
  show "Def (fst prog) (_Entry_) = {} \<and> Use (fst prog) (_Entry_) = {}"
    by (auto elim: Def.cases Use.cases)
next
  fix a V s
  assume ve:"valid_edge prog a"
    and v_not_def: "V \<notin> Def (fst prog) (sourcenode a)"
  thus "state_val (transfer (kind a) s) V = state_val s V"
    by -(cases prog,
    rule edge_no_Def_equal [of "fst prog" "fst (snd prog)" "snd (snd prog)"], auto)
next
  fix a s s'
  assume ve: "valid_edge prog a"
    and use_eq: "\<forall>V\<in>Use (fst prog) (sourcenode a). state_val s V = state_val s' V"
  thus "\<forall>V\<in>Def (fst prog) (sourcenode a).
    state_val (transfer (kind a) s) V = state_val (transfer (kind a) s') V"
    by -(cases prog,
      rule edge_transfer_uses_only_Use [of "fst prog" "fst(snd prog)" "snd(snd prog)"], auto)
next
  fix a s s'
  assume ve: "valid_edge prog a"
    and pred: "pred (kind a) s"
    and use_eq: "\<forall>V\<in>Use (fst prog) (sourcenode a). state_val s V = state_val s' V"
  thus "pred (kind a) s'"
    by -(cases prog,
      rule CFG_edge_Uses_pred_equal [of "fst prog" "fst(snd prog)" "snd(snd prog)"], auto)
next
  fix a a'
  assume ve_a: "valid_edge prog a"
    and ve_a': "valid_edge prog a'"
    and src_eq: "sourcenode a = sourcenode a'"
    and trg_neq: "targetnode a \<noteq> targetnode a'"
  hence "prog \<turnstile> (sourcenode a)-kind a\<rightarrow>(targetnode a)"
    and "prog \<turnstile> (sourcenode a')-kind a'\<rightarrow>(targetnode a')"
    by simp_all
  with src_eq trg_neq
  show "\<exists>Q Q'. kind a = (Q)\<^sub>\<surd> \<and> kind a' = (Q')\<^sub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
    apply (cases prog, auto)
    apply (erule JVM_CFG.cases, erule_tac [!] JVM_CFG.cases)
    (* This takes veeery long! *)
    by simp_all
qed

interpretation JVM_CFGExit_wf: CFGExit_wf
  "sourcenode" "targetnode" "kind" "valid_edge prog" "(_Entry_)"
  "Def (fst prog)" "Use (fst prog)" "state_val" "(_Exit_)"
proof
  show "Def (fst prog) (_Exit_) = {} \<and> Use (fst prog) (_Exit_) = {}"
    by(fastforce elim:Def.cases Use.cases)
qed

  
end
