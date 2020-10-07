theory JVMPostdomination imports JVMInterpretation "../StaticInter/Postdomination" begin

context CFG begin

lemma vp_snocI:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<surd>* n'; n' -[a]\<rightarrow>* n''; \<forall>Q p ret fs. kind a \<noteq> Q\<hookleftarrow>\<^bsub>p\<^esub>ret \<rbrakk> \<Longrightarrow> n -as @ [a]\<rightarrow>\<^sub>\<surd>* n''"
  by (cases "kind a") (auto intro: path_Append valid_path_aux_Append simp: vp_def valid_path_def)

lemma valid_node_cases' [case_names Source Target, consumes 1]:
  "\<lbrakk> valid_node n; \<And>e. \<lbrakk> valid_edge e; sourcenode e = n \<rbrakk> \<Longrightarrow> thesis;
  \<And>e. \<lbrakk> valid_edge e; targetnode e = n \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
  by (auto simp: valid_node_def)

end

lemma disjE_strong: "\<lbrakk>P \<or> Q; P \<Longrightarrow> R; \<lbrakk>Q; \<not> P\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

lemmas path_intros [intro] = JVMCFG_Interpret.path.Cons_path JVMCFG_Interpret.path.empty_path
declare JVMCFG_Interpret.vp_snocI [intro]
declare JVMCFG_Interpret.valid_node_def [simp add]
  valid_edge_def [simp add]
  JVMCFG_Interpret.intra_path_def [simp add]

abbreviation vp_snoc :: "wf_jvmprog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cfg_edge list \<Rightarrow> cfg_node
  \<Rightarrow> (var, val, cname \<times> mname \<times> pc, cname \<times> mname) edge_kind \<Rightarrow> cfg_node \<Rightarrow> bool"
  where "vp_snoc P C0 Main as n ek n'
  \<equiv> JVMCFG_Interpret.valid_path' P C0 Main
  (ClassMain P, MethodMain P, None, Enter) (as @ [(n,ek,n')]) n'"

lemma
  "(P, C0, Main) \<turnstile> (C, M, pc, nt) -ek\<rightarrow> (C', M', pc', nt')
  \<Longrightarrow> (\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge (P, C0, Main))
  (get_return_edges P) (ClassMain P, MethodMain P, None, Enter) as (C, M, pc, nt)) \<and>
  (\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge (P, C0, Main))
  (get_return_edges P) (ClassMain P, MethodMain P, None, Enter) as (C', M', pc', nt'))"
  and valid_Entry_path: "(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, pc, nt)
  \<Longrightarrow> \<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge (P, C0, Main))
  (get_return_edges P) (ClassMain P, MethodMain P, None, Enter) as (C, M, pc, nt)"
proof (induct rule: JVMCFG_reachable_inducts)
  case (Entry_reachable P C0 Main)
  hence "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) [] (ClassMain P, MethodMain P, None, Enter)"
    by (fastforce intro: JVMCFG_Interpret.intra_path_vp Method_LTrue
      JVMCFG_reachable.Entry_reachable)
  thus ?case by blast
next
  case (reachable_step P C0 Main C M pc nt ek C' M' pc' nt')
  thus ?case by simp
next
  case (Main_to_Call P C0 Main)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter)\<close>
  have "vp_snoc P C0 Main as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter) \<Up>id
    (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
    by (fastforce intro: JVMCFG_reachable.Main_to_Call)
  ultimately show ?case by blast
next
  case (Main_Call_LFalse P C0 Main)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)\<close>
  have "vp_snoc P C0 Main as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal) (\<lambda>s. False)\<^sub>\<surd>
    (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)"
    by (fastforce intro: JVMCFG_reachable.Main_Call_LFalse)
  ultimately show ?case by blast
next
  case (Main_Call P C0 Main T mxs mxl\<^sub>0 "is" xt D initParams ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)\<close>
    \<open>PROG P \<turnstile> C0 sees Main: []\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D\<close>
    \<open>initParams = [\<lambda>s. s Heap, \<lambda>s. \<lfloor>Value Null\<rfloor>]\<close>
    \<open>ek = \<lambda>(s, ret). True:(ClassMain P, MethodMain P, 0)\<hookrightarrow>\<^bsub>(D, Main)\<^esub>initParams\<close>
  have "vp_snoc P C0 Main as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)
    ((\<lambda>(s, ret). True):(ClassMain P, MethodMain P, 0)\<hookrightarrow>\<^bsub>(D, Main)\<^esub>[(\<lambda>s. s Heap),(\<lambda>s. \<lfloor>Value Null\<rfloor>)])
    (D, Main, None, Enter)"
    by (fastforce intro: JVMCFG_reachable.Main_Call)
  ultimately show ?case by blast
next
  case (Main_Return_to_Exit P C0 Main)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, nodeType.Return)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, nodeType.Return)\<close>
  have "vp_snoc P C0 Main as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, nodeType.Return) \<Up>id
    (ClassMain P, MethodMain P, None, nodeType.Return)"
    by (fastforce intro: JVMCFG_reachable.Main_Return_to_Exit)
  ultimately show ?case by blast
next
  case (Method_LFalse P C0 Main C M)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, None, Enter)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Enter)\<close>
  have "vp_snoc P C0 Main as (C, M, None, Enter) (\<lambda>s. False)\<^sub>\<surd> (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.Method_LFalse)
  ultimately show ?case by blast
next
  case (Method_LTrue P C0 Main C M)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, None, Enter)"
    by blast
  moreover with \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Enter)\<close>
  have "vp_snoc P C0 Main as (C, M, None, Enter) (\<lambda>s. True)\<^sub>\<surd> (C, M, \<lfloor>0\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.Method_LTrue)
  ultimately show ?case by blast
next
  case (CFG_Load C P C0 Main M pc n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Load n\<close>
    \<open>ek = \<Up>\<lambda>s. s(Stack (stkLength (P, C, M) pc) := s (Local n))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Load)
  ultimately show ?case by blast
next
  case (CFG_Store C P C0 Main M pc n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Store n\<close>
    \<open>ek = \<Up>\<lambda>s. s(Local n := s (Stack (stkLength (P, C, M) pc - 1)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Store)
  ultimately show ?case by blast
next
  case (CFG_Push C P C0 Main M pc v ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Push v\<close>
    \<open>ek = \<Up>\<lambda>s. s(Stack (stkLength (P, C, M) pc) \<mapsto> Value v)\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Push)
  ultimately show ?case by blast
next
  case (CFG_Pop C P C0 Main M pc ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Pop\<close> \<open>ek = \<Up>id\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Pop)
  ultimately show ?case by blast
next
  case (CFG_IAdd C P C0 Main M pc ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = IAdd\<close>
    \<open>ek = \<Up>\<lambda>s. let i1 = the_Intg (stkAt s (stkLength (P, C, M) pc - 1));
                   i2 = the_Intg (stkAt s (stkLength (P, C, M) pc - 2))
    in s(Stack (stkLength (P, C, M) pc - 2) \<mapsto> Value (Intg (i1 + i2)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_IAdd)
  ultimately show ?case by blast
next
  case (CFG_Goto C P C0 Main M pc i)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Goto i\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) (\<lambda>s. True)\<^sub>\<surd> (C, M, \<lfloor>nat (int pc + i)\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Goto)
  ultimately show ?case by blast
next
  case (CFG_CmpEq C P C0 Main M pc ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = CmpEq\<close>
    \<open>ek = \<Up>\<lambda>s. let e1 = stkAt s (stkLength (P, C, M) pc - 1);
                   e2 = stkAt s (stkLength (P, C, M) pc - 2)
    in s(Stack (stkLength (P, C, M) pc - 2) \<mapsto> Value (Bool (e1 = e2)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_CmpEq)
  ultimately show ?case by blast
next
  case (CFG_IfFalse_False C P C0 Main M pc i ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = IfFalse i\<close> \<open>i \<noteq> 1\<close>
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) = Bool False)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>nat (int pc + i)\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_IfFalse_False)
  ultimately show ?case by blast
next
  case (CFG_IfFalse_True C P C0 Main M pc i ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = IfFalse i\<close>
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) \<noteq> Bool False \<or> i = 1)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_IfFalse_True)
  ultimately show ?case by blast
next
  case (CFG_New_Check_Normal C P C0 Main M pc Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = New Cl\<close> \<open>ek = (\<lambda>s. new_Addr (heap_of s) \<noteq> None)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by (fastforce intro: JVMCFG_reachable.CFG_New_Check_Normal)
  ultimately show ?case by blast
next
  case (CFG_New_Check_Exceptional C P C0 Main M pc Cl pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open> instrs_of (PROG P) C M ! pc = New Cl\<close>
    \<open>pc' = (case match_ex_table (PROG P) OutOfMemory pc (ex_table_of (PROG P) C M) of None \<Rightarrow> None
    | \<lfloor>(pc'', d)\<rfloor> \<Rightarrow> \<lfloor>pc''\<rfloor>)\<close> \<open>ek = (\<lambda>s. new_Addr (heap_of s) = None)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_New_Check_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_New_Update C P C0 Main M pc Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close>
    \<open> instrs_of (PROG P) C M ! pc = New Cl\<close>
    \<open> ek = \<Up>\<lambda>s. let a = the (new_Addr (heap_of s)) in
    s(Heap \<mapsto> Hp (heap_of s(a \<mapsto> blank (PROG P) Cl)),
      Stack (stkLength (P, C, M) pc) \<mapsto> Value (Addr a))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Normal) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_New_Update)
  ultimately show ?case by blast
next
  case (CFG_New_Exceptional_prop C P C0 Main M pc Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = New Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt OutOfMemory)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_New_Exceptional_prop)
  ultimately show ?case by blast
next
  case (CFG_New_Exceptional_handle C P C0 Main M pc pc' Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = New Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (Addr (addr_of_sys_xcpt OutOfMemory)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_New_Exceptional_handle)
  ultimately show ?case by blast
next
  case (CFG_Getfield_Check_Normal C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) \<noteq> Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by (fastforce intro: JVMCFG_reachable.CFG_Getfield_Check_Normal)
  ultimately show ?case by blast
next
  case (CFG_Getfield_Check_Exceptional C P C0 Main M pc F Cl pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    \<open>pc' = (case match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) of None \<Rightarrow> None
    | \<lfloor>(pc'', d)\<rfloor> \<Rightarrow> \<lfloor>pc''\<rfloor>)\<close> \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) = Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Getfield_Check_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_Getfield_Update C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. let (D, fs) = the (heap_of s (the_Addr (stkAt s (stkLength (P, C, M) pc - 1))))
    in s(Stack (stkLength (P, C, M) pc - 1) \<mapsto> Value (the (fs (F, Cl))))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Normal) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Getfield_Update)
  ultimately show ?case by blast
next
  case (CFG_Getfield_Exceptional_prop C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Getfield_Exceptional_prop)
  ultimately show ?case by blast
next
  case (CFG_Getfield_Exceptional_handle C P C0 Main M pc pc' F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Getfield_Exceptional_handle)
  ultimately show ?case by blast
next
  case (CFG_Putfield_Check_Normal C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 2) \<noteq> Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by (fastforce intro: JVMCFG_reachable.CFG_Putfield_Check_Normal)
  ultimately show ?case by blast
next
  case (CFG_Putfield_Check_Exceptional C P C0 Main M pc F Cl pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    \<open>pc' = (case match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) of None \<Rightarrow> None
    | \<lfloor>(pc'', d)\<rfloor> \<Rightarrow> \<lfloor>pc''\<rfloor>)\<close> \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 2) = Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Putfield_Check_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_Putfield_Update C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
    r = stkAt s (stkLength (P, C, M) pc - 2);
    a = the_Addr r; (D, fs) = the (heap_of s a); h' = heap_of s(a \<mapsto> (D, fs((F, Cl) \<mapsto> v)))
    in s(Heap \<mapsto> Hp h')\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Normal) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Putfield_Update)
  ultimately show ?case by blast
next
  case (CFG_Putfield_Exceptional_prop C P C0 Main M pc F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Putfield_Exceptional_prop)
  ultimately show ?case by blast
next
  case (CFG_Putfield_Exceptional_handle C P C0 Main M pc pc' F Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Putfield_Exceptional_handle)
  ultimately show ?case by blast
next
  case (CFG_Checkcast_Check_Normal C P C0 Main M pc Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
    \<open>ek = (\<lambda>s. cast_ok (PROG P) Cl (heap_of s) (stkAt s (stkLength (P, C, M) pc - 1)))\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Checkcast_Check_Normal)
  ultimately show ?case by blast
next
  case (CFG_Checkcast_Check_Exceptional C P C0 Main M pc Cl pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
    \<open>pc' = (case match_ex_table (PROG P) ClassCast pc (ex_table_of (PROG P) C M) of None \<Rightarrow> None
    | \<lfloor>(pc'', d)\<rfloor> \<Rightarrow> \<lfloor>pc''\<rfloor>)\<close>
    \<open>ek = (\<lambda>s. \<not> cast_ok (PROG P) Cl (heap_of s) (stkAt s (stkLength (P, C, M) pc - 1)))\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Checkcast_Check_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_Checkcast_Exceptional_prop C P C0 Main M pc Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt ClassCast)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Checkcast_Exceptional_prop)
  ultimately show ?case by blast
next
  case (CFG_Checkcast_Exceptional_handle C P C0 Main M pc pc' Cl ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (Addr (addr_of_sys_xcpt ClassCast)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Checkcast_Exceptional_handle)
  ultimately show ?case by blast
next
  case (CFG_Throw_Check C P C0 Main M pc pc' Exc d ek)
  then obtain as where path_src: "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  from \<open>pc' = None \<or> match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(the pc', d)\<rfloor>\<close>
  show ?case
  proof (elim disjE_strong)
    assume "pc' = None"
    with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
    \<open>ek = (\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
           Cl = if v = Null then NullPointer else cname_of (heap_of s) (the_Addr v)
       in case pc' of None \<Rightarrow> match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = None
          | \<lfloor>pc''\<rfloor> \<Rightarrow>
              \<exists>d. match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = \<lfloor>(pc'', d)\<rfloor>)\<^sub>\<surd>\<close>
    have "(P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -
      (\<lambda>s. (stkAt s (stkLength (P, C, M) pc - Suc 0) = Null \<longrightarrow>
        match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) = None) \<and>
        (stkAt s (stkLength (P, C, M) pc - Suc 0) \<noteq> Null \<longrightarrow>
          match_ex_table (PROG P) (cname_of (heap_of s)
           (the_Addr (stkAt s (stkLength (P, C, M) pc - Suc 0)))) pc (ex_table_of (PROG P) C M) =
      None))\<^sub>\<surd>\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
      by -(erule JVMCFG_reachable.CFG_Throw_Check, simp_all)
    with path_src \<open>pc' = None\<close> \<open>ek = (\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
           Cl = if v = Null then NullPointer else cname_of (heap_of s) (the_Addr v)
       in case pc' of None \<Rightarrow> match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = None
          | \<lfloor>pc''\<rfloor> \<Rightarrow>
              \<exists>d. match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = \<lfloor>(pc'', d)\<rfloor>)\<^sub>\<surd>\<close>
    have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
      by (fastforce intro: JVMCFG_reachable.CFG_Throw_Check)
    with path_src \<open>pc' = None\<close> show ?thesis by blast
  next
    assume met: "match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(the pc', d)\<rfloor>"
      and pc': "pc' \<noteq> None"
    with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
    \<open>ek = (\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
           Cl = if v = Null then NullPointer else cname_of (heap_of s) (the_Addr v)
       in case pc' of None \<Rightarrow> match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = None
          | \<lfloor>pc''\<rfloor> \<Rightarrow>
              \<exists>d. match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = \<lfloor>(pc'', d)\<rfloor>)\<^sub>\<surd>\<close>
    have "(P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -
      (\<lambda>s. (stkAt s (stkLength (P, C, M) pc - Suc 0) = Null \<longrightarrow>
                                    (\<exists>d. match_ex_table (PROG P) NullPointer pc
                                          (ex_table_of (PROG P) C M) =
                                         \<lfloor>(the pc', d)\<rfloor>)) \<and>
                                   (stkAt s (stkLength (P, C, M) pc - Suc 0) \<noteq> Null \<longrightarrow>
                                    (\<exists>d. match_ex_table (PROG P)
                                          (cname_of (heap_of s)
                                            (the_Addr
                                              (stkAt s (stkLength (P, C, M) pc - Suc 0))))
                                          pc (ex_table_of (PROG P) C M) =
                                         \<lfloor>(the pc', d)\<rfloor>)))\<^sub>\<surd>\<rightarrow>
      (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>the pc'\<rfloor> Enter)"
      by -(rule JVMCFG_reachable.CFG_Throw_Check, simp_all)
    with met pc' path_src \<open>ek = (\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
           Cl = if v = Null then NullPointer else cname_of (heap_of s) (the_Addr v)
       in case pc' of None \<Rightarrow> match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = None
          | \<lfloor>pc''\<rfloor> \<Rightarrow>
              \<exists>d. match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = \<lfloor>(pc'', d)\<rfloor>)\<^sub>\<surd>\<close>
    have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
      by (fastforce intro: JVMCFG_reachable.CFG_Throw_Check)
    with path_src show ?thesis by blast
  qed
next
  case (CFG_Throw_prop C P C0 Main M pc ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (stkAt s (stkLength (P, C, M) pc - 1)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, nodeType.Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Throw_prop)
  ultimately show ?case by blast
next
  case (CFG_Throw_handle C P C0 Main M pc pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>pc' \<noteq> length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (stkAt s (stkLength (P, C, M) pc - 1)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Throw_handle)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Check_NP_Normal C P C0 Main M pc M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> 
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - Suc n) \<noteq> Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Check_NP_Normal)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Check_NP_Exceptional C P C0 Main M pc M' n pc' ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>pc' = (case match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) of None \<Rightarrow> None
    | \<lfloor>(pc'', d)\<rfloor> \<Rightarrow> \<lfloor>pc''\<rfloor>)\<close>
    \<open>ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - Suc n) = Null)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Check_NP_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_Invoke_NP_prop C P C0 Main M pc M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_NP_prop)
  ultimately show ?case by blast
next
  case (CFG_Invoke_NP_handle C P C0 Main M pc pc' M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None)(Stack (stkLength (P, C, M) pc' - 1) \<mapsto>
    Value (Addr (addr_of_sys_xcpt NullPointer)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_NP_handle)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Call C P C0 Main M pc M' n ST LT D' Ts T mxs mxl\<^sub>0 "is" xt D Q paramDefs ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> \<open>TYPING P C M ! pc = \<lfloor>(ST, LT)\<rfloor>\<close>
    \<open>ST ! n = Class D'\<close> \<open>PROG P \<turnstile> D' sees M': Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D\<close>
    \<open>Q = (\<lambda>(s, ret). let r = stkAt s (stkLength (P, C, M) pc - Suc n);
              C' = cname_of (heap_of s) (the_Addr r) in D = fst (method (PROG P) C' M'))\<close>
    \<open>paramDefs = (\<lambda>s. s Heap) # (\<lambda>s. s (Stack (stkLength (P, C, M) pc - Suc n))) #
    rev (map (\<lambda>i s. s (Stack (stkLength (P, C, M) pc - Suc i))) [0..<n])\<close>
    \<open>ek = Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D, M')\<^esub>paramDefs\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Normal) ek (D, M', None, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Call)
  ultimately show ?case by blast
next
  case (CFG_Invoke_False C P C0 Main M pc M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Normal)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> \<open>ek = (\<lambda>s. False)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Normal) ek (C, M, \<lfloor>pc\<rfloor>, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_False)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Return_Check_Normal C P C0 Main M pc M' n ST LT ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, nodeType.Return)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, nodeType.Return)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> \<open>TYPING P C M ! pc = \<lfloor>(ST, LT)\<rfloor>\<close>
    \<open>ST ! n \<noteq> NT\<close> \<open>ek = (\<lambda>s. s Exception = None)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Return) ek (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Return_Check_Normal)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Return_Check_Exceptional C P C0 Main M pc M' n Exc pc' diff ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, nodeType.Return)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, nodeType.Return)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', diff)\<rfloor>\<close>
    \<open>pc' \<noteq> length (instrs_of (PROG P) C M)\<close>
    \<open>ek = (\<lambda>s. \<exists>v d. s Exception = \<lfloor>v\<rfloor> \<and>
             match_ex_table (PROG P) (cname_of (heap_of s) (the_Addr (the_Value v))) pc
              (ex_table_of (PROG P) C M) = \<lfloor>(pc', d)\<rfloor>)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Return) ek (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Return_Check_Exceptional)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Return_Exceptional_handle C P C0 Main M pc pc' M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> nodeType.Return)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> nodeType.Return)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>ek = \<Up>\<lambda>s. s(Exception := None, Stack (stkLength (P, C, M) pc' - 1) := s Exception)\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return) ek (C, M, \<lfloor>pc'\<rfloor>, Enter)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Return_Exceptional_handle)
  ultimately show ?case by blast
next
  case (CFG_Invoke_Return_Exceptional_prop C P C0 Main M pc M' n ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, nodeType.Return)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, nodeType.Return)\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    \<open>ek = (\<lambda>s. \<exists>v. s Exception = \<lfloor>v\<rfloor> \<and>
           match_ex_table (PROG P) (cname_of (heap_of s) (the_Addr (the_Value v))) pc
            (ex_table_of (PROG P) C M) = None)\<^sub>\<surd>\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Return) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Invoke_Return_Exceptional_prop)
  ultimately show ?case by blast
next
  case (CFG_Return C P C0 Main M pc ek)
  then obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
    (ClassMain P, MethodMain P, None, Enter) as (C, M, \<lfloor>pc\<rfloor>, Enter)"
    by blast
  moreover with \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close>
    \<open>instrs_of (PROG P) C M ! pc = instr.Return\<close>
    \<open>ek = \<Up>\<lambda>s. s(Stack 0 := s (Stack (stkLength (P, C, M) pc - 1)))\<close>
  have "vp_snoc P C0 Main as (C, M, \<lfloor>pc\<rfloor>, Enter) ek (C, M, None, Return)"
    by (fastforce intro: JVMCFG_reachable.CFG_Return)
  ultimately show ?case by blast
next
  case (CFG_Return_from_Method P C0 Main C M C' M' pc' Q' ps Q stateUpdate ek)
  from \<open>(P, C0, Main) \<turnstile> (C', M', \<lfloor>pc'\<rfloor>, Normal) -Q':(C', M', pc')\<hookrightarrow>\<^bsub>(C, M)\<^esub>ps\<rightarrow> (C, M, None, Enter)\<close>
  show ?case
  proof cases
    case Main_Call
    with CFG_Return_from_Method obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
      (ClassMain P, MethodMain P, None, Enter) as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
      by blast
    moreover with Main_Call have "vp_snoc P C0 Main as (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)
      (\<lambda>s. False)\<^sub>\<surd> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)"
      by (fastforce intro: Main_Call_LFalse)
    ultimately show ?thesis using Main_Call CFG_Return_from_Method by blast
  next
    case CFG_Invoke_Call
    with CFG_Return_from_Method obtain as where "JVMCFG_Interpret.valid_path' P C0 Main
      (ClassMain P, MethodMain P, None, Enter) as (C', M', \<lfloor>pc'\<rfloor>, Normal)"
      by blast
    moreover with CFG_Invoke_Call
    have "vp_snoc P C0 Main as (C', M', \<lfloor>pc'\<rfloor>, Normal) (\<lambda>s. False)\<^sub>\<surd> (C', M', \<lfloor>pc'\<rfloor>, Return)"
      by (fastforce intro: CFG_Invoke_False)
    ultimately show ?thesis using CFG_Invoke_Call CFG_Return_from_Method by blast
  qed
qed

declare JVMCFG_Interpret.vp_snocI []
declare JVMCFG_Interpret.valid_node_def [simp del]
  valid_edge_def [simp del]
  JVMCFG_Interpret.intra_path_def [simp del]


definition EP :: jvm_prog
  where "EP = (''C'', Object, [],
  [(''M'', [], Void, 1::nat, 0::nat, [Push Unit, instr.Return], [])]) # SystemClasses"

definition Phi_EP :: ty\<^sub>P
  where "Phi_EP C M = (if C = ''C'' \<and> M = ''M''
      then [\<lfloor>([],[OK (Class ''C'')])\<rfloor>,\<lfloor>([Void],[OK (Class ''C'')])\<rfloor>] else [])"

lemma distinct_classes'':
  "''C'' \<noteq> Object"
  "''C'' \<noteq> NullPointer"
  "''C'' \<noteq> OutOfMemory"
  "''C'' \<noteq> ClassCast"
  by (simp_all add: Object_def NullPointer_def OutOfMemory_def ClassCast_def)

lemmas distinct_classes =
  distinct_classes distinct_classes'' distinct_classes'' [symmetric]
  
declare distinct_classes [simp add]

lemma i_max_2D: "i < Suc (Suc 0) \<Longrightarrow> i = 0 \<or> i = 1" by auto

lemma EP_wf: "wf_jvm_prog\<^bsub>Phi_EP\<^esub> EP"
  unfolding wf_jvm_prog_phi_def wf_prog_def
proof
  show "wf_syscls EP"
    by (simp add: EP_def wf_syscls_def SystemClasses_def sys_xcpts_def
      ObjectC_def NullPointerC_def OutOfMemoryC_def ClassCastC_def)
next
  have distinct_EP: "distinct_fst EP"
    by (auto simp: EP_def SystemClasses_def ObjectC_def NullPointerC_def OutOfMemoryC_def
      ClassCastC_def)
  moreover have classes_wf:
    "\<forall>c\<in>set EP. wf_cdecl
    (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M)) EP c"
  proof
    fix C
    assume C_in_EP: "C \<in> set EP"
    show "wf_cdecl
      (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M)) EP C"
    proof (cases "C \<in> set SystemClasses")
      case True
      thus ?thesis
        by (auto simp: wf_cdecl_def SystemClasses_def ObjectC_def NullPointerC_def
          OutOfMemoryC_def ClassCastC_def EP_def class_def)
    next
      case False
      with C_in_EP have "C = (''C'', the (class EP ''C''))"
        by (auto simp: EP_def SystemClasses_def class_def)
      thus ?thesis
        by (auto dest!: i_max_2D elim: Methods.cases
          simp: wf_cdecl_def class_def EP_def wf_mdecl_def wt_method_def Phi_EP_def
          wt_start_def check_types_def states_def JVM_SemiType.sl_def SystemClasses_def
          stk_esl_def upto_esl_def loc_sl_def SemiType.esl_def ObjectC_def
          SemiType.sup_def Err.sl_def Err.le_def err_def Listn.sl_def Method_def
          Err.esl_def Opt.esl_def Product.esl_def relevant_entries_def)
    qed
  qed
  ultimately show "(\<forall>c\<in>set EP. wf_cdecl
    (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M)) EP c) \<and>
    distinct_fst EP"
    by simp
qed

lemma [simp]: "PROG (Abs_wf_jvmprog (EP, Phi_EP)) = EP"
proof (cases "(EP, Phi_EP) \<in> wf_jvmprog")
  case True thus ?thesis by (simp add: Abs_wf_jvmprog_inverse)
next
  case False with EP_wf show ?thesis by (simp add: wf_jvmprog_def)
qed

lemma [simp]: "TYPING (Abs_wf_jvmprog (EP, Phi_EP)) = Phi_EP"
proof (cases "(EP, Phi_EP) \<in> wf_jvmprog")
  case True thus ?thesis by (simp add: Abs_wf_jvmprog_inverse)
next
  case False with EP_wf show ?thesis by (simp add: wf_jvmprog_def)
qed

lemma method_in_EP_is_M:
  "EP \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, is, xt) in D
  \<Longrightarrow> C = ''C'' \<and> M = ''M'' \<and> Ts = [] \<and> T = Void \<and> mxs = 1 \<and> mxl = 0 \<and>
  is = [Push Unit, instr.Return] \<and> xt = [] \<and> D = ''C''"
  by (fastforce elim: Methods.cases 
    simp: class_def SystemClasses_def ObjectC_def NullPointerC_def OutOfMemoryC_def ClassCastC_def
    if_split_eq1 EP_def Method_def)

lemma [simp]:
  "\<exists>T Ts mxs mxl is. (\<exists>xt. EP \<turnstile> ''C'' sees ''M'': Ts\<rightarrow>T = (mxs, mxl, is, xt) in ''C'') \<and> is \<noteq> []"
  using EP_wf
  by (fastforce dest: mdecl_visible simp: wf_jvm_prog_phi_def EP_def)

lemma [simp]:
  "\<exists>T Ts mxs mxl is. (\<exists>xt. EP \<turnstile> ''C'' sees ''M'': Ts\<rightarrow>T = (mxs, mxl, is, xt) in ''C'') \<and> 
  Suc 0 < length is"
  using EP_wf
  by (fastforce dest: mdecl_visible simp: wf_jvm_prog_phi_def EP_def)

lemma C_sees_M_in_EP [simp]:
  "EP \<turnstile> ''C'' sees ''M'': []\<rightarrow>Void = (Suc 0, 0, [Push Unit, instr.Return], []) in ''C''"
proof -
  have "EP \<turnstile> ''C'' sees_methods [''M'' \<mapsto> (([], Void, 1, 0, [Push Unit, instr.Return], []), ''C'')]"
    by (fastforce intro: Methods.intros simp: class_def SystemClasses_def ObjectC_def EP_def)
  thus ?thesis by (fastforce simp: Method_def)
qed

lemma instrs_of_EP_C_M [simp]:
  "instrs_of EP ''C'' ''M'' = [Push Unit, instr.Return]"
  unfolding method_def
  by (rule theI2 [where P = "\<lambda>(D, Ts, T, m). EP \<turnstile> ''C'' sees ''M'': Ts\<rightarrow>T = m in D"])
(auto dest: method_in_EP_is_M)

lemma ClassMain_not_C [simp]: "ClassMain (Abs_wf_jvmprog (EP, Phi_EP)) \<noteq> ''C''"
  by (fastforce intro: no_Call_in_ClassMain [where P="Abs_wf_jvmprog (EP, Phi_EP)"] C_sees_M_in_EP)

lemma method_entry [dest!]: "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') \<turnstile> \<Rightarrow>(C, M, None, Enter)
  \<Longrightarrow> (C = ClassMain (Abs_wf_jvmprog (EP, Phi_EP)) \<and> M = MethodMain (Abs_wf_jvmprog (EP, Phi_EP)))
  \<or> (C = ''C'' \<and> M = ''M'')"
  by (fastforce elim: reachable.cases elim!: JVMCFG.cases dest!: method_in_EP_is_M)

lemma valid_node_in_EP_D:
  assumes vn: "JVMCFG_Interpret.valid_node (Abs_wf_jvmprog (EP, Phi_EP)) ''C'' ''M'' n"
  shows "n \<in> {
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), None, Enter),
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), None, Return),
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), \<lfloor>0\<rfloor>, Enter),
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), \<lfloor>0\<rfloor>, Normal),
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), \<lfloor>0\<rfloor>, Return),
  (''C'', ''M'', None, Enter),
  (''C'', ''M'', \<lfloor>0\<rfloor>, Enter),
  (''C'', ''M'', \<lfloor>1\<rfloor>, Enter),
  (''C'', ''M'', None, Return)
  }"
  using vn
proof (cases rule: JVMCFG_Interpret.valid_node_cases')
  let ?prog = "Abs_wf_jvmprog (EP, Phi_EP)"
  case (Source e)
  then obtain C M pc nt ek C' M' pc' nt'
    where [simp]: "e = ((C, M, pc, nt), ek, (C', M', pc', nt'))"
    and [simp]: "n = (C, M, pc, nt)"
    and edge: "(?prog, ''C'', ''M'') \<turnstile> (C, M, pc, nt) -ek\<rightarrow> (C', M', pc', nt')"
    by (cases e) (fastforce simp: valid_edge_def)
  from edge have src_reachable: "(?prog, ''C'', ''M'') \<turnstile> \<Rightarrow>(C, M, pc, nt)"
    by -(drule sourcenode_reachable)
  show ?thesis
  proof (cases "C = ClassMain ?prog")
    case True
    with src_reachable have "M = MethodMain ?prog"
      by (fastforce dest: ClassMain_imp_MethodMain)
    with True edge show ?thesis
      by clarsimp (erule JVMCFG.cases, simp_all)
  next
    case False
    with src_reachable obtain T Ts mb where "EP \<turnstile> C sees M:Ts\<rightarrow>T = mb in C"
      by (fastforce dest: method_of_reachable_node_exists)
    hence [simp]: "C = ''C''"
      and [simp]: "M = ''M''"
      and [simp]: "Ts = []"
      and [simp]: "T = Void"
      and [simp]: "mb = (1, 0, [Push Unit, instr.Return], [])"
      by (cases mb, fastforce dest: method_in_EP_is_M)+
    from src_reachable False have "pc \<in> {None, \<lfloor>0\<rfloor>, \<lfloor>1\<rfloor>}"
      by (fastforce dest: instr_of_reachable_node_typable)
    show ?thesis
    proof (cases pc)
      case None
      with edge False show ?thesis
        by clarsimp (erule JVMCFG.cases, simp_all)
    next
      case (Some pc')
      show ?thesis
      proof (cases pc')
        case 0
        with Some False edge show ?thesis
          by clarsimp (erule JVMCFG.cases, fastforce+)
      next
        case (Suc n)
        with \<open>pc \<in> {None, \<lfloor>0\<rfloor>, \<lfloor>1\<rfloor>}\<close> Some have "pc = \<lfloor>1\<rfloor>"
          by simp
        with False edge show ?thesis
          by clarsimp (erule JVMCFG.cases, fastforce+)
      qed
    qed
  qed
next
  let ?prog = "Abs_wf_jvmprog (EP, Phi_EP)"
  case (Target e)
  then obtain C M pc nt ek C' M' pc' nt'
    where [simp]: "e = ((C, M, pc, nt), ek, (C', M', pc', nt'))"
    and [simp]: "n = (C', M', pc', nt')"
    and edge: "(?prog, ''C'', ''M'') \<turnstile> (C, M, pc, nt) -ek\<rightarrow> (C', M', pc', nt')"
    by (cases e) (fastforce simp: valid_edge_def)
  from edge have trg_reachable: "(?prog, ''C'', ''M'') \<turnstile> \<Rightarrow>(C', M', pc', nt')"
    by -(drule targetnode_reachable)
  show ?thesis
  proof (cases "C' = ClassMain ?prog")
    case True
    with trg_reachable have "M' = MethodMain ?prog"
      by (fastforce dest: ClassMain_imp_MethodMain)
    with True edge show ?thesis
      by -(clarsimp, (erule JVMCFG.cases, simp_all))+
  next
    case False
    with trg_reachable obtain T Ts mb where "EP \<turnstile> C' sees M':Ts\<rightarrow>T = mb in C'"
      by (fastforce dest: method_of_reachable_node_exists)
    hence [simp]: "C' = ''C''"
      and [simp]: "M' = ''M''"
      and [simp]: "Ts = []"
      and [simp]: "T = Void"
      and [simp]: "mb = (1, 0, [Push Unit, instr.Return], [])"
      by (cases mb, fastforce dest: method_in_EP_is_M)+
    from trg_reachable False have "pc' \<in> {None, \<lfloor>0\<rfloor>, \<lfloor>1\<rfloor>}"
      by (fastforce dest: instr_of_reachable_node_typable)
    show ?thesis
    proof (cases pc')
      case None
      with edge False show ?thesis
        by clarsimp (erule JVMCFG.cases, simp_all)
    next
      case (Some pc'')
      show ?thesis
      proof (cases pc'')
        case 0
        with Some False edge show ?thesis
          by -(clarsimp, (erule JVMCFG.cases, fastforce+))+
      next
        case (Suc n)
        with \<open>pc' \<in> {None, \<lfloor>0\<rfloor>, \<lfloor>1\<rfloor>}\<close> Some have "pc' = \<lfloor>1\<rfloor>"
          by simp
        with False edge show ?thesis
          by -(clarsimp, (erule JVMCFG.cases, fastforce+))+
      qed
    qed
  qed
qed

lemma Main_Entry_valid [simp]:
  "JVMCFG_Interpret.valid_node (Abs_wf_jvmprog (EP, Phi_EP)) ''C'' ''M''
  (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), None, Enter)"
proof -
  have "valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'')
    ((ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), None,
      Enter),
    (\<lambda>s. False)\<^sub>\<surd>,
    (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)), None,
      Return))"
    by (auto simp: valid_edge_def intro: JVMCFG_reachable.intros)
  thus ?thesis by (fastforce simp: JVMCFG_Interpret.valid_node_def)
qed

lemma main_0_Enter_reachable [simp]: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter)"
  by (rule reachable_step [where n="(ClassMain P, MethodMain P, None, Enter)"])
(fastforce intro: JVMCFG_reachable.intros)+

lemma main_0_Normal_reachable [simp]: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
  by (rule reachable_step [where n="(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter)"], simp)
(fastforce intro: JVMCFG_reachable.intros)

lemma main_0_Return_reachable [simp]: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)"
  by (rule reachable_step [where n="(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"], simp)
(fastforce intro: JVMCFG_reachable.intros)

lemma Exit_reachable [simp]: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, None, Return)"
  by (rule reachable_step [where n="(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)"], simp)
(fastforce intro: JVMCFG_reachable.intros)

definition
  "cfg_wf_prog =
    {(P, C0, Main). (\<forall>n. JVMCFG_Interpret.valid_node P C0 Main n \<longrightarrow>
         (\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge (P, C0, Main))
                         (get_return_edges P) n as (ClassMain P, MethodMain P, None, Return)))}"

typedef cfg_wf_prog = cfg_wf_prog
  unfolding cfg_wf_prog_def
proof
  let ?prog = "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'')"
  let ?edge_main0 = "((ClassMain (fst ?prog), MethodMain (fst ?prog), None, Enter),
    (\<lambda>s. False)\<^sub>\<surd>,
    (ClassMain (fst ?prog), MethodMain (fst ?prog), None, Return))"
  let ?edge_main1 = "((ClassMain (fst ?prog), MethodMain (fst ?prog), None, Enter),
    (\<lambda>s. True)\<^sub>\<surd>,
    (ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Enter))"
  let ?edge_main2 = "((ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Enter),
    \<Up>id,
    (ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Normal))"
  let ?edge_main3 = "((ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Normal),
    (\<lambda>s. False)\<^sub>\<surd>,
    (ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Return))"
  let ?edge_main4 = "((ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Return),
    \<Up>id,
    (ClassMain (fst ?prog), MethodMain (fst ?prog), None, Return))"
  let ?edge_call = "((ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Normal),
    ((\<lambda>(s, ret). True):(ClassMain (fst ?prog),
      MethodMain (fst ?prog), 0)\<hookrightarrow>\<^bsub>(''C'', ''M'')\<^esub>[(\<lambda>s. s Heap),(\<lambda>s. \<lfloor>Value Null\<rfloor>)]),
    (''C'', ''M'', None, Enter))"
  let ?edge_C0 = "((''C'', ''M'', None, Enter),
    (\<lambda>s. False)\<^sub>\<surd>,
    (''C'', ''M'', None, Return))"
  let ?edge_C1 = "((''C'', ''M'', None, Enter),
    (\<lambda>s. True)\<^sub>\<surd>,
    (''C'', ''M'', \<lfloor>0\<rfloor>, Enter))"
  let ?edge_C2 = "((''C'', ''M'', \<lfloor>0\<rfloor>, Enter),
    \<Up>(\<lambda>s. s(Stack 0 \<mapsto> Value Unit)),
    (''C'', ''M'', \<lfloor>1\<rfloor>, Enter))"
  let ?edge_C3 = "((''C'', ''M'', \<lfloor>1\<rfloor>, Enter),
    \<Up>(\<lambda>s. s(Stack 0 := s (Stack 0))),
    (''C'', ''M'', None, Return))"
  let ?edge_return = "((''C'', ''M'', None, Return),
    (\<lambda>(s, ret). ret = (ClassMain (fst ?prog),
      MethodMain (fst ?prog), 0))\<hookleftarrow>\<^bsub>(''C'',''M'')\<^esub>(\<lambda>s s'. s'(Heap := s Heap,
                            Exception := s Exception,
                            Stack 0 := s (Stack 0))),
    (ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Return))"
  have [simp]:
    "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') \<turnstile> \<Rightarrow>(''C'', ''M'', None, Enter)"
    by (rule reachable_step [where n="(ClassMain (fst ?prog), MethodMain (fst ?prog), \<lfloor>0\<rfloor>, Normal)"]
      , simp)
  (fastforce intro: Main_Call C_sees_M_in_EP)
  hence [simp]:
    "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') \<turnstile> \<Rightarrow>(''C'', ''M'', None, nodeType.Return)"
    by (rule reachable_step [where n="(''C'', ''M'', None, Enter)"])
  (fastforce intro: JVMCFG_reachable.intros)
  have [simp]:
    "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') \<turnstile> \<Rightarrow>(''C'', ''M'', \<lfloor>0\<rfloor>, Enter)"
    by (rule reachable_step [where n="(''C'', ''M'', None, Enter)"], simp)
  (fastforce intro: JVMCFG_reachable.intros)
  hence [simp]:
    "(Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') \<turnstile> \<Rightarrow>(''C'', ''M'', \<lfloor>Suc 0\<rfloor>, Enter)"
    by (fastforce intro: reachable_step [where n="(''C'', ''M'', \<lfloor>0\<rfloor>, Enter)"] CFG_Push
      simp: ClassMain_not_C [symmetric])
  show "?prog \<in> {(P, C0, Main).
          \<forall>n. CFG.valid_node sourcenode targetnode (valid_edge (P, C0, Main)) n \<longrightarrow>
              (\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge (P, C0, Main))
                     (get_return_edges P) n as
                     (ClassMain P, MethodMain P, None, nodeType.Return))}"
  proof (auto dest!: valid_node_in_EP_D)
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, Enter)
          [?edge_main0]
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_Interpret.intra_path_vp JVMCFG_reachable.intros
        simp: JVMCFG_Interpret.intra_path_def intra_kind_def valid_edge_def)
    thus " \<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, Enter)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)
      [] (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_Interpret.intra_path_vp simp: JVMCFG_Interpret.intra_path_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, Enter)
      [?edge_main2, ?edge_main3, ?edge_main4]
      (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_Interpret.intra_path_vp JVMCFG_reachable.intros
        simp: JVMCFG_Interpret.intra_path_def intra_kind_def valid_edge_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, Enter)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, Normal)
      [?edge_main3, ?edge_main4]
      (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_Interpret.intra_path_vp JVMCFG_reachable.intros
        simp: JVMCFG_Interpret.intra_path_def intra_kind_def valid_edge_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, Normal)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, nodeType.Return)
      [?edge_main4]
      (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_Interpret.intra_path_vp JVMCFG_reachable.intros
        simp: JVMCFG_Interpret.intra_path_def intra_kind_def valid_edge_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP)))
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           \<lfloor>0\<rfloor>, nodeType.Return)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', None, Enter)
      [?edge_C0, ?edge_return, ?edge_main4]
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by (fastforce intro: JVMCFG_reachable.intros C_sees_M_in_EP
        simp: JVMCFG_Interpret.vp_def valid_edge_def stkLength_def JVMCFG_Interpret.valid_path_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', None, Enter) as
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', \<lfloor>0\<rfloor>, Enter)
      [?edge_C2, ?edge_C3, ?edge_return, ?edge_main4]
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by (fastforce intro: Main_Return_to_Exit CFG_Return_from_Method Main_Call
        C_sees_M_in_EP CFG_Return CFG_Push
        simp: JVMCFG_Interpret.vp_def valid_edge_def stkLength_def Phi_EP_def
        ClassMain_not_C [symmetric] JVMCFG_Interpret.valid_path_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', \<lfloor>0\<rfloor>, Enter) as
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', \<lfloor>Suc 0\<rfloor>, Enter)
      [?edge_C3, ?edge_return, ?edge_main4]
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by (fastforce intro: JVMCFG_reachable.intros C_sees_M_in_EP
        simp: JVMCFG_Interpret.vp_def valid_edge_def stkLength_def Phi_EP_def
        ClassMain_not_C [symmetric] JVMCFG_Interpret.valid_path_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', \<lfloor>Suc 0\<rfloor>, Enter) as
          (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
           None, nodeType.Return)"
      by blast
  next
    have "CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', None, nodeType.Return)
          [?edge_return, ?edge_main4]
      (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by (fastforce intro: JVMCFG_reachable.intros C_sees_M_in_EP
        simp: JVMCFG_Interpret.vp_def valid_edge_def JVMCFG_Interpret.valid_path_def stkLength_def)
    thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
          (valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M''))
          (get_return_edges (Abs_wf_jvmprog (EP, Phi_EP))) (''C'', ''M'', None, nodeType.Return)
          as (ClassMain (Abs_wf_jvmprog (EP, Phi_EP)), MethodMain (Abs_wf_jvmprog (EP, Phi_EP)),
              None, nodeType.Return)"
      by blast
  qed
qed


abbreviation lift_to_cfg_wf_prog :: "(jvm_method \<Rightarrow> 'a) \<Rightarrow> (cfg_wf_prog \<Rightarrow> 'a)"
  ("_\<^bsub>CFG\<^esub>")
  where "f\<^bsub>CFG\<^esub> \<equiv> (\<lambda>P. f (Rep_cfg_wf_prog P))"

lemma valid_edge_CFG_def: "valid_edge\<^bsub>CFG\<^esub> P = valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P))"
  by (cases P) (clarsimp simp: Abs_cfg_wf_prog_inverse)

interpretation JVMCFG_Postdomination:
  Postdomination "sourcenode" "targetnode" "kind" "valid_edge\<^bsub>CFG\<^esub> P"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges (fst\<^bsub>CFG\<^esub> P)"
  "((ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P)),[],[]) # procs (PROG (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Return)"
  for P
  unfolding valid_edge_CFG_def
proof
  fix n
  obtain P' C0 Main where [simp]: "fst\<^bsub>CFG\<^esub> P = P'" and [simp]: "fst (snd\<^bsub>CFG\<^esub> P) = C0"
    and [simp]: "snd (snd\<^bsub>CFG\<^esub> P) = Main"
    by (cases P) clarsimp
  assume "CFG.valid_node sourcenode targetnode
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P))) n"
  thus "\<exists>as. CFG.valid_path' sourcenode targetnode kind
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P)))
    (get_return_edges (fst\<^bsub>CFG\<^esub> P))
    (ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Enter) as n"
    by (auto dest: sourcenode_reachable targetnode_reachable valid_Entry_path
      simp: JVMCFG_Interpret.valid_node_def valid_edge_def)
next
  fix n
  obtain P' C0 Main where [simp]: "fst\<^bsub>CFG\<^esub> P = P'" and [simp]: "fst (snd\<^bsub>CFG\<^esub> P) = C0"
    and [simp]: "snd (snd\<^bsub>CFG\<^esub> P) = Main"
    and "(P', C0, Main) \<in> cfg_wf_prog"
    by (cases P) (clarsimp simp: Abs_cfg_wf_prog_inverse)
  assume "CFG.valid_node sourcenode targetnode
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P))) n"
  with \<open>(P', C0, Main) \<in> cfg_wf_prog\<close>
  show "\<exists>as. CFG.valid_path' sourcenode targetnode kind
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P)))
    (get_return_edges (fst\<^bsub>CFG\<^esub> P)) n as
    (ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, nodeType.Return)"
    by (cases n) (fastforce simp: cfg_wf_prog_def)
next
  fix n n'
  obtain P' C0 Main where [simp]: "fst\<^bsub>CFG\<^esub> P = P'" and [simp]: "fst (snd\<^bsub>CFG\<^esub> P) = C0"
    and [simp]: "snd (snd\<^bsub>CFG\<^esub> P) = Main"
    by (cases P) clarsimp
  assume "CFGExit.method_exit sourcenode kind
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P)))
    (ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, nodeType.Return) n"
    and "CFGExit.method_exit sourcenode kind
    (valid_edge (fst\<^bsub>CFG\<^esub> P, fst (snd\<^bsub>CFG\<^esub> P), snd (snd\<^bsub>CFG\<^esub> P)))
    (ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, nodeType.Return) n'"
    and "(\<lambda>(C, M, pc, type). (C, M)) n = (\<lambda>(C, M, pc, type). (C, M)) n'"
  thus "n = n'"
    by (auto simp: JVMCFG_Exit_Interpret.method_exit_def valid_edge_def)
  (fastforce elim: JVMCFG.cases)+
qed

end
