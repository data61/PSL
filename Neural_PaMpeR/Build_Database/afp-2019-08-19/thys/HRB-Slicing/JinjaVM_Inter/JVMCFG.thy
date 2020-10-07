chapter \<open>A Control Flow Graph for Jinja Byte Code\<close>

section \<open>Formalizing the CFG\<close>

theory JVMCFG imports "../StaticInter/BasicDefs" Jinja.BVExample begin

declare lesub_list_impl_same_size [simp del]
declare listE_length [simp del]

subsection \<open>Type definitions\<close>

subsubsection \<open>Wellformed Programs\<close>

definition "wf_jvmprog = {(P, Phi). wf_jvm_prog\<^bsub>Phi\<^esub> P}"

typedef wf_jvmprog = "wf_jvmprog"
proof
  show "(E, Phi) \<in> wf_jvmprog"
    unfolding wf_jvmprog_def by (auto intro: wf_prog)
qed

hide_const Phi E

abbreviation PROG :: "wf_jvmprog \<Rightarrow> jvm_prog"
  where "PROG P \<equiv> fst(Rep_wf_jvmprog(P))"

abbreviation TYPING :: "wf_jvmprog \<Rightarrow> ty\<^sub>P"
  where "TYPING P \<equiv> snd(Rep_wf_jvmprog(P))"

lemma wf_jvmprog_is_wf_typ: "wf_jvm_prog\<^bsub>TYPING P\<^esub> (PROG P)"
using Rep_wf_jvmprog [of P]
  by (auto simp: wf_jvmprog_def split_beta)

lemma wf_jvmprog_is_wf: "wf_jvm_prog (PROG P)"
  using wf_jvmprog_is_wf_typ unfolding wf_jvm_prog_def
  by blast

subsubsection \<open>Interprocedural CFG\<close>

type_synonym jvm_method = "wf_jvmprog \<times> cname \<times> mname"
datatype var = Heap | Local "nat" | Stack "nat" | Exception
datatype val = Hp "heap" | Value "Value.val"

type_synonym state = "var \<rightharpoonup> val"

definition valid_state :: "state \<Rightarrow> bool"
  where "valid_state s \<equiv> (\<forall>val. s Heap \<noteq> Some (Value val))
  \<and> (s Exception = None \<or> (\<exists>addr. s Exception = Some (Value (Addr addr))))
  \<and> (\<forall>var. var \<noteq> Heap \<and> var \<noteq> Exception \<longrightarrow> (\<forall>h. s var \<noteq> Some (Hp h)))"

fun the_Heap :: "val \<Rightarrow> heap"
  where "the_Heap (Hp h) = h"

fun the_Value :: "val \<Rightarrow> Value.val"
  where "the_Value (Value v) = v"

abbreviation heap_of :: "state \<Rightarrow> heap"
  where "heap_of s \<equiv> the_Heap (the (s Heap))"

abbreviation exc_flag :: "state \<Rightarrow> addr option"
  where "exc_flag s \<equiv> case (s Exception) of None \<Rightarrow> None
  | Some v \<Rightarrow> Some (THE a. v = Value (Addr a))"

abbreviation stkAt :: "state \<Rightarrow> nat \<Rightarrow> Value.val"
  where "stkAt s n \<equiv> the_Value (the (s (Stack n)))"

abbreviation locAt :: "state \<Rightarrow> nat \<Rightarrow> Value.val"
  where "locAt s n \<equiv> the_Value (the (s (Local n)))"

datatype nodeType = Enter | Normal | Return | Exceptional "pc option" "nodeType"
type_synonym cfg_node = "cname \<times> mname \<times> pc option \<times> nodeType"

type_synonym
  cfg_edge = "cfg_node \<times> (var, val, cname \<times> mname \<times> pc, cname \<times> mname) edge_kind \<times> cfg_node"

definition ClassMain :: "wf_jvmprog \<Rightarrow> cname"
  where "ClassMain P \<equiv> SOME Name. \<not> is_class (PROG P) Name"

definition MethodMain :: "wf_jvmprog \<Rightarrow> mname"
  where "MethodMain P \<equiv> SOME Name.
  \<forall>C D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor> \<longrightarrow> (\<forall>m \<in> set ms. Name \<noteq> fst m)"

definition stkLength :: "jvm_method \<Rightarrow> pc \<Rightarrow> nat"
  where
  "stkLength m pc \<equiv> let (P, C, M) = m in (
  if (C = ClassMain P) then 1 else (
    length (fst(the(((TYPING P) C M) ! pc)))
  ))"

definition locLength :: "jvm_method \<Rightarrow> pc \<Rightarrow> nat"
  where
  "locLength m pc \<equiv> let (P, C, M) = m in (
  if (C = ClassMain P) then 1 else (
    length (snd(the(((TYPING P) C M) ! pc)))
  ))"

lemma ex_new_class_name: "\<exists>C. \<not> is_class P C"
proof -
  have "\<not> finite (UNIV :: cname set)"
    by (rule infinite_UNIV_listI)
  hence "\<exists>C. C \<notin> set (map fst P)"
    by -(rule ex_new_if_finite, auto)
  then obtain C where "C \<notin> set (map fst P)"
    by blast
  have "\<not> is_class P C"
  proof
    assume "is_class P C"
    then obtain D fs ms where "class P C = \<lfloor>(D, fs, ms)\<rfloor>"
      by auto
    with \<open>C \<notin> set (map fst P)\<close> show False
      by (auto dest: map_of_SomeD intro!: image_eqI simp: class_def)
  qed
  thus ?thesis
    by blast
qed

lemma ClassMain_unique_in_P:
  assumes "is_class (PROG P) C"
  shows "ClassMain P \<noteq> C"
proof -
  from ex_new_class_name [of "PROG P"] obtain D where "\<not> is_class (PROG P) D"
    by blast
  with \<open>is_class (PROG P) C\<close> show ?thesis
    unfolding ClassMain_def
    by -(rule someI2, fastforce+)
qed

lemma map_of_fstD: "\<lbrakk> map_of xs a = \<lfloor>b\<rfloor>; \<forall>x \<in> set xs. fst x \<noteq> a \<rbrakk> \<Longrightarrow> False"
  by (induct xs, auto)

lemma map_of_fstE: "\<lbrakk> map_of xs a = \<lfloor>b\<rfloor>; \<exists>x \<in> set xs. fst x = a \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  by (induct xs) (auto split: if_split_asm)

lemma ex_unique_method_name:
  "\<exists>Name. \<forall>C D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor> \<longrightarrow> (\<forall>m\<in>set ms. Name \<noteq> fst m)"
proof -
  from wf_jvmprog_is_wf [of P]
  have "distinct_fst (PROG P)"
    by (simp add: wf_jvm_prog_def wf_jvm_prog_phi_def wf_prog_def)
  hence "{C. \<exists>D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>} = fst ` set (PROG P)"
    by (fastforce elim: map_of_fstE simp: class_def intro: map_of_SomeI)
  hence "finite {C. \<exists>D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>}"
    by auto
  moreover have "{ms. \<exists>C D fs. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>}
    = snd ` snd ` the ` (\<lambda>C. class (PROG P) C) ` {C. \<exists>D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>}"
    by (fastforce intro: rev_image_eqI map_of_SomeI simp: class_def)
  ultimately have "finite {ms. \<exists>C D fs. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>}"
    by auto
  moreover have "\<not> finite (UNIV :: mname set)"
    by (rule infinite_UNIV_listI)
  ultimately
  have "\<exists>Name. Name \<notin> fst ` (\<Union>ms \<in> {ms. \<exists>C D fs. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor>}. set ms)"
    by -(rule ex_new_if_finite, auto)
  thus ?thesis
    by fastforce
qed

lemma MethodMain_unique_in_P:
  assumes "PROG P \<turnstile> D sees M:Ts\<rightarrow>T = mb in C"
  shows "MethodMain P \<noteq> M"
proof -
  from ex_unique_method_name [of P] obtain M'
    where "\<And>C D fs ms. class (PROG P) C = \<lfloor>(D, fs, ms)\<rfloor> \<Longrightarrow> (\<forall>m \<in> set ms. M' \<noteq> fst m)"
    by blast
  with \<open>PROG P \<turnstile> D sees M:Ts\<rightarrow>T = mb in C\<close>
  show ?thesis
    unfolding MethodMain_def
    by -(rule someI2_ex, fastforce, fastforce dest!: visible_method_exists elim: map_of_fstE)
qed

lemma ClassMain_is_no_class [dest!]: "is_class (PROG P) (ClassMain P) \<Longrightarrow> False"
proof (erule rev_notE)
  from ex_new_class_name [of "PROG P"] obtain C where "\<not> is_class (PROG P) C"
    by blast
  thus "\<not> is_class (PROG P) (ClassMain P)" unfolding ClassMain_def
    by (rule someI)
qed

lemma MethodMain_not_seen [dest!]: "PROG P \<turnstile> C sees (MethodMain P):Ts\<rightarrow>T = mb in D \<Longrightarrow> False"
  by (fastforce dest: MethodMain_unique_in_P)

lemma no_Call_from_ClassMain [dest!]: "PROG P \<turnstile> ClassMain P sees M:Ts\<rightarrow>T = mb in C \<Longrightarrow> False"
  by (fastforce dest: sees_method_is_class)

lemma no_Call_in_ClassMain [dest!]: "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = mb in ClassMain P \<Longrightarrow> False"
  by (fastforce dest: sees_method_idemp)

inductive JVMCFG :: "jvm_method \<Rightarrow> cfg_node \<Rightarrow> (var, val, cname \<times> mname \<times> pc, cname \<times> mname) edge_kind \<Rightarrow> cfg_node \<Rightarrow> bool" (" _ \<turnstile> _ -_\<rightarrow> _")
  and reachable :: "jvm_method \<Rightarrow> cfg_node \<Rightarrow> bool" (" _ \<turnstile> \<Rightarrow>_")
  where
    Entry_reachable: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, None, Enter)"
  | reachable_step: "\<lbrakk> P \<turnstile> \<Rightarrow>n; P \<turnstile> n -(e)\<rightarrow> n' \<rbrakk> \<Longrightarrow> P \<turnstile> \<Rightarrow>n'"
  | Main_to_Call: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter)
  \<Longrightarrow> (P, C0, Main) \<turnstile> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Enter) -\<Up>id\<rightarrow> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)"
  | Main_Call_LFalse: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal)
  \<Longrightarrow> (P, C0, Main) \<turnstile> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)"
  | Main_Call: "\<lbrakk> (P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal);
     PROG P \<turnstile> C0 sees Main:[]\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D;
     initParams = [(\<lambda>s. s Heap),(\<lambda>s. \<lfloor>Value Null\<rfloor>)];
     ek = (\<lambda>(s, ret). True):(ClassMain P, MethodMain P, 0)\<hookrightarrow>\<^bsub>(D, Main)\<^esub>initParams \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Normal) -(ek)\<rightarrow> (D, Main, None, Enter)"
  | Main_Return_to_Exit: "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return)
  \<Longrightarrow> (P, C0, Main) \<turnstile> (ClassMain P, MethodMain P, \<lfloor>0\<rfloor>, Return) -(\<Up>id)\<rightarrow> (ClassMain P, MethodMain P, None, Return)"
  | Method_LFalse: "(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Enter)
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, None, Enter) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (C, M, None, Return)"
  | Method_LTrue: "(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Enter)
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, None, Enter) -(\<lambda>s. True)\<^sub>\<surd>\<rightarrow> (C, M, \<lfloor>0\<rfloor>, Enter)"
  | CFG_Load: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = Load n;
    ek = \<Up>(\<lambda>s. s(Stack (stkLength (P, C, M) pc) := s (Local n))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Store: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = Store n;
    ek = \<Up>(\<lambda>s. s(Local n := s (Stack (stkLength (P, C, M) pc - 1)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Push: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = Push v;
    ek = \<Up>(\<lambda>s. s(Stack (stkLength (P, C, M) pc) \<mapsto> Value v)) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Pop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = Pop;
    ek = \<Up>id \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_IAdd: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = IAdd;
    ek = \<Up>(\<lambda>s. let i1 = the_Intg (stkAt s (stkLength (P, C, M) pc - 1));
                   i2 = the_Intg (stkAt s (stkLength (P, C, M) pc - 2))
                in s(Stack (stkLength (P, C, M) pc - 2) \<mapsto> Value (Intg (i1 + i2)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Goto: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = Goto i \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -((\<lambda>s. True)\<^sub>\<surd>)\<rightarrow> (C, M, \<lfloor>nat (int pc + i)\<rfloor>, Enter)"
  | CFG_CmpEq: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter); instrs_of (PROG P) C M ! pc = CmpEq;
    ek = \<Up>(\<lambda>s. let e1 = stkAt s (stkLength (P, C, M) pc - 1);
                   e2 = stkAt s (stkLength (P, C, M) pc - 2)
                in s(Stack (stkLength (P, C, M) pc - 2) \<mapsto> Value (Bool (e1 = e2)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_IfFalse_False: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = IfFalse i;
    i \<noteq> 1;
    ek = (\<lambda>s. stkAt s (stkLength(P, C, M) pc - 1) = Bool False)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>nat (int pc + i)\<rfloor>, Enter)"
  | CFG_IfFalse_True: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = IfFalse i;
    ek = (\<lambda>s. stkAt s (stkLength(P, C, M) pc - 1) \<noteq> Bool False \<or> i = 1)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_New_Check_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = New Cl;
    ek = (\<lambda>s. new_Addr (heap_of s) \<noteq> None)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Normal)"
  | CFG_New_Check_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = New Cl;
    pc' = (case (match_ex_table (PROG P) OutOfMemory pc (ex_table_of (PROG P) C M)) of
             None \<Rightarrow> None
           | Some (pc'', d) \<Rightarrow> \<lfloor>pc''\<rfloor>);
    ek = (\<lambda>s. new_Addr (heap_of s) = None)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
  | CFG_New_Update: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal);
    instrs_of (PROG P) C M ! pc = New Cl;
    ek = \<Up>(\<lambda>s. let a = the (new_Addr (heap_of s))
                in s(Heap \<mapsto> Hp ((heap_of s)(a \<mapsto> blank (PROG P) Cl)))
                    (Stack (stkLength(P, C, M) pc) \<mapsto> Value (Addr a))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Normal) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_New_Exceptional_prop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = New Cl;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt OutOfMemory)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_New_Exceptional_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    instrs_of (PROG P) C M ! pc = New Cl;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (Addr (addr_of_sys_xcpt OutOfMemory)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Getfield_Check_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Getfield F Cl;
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) \<noteq> Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Normal)"
  | CFG_Getfield_Check_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Getfield F Cl;
    pc' = (case (match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M)) of
             None \<Rightarrow> None
           | Some (pc'', d) \<Rightarrow> \<lfloor>pc''\<rfloor>);
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 1) = Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
  | CFG_Getfield_Update: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal);
    instrs_of (PROG P) C M ! pc = Getfield F Cl;
    ek = \<Up>(\<lambda>s. let (D, fs) = the (heap_of s (the_Addr (stkAt s (stkLength (P, C, M) pc - 1))))
                 in s(Stack (stkLength(P, C, M) pc - 1) \<mapsto> Value (the (fs (F, Cl))))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Normal) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Getfield_Exceptional_prop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = Getfield F Cl;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Getfield_Exceptional_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    instrs_of (PROG P) C M ! pc = Getfield F Cl;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Putfield_Check_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Putfield F Cl;
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 2) \<noteq> Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Normal)"
  | CFG_Putfield_Check_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Putfield F Cl;
    pc' = (case (match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M)) of
             None \<Rightarrow> None
           | Some (pc'', d) \<Rightarrow> \<lfloor>pc''\<rfloor>);
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - 2) = Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
  | CFG_Putfield_Update: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal);
    instrs_of (PROG P) C M ! pc = Putfield F Cl;
    ek = \<Up>(\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
                   r = stkAt s (stkLength (P, C, M) pc - 2);
                   a = the_Addr r;
                   (D, fs) = the (heap_of s a);
                   h' = (heap_of s)(a \<mapsto> (D, fs((F, Cl) \<mapsto> v)))
                 in s(Heap \<mapsto> Hp h')) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Normal) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Putfield_Exceptional_prop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = Putfield F Cl;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Putfield_Exceptional_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    instrs_of (PROG P) C M ! pc = Putfield F Cl;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Checkcast_Check_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Checkcast Cl;
    ek = (\<lambda>s. cast_ok (PROG P) Cl (heap_of s) (stkAt s (stkLength (P, C, M) pc - 1)))\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Checkcast_Check_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Checkcast Cl;
    pc' = (case (match_ex_table (PROG P) ClassCast pc (ex_table_of (PROG P) C M)) of
             None \<Rightarrow> None
           | Some (pc'', d) \<Rightarrow> \<lfloor>pc''\<rfloor>);
    ek = (\<lambda>s. \<not> cast_ok (PROG P) Cl (heap_of s) (stkAt s (stkLength (P, C, M) pc - 1)))\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
  | CFG_Checkcast_Exceptional_prop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = Checkcast Cl;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt ClassCast)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Checkcast_Exceptional_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    instrs_of (PROG P) C M ! pc = Checkcast Cl;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (Addr (addr_of_sys_xcpt ClassCast)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Throw_Check: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Throw;
    pc' = None \<or> match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(the pc', d)\<rfloor>;
    ek = (\<lambda>s. let v = stkAt s (stkLength (P, C, M) pc - 1);
                  Cl = if (v = Null) then NullPointer else (cname_of (heap_of s) (the_Addr v))
               in case pc' of
                  None \<Rightarrow> match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M) = None
                | Some pc'' \<Rightarrow> \<exists>d. match_ex_table (PROG P) Cl pc (ex_table_of (PROG P) C M)
                                  = \<lfloor>(pc'', d)\<rfloor>
    )\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"

  | CFG_Throw_prop: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = Throw;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (stkAt s (stkLength (P, C, M) pc - 1)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Throw_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    pc' \<noteq> length (instrs_of (PROG P) C M);
    instrs_of (PROG P) C M ! pc = Throw;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (stkAt s (stkLength (P, C, M) pc - 1)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Invoke_Check_NP_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - Suc n) \<noteq> Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Normal)"
  | CFG_Invoke_Check_NP_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    pc' = (case (match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M)) of
             None \<Rightarrow> None
           | Some (pc'', d) \<Rightarrow> \<lfloor>pc''\<rfloor>);
    ek = (\<lambda>s. stkAt s (stkLength (P, C, M) pc - Suc n) = Null)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional pc' Enter)"
  | CFG_Invoke_NP_prop: "\<lbrakk> C \<noteq> ClassMain P;
    (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = \<Up>(\<lambda>s. s(Exception \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional None Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Invoke_NP_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = \<Up>(\<lambda>s. s(Exception := None)
                (Stack (stkLength (P, C, M) pc' - 1) \<mapsto> Value (Addr (addr_of_sys_xcpt NullPointer)))) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Invoke_Call: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    TYPING P C M ! pc = \<lfloor>(ST, LT)\<rfloor>;
    ST ! n = Class D';
    PROG P \<turnstile> D' sees M':Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in D;
    Q = (\<lambda>(s, ret). let r = stkAt s (stkLength (P, C, M) pc - Suc n);
                        C' = fst (the (heap_of s (the_Addr r)))
                     in D = fst (method (PROG P) C' M'));
    paramDefs = (\<lambda>s. s Heap)
                # (\<lambda>s. s (Stack (stkLength (P, C, M) pc - Suc n)))
                # (rev (map (\<lambda>i. (\<lambda>s. s (Stack (stkLength (P, C, M) pc - Suc i)))) [0..<n]));
    ek = Q:(C, M, pc)\<hookrightarrow>\<^bsub>(D,M')\<^esub>paramDefs
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Normal) -(ek)\<rightarrow> (D, M', None, Enter)"
  | CFG_Invoke_False: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = (\<lambda>s. False)\<^sub>\<surd>
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Normal) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Return)"
  | CFG_Invoke_Return_Check_Normal: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Return);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    (TYPING P) C M ! pc = \<lfloor>(ST, LT)\<rfloor>;
    ST ! n \<noteq> NT;
    ek = (\<lambda>s. s Exception = None)\<^sub>\<surd>
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Return) -(ek)\<rightarrow> (C, M, \<lfloor>Suc pc\<rfloor>, Enter)"
  | CFG_Invoke_Return_Check_Exceptional: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Return);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', diff)\<rfloor>;
    pc' \<noteq> length (instrs_of (PROG P) C M);
    ek = (\<lambda>s. \<exists>v d. s Exception = \<lfloor>v\<rfloor> \<and>
                  match_ex_table (PROG P) (cname_of (heap_of s) (the_Addr (the_Value v))) pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d)\<rfloor>)\<^sub>\<surd>
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Return) -(ek)\<rightarrow> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return)"
  | CFG_Invoke_Return_Exceptional_handle: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = \<Up>(\<lambda>s. s(Exception := None,
                 Stack (stkLength (P, C, M) pc' - 1) := s Exception)) \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return) -(ek)\<rightarrow> (C, M, \<lfloor>pc'\<rfloor>, Enter)"
  | CFG_Invoke_Return_Exceptional_prop: "\<lbrakk> C \<noteq> ClassMain P;
    (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Return);
    instrs_of (PROG P) C M ! pc = Invoke M' n;
    ek = (\<lambda>s. \<exists>v. s Exception = \<lfloor>v\<rfloor> \<and>
              match_ex_table (PROG P) (cname_of (heap_of s) (the_Addr (the_Value v))) pc (ex_table_of (PROG P) C M) = None)\<^sub>\<surd> \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Return) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Return: "\<lbrakk> C \<noteq> ClassMain P; (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter);
    instrs_of (PROG P) C M ! pc = instr.Return;
    ek = \<Up>(\<lambda>s. s(Stack 0 := s (Stack (stkLength (P, C, M) pc - 1))))
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, \<lfloor>pc\<rfloor>, Enter) -(ek)\<rightarrow> (C, M, None, Return)"
  | CFG_Return_from_Method: "\<lbrakk> (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Return);
    (P, C0, Main) \<turnstile> (C', M', \<lfloor>pc'\<rfloor>, Normal) -(Q':(C', M', pc')\<hookrightarrow>\<^bsub>(C,M)\<^esub>ps)\<rightarrow> (C, M, None, Enter);
    Q = (\<lambda>(s, ret). ret = (C', M', pc'));
    stateUpdate = (\<lambda>s s'. s'(Heap := s Heap,
                            Exception := s Exception,
                            Stack (stkLength (P, C', M') (Suc pc') - 1) := s (Stack 0))
                  );
    ek = Q\<hookleftarrow>\<^bsub>(C, M)\<^esub>stateUpdate
  \<rbrakk>
  \<Longrightarrow> (P, C0, Main) \<turnstile> (C, M, None, Return) -(ek)\<rightarrow> (C', M', \<lfloor>pc'\<rfloor>, Return)"


(* This takes veeeery long *)
lemma JVMCFG_edge_det: "\<lbrakk> P \<turnstile> n -(et)\<rightarrow> n'; P \<turnstile> n -(et')\<rightarrow> n' \<rbrakk> \<Longrightarrow> et = et'"
  by (erule JVMCFG.cases) (erule JVMCFG.cases, (fastforce dest: sees_method_fun)+)+

lemma sourcenode_reachable: "P \<turnstile> n -(ek)\<rightarrow> n' \<Longrightarrow> P \<turnstile> \<Rightarrow>n"
  by (erule JVMCFG.cases, auto)

lemma targetnode_reachable:
  assumes edge: "P \<turnstile> n -(ek)\<rightarrow> n'"
  shows "P \<turnstile> \<Rightarrow>n'"
proof -
  from edge have "P \<turnstile> \<Rightarrow>n"
    by -(drule sourcenode_reachable)
  with edge show ?thesis
    by -(rule JVMCFG_reachable.intros)
qed

lemmas JVMCFG_reachable_inducts = JVMCFG_reachable.inducts[split_format (complete)]

lemma ClassMain_imp_MethodMain:
  "(P, C0, Main) \<turnstile> (C', M', pc', nt') -ek\<rightarrow> (ClassMain P, M, pc, nt) \<Longrightarrow> M = MethodMain P"
  "(P, C0, Main) \<turnstile> \<Rightarrow>(ClassMain P, M, pc, nt) \<Longrightarrow> M = MethodMain P"
proof (induct P=="P" C0\<equiv>"C0" Main\<equiv>Main C' M' pc' nt' ek C''=="ClassMain P" M pc nt and
              P=="P" C0\<equiv>"C0" Main\<equiv>Main C'=="ClassMain P" M pc nt
       rule: JVMCFG_reachable_inducts)
  case CFG_Return_from_Method
  thus ?case
    by (fastforce elim: JVMCFG.cases)
qed auto

lemma ClassMain_no_Call_target [dest!]:
  "(P, C0, Main) \<turnstile> (C, M, pc, nt) -Q:(C', M', pc')\<hookrightarrow>\<^bsub>(D,M'')\<^esub>paramDefs\<rightarrow> (ClassMain P, M''', pc'', nt')
  \<Longrightarrow> False"
  and
  "(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, pc, nt) \<Longrightarrow> True"
  by (induct  P C0 Main C M pc nt ek=="Q:(C', M', pc')\<hookrightarrow>\<^bsub>(D,M'')\<^esub>paramDefs"
                         C''=="ClassMain P" M''' pc'' nt' and
               P C0 Main C M pc nt
    rule: JVMCFG_reachable_inducts) auto

lemma method_of_src_and_trg_exists:
  "\<lbrakk> (P, C0, Main) \<turnstile> (C', M', pc', nt') -ek\<rightarrow> (C, M, pc, nt); C \<noteq> ClassMain P; C' \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> (\<exists>Ts T mb. (PROG P) \<turnstile> C sees M:Ts\<rightarrow>T = mb in C) \<and>
     (\<exists>Ts T mb. (PROG P) \<turnstile> C' sees M':Ts\<rightarrow>T = mb in C')"
  and method_of_reachable_node_exists:
  "\<lbrakk> (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, pc, nt); C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> \<exists>Ts T mb. (PROG P) \<turnstile> C sees M:Ts\<rightarrow>T = mb in C"
proof (induct rule: JVMCFG_reachable_inducts)
  case CFG_Invoke_Call
  thus ?case
    by (blast dest: sees_method_idemp)
next
  case (reachable_step P C0 Main C M pc nt ek C' M' pc' nt')
  show ?case
  proof (cases "C = ClassMain P")
    case True
    with \<open>(P, C0, Main) \<turnstile> (C, M, pc, nt) -ek\<rightarrow> (C', M', pc', nt')\<close> \<open>C' \<noteq> ClassMain P\<close>
    show ?thesis
    proof cases
      case Main_Call
      thus ?thesis
        by (blast dest: sees_method_idemp)
    qed auto
  next
    case False
    with reachable_step show ?thesis
      by simp
  qed
qed simp_all

lemma "\<lbrakk> (P, C0, Main) \<turnstile> (C', M', pc', nt') -ek\<rightarrow> (C, M, pc, nt); C \<noteq> ClassMain P; C' \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> (case pc of None \<Rightarrow> True |
    \<lfloor>pc''\<rfloor> \<Rightarrow> (TYPING P) C M ! pc'' \<noteq> None \<and> pc'' < length (instrs_of (PROG P) C M)) \<and>
  (case pc' of None \<Rightarrow> True |
    \<lfloor>pc''\<rfloor> \<Rightarrow> (TYPING P) C' M' ! pc'' \<noteq> None \<and> pc'' < length (instrs_of (PROG P) C' M'))"
  and instr_of_reachable_node_typable: "\<lbrakk> (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, pc, nt); C \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> case pc of None \<Rightarrow> True |
  \<lfloor>pc''\<rfloor> \<Rightarrow> (TYPING P) C M ! pc'' \<noteq> None \<and> pc'' < length (instrs_of (PROG P) C M)"
proof (induct rule: JVMCFG_reachable_inducts)
  case (CFG_Load C P C0 Main M pc n ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Load show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Store C P C0 Main M pc n ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Store show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Push C P C0 Main M pc v ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Push show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Pop C P C0 Main M pc ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Pop show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_IAdd C P C0 Main M pc ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_IAdd show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Goto C P C0 Main M pc i)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Goto show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_CmpEq C P C0 Main M pc ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_CmpEq show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_IfFalse_False C P C0 Main M pc i ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_IfFalse_False show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_IfFalse_True C P C0 Main M pc i ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_IfFalse_True show ?case
    using [[simproc del: list_to_set_comprehension]] by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_New_Update C P C0 Main M pc Cl ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_New_Update show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_New_Exceptional_handle C P C0 Main M pc pc' Cl ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = New Cl\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> New Cl,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = New Cl\<close> obtain d'
    where "match_ex_table (PROG P) OutOfMemory pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) OutOfMemory pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = New Cl\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Getfield_Update C P C0 Main M pc F Cl ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Getfield_Update show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Getfield_Exceptional_handle C P C0 Main M pc pc' F Cl ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Getfield F Cl,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close> obtain d'
    where "match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) NullPointer pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Getfield F Cl\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Putfield_Update C P C0 Main M pc F Cl ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Normal)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Putfield_Update show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Putfield_Exceptional_handle C P C0 Main M pc pc' F Cl ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Putfield F Cl,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close> obtain d'
    where "match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) NullPointer pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Putfield F Cl\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Checkcast_Check_Normal C P C0 Main M pc Cl ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Checkcast_Check_Normal show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next
  case (CFG_Checkcast_Exceptional_handle C P C0 Main M pc pc' Cl ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Checkcast Cl,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close> obtain d'
    where "match_ex_table (PROG P) ClassCast pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) ClassCast pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Checkcast Cl\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Throw_handle C P C0 Main M pc pc' ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Throw,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Throw\<close> obtain d' Exc
    where "match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) Exc pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Throw\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Invoke_NP_handle C P C0 Main M pc pc' M' n ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Invoke M' n,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> obtain d'
    where "match_ex_table (PROG P) NullPointer pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) NullPointer pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Invoke_Return_Exceptional_handle C P C0 Main M pc pc' M' n ek)
  hence "TYPING P C M ! pc \<noteq> None" and "pc < length (instrs_of (PROG P) C M)"
    by simp_all
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 where
    "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, instrs_of (PROG P) C M, ex_table_of (PROG P) C M) in C"
    by (fastforce dest: method_of_reachable_node_exists)
  with \<open>pc < length (instrs_of (PROG P) C M)\<close> \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
  have "PROG P,T,mxs,length (instrs_of (PROG P) C M),ex_table_of (PROG P) C M
    \<turnstile> Invoke M' n,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
  moreover from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Exceptional \<lfloor>pc'\<rfloor> Return)\<close> \<open>C \<noteq> ClassMain P\<close>
    \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close> obtain d' Exc
    where "match_ex_table (PROG P) Exc pc (ex_table_of (PROG P) C M) = \<lfloor>(pc', d')\<rfloor>"
    by cases (fastforce elim: JVMCFG.cases)
  hence "\<exists>(f, t, D, h, d)\<in>set (ex_table_of (PROG P) C M).
    matches_ex_entry (PROG P) Exc pc (f, t, D, h, d) \<and> h = pc' \<and> d = d'"
    by -(drule match_ex_table_SomeD)
  ultimately show ?case using \<open>instrs_of (PROG P) C M ! pc = Invoke M' n\<close>
    by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
next
  case (CFG_Invoke_Return_Check_Normal C P C0 Main M pc M' n ST LT ek)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, Return)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with CFG_Invoke_Return_Check_Normal show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr [OF wf_jvmprog_is_wf_typ])
next 
  case (Method_LTrue P C0 Main C M)
  from \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, None, Enter)\<close> \<open>C \<noteq> ClassMain P\<close>
  obtain Ts T mxs mxl\<^sub>0 "is" xt where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "instrs_of (PROG P) C M = is"
    by -(drule method_of_reachable_node_exists, auto)
  with Method_LTrue show ?case
    by (fastforce dest!: wt_jvm_prog_impl_wt_start [OF wf_jvmprog_is_wf_typ] simp: wt_start_def)
next
  case (reachable_step P C0 Main C M opc nt ek C' M' opc' nt')
  thus ?case
    by (cases "C = ClassMain P") (fastforce elim: JVMCFG.cases, simp)
qed simp_all

lemma reachable_node_impl_wt_instr:
  assumes "(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, nt)"
  and "C \<noteq> ClassMain P"
  shows "\<exists>T mxs mpc xt. PROG P,T,mxs,mpc,xt \<turnstile> (instrs_of (PROG P) C M ! pc),pc :: TYPING P C M"
proof -
  from \<open>C \<noteq> ClassMain P\<close> \<open>(P, C0, Main) \<turnstile> \<Rightarrow>(C, M, \<lfloor>pc\<rfloor>, nt)\<close>
    method_of_reachable_node_exists [of P C0 Main C M "\<lfloor>pc\<rfloor>" nt]
    instr_of_reachable_node_typable [of P C0 Main C M "\<lfloor>pc\<rfloor>" nt]
  obtain Ts T mxs mxl\<^sub>0 "is" xt
    where "PROG P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl\<^sub>0, is, xt) in C"
    and "TYPING P C M ! pc \<noteq> None"
    and "pc < length (instrs_of (PROG P) C M)"
    by fastforce+
  with wf_jvmprog_is_wf_typ [of P]
  have "PROG P,T,mxs,length is,xt \<turnstile> instrs_of (PROG P) C M ! pc,pc :: TYPING P C M"
    by (fastforce dest!: wt_jvm_prog_impl_wt_instr)
  thus ?thesis
    by blast
qed

lemma
  "\<lbrakk> (P, C0, Main) \<turnstile> (C, M, pc, nt) -ek\<rightarrow> (C', M', pc', nt'); C \<noteq> ClassMain P \<or> C' \<noteq> ClassMain P \<rbrakk>
  \<Longrightarrow> \<exists>T mb D. PROG P \<turnstile> C0 sees Main:[]\<rightarrow>T = mb in D"
  and reachable_node_impl_Main_ex:
  "\<lbrakk> (P, C0, Main) \<turnstile> \<Rightarrow>(C, M, pc, nt); C \<noteq> ClassMain P\<rbrakk>
  \<Longrightarrow> \<exists>T mb D. PROG P \<turnstile> C0 sees Main:[]\<rightarrow>T = mb in D"
  by (induct rule: JVMCFG_reachable_inducts) fastforce+

end
