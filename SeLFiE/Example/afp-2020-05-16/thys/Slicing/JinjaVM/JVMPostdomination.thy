chapter \<open>Standard and Weak Control Dependence\<close>

section \<open>A type for well-formed programs\<close>

theory JVMPostdomination imports JVMInterpretation "../Basic/Postdomination" begin

text \<open>
For instantiating \<open>Postdomination\<close> every node in the CFG of a program must be
reachable from the \<open>(_Entry_)\<close> node and there must be a path to the
\<open>(_Exit_)\<close> node from each node.

Therefore, we restrict the set of allowed programs to those, where the CFG fulfills
these requirements. This is done by defining a new type for well-formed programs.
The universe of every type in Isabelle must be non-empty. That's why we first
define an example program \<open>EP\<close> and its typing \<open>Phi_EP\<close>, which
is a member of the carrier set of the later defined type.

Restricting the set of allowed programs in this way is reasonable, as Jinja's compiler
only produces byte code programs, that are members of this type (A proof for this is
current work).
\<close>

definition EP :: jvm_prog
  where "EP = (''C'', Object, [], [(''M'', [], Void, 1::nat, 0::nat, [Push Unit, Return], [])]) #
  SystemClasses"

definition Phi_EP :: ty\<^sub>P
  where "Phi_EP C M = (if C = ''C'' \<and> M = ''M'' then [\<lfloor>([],[OK (Class ''C'')])\<rfloor>,\<lfloor>([Void],[OK (Class ''C'')])\<rfloor>] else [])"

text \<open>
Now we show, that \<open>EP\<close> is indeed a well-formed program in the sense of Jinja's
byte code verifier
\<close>

lemma distinct_classes'':
  "''C'' \<noteq> Object"
  "''C'' \<noteq> NullPointer"
  "''C'' \<noteq> OutOfMemory"
  "''C'' \<noteq> ClassCast"
  by (simp_all add: Object_def NullPointer_def OutOfMemory_def ClassCast_def)

lemmas distinct_classes =
  distinct_classes distinct_classes'' distinct_classes'' [symmetric]
  
declare distinct_classes [simp add]

lemma i_max_2D: "i < Suc (Suc 0) \<Longrightarrow> i = 0 \<or> i = 1"
  by auto

lemma EP_wf: "wf_jvm_prog\<^bsub>Phi_EP\<^esub> EP"
  unfolding wf_jvm_prog_phi_def wf_prog_def
proof
  show "wf_syscls EP"
    by (simp add: EP_def wf_syscls_def SystemClasses_def sys_xcpts_def
                  ObjectC_def NullPointerC_def OutOfMemoryC_def ClassCastC_def)
next
  have distinct_EP: "distinct_fst EP"
    by (auto simp:
      EP_def SystemClasses_def ObjectC_def NullPointerC_def OutOfMemoryC_def ClassCastC_def)
  have classes_wf:
    "\<forall>c\<in>set EP.
        wf_cdecl
         (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M))
         EP c"
  proof
    fix C
    assume C_in_EP: "C \<in> set EP"
    show "wf_cdecl
         (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M))
         EP C"
    proof (cases "C \<in> set SystemClasses")
      case True
      thus ?thesis
        by (auto simp: wf_cdecl_def SystemClasses_def ObjectC_def NullPointerC_def
                       OutOfMemoryC_def ClassCastC_def EP_def class_def)
    next
      case False
      with C_in_EP
      have [simp]: "C = (''C'', the (class EP ''C''))"
        by (auto simp: EP_def SystemClasses_def class_def)
      show ?thesis
        apply (auto dest!: i_max_2D
                     simp: wf_cdecl_def class_def EP_def wf_mdecl_def wt_method_def Phi_EP_def
                           wt_start_def check_types_def states_def JVM_SemiType.sl_def
                           stk_esl_def upto_esl_def loc_sl_def SemiType.esl_def
                           SemiType.sup_def Err.sl_def Err.le_def err_def Listn.sl_def
                           Err.esl_def Opt.esl_def Product.esl_def relevant_entries_def)
          apply (fastforce simp: SystemClasses_def ObjectC_def)
         apply (clarsimp simp: Method_def)
         apply (cases rule: Methods.cases,
                (fastforce simp: class_def SystemClasses_def ObjectC_def)+)
        apply (clarsimp simp: Method_def)
        by (cases rule: Methods.cases,
            (fastforce simp: class_def SystemClasses_def ObjectC_def)+)
    qed
  qed
  with distinct_EP
  show "(\<forall>c\<in>set EP.
    wf_cdecl
      (\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (Phi_EP C M))
      EP c) \<and>
    distinct_fst EP"
    by simp
qed

lemma [simp]: "Abs_wf_jvmprog (EP, Phi_EP)\<^bsub>wf\<^esub> = EP"
proof (cases "(EP, Phi_EP) \<in> wf_jvmprog")
  case True
  thus ?thesis
    by (simp add: Abs_wf_jvmprog_inverse)
next
  case False
  with EP_wf
  show ?thesis
    by (simp add: wf_jvmprog_def)
qed

lemma [simp]: "Abs_wf_jvmprog (EP, Phi_EP)\<^bsub>\<Phi>\<^esub> = Phi_EP"
proof (cases "(EP, Phi_EP) \<in> wf_jvmprog")
  case True
  thus ?thesis
    by (simp add: Abs_wf_jvmprog_inverse)
next
  case False
  with EP_wf
  show ?thesis
    by (simp add: wf_jvmprog_def)
qed

(*
lemma sees_method_instruct_listD:
  "((C, D, Fds, (((M::char list), (Ts:: ty list), (T:: ty), mxs, mxl, is, xt) # meths) ) # cs) \<turnstile> C sees M: Tsa\<rightarrow>Ta = (mxsa, mxla, isa, xta) in C \<Longrightarrow> mxsa = mxs \<and> mxla = mxl \<and> xta = xt \<and> isa = is"
apply (clarsimp simp: Method_def)
apply (erule Methods.cases)
 apply (clarsimp simp: class_def)
by (clarsimp simp: class_def)
*)

lemma method_in_EP_is_M:
  "EP \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, is, xt) in D
  \<Longrightarrow> C = ''C'' \<and>
     M = ''M'' \<and>
     Ts = [] \<and>
     T = Void \<and>
     mxs = 1 \<and>
     mxl = 0 \<and>
     is = [Push Unit, Return] \<and>
     xt = [] \<and>
     D = ''C''"
apply (clarsimp simp: Method_def EP_def)
apply (erule Methods.cases, clarsimp simp: class_def SystemClasses_def ObjectC_def)
apply (clarsimp simp: class_def)
apply (erule Methods.cases)
 by (fastforce simp: class_def SystemClasses_def ObjectC_def NullPointerC_def
                       OutOfMemoryC_def ClassCastC_def if_split_eq1)+

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
  "EP \<turnstile> ''C'' sees ''M'': []\<rightarrow>Void = (1, 0, [Push Unit, Return], []) in ''C''"
apply (auto simp: Method_def EP_def)
apply (rule_tac x="Map.empty(''M'' \<mapsto> (([], Void, 1, 0, [Push Unit, Return], []),''C''))" in exI)
apply auto
apply (rule Methods.intros(2))
   apply (fastforce simp: class_def)
  apply clarsimp
 apply (rule Methods.intros(1))
  apply (fastforce simp: class_def SystemClasses_def ObjectC_def)
 apply fastforce
by fastforce

lemma instrs_of_EP_C_M [simp]:
  "instrs_of EP ''C'' ''M'' = [Push Unit, Return]"
  using C_sees_M_in_EP
apply (simp add: method_def)
apply (rule theI2)
  apply fastforce
 apply (clarsimp dest!: method_in_EP_is_M)
by (clarsimp dest!: method_in_EP_is_M)

(*
lemma valid_cs_seesM_D: 
  "valid_callstack (P, C0, Main) ((C, M, pc)#cs) \<Longrightarrow>
  \<exists>Ts T mxs mxl is xt. (P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T=(mxs, mxl, is, xt) in C \<and> pc < length is"
  by (cases cs, fastforce+)
*)

lemma valid_node_in_EP_D:
  "valid_node (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') n
  \<Longrightarrow> n \<in> {(_Entry_), (_ [(''C'', ''M'', 0)],None _), (_ [(''C'', ''M'', 1)],None _), (_Exit_)}"
proof -
  assume vn: "valid_node (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') n"
  show ?thesis
  proof (cases n)
    case Entry
    thus ?thesis
      by simp
  next
    case [simp]: (Node cs opt)
    show ?thesis
    proof (cases opt)
      case [simp]: None
      from vn
      show ?thesis
        apply (cases cs)
         apply simp
        apply (case_tac list)
         apply clarsimp
         apply (drule method_in_EP_is_M)
         apply clarsimp
        apply clarsimp
        apply (drule method_in_EP_is_M)
        apply clarsimp
        apply (case_tac lista)
         apply clarsimp
         apply (drule method_in_EP_is_M)
         apply clarsimp
         apply (case_tac ba, clarsimp, clarsimp)
        apply clarsimp
        apply (drule method_in_EP_is_M)
        apply clarsimp
        by (case_tac ba, clarsimp, clarsimp)
    next
      case [simp]: (Some f)
      obtain cs'' xf where [simp]: "f = (cs'', xf)"
        by (cases f, fastforce)
      from vn
      show ?thesis
        apply (cases cs)
         apply clarsimp
         apply (erule JVM_CFG.cases, clarsimp+)
        apply (case_tac list)
         apply clarsimp
         apply (frule method_in_EP_is_M)
         apply (case_tac b)
          apply (erule JVM_CFG.cases, clarsimp+)
         apply (erule JVM_CFG.cases, clarsimp+)
        apply (frule method_in_EP_is_M)
        apply (case_tac b)
         apply (erule JVM_CFG.cases, clarsimp+)
        by (erule JVM_CFG.cases, clarsimp+)
    qed
  qed
qed

lemma EP_C_M_0_valid [simp]:
  "JVM_CFG_Interpret.valid_node (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') 
    (_ [(''C'', ''M'', 0)],None _)"
proof -
  have "valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'')
    ((_Entry_), (\<lambda>s. True)\<^sub>\<surd>, (_ [(''C'', ''M'', 0)],None _))"
    apply (auto simp: Phi_EP_def)
    by rule auto
  thus ?thesis
    by (fastforce simp: JVM_CFG_Interpret.valid_node_def)
qed

lemma EP_C_M_Suc_0_valid [simp]:
  "JVM_CFG_Interpret.valid_node (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'') 
    (_ [(''C'', ''M'', Suc 0)],None _)"
proof -
  have "valid_edge (Abs_wf_jvmprog (EP, Phi_EP), ''C'', ''M'')
    ((_ [(''C'', ''M'', Suc 0)],None _), \<Up>id, (_Exit_))"
    apply (auto simp: Phi_EP_def)
    by rule auto
  thus ?thesis
    by (fastforce simp: JVM_CFG_Interpret.valid_node_def)
qed


definition
  "cfg_wf_prog =
    {P. (\<forall>n. valid_node P n \<longrightarrow>
         (\<exists>as. JVM_CFG_Interpret.path P (_Entry_) as n) \<and>
         (\<exists>as. JVM_CFG_Interpret.path P n as (_Exit_)))}"

typedef cfg_wf_prog = cfg_wf_prog
  unfolding cfg_wf_prog_def
proof
  let ?prog = "((Abs_wf_jvmprog (EP, Phi_EP)), ''C'', ''M'')"
  let ?edge0 = "((_Entry_), (\<lambda>s. False)\<^sub>\<surd>, (_Exit_))"
  let ?edge1 = "((_Entry_), (\<lambda>s. True)\<^sub>\<surd>, (_ [(''C'', ''M'', 0)],None _))"
  let ?edge2 = "((_ [(''C'', ''M'', 0)],None _),
                 \<Up>(\<lambda>(h, stk, loc). (h, stk((0, 0) := Unit), loc)),
                 (_ [(''C'', ''M'', 1)],None _))"
  let ?edge3 = "((_ [(''C'', ''M'', 1)],None _), \<Up>id, (_Exit_))"
  show "?prog \<in> {P. \<forall>n. valid_node P n \<longrightarrow>
                 (\<exists>as. CFG.path sourcenode targetnode (valid_edge P) (_Entry_) as n) \<and>
                 (\<exists>as. CFG.path sourcenode targetnode (valid_edge P) n as (_Exit_))}"
  proof (auto dest!: valid_node_in_EP_D)
    have "JVM_CFG_Interpret.path ?prog (_Entry_) [] (_Entry_)"
      by (simp add: JVM_CFG_Interpret.path.empty_path)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Entry_) as (_Entry_)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_Entry_) [?edge0] (_Exit_)"
      by rule (auto intro: JCFG_EntryExit JVM_CFG_Interpret.path.empty_path)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Entry_) as (_Exit_)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_Entry_) [?edge1] (_ [(''C'', ''M'', 0)],None _)"
      by rule (auto intro: JCFG_EntryStart simp: JVM_CFG_Interpret.path.empty_path Phi_EP_def)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Entry_) as (_ [(''C'', ''M'', 0)],None _)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_ [(''C'', ''M'', 0)],None _) [?edge2, ?edge3] (_Exit_)"
      apply rule
         apply rule
            apply (auto simp: JVM_CFG_Interpret.path.empty_path Phi_EP_def)
       apply (rule JCFG_ReturnExit, auto)
      by (rule JCFG_Straight_NoExc, auto simp: Phi_EP_def)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_ [(''C'', ''M'', 0)],None _) as (_Exit_)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_Entry_) [?edge1, ?edge2] (_ [(''C'', ''M'', 1)],None _)"
      apply rule
         apply rule
            apply (auto simp: JVM_CFG_Interpret.path.empty_path Phi_EP_def)
       apply (rule JCFG_Straight_NoExc, auto simp: Phi_EP_def)
      by (rule JCFG_EntryStart, auto)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Entry_) as (_ [(''C'', ''M'', Suc 0)],None _)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_ [(''C'', ''M'', Suc 0)],None _) [?edge3] (_Exit_)"
      apply rule
         apply (auto simp: JVM_CFG_Interpret.path.empty_path Phi_EP_def)
      by (rule JCFG_ReturnExit, auto)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_ [(''C'', ''M'', Suc 0)],None _) as (_Exit_)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_Entry_) [?edge0] (_Exit_)"
      by rule (auto intro: JCFG_EntryExit JVM_CFG_Interpret.path.empty_path)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Entry_) as (_Exit_)"
      by fastforce
  next
    have "JVM_CFG_Interpret.path ?prog (_Exit_) [] (_Exit_)"
      by (simp add: JVM_CFG_Interpret.path.empty_path)
    thus "\<exists>as. JVM_CFG_Interpret.path ?prog (_Exit_) as (_Exit_)"
      by fastforce
  qed
qed


abbreviation lift_to_cfg_wf_prog :: "(jvmprog \<Rightarrow> 'a) \<Rightarrow> (cfg_wf_prog \<Rightarrow> 'a)"
  ("_\<^bsub>CFG\<^esub>")
  where "f\<^bsub>CFG\<^esub> \<equiv> (\<lambda>P. f (Rep_cfg_wf_prog P))"

section \<open>Interpretation of the \<open>Postdomination\<close> locale\<close>

interpretation JVM_CFG_Postdomination:
  Postdomination "sourcenode" "targetnode" "kind" "valid_edge\<^bsub>CFG\<^esub> prog" "Entry" "(_Exit_)"
  for prog
proof(unfold_locales)
  fix n
  assume vn: "CFG.valid_node sourcenode targetnode (valid_edge\<^bsub>CFG\<^esub> prog) n" 
  have prog_is_cfg_wf_prog: "Rep_cfg_wf_prog prog \<in> cfg_wf_prog"
    by (rule Rep_cfg_wf_prog)
  obtain P C0 Main where [simp]: "Rep_cfg_wf_prog prog = (P,C0,Main)"
    by (cases "Rep_cfg_wf_prog prog", fastforce)
  from prog_is_cfg_wf_prog have "(P, C0, Main) \<in> cfg_wf_prog"
    by simp
  hence "valid_node (P, C0, Main) n \<longrightarrow>
    (\<exists>as. CFG.path sourcenode targetnode (valid_edge (P, C0, Main)) (_Entry_) as n)"
    by (fastforce simp: cfg_wf_prog_def)
  moreover from vn have "valid_node (P, C0, Main) n"
    by (auto simp: JVM_CFG_Interpret.valid_node_def)
  ultimately
  show "\<exists>as. CFG.path sourcenode targetnode (valid_edge\<^bsub>CFG\<^esub> prog) (_Entry_) as n"
    by simp
next
  fix n
  assume vn: "CFG.valid_node sourcenode targetnode (valid_edge\<^bsub>CFG\<^esub> prog) n" 
  have prog_is_cfg_wf_prog: "Rep_cfg_wf_prog prog \<in> cfg_wf_prog"
    by (rule Rep_cfg_wf_prog)
  obtain P C0 Main where [simp]: "Rep_cfg_wf_prog prog = (P,C0,Main)"
    by (cases "Rep_cfg_wf_prog prog", fastforce)
  from prog_is_cfg_wf_prog have "(P, C0, Main) \<in> cfg_wf_prog"
    by simp
  hence "valid_node (P, C0, Main) n \<longrightarrow>
    (\<exists>as. CFG.path sourcenode targetnode (valid_edge (P, C0, Main)) n as (_Exit_))"
    by (fastforce simp: cfg_wf_prog_def)
  moreover from vn have "valid_node (P, C0, Main) n"
    by (auto simp: JVM_CFG_Interpret.valid_node_def)
  ultimately
  show "\<exists>as. CFG.path sourcenode targetnode (valid_edge\<^bsub>CFG\<^esub> prog) n as (_Exit_)"
    by simp
qed


section \<open>Interpretation of the \<open>StrongPostdomination\<close> locale\<close>

subsection \<open>Some helpfull lemmas\<close>

lemma find_handler_for_tl_eq:
  "find_handler_for P Exc cs = (C,M,pcx)#cs' \<Longrightarrow> \<exists>cs'' pc. cs = cs'' @ [(C,M,pc)] @ cs'"
  by (induct cs, auto)

lemma valid_callstack_tl:
  "valid_callstack prog ((C,M,pc)#cs) \<Longrightarrow> valid_callstack prog cs"
  by (cases prog, cases cs, auto)

lemma find_handler_Throw_Invoke_pc_in_range:
  "\<lbrakk>cs = (C',M',pc')#cs'; valid_callstack (P,C0,Main) cs;
  instrs_of (P\<^bsub>wf\<^esub>) C' M' ! pc' = Throw \<or> (\<exists>M'' n''. instrs_of (P\<^bsub>wf\<^esub>) C' M' ! pc' = Invoke M'' n'');
  find_handler_for P Exc cs = (C,M,pc)#cs'' \<rbrakk>
  \<Longrightarrow> pc < length (instrs_of (P\<^bsub>wf\<^esub>) C M)"
proof (induct cs arbitrary: C' M' pc' cs')
  case Nil
  thus ?case by simp
next
  case (Cons a cs)
  hence [simp]: "a = (C',M',pc')" and [simp]: "cs = cs'" by simp_all
  note IH = \<open>\<And>C' M' pc' cs'.
           \<lbrakk>cs = (C', M', pc') # cs'; valid_callstack (P, C0, Main) cs;
            instrs_of P\<^bsub>wf\<^esub> C' M' ! pc' = Throw \<or>
            (\<exists>M'' n''. instrs_of P\<^bsub>wf\<^esub> C' M' ! pc' = Invoke M'' n'');
            find_handler_for P Exc cs = (C, M, pc) # cs''\<rbrakk>
           \<Longrightarrow> pc < length (instrs_of P\<^bsub>wf\<^esub> C M)\<close>
  note throw = \<open>instrs_of P\<^bsub>wf\<^esub> C' M' ! pc' = Throw \<or> (\<exists>M'' n''. instrs_of P\<^bsub>wf\<^esub> C' M' ! pc' = Invoke M'' n'')\<close>
  note fhf = \<open>find_handler_for P Exc (a # cs) = (C, M, pc) # cs''\<close>
  note v_cs_a_cs = \<open>valid_callstack (P, C0, Main) (a # cs)\<close>
  show ?case
  proof (cases "match_ex_table (P\<^bsub>wf\<^esub>) Exc pc' (ex_table_of (P\<^bsub>wf\<^esub>) C' M')")
    case None
    with fhf have fhf_tl: "find_handler_for P Exc cs = (C,M,pc)#cs''"
      by simp
    from v_cs_a_cs have "valid_callstack (P, C0, Main) cs"
      by (auto dest: valid_callstack_tl)
    from v_cs_a_cs
    have "cs \<noteq> [] \<longrightarrow> (let (C,M,pc) = hd cs in \<exists>n. instrs_of (P\<^bsub>wf\<^esub>) C M ! pc = Invoke M' n)"
      by (cases cs', auto)
    with IH None fhf_tl \<open>valid_callstack (P, C0, Main) cs\<close>
    show ?thesis
      by (cases cs) fastforce+
  next
    case (Some xte)
    with fhf have [simp]: "C' = C" and [simp]: "M' = M" by simp_all
    from v_cs_a_cs fhf Some
    obtain Ts T mxs mxl "is" xt where wt_class:
      "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, is, xt) in C \<and>
      pc' < length is \<and> (P\<^bsub>\<Phi>\<^esub>) C M ! pc' \<noteq> None"
      by (cases cs) fastforce+
    with wf_jvmprog_is_wf [of P]
    have wt_instr:"(P\<^bsub>wf\<^esub>),T,mxs,length is,xt \<turnstile> is ! pc',pc' :: (P\<^bsub>\<Phi>\<^esub>) C M"
      by (fastforce dest!: wt_jvm_prog_impl_wt_instr)
    from Some fhf obtain f t D d where "(f,t,D,pc,d)\<in> set (ex_table_of (P\<^bsub>wf\<^esub>) C M) \<and>
      matches_ex_entry (P\<^bsub>wf\<^esub>) Exc pc' (f,t,D,pc,d)"
      by (cases xte, fastforce dest: match_ex_table_SomeD)
    with wt_instr throw wt_class
    show ?thesis
      by (fastforce simp: relevant_entries_def is_relevant_entry_def matches_ex_entry_def)
  qed
qed


subsection \<open>Every node has only finitely many successors\<close>

lemma successor_set_finite:
  "JVM_CFG_Interpret.valid_node prog n 
  \<Longrightarrow> finite {n'. \<exists>a'. valid_edge prog a' \<and> sourcenode a' = n \<and>
                      targetnode a' = n'}"
proof -
  assume valid_node: "JVM_CFG_Interpret.valid_node prog n"
  obtain P C0 Main where [simp]: "prog = (P, C0, Main)"
    by (cases prog, fastforce)
  note P_wf = wf_jvmprog_is_wf [of P]
  show ?thesis
  proof (cases n)
    case Entry
    thus ?thesis
      by (rule_tac B="{(_Exit_), (_ [(C0, Main, 0)],None _)}" in finite_subset,
        auto dest: JVMCFG_EntryD)
  next
    case [simp]: (Node cs x)
    show ?thesis
    proof (cases cs)
      case Nil
      thus ?thesis
        by (rule_tac B="{}" in finite_subset,
          auto elim: JVM_CFG.cases)
    next
      case [simp]: (Cons a cs')
      obtain C M pc where [simp]: "a = (C,M,pc)" by (cases a, fastforce)
      have finite_classes: "finite {C. is_class (P\<^bsub>wf\<^esub>) C}"
        by (rule finite_is_class)
      from valid_node have "is_class (P\<^bsub>wf\<^esub>) C"
        apply (auto simp: JVM_CFG_Interpret.valid_node_def)
         apply (cases x, auto)
          apply (cases cs', auto dest!: sees_method_is_class)
         apply (cases cs', auto dest!: sees_method_is_class)
        apply (cases cs', auto dest!: sees_method_is_class)
         apply (cases x, auto dest!: sees_method_is_class)
        by (cases x, auto dest!: sees_method_is_class)
      show ?thesis
      proof (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
        case (Load nat)
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',x _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case (Store nat)
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',x _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case (Push val)
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',x _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case (New C')
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,pc)#cs',\<lfloor>((C,M,Suc pc)#cs',False)\<rfloor> _),
            (_ (C,M,pc)#cs',\<lfloor>(find_handler_for P OutOfMemory ((C,M,pc)#cs'),True)\<rfloor> _),
            (_ fst(the(x)),None _)}" in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           by (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
      next
        case (Getfield Fd C')
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,pc)#cs',\<lfloor>((C,M,Suc pc)#cs',False)\<rfloor> _),
            (_ (C,M,pc)#cs',\<lfloor>(find_handler_for P NullPointer ((C,M,pc)#cs'),True)\<rfloor> _),
            (_ fst(the(x)),None _)}" in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           by (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
      next
        case (Putfield Fd C')
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,pc)#cs',\<lfloor>((C,M,Suc pc)#cs',False)\<rfloor> _),
            (_ (C,M,pc)#cs',\<lfloor>(find_handler_for P NullPointer ((C,M,pc)#cs'),True)\<rfloor> _),
            (_ fst(the(x)),None _)}" in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           by (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
      next
        case (Checkcast C')
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',None _),
            (_ (C,M,pc)#cs',\<lfloor>(find_handler_for P ClassCast ((C,M,pc)#cs'),True)\<rfloor> _),
            (_ fst(the(x)),None _)}" in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           by (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
      next
        case (Invoke M' n')
        with finite_classes valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="
            {n'. (\<exists>D. is_class (P\<^bsub>wf\<^esub>) D \<and> n' = (_ (C,M,pc)#cs',\<lfloor>((D,M',0)#(C,M,pc)#cs',False)\<rfloor> _))}
            \<union> {(_ (C,M,pc)#cs',\<lfloor>(find_handler_for P NullPointer ((C,M,pc)#cs'),True)\<rfloor> _),
               (_ fst(the(x)),None _)}"
            in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           apply (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
          apply (clarsimp simp del: find_handler_for.simps)
          apply (drule sees_method_is_class)
          by (clarsimp simp del: find_handler_for.simps)
      next
        case Return
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="
            {(_ (fst(hd(cs')),fst(snd(hd(cs'))),Suc(snd(snd(hd(cs')))))#(tl cs'),None _),
             (_Exit_)}" in finite_subset)
           apply (rule subsetI)
           apply (clarsimp simp del: find_handler_for.simps)
           by (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
      next
        case Pop
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',None _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case IAdd
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',None _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case (Goto i)
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,nat (int pc + i))#cs',None _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case CmpEq
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',None _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case (IfFalse i)
        with valid_node
        show ?thesis
          apply auto
          apply (rule_tac B="{(_ (C,M,Suc pc)#cs',None _),
            (_ (C,M,nat (int pc + i))#cs',None _)}" in finite_subset)
           by (auto elim: JVM_CFG.cases)
      next
        case Throw
        have "finite {(l,pc'). l < Suc (length cs') \<and>
          pc' < (\<Sum>i\<le>(length cs'). (length (instrs_of (P\<^bsub>wf\<^esub>) (fst (((C, M, pc) # cs') ! i))
          (fst (snd (((C, M, pc) # cs') ! i))))))}"
          (is "finite ?f1")
          by (auto intro: finite_cartesian_product bounded_nat_set_is_finite)
        hence f_1: "finite {(l,pc'). l < length ((C, M, pc) # cs') \<and>
            pc' < length (instrs_of (P\<^bsub>wf\<^esub>) (fst(((C,M,pc)#cs')!l)) (fst(snd(((C,M,pc)#cs')!l))))}"
          apply (rule_tac B="?f1" in finite_subset)
           apply clarsimp
           apply (rule less_le_trans)
            defer
            apply (rule_tac A="{a}" in sum_mono2)
              by simp_all
        from valid_node Throw
        show ?thesis
          apply auto
          apply (rule_tac B="
            {n'. \<exists>Cx Mx pc' h cs'' pcx. (C,M,pc)#cs' = cs''@[(Cx,Mx,pcx)]@h \<and>
              pc' < length (instrs_of (P\<^bsub>wf\<^esub>) Cx Mx) \<and>
              n' = (_ (C,M,pc)#cs',\<lfloor>((Cx,Mx,pc')#h,True)\<rfloor> _)}
            \<union> {(_ fst(the(x)),None _), (_Exit_), (_ (C,M,pc)#cs',\<lfloor>([],True)\<rfloor> _)}"
            in finite_subset)
           apply (rule subsetI)
           apply clarsimp
           apply (erule JVM_CFG.cases, simp_all del: find_handler_for.simps)
           apply (clarsimp simp del: find_handler_for.simps)
           apply (case_tac "find_handler_for P Exc ((C,M,pc)#cs')", simp)
           apply (clarsimp simp del: find_handler_for.simps)
           apply (erule impE)
            apply (case_tac "list", fastforce, fastforce)
           apply (frule find_handler_for_tl_eq)
           apply (clarsimp simp del: find_handler_for.simps)
           apply (erule_tac x="list" in allE)
           apply (clarsimp simp del: find_handler_for.simps)
          apply (subgoal_tac 
            "finite (
              (\<lambda>(Cx,Mx,pc',h,cs'',pcx).  (_ (C, M, pc) # cs',\<lfloor>((Cx, Mx, pc') # h, True)\<rfloor> _)) `
              {(Cx,Mx,pc',h,cs'',pcx). (C, M, pc) # cs' = cs'' @ (Cx, Mx, pcx) # h \<and>
                pc' < length (instrs_of P\<^bsub>wf\<^esub> Cx Mx)})")
           apply (case_tac "((\<lambda>(Cx, Mx, pc', h, cs'', pcx).
             (_ (C, M, pc) # cs',\<lfloor>((Cx, Mx, pc') # h, True)\<rfloor> _)) `
             {(Cx, Mx, pc', h, cs'', pcx).
               (C, M, pc) # cs' = cs'' @ (Cx, Mx, pcx) # h \<and>
               pc' < length (instrs_of (P\<^bsub>wf\<^esub>) Cx Mx)}) =
             {n'. \<exists>Cx Mx pc' h.
                (\<exists>cs'' pcx. (C, M, pc) # cs' = cs'' @ (Cx, Mx, pcx) # h) \<and>
                pc' < length (instrs_of (P\<^bsub>wf\<^esub>) Cx Mx) \<and>
                n' = (_ (C, M, pc) # cs',\<lfloor>((Cx, Mx, pc') # h, True)\<rfloor> _)}")
            apply clarsimp
           apply (erule notE)
           apply (rule equalityI)
            apply clarsimp
           apply clarsimp
           apply (rule_tac x="(Cx,Mx,pc',h,cs'',pcx)" in image_eqI)
            apply clarsimp
           apply clarsimp
          apply (rule finite_imageI)
          apply (subgoal_tac "finite (
            (\<lambda>(l, pc'). (fst(((C, M, pc)#cs') ! l),
                         fst(snd(((C, M, pc)#cs') ! l)),
                         pc',
                         drop l cs',
                         take l ((C, M, pc)#cs'),
                         snd(snd(((C, M, pc)#cs') ! l))
                        )
            ) ` {(l, pc'). l < length ((C,M,pc)#cs') \<and>
                           pc' < length (instrs_of (P\<^bsub>wf\<^esub>) (fst(((C, M, pc)#cs') ! l))
                                                        (fst(snd(((C, M, pc)#cs') ! l))))})")
           apply (case_tac "((\<lambda>(l, pc').
             (fst (((C, M, pc) # cs') ! l),
              fst (snd (((C, M, pc) # cs') ! l)),
              pc',
              drop l cs',
              take l ((C, M, pc) # cs'),
              snd (snd (((C, M, pc) # cs') ! l))
             )) ` {(l, pc'). l < length ((C,M,pc)#cs') \<and>
                             pc' < length (instrs_of (P\<^bsub>wf\<^esub>) (fst (((C, M, pc) # cs') ! l))
                                                          (fst (snd (((C, M, pc) # cs') ! l))))})
             = {(Cx, Mx, pc', h, cs'', pcx).
                (C, M, pc) # cs' = cs'' @ (Cx, Mx, pcx) # h \<and>
                pc' < length (instrs_of (P\<^bsub>wf\<^esub>) Cx Mx)}")
            apply clarsimp
           apply (erule notE)
           apply (rule equalityI)
            apply clarsimp
            apply (rule id_take_nth_drop [of _ "(C,M,pc)#cs'", simplified])
            apply simp
           apply clarsimp
           apply (rule_tac x="(length ad,ab)" in image_eqI)
            apply clarsimp
            apply (case_tac ad, clarsimp, clarsimp)
           apply clarsimp
           apply (case_tac ad, clarsimp, clarsimp)
          apply (rule finite_imageI)
          by (rule f_1)
      qed
    qed
  qed
qed

subsection \<open>Interpretation of the locale\<close>

interpretation JVM_CFG_StrongPostdomination:
  StrongPostdomination "sourcenode" "targetnode" "kind" "valid_edge\<^bsub>CFG\<^esub> prog" "Entry" "(_Exit_)"
  for prog
proof(unfold_locales)
  fix n
  assume vn: "CFG.valid_node sourcenode targetnode (valid_edge\<^bsub>CFG\<^esub> prog) n"
  thus "finite {n'. \<exists>a'. valid_edge\<^bsub>CFG\<^esub> prog a' \<and> sourcenode a' = n \<and> targetnode a' = n'}"
    by (rule successor_set_finite)
qed

end
