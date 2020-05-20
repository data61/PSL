section \<open>Instantiate well-formedness locales with Proc CFG\<close>

theory WellFormed imports Interpretation Labels "../StaticInter/CFGExit_wf" begin

subsection \<open>Determining the first atomic command\<close>

fun fst_cmd :: "cmd \<Rightarrow> cmd"
where "fst_cmd (c\<^sub>1;;c\<^sub>2) = fst_cmd c\<^sub>1"
  | "fst_cmd c = c"

lemma Proc_CFG_Call_target_fst_cmd_Skip:
  "\<lbrakk>labels prog l' c; prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'\<rbrakk> 
  \<Longrightarrow> fst_cmd c = Skip"
proof(induct arbitrary:n rule:labels.induct) 
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = \<open>\<And>n. c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip\<close>
  from \<open>c\<^sub>1;; c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l\<close> \<open>labels c\<^sub>1 l c\<close>
  have "c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n')(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1)
  note IH = \<open>\<And>n. c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip\<close>
  from \<open>c\<^sub>1;; c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + #:c\<^sub>1)\<close> \<open>labels c\<^sub>2 l c\<close>
  obtain nx where "c\<^sub>2 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases)
    apply(auto dest:Proc_CFG_targetlabel_less_num_nodes Proc_CFG_Call_Labels)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2)
  note IH = \<open>\<And>n. c\<^sub>1 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip\<close>
  from \<open>if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + 1)\<close> \<open>labels c\<^sub>1 l c\<close>
  obtain nx where "c\<^sub>1 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n') apply auto
    by(case_tac n')(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1)
  note IH = \<open>\<And>n. c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip\<close>
  from \<open>if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + #:c\<^sub>1 + 1)\<close> 
    \<open>labels c\<^sub>2 l c\<close>
  obtain nx where "c\<^sub>2 \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n') apply(auto dest:Proc_CFG_targetlabel_less_num_nodes)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileBody c' l c b)
  note IH = \<open>\<And>n. c' \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l \<Longrightarrow> fst_cmd c = Skip\<close>
  from \<open>while (b) c' \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label (l + 2)\<close> \<open>labels c' l c\<close>
  obtain nx where "c' \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l"
    apply - apply(erule Proc_CFG.cases,auto)
    by(case_tac n') auto
  from IH[OF this] show ?case by simp
next
  case (Labels_Call px esx retsx)
  from \<open>Call px esx retsx \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label 1\<close>
  show ?case by(fastforce elim:Proc_CFG.cases)
qed(auto dest:Proc_CFG_Call_Labels)


lemma Proc_CFG_Call_source_fst_cmd_Call:
  "\<lbrakk>labels prog l c; prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'\<rbrakk> 
  \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets"
proof(induct arbitrary:n' rule:labels.induct)
  case (Labels_Base c n')
  from \<open>c \<turnstile> Label 0 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> show ?case
    by(induct c "Label 0" "CEdge (p, es, rets)" n' rule:Proc_CFG.induct) auto
next
  case (Labels_LAss V e n')
  from \<open>V:=e \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> show ?case
    by(fastforce elim:Proc_CFG.cases)
next
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = \<open>\<And>n'. c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets\<close>
  from \<open>c\<^sub>1;; c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>labels c\<^sub>1 l c\<close>
  have "c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n)(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1)
  note IH = \<open>\<And>n'. c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets\<close>
  from \<open>c\<^sub>1;; c\<^sub>2 \<turnstile> Label (l + #:c\<^sub>1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>labels c\<^sub>2 l c\<close>
  obtain nx where "c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases)
    apply(auto dest:Proc_CFG_sourcelabel_less_num_nodes Proc_CFG_Call_Labels)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2)
  note IH = \<open>\<And>n'. c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets\<close>
  from \<open>if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> Label (l + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>labels c\<^sub>1 l c\<close>
  obtain nx where "c\<^sub>1 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n) apply auto
    by(case_tac n)(auto dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case by simp
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1)
  note IH = \<open>\<And>n'. c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets\<close>
  from \<open>if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> Label  (l + #:c\<^sub>1 + 1)-CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> 
    \<open>labels c\<^sub>2 l c\<close>
  obtain nx where "c\<^sub>2 \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto)
     apply(case_tac n) apply(auto dest:Proc_CFG_sourcelabel_less_num_nodes)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileBody c' l c b)
  note IH = \<open>\<And>n'. c' \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' 
    \<Longrightarrow> \<exists>p es rets. fst_cmd c = Call p es rets\<close>
  from \<open>while (b) c' \<turnstile> Label (l + 2) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>labels c' l c\<close>
  obtain nx where "c' \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx"
    apply - apply(erule Proc_CFG.cases,auto dest:Proc_CFG_Call_Labels)
    by(case_tac n) auto
  from IH[OF this] show ?case by simp
next
  case (Labels_WhileExit b c' n')
  have "while (b) c' \<turnstile> Label 1 -IEdge \<Up>id\<rightarrow>\<^sub>p Exit" by(rule Proc_CFG_WhileFalseSkip)
  with \<open>while (b) c' \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
  have False by(rule Proc_CFG_Call_Intra_edge_not_same_source)
  thus ?case by simp
next
  case (Labels_Call px esx retsx)
  from \<open>Call px esx retsx \<turnstile> Label 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
  show ?case by(fastforce elim:Proc_CFG.cases)
qed


subsection \<open>Definition of \<open>Def\<close> and \<open>Use\<close> sets\<close>

subsubsection \<open>\<open>ParamDefs\<close>\<close>

lemma PCFG_CallEdge_THE_rets:
  "prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'
\<Longrightarrow> (THE rets'. \<exists>p' es' n. prog \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') = rets"
by(fastforce intro:the_equality dest:Proc_CFG_Call_nodes_eq')


definition ParamDefs_proc :: "cmd \<Rightarrow> label \<Rightarrow> vname list"
  where "ParamDefs_proc c n \<equiv> 
  if (\<exists>n' p' es' rets'. c \<turnstile> n' -CEdge(p',es',rets')\<rightarrow>\<^sub>p n) then 
     (THE rets'. \<exists>p' es' n'. c \<turnstile> n' -CEdge(p',es',rets')\<rightarrow>\<^sub>p n)
  else []"


lemma in_procs_THE_in_procs_cmd:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
  by(fastforce intro:the_equality)


definition ParamDefs :: "wf_prog \<Rightarrow> node \<Rightarrow> vname list"
  where "ParamDefs wfp n \<equiv> let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (if (p = Main) then ParamDefs_proc prog l
   else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
         then ParamDefs_proc (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) l
         else []))"


lemma ParamDefs_Main_Return_target:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = rets"
  by(fastforce dest:PCFG_CallEdge_THE_rets simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_Return_target:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'"
  shows "ParamDefs wfp (p,n') = rets"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce
  moreover
  from \<open>well_formed procs\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:PCFG_CallEdge_THE_rets simp:ParamDefs_def ParamDefs_proc_def)
qed

lemma ParamDefs_Main_IEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = []"
by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_target 
            simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_IEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'"
  shows "ParamDefs wfp (p,n') = []"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce  
  moreover
  from \<open>well_formed procs\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_target 
                simp:ParamDefs_def ParamDefs_proc_def)
qed

lemma ParamDefs_Main_CEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n''\<rbrakk>
  \<Longrightarrow> ParamDefs wfp (Main,n') = []"
by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
            simp:ParamDefs_def ParamDefs_proc_def)

lemma ParamDefs_Proc_CEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n''"
  shows "ParamDefs wfp (p,n') = []"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce  
  moreover
  from \<open>well_formed procs\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
                simp:ParamDefs_def ParamDefs_proc_def)
qed


lemma assumes "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
  and "(p, ins, outs) \<in> set (lift_procs wfp)"
  shows ParamDefs_length:"length (ParamDefs wfp (targetnode a)) = length outs"
  (is ?length)
  and Return_update:"f' cf cf' = cf'(ParamDefs wfp (targetnode a) [:=] map cf outs)"
  (is ?update)
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence "wf prog procs" by(rule wf_wf_prog)
  hence wf:"well_formed procs" by fastforce
  from assms have "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    by(simp add:valid_edge_def)
  from this \<open>kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> wf have "?length \<and> ?update"
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (MainReturn l p' es rets l' insx outsx cx)
    from \<open>\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outsx) =
      kind a\<close> \<open>kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> have "p' = p" 
      and f':"f' = (\<lambda>cf cf'. cf'(rets [:=] map cf outsx))" by simp_all
    with \<open>well_formed procs\<close> \<open>(p', insx, outsx, cx) \<in> set procs\<close>
      \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
    have [simp]:"outsx = outs" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
    with \<open>wf prog procs\<close> \<open>(p', insx, outsx, cx) \<in> set procs\<close> 
      \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "length rets = length outs" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "ParamDefs wfp (Main,Label l') = rets"
      by(fastforce intro:ParamDefs_Main_Return_target)
    with \<open>(Main, Label l') = targetnode a\<close> f' \<open>length rets = length outs\<close>
    show ?thesis by simp
  next
    case (ProcReturn px insx outsx cx l p' es rets l' ins' outs' c' ps)
    from \<open>\<lambda>cf. snd cf = (px, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs') =
      kind a\<close> \<open>kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
    have "p' = p" and f':"f' = (\<lambda>cf cf'. cf'(rets [:=] map cf outs'))"
      by simp_all
    with \<open>well_formed procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
    have [simp]:"outs' = outs" by fastforce
    from \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
    with \<open>containsCall procs prog ps px\<close> \<open>(px, insx, outsx, cx) \<in> set procs\<close>
    have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
    with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "length rets = length outs" by fastforce
    from \<open>(px, insx, outsx, cx) \<in> set procs\<close>
      \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "ParamDefs wfp (px,Label l') = rets"
      by(fastforce intro:ParamDefs_Proc_Return_target simp:set_conv_nth)
    with \<open>(px, Label l') = targetnode a\<close> f' \<open>length rets = length outs\<close>
    show ?thesis by simp
  qed auto
  thus "?length" and "?update" by simp_all
qed


subsubsection \<open>\<open>ParamUses\<close>\<close>

fun fv :: "expr \<Rightarrow> vname set"
where
  "fv (Val v)       = {}"
  | "fv (Var V)       = {V}"
  | "fv (e1 \<guillemotleft>bop\<guillemotright> e2) = (fv e1 \<union> fv e2)"


lemma rhs_interpret_eq: 
  "\<lbrakk>state_check cf e v'; \<forall>V \<in> fv e. cf V = cf' V\<rbrakk> 
   \<Longrightarrow> state_check cf' e v'"
proof(induct e arbitrary:v')
  case (Val v)
  from \<open>state_check cf (Val v) v'\<close> have "v' = Some v" 
    by(fastforce elim:interpret.cases)
  thus ?case by simp
next
  case (Var V)
  hence "cf' (V) = v'" by(fastforce elim:interpret.cases)
  thus ?case by simp
next
  case (BinOp b1 bop b2)
  note IH1 = \<open>\<And>v'. \<lbrakk>state_check cf b1 v'; \<forall>V\<in>fv b1. cf V = cf' V\<rbrakk>
    \<Longrightarrow> state_check cf' b1 v'\<close>
  note IH2 = \<open>\<And>v'. \<lbrakk>state_check cf b2 v'; \<forall>V\<in>fv b2. cf V = cf' V\<rbrakk>
    \<Longrightarrow> state_check cf' b2 v'\<close>
  from \<open>\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V\<close> have "\<forall>V \<in> fv b1. cf V = cf' V"
    and "\<forall>V \<in> fv b2. cf V = cf' V" by simp_all
  from \<open>state_check cf (b1 \<guillemotleft>bop\<guillemotright> b2) v'\<close>
  have "((state_check cf b1 None \<and> v' = None) \<or> 
          (state_check cf b2 None \<and> v' = None)) \<or>
    (\<exists>v\<^sub>1 v\<^sub>2. state_check cf b1 (Some v\<^sub>1) \<and> state_check cf b2 (Some v\<^sub>2) \<and>
    binop bop v\<^sub>1 v\<^sub>2 = v')"
    apply(cases "interpret b1 cf",simp)
    apply(cases "interpret b2 cf",simp)
    by(case_tac "binop bop a aa",simp+)
  thus ?case apply - 
  proof(erule disjE)+
    assume "state_check cf b1 None \<and> v' = None"
    hence check:"state_check cf b1 None" and "v' = None" by simp_all
    from IH1[OF check \<open>\<forall>V \<in> fv b1. cf V = cf' V\<close>] have "state_check cf' b1 None" .
    with \<open>v' = None\<close> show ?case by simp
  next
    assume "state_check cf b2 None \<and> v' = None"
    hence check:"state_check cf b2 None" and "v' = None" by simp_all
    from IH2[OF check \<open>\<forall>V \<in> fv b2. cf V = cf' V\<close>] have "state_check cf' b2 None" .
    with \<open>v' = None\<close> show ?case by(cases "interpret b1 cf'") simp+
  next
    assume "\<exists>v\<^sub>1 v\<^sub>2. state_check cf b1 (Some v\<^sub>1) \<and>
      state_check cf b2 (Some v\<^sub>2) \<and> binop bop v\<^sub>1 v\<^sub>2 = v'"
    then obtain v\<^sub>1 v\<^sub>2 where "state_check cf b1 (Some v\<^sub>1)"
      and "state_check cf b2 (Some v\<^sub>2)" and "binop bop v\<^sub>1 v\<^sub>2 = v'" by blast
    from \<open>\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V\<close> have "\<forall>V \<in> fv b1. cf V = cf' V"
      by simp
    from IH1[OF \<open>state_check cf b1 (Some v\<^sub>1)\<close> this]
    have "interpret b1 cf' = Some v\<^sub>1" .
    from \<open>\<forall>V \<in> fv (b1 \<guillemotleft>bop\<guillemotright> b2). cf V = cf' V\<close> have "\<forall>V \<in> fv b2. cf V = cf' V"
      by simp
    from IH2[OF \<open>state_check cf b2 (Some v\<^sub>2)\<close> this] 
    have "interpret b2 cf' = Some v\<^sub>2" .
    with \<open>interpret b1 cf' = Some v\<^sub>1\<close> \<open>binop bop v\<^sub>1 v\<^sub>2 = v'\<close>
    show ?thesis by(cases v') simp+
  qed
qed



lemma PCFG_CallEdge_THE_es:
  "prog \<turnstile> n -CEdge(p,es,rets)\<rightarrow>\<^sub>p n'
\<Longrightarrow> (THE es'. \<exists>p' rets' n'. prog \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') = es"
by(fastforce intro:the_equality dest:Proc_CFG_Call_nodes_eq)


definition ParamUses_proc :: "cmd \<Rightarrow> label \<Rightarrow> vname set list"
  where "ParamUses_proc c n \<equiv>
  if (\<exists>n' p' es' rets'. c \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n') then 
  (map fv (THE es'. \<exists>p' rets' n'. c \<turnstile> n -CEdge(p',es',rets')\<rightarrow>\<^sub>p n'))
  else []"


definition ParamUses :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set list"
  where "ParamUses wfp n \<equiv> let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (if (p = Main) then ParamUses_proc prog l
   else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
         then ParamUses_proc (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) l
         else []))"


lemma ParamUses_Main_Return_target:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n' \<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = map fv es"
  by(fastforce dest:PCFG_CallEdge_THE_es simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_Return_target:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -CEdge(p',es,rets)\<rightarrow>\<^sub>p n'"
  shows "ParamUses wfp (p,n) = map fv es"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce  
  moreover
  from \<open>well_formed procs\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:PCFG_CallEdge_THE_es simp:ParamUses_def ParamUses_proc_def)
qed

lemma ParamUses_Main_IEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'\<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = []"
by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source
            simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_IEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n -IEdge et\<rightarrow>\<^sub>p n'"
  shows "ParamUses wfp (p,n) = []"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce  
  moreover
  from \<open>well_formed procs\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_Intra_edge_not_same_source
                simp:ParamUses_def ParamUses_proc_def)
qed

lemma ParamUses_Main_CEdge_Nil:
  "\<lbrakk>Rep_wf_prog wfp = (prog,procs); prog \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n\<rbrakk>
  \<Longrightarrow> ParamUses wfp (Main,n) = []"
by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
            simp:ParamUses_def ParamUses_proc_def)

lemma ParamUses_Proc_CEdge_Nil:
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "c \<turnstile> n' -CEdge(p',es,rets)\<rightarrow>\<^sub>p n"
  shows "ParamUses wfp (p,n) = []"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have "well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  with \<open>(p,ins,outs,c) \<in> set procs\<close> have "p \<noteq> Main" by fastforce  
  moreover
  from \<open>well_formed procs\<close> 
    \<open>(p,ins,outs,c) \<in> set procs\<close>
  have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
    by(rule in_procs_THE_in_procs_cmd)
  ultimately show ?thesis using assms
    by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
                simp:ParamUses_def ParamUses_proc_def)
qed


subsubsection \<open>\<open>Def\<close>\<close>

fun lhs :: "cmd \<Rightarrow> vname set"
where
  "lhs Skip                = {}"
  | "lhs (V:=e)              = {V}"
  | "lhs (c\<^sub>1;;c\<^sub>2)            = lhs c\<^sub>1"
  | "lhs (if (b) c\<^sub>1 else c\<^sub>2) = {}"
  | "lhs (while (b) c)       = {}"
  | "lhs (Call p es rets)    = {}"

lemma lhs_fst_cmd:"lhs (fst_cmd c) = lhs c" by(induct c) auto

lemma Proc_CFG_Call_source_empty_lhs:
  assumes "prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'"
  shows "lhs (label prog l) = {}"
proof -
  from \<open>prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'\<close> have "l < #:prog"
    by(rule Proc_CFG_sourcelabel_less_num_nodes)
  then obtain c' where "labels prog l c'"
    by(erule less_num_inner_nodes_label)
  hence "label prog l = c'" by(rule labels_label)
  from \<open>labels prog l c'\<close> \<open>prog \<turnstile> Label l -CEdge (p,es,rets)\<rightarrow>\<^sub>p n'\<close>
  have "\<exists>p es rets. fst_cmd c' = Call p es rets" 
    by(rule Proc_CFG_Call_source_fst_cmd_Call)
  with lhs_fst_cmd[of c'] have "lhs c' = {}" by auto
  with \<open>label prog l = c'\<close> show ?thesis by simp
qed


lemma in_procs_THE_in_procs_ins:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs) = ins"
  by(fastforce intro:the_equality)


definition Def :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set"
  where "Def wfp n \<equiv> (let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (case l of Label lx \<Rightarrow> 
    (if p = Main then lhs (label prog lx)
     else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
           then 
  lhs (label (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) lx)
           else {}))
  | Entry \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
            then (set 
      (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs)) else {}
  | Exit \<Rightarrow> {}))
    \<union> set (ParamDefs wfp n)"

lemma Entry_Def_empty:"Def wfp (Main, Entry) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto simp:Def_def ParamDefs_def ParamDefs_proc_def)
qed


lemma Exit_Def_empty:"Def wfp (Main, Exit) = {}"
  proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis 
    by(auto dest:Proc_CFG_Call_Labels simp:Def_def ParamDefs_def ParamDefs_proc_def)
qed



subsubsection \<open>\<open>Use\<close>\<close>

fun rhs :: "cmd \<Rightarrow> vname set"
where
  "rhs Skip                = {}"
  | "rhs (V:=e)              = fv e"
  | "rhs (c\<^sub>1;;c\<^sub>2)            = rhs c\<^sub>1"
  | "rhs (if (b) c\<^sub>1 else c\<^sub>2) = fv b"
  | "rhs (while (b) c)       = fv b"
  | "rhs (Call p es rets)    = {}"

lemma rhs_fst_cmd:"rhs (fst_cmd c) = rhs c" by(induct c) auto

lemma Proc_CFG_Call_target_empty_rhs:
  assumes "prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'"
  shows "rhs (label prog l') = {}"
proof -
  from \<open>prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'\<close> have "l' < #:prog"
    by(rule Proc_CFG_targetlabel_less_num_nodes)
  then obtain c' where "labels prog l' c'"
    by(erule less_num_inner_nodes_label)
  hence "label prog l' = c'" by(rule labels_label)
  from \<open>labels prog l' c'\<close> \<open>prog \<turnstile> n -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label l'\<close>
  have "fst_cmd c' = Skip" by(rule Proc_CFG_Call_target_fst_cmd_Skip)
  with rhs_fst_cmd[of c'] have "rhs c' = {}" by simp
  with \<open>label prog l' = c'\<close> show ?thesis by simp
qed



lemma in_procs_THE_in_procs_outs:
  "\<lbrakk>well_formed procs; (p,ins,outs,c) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE outs'. \<exists>c' ins'. (p,ins',outs',c') \<in> set procs) = outs"
  by(fastforce intro:the_equality)


definition Use :: "wf_prog \<Rightarrow> node \<Rightarrow> vname set"
  where "Use wfp n \<equiv> (let (prog,procs) = Rep_wf_prog wfp; (p,l) = n in
  (case l of Label lx \<Rightarrow> 
    (if p = Main then rhs (label prog lx) 
     else (if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
           then 
  rhs (label (THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) lx)
           else {}))
  | Exit \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
            then (set (THE outs'. \<exists>c' ins'. (p,ins',outs',c') \<in> set procs) )
            else {}
  | Entry \<Rightarrow> if (\<exists>ins outs c. (p,ins,outs,c) \<in> set procs)
      then (set (THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs))
      else {}))
  \<union> Union (set (ParamUses wfp n)) \<union> set (ParamDefs wfp n)"


lemma Entry_Use_empty:"Use wfp (Main, Entry) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto dest:Proc_CFG_Call_Labels 
    simp:Use_def ParamUses_def ParamUses_proc_def ParamDefs_def ParamDefs_proc_def)
qed

lemma Exit_Use_empty:"Use wfp (Main, Exit) = {}"
proof -
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)"
    by(cases "Rep_wf_prog wfp") auto
  hence "well_formed procs" by(fastforce intro:wf_wf_prog)
  thus ?thesis by(auto dest:Proc_CFG_Call_Labels 
    simp:Use_def ParamUses_def ParamUses_proc_def ParamDefs_def ParamDefs_proc_def)
qed


subsection \<open>Lemmas about edges and call frames\<close>

lemmas transfers_simps = ProcCFG.transfer.simps[simplified]
declare transfers_simps [simp]

abbreviation state_val :: "(('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'var \<rightharpoonup> 'val"
  where "state_val s V \<equiv> (fst (hd s)) V"

lemma Proc_CFG_edge_no_lhs_equal:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "V \<notin> lhs (label prog l)"
  shows "state_val (CFG.transfer (lift_procs wfp) et (cf#cfs)) V = fst cf V"
proof -
  from \<open>prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'\<close> 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from \<open>prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'\<close> \<open>IEdge et = x\<close> \<open>V \<notin> lhs (label prog l)\<close>
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case (Proc_CFG_LAss V' e)
    have "labels (V':=e) 0 (V':=e)" by(rule Labels_Base)
    hence "label (V':=e) 0 = (V':=e)" by(rule labels_label)
    have "V' \<in> lhs (V':=e)" by simp
    with \<open>V \<notin> lhs (label (V':=e) 0)\<close>
      \<open>IEdge et = IEdge \<Up>\<lambda>cf. update cf V' e\<close> \<open>label (V':=e) 0 = (V':=e)\<close>
    show ?case by fastforce
  next
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'\<close> have "l < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c';;c\<^sub>2" by(rule labels_label)
    with \<open>V \<notin> lhs (label (c\<^sub>1;; c\<^sub>2) l)\<close> \<open>labels c\<^sub>1 l c'\<close> 
    have "V \<notin> lhs (label c\<^sub>1 l)" by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit\<close> have "l < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c';;c\<^sub>2" by(rule labels_label)
    with \<open>V \<notin> lhs (label (c\<^sub>1;; c\<^sub>2) l)\<close> \<open>labels c\<^sub>1 l c'\<close> 
    have "V \<notin> lhs (label c\<^sub>1 l)" by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1 l)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>2 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>n \<oplus> #:c\<^sub>1 = Label l\<close> obtain l' 
      where "n = Label l'" and "l = l' + #:c\<^sub>1" by(cases n) auto
    from \<open>n = Label l'\<close> \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> have "l' < #:c\<^sub>2"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1\<close> have "labels (c\<^sub>1;;c\<^sub>2) l c'" 
      by(fastforce intro:Labels_Seq2)
    hence "label (c\<^sub>1;;c\<^sub>2) l = c'" by(rule labels_label)
    with \<open>V \<notin> lhs (label (c\<^sub>1;;c\<^sub>2) l)\<close> \<open>labels c\<^sub>2 l' c'\<close> \<open>l = l' + #:c\<^sub>1\<close>
    have "V \<notin> lhs (label c\<^sub>2 l')" by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2 l)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>1 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>n \<oplus> 1 = Label l\<close> obtain l' 
      where "n = Label l'" and "l = l' + 1" by(cases n) auto
    from \<open>n = Label l'\<close> \<open>c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> have "l' < #:c\<^sub>1"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) l = c'" by(rule labels_label)
    with \<open>V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) l)\<close> \<open>labels c\<^sub>1 l' c'\<close> \<open>l = l' + 1\<close>
    have "V \<notin> lhs (label c\<^sub>1 l')" by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1 l)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c\<^sub>2 l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>n \<oplus> #:c\<^sub>1 + 1 = Label l\<close> obtain l' 
      where "n = Label l'" and "l = l' + #:c\<^sub>1 + 1" by(cases n) auto
    from \<open>n = Label l'\<close> \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> have "l' < #:c\<^sub>2"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1 + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) l = c'" by(rule labels_label)
    with \<open>V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) l)\<close> \<open>labels c\<^sub>2 l' c'\<close> \<open>l = l' + #:c\<^sub>1 + 1\<close>
    have "V \<notin> lhs (label c\<^sub>2 l')" by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBody c' n et' n' b l)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c' l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' 
      where "n = Label l'" and "l = l' + 2" by(cases n) auto
    from \<open>n = Label l'\<close> \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> have "l' < #:c'"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    hence "label (while (b) c') l = cx;;while (b) c'" by(rule labels_label)
    with \<open>V \<notin> lhs (label (while (b) c') l)\<close> \<open>labels c' l' cx\<close> \<open>l = l' + 2\<close>
    have "V \<notin> lhs (label c' l')" by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b l)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; V \<notin> lhs (label c' l)\<rbrakk>
      \<Longrightarrow> state_val (CFG.transfer (lift_procs wfp) et (cf # cfs)) V = fst cf V\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' 
      where "n = Label l'" and "l = l' + 2" by(cases n) auto
    from \<open>n = Label l'\<close> \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit\<close> have "l' < #:c'"
      by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    hence "label (while (b) c') l = cx;;while (b) c'" by(rule labels_label)
    with \<open>V \<notin> lhs (label (while (b) c') l)\<close> \<open>labels c' l' cx\<close> \<open>l = l' + 2\<close>
    have "V \<notin> lhs (label c' l')" by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  qed auto
qed



lemma Proc_CFG_edge_uses_only_rhs:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "CFG.pred et s"
  and "CFG.pred et s'" and "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
  shows "\<forall>V\<in>lhs (label prog l). 
    state_val (CFG.transfer (lift_procs wfp) et s) V =
    state_val (CFG.transfer (lift_procs wfp) et s') V"
proof -
  from \<open>prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'\<close> 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from \<open>CFG.pred et s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from \<open>CFG.pred et s'\<close> obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
    by(cases s') auto
  from \<open>prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'\<close> \<open>IEdge et = x\<close>
    \<open>\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V\<close>
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case Proc_CFG_Skip
    have "labels Skip 0 Skip" by(rule Labels_Base)
    hence "label Skip 0 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label Skip 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_LAss V e)
    have "labels (V:=e) 0 (V:=e)" by(rule Labels_Base)
    hence "label (V:=e) 0 = V:=e" by(rule labels_label)
    then have "lhs (label (V:=e) 0) = {V}"
      and "rhs (label (V:=e) 0) = fv e" by auto
    with \<open>IEdge et = IEdge \<Up>\<lambda>cf. update cf V e\<close> 
      \<open>\<forall>V\<in>rhs (label (V:=e) 0). state_val s V = state_val s' V\<close>
    show ?case by(fastforce intro:rhs_interpret_eq)
  next
    case (Proc_CFG_LAssSkip V e)
    have "labels (V:=e) 1 Skip" by(rule Labels_LAss)
    hence "label (V:=e) 1 = Skip" by(rule labels_label)
    hence "\<forall>V'. V' \<notin> lhs (label (V:=e) 1)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'\<close>
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit\<close>
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>2 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>n \<oplus> #:c\<^sub>1 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1"
      by(cases n) auto
    from \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1\<close> have "labels (c\<^sub>1;;c\<^sub>2) l c'" by(fastforce intro:Labels_Seq2)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;;c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c\<^sub>2 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>labels (c\<^sub>1;;c\<^sub>2) l c'\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CondTrue b c\<^sub>1 c\<^sub>2)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_CondFalse b c\<^sub>1 c\<^sub>2)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>1 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>n \<oplus> 1 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 1"
      by(cases n) auto
    from \<open>c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    with \<open>labels c\<^sub>1 l' c'\<close> \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c\<^sub>1 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c\<^sub>1 l' c'\<close> \<open>labels (if (b) c\<^sub>1 else c\<^sub>2) l c'\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c\<^sub>2 l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>n \<oplus> #:c\<^sub>1 + 1= Label l\<close> obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1+1"
      by(cases n) auto
    from \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1 + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c\<^sub>2 l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>labels (if (b) c\<^sub>1 else c\<^sub>2) l c'\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_WhileTrue b c')
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileFalse b c')
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 0)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileFalseSkip b c')
    have "labels (while (b) c') 1 Skip" by(rule Labels_WhileExit)
    hence "label (while (b) c') 1 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (while (b) c') 1)" by simp
    then show ?case by fastforce
  next
    case (Proc_CFG_WhileBody c' n et' n' b)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c' l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with \<open>labels c' l' cx\<close> \<open>\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c' l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c' l' cx\<close> \<open>labels (while (b) c') l (cx;;while (b) c')\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> \<forall>V\<in>lhs (label c' l). state_val (CFG.transfer (lift_procs wfp) et s) V =
        state_val (CFG.transfer (lift_procs wfp) et s') V\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit\<close> \<open>n = Label l'\<close>
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with \<open>labels c' l' cx\<close> \<open>\<forall>V\<in>rhs (label (while (b) c') l).
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close>
    have "\<forall>V\<in>lhs (label c' l'). state_val (CFG.transfer (lift_procs wfp) et s) V =
      state_val (CFG.transfer (lift_procs wfp) et s') V" by (rule IH)
    with \<open>labels c' l' cx\<close> \<open>labels (while (b) c') l (cx;;while (b) c')\<close>
    show ?case by(fastforce dest:labels_label)
  next
    case (Proc_CFG_CallSkip p es rets)
    have "labels (Call p es rets) 1 Skip" by(rule Labels_Call)
    hence "label (Call p es rets) 1 = Skip" by(rule labels_label)
    hence "\<forall>V. V \<notin> lhs (label (Call p es rets) 1)" by simp
    then show ?case by fastforce
  qed auto
qed


lemma Proc_CFG_edge_rhs_pred_eq:
  assumes "prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'" and "CFG.pred et s"
  and "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
  and "length s = length s'"
  shows "CFG.pred et s'"
proof -
  from \<open>prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'\<close> 
  obtain x where "IEdge et = x" and "prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'" by simp_all
  from \<open>CFG.pred et s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from \<open>length s = length s'\<close> obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
    by(cases s') auto
  from \<open>prog \<turnstile> Label l -x\<rightarrow>\<^sub>p n'\<close> \<open>IEdge et = x\<close> 
    \<open>\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V\<close>
  show ?thesis
  proof(induct prog "Label l" x n' arbitrary:l rule:Proc_CFG.induct)
    case (Proc_CFG_SeqFirst c\<^sub>1 et' n' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; \<forall>V\<in>rhs (label c\<^sub>1 l). 
      state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p n'\<close>
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_SeqConnect c\<^sub>1 et' c\<^sub>2)
    note IH = \<open>\<lbrakk>IEdge et = et'; 
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk>
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>c\<^sub>1 \<turnstile> Label l -et'\<rightarrow>\<^sub>p Exit\<close>
    have "l < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l c'" by(erule less_num_inner_nodes_label)
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(rule Labels_Seq1)
    with \<open>labels c\<^sub>1 l c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;; c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_SeqSecond c\<^sub>2 n et' n' c\<^sub>1)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>n \<oplus> #:c\<^sub>1 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1"
      by(cases n) auto
    from \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1\<close> have "labels (c\<^sub>1;;c\<^sub>2) l c'" by(fastforce intro:Labels_Seq2)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>\<forall>V\<in>rhs (label (c\<^sub>1;;c\<^sub>2) l). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_CondTrue b c\<^sub>1 c\<^sub>2)
    from \<open>CFG.pred et s\<close> \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<close>
    have "state_check (fst cf) b (Some true)" by simp
    moreover
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    with \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some true)" 
      by simp(rule rhs_interpret_eq)
    with \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<close>
    show ?case by simp
  next
    case (Proc_CFG_CondFalse b c\<^sub>1 c\<^sub>2)
    from \<open>CFG.pred et s\<close> 
      \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<close>
    have "state_check (fst cf) b (Some false)" by simp
    moreover
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) 0 (if (b) c\<^sub>1 else c\<^sub>2)" by(rule Labels_Base)
    hence "label (if (b) c\<^sub>1 else c\<^sub>2) 0 = if (b) c\<^sub>1 else c\<^sub>2" by(rule labels_label)
    with \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) 0). state_val s V = state_val s' V\<close>
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some false)" 
      by simp(rule rhs_interpret_eq)
    with \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<close> 
    show ?case by simp
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et' n' b c\<^sub>2)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>1 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>n \<oplus> 1 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 1"
      by(cases n) auto
    from \<open>c\<^sub>1 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>1" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>1 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondTrue)
    with \<open>labels c\<^sub>1 l' c'\<close> \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>1 l'). state_val s V = state_val s' V"
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_CondElse c\<^sub>2 n et' n' b c\<^sub>1)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c\<^sub>2 l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>n \<oplus> #:c\<^sub>1 + 1= Label l\<close> obtain l' where "n = Label l'" and "l = l' + #:c\<^sub>1+1"
      by(cases n) auto
    from \<open>c\<^sub>2 \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c\<^sub>2" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain c' where "labels c\<^sub>2 l' c'" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + #:c\<^sub>1 + 1\<close> have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'" 
      by(fastforce intro:Labels_CondFalse)
    with \<open>labels c\<^sub>2 l' c'\<close> \<open>\<forall>V\<in>rhs (label (if (b) c\<^sub>1 else c\<^sub>2) l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c\<^sub>2 l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_WhileTrue b c')
    from \<open>CFG.pred et s\<close> \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<close>
    have "state_check (fst cf) b (Some true)" by simp
    moreover
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    with \<open>\<forall>V\<in>rhs (label (while (b) c') 0). state_val s V = state_val s' V\<close> 
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some true)" 
      by simp(rule rhs_interpret_eq)
    with \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<close>
    show ?case by simp
  next
    case (Proc_CFG_WhileFalse b c')
    from \<open>CFG.pred et s\<close>
      \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<close>
    have "state_check (fst cf) b (Some false)" by simp
    moreover
    have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
    hence "label (while (b) c') 0 = while (b) c'" by(rule labels_label)
    with \<open>\<forall>V\<in>rhs (label (while (b) c') 0). state_val s V = state_val s' V\<close> 
    have "\<forall>V\<in> fv b. state_val s V = state_val s' V" by fastforce
    ultimately have "state_check (fst cf') b (Some false)" 
      by simp(rule rhs_interpret_eq)
    with \<open>IEdge et = IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<close>
    show ?case by simp
  next
    case (Proc_CFG_WhileBody c' n et' n' b)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l'\<close>
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with \<open>labels c' l' cx\<close> \<open>\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  next
    case (Proc_CFG_WhileBodyExit c' n et' b)
    note IH = \<open>\<And>l. \<lbrakk>n = Label l; IEdge et = et';
      \<forall>V\<in>rhs (label c' l). state_val s V = state_val s' V\<rbrakk> 
      \<Longrightarrow> CFG.pred et s'\<close>
    from \<open>n \<oplus> 2 = Label l\<close> obtain l' where "n = Label l'" and "l = l' + 2"
      by(cases n) auto
    from \<open>c' \<turnstile> n -et'\<rightarrow>\<^sub>p Exit\<close> \<open>n = Label l'\<close>
    have "l' < #:c'" by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
    then obtain cx where "labels c' l' cx" by(erule less_num_inner_nodes_label)
    with \<open>l = l' + 2\<close> have "labels (while (b) c') l (cx;;while (b) c')" 
      by(fastforce intro:Labels_WhileBody)
    with \<open>labels c' l' cx\<close> \<open>\<forall>V\<in>rhs (label (while (b) c') l). 
      state_val s V = state_val s' V\<close>
    have "\<forall>V\<in>rhs (label c' l'). state_val s V = state_val s' V" 
      by(fastforce dest:labels_label)
    with \<open>n = Label l'\<close> \<open>IEdge et = et'\<close> show ?case by (rule IH)
  qed auto
qed



subsection \<open>Instantiating the \<open>CFG_wf\<close> locale\<close>

interpretation ProcCFG_wf:
  CFG_wf sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main 
  "Def wfp" "Use wfp" "ParamDefs wfp" "ParamUses wfp"
  for wfp
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence "wf prog procs" by(rule wf_wf_prog)
  hence wf:"well_formed procs" by fastforce
  show "CFG_wf sourcenode targetnode kind (valid_edge wfp)
    (Main, Entry) get_proc (get_return_edges wfp) (lift_procs wfp) Main 
    (Def wfp) (Use wfp) (ParamDefs wfp) (ParamUses wfp)"
  proof
    from Entry_Def_empty Entry_Use_empty
    show "Def wfp (Main, Entry) = {} \<and> Use wfp (Main, Entry) = {}" by simp
  next
    fix a Q r p fs ins outs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
    show "length (ParamUses wfp (sourcenode a)) = length ins"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" by fastforce
      from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>wf prog procs\<close> \<open>(p', insx, outsx, cx) \<in> set procs\<close> 
        \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "length es = length ins" by fastforce
      from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "ParamUses wfp (Main, Label l) = map fv es"
        by(fastforce intro:ParamUses_Main_Return_target)
      with \<open>(Main, Label l) = sourcenode a\<close> \<open>length es = length ins\<close>
      show ?case by simp
    next
      case (ProcCall px insx outsx cx l p' es rets l' ins' outs' c' ps)
      with wf have [simp]:"ins' = ins" by fastforce
      from \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps px\<close> \<open>(px, insx, outsx, cx) \<in> set procs\<close>
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "length es = length ins" by fastforce
      from \<open>(px, insx, outsx, cx) \<in> set procs\<close>
        \<open>cx \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "ParamUses wfp (px,Label l) = map fv es"
        by(fastforce intro:ParamUses_Proc_Return_target simp:set_conv_nth)
      with \<open>(px, Label l) = sourcenode a\<close> \<open>length es = length ins\<close>
      show ?case by simp
    qed auto
  next
    fix a assume "valid_edge wfp a"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    thus "distinct (ParamDefs wfp (targetnode a))"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      from \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>(Main, n') = targetnode a\<close>
      have "ParamDefs wfp (Main,n') = []" by(fastforce intro:ParamDefs_Main_IEdge_Nil)
      with \<open>(Main, n') = targetnode a\<close> show ?case by simp
    next
      case (Proc p ins outs c n n')
      from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close>
      have "ParamDefs wfp (p,n') = []" by(fastforce intro:ParamDefs_Proc_IEdge_Nil)
      with \<open>(p, n') = targetnode a\<close> show ?case by simp
    next
      case (MainCall l p es rets n' ins outs c)
      with \<open>(p, ins, outs, c) \<in> set procs\<close> wf have [simp]:"p \<noteq> Main"
        by fastforce
      from wf \<open>(p, ins, outs, c) \<in> set procs\<close>
      have "(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
        by(rule in_procs_THE_in_procs_cmd)
      with \<open>(p, Entry) = targetnode a\<close>[THEN sym] show ?case 
        by(auto simp:ParamDefs_def ParamDefs_proc_def)
    next
      case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c')
      with \<open>(p', ins', outs', c') \<in> set procs\<close> wf 
      have [simp]:"p' \<noteq> Main" by fastforce
      from wf \<open>(p', ins', outs', c') \<in> set procs\<close>
      have "(THE cx. \<exists>insx outsx. (p',insx,outsx,cx) \<in> set procs) = c'"
        by(rule in_procs_THE_in_procs_cmd)
      with \<open>(p', Entry) = targetnode a\<close>[THEN sym] show ?case 
        by(fastforce simp:ParamDefs_def ParamDefs_proc_def)
    next
      case (MainReturn l p es rets l' ins outs c)
      from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs prog [] p" by(rule Proc_CFG_Call_containsCall)
      with \<open>wf prog procs\<close> \<open>(p, ins, outs, c) \<in> set procs\<close> 
        \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "distinct rets" by fastforce
      from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "ParamDefs wfp (Main,Label l') = rets"
        by(fastforce intro:ParamDefs_Main_Return_target)
      with \<open>distinct rets\<close> \<open>(Main, Label l') = targetnode a\<close> show ?case
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
      from \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps p\<close> \<open>(p, ins, outs, c) \<in> set procs\<close>
      have "containsCall procs prog (ps@[p]) p'" by(rule containsCall_in_proc)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "distinct rets'" by fastforce
      from \<open>(p, ins, outs, c) \<in> set procs\<close>
        \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "ParamDefs wfp (p,Label l') = rets'"
        by(fastforce intro:ParamDefs_Proc_Return_target simp:set_conv_nth)
      with \<open>distinct rets'\<close> \<open>(p, Label l') = targetnode a\<close> show ?case 
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (MainCallReturn n p es rets n')
      from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "containsCall procs prog [] p" by(rule Proc_CFG_Call_containsCall)
      with \<open>wf prog procs\<close> obtain ins outs c where "(p, ins, outs, c) \<in> set procs"
        by(simp add:wf_def) blast
      with \<open>wf prog procs\<close> \<open>containsCall procs prog [] p\<close>
        \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "distinct rets" by fastforce
      from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "ParamDefs wfp (Main,n') = rets"
        by(fastforce intro:ParamDefs_Main_Return_target)
      with \<open>distinct rets\<close> \<open>(Main, n') = targetnode a\<close> show ?case
        by(fastforce simp:distinct_map inj_on_def)
    next
      case (ProcCallReturn p ins outs c n p' es' rets' n' ps)
      from \<open>c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'\<close>
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(p, ins, outs, c) \<in> set procs\<close>
        \<open>containsCall procs prog ps p\<close>
      obtain wfp' where "Rep_wf_prog wfp' = (c,procs)" by(erule wfp_Call)
      hence "wf c procs" by(rule wf_wf_prog)
      with \<open>containsCall procs c [] p'\<close> obtain ins' outs' c'
        where "(p', ins', outs', c') \<in> set procs"
        by(simp add:wf_def) blast
      from \<open>containsCall procs prog ps p\<close> \<open>(p, ins, outs, c) \<in> set procs\<close>
        \<open>containsCall procs c [] p'\<close>
      have "containsCall procs prog (ps@[p]) p'" by(rule containsCall_in_proc)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'\<close>
      have "distinct rets'" by fastforce
      from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>c \<turnstile> n -CEdge (p', es', rets')\<rightarrow>\<^sub>p n'\<close>
      have "ParamDefs wfp (p,n') = rets'"
        by(fastforce intro:ParamDefs_Proc_Return_target)
      with \<open>distinct rets'\<close> \<open>(p, n') = targetnode a\<close> show ?case
        by(fastforce simp:distinct_map inj_on_def)
    qed
  next
    fix a Q' p f' ins outs
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    thus "length (ParamDefs wfp (targetnode a)) = length outs"
      by(rule ParamDefs_length)
  next
    fix n V assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) n"
      and "V \<in> set (ParamDefs wfp n)"
    thus "V \<in> Def wfp n" by(simp add:Def_def)
  next
    fix a Q r p fs ins outs V
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "(p, ins, outs) \<in> set (lift_procs wfp)" and "V \<in> set ins"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close> \<open>V \<in> set ins\<close>
    show "V \<in> Def wfp (targetnode a)"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" by fastforce
      from wf \<open>(p', insx, outsx, cx) \<in> set procs\<close> 
      have "(THE ins'. \<exists>c' outs'. (p',ins',outs',c') \<in> set procs) = 
        insx" by(rule in_procs_THE_in_procs_ins)
      with \<open>(p', Entry) = targetnode a\<close>[THEN sym] \<open>V \<in> set ins\<close>
        \<open>(p', insx, outsx, cx) \<in> set procs\<close> show ?case by(auto simp:Def_def)
    next
      case (ProcCall px insx outsx cx l p' es rets l' ins' outs' c')
      with wf have [simp]:"ins' = ins" by fastforce
      from wf \<open>(p', ins', outs', c') \<in> set procs\<close> 
      have "(THE insx. \<exists>cx outsx. (p',insx,outsx,cx) \<in> set procs) = 
        ins'" by(rule in_procs_THE_in_procs_ins)
      with \<open>(p', Entry) = targetnode a\<close>[THEN sym] \<open>V \<in> set ins\<close>
        \<open>(p', ins', outs', c') \<in> set procs\<close> show ?case by(auto simp:Def_def)
    qed auto
  next
    fix a Q r p fs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show "Def wfp (sourcenode a) = {}"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      from \<open>(Main, Label l) = sourcenode a\<close>[THEN sym]
        \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "ParamDefs wfp (sourcenode a) = []"
        by(fastforce intro:ParamDefs_Main_CEdge_Nil)
      with \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
        \<open>(Main, Label l) = sourcenode a\<close>[THEN sym]
      show ?case by(fastforce dest:Proc_CFG_Call_source_empty_lhs simp:Def_def)
    next
      case (ProcCall px insx outsx cx l p' es' rets' l' ins' outs' c')
      from \<open>(px, insx, outsx, cx) \<in> set procs\<close> wf
      have [simp]:"px \<noteq> Main" by fastforce
      from \<open>cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "lhs (label cx l) = {}" by(rule Proc_CFG_Call_source_empty_lhs)
      from wf \<open>(px, insx, outsx, cx) \<in> set procs\<close>
      have THE:"(THE c'. \<exists>ins' outs'. (px,ins',outs',c') \<in> set procs) = cx" 
        by(rule in_procs_THE_in_procs_cmd)
      with \<open>(px, Label l) = sourcenode a\<close>[THEN sym]
        \<open>cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>  wf
      have "ParamDefs wfp (sourcenode a) = []"
        by(fastforce dest:Proc_CFG_Call_targetnode_no_Call_sourcenode
        [of _ _ _ _ _ "Label l"] simp:ParamDefs_def ParamDefs_proc_def)
      with \<open>(px, Label l) = sourcenode a\<close>[THEN sym] \<open>lhs (label cx l) = {}\<close> THE
      show ?case by(auto simp:Def_def)
    qed auto
  next
    fix n V assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) n"
      and "V \<in> \<Union>(set (ParamUses wfp n))"
    thus "V \<in> Use wfp n" by(fastforce simp:Use_def)
  next
    fix a Q p f ins outs V
    assume "valid_edge wfp a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "(p, ins, outs) \<in> set (lift_procs wfp)" and "V \<in> set outs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close> \<open>V \<in> set outs\<close>
    show "V \<in> Use wfp (sourcenode a)"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' insx outsx cx)
      with wf have [simp]:"outsx = outs" by fastforce
      from wf \<open>(p', insx, outsx, cx) \<in> set procs\<close> 
      have "(THE outs'. \<exists>c' ins'. (p',ins',outs',c') \<in> set procs) = 
        outsx" by(rule in_procs_THE_in_procs_outs)
      with \<open>(p', Exit) = sourcenode a\<close>[THEN sym] \<open>V \<in> set outs\<close>
        \<open>(p', insx, outsx, cx) \<in> set procs\<close> show ?case by(auto simp:Use_def)
    next
      case (ProcReturn px insx outsx cx l p' es' rets' l' ins' outs' c')
      with wf have [simp]:"outs' = outs" by fastforce
      from wf \<open>(p', ins', outs', c') \<in> set procs\<close> 
      have "(THE outsx. \<exists>cx insx. (p',insx,outsx,cx) \<in> set procs) = 
        outs'" by(rule in_procs_THE_in_procs_outs)
      with \<open>(p', Exit) = sourcenode a\<close>[THEN sym] \<open>V \<in> set outs\<close>
        \<open>(p', ins', outs', c') \<in> set procs\<close> show ?case by(auto simp:Use_def)
    qed auto
  next
    fix a V s
    assume "valid_edge wfp a" and "V \<notin> Def wfp (sourcenode a)"
      and "intra_kind (kind a)" and "CFG.pred (kind a) s"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>V \<notin> Def wfp (sourcenode a)\<close> \<open>intra_kind (kind a)\<close> \<open>CFG.pred (kind a) s\<close>
    show "state_val (CFG.transfer (lift_procs wfp) (kind a) s) V = state_val s V"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      from \<open>CFG.pred (kind a) s\<close> obtain cf cfs where "s = cf#cfs" by(cases s) auto
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>V \<notin> Def wfp (sourcenode a)\<close> \<open>(Main, n) = sourcenode a\<close>
        have "V \<notin> lhs (label prog l)" by(fastforce simp:Def_def)
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l\<close>
        have "state_val (CFG.transfer (lift_procs wfp) (kind a) (cf#cfs)) V = fst cf V"
          by(fastforce intro:Proc_CFG_edge_no_lhs_equal)
        with \<open>s = cf#cfs\<close> show ?thesis by simp
      next
        case Entry
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>s = cf#cfs\<close>
        show ?thesis 
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
      next
        case Exit
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      from \<open>CFG.pred (kind a) s\<close> obtain cf cfs where "s = cf#cfs" by(cases s) auto
      from wf \<open>(p, ins, outs, c) \<in> set procs\<close>
      have THE1:"(THE ins'. \<exists>c' outs'. (p,ins',outs',c') \<in> set procs) = ins"
        by(rule in_procs_THE_in_procs_ins)
      from wf \<open>(p, ins, outs, c) \<in> set procs\<close>
      have THE2:"(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c"
        by(rule in_procs_THE_in_procs_cmd)
      from wf \<open>(p, ins, outs, c) \<in> set procs\<close>
      have [simp]:"p \<noteq> Main" by fastforce
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>V \<notin> Def wfp (sourcenode a)\<close> \<open>(p, n) = sourcenode a\<close>
          \<open>(p, ins, outs, c) \<in> set procs\<close> wf THE1 THE2
        have "V \<notin> lhs (label c l)" by(fastforce simp:Def_def split:if_split_asm)
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l\<close>
        have "state_val (CFG.transfer (lift_procs wfp) (kind a) (cf#cfs)) V = fst cf V"
          by(fastforce intro:Proc_CFG_edge_no_lhs_equal)
        with \<open>s = cf#cfs\<close> show ?thesis by simp
      next
        case Entry
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>s = cf#cfs\<close>
        show ?thesis
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
      next
        case Exit
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    next
      case MainCallReturn thus ?case by(cases s,auto simp:intra_kind_def)
    next
      case ProcCallReturn thus ?case by(cases s,auto simp:intra_kind_def)
    qed(auto simp:intra_kind_def)
  next
    fix a s s'
    assume "valid_edge wfp a" 
      and "\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V"
      and "intra_kind (kind a)" and "CFG.pred (kind a) s" and "CFG.pred (kind a) s'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from \<open>CFG.pred (kind a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" 
      by(cases s) auto
    from \<open>CFG.pred (kind a) s'\<close> obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
      by(cases s') auto
    from \<open>prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a\<close> \<open>intra_kind (kind a)\<close>
      \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close>
      \<open>CFG.pred (kind a) s\<close> \<open>CFG.pred (kind a) s'\<close>
    show "\<forall>V\<in>Def wfp (sourcenode a). 
      state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
      state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close>
          \<open>(Main, n) = sourcenode a\<close>[THEN sym]
        have rhs:"\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V"
          and PDef:"\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val s V = state_val s' V"
          by(auto simp:Use_def)
        from rhs \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l\<close> \<open>CFG.pred (kind a) s\<close> 
          \<open>CFG.pred (kind a) s'\<close>
        have lhs:"\<forall>V\<in>lhs (label prog l). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by -(rule Proc_CFG_edge_uses_only_rhs,auto)
        from PDef \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>(Main, n) = sourcenode a\<close>[THEN sym]
        have "\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_Call_follows_id_edge 
            simp:ParamDefs_def ParamDefs_proc_def transfers_simps[of wfp,simplified]
            split:if_split_asm)
        with lhs \<open>(Main, n) = sourcenode a\<close>[THEN sym] Label show ?thesis
          by(fastforce simp:Def_def)
      next
        case Entry
        with \<open>(Main, n) = sourcenode a\<close>[THEN sym]
        show ?thesis by(fastforce simp:Entry_Def_empty)
      next
        case Exit
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close> wf
          \<open>(p, n) = sourcenode a\<close>[THEN sym] \<open>(p, ins, outs, c) \<in> set procs\<close>
        have rhs:"\<forall>V\<in>rhs (label c l). state_val s V = state_val s' V"
          and PDef:"\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val s V = state_val s' V"
          by(auto dest:in_procs_THE_in_procs_cmd simp:Use_def split:if_split_asm)
        from rhs \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>n = Label l\<close> \<open>CFG.pred (kind a) s\<close> 
          \<open>CFG.pred (kind a) s'\<close>
        have lhs:"\<forall>V\<in>lhs (label c l). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by -(rule Proc_CFG_edge_uses_only_rhs,auto)
        from \<open>(p, ins, outs, c) \<in> set procs\<close> wf have [simp]:"p \<noteq> Main" by fastforce
        from wf \<open>(p, ins, outs, c) \<in> set procs\<close>
        have THE:"(THE c'. \<exists>ins' outs'. (p,ins',outs',c') \<in> set procs) = c" 
          by(fastforce intro:in_procs_THE_in_procs_cmd)
        with PDef \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>(p, n) = sourcenode a\<close>[THEN sym]
        have "\<forall>V\<in>set (ParamDefs wfp (sourcenode a)). 
          state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_Call_follows_id_edge 
            simp:ParamDefs_def ParamDefs_proc_def transfers_simps[of wfp,simplified]
            split:if_split_asm)
        with lhs \<open>(p, n) = sourcenode a\<close>[THEN sym] Label THE
        show ?thesis by(auto simp:Def_def)
      next
        case Entry
        with wf \<open>(p, ins, outs, c) \<in> set procs\<close> have "ParamDefs wfp (p,n) = []"
          by(fastforce simp:ParamDefs_def ParamDefs_proc_def)
        moreover
        from Entry \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>(p, ins, outs, c) \<in> set procs\<close>
        have "ParamUses wfp (p,n) = []" by(fastforce intro:ParamUses_Proc_IEdge_Nil)
        ultimately have "\<forall>V\<in>set ins. state_val s V = state_val s' V"
          using wf \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p,n) = sourcenode a\<close>
          \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close>  Entry
          by(fastforce dest:in_procs_THE_in_procs_ins simp:Use_def split:if_split_asm)
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> Entry
        have "\<forall>V\<in>set ins. state_val (CFG.transfer (lift_procs wfp) (kind a) s) V =
          state_val (CFG.transfer (lift_procs wfp) (kind a) s') V"
          by(fastforce dest:Proc_CFG_EntryD simp:transfers_simps[of wfp,simplified])
        with \<open>(p,n) = sourcenode a\<close>[THEN sym] Entry wf  
          \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>ParamDefs wfp (p,n) = []\<close>
        show ?thesis by(auto dest:in_procs_THE_in_procs_ins simp:Def_def)
      next
        case Exit
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    qed(auto simp:intra_kind_def)
  next
    fix a s fix s'::"((char list \<rightharpoonup> val) \<times> node) list"
    assume "valid_edge wfp a" and "CFG.pred (kind a) s"
      and "\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V" 
      and "length s = length s'" and "snd (hd s) = snd (hd s')"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from \<open>CFG.pred (kind a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" 
      by(cases s) auto
    from \<open>length s = length s'\<close> obtain cf' cfs' where [simp]:"s' = cf'#cfs'" 
      by(cases s') auto
    from \<open>prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a\<close> \<open>CFG.pred (kind a) s\<close>
      \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close>
      \<open>length s = length s'\<close> \<open>snd (hd s) = snd (hd s')\<close>
    show "CFG.pred (kind a) s'"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (Main n n')
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close>
          \<open>(Main, n) = sourcenode a\<close>
        have "\<forall>V\<in>rhs (label prog l). state_val s V = state_val s' V" 
          by(fastforce simp:Use_def)
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> Label \<open>CFG.pred (kind a) s\<close>
          \<open>length s = length s'\<close>
        show ?thesis by(fastforce intro:Proc_CFG_edge_rhs_pred_eq)
      next
        case Entry
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>CFG.pred (kind a) s\<close>
        show ?thesis by(fastforce dest:Proc_CFG_EntryD)
      next
        case Exit
        with \<open>prog \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (Proc p ins outs c n n')
      show ?case
      proof(cases n)
        case (Label l)
        with \<open>\<forall>V\<in>Use wfp (sourcenode a). state_val s V = state_val s' V\<close> wf
          \<open>(p, n) = sourcenode a\<close>[THEN sym] \<open>(p, ins, outs, c) \<in> set procs\<close>
        have "\<forall>V\<in>rhs (label c l). state_val s V = state_val s' V"
          by(auto dest:in_procs_THE_in_procs_cmd simp:Use_def split:if_split_asm)
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> Label \<open>CFG.pred (kind a) s\<close>
          \<open>length s = length s'\<close>
        show ?thesis by(fastforce intro:Proc_CFG_edge_rhs_pred_eq)
      next
        case Entry
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> \<open>CFG.pred (kind a) s\<close>
        show ?thesis by(fastforce dest:Proc_CFG_EntryD)
      next
        case Exit
        with \<open>c \<turnstile> n -IEdge (kind a)\<rightarrow>\<^sub>p n'\<close> have False by fastforce
        thus ?thesis by simp
      qed
    next
      case (MainReturn l p es rets l' ins outs c)
      with \<open>\<lambda>cf. snd cf = (Main, Label l')\<hookleftarrow>\<^bsub>p\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs) =
        kind a\<close>[THEN sym]
      show ?case by fastforce
    next
      case (ProcReturn p ins outs c l p' es rets l' ins' outs' c')
      with \<open>\<lambda>cf. snd cf = (p, Label l')\<hookleftarrow>\<^bsub>p'\<^esub>\<lambda>cf cf'. cf'(rets [:=] map cf outs') =
        kind a\<close>[THEN sym]
      show ?case by fastforce
    qed(auto dest:sym)
  next
    fix a Q r p fs ins outs
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
    show "length fs = length ins"
    proof(induct rule:PCFG.induct)
      case (MainCall l p' es rets n' ins' outs' c)
      hence "fs = map interpret es" and "p' = p" by simp_all
      with wf \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
        \<open>(p', ins', outs', c) \<in> set procs\<close>
      have [simp]:"ins' = ins" by fastforce
      from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c) \<in> set procs\<close>
        \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "length es = length ins" by fastforce
      with \<open>fs = map interpret es\<close> show ?case by simp
    next
      case (ProcCall px insx outsx c l p' es' rets' l' ins' outs' c' ps)
      hence "fs = map interpret es'" and "p' = p" by simp_all
      with wf \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close>
        \<open>(p', ins', outs', c') \<in> set procs\<close>
      have [simp]:"ins' = ins" by fastforce
      from \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps px\<close> \<open>(px, insx, outsx, c) \<in> set procs\<close>
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "length es' = length ins" by fastforce
      with \<open>fs = map interpret es'\<close> show ?case by simp
    qed auto
  next
    fix a Q r p fs a' Q' r' p' fs' s s'
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "valid_edge wfp a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'" 
      and "sourcenode a = sourcenode a'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      and "prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'"
      by(simp_all add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close> show "a = a'"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l px es rets n' insx outsx cx)
      from \<open>prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'\<close>
        \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close> 
        \<open>(Main, Label l) = sourcenode a\<close> \<open>sourcenode a = sourcenode a'\<close>
        \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p n'\<close> wf
      have "targetnode a' = (px, Entry)"
        by(fastforce elim!:PCFG.cases dest:Proc_CFG_Call_nodes_eq)
      with \<open>valid_edge wfp a\<close> \<open>valid_edge wfp a'\<close>
        \<open>sourcenode a = sourcenode a'\<close> \<open>(px, Entry) = targetnode a\<close> wf
      have "kind a = kind a'" by(fastforce intro:Proc_CFG_edge_det simp:valid_edge_def)
      with \<open>sourcenode a = sourcenode a'\<close> \<open>(px, Entry) = targetnode a\<close>
        \<open>targetnode a' = (px, Entry)\<close>
      show ?case by(cases a,cases a',auto)
    next
      case (ProcCall px ins outs c l px' es rets l' insx outsx cx)
      with wf have "px \<noteq> Main" by fastforce
      with \<open>prog,procs \<turnstile> sourcenode a' -kind a'\<rightarrow> targetnode a'\<close>
        \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close>
        \<open>(px, Label l) = sourcenode a\<close> \<open>sourcenode a = sourcenode a'\<close>
        \<open>c \<turnstile> Label l -CEdge (px', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
        \<open>(px', insx, outsx, cx) \<in> set procs\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      have "targetnode a' = (px', Entry)"
      proof(induct n\<equiv>"sourcenode a'" et\<equiv>"kind a'" n'\<equiv>"targetnode a'" rule:PCFG.induct)
        case (ProcCall p insa outsa ca la p'a es' rets' l'a ins' outs' c')
        hence [simp]:"px = p" "l = la" by(auto dest:sym)
        from \<open>(p, insa, outsa, ca) \<in> set procs\<close>
          \<open>(px, ins, outs, c) \<in> set procs\<close> wf have [simp]:"ca = c"  by auto
        from \<open>ca \<turnstile> Label la -CEdge (p'a, es', rets')\<rightarrow>\<^sub>p Label l'a\<close>
          \<open>c \<turnstile> Label l -CEdge (px', es, rets)\<rightarrow>\<^sub>p Label l'\<close>
        have "p'a = px'" by(fastforce dest:Proc_CFG_Call_nodes_eq)
        with \<open>(p'a, Entry) = targetnode a'\<close> show ?case by simp
      qed(auto dest:sym)
      with \<open>valid_edge wfp a\<close> \<open>valid_edge wfp a'\<close>
        \<open>sourcenode a = sourcenode a'\<close> \<open>(px', Entry) = targetnode a\<close> wf
      have "kind a = kind a'" by(fastforce intro:Proc_CFG_edge_det simp:valid_edge_def)
      with \<open>sourcenode a = sourcenode a'\<close> \<open>(px', Entry) = targetnode a\<close>
        \<open>targetnode a' = (px', Entry)\<close> show ?case by(cases a,cases a',auto)
    qed auto
  next
    fix a Q r p fs i ins outs fix s s'::"((char list \<rightharpoonup> val) \<times> node) list"
    assume "valid_edge wfp a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "i < length ins"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
      and "\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>i < length ins\<close> 
      \<open>(p, ins, outs) \<in> set (lift_procs wfp)\<close> 
      \<open>\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V\<close>
    show "CFG.params fs (state_val s) ! i = CFG.params fs (state_val s') ! i"
    proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' insx outsx cx)
      with wf have [simp]:"insx = ins" "fs = map interpret es" by auto
      from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "containsCall procs prog [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>wf prog procs\<close> \<open>(p', insx, outsx, cx) \<in> set procs\<close> 
        \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "length es = length ins" by fastforce
      with \<open>i < length ins\<close> have "i < length (map interpret es)" by simp
      from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p n'\<close>
      have "ParamUses wfp (Main,Label l) = map fv es"
        by(fastforce intro:ParamUses_Main_Return_target)
      with \<open>\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V\<close>
        \<open>i < length (map interpret es)\<close> \<open>(Main, Label l) = sourcenode a\<close>
      have " ((map (\<lambda>e cf. interpret e cf) es)!i) (fst (hd s)) = 
        ((map (\<lambda>e cf. interpret e cf) es)!i) (fst (hd s'))"
        by(cases "interpret (es ! i) (fst (hd s))")(auto dest:rhs_interpret_eq)
      with \<open>i < length (map interpret es)\<close> show ?case by(simp add:ProcCFG.params_nth)
    next
      case (ProcCall px insx outsx cx l p' es' rets' l' ins' outs' c' ps)
      with wf have [simp]:"ins' = ins" by fastforce
      from \<open>cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs cx [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps px\<close> \<open>(px, insx, outsx, cx) \<in> set procs\<close>
      have "containsCall procs prog (ps@[px]) p'" by(rule containsCall_in_proc)
      with \<open>wf prog procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "length es' = length ins" by fastforce
      from \<open>\<lambda>s. True:(px, Label l')\<hookrightarrow>\<^bsub>p'\<^esub>map interpret es' = kind a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "fs = map interpret es'" by simp_all
      from \<open>i < length ins\<close> \<open>fs = map interpret es'\<close> 
        \<open>length es' = length ins\<close> have "i < length fs" by simp
      from \<open>(px, insx, outsx, cx) \<in> set procs\<close>
        \<open>cx \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "ParamUses wfp (px,Label l) = map fv es'"
        by(auto intro!:ParamUses_Proc_Return_target simp:set_conv_nth)
      with \<open>\<forall>V\<in>ParamUses wfp (sourcenode a) ! i. state_val s V = state_val s' V\<close>
        \<open>(px, Label l) = sourcenode a\<close> \<open>i < length fs\<close> 
        \<open>fs = map interpret es'\<close>
      have " ((map (\<lambda>e cf. interpret e cf) es')!i) (fst (hd s)) = 
        ((map (\<lambda>e cf. interpret e cf) es')!i) (fst (hd s'))"
        by(cases "interpret (es' ! i) (fst (hd s))")(auto dest:rhs_interpret_eq)
      with \<open>i < length fs\<close> \<open>fs = map interpret es'\<close> 
      show ?case by(simp add:ProcCFG.params_nth)
    qed auto
  next
    fix a Q' p f' ins outs cf cf'
    assume "valid_edge wfp a" and "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
      and "(p, ins, outs) \<in> set (lift_procs wfp)"
    thus "f' cf cf' = cf'(ParamDefs wfp (targetnode a) [:=] map cf outs)"
      by(rule Return_update)
  next
    fix a a'
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
      and "intra_kind (kind a)" and "intra_kind (kind a')"
    with wf show "\<exists>Q Q'. kind a = (Q)\<^sub>\<surd> \<and> kind a' = (Q')\<^sub>\<surd> \<and> 
      (\<forall>cf. (Q cf \<longrightarrow> \<not> Q' cf) \<and> (Q' cf \<longrightarrow> \<not> Q cf))"
      by(auto dest:Proc_CFG_deterministic simp:valid_edge_def)
  qed
qed


subsection \<open>Instantiating the \<open>CFGExit_wf\<close> locale\<close>

interpretation ProcCFGExit_wf:
  CFGExit_wf sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
  "Def wfp" "Use wfp" "ParamDefs wfp" "ParamUses wfp"
  for wfp
proof
  from Exit_Def_empty Exit_Use_empty
  show "Def wfp (Main, Exit) = {} \<and> Use wfp (Main, Exit) = {}" by simp
qed


end
