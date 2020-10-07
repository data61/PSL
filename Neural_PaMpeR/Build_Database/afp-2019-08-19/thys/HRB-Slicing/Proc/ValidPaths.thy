section \<open>Lemmas concerning paths to instantiate locale Postdomination\<close>

theory ValidPaths imports WellFormed "../StaticInter/Postdomination" begin

subsection \<open>Intraprocedural paths from method entry and to method exit\<close>


abbreviation path :: "wf_prog \<Rightarrow> node \<Rightarrow> edge list \<Rightarrow> node \<Rightarrow> bool" ("_ \<turnstile> _ -_\<rightarrow>* _")
  where "wfp \<turnstile> n -as\<rightarrow>* n' \<equiv> CFG.path sourcenode targetnode (valid_edge wfp) n as n'"

definition label_incrs :: "edge list \<Rightarrow> nat \<Rightarrow> edge list" ("_ \<oplus>s _" 60)
  where "as \<oplus>s i \<equiv> map (\<lambda>((p,n),et,(p',n')). ((p,n \<oplus> i),et,(p',n' \<oplus> i))) as"


declare One_nat_def [simp del]



subsubsection \<open>From \<open>prog\<close> to \<open>prog;;c\<^sub>2\<close>\<close>


lemma Proc_CFG_edge_SeqFirst_nodes_Label:
  "prog \<turnstile> Label l -et\<rightarrow>\<^sub>p Label l' \<Longrightarrow> prog;;c\<^sub>2 \<turnstile> Label l -et\<rightarrow>\<^sub>p Label l'"
proof(induct prog "Label l" et "Label l'" rule:Proc_CFG.induct)
  case (Proc_CFG_SeqSecond c\<^sub>2' n et n' c\<^sub>1)
  hence "(c\<^sub>1;; c\<^sub>2');; c\<^sub>2 \<turnstile> n \<oplus> #:c\<^sub>1 -et\<rightarrow>\<^sub>p n' \<oplus> #:c\<^sub>1"
    by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_SeqSecond)
  with \<open>n \<oplus> #:c\<^sub>1 = Label l\<close> \<open>n' \<oplus> #:c\<^sub>1 = Label l'\<close> show ?case by fastforce
next
  case (Proc_CFG_CondThen c\<^sub>1 n et n' b c\<^sub>2')
  hence "if (b) c\<^sub>1 else c\<^sub>2';; c\<^sub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^sub>p n' \<oplus> 1"
    by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondThen)
  with \<open>n \<oplus> 1 = Label l\<close> \<open>n' \<oplus> 1 = Label l'\<close> show ?case by fastforce
next
  case (Proc_CFG_CondElse c\<^sub>1 n et n' b c\<^sub>2')
  hence "if (b) c\<^sub>2' else c\<^sub>1 ;; c\<^sub>2 \<turnstile> n \<oplus> #:c\<^sub>2' + 1 -et\<rightarrow>\<^sub>p n' \<oplus> (#:c\<^sub>2' + 1)"   
    by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondElse)
  with \<open>n \<oplus> #:c\<^sub>2' + 1 = Label l\<close> \<open>n' \<oplus> #:c\<^sub>2' + 1 = Label l'\<close> show ?case by fastforce
next
  case (Proc_CFG_WhileBody c' n et n' b)
  hence "while (b) c';; c\<^sub>2 \<turnstile> n \<oplus> 2 -et\<rightarrow>\<^sub>p n' \<oplus> 2"
    by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_WhileBody)
  with \<open>n \<oplus> 2 = Label l\<close> \<open>n' \<oplus> 2 = Label l'\<close> show ?case by fastforce
next
  case (Proc_CFG_WhileBodyExit c' n et b)
  hence "while (b) c';; c\<^sub>2 \<turnstile> n \<oplus> 2 -et\<rightarrow>\<^sub>p Label 0"
    by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_WhileBodyExit)
  with \<open>n \<oplus> 2 = Label l\<close> \<open>0 = l'\<close> show ?case by fastforce
qed (auto intro:Proc_CFG.intros)


lemma Proc_CFG_edge_SeqFirst_source_Label:
  assumes "prog \<turnstile> Label l -et\<rightarrow>\<^sub>p n'"
  obtains nx where "prog;;c\<^sub>2 \<turnstile> Label l -et\<rightarrow>\<^sub>p nx"
proof(atomize_elim)
  from \<open>prog \<turnstile> Label l -et\<rightarrow>\<^sub>p n'\<close> obtain n where "prog \<turnstile> n -et\<rightarrow>\<^sub>p n'" and "Label l = n"
    by simp
  thus "\<exists>nx. prog;;c\<^sub>2 \<turnstile> Label l -et\<rightarrow>\<^sub>p nx"
  proof(induct prog n et n' rule:Proc_CFG.induct)
    case (Proc_CFG_SeqSecond c\<^sub>2' n et n' c\<^sub>1)
    show ?case
    proof(cases "n' = Exit")
      case True
      with \<open>c\<^sub>2' \<turnstile> n -et\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close> have "c\<^sub>1;; c\<^sub>2' \<turnstile> n \<oplus> #:c\<^sub>1 -et\<rightarrow>\<^sub>p Exit \<oplus> #:c\<^sub>1"
        by(fastforce intro:Proc_CFG.Proc_CFG_SeqSecond)
      moreover from \<open>n \<noteq> Entry\<close> have "n \<oplus> #:c\<^sub>1 \<noteq> Entry" by(cases n) auto
      ultimately
      have "c\<^sub>1;; c\<^sub>2';; c\<^sub>2 \<turnstile> n \<oplus> #:c\<^sub>1 -et\<rightarrow>\<^sub>p Label (#:c\<^sub>1;; c\<^sub>2')"
        by(fastforce intro:Proc_CFG_SeqConnect)
      with \<open>Label l = n \<oplus> #:c\<^sub>1\<close> show ?thesis by fastforce
    next
      case False
      with Proc_CFG_SeqSecond
      have "(c\<^sub>1;; c\<^sub>2');; c\<^sub>2 \<turnstile> n \<oplus> #:c\<^sub>1 -et\<rightarrow>\<^sub>p n' \<oplus> #:c\<^sub>1"
        by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_SeqSecond)
      with \<open>Label l = n \<oplus> #:c\<^sub>1\<close> show ?thesis by fastforce
    qed
  next
    case (Proc_CFG_CondThen c\<^sub>1 n et n' b c\<^sub>2')
    show ?case
    proof(cases "n' = Exit")
      case True
      with \<open>c\<^sub>1 \<turnstile> n -et\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close>
      have "if (b) c\<^sub>1 else c\<^sub>2' \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^sub>p Exit \<oplus> 1"
        by(fastforce intro:Proc_CFG.Proc_CFG_CondThen)
      moreover from \<open>n \<noteq> Entry\<close> have "n \<oplus> 1 \<noteq> Entry" by(cases n) auto
      ultimately
      have "if (b) c\<^sub>1 else c\<^sub>2';; c\<^sub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^sub>p Label (#:if (b) c\<^sub>1 else c\<^sub>2')"
        by(fastforce intro:Proc_CFG_SeqConnect)
      with \<open>Label l = n \<oplus> 1\<close> show ?thesis by fastforce
    next
      case False
      hence "n' \<oplus> 1 \<noteq> Exit" by(cases n') auto
      with Proc_CFG_CondThen
      have  "if (b) c\<^sub>1 else c\<^sub>2';; c\<^sub>2 \<turnstile> Label l -et\<rightarrow>\<^sub>p n' \<oplus> 1"
        by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondThen)
      with \<open>Label l = n \<oplus> 1\<close> show ?thesis by fastforce
    qed
  next
    case (Proc_CFG_CondElse c\<^sub>1 n et n' b c\<^sub>2')
    show ?case
    proof(cases "n' = Exit")
      case True
      with \<open>c\<^sub>1 \<turnstile> n -et\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close>
      have "if (b) c\<^sub>2' else c\<^sub>1 \<turnstile> n \<oplus> (#:c\<^sub>2' + 1) -et\<rightarrow>\<^sub>p Exit \<oplus> (#:c\<^sub>2' + 1)"
        by(fastforce intro:Proc_CFG.Proc_CFG_CondElse)
      moreover from \<open>n \<noteq> Entry\<close> have "n \<oplus> (#:c\<^sub>2' + 1) \<noteq> Entry" by(cases n) auto
      ultimately
      have "if (b) c\<^sub>2' else c\<^sub>1;; c\<^sub>2 \<turnstile> n \<oplus> (#:c\<^sub>2' + 1) -et\<rightarrow>\<^sub>p 
        Label (#:if (b) c\<^sub>2' else c\<^sub>1)"
        by(fastforce intro:Proc_CFG_SeqConnect)
      with \<open>Label l = n \<oplus> (#:c\<^sub>2' + 1)\<close> show ?thesis by fastforce
    next
      case False
      hence "n' \<oplus> (#:c\<^sub>2' + 1) \<noteq> Exit" by(cases n') auto
      with Proc_CFG_CondElse
      have  "if (b) c\<^sub>2' else c\<^sub>1 ;; c\<^sub>2 \<turnstile> Label l -et\<rightarrow>\<^sub>p n' \<oplus> (#:c\<^sub>2' + 1)"
        by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondElse)
      with \<open>Label l = n \<oplus> (#:c\<^sub>2' + 1)\<close> show ?thesis by fastforce
    qed
  qed (auto intro:Proc_CFG.intros)
qed


lemma Proc_CFG_edge_SeqFirst_target_Label:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^sub>p n'; Label l' = n'\<rbrakk> \<Longrightarrow> prog;;c\<^sub>2 \<turnstile> n -et\<rightarrow>\<^sub>p Label l'"
proof(induct prog n et n' rule:Proc_CFG.induct)
  case (Proc_CFG_SeqSecond c\<^sub>2' n et n' c\<^sub>1)
  from \<open>Label l' = n' \<oplus> #:c\<^sub>1\<close> have "n' \<noteq> Exit" by(cases n') auto
  with Proc_CFG_SeqSecond
  show ?case by(fastforce intro:Proc_CFG_SeqFirst intro:Proc_CFG.Proc_CFG_SeqSecond)
next
  case (Proc_CFG_CondThen c\<^sub>1 n et n' b c\<^sub>2')
  from \<open>Label l' = n' \<oplus> 1\<close> have "n' \<noteq> Exit" by(cases n') auto
  with Proc_CFG_CondThen
  show ?case by(fastforce intro:Proc_CFG_SeqFirst Proc_CFG.Proc_CFG_CondThen)
qed (auto intro:Proc_CFG.intros)


lemma PCFG_edge_SeqFirst_source_Label:
  assumes "prog,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',n')"
  obtains nx where "prog;;c\<^sub>2,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',nx)"
proof(atomize_elim)
  from \<open>prog,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',n')\<close>
  show "\<exists>nx. prog;;c\<^sub>2,procs \<turnstile> (p,Label l) -et\<rightarrow> (p',nx)"
  proof(induct "(p,Label l)" et "(p',n')" rule:PCFG.induct)
    case (Main et)
    from \<open>prog \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p n'\<close>
    obtain nx' where "prog;;c\<^sub>2 \<turnstile> Label l -IEdge et\<rightarrow>\<^sub>p nx'"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with \<open>Main = p\<close> \<open>Main = p'\<close> show ?case 
      by(fastforce dest:PCFG.Main)
  next
    case (Proc ins outs c et ps)
    from \<open>containsCall procs prog ps p\<close>
    have "containsCall procs (prog;;c\<^sub>2) ps p" by simp
    with Proc show ?case by(fastforce dest:PCFG.Proc)
  next
    case (MainCall es rets nx ins outs c)
    from \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p nx\<close>
    obtain lx where [simp]:"nx = Label lx" by(fastforce dest:Proc_CFG_Call_Labels)
    with \<open>prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p nx\<close>
    have "prog;;c\<^sub>2 \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^sub>p Label lx"
      by(auto intro:Proc_CFG_edge_SeqFirst_nodes_Label)
    with MainCall show ?case by(fastforce dest:PCFG.MainCall)
  next
    case (ProcCall ins outs c es' rets' l' ins' outs' c' ps)
    from \<open>containsCall procs prog ps p\<close> 
    have "containsCall procs (prog;;c\<^sub>2) ps p" by simp
    with ProcCall show ?case by(fastforce intro:PCFG.ProcCall)
  next
    case (MainCallReturn px es rets)
    from \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>Main = p\<close>
    obtain nx'' where "prog;;c\<^sub>2 \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p nx''"
      by(auto elim:Proc_CFG_edge_SeqFirst_source_Label)
    with MainCallReturn show ?case by(fastforce dest:PCFG.MainCallReturn)
  next
    case (ProcCallReturn ins outs c px' es' rets' ps)
    from \<open>containsCall procs prog ps p\<close>
    have "containsCall procs (prog;;c\<^sub>2) ps p" by simp
    with ProcCallReturn show ?case by(fastforce dest!:PCFG.ProcCallReturn)
  qed
qed


lemma PCFG_edge_SeqFirst_target_Label:
  "prog,procs \<turnstile> (p,n) -et\<rightarrow> (p',Label l') 
  \<Longrightarrow> prog;;c\<^sub>2,procs \<turnstile> (p,n) -et\<rightarrow> (p',Label l')"
proof(induct "(p,n)" et "(p',Label l')" rule:PCFG.induct)
  case Main
  thus ?case by(fastforce dest:Proc_CFG_edge_SeqFirst_target_Label intro:PCFG.Main)
next
  case (Proc ins outs c et ps)
  from \<open>containsCall procs prog ps p\<close> 
  have "containsCall procs (prog;;c\<^sub>2) ps p" by simp
  with Proc show ?case by(fastforce dest:PCFG.Proc)
next
  case MainReturn thus ?case
    by(fastforce dest:Proc_CFG_edge_SeqFirst_target_Label 
               intro!:PCFG.MainReturn[simplified])
next
  case (ProcReturn ins outs c lx es' rets' ins' outs' c' ps)
  from \<open>containsCall procs prog ps p'\<close> 
  have "containsCall procs (prog;;c\<^sub>2) ps p'" by simp
  with ProcReturn show ?case by(fastforce intro:PCFG.ProcReturn)
next
  case MainCallReturn thus ?case
  by(fastforce dest:Proc_CFG_edge_SeqFirst_target_Label intro:PCFG.MainCallReturn)
next
  case (ProcCallReturn ins outs c px' es' rets' ps)
  from \<open>containsCall procs prog ps p\<close> 
  have "containsCall procs (prog;;c\<^sub>2) ps p" by simp
  with ProcCallReturn show ?case by(fastforce dest!:PCFG.ProcCallReturn)
qed


lemma path_SeqFirst:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "Rep_wf_prog wfp' = (prog;;c\<^sub>2,procs)"
  shows "\<lbrakk>wfp \<turnstile> (p,n) -as\<rightarrow>* (p,Label l); \<forall>a \<in> set as. intra_kind (kind a)\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (p,n) -as\<rightarrow>* (p,Label l)"
proof(induct "(p,n)" as "(p,Label l)" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (p, Label l)\<close> 
    \<open>Rep_wf_prog wfp = (prog, procs)\<close> \<open>Rep_wf_prog wfp' = (prog;; c\<^sub>2, procs)\<close>
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (p, Label l)"
    apply(auto simp:ProcCFG.valid_node_def valid_edge_def)
    apply(erule PCFG_edge_SeqFirst_source_Label,fastforce)
    by(drule PCFG_edge_SeqFirst_target_Label,fastforce)
  thus ?case by(fastforce intro:ProcCFG.empty_path)
next
  case (Cons_path n'' as a nx)
  note IH = \<open>\<And>n. \<lbrakk>n'' = (p, n); \<forall>a\<in>set as. intra_kind (kind a)\<rbrakk>
    \<Longrightarrow> wfp' \<turnstile> (p, n) -as\<rightarrow>* (p, Label l)\<close>
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>Rep_wf_prog wfp' = (prog;;c\<^sub>2,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (p, nx)\<close> \<open>targetnode a = n''\<close>
    \<open>intra_kind (kind a)\<close> wf 
  obtain nx' where "n'' = (p,nx')"
    by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF this \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close>]
  have path:"wfp' \<turnstile> (p, nx') -as\<rightarrow>* (p, Label l)" .
  have "valid_edge wfp' a"
  proof(cases nx')
    case (Label lx)
    with \<open>valid_edge wfp a\<close> \<open>sourcenode a = (p, nx)\<close> \<open>targetnode a = n''\<close>
      \<open>n'' = (p,nx')\<close> show ?thesis
      by(fastforce intro:PCFG_edge_SeqFirst_target_Label 
                   simp:intra_kind_def valid_edge_def)
  next
    case Entry
    with \<open>valid_edge wfp a\<close> \<open>targetnode a = n''\<close> \<open>n'' = (p,nx')\<close>
      \<open>intra_kind (kind a)\<close> have False 
      by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
    thus ?thesis by simp
  next
    case Exit
    with path \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> have False 
      by(induct "(p,nx')" as "(p,Label l)" rule:ProcCFG.path.induct)
    (auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
    thus ?thesis by simp
  qed
  with \<open>sourcenode a = (p, nx)\<close> \<open>targetnode a = n''\<close> \<open>n'' = (p,nx')\<close> path
  show ?case by(fastforce intro:ProcCFG.Cons_path)
qed


subsubsection \<open>From \<open>prog\<close> to \<open>c\<^sub>1;;prog\<close>\<close>

lemma Proc_CFG_edge_SeqSecond_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^sub>p n'; n \<noteq> Entry\<rbrakk> \<Longrightarrow> c\<^sub>1;;prog \<turnstile> n \<oplus> #:c\<^sub>1 -et\<rightarrow>\<^sub>p n' \<oplus> #:c\<^sub>1"
by(induct rule:Proc_CFG.induct)(fastforce intro:Proc_CFG_SeqSecond Proc_CFG.intros)+


lemma PCFG_Main_edge_SeqSecond_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> c\<^sub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^sub>1) -et\<rightarrow> (p',n' \<oplus> #:c\<^sub>1)"
proof(induct "(Main,n)" et "(p',n')" rule:PCFG.induct)
  case Main
  thus ?case
    by(fastforce dest:Proc_CFG_edge_SeqSecond_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn p es rets)
  from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close>
  have "c\<^sub>1;;prog \<turnstile> n \<oplus> #:c\<^sub>1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> #:c\<^sub>1"
    by(rule Proc_CFG_edge_SeqSecond_source_not_Entry)
  with MainCallReturn show ?case by(fastforce intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_SeqSecond:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (c\<^sub>1;;prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> #:c\<^sub>1)"
proof -
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>Rep_wf_prog wfp' = (c\<^sub>1;;prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)\<close>
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastforce simp:ProcCFG.valid_node_def valid_edge_def)
  from this \<open>n \<noteq> Entry\<close> wf show ?thesis
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (Main nx nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
      have "c\<^sub>1;;prog \<turnstile> n \<oplus> #:c\<^sub>1 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> #:c\<^sub>1"
        by(fastforce intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      hence "c\<^sub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^sub>1) -kind a\<rightarrow> (Main,nx' \<oplus> #:c\<^sub>1)"
        by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
        case True
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> 
        have "nx' = Exit \<or> nx' = Label 0" by(fastforce dest:Proc_CFG_EntryD)
        thus ?thesis
        proof
          assume "nx' = Exit"
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis by simp
        next
          assume "nx' = Label 0"
          obtain l etx where "c\<^sub>1 \<turnstile> Label l -IEdge etx\<rightarrow>\<^sub>p Exit" and "l \<le> #:c\<^sub>1"
            by(erule Proc_CFG_Exit_edge)
          hence "c\<^sub>1;;prog \<turnstile> Label l -IEdge etx\<rightarrow>\<^sub>p Label #:c\<^sub>1"
            by(fastforce intro:Proc_CFG_SeqConnect)
          with \<open>nx' = Label 0\<close> 
          have "c\<^sub>1;;prog,procs \<turnstile> (Main,Label l) -etx\<rightarrow> (Main,nx'\<oplus>#:c\<^sub>1)"
            by(fastforce intro:PCFG.Main)
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis
            by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
        qed
      next
        case False
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "c\<^sub>1;;prog \<turnstile> nx \<oplus> #:c\<^sub>1 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> #:c\<^sub>1"
          by(fastforce intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
        hence "c\<^sub>1;;prog,procs \<turnstile> (Main,nx \<oplus> #:c\<^sub>1) -kind a\<rightarrow> (Main,nx' \<oplus> #:c\<^sub>1)"
          by(rule PCFG.Main)
        with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
        show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close> 
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close> have False by fastforce
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> wf \<open>(p, Entry) = targetnode a\<close>[THEN sym]
      \<open>(Main, Label l) = sourcenode a\<close>[THEN sym]
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
     have [simp]:"n = Label l" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
    have "c\<^sub>1;;prog \<turnstile> Label l \<oplus> #:c\<^sub>1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> #:c\<^sub>1"
      by -(rule Proc_CFG_edge_SeqSecond_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "c\<^sub>1;;prog,procs \<turnstile> (Main,Label (l + #:c\<^sub>1)) 
      -(\<lambda>s. True):(Main,n' \<oplus> #:c\<^sub>1)\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
      by(fastforce intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c')
    from \<open>(p, Label l) = sourcenode a\<close>[THEN sym]
      \<open>(p', Entry) = targetnode a\<close>[THEN sym]  \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> wf \<open>(p, Exit) = sourcenode a\<close>[THEN sym]
      \<open>(Main, Label l') = targetnode a\<close>[THEN sym]
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l'" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "c\<^sub>1;;prog \<turnstile> Label l \<oplus> #:c\<^sub>1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l' \<oplus> #:c\<^sub>1"
      by -(rule Proc_CFG_edge_SeqSecond_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "c\<^sub>1;;prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label l' \<oplus> #:c\<^sub>1))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + #:c\<^sub>1))"
      by(fastforce intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p', Exit) = sourcenode a\<close>[THEN sym] 
      \<open>(p, Label l') = targetnode a\<close>[THEN sym] \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "c\<^sub>1;;prog \<turnstile> n \<oplus> #:c\<^sub>1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx' \<oplus> #:c\<^sub>1"
        by(fastforce intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      hence "c\<^sub>1;;prog,procs \<turnstile> (Main,n \<oplus> #:c\<^sub>1) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> #:c\<^sub>1)"
        by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "nx \<noteq> Entry" by(fastforce dest:Proc_CFG_Call_Labels)
      with \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "c\<^sub>1;;prog \<turnstile> nx \<oplus> #:c\<^sub>1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx' \<oplus> #:c\<^sub>1"
        by(fastforce intro:Proc_CFG_edge_SeqSecond_source_not_Entry)
      hence "c\<^sub>1;;prog,procs \<turnstile> (Main,nx \<oplus> #:c\<^sub>1) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> #:c\<^sub>1)"
        by -(rule PCFG.MainCallReturn)
      with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym] 
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  qed
qed


lemma path_Main_SeqSecond:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "Rep_wf_prog wfp' = (c\<^sub>1;;prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> #:c\<^sub>1) -as \<oplus>s #:c\<^sub>1\<rightarrow>* (p',n' \<oplus> #:c\<^sub>1)"
proof(induct "(Main,n)" as "(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main, n')\<close>
    \<open>n' \<noteq> Entry\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (c\<^sub>1;;prog,procs)\<close>
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n' \<oplus> #:c\<^sub>1)"
    by(fastforce intro:valid_node_Main_SeqSecond)
  with \<open>Main = p'\<close> show ?case
    by(fastforce intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as a n)
  note IH = \<open>\<And>n.  \<lbrakk>n'' = (Main, n); \<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk> 
    \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> #:c\<^sub>1) -as \<oplus>s #:c\<^sub>1\<rightarrow>* (p', n' \<oplus> #:c\<^sub>1)\<close>
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>Rep_wf_prog wfp' = (c\<^sub>1;;prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>intra_kind (kind a)\<close> wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF \<open>n'' = (Main,nx'')\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> \<open>nx'' \<noteq> Entry\<close>]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> #:c\<^sub>1) -as \<oplus>s #:c\<^sub>1\<rightarrow>* (p', n' \<oplus> #:c\<^sub>1)" .
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>n'' = (Main,nx'')\<close> \<open>n \<noteq> Entry\<close> \<open>intra_kind (kind a)\<close> wf
  have "c\<^sub>1;; prog,procs \<turnstile> (Main, n \<oplus> #:c\<^sub>1) -kind a\<rightarrow> (Main, nx'' \<oplus> #:c\<^sub>1)"
    by(fastforce intro:PCFG_Main_edge_SeqSecond_source_not_Entry simp:valid_edge_def)
  with path \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close> \<open>n'' = (Main,nx'')\<close>
  show ?case apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection \<open>From \<open>prog\<close> to \<open>if (b) prog else c\<^sub>2\<close>\<close>

lemma Proc_CFG_edge_CondTrue_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^sub>p n'; n \<noteq> Entry\<rbrakk> \<Longrightarrow> if (b) prog else c\<^sub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow>\<^sub>p n' \<oplus> 1"
by(induct rule:Proc_CFG.induct)(fastforce intro:Proc_CFG_CondThen Proc_CFG.intros)+


lemma PCFG_Main_edge_CondTrue_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> if (b) prog else c\<^sub>2,procs \<turnstile> (Main,n \<oplus> 1) -et\<rightarrow> (p',n' \<oplus> 1)"
proof(induct "(Main,n)" et "(p',n')" rule:PCFG.induct)
  case Main
  thus ?case by(fastforce dest:Proc_CFG_edge_CondTrue_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn p es rets)
  from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close>
  have "if (b) prog else c\<^sub>2 \<turnstile> n \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> 1"
    by(rule Proc_CFG_edge_CondTrue_source_not_Entry)
  with MainCallReturn show ?case by(fastforce intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_CondTrue:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) prog else c\<^sub>2,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 1)"
proof -
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) prog else c\<^sub>2,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)\<close>
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastforce simp:ProcCFG.valid_node_def valid_edge_def)
  from this \<open>n \<noteq> Entry\<close> wf show ?thesis
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (Main nx nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) prog else c\<^sub>2 \<turnstile> n \<oplus> 1 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> 1"
        by(fastforce intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      hence "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,n \<oplus> 1) -kind a\<rightarrow> (Main,nx' \<oplus> 1)"
        by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
        case True
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "nx' = Exit \<or> nx' = Label 0" by(fastforce dest:Proc_CFG_EntryD)
        thus ?thesis
        proof
          assume "nx' = Exit"
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis by simp
        next
          assume "nx' = Label 0"
          have "if (b) prog else c\<^sub>2 \<turnstile> Label 0 
            -IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<rightarrow>\<^sub>p Label 1"
            by(rule Proc_CFG_CondTrue)
          with \<open>nx' = Label 0\<close> 
          have "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,Label 0) 
            -(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> 1)" 
            by(fastforce intro:PCFG.Main)
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis
            by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
        qed
      next
        case False
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "if (b) prog else c\<^sub>2 \<turnstile> nx \<oplus> 1 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> 1"
          by(fastforce intro:Proc_CFG_edge_CondTrue_source_not_Entry)
        hence "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,nx \<oplus> 1) -kind a\<rightarrow> 
          (Main,nx' \<oplus> 1)" by(rule PCFG.Main)
        with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
        show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Entry) = targetnode a\<close>[THEN sym] 
      \<open>(Main, Label l) = sourcenode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
    have "if (b) prog else c\<^sub>2 \<turnstile> Label l \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> 1"
      by -(rule Proc_CFG_edge_CondTrue_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,Label (l + 1)) 
      -(\<lambda>s. True):(Main,n' \<oplus> 1)\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
      by(fastforce intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p, Label l) = sourcenode a\<close>[THEN sym] 
      \<open>(p', Entry) = targetnode a\<close>[THEN sym] \<open>well_formed procs\<close> 
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Exit) = sourcenode a\<close>[THEN sym] 
      \<open>(Main, Label l') = targetnode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l'" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "if (b) prog else c\<^sub>2 \<turnstile> Label l \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l' \<oplus> 1"
      by -(rule Proc_CFG_edge_CondTrue_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "if (b) prog else c\<^sub>2,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label l' \<oplus> 1))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + 1))"
      by(fastforce intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p', Exit) = sourcenode a\<close>[THEN sym] 
      \<open>(p, Label l') = targetnode a\<close>[THEN sym] \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) prog else c\<^sub>2 \<turnstile> n \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx' \<oplus> 1"
        by(fastforce intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      hence "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,n \<oplus> 1) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> 
        (Main,nx' \<oplus> 1)" by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "nx \<noteq> Entry" by(fastforce dest:Proc_CFG_Call_Labels)
      with \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) prog else c\<^sub>2 \<turnstile> nx \<oplus> 1 -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx' \<oplus> 1"
        by(fastforce intro:Proc_CFG_edge_CondTrue_source_not_Entry)
      hence "if (b) prog else c\<^sub>2,procs \<turnstile> (Main,nx \<oplus> 1) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> 1)"
        by -(rule PCFG.MainCallReturn)
      with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  qed
qed


lemma path_Main_CondTrue:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) prog else c\<^sub>2,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p',n' \<oplus> 1)"
proof(induct "(Main,n)" as "(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main, n')\<close>
    \<open>n' \<noteq> Entry\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) prog else c\<^sub>2,procs)\<close>
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n' \<oplus> 1)" 
    by(fastforce intro:valid_node_Main_CondTrue)
  with \<open>Main = p'\<close> show ?case
    by(fastforce intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as a n)
  note IH = \<open>\<And>n.  \<lbrakk>n'' = (Main, n); \<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk> 
    \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p', n' \<oplus> 1)\<close>
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) prog else c\<^sub>2,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>intra_kind (kind a)\<close> wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF \<open>n'' = (Main,nx'')\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> \<open>nx'' \<noteq> Entry\<close>]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (p', n' \<oplus> 1)" .
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>n'' = (Main,nx'')\<close> \<open>n \<noteq> Entry\<close> \<open>intra_kind (kind a)\<close> wf
  have "if (b) prog else c\<^sub>2,procs \<turnstile> (Main, n \<oplus> 1) -kind a\<rightarrow> (Main, nx'' \<oplus> 1)"
    by(fastforce intro:PCFG_Main_edge_CondTrue_source_not_Entry simp:valid_edge_def)
  with path \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close> \<open>n'' = (Main,nx'')\<close>
  show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection \<open>From \<open>prog\<close> to \<open>if (b) c\<^sub>1 else prog\<close>\<close>

lemma Proc_CFG_edge_CondFalse_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^sub>p n'; n \<noteq> Entry\<rbrakk> 
  \<Longrightarrow> if (b) c\<^sub>1 else prog \<turnstile> n \<oplus> (#:c\<^sub>1 + 1) -et\<rightarrow>\<^sub>p n' \<oplus> (#:c\<^sub>1 + 1)"
by(induct rule:Proc_CFG.induct)(fastforce intro:Proc_CFG_CondElse Proc_CFG.intros)+


lemma PCFG_Main_edge_CondFalse_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; intra_kind et; well_formed procs\<rbrakk>
  \<Longrightarrow> if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^sub>1 + 1)) -et\<rightarrow> (p',n' \<oplus> (#:c\<^sub>1 + 1))"
proof(induct "(Main,n)" et "(p',n')" rule:PCFG.induct)
  case Main
  thus ?case 
    by(fastforce dest:Proc_CFG_edge_CondFalse_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn p es rets)
  from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close>
  have "if (b) c\<^sub>1 else prog \<turnstile> n \<oplus> (#:c\<^sub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> (#:c\<^sub>1 + 1)"
    by(rule Proc_CFG_edge_CondFalse_source_not_Entry)
  with MainCallReturn show ?case by(fastforce intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_CondFalse:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) c\<^sub>1 else prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') 
  (Main, n \<oplus> (#:c\<^sub>1 + 1))"
proof -
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) c\<^sub>1 else prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)\<close>
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastforce simp:ProcCFG.valid_node_def valid_edge_def)
  from this \<open>n \<noteq> Entry\<close> wf show ?thesis
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (Main nx nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) c\<^sub>1 else prog \<turnstile> n \<oplus> (#:c\<^sub>1 + 1) -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> (#:c\<^sub>1 + 1)"
        by(fastforce intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      hence "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^sub>1 + 1)) -kind a\<rightarrow> 
        (Main,nx' \<oplus> (#:c\<^sub>1 + 1))" by(rule PCFG.Main)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
        case True
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> 
        have "nx' = Exit \<or> nx' = Label 0" by(fastforce dest:Proc_CFG_EntryD)
        thus ?thesis
        proof
          assume "nx' = Exit"
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis by simp
        next
          assume "nx' = Label 0"
          have "if (b) c\<^sub>1 else prog \<turnstile> Label 0 
            -IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<rightarrow>\<^sub>p Label (#:c\<^sub>1 + 1)"
            by(rule Proc_CFG_CondFalse)
          with \<open>nx' = Label 0\<close> 
          have "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,Label 0) 
            -(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^sub>1 + 1))" 
            by(fastforce intro:PCFG.Main)
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis
            by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
        qed
      next
        case False
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "if (b) c\<^sub>1 else prog \<turnstile> nx \<oplus> (#:c\<^sub>1 + 1) -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> (#:c\<^sub>1 + 1)"
          by(fastforce intro:Proc_CFG_edge_CondFalse_source_not_Entry)
        hence "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,nx \<oplus> (#:c\<^sub>1 + 1)) -kind a\<rightarrow> 
          (Main,nx' \<oplus> (#:c\<^sub>1 + 1))" by(rule PCFG.Main)
        with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym] 
        show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
      qed
    qed
  next
    case (Proc p ins outs c nx n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Entry) = targetnode a\<close>[THEN sym]
      \<open>(Main, Label l) = sourcenode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
    have "if (b) c\<^sub>1 else prog \<turnstile> Label l \<oplus> (#:c\<^sub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
      n' \<oplus> (#:c\<^sub>1 + 1)" by -(rule Proc_CFG_edge_CondFalse_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,Label (l + (#:c\<^sub>1 + 1))) 
      -(\<lambda>s. True):(Main,n' \<oplus> (#:c\<^sub>1 + 1))\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
      by(fastforce intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p, Label l) = sourcenode a\<close>[THEN sym]
      \<open>(p', Entry) = targetnode a\<close>[THEN sym]  \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Exit) = sourcenode a\<close>[THEN sym]
      \<open>(Main, Label l') = targetnode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l'" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "if (b) c\<^sub>1 else prog \<turnstile> Label l \<oplus> (#:c\<^sub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
      Label l' \<oplus> (#:c\<^sub>1 + 1)" by -(rule Proc_CFG_edge_CondFalse_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "if (b) c\<^sub>1 else prog,procs \<turnstile> (p,Exit) 
      -(\<lambda>cf. snd cf = (Main,Label l' \<oplus> (#:c\<^sub>1 + 1)))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label (l' + (#:c\<^sub>1 + 1)))"
      by(fastforce intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p', Exit) = sourcenode a\<close>[THEN sym] 
      \<open>(p, Label l') = targetnode a\<close>[THEN sym] \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) c\<^sub>1 else prog \<turnstile> n \<oplus> (#:c\<^sub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
        nx' \<oplus> (#:c\<^sub>1 + 1)" by(fastforce intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      hence "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,n \<oplus> (#:c\<^sub>1 + 1)) 
        -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^sub>1 + 1))" by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "nx \<noteq> Entry" by(fastforce dest:Proc_CFG_Call_Labels)
      with \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "if (b) c\<^sub>1 else prog \<turnstile> nx \<oplus> (#:c\<^sub>1 + 1) -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
        nx' \<oplus> (#:c\<^sub>1 + 1)" by(fastforce intro:Proc_CFG_edge_CondFalse_source_not_Entry)
      hence "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main,nx \<oplus> (#:c\<^sub>1 + 1)) 
        -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> (#:c\<^sub>1 + 1))" by -(rule PCFG.MainCallReturn)
      with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  qed
qed


lemma path_Main_CondFalse:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (if (b) c\<^sub>1 else prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
  \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> (#:c\<^sub>1 + 1)) -as \<oplus>s (#:c\<^sub>1 + 1)\<rightarrow>* (p',n' \<oplus> (#:c\<^sub>1 + 1))"
proof(induct "(Main,n)" as "(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main, n')\<close>
    \<open>n' \<noteq> Entry\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) c\<^sub>1 else prog,procs)\<close>
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n' \<oplus> (#:c\<^sub>1 + 1))"
    by(fastforce intro:valid_node_Main_CondFalse)
  with \<open>Main = p'\<close> show ?case
    by(fastforce intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as a n)
  note IH = \<open>\<And>n. \<And>n.  \<lbrakk>n'' = (Main, n); \<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry\<rbrakk>
    \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> (#:c\<^sub>1 + 1)) -as \<oplus>s (#:c\<^sub>1 + 1)\<rightarrow>* (p', n' \<oplus> (#:c\<^sub>1 + 1))\<close>
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (if (b) c\<^sub>1 else prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>intra_kind (kind a)\<close> wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF \<open>n'' = (Main,nx'')\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> \<open>nx'' \<noteq> Entry\<close>]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> (#:c\<^sub>1 + 1)) -as \<oplus>s (#:c\<^sub>1 + 1)\<rightarrow>* 
    (p', n' \<oplus> (#:c\<^sub>1 + 1))" .
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>n'' = (Main,nx'')\<close> \<open>n \<noteq> Entry\<close> \<open>intra_kind (kind a)\<close> wf
  have "if (b) c\<^sub>1 else prog,procs \<turnstile> (Main, n \<oplus> (#:c\<^sub>1 + 1)) -kind a\<rightarrow> 
    (Main, nx'' \<oplus> (#:c\<^sub>1 + 1))"
    by(fastforce intro:PCFG_Main_edge_CondFalse_source_not_Entry simp:valid_edge_def)
  with path \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close> \<open>n'' = (Main,nx'')\<close>
  show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection \<open>From \<open>prog\<close> to \<open>while (b) prog\<close>\<close>

lemma Proc_CFG_edge_WhileBody_source_not_Entry:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow>\<^sub>p n'; n \<noteq> Entry; n' \<noteq> Exit\<rbrakk> 
  \<Longrightarrow> while (b) prog \<turnstile> n \<oplus> 2 -et\<rightarrow>\<^sub>p n' \<oplus> 2"
by(induct rule:Proc_CFG.induct)(fastforce intro:Proc_CFG_WhileBody Proc_CFG.intros)+


lemma PCFG_Main_edge_WhileBody_source_not_Entry:
  "\<lbrakk>prog,procs \<turnstile> (Main,n) -et\<rightarrow> (p',n'); n \<noteq> Entry; n' \<noteq> Exit; intra_kind et; 
  well_formed procs\<rbrakk> \<Longrightarrow> while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -et\<rightarrow> (p',n' \<oplus> 2)"
proof(induct "(Main,n)" et "(p',n')" rule:PCFG.induct)
  case Main
  thus ?case 
    by(fastforce dest:Proc_CFG_edge_WhileBody_source_not_Entry intro:PCFG.Main)
next
  case (MainCallReturn p es rets)
  from \<open>prog \<turnstile> n -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> \<open>n \<noteq> Entry\<close> \<open>n' \<noteq> Exit\<close>
  have "while (b) prog \<turnstile> n \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^sub>p n' \<oplus> 2"
    by(rule Proc_CFG_edge_WhileBody_source_not_Entry)
  with MainCallReturn show ?case by(fastforce intro:PCFG.MainCallReturn)
qed (auto simp:intra_kind_def)


lemma valid_node_Main_WhileBody:
  assumes "CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)"
  and "n \<noteq> Entry" and "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (while (b) prog,procs)"
  shows "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n \<oplus> 2)"
proof -
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    \<open>Rep_wf_prog wfp' = (while (b) prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main,n)\<close>
  obtain a where "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
    and "(Main,n) = sourcenode a \<or> (Main,n) = targetnode a"
    by(fastforce simp:ProcCFG.valid_node_def valid_edge_def)
  from this \<open>n \<noteq> Entry\<close> wf show ?thesis
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (Main nx nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      show ?thesis
      proof(cases "nx' = Exit")
        case True
        with \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "while (b) prog \<turnstile> n \<oplus> 2 -IEdge (kind a)\<rightarrow>\<^sub>p Label 0"
          by(fastforce intro:Proc_CFG_WhileBodyExit)
        hence "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -kind a\<rightarrow> (Main,Label 0)"
          by(rule PCFG.Main)
        thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
      next
        case False
        with \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close>
        have "while (b) prog \<turnstile> n \<oplus> 2 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> 2"
          by(fastforce intro:Proc_CFG_edge_WhileBody_source_not_Entry)
        hence "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -kind a\<rightarrow> (Main,nx' \<oplus> 2)"
          by(rule PCFG.Main)
        thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
      qed
    next
      assume "(Main, n) = targetnode a"
      show ?thesis
      proof(cases "nx = Entry")
        case True
        with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> 
        have "nx' = Exit \<or> nx' = Label 0" by(fastforce dest:Proc_CFG_EntryD)
        thus ?thesis
        proof
          assume "nx' = Exit"
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis by simp
        next
          assume "nx' = Label 0"
          have "while (b) prog \<turnstile> Label 0 
            -IEdge (\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<rightarrow>\<^sub>p Label 2"
            by(rule Proc_CFG_WhileTrue)
          hence "while (b) prog,procs \<turnstile> (Main,Label 0) 
            -(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<rightarrow> (Main,Label 2)"
            by(fastforce intro:PCFG.Main)
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
            \<open>nx' = Label 0\<close> show ?thesis
            by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
        qed
      next
        case False
        show ?thesis
        proof(cases "nx' = Exit")
          case True
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis by simp
        next
          case False
          with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> \<open>nx \<noteq> Entry\<close>
          have "while (b) prog \<turnstile> nx \<oplus> 2 -IEdge (kind a)\<rightarrow>\<^sub>p nx' \<oplus> 2"
            by(fastforce intro:Proc_CFG_edge_WhileBody_source_not_Entry)
          hence "while (b) prog,procs \<turnstile> (Main,nx \<oplus> 2)  -kind a\<rightarrow> 
            (Main,nx' \<oplus> 2)" by(rule PCFG.Main)
          with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym]
          show ?thesis
            by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
        qed
      qed
    qed
  next
    case (Proc p ins outs c nx n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close> 
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close> 
    have False by fastforce
    thus ?case by simp
  next
    case (MainCall l p es rets n' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Entry) = targetnode a\<close>[THEN sym]
      \<open>(Main, Label l) = sourcenode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close> have "n' \<noteq> Exit"
      by(fastforce dest:Proc_CFG_Call_Labels)
    with \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p n'\<close>
    have "while (b) prog \<turnstile> Label l \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
      n' \<oplus> 2" by -(rule Proc_CFG_edge_WhileBody_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "while (b) prog,procs \<turnstile> (Main,Label l \<oplus> 2) 
      -(\<lambda>s. True):(Main,n' \<oplus> 2)\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
      by(fastforce intro:PCFG.MainCall)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcCall p ins outs c l p' es' rets' l' ins' outs' c')
    from \<open>(p, Label l) = sourcenode a\<close>[THEN sym]
      \<open>(p', Entry) = targetnode a\<close>[THEN sym]  \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainReturn l p es rets l' ins outs c)
    from \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p, Exit) = sourcenode a\<close>[THEN sym]
      \<open>(Main, Label l') = targetnode a\<close>[THEN sym] wf
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have [simp]:"n = Label l'" by fastforce
    from \<open>prog \<turnstile> Label l -CEdge (p, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
    have "while (b) prog \<turnstile> Label l \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
      Label l' \<oplus> 2" by -(rule Proc_CFG_edge_WhileBody_source_not_Entry,auto)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "while (b) prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label l' \<oplus> 2))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label l' \<oplus> 2)"
      by(fastforce intro:PCFG.MainReturn)
    thus ?case by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
  next
    case (ProcReturn p ins outs c l p' es' rets' l' ins' outs' c' ps)
    from \<open>(p', Exit) = sourcenode a\<close>[THEN sym] 
      \<open>(p, Label l') = targetnode a\<close>[THEN sym] \<open>well_formed procs\<close>
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  next
    case (MainCallReturn nx p es rets nx')
    from \<open>(Main,n) = sourcenode a \<or> (Main,n) = targetnode a\<close> show ?case
    proof
      assume "(Main,n) = sourcenode a"
      with \<open>(Main, nx) = sourcenode a\<close>[THEN sym] have [simp]:"nx = n" by simp
      from \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close> have "nx' \<noteq> Exit"
        by(fastforce dest:Proc_CFG_Call_Labels)
      with \<open>n \<noteq> Entry\<close> \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "while (b) prog \<turnstile> n \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
        nx' \<oplus> 2" by(fastforce intro:Proc_CFG_edge_WhileBody_source_not_Entry)
      hence "while (b) prog,procs \<turnstile> (Main,n \<oplus> 2) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> 2)"
        by -(rule PCFG.MainCallReturn)
      thus ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    next
      assume "(Main, n) = targetnode a"
      from \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "nx \<noteq> Entry" and "nx' \<noteq> Exit" by(auto dest:Proc_CFG_Call_Labels)
      with \<open>prog \<turnstile> nx -CEdge (p, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "while (b) prog \<turnstile> nx \<oplus> 2 -CEdge (p, es, rets)\<rightarrow>\<^sub>p 
        nx' \<oplus> 2" by(fastforce intro:Proc_CFG_edge_WhileBody_source_not_Entry)
      hence "while (b) prog,procs \<turnstile> (Main,nx \<oplus> 2) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,nx' \<oplus> 2)"
        by -(rule PCFG.MainCallReturn)
      with \<open>(Main, n) = targetnode a\<close> \<open>(Main, nx') = targetnode a\<close>[THEN sym] 
      show ?thesis by(simp add:ProcCFG.valid_node_def)(fastforce simp:valid_edge_def)
    qed
  next
    case (ProcCallReturn p ins outs c nx p' es' rets' n' ps)
    from \<open>(p, nx) = sourcenode a\<close>[THEN sym] \<open>(p, n') = targetnode a\<close>[THEN sym]
      \<open>(p, ins, outs, c) \<in> set procs\<close> \<open>well_formed procs\<close>
      \<open>(Main, n) = sourcenode a \<or> (Main, n) = targetnode a\<close>
    have False by fastforce
    thus ?case by simp
  qed
qed


lemma path_Main_WhileBody:
  assumes "Rep_wf_prog wfp = (prog,procs)" 
  and "Rep_wf_prog wfp' = (while (b) prog,procs)"
  shows "\<lbrakk>wfp \<turnstile> (Main,n) -as\<rightarrow>* (p',n'); \<forall>a \<in> set as. intra_kind (kind a); 
    n \<noteq> Entry; n' \<noteq> Exit\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main,n \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p',n' \<oplus> 2)"
proof(induct "(Main,n)" as "(p',n')" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp) (Main, n')\<close>
    \<open>n' \<noteq> Entry\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    \<open>Rep_wf_prog wfp' = (while (b) prog,procs)\<close>
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n' \<oplus> 2)" 
    by(fastforce intro:valid_node_Main_WhileBody)
  with \<open>Main = p'\<close> show ?case
    by(fastforce intro:ProcCFG.empty_path simp:label_incrs_def)
next
  case (Cons_path n'' as a n)
  note IH = \<open>\<And>n.  \<lbrakk>n'' = (Main, n); \<forall>a\<in>set as. intra_kind (kind a); n \<noteq> Entry; 
    n' \<noteq> Exit\<rbrakk> \<Longrightarrow> wfp' \<turnstile> (Main, n \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p', n' \<oplus> 2)\<close>
  note [simp] = \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
     \<open>Rep_wf_prog wfp' = (while (b) prog,procs)\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>intra_kind (kind a)\<close> wf 
  obtain nx'' where "n'' = (Main,nx'')" and "nx'' \<noteq> Entry"
    by(auto elim!:PCFG.cases simp:valid_edge_def intra_kind_def)
  from IH[OF \<open>n'' = (Main,nx'')\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> 
    \<open>nx'' \<noteq> Entry\<close> \<open>n' \<noteq> Exit\<close>]
  have path:"wfp' \<turnstile> (Main, nx'' \<oplus> 2) -as \<oplus>s 2\<rightarrow>* (p', n' \<oplus> 2)" .
  with \<open>n' \<noteq> Exit\<close> have "nx'' \<noteq> Exit" by(fastforce dest:ProcCFGExit.path_Exit_source)
  with \<open>valid_edge wfp a\<close> \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close>
    \<open>n'' = (Main,nx'')\<close> \<open>n \<noteq> Entry\<close> \<open>intra_kind (kind a)\<close> wf
  have "while (b) prog,procs \<turnstile> (Main, n \<oplus> 2) -kind a\<rightarrow> (Main, nx'' \<oplus> 2)"
    by(fastforce intro:PCFG_Main_edge_WhileBody_source_not_Entry simp:valid_edge_def)
  with path \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = n''\<close> \<open>n'' = (Main,nx'')\<close>
  show ?case
    apply(cases a) apply(clarsimp simp:label_incrs_def)
    by(auto intro:ProcCFG.Cons_path simp:valid_edge_def)
qed


subsubsection \<open>Existence of intraprodecural paths\<close>

lemma Label_Proc_CFG_Entry_Exit_path_Main:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "l < #:prog"
  obtains as as' where "wfp \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)"
  and "\<forall>a \<in> set as. intra_kind (kind a)"
  and "wfp \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)"
  and "\<forall>a \<in> set as'. intra_kind (kind a)"
proof(atomize_elim)
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>l < #:prog\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
  show "\<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and>
    (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
    wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))"
  proof(induct prog arbitrary:l wfp)
    case Skip
    note [simp] = \<open>Rep_wf_prog wfp = (Skip, procs)\<close>
    from \<open>l < #:Skip\<close> have [simp]:"l = 0" by simp
    have "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))]\<rightarrow>* 
      (Main,Label 0)" 
      by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_Entry
                   simp:valid_edge_def ProcCFG.valid_node_def)
    moreover
    have "wfp \<turnstile> (Main,Label l) -[((Main,Label l),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)" 
      by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_Skip simp:valid_edge_def)
    ultimately show ?case by(fastforce simp:intra_kind_def)
  next
    case (LAss V e)
    note [simp] = \<open>Rep_wf_prog wfp = (V:=e, procs)\<close>
    from \<open>l < #:V:=e\<close> have "l = 0 \<or> l = 1" by auto
    thus ?case
    proof
      assume [simp]:"l = 0"
      have "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))]\<rightarrow>*
        (Main,Label 0)" 
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_Entry
                    simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      have "wfp \<turnstile> (Main,Label 0) 
        -((Main,Label 0),\<Up>(\<lambda>cf. update cf V e),(Main,Label 1))#
        [((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
        by(fastforce intro:ProcCFG.Cons_path ProcCFG.path.intros Main Proc_CFG_LAss 
          Proc_CFG_LAssSkip simp:valid_edge_def ProcCFG.valid_node_def)
      ultimately show ?thesis by(fastforce simp:intra_kind_def)
    next
      assume [simp]:"l = 1"
      have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
        [((Main,Label 0),\<Up>(\<lambda>cf. update cf V e),(Main,Label 1))]\<rightarrow>* (Main,Label 1)"
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_LAss ProcCFG.Cons_path 
          Main Proc_CFG_Entry simp:ProcCFG.valid_node_def valid_edge_def)
      moreover
      have "wfp \<turnstile> (Main,Label 1) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* 
        (Main,Exit)" by(fastforce intro:ProcCFG.path.intros  Main Proc_CFG_LAssSkip
        simp:valid_edge_def ProcCFG.valid_node_def)
      ultimately show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case (Seq c\<^sub>1 c\<^sub>2)
    note IH1 = \<open>\<And>l wfp. \<lbrakk>l < #:c\<^sub>1; Rep_wf_prog wfp = (c\<^sub>1, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))\<close>
    note IH2 = \<open>\<And>l wfp. \<lbrakk>l < #:c\<^sub>2; Rep_wf_prog wfp = (c\<^sub>2, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))\<close>
    note [simp] = \<open>Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)\<close>
    show ?case
    proof(cases "l < #:c\<^sub>1")
      case True
      from \<open>Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)\<close>
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^sub>1, procs)" by(erule wfp_Seq1)
      from IH1[OF True this] obtain as as' 
        where path1:"wfp' \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit)"
        and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
        and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l)"
        and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
      from path1 have "as \<noteq> []" by(fastforce elim:ProcCFG.path.cases)
      then obtain ax asx where [simp]:"as = asx@[ax]"
        by(cases as rule:rev_cases) fastforce+
      with path1 have "wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax"
        and "valid_edge wfp' ax" and "targetnode ax = (Main, Exit)"
        by(auto elim:ProcCFG.path_split_snoc)
      from \<open>valid_edge wfp' ax\<close> \<open>targetnode ax = (Main, Exit)\<close>
      obtain nx where "sourcenode ax = (Main,nx)" 
        by(fastforce elim:PCFG.cases simp:valid_edge_def)
      with \<open>wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax\<close> have "nx \<noteq> Entry"
        by fastforce
      moreover
      from \<open>valid_edge wfp' ax\<close> \<open>sourcenode ax = (Main,nx)\<close> have "nx \<noteq> Exit"
        by(fastforce intro:ProcCFGExit.Exit_source)
      ultimately obtain lx where [simp]:"nx = Label lx" by(cases nx) auto
      with \<open>wfp' \<turnstile> (Main, Label l) -asx\<rightarrow>* sourcenode ax\<close> 
        \<open>sourcenode ax = (Main,nx)\<close> intra1
      have path3:"wfp \<turnstile> (Main, Label l) -asx\<rightarrow>* (Main, Label lx)"
        by -(rule path_SeqFirst,auto)
      from \<open>valid_edge wfp' ax\<close> \<open>targetnode ax = (Main, Exit)\<close>
        \<open>sourcenode ax = (Main,nx)\<close> wf
      obtain etx where "c\<^sub>1 \<turnstile> Label lx -etx\<rightarrow>\<^sub>p Exit" 
        by(fastforce elim!:PCFG.cases simp:valid_edge_def)
      then obtain et where [simp]:"etx = IEdge et" 
        by(cases etx)(auto dest:Proc_CFG_Call_Labels)
      with \<open>c\<^sub>1 \<turnstile> Label lx -etx\<rightarrow>\<^sub>p Exit\<close> have "intra_kind et"
        by(fastforce intro:Proc_CFG_IEdge_intra_kind)
      from \<open>c\<^sub>1 \<turnstile> Label lx -etx\<rightarrow>\<^sub>p Exit\<close> path3
      have path4:"wfp \<turnstile> (Main, Label l) -asx@
        [((Main, Label lx),et,(Main,Label 0 \<oplus> #:c\<^sub>1))] \<rightarrow>* (Main,Label 0 \<oplus> #:c\<^sub>1)"
        by(fastforce intro:ProcCFG.path_Append ProcCFG.path.intros Proc_CFG_SeqConnect
          Main simp:ProcCFG.valid_node_def valid_edge_def)
      from \<open>Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)\<close>
      obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^sub>2, procs)" by(erule wfp_Seq2)
      from IH2[OF _ this,of "0"] obtain asx' 
        where "wfp'' \<turnstile> (Main, Label 0) -asx'\<rightarrow>* (Main, Exit)"
        and "\<forall>a\<in>set asx'. intra_kind (kind a)" by blast
      with path4 intra1 \<open>intra_kind et\<close> have "wfp \<turnstile> (Main, Label l) 
        -(asx@[((Main, Label lx),et,(Main,Label 0 \<oplus> #:c\<^sub>1))])@(asx' \<oplus>s #:c\<^sub>1)\<rightarrow>*
        (Main, Exit \<oplus> #:c\<^sub>1)"
        by -(erule ProcCFG.path_Append,rule path_Main_SeqSecond,auto)
      moreover
      from intra1 \<open>intra_kind et\<close> \<open>\<forall>a\<in>set asx'. intra_kind (kind a)\<close>
      have "\<forall>a \<in> set ((asx@[((Main, Label lx),et,(Main,Label #:c\<^sub>1))])@(asx' \<oplus>s #:c\<^sub>1)).
        intra_kind (kind a)" by(auto simp:label_incrs_def)
      moreover
      from path2 intra2 have "wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l)"
        by -(rule path_SeqFirst,auto)
      ultimately show ?thesis using \<open>\<forall>a\<in>set as'. intra_kind (kind a)\<close> by fastforce
    next
      case False
      hence "#:c\<^sub>1 \<le> l" by simp
      then obtain l' where [simp]:"l = l' + #:c\<^sub>1" and "l' = l - #:c\<^sub>1" by simp
      from \<open>l < #:c\<^sub>1;; c\<^sub>2\<close> have "l' < #:c\<^sub>2" by simp
      from \<open>Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)\<close>
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^sub>2, procs)" by(erule wfp_Seq2)
      from IH2[OF \<open>l' < #:c\<^sub>2\<close> this] obtain as as' 
        where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
        and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
        and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
        and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
      from path1 intra1
      have "wfp \<turnstile> (Main, Label l' \<oplus> #:c\<^sub>1) -as \<oplus>s #:c\<^sub>1\<rightarrow>* (Main, Exit \<oplus> #:c\<^sub>1)"
        by -(rule path_Main_SeqSecond,auto)
      moreover
      from path2 have "as' \<noteq> []" by(fastforce elim:ProcCFG.path.cases)
      with path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
        and "sourcenode ax' = (Main, Entry)" and "valid_edge wfp' ax'" 
        and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')"
        by -(erule ProcCFG.path_split_Cons,fastforce+)
      from \<open>wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')\<close>
      have "targetnode ax' \<noteq> (Main,Exit)" by fastforce
      with \<open>valid_edge wfp' ax'\<close> \<open>sourcenode ax' = (Main, Entry)\<close> wf
      have "targetnode ax' = (Main,Label 0)"
        by(fastforce elim:PCFG.cases dest:Proc_CFG_EntryD simp:valid_edge_def)
      with \<open>wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')\<close> intra2
      have path3:"wfp \<turnstile> (Main,Label 0 \<oplus> #:c\<^sub>1) -asx' \<oplus>s #:c\<^sub>1\<rightarrow>* 
        (Main, Label l' \<oplus> #:c\<^sub>1)" by -(rule path_Main_SeqSecond,auto)
      from \<open>Rep_wf_prog wfp = (c\<^sub>1;; c\<^sub>2, procs)\<close>
      obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^sub>1, procs)" by(erule wfp_Seq1)
      from IH1[OF _ this,of "0"] obtain xs 
        where "wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)"
        and "\<forall>a\<in>set xs. intra_kind (kind a)" by blast
      from \<open>wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)\<close> have "xs \<noteq> []"
        by(fastforce elim:ProcCFG.path.cases)
      then obtain x xs' where [simp]:"xs = xs'@[x]"
        by(cases xs rule:rev_cases) fastforce+
      with \<open>wfp'' \<turnstile> (Main, Label 0) -xs\<rightarrow>* (Main, Exit)\<close>
      have "wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x"
        and "valid_edge wfp'' x" and "targetnode x = (Main, Exit)"
        by(auto elim:ProcCFG.path_split_snoc)
      from \<open>valid_edge wfp'' x\<close> \<open>targetnode x = (Main, Exit)\<close>
      obtain nx where "sourcenode x = (Main,nx)" 
        by(fastforce elim:PCFG.cases simp:valid_edge_def)
      with \<open>wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x\<close> have "nx \<noteq> Entry"
        by fastforce
      from \<open>valid_edge wfp'' x\<close> \<open>sourcenode x = (Main,nx)\<close> have "nx \<noteq> Exit"
        by(fastforce intro:ProcCFGExit.Exit_source)
      with \<open>nx \<noteq> Entry\<close> obtain lx where [simp]:"nx = Label lx" by(cases nx) auto
      from \<open>wfp'' \<turnstile> (Main, Label 0) -xs'\<rightarrow>* sourcenode x\<close> 
        \<open>sourcenode x = (Main,nx)\<close> \<open>\<forall>a\<in>set xs. intra_kind (kind a)\<close>
      have "wfp \<turnstile> (Main, Entry) 
        -((Main, Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main, Label 0))#xs'\<rightarrow>* sourcenode x"
        apply simp apply(rule path_SeqFirst[OF \<open>Rep_wf_prog wfp'' = (c\<^sub>1, procs)\<close>])
        apply(auto intro!:ProcCFG.Cons_path)
        by(auto intro:Main Proc_CFG_Entry simp:valid_edge_def intra_kind_def)
      with \<open>valid_edge wfp'' x\<close> \<open>targetnode x = (Main, Exit)\<close> path3
        \<open>sourcenode x = (Main,nx)\<close> \<open>nx \<noteq> Entry\<close> \<open>sourcenode x = (Main,nx)\<close> wf
      have "wfp \<turnstile> (Main, Entry) -((((Main, Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main, Label 0))#xs')@
        [(sourcenode x,kind x,(Main,Label #:c\<^sub>1))])@(asx' \<oplus>s #:c\<^sub>1)\<rightarrow>* 
        (Main, Label l' \<oplus> #:c\<^sub>1)" 
        by(fastforce intro:ProcCFG.path_Append ProcCFG.path.intros Main 
          Proc_CFG_SeqConnect elim!:PCFG.cases dest:Proc_CFG_Call_Labels
          simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using intra1 intra2 \<open>\<forall>a\<in>set xs. intra_kind (kind a)\<close>
        by(fastforce simp:label_incrs_def intra_kind_def)
    qed
  next
    case (Cond b c\<^sub>1 c\<^sub>2)
    note IH1 = \<open>\<And>l wfp. \<lbrakk>l < #:c\<^sub>1; Rep_wf_prog wfp = (c\<^sub>1, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))\<close>
    note IH2 = \<open>\<And>l wfp. \<lbrakk>l < #:c\<^sub>2; Rep_wf_prog wfp = (c\<^sub>2, procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and> 
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))\<close>
    note [simp] = \<open>Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)\<close>
    show ?case
    proof(cases "l = 0")
      case True
      from \<open>Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)\<close>
      obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^sub>1, procs)" by(erule wfp_CondTrue)
      from IH1[OF _ this,of 0] obtain as 
        where path:"wfp' \<turnstile> (Main, Label 0) -as\<rightarrow>* (Main, Exit)"
        and intra:"\<forall>a\<in>set as. intra_kind (kind a)" by blast
      have "if (b) c\<^sub>1 else c\<^sub>2,procs \<turnstile> (Main,Label 0)
        -(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>\<rightarrow> (Main,Label 0 \<oplus> 1)"
        by(fastforce intro:Main Proc_CFG_CondTrue)
      with path intra have "wfp \<turnstile> (Main,Label 0)
        -[((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>,(Main,Label 0 \<oplus> 1))]@
        (as \<oplus>s 1)\<rightarrow>* (Main,Exit \<oplus> 1)"
        apply - apply(rule ProcCFG.path_Append) apply(rule ProcCFG.path.intros)+
        prefer 5 apply(rule path_Main_CondTrue)
        apply(auto intro:ProcCFG.path.intros simp:valid_edge_def)
        by(fastforce simp:ProcCFG.valid_node_def valid_edge_def)
      moreover
      have "if (b) c\<^sub>1 else c\<^sub>2,procs \<turnstile> (Main,Entry) -(\<lambda>s. True)\<^sub>\<surd>\<rightarrow> 
        (Main,Label 0)" by(fastforce intro:Main Proc_CFG_Entry)
      hence "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))]\<rightarrow>* 
        (Main,Label 0)"
        by(fastforce intro:ProcCFG.path.intros 
                    simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using \<open>l = 0\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> 
        by(fastforce simp:label_incrs_def intra_kind_def)
    next
      case False
      hence "0 < l" by simp
      then obtain l' where [simp]:"l = l' + 1" and "l' = l - 1" by simp
      show ?thesis
      proof(cases "l' < #:c\<^sub>1")
        case True
        from \<open>Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)\<close>
        obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c\<^sub>1, procs)" 
          by(erule wfp_CondTrue)
        from IH1[OF True this] obtain as as' 
          where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
          and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
          and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
          and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
        from path1 intra1
        have "wfp \<turnstile> (Main, Label l' \<oplus> 1) -as \<oplus>s 1\<rightarrow>* (Main, Exit \<oplus> 1)"
          by -(rule path_Main_CondTrue,auto)
        moreover
        from path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
          and "sourcenode ax' = (Main,Entry)" and "valid_edge wfp' ax'"
          and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')"
          by -(erule ProcCFG.path.cases,fastforce+)
        with wf have "targetnode ax' = (Main,Label 0)"
          by(fastforce elim:PCFG.cases dest:Proc_CFG_EntryD Proc_CFG_Call_Labels 
                      simp:valid_edge_def)
        with \<open>wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l')\<close> intra2
        have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
          ((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>,(Main,Label 0 \<oplus> 1))#
          (asx' \<oplus>s 1)\<rightarrow>* (Main,Label l' \<oplus> 1)"
          apply - apply(rule ProcCFG.path.intros)+ apply(rule path_Main_CondTrue) 
          by(auto intro:Main Proc_CFG_Entry Proc_CFG_CondTrue simp:valid_edge_def)
        ultimately show ?thesis using intra1 intra2
          by(fastforce simp:label_incrs_def intra_kind_def)
      next
        case False
        hence "#:c\<^sub>1 \<le> l'" by simp
        then obtain l'' where [simp]:"l' = l'' + #:c\<^sub>1" and "l'' = l' - #:c\<^sub>1" by simp
        from  \<open>l < #:(if (b) c\<^sub>1 else c\<^sub>2)\<close> have "l'' < #:c\<^sub>2" by simp
        from \<open>Rep_wf_prog wfp = (if (b) c\<^sub>1 else c\<^sub>2, procs)\<close>
        obtain wfp'' where [simp]:"Rep_wf_prog wfp'' = (c\<^sub>2, procs)" 
          by(erule wfp_CondFalse)
        from IH2[OF \<open>l'' < #:c\<^sub>2\<close> this] obtain as as' 
          where path1:"wfp'' \<turnstile> (Main, Label l'') -as\<rightarrow>* (Main, Exit)"
          and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
          and path2:"wfp'' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l'')"
          and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
        from path1 intra1
        have "wfp \<turnstile> (Main, Label l'' \<oplus> (#:c\<^sub>1 + 1)) -as \<oplus>s (#:c\<^sub>1 + 1)\<rightarrow>* 
          (Main, Exit \<oplus> (#:c\<^sub>1 + 1))"
          by -(rule path_Main_CondFalse,auto simp:add.assoc)
        moreover
        from path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
          and "sourcenode ax' = (Main,Entry)" and "valid_edge wfp'' ax'"
          and "wfp'' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l'')"
          by -(erule ProcCFG.path.cases,fastforce+)
        with wf have "targetnode ax' = (Main,Label 0)"
          by(fastforce elim:PCFG.cases dest:Proc_CFG_EntryD Proc_CFG_Call_Labels 
                      simp:valid_edge_def)
        with \<open>wfp'' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main, Label l'')\<close> intra2
        have "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
          ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>,
          (Main,Label (#:c\<^sub>1 + 1)))#(asx' \<oplus>s (#:c\<^sub>1 + 1))\<rightarrow>* 
          (Main,Label l'' \<oplus> (#:c\<^sub>1 + 1))"
          apply - apply(rule ProcCFG.path.intros)+ apply(rule path_Main_CondFalse)
          by(auto intro:Main Proc_CFG_Entry Proc_CFG_CondFalse simp:valid_edge_def)
        ultimately show ?thesis using intra1 intra2
          by(fastforce simp:label_incrs_def intra_kind_def add.assoc)
      qed
    qed
  next
    case (While b c')
    note IH = \<open>\<And>l wfp. \<lbrakk>l < #:c'; Rep_wf_prog wfp = (c', procs)\<rbrakk> \<Longrightarrow>
      \<exists>as as'. wfp \<turnstile> (Main, Label l) -as\<rightarrow>* (Main, Exit) \<and>
      (\<forall>a\<in>set as. intra_kind (kind a)) \<and>
      wfp \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l) \<and> (\<forall>a\<in>set as'. intra_kind (kind a))\<close>
    note [simp] = \<open>Rep_wf_prog wfp = (while (b) c', procs)\<close>
    show ?case
    proof(cases "l = 0")
      case True
      hence "wfp \<turnstile> (Main,Label l) - 
        ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>,(Main,Label 1))#
        [((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_WhileFalseSkip 
          Proc_CFG_WhileFalse simp:valid_edge_def)
      moreover
      have "while (b) c' \<turnstile> Entry -IEdge (\<lambda>s. True)\<^sub>\<surd>\<rightarrow>\<^sub>p Label 0" by(rule Proc_CFG_Entry)
      with \<open>l = 0\<close> have "wfp \<turnstile> (Main,Entry) 
        -[((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))]\<rightarrow>* (Main,Label l)"
        by(fastforce intro:ProcCFG.path.intros Main 
                     simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis by(fastforce simp:intra_kind_def)
    next
      case False
      hence "1 \<le> l" by simp
      thus ?thesis
      proof(cases "l < 2")
        case True
        with \<open>1 \<le> l\<close> have [simp]:"l = 1" by simp
        have "wfp \<turnstile> (Main,Label l) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
          by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_WhileFalseSkip 
                      simp:valid_edge_def)
        moreover
        have "while (b) c' \<turnstile> Label 0 -IEdge (\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>\<rightarrow>\<^sub>p 
          Label 1" by(rule Proc_CFG_WhileFalse)
        hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
          [((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>,(Main,Label 1))]\<rightarrow>*
          (Main,Label l)"
          by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_Entry 
                       simp:ProcCFG.valid_node_def valid_edge_def)
        ultimately show ?thesis by(fastforce simp:intra_kind_def)
      next
        case False
        with \<open>1 \<le> l\<close> have "2 \<le> l" by simp
        then obtain l' where [simp]:"l = l' + 2" and "l' = l - 2" 
          by(simp del:add_2_eq_Suc')
        from \<open>l < #:while (b) c'\<close> have "l' < #:c'" by simp
        from \<open>Rep_wf_prog wfp = (while (b) c', procs)\<close>
        obtain wfp' where [simp]:"Rep_wf_prog wfp' = (c', procs)" 
          by(erule wfp_WhileBody)
        from IH[OF \<open>l' < #:c'\<close> this] obtain as as' 
          where path1:"wfp' \<turnstile> (Main, Label l') -as\<rightarrow>* (Main, Exit)"
          and intra1:"\<forall>a\<in>set as. intra_kind (kind a)"
          and path2:"wfp' \<turnstile> (Main, Entry) -as'\<rightarrow>* (Main, Label l')"
          and intra2:"\<forall>a\<in>set as'. intra_kind (kind a)" by blast
        from path1 have "as \<noteq> []" by(fastforce elim:ProcCFG.path.cases)
        with path1 obtain ax asx where [simp]:"as = asx@[ax]"
          and "wfp' \<turnstile> (Main, Label l') -asx\<rightarrow>* sourcenode ax"
          and "valid_edge wfp' ax" and "targetnode ax = (Main, Exit)"
          by -(erule ProcCFG.path_split_snoc,fastforce+)
        with wf obtain lx etx where "sourcenode ax = (Main,Label lx)"
          and "intra_kind (kind ax)"
          apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Labels simp:valid_edge_def)
          by(case_tac n)(auto dest:Proc_CFG_IEdge_intra_kind)
        with \<open>wfp' \<turnstile> (Main, Label l') -asx\<rightarrow>* sourcenode ax\<close> intra1
        have "wfp \<turnstile> (Main, Label l' \<oplus> 2) -asx \<oplus>s 2\<rightarrow>* (Main,Label lx \<oplus> 2)"
          by -(rule path_Main_WhileBody,auto)
        from \<open>valid_edge wfp' ax\<close> \<open>sourcenode ax = (Main,Label lx)\<close>
          \<open>targetnode ax = (Main, Exit)\<close> \<open>intra_kind (kind ax)\<close> wf
        have "while (b) c',procs \<turnstile> (Main,Label lx \<oplus> 2) -kind ax\<rightarrow> 
          (Main,Label 0)"
          by(fastforce intro!:Main Proc_CFG_WhileBodyExit elim!:PCFG.cases 
                        dest:Proc_CFG_Call_Labels simp:valid_edge_def)
        hence "wfp \<turnstile> (Main,Label lx \<oplus> 2) 
          -((Main,Label lx \<oplus> 2),kind ax,(Main,Label 0))#
          ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>,(Main,Label 1))#
          [((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
          by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_WhileFalse 
            Proc_CFG_WhileFalseSkip simp:valid_edge_def)
        with \<open>wfp \<turnstile> (Main, Label l' \<oplus> 2) -asx \<oplus>s 2\<rightarrow>* (Main,Label lx \<oplus> 2)\<close>
        have "wfp \<turnstile> (Main, Label l) -(asx \<oplus>s 2)@
          (((Main,Label lx \<oplus> 2),kind ax,(Main,Label 0))#
          ((Main,Label 0),(\<lambda>cf. state_check cf b (Some false))\<^sub>\<surd>,(Main,Label 1))#
          [((Main,Label 1),\<Up>id,(Main,Exit))])\<rightarrow>* (Main,Exit)"
          by(fastforce intro:ProcCFG.path_Append)
        moreover
        from path2 have "as' \<noteq> []" by(fastforce elim:ProcCFG.path.cases)
        with path2 obtain ax' asx' where [simp]:"as' = ax'#asx'"
          and "wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main,Label l')"
          and "valid_edge wfp' ax'" and "sourcenode ax' = (Main, Entry)"
          by -(erule ProcCFG.path_split_Cons,fastforce+)
        with wf have "targetnode ax' = (Main,Label 0)" and "intra_kind (kind ax')"
          by(fastforce elim!:PCFG.cases dest:Proc_CFG_Call_Labels 
            Proc_CFG_EntryD simp:intra_kind_def valid_edge_def)+
        with \<open>wfp' \<turnstile> targetnode ax' -asx'\<rightarrow>* (Main,Label l')\<close> intra2
        have "wfp \<turnstile> (Main, Label 0 \<oplus> 2) -asx' \<oplus>s 2\<rightarrow>* (Main,Label l' \<oplus> 2)"
          by -(rule path_Main_WhileBody,auto simp del:add_2_eq_Suc')
        hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
          ((Main,Label 0),(\<lambda>cf. state_check cf b (Some true))\<^sub>\<surd>,(Main,Label 2))#
          (asx' \<oplus>s 2)\<rightarrow>* (Main,Label l)"
          by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_WhileTrue 
            Proc_CFG_Entry simp:valid_edge_def)
        ultimately show ?thesis using \<open>intra_kind (kind ax)\<close> intra1 intra2
          by(fastforce simp:label_incrs_def intra_kind_def)
      qed
    qed
  next
    case (Call p es rets)
    note Rep [simp] = \<open>Rep_wf_prog wfp = (Call p es rets, procs)\<close>
    have cC:"containsCall procs (Call p es rets) [] p" by simp
    show ?case
    proof(cases "l = 0")
      case True
      have "wfp \<turnstile> (Main,Label 0) -((Main,Label 0),(\<lambda>s. False)\<^sub>\<surd>,(Main,Label 1))#
        [((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_CallSkip MainCallReturn
          Proc_CFG_Call simp:valid_edge_def)
      moreover
      have "Call p es rets,procs \<turnstile> (Main,Entry) -(\<lambda>s. True)\<^sub>\<surd>\<rightarrow> (Main,Label 0)"
        by(fastforce intro:Main Proc_CFG_Entry)
      hence "wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))]\<rightarrow>*
        (Main,Label 0)"
        by(fastforce intro:ProcCFG.path.intros 
          simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using \<open>l = 0\<close> by(fastforce simp:intra_kind_def)
    next
      case False
      with \<open>l < #:Call p es rets\<close> have "l = 1" by simp
      have "wfp \<turnstile> (Main,Label 1) -[((Main,Label 1),\<Up>id,(Main,Exit))]\<rightarrow>* (Main,Exit)"
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_CallSkip
                    simp:valid_edge_def)
      moreover
      have "Call p es rets,procs \<turnstile> (Main,Label 0) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main,Label 1)"
        by(fastforce intro:MainCallReturn Proc_CFG_Call)
      hence "wfp \<turnstile> (Main,Entry) -((Main,Entry),(\<lambda>s. True)\<^sub>\<surd>,(Main,Label 0))#
        [((Main,Label 0),(\<lambda>s. False)\<^sub>\<surd>,(Main,Label 1))]\<rightarrow>* (Main,Label 1)"
        by(fastforce intro:ProcCFG.path.intros Main Proc_CFG_Entry 
                    simp:ProcCFG.valid_node_def valid_edge_def)
      ultimately show ?thesis using \<open>l = 1\<close> by(fastforce simp:intra_kind_def)
    qed
  qed
qed



subsection \<open>Lifting from edges in procedure Main to arbitrary procedures\<close>

lemma lift_edge_Main_Main:
  "\<lbrakk>c,procs \<turnstile> (Main, n) -et\<rightarrow> (Main, n'); (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p; well_formed procs\<rbrakk> 
  \<Longrightarrow> prog,procs \<turnstile> (p, n) -et\<rightarrow> (p, n')"
proof(induct "(Main,n)" et "(Main,n')" rule:PCFG.induct)
  case Main thus ?case by(fastforce intro:Proc)
next
  case MainCallReturn thus ?case by(fastforce intro:ProcCallReturn)
qed auto

lemma lift_edge_Main_Proc:
  "\<lbrakk>c,procs \<turnstile> (Main, n) -et\<rightarrow> (q, n'); q \<noteq> Main; (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p; well_formed procs\<rbrakk> 
  \<Longrightarrow> \<exists>et'. prog,procs \<turnstile> (p, n) -et'\<rightarrow> (q, n')"
proof(induct "(Main,n)" et "(q,n')" rule:PCFG.induct)
  case (MainCall l esx retsx n'x insx outsx cx)
  from \<open>c \<turnstile> Label l -CEdge (q, esx, retsx)\<rightarrow>\<^sub>p n'x\<close> 
  obtain l' where [simp]:"n'x = Label l'" by(fastforce dest:Proc_CFG_Call_Labels)
  with MainCall have "prog,procs \<turnstile> (p, n) 
    -(\<lambda>s. True):(p,n'x)\<hookrightarrow>\<^bsub>q\<^esub>map (\<lambda>e cf. interpret e cf) esx\<rightarrow> (q, n')"
    by(fastforce intro:ProcCall)
  thus ?case by fastforce
qed auto

lemma lift_edge_Proc_Main:
  "\<lbrakk>c,procs \<turnstile> (q, n) -et\<rightarrow> (Main, n'); q \<noteq> Main; (p,ins,outs,c) \<in> set procs;
  containsCall procs prog ps p; well_formed procs\<rbrakk> 
  \<Longrightarrow> \<exists>et'. prog,procs \<turnstile> (q, n) -et'\<rightarrow> (p, n')"
proof(induct "(q,n)" et "(Main,n')" rule:PCFG.induct)
  case (MainReturn l esx retsx l' insx outsx cx)
  note [simp] = \<open>Exit = n\<close>[THEN sym] \<open>Label l' = n'\<close>[THEN sym]
  from MainReturn have "prog,procs \<turnstile> (q,Exit) -(\<lambda>cf. snd cf = (p,Label l'))\<hookleftarrow>\<^bsub>q\<^esub>
    (\<lambda>cf cf'. cf'(retsx [:=] map cf outsx))\<rightarrow> (p,Label l')"
    by(fastforce intro!:ProcReturn)
  thus ?case by fastforce
qed auto


fun lift_edge :: "edge \<Rightarrow> pname \<Rightarrow> edge"
where "lift_edge a p = ((p,snd(sourcenode a)),kind a,(p,snd(targetnode a)))"

fun lift_path :: "edge list \<Rightarrow> pname \<Rightarrow> edge list"
  where "lift_path as p = map (\<lambda>a. lift_edge a p) as"


lemma lift_path_Proc: 
  assumes "Rep_wf_prog wfp' = (c,procs)" and "Rep_wf_prog wfp = (prog,procs)"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p"
  shows "\<lbrakk>wfp' \<turnstile> (Main,n) -as\<rightarrow>* (Main,n'); \<forall>a \<in> set as. intra_kind (kind a)\<rbrakk>
  \<Longrightarrow> wfp \<turnstile> (p,n) -lift_path as p\<rightarrow>* (p,n')"
proof(induct "(Main,n)" as "(Main,n')" arbitrary:n rule:ProcCFG.path.induct)
  case empty_path
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>CFG.valid_node sourcenode targetnode (valid_edge wfp') (Main, n')\<close>
    assms wf
  have "CFG.valid_node sourcenode targetnode (valid_edge wfp) (p,n')"
    apply(auto simp:ProcCFG.valid_node_def valid_edge_def)
     apply(case_tac "ab = Main")
      apply(fastforce dest:lift_edge_Main_Main)
     apply(fastforce dest!:lift_edge_Main_Proc)
    apply(case_tac "a = Main")
     apply(fastforce dest:lift_edge_Main_Main)
    by(fastforce dest!:lift_edge_Proc_Main)
  thus ?case by(fastforce dest:ProcCFG.empty_path)
next
  case (Cons_path m'' as a n)
  note IH = \<open>\<And>n. \<lbrakk>m'' = (Main, n); \<forall>a\<in>set as. intra_kind (kind a)\<rbrakk>
    \<Longrightarrow> wfp \<turnstile> (p, n) -lift_path as p\<rightarrow>* (p, n')\<close>
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs" 
    by(fastforce intro:wf_wf_prog)
  from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "intra_kind (kind a)"
    and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
  from \<open>valid_edge wfp' a\<close> \<open>intra_kind (kind a)\<close> \<open>sourcenode a = (Main, n)\<close> 
    \<open>targetnode a = m''\<close> \<open>Rep_wf_prog wfp' = (c,procs)\<close>
  obtain n'' where "m'' = (Main, n'')"
    by(fastforce elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  with \<open>valid_edge wfp' a\<close> \<open>Rep_wf_prog wfp' = (c,procs)\<close>
    \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = m''\<close>
    \<open>(p,ins,outs,c) \<in> set procs\<close> \<open>containsCall procs prog ps p\<close> 
    \<open>Rep_wf_prog wfp = (prog,procs)\<close> wf
  have "prog,procs \<turnstile> (p, n) -kind a\<rightarrow> (p, n'')"
    by(auto intro:lift_edge_Main_Main simp:valid_edge_def)  
  from IH[OF \<open>m'' = (Main, n'')\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close>]
  have "wfp \<turnstile> (p, n'') -lift_path as p\<rightarrow>* (p, n')" .
  with \<open>prog,procs \<turnstile> (p, n) -kind a\<rightarrow> (p, n'')\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    \<open>sourcenode a = (Main, n)\<close> \<open>targetnode a = m''\<close> \<open>m'' = (Main, n'')\<close>
  show ?case by simp (rule ProcCFG.Cons_path,auto simp:valid_edge_def)
qed


subsection \<open>Existence of paths from Entry and to Exit\<close>

lemma Label_Proc_CFG_Entry_Exit_path_Proc:
  assumes "Rep_wf_prog wfp = (prog,procs)" and "l < #:c"
  and "(p,ins,outs,c) \<in> set procs" and "containsCall procs prog ps p"
  obtains as as' where "wfp \<turnstile> (p,Label l) -as\<rightarrow>* (p,Exit)"
  and "\<forall>a \<in> set as. intra_kind (kind a)"
  and "wfp \<turnstile> (p,Entry) -as'\<rightarrow>* (p,Label l)"
  and "\<forall>a \<in> set as'. intra_kind (kind a)"
proof(atomize_elim)
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
    \<open>containsCall procs prog ps p\<close>
  obtain wfp' where "Rep_wf_prog wfp' = (c,procs)" by(erule wfp_Call)
  from this \<open>l < #:c\<close> obtain as as' where "wfp' \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)"
    and "\<forall>a \<in> set as. intra_kind (kind a)"
    and "wfp' \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)"
    and "\<forall>a \<in> set as'. intra_kind (kind a)" 
    by(erule Label_Proc_CFG_Entry_Exit_path_Main)
  from \<open>Rep_wf_prog wfp' = (c,procs)\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    \<open>(p,ins,outs,c) \<in> set procs\<close> \<open>containsCall procs prog ps p\<close>
    \<open>wfp' \<turnstile> (Main,Label l) -as\<rightarrow>* (Main,Exit)\<close> \<open>\<forall>a \<in> set as. intra_kind (kind a)\<close>
  have "wfp \<turnstile> (p,Label l) -lift_path as p\<rightarrow>* (p,Exit)"
    by(fastforce intro:lift_path_Proc)
  moreover
  from \<open>Rep_wf_prog wfp' = (c,procs)\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    \<open>(p,ins,outs,c) \<in> set procs\<close> \<open>containsCall procs prog ps p\<close>
    \<open>wfp' \<turnstile> (Main,Entry) -as'\<rightarrow>* (Main,Label l)\<close> \<open>\<forall>a \<in> set as'. intra_kind (kind a)\<close>
  have "wfp \<turnstile> (p,Entry) -lift_path as' p\<rightarrow>* (p,Label l)"
    by(fastforce intro:lift_path_Proc)
  moreover
  from \<open>\<forall>a \<in> set as. intra_kind (kind a)\<close> \<open>\<forall>a \<in> set as'. intra_kind (kind a)\<close>
  have "\<forall>a \<in> set (lift_path as p). intra_kind (kind a)"
    and "\<forall>a \<in> set (lift_path as' p). intra_kind (kind a)" by auto
  ultimately
  show "\<exists>as as'. wfp \<turnstile> (p, Label l) -as\<rightarrow>* (p, Exit) \<and>
    (\<forall>a\<in>set as. intra_kind (kind a)) \<and> wfp \<turnstile> (p, Entry) -as'\<rightarrow>* (p, Label l) \<and>
    (\<forall>a\<in>set as'. intra_kind (kind a))" by fastforce
qed


lemma Entry_to_Entry_and_Exit_to_Exit: 
  assumes "Rep_wf_prog wfp = (prog,procs)"
  and "containsCall procs prog ps p" and "(p,ins,outs,c) \<in> set procs"
  obtains as as' where "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p,Entry)"
  and "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (p,Exit) as' (Main,Exit)"
proof(atomize_elim)
  from \<open>containsCall procs prog ps p\<close> \<open>(p,ins,outs,c) \<in> set procs\<close>
  show "\<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
    (get_return_edges wfp) (Main, Entry) as (p, Entry) \<and>
    CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
    (get_return_edges wfp) (p, Exit) as' (Main, Exit)"
  proof(induct ps arbitrary:p ins outs c rule:rev_induct)
    case Nil
    from \<open>containsCall procs prog [] p\<close>
    obtain lx es rets lx' where "prog \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label lx'"
      by(erule containsCall_empty_Proc_CFG_Call_edge)
    with \<open>(p, ins, outs, c) \<in> set procs\<close>
    have "prog,procs \<turnstile> (Main,Label lx) -(\<lambda>s. True):(Main,Label lx')\<hookrightarrow>\<^bsub>p\<^esub>
      map (\<lambda>e cf. interpret e cf) es\<rightarrow>  (p,Entry)" 
      and "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (Main,Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (Main,Label lx')"
      by -(rule MainCall,assumption+,rule MainReturn)
    with \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    have "wfp \<turnstile> (Main,Label lx) -[((Main,Label lx),
      (\<lambda>s. True):(Main,Label lx')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es,(p,Entry))]\<rightarrow>* 
      (p,Entry)"
      and "wfp \<turnstile> (p,Exit) -[((p,Exit),(\<lambda>cf. snd cf = (Main,Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs)),(Main,Label lx'))]\<rightarrow>* (Main,Label lx')"
      by(fastforce intro:ProcCFG.path.intros 
        simp:ProcCFG.valid_node_def valid_edge_def)+
    moreover
    from \<open>prog \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label lx'\<close>
    have "lx < #:prog" and "lx' < #:prog"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes 
                    Proc_CFG_targetlabel_less_num_nodes)
    from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>lx < #:prog\<close> obtain as 
      where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label lx)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)
    moreover
    from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>lx' < #:prog\<close> obtain as' 
      where "wfp \<turnstile> (Main,Label lx') -as'\<rightarrow>* (Main,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)
    moreover
    from \<open>\<forall>a \<in> set as. intra_kind (kind a)\<close> 
    have "CFG.valid_path kind (get_return_edges wfp) 
      (as@[((Main,Label lx),(\<lambda>s. True):(Main,Label lx')\<hookrightarrow>\<^bsub>p\<^esub>
      map (\<lambda>e cf. interpret e cf) es,(p,Entry))])"
      by(fastforce intro:ProcCFG.same_level_path_valid_path_Append 
        ProcCFG.intras_same_level_path simp:ProcCFG.valid_path_def)
    moreover
    from \<open>\<forall>a \<in> set as'. intra_kind (kind a)\<close> 
    have "CFG.valid_path kind (get_return_edges wfp) 
      ([((p,Exit),(\<lambda>cf. snd cf = (Main,Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs)),(Main,Label lx'))]@as')"
      by(fastforce intro:ProcCFG.valid_path_same_level_path_Append 
        ProcCFG.intras_same_level_path simp:ProcCFG.valid_path_def)
    ultimately show ?case by(fastforce intro:ProcCFG.path_Append simp:ProcCFG.vp_def)
  next
    case (snoc p' ps')
    note IH = \<open>\<And>p ins outs c. 
      \<lbrakk>containsCall procs prog ps' p; (p,ins,outs,c) \<in> set procs\<rbrakk>
      \<Longrightarrow> \<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) as (p, Entry) \<and>
      CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (p, Exit) as' (Main, Exit)\<close>
    from \<open>containsCall procs prog (ps' @ [p']) p\<close>
    obtain ins' outs' c' where "(p',ins',outs',c') \<in> set procs"
      and "containsCall procs c' [] p" 
      and "containsCall procs prog ps' p'" by(auto elim:containsCallE)
    from IH[OF \<open>containsCall procs prog ps' p'\<close> \<open>(p',ins',outs',c') \<in> set procs\<close>] 
    obtain as as' where pathE:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (Main, Entry) as (p', Entry)"
      and pathX:"CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (p', Exit) as' (Main, Exit)" by blast
    from \<open>containsCall procs c' [] p\<close>
    obtain lx es rets lx' where edge:"c' \<turnstile> Label lx -CEdge (p,es,rets)\<rightarrow>\<^sub>p Label lx'"
      by(erule containsCall_empty_Proc_CFG_Call_edge)
    hence "lx < #:c'" and "lx' < #:c'"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes 
                    Proc_CFG_targetlabel_less_num_nodes)
    from \<open>lx < #:c'\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(p',ins',outs',c') \<in> set procs\<close>
      \<open>containsCall procs prog ps' p'\<close> obtain asx 
      where "wfp \<turnstile> (p',Entry) -asx\<rightarrow>* (p',Label lx)"
      and "\<forall>a \<in> set asx. intra_kind (kind a)"
      by(fastforce elim:Label_Proc_CFG_Entry_Exit_path_Proc)
    with pathE have pathE2:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (Main, Entry) (as@asx) (p', Label lx)"
      by(fastforce intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
        ProcCFG.intras_same_level_path simp:ProcCFG.vp_def)
    from \<open>lx' < #:c'\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
      \<open>(p',ins',outs',c') \<in> set procs\<close> \<open>containsCall procs prog ps' p'\<close> 
    obtain asx' where "wfp \<turnstile> (p',Label lx') -asx'\<rightarrow>* (p',Exit)"
      and "\<forall>a \<in> set asx'. intra_kind (kind a)"
      by(fastforce elim:Label_Proc_CFG_Entry_Exit_path_Proc)
    with pathX have pathX2:"CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (p', Label lx') (asx'@as') (Main, Exit)"
      by(fastforce intro:ProcCFG.path_Append ProcCFG.same_level_path_valid_path_Append
        ProcCFG.intras_same_level_path simp:ProcCFG.vp_def)
    from edge \<open>(p,ins,outs,c) \<in> set procs\<close> \<open>(p',ins',outs',c') \<in> set procs\<close>
      \<open>containsCall procs prog ps' p'\<close>
    have "prog,procs \<turnstile> (p',Label lx) -(\<lambda>s. True):(p',Label lx')\<hookrightarrow>\<^bsub>p\<^esub>
      map (\<lambda>e cf. interpret e cf) es\<rightarrow> (p,Entry)"
      and "prog,procs \<turnstile> (p,Exit) -(\<lambda>cf. snd cf = (p',Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs))\<rightarrow> (p',Label lx')"
      by(fastforce intro:ProcCall ProcReturn)+
    with \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    have path:"wfp \<turnstile> (p',Label lx) -[((p',Label lx),(\<lambda>s. True):(p',Label lx')\<hookrightarrow>\<^bsub>p\<^esub>
      map (\<lambda>e cf. interpret e cf) es,(p,Entry))]\<rightarrow>* (p,Entry)"
      and path':"wfp \<turnstile> (p,Exit) -[((p,Exit),(\<lambda>cf. snd cf = (p',Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs)),(p',Label lx'))]\<rightarrow>* 
      (p',Label lx')"
      by(fastforce intro:ProcCFG.path.intros 
                  simp:ProcCFG.valid_node_def valid_edge_def)+
    from path pathE2 have "CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) ((as@asx)@[((p',Label lx),
      (\<lambda>s. True):(p',Label lx')\<hookrightarrow>\<^bsub>p\<^esub>map (\<lambda>e cf. interpret e cf) es,(p,Entry))])
      (p,Entry)"
      apply(unfold ProcCFG.vp_def) apply(rule conjI)
       apply(fastforce intro:ProcCFG.path_Append)
      by(unfold ProcCFG.valid_path_def,fastforce intro:ProcCFG.vpa_snoc_Call)
    moreover
    from path' pathX2 have "CFG.valid_path' sourcenode targetnode kind 
      (valid_edge wfp) (get_return_edges wfp) (p,Exit)
      ([((p,Exit),(\<lambda>cf. snd cf = (p',Label lx'))\<hookleftarrow>\<^bsub>p\<^esub>
      (\<lambda>cf cf'. cf'(rets [:=] map cf outs)),(p',Label lx'))]@(asx'@as')) (Main, Exit)"
      apply(unfold ProcCFG.vp_def) apply(rule conjI)
       apply(fastforce intro:ProcCFG.path_Append)
      by(simp add:ProcCFG.valid_path_def ProcCFG.valid_path_def)
    ultimately show ?case by blast
  qed
qed


lemma edge_valid_paths:
  assumes "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
  and disj:"(p,n) = sourcenode a \<or> (p,n) = targetnode a" 
  and [simp]:"Rep_wf_prog wfp = (prog,procs)"
  shows "\<exists>as as'. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
                (get_return_edges wfp) (Main,Entry) as (p,n) \<and>
              CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
                (get_return_edges wfp) (p,n) as' (Main,Exit)"
proof -
  from \<open>Rep_wf_prog wfp = (prog,procs)\<close> have wf:"well_formed procs"
    by(fastforce intro:wf_wf_prog)
  from \<open>prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a\<close>
  show ?thesis
  proof(induct "sourcenode a" "kind a" "targetnode a" rule:PCFG.induct)
    case (Main nx nx')
    from \<open>(Main, nx) = sourcenode a\<close>[THEN sym] \<open>(Main, nx') = targetnode a\<close>[THEN sym]
      disj have [simp]:"p = Main" by auto
    have "prog,procs \<turnstile> (Main, Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (Main, Exit)"
      by(fastforce intro:PCFG.Main Proc_CFG_Entry_Exit)
    hence EXpath:"wfp \<turnstile> (Main,Entry) -[((Main,Entry),(\<lambda>s. False)\<^sub>\<surd>,(Main,Exit))]\<rightarrow>*
        (Main,Exit)"
      by(fastforce intro:ProcCFG.path.intros
        simp:valid_edge_def ProcCFG.valid_node_def)
    show ?case
    proof(cases n)
      case (Label l)
      with \<open>prog \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> \<open>(Main, nx) = sourcenode a\<close>[THEN sym]
        \<open>(Main, nx') = targetnode a\<close>[THEN sym] disj
      have "l < #:prog" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
        Proc_CFG_targetlabel_less_num_nodes)
      with \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      with Label show ?thesis
        apply(rule_tac x="as" in exI) apply(rule_tac x="as'" in exI) apply simp
        by(fastforce intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    next
      case Entry
      hence "wfp \<turnstile> (Main,Entry) -[]\<rightarrow>* (Main,n)" by(fastforce intro:ProcCFG.empty_path)
      with EXpath show ?thesis by(fastforce simp:ProcCFG.vp_def ProcCFG.valid_path_def)
    next
      case Exit
      hence "wfp \<turnstile> (Main,n) -[]\<rightarrow>* (Main,Exit)" by(fastforce intro:ProcCFG.empty_path)
      with Exit EXpath show ?thesis using Exit
        apply(rule_tac x="[((Main,Entry),(\<lambda>s. False)\<^sub>\<surd>,(Main,Exit))]" in exI) 
        apply simp
        by(fastforce intro:ProcCFG.intra_path_vp 
          simp:ProcCFG.intra_path_def intra_kind_def)
    qed
  next
    case (Proc px ins outs c nx nx' ps)
    from \<open>(px, ins, outs, c) \<in> set procs\<close> wf have [simp]:"px \<noteq> Main" by auto
    from disj \<open>(px, nx) = sourcenode a\<close>[THEN sym] \<open>(px, nx') = targetnode a\<close>[THEN sym]
    have [simp]:"p = px" by auto
    from \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
      \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
    obtain asx asx' where path:"CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
      and path':"CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
      by -(erule Entry_to_Entry_and_Exit_to_Exit)+
    from \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
    have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px, Exit)"
      by(fastforce intro:PCFG.Proc Proc_CFG_Entry_Exit)
    hence EXpath:"wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]\<rightarrow>* 
      (px,Exit)" by(fastforce intro:ProcCFG.path.intros 
        simp:valid_edge_def ProcCFG.valid_node_def)
    show ?case
    proof(cases n)
      case (Label l)
      with \<open>c \<turnstile> nx -IEdge (kind a)\<rightarrow>\<^sub>p nx'\<close> disj \<open>(px, nx) = sourcenode a\<close>[THEN sym]
        \<open>(px, nx') = targetnode a\<close>[THEN sym]
      have "l < #:c" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
        Proc_CFG_targetlabel_less_num_nodes)
      with \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(px, ins, outs, c) \<in> set procs\<close> 
        \<open>containsCall procs prog ps px\<close>
      obtain as as' where "wfp \<turnstile> (px,Entry) -as\<rightarrow>* (px,Label l)"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (px,Label l) -as'\<rightarrow>* (px,Exit)"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      with path path' show ?thesis using Label
        apply(rule_tac x="asx@as" in exI) apply(rule_tac x="as'@asx'" in exI)
        by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:ProcCFG.vp_def)
    next
      case Entry
      from EXpath path' have "CFG.valid_path' sourcenode targetnode kind 
        (valid_edge wfp) (get_return_edges wfp) (px,Entry) 
        ([((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]@asx') (Main, Exit)"
        apply(unfold ProcCFG.vp_def) apply(erule conjE) apply(rule conjI)
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:intra_kind_def)+
      with path Entry show ?thesis by simp blast
    next
      case Exit
      with path EXpath path' show ?thesis
        apply(rule_tac x="asx@[((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]" in exI)
        apply simp
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
          simp:ProcCFG.vp_def ProcCFG.intra_path_def intra_kind_def)
    qed
  next
    case (MainCall l px es rets nx' ins outs c)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with \<open>(Main, Label l) = sourcenode a\<close>[THEN sym] 
      have [simp]:"n = Label l" "p = Main" by simp_all
      with \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p nx'\<close> have "l < #:prog"
        by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
      with \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      thus ?thesis 
        by(fastforce intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    next
      assume "(p,n) = targetnode a"
      with \<open>(px, Entry) = targetnode a\<close>[THEN sym] 
      have [simp]:"n = Entry" "p = px" by simp_all
      from \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p nx'\<close>
      have "containsCall procs prog [] px" 
        by(rule Proc_CFG_Call_containsCall)
      with \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      obtain as' where Xpath:"CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (px,Exit) as' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)      
      from \<open>containsCall procs prog [] px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px, Exit)"
        by(fastforce intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]\<rightarrow>* (px,Exit)"
        by(fastforce intro:ProcCFG.path.intros 
          simp:valid_edge_def ProcCFG.valid_node_def)
      with Xpath have "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (px,Entry) 
        ([((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]@as') (Main,Exit)"
        apply(unfold ProcCFG.vp_def) apply(erule conjE) apply(rule conjI)
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:intra_kind_def)+
      with \<open>containsCall procs prog [] px\<close> \<open>Rep_wf_prog wfp = (prog,procs)\<close>
        \<open>(px, ins, outs, c) \<in> set procs\<close>
      show ?thesis by(fastforce elim:Entry_to_Entry_and_Exit_to_Exit)
    qed
  next
    case (ProcCall px ins outs c l p' es' rets' l' ins' outs' c' ps)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with \<open>(px, Label l) = sourcenode a\<close>[THEN sym] 
      have [simp]:"n = Label l" "p = px" by simp_all
      with \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close> have "l < #:c"
        by(fastforce intro:Proc_CFG_sourcelabel_less_num_nodes)
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>l < #:c\<close> 
        \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      obtain as as' where "wfp \<turnstile> (px,Label l) -as\<rightarrow>* (px,Exit)"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (px,Entry) -as'\<rightarrow>* (px,Label l)"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      moreover
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>containsCall procs prog ps px\<close>
        \<open>(px, ins, outs, c) \<in> set procs\<close> obtain asx asx' 
        where" CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
        and "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis 
        apply(rule_tac x="asx@as'" in exI) apply(rule_tac x="as@asx'" in exI)
        by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:ProcCFG.vp_def)
    next
      assume "(p,n) = targetnode a"
      with \<open>(p', Entry) = targetnode a\<close>[THEN sym] 
      have [simp]:"n = Entry" "p = p'" by simp_all
      from \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      have "containsCall procs prog (ps@[px]) p'"
        by(rule containsCall_in_proc)
      with \<open>(p', ins', outs', c') \<in> set procs\<close>
      have "prog,procs \<turnstile> (p', Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (p', Exit)"
        by(fastforce intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (p',Entry) -[((p',Entry),(\<lambda>s. False)\<^sub>\<surd>,(p',Exit))]\<rightarrow>* (p',Exit)"
        by(fastforce intro:ProcCFG.path.intros 
          simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>containsCall procs prog (ps@[px]) p'\<close>
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p',Entry)"
        and "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (p',Exit) as' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
        apply(rule_tac x="as" in exI)
        apply(rule_tac x="[((p',Entry),(\<lambda>s. False)\<^sub>\<surd>,(p',Exit))]@as'" in exI)
        apply(unfold ProcCFG.vp_def)
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:intra_kind_def)+
    qed
  next
    case (MainReturn l px es rets l' ins outs c)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with \<open>(px, Exit) = sourcenode a\<close>[THEN sym] 
      have [simp]:"n = Exit" "p = px" by simp_all
      from \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs prog [] px" by(rule Proc_CFG_Call_containsCall)
      with \<open>(px, ins, outs, c) \<in> set procs\<close>
      have "prog,procs \<turnstile> (px, Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (px, Exit)"
        by(fastforce intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (px,Entry) -[((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]\<rightarrow>* (px,Exit)"
        by(fastforce intro:ProcCFG.path.intros 
          simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
        \<open>containsCall procs prog [] px\<close>
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (px,Entry)"
        and "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (px,Exit) as' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
        apply(rule_tac x="as@[((px,Entry),(\<lambda>s. False)\<^sub>\<surd>,(px,Exit))]" in exI)
        apply(rule_tac x="as'" in exI)
        apply(unfold ProcCFG.vp_def)
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
          simp:intra_kind_def)+
    next
      assume "(p, n) = targetnode a"
      with \<open>(Main, Label l') = targetnode a\<close>[THEN sym] 
      have [simp]:"n = Label l'" "p = Main" by simp_all
      with \<open>prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^sub>p Label l'\<close> have "l' < #:prog"
        by(fastforce intro:Proc_CFG_targetlabel_less_num_nodes)
      with \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
      obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l')"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (Main,Label l') -as'\<rightarrow>* (Main,Exit)"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
      thus ?thesis 
        by(fastforce intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
    qed
  next
    case (ProcReturn px ins outs c l p' es' rets' l' ins' outs' c' ps)
    from disj show ?case
    proof
      assume "(p,n) = sourcenode a"
      with \<open>(p', Exit) = sourcenode a\<close>[THEN sym] 
      have [simp]:"n = Exit" "p = p'" by simp_all
      from \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close>
      have "containsCall procs c [] p'" by(rule Proc_CFG_Call_containsCall)
      with \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      have "containsCall procs prog (ps@[px]) p'"
        by(rule containsCall_in_proc)
      with \<open>(p', ins', outs', c') \<in> set procs\<close>
      have "prog,procs \<turnstile> (p', Entry) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (p', Exit)"
        by(fastforce intro:PCFG.Proc Proc_CFG_Entry_Exit)
      hence "wfp \<turnstile> (p',Entry) -[((p',Entry),(\<lambda>s. False)\<^sub>\<surd>,(p',Exit))]\<rightarrow>* (p',Exit)"
        by(fastforce intro:ProcCFG.path.intros 
          simp:valid_edge_def ProcCFG.valid_node_def)
      moreover
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(p', ins', outs', c') \<in> set procs\<close>
        \<open>containsCall procs prog (ps@[px]) p'\<close>
      obtain as as' where "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (Main,Entry) as (p',Entry)"
        and "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (p',Exit) as' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis
        apply(rule_tac x="as@[((p',Entry),(\<lambda>s. False)\<^sub>\<surd>,(p',Exit))]" in exI)
        apply(rule_tac x="as'" in exI)
        apply(unfold ProcCFG.vp_def)
        by(fastforce intro:ProcCFG.path_Append 
          ProcCFG.valid_path_same_level_path_Append ProcCFG.intras_same_level_path
          simp:intra_kind_def)+
    next
      assume "(p, n) = targetnode a"
      with \<open>(px, Label l') = targetnode a\<close>[THEN sym] 
      have [simp]:"n = Label l'" "p = px" by simp_all
      with \<open>c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^sub>p Label l'\<close> have "l' < #:c"
        by(fastforce intro:Proc_CFG_targetlabel_less_num_nodes)
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>l' < #:c\<close> 
        \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
      obtain as as' where "wfp \<turnstile> (px,Label l') -as\<rightarrow>* (px,Exit)"
        and "\<forall>a \<in> set as. intra_kind (kind a)"
        and "wfp \<turnstile> (px,Entry) -as'\<rightarrow>* (px,Label l')"
        and "\<forall>a \<in> set as'. intra_kind (kind a)"
        by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
      moreover
      from \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>containsCall procs prog ps px\<close>
        \<open>(px, ins, outs, c) \<in> set procs\<close> obtain asx asx' 
        where" CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
        and "CFG.valid_path' sourcenode targetnode kind
        (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
        by -(erule Entry_to_Entry_and_Exit_to_Exit)+
      ultimately show ?thesis 
        apply(rule_tac x="asx@as'" in exI) apply(rule_tac x="as@asx'" in exI)
        by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
          ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
          simp:ProcCFG.vp_def)
    qed
  next
    case (MainCallReturn nx px es rets nx')
    from \<open>prog \<turnstile> nx -CEdge (px, es, rets)\<rightarrow>\<^sub>p nx'\<close> disj
      \<open>(Main, nx) = sourcenode a\<close>[THEN sym] \<open>(Main, nx') = targetnode a\<close>[THEN sym]
    obtain l where [simp]:"n = Label l" "p = Main"
      by(fastforce dest:Proc_CFG_Call_Labels)
    from \<open>prog \<turnstile> nx -CEdge (px, es, rets)\<rightarrow>\<^sub>p nx'\<close> disj
      \<open>(Main, nx) = sourcenode a\<close>[THEN sym] \<open>(Main, nx') = targetnode a\<close>[THEN sym]
    have "l < #:prog" by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
      Proc_CFG_targetlabel_less_num_nodes)
    with \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
    obtain as as' where "wfp \<turnstile> (Main,Entry) -as\<rightarrow>* (Main,Label l)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      and "wfp \<turnstile> (Main,Label l) -as'\<rightarrow>* (Main,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Main)+
    thus ?thesis
      apply(rule_tac x="as" in exI) apply(rule_tac x="as'" in exI) apply simp
      by(fastforce intro:ProcCFG.intra_path_vp simp:ProcCFG.intra_path_def)
  next
    case (ProcCallReturn px ins outs c nx p' es' rets' nx' ps)
    from \<open>(px, ins, outs, c) \<in> set procs\<close> wf have [simp]:"px \<noteq> Main" by auto
    from \<open>c \<turnstile> nx -CEdge (p', es', rets')\<rightarrow>\<^sub>p nx'\<close> disj 
      \<open>(px, nx) = sourcenode a\<close>[THEN sym] \<open>(px, nx') = targetnode a\<close>[THEN sym]
    obtain l where [simp]:"n = Label l" "p = px"
      by(fastforce dest:Proc_CFG_Call_Labels)
    from \<open>c \<turnstile> nx -CEdge (p', es', rets')\<rightarrow>\<^sub>p nx'\<close> disj 
    \<open>(px, nx) = sourcenode a\<close>[THEN sym] \<open>(px, nx') = targetnode a\<close>[THEN sym]
    have "l < #:c"
      by(auto intro:Proc_CFG_sourcelabel_less_num_nodes
        Proc_CFG_targetlabel_less_num_nodes)
    with \<open>Rep_wf_prog wfp = (prog,procs)\<close> \<open>(px, ins, outs, c) \<in> set procs\<close> 
      \<open>containsCall procs prog ps px\<close>
    obtain as as' where "wfp \<turnstile> (px,Entry) -as\<rightarrow>* (px,Label l)"
      and "\<forall>a \<in> set as. intra_kind (kind a)"
      and "wfp \<turnstile> (px,Label l) -as'\<rightarrow>* (px,Exit)"
      and "\<forall>a \<in> set as'. intra_kind (kind a)"
      by -(erule Label_Proc_CFG_Entry_Exit_path_Proc)+
    moreover
    from \<open>Rep_wf_prog wfp = (prog,procs)\<close> 
      \<open>containsCall procs prog ps px\<close> \<open>(px, ins, outs, c) \<in> set procs\<close>
    obtain asx asx' where "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (Main,Entry) asx (px,Entry)"
      and "CFG.valid_path' sourcenode targetnode kind
      (valid_edge wfp) (get_return_edges wfp) (px,Exit) asx' (Main,Exit)"
      by -(erule Entry_to_Entry_and_Exit_to_Exit)+
    ultimately show ?thesis
      apply(rule_tac x="asx@as" in exI) apply(rule_tac x="as'@asx'" in exI)
      by(auto intro:ProcCFG.path_Append ProcCFG.valid_path_same_level_path_Append
        ProcCFG.same_level_path_valid_path_Append ProcCFG.intras_same_level_path
        simp:ProcCFG.vp_def)
  qed
qed



subsection \<open>Instantiating the \<open>Postdomination\<close> locale\<close>

interpretation ProcPostdomination:
  Postdomination sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
  for wfp
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastforce simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastforce intro:wf_wf_prog)
  show "Postdomination sourcenode targetnode kind (valid_edge wfp)
    (Main, Entry) get_proc (get_return_edges wfp) (lift_procs wfp) Main (Main, Exit)"
  proof
    fix m
    assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) m"
    then obtain a where "valid_edge wfp a"
      and "m = sourcenode a \<or> m = targetnode a"
      by(fastforce simp:ProcCFG.valid_node_def)
    obtain p n where [simp]:"m = (p,n)" by(cases m) auto
    from \<open>valid_edge wfp a\<close> \<open>m = sourcenode a \<or> m = targetnode a\<close> 
      \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    show "\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) (Main, Entry) as m"
      by(auto dest!:edge_valid_paths simp:valid_edge_def)
  next
    fix m
    assume "CFG.valid_node sourcenode targetnode (valid_edge wfp) m"
    then obtain a where "valid_edge wfp a"
      and "m = sourcenode a \<or> m = targetnode a"
      by(fastforce simp:ProcCFG.valid_node_def)
    obtain p n where [simp]:"m = (p,n)" by(cases m) auto
    from \<open>valid_edge wfp a\<close> \<open>m = sourcenode a \<or> m = targetnode a\<close> 
      \<open>Rep_wf_prog wfp = (prog,procs)\<close>
    show "\<exists>as. CFG.valid_path' sourcenode targetnode kind (valid_edge wfp)
      (get_return_edges wfp) m as (Main,Exit)"
      by(auto dest!:edge_valid_paths simp:valid_edge_def)
  next
    fix n n'
    assume mex1:"CFGExit.method_exit sourcenode kind (valid_edge wfp) (Main,Exit) n"
      and mex2:"CFGExit.method_exit sourcenode kind (valid_edge wfp) (Main,Exit) n'"
      and "get_proc n = get_proc n'"
    from mex1 
    have "n = (Main,Exit) \<or> (\<exists>a Q p f. n = sourcenode a \<and> valid_edge wfp a \<and> 
      kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)" by(simp add:ProcCFGExit.method_exit_def)
    thus "n = n'"
    proof
      assume "n = (Main,Exit)"
      from mex2 have "n' = (Main,Exit) \<or> (\<exists>a Q p f. n' = sourcenode a \<and> 
        valid_edge wfp a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)" 
        by(simp add:ProcCFGExit.method_exit_def)
      thus ?thesis
      proof
        assume "n' = (Main,Exit)"
        with \<open>n = (Main,Exit)\<close> show ?thesis by simp
      next
        assume "\<exists>a Q p f. n' = sourcenode a \<and> 
          valid_edge wfp a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        then obtain a Q p f where "n' = sourcenode a"
          and "valid_edge wfp a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by blast
        from \<open>valid_edge wfp a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have "get_proc (sourcenode a) = p" by(rule ProcCFG.get_proc_return)
        with \<open>get_proc n = get_proc n'\<close> \<open>n = (Main,Exit)\<close> \<open>n' = sourcenode a\<close>
        have "get_proc (Main,Exit) = p" by simp
        hence "p = Main" by simp
        with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with \<open>valid_edge wfp a\<close> have False by(rule ProcCFG.Main_no_return_source)
        thus ?thesis by simp
      qed
    next
      assume "\<exists>a Q p f. n = sourcenode a \<and> 
        valid_edge wfp a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      then obtain a Q p f where "n = sourcenode a"
        and "valid_edge wfp a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by blast
      from \<open>valid_edge wfp a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      have "get_proc (sourcenode a) = p" by(rule ProcCFG.get_proc_return)
      from mex2 have "n' = (Main,Exit) \<or> (\<exists>a Q p f. n' = sourcenode a \<and> 
        valid_edge wfp a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)" 
        by(simp add:ProcCFGExit.method_exit_def)
      thus ?thesis
      proof
        assume "n' = (Main,Exit)"
        from \<open>get_proc (sourcenode a) = p\<close> \<open>get_proc n = get_proc n'\<close>
          \<open>n' = (Main,Exit)\<close> \<open>n = sourcenode a\<close>
        have "get_proc (Main,Exit) = p" by simp
        hence "p = Main" by simp
        with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with \<open>valid_edge wfp a\<close> have False by(rule ProcCFG.Main_no_return_source)
        thus ?thesis by simp
      next
        assume "\<exists>a Q p f. n' = sourcenode a \<and> 
          valid_edge wfp a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        then obtain a' Q' p' f' where "n' = sourcenode a'"
          and "valid_edge wfp a'" and "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" by blast
        from \<open>valid_edge wfp a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
        have "get_proc (sourcenode a') = p'" by(rule ProcCFG.get_proc_return)
        with \<open>get_proc n = get_proc n'\<close> \<open>get_proc (sourcenode a) = p\<close>
          \<open>n = sourcenode a\<close> \<open>n' = sourcenode a'\<close>
        have "p' = p" by simp
        from \<open>valid_edge wfp a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have "sourcenode a = (p,Exit)" by(auto elim:PCFG.cases simp:valid_edge_def)
        from \<open>valid_edge wfp a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
        have "sourcenode a' = (p',Exit)" by(auto elim:PCFG.cases simp:valid_edge_def)
        with \<open>n = sourcenode a\<close> \<open>n' = sourcenode a'\<close> \<open>p' = p\<close>
          \<open>sourcenode a = (p,Exit)\<close> show ?thesis by simp
      qed
    qed
  qed
qed


end
