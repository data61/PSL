(*  Title:       Conflict analysis/Normalized Paths
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Normalized Paths"
theory Normalization
imports Main ThreadTracking Semantics ConsInterleave
begin
text_raw \<open>\label{thy:Normalization}\<close>

text \<open>
  The idea of normalized paths is to consider particular schedules only. While the original semantics allows a context switch to occur after every single step, we now define a semantics that allows context switches only before
  non-returning calls or after a thread has reached its final stack. We then show that this semantics is able to reach the same set of configurations as the original semantics.
\<close>

subsection "Semantic properties of restricted flowgraphs"
text_raw \<open>\label{sec:Normalization:eflowgraph}\<close>
text \<open>
  It makes the formalization smoother, if we assume that every thread's execution begins with a non-returning call. For this purpose, we defined syntactic restrictions on flowgraphs already 
  (cf. Section~\ref{sec:Flowgraph:extra_asm}). We now show that these restrictions have the desired semantic effect.\<close>  

\<comment> \<open>Procedures with isolated return nodes will never return\<close>
lemma (in eflowgraph) iso_ret_no_ret: "!!u c. \<lbrakk> 
    isolated_ret fg p; 
    proc_of fg u = p; 
    u \<noteq> return fg p; 
    (([u],c),w,([return fg p'],c'))\<in>trcl (trss fg) 
  \<rbrakk> \<Longrightarrow> False"
proof (induct w rule: length_compl_induct)
  case Nil thus ?case by auto 
next
  case (Cons e w) note IHP=this
  then obtain sh ch where SPLIT1: "(([u],c),e,(sh,ch))\<in>trss fg" and SPLIT2: "((sh,ch),w,([return fg p'],c'))\<in>trcl (trss fg)" by (fast dest: trcl_uncons)
  show ?case proof (cases e)
    case LRet with SPLIT1 IHP(3,4) show False by (auto elim!: trss.cases)
  next
    case LBase with SPLIT1 IHP(2,3) obtain v where A: "sh=[v]" "proc_of fg v = p" "v\<noteq>return fg p" by (force elim!: trss.cases simp add: edges_part isolated_ret_def)
    with IHP SPLIT2 show False by auto
  next
    case (LSpawn q) with SPLIT1 IHP(2,3) obtain v where A: "sh=[v]" "proc_of fg v = p" "v\<noteq>return fg p" by (force elim!: trss.cases simp add: edges_part isolated_ret_def)
    with IHP SPLIT2 show False by auto
  next
    case (LCall q) with SPLIT1 IHP(2,3) obtain uh where A: "sh=entry fg q#[uh]" "proc_of fg uh = p" "uh\<noteq>return fg p" by (force elim!: trss.cases simp add: edges_part isolated_ret_def)
    with SPLIT2 have B: "((entry fg q#[uh],ch),w,([return fg p'],c'))\<in>trcl (trss fg)" by simp
    from trss_return_cases[OF B] obtain w1 w2 ct where C: "w=w1@w2" "length w2 \<le> length w" "(([entry fg q],ch),w1,([],ct))\<in>trcl (trss fg)" "(([uh],ct),w2,([return fg p'],c'))\<in>trcl (trss fg)" by (auto)
    from IHP(1)[OF C(2) IHP(2) A(2,3) C(4)] show False .
  qed
qed

\<comment> \<open>The first step of an initial procedure is a call\<close>  
lemma (in eflowgraph) initial_starts_with_call: "
  \<lbrakk> (([entry fg p],c),e,(s',c'))\<in>trss fg; initialproc fg p \<rbrakk> 
    \<Longrightarrow> \<exists>p'. e=LCall p' \<and> isolated_ret fg p'"
  by (auto elim!: trss.cases dest: initial_call_no_ret initial_no_ret entry_return_same_proc)

\<comment> \<open>There are no same-level paths starting from the entry node of an initial procedure\<close>
lemma (in eflowgraph) no_sl_from_initial: 
  assumes A: "w\<noteq>[]" "initialproc fg p" 
             "(([entry fg p],c),w,([v],c'))\<in>trcl (trss fg)" 
  shows False
proof -
  from A obtain sh ch e w' where SPLIT: "(([entry fg p],c),e,(sh,ch))\<in>trss fg" "((sh,ch),w',([v],c'))\<in>trcl (trss fg)" by (cases w, simp, fast dest: trcl_uncons)
  from initial_starts_with_call[OF SPLIT(1) A(2)] obtain p' where CE: "e=LCall p'" "isolated_ret fg p'" by blast
  with SPLIT(1) obtain u' where "sh=entry fg p'#[u']" by (auto elim!: trss.cases)
  with SPLIT(2) have "((entry fg p'#[u'],ch),w',([v],c'))\<in>trcl (trss fg)" by simp
  then obtain wa ct where "(([entry fg p'],ch),wa,([],ct))\<in>trcl (trss fg)" by (erule_tac trss_return_cases, auto)
  then obtain wa' p'' where "(([entry fg p'],ch),wa',([return fg p''],ct))\<in>trcl (trss fg)" by (blast dest: trss_2empty_to_2return)
  from iso_ret_no_ret[OF CE(2) _ _ this] CE(2)[unfolded isolated_ret_def] show ?thesis by simp
qed
  
\<comment> \<open>There are no same-level or returning paths starting from the entry node of an initial procedure\<close>
lemma (in eflowgraph) no_retsl_from_initial: 
  assumes A: "w\<noteq>[]" 
             "initialproc fg p" 
             "(([entry fg p],c),w,(r',c'))\<in>trcl (trss fg)" 
             "length r' \<le> 1" 
  shows False
proof (cases r')
  case Nil with A(3) have "(([entry fg p],c),w,([],c'))\<in>trcl (trss fg)" by simp
  from trss_2empty_to_2return[OF this, simplified] obtain w' q where B: "w=w'@[LRet]" "(([entry fg p], c), w', [return fg q], c') \<in> trcl (trss fg)" by (blast)
  show ?thesis proof (cases w')
    case Nil with B have "p=q" "entry fg p = return fg p" by (auto dest: trcl_empty_cons entry_return_same_proc)
    with A(2) initial_no_ret show False by blast
  next
    case Cons hence "w'\<noteq>[]" by simp 
    from no_sl_from_initial[OF this A(2) B(2)] show False .
  qed
next
  case (Cons u rr) with A(4) have "r'=[u]" by auto
  with no_sl_from_initial[OF A(1,2)] A(3) show False by auto
qed


subsection "Definition of normalized paths"
text \<open>
  In order to describe the restricted schedules, we define an operational semantics that performs an atomically scheduled sequence of steps in one step, called a {\em macrostep}. 
  Context switches may occur after macrosteps only. We call this the {\em normalized semantics} and a sequence of macrosteps a {\em normalized path}.  

  Since we ensured that every path starts with a non-returning call, we can define a macrostep as an initial call followed by a same-level path\footnote{Same-level paths are paths with balanced calls and returns. 
  The stack-level at the beginning of their execution is the same as at the end, and during the execution, the stack never falls below the initial level.} of the called procedure. This has the effect that context switches are
  either performed before a non-returning call (if the thread makes a further macrostep in the future) or after the thread has reached its final configuration. 

  As for the original semantics, we first define the normalized semantics on a single thread with a context and then use the theory developed in Section~\ref{thy:ThreadTracking} to derive interleaving semantics on multisets and 
  configurations with an explicit local thread (loc/env-semantics, cf. Section~\ref{sec:ThreadTracking:exp_local}). 
\<close>


inductive_set
  ntrs :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> 
             (('n list \<times> 'n conf) \<times> ('p,'ba) label list \<times> ('n list \<times> 'n conf)) set"
  for fg
  where
  \<comment> \<open>A macrostep transforms one thread by first calling a procedure and then doing a same-level path\<close>
  ntrs_step: "\<lbrakk>((u#r,ce),LCall p, (entry fg p # u' # r,ce))\<in>trss fg; 
               (([entry fg p],ce),w,([v],ce'))\<in>trcl (trss fg)\<rbrakk> \<Longrightarrow> 
             ((u#r,ce),LCall p#w,(v#u'#r,ce'))\<in>ntrs fg"


abbreviation ntr where "ntr fg == gtr (ntrs fg)"
abbreviation ntrp where "ntrp fg == gtrp (ntrs fg)"

interpretation ntrs: env_no_step "ntrs fg"
  apply (rule env_no_step.intro)
  apply (erule ntrs.cases)
  apply clarsimp
  apply (erule trss_c_cases)
  apply auto
  done

subsection "Representation property for reachable configurations"
text \<open>
  In this section, we show that a configuration is reachable if and only if it is reachable via a normalized path.
\<close>

text \<open>The first direction is to show that a normalized path is also a path. This follows from the definitions. Note that we first show that a single macrostep corresponds to a path and then
  generalize the result to sequences of macrosteps\<close>
lemma ntrs_is_trss_s: "((s,c),w,(s',c'))\<in>ntrs fg \<Longrightarrow> ((s,c),w,(s',c'))\<in>trcl (trss fg)" 
proof (erule ntrs.cases, auto)
  fix p r u u' v w
  assume A: "((u # r, c), LCall p, entry fg p # u' # r, c) \<in> trss fg" "(([entry fg p], c), w, [v], c') \<in> trcl (trss fg)"
  from trss_stack_comp[OF A(2), of "u'#r"] have "((entry fg p # u' # r, c), w, v # u' # r, c') \<in> trcl (trss fg)" by simp
  with A(1) show "((u # r, c), LCall p # w, v # u' # r, c') \<in> trcl (trss fg)" by auto
qed

lemma ntrs_is_trss: "((s,c),w,(s',c'))\<in>trcl (ntrs fg) 
  \<Longrightarrow> ((s,c),foldl (@) [] w,(s',c'))\<in>trcl (trss fg)" 
proof (induct rule: trcl_pair_induct)
  case empty thus ?case by simp
next
  case (cons s c e sh ch w s' c') note IHP=this
  from trcl_concat[OF ntrs_is_trss_s[OF IHP(1)] IHP(3)] foldl_conc_empty_eq[of e w] show ?case by simp
qed

lemma ntr_is_tr_s: "(c,w,c')\<in>ntr fg \<Longrightarrow> (c,w,c')\<in>trcl (tr fg)"
  by (erule gtrE) (auto dest: ntrs_is_trss_s intro: gtrI)
  
lemma ntr_is_tr: "(c,ww,c')\<in>trcl (ntr fg) \<Longrightarrow> (c,foldl (@) [] ww,c')\<in>trcl (tr fg)" 
proof (induct rule: trcl.induct)
  case empty thus ?case by auto
next
  case (cons c ee c' ww c'') note IHP=this
  from trcl_concat[OF ntr_is_tr_s[OF IHP(1)] IHP(3)] foldl_conc_empty_eq[of ee ww] show ?case by (auto)
qed
  

text \<open>
  The other direction requires to prove that for each path reaching a configuration there is also a normalized path reaching the same configuration. 
  We need an auxiliary lemma for this proof, that is a kind of append rule: {\em Given a normalized path reaching some configuration @{term c}, and a same level or returning path from some 
  stack in @{term c}, we can derive a normalized path to @{term c} modified according to the same-level path}. We cannot simply append the same-level or returning path
  as a macrostep, because it does not start with a non-returning call. Instead, we will have to append it to some macrostep in the normalized path, i.e. move it ,,left'' into the normalized
  path.
\<close>

  
text \<open>
  Intuitively, we can describe the concept of the proof as follows:
  Due to the restrictions we made on flowgraphs, a same-level or returning path cannot be the first steps on a thread. 
  Hence there is a last macrostep that was executed on the thread. When this macrostep was executed, all threads held less monitors then they do at the end of the execution, because
  the set of monitors held by every single thread is increasing during the execution of a normalized path. Thus we can append the same-level or returning path to the last macrostep
  on that thread. As a same-level or returning path does not allocate any monitors, the following macrosteps remain executable. If we have a same-level path, appending it to a macrostep
  yields a valid macrostep again and we are done. Appending a returning path to a macrostep yields a same-level path. In this case we inductively repeat our argument. 

  The actual proof is strictly inductive; it either appends the same-level path to the {\em last} macrostep or inductively repeats the argument.
\<close>
lemma (in eflowgraph) ntr_sl_move_left: "!!ce u r w r' ce'.  
  \<lbrakk> ({#[entry fg p]#},ww,{# u#r #}+ce)\<in>trcl (ntr fg); 
    (([u],ce),w,(r',ce'))\<in>trcl (trss fg); 
    initialproc fg p; 
    length r' \<le> 1; w\<noteq>[] 
  \<rbrakk> \<Longrightarrow> \<exists>ww'. ({#[entry fg p]#}, ww',{# r'@r #}+ce')\<in>trcl (ntr fg)"
proof (induct ww rule: rev_induct)
  case Nil note CC=this hence "u=entry fg p" by auto
  \<comment> \<open>If the normalized path is empty, we get a contradiction, because there is no same-level path from the initial configuration of a thread\<close>
  with CC(2) no_retsl_from_initial[OF CC(5,3) _ CC(4)] have False by blast
  thus ?case ..
next
  case (snoc ee ww) note IHP=this 
  \<comment> \<open>In the induction step, we extract the last macrostep\<close>
  then obtain ch where SPLIT: "({#[entry fg p]#},ww,ch)\<in>trcl (ntr fg)" "(ch,ee,{# u#r #}+ce)\<in>ntr fg" by (fast dest: trcl_rev_uncons) 
  \<comment> \<open>The last macrostep first executes a call and then a same-level path\<close>
  from SPLIT(2) obtain q wws uh rh ceh uh' vt cet where 
    STEPFMT: "ee=LCall q#wws" "ch=add_mset (uh#rh) ceh" "add_mset (u#r) ce = add_mset (vt#uh'#rh) cet" "((uh#rh,ceh),LCall q,(entry fg q#uh'#rh,ceh))\<in>trss fg" "(([entry fg q],ceh),wws,([vt],cet))\<in>trcl (trss fg)"
    by (auto elim!: gtrE ntrs.cases[simplified])
  \<comment> \<open>Make a case distinction whether the last step was executed on the same thread as the sl/ret-path or not\<close>
  from STEPFMT(3) show ?case proof (cases rule: mset_single_cases') 
    \<comment> \<open>If the sl/ret path was executed on the same thread as the last macrostep\<close>
    case loc note CASE=this hence C': "u=vt" "r=uh'#rh" "ce=cet" by auto
    \<comment> \<open>we append it to the last macrostep.\<close>
    with STEPFMT(5) IHP(3) have NEWPATH: "(([entry fg q],ceh),wws@w,(r',ce'))\<in>trcl (trss fg)" by (simp add: trcl_concat)
    \<comment> \<open>We then distinguish whether we appended a same-level or a returning path\<close>
    show ?thesis proof (cases r')
      \<comment> \<open>If we appended a same-level path\<close>
      case (Cons v') \<comment> \<open>Same-level path\<close> with IHP(5) have CC: "r'=[v']" by auto
      \<comment> \<open>The macrostep still ends with a same-level path\<close>
      with NEWPATH have "(([entry fg q],ceh),wws@w,([v'],ce'))\<in>trcl (trss fg)" by simp
      \<comment> \<open>and thus remains a valid macrostep\<close>
      from gtrI_s[OF ntrs_step[OF STEPFMT(4), simplified, OF this]] have "(add_mset (uh # rh) ceh, LCall q # wws@w, add_mset (v' # uh' # rh) ce') \<in> ntr fg" .
      \<comment> \<open>that we can append to the prefix of the normalized path to get our proposition\<close>
      with STEPFMT(2) SPLIT(1) CC C'(2) have "({#[entry fg p]#},ww@[LCall q#wws@w],{# r'@r #} + ce')\<in>trcl (ntr fg)" by (auto simp add: trcl_rev_cons)
      thus ?thesis by blast
    next
      \<comment> \<open>If we appended a returning path\<close>
      case Nil note CC=this
      \<comment> \<open>The macrostep now ends with a returning path, and thus gets a same-level path\<close>
      have NEWSL: "(([uh], ceh), LCall q # wws @ w, [uh'], ce') \<in> trcl (trss fg)" proof -
        from STEPFMT(4) have "(([uh],ceh),LCall q,(entry fg q#[uh'],ceh))\<in>trss fg" by (auto elim!: trss.cases intro: trss.intros)
        also from trss_stack_comp[OF NEWPATH] CC have "((entry fg q#[uh'],ceh),wws@w,([uh'],ce'))\<in>trcl (trss fg)" by auto
        finally show ?thesis .
      qed
      \<comment> \<open>Hence we can apply the induction hypothesis and get the proposition\<close>
      from IHP(1)[OF _ NEWSL] SPLIT STEPFMT(2) IHP(4) CC C'(2) show ?thesis by auto 
    qed
  next
    \<comment> \<open>If the sl/ret path was executed on a different thread than the last macrostep\<close>
    case (env cc) note CASE=this
    \<comment> \<open>we first look at the context after the last macrostep. It consists of the threads that already have been there and the threads that have been spawned by the last macrostep\<close>
    from STEPFMT(5) obtain cspt where CETFMT: "cet=cspt+ceh" "!!s. s \<in># cspt \<Longrightarrow> \<exists>p. s=[entry fg p] \<and> initialproc fg p" 
      by (unfold initialproc_def) (erule trss_c_cases, blast)
    \<comment> \<open>The spawned threads do not hold any monitors yet\<close>
    hence CSPT_NO_MON: "mon_c fg cspt = {}" by (simp add: c_of_initial_no_mon)
    \<comment> \<open>We now distinguish whether the sl/ret path is executed on a thread that was just spawned or on a thread that was already there\<close>
    from CASE(1) CETFMT(1) have "u#r \<in># cspt+ceh" by auto 
    thus ?thesis proof (cases rule: mset_un_cases[cases set]) 
      \<comment> \<open>The sl/ret path cannot have been executed on a freshly spawned thread due to the restrictions we made on the flowgraph\<close>
      case left \<comment> \<open>Thread was spawned\<close> with CETFMT obtain q where "u=entry fg q" "r=[]" "initialproc fg q" by auto
      with IHP(3,5,6) no_retsl_from_initial have False by blast 
      thus ?thesis ..
    next
      \<comment> \<open>Hence let's assume the sl/ret path is executed on a thread that was already there before the last macrostep\<close>
      case right note CC=this 
      \<comment> \<open>We can write the configuration before the last macrostep in a way that one sees the thread that executed the sl/ret path\<close>
      hence CEHFMT: "ceh={# u#r #}+(ceh-{# u#r #})" by auto
      have CHFMT: "ch = {# u#r #} + ({# uh#rh #}+(ceh-{# u#r #}))" proof -
        from CEHFMT STEPFMT(2) have "ch = {# uh#rh #} + ({# u#r #}+(ceh-{# u#r #}))" by simp
        thus ?thesis by (auto simp add: union_ac)
      qed
      \<comment> \<open>There are not more monitors than after the last macrostep\<close>
      have MON_CE: "mon_c fg ({# uh#rh #}+(ceh-{# u#r #})) \<subseteq> mon_c fg ce" proof -
        have "mon_n fg uh \<subseteq> mon_n fg uh'" using STEPFMT(4) by (auto elim!: trss.cases dest: mon_n_same_proc edges_part)
        moreover have "mon_c fg (ceh-{#u#r#}) \<subseteq> mon_c fg cc" proof -
          from CASE(3) CETFMT have "cc=(cspt+ceh)-{#u#r#}" by simp
          with CC have "cc = cspt+(ceh-{#u#r#})" by auto
          with CSPT_NO_MON show ?thesis by (auto simp add: mon_c_unconc)
        qed
        ultimately show ?thesis using CASE(2) by (auto simp add: mon_c_unconc)
      qed
      \<comment> \<open>The same-level path preserves the threads in its environment and the threads that it creates hold no monitors\<close>
      from IHP(3) obtain csp' where CE'FMT: "ce'=csp'+ce" "mon_c fg csp' = {}" by (-) (erule trss_c_cases, blast intro!: c_of_initial_no_mon)
      \<comment> \<open>We can execute the sl/ret-path also from the configuration before the last step\<close>
      from trss_xchange_context[OF _ MON_CE] IHP(3) CE'FMT have NSL: "(([u], {#uh # rh#} + (ceh - {#u # r#})), w, r', csp' + ({#uh # rh#} + (ceh - {#u # r#}))) \<in> trcl (trss fg)" by auto 
      \<comment> \<open>And with the induction hypothesis we get a normalized path\<close>
      from IHP(1)[OF _ NSL IHP(4,5,6)] SPLIT(1) CHFMT obtain ww' where NNPATH: "({#[entry fg p]#}, ww', {#r' @ r#} + (csp' + ({#uh # rh#} + (ceh - {#u # r#})))) \<in> trcl (ntr fg)" by blast
      \<comment> \<open>We now show that the last macrostep can also be executed from the new configuration, after the sl/ret path has been executed (on another thread)\<close>
      have "({#r' @ r#} + (csp' + ({#uh # rh#} + (ceh - {#u # r#}))), ee, {#vt # uh' # rh#} + (cspt + ({#r' @ r#} + (csp' + (ceh - {#u # r#}))))) \<in> ntr fg"
      proof -
        \<comment> \<open>This is because the sl/ret path has not allocated any monitors\<close>
        have MON_CEH: "mon_c fg ({#r' @ r#} + (csp' + (ceh - {#u # r#}))) \<subseteq> mon_c fg ceh" proof -
          from IHP(3,5) trss_bot_proc_const[of "[]" u ce w "[]" _ ce'] mon_n_same_proc have "mon_s fg r' \<subseteq> mon_n fg u" by (cases r') (simp, force)
          moreover from CEHFMT have "mon_c fg ceh = mon_c fg ({#u # r#} + (ceh - {#u # r#}))" by simp \<comment> \<open>Need to state this explicitly because of recursive simp rule @{thm CEHFMT}\<close>
          ultimately show ?thesis using CE'FMT(2) by (auto simp add: mon_c_unconc mon_s_unconc)
        qed
        \<comment> \<open>And we can reassemble the macrostep within the new context\<close>
        note trss_xchange_context_s[OF _ MON_CEH, where csp="{#}", simplified, OF STEPFMT(4)]
        moreover from trss_xchange_context[OF _ MON_CEH, of "[entry fg q]" wws "[vt]" cspt] STEPFMT(5) CETFMT(1) have 
          "(([entry fg q], {#r' @ r#} + (csp' + (ceh - {#u # r#}))), wws, [vt], cspt + ({#r' @ r#} + (csp' + (ceh - {#u # r#})))) \<in> trcl (trss fg)" by blast
        moreover note STEPFMT(1)
        ultimately have "((uh#rh,({#r' @ r#} + (csp' + (ceh - {#u # r#})))),ee,(vt#uh'#rh,cspt+({#r' @ r#} + (csp' + (ceh - {#u # r#})))))\<in>ntrs fg" by (auto intro: ntrs.intros)
        from gtrI_s[OF this] show ?thesis by (simp add: add_mset_commute)
      qed
      \<comment> \<open>Finally we append the last macrostep to the normalized paths we obtained by the induction hypothesis\<close>
      from trcl_rev_cons[OF NNPATH this] have "({#[entry fg p]#}, ww' @ [ee], {#vt # uh' # rh#} + (cspt + ({#r' @ r#} + (csp' + (ceh - {#u # r#}))))) \<in> trcl (ntr fg)" .
      \<comment> \<open>And show that we got the right configuration\<close>
      moreover from CC CETFMT CASE(3)[symmetric] CASE(2) CE'FMT(1) have "{#vt # uh' # rh#} + (cspt + ({#r' @ r#} + (csp' + (ceh - {#u # r#})))) = {# r'@r #}+ce'" by (simp add: union_ac)
      ultimately show ?thesis by auto
    qed
  qed
qed

text \<open>Finally we can prove: {\em Any reachable configuration can also be reached by a normalized path}.
  With @{thm [source] eflowgraph.ntr_sl_move_left} we can easily show this lemma
  With @{thm [source] eflowgraph.ntr_sl_move_left} we can easily show this   by induction on the reaching path. For the empty path, the proposition follows trivially.
  Else we consider the last step. If it is a call, we can execute it as a macrostep and get the proposition. Otherwise the last step is a same-level (Base, Spawn) or returning (Ret) path of length 1, and
  we can append it to the normalized path using @{thm [source] eflowgraph.ntr_sl_move_left}.
\<close>
lemma (in eflowgraph) normalize: "\<lbrakk> 
    (cstart,w,c')\<in>trcl (tr fg); 
    cstart={# [entry fg p] #}; 
    initialproc fg p \<rbrakk> 
  \<Longrightarrow> \<exists>w'. ({# [entry fg p] #},w',c')\<in>trcl (ntr fg)"
\<comment> \<open>The lemma is shown by induction on the reaching path\<close>
proof (induct rule: trcl_rev_induct) 
  \<comment> \<open>The empty case is trivial, as the empty path is also a valid normalized path\<close>
  case empty thus ?case by (auto intro: exI[of _ "[]"] ) 
next
  case (snoc cstart w c e c') note IHP=this
  \<comment> \<open>In the inductive case, we can assume that we have an already normalized path and need to append a last step\<close>
  then obtain w' where IHP': "({# [entry fg p] #},w',c)\<in>trcl (ntr fg)" "(c,e,c')\<in>tr fg" by blast
  \<comment> \<open>We make explicit the thread on that this last step was executed\<close>
  from gtr_find_thread[OF IHP'(2)] obtain s ce s' ce' where TSTEP: "c = add_mset s ce" "c' = add_mset s' ce'" "((s, ce), e, (s', ce')) \<in> trss fg" by blast 
  \<comment> \<open>The proof is done by a case distinction whether the last step was a call or not\<close>
  {
    \<comment> \<open>Last step was a procedure call\<close>
    fix q
    assume CASE: "e=LCall q" 
    \<comment> \<open>As it is the last step, the procedure call will not return and thus is a valid macrostep\<close>
    have "(c,LCall q # [], c')\<in>ntr fg" using TSTEP CASE by (auto elim!: trss.cases intro!: ntrs.intros gtrI_s trss.intros)
    \<comment> \<open>That can be appended to the initial normalized path\<close>
    from trcl_rev_cons[OF IHP'(1) this] have ?case by blast 
  } moreover {
    \<comment> \<open>Last step was no procedure call\<close>
    fix q a
    assume CASE: "e=LBase a \<or> e=LSpawn q \<or> e=LRet" 
    \<comment> \<open>Then it is a same-level or returning path\<close>
    with TSTEP(3) obtain u r r' where SLR: "s=u#r" "s'=r'@r" "length r'\<le>1" "(([u],ce),[e],(r',ce'))\<in>trcl (trss fg)" by (force elim!: trss.cases intro!: trss.intros) 
     \<comment> \<open>That can be appended to the normalized path using the @{thm ntr_sl_move_left} - lemma\<close>
    from ntr_sl_move_left[OF _ SLR(4) IHP(5) SLR(3)] IHP'(1) TSTEP(1) SLR(1) obtain ww' where "({#[entry fg p]#}, ww', {#r' @ r#} + ce') \<in> trcl (ntr fg)" by auto
    with SLR(2) TSTEP(2) have ?case by auto
  } ultimately show ?case by (cases e, auto)
qed
 
text \<open>As the main result of this section we get: {\em A configuration is reachable if and only if it is also reachable via a normalized path}:\<close>
theorem (in eflowgraph) ntr_repr:
  "    (\<exists>w. ({#[entry fg (main fg)]#},w,c)\<in>trcl (tr fg)) 
   \<longleftrightarrow> (\<exists>w. ({#[entry fg (main fg)]#},w,c)\<in>trcl (ntr fg))"
  by (auto simp add: initialproc_def intro!: normalize ntr_is_tr)

subsection \<open>Properties of normalized path\<close>

text \<open>Like a usual path, also a macrostep modifies one thread, spawns some threads and preserves the state of all the other threads. The spawned threads do not make any steps, thus they stay in their initial configurations.\<close>
lemma ntrs_c_cases_s[cases set]: "\<lbrakk> 
    ((s,c),w,(s',c'))\<in>ntrs fg; 
    !!csp. \<lbrakk> c'=csp+c; !!s. s \<in># csp \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> 
                                         (u,Spawn p,v)\<in>edges fg \<and> 
                                         initialproc fg p 
           \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (auto dest!: ntrs_is_trss_s elim!: trss_c_cases)

lemma ntrs_c_cases[cases set]: "\<lbrakk> 
    ((s,c),ww,(s',c'))\<in>trcl (ntrs fg); 
    !!csp. \<lbrakk> c'=csp+c; !!s. s \<in># csp \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> 
                                         (u,Spawn p,v)\<in>edges fg \<and> 
                                         initialproc fg p 
           \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (auto dest!: ntrs_is_trss elim!: trss_c_cases)

subsubsection \<open>Validity\<close>
text \<open>Like usual paths, also normalized paths preserve validity of the configurations.\<close>
lemmas (in flowgraph) ntrs_valid_preserve_s = trss_valid_preserve[OF ntrs_is_trss_s]
lemmas (in flowgraph) ntr_valid_preserve_s = tr_valid_preserve[OF ntr_is_tr_s]
lemmas (in flowgraph) ntrs_valid_preserve = trss_valid_preserve[OF ntrs_is_trss]
lemmas (in flowgraph) ntr_valid_preserve = tr_valid_preserve[OF ntr_is_tr]
lemma (in flowgraph) ntrp_valid_preserve_s: 
  assumes A: "((s,c),e,(s',c'))\<in>ntrp fg" 
  and V: "valid fg (add_mset s c)" 
  shows "valid fg (add_mset s' c')"
  using ntr_valid_preserve_s[OF gtrp2gtr_s[OF A] V] by assumption 
lemma (in flowgraph) ntrp_valid_preserve: 
  assumes A: "((s,c),e,(s',c'))\<in>trcl (ntrp fg)" 
  and V: "valid fg (add_mset s c)" 
  shows "valid fg (add_mset s' c')"
  using ntr_valid_preserve[OF gtrp2gtr[OF A] V] by assumption 

subsubsection \<open>Monitors\<close>
text \<open>The following defines the set of monitors used by a normalized path and shows its basic properties:\<close>
definition 
  "mon_ww fg ww == foldl (\<union>) {} (map (mon_w fg) ww)"

definition 
  "mon_loc fg ww == mon_ww fg (map le_rem_s (loc ww))"

definition 
  "mon_env fg ww == mon_ww fg (map le_rem_s (env ww))"

lemma mon_ww_empty[simp]: "mon_ww fg [] = {}"
  by (unfold mon_ww_def, auto)
lemma mon_ww_uncons[simp]: 
  "mon_ww fg (ee#ww) = mon_w fg ee \<union> mon_ww fg ww"
  by (unfold mon_ww_def, auto simp add: foldl_un_empty_eq[of "mon_w fg ee"])
lemma mon_ww_unconc: 
  "mon_ww fg (ww1@ww2) = mon_ww fg ww1 \<union> mon_ww fg ww2"
  by (induct ww1) auto

lemma mon_env_empty[simp]: "mon_env fg [] = {}"
  by (unfold mon_env_def) auto
lemma mon_env_single[simp]: 
  "mon_env fg [e] = (case e of LOC a \<Rightarrow> {} | ENV a \<Rightarrow> mon_w fg a)"
  by (unfold mon_env_def) (auto split: el_step.split)
lemma mon_env_uncons[simp]: 
  "mon_env fg (e#w) 
   = (case e of LOC a \<Rightarrow> {} | ENV a \<Rightarrow> mon_w fg a) \<union> mon_env fg w"
  by (unfold mon_env_def) (auto split: el_step.split)
lemma mon_env_unconc: 
  "mon_env fg (w1@w2) = mon_env fg w1 \<union> mon_env fg w2"
  by (unfold mon_env_def) (auto simp add: mon_ww_unconc)

lemma mon_loc_empty[simp]: "mon_loc fg [] = {}"
  by (unfold mon_loc_def) auto
lemma mon_loc_single[simp]: 
  "mon_loc fg [e] = (case e of ENV a \<Rightarrow> {} | LOC a \<Rightarrow> mon_w fg a)"
  by (unfold mon_loc_def) (auto split: el_step.split)
lemma mon_loc_uncons[simp]: 
  "mon_loc fg (e#w) 
  = (case e of ENV a \<Rightarrow> {} | LOC a \<Rightarrow> mon_w fg a) \<union> mon_loc fg w"
  by (unfold mon_loc_def) (auto split: el_step.split)
lemma mon_loc_unconc: 
  "mon_loc fg (w1@w2) = mon_loc fg w1 \<union> mon_loc fg w2"
  by (unfold mon_loc_def) (auto simp add: mon_ww_unconc)


lemma mon_ww_of_foldl[simp]: "mon_w fg (foldl (@) [] ww) = mon_ww fg ww"
  apply (induct ww)
  apply (unfold mon_ww_def) 
  apply simp
  apply simp
  apply (subst foldl_conc_empty_eq, subst foldl_un_empty_eq)
  apply (simp add: mon_w_unconc)
done

lemma mon_ww_ileq: "w\<preceq>w' \<Longrightarrow> mon_ww fg w \<subseteq> mon_ww fg w'"
  by (induct rule: less_eq_list_induct) auto

  (* TODO: Find some general statement about the property that monitors are computed element-wise and pslit this lemma and move the essential part to ConsInterleave.thy. Maybe the essential part is cil_set ?*)
lemma mon_ww_cil: 
  "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> mon_ww fg w = mon_ww fg w1 \<union> mon_ww fg w2"
  by (induct rule: cil_set_induct_fix\<alpha>) auto
lemma mon_loc_cil: 
  "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> mon_loc fg w = mon_loc fg w1 \<union> mon_loc fg w2"
  by (induct rule: cil_set_induct_fix\<alpha>) auto
lemma mon_env_cil: 
  "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> mon_env fg w = mon_env fg w1 \<union> mon_env fg w2"
  by (induct rule: cil_set_induct_fix\<alpha>) auto

lemma mon_ww_of_le_rem: 
  "mon_ww fg (map le_rem_s w) = mon_loc fg w \<union> mon_env fg w"
  by (induct w) (auto split: el_step.split)

lemma mon_env_ileq: "w\<preceq>w' \<Longrightarrow> mon_env fg w \<subseteq> mon_env fg w'"
  by (induct rule: less_eq_list_induct) auto
lemma mon_loc_ileq: "w\<preceq>w' \<Longrightarrow> mon_loc fg w \<subseteq> mon_loc fg w'"
  by (induct rule: less_eq_list_induct) auto

lemma mon_loc_map_loc[simp]: "mon_loc fg (map LOC w) = mon_ww fg w"
  by (unfold mon_loc_def) simp
lemma mon_env_map_env[simp]: "mon_env fg (map ENV w) = mon_ww fg w"
  by (unfold mon_env_def) simp
lemma mon_loc_map_env[simp]: "mon_loc fg (map ENV w) = {}"
  by (induct w) auto
lemma mon_env_map_loc[simp]: "mon_env fg (map LOC w) = {}"
  by (induct w) auto

\<comment> \<open>As monitors are syntactically bound to procedures, and each macrostep starts with a non-returning call, the set of monitors allocated during the execution of a normalized path is monotonically increasing\<close>
lemma (in flowgraph) ntrs_mon_increasing_s: "((s,c),e,(s',c'))\<in>ntrs fg 
  \<Longrightarrow> mon_s fg s \<subseteq> mon_s fg s' \<and> mon_c fg c = mon_c fg c'"
  apply (erule ntrs.cases)
  apply (auto simp add: trss_c_no_mon)
  apply (subgoal_tac "mon_n fg u = mon_n fg u'")
  apply (simp)
  apply (auto elim!: trss.cases dest!: mon_n_same_proc edges_part)
done

lemma (in flowgraph) ntr_mon_increasing_s: 
  "(c,ee,c')\<in>ntr fg \<Longrightarrow> mon_c fg c \<subseteq> mon_c fg c'"
  by (erule gtrE) (auto dest: ntrs_mon_increasing_s simp add: mon_c_unconc)

(* FIXME: Quick&dirty proof *)
lemma (in flowgraph) ntrp_mon_increasing_s: "((s,c),e,(s',c'))\<in>ntrp fg 
  \<Longrightarrow> mon_s fg s \<subseteq> mon_s fg s' \<and> mon_c fg c \<subseteq> mon_c fg c'"
  apply (erule gtrp.cases)
   apply (auto dest: ntrs_mon_increasing_s simp add: mon_c_unconc)[]
  apply (intro conjI)
   apply (auto dest: ntrs_mon_increasing_s simp add: mon_c_unconc)[]
  apply (auto dest: ntrs_mon_increasing_s simp add: mon_c_unconc)[]
  apply (erule ntrs_c_cases_s)
  apply (auto simp: mon_c_unconc)
  done

lemma (in flowgraph) ntrp_mon_increasing: "((s,c),e,(s',c'))\<in>trcl (ntrp fg) 
  \<Longrightarrow> mon_s fg s \<subseteq> mon_s fg s' \<and> mon_c fg c \<subseteq> mon_c fg c'"
  by (induct rule: trcl_rev_pair_induct) (auto dest!: ntrp_mon_increasing_s)

subsubsection \<open>Modifying the context\<close> 

lemmas (in flowgraph) ntrs_c_no_mon_s = trss_c_no_mon[OF ntrs_is_trss_s]
lemmas (in flowgraph) ntrs_c_no_mon = trss_c_no_mon[OF ntrs_is_trss]
  
text \<open>Also like a usual path, a normalized step must not use any monitors that are allocated by other threads\<close>
lemmas (in flowgraph) ntrs_mon_e_no_ctx = trss_mon_w_no_ctx[OF ntrs_is_trss_s]
lemma (in flowgraph) ntrs_mon_w_no_ctx: 
  assumes A: "((s,c),w,(s',c'))\<in>trcl (ntrs fg)" 
  shows "mon_ww fg w \<inter> mon_c fg c = {}" 
  using trss_mon_w_no_ctx[OF ntrs_is_trss[OF A]] by simp


lemma (in flowgraph) ntrp_mon_env_e_no_ctx: 
  "((s,c),ENV e,(s',c'))\<in>ntrp fg \<Longrightarrow> mon_w fg e \<inter> mon_s fg s = {}"
  by (auto elim!: gtrp.cases dest!: ntrs_mon_e_no_ctx simp add: mon_c_unconc)
lemma (in flowgraph) ntrp_mon_loc_e_no_ctx: 
  "((s,c),LOC e,(s',c'))\<in>ntrp fg \<Longrightarrow> mon_w fg e \<inter> mon_c fg c = {}"
  by (auto elim!: gtrp.cases dest!: ntrs_mon_e_no_ctx)

lemma (in flowgraph) ntrp_mon_env_w_no_ctx: 
  "((s,c),w,(s',c'))\<in>trcl (ntrp fg) \<Longrightarrow> mon_env fg w \<inter> mon_s fg s = {}" 
  by (induct rule: trcl_rev_pair_induct) (unfold mon_env_def, auto split: el_step.split dest!: ntrp_mon_env_e_no_ctx ntrp_mon_increasing simp add: mon_ww_unconc)

lemma (in flowgraph) ntrp_mon_loc_w_no_ctx: 
  "((s,c),w,(s',c'))\<in>trcl (ntrp fg) \<Longrightarrow> mon_loc fg w \<inter> mon_c fg c = {}" 
  by (induct rule: trcl_rev_pair_induct) (unfold mon_loc_def, auto split: el_step.split dest!: ntrp_mon_loc_e_no_ctx ntrp_mon_increasing simp add: mon_ww_unconc)

text \<open>
  The next lemmas are rules how to add or remove threads while preserving the executability of a path
\<close>

(* TODO: There are far too many {ntrs,ntrp}_{add,drop,replace,modify,xchange}_context - lemmas, try to give them a good sructure, find the most general cases and derive the other ones from these cases *)
lemma (in flowgraph) ntrs_modify_context_s: 
  assumes A: "((s,c),ee,(s',c'))\<in>ntrs fg" 
  and B: "mon_w fg ee \<inter> mon_c fg cn = {}" 
  shows "\<exists>csp. c'=csp+c \<and> mon_c fg csp={} \<and> ((s,cn),ee,(s',csp+cn))\<in>ntrs fg" 
proof -
  from A obtain p r u u' v w where S: "s=u#r" "ee=LCall p#w" "s'=v#u'#r" "((u#r,c),LCall p,(entry fg p#u'#r,c))\<in>trss fg" "(([entry fg p],c),w,([v],c'))\<in>trcl (trss fg)" by (blast elim!: ntrs.cases[simplified])
  with trss_modify_context_s[OF S(4)] B have "((u#r,cn),LCall p,(entry fg p#u'#r,cn))\<in>trss fg" by auto
  moreover from S trss_modify_context[OF S(5)] B obtain csp where "c'=csp+c" "mon_c fg csp = {}" "(([entry fg p],cn),w,([v],csp+cn))\<in>trcl (trss fg)" by auto
  ultimately show ?thesis using S by (auto intro!: ntrs_step)
qed
  
lemma (in flowgraph) ntrs_modify_context[rule_format]: "
  \<lbrakk>((s,c),w,(s',c'))\<in>trcl (ntrs fg)\<rbrakk> 
    \<Longrightarrow> \<forall>cn. mon_ww fg w \<inter> mon_c fg cn = {} 
        \<longrightarrow> (\<exists>csp. c'=csp+c \<and> mon_c fg csp = {} \<and> 
              ((s,cn),w,(s',csp+cn))\<in>trcl (ntrs fg))"
proof (induct rule: trcl_pair_induct)
  case empty thus ?case by simp 
next
  case (cons s c e sh ch w s' c') note IHP=this show ?case 
  proof (intro allI impI)
    fix cn
    assume MON: "mon_ww fg (e # w) \<inter> mon_c fg cn = {}"
    from ntrs_modify_context_s[OF IHP(1)] MON obtain csph where S1: "ch = csph + c" "mon_c fg csph={}" "((s, cn), e, sh, csph + cn) \<in> ntrs fg" by auto
    with MON have "mon_ww fg w \<inter> mon_c fg (csph+cn) = {}" by (auto simp add: mon_c_unconc)
    with IHP(3)[rule_format] obtain csp where S2: "c'=csp+ch" "mon_c fg csp={}" "((sh,csph+cn),w,(s',csp+(csph+cn)))\<in>trcl (ntrs fg)" by blast 
    from S1 S2 have "c'=(csp+csph)+c" "mon_c fg (csp+csph)={}" "((s,cn),e#w,(s',(csp+csph)+cn))\<in>trcl (ntrs fg)" by (auto simp add: union_assoc mon_c_unconc)
    thus "\<exists>csp. c' = csp + c \<and> mon_c fg csp = {} \<and> ((s, cn), e # w, s', csp + cn) \<in> trcl (ntrs fg)" by blast
  qed
qed
  
lemma ntrs_xchange_context_s: 
  assumes A: "((s,c),ee,(s',csp+c))\<in>ntrs fg" 
  and B: "mon_c fg cn \<subseteq> mon_c fg c" 
  shows "((s,cn),ee,(s',csp+cn))\<in>ntrs fg" 
proof -
  obtain p r u u' v w where S: "s=u#r" "ee=LCall p#w" "s'=v#u'#r" "((u#r,c),LCall p,(entry fg p#u'#r,c))\<in>trss fg" "(([entry fg p],c),w,([v],csp+c))\<in>trcl (trss fg)" 
  proof -
    from ntrs.cases[OF A, simplified] obtain ce ce' p r u u' v w where "s = u # r" "c = ce" "ee = LCall p # w" "s' = v # u' # r" "csp + ce = ce'" "((u # r, ce), LCall p, entry fg p # u' # r, ce) \<in> trss fg" 
      "(([entry fg p], ce), w, [v], ce') \<in> trcl (trss fg)" .
    hence "s=u#r" "ee=LCall p#w" "s'=v#u'#r" "((u#r,c),LCall p,(entry fg p#u'#r,c))\<in>trss fg" "(([entry fg p],c),w,([v],csp+c))\<in>trcl (trss fg)" by auto
    then show ?thesis ..
  qed
  from ntrs_step[simplified, OF trss_xchange_context_s[where csp="{#}", simplified, OF S(4) B] trss_xchange_context[OF S(5) B]] S show ?thesis by simp
qed

lemma ntrs_replace_context_s: 
  assumes A: "((s,c+cr),ee,(s',c'+cr))\<in>ntrs fg" 
  and B: "mon_c fg crn \<subseteq> mon_c fg cr" 
  shows "((s,c+crn),ee,(s',c'+crn))\<in>ntrs fg" 
proof -
  from ntrs_c_cases_s[OF A] obtain csp where G: "c'+cr = csp+(c+cr)" . hence F: "c'=csp+c" by (auto simp add: union_assoc[symmetric])
  from B have MON: "mon_c fg (c+crn) \<subseteq> mon_c fg (c+cr)" by (auto simp add: mon_c_unconc)
  from ntrs_xchange_context_s[OF _ MON] A G have "((s,c+crn),ee,(s',csp+(c+crn)))\<in>ntrs fg" by auto
  with F show ?thesis by (simp add: union_assoc)
qed

lemma (in flowgraph) ntrs_xchange_context: "!!s c c' cn. \<lbrakk>
    ((s,c),ww,(s',c'))\<in>trcl (ntrs fg); 
    mon_c fg cn \<subseteq> mon_c fg c
  \<rbrakk> \<Longrightarrow> \<exists>csp. 
    c'=csp+c \<and> ((s,cn),ww,(s',csp+cn))\<in>trcl (ntrs fg)"
proof (induct ww)
  case Nil note CASE=this
  thus ?case by (auto intro!: exI[of _ "{#}"])
next
  case (Cons ee ww) note IHP=this
  then obtain sh ch where SPLIT: "((s,c),ee,(sh,ch))\<in>ntrs fg" "((sh,ch),ww,(s',c'))\<in>trcl (ntrs fg)" by (fast dest: trcl_uncons)
  from ntrs_c_cases_s[OF SPLIT(1)] obtain csph where CHFMT: "ch=csph+c" "!!s. s \<in># csph \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> (u, Spawn p, v) \<in> edges fg \<and> initialproc fg p" by blast
  with ntrs_xchange_context_s SPLIT(1) IHP(3) have "((s,cn),ee,(sh,csph+cn))\<in>ntrs fg" by blast
  also
  from c_of_initial_no_mon CHFMT(2) have CSPH_NO_MON: "mon_c fg csph = {}" by auto
  with IHP(3) CHFMT have 1: "mon_c fg (csph+cn) \<subseteq> mon_c fg ch" by (auto simp add: mon_c_unconc)
  from IHP(1)[OF SPLIT(2) this] obtain csp where C'FMT: "c'=csp+ch" and SND: "((sh,csph+cn),ww,(s',csp+(csph+cn)))\<in>trcl (ntrs fg)" by blast
  note SND
  finally have "((s, cn), ee # ww, s', (csp + csph) + cn) \<in> trcl (ntrs fg)" by (simp add: union_assoc)
  moreover from CHFMT(1) C'FMT have "c'=(csp+csph)+c" by (simp add: union_assoc)
  ultimately show ?case by blast
qed


lemma (in flowgraph) ntrs_replace_context: 
  assumes A: "((s,c+cr),ww,(s',c'+cr))\<in>trcl (ntrs fg)" 
  and B: "mon_c fg crn \<subseteq> mon_c fg cr" 
  shows "((s,c+crn),ww,(s',c'+crn))\<in>trcl (ntrs fg)"
proof -
  from ntrs_c_cases[OF A] obtain csp where G: "c'+cr = csp+(c+cr)" . hence F: "c'=csp+c" by (auto simp add: union_assoc[symmetric])
  from B have MON: "mon_c fg (c+crn) \<subseteq> mon_c fg (c+cr)" by (auto simp add: mon_c_unconc)
  from ntrs_xchange_context[OF A MON] G have "((s,c+crn),ww,(s',csp+(c+crn)))\<in>trcl (ntrs fg)" by auto
  with F show ?thesis by (simp add: union_assoc)
qed

lemma (in flowgraph) ntr_add_context_s: 
  assumes A: "(c,e,c')\<in>ntr fg" 
  and B: "mon_w fg e \<inter> mon_c fg cn = {}" 
  shows "(c+cn,e,c'+cn)\<in>ntr fg"
proof -
  from gtrE[OF A] obtain s ce s' ce' where NTRS: "c = add_mset s ce" "c' = add_mset s' ce'" "((s, ce), e, s', ce') \<in> ntrs fg" .
  from ntrs_mon_e_no_ctx[OF NTRS(3)] B have M: "mon_w fg e \<inter> (mon_c fg (ce+cn)) = {}" by (auto simp add: mon_c_unconc)
  from ntrs_modify_context_s[OF NTRS(3) M] have "((s,ce+cn),e,(s',ce'+cn))\<in>ntrs fg" by (auto simp add: union_assoc)
  with NTRS show ?thesis by (auto simp add: union_assoc intro: gtrI_s)
qed
  
lemma (in flowgraph) ntr_add_context: 
  "\<lbrakk>(c,w,c')\<in>trcl (ntr fg); mon_ww fg w \<inter> mon_c fg cn = {}\<rbrakk> 
    \<Longrightarrow> (c+cn,w,c'+cn)\<in>trcl (ntr fg)"
  by (induct rule: trcl.induct) (simp, force dest: ntr_add_context_s)


lemma (in flowgraph) ntrs_add_context_s: 
  assumes A: "((s,c),e,(s',c'))\<in>ntrs fg" 
  and B: "mon_w fg e \<inter> mon_c fg cn = {}" 
  shows "((s,c+cn),e,(s',c'+cn))\<in>ntrs fg"
  using ntrs_mon_e_no_ctx[OF A] ntrs_modify_context_s[OF A, of "c+cn"] B by (force simp add: mon_c_unconc union_ac)

lemma (in flowgraph) ntrp_add_context_s: 
  "\<lbrakk> ((s,c),e,(s',c'))\<in>ntrp fg; mon_w fg (le_rem_s e) \<inter> mon_c fg cn = {} \<rbrakk> 
  \<Longrightarrow> ((s,c+cn),e,(s',c'+cn))\<in>ntrp fg"
  apply (erule gtrp.cases)
  by (auto dest: ntrs_add_context_s intro!: gtrp.intros)

lemma (in flowgraph) ntrp_add_context: "\<lbrakk> 
    ((s,c),w,(s',c'))\<in>trcl (ntrp fg); 
    mon_ww fg (map le_rem_s w) \<inter> mon_c fg cn = {} 
  \<rbrakk> \<Longrightarrow> ((s,c+cn),w,(s',c'+cn))\<in>trcl (ntrp fg)"
  by (induct rule: trcl_pair_induct) (simp, force dest: ntrp_add_context_s)



subsubsection \<open>Altering the local stack\<close>

lemma ntrs_stack_comp_s: 
  assumes A: "((s,c),ee,(s',c'))\<in>ntrs fg" 
  shows "((s@r,c),ee,(s'@r,c'))\<in>ntrs fg" 
  using A
  by (auto dest: trss_stack_comp trss_stack_comp_s elim!: ntrs.cases intro!: ntrs_step[simplified])

lemma ntrs_stack_comp: "((s,c),ww,(s',c'))\<in>trcl (ntrs fg) 
  \<Longrightarrow> ((s@r,c),ww,(s'@r,c'))\<in>trcl (ntrs fg)"
  by (induct rule: trcl_pair_induct) (auto intro!: trcl.cons[OF ntrs_stack_comp_s])

lemma (in flowgraph) ntrp_stack_comp_s: 
  assumes A: "((s,c),ee,(s',c'))\<in>ntrp fg" 
  and B: "mon_s fg r \<inter> mon_env fg [ee] = {}" 
  shows "((s@r,c),ee,(s'@r,c'))\<in>ntrp fg" 
  using A 
proof (cases rule: gtrp.cases)
  case gtrp_loc then obtain e where CASE: "ee=LOC e" "((s,c),e,(s',c'))\<in>ntrs fg" by auto
  hence "((s@r,c),e,(s'@r,c'))\<in>ntrs fg" by (blast dest: ntrs_stack_comp_s)
  with CASE(1) show ?thesis by (auto intro: gtrp.gtrp_loc)
next
  case gtrp_env then obtain sm ce sm' ce' e where CASE: "s'=s" "c={#sm#}+ce" "c'={#sm'#}+ce'" "ee=ENV e" "((sm,{#s#}+ce),e,(sm',{#s#}+ce'))\<in>ntrs fg" by auto
  from ntrs_modify_context_s[OF CASE(5), where cn="{#s@r#}+ce"] ntrs_mon_e_no_ctx[OF CASE(5)] B CASE(4) obtain csp where 
    ADD: "{#s#} + ce' = csp + ({#s#} + ce)" "mon_c fg csp = {}" "((sm, {#s @ r#} + ce), e, sm', csp + ({#s @ r#} + ce)) \<in> ntrs fg" by (auto simp add: mon_c_unconc mon_s_unconc)
  moreover from ADD(1) have "{#s#}+ce'={#s#}+(csp+ce)" by (simp add: union_ac) hence "ce'=csp+ce" by simp
  ultimately have "((sm, {#s @ r#} + ce), e, sm', ({#s @ r#} + ce')) \<in> ntrs fg" by (simp add: union_ac)
  with CASE(1,2,3,4) show ?thesis by (auto intro: gtrp.gtrp_env)
qed
  
lemma (in flowgraph) ntrp_stack_comp: 
  "\<lbrakk> ((s,c),ww,(s',c'))\<in>trcl (ntrp fg); mon_s fg r \<inter> mon_env fg ww = {} \<rbrakk> 
    \<Longrightarrow> ((s@r,c),ww,(s'@r,c'))\<in>trcl (ntrp fg)" 
  by (induct rule: trcl_pair_induct) (auto intro!: trcl.cons[OF ntrp_stack_comp_s])

lemma ntrs_stack_top_decomp_s: 
  assumes A: "((u#r,c),ee,(s',c'))\<in>ntrs fg" 
  and EX: "!!v u' p. \<lbrakk> 
      s'=v#u'#r; 
      (([u],c),ee,([v,u'],c'))\<in>ntrs fg; 
      (u,Call p,u')\<in>edges fg 
    \<rbrakk> \<Longrightarrow> P" 
  shows "P"
using A 
proof (cases rule: ntrs.cases)
  case ntrs_step then obtain u' v p w where CASE: "ee=LCall p#w" "s'=v#u'#r" "((u#r,c),LCall p,(entry fg p#u'#r,c))\<in>trss fg" "(([entry fg p],c),w,([v],c'))\<in>trcl (trss fg)" by (simp)
  from trss_stack_decomp_s[where s="[u]", simplified, OF CASE(3)] have SDC: "(([u], c), LCall p, ([entry fg p, u'], c)) \<in> trss fg" by auto
  with CASE(1,4) have "(([u],c),ee,([v,u'],c'))\<in>ntrs fg" by (auto intro!: ntrs.ntrs_step)
  moreover from SDC have "(u,Call p,u')\<in>edges fg" by (auto elim!: trss.cases)
  ultimately show ?thesis using CASE(2) by (blast intro!: EX)
qed

lemma ntrs_stack_decomp_s: 
  assumes A: "((u#s@r,c),ee,(s',c'))\<in>ntrs fg" 
  and EX: "!!v u' p. \<lbrakk> 
      s'=v#u'#s@r; 
      ((u#s,c),ee,(v#u'#s,c'))\<in>ntrs fg; 
      (u,Call p,u')\<in>edges fg
    \<rbrakk> \<Longrightarrow> P" 
  shows P
  apply (rule ntrs_stack_top_decomp_s[OF A])
  apply (rule EX)
  apply (auto dest: ntrs_stack_comp_s)
  done

lemma ntrs_stack_decomp: "!!u s r c P. \<lbrakk>
    ((u#s@r,c),ww,(s',c'))\<in>trcl (ntrs fg); 
    !!v rr. \<lbrakk>s'=v#rr@r; ((u#s,c),ww,(v#rr,c'))\<in>trcl (ntrs fg)\<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
proof (induct ww)
  case Nil thus ?case by fastforce 
next
  case (Cons e w) from Cons.prems show ?case proof (cases rule: trcl_pair_unconsE)
    case (split sh ch)
    from ntrs_stack_decomp_s[OF split(1)] obtain vh uh p where F: "sh = vh#uh#s@r" "((u#s, c), e, vh#uh#s, ch) \<in> ntrs fg" "(u, Call p, uh) \<in> edges fg" by blast
    from F(1) split(2) Cons.hyps[of vh "uh#s" r ch] obtain v' rr where S: "s'=v'#rr@r" "((vh#uh#s,ch),w,(v'#rr,c'))\<in>trcl (ntrs fg)" by auto
    from trcl.cons[OF F(2) S(2)] S(1) Cons.prems(2) show ?thesis by blast
  qed
qed
   
lemma ntrp_stack_decomp_s: 
  assumes A: "((u#s@r,c),ee,(s',c'))\<in>ntrp fg" 
  and EX: "!!v rr. \<lbrakk> s'=v#rr@r; ((u#s,c),ee,(v#rr,c'))\<in>ntrp fg \<rbrakk> \<Longrightarrow> P" 
  shows "P" 
  using A 
proof (cases rule: gtrp.cases)
  case gtrp_loc thus ?thesis using EX by (force elim!: ntrs_stack_decomp_s intro!: gtrp.intros)
next
  case gtrp_env then obtain e ss ss' ce ce' where S: "ee=ENV e" "s'=u#s@r" "c={#ss#}+ce" "c'={#ss'#}+ce'" "((ss,ce+{#u#s@r#}),e,(ss',ce'+{#u#s@r#}))\<in>ntrs fg" by (auto simp add: union_ac)
  from ntrs_replace_context_s[OF S(5), where crn="{#u#s#}"] have "((ss, {#u # s#} + ce), e, ss', {#u # s#} + ce') \<in> ntrs fg" by (auto simp add: mon_s_unconc union_ac)
  with S show P by (rule_tac EX) (auto intro: gtrp.gtrp_env)
qed

lemma ntrp_stack_decomp: "!!u s r c P. \<lbrakk>
    ((u#s@r,c),ww,(s',c'))\<in>trcl (ntrp fg); 
    !!v rr. \<lbrakk>s'=v#rr@r; ((u#s,c),ww,(v#rr,c'))\<in>trcl (ntrp fg)\<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
proof (induct ww)
  case Nil thus ?case by fastforce 
next
  case (Cons e w) from Cons.prems show ?case proof (cases rule: trcl_pair_unconsE)
    case (split sh ch)
    from ntrp_stack_decomp_s[OF split(1)] obtain vh rrh where F: "sh = vh#rrh@r" "((u#s, c), e, vh#rrh, ch) \<in> ntrp fg" by blast
    from F(1) split(2) Cons.hyps[of vh "rrh" r ch] obtain v' rr where S: "s'=v'#rr@r" "((vh#rrh,ch),w,(v'#rr,c'))\<in>trcl (ntrp fg)" by auto
    from trcl.cons[OF F(2) S(2)] S(1) Cons.prems(2) show ?thesis by blast
  qed
qed


subsection \<open>Relation to monitor consistent interleaving\<close>
text \<open>
  In this section, we describe the relation of the consistent interleaving operator (cf. Section~\ref{thy:ConsInterleave}) and the macrostep-semantics.
\<close>

subsubsection \<open>Abstraction function for normalized paths\<close>
text \<open>
  We first need to define an abstraction function that maps a macrostep on a pair of entered and passed monitors, as required by the \<open>\<otimes>\<^bsub>\<alpha>\<^esub>\<close>-operator: 
  
  A step on a normalized paths enters the monitors of the first called procedure and passes the monitors that occur in the following same-level path.
\<close>

definition 
  "\<alpha>n fg e == if e=[] then ({},{}) else (mon_e fg (hd e), mon_w fg (tl e))"
  (* TODO: We could also use a primrec here, this would generate simps- (and induct-) lemmas automatically *)
lemma \<alpha>n_simps[simp]: 
  "\<alpha>n fg [] = ({},{})" 
  "\<alpha>n fg (e#w) = (mon_e fg e, mon_w fg w)"
  by (unfold \<alpha>n_def, auto)

\<comment> \<open>We also need an abstraction function for normalized loc/env-paths\<close>
definition 
  "\<alpha>nl fg e == \<alpha>n fg (le_rem_s e)"

lemma \<alpha>nl_def': "\<alpha>nl fg == \<alpha>n fg \<circ> le_rem_s"
  by (rule eq_reflection[OF ext]) (auto simp add: \<alpha>nl_def)

\<comment> \<open>These are some ad-hoc simplifications, with the aim at converting @{term "\<alpha>nl"} back to @{term "\<alpha>n"}\<close>
lemma \<alpha>nl_simps[simp]: 
  "\<alpha>nl fg (ENV x) = \<alpha>n fg x" 
  "\<alpha>nl fg (LOC x) = \<alpha>n fg x"
  by (unfold \<alpha>nl_def, auto)
lemma \<alpha>nl_simps1[simp]:
  "(\<alpha>nl fg) \<circ> ENV = \<alpha>n fg"
  "(\<alpha>nl fg) \<circ> LOC = \<alpha>n fg"
  by (unfold \<alpha>nl_def' comp_def) (simp_all)
lemma \<alpha>n_\<alpha>nl: "(\<alpha>n fg) \<circ> le_rem_s = \<alpha>nl fg"
  unfolding \<alpha>nl_def'[symmetric] ..
lemma \<alpha>n_fst_snd[simp]: "fst (\<alpha>n fg w) \<union> snd (\<alpha>n fg w) = mon_w fg w"
  by (induct w) auto

lemma mon_pl_of_\<alpha>nl: "mon_pl (map (\<alpha>nl fg) w) = mon_loc fg w \<union> mon_env fg w"
  by (induct w) (auto split: el_step.split)

text \<open>We now derive specialized introduction lemmas for \<open>\<otimes>\<^bsub>\<alpha>n fg\<^esub>\<close>\<close>
lemma cil_\<alpha>n_cons_helper: "mon_pl (map (\<alpha>n fg) wb) = mon_ww fg wb"
  apply (unfold mon_pl_def)
  apply (induct wb)
  apply simp_all
  apply (unfold mon_ww_def)
  apply (subst foldl_un_empty_eq)
  apply (case_tac a)
  apply simp_all
  done

lemma cil_\<alpha>nl_cons_helper: 
  "mon_pl (map (\<alpha>nl fg) wb) = mon_ww fg (map le_rem_s wb)"
  by (simp add: \<alpha>n_\<alpha>nl cil_\<alpha>n_cons_helper[symmetric])
  
lemma cil_\<alpha>n_cons1: "\<lbrakk>w\<in>wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb; fst (\<alpha>n fg e) \<inter> mon_ww fg wb = {}\<rbrakk> 
  \<Longrightarrow> e#w \<in> e#wa \<otimes>\<^bsub>\<alpha>n fg\<^esub> wb" 
  apply (rule cil_cons1)
  apply assumption
  apply (subst cil_\<alpha>n_cons_helper)
  apply assumption
done

lemma cil_\<alpha>n_cons2: "\<lbrakk>w\<in>wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb; fst (\<alpha>n fg e) \<inter> mon_ww fg wa = {}\<rbrakk> 
  \<Longrightarrow> e#w \<in> wa \<otimes>\<^bsub>\<alpha>n fg\<^esub> e#wb" 
  apply (rule cil_cons2)
  apply assumption
  apply (subst cil_\<alpha>n_cons_helper)
  apply assumption
done

subsubsection "Monitors"
lemma (in flowgraph) ntrs_mon_s: 
  assumes A: "((s,c),e,(s',c'))\<in>ntrs fg" 
  shows "mon_s fg s' = mon_s fg s \<union> fst (\<alpha>n fg e)"
proof -
  from A obtain u r p u' w v where DET: "s=u#r" "e=LCall p#w" "((u#r,c),LCall p,(entry fg p#u'#r,c))\<in>trss fg" "(([entry fg p],c),w,([v],c'))\<in>trcl (trss fg)" "s'=v#u'#r" by (blast elim!: ntrs.cases[simplified])
  hence "mon_n fg u = mon_n fg u'" by (auto elim!: trss.cases dest: mon_n_same_proc edges_part)
  with trss_bot_proc_const[where s="[]" and s'="[]", simplified, OF DET(4)] DET(1,2,5) show ?thesis by (auto simp add: mon_n_def \<alpha>n_def)
qed

corollary (in flowgraph) ntrs_called_mon: 
  assumes A: "((s,c),e,(s',c'))\<in>ntrs fg" 
  shows "fst (\<alpha>n fg e) \<subseteq> mon_s fg s'" 
  using ntrs_mon_s[OF A] by auto

lemma (in flowgraph) ntr_mon_s: 
  "(c,e,c')\<in>ntr fg \<Longrightarrow> mon_c fg c' = mon_c fg c \<union> fst (\<alpha>n fg e)"
  by (erule gtrE) (auto simp add: mon_c_unconc ntrs_c_no_mon_s ntrs_mon_s)

lemma (in flowgraph) ntrp_mon_s: 
  assumes A: "((s,c),e,(s',c'))\<in>ntrp fg" 
  shows "mon_c fg (add_mset s' c') = mon_c fg (add_mset s c) \<union> fst (\<alpha>nl fg e)"
  using ntr_mon_s[OF gtrp2gtr_s[OF A]] by (unfold \<alpha>nl_def)


subsubsection \<open>Interleaving theorem\<close>
text \<open>In this section, we show that the consistent interleaving operator describes the intuition behind interleavability of normalized paths. We show:
  {\em Two paths are simultaneously executable if and only if they are consistently interleavable and the monitors of the initial configurations are compatible}
\<close>

text \<open>The split lemma splits an execution from a context of the form @{term "ca+cb"} into two interleavable executions from @{term ca} and @{term cb} respectively.
  While further down we prove this lemma for loc/env-path, which is more general but also more complicated, we start with the proof for paths of the multiset-semantics
  for illustrating the idea.
\<close>
lemma (in flowgraph) ntr_split: 
  "!!ca cb. \<lbrakk>(ca+cb,w,c')\<in>trcl (ntr fg); valid fg (ca+cb)\<rbrakk> \<Longrightarrow> 
  \<exists>ca' cb' wa wb. 
  c'=ca'+cb' \<and> 
  w\<in>(wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb) \<and> 
  mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {} \<and> 
  mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa) = {} \<and> 
  (ca,wa,ca')\<in>trcl (ntr fg) \<and> (cb,wb,cb')\<in>trcl (ntr fg)"
proof (induct w) \<comment> \<open>The proof is done by induction on the path\<close>
   \<comment> \<open>If the path is empty, the lemma is trivial\<close>
  case Nil thus ?case by - (rule exI[of _ "ca"], rule exI[of _ "cb"], intro exI[of _ "[]"], auto simp add: valid_unconc)
next
  case (Cons e w) note IHP=this
   \<comment> \<open>We split a non-empty paths after the first (macro) step\<close>
  then obtain ch where SPLIT: "(ca+cb,e,ch)\<in>ntr fg" "(ch,w,c')\<in>trcl (ntr fg)" by (fast dest: trcl_uncons)
  \<comment> \<open>Pick the stack that made the first step\<close>
  from gtrE[OF SPLIT(1)] obtain s ce sh ceh where NTRS: "ca+cb=add_mset s ce" "ch=add_mset sh ceh" "((s,ce),e,(sh,ceh))\<in>ntrs fg" . 
  \<comment> \<open>And separate the threads that where spawned during the first step from the ones that where already there\<close>
  then obtain csp where CEHFMT: "ceh=csp+ce" "mon_c fg csp={}" by (auto elim!: ntrs_c_cases_s intro!: c_of_initial_no_mon) 

  \<comment> \<open>Needed later: The first macrostep uses no monitors already owned by threads that where already there\<close>
  from ntrs_mon_e_no_ctx[OF NTRS(3)] have MONED: "mon_w fg e \<inter> mon_c fg ce = {}" by (auto simp add: mon_c_unconc) 
  \<comment> \<open>Needed later: The intermediate configuration is valid\<close>
  from ntr_valid_preserve_s[OF SPLIT(1) IHP(3)] have CHVALID: "valid fg ch" . 

  \<comment> \<open>We make a case distinction whether the thread that made the first step was in the left or right part of the initial configuration\<close>
  from NTRS(1)[symmetric] show ?case proof (cases rule: mset_unplusm_dist_cases) 
    \<comment> \<open>The first step was on a thread in the left part of the initial configuration\<close>
    case left note CASE=this 
    \<comment> \<open>We can write the intermediate configuration so that it is suited for the induction hypothesis\<close>
    with CEHFMT NTRS have CHFMT: "ch=({#sh#}+csp+(ca-{#s#}))+cb" by (simp add: union_ac) 
    \<comment> \<open>and by the induction hypothesis, we split the path from the intermediate configuration\<close>
    with IHP(1) SPLIT(2) CHVALID obtain ca' cb' wa wb where IHAPP: 
      "c'=ca'+cb'" 
      "w\<in>wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb" 
      "mon_c fg ({#sh#}+csp+(ca-{#s#})) \<inter> (mon_c fg cb \<union> mon_ww fg wb)={}" 
      "mon_c fg cb \<inter> (mon_c fg ({#sh#}+csp+(ca-{#s#})) \<union> mon_ww fg wa)={}" 
      "({#sh#}+csp+(ca-{#s#}),wa,ca')\<in>trcl (ntr fg)" 
      "(cb,wb,cb')\<in>trcl (ntr fg)" 
      by blast 
    moreover
    \<comment> \<open>It remains to show that we can execute the first step with the right part of the configuration removed\<close>
    have FIRSTSTEP: "(ca,e,{#sh#}+csp+(ca-{#s#}))\<in>ntr fg" 
    proof -
      from CASE(2) have "mon_c fg (ca-{#s#}) \<subseteq> mon_c fg ce" by (auto simp add: mon_c_unconc)
      with ntrs_xchange_context_s NTRS(3) CEHFMT CASE(2) have "((s,ca-{#s#}),e,(sh,csp+(ca-{#s#})))\<in>ntrs fg" by blast
      from gtrI_s[OF this] CASE(1) show ?thesis by (auto simp add: union_assoc)
    qed
    with IHAPP(5) have "(ca,e#wa,ca')\<in>trcl (ntr fg)" by simp
    moreover
    \<comment> \<open>and that we can prepend the first step to the interleaving\<close>
    have "e#w \<in> e#wa \<otimes>\<^bsub>\<alpha>n fg\<^esub> wb" 
    proof -
      from ntrs_called_mon[OF NTRS(3)] have "fst (\<alpha>n fg e) \<subseteq> mon_s fg sh" .
      with IHAPP(3) have "fst (\<alpha>n fg e) \<inter> mon_ww fg wb = {}" by (auto simp add: mon_c_unconc) 
      from cil_\<alpha>n_cons1[OF IHAPP(2) this] show ?thesis .
    qed
    moreover
    \<comment> \<open>and that the monitors of the initial context does not interfere\<close>
    have "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {}" "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg (e#wa)) = {}" 
    proof -
      from ntr_mon_increasing_s[OF FIRSTSTEP] IHAPP(3) show "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {}" by auto
      from MONED CASE have "mon_c fg cb \<inter> mon_w fg e = {}" by (auto simp add: mon_c_unconc)
      with ntr_mon_increasing_s[OF FIRSTSTEP] IHAPP(4) show "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg (e#wa)) = {}" by auto
    qed
    ultimately show ?thesis by blast
  next
    \<comment> \<open>The other case, that is if the first step was made on a thread in the right part of the configuration, is shown completely analogously\<close>
    case right note CASE=this 
    with CEHFMT NTRS have CHFMT: "ch=ca+({#sh#}+csp+(cb-{#s#}))" by (simp add: union_ac)
    with IHP(1) SPLIT(2) CHVALID obtain ca' cb' wa wb where IHAPP: "c'=ca'+cb'" "w\<in>wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb" "mon_c fg ca \<inter> (mon_c fg ({#sh#}+csp+(cb-{#s#})) \<union> mon_ww fg wb)={}" 
      "mon_c fg ({#sh#}+csp+(cb-{#s#})) \<inter> (mon_c fg ca \<union> mon_ww fg wa)={}" "(ca,wa,ca')\<in>trcl (ntr fg)" "({#sh#}+csp+(cb-{#s#}),wb,cb')\<in>trcl (ntr fg)" 
      by blast
    moreover
    have FIRSTSTEP: "(cb,e,{#sh#}+csp+(cb-{#s#}))\<in>ntr fg" proof -
      from CASE(2) have "mon_c fg (cb-{#s#}) \<subseteq> mon_c fg ce" by (auto simp add: mon_c_unconc)
      with ntrs_xchange_context_s NTRS(3) CEHFMT CASE(2) have "((s,cb-{#s#}),e,(sh,csp+(cb-{#s#})))\<in>ntrs fg" by blast
      from gtrI_s[OF this] CASE(1) show ?thesis by (auto simp add: union_assoc)
    qed
    with IHAPP(6) have PA: "(cb,e#wb,cb')\<in>trcl (ntr fg)" by simp
    moreover
    have "e#w \<in> wa \<otimes>\<^bsub>\<alpha>n fg\<^esub> e#wb" 
    proof -
      from ntrs_called_mon[OF NTRS(3)] have "fst (\<alpha>n fg e) \<subseteq> mon_s fg sh" .
      with IHAPP(4) have "fst (\<alpha>n fg e) \<inter> mon_ww fg wa = {}" by (auto simp add: mon_c_unconc) 
      from cil_\<alpha>n_cons2[OF IHAPP(2) this] show ?thesis  .
    qed
    moreover
    have "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa) = {}" "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg (e#wb)) = {}" 
    proof -
      from ntr_mon_increasing_s[OF FIRSTSTEP] IHAPP(4) show "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa) = {}" by auto
      from MONED CASE have "mon_c fg ca \<inter> mon_w fg e = {}" by (auto simp add: mon_c_unconc)
      with ntr_mon_increasing_s[OF FIRSTSTEP] IHAPP(3) show "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg (e#wb)) = {}" by auto
    qed
    ultimately show ?thesis by blast
  qed
qed

text \<open>The next lemma is a more general version of @{thm [source] flowgraph.ntr_split} for the semantics with a distinguished local thread. The proof follows exactly the same ideas, but is more complex.\<close>
lemma (in flowgraph) ntrp_split: "
  !!s c1 c2 s' c'. 
  \<lbrakk>((s,c1+c2),w,(s',c'))\<in>trcl (ntrp fg); valid fg ({#s#}+c1+c2)\<rbrakk> 
  \<Longrightarrow> \<exists>w1 w2 c1' c2'. 
        w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> (map ENV w2) \<and> 
        c'=c1'+c2' \<and> 
        ((s,c1),w1,(s',c1'))\<in>trcl (ntrp fg) \<and> 
        (c2,w2,c2')\<in>trcl (ntr fg) \<and> 
        mon_ww fg (map le_rem_s w1) \<inter> mon_c fg c2 = {} \<and> 
        mon_ww fg w2 \<inter> mon_c fg ({#s#}+c1) = {}"
proof (induct w)
  case Nil thus ?case by (auto intro: exI[of _ "[]"] exI[of _ "{#}"])
next
  case (Cons ee w) then obtain sh ch where SPLIT: "((s,c1+c2),ee,(sh,ch))\<in>ntrp fg" "((sh,ch),w,(s',c'))\<in>trcl (ntrp fg)" by (fast dest: trcl_uncons)
  from SPLIT(1) show ?case proof (cases rule: gtrp.cases)
    case gtrp_loc then obtain e where CASE: "ee=LOC e" "((s,c1+c2),e,(sh,ch))\<in>ntrs fg" by auto
    from ntrs_c_cases_s[OF CASE(2)] obtain csp where CHFMT: "ch=(csp+c1)+c2" "\<And>s. s \<in># csp \<Longrightarrow> \<exists>p u v. s = [entry fg p] \<and> (u, Spawn p, v) \<in> edges fg \<and> initialproc fg p" by (simp add: union_assoc, blast) 
    with c_of_initial_no_mon have CSPNOMON: "mon_c fg csp = {}" by auto
    from ntr_valid_preserve_s[OF gtrI_s, OF CASE(2)] Cons.prems(2) CHFMT have VALID: "valid fg ({#sh#}+(csp+c1)+c2)" by (simp add: union_ac)
    from Cons.hyps[OF _ VALID, of s' c'] CHFMT(1) SPLIT(2) obtain w1 w2 c1' c2' where IHAPP: "w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> (map ENV w2)" "c' = c1' + c2'" "((sh, csp + c1), w1, s', c1') \<in> trcl (ntrp fg)" 
      "(c2, w2, c2') \<in> trcl (ntr fg)" "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg c2 = {}" "mon_ww fg w2 \<inter> mon_c fg ({#sh#} + (csp + c1)) = {}" by blast
    have "ee#w \<in> ee#w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> (map ENV w2)" proof (rule cil_cons1)
      from ntrp_mon_env_w_no_ctx[OF SPLIT(2), unfolded mon_env_def] have "mon_ww fg (map le_rem_s (env w)) \<inter> mon_s fg sh = {}" .
      moreover have "mon_ww fg w2 \<subseteq> mon_ww fg (map le_rem_s (env w))" proof - (* TODO: This proof should be shorter and more straightforward *)
        from cil_subset_il IHAPP(1) ileq_interleave have "map ENV w2 \<preceq> w" by blast
        from le_list_filter[OF this] have "env (map ENV w2) \<preceq> env w" by (unfold env_def) blast
        hence "map ENV w2 \<preceq> env w" by (unfold env_def) simp
        from le_list_map[OF this, of le_rem_s] have "w2 \<preceq> map le_rem_s (env w)" by simp
        thus ?thesis by (rule mon_ww_ileq)
      qed
      ultimately have "mon_ww fg w2 \<inter> mon_s fg sh = {}" by blast
      with ntrs_mon_s[OF CASE(2)] CASE(1) show "fst (\<alpha>nl fg ee) \<inter> mon_pl (map (\<alpha>nl fg) (map ENV w2)) = {}" by (auto simp add: cil_\<alpha>n_cons_helper)
    qed (rule IHAPP(1))
    moreover
    have "((s,c1),ee#w1,(s',c1'))\<in>trcl (ntrp fg)" proof -
      from ntrs_xchange_context_s[of s "c1+c2" e sh "csp" fg "c1"] CASE(2) CHFMT(1) have "((s, c1), e, sh, csp + c1) \<in> ntrs fg" by (auto simp add: mon_c_unconc union_ac)
      with CASE(1) have "((s, c1), ee, sh, csp + c1) \<in> ntrp fg" by (auto intro: gtrp.gtrp_loc)
      also note IHAPP(3)
      finally show ?thesis .
    qed
    moreover from CASE(1) ntrs_mon_e_no_ctx[OF CASE(2)] IHAPP(5) have "mon_ww fg (map le_rem_s (ee#w1)) \<inter> mon_c fg c2 = {}" by (auto simp add: mon_c_unconc)
    moreover from ntrs_mon_increasing_s[OF CASE(2)] CHFMT(1) IHAPP(6) have "mon_ww fg w2 \<inter> mon_c fg ({#s#} + c1) = {}" by (auto simp add: mon_c_unconc)
    moreover note IHAPP(2,4)
    ultimately show ?thesis by blast
  next
    case gtrp_env then obtain e ss ce ssh ceh where CASE: "ee=ENV e" "c1+c2=add_mset ss ce" "sh=s" "ch=add_mset ssh ceh" "((ss,add_mset s ce),e,(ssh,add_mset s ceh))\<in>ntrs fg" by auto
    from ntrs_c_cases_s[OF CASE(5)] obtain csp where HFMT: "add_mset s ceh = csp + (add_mset s ce)" "\<And>s. s \<in># csp \<Longrightarrow> \<exists>p u v. s = [entry fg p] \<and> (u, Spawn p, v) \<in> edges fg \<and> initialproc fg p" by (blast)
    from union_left_cancel[of "{#s#}" ceh "csp+ce"] HFMT(1) have CEHFMT: "ceh=csp+ce" by (auto simp add: union_ac)
    from HFMT(2) have CHNOMON: "mon_c fg csp = {}" by (blast intro!: c_of_initial_no_mon)
    from CASE(2)[symmetric] show ?thesis proof (cases rule: mset_unplusm_dist_cases)
      \<comment> \<open>Made an env-step in @{term c1}, this is considered the ,,left'' part. Apply induction hypothesis with original(!) local thread and the spawned threads on the left side\<close>
      case left 
      with HFMT(1) CASE(4) CEHFMT have CHFMT': "ch=(csp+{#ssh#}+(c1-{#ss#})) + c2" by (simp add: union_ac)
      have VALID: "valid fg ({#s#} + (csp+{#ssh#}+(c1-{#ss#})) + c2)" proof -
        from ntr_valid_preserve_s[OF gtrI_s, OF CASE(5)] Cons.prems(2) CASE(2) have "valid fg ({#ssh#} + ({#s#} + ceh))" by (simp add: union_assoc add_mset_commute)
        with left CEHFMT show ?thesis by (auto simp add: union_ac add_mset_commute)
      qed
      from Cons.hyps[OF _ VALID,of s' c'] CHFMT' SPLIT(2) CASE(3) obtain w1 w2 c1' c2' where IHAPP: "w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV w2" "c' = c1' + c2'" 
        "((s, csp + {#ssh#} + (c1 - {#ss#})), w1, s', c1') \<in> trcl (ntrp fg)" "(c2, w2, c2') \<in> trcl (ntr fg)" 
        "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg c2 = {}" "mon_ww fg w2 \<inter> mon_c fg ({#s#} + (csp + {#ssh#} + (c1 - {#ss#}))) = {}" by blast
      have "ee # w \<in> (ee#w1) \<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV w2" proof (rule cil_cons1)
        from IHAPP(6) have "mon_ww fg w2 \<inter> mon_s fg ssh = {}" by (auto simp add: mon_c_unconc)
        moreover from ntrs_mon_s[OF CASE(5)] CASE(1) have "fst (\<alpha>nl fg ee) \<subseteq> mon_s fg ssh" by auto
        ultimately have "fst (\<alpha>nl fg ee) \<inter> mon_ww fg w2 = {}" by auto
        moreover have "mon_pl (map (\<alpha>nl fg) (map ENV w2)) = mon_ww fg w2" by (simp add: cil_\<alpha>n_cons_helper)
        ultimately show "fst (\<alpha>nl fg ee) \<inter> mon_pl (map (\<alpha>nl fg) (map ENV w2)) = {}" by auto
      qed (rule IHAPP(1))
      moreover 
      have SS: "((s,c1),ee,(s,csp + {#ssh#} + (c1 - {#ss#})))\<in>ntrp fg" proof -
        from left HFMT(1) have "{#s#}+ce={#s#}+(c1-{#ss#})+c2" "{#s#}+ceh = csp+({#s#}+(c1-{#ss#})+c2)" by (simp_all add: union_ac)
        with CASE(5) ntrs_xchange_context_s[of ss "{#s#}+(c1-{#ss#})+c2" e ssh csp fg "({#s#}+(c1-{#ss#}))"] have 
          "((ss, add_mset s (c1 - {#ss#})), e, ssh, add_mset s (csp+(c1 - {#ss#}))) \<in> ntrs fg" by (auto simp add: mon_c_unconc union_ac)
        from gtrp.gtrp_env[OF this] left(1)[symmetric] CASE(1) show ?thesis by (simp add: union_ac)
      qed
      from trcl.cons[OF this IHAPP(3)] have "((s, c1), ee # w1, s', c1') \<in> trcl (ntrp fg)" .
      moreover
      from ntrs_mon_e_no_ctx[OF CASE(5)] left CASE(1) IHAPP(5) have "mon_ww fg (map le_rem_s (ee#w1)) \<inter> mon_c fg c2 = {}" by (auto simp add: mon_c_unconc)
      moreover
      from ntrp_mon_increasing_s[OF SS] IHAPP(6) have "mon_ww fg w2 \<inter> mon_c fg ({#s#} + c1) = {}" by (auto simp add: mon_c_unconc)
      moreover note IHAPP(2,4)
      ultimately show ?thesis by blast
    next
      \<comment> \<open>Made an env-step in @{term c2}. This is considered the right part. Induction hypothesis is applied with original local thread and the spawned threads on the right side\<close> 
      case right 
      with HFMT(1) CASE(4) CEHFMT have CHFMT': "ch=c1 + (csp+{#ssh#}+(c2-{#ss#}))" by (simp add: union_ac)
      have VALID: "valid fg ({#s#} + c1 + ((csp+{#ssh#}+(c2-{#ss#}))))" proof -
        from ntr_valid_preserve_s[OF gtrI_s, OF CASE(5)] Cons.prems(2) CASE(2) have "valid fg ({#ssh#} + ({#s#} + ceh))" by  (auto simp add: union_ac add_mset_commute)
        with right CEHFMT show ?thesis by (auto simp add: union_ac add_mset_commute)
      qed
      from Cons.hyps[OF _ VALID,of s' c'] CHFMT' SPLIT(2) CASE(3) obtain w1 w2 c1' c2' where IHAPP: "w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV w2" "c' = c1' + c2'" 
        "((s, c1), w1, s', c1') \<in> trcl (ntrp fg)" "(csp + {#ssh#} + (c2 - {#ss#}), w2, c2') \<in> trcl (ntr fg)" 
        "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg (csp + {#ssh#} + (c2 - {#ss#})) = {}" "mon_ww fg w2 \<inter> mon_c fg ({#s#} + c1) = {}" by blast
      have "ee # w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV (e#w2)" proof (simp add: CASE(1), rule cil_cons2)
        from IHAPP(5) have "mon_ww fg (map le_rem_s w1) \<inter> mon_s fg ssh = {}" by (auto simp add: mon_c_unconc)
        moreover from ntrs_mon_s[OF CASE(5)] CASE(1) have "fst (\<alpha>nl fg ee) \<subseteq> mon_s fg ssh" by auto
        ultimately have "fst (\<alpha>nl fg ee) \<inter> mon_ww fg (map le_rem_s w1) = {}" by auto
        moreover have "mon_pl (map (\<alpha>nl fg) w1) = mon_ww fg (map le_rem_s w1)" by (unfold \<alpha>nl_def') (simp add: cil_\<alpha>n_cons_helper[symmetric])
        ultimately show "fst (\<alpha>nl fg (ENV e)) \<inter> mon_pl (map (\<alpha>nl fg) w1) = {}" using CASE(1) by auto
      qed (rule IHAPP(1))
      moreover 
      have SS: "(c2,e,csp + {#ssh#} + (c2 - {#ss#}))\<in>ntr fg" proof -
        from right HFMT(1) have "{#s#}+ce={#s#}+c1+(c2-{#ss#})" "{#s#}+ceh = csp+({#s#}+c1+(c2-{#ss#}))" by (simp_all add: union_ac)
        with CASE(5) ntrs_xchange_context_s[of ss "{#s#}+c1+(c2-{#ss#})" e ssh csp fg "c2-{#ss#}"] have 
          "((ss, (c2 - {#ss#})), e, ssh, csp+ (c2 - {#ss#})) \<in> ntrs fg" by (auto simp add: mon_c_unconc union_ac)
        from gtrI_s[OF this] right(1)[symmetric] show ?thesis by (simp add: union_ac)
      qed
      from trcl.cons[OF this IHAPP(4)] have "(c2, e # w2, c2') \<in> trcl (ntr fg)" .
      moreover
      from ntr_mon_increasing_s[OF SS] IHAPP(5) have "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg c2 = {}" by (auto simp add: mon_c_unconc)
      moreover 
      from ntrs_mon_e_no_ctx[OF CASE(5)] right IHAPP(6) have "mon_ww fg (e#w2) \<inter> mon_c fg ({#s#} + c1) = {}" by (auto simp add: mon_c_unconc)
      moreover note IHAPP(2,3)
      ultimately show ?thesis by blast
    qed
  qed
qed

\<comment> \<open>Just a check that @{thm [source] "flowgraph.ntrp_split"} is really a generalization of @{thm [source] "flowgraph.ntr_split"}:\<close>
lemma (in flowgraph) ntr_split': 
  assumes A: "(ca+cb,w,c')\<in>trcl (ntr fg)" 
  and VALID: "valid fg (ca+cb)" 
  shows "\<exists>ca' cb' wa wb. 
    c'=ca'+cb' \<and> 
    w\<in>(wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb) \<and> 
    mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {} \<and> 
    mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa) = {} \<and> 
    (ca,wa,ca')\<in>trcl (ntr fg) \<and> 
    (cb,wb,cb')\<in>trcl (ntr fg)"
using A VALID by(rule ntr_split)

text \<open>The unsplit lemma combines two interleavable executions. For illustration purposes, we first prove the less general version for multiset-configurations.
  The general version for loc/env-configurations is shown later.\<close>   
lemma (in flowgraph) ntr_unsplit: 
  assumes A: "w\<in>wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb" and 
  B: "(ca,wa,ca')\<in>trcl (ntr fg)" 
  "(cb,wb,cb')\<in>trcl (ntr fg)" 
  "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb)={}" 
  "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa)={}"
  shows "(ca+cb,w,ca'+cb')\<in>trcl (ntr fg)"
proof -
  \<comment> \<open>We have to generalize and rewrite the goal, in order to apply Isabelle's induction method\<close>
  from A have "\<forall>ca cb. (ca,wa,ca')\<in>trcl (ntr fg) \<and> (cb,wb,cb')\<in>trcl (ntr fg) \<and> mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb)={} \<and> mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa)={} \<longrightarrow> 
    (ca+cb,w,ca'+cb')\<in>trcl (ntr fg)"
  \<comment> \<open>We prove the generalized goal by induction over the structure of consistent interleaving\<close>
  proof (induct rule: cil_set_induct_fix\<alpha>) 
    \<comment> \<open>If both words are empty, the proposition is trivial\<close>
    case empty thus ?case by simp 
  next
    \<comment> \<open>The first macrostep of the combined path was taken from the left operand of the interleaving\<close>
    case (left e w' w1' w2) thus ?case
    proof (intro allI impI, goal_cases) 
      case (1 ca cb)
      hence I: "w' \<in> w1' \<otimes>\<^bsub>\<alpha>n fg\<^esub> w2" "fst (\<alpha>n fg e) \<inter> mon_pl (map (\<alpha>n fg) w2) = {}" 
        "!!ca cb.
           \<lbrakk>(ca, w1', ca') \<in> trcl (ntr fg);
           (cb, w2, cb') \<in> trcl (ntr fg);
           mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg w2) = {};
           mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg w1') = {}\<rbrakk> \<Longrightarrow>
           (ca + cb, w', ca' + cb') \<in> trcl (ntr fg)" 
        "(ca, e # w1', ca') \<in> trcl (ntr fg)" "(cb, w2, cb') \<in> trcl (ntr fg)"
        "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg w2) = {}"
        "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg (e # w1')) = {}" by blast+
      \<comment> \<open>Split the left path after the first step\<close>
      then obtain cah where SPLIT: "(ca,e,cah)\<in>ntr fg" "(cah,w1',ca')\<in>trcl (ntr fg)" by (fast dest: trcl_uncons)
      \<comment> \<open>and combine the first step of the left path with the initial right context\<close>
      from ntr_add_context_s[OF SPLIT(1), where cn=cb] I(7) have "(ca + cb, e, cah + cb) \<in> ntr fg" by auto 
      also
      \<comment> \<open>The rest of the path is combined by using the induction hypothesis\<close>
      have "(cah + cb, w', ca' + cb') \<in> trcl (ntr fg)" proof - 
        from I(2,6,7) ntr_mon_s[OF SPLIT(1)] have MON_CAH: "mon_c fg cah \<inter> (mon_c fg cb \<union> mon_ww fg w2) = {}" by (cases e) (auto simp add: cil_\<alpha>n_cons_helper) 
        with I(7) have MON_CB: "mon_c fg cb \<inter> (mon_c fg cah \<union> mon_ww fg w1') = {}" by auto
        from I(3)[OF SPLIT(2) I(5) MON_CAH MON_CB] show ?thesis .
      qed
      finally show ?case .
    qed
  next
    \<comment> \<open>The first macrostep of the combined path was taken from the right path -- this case is done completely analogous\<close>
    case (right e w' w2' w1) thus ?case
    proof (intro allI impI, goal_cases) 
      case (1 ca cb)
      hence I: "w' \<in> w1 \<otimes>\<^bsub>\<alpha>n fg\<^esub> w2'" "fst (\<alpha>n fg e) \<inter> mon_pl (map (\<alpha>n fg) w1) = {}" 
        "!!ca cb.
           \<lbrakk>(ca, w1, ca') \<in> trcl (ntr fg);
           (cb, w2', cb') \<in> trcl (ntr fg);
           mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg w2') = {};
           mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg w1) = {}\<rbrakk> \<Longrightarrow>
           (ca + cb, w', ca' + cb') \<in> trcl (ntr fg)" 
        "(ca, w1, ca') \<in> trcl (ntr fg)" "(cb, e#w2', cb') \<in> trcl (ntr fg)"
        "mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg (e#w2')) = {}"
        "mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg w1) = {}" by blast+
      then obtain cbh where SPLIT: "(cb,e,cbh)\<in>ntr fg" "(cbh,w2',cb')\<in>trcl (ntr fg)" by (fast dest: trcl_uncons)
      from ntr_add_context_s[OF SPLIT(1), where cn=ca] I(6) have "(ca + cb, e, ca + cbh) \<in> ntr fg" by (auto simp add: union_commute)
      also
      have "(ca + cbh, w', ca' + cb') \<in> trcl (ntr fg)" proof -
        from I(2,6,7) ntr_mon_s[OF SPLIT(1)] have MON_CBH: "mon_c fg cbh \<inter> (mon_c fg ca \<union> mon_ww fg w1) = {}" by (cases e) (auto simp add: cil_\<alpha>n_cons_helper)
        with I(6) have MON_CA: "mon_c fg ca \<inter> (mon_c fg cbh \<union> mon_ww fg w2') = {}" by auto
        from I(3)[OF I(4) SPLIT(2) MON_CA MON_CBH] show ?thesis .
      qed
      finally show ?case .
    qed
  qed
  with B show ?thesis by blast
qed


lemma (in flowgraph) ntrp_unsplit: 
  assumes A: "w\<in>wa\<otimes>\<^bsub>\<alpha>nl fg\<^esub> (map ENV wb)" and
  B: "((s,ca),wa,(s',ca'))\<in>trcl (ntrp fg)" 
  "(cb,wb,cb')\<in>trcl (ntr fg)" 
  "mon_c fg ({#s#}+ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb)={}" 
  "mon_c fg cb \<inter> (mon_c fg ({#s#}+ca) \<union> mon_ww fg (map le_rem_s wa))={}"
  shows "((s,ca+cb),w,(s',ca'+cb'))\<in>trcl (ntrp fg)"
proof -
  { fix wb'
    have "w\<in>wa\<otimes>\<^bsub>\<alpha>nl fg\<^esub>wb' \<Longrightarrow> 
      \<forall>s ca cb wb. wb'=map ENV wb \<and> 
      ((s,ca),wa,(s',ca'))\<in>trcl (ntrp fg) \<and> (cb,wb,cb')\<in>trcl (ntr fg) \<and> mon_c fg ({#s#}+ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb)={} \<and> mon_c fg cb \<inter> (mon_c fg ({#s#}+ca) \<union> mon_ww fg (map le_rem_s wa))={} \<longrightarrow> 
      ((s,ca+cb),w,(s',ca'+cb'))\<in>trcl (ntrp fg)" 
    proof (induct rule: cil_set_induct_fix\<alpha>)
      case empty thus ?case by simp
    next
      case (left e w' w1' w2)
      thus ?case
      proof (intro allI impI, goal_cases)
        case (1 s ca cb wb)
        hence I: "w' \<in> w1' \<otimes>\<^bsub>\<alpha>nl fg\<^esub> w2" "fst (\<alpha>nl fg e) \<inter> mon_pl (map (\<alpha>nl fg) w2) = {}"
          "!!s ca cb wb. \<lbrakk>
            w2 = map ENV wb;
            ((s, ca), w1', s', ca') \<in> trcl (ntrp fg);
            (cb, wb, cb') \<in> trcl (ntr fg);
            mon_c fg ({#s#} + ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {};
            mon_c fg cb \<inter> (mon_c fg ({#s#} + ca) \<union> mon_ww fg (map le_rem_s w1')) = {}
          \<rbrakk> \<Longrightarrow> ((s, ca + cb), w', s', ca' + cb') \<in> trcl (ntrp fg)"
          "w2 = map ENV wb"
          "((s, ca), e # w1', s', ca') \<in> trcl (ntrp fg)"
          "(cb, wb, cb') \<in> trcl (ntr fg)"
          "mon_c fg ({#s#} + ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {}"
          "mon_c fg cb \<inter> (mon_c fg ({#s#} + ca) \<union> mon_ww fg (map le_rem_s (e # w1'))) = {}"
          by blast+
        then obtain sh cah where SPLIT: "((s,ca),e,(sh,cah))\<in>ntrp fg" "((sh,cah),w1',(s',ca'))\<in>trcl (ntrp fg)" by (fast dest: trcl_uncons)
        from ntrp_add_context_s[OF SPLIT(1), of cb] I(8) have "((s, ca + cb), e, sh, cah + cb) \<in> ntrp fg" by auto
        also have "((sh,cah+cb),w',(s',ca'+cb'))\<in>trcl (ntrp fg)" proof (rule I(3))
          from ntrp_mon_s[OF SPLIT(1)] I(2,4,7,8) show 1: "mon_c fg ({#sh#} + cah) \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {}"
            by (cases e) (rename_tac a, case_tac a, simp add: cil_\<alpha>n_cons_helper, fastforce simp add: cil_\<alpha>n_cons_helper)+ (* FIXME: Ughly apply-script style proof *)
          from I(8) 1 show "mon_c fg cb \<inter> (mon_c fg ({#sh#} + cah) \<union> mon_ww fg (map le_rem_s w1')) = {}" by auto
        qed (auto simp add: I(4,6) SPLIT(2)) 
        finally show ?case .
      qed
    next
      case (right ee w' w2' w1)
      thus ?case
      proof (intro allI impI, goal_cases)
        case (1 s ca cb wb)
        hence I: "w' \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> w2'" "fst (\<alpha>nl fg ee) \<inter> mon_pl (map (\<alpha>nl fg) w1) = {}"
          "!!s ca cb wb. \<lbrakk>
            w2' = map ENV wb;
            ((s, ca), w1, s', ca') \<in> trcl (ntrp fg);
            (cb, wb, cb') \<in> trcl (ntr fg);
            mon_c fg ({#s#} + ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {};
            mon_c fg cb \<inter> (mon_c fg ({#s#} + ca) \<union> mon_ww fg (map le_rem_s w1)) = {}
          \<rbrakk> \<Longrightarrow> ((s, ca + cb), w', s', ca' + cb') \<in> trcl (ntrp fg)"
          "ee#w2' = map ENV wb"
          "((s, ca), w1, s', ca') \<in> trcl (ntrp fg)"
          "(cb, wb, cb') \<in> trcl (ntr fg)"
          "mon_c fg ({#s#} + ca) \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {}"
          "mon_c fg cb \<inter> (mon_c fg ({#s#} + ca) \<union> mon_ww fg (map le_rem_s w1)) = {}"
          by fastforce+
        from I(4) obtain e wb' where EE: "wb=e#wb'" "ee=ENV e" "w2'=map ENV wb'" by (cases wb, auto)
        with I(6) obtain cbh where SPLIT: "(cb,e,cbh)\<in>ntr fg" "(cbh,wb',cb')\<in>trcl (ntr fg)" by (fast dest: trcl_uncons)
        have "((s, ca + cb), ee, (s, ca + cbh)) \<in> ntrp fg" proof -
          from gtrE[OF SPLIT(1)] obtain sb ceb sbh cebh where NTRS: "cb = add_mset sb ceb" "cbh = add_mset sbh cebh" "((sb, ceb), e, sbh, cebh) \<in> ntrs fg" .
          from ntrs_add_context_s[OF NTRS(3), of "{#s#}+ca"] EE(1) I(7) have "((sb, add_mset s (ca+ceb)), e, sbh, add_mset s (ca+cebh)) \<in> ntrs fg" by (auto simp add: union_ac)
          from gtrp_env[OF this] NTRS(1,2) EE(2) show ?thesis by (simp add: union_ac)
        qed
        also have "((s,ca+cbh),w',(s',ca'+cb'))\<in>trcl (ntrp fg)" proof (rule I(3))
          from ntr_mon_s[OF SPLIT(1)] I(2,4,7,8) EE(2) show 1: "mon_c fg cbh \<inter> (mon_c fg ({#s#} + ca) \<union> mon_ww fg (map le_rem_s w1)) = {}"
            by (cases e) (simp add: cil_\<alpha>nl_cons_helper, fastforce simp add: cil_\<alpha>nl_cons_helper) (* FIXME: Ughly apply-script style proof *)
          from I(7) 1 EE(1) show "mon_c fg ({#s#} + ca) \<inter> (mon_c fg cbh \<union> mon_ww fg wb') = {}" by auto
        qed (auto simp add: EE(3) I(5) SPLIT(2)) 
        finally show ?case .
      qed
    qed
  }
  with A B show ?thesis by blast
qed


text \<open>And finally we get the desired theorem: {\em Two paths are simultaneously executable if and only if they are consistently interleavable and the monitors of the initial configurations are compatible}.
Note that we have to assume a valid starting configuration.\<close>  
theorem (in flowgraph) ntr_interleave: "valid fg (ca+cb) \<Longrightarrow> 
  (ca+cb,w,c')\<in>trcl (ntr fg) \<longleftrightarrow> 
  (\<exists>ca' cb' wa wb. 
    c'=ca'+cb' \<and> 
    w\<in>(wa\<otimes>\<^bsub>\<alpha>n fg\<^esub>wb) \<and> 
    mon_c fg ca \<inter> (mon_c fg cb \<union> mon_ww fg wb) = {} \<and> 
    mon_c fg cb \<inter> (mon_c fg ca \<union> mon_ww fg wa) = {} \<and> 
    (ca,wa,ca')\<in>trcl (ntr fg) \<and> (cb,wb,cb')\<in>trcl (ntr fg))"
by (blast intro!: ntr_split ntr_unsplit)

\<comment> \<open>Here is the corresponding version for executions with an explicit local thread\<close>
theorem (in flowgraph) ntrp_interleave: 
  "valid fg ({#s#}+c1+c2) \<Longrightarrow> 
  ((s,c1+c2),w,(s',c'))\<in>trcl (ntrp fg) \<longleftrightarrow> 
  (\<exists>w1 w2 c1' c2'. 
    w \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> (map ENV w2) \<and> 
    c'=c1'+c2' \<and> 
    ((s,c1),w1,(s',c1'))\<in>trcl (ntrp fg) \<and> 
    (c2,w2,c2')\<in>trcl (ntr fg) \<and> 
    mon_ww fg (map le_rem_s w1) \<inter> 
    mon_c fg c2 = {} \<and> 
    mon_ww fg w2 \<inter> mon_c fg ({#s#}+c1) = {})"
  apply (intro iffI)
  apply (blast intro: ntrp_split)
  apply (auto intro!: ntrp_unsplit simp add: valid_unconc
      mon_c_unconc)
  done

text \<open>The next is a corollary of @{thm [source] flowgraph.ntrp_unsplit}, allowing us to convert a path to loc/env semantics by adding a local stack that does not make any steps.\<close>
corollary (in flowgraph) ntr2ntrp: "\<lbrakk>
    (c,w,c')\<in>trcl (ntr fg); 
    mon_c fg (add_mset s cl) \<inter> (mon_c fg c \<union> mon_ww fg w)={}
  \<rbrakk> \<Longrightarrow> ((s,cl+c),map ENV w,(s,cl+c'))\<in>trcl (ntrp fg)" 
  using ntrp_unsplit[where wa="[]", simplified] by fast

subsubsection "Reverse splitting"
text \<open>This section establishes a theorem that allows us to find the thread in the original configuration that created some distinguished thread in the final configuration.\<close>

lemma (in flowgraph) ntr_reverse_split: "!!w s' ce'. \<lbrakk> 
  (c,w,{#s'#}+ce')\<in>trcl (ntr fg); 
  valid fg c \<rbrakk> \<Longrightarrow> 
  \<exists>s ce w1 w2 ce1' ce2'. 
    c={#s#}+ce \<and> 
    ce'=ce1'+ce2' \<and> 
    w\<in>w1\<otimes>\<^bsub>\<alpha>n fg\<^esub> w2 \<and> 
    mon_s fg s \<inter> (mon_c fg ce \<union> mon_ww fg w2) = {} \<and> 
    mon_c fg ce \<inter> (mon_s fg s \<union> mon_ww fg w1) = {} \<and> 
    ({#s#},w1,{#s'#}+ce1')\<in>trcl (ntr fg) \<and> 
    (ce,w2,ce2')\<in>trcl (ntr fg)" 
\<comment> \<open>The proof works by induction on the initial configuration. Note that configurations consist of finitely many threads only\<close>
\<comment> \<open>FIXME: An induction over the size (rather then over the adding of some fixed element) may lead to a smoother proof here\<close>
proof (induct c rule: multiset_induct') 
  \<comment> \<open>If the initial configuration is empty, we immediately get a contradiction\<close>
  case empty hence False by auto thus ?case .. 
next
  \<comment> \<open>The initial configuration has the form @{text "{#s#}+ce"}.\<close>
  case (add ce s)
  \<comment> \<open>We split the path by this initial configuration\<close>
  from ntr_split[OF add.prems(1,2)] obtain ce1' ce2' w1 w2 where 
    SPLIT: "add_mset s' ce'=ce1'+ce2'" "w\<in>w1\<otimes>\<^bsub>\<alpha>n fg\<^esub>w2" 
    "mon_c fg ce \<inter> (mon_s fg s\<union>mon_ww fg w1) = {}" 
    "mon_s fg s \<inter> (mon_c fg ce \<union> mon_ww fg w2) = {}" 
    "({#s#},w1,ce1')\<in>trcl (ntr fg)" 
    "(ce,w2,ce2')\<in>trcl (ntr fg)" 
    by auto 
  \<comment> \<open>And then check whether splitting off @{term s} was the right choice\<close>
  from SPLIT(1) show ?case proof (cases rule: mset_unplusm_dist_cases) 
    \<comment> \<open>Our choice was correct, @{term s'} is generated by some descendant of @{term s}"\<close>
    case left 
    with SPLIT show ?thesis by fastforce 
  next
    \<comment> \<open>Our choice was not correct, @{term s'} is generated by some descendant of @{term ce}\<close>
    case right with SPLIT(6) have C: "(ce,w2,{#s'#}+(ce2'-{#s'#}))\<in>trcl (ntr fg)" by auto 
    \<comment> \<open>In this case we apply the induction hypothesis to the path from @{term ce}\<close>
    from add.prems(2) have VALID: "valid fg ce" "mon_s fg s \<inter> mon_c fg ce = {}" by (simp_all add: valid_unconc)
    from add.hyps[OF C VALID(1)] obtain st cet w21 w22 ce21' ce22' where 
      IHAPP: 
      "ce={#st#}+cet" 
      "ce2'-{#s'#} = ce21'+ce22'" 
      "w2\<in>w21\<otimes>\<^bsub>\<alpha>n fg\<^esub>w22" 
      "mon_s fg st \<inter> (mon_c fg cet \<union> mon_ww fg w22)={}" 
      "mon_c fg cet \<inter> (mon_s fg st \<union> mon_ww fg w21)={}" 
      "({#st#},w21,{#s'#}+ce21')\<in>trcl (ntr fg)" 
      "(cet,w22,ce22')\<in>trcl (ntr fg)" by blast 
    
    \<comment> \<open>And finally we add the path from @{term s} again. This requires some monitor sorting and the associativity of the consistent interleaving operator.\<close>
    from cil_assoc2 [of w w1 _ w2 w22 w21] SPLIT(2) IHAPP(3) obtain wl where CASSOC: "w\<in>w21\<otimes>\<^bsub>\<alpha>n fg\<^esub>wl" "wl\<in>w1\<otimes>\<^bsub>\<alpha>n fg\<^esub>w22" by (auto simp add: cil_commute)
    from CASSOC IHAPP(1,3,4,5) SPLIT(3,4) have COMBINE: "(add_mset s cet, wl, ce1' + ce22') \<in> trcl (ntr fg)" using ntr_unsplit[OF CASSOC(2) SPLIT(5) IHAPP(7)] by (auto simp add: mon_c_unconc mon_ww_cil Int_Un_distrib2) 
    moreover from CASSOC IHAPP(1,3,4,5) SPLIT(3,4) have "mon_s fg st \<inter> (mon_c fg ({#s#}+cet) \<union> mon_ww fg wl) = {}" "mon_c fg ({#s#}+cet) \<inter> (mon_s fg st \<union> mon_ww fg w21) = {}" by (auto simp add: mon_c_unconc mon_ww_cil)
    moreover from right IHAPP(1,2) have "{#s#}+ce={#st#}+({#s#}+cet)" "ce'=ce21'+(ce1'+ce22')" by (simp_all add: union_ac)
    moreover note IHAPP(6) CASSOC(1)
    ultimately show ?thesis by fastforce
  qed
qed
    
end
