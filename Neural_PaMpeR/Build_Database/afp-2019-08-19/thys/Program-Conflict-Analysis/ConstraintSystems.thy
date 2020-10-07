(*  Title:       Conflict analysis/Constraint Systems
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Constraint Systems"
theory ConstraintSystems
imports Main AcquisitionHistory Normalization
begin
text_raw \<open>\label{thy:ConstraintSystems}\<close>

text \<open>
  In this section we develop a constraint-system-based characterization of our analysis. 
\<close>

text \<open>
  Constraint systems are widely used in static program analysis. There least solution describes the desired analysis information. In its generic form, a constraint system $R$ is a set of inequations over
  a complete lattice $(L,\sqsubseteq)$ and a set of variables $V$. An inequation has the form $ R[v] \sqsupseteq {\sf rhs}$, where $R[v]\in V$ and ${\sf rhs}$ is a monotonic function over the variables. 
  Note that for program analysis, there is usually one variable per control point. The variables are then named $R[v]$, where $v$ is a control point.
  By standard fixed-point theory, those constraint systems have a least solution. Outside the constraint system definition $R[v]$ usually refers to a component of that least solution.

  Usually a constraint system is generated from the program. For example, a constraint generation pattern could be the following:
  $$
    \begin{array}{lcl}
      \multicolumn{3}{l}{\mbox{for $(u,{\sf Call}~q,v)\in E$:}} \\ 
        S^k[v] & \supseteq & \{({\sf mon}(q)\cup M\cup M',\tilde P) \mid (M,P)\in S^k[u] \wedge (M',P')\in S^k[{\sf r}_q] \\&&\wedge~\tilde P \le P \uplus P' \wedge |\tilde P| \le 2 \} \\
    \end{array}
  $$

  For some parameter $k$ and a flowgraph with nodes $N$ and edges $E$, this generates a constraint system over the variables $\{ S^k[v] \mid v\in N \}$. One constraint is generated for each call edge. While we use
  a powerset lattice here, we can in general use any complete lattice. However, all the constraint systems needed for our conflict analysis are defined over powerset lattices $(\mathcal P('a), \subseteq)$ for some type $'a$. 
  This admits a convenient formalization in Isabelle/HOL using inductively defined sets. We inductively define a relation between variables\footnote{Variables are identified by control nodes here} and the elements of their values 
  in the least solution, i.e. the set $\{ (v,x) \mid x\in R[v] \}$. For example, the constraint generator pattern from above would become the following introduction rule in the inductive definition of the set \<open>S_cs fg k\<close>:
    @{text [display] "\<lbrakk>(u,Call q,v)\<in>edges fg; (u,M,P)\<in>S_cs fg k; 
              (return fg q,Ms,Ps)\<in>S_cs fg k; P'\<subseteq>#P+Ps; size P' \<le> k \<rbrakk> 
             \<Longrightarrow> (v,mon fg q \<union> M \<union> Ms,P')\<in>S_cs fg k"}
  The main advantage of this approach is that one gets a concise formalization by using Isabelle's standard machinery, the main disadvantage is that this approach only works for powerset lattices ordered by $\subseteq$.
\<close>

subsection "Same-level paths"

subsubsection \<open>Definition\<close>
text \<open>
  We define a constraint system that collects abstract information about same-level paths. In particular, we collect the set of used monitors and all multi-subsets of spawned threads 
  that are not bigger than @{term k} elements, where @{term k} is a parameter that can be freely chosen. 
\<close>


text \<open>
  An element \<open>(u,M,P)\<in>S_cs fg k\<close> means that there is a same-level path from the entry node of the procedure of @{term u} to @{term u}, that uses the monitors @{term M} and spawns at least the threads in @{term P}.
\<close>
inductive_set
  S_cs :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> nat \<Rightarrow> 
             ('n \<times> 'm set \<times> 'p multiset) set"
  for fg k
  where
    S_init: "(entry fg p,{},{#})\<in>S_cs fg k" 
  | S_base: "\<lbrakk>(u,Base a,v)\<in>edges fg; (u,M,P)\<in>S_cs fg k\<rbrakk> \<Longrightarrow> (v,M,P)\<in>S_cs fg k" 
  | S_call: "\<lbrakk>(u,Call q,v)\<in>edges fg; (u,M,P)\<in>S_cs fg k; 
              (return fg q,Ms,Ps)\<in>S_cs fg k; P'\<subseteq>#P+Ps; size P' \<le> k \<rbrakk>
             \<Longrightarrow> (v,mon fg q \<union> M \<union> Ms,P')\<in>S_cs fg k" 
  | S_spawn: "\<lbrakk>(u,Spawn q,v)\<in>edges fg; (u,M,P)\<in>S_cs fg k; 
               P'\<subseteq>#{#q#}+P; size P' \<le> k\<rbrakk>
             \<Longrightarrow> (v,M,P')\<in>S_cs fg k" 
text \<open>
  The intuition underlying this constraint system is the following: The @{thm [source] S_init}-constraint describes that the procedures entry node can be reached with the empty path, that has no monitors and spawns no procedures. 
  The @{thm [source] S_base}-constraint describes that executing a base edge does not use monitors or spawn threads, so each path reaching the start node of the base edge also induces a path reaching the end node of the base edge
  with the same set of monitors and the same set of spawned threads. 
  The @{thm [source] S_call}-constraint models the effect of a procedure call. If there is a path to the start node of a call edge and a same-level path through the procedure, this also induces a path to the end
  node of the call edge. This path uses the monitors of both path and spawns the threads that are spawned on both paths. Since we only record a limited subset of the spawned threads, we have to choose which of the 
  threads are recorded.
  The @{thm [source] S_spawn}-constraint models the effect of a spawn edge. A path to the start node of the spawn edge induces a path to the end node that uses the same set of monitors and spawns the threads of the initial path
  plus the one spawned by the spawn edge. We again have to choose which of these threads are recorded.

\<close>

subsubsection \<open>Soundness and Precision\<close>

text \<open>
  Soundness of the constraint system \<open>S_cs\<close> means, that every same-level path has a corresponding entry in the constraint system.

  As usual the soundness proof works by induction over the length of execution paths. The base case (empty path) trivially follows from the @{thm [source] S_init} constraint. In the inductive case,
  we consider the edge that induces the last step of the path; for a return step, this is the corresponding call edge (cf. Lemma @{thm [source] flowgraph.trss_find_call'}). With the induction hypothesis, we get
  the soundness for the (shorter) prefix of the path, and depending on the last step we can choose a constraint that implies soundness for the whole path.  
\<close>

lemma (in flowgraph) S_sound: "!!p v c' P. 
  \<lbrakk>(([entry fg p],{#}),w,([v],c'))\<in>trcl (trss fg); 
    size P\<le>k; (\<lambda>p. [entry fg p]) `# P \<subseteq># c' \<rbrakk>
  \<Longrightarrow> (v,mon_w fg w,P)\<in>S_cs fg k"
proof (induct w rule: length_compl_rev_induct) 
  case Nil thus ?case by (auto intro: S_init)
next
  case (snoc w e) then obtain sh ch where SPLIT: "(([entry fg p],{#}),w,(sh,ch))\<in>trcl (trss fg)" "((sh,ch),e,([v],c'))\<in>trss fg" by (fast dest: trcl_rev_uncons)
  from SPLIT(2) show ?case proof (cases rule: trss.cases)
    case trss_base then obtain u a where CASE: "e=LBase a" "sh=[u]" "ch=c'" "(u,Base a,v)\<in>edges fg" by auto 
    with snoc.hyps[of w p u c', OF _ _ snoc.prems(2,3)] SPLIT(1) have "(u,mon_w fg w,P)\<in>S_cs fg k" by blast
    moreover from CASE(1) have "mon_e fg e = {}" by simp
    ultimately show ?thesis using S_base[OF CASE(4)] by (auto simp add: mon_w_unconc)
  next
    case trss_ret then obtain q where CASE: "e=LRet" "sh=return fg q#[v]" "ch=c'" by auto
    with SPLIT(1) have "(([entry fg p], {#}), w, [return fg q,v], c') \<in> trcl (trss fg)" by simp
    from trss_find_call'[OF this] obtain ut ct w1 w2 where FC:
      "w=w1@LCall q#w2" 
      "(([entry fg p],{#}),w1,([ut],ct))\<in>trcl (trss fg)" 
      "(([ut],ct),LCall q,([entry fg q,v],ct))\<in>trss fg"
      "(ut,Call q,v)\<in>edges fg" 
      "(([entry fg q],ct),w2,([return fg q],c'))\<in>trcl (trss fg)" .
    from trss_drop_all_context[OF FC(5)] obtain csp' where SLP: "c'=ct+csp'" "(([entry fg q],{#}),w2,([return fg q],csp'))\<in>trcl (trss fg)" by (auto simp add: union_ac)
    from FC(1) have LEN: "length w1 \<le> length w" "length w2 \<le> length w" by auto
    from mset_map_split_orig_le SLP(1) snoc.prems(3) obtain P1 P2 where PSPLIT: "P=P1+P2" "(\<lambda>p. [entry fg p]) `# P1 \<subseteq># ct" "(\<lambda>p. [entry fg p]) `# P2 \<subseteq># csp'" by blast
    with snoc.prems(2) have PSIZE: "size P1 \<le> k" "size P2 \<le> k" by auto
    from snoc.hyps[OF LEN(1) FC(2) PSIZE(1) PSPLIT(2)] snoc.hyps[OF LEN(2) SLP(2) PSIZE(2) PSPLIT(3)] have IHAPP: "(ut, mon_w fg w1, P1) \<in> S_cs fg k" "(return fg q, mon_w fg w2, P2) \<in> S_cs fg k" .
    from S_call[OF FC(4) IHAPP subset_mset.eq_refl[OF PSPLIT(1)] snoc.prems(2)] FC(1) CASE(1) show "(v, mon_w fg (w@[e]), P) \<in> S_cs fg k" by (auto simp add: mon_w_unconc Un_ac)
  next
    case trss_spawn then obtain u q where CASE: "e=LSpawn q" "sh=[u]" "c'={#[entry fg q]#}+ch" "(u,Spawn q,v)\<in>edges fg" by auto
    from mset_map_split_orig_le CASE(3) snoc.prems(3) obtain P1 P2 where PSPLIT: "P=P1+P2" "(\<lambda>p. [entry fg p]) `# P1 \<subseteq># {#[entry fg q]#}" "(\<lambda>p. [entry fg p]) `# P2 \<subseteq># ch" by blast
    with snoc.prems(2) have PSIZE: "size P2 \<le> k" by simp
    from snoc.hyps[OF _ _ PSIZE PSPLIT(3)] SPLIT(1) CASE(2) have IHAPP: "(u,mon_w fg w,P2)\<in>S_cs fg k" by blast
    have PCOND: "P \<subseteq># {#q#}+P2" proof -
      from PSPLIT(2) have "P1\<subseteq>#{#q#}" by (auto elim!: mset_le_single_cases mset_map_single_rightE)
      with PSPLIT(1) show ?thesis by simp
    qed
    from S_spawn[OF CASE(4) IHAPP PCOND snoc.prems(2)] CASE(1) show "(v, mon_w fg (w @ [e]), P) \<in> S_cs fg k" by (auto simp add: mon_w_unconc)
  qed
qed
    
text \<open>
  Precision means that all entries appearing in the smallest solution of the constraint system are justified by some path in the operational characterization.
  For proving precision, one usually shows that a family of sets derived as an abstraction from the operational characterization solves all constraints.

  In our formalization of constraint systems as inductive sets this amounts to constructing for each constraint a justifying path for the entries described on the conclusion side of the implication -- under the assumption
  that corresponding paths exists for the entries mentioned in the antecedent.
\<close>

lemma (in flowgraph) S_precise: "(v,M,P)\<in>S_cs fg k 
  \<Longrightarrow> \<exists>p c' w. 
        (([entry fg p],{#}),w,([v],c'))\<in>trcl (trss fg) \<and> 
        size P\<le>k \<and> 
        (\<lambda>p. [entry fg p]) `# P \<subseteq># c' \<and>
        M=mon_w fg w"
proof (induct rule: S_cs.induct)
  case (S_init p) have "(([entry fg p],{#}),[],([entry fg p],{#}))\<in>trcl (trss fg)" by simp_all
  thus ?case by fastforce
next
  case (S_base u a v M P) then obtain p c' w where IHAPP: "(([entry fg p], {#}), w, [u], c') \<in> trcl (trss fg)" "size P \<le> k" "(\<lambda>p. [entry fg p]) `# P \<subseteq># c'" "M = mon_w fg w" by blast
  note IHAPP(1)
  also from S_base have "(([u],c'),LBase a,([v],c'))\<in>trss fg" by (auto intro: trss_base)
  finally have "(([entry fg p], {#}), w @ [LBase a], [v], c') \<in> trcl (trss fg)" .
  moreover from IHAPP(4) have "M=mon_w fg (w @ [LBase a])" by (simp add: mon_w_unconc)
  ultimately show ?case using IHAPP(2,3,4) by blast
next
  case (S_call u q v M P Ms Ps P') then obtain p csp1 w1 where REACHING_PATH: "(([entry fg p], {#}), w1, [u], csp1) \<in> trcl (trss fg)" "size P \<le> k" "(\<lambda>p. [entry fg p]) `# P \<subseteq># csp1" "M = mon_w fg w1" by blast
  from S_call obtain csp2 w2 where SL_PATH: "(([entry fg q], {#}), w2, [return fg q], csp2) \<in> trcl (trss fg)" "size Ps \<le> k" "(\<lambda>p. [entry fg p]) `# Ps \<subseteq># csp2" "Ms = mon_w fg w2"
    by (blast dest: trss_er_path_proc_const)
  from trss_c_no_mon[OF REACHING_PATH(1)] trss_c_no_mon[OF SL_PATH(1)] have NOMON: "mon_c fg csp1 = {}" "mon_c fg csp2 = {}" by auto
  have "(([entry fg p], {#}), w1@LCall q#w2@[LRet],([v],csp1+csp2))\<in>trcl (trss fg)" proof -
    note REACHING_PATH(1)
    also from trss_call[OF S_call(1)] NOMON have "(([u],csp1),LCall q,([entry fg q,v],csp1))\<in>trss fg" by (auto)
    also from trss_add_context[OF trss_stack_comp[OF SL_PATH(1)]] NOMON have "(([entry fg q,v],csp1),w2,([return fg q,v],csp1+csp2))\<in>trcl (trss fg)" by (simp add: union_ac)
    also have "(([return fg q,v],csp1+csp2),LRet,([v],csp1+csp2))\<in>trss fg" by (rule trss_ret)
    finally show ?thesis by simp
  qed
  moreover from REACHING_PATH(4) SL_PATH(4) have "mon fg q \<union> M \<union> Ms = mon_w fg (w1@LCall q#w2@[LRet])" by (auto simp add: mon_w_unconc)
  moreover have "(\<lambda>p. [entry fg p]) `# (P') \<subseteq># csp1+csp2" (is "?f `# P' \<subseteq># _") proof -
    from image_mset_subseteq_mono[OF S_call(6)] have "?f `# P' \<subseteq># ?f `# P + ?f `# Ps" by auto
    also from mset_subset_eq_mono_add[OF REACHING_PATH(3) SL_PATH(3)] have "\<dots> \<subseteq># csp1+csp2" .
    finally show ?thesis .
  qed
  moreover note S_call(7)
  ultimately show ?case by blast
next
  case (S_spawn u q v M P P') then obtain p c' w where IHAPP: "(([entry fg p], {#}), w, [u], c') \<in> trcl (trss fg)" "size P \<le> k" "(\<lambda>p. [entry fg p]) `# P \<subseteq># c'" "M = mon_w fg w" by blast
  note IHAPP(1)
  also from S_spawn(1) have "(([u],c'),LSpawn q,([v],add_mset [entry fg q] c'))\<in>trss fg" by (rule trss_spawn)
  finally have "(([entry fg p], {#}), w @ [LSpawn q], [v], add_mset [entry fg q] c') \<in> trcl (trss fg)" .
  moreover from IHAPP(4) have "M=mon_w fg (w @ [LSpawn q])" by (simp add: mon_w_unconc)
  moreover have "(\<lambda>p. [entry fg p]) `# P' \<subseteq># {#[entry fg q]#} + c'" (is "?f `# _ \<subseteq># _") proof -
    from image_mset_subseteq_mono[OF S_spawn(4)] have "?f `# P' \<subseteq># {#[entry fg q]#} + ?f `# P" by auto
    also from mset_subset_eq_mono_add[OF _ IHAPP(3)] have "\<dots> \<subseteq># {#[entry fg q]#} + c'" by (auto intro: IHAPP(3))
    finally show ?thesis .
  qed
  moreover note S_spawn(5)
  ultimately show ?case by auto
qed

\<comment> \<open>Finally we can state the soundness and precision as a single theorem\<close>  
theorem (in flowgraph) S_sound_precise: 
  "(v,M,P)\<in>S_cs fg k \<longleftrightarrow> 
  (\<exists>p c' w. (([entry fg p],{#}),w,([v],c'))\<in>trcl (trss fg) \<and> 
    size P\<le>k \<and> (\<lambda>p. [entry fg p]) `# P \<subseteq># c' \<and> M=mon_w fg w)"
  using S_sound S_precise by blast


text \<open>Next, we present specialized soundness and precision lemmas, that reason over a macrostep (@{term "ntrp fg"}) rather than a same-level path (@{term "trcl (trss fg)"}). They are tailored for the
  use in the soundness and precision proofs of the other constraint systems.
\<close>
lemma (in flowgraph) S_sound_ntrp: 
  assumes A: "(([u],{#}),eel,(sh,ch))\<in>ntrp fg" and 
  CASE: "!!p u' v w. \<lbrakk>
    eel=LOC (LCall p#w); 
    (u,Call p,u')\<in>edges fg; 
    sh=[v,u']; 
    proc_of fg v = p; 
    mon_c fg ch = {}; 
    !!s. s \<in># ch \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> 
                     (u,Spawn p,v)\<in>edges fg \<and> 
                     initialproc fg p; 
    !!P. (\<lambda>p. [entry fg p]) `# P \<subseteq># ch \<Longrightarrow>
                    (v,mon_w fg w,P)\<in>S_cs fg (size P)
  \<rbrakk> \<Longrightarrow> Q"
  shows Q
proof -
  from A obtain ee where EE: "eel=LOC ee" "(([u],{#}),ee,(sh,ch))\<in>ntrs fg" by (auto elim: gtrp.cases)
  have CHFMT: "!!s. s \<in># ch \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> (u,Spawn p,v)\<in>edges fg \<and> initialproc fg p" by (auto intro: ntrs_c_cases_s[OF EE(2)])
  with c_of_initial_no_mon have CHNOMON: "mon_c fg ch = {}" by blast
  from EE(2) obtain p u' v w where FIRSTSPLIT: "ee=LCall p#w" "(([u],{#}),LCall p,([entry fg p,u'],{#}))\<in>trss fg" "sh=[v,u']" "(([entry fg p],{#}),w,([v],ch))\<in>trcl (trss fg)" by (auto elim!: ntrs.cases[simplified])
  from FIRSTSPLIT have EDGE: "(u,Call p,u')\<in>edges fg" by (auto elim!: trss.cases)
  from trss_bot_proc_const[where s="[]" and s'="[]", simplified, OF FIRSTSPLIT(4)] have PROC_OF_V: "proc_of fg v = p" by simp
  have "!!P. (\<lambda>p. [entry fg p]) `# P \<subseteq># ch \<Longrightarrow> (v,mon_w fg w,P)\<in>S_cs fg (size P)" proof -
    fix P assume "(\<lambda>p. [entry fg p]) `# P \<subseteq># ch"
    from S_sound[OF FIRSTSPLIT(4) _ this, of "size P"] show "?thesis P" by simp
  qed
  with EE(1) FIRSTSPLIT(1,3) EDGE PROC_OF_V CHNOMON CHFMT show Q by (rule_tac CASE) auto 
qed

lemma (in flowgraph) S_precise_ntrp: 
  assumes ENTRY: "(v,M,P)\<in>S_cs fg k" and 
              P: "proc_of fg v = p" and 
           EDGE: "(u,Call p,u')\<in>edges fg"
  shows "\<exists>w ch. 
    (([u],{#}),LOC (LCall p#w),([v,u'],ch))\<in>ntrp fg \<and> 
    size P \<le> k \<and> 
    M=mon_w fg w \<and> 
    mon_n fg v = mon fg p \<and> 
    (\<lambda>p. [entry fg p]) `# P \<subseteq># ch \<and>
    mon_c fg ch={}"
proof -
  from P S_precise[OF ENTRY, simplified] trss_bot_proc_const[where s="[]" and s'="[]", simplified] obtain wsl ch where 
    SLPATH: "(([entry fg p], {#}), wsl, [v], ch) \<in> trcl (trss fg)" "size P \<le> k" "(\<lambda>p. [entry fg p]) `# P \<subseteq># ch" "M = mon_w fg wsl" by fastforce
  from mon_n_same_proc[OF trss_bot_proc_const[where s="[]" and s'="[]", simplified, OF SLPATH(1)]] have MON_V: "mon_n fg v = mon fg p" by (simp)
  from trss_c_cases[OF SLPATH(1), simplified] have CHFMT: "\<And>s. s \<in># ch \<Longrightarrow> \<exists>p. s = [entry fg p] \<and> (\<exists>u v. (u, Spawn p, v) \<in> edges fg) \<and> initialproc fg p" by blast
  with c_of_initial_no_mon have CHNOMON: "mon_c fg ch = {}" by blast
  \<comment> \<open>From the constraints prerequisites, we can construct the first step\<close>
  have FS: "(([u],{#}),LCall p#wsl,([v,u'],ch))\<in>ntrs fg" proof (rule ntrs_step[where r="[]", simplified])
    from EDGE show "(([u], {#}), LCall p, [entry fg p, u'], {#}) \<in> trss fg" by (auto intro: trss_call)
  qed (rule SLPATH(1))
  hence FSP: "(([u],{#}),LOC (LCall p#wsl),([v,u'],ch))\<in>ntrp fg" by (blast intro: gtrp_loc) 
  from FSP SLPATH(2,3,4) CHNOMON MON_V show ?thesis by blast 
qed


subsection "Single reaching path"
  
text \<open>
  In this section we define a constraint system that collects abstract information of paths reaching a control node at @{term U}. 
  The path starts with a single initial thread. The collected information are the monitors used by the steps of the initial thread, 
  the monitors used by steps of other threads and the acquisition history of the path. To distinguish the steps of the initial thread 
  from steps of other threads, we use the loc/env-semantics (cf. Section~\ref{sec:ThreadTracking:exp_local}).
\<close>

subsubsection "Constraint system"

text \<open>
  An element @{term "(u,Ml,Me,h)\<in>RU_cs fg U"} corresponds to a path from @{term "{#[u]#}"} to some configuration at @{term U}, 
  that uses monitors from @{term Ml} in the steps of the initial thread, monitors from @{term Me} in the steps of other threads and
  has acquisition history @{term h}. 

  Here, the correspondence between paths and entries included into the inductively defined set is not perfect but strong enough for our purposes:
  While each constraint system entry corresponds to a path, not each path corresponds to a constraint system entry. But for each path reaching a configuration at @{term U}, we find
  an entry with less or equal monitors and an acquisition history less or equal to the acquisition history of the path. 
\<close>
inductive_set
  RU_cs :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> 'n set \<Rightarrow> 
              ('n \<times> 'm set \<times> 'm set \<times> ('m \<Rightarrow> 'm set)) set"
  for fg U
  where
    RU_init: "u\<in>U \<Longrightarrow> (u,{},{},\<lambda>x.{})\<in>RU_cs fg U"
  | RU_call: "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 0; 
                (v,Ml,Me,h)\<in>RU_cs fg U; mon_n fg u \<inter> Me = {} \<rbrakk> 
    \<Longrightarrow> ( u, mon fg p \<union> M \<union> Ml, Me, ah_update h (mon fg p,M) (Ml\<union>Me)) 
        \<in> RU_cs fg U"
  | RU_spawn: "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 1; 
                 q \<in># P; (entry fg q,Ml,Me,h)\<in>RU_cs fg U; 
                 (mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me)={} \<rbrakk> 
    \<Longrightarrow> (u,mon fg p \<union> M, Ml \<union> Me, ah_update h (mon fg p,M) (Ml\<union>Me))
        \<in> RU_cs fg U"

text \<open>
  The constraint system works by tracking only a single thread. Initially, there is just one thread, and from this thread we reach a configuration at @{term U}. After a macrostep, we have the
  transformed initial thread and some spawned threads. The key idea is, that the actual node @{term U} is reached by just one of these threads. The steps of the other threads are useless
  for reaching @{term U}. Because of the nice properties of normalized paths, we can simply prune those steps from the path.

  The @{thm [source] RU_init}-constraint reflects that we can reach a control node from itself with the empty path. 
  The @{thm [source] RU_call}-constraint describes the case that @{term U} is reached from the initial thread, and the 
  @{thm [source] RU_spawn}-constraint describes the case that @{term U} is reached from one of the spawned threads. In the two latter cases, we 
  have to check whether prepending the macrostep to the reaching path is allowed or not due to monitor restrictions. In the call case, the procedure 
  of the initial node must not own monitors that are used in the environment steps of the appended reaching path (\<open>mon_n fg u \<inter> Me = {}\<close>). 
  As we only test disjointness with the set of monitors used by the environment, reentrant monitors can be handled. 
  In the spawn case, we have to check disjointness with both, the monitors of local and environment steps of the
  reaching path from the spawned thread, because from the perspective of the initial thread, all these steps are environment steps (\<open>(mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me)={}\<close>). 
  Note that in the call case, we do not need to explicitly check that the monitors used by the environment are disjoint from the monitors acquired by the called procedure because this already follows from the existence
  of a reaching path, as the starting point of this path already holds all these monitors. 

  However, in the spawn case, we have to check for both the monitors of the start node and of the called procedure to be compatible with
  the already known reaching path from the entry node of the spawned thread.
\<close>


subsubsection "Soundness and precision"

text \<open>The following lemma intuitively states:
  {\em If we can reach a configuration that is at @{term U} from some start configuration, then there is a single thread in the start configuration that 
  can reach a configuration at @{term U} with a subword of the original path}. 

  The proof follows from Lemma @{thm [source] flowgraph.ntr_reverse_split} rather directly.
\<close>
lemma (in flowgraph) ntr_reverse_split_atU: 
  assumes V: "valid fg c" and 
          A: "atU U c'" and 
          B: "(c,w,c')\<in>trcl (ntr fg)" 
  shows "\<exists>s w' c1'. 
           s \<in># c \<and> w'\<preceq>w \<and> c1' \<subseteq># c' \<and>
           atU U c1' \<and> ({#s#},w',c1')\<in>trcl (ntr fg)" 
proof -
  obtain ui r ce' where C'FMT: "c'={#ui#r#}+ce'" "ui\<in>U" by (rule atU_fmt[OF A], simp only: mset_contains_eq) (blast dest: sym)
  with ntr_reverse_split[OF _ V] B obtain s ce w1 w2 ce1' ce2' where RSPLIT: "c={#s#}+ce" "ce'=ce1'+ce2'" "w\<in>w1\<otimes>\<^bsub>\<alpha>n fg\<^esub>w2" "({#s#}, w1, {#ui#r#} + ce1') \<in> trcl (ntr fg)" by blast
  with C'FMT have "s \<in># c" "w1\<preceq>w" "{#ui#r#}+ce1' \<subseteq># c'" "atU U ({#ui#r#}+ce1')" by (auto dest: cil_ileq)
  with RSPLIT(4) show ?thesis by blast
qed

text \<open>
  The next lemma shows the soundness of the RU constraint system.

  The proof works by induction over the length of the reaching path. For the empty path, the proposition follows by the @{thm [source] RU_init}-constraint. 
  For a non-empty path, we consider the first step.
  It has transformed the initial thread and may have spawned some other threads. From the resulting configuration, @{term U} is reached. 
  Due to @{thm [source] "flowgraph.ntr_split"} we get two interleavable paths from the rest of the original path, one from the transformed initial thread and one from the spawned threads. 
  We then distinguish two cases: if the first path reaches \<open>U\<close>, the proposition follows by the induction hypothesis and the @{thm [source] RU_call} constraint. 
  
  Otherwise, we use @{thm [source] "flowgraph.ntr_reverse_split_atU"} to identify the thread that actually reaches @{term U} among all the spawned threads. Then we 
  apply the induction hypothesis to the path of that thread and prepend the first step using the @{thm [source] RU_spawn}-constraint.
  
  The main complexity of the proof script below results from fiddling with the monitors and converting between the multiset-and loc/env-semantics. 
  Also the arguments to show that the acquisition histories are sound approximations require some space.
\<close>
lemma (in flowgraph) RU_sound: 
  "!!u s' c'. \<lbrakk>(([u],{#}),w,(s',c'))\<in>trcl (ntrp fg); atU U (add_mset s' c')\<rbrakk> 
  \<Longrightarrow> \<exists>Ml Me h. 
    (u,Ml,Me,h)\<in>RU_cs fg U \<and> 
    Ml \<subseteq> mon_loc fg w \<and> 
    Me \<subseteq> mon_env fg w \<and> 
    h \<le> \<alpha>ah (map (\<alpha>nl fg) w)"
\<comment> \<open>The proof works by induction over the length of the reaching path\<close>
proof (induct w rule: length_compl_induct) 
  \<comment> \<open>For a reaching path of length zero, the proposition follows immediately by the constraint @{thm [source] RU_init}\<close>
  case Nil thus ?case by auto (auto intro!: RU_init) 
next
  case (Cons eel wwl) 
  \<comment> \<open>For a non-empty path, we regard the first step and the rest of the path\<close>
  then obtain sh ch where SPLIT: 
    "(([u],{#}),eel,(sh,ch))\<in>ntrp fg" 
    "((sh,ch),wwl,(s',c'))\<in>trcl (ntrp fg)" 
    by (fast dest: trcl_uncons)
  obtain p u' v w where 
    \<comment> \<open>The first step consists of an initial call and a same-level path\<close>
    FS_FMT: "eel = LOC (LCall p # w)" "(u, Call p, u') \<in> edges fg" "sh = [v, u']" "proc_of fg v = p" "mon_c fg ch = {}" 
    \<comment> \<open>The only environment threads after the first step are the threads that where spawned by the first step\<close>
    and CHFMT: "\<And>s. s \<in># ch \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> (u,Spawn p,v)\<in>edges fg \<and> initialproc fg p"
    \<comment> \<open>For the same-level path, we find a corresponding entry in the @{text "S_cs"}-constraint system\<close>
    and S_ENTRY_PAT: "\<And>P. (\<lambda>p. [entry fg p]) `# P \<subseteq># ch \<Longrightarrow> (v, mon_w fg w, P) \<in> S_cs fg (size P)"
    by (rule S_sound_ntrp[OF SPLIT(1)]) blast
  from ntrp_valid_preserve_s[OF SPLIT(1)] have HVALID: "valid fg ({#sh#} + ch)" by simp
  \<comment> \<open>We split the remaining path by the local thread and the spawned threads, getting two interleavable paths, one from the local thread and one from the spawned threads\<close>
  from ntrp_split[where ?c1.0="{#}", simplified, OF SPLIT(2) ntrp_valid_preserve_s[OF SPLIT(1)], simplified] obtain w1 w2 c1' c2' where 
    LESPLIT: 
      "wwl\<in>w1\<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV w2" 
      "c' = c1' + c2'" 
      "((sh, {#}), w1, s', c1') \<in> trcl (ntrp fg)" 
      "(ch, w2, c2') \<in> trcl (ntr fg)" 
      "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg ch = {}" 
      "mon_ww fg w2 \<inter> mon_s fg sh = {}" 
    by blast
  \<comment> \<open>We make a case distinction whether @{term U} was reached from the local thread or from the spawned threads\<close>
  from Cons.prems(2) LESPLIT(2) have "atU U (({#s'#}+c1') + c2')" by (auto simp add: union_ac)
  thus ?case proof (cases rule: atU_union_cases) 
    case left \<comment> \<open>@{term U} was reached from the local thread\<close>
    from cil_ileq[OF LESPLIT(1)] have ILEQ: "w1\<preceq>wwl" and LEN: "length w1 \<le> length wwl" by (auto simp add: le_list_length)
    \<comment> \<open>We can cut off the bottom stack symbol from the reaching path (as always possible for normalized paths)\<close>
    from FS_FMT(3) LESPLIT(3) ntrp_stack_decomp[of v "[]" "[u']" "{#}" w1 s' c1' fg, simplified] obtain v' rr where DECOMP: "s'=v'#rr@[u']" "(([v],{#}),w1,(v'#rr,c1'))\<in>trcl (ntrp fg)" by auto
    \<comment> \<open>This does not affect the configuration being at @{term U}\<close>
    from atU_xchange_stack left DECOMP(1) have ATU: "atU U (add_mset (v'#rr) c1')" by fastforce 
    \<comment> \<open>Then we can apply the induction hypothesis to get a constraint system entry for the path\<close>
    from Cons.hyps[OF LEN DECOMP(2) ATU] obtain Ml Me h where IHAPP: "(v,Ml,Me,h)\<in>RU_cs fg U" "Ml \<subseteq> mon_loc fg w1" "Me \<subseteq> mon_env fg w1" "h \<le> \<alpha>ah (map (\<alpha>nl fg) w1)" by blast 
    \<comment> \<open>Next, we have to apply the constraint @{thm [source] RU_call}\<close>
    from S_ENTRY_PAT[of "{#}", simplified] have S_ENTRY: "(v, mon_w fg w, {#}) \<in> S_cs fg 0" .
    have MON_U_ME: "mon_n fg u \<inter> Me = {}" proof -
      from ntrp_mon_env_w_no_ctx[OF Cons.prems(1)] have "mon_env fg wwl \<inter> mon_n fg u = {}" by (auto)
      with mon_env_ileq[OF ILEQ] IHAPP(3) show ?thesis by fast
    qed
    from RU_call[OF FS_FMT(2,4) S_ENTRY IHAPP(1) MON_U_ME] have "(u, mon fg p \<union> mon_w fg w \<union> Ml, Me, ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me)) \<in> RU_cs fg U" . 
    \<comment> \<open>Then we assemble the rest of the proposition, that are the monitor restrictions and the acquisition history restriction\<close>
    moreover have "mon fg p \<union> mon_w fg w \<union> Ml \<subseteq> mon_loc fg (eel#wwl)" using mon_loc_ileq[OF ILEQ] IHAPP(2) FS_FMT(1) by fastforce
    moreover have "Me \<subseteq> mon_env fg (eel#wwl)" using mon_env_ileq[OF ILEQ, of fg] IHAPP(3) by auto
    moreover have "ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me) \<le> \<alpha>ah (map (\<alpha>nl fg) (eel#wwl))" proof (simp add: ah_update_cons)
      show "ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me) \<le> ah_update (\<alpha>ah (map (\<alpha>nl fg) wwl)) (\<alpha>nl fg eel) (mon_pl (map (\<alpha>nl fg) wwl))" proof (rule ah_update_mono)
        from IHAPP(4) have "h \<le> \<alpha>ah (map (\<alpha>nl fg) w1)" .
        also from \<alpha>ah_ileq[OF le_list_map[OF ILEQ]] have "\<alpha>ah (map (\<alpha>nl fg) w1) \<le> \<alpha>ah (map (\<alpha>nl fg) wwl)" .
        finally show "h \<le> \<alpha>ah (map (\<alpha>nl fg) wwl)" .
      next
        from FS_FMT(1) show "(mon fg p, mon_w fg w) = \<alpha>nl fg eel" by auto
      next
        from IHAPP(2,3) have "(Ml \<union> Me) \<subseteq> mon_pl (map (\<alpha>nl fg) w1)" by (auto simp add: mon_pl_of_\<alpha>nl)
        also from mon_pl_ileq[OF le_list_map[OF ILEQ]] have "\<dots> \<subseteq> mon_pl (map (\<alpha>nl fg) wwl)" .
        finally show "(Ml \<union> Me) \<subseteq> mon_pl (map (\<alpha>nl fg) wwl)" .
      qed
    qed
    ultimately show ?thesis by blast
  next
    case right \<comment> \<open>@{term U} was reached from the spawned threads\<close>
    from cil_ileq[OF LESPLIT(1)] le_list_length[of "map ENV w2" "wwl"] have ILEQ: "map ENV w2\<preceq>wwl" and LEN: "length w2 \<le> length wwl" by (auto)
    from HVALID have CHVALID: "valid fg ch" "mon_s fg sh \<inter> mon_c fg ch = {}" by (auto simp add: valid_unconc)
      \<comment> \<open>We first identify the actual thread from that @{term U} was reached\<close>
    from ntr_reverse_split_atU[OF CHVALID(1) right LESPLIT(4)] obtain q wr cr' where RI: "[entry fg q] \<in># ch" "wr\<preceq>w2" "cr'\<subseteq>#c2'" "atU U cr'" "({#[entry fg q]#},wr,cr')\<in>trcl (ntr fg)" by (blast dest: CHFMT)
      \<comment> \<open>In order to apply the induction hypothesis, we have to convert the reaching path to loc/env semantics\<close>
    from ntrs.gtr2gtrp[where c="{#}", simplified, OF RI(5)] obtain sr' cre' wwr where RI_NTRP: "cr'=add_mset sr' cre'" "wr=map le_rem_s wwr" "(([entry fg q],{#}),wwr,(sr',cre'))\<in>trcl (ntrp fg)" by blast
    from LEN le_list_length[OF RI(2)] RI_NTRP(2) have LEN': "length wwr \<le> length wwl" by simp
    \<comment> \<open>The induction hypothesis yields a constraint system entry\<close>
    from Cons.hyps[OF LEN' RI_NTRP(3)] RI_NTRP(1) RI(4) obtain Ml Me h where IHAPP: "(entry fg q, Ml, Me, h)\<in>RU_cs fg U" "Ml \<subseteq> mon_loc fg wwr" "Me \<subseteq> mon_env fg wwr" "h \<le> \<alpha>ah (map (\<alpha>nl fg) wwr)" by auto 
    \<comment> \<open>We also have an entry in the same-level path constraint system that contains the thread from that @{term U} was reached\<close>
    from S_ENTRY_PAT[of "{#q#}", simplified] RI(1) have S_ENTRY: "(v, mon_w fg w, {#q#}) \<in> S_cs fg 1" by auto 
    \<comment> \<open>Before we can apply the  @{thm [source] RU_spawn}-constraint, we have to analyze the monitors\<close>
    have MON_MLE_ENV: "Ml \<union> Me \<subseteq> mon_env fg wwl" proof -
      from IHAPP(2,3) have "Ml \<union> Me \<subseteq> mon_loc fg wwr \<union> mon_env fg wwr" by auto
      also from mon_ww_of_le_rem[symmetric] RI_NTRP(2) have "\<dots> = mon_ww fg wr" by fastforce
      also from mon_env_ileq[OF ILEQ] mon_ww_ileq[OF RI(2)] have "\<dots> \<subseteq> mon_env fg wwl" by fastforce
      finally show ?thesis .
    qed
    have MON_UP_MLE: "(mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me) = {}" proof -
      from ntrp_mon_env_w_no_ctx[OF SPLIT(2)] FS_FMT(3,4) edges_part[OF FS_FMT(2)] have "(mon_n fg u \<union> mon fg p) \<inter> mon_env fg wwl = {}" by (auto simp add: mon_n_def)
      with MON_MLE_ENV show ?thesis by auto
    qed
    \<comment> \<open>Finally we can apply the @{thm [source] RU_spawn}-constraint that yields us an entry for the reaching path from @{term u}\<close>
    from RU_spawn[OF FS_FMT(2,4) S_ENTRY _ IHAPP(1) MON_UP_MLE] have "(u, mon fg p \<union> mon_w fg w, Ml \<union> Me, ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me)) \<in> RU_cs fg U" by simp 
    \<comment> \<open>Next we have to assemble the rest of the proposition\<close>
    moreover have "mon fg p \<union> mon_w fg w \<subseteq> mon_loc fg (eel#wwl)" using FS_FMT(1) by fastforce
    moreover have "Ml \<union> Me \<subseteq> mon_env fg (eel#wwl)" using MON_MLE_ENV by auto
    moreover have "ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me) \<le> \<alpha>ah (map (\<alpha>nl fg) (eel#wwl))" \<comment> \<open>Only the proposition about the acquisition histories needs some more work\<close>
    proof (simp add: ah_update_cons)
      have MAP_HELPER: "map (\<alpha>nl fg) wwr \<preceq> map (\<alpha>nl fg) wwl" proof -
        from RI_NTRP(2) have "map (\<alpha>nl fg) wwr = map (\<alpha>n fg) wr" by (simp add: \<alpha>n_\<alpha>nl)
        also from le_list_map[OF RI(2)] have "\<dots> \<preceq> map (\<alpha>n fg) w2" .
        also have "\<dots> = map (\<alpha>nl fg) (map ENV w2)" by simp
        also from le_list_map[OF ILEQ] have "\<dots> \<preceq> map (\<alpha>nl fg) wwl" .
        finally show "?thesis" .
      qed
      show "ah_update h (mon fg p, mon_w fg w) (Ml \<union> Me) \<le> ah_update (\<alpha>ah (map (\<alpha>nl fg) wwl)) (\<alpha>nl fg eel) (mon_pl (map (\<alpha>nl fg) wwl))" proof (rule ah_update_mono)
        from IHAPP(4) have "h \<le> \<alpha>ah (map (\<alpha>nl fg) wwr)" .
        also have "\<dots> \<le> \<alpha>ah (map (\<alpha>nl fg) wwl)" by (rule \<alpha>ah_ileq[OF MAP_HELPER])
        finally show "h \<le> \<alpha>ah (map (\<alpha>nl fg) wwl)" .
      next
        from FS_FMT(1) show "(mon fg p, mon_w fg w) = \<alpha>nl fg eel" by simp
      next
        from IHAPP(2,3) mon_pl_ileq[OF MAP_HELPER] show "Ml \<union> Me \<subseteq> mon_pl (map (\<alpha>nl fg) wwl)" by (auto simp add: mon_pl_of_\<alpha>nl)
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed


text \<open>
  Now we prove a statement about the precision of the least solution. As in the precision proof of the @{term "S_cs"} constraint system, we construct a path for the entry on the conclusion side of each constraint, assuming
  that there already exists paths for the entries mentioned in the antecedent.

  We show that each entry in the least solution corresponds exactly to some executable path, and is not just an under-approximation of a path; while for the soundness direction, we could only show that every executable path is 
  under-approximated. The reason for this is that in effect, the constraint system prunes the steps of threads that are not needed to reach the control point. However, each pruned path is executable. 
\<close>
lemma (in flowgraph) RU_precise: "(u,Ml,Me,h)\<in>RU_cs fg U 
  \<Longrightarrow> \<exists>w s' c'. 
    (([u],{#}),w,(s',c'))\<in>trcl (ntrp fg) \<and> 
    atU U ({#s'#}+c') \<and> 
    mon_loc fg w = Ml \<and> 
    mon_env fg w = Me \<and> 
    \<alpha>ah (map (\<alpha>nl fg) w) = h"
proof (induct rule: RU_cs.induct)
  \<comment> \<open>The @{text "RU_init"} constraint is trivially covered by the empty path\<close>
  case (RU_init u) thus ?case by (auto intro: exI[of _ "[]"]) 
next
  \<comment> \<open>Call constraint\<close>
  case (RU_call u p u' v M P Ml Me h) 
  then obtain w s' c' where IHAPP: "(([v], {#}), w, s', c') \<in> trcl (ntrp fg)" "atU U ({#s'#} + c')" "mon_loc fg w = Ml" "mon_env fg w = Me" "\<alpha>ah (map (\<alpha>nl fg) w) = h" by blast
  from RU_call.hyps(2) S_precise[OF RU_call.hyps(3), simplified] trss_bot_proc_const[where s="[]" and s'="[]", simplified] obtain wsl ch where 
    SLPATH: "(([entry fg p], {#}), wsl, [v], ch) \<in> trcl (trss fg)" "M = mon_w fg wsl" by fastforce
  from trss_c_cases[OF SLPATH(1), simplified] have CHFMT: "\<And>s. s \<in># ch \<Longrightarrow> \<exists>p. s = [entry fg p] \<and> (\<exists>u v. (u, Spawn p, v) \<in> edges fg) \<and> initialproc fg p" by blast
  with c_of_initial_no_mon have CHNOMON: "mon_c fg ch = {}" by blast
    \<comment> \<open>From the constraints prerequisites, we can construct the first step\<close>
  have FS: "(([u],{#}),LCall p#wsl,([v,u'],ch))\<in>ntrs fg" proof (rule ntrs_step[where r="[]", simplified])
    from RU_call.hyps(1) show "(([u], {#}), LCall p, [entry fg p, u'], {#}) \<in> trss fg" by (auto intro: trss_call)
  qed (rule SLPATH(1))
  hence FSP: "(([u],{#}),LOC (LCall p#wsl),([v,u'],ch))\<in>ntrp fg" by (blast intro: gtrp_loc) 
  also 
    \<comment> \<open>The rest of the path comes from the induction hypothesis, after adding the rest of the threads to the context\<close>
  have "(([v, u'], ch), w, s' @ [u'], c' + ch) \<in> trcl (ntrp fg)" proof (rule ntrp_add_context[OF ntrp_stack_comp[OF IHAPP(1), where r="[u']"], where cn=ch, simplified])
    from RU_call.hyps(1,6) IHAPP(4) show "mon_n fg u' \<inter> mon_env fg w = {}" by (auto simp add: mon_n_def edges_part)
    from CHNOMON show "mon_ww fg (map le_rem_s w) \<inter> mon_c fg ch = {}" by auto
  qed
  finally have "(([u], {#}), LOC (LCall p # wsl) # w, s' @ [u'], c' + ch) \<in> trcl (ntrp fg)" . 
    \<comment> \<open>It is straightforward to show that the new path satisfies the required properties for its monitors and acquisition history\<close>
  moreover from IHAPP(2) have "atU U ({# s'@[u'] #}+(c'+ch))" by auto
  moreover have "mon_loc fg (LOC (LCall p # wsl) # w) = mon fg p \<union> M \<union> Ml" using SLPATH(2) IHAPP(3) by auto
  moreover have "mon_env fg (LOC (LCall p # wsl) # w) = Me" using IHAPP(4) by auto
  moreover have "\<alpha>ah (map (\<alpha>nl fg) (LOC (LCall p # wsl) # w)) = ah_update h (mon fg p, M) (Ml \<union> Me)" proof -
    have "\<alpha>ah (map (\<alpha>nl fg) (LOC (LCall p # wsl) # w)) = ah_update (\<alpha>ah (map (\<alpha>nl fg) w)) (mon fg p, mon_w fg wsl) (mon_pl (map (\<alpha>nl fg) w))" by (auto simp add: ah_update_cons)
    also have "\<dots> = ah_update h (mon fg p, M) (Ml \<union> Me)" proof -
      from IHAPP(5) have "\<alpha>ah (map (\<alpha>nl fg) w) = h" .
      moreover from SLPATH(2) have "(mon fg p, mon_w fg wsl) = (mon fg p, M)" by (simp add: mon_pl_of_\<alpha>nl)
      moreover from IHAPP(3,4) have "mon_pl (map (\<alpha>nl fg) w) = Ml \<union> Me" by (auto simp add: mon_pl_of_\<alpha>nl)
      ultimately show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by blast
next
  \<comment> \<open>Spawn constraint\<close>
  case (RU_spawn u p u' v M P q Ml Me h) then obtain w s' c' where IHAPP: "(([entry fg q], {#}), w, s', c') \<in> trcl (ntrp fg)" "atU U ({#s'#} + c')" "mon_loc fg w = Ml" "mon_env fg w = Me" "\<alpha>ah (map (\<alpha>nl fg) w) = h" by blast
  from RU_spawn.hyps(2) S_precise[OF RU_spawn.hyps(3), simplified] trss_bot_proc_const[where s="[]" and s'="[]", simplified] obtain wsl ch where 
    SLPATH: "(([entry fg p], {#}), wsl, [v], ch) \<in> trcl (trss fg)" "M = mon_w fg wsl" "size P \<le> 1" "(\<lambda>p. [entry fg p]) `# P \<subseteq># ch" by fastforce
  with RU_spawn.hyps(4) obtain che where PFMT: "P={#q#}" "ch = {#[entry fg q]#} + che" by (auto elim!: mset_size_le1_cases mset_le_addE)
  from trss_c_cases[OF SLPATH(1), simplified] have CHFMT: "\<And>s. s \<in># ch \<Longrightarrow> \<exists>p. s = [entry fg p] \<and> (\<exists>u v. (u, Spawn p, v) \<in> edges fg) \<and> initialproc fg p" by blast
  with c_of_initial_no_mon have CHNOMON: "mon_c fg ch = {}" by blast
  have FS: "(([u],{#}),LCall p#wsl,([v,u'],ch))\<in>ntrs fg" proof (rule ntrs_step[where r="[]", simplified])
    from RU_spawn.hyps(1) show "(([u], {#}), LCall p, [entry fg p, u'], {#}) \<in> trss fg" by (auto intro: trss_call)
  qed (rule SLPATH(1))
  hence FSP: "(([u],{#}),LOC (LCall p#wsl),([v,u'],ch))\<in>ntrp fg" by (blast intro: gtrp_loc) 
  also have "(([v, u'], ch), map ENV (map le_rem_s w), [v,u'], che+({#s'#}+c')) \<in> trcl (ntrp fg)" proof -
    from IHAPP(3,4) have "mon_ww fg (map le_rem_s w) \<subseteq> Ml \<union> Me" by (auto simp add: mon_ww_of_le_rem)
    with RU_spawn.hyps(1,2,7) have "(mon_n fg v \<union> mon_n fg u') \<inter> mon_ww fg (map le_rem_s w) = {}" by (auto simp add: mon_n_def edges_part)
    with ntr2ntrp[OF gtrp2gtr[OF IHAPP(1)], of "[v,u']" che] PFMT(2) CHNOMON show ?thesis by (auto simp add: union_ac mon_c_unconc)
  qed
  finally have "(([u], {#}), LOC (LCall p # wsl) # map ENV (map le_rem_s w), [v, u'], che + ({#s'#} + c')) \<in> trcl (ntrp fg)" .
  moreover from IHAPP(2) have "atU U ({#[v,u']#} + (che+({#s'#} + c')))" by auto
  moreover have "mon_loc fg (LOC (LCall p # wsl) # map ENV (map le_rem_s w)) = mon fg p \<union> M" using SLPATH(2) by (auto simp del: map_map)
  moreover have "mon_env fg (LOC (LCall p # wsl) # map ENV (map le_rem_s w)) = Ml \<union> Me" using IHAPP(3,4) by (auto simp add: mon_ww_of_le_rem simp del: map_map)
  moreover have "\<alpha>ah (map (\<alpha>nl fg) (LOC (LCall p # wsl) # map ENV (map le_rem_s w))) = ah_update h (mon fg p, M) (Ml \<union> Me)" proof -
    have "\<alpha>ah (map (\<alpha>nl fg) (LOC (LCall p # wsl) # map ENV (map le_rem_s w))) = ah_update (\<alpha>ah (map (\<alpha>n fg) (map le_rem_s w))) (mon fg p, mon_w fg wsl) (mon_pl (map (\<alpha>n fg) (map le_rem_s w)))" by (simp add: ah_update_cons o_assoc)
    also have "\<dots> = ah_update h (mon fg p, M) (Ml \<union> Me)" proof -
      from IHAPP(5) have "\<alpha>ah (map (\<alpha>n fg) (map le_rem_s w)) = h" by (simp add: \<alpha>n_\<alpha>nl)
      moreover from SLPATH(2) have "(mon fg p, mon_w fg wsl) = (mon fg p, M)" by simp
      moreover from IHAPP(3,4) have "mon_pl (map (\<alpha>n fg) (map le_rem_s w)) = Ml \<union> Me" by (auto simp add: mon_pl_of_\<alpha>nl \<alpha>n_\<alpha>nl)
      ultimately show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by blast
qed


subsection "Simultaneously reaching path"
text \<open>
  In this section, we define a constraint system that collects abstract information for paths starting at a single control node and reaching two program points simultaneously, one from a set @{term U} and one from a set @{term V}.
\<close>

subsubsection "Constraint system"
text \<open>
  An element @{term "(u,Ml,Me)\<in>RUV_cs fg U V"} means, that there is a path from @{term "{#[u]#}"} to some configuration that is simultaneously at @{term U} and at @{term V}. 
  That path uses monitors from @{term Ml} in the first thread and monitors from @{term Me} in the other threads.
\<close>
inductive_set
  RUV_cs :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> 
             'n set \<Rightarrow> 'n set \<Rightarrow> ('n \<times> 'm set \<times> 'm set) set"
  for fg U V
where
    RUV_call: 
      "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 0; 
         (v,Ml,Me)\<in>RUV_cs fg U V; mon_n fg u \<inter> Me = {} \<rbrakk> 
      \<Longrightarrow> (u,mon fg p \<union> M \<union> Ml,Me)\<in>RUV_cs fg U V"
  | RUV_spawn: 
      "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 1; q \<in># P; 
         (entry fg q,Ml,Me)\<in>RUV_cs fg U V; 
         (mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me) = {} \<rbrakk> 
      \<Longrightarrow> (u, mon fg p \<union> M, Ml\<union>Me)\<in>RUV_cs fg U V"
  | RUV_split_le: 
      "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 1; q \<in># P; 
         (v,Ml,Me,h)\<in>RU_cs fg U; (entry fg q,Ml',Me',h')\<in>RU_cs fg V; 
         (mon_n fg u \<union> mon fg p) \<inter> (Me\<union>Ml'\<union>Me')={}; h [*] h' \<rbrakk> 
      \<Longrightarrow> (u, mon fg p \<union> M \<union> Ml, Me \<union> Ml' \<union> Me')\<in>RUV_cs fg U V"
  | RUV_split_el: 
      "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 1; q \<in># P; 
         (v,Ml,Me,h)\<in>RU_cs fg V; (entry fg q,Ml',Me',h')\<in>RU_cs fg U; 
         (mon_n fg u \<union> mon fg p) \<inter> (Me\<union>Ml'\<union>Me')={}; h [*] h' \<rbrakk> 
      \<Longrightarrow> (u, mon fg p \<union> M \<union> Ml, Me \<union> Ml' \<union> Me')\<in>RUV_cs fg U V"
  | RUV_split_ee: 
      "\<lbrakk> (u,Call p,u')\<in>edges fg; proc_of fg v = p; (v,M,P)\<in>S_cs fg 2; 
         {#q#}+{#q'#} \<subseteq># P;
         (entry fg q,Ml,Me,h)\<in>RU_cs fg U; (entry fg q',Ml',Me',h')\<in>RU_cs fg V; 
         (mon_n fg u \<union> mon fg p) \<inter> (Ml\<union>Me\<union>Ml'\<union>Me') = {}; h [*] h' \<rbrakk> 
      \<Longrightarrow> (u, mon fg p \<union> M, Ml\<union>Me\<union>Ml'\<union>Me')\<in>RUV_cs fg U V"

text \<open>
  The idea underlying this constraint system is similar to the @{term RU_cs}-constraint system for reaching a single node set. 
  Initially, we just track one thread. After a macrostep, we have a configuration consisting of the transformed initial thread and the spawned threads.
  From this configuration, we reach two nodes simultaneously, one in @{term U} and one in @{term V}. Each of these nodes is reached by just a single thread. The constraint system
  contains one constraint for each case how these threads are related to the initial and the spawned threads:

  \begin{description}
    \item[RUV\_call] Both, @{term U} and @{term V} are reached from the initial thread.
    \item[RUV\_spawn] Both, @{term U} and @{term V} are reached from a single spawned thread.
    \item[RUV\_split\_le] @{term U} is reached from the initial thread, @{term V} is reached from a spawned thread.
    \item[RUV\_split\_el] @{term V} is reached from the initial thread, @{term U} is reached from a spawned thread.
    \item[RUV\_split\_ee] Both, @{term U} and @{term V} are reached from different spawned threads.
  \end{description}

  In the latter three cases, we have to analyze the interleaving of two paths each reaching a single control node. This is done via the acquisition history
  information that we collected in the @{term RU_cs}-constraint system.

  Note that we do not need an initializing constraint for the empty path, as a single configuration cannot simultaneously be at two control nodes.
\<close>

subsubsection \<open>Soundness and precision\<close>

lemma (in flowgraph) RUV_sound: "!!u s' c'. 
  \<lbrakk> (([u],{#}),w,(s',c'))\<in>trcl (ntrp fg); atUV U V ({#s'#}+c') \<rbrakk> 
  \<Longrightarrow> \<exists>Ml Me. 
    (u,Ml,Me)\<in>RUV_cs fg U V \<and> 
    Ml \<subseteq> mon_loc fg w \<and> 
    Me \<subseteq> mon_env fg w"
\<comment> \<open>The soundness proof is done by induction over the length of the reaching path\<close>
proof (induct w rule: length_compl_induct)
  \<comment> \<open>In case of the empty path, a contradiction follows because a single-thread configuration cannot simultaneously be at two control nodes\<close>
  case Nil hence False by simp thus ?case .. 
next
  case (Cons ee ww) then obtain sh ch where SPLIT: "(([u],{#}),ee,(sh,ch))\<in>ntrp fg" "((sh,ch),ww,(s',c'))\<in>trcl (ntrp fg)" by (fast dest: trcl_uncons)
  from ntrp_split[where ?c1.0="{#}", simplified, OF SPLIT(2) ntrp_valid_preserve_s[OF SPLIT(1)], simplified] obtain w1 w2 c1' c2' where 
    LESPLIT: "ww \<in> w1 \<otimes>\<^bsub>\<alpha>nl fg\<^esub> map ENV w2" "c' = c1' + c2'" "((sh, {#}), w1, s', c1') \<in> trcl (ntrp fg)" "(ch, w2, c2') \<in> trcl (ntr fg)" "mon_ww fg (map le_rem_s w1) \<inter> mon_c fg ch = {}" "mon_ww fg w2 \<inter> mon_s fg sh = {}"
    by blast
  obtain p u' v w where 
    FS_FMT: "ee = LOC (LCall p # w)" "(u, Call p, u') \<in> edges fg" "sh = [v, u']" "proc_of fg v = p" "mon_c fg ch = {}" 
    and CHFMT: "\<And>s. s \<in># ch \<Longrightarrow> \<exists>p u v. s = [entry fg p] \<and> (u, Spawn p, v) \<in> edges fg \<and> initialproc fg p"
    and S_ENTRY_PAT: "\<And>P. (\<lambda>p. [entry fg p]) `# P \<subseteq># ch \<Longrightarrow> (v, mon_w fg w, P) \<in> S_cs fg (size P)"
    by (rule S_sound_ntrp[OF SPLIT(1)]) blast
  from ntrp_mon_env_w_no_ctx[OF SPLIT(2)] FS_FMT(3,4) edges_part[OF FS_FMT(2)] have MON_PU: "mon_env fg ww \<inter> (mon fg p \<union> mon_n fg u) = {}" by (auto simp add: mon_n_def)
  from cil_ileq[OF LESPLIT(1)] mon_loc_ileq[of w1 ww fg] mon_env_ileq[of w1 ww fg] have MON1_LEQ: "mon_loc fg w1 \<subseteq> mon_loc fg ww" "mon_env fg w1 \<subseteq> mon_env fg ww" by auto
  from cil_ileq[OF LESPLIT(1)] mon_env_ileq[of "map ENV w2" ww fg] have MON2_LEQ: "mon_ww fg w2 \<subseteq> mon_env fg ww" by simp
  from LESPLIT(3) FS_FMT(3) ntrp_stack_decomp[of v "[]" "[u']" "{#}" w1 s' c1', simplified] obtain v' rr where DECOMP_LOC: "s'=v'#rr@[u']" "(([v],{#}),w1,(v'#rr,c1'))\<in>trcl (ntrp fg)" by (simp, blast)
  from Cons.prems(2) LESPLIT(2) have "atUV U V (({#s'#}+c1') + c2')" by (simp add: union_ac)
  thus ?case proof (cases rule: atUV_union_cases)
    case left with DECOMP_LOC(1) have ATUV: "atUV U V ({# v'#rr #}+c1')" by simp
    from Cons.hyps[OF _ DECOMP_LOC(2) ATUV] cil_length[OF LESPLIT(1)] obtain Ml Me where IHAPP: "(v, Ml, Me) \<in> RUV_cs fg U V" "Ml \<subseteq> mon_loc fg w1" "Me \<subseteq> mon_env fg w1" by auto
    from RUV_call[OF FS_FMT(2,4) S_ENTRY_PAT[of "{#}", simplified] IHAPP(1)] have "(u, mon fg p \<union> mon_w fg w \<union> Ml, Me) \<in> RUV_cs fg U V" using IHAPP(3) MON_PU MON1_LEQ by fastforce
    moreover have "mon fg p \<union> mon_w fg w \<union> Ml \<subseteq> mon_loc fg (ee#ww)" using FS_FMT(1) IHAPP(2) MON1_LEQ by auto
    moreover have "Me \<subseteq> mon_env fg (ee#ww)" using IHAPP(3) MON1_LEQ by auto
    ultimately show ?thesis by blast
  next
    case right \<comment> \<open>Both nodes are reached from the spawned threads, we have to further distinguish whether both nodes are reached from the same thread or from different threads\<close>
    then obtain s1' s2' where R_STACKS: "{#s1'#}+{#s2'#} \<subseteq># c2'" "atU_s U s1'" "atU_s V s2'" by (unfold atUV_def) auto
    then obtain ce2' where C2'FMT: "c2'={#s1'#}+({#s2'#}+ce2')" by (auto simp add: mset_subset_eq_exists_conv union_ac)
    obtain q ceh w21 w22 ce21' ce22' where 
      REVSPLIT: "ch={#[entry fg q]#}+ceh" "add_mset s2' ce2' = ce21'+ce22'" "w2\<in>w21\<otimes>\<^bsub>\<alpha>n fg\<^esub>w22" "mon fg q \<inter> (mon_c fg ceh \<union> mon_ww fg w22)={}" "mon_c fg ceh \<inter> (mon fg q \<union> mon_ww fg w21) = {}"
      "({#[entry fg q]#},w21,{#s1'#}+ce21')\<in>trcl (ntr fg)" "(ceh,w22,ce22')\<in>trcl (ntr fg)" 
    proof -
      from ntr_reverse_split[of ch w2 s1' "{#s2'#}+ce2'"] ntrp_valid_preserve_s[OF SPLIT(1), simplified] C2'FMT LESPLIT(4)
      obtain seh ceh w21 w22 ce21' ce22' where 
        *: "ch={#seh#}+ceh" "{#s2'#}+ce2' = ce21'+ce22'" "w2\<in>w21\<otimes>\<^bsub>\<alpha>n fg\<^esub>w22" "mon_s fg seh \<inter> (mon_c fg ceh \<union> mon_ww fg w22)={}" "mon_c fg ceh \<inter> (mon_s fg seh \<union> mon_ww fg w21) = {}"
        "({#seh#},w21,{#s1'#}+ce21')\<in>trcl (ntr fg)" "(ceh,w22,ce22')\<in>trcl (ntr fg)" by (auto simp add: valid_unconc)
      from this(1) CHFMT[of seh] obtain q where "seh=[entry fg q]" by auto
      with * have "ch={#[entry fg q]#}+ceh" "add_mset s2' ce2' = ce21'+ce22'" "w2\<in>w21\<otimes>\<^bsub>\<alpha>n fg\<^esub>w22" "mon fg q \<inter> (mon_c fg ceh \<union> mon_ww fg w22)={}" "mon_c fg ceh \<inter> (mon fg q \<union> mon_ww fg w21) = {}"
        "({#[entry fg q]#},w21,{#s1'#}+ce21')\<in>trcl (ntr fg)" "(ceh,w22,ce22')\<in>trcl (ntr fg)" by auto
      thus thesis using that by (blast)
    qed
        \<comment> \<open>For applying the induction hypothesis, it will be handy to have the reaching path in loc/env format:\<close>
    from ntrs.gtr2gtrp[where c="{#}", simplified, OF REVSPLIT(6)] obtain sq' csp_q ww21 where 
      R_CONV: "add_mset s1' ce21' = add_mset sq' csp_q" "w21 = map le_rem_s ww21" "(([entry fg q], {#}), ww21, sq', csp_q) \<in> trcl (ntrp fg)" by auto  
    from cil_ileq[OF REVSPLIT(3)] mon_ww_ileq[of w21 w2 fg] mon_ww_ileq[of w22 w2 fg] have MON2N_LEQ: "mon_ww fg w21 \<subseteq> mon_ww fg w2" "mon_ww fg w22 \<subseteq> mon_ww fg w2" by auto
    from REVSPLIT(2) show ?thesis proof (cases rule: mset_unplusm_dist_cases[case_names left' right'])
      case left' \<comment> \<open>Both nodes are reached from the same thread\<close>
      have ATUV: "atUV U V ({#sq'#}+csp_q)" using right C2'FMT R_STACKS(2,3) left'(1)
        by (metis R_CONV(1) add_mset_add_single atUV_union atU_add_mset union_commute)
      from Cons.hyps[OF _ R_CONV(3) ATUV] cil_length[OF REVSPLIT(3)] cil_length[OF LESPLIT(1)] R_CONV(2) obtain Ml Me where IHAPP: "(entry fg q, Ml, Me) \<in> RUV_cs fg U V" "Ml \<subseteq> mon_loc fg ww21" "Me \<subseteq> mon_env fg ww21" by auto
      from REVSPLIT(1) S_ENTRY_PAT[of "{#q#}", simplified] have S_ENTRY: "(v, mon_w fg w, {#q#}) \<in> S_cs fg 1" by simp
      have MON_COND: "(mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me) = {}" proof -
        from R_CONV(2) have "mon_ww fg w21 = mon_loc fg ww21 \<union> mon_env fg ww21" by (simp add: mon_ww_of_le_rem)
        with IHAPP(2,3) MON2N_LEQ(1) MON_PU MON2_LEQ show ?thesis by blast
      qed
      from RUV_spawn[OF FS_FMT(2) FS_FMT(4) S_ENTRY _ IHAPP(1) MON_COND] have "(u, mon fg p \<union> mon_w fg w, Ml \<union> Me) \<in> RUV_cs fg U V" by simp
      moreover have "mon fg p \<union> mon_w fg w \<subseteq> mon_loc fg (ee#ww)" using FS_FMT(1) by auto
      moreover have "Ml \<union> Me \<subseteq> mon_env fg (ee#ww)" using IHAPP(2,3) R_CONV(2) MON2N_LEQ(1) MON2_LEQ by (auto simp add: mon_ww_of_le_rem)
      ultimately show ?thesis by blast
    next
      (* TODO: Clean up monitor arguments *)
      case right' \<comment> \<open>The nodes are reached from different threads\<close>
      from R_STACKS(2,3) have ATUV: "atU U (add_mset sq' csp_q)" "atU V ce22'" by (-) (subst R_CONV(1)[symmetric], simp, subst right'(1), simp)
      \<comment> \<open>We have to reverse-split the second path again, to extract the second interesting thread\<close>
      obtain q' w22' ce22e' where REVSPLIT': "[entry fg q'] \<in># ceh" "w22'\<preceq>w22" "ce22e' \<subseteq># ce22'" "atU V ce22e'" "({#[entry fg q']#},w22',ce22e')\<in>trcl (ntr fg)"
      proof -
        from ntr_reverse_split_atU[OF _ ATUV(2) REVSPLIT(7)] ntrp_valid_preserve_s[OF SPLIT(1), simplified] REVSPLIT(1) obtain sq'' w22' ce22e' where 
          *: "sq'' \<in># ceh" "w22'\<preceq>w22" "ce22e' \<subseteq># ce22'" "atU V ce22e'" "({#sq''#},w22',ce22e')\<in>trcl (ntr fg)" by (auto simp add: valid_unconc)
        from CHFMT[of sq''] REVSPLIT(1) this(1) obtain q' where "sq''=[entry fg q']" by auto 
        with * show thesis using that by blast 
      qed
      from ntrs.gtr2gtrp[where c="{#}", simplified, OF REVSPLIT'(5)] obtain sq'' ce22ee' ww22' where R_CONV': "ce22e' = add_mset sq'' ce22ee'" "w22'=map le_rem_s ww22'" "(([entry fg q'],{#}),ww22',(sq'',ce22ee'))\<in>trcl (ntrp fg)" by blast
      \<comment> \<open>From the soundness of the RU-constraint system, we get the corresponding entries\<close>
      from RU_sound[OF R_CONV(3) ATUV(1)] obtain Ml Me h where RU: "(entry fg q, Ml, Me, h) \<in> RU_cs fg U" "Ml \<subseteq> mon_loc fg ww21" "Me \<subseteq> mon_env fg ww21" "h \<le> \<alpha>ah (map (\<alpha>nl fg) ww21)" by blast
      from RU_sound[OF R_CONV'(3), of V] REVSPLIT'(4) R_CONV'(1) obtain Ml' Me' h' where RV: "(entry fg q', Ml', Me', h') \<in> RU_cs fg V" "Ml' \<subseteq> mon_loc fg ww22'" "Me' \<subseteq> mon_env fg ww22'" "h' \<le> \<alpha>ah (map (\<alpha>nl fg) ww22')" by auto 
      from S_ENTRY_PAT[of "{#q#}+{#q'#}", simplified] REVSPLIT(1) REVSPLIT'(1) have S_ENTRY: "(v, mon_w fg w, {#q#} + {#q'#}) \<in> S_cs fg (2::nat)" by (simp add: numerals)
      have "(u, mon fg p \<union> mon_w fg w, Ml \<union> Me \<union> Ml' \<union> Me') \<in> RUV_cs fg U V" proof (rule RUV_split_ee[OF FS_FMT(2,4) S_ENTRY _ RU(1) RV(1)])
        from MON_PU MON2_LEQ MON2N_LEQ R_CONV(2) R_CONV'(2) mon_ww_ileq[OF REVSPLIT'(2), of fg] RU(2,3) RV(2,3) show "(mon_n fg u \<union> mon fg p) \<inter> (Ml \<union> Me \<union> Ml' \<union> Me') = {}" by (simp add: mon_ww_of_le_rem) blast
      next
        from ah_interleavable1[OF REVSPLIT(3)] have "\<alpha>ah (map (\<alpha>n fg) w21) [*] \<alpha>ah (map (\<alpha>n fg) w22)" .
        thus "h [*] h'" 
        proof (erule_tac ah_leq_il)
          note RU(4)
          also have "map (\<alpha>nl fg) ww21 \<preceq> map (\<alpha>n fg) w21" using R_CONV(2) by (simp add: \<alpha>n_\<alpha>nl)
          hence "\<alpha>ah (map (\<alpha>nl fg) ww21) \<le> \<alpha>ah (map (\<alpha>n fg) w21)" by (rule \<alpha>ah_ileq)
          finally show "h \<le> \<alpha>ah (map (\<alpha>n fg) w21)" .
        next
          note RV(4)
          also have "map (\<alpha>nl fg) ww22' \<preceq> map (\<alpha>n fg) w22" using R_CONV'(2) REVSPLIT'(2) by (simp add: \<alpha>n_\<alpha>nl[symmetric] le_list_map map_map[symmetric] del: map_map)
          hence "\<alpha>ah (map (\<alpha>nl fg) ww22') \<le> \<alpha>ah (map (\<alpha>n fg) w22)" by (rule \<alpha>ah_ileq)
          finally show "h' \<le> \<alpha>ah (map (\<alpha>n fg) w22)" .
        qed
      qed (simp)
      moreover have "mon fg p \<union> mon_w fg w \<subseteq> mon_loc fg (ee#ww)" using FS_FMT(1) by auto
      moreover have "Ml \<union> Me \<union> Ml' \<union> Me' \<subseteq> mon_env fg (ee#ww)" using RV(2,3) RU(2,3) mon_ww_ileq[OF REVSPLIT'(2), of fg] MON2N_LEQ R_CONV(2) R_CONV'(2) MON2_LEQ by (simp add: mon_ww_of_le_rem) blast
      ultimately show ?thesis by blast
    qed
  next
    case lr \<comment> \<open>The first node is reached from the local thread, the second one from a spawned thread\<close>
    from RU_sound[OF DECOMP_LOC(2), of U] lr(1) DECOMP_LOC(1) obtain Ml Me h where RU: "(v, Ml, Me, h) \<in> RU_cs fg U" "Ml \<subseteq> mon_loc fg w1" "Me \<subseteq> mon_env fg w1" "h \<le> \<alpha>ah (map (\<alpha>nl fg) w1)" by auto
    obtain Ml' Me' h' q' where RV: "[entry fg q'] \<in># ch" "(entry fg q', Ml', Me', h') \<in> RU_cs fg V" "Ml' \<subseteq> mon_ww fg w2" "Me' \<subseteq> mon_ww fg w2" "h' \<le> \<alpha>ah (map (\<alpha>n fg) w2)"
    proof -
      \<comment> \<open>We have to extract the interesting thread from the spawned threads in order to get an entry in @{term "RU fg V"}\<close>
      obtain q' w2' c2i' where REVSPLIT: "[entry fg q'] \<in># ch" "w2'\<preceq>w2" "c2i' \<subseteq># c2'" "atU V c2i'" "({#[entry fg q']#},w2',c2i')\<in>trcl (ntr fg)"
        using ntr_reverse_split_atU[OF _ lr(2) LESPLIT(4)] ntrp_valid_preserve_s[OF SPLIT(1), simplified] CHFMT by (simp add: valid_unconc) blast
      from ntrs.gtr2gtrp[where c="{#}", simplified, OF REVSPLIT(5)] obtain s2i' c2ie' ww2' where R_CONV: "c2i'=add_mset s2i' c2ie'" "w2'=map le_rem_s ww2'" "(([entry fg q'], {#}), ww2', s2i', c2ie') \<in> trcl (ntrp fg)" .
      from RU_sound[OF R_CONV(3), of V] REVSPLIT(4) R_CONV(1) obtain Ml' Me' h' where RV: "(entry fg q', Ml', Me', h') \<in> RU_cs fg V" "Ml' \<subseteq> mon_loc fg ww2'" "Me' \<subseteq> mon_env fg ww2'" "h' \<le> \<alpha>ah (map (\<alpha>nl fg) ww2')" by auto
      moreover have "mon_loc fg ww2' \<subseteq> mon_ww fg w2" "mon_env fg ww2' \<subseteq> mon_ww fg w2" using mon_ww_ileq[OF REVSPLIT(2), of fg] R_CONV(2) by (auto simp add: mon_ww_of_le_rem)
      moreover have "\<alpha>ah (map (\<alpha>nl fg) ww2') \<le> \<alpha>ah (map (\<alpha>n fg) w2)" using REVSPLIT(2) R_CONV(2) by (auto simp add: \<alpha>n_\<alpha>nl[symmetric] le_list_map map_map[symmetric] simp del: map_map intro: \<alpha>ah_ileq del: predicate2I)
      ultimately show thesis using that REVSPLIT(1) by (blast intro: order_trans)
    qed
    from S_ENTRY_PAT[of "{#q'#}", simplified] RV(1) have S_ENTRY: "(v, mon_w fg w, {#q'#}) \<in> S_cs fg 1" by simp
    have "(u, mon fg p \<union> mon_w fg w \<union> Ml, Me \<union> Ml' \<union> Me') \<in> RUV_cs fg U V" proof (rule RUV_split_le[OF FS_FMT(2,4) S_ENTRY _ RU(1) RV(2)])
      from MON_PU MON1_LEQ MON2_LEQ RU(3) RV(3,4) show "(mon_n fg u \<union> mon fg p) \<inter> (Me \<union> Ml' \<union> Me') = {}" by blast
    next
      from ah_interleavable1[OF LESPLIT(1)] have "\<alpha>ah (map (\<alpha>nl fg) w1) [*] \<alpha>ah (map (\<alpha>n fg) w2)" by simp
      thus "h [*] h'" using RU(4) RV(5) by (auto elim: ah_leq_il) 
    qed (simp)
    moreover have "mon fg p \<union> mon_w fg w \<union> Ml \<subseteq> mon_loc fg (ee # ww)" using FS_FMT(1) MON1_LEQ RU(2) by (simp) blast
    moreover have "Me \<union> Ml' \<union> Me' \<subseteq> mon_env fg (ee # ww)" using MON1_LEQ MON2_LEQ RU(3) RV(3,4) by (simp) blast
    ultimately show ?thesis by blast
  next
    case rl \<comment> \<open>The second node is reached from the local thread, the first one from a spawned thread. This case is symmetric to the previous one\<close>
    from RU_sound[OF DECOMP_LOC(2), of V] rl(1) DECOMP_LOC(1) obtain Ml Me h where RV: "(v, Ml, Me, h) \<in> RU_cs fg V" "Ml \<subseteq> mon_loc fg w1" "Me \<subseteq> mon_env fg w1" "h \<le> \<alpha>ah (map (\<alpha>nl fg) w1)" by auto
    obtain Ml' Me' h' q' where RU: "[entry fg q'] \<in># ch" "(entry fg q', Ml', Me', h') \<in> RU_cs fg U" "Ml' \<subseteq> mon_ww fg w2" "Me' \<subseteq> mon_ww fg w2" "h' \<le> \<alpha>ah (map (\<alpha>n fg) w2)"
    proof -
      \<comment> \<open>We have to extract the interesting thread from the spawned threads in order to get an entry in @{term "RU fg V"}\<close>
      obtain q' w2' c2i' where REVSPLIT: "[entry fg q'] \<in># ch" "w2'\<preceq>w2" "c2i' \<subseteq># c2'" "atU U c2i'" "({#[entry fg q']#},w2',c2i')\<in>trcl (ntr fg)"
        using ntr_reverse_split_atU[OF _ rl(2) LESPLIT(4)] ntrp_valid_preserve_s[OF SPLIT(1), simplified] CHFMT by (simp add: valid_unconc) blast
      from ntrs.gtr2gtrp[where c="{#}", simplified, OF REVSPLIT(5)] obtain s2i' c2ie' ww2' where R_CONV: "c2i'=add_mset s2i' c2ie'" "w2'=map le_rem_s ww2'" "(([entry fg q'], {#}), ww2', s2i', c2ie') \<in> trcl (ntrp fg)" .
      from RU_sound[OF R_CONV(3), of U] REVSPLIT(4) R_CONV(1) obtain Ml' Me' h' where RU: "(entry fg q', Ml', Me', h') \<in> RU_cs fg U" "Ml' \<subseteq> mon_loc fg ww2'" "Me' \<subseteq> mon_env fg ww2'" "h' \<le> \<alpha>ah (map (\<alpha>nl fg) ww2')" by auto
      moreover have "mon_loc fg ww2' \<subseteq> mon_ww fg w2" "mon_env fg ww2' \<subseteq> mon_ww fg w2" using mon_ww_ileq[OF REVSPLIT(2), of fg] R_CONV(2) by (auto simp add: mon_ww_of_le_rem)
      moreover have "\<alpha>ah (map (\<alpha>nl fg) ww2') \<le> \<alpha>ah (map (\<alpha>n fg) w2)" using REVSPLIT(2) R_CONV(2) by (auto simp add: \<alpha>n_\<alpha>nl[symmetric] le_list_map map_map[symmetric] simp del: map_map intro: \<alpha>ah_ileq del: predicate2I)
      ultimately show thesis using that REVSPLIT(1) by (blast intro: order_trans)
    qed
    from S_ENTRY_PAT[of "{#q'#}", simplified] RU(1) have S_ENTRY: "(v, mon_w fg w, {#q'#}) \<in> S_cs fg 1" by simp
    have "(u, mon fg p \<union> mon_w fg w \<union> Ml, Me \<union> Ml' \<union> Me') \<in> RUV_cs fg U V" proof (rule RUV_split_el[OF FS_FMT(2,4) S_ENTRY _ RV(1) RU(2)])
      from MON_PU MON1_LEQ MON2_LEQ RV(3) RU(3,4) show "(mon_n fg u \<union> mon fg p) \<inter> (Me \<union> Ml' \<union> Me') = {}" by blast
    next
      from ah_interleavable1[OF LESPLIT(1)] have "\<alpha>ah (map (\<alpha>nl fg) w1) [*] \<alpha>ah (map (\<alpha>n fg) w2)" by simp
      thus "h [*] h'" using RV(4) RU(5) by (auto elim: ah_leq_il) 
    qed (simp)
    moreover have "mon fg p \<union> mon_w fg w \<union> Ml \<subseteq> mon_loc fg (ee # ww)" using FS_FMT(1) MON1_LEQ RV(2) by (simp) blast
    moreover have "Me \<union> Ml' \<union> Me' \<subseteq> mon_env fg (ee # ww)" using MON1_LEQ MON2_LEQ RV(3) RU(3,4) by (simp) blast
    ultimately show ?thesis by blast
  qed
qed
   
lemma (in flowgraph) RUV_precise: "(u,Ml,Me)\<in>RUV_cs fg U V 
  \<Longrightarrow> \<exists>w s' c'. 
    (([u],{#}),w,(s',c'))\<in>trcl (ntrp fg) \<and> 
    atUV U V ({#s'#}+c') \<and> 
    mon_loc fg w = Ml \<and> 
    mon_env fg w = Me"
proof (induct rule: RUV_cs.induct)
  case (RUV_call u p u' v M P Ml Me) then obtain ww s' c' where IH: "(([v], {#}), ww, s', c') \<in> trcl (ntrp fg)" "atUV U V ({#s'#} + c')" "mon_loc fg ww = Ml" "mon_env fg ww = Me" by blast
  from S_precise_ntrp[OF RUV_call(3,2,1), simplified] obtain w ch where FS: "(([u], {#}), LOC (LCall p # w), [v, u'], ch) \<in> ntrp fg" "P = {#}" "M = mon_w fg w"  "mon_n fg v = mon fg p" "mon_c fg ch = {}" by blast
  note FS(1)
  also have "(([v, u'], ch), ww, s' @ [u'], c' + ch) \<in> trcl (ntrp fg)" 
    using ntrp_add_context[OF ntrp_stack_comp[OF IH(1), of "[u']"], of ch, simplified] FS(5) IH(4) RUV_call.hyps(6) mon_n_same_proc[OF edges_part[OF RUV_call.hyps(1)]] by simp
  finally have "(([u], {#}), LOC (LCall p # w) # ww, s' @ [u'], c' + ch) \<in> trcl (ntrp fg)" .
  moreover from IH(2) have "atUV U V ({#s' @ [u']#}+(c'+ch))" by auto
  moreover have "mon_loc fg (LOC (LCall p # w) # ww) = mon fg p \<union> M \<union> Ml" using IH(3) FS(3) by auto
  moreover have "mon_env fg (LOC (LCall p # w) # ww) = Me" using IH(4) by auto
  ultimately show ?case by blast
next
  case (RUV_spawn u p u' v M P q Ml Me) then obtain ww s' c' where IH: "(([entry fg q], {#}), ww, s', c') \<in> trcl (ntrp fg)" "atUV U V ({#s'#} + c')" "mon_loc fg ww = Ml" "mon_env fg ww = Me" by blast
  from S_precise_ntrp[OF RUV_spawn(3,2,1), simplified] mset_size1elem[OF _ RUV_spawn(4)] obtain w che where 
    FS: "(([u], {#}), LOC (LCall p # w), [v, u'], {#[entry fg q]#} + che) \<in> ntrp fg" "P={#q#}" "M = mon_w fg w" "mon_n fg v = mon fg p" "mon_c fg ({#[entry fg q]#}+che) = {}" by (auto elim: mset_le_addE)
  moreover
  have "(([v, u'], che + {#[entry fg q]#}), map ENV (map le_rem_s ww), ([v,u'],che+({#s'#} + c')))\<in>trcl (ntrp fg)" 
    using ntr2ntrp[OF gtrp2gtr[OF IH(1)], of "[v,u']" che] IH(3,4) RUV_spawn(7) FS(4,5) mon_n_same_proc[OF edges_part[OF RUV_spawn(1)]]
    by (auto simp add: mon_c_unconc mon_ww_of_le_rem)
  ultimately have "(([u], {#}), LOC (LCall p # w) # map ENV (map le_rem_s ww), ([v,u'],che+({#s'#} + c'))) \<in> trcl (ntrp fg)" by (auto simp add: union_ac)
  moreover have "atUV U V ({#[v,u']#} + (che+({#s'#} + c')))" using IH(2) by auto
  moreover have "mon_loc fg (LOC (LCall p # w) # map ENV (map le_rem_s ww)) = mon fg p \<union> M" using FS(3) by (simp del: map_map)
  moreover have "mon_env fg (LOC (LCall p # w) # map ENV (map le_rem_s ww)) = Ml \<union> Me" using IH(3,4) by (auto simp add: mon_ww_of_le_rem simp del: map_map)
  ultimately show ?case by blast
next
  case (RUV_split_le u p u' v M P q Ml Me h Ml' Me' h')
  \<comment> \<open>Get paths from precision results\<close>
  from S_precise_ntrp[OF RUV_split_le(3,2,1), simplified] mset_size1elem[OF _ RUV_split_le(4)] obtain w che where 
    FS: "(([u], {#}), LOC (LCall p # w), [v, u'], {#[entry fg q]#} + che) \<in> ntrp fg" "P={#q#}" "M = mon_w fg w" "mon_n fg v = mon fg p" "mon_c fg ({#[entry fg q]#}+che) = {}" by (auto elim: mset_le_addE)
  from RU_precise[OF RUV_split_le(5)] obtain ww1 s1' c1' where P1: "(([v], {#}), ww1, s1', c1') \<in> trcl (ntrp fg)" "atU U ({#s1'#} + c1')" "mon_loc fg ww1 = Ml" "mon_env fg ww1 = Me" "\<alpha>ah (map (\<alpha>nl fg) ww1) = h" by blast
  from RU_precise[OF RUV_split_le(6)] obtain ww2 s2' c2' where P2: "(([entry fg q], {#}), ww2, s2', c2') \<in> trcl (ntrp fg)" "atU V ({#s2'#} + c2')" "mon_loc fg ww2 = Ml'" "mon_env fg ww2 = Me'" "\<alpha>ah (map (\<alpha>nl fg) ww2) = h'" by blast
  \<comment> \<open>Get combined path from the acquisition history interleavability, need to remap loc/env-steps in second path\<close>
  from P2(5) have "\<alpha>ah (map (\<alpha>nl fg) (map ENV (map le_rem_s ww2))) = h'" by (simp add: \<alpha>n_\<alpha>nl o_assoc)
  with P1(5) RUV_split_le(8) obtain ww where IL: "ww\<in>ww1\<otimes>\<^bsub>\<alpha>nl fg\<^esub>(map ENV (map le_rem_s ww2))" using ah_interleavable2 by (force)
  \<comment> \<open>Use the @{thm [source] ntrp_unsplit}-theorem to combine the executions\<close>
  from ntrp_unsplit[where ca="{#}",OF IL P1(1) gtrp2gtr[OF P2(1)], simplified] have "(([v], {#[entry fg q]#}), ww, s1', c1' + ({#s2'#} + c2')) \<in> trcl (ntrp fg)" 
    using FS(4,5) RUV_split_le(7)
    by (auto simp add: mon_c_unconc mon_ww_of_le_rem P2(3,4))
  from ntrp_add_context[OF ntrp_stack_comp[OF this, of "[u']"], of che] have "(([v] @ [u'], {#[entry fg q]#} + che), ww, s1' @ [u'], c1' + ({#s2'#} + c2') + che) \<in> trcl (ntrp fg)"
    using mon_n_same_proc[OF edges_part[OF RUV_split_le(1)]] mon_loc_cil[OF IL, of fg] mon_env_cil[OF IL, of fg] FS(4,5) RUV_split_le(7) by (auto simp add: mon_c_unconc P1(3,4) P2(3,4) mon_ww_of_le_rem simp del: map_map)
  with FS(1) have "(([u], {#}), LOC (LCall p # w) # ww, (s1' @ [u'], c1' + ({#s2'#} + c2') + che))\<in>trcl (ntrp fg)" by simp
  moreover have "atUV U V ({#s1' @ [u']#}+(c1' + ({#s2'#} + c2') + che))" using P1(2) P2(2) by auto
  moreover have "mon_loc fg (LOC (LCall p # w) # ww) = mon fg p \<union> M \<union> Ml" using FS(3) P1(3) mon_loc_cil[OF IL, of fg] by (auto simp del: map_map)
  moreover have "mon_env fg (LOC (LCall p # w) # ww) = Me \<union> Ml' \<union> Me'" using P1(4) P2(3,4) mon_env_cil[OF IL, of fg] by (auto simp add: mon_ww_of_le_rem simp del: map_map)
  ultimately show ?case by blast
next
  case (RUV_split_el u p u' v M P q Ml Me h Ml' Me' h') \<comment> \<open>This is the symmetric case to @{text "RUV_split_le"}, it is proved completely analogously, just need to swap @{text U} and @{text V}.\<close>
  \<comment> \<open>Get paths from precision results\<close>
  from S_precise_ntrp[OF RUV_split_el(3,2,1), simplified] mset_size1elem[OF _ RUV_split_el(4)] obtain w che where 
    FS: "(([u], {#}), LOC (LCall p # w), [v, u'], {#[entry fg q]#} + che) \<in> ntrp fg" "P={#q#}" "M = mon_w fg w" "mon_n fg v = mon fg p" "mon_c fg ({#[entry fg q]#}+che) = {}" by (auto elim: mset_le_addE)
  from RU_precise[OF RUV_split_el(5)] obtain ww1 s1' c1' where P1: "(([v], {#}), ww1, s1', c1') \<in> trcl (ntrp fg)" "atU V ({#s1'#} + c1')" "mon_loc fg ww1 = Ml" "mon_env fg ww1 = Me" "\<alpha>ah (map (\<alpha>nl fg) ww1) = h" by blast
  from RU_precise[OF RUV_split_el(6)] obtain ww2 s2' c2' where P2: "(([entry fg q], {#}), ww2, s2', c2') \<in> trcl (ntrp fg)" "atU U ({#s2'#} + c2')" "mon_loc fg ww2 = Ml'" "mon_env fg ww2 = Me'" "\<alpha>ah (map (\<alpha>nl fg) ww2) = h'" by blast
  \<comment> \<open>Get combined path from the acquisition history interleavability, need to remap loc/env-steps in second path\<close>
  from P2(5) have "\<alpha>ah (map (\<alpha>nl fg) (map ENV (map le_rem_s ww2))) = h'" by (simp add: \<alpha>n_\<alpha>nl o_assoc)
  with P1(5) RUV_split_el(8) obtain ww where IL: "ww\<in>ww1\<otimes>\<^bsub>\<alpha>nl fg\<^esub>(map ENV (map le_rem_s ww2))" using ah_interleavable2 by (force)
  \<comment> \<open>Use the @{thm [source] ntrp_unsplit}-theorem to combine the executions\<close>
  from ntrp_unsplit[where ca="{#}",OF IL P1(1) gtrp2gtr[OF P2(1)], simplified] have "(([v], {#[entry fg q]#}), ww, s1', c1' + ({#s2'#} + c2')) \<in> trcl (ntrp fg)" 
    using FS(4,5) RUV_split_el(7)
    by (auto simp add: mon_c_unconc mon_ww_of_le_rem P2(3,4))
  from ntrp_add_context[OF ntrp_stack_comp[OF this, of "[u']"], of che] have "(([v] @ [u'], {#[entry fg q]#} + che), ww, s1' @ [u'], c1' + ({#s2'#} + c2') + che) \<in> trcl (ntrp fg)"
    using mon_n_same_proc[OF edges_part[OF RUV_split_el(1)]] mon_loc_cil[OF IL, of fg] mon_env_cil[OF IL, of fg] FS(4,5) RUV_split_el(7) by (auto simp add: mon_c_unconc P1(3,4) P2(3,4) mon_ww_of_le_rem simp del: map_map)
  with FS(1) have "(([u], {#}), LOC (LCall p # w) # ww, (s1' @ [u'], c1' + ({#s2'#} + c2') + che))\<in>trcl (ntrp fg)" by simp
  moreover have "atUV U V ({#s1' @ [u']#}+(c1' + ({#s2'#} + c2') + che))" using P1(2) P2(2) by auto
  moreover have "mon_loc fg (LOC (LCall p # w) # ww) = mon fg p \<union> M \<union> Ml" using FS(3) P1(3) mon_loc_cil[OF IL, of fg] by (auto simp del: map_map)
  moreover have "mon_env fg (LOC (LCall p # w) # ww) = Me \<union> Ml' \<union> Me'" using P1(4) P2(3,4) mon_env_cil[OF IL, of fg] by (auto simp add: mon_ww_of_le_rem simp del: map_map)
  ultimately show ?case by blast
next
  case (RUV_split_ee u p u' v M P q q' Ml Me h Ml' Me' h')
  \<comment> \<open>Get paths from precision results\<close>
  from S_precise_ntrp[OF RUV_split_ee(3,2,1), simplified] mset_size2elem[OF _ RUV_split_ee(4)] obtain w che where 
    FS: "(([u], {#}), LOC (LCall p # w), [v, u'], {#[entry fg q]#} + {#[entry fg q']#} + che) \<in> ntrp fg" "P={#q#}+{#q'#}" "M = mon_w fg w" "mon_n fg v = mon fg p" "mon_c fg ({#[entry fg q]#}+{#[entry fg q']#}+che) = {}" 
    by (auto elim: mset_le_addE)
  from RU_precise[OF RUV_split_ee(5)] obtain ww1 s1' c1' where P1: "(([entry fg q], {#}), ww1, s1', c1') \<in> trcl (ntrp fg)" "atU U ({#s1'#} + c1')" "mon_loc fg ww1 = Ml" "mon_env fg ww1 = Me" "\<alpha>ah (map (\<alpha>nl fg) ww1) = h" by blast
  from RU_precise[OF RUV_split_ee(6)] obtain ww2 s2' c2' where P2: "(([entry fg q'], {#}), ww2, s2', c2') \<in> trcl (ntrp fg)" "atU V ({#s2'#} + c2')" "mon_loc fg ww2 = Ml'" "mon_env fg ww2 = Me'" "\<alpha>ah (map (\<alpha>nl fg) ww2) = h'" by blast

  \<comment> \<open>Get interleaved paths, project away loc/env information first\<close>
  from P1(5) P2(5) have "\<alpha>ah (map (\<alpha>n fg) (map le_rem_s ww1)) = h" "\<alpha>ah (map (\<alpha>n fg) (map le_rem_s ww2)) = h'" by (auto simp add: \<alpha>n_\<alpha>nl o_assoc)
  with RUV_split_ee(8) obtain ww where IL: "ww \<in> (map le_rem_s ww1) \<otimes>\<^bsub>\<alpha>n fg\<^esub> (map le_rem_s ww2)" using ah_interleavable2 by (force simp del: map_map)
  \<comment> \<open>Use the @{thm [source] ntr_unsplit}-theorem to combine the executions\<close>
  from ntr_unsplit[OF IL gtrp2gtr[OF P1(1)] gtrp2gtr[OF P2(1)], simplified] have PC: "({#[entry fg q]#} + {#[entry fg q']#}, ww, {#s1'#} + c1' + ({#s2'#} + c2')) \<in> trcl (ntr fg)" using FS(5) by (auto simp add: mon_c_unconc)
  \<comment> \<open>Prepend first step\<close>
  from ntr2ntrp[OF PC(1), of "[v,u']" che] have "(([v, u'], che + ({#[entry fg q]#} + {#[entry fg q']#})), map ENV ww, [v, u'], che + ({#s1'#} + c1' + ({#s2'#} + c2'))) \<in> trcl (ntrp fg)"
    using RUV_split_ee(7) FS(5) mon_ww_cil[OF IL, of fg] FS(4) mon_n_same_proc[OF edges_part[OF RUV_split_ee(1)]] by (auto simp add: mon_c_unconc mon_ww_of_le_rem P1(3,4) P2(3,4))
  with FS(1) have "(([u], {#}), LOC (LCall p # w) # map ENV ww, ([v, u'], che + ({#s1'#} + c1' + ({#s2'#} + c2')))) \<in> trcl (ntrp fg)" by (auto simp add: union_ac)
  moreover have "atUV U V ({#[v, u']#}+(che + ({#s1'#} + c1' + ({#s2'#} + c2'))))" using P1(2) P2(2) by auto
  moreover have "mon_loc fg (LOC (LCall p # w) # map ENV ww) = mon fg p \<union> M" using FS(3) by auto
  moreover have "mon_env fg (LOC (LCall p # w) # map ENV ww) = Ml \<union> Me \<union> Ml' \<union> Me'" using mon_ww_cil[OF IL, of fg] by (auto simp add: P1(3,4) P2(3,4) mon_ww_of_le_rem)
  ultimately show ?case by blast
qed
  
end
