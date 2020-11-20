(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{State Space Exploration}\<close>
theory Exploration
imports Main Collections.Collections
begin
text_raw \<open>\label{thy:Exploration}\<close>
  
text \<open>
  In this theory, a workset algorithm for state-space exploration is defined.
  It explores the set of states that are reachable by a given relation, 
   starting at a given set of initial states.

  The specification makes use of the data refinement framework for 
  while-algorithms (cf. Section~\ref{thy:DatRef}), and is thus suited for 
  being refined to an executable algorithm, using the Isabelle Collections Framework
  to provide the necessary data structures.
\<close>

subsection "Generic Search Algorithm"

  \<comment> \<open>The algorithm contains a set of discovered states and a workset\<close>
type_synonym '\<Sigma> sse_state = "'\<Sigma> set \<times> '\<Sigma> set"

  \<comment> \<open>Loop body\<close>
inductive_set 
  sse_step :: "('\<Sigma>\<times>'\<Sigma>) set \<Rightarrow> ('\<Sigma> sse_state \<times> '\<Sigma> sse_state) set" 
  for R where
  "\<lbrakk> \<sigma>\<in>W;
     \<Sigma>' = \<Sigma> \<union> (R``{\<sigma>});
     W' = (W-{\<sigma>}) \<union> ((R``{\<sigma>}) - \<Sigma>)
   \<rbrakk> \<Longrightarrow> ((\<Sigma>,W),(\<Sigma>',W'))\<in>sse_step R"
  
  \<comment> \<open>Loop condition\<close>
definition sse_cond :: "'\<Sigma> sse_state set" where
  "sse_cond = {(\<Sigma>,W). W\<noteq>{}}"

  \<comment> \<open>Initial state\<close>
definition sse_initial :: "'\<Sigma> set \<Rightarrow> '\<Sigma> sse_state" where
  "sse_initial \<Sigma>i == (\<Sigma>i,\<Sigma>i)"


  \<comment> \<open>Invariants: 
  \begin{itemize}
    \item The workset contains only states that are already 
      discovered.
    \item All discovered states are target states
    \item If there is a target state that is not discovered yet,
          then there is an element in the workset from that this 
          target state is reachable without using discovered 
          states as intermediate states. This supports the intuition 
          of the workset as a frontier between the sets of discovered 
          and undiscovered states.

  \end{itemize}\<close>
definition sse_invar :: "'\<Sigma> set \<Rightarrow> ('\<Sigma>\<times>'\<Sigma>) set \<Rightarrow> '\<Sigma> sse_state set" where
  "sse_invar \<Sigma>i R = {(\<Sigma>,W). 
    W\<subseteq>\<Sigma> \<and>
    (\<Sigma> \<subseteq> R\<^sup>*``\<Sigma>i) \<and> 
    (\<forall>\<sigma>\<in>(R\<^sup>*``\<Sigma>i)-\<Sigma>. \<exists>\<sigma>h\<in>W. (\<sigma>h,\<sigma>)\<in>(R - (UNIV \<times> \<Sigma>))\<^sup>*)
  }"

definition "sse_algo \<Sigma>i R == 
  \<lparr> wa_cond=sse_cond, 
    wa_step=sse_step R, 
    wa_initial = {sse_initial \<Sigma>i}, 
    wa_invar = sse_invar \<Sigma>i R \<rparr>"

definition "sse_term_rel \<Sigma>i R == 
  { (\<sigma>',\<sigma>). \<sigma>\<in>sse_invar \<Sigma>i R \<and> (\<sigma>,\<sigma>')\<in>sse_step R }"

  \<comment> \<open>Termination: Either a new state is discovered, or the workset shrinks\<close>
theorem sse_term:
  assumes finite[simp, intro!]: "finite (R\<^sup>*``\<Sigma>i)"
  shows "wf (sse_term_rel \<Sigma>i R)"
proof -
  have "wf (({(\<Sigma>',\<Sigma>). \<Sigma> \<subset> \<Sigma>' \<and> \<Sigma>' \<subseteq> (R\<^sup>*``\<Sigma>i)}) <*lex*> finite_psubset)"
    by (auto intro: wf_bounded_supset)
  moreover have "sse_term_rel \<Sigma>i R \<subseteq> \<dots>" (is "_ \<subseteq> ?R")
  proof
    fix S
    assume A: "S\<in>sse_term_rel \<Sigma>i R"
    obtain \<Sigma> W \<Sigma>' W' \<sigma> where
      [simp]: "S=((\<Sigma>',W'),(\<Sigma>,W))" and
      S: "(\<Sigma>,W) \<in> sse_invar \<Sigma>i R"
         "\<sigma>\<in>W"
         "\<Sigma>' = \<Sigma> \<union> R``{\<sigma>}"
         "W' = (W-{\<sigma>}) \<union> (R``{\<sigma>} - \<Sigma>)"
    proof -
      obtain \<Sigma> W \<Sigma>' W' where SF[simp]: "S=((\<Sigma>',W'),(\<Sigma>,W))" by (cases S) force
      from A have R: "(\<Sigma>,W) \<in> sse_invar \<Sigma>i R" "((\<Sigma>,W),(\<Sigma>',W'))\<in>sse_step R" 
        by (auto simp add: sse_term_rel_def)
      from sse_step.cases[OF R(2)] obtain \<sigma> where S:
        "\<sigma>\<in>W"
        "\<Sigma>' = \<Sigma> \<union> R``{\<sigma>}"
        "W' = (W-{\<sigma>}) \<union> (R``{\<sigma>} - \<Sigma>)"
        by metis
      thus ?thesis 
        by (rule_tac that[OF SF R(1) S])
    qed

    from S(1) have 
      [simp, intro!]: "finite \<Sigma>" "finite W" and
      WSS: "W\<subseteq>\<Sigma>" and
      SSS: "\<Sigma>\<subseteq>R\<^sup>*``\<Sigma>i"
      by (auto simp add: sse_invar_def intro: finite_subset)

    show "S\<in>?R" proof (cases "R``{\<sigma>} \<subseteq> \<Sigma>")
      case True with S have "\<Sigma>'=\<Sigma>" "W' \<subset> W" by auto
      thus ?thesis by (simp)
    next
      case False
      with S have "\<Sigma>' \<supset> \<Sigma>" by auto
      moreover from S(2) WSS SSS have "\<sigma>\<in>R\<^sup>*``\<Sigma>i" by auto
      hence "R``{\<sigma>} \<subseteq> R\<^sup>*``\<Sigma>i" 
        by (auto intro: rtrancl_into_rtrancl)
      with S(3) SSS have "\<Sigma>' \<subseteq> R\<^sup>*``\<Sigma>i" by auto
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show ?thesis by (auto intro: wf_subset)
qed
        
lemma sse_invar_initial: "(sse_initial \<Sigma>i) \<in> sse_invar \<Sigma>i R"
  by (unfold sse_invar_def sse_initial_def)
     (auto elim: rtrancl_last_touch)

  \<comment> \<open>Correctness theorem: If the loop terminates, the discovered states are
       exactly the reachable states\<close>
theorem sse_invar_final: 
  "\<forall>S. S\<in>wa_invar (sse_algo \<Sigma>i R) \<and> S\<notin>wa_cond (sse_algo \<Sigma>i R) 
    \<longrightarrow> fst S = R\<^sup>*``\<Sigma>i"
  by (intro allI, case_tac S)
     (auto simp add: sse_invar_def sse_cond_def sse_algo_def)

lemma sse_invar_step: "\<lbrakk>S\<in>sse_invar \<Sigma>i R; (S,S')\<in>sse_step R\<rbrakk> 
  \<Longrightarrow> S'\<in>sse_invar \<Sigma>i R"
  \<comment> \<open>Split the goal by the invariant:\<close>
  apply (cases S, cases S')
  apply clarsimp
  apply (erule sse_step.cases)
  apply clarsimp
  apply (subst sse_invar_def)
  apply (simp add: Let_def split_conv)
  apply (intro conjI)
  \<comment> \<open>Solve the easy parts automatically\<close>
  apply (auto simp add: sse_invar_def) [3]
  apply (force simp add: sse_invar_def 
               dest: rtrancl_into_rtrancl) [1]
  \<comment> \<open>Tackle the complex part (last part of the invariant) in Isar\<close>
proof (intro ballI)
  fix \<sigma> W \<Sigma> \<sigma>'
  assume A: 
    "(\<Sigma>,W)\<in>sse_invar \<Sigma>i R"
    "\<sigma>\<in>W"
    "\<sigma>'\<in>R\<^sup>* `` \<Sigma>i - (\<Sigma> \<union> R `` {\<sigma>})"
    \<comment> \<open>Using the invariant of the original state, we obtain
        a state in the original workset and a path not touching
        the originally discovered states\<close>
  from A(3) have "\<sigma>' \<in> R\<^sup>* `` \<Sigma>i - \<Sigma>" by auto
  with A(1) obtain \<sigma>h where IP: 
    "\<sigma>h\<in>W" 
    "(\<sigma>h,\<sigma>')\<in>(R - (UNIV \<times> \<Sigma>))\<^sup>*" 
  and SS:
    "W\<subseteq>\<Sigma>"
    "\<Sigma>\<subseteq>R\<^sup>* `` \<Sigma>i"
    by (unfold sse_invar_def) force

  \<comment> \<open>We now make a case distinction, whether the obtained path contains
      states from @{term "post \<sigma>"} or not:\<close>
  from IP(2) show "\<exists>\<sigma>h\<in>W - {\<sigma>} \<union> (R `` {\<sigma>} - \<Sigma>). 
                     (\<sigma>h, \<sigma>') \<in> (R - UNIV \<times> (\<Sigma> \<union> R `` {\<sigma>}))\<^sup>*"
  proof (cases rule: rtrancl_last_visit[where S="R `` {\<sigma>}"])
    case no_visit
    \<comment> \<open>In the case that the obtained path contains no states from 
          @{term "post \<sigma>"}, we can take it.\<close>
    hence G1: "(\<sigma>h,\<sigma>')\<in>(R- (UNIV \<times> (\<Sigma>\<union>R `` {\<sigma>})))\<^sup>*" 
      by (simp add: set_diff_diff_left Sigma_Un_distrib2)
    moreover have "\<sigma>h \<noteq> \<sigma>" 
      \<comment> \<open>We may exclude the case that our obtained path started at 
            @{text \<sigma>}, as all successors of @{text \<sigma>} are 
            in @{term "R `` {\<sigma>}"}\<close>
    proof
      assume [simp]: "\<sigma>h=\<sigma>"
      from A SS have "\<sigma>\<noteq>\<sigma>'" by auto
      with G1 show False
        by (auto simp add: elim: converse_rtranclE)
    qed
    ultimately show ?thesis using IP(1) by auto
  next
    case (last_visit_point \<sigma>t)
    \<comment> \<open>If the obtained path contains a state from @{text "R `` {\<sigma>}"}, 
          we simply pick the last one:\<close>
    hence "(\<sigma>t,\<sigma>')\<in>(R- (UNIV \<times> (\<Sigma>\<union>R `` {\<sigma>})))\<^sup>*" 
      by (simp add: set_diff_diff_left Sigma_Un_distrib2)
    moreover from last_visit_point(2) have "\<sigma>t\<notin>\<Sigma>" 
      by (auto elim: trancl.cases)
    ultimately show ?thesis using last_visit_point(1) by auto
  qed
qed

\<comment> \<open>The sse-algorithm is a well-defined while-algorithm\<close>
theorem sse_while_algo: "finite (R\<^sup>*``\<Sigma>i) \<Longrightarrow> while_algo (sse_algo \<Sigma>i R)"
  apply unfold_locales
  apply (auto simp add: sse_algo_def intro: sse_invar_step sse_invar_initial)
  apply (drule sse_term)
  apply (erule_tac wf_subset)
  apply (unfold sse_term_rel_def)
  apply auto
  done

subsection "Depth First Search"
text_raw \<open>\label{sec:sse:dfs}\<close>
text \<open>
  In this section, the generic state space exploration algorithm is refined
  to a DFS-algorithm, that uses a stack to implement the workset.
\<close>

type_synonym '\<Sigma> dfs_state = "'\<Sigma> set \<times> '\<Sigma> list"

definition dfs_\<alpha> :: "'\<Sigma> dfs_state \<Rightarrow> '\<Sigma> sse_state" 
  where "dfs_\<alpha> S == let (\<Sigma>,W)=S in (\<Sigma>,set W)"

definition dfs_invar_add :: "'\<Sigma> dfs_state set"
  where "dfs_invar_add == {(\<Sigma>,W). distinct W}"

definition "dfs_invar \<Sigma>i R == dfs_invar_add \<inter> { s. dfs_\<alpha> s \<in> sse_invar \<Sigma>i R }"

inductive_set dfs_initial :: "'\<Sigma> set \<Rightarrow> '\<Sigma> dfs_state set" for \<Sigma>i
  where "\<lbrakk> distinct W; set W = \<Sigma>i\<rbrakk> \<Longrightarrow> (\<Sigma>i,W)\<in>dfs_initial \<Sigma>i"

inductive_set dfs_step :: "('\<Sigma>\<times>'\<Sigma>) set \<Rightarrow> ('\<Sigma> dfs_state \<times>'\<Sigma> dfs_state) set" 
  for R where
  "\<lbrakk> W=\<sigma>#Wtl;
     distinct Wn;
     set Wn = R``{\<sigma>} - \<Sigma>;
     W' = Wn@Wtl;
     \<Sigma>' = R``{\<sigma>} \<union> \<Sigma>
  \<rbrakk> \<Longrightarrow> ((\<Sigma>,W),(\<Sigma>',W'))\<in>dfs_step R"

definition dfs_cond :: "'\<Sigma> dfs_state set" 
  where "dfs_cond == { (\<Sigma>,W). W\<noteq>[]}"

definition "dfs_algo \<Sigma>i R == \<lparr> 
  wa_cond = dfs_cond, 
  wa_step = dfs_step R, 
  wa_initial = dfs_initial \<Sigma>i, 
  wa_invar = dfs_invar \<Sigma>i R \<rparr>"

  \<comment> \<open>The DFS-algorithm refines the state-space exploration algorithm\<close>
theorem dfs_pref_sse: 
  "wa_precise_refine (dfs_algo \<Sigma>i R) (sse_algo \<Sigma>i R) dfs_\<alpha>"
  apply (unfold_locales)
  apply (auto simp add: dfs_algo_def sse_algo_def dfs_cond_def sse_cond_def 
                        dfs_\<alpha>_def)
  apply (erule dfs_step.cases)
  apply (rule_tac \<sigma>=\<sigma> in sse_step.intros)
  apply (auto simp add: dfs_invar_def sse_invar_def dfs_invar_add_def 
                        sse_initial_def dfs_\<alpha>_def 
              elim: dfs_initial.cases)
  done

  \<comment> \<open>The DFS-algorithm is a well-defined while-algorithm\<close>
theorem dfs_while_algo:
  assumes finite[simp, intro!]: "finite (R\<^sup>*``\<Sigma>i)"
  shows "while_algo (dfs_algo \<Sigma>i R)"
proof -
  interpret wa_precise_refine "(dfs_algo \<Sigma>i R)" "(sse_algo \<Sigma>i R)" dfs_\<alpha> 
    using dfs_pref_sse .

  have [simp]: "wa_invar (sse_algo \<Sigma>i R) = sse_invar \<Sigma>i R" 
    by (simp add: sse_algo_def)

  show ?thesis 
    apply (rule wa_intro)
    apply (simp add: sse_while_algo)

    apply (simp add: dfs_invar_def dfs_algo_def)
    
    apply (auto simp add: dfs_invar_add_def dfs_algo_def dfs_\<alpha>_def 
                          dfs_cond_def sse_invar_def 
                elim!: dfs_step.cases) [1]

    apply (auto simp add: dfs_invar_add_def dfs_algo_def 
                elim: dfs_initial.cases) [1]
    done 
qed

  \<comment> \<open>The result of the DFS-algorithm is correct\<close>
lemmas dfs_invar_final = 
  wa_precise_refine.transfer_correctness[OF dfs_pref_sse sse_invar_final]

end
