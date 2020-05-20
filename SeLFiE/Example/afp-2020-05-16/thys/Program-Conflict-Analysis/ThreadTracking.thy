(*  Title:       Conflict analysis/Thread Tracking
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Thread Tracking"
theory ThreadTracking
imports Main "HOL-Library.Multiset" LTS Misc
begin
text_raw \<open>\label{thy:ThreadTracking}\<close>

text \<open>
  This theory defines some general notion of an interleaving semantics. It defines how to extend a semantics specified on a single thread and a context to a semantic on multisets of threads.
  The context is needed in order to keep track of synchronization.
\<close>

subsection "Semantic on multiset configuration"
text \<open>The interleaving semantics is defined on a multiset of stacks. The thread to make the next step is nondeterministically chosen from all threads ready to make steps.\<close>
definition 
  "gtr gtrs == { (add_mset s c,e,add_mset s' c') | s c e s' c' . ((s,c),e,(s',c'))\<in>gtrs }"

lemma gtrI_s: "((s,c),e,(s',c'))\<in>gtrs \<Longrightarrow> (add_mset s c,e,add_mset s' c')\<in>gtr gtrs"
  by (unfold gtr_def, auto)
lemma gtrI: "((s,c),w,(s',c'))\<in>trcl gtrs 
  \<Longrightarrow> (add_mset s c,w,add_mset s' c')\<in>trcl (gtr gtrs)"
  by (induct rule: trcl_pair_induct) (auto dest: gtrI_s)

lemma gtrE: "\<lbrakk>
    (c,e,c')\<in>gtr T; 
    !!s ce s' ce'. \<lbrakk> c=add_mset s ce; c'=add_mset s' ce'; ((s,ce),e,(s',ce'))\<in>T \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (unfold gtr_def) auto

lemma gtr_empty_conf_s[simp]: 
  "({#},w,c')\<notin>gtr S" 
  "(c,w,{#})\<notin>gtr S"
  by (auto elim: gtrE)
lemma gtr_empty_conf1[simp]: "(({#},w,c')\<in>trcl (gtr S)) \<longleftrightarrow> (w=[] \<and> c'={#})"
  by (induct w) (auto dest: trcl_uncons)
lemma gtr_empty_conf2[simp]: "((c,w,{#})\<in>trcl (gtr S)) \<longleftrightarrow> (w=[] \<and> c={#})"
  by (induct w rule: rev_induct) (auto dest: trcl_rev_uncons)

lemma gtr_find_thread: "\<lbrakk>
    (c,e,c')\<in>gtr gtrs; 
    !!s ce s' ce'. \<lbrakk>c=add_mset s ce; c'=add_mset s' ce'; ((s,ce),e,(s',ce'))\<in>gtrs\<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (unfold gtr_def) auto

lemma gtr_step_cases[cases set, case_names loc other]: "\<lbrakk> 
    (add_mset s ce,e,c')\<in>gtr gtrs; 
    !!s' ce'. \<lbrakk> c'=add_mset s' ce'; ((s,ce),e,(s',ce'))\<in>gtrs \<rbrakk> \<Longrightarrow> P;
    !!cc ss ss' ce'. \<lbrakk> ce=add_mset ss cc; c'=add_mset ss' ce'; 
                       ((ss,add_mset s cc),e,(ss',ce'))\<in>gtrs \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
  by (auto elim!: gtr_find_thread mset_single_cases)

lemma gtr_rev_cases[cases set, case_names loc other]: "\<lbrakk> 
    (c,e,add_mset s' ce')\<in>gtr gtrs; 
    !!s ce. \<lbrakk> c=add_mset s ce; ((s,ce),e,(s',ce'))\<in>gtrs \<rbrakk> \<Longrightarrow> P;
    !!cc ss ss' ce. \<lbrakk> c=add_mset ss ce; ce'=add_mset ss' cc; 
                      ((ss,ce),e,(ss',add_mset s' cc))\<in>gtrs \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
  by (auto elim!: gtr_find_thread mset_single_cases)

subsection "Invariants"
lemma gtr_preserve_s: "\<lbrakk> 
    (c,e,c')\<in>gtr T; 
    P c; 
    !!s c s' c' e. \<lbrakk>P (add_mset s c); ((s,c),e,(s',c'))\<in>T\<rbrakk> \<Longrightarrow> P (add_mset s' c') 
  \<rbrakk> \<Longrightarrow> P c'"
  by (unfold gtr_def) blast

lemma gtr_preserve: "\<lbrakk> 
    (c,w,c')\<in>trcl (gtr T); 
    P c; 
    !!s c s' c' e. \<lbrakk>P (add_mset s c); ((s,c),e,(s',c'))\<in>T\<rbrakk> \<Longrightarrow> P (add_mset s' c') 
  \<rbrakk> \<Longrightarrow> P c'"
  apply (induct rule: trcl.induct)
  apply simp
  apply (subgoal_tac "P c'")
  apply blast
  apply (blast intro: gtr_preserve_s)
done  


subsection "Context preservation assumption"
text \<open>
  We now assume that the original semantics does not modify threads in the context, i.e. it may only add new threads to the context and use the context to obtain monitor information, but not change any
  existing thread in the context. This assumption is valid for our semantics, where the context is just needed to determine the set of allocated monitors. It allows us to generally derive some further properties of
  such semantics.
\<close>
locale env_no_step =
  fixes gtrs :: "(('s\<times>'s multiset),'l) LTS"
  assumes env_no_step_s[cases set, case_names csp]: 
    "\<lbrakk>((s,c),e,(s',c'))\<in>gtrs; !!csp. c'=csp+c \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"

\<comment> \<open>The property of not changing existing threads in the context transfers to paths\<close>
lemma (in env_no_step) env_no_step[cases set, case_names csp]: "\<lbrakk>
    ((s,c),w,(s',c'))\<in>trcl gtrs; 
    !! csp. c'=csp+c \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
proof -
  have "((s,c),w,(s',c'))\<in>trcl gtrs \<Longrightarrow> \<exists>csp. c'=csp+c" proof (induct rule: trcl_pair_induct)
    case empty thus ?case by (auto intro: exI[of _ "{#}"])
  next
    case (cons s c e sh ch w s' c') note IHP=this
    from env_no_step_s[OF IHP(1)] obtain csph where "ch=csph+c" by auto
    moreover from IHP(3) obtain csp' where "c'=csp'+ch" by auto
    ultimately have "c'=csp'+csph+c" by (simp add: union_assoc)
    thus ?case by blast
  qed
  moreover assume "((s,c),w,(s',c'))\<in>trcl gtrs" "!! csp. c'=csp+c \<Longrightarrow> P"
  ultimately show ?thesis by blast
qed

text \<open>
  The following lemma can be used to make a case distinction how a step operated on a given thread in the end configuration:
    \begin{description}
      \item[\<open>loc\<close>] The thread made the step
      \item[\<open>spawn\<close>] The thread was spawned by the step
      \item[\<open>env\<close>] The thread was not involved in the step
    \end{description}
\<close>

lemma (in env_no_step) rev_cases_p[cases set, case_names loc spawn env]: 
  assumes STEP: "(c,e,add_mset s' ce')\<in>gtr gtrs" and
  LOC: "!!s ce. \<lbrakk> c={#s#}+ce; ((s,ce),e,(s',ce'))\<in>gtrs \<rbrakk> \<Longrightarrow> P" and
  SPAWN: "!!ss ss' ce csp. 
            \<lbrakk> c=add_mset ss ce; ce'=add_mset ss' (csp+ce); 
              ((ss,ce),e,(ss',add_mset s' (csp+ce)))\<in>gtrs \<rbrakk> 
           \<Longrightarrow> P" and
  ENV: "!!ss ss' ce csp. 
            \<lbrakk> c=add_mset ss (add_mset s' ce); ce'=add_mset ss' (csp+ce); 
              ((ss,add_mset s' ce),e,(ss',csp+(add_mset s' ce)))\<in>gtrs \<rbrakk> 
           \<Longrightarrow> P"
  shows "P"
proof (rule gtr_rev_cases[OF STEP], goal_cases)
  case 1 thus ?thesis using LOC by auto
next
  case CASE: (2 cc ss ss' ce)
  hence CASE': "c = {#ss#} + ce" "ce' = {#ss'#} + cc" "((ss, ce), e, ss', {#s'#} + cc) \<in> gtrs" by simp_all
  from env_no_step_s[OF CASE'(3)] obtain csp where EQ: "add_mset s' cc = csp + ce" by auto
  thus ?thesis proof (cases rule: mset_unplusm_dist_cases)
    case left note CC=this
    with CASE' have "ce'={#ss'#} + (csp-{#s'#}) + ce" by (auto simp add: union_assoc)
    moreover from CC(2) have "{#s'#}+cc = {#s'#} + (csp-{#s'#}) + ce" by (simp add: union_assoc)
    ultimately show ?thesis using CASE'(1,3) CASE(2) SPAWN by auto
  next
    case right note CC=this
    from CC(1) CASE'(1) have "c=add_mset ss (add_mset s' (ce - {#s'#}))" by (simp add: union_assoc)
    moreover from CC(2) CASE'(2) have "ce'=add_mset ss' (csp+(ce-{#s'#}))" by (simp add: union_assoc)
    moreover from CC(2) have "add_mset s' cc = csp+(add_mset s' (ce-{#s'#}))" by (simp add: union_ac)
    ultimately show ?thesis using CASE'(3) CASE(3) CC(1) ENV by metis
  qed
qed

subsection "Explicit local context"
text_raw \<open>\label{sec:ThreadTracking:exp_local}\<close>
text \<open>
  In the multiset semantics, a single thread has no identity. This may become a problem when reasoning about a fixed thread during an execution. For example, in our constraint-system-based approach
  the operational characterization of the least solution of the constraint system requires to state properties of the steps of the initial thread in some execution. With the multiset semantics, we are unable 
  to identify those steps among all steps.

  There are many solutions to this problem, for example, using thread ids either as part of the thread's configuration or as part of the whole configuration by using 
  lists of stacks or maps from ids to stacks as configuration datatype. 

  In the following we present a special solution that is strong enough to suit our purposes but not meant as a general solution. 

  Instead of identifying every single thread uniquely, we only distinguish one thread as the {\em local} thread. The other
  threads are {\em environment} threads. We then attach to every step the information whether it was on the local or on some environment thread. 

  We call this semantics {\em loc/env}-semantics in contrast to the {\em multiset}-semantics of the last section.
\<close>

subsubsection "Lifted step datatype"
datatype 'a el_step = LOC 'a | ENV 'a

definition
  "loc w == filter (\<lambda>e. case e of LOC a \<Rightarrow> True | ENV a \<Rightarrow> False) w"

definition
  "env w == filter (\<lambda>e. case e of LOC a \<Rightarrow> False | ENV a \<Rightarrow> True) w"

definition
  "le_rem_s e == case e of LOC a \<Rightarrow> a | ENV a \<Rightarrow> a"

text \<open>Standard simplification lemmas\<close>
lemma loc_env_simps[simp]: 
  "loc [] = []" 
  "env [] = []"
  by (unfold loc_def env_def) auto

lemma loc_single[simp]: "loc [a] = (case a of LOC e \<Rightarrow> [a] | ENV e \<Rightarrow> [])"
  by (unfold loc_def) (auto split: el_step.split)
lemma loc_uncons[simp]: 
  "loc (a#b) = (case a of LOC e \<Rightarrow> [a] | ENV e \<Rightarrow> [])@loc b"
  by (unfold loc_def) (auto split: el_step.split)
lemma loc_unconc[simp]: "loc (a@b) = loc a @ loc b"
  by (unfold loc_def, simp)

lemma env_single[simp]: "env [a] = (case a of LOC e \<Rightarrow> [] | ENV e \<Rightarrow> [a])"
  by (unfold env_def) (auto split: el_step.split)
lemma env_uncons[simp]: 
  "env (a#b) = (case a of LOC e \<Rightarrow> [] | ENV e \<Rightarrow> [a]) @ env b"
  by (unfold env_def) (auto split: el_step.split)
lemma env_unconc[simp]: "env (a@b) = env a @ env b"
  by (unfold env_def, simp)

text \<open>The following simplification lemmas are for converting between paths of the multiset- and loc/env-semantics\<close>
lemma le_rem_simps [simp]: 
  "le_rem_s (LOC a) = a" 
  "le_rem_s (ENV a) = a"
  by (unfold le_rem_s_def, auto) 
lemma le_rem_id_simps[simp]: 
  "le_rem_s\<circ>LOC = id" 
  "le_rem_s\<circ>ENV = id"
  by (auto intro: ext) 

lemma le_rem_id_map[simp]: 
  "map le_rem_s (map LOC w) = w" 
  "map le_rem_s (map ENV w) = w"
  by auto

lemma env_map_env [simp]: "env (map ENV w) = map ENV w"
  by (unfold env_def) simp
lemma env_map_loc [simp]: "env (map LOC w) = []"
  by (unfold env_def) simp
lemma loc_map_env [simp]: "loc (map ENV w) = []"
  by (unfold loc_def) simp
lemma loc_map_loc [simp]: "loc (map LOC w) = map LOC w"
  by (unfold loc_def) simp

subsubsection "Definition of the loc/env-semantics"
type_synonym 's el_conf = "('s \<times> 's multiset)"

inductive_set
  gtrp :: "('s el_conf,'l) LTS \<Rightarrow> ('s el_conf,'l el_step) LTS"
  for S
  where
  gtrp_loc: "((s,c),e,(s',c'))\<in>S \<Longrightarrow> ((s,c),LOC e,(s',c'))\<in>gtrp S"
  | gtrp_env: "((s,add_mset sl c),e,(s',add_mset sl c'))\<in>S
               \<Longrightarrow> ((sl,add_mset s c),ENV e,(sl,add_mset s' c'))\<in>gtrp S"


subsubsection "Relation between multiset- and loc/env-semantics"
lemma gtrp2gtr_s: 
  "((s,c),e,(s',c'))\<in>gtrp T \<Longrightarrow> (add_mset s c,le_rem_s e,add_mset s' c')\<in>gtr T" 
proof (cases rule: gtrp.cases, auto intro: gtrI_s) 
  fix c c' e ss ss' assume "((ss,add_mset s c),e,(ss',add_mset s c'))\<in>T"
  hence "(add_mset ss (add_mset s c),e,add_mset ss' (add_mset s c')) \<in> gtr T" by (auto intro!: gtrI_s)
  thus "(add_mset s (add_mset ss c), e, add_mset s (add_mset ss' c')) \<in> gtr T"  by (auto simp add: add_mset_commute)
qed


lemma gtrp2gtr: 
  "((s,c),w,(s',c'))\<in>trcl (gtrp T) 
  \<Longrightarrow> (add_mset s c,map le_rem_s w,add_mset s' c')\<in>trcl (gtr T)" 
  by (induct rule: trcl_pair_induct) (auto dest: gtrp2gtr_s)

lemma (in env_no_step) gtr2gtrp_s[cases set, case_names gtrp]: 
  assumes A: "(add_mset s c,e,c')\<in>gtr gtrs" 
  and CASE: "!!s' ce' ee. \<lbrakk>c'=add_mset s' ce'; e=le_rem_s ee; 
                          ((s,c),ee,(s',ce'))\<in>gtrp gtrs\<rbrakk> 
                         \<Longrightarrow> P"
  shows "P" 
  using A 
proof (cases rule: gtr_step_cases)
  case (loc s' ce') hence "((s,c),LOC e,(s',ce'))\<in>gtrp gtrs" by (blast intro: gtrp_loc)
  with loc(1) show ?thesis by (rule_tac CASE) auto
next
  case (other cc ss ss' ce') from env_no_step_s[OF other(3)] obtain csp where CE'FMT: "ce'=csp + (add_mset s cc)" .
  with other(3) have "((ss,add_mset s cc),e,(ss',add_mset s (csp+cc)))\<in>gtrs" by auto
  from gtrp_env[OF this] other(1) have "((s, c), ENV e, s, {#ss'#} + (csp + cc)) \<in> gtrp gtrs" by simp
  moreover from other CE'FMT have "c' = {#s#} + ({#ss'#} + (csp + cc))" by (simp add: union_ac)
  ultimately show ?thesis by (rule_tac CASE) auto
qed

lemma (in env_no_step) gtr2gtrp[cases set, case_names gtrp]: 
  assumes A: "(add_mset s c,w,c')\<in>trcl (gtr gtrs)" 
  and CASE: "!!s' ce' ww. \<lbrakk>c'=add_mset s' ce'; w=map le_rem_s ww; 
                           ((s,c),ww,(s',ce'))\<in>trcl (gtrp gtrs)\<rbrakk> 
                          \<Longrightarrow> P" 
  shows P 
proof -
  have "!!s c. (add_mset s c,w,c')\<in>trcl (gtr gtrs) \<Longrightarrow> \<exists>s' ce' ww. c'=add_mset s' ce' \<and> w=map le_rem_s ww \<and> ((s,c),ww,(s',ce'))\<in>trcl (gtrp gtrs)" proof (induct w)
    case Nil thus ?case by auto
  next
    case (Cons e w) then obtain ch where SPLIT: "(add_mset s c,e,ch)\<in>gtr gtrs" "(ch,w,c')\<in>trcl (gtr gtrs)" by (auto dest: trcl_uncons)
    from gtr2gtrp_s[OF SPLIT(1)] obtain sh ceh ee where FS: "ch = add_mset sh  ceh" "e = le_rem_s ee" "((s, c), ee, sh, ceh) \<in> gtrp gtrs" by blast
    moreover from FS(1) SPLIT(2) Cons.hyps obtain s' ce' ww where IH: "c'=add_mset s' ce'" "w=map le_rem_s ww" "((sh,ceh),ww,(s',ce'))\<in>trcl (gtrp gtrs)" by blast
    ultimately have "((s,c),ee#ww,(s',ce'))\<in>trcl (gtrp gtrs)" "e#w = map le_rem_s (ee#ww)" by auto
    with IH(1) show ?case by iprover
  qed
  with A CASE show ?thesis by blast
qed
   
subsubsection "Invariants"
lemma gtrp_preserve_s: 
  assumes A: "((s,c),e,(s',c'))\<in>gtrp T" 
  and INIT: "P (add_mset s c)" 
  and PRES: "!!s c s' c' e. \<lbrakk>P (add_mset s c); ((s,c),e,(s',c'))\<in>T\<rbrakk> 
                            \<Longrightarrow> P (add_mset s' c')" 
  shows "P (add_mset s' c')" 
proof -
  from gtr_preserve_s[OF gtrp2gtr_s[OF A], where P=P, OF INIT] PRES show "P (add_mset s' c')" by blast
qed

lemma gtrp_preserve: 
  assumes A: "((s,c),w,(s',c'))\<in>trcl (gtrp T)" 
  and INIT: "P (add_mset s c)" 
  and PRES: "!!s c s' c' e. \<lbrakk>P (add_mset s c); ((s,c),e,(s',c'))\<in>T\<rbrakk> 
                            \<Longrightarrow> P (add_mset s' c')" 
  shows "P (add_mset s' c')" 
proof -
  from gtr_preserve[OF gtrp2gtr[OF A], where P=P, OF INIT] PRES show "P (add_mset s' c')" by blast
qed
    

end
