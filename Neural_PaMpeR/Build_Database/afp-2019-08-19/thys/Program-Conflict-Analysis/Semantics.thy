(*  Title:       Conflict analysis/Operational Semantics
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Operational Semantics"
theory Semantics
imports Main Flowgraph "HOL-Library.Multiset" LTS Interleave ThreadTracking
begin
text_raw \<open>\label{thy:Semantics}\<close>

subsection "Configurations and labels"
text \<open>
  The state of a single thread is described by a stack of control nodes. The top node is the current control node and the nodes deeper in the stack are stored return addresses. 
  The configuration of a whole program is described by a multiset of stacks. 

  Note that we model stacks as lists here, the first element being the top element.
\<close>
type_synonym 'n conf = "('n list) multiset"

text \<open>
  A step is labeled according to the executed edge. Additionally, we introduce a label for a procedure return step, that has no corresponding edge. 
\<close>
datatype ('p,'ba) label = LBase 'ba | LCall 'p | LRet | LSpawn 'p

subsection \<open>Monitors\<close>
text \<open>
  The following defines the monitors of nodes, stacks, configurations, step labels and paths (sequences of step labels)
\<close>
definition
  \<comment> \<open>The monitors of a node are the monitors the procedure of the node synchronizes on\<close>
  "mon_n fg n == mon fg (proc_of fg n)"

definition
  \<comment> \<open>The monitors of a stack are the monitors of all its nodes\<close>
  "mon_s fg s == \<Union> { mon_n fg n | n . n \<in> set s }"

definition
  \<comment> \<open>The monitors of a configuration are the monitors of all its stacks\<close>
  "mon_c fg c == \<Union> { mon_s fg s | s . s \<in># c }"

\<comment> \<open>The monitors of a step label are the monitors of procedures that are called by this step\<close>
definition mon_e :: "('b, 'c, 'd, 'a, 'e) flowgraph_rec_scheme \<Rightarrow> ('c, 'f) label \<Rightarrow> 'a set" where
  "mon_e fg e = (case e of (LCall p) \<Rightarrow> mon fg p | _ \<Rightarrow> {})"

lemma mon_e_simps [simp]:
  "mon_e fg (LBase a) = {}"
  "mon_e fg (LCall p) = mon fg p"
  "mon_e fg (LRet) = {}"
  "mon_e fg (LSpawn p) = {}"
  by (simp_all add: mon_e_def)

\<comment> \<open>The monitors of a path are the monitors of all procedures that are called on the path\<close>
definition
  "mon_w fg w == \<Union> { mon_e fg e | e. e \<in> set w}"

lemma mon_s_alt: "mon_s fg s == \<Union> (mon fg ` proc_of fg ` set s)"
  by (unfold mon_s_def mon_n_def) (auto intro!: eq_reflection)
lemma mon_c_alt: "mon_c fg c == \<Union> (mon_s fg ` set_mset c)"
  by (unfold mon_c_def set_mset_def) (auto intro!: eq_reflection)
lemma mon_w_alt: "mon_w fg w == \<Union> (mon_e fg ` set w)"
  by (unfold mon_w_def) (auto intro!: eq_reflection)

lemma mon_sI: "\<lbrakk>n\<in>set s; m\<in>mon_n fg n\<rbrakk> \<Longrightarrow> m\<in>mon_s fg s"
  by (unfold mon_s_def, auto)
lemma mon_sD: "m\<in>mon_s fg s \<Longrightarrow> \<exists>n\<in>set s. m\<in>mon_n fg n"
  by (unfold mon_s_def, auto)

lemma mon_n_same_proc: 
  "proc_of fg n = proc_of fg n' \<Longrightarrow> mon_n fg n = mon_n fg n'"
  by (unfold mon_n_def, simp)
lemma mon_s_same_proc: 
  "proc_of fg ` set s = proc_of fg ` set s' \<Longrightarrow> mon_s fg s = mon_s fg s'"
  by (unfold mon_s_alt, simp)

lemma (in flowgraph) mon_of_entry[simp]: "mon_n fg (entry fg p) = mon fg p"
  by (unfold mon_n_def, simp add: entry_valid)
lemma (in flowgraph) mon_of_ret[simp]: "mon_n fg (return fg p) = mon fg p"
  by (unfold mon_n_def, simp add: return_valid)

lemma mon_c_single[simp]: "mon_c fg {#s#} = mon_s fg s"
  by (unfold mon_c_def) auto
lemma mon_s_single[simp]: "mon_s fg [n] = mon_n fg n"
  by (unfold mon_s_def) auto
lemma mon_s_empty[simp]: "mon_s fg [] = {}"
  by (unfold mon_s_def) auto
lemma mon_c_empty[simp]: "mon_c fg {#} = {}"
  by (unfold mon_c_def) auto

lemma mon_s_unconc: "mon_s fg (a@b) = mon_s fg a \<union> mon_s fg b"
  by (unfold mon_s_def) auto
lemma mon_s_uncons[simp]: "mon_s fg (a#as) = mon_n fg a \<union> mon_s fg as"
  by (rule mon_s_unconc[where a="[a]", simplified])

lemma mon_c_union_conc: "mon_c fg (a+b) = mon_c fg a \<union> mon_c fg b"
  by (unfold mon_c_def) auto

lemma mon_c_add_mset_unconc: "mon_c fg (add_mset x b) = mon_s fg x \<union> mon_c fg b"
  by (unfold mon_c_def) auto

lemmas mon_c_unconc = mon_c_union_conc mon_c_add_mset_unconc

lemma mon_cI: "\<lbrakk>s \<in># c; m\<in>mon_s fg s\<rbrakk> \<Longrightarrow> m\<in>mon_c fg c"
  by (unfold mon_c_def, auto)
lemma mon_cD: "\<lbrakk>m\<in>mon_c fg c\<rbrakk> \<Longrightarrow> \<exists>s. s \<in># c \<and> m\<in>mon_s fg s"
  by (unfold mon_c_def, auto)

lemma mon_s_mono: "set s \<subseteq> set s' \<Longrightarrow> mon_s fg s \<subseteq> mon_s fg s'"
  by (unfold mon_s_def) auto
lemma mon_c_mono: "c\<subseteq>#c' \<Longrightarrow> mon_c fg c \<subseteq> mon_c fg c'"
  by (unfold mon_c_def) (auto dest: mset_subset_eqD)

lemma mon_w_empty[simp]: "mon_w fg [] = {}"
  by (unfold mon_w_def, auto)
lemma mon_w_single[simp]: "mon_w fg [e] = mon_e fg e"
  by (unfold mon_w_def, auto)
lemma mon_w_unconc: "mon_w fg (wa@wb) = mon_w fg wa \<union> mon_w fg wb"
  by (unfold mon_w_def) auto
lemma mon_w_uncons[simp]: "mon_w fg (e#w) = mon_e fg e \<union> mon_w fg w"
  by (rule mon_w_unconc[where wa="[e]", simplified])
lemma mon_w_ileq: "w\<preceq>w' \<Longrightarrow> mon_w fg w \<subseteq> mon_w fg w'"
  by (induct rule: less_eq_list_induct) auto



subsection \<open>Valid configurations\<close>
text_raw \<open>\label{sec:Semantics:validity}\<close>
text \<open>We call a configuration {\em valid} if each monitor is owned by at most one thread.\<close>
definition
  "valid fg c == \<forall>s s'. {#s, s'#} \<subseteq># c \<longrightarrow> mon_s fg s \<inter> mon_s fg s' = {}"

lemma valid_empty[simp, intro!]: "valid fg {#}" 
  by (unfold valid_def, auto)

lemma valid_single[simp, intro!]: "valid fg {#s#}" 
  by (unfold valid_def subset_mset_def) auto

lemma valid_split1: 
  "valid fg (c+c') \<Longrightarrow> valid fg c \<and> valid fg c' \<and> mon_c fg c \<inter> mon_c fg c' = {}"
  apply (unfold valid_def)
  apply (auto simp add: mset_le_incr_right)
  apply (drule mon_cD)+
  apply auto
  apply (subgoal_tac "{#s#}+{#sa#} \<subseteq># c+c'")
  apply (auto dest!: multi_member_split)
  done
  
lemma valid_split2: 
  "\<lbrakk>valid fg c; valid fg c'; mon_c fg c \<inter> mon_c fg c' = {}\<rbrakk> \<Longrightarrow> valid fg (c+c')"
  apply (unfold valid_def)
  apply (intro impI allI)
  apply (erule mset_2dist2_cases)
  apply simp_all
  apply (blast intro: mon_cI)+
  done

lemma valid_union_conc: 
  "valid fg (c+c') \<longleftrightarrow> (valid fg c \<and> valid fg c' \<and> mon_c fg c \<inter> mon_c fg c' = {})" 
  by (blast dest: valid_split1 valid_split2)

lemma valid_add_mset_conc: 
  "valid fg (add_mset x c') \<longleftrightarrow> (valid fg c' \<and> mon_s fg x \<inter> mon_c fg c' = {})"
  unfolding add_mset_add_single[of x c'] valid_union_conc by (auto simp: mon_s_def)

lemmas valid_unconc = valid_union_conc valid_add_mset_conc

lemma valid_no_mon: "mon_c fg c = {} \<Longrightarrow> valid fg c" 
proof (unfold valid_def, intro allI impI)
  fix s s'
  assume A: "mon_c fg c = {}" and B: "{#s, s'#} \<subseteq># c"
  from mon_c_mono[OF B, of fg] A have "mon_s fg s = {}" "mon_s fg s' = {}" by (auto simp add: mon_c_unconc)
  thus "mon_s fg s \<inter> mon_s fg s' = {}" by blast
qed

subsection \<open>Configurations at control points\<close>

\<comment> \<open>A stack is {\em at} @{term U} if its top node is from the set @{term U}\<close>
primrec atU_s :: "'n set \<Rightarrow> 'n list \<Rightarrow> bool" where
  "atU_s U [] = False"
| "atU_s U (u#r) = (u\<in>U)"

lemma atU_s_decomp[simp]: "atU_s U (s@s') = (atU_s U s \<or> (s=[] \<and> atU_s U s'))"
  by (induct s) auto

\<comment> \<open>A configuration is {\em at} @{term U} if it contains a stack that is at @{term U}\<close>
definition
  "atU U c == \<exists>s. s \<in># c \<and> atU_s U s"

lemma atU_fmt: "\<lbrakk>atU U c; !!ui r. \<lbrakk>ui#r \<in># c; ui\<in>U\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (unfold atU_def)
  apply auto
  apply (case_tac s)
  apply auto
  done

lemma atU_union_cases[case_names left right, consumes 1]: "\<lbrakk> 
    atU U (c1+c2); 
    atU U c1 \<Longrightarrow> P; 
    atU U c2 \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (unfold atU_def) (blast elim: mset_un_cases)

lemma atU_add: "atU U c \<Longrightarrow> atU U (c+ce) \<and> atU U (ce+c)"
  by (unfold atU_def) (auto simp add: union_ac)

lemma atU_union[simp]: "atU U (c1+c2) = (atU U c1 \<or> atU U c2)"
  by (auto simp add: atU_add elim: atU_union_cases)

lemma atU_empty[simp]: "\<not>atU U {#}"
  by (unfold atU_def, auto)
lemma atU_single[simp]: "atU U {#s#} = atU_s U s"
  by (unfold atU_def, auto)
lemma atU_single_top[simp]: "atU U {#u#r#} = (u\<in>U)" 
  by (auto) (* This is also done by atU_single, atU_s.simps *)

lemma atU_add_mset[simp]: "atU U (add_mset c c2) = (atU_s U c \<or> atU U c2)"
  unfolding add_mset_add_single[of c c2] atU_union by auto

lemma atU_xchange_stack: "atU U (add_mset (u#r) c) \<Longrightarrow> atU U (add_mset (u#r') c)"
  by (simp)

\<comment> \<open>A configuration is {\em simultaneously at} @{term U} and @{term V} if it contains a stack at @{term U} and another one at @{term V}\<close>
definition 
  "atUV U V c == \<exists>su sv. {#su#}+{#sv#} \<subseteq># c \<and> atU_s U su \<and> atU_s V sv"

lemma atUV_empty[simp]: "\<not>atUV U V {#}"
  by (unfold atUV_def) auto
lemma atUV_single[simp]: "\<not>atUV U V {#s#}"
  by (unfold atUV_def) auto

lemma atUV_union[simp]: "
  atUV U V (c1+c2) \<longleftrightarrow> 
  (
    (atUV U V c1) \<or> 
    (atUV U V c2) \<or> 
    (atU U c1 \<and> atU V c2) \<or> 
    (atU V c1 \<and> atU U c2)
  )"
  apply (unfold atUV_def atU_def)
  apply (auto elim!: mset_2dist2_cases intro: mset_le_incr_right iff add: mset_le_mono_add_single)
  apply (subst union_commute)
  apply (auto iff add: mset_le_mono_add_single)
  done

lemma atUV_add_mset[simp]: "
  atUV U V (add_mset c c2) \<longleftrightarrow>
  (
    (atUV U V c2) \<or>
    (atU U {#c#} \<and> atU V c2) \<or>
    (atU V {#c#} \<and> atU U c2)
  )"
  unfolding add_mset_add_single[of c c2]
  unfolding atUV_union
  by auto

lemma atUV_union_cases[case_names left right lr rl, consumes 1]: "\<lbrakk>
    atUV U V (c1+c2); 
    atUV U V c1 \<Longrightarrow> P; 
    atUV U V c2 \<Longrightarrow> P; 
    \<lbrakk>atU U c1; atU V c2\<rbrakk> \<Longrightarrow> P; 
    \<lbrakk>atU V c1; atU U c2\<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by auto

subsection \<open>Operational semantics\<close>

subsubsection "Semantic reference point"
text \<open>We now define our semantic reference point. We assess correctness and completeness of analyses relative to this reference point.\<close>
inductive_set 
  refpoint :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> 
                 ('n conf \<times> ('p,'ba) label \<times> 'n conf) set"
  for fg
where
  \<comment> \<open>A base edge transforms the top node of one stack and leaves the other stacks untouched.\<close>
  refpoint_base: "\<lbrakk> (u,Base a,v)\<in>edges fg; valid fg ({#u#r#}+c) \<rbrakk> 
    \<Longrightarrow> (add_mset (u#r) c,LBase a,add_mset (v#r) c)\<in>refpoint fg" |
  \<comment> \<open>A call edge transforms the top node of a stack and then pushes the entry node of the called procedure onto that stack. 
      It can only be executed if all monitors the called procedure synchronizes on are available. Reentrant monitors are modeled here by
      checking availability of monitors just against the other stacks, not against the stack of the thread that executes the call. The other stacks are left untouched.\<close>
  refpoint_call: "\<lbrakk> (u,Call p,v)\<in>edges fg; valid fg ({#u#r#}+c); 
                    mon fg p \<inter> mon_c fg c = {} \<rbrakk> 
    \<Longrightarrow> (add_mset (u#r) c,LCall p, add_mset (entry fg p#v#r) c)\<in>refpoint fg" |
  \<comment> \<open>A return step pops a return node from a stack. There is no corresponding flowgraph edge for a return step. The other stacks are left untouched.\<close>
  refpoint_ret: "\<lbrakk> valid fg ({#return fg p#r#}+c) \<rbrakk> 
    \<Longrightarrow> (add_mset (return fg p#r) c,LRet,(add_mset r c))\<in>refpoint fg" |
  \<comment> \<open>A spawn edge transforms the top node of a stack and adds a new stack to the environment, with the entry node of the spawned procedure at the top and no stored return addresses. The other stacks are also left untouched.\<close>
  refpoint_spawn: "\<lbrakk> (u,Spawn p,v)\<in>edges fg; valid fg (add_mset (u#r) c) \<rbrakk> 
    \<Longrightarrow> (add_mset (u#r) c,LSpawn p, add_mset (v#r) (add_mset [entry fg p] c))\<in>refpoint fg"

text \<open>
  Instead of working directly with the reference point semantics, we define the operational semantics of flowgraphs by describing how a single stack is transformed in a context of environment threads, 
  and then use the theory developed in Section~\ref{thy:ThreadTracking} to derive an interleaving semantics. 
  Note that this semantics is also defined for invalid configurations (cf. Section~\ref{sec:Semantics:validity}). In Section~\ref{sec:Semantics:valid_preserve} we will show that it preserves validity
  of a configuration, and in Section~\ref{sec:Semantics: refpoint_eq} we show that it is equivalent 
  to the reference point semantics on valid configurations.
\<close>

inductive_set
  trss :: "('n,'p,'ba,'m,'more) flowgraph_rec_scheme \<Rightarrow> 
             (('n list * 'n conf) * ('p,'ba) label * ('n list * 'n conf)) set"
  for fg
  where
    trss_base: "\<lbrakk>(u,Base a,v)\<in>edges fg\<rbrakk> \<Longrightarrow> 
      ((u#r,c), LBase a, (v#r,c) ) \<in> trss fg"
  | trss_call: "\<lbrakk>(u,Call p,v)\<in>edges fg; mon fg p \<inter> mon_c fg c = {} \<rbrakk> \<Longrightarrow> 
    ((u#r,c),LCall p, ((entry fg p)#v#r,c)) \<in> trss fg"
  | trss_ret: "((((return fg p)#r),c),LRet,(r,c)) \<in> trss fg"
  | trss_spawn: "\<lbrakk> (u,Spawn p,v)\<in>edges fg \<rbrakk> \<Longrightarrow> 
    ((u#r,c),LSpawn p,(v#r,add_mset [entry fg p] c)) \<in> trss fg"

(* Not needed
lemma trss_base': "\<lbrakk>(u,Base a,v)\<in>edges fg; s=u#r; s'=v#r; e=LBase a\<rbrakk> \<Longrightarrow> ((s,c), e, (s',c) ) \<in> trss fg"
  by (simp add: trss_base)
lemma trss_call': "\<lbrakk>(u,Call p,v)\<in>edges fg; mon fg p \<inter> mon_c fg c = {}; s=u#r; e=LCall p; s'=(entry fg p)#v#r\<rbrakk> \<Longrightarrow> ((s,c),e, (s',c)) \<in> trss fg"
  by (simp add: trss_call)
lemma trss_ret': "\<lbrakk> s=(return fg p)#r; e=LRet \<rbrakk> \<Longrightarrow> ((s,c),e,(r,c)) \<in> trss fg"
  by (simp add: trss_ret)
lemma trss_spawn': "\<lbrakk> (u,Spawn p,v)\<in>edges fg; s=u#r; e=LSpawn p; s'=v#r; c'={#[entry fg p]#}+c\<rbrakk> \<Longrightarrow> ((s,c),e,(s',c')) \<in> trss fg"
  by (simp add: trss_spawn)
*)

\<comment> \<open>The interleaving semantics is generated using the general techniques from Section~\ref{thy:ThreadTracking}\<close>
abbreviation tr where "tr fg == gtr (trss fg)"
\<comment> \<open>We also generate the loc/env-semantics\<close>
abbreviation trp where "trp fg == gtrp (trss fg)"


subsection "Basic properties"
subsubsection "Validity"
text_raw\<open>\label{sec:Semantics:valid_preserve}\<close>
lemma (in flowgraph) trss_valid_preserve_s: 
  "\<lbrakk>valid fg (add_mset s c); ((s,c),e,(s',c'))\<in>trss fg\<rbrakk> \<Longrightarrow> valid fg (add_mset s' c')"
  apply (erule trss.cases)
  apply (simp_all add: valid_unconc mon_c_unconc)
by (blast dest: mon_n_same_proc edges_part)+

lemma (in flowgraph) trss_valid_preserve: 
  "\<lbrakk>((s,c),w,(s',c'))\<in>trcl (trss fg); valid fg ({#s#}+c)\<rbrakk> \<Longrightarrow> valid fg ({#s'#}+c')"
  by (induct rule: trcl_pair_induct) (auto intro: trss_valid_preserve_s)

lemma (in flowgraph) tr_valid_preserve_s: 
  "\<lbrakk>(c,e,c')\<in>tr fg; valid fg c\<rbrakk> \<Longrightarrow> valid fg c'"
  by (rule gtr_preserve_s[where P="valid fg"]) (auto dest: trss_valid_preserve_s)

lemma (in flowgraph) tr_valid_preserve: 
  "\<lbrakk>(c,w,c')\<in>trcl (tr fg); valid fg c\<rbrakk> \<Longrightarrow> valid fg c'"
  by (rule gtr_preserve[where P="valid fg"]) (auto dest: trss_valid_preserve_s)
  
lemma (in flowgraph) trp_valid_preserve_s: 
  "\<lbrakk>((s,c),e,(s',c'))\<in>trp fg; valid fg (add_mset s c)\<rbrakk> \<Longrightarrow> valid fg (add_mset s' c')"
  by (rule gtrp_preserve_s[where P="valid fg"]) (auto dest: trss_valid_preserve_s)

lemma (in flowgraph) trp_valid_preserve: 
  "\<lbrakk>((s,c),w,(s',c'))\<in>trcl (trp fg); valid fg ({#s#}+c)\<rbrakk> \<Longrightarrow> valid fg (add_mset s' c')"
  by (rule gtrp_preserve[where P="valid fg"]) (auto dest: trss_valid_preserve_s)


subsubsection "Equivalence to reference point"
text_raw \<open>\label{sec:Semantics: refpoint_eq}\<close>
\<comment> \<open>The equivalence between the semantics that we derived using the techniques from Section~\ref{thy:ThreadTracking} and the semantic reference point is shown nearly automatically.\<close>
lemma refpoint_eq_s: "valid fg c \<Longrightarrow> ((c,e,c')\<in>refpoint fg) \<longleftrightarrow> ((c,e,c')\<in>tr fg)"
  apply rule
  apply (erule refpoint.cases)
      apply (auto intro: gtrI_s trss.intros simp add: union_assoc add_mset_commute)
  apply (erule gtrE)
  apply (erule trss.cases)
  apply (auto intro: refpoint.intros simp add: union_assoc[symmetric] add_mset_commute)
  done
  
lemma (in flowgraph) refpoint_eq: 
  "valid fg c \<Longrightarrow> ((c,w,c')\<in>trcl (refpoint fg)) \<longleftrightarrow> ((c,w,c')\<in>trcl (tr fg))" 
proof -
  have "((c,w,c')\<in>trcl (refpoint fg)) \<Longrightarrow> valid fg c \<Longrightarrow> ((c,w,c')\<in>trcl (tr fg))" by (induct rule: trcl.induct) (auto simp add: refpoint_eq_s tr_valid_preserve_s)
  moreover have "((c,w,c')\<in>trcl (tr fg)) \<Longrightarrow> valid fg c \<Longrightarrow> ((c,w,c')\<in>trcl (refpoint fg))" by (induct rule: trcl.induct) (auto simp add: refpoint_eq_s tr_valid_preserve_s)
  ultimately show "valid fg c \<Longrightarrow> ((c,w,c')\<in>trcl (refpoint fg)) = ((c,w,c')\<in>trcl (tr fg))" ..
qed

subsubsection \<open>Case distinctions\<close>

lemma trss_c_cases_s[cases set, case_names no_spawn spawn]: "\<lbrakk> 
    ((s,c),e,(s',c'))\<in>trss fg; 
    \<lbrakk> c'=c \<rbrakk> \<Longrightarrow> P; 
    !!p u v. \<lbrakk> e=LSpawn p; (u,Spawn p,v)\<in>edges fg; 
               hd s=u; hd s'=v; c'={#[ entry fg p ]#}+c \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
by (auto elim!: trss.cases)
lemma trss_c_fmt_s: "\<lbrakk>((s,c),e,(s',c'))\<in>trss fg\<rbrakk> 
  \<Longrightarrow> \<exists>csp. c'=csp+c \<and> 
        (csp={#} \<or> (\<exists>p. e=LSpawn p \<and> csp={#[ entry fg p ]#}))"
  by (force elim!: trss_c_cases_s)
  
lemma (in flowgraph) trss_c'_split_s: "\<lbrakk>
    ((s,c),e,(s',c'))\<in>trss fg; 
    !!csp. \<lbrakk>c'=csp+c; mon_c fg csp={}\<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
  apply (erule trss_c_cases_s)
  apply (subgoal_tac "c'={#}+c")
  apply (fastforce)
  apply auto
  done

lemma trss_c_cases[cases set, case_names c_case]: "!!s c. \<lbrakk> 
    ((s,c),w,(s',c'))\<in>trcl (trss fg); 
    !!csp. \<lbrakk> c'=csp+c; !!s. s \<in># csp \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> 
                                               (u,Spawn p,v)\<in>edges fg \<and> 
                                               initialproc fg p\<rbrakk> 
            \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P" 
proof (induct w)
  case Nil note A=this 
  hence "s'=s" "c'=c" by simp_all
  hence "c'={#}+c" by simp
  from A(2)[OF this] show P by simp
next  
  case (Cons e w) note IHP=this
  then obtain sh ch where SPLIT1: "((s,c),e,(sh,ch))\<in>trss fg" and SPLIT2: "((sh,ch),w,(s',c'))\<in>trcl (trss fg)" by (fastforce dest: trcl_uncons)
  from SPLIT2 show ?case proof (rule IHP(1))
    fix csp
    assume C'FMT: "c'=csp+ch" and CSPFMT: "!!s. s \<in># csp \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> (u,Spawn p, v)\<in>edges fg \<and> initialproc fg p"
    from SPLIT1 show ?thesis
    proof (rule trss_c_cases_s)
      assume "ch=c" with C'FMT CSPFMT IHP(3) show ?case by blast
    next
      fix p
      assume EFMT: "e=LSpawn p" and CHFMT: "ch={#[entry fg p]#}+c" 
      with C'FMT have "c'=({#[entry fg p]#}+csp)+c" by (simp add: union_ac)
      moreover 
      from EFMT SPLIT1 have "\<exists>u v. (u,Spawn p, v)\<in>edges fg" by (blast elim!: trss.cases)
      hence "!!s. s \<in># {#[entry fg p]#} + csp \<Longrightarrow> \<exists>p u v. s=[entry fg p] \<and> (u,Spawn p, v)\<in>edges fg \<and> initialproc fg p" using CSPFMT by (unfold initialproc_def, erule_tac mset_un_cases) (auto)
      ultimately show ?case using IHP(3) by blast
    qed
  qed
qed

lemma (in flowgraph) c_of_initial_no_mon: 
  assumes A: "!!s. s \<in># csp \<Longrightarrow> \<exists>p. s=[entry fg p] \<and> initialproc fg p" 
  shows "mon_c fg csp = {}"
  by (unfold mon_c_def) (auto dest: A initial_no_mon)
  
  (* WARNING: Don't declare this [simp], as c=c' will cause a simplifier loop *)
lemma (in flowgraph) trss_c_no_mon_s: 
  assumes A: "((s,c),e,(s',c'))\<in>trss fg" 
  shows "mon_c fg c' = mon_c fg c" 
  using A 
proof (erule_tac trss_c_cases_s)
  assume "c'=c" thus ?thesis by simp
next
  fix p assume EFMT: "e=LSpawn p" and C'FMT: "c'={#[entry fg p]#} + c"
  from EFMT obtain u v where "(u,Spawn p,v)\<in>edges fg" using A by (auto elim: trss.cases)
  with spawn_no_mon have "mon_c fg {#[entry fg p]#} = {}" by simp
  with C'FMT show ?thesis by (simp add: mon_c_unconc)
qed
        
  (* WARNING: Don't declare this [simp], as c=c' will cause a simplifier loop *)
  (* FIXME: Dirty proof, not very robust *)
corollary (in flowgraph) trss_c_no_mon: 
  "((s,c),w,(s',c'))\<in>trcl (trss fg) \<Longrightarrow> mon_c fg c' = mon_c fg c" 
  apply (auto elim!: trss_c_cases simp add: mon_c_unconc)
proof -
  fix csp x
  assume "x\<in>mon_c fg csp"
  then obtain s where "s \<in># csp" and M: "x\<in>mon_s fg s" by (unfold mon_c_def, auto) 
  moreover assume "\<forall>s. s \<in># csp \<longrightarrow> (\<exists>p. s = [entry fg p] \<and> (\<exists>u v. (u, Spawn p, v) \<in> edges fg) \<and> initialproc fg p)"
  ultimately obtain p u v where "s=[entry fg p]" and "(u,Spawn p,v)\<in>edges fg" by blast
  hence "mon_s fg s = {}" by (simp)
  with M have False by simp
  thus "x\<in>mon_c fg c" ..
qed


lemma (in flowgraph) trss_spawn_no_mon_step[simp]: 
  "((s,c),LSpawn p, (s',c'))\<in>trss fg \<Longrightarrow> mon fg p = {}"
  by (auto elim: trss.cases)

lemma trss_no_empty_s[simp]: "(([],c),e,(s',c'))\<in>trss fg = False"
  by (auto elim!: trss.cases)
lemma trss_no_empty[simp]: 
  assumes A: "(([],c),w,(s',c'))\<in>trcl (trss fg)" 
  shows "w=[] \<and> s'=[] \<and> c=c'" 
proof -
  note A 
  moreover { 
    fix s
    have "((s,c),w,(s',c'))\<in>trcl (trss fg) \<Longrightarrow> s=[] \<Longrightarrow> w=[] \<and> s'=[] \<and> c=c'"
      by (induct rule: trcl_pair_induct) auto
  } ultimately show ?thesis by blast
qed


lemma trs_step_cases[cases set, case_names NO_SPAWN SPAWN]: 
  assumes A: "(c,e,c')\<in>tr fg" 
  assumes A_NO_SPAWN: "!!s ce s' csp. \<lbrakk>
      ((s,ce),e,(s',ce))\<in>trss fg; 
      c={#s#}+ce; c'={#s'#}+ce
    \<rbrakk> \<Longrightarrow> P"
  assumes A_SPAWN: "!!s ce s' p. \<lbrakk>
      ((s,ce),LSpawn p,(s',{#[entry fg p]#}+ce))\<in>trss fg; 
      c={#s#}+ce; 
      c'={#s'#}+{#[entry fg p]#}+ce; 
      e=LSpawn p
    \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from A show ?thesis proof (erule_tac gtr_find_thread)
    fix s ce s' ce' 
    assume FMT: "c = add_mset s ce" "c' = add_mset s' ce'"
    assume B: "((s, ce), e, s', ce') \<in> trss fg" thus ?thesis proof (cases rule: trss_c_cases_s)
      case no_spawn thus ?thesis using FMT B by (-) (rule A_NO_SPAWN, auto)  
    next
      case (spawn p) thus ?thesis using FMT B by (-) (rule A_SPAWN, auto simp add: union_assoc)
    qed
  qed
qed

subsection "Advanced properties"
subsubsection "Stack composition / decomposition"
lemma trss_stack_comp_s: 
  "((s,c),e,(s',c'))\<in>trss fg \<Longrightarrow> ((s@r,c),e,(s'@r,c'))\<in>trss fg"
  by (auto elim!: trss.cases intro: trss.intros)

lemma trss_stack_comp: 
  "((s,c),w,(s',c'))\<in>trcl (trss fg) \<Longrightarrow> ((s@r,c),w,(s'@r,c'))\<in>trcl (trss fg)" 
proof (induct rule: trcl_pair_induct)
  case empty thus ?case by auto
next
  case (cons s c e sh ch w s' c') note IHP=this
  from trss_stack_comp_s[OF IHP(1)] have "((s @ r, c), e, sh @ r, ch) \<in> trss fg" .
  also note IHP(3)
  finally show ?case .
qed

lemma trss_stack_decomp_s: "\<lbrakk> ((s@r,c),e,(s',c'))\<in>trss fg; s\<noteq>[] \<rbrakk> 
  \<Longrightarrow> \<exists>sp'. s'=sp'@r \<and> ((s,c),e,(sp',c'))\<in>trss fg" 
  by (cases s, simp) (auto intro: trss.intros elim!: trss.cases)

lemma trss_find_return: "\<lbrakk> 
    ((s@r,c),w,(r,c'))\<in>trcl (trss fg); 
    !!wa wb ch. \<lbrakk> w=wa@wb; ((s,c),wa,([],ch))\<in>trcl (trss fg); 
                  ((r,ch),wb,(r,c'))\<in>trcl (trss fg) \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  \<comment> \<open>If @{term "s=[]"}, the proposition follows trivially\<close>
  apply (cases "s=[]")
  apply fastforce
proof -
  \<comment> \<open>For @{term "s\<noteq>[]"}, we use induction by @{term w}\<close>
  have IM: "!!s c. \<lbrakk> ((s@r,c),w,(r,c'))\<in>trcl (trss fg); s\<noteq>[] \<rbrakk> \<Longrightarrow> \<exists>wa wb ch. w=wa@wb \<and> ((s,c),wa,([],ch))\<in>trcl (trss fg) \<and> ((r,ch),wb,(r,c'))\<in>trcl (trss fg)"
  proof (induct w)
    case Nil thus ?case by (auto)
  next
    case (Cons e w) note IHP=this
    then obtain sh ch where SPLIT1: "((s@r,c),e,(sh,ch))\<in>trss fg" and SPLIT2: "((sh,ch),w,(r,c'))\<in>trcl (trss fg)" by (fast dest: trcl_uncons)
    { assume CASE: "e=LRet"
      with SPLIT1 obtain p where EDGE: "s@r=return fg p # sh" "c=ch" by (auto elim!: trss.cases)
      with IHP(3) obtain ss where SHFMT: "s=return fg p # ss" "sh=ss@r" by (cases s, auto) 
      { assume CC: "ss\<noteq>[]"
        with SHFMT have "\<exists>ss. ss\<noteq>[] \<and> sh=ss@r" by blast
      } moreover {
        assume CC: "ss=[]"
        with CASE SHFMT EDGE have "((s,c),[e],([],ch))\<in>trcl (trss fg)" "e#w=[e]@w" by (auto intro: trss_ret)
        moreover from SPLIT2 SHFMT CC have "((r,ch),w,(r,c'))\<in>trcl (trss fg)" by simp
        ultimately have ?case by blast
      } ultimately have "?case \<or> (\<exists>ss. ss\<noteq>[] \<and> sh=ss@r)" by blast
    } moreover {
      assume "e\<noteq>LRet"
      with SPLIT1 IHP(3) have "(\<exists>ss. ss\<noteq>[] \<and> sh=ss@r)" by (force elim!: trss.cases simp add: append_eq_Cons_conv)
    } moreover {
      assume "(\<exists>ss. ss\<noteq>[] \<and> sh=ss@r)"
      then obtain ss where CASE: "ss\<noteq>[]" "sh=ss@r" by blast
      with SPLIT2 have "((ss@r, ch), w, r, c') \<in> trcl (trss fg)" by simp
      from IHP(1)[OF this CASE(1)] obtain wa wb ch' where IHAPP: "w=wa@wb" "((ss,ch),wa,([],ch'))\<in>trcl (trss fg)" "((r,ch'),wb,(r,c'))\<in>trcl (trss fg)" by blast
      moreover from CASE SPLIT1 have "((s @ r, c), e, ss@r, ch) \<in> trss fg" by simp
      from trss_stack_decomp_s[OF this IHP(3)] have "((s, c), e, ss, ch) \<in> trss fg" by auto
      with IHAPP have "((s, c), e#wa, ([],ch')) \<in> trcl (trss fg)" by (rule_tac trcl.cons)
      moreover from IHAPP have "e#w=(e#wa)@wb" by auto
      ultimately have ?case by blast
    } ultimately show ?case by blast
  qed
  assume "((s @ r, c), w, r, c') \<in> trcl (trss fg)" "s \<noteq> []" "!!wa wb ch. \<lbrakk> w=wa@wb; ((s,c),wa,([],ch))\<in>trcl (trss fg); ((r,ch),wb,(r,c'))\<in>trcl (trss fg) \<rbrakk> \<Longrightarrow> P" thus P by (blast dest: IM)
qed

    (* TODO: Try backward induction proof \<dots> is this simpler ? *)
lemma trss_return_cases[cases set]: "!!u r c. \<lbrakk> 
    ((u#r,c),w,(r',c'))\<in>trcl (trss fg);
    !! s' u'. \<lbrakk> r'=s'@u'#r; (([u],c),w,(s'@[u'],c'))\<in>trcl (trss fg) \<rbrakk> \<Longrightarrow> P; 
    !! wa wb ch. \<lbrakk> w=wa@wb; (([u],c),wa,([],ch))\<in>trcl (trss fg); 
                   ((r,ch),wb,(r',c'))\<in>trcl (trss fg) \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
proof (induct w rule: length_compl_induct)
  case Nil thus ?case by auto
next
  case (Cons e w) note IHP=this
  then obtain sh ch where SPLIT1: "((u#r,c),e,(sh,ch))\<in>trss fg" and SPLIT2: "((sh,ch),w,(r',c'))\<in>trcl (trss fg)" by (fast dest: trcl_uncons)
  {
    fix ba q
    assume CASE: "e=LBase ba \<or> e=LSpawn q"
    with SPLIT1 obtain v where E: "sh=v#r" "(([u],c),e,([v],ch))\<in>trss fg" by (auto elim!: trss.cases intro: trss.intros)
    with SPLIT2 have "((v#r,ch),w,(r',c'))\<in>trcl (trss fg)" by simp
    hence ?case proof (cases rule: IHP(1)[of w, simplified, cases set])
      case (1 s' u') note CC=this
      with E(2) have "(([u],c),e#w,(s'@[u'],c'))\<in>trcl (trss fg)" by simp
      from IHP(3)[OF CC(1) this] show ?thesis .
    next
      case (2 wa wb ct) note CC=this
      with E(2) have "(([u],c),e#wa,([],ct))\<in>trcl (trss fg)" "e#w = (e#wa)@wb" by simp_all
      from IHP(4)[OF this(2,1) CC(3)] show ?thesis .
    qed
  } moreover {
    assume CASE: "e=LRet"
    with SPLIT1 have "sh=r" "(([u],c),[e],([],ch))\<in>trcl (trss fg)" by (auto elim!: trss.cases intro: trss.intros)
    with IHP(4)[OF _ this(2)] SPLIT2 have ?case by auto
  } moreover {
    fix q
    assume CASE: "e=LCall q"
    with SPLIT1 obtain u' where SHFMT: "sh=entry fg q # u' # r" "(([u],c),e,(entry fg q # [u'],ch))\<in>trss fg" by (auto elim!: trss.cases intro: trss.intros)
    with SPLIT2 have "((entry fg q # u' # r,ch),w,(r',c'))\<in>trcl (trss fg)" by simp
    hence ?case proof (cases rule: IHP(1)[of w, simplified, cases set])
      case (1 st ut) note CC=this
      from trss_stack_comp[OF CC(2), where r="[u']"] have "((entry fg q#[u'], ch), w, (st @ [ut]) @ [u'], c') \<in> trcl (trss fg)" by auto
      with SHFMT(2) have "(([u],c),e#w, (st @ [ut]) @ [u'], c') \<in> trcl (trss fg)" by auto
      from IHP(3)[OF _ this] CC(1) show ?thesis by simp
    next
      case (2 wa wb ct) note CC=this
      from trss_stack_comp[OF CC(2), where r="[u']"] have "((entry fg q # [u'], ch), wa, [u'], ct) \<in> trcl (trss fg)" by simp
      with SHFMT have PREPATH: "(([u],c),e#wa, [u'], ct) \<in> trcl (trss fg)" by simp
      from CC have L: "length wb\<le>length w" by simp
      from CC(3) show ?case proof (cases rule: IHP(1)[OF L, cases set])
        case (1 s'' u'') note CCC=this from trcl_concat[OF PREPATH CCC(2)] CC(1) have "(([u],c),e#w,(s''@[u''],c'))\<in>trcl (trss fg)" by (simp)
        from IHP(3)[OF CCC(1) this] show ?thesis .
      next
        case (2 wba wbb c'') note CCC=this from trcl_concat[OF PREPATH CCC(2)] CC(1) CCC(1) have "e#w = (e#wa@wba)@wbb" "(([u], c), e # wa @ wba, [], c'') \<in> trcl (trss fg)" by auto
        from IHP(4)[OF this CCC(3)] show ?thesis .
      qed
    qed
  } ultimately show ?case by (cases e, auto)
qed

lemma (in flowgraph) trss_find_call: 
  "!!v r' c'. \<lbrakk> (([sp],c),w,(v#r',c')) \<in> trcl (trss fg); r'\<noteq>[] \<rbrakk> 
  \<Longrightarrow> \<exists>rh ch p wa wb. 
        w=wa@(LCall p)#wb \<and> 
        proc_of fg v = p \<and> 
        (([sp],c),wa,(rh,ch))\<in>trcl (trss fg) \<and> 
        ((rh,ch),LCall p,((entry fg p)#r',ch))\<in>trss fg \<and> 
        (([entry fg p],ch),wb,([v],c'))\<in>trcl (trss fg)"
proof (induct w rule: length_compl_rev_induct)
  case Nil thus ?case by (auto) 
next
  case (snoc w e) note IHP=this
  then obtain rh ch where SPLIT1: "(([sp],c),w,(rh,ch))\<in>trcl (trss fg)" and SPLIT2: "((rh,ch),e,(v#r',c'))\<in>trss fg" by (fast dest: trcl_rev_uncons)

  {
    assume "\<exists>u. rh=u#r'"
    then obtain u where RHFMT[simp]: "rh=u#r'" by blast
    with SPLIT2 have "proc_of fg u = proc_of fg v" by (auto elim: trss.cases intro: edges_part)
    moreover from IHP(1)[of w u r' ch, OF _ SPLIT1[simplified] IHP(3)] obtain rt ct p wa wb where 
      IHAPP: "w = wa @ LCall p # wb" "proc_of fg u = p" "(([sp], c), wa, (rt, ct)) \<in> trcl (trss fg)" "((rt, ct), LCall p, entry fg p # r', ct) \<in> trss fg"  
          "(([entry fg p], ct), wb, ([u], ch)) \<in> trcl (trss fg)" by (blast)
    moreover
    have "(([entry fg p], ct), wb@[e], ([v], c')) \<in> trcl (trss fg)" proof -
      note IHAPP(5)
      also from SPLIT2 have "(([u],ch),e,([v],c')) \<in> trss fg" by (auto elim!: trss.cases intro!: trss.intros)
      finally show ?thesis .
    qed
    moreover from IHAPP have "w@[e] = wa @ LCall p # (wb@[e])" by auto
    ultimately have ?case by auto
  }
  moreover have "(\<exists>u. rh=u#r') \<or> ?case"
  proof (rule trss.cases[OF SPLIT2], simp_all, goal_cases) \<comment> \<open>Cases for base- and spawn edge are discharged automatically\<close>
      \<comment> \<open>Case: call-edge\<close>
    case (1 ca p r u vv) with SPLIT1 SPLIT2 show ?case by fastforce 
  next
      \<comment> \<open>Case: return edge\<close>
    case CC: (2 q r ca)
    hence [simp]: "rh=(return fg q)#v#r'" by simp
    with IHP(1)[of w "(return fg q)" "v#r'" ch, OF _ SPLIT1[simplified]] obtain rt ct wa wb where 
      IHAPP: "w = wa @ LCall q # wb" "(([sp], c), wa, rt, ct) \<in> trcl (trss fg)" "((rt, ct), LCall q, entry fg q # v # r', ct) \<in> trss fg"
          "(([entry fg q], ct), wb, [return fg q], ch) \<in> trcl (trss fg)" by force
    then obtain u where RTFMT [simp]: "rt=u#r'" and PROC_OF_U: "proc_of fg u = proc_of fg v" by (auto elim: trss.cases intro: edges_part)
    from IHAPP(1) have LENWA: "length wa \<le> length w" by auto
    from IHP(1)[OF LENWA IHAPP(2)[simplified] IHP(3)] obtain rhh chh p waa wab where 
      IHAPP': "wa=waa@LCall p # wab" "proc_of fg u = p" "(([sp],c),waa,(rhh,chh))\<in>trcl (trss fg)" "((rhh,chh),LCall p, (entry fg p#r',chh))\<in>trss fg" 
          "(([entry fg p],chh),wab,([u],ct))\<in>trcl (trss fg)" 
      by blast
    from IHAPP IHAPP' PROC_OF_U have "w@[e]=waa@LCall p#(wab@LCall q#wb@[e]) \<and> proc_of fg v = p" by auto
    moreover have "(([entry fg p],chh),wab@(LCall q)#wb@[e],([v],c'))\<in>trcl (trss fg)" proof -
      note IHAPP'(5)
      also from IHAPP have "(([u], ct), LCall q, entry fg q # [v], ct) \<in> trss fg" by (auto elim!: trss.cases intro!: trss.intros)
      also from trss_stack_comp[OF IHAPP(4)] have "((entry fg q#[v],ct),wb,(return fg q#[v],ch))\<in>trcl (trss fg)" by simp
      also from CC have "((return fg q#[v],ch),e,([v],c'))\<in>trss fg" by (auto intro: trss_ret)
      finally show ?thesis by simp
    qed
    moreover note IHAPP' CC
    ultimately show ?case by auto
  qed
  ultimately show ?case by blast
qed

\<comment> \<open>This lemma is better suited for application in soundness proofs of constraint systems than @{thm [source] flowgraph.trss_find_call}\<close>
lemma (in flowgraph) trss_find_call': 
  assumes A: "(([sp],c),w,(return fg p#[u'],c')) \<in> trcl (trss fg)" 
  and EX: "!!uh ch wa wb. \<lbrakk>
      w=wa@(LCall p)#wb; 
      (([sp],c),wa,([uh],ch))\<in>trcl (trss fg); 
      (([uh],ch),LCall p,((entry fg p)#[u'],ch))\<in>trss fg;
      (uh,Call p,u')\<in>edges fg; 
      (([entry fg p],ch),wb,([return fg p],c'))\<in>trcl (trss fg)
    \<rbrakk> \<Longrightarrow> P" 
  shows "P"
proof -
  from trss_find_call[OF A] obtain rh ch wa wb where FC: 
    "w = wa @ LCall p # wb" 
    "(([sp], c), wa, rh, ch) \<in> trcl (trss fg)" 
    "((rh, ch), LCall p, [entry fg p, u'], ch) \<in> trss fg" 
    "(([entry fg p], ch), wb, [return fg p], c') \<in> trcl (trss fg)"
    by auto
  moreover from FC(3) obtain uh where ADD: "rh=[uh]" "(uh,Call p,u')\<in>edges fg" by (auto elim: trss.cases)
  ultimately show ?thesis using EX by auto
qed
      
lemma (in flowgraph) trss_bot_proc_const: 
  "!!s' u' c'. ((s@[u],c),w,(s'@[u'],c'))\<in>trcl (trss fg) 
    \<Longrightarrow> proc_of fg u = proc_of fg u'" 
proof (induct w rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc e w) note IHP=this then obtain sh ch where SPLIT1: "((s@[u],c),w,(sh,ch))\<in>trcl (trss fg)" and SPLIT2: "((sh,ch),e,(s'@[u'],c'))\<in>trss fg" by (fast dest: trcl_rev_uncons)
  from SPLIT2 have "sh\<noteq>[]" by (auto elim!: trss.cases)
  then obtain ssh uh where SHFMT: "sh=ssh@[uh]" by (blast dest: list_rev_decomp)
  with IHP(1)[of ssh uh ch] SPLIT1 have "proc_of fg u = proc_of fg uh" by auto
  also from SPLIT2 SHFMT have "proc_of fg uh = proc_of fg u'" by (cases rule: trss.cases) (cases ssh, auto simp add: edges_part)+
  finally show ?case .
qed

\<comment> \<open>Specialized version of @{thm [source] flowgraph.trss_bot_proc_const}that comes in handy for precision proofs of constraint systems\<close>
lemma (in flowgraph) trss_er_path_proc_const: 
  "(([entry fg p],c),w,([return fg q],c'))\<in>trcl (trss fg) \<Longrightarrow> p=q"
  using trss_bot_proc_const[of "[]" "entry fg p" _ _ "[]" "return fg q", simplified] .

lemma trss_2empty_to_2return: "\<lbrakk> ((s,c),w,([],c'))\<in>trcl (trss fg); s\<noteq>[] \<rbrakk> \<Longrightarrow> 
  \<exists>w' p. w=w'@[LRet] \<and> ((s,c),w',([return fg p],c'))\<in>trcl (trss fg)" 
proof -
  assume A: "((s,c),w,([],c'))\<in>trcl (trss fg)" "s\<noteq>[]"
  hence "w\<noteq>[]" by auto
  then obtain w' e where WD: "w=w'@[e]" by (blast dest: list_rev_decomp)
  with A(1) obtain sh ch where SPLIT: "((s,c),w',(sh,ch))\<in>trcl (trss fg)" "((sh,ch),e,([],c'))\<in>trss fg" by (fast dest: trcl_rev_uncons)
  from SPLIT(2) obtain p where "e=LRet" "sh=[return fg p]" "ch=c'" by (cases rule: trss.cases, auto)
  with SPLIT(1) WD show ?thesis by blast
qed
  
lemma trss_2return_to_2empty: "\<lbrakk> ((s,c),w,([return fg p],c'))\<in>trcl (trss fg) \<rbrakk> 
  \<Longrightarrow> ((s,c),w@[LRet],([],c'))\<in>trcl (trss fg)"
  apply (subgoal_tac "(([return fg p],c'),LRet,([],c'))\<in>trss fg")
  by (auto dest: trcl_rev_cons intro: trss.intros)

subsubsection "Adding threads"
lemma trss_env_increasing_s: "((s,c),e,(s',c'))\<in>trss fg \<Longrightarrow> c\<subseteq>#c'"
  by (auto elim!: trss.cases)
lemma trss_env_increasing: "((s,c),w,(s',c'))\<in>trcl (trss fg) \<Longrightarrow> c\<subseteq>#c'"
  by (induct rule: trcl_pair_induct) (auto dest: trss_env_increasing_s order_trans)

subsubsection "Conversion between environment and monitor restrictions"
lemma trss_mon_e_no_ctx: 
  "((s,c),e,(s',c'))\<in>trss fg \<Longrightarrow> mon_e fg e \<inter> mon_c fg c = {}"
  by (erule trss.cases) auto
lemma (in flowgraph) trss_mon_w_no_ctx: 
  "((s,c),w,(s',c'))\<in>trcl (trss fg) \<Longrightarrow> mon_w fg w \<inter> mon_c fg c = {}"
  by (induct rule: trcl_pair_induct) (auto dest: trss_mon_e_no_ctx simp add: trss_c_no_mon_s)

lemma (in flowgraph) trss_modify_context_s: 
  "!!cn. \<lbrakk>((s,c),e,(s',c'))\<in>trss fg; mon_e fg e \<inter> mon_c fg cn = {}\<rbrakk> 
    \<Longrightarrow> \<exists>csp. c'=csp+c \<and> mon_c fg csp = {} \<and> ((s,cn),e,(s',csp+cn))\<in>trss fg"
  by (erule trss.cases) (auto intro!: trss.intros)

lemma (in flowgraph) trss_modify_context[rule_format]: 
  "\<lbrakk>((s,c),w,(s',c'))\<in>trcl (trss fg)\<rbrakk> 
  \<Longrightarrow> \<forall>cn. mon_w fg w \<inter> mon_c fg cn = {} 
      \<longrightarrow> (\<exists>csp. c'=csp+c \<and> mon_c fg csp = {} \<and> 
                 ((s,cn),w,(s',csp+cn))\<in>trcl (trss fg))"
proof (induct rule: trcl_pair_induct)
  case empty thus ?case by simp 
next
  case (cons s c e sh ch w s' c') note IHP=this show ?case 
  proof (intro allI impI)
    fix cn
    assume MON: "mon_w fg (e # w) \<inter> mon_c fg cn = {}"
    from trss_modify_context_s[OF IHP(1)] MON obtain csph where S1: "ch = csph + c" "mon_c fg csph={}" "((s, cn), e, sh, csph + cn) \<in> trss fg" by auto
    with MON have "mon_w fg w \<inter> mon_c fg (csph+cn) = {}" by (auto simp add: mon_c_unconc)
    with IHP(3)[rule_format] obtain csp where S2: "c'=csp+ch" "mon_c fg csp={}" "((sh,csph+cn),w,(s',csp+(csph+cn)))\<in>trcl (trss fg)" by blast 
    from S1 S2 have "c'=(csp+csph)+c" "mon_c fg (csp+csph)={}" "((s,cn),e#w,(s',(csp+csph)+cn))\<in>trcl (trss fg)" by (auto simp add: union_assoc mon_c_unconc)
    thus "\<exists>csp. c' = csp + c \<and> mon_c fg csp = {} \<and> ((s, cn), e # w, s', csp + cn) \<in> trcl (trss fg)" by blast
  qed
qed

lemma trss_add_context_s: 
  "\<lbrakk>((s,c),e,(s',c'))\<in>trss fg; mon_e fg e \<inter> mon_c fg ce = {}\<rbrakk> 
    \<Longrightarrow> ((s,c+ce),e,(s',c'+ce))\<in>trss fg"
  by (auto elim!: trss.cases intro!: trss.intros simp add: union_assoc mon_c_unconc)

lemma trss_add_context: 
  "\<lbrakk>((s,c),w,(s',c'))\<in>trcl (trss fg); mon_w fg w \<inter> mon_c fg ce = {}\<rbrakk> 
    \<Longrightarrow> ((s,c+ce),w,(s',c'+ce))\<in>trcl (trss fg)" 
proof (induct rule: trcl_pair_induct)
  case empty thus ?case by simp
next
  case (cons s c e sh ch w s' c') note IHP=this
  from IHP(4) have MM: "mon_e fg e \<inter> mon_c fg ce = {}" "mon_w fg w \<inter> mon_c fg ce = {}" by auto
  from trcl.cons[OF trss_add_context_s[OF IHP(1) MM(1)] IHP(3)[OF MM(2)]] show ?case .
qed
  
lemma trss_drop_context_s: "\<lbrakk> ((s,c+ce),e,(s',c'+ce))\<in>trss fg \<rbrakk> 
  \<Longrightarrow> ((s,c),e,(s',c'))\<in>trss fg \<and> mon_e fg e \<inter> mon_c fg ce = {}"
  by (erule trss.cases) (auto intro!: trss.intros simp add: mon_c_unconc union_assoc[of _ c ce, symmetric])

lemma trss_drop_context: "!!s c. \<lbrakk> ((s,c+ce),w,(s',c'+ce))\<in>trcl (trss fg) \<rbrakk> 
  \<Longrightarrow> ((s,c),w,(s',c'))\<in>trcl (trss fg) \<and> mon_w fg w \<inter> mon_c fg ce = {}" 
proof (induct w)
  case Nil thus ?case by auto
next
  case (Cons e w) note IHP=this
  then obtain sh ch where SPLIT: "((s,c+ce),e,(sh,ch))\<in>trss fg" "((sh,ch),w,(s',c'+ce))\<in> trcl (trss fg)" by (fast dest: trcl_uncons)
  from trss_c_fmt_s[OF SPLIT(1)] obtain csp where CHFMT: "ch = (csp + c) + ce" by (auto simp add: union_assoc)
  from CHFMT trss_drop_context_s SPLIT(1) have "((s,c),e,(sh,csp+c))\<in>trss fg" "mon_e fg e \<inter> mon_c fg ce = {}" by blast+
  moreover from CHFMT IHP(1) SPLIT(2) have "((sh,csp+c),w,(s',c'))\<in>trcl (trss fg)" "mon_w fg w \<inter> mon_c fg ce = {}" by blast+
  ultimately show ?case by auto
qed

lemma trss_xchange_context_s: 
  assumes A: "((s,c),e,(s',csp+c))\<in>trss fg" 
  and M:"mon_c fg cn \<subseteq> mon_c fg c" 
  shows "((s,cn),e,(s',csp+cn))\<in>trss fg"
proof -
  from trss_drop_context_s[of _ "{#}", simplified, OF A] have DC: "((s, {#}), e, s', csp) \<in> trss fg" "mon_e fg e \<inter> mon_c fg c = {}" by simp_all
  with M have "mon_e fg e \<inter> mon_c fg cn = {}" by auto
  from trss_add_context_s[OF DC(1) this] show ?thesis by auto
qed
  
lemma trss_xchange_context: 
  assumes A: "((s,c),w,(s',csp+c))\<in>trcl (trss fg)" 
  and M:"mon_c fg cn \<subseteq> mon_c fg c" 
  shows "((s,cn),w,(s',csp+cn))\<in>trcl (trss fg)"
proof -
  from trss_drop_context[of _ "{#}", simplified, OF A] have DC: "((s, {#}), w, s', csp) \<in> trcl (trss fg)" "mon_w fg w \<inter> mon_c fg c = {}" by simp_all
  with M have "mon_w fg w \<inter> mon_c fg cn = {}" by auto
  from trss_add_context[OF DC(1) this] show ?thesis by auto
qed

lemma trss_drop_all_context_s[cases set, case_names dropped]: 
  assumes A: "((s,c),e,(s',c'))\<in>trss fg" 
  and C: "!!csp. \<lbrakk> c'=csp+c; ((s,{#}),e,(s',csp))\<in>trss fg \<rbrakk> \<Longrightarrow> P" 
  shows P
using A proof (cases rule: trss_c_cases_s)
  case no_spawn with trss_xchange_context_s[of s c e s' "{#}" fg "{#}"] A C show P by auto
next
  case (spawn p u v) with trss_xchange_context_s[of s c e s' "{#[entry fg p]#}" fg "{#}"] A C show P by auto
qed

lemma trss_drop_all_context[cases set, case_names dropped]: 
  assumes A: "((s,c),w,(s',c'))\<in>trcl (trss fg)" 
  and C: "!!csp. \<lbrakk> c'=csp+c; ((s,{#}),w,(s',csp))\<in>trcl (trss fg)\<rbrakk> \<Longrightarrow> P" 
  shows P
using A proof (cases rule: trss_c_cases)
  case (c_case csp) with trss_xchange_context[of s c w s' csp fg "{#}"] A C show P by auto
qed

lemma tr_add_context_s: 
  "\<lbrakk> (c,e,c')\<in>tr fg; mon_e fg e \<inter> mon_c fg ce = {} \<rbrakk> \<Longrightarrow> (c+ce,e,c'+ce)\<in>tr fg"
  by (erule gtrE) (auto simp add: mon_c_unconc union_assoc intro: gtrI_s dest: trss_add_context_s)

lemma tr_add_context: 
  "\<lbrakk> (c,w,c')\<in>trcl (tr fg); mon_w fg w \<inter> mon_c fg ce = {} \<rbrakk> 
    \<Longrightarrow> (c+ce,w,c'+ce)\<in>trcl (tr fg)" 
proof (induct rule: trcl.induct)
  case empty thus ?case by auto
next
  case (cons c e c' w c'') note IHP=this
  from tr_add_context_s[OF IHP(1), of ce] IHP(4) have "(c + ce, e, c' + ce) \<in> tr fg" by auto
  also from IHP(3,4) have "(c' + ce, w, c'' + ce) \<in> trcl (tr fg)" by auto
  finally show ?case .
qed
   
end

