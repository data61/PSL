(*  Title:      JinjaThreads/Common/Conform.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Conform.thy by David von Oheimb and Tobias Nipkow
*)

section \<open>Conformance Relations for Type Soundness Proofs\<close>

theory Conform
imports
  StartConfig
begin

context heap_base begin

definition conf :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr val \<Rightarrow> ty \<Rightarrow> bool"   ("_,_ \<turnstile> _ :\<le> _"  [51,51,51,51] 50)
where "P,h \<turnstile> v :\<le> T  \<equiv> \<exists>T'. typeof\<^bsub>h\<^esub> v = Some T' \<and> P \<turnstile> T' \<le> T"

definition lconf :: "'m prog \<Rightarrow> 'heap \<Rightarrow> (vname \<rightharpoonup> 'addr val) \<Rightarrow> (vname \<rightharpoonup> ty) \<Rightarrow> bool"   ("_,_ \<turnstile> _ '(:\<le>') _" [51,51,51,51] 50)
where "P,h \<turnstile> l (:\<le>) E  \<equiv> \<forall>V v. l V = Some v \<longrightarrow> (\<exists>T. E V = Some T \<and> P,h \<turnstile> v :\<le> T)"

abbreviation confs :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [:\<le>] _" [51,51,51,51] 50)
where "P,h \<turnstile> vs [:\<le>] Ts  ==  list_all2 (conf P h) vs Ts"

definition tconf :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'thread_id \<Rightarrow> bool" ("_,_ \<turnstile> _ \<surd>t" [51,51,51] 50)
where "P,h \<turnstile> t \<surd>t \<equiv> \<exists>C. typeof_addr h (thread_id2addr t) = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"

end

locale heap_conf_base =
  heap_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  fixes hconf :: "'heap \<Rightarrow> bool"
  and P :: "'m prog"

sublocale heap_conf_base < prog P .

locale heap_conf = 
  heap
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    P
  +
  heap_conf_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    hconf P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool" 
  and P :: "'m prog" 
  +
  assumes hconf_empty [iff]: "hconf empty_heap"
  and typeof_addr_is_type: "\<lbrakk> typeof_addr h a = \<lfloor>hT\<rfloor>; hconf h \<rbrakk> \<Longrightarrow> is_type P (ty_of_htype hT)"
  and hconf_allocate_mono: "\<And>a. \<lbrakk> (h', a) \<in> allocate h hT; hconf h; is_htype P hT \<rbrakk> \<Longrightarrow> hconf h'"
  and hconf_heap_write_mono:
  "\<And>T. \<lbrakk> heap_write h a al v h'; hconf h; P,h \<turnstile> a@al : T; P,h \<turnstile> v :\<le> T \<rbrakk> \<Longrightarrow> hconf h'"

locale heap_progress =
  heap_conf
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    hconf P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool" 
  and P :: "'m prog" 
  +
  assumes heap_read_total: "\<lbrakk> hconf h; P,h \<turnstile> a@al : T \<rbrakk> \<Longrightarrow> \<exists>v. heap_read h a al v \<and> P,h \<turnstile> v :\<le> T"
  and heap_write_total: "\<lbrakk> hconf h; P,h \<turnstile> a@al : T; P,h \<turnstile> v :\<le> T \<rbrakk> \<Longrightarrow> \<exists>h'. heap_write h a al v h'"

locale heap_conf_read =
  heap_conf
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    hconf P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool" 
  and P :: "'m prog" 
  +
  assumes heap_read_conf: "\<lbrakk> heap_read h a al v; P,h \<turnstile> a@al : T; hconf h \<rbrakk> \<Longrightarrow> P,h \<turnstile> v :\<le> T"

locale heap_typesafe =
  heap_conf_read +
  heap_progress +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'m prog"

context heap_conf begin

lemmas hconf_heap_ops_mono = 
  hconf_allocate_mono
  hconf_heap_write_mono

end

subsection\<open>Value conformance \<open>:\<le>\<close>\<close>

context heap_base begin

lemma conf_Null [simp]: "P,h \<turnstile> Null :\<le> T  =  P \<turnstile> NT \<le> T"
unfolding conf_def by(simp (no_asm))

lemma typeof_conf[simp]: "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
unfolding conf_def by (cases v) auto

lemma typeof_lit_conf[simp]: "typeof v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
by (rule typeof_conf[OF typeof_lit_typeof])

lemma defval_conf[simp]: "P,h \<turnstile> default_val T :\<le> T"
unfolding conf_def by (cases T) auto

lemma conf_widen: "P,h \<turnstile> v :\<le> T \<Longrightarrow> P \<turnstile> T \<le> T' \<Longrightarrow> P,h \<turnstile> v :\<le> T'"
unfolding conf_def by (cases v) (auto intro: widen_trans)

lemma conf_sys_xcpt:
  "\<lbrakk>preallocated h; C \<in> sys_xcpts\<rbrakk> \<Longrightarrow> P,h \<turnstile> Addr (addr_of_sys_xcpt C) :\<le> Class C"
by(simp add: conf_def typeof_addr_sys_xcp)

lemma conf_NT [iff]: "P,h \<turnstile> v :\<le> NT = (v = Null)"
by (auto simp add: conf_def)

lemma is_IntgI: "P,h \<turnstile> v :\<le> Integer \<Longrightarrow> is_Intg v"
by (unfold conf_def) auto

lemma is_BoolI: "P,h \<turnstile> v :\<le> Boolean \<Longrightarrow> is_Bool v"
by (unfold conf_def) auto

lemma is_RefI: "P,h \<turnstile> v :\<le> T \<Longrightarrow> is_refT T \<Longrightarrow> is_Ref v"
by(cases v)(auto elim: is_refT.cases simp add: conf_def is_Ref_def)

lemma non_npD:
  "\<lbrakk> v \<noteq> Null; P,h \<turnstile> v :\<le> Class C; C \<noteq> Object \<rbrakk> 
  \<Longrightarrow> \<exists>a C'. v = Addr a \<and> typeof_addr h a = \<lfloor>Class_type C'\<rfloor> \<and> P \<turnstile> C' \<preceq>\<^sup>* C"
by(cases v)(auto simp add: conf_def widen_Class)

lemma non_npD2:
  "\<lbrakk>v \<noteq> Null; P,h \<turnstile> v :\<le> Class C \<rbrakk>
  \<Longrightarrow> \<exists>a hT. v = Addr a \<and> typeof_addr h a = \<lfloor>hT\<rfloor> \<and> P \<turnstile> class_type_of hT \<preceq>\<^sup>* C"
by(cases v)(auto simp add: conf_def widen_Class)

end

context heap begin

lemma conf_hext: "\<lbrakk> h \<unlhd> h'; P,h \<turnstile> v :\<le> T \<rbrakk> \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
unfolding conf_def by(cases v)(auto dest: typeof_addr_hext_mono)

lemma conf_heap_ops_mono:
  assumes "P,h \<turnstile> v :\<le> T"
  shows conf_allocate_mono: "(h', a) \<in> allocate h hT \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
  and conf_heap_write_mono: "heap_write h a al v' h' \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
using assms
by(auto intro: conf_hext dest: hext_heap_ops)

end

subsection\<open>Value list conformance \<open>[:\<le>]\<close>\<close>

context heap_base begin

lemma confs_widens [trans]: "\<lbrakk>P,h \<turnstile> vs [:\<le>] Ts; P \<turnstile> Ts [\<le>] Ts'\<rbrakk> \<Longrightarrow> P,h \<turnstile> vs [:\<le>] Ts'"
by (rule list_all2_trans)(rule conf_widen)

lemma confs_rev: "P,h \<turnstile> rev s [:\<le>] t = (P,h \<turnstile> s [:\<le>] rev t)"
by(rule list_all2_rev1)

lemma confs_conv_map:
  "P,h \<turnstile> vs [:\<le>] Ts' = (\<exists>Ts. map typeof\<^bsub>h\<^esub> vs = map Some Ts \<and> P \<turnstile> Ts [\<le>] Ts')"
apply(induct vs arbitrary: Ts')
 apply simp
apply(case_tac Ts')
apply(auto simp add:conf_def)
apply(rule_tac x="T' # Ts" in exI)
apply(simp add: fun_of_def)
done

lemma confs_Cons2: "P,h \<turnstile> xs [:\<le>] y#ys = (\<exists>z zs. xs = z#zs \<and> P,h \<turnstile> z :\<le> y \<and> P,h \<turnstile> zs [:\<le>] ys)"
by (rule list_all2_Cons2)

end

context heap begin

lemma confs_hext: "P,h \<turnstile> vs [:\<le>] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> vs [:\<le>] Ts"
by (erule list_all2_mono, erule conf_hext, assumption)

end

subsection \<open>Local variable conformance\<close>

context heap_base begin

lemma lconf_upd:
  "\<lbrakk> P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T; E V = Some T \<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E"
unfolding lconf_def by auto

lemma lconf_empty [iff]: "P,h \<turnstile> Map.empty (:\<le>) E"
by(simp add:lconf_def)

lemma lconf_upd2: "\<lbrakk>P,h \<turnstile> l (:\<le>) E; P,h \<turnstile> v :\<le> T\<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)"
by(simp add:lconf_def)

end

context heap begin

lemma lconf_hext: "\<lbrakk> P,h \<turnstile> l (:\<le>) E; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l (:\<le>) E"
unfolding lconf_def by(fast elim: conf_hext)

end

subsection \<open>Thread object conformance\<close>

context heap_base begin

lemma tconfI: "\<lbrakk> typeof_addr h (thread_id2addr t) = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> P,h \<turnstile> t \<surd>t"
by(simp add: tconf_def)

lemma tconfD: "P,h \<turnstile> t \<surd>t \<Longrightarrow> \<exists>C. typeof_addr h (thread_id2addr t) = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Thread"
by(auto simp add: tconf_def)

end

context heap begin
 
lemma tconf_hext_mono: "\<lbrakk> P,h \<turnstile> t \<surd>t; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> t \<surd>t"
by(auto simp add: tconf_def dest: typeof_addr_hext_mono)

lemma tconf_heap_ops_mono:
  assumes "P,h \<turnstile> t \<surd>t"
  shows tconf_allocate_mono: "(h', a) \<in> allocate h hT \<Longrightarrow> P,h' \<turnstile> t \<surd>t"
  and tconf_heap_write_mono: "heap_write h a al v h' \<Longrightarrow> P,h' \<turnstile> t \<surd>t"
using tconf_hext_mono[OF assms, of h']
by(blast intro: hext_heap_ops)+

lemma tconf_start_heap_start_tid:
  "\<lbrakk> start_heap_ok; wf_syscls P \<rbrakk> \<Longrightarrow> P,start_heap \<turnstile> start_tid \<surd>t"
unfolding start_tid_def start_heap_def start_heap_ok_def start_heap_data_def initialization_list_def addr_of_sys_xcpt_def start_addrs_def sys_xcpts_list_def 
apply(clarsimp split: prod.split_asm simp add: create_initial_object_simps split: if_split_asm)
apply(erule not_empty_pairE)+
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule allocate_SomeD[where hT="Class_type Thread"])
 apply simp
apply(rule tconfI)
 apply(erule typeof_addr_hext_mono[OF hext_allocate])+
 apply simp
apply blast
done

lemma start_heap_write_typeable:
  assumes "WriteMem ad al v \<in> set start_heap_obs"
  shows "\<exists>T. P,start_heap \<turnstile> ad@al : T \<and> P,start_heap \<turnstile> v :\<le> T"
using assms
unfolding start_heap_obs_def start_heap_def
by clarsimp

end

subsection \<open>Well-formed start state\<close>

context heap_base begin

inductive wf_start_state :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> bool"
for P :: "'m prog" and C :: cname and M :: mname and vs :: "'addr val list"
where
  wf_start_state:
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D; start_heap_ok; P,start_heap \<turnstile> vs [:\<le>] Ts \<rbrakk>
  \<Longrightarrow> wf_start_state P C M vs"

end

end
