(*  Title:      JinjaThreads/MM/JMM_Type2.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM heap implementation 2\<close>

theory JMM_Type2
imports 
  "../Common/ExternalCallWF"
  "../Common/ConformThreaded"
  JMM_Heap
begin

subsection \<open>Definitions\<close>

datatype addr = Address htype nat   \<comment> \<open>heap type and sequence number\<close>

lemma rec_addr_conv_case_addr [simp]: "rec_addr = case_addr"
by(auto intro!: ext split: addr.split)

instantiation addr :: addr begin
definition "hash_addr (a :: addr) = (case a of Address ht n \<Rightarrow> int n)"
definition "monitor_finfun_to_list (ls :: addr \<Rightarrow>f nat) = (SOME xs. set xs = {x. finfun_dom ls $ x })"
instance
proof
  fix ls :: "addr \<Rightarrow>f nat"
  show "set (monitor_finfun_to_list ls) = Collect (($) (finfun_dom ls))"
    unfolding monitor_finfun_to_list_addr_def
    using finite_list[OF finite_finfun_dom, where ?f.1 = "ls"]
    by(rule someI_ex)
qed
end

primrec the_Address :: "addr \<Rightarrow> htype \<times> nat"
where "the_Address (Address hT n) = (hT, n)"

text \<open>
  The JMM heap only stores which sequence numbers of a given @{typ "htype"} have already been allocated.
\<close>

type_synonym JMM_heap = "htype \<Rightarrow> nat set"

translations (type) "JMM_heap" <= (type) "htype \<Rightarrow> nat set"

definition jmm_allocate :: "JMM_heap \<Rightarrow> htype \<Rightarrow> (JMM_heap \<times> addr) set"
where "jmm_allocate h hT = (let hhT = h hT in (\<lambda>n. (h(hT := insert n hhT), Address hT n)) ` (- hhT))"

abbreviation jmm_empty :: "JMM_heap" where "jmm_empty == (\<lambda>_. {})"

definition jmm_typeof_addr :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<rightharpoonup> htype"
where "jmm_typeof_addr P h = (\<lambda>hT. if is_htype P hT then Some hT else None) \<circ> fst \<circ> the_Address"

definition jmm_typeof_addr' :: "'m prog \<Rightarrow> addr \<rightharpoonup> htype"
where "jmm_typeof_addr' P = (\<lambda>hT. if is_htype P hT then Some hT else None) \<circ> fst \<circ> the_Address"

lemma jmm_typeof_addr'_conv_jmm_type_addr: "jmm_typeof_addr' P = jmm_typeof_addr P h"
by(simp add: jmm_typeof_addr_def jmm_typeof_addr'_def)

lemma jmm_typeof_addr'_conv_jmm_typeof_addr: "(\<lambda>_. jmm_typeof_addr' P) = jmm_typeof_addr P"
by(simp add: jmm_typeof_addr_def jmm_typeof_addr'_def fun_eq_iff)

lemma jmm_typeof_addr_conv_jmm_typeof_addr': "jmm_typeof_addr = (\<lambda>P _. jmm_typeof_addr' P)"
by(simp add: jmm_typeof_addr'_conv_jmm_typeof_addr)

definition jmm_heap_read :: "JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> bool"
where "jmm_heap_read h a ad v = True"

context
  notes [[inductive_internals]]
begin

inductive jmm_heap_write :: "JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm_heap_write h a ad v h"

end

definition jmm_hconf :: "JMM_heap \<Rightarrow> bool"
where "jmm_hconf h \<longleftrightarrow> True"

definition jmm_allocated :: "JMM_heap \<Rightarrow> addr set"
where "jmm_allocated h = {Address CTn n|CTn n. n \<in> h CTn}"

definition jmm_spurious_wakeups :: "bool"
where "jmm_spurious_wakeups = True"

lemmas jmm_heap_ops_defs =
  jmm_allocate_def jmm_typeof_addr_def 
  jmm_heap_read_def jmm_heap_write_def
  jmm_allocated_def jmm_spurious_wakeups_def

type_synonym thread_id = "addr"

abbreviation (input) addr2thread_id :: "addr \<Rightarrow> thread_id"
where "addr2thread_id \<equiv> \<lambda>x. x"

abbreviation (input) thread_id2addr :: "thread_id \<Rightarrow> addr"
where "thread_id2addr \<equiv> \<lambda>x. x"

interpretation jmm: heap_base
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write
  for P
.

abbreviation jmm_hext :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> JMM_heap \<Rightarrow> bool" ("_ \<turnstile> _ \<unlhd>jmm _" [51,51,51] 50)
where "jmm_hext \<equiv> jmm.hext TYPE('m)"

abbreviation jmm_conf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr val \<Rightarrow> ty \<Rightarrow> bool" 
  ("_,_ \<turnstile>jmm _ :\<le> _"  [51,51,51,51] 50)
where "jmm_conf P \<equiv> jmm.conf TYPE('m) P P"

abbreviation jmm_addr_loc_type :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool" 
  ("_,_ \<turnstile>jmm _@_ : _" [50, 50, 50, 50, 50] 51)
where "jmm_addr_loc_type P \<equiv> jmm.addr_loc_type TYPE('m) P P"

abbreviation jmm_confs :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr val list \<Rightarrow> ty list \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm _ [:\<le>] _"  [51,51,51,51] 50)
where "jmm_confs P \<equiv> jmm.confs TYPE('m) P P"

abbreviation jmm_tconf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> bool" ("_,_ \<turnstile>jmm _ \<surd>t" [51,51,51] 50)
where "jmm_tconf P \<equiv> jmm.tconf TYPE('m) P P"

interpretation jmm: allocated_heap_base
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write
  jmm_allocated
  for P
.

text \<open>Now a variation of the JMM with a different read operation that permits to read only type-conformant values\<close>

abbreviation jmm_heap_read_typed :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> bool"
where "jmm_heap_read_typed P \<equiv> jmm.heap_read_typed TYPE('m) P P"

interpretation jmm': heap_base
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write
  for P .

abbreviation jmm'_hext :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> JMM_heap \<Rightarrow> bool" ("_ \<turnstile> _ \<unlhd>jmm' _" [51,51,51] 50)
where "jmm'_hext \<equiv> jmm'.hext TYPE('m)"

abbreviation jmm'_conf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr val \<Rightarrow> ty \<Rightarrow> bool" 
  ("_,_ \<turnstile>jmm' _ :\<le> _"  [51,51,51,51] 50)
where "jmm'_conf P \<equiv> jmm'.conf TYPE('m) P P"

abbreviation jmm'_addr_loc_type :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool" 
  ("_,_ \<turnstile>jmm' _@_ : _" [50, 50, 50, 50, 50] 51)
where "jmm'_addr_loc_type P \<equiv> jmm'.addr_loc_type TYPE('m) P P"

abbreviation jmm'_confs :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr val list \<Rightarrow> ty list \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' _ [:\<le>] _"  [51,51,51,51] 50)
where "jmm'_confs P \<equiv> jmm'.confs TYPE('m) P P"

abbreviation jmm'_tconf :: "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> bool" ("_,_ \<turnstile>jmm' _ \<surd>t" [51,51,51] 50)
where "jmm'_tconf P \<equiv> jmm'.tconf TYPE('m) P P"

subsection \<open>Heap locale interpretations\<close>

subsection \<open>Locale \<open>heap\<close>\<close>

lemma jmm_heap: "heap addr2thread_id thread_id2addr jmm_allocate (jmm_typeof_addr P) jmm_heap_write P"
proof
  fix h' a h hT
  assume "(h', a) \<in> jmm_allocate h hT" "is_htype P hT"
  thus "jmm_typeof_addr P h' a = \<lfloor>hT\<rfloor>"
    by(auto simp add: jmm_heap_ops_defs)
next
  fix h hT h' a
  assume "(h', a) \<in> jmm_allocate h hT"
  thus "P \<turnstile> h \<unlhd>jmm h'" by(auto simp add: jmm_heap_ops_defs intro: jmm.hextI)
next
  fix h a al v h'
  assume "jmm_heap_write h a al v h'"
  thus "P \<turnstile> h \<unlhd>jmm h'" by cases auto
qed simp

interpretation jmm: heap
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write
  P
  for P
by(rule jmm_heap)

declare jmm.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

lemmas jmm'_heap = jmm_heap

interpretation jmm': heap
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write
  P
  for P
by(rule jmm'_heap)

declare jmm'.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

lemma jmm_heap_read_typed_default_val:
  "heap_base.heap_read_typed typeof_addr jmm_heap_read P h a al
   (default_val (THE T. heap_base.addr_loc_type typeof_addr P h a al T))"
by(rule heap_base.heap_read_typedI)(simp_all add: heap_base.THE_addr_loc_type jmm_heap_read_def heap_base.defval_conf)

lemma jmm_allocate_Eps:
  "(SOME ha. ha \<in> jmm_allocate h hT) = (h', a')
  \<Longrightarrow> jmm_allocate h hT \<noteq> {} \<longrightarrow> (h', a') \<in> jmm_allocate h hT"
by(auto dest: jmm.allocate_Eps)

lemma jmm_allocate_eq_empty: "jmm_allocate h hT = {} \<longleftrightarrow> h hT = UNIV"
by(auto simp add: jmm_allocate_def)

lemma jmm_allocate_otherD:
  "(h', a) \<in> jmm_allocate h hT \<Longrightarrow> \<forall>hT'. hT' \<noteq> hT \<longrightarrow> h' hT' = h hT'"
by(auto simp add: jmm_allocate_def)

lemma jmm_start_heap_ok: "jmm.start_heap_ok"
apply(simp add: jmm.start_heap_ok_def jmm.start_heap_data_def initialization_list_def sys_xcpts_list_def jmm.create_initial_object_simps)
apply(split prod.split, clarify, clarsimp simp add: jmm.create_initial_object_simps jmm_allocate_eq_empty Thread_neq_sys_xcpts sys_xcpts_neqs dest!: jmm_allocate_Eps jmm_allocate_otherD)+
done

subsection \<open>Locale \<open>heap_conf\<close>\<close>

interpretation jmm: heap_conf_base
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write jmm_hconf
  P
  for P .

abbreviation (input) jmm'_hconf :: "JMM_heap \<Rightarrow> bool"
where "jmm'_hconf == jmm_hconf"

interpretation jmm': heap_conf_base
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write jmm'_hconf
  P
  for P .

abbreviation jmm_heap_read_typeable :: "'m prog \<Rightarrow> bool"
where "jmm_heap_read_typeable P \<equiv> jmm.heap_read_typeable TYPE('m) P jmm_hconf P"

abbreviation jmm'_heap_read_typeable :: "'m prog \<Rightarrow> bool"
where "jmm'_heap_read_typeable P \<equiv> jmm'.heap_read_typeable TYPE('m) P jmm_hconf P"

lemma jmm_heap_read_typeable: "jmm_heap_read_typeable P"
by(rule jmm.heap_read_typeableI)(simp add: jmm_heap_read_def)

lemma jmm'_heap_read_typeable: "jmm'_heap_read_typeable P"
by(rule jmm'.heap_read_typeableI)(auto simp add: jmm_heap_read_def jmm.heap_read_typed_def dest: jmm'.addr_loc_type_fun)

lemma jmm_heap_conf:
  "heap_conf addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_write jmm_hconf P"
by(unfold_locales)(simp_all add: jmm_hconf_def jmm_heap_ops_defs split: if_split_asm)

interpretation jmm: heap_conf
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write jmm_hconf
  P
  for P
by(rule jmm_heap_conf)

lemmas jmm'_heap_conf = jmm_heap_conf

interpretation jmm': heap_conf
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write jmm'_hconf
  P
  for P
by(rule jmm'_heap_conf)

subsection \<open>Locale \<open>heap_progress\<close>\<close>

lemma jmm_heap_progress:
  "heap_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_read jmm_heap_write jmm_hconf P"
proof
  fix h a al T
  assume "jmm_hconf h"
    and al: "P,h \<turnstile>jmm a@al : T"
  show "\<exists>v. jmm_heap_read h a al v \<and> P,h \<turnstile>jmm v :\<le> T"
    using jmm.defval_conf[of P P h T] unfolding jmm_heap_ops_defs by blast
next
  fix h a al T v
  assume "P,h \<turnstile>jmm a@al : T"
  show "\<exists>h'. jmm_heap_write h a al v h'"
    by(auto intro: jmm_heap_write.intros)
qed

interpretation jmm: heap_progress
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write jmm_hconf
  P
  for P
by(rule jmm_heap_progress)

lemma jmm'_heap_progress:
  "heap_progress addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm'_hconf P"
proof
  fix h a al T
  assume "jmm'_hconf h"
    and al: "P,h \<turnstile>jmm' a@al : T"
  thus "\<exists>v. jmm_heap_read_typed P h a al v \<and> P,h \<turnstile>jmm' v :\<le> T"
    unfolding jmm_heap_read_def jmm.heap_read_typed_def
    by(blast dest: jmm'.addr_loc_type_fun intro: jmm'.defval_conf)+
next
  fix h a al T v
  assume "P,h \<turnstile>jmm' a@al : T"
    and "P,h \<turnstile>jmm' v :\<le> T"
  thus "\<exists>h'. jmm_heap_write h a al v h'"
    by(auto intro: jmm_heap_write.intros)
qed

interpretation jmm': heap_progress
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write jmm'_hconf
  P
  for P
by(rule jmm'_heap_progress)

subsection \<open>Locale \<open>heap_conf_read\<close>\<close>

lemma jmm'_heap_conf_read:
  "heap_conf_read addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) (jmm_heap_read_typed P) jmm_heap_write jmm'_hconf P"
by(rule jmm.heap_conf_read_heap_read_typed)

interpretation jmm': heap_conf_read
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write jmm'_hconf
  P
  for P
by(rule jmm'_heap_conf_read)

interpretation jmm': heap_typesafe
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write jmm'_hconf
  P
  for P
..

subsection \<open>Locale \<open>allocated_heap\<close>\<close>

lemma jmm_allocated_heap:
  "allocated_heap addr2thread_id thread_id2addr jmm_empty jmm_allocate (jmm_typeof_addr P) jmm_heap_write jmm_allocated P"
proof
  show "jmm_allocated jmm_empty = {}" by(simp add: jmm_allocated_def)
next
  fix h' a h hT
  assume "(h', a) \<in> jmm_allocate h hT"
  thus "jmm_allocated h' = insert a (jmm_allocated h) \<and> a \<notin> jmm_allocated h"
    by(auto simp add: jmm_heap_ops_defs split: if_split_asm)
next
  fix h a al v h'
  assume "jmm_heap_write h a al v h'"
  thus "jmm_allocated h' = jmm_allocated h" by cases simp
qed

interpretation jmm: allocated_heap
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" jmm_heap_read jmm_heap_write
  jmm_allocated
  P
  for P
by(rule jmm_allocated_heap)

lemmas jmm'_allocated_heap = jmm_allocated_heap

interpretation jmm': allocated_heap
  addr2thread_id thread_id2addr
  jmm_spurious_wakeups
  jmm_empty jmm_allocate "jmm_typeof_addr P" "jmm_heap_read_typed P" jmm_heap_write
  jmm_allocated
  P
  for P
by(rule jmm'_allocated_heap)

subsection \<open>Syntax translations\<close>

notation jmm'.external_WT' ("_,_ \<turnstile>jmm' (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)

abbreviation jmm'_red_external :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> addr val list
  \<Rightarrow> (addr, thread_id, JMM_heap) external_thread_action 
  \<Rightarrow> addr extCallRet \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_red_external P \<equiv> jmm'.red_external (TYPE('m)) P P"

abbreviation jmm'_red_external_syntax :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> JMM_heap
  \<Rightarrow> (addr, thread_id, JMM_heap) external_thread_action 
  \<Rightarrow> addr extCallRet \<Rightarrow> JMM_heap \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
where
  "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> jmm'_red_external P t h a M vs ta va h'"

abbreviation jmm'_red_external_aggr :: 
  "'m prog \<Rightarrow> thread_id \<Rightarrow> addr \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> JMM_heap 
    \<Rightarrow> ((addr, thread_id, JMM_heap) external_thread_action \<times> addr extCallRet \<times> JMM_heap) set"
where "jmm'_red_external_aggr P \<equiv> jmm'.red_external_aggr TYPE('m) P P"

abbreviation jmm'_heap_copy_loc :: 
  "'m prog \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> JMM_heap
  \<Rightarrow> (addr, thread_id) obs_event list \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copy_loc \<equiv> jmm'.heap_copy_loc TYPE('m)"

abbreviation jmm'_heap_copies :: 
  "'m prog \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> addr_loc list \<Rightarrow> JMM_heap
  \<Rightarrow> (addr, thread_id) obs_event list \<Rightarrow> JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copies \<equiv> jmm'.heap_copies TYPE('m)"

abbreviation jmm'_heap_clone ::
  "'m prog \<Rightarrow> JMM_heap \<Rightarrow> addr \<Rightarrow> JMM_heap
  \<Rightarrow> ((addr, thread_id) obs_event list \<times> addr) option \<Rightarrow> bool"
where "jmm'_heap_clone P \<equiv> jmm'.heap_clone TYPE('m) P P"

end
