(*  Title:      JinjaThreads/MM/SC.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theories Common/Objects.thy and Common/Conform by David von Oheimb
*)

section \<open>Sequential consistency\<close>

theory SC
imports 
  "../Common/Conform"
  MM
begin

subsection\<open>Objects and Arrays\<close>

type_synonym 
  fields = "vname \<times> cname \<rightharpoonup> addr val"       \<comment> \<open>field name, defining class, value\<close>

type_synonym
  cells = "addr val list"

datatype heapobj
  = Obj cname fields
    \<comment> \<open>class instance with class name and fields\<close>

  | Arr ty fields cells
    \<comment> \<open>element type, fields (from object), and list of each cell's content\<close>

lemma rec_heapobj [simp]: "rec_heapobj = case_heapobj"
by(auto intro!: ext split: heapobj.split)

primrec obj_ty  :: "heapobj \<Rightarrow> htype"
where
  "obj_ty (Obj C f)     = Class_type C"
| "obj_ty (Arr T fs cs) = Array_type T (length cs)"

fun is_Arr :: "heapobj \<Rightarrow> bool" where
  "is_Arr (Obj C fs)   = False"
| "is_Arr (Arr T f el) = True"

lemma is_Arr_conv:
  "is_Arr arrobj = (\<exists>T f el. arrobj = Arr T f el)"
by(cases arrobj, auto)

lemma is_ArrE:
  "\<lbrakk> is_Arr arrobj; \<And>T f el. arrobj = Arr T f el \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  "\<lbrakk> \<not> is_Arr arrobj; \<And>C fs. arrobj = Obj C fs \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(cases arrobj, auto)+

definition init_fields :: "('field_name \<times> (ty \<times> fmod)) list \<Rightarrow> 'field_name \<rightharpoonup> addr val"
where "init_fields \<equiv> map_of \<circ> map (\<lambda>(FD,(T, fm)). (FD,default_val T))"

primrec
  \<comment> \<open>a new, blank object with default values in all fields:\<close>
  blank :: "'m prog \<Rightarrow> htype \<Rightarrow> heapobj"
where
  "blank P (Class_type C)   = Obj C (init_fields (fields P C))"
| "blank P (Array_type T n) = Arr T (init_fields (fields P Object)) (replicate n (default_val T))"

lemma obj_ty_blank [iff]: 
  "obj_ty (blank P hT) = hT"
by(cases hT)(simp_all)


subsection\<open>Heap\<close>

type_synonym heap = "addr \<rightharpoonup> heapobj"

translations
  (type) "heap" <= (type) "nat \<Rightarrow> heapobj option"

abbreviation sc_empty :: heap
where "sc_empty \<equiv> Map.empty"

fun the_obj :: "heapobj \<Rightarrow> cname \<times> fields" where
  "the_obj (Obj C fs) = (C, fs)"

fun the_arr :: "heapobj \<Rightarrow> ty \<times> fields \<times> cells" where
  "the_arr (Arr T f el) = (T, f, el)"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the_obj (the (hp a)))"

definition sc_allocate :: "'m prog \<Rightarrow> heap \<Rightarrow> htype \<Rightarrow> (heap \<times> addr) set"
where
  "sc_allocate P h hT = 
   (case new_Addr h of None \<Rightarrow> {}
                   | Some a \<Rightarrow> {(h(a \<mapsto> blank P hT), a)})"

definition sc_typeof_addr :: "heap \<Rightarrow> addr \<Rightarrow> htype option"
where "sc_typeof_addr h a = map_option obj_ty (h a)"

inductive sc_heap_read :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; fs (F, D) = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField D F) v"
| Arr: "\<lbrakk> h a = \<lfloor>Arr T f el\<rfloor>; n < length el \<rbrakk> \<Longrightarrow> sc_heap_read h a (ACell n) (el ! n)"
| ArrObj: "\<lbrakk> h a = \<lfloor>Arr T f el\<rfloor>; f (F, Object) = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField Object F) v"

hide_fact (open) Obj Arr ArrObj

inductive_cases sc_heap_read_cases [elim!]:
  "sc_heap_read h a (CField C F) v"
  "sc_heap_read h a (ACell n) v"

inductive sc_heap_write :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> heap \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> h a = \<lfloor>Obj C fs\<rfloor>; h' = h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v))) \<rbrakk> \<Longrightarrow> sc_heap_write h a (CField D F) v h'"
| Arr: "\<lbrakk> h a = \<lfloor>Arr T f el\<rfloor>; h' = h(a \<mapsto> Arr T f (el[n := v])) \<rbrakk> \<Longrightarrow> sc_heap_write h a (ACell n) v h'"
| ArrObj: "\<lbrakk> h a = \<lfloor>Arr T f el\<rfloor>; h' = h(a \<mapsto> Arr T (f((F, Object) \<mapsto> v)) el) \<rbrakk> \<Longrightarrow> sc_heap_write h a (CField Object F) v h'"

hide_fact (open) Obj Arr ArrObj

inductive_cases sc_heap_write_cases [elim!]:
  "sc_heap_write h a (CField C F) v h'"
  "sc_heap_write h a (ACell n) v h'"

consts sc_spurious_wakeups :: bool

interpretation sc: 
  heap_base
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read"
    "sc_heap_write"
  for P .

text \<open>Translate notation from \<open>heap_base\<close>\<close>

(* FIXME! Why does sc.preallocated need the type token?? *)
abbreviation sc_preallocated :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"
where "sc_preallocated == sc.preallocated TYPE('m)"

abbreviation sc_start_tid :: "'md prog \<Rightarrow> thread_id"
where "sc_start_tid \<equiv> sc.start_tid TYPE('md)"

abbreviation sc_start_heap_ok :: "'m prog \<Rightarrow> bool"
where "sc_start_heap_ok \<equiv> sc.start_heap_ok TYPE('m)"

abbreviation sc_start_heap :: "'m prog \<Rightarrow> heap"
where "sc_start_heap \<equiv> sc.start_heap TYPE('m)"

abbreviation sc_start_state :: 
  "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> addr val list \<Rightarrow> 'x)
  \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> (addr, thread_id, 'x, heap, addr) state"
where
  "sc_start_state f P \<equiv> sc.start_state TYPE('m) P f P"

abbreviation sc_wf_start_state :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr val list \<Rightarrow> bool"
where "sc_wf_start_state P \<equiv> sc.wf_start_state TYPE('m) P P"

notation sc.conf ("_,_ \<turnstile>sc _ :\<le> _"  [51,51,51,51] 50)
notation sc.confs ("_,_ \<turnstile>sc _ [:\<le>] _" [51,51,51,51] 50)
notation sc.hext ("_ \<unlhd>sc _" [51,51] 50)

lemma sc_start_heap_ok: "sc_start_heap_ok P"
apply(simp add: sc.start_heap_ok_def sc.start_heap_data_def initialization_list_def sc.create_initial_object_simps sc_allocate_def sys_xcpts_list_def case_option_conv_if new_Addr_SomeI del: blank.simps split del: option.split if_split)
done

lemma sc_wf_start_state_iff:
  "sc_wf_start_state P C M vs \<longleftrightarrow> (\<exists>Ts T meth D. P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D \<and> P,sc_start_heap P \<turnstile>sc vs [:\<le>] Ts)"
by(simp add: sc.wf_start_state.simps sc_start_heap_ok)

lemma sc_heap:
  "heap addr2thread_id thread_id2addr (sc_allocate P) sc_typeof_addr sc_heap_write P"
proof
  fix h' a h hT
  assume "(h', a) \<in> sc_allocate P h hT"
  thus "sc_typeof_addr h' a = \<lfloor>hT\<rfloor>"
    by(auto simp add: sc_allocate_def sc_typeof_addr_def dest: new_Addr_SomeD split: if_split_asm)
next
  fix h' h hT a
  assume "(h', a) \<in> sc_allocate P h hT"
  from this[symmetric] show "h \<unlhd>sc h'"
    by(fastforce simp add: sc_allocate_def sc_typeof_addr_def sc.hext_def dest: new_Addr_SomeD intro!: map_leI)
next
  fix h a al v h'
  assume "sc_heap_write h a al v h'"
  thus "h \<unlhd>sc h'"
    by(cases al)(auto intro!: sc.hextI simp add: sc_typeof_addr_def)
qed simp

interpretation sc: 
  heap 
    "addr2thread_id"
    "thread_id2addr"
    "sc_spurious_wakeups"
    "sc_empty"
    "sc_allocate P"
    "sc_typeof_addr"
    "sc_heap_read"
    "sc_heap_write"
  for P by(rule sc_heap)

lemma sc_hext_new:
  "h a = None \<Longrightarrow> h \<unlhd>sc h(a \<mapsto> arrobj)"
by(rule sc.hextI)(auto simp add: sc_typeof_addr_def dest!: new_Addr_SomeD)

lemma sc_hext_upd_obj: "h a = Some (Obj C fs) \<Longrightarrow> h \<unlhd>sc h(a\<mapsto>(Obj C fs'))"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def)

lemma sc_hext_upd_arr: "\<lbrakk> h a = Some (Arr T f e); length e = length e' \<rbrakk> \<Longrightarrow> h \<unlhd>sc h(a\<mapsto>(Arr T f' e'))"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def)

subsection \<open>Conformance\<close>

definition sc_fconf :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> fields \<Rightarrow> bool" ("_,_,_ \<turnstile>sc _ \<surd>" [51,51,51,51] 50)
where "P,C,h \<turnstile>sc fs \<surd> = (\<forall>F D T fm. P \<turnstile> C has F:T (fm) in D \<longrightarrow> (\<exists>v. fs(F,D) = Some v \<and> P,h \<turnstile>sc v :\<le> T))"

primrec sc_oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> heapobj \<Rightarrow> bool"   ("_,_ \<turnstile>sc _ \<surd>" [51,51,51] 50)
where
  "P,h \<turnstile>sc Obj C fs \<surd> \<longleftrightarrow> is_class P C \<and> P,C,h \<turnstile>sc fs \<surd>"
| "P,h \<turnstile>sc Arr T fs el \<surd> \<longleftrightarrow> is_type P (T\<lfloor>\<rceil>) \<and> P,Object,h \<turnstile>sc fs \<surd> \<and> (\<forall>v \<in> set el. P,h \<turnstile>sc v :\<le> T)"

definition sc_hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile>sc _ \<surd>" [51,51] 50)
where "P \<turnstile>sc h \<surd> \<longleftrightarrow> (\<forall>a obj. h a = Some obj \<longrightarrow> P,h \<turnstile>sc obj \<surd>)"

interpretation sc: heap_conf_base  
  "addr2thread_id"
  "thread_id2addr"
  "sc_spurious_wakeups"
  "sc_empty"
  "sc_allocate P"
  "sc_typeof_addr"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P .

declare sc.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

lemma sc_conf_upd_obj: "h a = Some(Obj C fs) \<Longrightarrow> (P,h(a\<mapsto>(Obj C fs')) \<turnstile>sc x :\<le> T) = (P,h \<turnstile>sc x :\<le> T)"
apply (unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply (auto simp add: sc_typeof_addr_def split: if_split_asm)
done

lemma sc_conf_upd_arr: "h a = Some(Arr T f el) \<Longrightarrow> (P,h(a\<mapsto>(Arr T f' el')) \<turnstile>sc x :\<le> T') = (P,h \<turnstile>sc x :\<le> T')"
apply(unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply(auto simp add: sc_typeof_addr_def split: if_split_asm)
done

lemma sc_oconf_hext: "P,h \<turnstile>sc obj \<surd> \<Longrightarrow> h \<unlhd>sc h' \<Longrightarrow> P,h' \<turnstile>sc obj \<surd>"
by(cases obj)(fastforce elim: sc.conf_hext simp add: sc_fconf_def)+

lemma sc_oconf_init_fields:
  assumes "P \<turnstile> C has_fields FDTs"
  shows "P,h \<turnstile>sc (Obj C (init_fields FDTs)) \<surd>"
using assms has_fields_is_class[OF assms]
by(auto simp add: has_field_def init_fields_def sc_fconf_def split_def o_def map_of_map[simplified split_def, where f="\<lambda>p. default_val (fst p)"] dest: has_fields_fun)

lemma sc_oconf_init:
 "is_htype P hT \<Longrightarrow> P,h \<turnstile>sc blank P hT \<surd>"
by(cases hT)(auto simp add: sc_fconf_def has_field_def init_fields_def split_def o_def map_of_map[simplified split_def, where f="\<lambda>p. default_val (fst p)"] dest: has_fields_fun)

lemma sc_oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T (fm) in D; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Obj C fs) \<surd> \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile>sc (Obj C (fs((F,D)\<mapsto>v))) \<surd>"
unfolding has_field_def
by(auto simp add: sc_fconf_def has_field_def dest: has_fields_fun)

lemma sc_oconf_fupd_arr [intro?]:
  "\<lbrakk> P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T f el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T f (el[i := v])) \<surd>"
by(auto dest: subsetD[OF set_update_subset_insert])

lemma sc_oconf_fupd_arr_fields:
  "\<lbrakk> P \<turnstile> Object has F:T (fm) in Object; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T' f el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T' (f((F, Object) \<mapsto> v)) el) \<surd>"
by(auto dest: has_fields_fun simp add: sc_fconf_def has_field_def)

lemma sc_oconf_new: "\<lbrakk> P,h \<turnstile>sc obj \<surd>; h a = None \<rbrakk> \<Longrightarrow> P,h(a \<mapsto> arrobj) \<turnstile>sc obj \<surd>"
by(erule sc_oconf_hext)(rule sc_hext_new)

lemmas sc_oconf_upd_obj = sc_oconf_hext [OF _ sc_hext_upd_obj]

lemma sc_oconf_upd_arr:
  assumes "P,h \<turnstile>sc obj \<surd>"
  and ha: "h a = \<lfloor>Arr T f el\<rfloor>"
  shows "P,h(a \<mapsto> Arr T f' el') \<turnstile>sc obj \<surd>"
using assms
by(cases obj)(auto simp add: sc_conf_upd_arr[where h=h, OF ha] sc_fconf_def)

lemma sc_hconfD: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile>sc obj \<surd>"
unfolding sc_hconf_def by blast

lemmas sc_preallocated_new = sc.preallocated_hext[OF _ sc_hext_new]
lemmas sc_preallocated_upd_obj = sc.preallocated_hext [OF _ sc_hext_upd_obj]
lemmas sc_preallocated_upd_arr = sc.preallocated_hext [OF _ sc_hext_upd_arr]

lemma sc_hconf_new: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = None; P,h \<turnstile>sc obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>obj) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_new)

lemma sc_hconf_upd_obj: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some (Obj C fs); P,h \<turnstile>sc (Obj C fs') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>(Obj C fs')) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_obj simp del: sc_oconf.simps)

lemma sc_hconf_upd_arr: "\<lbrakk> P \<turnstile>sc h \<surd>; h a = Some(Arr T f el); P,h \<turnstile>sc (Arr T f' el') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc h(a\<mapsto>(Arr T f' el')) \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_arr simp del: sc_oconf.simps)

lemma sc_heap_conf: 
  "heap_conf addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_write (sc_hconf P) P"
proof
  show "P \<turnstile>sc sc_empty \<surd>" by(simp add: sc_hconf_def)
next
  fix h a hT
  assume "sc_typeof_addr h a = \<lfloor>hT\<rfloor>" "P \<turnstile>sc h \<surd>"
  thus "is_htype P hT"
    by(auto simp add: sc_typeof_addr_def sc_oconf_def dest!: sc_hconfD split: heapobj.split_asm)
next
  fix h h' hT a
  assume "P \<turnstile>sc h \<surd>" "(h', a) \<in> sc_allocate P h hT" "is_htype P hT"
  thus "P \<turnstile>sc h' \<surd>"
    by(auto simp add: sc_allocate_def dest!: new_Addr_SomeD intro: sc_hconf_new sc_oconf_init split: if_split_asm)
next
  fix h a al T v h'
  assume "P \<turnstile>sc h \<surd>"
    and "sc.addr_loc_type P h a al T"
    and "P,h \<turnstile>sc v :\<le> T"
    and "sc_heap_write h a al v h'"
  thus "P \<turnstile>sc h' \<surd>"
    by(cases al)(fastforce elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def intro: sc_hconf_upd_obj sc_oconf_fupd sc_hconfD sc_hconf_upd_arr sc_oconf_fupd_arr sc_oconf_fupd_arr_fields)+
qed

interpretation sc: heap_conf
  "addr2thread_id"
  "thread_id2addr"
  "sc_spurious_wakeups"
  "sc_empty"
  "sc_allocate P"
  "sc_typeof_addr"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P 
by(rule sc_heap_conf)

lemma sc_heap_progress:
  "heap_progress addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al T
  assume hconf: "P \<turnstile>sc h \<surd>"
    and alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  from alt show "\<exists>v. sc_heap_read h a al v \<and> P,h \<turnstile>sc v :\<le> T"
  proof(cases)
    case (addr_loc_type_field U F fm D) 
    note [simp] = \<open>al = CField D F\<close>
    show ?thesis
    proof(cases "arrobj")
      case (Obj C' fs)
      with \<open>sc_typeof_addr h a = \<lfloor>U\<rfloor>\<close> arrobj
      have [simp]: "C' = class_type_of U" by(auto simp add: sc_typeof_addr_def)
      from hconf arrobj Obj have "P,h \<turnstile>sc Obj (class_type_of U) fs \<surd>" by(auto dest: sc_hconfD)
      with \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close> obtain v 
        where "fs (F, D) = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T" by(fastforce simp add: sc_fconf_def)
      thus ?thesis using Obj arrobj by(auto intro: sc_heap_read.intros)
    next
      case (Arr T' f el)
      with \<open>sc_typeof_addr h a = \<lfloor>U\<rfloor>\<close> arrobj
      have [simp]: "U = Array_type T' (length el)" by(auto simp add: sc_typeof_addr_def)
      from hconf arrobj Arr have "P,h \<turnstile>sc Arr T' f el \<surd>" by(auto dest: sc_hconfD)
      from \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close> have [simp]: "D = Object"
        by(auto dest: has_field_decl_above)
      with \<open>P,h \<turnstile>sc Arr T' f el \<surd>\<close> \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close>
      obtain v where "f (F, Object) = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
        by(fastforce simp add: sc_fconf_def)
      thus ?thesis using Arr arrobj by(auto intro: sc_heap_read.intros)
    qed
  next
    case (addr_loc_type_cell n' n)
    with arrobj obtain f el
      where [simp]: "arrobj = Arr T f el"
      by(cases arrobj)(auto simp add: sc_typeof_addr_def)
    from addr_loc_type_cell arrobj
    have [simp]: "al = ACell n" "n < length el" by(auto simp add: sc_typeof_addr_def)
    from hconf arrobj have "P,h \<turnstile>sc Arr T f el \<surd>" by(auto dest: sc_hconfD)
    hence "P,h \<turnstile>sc el ! n :\<le> T" by(fastforce)
    thus ?thesis using arrobj by(fastforce intro: sc_heap_read.intros)
  qed
next
  fix h a al T v
  assume alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  thus "\<exists>h'. sc_heap_write h a al v h'" using alt
    by(cases arrobj)(fastforce intro: sc_heap_write.intros elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def dest: has_field_decl_above)+
qed

interpretation sc: heap_progress
  "addr2thread_id"
  "thread_id2addr"
  "sc_spurious_wakeups"
  "sc_empty"
  "sc_allocate P"
  "sc_typeof_addr"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
by(rule sc_heap_progress)

lemma sc_heap_conf_read:
  "heap_conf_read addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_read sc_heap_write (sc_hconf P) P"
proof
  fix h a al v T
  assume read: "sc_heap_read h a al v"
    and alt: "sc.addr_loc_type P h a al T"
    and hconf: "P \<turnstile>sc h \<surd>"
  thus "P,h \<turnstile>sc v :\<le> T"
    by(auto elim!: sc_heap_read.cases sc.addr_loc_type.cases simp add: sc_typeof_addr_def)(fastforce dest!: sc_hconfD simp add: sc_fconf_def)+
qed

interpretation sc: heap_conf_read
  "addr2thread_id"
  "thread_id2addr"
  "sc_spurious_wakeups"
  "sc_empty"
  "sc_allocate P"
  "sc_typeof_addr"
  "sc_heap_read"
  "sc_heap_write"
  "sc_hconf P"
  "P"
for P
by(rule sc_heap_conf_read)

abbreviation sc_deterministic_heap_ops :: "'m prog \<Rightarrow> bool"
where "sc_deterministic_heap_ops \<equiv> sc.deterministic_heap_ops TYPE('m)"

lemma sc_deterministic_heap_ops: "\<not> sc_spurious_wakeups \<Longrightarrow> sc_deterministic_heap_ops P"
by(rule sc.deterministic_heap_opsI)(auto elim: sc_heap_read.cases sc_heap_write.cases simp add: sc_allocate_def)

subsection \<open>Code generation\<close>

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  sc_heap_read .

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  sc_heap_write .

lemma eval_sc_heap_read_i_i_i_o:
  "Predicate.eval (sc_heap_read_i_i_i_o h ad al) = sc_heap_read h ad al"
by(auto elim: sc_heap_read_i_i_i_oE intro: sc_heap_read_i_i_i_oI intro!: ext)

lemma eval_sc_heap_write_i_i_i_i_o:
  "Predicate.eval (sc_heap_write_i_i_i_i_o h ad al v) = sc_heap_write h ad al v"
by(auto elim: sc_heap_write_i_i_i_i_oE intro: sc_heap_write_i_i_i_i_oI intro!: ext)

end
