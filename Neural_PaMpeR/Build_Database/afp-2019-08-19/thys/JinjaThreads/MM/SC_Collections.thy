(*  Title:      JinjaThreads/MM/SC_Collections.thy
    Author:     Andreas Lochbihler
*)

section \<open>Sequential consistency with efficient data structures\<close>

theory SC_Collections
imports
  "../Common/Conform"
  (*"../../Collections/impl/RBTMapImpl"
  "../../Collections/impl/TrieMapImpl"
  "../../Collections/impl/ListMapImpl"*)
  "../Basic/JT_ICF"
  MM
begin

hide_const (open) new_Addr
hide_fact (open) new_Addr_SomeD new_Addr_SomeI

subsection\<open>Objects and Arrays\<close>

type_synonym fields = "(char, (cname, addr val) lm) tm"
type_synonym array_cells = "(nat, addr val) rbt"
type_synonym array_fields = "(vname, addr val) lm"

datatype heapobj
  = Obj cname fields                    \<comment> \<open>class instance with class name and fields\<close>
  | Arr ty nat array_fields array_cells                 \<comment> \<open>element type, size, fields and cell contents\<close>

lemma rec_heapobj [simp]: "rec_heapobj = case_heapobj"
by(auto intro!: ext split: heapobj.split)

primrec obj_ty  :: "heapobj \<Rightarrow> htype"
where
  "obj_ty (Obj c f)   = Class_type c"
| "obj_ty (Arr t si f e) = Array_type t si"

fun is_Arr :: "heapobj \<Rightarrow> bool" where
  "is_Arr (Obj C fs)      = False"
| "is_Arr (Arr T f si el) = True"

lemma is_Arr_conv:
  "is_Arr arrobj = (\<exists>T si f el. arrobj = Arr T si f el)"
by(cases arrobj, auto)

lemma is_ArrE:
  "\<lbrakk> is_Arr arrobj; \<And>T si f el. arrobj = Arr T si f el \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
  "\<lbrakk> \<not> is_Arr arrobj; \<And>C fs. arrobj = Obj C fs \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(cases arrobj, auto)+

definition init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
where
  "init_fields FDTs \<equiv>
  foldr (\<lambda>((F, D), T) fields. 
           let F' = String.explode F
           in tm_update F' (lm_update D (default_val T)
                                      (case tm_lookup F' fields of None \<Rightarrow> lm_empty () | Some lm \<Rightarrow> lm)) fields)
        FDTs (tm_empty ())"

definition init_fields_array :: "(vname \<times> ty) list \<Rightarrow> array_fields"
where
  "init_fields_array \<equiv> lm.to_map \<circ> map (\<lambda>(F, T). (F, default_val T))"

definition init_cells :: "ty \<Rightarrow> nat \<Rightarrow> array_cells"
where "init_cells T n = foldl (\<lambda>cells i. rm_update i (default_val T) cells) (rm_empty ()) [0..<n]"

primrec \<comment> \<open>a new, blank object with default values in all fields:\<close>
  blank :: "'m prog \<Rightarrow> htype \<Rightarrow> heapobj"
where
  "blank P (Class_type C) = Obj C (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) (TypeRel.fields P C)))"
| "blank P (Array_type T n) =
   Arr T n (init_fields_array (map (\<lambda>((F, D), (T, fm)). (F, T)) (TypeRel.fields P Object))) (init_cells T n)"

lemma obj_ty_blank [iff]: "obj_ty (blank P hT) = hT"
by(cases hT) simp_all

subsection\<open>Heap\<close>

type_synonym heap = "(addr, heapobj) rbt"

translations
  (type) "heap" <= (type) "(nat, heapobj) rbt"

abbreviation sc_empty :: heap
where "sc_empty \<equiv> rm_empty ()"

fun the_obj :: "heapobj \<Rightarrow> cname \<times> fields" where
  "the_obj (Obj C fs) = (C, fs)"

fun the_arr :: "heapobj \<Rightarrow> ty \<times> nat \<times> array_fields \<times> array_cells" where
  "the_arr (Arr T si f el) = (T, si, f, el)"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the_obj (the (rm_lookup a hp)))"

definition new_Addr :: "heap \<Rightarrow> addr option"
where "new_Addr h = Some (case rm_max h (\<lambda>_. True) of None \<Rightarrow> 0 | Some (a, _) \<Rightarrow> a + 1)"

definition sc_allocate :: "'m prog \<Rightarrow> heap \<Rightarrow> htype \<Rightarrow> (heap \<times> addr) set"
where
  "sc_allocate P h hT = 
   (case new_Addr h of None \<Rightarrow> {}
                   | Some a \<Rightarrow> {(rm_update a (blank P hT) h, a)})"

definition sc_typeof_addr :: "heap \<Rightarrow> addr \<Rightarrow> htype option"
where "sc_typeof_addr h a = map_option obj_ty (rm_lookup a h)"

inductive sc_heap_read :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj: "\<lbrakk> rm_lookup a h = \<lfloor>Obj C fs\<rfloor>; tm_lookup (String.explode F) fs = \<lfloor>fs'\<rfloor>; lm_lookup D fs' = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField D F) v"
| Arr: "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si f el\<rfloor>; n < si \<rbrakk> \<Longrightarrow> sc_heap_read h a (ACell n) (the (rm_lookup n el))"
| ArrObj: "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si f el\<rfloor>; lm_lookup F f = \<lfloor>v\<rfloor> \<rbrakk> \<Longrightarrow> sc_heap_read h a (CField Object F) v"

hide_fact (open) Obj Arr ArrObj

inductive_cases sc_heap_read_cases [elim!]:
  "sc_heap_read h a (CField C F) v"
  "sc_heap_read h a (ACell n) v"

inductive sc_heap_write :: "heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> addr val \<Rightarrow> heap \<Rightarrow> bool"
for h :: heap and a :: addr
where
  Obj:
  "\<lbrakk> rm_lookup a h = \<lfloor>Obj C fs\<rfloor>; F' = String.explode F;
     h' = rm_update a (Obj C (tm_update F' (lm_update D v (case tm_lookup (String.explode F) fs of None \<Rightarrow> lm_empty () | Some fs' \<Rightarrow> fs')) fs)) h \<rbrakk>
  \<Longrightarrow> sc_heap_write h a (CField D F) v h'"

| Arr:
  "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si f el\<rfloor>; h' = rm_update a (Arr T si f (rm_update n v el)) h \<rbrakk>
  \<Longrightarrow> sc_heap_write h a (ACell n) v h'"

| ArrObj:
  "\<lbrakk> rm_lookup a h = \<lfloor>Arr T si f el\<rfloor>; h' = rm_update a (Arr T si (lm_update F v f) el) h \<rbrakk>
  \<Longrightarrow> sc_heap_write h a (CField Object F) v h'"

hide_fact (open) Obj Arr ArrObj

inductive_cases sc_heap_write_cases [elim!]:
  "sc_heap_write h a (CField C F) v h'"
  "sc_heap_write h a (ACell n) v h'"

consts sc_spurious_wakeups :: bool

lemma new_Addr_SomeD: "new_Addr h = \<lfloor>a\<rfloor> \<Longrightarrow> rm_lookup a h = None"
apply(simp add: new_Addr_def)
apply(drule rm.max_None[OF rm.invar])
apply(simp add: rm.lookup_correct rel_of_def)
apply(clarsimp simp add: rm.lookup_correct)
apply(frule rm.max_Some[OF rm.invar])
apply(clarsimp simp add: rel_of_def)
apply(hypsubst_thin)
apply(rule ccontr)
apply(clarsimp)
apply(drule_tac k'="Suc a" in rm.max_Some(2)[OF rm.invar])
apply(auto simp add: rel_of_def)
done

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

lemma new_Addr_SomeI: "\<exists>a. new_Addr h = Some a"
by(simp add: new_Addr_def)

lemma sc_start_heap_ok: "sc_start_heap_ok P"
by(simp add: sc.start_heap_ok_def sc.start_heap_data_def initialization_list_def sc.create_initial_object_simps sc_allocate_def case_option_conv_if new_Addr_SomeI sys_xcpts_list_def del: blank.simps split del: option.split if_split)

lemma sc_wf_start_state_iff:
  "sc_wf_start_state P C M vs \<longleftrightarrow> (\<exists>Ts T meth D. P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D \<and> P,sc_start_heap P \<turnstile>sc vs [:\<le>] Ts)"
by(simp add: sc.wf_start_state.simps sc_start_heap_ok)

lemma sc_heap:
  "heap addr2thread_id thread_id2addr (sc_allocate P) sc_typeof_addr sc_heap_write P"
proof
  fix h' a h hT
  assume "(h', a) \<in> sc_allocate P h hT"
  thus "sc_typeof_addr h' a = \<lfloor>hT\<rfloor>"
    by(auto simp add: sc_allocate_def sc_typeof_addr_def rm.lookup_correct rm.update_correct dest: new_Addr_SomeD split: if_split_asm)
next
  fix h h' hT a
  assume "(h', a) \<in> sc_allocate P h hT"
  from this[symmetric] show "h \<unlhd>sc h'"
    by(fastforce simp add: sc_allocate_def sc_typeof_addr_def sc.hext_def rm.lookup_correct rm.update_correct intro!: map_leI dest: new_Addr_SomeD)
next
  fix h a al v h'
  assume "sc_heap_write h a al v h'"
  thus "h \<unlhd>sc h'"
    by(cases al)(auto intro!: sc.hextI simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct)
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
    P
  for P by(rule sc_heap)

declare sc.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

lemma sc_hext_new:
  "rm_lookup a h = None \<Longrightarrow> h \<unlhd>sc rm_update a arrobj h"
by(rule sc.hextI)(auto simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct dest!: new_Addr_SomeD)

lemma sc_hext_upd_obj: "rm_lookup a h = Some (Obj C fs) \<Longrightarrow> h \<unlhd>sc rm_update a (Obj C fs') h"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def rm.lookup_correct rm.update_correct)

lemma sc_hext_upd_arr: "\<lbrakk> rm_lookup a h = Some (Arr T si f e) \<rbrakk> \<Longrightarrow> h \<unlhd>sc rm_update a (Arr T si f' e') h"
by(rule sc.hextI)(auto simp:fun_upd_apply sc_typeof_addr_def rm.lookup_correct rm.update_correct)

subsection \<open>Conformance\<close>

definition sc_oconf :: "'m prog \<Rightarrow> heap \<Rightarrow> heapobj \<Rightarrow> bool"   ("_,_ \<turnstile>sc _ \<surd>" [51,51,51] 50)
where
  "P,h \<turnstile>sc obj \<surd>  \<equiv>
   (case obj of 
     Obj C fs \<Rightarrow> 
        is_class P C \<and> 
        (\<forall>F D T fm. P \<turnstile> C has F:T (fm) in D \<longrightarrow> 
           (\<exists>fs' v. tm_\<alpha> fs (String.explode F) = Some fs' \<and> lm_\<alpha> fs' D = Some v \<and> P,h \<turnstile>sc v :\<le> T))
   | Arr T si f el \<Rightarrow> 
      is_type P (T\<lfloor>\<rceil>) \<and> (\<forall>n. n < si \<longrightarrow> (\<exists>v. rm_\<alpha> el n = Some v \<and> P,h \<turnstile>sc v :\<le> T)) \<and>
      (\<forall>F T fm. P \<turnstile> Object has F:T (fm) in Object \<longrightarrow> (\<exists>v. lm_lookup F f = Some v \<and> P,h \<turnstile>sc v :\<le> T)))"

definition sc_hconf :: "'m prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile>sc _ \<surd>" [51,51] 50)
where "P \<turnstile>sc h \<surd> \<longleftrightarrow> (\<forall>a obj. rm_\<alpha> h a = Some obj \<longrightarrow> P,h \<turnstile>sc obj \<surd>)"

interpretation sc: 
  heap_conf_base  
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
.

lemma sc_conf_upd_obj: "rm_lookup a h = Some(Obj C fs) \<Longrightarrow> (P,rm_update a (Obj C fs') h \<turnstile>sc x :\<le> T) = (P,h \<turnstile>sc x :\<le> T)"
apply (unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply (auto simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct split: if_split_asm)
done

lemma sc_conf_upd_arr:
  "rm_lookup a h = Some(Arr T si f el) \<Longrightarrow> (P,rm_update a (Arr T si f' el') h \<turnstile>sc x :\<le> T') = (P,h \<turnstile>sc x :\<le> T')"
apply(unfold sc.conf_def)
apply (rule val.induct)
apply (auto simp:fun_upd_apply)
apply(auto simp add: sc_typeof_addr_def rm.lookup_correct rm.update_correct split: if_split_asm)
done

lemma sc_oconf_hext: "P,h \<turnstile>sc obj \<surd> \<Longrightarrow> h \<unlhd>sc h' \<Longrightarrow> P,h' \<turnstile>sc obj \<surd>"
unfolding sc_oconf_def
by(fastforce split: heapobj.split elim: sc.conf_hext)

lemma map_of_fields_init_fields:
  assumes "map_of FDTs (F, D) = \<lfloor>(T, fm)\<rfloor>"
  shows "\<exists>fs' v. tm_\<alpha> (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) FDTs)) (String.explode F) = \<lfloor>fs'\<rfloor> \<and> lm_\<alpha> fs' D = \<lfloor>v\<rfloor> \<and> sc.conf P h v T"
using assms
  by(induct FDTs)(auto simp add: tm.lookup_correct tm.update_correct lm.update_correct init_fields_def String.explode_inject)

lemma sc_oconf_init_fields:
  assumes "P \<turnstile> C has_fields FDTs"
  shows "P,h \<turnstile>sc (Obj C (init_fields (map (\<lambda>(FD, (T, fm)). (FD, T)) FDTs))) \<surd>"
using assms has_fields_is_class[OF assms] map_of_fields_init_fields[of FDTs]
by(fastforce simp add: has_field_def sc_oconf_def dest: has_fields_fun)

lemma sc_oconf_init_arr:
  assumes type: "is_type P (T\<lfloor>\<rceil>)"
  shows "P,h \<turnstile>sc Arr T n (init_fields_array (map (\<lambda>((F, D), (T, fm)). (F, T)) (TypeRel.fields P Object))) (init_cells T n) \<surd>"
proof -
  { fix n'
    assume "n' < n"
    { fix rm and k :: nat
      assume "\<forall>i<k. \<exists>v. rm_\<alpha> rm i = \<lfloor>v\<rfloor> \<and> sc.conf P h v T"
      with \<open>n' < n\<close> have "\<exists>v. rm_\<alpha> (foldl (\<lambda>cells i. rm_update i (default_val T) cells) rm [k..<n]) n' = \<lfloor>v\<rfloor> \<and> sc.conf P h v T"
        by(induct m\<equiv>"n-k" arbitrary: n k rm)(auto simp add: rm.update_correct upt_conv_Cons type)
    }
    from this[of 0 "rm_empty ()"]
    have "\<exists>v. rm_\<alpha> (foldl (\<lambda>cells i. rm_update i (default_val T) cells) (rm_empty ()) [0..<n]) n' = \<lfloor>v\<rfloor> \<and> sc.conf P h v T" by simp
  }
  moreover
  { fix F T fm
    assume "P \<turnstile> Object has F:T (fm) in Object"
    then obtain FDTs where has: "P \<turnstile> Object has_fields FDTs"
      and FDTs: "map_of FDTs (F, Object) = \<lfloor>(T, fm)\<rfloor>"
      by(auto simp add: has_field_def)
    from has have "snd ` fst ` set FDTs \<subseteq> {Object}" by(rule Object_has_fields_Object)
    with FDTs have "map_of (map ((\<lambda>(F, T). (F, default_val T)) \<circ> (\<lambda>((F, D), T, fm). (F, T))) FDTs) F = \<lfloor>default_val T\<rfloor>"
      by(induct FDTs) auto
    with has FDTs
    have "\<exists>v. lm_lookup F (init_fields_array (map (\<lambda>((F, D), T, fm). (F, T)) (TypeRel.fields P Object))) = \<lfloor>v\<rfloor> \<and>
              sc.conf P h v T"
      by(auto simp add: init_fields_array_def lm_correct has_field_def)
  }
  ultimately show ?thesis using type by(auto simp add: sc_oconf_def init_cells_def)
qed

lemma sc_oconf_fupd [intro?]:
  "\<lbrakk> P \<turnstile> C has F:T (fm) in D; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Obj C fs) \<surd>;
    fs' = (case tm_lookup (String.explode F) fs of None \<Rightarrow> lm_empty () | Some fs' \<Rightarrow> fs') \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Obj C (tm_update (String.explode F) (lm_update D v fs') fs)) \<surd>"
unfolding sc_oconf_def has_field_def
apply(auto dest: has_fields_fun simp add: lm.update_correct tm.update_correct tm.lookup_correct String.explode_inject)
apply(drule (1) has_fields_fun, fastforce)
apply(drule (1) has_fields_fun, fastforce)
done

lemma sc_oconf_fupd_arr [intro?]:
  "\<lbrakk> P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T si f el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T si f (rm_update i v el)) \<surd>"
unfolding sc_oconf_def
by(auto simp add: rm.update_correct)

lemma sc_oconf_fupd_arr_fields:
  "\<lbrakk> P \<turnstile> Object has F:T (fm) in Object; P,h \<turnstile>sc v :\<le> T; P,h \<turnstile>sc (Arr T' si f el) \<surd> \<rbrakk>
  \<Longrightarrow> P,h \<turnstile>sc (Arr T' si (lm_update F v f) el) \<surd>"
unfolding sc_oconf_def by(auto dest: has_field_fun simp add: lm_correct)

lemma sc_oconf_new: "\<lbrakk> P,h \<turnstile>sc obj \<surd>; rm_lookup a h = None \<rbrakk> \<Longrightarrow> P,rm_update a arrobj h \<turnstile>sc obj \<surd>"
by(erule sc_oconf_hext)(rule sc_hext_new)

lemmas sc_oconf_upd_obj = sc_oconf_hext [OF _ sc_hext_upd_obj]

lemma sc_oconf_upd_arr:
  assumes "P,h \<turnstile>sc obj \<surd>"
  and ha: "rm_lookup a h = \<lfloor>Arr T si f el\<rfloor>"
  shows "P,rm_update a (Arr T si f' el') h \<turnstile>sc obj \<surd>"
using assms
by(fastforce simp add: sc_oconf_def sc_conf_upd_arr[OF ha] split: heapobj.split)

lemma sc_oconf_blank: "is_htype P hT \<Longrightarrow> P,h \<turnstile>sc blank P hT \<surd>"
apply(cases hT)
 apply(fastforce dest: map_of_fields_init_fields simp add: has_field_def sc_oconf_def)
by(auto intro: sc_oconf_init_arr)

lemma sc_hconfD: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile>sc obj \<surd>"
unfolding sc_hconf_def by(auto simp add: rm.lookup_correct)

lemmas sc_preallocated_new = sc.preallocated_hext[OF _ sc_hext_new]
lemmas sc_preallocated_upd_obj = sc.preallocated_hext [OF _ sc_hext_upd_obj]
lemmas sc_preallocated_upd_arr = sc.preallocated_hext [OF _ sc_hext_upd_arr]

lemma sc_hconf_new: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = None; P,h \<turnstile>sc obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a obj h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_new simp add: rm.lookup_correct rm.update_correct)

lemma sc_hconf_upd_obj: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some (Obj C fs); P,h \<turnstile>sc (Obj C fs') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a (Obj C fs') h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_obj simp add: rm.lookup_correct rm.update_correct)

lemma sc_hconf_upd_arr: "\<lbrakk> P \<turnstile>sc h \<surd>; rm_lookup a h = Some(Arr T si f el); P,h \<turnstile>sc (Arr T si f' el') \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile>sc rm_update a (Arr T si f' el') h \<surd>"
unfolding sc_hconf_def
by(auto intro: sc_oconf_upd_arr simp add: rm.lookup_correct rm.update_correct)

lemma sc_heap_conf: 
  "heap_conf addr2thread_id thread_id2addr sc_empty (sc_allocate P) sc_typeof_addr sc_heap_write (sc_hconf P) P"
proof
  show "P \<turnstile>sc sc_empty \<surd>" by(simp add: sc_hconf_def rm.empty_correct)
next
  fix h a hT
  assume "sc_typeof_addr h a = \<lfloor>hT\<rfloor>" "P \<turnstile>sc h \<surd>"
  thus "is_htype P hT"
    by(auto simp add: sc_typeof_addr_def sc_oconf_def dest!: sc_hconfD split: heapobj.split_asm)
next
  fix h' hT h a
  assume "P \<turnstile>sc h \<surd>" "(h', a) \<in> sc_allocate P h hT" "is_htype P hT"
  thus "P \<turnstile>sc h' \<surd>"
    by(auto simp add: sc_allocate_def dest!: new_Addr_SomeD intro: sc_hconf_new sc_oconf_blank split: if_split_asm)
next
  fix h a al T v h'
  assume "P \<turnstile>sc h \<surd>"
    and "sc.addr_loc_type P h a al T"
    and "P,h \<turnstile>sc v :\<le> T"
    and "sc_heap_write h a al v h'"
  thus "P \<turnstile>sc h' \<surd>"
    by(cases al)(fastforce elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def intro: sc_hconf_upd_obj sc_oconf_fupd sc_hconfD sc_hconf_upd_arr sc_oconf_fupd_arr sc_oconf_fupd_arr_fields)+
qed

interpretation sc: 
  heap_conf
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
  from alt obtain arrobj where arrobj: "rm_lookup a h = \<lfloor>arrobj\<rfloor>"
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
      with \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close> obtain fs' v 
      where "tm_lookup (String.explode F) fs = \<lfloor>fs'\<rfloor>" "lm_lookup D fs' = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
      by(fastforce simp add: sc_oconf_def tm.lookup_correct lm.lookup_correct)
      thus ?thesis using Obj arrobj by(auto intro: sc_heap_read.intros)
    next
      case (Arr T' si f el)
      with \<open>sc_typeof_addr h a = \<lfloor>U\<rfloor>\<close> arrobj
      have [simp]: "U = Array_type T' si" by(auto simp add: sc_typeof_addr_def)
      from hconf arrobj Arr have "P,h \<turnstile>sc Arr T' si f el \<surd>" by(auto dest: sc_hconfD)
      from \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close> have [simp]: "D = Object"
        by(auto dest: has_field_decl_above)
      with \<open>P,h \<turnstile>sc Arr T' si f el \<surd>\<close> \<open>P \<turnstile> class_type_of U has F:T (fm) in D\<close>
      obtain v where "lm_lookup F f = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
        by(fastforce simp add: sc_oconf_def)
      thus ?thesis using Arr arrobj by(auto intro: sc_heap_read.intros)
    qed
  next
    case (addr_loc_type_cell n' n)
    with arrobj obtain si f el
      where [simp]: "arrobj = Arr T si f el"
      by(cases arrobj)(auto simp add: sc_typeof_addr_def)
    from addr_loc_type_cell arrobj
    have [simp]: "al = ACell n" and n: "n < si" by(auto simp add: sc_typeof_addr_def)
    from hconf arrobj have "P,h \<turnstile>sc Arr T si f el \<surd>" by(auto dest: sc_hconfD)
    with n obtain v where "rm_lookup n el = \<lfloor>v\<rfloor>" "P,h \<turnstile>sc v :\<le> T"
      by(fastforce simp add: sc_oconf_def rm.lookup_correct)
    thus ?thesis using arrobj n by(fastforce intro: sc_heap_read.intros)
  qed
next
  fix h a al T v
  assume alt: "sc.addr_loc_type P h a al T"
  from alt obtain arrobj where arrobj: "rm_lookup a h = \<lfloor>arrobj\<rfloor>"
    by(auto elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
  thus "\<exists>h'. sc_heap_write h a al v h'" using alt
    by(cases arrobj)(fastforce intro: sc_heap_write.intros elim!: sc.addr_loc_type.cases simp add: sc_typeof_addr_def dest: has_field_decl_above)+
qed

interpretation sc: 
  heap_progress
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
    apply(auto elim!: sc_heap_read.cases sc.addr_loc_type.cases simp add: sc_typeof_addr_def)
    apply(fastforce dest!: sc_hconfD simp add: sc_oconf_def tm.lookup_correct lm.lookup_correct rm.lookup_correct)+
    done
qed

interpretation sc: 
  heap_conf_read
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
