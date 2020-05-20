(*  Title:      JinjaThreads/Common/Heap.thy
    Author:     Andreas Lochbihler

    Reminiscent of the Jinja theory Common/Objects.thy
*)

section \<open>An abstract heap model\<close>

theory Heap
imports 
  Value
begin

primrec typeof :: "'addr val \<rightharpoonup> ty"
where
  "typeof  Unit    = Some Void"
| "typeof  Null    = Some NT"
| "typeof (Bool b) = Some Boolean"
| "typeof (Intg i) = Some Integer"
| "typeof (Addr a) = None"

datatype addr_loc =
    CField cname vname
  | ACell nat

lemma rec_addr_loc [simp]: "rec_addr_loc = case_addr_loc"
by(auto simp add: fun_eq_iff split: addr_loc.splits)

primrec is_volatile :: "'m prog \<Rightarrow> addr_loc \<Rightarrow> bool"
where 
  "is_volatile P (ACell n) = False"
| "is_volatile P (CField D F) = volatile (snd (snd (field P D F)))"

locale heap_base =
  addr_base addr2thread_id thread_id2addr 
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  +
  fixes spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

fun typeof_h :: "'heap \<Rightarrow> 'addr val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub> (Addr a) = map_option ty_of_htype (typeof_addr h a)"
| "typeof\<^bsub>h\<^esub>  v = typeof v"

definition cname_of :: "'heap \<Rightarrow> 'addr \<Rightarrow> cname"
where "cname_of h a = the_Class (ty_of_htype (the (typeof_addr h a)))"

definition hext :: "'heap \<Rightarrow> 'heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h' \<equiv> typeof_addr h \<subseteq>\<^sub>m typeof_addr h'"

context
  notes [[inductive_internals]]
begin

inductive addr_loc_type :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool"
  ("_,_ \<turnstile> _@_ : _" [50, 50, 50, 50, 50] 51)
for P :: "'m prog" and h :: 'heap and a :: 'addr
where
  addr_loc_type_field:
  "\<lbrakk> typeof_addr h a = \<lfloor>U\<rfloor>; P \<turnstile> class_type_of U has F:T (fm) in D \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> a@CField D F : T"

| addr_loc_type_cell:
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n'\<rfloor>; n < n' \<rbrakk>
  \<Longrightarrow> P,h \<turnstile> a@ACell n : T"

end

definition typeof_addr_loc :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty"
where "typeof_addr_loc P h a al = (THE T. P,h \<turnstile> a@al : T)"

definition deterministic_heap_ops :: bool
where
  "deterministic_heap_ops \<longleftrightarrow>
  (\<forall>h ad al v v'. heap_read h ad al v \<longrightarrow> heap_read h ad al v' \<longrightarrow> v = v') \<and>
  (\<forall>h ad al v h' h''. heap_write h ad al v h' \<longrightarrow> heap_write h ad al v h'' \<longrightarrow> h' = h'') \<and>
  (\<forall>h hT h' a h'' a'. (h', a) \<in> allocate h hT \<longrightarrow> (h'', a') \<in> allocate h hT \<longrightarrow> h' = h'' \<and> a = a') \<and>
  \<not> spurious_wakeups"

end

lemma typeof_lit_eq_Boolean [simp]: "(typeof v = Some Boolean) = (\<exists>b. v = Bool b)"
by(cases v)(auto)

lemma typeof_lit_eq_Integer [simp]: "(typeof v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v)(auto)

lemma typeof_lit_eq_NT [simp]: "(typeof v = Some NT) = (v = Null)"
by(cases v)(auto)

lemma typeof_lit_eq_Void [simp]: "typeof v = Some Void \<longleftrightarrow> v = Unit"
by(cases v)(auto)

lemma typeof_lit_neq_Class [simp]: "typeof v \<noteq> Some (Class C)"
by(cases v) auto

lemma typeof_lit_neq_Array [simp]: "typeof v \<noteq> Some (Array T)"
by(cases v) auto

lemma typeof_NoneD [simp,dest]:
  "typeof v = Some x \<Longrightarrow> \<not> is_Addr v"
  by (cases v) auto

lemma typeof_lit_is_type:
  "typeof v = Some T \<Longrightarrow> is_type P T"
by(cases v) auto

context heap_base begin

lemma typeof_h_eq_Boolean [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
by(cases v)(auto)

lemma typeof_h_eq_Integer [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v)(auto)

lemma typeof_h_eq_NT [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
by(cases v)(auto)


lemma hextI:
  "\<lbrakk> \<And>a C. typeof_addr h a = \<lfloor>Class_type C\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Class_type C\<rfloor>;
     \<And>a T n. typeof_addr h a = \<lfloor>Array_type T n\<rfloor> \<Longrightarrow> typeof_addr h' a = \<lfloor>Array_type T n\<rfloor> \<rbrakk>
  \<Longrightarrow> h \<unlhd> h'"
unfolding hext_def 
by(rule map_leI)(case_tac v, simp_all)

lemma hext_objD:
  assumes "h \<unlhd> h'"
  and "typeof_addr h a = \<lfloor>Class_type C\<rfloor>"
  shows "typeof_addr h' a = \<lfloor>Class_type C\<rfloor>"
using assms unfolding hext_def by(auto dest: map_le_SomeD)

lemma hext_arrD:
  assumes "h \<unlhd> h'" "typeof_addr h a = \<lfloor>Array_type T n\<rfloor>"
  shows "typeof_addr h' a = \<lfloor>Array_type T n\<rfloor>"
using assms unfolding hext_def by(blast dest: map_le_SomeD)

lemma hext_refl [iff]: "h \<unlhd> h"
by (rule hextI) blast+

lemma hext_trans [trans]: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
unfolding hext_def by(rule map_le_trans)

lemma typeof_lit_typeof:
  "typeof v = \<lfloor>T\<rfloor> \<Longrightarrow> typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
by(cases v)(simp_all)

lemma addr_loc_type_fun:
  "\<lbrakk> P,h \<turnstile> a@al : T; P,h \<turnstile> a@al : T' \<rbrakk> \<Longrightarrow> T = T'"
by(auto elim!: addr_loc_type.cases dest: has_field_fun)

lemma THE_addr_loc_type:
  "P,h \<turnstile> a@al : T \<Longrightarrow> (THE T. P,h \<turnstile> a@al : T) = T"
by(rule the_equality)(auto dest: addr_loc_type_fun)

lemma typeof_addr_locI [simp]:
  "P,h \<turnstile> a@al : T \<Longrightarrow> typeof_addr_loc P h a al = T"
by(auto simp add: typeof_addr_loc_def dest: addr_loc_type_fun)

lemma deterministic_heap_opsI:
  "\<lbrakk> \<And>h ad al v v'. \<lbrakk> heap_read h ad al v; heap_read h ad al v' \<rbrakk> \<Longrightarrow> v = v';
     \<And>h ad al v h' h''. \<lbrakk> heap_write h ad al v h'; heap_write h ad al v h'' \<rbrakk> \<Longrightarrow> h' = h'';
     \<And>h hT h' a h'' a'. \<lbrakk> (h', a) \<in> allocate h hT; (h'', a') \<in> allocate h hT \<rbrakk> \<Longrightarrow> h' = h'' \<and> a = a';
     \<not> spurious_wakeups \<rbrakk>
  \<Longrightarrow> deterministic_heap_ops"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_readD:
  "\<lbrakk> deterministic_heap_ops; heap_read h ad al v; heap_read h ad al v' \<rbrakk> \<Longrightarrow> v = v'"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_writeD:
  "\<lbrakk> deterministic_heap_ops; heap_write h ad al v h'; heap_write h ad al v h'' \<rbrakk> \<Longrightarrow> h' = h''"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_allocateD:
  "\<lbrakk> deterministic_heap_ops; (h', a) \<in> allocate h hT; (h'', a') \<in> allocate h hT \<rbrakk> \<Longrightarrow> h' = h'' \<and> a = a'"
unfolding deterministic_heap_ops_def by blast

lemma deterministic_heap_ops_no_spurious_wakeups:
  "deterministic_heap_ops \<Longrightarrow> \<not> spurious_wakeups"
unfolding deterministic_heap_ops_def by blast

end

locale addr_conv =
  heap_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
  +
  prog P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'m prog"
  +
  assumes addr2thread_id_inverse: 
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> thread_id2addr (addr2thread_id a) = a"
begin

lemma typeof_addr_thread_id2_addr_addr2thread_id [simp]:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type C\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> typeof_addr h (thread_id2addr (addr2thread_id a)) = \<lfloor>Class_type C\<rfloor>"
by(simp add: addr2thread_id_inverse)

end

locale heap =
  addr_conv
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'m prog"
  +
  assumes allocate_SomeD: "\<lbrakk> (h', a) \<in> allocate h hT; is_htype P hT \<rbrakk> \<Longrightarrow> typeof_addr h' a = Some hT"

  and hext_allocate: "\<And>a. (h', a) \<in> allocate h hT \<Longrightarrow> h \<unlhd> h'"

  and hext_heap_write:
  "heap_write h a al v h' \<Longrightarrow> h \<unlhd> h'"

begin

lemmas hext_heap_ops = hext_allocate hext_heap_write

lemma typeof_addr_hext_mono:
  "\<lbrakk> h \<unlhd> h'; typeof_addr h a = \<lfloor>hT\<rfloor> \<rbrakk> \<Longrightarrow> typeof_addr h' a = \<lfloor>hT\<rfloor>"
unfolding hext_def by(rule map_le_SomeD)

lemma hext_typeof_mono:
  "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
by (cases v)(auto intro: typeof_addr_hext_mono)

lemma addr_loc_type_hext_mono:
  "\<lbrakk> P,h \<turnstile> a@al : T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> a@al : T"
by(force elim!: addr_loc_type.cases intro: addr_loc_type.intros elim: typeof_addr_hext_mono dest: hext_arrD)

lemma type_of_hext_type_of: \<comment> \<open>FIXME: What's this rule good for?\<close>
  "\<lbrakk> typeof\<^bsub>h\<^esub> w = \<lfloor>T\<rfloor>; hext h h' \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> w = \<lfloor>T\<rfloor>"
by(rule hext_typeof_mono)

lemma hext_None: "\<lbrakk> h \<unlhd> h'; typeof_addr h' a = None \<rbrakk> \<Longrightarrow> typeof_addr h a = None"
by(rule ccontr)(auto dest: typeof_addr_hext_mono)

lemma map_typeof_hext_mono:
  "\<lbrakk> map typeof\<^bsub>h\<^esub> vs = map Some Ts; h \<unlhd> h' \<rbrakk> \<Longrightarrow>  map typeof\<^bsub>h'\<^esub> vs = map Some Ts"
apply(induct vs arbitrary: Ts)
apply(auto simp add: Cons_eq_map_conv intro: hext_typeof_mono)
done

lemma hext_typeof_addr_map_le:
  "h \<unlhd> h' \<Longrightarrow> typeof_addr h \<subseteq>\<^sub>m typeof_addr h'"
by(auto simp add: map_le_def dest: typeof_addr_hext_mono)

lemma hext_dom_typeof_addr_subset:
  "h \<unlhd> h' \<Longrightarrow> dom (typeof_addr h) \<subseteq> dom (typeof_addr h')"
by (metis hext_typeof_addr_map_le map_le_implies_dom_le)

end

declare heap_base.typeof_h.simps [code]
declare heap_base.cname_of_def [code]

end
