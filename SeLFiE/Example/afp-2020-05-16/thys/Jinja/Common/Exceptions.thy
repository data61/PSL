(*  Title:      HOL/MicroJava/J/Exceptions.thy

    Author:     Gerwin Klein, Martin Strecker
    Copyright   2002 Technische Universitaet Muenchen
*)

section \<open>Exceptions\<close>

theory Exceptions imports Objects begin

definition NullPointer :: cname
where
  "NullPointer \<equiv> ''NullPointer''"

definition ClassCast :: cname
where
  "ClassCast \<equiv> ''ClassCast''"

definition OutOfMemory :: cname
where
  "OutOfMemory \<equiv> ''OutOfMemory''"

definition sys_xcpts :: "cname set"
where
  "sys_xcpts  \<equiv>  {NullPointer, ClassCast, OutOfMemory}"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
where
  "addr_of_sys_xcpt s \<equiv> if s = NullPointer then 0 else
                        if s = ClassCast then 1 else
                        if s = OutOfMemory then 2 else undefined"

definition start_heap :: "'c prog \<Rightarrow> heap"
where
  "start_heap G \<equiv> Map.empty (addr_of_sys_xcpt NullPointer \<mapsto> blank G NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank G ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank G OutOfMemory)"

definition preallocated :: "heap \<Rightarrow> bool"
where
  "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. \<exists>fs. h(addr_of_sys_xcpt C) = Some (C,fs)"


subsection "System exceptions"

lemma [simp]: "NullPointer \<in> sys_xcpts \<and> OutOfMemory \<in> sys_xcpts \<and> ClassCast \<in> sys_xcpts"
(*<*)by(simp add: sys_xcpts_def)(*>*)


lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast\<rbrakk> \<Longrightarrow> P C"
(*<*)by (auto simp add: sys_xcpts_def)(*>*)


subsection "@{term preallocated}"

lemma preallocated_dom [simp]: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> dom h"
(*<*)by (fastforce simp:preallocated_def dom_def)(*>*)


lemma preallocatedD:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> \<exists>fs. h(addr_of_sys_xcpt C) = Some (C, fs)"
(*<*)by(auto simp add: preallocated_def sys_xcpts_def)(*>*)


lemma preallocatedE [elim?]:
  "\<lbrakk> preallocated h;  C \<in> sys_xcpts; \<And>fs. h(addr_of_sys_xcpt C) = Some(C,fs) \<Longrightarrow> P h C\<rbrakk>
  \<Longrightarrow> P h C"
(*<*)by (fast dest: preallocatedD)(*>*)


lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_ClassCast [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ClassCast)) = Some(Class ClassCast)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_OutOfMemory [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt OutOfMemory)) = Some(Class OutOfMemory)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_NullPointer [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NullPointer)) = Some(Class NullPointer)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
(*<*)by (simp add: preallocated_def hext_def)(*>*)

(*<*)
lemmas preallocated_upd_obj = preallocated_hext [OF _ hext_upd_obj]
lemmas preallocated_new  = preallocated_hext [OF _ hext_new]
(*>*)


lemma preallocated_start:
  "preallocated (start_heap P)"
(*<*)by (auto simp add: start_heap_def blank_def sys_xcpts_def fun_upd_apply
                     addr_of_sys_xcpt_def preallocated_def)(*>*)


end
