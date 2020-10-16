(*  Title:       CoreC++
    Author:      Gerwin Klein, Martin Strecker, Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Exceptions\<close>

theory Exceptions imports Objects begin

subsection \<open>Exceptions\<close>


definition NullPointer :: cname where 
  "NullPointer \<equiv> ''NullPointer''"

definition ClassCast :: cname where
  "ClassCast \<equiv> ''ClassCast''"

definition OutOfMemory :: cname where
  "OutOfMemory \<equiv> ''OutOfMemory''"

definition sys_xcpts :: "cname set" where
  "sys_xcpts  \<equiv>  {NullPointer, ClassCast, OutOfMemory}"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr" where
  "addr_of_sys_xcpt s \<equiv> if s = NullPointer then 0 else
                        if s = ClassCast then 1 else
                        if s = OutOfMemory then 2 else undefined"

definition start_heap :: "prog \<Rightarrow> heap" where
  "start_heap P \<equiv> Map.empty (addr_of_sys_xcpt NullPointer \<mapsto> blank P NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank P ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank P OutOfMemory)"

definition preallocated :: "heap \<Rightarrow> bool" where
  "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. \<exists>S. h (addr_of_sys_xcpt C) = Some (C,S)"


subsection "System exceptions"

lemma [simp]: 
"NullPointer \<in> sys_xcpts \<and> OutOfMemory \<in> sys_xcpts \<and> ClassCast \<in> sys_xcpts"
by(simp add: sys_xcpts_def)


lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast\<rbrakk> \<Longrightarrow> P C"
by (auto simp add: sys_xcpts_def)


subsection "@{term preallocated}"

lemma preallocated_dom [simp]: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> dom h"
by (fastforce simp:preallocated_def dom_def)


lemma preallocatedD:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> \<exists>S. h (addr_of_sys_xcpt C) = Some (C,S)"
by(auto simp add: preallocated_def sys_xcpts_def)


lemma preallocatedE [elim?]:
  "\<lbrakk> preallocated h;  C \<in> sys_xcpts; \<And>S. h (addr_of_sys_xcpt C) = Some(C,S) \<Longrightarrow> P h C\<rbrakk>
  \<Longrightarrow> P h C"
by (fast dest: preallocatedD)


lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
by (auto elim: preallocatedE)


lemma preallocated_start:
  "preallocated (start_heap P)"
by (auto simp add: start_heap_def blank_def sys_xcpts_def fun_upd_apply
                     addr_of_sys_xcpt_def preallocated_def)



subsection "@{term start_heap}"

lemma start_Subobj:
"\<lbrakk>start_heap P a = Some(C, S); (Cs,fs) \<in> S\<rbrakk> \<Longrightarrow> Subobjs P C Cs"
by (fastforce elim:init_obj.cases simp:start_heap_def blank_def 
                                    fun_upd_apply split:if_split_asm)

lemma start_SuboSet:
"\<lbrakk>start_heap P a = Some(C, S); Subobjs P C Cs\<rbrakk> \<Longrightarrow> \<exists>fs. (Cs,fs) \<in> S"
by (fastforce intro:init_obj.intros simp:start_heap_def blank_def
                split:if_split_asm)

lemma start_init_obj: "start_heap P a = Some(C,S) \<Longrightarrow> S = Collect (init_obj P C)"
by (auto simp:start_heap_def blank_def split:if_split_asm)

lemma start_subobj:
  "\<lbrakk>start_heap P a = Some(C, S); \<exists>fs. (Cs, fs) \<in> S\<rbrakk> \<Longrightarrow> Subobjs P C Cs"
by (fastforce elim:init_obj.cases simp:start_heap_def blank_def
                  split:if_split_asm)

end
