(***********************************************************************************
 * Copyright (c) 2016-2018 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>Object\<close>
text\<open>In this theory, we introduce the definition of the class Object. This class is the 
common superclass of our class model.\<close>

theory ObjectClass
  imports
    BaseClass
    "../pointers/ObjectPointer"
begin

record RObject =
  nothing :: unit
register_default_tvars "'Object RObject_ext" 
type_synonym 'Object Object = "'Object RObject_scheme"
register_default_tvars "'Object Object" 

datatype ('object_ptr, 'Object) heap = Heap (the_heap: "((_) object_ptr, (_) Object) fmap")
register_default_tvars "('object_ptr, 'Object) heap"  

definition object_ptr_kinds :: "(_) heap \<Rightarrow> (_) object_ptr fset"
  where
    "object_ptr_kinds = fmdom \<circ> the_heap"

lemma object_ptr_kinds_simp [simp]: 
  "object_ptr_kinds (Heap (fmupd object_ptr object (the_heap h))) 
           = {|object_ptr|} |\<union>| object_ptr_kinds h"
  by(auto simp add: object_ptr_kinds_def)

definition get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) object_ptr \<Rightarrow> (_) heap \<Rightarrow> (_) Object option"
  where
    "get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = fmlookup (the_heap h) ptr"
adhoc_overloading get get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t 

locale l_type_wf_def\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
begin
definition a_type_wf :: "(_) heap \<Rightarrow> bool"
  where
    "a_type_wf h = True"
end
global_interpretation l_type_wf_def\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t defines type_wf = a_type_wf .
lemmas type_wf_defs = a_type_wf_def

locale l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t = l_type_wf type_wf for type_wf :: "((_) heap \<Rightarrow> bool)" +
  assumes type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t: "type_wf h \<Longrightarrow> ObjectClass.type_wf h"

locale l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas = l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
begin
lemma get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf:
  assumes "type_wf h"
  shows "object_ptr |\<in>| object_ptr_kinds h \<longleftrightarrow> get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr h \<noteq> None"
  using l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_axioms assms
  apply(simp add: type_wf_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
  by (simp add: fmlookup_dom_iff object_ptr_kinds_def)
end

global_interpretation l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas type_wf
  by (simp add: l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas.intro l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t.intro)

definition put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) object_ptr \<Rightarrow> (_) Object \<Rightarrow> (_) heap \<Rightarrow> (_) heap"
  where
    "put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h = Heap (fmupd ptr obj (the_heap h))"
adhoc_overloading put put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

lemma put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ptr_in_heap:
  assumes "put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr object h = h'"
  shows "object_ptr |\<in>| object_ptr_kinds h'"
  using assms
  unfolding put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def
  by auto

lemma put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_put_ptrs:
  assumes "put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr object h = h'"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|object_ptr|}"
  using assms
  by (metis comp_apply fmdom_fmupd funion_finsert_right heap.sel object_ptr_kinds_def 
      sup_bot.right_neutral put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)

lemma object_more_extend_id [simp]: "more (extend x y) = y"
  by(simp add: extend_def)

lemma object_empty [simp]: "\<lparr>nothing = (), \<dots> = more x\<rparr> = x"
  by simp

locale l_known_ptr\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
begin
definition a_known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  where
    "a_known_ptr ptr = False"

lemma known_ptr_not_object_ptr: 
  "a_known_ptr ptr \<Longrightarrow> \<not>is_object_ptr ptr \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptr_def)
end
global_interpretation l_known_ptr\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t defines known_ptr = a_known_ptr .
lemmas known_ptr_defs = a_known_ptr_def

locale l_known_ptrs = l_known_ptr known_ptr for known_ptr :: "(_) object_ptr \<Rightarrow> bool" +
  fixes known_ptrs :: "(_) heap \<Rightarrow> bool"
  assumes known_ptrs_known_ptr: "known_ptrs h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptr ptr"
  assumes known_ptrs_preserved: "object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> known_ptrs h = known_ptrs h'"
  assumes known_ptrs_subset: "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h \<Longrightarrow> known_ptrs h \<Longrightarrow> known_ptrs h'"

locale l_known_ptrs\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t = l_known_ptr known_ptr for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
begin
definition a_known_ptrs :: "(_) heap \<Rightarrow> bool"
  where
    "a_known_ptrs h = (\<forall>ptr. ptr |\<in>| object_ptr_kinds h \<longrightarrow> known_ptr ptr)"

lemma known_ptrs_known_ptr: 
  "a_known_ptrs h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptrs_def)

lemma known_ptrs_preserved: "object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> a_known_ptrs h = a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
lemma known_ptrs_subset: "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h \<Longrightarrow> a_known_ptrs h \<Longrightarrow> a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
end
global_interpretation l_known_ptrs\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t known_ptr defines known_ptrs = a_known_ptrs .
lemmas known_ptrs_defs = a_known_ptrs_def

lemma known_ptrs_is_l_known_ptrs: "l_known_ptrs known_ptr known_ptrs"
  using known_ptrs_known_ptr known_ptrs_preserved l_known_ptrs_def known_ptrs_subset by blast


lemma get_object_ptr_simp1 [simp]: "get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr object h) = Some object"
  by(simp add: get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
lemma get_object_ptr_simp2 [simp]: 
  "object_ptr \<noteq> object_ptr' 
   \<Longrightarrow> get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr' object h) = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr h"
  by(simp add: get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)


subsection\<open>Limited Heap Modifications\<close>

definition heap_unchanged_except :: "(_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  where
    "heap_unchanged_except S h h' = (\<forall>ptr \<in> (fset (object_ptr_kinds h) 
                                   \<union> (fset (object_ptr_kinds h'))) - S. get ptr h = get ptr h')"

definition delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) object_ptr \<Rightarrow> (_) heap \<Rightarrow> (_) heap option" where
  "delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = (if ptr |\<in>| object_ptr_kinds h then Some (Heap (fmdrop ptr (the_heap h))) 
                                                      else None)"

lemma delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_pointer_removed:
  assumes "delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = Some h'"
  shows "ptr |\<notin>| object_ptr_kinds h'"
  using assms
  by(auto simp add: delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def object_ptr_kinds_def split: if_splits)

lemma delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_pointer_ptr_in_heap:
  assumes "delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = Some h'"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def object_ptr_kinds_def split: if_splits)

lemma delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ok:
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h \<noteq> None"
  using assms
  by(auto simp add: delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def object_ptr_kinds_def split: if_splits)

end
