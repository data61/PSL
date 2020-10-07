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


section\<open>Node\<close>
text\<open>In this theory, we introduce the types for the Node class.\<close>

theory NodeClass
  imports
    ObjectClass
    "../pointers/NodePointer"
begin

subsubsection\<open>Node\<close>

record RNode = RObject
  + nothing :: unit
register_default_tvars "'Node RNode_ext" 
type_synonym 'Node Node = "'Node RNode_scheme"
register_default_tvars "'Node Node" 
type_synonym ('Object, 'Node) Object = "('Node RNode_ext + 'Object) Object"
register_default_tvars "('Object, 'Node) Object" 

type_synonym ('object_ptr, 'node_ptr, 'Object, 'Node) heap
  = "('node_ptr node_ptr + 'object_ptr, 'Node RNode_ext + 'Object) heap"
register_default_tvars
  "('object_ptr, 'node_ptr, 'Object, 'Node) heap" 


definition node_ptr_kinds :: "(_) heap \<Rightarrow> (_) node_ptr fset"
  where
    "node_ptr_kinds heap = 
    (the |`| (cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r |`| (ffilter is_node_ptr_kind (object_ptr_kinds heap))))"

lemma node_ptr_kinds_simp [simp]: 
  "node_ptr_kinds (Heap (fmupd (cast node_ptr) node (the_heap h))) 
       = {|node_ptr|} |\<union>| node_ptr_kinds h"
  apply(auto simp add: node_ptr_kinds_def)[1]
  by force

definition cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) Object \<Rightarrow> (_) Node option"
  where
    "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e obj = (case RObject.more obj of Inl node 
    \<Rightarrow> Some (RObject.extend (RObject.truncate obj) node) | _ \<Rightarrow> None)"
adhoc_overloading cast cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e

definition cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:: "(_) Node \<Rightarrow> (_) Object"
  where
    "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t node = (RObject.extend (RObject.truncate node) (Inl (RObject.more node)))"
adhoc_overloading cast cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

definition is_node_kind :: "(_) Object \<Rightarrow> bool"
  where
    "is_node_kind ptr \<longleftrightarrow> cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr \<noteq> None"

definition get\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) node_ptr \<Rightarrow> (_) heap \<Rightarrow> (_) Node option"
  where                             
    "get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr h = Option.bind (get (cast node_ptr) h) cast"
adhoc_overloading get get\<^sub>N\<^sub>o\<^sub>d\<^sub>e

locale l_type_wf_def\<^sub>N\<^sub>o\<^sub>d\<^sub>e
begin
definition a_type_wf :: "(_) heap \<Rightarrow> bool"
  where
    "a_type_wf h = (ObjectClass.type_wf h 
                    \<and> (\<forall>node_ptr. node_ptr |\<in>| node_ptr_kinds h 
                                     \<longrightarrow> get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr h \<noteq> None))"
end
global_interpretation l_type_wf_def\<^sub>N\<^sub>o\<^sub>d\<^sub>e defines type_wf = a_type_wf .
lemmas type_wf_defs = a_type_wf_def

locale l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e = l_type_wf type_wf for type_wf :: "((_) heap \<Rightarrow> bool)" +
  assumes type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e: "type_wf h \<Longrightarrow> NodeClass.type_wf h"

sublocale l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e \<subseteq> l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
  apply(unfold_locales)
  using ObjectClass.a_type_wf_def by auto

locale l_get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas = l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
begin
sublocale l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas by unfold_locales
lemma get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf:
  assumes "type_wf h"
  shows "node_ptr |\<in>| node_ptr_kinds h \<longleftrightarrow> get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr h \<noteq> None"
  using l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e_axioms assms
  apply(simp add: type_wf_defs get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)
  by (metis (mono_tags, lifting) bind_eq_None_conv ffmember_filter fimage_eqI 
      is_node_ptr_kind_cast get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf local.l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_axioms 
      node_ptr_casts_commute2 node_ptr_kinds_def option.sel option.simps(3))
end

global_interpretation l_get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas type_wf
  by unfold_locales

definition put\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) node_ptr \<Rightarrow> (_) Node \<Rightarrow> (_) heap \<Rightarrow> (_) heap"
  where
    "put\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr node = put (cast node_ptr) (cast node)"
adhoc_overloading put put\<^sub>N\<^sub>o\<^sub>d\<^sub>e

lemma put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ptr_in_heap:
  assumes "put\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr node h = h'"
  shows "node_ptr |\<in>| node_ptr_kinds h'"
  using assms
  unfolding put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def node_ptr_kinds_def
  by (metis ffmember_filter fimage_eqI is_node_ptr_kind_cast node_ptr_casts_commute2 
      option.sel put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ptr_in_heap)

lemma put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_put_ptrs:
  assumes "put\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr node h = h'"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast node_ptr|}"
  using assms
  by (simp add: put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_put_ptrs)

lemma node_ptr_kinds_commutes [simp]: 
  "cast node_ptr |\<in>| object_ptr_kinds h \<longleftrightarrow> node_ptr |\<in>| node_ptr_kinds h"
  apply(auto simp add: node_ptr_kinds_def split: option.splits)[1]
  by (metis (no_types, lifting) ffmember_filter fimage_eqI fset.map_comp 
      is_node_ptr_kind_none node_ptr_casts_commute2
      option.distinct(1) option.sel)

lemma node_empty [simp]: 
  "\<lparr>RObject.nothing = (), RNode.nothing = (), \<dots> = RNode.more node\<rparr> = node"
  by simp

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_inject [simp]: "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x = cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t y \<longleftrightarrow> x = y"
  apply(simp add: cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def RObject.extend_def)
  by (metis (full_types) RObject.surjective old.unit.exhaust)

lemma cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none [simp]: 
  "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e obj = None \<longleftrightarrow> \<not> (\<exists>node. cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t node = obj)"
  apply(auto simp add: cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def RObject.extend_def split: sum.splits)[1]
  by (metis (full_types) RObject.select_convs(2) RObject.surjective old.unit.exhaust)

lemma cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_some [simp]: "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e obj = Some node \<longleftrightarrow> cast node = obj"
  by(auto simp add: cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def RObject.extend_def split: sum.splits)

lemma cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv [simp]: "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e (cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t node) = Some node"
  by simp

locale l_known_ptr\<^sub>N\<^sub>o\<^sub>d\<^sub>e
begin
definition a_known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  where
    "a_known_ptr ptr = False"
end
global_interpretation l_known_ptr\<^sub>N\<^sub>o\<^sub>d\<^sub>e defines known_ptr = a_known_ptr .
lemmas known_ptr_defs = a_known_ptr_def


locale l_known_ptrs\<^sub>N\<^sub>o\<^sub>d\<^sub>e = l_known_ptr known_ptr for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
begin
definition a_known_ptrs :: "(_) heap \<Rightarrow> bool"
  where
    "a_known_ptrs h = (\<forall>ptr. ptr |\<in>| object_ptr_kinds h \<longrightarrow> known_ptr ptr)"

lemma known_ptrs_known_ptr: "a_known_ptrs h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptrs_def)

lemma known_ptrs_preserved: "object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> a_known_ptrs h = a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
lemma known_ptrs_subset: "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h \<Longrightarrow> a_known_ptrs h \<Longrightarrow> a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
end
global_interpretation l_known_ptrs\<^sub>N\<^sub>o\<^sub>d\<^sub>e known_ptr defines known_ptrs = a_known_ptrs .
lemmas known_ptrs_defs = a_known_ptrs_def

lemma known_ptrs_is_l_known_ptrs: "l_known_ptrs known_ptr known_ptrs"
  using known_ptrs_known_ptr known_ptrs_preserved l_known_ptrs_def known_ptrs_subset by blast

lemma get_node_ptr_simp1 [simp]: "get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr (put\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr node h) = Some node"
  by(auto simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)
lemma get_node_ptr_simp2 [simp]: 
  "node_ptr \<noteq> node_ptr' \<Longrightarrow> get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr (put\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr' node h) = get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr h"
  by(auto simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)

end
