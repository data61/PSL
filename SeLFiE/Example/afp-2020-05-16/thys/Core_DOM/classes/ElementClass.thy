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

section\<open>Element\<close>
text\<open>In this theory, we introduce the types for the Element  class.\<close>
theory ElementClass
  imports
    NodeClass
    "../pointers/ShadowRootPointer"
begin
text\<open>The type @{type "DOMString"} is a type synonym for @{type "string"}, define 
     in \autoref{sec:Core_DOM_Basic_Datatypes}.\<close>
type_synonym attr_key = DOMString 
type_synonym attr_value = DOMString
type_synonym attrs = "(attr_key, attr_value) fmap"
type_synonym tag_type = DOMString
record ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr) RElement = RNode +
  nothing :: unit
  tag_type :: tag_type
  child_nodes :: "('node_ptr, 'element_ptr, 'character_data_ptr) node_ptr list"
  attrs :: attrs
  shadow_root_opt :: "'shadow_root_ptr shadow_root_ptr option"
type_synonym 
  ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element) Element
  = "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element option) RElement_scheme"
register_default_tvars 
  "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element) Element"
type_synonym 
  ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Node, 'Element) Node
  = "(('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element option) RElement_ext + 'Node) Node"
register_default_tvars 
  "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Node, 'Element) Node"
type_synonym 
  ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Object, 'Node, 'Element) Object
  = "('Object, ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element option) RElement_ext + 'Node) Object"
register_default_tvars 
  "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Object, 'Node, 'Element) Object"

type_synonym
  ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 'shadow_root_ptr, 'Object, 'Node, 'Element) heap
  = "('document_ptr document_ptr + 'shadow_root_ptr shadow_root_ptr + 'object_ptr, 'element_ptr element_ptr + 'character_data_ptr character_data_ptr + 'node_ptr, 'Object,
      ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Element option) RElement_ext + 'Node) heap" 
register_default_tvars
  "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 'shadow_root_ptr, 'Object, 'Node, 'Element) heap" 

definition element_ptr_kinds :: "(_) heap \<Rightarrow> (_) element_ptr fset"
  where
    "element_ptr_kinds heap = the |`| (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |`| (ffilter is_element_ptr_kind (node_ptr_kinds heap)))"

lemma element_ptr_kinds_simp [simp]: 
  "element_ptr_kinds (Heap (fmupd (cast element_ptr) element (the_heap h))) = {|element_ptr|} |\<union>| element_ptr_kinds h"
  apply(auto simp add: element_ptr_kinds_def)[1]
  by force

definition element_ptrs :: "(_) heap \<Rightarrow> (_) element_ptr fset"
  where
    "element_ptrs heap = ffilter is_element_ptr (element_ptr_kinds heap)"

definition cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(_) Node \<Rightarrow> (_) Element option"
  where
    "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t node = (case RNode.more node of Inl element \<Rightarrow> Some (RNode.extend (RNode.truncate node) element) | _ \<Rightarrow> None)"
adhoc_overloading cast cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t

abbreviation cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(_) Object \<Rightarrow> (_) Element option"
  where
    "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t obj \<equiv> (case cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e obj of Some node \<Rightarrow> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t node | None \<Rightarrow> None)"
adhoc_overloading cast cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t

definition cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) Element \<Rightarrow> (_) Node"
  where
    "cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element = RNode.extend (RNode.truncate element) (Inl (RNode.more element))"
adhoc_overloading cast cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e

abbreviation cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) Element \<Rightarrow> (_) Object"
  where
    "cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr \<equiv> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr)"
adhoc_overloading cast cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

consts is_element_kind :: 'a
definition is_element_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) Node \<Rightarrow> bool"
  where
    "is_element_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr \<longleftrightarrow> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr \<noteq> None"

adhoc_overloading is_element_kind is_element_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e
lemmas is_element_kind_def = is_element_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def

abbreviation is_element_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) Object \<Rightarrow> bool"
  where
    "is_element_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr \<equiv> cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr \<noteq> None"
adhoc_overloading is_element_kind is_element_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

lemma element_ptr_kinds_commutes [simp]: 
  "cast element_ptr |\<in>| node_ptr_kinds h \<longleftrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  apply(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)[1]
  by (metis (no_types, lifting) element_ptr_casts_commute2 ffmember_filter fimage_eqI 
      fset.map_comp is_element_ptr_kind_none node_ptr_casts_commute3 
      node_ptr_kinds_commutes node_ptr_kinds_def option.sel option.simps(3))

definition get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(_) element_ptr \<Rightarrow> (_) heap \<Rightarrow> (_) Element option"
  where                             
    "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr h = Option.bind (get\<^sub>N\<^sub>o\<^sub>d\<^sub>e (cast element_ptr) h) cast"
adhoc_overloading get get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t

locale l_type_wf_def\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
definition a_type_wf :: "(_) heap \<Rightarrow> bool"
  where
    "a_type_wf h = (NodeClass.type_wf h \<and> (\<forall>element_ptr. element_ptr |\<in>| element_ptr_kinds h 
                                             \<longrightarrow> get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr h \<noteq> None))"
end
global_interpretation l_type_wf_def\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t defines type_wf = a_type_wf .
lemmas type_wf_defs = a_type_wf_def

locale l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t = l_type_wf type_wf for type_wf :: "((_) heap \<Rightarrow> bool)" +
  assumes type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t: "type_wf h \<Longrightarrow> ElementClass.type_wf h"

sublocale l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t \<subseteq> l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
  apply(unfold_locales)
  using NodeClass.a_type_wf_def
  by (meson ElementClass.a_type_wf_def l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_axioms l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)

locale l_get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas = l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
sublocale l_get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas by unfold_locales

lemma get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf:
  assumes "type_wf h"
  shows "element_ptr |\<in>| element_ptr_kinds h \<longleftrightarrow> get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr h \<noteq> None"
  using l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_axioms assms
  apply(simp add: type_wf_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)
  by (metis NodeClass.get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf bind_eq_None_conv element_ptr_kinds_commutes 
      option.distinct(1))
end

global_interpretation l_get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas type_wf
  by unfold_locales

definition put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(_) element_ptr \<Rightarrow> (_) Element \<Rightarrow> (_) heap \<Rightarrow> (_) heap"
  where                                     
    "put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr element = put\<^sub>N\<^sub>o\<^sub>d\<^sub>e (cast element_ptr) (cast element)"
adhoc_overloading put put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t      

lemma put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap:
  assumes "put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr element h = h'"
  shows "element_ptr |\<in>| element_ptr_kinds h'"
  using assms
  unfolding put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def element_ptr_kinds_def
  by (metis element_ptr_kinds_commutes element_ptr_kinds_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ptr_in_heap)

lemma put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_put_ptrs:
  assumes "put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr element h = h'"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast element_ptr|}"
  using assms
  by (simp add: put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_put_ptrs)



lemma cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inject [simp]: 
  "cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e x = cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e y \<longleftrightarrow> x = y"
  apply(simp add: cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def)
  by (metis (full_types) RNode.surjective old.unit.exhaust)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none [simp]: 
  "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t node = None \<longleftrightarrow> \<not> (\<exists>element. cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element = node)"
  apply(auto simp add: cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def 
      split: sum.splits)[1]
  by (metis (full_types) RNode.select_convs(2) RNode.surjective old.unit.exhaust)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_some [simp]: 
  "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t node = Some element \<longleftrightarrow> cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element = node"
  by(auto simp add: cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def 
      split: sum.splits)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_inv [simp]: "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t (cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element) = Some element"
  by simp

lemma get_elment_ptr_simp1 [simp]: 
  "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr (put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr element h) = Some element"
  by(auto simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)
lemma get_elment_ptr_simp2 [simp]: 
  "element_ptr \<noteq> element_ptr' 
  \<Longrightarrow> get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr (put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr' element h) = get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr h"
  by(auto simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)


abbreviation "create_element_obj tag_type_arg child_nodes_arg attrs_arg shadow_root_opt_arg
  \<equiv> \<lparr> RObject.nothing = (), RNode.nothing = (), RElement.nothing = (),
      tag_type = tag_type_arg, Element.child_nodes = child_nodes_arg, attrs = attrs_arg,
      shadow_root_opt = shadow_root_opt_arg, \<dots> = None \<rparr>"

definition new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t :: "(_) heap \<Rightarrow> ((_) element_ptr \<times> (_) heap)"
  where
    "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = 
      (let new_element_ptr = element_ptr.Ref (Suc (fMax (finsert 0 (element_ptr.the_ref 
                                 |`| (element_ptrs h))))) 
       in
      (new_element_ptr, put new_element_ptr (create_element_obj '''' [] fmempty None) h))"

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  shows "new_element_ptr |\<in>| element_ptr_kinds h'"
  using assms
  unfolding new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def
  using put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap by blast

lemma new_element_ptr_new: 
  "element_ptr.Ref (Suc (fMax (finsert 0 (element_ptr.the_ref |`| element_ptrs h)))) |\<notin>| element_ptrs h"
  by (metis Suc_n_not_le_n element_ptr.sel(1) fMax_ge fimage_finsert finsertI1 finsertI2 set_finsert)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  shows "new_element_ptr |\<notin>| element_ptr_kinds h"
  using assms
  unfolding new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
  by (metis Pair_inject element_ptrs_def ffmember_filter new_element_ptr_new is_element_ptr_ref)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_new_ptr:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
  using assms
  by (metis Pair_inject new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_put_ptrs)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_is_element_ptr:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  shows "is_element_ptr new_element_ptr"
  using assms
  by(auto simp add: new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t [simp]:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  assumes "ptr \<noteq> cast new_element_ptr"
  shows "get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h'"
  using assms
  by(auto simp add: new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_get\<^sub>N\<^sub>o\<^sub>d\<^sub>e [simp]:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  assumes "ptr \<noteq> cast new_element_ptr"
  shows "get\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr h = get\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr h'"
  using assms
  by(auto simp add: new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t [simp]:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  assumes "ptr \<noteq> new_element_ptr"
  shows "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr h = get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr h'"
  using assms
  by(auto simp add: new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def)


locale l_known_ptr\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
definition a_known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  where
    "a_known_ptr ptr = (known_ptr ptr \<or> is_element_ptr ptr)"

lemma known_ptr_not_element_ptr: "\<not>is_element_ptr ptr \<Longrightarrow> a_known_ptr ptr \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptr_def)
end
global_interpretation l_known_ptr\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t defines known_ptr = a_known_ptr .
lemmas known_ptr_defs = a_known_ptr_def


locale l_known_ptrs\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t = l_known_ptr known_ptr for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
begin
definition a_known_ptrs :: "(_) heap \<Rightarrow> bool"
  where
    "a_known_ptrs h = (\<forall>ptr. ptr |\<in>| object_ptr_kinds h \<longrightarrow> known_ptr ptr)"

lemma known_ptrs_known_ptr: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> a_known_ptrs h \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptrs_def)

lemma known_ptrs_preserved: "object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> a_known_ptrs h = a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
lemma known_ptrs_subset: "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h \<Longrightarrow> a_known_ptrs h \<Longrightarrow> a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
end
global_interpretation l_known_ptrs\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t known_ptr defines known_ptrs = a_known_ptrs .
lemmas known_ptrs_defs = a_known_ptrs_def

lemma known_ptrs_is_l_known_ptrs: "l_known_ptrs known_ptr known_ptrs"
  using known_ptrs_known_ptr known_ptrs_preserved l_known_ptrs_def known_ptrs_subset by blast

end
