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

section\<open>CharacterData\<close>
text\<open>In this theory, we introduce the types for the CharacterData class.\<close>
theory CharacterDataClass
  imports
    ElementClass
begin

subsubsection\<open>CharacterData\<close>

text\<open>The type @{type "DOMString"} is a type synonym for @{type "string"}, defined 
     \autoref{sec:Core_DOM_Basic_Datatypes}.\<close>

record RCharacterData = RNode +
  nothing :: unit
  val :: DOMString
register_default_tvars "'CharacterData RCharacterData_ext" 
type_synonym 'CharacterData CharacterData = "'CharacterData option RCharacterData_scheme"
register_default_tvars "'CharacterData CharacterData" 
type_synonym ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Node, 
    'Element, 'CharacterData) Node
  = "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 
      'CharacterData option RCharacterData_ext + 'Node, 'Element) Node"
register_default_tvars "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Node, 
                         'Element, 'CharacterData) Node" 
type_synonym ('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Object, 'Node, 
    'Element, 'CharacterData) Object
  = "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Object, 
      'CharacterData option RCharacterData_ext + 'Node,
      'Element) Object"
register_default_tvars "('node_ptr, 'element_ptr, 'character_data_ptr, 'shadow_root_ptr, 'Object, 
                         'Node, 'Element, 'CharacterData) Object" 

type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
    'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData) heap
  = "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 'shadow_root_ptr, 
      'Object, 'CharacterData option RCharacterData_ext + 'Node, 'Element) heap"
register_default_tvars "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
                         'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData) heap"  


definition character_data_ptr_kinds :: "(_) heap \<Rightarrow> (_) character_data_ptr fset"
  where                                                                                           
    "character_data_ptr_kinds heap = the |`| (cast |`| (ffilter is_character_data_ptr_kind 
                                                                (node_ptr_kinds heap)))"

lemma character_data_ptr_kinds_simp [simp]:
  "character_data_ptr_kinds (Heap (fmupd (cast character_data_ptr) character_data (the_heap h))) 
              = {|character_data_ptr|} |\<union>| character_data_ptr_kinds h"
  apply(auto simp add: character_data_ptr_kinds_def)[1]
  by force

definition character_data_ptrs :: "(_) heap \<Rightarrow> _ character_data_ptr fset"
  where
    "character_data_ptrs heap = ffilter is_character_data_ptr (character_data_ptr_kinds heap)"

abbreviation "character_data_ptr_exts heap \<equiv> character_data_ptr_kinds heap - character_data_ptrs heap"

definition cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a :: "(_) Node \<Rightarrow> (_) CharacterData option"
  where
    "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a node = (case RNode.more node of
          Inr (Inl character_data) \<Rightarrow> Some (RNode.extend (RNode.truncate node) character_data)
        | _ \<Rightarrow> None)"
adhoc_overloading cast cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a

abbreviation cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a :: "(_) Object \<Rightarrow> (_) CharacterData  option"
  where
    "cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a obj \<equiv> (case cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e obj of Some node \<Rightarrow> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a node 
                                                       | None \<Rightarrow> None)"
adhoc_overloading cast cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a

definition cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) CharacterData \<Rightarrow> (_) Node"
  where
    "cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data = RNode.extend (RNode.truncate character_data)
                                                      (Inr (Inl (RNode.more character_data)))"
adhoc_overloading cast cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e

abbreviation cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) CharacterData \<Rightarrow> (_) Object"
  where
    "cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr \<equiv> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr)"
adhoc_overloading cast cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

consts is_character_data_kind :: 'a
definition is_character_data_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e :: "(_) Node \<Rightarrow> bool"
  where
    "is_character_data_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr \<longleftrightarrow> cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr \<noteq> None"

adhoc_overloading is_character_data_kind is_character_data_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e
lemmas is_character_data_kind_def = is_character_data_kind\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def

abbreviation is_character_data_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "(_) Object \<Rightarrow> bool"
  where
    "is_character_data_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr \<equiv> cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr \<noteq> None"
adhoc_overloading is_character_data_kind is_character_data_kind\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

lemma character_data_ptr_kinds_commutes [simp]:
  "cast character_data_ptr |\<in>| node_ptr_kinds h 
       \<longleftrightarrow> character_data_ptr |\<in>| character_data_ptr_kinds h"
  apply(auto simp add: character_data_ptr_kinds_def)[1]
  by (metis character_data_ptr_casts_commute2 comp_eq_dest_lhs ffmember_filter fimage_eqI 
      is_character_data_ptr_kind_none
      option.distinct(1) option.sel)

definition get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a :: "(_) character_data_ptr \<Rightarrow> (_) heap \<Rightarrow> (_) CharacterData option"
  where                             
    "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr h = Option.bind (get\<^sub>N\<^sub>o\<^sub>d\<^sub>e (cast character_data_ptr) h) cast"
adhoc_overloading get get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a

locale l_type_wf_def\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
begin
definition a_type_wf :: "(_) heap \<Rightarrow> bool"
  where
    "a_type_wf h = (ElementClass.type_wf h
                 \<and> (\<forall>character_data_ptr. character_data_ptr |\<in>| character_data_ptr_kinds h 
                 \<longrightarrow> get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr h \<noteq> None))"
end
global_interpretation l_type_wf_def\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a defines type_wf = a_type_wf .
lemmas type_wf_defs = a_type_wf_def

locale l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a = l_type_wf type_wf for type_wf :: "((_) heap \<Rightarrow> bool)" +
  assumes type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a: "type_wf h \<Longrightarrow> CharacterDataClass.type_wf h"

sublocale l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a \<subseteq> l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
  apply(unfold_locales)
  using ElementClass.a_type_wf_def
  by (meson CharacterDataClass.a_type_wf_def l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_axioms l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)

locale l_get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas = l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
begin
sublocale l_get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas by unfold_locales

lemma get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_type_wf:
  assumes "type_wf h"
  shows "character_data_ptr |\<in>| character_data_ptr_kinds h 
          \<longleftrightarrow> get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr h \<noteq> None"
  using l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_axioms assms
  apply(simp add: type_wf_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)
  by (metis NodeClass.get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf bind_eq_None_conv character_data_ptr_kinds_commutes 
      l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def local.l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e_axioms option.distinct(1))
end

global_interpretation l_get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas type_wf
  by unfold_locales

definition put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a :: "(_) character_data_ptr \<Rightarrow> (_) CharacterData \<Rightarrow> (_) heap \<Rightarrow> (_) heap"
  where
    "put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr character_data = put\<^sub>N\<^sub>o\<^sub>d\<^sub>e (cast character_data_ptr) 
                   (cast character_data)"
adhoc_overloading put put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a

lemma put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_in_heap:
  assumes "put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr character_data h = h'"
  shows "character_data_ptr |\<in>| character_data_ptr_kinds h'"
  using assms put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ptr_in_heap
  unfolding put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def character_data_ptr_kinds_def
  by (metis character_data_ptr_kinds_commutes character_data_ptr_kinds_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ptr_in_heap)

lemma put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_put_ptrs:
  assumes "put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr character_data h = h'"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast character_data_ptr|}"
  using assms
  by (simp add: put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_put_ptrs)


lemma cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inject [simp]: "cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e x = cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e y \<longleftrightarrow> x = y"
  apply(simp add: cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def)
  by (metis (full_types) RNode.surjective old.unit.exhaust)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_none [simp]:
  "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a node = None \<longleftrightarrow> \<not> (\<exists>character_data. cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data = node)"
  apply(auto simp add: cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def 
      split: sum.splits)[1]
  by (metis (full_types) RNode.select_convs(2) RNode.surjective old.unit.exhaust)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_some [simp]: 
  "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a node = Some character_data \<longleftrightarrow> cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data = node"
  by(auto simp add: cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RObject.extend_def RNode.extend_def 
      split: sum.splits)

lemma cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_inv [simp]: 
  "cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a (cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data) = Some character_data"
  by simp

lemma cast_element_not_character_data [simp]:
  "(cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element \<noteq> cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data)"
  "(cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e character_data \<noteq> cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e element)"
  by(auto simp add: cast\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def cast\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def RNode.extend_def)

lemma get_CharacterData_simp1 [simp]: 
  "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr (put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr character_data h) 
       = Some character_data"
  by(auto simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)
lemma get_CharacterData_simp2 [simp]: 
  "character_data_ptr \<noteq> character_data_ptr' \<Longrightarrow> get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr 
         (put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr' character_data h) = get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr h"
  by(auto simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)

lemma get_CharacterData_simp3 [simp]: 
  "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr (put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr f h) = get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr h"
  by(auto simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)
lemma get_CharacterData_simp4 [simp]: 
  "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a element_ptr (put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t character_data_ptr f h) = get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a element_ptr h"
  by(auto simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)

lemma new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a [simp]:
  assumes "new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h = (new_element_ptr, h')"
  shows "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr h = get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr h'"
  using assms
  by(auto simp add: new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def)



abbreviation "create_character_data_obj val_arg
  \<equiv> \<lparr> RObject.nothing = (), RNode.nothing = (), RCharacterData.nothing = (), val = val_arg, \<dots> = None \<rparr>"

definition new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a :: "(_) heap \<Rightarrow> ((_) character_data_ptr \<times> (_) heap)"
  where
    "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h =
      (let new_character_data_ptr = character_data_ptr.Ref (Suc (fMax (character_data_ptr.the_ref 
            |`| (character_data_ptrs h)))) in
        (new_character_data_ptr, put new_character_data_ptr (create_character_data_obj '''') h))"

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_in_heap:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  shows "new_character_data_ptr |\<in>| character_data_ptr_kinds h'"
  using assms
  unfolding new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def
  using put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_in_heap by blast

lemma new_character_data_ptr_new: 
  "character_data_ptr.Ref (Suc (fMax (finsert 0 (character_data_ptr.the_ref |`| character_data_ptrs h)))) 
              |\<notin>| character_data_ptrs h"
  by (metis Suc_n_not_le_n character_data_ptr.sel(1) fMax_ge fimage_finsert finsertI1 finsertI2 set_finsert)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_not_in_heap:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  shows "new_character_data_ptr |\<notin>| character_data_ptr_kinds h"
  using assms
  unfolding new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def
  by (metis Pair_inject character_data_ptrs_def fMax_finsert fempty_iff ffmember_filter fimage_is_fempty is_character_data_ptr_ref max_0L new_character_data_ptr_new)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_new_ptr:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
  using assms
  by (metis Pair_inject new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_put_ptrs)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_is_character_data_ptr:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  shows "is_character_data_ptr new_character_data_ptr"
  using assms
  by(auto simp add: new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t [simp]:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  assumes "ptr \<noteq> cast new_character_data_ptr"
  shows "get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr h'"
  using assms
  by(auto simp add: new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_get\<^sub>N\<^sub>o\<^sub>d\<^sub>e [simp]:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  assumes "ptr \<noteq> cast new_character_data_ptr"
  shows "get\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr h = get\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr h'"
  using assms
  by(auto simp add: new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t [simp]:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  shows "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr h = get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr h'"
  using assms
  by(auto simp add: new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def)

lemma new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a [simp]:
  assumes "new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h = (new_character_data_ptr, h')"
  assumes "ptr \<noteq> new_character_data_ptr"
  shows "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr h = get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr h'"
  using assms
  by(auto simp add: new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def)


locale l_known_ptr\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
begin
definition a_known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  where
    "a_known_ptr ptr = (known_ptr ptr \<or> is_character_data_ptr ptr)"

lemma known_ptr_not_character_data_ptr: 
  "\<not>is_character_data_ptr ptr \<Longrightarrow> a_known_ptr ptr \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptr_def)
end
global_interpretation l_known_ptr\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a defines known_ptr = a_known_ptr .
lemmas known_ptr_defs = a_known_ptr_def


locale l_known_ptrs\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a = l_known_ptr known_ptr for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
begin
definition a_known_ptrs :: "(_) heap \<Rightarrow> bool"
  where
    "a_known_ptrs h = (\<forall>ptr. ptr |\<in>| object_ptr_kinds h \<longrightarrow> known_ptr ptr)"

lemma known_ptrs_known_ptr: "a_known_ptrs h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptr ptr"
  by(simp add: a_known_ptrs_def)

lemma known_ptrs_preserved: 
  "object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> a_known_ptrs h = a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
lemma known_ptrs_subset: 
  "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h \<Longrightarrow> a_known_ptrs h \<Longrightarrow> a_known_ptrs h'"
  by(auto simp add: a_known_ptrs_def)
end
global_interpretation l_known_ptrs\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a known_ptr defines known_ptrs = a_known_ptrs .
lemmas known_ptrs_defs = a_known_ptrs_def

lemma known_ptrs_is_l_known_ptrs: "l_known_ptrs known_ptr known_ptrs"
  using known_ptrs_known_ptr known_ptrs_preserved l_known_ptrs_def known_ptrs_subset
  by blast

end
