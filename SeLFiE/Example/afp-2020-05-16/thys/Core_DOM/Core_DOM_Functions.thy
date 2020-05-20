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

section\<open>Querying and Modifying the DOM\<close>
text\<open>In this theory, we are formalizing the functions for querying and modifying 
the DOM.\<close>

theory Core_DOM_Functions
imports
  "monads/DocumentMonad"
begin

text \<open>If we do not declare show\_variants, then all abbreviations that contain
  constants that are overloaded by using adhoc\_overloading get immediately unfolded.\<close>
declare [[show_variants]]

subsection \<open>Various Functions\<close>

lemma insort_split: "x \<in> set (insort y xs) \<longleftrightarrow> (x = y \<or> x \<in> set xs)"
  apply(induct xs)
  by(auto)

lemma concat_map_distinct: 
  "distinct (concat (map f xs)) \<Longrightarrow> y \<in> set (concat (map f xs)) \<Longrightarrow> \<exists>!x \<in> set xs. y \<in> set (f x)"
  apply(induct xs) 
  by(auto)

lemma concat_map_all_distinct: "distinct (concat (map f xs)) \<Longrightarrow> x \<in> set xs \<Longrightarrow> distinct (f x)"
  apply(induct xs)
  by(auto)

lemma distinct_concat_map_I:
  assumes "distinct xs"
    and "\<And>x. x \<in> set xs \<Longrightarrow> distinct (f x)"
and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> (set (f x)) \<inter> (set (f y)) = {}"
shows "distinct (concat ((map f xs)))"
  using assms
  apply(induct xs) 
  by(auto)

lemma distinct_concat_map_E:
  assumes "distinct (concat ((map f xs)))"
  shows "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> (set (f x)) \<inter> (set (f y)) = {}"
    and "\<And>x. x \<in> set xs \<Longrightarrow> distinct (f x)"
  using assms
  apply(induct xs) 
  by(auto)

lemma bind_is_OK_E3 [elim]:
  assumes "h \<turnstile> ok (f \<bind> g)" and "pure f h"
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x"  and "h \<turnstile> ok (g x)"
  using assms 
  by(auto simp add: bind_def returns_result_def returns_heap_def is_OK_def execute_def pure_def
               split: sum.splits)


subsection \<open>Basic Functions\<close>

subsubsection \<open>get\_child\_nodes\<close>

locale l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin

definition get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) element_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr _ = get_M element_ptr RElement.child_nodes"

definition get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) character_data_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r _ _ = return []"

definition get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) document_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr _ = do {
    doc_elem \<leftarrow> get_M document_ptr document_element;
    (case doc_elem of
      Some element_ptr \<Rightarrow> return [cast element_ptr]
    | None \<Rightarrow> return [])
  }"

definition a_get_child_nodes_tups :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> unit
  \<Rightarrow> (_, (_) node_ptr list) dom_prog)) list"
  where
    "a_get_child_nodes_tups = [
        (is_element_ptr, get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_character_data_ptr, get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_document_ptr, get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)
     ]"

definition a_get_child_nodes :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "a_get_child_nodes ptr = invoke a_get_child_nodes_tups ptr ()"

definition a_get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_child_nodes_locs ptr \<equiv> 
      (if is_element_ptr_kind ptr then {preserved (get_M (the (cast ptr)) RElement.child_nodes)} else {}) \<union>
      (if is_document_ptr_kind ptr then {preserved (get_M (the (cast ptr)) RDocument.document_element)} else {}) \<union>
      {preserved (get_M ptr RObject.nothing)}"

definition first_child :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr option) dom_prog"
  where
    "first_child ptr = do {
      children \<leftarrow> a_get_child_nodes ptr;
      return (case children of [] \<Rightarrow> None | child#_ \<Rightarrow> Some child)}"
end

locale l_get_child_nodes_defs =
  fixes get_child_nodes :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  fixes get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_known_ptr known_ptr + 
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes known_ptr_impl: "known_ptr = DocumentClass.known_ptr"
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes get_child_nodes_impl: "get_child_nodes = a_get_child_nodes"
  assumes get_child_nodes_locs_impl: "get_child_nodes_locs = a_get_child_nodes_locs"
begin
lemmas get_child_nodes_def = get_child_nodes_impl[unfolded a_get_child_nodes_def]
lemmas get_child_nodes_locs_def = get_child_nodes_locs_impl[unfolded a_get_child_nodes_locs_def]

lemma get_child_nodes_split:
  "P (invoke (a_get_child_nodes_tups @ xs) ptr ()) =
    ((known_ptr ptr \<longrightarrow> P (get_child_nodes ptr))
    \<and> (\<not>(known_ptr ptr) \<longrightarrow> P (invoke xs ptr ())))"
  by(auto simp add: known_ptr_impl get_child_nodes_impl a_get_child_nodes_def a_get_child_nodes_tups_def 
                     known_ptr_defs CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs 
                     NodeClass.known_ptr_defs 
          split: invoke_splits)

lemma get_child_nodes_split_asm:
  "P (invoke (a_get_child_nodes_tups @ xs) ptr ()) =
    (\<not>((known_ptr ptr \<and> \<not>P (get_child_nodes ptr))
    \<or> (\<not>(known_ptr ptr) \<and> \<not>P (invoke xs ptr ()))))"
  by(auto simp add: known_ptr_impl get_child_nodes_impl a_get_child_nodes_def 
                    a_get_child_nodes_tups_def known_ptr_defs CharacterDataClass.known_ptr_defs 
                    ElementClass.known_ptr_defs NodeClass.known_ptr_defs 
          split: invoke_splits)

lemmas get_child_nodes_splits = get_child_nodes_split get_child_nodes_split_asm

lemma get_child_nodes_ok [simp]:
  assumes "known_ptr ptr"
  assumes "type_wf h"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_child_nodes ptr)"
  using assms(1) assms(2) assms(3)
  apply(auto simp add:  known_ptr_impl type_wf_impl get_child_nodes_def a_get_child_nodes_tups_def)[1]
  apply(split invoke_splits, rule conjI)+
     apply((rule impI)+, drule(1) known_ptr_not_document_ptr, drule(1) known_ptr_not_character_data_ptr, 
                         drule(1) known_ptr_not_element_ptr)
     apply(auto simp add: NodeClass.known_ptr_defs)[1]
    apply(auto simp add: get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def dest: get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok 
               split: list.splits option.splits intro!: bind_is_OK_I2)[1]
   apply(auto simp add: get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)[1]                                                    
  apply (auto simp add: get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def  CharacterDataClass.type_wf_defs 
                        DocumentClass.type_wf_defs intro!: bind_is_OK_I2 split: option.splits)[1]
  using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok \<open>type_wf h\<close>[unfolded type_wf_impl] by blast

lemma get_child_nodes_ptr_in_heap [simp]:
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: get_child_nodes_impl a_get_child_nodes_def invoke_ptr_in_heap 
          dest: is_OK_returns_result_I)

lemma get_child_nodes_pure [simp]:
  "pure (get_child_nodes ptr) h"
  apply (auto simp add: get_child_nodes_impl a_get_child_nodes_def a_get_child_nodes_tups_def)[1]
  apply(split invoke_splits, rule conjI)+
  by(auto simp add: get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
                   get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_I split: option.splits)

lemma get_child_nodes_reads: "reads (get_child_nodes_locs ptr) (get_child_nodes ptr) h h'"
  apply(simp add: get_child_nodes_locs_impl get_child_nodes_impl a_get_child_nodes_def 
      a_get_child_nodes_tups_def a_get_child_nodes_locs_def) 
  apply(split invoke_splits, rule conjI)+
     apply(auto)[1] 
    apply(auto simp add: get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro: reads_subset[OF reads_singleton] 
      reads_subset[OF check_in_heap_reads]  
      intro!: reads_bind_pure  reads_subset[OF return_reads] split: option.splits)[1] (* slow: ca 1min *)
   apply(auto simp add: get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro: reads_subset[OF check_in_heap_reads] 
      intro!: reads_bind_pure  reads_subset[OF return_reads] )[1]
  apply(auto simp add: get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro: reads_subset[OF reads_singleton] 
      reads_subset[OF check_in_heap_reads] intro!: reads_bind_pure  reads_subset[OF return_reads] 
      split: option.splits)
  done
end

locale l_get_child_nodes = l_type_wf + l_known_ptr + l_get_child_nodes_defs +
  assumes get_child_nodes_reads: "reads (get_child_nodes_locs ptr) (get_child_nodes ptr) h h'"
  assumes get_child_nodes_ok: "type_wf h \<Longrightarrow> known_ptr ptr \<Longrightarrow> ptr |\<in>| object_ptr_kinds h 
                                         \<Longrightarrow> h \<turnstile> ok (get_child_nodes ptr)"
  assumes get_child_nodes_ptr_in_heap: "h \<turnstile> ok (get_child_nodes ptr) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  assumes get_child_nodes_pure [simp]: "pure (get_child_nodes ptr) h"

global_interpretation l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  get_child_nodes = l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_child_nodes and
  get_child_nodes_locs = l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_child_nodes_locs
  .

interpretation
  i_get_child_nodes?: l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  by(auto simp add: l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def get_child_nodes_def get_child_nodes_locs_def)
declare l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_child_nodes_is_l_get_child_nodes [instances]: 
  "l_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  apply(unfold_locales)
  using get_child_nodes_reads get_child_nodes_ok get_child_nodes_ptr_in_heap get_child_nodes_pure
  by blast+


paragraph \<open>new\_element\<close>

locale l_new_element_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_child_nodes_new_element: 
  "ptr' \<noteq> cast new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_child_nodes_locs_def new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_element_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t 
                     new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t split: prod.splits if_splits option.splits 
           elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)

lemma new_element_no_child_nodes:
  "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def a_get_child_nodes_tups_def 
      split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)[1]
  apply(split invoke_splits, rule conjI)+
     apply(auto intro: new_element_is_element_ptr)[1]
  by(auto simp add: new_element_ptr_in_heap get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def check_in_heap_def 
      new_element_child_nodes intro!: bind_pure_returns_result_I 
      intro: new_element_is_element_ptr elim!: new_element_ptr_in_heap)
end

locale l_new_element_get_child_nodes = l_new_element + l_get_child_nodes +
  assumes get_child_nodes_new_element:  
          "ptr' \<noteq> cast new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr 
            \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
        assumes new_element_no_child_nodes: 
          "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' 
            \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"

interpretation i_new_element_get_child_nodes?:
  l_new_element_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  by(unfold_locales)
declare l_new_element_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_element_get_child_nodes_is_l_new_element_get_child_nodes [instances]: 
  "l_new_element_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  using new_element_is_l_new_element get_child_nodes_is_l_get_child_nodes
  apply(auto simp add: l_new_element_get_child_nodes_def l_new_element_get_child_nodes_axioms_def)[1]
  using get_child_nodes_new_element new_element_no_child_nodes
  by fast+


paragraph \<open>new\_character\_data\<close>

locale l_new_character_data_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_child_nodes_new_character_data: 
  "ptr' \<noteq> cast new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
   \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_child_nodes_locs_def new_character_data_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t 
                     new_character_data_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t new_character_data_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t 
           split: prod.splits if_splits option.splits 
           elim!: bind_returns_result_E bind_returns_heap_E 
           intro: is_character_data_ptr_kind_obtains)

lemma new_character_data_no_child_nodes:
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def a_get_child_nodes_tups_def 
             split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)[1]
  apply(split invoke_splits, rule conjI)+
     apply(auto intro: new_character_data_is_character_data_ptr)[1]
  by(auto simp add: new_character_data_ptr_in_heap get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
                    check_in_heap_def new_character_data_child_nodes 
          intro!: bind_pure_returns_result_I 
          intro: new_character_data_is_character_data_ptr elim!: new_character_data_ptr_in_heap)
end

locale l_new_character_data_get_child_nodes = l_new_character_data + l_get_child_nodes +
  assumes get_child_nodes_new_character_data:  
   "ptr' \<noteq> cast new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
       \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
 assumes new_character_data_no_child_nodes: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' 
       \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []"

interpretation i_new_character_data_get_child_nodes?:
  l_new_character_data_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  by(unfold_locales)
declare l_new_character_data_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_character_data_get_child_nodes_is_l_new_character_data_get_child_nodes [instances]: 
  "l_new_character_data_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  using new_character_data_is_l_new_character_data get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_new_character_data_get_child_nodes_def l_new_character_data_get_child_nodes_axioms_def)
  using get_child_nodes_new_character_data new_character_data_no_child_nodes
  by fast



paragraph \<open>new\_document\<close>

locale l_new_document_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_child_nodes_new_document: 
  "ptr' \<noteq> cast new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
     \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_child_nodes_locs_def new_document_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_document_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
                     new_document_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t split: prod.splits if_splits option.splits 
           elim!: bind_returns_result_E bind_returns_heap_E 
           intro: is_document_ptr_kind_obtains)

lemma new_document_no_child_nodes:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def a_get_child_nodes_tups_def 
      split: prod.splits 
      elim!: bind_returns_result_E bind_returns_heap_E)[1]
  apply(split invoke_splits, rule conjI)+
     apply(auto intro: new_document_is_document_ptr)[1]
  by(auto simp add: new_document_ptr_in_heap get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def check_in_heap_def 
      new_document_document_element 
      intro!: bind_pure_returns_result_I 
      intro: new_document_is_document_ptr elim!: new_document_ptr_in_heap split: option.splits)
end

locale l_new_document_get_child_nodes = l_new_document + l_get_child_nodes +
  assumes get_child_nodes_new_document:  
   "ptr' \<noteq> cast new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
     \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
 assumes new_document_no_child_nodes: 
   "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []"

interpretation i_new_document_get_child_nodes?:
  l_new_document_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  by(unfold_locales)
declare l_new_document_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_document_get_child_nodes_is_l_new_document_get_child_nodes [instances]: 
  "l_new_document_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  using new_document_is_l_new_document get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_new_document_get_child_nodes_def l_new_document_get_child_nodes_axioms_def)
  using get_child_nodes_new_document new_document_no_child_nodes
  by fast

subsubsection \<open>set\_child\_nodes\<close>

locale l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition set_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: 
  "(_) element_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
  "set_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr children = put_M element_ptr RElement.child_nodes_update children"

definition set_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: 
  "(_) character_data_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
    "set_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r _ _ =  error HierarchyRequestError"

definition set_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
    "set_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr children = do {
      (case children of
        [] \<Rightarrow> put_M document_ptr document_element_update None
      | child # [] \<Rightarrow> (case cast child of
          Some element_ptr \<Rightarrow> put_M document_ptr document_element_update (Some element_ptr)
        | None \<Rightarrow> error HierarchyRequestError)
      | _ \<Rightarrow> error HierarchyRequestError)
    }"

definition a_set_child_nodes_tups :: 
  "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog)) list"
  where
    "a_set_child_nodes_tups \<equiv> [
        (is_element_ptr, set_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_character_data_ptr, set_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_document_ptr, set_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)
     ]"

definition a_set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_child_nodes ptr children = invoke a_set_child_nodes_tups ptr (children)"
lemmas set_child_nodes_defs = a_set_child_nodes_def

definition a_set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_child_nodes_locs ptr \<equiv> 
      (if is_element_ptr_kind ptr 
          then all_args (put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t (the (cast ptr)) RElement.child_nodes_update) else {}) \<union>
      (if is_document_ptr_kind ptr 
          then all_args (put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t (the (cast ptr)) document_element_update) else {})"
end

locale l_set_child_nodes_defs =
  fixes set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  fixes set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_known_ptr known_ptr + 
  l_set_child_nodes_defs set_child_nodes set_child_nodes_locs +
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs 
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes known_ptr_impl: "known_ptr = DocumentClass.known_ptr"
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes set_child_nodes_impl: "set_child_nodes = a_set_child_nodes"
  assumes set_child_nodes_locs_impl: "set_child_nodes_locs = a_set_child_nodes_locs"
begin
lemmas set_child_nodes_def = set_child_nodes_impl[unfolded a_set_child_nodes_def]
lemmas set_child_nodes_locs_def = set_child_nodes_locs_impl[unfolded a_set_child_nodes_locs_def]

lemma set_child_nodes_split:
  "P (invoke (a_set_child_nodes_tups @ xs) ptr (children)) =
    ((known_ptr ptr \<longrightarrow> P (set_child_nodes ptr children))
    \<and> (\<not>(known_ptr ptr) \<longrightarrow> P (invoke xs ptr (children))))"
  by(auto simp add: known_ptr_impl set_child_nodes_impl a_set_child_nodes_def 
          a_set_child_nodes_tups_def known_ptr_defs CharacterDataClass.known_ptr_defs 
          ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: invoke_splits)

lemma set_child_nodes_split_asm:
  "P (invoke (a_set_child_nodes_tups @ xs) ptr (children)) =
    (\<not>((known_ptr ptr \<and> \<not>P (set_child_nodes ptr children))
    \<or> (\<not>(known_ptr ptr) \<and> \<not>P (invoke xs ptr (children)))))"
  by(auto simp add: known_ptr_impl set_child_nodes_impl a_set_child_nodes_def 
             a_set_child_nodes_tups_def known_ptr_defs CharacterDataClass.known_ptr_defs 
             ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: invoke_splits)[1]
lemmas set_child_nodes_splits = set_child_nodes_split set_child_nodes_split_asm

lemma set_child_nodes_writes: "writes (set_child_nodes_locs ptr) (set_child_nodes ptr children) h h'"
  apply(simp add: set_child_nodes_locs_impl set_child_nodes_impl a_set_child_nodes_def 
      a_set_child_nodes_tups_def a_set_child_nodes_locs_def)
  apply(split invoke_splits, rule conjI)+
     apply(auto)[1]
    apply(auto simp add: set_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: writes_bind_pure 
      intro: writes_union_right_I split: list.splits)[1] 
        apply(auto intro: writes_union_right_I split: option.splits)[1]
       apply(auto intro: writes_union_right_I split: option.splits)[1]
      apply(auto intro: writes_union_right_I split: option.splits)[1]
     apply(auto intro: writes_union_right_I split: option.splits)[1]
    apply(auto intro: writes_union_right_I split: option.splits)[1]
   apply(auto intro: writes_union_right_I split: option.splits)[1] (*slow: ca. 1min *)
  apply(auto simp add: set_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: writes_bind_pure)[1]
  apply(auto simp add: set_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro: writes_union_left_I 
      intro!: writes_bind_pure split: list.splits option.splits)[1]
  done

lemma set_child_nodes_pointers_preserved:
  assumes "w \<in> set_child_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: set_child_nodes_locs_impl all_args_def a_set_child_nodes_locs_def 
          split: if_splits)

lemma set_child_nodes_typess_preserved:
  assumes "w \<in> set_child_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: set_child_nodes_locs_impl type_wf_impl all_args_def a_set_child_nodes_locs_def
          split: if_splits)
end

locale l_set_child_nodes = l_type_wf + l_set_child_nodes_defs +
  assumes set_child_nodes_writes: 
   "writes (set_child_nodes_locs ptr) (set_child_nodes ptr children) h h'"
 assumes set_child_nodes_pointers_preserved: 
   "w \<in> set_child_nodes_locs object_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
 assumes set_child_nodes_types_preserved: 
   "w \<in> set_child_nodes_locs object_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

global_interpretation l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_child_nodes = l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_child_nodes and
  set_child_nodes_locs = l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_child_nodes_locs .

interpretation
  i_set_child_nodes?: l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr set_child_nodes set_child_nodes_locs
  apply(unfold_locales)
  by (auto simp add: set_child_nodes_def set_child_nodes_locs_def)
declare l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma set_child_nodes_is_l_set_child_nodes [instances]: 
  "l_set_child_nodes type_wf set_child_nodes set_child_nodes_locs"
  apply(unfold_locales)
  using set_child_nodes_pointers_preserved set_child_nodes_typess_preserved set_child_nodes_writes
  by blast+


paragraph \<open>get\_child\_nodes\<close>

locale l_set_child_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M + l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma set_child_nodes_get_child_nodes:
  assumes "known_ptr ptr"
  assumes "type_wf h"
  assumes "h \<turnstile> set_child_nodes ptr children \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
proof -
  have "h \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()"
    using assms set_child_nodes_impl[unfolded a_set_child_nodes_def] invoke_ptr_in_heap
    by (metis (full_types) check_in_heap_ptr_in_heap is_OK_returns_heap_I is_OK_returns_result_E 
        old.unit.exhaust)
  then have ptr_in_h: "ptr |\<in>| object_ptr_kinds h"
    by (simp add: check_in_heap_ptr_in_heap is_OK_returns_result_I)

  have "type_wf h'"
    apply(unfold type_wf_impl)
    apply(rule subst[where P=id, OF type_wf_preserved[OF set_child_nodes_writes assms(3), 
            unfolded all_args_def], simplified])
    by(auto simp add: all_args_def assms(2)[unfolded type_wf_impl] 
        set_child_nodes_locs_impl[unfolded a_set_child_nodes_locs_def]
        split: if_splits)
  have "h' \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()"
    using check_in_heap_reads set_child_nodes_writes assms(3) \<open>h \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()\<close> 
    apply(rule reads_writes_separate_forwards)
    by(auto simp add: all_args_def set_child_nodes_locs_impl[unfolded a_set_child_nodes_locs_def])
  then have "ptr |\<in>| object_ptr_kinds h'"
    using check_in_heap_ptr_in_heap by blast
  with assms ptr_in_h \<open>type_wf h'\<close> show ?thesis
    apply(auto simp add: get_child_nodes_impl set_child_nodes_impl type_wf_impl known_ptr_impl  
        a_get_child_nodes_def a_get_child_nodes_tups_def a_set_child_nodes_def 
        a_set_child_nodes_tups_def 
        del: bind_pure_returns_result_I2 
        intro!: bind_pure_returns_result_I2)[1]
    apply(split invoke_splits, rule conjI)
     apply(split invoke_splits, rule conjI)
      apply(split invoke_splits, rule conjI)
       apply(auto simp add: NodeClass.known_ptr_defs 
        dest!: known_ptr_not_document_ptr known_ptr_not_character_data_ptr 
        known_ptr_not_element_ptr)[1]                                                                                                                             
      apply(auto simp add: NodeClass.known_ptr_defs 
        dest!: known_ptr_not_document_ptr known_ptr_not_character_data_ptr 
        known_ptr_not_element_ptr)[1]                                                                                                                             
      apply(auto simp add: get_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def set_child_nodes\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
        split: list.splits option.splits 
        intro!: bind_pure_returns_result_I2 
        dest: get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok; auto dest: returns_result_eq 
        dest!: document_put_get[where getter = document_element])[1] (* slow, ca 1min *)
     apply(auto simp add: get_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def set_child_nodes\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)[1]
    by(auto simp add: get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def set_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def dest: element_put_get)
qed

lemma set_child_nodes_get_child_nodes_different_pointers: 
  assumes "ptr \<noteq> ptr'"
  assumes "w \<in> set_child_nodes_locs ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"   
  assumes "r \<in> get_child_nodes_locs ptr'"
  shows "r h h'"
  using assms
  apply(auto simp add: get_child_nodes_locs_impl set_child_nodes_locs_impl all_args_def 
      a_set_child_nodes_locs_def a_get_child_nodes_locs_def 
      split: if_splits option.splits )[1] 
   apply(rule is_document_ptr_kind_obtains) 
    apply(simp)
   apply(rule is_document_ptr_kind_obtains) 
    apply(auto)[1]
   apply(auto)[1]
  apply(rule is_element_ptr_kind_obtains) 
   apply(auto)[1]
  apply(auto)[1]
  apply(rule is_element_ptr_kind_obtains) 
   apply(auto)
  done
end

locale l_set_child_nodes_get_child_nodes = l_get_child_nodes + l_set_child_nodes +
  assumes set_child_nodes_get_child_nodes: 
    "type_wf h \<Longrightarrow> known_ptr ptr 
               \<Longrightarrow> h \<turnstile> set_child_nodes ptr children \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes set_child_nodes_get_child_nodes_different_pointers: 
    "ptr \<noteq> ptr' \<Longrightarrow> w \<in> set_child_nodes_locs ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
                \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"

interpretation
  i_set_child_nodes_get_child_nodes?: l_set_child_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
  known_ptr get_child_nodes get_child_nodes_locs set_child_nodes set_child_nodes_locs
  by unfold_locales
declare l_set_child_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_child_nodes_is_l_set_child_nodes_get_child_nodes [instances]: 
  "l_set_child_nodes_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs 
                                     set_child_nodes set_child_nodes_locs"
  using get_child_nodes_is_l_get_child_nodes set_child_nodes_is_l_set_child_nodes
  apply(auto simp add: l_set_child_nodes_get_child_nodes_def l_set_child_nodes_get_child_nodes_axioms_def)[1]
  using set_child_nodes_get_child_nodes apply blast
  using set_child_nodes_get_child_nodes_different_pointers apply metis
  done


subsubsection \<open>get\_attribute\<close>

locale l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_get_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> (_, attr_value option) dom_prog"
  where
    "a_get_attribute ptr k = do {m \<leftarrow> get_M ptr attrs; return (fmlookup m k)}"
lemmas get_attribute_defs = a_get_attribute_def

definition a_get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_attribute_locs element_ptr = {preserved (get_M element_ptr attrs)}"
end

locale l_get_attribute_defs =
  fixes get_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> (_, attr_value option) dom_prog"
  fixes get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_get_attribute_defs get_attribute get_attribute_locs +
  l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> (_, attr_value option) dom_prog"
  and get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes get_attribute_impl: "get_attribute = a_get_attribute"
  assumes get_attribute_locs_impl: "get_attribute_locs = a_get_attribute_locs"
begin
lemma get_attribute_pure [simp]: "pure (get_attribute ptr k) h"
  by (auto simp add: bind_pure_I get_attribute_impl[unfolded a_get_attribute_def])

lemma get_attribute_ok: 
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_attribute element_ptr k)"
  apply(unfold type_wf_impl)
  unfolding get_attribute_impl[unfolded a_get_attribute_def] using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by (metis bind_is_OK_pure_I return_ok ElementMonad.get_M_pure)
    
lemma get_attribute_ptr_in_heap: 
  "h \<turnstile> ok (get_attribute element_ptr k) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  unfolding get_attribute_impl[unfolded a_get_attribute_def]
  by (meson DocumentMonad.get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap bind_is_OK_E is_OK_returns_result_I)

lemma get_attribute_reads: 
  "reads (get_attribute_locs element_ptr) (get_attribute element_ptr k) h h'"
  by(auto simp add: get_attribute_impl[unfolded a_get_attribute_def] 
                    get_attribute_locs_impl[unfolded a_get_attribute_locs_def] 
                    reads_insert_writes_set_right 
          intro!: reads_bind_pure)
end

locale l_get_attribute = l_type_wf + l_get_attribute_defs +
assumes get_attribute_reads: 
  "reads (get_attribute_locs element_ptr) (get_attribute element_ptr k) h h'"
assumes get_attribute_ok: 
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_attribute element_ptr k)"
assumes get_attribute_ptr_in_heap: 
  "h \<turnstile> ok (get_attribute element_ptr k) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
assumes get_attribute_pure [simp]: "pure (get_attribute element_ptr k) h"

global_interpretation l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  get_attribute = l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_attribute and
  get_attribute_locs = l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_attribute_locs .

interpretation
  i_get_attribute?: l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_attribute get_attribute_locs
  apply(unfold_locales)
  by (auto simp add: get_attribute_def get_attribute_locs_def)
declare l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_attribute_is_l_get_attribute [instances]: 
  "l_get_attribute type_wf get_attribute get_attribute_locs"
  apply(unfold_locales)
  using get_attribute_reads get_attribute_ok get_attribute_ptr_in_heap get_attribute_pure
  by blast+


subsubsection \<open>set\_attribute\<close>

locale l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin

definition 
  a_set_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> attr_value option \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_attribute ptr k v = do {
      m \<leftarrow> get_M ptr attrs;
      put_M ptr attrs_update (if v = None then fmdrop k m else fmupd k (the v) m)
    }"

definition a_set_attribute_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_attribute_locs element_ptr \<equiv> all_args (put_M element_ptr attrs_update)"
end

locale l_set_attribute_defs =
  fixes set_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> attr_value option \<Rightarrow> (_, unit) dom_prog"
  fixes set_attribute_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_set_attribute_defs set_attribute set_attribute_locs +
  l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and set_attribute :: "(_) element_ptr \<Rightarrow> attr_key \<Rightarrow> attr_value option \<Rightarrow> (_, unit) dom_prog"
  and set_attribute_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes set_attribute_impl: "set_attribute = a_set_attribute"
  assumes set_attribute_locs_impl: "set_attribute_locs = a_set_attribute_locs"
begin
lemmas set_attribute_def = set_attribute_impl[folded a_set_attribute_def]
lemmas set_attribute_locs_def = set_attribute_locs_impl[unfolded a_set_attribute_locs_def]

lemma set_attribute_ok: "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_attribute element_ptr k v)"
  apply(unfold type_wf_impl)
  unfolding set_attribute_impl[unfolded a_set_attribute_def] using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by(metis (no_types, lifting) DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ElementMonad.get_M_pure bind_is_OK_E 
                               bind_is_OK_pure_I is_OK_returns_result_I)

lemma set_attribute_writes: 
  "writes (set_attribute_locs element_ptr) (set_attribute element_ptr k v) h h'"
  by(auto simp add: set_attribute_impl[unfolded a_set_attribute_def] 
                    set_attribute_locs_impl[unfolded a_set_attribute_locs_def] 
          intro: writes_bind_pure)
end

locale l_set_attribute = l_type_wf + l_set_attribute_defs +
  assumes set_attribute_writes: 
    "writes (set_attribute_locs element_ptr) (set_attribute element_ptr k v) h h'"
  assumes set_attribute_ok: 
    "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_attribute element_ptr k v)"

global_interpretation l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_attribute = l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_attribute and
  set_attribute_locs = l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_attribute_locs .
interpretation 
  i_set_attribute?: l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_attribute set_attribute_locs
  apply(unfold_locales)
  by (auto simp add: set_attribute_def set_attribute_locs_def)
declare l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_attribute_is_l_set_attribute [instances]: 
  "l_set_attribute type_wf set_attribute set_attribute_locs"
  apply(unfold_locales)
  using set_attribute_ok set_attribute_writes
  by blast+


paragraph \<open>get\_attribute\<close>

locale l_set_attribute_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma set_attribute_get_attribute:
  "h \<turnstile> set_attribute ptr k v \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_attribute ptr k \<rightarrow>\<^sub>r v"
  by(auto simp add: set_attribute_impl[unfolded a_set_attribute_def] 
                    get_attribute_impl[unfolded a_get_attribute_def] 
          elim!: bind_returns_heap_E2 
          intro!: bind_pure_returns_result_I 
          elim: element_put_get)
end

locale l_set_attribute_get_attribute = l_get_attribute + l_set_attribute +
  assumes set_attribute_get_attribute:
    "h \<turnstile> set_attribute ptr k v \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_attribute ptr k \<rightarrow>\<^sub>r v"

interpretation
  i_set_attribute_get_attribute?: l_set_attribute_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                                  get_attribute get_attribute_locs set_attribute set_attribute_locs
  by(unfold_locales)
declare l_set_attribute_get_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_attribute_get_attribute_is_l_set_attribute_get_attribute [instances]: 
  "l_set_attribute_get_attribute type_wf get_attribute get_attribute_locs set_attribute set_attribute_locs"
  using get_attribute_is_l_get_attribute set_attribute_is_l_set_attribute
  apply(simp add: l_set_attribute_get_attribute_def l_set_attribute_get_attribute_axioms_def)
  using set_attribute_get_attribute
  by blast

paragraph \<open>get\_child\_nodes\<close>

locale l_set_attribute_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_attribute_get_child_nodes:
  "\<forall>w \<in> set_attribute_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_attribute_locs_def get_child_nodes_locs_def all_args_def 
          intro: element_put_get_preserved[where setter=attrs_update])
end

locale l_set_attribute_get_child_nodes =
  l_set_attribute +
  l_get_child_nodes +
  assumes set_attribute_get_child_nodes: 
         "\<forall>w \<in> set_attribute_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

interpretation
  i_set_attribute_get_child_nodes?: l_set_attribute_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                    set_attribute set_attribute_locs known_ptr get_child_nodes get_child_nodes_locs
  by unfold_locales
declare l_set_attribute_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_attribute_get_child_nodes_is_l_set_attribute_get_child_nodes [instances]:
  "l_set_attribute_get_child_nodes type_wf set_attribute set_attribute_locs known_ptr 
                                   get_child_nodes get_child_nodes_locs"
  using set_attribute_is_l_set_attribute get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_attribute_get_child_nodes_def l_set_attribute_get_child_nodes_axioms_def)
  using set_attribute_get_child_nodes
  by blast


subsubsection \<open>get\_disconnected\_nodes\<close>

locale l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_get_disconnected_nodes :: "(_) document_ptr
    \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "a_get_disconnected_nodes document_ptr = get_M document_ptr disconnected_nodes"
lemmas get_disconnected_nodes_defs = a_get_disconnected_nodes_def

definition a_get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_disconnected_nodes_locs document_ptr = {preserved (get_M document_ptr disconnected_nodes)}"
end

locale l_get_disconnected_nodes_defs = 
  fixes get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  fixes get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes get_disconnected_nodes_impl: "get_disconnected_nodes = a_get_disconnected_nodes"
  assumes get_disconnected_nodes_locs_impl: "get_disconnected_nodes_locs = a_get_disconnected_nodes_locs"
begin
lemmas 
  get_disconnected_nodes_def = get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def]
lemmas 
  get_disconnected_nodes_locs_def = get_disconnected_nodes_locs_impl[unfolded a_get_disconnected_nodes_locs_def]

lemma get_disconnected_nodes_ok: 
  "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_disconnected_nodes document_ptr)"
  apply(unfold type_wf_impl)
  unfolding get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def] using get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by fast

lemma get_disconnected_nodes_ptr_in_heap: 
  "h \<turnstile> ok (get_disconnected_nodes document_ptr) \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h"
  unfolding get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def]
  by (simp add: DocumentMonad.get_M_ptr_in_heap)

lemma get_disconnected_nodes_pure [simp]: "pure (get_disconnected_nodes document_ptr) h"
  unfolding get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def] by simp

lemma get_disconnected_nodes_reads: 
  "reads (get_disconnected_nodes_locs document_ptr) (get_disconnected_nodes document_ptr) h h'"
  by(simp add: get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def] 
               get_disconnected_nodes_locs_impl[unfolded a_get_disconnected_nodes_locs_def] 
               reads_bind_pure reads_insert_writes_set_right)
end

locale l_get_disconnected_nodes = l_type_wf + l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_reads: 
    "reads (get_disconnected_nodes_locs document_ptr) (get_disconnected_nodes document_ptr) h h'"
  assumes get_disconnected_nodes_ok: 
    "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_disconnected_nodes document_ptr)"
  assumes get_disconnected_nodes_ptr_in_heap: 
    "h \<turnstile> ok (get_disconnected_nodes document_ptr) \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h"
  assumes get_disconnected_nodes_pure [simp]: 
   "pure (get_disconnected_nodes document_ptr) h"

global_interpretation l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  get_disconnected_nodes = l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_disconnected_nodes and
  get_disconnected_nodes_locs = l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_disconnected_nodes_locs .
interpretation 
  i_get_disconnected_nodes?: l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes 
                             get_disconnected_nodes_locs
  apply(unfold_locales)
  by (auto simp add: get_disconnected_nodes_def get_disconnected_nodes_locs_def)
declare l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_disconnected_nodes_is_l_get_disconnected_nodes [instances]: 
  "l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs"
  apply(simp add: l_get_disconnected_nodes_def)
  using get_disconnected_nodes_reads get_disconnected_nodes_ok get_disconnected_nodes_ptr_in_heap 
        get_disconnected_nodes_pure
  by blast+


paragraph \<open>set\_child\_nodes\<close>

locale l_set_child_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  CD: l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_child_nodes_get_disconnected_nodes: 
  "\<forall>w \<in> a_set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> a_get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: a_set_child_nodes_locs_def a_get_disconnected_nodes_locs_def all_args_def)
end

locale l_set_child_nodes_get_disconnected_nodes = l_set_child_nodes + l_get_disconnected_nodes +
  assumes set_child_nodes_get_disconnected_nodes: 
  "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

interpretation
  i_set_child_nodes_get_disconnected_nodes?: l_set_child_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                                             known_ptr set_child_nodes set_child_nodes_locs 
                                             get_disconnected_nodes get_disconnected_nodes_locs
  by(unfold_locales)
declare l_set_child_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_disconnected_nodes_is_l_set_child_nodes_get_disconnected_nodes [instances]:
  "l_set_child_nodes_get_disconnected_nodes type_wf set_child_nodes set_child_nodes_locs 
                                            get_disconnected_nodes get_disconnected_nodes_locs"
  using set_child_nodes_is_l_set_child_nodes get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_child_nodes_get_disconnected_nodes_def 
                  l_set_child_nodes_get_disconnected_nodes_axioms_def)
  using set_child_nodes_get_disconnected_nodes
  by fast


paragraph \<open>set\_attribute\<close>

locale l_set_attribute_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_attribute_get_disconnected_nodes: 
  "\<forall>w \<in> a_set_attribute_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> a_get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: a_set_attribute_locs_def a_get_disconnected_nodes_locs_def all_args_def)
end

locale l_set_attribute_get_disconnected_nodes = l_set_attribute + l_get_disconnected_nodes +
  assumes set_attribute_get_disconnected_nodes: 
  "\<forall>w \<in> set_attribute_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

interpretation
  i_set_attribute_get_disconnected_nodes?: l_set_attribute_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                set_attribute set_attribute_locs get_disconnected_nodes get_disconnected_nodes_locs
  by(unfold_locales)
declare l_set_attribute_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_attribute_get_disconnected_nodes_is_l_set_attribute_get_disconnected_nodes [instances]:
  "l_set_attribute_get_disconnected_nodes type_wf set_attribute set_attribute_locs 
                                          get_disconnected_nodes get_disconnected_nodes_locs"
  using set_attribute_is_l_set_attribute get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_attribute_get_disconnected_nodes_def 
                  l_set_attribute_get_disconnected_nodes_axioms_def)
  using set_attribute_get_disconnected_nodes
  by fast


paragraph \<open>new\_element\<close>

locale l_new_element_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_disconnected_nodes_new_element:  
   "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
        \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: get_disconnected_nodes_locs_def new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_new_element_get_disconnected_nodes = l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_new_element:  
   "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
        \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_element_get_disconnected_nodes?: 
  l_new_element_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes 
  get_disconnected_nodes_locs
  by unfold_locales
declare l_new_element_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_element_get_disconnected_nodes_is_l_new_element_get_disconnected_nodes [instances]:
  "l_new_element_get_disconnected_nodes get_disconnected_nodes_locs"
  by (simp add: get_disconnected_nodes_new_element l_new_element_get_disconnected_nodes_def)


paragraph \<open>new\_character\_data\<close>

locale l_new_character_data_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_disconnected_nodes_new_character_data:  
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: get_disconnected_nodes_locs_def new_character_data_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_new_character_data_get_disconnected_nodes = l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_new_character_data:  
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_character_data_get_disconnected_nodes?: 
  l_new_character_data_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes 
                                                    get_disconnected_nodes_locs
  by unfold_locales
declare l_new_character_data_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_character_data_get_disconnected_nodes_is_l_new_character_data_get_disconnected_nodes [instances]:
  "l_new_character_data_get_disconnected_nodes get_disconnected_nodes_locs"
  by (simp add: get_disconnected_nodes_new_character_data l_new_character_data_get_disconnected_nodes_def)


paragraph \<open>new\_document\<close>

locale l_new_document_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_disconnected_nodes_new_document_different_pointers:  
  "new_document_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: get_disconnected_nodes_locs_def new_document_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)

lemma new_document_no_disconnected_nodes:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"
  by(simp add: get_disconnected_nodes_def new_document_disconnected_nodes)
  
end

interpretation i_new_document_get_disconnected_nodes?: 
  l_new_document_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs
  by unfold_locales
declare l_new_document_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_new_document_get_disconnected_nodes = l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_new_document_different_pointers:  
  "new_document_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  assumes new_document_no_disconnected_nodes:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"

lemma new_document_get_disconnected_nodes_is_l_new_document_get_disconnected_nodes [instances]:
  "l_new_document_get_disconnected_nodes get_disconnected_nodes get_disconnected_nodes_locs"
  apply (auto simp add: l_new_document_get_disconnected_nodes_def)[1]
  using get_disconnected_nodes_new_document_different_pointers apply fast
  using new_document_no_disconnected_nodes apply blast
  done



subsubsection \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin

definition a_set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_disconnected_nodes document_ptr disc_nodes = put_M document_ptr disconnected_nodes_update disc_nodes"
lemmas set_disconnected_nodes_defs = a_set_disconnected_nodes_def

definition a_set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_disconnected_nodes_locs document_ptr \<equiv> all_args (put_M document_ptr disconnected_nodes_update)"
end

locale l_set_disconnected_nodes_defs =
  fixes set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  fixes set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf + 
  l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes set_disconnected_nodes_impl: "set_disconnected_nodes = a_set_disconnected_nodes"
  assumes set_disconnected_nodes_locs_impl: "set_disconnected_nodes_locs = a_set_disconnected_nodes_locs"
begin
lemmas set_disconnected_nodes_def = set_disconnected_nodes_impl[unfolded a_set_disconnected_nodes_def]
lemmas set_disconnected_nodes_locs_def = set_disconnected_nodes_locs_impl[unfolded a_set_disconnected_nodes_locs_def]
lemma set_disconnected_nodes_ok:
  "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_disconnected_nodes document_ptr node_ptrs)"
  by (simp add: type_wf_impl put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok set_disconnected_nodes_impl[unfolded a_set_disconnected_nodes_def])

lemma set_disconnected_nodes_ptr_in_heap: 
  "h \<turnstile> ok (set_disconnected_nodes document_ptr disc_nodes) \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h"
  by (simp add: set_disconnected_nodes_impl[unfolded a_set_disconnected_nodes_def] 
                DocumentMonad.put_M_ptr_in_heap)

lemma set_disconnected_nodes_writes: 
  "writes (set_disconnected_nodes_locs document_ptr) (set_disconnected_nodes document_ptr disc_nodes) h h'"
  by(auto simp add: set_disconnected_nodes_impl[unfolded a_set_disconnected_nodes_def] 
                    set_disconnected_nodes_locs_impl[unfolded a_set_disconnected_nodes_locs_def] 
          intro: writes_bind_pure)

lemma set_disconnected_nodes_pointers_preserved:
  assumes "w \<in> set_disconnected_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def  set_disconnected_nodes_locs_impl[unfolded 
                    a_set_disconnected_nodes_locs_def] 
          split: if_splits)

lemma set_disconnected_nodes_typess_preserved:
  assumes "w \<in> set_disconnected_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  apply(unfold type_wf_impl)
  by(auto simp add: all_args_def 
                    set_disconnected_nodes_locs_impl[unfolded a_set_disconnected_nodes_locs_def] 
          split: if_splits)
end

locale l_set_disconnected_nodes = l_type_wf + l_set_disconnected_nodes_defs +
  assumes set_disconnected_nodes_writes: 
    "writes (set_disconnected_nodes_locs document_ptr) (set_disconnected_nodes document_ptr disc_nodes) h h'"
  assumes set_disconnected_nodes_ok: 
    "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_disconnected_nodes document_ptr disc_noded)"
  assumes set_disconnected_nodes_ptr_in_heap: 
    "h \<turnstile> ok (set_disconnected_nodes document_ptr disc_noded) \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h"
  assumes set_disconnected_nodes_pointers_preserved: 
   "w \<in> set_disconnected_nodes_locs document_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
 assumes set_disconnected_nodes_types_preserved: 
   "w \<in> set_disconnected_nodes_locs document_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

global_interpretation l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_disconnected_nodes = l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_disconnected_nodes and
  set_disconnected_nodes_locs = l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_disconnected_nodes_locs .
interpretation 
  i_set_disconnected_nodes?: l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_disconnected_nodes 
                             set_disconnected_nodes_locs
  apply unfold_locales
  by (auto simp add: set_disconnected_nodes_def set_disconnected_nodes_locs_def)
declare l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_is_l_set_disconnected_nodes [instances]: 
  "l_set_disconnected_nodes type_wf set_disconnected_nodes set_disconnected_nodes_locs"
  apply(simp add: l_set_disconnected_nodes_def)
  using set_disconnected_nodes_ok set_disconnected_nodes_writes set_disconnected_nodes_pointers_preserved 
        set_disconnected_nodes_ptr_in_heap set_disconnected_nodes_typess_preserved
  by blast+


paragraph \<open>get\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M 
                                                             + l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_disconnected_nodes:
  assumes "h \<turnstile> a_set_disconnected_nodes document_ptr disc_nodes \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> a_get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  using assms 
  by(auto simp add: a_get_disconnected_nodes_def a_set_disconnected_nodes_def)

lemma set_disconnected_nodes_get_disconnected_nodes_different_pointers: 
  assumes "ptr \<noteq> ptr'"
  assumes "w \<in> a_set_disconnected_nodes_locs ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"   
  assumes "r \<in> a_get_disconnected_nodes_locs ptr'"
  shows "r h h'"
  using assms
  by(auto simp add: all_args_def a_set_disconnected_nodes_locs_def a_get_disconnected_nodes_locs_def 
             split: if_splits option.splits )
end

locale l_set_disconnected_nodes_get_disconnected_nodes = l_get_disconnected_nodes 
                                                       + l_set_disconnected_nodes +
  assumes set_disconnected_nodes_get_disconnected_nodes: 
  "h \<turnstile> set_disconnected_nodes document_ptr disc_nodes \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assumes set_disconnected_nodes_get_disconnected_nodes_different_pointers: 
  "ptr \<noteq> ptr' \<Longrightarrow> w \<in> set_disconnected_nodes_locs ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"

interpretation i_set_disconnected_nodes_get_disconnected_nodes?:
  l_set_disconnected_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes 
                     get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  by unfold_locales
declare l_set_disconnected_nodes_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_disconnected_nodes_is_l_set_disconnected_nodes_get_disconnected_nodes [instances]:
  "l_set_disconnected_nodes_get_disconnected_nodes  type_wf get_disconnected_nodes get_disconnected_nodes_locs 
                                                    set_disconnected_nodes set_disconnected_nodes_locs"
  using set_disconnected_nodes_is_l_set_disconnected_nodes get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_disconnected_nodes_get_disconnected_nodes_def 
                  l_set_disconnected_nodes_get_disconnected_nodes_axioms_def)
  using set_disconnected_nodes_get_disconnected_nodes 
        set_disconnected_nodes_get_disconnected_nodes_different_pointers
  by fast+


paragraph \<open>get\_child\_nodes\<close>

locale l_set_disconnected_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_child_nodes: 
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_disconnected_nodes_locs_impl[unfolded a_set_disconnected_nodes_locs_def] 
                    get_child_nodes_locs_impl[unfolded a_get_child_nodes_locs_def] all_args_def)
end

locale l_set_disconnected_nodes_get_child_nodes = l_set_disconnected_nodes_defs + l_get_child_nodes_defs +
  assumes set_disconnected_nodes_get_child_nodes [simp]: 
    "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

interpretation
  i_set_disconnected_nodes_get_child_nodes?: l_set_disconnected_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M 
                                             type_wf 
                                             set_disconnected_nodes set_disconnected_nodes_locs 
                                             known_ptr get_child_nodes get_child_nodes_locs
  by unfold_locales
declare l_set_disconnected_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_child_nodes_is_l_set_disconnected_nodes_get_child_nodes [instances]:
  "l_set_disconnected_nodes_get_child_nodes set_disconnected_nodes_locs get_child_nodes_locs"
  using set_disconnected_nodes_is_l_set_disconnected_nodes get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_disconnected_nodes_get_child_nodes_def)
  using set_disconnected_nodes_get_child_nodes
  by fast


subsubsection \<open>get\_tag\_name\<close>

locale l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_get_tag_name :: "(_) element_ptr \<Rightarrow> (_, tag_type) dom_prog"
  where
    "a_get_tag_name element_ptr = get_M element_ptr tag_type"

definition a_get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_tag_name_locs element_ptr \<equiv> {preserved (get_M element_ptr tag_type)}"
end

locale l_get_tag_name_defs =
  fixes get_tag_name :: "(_) element_ptr \<Rightarrow> (_, tag_type) dom_prog"
  fixes get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_get_tag_name_defs get_tag_name get_tag_name_locs +
  l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs 
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and get_tag_name :: "(_) element_ptr \<Rightarrow> (_, tag_type) dom_prog"
  and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes get_tag_name_impl: "get_tag_name = a_get_tag_name"
  assumes get_tag_name_locs_impl: "get_tag_name_locs = a_get_tag_name_locs"
begin
lemmas get_tag_name_def = get_tag_name_impl[unfolded a_get_tag_name_def]
lemmas get_tag_name_locs_def = get_tag_name_locs_impl[unfolded a_get_tag_name_locs_def]



lemma get_tag_name_ok: 
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_tag_name element_ptr)"
  apply(unfold type_wf_impl get_tag_name_impl[unfolded a_get_tag_name_def])
  using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by blast

lemma get_tag_name_pure [simp]: "pure (get_tag_name element_ptr) h"
  unfolding get_tag_name_impl[unfolded a_get_tag_name_def]
  by simp

lemma get_tag_name_ptr_in_heap [simp]:
  assumes "h \<turnstile> get_tag_name element_ptr \<rightarrow>\<^sub>r children"
  shows "element_ptr |\<in>| element_ptr_kinds h"
  using assms
  by(auto simp add: get_tag_name_impl[unfolded a_get_tag_name_def] get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap 
          dest: is_OK_returns_result_I)

lemma get_tag_name_reads: "reads (get_tag_name_locs element_ptr) (get_tag_name element_ptr) h h'"
  by(simp add: get_tag_name_impl[unfolded a_get_tag_name_def] 
               get_tag_name_locs_impl[unfolded a_get_tag_name_locs_def] reads_bind_pure 
               reads_insert_writes_set_right)
end

locale l_get_tag_name = l_type_wf + l_get_tag_name_defs +
  assumes get_tag_name_reads: 
    "reads (get_tag_name_locs element_ptr) (get_tag_name element_ptr) h h'"
  assumes get_tag_name_ok: 
    "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_tag_name element_ptr)"
  assumes get_tag_name_ptr_in_heap: 
    "h \<turnstile> ok (get_tag_name element_ptr) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  assumes get_tag_name_pure [simp]: 
    "pure (get_tag_name element_ptr) h"


global_interpretation l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  get_tag_name = l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_tag_name and
  get_tag_name_locs = l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_tag_name_locs .

interpretation
  i_get_tag_name?: l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_tag_name get_tag_name_locs
  apply(unfold_locales)
  by (auto simp add: get_tag_name_def get_tag_name_locs_def)
declare l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_tag_name_is_l_get_tag_name [instances]: 
  "l_get_tag_name type_wf get_tag_name get_tag_name_locs"
  apply(unfold_locales)
  using get_tag_name_reads get_tag_name_ok get_tag_name_ptr_in_heap get_tag_name_pure
  by blast+


paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_tag_name: 
  "\<forall>w \<in> a_set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> a_get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: a_set_disconnected_nodes_locs_def a_get_tag_name_locs_def all_args_def)
end

locale l_set_disconnected_nodes_get_tag_name = l_set_disconnected_nodes + l_get_tag_name +
  assumes set_disconnected_nodes_get_tag_name: 
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"

interpretation
  i_set_disconnected_nodes_get_tag_name?: l_set_disconnected_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                                          set_disconnected_nodes set_disconnected_nodes_locs 
                                          get_tag_name get_tag_name_locs
  by unfold_locales
declare l_set_disconnected_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_tag_name_is_l_set_disconnected_nodes_get_tag_name [instances]:
  "l_set_disconnected_nodes_get_tag_name type_wf set_disconnected_nodes set_disconnected_nodes_locs 
                                         get_tag_name get_tag_name_locs"
  using set_disconnected_nodes_is_l_set_disconnected_nodes get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_disconnected_nodes_get_tag_name_def l_set_disconnected_nodes_get_tag_name_axioms_def)
  using set_disconnected_nodes_get_tag_name
  by fast


paragraph \<open>set\_child\_nodes\<close>

locale l_set_child_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_child_nodes_get_tag_name: 
  "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: set_child_nodes_locs_def get_tag_name_locs_def all_args_def 
          intro: element_put_get_preserved[where getter=tag_type and setter=child_nodes_update])
end

locale l_set_child_nodes_get_tag_name = l_set_child_nodes + l_get_tag_name +
  assumes set_child_nodes_get_tag_name: 
    "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"

interpretation
  i_set_child_nodes_get_tag_name?: l_set_child_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr 
                                   set_child_nodes set_child_nodes_locs get_tag_name get_tag_name_locs
  by unfold_locales
declare l_set_child_nodes_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_tag_name_is_l_set_child_nodes_get_tag_name [instances]:
  "l_set_child_nodes_get_tag_name type_wf set_child_nodes set_child_nodes_locs get_tag_name get_tag_name_locs"
  using set_child_nodes_is_l_set_child_nodes get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_child_nodes_get_tag_name_def l_set_child_nodes_get_tag_name_axioms_def)
  using set_child_nodes_get_tag_name
  by fast


subsubsection \<open>set\_tag\_type\<close>

locale l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin

definition a_set_tag_type :: "(_) element_ptr \<Rightarrow> tag_type \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_tag_type ptr tag = do {
      m \<leftarrow> get_M ptr attrs;
      put_M ptr tag_type_update tag
    }"
lemmas set_tag_type_defs = a_set_tag_type_def

definition a_set_tag_type_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_tag_type_locs element_ptr \<equiv> all_args (put_M element_ptr tag_type_update)"
end

locale l_set_tag_type_defs =
  fixes set_tag_type :: "(_) element_ptr \<Rightarrow> tag_type \<Rightarrow> (_, unit) dom_prog"
  fixes set_tag_type_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_set_tag_type_defs set_tag_type set_tag_type_locs +
  l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs 
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and set_tag_type :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> (_, unit) dom_prog"
  and set_tag_type_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes set_tag_type_impl: "set_tag_type = a_set_tag_type"
  assumes set_tag_type_locs_impl: "set_tag_type_locs = a_set_tag_type_locs"
begin

lemma set_tag_type_ok: 
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_tag_type element_ptr tag)"
  apply(unfold type_wf_impl)
  unfolding set_tag_type_impl[unfolded a_set_tag_type_def] using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by (metis (no_types, lifting) DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ElementMonad.get_M_pure bind_is_OK_E 
                                bind_is_OK_pure_I is_OK_returns_result_I)

lemma set_tag_type_writes: 
  "writes (set_tag_type_locs element_ptr) (set_tag_type element_ptr tag) h h'"
  by(auto simp add: set_tag_type_impl[unfolded a_set_tag_type_def] 
                    set_tag_type_locs_impl[unfolded a_set_tag_type_locs_def] intro: writes_bind_pure)

lemma set_tag_type_pointers_preserved:
  assumes "w \<in> set_tag_type_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_tag_type_locs_impl[unfolded a_set_tag_type_locs_def] 
          split: if_splits)

lemma set_tag_type_typess_preserved:
  assumes "w \<in> set_tag_type_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_tag_type_locs_impl[unfolded a_set_tag_type_locs_def] 
          split: if_splits)
end

locale l_set_tag_type = l_type_wf + l_set_tag_type_defs +
  assumes set_tag_type_writes: 
    "writes (set_tag_type_locs element_ptr) (set_tag_type element_ptr tag) h h'"
  assumes set_tag_type_ok: 
    "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_tag_type element_ptr tag)"
  assumes set_tag_type_pointers_preserved: 
    "w \<in> set_tag_type_locs element_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes set_tag_type_types_preserved: 
    "w \<in> set_tag_type_locs element_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"


global_interpretation l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_tag_type = l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_tag_type and
  set_tag_type_locs = l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_tag_type_locs .
interpretation 
  i_set_tag_type?: l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_tag_type set_tag_type_locs
  apply(unfold_locales)
  by (auto simp add: set_tag_type_def set_tag_type_locs_def)
declare l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_type_is_l_set_tag_type [instances]: 
  "l_set_tag_type type_wf set_tag_type set_tag_type_locs"
  apply(simp add: l_set_tag_type_def)
  using set_tag_type_ok set_tag_type_writes set_tag_type_pointers_preserved 
        set_tag_type_typess_preserved
  by blast

paragraph \<open>get\_child\_nodes\<close>

locale l_set_tag_type_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_type_get_child_nodes: 
  "\<forall>w \<in> set_tag_type_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_tag_type_locs_impl[unfolded a_set_tag_type_locs_def] 
                    get_child_nodes_locs_impl[unfolded a_get_child_nodes_locs_def] all_args_def 
          intro: element_put_get_preserved[where setter=tag_type_update and getter=child_nodes])
end

locale l_set_tag_type_get_child_nodes = l_set_tag_type + l_get_child_nodes +
  assumes set_tag_type_get_child_nodes: 
    "\<forall>w \<in> set_tag_type_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

interpretation
  i_set_tag_type_get_child_nodes?: l_set_tag_type_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                                   set_tag_type set_tag_type_locs known_ptr 
                                   get_child_nodes get_child_nodes_locs
  by unfold_locales
declare l_set_tag_type_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_type_get_child_nodes_is_l_set_tag_type_get_child_nodes [instances]:
  "l_set_tag_type_get_child_nodes type_wf set_tag_type set_tag_type_locs known_ptr get_child_nodes 
                                  get_child_nodes_locs"
  using set_tag_type_is_l_set_tag_type get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_tag_type_get_child_nodes_def l_set_tag_type_get_child_nodes_axioms_def)
  using set_tag_type_get_child_nodes
  by fast


paragraph \<open>get\_disconnected\_nodes\<close>

locale l_set_tag_type_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_tag_type\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_type_get_disconnected_nodes: 
  "\<forall>w \<in> set_tag_type_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_tag_type_locs_impl[unfolded a_set_tag_type_locs_def] 
                    get_disconnected_nodes_locs_impl[unfolded a_get_disconnected_nodes_locs_def] 
                    all_args_def)
end

locale l_set_tag_type_get_disconnected_nodes = l_set_tag_type + l_get_disconnected_nodes +
  assumes set_tag_type_get_disconnected_nodes: 
   "\<forall>w \<in> set_tag_type_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

interpretation
  i_set_tag_type_get_disconnected_nodes?: l_set_tag_type_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf 
                                          set_tag_type set_tag_type_locs get_disconnected_nodes 
                                          get_disconnected_nodes_locs
  by unfold_locales
declare l_set_tag_type_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_type_get_disconnected_nodes_is_l_set_tag_type_get_disconnected_nodes [instances]:
  "l_set_tag_type_get_disconnected_nodes type_wf set_tag_type set_tag_type_locs get_disconnected_nodes 
                                         get_disconnected_nodes_locs"
  using set_tag_type_is_l_set_tag_type get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_tag_type_get_disconnected_nodes_def 
                  l_set_tag_type_get_disconnected_nodes_axioms_def)
  using set_tag_type_get_disconnected_nodes
  by fast


subsubsection \<open>set\_val\<close>

locale l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin

definition a_set_val :: "(_) character_data_ptr \<Rightarrow> DOMString \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_val ptr v = do {
      m \<leftarrow> get_M ptr val;
      put_M ptr val_update v
    }"
lemmas set_val_defs = a_set_val_def

definition a_set_val_locs :: "(_) character_data_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_val_locs character_data_ptr \<equiv> all_args (put_M character_data_ptr val_update)"
end

locale l_set_val_defs =
  fixes set_val :: "(_) character_data_ptr \<Rightarrow> DOMString \<Rightarrow> (_, unit) dom_prog"
  fixes set_val_locs :: "(_) character_data_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_set_val_defs set_val set_val_locs +
  l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
  and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> (_, unit) dom_prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> (_, unit) dom_prog set"  +
  assumes type_wf_impl: "type_wf = DocumentClass.type_wf"
  assumes set_val_impl: "set_val = a_set_val"
  assumes set_val_locs_impl: "set_val_locs = a_set_val_locs"
begin

lemma set_val_ok: 
  "type_wf h \<Longrightarrow> character_data_ptr |\<in>| character_data_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_val character_data_ptr tag)"
  apply(unfold type_wf_impl)
  unfolding set_val_impl[unfolded a_set_val_def] using get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ok put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ok
  by (metis (no_types, lifting) DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a CharacterDataMonad.get_M_pure 
            bind_is_OK_E bind_is_OK_pure_I is_OK_returns_result_I)

lemma set_val_writes: "writes (set_val_locs character_data_ptr) (set_val character_data_ptr tag) h h'"
  by(auto simp add: set_val_impl[unfolded a_set_val_def] set_val_locs_impl[unfolded a_set_val_locs_def] 
               intro: writes_bind_pure)

lemma set_val_pointers_preserved:
  assumes "w \<in> set_val_locs character_data_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_val_locs_impl[unfolded a_set_val_locs_def] split: if_splits)

lemma set_val_typess_preserved:
  assumes "w \<in> set_val_locs character_data_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_val_locs_impl[unfolded a_set_val_locs_def] split: if_splits)
end

locale l_set_val = l_type_wf + l_set_val_defs +
  assumes set_val_writes: 
    "writes (set_val_locs character_data_ptr) (set_val character_data_ptr tag) h h'"
  assumes set_val_ok: 
    "type_wf h \<Longrightarrow> character_data_ptr |\<in>| character_data_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_val character_data_ptr tag)"
  assumes set_val_pointers_preserved: 
    "w \<in> set_val_locs character_data_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes set_val_types_preserved: 
    "w \<in> set_val_locs character_data_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"


global_interpretation l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_val = l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_val and
  set_val_locs = l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_val_locs .
interpretation 
  i_set_val?: l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_val set_val_locs
  apply(unfold_locales)
  by (auto simp add: set_val_def set_val_locs_def)
declare l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_is_l_set_val [instances]: "l_set_val type_wf set_val set_val_locs"
  apply(simp add: l_set_val_def)
  using set_val_ok set_val_writes set_val_pointers_preserved set_val_typess_preserved
  by blast

paragraph \<open>get\_child\_nodes\<close>

locale l_set_val_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_val_get_child_nodes: 
  "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_val_locs_impl[unfolded a_set_val_locs_def] 
                    get_child_nodes_locs_impl[unfolded a_get_child_nodes_locs_def] all_args_def)
end

locale l_set_val_get_child_nodes = l_set_val + l_get_child_nodes +
  assumes set_val_get_child_nodes: 
    "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

interpretation
  i_set_val_get_child_nodes?: l_set_val_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_val set_val_locs known_ptr 
                              get_child_nodes get_child_nodes_locs
  by unfold_locales
declare l_set_val_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_get_child_nodes_is_l_set_val_get_child_nodes [instances]:
  "l_set_val_get_child_nodes type_wf set_val set_val_locs known_ptr get_child_nodes get_child_nodes_locs"
  using set_val_is_l_set_val get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_val_get_child_nodes_def l_set_val_get_child_nodes_axioms_def)
  using set_val_get_child_nodes
  by fast


paragraph \<open>get\_disconnected\_nodes\<close>

locale l_set_val_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_val_get_disconnected_nodes: 
  "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_val_locs_impl[unfolded a_set_val_locs_def] 
                    get_disconnected_nodes_locs_impl[unfolded a_get_disconnected_nodes_locs_def] 
                    all_args_def)
end

locale l_set_val_get_disconnected_nodes = l_set_val + l_get_disconnected_nodes +
  assumes set_val_get_disconnected_nodes: 
   "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

interpretation
  i_set_val_get_disconnected_nodes?: l_set_val_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_val 
                                     set_val_locs get_disconnected_nodes get_disconnected_nodes_locs
  by unfold_locales
declare l_set_val_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_get_disconnected_nodes_is_l_set_val_get_disconnected_nodes [instances]:
  "l_set_val_get_disconnected_nodes type_wf set_val set_val_locs get_disconnected_nodes get_disconnected_nodes_locs"
  using set_val_is_l_set_val get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_val_get_disconnected_nodes_def l_set_val_get_disconnected_nodes_axioms_def)
  using set_val_get_disconnected_nodes
  by fast



subsubsection \<open>get\_parent\<close>

locale l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_parent :: "(_) node_ptr \<Rightarrow> (_, (_::linorder) object_ptr option) dom_prog"
  where
    "a_get_parent node_ptr = do {
      check_in_heap (cast node_ptr);
      parent_ptrs \<leftarrow> object_ptr_kinds_M \<bind> filter_M (\<lambda>ptr. do {
        children \<leftarrow> get_child_nodes ptr;
        return (node_ptr \<in> set children)
      });
      (if parent_ptrs = []
        then return None
        else return (Some (hd parent_ptrs)))
    }"

definition 
  "a_get_parent_locs \<equiv> (\<Union>ptr. get_child_nodes_locs ptr \<union> {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t  ptr RObject.nothing)})"
end

locale l_get_parent_defs =
  fixes get_parent :: "(_) node_ptr \<Rightarrow> (_, (_::linorder) object_ptr option) dom_prog"
  fixes get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs +
  l_known_ptrs known_ptr known_ptrs +
  l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs +
  l_get_parent_defs get_parent get_parent_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes (* :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog" *)
  and get_child_nodes_locs (* :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" *)
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs (* :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" *) +
  assumes get_parent_impl: "get_parent = a_get_parent"
  assumes get_parent_locs_impl: "get_parent_locs = a_get_parent_locs"
begin
lemmas get_parent_def = get_parent_impl[unfolded a_get_parent_def]
lemmas get_parent_locs_def = get_parent_locs_impl[unfolded a_get_parent_locs_def]

lemma get_parent_pure [simp]: "pure (get_parent ptr) h"
  using get_child_nodes_pure
  by(auto simp add: get_parent_def intro!: bind_pure_I filter_M_pure_I)

lemma get_parent_ok [simp]:
  assumes "type_wf h"
  assumes "known_ptrs h"
  assumes "ptr |\<in>| node_ptr_kinds h"
  shows "h \<turnstile> ok (get_parent ptr)"
  using assms get_child_nodes_ok get_child_nodes_pure
  by(auto simp add: get_parent_impl[unfolded a_get_parent_def] known_ptrs_known_ptr 
          intro!: bind_is_OK_pure_I filter_M_pure_I filter_M_is_OK_I bind_pure_I)

lemma get_parent_ptr_in_heap [simp]: "h \<turnstile> ok (get_parent node_ptr) \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h"
  using get_parent_def is_OK_returns_result_I check_in_heap_ptr_in_heap
  by (metis (no_types, lifting) bind_returns_heap_E get_parent_pure node_ptr_kinds_commutes pure_pure)

lemma get_parent_parent_in_heap:
  assumes "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent"
  shows "parent |\<in>| object_ptr_kinds h"
  using assms get_child_nodes_pure
  by(auto simp add: get_parent_def elim!: bind_returns_result_E2 
          dest!: filter_M_not_more_elements[where x=parent] 
          intro!: filter_M_pure_I bind_pure_I 
          split: if_splits)

lemma get_parent_child_dual:
  assumes "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr"
  obtains children where "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children" and "child \<in> set children"
  using assms get_child_nodes_pure
  by(auto simp add: get_parent_def bind_pure_I 
          dest!: filter_M_holds_for_result 
          elim!: bind_returns_result_E2 
          intro!: filter_M_pure_I 
          split: if_splits)

lemma get_parent_reads: "reads get_parent_locs (get_parent node_ptr) h h'"
  using get_child_nodes_reads[unfolded reads_def]
  by(auto simp add: get_parent_def get_parent_locs_def 
          intro!: reads_bind_pure reads_subset[OF check_in_heap_reads] 
                  reads_subset[OF get_child_nodes_reads] reads_subset[OF return_reads] 
                  reads_subset[OF object_ptr_kinds_M_reads] filter_M_reads filter_M_pure_I bind_pure_I)

lemma get_parent_reads_pointers: "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr RObject.nothing) \<in> get_parent_locs"
  by(auto simp add: get_parent_locs_def)
end

locale l_get_parent = l_type_wf + l_known_ptrs + l_get_parent_defs + l_get_child_nodes +
  assumes get_parent_reads: 
    "reads get_parent_locs (get_parent node_ptr) h h'"
  assumes get_parent_ok: 
    "type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_parent node_ptr)"
  assumes get_parent_ptr_in_heap: 
    "h \<turnstile> ok (get_parent node_ptr) \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h"
  assumes get_parent_pure [simp]: 
    "pure (get_parent node_ptr) h"
  assumes get_parent_parent_in_heap: 
    "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> parent |\<in>| object_ptr_kinds h"
  assumes get_parent_child_dual: 
    "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr \<Longrightarrow> (\<And>children. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
         \<Longrightarrow> child \<in> set children \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  assumes get_parent_reads_pointers: 
    "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr RObject.nothing) \<in> get_parent_locs"

global_interpretation l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs defines      
  get_parent = "l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_parent get_child_nodes" and
  get_parent_locs = "l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_parent_locs get_child_nodes_locs" .

interpretation 
  i_get_parent?: l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs 
                 get_parent get_parent_locs
  using instances
  apply(simp add: l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def)
  apply(simp add: get_parent_def get_parent_locs_def)
  done
declare l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_parent_is_l_get_parent [instances]: 
  "l_get_parent type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs"
  using instances
  apply(auto simp add: l_get_parent_def l_get_parent_axioms_def)[1]
  using get_parent_reads get_parent_ok get_parent_ptr_in_heap get_parent_pure 
        get_parent_parent_in_heap get_parent_child_dual
  using get_parent_reads_pointers
  by blast+


paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_child_nodes
    set_disconnected_nodes set_disconnected_nodes_locs get_child_nodes get_child_nodes_locs
  + l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    type_wf set_disconnected_nodes set_disconnected_nodes_locs
  + l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma set_disconnected_nodes_get_parent [simp]: 
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_parent_locs. r h h'))"
  by(auto simp add: get_parent_locs_def set_disconnected_nodes_locs_def all_args_def)
end

locale l_set_disconnected_nodes_get_parent = l_set_disconnected_nodes_defs + l_get_parent_defs +
  assumes set_disconnected_nodes_get_parent [simp]: 
     "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_parent_locs. r h h'))"

interpretation i_set_disconnected_nodes_get_parent?:
  l_set_disconnected_nodes_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf set_disconnected_nodes 
  set_disconnected_nodes_locs get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  using instances
  by (simp add: l_set_disconnected_nodes_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_set_disconnected_nodes_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_parent_is_l_set_disconnected_nodes_get_parent [instances]:
  "l_set_disconnected_nodes_get_parent set_disconnected_nodes_locs get_parent_locs"
  by(simp add: l_set_disconnected_nodes_get_parent_def)



subsubsection \<open>get\_root\_node\<close>

locale l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_parent_defs get_parent get_parent_locs
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
partial_function (dom_prog) 
  a_get_ancestors :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_get_ancestors ptr = do {
      check_in_heap ptr;
      ancestors \<leftarrow> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
        Some node_ptr \<Rightarrow> do {
          parent_ptr_opt \<leftarrow> get_parent node_ptr;
          (case parent_ptr_opt of
            Some parent_ptr \<Rightarrow> a_get_ancestors parent_ptr
          | None \<Rightarrow> return [])
        }
      | None \<Rightarrow> return []);
      return (ptr # ancestors)
    }"

definition "a_get_ancestors_locs = get_parent_locs"

definition a_get_root_node :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr) dom_prog"
  where
    "a_get_root_node ptr = do {
      ancestors \<leftarrow> a_get_ancestors ptr;
      return (last ancestors)
    }"
definition "a_get_root_node_locs = a_get_ancestors_locs"
end

locale l_get_ancestors_defs =
  fixes get_ancestors :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  fixes get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_root_node_defs = 
  fixes get_root_node :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr) dom_prog"
  fixes get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent +
  l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_ancestors_defs +
  l_get_root_node_defs +
  assumes get_ancestors_impl: "get_ancestors = a_get_ancestors"
  assumes get_ancestors_locs_impl: "get_ancestors_locs = a_get_ancestors_locs"
  assumes get_root_node_impl: "get_root_node = a_get_root_node"
  assumes get_root_node_locs_impl: "get_root_node_locs = a_get_root_node_locs"
begin
lemmas get_ancestors_def = a_get_ancestors.simps[folded get_ancestors_impl]
lemmas get_ancestors_locs_def = a_get_ancestors_locs_def[folded get_ancestors_locs_impl]
lemmas get_root_node_def = a_get_root_node_def[folded get_root_node_impl get_ancestors_impl]
lemmas get_root_node_locs_def = a_get_root_node_locs_def[folded get_root_node_locs_impl  
                                                         get_ancestors_locs_impl]

lemma get_ancestors_pure [simp]:
  "pure (get_ancestors ptr) h"
proof -
  have "\<forall>ptr h h' x. h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>h h' \<longrightarrow> h = h'"
  proof (induct rule: a_get_ancestors.fixp_induct[folded get_ancestors_impl])
    case 1
    then show ?case
      by(rule admissible_dom_prog)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 f)
    then show ?case
      using get_parent_pure
      apply(auto simp add: pure_returns_heap_eq pure_def 
                 split: option.splits 
                 elim!: bind_returns_heap_E bind_returns_result_E 
                 dest!: pure_returns_heap_eq[rotated, OF check_in_heap_pure])[1]
      apply (meson option.simps(3) returns_result_eq)
      by (metis get_parent_pure pure_returns_heap_eq)
  qed
  then show ?thesis
    by (meson pure_eq_iff)
qed


lemma get_root_node_pure [simp]: "pure (get_root_node ptr) h"
  by(auto simp add: get_root_node_def bind_pure_I)


lemma get_ancestors_ptr_in_heap:
  assumes "h \<turnstile> ok (get_ancestors ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms 
  by(auto simp add: get_ancestors_def check_in_heap_ptr_in_heap 
          elim!: bind_is_OK_E  dest: is_OK_returns_result_I)

lemma get_ancestors_ptr:
  assumes "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
  shows "ptr \<in> set ancestors"
  using assms
  apply(simp add: get_ancestors_def) 
  by(auto  elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)

lemma get_ancestors_not_node:
  assumes "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
  assumes "\<not>is_node_ptr_kind ptr"
  shows "ancestors = [ptr]"
  using assms
  apply(simp add: get_ancestors_def) 
  by(auto elim!: bind_returns_result_E2 split: option.splits)

lemma get_root_node_no_parent: 
  "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None \<Longrightarrow> h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
  apply(auto simp add: check_in_heap_def get_root_node_def get_ancestors_def 
             intro!: bind_pure_returns_result_I )[1]
  using get_parent_ptr_in_heap by blast

end

locale l_get_ancestors = l_get_ancestors_defs +
  assumes get_ancestors_pure [simp]: "pure (get_ancestors node_ptr) h"
  assumes get_ancestors_ptr_in_heap: "h \<turnstile> ok (get_ancestors ptr) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  assumes get_ancestors_ptr: "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors \<Longrightarrow> ptr \<in> set ancestors"

locale l_get_root_node = l_get_root_node_defs + l_get_parent_defs +
  assumes get_root_node_pure[simp]: 
   "pure (get_root_node ptr) h"
  assumes get_root_node_no_parent: 
   "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None \<Longrightarrow> h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"

global_interpretation l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs
  defines get_root_node = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_root_node get_parent"
      and get_root_node_locs = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_root_node_locs get_parent_locs"
      and get_ancestors = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_ancestors get_parent"
      and get_ancestors_locs = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_ancestors_locs get_parent_locs"
  .
declare a_get_ancestors.simps [code]

interpretation 
  i_get_root_node?: l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr known_ptrs get_parent get_parent_locs 
                    get_child_nodes get_child_nodes_locs get_ancestors get_ancestors_locs 
                    get_root_node get_root_node_locs
  using instances
  apply(simp add: l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def)
  by(simp add: get_root_node_def get_root_node_locs_def get_ancestors_def get_ancestors_locs_def)
declare l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_ancestors_is_l_get_ancestors [instances]: "l_get_ancestors get_ancestors"
  unfolding l_get_ancestors_def
  using get_ancestors_pure get_ancestors_ptr get_ancestors_ptr_in_heap
  by blast

lemma get_root_node_is_l_get_root_node [instances]: "l_get_root_node get_root_node get_parent"
  apply(simp add: l_get_root_node_def)
  using get_root_node_no_parent
  by fast


paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_ancestors\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_parent
    set_disconnected_nodes set_disconnected_nodes_locs get_parent get_parent_locs
  + l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs 
    get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  + l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
     type_wf set_disconnected_nodes set_disconnected_nodes_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
  and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma set_disconnected_nodes_get_ancestors: 
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_ancestors_locs. r h h'))"
  by(auto simp add: get_parent_locs_def set_disconnected_nodes_locs_def get_ancestors_locs_def 
                    all_args_def)
end

locale l_set_disconnected_nodes_get_ancestors = l_set_disconnected_nodes_defs + l_get_ancestors_defs +
  assumes set_disconnected_nodes_get_ancestors: 
    "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_ancestors_locs. r h h'))"

interpretation
  i_set_disconnected_nodes_get_ancestors?: l_set_disconnected_nodes_get_ancestors\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr 
                                           set_disconnected_nodes set_disconnected_nodes_locs 
                                           get_child_nodes get_child_nodes_locs get_parent 
                                           get_parent_locs type_wf known_ptrs get_ancestors 
                                           get_ancestors_locs get_root_node get_root_node_locs
  using instances
  by (simp add: l_set_disconnected_nodes_get_ancestors\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)           
declare l_set_disconnected_nodes_get_ancestors\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma set_disconnected_nodes_get_ancestors_is_l_set_disconnected_nodes_get_ancestors [instances]:
  "l_set_disconnected_nodes_get_ancestors set_disconnected_nodes_locs get_ancestors_locs"
  using instances
  apply(simp add: l_set_disconnected_nodes_get_ancestors_def)
  using set_disconnected_nodes_get_ancestors
  by fast



subsubsection \<open>get\_owner\_document\<close>
                                                                            
locale l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_get_root_node_defs get_root_node get_root_node_locs
  for get_root_node :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
  and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin

definition a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) node_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where                                                                                   
    "a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr _ = do {
      root \<leftarrow> get_root_node (cast node_ptr);
      (case cast root of
        Some document_ptr \<Rightarrow> return document_ptr
      | None \<Rightarrow> do {
        ptrs \<leftarrow> document_ptr_kinds_M;
        candidates \<leftarrow> filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (root \<in> cast ` set disconnected_nodes)
        }) ptrs;
        return (hd candidates)
      })
    }"

definition 
  a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) document_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where
    "a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr _ = do {
      document_ptrs \<leftarrow> document_ptr_kinds_M;
      (if document_ptr \<in> set document_ptrs then return document_ptr else error SegmentationFault)}"

definition 
  a_get_owner_document_tups :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> unit 
                                                 \<Rightarrow> (_, (_) document_ptr) dom_prog)) list"
  where
     "a_get_owner_document_tups = [
        (is_element_ptr, a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_character_data_ptr, a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast),
        (is_document_ptr, a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)
      ]"

definition a_get_owner_document :: "(_) object_ptr \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where
    "a_get_owner_document ptr = invoke a_get_owner_document_tups ptr ()"
end

locale l_get_owner_document_defs =
  fixes get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) document_ptr) dom_prog"
                                                     
locale l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_known_ptr known_ptr +
  l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_get_root_node get_root_node get_root_node_locs +
  l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs get_disconnected_nodes 
                                  get_disconnected_nodes_locs +
  l_get_owner_document_defs get_owner_document
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
  and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_owner_document :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog" +
  assumes known_ptr_impl: "known_ptr = a_known_ptr"
  assumes get_owner_document_impl: "get_owner_document = a_get_owner_document"
begin
lemmas known_ptr_def = known_ptr_impl[unfolded a_known_ptr_def]
lemmas get_owner_document_def = a_get_owner_document_def[folded get_owner_document_impl]

lemma get_owner_document_split:
  "P (invoke (a_get_owner_document_tups @ xs) ptr ()) =
    ((known_ptr ptr \<longrightarrow> P (get_owner_document ptr))
    \<and> (\<not>(known_ptr ptr) \<longrightarrow> P (invoke xs ptr ())))"
  by(auto simp add: get_owner_document_def a_get_owner_document_tups_def known_ptr_def 
                    CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs 
                    NodeClass.known_ptr_defs 
          split: invoke_splits option.splits)

lemma get_owner_document_split_asm:
  "P (invoke (a_get_owner_document_tups @ xs) ptr ()) =
    (\<not>((known_ptr ptr \<and> \<not>P (get_owner_document ptr))
    \<or> (\<not>(known_ptr ptr) \<and> \<not>P (invoke xs ptr ()))))"
  by(auto simp add: get_owner_document_def a_get_owner_document_tups_def known_ptr_def 
                    CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs 
                    NodeClass.known_ptr_defs 
          split: invoke_splits)
lemmas get_owner_document_splits = get_owner_document_split get_owner_document_split_asm

lemma get_owner_document_pure [simp]:
  "pure (get_owner_document ptr) h"
proof -
  have "\<And>node_ptr. pure (a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr ()) h"
    by(auto simp add: a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
                 intro!: bind_pure_I filter_M_pure_I 
                 split: option.splits)
  moreover have "\<And>document_ptr. pure (a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr ()) h"
    by(auto simp add: a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def bind_pure_I)
  ultimately show ?thesis
    by(auto simp add: get_owner_document_def a_get_owner_document_tups_def 
            intro!: bind_pure_I 
            split: invoke_splits)
qed

lemma get_owner_document_ptr_in_heap:
  assumes "h \<turnstile> ok (get_owner_document ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms 
  by(auto simp add: get_owner_document_def invoke_ptr_in_heap dest: is_OK_returns_heap_I)
end

locale l_get_owner_document = l_get_owner_document_defs +
  assumes get_owner_document_ptr_in_heap: 
    "h \<turnstile> ok (get_owner_document ptr) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  assumes get_owner_document_pure [simp]: 
    "pure (get_owner_document ptr) h"

global_interpretation l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs 
                                                      get_disconnected_nodes get_disconnected_nodes_locs
  defines get_owner_document_tups = 
          "l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document_tups get_root_node get_disconnected_nodes"
     and get_owner_document = 
         "l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document get_root_node get_disconnected_nodes"
     and get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r = 
         "l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r get_root_node get_disconnected_nodes"
  .
interpretation
  i_get_owner_document?: l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs known_ptr type_wf 
                         get_disconnected_nodes get_disconnected_nodes_locs get_root_node 
                         get_root_node_locs get_owner_document
  using instances
     apply(auto simp add: l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def)[1]
  by(auto simp add: get_owner_document_tups_def get_owner_document_def get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)[1]
declare l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_owner_document_is_l_get_owner_document [instances]: 
  "l_get_owner_document get_owner_document"
  using get_owner_document_ptr_in_heap
  by(auto simp add: l_get_owner_document_def)

subsubsection \<open>remove\_child\<close>

locale l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_set_child_nodes_defs set_child_nodes set_child_nodes_locs +
  l_get_parent_defs get_parent get_parent_locs +
  l_get_owner_document_defs get_owner_document +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_owner_document :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin
definition a_remove_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  where
    "a_remove_child ptr child = do {
      children \<leftarrow> get_child_nodes ptr;
      if child \<notin> set children then
        error NotFoundError
      else do {
        owner_document \<leftarrow> get_owner_document (cast child);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (child # disc_nodes);
        set_child_nodes ptr (remove1 child children)
      }
    }"

definition a_remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_remove_child_locs ptr owner_document = set_child_nodes_locs ptr 
                                              \<union> set_disconnected_nodes_locs owner_document"

definition a_remove :: "(_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  where
    "a_remove node_ptr = do {
      parent_opt \<leftarrow> get_parent node_ptr;
      (case parent_opt of
        Some parent \<Rightarrow> do {
          a_remove_child parent node_ptr;
          return ()
        }
      | None \<Rightarrow> return ())
    }"
end

locale l_remove_child_defs =
  fixes remove_child :: "(_::linorder) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  fixes remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_remove_defs = 
  fixes remove :: "(_) node_ptr \<Rightarrow> (_, unit) dom_prog"

locale l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_remove_child_defs +
  l_remove_defs +
  l_get_parent +
  l_get_owner_document +
  l_set_child_nodes_get_child_nodes +
  l_set_child_nodes_get_disconnected_nodes +
  l_set_disconnected_nodes_get_disconnected_nodes +
  l_set_disconnected_nodes_get_child_nodes +
  assumes remove_child_impl: "remove_child = a_remove_child"
  assumes remove_child_locs_impl: "remove_child_locs = a_remove_child_locs"
  assumes remove_impl: "remove = a_remove"
begin
lemmas remove_child_def = a_remove_child_def[folded remove_child_impl]
lemmas remove_child_locs_def = a_remove_child_locs_def[folded remove_child_locs_impl]
lemmas remove_def = a_remove_def[folded remove_child_impl remove_impl]

lemma remove_child_ptr_in_heap:
  assumes "h \<turnstile> ok (remove_child ptr child)"
  shows "ptr |\<in>| object_ptr_kinds h"
proof -
  obtain children where children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    using assms
    by(auto simp add: remove_child_def)
  moreover have "children \<noteq> []"
    using assms calculation
    by(auto simp add: remove_child_def elim!: bind_is_OK_E2)
  ultimately show ?thesis
    using assms(1) get_child_nodes_ptr_in_heap by blast 
qed

lemma remove_child_in_disconnected_nodes:
  (* assumes "known_ptrs h" *)
  assumes "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r owner_document"
  assumes "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
  shows "child \<in> set disc_nodes"
proof -
  obtain prev_disc_nodes h2 children where
    disc_nodes: "h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r prev_disc_nodes" and
    h2: "h \<turnstile> set_disconnected_nodes owner_document (child # prev_disc_nodes) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes ptr (remove1 child children) \<rightarrow>\<^sub>h h'"
    using assms(1)
    apply(auto simp add: remove_child_def 
               elim!: bind_returns_heap_E 
               dest!: returns_result_eq[OF assms(2)] pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                      pure_returns_heap_eq[rotated, OF get_child_nodes_pure] 
               split: if_splits)[1]
    by (metis get_disconnected_nodes_pure pure_returns_heap_eq)
  have "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
    apply(rule reads_writes_separate_backwards[OF get_disconnected_nodes_reads 
               set_child_nodes_writes h' assms(3)])
    by (simp add: set_child_nodes_get_disconnected_nodes)
  then show ?thesis
    by (metis (no_types, lifting) h2 set_disconnected_nodes_get_disconnected_nodes 
                                  list.set_intros(1) select_result_I2)
qed

lemma remove_child_writes [simp]: 
  "writes (remove_child_locs ptr |h \<turnstile> get_owner_document (cast child)|\<^sub>r) (remove_child ptr child) h h'"
  apply(auto simp add: remove_child_def intro!: writes_bind_pure[OF get_child_nodes_pure] 
                       writes_bind_pure[OF get_owner_document_pure] 
                       writes_bind_pure[OF get_disconnected_nodes_pure])[1]
  by(auto simp add: remove_child_locs_def set_disconnected_nodes_writes writes_union_right_I 
                    set_child_nodes_writes writes_union_left_I 
          intro!: writes_bind)

lemma remove_writes: 
  "writes (remove_child_locs (the |h \<turnstile> get_parent child|\<^sub>r) |h \<turnstile> get_owner_document (cast child)|\<^sub>r) (remove child) h h'"
  by(auto simp add: remove_def intro!: writes_bind_pure split: option.splits)

lemma remove_child_children_subset:
  assumes "h \<turnstile> remove_child parent child \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "set children' \<subseteq> set children"
proof -
  obtain ptr_children owner_document h2 disc_nodes where
    owner_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r owner_document" and
    ptr_children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r ptr_children" and
    disc_nodes: "h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes" and
    h2: "h \<turnstile> set_disconnected_nodes owner_document (child # disc_nodes) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes parent (remove1 child ptr_children) \<rightarrow>\<^sub>h h'"
    using assms(1)
    by(auto simp add: remove_child_def 
                 elim!: bind_returns_heap_E 
                 dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                        pure_returns_heap_eq[rotated, OF get_disconnected_nodes_pure] 
                        pure_returns_heap_eq[rotated, OF get_child_nodes_pure] 
                 split: if_splits)
  have "parent |\<in>| object_ptr_kinds h"
    using get_child_nodes_ptr_in_heap ptr_children by blast
  have "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                      OF set_disconnected_nodes_writes h2])
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved 
    by (auto simp add: reflp_def transp_def)
  have "type_wf h2"
    using type_wf writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", 
                                         OF set_disconnected_nodes_writes h2]
      using  set_disconnected_nodes_types_preserved  
      by(auto simp add: reflp_def transp_def)
  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
   using get_child_nodes_reads set_disconnected_nodes_writes h2 assms(2)
      apply(rule reads_writes_separate_forwards)
      by (simp add: set_disconnected_nodes_get_child_nodes)
  moreover have "h2 \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r ptr_children"
    using get_child_nodes_reads set_disconnected_nodes_writes h2 ptr_children
      apply(rule reads_writes_separate_forwards)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    moreover have 
      "ptr \<noteq> parent \<Longrightarrow> h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_child_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (metis set_child_nodes_get_child_nodes_different_pointers)
  moreover have "h' \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r remove1 child ptr_children"
    using h' set_child_nodes_get_child_nodes  known_ptrs type_wf known_ptrs_known_ptr 
              \<open>parent |\<in>| object_ptr_kinds h\<close> \<open>object_ptr_kinds h = object_ptr_kinds h2\<close> \<open>type_wf h2\<close> 
              by fast
  moreover have "set ( remove1 child ptr_children) \<subseteq> set ptr_children"
    by (simp add: set_remove1_subset)
  ultimately show ?thesis
    by (metis assms(3) order_refl returns_result_eq)
qed


lemma remove_child_pointers_preserved:
  assumes "w \<in> remove_child_locs ptr owner_document"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms
  using set_child_nodes_pointers_preserved
  using set_disconnected_nodes_pointers_preserved
  unfolding remove_child_locs_def
  by auto

lemma remove_child_types_preserved:
  assumes "w \<in> remove_child_locs ptr owner_document"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms
  using set_child_nodes_types_preserved
  using set_disconnected_nodes_types_preserved
  unfolding remove_child_locs_def
  by auto
end

locale l_remove_child = l_type_wf + l_known_ptrs + l_remove_child_defs + l_get_owner_document_defs 
                      + l_get_child_nodes_defs + l_get_disconnected_nodes_defs +
  assumes remove_child_writes: 
  "writes (remove_child_locs object_ptr |h \<turnstile> get_owner_document (cast child)|\<^sub>r) (remove_child object_ptr child) h h'"
  assumes remove_child_pointers_preserved: 
  "w \<in> remove_child_locs ptr owner_document \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes remove_child_types_preserved: 
  "w \<in> remove_child_locs ptr owner_document \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  assumes remove_child_in_disconnected_nodes:
    "known_ptrs h \<Longrightarrow> h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'
    \<Longrightarrow> h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r owner_document
    \<Longrightarrow> h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes
    \<Longrightarrow> child \<in> set disc_nodes"
  assumes remove_child_ptr_in_heap: "h \<turnstile> ok (remove_child ptr child) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  assumes remove_child_children_subset:
    "known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow> h \<turnstile> remove_child parent child \<rightarrow>\<^sub>h h'
    \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children
    \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'
    \<Longrightarrow> set children' \<subseteq> set children"

locale l_remove


global_interpretation l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs set_child_nodes 
                                                set_child_nodes_locs get_parent get_parent_locs 
                                                get_owner_document get_disconnected_nodes 
                                                get_disconnected_nodes_locs set_disconnected_nodes 
                                                set_disconnected_nodes_locs
  defines remove = 
    "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove get_child_nodes set_child_nodes get_parent get_owner_document 
                                        get_disconnected_nodes set_disconnected_nodes"
  and remove_child = 
    "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove_child get_child_nodes set_child_nodes get_owner_document 
                                              get_disconnected_nodes set_disconnected_nodes"
  and remove_child_locs = 
    "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove_child_locs set_child_nodes_locs set_disconnected_nodes_locs"
  .                                                                
interpretation
  i_remove_child?: l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs set_child_nodes 
                   set_child_nodes_locs get_parent get_parent_locs get_owner_document 
                   get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
                   set_disconnected_nodes_locs remove_child remove_child_locs remove type_wf 
                   known_ptr known_ptrs
  using instances
  apply(simp add: l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def)
  by(simp add: remove_child_def remove_child_locs_def remove_def)
declare l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma remove_child_is_l_remove_child [instances]: 
  "l_remove_child type_wf known_ptr known_ptrs remove_child remove_child_locs get_owner_document 
                  get_child_nodes get_disconnected_nodes"
  using instances
  apply(auto simp add: l_remove_child_def l_remove_child_axioms_def)[1] (*slow, ca 1min *)
  using remove_child_pointers_preserved apply(blast)
  using remove_child_pointers_preserved apply(blast)
  using remove_child_types_preserved apply(blast)
  using remove_child_types_preserved apply(blast)
  using remove_child_in_disconnected_nodes apply(blast)
  using remove_child_ptr_in_heap  apply(blast)
  using remove_child_children_subset  apply(blast)
  done



subsubsection \<open>adopt\_node\<close>

locale l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_owner_document_defs get_owner_document +
  l_get_parent_defs get_parent get_parent_locs +
  l_remove_child_defs remove_child remove_child_locs +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs
  for get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and remove_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin
definition a_adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  where
    "a_adopt_node document node = do {
      old_document \<leftarrow> get_owner_document (cast node);
      parent_opt \<leftarrow> get_parent node;
      (case parent_opt of
        Some parent \<Rightarrow> do {
          remove_child parent node
        } | None \<Rightarrow> do {
          return ()
        });
      (if document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes document;
        set_disconnected_nodes document (node # disc_nodes)
      } else do {
        return ()
      })
    }"

definition 
  a_adopt_node_locs :: "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_adopt_node_locs parent owner_document document_ptr = 
    ((if parent = None 
      then {} 
      else remove_child_locs (the parent) owner_document) \<union> set_disconnected_nodes_locs document_ptr 
                                                          \<union> set_disconnected_nodes_locs owner_document)"
end

locale l_adopt_node_defs =
  fixes 
  adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  fixes 
  adopt_node_locs :: "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"

global_interpretation l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_parent get_parent_locs remove_child 
                                              remove_child_locs get_disconnected_nodes 
                                              get_disconnected_nodes_locs set_disconnected_nodes 
                                              set_disconnected_nodes_locs
  defines adopt_node = "l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_adopt_node get_owner_document get_parent remove_child 
                                                             get_disconnected_nodes set_disconnected_nodes"
      and adopt_node_locs = "l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_adopt_node_locs 
                                                      remove_child_locs set_disconnected_nodes_locs"
  .

locale l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
    get_owner_document get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes 
                       get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  + l_adopt_node_defs
    adopt_node adopt_node_locs
  + l_get_owner_document
    get_owner_document
  + l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  + l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    get_child_nodes get_child_nodes_locs set_child_nodes set_child_nodes_locs get_parent 
    get_parent_locs get_owner_document get_disconnected_nodes get_disconnected_nodes_locs 
    set_disconnected_nodes set_disconnected_nodes_locs remove_child remove_child_locs remove type_wf 
    known_ptr known_ptrs
  + l_set_disconnected_nodes_get_disconnected_nodes
    type_wf get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
    set_disconnected_nodes_locs
  for get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and remove_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and adopt_node_locs :: "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr 
                          \<Rightarrow> ((_) heap, exception, unit) prog set"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and remove :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog" +
  assumes adopt_node_impl: "adopt_node = a_adopt_node"
  assumes adopt_node_locs_impl: "adopt_node_locs = a_adopt_node_locs"
begin
lemmas adopt_node_def = a_adopt_node_def[folded adopt_node_impl]
lemmas adopt_node_locs_def = a_adopt_node_locs_def[folded adopt_node_locs_impl]

lemma adopt_node_writes:
  shows "writes (adopt_node_locs |h \<turnstile> get_parent node|\<^sub>r |h 
         \<turnstile> get_owner_document (cast node)|\<^sub>r document_ptr) (adopt_node document_ptr node) h h'"
  apply(auto simp add: adopt_node_def adopt_node_locs_def 
             intro!: writes_bind_pure[OF get_owner_document_pure] writes_bind_pure[OF get_parent_pure] 
                     writes_bind_pure[OF get_disconnected_nodes_pure] 
             split: option.splits)[1]
  apply(auto intro!: writes_bind)[1]
  apply (simp add: set_disconnected_nodes_writes writes_union_right_I)
    apply (simp add: set_disconnected_nodes_writes writes_union_left_I writes_union_right_I)
   apply(auto intro!: writes_bind)[1]
  apply (metis (no_types, lifting) remove_child_writes select_result_I2 writes_union_left_I)
    apply (simp add: set_disconnected_nodes_writes writes_union_right_I)
  by(auto intro: writes_subset[OF set_disconnected_nodes_writes] writes_subset[OF remove_child_writes])

lemma adopt_node_children_subset:
  assumes "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "set children' \<subseteq> set children"
proof -
  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast node) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node \<rightarrow>\<^sub>r parent_opt" and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> do { remove_child parent node } | None \<Rightarrow> do { return ()}) \<rightarrow>\<^sub>h h2" 
    and
    h': "h2 \<turnstile> (if owner_document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (node # disc_nodes)
      } else do { return () }) \<rightarrow>\<^sub>h h'"
    using assms(1)
    by(auto simp add: adopt_node_def 
            elim!: bind_returns_heap_E 
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                   pure_returns_heap_eq[rotated, OF get_parent_pure])

  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
  proof (cases "owner_document \<noteq> old_document")
    case True
    then obtain h3 old_disc_nodes disc_nodes where
      old_disc_nodes: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
      h3: "h2 \<turnstile> set_disconnected_nodes old_document (remove1 node old_disc_nodes) \<rightarrow>\<^sub>h h3" and
      old_disc_nodes: "h3 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes" and
      h': "h3 \<turnstile> set_disconnected_nodes owner_document (node # disc_nodes) \<rightarrow>\<^sub>h h'"
      using h'
      by(auto elim!: bind_returns_heap_E 
                     bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] ) 
    have "h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
      using get_child_nodes_reads set_disconnected_nodes_writes h' assms(3)
      apply(rule reads_writes_separate_backwards)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    show ?thesis
      using get_child_nodes_reads set_disconnected_nodes_writes h3 \<open>h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'\<close>
      apply(rule reads_writes_separate_backwards)
      by (simp add: set_disconnected_nodes_get_child_nodes)
  next
    case False
    then show ?thesis
      using h' assms(3) by(auto)
  qed

  show ?thesis
  proof (insert h2, induct parent_opt)
    case None
    then show ?case
      using assms
      by(auto dest!: returns_result_eq[OF \<open>h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'\<close>])
  next
    case (Some option)
    then show ?case 
      using assms(2) \<open>h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'\<close> remove_child_children_subset known_ptrs type_wf 
      by simp
  qed
qed

lemma adopt_node_child_in_heap:
  assumes "h \<turnstile> ok (adopt_node document_ptr child)"
  shows "child |\<in>| node_ptr_kinds h"
  using assms
  apply(auto simp add: adopt_node_def elim!: bind_is_OK_E)[1]
  using get_owner_document_pure get_parent_ptr_in_heap pure_returns_heap_eq
  by fast

lemma adopt_node_pointers_preserved:
  assumes "w \<in> adopt_node_locs parent owner_document document_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms
  using set_disconnected_nodes_pointers_preserved
  using remove_child_pointers_preserved
  unfolding adopt_node_locs_def
  by (auto split: if_splits)

lemma adopt_node_types_preserved:
  assumes "w \<in> adopt_node_locs parent owner_document document_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms
  using remove_child_types_preserved
  using set_disconnected_nodes_types_preserved
  unfolding adopt_node_locs_def
  by (auto split: if_splits)
end

locale l_adopt_node = l_type_wf + l_known_ptrs + l_get_parent_defs + l_adopt_node_defs + l_get_child_nodes_defs + l_get_owner_document_defs +
  assumes adopt_node_writes: 
  "writes (adopt_node_locs |h \<turnstile> get_parent node|\<^sub>r 
           |h \<turnstile> get_owner_document (cast node)|\<^sub>r document_ptr) (adopt_node document_ptr node) h h'"
  assumes adopt_node_pointers_preserved: 
  "w \<in> adopt_node_locs parent owner_document document_ptr 
   \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes adopt_node_types_preserved: 
  "w \<in> adopt_node_locs parent owner_document document_ptr 
   \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  assumes adopt_node_child_in_heap: 
  "h \<turnstile> ok (adopt_node document_ptr child) \<Longrightarrow> child |\<in>| node_ptr_kinds h"
  assumes adopt_node_children_subset:
  "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
     \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children' 
     \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow> set children' \<subseteq> set children"

interpretation
  i_adopt_node?: l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_owner_document get_parent get_parent_locs remove_child 
                 remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs 
                 set_disconnected_nodes set_disconnected_nodes_locs adopt_node adopt_node_locs 
                 known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes 
                 set_child_nodes_locs remove
  apply(unfold_locales)
  by(auto simp add: adopt_node_def adopt_node_locs_def)                     
declare l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma adopt_node_is_l_adopt_node [instances]: 
  "l_adopt_node type_wf known_ptr known_ptrs get_parent adopt_node adopt_node_locs get_child_nodes 
                get_owner_document"
  using instances
  by (simp add: l_adopt_node_axioms_def adopt_node_child_in_heap adopt_node_children_subset 
                adopt_node_pointers_preserved adopt_node_types_preserved adopt_node_writes 
                l_adopt_node_def)



subsubsection \<open>insert\_before\<close>
                                                       
locale l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_parent_defs get_parent get_parent_locs
  + l_get_child_nodes_defs get_child_nodes get_child_nodes_locs
  + l_set_child_nodes_defs set_child_nodes set_child_nodes_locs
  + l_get_ancestors_defs get_ancestors get_ancestors_locs
  + l_adopt_node_defs adopt_node adopt_node_locs
  + l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs
  + l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs
  + l_get_owner_document_defs get_owner_document
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and adopt_node_locs :: "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr 
                                                \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_owner_document :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
begin

definition a_next_sibling :: "(_) node_ptr \<Rightarrow> (_, (_) node_ptr option) dom_prog"
  where
    "a_next_sibling node_ptr = do {
      parent_opt \<leftarrow> get_parent node_ptr;
      (case parent_opt of
        Some parent \<Rightarrow> do {
          children \<leftarrow> get_child_nodes parent;
          (case (dropWhile (\<lambda>ptr. ptr = node_ptr) (dropWhile (\<lambda>ptr. ptr \<noteq> node_ptr) children)) of
            x#_ \<Rightarrow> return (Some x)
          | [] \<Rightarrow> return None)}
      | None \<Rightarrow> return None)
    }"

fun insert_before_list :: "'xyz \<Rightarrow> 'xyz option \<Rightarrow> 'xyz list \<Rightarrow> 'xyz list"
  where
    "insert_before_list v (Some reference) (x#xs) = (if reference = x
      then v#x#xs else x # insert_before_list v (Some reference) xs)"
    | "insert_before_list v (Some _) [] = [v]"
    | "insert_before_list v None xs = xs @ [v]"

definition a_insert_node :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_) node_ptr option
  \<Rightarrow> (_, unit) dom_prog"
  where
    "a_insert_node ptr new_child reference_child_opt = do {
      children \<leftarrow> get_child_nodes ptr;
      set_child_nodes ptr (insert_before_list new_child reference_child_opt children)
    }"

definition a_ensure_pre_insertion_validity :: "(_) node_ptr \<Rightarrow> (_) object_ptr
  \<Rightarrow> (_) node_ptr option \<Rightarrow> (_, unit) dom_prog"
  where
    "a_ensure_pre_insertion_validity node parent child_opt = do {
      (if is_character_data_ptr_kind parent
        then error HierarchyRequestError else return ());
      ancestors \<leftarrow> get_ancestors parent;
      (if cast node \<in> set ancestors then error HierarchyRequestError else return ());
      (case child_opt of
        Some child \<Rightarrow> do {
          child_parent \<leftarrow> get_parent child;
          (if child_parent \<noteq> Some parent then error NotFoundError else return ())}
      | None \<Rightarrow> return ());
      children \<leftarrow> get_child_nodes parent;
      (if children \<noteq> [] \<and> is_document_ptr parent
        then error HierarchyRequestError else return ());
      (if is_character_data_ptr node \<and> is_document_ptr parent
        then error HierarchyRequestError else return ())
    }"

definition a_insert_before :: "(_) object_ptr \<Rightarrow> (_) node_ptr
  \<Rightarrow> (_) node_ptr option \<Rightarrow> (_, unit) dom_prog"
  where
    "a_insert_before ptr node child = do {
      a_ensure_pre_insertion_validity node ptr child;
      reference_child \<leftarrow> (if Some node = child
        then a_next_sibling node                                         
        else return child);
      owner_document \<leftarrow> get_owner_document ptr;
      adopt_node owner_document node;
      disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
      set_disconnected_nodes owner_document (remove1 node disc_nodes);
      a_insert_node ptr node reference_child
    }"

definition a_insert_before_locs :: "(_) object_ptr \<Rightarrow> (_) object_ptr option \<Rightarrow> (_) document_ptr 
                                                   \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_insert_before_locs ptr old_parent child_owner_document ptr_owner_document =
      adopt_node_locs old_parent child_owner_document ptr_owner_document \<union>
      set_child_nodes_locs ptr \<union>
      set_disconnected_nodes_locs ptr_owner_document"
end

locale l_insert_before_defs =
  fixes insert_before :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_) node_ptr option \<Rightarrow> (_, unit) dom_prog"
  fixes insert_before_locs :: "(_) object_ptr \<Rightarrow> (_) object_ptr option \<Rightarrow> (_) document_ptr 
                                              \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"

locale l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_insert_before_defs
begin
definition "a_append_child ptr child = insert_before ptr child None"
end

locale l_append_child_defs =
  fixes append_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
                                                                 
locale l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
    get_parent get_parent_locs get_child_nodes get_child_nodes_locs set_child_nodes 
    set_child_nodes_locs get_ancestors get_ancestors_locs adopt_node adopt_node_locs 
    set_disconnected_nodes set_disconnected_nodes_locs get_disconnected_nodes 
    get_disconnected_nodes_locs get_owner_document
  + l_insert_before_defs
    insert_before insert_before_locs
  + l_append_child_defs
    append_child
  + l_set_child_nodes_get_child_nodes
    type_wf known_ptr get_child_nodes get_child_nodes_locs set_child_nodes set_child_nodes_locs
  + l_get_ancestors
    get_ancestors get_ancestors_locs
  + l_adopt_node
    type_wf known_ptr known_ptrs get_parent get_parent_locs adopt_node adopt_node_locs 
    get_child_nodes get_child_nodes_locs get_owner_document
  + l_set_disconnected_nodes
    type_wf set_disconnected_nodes set_disconnected_nodes_locs
  + l_get_disconnected_nodes
    type_wf get_disconnected_nodes get_disconnected_nodes_locs
  + l_get_owner_document
    get_owner_document
  + l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  + l_set_disconnected_nodes_get_child_nodes
    set_disconnected_nodes set_disconnected_nodes_locs get_child_nodes get_child_nodes_locs
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and adopt_node_locs :: "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr 
                                                \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_owner_document :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and insert_before :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_) node_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
  and insert_before_locs :: "(_) object_ptr \<Rightarrow> (_) object_ptr option \<Rightarrow> (_) document_ptr 
                                            \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  and append_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool" +
  assumes insert_before_impl: "insert_before = a_insert_before"
  assumes insert_before_locs_impl: "insert_before_locs = a_insert_before_locs"
begin
lemmas insert_before_def = a_insert_before_def[folded insert_before_impl]
lemmas insert_before_locs_def = a_insert_before_locs_def[folded insert_before_locs_impl]

lemma next_sibling_pure [simp]:
  "pure (a_next_sibling new_child) h"
  by(auto simp add: a_next_sibling_def get_parent_pure intro!: bind_pure_I split: option.splits list.splits)

lemma insert_before_list_in_set: "x \<in> set (insert_before_list v ref xs) \<longleftrightarrow> x = v \<or> x \<in> set xs"
  apply(induct v ref xs rule: insert_before_list.induct)
  by(auto)

lemma insert_before_list_distinct: "x \<notin> set xs \<Longrightarrow> distinct xs \<Longrightarrow> distinct (insert_before_list x ref xs)"
  by (induct x ref xs rule: insert_before_list.induct)
     (auto simp add: insert_before_list_in_set)

lemma insert_before_list_subset: "set xs \<subseteq> set (insert_before_list x ref xs)"
  apply(induct x ref xs rule: insert_before_list.induct)
  by(auto)

lemma insert_before_list_node_in_set: "x \<in> set (insert_before_list x ref xs)"
  apply(induct x ref xs rule: insert_before_list.induct)
  by(auto)

lemma insert_node_writes: 
  "writes (set_child_nodes_locs ptr) (a_insert_node ptr new_child reference_child_opt) h h'"
  by(auto simp add: a_insert_node_def set_child_nodes_writes 
          intro!: writes_bind_pure[OF get_child_nodes_pure])

lemma ensure_pre_insertion_validity_pure [simp]:
  "pure (a_ensure_pre_insertion_validity node ptr child) h"
  by(auto simp add: a_ensure_pre_insertion_validity_def 
          intro!: bind_pure_I 
          split: option.splits)

lemma insert_before_reference_child_not_in_children:
  assumes "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
    and "ptr \<noteq> parent"
    and "\<not>is_character_data_ptr_kind ptr"
    and "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
    and "cast node \<notin> set ancestors"
  shows "h \<turnstile> insert_before ptr node (Some child) \<rightarrow>\<^sub>e NotFoundError"
proof -
  have "h \<turnstile> a_ensure_pre_insertion_validity node ptr (Some child) \<rightarrow>\<^sub>e NotFoundError"
    using assms unfolding insert_before_def a_ensure_pre_insertion_validity_def
    by auto (simp | rule bind_returns_error_I2)+
  then show ?thesis
    unfolding insert_before_def by auto
qed

lemma insert_before_child_in_heap:
  assumes "h \<turnstile> ok (insert_before ptr node reference_child)"
  shows "node |\<in>| node_ptr_kinds h"
  using assms
  apply(auto simp add: insert_before_def elim!: bind_is_OK_E)[1]
  by (metis (mono_tags, lifting) ensure_pre_insertion_validity_pure is_OK_returns_heap_I 
            l_get_owner_document.get_owner_document_pure local.adopt_node_child_in_heap 
            local.l_get_owner_document_axioms next_sibling_pure pure_returns_heap_eq return_pure)

lemma insert_node_children_remain_distinct:
    assumes insert_node: "h \<turnstile> a_insert_node ptr new_child reference_child_opt \<rightarrow>\<^sub>h h2"
    and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and "new_child \<notin> set children"
    and "\<And>ptr children. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
    and known_ptr: "known_ptr ptr"
    and type_wf: "type_wf h"
  shows "\<And>ptr children. h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
proof -
  fix ptr' children'
  assume a1: "h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children'"
  then show "distinct children'"
  proof (cases "ptr = ptr'")
    case True
    have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r (insert_before_list new_child reference_child_opt children)"
      using assms(1) assms(2) apply(auto simp add: a_insert_node_def elim!: bind_returns_heap_E)[1]
      using returns_result_eq set_child_nodes_get_child_nodes known_ptr type_wf
      using pure_returns_heap_eq by fastforce
    then show ?thesis
      using True a1 assms(2) assms(3) assms(4) insert_before_list_distinct returns_result_eq 
      by fastforce
  next
    case False
    have "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children'"
      using  get_child_nodes_reads insert_node_writes insert_node a1
      apply(rule reads_writes_separate_backwards)
      by (meson False set_child_nodes_get_child_nodes_different_pointers)
    then show ?thesis
      using assms(4) by blast
  qed
qed
                                               
lemma insert_before_writes: 
  "writes (insert_before_locs ptr |h \<turnstile> get_parent child|\<^sub>r 
       |h \<turnstile> get_owner_document (cast child)|\<^sub>r |h \<turnstile> get_owner_document ptr|\<^sub>r) (insert_before ptr child ref) h h'"
  apply(auto simp add: insert_before_def insert_before_locs_def a_insert_node_def 
      intro!: writes_bind)[1]
       apply (metis (no_types, hide_lams) ensure_pre_insertion_validity_pure local.adopt_node_writes 
                    local.get_owner_document_pure next_sibling_pure pure_returns_heap_eq 
                    select_result_I2 sup_commute writes_union_right_I)
      apply (metis (no_types, hide_lams) ensure_pre_insertion_validity_pure next_sibling_pure 
                   pure_returns_heap_eq select_result_I2 set_disconnected_nodes_writes 
                   writes_union_right_I)
     apply (simp add: set_child_nodes_writes writes_union_left_I writes_union_right_I)
    apply (metis (no_types, hide_lams) adopt_node_writes ensure_pre_insertion_validity_pure 
                 get_owner_document_pure pure_returns_heap_eq select_result_I2 writes_union_left_I)
   apply (metis (no_types, hide_lams) ensure_pre_insertion_validity_pure pure_returns_heap_eq 
                select_result_I2 set_disconnected_nodes_writes writes_union_right_I)
  by (simp add: set_child_nodes_writes writes_union_left_I writes_union_right_I)                      
end


locale l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_append_child_defs +
  l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +     
  assumes append_child_impl: "append_child = a_append_child"
begin

lemmas append_child_def = a_append_child_def[folded append_child_impl]
end

locale l_insert_before = l_insert_before_defs

locale l_append_child = l_append_child_defs

global_interpretation l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs get_child_nodes 
   get_child_nodes_locs set_child_nodes set_child_nodes_locs get_ancestors get_ancestors_locs 
   adopt_node adopt_node_locs set_disconnected_nodes set_disconnected_nodes_locs 
   get_disconnected_nodes get_disconnected_nodes_locs get_owner_document
  defines
    next_sibling = "l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_next_sibling get_parent get_child_nodes" and
    insert_node = "l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_insert_node get_child_nodes set_child_nodes" and
    ensure_pre_insertion_validity = "l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_ensure_pre_insertion_validity 
                                                     get_parent get_child_nodes get_ancestors" and
    insert_before = "l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_insert_before get_parent get_child_nodes 
                                   set_child_nodes get_ancestors adopt_node set_disconnected_nodes 
                                   get_disconnected_nodes get_owner_document" and
    insert_before_locs = "l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_insert_before_locs set_child_nodes_locs 
                                                        adopt_node_locs set_disconnected_nodes_locs"
  .

global_interpretation l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs insert_before
  defines append_child = "l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_append_child insert_before"
  .

interpretation                                           
  i_insert_before?: l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs get_child_nodes 
  get_child_nodes_locs set_child_nodes set_child_nodes_locs get_ancestors get_ancestors_locs 
  adopt_node adopt_node_locs set_disconnected_nodes set_disconnected_nodes_locs get_disconnected_nodes 
  get_disconnected_nodes_locs get_owner_document insert_before insert_before_locs append_child 
  type_wf known_ptr known_ptrs
  apply(simp add: l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
  by (simp add: insert_before_def insert_before_locs_def)
declare l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

interpretation i_append_child?: l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M append_child insert_before insert_before_locs
  apply(simp add: l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances append_child_def)
  done
declare l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]




subsubsection \<open>create\_element\<close>

locale l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_tag_type_defs set_tag_type set_tag_type_locs
  for get_disconnected_nodes :: 
      "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: 
      "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: 
      "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: 
      "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_tag_type :: 
      "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_tag_type_locs :: 
      "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin
definition a_create_element :: "(_) document_ptr \<Rightarrow> tag_type \<Rightarrow> (_, (_) element_ptr) dom_prog"
  where
    "a_create_element document_ptr tag = do {
      new_element_ptr \<leftarrow> new_element;
      set_tag_type new_element_ptr tag;
      disc_nodes \<leftarrow> get_disconnected_nodes document_ptr;
      set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes);
      return new_element_ptr
    }"
end

locale l_create_element_defs =
  fixes create_element :: "(_) document_ptr \<Rightarrow> tag_type \<Rightarrow> (_, (_) element_ptr) dom_prog"

global_interpretation l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_disconnected_nodes get_disconnected_nodes_locs 
                                                  set_disconnected_nodes set_disconnected_nodes_locs 
                                                  set_tag_type set_tag_type_locs
  defines 
  create_element = "l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_create_element get_disconnected_nodes 
                                                                set_disconnected_nodes set_tag_type"
  .

locale l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_create_element_defs +
  assumes create_element_impl: "create_element = a_create_element"
begin
lemmas create_element_def = a_create_element_def[folded create_element_impl]
end

locale l_create_element = l_create_element_defs

interpretation
  i_create_element?: l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs 
                     set_disconnected_nodes set_disconnected_nodes_locs set_tag_type 
                     set_tag_type_locs create_element
  by unfold_locales (simp add: create_element_def)
declare l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


subsubsection \<open>create\_character\_data\<close>

locale l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_set_val_defs set_val set_val_locs +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes_defs set_disconnected_nodes set_disconnected_nodes_locs
  for set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin
definition a_create_character_data :: "(_) document_ptr \<Rightarrow> string \<Rightarrow> (_, (_) character_data_ptr) dom_prog"
  where
    "a_create_character_data document_ptr text = do {
      new_character_data_ptr \<leftarrow> new_character_data;
      set_val new_character_data_ptr text;
      disc_nodes \<leftarrow> get_disconnected_nodes document_ptr;
      set_disconnected_nodes document_ptr (cast new_character_data_ptr # disc_nodes);
      return new_character_data_ptr
    }"
end

locale l_create_character_data_defs =
  fixes create_character_data :: "(_) document_ptr \<Rightarrow> string \<Rightarrow> (_, (_) character_data_ptr) dom_prog"

global_interpretation l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs set_val set_val_locs get_disconnected_nodes 
                     get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  defines create_character_data = "l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_create_character_data 
                                             set_val get_disconnected_nodes set_disconnected_nodes"
  .

locale l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_create_character_data_defs +
  assumes create_character_data_impl: "create_character_data = a_create_character_data"
begin
lemmas create_character_data_def = a_create_character_data_def[folded create_character_data_impl] 
end

locale l_create_character_data = l_create_character_data_defs

interpretation
  i_create_character_data?: l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_val set_val_locs get_disconnected_nodes 
                            get_disconnected_nodes_locs set_disconnected_nodes 
                            set_disconnected_nodes_locs create_character_data
  by unfold_locales (simp add: create_character_data_def)
declare l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>create\_character\_data\<close>

locale l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_create_document :: "(_, (_) document_ptr) dom_prog"
  where
    "a_create_document = new_document"
end

locale l_create_document_defs =
  fixes create_document :: "(_, (_) document_ptr) dom_prog"

global_interpretation l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  defines create_document = "l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_create_document"
  .

locale l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_create_document_defs +
  assumes create_document_impl: "create_document = a_create_document"
begin
lemmas 
  create_document_def = create_document_impl[unfolded create_document_def, unfolded a_create_document_def]
end

locale l_create_document = l_create_document_defs

interpretation
  i_create_document?: l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M create_document
  by(simp add: l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>tree\_order\<close>

locale l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
partial_function (dom_prog) a_to_tree_order :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_to_tree_order ptr = (do {
      children \<leftarrow> get_child_nodes ptr;
      treeorders \<leftarrow> map_M a_to_tree_order (map (cast) children);
      return (ptr # concat treeorders)
    })"
end

locale l_to_tree_order_defs =
  fixes to_tree_order :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"

global_interpretation l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs defines
  to_tree_order = "l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_to_tree_order get_child_nodes" .
declare a_to_tree_order.simps [code]

locale l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs +
  l_to_tree_order_defs to_tree_order
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog" +
  assumes to_tree_order_impl: "to_tree_order = a_to_tree_order"
begin
lemmas to_tree_order_def = a_to_tree_order.simps[folded to_tree_order_impl]

lemma to_tree_order_pure [simp]: "pure (to_tree_order ptr) h"
proof -
  have "\<forall>ptr h h' x. h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>h h' \<longrightarrow> h = h'"
  proof (induct rule: a_to_tree_order.fixp_induct[folded to_tree_order_impl])
    case 1
    then show ?case
      by (rule admissible_dom_prog)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 f)
    then have "\<And>x h. pure (f x) h"
      by (metis is_OK_returns_heap_E is_OK_returns_result_E pure_def)
    then have "\<And>xs h. pure (map_M f xs) h"
      by(rule map_M_pure_I)
    then show ?case
      by(auto elim!: bind_returns_heap_E2)
  qed
  then show ?thesis
    unfolding pure_def
    by (metis is_OK_returns_heap_E is_OK_returns_result_E)
qed
end

locale l_to_tree_order =
  fixes to_tree_order :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  assumes to_tree_order_pure [simp]: "pure (to_tree_order ptr) h"

interpretation 
  i_to_tree_order?: l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs 
                    to_tree_order
  apply(unfold_locales)
  by (simp add: to_tree_order_def)
declare l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma to_tree_order_is_l_to_tree_order [instances]: "l_to_tree_order to_tree_order"
  using to_tree_order_pure l_to_tree_order_def by blast



subsubsection \<open>first\_in\_tree\_order\<close>

locale l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_to_tree_order_defs to_tree_order
  for to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
begin
definition a_first_in_tree_order :: "(_) object_ptr \<Rightarrow> ((_) object_ptr 
                                \<Rightarrow> (_, 'result option) dom_prog) \<Rightarrow> (_, 'result option) dom_prog"
  where
    "a_first_in_tree_order ptr f = (do {
      tree_order \<leftarrow> to_tree_order ptr;
      results \<leftarrow> map_filter_M f tree_order;
      (case results of
        [] \<Rightarrow> return None
      | x#_\<Rightarrow> return (Some x))
    })"
end

locale l_first_in_tree_order_defs =
  fixes first_in_tree_order :: "(_) object_ptr \<Rightarrow> ((_) object_ptr \<Rightarrow> (_, 'result option) dom_prog) 
                                               \<Rightarrow> (_, 'result option) dom_prog"

global_interpretation l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order defines
  first_in_tree_order = "l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_first_in_tree_order to_tree_order" .

locale l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order +
  l_first_in_tree_order_defs first_in_tree_order
  for to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and first_in_tree_order :: "(_) object_ptr \<Rightarrow> ((_) object_ptr \<Rightarrow> ((_) heap, exception, 'result option) prog) 
                                             \<Rightarrow> ((_) heap, exception, 'result option) prog" +
assumes first_in_tree_order_impl: "first_in_tree_order = a_first_in_tree_order"
begin
lemmas first_in_tree_order_def = first_in_tree_order_impl[unfolded a_first_in_tree_order_def]
end

locale l_first_in_tree_order

interpretation i_first_in_tree_order?:
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order first_in_tree_order
  by unfold_locales (simp add: first_in_tree_order_def)
declare l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]



subsubsection \<open>get\_element\_by\<close>

locale l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_first_in_tree_order_defs first_in_tree_order +
  l_to_tree_order_defs to_tree_order +
  l_get_attribute_defs get_attribute get_attribute_locs
  for to_tree_order :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and first_in_tree_order :: "(_) object_ptr \<Rightarrow> ((_) object_ptr 
                              \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog) 
                              \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
  and get_attribute :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, char list option) prog"
  and get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_element_by_id :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr option) dom_prog"
  where
    "a_get_element_by_id ptr iden = first_in_tree_order ptr (\<lambda>ptr. (case cast ptr of
      Some element_ptr \<Rightarrow> do {
        id_opt \<leftarrow> get_attribute element_ptr ''id'';
        (if id_opt = Some iden then return (Some element_ptr) else return None)
      }
    | _ \<Rightarrow> return None
    ))"

definition a_get_elements_by_class_name :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr list) dom_prog"
  where
    "a_get_elements_by_class_name ptr class_name = to_tree_order ptr \<bind>
      map_filter_M (\<lambda>ptr. (case cast ptr of
        Some element_ptr \<Rightarrow> do {
          class_name_opt \<leftarrow> get_attribute element_ptr ''class'';
          (if class_name_opt = Some class_name then return (Some element_ptr) else return None)
        }
      | _ \<Rightarrow> return None))"

definition a_get_elements_by_tag_name :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr list) dom_prog"
  where
    "a_get_elements_by_tag_name ptr tag_name = to_tree_order ptr \<bind>
      map_filter_M (\<lambda>ptr. (case cast ptr of
        Some element_ptr \<Rightarrow> do {
          this_tag_name \<leftarrow> get_M element_ptr tag_type;
          (if this_tag_name = tag_name then return (Some element_ptr) else return None)
        }
      | _ \<Rightarrow> return None))"
end

locale l_get_element_by_defs =
  fixes get_element_by_id :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr option) dom_prog"
  fixes get_elements_by_class_name :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr list) dom_prog"
  fixes get_elements_by_tag_name :: "(_) object_ptr \<Rightarrow> attr_value \<Rightarrow> (_, (_) element_ptr list) dom_prog"

global_interpretation 
l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order first_in_tree_order get_attribute get_attribute_locs 
defines                      
  get_element_by_id = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_element_by_id first_in_tree_order get_attribute" 
and
  get_elements_by_class_name = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_class_name to_tree_order get_attribute" 
and
  get_elements_by_tag_name = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_tag_name to_tree_order" .

locale l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order first_in_tree_order get_attribute get_attribute_locs +
  l_get_element_by_defs get_element_by_id get_elements_by_class_name get_elements_by_tag_name +
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order first_in_tree_order +
  l_to_tree_order to_tree_order +
  l_get_attribute type_wf get_attribute get_attribute_locs
  for to_tree_order :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and first_in_tree_order :: "(_) object_ptr \<Rightarrow> ((_) object_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog) 
                                             \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
  and get_attribute :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, char list option) prog"
  and get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_element_by_id :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
  and get_elements_by_class_name :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
  and get_elements_by_tag_name :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
  and type_wf :: "(_) heap \<Rightarrow> bool" +
  assumes get_element_by_id_impl: "get_element_by_id = a_get_element_by_id"
  assumes get_elements_by_class_name_impl: "get_elements_by_class_name = a_get_elements_by_class_name"
  assumes get_elements_by_tag_name_impl: "get_elements_by_tag_name = a_get_elements_by_tag_name"
begin
lemmas 
  get_element_by_id_def = get_element_by_id_impl[unfolded a_get_element_by_id_def]
lemmas 
  get_elements_by_class_name_def = get_elements_by_class_name_impl[unfolded a_get_elements_by_class_name_def]
lemmas 
  get_elements_by_tag_name_def = get_elements_by_tag_name_impl[unfolded a_get_elements_by_tag_name_def]

lemma get_element_by_id_result_in_tree_order:
  assumes "h \<turnstile> get_element_by_id ptr iden \<rightarrow>\<^sub>r Some element_ptr"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  shows "cast element_ptr \<in> set to"
  using assms 
  by(auto simp add: get_element_by_id_def first_in_tree_order_def  
               elim!: map_filter_M_pure_E[where y=element_ptr]  bind_returns_result_E2 
               dest!: bind_returns_result_E3[rotated, OF assms(2), rotated] 
               intro!: map_filter_M_pure map_M_pure_I bind_pure_I 
               split: option.splits list.splits if_splits)

lemma get_elements_by_tag_name_pure [simp]: "pure (get_elements_by_tag_name ptr tag_name) h"
  by(auto simp add: get_elements_by_tag_name_def 
          intro!: bind_pure_I map_filter_M_pure 
          split: option.splits)
end

locale l_get_element_by = l_get_element_by_defs + l_to_tree_order_defs +
  assumes get_element_by_id_result_in_tree_order: 
          "h \<turnstile> get_element_by_id ptr iden \<rightarrow>\<^sub>r Some element_ptr \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to 
               \<Longrightarrow> cast element_ptr \<in> set to"
  assumes get_elements_by_tag_name_pure [simp]: "pure (get_elements_by_tag_name ptr tag_name) h"

interpretation 
  i_get_element_by?: l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order first_in_tree_order get_attribute 
                     get_attribute_locs get_element_by_id get_elements_by_class_name
                     get_elements_by_tag_name type_wf
  using instances
  apply(simp add: l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def)
  by(simp add: get_element_by_id_def get_elements_by_class_name_def get_elements_by_tag_name_def)
declare l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_element_by_is_l_get_element_by [instances]: 
  "l_get_element_by get_element_by_id get_elements_by_tag_name to_tree_order"
  apply(unfold_locales)
  using get_element_by_id_result_in_tree_order get_elements_by_tag_name_pure
  by fast+
end
