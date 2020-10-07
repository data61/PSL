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
text\<open>In this theory, we introduce the monadic method setup for the Element class.\<close>
theory ElementMonad
  imports
    NodeMonad
    "../classes/ElementClass"
begin

type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
    'shadow_root_ptr, 'Object, 'Node, 'Element,'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 
                        'document_ptr, 'shadow_root_ptr, 'Object, 'Node, 'Element,'result) dom_prog" 


global_interpretation l_ptr_kinds_M element_ptr_kinds defines element_ptr_kinds_M = a_ptr_kinds_M .
lemmas element_ptr_kinds_M_defs = a_ptr_kinds_M_def


lemma element_ptr_kinds_M_eq:
  assumes "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
  shows "|h \<turnstile> element_ptr_kinds_M|\<^sub>r = |h' \<turnstile> element_ptr_kinds_M|\<^sub>r"
  using assms 
  by(auto simp add: element_ptr_kinds_M_defs node_ptr_kinds_M_defs element_ptr_kinds_def)

lemma element_ptr_kinds_M_reads: 
  "reads (\<Union>element_ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t element_ptr RObject.nothing)}) element_ptr_kinds_M h h'"
  apply (simp add: reads_def node_ptr_kinds_M_defs element_ptr_kinds_M_defs element_ptr_kinds_def
    node_ptr_kinds_M_reads preserved_def cong del: image_cong_simp)
  apply (metis (mono_tags, hide_lams) node_ptr_kinds_small old.unit.exhaust preserved_def)
  done

global_interpretation l_dummy defines get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t = "l_get_M.a_get_M get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t type_wf element_ptr_kinds"
  apply(simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf l_get_M_def)
  by (metis (no_types, lifting) ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf ObjectClass.type_wf_defs 
      bind_eq_Some_conv bind_eq_Some_conv element_ptr_kinds_commutes get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def node_ptr_kinds_commutes option.simps(3))
lemmas get_M_defs = get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t

locale l_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas = l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
sublocale l_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas by unfold_locales

interpretation l_get_M get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t type_wf element_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf local.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
  by (meson ElementMonad.get_M_is_l_get_M l_get_M_def)
lemmas get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok = get_M_ok[folded get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def]
lemmas get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap = get_M_ptr_in_heap[folded get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def]
end

global_interpretation l_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas type_wf by unfold_locales


global_interpretation l_put_M type_wf element_ptr_kinds get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t 
  rewrites "a_get_M = get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t" 
  defines put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)

lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t


locale l_put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas = l_type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
sublocale l_put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas by unfold_locales

interpretation l_put_M type_wf element_ptr_kinds get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
  apply(unfold_locales)
   apply (simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf local.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
  by (meson ElementMonad.get_M_is_l_get_M l_get_M_def)

lemmas put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok = put_M_ok[folded put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def]
end

global_interpretation l_put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas type_wf by unfold_locales


lemma element_put_get [simp]: 
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> (\<And>x. getter (setter (\<lambda>_. v) x) = v) 
  \<Longrightarrow> h' \<turnstile> get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter \<rightarrow>\<^sub>r v"
  by(auto simp add: put_M_defs get_M_defs split: option.splits)
lemma get_M_Element_preserved1 [simp]: 
  "element_ptr \<noteq> element_ptr' \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr' getter) h h'"
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma element_put_get_preserved [simp]: 
  "(\<And>x. getter (setter (\<lambda>_. v) x) = getter x) \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr' getter) h h'"
  apply(cases "element_ptr = element_ptr'") 
  by(auto simp add: put_M_defs get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma  get_M_Element_preserved3 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
    \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast element_ptr = object_ptr") 
  by (auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def bind_eq_Some_conv 
      split: option.splits)
lemma  get_M_Element_preserved4 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
     \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  apply(cases "cast element_ptr = node_ptr") 
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def bind_eq_Some_conv 
      split: option.splits)

lemma  get_M_Element_preserved5 [simp]: 
  "cast element_ptr \<noteq> node_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def NodeMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma  get_M_Element_preserved6 [simp]: 
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
    \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  apply(cases "cast element_ptr \<noteq> node_ptr")
  by(auto simp add: put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def NodeMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)

lemma  get_M_Element_preserved7 [simp]: 
  "cast element_ptr \<noteq> node_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: NodeMonad.put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def NodeMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)

lemma  get_M_Element_preserved8 [simp]: 
  "cast element_ptr \<noteq> object_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      ObjectMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma  get_M_Element_preserved9 [simp]: 
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast element_ptr \<noteq> object_ptr")
  by(auto simp add: put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      ObjectMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)

lemma  get_M_Element_preserved10 [simp]: 
  "cast element_ptr \<noteq> object_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: ObjectMonad.put_M_defs get_M_defs get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      ObjectMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)

subsection\<open>Creating Elements\<close>

definition new_element :: "(_, (_) element_ptr) dom_prog"
  where
    "new_element = do {
      h \<leftarrow> get_heap;
      (new_ptr, h') \<leftarrow> return (new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t h);
      return_heap h';
      return new_ptr
    }"

lemma new_element_ok [simp]:
  "h \<turnstile> ok new_element"
  by(auto simp add: new_element_def split: prod.splits)

lemma new_element_ptr_in_heap:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "new_element_ptr |\<in>| element_ptr_kinds h'"
  using assms
  unfolding new_element_def
  by(auto simp add: new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap is_OK_returns_result_I
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_element_ptr_not_in_heap:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "new_element_ptr |\<notin>| element_ptr_kinds h"
  using assms new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap
  by(auto simp add: new_element_def split: prod.splits elim!: bind_returns_result_E 
      bind_returns_heap_E)

lemma new_element_new_ptr:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
  using assms new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_new_ptr
  by(auto simp add: new_element_def split: prod.splits elim!: bind_returns_result_E 
      bind_returns_heap_E)

lemma new_element_is_element_ptr:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "is_element_ptr new_element_ptr"
  using assms new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_is_element_ptr
  by(auto simp add: new_element_def elim!: bind_returns_result_E split: prod.splits)

lemma new_element_child_nodes:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "h' \<turnstile> get_M new_element_ptr child_nodes \<rightarrow>\<^sub>r []"
  using assms
  by(auto simp add: get_M_defs new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_element_tag_type:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "h' \<turnstile> get_M new_element_ptr tag_type \<rightarrow>\<^sub>r ''''"
  using assms
  by(auto simp add: get_M_defs new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_element_attrs:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "h' \<turnstile> get_M new_element_ptr attrs \<rightarrow>\<^sub>r fmempty"
  using assms
  by(auto simp add: get_M_defs new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_element_shadow_root_opt:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  shows "h' \<turnstile> get_M new_element_ptr shadow_root_opt \<rightarrow>\<^sub>r None"
  using assms
  by(auto simp add: get_M_defs new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> ptr \<noteq> cast new_element_ptr 
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: new_element_def ObjectMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_element_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> ptr \<noteq> cast new_element_ptr 
    \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: new_element_def NodeMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_element_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> ptr \<noteq> new_element_ptr 
    \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_element_def get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

subsection\<open>Modified Heaps\<close>

lemma get_Element_ptr_simp [simp]: 
  "get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
      = (if ptr = cast element_ptr then cast obj else get element_ptr h)"
  by(auto simp add: get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def split: option.splits Option.bind_splits)


lemma element_ptr_kinds_simp [simp]: 
  "element_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
      = element_ptr_kinds h |\<union>| (if is_element_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: element_ptr_kinds_def is_node_ptr_kind_def split: option.splits)

lemma type_wf_put_I:
  assumes "type_wf h"
  assumes "NodeClass.type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "is_element_ptr_kind ptr \<Longrightarrow> is_element_kind obj"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  by(auto simp add: type_wf_defs split: option.splits)

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs elim!: NodeMonad.type_wf_put_ptr_not_in_heap_E 
      split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "NodeClass.type_wf h"
  assumes "is_element_ptr_kind ptr \<Longrightarrow> is_element_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs split: option.splits if_splits)[1]
  apply(case_tac "x2 = cast element_ptr")
   apply(drule_tac x=element_ptr in allE)
    apply(auto)[1]
   apply(metis (no_types, lifting) NodeClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf assms(2) bind.bind_lunit 
      cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_inv cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def option.exhaust_sel)
  by(auto)

subsection\<open>Preserving Types\<close>

lemma new_element_type_wf_preserved [simp]: "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      new_element_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def
      split: prod.splits if_splits elim!: bind_returns_heap_E)[1]
     apply (metis element_ptr_kinds_commutes element_ptrs_def fempty_iff ffmember_filter 
      is_element_ptr_ref)
  using element_ptrs_def apply fastforce
   apply (metis (mono_tags, hide_lams) Suc_n_not_le_n element_ptr.sel(1) element_ptr_kinds_commutes 
      element_ptrs_def fMax_ge ffmember_filter fimageI is_element_ptr_ref)
  by (metis (no_types, lifting) fMax_finsert fempty_iff fimage_is_fempty max_0L new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap)

locale l_new_element = l_type_wf +
  assumes new_element_types_preserved: "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma new_element_is_l_new_element: "l_new_element type_wf"
  using l_new_element.intro new_element_type_wf_preserved
  by blast

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_tag_type_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr tag_type_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs  
      Let_def put_M_defs get_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      split: prod.splits option.splits Option.bind_splits elim!: bind_returns_heap_E)[1]
      apply (metis option.distinct(1))
     apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
    apply (metis option.distinct(1))
   apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
  by (metis bind.bind_lunit cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv)


lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_child_nodes_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr child_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs  
      Let_def put_M_defs get_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      split: prod.splits option.splits Option.bind_splits elim!: bind_returns_heap_E)[1]
      apply (metis option.distinct(1))
     apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
    apply (metis option.distinct(1))
   apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
  by (metis bind.bind_lunit cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv)

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_attrs_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr attrs_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs  Let_def 
      put_M_defs get_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      split: prod.splits option.splits Option.bind_splits elim!: bind_returns_heap_E)[1]
      apply (metis option.distinct(1))
     apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
    apply (metis option.distinct(1))
   apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
  by (metis bind.bind_lunit cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv)

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_shadow_root_opt_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr shadow_root_opt_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs  
      Let_def put_M_defs get_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      split: prod.splits option.splits Option.bind_splits elim!: bind_returns_heap_E)[1]
      apply (metis option.distinct(1))
     apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
    apply (metis option.distinct(1))
   apply (metis bind.bind_lunit  cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none)
  by (metis bind.bind_lunit cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv)

lemma put_M_pointers_preserved:
  assumes "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms 
  apply(auto simp add: put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      elim!: bind_returns_heap_E2 dest!: get_heap_E)[1]
  by (meson get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap is_OK_returns_result_I)

lemma element_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' 
                    \<longrightarrow> (\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "element_ptr_kinds h = element_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def element_ptr_kinds_def)
  by (metis assms node_ptr_kinds_preserved)


lemma element_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "element_ptr_kinds h = element_ptr_kinds h'"
  by(simp add: element_ptr_kinds_def node_ptr_kinds_def preserved_def 
      object_ptr_kinds_preserved_small[OF assms])

lemma type_wf_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  shows "type_wf h = type_wf h'"
  using type_wf_preserved_small[OF assms(1) assms(2)] allI[OF assms(3), of id, simplified]
  apply(auto simp add: type_wf_defs )[1]
   apply(auto simp add: preserved_def get_M_defs element_ptr_kinds_small[OF assms(1)] 
      split: option.splits,force)[1]
  by(auto simp add: preserved_def get_M_defs element_ptr_kinds_small[OF assms(1)] 
      split: option.splits,force)

lemma type_wf_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<Longrightarrow> \<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<Longrightarrow> \<forall>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<Longrightarrow> \<forall>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
    using assms type_wf_preserved_small by fast
  with assms(1) assms(2) show ?thesis
    apply(rule writes_small_big)
    by(auto simp add: reflp_def transp_def)
qed

lemma type_wf_drop: "type_wf h \<Longrightarrow> type_wf (Heap (fmdrop ptr (the_heap h)))"
  apply(auto simp add: type_wf_defs NodeClass.type_wf_defs ObjectClass.type_wf_defs 
      node_ptr_kinds_def object_ptr_kinds_def is_node_ptr_kind_def 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)[1]
    apply (metis (mono_tags, lifting) comp_apply ffmember_filter fimage_eqI 
      is_node_ptr_kind_cast node_ptr_casts_commute2 option.sel)
   apply (metis (no_types, lifting) comp_apply element_ptr_kinds_commutes ffmember_filter 
      fmdom_filter fmfilter_alt_defs(1) heap.sel node_ptr_kinds_commutes object_ptr_kinds_def)
  by (metis comp_eq_dest_lhs element_ptr_kinds_commutes fmdom_notI fmdrop_lookup heap.sel 
      node_ptr_kinds_commutes object_ptr_kinds_def)

end
