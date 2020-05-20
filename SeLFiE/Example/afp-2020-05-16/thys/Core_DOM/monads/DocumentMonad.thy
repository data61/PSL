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

section\<open>Document\<close>
text\<open>In this theory, we introduce the monadic method setup for the Document class.\<close>

theory DocumentMonad
  imports
    CharacterDataMonad
    "../classes/DocumentClass"
begin

type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
    'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData, 'Document, 'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
           'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData, 'Document, 'result) dom_prog" 


global_interpretation l_ptr_kinds_M document_ptr_kinds defines document_ptr_kinds_M = a_ptr_kinds_M .
lemmas document_ptr_kinds_M_defs = a_ptr_kinds_M_def

lemma document_ptr_kinds_M_eq:
  assumes "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
  shows "|h \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
  using assms 
  by(auto simp add: document_ptr_kinds_M_defs object_ptr_kinds_M_defs document_ptr_kinds_def)

lemma document_ptr_kinds_M_reads: 
  "reads (\<Union>object_ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing)}) document_ptr_kinds_M h h'"
  using object_ptr_kinds_M_reads
  apply (simp add: reads_def object_ptr_kinds_M_defs document_ptr_kinds_M_defs 
    document_ptr_kinds_def preserved_def cong del: image_cong_simp)
  apply (metis (mono_tags, hide_lams) object_ptr_kinds_preserved_small old.unit.exhaust preserved_def)
  done

global_interpretation l_dummy defines get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t = "l_get_M.a_get_M get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t type_wf document_ptr_kinds"
  apply(simp add: get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf l_get_M_def)
  by (metis ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf ObjectClass.type_wf_defs bind_eq_None_conv 
      document_ptr_kinds_commutes get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.simps(3))
lemmas get_M_defs = get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t

locale l_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas = l_type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
sublocale l_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas by unfold_locales

interpretation l_get_M get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t type_wf document_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf local.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
  by (meson DocumentMonad.get_M_is_l_get_M l_get_M_def)
lemmas get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok = get_M_ok[folded get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def]
end

global_interpretation l_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas type_wf by unfold_locales


global_interpretation l_put_M type_wf document_ptr_kinds get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t 
  rewrites "a_get_M = get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t" defines put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)

lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t


locale l_put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas = l_type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
begin
sublocale l_put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas by unfold_locales

interpretation l_put_M type_wf document_ptr_kinds get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
  apply(unfold_locales)
   apply (simp add: get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_type_wf local.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
  by (meson DocumentMonad.get_M_is_l_get_M l_get_M_def)
lemmas put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok = put_M_ok[folded put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def]
end

global_interpretation l_put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas type_wf by unfold_locales


lemma document_put_get [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> (\<And>x. getter (setter (\<lambda>_. v) x) = v) 
     \<Longrightarrow> h' \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter \<rightarrow>\<^sub>r v"
  by(auto simp add: put_M_defs get_M_defs split: option.splits)
lemma get_M_Mdocument_preserved1 [simp]: 
  "document_ptr \<noteq> document_ptr' 
    \<Longrightarrow> h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr' getter) h h'"
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma document_put_get_preserved [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> (\<And>x. getter (setter (\<lambda>_. v) x) = getter x) 
   \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr' getter) h h'"
  apply(cases "document_ptr = document_ptr'") 
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mdocument_preserved2 [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs NodeMonad.get_M_defs get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mdocument_preserved3 [simp]: 
  "cast document_ptr \<noteq> object_ptr 
   \<Longrightarrow> h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def ObjectMonad.get_M_defs 
      preserved_def split: option.splits dest: get_heap_E)
lemma get_M_Mdocument_preserved4  [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast document_ptr \<noteq> object_ptr")[1]
  by(auto simp add: put_M_defs get_M_defs get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      ObjectMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)

lemma get_M_Mdocument_preserved5 [simp]: 
  "cast document_ptr \<noteq> object_ptr 
  \<Longrightarrow> h \<turnstile> put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: ObjectMonad.put_M_defs get_M_defs get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def ObjectMonad.get_M_defs 
      preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mdocument_preserved6 [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: put_M_defs ElementMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma get_M_Mdocument_preserved7 [simp]: 
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: ElementMonad.put_M_defs get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma get_M_Mdocument_preserved8 [simp]: 
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: put_M_defs CharacterDataMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma get_M_Mdocument_preserved9 [simp]: 
  "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: CharacterDataMonad.put_M_defs get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma get_M_Mdocument_preserved10 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
    \<Longrightarrow> h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast document_ptr = object_ptr") 
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def bind_eq_Some_conv 
      split: option.splits)

lemma new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_element_def get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_character_data_def get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)


subsection \<open>Creating Documents\<close>

definition new_document :: "(_, (_) document_ptr) dom_prog"
  where
    "new_document = do {
      h \<leftarrow> get_heap;
      (new_ptr, h') \<leftarrow> return (new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t h);
      return_heap h';
      return new_ptr
    }"

lemma new_document_ok [simp]:
  "h \<turnstile> ok new_document"
  by(auto simp add: new_document_def split: prod.splits)

lemma new_document_ptr_in_heap:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "new_document_ptr |\<in>| document_ptr_kinds h'"
  using assms
  unfolding new_document_def
  by(auto simp add: new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap is_OK_returns_result_I
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_ptr_not_in_heap:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "new_document_ptr |\<notin>| document_ptr_kinds h"
  using assms new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap
  by(auto simp add: new_document_def split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_new_ptr:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_document_ptr|}"
  using assms new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_new_ptr
  by(auto simp add: new_document_def split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_is_document_ptr:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "is_document_ptr new_document_ptr"
  using assms new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_is_document_ptr
  by(auto simp add: new_document_def elim!: bind_returns_result_E split: prod.splits)

lemma new_document_doctype:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "h' \<turnstile> get_M new_document_ptr doctype \<rightarrow>\<^sub>r ''''"
  using assms
  by(auto simp add: get_M_defs new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_document_element:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "h' \<turnstile> get_M new_document_ptr document_element \<rightarrow>\<^sub>r None"
  using assms
  by(auto simp add: get_M_defs new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_disconnected_nodes:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
  shows "h' \<turnstile> get_M new_document_ptr disconnected_nodes \<rightarrow>\<^sub>r []"
  using assms
  by(auto simp add: get_M_defs new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)


lemma new_document_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t: 
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
    \<Longrightarrow> ptr \<noteq> cast new_document_ptr \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: new_document_def ObjectMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_document_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e: 
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
    \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: new_document_def NodeMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_document_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
     \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_document_def ElementMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_document_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a: 
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr 
    \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: new_document_def CharacterDataMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_document_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' 
     \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> ptr \<noteq> new_document_ptr 
     \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_document_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)



subsection \<open>Modified Heaps\<close>

lemma get_document_ptr_simp [simp]: 
  "get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
     = (if ptr = cast document_ptr then cast obj else get document_ptr h)"
  by(auto simp add: get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def split: option.splits Option.bind_splits)

lemma document_ptr_kidns_simp [simp]: 
  "document_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
    = document_ptr_kinds h |\<union>| (if is_document_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: document_ptr_kinds_def split: option.splits)

lemma type_wf_put_I:
  assumes "type_wf h"
  assumes "CharacterDataClass.type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "is_document_ptr_kind ptr \<Longrightarrow> is_document_kind obj"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  by(auto simp add: type_wf_defs is_document_kind_def split: option.splits)

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs elim!: CharacterDataMonad.type_wf_put_ptr_not_in_heap_E 
      split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "CharacterDataClass.type_wf h"
  assumes "is_document_ptr_kind ptr \<Longrightarrow> is_document_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs elim!: CharacterDataMonad.type_wf_put_ptr_in_heap_E 
      split: option.splits if_splits)[1]
  by (metis (no_types, lifting) CharacterDataClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf bind.bind_lunit get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      is_document_kind_def option.collapse)



subsection \<open>Preserving Types\<close>

lemma new_element_type_wf_preserved [simp]: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def element_ptrs_def
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I 
      split: if_splits)[1]
   apply fastforce
  by (metis Suc_n_not_le_n element_ptr.sel(1) element_ptrs_def fMax_ge ffmember_filter 
      fimage_eqI is_element_ptr_ref)

lemma new_element_is_l_new_element [instances]: 
  "l_new_element type_wf"
  using l_new_element.intro new_element_type_wf_preserved
  by blast

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_tag_type_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr tag_type_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs
      ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply (metis (no_types, lifting) Option.bind_cong bind_rzero 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.distinct(1))
  by metis

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_child_nodes_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr child_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply (metis (no_types, lifting) Option.bind_cong bind_rzero get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.distinct(1))
  by metis

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_attrs_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr attrs_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply (metis (no_types, lifting) Option.bind_cong bind_rzero get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.distinct(1))
  by metis

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_shadow_root_opt_type_wf_preserved [simp]:
  "h \<turnstile> put_M element_ptr shadow_root_opt_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply (metis (no_types, lifting) Option.bind_cong bind_rzero get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.distinct(1))
  by metis

lemma new_character_data_type_wf_preserved [simp]: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      new_character_data_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2 bind_returns_heap_E type_wf_put_ptr_not_in_heap_E
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  by (meson new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_not_in_heap)

lemma new_character_data_is_l_new_character_data [instances]: 
  "l_new_character_data type_wf"
  using l_new_character_data.intro new_character_data_type_wf_preserved
  by blast

lemma put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_val_type_wf_preserved [simp]: 
  "h \<turnstile> put_M character_data_ptr val_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: CharacterDataMonad.put_M_defs put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t is_node_kind_def
      dest!: get_heap_E  elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply (metis (no_types, lifting) CharacterDataMonad.a_get_M_def bind_eq_None_conv 
      error_returns_result get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get_heap_returns_result option.exhaust_sel 
      option.simps(4))
  by (metis (no_types, lifting) CharacterDataMonad.a_get_M_def error_returns_result 
      get_heap_returns_result option.exhaust_sel option.simps(4))

lemma new_document_type_wf_preserved [simp]: "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a  DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_ptr_kind_none
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I 
      split: if_splits)[1] 
   apply(auto simp add: type_wf_defs ElementClass.type_wf_defs CharacterDataClass.type_wf_defs 
      NodeClass.type_wf_defs ObjectClass.type_wf_defs is_document_kind_def 
      split: option.splits)[1]
  by (meson new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap)

locale l_new_document = l_type_wf +
  assumes new_document_types_preserved: "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma new_document_is_l_new_document  [instances]: "l_new_document type_wf"
  using l_new_document.intro new_document_type_wf_preserved
  by blast

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_doctype_type_wf_preserved [simp]: 
  "h \<turnstile> put_M document_ptr doctype_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I 
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
         apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
        apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
       apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
      apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
     apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
    apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
   apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
  apply(auto simp add: is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
  apply(auto simp add: get_M_defs)
  by (metis (no_types, lifting)  error_returns_result option.exhaust_sel option.simps(4))

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_document_element_type_wf_preserved [simp]: 
  "h \<turnstile> put_M document_ptr document_element_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def 
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
      DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
      DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t is_node_ptr_kind_none
      cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none is_document_kind_def
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I 
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I 
      ObjectMonad.type_wf_put_I)[1]
  apply(auto simp add: get_M_defs is_document_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs 
      split: option.splits)[1]
  by (metis)

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_disconnected_nodes_type_wf_preserved [simp]: 
  "h \<turnstile> put_M document_ptr disconnected_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      DocumentClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
      DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      DocumentClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
      DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_ptr_kind_none
      cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_none is_document_kind_def
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I CharacterDataMonad.type_wf_put_I 
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I
      ObjectMonad.type_wf_put_I)[1] 
  apply(auto simp add: is_document_kind_def get_M_defs type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs 
      CharacterDataClass.type_wf_defs split: option.splits)[1]
  by (metis)

lemma document_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "document_ptr_kinds h = document_ptr_kinds h'"
  by(simp add: document_ptr_kinds_def preserved_def object_ptr_kinds_preserved_small[OF assms])

lemma document_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<longrightarrow> (\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "document_ptr_kinds h = document_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def document_ptr_kinds_def)
  by (metis assms object_ptr_kinds_preserved)

lemma type_wf_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>character_data_ptr. preserved 
                          (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr RCharacterData.nothing) h h'"
  assumes "\<And>document_ptr. preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr RDocument.nothing) h h'"
  shows "DocumentClass.type_wf h = DocumentClass.type_wf h'"
  using type_wf_preserved_small[OF assms(1) assms(2) assms(3) assms(4)]  
    allI[OF assms(5), of id, simplified] document_ptr_kinds_small[OF assms(1)]
  apply(auto simp add: type_wf_defs )[1]
   apply(auto simp add: type_wf_defs preserved_def get_M_defs document_ptr_kinds_small[OF assms(1)] 
      split: option.splits)[1]
   apply force
  apply(auto simp add: type_wf_defs preserved_def get_M_defs document_ptr_kinds_small[OF assms(1)] 
      split: option.splits)[1]
  by force

lemma type_wf_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> \<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> \<forall>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> \<forall>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> \<forall>character_data_ptr. preserved 
                    (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr RCharacterData.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> \<forall>document_ptr. preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr RDocument.nothing) h h'"
  shows "DocumentClass.type_wf h = DocumentClass.type_wf h'"
proof -
  have "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> DocumentClass.type_wf h = DocumentClass.type_wf h'"
    using assms type_wf_preserved_small by fast
  with assms(1) assms(2) show ?thesis
    apply(rule writes_small_big)
    by(auto simp add: reflp_def transp_def)
qed

lemma type_wf_drop: "type_wf h \<Longrightarrow> type_wf (Heap (fmdrop ptr (the_heap h)))"
  apply(auto simp add: type_wf_defs)[1]
  using type_wf_drop
   apply blast
  by (metis (mono_tags, lifting) comp_apply document_ptr_kinds_commutes ffmember_filter fmdom_filter 
      fmfilter_alt_defs(1) fmlookup_drop get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def heap.sel object_ptr_kinds_def)
end
