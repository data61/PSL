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
text\<open>In this theory, we introduce the monadic method setup for the CharacterData class.\<close>
theory CharacterDataMonad
  imports
    ElementMonad
    "../classes/CharacterDataClass"
begin

type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 
    'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData, 'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars 
  "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr, 'shadow_root_ptr, 
                              'Object, 'Node, 'Element, 'CharacterData, 'result) dom_prog" 


global_interpretation l_ptr_kinds_M character_data_ptr_kinds 
  defines character_data_ptr_kinds_M = a_ptr_kinds_M .
lemmas character_data_ptr_kinds_M_defs = a_ptr_kinds_M_def

lemma character_data_ptr_kinds_M_eq:
  assumes "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
  shows "|h \<turnstile> character_data_ptr_kinds_M|\<^sub>r = |h' \<turnstile> character_data_ptr_kinds_M|\<^sub>r"
  using assms 
  by(auto simp add: character_data_ptr_kinds_M_defs node_ptr_kinds_M_defs 
      character_data_ptr_kinds_def)

lemma character_data_ptr_kinds_M_reads: 
  "reads (\<Union>node_ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t node_ptr RObject.nothing)}) character_data_ptr_kinds_M h h'"
  using node_ptr_kinds_M_reads
  apply (simp add: reads_def node_ptr_kinds_M_defs character_data_ptr_kinds_M_defs 
    character_data_ptr_kinds_def preserved_def cong del: image_cong_simp)
  apply (metis (mono_tags, hide_lams) node_ptr_kinds_small old.unit.exhaust preserved_def)
  done

global_interpretation l_dummy defines get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a = "l_get_M.a_get_M get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a type_wf character_data_ptr_kinds"
  apply(simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_type_wf l_get_M_def)
  by (metis (no_types, hide_lams) NodeMonad.get_M_is_l_get_M bind_eq_Some_conv 
      character_data_ptr_kinds_commutes get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def l_get_M_def option.distinct(1))
lemmas get_M_defs = get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a

locale l_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas = l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
begin
sublocale l_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas by unfold_locales

interpretation l_get_M get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a type_wf character_data_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_type_wf local.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a)
  by (meson CharacterDataMonad.get_M_is_l_get_M l_get_M_def)
lemmas get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ok = get_M_ok[folded get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def]
end

global_interpretation l_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas type_wf by unfold_locales


global_interpretation l_put_M type_wf character_data_ptr_kinds get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a 
  rewrites "a_get_M = get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a" defines put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)

lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a


locale l_put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas = l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
begin
sublocale l_put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_lemmas by unfold_locales

interpretation l_put_M type_wf character_data_ptr_kinds get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a
  apply(unfold_locales)
  using get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_type_wf l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a local.l_type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_axioms
   apply blast
  by (meson CharacterDataMonad.get_M_is_l_get_M l_get_M_def)
lemmas put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ok = put_M_ok[folded put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def]
end

global_interpretation l_put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas type_wf by unfold_locales



lemma CharacterData_simp1 [simp]: 
  "(\<And>x. getter (setter (\<lambda>_. v) x) = v) \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> h' \<turnstile> get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter \<rightarrow>\<^sub>r v"
  by(auto simp add: put_M_defs get_M_defs split: option.splits)
lemma CharacterData_simp2 [simp]: 
  "character_data_ptr \<noteq> character_data_ptr' 
   \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr' getter) h h'"
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma CharacterData_simp3 [simp]: "
  (\<And>x. getter (setter (\<lambda>_. v) x) = getter x) 
  \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr' getter) h h'"
  apply(cases "character_data_ptr = character_data_ptr'") 
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma CharacterData_simp4 [simp]: 
  "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: put_M_defs ElementMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma CharacterData_simp5 [simp]: 
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: ElementMonad.put_M_defs get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma CharacterData_simp6 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
   \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h'
  \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply (cases "cast character_data_ptr = object_ptr") 
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs 
      get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      bind_eq_Some_conv split: option.splits)
lemma CharacterData_simp7 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
  \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  apply(cases "cast character_data_ptr = node_ptr")
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs 
      get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      bind_eq_Some_conv split: option.splits)

lemma CharacterData_simp8 [simp]: 
  "cast character_data_ptr \<noteq> node_ptr 
   \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def NodeMonad.get_M_defs 
      preserved_def split: option.splits dest: get_heap_E)
lemma CharacterData_simp9 [simp]: 
  "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
   \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  apply(cases "cast character_data_ptr \<noteq> node_ptr")
  by(auto simp add: put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def 
      NodeMonad.get_M_defs preserved_def split: option.splits bind_splits 
      dest: get_heap_E)
lemma CharacterData_simp10 [simp]: 
  "cast character_data_ptr \<noteq> node_ptr 
   \<Longrightarrow> h \<turnstile> put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: NodeMonad.put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def NodeMonad.get_M_defs 
      preserved_def split: option.splits dest: get_heap_E)

lemma CharacterData_simp11 [simp]: 
  "cast character_data_ptr \<noteq> object_ptr 
  \<Longrightarrow> h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
  \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def 
      ObjectMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)

lemma CharacterData_simp12 [simp]:
  "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' 
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast character_data_ptr \<noteq> object_ptr")
   apply(auto simp add: put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def ObjectMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)[1]
  by(auto simp add: put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def ObjectMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)[1]

lemma CharacterData_simp13 [simp]: 
  "cast character_data_ptr \<noteq> object_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: ObjectMonad.put_M_defs get_M_defs get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      ObjectMonad.get_M_defs preserved_def split: option.splits dest: get_heap_E)

lemma new_element_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a: 
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: new_element_def get_M_defs preserved_def split: prod.splits option.splits 
      elim!: bind_returns_result_E bind_returns_heap_E)


subsection\<open>Creating CharacterData\<close>

definition new_character_data :: "(_, (_) character_data_ptr) dom_prog"
  where
    "new_character_data = do {
      h \<leftarrow> get_heap;
      (new_ptr, h') \<leftarrow> return (new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a h);
      return_heap h';
      return new_ptr
    }"

lemma new_character_data_ok [simp]:
  "h \<turnstile> ok new_character_data"
  by(auto simp add: new_character_data_def split: prod.splits)

lemma new_character_data_ptr_in_heap:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "new_character_data_ptr |\<in>| character_data_ptr_kinds h'"
  using assms
  unfolding new_character_data_def
  by(auto simp add: new_character_data_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_in_heap 
      is_OK_returns_result_I
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_ptr_not_in_heap:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "new_character_data_ptr |\<notin>| character_data_ptr_kinds h"
  using assms new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_not_in_heap
  by(auto simp add: new_character_data_def split: prod.splits 
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_new_ptr:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
  using assms new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_new_ptr
  by(auto simp add: new_character_data_def split: prod.splits 
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_is_character_data_ptr:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "is_character_data_ptr new_character_data_ptr"
  using assms new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_is_character_data_ptr
  by(auto simp add: new_character_data_def elim!: bind_returns_result_E split: prod.splits)

lemma new_character_data_child_nodes:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "h' \<turnstile> get_M new_character_data_ptr val \<rightarrow>\<^sub>r ''''"
  using assms
  by(auto simp add: get_M_defs new_character_data_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def 
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
    \<Longrightarrow> ptr \<noteq> cast new_character_data_ptr \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: new_character_data_def ObjectMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_character_data_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
    \<Longrightarrow> ptr \<noteq> cast new_character_data_ptr \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: new_character_data_def NodeMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_character_data_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
    \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new_character_data_def ElementMonad.get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_character_data_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr 
    \<Longrightarrow> ptr \<noteq> new_character_data_ptr \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: new_character_data_def get_M_defs preserved_def 
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)



subsection\<open>Modified Heaps\<close>

lemma get_CharacterData_ptr_simp [simp]: 
  "get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
      = (if ptr = cast character_data_ptr then cast obj else get character_data_ptr h)"
  by(auto simp add: get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def split: option.splits Option.bind_splits)

lemma Character_data_ptr_kinds_simp [simp]: 
  "character_data_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = character_data_ptr_kinds h |\<union>| 
                            (if is_character_data_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: character_data_ptr_kinds_def is_node_ptr_kind_def split: option.splits)

lemma type_wf_put_I:
  assumes "type_wf h"
  assumes "ElementClass.type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "is_character_data_ptr_kind ptr \<Longrightarrow> is_character_data_kind obj"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  by(auto simp add: type_wf_defs split: option.splits)

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs elim!: ElementMonad.type_wf_put_ptr_not_in_heap_E 
      split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "ElementClass.type_wf h"
  assumes "is_character_data_ptr_kind ptr \<Longrightarrow> is_character_data_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs split: option.splits if_splits)[1]
  apply(case_tac "x2 = cast character_data_ptr")
   apply(auto)[1]
   apply(drule_tac x=character_data_ptr in allE)
    apply(simp)
   apply (metis (no_types, lifting) ElementClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf assms(2) bind.bind_lunit 
      cast\<^sub>N\<^sub>o\<^sub>d\<^sub>e\<^sub>2\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_inv cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_inv get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def 
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def option.exhaust_sel)
  by(blast)

subsection\<open>Preserving Types\<close>

lemma new_element_type_wf_preserved [simp]:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms
  apply(auto simp add: new_element_def new\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E 
      intro!: type_wf_put_I split: if_splits)[1]
  using CharacterDataClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t assms new_element_type_wf_preserved apply blast
  using element_ptrs_def apply fastforce
  using CharacterDataClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t assms new_element_type_wf_preserved apply blast
  by (metis Suc_n_not_le_n element_ptr.sel(1) element_ptrs_def fMax_ge ffmember_filter 
      fimage_eqI is_element_ptr_ref)

lemma new_element_is_l_new_element: "l_new_element type_wf"
  using l_new_element.intro new_element_type_wf_preserved
  by blast

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_tag_type_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr tag_type_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I 
      ObjectMonad.type_wf_put_I)[1]
      apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs split: option.splits)[1]
     apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs split: option.splits)[1]
    apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs split: option.splits)[1]
   apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs split: option.splits)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs split: option.splits)[1]
  using ObjectMonad.type_wf_put_ptr_in_heap_E ObjectMonad.type_wf_put_ptr_not_in_heap_E apply blast
   apply (metis (mono_tags, lifting) bind_eq_Some_conv get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.exhaust_sel)
  by (metis (no_types, lifting) option.exhaust_sel )


lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_child_nodes_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr child_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      dest!: get_heap_E  elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I 
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
      apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs 
      split: option.splits)[1]
     apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs 
      split: option.splits)[1]
    apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs 
      split: option.splits)[1]
   apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs 
      split: option.splits)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs ElementMonad.get_M_defs 
      split: option.splits)[1]
  using ObjectMonad.type_wf_put_ptr_in_heap_E ObjectMonad.type_wf_put_ptr_not_in_heap_E apply blast
   apply (metis (mono_tags, lifting) ElementMonad.a_get_M_def bind_eq_Some_conv error_returns_result 
      get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get_heap_returns_result option.exhaust_sel option.simps(4))
  by (metis (no_types, lifting) option.exhaust_sel)

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_attrs_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr attrs_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I 
      ObjectMonad.type_wf_put_I)[1]
      apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
     apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
    apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
   apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
  using ObjectMonad.type_wf_put_ptr_in_heap_E ObjectMonad.type_wf_put_ptr_not_in_heap_E apply blast
   apply (metis (mono_tags, lifting) ElementMonad.a_get_M_def bind_eq_Some_conv error_returns_result get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get_heap_returns_result option.exhaust_sel option.simps(4))
  by (metis (no_types, lifting) option.exhaust_sel)

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_shadow_root_opt_type_wf_preserved [simp]: 
  "h \<turnstile> put_M element_ptr shadow_root_opt_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: ElementMonad.put_M_defs put\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I 
      ObjectMonad.type_wf_put_I)[1]
      apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
     apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
    apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
   apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs 
      ElementMonad.get_M_defs split: option.splits)[1]
  using ObjectMonad.type_wf_put_ptr_in_heap_E ObjectMonad.type_wf_put_ptr_not_in_heap_E apply blast
   apply (metis (mono_tags, lifting) bind_eq_Some_conv get\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def)
  by (metis (no_types, lifting) option.exhaust_sel)


lemma new_character_data_type_wf_preserved [simp]: 
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: new_character_data_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def Let_def put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I 
      split: if_splits)[1]
      apply(simp_all add: type_wf_defs ElementClass.type_wf_defs NodeClass.type_wf_defs is_node_kind_def)
  by (meson new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def new\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_ptr_not_in_heap)

locale l_new_character_data = l_type_wf +
  assumes new_character_data_types_preserved: "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma new_character_data_is_l_new_character_data: "l_new_character_data type_wf"
  using l_new_character_data.intro new_character_data_type_wf_preserved
  by blast

lemma put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_val_type_wf_preserved [simp]: 
  "h \<turnstile> put_M character_data_ptr val_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: CharacterDataMonad.put_M_defs put\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      CharacterDataClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e CharacterDataClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_kind_def
      dest!: get_heap_E  
      elim!: bind_returns_heap_E2 
      intro!: type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I 
      ObjectMonad.type_wf_put_I)[1]      
   apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs CharacterDataMonad.get_M_defs 
      split: option.splits)[1]
  apply(auto simp add: is_node_kind_def type_wf_defs ElementClass.type_wf_defs 
      NodeClass.type_wf_defs CharacterDataMonad.get_M_defs
      ObjectClass.a_type_wf_def
      split: option.splits)[1]
   apply (metis (no_types, lifting) bind_eq_Some_conv get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def)
  by metis

lemma character_data_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "character_data_ptr_kinds h = character_data_ptr_kinds h'"
  by(simp add: character_data_ptr_kinds_def node_ptr_kinds_def preserved_def 
      object_ptr_kinds_preserved_small[OF assms])

lemma character_data_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<longrightarrow> (\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "character_data_ptr_kinds h = character_data_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def character_data_ptr_kinds_def)
  by (metis assms node_ptr_kinds_preserved)


lemma type_wf_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>character_data_ptr. preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr 
                                           RCharacterData.nothing) h h'"
  shows "type_wf h = type_wf h'"
  using type_wf_preserved_small[OF assms(1) assms(2) assms(3)]  
    allI[OF assms(4), of id, simplified] character_data_ptr_kinds_small[OF assms(1)]
  apply(auto simp add: type_wf_defs preserved_def get_M_defs character_data_ptr_kinds_small[OF assms(1)] 
      split: option.splits)[1]
   apply(force)
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
          \<Longrightarrow> \<forall>character_data_ptr. preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr 
                                              RCharacterData.nothing) h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
    using assms type_wf_preserved_small by fast
  with assms(1) assms(2) show ?thesis
    apply(rule writes_small_big)
    by(auto simp add: reflp_def transp_def)
qed

lemma type_wf_drop: "type_wf h \<Longrightarrow> type_wf (Heap (fmdrop ptr (the_heap h)))"
  apply(auto simp add: type_wf_def ElementMonad.type_wf_drop  
      l_type_wf_def\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a.a_type_wf_def)[1]
  using type_wf_drop
  by (metis (no_types, lifting) ElementClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf character_data_ptr_kinds_commutes 
      fmlookup_drop get\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def heap.sel 
      node_ptr_kinds_commutes)

end