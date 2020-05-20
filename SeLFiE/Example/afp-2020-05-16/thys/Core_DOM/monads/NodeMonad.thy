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
text\<open>In this theory, we introduce the monadic method setup for the Node class.\<close>
theory NodeMonad
  imports
    ObjectMonad
    "../classes/NodeClass"
begin

type_synonym ('object_ptr, 'node_ptr, 'Object, 'Node, 'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars "('object_ptr, 'node_ptr, 'Object, 'Node, 'result) dom_prog" 


global_interpretation l_ptr_kinds_M node_ptr_kinds defines node_ptr_kinds_M = a_ptr_kinds_M .
lemmas node_ptr_kinds_M_defs = a_ptr_kinds_M_def

lemma node_ptr_kinds_M_eq:
  assumes "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
  shows "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
  using assms 
  by(auto simp add: node_ptr_kinds_M_defs object_ptr_kinds_M_defs node_ptr_kinds_def)


global_interpretation l_dummy defines get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e = "l_get_M.a_get_M get\<^sub>N\<^sub>o\<^sub>d\<^sub>e" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>N\<^sub>o\<^sub>d\<^sub>e type_wf node_ptr_kinds"
  apply(simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf l_get_M_def)
  by (metis ObjectClass.a_type_wf_def ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf bind_eq_None_conv get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      node_ptr_kinds_commutes option.simps(3))
lemmas get_M_defs = get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e

locale l_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas = l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
begin
sublocale l_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas by unfold_locales

interpretation l_get_M get\<^sub>N\<^sub>o\<^sub>d\<^sub>e type_wf node_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf local.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e)
  by (meson NodeMonad.get_M_is_l_get_M l_get_M_def)
lemmas get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ok = get_M_ok[folded get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def]
end

global_interpretation l_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas type_wf by unfold_locales

lemma node_ptr_kinds_M_reads: 
  "reads (\<Union>object_ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing)}) node_ptr_kinds_M h h'"
  using object_ptr_kinds_M_reads
  apply (simp add: reads_def node_ptr_kinds_M_defs node_ptr_kinds_def
    object_ptr_kinds_M_reads preserved_def cong del: image_cong_simp)
  apply (metis (mono_tags, hide_lams)  object_ptr_kinds_preserved_small old.unit.exhaust preserved_def)
  done

global_interpretation l_put_M type_wf node_ptr_kinds get\<^sub>N\<^sub>o\<^sub>d\<^sub>e put\<^sub>N\<^sub>o\<^sub>d\<^sub>e 
  rewrites "a_get_M = get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e" 
  defines put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)

lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e


locale l_put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas = l_type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e
begin
sublocale l_put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas by unfold_locales

interpretation l_put_M type_wf node_ptr_kinds get\<^sub>N\<^sub>o\<^sub>d\<^sub>e put\<^sub>N\<^sub>o\<^sub>d\<^sub>e
  apply(unfold_locales)
   apply (simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_type_wf local.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e)
  by (meson NodeMonad.get_M_is_l_get_M l_get_M_def)
lemmas put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_ok = put_M_ok[folded put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def]
end

global_interpretation l_put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e_lemmas type_wf by unfold_locales

lemma get_M_Object_preserved1 [simp]: 
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) \<Longrightarrow> h \<turnstile> put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast node_ptr = object_ptr") 
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def 
      bind_eq_Some_conv 
      split: option.splits)

lemma get_M_Object_preserved2 [simp]: 
  "cast node_ptr \<noteq> object_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr setter v \<rightarrow>\<^sub>h h' 
    \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def ObjectMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)
lemma get_M_Object_preserved3 [simp]: 
  "h \<turnstile> put_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) 
    \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast node_ptr \<noteq> object_ptr")
  by(auto simp add: put_M_defs get_M_defs get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def ObjectMonad.get_M_defs preserved_def 
      split: option.splits bind_splits dest: get_heap_E)

lemma get_M_Object_preserved4 [simp]: 
  "cast node_ptr \<noteq> object_ptr \<Longrightarrow> h \<turnstile> put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr setter v \<rightarrow>\<^sub>h h' 
      \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  by(auto simp add: ObjectMonad.put_M_defs get_M_defs get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def ObjectMonad.get_M_defs preserved_def 
      split: option.splits dest: get_heap_E)

subsection\<open>Modified Heaps\<close>

lemma get_node_ptr_simp [simp]: 
  "get\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = (if ptr = cast node_ptr then cast obj else get node_ptr h)"
  by(auto simp add: get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def)

lemma node_ptr_kinds_simp [simp]: 
  "node_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) 
                = node_ptr_kinds h |\<union>| (if is_node_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: node_ptr_kinds_def)

lemma type_wf_put_I:
  assumes "type_wf h"
  assumes "ObjectClass.type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "is_node_ptr_kind ptr \<Longrightarrow> is_node_kind obj"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  apply(auto simp add: type_wf_defs split: option.splits)[1]
  using cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none is_node_kind_def apply blast
  using cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>N\<^sub>o\<^sub>d\<^sub>e_none is_node_kind_def apply blast
  done

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs elim!: ObjectMonad.type_wf_put_ptr_not_in_heap_E  
      split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "ObjectClass.type_wf h"
  assumes "is_node_ptr_kind ptr \<Longrightarrow> is_node_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs split: option.splits if_splits)
  by (metis ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf bind.bind_lunit get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def is_node_kind_def option.collapse)


subsection\<open>Preserving Types\<close>

lemma node_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "node_ptr_kinds h = node_ptr_kinds h'"
  by(simp add: node_ptr_kinds_def preserved_def object_ptr_kinds_preserved_small[OF assms])

lemma node_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' 
            \<longrightarrow> (\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "node_ptr_kinds h = node_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def node_ptr_kinds_def)
  by (metis assms object_ptr_kinds_preserved)


lemma type_wf_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  shows "type_wf h = type_wf h'"
  using type_wf_preserved allI[OF assms(2), of id, simplified]
  apply(auto simp add: type_wf_defs)
   apply(auto simp add: preserved_def get_M_defs node_ptr_kinds_small[OF assms(1)]
      split: option.splits, force)[1]
  by(auto simp add: preserved_def get_M_defs node_ptr_kinds_small[OF assms(1)]
      split: option.splits, force)[1]

lemma type_wf_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<Longrightarrow> \<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
           \<Longrightarrow> \<forall>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
    using assms type_wf_preserved_small by fast
  with assms(1) assms(2) show ?thesis
    apply(rule writes_small_big)
    by(auto simp add: reflp_def transp_def)
qed
end

