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
text\<open>In this theory, we introduce the monadic method setup for the Object class.\<close>
theory ObjectMonad
  imports
    BaseMonad
    "../classes/ObjectClass"
begin

type_synonym ('object_ptr, 'Object, 'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars "('object_ptr, 'Object, 'result) dom_prog" 

global_interpretation l_ptr_kinds_M object_ptr_kinds defines object_ptr_kinds_M = a_ptr_kinds_M .
lemmas object_ptr_kinds_M_defs = a_ptr_kinds_M_def


global_interpretation l_dummy defines get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t = "l_get_M.a_get_M get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t type_wf object_ptr_kinds"
  by (simp add: a_type_wf_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf l_get_M_def)
lemmas get_M_defs = get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t

locale l_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas = l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
begin
interpretation l_get_M get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t type_wf object_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf local.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t)
  by (simp add: a_type_wf_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf)
lemmas get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ok = get_M_ok[folded get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def]
lemmas get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ptr_in_heap = get_M_ptr_in_heap[folded get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def]
end

global_interpretation l_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas type_wf
  by (simp add: l_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas_def l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_axioms)

lemma object_ptr_kinds_M_reads: 
  "reads (\<Union>object_ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing)}) object_ptr_kinds_M h h'"
  apply(auto simp add: object_ptr_kinds_M_defs get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf type_wf_defs reads_def 
      preserved_def get_M_defs  
      split: option.splits)[1]
  using a_type_wf_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf by blast+


global_interpretation l_put_M type_wf object_ptr_kinds get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t 
  rewrites "a_get_M = get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t" 
  defines put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t


locale l_put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas = l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
begin
interpretation l_put_M  type_wf object_ptr_kinds get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
  apply(unfold_locales)
  using get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t local.l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_axioms apply blast
  by (simp add: a_type_wf_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf)
lemmas put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ok = put_M_ok[folded put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def]
lemmas put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ptr_in_heap = put_M_ptr_in_heap[folded put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def]
end

global_interpretation l_put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas type_wf
  by (simp add: l_put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas_def l_type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_axioms)


definition check_in_heap :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog"
  where
    "check_in_heap ptr = do {
      h \<leftarrow> get_heap;
      (if ptr |\<in>| object_ptr_kinds h then
        return ()
      else
        error SegmentationFault
      )}"

lemma check_in_heap_ptr_in_heap: "ptr |\<in>| object_ptr_kinds h \<longleftrightarrow> h \<turnstile> ok (check_in_heap ptr)"
  by(auto simp add: check_in_heap_def)
lemma check_in_heap_pure [simp]: "pure (check_in_heap ptr) h"
  by(auto simp add: check_in_heap_def intro!: bind_pure_I)
lemma check_in_heap_is_OK [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (check_in_heap ptr \<bind> f) = h \<turnstile> ok (f ())"
  by(simp add: check_in_heap_def)
lemma check_in_heap_returns_result [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> h \<turnstile> (check_in_heap ptr \<bind> f) \<rightarrow>\<^sub>r x = h \<turnstile> f () \<rightarrow>\<^sub>r x"
  by(simp add: check_in_heap_def)
lemma check_in_heap_returns_heap [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> h \<turnstile> (check_in_heap ptr \<bind> f) \<rightarrow>\<^sub>h h' = h \<turnstile> f () \<rightarrow>\<^sub>h h'"
  by(simp add: check_in_heap_def)

lemma check_in_heap_reads: 
  "reads {preserved (get_M object_ptr nothing)} (check_in_heap object_ptr) h h'"
  apply(simp add: check_in_heap_def reads_def preserved_def)
  by (metis a_type_wf_def get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ok get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_ptr_in_heap is_OK_returns_result_E 
      is_OK_returns_result_I unit_all_impI)

subsection\<open>Invoke\<close>

fun invoke_rec :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> 'args 
                  \<Rightarrow> (_, 'result) dom_prog)) list \<Rightarrow> (_) object_ptr \<Rightarrow> 'args 
                  \<Rightarrow> (_, 'result) dom_prog"
  where
    "invoke_rec ((P, f)#xs) ptr args = (if P ptr then f ptr args else invoke_rec xs ptr args)"
  | "invoke_rec [] ptr args = error InvokeError"

definition invoke :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> 'args 
                     \<Rightarrow> (_, 'result) dom_prog)) list 
                     \<Rightarrow> (_) object_ptr \<Rightarrow> 'args \<Rightarrow> (_, 'result) dom_prog"
  where                               
    "invoke xs ptr args = do { check_in_heap ptr; invoke_rec xs ptr args}"

lemma invoke_split: "P (invoke ((Pred, f) # xs) ptr args) =
    ((\<not>(Pred ptr) \<longrightarrow> P (invoke xs ptr args))
  \<and> (Pred ptr \<longrightarrow> P (do {check_in_heap ptr; f ptr args})))"
  by(simp add: invoke_def)

lemma invoke_split_asm: "P (invoke ((Pred, f) # xs) ptr args) =
    (\<not>((\<not>(Pred ptr) \<and> (\<not> P (invoke xs ptr args)))
    \<or> (Pred ptr \<and> (\<not> P (do {check_in_heap ptr; f ptr args})))))"
  by(simp add: invoke_def)
lemmas invoke_splits = invoke_split invoke_split_asm

lemma invoke_ptr_in_heap: "h \<turnstile> ok (invoke xs ptr args) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  by (metis bind_is_OK_E check_in_heap_ptr_in_heap invoke_def is_OK_returns_heap_I)

lemma invoke_pure [simp]: "pure (invoke [] ptr args) h"
  by(auto simp add: invoke_def intro!: bind_pure_I)

lemma invoke_is_OK [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> Pred ptr 
    \<Longrightarrow> h \<turnstile> ok (invoke ((Pred, f) # xs) ptr args) = h \<turnstile> ok (f ptr args)"
  by(simp add: invoke_def)
lemma invoke_returns_result [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> Pred ptr 
   \<Longrightarrow> h \<turnstile> (invoke ((Pred, f) # xs) ptr args) \<rightarrow>\<^sub>r x = h \<turnstile> f ptr args \<rightarrow>\<^sub>r x"
  by(simp add: invoke_def)
lemma invoke_returns_heap [simp]: 
  "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> Pred ptr 
   \<Longrightarrow> h \<turnstile> (invoke ((Pred, f) # xs) ptr args) \<rightarrow>\<^sub>h h' = h \<turnstile> f ptr args \<rightarrow>\<^sub>h h'"
  by(simp add: invoke_def)

lemma invoke_not [simp]: "\<not>Pred ptr \<Longrightarrow> invoke ((Pred, f) # xs) ptr args = invoke xs ptr args"
  by(auto simp add: invoke_def)

lemma invoke_empty [simp]: "\<not>h \<turnstile> ok (invoke [] ptr args)"
  by(auto simp add: invoke_def check_in_heap_def)

lemma invoke_empty_reads [simp]: "\<forall>P \<in> S. reflp P \<and> transp P \<Longrightarrow> reads S (invoke [] ptr args) h h'"
  apply(simp add: invoke_def reads_def preserved_def)
  by (meson bind_returns_result_E error_returns_result)


subsection\<open>Modified Heaps\<close>

lemma get_object_ptr_simp [simp]: 
  "get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = (if ptr = object_ptr then Some obj else get object_ptr h)"
  by(auto simp add: get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: option.splits Option.bind_splits)

lemma object_ptr_kinds_simp [simp]: "object_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = object_ptr_kinds h |\<union>| {|ptr|}"
  by(auto simp add: object_ptr_kinds_def put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: option.splits)

lemma type_wf_put_I:
  assumes "type_wf h"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  by(auto simp add: type_wf_defs split: option.splits)

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by(auto simp add: type_wf_defs split: option.splits if_splits)


subsection\<open>Preserving Types\<close>

lemma type_wf_preserved: "type_wf h = type_wf h'"
  by(auto simp add: type_wf_defs)


lemma object_ptr_kinds_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms
  apply(auto simp add: object_ptr_kinds_def preserved_def get_M_defs get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def 
      split: option.splits)[1]
   apply (metis (mono_tags, lifting) domIff error_returns_result fmdom.rep_eq fmember.rep_eq 
      old.unit.exhaust option.case_eq_if return_returns_result)
  by (metis (mono_tags, lifting) domIff error_returns_result fmdom.rep_eq fmember.rep_eq 
      old.unit.exhaust option.case_eq_if return_returns_result)

lemma object_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w object_ptr. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
          \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
proof -
  {
    fix object_ptr w
    have "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
      apply(rule writes_small_big[OF assms])
      by auto
  }
  then show ?thesis
    using object_ptr_kinds_preserved_small by blast
qed

end
