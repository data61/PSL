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

section\<open>Wellformedness\<close>
text\<open>In this theory, we discuss the wellformedness of the DOM. First, we define 
wellformedness and, second, we show for all functions for querying and modifying the 
DOM to what extend they preserve wellformendess.\<close>

theory Core_DOM_Heap_WF
imports
  "Core_DOM_Functions"
begin

locale l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_owner_document_valid :: "(_) heap \<Rightarrow> bool"
  where
    "a_owner_document_valid h = (\<forall>node_ptr. node_ptr |\<in>| node_ptr_kinds h \<longrightarrow>
      ((\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h 
         \<and> node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
    \<or> (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h 
            \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)))"


definition a_parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  where
    "a_parent_child_rel h = {(parent, child). parent |\<in>| object_ptr_kinds h 
                            \<and> child \<in> cast ` set |h \<turnstile> get_child_nodes parent|\<^sub>r}"

definition a_acyclic_heap :: "(_) heap \<Rightarrow> bool"
  where
    "a_acyclic_heap h = acyclic (a_parent_child_rel h)"


definition a_all_ptrs_in_heap :: "(_) heap \<Rightarrow> bool"
  where
    "a_all_ptrs_in_heap h = ((\<forall>ptr children. (h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children) 
    \<longrightarrow> fset_of_list children |\<subseteq>| node_ptr_kinds h)
      \<and> (\<forall>document_ptr disc_node_ptrs. (h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_node_ptrs) 
         \<longrightarrow> fset_of_list disc_node_ptrs |\<subseteq>| node_ptr_kinds h))"


definition a_distinct_lists :: "(_) heap \<Rightarrow> bool"
  where                     
    "a_distinct_lists h = distinct (concat (
      (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r) 
   @ (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) |h \<turnstile> document_ptr_kinds_M|\<^sub>r)
    ))"

definition a_heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  where
    "a_heap_is_wellformed h \<longleftrightarrow>
      a_acyclic_heap h \<and> a_all_ptrs_in_heap h \<and> a_distinct_lists h \<and> a_owner_document_valid h"
end

locale l_heap_is_wellformed_defs =
  fixes heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  fixes parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"

global_interpretation l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs 
                       get_disconnected_nodes get_disconnected_nodes_locs
defines heap_is_wellformed = "l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_heap_is_wellformed get_child_nodes 
                     get_disconnected_nodes"
      and parent_child_rel = "l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_parent_child_rel get_child_nodes"
  .

locale l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs
  + l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs get_disconnected_nodes 
                                    get_disconnected_nodes_locs
  + l_heap_is_wellformed_defs heap_is_wellformed parent_child_rel
  + l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set" +
  assumes heap_is_wellformed_impl: "heap_is_wellformed = a_heap_is_wellformed"
  assumes parent_child_rel_impl: "parent_child_rel = a_parent_child_rel"
begin
lemmas heap_is_wellformed_def = heap_is_wellformed_impl[unfolded a_heap_is_wellformed_def]
lemmas parent_child_rel_def = parent_child_rel_impl[unfolded a_parent_child_rel_def]
lemmas acyclic_heap_def = a_acyclic_heap_def[folded parent_child_rel_impl]

lemma parent_child_rel_node_ptr:
  "(parent, child) \<in> parent_child_rel h \<Longrightarrow> is_node_ptr_kind child"
  by(auto simp add: parent_child_rel_def)

lemma parent_child_rel_child_nodes:
  assumes "known_ptr parent"
    and "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
    and "child \<in> set children"
  shows "(parent, cast child) \<in> parent_child_rel h"
  using assms
  apply(auto simp add: parent_child_rel_def is_OK_returns_result_I )[1]
  using get_child_nodes_ptr_in_heap by blast

lemma parent_child_rel_child_nodes2:
  assumes "known_ptr parent"
    and "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
    and "child \<in> set children"
    and "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = child_obj"
  shows "(parent, child_obj) \<in> parent_child_rel h"
  using assms parent_child_rel_child_nodes by blast


lemma parent_child_rel_finite: "finite (parent_child_rel h)"
proof -
  have "parent_child_rel h = (\<Union>ptr \<in> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r. 
                 (\<Union>child \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r. {(ptr, cast child)}))"
    by(auto simp add: parent_child_rel_def)
  moreover have "finite (\<Union>ptr \<in> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r. 
                    (\<Union>child \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r. {(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)}))"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma distinct_lists_no_parent:
  assumes "a_distinct_lists h"
  assumes "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assumes "node_ptr \<in> set disc_nodes"
  shows "\<not>(\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h 
                \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
  using assms
  apply(auto simp add: a_distinct_lists_def)[1]
proof -
  fix parent_ptr :: "(_) object_ptr"
  assume a1: "parent_ptr |\<in>| object_ptr_kinds h"
  assume a2: "(\<Union>x\<in>fset (object_ptr_kinds h). 
              set |h \<turnstile> get_child_nodes x|\<^sub>r) \<inter> (\<Union>x\<in>fset (document_ptr_kinds h). 
                  set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
  assume a3: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assume a4: "node_ptr \<in> set disc_nodes"
  assume a5: "node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r"
  have f6: "parent_ptr \<in> fset (object_ptr_kinds h)"
    using a1 by auto
  have f7: "document_ptr \<in> fset (document_ptr_kinds h)"
    using a3 by (meson fmember.rep_eq get_disconnected_nodes_ptr_in_heap is_OK_returns_result_I)
  have "|h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r = disc_nodes"
    using a3 by simp
  then show False
    using f7 f6 a5 a4 a2 by blast
qed


lemma distinct_lists_disconnected_nodes:
  assumes "a_distinct_lists h"
    and "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  shows "distinct disc_nodes"
proof -
  have h1: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                             |h \<turnstile> document_ptr_kinds_M|\<^sub>r))"
    using assms(1)
    by(simp add: a_distinct_lists_def)
  then show ?thesis
    using concat_map_all_distinct[OF h1] assms(2) is_OK_returns_result_I get_disconnected_nodes_ok
    by (metis (no_types, lifting) DocumentMonad.ptr_kinds_ptr_kinds_M 
                                  l_get_disconnected_nodes.get_disconnected_nodes_ptr_in_heap 
                                  l_get_disconnected_nodes_axioms select_result_I2)
qed

lemma distinct_lists_children:
  assumes "a_distinct_lists h"
    and "known_ptr ptr"
    and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  shows "distinct children"
proof (cases "children = []", simp)
  assume "children \<noteq> []"
  have h1: "distinct (concat ((map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r)))"
    using assms(1)
    by(simp add: a_distinct_lists_def)
  show ?thesis
    using concat_map_all_distinct[OF h1] assms(2) assms(3)
    by (metis (no_types, lifting) ObjectMonad.ptr_kinds_ptr_kinds_M get_child_nodes_ptr_in_heap 
                                  is_OK_returns_result_I select_result_I2)
qed

lemma heap_is_wellformed_children_in_heap:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "child \<in> set children"
  shows "child |\<in>| node_ptr_kinds h"
  using assms
  apply(auto simp add: heap_is_wellformed_def a_all_ptrs_in_heap_def)[1]
  by (meson fset_of_list_elem fset_rev_mp)

lemma heap_is_wellformed_one_parent:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children'"
  assumes "set children \<inter> set children' \<noteq> {}"
  shows "ptr = ptr'"
  using assms
proof (auto simp add: heap_is_wellformed_def a_distinct_lists_def)[1]
  fix x :: "(_) node_ptr"
  assume a1: "ptr \<noteq> ptr'"
  assume a2: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assume a3: "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children'"
  assume a4: "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) 
                                     (sorted_list_of_set (fset (object_ptr_kinds h)))))"
  have f5: "|h \<turnstile> get_child_nodes ptr|\<^sub>r = children"
    using a2 by simp
  have "|h \<turnstile> get_child_nodes ptr'|\<^sub>r = children'"
    using a3 by (meson select_result_I2)
  then have "ptr \<notin> set (sorted_list_of_set (fset (object_ptr_kinds h))) 
          \<or> ptr' \<notin> set (sorted_list_of_set (fset (object_ptr_kinds h))) 
          \<or> set children \<inter> set children' = {}"
    using f5 a4 a1 by (meson distinct_concat_map_E(1))
  then show False
    using a3 a2 by (metis (no_types) assms(4) finite_fset fmember.rep_eq is_OK_returns_result_I 
                                          local.get_child_nodes_ptr_in_heap set_sorted_list_of_set)
qed

lemma parent_child_rel_child: 
  "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> child \<in> set children \<longleftrightarrow> (ptr, cast child) \<in> parent_child_rel h"
  by (simp add: is_OK_returns_result_I get_child_nodes_ptr_in_heap parent_child_rel_def)

lemma parent_child_rel_acyclic: "heap_is_wellformed h \<Longrightarrow> acyclic (parent_child_rel h)"
  by (simp add: acyclic_heap_def local.heap_is_wellformed_def)

lemma heap_is_wellformed_disconnected_nodes_distinct: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow> distinct disc_nodes"
  using distinct_lists_disconnected_nodes local.heap_is_wellformed_def by blast

lemma parent_child_rel_parent_in_heap: 
  "(parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> parent |\<in>| object_ptr_kinds h"
  using local.parent_child_rel_def by blast

lemma parent_child_rel_child_in_heap: 
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptr parent 
    \<Longrightarrow> (parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> child_ptr |\<in>| object_ptr_kinds h"
  apply(auto simp add: heap_is_wellformed_def parent_child_rel_def a_all_ptrs_in_heap_def)[1]
  using get_child_nodes_ok
  by (meson fin_mono fset_of_list_elem returns_result_select_result)

lemma heap_is_wellformed_disc_nodes_in_heap: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
   \<Longrightarrow> node \<in> set disc_nodes \<Longrightarrow> node |\<in>| node_ptr_kinds h"
  by (meson fset_mp fset_of_list_elem local.a_all_ptrs_in_heap_def local.heap_is_wellformed_def)

lemma heap_is_wellformed_one_disc_parent: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
   \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr' \<rightarrow>\<^sub>r disc_nodes' 
   \<Longrightarrow> set disc_nodes \<inter> set disc_nodes' \<noteq> {} \<Longrightarrow> document_ptr = document_ptr'"
  using DocumentMonad.ptr_kinds_ptr_kinds_M concat_append distinct_append distinct_concat_map_E(1) 
        is_OK_returns_result_I local.a_distinct_lists_def local.get_disconnected_nodes_ptr_in_heap 
        local.heap_is_wellformed_def select_result_I2
proof -
  assume a1: "heap_is_wellformed h"
  assume a2: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assume a3: "h \<turnstile> get_disconnected_nodes document_ptr' \<rightarrow>\<^sub>r disc_nodes'"
  assume a4: "set disc_nodes \<inter> set disc_nodes' \<noteq> {}"
  have f5: "|h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r = disc_nodes"
    using a2 by (meson select_result_I2)
  have f6: "|h \<turnstile> get_disconnected_nodes document_ptr'|\<^sub>r = disc_nodes'"
    using a3 by (meson select_result_I2)
  have "\<And>nss nssa. \<not> distinct (concat (nss @ nssa)) \<or> distinct (concat nssa::(_) node_ptr list)"
    by (metis (no_types) concat_append distinct_append)
  then have "distinct (concat (map (\<lambda>d. |h \<turnstile> get_disconnected_nodes d|\<^sub>r) |h \<turnstile> document_ptr_kinds_M|\<^sub>r))"
    using a1 local.a_distinct_lists_def local.heap_is_wellformed_def by blast
  then show ?thesis
    using f6 f5 a4 a3 a2 by (meson DocumentMonad.ptr_kinds_ptr_kinds_M distinct_concat_map_E(1) 
                                   is_OK_returns_result_I local.get_disconnected_nodes_ptr_in_heap)
qed

lemma heap_is_wellformed_children_disc_nodes_different: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
    \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
   \<Longrightarrow> set children \<inter> set disc_nodes = {}"
  by (metis (no_types, hide_lams) disjoint_iff_not_equal distinct_lists_no_parent 
                                  is_OK_returns_result_I local.get_child_nodes_ptr_in_heap 
                                  local.heap_is_wellformed_def select_result_I2)

lemma heap_is_wellformed_children_disc_nodes: 
  "heap_is_wellformed h \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h 
   \<Longrightarrow>  \<not>(\<exists>parent \<in> fset (object_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r) 
   \<Longrightarrow> (\<exists>document_ptr \<in> fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
  apply(auto simp add: heap_is_wellformed_def a_distinct_lists_def a_owner_document_valid_def)[1]
  by (meson fmember.rep_eq)
lemma heap_is_wellformed_children_distinct: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
  by (metis (no_types, lifting) ObjectMonad.ptr_kinds_ptr_kinds_M concat_append distinct_append 
                                distinct_concat_map_E(2) is_OK_returns_result_I local.a_distinct_lists_def 
                                local.get_child_nodes_ptr_in_heap local.heap_is_wellformed_def 
                               select_result_I2)
end

locale l_heap_is_wellformed = l_type_wf + l_known_ptr + l_heap_is_wellformed_defs 
                              + l_get_child_nodes_defs + l_get_disconnected_nodes_defs +
assumes heap_is_wellformed_children_in_heap: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> child \<in> set children 
                        \<Longrightarrow> child |\<in>| node_ptr_kinds h"
assumes heap_is_wellformed_disc_nodes_in_heap: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
                        \<Longrightarrow> node \<in> set disc_nodes \<Longrightarrow> node |\<in>| node_ptr_kinds h"
assumes heap_is_wellformed_one_parent: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
                        \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children' 
                        \<Longrightarrow> set children \<inter> set children' \<noteq> {} \<Longrightarrow> ptr = ptr'"
assumes heap_is_wellformed_one_disc_parent: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
                        \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr' \<rightarrow>\<^sub>r disc_nodes' 
                        \<Longrightarrow> set disc_nodes \<inter> set disc_nodes' \<noteq> {} \<Longrightarrow> document_ptr = document_ptr'"
assumes heap_is_wellformed_children_disc_nodes_different: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
                        \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
                        \<Longrightarrow> set children \<inter> set disc_nodes = {}"
assumes heap_is_wellformed_disconnected_nodes_distinct: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes 
                        \<Longrightarrow> distinct disc_nodes"
assumes heap_is_wellformed_children_distinct: 
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
assumes heap_is_wellformed_children_disc_nodes: 
  "heap_is_wellformed h \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h 
   \<Longrightarrow>  \<not>(\<exists>parent \<in> fset (object_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r) 
   \<Longrightarrow> (\<exists>document_ptr \<in> fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
assumes parent_child_rel_child: 
  "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
   \<Longrightarrow> child \<in> set children \<longleftrightarrow> (ptr, cast child) \<in> parent_child_rel h"
assumes parent_child_rel_finite: 
  "heap_is_wellformed h \<Longrightarrow> finite (parent_child_rel h)"
assumes parent_child_rel_acyclic: 
  "heap_is_wellformed h \<Longrightarrow> acyclic (parent_child_rel h)"
assumes parent_child_rel_node_ptr: 
  "(parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> is_node_ptr_kind child_ptr"
assumes parent_child_rel_parent_in_heap: 
  "(parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> parent |\<in>| object_ptr_kinds h"
assumes parent_child_rel_child_in_heap: 
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptr parent 
   \<Longrightarrow> (parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> child_ptr |\<in>| object_ptr_kinds h"

interpretation i_heap_is_wellformed?: l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes 
               get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs 
               heap_is_wellformed parent_child_rel
  apply(unfold_locales)
  by(auto simp add: heap_is_wellformed_def parent_child_rel_def)
declare l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma heap_is_wellformed_is_l_heap_is_wellformed [instances]:
  "l_heap_is_wellformed type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes 
                        get_disconnected_nodes"
  apply(auto simp add: l_heap_is_wellformed_def)[1]
  using heap_is_wellformed_children_in_heap 
                apply blast
  using heap_is_wellformed_disc_nodes_in_heap 
               apply blast
  using heap_is_wellformed_one_parent 
              apply blast
  using heap_is_wellformed_one_disc_parent 
             apply blast
  using heap_is_wellformed_children_disc_nodes_different 
            apply blast
  using heap_is_wellformed_disconnected_nodes_distinct 
           apply blast
  using heap_is_wellformed_children_distinct 
          apply blast
  using heap_is_wellformed_children_disc_nodes 
         apply blast
  using parent_child_rel_child 
        apply (blast)
  using parent_child_rel_child 
       apply(blast)
  using parent_child_rel_finite 
      apply blast
  using parent_child_rel_acyclic 
     apply blast
  using parent_child_rel_node_ptr 
    apply blast
  using parent_child_rel_parent_in_heap 
   apply blast
  using parent_child_rel_child_in_heap 
  apply blast
  done

subsection \<open>get\_parent\<close>

locale l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  + l_heap_is_wellformed
    type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes get_child_nodes_locs 
    get_disconnected_nodes get_disconnected_nodes_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma child_parent_dual:
  assumes heap_is_wellformed: "heap_is_wellformed h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "child \<in> set children"
  assumes "known_ptrs h"
  assumes type_wf: "type_wf h"
  shows "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr"
proof -
  obtain ptrs where ptrs: "h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have h1: "ptr \<in> set ptrs"
    using get_child_nodes_ok assms(2) is_OK_returns_result_I 
    by (metis (no_types, hide_lams) ObjectMonad.ptr_kinds_ptr_kinds_M 
      \<open>\<And>thesis. (\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
     get_child_nodes_ptr_in_heap returns_result_eq select_result_I2)

  let ?P = "(\<lambda>ptr. get_child_nodes ptr \<bind> (\<lambda>children. return (child \<in> set children)))"
  let ?filter = "filter_M ?P ptrs"

  have "h \<turnstile> ok ?filter"
    using ptrs type_wf
    using get_child_nodes_ok
    apply(auto intro!: filter_M_is_OK_I bind_is_OK_pure_I get_child_nodes_ok simp add: bind_pure_I)[1]
    using assms(4) local.known_ptrs_known_ptr by blast 
  then obtain parent_ptrs where parent_ptrs: "h \<turnstile> ?filter \<rightarrow>\<^sub>r parent_ptrs"
    by auto

  have h5: "\<exists>!x. x \<in> set ptrs \<and> h \<turnstile> Heap_Error_Monad.bind (get_child_nodes x) 
                  (\<lambda>children. return (child \<in> set children)) \<rightarrow>\<^sub>r True"
    apply(auto intro!: bind_pure_returns_result_I)[1]
    using heap_is_wellformed_one_parent
  proof -
    have "h \<turnstile> (return (child \<in> set children)::((_) heap, exception, bool) prog) \<rightarrow>\<^sub>r True"
      by (simp add: assms(3))
    then show 
      "\<exists>z. z \<in> set ptrs \<and> h \<turnstile> Heap_Error_Monad.bind (get_child_nodes z) 
                               (\<lambda>ns. return (child \<in> set ns)) \<rightarrow>\<^sub>r True"
      by (metis (no_types) assms(2) bind_pure_returns_result_I2 h1 is_OK_returns_result_I 
                                local.get_child_nodes_pure select_result_I2)
  next
    fix x y
    assume 0: "x \<in> set ptrs"
      and 1: "h \<turnstile> Heap_Error_Monad.bind (get_child_nodes x) 
                  (\<lambda>children. return (child \<in> set children)) \<rightarrow>\<^sub>r True"
      and 2: "y \<in> set ptrs"
      and 3: "h \<turnstile> Heap_Error_Monad.bind (get_child_nodes y) 
                  (\<lambda>children. return (child \<in> set children)) \<rightarrow>\<^sub>r True"
      and 4: "(\<And>h ptr children ptr' children'. heap_is_wellformed h 
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children' 
              \<Longrightarrow> set children \<inter> set children' \<noteq> {} \<Longrightarrow> ptr = ptr')"
    then show "x = y"
      by (metis (no_types, lifting) bind_returns_result_E disjoint_iff_not_equal heap_is_wellformed 
                                    return_returns_result)
  qed

  have "child |\<in>| node_ptr_kinds h"
    using heap_is_wellformed_children_in_heap heap_is_wellformed assms(2) assms(3)
    by fast 
  moreover have "parent_ptrs = [ptr]"
    apply(rule filter_M_ex1[OF parent_ptrs h1 h5])
    using ptrs assms(2) assms(3) 
    by(auto simp add: object_ptr_kinds_M_defs bind_pure_I intro!: bind_pure_returns_result_I)
  ultimately  show ?thesis
    using ptrs parent_ptrs
    by(auto simp add: bind_pure_I get_parent_def 
            elim!: bind_returns_result_E2 
            intro!: bind_pure_returns_result_I filter_M_pure_I) (*slow, ca 1min *)
qed

lemma parent_child_rel_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent"
  shows "(parent, cast child_node) \<in> parent_child_rel h"
  using assms parent_child_rel_child get_parent_child_dual by auto

lemma heap_wellformed_induct [consumes 1, case_names step]:
  assumes "heap_is_wellformed h"
    and step: "\<And>parent. (\<And>children child. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children 
               \<Longrightarrow> child \<in> set children \<Longrightarrow> P (cast child)) \<Longrightarrow> P parent"
  shows "P ptr"
proof -
  fix ptr
  have "wf ((parent_child_rel h)\<inverse>)"
    by (simp add: assms(1) finite_acyclic_wf_converse parent_child_rel_acyclic parent_child_rel_finite)
  then show "?thesis"
  proof (induct rule: wf_induct_rule)
    case (less parent)
    then show ?case
      using assms child_parent_dual parent_child_rel_parent
      by (meson converse_iff parent_child_rel_child)
  qed
qed

lemma heap_wellformed_induct2 [consumes 3, case_names not_in_heap empty_children step]:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
    and not_in_heap: "\<And>parent. parent |\<notin>| object_ptr_kinds h \<Longrightarrow> P parent"
    and empty_children: "\<And>parent. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r [] \<Longrightarrow> P parent"
    and step: "\<And>parent children child. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children 
               \<Longrightarrow> child \<in> set children \<Longrightarrow> P (cast child) \<Longrightarrow> P parent"
  shows "P ptr"
proof(insert assms(1), induct rule: heap_wellformed_induct)
  case (step parent)
  then show ?case
  proof(cases "parent |\<in>| object_ptr_kinds h")
    case True
    then obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
      using get_child_nodes_ok assms(2) assms(3) 
      by (meson is_OK_returns_result_E local.known_ptrs_known_ptr)
    then show ?thesis
    proof (cases "children = []")
      case True
      then show ?thesis
        using children empty_children
        by simp
    next
      case False
      then show ?thesis
        using assms(6) children last_in_set step.hyps by blast
    qed
  next
    case False
    then show ?thesis 
      by (simp add: not_in_heap)
  qed
qed

lemma heap_wellformed_induct_rev [consumes 1, case_names step]:
  assumes "heap_is_wellformed h"
    and step: "\<And>child. (\<And>parent child_node. cast child_node = child 
               \<Longrightarrow> h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> P parent) \<Longrightarrow> P child"
  shows "P ptr"
proof -
  fix ptr
  have "wf ((parent_child_rel h))"
    by (simp add: assms(1) local.parent_child_rel_acyclic local.parent_child_rel_finite 
                wf_iff_acyclic_if_finite)

  then show "?thesis"
  proof (induct rule: wf_induct_rule)
    case (less child)
    show ?case
      using assms get_parent_child_dual
      by (metis less.hyps parent_child_rel_parent)
  qed
qed
end

interpretation i_get_parent_wf?: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes 
               get_child_nodes_locs known_ptrs get_parent get_parent_locs heap_is_wellformed 
               parent_child_rel get_disconnected_nodes
  using instances
  by(simp add: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


locale l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs 
    heap_is_wellformed parent_child_rel get_disconnected_nodes get_disconnected_nodes_locs
  + l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs get_disconnected_nodes 
    get_disconnected_nodes_locs heap_is_wellformed parent_child_rel
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma preserves_wellformedness_writes_needed:
  assumes heap_is_wellformed: "heap_is_wellformed h"
    and "h \<turnstile> f \<rightarrow>\<^sub>h h'"
    and "writes SW f h h'"
    and preserved_get_child_nodes: 
    "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
                      \<Longrightarrow> \<forall>object_ptr. \<forall>r \<in> get_child_nodes_locs object_ptr. r h h'"
    and preserved_get_disconnected_nodes: 
    "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
                      \<Longrightarrow> \<forall>document_ptr. \<forall>r \<in> get_disconnected_nodes_locs document_ptr. r h h'"
    and preserved_object_pointers: 
    "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' 
                     \<Longrightarrow> \<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
shows "heap_is_wellformed h'"
proof -
  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    using assms(2) assms(3) object_ptr_kinds_preserved preserved_object_pointers by blast
  then have object_ptr_kinds_eq: 
       "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp 
  then have object_ptr_kinds_eq2: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    using select_result_eq by force
  then have node_ptr_kinds_eq2: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by auto
  then have node_ptr_kinds_eq3: "node_ptr_kinds h = node_ptr_kinds h'"
    by auto
  have document_ptr_kinds_eq2: "|h \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_eq2 document_ptr_kinds_M_eq by auto
  then have document_ptr_kinds_eq3: "document_ptr_kinds h = document_ptr_kinds h'"
     by auto
   have children_eq: 
    "\<And>ptr children. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    apply(rule reads_writes_preserved[OF get_child_nodes_reads assms(3) assms(2)])
    using preserved_get_child_nodes by fast
  then have children_eq2: "\<And>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r = |h' \<turnstile> get_child_nodes ptr|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq: 
    "\<And>document_ptr disconnected_nodes. 
        h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes 
                             = h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes"
    apply(rule reads_writes_preserved[OF get_disconnected_nodes_reads assms(3) assms(2)])
    using preserved_get_disconnected_nodes by fast
  then have disconnected_nodes_eq2: 
         "\<And>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r 
                            = |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using select_result_eq by force
  have get_parent_eq: "\<And>ptr parent. h \<turnstile> get_parent ptr \<rightarrow>\<^sub>r parent = h' \<turnstile> get_parent ptr \<rightarrow>\<^sub>r parent"
    apply(rule reads_writes_preserved[OF get_parent_reads assms(3) assms(2)])
    using preserved_get_child_nodes preserved_object_pointers unfolding get_parent_locs_def by fast
  have "a_acyclic_heap h"
    using heap_is_wellformed by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h' \<subseteq> parent_child_rel h"
  proof
    fix x
    assume "x \<in> parent_child_rel h'"
    then show "x \<in> parent_child_rel h"
      by(simp add: parent_child_rel_def  children_eq2 object_ptr_kinds_eq3)
  qed
  then have "a_acyclic_heap h'"
    using \<open>a_acyclic_heap h\<close> acyclic_heap_def acyclic_subset by blast

  moreover have "a_all_ptrs_in_heap h"
    using heap_is_wellformed by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h'"
    by(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_def node_ptr_kinds_eq2 
                      object_ptr_kinds_eq3 children_eq disconnected_nodes_eq)

  moreover have h0: "a_distinct_lists h"
    using heap_is_wellformed by (simp add: heap_is_wellformed_def)
  have h1: "map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) (sorted_list_of_set (fset (object_ptr_kinds h))) 
         = map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r) (sorted_list_of_set (fset (object_ptr_kinds h')))"
    by (simp add: children_eq2 object_ptr_kinds_eq3)                                                                                    
  have h2: "map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
               (sorted_list_of_set (fset (document_ptr_kinds h))) 
          = map (\<lambda>document_ptr. |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                (sorted_list_of_set (fset (document_ptr_kinds h')))"
    using disconnected_nodes_eq document_ptr_kinds_eq2 select_result_eq by force
  have "a_distinct_lists h'"
    using h0 
    by(simp add: a_distinct_lists_def h1 h2)

  moreover have "a_owner_document_valid h"
    using heap_is_wellformed by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    by(auto simp add: a_owner_document_valid_def children_eq2 disconnected_nodes_eq2 
                      object_ptr_kinds_eq3 node_ptr_kinds_eq3 document_ptr_kinds_eq3)
  ultimately show ?thesis
    by (simp add: heap_is_wellformed_def)
qed
end

interpretation i_get_parent_wf2?: l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes 
                                  get_child_nodes_locs known_ptrs get_parent get_parent_locs 
                                  heap_is_wellformed parent_child_rel get_disconnected_nodes 
                                  get_disconnected_nodes_locs
  using l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
  by (simp add: l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)

declare l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]
locale l_get_parent_wf = l_type_wf + l_known_ptrs  + l_heap_is_wellformed_defs 
                       + l_get_child_nodes_defs + l_get_parent_defs +
  assumes child_parent_dual:
    "heap_is_wellformed h
    \<Longrightarrow> type_wf h
    \<Longrightarrow> known_ptrs h
    \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children
    \<Longrightarrow> child \<in> set children
    \<Longrightarrow> h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr"
  assumes heap_wellformed_induct [consumes 1, case_names step]:
    "heap_is_wellformed h
    \<Longrightarrow> (\<And>parent. (\<And>children child. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children 
    \<Longrightarrow> child \<in> set children \<Longrightarrow> P (cast child)) \<Longrightarrow> P parent)
    \<Longrightarrow> P ptr"
  assumes heap_wellformed_induct_rev [consumes 1, case_names step]:
    "heap_is_wellformed h
    \<Longrightarrow> (\<And>child. (\<And>parent child_node. cast child_node = child 
    \<Longrightarrow> h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> P parent) \<Longrightarrow> P child)
    \<Longrightarrow> P ptr"
  assumes parent_child_rel_parent: "heap_is_wellformed h 
    \<Longrightarrow> h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent 
    \<Longrightarrow> (parent, cast child_node) \<in> parent_child_rel h"

lemma get_parent_wf_is_l_get_parent_wf [instances]: 
  "l_get_parent_wf type_wf known_ptr known_ptrs heap_is_wellformed parent_child_rel 
  get_child_nodes get_parent"
  using known_ptrs_is_l_known_ptrs
  apply(auto simp add: l_get_parent_wf_def l_get_parent_wf_axioms_def)[1]
  using child_parent_dual heap_wellformed_induct heap_wellformed_induct_rev parent_child_rel_parent
  by metis+ 



subsection \<open>get\_disconnected\_nodes\<close>



subsection \<open>set\_disconnected\_nodes\<close>


subsubsection \<open>get\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_disconnected_nodes
    type_wf get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
    set_disconnected_nodes_locs
  + l_heap_is_wellformed
    type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes get_child_nodes_locs 
    get_disconnected_nodes get_disconnected_nodes_locs
  for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin

lemma remove_from_disconnected_nodes_removes:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes"
  assumes "h \<turnstile> set_disconnected_nodes ptr (remove1 node_ptr disc_nodes) \<rightarrow>\<^sub>h h'"
  assumes "h' \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes'"
  shows "node_ptr \<notin> set disc_nodes'"
  using assms
  by (metis distinct_remove1_removeAll heap_is_wellformed_disconnected_nodes_distinct 
            set_disconnected_nodes_get_disconnected_nodes member_remove remove_code(1) 
            returns_result_eq)
end

locale l_set_disconnected_nodes_get_disconnected_nodes_wf = l_heap_is_wellformed
          + l_set_disconnected_nodes_get_disconnected_nodes +
  assumes remove_from_disconnected_nodes_removes:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes 
                          \<Longrightarrow> h \<turnstile> set_disconnected_nodes ptr (remove1 node_ptr disc_nodes) \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> h' \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes' 
                          \<Longrightarrow> node_ptr \<notin> set disc_nodes'"

interpretation i_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M?:
  l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M  known_ptr type_wf get_disconnected_nodes 
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs heap_is_wellformed 
  parent_child_rel get_child_nodes
  using instances
  by (simp add: l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]
 
lemma set_disconnected_nodes_get_disconnected_nodes_wf_is_l_set_disconnected_nodes_get_disconnected_nodes_wf [instances]:
  "l_set_disconnected_nodes_get_disconnected_nodes_wf type_wf known_ptr heap_is_wellformed parent_child_rel 
   get_child_nodes get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
      set_disconnected_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_disconnected_nodes_wf_def 
                       l_set_disconnected_nodes_get_disconnected_nodes_wf_axioms_def instances)[1]
  using remove_from_disconnected_nodes_removes apply fast
  done


subsection \<open>get\_root\_node\<close>

locale l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed
    type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes get_child_nodes_locs 
    get_disconnected_nodes get_disconnected_nodes_locs
  + l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs get_parent get_parent_locs
  + l_get_parent_wf
    type_wf known_ptr known_ptrs heap_is_wellformed parent_child_rel get_child_nodes 
    get_child_nodes_locs get_parent get_parent_locs
  + l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs 
    get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
  and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
  and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
  and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

begin
lemma get_ancestors_reads:
  assumes "heap_is_wellformed h"
  shows "reads get_ancestors_locs (get_ancestors node_ptr) h h'"
proof (insert assms(1), induct rule: heap_wellformed_induct_rev)
  case (step child)
  then show ?case
    using [[simproc del: Product_Type.unit_eq]] get_parent_reads[unfolded reads_def]
    apply(simp (no_asm) add: get_ancestors_def)
    by(auto simp add: get_ancestors_locs_def reads_subset[OF return_reads] get_parent_reads_pointers 
            intro!: reads_bind_pure reads_subset[OF check_in_heap_reads] 
                    reads_subset[OF get_parent_reads] reads_subset[OF get_child_nodes_reads] 
            split: option.splits)
qed

lemma get_ancestors_ok:
  assumes "heap_is_wellformed h"
    and "ptr |\<in>| object_ptr_kinds h"
    and "known_ptrs h"
    and type_wf: "type_wf h"
  shows "h \<turnstile> ok (get_ancestors ptr)"
proof (insert assms(1) assms(2), induct rule: heap_wellformed_induct_rev)
  case (step child)
  then show ?case
    using assms(3) assms(4)
    apply(simp (no_asm) add: get_ancestors_def)
    apply(simp add: assms(1) get_parent_parent_in_heap)
    by(auto intro!: bind_is_OK_pure_I bind_pure_I get_parent_ok split: option.splits)
qed

lemma get_root_node_ptr_in_heap:
  assumes "h \<turnstile> ok (get_root_node ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  unfolding get_root_node_def
  using get_ancestors_ptr_in_heap
  by auto


lemma get_root_node_ok:
  assumes "heap_is_wellformed h" "known_ptrs h" "type_wf h"
    and "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_root_node ptr)"
  unfolding get_root_node_def
  using assms get_ancestors_ok
  by auto


lemma get_ancestors_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
  shows "h \<turnstile> get_ancestors (cast child) \<rightarrow>\<^sub>r (cast child) # parent # ancestors 
     \<longleftrightarrow> h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r parent # ancestors"
proof
  assume a1: "h \<turnstile> get_ancestors (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child # parent # ancestors"
  then have "h \<turnstile> Heap_Error_Monad.bind (check_in_heap (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child))
          (\<lambda>_. Heap_Error_Monad.bind (get_parent child)
              (\<lambda>x. Heap_Error_Monad.bind (case x of None \<Rightarrow> return [] | Some x \<Rightarrow> get_ancestors x) 
               (\<lambda>ancestors. return (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child # ancestors))))
        \<rightarrow>\<^sub>r cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child # parent # ancestors"
    by(simp add: get_ancestors_def)
  then show "h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r parent # ancestors"
    using assms(2) apply(auto elim!: bind_returns_result_E2 split: option.splits)[1]
    using returns_result_eq by fastforce
next
  assume "h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r parent # ancestors"
  then show "h \<turnstile> get_ancestors (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child # parent # ancestors"
    using assms(2) 
    apply(simp (no_asm) add: get_ancestors_def)
    apply(auto intro!: bind_pure_returns_result_I split: option.splits)[1]
    by (metis (full_types) assms(2) check_in_heap_ptr_in_heap is_OK_returns_result_I 
                           local.get_parent_ptr_in_heap node_ptr_kinds_commutes old.unit.exhaust 
                           select_result_I)
qed


lemma get_ancestors_never_empty:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors child \<rightarrow>\<^sub>r ancestors"
  shows "ancestors \<noteq> []"
proof(insert assms(2), induct arbitrary: ancestors rule: heap_wellformed_induct_rev[OF assms(1)])
  case (1 child)
  then show ?case
  proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    then show ?case
      apply(simp add: get_ancestors_def)
      by(auto elim!: bind_returns_result_E2 split: option.splits)
  next
    case (Some child_node)
    then obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      apply(simp add: get_ancestors_def)
      by(auto elim!: bind_returns_result_E2 split: option.splits)
    with Some show ?case
    proof(induct parent_opt)
      case None
      then show ?case 
        apply(simp add: get_ancestors_def)
        by(auto elim!: bind_returns_result_E2 split: option.splits)
    next
      case (Some option)
      then show ?case 
        apply(simp add: get_ancestors_def)
        by(auto elim!: bind_returns_result_E2 split: option.splits)
    qed
  qed
qed



lemma get_ancestors_subset:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
    and "ancestor \<in> set ancestors"
    and "h \<turnstile> get_ancestors ancestor \<rightarrow>\<^sub>r ancestor_ancestors"
and type_wf: "type_wf h"
and known_ptrs: "known_ptrs h"
  shows "set ancestor_ancestors \<subseteq> set ancestors"
proof (insert assms(1) assms(2) assms(3), induct ptr arbitrary: ancestors 
              rule: heap_wellformed_induct_rev)
  case (step child)
  have "child |\<in>| object_ptr_kinds h"
    using get_ancestors_ptr_in_heap step(2) by auto
 (*  then have "h \<turnstile> check_in_heap child \<rightarrow>\<^sub>r ()"
    using returns_result_select_result by force *)
  show ?case
  proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    then have "ancestors = [child]"
      using step(2) step(3) 
      by(auto simp add: get_ancestors_def elim!: bind_returns_result_E2)
    show ?case
      using step(2) step(3)
      apply(auto simp add: \<open>ancestors = [child]\<close>)[1]
      using assms(4) returns_result_eq by fastforce
  next
    case (Some child_node)
    note s1 = Some
    obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      using \<open>child |\<in>| object_ptr_kinds h\<close> assms(1) Some[symmetric] get_parent_ok[OF type_wf known_ptrs]
      by (metis (no_types, lifting) is_OK_returns_result_E known_ptrs get_parent_ok 
                l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms node_ptr_casts_commute node_ptr_kinds_commutes)
    then show ?case
    proof (induct parent_opt)
      case None
      then have "ancestors = [child]"
        using step(2) step(3) s1
        apply(simp add: get_ancestors_def)
        by(auto elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
      show ?case
        using step(2) step(3)
        apply(auto simp add: \<open>ancestors = [child]\<close>)[1]
        using assms(4) returns_result_eq by fastforce
    next
      case (Some parent)
      have "h \<turnstile> Heap_Error_Monad.bind (check_in_heap child)
          (\<lambda>_. Heap_Error_Monad.bind
                 (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child of None \<Rightarrow> return []
                  | Some node_ptr \<Rightarrow> Heap_Error_Monad.bind (get_parent node_ptr) 
                                         (\<lambda>parent_ptr_opt. case parent_ptr_opt of None \<Rightarrow> return [] 
                                                                        | Some x \<Rightarrow> get_ancestors x))
                 (\<lambda>ancestors. return (child # ancestors)))
    \<rightarrow>\<^sub>r  ancestors"
        using step(2)
        by(simp add: get_ancestors_def)
      moreover obtain tl_ancestors where tl_ancestors: "ancestors = child # tl_ancestors"
        using calculation
        by(auto elim!: bind_returns_result_E2 split: option.splits)
      ultimately have "h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r tl_ancestors"
        using s1 Some
        by(auto elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
      show ?case
        using step(1)[OF s1[symmetric, simplified] Some \<open>h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r tl_ancestors\<close>] 
              step(3)
        apply(auto simp add: tl_ancestors)[1]
        by (metis assms(4) insert_iff list.simps(15) local.step(2) returns_result_eq tl_ancestors)
    qed
  qed
qed

lemma get_ancestors_also_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast child \<in> set ancestors"
    and "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "parent \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors (cast child) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(4) get_ancestors_ok is_OK_returns_result_I known_ptrs 
              local.get_parent_ptr_in_heap node_ptr_kinds_commutes returns_result_select_result 
              type_wf)
  then have "parent \<in> set child_ancestors"
    apply(simp add: get_ancestors_def)
    by(auto elim!: bind_returns_result_E2 split: option.splits dest!: returns_result_eq[OF assms(4)] 
                                                                     get_ancestors_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_subset by blast
qed

lemma get_ancestors_obtains_children:
  assumes "heap_is_wellformed h"
    and "ancestor \<noteq> ptr"
    and "ancestor \<in> set ancestors"
    and "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  obtains children ancestor_child where "h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children" 
    and "ancestor_child \<in> set children" and "cast ancestor_child \<in> set ancestors"
proof -
  assume 0: "(\<And>children ancestor_child.
        h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<Longrightarrow>
        ancestor_child \<in> set children \<Longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set ancestors 
        \<Longrightarrow> thesis)"
  have "\<exists>child. h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ancestor \<and> cast child \<in> set ancestors"
  proof (insert assms(1) assms(2) assms(3) assms(4), induct ptr arbitrary: ancestors 
                rule: heap_wellformed_induct_rev)
    case (step child)
    have "child |\<in>| object_ptr_kinds h"
      using get_ancestors_ptr_in_heap step(4) by auto
    show ?case
    proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
      case None
      then have "ancestors = [child]"
        using step(3) step(4)
        by(auto simp add: get_ancestors_def elim!: bind_returns_result_E2)
      show ?case
        using step(2) step(3) step(4)
        by(auto simp add: \<open>ancestors = [child]\<close>)
    next
      case (Some child_node)
      note s1 = Some
      obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
        using \<open>child |\<in>| object_ptr_kinds h\<close> assms(1) Some[symmetric]
        using get_parent_ok known_ptrs type_wf
        by (metis (no_types, lifting) is_OK_returns_result_E node_ptr_casts_commute 
                  node_ptr_kinds_commutes) 
      then show ?case
      proof (induct parent_opt)
        case None
        then have "ancestors = [child]"
          using step(2) step(3) step(4) s1
          apply(simp add: get_ancestors_def)
          by(auto elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
        show ?case
          using step(2) step(3) step(4)
          by(auto simp add: \<open>ancestors = [child]\<close>)
      next
        case (Some parent)
        have "h \<turnstile> Heap_Error_Monad.bind (check_in_heap child)
            (\<lambda>_. Heap_Error_Monad.bind
                   (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child of None \<Rightarrow> return []
                    | Some node_ptr \<Rightarrow> Heap_Error_Monad.bind (get_parent node_ptr) 
                       (\<lambda>parent_ptr_opt. case parent_ptr_opt of None \<Rightarrow> return [] 
                                                              | Some x \<Rightarrow> get_ancestors x))
                   (\<lambda>ancestors. return (child # ancestors)))
      \<rightarrow>\<^sub>r  ancestors"
          using step(4)
          by(simp add: get_ancestors_def)
        moreover obtain tl_ancestors where tl_ancestors: "ancestors = child # tl_ancestors"
          using calculation
          by(auto elim!: bind_returns_result_E2 split: option.splits)
        ultimately have "h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r tl_ancestors"
          using s1 Some
          by(auto elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
        (* have "ancestor \<noteq> parent" *)
        have "ancestor \<in> set tl_ancestors"
          using tl_ancestors step(2) step(3) by auto
        show ?case
        proof (cases "ancestor \<noteq> parent")
          case True
          show ?thesis 
            using step(1)[OF s1[symmetric, simplified] Some True 
                         \<open>ancestor \<in> set tl_ancestors\<close> \<open>h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r tl_ancestors\<close>]
            using tl_ancestors by auto
        next
          case False
          have "child \<in> set ancestors"
            using step(4) get_ancestors_ptr by simp
          then show ?thesis
            using Some False s1[symmetric] by(auto)
        qed
      qed
    qed
  qed
  then obtain child where child: "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ancestor" 
       and in_ancestors: "cast child \<in> set ancestors"
    by auto
  then obtain children where
    children: "h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children" and
    child_in_children: "child \<in> set children"
    using get_parent_child_dual by blast
  show thesis
    using 0[OF children child_in_children] child assms(3) in_ancestors by blast
qed

lemma get_ancestors_parent_child_rel:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors child \<rightarrow>\<^sub>r ancestors"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
shows "(ptr, child) \<in> (parent_child_rel h)\<^sup>* \<longleftrightarrow> ptr \<in> set ancestors"
proof (safe)
  assume 3: "(ptr, child) \<in> (parent_child_rel h)\<^sup>*"
  show "ptr \<in> set ancestors"
  proof (insert 3, induct ptr rule: heap_wellformed_induct[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        by (metis (no_types, lifting) assms(2) bind_returns_result_E get_ancestors_def
             in_set_member member_rec(1) return_returns_result)
    next
      case False
      obtain ptr_child where
        ptr_child: "(ptr, ptr_child) \<in> (parent_child_rel h) \<and> (ptr_child, child) \<in> (parent_child_rel h)\<^sup>*"
        using converse_rtranclE[OF 1(2)] \<open>ptr \<noteq> child\<close>
        by metis
      then obtain ptr_child_node 
           where ptr_child_ptr_child_node: "ptr_child = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node"
        using ptr_child node_ptr_casts_commute3 parent_child_rel_node_ptr
        by (metis )
      then obtain children where
        children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children" and
        ptr_child_node: "ptr_child_node \<in> set children"
      proof -
        assume a1: "\<And>children. \<lbrakk>h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children; ptr_child_node \<in> set children\<rbrakk> 
                   \<Longrightarrow> thesis"
   
        have "ptr |\<in>| object_ptr_kinds h"
          using local.parent_child_rel_parent_in_heap ptr_child by blast
        moreover have "ptr_child_node \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r"
          by (metis calculation known_ptrs local.get_child_nodes_ok local.known_ptrs_known_ptr 
                    local.parent_child_rel_child ptr_child ptr_child_ptr_child_node 
                    returns_result_select_result type_wf)
        ultimately show ?thesis
          using a1 get_child_nodes_ok type_wf known_ptrs
          by (meson local.known_ptrs_known_ptr returns_result_select_result) 
      qed
      moreover have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node, child) \<in> (parent_child_rel h)\<^sup>*"
        using ptr_child ptr_child_ptr_child_node by auto
      ultimately have "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node \<in> set ancestors"
        using 1 by auto
      moreover have "h \<turnstile> get_parent ptr_child_node \<rightarrow>\<^sub>r Some ptr"
        using assms(1) children ptr_child_node child_parent_dual
        using known_ptrs type_wf by blast 
      ultimately show ?thesis
        using get_ancestors_also_parent assms type_wf by blast
    qed
  qed
  next
  assume 3: "ptr \<in> set ancestors"
  show "(ptr, child) \<in> (parent_child_rel h)\<^sup>*"
  proof (insert 3, induct ptr rule: heap_wellformed_induct[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        by simp
    next
      case False
      then obtain children ptr_child_node where
        children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children" and
        ptr_child_node: "ptr_child_node \<in> set children" and
        ptr_child_node_in_ancestors: "cast ptr_child_node \<in> set ancestors"
        using 1(2) assms(2) get_ancestors_obtains_children assms(1)
        using known_ptrs type_wf by blast
      then have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node, child) \<in> (parent_child_rel h)\<^sup>*"
        using 1(1) by blast
  
      moreover have "(ptr, cast ptr_child_node) \<in> parent_child_rel h"
        using children ptr_child_node assms(1) parent_child_rel_child_nodes2
        using child_parent_dual known_ptrs parent_child_rel_parent type_wf
        by blast
  
      ultimately show ?thesis
        by auto
    qed
  qed
qed

lemma get_root_node_parent_child_rel:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r root"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "(root, child) \<in> (parent_child_rel h)\<^sup>*"
  using assms get_ancestors_parent_child_rel
  apply(auto simp add: get_root_node_def elim!: bind_returns_result_E2)[1]
  using get_ancestors_never_empty last_in_set by blast


lemma get_ancestors_eq:
  assumes "heap_is_wellformed h"
    and "heap_is_wellformed h'"
    and "\<And>object_ptr w. object_ptr \<noteq> ptr \<Longrightarrow> w \<in> get_child_nodes_locs object_ptr \<Longrightarrow> w h h'"
    and pointers_preserved: "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
    and known_ptrs: "known_ptrs h"
    and known_ptrs': "known_ptrs h'"
    and "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
    and type_wf: "type_wf h"
    and type_wf': "type_wf h'"
  shows "h' \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
proof -
  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    using pointers_preserved object_ptr_kinds_preserved_small by blast
  then have object_ptr_kinds_M_eq: 
           "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_eq: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by(simp)
  have "h' \<turnstile> ok (get_ancestors ptr)"
    using get_ancestors_ok get_ancestors_ptr_in_heap object_ptr_kinds_eq3 assms(1) known_ptrs
        known_ptrs' assms(2) assms(7) type_wf'
      by blast
  then obtain ancestors' where ancestors': "h' \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors'"
    by auto

  obtain root where root: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  proof -
    assume 0: "(\<And>root. h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root \<Longrightarrow> thesis)"
    show thesis
      apply(rule 0)
      using assms(7)
      by(auto simp add: get_root_node_def elim!: bind_returns_result_E2 split: option.splits)
  qed

  have children_eq: 
   "\<And>p children. p \<noteq> ptr \<Longrightarrow> h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads assms(3)
    apply(simp add: reads_def reflp_def transp_def preserved_def)
    by blast

  have "acyclic (parent_child_rel h)"
    using assms(1) local.parent_child_rel_acyclic by auto
  have "acyclic (parent_child_rel h')"
    using assms(2) local.parent_child_rel_acyclic by blast
  have 2: "\<And>c parent_opt. cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c \<in> set ancestors \<inter> set ancestors' 
          \<Longrightarrow> h \<turnstile> get_parent c \<rightarrow>\<^sub>r parent_opt = h' \<turnstile> get_parent c \<rightarrow>\<^sub>r parent_opt"
  proof -
    fix c parent_opt
    assume 1: " cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c \<in> set ancestors \<inter> set ancestors'"

    obtain ptrs where ptrs: "h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
      by simp

    let ?P = "(\<lambda>ptr. Heap_Error_Monad.bind (get_child_nodes ptr) (\<lambda>children. return (c \<in> set children)))"
    have children_eq_True: "\<And>p. p \<in> set ptrs \<Longrightarrow> h \<turnstile> ?P p \<rightarrow>\<^sub>r True \<longleftrightarrow> h' \<turnstile> ?P p \<rightarrow>\<^sub>r True"
    proof -
      fix p
      assume "p \<in> set ptrs"
      then show "h \<turnstile> ?P p \<rightarrow>\<^sub>r True \<longleftrightarrow> h' \<turnstile> ?P p \<rightarrow>\<^sub>r True"
      proof (cases "p = ptr")
        case True
        have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c, ptr) \<in> (parent_child_rel h)\<^sup>*"
          using get_ancestors_parent_child_rel 1 assms by blast 
        then have "(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h)"
        proof (cases "cast c = ptr")
          case True
          then show ?thesis 
            using \<open>acyclic (parent_child_rel h)\<close> by(auto simp add: acyclic_def)
        next
          case False
          then have "(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h)\<^sup>*"
            using \<open>acyclic (parent_child_rel h)\<close> False rtrancl_eq_or_trancl rtrancl_trancl_trancl 
                   \<open>(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c, ptr) \<in> (parent_child_rel h)\<^sup>*\<close>
            by (metis acyclic_def)
          then show ?thesis
            using r_into_rtrancl by auto
        qed
        obtain children where children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
          using type_wf 
          by (metis \<open>h' \<turnstile> ok get_ancestors ptr\<close> assms(1) get_ancestors_ptr_in_heap get_child_nodes_ok 
                    heap_is_wellformed_def is_OK_returns_result_E known_ptrs local.known_ptrs_known_ptr 
                    object_ptr_kinds_eq3)
        then have "c \<notin> set children"
          using \<open>(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h)\<close> assms(1)
          using parent_child_rel_child_nodes2
          using child_parent_dual known_ptrs parent_child_rel_parent
          type_wf by blast
        with children have "h \<turnstile> ?P p \<rightarrow>\<^sub>r False"
          by(auto simp add: True)

        moreover have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c, ptr) \<in> (parent_child_rel h')\<^sup>*"
          using get_ancestors_parent_child_rel assms(2) ancestors' 1 known_ptrs' type_wf 
          type_wf' by blast
        then have "(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h')"
        proof (cases "cast c = ptr")
          case True
          then show ?thesis 
            using \<open>acyclic (parent_child_rel h')\<close> by(auto simp add: acyclic_def)
        next
          case False
          then have "(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h')\<^sup>*"
            using \<open>acyclic (parent_child_rel h')\<close> False rtrancl_eq_or_trancl rtrancl_trancl_trancl
                         \<open>(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c, ptr) \<in> (parent_child_rel h')\<^sup>*\<close>
            by (metis acyclic_def)
          then show ?thesis
            using r_into_rtrancl by auto
        qed
        then have "(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h')"
          using r_into_rtrancl by auto
        obtain children' where children': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
          using  type_wf  type_wf' 
          by (meson \<open>h' \<turnstile> ok (get_ancestors ptr)\<close> assms(2) get_ancestors_ptr_in_heap 
                          get_child_nodes_ok is_OK_returns_result_E known_ptrs' 
                          local.known_ptrs_known_ptr)
        then have "c \<notin> set children'"
          using \<open>(ptr, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<notin> (parent_child_rel h')\<close> assms(2)  type_wf  type_wf' 
          using parent_child_rel_child_nodes2 child_parent_dual known_ptrs' parent_child_rel_parent
          by auto
        with children' have "h' \<turnstile> ?P p \<rightarrow>\<^sub>r False"
          by(auto simp add: True)

        ultimately show ?thesis
          by (metis returns_result_eq)
      next
        case False
        then show ?thesis
          using children_eq ptrs
          by (metis (no_types, lifting) bind_pure_returns_result_I bind_returns_result_E 
                get_child_nodes_pure return_returns_result)
      qed
    qed
    have "\<And>pa. pa \<in> set ptrs \<Longrightarrow> h \<turnstile> ok (get_child_nodes pa 
                     \<bind> (\<lambda>children. return (c \<in> set children))) = h' \<turnstile> ok ( get_child_nodes pa 
                     \<bind> (\<lambda>children. return (c \<in> set children)))"
      using assms(1) assms(2) object_ptr_kinds_eq ptrs type_wf  type_wf' 
      by (metis (no_types, lifting) ObjectMonad.ptr_kinds_ptr_kinds_M bind_is_OK_pure_I 
                                    get_child_nodes_ok get_child_nodes_pure known_ptrs' 
                                    local.known_ptrs_known_ptr return_ok select_result_I2) 
    have children_eq_False: 
         "\<And>pa. pa \<in> set ptrs \<Longrightarrow> h \<turnstile> get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False = h' \<turnstile> get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
    proof
      fix pa
      assume "pa \<in> set ptrs" 
          and "h \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
      have "h \<turnstile> ok (get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children))) 
           \<Longrightarrow> h' \<turnstile> ok ( get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)))"
        using \<open>pa \<in> set ptrs\<close> \<open>\<And>pa. pa \<in> set ptrs \<Longrightarrow> h \<turnstile> ok (get_child_nodes pa 
                    \<bind> (\<lambda>children. return (c \<in> set children))) = h' \<turnstile> ok ( get_child_nodes pa 
                    \<bind> (\<lambda>children. return (c \<in> set children)))\<close> 
        by auto
      moreover have "h \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False 
        \<Longrightarrow> h' \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
        by (metis (mono_tags, lifting) \<open>\<And>pa. pa \<in> set ptrs 
              \<Longrightarrow> h \<turnstile> get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r True = h' \<turnstile> get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r True\<close> \<open>pa \<in> set ptrs\<close> 
                calculation is_OK_returns_result_I returns_result_eq returns_result_select_result)
      ultimately show "h' \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
        using \<open>h \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False\<close>
        by auto
    next
      fix pa
      assume "pa \<in> set ptrs" 
        and "h' \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
      have "h' \<turnstile> ok (get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children))) 
            \<Longrightarrow> h \<turnstile> ok ( get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)))"
        using \<open>pa \<in> set ptrs\<close> \<open>\<And>pa. pa \<in> set ptrs 
              \<Longrightarrow> h \<turnstile> ok (get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children))) = h' \<turnstile> ok ( get_child_nodes pa 
                  \<bind> (\<lambda>children. return (c \<in> set children)))\<close> 
        by auto
      moreover have "h' \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False 
                  \<Longrightarrow> h \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
        by (metis (mono_tags, lifting) 
             \<open>\<And>pa. pa \<in> set ptrs \<Longrightarrow> h \<turnstile> get_child_nodes pa 
                        \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r True = h' \<turnstile> get_child_nodes pa 
                        \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r True\<close> \<open>pa \<in> set ptrs\<close> 
               calculation is_OK_returns_result_I returns_result_eq returns_result_select_result)
      ultimately show "h \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False"
        using \<open>h' \<turnstile> get_child_nodes pa \<bind> (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r False\<close> by blast
    qed

    have filter_eq: "\<And>xs. h \<turnstile> filter_M ?P ptrs \<rightarrow>\<^sub>r xs = h' \<turnstile> filter_M ?P ptrs \<rightarrow>\<^sub>r xs"
    proof (rule filter_M_eq)
      show 
      "\<And>xs x. pure (Heap_Error_Monad.bind (get_child_nodes x) (\<lambda>children. return (c \<in> set children))) h"
        by(auto intro!: bind_pure_I)
    next
      show 
      "\<And>xs x. pure (Heap_Error_Monad.bind (get_child_nodes x) (\<lambda>children. return (c \<in> set children))) h'"
        by(auto intro!: bind_pure_I)
    next
      fix xs b x
      assume 0: "x \<in> set ptrs"
      then show "h \<turnstile> Heap_Error_Monad.bind (get_child_nodes x) (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r b 
              = h' \<turnstile> Heap_Error_Monad.bind (get_child_nodes x) (\<lambda>children. return (c \<in> set children)) \<rightarrow>\<^sub>r b"
        apply(induct b)
        using children_eq_True apply blast
        using children_eq_False apply blast
        done
    qed

    show "h \<turnstile> get_parent c \<rightarrow>\<^sub>r parent_opt = h' \<turnstile> get_parent c \<rightarrow>\<^sub>r parent_opt"
      apply(simp add: get_parent_def)
      apply(rule bind_cong_2)
         apply(simp)
        apply(simp)
       apply(simp add: check_in_heap_def node_ptr_kinds_def object_ptr_kinds_eq3)
      apply(rule bind_cong_2)
         apply(auto simp add: object_ptr_kinds_M_eq object_ptr_kinds_eq3)[1]
        apply(auto simp add: object_ptr_kinds_M_eq object_ptr_kinds_eq3)[1]
       apply(auto simp add: object_ptr_kinds_M_eq object_ptr_kinds_eq3)[1]
      apply(rule bind_cong_2)
         apply(auto intro!: filter_M_pure_I bind_pure_I)[1]
        apply(auto intro!: filter_M_pure_I bind_pure_I)[1]
       apply(auto simp add: filter_eq (* dest!: returns_result_eq[OF ptrs] *))
      using filter_eq ptrs apply auto[1]
      using filter_eq ptrs by auto
  qed

  have "ancestors = ancestors'"
  proof(insert assms(1) assms(7) ancestors' 2, induct ptr arbitrary: ancestors ancestors' 
               rule: heap_wellformed_induct_rev)
    case (step child)
    show ?case
      using step(2) step(3) step(4)
      apply(simp add: get_ancestors_def)
      apply(auto intro!: elim!: bind_returns_result_E2 split: option.splits)[1]
      using returns_result_eq apply fastforce
      apply (meson option.simps(3) returns_result_eq)
      by (metis IntD1 IntD2 option.inject returns_result_eq step.hyps)
  qed
  then show ?thesis
    using assms(5) ancestors'
    by simp
qed

lemma get_ancestors_remains_not_in_ancestors:
  assumes "heap_is_wellformed h"
    and "heap_is_wellformed h'"
    and "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
    and "h' \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors'"
    and "\<And>p children children'. h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children 
        \<Longrightarrow> h' \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children' \<Longrightarrow> set children' \<subseteq> set children"
    and "node \<notin> set ancestors"
    and object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
    and type_wf': "type_wf h'"
  shows "node \<notin> set ancestors'"
proof -
  have object_ptr_kinds_M_eq: 
    "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    using object_ptr_kinds_eq3
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_eq: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by(simp)

  show ?thesis
  proof (insert assms(1) assms(3) assms(4) assms(6), induct ptr arbitrary: ancestors ancestors' 
        rule: heap_wellformed_induct_rev)
    case (step child)
    have 1: "\<And>p parent. h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent \<Longrightarrow> h \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
    proof -
      fix p parent
      assume "h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
      then obtain children' where
        children': "h' \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children'" and
        p_in_children': "p \<in> set children'"
        using get_parent_child_dual by blast
      obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
        using get_child_nodes_ok assms(1) get_child_nodes_ptr_in_heap object_ptr_kinds_eq children' 
              known_ptrs
        using  type_wf type_wf'
        by (metis \<open>h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent\<close> get_parent_parent_in_heap is_OK_returns_result_E 
                  local.known_ptrs_known_ptr object_ptr_kinds_eq3)
      have "p \<in> set children"
        using assms(5) children children' p_in_children'
        by blast
      then show "h \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
        using child_parent_dual assms(1) children known_ptrs  type_wf  by blast
    qed
    have "node \<noteq> child"
      using assms(1) get_ancestors_parent_child_rel step.prems(1) step.prems(3) known_ptrs 
      using type_wf type_wf'
      by blast
    then show ?case
      using step(2) step(3)
      apply(simp add: get_ancestors_def)
      using step(4) 
      apply(auto elim!: bind_returns_result_E2 split: option.splits)[1]
      using 1
       apply (meson option.distinct(1) returns_result_eq)
      by (metis "1" option.inject returns_result_eq step.hyps)
  qed
qed

lemma get_ancestors_ptrs_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
  assumes "ptr' \<in> set ancestors"
  shows "ptr' |\<in>| object_ptr_kinds h"
proof (insert assms(4) assms(5), induct ancestors arbitrary: ptr)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons a ancestors)
  then obtain x where x: "h \<turnstile> get_ancestors x \<rightarrow>\<^sub>r a # ancestors"
    by(auto simp add: get_ancestors_def[of a] elim!: bind_returns_result_E2 split: option.splits)
  then have "x = a"
    by(auto simp add: get_ancestors_def[of x] elim!: bind_returns_result_E2 split: option.splits)
  then show ?case
    using Cons.hyps Cons.prems(2) get_ancestors_ptr_in_heap x
    by (metis assms(1) assms(2) assms(3) get_ancestors_obtains_children get_child_nodes_ptr_in_heap 
              is_OK_returns_result_I)
qed


lemma get_ancestors_prefix:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
  assumes "ptr' \<in> set ancestors"
  assumes "h \<turnstile> get_ancestors ptr' \<rightarrow>\<^sub>r ancestors'"
  shows "\<exists>pre. ancestors = pre @ ancestors'"
proof (insert assms(1) assms(5) assms(6), induct ptr' arbitrary: ancestors' 
       rule: heap_wellformed_induct)
  case (step parent)
  then show ?case
  proof (cases "parent \<noteq> ptr" )
    case True

    then obtain children ancestor_child where "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children" 
          and "ancestor_child \<in> set children" and "cast ancestor_child \<in> set ancestors"
    using assms(1) assms(2) assms(3) assms(4) get_ancestors_obtains_children step.prems(1) by blast
  then have "h \<turnstile> get_parent ancestor_child \<rightarrow>\<^sub>r Some parent"
    using assms(1) assms(2) assms(3) child_parent_dual by blast
  then have "h \<turnstile> get_ancestors (cast ancestor_child) \<rightarrow>\<^sub>r cast ancestor_child # ancestors'"
    apply(simp add: get_ancestors_def)
    using \<open>h \<turnstile> get_ancestors parent \<rightarrow>\<^sub>r ancestors'\<close> get_parent_ptr_in_heap
    by(auto simp add: check_in_heap_def is_OK_returns_result_I intro!: bind_pure_returns_result_I)
  then show ?thesis 
    using step(1) \<open>h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children\<close> \<open>ancestor_child \<in> set children\<close> 
      \<open>cast ancestor_child \<in> set ancestors\<close> \<open>h \<turnstile> get_ancestors (cast ancestor_child) \<rightarrow>\<^sub>r cast ancestor_child # ancestors'\<close>
    by fastforce
  next
    case False
    then show ?thesis
      by (metis append_Nil assms(4) returns_result_eq step.prems(2))
  qed
qed


lemma get_ancestors_same_root_node:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors"
  assumes "ptr' \<in> set ancestors"
  assumes "ptr'' \<in> set ancestors"
  shows "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr \<longleftrightarrow> h \<turnstile> get_root_node ptr'' \<rightarrow>\<^sub>r root_ptr"
proof -
  have "ptr' |\<in>| object_ptr_kinds h"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) get_ancestors_obtains_children 
              get_ancestors_ptr_in_heap get_child_nodes_ptr_in_heap is_OK_returns_result_I)
  then obtain ancestors' where ancestors': "h \<turnstile> get_ancestors ptr' \<rightarrow>\<^sub>r ancestors'"
    by (meson assms(1) assms(2) assms(3) get_ancestors_ok is_OK_returns_result_E)
  then have "\<exists>pre. ancestors = pre @ ancestors'"
    using get_ancestors_prefix assms by blast
  moreover have "ptr'' |\<in>| object_ptr_kinds h"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(6) get_ancestors_obtains_children 
              get_ancestors_ptr_in_heap get_child_nodes_ptr_in_heap is_OK_returns_result_I)
  then obtain ancestors'' where ancestors'': "h \<turnstile> get_ancestors ptr'' \<rightarrow>\<^sub>r ancestors''"
    by (meson assms(1) assms(2) assms(3) get_ancestors_ok is_OK_returns_result_E)
  then have "\<exists>pre. ancestors = pre @ ancestors''"
    using get_ancestors_prefix assms by blast
  ultimately show ?thesis
    using ancestors' ancestors''
    apply(auto simp add: get_root_node_def elim!: bind_returns_result_E2 
        intro!: bind_pure_returns_result_I)[1]
     apply (metis (no_types, lifting) assms(1) get_ancestors_never_empty last_appendR 
                                      returns_result_eq)
    by (metis assms(1) get_ancestors_never_empty last_appendR returns_result_eq)
qed

lemma get_root_node_parent_same:
  assumes "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr"
  shows "h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root \<longleftrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
proof
  assume 1: " h \<turnstile> get_root_node (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r root"
  show "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
    using 1[unfolded get_root_node_def] assms
    apply(simp add: get_ancestors_def)
    apply(auto simp add: get_root_node_def dest: returns_result_eq elim!: bind_returns_result_E2 
        intro!: bind_pure_returns_result_I split: option.splits)[1]
    using returns_result_eq apply fastforce
    using get_ancestors_ptr by fastforce
next
  assume 1: " h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  show "h \<turnstile> get_root_node (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r root"
    apply(simp add: get_root_node_def)
    using assms 1
    apply(simp add: get_ancestors_def)
    apply(auto simp add: get_root_node_def dest: returns_result_eq elim!: bind_returns_result_E2 
               intro!: bind_pure_returns_result_I split: option.splits)[1]
     apply (simp add: check_in_heap_def is_OK_returns_result_I)
    using get_ancestors_ptr get_parent_ptr_in_heap
    apply (simp add: is_OK_returns_result_I)
    by (meson list.distinct(1) list.set_cases local.get_ancestors_ptr)
qed

lemma get_root_node_same_no_parent:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r cast child"
  shows "h \<turnstile> get_parent child \<rightarrow>\<^sub>r None"
proof (insert assms(1) assms(4), induct ptr rule: heap_wellformed_induct_rev)
  case (step c)
  then show ?case
  proof (cases "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r c")
    case None
    then have "c = cast child"
      using step(2)
      by(auto simp add: get_root_node_def get_ancestors_def[of c] elim!: bind_returns_result_E2)
    then show ?thesis
      using None by auto
  next
    case (Some child_node)
    note s = this
    then obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      by (metis (no_types, lifting) assms(2) assms(3) get_root_node_ptr_in_heap 
                is_OK_returns_result_I local.get_parent_ok node_ptr_casts_commute 
                node_ptr_kinds_commutes returns_result_select_result step.prems)
    then show ?thesis
    proof(induct parent_opt)
      case None
      then show ?case
        using Some get_root_node_no_parent returns_result_eq step.prems by fastforce
    next
      case (Some parent)
      then show ?case
        using step s
        apply(auto simp add: get_root_node_def get_ancestors_def[of c] 
                   elim!: bind_returns_result_E2 split: option.splits list.splits)[1]
        using get_root_node_parent_same step.hyps step.prems by auto
    qed
  qed
qed

lemma get_root_node_not_node_same:
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "\<not>is_node_ptr_kind ptr"
  shows "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r ptr"
  using assms
  apply(simp add: get_root_node_def get_ancestors_def)
  by(auto simp add: get_root_node_def dest: returns_result_eq elim!: bind_returns_result_E2 
          intro!: bind_pure_returns_result_I split: option.splits)


lemma get_root_node_root_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  shows "root |\<in>| object_ptr_kinds h"
  using assms
  apply(auto simp add: get_root_node_def elim!: bind_returns_result_E2)[1]
  by (simp add: get_ancestors_never_empty get_ancestors_ptrs_in_heap)


lemma get_root_node_same_no_parent_parent_child_rel:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r ptr'"
  shows "\<not>(\<exists>p. (p, ptr') \<in> (parent_child_rel h))"
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) get_root_node_same_no_parent 
            l_heap_is_wellformed.parent_child_rel_child local.child_parent_dual local.get_child_nodes_ok 
            local.known_ptrs_known_ptr local.l_heap_is_wellformed_axioms local.parent_child_rel_node_ptr
            local.parent_child_rel_parent_in_heap node_ptr_casts_commute3 option.simps(3) returns_result_eq 
            returns_result_select_result)

end


locale l_get_ancestors_wf = l_heap_is_wellformed_defs + l_known_ptrs + l_type_wf + l_get_ancestors_defs 
                          + l_get_child_nodes_defs + l_get_parent_defs +
  assumes get_ancestors_never_empty:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_ancestors child \<rightarrow>\<^sub>r ancestors \<Longrightarrow> ancestors \<noteq> []"
  assumes get_ancestors_ok:
    "heap_is_wellformed h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h 
                          \<Longrightarrow> h \<turnstile> ok (get_ancestors ptr)"
  assumes get_ancestors_reads:
    "heap_is_wellformed h \<Longrightarrow> reads get_ancestors_locs (get_ancestors node_ptr) h h'"
  assumes get_ancestors_ptrs_in_heap: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors \<Longrightarrow> ptr' \<in> set ancestors 
                          \<Longrightarrow> ptr' |\<in>| object_ptr_kinds h"
  assumes get_ancestors_remains_not_in_ancestors:
    "heap_is_wellformed h \<Longrightarrow> heap_is_wellformed h' \<Longrightarrow> h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors 
                          \<Longrightarrow> h' \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors' 
                          \<Longrightarrow> (\<And>p children children'. h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children 
                               \<Longrightarrow> h' \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children' 
                               \<Longrightarrow> set children' \<subseteq> set children) 
                          \<Longrightarrow> node \<notin> set ancestors 
                          \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h' \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> type_wf h \<Longrightarrow> type_wf h' \<Longrightarrow> node \<notin> set ancestors'"
  assumes get_ancestors_also_parent:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_ancestors some_ptr \<rightarrow>\<^sub>r ancestors 
                          \<Longrightarrow> cast child_node \<in> set ancestors 
                          \<Longrightarrow> h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> type_wf h 
                          \<Longrightarrow> known_ptrs h \<Longrightarrow> parent \<in> set ancestors"
  assumes get_ancestors_obtains_children:
    "heap_is_wellformed h \<Longrightarrow> ancestor \<noteq> ptr \<Longrightarrow> ancestor \<in> set ancestors 
                          \<Longrightarrow> h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> (\<And>children ancestor_child . h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children 
                               \<Longrightarrow> ancestor_child \<in> set children 
                               \<Longrightarrow> cast ancestor_child \<in> set ancestors 
                               \<Longrightarrow> thesis) 
                          \<Longrightarrow> thesis"
  assumes get_ancestors_parent_child_rel:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_ancestors child \<rightarrow>\<^sub>r ancestors \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h 
                          \<Longrightarrow> (ptr, child) \<in> (parent_child_rel h)\<^sup>* \<longleftrightarrow> ptr \<in> set ancestors"

locale l_get_root_node_wf = l_heap_is_wellformed_defs + l_get_root_node_defs + l_type_wf 
                          + l_known_ptrs + l_get_ancestors_defs + l_get_parent_defs +
  assumes get_root_node_ok: 
    "heap_is_wellformed h \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h 
                          \<Longrightarrow> h \<turnstile> ok (get_root_node ptr)"
  assumes get_root_node_ptr_in_heap: 
    "h \<turnstile> ok (get_root_node ptr) \<Longrightarrow> ptr |\<in>| object_ptr_kinds h"
  assumes get_root_node_root_in_heap: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root \<Longrightarrow> root |\<in>| object_ptr_kinds h"
  assumes get_ancestors_same_root_node: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors \<Longrightarrow> ptr' \<in> set ancestors 
                          \<Longrightarrow> ptr'' \<in> set ancestors 
                          \<Longrightarrow> h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr \<longleftrightarrow> h \<turnstile> get_root_node ptr'' \<rightarrow>\<^sub>r root_ptr"
  assumes get_root_node_same_no_parent: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r cast child \<Longrightarrow> h \<turnstile> get_parent child \<rightarrow>\<^sub>r None"
  assumes get_root_node_not_node_same: 
    "ptr |\<in>| object_ptr_kinds h \<Longrightarrow> \<not>is_node_ptr_kind ptr 
                                \<Longrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r ptr"
  assumes get_root_node_parent_same: 
    "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some ptr 
        \<Longrightarrow> h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root \<longleftrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"

interpretation i_get_root_node_wf?:
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf known_ptrs heap_is_wellformed parent_child_rel 
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs 
  get_parent get_parent_locs get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  using instances
  by(simp add: l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_ancestors_wf_is_l_get_ancestors_wf [instances]:
  "l_get_ancestors_wf heap_is_wellformed parent_child_rel known_ptr known_ptrs type_wf get_ancestors 
  get_ancestors_locs get_child_nodes get_parent"
  using known_ptrs_is_l_known_ptrs
  apply(auto simp add: l_get_ancestors_wf_def l_get_ancestors_wf_axioms_def)[1]
  using get_ancestors_never_empty apply blast
  using get_ancestors_ok apply blast
  using get_ancestors_reads apply blast
  using get_ancestors_ptrs_in_heap apply blast
  using get_ancestors_remains_not_in_ancestors apply blast
  using get_ancestors_also_parent apply blast
  using get_ancestors_obtains_children apply blast
  using get_ancestors_parent_child_rel apply blast
  using get_ancestors_parent_child_rel apply blast
  done

lemma get_root_node_wf_is_l_get_root_node_wf [instances]:
  "l_get_root_node_wf heap_is_wellformed get_root_node type_wf known_ptr known_ptrs 
   get_ancestors get_parent"
  using known_ptrs_is_l_known_ptrs
  apply(auto simp add: l_get_root_node_wf_def l_get_root_node_wf_axioms_def)[1]
  using get_root_node_ok apply blast
  using get_root_node_ptr_in_heap apply blast
  using get_root_node_root_in_heap apply blast
  using get_ancestors_same_root_node apply(blast, blast)
  using get_root_node_same_no_parent apply blast
  using get_root_node_not_node_same apply blast
  using get_root_node_parent_same apply (blast, blast)
  done


subsection \<open>to\_tree\_order\<close>
(* lemma to_tree_order_reads:
  assumes "a_heap_is_wellformed h"
  shows "reads (all_ptrs (getter_preserved_set_ext \<union> {get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_preserved document_element} 
         \<union> {get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_preserved Element.child_nodes})) (to_tree_order ptr) h h'"
  oops *)

locale l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = 
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent +
  l_get_parent_wf +
  l_heap_is_wellformed
  (* l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M *)
begin

lemma to_tree_order_ptr_in_heap:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
  assumes "h \<turnstile> ok (to_tree_order ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
proof(insert assms(1) assms(4), induct rule: heap_wellformed_induct)
  case (step parent)
  then show ?case
    apply(auto simp add: to_tree_order_def[of parent] map_M_pure_I elim!: bind_is_OK_E3)[1]
    using get_child_nodes_ptr_in_heap by blast
qed

lemma to_tree_order_either_ptr_or_in_children:
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
    and "node \<in> set nodes"
    and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and "node \<noteq> ptr"
  obtains child child_to where "child \<in> set children" 
    and "h \<turnstile> to_tree_order (cast child) \<rightarrow>\<^sub>r child_to" and "node \<in> set child_to"
proof -
  obtain treeorders where treeorders: "h \<turnstile> map_M to_tree_order (map cast children) \<rightarrow>\<^sub>r treeorders"
    using assms
    apply(auto simp add: to_tree_order_def elim!: bind_returns_result_E)[1]
    using pure_returns_heap_eq returns_result_eq by fastforce
  then have "node \<in> set (concat treeorders)"
    using assms[simplified to_tree_order_def]
    by(auto elim!: bind_returns_result_E4 dest: pure_returns_heap_eq)
  then obtain treeorder where "treeorder \<in> set treeorders" 
       and node_in_treeorder: "node \<in> set treeorder"
    by auto
  then obtain child where "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r treeorder" 
       and  "child \<in> set children"
    using assms[simplified to_tree_order_def] treeorders
    by(auto elim!: map_M_pure_E2)
  then show ?thesis
    using node_in_treeorder returns_result_eq that by auto
qed


lemma to_tree_order_ptrs_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  assumes "ptr' \<in> set to"
  shows "ptr' |\<in>| object_ptr_kinds h"
proof(insert assms(1) assms(4) assms(5), induct ptr arbitrary: to rule: heap_wellformed_induct)
  case (step parent)
  have "parent |\<in>| object_ptr_kinds h"
    using assms(1) assms(2) assms(3) step.prems(1) to_tree_order_ptr_in_heap by blast
  then obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children" 
    by (meson assms(2) assms(3) get_child_nodes_ok is_OK_returns_result_E local.known_ptrs_known_ptr)
  then show ?case
  proof (cases "children = []")
    case True
    then have "to = [parent]"
      using step(2) children
      apply(auto simp add: to_tree_order_def[of parent] map_M_pure_I elim!: bind_returns_result_E2)[1]
      by (metis list.distinct(1) list.map_disc_iff list.set_cases map_M_pure_E2 returns_result_eq)
    then show ?thesis 
      using \<open>parent |\<in>| object_ptr_kinds h\<close> step.prems(2) by auto
  next
    case False
    note f = this
    then show ?thesis
      using children step to_tree_order_either_ptr_or_in_children
    proof (cases "ptr' = parent")
      case True
      then show ?thesis
        using \<open>parent |\<in>| object_ptr_kinds h\<close> by blast
    next
      case False
    then show ?thesis
      using children step.hyps to_tree_order_either_ptr_or_in_children
      by (metis step.prems(1) step.prems(2))
    qed
  qed
qed

lemma to_tree_order_ok:
  assumes wellformed: "heap_is_wellformed h"
    and "ptr |\<in>| object_ptr_kinds h"
    and "known_ptrs h"
    and type_wf: "type_wf h"
  shows "h \<turnstile> ok (to_tree_order ptr)"
proof(insert assms(1) assms(2), induct rule: heap_wellformed_induct)
  case (step parent)
  then show ?case
    using assms(3) type_wf
    apply(simp add: to_tree_order_def)
    apply(auto simp add: heap_is_wellformed_def intro!: map_M_ok_I bind_is_OK_pure_I map_M_pure_I)[1]
    using get_child_nodes_ok known_ptrs_known_ptr apply blast
    by (simp add: local.heap_is_wellformed_children_in_heap local.to_tree_order_def wellformed)
qed

lemma to_tree_order_child_subset:
  assumes "heap_is_wellformed h"
   and "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
   and "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
   and "node \<in> set children"
   and "h \<turnstile> to_tree_order (cast node) \<rightarrow>\<^sub>r nodes'"
 shows "set nodes' \<subseteq> set nodes"
proof
  fix x
  assume a1: "x \<in> set nodes'"
  moreover obtain treeorders 
           where treeorders: "h \<turnstile> map_M to_tree_order (map cast children) \<rightarrow>\<^sub>r treeorders"
    using assms(2) assms(3)
    apply(auto simp add: to_tree_order_def elim!: bind_returns_result_E)[1]
    using pure_returns_heap_eq returns_result_eq by fastforce
  then have "nodes' \<in> set treeorders"
    using assms(4) assms(5)
    by(auto elim!: map_M_pure_E dest: returns_result_eq)
  moreover have "set (concat treeorders) \<subseteq> set nodes"
    using treeorders assms(2) assms(3)
    by(auto simp add: to_tree_order_def elim!: bind_returns_result_E4 dest: pure_returns_heap_eq)
  ultimately show "x \<in> set nodes"
    by auto
qed

lemma to_tree_order_ptr_in_result:
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  shows "ptr \<in> set nodes"
  using assms
  apply(simp add: to_tree_order_def)
  by(auto elim!: bind_returns_result_E2 intro!: map_M_pure_I bind_pure_I)

lemma to_tree_order_subset:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
    and "node \<in> set nodes"
    and "h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes'"
    and "known_ptrs h"
    and type_wf: "type_wf h"
  shows "set nodes' \<subseteq> set nodes"
proof -
  have "\<forall>nodes. h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes \<longrightarrow> (\<forall>node. node \<in> set nodes 
       \<longrightarrow> (\<forall>nodes'. h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes' \<longrightarrow> set nodes' \<subseteq> set nodes))"
  proof(insert assms(1), induct ptr rule: heap_wellformed_induct)
    case (step parent)
    then show ?case
    proof safe
      fix nodes node nodes' x
      assume 1: "(\<And>children child.
             h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children \<Longrightarrow>
             child \<in> set children \<Longrightarrow> \<forall>nodes. h \<turnstile> to_tree_order (cast child) \<rightarrow>\<^sub>r nodes 
            \<longrightarrow> (\<forall>node. node \<in> set nodes \<longrightarrow> (\<forall>nodes'. h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes' 
                                              \<longrightarrow> set nodes' \<subseteq> set nodes)))"
        and 2: "h \<turnstile> to_tree_order parent \<rightarrow>\<^sub>r nodes"
        and 3: "node \<in> set nodes"
        and "h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes'"
        and "x \<in> set nodes'"
      have h1: "(\<And>children child nodes node nodes'.
             h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children \<Longrightarrow>
             child \<in> set children \<Longrightarrow> h \<turnstile> to_tree_order (cast child) \<rightarrow>\<^sub>r nodes 
             \<longrightarrow> (node \<in> set nodes \<longrightarrow> (h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes' \<longrightarrow> set nodes' \<subseteq> set nodes)))"
        using 1
        by blast
      obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
        using 2
        by(auto simp add: to_tree_order_def elim!: bind_returns_result_E)
      then have "set nodes' \<subseteq> set nodes"
      proof (cases "children = []")
        case True
        then show ?thesis
          by (metis "2" "3" \<open>h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes'\<close> children empty_iff list.set(1) 
                     subsetI to_tree_order_either_ptr_or_in_children)
      next
        case False
        then show ?thesis
        proof (cases "node = parent")
          case True
          then show ?thesis
            using "2" \<open>h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes'\<close> returns_result_eq by fastforce
        next
          case False
          then obtain child nodes_of_child where
            "child \<in> set children" and
            "h \<turnstile> to_tree_order (cast child) \<rightarrow>\<^sub>r nodes_of_child" and
            "node \<in> set nodes_of_child"
            using 2[simplified to_tree_order_def] 3 
                  to_tree_order_either_ptr_or_in_children[where node=node and ptr=parent] children
            apply(auto elim!: bind_returns_result_E2 intro: map_M_pure_I)[1]
            using is_OK_returns_result_E 2 a_all_ptrs_in_heap_def assms(1) heap_is_wellformed_def
            using "3" by blast
          then have "set nodes' \<subseteq> set nodes_of_child"
            using h1
            using \<open>h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes'\<close> children by blast
          moreover have "set nodes_of_child \<subseteq> set nodes"
            using "2" \<open>child \<in> set children\<close> \<open>h \<turnstile> to_tree_order (cast child) \<rightarrow>\<^sub>r nodes_of_child\<close> 
                  assms children to_tree_order_child_subset by auto
          ultimately show ?thesis
            by blast
        qed
      qed
      then show "x \<in> set nodes"
        using \<open>x \<in> set nodes'\<close> by blast
    qed
  qed
  then show ?thesis
    using assms by blast
qed

lemma to_tree_order_parent:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  assumes "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
  assumes "parent \<in> set nodes"
  shows "cast child \<in> set nodes"
proof -
  obtain nodes' where nodes': "h \<turnstile> to_tree_order parent \<rightarrow>\<^sub>r nodes'"
    using assms to_tree_order_ok get_parent_parent_in_heap
    by (meson get_parent_parent_in_heap is_OK_returns_result_E)

  then have "set nodes' \<subseteq> set nodes"
    using to_tree_order_subset assms
    by blast
  moreover obtain children where
    children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children" and
    child: "child \<in> set children"
    using assms get_parent_child_dual by blast
  then obtain child_to where child_to: "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r child_to"
    by (meson assms(1) assms(2) assms(3) assms(5) is_OK_returns_result_E is_OK_returns_result_I 
              get_parent_ptr_in_heap node_ptr_kinds_commutes to_tree_order_ok)
  then have "cast child \<in> set child_to"
    apply(simp add: to_tree_order_def)
    by(auto elim!: bind_returns_result_E2 map_M_pure_E 
            dest!: bind_returns_result_E3[rotated, OF children, rotated]  intro!: map_M_pure_I)
    
  have "cast child \<in> set nodes'"
    using nodes' child
    apply(simp add: to_tree_order_def)
    apply(auto elim!: bind_returns_result_E2 map_M_pure_E 
               dest!: bind_returns_result_E3[rotated, OF children, rotated]  intro!: map_M_pure_I)[1]
    using child_to \<open>cast child \<in> set child_to\<close> returns_result_eq by fastforce
  ultimately show ?thesis
    by auto
qed

lemma to_tree_order_child:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  assumes "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
  assumes "cast child \<noteq> ptr"
  assumes "child \<in> set children"
  assumes "cast child \<in> set nodes"
shows "parent \<in> set nodes"
proof(insert assms(1) assms(4) assms(6) assms(8), induct ptr arbitrary: nodes 
             rule: heap_wellformed_induct)
  case (step p)
  have "p |\<in>| object_ptr_kinds h"
    using \<open>h \<turnstile> to_tree_order p \<rightarrow>\<^sub>r nodes\<close> to_tree_order_ptr_in_heap
    using assms(1) assms(2) assms(3) by blast
  then obtain children where children: "h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children"
    by (meson assms(2) assms(3) get_child_nodes_ok is_OK_returns_result_E local.known_ptrs_known_ptr)
  then show ?case
  proof (cases "children = []")
    case True
    then show ?thesis
      using step(2) step(3) step(4) children
      by(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2  
              dest!: bind_returns_result_E3[rotated, OF children, rotated])
  next
    case False
    then obtain c child_to where
      child: "c \<in> set children" and
      child_to: "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<rightarrow>\<^sub>r child_to" and
      "cast child \<in> set child_to"
      using step(2) children 
      apply(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2 
                 dest!: bind_returns_result_E3[rotated, OF children, rotated])[1]
      by (metis (full_types) assms(1) assms(2) assms(3) get_parent_ptr_in_heap
                is_OK_returns_result_I l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.child_parent_dual 
                l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms node_ptr_kinds_commutes
                returns_result_select_result step.prems(1) step.prems(2) step.prems(3) 
                to_tree_order_either_ptr_or_in_children to_tree_order_ok)
    then have "set child_to \<subseteq> set nodes"
      using assms(1) child children step.prems(1) to_tree_order_child_subset by auto

    show ?thesis
    proof (cases "c = child")
      case True
      then have "parent = p"
        using step(3) children child assms(5) assms(7)
        by (meson assms(1) assms(2) assms(3) child_parent_dual option.inject returns_result_eq)
        
      then show ?thesis
        using step.prems(1) to_tree_order_ptr_in_result by blast
    next
      case False
      then show ?thesis 
      using step(1)[OF children child child_to] step(3) step(4)
      using \<open>set child_to \<subseteq> set nodes\<close>
      using \<open>cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child \<in> set child_to\<close> by auto
  qed
  qed
qed

lemma to_tree_order_node_ptrs:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  assumes "ptr' \<noteq> ptr"
  assumes "ptr' \<in> set nodes"
  shows "is_node_ptr_kind ptr'"
proof(insert assms(1) assms(4) assms(5) assms(6), induct ptr arbitrary: nodes 
             rule: heap_wellformed_induct)
  case (step p)
  have "p |\<in>| object_ptr_kinds h"
    using \<open>h \<turnstile> to_tree_order p \<rightarrow>\<^sub>r nodes\<close> to_tree_order_ptr_in_heap
    using assms(1) assms(2) assms(3) by blast
  then obtain children where children: "h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children"
    by (meson assms(2) assms(3) get_child_nodes_ok is_OK_returns_result_E local.known_ptrs_known_ptr)
  then show ?case
  proof (cases "children = []")
    case True
    then show ?thesis
      using step(2) step(3) step(4) children
      by(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2  
              dest!: bind_returns_result_E3[rotated, OF children, rotated])[1]
  next
    case False
    then obtain c child_to where
      child: "c \<in> set children" and
      child_to: "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<rightarrow>\<^sub>r child_to" and
      "ptr' \<in> set child_to"
      using step(2) children 
      apply(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2 
                 dest!: bind_returns_result_E3[rotated, OF children, rotated])[1]
    using step.prems(1) step.prems(2) step.prems(3) to_tree_order_either_ptr_or_in_children by blast 
    then have "set child_to \<subseteq> set nodes"
      using assms(1) child children step.prems(1) to_tree_order_child_subset by auto

    show ?thesis
    proof (cases "cast c = ptr")
      case True
      then show ?thesis
        using step \<open>ptr' \<in> set child_to\<close> assms(5) child child_to children by blast
    next
      case False
      then show ?thesis
        using \<open>ptr' \<in> set child_to\<close> child child_to children is_node_ptr_kind_cast step.hyps by blast
    qed
  qed
qed

lemma to_tree_order_child2:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  assumes "cast child \<noteq> ptr"
  assumes "cast child \<in> set nodes"
  obtains parent where "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent" and "parent \<in> set nodes"
proof -
  assume 1: "(\<And>parent. h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent \<Longrightarrow> parent \<in> set nodes \<Longrightarrow> thesis)"
  show thesis
  proof(insert assms(1) assms(4) assms(5) assms(6) 1, induct ptr arbitrary: nodes
               rule: heap_wellformed_induct)
    case (step p)
    have "p |\<in>| object_ptr_kinds h"
      using \<open>h \<turnstile> to_tree_order p \<rightarrow>\<^sub>r nodes\<close> to_tree_order_ptr_in_heap
      using assms(1) assms(2) assms(3) by blast
    then obtain children where children: "h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children"
      by (meson assms(2) assms(3) get_child_nodes_ok is_OK_returns_result_E local.known_ptrs_known_ptr)
    then show ?case
    proof (cases "children = []")
      case True
      then show ?thesis
        using step(2) step(3) step(4) children
        by(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2  
                dest!: bind_returns_result_E3[rotated, OF children, rotated])
    next
      case False
      then obtain c child_to where
        child: "c \<in> set children" and
        child_to: "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r c) \<rightarrow>\<^sub>r child_to" and
        "cast child \<in> set child_to"
        using step(2) children 
        apply(auto simp add: to_tree_order_def[of p] map_M_pure_I  elim!: bind_returns_result_E2 
                   dest!: bind_returns_result_E3[rotated, OF children, rotated])[1]
        using step.prems(1) step.prems(2) step.prems(3) to_tree_order_either_ptr_or_in_children 
        by blast
      then have "set child_to \<subseteq> set nodes"
        using assms(1) child children step.prems(1) to_tree_order_child_subset by auto

      have "cast child |\<in>| object_ptr_kinds h"
        using assms(1) assms(2) assms(3) assms(4) assms(6) to_tree_order_ptrs_in_heap by blast
      then obtain parent_opt where parent_opt: "h \<turnstile> get_parent child \<rightarrow>\<^sub>r parent_opt"
        by (meson assms(2) assms(3) is_OK_returns_result_E get_parent_ok node_ptr_kinds_commutes)
      then show ?thesis
      proof (induct parent_opt)
        case None
        then show ?case
          by (metis \<open>cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child \<in> set child_to\<close> assms(1) assms(2) assms(3) 
                        cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject child child_parent_dual child_to children
                        option.distinct(1) returns_result_eq step.hyps)
      next
        case (Some option)
        then show ?case 
          by (meson assms(1) assms(2) assms(3) get_parent_child_dual step.prems(1) step.prems(2) 
                    step.prems(3) step.prems(4) to_tree_order_child)
      qed
    qed
  qed
qed

lemma to_tree_order_parent_child_rel:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  shows "(ptr, child) \<in> (parent_child_rel h)\<^sup>* \<longleftrightarrow> child \<in> set to"
proof
  assume 3: "(ptr, child) \<in> (parent_child_rel h)\<^sup>*"
  show "child \<in> set to"
  proof (insert 3, induct child rule: heap_wellformed_induct_rev[OF assms(1)])
    case (1 child)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        using assms(4)
        apply(simp add: to_tree_order_def)
        by(auto simp add: map_M_pure_I elim!: bind_returns_result_E2)
    next
      case False
      obtain child_parent where
        "(ptr, child_parent) \<in> (parent_child_rel h)\<^sup>*" and
        "(child_parent, child) \<in> (parent_child_rel h)"
        using \<open>ptr \<noteq> child\<close>
        by (metis "1.prems" rtranclE)
      obtain child_node where child_node: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node = child"
        using \<open>(child_parent, child) \<in> parent_child_rel h\<close> node_ptr_casts_commute3 
              parent_child_rel_node_ptr
        by blast
      then have "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some child_parent"
        using \<open>(child_parent, child) \<in> (parent_child_rel h)\<close>
        by (meson assms(1) assms(2) assms(3) is_OK_returns_result_E l_get_parent_wf.child_parent_dual 
                  l_heap_is_wellformed.parent_child_rel_child local.get_child_nodes_ok 
                  local.known_ptrs_known_ptr local.l_get_parent_wf_axioms 
                  local.l_heap_is_wellformed_axioms local.parent_child_rel_parent_in_heap)
      then show ?thesis
        using 1(1) child_node \<open>(ptr, child_parent) \<in> (parent_child_rel h)\<^sup>*\<close>
        using assms(1) assms(2) assms(3) assms(4) to_tree_order_parent by blast
    qed
  qed
next
  assume "child \<in> set to"
  then show "(ptr, child) \<in> (parent_child_rel h)\<^sup>*"
  proof (induct child rule: heap_wellformed_induct_rev[OF assms(1)])
    case (1 child)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        by simp
    next
      case False
      then have "\<exists>parent. (parent, child) \<in> (parent_child_rel h)"
        using 1(2) assms(4) to_tree_order_child2[OF assms(1) assms(2) assms(3) assms(4)] 
              to_tree_order_node_ptrs
        by (metis assms(1) assms(2) assms(3) node_ptr_casts_commute3 parent_child_rel_parent)
      then obtain child_node where child_node: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node = child"
        using node_ptr_casts_commute3 parent_child_rel_node_ptr by blast
      then obtain child_parent where child_parent: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some child_parent"
        using \<open>\<exists>parent. (parent, child) \<in> (parent_child_rel h)\<close>
        by (metis "1.prems" False assms(1) assms(2) assms(3) assms(4) to_tree_order_child2)
      then have "(child_parent, child) \<in> (parent_child_rel h)"
        using assms(1) child_node parent_child_rel_parent by blast
      moreover have "child_parent \<in> set to"
        by (metis "1.prems" False assms(1) assms(2) assms(3) assms(4) child_node child_parent 
                  get_parent_child_dual to_tree_order_child)
      then have "(ptr, child_parent) \<in> (parent_child_rel h)\<^sup>*"
        using 1 child_node child_parent by blast
      ultimately show ?thesis
        by auto
    qed
  qed
qed
end

interpretation i_to_tree_order_wf?: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes 
                                    get_child_nodes_locs to_tree_order known_ptrs get_parent 
                                    get_parent_locs heap_is_wellformed parent_child_rel 
                                    get_disconnected_nodes get_disconnected_nodes_locs
  using instances
  apply(simp add: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
  done
declare l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_to_tree_order_wf = l_heap_is_wellformed_defs + l_type_wf + l_known_ptrs 
                            + l_to_tree_order_defs 
                            + l_get_parent_defs + l_get_child_nodes_defs +
  assumes to_tree_order_ok: 
    "heap_is_wellformed h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h 
                          \<Longrightarrow> h \<turnstile> ok (to_tree_order ptr)"
  assumes to_tree_order_ptrs_in_heap: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to 
                          \<Longrightarrow> ptr' \<in> set to \<Longrightarrow> ptr' |\<in>| object_ptr_kinds h"
  assumes to_tree_order_parent_child_rel:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to 
                          \<Longrightarrow> (ptr, child_ptr) \<in> (parent_child_rel h)\<^sup>* \<longleftrightarrow> child_ptr \<in> set to"
  assumes to_tree_order_child2: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes 
                          \<Longrightarrow> cast child \<noteq> ptr \<Longrightarrow> cast child \<in> set nodes 
                          \<Longrightarrow> (\<And>parent. h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent  
                                         \<Longrightarrow> parent \<in> set nodes \<Longrightarrow> thesis) 
                          \<Longrightarrow> thesis"
  assumes to_tree_order_node_ptrs: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes
                          \<Longrightarrow> ptr' \<noteq> ptr \<Longrightarrow> ptr' \<in> set nodes \<Longrightarrow> is_node_ptr_kind ptr'"
  assumes to_tree_order_child: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes 
                          \<Longrightarrow> h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children \<Longrightarrow> cast child \<noteq> ptr 
                          \<Longrightarrow> child \<in> set children \<Longrightarrow> cast child \<in> set nodes 
                          \<Longrightarrow> parent \<in> set nodes"
  assumes to_tree_order_ptr_in_result: 
    "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes \<Longrightarrow> ptr \<in> set nodes"
  assumes to_tree_order_parent: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes 
                          \<Longrightarrow> h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent \<Longrightarrow> parent \<in> set nodes 
                          \<Longrightarrow> cast child \<in> set nodes"
  assumes to_tree_order_subset:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes \<Longrightarrow> node \<in> set nodes 
                          \<Longrightarrow> h \<turnstile> to_tree_order node \<rightarrow>\<^sub>r nodes' \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> type_wf h \<Longrightarrow> set nodes' \<subseteq> set nodes"

lemma to_tree_order_wf_is_l_to_tree_order_wf [instances]: 
  "l_to_tree_order_wf heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs 
                      to_tree_order get_parent get_child_nodes"
  using instances
  apply(auto simp add: l_to_tree_order_wf_def l_to_tree_order_wf_axioms_def)[1]
  using to_tree_order_ok 
           apply blast
  using to_tree_order_ptrs_in_heap 
          apply blast
  using to_tree_order_parent_child_rel
         apply(blast, blast)
  using to_tree_order_child2
       apply blast
  using to_tree_order_node_ptrs
      apply blast
  using to_tree_order_child 
     apply blast
  using to_tree_order_ptr_in_result
    apply blast
  using to_tree_order_parent
   apply blast
  using to_tree_order_subset
  apply blast
  done


subsubsection \<open>get\_root\_node\<close>

locale l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_ancestors
  + l_get_ancestors_wf
  + l_get_root_node
  + l_get_root_node_wf
  + l_to_tree_order_wf
  + l_get_parent
  + l_get_parent_wf
begin
lemma to_tree_order_get_root_node:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  assumes "ptr' \<in> set to"
  assumes "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
  assumes "ptr'' \<in> set to"
  shows "h \<turnstile> get_root_node ptr'' \<rightarrow>\<^sub>r root_ptr"
proof -
  obtain ancestors' where ancestors': "h \<turnstile> get_ancestors ptr' \<rightarrow>\<^sub>r ancestors'"
    by (meson assms(1) assms(2) assms(3) assms(4) assms(5) get_ancestors_ok is_OK_returns_result_E 
              to_tree_order_ptrs_in_heap )
  moreover have "ptr \<in> set ancestors'"
    using \<open>h \<turnstile> get_ancestors ptr' \<rightarrow>\<^sub>r ancestors'\<close>
    using assms(1) assms(2) assms(3) assms(4) assms(5) get_ancestors_parent_child_rel 
          to_tree_order_parent_child_rel by blast

  ultimately have "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    using \<open>h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr\<close>
    using assms(1) assms(2) assms(3) get_ancestors_ptr get_ancestors_same_root_node by blast
  
  obtain ancestors'' where ancestors'': "h \<turnstile> get_ancestors ptr'' \<rightarrow>\<^sub>r ancestors''"
    by (meson assms(1) assms(2) assms(3) assms(4) assms(7) get_ancestors_ok is_OK_returns_result_E 
              to_tree_order_ptrs_in_heap)
  moreover have "ptr \<in> set ancestors''"
    using \<open>h \<turnstile> get_ancestors ptr'' \<rightarrow>\<^sub>r ancestors''\<close>
    using assms(1) assms(2) assms(3) assms(4) assms(7) get_ancestors_parent_child_rel 
          to_tree_order_parent_child_rel by blast
  ultimately show ?thesis
    using \<open>h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr\<close> assms(1) assms(2) assms(3) get_ancestors_ptr 
          get_ancestors_same_root_node by blast
qed

lemma to_tree_order_same_root:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
  assumes "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r to"
  assumes "ptr' \<in> set to"
  shows "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
proof (insert assms(1)(*  assms(4) assms(5) *) assms(6), induct ptr' rule: heap_wellformed_induct_rev)
  case (step child)
  then show ?case
  proof (cases "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r child")
    case True
    then have "child = root_ptr"
      using  assms(1) assms(2) assms(3) assms(5) step.prems
      by (metis (no_types, lifting) get_root_node_same_no_parent node_ptr_casts_commute3 
                option.simps(3) returns_result_eq to_tree_order_child2 to_tree_order_node_ptrs)
    then show ?thesis
      using True by blast
  next
    case False
    then obtain child_node parent where "cast child_node = child" 
                  and "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent"
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) local.get_root_node_no_parent 
                local.get_root_node_not_node_same local.get_root_node_same_no_parent 
                local.to_tree_order_child2 local.to_tree_order_ptrs_in_heap node_ptr_casts_commute3  
                step.prems)
    then show ?thesis
    proof (cases "child = root_ptr")
      case True
      then have "h \<turnstile> get_root_node root_ptr \<rightarrow>\<^sub>r root_ptr"
        using assms(4)
        using \<open>cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node = child\<close> assms(1) assms(2) assms(3) 
              get_root_node_no_parent get_root_node_same_no_parent
        by blast
      then show ?thesis
        using step assms(4)
        using True by blast
    next
      case False
      then have "parent \<in> set to"
        using assms(5) step(2) to_tree_order_child \<open>h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent\<close> 
              \<open>cast child_node = child\<close>
        by (metis False assms(1) assms(2) assms(3) get_parent_child_dual)
      then show ?thesis
        using \<open>cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node = child\<close> \<open>h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent\<close> 
              get_root_node_parent_same 
        using step.hyps by blast
    qed
   
  qed
qed
end

interpretation i_to_tree_order_wf_get_root_node_wf?: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M 
               get_ancestors get_ancestors_locs heap_is_wellformed parent_child_rel known_ptr 
               known_ptrs type_wf get_child_nodes get_child_nodes_locs get_parent get_parent_locs 
               get_root_node get_root_node_locs to_tree_order
  using instances
  by(simp add: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)

locale l_to_tree_order_wf_get_root_node_wf = l_type_wf + l_known_ptrs + l_to_tree_order_defs 
                                           + l_get_root_node_defs + l_heap_is_wellformed_defs +
  assumes to_tree_order_get_root_node: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to 
                          \<Longrightarrow> ptr' \<in> set to \<Longrightarrow> h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr 
                          \<Longrightarrow> ptr'' \<in> set to \<Longrightarrow> h \<turnstile> get_root_node ptr'' \<rightarrow>\<^sub>r root_ptr"
  assumes to_tree_order_same_root: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr 
                          \<Longrightarrow> h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r to \<Longrightarrow> ptr' \<in> set to 
                          \<Longrightarrow> h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"

lemma to_tree_order_wf_get_root_node_wf_is_l_to_tree_order_wf_get_root_node_wf [instances]:
  "l_to_tree_order_wf_get_root_node_wf type_wf known_ptr known_ptrs to_tree_order 
                                       get_root_node heap_is_wellformed"
  using instances
  apply(auto simp add: l_to_tree_order_wf_get_root_node_wf_def 
      l_to_tree_order_wf_get_root_node_wf_axioms_def)[1]
  using to_tree_order_get_root_node apply blast
  using to_tree_order_same_root apply blast
  done


subsection \<open>get\_owner\_document\<close>
                                                                                                                                          
locale l_get_owner_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_known_ptrs
  + l_heap_is_wellformed
  + l_get_root_node
  + l_get_ancestors
  + l_get_ancestors_wf
  + l_get_parent
  + l_get_parent_wf
  + l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_owner_document_disconnected_nodes:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assumes "node_ptr \<in> set disc_nodes"
  assumes known_ptrs: "known_ptrs h"
  assumes type_wf: "type_wf h"
  shows "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r document_ptr"
proof -
  have 2: "node_ptr |\<in>| node_ptr_kinds h"
    using assms heap_is_wellformed_disc_nodes_in_heap
    by blast
  have 3: "document_ptr |\<in>| document_ptr_kinds h"
    using assms(2) get_disconnected_nodes_ptr_in_heap by blast
  have 0: 
  "\<exists>!document_ptr\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r. node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    by (metis (no_types, lifting) "3" DocumentMonad.ptr_kinds_ptr_kinds_M assms(1) assms(2) assms(3) 
              disjoint_iff_not_equal l_heap_is_wellformed.heap_is_wellformed_one_disc_parent 
              local.get_disconnected_nodes_ok local.l_heap_is_wellformed_axioms 
              returns_result_select_result select_result_I2 type_wf)

  have "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
    using heap_is_wellformed_children_disc_nodes_different child_parent_dual assms
    using "2" disjoint_iff_not_equal local.get_parent_child_dual local.get_parent_ok 
          returns_result_select_result split_option_ex
    by (metis (no_types, lifting))

  then have 4: "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
    using 2 get_root_node_no_parent
    by blast
  obtain document_ptrs where document_ptrs: "h \<turnstile> document_ptr_kinds_M \<rightarrow>\<^sub>r document_ptrs"
    by simp
  
  then
  have "h \<turnstile> ok (filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs)"
    using assms(1) get_disconnected_nodes_ok  type_wf unfolding heap_is_wellformed_def
    by(auto intro!: bind_is_OK_I2 filter_M_is_OK_I bind_pure_I)
  then obtain candidates where 
    candidates: "h \<turnstile> filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs \<rightarrow>\<^sub>r candidates"
    by auto


  have eq: "\<And>document_ptr. document_ptr |\<in>| document_ptr_kinds h 
           \<Longrightarrow> node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r \<longleftrightarrow> |h \<turnstile> do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }|\<^sub>r"
    apply(auto dest!: get_disconnected_nodes_ok[OF type_wf] 
               intro!: select_result_I[where P=id, simplified] elim!: bind_returns_result_E2)[1]
    apply(drule select_result_E[where P=id, simplified])
    by(auto elim!: bind_returns_result_E2)

  have filter: "filter (\<lambda>document_ptr. |h \<turnstile> do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr \<in> cast ` set disconnected_nodes)
        }|\<^sub>r) document_ptrs = [document_ptr]"
    apply(rule filter_ex1)
    using 0 document_ptrs apply(simp)[1]
    using eq
    using local.get_disconnected_nodes_ok apply auto[1]
    using assms(2) assms(3)
      apply(auto intro!: intro!: select_result_I[where P=id, simplified] 
                 elim!: bind_returns_result_E2)[1]
    using returns_result_eq apply fastforce
    using document_ptrs  3 apply(simp)
    using document_ptrs
    by simp
  have "h \<turnstile> filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs \<rightarrow>\<^sub>r [document_ptr]"
    apply(rule filter_M_filter2)
    using get_disconnected_nodes_ok document_ptrs 3  assms(1)  type_wf filter 
    unfolding heap_is_wellformed_def
    by(auto intro: bind_pure_I bind_is_OK_I2)

  with 4 document_ptrs have "h \<turnstile> a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r document_ptr"
    by(auto simp add: a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
            intro!:  bind_pure_returns_result_I filter_M_pure_I bind_pure_I 
            split: option.splits)[1]
  moreover have "known_ptr (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)"
    using "4" assms(1)  known_ptrs type_wf known_ptrs_known_ptr "2" node_ptr_kinds_commutes by blast
  ultimately show ?thesis
    using 2
    apply(auto simp add: known_ptr_impl get_owner_document_def a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, (rule conjI | rule impI)+)+
    apply(drule(1) known_ptr_not_document_ptr[folded known_ptr_impl])
    apply(drule(1)  known_ptr_not_character_data_ptr)
       apply(drule(1)  known_ptr_not_element_ptr)
       apply(simp add: NodeClass.known_ptr_defs)
    by(auto split: option.splits intro!: bind_pure_returns_result_I)
qed

lemma in_disconnected_nodes_no_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
    and "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r owner_document"
    and "h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "node_ptr \<in> set disc_nodes"
proof -
  have 2: "cast node_ptr |\<in>| object_ptr_kinds h"
    using assms(3) get_owner_document_ptr_in_heap by fast
  then have 3: "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
    using assms(2) local.get_root_node_no_parent by blast

  have "\<not>(\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
    apply(auto)[1]
    using assms(2) child_parent_dual[OF assms(1)] type_wf
          assms(1) assms(5) get_child_nodes_ok known_ptrs_known_ptr option.simps(3) 
          returns_result_eq returns_result_select_result
    by (metis (no_types, hide_lams))
  moreover have "node_ptr |\<in>| node_ptr_kinds h"
    using assms(2) get_parent_ptr_in_heap by blast
  thm heap_is_wellformed_children_disc_nodes_different
  ultimately 
  have 0: "\<exists>document_ptr\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r. node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    by (metis DocumentMonad.ptr_kinds_ptr_kinds_M assms(1) finite_set_in heap_is_wellformed_children_disc_nodes)
  then  obtain document_ptr where
    document_ptr: "document_ptr\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r" and
    node_ptr_in_disc_nodes: "node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    by auto
  then show ?thesis
    using get_owner_document_disconnected_nodes known_ptrs type_wf assms
    using DocumentMonad.ptr_kinds_ptr_kinds_M assms(1) assms(3) assms(4) get_disconnected_nodes_ok 
          returns_result_select_result select_result_I2
    by (metis (no_types, hide_lams) )
qed
end

locale l_get_owner_document_wf = l_heap_is_wellformed_defs + l_type_wf + l_known_ptrs 
                               + l_get_disconnected_nodes_defs + l_get_owner_document_defs 
                               + l_get_parent_defs +
  assumes get_owner_document_disconnected_nodes:
    "heap_is_wellformed h \<Longrightarrow>
     known_ptrs h \<Longrightarrow>
     type_wf h \<Longrightarrow>
     h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow>
     node_ptr \<in> set disc_nodes \<Longrightarrow>
     h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r document_ptr"
  assumes in_disconnected_nodes_no_parent:
   "heap_is_wellformed h \<Longrightarrow>
    h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None\<Longrightarrow>
    h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r owner_document \<Longrightarrow>
    h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow>
    known_ptrs h \<Longrightarrow>
    type_wf h\<Longrightarrow>
    node_ptr \<in> set disc_nodes"

interpretation i_get_owner_document_wf?:
  l_get_owner_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr known_ptrs type_wf heap_is_wellformed parent_child_rel 
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs 
  get_root_node get_root_node_locs get_parent get_parent_locs get_ancestors get_ancestors_locs 
  get_owner_document
  using known_ptrs_is_l_known_ptrs
  using heap_is_wellformed_is_l_heap_is_wellformed
  using get_root_node_is_l_get_root_node
  using get_ancestors_is_l_get_ancestors
  using get_ancestors_wf_is_l_get_ancestors_wf
  using get_parent_is_l_get_parent
  using get_ancestors_wf_is_l_get_ancestors_wf
  using get_parent_wf_is_l_get_parent_wf
  using l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
  by(simp add: l_get_owner_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)



lemma get_owner_document_wf_is_l_get_owner_document_wf [instances]:
  "l_get_owner_document_wf heap_is_wellformed type_wf known_ptr known_ptrs get_disconnected_nodes 
                           get_owner_document get_parent"
  using known_ptrs_is_l_known_ptrs
  apply(simp add: l_get_owner_document_wf_def l_get_owner_document_wf_axioms_def)
  using get_owner_document_disconnected_nodes in_disconnected_nodes_no_parent
  by fast


subsection \<open>Preserving heap-wellformedness\<close>


subsection \<open>set\_attribute\<close>

locale l_set_attribute_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_attribute\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M + 
  l_set_attribute_get_disconnected_nodes + 
  l_set_attribute_get_child_nodes
begin
lemma set_attribute_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> set_attribute element_ptr k v \<rightarrow>\<^sub>h h'"
  shows "heap_is_wellformed h'"
  thm preserves_wellformedness_writes_needed
  apply(rule preserves_wellformedness_writes_needed[OF assms set_attribute_writes])
  using  set_attribute_get_child_nodes
  apply(fast)
  using set_attribute_get_disconnected_nodes apply(fast)
  by(auto simp add: all_args_def set_attribute_locs_def)
end


subsection \<open>remove\_child\<close>

locale l_remove_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed +
  l_set_disconnected_nodes_get_child_nodes
begin
lemma remove_child_removes_parent:
  assumes wellformed: "heap_is_wellformed h"
    and remove_child: "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h2"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "h2 \<turnstile> get_parent child \<rightarrow>\<^sub>r None"
proof -
  obtain children where children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    using remove_child remove_child_def by auto
  then have "child \<in> set children"
    using remove_child remove_child_def
    by(auto elim!: bind_returns_heap_E dest: returns_result_eq split: if_splits)
  then have h1: "\<And>other_ptr other_children. other_ptr \<noteq> ptr 
                \<Longrightarrow> h \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children \<Longrightarrow> child \<notin> set other_children"
    using assms(1) known_ptrs  type_wf child_parent_dual
    by (meson child_parent_dual children option.inject returns_result_eq)

  have known_ptr: "known_ptr ptr"
    using known_ptrs
    by (meson is_OK_returns_heap_I l_known_ptrs.known_ptrs_known_ptr l_known_ptrs_axioms 
              remove_child remove_child_ptr_in_heap)

  obtain owner_document disc_nodes h' where
    owner_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r owner_document" and 
    disc_nodes: "h \<turnstile>  get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes" and
    h': "h \<turnstile>  set_disconnected_nodes owner_document (child # disc_nodes) \<rightarrow>\<^sub>h h'" and
    h2: "h' \<turnstile> set_child_nodes ptr (remove1 child children) \<rightarrow>\<^sub>h h2"
    using assms children unfolding remove_child_def
    apply(auto split: if_splits elim!: bind_returns_heap_E)[1]
    by (metis (full_types) get_child_nodes_pure get_disconnected_nodes_pure 
       get_owner_document_pure pure_returns_heap_eq returns_result_eq)

  have "object_ptr_kinds h = object_ptr_kinds h2"
    using remove_child_writes remove_child unfolding remove_child_locs_def
    apply(rule writes_small_big)
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by(auto simp add: reflp_def transp_def)
  then have "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    unfolding object_ptr_kinds_M_defs by simp

  have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", 
                           OF set_disconnected_nodes_writes h']
    using set_disconnected_nodes_types_preserved type_wf
    by(auto simp add: reflp_def transp_def)
  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", 
                           OF remove_child_writes remove_child]  unfolding remove_child_locs_def
    using set_disconnected_nodes_types_preserved set_child_nodes_types_preserved type_wf 
    apply(auto simp add: reflp_def transp_def)[1]
    by blast
  then obtain children' where children': "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'"
    using h2 set_child_nodes_get_child_nodes known_ptr
    by (metis \<open>object_ptr_kinds h = object_ptr_kinds h2\<close> children get_child_nodes_ok 
              get_child_nodes_ptr_in_heap is_OK_returns_result_E is_OK_returns_result_I)

  have "child \<notin> set children'"
    by (metis (mono_tags, lifting) \<open>type_wf h'\<close> children children' distinct_remove1_removeAll h2 
              known_ptr local.heap_is_wellformed_children_distinct 
              local.set_child_nodes_get_child_nodes member_remove remove_code(1) select_result_I2 
              wellformed)


  moreover have "\<And>other_ptr other_children. other_ptr \<noteq> ptr 
                \<Longrightarrow> h' \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children \<Longrightarrow> child \<notin> set other_children"
  proof -
    fix other_ptr other_children
    assume a1: "other_ptr \<noteq> ptr"  and a3: "h' \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children"
    have "h \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children"
      using get_child_nodes_reads set_disconnected_nodes_writes h' a3 
      apply(rule reads_writes_separate_backwards)
      using set_disconnected_nodes_get_child_nodes by fast
    show "child \<notin> set other_children"
      using \<open>h \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children\<close> a1 h1 by blast
  qed
  then have "\<And>other_ptr other_children. other_ptr \<noteq> ptr 
            \<Longrightarrow>  h2 \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children \<Longrightarrow> child \<notin> set other_children"
  proof -
    fix other_ptr other_children
    assume a1: "other_ptr \<noteq> ptr" and a3: "h2 \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children"
    have "h' \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children"
      using get_child_nodes_reads set_child_nodes_writes h2 a3
      apply(rule reads_writes_separate_backwards)
      using set_disconnected_nodes_get_child_nodes a1 set_child_nodes_get_child_nodes_different_pointers 
      by metis
    then show "child \<notin> set other_children"
      using \<open>\<And>other_ptr other_children. \<lbrakk>other_ptr \<noteq> ptr; h' \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children\<rbrakk> 
             \<Longrightarrow> child \<notin> set other_children\<close> a1 by blast
  qed
  ultimately have ha: "\<And>other_ptr other_children. h2 \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children 
                      \<Longrightarrow> child \<notin> set other_children"
    by (metis (full_types) children' returns_result_eq)
  moreover obtain ptrs where ptrs: "h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by (simp add: object_ptr_kinds_M_defs)
  moreover have "\<And>ptr. ptr \<in> set ptrs \<Longrightarrow> h2 \<turnstile> ok (get_child_nodes ptr)"
    using \<open>type_wf h2\<close> ptrs get_child_nodes_ok known_ptr
    using \<open>object_ptr_kinds h = object_ptr_kinds h2\<close> known_ptrs local.known_ptrs_known_ptr by auto 
  ultimately show "h2 \<turnstile> get_parent child \<rightarrow>\<^sub>r None"                     
    apply(auto simp add: get_parent_def intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I)[1]
  proof -
    have "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child |\<in>| object_ptr_kinds h"
      using get_owner_document_ptr_in_heap owner_document by blast
    then show "h2 \<turnstile> check_in_heap (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r ()"
      by (simp add: \<open>object_ptr_kinds h = object_ptr_kinds h2\<close> check_in_heap_def)
  next
    show "(\<And>other_ptr other_children. h2 \<turnstile> get_child_nodes other_ptr \<rightarrow>\<^sub>r other_children 
         \<Longrightarrow> child \<notin> set other_children) \<Longrightarrow>
    ptrs = sorted_list_of_set (fset (object_ptr_kinds h2)) \<Longrightarrow>
    (\<And>ptr. ptr |\<in>| object_ptr_kinds h2 \<Longrightarrow> h2 \<turnstile> ok get_child_nodes ptr) \<Longrightarrow>
    h2 \<turnstile> filter_M (\<lambda>ptr. Heap_Error_Monad.bind (get_child_nodes ptr) 
       (\<lambda>children. return (child \<in> set children))) (sorted_list_of_set (fset (object_ptr_kinds h2))) \<rightarrow>\<^sub>r []"
      by(auto intro!: filter_M_empty_I bind_pure_I)
  qed
qed
end

locale l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_remove_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma remove_child_parent_child_rel_subset:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
    and "known_ptrs h"
    and type_wf: "type_wf h"
  shows "parent_child_rel h' \<subseteq> parent_child_rel h"
proof (standard, safe)

  obtain owner_document children_h h2 disconnected_nodes_h where
    owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document" and
    children_h: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h" and 
    child_in_children_h: "child \<in> set children_h" and
    disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
    h2: "h \<turnstile>  set_disconnected_nodes owner_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes ptr (remove1 child children_h) \<rightarrow>\<^sub>h h'"
    using assms(2)
    apply(auto simp add: remove_child_def elim!: bind_returns_heap_E 
               dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                      pure_returns_heap_eq[rotated, OF get_child_nodes_pure] 
               split: if_splits)[1]
    using pure_returns_heap_eq by fastforce
  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF remove_child_writes assms(2)])  
    unfolding remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved 
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_eq: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq2: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    using select_result_eq by force
  then have node_ptr_kinds_eq2: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by auto
  then have node_ptr_kinds_eq3: "node_ptr_kinds h = node_ptr_kinds h'"
    using node_ptr_kinds_M_eq by auto
  have document_ptr_kinds_eq2: "|h \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_eq2 document_ptr_kinds_M_eq by auto
  then have document_ptr_kinds_eq3: "document_ptr_kinds h = document_ptr_kinds h'"
    using document_ptr_kinds_M_eq by auto
  have children_eq: 
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    apply(rule reads_writes_preserved[OF get_child_nodes_reads remove_child_writes assms(2)]) 
    unfolding remove_child_locs_def
    using set_disconnected_nodes_get_child_nodes set_child_nodes_get_child_nodes_different_pointers 
    by fast
  then have children_eq2: 
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq: 
   "\<And>document_ptr disconnected_nodes. document_ptr \<noteq> owner_document 
       \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes
         = h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes"
    apply(rule reads_writes_preserved[OF get_disconnected_nodes_reads remove_child_writes assms(2)])  
    unfolding remove_child_locs_def
    using set_child_nodes_get_disconnected_nodes set_disconnected_nodes_get_disconnected_nodes_different_pointers
    by (metis (no_types, lifting) Un_iff owner_document select_result_I2)
  then have disconnected_nodes_eq2: 
    "\<And>document_ptr. document_ptr \<noteq> owner_document 
       \<Longrightarrow> |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h"
    apply(rule reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes h2 children_h] )
    by (simp add: set_disconnected_nodes_get_child_nodes)

  have "known_ptr ptr"
    using assms(3)
    using children_h get_child_nodes_ptr_in_heap local.known_ptrs_known_ptr by blast
  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h2]
    using set_disconnected_nodes_types_preserved type_wf
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_child_nodes_writes h']
    using  set_child_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  have children_h': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r remove1 child children_h"
    using assms(2) owner_document h2 disconnected_nodes_h children_h
    apply(auto simp add: remove_child_def split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto split: if_splits)[1]
     apply(simp)
    apply(auto split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E4)
      apply(auto)[1]
     apply(simp)
    using \<open>type_wf h2\<close> set_child_nodes_get_child_nodes \<open>known_ptr ptr\<close> h'
    by blast

  fix parent child
  assume a1: "(parent, child) \<in> parent_child_rel h'"
  then show "(parent, child) \<in> parent_child_rel h"
  proof (cases "parent = ptr")
    case True
    then show ?thesis
      using a1 remove_child_removes_parent[OF assms(1) assms(2)] children_h children_h' 
            get_child_nodes_ptr_in_heap
      apply(auto simp add: parent_child_rel_def object_ptr_kinds_eq )[1]
      by (metis notin_set_remove1)
  next
    case False
    then show ?thesis
      using a1
      by(auto simp add: parent_child_rel_def object_ptr_kinds_eq3 children_eq2)
  qed
qed


lemma remove_child_heap_is_wellformed_preserved:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
    and "known_ptrs h"
    and type_wf: "type_wf h"
  shows "type_wf h'" and "known_ptrs h'" and "heap_is_wellformed h'"
proof -
  obtain owner_document children_h h2 disconnected_nodes_h where
    owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document" and
    children_h: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h" and 
    child_in_children_h: "child \<in> set children_h" and
    disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
    h2: "h \<turnstile>  set_disconnected_nodes owner_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes ptr (remove1 child children_h) \<rightarrow>\<^sub>h h'"
    using assms(2)
    apply(auto simp add: remove_child_def elim!: bind_returns_heap_E
               dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                      pure_returns_heap_eq[rotated, OF get_child_nodes_pure] split: if_splits)[1]
    using pure_returns_heap_eq by fastforce

  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
                                OF remove_child_writes assms(2)])  
    unfolding remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved 
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_eq: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq2: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    using select_result_eq by force
  then have node_ptr_kinds_eq2: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by auto
  then have node_ptr_kinds_eq3: "node_ptr_kinds h = node_ptr_kinds h'"
    using node_ptr_kinds_M_eq by auto
  have document_ptr_kinds_eq2: "|h \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_eq2 document_ptr_kinds_M_eq by auto
  then have document_ptr_kinds_eq3: "document_ptr_kinds h = document_ptr_kinds h'"
    using document_ptr_kinds_M_eq by auto
  have children_eq: 
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    apply(rule reads_writes_preserved[OF get_child_nodes_reads remove_child_writes assms(2)])  
    unfolding remove_child_locs_def
    using set_disconnected_nodes_get_child_nodes set_child_nodes_get_child_nodes_different_pointers 
    by fast
  then have children_eq2: 
      "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq: "\<And>document_ptr disconnected_nodes. document_ptr \<noteq> owner_document 
         \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes 
             = h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes"
    apply(rule reads_writes_preserved[OF get_disconnected_nodes_reads remove_child_writes assms(2)]) 
    unfolding remove_child_locs_def
    using set_child_nodes_get_disconnected_nodes set_disconnected_nodes_get_disconnected_nodes_different_pointers
    by (metis (no_types, lifting) Un_iff owner_document select_result_I2)
  then have disconnected_nodes_eq2: 
   "\<And>document_ptr. document_ptr \<noteq> owner_document 
    \<Longrightarrow> |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h"
    apply(rule reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes h2 children_h] )
    by (simp add: set_disconnected_nodes_get_child_nodes)

  show "known_ptrs h'"
    using object_ptr_kinds_eq3 known_ptrs_preserved \<open>known_ptrs h\<close> by blast

  have "known_ptr ptr"
    using assms(3)
    using children_h get_child_nodes_ptr_in_heap local.known_ptrs_known_ptr by blast
have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h2]
    using set_disconnected_nodes_types_preserved type_wf
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_child_nodes_writes h']
    using  set_child_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  have children_h': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r remove1 child children_h"
    using assms(2) owner_document h2 disconnected_nodes_h children_h
    apply(auto simp add: remove_child_def split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto split: if_splits)[1]
     apply(simp)
    apply(auto split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E4)
      apply(auto)[1]
     apply simp
    using \<open>type_wf h2\<close> set_child_nodes_get_child_nodes \<open>known_ptr ptr\<close> h'
    by blast

  have disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
    using owner_document assms(2) h2 disconnected_nodes_h
    apply (auto simp add: remove_child_def  split: if_splits)[1]
    apply(drule bind_returns_heap_E2)
      apply(auto split: if_splits)[1]
     apply(simp)
    by(auto simp add: local.set_disconnected_nodes_get_disconnected_nodes split: if_splits)
  then have disconnected_nodes_h': "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
    apply(rule reads_writes_separate_forwards[OF get_disconnected_nodes_reads set_child_nodes_writes h'])
    by (simp add: set_child_nodes_get_disconnected_nodes)

  moreover have "a_acyclic_heap h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h' \<subseteq> parent_child_rel h"
  proof (standard, safe)
    fix parent child
    assume a1: "(parent, child) \<in> parent_child_rel h'"
    then show "(parent, child) \<in> parent_child_rel h"
    proof (cases "parent = ptr")
      case True
      then show ?thesis
        using a1 remove_child_removes_parent[OF assms(1) assms(2)] children_h children_h' 
              get_child_nodes_ptr_in_heap
        apply(auto simp add: parent_child_rel_def object_ptr_kinds_eq )[1]
        by (metis imageI notin_set_remove1)
    next
      case False
      then show ?thesis
        using a1
        by(auto simp add: parent_child_rel_def object_ptr_kinds_eq3 children_eq2)
    qed
  qed
  then have "a_acyclic_heap h'"
    using \<open>a_acyclic_heap h\<close> acyclic_heap_def acyclic_subset by blast

  moreover have "a_all_ptrs_in_heap h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3 disconnected_nodes_eq)[1]
     apply (metis (no_types, lifting) type_wf assms(3) children_eq2 children_h children_h' 
                    fset_of_list_subset fsubsetD get_child_nodes_ok get_child_nodes_ptr_in_heap 
                    is_OK_returns_result_E is_OK_returns_result_I local.known_ptrs_known_ptr 
                    object_ptr_kinds_eq3 select_result_I2 set_remove1_subset)
    by (metis (no_types, lifting) 
       \<open>\<And>thesis. (\<And>owner_document children_h h2 disconnected_nodes_h. 
             \<lbrakk>h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document; 
              h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h; child \<in> set children_h; 
              h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h; 
              h \<turnstile> set_disconnected_nodes owner_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h2; 
             h2 \<turnstile> set_child_nodes ptr (remove1 child children_h) \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
       disconnected_nodes_h disconnected_nodes_eq disconnected_nodes_h' fset_mp fset_of_list_elem 
       returns_result_eq set_ConsD)

  moreover have "a_owner_document_valid h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    apply(auto simp add: a_owner_document_valid_def object_ptr_kinds_eq3 document_ptr_kinds_eq3 
                         node_ptr_kinds_eq3)[1]
  proof -
    fix node_ptr
    assume 0: "\<forall>node_ptr. node_ptr |\<in>| node_ptr_kinds h' 
               \<longrightarrow> (\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' 
                     \<and> node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                          \<or> (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h'
                               \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
      and 1: "node_ptr |\<in>| node_ptr_kinds h'"
      and 2: "\<forall>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h' 
                      \<longrightarrow> node_ptr \<notin> set |h' \<turnstile> get_child_nodes parent_ptr|\<^sub>r"
    then show "\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' 
                       \<and> node_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    proof (cases "node_ptr = child")
      case True
      show ?thesis 
        apply(rule exI[where x=owner_document])
        using children_eq2 disconnected_nodes_eq2 children_h children_h' disconnected_nodes_h' True
        by (metis (no_types, lifting) get_disconnected_nodes_ptr_in_heap is_OK_returns_result_I 
                                      list.set_intros(1) select_result_I2)
    next
      case False
      then show ?thesis
        using 0 1 2 children_eq2 children_h children_h' disconnected_nodes_eq2 disconnected_nodes_h 
              disconnected_nodes_h' 
        apply(auto simp add: children_eq2 disconnected_nodes_eq2 dest!: select_result_I2)[1]
        by (metis children_eq2 disconnected_nodes_eq2 in_set_remove1 list.set_intros(2))
    qed
  qed

  moreover 
  {
    have h0: "a_distinct_lists h"
      using assms(1)  by (simp add: heap_is_wellformed_def)
    moreover have ha1: "(\<Union>x\<in>set |h \<turnstile> object_ptr_kinds_M|\<^sub>r. set |h \<turnstile> get_child_nodes x|\<^sub>r) 
                 \<inter> (\<Union>x\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r. set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      using \<open>a_distinct_lists h\<close>
      unfolding a_distinct_lists_def
      by(auto)
    have ha2: "ptr |\<in>| object_ptr_kinds h"
      using children_h get_child_nodes_ptr_in_heap by blast
    have ha3: "child \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r"
      using child_in_children_h children_h
      by(simp)
    have child_not_in: "\<And>document_ptr. document_ptr |\<in>| document_ptr_kinds h 
                          \<Longrightarrow> child \<notin> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
      using ha1 ha2 ha3 
      apply(simp)
      using IntI by fastforce
    moreover have "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
      apply(rule select_result_I)
      by(auto simp add: object_ptr_kinds_M_defs)
    moreover have "distinct |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
      apply(rule select_result_I)
      by(auto simp add: document_ptr_kinds_M_defs)
    ultimately have "a_distinct_lists h'"
    proof(simp (no_asm) add: a_distinct_lists_def, safe)
      assume 1: "a_distinct_lists h"
        and 3: "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"

      assume 1: "a_distinct_lists h"
        and 3: "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
      have 4: "distinct (concat ((map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r)))"
        using 1 by(auto simp add: a_distinct_lists_def)
      show "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r) 
                     (sorted_list_of_set (fset (object_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I[OF 3[unfolded object_ptr_kinds_eq2], simplified])
        fix x
        assume 5: "x |\<in>| object_ptr_kinds h'"
        then have 6: "distinct |h \<turnstile> get_child_nodes x|\<^sub>r"
          using 4 distinct_concat_map_E object_ptr_kinds_eq2 by fastforce
        obtain children where children: "h \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children" 
                        and distinct_children: "distinct children"
          by (metis "5" "6" type_wf assms(3) get_child_nodes_ok local.known_ptrs_known_ptr 
                            object_ptr_kinds_eq3 select_result_I)
        obtain children' where children': "h' \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children'"
          using children children_eq children_h' by fastforce
        then have "distinct children'"
        proof (cases "ptr = x")
          case True
          then show ?thesis 
            using children distinct_children children_h children_h'
            by (metis children' distinct_remove1 returns_result_eq)
        next
          case False
          then show ?thesis 
            using children distinct_children children_eq[OF False]
            using children' distinct_lists_children h0
            using select_result_I2 by fastforce
        qed

        then show "distinct |h' \<turnstile> get_child_nodes x|\<^sub>r"
          using children' by(auto simp add: )
      next
        fix x y
        assume 5: "x |\<in>| object_ptr_kinds h'" and 6: "y |\<in>| object_ptr_kinds h'" and 7: "x \<noteq> y"
        obtain children_x where children_x: "h \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children_x"
          by (metis "5" type_wf assms(3) get_child_nodes_ok is_OK_returns_result_E 
                    local.known_ptrs_known_ptr object_ptr_kinds_eq3)
        obtain children_y where children_y: "h \<turnstile> get_child_nodes y \<rightarrow>\<^sub>r children_y"
          by (metis "6" type_wf assms(3) get_child_nodes_ok is_OK_returns_result_E 
                    local.known_ptrs_known_ptr object_ptr_kinds_eq3)
        obtain children_x' where children_x': "h' \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children_x'"
          using children_eq children_h' children_x by fastforce
        obtain children_y' where children_y': "h' \<turnstile> get_child_nodes y \<rightarrow>\<^sub>r children_y'"
          using children_eq children_h' children_y by fastforce
        have "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r))"
          using h0 by(auto simp add: a_distinct_lists_def)
        then have 8: "set children_x \<inter> set children_y = {}"
          using "7" assms(1) children_x children_y local.heap_is_wellformed_one_parent by blast
        have "set children_x' \<inter> set children_y' = {}"
        proof (cases "ptr = x")
          case True
          then have "ptr \<noteq> y"
            by(simp add: 7)
          have "children_x' = remove1 child children_x"
            using children_h children_h' children_x children_x' True returns_result_eq by fastforce
          moreover have "children_y' = children_y"
            using children_y children_y' children_eq[OF \<open>ptr \<noteq> y\<close>] by auto
          ultimately show ?thesis
            using 8 set_remove1_subset by fastforce
        next
          case False
          then show ?thesis
          proof (cases "ptr = y")
            case True
            have "children_y' = remove1 child children_y"
              using children_h children_h' children_y children_y' True returns_result_eq by fastforce
            moreover have "children_x' = children_x"
              using children_x children_x' children_eq[OF \<open>ptr \<noteq> x\<close>] by auto
            ultimately show ?thesis
              using 8 set_remove1_subset by fastforce
          next
            case False
            have "children_x' = children_x"
              using children_x children_x' children_eq[OF \<open>ptr \<noteq> x\<close>] by auto
            moreover have "children_y' = children_y"
              using children_y children_y' children_eq[OF \<open>ptr \<noteq> y\<close>] by auto
            ultimately show ?thesis
              using 8 by simp
          qed
        qed
        then show "set |h' \<turnstile> get_child_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_child_nodes y|\<^sub>r = {}"
          using children_x' children_y'
          by (metis (no_types, lifting) select_result_I2)
      qed
    next
      assume 2: "distinct |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
      then have 4: "distinct  (sorted_list_of_set (fset (document_ptr_kinds h')))"
        by simp
      have 3: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                        (sorted_list_of_set (fset (document_ptr_kinds h')))))"
        using h0
        by(simp add: a_distinct_lists_def document_ptr_kinds_eq3)

      show "distinct (concat (map (\<lambda>document_ptr. |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                         (sorted_list_of_set (fset (document_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I[OF 4[unfolded document_ptr_kinds_eq3]])
        fix x
        assume 4: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
        have 5: "distinct |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
          using distinct_lists_disconnected_nodes[OF h0] 4 get_disconnected_nodes_ok
          by (simp add: type_wf document_ptr_kinds_eq3 select_result_I)
        show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
        proof (cases "x = owner_document")
          case True
          have "child \<notin> set |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
            using child_not_in  document_ptr_kinds_eq2 "4" by fastforce
          moreover have "|h' \<turnstile> get_disconnected_nodes x|\<^sub>r = child # |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
            using disconnected_nodes_h' disconnected_nodes_h unfolding True
            by(simp)
          ultimately show ?thesis
            using 5 unfolding True
            by simp 
        next
          case False
          show ?thesis
            using "5" False disconnected_nodes_eq2 by auto
        qed
      next
        fix x y
        assume 4: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and 5: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))" and "x \<noteq> y"
        obtain disc_nodes_x where disc_nodes_x: "h \<turnstile> get_disconnected_nodes x \<rightarrow>\<^sub>r disc_nodes_x"
          using 4 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of x] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_y where disc_nodes_y: "h \<turnstile> get_disconnected_nodes y \<rightarrow>\<^sub>r disc_nodes_y"
          using 5 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of y] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_x' where disc_nodes_x': "h' \<turnstile> get_disconnected_nodes x \<rightarrow>\<^sub>r disc_nodes_x'"
          using 4 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of x] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_y' where disc_nodes_y': "h' \<turnstile> get_disconnected_nodes y \<rightarrow>\<^sub>r disc_nodes_y'"
          using 5 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of y] document_ptr_kinds_eq2
          by auto
        have "distinct 
               (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) |h \<turnstile> document_ptr_kinds_M|\<^sub>r))"
          using h0 by (simp add: a_distinct_lists_def)
        then have 6: "set disc_nodes_x \<inter> set disc_nodes_y = {}"
          using \<open>x \<noteq> y\<close> assms(1) disc_nodes_x disc_nodes_y local.heap_is_wellformed_one_disc_parent 
          by blast

        have "set disc_nodes_x' \<inter> set disc_nodes_y' = {}"
        proof (cases "x = owner_document")
          case True
          then have "y \<noteq> owner_document"
            using \<open>x \<noteq> y\<close> by simp
          then have "disc_nodes_y' = disc_nodes_y"
            using disconnected_nodes_eq[OF \<open>y \<noteq> owner_document\<close>] disc_nodes_y disc_nodes_y' 
            by auto
          have "disc_nodes_x' = child # disc_nodes_x"
            using disconnected_nodes_h' disc_nodes_x disc_nodes_x' True disconnected_nodes_h returns_result_eq 
            by fastforce
          have "child \<notin> set disc_nodes_y"
            using child_not_in  disc_nodes_y 5
            using document_ptr_kinds_eq2  by fastforce
          then show ?thesis
            apply(unfold \<open>disc_nodes_x' = child # disc_nodes_x\<close> \<open>disc_nodes_y' = disc_nodes_y\<close>)
            using 6 by auto
        next
          case False
          then show ?thesis
          proof (cases "y = owner_document")
            case True
            then have "disc_nodes_x' = disc_nodes_x"
              using disconnected_nodes_eq[OF \<open>x \<noteq> owner_document\<close>] disc_nodes_x disc_nodes_x' by auto
            have "disc_nodes_y' = child # disc_nodes_y"
              using disconnected_nodes_h' disc_nodes_y disc_nodes_y' True disconnected_nodes_h returns_result_eq 
              by fastforce
            have "child \<notin> set disc_nodes_x"
              using child_not_in  disc_nodes_x 4
              using document_ptr_kinds_eq2  by fastforce
            then show ?thesis
              apply(unfold \<open>disc_nodes_y' = child # disc_nodes_y\<close> \<open>disc_nodes_x' = disc_nodes_x\<close>)
              using 6 by auto
          next
            case False
            have "disc_nodes_x' = disc_nodes_x"
              using disconnected_nodes_eq[OF \<open>x \<noteq> owner_document\<close>] disc_nodes_x disc_nodes_x' by auto
            have "disc_nodes_y' = disc_nodes_y"
              using disconnected_nodes_eq[OF \<open>y \<noteq> owner_document\<close>] disc_nodes_y disc_nodes_y' by auto
            then show ?thesis 
              apply(unfold \<open>disc_nodes_y' = disc_nodes_y\<close> \<open>disc_nodes_x' = disc_nodes_x\<close>)
              using 6 by auto
          qed
        qed
        then show "set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
          using disc_nodes_x' disc_nodes_y' by auto
      qed
    next
fix x xa xb
assume 1: "xa \<in> fset (object_ptr_kinds h')"
    and 2: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
    and 3: "xb \<in> fset (document_ptr_kinds h')"
    and 4: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      obtain disc_nodes where disc_nodes: "h \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r disc_nodes"
        using 3 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of xb] document_ptr_kinds_eq2 by auto
      obtain disc_nodes' where disc_nodes': "h' \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r disc_nodes'"
        using 3 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of xb]  document_ptr_kinds_eq2 by auto

      obtain children where children: "h \<turnstile> get_child_nodes xa \<rightarrow>\<^sub>r children"
        by (metis "1" type_wf assms(3) finite_set_in get_child_nodes_ok is_OK_returns_result_E 
                  local.known_ptrs_known_ptr object_ptr_kinds_eq3)
      obtain children' where children': "h' \<turnstile> get_child_nodes xa \<rightarrow>\<^sub>r children'"
        using children children_eq children_h' by fastforce
      have "\<And>x. x \<in> set |h \<turnstile> get_child_nodes xa|\<^sub>r \<Longrightarrow> x \<in> set |h \<turnstile> get_disconnected_nodes xb|\<^sub>r \<Longrightarrow> False"
        using 1 3 
        apply(fold \<open> object_ptr_kinds h =  object_ptr_kinds h'\<close>) 
        apply(fold \<open> document_ptr_kinds h =  document_ptr_kinds h'\<close>) 
        using children disc_nodes h0 apply(auto simp add: a_distinct_lists_def)[1]
      by (metis (no_types, lifting) h0 local.distinct_lists_no_parent select_result_I2)
      then have 5: "\<And>x. x \<in> set children \<Longrightarrow> x \<in> set disc_nodes \<Longrightarrow> False"
        using children disc_nodes  by fastforce
      have 6: "|h' \<turnstile> get_child_nodes xa|\<^sub>r = children'"
        using children' by (simp add: )
      have 7: "|h' \<turnstile> get_disconnected_nodes xb|\<^sub>r = disc_nodes'"
        using disc_nodes' by (simp add: )
      have "False"
      proof (cases "xa = ptr")
        case True
        have "distinct children_h"
          using children_h distinct_lists_children h0 \<open>known_ptr ptr\<close> by blast
        have "|h' \<turnstile> get_child_nodes ptr|\<^sub>r = remove1 child children_h"
          using children_h'
          by(simp add: )
        have "children = children_h"
          using True children children_h by auto
        show ?thesis
          using disc_nodes' children' 5 2 4 children_h \<open>distinct children_h\<close> disconnected_nodes_h'
          apply(auto simp add: 6 7 
                \<open>xa = ptr\<close> \<open>|h' \<turnstile> get_child_nodes ptr|\<^sub>r = remove1 child children_h\<close> \<open>children = children_h\<close>)[1]
          by (metis (no_types, lifting) disc_nodes disconnected_nodes_eq2 disconnected_nodes_h 
                                        select_result_I2 set_ConsD)
      next
        case False
        have "children' = children"
          using children' children children_eq[OF False[symmetric]]
          by auto                      
        then show ?thesis
        proof (cases "xb = owner_document")
          case True
          then show ?thesis
            using disc_nodes disconnected_nodes_h disconnected_nodes_h'
            using "2" "4" "5" "6" "7" False \<open>children' = children\<close> assms(1) child_in_children_h 
                   child_parent_dual children children_h disc_nodes' get_child_nodes_ptr_in_heap 
                   list.set_cases list.simps(3) option.simps(1) returns_result_eq set_ConsD 
            by (metis (no_types, hide_lams) assms(3) type_wf)
        next
          case False
          then show ?thesis
            using "2" "4" "5" "6" "7" \<open>children' = children\<close> disc_nodes disc_nodes' 
                  disconnected_nodes_eq returns_result_eq 
            by metis
        qed
      qed
      then show "x \<in> {}"
        by simp
    qed
  }

  ultimately show "heap_is_wellformed h'"
    using heap_is_wellformed_def by blast
qed

lemma remove_child_removes_child:
  assumes wellformed: "heap_is_wellformed h"
    and remove_child: "h \<turnstile> remove_child ptr' child \<rightarrow>\<^sub>h h'"
    and children: "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
and known_ptrs: "known_ptrs h"
and type_wf: "type_wf h"
shows "child \<notin> set children"
proof -
  obtain owner_document children_h h2 disconnected_nodes_h where
    owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document" and
    children_h: "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children_h" and 
    child_in_children_h: "child \<in> set children_h" and
    disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
    h2: "h \<turnstile>  set_disconnected_nodes owner_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes ptr' (remove1 child children_h) \<rightarrow>\<^sub>h h'"
    using assms(2)
    apply(auto simp add: remove_child_def elim!: bind_returns_heap_E 
               dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                      pure_returns_heap_eq[rotated, OF get_child_nodes_pure] 
               split: if_splits)[1]
    using pure_returns_heap_eq
    by fastforce
  have "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF remove_child_writes remove_child]) 
    unfolding remove_child_locs_def
    using set_child_nodes_pointers_preserved set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  moreover have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF remove_child_writes assms(2)]
    using set_child_nodes_types_preserved set_disconnected_nodes_types_preserved type_wf
    unfolding remove_child_locs_def
    apply(auto simp add: reflp_def transp_def)
    by blast
  ultimately show ?thesis
    using remove_child_removes_parent remove_child_heap_is_wellformed_preserved child_parent_dual
    by (meson children known_ptrs local.known_ptrs_preserved option.distinct(1) remove_child 
              returns_result_eq type_wf wellformed)
qed

lemma remove_child_removes_first_child:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children"
  assumes "h \<turnstile> remove_child ptr node_ptr \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
proof -
  obtain h2 disc_nodes owner_document where
    "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r owner_document" and
    "h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes" and
    h2: "h \<turnstile> set_disconnected_nodes owner_document (node_ptr # disc_nodes) \<rightarrow>\<^sub>h h2" and
    "h2 \<turnstile> set_child_nodes ptr children \<rightarrow>\<^sub>h h'"
    using assms(5)
    apply(auto simp add: remove_child_def 
               dest!: bind_returns_heap_E3[rotated, OF assms(4) get_child_nodes_pure, rotated])[1]
    by(auto elim!: bind_returns_heap_E
                   bind_returns_heap_E2[rotated,OF get_owner_document_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])
  have "known_ptr ptr"
    by (meson assms(3) assms(4) is_OK_returns_result_I get_child_nodes_ptr_in_heap known_ptrs_known_ptr)
  moreover have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children"
    apply(rule reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes h2 assms(4)])
    using set_disconnected_nodes_get_child_nodes set_child_nodes_get_child_nodes_different_pointers 
    by fast
  moreover have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h2]
    using \<open>type_wf h\<close> set_disconnected_nodes_types_preserved
    by(auto simp add:  reflp_def transp_def)
  ultimately show ?thesis
    using set_child_nodes_get_child_nodes\<open>h2 \<turnstile> set_child_nodes ptr children \<rightarrow>\<^sub>h h'\<close>
    by fast
qed

lemma remove_removes_child:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children"
  assumes "h \<turnstile> remove node_ptr \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
proof -
  have "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some ptr"
    using child_parent_dual assms by fastforce
  show ?thesis
    using assms remove_child_removes_first_child
    by(auto simp add: remove_def 
            dest!: bind_returns_heap_E3[rotated, OF \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some ptr\<close>, rotated] 
                   bind_returns_heap_E3[rotated, OF assms(4) get_child_nodes_pure, rotated])
qed

lemma remove_for_all_empty_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "h \<turnstile> forall_M remove children \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"
  using assms
proof(induct children arbitrary: h h')
  case Nil
  then show ?case 
    by simp
next
  case (Cons a children)
  have "h \<turnstile> get_parent a \<rightarrow>\<^sub>r Some ptr"
    using child_parent_dual Cons by fastforce
  with Cons show ?case
  proof(auto elim!: bind_returns_heap_E)[1]
    fix h2
    assume 0: "(\<And>h h'. heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                   \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
                       \<Longrightarrow> h \<turnstile> forall_M remove children \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r [])"
      and 1: "heap_is_wellformed h"
      and 2: "type_wf h"
      and 3: "known_ptrs h"
      and 4: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r a # children"
      and 5: "h \<turnstile> get_parent a \<rightarrow>\<^sub>r Some ptr"
      and 7: "h \<turnstile> remove a \<rightarrow>\<^sub>h h2"
      and 8: "h2 \<turnstile> forall_M remove children \<rightarrow>\<^sub>h h'"
    then have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using remove_removes_child by blast

    moreover have "heap_is_wellformed h2"
      using 7 1 2 3 remove_child_heap_is_wellformed_preserved(3)
      by(auto simp add: remove_def
               elim!: bind_returns_heap_E 
                      bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] 
               split: option.splits)
    moreover have "type_wf h2"
      using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF remove_writes 7]
      using \<open>type_wf h\<close> remove_child_types_preserved
      by(auto simp add: a_remove_child_locs_def reflp_def transp_def)
    moreover have "object_ptr_kinds h = object_ptr_kinds h2"
      using 7
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                  OF remove_writes])
      using remove_child_pointers_preserved
      by (auto simp add: reflp_def transp_def)
    then have "known_ptrs h2"
      using 3  known_ptrs_preserved by blast

    ultimately show "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"
      using 0 8 by fast
  qed
qed
end

locale l_remove_child_wf2 = l_type_wf + l_known_ptrs + l_remove_child_defs + l_heap_is_wellformed_defs 
                            + l_get_child_nodes_defs + l_remove_defs +
  assumes remove_child_preserves_type_wf: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> type_wf h'"
  assumes remove_child_preserves_known_ptrs: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> known_ptrs h'"
  assumes remove_child_heap_is_wellformed_preserved:
    "type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> heap_is_wellformed h \<Longrightarrow> h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'
               \<Longrightarrow> heap_is_wellformed h'"
  assumes remove_child_removes_child:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> remove_child ptr' child \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children
                          \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h
                          \<Longrightarrow> child \<notin> set children"
  assumes remove_child_removes_first_child: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children 
                          \<Longrightarrow> h \<turnstile> remove_child ptr node_ptr \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes remove_removes_child: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children 
                          \<Longrightarrow> h \<turnstile> remove node_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes remove_for_all_empty_children: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children 
                          \<Longrightarrow> h \<turnstile> forall_M remove children \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"

interpretation i_remove_child_wf2?: l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs 
     set_child_nodes set_child_nodes_locs get_parent get_parent_locs get_owner_document 
     get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
     set_disconnected_nodes_locs remove_child remove_child_locs remove type_wf known_ptr known_ptrs 
     heap_is_wellformed parent_child_rel
  by unfold_locales

lemma remove_child_wf2_is_l_remove_child_wf2 [instances]: 
  "l_remove_child_wf2 type_wf known_ptr known_ptrs remove_child heap_is_wellformed get_child_nodes remove"
  apply(auto simp add: l_remove_child_wf2_def l_remove_child_wf2_axioms_def instances)[1]
  using remove_child_heap_is_wellformed_preserved apply(fast, fast, fast)
  using remove_child_removes_child apply fast
  using remove_child_removes_first_child apply fast
  using remove_removes_child apply fast
  using remove_for_all_empty_children apply fast
  done
  


subsection \<open>adopt\_node\<close>
                     
locale l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf +
  l_remove_child_wf2 +
  l_heap_is_wellformed
begin
lemma adopt_node_removes_first_child:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r node # children"
  shows "h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
proof -
  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast node) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node \<rightarrow>\<^sub>r parent_opt" and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> do { remove_child parent node } 
                               | None \<Rightarrow> do { return ()}) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> (if owner_document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (node # disc_nodes)
      } else do { return () }) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: adopt_node_def elim!: bind_returns_heap_E 
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                   pure_returns_heap_eq[rotated, OF get_parent_pure])
  have "h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using h2 remove_child_removes_first_child assms(1) assms(2) assms(3) assms(5)
    by (metis list.set_intros(1) local.child_parent_dual option.simps(5) parent_opt returns_result_eq)
  then
  show ?thesis
    using h'
    by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] 
            dest!: reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes] 
            split: if_splits)
qed
end
                     
locale l_adopt_node_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node +
  l_get_owner_document_wf +
  l_remove_child_wf2 +
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma adopt_node_removes_child:
  assumes wellformed: "heap_is_wellformed h"
    and adopt_node: "h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h2"
    and children: "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "node_ptr \<notin> set children"
proof -
  obtain old_document parent_opt h' where
    old_document: "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt" and
    h': "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent node_ptr | None \<Rightarrow> return () ) \<rightarrow>\<^sub>h h'"
    using adopt_node get_parent_pure 
    by(auto simp add: adopt_node_def
            elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] 
            split: if_splits)

  then have "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    using adopt_node                                                                                            
    apply(auto simp add: adopt_node_def  
                    dest!: bind_returns_heap_E3[rotated, OF old_document, rotated] 
                           bind_returns_heap_E3[rotated, OF parent_opt, rotated] 
                    elim!: bind_returns_heap_E4[rotated, OF h', rotated])[1]
    apply(auto split: if_splits 
               elim!: bind_returns_heap_E 
                      bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])[1]
     apply (simp add: set_disconnected_nodes_get_child_nodes children 
                      reads_writes_preserved[OF get_child_nodes_reads set_disconnected_nodes_writes])
    using children by blast
  show ?thesis
  proof(insert parent_opt h', induct parent_opt)
    case None
    then show ?case
      using child_parent_dual wellformed known_ptrs type_wf 
            \<open>h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children\<close> returns_result_eq
      by fastforce
  next
    case (Some option)
    then show ?case
      using remove_child_removes_child \<open>h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children\<close> known_ptrs type_wf 
            wellformed
      by auto
  qed
qed

lemma adopt_node_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> adopt_node document_ptr child \<rightarrow>\<^sub>h h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "heap_is_wellformed h'"
proof -
  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r old_document" 
  and
    parent_opt: "h \<turnstile> get_parent child \<rightarrow>\<^sub>r parent_opt" 
  and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent child | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h2" 
  and
    h': "h2 \<turnstile> (if document_ptr \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 child old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes document_ptr;
        set_disconnected_nodes document_ptr (child # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h'"
    using assms(2)
    by(auto simp add: adopt_node_def elim!: bind_returns_heap_E 
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                   pure_returns_heap_eq[rotated, OF get_parent_pure])

  have object_ptr_kinds_h_eq3: "object_ptr_kinds h = object_ptr_kinds h2"
    using h2 apply(simp split: option.splits)
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF remove_child_writes])
    using remove_child_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h: 
           "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using h2 remove_child_heap_is_wellformed_preserved known_ptrs type_wf
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure) 
  then show ?thesis
  proof(cases "document_ptr = old_document")
    case True
    then show ?thesis
      using h' wellformed_h2 by auto
  next
    case False
    then obtain h3 old_disc_nodes disc_nodes_document_ptr_h3 where
      docs_neq: "document_ptr \<noteq> old_document" and
      old_disc_nodes: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
      h3: "h2 \<turnstile> set_disconnected_nodes old_document (remove1 child old_disc_nodes) \<rightarrow>\<^sub>h h3" and
      disc_nodes_document_ptr_h3: 
             "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3" and
      h': "h3 \<turnstile> set_disconnected_nodes document_ptr (child # disc_nodes_document_ptr_h3) \<rightarrow>\<^sub>h h'"
      using h'
      by(auto elim!: bind_returns_heap_E 
                     bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

    have object_ptr_kinds_h2_eq3: "object_ptr_kinds h2 = object_ptr_kinds h3"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                  OF set_disconnected_nodes_writes h3])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved 
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h2: 
              "\<And>ptrs. h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
      by(simp add: object_ptr_kinds_M_defs)
    then have object_ptr_kinds_eq_h2: "|h2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
      by(simp)
    then have node_ptr_kinds_eq_h2: "|h2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_ptr_kinds_M_eq by blast
    then have node_ptr_kinds_eq3_h2: "node_ptr_kinds h2 = node_ptr_kinds h3"
      by auto
    have document_ptr_kinds_eq2_h2: "|h2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
      using object_ptr_kinds_eq_h2 document_ptr_kinds_M_eq by auto
    then have document_ptr_kinds_eq3_h2: "document_ptr_kinds h2 = document_ptr_kinds h3"
      using object_ptr_kinds_eq_h2 document_ptr_kinds_M_eq by auto
    have children_eq_h2: 
      "\<And>ptr children. h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h2: "\<And>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have object_ptr_kinds_h3_eq3: "object_ptr_kinds h3 = object_ptr_kinds h'"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                  OF set_disconnected_nodes_writes h'])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved 
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h3: 
      "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
      by(simp add: object_ptr_kinds_M_defs)
    then have object_ptr_kinds_eq_h3: "|h3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
      by(simp)
    then have node_ptr_kinds_eq_h3: "|h3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_ptr_kinds_M_eq by blast
    then have node_ptr_kinds_eq3_h3: "node_ptr_kinds h3 = node_ptr_kinds h'"
      by auto
    have document_ptr_kinds_eq2_h3: "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
      using object_ptr_kinds_eq_h3 document_ptr_kinds_M_eq by auto
    then have document_ptr_kinds_eq3_h3: "document_ptr_kinds h3 = document_ptr_kinds h'"
      using object_ptr_kinds_eq_h3 document_ptr_kinds_M_eq by auto
    have children_eq_h3: 
      "\<And>ptr children. h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h3: "\<And>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r = |h' \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have disconnected_nodes_eq_h2: 
      "\<And>doc_ptr disc_nodes. old_document \<noteq> doc_ptr 
      \<Longrightarrow> h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h2: 
      "\<And>doc_ptr. old_document \<noteq> doc_ptr 
       \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
      using select_result_eq by force
    obtain disc_nodes_old_document_h2 where disc_nodes_old_document_h2: 
      "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
      using old_disc_nodes by blast
    then have disc_nodes_old_document_h3:
      "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 child disc_nodes_old_document_h2"
      using h3 old_disc_nodes returns_result_eq set_disconnected_nodes_get_disconnected_nodes 
      by fastforce
    have "distinct disc_nodes_old_document_h2"
      using disc_nodes_old_document_h2 local.heap_is_wellformed_disconnected_nodes_distinct wellformed_h2 
      by blast


    have "type_wf h2"
    proof (insert h2, induct  parent_opt)
      case None
      then show ?case
        using type_wf by simp
    next
      case (Some option)
      then show ?case
        using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF remove_child_writes] 
             type_wf remove_child_types_preserved
        by (simp add: reflp_def transp_def)
    qed
    then have "type_wf h3"
      using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
      using  set_disconnected_nodes_types_preserved  
      by(auto simp add: reflp_def transp_def)
    then have "type_wf h'"
      using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
      using  set_disconnected_nodes_types_preserved  
      by(auto simp add: reflp_def transp_def)

    have disconnected_nodes_eq_h3: 
      "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr 
       \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h3: 
      "\<And>doc_ptr. document_ptr \<noteq> doc_ptr 
      \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
      using select_result_eq by force
    have disc_nodes_document_ptr_h2: 
      "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3"
      using disconnected_nodes_eq_h2 docs_neq disc_nodes_document_ptr_h3 by auto
    have disc_nodes_document_ptr_h': "
      h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r child # disc_nodes_document_ptr_h3"
      using h' disc_nodes_document_ptr_h3
      using set_disconnected_nodes_get_disconnected_nodes by blast

    have document_ptr_in_heap: "document_ptr |\<in>| document_ptr_kinds h2"
      using disc_nodes_document_ptr_h3 document_ptr_kinds_eq2_h2 get_disconnected_nodes_ok assms(1)
      unfolding heap_is_wellformed_def
      using disc_nodes_document_ptr_h2 get_disconnected_nodes_ptr_in_heap by blast 
    have old_document_in_heap: "old_document |\<in>| document_ptr_kinds h2"
      using disc_nodes_old_document_h3 document_ptr_kinds_eq2_h2 get_disconnected_nodes_ok assms(1)
      unfolding heap_is_wellformed_def
      using get_disconnected_nodes_ptr_in_heap old_disc_nodes by blast 

    have "child \<in> set disc_nodes_old_document_h2"
    proof (insert parent_opt h2, induct parent_opt)
      case None
      then have "h = h2"
        by(auto)
      moreover have "a_owner_document_valid h"
        using assms(1) heap_is_wellformed_def by(simp add: heap_is_wellformed_def)
      ultimately show ?case 
        using old_document disc_nodes_old_document_h2 None(1) child_parent_dual[OF assms(1)] 
              in_disconnected_nodes_no_parent assms(1) known_ptrs type_wf by blast
    next
      case (Some option)
      then show ?case
        apply(simp split: option.splits)
        using assms(1) disc_nodes_old_document_h2 old_document remove_child_in_disconnected_nodes known_ptrs 
        by blast
    qed
    have "child \<notin> set (remove1 child disc_nodes_old_document_h2)"
      using disc_nodes_old_document_h3 h3 known_ptrs wellformed_h2 \<open>distinct disc_nodes_old_document_h2\<close> 
      by auto
    have "child \<notin> set disc_nodes_document_ptr_h3"
    proof -
      have "a_distinct_lists h2"
        using heap_is_wellformed_def wellformed_h2 by blast
      then have 0: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                                          |h2 \<turnstile> document_ptr_kinds_M|\<^sub>r))"
        by(simp add: a_distinct_lists_def)
      show ?thesis
        using distinct_concat_map_E(1)[OF 0] \<open>child \<in> set disc_nodes_old_document_h2\<close> 
              disc_nodes_old_document_h2 disc_nodes_document_ptr_h2
        by (meson \<open>type_wf h2\<close> docs_neq known_ptrs local.get_owner_document_disconnected_nodes 
                  local.known_ptrs_preserved object_ptr_kinds_h_eq3 returns_result_eq wellformed_h2)
    qed

    have child_in_heap: "child |\<in>| node_ptr_kinds h"
      using get_owner_document_ptr_in_heap[OF is_OK_returns_result_I[OF old_document]] 
            node_ptr_kinds_commutes by blast
    have "a_acyclic_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    have "parent_child_rel h' \<subseteq> parent_child_rel h2"
    proof
      fix x
      assume "x \<in> parent_child_rel h'"
      then show "x \<in> parent_child_rel h2"
        using object_ptr_kinds_h2_eq3  object_ptr_kinds_h3_eq3 children_eq2_h2 children_eq2_h3 
              mem_Collect_eq object_ptr_kinds_M_eq_h3 select_result_eq split_cong
        unfolding parent_child_rel_def
        by(simp)
    qed
    then have "a_acyclic_heap h'"
      using \<open>a_acyclic_heap h2\<close> acyclic_heap_def acyclic_subset by blast

    moreover have "a_all_ptrs_in_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_all_ptrs_in_heap h3"
      apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3_h2 children_eq_h2)[1]
      by (metis (mono_tags, lifting) disc_nodes_old_document_h2 disc_nodes_old_document_h3 
                disconnected_nodes_eq_h2 fset_of_list_elem fset_rev_mp returns_result_eq 
                set_remove1_subset subsetCE)
    then have "a_all_ptrs_in_heap h'"   
      apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3_h3 children_eq_h3)[1]
      by (metis (no_types) NodeMonad.ptr_kinds_ptr_kinds_M child_in_heap disc_nodes_document_ptr_h' 
                disc_nodes_document_ptr_h3 disconnected_nodes_eq_h3 fset_mp fset_of_list_elem 
                node_ptr_kinds_eq_h node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h3 select_result_I2 
                set_ConsD)

    moreover have "a_owner_document_valid h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_owner_document_valid h'"
      apply(simp add: a_owner_document_valid_def node_ptr_kinds_eq_h2 node_ptr_kinds_eq3_h3 
                      object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 document_ptr_kinds_eq2_h2 
                      document_ptr_kinds_eq2_h3 children_eq2_h2 children_eq2_h3 )
      by (metis (no_types) disc_nodes_document_ptr_h' disc_nodes_document_ptr_h2 
                           disc_nodes_old_document_h2 disc_nodes_old_document_h3 
                           disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_in_heap 
                           document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3 in_set_remove1
                           list.set_intros(1) list.set_intros(2) node_ptr_kinds_eq3_h2 
                           node_ptr_kinds_eq3_h3 object_ptr_kinds_h2_eq3 object_ptr_kinds_h3_eq3 
                           select_result_I2)

    have a_distinct_lists_h2: "a_distinct_lists h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_distinct_lists h'"
      apply(auto simp add: a_distinct_lists_def object_ptr_kinds_eq_h3 object_ptr_kinds_eq_h2 
                          children_eq2_h2 children_eq2_h3)[1]
    proof -
      assume 1: "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r)
                          (sorted_list_of_set (fset (object_ptr_kinds h')))))"
        and 2: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                             (sorted_list_of_set (fset (document_ptr_kinds h2)))))"
        and 3: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) 
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      show "distinct (concat (map (\<lambda>document_ptr. |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                              (sorted_list_of_set (fset (document_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I)
        show "distinct (sorted_list_of_set (fset (document_ptr_kinds h')))"
          by(auto simp add: document_ptr_kinds_M_def )
      next
        fix x
        assume a1: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
        have 4: "distinct |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r"
          using a_distinct_lists_h2 "2" a1 concat_map_all_distinct document_ptr_kinds_eq2_h2 
                document_ptr_kinds_eq2_h3 
          by fastforce
        then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
        proof (cases "old_document \<noteq> x")
          case True
          then show ?thesis 
          proof (cases "document_ptr \<noteq> x")
            case True
            then show ?thesis 
              using disconnected_nodes_eq2_h2[OF \<open>old_document \<noteq> x\<close>] 
                    disconnected_nodes_eq2_h3[OF \<open>document_ptr \<noteq> x\<close>] 4
              by(auto)
          next
            case False
            then show ?thesis 
              using  disc_nodes_document_ptr_h3 disc_nodes_document_ptr_h' 4
                      \<open>child \<notin> set disc_nodes_document_ptr_h3\<close>
              by(auto simp add: disconnected_nodes_eq2_h2[OF \<open>old_document \<noteq> x\<close>] )
          qed
        next
          case False
          then show ?thesis
            by (metis (no_types, hide_lams) \<open>distinct disc_nodes_old_document_h2\<close> 
                      disc_nodes_old_document_h3 disconnected_nodes_eq2_h3 
                      distinct_remove1 docs_neq select_result_I2)
        qed
      next
        fix x y
        assume a0: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a1: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a2: "x \<noteq> y"

        moreover have 5: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
          using 2 calculation 
          by (auto simp add: document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3 dest: distinct_concat_map_E(1))
        ultimately show "set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
        proof(cases "old_document = x")
          case True
          have "old_document \<noteq> y"
            using \<open>x \<noteq> y\<close> \<open>old_document = x\<close> by simp
          have "document_ptr \<noteq> x"
            using docs_neq \<open>old_document = x\<close> by auto
          show ?thesis
          proof(cases "document_ptr = y")
            case True
            then show ?thesis
              using 5 True select_result_I2[OF disc_nodes_document_ptr_h'] 
                select_result_I2[OF disc_nodes_document_ptr_h2]
                select_result_I2[OF disc_nodes_old_document_h2]
                select_result_I2[OF disc_nodes_old_document_h3] \<open>old_document = x\<close>
              by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
                         \<open>document_ptr \<noteq> x\<close> disconnected_nodes_eq2_h3 disjoint_iff_not_equal 
                         notin_set_remove1 set_ConsD) 
          next
            case False
            then show ?thesis 
              using 5 select_result_I2[OF disc_nodes_document_ptr_h'] 
                select_result_I2[OF disc_nodes_document_ptr_h2]
                select_result_I2[OF disc_nodes_old_document_h2] 
                select_result_I2[OF disc_nodes_old_document_h3]
                disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 \<open>old_document = x\<close> 
                docs_neq \<open>old_document \<noteq> y\<close>
              by (metis (no_types, lifting) disjoint_iff_not_equal notin_set_remove1)
          qed
        next
          case False
          then show ?thesis
          proof(cases "old_document = y")
            case True
            then show ?thesis
            proof(cases "document_ptr = x")
              case True
              show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h'] 
                        select_result_I2[OF disc_nodes_document_ptr_h2]
                        select_result_I2[OF disc_nodes_old_document_h2] 
                        select_result_I2[OF disc_nodes_old_document_h3]
                        \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close> \<open>document_ptr = x\<close>
              apply(simp)
              by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close> 
                        disconnected_nodes_eq2_h3 disjoint_iff_not_equal notin_set_remove1)
            next
              case False
              then show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h'] 
                      select_result_I2[OF disc_nodes_document_ptr_h2]
                      select_result_I2[OF disc_nodes_old_document_h2] 
                      select_result_I2[OF disc_nodes_old_document_h3] 
                      \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close> \<open>document_ptr \<noteq> x\<close>
                by (metis (no_types, lifting) disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 
                          disjoint_iff_not_equal docs_neq notin_set_remove1)
            qed
          next
            case False
            have "set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}"
              by (metis DocumentMonad.ptr_kinds_M_ok DocumentMonad.ptr_kinds_M_ptr_kinds False
                        \<open>type_wf h2\<close> a1 disc_nodes_old_document_h2 document_ptr_kinds_M_def 
                        document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3 
                        l_ptr_kinds_M.ptr_kinds_ptr_kinds_M local.get_disconnected_nodes_ok
                        local.heap_is_wellformed_one_disc_parent returns_result_select_result 
                        wellformed_h2)
            then show ?thesis
            proof(cases "document_ptr = x")
              case True
              then have "document_ptr \<noteq> y"
                using \<open>x \<noteq> y\<close> by auto
              have "set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}"
                using \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close> 
                by blast
              then show ?thesis 
                using 5 select_result_I2[OF disc_nodes_document_ptr_h'] 
                  select_result_I2[OF disc_nodes_document_ptr_h2]
                  select_result_I2[OF disc_nodes_old_document_h2] 
                  select_result_I2[OF disc_nodes_old_document_h3] 
                  \<open>old_document \<noteq> x\<close> \<open>old_document \<noteq> y\<close> \<open>document_ptr = x\<close> \<open>document_ptr \<noteq> y\<close>
                  \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2 
                  disconnected_nodes_eq2_h3
                  \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close>
                by(auto)
            next
              case False
              then show ?thesis
              proof(cases "document_ptr = y")
                case True
                have f1: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set disc_nodes_document_ptr_h3 = {}"
                  using 2 a1 document_ptr_in_heap document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3 
                        \<open>document_ptr \<noteq> x\<close> select_result_I2[OF disc_nodes_document_ptr_h3, symmetric] 
                        disconnected_nodes_eq2_h2[OF docs_neq[symmetric], symmetric]
                  by (simp add: "5" True)
                moreover have f1: 
                     "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = {}"
                  using 2 a1 old_document_in_heap document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3 
                       \<open>old_document \<noteq> x\<close>
                  by (metis (no_types, lifting) a0 distinct_concat_map_E(1) document_ptr_kinds_eq3_h2 
                         document_ptr_kinds_eq3_h3 finite_fset fmember.rep_eq set_sorted_list_of_set) 
                ultimately show ?thesis
                  using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                    select_result_I2[OF disc_nodes_old_document_h2] \<open>old_document \<noteq> x\<close>  
                    \<open>document_ptr \<noteq> x\<close> \<open>document_ptr = y\<close>
                    \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2 
                    disconnected_nodes_eq2_h3 
                  by auto
              next
                case False
                then show ?thesis
                  using 5 
                    select_result_I2[OF disc_nodes_old_document_h2] \<open>old_document \<noteq> x\<close> 
                    \<open>document_ptr \<noteq> x\<close> \<open>document_ptr \<noteq> y\<close>
                    \<open>child \<in> set disc_nodes_old_document_h2\<close> 
                    disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
                  by (metis \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close> 
                            empty_iff inf.idem) 
              qed
            qed
          qed
        qed
      qed
    next
      fix x xa xb
      assume 0: "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r) 
                                  (sorted_list_of_set (fset (object_ptr_kinds h')))))"
          and 1: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                   (sorted_list_of_set (fset (document_ptr_kinds h2)))))"
          and 2: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                    \<inter> (\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
          and 3: "xa |\<in>| object_ptr_kinds h'"
          and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
          and 5: "xb |\<in>| document_ptr_kinds h'"
          and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      then show False
        using \<open>child \<in> set disc_nodes_old_document_h2\<close> disc_nodes_document_ptr_h'
               disc_nodes_document_ptr_h2 disc_nodes_old_document_h2 disc_nodes_old_document_h3 
               disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq2_h2 
               document_ptr_kinds_eq2_h3  old_document_in_heap
        apply(auto)[1]
        apply(cases "xb = old_document")
      proof -
        assume a1: "xb = old_document"
        assume a2: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
        assume a3: "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 child disc_nodes_old_document_h2"
        assume a4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        assume "document_ptr_kinds h2 = document_ptr_kinds h'"
        assume a5: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) 
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        have f6: "old_document |\<in>| document_ptr_kinds h'"
          using a1 \<open>xb |\<in>| document_ptr_kinds h'\<close> by blast
        have f7: "|h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = disc_nodes_old_document_h2"
          using a2 by simp
        have "x \<in> set disc_nodes_old_document_h2"
          using f6 a3 a1 by (metis (no_types) \<open>type_wf h'\<close> \<open>x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r\<close> 
                disconnected_nodes_eq_h3 docs_neq get_disconnected_nodes_ok returns_result_eq
                returns_result_select_result set_remove1_subset subsetCE)
        then have "set |h' \<turnstile> get_child_nodes xa|\<^sub>r \<inter>  set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
          using f7 f6 a5 a4 \<open>xa |\<in>| object_ptr_kinds h'\<close>
          by fastforce 
        then show ?thesis
          using \<open>x \<in> set disc_nodes_old_document_h2\<close> a1 a4 f7 by blast
      next
        assume a1: "xb \<noteq> old_document"
        assume a2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3"
        assume a3: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
        assume a4: "xa |\<in>| object_ptr_kinds h'"
        assume a5: "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r child # disc_nodes_document_ptr_h3"
        assume a6: "old_document |\<in>| document_ptr_kinds h'"
        assume a7: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
        assume a8: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        assume a9: "document_ptr_kinds h2 = document_ptr_kinds h'"
        assume a10: "\<And>doc_ptr. old_document \<noteq> doc_ptr 
               \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a11: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr 
               \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a12: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) 
                    \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        have f13: "\<And>d. d \<notin> set |h' \<turnstile> document_ptr_kinds_M|\<^sub>r \<or> h2 \<turnstile> ok get_disconnected_nodes d"
          using a9 \<open>type_wf h2\<close> get_disconnected_nodes_ok
          by simp
        then have f14: "|h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = disc_nodes_old_document_h2"
          using a6 a3 by simp
        have "x \<notin> set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r"
          using a12 a8 a4 \<open>xb |\<in>| document_ptr_kinds h'\<close>
          by (meson UN_I disjoint_iff_not_equal fmember.rep_eq)
        then have "x = child"
          using f13 a11 a10 a7 a5 a2 a1
          by (metis (no_types, lifting) select_result_I2 set_ConsD) 
        then have "child \<notin> set disc_nodes_old_document_h2"
          using f14 a12 a8 a6 a4
          by (metis \<open>type_wf h'\<close> adopt_node_removes_child assms(1) assms(2) type_wf 
                    get_child_nodes_ok known_ptrs local.known_ptrs_known_ptr object_ptr_kinds_h2_eq3 
                    object_ptr_kinds_h3_eq3 object_ptr_kinds_h_eq3 returns_result_select_result)
        then show ?thesis
          using \<open>child \<in> set disc_nodes_old_document_h2\<close> by fastforce
      qed
    qed
    ultimately show ?thesis
      using \<open>type_wf h'\<close> \<open>a_owner_document_valid h'\<close> heap_is_wellformed_def by blast
  qed
qed

lemma adopt_node_node_in_disconnected_nodes:
  assumes wellformed: "heap_is_wellformed h"
    and adopt_node: "h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h'"
    and "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "node_ptr \<in> set disc_nodes"
proof -
  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt" and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent node_ptr | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h2" 
    and
    h': "h2 \<turnstile> (if owner_document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node_ptr old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (node_ptr # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h'"
    using assms(2)
    by(auto simp add: adopt_node_def elim!: bind_returns_heap_E 
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] 
                   pure_returns_heap_eq[rotated, OF get_parent_pure])

  show ?thesis
  proof (cases "owner_document = old_document")
    case True
    then show ?thesis
    proof (insert parent_opt h2, induct parent_opt)
      case None
      then have "h = h'"
        using h2 h' by(auto)
      then show ?case
        using in_disconnected_nodes_no_parent assms None old_document by blast
    next
      case (Some parent)
      then show ?case
        using remove_child_in_disconnected_nodes known_ptrs True h' assms(3) old_document by auto
    qed
  next
    case False
    then show ?thesis
      using assms(3)  h' list.set_intros(1) select_result_I2 set_disconnected_nodes_get_disconnected_nodes
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])[1]
    proof -
      fix x  and h'a and xb 
      assume a1: "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
      assume a2: "\<And>h document_ptr disc_nodes h'. h \<turnstile> set_disconnected_nodes document_ptr disc_nodes \<rightarrow>\<^sub>h h' 
                 \<Longrightarrow> h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
      assume "h'a \<turnstile> set_disconnected_nodes owner_document (node_ptr # xb) \<rightarrow>\<^sub>h h'"
      then have "node_ptr # xb = disc_nodes"
        using a2 a1 by (meson returns_result_eq)
      then show ?thesis
        by (meson list.set_intros(1))
    qed
  qed
qed
end

interpretation i_adopt_node_wf?: l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_owner_document get_parent get_parent_locs 
               remove_child remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs 
               set_disconnected_nodes set_disconnected_nodes_locs adopt_node adopt_node_locs known_ptr 
               type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes set_child_nodes_locs 
               remove heap_is_wellformed parent_child_rel
  by(simp add: l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

interpretation i_adopt_node_wf2?: l_adopt_node_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_owner_document get_parent get_parent_locs 
               remove_child remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs 
               set_disconnected_nodes set_disconnected_nodes_locs adopt_node adopt_node_locs known_ptr 
               type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes set_child_nodes_locs 
               remove heap_is_wellformed parent_child_rel get_root_node get_root_node_locs
  by(simp add: l_adopt_node_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


locale l_adopt_node_wf = l_heap_is_wellformed + l_known_ptrs + l_type_wf + l_adopt_node_defs 
                       + l_get_child_nodes_defs + l_get_disconnected_nodes_defs +
  assumes adopt_node_preserves_wellformedness:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> adopt_node document_ptr child \<rightarrow>\<^sub>h h' \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> type_wf h \<Longrightarrow> heap_is_wellformed h'"
  assumes adopt_node_removes_child:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h2 
                          \<Longrightarrow> h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> known_ptrs h 
                          \<Longrightarrow> type_wf h \<Longrightarrow> node_ptr \<notin> set children"
  assumes adopt_node_node_in_disconnected_nodes:
    "heap_is_wellformed h \<Longrightarrow> h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes 
                          \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow> node_ptr \<in> set disc_nodes"
  assumes adopt_node_removes_first_child: "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
                         \<Longrightarrow> h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h' 
                         \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r node # children 
                         \<Longrightarrow> h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"

lemma adopt_node_wf_is_l_adopt_node_wf [instances]: 
  "l_adopt_node_wf type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes
                   get_disconnected_nodes known_ptrs adopt_node"
  using heap_is_wellformed_is_l_heap_is_wellformed known_ptrs_is_l_known_ptrs
  apply(auto simp add: l_adopt_node_wf_def l_adopt_node_wf_axioms_def)[1]
  using adopt_node_preserves_wellformedness apply blast
  using adopt_node_removes_child apply blast
  using adopt_node_node_in_disconnected_nodes apply blast
  using adopt_node_removes_first_child apply blast
  done


subsection \<open>insert\_before\<close>

locale l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node_wf +
  l_set_disconnected_nodes_get_child_nodes +
  l_heap_is_wellformed
begin
lemma insert_before_removes_child:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "ptr \<noteq> ptr'"
  assumes "h \<turnstile> insert_before ptr node child \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r node # children"
  shows "h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
proof -
  obtain owner_document h2 h3 disc_nodes reference_child where
    "h \<turnstile> (if Some node = child then a_next_sibling node else return child) \<rightarrow>\<^sub>r reference_child" and
    "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document" and
    h2: "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h2" and
    "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes" and
    h3: "h2 \<turnstile> set_disconnected_nodes owner_document (remove1 node disc_nodes) \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> a_insert_node ptr node reference_child \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: insert_before_def a_ensure_pre_insertion_validity_def 
            elim!: bind_returns_heap_E bind_returns_result_E 
                   bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_ancestors_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated] 
                   bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] 
            split: if_splits option.splits)

  have "h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using h2 adopt_node_removes_first_child assms(1) assms(2) assms(3) assms(6)
    by simp
  then have "h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using h3
    by(auto simp add: set_disconnected_nodes_get_child_nodes 
            dest!: reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes])
  then show ?thesis
    using h' assms(4)
    apply(auto simp add: a_insert_node_def  
               elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated])[1]
    by(auto simp add: set_child_nodes_get_child_nodes_different_pointers 
            elim!: reads_writes_separate_forwards[OF get_child_nodes_reads set_child_nodes_writes])
qed
end

locale l_insert_before_wf = l_heap_is_wellformed_defs + l_type_wf + l_known_ptrs 
                          + l_insert_before_defs + l_get_child_nodes_defs +
assumes insert_before_removes_child: 
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> ptr \<noteq> ptr' 
                        \<Longrightarrow> h \<turnstile> insert_before ptr node child \<rightarrow>\<^sub>h h' 
                        \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r node # children 
                        \<Longrightarrow> h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"

interpretation i_insert_before_wf?: l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs 
                                    get_child_nodes get_child_nodes_locs set_child_nodes 
                                    set_child_nodes_locs get_ancestors get_ancestors_locs 
                                    adopt_node adopt_node_locs set_disconnected_nodes 
                                    set_disconnected_nodes_locs get_disconnected_nodes 
                                    get_disconnected_nodes_locs get_owner_document insert_before 
                                    insert_before_locs append_child type_wf known_ptr known_ptrs 
                                    heap_is_wellformed parent_child_rel
  by(simp add: l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma insert_before_wf_is_l_insert_before_wf [instances]: 
  "l_insert_before_wf heap_is_wellformed type_wf known_ptr known_ptrs insert_before get_child_nodes"
  apply(auto simp add: l_insert_before_wf_def l_insert_before_wf_axioms_def instances)[1]
  using insert_before_removes_child apply fast
  done

locale l_insert_before_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes_get_disconnected_nodes +
  l_remove_child +
  l_get_root_node_wf +
  l_set_disconnected_nodes_get_disconnected_nodes_wf +
  l_set_disconnected_nodes_get_ancestors +
  l_get_ancestors_wf +
  l_get_owner_document +
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma insert_before_heap_is_wellformed_preserved:
  assumes wellformed: "heap_is_wellformed h"
    and insert_before: "h \<turnstile> insert_before ptr node child \<rightarrow>\<^sub>h h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "heap_is_wellformed h'" and "type_wf h'" and "known_ptrs h'"
proof -
  obtain ancestors reference_child owner_document h2 h3 disconnected_nodes_h2 where
    ancestors: "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors" and
    node_not_in_ancestors: "cast node \<notin> set ancestors" and
    reference_child:
       "h \<turnstile> (if Some node = child then a_next_sibling node else return child) \<rightarrow>\<^sub>r reference_child" and
    owner_document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document" and
    h2: "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h2" and
    disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h2" and
    h3: "h2 \<turnstile> set_disconnected_nodes owner_document (remove1 node disconnected_nodes_h2) \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> a_insert_node ptr node reference_child \<rightarrow>\<^sub>h h'"
    using assms(2)
    by(auto simp add: insert_before_def a_ensure_pre_insertion_validity_def 
            elim!: bind_returns_heap_E bind_returns_result_E
                 bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_ancestors_pure, rotated]
                 bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
          split: if_splits option.splits)

  have "known_ptr ptr"
    by (meson get_owner_document_ptr_in_heap is_OK_returns_result_I known_ptrs 
              l_known_ptrs.known_ptrs_known_ptr l_known_ptrs_axioms owner_document)

  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF adopt_node_writes h2]
    using type_wf adopt_node_types_preserved
    by(auto simp add: a_remove_child_locs_def reflp_def transp_def)
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
    using  set_disconnected_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF insert_node_writes h']
    using set_child_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  have object_ptr_kinds_M_eq3_h: "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF adopt_node_writes h2])
    using adopt_node_pointers_preserved
    apply blast
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs )
  then have object_ptr_kinds_M_eq2_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have "known_ptrs h2"
    using known_ptrs object_ptr_kinds_M_eq3_h known_ptrs_preserved by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using adopt_node_preserves_wellformedness[OF wellformed h2] known_ptrs type_wf .

  have object_ptr_kinds_M_eq3_h2: "object_ptr_kinds h2 = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF set_disconnected_nodes_writes h3])  
    unfolding a_remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved 
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h2: "\<And>ptrs. h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_M_eq2_h2: "|h2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h2: "|h2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast
  have document_ptr_kinds_eq2_h2: "|h2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_M_eq2_h2 document_ptr_kinds_M_eq by auto

  have "known_ptrs h3"
    using object_ptr_kinds_M_eq3_h2 known_ptrs_preserved \<open>known_ptrs h2\<close> by blast
  
  have object_ptr_kinds_M_eq3_h': "object_ptr_kinds h3 = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", 
                                OF insert_node_writes h']) 
    unfolding a_remove_child_locs_def
    using set_child_nodes_pointers_preserved 
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h3: 
    "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_M_eq2_h3: 
    "|h3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h3: "|h3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast
  have document_ptr_kinds_eq2_h3: "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_M_eq2_h3 document_ptr_kinds_M_eq by auto

  show "known_ptrs h'"
    using object_ptr_kinds_M_eq3_h' known_ptrs_preserved \<open>known_ptrs h3\<close> by blast

  have disconnected_nodes_eq_h2: 
    "\<And>doc_ptr disc_nodes. owner_document \<noteq> doc_ptr 
      \<Longrightarrow> h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by (auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h2: 
     "\<And>doc_ptr. doc_ptr \<noteq> owner_document 
     \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_h3: 
   "h3 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r remove1 node disconnected_nodes_h2"
    using h3 set_disconnected_nodes_get_disconnected_nodes
    by blast

  have disconnected_nodes_eq_h3: 
    "\<And>doc_ptr disc_nodes. h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                        = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads insert_node_writes  h'
    apply(rule reads_writes_preserved)
    using set_child_nodes_get_disconnected_nodes by fast
  then have disconnected_nodes_eq2_h3: 
    "\<And>doc_ptr. |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2: 
     "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by (auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h2: 
     "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have children_eq_h3: 
    "\<And>ptr' children. ptr \<noteq> ptr' 
        \<Longrightarrow> h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads insert_node_writes h'
    apply(rule reads_writes_preserved)
    by (auto simp add: set_child_nodes_get_child_nodes_different_pointers)
  then have children_eq2_h3: 
     "\<And>ptr'. ptr \<noteq> ptr' \<Longrightarrow> |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  obtain children_h3 where children_h3: "h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h3"
    using h' a_insert_node_def by auto
  have children_h': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r insert_before_list node reference_child children_h3"
    using h' \<open>type_wf h3\<close> \<open>known_ptr ptr\<close>
    by(auto simp add: a_insert_node_def elim!: bind_returns_heap_E2 
            dest!: set_child_nodes_get_child_nodes returns_result_eq[OF children_h3])

  have ptr_in_heap: "ptr |\<in>| object_ptr_kinds h3"
    using children_h3 get_child_nodes_ptr_in_heap by blast
  have node_in_heap: "node |\<in>| node_ptr_kinds h"
    using h2 adopt_node_child_in_heap by fast
  have child_not_in_any_children: 
    "\<And>p children. h2 \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children \<Longrightarrow> node \<notin> set children"
    using wellformed h2 adopt_node_removes_child \<open>type_wf h\<close> \<open>known_ptrs h\<close> by auto
  have "node \<in> set disconnected_nodes_h2"
    using disconnected_nodes_h2 h2 adopt_node_node_in_disconnected_nodes assms(1) 
          \<open>type_wf h\<close> \<open>known_ptrs h\<close> by blast
  have node_not_in_disconnected_nodes: 
       "\<And>d. d |\<in>| document_ptr_kinds h3 \<Longrightarrow> node \<notin> set |h3 \<turnstile> get_disconnected_nodes d|\<^sub>r"
  proof -
    fix d
    assume "d |\<in>| document_ptr_kinds h3"
    show "node \<notin> set |h3 \<turnstile> get_disconnected_nodes d|\<^sub>r"
    proof (cases "d = owner_document")
      case True
      then show ?thesis
        using disconnected_nodes_h2 wellformed_h2 h3 remove_from_disconnected_nodes_removes 
              wellformed_h2 \<open>d |\<in>| document_ptr_kinds h3\<close> disconnected_nodes_h3 
        by fastforce
    next
      case False
      then have 
        "set |h2 \<turnstile> get_disconnected_nodes d|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes owner_document|\<^sub>r = {}"
        using distinct_concat_map_E(1) wellformed_h2
        by (metis (no_types, lifting) \<open>d |\<in>| document_ptr_kinds h3\<close> \<open>type_wf h2\<close> 
                  disconnected_nodes_h2 document_ptr_kinds_M_def document_ptr_kinds_eq2_h2 
                  l_ptr_kinds_M.ptr_kinds_ptr_kinds_M local.get_disconnected_nodes_ok 
                  local.heap_is_wellformed_one_disc_parent returns_result_select_result 
                  select_result_I2) 
      then show ?thesis
        using disconnected_nodes_eq2_h2[OF False] \<open>node \<in> set disconnected_nodes_h2\<close> 
              disconnected_nodes_h2 by fastforce
    qed
  qed

  have "cast node \<noteq> ptr"                         
    using ancestors node_not_in_ancestors get_ancestors_ptr
    by fast

  obtain ancestors_h2 where ancestors_h2: "h2 \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors_h2"
    using get_ancestors_ok object_ptr_kinds_M_eq2_h2 \<open>known_ptrs h2\<close> \<open>type_wf h2\<close>
    by (metis is_OK_returns_result_E object_ptr_kinds_M_eq3_h2 ptr_in_heap wellformed_h2)
  have ancestors_h3: "h3 \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors_h2"
    using get_ancestors_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_separate_forwards)
    using \<open>heap_is_wellformed h2\<close> ancestors_h2  
    by (auto simp add: set_disconnected_nodes_get_ancestors)
  have node_not_in_ancestors_h2: "cast node \<notin> set ancestors_h2"
    apply(rule get_ancestors_remains_not_in_ancestors[OF assms(1) wellformed_h2 ancestors ancestors_h2])
    using adopt_node_children_subset using h2 \<open>known_ptrs h\<close> \<open> type_wf h\<close> apply(blast)
    using node_not_in_ancestors apply(blast)
    using object_ptr_kinds_M_eq3_h apply(blast)
    using \<open>known_ptrs h\<close> apply(blast)
    using \<open>type_wf h\<close> apply(blast)
    using \<open>type_wf h2\<close> by blast

  moreover have "a_acyclic_heap h'"
  proof -
    have "acyclic (parent_child_rel h2)"
      using wellformed_h2  by (simp add: heap_is_wellformed_def acyclic_heap_def)
    then have "acyclic (parent_child_rel h3)"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_M_eq3_h2 children_eq2_h2)
    moreover have "cast node \<notin> {x. (x, ptr) \<in> (parent_child_rel h2)\<^sup>*}"
      using get_ancestors_parent_child_rel node_not_in_ancestors_h2 \<open>known_ptrs h2\<close> \<open>type_wf h2\<close>
      using ancestors_h2 wellformed_h2 by blast
    then have "cast node \<notin> {x. (x, ptr) \<in> (parent_child_rel h3)\<^sup>*}"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_M_eq3_h2 children_eq2_h2)
    moreover have "parent_child_rel h' = insert (ptr, cast node) ((parent_child_rel h3))"
      using  children_h3 children_h' ptr_in_heap
      apply(auto simp add: parent_child_rel_def object_ptr_kinds_M_eq3_h' children_eq2_h3  
                           insert_before_list_node_in_set)[1] 
      apply (metis (no_types, lifting) children_eq2_h3 insert_before_list_in_set select_result_I2)
      by (metis (no_types, lifting) children_eq2_h3 imageI insert_before_list_in_set select_result_I2)
    ultimately show ?thesis
      by(auto simp add: acyclic_heap_def)
  qed
    

  moreover have "a_all_ptrs_in_heap h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def)
  have "a_all_ptrs_in_heap h'"
  proof -
    have "a_all_ptrs_in_heap h3"
      using \<open>a_all_ptrs_in_heap h2\<close>
      apply(auto simp add: a_all_ptrs_in_heap_def object_ptr_kinds_M_eq2_h2 node_ptr_kinds_eq2_h2 
                           children_eq_h2)[1]
      using disconnected_nodes_eq2_h2 disconnected_nodes_h2 disconnected_nodes_h3
      using node_ptr_kinds_eq2_h2 apply auto[1]
      by (metis (no_types, lifting) NodeMonad.ptr_kinds_ptr_kinds_M disconnected_nodes_eq_h2 
                disconnected_nodes_h2 disconnected_nodes_h3 fset_mp fset_of_list_subset 
                node_ptr_kinds_eq2_h2 select_result_I2 set_remove1_subset) 
    have "set children_h3  \<subseteq> set |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using children_h3 \<open>a_all_ptrs_in_heap h3\<close> 
      apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq2_h3)[1]
      by (metis (no_types, hide_lams) fset_mp fset_of_list_elem node_ptr_kinds_commutes object_ptr_kinds_M_eq3_h')
    then have "set (insert_before_list node reference_child children_h3) \<subseteq> set |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_in_heap
      apply(auto simp add: node_ptr_kinds_eq2_h node_ptr_kinds_eq2_h2 node_ptr_kinds_eq2_h3)[1]
      by (metis (no_types, hide_lams) contra_subsetD finite_set_in insert_before_list_in_set 
                node_ptr_kinds_commutes object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h' 
                object_ptr_kinds_M_eq3_h2)
    then show ?thesis
      using \<open>a_all_ptrs_in_heap h3\<close>
      apply(auto simp add: object_ptr_kinds_M_eq3_h' a_all_ptrs_in_heap_def node_ptr_kinds_def 
                           node_ptr_kinds_eq2_h3 disconnected_nodes_eq_h3)[1]
      using children_eq_h3 children_h'
      by (metis (no_types, hide_lams) NodeMonad.ptr_kinds_ptr_kinds_M 
                \<open>set (insert_before_list node reference_child children_h3) \<subseteq> set |h' \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
                fset.map_comp fset_mp fset_of_list_elem node_ptr_kinds_def node_ptr_kinds_eq2_h3 
                returns_result_eq subsetCE)
  qed


  moreover have "a_distinct_lists h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h3"
  proof(auto simp add: a_distinct_lists_def object_ptr_kinds_M_eq2_h2 document_ptr_kinds_eq2_h2 
                       children_eq2_h2 intro!: distinct_concat_map_I)[1]
    fix x
    assume 1: "x |\<in>| document_ptr_kinds h3"
      and 2: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                        (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
    show "distinct |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using distinct_concat_map_E(2)[OF 2] select_result_I2[OF disconnected_nodes_h3] 
            disconnected_nodes_eq2_h2 select_result_I2[OF disconnected_nodes_h2] 1
      by (metis (full_types) distinct_remove1 finite_fset fmember.rep_eq set_sorted_list_of_set)
  next      
    fix x y xa
    assume 1: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                          (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and 2: "x |\<in>| document_ptr_kinds h3"
      and 3: "y |\<in>| document_ptr_kinds h3"
      and 4: "x \<noteq> y"
      and 5: "xa \<in> set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and 6: "xa \<in> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r"
    show False
    proof (cases "x = owner_document")
      case True
      then have "y \<noteq> owner_document"
        using 4 by simp
      show ?thesis 
        using distinct_concat_map_E(1)[OF 1]   
        using 2 3 4 5 6 select_result_I2[OF disconnected_nodes_h3]  select_result_I2[OF disconnected_nodes_h2]
        apply(auto simp add: True disconnected_nodes_eq2_h2[OF \<open>y \<noteq> owner_document\<close>])[1]
        by (metis (no_types, hide_lams) disconnected_nodes_eq2_h2 disjoint_iff_not_equal notin_set_remove1)
    next
      case False
      then show ?thesis
      proof (cases "y = owner_document")
        case True
        then show ?thesis 
        using distinct_concat_map_E(1)[OF 1]   
        using 2 3 4 5 6 select_result_I2[OF disconnected_nodes_h3]  select_result_I2[OF disconnected_nodes_h2]
        apply(auto simp add: True disconnected_nodes_eq2_h2[OF \<open>x \<noteq> owner_document\<close>])[1]
        by (metis (no_types, hide_lams) disconnected_nodes_eq2_h2 disjoint_iff_not_equal notin_set_remove1)
      next
        case False
        then show ?thesis 
          using distinct_concat_map_E(1)[OF 1, simplified, OF 2 3 4] 5 6
          using disconnected_nodes_eq2_h2 disconnected_nodes_h2 disconnected_nodes_h3 
               disjoint_iff_not_equal finite_fset fmember.rep_eq notin_set_remove1 select_result_I2 
                 set_sorted_list_of_set
          by (metis (no_types, lifting))
      qed
    qed
  next
    fix x xa xb
    assume 1: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h3 \<turnstile> get_child_nodes x|\<^sub>r)
                     \<inter> (\<Union>x\<in>fset (document_ptr_kinds h3). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 2: "xa |\<in>| object_ptr_kinds h3"
      and 3: "x \<in> set |h3 \<turnstile> get_child_nodes xa|\<^sub>r"
      and 4: "xb |\<in>| document_ptr_kinds h3"
      and 5: "x \<in> set |h3 \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    have 6: "set |h3 \<turnstile> get_child_nodes xa|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
      using 1 2 4
      by (metis \<open>type_wf h2\<close> children_eq2_h2 document_ptr_kinds_commutes known_ptrs 
                local.get_child_nodes_ok local.get_disconnected_nodes_ok 
                local.heap_is_wellformed_children_disc_nodes_different local.known_ptrs_known_ptr 
                object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h2 returns_result_select_result 
                wellformed_h2)
    show False
    proof (cases "xb = owner_document")
      case True
      then show ?thesis 
        using select_result_I2[OF disconnected_nodes_h3,folded select_result_I2[OF disconnected_nodes_h2]]
        by (metis (no_types, lifting) "3" "5" "6" disjoint_iff_not_equal notin_set_remove1)
    next
      case False
      show ?thesis
        using 2 3 4 5 6 unfolding disconnected_nodes_eq2_h2[OF False] by auto
    qed
  qed
  then have "a_distinct_lists h'"
  proof(auto simp add: a_distinct_lists_def document_ptr_kinds_eq2_h3 object_ptr_kinds_M_eq2_h3 
                       disconnected_nodes_eq2_h3 intro!: distinct_concat_map_I)[1]
    fix x
    assume 1: "distinct (concat (map (\<lambda>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r)
                                      (sorted_list_of_set (fset (object_ptr_kinds h')))))" and
           2: "x |\<in>| object_ptr_kinds h'"
    have 3: "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> distinct |h3 \<turnstile> get_child_nodes p|\<^sub>r"
      using 1  by (auto elim: distinct_concat_map_E)
    show "distinct |h' \<turnstile> get_child_nodes x|\<^sub>r"
    proof(cases "ptr = x")
      case True
      show ?thesis
        using 3[OF 2] children_h3 children_h' 
        by(auto simp add: True  insert_before_list_distinct 
                dest: child_not_in_any_children[unfolded children_eq_h2])
    next
      case False
      show ?thesis 
        using children_eq2_h3[OF False] 3[OF 2] by auto
    qed
  next
    fix x y xa
    assume 1: "distinct (concat (map (\<lambda>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r) 
                     (sorted_list_of_set (fset (object_ptr_kinds h')))))"
      and 2: "x |\<in>| object_ptr_kinds h'"
      and 3: "y |\<in>| object_ptr_kinds h'"
      and 4: "x \<noteq> y"
      and 5: "xa \<in> set |h' \<turnstile> get_child_nodes x|\<^sub>r"
      and 6: "xa \<in> set |h' \<turnstile> get_child_nodes y|\<^sub>r"
    have 7:"set |h3 \<turnstile> get_child_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_child_nodes y|\<^sub>r = {}"
      using distinct_concat_map_E(1)[OF 1] 2 3 4 by auto
    show False
    proof (cases "ptr = x")
      case True
      then have "ptr \<noteq> y"
        using 4 by simp
      then show ?thesis
        using  children_h3 children_h' child_not_in_any_children[unfolded children_eq_h2] 5 6
        apply(auto simp add:  True children_eq2_h3[OF \<open>ptr \<noteq> y\<close>])[1]
        by (metis (no_types, hide_lams) "3" "7" \<open>type_wf h3\<close> children_eq2_h3 disjoint_iff_not_equal 
                  get_child_nodes_ok insert_before_list_in_set known_ptrs local.known_ptrs_known_ptr 
                  object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h' 
                  object_ptr_kinds_M_eq3_h2 returns_result_select_result select_result_I2)
    next
      case False
      then show ?thesis
      proof (cases "ptr = y")
        case True
        then show ?thesis 
          using  children_h3 children_h' child_not_in_any_children[unfolded children_eq_h2] 5 6
          apply(auto simp add:  True children_eq2_h3[OF \<open>ptr \<noteq> x\<close>])[1]
          by (metis (no_types, hide_lams) "2" "4" "7" IntI \<open>known_ptrs h3\<close> \<open>type_wf h'\<close>
                     children_eq_h3 empty_iff insert_before_list_in_set local.get_child_nodes_ok
                     local.known_ptrs_known_ptr object_ptr_kinds_M_eq3_h'
                     returns_result_select_result select_result_I2)
        next
        case False
        then show ?thesis
          using children_eq2_h3[OF \<open>ptr \<noteq> x\<close>] children_eq2_h3[OF \<open>ptr \<noteq> y\<close>] 5 6 7 by auto
      qed
    qed
  next
    fix x xa xb
    assume 1: " (\<Union>x\<in>fset (object_ptr_kinds h'). set |h3 \<turnstile> get_child_nodes x|\<^sub>r) 
                  \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r) = {} "
      and 2: "xa |\<in>| object_ptr_kinds h'"
      and 3: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 4: "xb |\<in>| document_ptr_kinds h'"
      and 5: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    have 6: "set |h3 \<turnstile> get_child_nodes xa|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
      using 1 2 3 4 5
    proof -
      have "\<forall>h d. \<not> type_wf h \<or> d |\<notin>| document_ptr_kinds h \<or> h \<turnstile> ok get_disconnected_nodes d"
        using local.get_disconnected_nodes_ok by satx
      then have "h' \<turnstile> ok get_disconnected_nodes xb"
        using "4" \<open>type_wf h'\<close> by fastforce
      then have f1: "h3 \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
        by (simp add: disconnected_nodes_eq_h3)
      have "xa |\<in>| object_ptr_kinds h3"
        using "2" object_ptr_kinds_M_eq3_h' by blast 
      then show ?thesis
        using f1 \<open>local.a_distinct_lists h3\<close> local.distinct_lists_no_parent by fastforce
    qed
    show False
    proof (cases "ptr = xa")
      case True
      show ?thesis
        using 6 node_not_in_disconnected_nodes  3 4 5  select_result_I2[OF children_h'] 
              select_result_I2[OF children_h3] True disconnected_nodes_eq2_h3
        by (metis (no_types, lifting) "2" DocumentMonad.ptr_kinds_ptr_kinds_M 
                  \<open>a_distinct_lists h3\<close> \<open>type_wf h'\<close> disconnected_nodes_eq_h3 
                  distinct_lists_no_parent document_ptr_kinds_eq2_h3 get_disconnected_nodes_ok 
                  insert_before_list_in_set object_ptr_kinds_M_eq3_h' returns_result_select_result)

      next
      case False
      then show ?thesis
        using 1 2 3 4 5 children_eq2_h3[OF False] by fastforce 
    qed
  qed

  moreover have "a_owner_document_valid h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    apply(auto simp add: a_owner_document_valid_def object_ptr_kinds_M_eq2_h2
                         object_ptr_kinds_M_eq2_h3 node_ptr_kinds_eq2_h2 node_ptr_kinds_eq2_h3 
                         document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3 children_eq2_h2)[1]
    apply(auto simp add: document_ptr_kinds_eq2_h2[simplified]  document_ptr_kinds_eq2_h3[simplified] 
                         object_ptr_kinds_M_eq2_h2[simplified] object_ptr_kinds_M_eq2_h3[simplified] 
                         node_ptr_kinds_eq2_h2[simplified] node_ptr_kinds_eq2_h3[simplified])[1]
    apply(auto simp add: disconnected_nodes_eq2_h3[symmetric])[1]
  proof -
    fix node_ptr
    assume 0: "\<forall>node_ptr. node_ptr |\<in>| node_ptr_kinds h' 
               \<longrightarrow> (\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' 
                         \<and> node_ptr \<in> set |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                      \<or> (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h' 
                                          \<and> node_ptr \<in> set |h3 \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
      and 1: "node_ptr |\<in>| node_ptr_kinds h'"
      and 2: "\<forall>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h' 
                                          \<longrightarrow> node_ptr \<notin> set |h' \<turnstile> get_child_nodes parent_ptr|\<^sub>r"
    then have "(\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' 
                                   \<and> node_ptr \<in> set |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
      by (metis (no_types, lifting) children_eq2_h3 children_h' children_h3 
                                   insert_before_list_in_set select_result_I2)
    then show "\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' 
                                     \<and> node_ptr \<in> set |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
      by (metis (no_types, hide_lams) "2" children_h' disconnected_nodes_eq2_h2 
                                      disconnected_nodes_h2 disconnected_nodes_h3 in_set_remove1 
                                      insert_before_list_in_set object_ptr_kinds_M_eq3_h' 
                                      ptr_in_heap select_result_I2)
  qed

  ultimately show "heap_is_wellformed h'"
    by (simp add: heap_is_wellformed_def)
qed
end

locale l_insert_before_wf2 = l_type_wf + l_known_ptrs + l_insert_before_defs 
                           + l_heap_is_wellformed_defs + l_get_child_nodes_defs + l_remove_defs +
  assumes insert_before_preserves_type_wf: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> insert_before ptr child ref \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> type_wf h'"
  assumes insert_before_preserves_known_ptrs: 
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> insert_before ptr child ref \<rightarrow>\<^sub>h h' 
                          \<Longrightarrow> known_ptrs h'"
  assumes insert_before_heap_is_wellformed_preserved:
    "type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> heap_is_wellformed h \<Longrightarrow> h \<turnstile> insert_before ptr child ref \<rightarrow>\<^sub>h h'
               \<Longrightarrow> heap_is_wellformed h'"

interpretation i_insert_before_wf2?: l_insert_before_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs 
                                     get_child_nodes get_child_nodes_locs set_child_nodes 
                                     set_child_nodes_locs get_ancestors get_ancestors_locs 
                                     adopt_node adopt_node_locs set_disconnected_nodes 
                                     set_disconnected_nodes_locs get_disconnected_nodes 
                                     get_disconnected_nodes_locs get_owner_document insert_before 
                                     insert_before_locs append_child type_wf known_ptr known_ptrs 
                                     heap_is_wellformed parent_child_rel remove_child 
                                     remove_child_locs get_root_node get_root_node_locs
  by(simp add: l_insert_before_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_insert_before_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma insert_before_wf2_is_l_insert_before_wf2 [instances]: 
  "l_insert_before_wf2 type_wf known_ptr known_ptrs insert_before heap_is_wellformed"
  apply(auto simp add: l_insert_before_wf2_def l_insert_before_wf2_axioms_def instances)[1]
  using insert_before_heap_is_wellformed_preserved apply(fast, fast, fast)
  done

locale l_append_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M  +
  l_insert_before_wf2  +
  l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes
begin

lemma append_child_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
  assumes "h \<turnstile> append_child ptr node \<rightarrow>\<^sub>h h'"
  assumes "node \<notin> set xs"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ [node]"
proof -

  obtain ancestors owner_document h2 h3 disconnected_nodes_h2 where
    ancestors: "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors" and
    node_not_in_ancestors: "cast node \<notin> set ancestors" and
    owner_document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document" and
    h2: "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h2" and
    disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h2" and
    h3: "h2 \<turnstile> set_disconnected_nodes owner_document (remove1 node disconnected_nodes_h2) \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> a_insert_node ptr node None \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: append_child_def insert_before_def a_ensure_pre_insertion_validity_def 
            elim!: bind_returns_heap_E bind_returns_result_E
         bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_ancestors_pure, rotated]
                 bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated]
                 bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
          split: if_splits option.splits)

  have "\<And>parent. |h \<turnstile> get_parent node|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr"
    using assms(1) assms(4) assms(6)
    by (metis (no_types, lifting) assms(2) assms(3) h2 is_OK_returns_heap_I is_OK_returns_result_E 
              local.adopt_node_child_in_heap local.get_parent_child_dual local.get_parent_ok 
              select_result_I2)
  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    using get_child_nodes_reads adopt_node_writes h2 assms(4)
    apply(rule reads_writes_separate_forwards)
    using \<open>\<And>parent. |h \<turnstile> get_parent node|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>
    apply(auto simp add: adopt_node_locs_def remove_child_locs_def)[1]
    by (meson local.set_child_nodes_get_child_nodes_different_pointers)

  have "h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    using get_child_nodes_reads set_disconnected_nodes_writes h3 \<open>h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs\<close>
    apply(rule reads_writes_separate_forwards)
    by(auto)

  have "ptr |\<in>| object_ptr_kinds h"
    by (meson ancestors is_OK_returns_result_I local.get_ancestors_ptr_in_heap)
  then
  have "known_ptr ptr"
    using assms(3)
    using local.known_ptrs_known_ptr by blast

  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF adopt_node_writes h2]
    using adopt_node_types_preserved  \<open>type_wf h\<close>
    by(auto simp add: adopt_node_locs_def remove_child_locs_def reflp_def transp_def split: if_splits)
  then
  have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
    using  set_disconnected_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  show "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs@[node]"
    using h'  
    apply(auto simp add: a_insert_node_def 
               dest!: bind_returns_heap_E3[rotated, OF \<open>h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs\<close> 
                      get_child_nodes_pure, rotated])[1]
    using \<open>type_wf h3\<close> set_child_nodes_get_child_nodes \<open>known_ptr ptr\<close>
    by metis
qed

lemma append_child_for_all_on_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
  assumes "h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
  assumes "set nodes \<inter> set xs = {}"
  assumes "distinct nodes"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs@nodes"
  using assms
  apply(induct nodes arbitrary: h xs)
  apply(simp)
proof(auto elim!: bind_returns_heap_E)[1]fix a nodes h xs h'a
  assume 0: "(\<And>h xs. heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h 
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs \<Longrightarrow> h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h' 
              \<Longrightarrow> set nodes \<inter> set xs = {} \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ nodes)"
    and 1: "heap_is_wellformed h"
    and 2: "type_wf h"
    and 3: "known_ptrs h"
    and 4: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    and 5: "h \<turnstile> append_child ptr a \<rightarrow>\<^sub>r ()"
    and 6: "h \<turnstile> append_child ptr a \<rightarrow>\<^sub>h h'a"
    and 7: "h'a \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
    and 8: "a \<notin> set xs"
    and 9: "set nodes \<inter> set xs = {}"
    and 10: "a \<notin> set nodes"
    and 11: "distinct nodes"
  then have "h'a \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ [a]"
    using append_child_children 6
    using "1" "2" "3" "4" "8" by blast

  moreover have "heap_is_wellformed h'a" and "type_wf h'a" and "known_ptrs h'a"
    using insert_before_heap_is_wellformed_preserved insert_before_preserves_known_ptrs 
          insert_before_preserves_type_wf 1 2 3 6 append_child_def
    by metis+
  moreover have "set nodes \<inter> set (xs @ [a]) = {}"
    using 9 10
    by auto
  ultimately show "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ a # nodes"
    using 0 7
    by fastforce
qed


lemma append_child_for_all_on_no_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"
  assumes "h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
  assumes "distinct nodes"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r nodes"
  using assms append_child_for_all_on_children
  by force
end

interpretation i_append_child_wf?: l_append_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_owner_document get_parent 
                                   get_parent_locs remove_child remove_child_locs 
                                   get_disconnected_nodes get_disconnected_nodes_locs 
                                   set_disconnected_nodes set_disconnected_nodes_locs 
                                   adopt_node adopt_node_locs known_ptr type_wf get_child_nodes 
                                   get_child_nodes_locs known_ptrs set_child_nodes 
                                   set_child_nodes_locs remove get_ancestors get_ancestors_locs 
                                   insert_before insert_before_locs append_child heap_is_wellformed
                                   parent_child_rel
  by(auto simp add: l_append_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)



subsection \<open>create\_element\<close>

locale l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs 
                             get_disconnected_nodes get_disconnected_nodes_locs 
                             heap_is_wellformed parent_child_rel +
  l_new_element_get_disconnected_nodes get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_tag_type_get_disconnected_nodes type_wf set_tag_type set_tag_type_locs 
                             get_disconnected_nodes get_disconnected_nodes_locs +
  l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
                        set_disconnected_nodes_locs set_tag_type set_tag_type_locs create_element +
  l_new_element_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs +
  l_set_tag_type_get_child_nodes type_wf set_tag_type set_tag_type_locs known_ptr 
                          get_child_nodes get_child_nodes_locs +
  l_set_disconnected_nodes_get_child_nodes set_disconnected_nodes set_disconnected_nodes_locs 
                          get_child_nodes get_child_nodes_locs +
  l_set_disconnected_nodes type_wf set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_disconnected_nodes_get_disconnected_nodes  type_wf get_disconnected_nodes 
                   get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs +
  l_new_element type_wf +
  l_known_ptrs known_ptr known_ptrs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and set_tag_type :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_tag_type_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
begin
lemma create_element_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'"
proof -
  obtain new_element_ptr h2 h3 disc_nodes_h3 where
    new_element_ptr: "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr" and
    h2: "h \<turnstile> new_element \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_tag_type new_element_ptr tag \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(2) 
    by(auto simp add: create_element_def
            elim!: bind_returns_heap_E 
                   bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

  have "new_element_ptr \<notin> set |h \<turnstile> element_ptr_kinds_M|\<^sub>r"
    using new_element_ptr ElementMonad.ptr_kinds_ptr_kinds_M h2
    using new_element_ptr_not_in_heap by blast  
  then have "cast new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r"
    by simp
  then have "cast new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp

  have object_ptr_kinds_eq_h: "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    using new_element_new_ptr h2 new_element_ptr by blast
  then have node_ptr_kinds_eq_h: "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h |\<union>| {|new_element_ptr|}"
    apply(simp add: element_ptr_kinds_def)
    by force
  have character_data_ptr_kinds_eq_h: "character_data_ptr_kinds h2 = character_data_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def character_data_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", OF set_tag_type_writes h3])
    using set_tag_type_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2 
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", 
                                OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2 
          get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_element_ptr 
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_element[rotated, OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_element_ptr 
                                    \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr] 
          new_element_is_element_ptr[OF new_element_ptr] new_element_no_child_nodes
    by blast
  have disconnected_nodes_eq_h: 
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h2 get_disconnected_nodes_new_element[OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h: 
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2: 
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_tag_type_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_type_get_child_nodes)
  then have children_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2: 
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                               = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_tag_type_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_type_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2: 
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_element_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_tag_type_writes h3]
    using  set_tag_type_types_preserved  
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3: 
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3: 
    "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr 
       \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                               = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3: 
    "\<And>doc_ptr. document_ptr \<noteq> doc_ptr 
                \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  
  have disc_nodes_document_ptr_h2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h2 disc_nodes_h3 by auto
  then have disc_nodes_document_ptr_h: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h by auto
  then have "cast new_element_ptr \<notin> set disc_nodes_h3"
    using \<open>heap_is_wellformed h\<close> 
    using \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
          a_all_ptrs_in_heap_def heap_is_wellformed_def
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M fset_mp fset_of_list_elem )

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h2"
  proof(auto simp add: parent_child_rel_def)[1]
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h2"
      by (simp add: object_ptr_kinds_eq_h)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis ObjectMonad.ptr_kinds_ptr_kinds_M 
             \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h"
      using object_ptr_kinds_eq_h \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close>
      by(auto)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
      and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis (no_types, lifting) 
                               \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> 
                               children_eq2_h empty_iff empty_set image_eqI select_result_I2)
  qed
  also have "\<dots> = parent_child_rel h3"
    by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
  also have "\<dots> = parent_child_rel h'"
    by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
  finally have "a_acyclic_heap h'"
    by (simp add: acyclic_heap_def)

  have "a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def)[1]
    using node_ptr_kinds_eq_h 
          \<open>cast new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
          \<open>h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []\<close>
     apply (metis (no_types, hide_lams) children_eq_h fempty_iff fset_mp fset_of_list_simps(1) 
                  funionCI select_result_I2)
    by (simp add: disconnected_nodes_eq_h fset_rev_mp node_ptr_kinds_eq_h)
  then have "a_all_ptrs_in_heap h3"
    by(auto simp add: a_all_ptrs_in_heap_def object_ptr_kinds_eq_h2 node_ptr_kinds_def 
                      children_eq_h2 disconnected_nodes_eq_h2)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def object_ptr_kinds_eq_h3 node_ptr_kinds_def children_eq_h3 )[1]
    using disconnected_nodes_eq_h3 object_ptr_kinds_eq_h object_ptr_kinds_eq_h2
    by (metis (no_types, lifting) disc_nodes_h3 finsertCI fset.map_comp fset_mp fset_of_list_elem 
              funion_finsert_right h' local.set_disconnected_nodes_get_disconnected_nodes 
              node_ptr_kinds_def node_ptr_kinds_eq_h select_result_I2 set_ConsD)

  have "\<And>p. p |\<in>| object_ptr_kinds h \<Longrightarrow> cast new_element_ptr \<notin> set |h \<turnstile> get_child_nodes p|\<^sub>r"
    using \<open>heap_is_wellformed h\<close> \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
          heap_is_wellformed_children_in_heap
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M a_all_ptrs_in_heap_def assms(3) assms(4) fset_mp 
              fset_of_list_elem get_child_nodes_ok known_ptrs_known_ptr returns_result_select_result) 
  then have "\<And>p. p |\<in>| object_ptr_kinds h2 \<Longrightarrow> cast new_element_ptr \<notin> set |h2 \<turnstile> get_child_nodes p|\<^sub>r"
    using children_eq2_h
    apply(auto simp add: object_ptr_kinds_eq_h)[1]
    using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> apply auto[1]
    by (metis ObjectMonad.ptr_kinds_ptr_kinds_M 
              \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>)
  then have "\<And>p. p |\<in>| object_ptr_kinds h3 \<Longrightarrow> cast new_element_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h2 children_eq2_h2 by auto
  then have new_element_ptr_not_in_any_children: 
    "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> cast new_element_ptr \<notin> set |h' \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h3 children_eq2_h3 by auto

  have "a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h2"

    using \<open>h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []\<close>
    apply(auto simp add: a_distinct_lists_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h  
        disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
       apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)
      apply(case_tac "x=cast new_element_ptr")
       apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
      apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply (metis IntI assms(1) assms(3) assms(4) empty_iff local.get_child_nodes_ok 
        local.heap_is_wellformed_one_parent local.known_ptrs_known_ptr returns_result_select_result)
    apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
    by (metis \<open>local.a_distinct_lists h\<close> \<open>type_wf h2\<close> disconnected_nodes_eq_h document_ptr_kinds_eq_h 
        local.distinct_lists_no_parent local.get_disconnected_nodes_ok returns_result_select_result)
    
  then have "a_distinct_lists h3"
    by(auto simp add: a_distinct_lists_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2 
                      children_eq2_h2 object_ptr_kinds_eq_h2)
  then have "a_distinct_lists h'"
  proof(auto simp add: a_distinct_lists_def disconnected_nodes_eq2_h3 children_eq2_h3 
                       object_ptr_kinds_eq_h3 document_ptr_kinds_eq_h3 
             intro!: distinct_concat_map_I)[1]
    fix x
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                              (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
    then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using document_ptr_kinds_eq_h3 disconnected_nodes_eq_h3 h' set_disconnected_nodes_get_disconnected_nodes
      by (metis (no_types, lifting) \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set disc_nodes_h3\<close> 
                \<open>a_distinct_lists h3\<close> \<open>type_wf h'\<close> disc_nodes_h3 distinct.simps(2) 
                distinct_lists_disconnected_nodes get_disconnected_nodes_ok returns_result_eq 
                returns_result_select_result)
  next
    fix x y xa
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                            (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
      and "y |\<in>| document_ptr_kinds h3"
      and "x \<noteq> y"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    moreover have "set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
      using calculation by(auto dest: distinct_concat_map_E(1))
    ultimately show "False"
      apply(-)
      apply(cases "x = document_ptr")
       apply (metis (no_types) NodeMonad.ptr_kinds_ptr_kinds_M 
                    \<open>a_all_ptrs_in_heap h\<close> 
                    \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
                    a_all_ptrs_in_heap_def assms(3) disc_nodes_h3 disconnected_nodes_eq2_h 
                    disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 disjoint_iff_not_equal 
                    document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 fset_mp fset_of_list_elem 
                    get_disconnected_nodes_ok h' returns_result_select_result select_result_I2 
                    set_ConsD set_disconnected_nodes_get_disconnected_nodes)
      apply(cases "y = document_ptr" )
      apply (metis (no_types) NodeMonad.ptr_kinds_ptr_kinds_M 
                   \<open>a_all_ptrs_in_heap h\<close> 
                   \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
                   a_all_ptrs_in_heap_def assms(3) disc_nodes_h3 disconnected_nodes_eq2_h 
                   disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 disjoint_iff_not_equal 
                   document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 fset_mp fset_of_list_elem 
                   get_disconnected_nodes_ok h' returns_result_select_result select_result_I2 
                   set_ConsD set_disconnected_nodes_get_disconnected_nodes)
      using disconnected_nodes_eq2_h3 by auto
  next
    fix x xa xb
    assume 2: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h' \<turnstile> get_child_nodes x|\<^sub>r) 
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h3). set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 3: "xa |\<in>| object_ptr_kinds h3"
      and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 5: "xb |\<in>| document_ptr_kinds h3"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
     show "False"
      using disc_nodes_document_ptr_h disconnected_nodes_eq2_h3
      apply -
      apply(cases "xb = document_ptr")
       apply (metis (no_types, hide_lams) "3" "4" "6" 
                     \<open>\<And>p. p |\<in>| object_ptr_kinds h3 
                      \<Longrightarrow> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r\<close> 
                    \<open>a_distinct_lists h3\<close> children_eq2_h3 disc_nodes_h3 distinct_lists_no_parent h' 
                    select_result_I2 set_ConsD set_disconnected_nodes_get_disconnected_nodes)
      by (metis "3" "4" "5" "6" \<open>a_distinct_lists h3\<close> \<open>type_wf h3\<close> children_eq2_h3 
                distinct_lists_no_parent get_disconnected_nodes_ok returns_result_select_result)
  qed

  have "a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    using disc_nodes_h3 \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(auto simp add: a_owner_document_valid_def)[1]
    apply(auto simp add:  object_ptr_kinds_eq_h object_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: object_ptr_kinds_eq_h2)[1]
    apply(auto simp add:  document_ptr_kinds_eq_h document_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: document_ptr_kinds_eq_h2)[1]
    apply(auto simp add:  node_ptr_kinds_eq_h node_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h )[1]
     apply(auto simp add: children_eq2_h2[symmetric] children_eq2_h3[symmetric] 
        disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 
        disconnected_nodes_eq2_h3)[1]
     apply (metis (no_types, lifting) document_ptr_kinds_eq_h h' list.set_intros(1) 
        local.set_disconnected_nodes_get_disconnected_nodes select_result_I2) 
    apply(simp add: object_ptr_kinds_eq_h)
  proof -
    fix node_ptr :: "(_) node_ptr"
    assume a1: "\<forall>node_ptr. node_ptr |\<in>| node_ptr_kinds h \<longrightarrow> (\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) \<or> (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
    assume a2: "node_ptr |\<in>| node_ptr_kinds h"
    assume a3: "\<forall>parent_ptr. (parent_ptr = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<longrightarrow> node_ptr \<notin> set |h' \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr)|\<^sub>r) \<and> (parent_ptr |\<in>| object_ptr_kinds h \<longrightarrow> node_ptr \<notin> set |h' \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
    assume a4: "document_ptr |\<in>| document_ptr_kinds h"
    assume a5: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    obtain dd :: "(_) node_ptr \<Rightarrow> (_) document_ptr" where
      "\<forall>x0. (\<exists>v1. v1 |\<in>| document_ptr_kinds h \<and> x0 \<in> set |h \<turnstile> get_disconnected_nodes v1|\<^sub>r) = (dd x0 |\<in>| document_ptr_kinds h \<and> x0 \<in> set |h \<turnstile> get_disconnected_nodes (dd x0)|\<^sub>r)"
      by moura
    then have f6: "dd node_ptr |\<in>| document_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_disconnected_nodes (dd node_ptr)|\<^sub>r"
      using a3 a2 a1 by (metis (no_types) \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h children_eq2_h2 children_eq2_h3 l_ptr_kinds_M.ptr_kinds_ptr_kinds_M object_ptr_kinds_M_def)
    moreover
    { assume "|h \<turnstile> get_disconnected_nodes (dd node_ptr)|\<^sub>r \<noteq> disc_nodes_h3"
      then have "document_ptr \<noteq> dd node_ptr"
        using a5 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 by force
      then have "\<exists>d. d |\<in>| document_ptr_kinds h2 \<and> node_ptr \<in> set |h' \<turnstile> get_disconnected_nodes d|\<^sub>r"
        using f6 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h by auto }
    ultimately show "\<exists>d. d |\<in>| document_ptr_kinds h2 \<and> node_ptr \<in> set |h' \<turnstile> get_disconnected_nodes d|\<^sub>r"
      using a4 by (metis (no_types) document_ptr_kinds_eq_h h' insert_iff list.set(2) local.set_disconnected_nodes_get_disconnected_nodes select_result_I2)
  qed
  show "heap_is_wellformed h'"
    using \<open>a_acyclic_heap h'\<close> \<open>a_all_ptrs_in_heap h'\<close> \<open>a_distinct_lists h'\<close> \<open>a_owner_document_valid h'\<close>
    by(simp add: heap_is_wellformed_def)
qed
end

interpretation i_create_element_wf?: l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr known_ptrs type_wf 
                                     get_child_nodes get_child_nodes_locs get_disconnected_nodes 
                                     get_disconnected_nodes_locs heap_is_wellformed parent_child_rel 
                                     set_tag_type set_tag_type_locs
     set_disconnected_nodes set_disconnected_nodes_locs create_element
  using instances
  by(auto simp add: l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>create\_character\_data\<close>

locale l_create_character_data_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs get_disconnected_nodes 
    get_disconnected_nodes_locs heap_is_wellformed parent_child_rel
  + l_new_character_data_get_disconnected_nodes
    get_disconnected_nodes get_disconnected_nodes_locs
  + l_set_val_get_disconnected_nodes
    type_wf set_val set_val_locs get_disconnected_nodes get_disconnected_nodes_locs
  + l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    set_val set_val_locs get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
    set_disconnected_nodes_locs create_character_data
  + l_new_character_data_get_child_nodes
    type_wf known_ptr get_child_nodes get_child_nodes_locs
  + l_set_val_get_child_nodes
    type_wf set_val set_val_locs known_ptr get_child_nodes get_child_nodes_locs
  + l_set_disconnected_nodes_get_child_nodes
    set_disconnected_nodes set_disconnected_nodes_locs get_child_nodes get_child_nodes_locs
  + l_set_disconnected_nodes
    type_wf set_disconnected_nodes set_disconnected_nodes_locs
  + l_set_disconnected_nodes_get_disconnected_nodes
    type_wf get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes 
    set_disconnected_nodes_locs
  + l_new_character_data
    type_wf
  + l_known_ptrs
    known_ptr known_ptrs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: 
      "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_character_data :: 
      "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) character_data_ptr) prog"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
begin

lemma create_character_data_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'"
proof -
  obtain new_character_data_ptr h2 h3 disc_nodes_h3 where
    new_character_data_ptr: "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr" and
    h2: "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_val new_character_data_ptr text \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_character_data_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(2) 
    by(auto simp add: create_character_data_def 
            elim!: bind_returns_heap_E 
                   bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )


  have "new_character_data_ptr \<notin> set |h \<turnstile> character_data_ptr_kinds_M|\<^sub>r"
    using new_character_data_ptr CharacterDataMonad.ptr_kinds_ptr_kinds_M h2
    using new_character_data_ptr_not_in_heap by blast  
  then have "cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r"
    by simp
  then have "cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp



  have object_ptr_kinds_eq_h: 
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using new_character_data_new_ptr h2 new_character_data_ptr by blast
  then have node_ptr_kinds_eq_h: 
    "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h: 
    "character_data_ptr_kinds h2 = character_data_ptr_kinds h |\<union>| {|new_character_data_ptr|}"
    apply(simp add: character_data_ptr_kinds_def)
    by force
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", 
                                OF set_val_writes h3])
    using set_val_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2 
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", 
                                OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2 
          get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr 
                  \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: 
    "\<And>ptr'. ptr' \<noteq> cast new_character_data_ptr 
      \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have object_ptr_kinds_eq_h: 
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using new_character_data_new_ptr h2 new_character_data_ptr by blast
  then have node_ptr_kinds_eq_h: 
    "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h: 
    "character_data_ptr_kinds h2 = character_data_ptr_kinds h |\<union>| {|new_character_data_ptr|}"
    apply(simp add: character_data_ptr_kinds_def)
    by force
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", 
                               OF set_val_writes h3])
    using set_val_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2 
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", 
                                OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2 
          get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr 
                \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_character_data_ptr 
                                 \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []"
    using new_character_data_ptr h2 new_character_data_ptr_in_heap[OF h2 new_character_data_ptr] 
          new_character_data_is_character_data_ptr[OF new_character_data_ptr] 
          new_character_data_no_child_nodes
    by blast
  have disconnected_nodes_eq_h: 
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h2 
          get_disconnected_nodes_new_character_data[OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h: 
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2: 
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_child_nodes)
  then have children_eq2_h2: 
    "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2: 
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                                              = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2: 
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_character_data_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_val_writes h3]
    using  set_val_types_preserved  
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved  
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3: 
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3: 
    " \<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3: "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr 
    \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes 
                            = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr 
             \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  
  have disc_nodes_document_ptr_h2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h2 disc_nodes_h3 by auto
  then have disc_nodes_document_ptr_h: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h by auto
  then have "cast new_character_data_ptr \<notin> set disc_nodes_h3"
    using \<open>heap_is_wellformed h\<close> using \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
           a_all_ptrs_in_heap_def heap_is_wellformed_def
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M fset_mp fset_of_list_elem )

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h2"
  proof(auto simp add: parent_child_rel_def)[1]
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h2"
      by (simp add: object_ptr_kinds_eq_h)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis ObjectMonad.ptr_kinds_ptr_kinds_M 
                \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h"
      using object_ptr_kinds_eq_h \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
      by(auto)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
      and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis (no_types, lifting) \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close> 
                children_eq2_h empty_iff empty_set image_eqI select_result_I2)
  qed
  also have "\<dots> = parent_child_rel h3"
    by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
  also have "\<dots> = parent_child_rel h'"
    by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
  finally have "a_acyclic_heap h'"
    by (simp add: acyclic_heap_def)

  have "a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def)[1]
    using node_ptr_kinds_eq_h \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
          \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
     apply (metis (no_types, hide_lams) children_eq_h fempty_iff fset_mp fset_of_list_simps(1) 
                  funionCI select_result_I2)
    by (simp add: disconnected_nodes_eq_h fset_rev_mp node_ptr_kinds_eq_h)
  then have "a_all_ptrs_in_heap h3"
    by(auto simp add: a_all_ptrs_in_heap_def object_ptr_kinds_eq_h2 node_ptr_kinds_def 
                      children_eq_h2 disconnected_nodes_eq_h2)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def object_ptr_kinds_eq_h3 node_ptr_kinds_def 
                         children_eq_h3 )[1]
    using disconnected_nodes_eq_h3 object_ptr_kinds_eq_h object_ptr_kinds_eq_h2
    by (metis (no_types, lifting) disc_nodes_h3 finsertCI fset.map_comp fset_mp fset_of_list_elem 
              funion_finsert_right h' local.set_disconnected_nodes_get_disconnected_nodes 
              node_ptr_kinds_def node_ptr_kinds_eq_h select_result_I2 set_ConsD)

  have "\<And>p. p |\<in>| object_ptr_kinds h \<Longrightarrow> cast new_character_data_ptr \<notin> set |h \<turnstile> get_child_nodes p|\<^sub>r"
    using \<open>heap_is_wellformed h\<close> \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
          heap_is_wellformed_children_in_heap
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M a_all_ptrs_in_heap_def assms(3) assms(4) fset_mp 
      fset_of_list_elem get_child_nodes_ok known_ptrs_known_ptr returns_result_select_result) 
  then have "\<And>p. p |\<in>| object_ptr_kinds h2 \<Longrightarrow> cast new_character_data_ptr \<notin> set |h2 \<turnstile> get_child_nodes p|\<^sub>r"
    using children_eq2_h
    apply(auto simp add: object_ptr_kinds_eq_h)[1]
    using \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close> apply auto[1]
    by (metis ObjectMonad.ptr_kinds_ptr_kinds_M \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>)
  then have "\<And>p. p |\<in>| object_ptr_kinds h3 \<Longrightarrow> cast new_character_data_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h2 children_eq2_h2 by auto
  then have new_character_data_ptr_not_in_any_children: 
    "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> cast new_character_data_ptr \<notin> set |h' \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h3 children_eq2_h3 by auto

  have "a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h2"
    using \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
    apply(auto simp add: a_distinct_lists_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h  
        disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
       apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)
      apply(case_tac "x=cast new_character_data_ptr")
       apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
      apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply (metis IntI assms(1) assms(3) assms(4) empty_iff local.get_child_nodes_ok 
        local.heap_is_wellformed_one_parent local.known_ptrs_known_ptr 
        returns_result_select_result)
    apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
    by (metis \<open>local.a_distinct_lists h\<close> \<open>type_wf h2\<close> disconnected_nodes_eq_h document_ptr_kinds_eq_h 
        local.distinct_lists_no_parent local.get_disconnected_nodes_ok returns_result_select_result)
  then have "a_distinct_lists h3"
    by(auto simp add: a_distinct_lists_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2 
                      children_eq2_h2 object_ptr_kinds_eq_h2)[1]
  then have "a_distinct_lists h'"
  proof(auto simp add: a_distinct_lists_def disconnected_nodes_eq2_h3 children_eq2_h3 
                       object_ptr_kinds_eq_h3 document_ptr_kinds_eq_h3 intro!: distinct_concat_map_I)[1]
    fix x
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                      (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
    then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using document_ptr_kinds_eq_h3 disconnected_nodes_eq_h3 h' set_disconnected_nodes_get_disconnected_nodes
      by (metis (no_types, lifting) \<open>cast new_character_data_ptr \<notin> set disc_nodes_h3\<close> 
                \<open>a_distinct_lists h3\<close> \<open>type_wf h'\<close> disc_nodes_h3 distinct.simps(2) 
                distinct_lists_disconnected_nodes get_disconnected_nodes_ok returns_result_eq 
                returns_result_select_result)
  next
    fix x y xa
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                            (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
      and "y |\<in>| document_ptr_kinds h3"
      and "x \<noteq> y"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    moreover have "set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
      using calculation by(auto dest: distinct_concat_map_E(1))
    ultimately show "False"
      apply(cases "x = document_ptr")
       apply (metis (no_types) NodeMonad.ptr_kinds_ptr_kinds_M \<open>a_all_ptrs_in_heap h\<close> 
                                \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
                                a_all_ptrs_in_heap_def assms(3) disc_nodes_h3 
                                disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 
                                disconnected_nodes_eq2_h3 disjoint_iff_not_equal 
                                document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 fset_mp 
                                fset_of_list_elem get_disconnected_nodes_ok h' 
                                returns_result_select_result select_result_I2 set_ConsD 
                                set_disconnected_nodes_get_disconnected_nodes)
      apply(cases "y = document_ptr" )
      apply (metis (no_types) NodeMonad.ptr_kinds_ptr_kinds_M 
                   \<open>a_all_ptrs_in_heap h\<close> \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> 
                   a_all_ptrs_in_heap_def assms(3) disc_nodes_h3 disconnected_nodes_eq2_h 
                   disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 disjoint_iff_not_equal 
                   document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 fset_mp fset_of_list_elem 
                   get_disconnected_nodes_ok h' returns_result_select_result select_result_I2 set_ConsD 
                   set_disconnected_nodes_get_disconnected_nodes)
      using disconnected_nodes_eq2_h3 by auto
  next
    fix x xa xb
    assume 2: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h' \<turnstile> get_child_nodes x|\<^sub>r) 
                  \<inter> (\<Union>x\<in>fset (document_ptr_kinds h3). set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 3: "xa |\<in>| object_ptr_kinds h3"
      and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 5: "xb |\<in>| document_ptr_kinds h3"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    show "False"
      using disc_nodes_document_ptr_h disconnected_nodes_eq2_h3
      apply(cases "xb = document_ptr")
       apply (metis (no_types, hide_lams) "3" "4" "6"
                    \<open>\<And>p. p |\<in>| object_ptr_kinds h3 \<Longrightarrow> cast new_character_data_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r\<close> 
                    \<open>a_distinct_lists h3\<close> children_eq2_h3 disc_nodes_h3 distinct_lists_no_parent h'
                    select_result_I2 set_ConsD set_disconnected_nodes_get_disconnected_nodes)
      by (metis "3" "4" "5" "6" \<open>a_distinct_lists h3\<close> \<open>type_wf h3\<close> children_eq2_h3 
                distinct_lists_no_parent get_disconnected_nodes_ok returns_result_select_result)
  qed

  have "a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    using disc_nodes_h3 \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(simp add: a_owner_document_valid_def)
    apply(simp add: object_ptr_kinds_eq_h object_ptr_kinds_eq_h3 )
    apply(simp add: object_ptr_kinds_eq_h2)
    apply(simp add: document_ptr_kinds_eq_h document_ptr_kinds_eq_h3 )
    apply(simp add: document_ptr_kinds_eq_h2)
    apply(simp add: node_ptr_kinds_eq_h node_ptr_kinds_eq_h3 )
    apply(simp add: node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h )
    apply(auto simp add: children_eq2_h2[symmetric] children_eq2_h3[symmetric] disconnected_nodes_eq2_h 
                         disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3)[1]
     apply (metis (no_types, lifting) document_ptr_kinds_eq_h h' list.set_intros(1) 
                          local.set_disconnected_nodes_get_disconnected_nodes select_result_I2) 
    apply(simp add: object_ptr_kinds_eq_h)
    by (metis (no_types, lifting) ObjectMonad.ptr_kinds_ptr_kinds_M
                \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> 
                children_eq2_h disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h h' list.set_intros(2) 
                local.set_disconnected_nodes_get_disconnected_nodes select_result_I2)

  show "heap_is_wellformed h'"
    using \<open>a_acyclic_heap h'\<close> \<open>a_all_ptrs_in_heap h'\<close> \<open>a_distinct_lists h'\<close> \<open>a_owner_document_valid h'\<close>
    by(simp add: heap_is_wellformed_def)
qed
end

interpretation i_create_character_data_wf?: l_create_character_data_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf 
     get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs 
      heap_is_wellformed parent_child_rel set_val set_val_locs set_disconnected_nodes
     set_disconnected_nodes_locs create_character_data known_ptrs
  using instances
  by (auto simp add: l_create_character_data_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)


subsection \<open>create\_document\<close>

locale l_create_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    known_ptr type_wf get_child_nodes get_child_nodes_locs get_disconnected_nodes 
    get_disconnected_nodes_locs heap_is_wellformed parent_child_rel
  + l_new_document_get_disconnected_nodes
    get_disconnected_nodes get_disconnected_nodes_locs
  + l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
    create_document
  + l_new_document_get_child_nodes
    type_wf known_ptr get_child_nodes get_child_nodes_locs
 + l_new_document
    type_wf
  + l_known_ptrs
    known_ptr known_ptrs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_document :: "((_) heap, exception, (_) document_ptr) prog"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
begin

lemma create_document_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_document \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'"
proof -
  obtain new_document_ptr where
    new_document_ptr: "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr" and
    h': "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
    using assms(2) 
    apply(simp add: create_document_def)
    using new_document_ok by blast

  have "new_document_ptr \<notin> set |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using new_document_ptr DocumentMonad.ptr_kinds_ptr_kinds_M
    using new_document_ptr_not_in_heap h' by blast
  then have "cast new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp

  have "new_document_ptr |\<notin>| document_ptr_kinds h"
    using new_document_ptr DocumentMonad.ptr_kinds_ptr_kinds_M
    using new_document_ptr_not_in_heap h' by blast
  then have "cast new_document_ptr |\<notin>| object_ptr_kinds h"
    by simp

  have object_ptr_kinds_eq: "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_document_ptr|}"
    using new_document_new_ptr h' new_document_ptr by blast
  then have node_ptr_kinds_eq: "node_ptr_kinds h' = node_ptr_kinds h"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h: "character_data_ptr_kinds h' = character_data_ptr_kinds h"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h: "element_ptr_kinds h' = element_ptr_kinds h"
    using object_ptr_kinds_eq
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h' = document_ptr_kinds h |\<union>| {|new_document_ptr|}"
    using object_ptr_kinds_eq
    apply(auto simp add: document_ptr_kinds_def)[1]
    by (metis (no_types, lifting) document_ptr_kinds_commutes document_ptr_kinds_def finsertI1 fset.map_comp)


  have children_eq: 
     "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_document_ptr 
             \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h' get_child_nodes_new_document[rotated, OF new_document_ptr h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2: "\<And>ptr'. ptr' \<noteq> cast new_document_ptr 
                                    \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force


  have "h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []"
    using new_document_ptr h' new_document_ptr_in_heap[OF h' new_document_ptr] 
                   new_document_is_document_ptr[OF new_document_ptr] new_document_no_child_nodes
    by blast
  have disconnected_nodes_eq_h: 
    "\<And>doc_ptr disc_nodes. doc_ptr \<noteq> new_document_ptr 
    \<Longrightarrow> h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h' get_disconnected_nodes_new_document_different_pointers new_document_ptr
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1] 
    by (metis(full_types) \<open>\<And>thesis. (\<And>new_document_ptr. 
             \<lbrakk>h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr; h \<turnstile> new_document \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
             local.get_disconnected_nodes_new_document_different_pointers new_document_ptr)+
  then have disconnected_nodes_eq2_h: "\<And>doc_ptr. doc_ptr \<noteq> new_document_ptr 
                 \<Longrightarrow> |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have "h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"
    using h' local.new_document_no_disconnected_nodes new_document_ptr by blast

  have "type_wf h'"
    using \<open>type_wf h\<close> new_document_types_preserved h' by blast

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h'"
  proof(auto simp add: parent_child_rel_def)[1]
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h'"
      by (simp add: object_ptr_kinds_eq)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis ObjectMonad.ptr_kinds_ptr_kinds_M 
                \<open>cast new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h'"
        and 1: "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h"
      using object_ptr_kinds_eq \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close>
      by(auto)
  next                
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h'"
      and 1: "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis (no_types, lifting) \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close> 
                                        children_eq2 empty_iff empty_set image_eqI select_result_I2)
  qed
  finally have "a_acyclic_heap h'"
    by (simp add: acyclic_heap_def)

  have "a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def)[1]
     apply (metis ObjectMonad.ptr_kinds_ptr_kinds_M 
                  \<open>cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> 
                  \<open>parent_child_rel h = parent_child_rel h'\<close> assms(1) children_eq fset_of_list_elem 
                  local.heap_is_wellformed_children_in_heap local.parent_child_rel_child 
                  local.parent_child_rel_parent_in_heap node_ptr_kinds_eq)
    by (metis (no_types, lifting) ObjectMonad.ptr_kinds_ptr_kinds_M 
                  \<open>cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> 
                  \<open>h' \<turnstile> get_child_nodes (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr) \<rightarrow>\<^sub>r []\<close> 
                  \<open>parent_child_rel h = parent_child_rel h'\<close> assms(1) disconnected_nodes_eq_h
                  fset_of_list_elem h' local.heap_is_wellformed_disc_nodes_in_heap
                  local.new_document_no_disconnected_nodes local.parent_child_rel_child 
                  local.parent_child_rel_parent_in_heap new_document_ptr node_ptr_kinds_eq
                  select_result_I2)

  have "a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close> 
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h'"
    using \<open>h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []\<close> 
          \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close>

    apply(auto simp add: children_eq2[symmetric] a_distinct_lists_def insort_split object_ptr_kinds_eq 
                         document_ptr_kinds_eq_h  disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
    apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)

    apply(auto simp add:  dest: distinct_concat_map_E)[1]
    apply(auto simp add:  dest: distinct_concat_map_E)[1]
    using \<open>new_document_ptr |\<notin>| document_ptr_kinds h\<close>
    apply(auto simp add: distinct_insort dest: distinct_concat_map_E)[1]
    using disconnected_nodes_eq_h
    apply (metis assms(1) assms(3) disconnected_nodes_eq2_h local.get_disconnected_nodes_ok 
                          local.heap_is_wellformed_disconnected_nodes_distinct 
                          returns_result_select_result)
  proof -
    fix x :: "(_) document_ptr" and y :: "(_) document_ptr" and xa :: "(_) node_ptr"
    assume a1: "x \<noteq> y"
    assume a2: "x |\<in>| document_ptr_kinds h"
    assume a3: "x \<noteq> new_document_ptr"
    assume a4: "y |\<in>| document_ptr_kinds h"
    assume a5: "y \<noteq> new_document_ptr"
    assume a6: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
    assume a7: "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
    assume a8: "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    have f9: "xa \<in> set |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using a7 a3 disconnected_nodes_eq2_h by presburger
    have f10: "xa \<in> set |h \<turnstile> get_disconnected_nodes y|\<^sub>r"
      using a8 a5 disconnected_nodes_eq2_h by presburger
    have f11: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a4 by simp
    have "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a2 by simp
    then show False
      using f11 f10 f9 a6 a1 by (meson disjoint_iff_not_equal distinct_concat_map_E(1))
  next
    fix x xa xb
    assume 0: "h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"
      and 1: "h' \<turnstile> get_child_nodes (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr) \<rightarrow>\<^sub>r []"
      and 2: "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) 
                                                  (sorted_list_of_set (fset (object_ptr_kinds h)))))"
      and 3: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) 
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
      and 4: "(\<Union>x\<in>fset (object_ptr_kinds h). set |h \<turnstile> get_child_nodes x|\<^sub>r) 
                      \<inter> (\<Union>x\<in>fset (document_ptr_kinds h). set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 5: "x \<in> set |h \<turnstile> get_child_nodes xa|\<^sub>r"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      and 7: "xa |\<in>| object_ptr_kinds h"
      and 8: "xa \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr"
      and 9: "xb |\<in>| document_ptr_kinds h"
      and 10: "xb \<noteq> new_document_ptr"
    then show "False"

      by (metis \<open>local.a_distinct_lists h\<close> assms(3) disconnected_nodes_eq2_h 
                local.distinct_lists_no_parent local.get_disconnected_nodes_ok
                 returns_result_select_result)
  qed

  have "a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    apply(auto simp add: a_owner_document_valid_def)[1]
    by (metis \<open>cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr |\<notin>| object_ptr_kinds h\<close> 
              \<open>new_document_ptr |\<notin>| document_ptr_kinds h\<close> assms(3) assms(4) children_eq 
              children_eq2 disconnected_nodes_eq2_h disconnected_nodes_eq_h
              is_OK_returns_result_E is_OK_returns_result_I local.get_child_nodes_ok 
              local.get_child_nodes_ptr_in_heap local.get_disconnected_nodes_ok 
              local.get_disconnected_nodes_ptr_in_heap local.known_ptrs_known_ptr node_ptr_kinds_eq)
  
  show "heap_is_wellformed h'"
    using \<open>a_acyclic_heap h'\<close> \<open>a_all_ptrs_in_heap h'\<close> \<open>a_distinct_lists h'\<close> \<open>a_owner_document_valid h'\<close>
    by(simp add: heap_is_wellformed_def)
qed
end

interpretation i_create_document_wf?: l_create_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes 
                                      get_child_nodes_locs get_disconnected_nodes 
                                      get_disconnected_nodes_locs heap_is_wellformed parent_child_rel
                                      set_val set_val_locs set_disconnected_nodes 
                                      set_disconnected_nodes_locs create_document known_ptrs
  using instances
  by (auto simp add: l_create_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_create_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


end
