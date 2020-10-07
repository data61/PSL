(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

theory Assertions
  imports CSP
begin

section\<open>CSP Assertions\<close>

definition trace_refine :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>T" 60)
  where "P \<sqsubseteq>\<^sub>T Q \<equiv> T Q \<subseteq> T P"

definition failure_refine :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>F" 60)
  where "P \<sqsubseteq>\<^sub>F Q \<equiv> F Q \<subseteq> F P"

definition failure_divergence_refine :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>F\<^sub>D" 60)
  where "P \<sqsubseteq>\<^sub>F\<^sub>D Q \<equiv> P \<le> Q"
text\<open>Note that this just another syntax to our standard process refinement order 
     defined in the theory Process. \<close> 

definition DF :: "'a set \<Rightarrow> 'a process"
  where   "DF A \<equiv> \<mu> X. \<sqinter> x \<in> A \<rightarrow> X"

lemma DF_unfold : "DF A = (\<sqinter> z \<in> A \<rightarrow> DF A)"
 by(simp add: DF_def, rule trans, rule fix_eq, simp)

definition deadlock_free :: "'a process \<Rightarrow> bool"
  where   "deadlock_free P \<equiv> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

definition DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a set \<Rightarrow> 'a process"
  where   "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. ((\<sqinter> x \<in> A \<rightarrow> X) \<sqinter> SKIP)"

definition RUN :: "'a set \<Rightarrow> 'a process"
  where   "RUN A \<equiv> \<mu> X. \<box> x \<in> A \<rightarrow> X"

definition CHAOS :: "'a set \<Rightarrow> 'a process" 
  where   "CHAOS A \<equiv> \<mu> X. (STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"

definition lifelock_free :: "'a process \<Rightarrow> bool"
  where   "lifelock_free P \<equiv> CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

section\<open>Some deadlock freeness laws\<close>

lemma DF_subset: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> DF B \<sqsubseteq>\<^sub>F\<^sub>D DF A" 
  apply(subst DF_def, unfold failure_divergence_refine_def, rule fix_ind) 
    apply(rule le_adm, simp_all add:monofunI, subst DF_unfold)
  by (metis mndet_FD_subset mono_mndet_FD order.trans)

lemma DF_Univ_freeness: "A \<noteq> {} \<Longrightarrow> (DF A) \<sqsubseteq>\<^sub>F\<^sub>D P  \<Longrightarrow> deadlock_free P"
  by (meson deadlock_free_def DF_subset failure_divergence_refine_def order.trans subset_UNIV)

lemma deadlock_free_ndet: "deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow> deadlock_free (P \<sqinter> Q)"
  by (simp add: D_ndet F_ndet deadlock_free_def failure_divergence_refine_def le_ref_def)

lemma deadlock_free_skip:"DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV  \<sqsubseteq>\<^sub>F\<^sub>D SKIP"
  by(simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def failure_divergence_refine_def, rule fix_ind, simp_all)

end