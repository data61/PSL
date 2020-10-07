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

section\<open>The SKIP Process\<close>

theory Skip 
imports Process
begin

definition SKIP :: "'a process"
where     "SKIP \<equiv> Abs_process ({(s, X). s = [] \<and> tick \<notin> X} \<union> {(s, X). s = [tick]}, {})"

lemma is_process_REP_Skip:
" is_process ({(s, X). s = [] \<and> tick \<notin> X} \<union> {(s, X). s = [tick]}, {})"
apply(auto simp: FAILURES_def DIVERGENCES_def front_tickFree_def is_process_def)
apply(erule contrapos_np,drule neq_Nil_conv[THEN iffD1], auto)
done

lemma is_process_REP_Skip2:
"is_process ({[]} \<times> {X. tick \<notin> X} \<union> {(s, X). s = [tick]}, {})"
using is_process_REP_Skip by auto


lemmas process_prover = Rep_process Abs_process_inverse 
	                       FAILURES_def TRACES_def 
	                       DIVERGENCES_def is_process_REP_Skip

lemma F_SKIP:
"F SKIP = {(s, X). s = [] \<and> tick \<notin> X} \<union> {(s, X). s = [tick]}"
by(simp add:  process_prover SKIP_def F_def is_process_REP_Skip2)

lemma D_SKIP: "D SKIP = {}"
by(simp add:  process_prover SKIP_def D_def is_process_REP_Skip2)

lemma T_SKIP: "T SKIP ={[],[tick]}"
by(auto simp:  process_prover SKIP_def T_def is_process_REP_Skip2)


end
