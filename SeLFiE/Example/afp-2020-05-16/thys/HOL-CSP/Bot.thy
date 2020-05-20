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

chapter\<open> The CSP Operators \<close>

section\<open>The Undefined Process\<close>

theory     Bot
imports    Process
begin 

definition Bot :: "'\<alpha> process"  
where     "Bot \<equiv> Abs_process ({(s,X). front_tickFree s}, {d. front_tickFree d})"

lemma is_process_REP_Bot : 
  "is_process  ({(s,X). front_tickFree s}, {d. front_tickFree d})"
by(auto simp: tickFree_implies_front_tickFree is_process_def 
              FAILURES_def DIVERGENCES_def
        elim: Process.front_tickFree_dw_closed 
        elim: Process.front_tickFree_append)


lemma Rep_Abs_Bot :"Rep_process (Abs_process ({(s,X). front_tickFree s},{d. front_tickFree d})) = 
                    ({(s,X). front_tickFree s},{d. front_tickFree d})"
by(subst Abs_process_inverse, simp_all only: CollectI Rep_process is_process_REP_Bot)

lemma F_Bot: "F Bot = {(s,X). front_tickFree s}"
by(simp add: Bot_def FAILURES_def F_def Rep_Abs_Bot)

lemma D_Bot: "D Bot = {d. front_tickFree d}"
by(simp add: Bot_def DIVERGENCES_def D_def Rep_Abs_Bot)

lemma T_Bot: "T Bot = {s. front_tickFree s}"
by(simp add: Bot_def TRACES_def T_def FAILURES_def Rep_Abs_Bot)

text\<open> This is the key result: @{term "\<bottom>"} --- which we know to exist 
from the process instantiation --- is equal Bot .
\<close>

lemma Bot_is_UU[simp]: "Bot = \<bottom>"
apply(auto simp: Pcpo.eq_bottom_iff Process.le_approx_def Ra_def 
                 min_elems_Collect_ftF_is_Nil Process.Nil_elem_T 
                 F_Bot D_Bot T_Bot
           elim: D_imp_front_tickFree)
apply(metis Process.is_processT2)
done

lemma F_UU: "F \<bottom> = {(s,X). front_tickFree s}"
  using F_Bot by auto

lemma D_UU: "D \<bottom> = {d. front_tickFree d}"
  using D_Bot by auto

lemma T_UU: "T \<bottom> = {s. front_tickFree s}"
  using T_Bot by auto


end

