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

section\<open> The STOP Process \<close>

theory     Stop
imports    Process 
begin 

definition STOP :: "'\<alpha> process"  
where     "STOP \<equiv> Abs_process ({(s, X). s = []}, {})"

lemma is_process_REP_STOP: "is_process ({(s, X). s = []},{})"
by(simp add: is_process_def FAILURES_def DIVERGENCES_def)

lemma Rep_Abs_STOP : "Rep_process (Abs_process ({(s, X). s = []},{})) = ({(s, X). s = []},{})"
by(subst Abs_process_inverse, simp add: Rep_process is_process_REP_STOP, auto)

lemma F_STOP : "F STOP = {(s,X). s = []}"
by(simp add: STOP_def FAILURES_def F_def Rep_Abs_STOP)

lemma D_STOP: "D STOP = {}"
by(simp add: STOP_def DIVERGENCES_def D_def Rep_Abs_STOP)

lemma T_STOP: "T STOP = {[]}"
by(simp add: STOP_def TRACES_def FAILURES_def T_def Rep_Abs_STOP)

end

