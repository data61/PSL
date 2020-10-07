(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Design_OCL.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
 ******************************************************************************)

theory
  Design_OCL
imports
  Design_UML
begin
text \<open>\label{ex:employee-design:ocl}\<close>

section\<open>OCL Part: Invariant\<close>
text\<open>These recursive predicates can be defined conservatively
by greatest fix-point
constructions---automatically. See~\cite{brucker.ea:hol-ocl-book:2006,brucker:interactive:2007}
for details. For the purpose of this example, we state them as axioms
here.

\begin{ocl}
context Person
  inv label : self .boss <> null implies (self .salary  \<le>  ((self .boss) .salary))
\end{ocl}
\<close>

definition Person_label\<^sub>i\<^sub>n\<^sub>v :: "Person \<Rightarrow> Boolean" 
where     "Person_label\<^sub>i\<^sub>n\<^sub>v (self) \<equiv>  
                 (self .boss <> null implies (self .salary  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss) .salary)))"
                                       

definition Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e :: "Person \<Rightarrow> Boolean" 
where     "Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e (self) \<equiv>  
                 (self .boss@pre <> null implies (self .salary@pre \<le>\<^sub>i\<^sub>n\<^sub>t ((self .boss@pre) .salary@pre)))"

definition Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v :: "Boolean"
where     "Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v \<equiv> (Person .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(x | Person_label\<^sub>i\<^sub>n\<^sub>v (x)) and 
                                  (Person .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(x | Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e (x))))"
                                  
                                  
lemma "\<tau> \<Turnstile> \<delta> (X .boss) \<Longrightarrow> \<tau> \<Turnstile> Person .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(X .boss) \<and>
                            \<tau> \<Turnstile> Person .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(X) "
oops  
(* To be generated generically ... hard, but crucial lemma that should hold. 
   It means that X and it successor are object representation that actually
   occur in the state. *)

lemma REC_pre : "\<tau> \<Turnstile> Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v 
       \<Longrightarrow> \<tau> \<Turnstile> Person .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(X) \<comment> \<open>\<open>X\<close> represented object in state\<close>
       \<Longrightarrow> \<exists> REC.  \<tau> \<Turnstile> REC(X)  \<triangleq> (Person_label\<^sub>i\<^sub>n\<^sub>v (X) and (X .boss <> null implies REC(X .boss)))"
oops (* Attempt to allegiate the burden of he following axiomatizations: could be
        a witness for a constant specification ...*)       

text\<open>This allows to state a predicate:\<close>
                                       
axiomatization inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l :: "Person \<Rightarrow> Boolean"
where inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l_def:
"(\<tau> \<Turnstile> Person .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(self)) \<Longrightarrow> 
 (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self) \<triangleq>  (self .boss <> null implies  
                                  (self .salary  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss) .salary)) and
                                   inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self .boss))))"

axiomatization inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e :: "Person \<Rightarrow> Boolean"
where inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e_def: 
"(\<tau> \<Turnstile> Person .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(self)) \<Longrightarrow>
 (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self) \<triangleq> (self .boss@pre <> null implies 
                                   (self .salary@pre  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss@pre) .salary@pre)) and
                                    inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self .boss@pre))))"


lemma inv_1 : 
"(\<tau> \<Turnstile> Person .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(self)) \<Longrightarrow>
    (\<tau> \<Turnstile> inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self) = ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or>
                               ( \<tau> \<Turnstile> (self .boss <> null) \<and> 
                                 \<tau> \<Turnstile> ((self .salary)  \<le>\<^sub>i\<^sub>n\<^sub>t  (self .boss .salary))  \<and>
                                 \<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self .boss))))) "
oops (* Let's hope that this holds ... *)


lemma inv_2 : 
"(\<tau> \<Turnstile> Person .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(self)) \<Longrightarrow>
    (\<tau> \<Turnstile> inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self)) =  ((\<tau> \<Turnstile> (self .boss@pre \<doteq> null)) \<or>
                                     (\<tau> \<Turnstile> (self .boss@pre <> null) \<and>
                                     (\<tau> \<Turnstile> (self .boss@pre .salary@pre \<le>\<^sub>i\<^sub>n\<^sub>t self .salary@pre))  \<and>
                                     (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self .boss@pre)))))"
oops (* Let's hope that this holds ... *)

text\<open>A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!)\<close>
coinductive inv :: "Person \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or>
                      (\<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> (self .boss .salary \<le>\<^sub>i\<^sub>n\<^sub>t self .salary))  \<and>
                     ( (inv(self .boss))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section\<open>OCL Part: The Contract of a Recursive Query\<close>
text\<open>This part is analogous to the Analysis Model and skipped here.\<close>


end
