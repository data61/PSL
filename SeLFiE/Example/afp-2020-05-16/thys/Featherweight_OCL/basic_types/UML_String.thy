(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_String.thy --- Library definitions.
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

theory  UML_String
imports "../UML_PropertyProfiles"
begin

section\<open>Basic Type String: Operations\<close>

subsection\<open>Fundamental Properties on Strings: Strict Equality \label{sec:string-strict-eq}\<close>

text\<open>The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Boolean"}-case as strict extension of the strong equality:\<close>
overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>)String,('\<AA>)String] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g[code_unfold] :
    "(x::('\<AA>)String) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y) \<tau>
                                  else invalid \<tau>"
end

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>)String) \<doteq> y" 
         by unfold_locales (auto simp: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g)
 
subsection\<open>Basic String Constants\<close>

text\<open>Although the remaining part of this library reasons about
integers abstractly, we provide here as example some convenient shortcuts.\<close>

definition OclStringa ::"('\<AA>)String" ("\<a>")    where      "\<a> = (\<lambda> _ . \<lfloor>\<lfloor>''a''\<rfloor>\<rfloor>)"
definition OclStringb ::"('\<AA>)String" ("\<b>")    where      "\<b> = (\<lambda> _ . \<lfloor>\<lfloor>''b''\<rfloor>\<rfloor>)"
definition OclStringc ::"('\<AA>)String" ("\<c>")    where      "\<c> = (\<lambda> _ . \<lfloor>\<lfloor>''c''\<rfloor>\<rfloor>)"
text\<open>Etc.\<close>
text_raw\<open>\isatagafp\<close>

subsection\<open>Validity and Definedness Properties\<close>

lemma  "\<delta>(null::('\<AA>)String) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)String) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> \<a> = true" by(simp add:OclStringa_def)
lemma [simp,code_unfold]: "\<upsilon> \<a> = true" by(simp add:OclStringa_def)
text_raw\<open>\endisatagafp\<close>

subsection\<open>String Operations\<close>

subsubsection\<open>Definition\<close>
text\<open>Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot).\<close>
text\<open>Note that we can not follow the lexis of the OCL Standard for Isabelle
technical reasons; these operators are heavily overloaded in the HOL library
that a further overloading would lead to heavy technical buzz in this
document.
\<close>
definition OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ::"('\<AA>)String \<Rightarrow> ('\<AA>)String \<Rightarrow> ('\<AA>)String" (infix "+\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" 40)
where "x +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>concat [\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>, \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>]\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g : profile_bin\<^sub>d_\<^sub>d "(+\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g)" "\<lambda> x y. \<lfloor>\<lfloor>concat [\<lceil>\<lceil>x\<rceil>\<rceil>, \<lceil>\<lceil>y\<rceil>\<rceil>]\<rfloor>\<rfloor>"
         by unfold_locales (auto simp:OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def bot_option_def null_option_def)
         
(* TODO : size(), concat, substring(s:string) toInteger, toReal, at(i:Integer), characters() etc. *)


subsubsection\<open>Basic Properties\<close>

lemma OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_not_commute: "\<exists>X Y. (X +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g Y) \<noteq> (Y +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g X)"
  apply(rule_tac x = "\<lambda>_. \<lfloor>\<lfloor>''b''\<rfloor>\<rfloor>" in exI)
  apply(rule_tac x = "\<lambda>_. \<lfloor>\<lfloor>''a''\<rfloor>\<rfloor>" in exI)
  apply(simp_all add:OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def)
  by(auto, drule fun_cong, auto)


subsection\<open>Test Statements\<close>
text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>
(*
Assert "\<tau> \<Turnstile> ( \<nine> \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> )"
Assert "\<tau> \<Turnstile> (( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<four> ) \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> )"
Assert "\<tau> |\<noteq> (( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<four> )) <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> )"
Assert "\<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>)) "
*)

text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>


text\<open>Elementary computations on String\<close>

Assert "\<tau> \<Turnstile> \<a> <> \<b>"
Assert "\<tau> \<Turnstile> \<b> <> \<a>"
Assert "\<tau> \<Turnstile> \<b> \<doteq> \<b>"

Assert "\<tau> \<Turnstile> \<upsilon> \<a>"
Assert "\<tau> \<Turnstile> \<delta> \<a>"
Assert "\<tau> \<Turnstile> \<upsilon> (null::('\<AA>)String)"
Assert "\<tau> \<Turnstile> (invalid \<triangleq> invalid)"
Assert "\<tau> \<Turnstile> (null \<triangleq> null)"
Assert "\<tau> \<Turnstile> (\<a> \<triangleq> \<a>)"
Assert "\<tau> |\<noteq> (\<a> \<triangleq> \<b>)"
Assert "\<tau> |\<noteq> (invalid \<triangleq> \<b>)"
Assert "\<tau> |\<noteq> (null \<triangleq> \<b>)"
Assert "\<tau> |\<noteq> (invalid \<doteq> (invalid::('\<AA>)String))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)String))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> (invalid <> (invalid::('\<AA>)String))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid <> (invalid::('\<AA>)String))" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)String) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)String) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (\<b> \<doteq> \<b>)"
Assert "\<tau> |\<noteq> (\<b> <> \<b>)"
Assert "\<tau> |\<noteq> (\<b> \<doteq> \<c>)"
Assert "\<tau> \<Turnstile> (\<b> <> \<c>)"
(*Assert "\<tau> |\<noteq> (\<zero> <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g null)"
Assert "\<tau> |\<noteq> (\<delta> (\<zero> <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g null))"
*)

end
