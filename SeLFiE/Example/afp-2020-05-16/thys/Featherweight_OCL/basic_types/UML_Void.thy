(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Void.thy --- Library definitions.
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

theory  UML_Void
imports "../UML_PropertyProfiles"
begin

section\<open>Basic Type Void: Operations\<close>

(* For technical reasons, the type does not contain to the null-class yet. *)
text \<open>This \emph{minimal} OCL type contains only two elements:
@{term "invalid"} and @{term "null"}.
@{term "Void"} could initially be defined as @{typ "unit option option"},
however the cardinal of this type is more than two, so it would have the cost to consider
 \<open>Some None\<close> and \<open>Some (Some ())\<close> seemingly everywhere.\<close>
 
subsection\<open>Fundamental Properties on Voids: Strict Equality\<close>

subsubsection\<open>Definition\<close>

instantiation   Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: bot
begin
   definition bot_Void_def: "(bot_class.bot :: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"

   instance proof show "\<exists>x:: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e. x \<noteq> bot"
                  apply(rule_tac x="Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Void_def, subst Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: null_option_def bot_option_def)
                  done
            qed
end

instantiation   Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e :: null
begin
   definition null_Void_def: "(null::Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<equiv> Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor> None \<rfloor>"

   instance proof show "(null:: Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<noteq> bot"
                  apply(simp add:null_Void_def bot_Void_def, subst Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
                  apply(simp_all add: null_option_def bot_option_def)
                  done
            qed
end


text\<open>The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Void"}-case as strict extension of the strong equality:\<close>
overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>)Void,('\<AA>)Void] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d[code_unfold] :
    "(x::('\<AA>)Void) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                               then (x \<triangleq> y) \<tau>
                               else invalid \<tau>"
end

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation   StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>)Void) \<doteq> y" 
       by unfold_locales (auto simp:  StrictRefEq\<^sub>V\<^sub>o\<^sub>i\<^sub>d)
 
                                    
subsection\<open>Basic Void Constants\<close>


subsection\<open>Validity and Definedness Properties\<close>

lemma  "\<delta>(null::('\<AA>)Void) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)Void) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e None) = false"
apply(simp add:defined_def true_def
               bot_fun_def bot_option_def)
apply(rule ext, simp split:, intro conjI impI)
by(simp add: bot_Void_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e None) = false"
apply(simp add:valid_def true_def
               bot_fun_def bot_option_def)
apply(rule ext, simp split:, intro conjI impI)
by(simp add: bot_Void_def)

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) = false"
apply(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)
apply(rule ext, simp split:, intro conjI impI)
by(simp add: null_Void_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) = true"
apply(simp add:valid_def true_def
               bot_fun_def bot_option_def)
apply(rule ext, simp split:, intro conjI impI)
by(metis null_Void_def null_is_valid, simp add: true_def)


subsection\<open>Test Statements\<close>

Assert "\<tau> \<Turnstile> ((null::('\<AA>)Void)  \<doteq> null)"


end
