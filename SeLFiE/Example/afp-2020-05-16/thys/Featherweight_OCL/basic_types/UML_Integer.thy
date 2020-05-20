(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Integer.thy --- Library definitions.
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

theory  UML_Integer
imports "../UML_PropertyProfiles"
begin

section\<open>Basic Type Integer: Operations\<close>

subsection\<open>Fundamental Predicates on Integers: Strict Equality \label{sec:integer-strict-eq}\<close>

text\<open>The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Boolean"}-case as strict extension of the strong equality:\<close>
overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>)Integer,('\<AA>)Integer] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[code_unfold] :
    "(x::('\<AA>)Integer) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y) \<tau>
                                  else invalid \<tau>"
end

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>)Integer) \<doteq> y" 
         by unfold_locales (auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r)

subsection\<open>Basic Integer Constants\<close>

text\<open>Although the remaining part of this library reasons about
integers abstractly, we provide here as example some convenient shortcuts.\<close>

definition OclInt0 ::"('\<AA>)Integer" ("\<zero>")  where      "\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>0::int\<rfloor>\<rfloor>)"
definition OclInt1 ::"('\<AA>)Integer" ("\<one>")  where      "\<one> = (\<lambda> _ . \<lfloor>\<lfloor>1::int\<rfloor>\<rfloor>)"
definition OclInt2 ::"('\<AA>)Integer" ("\<two>")  where      "\<two> = (\<lambda> _ . \<lfloor>\<lfloor>2::int\<rfloor>\<rfloor>)"
text\<open>Etc.\<close>
text_raw\<open>\isatagafp\<close>
definition OclInt3 ::"('\<AA>)Integer" ("\<three>")  where      "\<three> = (\<lambda> _ . \<lfloor>\<lfloor>3::int\<rfloor>\<rfloor>)"
definition OclInt4 ::"('\<AA>)Integer" ("\<four>")  where      "\<four> = (\<lambda> _ . \<lfloor>\<lfloor>4::int\<rfloor>\<rfloor>)"
definition OclInt5 ::"('\<AA>)Integer" ("\<five>")  where      "\<five> = (\<lambda> _ . \<lfloor>\<lfloor>5::int\<rfloor>\<rfloor>)"
definition OclInt6 ::"('\<AA>)Integer" ("\<six>")  where      "\<six> = (\<lambda> _ . \<lfloor>\<lfloor>6::int\<rfloor>\<rfloor>)"
definition OclInt7 ::"('\<AA>)Integer" ("\<seven>")  where      "\<seven> = (\<lambda> _ . \<lfloor>\<lfloor>7::int\<rfloor>\<rfloor>)"
definition OclInt8 ::"('\<AA>)Integer" ("\<eight>")  where      "\<eight> = (\<lambda> _ . \<lfloor>\<lfloor>8::int\<rfloor>\<rfloor>)"
definition OclInt9 ::"('\<AA>)Integer" ("\<nine>")  where      "\<nine> = (\<lambda> _ . \<lfloor>\<lfloor>9::int\<rfloor>\<rfloor>)"
definition OclInt10 ::"('\<AA>)Integer" ("\<one>\<zero>")where      "\<one>\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::int\<rfloor>\<rfloor>)"

subsection\<open>Validity and Definedness Properties\<close>

lemma  "\<delta>(null::('\<AA>)Integer) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)Integer) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> \<zero> = true" by(simp add:OclInt0_def)
lemma [simp,code_unfold]: "\<upsilon> \<zero> = true" by(simp add:OclInt0_def)
lemma [simp,code_unfold]: "\<delta> \<one> = true" by(simp add:OclInt1_def)
lemma [simp,code_unfold]: "\<upsilon> \<one> = true" by(simp add:OclInt1_def)
lemma [simp,code_unfold]: "\<delta> \<two> = true" by(simp add:OclInt2_def)
lemma [simp,code_unfold]: "\<upsilon> \<two> = true" by(simp add:OclInt2_def)
lemma [simp,code_unfold]: "\<delta> \<six> = true" by(simp add:OclInt6_def)
lemma [simp,code_unfold]: "\<upsilon> \<six> = true" by(simp add:OclInt6_def)
lemma [simp,code_unfold]: "\<delta> \<eight> = true" by(simp add:OclInt8_def)
lemma [simp,code_unfold]: "\<upsilon> \<eight> = true" by(simp add:OclInt8_def)
lemma [simp,code_unfold]: "\<delta> \<nine> = true" by(simp add:OclInt9_def)
lemma [simp,code_unfold]: "\<upsilon> \<nine> = true" by(simp add:OclInt9_def)

text_raw\<open>\endisatagafp\<close>

subsection\<open>Arithmetical Operations\<close>

subsubsection\<open>Definition\<close>
text\<open>Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot).\<close>
text\<open>Note that we can not follow the lexis of the OCL Standard for Isabelle
technical reasons; these operators are heavily overloaded in the HOL library
that a further overloading would lead to heavy technical buzz in this
document.
\<close>
definition OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "+\<^sub>i\<^sub>n\<^sub>t" 40)
where "x +\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> + \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>d_\<^sub>d "(+\<^sub>i\<^sub>n\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> + \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by unfold_locales (auto simp:OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def bot_option_def null_option_def)

  
definition OclMinus\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "-\<^sub>i\<^sub>n\<^sub>t" 41)
where "x -\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> - \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclMinus\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>d_\<^sub>d "(-\<^sub>i\<^sub>n\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> - \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclMinus\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def bot_option_def null_option_def)

                       
definition OclMult\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "*\<^sub>i\<^sub>n\<^sub>t" 45)
where "x *\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> * \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau>"
interpretation OclMult\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>d_\<^sub>d "OclMult\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> * \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclMult\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def bot_option_def null_option_def)
          
text\<open>Here is the special case of division, which is defined as invalid for division
by zero.\<close>
definition OclDivision\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "div\<^sub>i\<^sub>n\<^sub>t" 45)
where "x div\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclInt0 \<tau> then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> div \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> else invalid \<tau> 
                       else invalid \<tau> "
(* TODO: special locale setup.*)

definition OclModulus\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "mod\<^sub>i\<^sub>n\<^sub>t" 45)
where "x mod\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclInt0 \<tau> then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> mod \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> else invalid \<tau> 
                       else invalid \<tau> "
(* TODO: special locale setup.*)
                       
                       
definition OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>i\<^sub>n\<^sub>t" 35)
where "x <\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>d_\<^sub>d "(<\<^sub>i\<^sub>n\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> < \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def bot_option_def null_option_def)

definition OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>i\<^sub>n\<^sub>t" 35)
where "x \<le>\<^sub>i\<^sub>n\<^sub>t y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r : profile_bin\<^sub>d_\<^sub>d "(\<le>\<^sub>i\<^sub>n\<^sub>t)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> \<le> \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def bot_option_def null_option_def)

subsubsection\<open>Basic Properties\<close>

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_commute: "(X +\<^sub>i\<^sub>n\<^sub>t Y) = (Y +\<^sub>i\<^sub>n\<^sub>t X)"
  by(rule ext,auto simp:true_def false_def OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def invalid_def
                   split: option.split option.split_asm
                          bool.split bool.split_asm)

subsubsection\<open>Execution with Invalid or Null or Zero as Argument\<close>

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_zero1[simp,code_unfold] :
"(x +\<^sub>i\<^sub>n\<^sub>t \<zero>) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 proof (rule ext, rename_tac \<tau>, case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  fix \<tau> show "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau> \<Longrightarrow>
              (x +\<^sub>i\<^sub>n\<^sub>t \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_true', simp add: OclValid_def)
  by (metis OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclNot_defargs OclValid_def foundation5 foundation9)
 next fix \<tau>
  have A: "\<And>\<tau>. (\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))) = (x \<tau> = invalid \<tau> \<or> \<tau> \<Turnstile> \<delta> x)"
  by (metis OclNot_not OclOr_def defined5 defined6 defined_not_I foundation11 foundation18'
            foundation6 foundation7 foundation9 invalid_def)
  have B: "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> = x \<tau>"
   apply(cases "x \<tau>", metis bot_option_def foundation16)
   apply(rename_tac x', case_tac x', metis bot_option_def foundation16 null_option_def)
  by(simp)
  show "(x +\<^sub>i\<^sub>n\<^sub>t \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
    when "\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))"
   apply(insert that, subst OclIf_false', simp, simp add: A, auto simp: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclInt0_def)
     (* *)
     apply(simp add: foundation16'[simplified OclValid_def])
    apply(simp add: B)
  by(simp add: OclValid_def)
qed(metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_zero2[simp,code_unfold] :
"(\<zero> +\<^sub>i\<^sub>n\<^sub>t x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
by(subst OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_commute, simp)

(* TODO Basic proproperties for multiplication, division, modulus. *)



subsection\<open>Test Statements\<close>
text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>

Assert "\<tau> \<Turnstile> ( \<nine> \<le>\<^sub>i\<^sub>n\<^sub>t \<one>\<zero> )"
Assert "\<tau> \<Turnstile> (( \<four> +\<^sub>i\<^sub>n\<^sub>t \<four> ) \<le>\<^sub>i\<^sub>n\<^sub>t \<one>\<zero> )"
Assert "\<tau> |\<noteq> (( \<four> +\<^sub>i\<^sub>n\<^sub>t ( \<four> +\<^sub>i\<^sub>n\<^sub>t \<four> )) <\<^sub>i\<^sub>n\<^sub>t \<one>\<zero> )"
Assert "\<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>i\<^sub>n\<^sub>t \<one>)) "
Assert "\<tau> \<Turnstile> (((\<nine> *\<^sub>i\<^sub>n\<^sub>t \<four>) div\<^sub>i\<^sub>n\<^sub>t \<one>\<zero>) \<le>\<^sub>i\<^sub>n\<^sub>t  \<four>) "
Assert "\<tau> \<Turnstile> not (\<delta> (\<one> div\<^sub>i\<^sub>n\<^sub>t \<zero>)) "
Assert "\<tau> \<Turnstile> not (\<upsilon> (\<one> div\<^sub>i\<^sub>n\<^sub>t \<zero>)) "



lemma integer_non_null [simp]: "((\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) \<doteq> (null::('\<AA>)Integer)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma null_non_integer [simp]: "((null::('\<AA>)Integer) \<doteq> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma OclInt0_non_null [simp,code_unfold]: "(\<zero> \<doteq> null) = false" by(simp add: OclInt0_def)
lemma null_non_OclInt0 [simp,code_unfold]: "(null \<doteq> \<zero>) = false" by(simp add: OclInt0_def)
lemma OclInt1_non_null [simp,code_unfold]: "(\<one> \<doteq> null) = false" by(simp add: OclInt1_def)
lemma null_non_OclInt1 [simp,code_unfold]: "(null \<doteq> \<one>) = false" by(simp add: OclInt1_def)
lemma OclInt2_non_null [simp,code_unfold]: "(\<two> \<doteq> null) = false" by(simp add: OclInt2_def)
lemma null_non_OclInt2 [simp,code_unfold]: "(null \<doteq> \<two>) = false" by(simp add: OclInt2_def)
lemma OclInt6_non_null [simp,code_unfold]: "(\<six> \<doteq> null) = false" by(simp add: OclInt6_def)
lemma null_non_OclInt6 [simp,code_unfold]: "(null \<doteq> \<six>) = false" by(simp add: OclInt6_def)
lemma OclInt8_non_null [simp,code_unfold]: "(\<eight> \<doteq> null) = false" by(simp add: OclInt8_def)
lemma null_non_OclInt8 [simp,code_unfold]: "(null \<doteq> \<eight>) = false" by(simp add: OclInt8_def)
lemma OclInt9_non_null [simp,code_unfold]: "(\<nine> \<doteq> null) = false" by(simp add: OclInt9_def)
lemma null_non_OclInt9 [simp,code_unfold]: "(null \<doteq> \<nine>) = false" by(simp add: OclInt9_def)


text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>


text\<open>Elementary computations on Integer\<close>

Assert "\<tau> \<Turnstile> ((\<zero> <\<^sub>i\<^sub>n\<^sub>t \<two>) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t \<one>))"

Assert "\<tau> \<Turnstile> \<one> <> \<two>"
Assert "\<tau> \<Turnstile> \<two> <> \<one>"
Assert "\<tau> \<Turnstile> \<two> \<doteq> \<two>"

Assert "\<tau> \<Turnstile> \<upsilon> \<four>"
Assert "\<tau> \<Turnstile> \<delta> \<four>"
Assert "\<tau> \<Turnstile> \<upsilon> (null::('\<AA>)Integer)"
Assert "\<tau> \<Turnstile> (invalid \<triangleq> invalid)"
Assert "\<tau> \<Turnstile> (null \<triangleq> null)"
Assert "\<tau> \<Turnstile> (\<four> \<triangleq> \<four>)"
Assert "\<tau> |\<noteq> (\<nine> \<triangleq> \<one>\<zero>)"
Assert "\<tau> |\<noteq> (invalid \<triangleq> \<one>\<zero>)"
Assert "\<tau> |\<noteq> (null \<triangleq> \<one>\<zero>)"
Assert "\<tau> |\<noteq> (invalid \<doteq> (invalid::('\<AA>)Integer))"   (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)Integer))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> (invalid <> (invalid::('\<AA>)Integer))"   (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid <> (invalid::('\<AA>)Integer))" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (\<four> \<doteq> \<four>)"
Assert "\<tau> |\<noteq> (\<four> <> \<four>)"
Assert "\<tau> |\<noteq> (\<four> \<doteq> \<one>\<zero>)"
Assert "\<tau> \<Turnstile> (\<four> <> \<one>\<zero>)"
Assert "\<tau> |\<noteq> (\<zero> <\<^sub>i\<^sub>n\<^sub>t null)"
Assert "\<tau> |\<noteq> (\<delta> (\<zero> <\<^sub>i\<^sub>n\<^sub>t null))"


end
