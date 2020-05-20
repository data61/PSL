(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Real.thy --- Library definitions.
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

theory  UML_Real
imports "../UML_PropertyProfiles"
begin

section\<open>Basic Type Real: Operations\<close>

subsection\<open>Fundamental Predicates on Reals: Strict Equality \label{sec:real-strict-eq}\<close>

text\<open>The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Boolean"}-case as strict extension of the strong equality:\<close>
overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>)Real,('\<AA>)Real] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>R\<^sub>e\<^sub>a\<^sub>l [code_unfold] :
    "(x::('\<AA>)Real) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                  then (x \<triangleq> y) \<tau>
                                  else invalid \<tau>"
end

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation StrictRefEq\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>)Real) \<doteq> y" 
         by unfold_locales (auto simp: StrictRefEq\<^sub>R\<^sub>e\<^sub>a\<^sub>l)

subsection\<open>Basic Real Constants\<close>

text\<open>Although the remaining part of this library reasons about
reals abstractly, we provide here as example some convenient shortcuts.\<close>

definition OclReal0 ::"('\<AA>)Real" ("\<zero>.\<zero>")   where      "\<zero>.\<zero> =  (\<lambda> _ . \<lfloor>\<lfloor>0::real\<rfloor>\<rfloor>)"
definition OclReal1 ::"('\<AA>)Real" ("\<one>.\<zero>")   where      "\<one>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>1::real\<rfloor>\<rfloor>)"
definition OclReal2 ::"('\<AA>)Real" ("\<two>.\<zero>")   where      "\<two>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>2::real\<rfloor>\<rfloor>)"
text\<open>Etc.\<close>
text_raw\<open>\isatagafp\<close>
definition OclReal3 ::"('\<AA>)Real" ("\<three>.\<zero>")   where      "\<three>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>3::real\<rfloor>\<rfloor>)"
definition OclReal4 ::"('\<AA>)Real" ("\<four>.\<zero>")   where      "\<four>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>4::real\<rfloor>\<rfloor>)"
definition OclReal5 ::"('\<AA>)Real" ("\<five>.\<zero>")   where      "\<five>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>5::real\<rfloor>\<rfloor>)"
definition OclReal6 ::"('\<AA>)Real" ("\<six>.\<zero>")   where      "\<six>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>6::real\<rfloor>\<rfloor>)" 
definition OclReal7 ::"('\<AA>)Real" ("\<seven>.\<zero>")   where      "\<seven>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>7::real\<rfloor>\<rfloor>)"
definition OclReal8 ::"('\<AA>)Real" ("\<eight>.\<zero>")   where      "\<eight>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>8::real\<rfloor>\<rfloor>)"
definition OclReal9 ::"('\<AA>)Real" ("\<nine>.\<zero>")   where      "\<nine>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>9::real\<rfloor>\<rfloor>)"
definition OclReal10 ::"('\<AA>)Real" ("\<one>\<zero>.\<zero>") where      "\<one>\<zero>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::real\<rfloor>\<rfloor>)"
definition OclRealpi ::"('\<AA>)Real" ("\<pi>")    where      "\<pi> = (\<lambda> _ . \<lfloor>\<lfloor>pi\<rfloor>\<rfloor>)"

subsection\<open>Validity and Definedness Properties\<close>

lemma  "\<delta>(null::('\<AA>)Real) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)Real) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> \<zero>.\<zero> = true" by(simp add:OclReal0_def)
lemma [simp,code_unfold]: "\<upsilon> \<zero>.\<zero> = true" by(simp add:OclReal0_def)
lemma [simp,code_unfold]: "\<delta> \<one>.\<zero> = true" by(simp add:OclReal1_def)
lemma [simp,code_unfold]: "\<upsilon> \<one>.\<zero> = true" by(simp add:OclReal1_def)
lemma [simp,code_unfold]: "\<delta> \<two>.\<zero> = true" by(simp add:OclReal2_def)
lemma [simp,code_unfold]: "\<upsilon> \<two>.\<zero> = true" by(simp add:OclReal2_def)
lemma [simp,code_unfold]: "\<delta> \<six>.\<zero> = true" by(simp add:OclReal6_def)
lemma [simp,code_unfold]: "\<upsilon> \<six>.\<zero> = true" by(simp add:OclReal6_def)
lemma [simp,code_unfold]: "\<delta> \<eight>.\<zero> = true" by(simp add:OclReal8_def)
lemma [simp,code_unfold]: "\<upsilon> \<eight>.\<zero> = true" by(simp add:OclReal8_def)
lemma [simp,code_unfold]: "\<delta> \<nine>.\<zero> = true" by(simp add:OclReal9_def)
lemma [simp,code_unfold]: "\<upsilon> \<nine>.\<zero> = true" by(simp add:OclReal9_def)
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
definition OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "+\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 40)
where "x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> + \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(+\<^sub>r\<^sub>e\<^sub>a\<^sub>l)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> + \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by unfold_locales (auto simp:OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def null_option_def)


definition OclMinus\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "-\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 41)
where "x -\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> - \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclMinus\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(-\<^sub>r\<^sub>e\<^sub>a\<^sub>l)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> - \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclMinus\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def null_option_def)


definition OclMult\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "*\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x *\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> * \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau>"
interpretation OclMult\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "OclMult\<^sub>R\<^sub>e\<^sub>a\<^sub>l" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> * \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclMult\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def null_option_def)
          
text\<open>Here is the special case of division, which is defined as invalid for division
by zero.\<close>
definition OclDivision\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "div\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x div\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclReal0 \<tau> then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> / \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> else invalid \<tau> 
                       else invalid \<tau> "
(* TODO: special locale setup.*)

definition "mod_float a b = a - real_of_int (floor (a / b)) * b"
definition OclModulus\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "mod\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x mod\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then if y \<tau> \<noteq> OclReal0 \<tau> then \<lfloor>\<lfloor>mod_float \<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> else invalid \<tau> 
                       else invalid \<tau> "
(* TODO: special locale setup.*)


definition OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 35)
where "x <\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(<\<^sub>r\<^sub>e\<^sub>a\<^sub>l)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> < \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def null_option_def)

definition OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 35)
where "x \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l : profile_bin\<^sub>d_\<^sub>d "(\<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l)" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> \<le> \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def bot_option_def null_option_def)

subsubsection\<open>Basic Properties\<close>

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_commute: "(X +\<^sub>r\<^sub>e\<^sub>a\<^sub>l Y) = (Y +\<^sub>r\<^sub>e\<^sub>a\<^sub>l X)"
  by(rule ext,auto simp:true_def false_def OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def invalid_def
                   split: option.split option.split_asm
                          bool.split bool.split_asm)

subsubsection\<open>Execution with Invalid or Null or Zero as Argument\<close>

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_zero1[simp,code_unfold] :
"(x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>.\<zero>) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 proof (rule ext, rename_tac \<tau>, case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  fix \<tau> show "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau> \<Longrightarrow>
              (x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>.\<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_true', simp add: OclValid_def)
  by (metis OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def OclNot_defargs OclValid_def foundation5 foundation9)
 next fix \<tau>
  have A: "\<And>\<tau>. (\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))) = (x \<tau> = invalid \<tau> \<or> \<tau> \<Turnstile> \<delta> x)"
  by (metis OclNot_not OclOr_def defined5 defined6 defined_not_I foundation11 foundation18'
            foundation6 foundation7 foundation9 invalid_def)
  have B: "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> = x \<tau>"
   apply(cases "x \<tau>", metis bot_option_def foundation16)
   apply(rename_tac x', case_tac x', metis bot_option_def foundation16 null_option_def)
  by(simp)
  show "(x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>.\<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
    when "\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))"
   apply(insert that, subst OclIf_false', simp, simp add: A, auto simp: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def OclReal0_def)
     (* *)
     apply(simp add: foundation16'[simplified OclValid_def])
    apply(simp add: B)
  by(simp add: OclValid_def)
qed(metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_zero2[simp,code_unfold] :
"(\<zero>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
by(subst OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_commute, simp)

(* TODO Basic proproperties for multiplication, division, modulus. *)



subsection\<open>Test Statements\<close>
text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>

Assert "\<tau> \<Turnstile> ( \<nine>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> )"
Assert "\<tau> \<Turnstile> (( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<four>.\<zero> ) \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> )"
Assert "\<tau> |\<noteq> (( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l ( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<four>.\<zero> )) <\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> )"
Assert "\<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>.\<zero>)) "
Assert "\<tau> \<Turnstile> (((\<nine>.\<zero> *\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<four>.\<zero>) div\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero>) \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l  \<four>.\<zero>) "
Assert "\<tau> \<Turnstile> not (\<delta> (\<one>.\<zero> div\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>.\<zero>)) "
Assert "\<tau> \<Turnstile> not (\<upsilon> (\<one>.\<zero> div\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>.\<zero>)) "



lemma real_non_null [simp]: "((\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) \<doteq> (null::('\<AA>)Real)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>R\<^sub>e\<^sub>a\<^sub>l valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma null_non_real [simp]: "((null::('\<AA>)Real) \<doteq> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>R\<^sub>e\<^sub>a\<^sub>l valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma OclReal0_non_null [simp,code_unfold]: "(\<zero>.\<zero> \<doteq> null) = false" by(simp add: OclReal0_def)
lemma null_non_OclReal0 [simp,code_unfold]: "(null \<doteq> \<zero>.\<zero>) = false" by(simp add: OclReal0_def)
lemma OclReal1_non_null [simp,code_unfold]: "(\<one>.\<zero> \<doteq> null) = false" by(simp add: OclReal1_def)
lemma null_non_OclReal1 [simp,code_unfold]: "(null \<doteq> \<one>.\<zero>) = false" by(simp add: OclReal1_def)
lemma OclReal2_non_null [simp,code_unfold]: "(\<two>.\<zero> \<doteq> null) = false" by(simp add: OclReal2_def)
lemma null_non_OclReal2 [simp,code_unfold]: "(null \<doteq> \<two>.\<zero>) = false" by(simp add: OclReal2_def)
lemma OclReal6_non_null [simp,code_unfold]: "(\<six>.\<zero> \<doteq> null) = false" by(simp add: OclReal6_def)
lemma null_non_OclReal6 [simp,code_unfold]: "(null \<doteq> \<six>.\<zero>) = false" by(simp add: OclReal6_def)
lemma OclReal8_non_null [simp,code_unfold]: "(\<eight>.\<zero> \<doteq> null) = false" by(simp add: OclReal8_def)
lemma null_non_OclReal8 [simp,code_unfold]: "(null \<doteq> \<eight>.\<zero>) = false" by(simp add: OclReal8_def)
lemma OclReal9_non_null [simp,code_unfold]: "(\<nine>.\<zero> \<doteq> null) = false" by(simp add: OclReal9_def)
lemma null_non_OclReal9 [simp,code_unfold]: "(null \<doteq> \<nine>.\<zero>) = false" by(simp add: OclReal9_def)


text\<open>Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.\<close>


text\<open>Elementary computations on Real\<close>

Assert "\<tau> \<Turnstile> \<one>.\<zero> <> \<two>.\<zero>"
Assert "\<tau> \<Turnstile> \<two>.\<zero> <> \<one>.\<zero>"
Assert "\<tau> \<Turnstile> \<two>.\<zero> \<doteq> \<two>.\<zero>"

Assert "\<tau> \<Turnstile> \<upsilon> \<four>.\<zero>"
Assert "\<tau> \<Turnstile> \<delta> \<four>.\<zero>"
Assert "\<tau> \<Turnstile> \<upsilon> (null::('\<AA>)Real)"
Assert "\<tau> \<Turnstile> (invalid \<triangleq> invalid)"
Assert "\<tau> \<Turnstile> (null \<triangleq> null)"
Assert "\<tau> \<Turnstile> (\<four>.\<zero> \<triangleq> \<four>.\<zero>)"
Assert "\<tau> |\<noteq> (\<nine>.\<zero> \<triangleq> \<one>\<zero>.\<zero>)"
Assert "\<tau> |\<noteq> (invalid \<triangleq> \<one>\<zero>.\<zero>)"
Assert "\<tau> |\<noteq> (null \<triangleq> \<one>\<zero>.\<zero>)"
Assert "\<tau> |\<noteq> (invalid \<doteq> (invalid::('\<AA>)Real))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)Real))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> (invalid <> (invalid::('\<AA>)Real))" (* Without typeconstraint not executable.*)
Assert "\<tau> |\<noteq> \<upsilon> (invalid <> (invalid::('\<AA>)Real))" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Real) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Real) )" (* Without typeconstraint not executable.*)
Assert "\<tau> \<Turnstile> (\<four>.\<zero> \<doteq> \<four>.\<zero>)"
Assert "\<tau> |\<noteq> (\<four>.\<zero> <> \<four>.\<zero>)"
Assert "\<tau> |\<noteq> (\<four>.\<zero> \<doteq> \<one>\<zero>.\<zero>)"
Assert "\<tau> \<Turnstile> (\<four>.\<zero> <> \<one>\<zero>.\<zero>)"
Assert "\<tau> |\<noteq> (\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l null)"
Assert "\<tau> |\<noteq> (\<delta> (\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l null))"


end
