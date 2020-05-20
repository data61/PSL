(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Bag.thy --- Library definitions.
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


theory  UML_Bag
imports "../basic_types/UML_Void"
        "../basic_types/UML_Boolean"
        "../basic_types/UML_Integer"
        "../basic_types/UML_String"
        "../basic_types/UML_Real"
begin

no_notation None ("\<bottom>")
section\<open>Collection Type Bag: Operations\<close>

definition "Rep_Bag_base' x = {(x0, y). y < \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> x0 }"
definition "Rep_Bag_base x \<tau> = {(x0, y). y < \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> x0 }"
definition "Rep_Set_base x \<tau> = fst ` {(x0, y). y < \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> x0 }"

definition ApproxEq (infixl "\<cong>" 30)
where     "X \<cong> Y \<equiv>  \<lambda> \<tau>. \<lfloor>\<lfloor>Rep_Set_base X \<tau> = Rep_Set_base Y \<tau> \<rfloor>\<rfloor>"


subsection\<open>As a Motivation for the (infinite) Type Construction: Type-Extensions as Bags 
             \label{sec:type-extensions}\<close>

text\<open>Our notion of typed bag goes beyond the usual notion of a finite executable bag and
is powerful enough to capture \emph{the extension of a type} in UML and OCL. This means
we can have in Featherweight OCL Bags containing all possible elements of a type, not only
those (finite) ones representable in a state. This holds for base types as well as class types,
although the notion for class-types --- involving object id's not occurring in a state ---
requires some care.

In a world with @{term invalid} and @{term null}, there are two notions extensions possible:
\begin{enumerate}
\item the bag of all \emph{defined} values of a type @{term T}
      (for which we will introduce the constant  @{term T})
\item the bag of all \emph{valid} values of a type @{term T}, so including @{term null}
      (for which we will introduce the constant  @{term T\<^sub>n\<^sub>u\<^sub>l\<^sub>l}).
\end{enumerate}
\<close>

text\<open>We define the bag extensions for the base type @{term Integer} as follows:\<close>
definition Integer :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Integer \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | Some None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

definition Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

lemma Integer_defined : "\<delta> Integer = true"
apply(rule ext, auto simp: Integer_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

text\<open>This allows the theorems:

      \<open>\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer->includes\<^sub>B\<^sub>a\<^sub>g(x))\<close>
      \<open>\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> Integer  \<triangleq> (Integer->including\<^sub>B\<^sub>a\<^sub>g(x))\<close>

and

      \<open>\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->includes\<^sub>B\<^sub>a\<^sub>g(x))\<close>
      \<open>\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l  \<triangleq> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->including\<^sub>B\<^sub>a\<^sub>g(x))\<close>

which characterize the infiniteness of these bags by a recursive property on these bags.
\<close>

text\<open>In the same spirit, we proceed similarly for the remaining base types:\<close>

definition Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some) (\<lambda> x. if x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Some None) then 1 else 0))"

definition Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y :: "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some) (\<lambda>_. 0))"

lemma Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def
                           bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by((subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def bot_Void_def),
   (subst (asm) Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def))+

lemma Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_defined : "\<delta> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y = true"
apply(rule ext, auto simp: Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def
                           bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by((subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def bot_Void_def))+

lemma assumes "\<tau> \<Turnstile> \<delta> (V :: ('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag)"
      shows   "\<tau> \<Turnstile> V \<cong> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<cong> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
proof -
  have A:"\<And>x y. x \<noteq> {} \<Longrightarrow> \<exists>y. y\<in> x"
  by (metis all_not_in_conv)
show "?thesis"
  apply(case_tac "V \<tau>")
  proof - fix y show "V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e y \<Longrightarrow>
                      y \<in> {X. X = \<bottom> \<or> X = null \<or> \<lceil>\<lceil>X\<rceil>\<rceil> \<bottom> = 0} \<Longrightarrow>
                      \<tau> \<Turnstile> V \<cong> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<cong> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(insert assms, case_tac y, simp add: bot_option_def, simp add: bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def foundation16)
  apply(simp add: bot_option_def null_option_def)
  apply(erule disjE, metis OclValid_def defined_def foundation2 null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def true_def)
  proof - fix a show "V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>a\<rfloor> \<Longrightarrow> \<lceil>a\<rceil> \<bottom> = 0 \<Longrightarrow> \<tau> \<Turnstile> V \<cong> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<cong> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(case_tac a, simp, insert assms, metis OclValid_def foundation16 null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def true_def)
  apply(simp)
  proof - fix aa show " V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow> aa \<bottom> = 0 \<Longrightarrow> \<tau> \<Turnstile> V \<cong> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<cong> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(case_tac "aa (Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) = 0",
        rule disjI2,
        insert assms,
        simp add: Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_def OclValid_def ApproxEq_def Rep_Set_base_def true_def Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse image_def)
  apply(intro allI)
  proof - fix x fix b show " V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow> aa \<bottom> = 0 \<Longrightarrow> aa (Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) = 0 \<Longrightarrow> (\<delta> V) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Longrightarrow> \<not> b < aa x"
    apply (case_tac x, auto)
     apply (simp add: bot_Void_def bot_option_def)
    apply (simp add: bot_option_def null_option_def)
  done
  apply_end(simp+, rule disjI1)
  show "V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow> aa \<bottom> = 0 \<Longrightarrow> 0 < aa (Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) \<Longrightarrow> \<tau> \<Turnstile> \<delta> V \<Longrightarrow> \<tau> \<Turnstile> V \<cong> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l"
  apply(simp add: Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def OclValid_def ApproxEq_def Rep_Set_base_def true_def Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse image_def,
        subst Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp)
  using bot_Void_def apply auto[1]
  apply(simp)
  apply(rule equalityI, rule subsetI, simp)
   proof - fix x show "V \<tau> = Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow>
            aa \<bottom> = 0 \<Longrightarrow> 0 < aa (Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>) \<Longrightarrow> (\<delta> V) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor> \<Longrightarrow> \<exists>b. b < aa x \<Longrightarrow> x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
   apply( case_tac x, auto)
    apply (simp add: bot_Void_def bot_option_def)
   by (simp add: bot_option_def null_option_def)
  qed ((simp add: bot_Void_def bot_option_def)+, blast)
qed qed qed qed qed

definition Boolean :: "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Boolean \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | Some None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

definition Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

lemma Boolean_defined : "\<delta> Boolean = true"
apply(rule ext, auto simp: Boolean_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

definition String :: "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "String \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | Some None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

definition String\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "String\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

lemma String_defined : "\<delta> String = true"
apply(rule ext, auto simp: String_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma String\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> String\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: String\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

definition Real :: "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Real \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | Some None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

definition Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Bag"
where     "Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (\<lambda> None \<Rightarrow> 0 | _ \<Rightarrow> 1))"

lemma Real_defined : "\<delta> Real = true"
apply(rule ext, auto simp: Real_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

subsection\<open>Basic Properties of the Bag Type\<close>

text\<open>Every element in a defined bag is valid.\<close>

lemma Bag_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> bot = 0"
apply(insert Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def
           split:if_split_asm)
 apply(erule contrapos_pp [of "Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = bot"])
 apply(subst Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
 apply(simp add: Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = null"])
apply(subst Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
apply(simp add: Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse  null_option_def)
by (simp add: bot_option_def)

lemma Bag_inv_lemma' :
 assumes x_def : "\<tau> \<Turnstile> \<delta> X"
     and e_mem : "\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> e \<ge> 1"
   shows "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)"
apply(case_tac "e = bot", insert assms, drule Bag_inv_lemma, simp)
by (simp add: foundation18')

lemma abs_rep_simp' :
 assumes S_all_def : "\<tau> \<Turnstile> \<delta> S"
   shows "Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by(simp add: false_def true_def)
 show ?thesis
  apply(insert S_all_def, simp add: OclValid_def defined_def)
  apply(rule mp[OF Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau>
                                                    then false \<tau> else true \<tau>) = true \<tau> \<longrightarrow>
                                                   Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]],
        rename_tac S')
   apply(simp add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse discr_eq_false_true)
   apply(case_tac S') apply(simp add: bot_fun_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)+
   apply(rename_tac S'', case_tac S'') apply(simp add: null_fun_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)+
 done
qed

lemma invalid_bag_OclNot_defined [simp,code_unfold]:"\<delta>(invalid::('\<AA>,'\<alpha>::null) Bag) = false" by simp
lemma null_bag_OclNot_defined [simp,code_unfold]:"\<delta>(null::('\<AA>,'\<alpha>::null) Bag) = false"
by(simp add: defined_def null_fun_def)
lemma invalid_bag_valid [simp,code_unfold]:"\<upsilon>(invalid::('\<AA>,'\<alpha>::null) Bag) = false"
by simp
lemma null_bag_valid [simp,code_unfold]:"\<upsilon>(null::('\<AA>,'\<alpha>::null) Bag) = true"
apply(simp add: valid_def null_fun_def bot_fun_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(subst Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,simp_all add: null_option_def bot_option_def)
done

text\<open>... which means that we can have a type \<open>('\<AA>,('\<AA>,('\<AA>) Integer) Bag) Bag\<close>
corresponding exactly to Bag(Bag(Integer)) in OCL notation. Note that the parameter
\<open>'\<AA>\<close> still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties
independently from a concrete class diagram.\<close>

subsection\<open>Definition: Strict Equality \label{sec:bag-strict-equality}\<close>

text\<open>After the part of foundational operations on bags, we detail here equality on bags.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:\<close>

overloading StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>,'\<alpha>::null)Bag,('\<AA>,'\<alpha>::null)Bag] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>B\<^sub>a\<^sub>g :
    "(x::('\<AA>,'\<alpha>::null)Bag) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                       then (x \<triangleq> y)\<tau>
                                       else invalid \<tau>"
end

text\<open>One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its oid stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF-invariant), the referential equality and the
strong equality---and therefore the strict equality on bags in the sense above---coincides.\<close>

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>B\<^sub>a\<^sub>g : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>,'\<alpha>::null)Bag) \<doteq> y" 
         by unfold_locales (auto simp:  StrictRefEq\<^sub>B\<^sub>a\<^sub>g)



subsection\<open>Constants: mtBag\<close>
definition mtBag::"('\<AA>,'\<alpha>::null) Bag"  ("Bag{}")
where     "Bag{} \<equiv> (\<lambda> \<tau>.  Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lambda>_. 0::nat\<rfloor>\<rfloor> )"


lemma mtBag_defined[simp,code_unfold]:"\<delta>(Bag{}) = true"
apply(rule ext, auto simp: mtBag_def defined_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                           bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtBag_valid[simp,code_unfold]:"\<upsilon>(Bag{}) = true"
apply(rule ext,auto simp: mtBag_def valid_def
                          bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtBag_rep_bag: "\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Bag{} \<tau>)\<rceil>\<rceil> = (\<lambda> _. 0)"
 apply(simp add: mtBag_def, subst Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
by(simp add: bot_option_def)+

text_raw\<open>\isatagafp\<close>

lemma [simp,code_unfold]: "const Bag{}"
by(simp add: const_def mtBag_def)


text\<open>Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid.\<close>

text_raw\<open>\endisatagafp\<close>

subsection\<open>Definition: Including\<close>

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Bag"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e(x \<tau>)\<rceil>\<rceil> 
                                                      ((y \<tau>):=\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e(x \<tau>)\<rceil>\<rceil>(y \<tau>)+1) 
                                                    \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclIncluding   ("_->including\<^sub>B\<^sub>a\<^sub>g'(_')")

interpretation OclIncluding : profile_bin\<^sub>d_\<^sub>v OclIncluding "\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> 
                                                      (y := \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> y + 1)\<rfloor>\<rfloor>"
proof -  
   let ?X = "\<lambda>x y. \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e(x)\<rceil>\<rceil> ((y):=\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e(x)\<rceil>\<rceil>( y )+1)"
   show "profile_bin\<^sub>d_\<^sub>v OclIncluding (\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> ?X x y \<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclIncluding_def bot_option_def null_option_def 
                                           bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          by(subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, simp_all,
             metis (mono_tags, lifting) Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_option_def mem_Collect_eq null_option_def,
             simp add: bot_option_def null_option_def)+
qed

syntax
  "_OclFinbag" :: "args => ('\<AA>,'a::null) Bag"    ("Bag{(_)}")
translations
  "Bag{x, xs}" == "CONST OclIncluding (Bag{xs}) x"
  "Bag{x}"     == "CONST OclIncluding (Bag{}) x "


subsection\<open>Definition: Excluding\<close>

definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Bag"
where     "OclExcluding x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> ((y \<tau>):=0::nat) \<rfloor>\<rfloor>
                                     else invalid \<tau> )"
notation   OclExcluding   ("_->excluding\<^sub>B\<^sub>a\<^sub>g'(_')")

interpretation OclExcluding: profile_bin\<^sub>d_\<^sub>v OclExcluding  
                            "\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e(x)\<rceil>\<rceil>(y:=0::nat)\<rfloor>\<rfloor>"
proof -
    show "profile_bin\<^sub>d_\<^sub>v OclExcluding (\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>(y := 0)\<rfloor>\<rfloor>)"
         apply unfold_locales  
         apply(auto simp:OclExcluding_def bot_option_def null_option_def  
                         null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
         by(subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
               simp_all add: bot_option_def null_option_def,
               metis (mono_tags, lifting) Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_option_def
                                          mem_Collect_eq null_option_def)+
qed

subsection\<open>Definition: Includes\<close>

definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> (y \<tau>) > 0 \<rfloor>\<rfloor>
                                     else \<bottom>  )"
notation   OclIncludes    ("_->includes\<^sub>B\<^sub>a\<^sub>g'(_')" (*[66,65]65*))

interpretation OclIncludes : profile_bin\<^sub>d_\<^sub>v OclIncludes "\<lambda>x y. \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> y > 0 \<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclIncludes_def bot_option_def null_option_def invalid_def)

subsection\<open>Definition: Excludes\<close>

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"
notation   OclExcludes    ("_->excludes\<^sub>B\<^sub>a\<^sub>g'(_')" (*[66,65]65*))

text\<open>The case of the size definition is somewhat special, we admit
explicitly in Featherweight OCL the possibility of infinite bags. For
the size definition, this requires an extra condition that assures
that the cardinality of the bag is actually a defined integer.\<close>

interpretation OclExcludes : profile_bin\<^sub>d_\<^sub>v OclExcludes "\<lambda>x y. \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> y \<le> 0 \<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclExcludes_def OclIncludes_def OclNot_def bot_option_def null_option_def invalid_def)

subsection\<open>Definition: Size\<close>

definition OclSize     :: "('\<AA>,'\<alpha>::null)Bag \<Rightarrow> '\<AA> Integer"
where     "OclSize x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> finite (Rep_Bag_base x \<tau>)
                             then \<lfloor>\<lfloor> int (card (Rep_Bag_base x \<tau>)) \<rfloor>\<rfloor>
                             else \<bottom> )"
notation  (* standard ascii syntax *)
           OclSize        ("_->size\<^sub>B\<^sub>a\<^sub>g'(')" (*[66]*))

text\<open>The following definition follows the requirement of the
standard to treat null as neutral element of bags. It is
a well-documented exception from the general strictness
rule and the rule that the distinguished argument self should
be non-null.\<close>

(*TODO Locale - Equivalent*)  


subsection\<open>Definition: IsEmpty\<close>

definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Bag \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty\<^sub>B\<^sub>a\<^sub>g'(')" (*[66]*))

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: NotEmpty\<close>

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Bag \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty\<^sub>B\<^sub>a\<^sub>g'(')" (*[66]*))

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Any\<close>

(* Slight breach of naming convention in order to avoid naming conflict on constant.*)
definition OclANY   :: "[('\<AA>,'\<alpha>::null) Bag] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclANY x = (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau>
                            then if (\<delta> x and OclNotEmpty x) \<tau> = true \<tau>
                                 then SOME y. y \<in> (Rep_Set_base x \<tau>)
                                 else null \<tau>
                            else \<bottom> )"
notation   OclANY   ("_->any\<^sub>B\<^sub>a\<^sub>g'(')")

(*TODO Locale - Equivalent*)  

(* actually, this definition covers only: X->any\<^sub>B\<^sub>a\<^sub>g(true) of the standard, which foresees
a (totally correct) high-level definition
source->any\<^sub>B\<^sub>a\<^sub>g(iterator | body) =
source->select(iterator | body)->asSequence()->first(). Since we don't have sequences,
we have to go for a direct---restricted---definition. *)

subsection\<open>Definition: Forall\<close>

text\<open>The definition of OclForall mimics the one of @{term "OclAnd"}:
OclForall is not a strict operation.\<close>
definition OclForall     :: "[('\<AA>,'\<alpha>::null)Bag,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then if (\<exists>x\<in>Rep_Set_base S \<tau>. P (\<lambda>_. x) \<tau> = false \<tau>)
                                      then false \<tau>
                                      else if (\<exists>x\<in>Rep_Set_base S \<tau>. P (\<lambda>_. x) \<tau> = invalid \<tau>)
                                           then invalid \<tau>
                                           else if (\<exists>x\<in>Rep_Set_base S \<tau>. P (\<lambda>_. x) \<tau> = null \<tau>)
                                                then null \<tau>
                                                else true \<tau>
                                 else \<bottom>)"
syntax
  "_OclForallBag" :: "[('\<AA>,'\<alpha>::null) Bag,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forAll\<^sub>B\<^sub>a\<^sub>g'(_|_')")
translations
  "X->forAll\<^sub>B\<^sub>a\<^sub>g(x | P)" == "CONST UML_Bag.OclForall X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Exists\<close>
  
text\<open>Like OclForall, OclExists is also not strict.\<close>
definition OclExists     :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = not(UML_Bag.OclForall S (\<lambda> X. not (P X)))"

syntax
  "_OclExistBag" :: "[('\<AA>,'\<alpha>::null) Bag,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists\<^sub>B\<^sub>a\<^sub>g'(_|_')")
translations
  "X->exists\<^sub>B\<^sub>a\<^sub>g(x | P)" == "CONST UML_Bag.OclExists X (%x. P)"

(*TODO Locale - Equivalent*)  
  
subsection\<open>Definition: Iterate\<close>

definition OclIterate :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<beta>::null)val,
                           ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where     "OclIterate S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite (Rep_Bag_base S \<tau>)
                                    then Finite_Set.fold (F o (\<lambda>a \<tau>. a) o fst) A (Rep_Bag_base S \<tau>) \<tau>
                                    else \<bottom>)"
syntax
  "_OclIterateBag"  :: "[('\<AA>,'\<alpha>::null) Bag, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate\<^sub>B\<^sub>a\<^sub>g'(_;_=_ | _')" (*[71,100,70]50*))
translations
  "X->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = A | P)" == "CONST OclIterate X A (%a. (% x. P))"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Select\<close>
  
  
definition OclSelect :: "[('\<AA>,'\<alpha>::null)Bag,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>)Bag"
where "OclSelect S P = (\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau>
                              then if (\<exists>x\<in>Rep_Set_base S \<tau>. P(\<lambda> _. x) \<tau> = invalid \<tau>)
                                   then invalid \<tau>
                                   else Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lambda>x. 
                                          let n = \<lceil>\<lceil> Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>) \<rceil>\<rceil> x in
                                          if n = 0 | P (\<lambda>_. x) \<tau> = false \<tau> then
                                            0
                                          else
                                            n\<rfloor>\<rfloor>
                              else invalid \<tau>)"
syntax
  "_OclSelectBag" :: "[('\<AA>,'\<alpha>::null) Bag,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->select\<^sub>B\<^sub>a\<^sub>g'(_|_')")
translations
  "X->select\<^sub>B\<^sub>a\<^sub>g(x | P)" == "CONST OclSelect X (% x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Reject\<close>

definition OclReject :: "[('\<AA>,'\<alpha>::null)Bag,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>::null)Bag"
where "OclReject S P = OclSelect S (not o P)"
syntax
  "_OclRejectBag" :: "[('\<AA>,'\<alpha>::null) Bag,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->reject\<^sub>B\<^sub>a\<^sub>g'(_|_')")
translations
  "X->reject\<^sub>B\<^sub>a\<^sub>g(x | P)" == "CONST OclReject X (% x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: IncludesAll\<close>

definition OclIncludesAll   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) Bag] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludesAll x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then \<lfloor>\<lfloor>Rep_Bag_base y \<tau> \<subseteq> Rep_Bag_base x \<tau> \<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation   OclIncludesAll ("_->includesAll\<^sub>B\<^sub>a\<^sub>g'(_')" (*[66,65]65*))

interpretation OclIncludesAll : profile_bin\<^sub>d_\<^sub>d OclIncludesAll "\<lambda>x y. \<lfloor>\<lfloor>Rep_Bag_base' y \<subseteq> Rep_Bag_base' x \<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclIncludesAll_def bot_option_def null_option_def invalid_def
                             Rep_Bag_base_def Rep_Bag_base'_def)

subsection\<open>Definition: ExcludesAll\<close>

definition OclExcludesAll   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) Bag] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludesAll x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then \<lfloor>\<lfloor>Rep_Bag_base y \<tau> \<inter> Rep_Bag_base x \<tau> = {} \<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation  OclExcludesAll ("_->excludesAll\<^sub>B\<^sub>a\<^sub>g'(_')" (*[66,65]65*))

interpretation OclExcludesAll : profile_bin\<^sub>d_\<^sub>d OclExcludesAll "\<lambda>x y. \<lfloor>\<lfloor>Rep_Bag_base' y \<inter> Rep_Bag_base' x = {} \<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclExcludesAll_def bot_option_def null_option_def invalid_def
                             Rep_Bag_base_def Rep_Bag_base'_def)

subsection\<open>Definition: Union\<close>

definition OclUnion   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) Bag] \<Rightarrow> ('\<AA>,'\<alpha>) Bag"
where     "OclUnion x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                then Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lambda> X. \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> X + 
                                                       \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> X\<rfloor>\<rfloor>
                                else invalid \<tau> )"
notation   OclUnion       ("_->union\<^sub>B\<^sub>a\<^sub>g'(_')"          (*[66,65]65*))

interpretation OclUnion : 
               profile_bin\<^sub>d_\<^sub>d OclUnion "\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lambda> X. \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> X + 
                                                                \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> X\<rfloor>\<rfloor>"
proof -  
   show "profile_bin\<^sub>d_\<^sub>d OclUnion (\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lambda> X. \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> X + \<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> X\<rfloor>\<rfloor>)"
   apply unfold_locales 
   apply(auto simp:OclUnion_def bot_option_def null_option_def 
                   null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
   by(subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
      simp_all add: bot_option_def null_option_def, 
      metis (mono_tags, lifting) Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_option_def mem_Collect_eq
                                 null_option_def)+
qed

subsection\<open>Definition: Intersection\<close>

definition OclIntersection   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) Bag] \<Rightarrow> ('\<AA>,'\<alpha>) Bag"
where     "OclIntersection x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor> \<lambda> X. min (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> X) 
                                                       (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> X)\<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation   OclIntersection("_->intersection\<^sub>B\<^sub>a\<^sub>g'(_')"   (*[71,70]70*))

interpretation OclIntersection : 
               profile_bin\<^sub>d_\<^sub>d OclIntersection "\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lambda> X. min (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> X) 
                                                                (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> X)\<rfloor>\<rfloor>"
proof -  
   show "profile_bin\<^sub>d_\<^sub>d OclIntersection (\<lambda>x y. Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lambda> X. min (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> X) 
                                                                (\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> X)\<rfloor>\<rfloor>)"
   apply unfold_locales 
   apply(auto simp:OclIntersection_def bot_option_def null_option_def 
                   null_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def invalid_def)
   by(subst (asm) Abs_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
      simp_all add: bot_option_def null_option_def, 
      metis (mono_tags, lifting) Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_option_def mem_Collect_eq min_0R
                                 null_option_def)+
qed

subsection\<open>Definition: Count\<close>

definition OclCount   :: "[('\<AA>,'\<alpha>::null) Bag,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>) Integer"
where     "OclCount x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                             then  \<lfloor>\<lfloor>int(\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> (y \<tau>))\<rfloor>\<rfloor> 
                             else invalid \<tau> )"
notation   OclCount ("_->count\<^sub>B\<^sub>a\<^sub>g'(_')"  (*[66,65]65*))

interpretation OclCount : profile_bin\<^sub>d_\<^sub>d OclCount "\<lambda>x y. \<lfloor>\<lfloor>int(\<lceil>\<lceil>Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> y)\<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclCount_def bot_option_def null_option_def)

subsection\<open>Definition (future operators)\<close>

consts (* abstract bag collection operations *)
    OclSum         :: " ('\<AA>,'\<alpha>::null) Bag \<Rightarrow> '\<AA> Integer"
  
notation  OclSum         ("_->sum\<^sub>B\<^sub>a\<^sub>g'(')" (*[66]*))

subsection\<open>Logical Properties\<close>

text\<open>OclIncluding\<close>

lemma OclIncluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->including\<^sub>B\<^sub>a\<^sub>g(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis (hide_lams, no_types) OclIncluding.def_valid_then_def OclIncluding.defined_args_valid)

lemma OclIncluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->including\<^sub>B\<^sub>a\<^sub>g(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclIncluding.def_valid_then_def)

text\<open>etc. etc.\<close>
text_raw\<open>\isatagafp\<close> 

text\<open>OclExcluding\<close>

lemma OclExcluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excluding\<^sub>B\<^sub>a\<^sub>g(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis OclExcluding.def_valid_then_def OclExcluding.defined_args_valid)

lemma OclExcluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excluding\<^sub>B\<^sub>a\<^sub>g(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclExcluding.def_valid_then_def)

text\<open>OclIncludes\<close>

lemma OclIncludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->includes\<^sub>B\<^sub>a\<^sub>g(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (simp add: OclIncludes.def_valid_then_def foundation10')

lemma OclIncludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->includes\<^sub>B\<^sub>a\<^sub>g(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclIncludes.def_valid_then_def)

text\<open>OclExcludes\<close>

lemma OclExcludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excludes\<^sub>B\<^sub>a\<^sub>g(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (simp add: OclExcludes.def_valid_then_def foundation10')

lemma OclExcludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excludes\<^sub>B\<^sub>a\<^sub>g(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclExcludes.def_valid_then_def)

text\<open>OclSize\<close>

lemma OclSize_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->size\<^sub>B\<^sub>a\<^sub>g()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclSize_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def
        split: bool.split_asm HOL.if_split_asm option.split)

lemma OclSize_infinite:
assumes non_finite:"\<tau> \<Turnstile> not(\<delta>(S->size\<^sub>B\<^sub>a\<^sub>g()))"
shows   "(\<tau> \<Turnstile> not(\<delta>(S))) \<or> \<not> finite (Rep_Bag_base S \<tau>)"
apply(insert non_finite, simp)
apply(rule impI)
apply(simp add: OclSize_def OclValid_def defined_def bot_fun_def null_fun_def bot_option_def null_option_def
           split: if_split_asm)
done

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite (Rep_Bag_base X \<tau>) \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->size\<^sub>B\<^sub>a\<^sub>g())"
by(simp add: OclSize_def OclValid_def defined_def bot_fun_def false_def true_def)

lemma size_defined:
 assumes X_finite: "\<And>\<tau>. finite (Rep_Bag_base X \<tau>)"
 shows "\<delta> (X->size\<^sub>B\<^sub>a\<^sub>g()) = \<delta> X"
 apply(rule ext, simp add: cp_defined[of "X->size\<^sub>B\<^sub>a\<^sub>g()"] OclSize_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

lemma size_defined':
 assumes X_finite: "finite (Rep_Bag_base X \<tau>)"
 shows "(\<tau> \<Turnstile> \<delta> (X->size\<^sub>B\<^sub>a\<^sub>g())) = (\<tau> \<Turnstile> \<delta> X)"
 apply(simp add: cp_defined[of "X->size\<^sub>B\<^sub>a\<^sub>g()"] OclSize_def OclValid_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

text\<open>OclIsEmpty\<close>

lemma OclIsEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->isEmpty\<^sub>B\<^sub>a\<^sub>g()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: if_split_asm)
  apply(case_tac "(X->size\<^sub>B\<^sub>a\<^sub>g() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
  apply(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def)
by (metis (hide_lams, no_types)
           bot_fun_def OclValid_def defined_def foundation2 invalid_def)

lemma "\<tau> \<Turnstile> \<delta> (null->isEmpty\<^sub>B\<^sub>a\<^sub>g())"
by(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
              bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def null_is_valid
        split: if_split_asm)

lemma OclIsEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite (Rep_Bag_base X \<tau>) \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->isEmpty\<^sub>B\<^sub>a\<^sub>g())"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: if_split_asm)
  apply(case_tac "(X->size\<^sub>B\<^sub>a\<^sub>g() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
by(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def bot_fun_def false_def true_def invalid_def)

text\<open>OclNotEmpty\<close>

lemma OclNotEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->notEmpty\<^sub>B\<^sub>a\<^sub>g()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
by (metis (hide_lams, no_types) OclNotEmpty_def OclNot_defargs OclNot_not foundation6 foundation9
                                OclIsEmpty_defined_args_valid)

lemma "\<tau> \<Turnstile> \<delta> (null->notEmpty\<^sub>B\<^sub>a\<^sub>g())"
by (metis (hide_lams, no_types) OclNotEmpty_def OclAnd_false1 OclAnd_idem OclIsEmpty_def
                                OclNot3 OclNot4 OclOr_def defined2 defined4 transform1 valid2)

lemma OclNotEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite (Rep_Bag_base X \<tau>) \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->notEmpty\<^sub>B\<^sub>a\<^sub>g())"
 apply(simp add: OclNotEmpty_def)
 apply(drule OclIsEmpty_infinite, simp)
by (metis OclNot_defargs OclNot_not foundation6 foundation9)

lemma OclNotEmpty_has_elt : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                          \<tau> \<Turnstile> X->notEmpty\<^sub>B\<^sub>a\<^sub>g() \<Longrightarrow>
                          \<exists>e. e \<in> (Rep_Bag_base X \<tau>)"
proof -
 have s_non_empty: "\<And>S. S \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> S"
 by blast
show "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
      \<tau> \<Turnstile> X->notEmpty\<^sub>B\<^sub>a\<^sub>g() \<Longrightarrow>
      ?thesis"
 apply(simp add: OclNotEmpty_def OclIsEmpty_def deMorgan1 deMorgan2, drule foundation5)
 apply(subst (asm) (2) OclNot_def,
       simp add: OclValid_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def
            split: if_split_asm)
  prefer 2
  apply(simp add: invalid_def bot_option_def true_def)
 apply(simp add: OclSize_def valid_def split: if_split_asm,
       simp_all add: false_def true_def bot_option_def bot_fun_def OclInt0_def)
 apply(drule s_non_empty[of "Rep_Bag_base X \<tau>"], erule exE, case_tac x)
by blast
qed

lemma OclNotEmpty_has_elt' : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                          \<tau> \<Turnstile> X->notEmpty\<^sub>B\<^sub>a\<^sub>g() \<Longrightarrow>
                          \<exists>e. e \<in> (Rep_Set_base X \<tau>)"
 apply(drule OclNotEmpty_has_elt, simp)
by(simp add: Rep_Bag_base_def Rep_Set_base_def image_def)

text\<open>OclANY\<close>

lemma OclANY_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->any\<^sub>B\<^sub>a\<^sub>g()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def OclAnd_def
        split: bool.split_asm HOL.if_split_asm option.split)

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> X->isEmpty\<^sub>B\<^sub>a\<^sub>g() \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->any\<^sub>B\<^sub>a\<^sub>g())"
 apply(simp add: OclANY_def OclValid_def)
 apply(subst cp_defined, subst cp_OclAnd, simp add: OclNotEmpty_def, subst (1 2) cp_OclNot,
       simp add: cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_defined[symmetric],
       simp add: false_def true_def)
by(drule foundation20[simplified OclValid_def true_def], simp)

lemma OclANY_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>B\<^sub>a\<^sub>g())) = (\<tau> \<Turnstile> \<upsilon> X)"
proof -
 have A: "(\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>B\<^sub>a\<^sub>g())) \<Longrightarrow> ((\<tau> \<Turnstile>(\<upsilon> X)))"
          by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.if_split_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<upsilon> X)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>B\<^sub>a\<^sub>g()))"
           apply(auto simp: OclANY_def OclValid_def true_def false_def StrongEq_def
                            defined_def invalid_def valid_def bot_fun_def null_fun_def
                            bot_option_def null_option_def null_is_valid
                            OclAnd_def
                      split: bool.split_asm HOL.if_split_asm option.split)
           apply(frule Bag_inv_lemma[OF foundation16[THEN iffD2], OF conjI], simp)
           apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau>")
            prefer 2
            apply (metis (hide_lams, no_types) OclValid_def foundation16)
           apply(simp add: true_def,
                 drule OclNotEmpty_has_elt'[simplified OclValid_def true_def], simp)
           apply(erule exE,
                 rule someI2[where Q = "\<lambda>x. x \<noteq> \<bottom>" and P = "\<lambda>y. y \<in> (Rep_Set_base X \<tau>)",
                             simplified not_def, THEN mp], simp, auto)
          by(simp add: Rep_Set_base_def image_def)
 show ?thesis by(auto dest:A intro:B)
qed

lemma OclANY_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->any\<^sub>B\<^sub>a\<^sub>g()) = (\<upsilon> X)"
by(auto intro!: OclANY_valid_args_valid transform2_rev)

(* and higher order ones : forall, exists, iterate, select, reject... *)
text_raw\<open>\endisatagafp\<close> 

subsection\<open>Execution Laws with Invalid or Null or Infinite Set as Argument\<close>

text\<open>OclIncluding\<close> (* properties already generated by the corresponding locale *)

text\<open>OclExcluding\<close> (* properties already generated by the corresponding locale *)

text\<open>OclIncludes\<close> (* properties already generated by the corresponding locale *)

text\<open>OclExcludes\<close> (* properties already generated by the corresponding locale *)

text\<open>OclSize\<close>

lemma OclSize_invalid[simp,code_unfold]:"(invalid->size\<^sub>B\<^sub>a\<^sub>g()) = invalid"
by(simp add: bot_fun_def OclSize_def invalid_def defined_def valid_def false_def true_def)

lemma OclSize_null[simp,code_unfold]:"(null->size\<^sub>B\<^sub>a\<^sub>g()) = invalid"
by(rule ext,
   simp add: bot_fun_def null_fun_def null_is_valid OclSize_def
             invalid_def defined_def valid_def false_def true_def)

text\<open>OclIsEmpty\<close>

lemma OclIsEmpty_invalid[simp,code_unfold]:"(invalid->isEmpty\<^sub>B\<^sub>a\<^sub>g()) = invalid"
by(simp add: OclIsEmpty_def)

lemma OclIsEmpty_null[simp,code_unfold]:"(null->isEmpty\<^sub>B\<^sub>a\<^sub>g()) = true"
by(simp add: OclIsEmpty_def)

text\<open>OclNotEmpty\<close>

lemma OclNotEmpty_invalid[simp,code_unfold]:"(invalid->notEmpty\<^sub>B\<^sub>a\<^sub>g()) = invalid"
by(simp add: OclNotEmpty_def)

lemma OclNotEmpty_null[simp,code_unfold]:"(null->notEmpty\<^sub>B\<^sub>a\<^sub>g()) = false"
by(simp add: OclNotEmpty_def)

text\<open>OclANY\<close>

lemma OclANY_invalid[simp,code_unfold]:"(invalid->any\<^sub>B\<^sub>a\<^sub>g()) = invalid"
by(simp add: bot_fun_def OclANY_def invalid_def defined_def valid_def false_def true_def)

lemma OclANY_null[simp,code_unfold]:"(null->any\<^sub>B\<^sub>a\<^sub>g()) = null"
by(simp add: OclANY_def false_def true_def)

text\<open>OclForall\<close>

lemma OclForall_invalid[simp,code_unfold]:"invalid->forAll\<^sub>B\<^sub>a\<^sub>g(a| P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

lemma OclForall_null[simp,code_unfold]:"null->forAll\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

text\<open>OclExists\<close>

lemma OclExists_invalid[simp,code_unfold]:"invalid->exists\<^sub>B\<^sub>a\<^sub>g(a| P a) = invalid"
by(simp add: OclExists_def)

lemma OclExists_null[simp,code_unfold]:"null->exists\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: OclExists_def)

text\<open>OclIterate\<close>

lemma OclIterate_invalid[simp,code_unfold]:"invalid->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

lemma OclIterate_null[simp,code_unfold]:"null->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)


lemma OclIterate_invalid_args[simp,code_unfold]:"S->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

text\<open>An open question is this ...\<close>
lemma (*OclIterate_null_args[simp,code_unfold]:*) "S->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = null | P a x) = invalid"
oops
(* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *)

lemma OclIterate_infinite:
assumes non_finite: "\<tau> \<Turnstile> not(\<delta>(S->size\<^sub>B\<^sub>a\<^sub>g()))"
shows "(OclIterate S A F) \<tau> = invalid \<tau>"
apply(insert non_finite [THEN OclSize_infinite])
apply(subst (asm) foundation9, simp)
by(metis OclIterate_def OclValid_def invalid_def)

text\<open>OclSelect\<close>

lemma OclSelect_invalid[simp,code_unfold]:"invalid->select\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

lemma OclSelect_null[simp,code_unfold]:"null->select\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

text\<open>OclReject\<close>

lemma OclReject_invalid[simp,code_unfold]:"invalid->reject\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: OclReject_def)

lemma OclReject_null[simp,code_unfold]:"null->reject\<^sub>B\<^sub>a\<^sub>g(a | P a) = invalid"
by(simp add: OclReject_def)

text_raw\<open>\isatagafp\<close>

subsubsection\<open>Context Passing\<close>

lemma cp_OclIncludes1:
"(X->includes\<^sub>B\<^sub>a\<^sub>g(x)) \<tau> = (X->includes\<^sub>B\<^sub>a\<^sub>g(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclSize: "X->size\<^sub>B\<^sub>a\<^sub>g() \<tau> = ((\<lambda>_. X \<tau>)->size\<^sub>B\<^sub>a\<^sub>g()) \<tau>"
by(simp add: OclSize_def cp_defined[symmetric] Rep_Bag_base_def)

lemma cp_OclIsEmpty: "X->isEmpty\<^sub>B\<^sub>a\<^sub>g() \<tau> = ((\<lambda>_. X \<tau>)->isEmpty\<^sub>B\<^sub>a\<^sub>g()) \<tau>"
 apply(simp only: OclIsEmpty_def)
 apply(subst (2) cp_OclOr,
       subst cp_OclAnd,
       subst cp_OclNot,
       subst StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0)
by(simp add: cp_defined[symmetric] cp_valid[symmetric] StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric]
             cp_OclSize[symmetric] cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])

lemma cp_OclNotEmpty: "X->notEmpty\<^sub>B\<^sub>a\<^sub>g() \<tau> = ((\<lambda>_. X \<tau>)->notEmpty\<^sub>B\<^sub>a\<^sub>g()) \<tau>"
 apply(simp only: OclNotEmpty_def)
 apply(subst (2) cp_OclNot)
by(simp add: cp_OclNot[symmetric] cp_OclIsEmpty[symmetric])

lemma cp_OclANY: "X->any\<^sub>B\<^sub>a\<^sub>g() \<tau> = ((\<lambda>_. X \<tau>)->any\<^sub>B\<^sub>a\<^sub>g()) \<tau>"
 apply(simp only: OclANY_def)
 apply(subst (2) cp_OclAnd)
by(simp only: cp_OclAnd[symmetric] cp_defined[symmetric] cp_valid[symmetric]
              cp_OclNotEmpty[symmetric] Rep_Set_base_def)

lemma cp_OclForall:
"(S->forAll\<^sub>B\<^sub>a\<^sub>g(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->forAll\<^sub>B\<^sub>a\<^sub>g(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(auto simp add: OclForall_def cp_defined[symmetric] Rep_Set_base_def)

(* first-order version !*)
lemma cp_OclForall1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->forAll\<^sub>B\<^sub>a\<^sub>g(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclForall, simp)

lemma (*cp_OclForall2 [simp,intro!]:*)
"cp (\<lambda>X St x. P (\<lambda>\<tau>. x) X St) \<Longrightarrow> cp S \<Longrightarrow> cp (\<lambda>X. (S X)->forAll\<^sub>B\<^sub>a\<^sub>g(x|P x X)) "
apply(simp only: cp_def)
oops

lemma (*cp_OclForall:*)
"cp S \<Longrightarrow>
 (\<And> x. cp(P x)) \<Longrightarrow>
 cp(\<lambda>X. ((S X)->forAll\<^sub>B\<^sub>a\<^sub>g(x | P x X)))"
oops

lemma cp_OclExists:
"(S->exists\<^sub>B\<^sub>a\<^sub>g(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->exists\<^sub>B\<^sub>a\<^sub>g(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclExists_def OclNot_def, subst cp_OclForall, simp)

(* first-order version !*)
lemma cp_OclExists1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->exists\<^sub>B\<^sub>a\<^sub>g(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclExists,simp)

lemma cp_OclIterate: 
     "(X->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate\<^sub>B\<^sub>a\<^sub>g(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate_def cp_defined[symmetric] Rep_Bag_base_def)

lemma cp_OclSelect: "(X->select\<^sub>B\<^sub>a\<^sub>g(a | P a)) \<tau> =
                ((\<lambda> _. X \<tau>)->select\<^sub>B\<^sub>a\<^sub>g(a | P a)) \<tau>"
by(simp add: OclSelect_def cp_defined[symmetric] Rep_Set_base_def)

lemma cp_OclReject: "(X->reject\<^sub>B\<^sub>a\<^sub>g(a | P a)) \<tau> = ((\<lambda> _. X \<tau>)->reject\<^sub>B\<^sub>a\<^sub>g(a | P a)) \<tau>"
by(simp add: OclReject_def, subst cp_OclSelect, simp)

lemmas cp_intro''\<^sub>B\<^sub>a\<^sub>g[intro!,simp,code_unfold] =
       cp_OclSize      [THEN allI[THEN allI[THEN cpI1], of "OclSize"]]
       cp_OclIsEmpty   [THEN allI[THEN allI[THEN cpI1], of "OclIsEmpty"]]
       cp_OclNotEmpty  [THEN allI[THEN allI[THEN cpI1], of "OclNotEmpty"]]
       cp_OclANY       [THEN allI[THEN allI[THEN cpI1], of "OclANY"]]

subsubsection\<open>Const\<close>

lemma const_OclIncluding[simp,code_unfold] :
 assumes const_x : "const x"
     and const_S : "const S"
   shows  "const (S->including\<^sub>B\<^sub>a\<^sub>g(x))"
   proof -
     have A:"\<And>\<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<upsilon> x) \<Longrightarrow> (S->including\<^sub>B\<^sub>a\<^sub>g(x) \<tau>) = (S->including\<^sub>B\<^sub>a\<^sub>g(x) \<tau>')"
            apply(simp add: foundation18)
            apply(erule const_subst[OF const_x const_invalid],simp_all)
            by(rule const_charn[OF const_invalid])
     have B: "\<And> \<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<delta> S) \<Longrightarrow> (S->including\<^sub>B\<^sub>a\<^sub>g(x) \<tau>) = (S->including\<^sub>B\<^sub>a\<^sub>g(x) \<tau>')"
            apply(simp add: foundation16', elim disjE)
            apply(erule const_subst[OF const_S const_invalid],simp_all)
            apply(rule const_charn[OF const_invalid])
            apply(erule const_subst[OF const_S const_null],simp_all)
            by(rule const_charn[OF const_invalid])
     show ?thesis
       apply(simp only: const_def,intro allI, rename_tac \<tau> \<tau>')
       apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> x)", simp add: A)
       apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> S)", simp_all add: B)
       apply(frule_tac \<tau>'1= \<tau>' in  const_OclValid2[OF const_x, THEN iffD1])
       apply(frule_tac \<tau>'1= \<tau>' in  const_OclValid1[OF const_S, THEN iffD1])
       apply(simp add: OclIncluding_def OclValid_def)
       apply(subst (1 2) const_charn[OF const_x])
       apply(subst (1 2) const_charn[OF const_S])
       by simp
qed
text_raw\<open>\endisatagafp\<close>

subsection\<open>Test Statements\<close>

(*Assert   "(\<tau> \<Turnstile> (Bag{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Bag{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
Assert   "(\<tau> \<Turnstile> (Bag{\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Bag{\<lambda>_. \<lfloor>x\<rfloor>}))"*)

instantiation Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (equal)equal
begin
  definition "HOL.equal k l \<longleftrightarrow>  (k::('a::equal)Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) =  l"
  instance   by standard (rule equal_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
end

lemma equal_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_code [code]:
  "HOL.equal k (l::('a::{equal,null})Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<longleftrightarrow> Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e k = Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e l"
  by (auto simp add: equal Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Rep_Bag\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)

Assert   "\<tau> \<Turnstile> (Bag{} \<doteq> Bag{})" 

(*
Assert   "\<tau> \<Turnstile> not(Bag{\<one>,\<one>}      \<triangleq> Bag{\<one>})" 
Assert   "\<tau> \<Turnstile> (Bag{\<one>,\<two>}         \<triangleq> Bag{\<two>,\<one>}" 
Assert   "\<tau> \<Turnstile> (Bag{\<one>,null}      \<triangleq> Bag{null,\<one>}" 
Assert   "\<tau> \<Turnstile> (Bag{\<one>,invalid,\<two>} \<triangleq> invalid)"
Assert   "\<tau> \<Turnstile> (Bag{\<one>,\<two>}->including\<^sub>B\<^sub>a\<^sub>g(null) \<triangleq> Bag{\<one>,\<two>,null})"
*)

(* > *)

end
