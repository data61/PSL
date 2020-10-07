(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Set.thy --- Library definitions.
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


theory  UML_Set
imports "../basic_types/UML_Void"
        "../basic_types/UML_Boolean"
        "../basic_types/UML_Integer"
        "../basic_types/UML_String"
        "../basic_types/UML_Real"
begin

no_notation None ("\<bottom>")
section\<open>Collection Type Set: Operations \label{formal-set}\<close>

subsection\<open>As a Motivation for the (infinite) Type Construction: Type-Extensions as Sets 
             \label{sec:type-extensions}\<close>

text\<open>Our notion of typed set goes beyond the usual notion of a finite executable set and
is powerful enough to capture \emph{the extension of a type} in UML and OCL. This means
we can have in Featherweight OCL Sets containing all possible elements of a type, not only
those (finite) ones representable in a state. This holds for base types as well as class types,
although the notion for class-types --- involving object id's not occurring in a state ---
requires some care.

In a world with @{term invalid} and @{term null}, there are two notions extensions possible:
\begin{enumerate}
\item the set of all \emph{defined} values of a type @{term T}
      (for which we will introduce the constant  @{term T})
\item the set of all \emph{valid} values of a type @{term T}, so including @{term null}
      (for which we will introduce the constant  @{term T\<^sub>n\<^sub>u\<^sub>l\<^sub>l}).
\end{enumerate}
\<close>

text\<open>We define the set extensions for the base type @{term Integer} as follows:\<close>
definition Integer :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Integer \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  ((Some o Some) ` (UNIV::int set)))"

definition Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (Some ` (UNIV::int option set)))"

lemma Integer_defined : "\<delta> Integer = true"
apply(rule ext, auto simp: Integer_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

text\<open>This allows the theorems:

      \<open>\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer->includes\<^sub>S\<^sub>e\<^sub>t(x))\<close>
      \<open>\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> Integer  \<triangleq> (Integer->including\<^sub>S\<^sub>e\<^sub>t(x))\<close>

and

      \<open>\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->includes\<^sub>S\<^sub>e\<^sub>t(x))\<close>
      \<open>\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l  \<triangleq> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->including\<^sub>S\<^sub>e\<^sub>t(x))\<close>

which characterize the infiniteness of these sets by a recursive property on these sets.
\<close>

text\<open>In the same spirit, we proceed similarly for the remaining base types:\<close>

definition Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some) {Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Some None)})"

definition Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y :: "('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some) {})"

lemma Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def
                           bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by((subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def bot_Void_def),
   (subst (asm) Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def))+

lemma Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_defined : "\<delta> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y = true"
apply(rule ext, auto simp: Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def
                           bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by((subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, auto simp add: bot_option_def null_option_def bot_Void_def))+

lemma assumes "\<tau> \<Turnstile> \<delta> (V :: ('\<AA>,Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set)"
      shows   "\<tau> \<Turnstile> V \<triangleq> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
proof -
  have A:"\<And>x y. x \<noteq> {} \<Longrightarrow> \<exists>y. y\<in> x"
  by (metis all_not_in_conv)
show "?thesis"
  apply(case_tac "V \<tau>")
  proof - fix y show "V \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y \<Longrightarrow>
                      y \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)} \<Longrightarrow>
                      \<tau> \<Turnstile> V \<triangleq> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(insert assms, case_tac y, simp add: bot_option_def, simp add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def foundation16)
  apply(simp add: bot_option_def null_option_def)
  apply(erule disjE, metis OclValid_def defined_def foundation2 null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def true_def)
  proof - fix a show "V \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>a\<rfloor> \<Longrightarrow> \<forall>x\<in>\<lceil>a\<rceil>. x \<noteq> \<bottom> \<Longrightarrow> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(case_tac a, simp, insert assms, metis OclValid_def foundation16 null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def true_def)
  apply(simp)
  proof - fix aa show " V \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow> \<forall>x\<in>aa. x \<noteq> \<bottom> \<Longrightarrow> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<or> \<tau> \<Turnstile> V \<triangleq> Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y"
  apply(case_tac "aa = {}",
        rule disjI2,
        insert assms,
        simp add: Void\<^sub>e\<^sub>m\<^sub>p\<^sub>t\<^sub>y_def OclValid_def StrongEq_def true_def,
        rule disjI1)
  apply(subgoal_tac "aa = {Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>}", simp add: StrongEq_def OclValid_def true_def Void\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def)
  apply(drule A, erule exE)
  proof - fix y show "V \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow>
                      \<forall>x\<in>aa. x \<noteq> \<bottom> \<Longrightarrow>
                      \<tau> \<Turnstile> \<delta> V \<Longrightarrow>
                      y \<in> aa \<Longrightarrow>
                      aa = {Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>}"  
  apply(rule equalityI, rule subsetI, simp)
    proof - fix x show " V \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow>
             \<forall>x\<in>aa. x \<noteq> \<bottom> \<Longrightarrow> \<tau> \<Turnstile> \<delta> V \<Longrightarrow> y \<in> aa \<Longrightarrow> x \<in> aa \<Longrightarrow> x = Abs_Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
    apply(case_tac x, simp)
    by (metis bot_Void_def bot_option_def null_option_def)
  apply_end(simp_all)
  
  apply_end(erule ballE[where x = y], simp_all)
  apply_end(case_tac y,
            simp add: bot_option_def null_option_def OclValid_def defined_def split: if_split_asm,
            simp add: false_def true_def)
  qed (erule disjE, simp add: bot_Void_def, simp)
qed qed qed qed qed

definition Boolean :: "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Boolean \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  ((Some o Some) ` (UNIV::bool set)))"

definition Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (Some ` (UNIV::bool option set)))"

lemma Boolean_defined : "\<delta> Boolean = true"
apply(rule ext, auto simp: Boolean_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Boolean\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

definition String :: "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "String \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  ((Some o Some) ` (UNIV::string set)))"

definition String\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "String\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (Some ` (UNIV::string option set)))"

lemma String_defined : "\<delta> String = true"
apply(rule ext, auto simp: String_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma String\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> String\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: String\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

definition Real :: "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Real \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  ((Some o Some) ` (UNIV::real set)))"

definition Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e o Some o Some)  (Some ` (UNIV::real option set)))"

lemma Real_defined : "\<delta> Real = true"
apply(rule ext, auto simp: Real_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Real\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

subsection\<open>Basic Properties of the Set Type\<close>

text\<open>Every element in a defined set is valid.\<close>

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot"
apply(insert Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def
           split:if_split_asm)
 apply(erule contrapos_pp [of "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = bot"])
 apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
 apply(simp add: Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = null"])
apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
apply(simp add: Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse  null_option_def)
by (simp add: bot_option_def)

lemma Set_inv_lemma' :
 assumes x_def : "\<tau> \<Turnstile> \<delta> X"
     and e_mem : "e \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
   shows "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)"
 apply(rule Set_inv_lemma[OF x_def, THEN ballE[where x = e]])
  apply(simp add: foundation18')
by(simp add: e_mem)

lemma abs_rep_simp' :
 assumes S_all_def : "\<tau> \<Turnstile> \<delta> S"
   shows "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by(simp add: false_def true_def)
 show ?thesis
  apply(insert S_all_def, simp add: OclValid_def defined_def)
  apply(rule mp[OF Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau>
                                                    then false \<tau> else true \<tau>) = true \<tau> \<longrightarrow>
                                                   Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]],
        rename_tac S')
   apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse discr_eq_false_true)
   apply(case_tac S') apply(simp add: bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)+
   apply(rename_tac S'', case_tac S'') apply(simp add: null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)+
 done
qed

lemma S_lift' :
 assumes S_all_def : "(\<tau> :: '\<AA> st) \<Turnstile> \<delta> S"
   shows "\<exists>S'. (\<lambda>a (_::'\<AA> st). a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'\<AA> st). \<lfloor>a\<rfloor>) ` S'"
  apply(rule_tac x = "(\<lambda>a. \<lceil>a\<rceil>) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>" in exI)
  apply(simp only: image_comp)
  apply(simp add: comp_def)
  apply(rule image_cong, fast)
  (* *)
  apply(drule Set_inv_lemma'[OF S_all_def])
by(case_tac x, (simp add: bot_option_def foundation18')+)

lemma invalid_set_OclNot_defined [simp,code_unfold]:"\<delta>(invalid::('\<AA>,'\<alpha>::null) Set) = false" by simp
lemma null_set_OclNot_defined [simp,code_unfold]:"\<delta>(null::('\<AA>,'\<alpha>::null) Set) = false"
by(simp add: defined_def null_fun_def)
lemma invalid_set_valid [simp,code_unfold]:"\<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set) = false"
by simp
lemma null_set_valid [simp,code_unfold]:"\<upsilon>(null::('\<AA>,'\<alpha>::null) Set) = true"
apply(simp add: valid_def null_fun_def bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,simp_all add: null_option_def bot_option_def)
done

text\<open>... which means that we can have a type \<open>('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set\<close>
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
\<open>'\<AA>\<close> still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties
independently from a concrete class diagram.\<close>

subsection\<open>Definition: Strict Equality \label{sec:set-strict-equality}\<close>

text\<open>After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:\<close>

overloading
  StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>::null)Set] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>S\<^sub>e\<^sub>t :
    "(x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                       then (x \<triangleq> y)\<tau>
                                       else invalid \<tau>"
end

text\<open>One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its oid stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF-invariant), the referential equality and the
strong equality---and therefore the strict equality on sets in the sense above---coincides.\<close>

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>S\<^sub>e\<^sub>t : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y" 
         by unfold_locales (auto simp:  StrictRefEq\<^sub>S\<^sub>e\<^sub>t)



subsection\<open>Constants: mtSet\<close>
definition mtSet::"('\<AA>,'\<alpha>::null) Set"  ("Set{}")
where     "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{}::'\<alpha> set\<rfloor>\<rfloor> )"


lemma mtSet_defined[simp,code_unfold]:"\<delta>(Set{}) = true"
apply(rule ext, auto simp: mtSet_def defined_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                           bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma mtSet_valid[simp,code_unfold]:"\<upsilon>(Set{}) = true"
apply(rule ext,auto simp: mtSet_def valid_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                          bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def)

lemma mtSet_rep_set: "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Set{} \<tau>)\<rceil>\<rceil> = {}"
 apply(simp add: mtSet_def, subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
by(simp add: bot_option_def)+

lemma [simp,code_unfold]: "const Set{}"
by(simp add: const_def mtSet_def)


text\<open>Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid.\<close>

subsection\<open>Definition: Including\<close>

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclIncluding   ("_->including\<^sub>S\<^sub>e\<^sub>t'(_')")

interpretation OclIncluding : profile_bin\<^sub>d_\<^sub>v OclIncluding "\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> \<union> {y}\<rfloor>\<rfloor>"
proof -  
 have A : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" 
          by(simp add: null_option_def bot_option_def)
 have C : "\<And>x y. x \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> \<bottom>  \<Longrightarrow>
           \<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(auto intro!:Set_inv_lemma[simplified OclValid_def 
                                        defined_def false_def true_def null_fun_def bot_fun_def])          
         show "profile_bin\<^sub>d_\<^sub>v OclIncluding (\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> \<union> {y}\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclIncluding_def bot_option_def null_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" in contrapos_pp)
          apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF C A])
             apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF C B])
            apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         done
qed

syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}"     == "CONST OclIncluding (Set{}) x "


subsection\<open>Definition: Excluding\<close>

definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclExcluding x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> - {y \<tau>} \<rfloor>\<rfloor>
                                     else \<bottom> )"
notation   OclExcluding   ("_->excluding\<^sub>S\<^sub>e\<^sub>t'(_')")


lemma OclExcluding_inv: "(x:: Set('b::{null})) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> \<bottom>  \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> - {y}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix X :: "'a state \<times> 'a state \<Rightarrow> Set('b)" fix \<tau>
          show "x \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> ?thesis"
            when "x = X \<tau>"
  by(simp add: that Set_inv_lemma[simplified OclValid_def 
                                          defined_def null_fun_def bot_fun_def, of X \<tau>])
qed simp_all

interpretation OclExcluding : profile_bin\<^sub>d_\<^sub>v OclExcluding "\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> - {y}\<rfloor>\<rfloor>"
proof -  
 have A : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" 
          by(simp add: null_option_def bot_option_def)
         show "profile_bin\<^sub>d_\<^sub>v OclExcluding (\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x:: Set('b))\<rceil>\<rceil> - {y}\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclExcluding_def bot_option_def null_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def invalid_def)
          apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> - {y}\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" in contrapos_pp)
          apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclExcluding_inv A])
             apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> - {y}\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclExcluding_inv B])
            apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         done
qed


subsection\<open>Definition: Includes\<close>

definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then \<lfloor>\<lfloor>(y \<tau>) \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                     else \<bottom>  )"
notation   OclIncludes    ("_->includes\<^sub>S\<^sub>e\<^sub>t'(_')" (*[66,65]65*))

interpretation OclIncludes : profile_bin\<^sub>d_\<^sub>v OclIncludes "\<lambda>x y. \<lfloor>\<lfloor>y \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclIncludes_def bot_option_def null_option_def invalid_def)


subsection\<open>Definition: Excludes\<close>

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"
notation   OclExcludes    ("_->excludes\<^sub>S\<^sub>e\<^sub>t'(_')" (*[66,65]65*))

text\<open>The case of the size definition is somewhat special, we admit
explicitly in Featherweight OCL the possibility of infinite sets. For
the size definition, this requires an extra condition that assures
that the cardinality of the set is actually a defined integer.\<close>

interpretation OclExcludes : profile_bin\<^sub>d_\<^sub>v OclExcludes "\<lambda>x y. \<lfloor>\<lfloor>y \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclExcludes_def OclIncludes_def OclNot_def bot_option_def null_option_def invalid_def)

subsection\<open>Definition: Size\<close>

definition OclSize     :: "('\<AA>,'\<alpha>::null)Set \<Rightarrow> '\<AA> Integer"
where     "OclSize x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> finite(\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>)
                             then \<lfloor>\<lfloor> int(card \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>) \<rfloor>\<rfloor>
                             else \<bottom> )"
notation  (* standard ascii syntax *)
           OclSize        ("_->size\<^sub>S\<^sub>e\<^sub>t'(')" (*[66]*))

text\<open>The following definition follows the requirement of the
standard to treat null as neutral element of sets. It is
a well-documented exception from the general strictness
rule and the rule that the distinguished argument self should
be non-null.\<close>

(*TODO Locale - Equivalent*)  


subsection\<open>Definition: IsEmpty\<close>

definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty\<^sub>S\<^sub>e\<^sub>t'(')" (*[66]*))

(*TODO Locale - Equivalent*)  


subsection\<open>Definition: NotEmpty\<close>

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty\<^sub>S\<^sub>e\<^sub>t'(')" (*[66]*))

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Any\<close>

(* Slight breach of naming convention in order to avoid naming conflict on constant.*)
definition OclANY   :: "[('\<AA>,'\<alpha>::null) Set] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclANY x = (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau>
                            then if (\<delta> x and OclNotEmpty x) \<tau> = true \<tau>
                                 then SOME y. y \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>
                                 else null \<tau>
                            else \<bottom> )"
notation   OclANY   ("_->any\<^sub>S\<^sub>e\<^sub>t'(')")

(*TODO Locale - Equivalent*)  

(* actually, this definition covers only: X->any\<^sub>S\<^sub>e\<^sub>t(true) of the standard, which foresees
a (totally correct) high-level definition
source->any\<^sub>S\<^sub>e\<^sub>t(iterator | body) =
source->select(iterator | body)->asSequence()->first(). Since we don't have sequences,
we have to go for a direct---restricted---definition. *)



subsection\<open>Definition: Forall\<close>

text\<open>The definition of OclForall mimics the one of @{term "OclAnd"}:
OclForall is not a strict operation.\<close>
definition OclForall     :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = false \<tau>)
                                      then false \<tau>
                                      else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = invalid \<tau>)
                                           then invalid \<tau>
                                           else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = null \<tau>)
                                                then null \<tau>
                                                else true \<tau>
                                 else \<bottom>)"
syntax
  "_OclForallSet" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forAll\<^sub>S\<^sub>e\<^sub>t'(_|_')")
translations
  "X->forAll\<^sub>S\<^sub>e\<^sub>t(x | P)" == "CONST UML_Set.OclForall X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Exists\<close>
  
text\<open>Like OclForall, OclExists is also not strict.\<close>
definition OclExists     :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = not(UML_Set.OclForall S (\<lambda> X. not (P X)))"

syntax
  "_OclExistSet" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists\<^sub>S\<^sub>e\<^sub>t'(_|_')")
translations
  "X->exists\<^sub>S\<^sub>e\<^sub>t(x | P)" == "CONST UML_Set.OclExists X (%x. P)"

(*TODO Locale - Equivalent*)  
  
subsection\<open>Definition: Iterate\<close>

definition OclIterate :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<beta>::null)val,
                             ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where "OclIterate S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>
                                  then (Finite_Set.fold (F) (A) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))\<tau>
                                  else \<bottom>)"
syntax
  "_OclIterateSet"  :: "[('\<AA>,'\<alpha>::null) Set, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate\<^sub>S\<^sub>e\<^sub>t'(_;_=_ | _')" (*[71,100,70]50*))
translations
  "X->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P)" == "CONST OclIterate X A (%a. (% x. P))"

(*TODO Locale - Equivalent*)  
  
subsection\<open>Definition: Select\<close>

definition OclSelect :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>)Set"
where "OclSelect S P = (\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau>
                              then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = invalid \<tau>)
                                   then invalid \<tau>
                                   else Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x\<in>\<lceil>\<lceil> Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}\<rfloor>\<rfloor>
                              else invalid \<tau>)"
syntax
  "_OclSelectSet" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->select\<^sub>S\<^sub>e\<^sub>t'(_|_')")
translations
  "X->select\<^sub>S\<^sub>e\<^sub>t(x | P)" == "CONST OclSelect X (% x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Reject\<close>

definition OclReject :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>::null)Set"
where "OclReject S P = OclSelect S (not o P)"
syntax
  "_OclRejectSet" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->reject\<^sub>S\<^sub>e\<^sub>t'(_|_')")
translations
  "X->reject\<^sub>S\<^sub>e\<^sub>t(x | P)" == "CONST OclReject X (% x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: IncludesAll\<close>

definition OclIncludesAll   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludesAll x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation   OclIncludesAll ("_->includesAll\<^sub>S\<^sub>e\<^sub>t'(_')" (*[66,65]65*))

interpretation OclIncludesAll : profile_bin\<^sub>d_\<^sub>d OclIncludesAll "\<lambda>x y. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclIncludesAll_def bot_option_def null_option_def invalid_def)

subsection\<open>Definition: ExcludesAll\<close>

definition OclExcludesAll   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludesAll x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> = {} \<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation  OclExcludesAll ("_->excludesAll\<^sub>S\<^sub>e\<^sub>t'(_')" (*[66,65]65*))

interpretation OclExcludesAll : profile_bin\<^sub>d_\<^sub>d OclExcludesAll "\<lambda>x y. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> = {}\<rfloor>\<rfloor>"
by(unfold_locales, auto simp:OclExcludesAll_def bot_option_def null_option_def invalid_def)

subsection\<open>Definition: Union\<close>

definition OclUnion   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclUnion x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation   OclUnion       ("_->union\<^sub>S\<^sub>e\<^sub>t'(_')"          (*[66,65]65*))

lemma OclUnion_inv: "(x:: Set('b::{null})) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> \<bottom>  \<Longrightarrow> y \<noteq> null \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix X Y :: "'a state \<times> 'a state \<Rightarrow> Set('b)" fix \<tau>
          show "x \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> y \<noteq> null \<Longrightarrow> ?thesis"
            when "x = X \<tau>" "y = Y \<tau>"
  by(auto simp: that,
     insert
       Set_inv_lemma[simplified OclValid_def 
                                          defined_def null_fun_def bot_fun_def, of Y \<tau>]
       Set_inv_lemma[simplified OclValid_def 
                                          defined_def null_fun_def bot_fun_def, of X \<tau>],
     auto)
qed simp_all

interpretation OclUnion : profile_bin\<^sub>d_\<^sub>d OclUnion "\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -  
 have A : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" 
          by(simp add: null_option_def bot_option_def)
         show "profile_bin\<^sub>d_\<^sub>d OclUnion (\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclUnion_def bot_option_def null_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def invalid_def)
          apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" in contrapos_pp)
          apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclUnion_inv A])
             apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<union> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclUnion_inv B])
            apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         done
qed

subsection\<open>Definition: Intersection\<close>

definition OclIntersection   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIntersection x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                        then Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> 
                                                         \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>
                                        else \<bottom>  )"
notation   OclIntersection("_->intersection\<^sub>S\<^sub>e\<^sub>t'(_')"   (*[71,70]70*))

lemma OclIntersection_inv: "(x:: Set('b::{null})) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> \<bottom>  \<Longrightarrow> y \<noteq> null \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix X Y :: "'a state \<times> 'a state \<Rightarrow> Set('b)" fix \<tau>
          show "x \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> y \<noteq> null \<Longrightarrow> ?thesis"
            when "x = X \<tau>" "y = Y \<tau>"
  by(auto simp: that,
     insert
       Set_inv_lemma[simplified OclValid_def 
                                          defined_def null_fun_def bot_fun_def, of Y \<tau>]
       Set_inv_lemma[simplified OclValid_def 
                                          defined_def null_fun_def bot_fun_def, of X \<tau>],
     auto)
qed simp_all

interpretation OclIntersection : profile_bin\<^sub>d_\<^sub>d OclIntersection "\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -  
 have A : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" 
          by(simp add: null_option_def bot_option_def)
         show "profile_bin\<^sub>d_\<^sub>d OclIntersection (\<lambda>x y. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclIntersection_def bot_option_def null_option_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def invalid_def)
          apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" in contrapos_pp)
          apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclIntersection_inv A])
             apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil> \<inter> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF OclIntersection_inv B])
            apply(simp_all add:  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         done
qed

subsection\<open>Definition (future operators)\<close>

consts (* abstract set collection operations *)
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"
    OclSum         :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"
  
notation  OclCount       ("_->count\<^sub>S\<^sub>e\<^sub>t'(_')" (*[66,65]65*))
notation  OclSum         ("_->sum\<^sub>S\<^sub>e\<^sub>t'(')" (*[66]*))

subsection\<open>Logical Properties\<close>

text\<open>OclIncluding\<close>

lemma OclIncluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->including\<^sub>S\<^sub>e\<^sub>t(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis (hide_lams, no_types) OclIncluding.def_valid_then_def OclIncluding.defined_args_valid)

lemma OclIncluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->including\<^sub>S\<^sub>e\<^sub>t(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclIncluding.def_valid_then_def)

text\<open>etc. etc.\<close>
text_raw\<open>\isatagafp\<close> 

text\<open>OclExcluding\<close>

lemma OclExcluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excluding\<^sub>S\<^sub>e\<^sub>t(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis OclExcluding.def_valid_then_def OclExcluding.defined_args_valid)

lemma OclExcluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excluding\<^sub>S\<^sub>e\<^sub>t(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclExcluding.def_valid_then_def)

text\<open>OclIncludes\<close>

lemma OclIncludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->includes\<^sub>S\<^sub>e\<^sub>t(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (simp add: OclIncludes.def_valid_then_def foundation10')

lemma OclIncludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->includes\<^sub>S\<^sub>e\<^sub>t(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclIncludes.def_valid_then_def)

text\<open>OclExcludes\<close>

lemma OclExcludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excludes\<^sub>S\<^sub>e\<^sub>t(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (simp add: OclExcludes.def_valid_then_def foundation10')

lemma OclExcludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excludes\<^sub>S\<^sub>e\<^sub>t(x)) = ((\<delta> X) and (\<upsilon> x))"
by (simp add: OclExcludes.def_valid_then_def)

text\<open>OclSize\<close>

lemma OclSize_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->size\<^sub>S\<^sub>e\<^sub>t()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclSize_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def
        split: bool.split_asm HOL.if_split_asm option.split)

lemma OclSize_infinite:
assumes non_finite:"\<tau> \<Turnstile> not(\<delta>(S->size\<^sub>S\<^sub>e\<^sub>t()))"
shows   "(\<tau> \<Turnstile> not(\<delta>(S))) \<or> \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
apply(insert non_finite, simp)
apply(rule impI)
apply(simp add: OclSize_def OclValid_def defined_def)
apply(case_tac "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>",
      simp_all add:null_fun_def null_option_def bot_fun_def bot_option_def)
done

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())"
by(simp add: OclSize_def OclValid_def defined_def bot_fun_def false_def true_def)

lemma size_defined:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> (X->size\<^sub>S\<^sub>e\<^sub>t()) = \<delta> X"
 apply(rule ext, simp add: cp_defined[of "X->size\<^sub>S\<^sub>e\<^sub>t()"] OclSize_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

lemma size_defined':
 assumes X_finite: "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 shows "(\<tau> \<Turnstile> \<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())) = (\<tau> \<Turnstile> \<delta> X)"
 apply(simp add: cp_defined[of "X->size\<^sub>S\<^sub>e\<^sub>t()"] OclSize_def OclValid_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

text\<open>OclIsEmpty\<close>

lemma OclIsEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->isEmpty\<^sub>S\<^sub>e\<^sub>t()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: if_split_asm)
  apply(case_tac "(X->size\<^sub>S\<^sub>e\<^sub>t() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
  apply(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def)
by (metis (hide_lams, no_types)
           bot_fun_def OclValid_def defined_def foundation2 invalid_def)

lemma "\<tau> \<Turnstile> \<delta> (null->isEmpty\<^sub>S\<^sub>e\<^sub>t())"
by(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
              bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def null_is_valid
        split: if_split_asm)

lemma OclIsEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->isEmpty\<^sub>S\<^sub>e\<^sub>t())"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: if_split_asm)
  apply(case_tac "(X->size\<^sub>S\<^sub>e\<^sub>t() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
by(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def bot_fun_def false_def true_def invalid_def)

text\<open>OclNotEmpty\<close>

lemma OclNotEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->notEmpty\<^sub>S\<^sub>e\<^sub>t()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
by (metis (hide_lams, no_types) OclNotEmpty_def OclNot_defargs OclNot_not foundation6 foundation9
                                OclIsEmpty_defined_args_valid)

lemma "\<tau> \<Turnstile> \<delta> (null->notEmpty\<^sub>S\<^sub>e\<^sub>t())"
by (metis (hide_lams, no_types) OclNotEmpty_def OclAnd_false1 OclAnd_idem OclIsEmpty_def
                                OclNot3 OclNot4 OclOr_def defined2 defined4 transform1 valid2)

lemma OclNotEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->notEmpty\<^sub>S\<^sub>e\<^sub>t())"
 apply(simp add: OclNotEmpty_def)
 apply(drule OclIsEmpty_infinite, simp)
by (metis OclNot_defargs OclNot_not foundation6 foundation9)

lemma OclNotEmpty_has_elt : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                          \<tau> \<Turnstile> X->notEmpty\<^sub>S\<^sub>e\<^sub>t() \<Longrightarrow>
                          \<exists>e. e \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclNotEmpty_def OclIsEmpty_def deMorgan1 deMorgan2, drule foundation5)
 apply(subst (asm) (2) OclNot_def,
       simp add: OclValid_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def
            split: if_split_asm)
  prefer 2
  apply(simp add: invalid_def bot_option_def true_def)
 apply(simp add: OclSize_def valid_def split: if_split_asm,
       simp_all add: false_def true_def bot_option_def bot_fun_def OclInt0_def)
by (metis equals0I)

text\<open>OclANY\<close>

lemma OclANY_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->any\<^sub>S\<^sub>e\<^sub>t()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def OclAnd_def
        split: bool.split_asm HOL.if_split_asm option.split)

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> X->isEmpty\<^sub>S\<^sub>e\<^sub>t() \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->any\<^sub>S\<^sub>e\<^sub>t())"
 apply(simp add: OclANY_def OclValid_def)
 apply(subst cp_defined, subst cp_OclAnd, simp add: OclNotEmpty_def, subst (1 2) cp_OclNot,
       simp add: cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_defined[symmetric],
       simp add: false_def true_def)
by(drule foundation20[simplified OclValid_def true_def], simp)

lemma OclANY_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>S\<^sub>e\<^sub>t())) = (\<tau> \<Turnstile> \<upsilon> X)"
proof -
 have A: "(\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>S\<^sub>e\<^sub>t())) \<Longrightarrow> ((\<tau> \<Turnstile>(\<upsilon> X)))"
          by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.if_split_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<upsilon> X)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->any\<^sub>S\<^sub>e\<^sub>t()))"
           apply(auto simp: OclANY_def OclValid_def true_def false_def StrongEq_def
                            defined_def invalid_def valid_def bot_fun_def null_fun_def
                            bot_option_def null_option_def null_is_valid
                            OclAnd_def
                      split: bool.split_asm HOL.if_split_asm option.split)
           apply(frule Set_inv_lemma[OF foundation16[THEN iffD2], OF conjI], simp)
           apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau>")
            prefer 2
            apply (metis (hide_lams, no_types) OclValid_def foundation16)
           apply(simp add: true_def,
                 drule OclNotEmpty_has_elt[simplified OclValid_def true_def], simp)
          by(erule exE,
             insert someI2[where Q = "\<lambda>x. x \<noteq> \<bottom>" and P = "\<lambda>y. y \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"],
             simp)
 show ?thesis by(auto dest:A intro:B)
qed

lemma OclANY_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->any\<^sub>S\<^sub>e\<^sub>t()) = (\<upsilon> X)"
by(auto intro!: OclANY_valid_args_valid transform2_rev)

(* and higher order ones : forall, exists, iterate, select, reject... *)
text_raw\<open>\endisatagafp\<close> 

subsection\<open>Execution Laws with Invalid or Null or Infinite Set as Argument\<close>

text\<open>OclIncluding\<close> (* properties already generated by the corresponding locale *)

text\<open>OclExcluding\<close> (* properties already generated by the corresponding locale *)

text\<open>OclIncludes\<close> (* properties already generated by the corresponding locale *)

text\<open>OclExcludes\<close> (* properties already generated by the corresponding locale *)

text\<open>OclSize\<close>

lemma OclSize_invalid[simp,code_unfold]:"(invalid->size\<^sub>S\<^sub>e\<^sub>t()) = invalid"
by(simp add: bot_fun_def OclSize_def invalid_def defined_def valid_def false_def true_def)

lemma OclSize_null[simp,code_unfold]:"(null->size\<^sub>S\<^sub>e\<^sub>t()) = invalid"
by(rule ext,
   simp add: bot_fun_def null_fun_def null_is_valid OclSize_def
             invalid_def defined_def valid_def false_def true_def)

text\<open>OclIsEmpty\<close>

lemma OclIsEmpty_invalid[simp,code_unfold]:"(invalid->isEmpty\<^sub>S\<^sub>e\<^sub>t()) = invalid"
by(simp add: OclIsEmpty_def)

lemma OclIsEmpty_null[simp,code_unfold]:"(null->isEmpty\<^sub>S\<^sub>e\<^sub>t()) = true"
by(simp add: OclIsEmpty_def)

text\<open>OclNotEmpty\<close>

lemma OclNotEmpty_invalid[simp,code_unfold]:"(invalid->notEmpty\<^sub>S\<^sub>e\<^sub>t()) = invalid"
by(simp add: OclNotEmpty_def)

lemma OclNotEmpty_null[simp,code_unfold]:"(null->notEmpty\<^sub>S\<^sub>e\<^sub>t()) = false"
by(simp add: OclNotEmpty_def)

text\<open>OclANY\<close>

lemma OclANY_invalid[simp,code_unfold]:"(invalid->any\<^sub>S\<^sub>e\<^sub>t()) = invalid"
by(simp add: bot_fun_def OclANY_def invalid_def defined_def valid_def false_def true_def)

lemma OclANY_null[simp,code_unfold]:"(null->any\<^sub>S\<^sub>e\<^sub>t()) = null"
by(simp add: OclANY_def false_def true_def)

text\<open>OclForall\<close>

lemma OclForall_invalid[simp,code_unfold]:"invalid->forAll\<^sub>S\<^sub>e\<^sub>t(a| P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

lemma OclForall_null[simp,code_unfold]:"null->forAll\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

text\<open>OclExists\<close>

lemma OclExists_invalid[simp,code_unfold]:"invalid->exists\<^sub>S\<^sub>e\<^sub>t(a| P a) = invalid"
by(simp add: OclExists_def)

lemma OclExists_null[simp,code_unfold]:"null->exists\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: OclExists_def)

text\<open>OclIterate\<close>

lemma OclIterate_invalid[simp,code_unfold]:"invalid->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

lemma OclIterate_null[simp,code_unfold]:"null->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)


lemma OclIterate_invalid_args[simp,code_unfold]:"S->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

text\<open>An open question is this ...\<close>
lemma (*OclIterate_null_args[simp,code_unfold]:*) "S->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = null | P a x) = invalid"
oops
(* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *)

lemma OclIterate_infinite:
assumes non_finite: "\<tau> \<Turnstile> not(\<delta>(S->size\<^sub>S\<^sub>e\<^sub>t()))"
shows "(OclIterate S A F) \<tau> = invalid \<tau>"
apply(insert non_finite [THEN OclSize_infinite])
apply(subst (asm) foundation9, simp)
by(metis OclIterate_def OclValid_def invalid_def)

text\<open>OclSelect\<close>

lemma OclSelect_invalid[simp,code_unfold]:"invalid->select\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

lemma OclSelect_null[simp,code_unfold]:"null->select\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

text\<open>OclReject\<close>

lemma OclReject_invalid[simp,code_unfold]:"invalid->reject\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: OclReject_def)

lemma OclReject_null[simp,code_unfold]:"null->reject\<^sub>S\<^sub>e\<^sub>t(a | P a) = invalid"
by(simp add: OclReject_def)

text_raw\<open>\isatagafp\<close>

subsubsection\<open>Context Passing\<close>

lemma cp_OclIncludes1:
"(X->includes\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = (X->includes\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclSize: "X->size\<^sub>S\<^sub>e\<^sub>t() \<tau> = ((\<lambda>_. X \<tau>)->size\<^sub>S\<^sub>e\<^sub>t()) \<tau>"
by(simp add: OclSize_def cp_defined[symmetric])

lemma cp_OclIsEmpty: "X->isEmpty\<^sub>S\<^sub>e\<^sub>t() \<tau> = ((\<lambda>_. X \<tau>)->isEmpty\<^sub>S\<^sub>e\<^sub>t()) \<tau>"
 apply(simp only: OclIsEmpty_def)
 apply(subst (2) cp_OclOr,
       subst cp_OclAnd,
       subst cp_OclNot,
       subst StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0)
by(simp add: cp_defined[symmetric] cp_valid[symmetric] StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric]
             cp_OclSize[symmetric] cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])

lemma cp_OclNotEmpty: "X->notEmpty\<^sub>S\<^sub>e\<^sub>t() \<tau> = ((\<lambda>_. X \<tau>)->notEmpty\<^sub>S\<^sub>e\<^sub>t()) \<tau>"
 apply(simp only: OclNotEmpty_def)
 apply(subst (2) cp_OclNot)
by(simp add: cp_OclNot[symmetric] cp_OclIsEmpty[symmetric])

lemma cp_OclANY: "X->any\<^sub>S\<^sub>e\<^sub>t() \<tau> = ((\<lambda>_. X \<tau>)->any\<^sub>S\<^sub>e\<^sub>t()) \<tau>"
 apply(simp only: OclANY_def)
 apply(subst (2) cp_OclAnd)
by(simp only: cp_OclAnd[symmetric] cp_defined[symmetric] cp_valid[symmetric]
              cp_OclNotEmpty[symmetric])

lemma cp_OclForall:
"(S->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->forAll\<^sub>S\<^sub>e\<^sub>t(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall_def cp_defined[symmetric])

(* first-order version !*)
lemma cp_OclForall1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclForall, simp)

lemma (*cp_OclForall2 [simp,intro!]:*)
"cp (\<lambda>X St x. P (\<lambda>\<tau>. x) X St) \<Longrightarrow> cp S \<Longrightarrow> cp (\<lambda>X. (S X)->forAll\<^sub>S\<^sub>e\<^sub>t(x|P x X)) "
apply(simp only: cp_def)
oops

lemma (*cp_OclForall:*)
"cp S \<Longrightarrow>
 (\<And> x. cp(P x)) \<Longrightarrow>
 cp(\<lambda>X. ((S X)->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x X)))"
oops

lemma cp_OclExists:
"(S->exists\<^sub>S\<^sub>e\<^sub>t(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->exists\<^sub>S\<^sub>e\<^sub>t(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclExists_def OclNot_def, subst cp_OclForall, simp)

(* first-order version !*)
lemma cp_OclExists1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->exists\<^sub>S\<^sub>e\<^sub>t(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclExists,simp)

lemma cp_OclIterate: 
     "(X->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate_def cp_defined[symmetric])

lemma cp_OclSelect: "(X->select\<^sub>S\<^sub>e\<^sub>t(a | P a)) \<tau> =
                ((\<lambda> _. X \<tau>)->select\<^sub>S\<^sub>e\<^sub>t(a | P a)) \<tau>"
by(simp add: OclSelect_def cp_defined[symmetric])

lemma cp_OclReject: "(X->reject\<^sub>S\<^sub>e\<^sub>t(a | P a)) \<tau> = ((\<lambda> _. X \<tau>)->reject\<^sub>S\<^sub>e\<^sub>t(a | P a)) \<tau>"
by(simp add: OclReject_def, subst cp_OclSelect, simp)

lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>t[intro!,simp,code_unfold] =
       cp_OclSize      [THEN allI[THEN allI[THEN cpI1], of "OclSize"]]
       cp_OclIsEmpty   [THEN allI[THEN allI[THEN cpI1], of "OclIsEmpty"]]
       cp_OclNotEmpty  [THEN allI[THEN allI[THEN cpI1], of "OclNotEmpty"]]
       cp_OclANY       [THEN allI[THEN allI[THEN cpI1], of "OclANY"]]

subsubsection\<open>Const\<close>

lemma const_OclIncluding[simp,code_unfold] :
 assumes const_x : "const x"
     and const_S : "const S"
   shows  "const (S->including\<^sub>S\<^sub>e\<^sub>t(x))"
   proof -
     have A:"\<And>\<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<upsilon> x) \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>) = (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>')"
            apply(simp add: foundation18)
            apply(erule const_subst[OF const_x const_invalid],simp_all)
            by(rule const_charn[OF const_invalid])
     have B: "\<And> \<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<delta> S) \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>) = (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>')"
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
       apply(subst const_charn[OF const_x])
       apply(subst const_charn[OF const_S])
       by simp
qed
text_raw\<open>\endisatagafp\<close>

subsection\<open>General Algebraic Execution Rules\<close>
subsubsection\<open>Execution Rules on Including\<close>

lemma OclIncluding_finite_rep_set :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert X_def x_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclIncluding_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma OclIncluding_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = insert \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclIncluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF S_def], metis bot_option_def not_Some_eq)
 by(simp)

lemma OclIncluding_notempty_rep_set:
 assumes X_def: "\<tau> \<Turnstile> \<delta> X"
     and a_val: "\<tau> \<Turnstile> \<upsilon> a"
  shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(a) \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(simp add: OclIncluding_def X_def[simplified OclValid_def] a_val[simplified OclValid_def])
 apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF X_def], metis a_val foundation18')
 by(simp)

lemma OclIncluding_includes0:
 assumes "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x)"
   shows "X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau> = X \<tau>"
proof -
 have includes_def: "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
 by (metis bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

 have includes_val: "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
 using foundation5 foundation6 by fastforce

 show ?thesis
  apply(insert includes_def[OF assms] includes_val[OF assms] assms,
        simp add: OclIncluding_def OclIncludes_def OclValid_def true_def)
  apply(drule insert_absorb, simp, subst abs_rep_simp')
 by(simp_all add: OclValid_def true_def)
qed

lemma OclIncluding_includes:
 assumes "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x)"
   shows "\<tau> \<Turnstile> X->including\<^sub>S\<^sub>e\<^sub>t(x) \<triangleq> X"
by(simp add: StrongEq_def OclValid_def true_def OclIncluding_includes0[OF assms])

lemma OclIncluding_commute0 :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a::null) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) \<triangleq> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
proof -
  have A : "\<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def i_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
  have B : "\<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def j_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)

  have G1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
           by(insert A, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
           by(insert A, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G3 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
           by(insert B, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G4 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
           by(insert B, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

  have *   : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def S_def i_val G1 G2)

  have **  : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def S_def i_val G3 G4)

  have *** : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert(j \<tau>)\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>insert(i \<tau>)\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)\<rceil>\<rceil>\<rfloor>\<rfloor> =
              Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert(i \<tau>)\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>insert(j \<tau>)\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)\<rceil>\<rceil>\<rfloor>\<rfloor>"
              by(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF A] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF B] Set.insert_commute)
  show ?thesis
     apply(simp add: OclIncluding_def S_def[simplified OclValid_def]
                  i_val[simplified OclValid_def] j_val[simplified OclValid_def]
                  true_def OclValid_def StrongEq_def)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def ** ***)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * )
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * **)
     done
qed


lemma OclIncluding_commute[simp,code_unfold]:
"((S :: ('\<AA>, 'a::null) Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j) = (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A': "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B:"\<And> \<tau>.   \<tau> \<Turnstile> (j \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B':"\<And> \<tau>.   \<tau> \<Turnstile> (j \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(j)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<upsilon> j)")
      apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
       apply(simp only: OclIncluding_commute0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
     apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
    apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 B[OF foundation22[THEN iffD2]] B'[OF foundation22[THEN iffD2]])
  apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
 done
qed


subsubsection\<open>Execution Rules on Excluding\<close>

lemma OclExcluding_finite_rep_set :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert X_def x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclExcluding_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma OclExcluding_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->excluding\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {\<lfloor>\<lfloor>x\<rfloor>\<rfloor>}"
 apply(simp add: OclExcluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def null_option_def)
  apply(insert Set_inv_lemma[OF S_def], metis Diff_iff bot_option_def not_None_eq)
by(simp)

lemma OclExcluding_excludes0:
 assumes "\<tau> \<Turnstile> X->excludes\<^sub>S\<^sub>e\<^sub>t(x)"
   shows "X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau> = X \<tau>"
proof -
 have excludes_def: "\<tau> \<Turnstile> X->excludes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
 by (metis OclExcludes.def_valid_then_def OclExcludes_valid_args_valid'' foundation10' foundation6)

 have excludes_val: "\<tau> \<Turnstile> X->excludes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
 by (metis OclExcludes.def_valid_then_def OclExcludes_valid_args_valid'' foundation10' foundation6)

 show ?thesis
  apply(insert excludes_def[OF assms] excludes_val[OF assms] assms,
        simp add: OclExcluding_def OclExcludes_def OclIncludes_def OclNot_def OclValid_def true_def)
 by (metis (hide_lams, no_types) abs_rep_simp' assms excludes_def)
qed

lemma OclExcluding_excludes:
 assumes "\<tau> \<Turnstile> X->excludes\<^sub>S\<^sub>e\<^sub>t(x)"
   shows "\<tau> \<Turnstile> X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<triangleq> X"
by(simp add: StrongEq_def OclValid_def true_def OclExcluding_excludes0[OF assms])

lemma OclExcluding_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> ((Set{}->excluding\<^sub>S\<^sub>e\<^sub>t(x))  \<triangleq>  Set{})"
proof -
  have A : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  by(simp add: null_option_def bot_option_def)
  have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)

  show ?thesis using val_x
    apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def StrongEq_def
                     OclExcluding_def mtSet_def defined_def bot_fun_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
     apply(auto simp: mtSet_def Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse
                      Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF B A])
  done
qed

lemma OclExcluding_commute0 :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a::null) Set)->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j) \<triangleq> (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)))"
proof -
  have A : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def i_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
  have B : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def j_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)

  have G1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
           by(insert A, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
           by(insert A, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G3 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
           by(insert B, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
  have G4 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
           by(insert B, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

  have *   : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def S_def i_val G1 G2)

  have **  : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def  null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def S_def i_val G3 G4)

  have *** : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(S \<tau>)\<rceil>\<rceil>-{i \<tau>}\<rfloor>\<rfloor>)\<rceil>\<rceil>-{j \<tau>}\<rfloor>\<rfloor> =
              Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(S \<tau>)\<rceil>\<rceil>-{j \<tau>}\<rfloor>\<rfloor>)\<rceil>\<rceil>-{i \<tau>}\<rfloor>\<rfloor>"
              apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF A] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF B])
             by (metis Diff_insert2 insert_commute)
  show ?thesis
     apply(simp add: OclExcluding_def S_def[simplified OclValid_def]
                  i_val[simplified OclValid_def] j_val[simplified OclValid_def]
                  true_def OclValid_def StrongEq_def)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def ** ***)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * )
     apply(subst cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * **)
     done
qed


lemma OclExcluding_commute[simp,code_unfold]:
"((S :: ('\<AA>, 'a::null) Set)->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j) = (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> i \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A': "\<And> \<tau>.   \<tau> \<Turnstile> i \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B:"\<And> \<tau>.   \<tau> \<Turnstile> j \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B':"\<And> \<tau>.   \<tau> \<Turnstile> j \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> S \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> S \<triangleq> invalid   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> S \<triangleq> null   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> S \<triangleq> null   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(j)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<upsilon> j)")
      apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
       apply(simp only: OclExcluding_commute0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
     apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
    apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 B[OF foundation22[THEN iffD2]] B'[OF foundation22[THEN iffD2]])
  apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
 done
qed


lemma OclExcluding_charn0_exec[simp,code_unfold]:
"(Set{}->excluding\<^sub>S\<^sub>e\<^sub>t(x)) = (if (\<upsilon> x) then Set{} else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->excluding\<^sub>S\<^sub>e\<^sub>t(invalid)) \<tau> = (if (\<upsilon> invalid) then Set{} else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow>
                 (Set{}->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = (if (\<upsilon> x) then Set{} else invalid endif) \<tau>"
          by(simp add: OclExcluding_charn0[THEN foundation22[THEN iffD1]])
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
     apply(simp add: B)
    apply(simp add: foundation18)
    apply(subst OclExcluding.cp0, simp)
    apply(simp add: cp_OclIf[symmetric] OclExcluding.cp0[symmetric] cp_valid[symmetric] A)
   done
qed

lemma OclExcluding_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> ((X->including\<^sub>S\<^sub>e\<^sub>t(x))->excluding\<^sub>S\<^sub>e\<^sub>t(y)) \<triangleq> ((X->excluding\<^sub>S\<^sub>e\<^sub>t(y))->including\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have D : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have E : "x \<tau> \<noteq> y \<tau>"
          by(insert neq,
             auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                        null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def StrongEq_def OclNot_def)

 have G1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
          by(insert C, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 have G2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
          by(insert C, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 have G : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          by(auto simp: OclValid_def false_def true_def defined_def
                        bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def G1 G2)

 have H1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
          by(insert D, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 have H2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
          by(insert D, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 have H : "(\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          by(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def H1 H2)

 have Z : "insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>} = insert (x \<tau>) (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>})"
          by(auto simp: E)
 show ?thesis
  apply(insert def_X[THEN  foundation13[THEN iffD2]] val_x[THEN  foundation13[THEN iffD2]]
               val_y[THEN  foundation13[THEN iffD2]])
  apply(simp add: foundation22 OclIncluding_def OclExcluding_def def_X[THEN foundation16[THEN iffD1]])
  apply(subst cp_defined, simp)+
  apply(simp add: G H Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C] Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF D] Z)
  done
qed



lemma OclExcluding_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (((X->including\<^sub>S\<^sub>e\<^sub>t(x))->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<triangleq> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have G1 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"
          by(insert C, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 have G2 : "Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"
          by(insert C, simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)
 show ?thesis
   apply(insert def_X[THEN foundation16[THEN iffD1]]
                val_x[THEN foundation18[THEN iffD1]])
   apply(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def false_def true_def
                    invalid_def defined_def valid_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                    StrongEq_def)
   apply(subst OclExcluding.cp0)
   apply(auto simp:OclExcluding_def)
            apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C])
           apply(simp_all add: false_def true_def defined_def valid_def
                               null_fun_def bot_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                          split: bool.split_asm HOL.if_split_asm option.split)
   apply(auto simp: G1 G2)
  done
qed




theorem OclExcluding_charn3:  "((X->including\<^sub>S\<^sub>e\<^sub>t(x))->excluding\<^sub>S\<^sub>e\<^sub>t(x)) = (X->excluding\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 have A1 : "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A1': "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A2 : "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A2': "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A3 : "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A3': "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 show ?thesis
 apply(rule ext, rename_tac "\<tau>")
 apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
  apply(case_tac "\<tau> \<Turnstile> (\<delta> X)")
   apply(simp only: OclExcluding_charn2[THEN foundation22[THEN iffD1]])
   apply(simp add: foundation16', elim disjE)
   apply(simp add: A1[OF foundation22[THEN iffD2]] A1'[OF foundation22[THEN iffD2]])
  apply(simp add: A2[OF foundation22[THEN iffD2]] A2'[OF foundation22[THEN iffD2]])
 apply(simp add:foundation18 A3[OF foundation22[THEN iffD2]] A3'[OF foundation22[THEN iffD2]])
 done
qed


text\<open>One would like a generic theorem of the form:
\begin{isar}[mathescape]
lemma OclExcluding_charn_exec:
       "(X->including$_{Set}$(x::('$\mathfrak{A}$,'a::null)val)->excluding$_{Set}$(y)) =
        (if \<delta> X then if x \<doteq> y
                     then X->excluding$_{Set}$(y)
                     else X->excluding$_{Set}$(y)->including$_{Set}$(x)
                     endif
                else invalid endif)"
\end{isar}
Unfortunately, this does not hold in general, since referential equality is
an overloaded concept and has to be defined for each type individually.
Consequently, it is only valid for concrete  type instances for Boolean,
Integer, and Sets thereof...
\<close>


text\<open>The computational law \emph{OclExcluding-charn-exec} becomes generic since it
uses strict equality which in itself is generic. It is possible to prove
the following generic theorem and instantiate it later (using properties
that link the polymorphic logical strong equality with the concrete instance
of strict quality).\<close>
lemma OclExcluding_charn_exec:
 assumes strict1: "(invalid \<doteq> y) = invalid"
 and     strict2: "(x \<doteq> invalid) = invalid"
 and     StrictRefEq_valid_args_valid: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                     (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
 and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
 and     StrictRefEq_vs_StrongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
 shows "(X->including\<^sub>S\<^sub>e\<^sub>t(x::('\<AA>,'a::null)val)->excluding\<^sub>S\<^sub>e\<^sub>t(y)) =
        (if \<delta> X then if x \<doteq> y
                     then X->excluding\<^sub>S\<^sub>e\<^sub>t(y)
                     else X->excluding\<^sub>S\<^sub>e\<^sub>t(y)->including\<^sub>S\<^sub>e\<^sub>t(x)
                     endif
                else invalid endif)"
proof -
 (* Lifting theorems, largely analogous OclIncludes_execute_generic,
         with the same problems wrt. strict equality. *)
 have A1: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow>
            (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have B1: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = invalid  \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have A2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have B2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 note [simp] = cp_StrictRefEq [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]

 have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> =
           (if x \<doteq> y then X->excluding\<^sub>S\<^sub>e\<^sub>t(y) else X->excluding\<^sub>S\<^sub>e\<^sub>t(y)->including\<^sub>S\<^sub>e\<^sub>t(x) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by(simp add: strict1)

 have D: "\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> =
           (if x \<doteq> y then X->excluding\<^sub>S\<^sub>e\<^sub>t(y) else X->excluding\<^sub>S\<^sub>e\<^sub>t(y)->including\<^sub>S\<^sub>e\<^sub>t(x) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict2)

 have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then X->excluding\<^sub>S\<^sub>e\<^sub>t(y) else X->excluding\<^sub>S\<^sub>e\<^sub>t(y)->including\<^sub>S\<^sub>e\<^sub>t(x) endif) \<tau> =
              (if x \<triangleq> y then X->excluding\<^sub>S\<^sub>e\<^sub>t(y) else X->excluding\<^sub>S\<^sub>e\<^sub>t(y)->including\<^sub>S\<^sub>e\<^sub>t(x) endif) \<tau>"
           apply(subst cp_OclIf)
           apply(subst StrictRefEq_vs_StrongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_OclIf[symmetric])

 have F: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
           (X->including\<^sub>S\<^sub>e\<^sub>t(x)->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau>) = (X->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)"
           apply(drule StrongEq_L_sym)
           apply(rule foundation22[THEN iffD1])
           apply(erule StrongEq_L_subst2_rev,simp)
           by(simp add: OclExcluding_charn2)

 show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:defined_split,elim disjE A1 B1 A2 B2)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
     apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not (x \<triangleq> y)")
     apply(simp add: OclExcluding_charn1[simplified foundation22]
                     OclExcluding_charn2[simplified foundation22])
    apply(simp add: foundation9 F)
 done
qed


(* Hack to work around OF-Bug *)
schematic_goal OclExcluding_charn_exec\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.strict2
                                StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.defined_args_valid
                                StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.StrictRefEq_vs_StrongEq], simp_all)

schematic_goal OclExcluding_charn_exec\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.strict2
                                StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.defined_args_valid
                             StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.cp0 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.StrictRefEq_vs_StrongEq], simp_all)


schematic_goal OclExcluding_charn_exec\<^sub>S\<^sub>e\<^sub>t[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t.strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t.strict2
                                StrictRefEq\<^sub>S\<^sub>e\<^sub>t.defined_args_valid
                                StrictRefEq\<^sub>S\<^sub>e\<^sub>t.cp0 StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq], simp_all)


subsubsection\<open>Execution Rules on Includes\<close>

lemma OclIncludes_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> not(Set{}->includes\<^sub>S\<^sub>e\<^sub>t(x))"
using val_x
apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def)
apply(auto simp: mtSet_def Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
done


lemma OclIncludes_charn0'[simp,code_unfold]:
"Set{}->includes\<^sub>S\<^sub>e\<^sub>t(x) = (if \<upsilon> x then false else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->includes\<^sub>S\<^sub>e\<^sub>t(invalid)) \<tau> = (if (\<upsilon> invalid) then false else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow> (Set{}->includes\<^sub>S\<^sub>e\<^sub>t(x)) \<tau> = (if \<upsilon> x then false else invalid endif) \<tau>"
          apply(frule OclIncludes_charn0, simp add: OclValid_def)
          apply(rule foundation21[THEN fun_cong, simplified StrongEq_def,simplified,
                     THEN iffD1, of _ _ "false"])
          by simp
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
     apply(simp_all add: B foundation18)
    apply(subst OclIncludes.cp0, simp add: OclIncludes.cp0[symmetric] A)
  done
qed

lemma OclIncludes_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show ?thesis
  apply(subst OclIncludes_def, simp add: foundation10[simplified OclValid_def] OclValid_def
                                 def_X[simplified OclValid_def] val_x[simplified OclValid_def])
  apply(simp add: OclIncluding_def def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C] true_def)
 done
qed



lemma OclIncludes_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<triangleq> (X->includes\<^sub>S\<^sub>e\<^sub>t(y))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show ?thesis
  apply(subst OclIncludes_def,
        simp add: def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  val_y[simplified OclValid_def] foundation10[simplified OclValid_def]
                  OclValid_def StrongEq_def)
  apply(simp add: OclIncluding_def OclIncludes_def def_X[simplified OclValid_def]
                  val_x[simplified OclValid_def] val_y[simplified OclValid_def]
                  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF C] true_def)
 by(metis foundation22 foundation6 foundation9 neq)
qed

text\<open>Here is again a generic theorem similar as above.\<close>

lemma OclIncludes_execute_generic:
assumes strict1: "(invalid \<doteq> y) = invalid"
and     strict2: "(x \<doteq> invalid) = invalid"
and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
and     StrictRefEq_vs_StrongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
shows
      "(X->including\<^sub>S\<^sub>e\<^sub>t(x::('\<AA>,'a::null)val)->includes\<^sub>S\<^sub>e\<^sub>t(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif else invalid endif)"
proof -
  have A: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow>
            (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev,simp,simp)
  have B: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = invalid  \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev,simp,simp)

  note [simp] = cp_StrictRefEq [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]

  have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> =
           (if x \<doteq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict1)
  have D:"\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> =
           (if x \<doteq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict2)
  have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif) \<tau> =
              (if x \<triangleq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif) \<tau>"
           apply(subst cp_OclIf)
           apply(subst StrictRefEq_vs_StrongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_OclIf[symmetric])
  have F: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
               (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(y)) \<tau> = (X->including\<^sub>S\<^sub>e\<^sub>t(x)->includes\<^sub>S\<^sub>e\<^sub>t(x)) \<tau>"
           apply(rule foundation22[THEN iffD1])
           by(erule StrongEq_L_subst2_rev,simp, simp)
  show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:defined_split,elim disjE A B)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
     apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not(x \<triangleq> y)")
     apply(simp add: OclIncludes_charn2[simplified foundation22])
    apply(simp add: foundation9 F
                    OclIncludes_charn1[THEN foundation13[THEN iffD2],
                                     THEN foundation22[THEN iffD1]])
  done
qed


(* Hack to work around OF-Bug *)
schematic_goal OclIncludes_execute\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.strict2
                                    StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0
                                    StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.StrictRefEq_vs_StrongEq], simp_all)


schematic_goal OclIncludes_execute\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.strict2
                                    StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.cp0
                                    StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n.StrictRefEq_vs_StrongEq], simp_all)


schematic_goal OclIncludes_execute\<^sub>S\<^sub>e\<^sub>t[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t.strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t.strict2
                                    StrictRefEq\<^sub>S\<^sub>e\<^sub>t.cp0
                                    StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq], simp_all)

lemma OclIncludes_including_generic :
 assumes OclIncludes_execute_generic [simp] : "\<And>X x y.
           (X->including\<^sub>S\<^sub>e\<^sub>t(x::('\<AA>,'a::null)val)->includes\<^sub>S\<^sub>e\<^sub>t(y)) =
           (if \<delta> X then if x \<doteq> y then true else X->includes\<^sub>S\<^sub>e\<^sub>t(y) endif else invalid endif)"
     and StrictRefEq_strict'' : "\<And>x y. \<delta> ((x::('\<AA>,'a::null)val) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
     and a_val : "\<tau> \<Turnstile> \<upsilon> a"
     and x_val : "\<tau> \<Turnstile> \<upsilon> x"
     and S_incl : "\<tau> \<Turnstile> (S)->includes\<^sub>S\<^sub>e\<^sub>t((x::('\<AA>,'a::null)val))"
   shows "\<tau> \<Turnstile> S->including\<^sub>S\<^sub>e\<^sub>t((a::('\<AA>,'a::null)val))->includes\<^sub>S\<^sub>e\<^sub>t(x)"
proof -
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False"
 by (metis bot_fun_def foundation1 foundation18' valid3)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False"
 by (metis bot_fun_def discr_eq_bot1_true)
 have discr_neq_invalid_true : "\<And>\<tau>. (invalid \<tau> \<noteq> true \<tau>) = True"
 by (metis discr_eq_bot2_true invalid_def)
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False"
 by (metis bot_option_def invalid_def option.simps(2) true_def)
show ?thesis
  apply(simp)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
   prefer 2
   apply(insert S_incl[simplified OclIncludes_def], simp add:  OclValid_def)
   apply(metis discr_eq_bot2_true)
  apply(simp add: cp_OclIf[of "\<delta> S"] OclValid_def OclIf_def x_val[simplified OclValid_def]
                  discr_neq_invalid_true discr_eq_invalid_true)
 by (metis OclValid_def S_incl StrictRefEq_strict'' a_val foundation10 foundation6 x_val)
qed

lemmas OclIncludes_including\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r =
       OclIncludes_including_generic[OF OclIncludes_execute\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.def_homo]

subsubsection\<open>Execution Rules on Excludes\<close>

lemma OclExcludes_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)->excludes\<^sub>S\<^sub>e\<^sub>t(x))"
proof -
 let ?OclSet = "\<lambda>S. \<lfloor>\<lfloor>S\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
 have diff_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "?OclSet (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {x \<tau>})"
  apply(simp, (rule disjI2)+)
 by (metis (hide_lams, no_types) Diff_iff Set_inv_lemma def_X)

 show ?thesis
  apply(subst OclExcludes_def, simp add: foundation10[simplified OclValid_def] OclValid_def
                                 def_X[simplified OclValid_def] val_x[simplified OclValid_def])
  apply(subst OclIncludes_def, simp add: OclNot_def)
  apply(simp add: OclExcluding_def def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF diff_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e] true_def)
 by(simp add: OclAnd_def def_X[simplified OclValid_def] val_x[simplified OclValid_def] true_def)
qed

subsubsection\<open>Execution Rules on Size\<close>

lemma [simp,code_unfold]: "Set{} ->size\<^sub>S\<^sub>e\<^sub>t() = \<zero>"
 apply(rule ext)
 apply(simp add: defined_def mtSet_def OclSize_def
                 bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def
                 null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def)
 apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, simp_all add: bot_option_def null_option_def) +
by(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_option_def null_option_def OclInt0_def)

lemma OclSize_including_exec[simp,code_unfold]:
 "((X ->including\<^sub>S\<^sub>e\<^sub>t(x)) ->size\<^sub>S\<^sub>e\<^sub>t()) = (if \<delta> X and \<upsilon> x then
                                     X ->size\<^sub>S\<^sub>e\<^sub>t() +\<^sub>i\<^sub>n\<^sub>t if X ->includes\<^sub>S\<^sub>e\<^sub>t(x) then \<zero> else \<one> endif
                                   else
                                     invalid
                                   endif)"
proof -

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  proof -
  fix \<tau>
  have includes_notin: "\<not> \<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> (\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                        x \<tau> \<notin> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  by(simp add: OclIncludes_def OclValid_def true_def)

  have includes_def: "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
  by (metis bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

  have includes_val: "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
  using foundation5 foundation6 by fastforce

  have ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
    \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
   apply(simp add: bot_option_def null_option_def)
  by (metis (hide_lams, no_types) Set_inv_lemma foundation18' foundation5)

  have m : "\<And>\<tau>. (\<lambda>_. \<bottom>) = (\<lambda>_. invalid \<tau>)" by(rule ext, simp add:invalid_def)
  
  show "X->including\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t() \<tau> = (if \<delta> X and \<upsilon> x
                                     then X->size\<^sub>S\<^sub>e\<^sub>t() +\<^sub>i\<^sub>n\<^sub>t if X->includes\<^sub>S\<^sub>e\<^sub>t(x) then \<zero> else \<one> endif
                                     else invalid endif) \<tau>"
   apply(case_tac "\<tau> \<Turnstile> \<delta> X and \<upsilon> x", simp)
    apply(subst OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0)
    apply(case_tac "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(x)", simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric])
     apply(case_tac "\<tau> \<Turnstile> ((\<upsilon> (X->size\<^sub>S\<^sub>e\<^sub>t())) and not (\<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())))", simp)
      apply(drule foundation5[where P = "\<upsilon> X->size\<^sub>S\<^sub>e\<^sub>t()"], erule conjE)
      apply(drule OclSize_infinite)
      apply(frule includes_def, drule includes_val, simp)
      apply(subst OclSize_def, subst OclIncluding_finite_rep_set, assumption+)
     apply (metis (hide_lams, no_types) invalid_def)

     apply(subst OclIf_false',
           metis (hide_lams, no_types) defined5 defined6 defined_and_I defined_not_I
                                       foundation1 foundation9)
    apply(subst cp_OclSize, simp add: OclIncluding_includes0 cp_OclSize[symmetric])
    (* *)
    apply(subst OclIf_false', subst foundation9, auto, simp add: OclSize_def)
    apply(drule foundation5)
    apply(subst (1 2) OclIncluding_finite_rep_set, fast+)
    apply(subst (1 2) cp_OclAnd, subst (1 2) OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp)
    apply(rule conjI)
     apply(simp add: OclIncluding_def)
     apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e], fast+)
     apply(subst (asm) (2 3) OclValid_def, simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclInt1_def)
     apply(rule impI)
     apply(drule Finite_Set.card.insert[where x = "x \<tau>"])
     apply(rule includes_notin, simp, simp)
     apply (metis Suc_eq_plus1 of_nat_1 of_nat_add)

    apply(subst (1 2) m[of \<tau>], simp only:   OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric],simp, simp add:invalid_def)
    apply(subst OclIncluding_finite_rep_set, fast+, simp add: OclValid_def)
   (* *)
   apply(subst OclIf_false', metis (hide_lams, no_types) defined6 foundation1 foundation9
                                                         OclExcluding_valid_args_valid'')
  by (metis cp_OclSize foundation18' OclIncluding_valid_args_valid'' invalid_def OclSize_invalid)
 qed
qed

subsubsection\<open>Execution Rules on IsEmpty\<close>

lemma [simp,code_unfold]: "Set{}->isEmpty\<^sub>S\<^sub>e\<^sub>t() = true"
by(simp add: OclIsEmpty_def)

lemma OclIsEmpty_including [simp]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including\<^sub>S\<^sub>e\<^sub>t(a)->isEmpty\<^sub>S\<^sub>e\<^sub>t() \<tau> = false \<tau>"
proof -
 have A1 : "\<And>\<tau> X. X \<tau> = true \<tau> \<or> X \<tau> = false \<tau> \<Longrightarrow> (X and not X) \<tau> = false \<tau>"
 by (metis (no_types) OclAnd_false1 OclAnd_idem OclImplies_def OclNot3 OclNot_not OclOr_false1
                      cp_OclAnd cp_OclNot deMorgan1 deMorgan2)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have B : "\<And>X \<tau>. \<tau> \<Turnstile> \<upsilon> X \<Longrightarrow> X \<tau> \<noteq> \<zero> \<tau> \<Longrightarrow> (X \<doteq> \<zero>) \<tau> = false \<tau>"
      apply(simp add: foundation22[symmetric] foundation14 foundation9)
      apply(erule StrongEq_L_subst4_rev[THEN iffD2, OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.StrictRefEq_vs_StrongEq])
      by(simp_all)

 show ?thesis
  apply(simp add: OclIsEmpty_def del: OclSize_including_exec)
  apply(subst cp_OclOr, subst A1)
   apply (metis OclExcludes.def_homo defined_inject_true)
  apply(simp add: cp_OclOr[symmetric] del: OclSize_including_exec)
  apply(rule B,
        rule foundation20,
        metis OclIncluding.def_homo OclIncluding_finite_rep_set X_def X_finite a_val foundation10' size_defined')
  apply(simp add: OclSize_def OclIncluding_finite_rep_set[OF X_def a_val] X_finite OclInt0_def)
 by (metis OclValid_def X_def a_val foundation10 foundation6
           OclIncluding_notempty_rep_set[OF X_def a_val])
qed

subsubsection\<open>Execution Rules on NotEmpty\<close>

lemma [simp,code_unfold]: "Set{}->notEmpty\<^sub>S\<^sub>e\<^sub>t() = false"
by(simp add: OclNotEmpty_def)

lemma OclNotEmpty_including [simp,code_unfold]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including\<^sub>S\<^sub>e\<^sub>t(a)->notEmpty\<^sub>S\<^sub>e\<^sub>t() \<tau> = true \<tau>"
 apply(simp add: OclNotEmpty_def)
 apply(subst cp_OclNot, subst OclIsEmpty_including, simp_all add: assms)
by (metis OclNot4 cp_OclNot)

subsubsection\<open>Execution Rules on Any\<close>

lemma [simp,code_unfold]: "Set{}->any\<^sub>S\<^sub>e\<^sub>t() = null"
by(rule ext, simp add: OclANY_def, simp add: false_def true_def)

lemma OclANY_singleton_exec[simp,code_unfold]:
      "(Set{}->including\<^sub>S\<^sub>e\<^sub>t(a))->any\<^sub>S\<^sub>e\<^sub>t() = a"
 apply(rule ext, rename_tac \<tau>, simp add: mtSet_def OclANY_def)
 apply(case_tac "\<tau> \<Turnstile> \<upsilon> a")
  apply(simp add: OclValid_def mtSet_defined[simplified mtSet_def]
                  mtSet_valid[simplified mtSet_def] mtSet_rep_set[simplified mtSet_def])
  apply(subst (1 2) cp_OclAnd,
        subst (1 2) OclNotEmpty_including[where X = "Set{}", simplified mtSet_def])
     apply(simp add: mtSet_defined[simplified mtSet_def])
    apply(metis (hide_lams, no_types) finite.emptyI mtSet_def mtSet_rep_set)
   apply(simp add: OclValid_def)
  apply(simp add: OclIncluding_def)
  apply(rule conjI)
   apply(subst (1 2) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def null_option_def)
    apply(simp, metis OclValid_def foundation18')
   apply(simp)
 apply(simp add: mtSet_defined[simplified mtSet_def])
 (* *)
 apply(subgoal_tac "a \<tau> = \<bottom>")
  prefer 2
  apply(simp add: OclValid_def valid_def bot_fun_def split: if_split_asm)
 apply(simp)
 apply(subst (1 2 3 4) cp_OclAnd,
       simp add: mtSet_defined[simplified mtSet_def] valid_def bot_fun_def)
by(simp add: cp_OclAnd[symmetric], rule impI, simp add: false_def true_def)

subsubsection\<open>Execution Rules on Forall\<close>

lemma OclForall_mtSet_exec[simp,code_unfold] :"((Set{})->forAll\<^sub>S\<^sub>e\<^sub>t(z| P(z))) = true"
apply(simp add: OclForall_def)
apply(subst mtSet_def)+
apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all add: true_def)+
done


text\<open>The following rule is a main theorem of our approach: From a denotational definition
that assures consistency, but may be --- as in the case of the @{term "X->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x)"} ---
dauntingly complex, we derive operational rules that can serve as a gold-standard for operational
execution, since they may be evaluated in whatever situation and according to whatever strategy.
In the case of @{term "X->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x)"}, the operational rule gives immediately a way to
evaluation in any finite (in terms of conventional OCL: denotable) set, although the rule also
holds for the infinite case:

@{term "Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l ->forAll\<^sub>S\<^sub>e\<^sub>t(x | (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l ->forAll\<^sub>S\<^sub>e\<^sub>t(y | x +\<^sub>i\<^sub>n\<^sub>t y \<triangleq> y +\<^sub>i\<^sub>n\<^sub>t x)))"}

or even:

@{term "Integer ->forAll\<^sub>S\<^sub>e\<^sub>t(x | (Integer ->forAll\<^sub>S\<^sub>e\<^sub>t(y | x +\<^sub>i\<^sub>n\<^sub>t y \<doteq> y +\<^sub>i\<^sub>n\<^sub>t x)))"}

are valid OCL statements in any context $\tau$.
\<close>

theorem OclForall_including_exec[simp,code_unfold] :
        assumes cp0 : "cp P"
        shows         "((S->including\<^sub>S\<^sub>e\<^sub>t(x))->forAll\<^sub>S\<^sub>e\<^sub>t(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                                then P x and (S->forAll\<^sub>S\<^sub>e\<^sub>t(z | P(z)))
                                                                else invalid
                                                                endif)"
proof -
   have cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" by(insert cp0, auto simp: cp_def)

   have cp_eq : "\<And>\<tau> v. (P x \<tau> = v) = (P (\<lambda>_. x \<tau>) \<tau> = v)" by(subst cp, simp)

   have cp_OclNot_eq : "\<And>\<tau> v. (P x \<tau> \<noteq> v) = (P (\<lambda>_. x \<tau>) \<tau> \<noteq> v)" by(subst cp, simp)

   have insert_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                               \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in>
                                 {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

   have forall_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                            (f x \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
           apply(drule foundation5, simp add: OclIncluding_def)
           apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
           apply(rule insert_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e, fast+)
           by(simp add: OclValid_def)

   have exists_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                            (f x \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
           apply(subst arg_cong[where f = "\<lambda>x. \<not>x",
                                OF forall_including_invert[where f = "\<lambda>x \<tau>. \<not> (f x \<tau>)"],
                                simplified])
           by simp_all

   have contradict_Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e: "\<And>\<tau> S f. \<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. f (\<lambda>_. x) \<tau> \<Longrightarrow>
                                       (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = False"
           by(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = True", simp_all)

   have bot_invalid : "\<bottom> = invalid"  by(rule ext, simp add: invalid_def bot_fun_def)

   have bot_invalid2 : "\<And>\<tau>. \<bottom> = invalid \<tau>"  by(simp add: invalid_def)

   have C1 : "\<And>\<tau>. P x \<tau> = false \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau>) \<Longrightarrow>
                  \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                  false \<tau> = (P x and OclForall S P) \<tau>"
           apply(simp add: cp_OclAnd[of "P x"])
           apply(elim disjE, simp)
            apply(simp only: cp_OclAnd[symmetric], simp)
           apply(subgoal_tac "OclForall S P \<tau> = false \<tau>")
            apply(simp only: cp_OclAnd[symmetric], simp)
           apply(simp add: OclForall_def)
           apply(fold OclValid_def, simp add:  foundation10')
           done

   have C2 : "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                  P x \<tau> = null \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>) \<Longrightarrow>
                  P x \<tau> = invalid \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = invalid \<tau>) \<Longrightarrow>
                  \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> \<Longrightarrow>
                  invalid \<tau> = (P x and OclForall S P) \<tau>"
           apply(subgoal_tac "(\<delta> S)\<tau> = true \<tau>")
            prefer 2 apply(simp add: foundation10', simp add: OclValid_def)
           apply(drule forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>", OF cp_OclNot_eq, THEN iffD1])
            apply(assumption)
           apply(simp add: cp_OclAnd[of "P x"],elim disjE, simp_all)
              apply(simp add: invalid_def null_fun_def null_option_def bot_fun_def bot_option_def)
             apply(subgoal_tac "OclForall S P \<tau> = invalid \<tau>")
              apply(simp only:cp_OclAnd[symmetric],simp,simp add:invalid_def bot_fun_def)
             apply(unfold OclForall_def, simp add: invalid_def false_def bot_fun_def,simp)
            apply(simp add:cp_OclAnd[symmetric],simp)
           apply(erule conjE)
           apply(subgoal_tac "(P x \<tau> = invalid \<tau>) \<or> (P x \<tau> = null \<tau>) \<or> (P x \<tau> = true \<tau>) \<or> (P x \<tau> = false \<tau>)")
            prefer 2 apply(rule bool_split_0)
           apply(elim disjE, simp_all)
            apply(simp only:cp_OclAnd[symmetric],simp)+
           done

   have A : "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                 OclForall (S->including\<^sub>S\<^sub>e\<^sub>t(x)) P \<tau> = (P x and OclForall S P) \<tau>"
         proof - fix \<tau>
                 assume 0 : "\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)"
                 let ?S = "\<lambda>ocl. P x \<tau> \<noteq> ocl \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> ocl \<tau>)"
                 let ?S' = "\<lambda>ocl. \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> ocl \<tau>"
                 let ?assms_1 = "?S' null"
                 let ?assms_2 = "?S' invalid"
                 let ?assms_3 = "?S' false"
                 have 4 : "?assms_3 \<Longrightarrow> ?S false"
                     apply(subst  forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 5 : "?assms_2 \<Longrightarrow> ?S invalid"
                     apply(subst  forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> invalid \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 6 : "?assms_1 \<Longrightarrow> ?S null"
                     apply(subst forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> null \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 7 : "(\<delta> S) \<tau> = true \<tau>"
                     by(insert 0, simp add: foundation10', simp add: OclValid_def)
         show "?thesis \<tau>"
           apply(subst OclForall_def)
           apply(simp add: cp_OclAnd[THEN sym] OclValid_def contradict_Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e)
           apply(intro conjI impI,fold OclValid_def)
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>", OF cp_eq])
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = invalid \<tau>", OF cp_eq])
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>", OF cp_eq])
           proof -
              assume 1 : "P x \<tau> = null \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>)"
              and    2 : ?assms_2
              and    3 : ?assms_3
              show   "null \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 5 = 5[OF 2]
                 have 6 : "P x \<tau> = null \<tau> \<or> P x \<tau> = true \<tau>"
                     by(metis 4 5 bool_split_0)
                 show ?thesis
                 apply(insert 6, elim disjE)
                  apply(subst cp_OclAnd)
                  apply(simp add: OclForall_def 7 4[THEN conjunct2] 5[THEN conjunct2])
                  apply(simp_all add:cp_OclAnd[symmetric])
                 apply(subst cp_OclAnd, simp_all add:cp_OclAnd[symmetric] OclForall_def)
                 apply(simp add:4[THEN conjunct2] 5[THEN conjunct2] 0[simplified OclValid_def] 7)
                 apply(insert 1, elim disjE, auto)
                 done
              qed
           next
              assume 1 : ?assms_1
              and    2 : "P x \<tau> = invalid \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = invalid \<tau>)"
              and    3 : ?assms_3
              show   "invalid \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 6 = 6[OF 1]
                 have 5 : "P x \<tau> = invalid \<tau> \<or> P x \<tau> = true \<tau>"
                     by(metis 4 6 bool_split_0)
                 show ?thesis
                 apply(insert 5, elim disjE)
                  apply(subst cp_OclAnd)
                  apply(simp add: OclForall_def 4[THEN conjunct2] 6[THEN conjunct2] 7)
                  apply(simp_all add:cp_OclAnd[symmetric])
                 apply(subst cp_OclAnd, simp_all add:cp_OclAnd[symmetric] OclForall_def)
                 apply(insert 2, elim disjE, simp add: invalid_def true_def bot_option_def)
                 apply(simp add: 0[simplified OclValid_def] 4[THEN conjunct2] 6[THEN conjunct2] 7)
                 by(auto)
               qed
           next
              assume 1 : ?assms_1
              and    2 : ?assms_2
              and    3 : ?assms_3
              show   "true \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 5 = 5[OF 2]
                 note 6 = 6[OF 1]
                 have 8 : "P x \<tau> = true \<tau>"
                     by(metis 4 5 6 bool_split_0)
                 show ?thesis
                 apply(subst cp_OclAnd, simp add: 8 cp_OclAnd[symmetric])
                 by(simp add: OclForall_def 4 5 6 7)
              qed
           qed ( simp add: 0
               | rule C1, simp+
               | rule C2, simp add: 0 )+
        qed

   have B : "\<And>\<tau>. \<not> (\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)) \<Longrightarrow>
                 OclForall (S->including\<^sub>S\<^sub>e\<^sub>t(x)) P \<tau> = invalid \<tau>"
           apply(rule foundation22[THEN iffD1])
           apply(simp only: foundation10' de_Morgan_conj foundation18'', elim disjE)
            apply(simp add:  defined_split, elim disjE)
             apply(erule StrongEq_L_subst2_rev, simp+)+
           done

   show ?thesis
           apply(rule ext, rename_tac \<tau>)
           apply(simp add: OclIf_def)
           apply(simp add: cp_defined[of "\<delta> S and \<upsilon> x"] cp_defined[THEN sym])
           apply(intro conjI impI)
           by(auto intro!: A B simp: OclValid_def)
qed




subsubsection\<open>Execution Rules on Exists\<close>

lemma OclExists_mtSet_exec[simp,code_unfold] :
"((Set{})->exists\<^sub>S\<^sub>e\<^sub>t(z | P(z))) = false"
by(simp add: OclExists_def)

lemma OclExists_including_exec[simp,code_unfold] :
 assumes cp: "cp P"
 shows "((S->including\<^sub>S\<^sub>e\<^sub>t(x))->exists\<^sub>S\<^sub>e\<^sub>t(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x or (S->exists\<^sub>S\<^sub>e\<^sub>t(z | P(z)))
                                                 else invalid
                                                 endif)"
 by(simp add: OclExists_def OclOr_def  cp OclNot_inject)


subsubsection\<open>Execution Rules on Iterate\<close>

lemma OclIterate_empty[simp,code_unfold]: "((Set{})->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = A | P a x)) = A"
proof -
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis (no_types) defined_def mtSet_def mtSet_defined null_fun_def)
 show ?thesis
      apply(simp add: OclIterate_def mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse valid_def C)
      apply(rule ext, rename_tac \<tau>)
      apply(case_tac "A \<tau> = \<bottom> \<tau>", simp_all, simp add:true_def false_def bot_fun_def)
      apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
 done
qed

text\<open>In particular, this does hold for A = null.\<close>

lemma OclIterate_including:
assumes S_finite:    "\<tau> \<Turnstile> \<delta>(S->size\<^sub>S\<^sub>e\<^sub>t())"
and     F_valid_arg: "(\<upsilon> A) \<tau> = (\<upsilon> (F a A)) \<tau>"
and     F_commute:   "comp_fun_commute F"
and     F_cp:        "\<And> x y \<tau>. F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
shows   "((S->including\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x =     A | F a x)) \<tau> =
         ((S->excluding\<^sub>S\<^sub>e\<^sub>t(a))->iterate\<^sub>S\<^sub>e\<^sub>t(a; x = F a A | F a x)) \<tau>"
proof -
 have insert_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
    \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def)
  by(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
     rule insert_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp_all add: null_option_def bot_option_def)+

 have remove_finite : "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       finite ((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have remove_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
   \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def)
  by(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
     rule remove_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp_all add: null_option_def bot_option_def)+

 have abs_rep: "\<And>x. \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow>
                    \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)\<rceil>\<rceil> = x"
 by(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 show ?thesis
  apply(subst (1 2) cp_OclIterate, subst OclIncluding_def, subst OclExcluding_def)
  apply(case_tac "\<not> ((\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> a) \<tau> = true \<tau>)", simp add: invalid_def)

   apply(subgoal_tac "OclIterate (\<lambda>_. \<bottom>) A F \<tau> = OclIterate (\<lambda>_. \<bottom>) (F a A) F \<tau>", simp)
    apply(rule conjI, blast+)
  apply(simp add: OclIterate_def defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate_def)
  apply((subst abs_rep[OF insert_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e[simplified OclValid_def], of \<tau>], simp_all)+,
        (subst abs_rep[OF remove_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e[simplified OclValid_def], of \<tau>], simp_all)+,
        (subst insert_defined, simp_all add: OclValid_def)+,
        (subst remove_defined, simp_all add: OclValid_def)+)

  apply(case_tac "\<not> ((\<upsilon> A) \<tau> = true \<tau>)", (simp add: F_valid_arg)+)
  apply(rule impI,
        subst Finite_Set.comp_fun_commute.fold_fun_left_comm[symmetric, OF F_commute],
        rule remove_finite, simp)

  apply(subst image_set_diff[OF inject], simp)
  apply(subgoal_tac "Finite_Set.fold F A (insert (\<lambda>\<tau>'. a \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>)) \<tau> =
      F (\<lambda>\<tau>'. a \<tau>) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> - {\<lambda>\<tau>'. a \<tau>})) \<tau>")
   apply(subst F_cp, simp)

 by(subst Finite_Set.comp_fun_commute.fold_insert_remove[OF F_commute], simp+)
qed

subsubsection\<open>Execution Rules on Select\<close>

lemma OclSelect_mtSet_exec[simp,code_unfold]: "OclSelect mtSet P = mtSet"
 apply(rule ext, rename_tac \<tau>)
 apply(simp add: OclSelect_def mtSet_def defined_def false_def true_def
                 bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def)
by(( subst (1 2 3 4 5) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse
   | subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject), (simp add: null_option_def bot_option_def)+)+

definition "OclSelect_body :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('\<AA>, 'a option option) Set
           \<equiv> (\<lambda>P x acc. if P x \<doteq> false then acc else acc->including\<^sub>S\<^sub>e\<^sub>t(x) endif)"

theorem OclSelect_including_exec[simp,code_unfold]:
 assumes P_cp : "cp P"
 shows "OclSelect (X->including\<^sub>S\<^sub>e\<^sub>t(y)) P = OclSelect_body P y (OclSelect (X->excluding\<^sub>S\<^sub>e\<^sub>t(y)) P)"
 (is "_ = ?select")
proof -
 have P_cp: "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" by(insert P_cp, auto simp: cp_def)

 have ex_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (f (P (\<lambda>_. y \<tau>)) \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>))"
      apply(simp add: OclIncluding_def OclValid_def)
       apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18',simp)

 have al_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (f (P (\<lambda>_. y \<tau>)) \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>))"
      apply(simp add: OclIncluding_def OclValid_def)
       apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18', simp)

 have ex_excluding1 : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<not> (f (P (\<lambda>_. y \<tau>)) \<tau>) \<Longrightarrow>
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>)"
      apply(simp add: OclExcluding_def OclValid_def)
       apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
      by (metis (no_types) Diff_iff OclValid_def Set_inv_lemma) auto

 have al_excluding1 : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> f (P (\<lambda>_. y \<tau>)) \<tau> \<Longrightarrow>
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>)"
      apply(simp add: OclExcluding_def OclValid_def)
      apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
      by (metis (no_types) Diff_iff OclValid_def Set_inv_lemma) auto

 have in_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                  {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x) \<tau>)} =
                                   (let s = {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x) \<tau>)} in
                                    if f (P (\<lambda>_. y \<tau>) \<tau>) then insert (y \<tau>) s else s)"
      apply(simp add: OclIncluding_def OclValid_def)
      apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
       apply (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')
      by(simp add: Let_def, auto)

 let ?OclSet = "\<lambda>S. \<lfloor>\<lfloor>S\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"

 have diff_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> ?OclSet (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> - {y \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (mono_tags) Diff_iff OclValid_def Set_inv_lemma)

 have ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> (\<upsilon> y) \<tau> = true \<tau> \<Longrightarrow>
                           ?OclSet (insert (y \<tau>) {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')

 have ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> (\<upsilon> y) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet (insert (y \<tau>) {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau> \<noteq> false \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')

 have ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma)

 have ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e''' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet {x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}"
      apply(simp, (rule disjI2)+)
      by(metis (hide_lams, no_types) OclValid_def Set_inv_lemma)

 have if_same : "\<And>a b c d \<tau>. \<tau> \<Turnstile> \<delta> a \<Longrightarrow> b \<tau> = d \<tau> \<Longrightarrow> c \<tau> = d \<tau> \<Longrightarrow>
                             (if a then b else c endif) \<tau> = d \<tau>"
      by(simp add: OclIf_def OclValid_def)

 have invert_including : "\<And>P y \<tau>. P \<tau> = \<bottom> \<Longrightarrow> P->including\<^sub>S\<^sub>e\<^sub>t(y) \<tau> = \<bottom>"
      by (metis (hide_lams, no_types) foundation16[THEN iffD1]
                foundation18' OclIncluding_valid_args_valid)

 have exclude_defined : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow>
           (\<delta>(\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>{x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau>\<noteq>false \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
      apply(subst defined_def,
            simp add: false_def true_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def)
      by(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'''[simplified false_def]],
         (simp add: OclValid_def bot_option_def null_option_def)+)+

 have if_eq : "\<And>x A B \<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((if x \<doteq> false then A else B endif) \<triangleq>
                                          (if x \<triangleq> false then A else B endif))"
      apply(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def)
      apply(subst (2) StrongEq_def)
      by(subst cp_OclIf, simp add: cp_OclIf[symmetric] true_def)

 have OclSelect_body_bot: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> P y \<tau> \<noteq> \<bottom> \<Longrightarrow>
                               (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = \<bottom>) \<Longrightarrow> \<bottom> = ?select \<tau>"
      apply(drule ex_excluding1[where X2 = X and y2 = y and f2 = "\<lambda>x \<tau>. x \<tau> = \<bottom>"],
            (simp add: P_cp[symmetric])+)
      apply(subgoal_tac "\<tau> \<Turnstile> (\<bottom> \<triangleq> ?select)", simp add: OclValid_def StrongEq_def true_def bot_fun_def)
      apply(simp add: OclSelect_body_def)
      apply(subst StrongEq_L_subst3[OF _ if_eq], simp, metis foundation18')
      apply(simp add: OclValid_def, subst StrongEq_def, subst true_def, simp)
      apply(subgoal_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(y) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = \<bottom> \<tau>")
       prefer 2 apply (metis bot_fun_def )
       apply(subst if_same[where d5 = "\<bottom>"])
        apply (metis defined7 transform1)
       apply(simp add: OclSelect_def bot_option_def bot_fun_def invalid_def)
      apply(subst invert_including)
      by(simp add: OclSelect_def bot_option_def bot_fun_def invalid_def)+


 have d_and_v_inject : "\<And>\<tau> X y. (\<delta> X and \<upsilon> y) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> X and \<upsilon> y) \<tau> = false \<tau>"
      apply(fold OclValid_def, subst foundation22[symmetric])
      apply(auto simp:foundation10'  defined_split)
        apply(erule StrongEq_L_subst2_rev,simp,simp)
       apply(erule StrongEq_L_subst2_rev,simp,simp)
      by(erule foundation7'[THEN iffD2, THEN foundation15[THEN iffD2,
                                       THEN StrongEq_L_subst2_rev]],simp,simp)




 have OclSelect_body_bot': "\<And>\<tau>. (\<delta> X and \<upsilon> y) \<tau> \<noteq> true \<tau> \<Longrightarrow> \<bottom> = ?select \<tau>"
      apply(drule d_and_v_inject)
      apply(simp add: OclSelect_def OclSelect_body_def)
      apply(subst cp_OclIf, subst OclIncluding.cp0, simp add: false_def true_def)
      apply(subst cp_OclIf[symmetric], subst OclIncluding.cp0[symmetric])
      by (metis (lifting, no_types) OclIf_def foundation18 foundation18' invert_including)

 have conj_split2 : "\<And>a b c \<tau>. ((a \<triangleq> false) \<tau> = false \<tau> \<longrightarrow> b) \<and> ((a \<triangleq> false) \<tau> = true \<tau> \<longrightarrow> c) \<Longrightarrow>
                               (a \<tau> \<noteq> false \<tau> \<longrightarrow> b) \<and> (a \<tau> = false \<tau> \<longrightarrow> c)"
      by (metis OclValid_def defined7 foundation14 foundation22 foundation9)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have cp_OclSelect_body : "\<And>\<tau>. ?select \<tau> = OclSelect_body P y (\<lambda>_.(OclSelect (X->excluding\<^sub>S\<^sub>e\<^sub>t(y))P)\<tau>)\<tau>"
      apply(simp add: OclSelect_body_def)
      by(subst (1 2) cp_OclIf, subst (1 2) OclIncluding.cp0, blast)

 have OclSelect_body_strict1 : "OclSelect_body P y invalid = invalid"
      by(rule ext, simp add: OclSelect_body_def OclIf_def)

 have bool_invalid: "\<And>(x::('\<AA>)Boolean) y \<tau>. \<not> (\<tau> \<Turnstile> \<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> invalid)"
      by(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def StrongEq_def true_def)

 have conj_comm : "\<And>p q r. (p \<and> q \<and> r) = ((p \<and> q) \<and> r)" by blast

 have inv_bot : "\<And>\<tau>. invalid \<tau> = \<bottom> \<tau>" by (metis bot_fun_def invalid_def)
 have inv_bot' : "\<And>\<tau>. invalid \<tau> = \<bottom>" by (simp add: invalid_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(subst OclSelect_def)
  apply(case_tac "(\<delta> (X->including\<^sub>S\<^sub>e\<^sub>t(y))) \<tau> = true \<tau>", simp)
   apply(( subst ex_including | subst in_including),
         metis OclValid_def foundation5,
         metis OclValid_def foundation5)+
   apply(simp add: Let_def inv_bot)
   apply(subst (2 4 7 9) bot_fun_def)

   apply(subst (4) false_def, subst (4) bot_fun_def, simp add: bot_option_def P_cp[symmetric])
   (* *)
   apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> P y))")
    apply(subgoal_tac "P y \<tau> \<noteq> false \<tau>")
     prefer 2
     apply (metis (hide_lams, no_types) foundation1 foundation18' valid4)
    apply(simp)
    (* *)
    apply(subst conj_comm, rule conjI)
     apply(drule_tac y11 = false in bool_invalid)
     apply(simp only: OclSelect_body_def,
           metis OclIf_def OclValid_def defined_def foundation2 foundation22
                 bot_fun_def invalid_def)
    (* *)
    apply(drule foundation5[simplified OclValid_def],
          subst al_including[simplified OclValid_def],
          simp,
          simp)
    apply(simp add: P_cp[symmetric])
    apply (metis bot_fun_def foundation18')

   apply(simp add: foundation18' bot_fun_def OclSelect_body_bot OclSelect_body_bot')
   (* *)
   apply(subst (1 2) al_including, metis OclValid_def foundation5, metis OclValid_def foundation5)
   apply(simp add: P_cp[symmetric], subst (4) false_def, subst (4) bot_option_def, simp)

   apply(simp add: OclSelect_def[simplified inv_bot'] OclSelect_body_def StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)
   apply(subst (1 2 3 4) cp_OclIf,
         subst (1 2 3 4) foundation18'[THEN iffD2, simplified OclValid_def],
         simp,
         simp only: cp_OclIf[symmetric] refl if_True)
   apply(subst (1 2) OclIncluding.cp0, rule conj_split2, simp add: cp_OclIf[symmetric])
   apply(subst (1 2 3 4 5 6 7 8) cp_OclIf[symmetric], simp)
   apply(( subst ex_excluding1[symmetric]
         | subst al_excluding1[symmetric] ),
         metis OclValid_def foundation5,
         metis OclValid_def foundation5,
         simp add: P_cp[symmetric] bot_fun_def)+
   apply(simp add: bot_fun_def)
   apply(subst (1 2) invert_including, simp+)
   (* *)
   apply(rule conjI, blast)
   apply(intro impI conjI)
    apply(subst OclExcluding_def)
    apply(drule foundation5[simplified OclValid_def], simp)
    apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF diff_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e], fast)
    apply(simp add: OclIncluding_def cp_valid[symmetric])
    apply((erule conjE)+, frule exclude_defined[simplified OclValid_def], simp)
    apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'''], simp+)
    apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'], fast+)
   (* *)
   apply(simp add: OclExcluding_def)
   apply(simp add: foundation10[simplified OclValid_def])
   apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF diff_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e], simp+)
   apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'' ins_in_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e'''], simp+)
   apply(subgoal_tac "P (\<lambda>_. y \<tau>) \<tau> = false \<tau>")
    prefer 2
    apply(subst P_cp[symmetric], metis OclValid_def foundation22)
   apply(rule equalityI)
    apply(rule subsetI, simp, metis)
   apply(rule subsetI, simp)
  (* *)
  apply(drule defined_inject_true)
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> X) \<or> \<not> (\<tau> \<Turnstile> \<upsilon> y)")
   prefer 2
   apply (metis OclIncluding.def_homo OclIncluding_valid_args_valid OclIncluding_valid_args_valid'' OclValid_def foundation18 valid1)
  apply(subst cp_OclSelect_body, subst cp_OclSelect, subst OclExcluding_def)
  apply(simp add: OclValid_def false_def true_def, rule conjI, blast)
  apply(simp add: OclSelect_invalid[simplified invalid_def]
                  OclSelect_body_strict1[simplified invalid_def]
                  inv_bot')
 done
qed

subsubsection\<open>Execution Rules on Reject\<close>

lemma OclReject_mtSet_exec[simp,code_unfold]: "OclReject mtSet P = mtSet"
by(simp add: OclReject_def)

lemma OclReject_including_exec[simp,code_unfold]:
 assumes P_cp : "cp P"
 shows "OclReject (X->including\<^sub>S\<^sub>e\<^sub>t(y)) P = OclSelect_body (not o P) y (OclReject (X->excluding\<^sub>S\<^sub>e\<^sub>t(y)) P)"
 apply(simp add: OclReject_def comp_def, rule OclSelect_including_exec)
by (metis  assms cp_intro'(5))

subsubsection\<open>Execution Rules Combining Previous Operators\<close>

text\<open>OclIncluding\<close>

(* logical level : *)
lemma OclIncluding_idem0 :
 assumes "\<tau> \<Turnstile> \<delta> S"
     and "\<tau> \<Turnstile> \<upsilon> i"
   shows "\<tau> \<Turnstile> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(i) \<triangleq> (S->including\<^sub>S\<^sub>e\<^sub>t(i)))"
by(simp add: OclIncluding_includes OclIncludes_charn1 assms)

(* Pure algebraic level *)
theorem OclIncluding_idem[simp,code_unfold]: "((S :: ('\<AA>,'a::null)Set)->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(i) = (S->including\<^sub>S\<^sub>e\<^sub>t(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A':"\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
      apply(simp only: OclIncluding_idem0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
      apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
     apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
  done
qed

text\<open>OclExcluding\<close>

(* logical level : *)
lemma OclExcluding_idem0 :
 assumes "\<tau> \<Turnstile> \<delta> S"
     and "\<tau> \<Turnstile> \<upsilon> i"
   shows "\<tau> \<Turnstile> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(i) \<triangleq> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)))"
by(simp add: OclExcluding_excludes OclExcludes_charn1 assms)

(* Pure algebraic level *)
theorem OclExcluding_idem[simp,code_unfold]: "((S->excluding\<^sub>S\<^sub>e\<^sub>t(i))->excluding\<^sub>S\<^sub>e\<^sub>t(i)) = (S->excluding\<^sub>S\<^sub>e\<^sub>t(i))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A':"\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->excluding\<^sub>S\<^sub>e\<^sub>t(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
      apply(simp only: OclExcluding_idem0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
      apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
     apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
  done
qed

text\<open>OclIncludes\<close>


lemma OclIncludes_any[simp,code_unfold]:
      "X->includes\<^sub>S\<^sub>e\<^sub>t(X->any\<^sub>S\<^sub>e\<^sub>t()) = (if \<delta> X then
                                  if \<delta> (X->size\<^sub>S\<^sub>e\<^sub>t()) then not(X->isEmpty\<^sub>S\<^sub>e\<^sub>t())
                                  else X->includes\<^sub>S\<^sub>e\<^sub>t(null) endif
                                else invalid endif)"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)



 have notempty': "\<And>\<tau> X. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> not (X->isEmpty\<^sub>S\<^sub>e\<^sub>t()) \<tau> \<noteq> true \<tau> \<Longrightarrow>
                        X \<tau> = Set{} \<tau>"
  apply(case_tac "X \<tau>", rename_tac X', simp add: mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  apply(erule disjE, metis (hide_lams, mono_tags) bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def foundation16)
  apply(erule disjE, metis (hide_lams, no_types) bot_option_def
                                                 null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_option_def foundation16[THEN iffD1])
  apply(case_tac X', simp, metis (hide_lams, no_types) bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def foundation16[THEN iffD1])
  apply(rename_tac X'', case_tac X'', simp)
   apply (metis (hide_lams, no_types) foundation16[THEN iffD1] null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
  apply(simp add: OclIsEmpty_def OclSize_def)
  apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0,
        subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
  apply(simp only: OclValid_def foundation20[simplified OclValid_def]
                   cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
  apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse split: if_split_asm)
 by(simp add: true_def OclInt0_def OclNot_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def)

 have B: "\<And>X \<tau>. \<not> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())) \<tau> = false \<tau>"
  apply(subst cp_defined)
  apply(simp add: OclSize_def)
 by (metis bot_fun_def defined_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>, simp only: OclIncludes_def OclANY_def)
  apply(subst cp_OclIf, subst (2) cp_valid)
  apply(case_tac "(\<delta> X) \<tau> = true \<tau>",
        simp only: foundation20[simplified OclValid_def] cp_OclIf[symmetric], simp,
        subst (1 2) cp_OclAnd, simp add: cp_OclAnd[symmetric])
   apply(case_tac "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>")
    apply(frule size_defined'[THEN iffD2, simplified OclValid_def], assumption)
    apply(subst (1 2 3 4) cp_OclIf, simp)
    apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
    apply(case_tac "(X->notEmpty\<^sub>S\<^sub>e\<^sub>t()) \<tau> = true \<tau>", simp)
     apply(frule OclNotEmpty_has_elt[simplified OclValid_def], simp)
     apply(simp add: OclNotEmpty_def cp_OclIf[symmetric])
     apply(subgoal_tac "(SOME y. y \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>) \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>", simp add: true_def)
      apply(metis OclValid_def Set_inv_lemma foundation18' null_option_def true_def)
     apply(rule someI_ex, simp)
    apply(simp add: OclNotEmpty_def cp_valid[symmetric])
    apply(subgoal_tac "\<not> (null \<tau> \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>)", simp)
     apply(subst OclIsEmpty_def, simp add: OclSize_def)
     apply(subst cp_OclNot, subst cp_OclOr, subst StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, subst cp_OclAnd,
           subst cp_OclNot, simp add: OclValid_def foundation20[simplified OclValid_def]
                                      cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
     apply(frule notempty'[simplified OclValid_def],
           (simp add: mtSet_def Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse OclInt0_def false_def)+)
    apply(drule notempty'[simplified OclValid_def], simp, simp)
    apply (metis (hide_lams, no_types) empty_iff mtSet_rep_set)
   (* *)
   apply(frule B)
   apply(subst (1 2 3 4) cp_OclIf, simp)
   apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
   apply(case_tac "(X->notEmpty\<^sub>S\<^sub>e\<^sub>t()) \<tau> = true \<tau>", simp)
    apply(frule OclNotEmpty_has_elt[simplified OclValid_def], simp)
    apply(simp add: OclNotEmpty_def OclIsEmpty_def)
    apply(subgoal_tac "X->size\<^sub>S\<^sub>e\<^sub>t() \<tau> = \<bottom>")
     prefer 2
     apply (metis (hide_lams, no_types) OclSize_def)
    apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0,
          subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
    apply(simp add: OclValid_def foundation20[simplified OclValid_def]
                    cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
    apply(simp add: OclNot_def StrongEq_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def false_def true_def
                    bot_option_def bot_fun_def invalid_def)

   apply (metis bot_fun_def null_fun_def null_is_valid valid_def)
 by(drule defined_inject_true,
    simp add: false_def true_def OclIf_false[simplified false_def] invalid_def)
qed

text\<open>OclSize\<close>

lemma [simp,code_unfold]: "\<delta> (Set{} ->size\<^sub>S\<^sub>e\<^sub>t()) = true"
by simp


lemma [simp,code_unfold]: "\<delta> ((X ->including\<^sub>S\<^sub>e\<^sub>t(x)) ->size\<^sub>S\<^sub>e\<^sub>t()) = (\<delta>(X->size\<^sub>S\<^sub>e\<^sub>t()) and \<upsilon>(x))"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have OclIncluding_finite_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  apply(rule OclIncluding_finite_rep_set)
 by(metis OclValid_def foundation5)+

 have card_including_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                 (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
 by(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->including\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t())) \<tau> = true \<tau>", simp del: OclSize_including_exec)
   apply(subst cp_OclAnd, subst cp_defined, simp only: cp_defined[of "X->including\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()"],
         simp add: OclSize_def)
   apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->including\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>)", simp)
    apply(erule conjE,
          simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec
                    cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                    cp_OclAnd[of "true", THEN sym])
    apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
    apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def],
          simp only: cp_OclAnd[THEN sym])
   apply(simp, simp add: defined_def true_def false_def bot_fun_def bot_option_def)

  apply(drule defined_inject_true[of "X->including\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()"],
        simp del: OclSize_including_exec,
        simp only: cp_OclAnd[of "\<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())" "\<upsilon> x"],
        simp add: cp_defined[of "X->including\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()" ] cp_defined[of "X->size\<^sub>S\<^sub>e\<^sub>t()" ]
             del: OclSize_including_exec,
        simp add: OclSize_def card_including_exec
             del: OclSize_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>",
        simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec,
        simp only: cp_OclAnd[THEN sym],
        simp add: defined_def bot_fun_def)

  apply(split if_split_asm)
   apply(simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec)+
  apply(simp only: cp_OclAnd[THEN sym], simp, rule impI, erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
 by(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
qed

lemma [simp,code_unfold]: "\<delta> ((X ->excluding\<^sub>S\<^sub>e\<^sub>t(x)) ->size\<^sub>S\<^sub>e\<^sub>t()) = (\<delta>(X->size\<^sub>S\<^sub>e\<^sub>t()) and \<upsilon>(x))"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have OclExcluding_finite_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                                     finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil> =
                                     finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  apply(rule OclExcluding_finite_rep_set)
 by(metis OclValid_def foundation5)+

 have card_excluding_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                   (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
 by(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t())) \<tau> = true \<tau>", simp)
   apply(subst cp_OclAnd, subst cp_defined, simp only: cp_defined[of "X->excluding\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()"],
         simp add: OclSize_def)
   apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X->excluding\<^sub>S\<^sub>e\<^sub>t(x) \<tau>)\<rceil>\<rceil>)", simp)
    apply(erule conjE,
          simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec
                    cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                    cp_OclAnd[of "true", THEN sym])
    apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
    apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def],
          simp only: cp_OclAnd[THEN sym])
   apply(simp, simp add: defined_def true_def false_def bot_fun_def bot_option_def)

  apply(drule defined_inject_true[of "X->excluding\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()"],
        simp,
        simp only: cp_OclAnd[of "\<delta> (X->size\<^sub>S\<^sub>e\<^sub>t())" "\<upsilon> x"],
        simp add: cp_defined[of "X->excluding\<^sub>S\<^sub>e\<^sub>t(x)->size\<^sub>S\<^sub>e\<^sub>t()" ] cp_defined[of "X->size\<^sub>S\<^sub>e\<^sub>t()" ],
        simp add: OclSize_def card_excluding_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>",
        simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec,
        simp only: cp_OclAnd[THEN sym],
        simp add: defined_def bot_fun_def)

  apply(split if_split_asm)
   apply(simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec)+
  apply(simp only: cp_OclAnd[THEN sym], simp, rule impI, erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
 by(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
qed

lemma [simp]:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> ((X ->including\<^sub>S\<^sub>e\<^sub>t(x)) ->size\<^sub>S\<^sub>e\<^sub>t()) = (\<delta>(X) and \<upsilon>(x))"
by(simp add: size_defined[OF X_finite] del: OclSize_including_exec)


text\<open>OclForall\<close>

lemma OclForall_rep_set_false:
 assumes "\<tau> \<Turnstile> \<delta> X"
 shows "(OclForall X P \<tau> = false \<tau>) = (\<exists>x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>\<tau>. x) \<tau> = false \<tau>)"
by(insert assms, simp add: OclForall_def OclValid_def false_def true_def invalid_def
                           bot_fun_def bot_option_def null_fun_def null_option_def)

lemma OclForall_rep_set_true:
 assumes "\<tau> \<Turnstile> \<delta> X"
 shows "(\<tau> \<Turnstile> OclForall X P) = (\<forall>x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> P (\<lambda>\<tau>. x))"
proof -
 have destruct_ocl : "\<And>x \<tau>. x = true \<tau> \<or> x = false \<tau> \<or> x = null \<tau> \<or> x = \<bottom> \<tau>"
  apply(case_tac x) apply (metis bot_Boolean_def)
  apply(rename_tac x', case_tac x') apply (metis null_Boolean_def)
  apply(rename_tac x'', case_tac x'') apply (metis (full_types) true_def)
 by (metis (full_types) false_def)

 have disjE4 : "\<And> P1 P2 P3 P4 R.
   (P1 \<or> P2 \<or> P3 \<or> P4) \<Longrightarrow> (P1 \<Longrightarrow> R) \<Longrightarrow> (P2 \<Longrightarrow> R) \<Longrightarrow> (P3 \<Longrightarrow> R) \<Longrightarrow> (P4 \<Longrightarrow> R) \<Longrightarrow> R"
 by metis
 show ?thesis
  apply(simp add: OclForall_def OclValid_def true_def false_def invalid_def
                  bot_fun_def bot_option_def null_fun_def null_option_def split: if_split_asm)
  apply(rule conjI, rule impI) apply (metis drop.simps option.distinct(1) invalid_def)
  apply(rule impI, rule conjI, rule impI) apply (metis option.distinct(1))
  apply(rule impI, rule conjI, rule impI) apply (metis drop.simps)
  apply(intro conjI impI ballI)
   proof - fix x show "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>None\<rfloor> \<Longrightarrow>
                       \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. \<exists>y. P (\<lambda>_. x) \<tau> = \<lfloor>y\<rfloor> \<Longrightarrow>
                       \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> P (\<lambda>\<tau>. x) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
   apply(erule_tac x = x in ballE)+
   by(rule disjE4[OF destruct_ocl[of "P (\<lambda>\<tau>. x) \<tau>"]],
      (simp add: true_def false_def null_fun_def null_option_def bot_fun_def bot_option_def)+)
 qed(simp add: assms[simplified OclValid_def true_def])+
qed

lemma OclForall_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) = (\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil>)"
 apply(simp add: OclForall_rep_set_true[OF x_def],
       simp add: OclIncludes_def OclValid_def y_def[simplified OclValid_def])
 apply(insert Set_inv_lemma[OF x_def], simp add: valid_def false_def true_def bot_fun_def)
by(rule iffI, simp add: subsetI, simp add: subsetD)

lemma OclForall_not_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil>)"
 apply(simp add: OclForall_rep_set_false[OF x_def],
       simp add: OclIncludes_def OclValid_def y_def[simplified OclValid_def])
 apply(insert Set_inv_lemma[OF x_def], simp add: valid_def false_def true_def bot_fun_def)
by(rule iffI, metis rev_subsetD, metis subsetI)

lemma OclForall_iterate:
 assumes S_finite: "finite \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>"
   shows "S->forAll\<^sub>S\<^sub>e\<^sub>t(x | P x) \<tau> = (S->iterate\<^sub>S\<^sub>e\<^sub>t(x; acc = true | acc and P x)) \<tau>"
proof -
 have and_comm : "comp_fun_commute (\<lambda>x acc. acc and P x)"
  apply(simp add: comp_fun_commute_def comp_def)
 by (metis OclAnd_assoc OclAnd_commute)

 have ex_insert : "\<And>x F P. (\<exists>x\<in>insert x F. P x) = (P x \<or> (\<exists>x\<in>F. P x))"
 by (metis insert_iff)

 have destruct_ocl : "\<And>x \<tau>. x = true \<tau> \<or> x = false \<tau> \<or> x = null \<tau> \<or> x = \<bottom> \<tau>"
  apply(case_tac x) apply (metis bot_Boolean_def)
  apply(rename_tac x', case_tac x') apply (metis null_Boolean_def)
  apply(rename_tac x'', case_tac x'') apply (metis (full_types) true_def)
 by (metis (full_types) false_def)

 have disjE4 : "\<And> P1 P2 P3 P4 R.
   (P1 \<or> P2 \<or> P3 \<or> P4) \<Longrightarrow> (P1 \<Longrightarrow> R) \<Longrightarrow> (P2 \<Longrightarrow> R) \<Longrightarrow> (P3 \<Longrightarrow> R) \<Longrightarrow> (P4 \<Longrightarrow> R) \<Longrightarrow> R"
 by metis

 let ?P_eq = "\<lambda>x b \<tau>. P (\<lambda>_. x) \<tau> = b \<tau>"
 let ?P = "\<lambda>set b \<tau>. \<exists>x\<in>set. ?P_eq x b \<tau>"
 let ?if = "\<lambda>f b c. if f b \<tau> then b \<tau> else c"
 let ?forall = "\<lambda>P. ?if P false (?if P invalid (?if P null (true \<tau>)))"
 show ?thesis
  apply(simp only: OclForall_def OclIterate_def)
  apply(case_tac "\<tau> \<Turnstile> \<delta> S", simp only: OclValid_def)
   apply(subgoal_tac "let set = \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> in
                      ?forall (?P set) =
                      Finite_Set.fold (\<lambda>x acc. acc and P x) true ((\<lambda>a \<tau>. a) ` set) \<tau>",
         simp only: Let_def, simp add: S_finite, simp only: Let_def)
   apply(case_tac "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil> = {}", simp)
   apply(rule finite_ne_induct[OF S_finite], simp)
    (* *)
    apply(simp only: image_insert)
    apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
     apply (metis empty_iff image_empty)
    apply(simp add: invalid_def)
    apply (metis bot_fun_def destruct_ocl null_fun_def)
   (* *)
   apply(simp only: image_insert)
   apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
    apply (metis (mono_tags) imageE)

   (* *)
   apply(subst cp_OclAnd) apply(drule sym, drule sym, simp only:, drule sym, simp only:)
   apply(simp only: ex_insert)
   apply(subgoal_tac "\<exists>x. x\<in>F") prefer 2
    apply(metis all_not_in_conv)
   proof - fix x F show "(\<delta> S) \<tau> = true \<tau> \<Longrightarrow> \<exists>x. x \<in> F \<Longrightarrow>
            ?forall (\<lambda>b \<tau>. ?P_eq x b \<tau> \<or> ?P F b \<tau>) =
            ((\<lambda>_. ?forall (?P F)) and (\<lambda>_. P (\<lambda>\<tau>. x) \<tau>)) \<tau>"
    apply(rule disjE4[OF destruct_ocl[where x1 = "P (\<lambda>\<tau>. x) \<tau>"]])
       apply(simp_all add: true_def false_def invalid_def OclAnd_def
                           null_fun_def null_option_def bot_fun_def bot_option_def)
   by (metis (lifting) option.distinct(1))+
 qed(simp add: OclValid_def)+
qed

lemma OclForall_cong:
 assumes "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<tau> \<Turnstile> P (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> Q (\<lambda>\<tau>. x)"
 assumes P: "\<tau> \<Turnstile> OclForall X P"
 shows "\<tau> \<Turnstile> OclForall X Q"
proof -
 have def_X: "\<tau> \<Turnstile> \<delta> X"
 by(insert P, simp add: OclForall_def OclValid_def bot_option_def true_def split: if_split_asm)
 show ?thesis
  apply(insert P)
  apply(subst (asm) OclForall_rep_set_true[OF def_X], subst OclForall_rep_set_true[OF def_X])
 by (simp add: assms)
qed

lemma OclForall_cong':
 assumes "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<tau> \<Turnstile> P (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> Q (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> R (\<lambda>\<tau>. x)"
 assumes P: "\<tau> \<Turnstile> OclForall X P"
 assumes Q: "\<tau> \<Turnstile> OclForall X Q"
 shows "\<tau> \<Turnstile> OclForall X R"
proof -
 have def_X: "\<tau> \<Turnstile> \<delta> X"
 by(insert P, simp add: OclForall_def OclValid_def bot_option_def true_def split: if_split_asm)
 show ?thesis
  apply(insert P Q)
  apply(subst (asm) (1 2) OclForall_rep_set_true[OF def_X], subst OclForall_rep_set_true[OF def_X])
 by (simp add: assms)
qed

text\<open>Strict Equality\<close>

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_defined :
 assumes x_def: "\<tau> \<Turnstile> \<delta> x"
 assumes y_def: "\<tau> \<Turnstile> \<delta> y"
 shows "((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) \<tau> =
                (x->forAll\<^sub>S\<^sub>e\<^sub>t(z| y->includes\<^sub>S\<^sub>e\<^sub>t(z)) and (y->forAll\<^sub>S\<^sub>e\<^sub>t(z| x->includes\<^sub>S\<^sub>e\<^sub>t(z)))) \<tau>"
proof -
 have rep_set_inj : "\<And>\<tau>. (\<delta> x) \<tau> = true \<tau> \<Longrightarrow>
                         (\<delta> y) \<tau> = true \<tau> \<Longrightarrow>
                          x \<tau> \<noteq> y \<tau> \<Longrightarrow>
                          \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil> \<noteq> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>"
  apply(simp add: defined_def)
  apply(split if_split_asm, simp add: false_def true_def)+
  apply(simp add: null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)

  apply(case_tac "x \<tau>", rename_tac x')
  apply(case_tac x', simp_all, rename_tac x'')
  apply(case_tac x'', simp_all)

  apply(case_tac "y \<tau>", rename_tac y')
  apply(case_tac y', simp_all, rename_tac y'')
  apply(case_tac y'', simp_all)

  apply(simp add: Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
 by(blast)

 show ?thesis
  apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def
    foundation20[OF x_def, simplified OclValid_def]
    foundation20[OF y_def, simplified OclValid_def])
  apply(subgoal_tac "\<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = true \<tau> \<or> \<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = false \<tau>")
   prefer 2
   apply(simp add: false_def true_def)
  (* *)
  apply(erule disjE)
   apply(simp add: true_def)

   apply(subgoal_tac "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) \<and> (\<tau> \<Turnstile> OclForall y (OclIncludes x))")
    apply(subst cp_OclAnd, simp add: true_def OclValid_def)
   apply(simp add: OclForall_includes[OF x_def y_def]
                   OclForall_includes[OF y_def x_def])

  (* *)
  apply(simp)

  apply(subgoal_tac "OclForall x (OclIncludes y) \<tau> = false \<tau> \<or>
                     OclForall y (OclIncludes x) \<tau> = false \<tau>")
   apply(subst cp_OclAnd, metis OclAnd_false1 OclAnd_false2 cp_OclAnd)
  apply(simp only: OclForall_not_includes[OF x_def y_def, simplified OclValid_def]
                   OclForall_not_includes[OF y_def x_def, simplified OclValid_def],
        simp add: false_def)
 by (metis OclValid_def rep_set_inj subset_antisym x_def y_def)
qed

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec[simp,code_unfold] :
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) =
  (if \<delta> x then (if \<delta> y
                then ((x->forAll\<^sub>S\<^sub>e\<^sub>t(z| y->includes\<^sub>S\<^sub>e\<^sub>t(z)) and (y->forAll\<^sub>S\<^sub>e\<^sub>t(z| x->includes\<^sub>S\<^sub>e\<^sub>t(z)))))
                else if \<upsilon> y
                      then false \<comment> \<open>\<open>x'->includes = null\<close>\<close>
                      else invalid
                      endif
                endif)
         else if \<upsilon> x \<comment> \<open>\<open>null = ???\<close>\<close>
              then if \<upsilon> y then not(\<delta> y) else invalid endif
              else invalid
              endif
         endif)"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<not> (\<tau> \<Turnstile> \<delta> P)) = ((\<delta> P) \<tau> = false \<tau>)"
 by (metis bot_fun_def OclValid_def defined_def foundation16 null_fun_def)

 have valid_inject_true : "\<And>\<tau> P. (\<not> (\<tau> \<Turnstile> \<upsilon> P)) = ((\<upsilon> P) \<tau> = false \<tau>)"
 by (metis bot_fun_def OclIf_true' OclIncludes_charn0 OclIncludes_charn0' OclValid_def valid_def
           foundation6 foundation9)
 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  (* *)
  apply(simp add: OclIf_def
                  defined_inject_true[simplified OclValid_def]
                  valid_inject_true[simplified OclValid_def],
        subst false_def, subst true_def, simp)
  apply(subst (1 2) cp_OclNot, simp, simp add: cp_OclNot[symmetric])
  apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_defined[simplified OclValid_def])
 by(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def false_def true_def valid_def defined_def)
qed

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow>
    \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def)
 apply(split if_split_asm)
  apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma OclIncluding_cong' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
    \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including\<^sub>S\<^sub>e\<^sub>t(x) \<doteq> (t->including\<^sub>S\<^sub>e\<^sub>t(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including\<^sub>S\<^sub>e\<^sub>t(x)))"
  apply(simp add: cp_def, subst OclIncluding.cp0)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including\<^sub>S\<^sub>e\<^sub>t(x))" in StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1)
       apply(rule cp)
      apply(simp add: foundation20) apply(simp add: foundation20)
    apply (simp add: foundation10 foundation6)+
 done
qed

lemma OclIncluding_cong : "\<And>(s::('\<AA>,'a::null)Set) t x y \<tau>. \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             \<tau> \<Turnstile> s \<doteq> t \<Longrightarrow> x = y \<Longrightarrow> \<tau> \<Turnstile> s->including\<^sub>S\<^sub>e\<^sub>t(x) \<doteq> (t->including\<^sub>S\<^sub>e\<^sub>t(y))"
 apply(simp only:)
 apply(rule OclIncluding_cong', simp_all only:)
by(auto simp: OclValid_def OclIf_def invalid_def bot_option_def OclNot_def split : if_split_asm)

(* < *)
lemma const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_empty : "const X \<Longrightarrow>  const (X \<doteq> Set{})" 
 apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.const, assumption)
by(simp)

lemma const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including : 
 "const a \<Longrightarrow> const S \<Longrightarrow> const X \<Longrightarrow>  const (X \<doteq> S->including\<^sub>S\<^sub>e\<^sub>t(a))"
 apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.const, assumption)
by(rule const_OclIncluding)

subsection\<open>Test Statements\<close>

Assert   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
Assert   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>x\<rfloor>}))"

instantiation Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (equal)equal
begin
  definition "HOL.equal k l \<longleftrightarrow>  (k::('a::equal)Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) =  l"
  instance   by standard (rule equal_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
end

lemma equal_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_code [code]:
  "HOL.equal k (l::('a::{equal,null})Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<longleftrightarrow> Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e k = Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e l"
  by (auto simp add: equal Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)

Assert   "\<tau> \<Turnstile> (Set{} \<doteq> Set{})" 
Assert   "\<tau> \<Turnstile> (Set{\<one>,\<two>} \<triangleq> Set{}->including\<^sub>S\<^sub>e\<^sub>t(\<two>)->including\<^sub>S\<^sub>e\<^sub>t(\<one>))" 
Assert   "\<tau> \<Turnstile> (Set{\<one>,invalid,\<two>} \<triangleq> invalid)"
Assert   "\<tau> \<Turnstile> (Set{\<one>,\<two>}->including\<^sub>S\<^sub>e\<^sub>t(null) \<triangleq> Set{null,\<one>,\<two>})"
Assert   "\<tau> \<Turnstile> (Set{\<one>,\<two>}->including\<^sub>S\<^sub>e\<^sub>t(null) \<triangleq> Set{\<one>,\<two>,null})"

(*
Assert   "\<not> (\<tau> \<Turnstile> (Set{\<one>,\<one>,\<two>} \<doteq> Set{\<one>,\<two>}))"
Assert   "\<not> (\<tau> \<Turnstile> (Set{\<one>,\<two>} \<doteq> Set{\<two>,\<one>}))"
*)

(* > *)

end
