(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Pair.thy --- Library definitions.
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

theory  UML_Pair
imports "../UML_PropertyProfiles"
begin

section\<open>Collection Type Pairs: Operations \label{sec:collection_pairs}\<close>

text\<open>The OCL standard provides the concept of \emph{Tuples}, \ie{} a family of record-types
with projection functions. In FeatherWeight OCL,  only the theory of a special case is
developped, namely the type of Pairs, which is, however, sufficient for all applications
since it can be used to mimick all tuples. In particular, it can be used to express operations
with multiple arguments, roles of n-ary associations, ...\<close>

subsection\<open>Semantic Properties of the Type Constructor\<close>

lemma A[simp]:"Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> None \<Longrightarrow> Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> null \<Longrightarrow> (fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
by(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x],auto simp:null_option_def bot_option_def)

lemma A'[simp]:" x \<noteq> bot \<Longrightarrow>  x \<noteq> null \<Longrightarrow> (fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
apply(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x], simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(auto simp:null_option_def bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: null_option_def bot_option_def)
done

lemma B[simp]:"Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> None \<Longrightarrow> Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> null \<Longrightarrow> (snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
by(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x],auto simp:null_option_def bot_option_def)

lemma B'[simp]:"x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow> (snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
apply(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x], simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(auto simp:null_option_def bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: null_option_def bot_option_def)
done

subsection\<open>Fundamental Properties of Strict Equality \label{sec:pair-strict-eq}\<close>

text\<open>After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:\<close>

overloading
  StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>,'\<alpha>::null,'\<beta>::null)Pair,('\<AA>,'\<alpha>::null,'\<beta>::null)Pair] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r :
    "((x::('\<AA>,'\<alpha>::null,'\<beta>::null)Pair) \<doteq> y) \<equiv> (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                                     then (x \<triangleq> y)\<tau>
                                                     else invalid \<tau>)"
end

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>,'\<alpha>::null,'\<beta>::null)Pair) \<doteq> y" 
                by unfold_locales (auto simp:  StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r)
 
subsection\<open>Standard Operations Definitions\<close>

text\<open>This part provides a collection of operators for the Pair type.\<close>

subsubsection\<open>Definition: Pair Constructor\<close>

definition OclPair::"('\<AA>, '\<alpha>) val \<Rightarrow>
                     ('\<AA>, '\<beta>) val \<Rightarrow>
                     ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair"  ("Pair{(_),(_)}")
where     "Pair{X,Y} \<equiv> (\<lambda> \<tau>. if (\<upsilon> X) \<tau> = true \<tau> \<and> (\<upsilon> Y) \<tau> = true \<tau>
                              then Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>(X \<tau>, Y \<tau>)\<rfloor>\<rfloor>
                              else invalid \<tau>)"

interpretation OclPair : profile_bin\<^sub>v_\<^sub>v  
               OclPair "\<lambda> x y. Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>(x, y)\<rfloor>\<rfloor>"                             
               apply(unfold_locales, auto simp:  OclPair_def bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
               by(auto simp: Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject null_option_def bot_option_def)
             

subsubsection\<open>Definition: First\<close>

definition OclFirst::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<alpha>) val"  (" _ .First'(')")
where     "X .First() \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                              else invalid \<tau>)"


interpretation OclFirst : profile_mono\<^sub>d OclFirst "\<lambda>x.  fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x)\<rceil>\<rceil>"
                          by unfold_locales (auto simp:  OclFirst_def)

subsubsection\<open>Definition: Second\<close>
                              
definition OclSecond::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<beta>) val"  ("_ .Second'(')")
where     "X .Second() \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                               then snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                               else invalid \<tau>)"

interpretation OclSecond : profile_mono\<^sub>d OclSecond "\<lambda>x.  snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x)\<rceil>\<rceil>"
                           by unfold_locales  (auto simp:  OclSecond_def)
                           
subsection\<open>Logical Properties\<close>

lemma 1 : "\<tau> \<Turnstile> \<upsilon> Y \<Longrightarrow> \<tau> \<Turnstile> Pair{X,Y} .First() \<triangleq> X"
apply(case_tac "\<not>(\<tau> \<Turnstile> \<upsilon> X)")
apply(erule foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                       THEN StrongEq_L_subst2_rev]],simp_all add:foundation18')
apply(auto simp: OclValid_def valid_def defined_def StrongEq_def OclFirst_def OclPair_def
                true_def false_def invalid_def bot_fun_def null_fun_def)
apply(auto simp: Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject null_option_def bot_option_def bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by(simp add: Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)

lemma 2 : "\<tau> \<Turnstile> \<upsilon> X \<Longrightarrow> \<tau> \<Turnstile> Pair{X,Y} .Second() \<triangleq> Y" 
apply(case_tac "\<not>(\<tau> \<Turnstile> \<upsilon> Y)")
apply(erule foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                       THEN StrongEq_L_subst2_rev]],simp_all add:foundation18')
apply(auto simp: OclValid_def valid_def defined_def StrongEq_def OclSecond_def OclPair_def
                true_def false_def invalid_def bot_fun_def null_fun_def)
apply(auto simp: Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject null_option_def bot_option_def bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
by(simp add: Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)

subsection\<open>Algebraic Execution Properties\<close>

lemma proj1_exec [simp, code_unfold] : "Pair{X,Y} .First() = (if (\<upsilon> Y) then X else invalid endif)"
apply(rule ext, rename_tac "\<tau>", simp add: foundation22[symmetric])
apply(case_tac "\<not>(\<tau> \<Turnstile> \<upsilon> Y)")
apply(erule foundation7'[THEN iffD2, 
                         THEN foundation15[THEN iffD2, 
                                           THEN StrongEq_L_subst2_rev]],simp_all)
apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> Y")
apply(erule foundation13[THEN iffD2, THEN StrongEq_L_subst2_rev], simp_all)
by(erule 1)

lemma proj2_exec [simp, code_unfold] : "Pair{X,Y} .Second() = (if (\<upsilon> X) then Y else invalid endif)"
apply(rule ext, rename_tac "\<tau>", simp add: foundation22[symmetric])
apply(case_tac "\<not>(\<tau> \<Turnstile> \<upsilon> X)")
apply(erule foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                  THEN StrongEq_L_subst2_rev]],simp_all)
apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> X")
apply(erule foundation13[THEN iffD2, THEN StrongEq_L_subst2_rev], simp_all)
by(erule 2)

(* < *)

subsection\<open>Test Statements\<close>
(*
Assert   "(\<tau> \<Turnstile> (Pair{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>,\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Pair{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>,\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
Assert   "(\<tau> \<Turnstile> (Pair{\<lambda>_. \<lfloor>x\<rfloor>,\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Pair{\<lambda>_. \<lfloor>x\<rfloor>,\<lambda>_. \<lfloor>x\<rfloor>}))"
*)

instantiation Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (equal,equal)equal
begin
  definition "HOL.equal k l \<longleftrightarrow>  (k::('a::equal,'b::equal)Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) =  l"
  instance   by standard (rule equal_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
end

lemma equal_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_code [code]:
  "HOL.equal k (l::('a::{equal,null},'b::{equal,null})Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<longleftrightarrow> Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e k = Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e l"
  by (auto simp add: equal Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)

Assert "\<tau> \<Turnstile> invalid .First() \<triangleq> invalid "
Assert "\<tau> \<Turnstile> null .First() \<triangleq> invalid "
Assert "\<tau> \<Turnstile> null .Second() \<triangleq> invalid .Second() "
Assert "\<tau> \<Turnstile> Pair{invalid, true} \<triangleq> invalid "
Assert "\<tau> \<Turnstile> \<upsilon>(Pair{null, true}.First())"
Assert "\<tau> \<Turnstile> (Pair{null, true}).First() \<triangleq> null "
Assert "\<tau> \<Turnstile> (Pair{null, Pair{true,invalid}}).First() \<triangleq> invalid "


(*
Assert   "\<not> (\<tau> \<Turnstile> (Pair{\<one>,\<two>} \<doteq> Pair{\<two>,\<one>}))"
*)

(* > *)

end
