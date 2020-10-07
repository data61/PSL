(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Sequence.thy --- Library definitions.
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


theory  UML_Sequence
imports "../basic_types/UML_Boolean"
        "../basic_types/UML_Integer"
begin

no_notation None ("\<bottom>")
section\<open>Collection Type Sequence: Operations\<close>

subsection\<open>Basic Properties of the Sequence Type\<close>

text\<open>Every element in a defined sequence is valid.\<close>

lemma Sequence_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<forall>x\<in>set \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot"
apply(insert Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def
           split:if_split_asm)
 apply(erule contrapos_pp [of "Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = bot"])
 apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
 apply(simp add: Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = null"])
apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
apply(simp add: Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse  null_option_def)
by (simp add: bot_option_def)

subsection\<open>Definition: Strict Equality \label{sec:seq-strict-equality}\<close>

text\<open>After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:\<close>

overloading
  StrictRefEq \<equiv> "StrictRefEq :: [('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>::null)Sequence] \<Rightarrow> ('\<AA>)Boolean"
begin
  definition StrictRefEq\<^sub>S\<^sub>e\<^sub>q :
    "((x::('\<AA>,'\<alpha>::null)Sequence) \<doteq> y) \<equiv> (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                                then (x \<triangleq> y)\<tau>
                                                else invalid \<tau>)"
end

text_raw\<open>\isatagafp\<close>
text\<open>One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its oid stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF-invariant), the referential equality and the
strong equality---and therefore the strict equality on sequences in the sense above---coincides.\<close>
text_raw\<open>\endisatagafp\<close>

text\<open>Property proof in terms of @{term "profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v"}\<close>
interpretation  StrictRefEq\<^sub>S\<^sub>e\<^sub>q : profile_bin\<^sub>S\<^sub>t\<^sub>r\<^sub>o\<^sub>n\<^sub>g\<^sub>E\<^sub>q_\<^sub>v_\<^sub>v "\<lambda> x y. (x::('\<AA>,'\<alpha>::null)Sequence) \<doteq> y" 
                by unfold_locales (auto simp:  StrictRefEq\<^sub>S\<^sub>e\<^sub>q)



subsection\<open>Constants: mtSequence\<close>
definition mtSequence ::"('\<AA>,'\<alpha>::null) Sequence"  ("Sequence{}")
where     "Sequence{} \<equiv> (\<lambda> \<tau>.  Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>[]::'\<alpha> list\<rfloor>\<rfloor> )"


lemma mtSequence_defined[simp,code_unfold]:"\<delta>(Sequence{}) = true"
apply(rule ext, auto simp: mtSequence_def defined_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                           bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_valid[simp,code_unfold]:"\<upsilon>(Sequence{}) = true"
apply(rule ext,auto simp: mtSequence_def valid_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                          bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_rep_set: "\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Sequence{} \<tau>)\<rceil>\<rceil> = []"
 apply(simp add: mtSequence_def, subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
by(simp add: bot_option_def)+

text_raw\<open>\isatagafp\<close>

lemma [simp,code_unfold]: "const Sequence{}"
by(simp add: const_def mtSequence_def)

text\<open>Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid.\<close>

text_raw\<open>\endisatagafp\<close>


subsection\<open>Definition: Prepend\<close>
definition OclPrepend   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclPrepend x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> (y \<tau>)#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclPrepend   ("_->prepend\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclPrepend:profile_bin\<^sub>d_\<^sub>v OclPrepend "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -  
 have A : "\<And>x y. x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> bot  \<Longrightarrow>
           \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                         defined_def false_def true_def null_fun_def bot_fun_def])  
                                       
         show "profile_bin\<^sub>d_\<^sub>v OclPrepend (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclPrepend_def bot_option_def null_option_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
               bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" 
                in contrapos_pp)
          apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject [OF A])
             apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" 
               in contrapos_pp)
         apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF A])
            apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
                                 bot_option_def null_option_def)
         done
qed
                
syntax
  "_OclFinsequence" :: "args => ('\<AA>,'a::null) Sequence"    ("Sequence{(_)}")
translations
  "Sequence{x, xs}" == "CONST OclPrepend (Sequence{xs}) x"
  "Sequence{x}"     == "CONST OclPrepend (Sequence{}) x "

subsection\<open>Definition: Including\<close>

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>  @ [y \<tau>] \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclIncluding   ("_->including\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclIncluding : 
               profile_bin\<^sub>d_\<^sub>v OclIncluding "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor>"
proof -  
 have A : "\<And>x y. x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> bot  \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                         defined_def false_def true_def null_fun_def bot_fun_def])  
                                       
         show "profile_bin\<^sub>d_\<^sub>v OclIncluding (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclIncluding_def bot_option_def null_option_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
               bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" 
                in contrapos_pp)
          apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject [OF A])
             apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" 
               in contrapos_pp)
         apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF A])
            apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def null_option_def)
         done
qed

lemma [simp,code_unfold] : "(Sequence{}->including\<^sub>S\<^sub>e\<^sub>q(a)) = (Sequence{}->prepend\<^sub>S\<^sub>e\<^sub>q(a))"
  apply(simp add: OclIncluding_def OclPrepend_def mtSequence_def)
  apply(subst (1 2) Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp)
by(metis drop.simps append_Nil)

lemma [simp,code_unfold] : "((S->prepend\<^sub>S\<^sub>e\<^sub>q(a))->including\<^sub>S\<^sub>e\<^sub>q(b)) = ((S->including\<^sub>S\<^sub>e\<^sub>q(b))->prepend\<^sub>S\<^sub>e\<^sub>q(a))"
 proof -
  have A: "\<And>S b \<tau>. S \<noteq> \<bottom> \<Longrightarrow> S \<noteq> null \<Longrightarrow> b \<noteq> \<bottom>  \<Longrightarrow>
                   \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil> @ [b]\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
           by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                                        defined_def false_def true_def null_fun_def bot_fun_def])          
  have B: "\<And>S a \<tau>. S \<noteq> \<bottom> \<Longrightarrow> S \<noteq> null \<Longrightarrow> a \<noteq> \<bottom>  \<Longrightarrow>
                   \<lfloor>\<lfloor>a # \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
           by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                                        defined_def false_def true_def null_fun_def bot_fun_def])          
 show ?thesis
  apply(simp add: OclIncluding_def OclPrepend_def mtSequence_def, rule ext)
  apply(subst (2 5) cp_defined, simp split:)
  apply(intro conjI impI)
        apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF B],
              (simp add: foundation16[simplified OclValid_def] foundation18'[simplified OclValid_def])+)
        apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF A],
              (simp add: foundation16[simplified OclValid_def] foundation18'[simplified OclValid_def])+)
       apply(simp add: OclIncluding.def_body)
      apply (metis OclValid_def foundation16 invalid_def)
     apply (metis (no_types) OclPrepend.def_body' OclValid_def foundation16)
 by (metis OclValid_def foundation16 invalid_def)+
qed

subsection\<open>Definition: Excluding\<close>
definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclExcluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> filter (\<lambda>x. x = y \<tau>)
                                                                   \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclExcluding   ("_->excluding\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclExcluding:profile_bin\<^sub>d_\<^sub>v OclExcluding 
                          "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> filter (\<lambda>x. x = y) \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x)\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -
    show "profile_bin\<^sub>d_\<^sub>v OclExcluding (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>[x\<leftarrow>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> . x = y]\<rfloor>\<rfloor>)"
         apply unfold_locales  
         apply(auto simp:OclExcluding_def bot_option_def null_option_def  
                         null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
         apply(subst (asm) Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
               simp_all add: null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def null_option_def)+
   done
qed

subsection\<open>Definition: Append\<close>
text\<open>Identical to OclIncluding.\<close>
definition OclAppend   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclAppend = OclIncluding"
notation   OclAppend   ("_->append\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclAppend : 
               profile_bin\<^sub>d_\<^sub>v OclAppend "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor>"
         apply unfold_locales
 by(auto simp: OclAppend_def bin_def bin'_def
               OclIncluding.def_scheme OclIncluding.def_body)

subsection\<open>Definition: Union\<close>
definition OclUnion   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclUnion x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> @
                                                        \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>
                                else invalid \<tau> )"
notation   OclUnion   ("_->union\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclUnion : 
               profile_bin\<^sub>d_\<^sub>d OclUnion "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -  
   have A : "\<And>x y. x \<noteq> \<bottom> \<Longrightarrow>  x \<noteq> null \<Longrightarrow> \<forall>x\<in>set \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>. x \<noteq> \<bottom> " 
            apply(rule Sequence_inv_lemma[of \<tau>])
            by(simp add: defined_def OclValid_def bot_fun_def null_fun_def false_def true_def)   
   show "profile_bin\<^sub>d_\<^sub>d OclUnion (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>@\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e y\<rceil>\<rceil>\<rfloor>\<rfloor>)"
   apply unfold_locales 
   apply(auto simp:OclUnion_def bot_option_def null_option_def 
                   null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
   by(subst (asm) Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject,
      simp_all add: bot_option_def null_option_def  Set.ball_Un A null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)+
qed

subsection\<open>Definition: At\<close>
definition OclAt   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>) Integer] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclAt x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                             then if  1 \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> \<and>  \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> \<le> length\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> 
                                  then \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> ! (nat \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> - 1) 
                                  else invalid \<tau>
                             else invalid \<tau> )"
notation   OclAt ("_->at\<^sub>S\<^sub>e\<^sub>q'(_')")
(*TODO Locale - Equivalent*)  


subsection\<open>Definition: First\<close>
definition OclFirst   :: "[('\<AA>,'\<alpha>::null) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclFirst x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> then
                                case \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> of [] \<Rightarrow> invalid \<tau>
                                                               | x # _ \<Rightarrow> x
                              else invalid \<tau> )"
notation   OclFirst   ("_->first\<^sub>S\<^sub>e\<^sub>q'(_')")
(*TODO Locale - Equivalent*)  


subsection\<open>Definition: Last\<close>
definition OclLast   :: "[('\<AA>,'\<alpha>::null) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclLast x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> then
                               if \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> = [] then
                                 invalid \<tau>
                               else
                                 last \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>
                             else invalid \<tau> )"
notation   OclLast   ("_->last\<^sub>S\<^sub>e\<^sub>q'(_')")
(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Iterate\<close>

definition OclIterate :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<beta>::null)val,
                           ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where     "OclIterate S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> 
                                    then (foldr (F) (map (\<lambda>a \<tau>. a) \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))(A)\<tau>
                                    else \<bottom>)"
syntax  
  "_OclIterateSeq"  :: "[('\<AA>,'\<alpha>::null) Sequence, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate\<^sub>S\<^sub>e\<^sub>q'(_;_=_ | _')" (*[71,100,70]50*))
translations
  "X->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P)" == "CONST OclIterate X A (%a. (% x. P))"

(*TODO Locale - Equivalent*)  

  
  
subsection\<open>Definition: Forall\<close>
definition OclForall     :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = true | x and (P b)))"

syntax
  "_OclForallSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forAll\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->forAll\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST UML_Sequence.OclForall X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Exists\<close>
definition OclExists     :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = false | x or (P b)))"

syntax
  "_OclExistSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->exists\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST OclExists X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Collect\<close>
definition OclCollect     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val]\<Rightarrow>('\<AA>,'\<beta>::null)Sequence"
where     "OclCollect S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = Sequence{} | x->prepend\<^sub>S\<^sub>e\<^sub>q(P b)))"

syntax
  "_OclCollectSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->collect\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->collect\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST OclCollect X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Select\<close>
definition OclSelect     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean]\<Rightarrow>('\<AA>,'\<alpha>::null)Sequence"
where     "OclSelect S P = 
           (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = Sequence{} | if P b then x->prepend\<^sub>S\<^sub>e\<^sub>q(b) else x endif))"

syntax
  "_OclSelectSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"  ("(_)->select\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->select\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST UML_Sequence.OclSelect X (%x. P)"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Size\<close>
definition OclSize     :: "[('\<AA>,'\<alpha>::null)Sequence]\<Rightarrow>('\<AA>)Integer" ("(_)->size\<^sub>S\<^sub>e\<^sub>q'(')")
where     "OclSize S = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = \<zero> | x +\<^sub>i\<^sub>n\<^sub>t \<one> ))"

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: IsEmpty\<close>
definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Sequence \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty\<^sub>S\<^sub>e\<^sub>q'(')" (*[66]*))

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: NotEmpty\<close>

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Sequence \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty\<^sub>S\<^sub>e\<^sub>q'(')" (*[66]*))

(*TODO Locale - Equivalent*)  

subsection\<open>Definition: Any\<close>

definition "OclANY x = (\<lambda> \<tau>.
  if x \<tau> = invalid \<tau> then
    \<bottom>
  else
    case drop (drop (Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>))) of [] \<Rightarrow> \<bottom>
                                              | l \<Rightarrow> hd l)"
notation   OclANY   ("_->any\<^sub>S\<^sub>e\<^sub>q'(')")

(*TODO Locale - Equivalent*)  

subsection\<open>Definition (future operators)\<close>

consts (* abstract set collection operations *)
    OclCount       :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) Sequence] \<Rightarrow> '\<AA> Integer"
  (*OclFlatten*)
  (*OclInsertAt*)
  (*OclSubSequence*)
  (*OclIndexOf*)
  (*OclReverse*)
    OclSum         :: " ('\<AA>,'\<alpha>::null) Sequence \<Rightarrow> '\<AA> Integer"
  
notation  OclCount       ("_->count\<^sub>S\<^sub>e\<^sub>q'(_')" (*[66,65]65*))
notation  OclSum         ("_->sum\<^sub>S\<^sub>e\<^sub>q'(')" (*[66]*))

subsection\<open>Logical Properties\<close>

subsection\<open>Execution Laws with Invalid or Null as Argument\<close>

text\<open>OclIterate\<close>

lemma OclIterate_invalid[simp,code_unfold]:"invalid->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P a x) = invalid"  
by(simp add: OclIterate_def false_def true_def, simp add: invalid_def)

lemma OclIterate_null[simp,code_unfold]:"null->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P a x) = invalid"  
by(simp add: OclIterate_def false_def true_def, simp add: invalid_def)

lemma OclIterate_invalid_args[simp,code_unfold]:"S->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

text_raw\<open>\isatagafp\<close>

subsubsection\<open>Context Passing\<close>

lemma cp_OclIncluding:
"(X->including\<^sub>S\<^sub>e\<^sub>q(x)) \<tau> = ((\<lambda> _. X \<tau>)->including\<^sub>S\<^sub>e\<^sub>q(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncluding_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIterate: 
     "(X->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate_def cp_defined[symmetric])

lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>q[intro!,simp,code_unfold] = 
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncluding"]]

subsubsection\<open>Const\<close>

text_raw\<open>\endisatagafp\<close>

subsection\<open>General Algebraic Execution Rules\<close>
subsubsection\<open>Execution Rules on Iterate\<close>

lemma OclIterate_empty[simp,code_unfold]:"Sequence{}->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P a x) = A"  
apply(simp add: OclIterate_def foundation22[symmetric] foundation13, 
      rule ext, rename_tac "\<tau>")
apply(case_tac "\<tau> \<Turnstile> \<upsilon> A", simp_all add: foundation18')
apply(simp add: mtSequence_def)
apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse) by auto

text\<open>In particular, this does hold for A = null.\<close>

lemma OclIterate_including[simp,code_unfold]:
assumes strict1 : "\<And>X. P invalid X = invalid"
and     P_valid_arg: "\<And> \<tau>. (\<upsilon> A) \<tau> = (\<upsilon> (P a A)) \<tau>"
and     P_cp    : "\<And> x y \<tau>. P x y \<tau> = P (\<lambda> _. x \<tau>) y \<tau>"
and     P_cp'   : "\<And> x y \<tau>. P x y \<tau> = P x (\<lambda> _. y \<tau>) \<tau>"
shows  "(S->including\<^sub>S\<^sub>e\<^sub>q(a))->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = A | P b x) = S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = P a A| P b x)"
 apply(rule ext)
proof -
 have A: "\<And>S b \<tau>. S \<noteq> \<bottom> \<Longrightarrow> S \<noteq> null \<Longrightarrow> b \<noteq> \<bottom>  \<Longrightarrow>
                  \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil> @ [b]\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                                       defined_def false_def true_def null_fun_def bot_fun_def])          
 have P: "\<And>l A A' \<tau>. A \<tau> = A' \<tau> \<Longrightarrow> foldr P l A \<tau> = foldr P l A' \<tau>"
  apply(rule list.induct, simp, simp)
 by(subst (1 2) P_cp', simp)

 fix \<tau>
 show "OclIterate (S->including\<^sub>S\<^sub>e\<^sub>q(a)) A P \<tau> = OclIterate S (P a A) P \<tau>"
  apply(subst cp_OclIterate, subst OclIncluding_def, simp split:)
  apply(intro conjI impI)

   apply(simp add: OclIterate_def)
   apply(intro conjI impI)
     apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF A],
           (simp add: foundation16[simplified OclValid_def] foundation18'[simplified OclValid_def])+)
     apply(rule P, metis P_cp)
    apply (metis P_valid_arg)
   apply(simp add: P_valid_arg[symmetric])
   apply (metis (lifting, no_types) OclIncluding.def_body' OclValid_def foundation16)
  apply(simp add: OclIterate_def defined_def invalid_def bot_option_def bot_fun_def false_def true_def)
  apply(intro impI, simp add: false_def true_def P_valid_arg)
 by (metis P_cp P_valid_arg UML_Types.bot_fun_def cp_valid invalid_def strict1 true_def valid1 valid_def)
qed

lemma OclIterate_prepend[simp,code_unfold]:
assumes strict1 : "\<And>X. P invalid X = invalid"
and     strict2 : "\<And>X. P X invalid = invalid"
and     P_cp    : "\<And> x y \<tau>. P x y \<tau> = P (\<lambda> _. x \<tau>) y \<tau>"
and     P_cp'   : "\<And> x y \<tau>. P x y \<tau> = P x (\<lambda> _. y \<tau>) \<tau>"
shows  "(S->prepend\<^sub>S\<^sub>e\<^sub>q(a))->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = A | P b x) = P a (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = A| P b x))"
 apply(rule ext)
proof -
 have B: "\<And>S a \<tau>. S \<noteq> \<bottom> \<Longrightarrow> S \<noteq> null \<Longrightarrow> a \<noteq> \<bottom>  \<Longrightarrow>
                  \<lfloor>\<lfloor>a # \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e S\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                                       defined_def false_def true_def null_fun_def bot_fun_def])          
 fix \<tau>
 show "OclIterate (S->prepend\<^sub>S\<^sub>e\<^sub>q(a)) A P \<tau> = P a (OclIterate S A P) \<tau>"
  apply(subst cp_OclIterate, subst OclPrepend_def, simp split:)
  apply(intro conjI impI)

   apply(subst P_cp')
   apply(simp add: OclIterate_def)
   apply(intro conjI impI)
     apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse[OF B],
           (simp add: foundation16[simplified OclValid_def] foundation18'[simplified OclValid_def])+)
     apply(simp add: P_cp'[symmetric])
     apply(subst P_cp, simp add: P_cp[symmetric])
    apply (metis (no_types) OclPrepend.def_body' OclValid_def foundation16)
   apply (metis P_cp' invalid_def strict2 valid_def)

  apply(subst P_cp',
        simp add: OclIterate_def defined_def invalid_def bot_option_def bot_fun_def false_def true_def,
        intro conjI impI)
     apply (metis P_cp' invalid_def strict2 valid_def)
    apply (metis P_cp' invalid_def strict2 valid_def)
   apply (metis (no_types) P_cp invalid_def strict1 true_def valid1 valid_def)
  apply (metis P_cp' invalid_def strict2 valid_def)
 done
qed


(* < *)

subsection\<open>Test Statements\<close>
(*
Assert   "(\<tau> \<Turnstile> (Sequence{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Sequence{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
Assert   "(\<tau> \<Turnstile> (Sequence{\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Sequence{\<lambda>_. \<lfloor>x\<rfloor>}))"
*)

instantiation Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (equal)equal
begin
  definition "HOL.equal k l \<longleftrightarrow>  (k::('a::equal)Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) =  l"
  instance   by standard (rule equal_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
end

lemma equal_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_code [code]:
  "HOL.equal k (l::('a::{equal,null})Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<longleftrightarrow> Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e k = Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e l"
  by (auto simp add: equal Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  
Assert   "\<tau> \<Turnstile> (Sequence{} \<doteq> Sequence{})" 
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,\<two>} \<triangleq> Sequence{}->prepend\<^sub>S\<^sub>e\<^sub>q(\<two>)->prepend\<^sub>S\<^sub>e\<^sub>q(\<one>))" 
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,invalid,\<two>} \<triangleq> invalid)"
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,\<two>}->prepend\<^sub>S\<^sub>e\<^sub>q(null) \<triangleq> Sequence{null,\<one>,\<two>})"
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,\<two>}->including\<^sub>S\<^sub>e\<^sub>q(null) \<triangleq> Sequence{\<one>,\<two>,null})"

(* 
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<one>,\<two>} \<doteq> Sequence{\<one>,\<two>}))"
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<two>} \<doteq> Sequence{\<two>,\<one>}))"
*)

(* > *)

end
