(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Contracts.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
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

theory UML_Contracts
imports UML_State
begin

text\<open>Modeling of an operation contract for an operation  with 2 arguments,
       (so depending on three parameters if one takes "self" into account).\<close>

locale contract_scheme =
   fixes f_\<upsilon>
   fixes f_lam
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow> 
                 'b \<Rightarrow>
                  ('\<AA>,'res::null)val"
   fixes PRE
   fixes POST
   assumes def_scheme': "f self x \<equiv>  (\<lambda> \<tau>. SOME res. let res = \<lambda> _. res in
                                           if (\<tau> \<Turnstile> (\<delta> self)) \<and> f_\<upsilon> x \<tau>
                                           then (\<tau> \<Turnstile> PRE self x) \<and>
                                                (\<tau> \<Turnstile> POST self x res)
                                           else \<tau> \<Turnstile> res \<triangleq> invalid)"
   assumes all_post': "\<forall> \<sigma> \<sigma>' \<sigma>''. ((\<sigma>,\<sigma>') \<Turnstile> PRE self x) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self x)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E': "PRE (self) x \<tau> = PRE (\<lambda> _. self \<tau>) (f_lam x \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T':"POST (self) x (res) \<tau> = POST (\<lambda> _. self \<tau>) (f_lam x \<tau>) (\<lambda> _. res \<tau>) \<tau>"
   assumes f_\<upsilon>_val: "\<And>a1. f_\<upsilon> (f_lam a1 \<tau>) \<tau> = f_\<upsilon> a1 \<tau>"
begin  
   lemma strict0 [simp]: "f invalid X = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme' StrongEq_def OclValid_def false_def true_def)

   lemma nullstrict0[simp]: "f null X = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme' StrongEq_def OclValid_def false_def true_def)
    
   lemma cp0 : "f self a1 \<tau> = f (\<lambda> _. self \<tau>) (f_lam a1 \<tau>) \<tau>"
   proof -
      have A: "(\<tau> \<Turnstile> \<delta> (\<lambda>_. self \<tau>)) = (\<tau> \<Turnstile> \<delta> self)" by(simp add: OclValid_def cp_defined[symmetric])
      have B: "f_\<upsilon> (f_lam a1 \<tau>) \<tau> = f_\<upsilon> a1 \<tau>" by (rule f_\<upsilon>_val)
      have D: "(\<tau> \<Turnstile> PRE (\<lambda>_. self \<tau>) (f_lam a1 \<tau>)) = ( \<tau> \<Turnstile> PRE self a1 )"
                                                 by(simp add: OclValid_def cp\<^sub>P\<^sub>R\<^sub>E'[symmetric])
      show ?thesis
        apply(auto simp: def_scheme' A B D)
        apply(simp add: OclValid_def)
        by(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T', simp)
      qed

   theorem unfold' : 
      assumes context_ok:    "cp E"
      and args_def_or_valid: "(\<tau> \<Turnstile> \<delta> self) \<and> f_\<upsilon> a1 \<tau>"
      and pre_satisfied:     "\<tau> \<Turnstile> PRE self a1"
      and post_satisfiable:  " \<exists>res. (\<tau> \<Turnstile> POST self a1 (\<lambda> _. res))"
      and sat_for_sols_post: "(\<And>res. \<tau> \<Turnstile> POST self a1 (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self a1)"
   proof -  
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)
         apply(simp add:def_scheme' args_def_or_valid pre_satisfied)
         apply(insert post_satisfiable, elim exE)
         apply(rule Hilbert_Choice.someI2, assumption)
         by(rule sat_for_sols_post, simp)
   qed
   
   lemma unfold2' :
      assumes context_ok:      "cp E"
      and args_def_or_valid:   "(\<tau> \<Turnstile> \<delta> self) \<and> (f_\<upsilon> a1 \<tau>)"
      and pre_satisfied:       "\<tau> \<Turnstile> PRE self a1"
      and postsplit_satisfied: "\<tau> \<Turnstile> POST' self a1" (* split constraint holds on post-state *)
      and post_decomposable  : "\<And> res. (POST self a1 res) = 
                                       ((POST' self a1)  and (res \<triangleq> (BODY self a1)))"
      shows "(\<tau> \<Turnstile> E(f self a1)) = (\<tau> \<Turnstile> E(BODY self a1))"
   proof -
      have cp0: "\<And> X \<tau>. E X \<tau> = E (\<lambda>_. X \<tau>) \<tau>" by(insert context_ok[simplified cp_def], auto)
      show ?thesis
         apply(simp add: OclValid_def, subst cp0, fold OclValid_def)      
         apply(simp add:def_scheme' args_def_or_valid pre_satisfied 
                        post_decomposable postsplit_satisfied foundation10')
         apply(subst some_equality)
         apply(simp add: OclValid_def StrongEq_def true_def)+
         by(subst (2) cp0, rule refl)
   qed
end


locale contract0 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'res::null)val"
   fixes PRE
   fixes POST
   assumes def_scheme: "f self \<equiv>  (\<lambda> \<tau>. SOME res. let res = \<lambda> _. res in
                                        if (\<tau> \<Turnstile> (\<delta> self))
                                        then (\<tau> \<Turnstile> PRE self) \<and>
                                             (\<tau> \<Turnstile> POST self res)
                                        else \<tau> \<Turnstile> res \<triangleq> invalid)"
   assumes all_post: "\<forall> \<sigma> \<sigma>' \<sigma>''. ((\<sigma>,\<sigma>') \<Turnstile> PRE self) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self)  \<tau> = PRE (\<lambda> _. self \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"POST (self) (res) \<tau> = POST (\<lambda> _. self \<tau>) (\<lambda> _. res \<tau>) \<tau>"

sublocale contract0 < contract_scheme "\<lambda>_ _. True" "\<lambda>x _. x" "\<lambda>x _. f x" "\<lambda>x _. PRE x" "\<lambda>x _. POST x"
 apply(unfold_locales)
     apply(simp add: def_scheme, rule all_post, rule cp\<^sub>P\<^sub>R\<^sub>E, rule cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)
by simp

context contract0
begin
   lemma cp_pre: "cp self' \<Longrightarrow>  cp (\<lambda>X. PRE (self' X)  )"
   by(rule_tac f=PRE in cpI1, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   lemma cp_post: "cp self' \<Longrightarrow> cp res'  \<Longrightarrow> cp (\<lambda>X. POST (self' X) (res' X))"
   by(rule_tac f=POST in cpI2, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  

   lemma cp [simp]:  "cp self' \<Longrightarrow>  cp res' \<Longrightarrow> cp (\<lambda>X. f (self' X) )"
      by(rule_tac f=f in cpI1, auto intro:cp0)  

   lemmas unfold = unfold'[simplified]

   lemma unfold2 :
      assumes                  "cp E"
      and                      "(\<tau> \<Turnstile> \<delta> self)"
      and                      "\<tau> \<Turnstile> PRE self"
      and                      "\<tau> \<Turnstile> POST' self" (* split constraint holds on post-state *)
      and                      "\<And> res. (POST self res) = 
                                       ((POST' self)  and (res \<triangleq> (BODY self)))"
      shows "(\<tau> \<Turnstile> E(f self)) = (\<tau> \<Turnstile> E(BODY self))"
        apply(rule unfold2'[simplified])
      by((rule assms)+)

end

locale contract1 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> 
                  ('\<AA>,'res::null)val"
   fixes PRE
   fixes POST 
   assumes def_scheme: "f self a1 \<equiv> 
                               (\<lambda> \<tau>. SOME res. let res = \<lambda> _. res in
                                     if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> a1)
                                     then (\<tau> \<Turnstile> PRE self a1) \<and>
                                          (\<tau> \<Turnstile> POST self a1 res)
                                     else \<tau> \<Turnstile> res \<triangleq> invalid) "
   assumes all_post: "\<forall> \<sigma> \<sigma>' \<sigma>''.  ((\<sigma>,\<sigma>') \<Turnstile> PRE self a1) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self a1)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self) (a1)  \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"POST (self) (a1) (res) \<tau> = POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>) (\<lambda> _. res \<tau>) \<tau>"

sublocale contract1 < contract_scheme "\<lambda>a1 \<tau>. (\<tau> \<Turnstile> \<upsilon> a1)" "\<lambda>a1 \<tau>. (\<lambda> _. a1 \<tau>)"
 apply(unfold_locales)
     apply(rule def_scheme, rule all_post, rule cp\<^sub>P\<^sub>R\<^sub>E, rule cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)
by(simp add: OclValid_def cp_valid[symmetric])

context contract1
begin
   lemma strict1[simp]: "f self invalid = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma defined_mono : "\<tau> \<Turnstile>\<upsilon>(f Y Z) \<Longrightarrow> (\<tau> \<Turnstile>\<delta> Y) \<and> (\<tau> \<Turnstile>\<upsilon> Z)"
   by(auto simp: valid_def bot_fun_def invalid_def 
                 def_scheme StrongEq_def OclValid_def false_def true_def
           split: if_split_asm)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow>  cp (\<lambda>X. PRE (self' X) (a1' X)  )"
   by(rule_tac f=PRE in cpI2, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
     
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (res' X))"
   by(rule_tac f=POST in cpI3, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
      
   lemma cp [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow>  cp res' \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X))"
      by(rule_tac f=f in cpI2, auto intro:cp0)  

   lemmas unfold = unfold'
   lemmas unfold2 = unfold2'
end

locale contract2 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> ('\<AA>,'\<alpha>2::null)val \<Rightarrow>
                  ('\<AA>,'res::null)val"
   fixes PRE 
   fixes POST 
   assumes def_scheme: "f self a1 a2 \<equiv> 
                               (\<lambda> \<tau>. SOME res. let res = \<lambda> _. res in
                                     if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)
                                     then (\<tau> \<Turnstile> PRE self a1 a2) \<and>
                                          (\<tau> \<Turnstile> POST self a1 a2 res)
                                     else \<tau> \<Turnstile> res \<triangleq> invalid) "
   assumes all_post: "\<forall> \<sigma> \<sigma>' \<sigma>''.  ((\<sigma>,\<sigma>') \<Turnstile> PRE self a1 a2) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self a1 a2)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self) (a1) (a2) \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"\<And>res. POST (self) (a1) (a2) (res) \<tau> = 
                         POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>)(\<lambda> _. a2 \<tau>) (\<lambda> _. res \<tau>) \<tau>"


sublocale contract2 < contract_scheme "\<lambda>(a1,a2) \<tau>. (\<tau> \<Turnstile> \<upsilon> a1) \<and> (\<tau> \<Turnstile> \<upsilon> a2)" 
                                      "\<lambda>(a1,a2) \<tau>. (\<lambda> _.a1 \<tau>, \<lambda> _.a2 \<tau>)"
                                      "(\<lambda>x (a,b). f x a b)"
                                      "(\<lambda>x (a,b). PRE x a b)"
                                      "(\<lambda>x (a,b). POST x a b)"
 apply(unfold_locales)
     apply(auto simp add: def_scheme)
        apply (metis all_post, metis all_post)
      apply(subst cp\<^sub>P\<^sub>R\<^sub>E, simp)
     apply(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T, simp)
by(simp_all add: OclValid_def cp_valid[symmetric])

context contract2
begin
   lemma strict0'[simp] : "f invalid X Y = invalid"
   by(insert strict0[of "(X,Y)"], simp)

   lemma nullstrict0'[simp]: "f null X Y = invalid"
   by(insert nullstrict0[of "(X,Y)"], simp)

   lemma strict1[simp]: "f self invalid Y = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma strict2[simp]: "f self X invalid = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)
   
   lemma defined_mono : "\<tau> \<Turnstile>\<upsilon>(f X Y Z) \<Longrightarrow> (\<tau> \<Turnstile>\<delta> X) \<and> (\<tau> \<Turnstile>\<upsilon> Y) \<and> (\<tau> \<Turnstile>\<upsilon> Z)"
   by(auto simp: valid_def bot_fun_def invalid_def 
                 def_scheme StrongEq_def OclValid_def false_def true_def
           split: if_split_asm)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) )"
   by(rule_tac f=PRE in cpI3, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (a2' X) (res' X))"
   by(rule_tac f=POST in cpI4, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
   
   lemma cp0' : "f self a1 a2 \<tau> = f (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) \<tau>"
   by (rule cp0[of _ "(a1,a2)", simplified])
      
   lemma cp [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp res'
                       \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X) (a2' X))"
      by(rule_tac f=f in cpI3, auto intro:cp0')  

   theorem unfold : 
      assumes                "cp E"
      and                    "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)"
      and                    "\<tau> \<Turnstile> PRE self a1 a2"
      and                    " \<exists>res. (\<tau> \<Turnstile> POST self a1 a2 (\<lambda> _. res))"
      and                    "(\<And>res. \<tau> \<Turnstile> POST self a1 a2 (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self a1 a2)"
      apply(rule unfold'[of _ _ _ "(a1, a2)", simplified])
      by((rule assms)+)

   lemma unfold2 :
      assumes                  "cp E"
      and                      "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2)"
      and                      "\<tau> \<Turnstile> PRE self a1 a2"
      and                      "\<tau> \<Turnstile> POST' self a1 a2" (* split constraint holds on post-state *)
      and                      "\<And> res. (POST self a1 a2 res) = 
                                       ((POST' self a1 a2)  and (res \<triangleq> (BODY self a1 a2)))"
      shows "(\<tau> \<Turnstile> E(f self a1 a2)) = (\<tau> \<Turnstile> E(BODY self a1 a2))"
      apply(rule unfold2'[of _ _ _ "(a1, a2)", simplified])
      by((rule assms)+)
end

locale contract3 =
   fixes f   :: "('\<AA>,'\<alpha>0::null)val \<Rightarrow>            
                  ('\<AA>,'\<alpha>1::null)val \<Rightarrow> 
                  ('\<AA>,'\<alpha>2::null)val \<Rightarrow>
                  ('\<AA>,'\<alpha>3::null)val \<Rightarrow>
                  ('\<AA>,'res::null)val"
   fixes PRE 
   fixes POST 
   assumes def_scheme: "f self a1 a2 a3 \<equiv> 
                               (\<lambda> \<tau>. SOME res. let res = \<lambda> _. res in
                                     if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2) \<and>  (\<tau> \<Turnstile> \<upsilon> a3)
                                     then (\<tau> \<Turnstile> PRE self a1 a2 a3) \<and>
                                          (\<tau> \<Turnstile> POST self a1 a2 a3 res)
                                     else \<tau> \<Turnstile> res \<triangleq> invalid) "
   assumes all_post: "\<forall> \<sigma> \<sigma>' \<sigma>''.  ((\<sigma>,\<sigma>') \<Turnstile> PRE self a1 a2 a3) = ((\<sigma>,\<sigma>'') \<Turnstile> PRE self a1 a2 a3)"
           (* PRE is really a pre-condition semantically,
              i.e. it does not depend on the post-state. ... *)
   assumes cp\<^sub>P\<^sub>R\<^sub>E: "PRE (self) (a1) (a2) (a3) \<tau> = PRE (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) (\<lambda> _. a3 \<tau>) \<tau> "
           (* this interface is preferable than :
              assumes "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp a3' \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) (a3' X) )"
              which is too polymorphic. *)
   assumes cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T:"\<And>res. POST (self) (a1) (a2) (a3) (res) \<tau> = 
                         POST (\<lambda> _. self \<tau>)(\<lambda> _. a1 \<tau>)(\<lambda> _. a2 \<tau>)(\<lambda> _. a3 \<tau>) (\<lambda> _. res \<tau>) \<tau>"


sublocale contract3 < contract_scheme "\<lambda>(a1,a2,a3) \<tau>. (\<tau> \<Turnstile> \<upsilon> a1) \<and> (\<tau> \<Turnstile> \<upsilon> a2)\<and> (\<tau> \<Turnstile> \<upsilon> a3)" 
                                      "\<lambda>(a1,a2,a3) \<tau>. (\<lambda> _.a1 \<tau>, \<lambda> _.a2 \<tau>, \<lambda> _.a3 \<tau>)"
                                      "(\<lambda>x (a,b,c). f x a b c)"
                                      "(\<lambda>x (a,b,c). PRE x a b c)"
                                      "(\<lambda>x (a,b,c). POST x a b c)"
 apply(unfold_locales)
     apply(auto simp add: def_scheme)
        apply (metis all_post, metis all_post)
      apply(subst cp\<^sub>P\<^sub>R\<^sub>E, simp)
     apply(subst cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T, simp)
by(simp_all add: OclValid_def cp_valid[symmetric])

context contract3
begin
   lemma strict0'[simp] : "f invalid X Y Z = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma nullstrict0'[simp]: "f null X Y Z = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma strict1[simp]: "f self invalid Y Z = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma strict2[simp]: "f self X invalid Z = invalid"
   by(rule ext, rename_tac "\<tau>", simp add: def_scheme StrongEq_def OclValid_def false_def true_def)

   lemma defined_mono : "\<tau> \<Turnstile>\<upsilon>(f W X Y Z) \<Longrightarrow> (\<tau> \<Turnstile>\<delta> W) \<and> (\<tau> \<Turnstile>\<upsilon> X) \<and> (\<tau> \<Turnstile>\<upsilon> Y) \<and> (\<tau> \<Turnstile>\<upsilon> Z)"
   by(auto simp: valid_def bot_fun_def invalid_def 
                 def_scheme StrongEq_def OclValid_def false_def true_def
           split: if_split_asm)
   
   lemma cp_pre: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2'\<Longrightarrow> cp a3' 
                  \<Longrightarrow> cp (\<lambda>X. PRE (self' X) (a1' X) (a2' X) (a3' X) )"
   by(rule_tac f=PRE in cpI4, auto intro: cp\<^sub>P\<^sub>R\<^sub>E)
  
   lemma cp_post: "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp a3' \<Longrightarrow> cp res'
                   \<Longrightarrow> cp (\<lambda>X. POST (self' X) (a1' X) (a2' X) (a3' X)  (res' X))"
   by(rule_tac f=POST in cpI5, auto intro: cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T)  
   
   lemma cp0' : "f self a1 a2 a3 \<tau> = f (\<lambda> _. self \<tau>) (\<lambda> _. a1 \<tau>) (\<lambda> _. a2 \<tau>) (\<lambda> _. a3 \<tau>) \<tau>"
   by (rule cp0[of _ "(a1,a2,a3)", simplified])
      
   lemma cp [simp]:  "cp self' \<Longrightarrow> cp a1' \<Longrightarrow> cp a2' \<Longrightarrow> cp a3' \<Longrightarrow> cp res'
                       \<Longrightarrow> cp (\<lambda>X. f (self' X) (a1' X) (a2' X) (a3' X))"
      by(rule_tac f=f in cpI4, auto intro:cp0')  

   theorem unfold : 
      assumes                "cp E"
      and                    "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2) \<and>  (\<tau> \<Turnstile> \<upsilon> a3)"
      and                    "\<tau> \<Turnstile> PRE self a1 a2 a3"
      and                    " \<exists>res. (\<tau> \<Turnstile> POST self a1 a2 a3 (\<lambda> _. res))"
      and                    "(\<And>res. \<tau> \<Turnstile> POST self a1 a2 a3 (\<lambda> _. res)  \<Longrightarrow> \<tau> \<Turnstile> E (\<lambda> _. res))"
      shows                  "\<tau> \<Turnstile> E(f self a1 a2 a3)"
      apply(rule unfold'[of _ _ _ "(a1, a2, a3)", simplified])
      by((rule assms)+)

   lemma unfold2 :
      assumes                  "cp E"
      and                      "(\<tau> \<Turnstile> \<delta> self) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and>  (\<tau> \<Turnstile> \<upsilon> a2) \<and>  (\<tau> \<Turnstile> \<upsilon> a3)"
      and                      "\<tau> \<Turnstile> PRE self a1 a2 a3"
      and                      "\<tau> \<Turnstile> POST' self a1 a2 a3" (* split constraint holds on post-state *)
      and                      "\<And> res. (POST self a1 a2 a3 res) = 
                                       ((POST' self a1 a2 a3)  and (res \<triangleq> (BODY self a1 a2 a3)))"
      shows "(\<tau> \<Turnstile> E(f self a1 a2 a3)) = (\<tau> \<Turnstile> E(BODY self a1 a2 a3))"
      apply(rule unfold2'[of _ _ _ "(a1, a2, a3)", simplified])
      by((rule assms)+)
end


end
