(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * UPF
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2012 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2017 Université Paris-Sud, France
 *               2015-2017 The University of Sheffield, UK
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


section\<open>Properties on Policies\<close>
theory 
  Analysis
  imports
    ParallelComposition
    SeqComposition
begin

text \<open>
  In this theory, several standard policy properties are paraphrased in UPF terms. 
\<close>

subsection\<open>Basic Properties\<close>

subsubsection\<open>A Policy Has no Gaps\<close>

definition gap_free :: "('a \<mapsto> 'b) \<Rightarrow> bool" 
where     "gap_free p = (dom p = UNIV)"

subsubsection\<open>Comparing Policies\<close>
text \<open>Policy p is more defined than q:\<close>
definition more_defined :: "('a \<mapsto> 'b) \<Rightarrow>('a \<mapsto> 'b) \<Rightarrow>bool" 
where     "more_defined p q = (dom q \<subseteq> dom p)"


definition strictly_more_defined :: "('a \<mapsto> 'b) \<Rightarrow>('a \<mapsto> 'b) \<Rightarrow>bool" 
where     "strictly_more_defined p q = (dom q \<subset> dom p)"

lemma strictly_more_vs_more: "strictly_more_defined p q \<Longrightarrow> more_defined p q"
  unfolding more_defined_def strictly_more_defined_def
  by auto

text\<open>Policy p is more permissive than q:\<close>
definition more_permissive :: "('a \<mapsto> 'b) \<Rightarrow> ('a \<mapsto> 'b) \<Rightarrow> bool"  (infixl "\<sqsubseteq>\<^sub>A" 60)
where " p \<sqsubseteq>\<^sub>A q =  (\<forall> x. (case q x of \<lfloor>allow y\<rfloor> \<Rightarrow> (\<exists> z. (p x = \<lfloor>allow z\<rfloor>))
                                   | \<lfloor>deny y\<rfloor>  \<Rightarrow> True
                                   | \<bottom>        \<Rightarrow> True))" 


lemma more_permissive_refl : "p \<sqsubseteq>\<^sub>A p "
  unfolding more_permissive_def
  by(auto split : option.split decision.split)
    
lemma more_permissive_trans : "p \<sqsubseteq>\<^sub>A p' \<Longrightarrow> p' \<sqsubseteq>\<^sub>A p'' \<Longrightarrow>  p \<sqsubseteq>\<^sub>A p''"
  unfolding more_permissive_def
  apply(auto split : option.split decision.split)
  subgoal for x y
    apply(erule_tac x = x and 
        P = "\<lambda>x. case p'' x of \<bottom> \<Rightarrow> True 
                                     | \<lfloor>allow y\<rfloor> \<Rightarrow> \<exists>z. p' x = \<lfloor>allow z\<rfloor> 
                                     | \<lfloor>deny y\<rfloor> \<Rightarrow> True" in allE)
    apply(simp, elim exE)
    by(erule_tac x = x in allE, simp)
  done 

text\<open>Policy p is more rejective than q:\<close>
definition more_rejective :: "('a \<mapsto> 'b) \<Rightarrow> ('a \<mapsto> 'b) \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>D" 60)
  where " p \<sqsubseteq>\<^sub>D q = (\<forall> x. (case q x of \<lfloor>deny y\<rfloor>  \<Rightarrow> (\<exists> z. (p x = \<lfloor>deny z\<rfloor>))
                                  | \<lfloor>allow y\<rfloor> \<Rightarrow> True
                                  | \<bottom>        \<Rightarrow> True))" 
    
    
lemma more_rejective_trans : "p \<sqsubseteq>\<^sub>D p' \<Longrightarrow> p' \<sqsubseteq>\<^sub>D p'' \<Longrightarrow>  p \<sqsubseteq>\<^sub>D p''"
  unfolding more_rejective_def
  apply(auto split : option.split decision.split)
  subgoal for x y
    apply(erule_tac x = x and 
        P = "\<lambda>x. case p'' x of \<bottom> \<Rightarrow> True 
                                     | \<lfloor>allow y\<rfloor> \<Rightarrow> True 
                                     | \<lfloor>deny y\<rfloor> \<Rightarrow> \<exists>z. p' x = \<lfloor>deny z\<rfloor>" in allE)
    apply(simp, elim exE)
    by(erule_tac x = x in allE, simp)
  done


lemma more_rejective_refl : "p \<sqsubseteq>\<^sub>D p "
  unfolding more_rejective_def
  by(auto split : option.split decision.split)
    
    
lemma "A\<^sub>f f \<sqsubseteq>\<^sub>A p"
  unfolding more_permissive_def allow_all_fun_def allow_pfun_def 
  by(auto split: option.split decision.split)
    
lemma "A\<^sub>I \<sqsubseteq>\<^sub>A p"
  unfolding more_permissive_def allow_all_fun_def allow_pfun_def allow_all_id_def
  by(auto split: option.split decision.split)
    
subsection\<open>Combined Data-Policy Refinement\<close>
  
definition policy_refinement :: 
  "('a \<mapsto> 'b) \<Rightarrow> ('a' \<Rightarrow> 'a) \<Rightarrow>('b' \<Rightarrow> 'b) \<Rightarrow> ('a' \<mapsto> 'b') \<Rightarrow> bool" 
  ("_ \<sqsubseteq>\<^bsub>_\<^esub>\<^sub>,\<^bsub>_\<^esub> _" [50,50,50,50]50)
  where     "p \<sqsubseteq>\<^bsub>abs\<^sub>a\<^esub>\<^sub>,\<^bsub>abs\<^sub>b\<^esub> q \<equiv> 
              (\<forall> a. case p a of 
                      \<bottom> \<Rightarrow> True
                    | \<lfloor>allow y\<rfloor> \<Rightarrow> (\<forall> a'\<in>{x. abs\<^sub>a x=a}. 
                                     \<exists> b'.  q a' = \<lfloor>allow b'\<rfloor>
                                            \<and> abs\<^sub>b b' = y)
                    | \<lfloor>deny y\<rfloor> \<Rightarrow> (\<forall> a'\<in>{x. abs\<^sub>a x=a}. 
                                     \<exists> b'.  q a' = \<lfloor>deny b'\<rfloor>
                                            \<and> abs\<^sub>b b' = y))"                                     
    
theorem polref_refl: "p \<sqsubseteq>\<^bsub>id\<^esub>\<^sub>,\<^bsub>id\<^esub> p"
  unfolding policy_refinement_def
  by(auto split: option.split decision.split)
    
theorem polref_trans: 
  assumes A: "p \<sqsubseteq>\<^bsub>f\<^esub>\<^sub>,\<^bsub>g\<^esub> p'"
    and     B: "p' \<sqsubseteq>\<^bsub>f'\<^esub>\<^sub>,\<^bsub>g'\<^esub> p''"
  shows   "p \<sqsubseteq>\<^bsub>f o f'\<^esub>\<^sub>,\<^bsub>g o g'\<^esub> p''"
  apply(insert A B)
  unfolding policy_refinement_def 
  apply(auto split: option.split decision.split simp: o_def)[1]
  subgoal for a a'
    apply(erule_tac x="f (f' a')" in allE, simp)[1]
    apply(erule_tac x="f' a'" in allE, auto)[1]
    apply(erule_tac x=" (f' a')" in allE, auto)[1]
    done 
  subgoal for a a'
    apply(erule_tac x="f (f' a')" in allE, simp)[1]
    apply(erule_tac x="f' a'" in allE, auto)[1]
    apply(erule_tac x=" (f' a')" in allE, auto)[1]
    done
  done 

subsection \<open>Equivalence of Policies\<close>
subsubsection\<open>Equivalence over domain D\<close>
  
definition p_eq_dom :: "('a \<mapsto> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<mapsto> 'b) \<Rightarrow>bool" ("_ \<approx>\<^bsub>_\<^esub> _" [60,60,60]60)
  where     "p \<approx>\<^bsub>D\<^esub> q  = (\<forall>x\<in>D. p x = q x)"
    
text\<open>p and q have no conflicts\<close>
definition no_conflicts :: "('a \<mapsto> 'b) \<Rightarrow>('a \<mapsto> 'b)  \<Rightarrow>bool" where
  "no_conflicts p q = (dom p = dom q \<and> (\<forall>x\<in>(dom p). 
    (case p x of \<lfloor>allow y\<rfloor> \<Rightarrow> (\<exists>z. q x = \<lfloor>allow z\<rfloor>)
               | \<lfloor>deny y\<rfloor> \<Rightarrow> (\<exists>z. q x = \<lfloor>deny z\<rfloor>))))"
  
lemma policy_eq:
  assumes p_over_qA: "p \<sqsubseteq>\<^sub>A q "
    and  q_over_pA:    "q \<sqsubseteq>\<^sub>A p" 
    and  p_over_qD:    "q \<sqsubseteq>\<^sub>D p" 
    and  q_over_pD:    "p \<sqsubseteq>\<^sub>D q" 
    and  dom_eq:       "dom p = dom q"
  shows                "no_conflicts p q"
  apply (insert p_over_qA q_over_pA p_over_qD q_over_pD dom_eq)
  apply (simp add:  no_conflicts_def more_permissive_def more_rejective_def
      split: option.splits decision.splits)
  apply (safe)
    apply (metis domI domIff dom_eq)
   apply (metis)+
  done
    
subsubsection\<open>Miscellaneous\<close>
  
lemma dom_inter: "\<lbrakk>dom p \<inter> dom q = {}; p x = \<lfloor>y\<rfloor>\<rbrakk> \<Longrightarrow> q x = \<bottom>"
  by (auto)
    
lemma dom_eq: "dom p \<inter> dom q = {} \<Longrightarrow> p \<Oplus>\<^sub>A q = p \<Oplus>\<^sub>D q"
  unfolding override_A_def override_D_def
  by (rule ext, auto simp: dom_def split: prod.splits option.splits decision.splits )
    
lemma dom_split_alt_def : "(f, g) \<Delta> p = (dom(p \<triangleright> Allow) \<triangleleft> (A\<^sub>f f)) \<Oplus> (dom(p \<triangleright> Deny) \<triangleleft> (D\<^sub>f g))"
  apply (rule ext)
  apply (simp add: dom_split2_def Allow_def Deny_def dom_restrict_def
      deny_all_fun_def allow_all_fun_def map_add_def)
  apply (simp split: option.splits decision.splits)
  apply (auto simp: map_add_def o_def deny_pfun_def ran_restrict_def image_def)
  done

end
