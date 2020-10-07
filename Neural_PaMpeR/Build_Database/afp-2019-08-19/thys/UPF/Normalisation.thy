(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
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

section\<open>Policy Transformations\<close>
theory 
  Normalisation
  imports 
    SeqComposition
    ParallelComposition
begin
  
text\<open>
  This theory provides the formalisations required for the transformation of UPF policies. 
  A typical usage scenario can be observed in the firewall case 
  study~\cite{brucker.ea:formal-fw-testing:2014}.
\<close>
  
subsection\<open>Elementary Operators\<close>
text\<open>
  We start by providing several operators and theorems useful when reasoning about a list of 
  rules which should eventually be interpreted as combined using the standard override operator. 
\<close>
  
text\<open>
  The following definition takes as argument a list of rules and returns a policy where the
  rules are combined using the standard override operator.
\<close>
definition list2policy::"('a \<mapsto> 'b) list \<Rightarrow> ('a \<mapsto> 'b)"  where
  "list2policy l = foldr (\<lambda> x y. (x \<Oplus> y)) l \<emptyset>"
  
text\<open>
  Determine the position of element of a list. 
\<close>
fun position :: "'\<alpha> \<Rightarrow> '\<alpha> list \<Rightarrow>  nat" where
  "position a []       = 0"
|"(position a (x#xs)) = (if a = x then 1 else (Suc (position a xs)))" 
  
text\<open>
  Provides the first applied rule of a policy given as a list of rules. 
\<close>
fun  applied_rule where
  "applied_rule C a (x#xs) = (if a \<in> dom (C x) then (Some x)
                                 else (applied_rule C a xs))"
|"applied_rule C a []    = None"
  
text \<open>
  The following is used if the list is constructed backwards. 
\<close>
definition applied_rule_rev where
  "applied_rule_rev C a x =  applied_rule C a (rev x)"
  
text\<open>
  The following is a typical policy transformation. It can be applied to any type of policy and
  removes all the rules from a policy with an empty domain. It takes two arguments: a semantic
  interpretation function and a list of rules. 
\<close>
fun rm_MT_rules  where
  "rm_MT_rules C (x#xs) = (if dom (C x)= {}
                             then rm_MT_rules C xs
                             else x#(rm_MT_rules C xs))"
|"rm_MT_rules C [] = []"
  
text \<open>
  The following invariant establishes that there are no rules with an empty domain in a list 
  of rules. 
\<close>
fun none_MT_rules where 
  "none_MT_rules C (x#xs) = (dom (C x) \<noteq> {} \<and>  (none_MT_rules C xs))"
|"none_MT_rules C [] = True" 
  
text\<open>
  The following related invariant establishes that the policy has not a completely empty domain. 
\<close>
fun not_MT where
  "not_MT C (x#xs) = (if (dom (C x) = {}) then (not_MT C xs) else True)"
|"not_MT C [] = False"
  
text\<open>
Next, a few theorems about the two invariants and the transformation:
\<close>
lemma none_MT_rules_vs_notMT: "none_MT_rules  C p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> not_MT C p" 
  apply (induct p) 
   apply (simp_all)
  done
    
lemma rmnMT: "none_MT_rules C (rm_MT_rules C p)"
  apply (induct p) 
   apply (simp_all)
  done
    
lemma rmnMT2: "none_MT_rules C  p \<Longrightarrow>  (rm_MT_rules C p) = p"
  apply (induct p) 
   apply (simp_all)
  done
    
lemma nMTcharn: "none_MT_rules C p = (\<forall> r \<in> set p. dom (C r) \<noteq> {})"
  apply (induct p) 
   apply (simp_all)
  done
    
lemma nMTeqSet: "set p = set s \<Longrightarrow> none_MT_rules C p = none_MT_rules C s"
  apply (simp add: nMTcharn)
  done
    
lemma notMTnMT: "\<lbrakk>a \<in> set p; none_MT_rules C p\<rbrakk> \<Longrightarrow> dom (C a) \<noteq> {}"
  apply (simp add: nMTcharn)
  done
    
lemma none_MT_rulesconc: "none_MT_rules C (a@[b]) \<Longrightarrow> none_MT_rules C a"
  apply (induct a)
   apply (simp_all)
  done
    
lemma nMTtail: "none_MT_rules C p \<Longrightarrow> none_MT_rules C (tl p)"
  apply (induct p)
   apply (simp_all)
  done
    
lemma not_MTimpnotMT[simp]: "not_MT C p \<Longrightarrow> p \<noteq> []"
  apply (auto)
  done 
    
lemma SR3nMT: "\<not> not_MT C  p \<Longrightarrow> rm_MT_rules C p = []"
  apply (induct p)
   apply (auto simp: if_splits)
  done
    
lemma NMPcharn: "\<lbrakk>a \<in> set p; dom (C a) \<noteq> {}\<rbrakk> \<Longrightarrow> not_MT C  p"
  apply (induct p)
   apply (auto simp: if_splits)
  done
    
lemma NMPrm: "not_MT C  p \<Longrightarrow> not_MT C (rm_MT_rules C p)"
  apply (induct p)
   apply (simp_all)
  done
    
text\<open>Next, a few theorems about applied\_rule:\<close>
lemma mrconc: "applied_rule_rev C x p = Some a \<Longrightarrow> applied_rule_rev C x (b#p) = Some a"
proof (induct p rule: rev_induct)
  case Nil show ?case using Nil
    by (simp add: applied_rule_rev_def)
next
  case (snoc xs x) show ?case using snoc 
    apply (simp add: applied_rule_rev_def if_splits) 
    by (metis option.inject)
qed
  
lemma mreq_end: "\<lbrakk>applied_rule_rev C x b = Some r; applied_rule_rev C x c = Some r\<rbrakk> \<Longrightarrow> 
 applied_rule_rev C x (a#b) = applied_rule_rev C x (a#c)"
  by (simp add: mrconc)
    
lemma mrconcNone: "applied_rule_rev C x p = None \<Longrightarrow>
                                applied_rule_rev C x (b#p) = applied_rule_rev C x [b]"
proof (induct p rule: rev_induct)
  case Nil show ?case 
    by (simp add: applied_rule_rev_def)
next
  case (snoc ys y) show ?case using snoc 
  proof (cases "x \<in> dom (C ys)")
    case True show ?thesis using True snoc
      by (auto simp: applied_rule_rev_def) 
  next
    case False show ?thesis using False snoc
      by (auto simp: applied_rule_rev_def) 
  qed
qed
  
lemma mreq_endNone: "\<lbrakk>applied_rule_rev C x b = None; applied_rule_rev C x c = None\<rbrakk> \<Longrightarrow> 
     applied_rule_rev C x (a#b) = applied_rule_rev C x (a#c)"
  by (metis mrconcNone)
    
lemma mreq_end2: "applied_rule_rev C x b = applied_rule_rev C x c \<Longrightarrow> 
     applied_rule_rev C x (a#b) = applied_rule_rev C x (a#c)"
  apply (case_tac "applied_rule_rev C x b = None")
   apply (auto intro: mreq_end mreq_endNone)
  done
    
lemma mreq_end3: "applied_rule_rev C x p \<noteq> None \<Longrightarrow>
                  applied_rule_rev C x (b # p) = applied_rule_rev C x (p)"
  by (auto simp: mrconc)
    
lemma mrNoneMT: "\<lbrakk>r \<in> set p; applied_rule_rev C x p = None\<rbrakk> \<Longrightarrow>
                              x \<notin> dom (C r)"
proof (induct p rule: rev_induct)
  case Nil show ?case using Nil
    by (simp add: applied_rule_rev_def)
next
  case (snoc y ys) show ?case using snoc
  proof (cases "r \<in> set ys")
    case True show ?thesis using snoc True
      by (simp add: applied_rule_rev_def split: if_split_asm)
  next
    case False show ?thesis using snoc False
      by (simp add: applied_rule_rev_def split: if_split_asm)
  qed
qed
  

subsection\<open>Distributivity of the Transformation.\<close>
text\<open>
  The scenario is the following (can be applied iteratively):
  \begin{itemize}
    \item Two policies are combined using one of the parallel combinators
    \item (e.g. P = P1 P2) (At least) one of the constituent policies has
    \item a normalisation procedures, which as output produces a list of
    \item policies that are semantically equivalent to the original policy if
    \item combined from left to right using the override operator.
  \end{itemize}
\<close>

text\<open>
  The following function is crucial for the distribution. Its arguments are a policy, a list
  of policies, a parallel combinator, and a range and a domain coercion function. 
\<close>
fun prod_list :: "('\<alpha> \<mapsto>'\<beta>) \<Rightarrow> (('\<gamma> \<mapsto>'\<delta>) list) \<Rightarrow> 
                  (('\<alpha> \<mapsto>'\<beta>) \<Rightarrow> ('\<gamma> \<mapsto>'\<delta>) \<Rightarrow> (('\<alpha> \<times> '\<gamma>) \<mapsto> ('\<beta> \<times> '\<delta>))) \<Rightarrow>
                  (('\<beta> \<times> '\<delta>) \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> ('\<alpha> \<times> '\<gamma>)) \<Rightarrow>  
                  (('x \<mapsto> 'y) list)"  (infixr "\<Otimes>\<^sub>L" 54) where
  "prod_list x (y#ys) par_comb ran_adapt dom_adapt = 
  ((ran_adapt o_f ((par_comb x y) o dom_adapt))#(prod_list x ys par_comb ran_adapt dom_adapt))"
| "prod_list x [] par_comb ran_adapt dom_adapt = []"
  
text\<open>
  An instance, as usual there are four of them. 
\<close>
  
definition prod_2_list :: "[('\<alpha> \<mapsto>'\<beta>), (('\<gamma> \<mapsto>'\<delta>) list)] \<Rightarrow> 
                  (('\<beta> \<times> '\<delta>) \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> ('\<alpha> \<times> '\<gamma>)) \<Rightarrow> 
                  (('x \<mapsto> 'y) list)" (infixr "\<Otimes>\<^sub>2\<^sub>L" 55) where 
  "x \<Otimes>\<^sub>2\<^sub>L y =  (\<lambda> d r. (x \<Otimes>\<^sub>L y) (\<Otimes>\<^sub>2) d r)"  
  
lemma list2listNMT:  "x \<noteq> [] \<Longrightarrow> map sem x \<noteq> []"
  apply (case_tac x)
   apply (simp_all)
  done
    
lemma two_conc: "(prod_list x (y#ys) p r d) = ((r o_f ((p x y) o d))#(prod_list x ys p r d))"
  by simp

text\<open>
  The following two invariants establish if the law of distributivity holds for a combinator
  and if an operator is strict regarding undefinedness. 
\<close>
definition is_distr where
 "is_distr p = (\<lambda> g f. (\<forall> N P1 P2. ((g o_f ((p N (P1 \<Oplus> P2)) o f)) = 
               ((g o_f ((p N P1) o f)) \<Oplus> (g o_f ((p N P2)  o f))))))"

definition is_strict where
 "is_strict p = (\<lambda> r d. \<forall> P1. (r o_f (p P1 \<emptyset> \<circ> d)) = \<emptyset>)"

lemma is_distr_orD: "is_distr (\<Otimes>\<^sub>\<or>\<^sub>D) d r"
  apply (simp add: is_distr_def)
  apply (rule allI)+
  apply (rule distr_orD)
  apply (simp)
  done
    
lemma is_strict_orD: "is_strict (\<Otimes>\<^sub>\<or>\<^sub>D) d r"
  apply (simp add: is_strict_def)
  apply (simp add: policy_range_comp_def)
  done
    
lemma is_distr_2: "is_distr (\<Otimes>\<^sub>2) d r"
  apply (simp add: is_distr_def)
  apply (rule allI)+
  apply (rule distr_or2)
  by simp
    
lemma is_strict_2: "is_strict (\<Otimes>\<^sub>2) d r"
  apply (simp only: is_strict_def)
  apply simp
  apply (simp add: policy_range_comp_def)
  done
    
lemma domStart: "t \<in> dom p1 \<Longrightarrow> (p1 \<Oplus> p2) t = p1 t"
  apply (simp add: map_add_dom_app_simps)
  done
    
lemma notDom: "x \<in> dom A \<Longrightarrow> \<not> A x = None"
  apply auto
  done
    
text\<open>
  The following theorems are crucial: they establish the correctness of the distribution.
\<close>
lemma Norm_Distr_1:  "((r o_f (((\<Otimes>\<^sub>1) P1 (list2policy P2)) o d)) x = 
                                                   ((list2policy ((P1 \<Otimes>\<^sub>L P2) (\<Otimes>\<^sub>1) r d)) x))"
proof (induct P2) 
  case Nil show ?case
    by (simp add: policy_range_comp_def  list2policy_def) 
next
  case (Cons p ps) show ?case using Cons
  proof (cases "x \<in> dom (r o_f ((P1 \<Otimes>\<^sub>1 p) \<circ> d))") 
    case True show ?thesis using True
      by (auto simp: list2policy_def policy_range_comp_def  prod_1_def 
          split: option.splits decision.splits prod.splits) 
  next
    case False show ?thesis using Cons False
      by (auto simp: list2policy_def policy_range_comp_def  map_add_dom_app_simps(3) prod_1_def
          split: option.splits decision.splits prod.splits) 
  qed
qed
  
lemma Norm_Distr_2: "((r o_f (((\<Otimes>\<^sub>2) P1 (list2policy P2)) o d)) x = 
                               ((list2policy ((P1 \<Otimes>\<^sub>L P2) (\<Otimes>\<^sub>2) r d)) x))"proof (induct P2) 
  case Nil show ?case
    by (simp add: policy_range_comp_def  list2policy_def) 
next
  case (Cons p ps) show ?case using Cons
  proof (cases "x \<in> dom (r o_f ((P1 \<Otimes>\<^sub>2 p) \<circ> d))") 
    case True show ?thesis using True
      by (auto simp: list2policy_def prod_2_def policy_range_comp_def 
          split: option.splits decision.splits prod.splits) 
  next
    case False show ?thesis using Cons False
      by (auto simp:  policy_range_comp_def  list2policy_def map_add_dom_app_simps(3) prod_2_def
          split: option.splits decision.splits prod.splits) 
  qed
qed
  
lemma Norm_Distr_A: "((r o_f (((\<Otimes>\<^sub>\<or>\<^sub>A) P1 (list2policy P2)) o d)) x = 
                                                 ((list2policy ((P1 \<Otimes>\<^sub>L P2) (\<Otimes>\<^sub>\<or>\<^sub>A) r d)) x))"
proof (induct P2) 
  case Nil show ?case
    by (simp add: policy_range_comp_def  list2policy_def) 
next
  case (Cons p ps) show ?case using Cons
  proof (cases "x \<in> dom (r o_f ((P1 \<Otimes>\<^sub>\<or>\<^sub>A p) \<circ> d))") 
    case True show ?thesis using True
      by (auto simp: policy_range_comp_def  list2policy_def prod_orA_def
          split: option.splits decision.splits prod.splits) 
  next
    case False show ?thesis using Cons False
      by (auto simp: policy_range_comp_def  list2policy_def map_add_dom_app_simps(3) prod_orA_def
          split: option.splits decision.splits prod.splits) 
  qed
qed

  
lemma Norm_Distr_D: "((r o_f (((\<Otimes>\<^sub>\<or>\<^sub>D) P1 (list2policy P2)) o d)) x = 
                                                  ((list2policy ((P1 \<Otimes>\<^sub>L P2) (\<Otimes>\<^sub>\<or>\<^sub>D) r d)) x))"
proof (induct P2) 
  case Nil show ?case
    by (simp add: policy_range_comp_def  list2policy_def) 
next
  case (Cons p ps) show ?case using Cons
  proof (cases "x \<in> dom (r o_f ((P1 \<Otimes>\<^sub>\<or>\<^sub>D p) \<circ> d))") 
    case True show ?thesis using True
      by (auto simp: policy_range_comp_def  list2policy_def prod_orD_def
          split: option.splits decision.splits prod.splits) 
  next
    case False show ?thesis using Cons False
      by (auto simp: policy_range_comp_def  list2policy_def map_add_dom_app_simps(3) prod_orD_def
          split: option.splits decision.splits prod.splits)  
  qed
qed
  
text \<open>Some domain reasoning\<close>
lemma domSubsetDistr1: "dom A = UNIV \<Longrightarrow> dom ((\<lambda>(x, y). x) o_f (A \<Otimes>\<^sub>1 B) o (\<lambda> x. (x,x))) = dom B"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (auto simp: prod_1_def policy_range_comp_def dom_def  
      split: decision.splits option.splits prod.splits)
  done
    
lemma domSubsetDistr2: "dom A = UNIV \<Longrightarrow> dom ((\<lambda>(x, y). x) o_f (A \<Otimes>\<^sub>2 B) o (\<lambda> x. (x,x))) = dom B"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (auto simp: prod_2_def policy_range_comp_def dom_def 
      split: decision.splits option.splits prod.splits)
  done
    
lemma domSubsetDistrA: "dom A = UNIV \<Longrightarrow> dom ((\<lambda>(x, y). x) o_f (A \<Otimes>\<^sub>\<or>\<^sub>A B) o (\<lambda> x. (x,x))) = dom B"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (auto simp: prod_orA_def policy_range_comp_def dom_def 
      split: decision.splits option.splits prod.splits)
  done
    
lemma domSubsetDistrD: "dom A = UNIV \<Longrightarrow> dom ((\<lambda>(x, y). x) o_f (A \<Otimes>\<^sub>\<or>\<^sub>D B) o (\<lambda> x. (x,x))) = dom B"
  apply (rule set_eqI)
  apply (rule iffI)
  apply (auto simp: prod_orD_def policy_range_comp_def dom_def 
      split: decision.splits option.splits prod.splits)
  done
end


