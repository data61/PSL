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

section \<open>Policy Transformation for Testing\<close>
theory 
  NormalisationTestSpecification
  imports 
    Normalisation
begin

text\<open>
  This theory provides functions and theorems which are useful if one wants to test policy 
  which are transformed. Most exist in two versions: one where the domains of the rules
  of the list (which is the result of a transformation) are pairwise disjoint, and one where 
  this applies not for the last rule in a list (which is usually a default rules).

  The examples in the firewall case study provide a good documentation how these theories can
  be applied. 
\<close>

text\<open>
  This invariant establishes that the domains of a list of rules are pairwise disjoint. 
\<close>
fun disjDom where
 "disjDom (x#xs) = ((\<forall>y\<in>(set xs). dom x \<inter> dom y = {}) \<and> disjDom xs)"
|"disjDom [] = True" 

fun PUTList :: "('a \<mapsto> 'b) \<Rightarrow> 'a \<Rightarrow> ('a \<mapsto> 'b) list \<Rightarrow> bool"
 where
 "PUTList PUT x (p#ps) = ((x \<in> dom p \<longrightarrow> (PUT x = p x)) \<and> (PUTList PUT x ps))"
|"PUTList PUT x [] = True" 

lemma distrPUTL1: "x \<in> dom P \<Longrightarrow> (list2policy PL) x = P x  
                             \<Longrightarrow>  (PUTList PUT x PL \<Longrightarrow> (PUT x = P x))"
  apply (induct PL) 
   apply (auto simp: list2policy_def dom_def)
  done

lemma PUTList_None: "x \<notin> dom (list2policy list) \<Longrightarrow> PUTList PUT x list"
  apply (induct list)
   apply (auto simp: list2policy_def dom_def)
  done

lemma PUTList_DomMT:
  "(\<forall>y\<in>set list. dom a \<inter> dom y = {}) \<Longrightarrow> x \<in> (dom a) \<Longrightarrow> x \<notin> dom (list2policy list)"
  apply (induct list)
   apply (auto simp: dom_def list2policy_def)
  done

lemma distrPUTL2: 
  "x \<in> dom P \<Longrightarrow> (list2policy PL) x = P x  \<Longrightarrow> disjDom PL \<Longrightarrow> (PUT x = P x) \<Longrightarrow> PUTList PUT x PL "
  apply (induct PL) 
   apply (simp_all add: list2policy_def)
  apply (auto)[1]
  subgoal for a PL p
    apply (case_tac "x \<in> dom a")
     apply (case_tac "list2policy PL x = P x")
      apply (simp add: list2policy_def)
     apply (rule PUTList_None) 
     apply (rule_tac a = a in PUTList_DomMT)
      apply (simp_all add: list2policy_def dom_def)
    done
  done

lemma distrPUTL: 
  "\<lbrakk>x \<in> dom P; (list2policy PL) x = P x; disjDom PL\<rbrakk> \<Longrightarrow> (PUT x = P x) = PUTList PUT x PL "
  apply (rule iffI)
   apply (rule distrPUTL2)
      apply (simp_all)
  apply (rule_tac PL = PL in distrPUTL1)
    apply (auto)
  done

text\<open>
  It makes sense to cater for the common special case where the normalisation returns a list 
  where the last element is a default-catch-all rule. It seems easier to cater for this globally,
  rather than to require the normalisation procedures to do this.  
\<close>

fun gatherDomain_aux where
  "gatherDomain_aux (x#xs) = (dom x \<union> (gatherDomain_aux xs))"
|"gatherDomain_aux [] = {}"

definition gatherDomain where "gatherDomain p = (gatherDomain_aux (butlast p))"

definition PUTListGD where "PUTListGD PUT x p = 
  (((x \<notin> (gatherDomain p) \<and> x \<in> dom (last p)) \<longrightarrow> PUT x = (last p) x) \<and> 
                          (PUTList PUT x (butlast p)))"


definition disjDomGD where "disjDomGD p = disjDom (butlast p)"

lemma distrPUTLG1: "\<lbrakk>x \<in> dom P; (list2policy PL) x = P x; PUTListGD PUT x PL\<rbrakk> \<Longrightarrow> PUT x = P x"
  apply (induct PL)  
   apply (simp_all add: domIff PUTListGD_def disjDomGD_def gatherDomain_def list2policy_def)
  apply (auto simp: dom_def domIff split: if_split_asm) 
  done

lemma distrPUTLG2: 
  "PL \<noteq> [] \<Longrightarrow> x \<in> dom P \<Longrightarrow> (list2policy (PL)) x = P x \<Longrightarrow> disjDomGD PL \<Longrightarrow> 
   (PUT x = P x) \<Longrightarrow> PUTListGD PUT x (PL)"
  apply (simp add: PUTListGD_def disjDomGD_def gatherDomain_def list2policy_def)
  apply (induct PL)
   apply (auto)
  apply (metis PUTList_DomMT PUTList_None domI)
done

lemma distrPUTLG: 
  "\<lbrakk>x \<in> dom P; (list2policy PL) x = P x; disjDomGD PL; PL \<noteq> []\<rbrakk> \<Longrightarrow>  
  (PUT x = P x) = PUTListGD PUT x PL "
  apply (rule iffI)
   apply (rule distrPUTLG2) 
       apply (simp_all)
  apply (rule_tac PL = PL in distrPUTLG1)
    apply (auto)
  done
    
end


