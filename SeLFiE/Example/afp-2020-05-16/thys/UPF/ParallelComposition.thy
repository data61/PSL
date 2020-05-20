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

section\<open>Parallel Composition\<close>
theory  
  ParallelComposition
  imports 
    ElementaryPolicies
begin

text\<open>
  The following combinators are based on the idea that two policies are executed in parallel. 
  Since both input and the output can differ, we chose to pair them. 
  
  The new input pair will often contain repetitions, which can be reduced using the 
  domain-restriction and domain-reduction operators. Using additional range-modifying operators 
  such as $\nabla$, decide which result argument is chosen; this might be the first or the latter 
  or, in case that $\beta = \gamma$, and $\beta$ underlies a lattice structure, the supremum or 
  infimum of both, or, an arbitrary combination of them.
  
  In any case, although we have strictly speaking a pairing of decisions and not a nesting of 
  them, we will apply the same notational conventions as for the latter, i.e. as for 
  flattening.
\<close>

subsection\<open>Parallel Combinators: Foundations\<close>
text \<open>
  There are four possible semantics how the decision can be combined, thus there are four 
  parallel composition operators. For each of them, we prove several properties. 
\<close>

definition prod_orA ::"['\<alpha>\<mapsto>'\<beta>, '\<gamma> \<mapsto>'\<delta>] \<Rightarrow> ('\<alpha>\<times>'\<gamma> \<mapsto> '\<beta>\<times>'\<delta>)"  (infixr "\<Otimes>\<^sub>\<or>\<^sub>A" 55)
  where "p1 \<Otimes>\<^sub>\<or>\<^sub>A p2 =
       (\<lambda>(x,y). (case p1 x of
             \<lfloor>allow d1\<rfloor> \<Rightarrow>(case p2 y of 
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<bottom> \<Rightarrow> \<bottom>) 
           | \<lfloor>deny d1\<rfloor>\<Rightarrow>(case p2 y of
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor> 
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>deny (d1,d2)\<rfloor> 
                                 | \<bottom> \<Rightarrow> \<bottom>)
           | \<bottom> \<Rightarrow> \<bottom>))"
    
lemma prod_orA_mt[simp]:"p \<Otimes>\<^sub>\<or>\<^sub>A \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_orA_def)
  apply (auto)
  apply (simp split: option.splits decision.splits)
  done

lemma mt_prod_orA[simp]:"\<emptyset> \<Otimes>\<^sub>\<or>\<^sub>A p = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_orA_def)
  done
    
lemma prod_orA_quasi_commute: "p2 \<Otimes>\<^sub>\<or>\<^sub>A p1 = (((\<lambda>(x,y). (y,x)) o_f (p1 \<Otimes>\<^sub>\<or>\<^sub>A p2))) o (\<lambda>(a,b).(b,a))"
  apply (rule ext)
  apply (simp add: prod_orA_def policy_range_comp_def o_def)
  apply (auto)[1]
  apply (simp split: option.splits decision.splits)
  done

definition prod_orD ::"['\<alpha> \<mapsto> '\<beta>, '\<gamma> \<mapsto>   '\<delta>] \<Rightarrow>  ('\<alpha> \<times> '\<gamma> \<mapsto>  '\<beta> \<times> '\<delta> )" (infixr "\<Otimes>\<^sub>\<or>\<^sub>D" 55)
where "p1 \<Otimes>\<^sub>\<or>\<^sub>D p2 =
       (\<lambda>(x,y). (case p1 x of
             \<lfloor>allow d1\<rfloor> \<Rightarrow>(case p2 y of 
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>deny(d1,d2)\<rfloor>
                                 | \<bottom> \<Rightarrow> \<bottom>) 
           | \<lfloor>deny d1\<rfloor>\<Rightarrow>(case p2 y of
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>deny(d1,d2)\<rfloor> 
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>deny (d1,d2)\<rfloor> 
                                 | \<bottom> \<Rightarrow> \<bottom>)
           | \<bottom> \<Rightarrow> \<bottom>))"

lemma prod_orD_mt[simp]:"p \<Otimes>\<^sub>\<or>\<^sub>D \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_orD_def)
  apply (auto)[1]
  apply (simp split: option.splits decision.splits)
  done
    
lemma mt_prod_orD[simp]:"\<emptyset> \<Otimes>\<^sub>\<or>\<^sub>D p = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_orD_def)
  done
    
lemma prod_orD_quasi_commute: "p2 \<Otimes>\<^sub>\<or>\<^sub>D p1 = (((\<lambda>(x,y). (y,x)) o_f (p1 \<Otimes>\<^sub>\<or>\<^sub>D p2))) o (\<lambda>(a,b).(b,a))"
  apply (rule ext)
  apply (simp add: prod_orD_def policy_range_comp_def o_def)
  apply (auto)[1]
  apply (simp split: option.splits decision.splits)
  done

text\<open>
  The following two combinators are by definition non-commutative, but still strict. 
\<close>
  
definition prod_1 :: "['\<alpha>\<mapsto>'\<beta>, '\<gamma> \<mapsto>'\<delta>] \<Rightarrow> ('\<alpha>\<times>'\<gamma> \<mapsto> '\<beta>\<times>'\<delta>)" (infixr "\<Otimes>\<^sub>1" 55)
  where "p1 \<Otimes>\<^sub>1 p2 \<equiv>
       (\<lambda>(x,y). (case p1 x of
             \<lfloor>allow d1\<rfloor>\<Rightarrow>(case p2 y of 
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<bottom> \<Rightarrow> \<bottom>) 
           | \<lfloor>deny d1\<rfloor> \<Rightarrow>(case p2 y of
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>deny(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>deny(d1,d2)\<rfloor>
                                 | \<bottom> \<Rightarrow> \<bottom>)
           |\<bottom> \<Rightarrow> \<bottom>))"
    
lemma prod_1_mt[simp]:"p \<Otimes>\<^sub>1 \<emptyset> = \<emptyset>"
  apply (rule ext) 
  apply (simp add: prod_1_def)
  apply (auto)[1]
  apply (simp split: option.splits decision.splits)
  done
    
lemma mt_prod_1[simp]:"\<emptyset> \<Otimes>\<^sub>1 p = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_1_def)
  done
    
definition prod_2 :: "['\<alpha>\<mapsto>'\<beta>, '\<gamma> \<mapsto>'\<delta>] \<Rightarrow> ('\<alpha>\<times>'\<gamma> \<mapsto> '\<beta>\<times>'\<delta>)" (infixr "\<Otimes>\<^sub>2" 55)
  where "p1 \<Otimes>\<^sub>2 p2 \<equiv>
       (\<lambda>(x,y). (case p1 x of
             \<lfloor>allow d1\<rfloor> \<Rightarrow>(case p2 y of 
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor>  \<Rightarrow> \<lfloor>deny (d1,d2)\<rfloor>
                                 | \<bottom> \<Rightarrow> \<bottom>) 
           | \<lfloor>deny d1\<rfloor>\<Rightarrow>(case p2 y of
                                   \<lfloor>allow d2\<rfloor> \<Rightarrow> \<lfloor>allow(d1,d2)\<rfloor>
                                 | \<lfloor>deny d2\<rfloor> \<Rightarrow>  \<lfloor>deny (d1,d2)\<rfloor> 
                                 | \<bottom> \<Rightarrow> \<bottom>)
           |\<bottom> \<Rightarrow>\<bottom>))"
    
lemma prod_2_mt[simp]:"p \<Otimes>\<^sub>2 \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_2_def)
  apply (auto)[1]
  apply (simp split: option.splits decision.splits)
  done
    
lemma mt_prod_2[simp]:"\<emptyset> \<Otimes>\<^sub>2 p = \<emptyset>"
  apply (rule ext) 
  apply (simp add: prod_2_def)
  done
    
definition prod_1_id ::"['\<alpha>\<mapsto>'\<beta>, '\<alpha>\<mapsto>'\<gamma>] \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>\<times>'\<gamma>)" (infixr "\<Otimes>\<^sub>1\<^sub>I" 55)
  where "p \<Otimes>\<^sub>1\<^sub>I q = (p \<Otimes>\<^sub>1 q) o (\<lambda>x. (x,x))"
    
lemma prod_1_id_mt[simp]:"p \<Otimes>\<^sub>1\<^sub>I \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_1_id_def)
  done
    
lemma mt_prod_1_id[simp]:"\<emptyset> \<Otimes>\<^sub>1\<^sub>I p = \<emptyset>"
  apply (rule ext) 
  apply (simp add: prod_1_id_def prod_1_def)
  done
    
definition prod_2_id ::"['\<alpha>\<mapsto>'\<beta>, '\<alpha>\<mapsto>'\<gamma>] \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>\<times>'\<gamma>)" (infixr "\<Otimes>\<^sub>2\<^sub>I" 55)
  where"p \<Otimes>\<^sub>2\<^sub>I q = (p \<Otimes>\<^sub>2 q) o (\<lambda>x. (x,x))"
    
lemma prod_2_id_mt[simp]:"p \<Otimes>\<^sub>2\<^sub>I \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_2_id_def)
  done
    
lemma mt_prod_2_id[simp]:"\<emptyset> \<Otimes>\<^sub>2\<^sub>I p = \<emptyset>"
  apply (rule ext)
  apply (simp add: prod_2_id_def prod_2_def)
  done
    
subsection\<open>Combinators for Transition Policies\<close>
text \<open>
  For constructing transition policies, two additional combinators are required: one combines 
  state transitions by pairing the states, the other works equivalently on general maps. 
\<close>
  
definition parallel_map :: "('\<alpha> \<rightharpoonup> '\<beta>) \<Rightarrow> ('\<delta> \<rightharpoonup> '\<gamma>) \<Rightarrow> 
                            ('\<alpha> \<times> '\<delta>  \<rightharpoonup> '\<beta> \<times> '\<gamma>)" (infixr "\<Otimes>\<^sub>M" 60) 
  where  "p1 \<Otimes>\<^sub>M p2 = (\<lambda> (x,y). case p1 x of \<lfloor>d1\<rfloor> \<Rightarrow>
                              (case p2 y of \<lfloor>d2\<rfloor> \<Rightarrow> \<lfloor>(d1,d2)\<rfloor>
                                                | \<bottom> \<Rightarrow> \<bottom>)
                                      | \<bottom> \<Rightarrow> \<bottom>)"

definition parallel_st :: "('i \<times> '\<sigma> \<rightharpoonup> '\<sigma>) \<Rightarrow> ('i \<times> '\<sigma>' \<rightharpoonup> '\<sigma>') \<Rightarrow> 
                            ('i \<times> '\<sigma> \<times> '\<sigma>' \<rightharpoonup> '\<sigma> \<times> '\<sigma>')" (infixr "\<Otimes>\<^sub>S" 60) 
where
   "p1 \<Otimes>\<^sub>S p2 = (p1 \<Otimes>\<^sub>M p2) o (\<lambda> (a,b,c). ((a,b),a,c))"


subsection\<open>Range Splitting\<close>
text\<open>
  The following combinator is a special case of both a parallel composition operator and a 
  range splitting operator. Its primary use case is when combining a policy with state transitions. 
\<close>

definition comp_ran_split :: "[('\<alpha> \<rightharpoonup> '\<gamma>) \<times> ('\<alpha> \<rightharpoonup>'\<gamma>), 'd \<mapsto> '\<beta>] \<Rightarrow> ('d \<times> '\<alpha>) \<mapsto> ('\<beta> \<times> '\<gamma>)"
                          (infixr "\<Otimes>\<^sub>\<nabla>" 100)
where "P \<Otimes>\<^sub>\<nabla> p \<equiv> \<lambda>x. case p (fst x) of 
                          \<lfloor>allow y\<rfloor> \<Rightarrow> (case ((fst P) (snd x)) of \<bottom> \<Rightarrow> \<bottom> | \<lfloor>z\<rfloor> \<Rightarrow> \<lfloor>allow (y,z)\<rfloor>)
                        | \<lfloor>deny y\<rfloor> \<Rightarrow>  (case ((snd P) (snd x)) of \<bottom> \<Rightarrow> \<bottom> | \<lfloor>z\<rfloor> \<Rightarrow> \<lfloor>deny (y,z)\<rfloor>)
                        | \<bottom> \<Rightarrow> \<bottom>"

text\<open>An alternative characterisation of the operator is as follows:\<close>
lemma comp_ran_split_charn:
  "(f, g)  \<Otimes>\<^sub>\<nabla> p = (
(((p  \<triangleright> Allow)\<Otimes>\<^sub>\<or>\<^sub>A (A\<^sub>p f)) \<Oplus> 
 ((p  \<triangleright> Deny) \<Otimes>\<^sub>\<or>\<^sub>A (D\<^sub>p g))))"
  apply (rule ext)
  apply (simp add: comp_ran_split_def map_add_def o_def ran_restrict_def image_def
      Allow_def Deny_def dom_restrict_def prod_orA_def 
      allow_pfun_def deny_pfun_def 
      split:option.splits decision.splits) 
  apply (auto)
  done

subsection \<open>Distributivity of the parallel combinators\<close>
  
lemma distr_or1_a: "(F = F1 \<Oplus> F2) \<Longrightarrow>  (((N  \<Otimes>\<^sub>1 F) o f) = 
               (((N \<Otimes>\<^sub>1 F1) o f)  \<Oplus> ((N   \<Otimes>\<^sub>1 F2)  o f))) "
  apply (rule ext)
  apply (simp add:  prod_1_def map_add_def 
      split: decision.splits option.splits)
  subgoal for x 
    apply (case_tac "f x")
    apply (simp_all add: prod_1_def map_add_def 
        split: decision.splits option.splits)
    done
  done

lemma distr_or1: "(F = F1 \<Oplus> F2) \<Longrightarrow>  ((g o_f ((N  \<Otimes>\<^sub>1 F) o f)) = 
               ((g o_f ((N \<Otimes>\<^sub>1 F1) o f)) \<Oplus>  (g o_f ((N \<Otimes>\<^sub>1 F2)  o f)))) "
  apply (rule ext)+
  apply (simp add: prod_1_def map_add_def policy_range_comp_def 
      split: decision.splits option.splits)
  subgoal for x
    apply (case_tac "f x")
    apply (simp_all add: prod_1_def map_add_def 
        split: decision.splits option.splits)
    done
  done 
    
lemma distr_or2_a: "(F = F1 \<Oplus> F2) \<Longrightarrow>  (((N  \<Otimes>\<^sub>2 F) o f) = 
               (((N \<Otimes>\<^sub>2 F1) o f)  \<Oplus> ((N  \<Otimes>\<^sub>2 F2)  o f))) "
  apply (rule ext)
  apply (simp add: prod_2_id_def prod_2_def map_add_def 
      split: decision.splits option.splits)
  subgoal for x
    apply (case_tac "f x")
    apply (simp_all add: prod_2_def map_add_def 
        split: decision.splits option.splits)
    done
  done
    
lemma distr_or2: "(F = F1 \<Oplus> F2) \<Longrightarrow>  ((r o_f ((N  \<Otimes>\<^sub>2 F) o f)) = 
               ((r o_f ((N \<Otimes>\<^sub>2 F1) o f))  \<Oplus> (r o_f ((N  \<Otimes>\<^sub>2 F2)  o f)))) "
  apply (rule ext)
  apply (simp add: prod_2_id_def prod_2_def map_add_def policy_range_comp_def
      split: decision.splits option.splits)
  subgoal for x 
    apply (case_tac "f x")
    apply (simp_all add: prod_2_def map_add_def 
        split: decision.splits option.splits)
    done
  done 
    
lemma distr_orA: "(F = F1 \<Oplus> F2) \<Longrightarrow>  ((g o_f ((N  \<Otimes>\<^sub>\<or>\<^sub>A F) o f)) = 
               ((g o_f ((N  \<Otimes>\<^sub>\<or>\<^sub>A F1) o f))  \<Oplus>  (g o_f ((N  \<Otimes>\<^sub>\<or>\<^sub>A F2)  o f)))) "
  apply (rule ext)+
  apply (simp add: prod_orA_def map_add_def policy_range_comp_def 
      split: decision.splits option.splits)
  subgoal for x 
    apply (case_tac "f x")
    apply (simp_all add:  map_add_def 
        split: decision.splits option.splits)
    done
  done 
    
lemma distr_orD: "(F = F1 \<Oplus> F2) \<Longrightarrow>  ((g o_f ((N  \<Otimes>\<^sub>\<or>\<^sub>D F) o f)) = 
               ((g o_f ((N \<Otimes>\<^sub>\<or>\<^sub>D F1) o f))  \<Oplus>  (g o_f ((N \<Otimes>\<^sub>\<or>\<^sub>D F2)  o f)))) "
  apply (rule ext)+
  apply (simp add: prod_orD_def map_add_def policy_range_comp_def 
      split: decision.splits option.splits)
  subgoal for x 
    apply (case_tac "f x")
    apply (simp_all add:  map_add_def 
        split: decision.splits option.splits)
    done
  done 
    
lemma coerc_assoc: "(r o_f P) o d = r o_f (P o d)"
  apply (simp add: policy_range_comp_def)
  apply (rule ext)
  apply (simp split: option.splits decision.splits)
  done

lemmas ParallelDefs = prod_orA_def prod_orD_def prod_1_def prod_2_def parallel_map_def 
                      parallel_st_def comp_ran_split_def
end
