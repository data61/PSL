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

section\<open>Sequential Composition\<close>
theory  
  SeqComposition
  imports 
    ElementaryPolicies
begin

text\<open>
  Sequential composition is based on the idea that two policies are to be combined by applying 
  the second policy to the output of the first one. Again, there are four possibilities how the 
  decisions can be combined.\<close> 

subsection \<open>Flattening\<close>
text\<open>
  A key concept of sequential policy composition is the flattening of nested decisions. There are 
  four possibilities, and these possibilities will give the various flavours of policy composition.
\<close>
fun    flat_orA :: "('\<alpha> decision) decision \<Rightarrow> ('\<alpha> decision)"
where "flat_orA(allow(allow y)) = allow y"
     |"flat_orA(allow(deny y))  = allow y"
     |"flat_orA(deny(allow y))  = allow y"
     |"flat_orA(deny(deny y))   = deny y"
       
lemma flat_orA_deny[dest]:"flat_orA x = deny y \<Longrightarrow> x = deny(deny y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

lemma flat_orA_allow[dest]: "flat_orA x = allow y \<Longrightarrow> x = allow(allow y) 
                                                    \<or> x = allow(deny y) 
                                                    \<or> x = deny(allow y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

fun    flat_orD :: "('\<alpha> decision) decision \<Rightarrow> ('\<alpha> decision)"
where "flat_orD(allow(allow y)) = allow y"
     |"flat_orD(allow(deny y))  = deny y"
     |"flat_orD(deny(allow y))  = deny y"
     |"flat_orD(deny(deny y))   = deny y"
       
lemma flat_orD_allow[dest]: "flat_orD x = allow y \<Longrightarrow> x = allow(allow y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

lemma flat_orD_deny[dest]: "flat_orD x = deny y \<Longrightarrow>  x = deny(deny y) 
                                                   \<or> x = allow(deny y) 
                                                   \<or> x = deny(allow y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

fun    flat_1 :: "('\<alpha> decision) decision \<Rightarrow> ('\<alpha> decision)"
where "flat_1(allow(allow y)) = allow y"
     |"flat_1(allow(deny y))  = allow y"
     |"flat_1(deny(allow y))  = deny y"
     |"flat_1(deny(deny y))   = deny y"

lemma flat_1_allow[dest]: "flat_1 x = allow y \<Longrightarrow> x = allow(allow y) \<or> x = allow(deny y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

lemma flat_1_deny[dest]: "flat_1 x = deny y \<Longrightarrow>  x = deny(deny y) \<or> x = deny(allow y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

fun    flat_2 :: "('\<alpha> decision) decision \<Rightarrow> ('\<alpha> decision)"
where "flat_2(allow(allow y)) = allow y"
     |"flat_2(allow(deny y))  = deny y"
     |"flat_2(deny(allow y))  = allow y"
     |"flat_2(deny(deny y))   = deny y"

lemma flat_2_allow[dest]: "flat_2 x = allow y \<Longrightarrow> x = allow(allow y) \<or> x = deny(allow y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
done

lemma flat_2_deny[dest]: "flat_2 x = deny y \<Longrightarrow>  x = deny(deny y) \<or> x = allow(deny y)"
  apply (case_tac "x")
   apply (rename_tac \<alpha>)
   apply (case_tac "\<alpha>", simp_all)[1]
  apply (rename_tac \<alpha>)
  apply (case_tac "\<alpha>", simp_all)[1]
  done

subsection\<open>Policy Composition\<close>
text\<open>
  The following definition allows to compose two policies. Denies and allows are transferred. 
\<close>

fun lift :: "('\<alpha> \<mapsto> '\<beta>) \<Rightarrow> ('\<alpha> decision \<mapsto>'\<beta> decision)"  
where "lift f (deny s)  = (case f s of 
                             \<lfloor>y\<rfloor> \<Rightarrow> \<lfloor>deny y\<rfloor>
                           | \<bottom> \<Rightarrow> \<bottom>)"
    | "lift f (allow s) = (case f s of 
                              \<lfloor>y\<rfloor> \<Rightarrow> \<lfloor>allow y\<rfloor>
                           | \<bottom> \<Rightarrow> \<bottom>)"

lemma lift_mt [simp]: "lift \<emptyset> = \<emptyset>"
  apply (rule ext)
  subgoal for x 
    apply (case_tac "x")
     apply (simp_all)  
    done
  done

text\<open>
  Since policies are maps, we inherit a composition on them. However, this results in nestings 
  of decisions---which must be flattened. As we now that there are four different forms of 
  flattening, we have four different forms of policy composition:\<close>
definition
  comp_orA :: "['\<beta>\<mapsto>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<gamma>"  (infixl "o'_orA" 55) where
  "p2 o_orA p1 \<equiv> (map_option flat_orA) o (lift p2 \<circ>\<^sub>m p1)"

notation
  comp_orA  (infixl "\<circ>\<^sub>\<or>\<^sub>A" 55)

lemma comp_orA_mt[simp]:"p \<circ>\<^sub>\<or>\<^sub>A \<emptyset> = \<emptyset>"
  by(simp add: comp_orA_def)

lemma mt_comp_orA[simp]:"\<emptyset> \<circ>\<^sub>\<or>\<^sub>A p = \<emptyset>"
  by(simp add: comp_orA_def)

definition
  comp_orD :: "['\<beta>\<mapsto>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<gamma>"  (infixl "o'_orD" 55) where
  "p2 o_orD p1 \<equiv> (map_option flat_orD) o (lift p2 \<circ>\<^sub>m p1)"

notation
  comp_orD  (infixl "\<circ>\<^sub>orD" 55)

lemma comp_orD_mt[simp]:"p o_orD \<emptyset> = \<emptyset>"
  by(simp add: comp_orD_def)

lemma mt_comp_orD[simp]:"\<emptyset> o_orD p = \<emptyset>"
  by(simp add: comp_orD_def)

definition
  comp_1 :: "['\<beta>\<mapsto>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<gamma>"  (infixl "o'_1" 55) where
  "p2 o_1 p1 \<equiv> (map_option flat_1) o (lift p2 \<circ>\<^sub>m p1)"

notation
  comp_1  (infixl "\<circ>\<^sub>1" 55)

lemma comp_1_mt[simp]:"p \<circ>\<^sub>1 \<emptyset> = \<emptyset>"
  by(simp add: comp_1_def)

lemma mt_comp_1[simp]:"\<emptyset> \<circ>\<^sub>1 p = \<emptyset>"
  by(simp add: comp_1_def)

definition
  comp_2 :: "['\<beta>\<mapsto>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<gamma>"  (infixl "o'_2" 55) where
  "p2 o_2 p1 \<equiv> (map_option flat_2) o (lift p2 \<circ>\<^sub>m p1)"

notation
  comp_2  (infixl "\<circ>\<^sub>2" 55)

lemma comp_2_mt[simp]:"p \<circ>\<^sub>2 \<emptyset> = \<emptyset>"
  by(simp add: comp_2_def)

lemma mt_comp_2[simp]:"\<emptyset> \<circ>\<^sub>2 p = \<emptyset>"
  by(simp add: comp_2_def)

end
