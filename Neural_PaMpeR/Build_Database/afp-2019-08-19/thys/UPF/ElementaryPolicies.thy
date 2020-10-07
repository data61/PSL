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

section\<open>Elementary Policies\<close>
theory 
  ElementaryPolicies
  imports 
    UPFCore
begin
text\<open>
  In this theory, we introduce the elementary policies of UPF that build the basis 
  for more complex policies. These complex policies, respectively, embedding of 
  well-known access control or security models, are build by composing the elementary 
  policies defined in this theory. 
\<close>

subsection\<open>The Core Policy Combinators: Allow and Deny Everything\<close>

definition
   deny_pfun    :: "('\<alpha> \<rightharpoonup>'\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ("AllD")
   where 
  "deny_pfun pf \<equiv> (\<lambda> x. case pf x of
                          \<lfloor>y\<rfloor> \<Rightarrow> \<lfloor>deny (y)\<rfloor>
                         |\<bottom> \<Rightarrow> \<bottom>)"

definition
   allow_pfun    :: "('\<alpha> \<rightharpoonup>'\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ( "AllA")
   where 
  "allow_pfun pf \<equiv> (\<lambda> x. case pf x of
                          \<lfloor>y\<rfloor> \<Rightarrow> \<lfloor>allow (y)\<rfloor>
                         |\<bottom> \<Rightarrow> \<bottom>)"

syntax
  "_allow_pfun"  :: "('\<alpha> \<rightharpoonup>'\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ("A\<^sub>p")
translations
  "A\<^sub>p f" \<rightleftharpoons> "AllA f"

syntax
  "_deny_pfun"  :: "('\<alpha> \<rightharpoonup>'\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ("D\<^sub>p")
translations
  "D\<^sub>p f" \<rightleftharpoons> "AllD f"

notation
   "deny_pfun"  (binder "\<forall>D" 10) and
   "allow_pfun" (binder "\<forall>A" 10)

lemma AllD_norm[simp]: "deny_pfun (id o (\<lambda>x. \<lfloor>x\<rfloor>)) = (\<forall>Dx. \<lfloor>x\<rfloor>)"
  by(simp add:id_def comp_def)
    
lemma AllD_norm2[simp]: "deny_pfun (Some o id) = (\<forall>Dx. \<lfloor>x\<rfloor>)"
  by(simp add:id_def comp_def)
    
lemma AllA_norm[simp]: "allow_pfun (id o Some) = (\<forall>Ax. \<lfloor>x\<rfloor>)"
  by(simp add:id_def comp_def)
    
lemma AllA_norm2[simp]: "allow_pfun (Some o id) = (\<forall>Ax. \<lfloor>x\<rfloor>)"
  by(simp add:id_def comp_def)
    
lemma AllA_apply[simp]: "(\<forall>Ax. Some (P x)) x = \<lfloor>allow (P x)\<rfloor>"
  by(simp add:allow_pfun_def)
    
lemma AllD_apply[simp]: "(\<forall>Dx. Some (P x)) x = \<lfloor>deny (P x)\<rfloor>"
  by(simp add:deny_pfun_def)

lemma neq_Allow_Deny: "pf \<noteq> \<emptyset> \<Longrightarrow> (deny_pfun pf) \<noteq> (allow_pfun pf)"
  apply (erule contrapos_nn)
  apply (rule ext)
  subgoal for x
    apply (drule_tac x=x in fun_cong)
    apply (auto simp: deny_pfun_def allow_pfun_def)
    apply (case_tac "pf x =  \<bottom>")
     apply (auto)
    done
  done

subsection\<open>Common Instances\<close>

definition allow_all_fun :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ("A\<^sub>f")
  where "allow_all_fun f =  allow_pfun (Some o f)"

definition deny_all_fun :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<alpha> \<mapsto> '\<beta>)" ("D\<^sub>f")
  where "deny_all_fun f \<equiv> deny_pfun (Some o f)"

definition
   deny_all_id   :: "'\<alpha> \<mapsto> '\<alpha>" ("D\<^sub>I") where 
  "deny_all_id  \<equiv> deny_pfun (id o Some)"

definition
   allow_all_id    :: "'\<alpha> \<mapsto> '\<alpha>" ("A\<^sub>I") where
  "allow_all_id  \<equiv> allow_pfun (id o Some)"

definition 
  allow_all    :: "('\<alpha> \<mapsto> unit)"  ("A\<^sub>U") where 
  "allow_all p  = \<lfloor>allow ()\<rfloor>" 

definition 
  deny_all :: "('\<alpha> \<mapsto> unit)" ("D\<^sub>U") where
  "deny_all p   = \<lfloor>deny ()\<rfloor>"              

text\<open>... and resulting properties:\<close>

lemma "A\<^sub>I  \<Oplus> Map.empty  = A\<^sub>I"
  by simp 
  
lemma "A\<^sub>f f  \<Oplus> Map.empty  = A\<^sub>f f"
  by simp 
  
lemma "allow_pfun Map.empty = Map.empty"
  apply (rule ext)
  apply (simp add: allow_pfun_def)
  done

lemma allow_left_cancel :"dom pf = UNIV \<Longrightarrow> (allow_pfun pf) \<Oplus> x = (allow_pfun pf)" 
  apply (rule ext)+
  apply (auto simp: allow_pfun_def option.splits)
  done


lemma deny_left_cancel :"dom pf = UNIV \<Longrightarrow> (deny_pfun pf) \<Oplus> x = (deny_pfun pf)"
  apply (rule ext)+
  by (auto simp: deny_pfun_def option.splits)

subsection\<open>Domain, Range, and Restrictions\<close>

text\<open>
  Since policies are essentially maps, we inherit the basic definitions for 
  domain and range on  Maps: \\
  \verb+Map.dom_def+ :  @{thm Map.dom_def} \\
  whereas range is just an abrreviation for image:
  \begin{verbatim}
  abbreviation range :: "('a => 'b) => 'b set" 
  where -- "of function"  "range f == f ` UNIV"
  \end{verbatim}
  As a consequence, we inherit the following properties on
  policies:
  \begin{itemize}
  \item  \verb+Map.domD+ @{thm Map.domD}
  \item\verb+Map.domI+ @{thm Map.domI}
  \item\verb+Map.domIff+ @{thm Map.domIff}
  \item\verb+Map.dom_const+ @{thm Map.dom_const}
  \item\verb+Map.dom_def+ @{thm Map.dom_def}
  \item\verb+Map.dom_empty+ @{thm Map.dom_empty}
  \item\verb+Map.dom_eq_empty_conv+ @{thm Map.dom_eq_empty_conv}
  \item\verb+Map.dom_eq_singleton_conv+ @{thm Map.dom_eq_singleton_conv}
  \item\verb+Map.dom_fun_upd+ @{thm Map.dom_fun_upd}
  \item\verb+Map.dom_if+ @{thm Map.dom_if}
  \item\verb+Map.dom_map_add+ @{thm Map.dom_map_add}
  \end{itemize}
\<close>

text\<open>
  However, some properties are specific to policy concepts: 
\<close>
lemma sub_ran : "ran p  \<subseteq> Allow \<union> Deny"
  apply (auto simp: Allow_def Deny_def ran_def full_SetCompr_eq[symmetric])[1]
  subgoal for x a
    apply (case_tac "x")
     apply (simp_all)
    done
  done 
    
lemma dom_allow_pfun [simp]:"dom(allow_pfun f) = dom f"
  apply (auto simp: allow_pfun_def)
  subgoal for x y
    apply (case_tac "f x", simp_all)
    done
  done
    
lemma dom_allow_all: "dom(A\<^sub>f f) = UNIV"
  by(auto simp: allow_all_fun_def o_def)

lemma dom_deny_pfun [simp]:"dom(deny_pfun f) = dom f"
  apply (auto simp: deny_pfun_def)[1]
  apply (case_tac "f x")
  apply (simp_all)
  done

lemma dom_deny_all: " dom(D\<^sub>f f) = UNIV"
  by(auto simp: deny_all_fun_def o_def)

lemma ran_allow_pfun [simp]:"ran(allow_pfun f) = allow `(ran f)"
  apply (simp add: allow_pfun_def ran_def) 
  apply (rule set_eqI)
  apply (auto)[1]
  subgoal for x a 
    apply (case_tac "f a")
     apply (auto simp: image_def)[1]
     apply (auto simp: image_def)[1]
    done 
  subgoal for xa a
    apply (rule_tac x=a in exI)
    apply (simp)
    done
  done

lemma ran_allow_all: "ran(A\<^sub>f id) = Allow"
  apply (simp add: allow_all_fun_def Allow_def o_def)
  apply (rule set_eqI)
  apply (auto simp: image_def ran_def)
  done
    
lemma ran_deny_pfun[simp]: "ran(deny_pfun f) = deny ` (ran f)"
  apply (simp add: deny_pfun_def ran_def)
  apply (rule set_eqI)
  apply (auto)[1] 
  subgoal for x a 
    apply (case_tac "f a")
     apply (auto simp: image_def)[1]
    apply (auto simp: image_def)[1]
    done
  subgoal for xa a
    apply (rule_tac x=a in exI)
    apply (simp)
    done
  done 
    
lemma ran_deny_all: "ran(D\<^sub>f id) = Deny"
  apply (simp add: deny_all_fun_def Deny_def o_def)
  apply (rule set_eqI)
  apply (auto simp: image_def ran_def)
  done


text\<open>
  Reasoning over \verb+dom+ is most crucial since it paves the way for simplification and 
  reordering of policies composed by override (i.e. by the normal left-to-right rule composition
  method.
  \begin{itemize}
    \item \verb+Map.dom_map_add+ @{thm Map.dom_map_add}
    \item \verb+Map.inj_on_map_add_dom+ @{thm Map.inj_on_map_add_dom}
    \item \verb+Map.map_add_comm+ @{thm Map.map_add_comm}
    \item \verb+Map.map_add_dom_app_simps(1)+ @{thm Map.map_add_dom_app_simps(1)}
    \item \verb+Map.map_add_dom_app_simps(2)+ @{thm Map.map_add_dom_app_simps(2)}
    \item \verb+Map.map_add_dom_app_simps(3)+ @{thm Map.map_add_dom_app_simps(3)}
    \item \verb+Map.map_add_upd_left+ @{thm Map.map_add_upd_left}
  \end{itemize}
  The latter rule also applies to allow- and deny-override.
\<close>

definition dom_restrict :: "['\<alpha> set, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<beta>" (infixr "\<triangleleft>" 55)
where     "S \<triangleleft> p \<equiv> (\<lambda>x. if x \<in> S then p x else \<bottom>)"

lemma dom_dom_restrict[simp] : "dom(S \<triangleleft> p) = S \<inter> dom p"
  apply (auto simp: dom_restrict_def)
  subgoal for x y
    apply (case_tac "x \<in> S")
     apply (simp_all)
    done 
  subgoal for x y 
    apply (case_tac "x \<in> S")
     apply (simp_all)
    done
  done 

lemma dom_restrict_idem[simp] : "(dom p) \<triangleleft> p = p"
  apply (rule ext) 
  apply (auto simp: dom_restrict_def
      dest: neq_commute[THEN iffD1,THEN not_None_eq [THEN iffD1]])
  done

lemma dom_restrict_inter[simp] : "T \<triangleleft> S \<triangleleft> p = T \<inter> S \<triangleleft> p"
  apply (rule ext)
  apply (auto simp: dom_restrict_def
      dest: neq_commute[THEN iffD1,THEN not_None_eq [THEN iffD1]])
  done

definition ran_restrict :: "['\<alpha>\<mapsto>'\<beta>,'\<beta> decision set] \<Rightarrow> '\<alpha> \<mapsto>'\<beta>" (infixr "\<triangleright>" 55)
where     "p \<triangleright> S \<equiv> (\<lambda>x. if p x \<in> (Some`S) then p x else \<bottom>)"

definition ran_restrict2 :: "['\<alpha>\<mapsto>'\<beta>,'\<beta> decision set] \<Rightarrow> '\<alpha> \<mapsto>'\<beta>" (infixr "\<triangleright>2" 55)
where     "p \<triangleright>2 S \<equiv> (\<lambda>x. if (the (p x)) \<in> (S) then p x else \<bottom>)"

lemma "ran_restrict = ran_restrict2"
  apply (rule ext)+
  apply (simp add: ran_restrict_def ran_restrict2_def)
  subgoal for x xa xb
    apply (case_tac "x xb")
     apply simp_all 
    apply (metis inj_Some inj_image_mem_iff)
    done
  done 


lemma ran_ran_restrict[simp] : "ran(p \<triangleright> S) = S \<inter> ran p"
  by(auto simp: ran_restrict_def image_def ran_def)
    
lemma ran_restrict_idem[simp] : "p \<triangleright> (ran p) = p"
  apply (rule ext)
  apply (auto simp: ran_restrict_def image_def Ball_def ran_def)
  apply (erule contrapos_pp)
  apply (auto dest!: neq_commute[THEN iffD1,THEN not_None_eq [THEN iffD1]])
  done
    
lemma ran_restrict_inter[simp] : "(p \<triangleright> S) \<triangleright> T = p \<triangleright> T \<inter> S"
  apply (rule ext) 
  apply (auto simp: ran_restrict_def
      dest: neq_commute[THEN iffD1,THEN not_None_eq [THEN iffD1]])
  done
    
lemma ran_gen_A[simp] : "(\<forall>Ax. \<lfloor>P x\<rfloor>) \<triangleright> Allow = (\<forall>Ax. \<lfloor>P x\<rfloor>)"
  apply (rule ext)
  apply (auto simp: Allow_def ran_restrict_def)
  done
    
lemma ran_gen_D[simp] : "(\<forall>Dx. \<lfloor>P x\<rfloor>) \<triangleright> Deny = (\<forall>Dx. \<lfloor>P x\<rfloor>)"
  apply (rule ext)
  apply (auto simp: Deny_def ran_restrict_def)
  done

lemmas ElementaryPoliciesDefs = deny_pfun_def allow_pfun_def allow_all_fun_def deny_all_fun_def 
                                allow_all_id_def deny_all_id_def allow_all_def deny_all_def 
                                dom_restrict_def ran_restrict_def

end
