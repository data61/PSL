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

section\<open>The Core of the Unified Policy Framework (UPF)\<close>
theory
  UPFCore
  imports 
    Monads
begin


subsection\<open>Foundation\<close>
text\<open>
  The purpose of this theory is to formalize a somewhat non-standard view
  on the fundamental concept of a security policy which is worth outlining.
  This view has arisen from prior experience in the modelling of network
  (firewall) policies. Instead of regarding policies as relations on resources,
  sets of permissions, etc., we emphasise the view that a policy is a policy
  decision function that grants or denies access to resources, permissions, etc.
  In other words, we model the concrete function that implements the policy
  decision point in a system, and which represents a "wrapper" around the
  business logic. An advantage of this view is that it is compatible
  with many different policy models, enabling a uniform modelling framework to be
  defined. Furthermore, this function is typically a large cascade of nested
  conditionals, using conditions referring to an internal state and security
  contexts of the system or a user. This cascade of conditionals can easily be
  decomposed into a set of test cases similar to transformations used for binary
  decision diagrams (BDD), and motivate equivalence class testing for unit test and 
  sequence test scenarios. From the modelling perspective, using \HOL as
  its input language, we will consequently use the expressive power of its
  underlying functional  programming language, including the possibility to
  define higher-order combinators.

  In more detail, we model policies as partial functions based on input
  data $\alpha$ (arguments, system state, security context, ...) to output
  data $\beta$: 
\<close>

datatype '\<alpha> decision = allow '\<alpha> | deny '\<alpha>

type_synonym ('\<alpha>,'\<beta>) policy = "'\<alpha>  \<rightharpoonup> '\<beta> decision" (infixr "|->" 0)

text\<open>In the following, we introduce a number of shortcuts and alternative notations.
The type of policies is represented as:\<close>

translations (type)        "'\<alpha> |-> '\<beta>" <= (type) "'\<alpha>  \<rightharpoonup> '\<beta> decision"
type_notation "policy" (infixr "\<mapsto>" 0) 

text\<open>... allowing the notation @{typ "'\<alpha> \<mapsto> '\<beta>"}  for the policy type and the
alternative notations for @{term None} and @{term Some} of the \HOL library 
@{typ "'\<alpha> option"} type:\<close>

notation    "None" ("\<bottom>")
notation    "Some" ("\<lfloor>_\<rfloor>" 80)

text\<open>Thus, the range of a policy may consist of @{term "\<lfloor>accept x\<rfloor>"} data,
  of @{term "\<lfloor>deny x\<rfloor>"} data, as well as @{term "\<bottom>"} modeling the undefinedness
  of a policy, i.e. a policy is considered as a partial function. Partial 
  functions are used since we describe elementary policies by partial system 
  behaviour, which are glued together by operators such as function override and 
  functional composition. 
\<close>

text\<open>We define the two fundamental sets, the allow-set $Allow$ and the
  deny-set $Deny$ (written $A$ and $D$ set for short), to characterize these
  two main sets of the range of a policy. 
\<close>
definition Allow :: "('\<alpha> decision) set"
where     "Allow = range allow"

definition Deny :: "('\<alpha> decision) set"
where     "Deny = range deny"
 

subsection\<open>Policy Constructors\<close>
text\<open>
  Most elementary policy constructors are based on the
  update operation @{thm [source] "Fun.fun_upd_def"} @{thm Fun.fun_upd_def}
  and the maplet-notation @{term "a(x \<mapsto> y)"} used for @{term "a(x:=\<lfloor>y\<rfloor>)"}.

  Furthermore, we add notation adopted to our problem domain:\<close>

nonterminal policylets and policylet

syntax
  "_policylet1"  :: "['a, 'a] => policylet"                 ("_ /\<mapsto>\<^sub>+/ _")
  "_policylet2"  :: "['a, 'a] => policylet"                 ("_ /\<mapsto>\<^sub>-/ _")
  ""             :: "policylet => policylets"               ("_")
  "_Maplets"     :: "[policylet, policylets] => policylets" ("_,/ _")
  "_Maplets"     :: "[policylet, policylets] => policylets" ("_,/ _")
   "_MapUpd"      :: "['a |-> 'b, policylets] => 'a |-> 'b"  ("_/'(_')" [900,0]900)
  "_emptypolicy" :: "'a |-> 'b"                             ("\<emptyset>")

translations
  "_MapUpd m (_Maplets xy ms)"   \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_policylet1 x y)"  \<rightleftharpoons> "m(x := CONST Some (CONST allow y))"
  "_MapUpd m (_policylet2 x y)"  \<rightleftharpoons> "m(x := CONST Some (CONST deny y))"
  "\<emptyset>"                            \<rightleftharpoons> "CONST Map.empty" 

text\<open>Here are some lemmas essentially showing syntactic equivalences:\<close>
lemma test: "\<emptyset>(x\<mapsto>\<^sub>+a, y\<mapsto>\<^sub>-b) = \<emptyset>(x \<mapsto>\<^sub>+ a, y \<mapsto>\<^sub>- b)"   by simp

lemma test2: "p(x\<mapsto>\<^sub>+a,x\<mapsto>\<^sub>-b) = p(x\<mapsto>\<^sub>-b)"   by simp

text\<open>
  We inherit a fairly rich theory on policy updates from Map here. Some examples are: 
\<close>

lemma pol_upd_triv1: "t k =   \<lfloor>allow x\<rfloor> \<Longrightarrow> t(k\<mapsto>\<^sub>+x) = t"
  by (rule ext) simp

lemma pol_upd_triv2: "t k = \<lfloor>deny x\<rfloor> \<Longrightarrow> t(k\<mapsto>\<^sub>-x) = t"
  by (rule ext) simp

lemma pol_upd_allow_nonempty: "t(k\<mapsto>\<^sub>+x) \<noteq> \<emptyset>" 
  by simp

lemma pol_upd_deny_nonempty: "t(k\<mapsto>\<^sub>-x) \<noteq> \<emptyset>" 
  by simp

lemma pol_upd_eqD1 : "m(a\<mapsto>\<^sub>+x) = n(a\<mapsto>\<^sub>+y) \<Longrightarrow> x = y"
  by(auto dest: map_upd_eqD1)

lemma pol_upd_eqD2 : "m(a\<mapsto>\<^sub>-x) = n(a\<mapsto>\<^sub>-y) \<Longrightarrow> x = y"
  by(auto dest: map_upd_eqD1)

lemma pol_upd_neq1 [simp]: "m(a\<mapsto>\<^sub>+x) \<noteq> n(a\<mapsto>\<^sub>-y)"
  by(auto dest: map_upd_eqD1)


subsection\<open>Override Operators\<close>
text\<open>
  Key operators for constructing policies are the override operators. There are four different 
  versions of them, with one of them being the override operator from the Map theory. As it is 
  common to compose policy rules in a ``left-to-right-first-fit''-manner, that one is taken as 
  default, defined by a syntax translation from the provided override operator from the Map 
  theory (which does it in reverse order).
\<close>

syntax
  "_policyoverride"  :: "['a \<mapsto> 'b, 'a \<mapsto> 'b] \<Rightarrow> 'a \<mapsto> 'b" (infixl "\<Oplus>" 100)
translations
  "p \<Oplus> q" \<rightleftharpoons> "q ++ p" 


text\<open>
  Some elementary facts inherited from Map are:
\<close>

lemma override_empty: "p \<Oplus> \<emptyset> = p" 
  by simp

lemma empty_override: "\<emptyset> \<Oplus> p = p" 
  by simp

lemma override_assoc: "p1 \<Oplus> (p2 \<Oplus> p3) = (p1 \<Oplus> p2) \<Oplus> p3" 
  by simp

text\<open>
  The following two operators are variants of the standard override.  For override\_A, 
  an allow of wins over a deny. For override\_D, the situation is dual. 
\<close>

definition override_A :: "['\<alpha>\<mapsto>'\<beta>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<beta>" (infixl "++'_A" 100) 
where  "m2 ++_A m1 = 
          (\<lambda>x. (case m1 x of 
                 \<lfloor>allow a\<rfloor> \<Rightarrow>  \<lfloor>allow a\<rfloor>
               | \<lfloor>deny a\<rfloor>  \<Rightarrow> (case m2 x of \<lfloor>allow b\<rfloor> \<Rightarrow> \<lfloor>allow b\<rfloor> 
                                            | _ \<Rightarrow> \<lfloor>deny a\<rfloor>)
               | \<bottom> \<Rightarrow> m2 x)
           )"

syntax
  "_policyoverride_A"  :: "['a \<mapsto> 'b, 'a \<mapsto> 'b] \<Rightarrow> 'a \<mapsto> 'b" (infixl "\<Oplus>\<^sub>A" 100)
translations
  "p \<Oplus>\<^sub>A q" \<rightleftharpoons> "p ++_A q"

lemma override_A_empty[simp]: "p \<Oplus>\<^sub>A \<emptyset> = p" 
  by(simp add:override_A_def)

lemma empty_override_A[simp]: "\<emptyset> \<Oplus>\<^sub>A p = p" 
  apply (rule ext)
  apply (simp add:override_A_def)
  subgoal for x 
    apply (case_tac "p x")
     apply (simp_all)
    subgoal for a
      apply (case_tac a)
       apply (simp_all)
      done
    done 
  done 


lemma override_A_assoc: "p1 \<Oplus>\<^sub>A (p2 \<Oplus>\<^sub>A p3) = (p1 \<Oplus>\<^sub>A p2) \<Oplus>\<^sub>A p3" 
  by (rule ext, simp add: override_A_def split: decision.splits  option.splits)

definition override_D :: "['\<alpha>\<mapsto>'\<beta>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha>\<mapsto>'\<beta>" (infixl "++'_D" 100) 
where "m1 ++_D m2 = 
          (\<lambda>x. case m2 x of 
                \<lfloor>deny a\<rfloor> \<Rightarrow> \<lfloor>deny a\<rfloor>
              | \<lfloor>allow a\<rfloor> \<Rightarrow> (case m1 x of \<lfloor>deny b\<rfloor> \<Rightarrow> \<lfloor>deny b\<rfloor>
                                  | _ \<Rightarrow> \<lfloor>allow a\<rfloor>)
              | \<bottom> \<Rightarrow> m1 x 
           )"
 
syntax
  "_policyoverride_D"  :: "['a \<mapsto> 'b, 'a \<mapsto> 'b] \<Rightarrow> 'a \<mapsto> 'b" (infixl "\<Oplus>\<^sub>D" 100)
translations
  "p \<Oplus>\<^sub>D q" \<rightleftharpoons> "p ++_D q"

lemma override_D_empty[simp]: "p \<Oplus>\<^sub>D \<emptyset> = p" 
  by(simp add:override_D_def)

lemma empty_override_D[simp]: "\<emptyset> \<Oplus>\<^sub>D p = p" 
  apply (rule ext)
  apply (simp add:override_D_def)
  subgoal for x 
    apply (case_tac "p x", simp_all)
    subgoal for a
      apply (case_tac a, simp_all)
      done
    done
  done

lemma override_D_assoc: "p1 \<Oplus>\<^sub>D (p2 \<Oplus>\<^sub>D p3) = (p1 \<Oplus>\<^sub>D p2) \<Oplus>\<^sub>D p3"
  apply (rule ext)
  apply (simp add: override_D_def split: decision.splits  option.splits)
done

subsection\<open>Coercion Operators\<close>
text\<open>
  Often, especially when combining policies of different type, it is necessary to 
  adapt the input or output domain of a policy to a more refined context. 
\<close>                        

text\<open>
  An analogous for the range of a policy is defined as follows: 
\<close>

definition policy_range_comp :: "['\<beta>\<Rightarrow>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha> \<mapsto>'\<gamma>"   (infixl "o'_f" 55) 
where
  "f o_f p = (\<lambda>x. case p x of
                     \<lfloor>allow y\<rfloor> \<Rightarrow> \<lfloor>allow (f y)\<rfloor>
                   | \<lfloor>deny y\<rfloor> \<Rightarrow> \<lfloor>deny (f y)\<rfloor>
                   | \<bottom> \<Rightarrow> \<bottom>)"

syntax
  "_policy_range_comp" :: "['\<beta>\<Rightarrow>'\<gamma>, '\<alpha>\<mapsto>'\<beta>] \<Rightarrow> '\<alpha> \<mapsto>'\<gamma>" (infixl "o\<^sub>f" 55)
translations
  "p o\<^sub>f q" \<rightleftharpoons> "p o_f q"

lemma policy_range_comp_strict : "f o\<^sub>f \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: policy_range_comp_def)
  done


text\<open>
  A generalized version is, where separate coercion functions are applied to the result 
  depending on the decision of the policy is as follows: 
\<close>

definition range_split :: "[('\<beta>\<Rightarrow>'\<gamma>)\<times>('\<beta>\<Rightarrow>'\<gamma>),'\<alpha> \<mapsto> '\<beta>] \<Rightarrow> '\<alpha> \<mapsto> '\<gamma>"
                          (infixr "\<nabla>" 100)
where "(P) \<nabla> p = (\<lambda>x. case p x of 
                          \<lfloor>allow y\<rfloor> \<Rightarrow> \<lfloor>allow ((fst P) y)\<rfloor>
                        | \<lfloor>deny y\<rfloor>  \<Rightarrow> \<lfloor>deny ((snd P) y)\<rfloor> 
                        | \<bottom>        \<Rightarrow> \<bottom>)"

lemma range_split_strict[simp]: "P \<nabla> \<emptyset> = \<emptyset>"
  apply (rule ext)
  apply (simp add: range_split_def)
  done


lemma range_split_charn:
  "(f,g) \<nabla> p = (\<lambda>x. case p x of 
                           \<lfloor>allow x\<rfloor> \<Rightarrow> \<lfloor>allow (f x)\<rfloor>
                         | \<lfloor>deny x\<rfloor>  \<Rightarrow> \<lfloor>deny (g x)\<rfloor> 
                         | \<bottom>        \<Rightarrow> \<bottom>)"
  apply (simp add: range_split_def)
  apply (rule ext)
  subgoal for x 
    apply (case_tac "p x")
     apply (simp_all)
    subgoal for a
      apply (case_tac "a")
       apply (simp_all)
      done
    done
  done

text\<open>
  The connection between these two becomes apparent if considering the following lemma:
\<close>

lemma range_split_vs_range_compose: "(f,f) \<nabla> p = f o\<^sub>f p"
  by(simp add: range_split_charn policy_range_comp_def)
    
lemma range_split_id [simp]: "(id,id) \<nabla> p = p"
  apply (rule ext)
  apply (simp add: range_split_charn id_def)
  subgoal for x
    apply (case_tac "p x")
     apply (simp_all)
    subgoal for a
      apply (case_tac "a")
       apply (simp_all)
      done
    done 
  done 

lemma range_split_bi_compose [simp]: "(f1,f2) \<nabla> (g1,g2) \<nabla> p = (f1 o g1,f2 o g2) \<nabla> p"
  apply (rule ext)
  apply (simp add: range_split_charn comp_def)
  subgoal for x 
    apply (case_tac "p x")
     apply (simp_all)
    subgoal for a
      apply (case_tac "a")
       apply (simp_all)
      done
    done
  done

text\<open>
  The next three operators are rather exotic and in most cases not used. 
\<close>

text \<open>
  The following is a variant of range\_split, where the change in the decision depends 
  on the input instead of the output. 
\<close>

definition dom_split2a :: "[('\<alpha> \<rightharpoonup> '\<gamma>) \<times> ('\<alpha> \<rightharpoonup>'\<gamma>),'\<alpha> \<mapsto> '\<beta>] \<Rightarrow> '\<alpha> \<mapsto> '\<gamma>"         (infixr "\<Delta>a" 100)
where "P \<Delta>a p = (\<lambda>x. case p x of 
                          \<lfloor>allow y\<rfloor> \<Rightarrow> \<lfloor>allow (the ((fst P) x))\<rfloor>
                        | \<lfloor>deny y\<rfloor>  \<Rightarrow>  \<lfloor>deny (the ((snd P) x))\<rfloor> 
                        | \<bottom>        \<Rightarrow> \<bottom>)"

definition dom_split2 :: "[('\<alpha> \<Rightarrow> '\<gamma>) \<times> ('\<alpha> \<Rightarrow>'\<gamma>),'\<alpha> \<mapsto> '\<beta>] \<Rightarrow> '\<alpha> \<mapsto> '\<gamma>"          (infixr "\<Delta>" 100)
where "P \<Delta> p = (\<lambda>x. case p x of 
                          \<lfloor>allow y\<rfloor> \<Rightarrow> \<lfloor>allow ((fst P) x)\<rfloor>
                        | \<lfloor>deny y\<rfloor>  \<Rightarrow>  \<lfloor>deny ((snd P) x)\<rfloor>
                        | \<bottom>        \<Rightarrow> \<bottom>)"

definition range_split2 :: "[('\<alpha> \<Rightarrow> '\<gamma>) \<times> ('\<alpha> \<Rightarrow>'\<gamma>),'\<alpha> \<mapsto> '\<beta>] \<Rightarrow> '\<alpha> \<mapsto> ('\<beta> \<times>'\<gamma>)" (infixr "\<nabla>2" 100)
where "P \<nabla>2 p = (\<lambda>x. case p x of 
                          \<lfloor>allow y\<rfloor> \<Rightarrow> \<lfloor>allow (y,(fst P) x)\<rfloor>
                        | \<lfloor>deny y\<rfloor>  \<Rightarrow> \<lfloor>deny (y,(snd P) x)\<rfloor> 
                        | \<bottom>        \<Rightarrow> \<bottom>)"

text\<open>
  The following operator is used for transition policies only: a transition policy is transformed 
  into a state-exception monad. Such a monad can for example be used for test case generation using 
  HOL-Testgen~\cite{brucker.ea:theorem-prover:2012}.
\<close>

definition policy2MON :: "('\<iota>\<times>'\<sigma> \<mapsto> 'o\<times>'\<sigma>) \<Rightarrow> ('\<iota> \<Rightarrow>('o decision,'\<sigma>) MON\<^sub>S\<^sub>E)"
where "policy2MON p = (\<lambda> \<iota> \<sigma>. case p (\<iota>,\<sigma>) of
                              \<lfloor>(allow (outs,\<sigma>'))\<rfloor> \<Rightarrow> \<lfloor>(allow outs, \<sigma>')\<rfloor>
                            | \<lfloor>(deny (outs,\<sigma>'))\<rfloor>  \<Rightarrow> \<lfloor>(deny outs, \<sigma>')\<rfloor>
                            | \<bottom>                  \<Rightarrow> \<bottom>)"

lemmas UPFCoreDefs = Allow_def Deny_def override_A_def override_D_def policy_range_comp_def 
                     range_split_def dom_split2_def map_add_def restrict_map_def
end

