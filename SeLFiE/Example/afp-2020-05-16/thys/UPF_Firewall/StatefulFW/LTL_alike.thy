(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
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
 *****************************************************************************)

subsection \<open>Termporal Combinators\<close>
theory
  LTL_alike 
  imports 
    Main
begin

text\<open>
  In the following, we present a small embbeding of temporal combinators, that may help to 
  formulate typical temporal properties in traces and protocols concisely. It is based on 
  \emph{finite} lists, therefore the properties of this logic are not fully compatible with  
  LTL based on Kripke-structures. For the purpose of this demonstration, however, the difference 
  does not matter.
\<close>

fun nxt :: "('\<alpha> list \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" ("N")
where 
   "nxt p [] = False"
|  "nxt p (a # S) = (p S)"

text\<open>Predicate $p$ holds at first position.\<close>

fun atom :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" ("\<guillemotleft>_\<guillemotright>")
where 
   "atom p [] = False"
|  "atom p (a # S) = (p a)"

lemma holds_mono : "\<guillemotleft>q\<guillemotright> s \<Longrightarrow> \<guillemotleft>q\<guillemotright> (s @ t)"
  by(cases "s",simp_all)


fun always :: "('\<alpha> list \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" ("\<box>")
where 
   "always p [] = True"
|  "always p (a # S) = ((p (a # S)) \<and> always p S)"

text\<open>
  Always is a generalization of the \verb+list_all+ combinator from the List-library; if arguing 
  locally, this paves the way to a wealth of library lemmas. 
\<close>
lemma always_is_listall : "(\<box> \<guillemotleft>p\<guillemotright>) (t) = list_all (p) (t)"
  by(induct "t", simp_all)

fun eventually :: "('\<alpha> list \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" ("\<diamondsuit>")
where 
   "eventually p [] = False"
|  "eventually p (a # S) = ((p (a # S)) \<or> eventually p S)"


text\<open>
  Eventually is a generalization of the \verb+list_ex+ combinator from the List-library; if arguing 
  locally, this paves the way to a wealth of library lemmas. 
\<close>
lemma eventually_is_listex : "(\<diamondsuit> \<guillemotleft>p\<guillemotright>) (t) = list_ex (p) (t)"
  by(induct "t", simp_all)

text\<open>
  The next two constants will help us later in defining the state transitions. The constant 
  \<open>before\<close> is \<open>True\<close> if for all elements which appear before the first element 
  for which  \<open>q\<close> holds, \<open>p\<close> must hold.
\<close>

fun before :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" 
where 
  "before p q [] = False"
| "before p q (a # S) = (q a \<or> (p a \<and> (before p q S)))"

text\<open>
  Analogously there is an operator \<open>not_before\<close> which returns
  \<open>True\<close> if for all elements which appear before the first
  element for which \<open>q\<close> holds, \<open>p\<close> must not hold.
\<close>

fun not_before :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" 
where  
  "not_before p q [] = False"
| "not_before p q (a # S) = (q a \<or> (\<not> (p a) \<and> (not_before p q S)))"

lemma not_before_superfluous: 
  "not_before p q = before (Not o p) q"
  apply(rule ext) 
  subgoal for n 
    apply(induct_tac "n")
     apply(simp_all)
    done
  done
    
text\<open>General "before":\<close>
fun until :: "('\<alpha> list \<Rightarrow> bool) \<Rightarrow> ('\<alpha> list \<Rightarrow> bool) \<Rightarrow> '\<alpha> list \<Rightarrow> bool" (infixl "U" 66)
where 
  "until p q [] = False"
| "until p q (a # S) = (\<exists> s t. a # S= s @ t \<and> p s \<and>  q t)"

text\<open>This leads to this amazingly tricky proof:\<close>
lemma before_vs_until: 
"(before p q) = ((\<box>\<guillemotleft>p\<guillemotright>) U \<guillemotleft>q\<guillemotright>)"
proof -
  have A:"\<And>a. q a \<Longrightarrow> (\<exists>s t. [a] = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t)" 
    apply(rule_tac x="[]" in exI)
    apply(rule_tac x="[a]" in exI, simp)
    done
  have B:"\<And>a. (\<exists>s t. [a] = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t) \<Longrightarrow> q a"
    apply auto
    apply(case_tac "t=[]", auto simp:List.neq_Nil_conv)
    apply(case_tac "s=[]", auto simp:List.neq_Nil_conv)
    done
  have C:"\<And>a aa list.(q a \<or> p a \<and> (\<exists>s t. aa # list = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t)) 
                         \<Longrightarrow> (\<exists>s t. a # aa # list = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t)"
    apply auto[1]
     apply(rule_tac x="[]" in exI)
     apply(rule_tac x="a # aa # list" in exI, simp)
    apply(rule_tac x="a # s" in exI)
    apply(rule_tac x="t" in exI,simp)
    done
  have D:"\<And>a aa list.(\<exists>s t. a # aa # list = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t)
                         \<Longrightarrow> (q a \<or> p a \<and> (\<exists>s t. aa # list = s @ t \<and> \<box> \<guillemotleft>p\<guillemotright> s \<and> \<guillemotleft>q\<guillemotright> t))"
    apply auto[1]
     apply(case_tac "s", auto simp:List.neq_Nil_conv)
    apply(case_tac "s", auto simp:List.neq_Nil_conv)
    done
  show ?thesis
    apply(rule ext)
    subgoal for n
      apply(induct_tac "n")
       apply(simp)
        subgoal for x xs
          apply(case_tac "xs")
           apply(simp,rule iffI,erule A, erule B)
          apply(simp,rule iffI,erule C, erule D)
          done
        done
      done
  qed
end
