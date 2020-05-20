(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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
 ******************************************************************************\<close>
(*>*)

chapter\<open>The Notion of Processes\<close>

text\<open>As mentioned earlier, we base the theory of CSP on HOLCF, a Isabelle/HOL library
providing a theory of continuous functions, fixpoint induction and recursion.\<close>

theory Process
  imports HOLCF
begin

text\<open>Since HOLCF sets the default type class to @{class "cpo"}, while our 
Process theory establishes links between standard types and @{class "pcpo"} 
types. Consequently, we reset the default type class to the default in HOL.\<close>

default_sort type

subsection\<open>Pre-Requisite: Basic Traces and tick-Freeness\<close>

text\<open>The denotational semantics of CSP assumes a distinguishable
special event, called \verb+tick+ and written $\checkmark$, that is required
to occur only in the end of traces in order to signalize successful termination of
a process. (In the original text of Hoare, this treatment was more
liberal and lead to foundational problems: the process invariant
could not be established for the sequential composition operator
of CSP; see @{cite "tej.ea:corrected:1997"} for details.)\<close>

datatype '\<alpha> event = ev '\<alpha> | tick

type_synonym '\<alpha> trace = "('\<alpha> event) list"

text\<open>We chose as standard ordering on traces the prefix ordering.\<close>

instantiation  list :: (type) order
begin 

definition  le_list_def  : "(s::'a list) \<le> t \<longleftrightarrow> (\<exists> r. s @ r = t)"

definition  less_list_def: "(s::'a list) < t \<longleftrightarrow> s \<le> t \<and> s \<noteq> t" 

lemma A : "((x::'a list) < y) = (x \<le> y \<and> \<not> y \<le> x)"
by(auto simp: le_list_def less_list_def)

instance 
proof
   fix x y z ::"'a list"
   show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" 
     by(auto simp: le_list_def less_list_def)
   show "x \<le> x"  by(simp add: le_list_def)
   assume A:"x \<le> y" and B:"y \<le> z" thus "x \<le> z"
     apply(insert A B, simp add: le_list_def, safe)  
     apply(rename_tac r ra, rule_tac x="r@ra" in exI, simp)
     done
   assume A:"x \<le> y" and B:"y \<le> x" thus "x = y"
     by(insert A B, auto simp: le_list_def)  
qed

end

text\<open>Some facts on the prefix ordering.\<close>

lemma nil_le[simp]: "[] \<le> s"
by(induct "s", simp_all, auto simp: le_list_def) 

lemma nil_le2[simp]: "s \<le> [] = (s = [])"
by(induct "s", auto simp:le_list_def)

lemma nil_less[simp]: "\<not> t < []"
by(simp add: less_list_def)

lemma nil_less2[simp]: "[] < t @ [a]"
by(simp add: less_list_def)

lemma less_self[simp]: "t < t@[a]"
by(simp add:less_list_def le_list_def)
   
lemma le_length_mono: "s \<le> t \<Longrightarrow> length s \<le> length t"
by(auto simp: le_list_def)

lemma less_length_mono: "s < t \<Longrightarrow> length s < length t"
by(auto simp: less_list_def le_list_def)

lemma less_cons: "s < t \<Longrightarrow> a # s < a # t"
by (simp add: le_list_def less_list_def)

lemma less_append: "s < t \<Longrightarrow> a @ s < a @ t"
by (simp add: le_list_def less_list_def)

lemma less_tail: "s \<noteq> [] \<Longrightarrow> s < t \<Longrightarrow> tl s < tl t"
by (auto simp add: le_list_def less_list_def)

\<comment>\<open>should be in the List library\<close>
lemma list_nonMt_append: "s \<noteq> [] \<Longrightarrow> \<exists> a t. s = t @ [a]"
by(erule rev_mp,induct "s",simp_all,case_tac "s = []",auto)

lemma append_eq_first_pref_spec[rule_format]: "s @ t = r @ [x] \<and> t \<noteq> [] \<longrightarrow> s \<le> r"
  apply(rule_tac x=s in spec)
  apply(induct r,auto)
    apply(erule rev_mp)
    apply(rename_tac xa, rule_tac list=xa in list.induct, simp_all)
  apply(simp add: le_list_def)
  apply(drule list_nonMt_append, auto)
  done

lemma prefixes_fin: "let prefixes = {t. \<exists>t2. x = t @ t2} in finite prefixes \<and> card prefixes = length x + 1"  
proof(induct x, simp)
  case (Cons a x)
  hence A:"finite {t. (\<exists>t2. x = t @ t2)}" using not_add_less2 by fastforce
  have B:"inj_on Cons UNIV" by (metis injI list.inject)
  from Cons A B inj_on_iff_eq_card have  C:"card ((\<lambda>x. a#x)`{t. (\<exists>t2. x = t @ t2)}) = length x + 1"
    by fastforce
  have D:"{t. \<exists>t2. a # x = t @ t2} = {[]} \<union> (\<lambda>x. a#x)`{t. (\<exists>t2. x = t @ t2)}" 
    by(intro set_eqI iffI, auto simp add:Cons_eq_append_conv) 
  from C D card_insert_if[of "(\<lambda>x. a#x)`{t. (\<exists>t2. x = t @ t2)}"] show ?case 
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Un_insert_left finite.insertI 
        finite_imageI image_iff list.distinct(1) list.size(4) local.A sup_bot.left_neutral)
qed

lemma sublists_fin: "finite {t. \<exists>t1 t2. x = t1 @ t @ t2}"
  proof(induct x, simp)
    case (Cons a x)
    have "{t. \<exists>t1 t2. a # x = t1 @ t @ t2} \<subseteq> {t. \<exists>t1 t2. x = t1 @ t @ t2} \<union> {t. \<exists>t2. a#x = t @ t2}"
      apply(auto) by (metis Cons_eq_append_conv)
    with Cons prefixes_fin[of "a#x"] show ?case by (meson finite_UnI finite_subset)
  qed

lemma suffixes_fin: "finite {t. \<exists>t1. x = t1 @ t}"
  apply(subgoal_tac "{t. \<exists>t1. x = t1 @ t} \<subseteq> {t. \<exists>t1 t2. x = t1 @ t @ t2}")
  using infinite_super sublists_fin apply blast
  by blast

text\<open>For the process invariant, it is a key element to
reduce the notion of traces to traces that may only contain
one tick event at the very end. This is captured by the definition
of the predicate \verb+front_tickFree+ and its stronger version
\verb+tickFree+. Here is the theory of this concept.\<close>

definition tickFree :: "'\<alpha> trace \<Rightarrow> bool"
  where "tickFree s = (tick \<notin> set s)"

definition front_tickFree :: "'\<alpha> trace \<Rightarrow> bool"
  where "front_tickFree s = (s =[] \<or> tickFree(tl(rev s)))"

lemma tickFree_Nil [simp]: "tickFree []"
by(simp add: tickFree_def)

lemma tickFree_Cons [simp]: "tickFree (a # t) = (a \<noteq> tick \<and> tickFree t)"
by(auto simp add: tickFree_def)

lemma tickFree_tl : "[|s ~= [] ; tickFree s|] ==> tickFree(tl s)"
by(case_tac s, simp_all)
  
lemma tickFree_append[simp]: "tickFree(s@t) = (tickFree s \<and> tickFree t)"
by(simp add: tickFree_def member_def)

lemma non_tickFree_tick [simp]: "\<not> tickFree [tick]"
by(simp add: tickFree_def)

lemma non_tickFree_implies_nonMt: "\<not> tickFree s \<Longrightarrow> s \<noteq> []"
by(simp add:tickFree_def,erule rev_mp, induct s, simp_all)

lemma  tickFree_rev : "tickFree(rev t) = (tickFree t)"
by(simp  add: tickFree_def member_def)

lemma front_tickFree_Nil[simp]: "front_tickFree []"
by(simp add: front_tickFree_def)

lemma front_tickFree_single[simp]: "front_tickFree [a]"
by(simp add: front_tickFree_def)

lemma tickFree_implies_front_tickFree: "tickFree s \<Longrightarrow> front_tickFree s"
apply(simp add: tickFree_def front_tickFree_def member_def,safe)
apply(erule contrapos_np, simp,(erule rev_mp)+)
apply(rule_tac xs=s in List.rev_induct,simp_all)
done

lemma front_tickFree_charn: "front_tickFree s = (s = [] \<or> (\<exists>a t. s = t @ [a] \<and> tickFree t))"
apply(simp add: front_tickFree_def)
apply(cases "s=[]", simp_all)
apply(drule list_nonMt_append, auto simp: tickFree_rev)
done

lemma front_tickFree_implies_tickFree: "front_tickFree (t @ [a]) \<Longrightarrow> tickFree t"
by(simp add: tickFree_def front_tickFree_def member_def)

lemma tickFree_implies_front_tickFree_single: "tickFree t \<Longrightarrow> front_tickFree (t @ [a])"
by(simp add:front_tickFree_charn) 


lemma nonTickFree_n_frontTickFree: "\<lbrakk>\<not> tickFree s; front_tickFree s \<rbrakk> \<Longrightarrow> \<exists>t. s = t @ [tick]"
apply(frule non_tickFree_implies_nonMt)
apply(drule front_tickFree_charn[THEN iffD1], auto)
done

lemma front_tickFree_dw_closed : "front_tickFree (s @ t) \<Longrightarrow>  front_tickFree s"
apply(erule rev_mp, rule_tac x= s in spec)
apply(rule_tac xs=t in List.rev_induct, simp, safe)
apply(rename_tac x xs xa)
apply(simp only: append_assoc[symmetric])
apply(rename_tac x xs xa, erule_tac x="xa @ xs" in all_dupE)
apply(drule front_tickFree_implies_tickFree)
apply(erule_tac x="xa" in allE, auto)
apply(auto dest!:tickFree_implies_front_tickFree)
done

lemma front_tickFree_append: "\<lbrakk> tickFree s; front_tickFree t\<rbrakk> \<Longrightarrow> front_tickFree (s @ t)"
apply(drule front_tickFree_charn[THEN iffD1], auto)
apply(erule tickFree_implies_front_tickFree)
apply(subst append_assoc[symmetric])
apply(rule tickFree_implies_front_tickFree_single)
apply(auto intro: tickFree_append)
done

lemma front_tickFree_mono: "front_tickFree (t @ r) \<and> r \<noteq> [] \<longrightarrow> tickFree t \<and> front_tickFree r"
by(metis append_assoc append_butlast_last_id front_tickFree_charn 
         front_tickFree_implies_tickFree tickFree_append)


subsection\<open> Basic Types, Traces, Failures and Divergences \<close>

type_synonym '\<alpha> refusal = "('\<alpha> event) set"
type_synonym '\<alpha> failure = "'\<alpha> trace \<times> '\<alpha> refusal"
type_synonym '\<alpha> divergence = "'\<alpha> trace set"
type_synonym '\<alpha> process\<^sub>0 = "'\<alpha> failure set \<times> '\<alpha> divergence"
 
definition FAILURES :: "'\<alpha> process\<^sub>0 \<Rightarrow> ('\<alpha> failure set)"
  where "FAILURES P = fst P"

definition TRACES :: "'\<alpha> process\<^sub>0 \<Rightarrow> ('\<alpha> trace set)"
  where "TRACES P = {tr. \<exists> a. a \<in> FAILURES P \<and> tr = fst a}"

definition DIVERGENCES :: "'\<alpha> process\<^sub>0 \<Rightarrow> '\<alpha> divergence"
  where "DIVERGENCES P = snd P"

definition REFUSALS :: "'\<alpha> process\<^sub>0 \<Rightarrow> ('\<alpha> refusal set)"
  where "REFUSALS P = {ref.  \<exists> F. F \<in> FAILURES P \<and> F = ([],ref)}"

subsection\<open> The Process Type Invariant \<close>

definition is_process :: "'\<alpha> process\<^sub>0 \<Rightarrow> bool" where
  "is_process P =
      (([],{}) \<in> FAILURES P \<and>
       (\<forall> s X.  (s,X) \<in> FAILURES P \<longrightarrow> front_tickFree s) \<and>
       (\<forall> s t . (s@t,{}) \<in> FAILURES P \<longrightarrow> (s,{}) \<in> FAILURES P) \<and>
       (\<forall> s X Y. (s,Y) \<in> FAILURES P & X <= Y \<longrightarrow> (s,X) \<in> FAILURES P) \<and> 
       (\<forall> s X Y. (s,X) \<in> FAILURES P \<and>
       (\<forall> c.      c \<in> Y \<longrightarrow> ((s@[c],{})\<notin>FAILURES P)) \<longrightarrow> 
                                         (s,X \<union> Y)\<in>FAILURES P) \<and>
       (\<forall> s X.  (s@[tick],{}) : FAILURES P \<longrightarrow> (s,X-{tick}) \<in> FAILURES P) \<and>
       (\<forall> s t.  s \<in> DIVERGENCES P \<and> tickFree s \<and> front_tickFree t 
                                      \<longrightarrow> s@t \<in> DIVERGENCES P)  \<and>
       (\<forall> s X. s \<in> DIVERGENCES P \<longrightarrow> (s,X) \<in> FAILURES P) \<and>
       (\<forall> s. s @ [tick] : DIVERGENCES P \<longrightarrow> s \<in> DIVERGENCES P))"


lemma is_process_spec:
 "is_process P = 
       (([],{}) \<in>  FAILURES P \<and>
       (\<forall> s X. (s,X) \<in>  FAILURES P \<longrightarrow> front_tickFree s) \<and>
       (\<forall> s t . (s @ t,{}) \<notin> FAILURES P \<or>   (s,{}) \<in> FAILURES P) \<and>
       (\<forall> s X Y. (s,Y)  \<notin>  FAILURES P \<or> \<not>(X\<subseteq>Y) | (s,X) \<in> FAILURES P) \<and>
       (\<forall> s X Y.(s,X) \<in> FAILURES P \<and> 
       (\<forall> c. c \<in>  Y \<longrightarrow> ((s@[c],{}) \<notin>  FAILURES P)) \<longrightarrow>(s,X \<union> Y) \<in>  FAILURES P) \<and>
       (\<forall> s X. (s@[tick],{}) \<in>  FAILURES P \<longrightarrow> (s,X - {tick}) \<in>  FAILURES P) \<and>
       (\<forall> s t. s \<notin> DIVERGENCES P \<or> \<not>tickFree s \<or> \<not>front_tickFree t 
                                 \<or> s @ t \<in> DIVERGENCES P) \<and>
       (\<forall> s X. s \<notin> DIVERGENCES P \<or> (s,X) \<in>  FAILURES P) \<and>
       (\<forall> s. s @ [tick] \<notin>  DIVERGENCES P \<or> s \<in>  DIVERGENCES P))"
by(simp  only: is_process_def  HOL.nnf_simps(1)  HOL.nnf_simps(3) [symmetric]  
                      HOL.imp_conjL[symmetric])

lemma Process_eqI :
assumes A: "FAILURES P = FAILURES Q "
assumes B: "DIVERGENCES P = DIVERGENCES Q"
shows      "(P::'\<alpha> process\<^sub>0) = Q"
apply(insert A B, unfold FAILURES_def DIVERGENCES_def) 
apply(rule_tac t=P in surjective_pairing[symmetric,THEN subst])
apply(rule_tac t=Q in surjective_pairing[symmetric,THEN subst])
apply(simp)
done

lemma process_eq_spec:
"((P::'a process\<^sub>0) = Q) = (FAILURES P = FAILURES Q \<and> DIVERGENCES P = DIVERGENCES Q)"
apply(auto simp: FAILURES_def DIVERGENCES_def)
apply(rule_tac t=P in surjective_pairing[symmetric,THEN subst])
apply(rule_tac t=Q in surjective_pairing[symmetric,THEN subst])
apply(simp)
done

lemma process_surj_pair: "(FAILURES P,DIVERGENCES P) = P"
by(auto simp:FAILURES_def DIVERGENCES_def)

lemma Fa_eq_imp_Tr_eq: "FAILURES P = FAILURES Q \<Longrightarrow> TRACES P = TRACES Q"
by(auto simp:FAILURES_def DIVERGENCES_def TRACES_def) 

lemma is_process1:  "is_process P \<Longrightarrow> ([],{})\<in> FAILURES P "
by(auto simp: is_process_def)

lemma is_process2: "is_process P \<Longrightarrow> \<forall> s X. (s,X) \<in> FAILURES P \<longrightarrow> front_tickFree s "
by(simp only: is_process_spec, metis)

lemma is_process3: "is_process P \<Longrightarrow> \<forall> s t. (s @ t,{}) \<in> FAILURES P \<longrightarrow> (s, {}) \<in> FAILURES P"
by(simp only: is_process_spec, metis)


lemma is_process3_S_pref: "\<lbrakk>is_process P; (t, {}) \<in> FAILURES P; s \<le> t\<rbrakk> \<Longrightarrow> (s, {}) \<in> FAILURES P"
by(auto simp: le_list_def intro: is_process3 [rule_format])

lemma is_process4: "is_process P \<Longrightarrow> \<forall>s X Y. (s, Y) \<notin> FAILURES P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> FAILURES P"
by(simp only: is_process_spec, simp)

lemma is_process4_S: "\<lbrakk>is_process P; (s, Y) \<in> FAILURES P; X \<subseteq> Y\<rbrakk> \<Longrightarrow> (s, X) \<in> FAILURES P"
by(drule is_process4, auto)

lemma is_process4_S1: "\<lbrakk>is_process P; x \<in> FAILURES P; X \<subseteq> snd x\<rbrakk> \<Longrightarrow> (fst x, X) \<in> FAILURES P"
by(drule is_process4_S, auto)

lemma is_process5:
"is_process P \<Longrightarrow>
    \<forall>sa X Y. (sa, X) \<in> FAILURES P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (sa @ [c], {}) \<notin> FAILURES P) \<longrightarrow> (sa, X \<union> Y) \<in> FAILURES P"
by(drule is_process_spec[THEN iffD1],metis)

lemma is_process5_S:
"\<lbrakk>is_process P; (sa, X) \<in> FAILURES P; \<forall>c. c \<in> Y \<longrightarrow> (sa @ [c], {}) \<notin> FAILURES P\<rbrakk> \<Longrightarrow> (sa, X \<union> Y) \<in> FAILURES P"
by(drule is_process5, metis)

lemma is_process5_S1:
"\<lbrakk>is_process P; (sa, X) \<in> FAILURES P; (sa, X \<union> Y) \<notin> FAILURES P\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> Y \<and> (sa @ [c], {}) \<in> FAILURES P"
by(erule contrapos_np, drule is_process5_S, simp_all)

lemma is_process6: "is_process P \<Longrightarrow>  \<forall> s X. (s@[tick],{}) \<in> FAILURES P \<longrightarrow> (s,X-{tick}) \<in> FAILURES P"
by(drule is_process_spec[THEN iffD1], metis)

lemma is_process6_S: "\<lbrakk>is_process P ;(s@[tick],{}) \<in> FAILURES P\<rbrakk> \<Longrightarrow>  (s,X-{tick}) \<in> FAILURES P"
by(drule is_process6, metis)

lemma is_process7:
"is_process P \<Longrightarrow> \<forall> s t. s \<notin> DIVERGENCES P \<or> \<not> tickFree s \<or> \<not> front_tickFree t \<or> s @ t \<in> DIVERGENCES P"
by(drule is_process_spec[THEN iffD1], metis)

lemma is_process7_S:
"\<lbrakk> is_process P;s : DIVERGENCES P;tickFree s;front_tickFree t\<rbrakk> 
 \<Longrightarrow>  s @ t \<in> DIVERGENCES P"
by(drule is_process7, metis)

lemma is_process8: "is_process P \<Longrightarrow> \<forall>  s X. s \<notin> DIVERGENCES P \<or>  (s,X) \<in> FAILURES P"
by(drule is_process_spec[THEN iffD1], metis)

lemma is_process8_S: "\<lbrakk> is_process P; s \<in> DIVERGENCES P \<rbrakk> \<Longrightarrow> (s,X)  \<in> FAILURES P"
by(drule is_process8, metis)

lemma is_process9: "is_process P \<Longrightarrow> \<forall>  s. s@[tick] \<notin> DIVERGENCES P \<or>  s \<in> DIVERGENCES P"
by(drule is_process_spec[THEN iffD1], metis)

lemma is_process9_S: "\<lbrakk> is_process P;s@[tick] \<in> DIVERGENCES P \<rbrakk> \<Longrightarrow> s \<in> DIVERGENCES P"
by(drule is_process9, metis)

lemma Failures_implies_Traces: " \<lbrakk>is_process P; (s, X) \<in> FAILURES P\<rbrakk> \<Longrightarrow> s \<in> TRACES P"
by(simp add: TRACES_def, metis)

lemma is_process5_sing: 
"\<lbrakk> is_process P ; (s,{x}) \<notin> FAILURES P;(s,{}) \<in> FAILURES P\<rbrakk> \<Longrightarrow> (s @ [x],{}) \<in> FAILURES P"
by(drule_tac X="{}" in is_process5_S1, auto)

lemma is_process5_singT: 
"\<lbrakk> is_process P ; (s,{x}) \<notin> FAILURES P;(s,{}) \<in> FAILURES P\<rbrakk>  \<Longrightarrow> s @ [x]  \<in> TRACES P"
apply(drule is_process5_sing, auto)
by(simp add: TRACES_def, auto)


lemma front_trace_is_tickfree:
assumes A: "is_process P" and B: "(t @ [tick],X) \<in> FAILURES P"
shows     "tickFree t"
proof -
  have C: "front_tickFree(t @ [tick])" by(insert A B, drule is_process2, metis) 
  show ?thesis  by(rule front_tickFree_implies_tickFree[OF C])   
qed


lemma trace_with_Tick_implies_tickFree_front : "\<lbrakk>is_process P; t @ [tick] \<in> TRACES P\<rbrakk> \<Longrightarrow> tickFree t"
by(auto simp: TRACES_def intro: front_trace_is_tickfree)


subsection \<open> The Abstraction to the process-Type \<close>

typedef 
  '\<alpha> process = "{p :: '\<alpha> process\<^sub>0 . is_process p}"
proof - 
   have "({(s, X). s = []},{}) \<in> {p::'\<alpha> process\<^sub>0. is_process p}"
        by(simp add: is_process_def  front_tickFree_def
                     FAILURES_def TRACES_def DIVERGENCES_def )
   thus ?thesis by auto
qed

definition F :: "'\<alpha> process \<Rightarrow>  ('\<alpha> failure set)"
  where   "F P = FAILURES (Rep_process P)"

definition T :: "'\<alpha> process \<Rightarrow>  ('\<alpha> trace set)"
  where   "T P = TRACES (Rep_process P)"

definition D :: "'\<alpha> process \<Rightarrow> '\<alpha> divergence"
  where   "D P = DIVERGENCES (Rep_process P)"

definition R :: "'\<alpha> process \<Rightarrow> ('\<alpha> refusal set)"
  where   "R P = REFUSALS (Rep_process P)"


lemma is_process_Rep : "is_process (Rep_process P)"
by(rule_tac P=is_process in CollectD, rule Rep_process)

lemma Process_spec: "Abs_process((F P , D P)) = P"
by(simp add: F_def FAILURES_def D_def 
             DIVERGENCES_def Rep_process_inverse)

lemma Process_eq_spec: "(P = Q)=(F P = F Q \<and> D P = D Q)"
apply(rule iffI,simp)
apply(rule_tac t=P in Process_spec[THEN subst])
apply(rule_tac t=Q in Process_spec[THEN subst])
apply simp
  done

lemma Process_eq_spec_optimized: "(P = Q) = (D P = D Q \<and> (D P = D Q \<longrightarrow> F P = F Q))"
  using Process_eq_spec by auto

lemma is_processT:
"([],{}) \<in> F P \<and>
 (\<forall> s X. (s,X) \<in> F P \<longrightarrow> front_tickFree s) \<and>
 (\<forall> s t .(s@t,{}) \<in> F P \<longrightarrow> (s,{}) \<in> F P) \<and>
 (\<forall> s X Y.(s,Y) \<in> F P \<and> (X\<subseteq>Y) \<longrightarrow> (s,X) \<in> F P) \<and>
 (\<forall> s X Y.(s,X) \<in> F P \<and> (\<forall>c. c \<in> Y \<longrightarrow>((s@[c],{})\<notin>F P)) \<longrightarrow> (s,X \<union> Y) \<in> F P) \<and>
 (\<forall> s X. (s@[tick],{}) \<in> F P \<longrightarrow> (s, X-{tick}) \<in> F P) \<and>
 (\<forall> s t. s \<in> D P \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> D P) \<and>
 (\<forall> s X. s \<in> D P \<longrightarrow> (s,X) \<in> F P) \<and>
 (\<forall> s. s@[tick] \<in> D P \<longrightarrow> s \<in> D P)"
apply(simp only: F_def D_def T_def)
apply(rule is_process_def[THEN iffD1])
apply(rule is_process_Rep)
done

lemma process_charn:
  "([], {}) \<in> F P \<and>
   (\<forall>s X. (s, X) \<in> F P \<longrightarrow> front_tickFree s) \<and>
   (\<forall>s t. (s @ t, {}) \<notin> F P \<or> (s, {}) \<in> F P) \<and>
   (\<forall>s X Y. (s, Y) \<notin> F P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> F P) \<and>
   (\<forall>s X Y. (s, X) \<in> F P \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> F P) \<longrightarrow>
             (s, X \<union> Y) \<in> F P) \<and>
   (\<forall>s X. (s @ [tick], {}) \<in> F P \<longrightarrow> (s, X - {tick}) \<in> F P) \<and>
   (\<forall>s t. s \<notin> D P \<or> \<not> tickFree s \<or> \<not> front_tickFree t \<or> s @ t \<in> D P) \<and>
   (\<forall>s X. s \<notin> D P \<or> (s, X) \<in> F P) \<and> (\<forall>s. s @ [tick] \<notin> D P \<or> s \<in> D P)"
proof -
  {
    have A: "(\<forall>s t. (s @ t, {}) \<notin> F P \<or>  (s, {}) \<in> F P) = 
      (\<forall>s t. (s @ t, {}) \<in> F P \<longrightarrow> (s, {}) \<in> F P)"
      by metis

    have B : "(\<forall>s X Y. (s, Y) \<notin> F P \<or> \<not> X \<subseteq> Y \<or> (s, X) \<in> F P)  =
      (\<forall>s X Y. (s, Y) \<in> F P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> F P) "
      by metis

    have C : "(\<forall>s t. s \<notin> D P \<or> \<not> tickFree s \<or> 
      \<not> front_tickFree t \<or> s @ t \<in> D P)  =
      (\<forall>s t. s \<in> D P \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> D P) "
      by metis

    have D:"(\<forall>s X. s \<notin> D P \<or> (s, X) \<in> F P) = (\<forall>s X. s \<in> D P \<longrightarrow> (s, X) \<in> F P)"
      by metis

    have E:"(\<forall>s. s @ [tick] \<notin> D P \<or> s \<in> D P) = 
      (\<forall>s. s @ [tick] \<in> D P \<longrightarrow> s \<in> D P)"
      by metis

    note A B C D E 
  }
  note a = this
  then
  show ?thesis
    apply(simp only: a)
    apply(rule is_processT)
    done
qed


text\<open> split of \verb+is_processT+: \<close>

lemma is_processT1: "([],{}) \<in> F P"
by(simp add:process_charn)

lemma is_processT2: "\<forall>s X. (s, X) \<in> F P \<longrightarrow> front_tickFree s"
by(simp add:process_charn)

lemma  is_processT2_TR : "\<forall>s. s \<in> T P \<longrightarrow> front_tickFree s"
apply(simp add: F_def [symmetric] T_def TRACES_def, safe)
apply (drule is_processT2[rule_format], assumption)
done

lemma is_proT2:
  assumes A : " (s, X) \<in> F P" and B : " s \<noteq> []"
  shows   "tick \<notin> set (tl (rev s))"
proof -
  have C: "front_tickFree s" by(insert A B, simp add: is_processT2)
  show ?thesis
  by(insert C,simp add: B  tickFree_def front_tickFree_def) 
qed

lemma is_processT3 : "\<forall>s t. (s @ t, {}) \<in> F P \<longrightarrow> (s, {}) \<in> F P"
by(simp only: process_charn  HOL.nnf_simps(3), simp)

lemma is_processT3_S_pref : 
"\<lbrakk>(t, {}) \<in> F P; s \<le> t\<rbrakk> \<Longrightarrow> (s, {}) \<in> F P"
apply(simp only: le_list_def, safe)
apply(erule is_processT3[rule_format])
done

lemma  is_processT4 : "\<forall>s X Y. (s, Y) \<in> F P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> F P"
by(insert  process_charn [of P], metis)

lemma is_processT4_S1 : "\<lbrakk>x \<in> F P; X \<subseteq> snd x\<rbrakk> \<Longrightarrow> (fst x, X) \<in> F P"
apply(rule_tac Y = "snd x" in is_processT4[rule_format])
apply simp
done

lemma is_processT5: "\<forall>s X Y.(s,X) \<in> F P \<and> (\<forall>c. c\<in>Y \<longrightarrow> (s@[c],{}) \<notin> F P) \<longrightarrow> (s,X\<union>Y)\<in>F P "
by(simp add: process_charn)

lemma is_processT5_S1: "\<lbrakk>(s, X) \<in> F P; (s, X \<union> Y) \<notin> F P\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> Y \<and> (s @ [c], {}) \<in> F P"
by(erule contrapos_np, simp add: is_processT5[rule_format])

lemma is_processT5_S2: "\<lbrakk>(s, X) \<in> F P; (s @ [c], {}) \<notin> F P\<rbrakk> \<Longrightarrow> (s, X \<union> {c}) \<in> F P"
by(rule is_processT5[rule_format,OF conjI], metis, safe)


lemma is_processT5_S2a: "\<lbrakk>(s, X) \<in> F P; (s, X \<union> {c}) \<notin> F P\<rbrakk> \<Longrightarrow> (s @ [c], {}) \<in> F P"
apply(erule contrapos_np)
apply(rule is_processT5_S2)
apply(simp_all)
done

lemma  is_processT5_S3:
assumes A: "(s, {}) \<in> F P"
and     B: "(s @ [c], {}) \<notin> F P"
shows      "(s, {c}) \<in> F P"
proof -
   have C : " {c} = ({} Un {c})" by simp
   show ?thesis
   by(subst C, rule is_processT5_S2, simp_all add: A B)
qed
   
lemma is_processT5_S4: "\<lbrakk>(s, {}) \<in> F P; (s, {c}) \<notin> F P\<rbrakk> \<Longrightarrow> (s @ [c], {}) \<in> F P"
by(erule contrapos_np, simp add: is_processT5_S3)


lemma is_processT5_S5:
"\<lbrakk>(s, X) \<in> F P; \<forall>c. c \<in> Y \<longrightarrow> (s, X \<union> {c}) \<notin> F P\<rbrakk> \<Longrightarrow> \<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<in> F P"
by(erule_tac Q = "\<forall>c. c \<in> Y \<longrightarrow> (s, X \<union> {c}) \<notin> F P" in contrapos_pp, metis is_processT5_S2) 

lemma is_processT5_S6: "([], {c}) \<notin> F P \<Longrightarrow> ([c], {}) \<in> F P"
apply(rule_tac t="[c]" and s="[]@[c]" in subst, simp)
apply(rule is_processT5_S4, simp_all add: is_processT1)
done

lemma is_processT6: "\<forall>s X. (s @ [tick], {}) \<in> F P \<longrightarrow> (s, X - {tick}) \<in> F P"
by(simp add: process_charn)


lemma is_processT7:  "\<forall>s t. s \<in> D P \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> D P"
by(insert process_charn[of P], metis)

lemmas is_processT7_S =  is_processT7[rule_format,OF conjI[THEN conjI, THEN  conj_commute[THEN iffD1]]]

lemma is_processT8: "\<forall>s X. s \<in> D P \<longrightarrow> (s, X) \<in> F P "
by(insert process_charn[of P], metis)

lemmas is_processT8_S = is_processT8[rule_format]

lemma is_processT8_Pair: "fst s \<in> D P \<Longrightarrow> s \<in> F P"
apply(subst surjective_pairing)
apply(rule is_processT8_S, simp)
done

lemma is_processT9: "\<forall>s. s @ [tick] \<in> D P \<longrightarrow> s \<in> D P"
by(insert process_charn[of P], metis)

lemma is_processT9_S_swap: "s \<notin> D P \<Longrightarrow> s @ [tick] \<notin> D P"
by(erule contrapos_nn,simp add: is_processT9[rule_format])


subsection\<open> Some Consequences of the Process Characterization\<close>

lemma no_Trace_implies_no_Failure: "s \<notin> T P \<Longrightarrow> (s, {}) \<notin> F P"
by(simp add: T_def TRACES_def F_def)

lemmas  NT_NF = no_Trace_implies_no_Failure

lemma T_def_spec: "T P = {tr. \<exists>a. a \<in> F P \<and> tr = fst a}"
by(simp add: T_def TRACES_def F_def)

lemma F_T: "(s, X) \<in> F P \<Longrightarrow> s \<in> T P"
by(simp add: T_def_spec split_def, metis)

lemma F_T1: "a \<in> F P \<Longrightarrow> fst a \<in> T P"
by(rule_tac X="snd a" in F_T,simp)


lemma T_F: "s \<in> T P \<Longrightarrow> (s, {}) \<in> F P"
apply(auto simp: T_def_spec)
apply(drule is_processT4_S1, simp_all)
done

lemmas is_processT4_empty [elim!]= F_T [THEN T_F]

lemma NF_NT: "(s, {}) \<notin> F P \<Longrightarrow> s \<notin> T P"
  by(erule contrapos_nn, simp only: T_F)

lemma  is_processT6_S1: "\<lbrakk> tick \<notin> X;(s @ [tick], {}) \<in> F P \<rbrakk> \<Longrightarrow> (s::'a event list, X) \<in> F P"
by(subst Diff_triv[of X "{tick}", symmetric],
   simp, erule is_processT6[rule_format])

lemmas is_processT3_ST = T_F [THEN is_processT3[rule_format,THEN F_T]]

lemmas is_processT3_ST_pref = T_F [THEN is_processT3_S_pref [THEN F_T]]

lemmas is_processT3_SR = F_T [THEN T_F [THEN is_processT3[rule_format]]]

lemmas D_T = is_processT8_S [THEN F_T]

lemma D_T_subset : "D P \<subseteq> T P" by(auto intro!:D_T)

lemma NF_ND : "(s, X) \<notin> F P \<Longrightarrow> s \<notin> D P"
by(erule contrapos_nn, simp add: is_processT8_S)

lemmas NT_ND = D_T_subset[THEN Set.contra_subsetD]

lemma T_F_spec : "((t, {}) \<in> F P) = (t \<in> T P)"
by(auto simp:T_F F_T)

lemma is_processT5_S7:  " \<lbrakk>t \<in> T P; (t, A) \<notin> F P\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> A \<and> t @ [x] \<in> T P"
apply(erule contrapos_np, simp)
apply(rule is_processT5[rule_format, OF conjI,of _ "{}", simplified])
apply(auto simp: T_F_spec)
  done

lemma is_processT5_S7': " \<lbrakk>(t, X) \<in> F P; (t, X \<union> A) \<notin> F P\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<notin> X \<and> t @ [x] \<in> T P"
  apply(erule contrapos_np, simp, subst Un_Diff_cancel[of X A, symmetric])
  apply(rule is_processT5[rule_format])  
  apply(auto simp: T_F_spec)
  done

lemma Nil_subset_T: " {[]} \<subseteq> T P"
by(auto simp: T_F_spec[symmetric] is_processT1)

lemma Nil_elem_T: "[] \<in> T P"
by(simp add: Nil_subset_T[THEN subsetD])

lemmas D_imp_front_tickFree = is_processT8_S[THEN is_processT2[rule_format]]

lemma D_front_tickFree_subset : "D P \<subseteq> Collect front_tickFree"
by(auto simp: D_imp_front_tickFree)

lemma F_D_part : "F P = {(s, x). s \<in> D P} \<union> {(s, x). s \<notin> D P \<and> (s, x) \<in> F P}"
by(auto intro:is_processT8_Pair)

lemma D_F : "{(s, x). s \<in> D P} \<subseteq> F P"
by(auto intro:is_processT8_Pair)

lemma append_T_imp_tickFree:  "\<lbrakk>t @ s \<in> T P; s \<noteq> []\<rbrakk> \<Longrightarrow> tickFree t"
by(frule is_processT2_TR[rule_format], 
   simp add: front_tickFree_def tickFree_rev)

corollary append_single_T_imp_tickFree : "t @ [a] \<in> T P \<Longrightarrow> tickFree t"
  by (simp add: append_T_imp_tickFree)

lemma F_subset_imp_T_subset: "F P \<subseteq> F Q \<Longrightarrow> T P \<subseteq> T Q"
by(auto simp: subsetD T_F_spec[symmetric])

lemma is_processT6_S2: "\<lbrakk>tick \<notin> X; [tick] \<in> T P\<rbrakk> \<Longrightarrow> ([], X) \<in> F P"
by(erule is_processT6_S1, simp add: T_F_spec) 

lemma is_processT9_tick: "\<lbrakk>[tick] \<in> D P; front_tickFree s\<rbrakk> \<Longrightarrow> s \<in> D P"
apply(rule append.simps(1) [THEN subst, of _ s])
apply(rule is_processT7_S, simp_all)
apply(rule is_processT9 [rule_format], simp)
done


lemma T_nonTickFree_imp_decomp: "\<lbrakk>t \<in> T P; \<not> tickFree t\<rbrakk> \<Longrightarrow> \<exists>s. t = s @ [tick]"
by(auto elim: is_processT2_TR[rule_format] nonTickFree_n_frontTickFree)


subsection\<open> Process Approximation is a Partial Ordering, a Cpo, and a Pcpo \<close>
text\<open>The Failure/Divergence Model of CSP Semantics provides two orderings:
The \emph{approximation ordering} (also called \emph{process ordering})
will be used for giving semantics to recursion (fixpoints) over processes,
the \emph{refinement ordering} captures our intuition that a more concrete
process is more deterministic and more defined than an abstract one.

We start with the key-concepts of the approximation ordering, namely
the predicates $min\_elems$ and $Ra$ (abbreviating \emph{refusals after}).
The former provides just a set of minimal elements from a given set
of elements of type-class $ord$ \ldots \<close>

definition min_elems :: "('s::ord) set \<Rightarrow> 's set"
  where   "min_elems X = {s \<in> X. \<forall>t. t \<in> X \<longrightarrow> \<not> (t < s)}"

lemma Nil_min_elems : "[] \<in> A \<Longrightarrow> [] \<in> min_elems A"
by(simp add: min_elems_def)

lemma min_elems_le_self[simp] : "(min_elems A) \<subseteq> A"
by(auto simp: min_elems_def)

lemmas elem_min_elems = Set.set_mp[OF min_elems_le_self]

lemma min_elems_Collect_ftF_is_Nil : "min_elems (Collect front_tickFree) = {[]}"
apply(auto simp: min_elems_def le_list_def)
apply(drule front_tickFree_charn[THEN iffD1])
apply(auto dest!: tickFree_implies_front_tickFree)
done

lemma min_elems5 : 
  assumes A: "(x::'a list) \<in> A"
  shows      "\<exists>s\<le>x. s \<in> min_elems A"
proof -
   have * : "!! (x::'a list) (A::'a list set) (n::nat).
                x \<in> A \<and> length x \<le> n \<longrightarrow> (\<exists>s\<le>x. s \<in> min_elems A)"
            apply(rule_tac x=x in spec)
            apply(rule_tac n=n in nat_induct) (* quirk in induct *)
            apply(auto simp: Nil_min_elems)
            apply(case_tac "\<exists> y.  y \<in> A \<and> y < x",auto)
            apply(rename_tac A na x y, erule_tac x=y in allE, simp)
            apply(erule impE,drule less_length_mono, arith)
            apply(safe, rename_tac s, rule_tac x=s in exI,simp)
            apply(rule_tac x=x in exI, simp add:min_elems_def)
            done
   show ?thesis by(rule_tac n="length x" in *[rule_format],simp add:A)
qed

lemma min_elems4: "A \<noteq> {} \<Longrightarrow> \<exists>s. (s :: 'a trace) \<in> min_elems A"
by(auto dest: min_elems5)

lemma min_elems_charn: "t \<in> A \<Longrightarrow> \<exists> t' r. t = (t' @ r) \<and> t' \<in> min_elems A"
by(drule min_elems5[simplified le_list_def], auto)

lemmas min_elems_ex = min_elems_charn  (* Legacy *)

lemma min_elems_no: "(x::'a list) \<in> min_elems A \<Longrightarrow> t \<in> A \<Longrightarrow> t \<le> x \<Longrightarrow> x = t" 
  by (metis (no_types, lifting) less_list_def mem_Collect_eq min_elems_def)

text\<open> \ldots while the second returns the set of possible
refusal sets after a given trace $s$ and a given process
$P$: \<close>

definition Ra :: "['\<alpha> process, '\<alpha> trace] \<Rightarrow> ('\<alpha> refusal set)"
  where   "Ra P s = {X. (s, X) \<in> F P}"

text\<open> In the following, we link the process theory to the underlying 
fixpoint/domain theory of HOLCF by identifying the approximation ordering 
with HOLCF's pcpo's. \<close>

instantiation 
   process  ::  ("type") below     
begin
text\<open> declares approximation ordering $\_ \sqsubseteq \_$ also written 
        \verb+_ << _+. \<close>

definition le_approx_def : "P \<sqsubseteq> Q \<equiv> D Q \<subseteq> D P \<and>
                                    (\<forall>s. s \<notin> D P \<longrightarrow> Ra P s = Ra Q s) \<and> 
                                     min_elems (D P) \<subseteq> T Q"

text\<open> The approximation ordering captures the fact that more concrete
processes should be more defined by ordering the divergence sets
appropriately. For defined positions in a process, the failure
sets must coincide pointwise; moreover, the minimal elements
(wrt.~prefix ordering on traces, i.e.~lists) must be contained in
the trace set of the more concrete process.\<close>

instance ..

end


lemma le_approx1: "P\<sqsubseteq>Q \<Longrightarrow> D Q \<subseteq> D P"
by(simp add: le_approx_def)


lemma le_approx2: "\<lbrakk> P\<sqsubseteq>Q; s \<notin> D P\<rbrakk> \<Longrightarrow> (s,X) \<in> F Q = ((s,X) \<in> F P)" 
by(auto simp: Ra_def le_approx_def)


lemma le_approx3: "P \<sqsubseteq> Q \<Longrightarrow> min_elems(D P) \<subseteq> T Q"
by(simp add: le_approx_def)

lemma le_approx2T: "\<lbrakk> P\<sqsubseteq>Q; s \<notin> D P\<rbrakk> \<Longrightarrow>  s \<in> T Q = (s \<in> T P)" 
by(auto simp: le_approx2 T_F_spec[symmetric])

lemma le_approx_lemma_F : "P\<sqsubseteq>Q \<Longrightarrow> F Q \<subseteq> F P"
apply(subst F_D_part[of Q], subst F_D_part[of P])
apply(auto simp:le_approx_def Ra_def min_elems_def)
done

lemmas order_lemma = le_approx_lemma_F

lemma le_approx_lemma_T: "P\<sqsubseteq>Q \<Longrightarrow> T Q \<subseteq> T P"
by(auto dest!:le_approx_lemma_F simp: T_F_spec[symmetric])

lemma proc_ord2a :  "\<lbrakk>P \<sqsubseteq> Q; s \<notin> D P\<rbrakk> \<Longrightarrow> ((s, X) \<in> F P) = ((s, X) \<in> F Q)"
by(auto simp: le_approx_def Ra_def)


instance
   process :: ("type") po
proof
   fix P::"'\<alpha> process"
   show "P \<sqsubseteq> P" by(auto simp: le_approx_def min_elems_def elim: Process.D_T)
 next
   fix P Q ::"'\<alpha> process" 
   assume A:"P \<sqsubseteq> Q" and B:"Q \<sqsubseteq> P" thus "P = Q"
   apply(insert A[THEN le_approx1] B[THEN le_approx1])
   apply(insert A[THEN le_approx_lemma_F] B[THEN le_approx_lemma_F])
   by(auto simp: Process_eq_spec)
 next
   fix P Q R ::"'\<alpha> process" 
   assume A: "P \<sqsubseteq> Q" and B: "Q \<sqsubseteq> R" thus "P \<sqsubseteq> R" 
   proof -
      have C : "D R \<subseteq> D P" 
               by(insert A[THEN le_approx1] B[THEN le_approx1], auto)
      have D : "\<forall> s. s \<notin> D P \<longrightarrow> {X. (s, X) \<in> F P} = {X. (s, X) \<in>  F R}" 
               apply(rule allI, rule impI, rule set_eqI, simp)
               apply(frule A[THEN le_approx1, THEN Set.contra_subsetD])
               apply(frule B[THEN le_approx1, THEN Set.contra_subsetD])
               apply(drule A[THEN le_approx2], drule B[THEN le_approx2]) 
               apply auto
               done
      have E : "min_elems (D P) \<subseteq> T R"
               apply(insert B[THEN le_approx3] A[THEN le_approx3] )
               apply(insert B[THEN le_approx_lemma_T] A[THEN le_approx1] ) 
               apply(rule subsetI, simp add: min_elems_def, auto)
               apply(rename_tac x, case_tac "x \<in> D Q")
               apply(drule_tac B = "T R" and t=x 
                     in subset_iff[THEN iffD1,rule_format], auto)
               apply(subst B [THEN le_approx2T],simp)
               apply(rename_tac x, drule_tac B = "T Q" and t=x 
                     in subset_iff[THEN iffD1,rule_format],auto)
               done
      show ?thesis
      by(insert C D E, simp add: le_approx_def Ra_def)
   qed
qed

text\<open> At this point, we inherit quite a number of facts from the underlying
HOLCF theory, which comprises a library of facts such as \verb+chain+,
\verb+directed+(sets), upper bounds and least upper bounds, etc. \<close>


text\<open>
Some facts from the theory of complete partial orders:
\begin{itemize}
\item \verb+Porder.chainE+ : @{thm "Porder.chainE"}
\item \verb+Porder.chain_mono+ : @{thm "Porder.chain_mono"}
\item \verb+Porder.is_ubD+ : @{thm "Porder.is_ubD"}
\item \verb+Porder.ub_rangeI+ : \\ @{thm "Porder.ub_rangeI"}
\item \verb+Porder.ub_imageD+ : @{thm "Porder.ub_imageD"}
\item \verb+Porder.is_ub_upward+ : @{thm "Porder.is_ub_upward"}
\item \verb+Porder.is_lubD1+ : @{thm "Porder.is_lubD1"}
\item \verb+Porder.is_lubI+ : @{thm "Porder.is_lubI"}
\item \verb+Porder.is_lub_maximal+ : @{thm "Porder.is_lub_maximal"}
\item \verb+Porder.is_lub_lub+ : @{thm "Porder.is_lub_lub"}
\item \verb+Porder.is_lub_range_shift+: \\ @{thm "Porder.is_lub_range_shift"}
\item \verb+Porder.is_lub_rangeD1+: @{thm "Porder.is_lub_rangeD1"}
\item \verb+Porder.lub_eqI+: @{thm "Porder.lub_eqI"}
\item \verb+Porder.is_lub_unique+:@{thm "Porder.is_lub_unique"}
\end{itemize}
\<close>


definition lim_proc :: "('\<alpha> process) set \<Rightarrow> '\<alpha> process"
  where   "lim_proc (X) = Abs_process (\<Inter> (F ` X), \<Inter> (D ` X))"

lemma min_elems3: "\<lbrakk>s @ [c] \<in> D P; s @ [c] \<notin> min_elems (D P)\<rbrakk> \<Longrightarrow> s \<in> D P"
apply(auto simp: min_elems_def le_list_def less_list_def)
apply(rename_tac t r) 
apply(subgoal_tac "t \<le> s")
apply(subgoal_tac "r \<noteq> []")
apply(simp add: le_list_def)
apply(auto intro!: is_processT7_S append_eq_first_pref_spec)
apply(auto dest!: D_T)
apply(simp_all only: append_assoc[symmetric],
      drule append_T_imp_tickFree,
      simp_all add: tickFree_implies_front_tickFree)+
done

lemma min_elems1: "\<lbrakk>s \<notin> D P; s @ [c] \<in> D P\<rbrakk> \<Longrightarrow> s @ [c] \<in> min_elems (D P)"
  by(erule contrapos_np, auto elim!: min_elems3)

lemma min_elems2: "\<lbrakk>s \<notin> D P; s @ [c] \<in> D P; P \<sqsubseteq> S; Q \<sqsubseteq> S\<rbrakk> \<Longrightarrow> (s @ [c], {}) \<in> F Q"
  apply(frule_tac P=Q and Q=S in le_approx_lemma_T)
  apply(simp add: T_F_spec)
  apply(rule_tac A="T S" in subsetD, assumption)
  apply(rule_tac A="min_elems(D P)" in subsetD) 
  apply(simp_all add: le_approx_def min_elems1)
done

lemma min_elems6: "\<lbrakk>s \<notin> D P; s @ [c] \<in> D P; P \<sqsubseteq> S\<rbrakk> \<Longrightarrow> (s @ [c], {}) \<in> F S"
by(auto intro!: min_elems2)

lemma ND_F_dir2: "\<lbrakk>s \<notin> D P; (s, {}) \<in> F P; P \<sqsubseteq> S; Q \<sqsubseteq> S\<rbrakk> \<Longrightarrow> (s, {}) \<in> F Q"
  apply(frule_tac P=Q and Q=S in le_approx_lemma_T)
  apply(simp add: le_approx_def Ra_def T_F_spec, safe)
  apply((erule_tac x=s in allE)+,simp)
  apply(drule_tac x="{}" in eqset_imp_iff, auto simp: T_F_spec)
done \<comment>\<open>orig version\<close>

lemma ND_F_dir2': "\<lbrakk>s \<notin> D P; s \<in> T P; P \<sqsubseteq> S; Q \<sqsubseteq> S\<rbrakk> \<Longrightarrow> s \<in> T Q"
  apply(frule_tac P=Q and Q=S in le_approx_lemma_T)
  apply(simp add: le_approx_def Ra_def T_F_spec, safe)
  apply((erule_tac x=s in allE)+,simp)
  apply(drule_tac x="{}" in eqset_imp_iff, auto simp: T_F_spec)
done


lemma chain_lemma: "\<lbrakk>chain S\<rbrakk> \<Longrightarrow> S i \<sqsubseteq> S k \<or> S k \<sqsubseteq> S i"
by(case_tac "i \<le> k", auto intro:chain_mono chain_mono_less)
 

lemma is_process_REP_LUB: 
  assumes chain: "chain S"
  shows "is_process (\<Inter> (F ` range S), \<Inter> (D ` range S))"

proof (auto simp: is_process_def)
   show   "([], {}) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp: FAILURES_def is_processT)
next
   fix s::"'a trace" fix X::"'a event set"
   assume A : "(s, X) \<in> (FAILURES (\<Inter> a :: nat. F (S a), \<Inter> a :: nat. D (S a)))" 
   thus   "front_tickFree s"
          by(auto simp:   DIVERGENCES_def FAILURES_def
                  intro!: is_processT2[rule_format])
next
   fix s  t::"'a trace"
   assume " (s @ t, {}) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a)) "
   thus "(s, {}) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp:  DIVERGENCES_def FAILURES_def
                  intro: is_processT3[rule_format])
next
   fix s::"'a trace"   fix X Y ::"'a event set"
   assume "(s, Y) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))" and "X \<subseteq> Y"
   thus   "(s, X) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp:  DIVERGENCES_def FAILURES_def
                  intro: is_processT4[rule_format])
next
   fix s::"'a trace"   fix X Y ::" 'a event set"
   assume A:"(s, X) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
   assume B:"\<forall> c. c\<in>Y \<longrightarrow> (s@[c],{})\<notin>FAILURES(\<Inter> a::nat. F(S a),\<Inter> a::nat. D(S a))"
   thus   "(s, X \<union> Y) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
   txt\<open> What does this mean: All trace prolongations $c$ in all $Y$, 
         which are blocking in the limit, will also occur in the refusal set 
         of the limit. \<close>
   using A B chain
   proof (auto simp: DIVERGENCES_def FAILURES_def,
          case_tac "\<forall> x. x \<in> (range S) \<longrightarrow> (s, X \<union> Y) \<in> F x",
          simp_all add:DIVERGENCES_def FAILURES_def,rename_tac a,
          case_tac "s \<notin> D (S a)",simp_all add: is_processT8)
      fix a::nat 
      assume X: "\<forall>a. (s, X) \<in> F (S a)"
                 have X_ref_at_a: "(s, X) \<in> F (S a)"
                 using X by auto
      assume Y: "\<forall>c. c \<in> Y \<longrightarrow> (\<exists>a. (s @ [c], {}) \<notin> F (S a))"
      assume defined: "s \<notin> D (S a)"
      show   "(s::'a trace, X \<union> Y) \<in> F (S a)"
      proof(auto simp:X_ref_at_a
                 intro!: is_processT5[rule_format],
            frule Y[THEN spec, THEN mp], erule exE,
            erule_tac Q="(s @ [c], {}) \<in> F (S a)" in contrapos_pp)
         fix c::"'a event" fix a' :: nat
         assume s_c_trace_not_trace_somewhere: "(s @ [c], {}) \<notin> F (S a')"
         show "(s @ [c], {}) \<notin> F (S a)"
         proof(insert chain_lemma[OF chain, of "a" "a'"],erule disjE)
           assume before: "S a \<sqsubseteq> S a'"
           show "(s @ [c], {}) \<notin> F (S a)"
             using s_c_trace_not_trace_somewhere  before
             apply(case_tac "s @ [c] \<notin> D (S a)",
                   simp_all add: T_F_spec before[THEN le_approx2T,symmetric])
             apply(erule contrapos_nn)
             apply(simp only: T_F_spec[symmetric])
             apply(auto dest!:min_elems6[OF defined])
             done
         next
           assume after:"S a' \<sqsubseteq> S a"
           show "(s @ [c], {}) \<notin> F (S a)"
             using s_c_trace_not_trace_somewhere
             by(simp add:T_F_spec after[THEN le_approx2T]
                         s_c_trace_not_trace_somewhere[THEN NF_ND])
         qed
      qed
   qed
next
   fix s::"'a trace"   fix X::"'a event set"
   assume "(s @ [tick], {}) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
   thus   "(s, X - {tick}) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp: DIVERGENCES_def FAILURES_def
                  intro! : is_processT6[rule_format])
next
   fix s t ::"'a trace"
   assume "s : DIVERGENCES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
   and    "tickFree s" and " front_tickFree t"
   thus   "s @ t \<in> DIVERGENCES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp: DIVERGENCES_def FAILURES_def
                  intro: is_processT7[rule_format])
next
   fix s::"'a trace"  fix X::"'a event set"
   assume "s \<in> DIVERGENCES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a)) "
   thus   "(s, X) \<in> FAILURES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp: DIVERGENCES_def FAILURES_def
                       intro: is_processT8[rule_format])
next
   fix s::"'a trace"
   assume "s @ [tick] \<in> DIVERGENCES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a)) "
   thus   "s \<in> DIVERGENCES (\<Inter> a::nat. F (S a), \<Inter> a::nat. D (S a))"
          by(auto simp: DIVERGENCES_def FAILURES_def
                  intro: is_processT9[rule_format])
qed



lemmas Rep_Abs_LUB = Abs_process_inverse[simplified Rep_process, 
                                         simplified, OF is_process_REP_LUB,
                                         simplified]

lemma F_LUB: "chain S \<Longrightarrow> F(lim_proc(range S)) = \<Inter> (F ` range S)"
by(simp add: lim_proc_def , subst F_def, auto simp: FAILURES_def Rep_Abs_LUB)

lemma D_LUB: "chain S \<Longrightarrow> D(lim_proc(range S)) = \<Inter> (D ` range S)"
by(simp add: lim_proc_def , subst D_def, auto simp: DIVERGENCES_def Rep_Abs_LUB)

lemma T_LUB: "chain S \<Longrightarrow> T(lim_proc(range S)) = \<Inter> (T ` range S)"
apply(simp add: lim_proc_def , subst T_def) 
apply(simp add: TRACES_def FAILURES_def Rep_Abs_LUB)
apply(auto intro: F_T, rule_tac x="{}" in exI, auto intro: T_F)
done

schematic_goal D_LUB_2: "chain S \<Longrightarrow> t \<in> D(lim_proc(range S)) =  ?X"
apply(subst D_LUB, simp)
apply(rule trans, simp)
apply(simp)
done

schematic_goal T_LUB_2: "chain S \<Longrightarrow> (t \<in> T (lim_proc (range S))) = ?X"
apply(subst T_LUB, simp)
apply(rule trans, simp)
apply(simp)
done


subsection\<open> Process Refinement is a Partial Ordering\<close>

text\<open> The following type instantiation declares the refinement order
$\_ \le \_ $ written \verb+_  <= _+. It captures the intuition that more
concrete processes should be more deterministic and more defined.\<close>

instantiation
   process :: (type) ord          
begin

definition  le_ref_def   : "P \<le> Q \<equiv> D Q \<subseteq> D P \<and> F Q \<subseteq> F P"

definition  less_ref_def : "(P::'a process) < Q \<equiv> P \<le> Q \<and> P \<noteq> Q"

instance ..

end

lemma le_approx_implies_le_ref:    "(P::'\<alpha> process) \<sqsubseteq> Q \<Longrightarrow> P \<le> Q"
by(simp add: le_ref_def le_approx1 le_approx_lemma_F)

lemma le_ref1:                     "P \<le> Q \<Longrightarrow> D Q \<subseteq> D P"
by(simp add: le_ref_def) 


lemma le_ref2:                     "P\<le>Q \<Longrightarrow> F Q \<subseteq> F P"
by(simp add: le_ref_def) 

lemma le_ref2T :                    "P\<le>Q \<Longrightarrow> T Q \<subseteq> T P"
  by (rule subsetI) (simp add: T_F_spec[symmetric] le_ref2[THEN subsetD])


instance  process :: (type) order
proof
   fix P Q R :: "'\<alpha> process"
   {
     show "(P < Q) = (P \<le> Q \<and> \<not> Q \<le>  P)"
       by(auto simp: le_ref_def less_ref_def Process_eq_spec)
   next
     show "P \<le> P"  by(simp add: le_ref_def)
   next
     assume "P \<le> Q" and "Q \<le> R" then show "P \<le> R"
       by (simp add: le_ref_def, auto)
   next
     assume "P \<le> Q" and "Q \<le> P" then show "P = Q"
       by(auto simp: le_ref_def Process_eq_spec)  
   }
qed

lemma lim_proc_is_ub:"chain S \<Longrightarrow> range S <| lim_proc (range S)" 
  apply(auto simp: is_ub_def le_approx_def F_LUB D_LUB T_LUB Ra_def) 
  using chain_lemma is_processT8 le_approx2 apply blast 
  using D_T chain_lemma le_approx2T le_approx_def by blast

lemma lim_proc_is_lub1: "chain S \<Longrightarrow> \<forall> u . (range S <| u \<longrightarrow>  D u \<subseteq> D (lim_proc (range S)))"
  by(auto simp: D_LUB, frule_tac i=a in Porder.ub_rangeD, auto dest: le_approx1)

lemma lim_proc_is_lub2: 
  "chain S \<Longrightarrow> \<forall> u . range S <| u \<longrightarrow> (\<forall> s.  s \<notin> D (lim_proc (range S))
   \<longrightarrow> Ra (lim_proc (range S)) s = Ra u s)" 
    apply(auto simp: is_ub_def D_LUB F_LUB Ra_def)
    using proc_ord2a apply blast
    using is_processT8_S proc_ord2a by blast


lemma lim_proc_is_lub3a: "front_tickFree s \<Longrightarrow> s \<notin> D P \<longrightarrow> (\<forall>t. t \<in> D P \<longrightarrow> \<not> t < s @ [c])" 
apply(rule impI, erule contrapos_np, auto)
apply(auto simp: le_list_def  less_list_def)
by (metis D_def butlast_append butlast_snoc 
          front_tickFree_mono is_process7 is_process_Rep self_append_conv)


lemma lim_proc_is_lub3b:
assumes 1 : "\<forall>x. x \<in> X \<longrightarrow> (\<forall>xa. xa \<in> D x \<and> (\<forall>t. t \<in> D x \<longrightarrow> \<not> t < xa) \<longrightarrow> xa \<in> T u)"
and     2 : "xa \<in> X"
and     3 : "\<forall>xa. xa \<in> X \<longrightarrow> x \<in> D xa"
and     4 : "\<forall>t. (\<forall>x. x \<in> X \<longrightarrow> t \<in> D x) \<longrightarrow> \<not> t < x"
shows       "x \<in> T u"
proof (cases "\<forall>t. t \<in> D xa \<longrightarrow> \<not> t < x") 
      case True  from \<open>\<forall>t. t \<in> D xa \<longrightarrow> \<not> t < x\<close>  show ?thesis using 1 2 3  by simp
next
      case False from \<open>\<not>(\<forall>t. t \<in> D xa \<longrightarrow> \<not> t < x)\<close> and 3 4
                 have A: "\<exists>y r c. y \<in> X \<and> r \<notin> D y \<and> r \<in> D xa \<and> r @ [c] = x" 
                         by (metis D_imp_front_tickFree front_tickFree_charn 
                                   less_self lim_proc_is_lub3a nil_less 
                                   tickFree_implies_front_tickFree)
           show ?thesis
              apply(insert A) apply(erule exE)+
              using "1" "3" D_imp_front_tickFree lim_proc_is_lub3a by blast
qed

lemma lim_proc_is_lub3c: 
assumes *:"chain S"
and     **:"X = range S"  \<comment>\<open>protection for range - otherwise auto unfolds and gets lost\<close>
shows   "\<forall> u. X <| u \<longrightarrow>  min_elems(D(lim_proc X)) \<subseteq> T u"
proof -
  have B : "D (lim_proc X) = \<Inter> (D ` X)" by(simp add: * ** D_LUB)
  show ?thesis
     apply(auto simp: is_ub_def * **)
     apply(auto simp: B min_elems_def le_approx_def HOL.imp_conjR HOL.all_conj_distrib Ball_def)
      apply(simp add: subset_iff imp_conjL[symmetric])
    apply(rule lim_proc_is_lub3b[of "range S", simplified])
    using "**" B by auto
qed

lemma limproc_is_lub: "chain S \<Longrightarrow> range S <<| lim_proc (range S)"
apply (auto simp: is_lub_def lim_proc_is_ub)
apply (simp add: le_approx_def is_lub_def lim_proc_is_ub)
by (simp add: lim_proc_is_lub1 lim_proc_is_lub2 lim_proc_is_lub3c)

lemma limproc_is_thelub: "chain S \<Longrightarrow> Lub S = lim_proc (range S)"
by (frule limproc_is_lub,frule Porder.po_class.lub_eqI, simp)


instance
   process :: (type) cpo
proof
   fix S ::"nat \<Rightarrow> '\<alpha> process"
   assume C:"chain S" 
   thus "\<exists> x. range S <<| x" using limproc_is_lub by blast
qed

instance
   process :: (type) pcpo
proof
   show "\<exists> x::'a process. \<forall> y::'a process. x \<sqsubseteq> y" 
   proof -
      have is_process_witness : 
           "is_process({(s,X). front_tickFree s},{d. front_tickFree d})"
           apply(auto simp:is_process_def FAILURES_def DIVERGENCES_def)
           apply(auto elim!: tickFree_implies_front_tickFree front_tickFree_dw_closed
                             front_tickFree_append)
           done
      have bot_inverse : 
           "Rep_process(Abs_process({(s, X). front_tickFree s},Collect front_tickFree))=
                          ({(s, X). front_tickFree s}, Collect front_tickFree)"
           by(subst Abs_process_inverse, simp_all add: Rep_process is_process_witness)
      have divergences_frontTickFree:
           "\<And>y x. x \<in> snd (Rep_process y) \<Longrightarrow> front_tickFree x" 
           by(rule D_imp_front_tickFree, simp add: D_def DIVERGENCES_def)
      have failures_frontTickFree:
           "\<And>y s x. (s, x) \<in> fst (Rep_process y) \<Longrightarrow> front_tickFree s"
           by(rule is_processT2[rule_format], 
              simp add: F_def FAILURES_def)
      have minelems_contains_mt:
           "\<And>y x. x \<in> min_elems (Collect front_tickFree) \<Longrightarrow> x = []"
           by(simp add: min_elems_def front_tickFree_charn,safe, 
              auto simp: Nil_elem_T)
      show ?thesis 
      apply(rule_tac x="Abs_process ({(s,X). front_tickFree s},{d. front_tickFree d})" 
            in exI)
      apply(auto simp: le_approx_def bot_inverse Ra_def 
                       F_def D_def FAILURES_def DIVERGENCES_def
                       divergences_frontTickFree failures_frontTickFree)
      apply (metis minelems_contains_mt Nil_elem_T )
      done
   qed
qed


subsection\<open> Process Refinement is admissible \<close>

lemma le_adm[simp]: "cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<le> v x)"
proof(auto simp add:le_ref_def cont2contlubE adm_def, goal_cases)
  case (1 Y x)
  hence "v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)" for i by (simp add: is_ub_thelub monofunE)
  hence "D (v (\<Squnion>i. Y i)) \<subseteq> D (u (Y i))" for i using "1"(4) le_approx1 by blast    
  then show ?case 
    using D_LUB[OF ch2ch_cont[OF 1(1) 1(3)]] limproc_is_thelub[OF ch2ch_cont[OF 1(1) 1(3)]] "1"(5) by force
next
  case (2 Y a b)
  hence "v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)" for i by (simp add: is_ub_thelub monofunE)
  hence "F (v (\<Squnion>i. Y i)) \<subseteq> F (u (Y i))" for i using "2"(4) le_approx_lemma_F by blast   
  then show ?case
    using F_LUB[OF ch2ch_cont[OF 2(1) 2(3)]] limproc_is_thelub[OF ch2ch_cont[OF 2(1) 2(3)]] "2"(5) by force
qed

lemmas le_adm_cont[simp] = le_adm[OF _ cont2mono]

subsection\<open> Conditional statement is cont \<close>
text\<open>The conditional operator of CSP is obtained by a direct shallow embedding. Here we prove it continuous\<close>

lemma if_then_else_cont[simp]: 
  assumes *:"(\<And>x. P x \<Longrightarrow> cont ((f::'c \<Rightarrow> ('a::cpo) \<Rightarrow> 'b process) x))"
  and     **:"(\<And>x. \<not> P x \<Longrightarrow> cont (g x))"
  shows "\<And>x. cont(\<lambda>y. if P x then f x y else g x y)"
  using * ** by (auto simp:cont_def)

end
