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

section\<open> Deterministic Choice Operator Definition \<close>

theory  Det 
imports Process
begin

subsection\<open>Definition\<close>
definition
        det      :: "['\<alpha> process,'\<alpha> process] \<Rightarrow> '\<alpha> process"   (infixl "[+]" 18)
where   "P [+] Q \<equiv> Abs_process(  {(s,X). s = [] \<and> (s,X) \<in> F P \<inter> F Q}
                               \<union> {(s,X). s \<noteq> [] \<and> (s,X) \<in> F P \<union> F Q}
                               \<union> {(s,X). s = [] \<and> s \<in> D P \<union> D Q}
                               \<union> {(s,X). s = [] \<and> tick \<notin> X \<and> [tick] \<in> T P \<union> T Q},
                               D P \<union> D Q)"

notation(xsymbols)
  det (infixl "\<box>" 18)


lemma is_process_REP_D:
"is_process ({(s, X). s = [] \<and> (s, X) \<in> F P \<inter> F Q} \<union>
             {(s, X). s \<noteq> [] \<and> (s, X) \<in> F P \<union> F Q} \<union>
             {(s, X). s = [] \<and> s \<in> D P \<union> D Q} \<union>
             {(s, X). s = [] \<and> tick \<notin> X \<and> [tick] \<in> T P \<union> T Q},
             D P \<union> D Q)"
(is "is_process(?T,?D)")
proof (simp only: fst_conv snd_conv Rep_process is_process_def 
                  DIVERGENCES_def FAILURES_def, intro conjI)
     show "([], {}) \<in> ?T"
          by(simp add: is_processT1)
next
     show "\<forall>s X. (s, X) \<in> ?T \<longrightarrow> front_tickFree s"
          by(auto simp: is_processT2)
next
     show "\<forall>s t.   (s @ t, {}) \<in> ?T \<longrightarrow> (s, {}) \<in> ?T"
          by(auto simp: is_processT1 dest!: is_processT3[rule_format])
next
     show "\<forall>s X Y. (s, Y) \<in> ?T \<and> X \<subseteq> Y  \<longrightarrow>  (s, X) \<in> ?T"
          by(auto dest: is_processT4[rule_format,OF conj_commute[THEN iffD1],OF conjI])
next
     show "\<forall>sa X Y. (sa, X) \<in> ?T \<and> (\<forall>c. c \<in> Y \<longrightarrow> (sa @ [c], {}) \<notin> ?T) \<longrightarrow> (sa, X \<union> Y) \<in> ?T"
          by(auto simp: is_processT5 T_F)
next
     show " \<forall>s X. (s @ [tick], {}) \<in> ?T \<longrightarrow> (s, X - {tick}) \<in> ?T"
          apply((rule allI)+, rule impI, rename_tac s X)
          apply(case_tac "s=[]", simp_all add: is_processT6[rule_format] T_F_spec)
          by(auto simp: is_processT6[rule_format] T_F_spec)
next
     show "\<forall>s t. s \<in> ?D \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> ?D"
          by(auto simp: is_processT7)
next
     show "\<forall>s X. s \<in> ?D \<longrightarrow> (s, X) \<in> ?T"
          by(auto simp: is_processT8[rule_format]) 
next
     show "\<forall>s. s @ [tick] \<in> ?D \<longrightarrow> s \<in> ?D"
          by(auto intro!:is_processT9[rule_format])  
qed


lemma Rep_Abs_D:
"Rep_process
     (Abs_process
       ({(s, X). s = [] \<and> (s, X) \<in> F P \<inter> F Q} \<union>
        {(s, X). s \<noteq> [] \<and> (s, X) \<in> F P \<union> F Q} \<union>
        {(s, X). s = [] \<and> s \<in> D P \<union> D Q} \<union>
        {(s, X). s = [] \<and> tick \<notin> X \<and> [tick] \<in> T P \<union> T Q},
        D P \<union> D Q)) =
    ({(s, X). s = [] \<and> (s, X) \<in> F P \<inter> F Q} \<union>
     {(s, X). s \<noteq> [] \<and> (s, X) \<in> F P \<union> F Q} \<union>
     {(s, X). s = [] \<and> s \<in> D P \<union> D Q} \<union>
     {(s, X). s = [] \<and> tick \<notin> X \<and> [tick] \<in> T P \<union> T Q},
     D P \<union> D Q)"
  by(simp only:CollectI Rep_process Abs_process_inverse is_process_REP_D)


subsection\<open>The Projections\<close>

lemma F_det    :
   "F(P \<box> Q) =    {(s,X). s = [] \<and> (s,X) \<in> F P \<inter> F Q}
                 \<union> {(s,X). s \<noteq> [] \<and> (s,X) \<in> F P \<union> F Q}
                 \<union> {(s,X). s = [] \<and> s \<in> D P \<union> D Q}
                 \<union> {(s,X). s = [] \<and> tick \<notin> X \<and> [tick] \<in> T P \<union> T Q}"
  by(subst F_def, simp only: det_def Rep_Abs_D FAILURES_def fst_conv)


subsection\<open>Basic Laws\<close>
text\<open>The following theorem of Commutativity helps to simplify the subsequent
continuity proof by symmetry breaking. It is therefore already developed here:\<close>
lemma D_det: "D(P \<box> Q) = D P \<union> D Q"
  by(subst D_def, simp only: det_def Rep_Abs_D DIVERGENCES_def snd_conv)


lemma T_det: "T(P \<box> Q) = T P \<union> T Q"
apply(subst T_def, simp only: det_def Rep_Abs_D TRACES_def FAILURES_def
                              fst_def snd_conv)
apply(auto simp: T_F F_T is_processT1 Nil_elem_T)
apply(rule_tac x="{}" in exI, simp add: T_F F_T is_processT1 Nil_elem_T)+
done

lemma Det_commute:"(P \<box> Q) = (Q \<box> P)"
by(auto simp: Process_eq_spec F_det D_det)


subsection\<open>The Continuity-Rule\<close>

lemma mono_D1: "P \<sqsubseteq> Q \<Longrightarrow> D (Q \<box> S) \<subseteq> D (P \<box> S)"
apply (drule le_approx1)
by (auto simp: Process_eq_spec F_det D_det)

lemma mono_D2: 
assumes ordered: "P \<sqsubseteq> Q"
shows   "(\<forall> s. s \<notin> D (P \<box> S) \<longrightarrow> Ra (P \<box> S) s = Ra (Q \<box> S) s)"
proof -
   have A:"\<And>s t. [] \<notin> D P \<Longrightarrow> [] \<notin> D S \<Longrightarrow> s = [] \<Longrightarrow> 
           ([], t) \<in> F P \<Longrightarrow> ([], t) \<in> F S \<Longrightarrow> ([], t) \<in> F Q"
        by (insert ordered,frule_tac X="t" and s="[]" in proc_ord2a, simp_all)
   have B:"\<And>s t. s \<notin> D P \<Longrightarrow> s \<notin> D S \<Longrightarrow>
          (s \<noteq> [] \<and> ((s, t) \<in> F P \<or> (s, t) \<in> F S) \<longrightarrow> (s, t) \<in> F Q \<or> (s, t) \<in> F S) \<and>
          (s = [] \<and> tick \<notin> t \<and> ([tick] \<in> T P \<or> [tick] \<in> T S) \<longrightarrow>
           ([], t) \<in> F Q \<and> ([], t) \<in> F S \<or> [] \<in> D Q \<or>  [tick] \<in> T Q \<or>  [tick] \<in> T S)"
        apply(intro conjI impI, elim conjE disjE, rule disjI1)
        apply(simp_all add: proc_ord2a[OF ordered,symmetric])
        apply(elim conjE disjE,subst le_approx2T[OF ordered])
        apply(frule is_processT9_S_swap, simp_all)
        done
   have C: "\<And>s. s \<notin> D P \<Longrightarrow> s \<notin> D S \<Longrightarrow>
                {X. s = [] \<and> (s, X) \<in> F Q \<and> (s, X) \<in> F S \<or>
                    s \<noteq> [] \<and> ((s, X) \<in> F Q \<or> (s, X) \<in> F S) \<or>
                    s = [] \<and> s \<in> D Q \<or> s = [] \<and> tick \<notin> X \<and> 
                    ([tick] \<in> T Q \<or> [tick] \<in> T S)}
              \<subseteq> {X. s = [] \<and> (s, X) \<in> F P \<and> (s, X) \<in> F S \<or>
                     s \<noteq> [] \<and> ((s, X) \<in> F P \<or> (s, X) \<in> F S) \<or>
                     s = [] \<and> tick \<notin> X \<and> ([tick] \<in> T P \<or> [tick] \<in> T S)}"
        apply(intro subsetI, frule is_processT9_S_swap, simp)
        apply(elim conjE disjE, simp_all add: proc_ord2a[OF ordered,symmetric] is_processT8_S)
        apply(insert le_approx1[OF ordered] le_approx_lemma_T[OF ordered]) 
        by   (auto simp: proc_ord2a[OF ordered,symmetric])    
    show ?thesis
    apply(simp add: Process_eq_spec F_det D_det Ra_def min_elems_def)
    apply(intro allI impI equalityI C, simp_all)
    apply(intro allI impI subsetI, simp)
    apply(metis A B)    
    done
qed


lemma mono_D3 : "P \<sqsubseteq> Q \<Longrightarrow> min_elems (D (P \<box> S)) \<subseteq> T (Q \<box> S)"
apply (frule le_approx3)
apply (simp add: Process_eq_spec F_det T_det D_det Ra_def min_elems_def subset_iff)
apply (auto intro:D_T)
done

lemma mono_Det[simp]  : "P \<sqsubseteq> Q \<Longrightarrow> (P \<box> S) \<sqsubseteq> (Q \<box> S)"
by (auto simp: le_approx_def mono_D1 mono_D2 mono_D3)


lemma mono_Det_sym[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (S \<box> P) \<sqsubseteq> (S \<box> Q)"
by (simp add: Det_commute)



lemma cont_D0 : 
assumes C : "chain Y"
shows       "(lim_proc (range Y) \<box> S) = lim_proc (range (\<lambda>i. Y i \<box> S))"
proof -
  have C':"chain (\<lambda>i. Y i \<box> S)"
          by(auto intro!:chainI simp:chainE[OF C])
  show ?thesis
  apply (subst Process_eq_spec)
  apply (simp add: D_det F_det)
  apply(simp add: F_LUB[OF C]  D_LUB[OF C] T_LUB[OF C] F_LUB[OF C']  D_LUB[OF C'] T_LUB[OF C'])
  apply(safe)
  apply(auto simp: D_det F_det T_det)
  using NF_ND apply blast
  using is_processT6_S2 is_processT8 apply blast
  apply (metis D_T append_Nil front_tickFree_single process_charn tickFree_Nil)
  using NF_ND is_processT6_S2 apply blast
  using NF_ND is_processT6_S2 by blast
qed

lemma cont_D : 
assumes C: "chain Y"
shows   " ((\<Squnion> i. Y i) \<box> S) = (\<Squnion> i. (Y i \<box> S))"
apply(insert C)
apply(subst limproc_is_thelub, simp)
apply(subst limproc_is_thelub)
apply(rule chainI)
apply(frule_tac i="i" in chainE)
apply(simp)
apply(erule cont_D0)
done


lemma cont_D' : 
assumes chain:"chain Y"
shows "((\<Squnion> i. Y i) \<box> S) = (\<Squnion> i. (Y i \<box> S))"
proof -
   have chain':"chain (\<lambda>i. Y i \<box> S)"
          by(auto intro!:chainI simp: chainE[OF chain])
   have B:"F (lim_proc (range Y) \<box> S) \<subseteq>  F (lim_proc (range (\<lambda>i. Y i \<box> S)))"
          apply(simp add: D_det F_det F_LUB T_LUB D_LUB chain chain')
          apply(intro conjI subsetI, simp_all)
          by(auto split:prod.split prod.split_asm)
   have C:"F (lim_proc (range (\<lambda>i. Y i \<box> S))) \<subseteq> F(lim_proc (range Y) \<box> S)"
      proof -
      have C1 : "\<And>ba ab ac. \<forall>a. ([], ba) \<in> F (Y a) \<and> ([], ba) \<in> F S \<or> [] \<in> D (Y a) \<Longrightarrow>
                   [] \<notin> D (Y ab) \<Longrightarrow> [] \<notin> D S \<Longrightarrow>  tick \<in> ba \<Longrightarrow> ([], ba) \<in> F (Y ac) "
                using is_processT8 by auto
      have C2 : "\<And>ba ab ac ad. \<forall>a. ([], ba) \<in> F (Y a) \<and> ([], ba) \<in> F S \<or> [] \<in> D (Y a) 
                               \<or> tick \<notin> ba \<and> [tick] \<in> T (Y a) \<Longrightarrow>
                   []\<notin>D(Y ab) \<Longrightarrow> []\<notin>D S \<Longrightarrow> ([],ba)\<notin> F(Y ac) \<Longrightarrow> [tick]\<notin>T S \<Longrightarrow> [tick]\<in>T(Y ad)"
                using NF_ND is_processT6_S2 by blast
      have C3: "\<And>ba ab ac. \<forall>a. [] \<in> D (Y a) \<or> tick \<notin> ba \<and> [tick] \<in> T (Y a) \<Longrightarrow>
                   [] \<notin> D (Y ab) \<Longrightarrow> [] \<notin> D S \<Longrightarrow> ([], ba) \<notin> F S \<Longrightarrow> 
                   [tick] \<notin> T S \<Longrightarrow> [tick] \<in> T (Y ac)"
                by (metis D_T append_Nil front_tickFree_single process_charn tickFree_Nil)
      show ?thesis
          apply(simp add: D_det F_det F_LUB T_LUB D_LUB chain chain')
          apply(rule subsetI, simp)
          apply(simp split:prod.split prod.split_asm)
          apply(intro allI impI,simp)
          by (metis C3 is_processT6_S2 is_processT8_S)
      qed
   have D:"D (lim_proc (range Y) \<box> S) = D (lim_proc (range (\<lambda>i. Y i \<box> S)))"
          by(simp add: D_det F_det F_LUB T_LUB D_LUB chain chain')
   show ?thesis
   by(simp add: chain chain' limproc_is_thelub Process_eq_spec equalityI B C D)
qed

lemma det_cont[simp]: 
assumes f:"cont f"
and     g:"cont g"
shows     "cont (\<lambda>x. f x \<box> g x)"
proof -
   have A : "\<And>x. cont f \<Longrightarrow> cont (\<lambda>y. y \<box> f x)"
       apply (rule contI2,rule monofunI)
       apply (auto)
       apply (subst Det_commute,subst cont_D)
       apply (auto simp: Det_commute)
       done
   have B : "\<And>y. cont f \<Longrightarrow> cont (\<lambda>x. y \<box> f x)"
       apply (rule_tac c="(\<lambda> x. y \<box> x)" in cont_compose)
       apply (rule contI2,rule monofunI)
       apply (auto)
       apply (subst Det_commute,subst cont_D)
       by (simp_all add: Det_commute)
   show ?thesis using f g 
      apply(rule_tac f="(\<lambda>x. (\<lambda> g. f x \<box> g))" in cont_apply)
      apply(auto intro:contI2 monofunI simp:Det_commute A B)
      done
qed

end