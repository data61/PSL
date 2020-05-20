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

section\<open>The Sequence Operator\<close>

theory  Seq
  imports Process 
begin 

subsection\<open>Definition\<close>
abbreviation "div_seq P Q   \<equiv> {t1 @ t2 |t1 t2. t1 \<in> D P \<and> tickFree t1 \<and> front_tickFree t2}
                            \<union> {t1 @ t2 |t1 t2. t1 @ [tick] \<in> T P \<and> t2 \<in> D Q}"

definition  seq :: "['a process,'a process] \<Rightarrow> 'a process"  (infixl  "`;`" 24)  
where       "P `;` Q \<equiv> Abs_process
                            ({(t, X). (t, X \<union> {tick}) \<in> F P \<and> tickFree t} \<union>
                             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> (t2, X) \<in> F Q} \<union>
                             {(t, X). t \<in> div_seq P Q},
                             div_seq P Q)"

lemma  seq_maintains_is_process:
      "is_process     ({(t, X). (t, X \<union> {tick}) \<in> F P \<and> tickFree t} \<union>
                       {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> (t2, X) \<in> F Q} \<union>
                       {(t, X). t \<in> div_seq P Q},
                       div_seq P Q)"
       (is "is_process(?f, ?d)")
proof(simp only: fst_conv snd_conv F_def is_process_def FAILURES_def DIVERGENCES_def,
      fold FAILURES_def DIVERGENCES_def,fold F_def,intro conjI)
  show "([], {}) \<in> ?f" 
    apply(cases "[tick] \<in> T P", simp_all add: is_processT1)
    using F_T is_processT5_S6 by blast        
next
  show " \<forall>s X. (s, X) \<in> ?f \<longrightarrow> front_tickFree s"
    by (auto simp:is_processT2 append_T_imp_tickFree front_tickFree_append D_imp_front_tickFree)   
next
  show "\<forall>s t. (s @ t, {}) \<in> ?f \<longrightarrow> (s, {}) \<in> ?f"       
    apply auto
          apply (metis F_T append_Nil2 is_processT is_processT3_SR is_processT5_S3)
         apply(simp add:append_eq_append_conv2) 
         apply (metis T_F_spec append_Nil2 is_processT is_processT5_S4)
        apply (metis append_self_conv front_tickFree_append front_tickFree_mono is_processT2_TR 
              no_Trace_implies_no_Failure non_tickFree_implies_nonMt non_tickFree_tick)
       apply (metis (mono_tags, lifting) F_T append_Nil2 is_processT5_S3 process_charn)
      apply (metis front_tickFree_append front_tickFree_mono self_append_conv)
     apply(simp add:append_eq_append_conv2)
     apply (metis T_F_spec append_Nil2 is_processT is_processT5_S4)
    by (metis D_imp_front_tickFree append_T_imp_tickFree front_tickFree_append 
               front_tickFree_mono not_Cons_self2 self_append_conv)
next
  show "\<forall>s X Y. (s, Y) \<in> ?f \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> ?f" 
    apply auto
       apply (metis insert_mono is_processT4_S1 prod.sel(1) prod.sel(2))
      apply (metis is_processT4)
     apply (simp add: append_T_imp_tickFree)
    by (metis process_charn)
next
  { fix sa X Y
    have "(sa, X \<union> {tick}) \<in> F P \<Longrightarrow>
            tickFree sa \<Longrightarrow>
            \<forall>c. c \<in> Y \<and> c \<noteq> tick \<longrightarrow> (sa @ [c], {}) \<notin> F P \<Longrightarrow> 
            (sa, X \<union> Y \<union> {tick}) \<in> F P \<and> tickFree sa"
    apply(rule_tac t="X \<union> Y \<union> {tick}" and s="X \<union> {tick} \<union> (Y-{tick})" in subst,auto)
    by   (metis DiffE Un_insert_left is_processT5 singletonI)
  } note is_processT5_SEQH3 = this
  have is_processT5_SEQH4 : "\<And> sa X Y. (sa, X \<union> {tick}) \<in> F P \<Longrightarrow>
                                         tickFree sa \<Longrightarrow>
                                         \<forall>c. c \<in> Y \<longrightarrow> (sa@[c],{tick}) \<notin> F P \<or> \<not> tickFree(sa@[c]) \<Longrightarrow>
                                         \<forall>c. c \<in> Y \<longrightarrow> (\<forall>t1 t2. sa@[c]\<noteq>t1@t2 \<or> t1@[tick]\<notin>T P \<or> (t2,{})\<notin>F Q) \<Longrightarrow>
                                         (sa, X \<union> Y \<union> {tick}) \<in> F P \<and> tickFree sa"
    by (metis append_Nil2 is_processT1 is_processT5_S3 is_processT5_SEQH3 
                         no_Trace_implies_no_Failure tickFree_Cons tickFree_append)
  let ?f1 = "{(t, X). (t, X \<union> {tick}) \<in> F P \<and> tickFree t} \<union> 
             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> (t2, X) \<in> F Q}"
  have is_processT5_SEQ2: "\<And> sa X Y. (sa, X) \<in> ?f1 \<Longrightarrow> (\<forall>c. c \<in> Y \<longrightarrow> (sa@[c], {})\<notin>?f) \<Longrightarrow> (sa, X\<union>Y) \<in> ?f1"
    apply (clarsimp,rule is_processT5_SEQH4[simplified])
    by (auto simp: is_processT5)
  show "\<forall>s X Y. (s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<longrightarrow> (s, X \<union> Y) \<in> ?f"
    apply(intro allI impI, elim conjE UnE)
      apply(rule rev_subsetD)
       apply(rule is_processT5_SEQ2)
        apply auto
      using is_processT5_S1 apply force
     apply (simp add: append_T_imp_tickFree)
    using is_processT5[rule_format, OF conjI] by force
next  
  show "\<forall>s X. (s @ [tick], {}) \<in> ?f \<longrightarrow> (s, X - {tick}) \<in> ?f" 
    apply auto
        apply (metis (no_types, lifting) append_T_imp_tickFree butlast_append 
                     butlast_snoc is_processT2 is_processT6 nonTickFree_n_frontTickFree 
                     non_tickFree_tick tickFree_append)
       apply (metis append_T_imp_tickFree front_tickFree_append front_tickFree_mono 
                    is_processT2 non_tickFree_implies_nonMt non_tickFree_tick)
      apply (metis process_charn)
     apply (metis front_tickFree_append front_tickFree_implies_tickFree)
    apply (metis D_T T_nonTickFree_imp_decomp append_T_imp_tickFree append_assoc 
                 append_same_eq non_tickFree_implies_nonMt non_tickFree_tick process_charn 
                 tickFree_append)
    by    (metis D_imp_front_tickFree append_T_imp_tickFree front_tickFree_append 
                    front_tickFree_mono non_tickFree_implies_nonMt non_tickFree_tick)
next
  show "\<forall>s t. s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> ?d"
    apply auto 
     using front_tickFree_append apply blast     
    by (metis process_charn)
next  
  show "\<forall>s X. s \<in> ?d \<longrightarrow>  (s, X) \<in> ?f"
    by blast
next  
  show "\<forall>s. s @ [tick] \<in> ?d \<longrightarrow> s \<in> ?d"
    apply auto      
     apply (metis append_Nil2 front_tickFree_implies_tickFree process_charn)
    by (metis append1_eq_conv append_assoc front_tickFree_implies_tickFree is_processT2_TR 
                nonTickFree_n_frontTickFree non_tickFree_tick process_charn tickFree_append)
qed


subsection\<open>The Projections\<close>


lemmas  Rep_Abs_Seq[simp] = Abs_process_inverse[simplified, OF seq_maintains_is_process]

lemma  
    F_seq   : "F(P `;` Q) =  {(t, X). (t, X \<union> {tick}) \<in> F P \<and> tickFree t} \<union>
                             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> (t2, X) \<in> F Q} \<union>
                             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 \<in> D P \<and> tickFree t1 \<and> front_tickFree t2} \<union>
                             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> t2 \<in> D Q}"
unfolding seq_def by(subst F_def, simp only:Rep_Abs_Seq, auto simp: FAILURES_def)

lemma
    D_seq   : "D(P `;` Q) =  {t1 @ t2 |t1 t2. t1 \<in> D P \<and> tickFree t1 \<and> front_tickFree t2} \<union>
                             {t1 @ t2 |t1 t2. t1 @ [tick] \<in> T P \<and> t2 \<in> D Q}"
unfolding seq_def by(subst D_def,simp only:Rep_Abs_Seq, simp add:DIVERGENCES_def)

lemma
    T_seq   : "T(P `;` Q) =  {t. \<exists> X. (t, X \<union> {tick}) \<in> F P \<and> tickFree t} \<union>  
                             {t. \<exists> t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> T P \<and> t2 \<in> T Q} \<union>
                             {t1 @ t2 |t1 t2. t1 \<in> D P \<and> tickFree t1 \<and> front_tickFree t2} \<union>
                             {t1 @ t2 |t1 t2. t1 @ [tick] \<in> T P \<and> t2 \<in> D Q} \<union>
                             {t1 @ t2 |t1 t2. t1 \<in> D P \<and> tickFree t1 \<and> front_tickFree t2} \<union>
                             {t1 @ t2 |t1 t2. t1 @ [tick] \<in> T P \<and> t2 \<in> D Q}"
  unfolding seq_def  
  apply(subst T_def, simp only: Rep_Abs_Seq, auto simp:TRACES_def FAILURES_def)
     using F_T apply fastforce
    apply (simp add: append_T_imp_tickFree)
   using F_T apply fastforce
  using T_F by blast

subsection\<open> Continuity Rule \<close>

lemma mono_D11:  
"P \<sqsubseteq> Q \<Longrightarrow> D (Q `;` S) \<subseteq> D (P `;` S)"
  apply(auto simp: D_seq)
   using le_approx1 apply blast
  using le_approx_lemma_T by blast

lemma mono_D12: 
assumes ordered: "P \<sqsubseteq> Q"
shows   "(\<forall> s. s \<notin> D (P `;` S) \<longrightarrow> Ra (P `;` S) s = Ra (Q `;` S) s)"
proof -
  have mono_SEQI2a:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> D (P `;` S) \<longrightarrow> Ra (Q `;` S) s \<subseteq> Ra (P `;` S) s"
    apply(simp add: Ra_def D_seq F_seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q], auto) 
    using le_approx1 by blast+
  have mono_SEQI2b:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> D (P `;` S) \<longrightarrow> Ra (P `;` S) s \<subseteq> Ra (Q `;` S) s"
    apply(simp add: Ra_def D_seq F_seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] 
          le_approx1[of P Q] le_approx2T[of P Q], auto) 
      using le_approx2 apply fastforce
     apply (metis front_tickFree_implies_tickFree is_processT2_TR process_charn)
    apply (simp add: append_T_imp_tickFree) 
    by (metis front_tickFree_implies_tickFree is_processT2_TR process_charn)
  show ?thesis 
    using ordered mono_SEQI2a mono_SEQI2b by(blast)
qed

lemma minSeqInclu: 
  "min_elems(D (P `;` S)) \<subseteq> min_elems(D P) \<union> {t1@t2|t1 t2. t1@[tick]\<in>T P\<and>t1\<notin>D P\<and>t2\<in>min_elems(D S)}"
  apply(auto simp: D_seq min_elems_def)
     apply (meson process_charn)
    apply (metis append_Nil2 front_tickFree_Nil front_tickFree_append front_tickFree_mono 
           le_list_def less_list_def)
   apply (metis (no_types, lifting) D_imp_front_tickFree Nil_is_append_conv append_T_imp_tickFree 
          append_butlast_last_id butlast_append process_charn less_self lim_proc_is_lub3a 
          list.distinct(1) nil_less)
  by (metis D_imp_front_tickFree append_Nil2 front_tickFree_Nil front_tickFree_mono process_charn 
      list.distinct(1) nonTickFree_n_frontTickFree)

lemma mono_D13 : 
assumes ordered: "P \<sqsubseteq> Q"
shows        "min_elems (D (P `;` S)) \<subseteq> T (Q `;` S)"
  apply (insert ordered, frule le_approx3, rule subset_trans [OF minSeqInclu])
  apply (auto simp: F_seq T_seq min_elems_def append_T_imp_tickFree)
     apply(rule_tac x="{}" in exI, rule is_processT5_S3)
      apply (metis (no_types, lifting) T_F elem_min_elems le_approx3 less_list_def min_elems5 subset_eq)
     using Nil_elem_T no_Trace_implies_no_Failure apply fastforce
    apply (metis (no_types, lifting) less_self nonTickFree_n_frontTickFree process_charn)  
   apply(rule_tac x="{}" in exI, metis (no_types, lifting) le_approx2T process_charn)
  by (metis (no_types, lifting) less_self nonTickFree_n_frontTickFree process_charn)  

lemma mono_Seq[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (P `;` S) \<sqsubseteq> (Q `;` S)"
by (auto simp: le_approx_def mono_D11 mono_D12 mono_D13)

lemma mono_D21:  
"P \<sqsubseteq> Q \<Longrightarrow> D (S `;` Q) \<subseteq> D (S `;` P)"
  apply(auto simp: D_seq)
  using le_approx1 by blast

lemma mono_D22: 
assumes ordered: "P \<sqsubseteq> Q"
shows   "(\<forall> s. s \<notin> D (S `;` P) \<longrightarrow> Ra (S `;` P) s = Ra (S `;` Q) s)"
proof -
  have mono_SEQI2a:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> D (S `;` P) \<longrightarrow> Ra (S `;` Q) s \<subseteq> Ra (S `;` P) s"
    apply(simp add: Ra_def D_seq F_seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q], auto) 
    using le_approx1 by fastforce+
  have mono_SEQI2b:"P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> D (S `;` P) \<longrightarrow> Ra (S `;` P) s \<subseteq> Ra (S `;` Q) s"
    apply(simp add: Ra_def D_seq F_seq)
    apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] 
            le_approx1[of P Q] le_approx2T[of P Q], auto) 
    using le_approx2 by fastforce+
  show ?thesis 
    using ordered mono_SEQI2a mono_SEQI2b by(blast)
qed

lemma mono_D23 : 
assumes ordered: "P \<sqsubseteq> Q"
shows       "min_elems (D (S `;` P)) \<subseteq> T (S `;` Q)"
  apply (insert ordered, frule le_approx3, auto simp:D_seq T_seq min_elems_def)
     apply (metis (no_types, lifting) D_imp_front_tickFree Nil_elem_T append.assoc below_refl 
            front_tickFree_charn less_self min_elems2 no_Trace_implies_no_Failure)
    apply (simp add: append_T_imp_tickFree)
  by (metis (no_types, lifting) D_def D_imp_front_tickFree append_butlast_last_id append_is_Nil_conv 
        butlast_append butlast_snoc is_process9 is_process_Rep less_self nonTickFree_n_frontTickFree)

lemma mono_Seq_sym[simp] : "P \<sqsubseteq> Q \<Longrightarrow> (S `;` P) \<sqsubseteq> (S `;` Q)"
by (auto simp: le_approx_def mono_D21 mono_D22 mono_D23)

lemma chain_Seq1: "chain Y \<Longrightarrow> chain (\<lambda>i. Y i `;` S)"
  by(simp add: chain_def) 

lemma chain_Seq2: "chain Y \<Longrightarrow> chain (\<lambda>i. S `;` Y i)"
  by(simp add: chain_def)  

lemma limproc_Seq_D1: "chain Y \<Longrightarrow> D (lim_proc (range Y) `;` S) = D (lim_proc (range (\<lambda>i. Y i `;` S)))"
  apply(auto simp:Process_eq_spec D_seq F_seq F_LUB D_LUB T_LUB chain_Seq1)
   apply(blast)
  proof -
    fix x
    assume A:"\<forall>xa. (\<exists>t1 t2. x = t1 @ t2 \<and> t1 \<in> D (Y xa) \<and> tickFree t1 \<and> front_tickFree t2) \<or>
                (\<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> T (Y xa) \<and> t2 \<in> D S)"
    and B: "\<forall>t1 t2. x = t1 @ t2 \<longrightarrow> (\<exists>x. t1 @ [tick] \<notin> T (Y x)) \<or> t2 \<notin> D S"
    and C: "chain Y"
    thus "\<exists>t1 t2. x = t1 @ t2 \<and> (\<forall>x. t1 \<in> D (Y x)) \<and> tickFree t1 \<and> front_tickFree t2"        
      proof (cases "\<exists>n. \<forall>t1 \<le> x. t1 \<notin> D (Y n)")
        case True
        then obtain n where "\<forall>t1 \<le> x. t1 \<notin> D (Y n)" by blast
        with A B C show ?thesis 
          apply(erule_tac x=n in allE, elim exE disjE, auto simp add:le_list_def)
          by (metis D_T chain_lemma is_processT le_approx2T)
      next
        case False
        from False obtain t1 where D:"t1 \<le> x \<and> (\<forall>n. \<forall>t \<le> x. t \<in> D (Y n) \<longrightarrow> t \<le> t1)" by blast
        with False have E:"\<forall>n. t1 \<in> D (Y n)" 
          by (metis append_Nil2 append_T_imp_tickFree front_tickFree_append front_tickFree_mono 
                    is_processT le_list_def local.A not_Cons_self2)
        from A B C D E show ?thesis
          by (metis D_imp_front_tickFree T_def append_Nil2 front_tickFree_append 
                    front_tickFree_implies_tickFree front_tickFree_mono is_processT 
                    is_process_Rep le_list_def nonTickFree_n_frontTickFree 
                    trace_with_Tick_implies_tickFree_front)          
      qed
  qed

lemma limproc_Seq_F1: "chain Y \<Longrightarrow> F (lim_proc (range Y) `;` S) = F (lim_proc (range (\<lambda>i. Y i `;` S)))"
  apply(auto simp add:Process_eq_spec D_seq F_seq F_LUB D_LUB T_LUB chain_Seq1)
  proof (auto, goal_cases)
    case (1 a b x)
    then show ?case
      apply(erule_tac x=x in allE, elim disjE exE, auto simp add: is_processT7 is_processT8_S) 
       apply(rename_tac t1 t2, erule_tac x=t1 in allE, erule_tac x=t1 in allE, erule_tac x=t1 in allE)
       apply (metis D_T append_T_imp_tickFree chain_lemma is_processT le_approx2T not_Cons_self2)
      by (metis D_T append_T_imp_tickFree chain_lemma is_processT le_approx2T not_Cons_self2)
  next
    case (2 a b)
    assume A1:"\<forall>t1 t2. a = t1 @ t2 \<longrightarrow> (\<exists>x. t1 @ [tick] \<notin> T (Y x)) \<or> t2 \<notin> D S"
      and  A2:"\<forall>t1. tickFree t1 \<longrightarrow> (\<forall>t2. a = t1 @ t2 \<longrightarrow> (\<exists>x. t1 \<notin> D (Y x)) \<or> \<not> front_tickFree t2)"
      and  A3:"\<forall>t1 t2. a = t1 @ t2 \<longrightarrow> (\<exists>x. t1 @ [tick] \<notin> T (Y x)) \<or> (t2, b) \<notin> F S"
      and  B: "\<forall>x. (a, insert tick b) \<in> F (Y x) \<and> tickFree a \<or>
               (\<exists>t1 t2. a = t1 @ t2 \<and> t1 @ [tick] \<in> T (Y x) \<and> (t2, b) \<in> F S) \<or>
               (\<exists>t1 t2. a = t1 @ t2 \<and> t1 \<in> D (Y x) \<and> tickFree t1 \<and> front_tickFree t2) \<or>
               (\<exists>t1 t2. a = t1 @ t2 \<and> t1 @ [tick] \<in> T (Y x) \<and> t2 \<in> D S)"
      and  C:"chain Y" 
    have E:"\<not> tickFree a \<Longrightarrow> False"
      proof -
        assume F:"\<not> tickFree a"
        from A obtain f where D:"f = (\<lambda>t2. {n. \<exists>t1. a = t1 @ t2 \<and> t1 @ [tick] \<in> T (Y n) \<and> (t2, b) \<in> F S}
                                      \<union> {n. \<exists>t1. a = t1 @ t2 \<and> t1 \<in> D (Y n) \<and> tickFree t1 \<and> front_tickFree t2})"
          by simp
        with B F have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. a = t1 @ t}. f x)"  (is "\<forall>n. n \<in> ?S f") using NF_ND by fastforce
        hence "infinite (?S f)" by (simp add: Sup_set_def)
        then obtain t2 where E:"t2\<in>{t. \<exists>t1. a = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
        { assume E1:"infinite{n. \<exists>t1. a = t1 @ t2 \<and> t1 @ [tick] \<in> T (Y n) \<and> (t2, b) \<in> F S}" (is "infinite ?E1")
          with E obtain t1 where F:"a = t1 @ t2 \<and> (t2, b) \<in> F S" using D not_finite_existsD by blast
          with A3 obtain m where G:"t1@ [tick] \<notin> T (Y m)" by blast
          with E1 obtain n where "n \<ge> m \<and> n \<in> ?E1" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
          with D have "n \<ge> m \<and> t1@ [tick] \<in> T (Y n)" by (simp add: F)
          with G C have False using le_approx_lemma_T chain_mono by blast
        } note E1 = this
        { assume E2:"infinite{n. \<exists>t1. a = t1 @ t2 \<and> t1 \<in> D (Y n) \<and> tickFree t1 \<and> front_tickFree t2}" (is "infinite ?E2")
          with E obtain t1 where F:"a = t1 @ t2 \<and> tickFree t1 \<and> front_tickFree t2" using D not_finite_existsD by blast
          with A2 obtain m where G:"t1 \<notin> D (Y m)" by blast
          with E2 obtain n where "n \<ge> m \<and> n \<in> ?E2" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
          with D have "n \<ge> m \<and> t1 \<in> D (Y n)" by (simp add: F)
          with G C have False using le_approx1 chain_mono by blast
        } note E2 = this      
        from D E E1 E2 show False by blast
      qed
    from E show "tickFree a" by blast
  qed

lemma cont_left_D : "chain Y \<Longrightarrow> ((\<Squnion> i. Y i) `;` S) = (\<Squnion> i. (Y i `;` S))"
  by (simp add: Process_eq_spec chain_Seq1 limproc_Seq_D1 limproc_Seq_F1 limproc_is_thelub)

lemma limproc_Seq_D2: "chain Y \<Longrightarrow> D (S `;` lim_proc (range Y)) = D (lim_proc (range (\<lambda>i. S `;` Y i )))"
  apply(auto simp add:Process_eq_spec D_seq F_seq F_LUB D_LUB T_LUB chain_Seq2)
  apply(blast)
  proof -
    fix x
    assume A:"\<forall>t1. t1 @ [tick] \<in> T S \<longrightarrow> (\<forall>t2. x = t1 @ t2 \<longrightarrow> (\<exists>x. t2 \<notin> D (Y x)))"
    and B: "\<forall>n. \<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> t2 \<in> D (Y n)"
    and C: "chain Y"
    from A obtain f where D:"f = (\<lambda>t2. {n. \<exists>t1. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> t2 \<in> D (Y n)})"
      by simp
    with B have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. x = t1 @ t}. f x)" (is "\<forall>n. n \<in> ?S f") by fastforce
    hence "infinite (?S f)" by (simp add: Sup_set_def)
    then obtain t2 where E:"t2\<in>{t. \<exists>t1. x = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
    then obtain t1 where F:"x = t1 @ t2 \<and> t1 @ [tick] \<in> T S" using D not_finite_existsD by blast
    from A F obtain m where G:"t2 \<notin> D (Y m)" by blast
    with E obtain n where "n \<ge> m \<and> n \<in> (f t2)" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
    with D have "n \<ge> m \<and> t2 \<in> D (Y n)" by blast
    with G C have False using le_approx1 po_class.chain_mono by blast
    thus "\<exists>t1 t2. x = t1 @ t2 \<and> t1 \<in> D S \<and> tickFree t1 \<and> front_tickFree t2" ..       
  qed

lemma limproc_Seq_F2: "chain Y \<Longrightarrow> F (S `;` lim_proc (range Y)) = F (lim_proc (range (\<lambda>i. S `;` Y i )))"
  apply(auto simp:Process_eq_spec D_seq F_seq T_seq F_LUB D_LUB D_LUB_2 T_LUB T_LUB_2 chain_Seq2 del:conjI)
    apply(auto)[1]
   apply(auto)[1]
  proof-
    fix x X
    assume A:"\<forall>t1. t1 @ [tick] \<in> T S \<longrightarrow> (\<forall>t2. x = t1 @ t2 \<longrightarrow> (\<exists>m. (t2, X) \<notin> F (Y m)))"
    and B: "\<forall>n. (\<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> (t2, X) \<in> F (Y n)) \<or>
                (\<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> t2 \<in> D (Y n))"
    and C: "chain Y"
    hence D:"\<forall>n. (\<exists>t1 t2. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> (t2, X) \<in> F (Y n))" by (meson NF_ND)
    from A obtain f where D:"f = (\<lambda>t2. {n. \<exists>t1. x = t1 @ t2 \<and> t1 @ [tick] \<in> T S \<and> (t2, X) \<in> F (Y n)})"
      by simp
    with D have "\<forall>n. n \<in> (\<Union>x\<in>{t. \<exists>t1. x = t1 @ t}. f x)" using B NF_ND by fastforce
    hence "infinite (\<Union>x\<in>{t. \<exists>t1. x = t1 @ t}. f x)" by (simp add: Sup_set_def)
    then obtain t2 where E:"t2\<in>{t. \<exists>t1. x = t1 @ t} \<and> infinite (f t2)" using suffixes_fin by blast
    then obtain t1 where F:"x = t1 @ t2 \<and> t1 @ [tick] \<in> T S" using D not_finite_existsD by blast
    from A F obtain m where G:"(t2, X) \<notin> F (Y m)" by blast
    with E obtain n where "n \<ge> m \<and> n \<in> (f t2)" by (meson finite_nat_set_iff_bounded_le nat_le_linear)
    with D have "n \<ge> m \<and> (t2, X) \<in> F (Y n)" by blast
    with G C have False using is_processT8 po_class.chain_mono proc_ord2a by blast
    thus "(x, insert tick X) \<in> F S \<and> tickFree x" ..
  qed

lemma cont_right_D : "chain Y \<Longrightarrow> (S `;` (\<Squnion> i. Y i)) = (\<Squnion> i. (S `;` Y i))"
  by (simp add: Process_eq_spec chain_Seq2 limproc_Seq_D2 limproc_Seq_F2 limproc_is_thelub)

lemma Seq_cont[simp]:
assumes f:"cont f"
and     g:"cont g"
shows     "cont (\<lambda>x. f x `;` g x)"
proof -
  have A : "\<And>x. cont g \<Longrightarrow> cont (\<lambda>y. y `;` g x)"
    apply (rule contI2, rule monofunI)
     apply (auto)
    by (simp add: cont_left_D)
  have B : "\<And>y. cont g \<Longrightarrow> cont (\<lambda>x. y `;` g x)"
    apply (rule_tac c="(\<lambda> x. y `;` x)" in cont_compose)
     apply (rule contI2,rule monofunI)
    by (auto simp add: chain_Seq2 cont_right_D)
  show ?thesis using f g 
    apply(rule_tac f="(\<lambda>x. (\<lambda> f. f `;` g x))" in cont_apply)
      by(auto intro:contI2 monofunI simp:A B)
qed

end

