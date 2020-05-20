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

chapter\<open>Concurrent CSP Operators\<close>

section\<open>The Hiding Operator\<close>

theory  Hide
imports Process
begin

subsection\<open>Preliminaries : primitives and lemmas\<close>

abbreviation "trace_hide t A \<equiv> filter (\<lambda>x. x \<notin> A) t"

lemma hiding_tickFree : "tickFree s \<longleftrightarrow> tickFree (trace_hide s (ev`A))"
  by (auto simp add: tickFree_def)

lemma hiding_fronttickFree : "front_tickFree s \<Longrightarrow> front_tickFree (trace_hide s (ev`A))"
  apply(auto simp add: front_tickFree_charn tickFree_def split:if_splits)
  by (metis hiding_tickFree list_nonMt_append tickFree_append tickFree_def)

lemma trace_hide_union[simp] : "trace_hide t (ev ` (A \<union> B)) = trace_hide (trace_hide t (ev ` A)) (ev ` B)" 
  by (subgoal_tac "ev ` (A \<union> B) = (ev ` A) \<union> (ev ` B)") auto

abbreviation "isInfHiddenRun f P A \<equiv> strict_mono f \<and> (\<forall> i. f i \<in> T P) \<and> 
                                      (\<forall> i. trace_hide (f i) (ev ` A) = trace_hide (f (0::nat)) (ev ` A))"

lemma isInfHiddenRun_1: "isInfHiddenRun f P A \<longleftrightarrow> strict_mono f \<and> (\<forall> i. f i \<in> T P) \<and>  
                                                  (\<forall>i. \<exists>t. f i = f 0 @ t \<and> set t \<subseteq>  (ev ` A))"
                         (is "?A \<longleftrightarrow> ?B")
proof
  assume A: ?A
  {
    fix i
    from A have "f 0 \<le> f i" using strict_mono_less_eq by blast
    then obtain t where B:"f i = f 0 @ t" by (metis le_list_def)
    hence "trace_hide (f i) (ev ` A) = (trace_hide (f 0) (ev ` A)) @ (trace_hide t (ev ` A))" by simp
    with A have "trace_hide t (ev ` A) = []" by (metis append_self_conv)
    with B have "\<exists>t. f i = f 0 @ t \<and> set t \<subseteq>  (ev ` A)"
      using filter_empty_conv[of "\<lambda>x. x \<notin> (ev ` A)"] by auto
  }
  with A show ?B by simp
next
  assume B: ?B
  {
    fix i
    from B obtain t where B:"f i = f 0 @ t" and "set t \<subseteq>  (ev ` A)" by blast
    hence "trace_hide (f i) (ev ` A) = (trace_hide (f 0) (ev ` A))" by (simp add: subset_iff)
  }
  with B show ?A by simp
qed

subsection\<open>The Hiding Operator Definition\<close>

abbreviation "div_hide P A \<equiv> {s. \<exists> t u. front_tickFree u \<and>
                                        tickFree t \<and> s = trace_hide t (ev ` A) @ u \<and> 
                                        (t \<in> D P \<or> (\<exists> f. isInfHiddenRun f P A \<and> t \<in> range f))}"

definition hiding  :: "['\<alpha> process ,'\<alpha> set] => '\<alpha> process"     ("_ \\ _" [73,72] 72)  where  
  "P \\ A \<equiv> Abs_process ({(s,X). \<exists> t. s = trace_hide t (ev`A) \<and> (t,X \<union> (ev`A)) \<in> F P} \<union>
                          {(s,X). s \<in> div_hide P A}, div_hide P A)"

lemma inf_hidden:
  assumes as1:"\<forall>t. trace_hide t (ev ` A) = trace_hide s (ev ` A) \<longrightarrow> (t, ev ` A) \<notin> F P"
      and as2:"s \<in> T P"
    shows "\<exists>f. isInfHiddenRun f P A \<and> s \<in> range f"
proof
  define f where A:"f = rec_nat s (\<lambda>i t. (let e = SOME e. e \<in> ev`A \<and> t @ [e] \<in> T P in t @ [e]))"
  hence B:"strict_mono f" by (simp add:strict_mono_def lift_Suc_mono_less_iff)
  from A have C:"s \<in> range f" 
    by (metis (mono_tags, lifting) old.nat.simps(6) range_eqI)
  { fix i
    have "f i \<in> T P \<and> trace_hide (f i) (ev ` A) = (trace_hide s (ev ` A))"
    proof(induct i, simp add: A Nil_elem_T as2)
      case (Suc i)
      with as1[THEN spec, of "f i"] have a:"\<exists>e. e \<in> ev`A \<and> f i @ [e] \<in> T P" 
        using is_processT5_S7 by force
      from A have b:"f (Suc i) = (let e = SOME e. e \<in> ev`A \<and> f i @ [e] \<in> T P in  f i @ [e])"
        by simp
      with Suc a[THEN someI_ex] show ?case by simp
    qed
  } 
  with B C show "isInfHiddenRun f P A \<and> s \<in> range f" by simp
qed

subsection\<open>Consequences\<close>

lemma trace_hide_append: "s @ t = trace_hide ta (ev ` A) \<Longrightarrow> \<exists>ss tt. ta = ss@tt \<and> 
                                                                     s = trace_hide ss (ev ` A) \<and> 
                                                                     t = trace_hide tt (ev ` A)"
proof(induct "ta" arbitrary:s t)
  case Nil thus ?case by simp
next
  case (Cons a ta) thus ?case
  proof(cases "a \<in> (ev ` A)")
    case True
    hence "s @ t = trace_hide ta (ev ` A)" by (simp add: Cons)
    with Cons obtain ss tt where "ta = ss @ tt \<and> s = trace_hide ss (ev ` A) 
                                  \<and> t = trace_hide tt (ev ` A)" by blast
    with True Cons show ?thesis by (rule_tac x="a#ss" in exI, rule_tac x=tt in exI, auto)
  next
    case False thus ?thesis 
    proof(cases s)
      case Nil thus ?thesis using Cons by fastforce
    next
      case Cons2:(Cons aa tls)
      with False have A:"a = aa \<and> tls @ t = trace_hide ta (ev ` A)" using Cons by auto
      with Cons obtain ss tt where "ta = ss @ tt \<and> tls = trace_hide ss (ev ` A) 
                                  \<and> t = trace_hide tt (ev ` A)" by blast
      with Cons2 A False show ?thesis by (rule_tac x="a#ss" in exI, rule_tac x=tt in exI, auto)
    qed
  qed
qed

lemma hiding_maintains_is_process:
      "is_process     ({(s,X). \<exists> t. s = trace_hide t (ev`A) \<and> (t,X \<union> (ev`A)) \<in> F P} \<union>
                          {(s,X). s \<in> div_hide P A}, div_hide P A)" (is "is_process(?f, ?d)")
proof (simp only: fst_conv snd_conv F_def is_process_def FAILURES_def DIVERGENCES_def,
      fold FAILURES_def DIVERGENCES_def,fold F_def,intro conjI, goal_cases)
  case 1 thus ?case
  proof (auto, rule not_not[THEN iffD1], rule notI, simp, goal_cases)
    case 1
    from inf_hidden[of A "[]" P] obtain f where A:"isInfHiddenRun f P A \<and> [] \<in> range f"
      using "1"(2) Nil_elem_T by auto
    from A 1(1)[THEN spec, of "[]"] filter.simps(1) tickFree_Nil show ?case by auto
  qed
next
  case 2 thus ?case
    using is_processT2 hiding_fronttickFree front_tickFree_append hiding_tickFree by blast+
next
  case 3 thus ?case
  proof(auto del:disjE, goal_cases)
    case (1 s t ta) show ?case
    proof(cases "tickFree s")
      case True
      from 1(2) obtain ss tt where A:"ta = ss@tt \<and> s = trace_hide ss (ev ` A) \<and> ss \<in> T P"
        using trace_hide_append[of s t A ta, OF 1(1)] by (metis F_T is_processT3_SR)
      with True have B:"tickFree ss"
        by (metis event.distinct(1) filter_set imageE member_filter tickFree_def)
      show ?thesis 
        using 1(3) A B inf_hidden[of A ss P] by (metis append_Nil2 front_tickFree_Nil)
    next
      case False
      with 1(1,2) obtain ss tt where A:"s = ss@[tick] \<and> ta = tt@[tick]"
        by (metis append_Nil2 contra_subsetD filter_is_subset front_tickFree_mono 
                  hiding_fronttickFree is_processT nonTickFree_n_frontTickFree tickFree_def)
      with 1(1,2) have "ss = trace_hide tt (ev ` A)"
        by (metis (no_types, lifting) butlast_append butlast_snoc contra_subsetD 
                  filter.simps(2) filter_append filter_is_subset front_tickFree_implies_tickFree 
                  front_tickFree_single is_processT nonTickFree_n_frontTickFree non_tickFree_tick 
                  self_append_conv2 tickFree_append tickFree_def)
      with False 1(1,2) A show ?thesis
        by (metis append_Nil2 front_tickFree_mono hiding_fronttickFree is_processT)
    qed
  next
    case (2 s t ta u) show ?case
    proof(cases "length s \<le> length (trace_hide ta (ev ` A))")
      case True
      with append_eq_append_conv2[THEN iffD1, OF 2(3)] 
        obtain tt where "s@tt = trace_hide ta (ev ` A)" by auto
      with 2(4) obtain ss ttt where A:"ta = ss@ttt \<and> s = trace_hide ss (ev ` A) \<and> ss \<in> T P"
        using trace_hide_append[of s tt A ta] by (metis D_T imageE is_processT3_ST)
      with 2(2) have B:"tickFree ss" using tickFree_append by blast
      show ?thesis 
        using 2(4,5) A B inf_hidden[of A ss P]
        by (metis (no_types, lifting) append_Nil2 is_processT)
    next
      case False
      with 2(3) obtain uu uuu where A:"s = trace_hide ta (ev ` A) @ uu \<and> u = uu @ uuu"
        by (auto simp add: append_eq_append_conv2, metis le_length_mono le_list_def)          
      with 2(1,2,4) 2(5)[rule_format, of ta uu] show ?thesis
        using front_tickFree_dw_closed by blast
    qed
  qed
next
  case 4 thus ?case
    by (auto, metis (mono_tags) Un_subset_iff is_processT4 sup.cobounded2 sup.coboundedI1)
next
  case 5 thus ?case
  proof(intro impI allI, auto, rule not_not[THEN iffD1], rule notI, simp, goal_cases)
    case (1 X Y t)
    from 1(3) 1(4)[THEN spec, of t, simplified] obtain c where A1:"c \<in> Y" and A2:"c \<notin> (ev`A)" 
                                                           and A3:"t@[c] \<in> T P"
      using is_processT5_S7'[of t "X \<union> (ev`A)" P Y] by (metis UnCI sup_commute sup_left_commute)
    hence "trace_hide t (ev ` A) @ [c] = trace_hide (t@[c]) (ev ` A)" by simp
    thus ?case using 1(1)[rule_format, OF A1] inf_hidden[of A "t@[c]", rotated, OF A3]
      by (metis (no_types, lifting) append.right_neutral append_T_imp_tickFree 
                                    front_tickFree_Nil is_processT5_S7 not_Cons_self2 rangeE)
  qed
next
  case 6 thus ?case
  proof (auto, goal_cases)
    case (1 s X t)
    hence "front_tickFree t" by (simp add:is_processT2)
    with 1(1) obtain t' where A:"t = t'@[tick]"
      by (metis filter_is_subset nonTickFree_n_frontTickFree non_tickFree_tick 
          subset_iff tickFree_append tickFree_def)
    with 1(1,2) have B:"s = trace_hide t' (ev ` A)" 
      by (auto simp add:tickFree_def split:if_splits)
    with A 1(1,2) is_processT6[of P, THEN spec, THEN spec, of t' "X \<union> ev ` A"] 
         is_processT4_empty[of t "ev ` A" P] show ?case
    by (auto simp add: Un_Diff split:if_splits) 
  next
    case (2 s X t u) 
    then obtain u' where A:"u = u'@[tick]"
      by (metis filter_is_subset nonTickFree_n_frontTickFree non_tickFree_tick           
          subset_iff tickFree_append tickFree_def)
     with 2(3) have B:"s = trace_hide t (ev ` A) @ u'" 
       by (auto simp add:tickFree_def split:if_splits)
     with 2(1,2,5) 2(4)[THEN spec, THEN spec, of t u'] show ?case
       using front_tickFree_dw_closed A by blast
  next
    case (3 s X u f x)
    then obtain u' where A:"u = u'@[tick]"
      by (metis filter_is_subset nonTickFree_n_frontTickFree non_tickFree_tick           
          subset_iff tickFree_append tickFree_def)
     with 3(3) have B:"s = trace_hide (f x) (ev ` A) @ u'" 
       by (auto simp add:tickFree_def split:if_splits)
     with 3(1,2,3,5,6,7) 3(4)[THEN spec, THEN spec, of "f x" u'] show ?case
       using front_tickFree_dw_closed[of u' "[tick]"] by auto
  qed
next
  case 7 thus ?case using front_tickFree_append by (auto, blast +)
next
  case 8 thus ?case by simp
next
  case 9 thus ?case 
  proof (intro allI impI, simp, elim exE, goal_cases)
    case (1 s t u)
    then obtain u' where "u = u'@[tick]"
      by (metis hiding_tickFree nonTickFree_n_frontTickFree non_tickFree_tick tickFree_append)
    with 1 show ?case
      apply(rule_tac x=t in exI, rule_tac x=u' in exI)
      using front_tickFree_dw_closed by auto
  qed
qed

lemma Rep_Abs_Hiding: "Rep_process (Abs_process 
                                  ({(s,X). \<exists> t. s = trace_hide t (ev`A) \<and> (t,X \<union> (ev`A)) \<in> F P} \<union>
                                   {(s,X). s \<in> div_hide P A}, div_hide P A))
                                  = ({(s,X). \<exists> t. s = trace_hide t (ev`A) \<and> (t,X \<union> (ev`A)) \<in> F P} \<union>
                                     {(s,X). s \<in> div_hide P A}, div_hide P A)"
  by (simp only:CollectI Rep_process Abs_process_inverse hiding_maintains_is_process)

subsection\<open>Projections\<close>

lemma F_hiding: "F(P \\ A) = {(s,X). \<exists> t. s = trace_hide t (ev`A) \<and> (t,X \<union> (ev`A)) \<in> F P} \<union>
                              {(s,X). s \<in> div_hide P A}"
  by (subst F_def, simp only: hiding_def Rep_Abs_Hiding FAILURES_def fst_conv)

lemma D_hiding: "D(P \\ A) = div_hide P A"
  by (subst D_def, simp only: hiding_def Rep_Abs_Hiding DIVERGENCES_def snd_conv)

lemma T_hiding: "T(P \\ A) = {s. \<exists>t. s = trace_hide t (ev`A) \<and>  (t, ev`A) \<in> F P} \<union> div_hide P A"
  apply (unfold T_def, simp only:Rep_Abs_Hiding hiding_def TRACES_def FAILURES_def fst_conv, auto)
     apply (metis is_processT sup.cobounded2)
    apply (metis FAILURES_def F_def NF_NT range_eqI)
   apply (metis sup.idem)
  by (metis FAILURES_def F_T F_def range_eqI)

subsection\<open>Continuity Rule\<close>

lemma mono_hiding[simp]: "(P::'a process) \<sqsubseteq> Q \<Longrightarrow> (P \\ A) \<sqsubseteq> (Q \\ A)" 
proof (auto simp only:le_approx_def D_hiding Ra_def F_hiding T_hiding, goal_cases)
  case (1 t u) thus ?case by blast
next
  case (2 u f xa) thus ?case 
    apply(rule_tac x="f xa" in exI, rule_tac x=u in exI)
    by (metis D_T Ra_def le_approx2T le_approx_def rangeI)
next
  case (3 x t) 
  hence A:"front_tickFree t" by (meson is_processT2)
  show ?case 
  proof(cases "tickFree t")
    case True thus ?thesis
      by (metis "3"(2) "3"(4) "3"(5) "3"(6) front_tickFree_charn mem_Collect_eq self_append_conv)
  next
    case False
    with A obtain t' where "t = t'@[tick]" using nonTickFree_n_frontTickFree by blast
    with 3 show ?thesis
      by (metis (no_types, lifting) filter.simps(1) filter.simps(2) front_tickFree_mono
          front_tickFree_Nil filter_append is_processT9 list.distinct(1) local.A mem_Collect_eq)
  qed
next
  case (4 x t) thus ?case using NF_ND by blast
next
  case (5 x t u) thus ?case by blast 
next
  case (6 x u f xa) thus ?case by (metis D_T Ra_def le_approx2T le_approx_def rangeI)
next
  case (7 x)
  from 7(4) have A:"x \<in> min_elems (div_hide P A)" by simp
  from elem_min_elems[OF 7(4), simplified] obtain t u 
    where B1:"x = trace_hide t (ev ` A) @ u" and B2:"tickFree t" and B3:"front_tickFree u" and 
             B4:"(t \<in> D P \<or> (\<exists>(f:: nat \<Rightarrow> 'a event list). strict_mono f \<and> (\<forall>i. f i \<in> T P) \<and>
             (\<forall>i. trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A)) \<and> t \<in> range f))" by blast
  show ?case proof(cases "t \<in> D P")
    case True
    then obtain t' t'' where C1:"t'@t''=t" and C2:"t' \<in> min_elems (D P)" by (metis min_elems_charn)
    hence C3:"trace_hide t' (ev ` A) \<in> div_hide P A" 
      apply (simp, rule_tac x=t' in exI, rule_tac x="[]" in exI, simp)
      using B2 elem_min_elems tickFree_append by blast 
    from C1 B1 have D1:"trace_hide t' (ev ` A) @ trace_hide t'' (ev ` A) = trace_hide t (ev ` A)"
      by fastforce
    from B1 C1 D1 min_elems_no[OF A C3] have E1:"x=trace_hide t' (ev ` A)"
      by (metis (no_types, lifting) append.assoc le_list_def)
    with B1 B2 B3 C1 D1 7(5)[simplified, rule_format, of "t'" "[]"] 
      have E2:"(\<forall>(f:: nat \<Rightarrow> 'a event list). strict_mono f \<longrightarrow> (\<exists>i. f i \<notin> T Q) \<or>
              (\<exists>i. trace_hide (f i) (ev ` A) \<noteq> trace_hide (f 0) (ev ` A)) \<or> t' \<notin> range f)"
      apply simp
      using front_tickFree_append hiding_tickFree tickFree_append by blast
    with E1 7(3) C2 inf_hidden[of A t' Q] show ?thesis 
      by (metis (no_types, lifting) contra_subsetD)
  next
    case False
    from B1 B2 B3 B4 have  C:"trace_hide t (ev ` A) \<in> div_hide P A"
      by (simp, rule_tac x=t in exI, rule_tac x="[]" in exI, simp)
    from B1 min_elems_no[OF A C] have E1:"x=trace_hide t (ev ` A)"
      using le_list_def by auto
    from B4 False 7(2)[rule_format, of t, OF False] have "t \<in> T Q" using F_T T_F by blast
    with E1 7(5)[simplified, rule_format, of t "[]", simplified, OF E1 B2] inf_hidden[of A t Q] show ?thesis
      by metis
  qed
qed

lemma cont_hiding1 : "chain Y \<Longrightarrow> chain (\<lambda> i. (Y i \\ A))"
  by (simp add: po_class.chain_def)

lemma KoenigLemma: 
  assumes *:"infinite (Tr::'a list set)" and **:"\<forall>i. finite{t. \<exists>t'\<in>Tr. t = take i t'}"
  shows "\<exists>(f::nat \<Rightarrow> 'a list). strict_mono f \<and> range f \<subseteq> {t. \<exists>t'\<in>Tr. t \<le> t'}"
proof -
  define Tr' where "Tr' = {t. \<exists>t'\<in>Tr. t \<le> t'}" (* prefix closure *)
  have a:"infinite Tr'"
    by (metis (mono_tags, lifting) * Tr'_def infinite_super mem_Collect_eq order_refl subsetI) 
  { fix i
    have "{t \<in> Tr'. length t = i} \<subseteq> {t. \<exists>t'\<in>Tr. t = take i t'}" 
      by (auto simp add:Tr'_def, metis append_eq_conv_conj le_list_def)
    with ** have "finite({t\<in>Tr'. length t = i})" using infinite_super by blast     
  } note b=this
  { fix t
    define E where "E = {e |e. t@[e]\<in> Tr'}" 
    have aa:"finite E"
      proof - 
        have "inj_on (\<lambda>e. t @ [e]) E" by (simp add: inj_on_def)
        
        with b[of "Suc (length t)"] inj_on_finite[of "\<lambda>e. t@[e]" E "{t' \<in> Tr'. length t' = Suc (length t)}"]
        show ?thesis  by (simp add: E_def image_Collect_subsetI)
      qed 
    hence bb:"finite {t@[e] |e. e\<in>E}" by simp
    have "{t'\<in>Tr'. t < t'} = {t@[e] |e. e\<in>E} \<union> (\<Union>e\<in>E. {t'\<in>Tr'. t@[e] < t'})"
      proof (auto simp add:Let_def E_def Tr'_def, goal_cases)
        case (1 x xa)
        then obtain u e where "x = t @ [e] @ u"
          by (metis A append_Cons append_Nil append_Nil2 le_list_def list.exhaust) 
        with 1 1(4)[rule_format, of e] show ?case by (metis append_assoc le_list_def less_list_def)
      next
        case (2 x xa xb xc)
        thus ?case by (meson less_self less_trans) 
      qed     
    with aa bb have "infinite {t'\<in>Tr'. t < t'} \<Longrightarrow> \<exists>e. infinite {t'\<in>Tr'. t@[e] < t'}" by auto
  } note c=this
  define ff where d:"ff =rec_nat [] (\<lambda>i t. (let e = SOME e. infinite {t'\<in>Tr'. t@[e] < t'} in t @ [e]))"
  hence dd:"\<forall>n. ff (Suc n) > ff n" by simp (* funny *)
  hence e:"strict_mono ff" by (simp add: lift_Suc_mono_less strict_monoI)
  { fix n
    have "ff n \<in> Tr' \<and> infinite {t' \<in> Tr'. ff n < t'}" 
    proof(induct n)
      case 0
      from a Tr'_def have  "Tr' = {t' \<in> Tr'. [] < t'} \<union> {[]}" by (auto simp add: le_neq_trans)
      with a have "infinite {t' \<in> Tr'. [] < t'}"
        by (metis (no_types, lifting) finite.emptyI finite.insertI finite_UnI)
      with d Tr'_def show ?case by auto        
    next
      case (Suc n)
      from d have "ff (Suc n) = (let e = SOME e. infinite {t'\<in>Tr'. ff n@[e] < t'} in ff n @ [e])" by simp 
      with c[rule_format, of "ff n"] obtain e where 
        a1:"ff (Suc n) = (ff n) @ [e] \<and> infinite {t' \<in> Tr'. ff n @ [e] < t'}"
        by (metis (no_types, lifting) Suc.hyps someI_ex)
      then obtain i where "i \<in> Tr' \<and> ff (Suc n) < i" using not_finite_existsD by auto 
      with Tr'_def have "ff (Suc n) \<in> Tr'" using dual_order.trans less_imp_le by fastforce
      with a1 show ?case by simp
    qed
  } note g=this
  hence h:"range ff \<subseteq> Tr'" by auto
  show ?thesis using Tr'_def e h by blast
qed

lemma div_hiding_lub :  "finite (A::'a set) \<Longrightarrow> chain Y \<Longrightarrow> D (\<Squnion> i. (Y i \\ A)) \<subseteq> D ((\<Squnion> i. Y i) \\ A)"
proof (auto simp add:limproc_is_thelub cont_hiding1 D_hiding T_hiding D_LUB T_LUB, goal_cases)
  case (1 x)
  { fix xa t u f
    assume a:"front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and>
              isInfHiddenRun f (Y xa) A \<and> (\<forall> i. f i \<notin> D (Y xa)) \<and> t \<in> range f"
    hence "(\<forall>i n. f i \<in> T (Y n))" using 1(2) NT_ND chain_lemma le_approx2T by blast
    with a have ?case by blast
  } note aa=this 
  { fix xa t u f j
    assume a:"front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and> 
              isInfHiddenRun f (Y xa) A \<and> (f j \<in> D (Y xa)) \<and> t \<in> range f"
    hence "\<exists>t u. front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> D (Y xa)"
      apply(rule_tac x="f j" in exI, rule_tac x=u in exI) 
      using hiding_tickFree[of "f j" A] hiding_tickFree[of t A] by (metis imageE)
  } note bb=this
  have cc: "\<forall>xa. \<exists>t u. front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> D (Y xa)
           \<Longrightarrow> ?case" (is "\<forall>xa. \<exists>t. ?S t xa \<Longrightarrow> ?case")
    proof -
      assume dd:"\<forall>xa. \<exists>t u. front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> D (Y xa)"
             (is "\<forall>xa. \<exists>t. ?S t xa")
      define f where "f = (\<lambda>n. SOME t. ?S t n)"
      thus ?case 
      proof (cases "finite(range f)")
        case True
        obtain t where gg:"infinite (f -` {t})" using f_def True inf_img_fin_dom by blast 
        then obtain k where "f k = t" using finite_nat_set_iff_bounded_le by blast
        then obtain u where uu:"front_tickFree u \<and> x = trace_hide t (ev ` A) @ u \<and> tickFree t"
          using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] by blast
        { fix m
          from gg obtain n where gg:"n \<ge> m \<and> n \<in> (f -` {t})"
            by (meson finite_nat_set_iff_bounded_le nat_le_linear)
          hence "t \<in> D (Y n)" using f_def dd[rule_format, of n] some_eq_ex[of "\<lambda>t. ?S t n"] by auto
          with gg 1(2) have "t \<in> D (Y m)" by (meson contra_subsetD le_approx_def po_class.chain_mono)
        }
        with gg uu show ?thesis by blast
      next
        case False
        { fix t
          assume "t \<in> range f"
          then obtain k where "f k = t" using finite_nat_set_iff_bounded_le by blast
          then obtain u where uu:"front_tickFree u \<and> x = trace_hide t (ev ` A) @ u \<and> tickFree t"
            using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] by blast
          hence "set t \<subseteq> set x \<union> (ev ` A)" by auto
        } note ee=this
        { fix i
          have "finite {(take i t)|t. t \<in> range f}" 
          proof(induct i, simp)
            case (Suc i)
            have ff:"{take (Suc i) t|t. t \<in> range f} \<subseteq> {(take i t)|t. t \<in> range f} \<union>
                        (\<Union>e\<in>(set x \<union> (ev ` A)). {(take i t)@[e]|t. t \<in> range f})" (is "?AA \<subseteq> ?BB")
              proof
                fix t
                assume "t \<in> ?AA"
                then obtain t' where hh:"t' \<in> range f \<and> t = take (Suc i) t'" 
                  using finite_nat_set_iff_bounded_le by blast
                with ee[of t'] show "t \<in> ?BB"
                  proof(cases "length t' > i")
                    case True
                    hence ii:"take (Suc i) t' = take i t' @ [t'!i]" by (simp add: take_Suc_conv_app_nth)
                    with ee[of t'] have "t'!i \<in> set x \<union> (ev ` A)" 
                      by (meson True contra_subsetD hh nth_mem)
                    with ii hh show ?thesis by blast
                  next
                    case False
                    hence "take (Suc i) t' = take i t'" by fastforce
                    with hh show ?thesis by auto
                  qed
              qed
            { fix e 
              have "{x @ [e] |x. \<exists>t. x = take i t \<and> t \<in> range f} = {take i t' @ [e] |t'. t' \<in> range f}"
                by auto
              hence "finite({(take i t') @ [e] |t'. t'\<in>range f})"
                using finite_image_set[of _ "\<lambda>t. t@[e]", OF Suc] by auto 
            } note gg=this
            have "finite(set x \<union> (ev ` A))" using 1(1) by simp
            with ff gg Suc show ?case by (metis (no_types, lifting) finite_UN finite_Un finite_subset)
          qed
        } note ff=this
        hence "\<forall>i. {take i t |t. t \<in> range f} = {t. \<exists>t'. t = take i (f t')}" by auto
        with KoenigLemma[of "range f", OF False] ff
        obtain f' where gg:"strict_mono (f':: nat \<Rightarrow> 'a event list) \<and> 
                                            range f' \<subseteq> {t. \<exists>t'\<in>range f. t \<le> t'}" by auto
        { fix n
          define M where "M = {m. f' n \<le> f m }"
          assume "finite M"
          hence l1:"finite {length (f m)|m. m \<in> M}" by simp
          obtain lm where l2:"lm = Max {length (f m)|m. m \<in> M}" by blast
          { fix k
            have "length (f' k) \<ge> k" 
              by(induct k, simp, metis (full_types) gg lessI less_length_mono linorder_not_le 
                                        not_less_eq_eq order_trans strict_mono_def)
          }
          with gg obtain m where r1:"length (f' m) > lm" by (meson lessI less_le_trans)
          from gg obtain r where r2:"f' (max m n) \<le> f r" by blast
          with gg have r3: "r \<in> M" 
            by (metis (no_types, lifting) M_def max.bounded_iff mem_Collect_eq order_refl 
                                          order_trans strict_mono_less_eq)
          with l1 l2 have f1:"length (f r) \<le> lm" using Max_ge by blast
          from r1 r2 have f2:"length (f r) > lm"
            by (meson dual_order.strict_trans1 gg le_length_mono max.bounded_iff order_refl 
                      strict_mono_less_eq) 
          from f1 f2 have False by simp
        } note ii=this
        { fix i n
          from ii obtain m where jj:"m \<ge> n \<and> f m \<ge> f' i" 
            by (metis finite_nat_set_iff_bounded_le mem_Collect_eq nat_le_linear)
          have kk: "(f m) \<in> D (Y m)" using f_def dd[rule_format, of m] some_eq_ex[of "\<lambda>t. ?S t m"] by auto 
          with jj gg have "(f' i) \<in> T (Y m)" by (meson D_T is_processT3_ST_pref)
          with jj 1(2) have  "(f' i) \<in> T (Y n)" using D_T le_approx2T po_class.chain_mono by blast
        } note jj=this
        from gg have kk:"mono (\<lambda>n. trace_hide (f' n) (ev ` A))" 
          unfolding strict_mono_def mono_def
          by (metis (no_types, lifting) filter_append gg le_list_def mono_def strict_mono_mono)
        { fix n
          from gg obtain k r where "f k = f' n @ r" by (metis ii le_list_def not_finite_existsD)
          hence "trace_hide (f' n) (ev ` A) \<le> x" 
            using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] le_list_def by auto blast
        } note ll=this
        { assume llll:"\<forall>m. \<exists>n. trace_hide (f' n) (ev ` A) > trace_hide (f' m) (ev ` A)"
          hence lll:"\<forall>m. \<exists>n. length (trace_hide (f' n) (ev ` A)) > length (trace_hide (f' m) (ev ` A))"
            using less_length_mono by blast
          define ff where lll':"ff = rec_nat (length (trace_hide (f' 0) (ev ` A))) 
                (\<lambda>i t. (let n = SOME n. (length (trace_hide (f' n) (ev ` A))) > t 
                         in length (trace_hide (f' n) (ev ` A))))"
          { fix n
            from lll' lll[rule_format, of n] have "ff (Suc n) > ff n" 
              apply simp apply (cases n)
              apply (metis (no_types, lifting) old.nat.simps(6) someI_ex)
              by (metis (no_types, lifting) llll less_length_mono old.nat.simps(7) someI_ex)
          } note lll''=this
          with lll'' have "strict_mono ff" by (simp add: lll'' lift_Suc_mono_less strict_monoI)
          hence lll''':"infinite(range ff)" using finite_imageD strict_mono_imp_inj_on by auto
          from lll lll' have "range ff \<subseteq> range (\<lambda>n. length (trace_hide (f' n) (ev ` A)))" 
            by (auto, metis (mono_tags, lifting) old.nat.exhaust old.nat.simps(6) old.nat.simps(7) range_eqI)
          with lll''' have "infinite (range (\<lambda>n. length (trace_hide (f' n) (ev ` A))))"
            using finite_subset by auto
          hence "\<exists>m. length (trace_hide (f' m) (ev ` A)) > length x"
            using finite_nat_set_iff_bounded_le by (metis (no_types, lifting) not_less rangeE)
          with ll have False using le_length_mono not_less by blast
        }
        then obtain m where mm:"\<forall>n. trace_hide (f' n) (ev ` A) \<le> trace_hide (f' m) (ev ` A)"
          by (metis (mono_tags, lifting) A kk le_cases mono_def)
        with gg obtain k where nn:"f k \<ge> f' m" by blast
        then obtain u where oo:"front_tickFree u \<and> x = trace_hide (f' m) (ev ` A) @ u \<and> tickFree (f' m)"
          using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] 
          by (auto, metis (no_types, lifting) contra_subsetD filter_is_subset front_tickFree_append 
                          front_tickFree_mono le_list_def ll tickFree_Nil tickFree_append 
                          tickFree_def tickFree_implies_front_tickFree)        
        show ?thesis
          apply(rule_tac x="f' m" in exI, rule_tac x=u in exI)
          apply(simp add:oo, rule disjI2, rule_tac x="\<lambda>n. f' (n + m)" in exI)
          using gg jj kk mm apply (auto simp add: strict_mono_def dual_order.antisym mono_def)
          by (metis plus_nat.add_0 rangeI)
      qed
    qed
  show ?case 
  proof (cases "\<exists> xa t u f. front_tickFree u \<and> tickFree t \<and> (\<forall> i. f i \<notin> D (Y xa)) \<and> t \<in> range f \<and>
                            x = trace_hide t (ev ` A) @ u \<and> isInfHiddenRun f (Y xa) A")
    case True
    then show ?thesis using aa by blast
  next
    case False
    have dd:"\<forall>xa. \<exists>t u. front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and>
             (t \<in> D (Y xa) \<or> (\<exists>f. isInfHiddenRun f (Y xa) A \<and> (\<exists>i. f i \<in> D (Y xa)) \<and> t \<in> range f))" 
            (is "\<forall>xa. ?dd xa")
      proof (rule_tac allI)
        fix xa
        from 1(3) obtain t u where 
              "front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and>
              (t \<in> D (Y xa) \<or> (\<exists>f. isInfHiddenRun f (Y xa) A \<and> t \<in> range f))" 
          by blast
        thus "?dd xa"
          apply(rule_tac x=t in exI, rule_tac x=u in exI, intro conjI, simp_all, elim conjE disjE, simp_all)
          using 1(1) False NT_ND chain_lemma le_approx2T by blast
      qed
    hence ee:"\<forall>xa. \<exists>t u. front_tickFree u \<and> tickFree t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> D (Y xa)"
      using bb by blast
    with cc show ?thesis by simp
  qed
qed

lemma cont_hiding2 : "finite A \<Longrightarrow> chain Y \<Longrightarrow> ((\<Squnion> i. Y i) \\ A) = (\<Squnion> i. (Y i \\ A))"
proof(auto simp add:limproc_is_thelub cont_hiding1 Process_eq_spec 
                    D_hiding Ra_def F_hiding T_hiding F_LUB  D_LUB T_LUB, goal_cases)
  case (1 b x t u) thus ?case by blast
next
  case (2 b x u f xa) thus ?case by blast
next
  case (3 s X)
  hence "s \<notin> D ((\<Squnion> i. Y i) \\ A)" 
    by (simp add:limproc_is_thelub cont_hiding1 F_LUB  D_LUB T_LUB D_hiding)
  with 3(1,2) obtain n where a:"s \<notin> D (Y n \\ A)"
    by (metis (no_types, lifting) D_LUB_2 div_hiding_lub subsetCE limproc_is_thelub cont_hiding1) 
  with 3(3) obtain t where b:"s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> F (Y n)" 
    unfolding D_hiding by blast
  hence c:"front_tickFree t" using is_processT2 by blast
  have d:"t \<notin> D(Y n)"
    proof(cases "tickFree t")
      case True
      with a b show ?thesis using front_tickFree_Nil 
        by (simp add:D_hiding)
    next
      case False
      with c obtain t' where "t = t'@[tick]" using nonTickFree_n_frontTickFree by blast
      with a b show ?thesis
        apply(simp add:D_hiding, erule_tac x=t' in allE, erule_tac x="[tick]" in allE, simp)
        by (metis event.distinct(1) filter.simps(1) front_tickFree_implies_tickFree imageE is_processT)
    qed
    with b show ?case using 3(2) NF_ND chain_lemma proc_ord2a by blast   
next
  case (4 xa t u) thus ?case by blast
next
  case (5 xa u f xb) thus ?case by blast
next
  case (6 s)
  hence "s \<in> D (\<Squnion> i. (Y i \\ A))" 
    by (simp add:limproc_is_thelub cont_hiding1 6(1) D_hiding D_LUB)
  with div_hiding_lub[OF 6(1,2)] have  "s \<in> D ((\<Squnion>i. Y i) \\ A)" by blast
  thus ?case by (simp add:limproc_is_thelub 6(2) D_hiding D_LUB T_LUB)
qed

lemma cont_hiding_base[simp] : "finite A \<Longrightarrow> cont (\<lambda>x. x \\ A)"
  by (simp add: cont_def cont_hiding1 cont_hiding2 cpo_lubI)

lemma hiding_cont[simp]:  "finite A \<Longrightarrow> cont f \<Longrightarrow> cont (\<lambda>x. f x \\ A)"
  by (rule_tac f=f in cont_compose, simp_all)

end