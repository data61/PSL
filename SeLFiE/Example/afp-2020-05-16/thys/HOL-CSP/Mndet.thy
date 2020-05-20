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

theory Mndet
  imports Process Stop Mprefix Ndet
begin

section\<open>Multiple non deterministic operator\<close>

definition
        mndet      :: "['\<alpha> set, '\<alpha> \<Rightarrow> '\<alpha> process] \<Rightarrow> '\<alpha> process" 
        where   "mndet A P \<equiv> if A = {} 
                             then STOP
                             else Abs_process(\<Union> x\<in>A.  F(x \<rightarrow> P x),
                                              \<Union> x\<in>A.  D(x \<rightarrow> P x))"
syntax
  "_Mndet"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a process \<Rightarrow> 'a process"      ("(3\<sqinter>_\<in>_ \<rightarrow> / _)" [0, 0, 10] 10)

translations
  "\<sqinter>x\<in>A\<rightarrow> P" \<rightleftharpoons> "CONST mndet A (\<lambda>x. P)"

lemma mt_mndet[simp] : "mndet {} P = STOP"
  unfolding mndet_def   by simp

lemma mndet_is_process : "A \<noteq> {} \<Longrightarrow> is_process (\<Union> x\<in>A. F(x \<rightarrow> P x), \<Union> x\<in>A.   D(x \<rightarrow> P x))"
  unfolding is_process_def FAILURES_def DIVERGENCES_def
  apply auto
  using is_processT1 apply auto[1]
  using is_processT2 apply blast
  using is_processT3_SR apply blast
  using is_processT4 apply blast  
  using is_processT5_S1 apply blast
  using is_processT6 apply blast
  using is_processT7 apply blast
  using NF_ND apply auto[1]
  using is_processT9 by blast  

lemma T_mdet1 : "T(mndet {} P) = {[]}"
  unfolding mndet_def by(simp add: T_STOP)

lemma rep_abs_mndet[simp]: "A \<noteq> {} \<Longrightarrow>
     (Rep_process (Abs_process(\<Union>x\<in>A. F (x \<rightarrow> P x),\<Union>x\<in>A. D (x \<rightarrow> P x)))) = 
      (\<Union>x\<in>A. F (x \<rightarrow> P x), \<Union>x\<in>A. D (x \<rightarrow> P x))"
  apply(subst Process.process.Abs_process_inverse)
  by(auto intro: mndet_is_process[simplified])
  
lemma T_mndet: "A\<noteq>{} \<Longrightarrow> T(mndet A P) = (\<Union> x\<in>A. T (x \<rightarrow> P x))"
  unfolding mndet_def
  apply(simp, subst T_def, simp add: TRACES_def FAILURES_def)
  apply(auto intro: mndet_is_process[simplified])
  unfolding TRACES_def FAILURES_def apply(cases "A = {}") 
   apply(auto intro: F_T D_T simp: Nil_elem_T)
  using NF_NT by blast

lemma F_mndet1 : "F(mndet {} P) = {(s, X). s = []}"
  unfolding mndet_def by(simp add: F_STOP)

lemma F_mndet: "A\<noteq>{} \<Longrightarrow> F(mndet A P) = (\<Union> x\<in>A. F (x \<rightarrow> P x))"
  unfolding mndet_def 
  by(simp, subst F_def, auto simp : FAILURES_def F_mndet1)


lemma D_mndet1 : "D(mndet {} P) = {}"
  unfolding mndet_def by(simp add: D_STOP)

lemma D_mndet : "A\<noteq>{} \<Longrightarrow> D(mndet A P) = (\<Union> x\<in>A. D (x \<rightarrow> P x))"
  unfolding mndet_def 
  apply(simp, subst D_def, subst Process.process.Abs_process_inverse)
   by(auto intro: mndet_is_process[simplified] simp: DIVERGENCES_def)
  

text\<open> Thus we know now, that mndet yields processes. Direct consequences are the following
  distributivities: \<close>

lemma mndet_unit : "(\<sqinter> x \<in> {a} \<rightarrow> P x)  = (a \<rightarrow> P a)" 
  by(auto simp : Process.Process_eq_spec F_mndet D_mndet)

lemma mndet_distrib : "A \<noteq>{} \<Longrightarrow> B \<noteq>{} \<Longrightarrow> (\<sqinter> x \<in> A\<union>B \<rightarrow> P x) = ((\<sqinter> x \<in> A \<rightarrow> P x) \<sqinter> (\<sqinter> x \<in> B \<rightarrow> P x))"
  by(auto simp : Process.Process_eq_spec F_ndet D_ndet F_mndet D_mndet)

text\<open> The two lemmas @{thm mndet_unit} and @{thm mndet_distrib} together give us that @{const mndet} 
      can be represented by a fold in the finite case. \<close>                                         

lemma mndet_distrib_unit : "A-{a} \<noteq> {}  \<Longrightarrow> (\<sqinter> x \<in> insert a A \<rightarrow> P x) = ((a \<rightarrow> P a) \<sqinter> (\<sqinter> x \<in> A-{a} \<rightarrow> P x))"
  by (metis Un_Diff_cancel insert_is_Un insert_not_empty mndet_distrib mndet_unit)

subsection\<open>Finite case Continuity\<close>

text\<open> This also implies that mndet is continuous for the
      finite @{term A} and an arbitrary body @{term f}: \<close>

lemma Mndet_cont_finite[simp]:
assumes "finite A"
 and    "\<And>x. cont (f x)"
shows   "cont (\<lambda>y. \<sqinter> z \<in> A \<rightarrow> f z y)"
proof(rule Finite_Set.finite_induct[OF `finite A`])
  show  "cont (\<lambda>y. \<sqinter>z\<in>{} \<rightarrow> f z y)" by auto
next
  fix A fix a 
  assume "cont (\<lambda>y. \<sqinter>z\<in>A \<rightarrow> f z y)" and "a \<notin> A"
  show   "cont (\<lambda>y. \<sqinter>z\<in>insert a A \<rightarrow> f z y)"
  proof(cases "A={}")
    case True
    then show ?thesis by(simp add: mndet_unit True `\<And>x. cont (f x)`)
  next
    case False
    have *  : "A-{a} \<noteq> {}" by (simp add: False \<open>a \<notin> A\<close>)
    have ** : "A-{a} = A"  by (simp add: \<open>a \<notin> A\<close>)
    show ?thesis
      apply(simp only: mndet_distrib_unit[OF *], simp only: **)  
      by (simp add: \<open>cont (\<lambda>y. \<sqinter>z\<in>A \<rightarrow> f z y)\<close> assms(2))
  qed
qed

subsection\<open>General case Continuity\<close>

lemma mono_Mndet[simp] : "monofun (mndet (A::'a set))" 
proof(cases "A={}")
  case True
  then show ?thesis by(auto simp: monofun_def)
next
  case False
  then show ?thesis apply(simp add: monofun_def, intro allI impI) 
    unfolding le_approx_def
    proof(simp add:T_mndet F_mndet D_mndet, intro conjI)
      fix x::"'a \<Rightarrow> 'a process" and y::"'a \<Rightarrow> 'a process"  
      assume "A \<noteq> {}" and "x \<sqsubseteq> y"
      show "(\<Union>x\<in>A.  D (x\<rightarrow> y x)) \<subseteq> (\<Union>xa\<in>A. D (xa \<rightarrow> x xa))" 
        by (metis (mono_tags, lifting) SUP_mono \<open>x \<sqsubseteq> y\<close> fun_below_iff le_approx1 mono_Mprefix0 write0_def)
    next
      fix x::"'a \<Rightarrow> 'a process" and y::"'a \<Rightarrow>  'a process"  
      assume *:"A \<noteq> {}" and **:"x \<sqsubseteq> y"
      have *** : "\<And>z. z \<in> A \<Longrightarrow> x z \<sqsubseteq> y z " by (simp add: \<open>x \<sqsubseteq> y\<close> fun_belowD)
      with * show "\<forall>s. (\<forall>xa\<in>A. s \<notin> D (xa \<rightarrow> x xa)) \<longrightarrow> Ra (mndet A x) s = Ra (mndet A y) s"
        unfolding Ra_def
        by (auto simp:proc_ord2a mono_Mprefix0 write0_def F_mndet) (meson le_approx2 mono_Mprefix0 write0_def)+
    next
      fix x::"'a \<Rightarrow> 'a process" and y::"'a \<Rightarrow>  'a process"  
      assume *:"A \<noteq> {}" and "x \<sqsubseteq> y"
      have *** : "\<And>z. z \<in> A \<Longrightarrow> (z \<rightarrow> x z) \<sqsubseteq> (z \<rightarrow> y z) "
        by (metis \<open>x \<sqsubseteq> y\<close> fun_below_iff mono_Mprefix0 write0_def)
      with * show "min_elems (\<Union>xa\<in>A. D (xa \<rightarrow> x xa)) \<subseteq> (\<Union>x\<in>A. T (x \<rightarrow> y x))"
        unfolding min_elems_def apply auto 
        by (metis Set.set_insert elem_min_elems insert_subset le_approx3 le_less min_elems5)
    qed
qed  

lemma mndet_chainpreserving: "chain Y \<Longrightarrow> chain (\<lambda>i. (\<sqinter> z \<in> A \<rightarrow> Y i z))"
  apply(rule chainI, rename_tac i)
  apply(frule_tac i="i" in chainE)
  by (simp add: below_fun_def mono_Mprefix0 write0_def monofunE)

lemma contlub_Mndet : "contlub (mndet A)"
proof(cases "A={}")
  case True
  then show ?thesis by(auto simp: contlub_def)
next
  case False
  show ?thesis
  proof(rule contlubI, rule proc_ord_proc_eq_spec)
    fix Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'a process"
    assume a:"chain Y"
    show "(\<sqinter>x\<in>A \<rightarrow> (\<Squnion>i. Y i) x) \<sqsubseteq> (\<Squnion>i. \<sqinter>x\<in>A \<rightarrow> Y i x)"
    proof(simp add:le_approx_def, intro conjI allI impI)
      show "D (\<Squnion>i. \<sqinter>x\<in>A \<rightarrow> Y i x) \<subseteq> D (\<sqinter>x\<in>A \<rightarrow> Lub Y x)"
        using a False D_LUB[OF mndet_chainpreserving[OF a], of A] 
              limproc_is_thelub[OF mndet_chainpreserving[OF a], of A] 
        apply (auto simp add:write0_def D_Mprefix D_LUB[OF ch2ch_fun[OF a]] limproc_is_thelub_fun[OF a] D_mndet) 
        by (metis (mono_tags, hide_lams) event.inject)
    next
      fix s :: "'a event list"
      assume "s \<notin> D (\<sqinter>x\<in>A \<rightarrow> Lub Y x)"
      show "Ra (\<sqinter>x\<in>A \<rightarrow> Lub Y x) s = Ra (\<Squnion>i. \<sqinter>x\<in>A \<rightarrow> Y i x) s" 
        unfolding Ra_def 
        using a False F_LUB[OF mndet_chainpreserving[OF a], of A] 
              limproc_is_thelub[OF mndet_chainpreserving[OF a], of A] 
        apply (auto simp add:write0_def F_Mprefix F_LUB[OF ch2ch_fun[OF a]] limproc_is_thelub_fun[OF a] F_mndet)
        by (metis (mono_tags, hide_lams) event.inject)
    next
      show "min_elems (D (\<sqinter>x\<in>A \<rightarrow> Lub Y x)) \<subseteq> T (\<Squnion>i. \<sqinter>x\<in>A \<rightarrow> Y i x)"
        unfolding min_elems_def
        using a False limproc_is_thelub[OF mndet_chainpreserving[OF a], of A]
              D_LUB[OF mndet_chainpreserving[OF a], of A] 
              F_LUB[OF mndet_chainpreserving[OF a], of A] 
        by (auto simp add:D_T write0_def D_Mprefix F_Mprefix D_mndet F_mndet D_LUB[OF ch2ch_fun[OF a]] F_LUB[OF ch2ch_fun[OF a]] limproc_is_thelub_fun[OF a])
    qed
  next
    fix Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'a process"
    assume a:"chain Y"      
    show "D (\<sqinter>x\<in>A \<rightarrow> (\<Squnion>i. Y i) x) \<subseteq> D (\<Squnion>i. \<sqinter>x\<in>A \<rightarrow> Y i x)"
        using a False D_LUB[OF mndet_chainpreserving[OF a], of A] 
              limproc_is_thelub[OF mndet_chainpreserving[OF a], of A] 
        by (auto simp add:write0_def D_Mprefix D_mndet D_LUB[OF ch2ch_fun[OF a]] limproc_is_thelub_fun[OF a])
  qed
qed

lemma Mndet_cont[simp]: "(\<And>x. cont (f x)) \<Longrightarrow> cont (\<lambda>y. (\<sqinter> z \<in> A \<rightarrow> (f z y)))"
  apply(rule_tac f = "\<lambda>z y. (f y z)" in Cont.cont_compose, rule monocontlub2cont) 
  by (auto intro: mono_Mndet contlub_Mndet Fun_Cpo.cont2cont_lambda)

end