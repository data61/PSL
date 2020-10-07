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

chapter\<open> Annex: Refinement Example with Buffer over infinite Alphabet\<close>

theory     CopyBuffer
 imports    "Assertions"
begin 

section\<open> Defining the Copy-Buffer Example \<close>

datatype 'a channel = left 'a | right 'a | mid 'a | ack

definition SYN  :: "('a channel) set"
where     "SYN  \<equiv> (range mid) \<union> {ack}"

definition COPY :: "('a channel) process"
where     "COPY \<equiv> (\<mu> COPY. left`?`x \<rightarrow> (right`!`x \<rightarrow> COPY))"

definition SEND :: "('a channel) process"
where     "SEND \<equiv> (\<mu> SEND. left`?`x \<rightarrow> (mid`!`x \<rightarrow>( ack \<rightarrow> SEND)))"

definition REC  :: "('a channel) process"
where     "REC  \<equiv> (\<mu> REC. mid`?`x \<rightarrow> (right`!`x \<rightarrow> (ack \<rightarrow> REC)))"


definition SYSTEM :: "('a channel) process"
where     "SYSTEM \<equiv> ((SEND \<lbrakk> SYN \<rbrakk> REC) \\ SYN)"


section\<open> The Standard Proof \<close>

subsection\<open> Channels and Synchronization Sets\<close>

text\<open> First part: abstract properties for these events to SYN.
       This kind of stuff could be automated easily by some
       extra-syntax for channels and SYN-sets. \<close>

lemma [simp]: "left x  \<notin>  SYN"
    by(auto simp: SYN_def)
  
lemma [simp]: "right x  \<notin>  SYN"
    by(auto simp: SYN_def)

lemma [simp]: "ack \<in> SYN"
    by(auto simp: SYN_def)

lemma [simp]: "mid x \<in> SYN"
    by(auto simp: SYN_def)

lemma [simp]: "inj mid"  
  by(auto simp: inj_on_def)

lemma "finite (SYN:: 'a channel set) \<Longrightarrow> finite {(t::'a). True}"
  by (metis (no_types) SYN_def UNIV_def channel.inject(3) finite_Un finite_imageD inj_on_def)

subsection\<open> Definitions by Recursors \<close>

text\<open> Second part: Derive recursive process equations, which
       are easier to handle in proofs. This part IS actually
       automated if we could reuse the fixrec-syntax below. \<close>

lemma COPY_rec:
  "COPY = (left`?`x \<rightarrow> (right`!`x \<rightarrow> COPY))"
  by(simp add: COPY_def,rule trans, rule fix_eq, simp)
  
lemma SEND_rec: 
  "SEND = (left`?`x \<rightarrow> (mid`!`x \<rightarrow> (ack \<rightarrow> SEND)))"
  by(simp add: SEND_def,rule trans, rule fix_eq, simp)

lemma REC_rec:
  "REC = (mid`?`x \<rightarrow> (right`!`x \<rightarrow> (ack \<rightarrow> REC)))"
  by(simp add: REC_def,rule trans, rule fix_eq, simp)


subsection\<open> A Refinement Proof \<close>

text\<open> Third part: No comes the proof by fixpoint induction. 
       Not too bad in automation considering what is inferred,
       but wouldn't scale for large examples. \<close>

lemma impl_refines_spec : "COPY \<sqsubseteq> SYSTEM"
  apply(simp add: SYSTEM_def COPY_def)
  apply(rule fix_ind, simp_all)
  by (subst SEND_rec, subst REC_rec, simp add: sync_rules hide_rules mono_rules)

lemma spec_refines_impl : 
  assumes fin: "finite (SYN:: 'a channel set)"
  shows        "SYSTEM \<sqsubseteq> (COPY :: 'a channel process)"
  apply(simp add: SYSTEM_def SEND_def)
  apply(rule fix_ind, simp_all)
    using adm_below hiding_cont[of SYN "\<lambda>(a:: 'a channel process). (a \<lbrakk>SYN\<rbrakk> REC)", OF fin] 
      apply (simp add: contI cont_left_sync chain_Sync1 thelubE)
   apply (simp add: hide_set_bot par_Int_bot sync_commute)
  by (subst COPY_rec, subst REC_rec, simp add:sync_rules hide_rules mono_rules)

text\<open> Note that this was actually proven for the
       Process ordering, not the refinement ordering. 
       But the former implies the latter.
       And due to anti-symmetry, equality follows
       for the case of finite alphabets \ldots \<close>

lemma spec_equal_impl : 
assumes fin:  "finite (SYN::('a channel)set)"
shows         "SYSTEM = (COPY::'a channel process)"
  by (simp add: below_antisym fin impl_refines_spec spec_refines_impl)

subsection\<open>Deadlock Freeness Proof \<close>

text\<open>HOL-CSP can be used to prove deadlock-freeness of processes with infinite alphabet. In the
case of the @{term COPY} - process, this can be formulated as the following refinement problem:\<close>

lemma "(DF (range left \<union> range right)) \<sqsubseteq>\<^sub>F\<^sub>D COPY"
  apply(simp add:DF_def,rule fix_ind2,simp_all)
  unfolding failure_divergence_refine_def 
proof -
  show "adm (\<lambda>a. a \<le> COPY)"   by(rule le_adm, simp_all add:monofunI)
next
  show "\<bottom> \<le> COPY" by(simp_all)
next
    have 1:"(\<sqinter>xa\<in> range left \<union> range right \<rightarrow> \<bottom>) \<le> (\<sqinter>xa\<in> range left \<rightarrow>  \<bottom>)"
      using mndet_subset_FD by (metis UNIV_I empty_iff imageI)
    have 2:"(\<sqinter>xa\<in> range left \<rightarrow>  \<bottom>) \<le> (left`?`x \<rightarrow>  \<bottom>)" 
      unfolding read_def
      by (metis Mprefix_refines_Mndet comp_apply dual_order.antisym mono_mprefix_FD order_refl)

  show "(\<sqinter>x\<in>range left \<union> range right \<rightarrow>  \<bottom>) \<le> COPY"
    by (metis (mono_tags, lifting)  1 2 COPY_rec bot_less1 mono_read_FD order.trans)
next
  fix P::"'a channel process"
  assume  *: "P \<le> COPY" and ** : "(\<sqinter>x\<in>range left \<union> range right \<rightarrow>  P) \<le> COPY"
    have 1:"(\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P) \<le> (\<sqinter>xa\<in> range right \<rightarrow>  P)"
      using mndet_subset_FD by (metis UNIV_I Un_commute empty_iff imageI)
    have 2:"(\<sqinter>xa\<in> range right \<rightarrow>  P) \<le> (right`!`x \<rightarrow>  P)" for x
      using mndet_subset_FD[of "{right x}" "range right"]
      by(simp add:write_def write0_def mndet_unit)
    from 1 2 have ab:"(\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P) \<le> (right`!`x \<rightarrow>  P)" for x
      using dual_order.trans by blast
    hence 3:"(left`?`x \<rightarrow> (\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P)) \<le> (left`?`x \<rightarrow>(right`!`x \<rightarrow>  P))"
      by (simp add: mono_read_FD)
    have 4:"\<And>X. (\<sqinter>xa\<in> range left \<union> range right \<rightarrow> X) \<le> (\<sqinter>xa\<in> range left \<rightarrow> X)"
      using mndet_subset_FD by (metis UNIV_I empty_iff imageI)
    have 5:"\<And>X. (\<sqinter>xa\<in> range left \<rightarrow> X) \<le> (left`?`x \<rightarrow> X)"
      unfolding read_def
      by (metis Mprefix_refines_Mndet comp_apply dual_order.antisym mono_mprefix_FD order_refl)
    from 3 4[of "(\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P)"] 
         5  [of "(\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P)"] 
    have 6:"(\<sqinter>xa\<in> range left \<union> range right \<rightarrow> 
                    (\<sqinter>xa\<in> range left \<union> range right \<rightarrow>  P)) \<le> (left`?`x \<rightarrow> (right`!`x \<rightarrow>  P))"
      by (meson dual_order.trans)
    from * ** have 7:"(left`?`x \<rightarrow> (right`!`x \<rightarrow>  P)) \<le> (left`?`x \<rightarrow> (right`!`x \<rightarrow>  COPY))"
      by (simp add: mono_read_FD mono_write_FD)

  show "(\<sqinter>x\<in>range left \<union> range right \<rightarrow>  \<sqinter>x\<in>range left \<union> range right \<rightarrow>  P) \<le> COPY"
    by (metis (mono_tags, lifting) 6 7  COPY_rec dual_order.trans)
qed

section\<open> An Alternative Approach: Using the fixrec-Package \<close>

subsection\<open> Channels and Synchronisation Sets \<close>

text\<open> As before. \<close>

subsection\<open> Process Definitions via fixrec-Package  \<close>

fixrec
  COPY' :: "('a channel) process"
and
  SEND' :: "('a channel) process"
and
  REC' :: "('a channel) process"
where
   COPY'_rec[simp del]:  "COPY' = (left`?`x \<rightarrow> (right`!`x \<rightarrow> COPY'))"
|  SEND'_rec[simp del]:  "SEND' = (left`?`x \<rightarrow> (mid`!`x \<rightarrow> (ack \<rightarrow> SEND')))"
|  REC'_rec[simp del] :  "REC'  = (mid`?`x \<rightarrow> (right`!`x \<rightarrow> (ack \<rightarrow> REC')))"

definition SYSTEM' :: "('a channel) process"
where     "SYSTEM' \<equiv> ((SEND' \<lbrakk> SYN \<rbrakk> REC') \\ SYN)"

subsection\<open> Another Refinement Proof on fixrec-infrastructure \<close>

text\<open> Third part: No comes the proof by fixpoint induction. 
       Not too bad in automation considering what is inferred,
       but wouldn't scale for large examples. \<close>

lemma impl_refines_spec' : "(COPY'::'a channel process) \<sqsubseteq> SYSTEM'"
  apply(unfold SYSTEM'_def)
  apply(rule_tac P="\<lambda> a b c. a \<sqsubseteq> (SEND' \<lbrakk>SYN\<rbrakk> REC') \\ SYN" in COPY'_SEND'_REC'.induct, simp_all)
  by (subst SEND'_rec, subst REC'_rec, simp add: sync_rules hide_rules mono_rules)

lemma spec_refines_impl' : 
assumes fin:  "finite (SYN::('a channel)set)"
shows         "SYSTEM' \<sqsubseteq> (COPY'::'a channel process)"
proof(unfold SYSTEM'_def, rule_tac P="\<lambda> a b c. ((b \<lbrakk>SYN\<rbrakk> REC') \\ SYN) \<sqsubseteq> COPY'" in COPY'_SEND'_REC'.induct, goal_cases)
  case 1
  have aa:"adm (\<lambda>(a::'a channel process). ((a \<lbrakk>SYN\<rbrakk> REC') \\ SYN) \<sqsubseteq> COPY')"
    by (simp add: contI cont_left_sync chain_Sync1 thelubE fin) 
  thus ?case using adm_subst[of "\<lambda>(a,b,c). b", simplified, OF aa] by (simp add:split_def)
next
  case 2
  then show ?case by (simp add: hide_set_bot par_Int_bot sync_commute)
next
  case (3 a aa b)
  then show ?case   by (subst COPY'_rec, subst REC'_rec, simp add:sync_rules hide_rules mono_rules)
qed

lemma spec_equal_impl' : 
assumes fin:  "finite (SYN::('a channel)set)"
shows         "SYSTEM' = (COPY'::'a channel process)"
  apply(rule Porder.po_class.below_antisym)
   apply(rule spec_refines_impl'[OF fin])
  apply(rule impl_refines_spec')
done



end
