(******************************************************************************
 * Clean
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

(*
 * A Hoare Calculus for Clean
 *
 * Authors : Burkhart Wolff
 *)

theory Hoare_Clean
  imports Hoare_MonadSE
          Clean
begin


subsection\<open>Clean Control Rules\<close>

lemma break1: 
  "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> break_status := True \<rparr>) \<rbrace> break \<lbrace>\<lambda>r \<sigma>.  P \<sigma> \<and> break_status \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def break_def unit_SE_def by auto

lemma unset_break1: 
  "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> break_status := False \<rparr>) \<rbrace> unset_break_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<and> \<not> break_status \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def unset_break_status_def unit_SE_def by auto

lemma set_return1: 
  "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> return_status := True \<rparr>) \<rbrace> set_return_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<and> return_status \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def set_return_status_def unit_SE_def by auto

lemma unset_return1: 
  "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> return_status := False \<rparr>) \<rbrace> unset_return_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<and> \<not>return_status \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def unset_return_status_def unit_SE_def by auto


subsection\<open>Clean Skip Rules\<close>

lemma assign_global_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  assign_global upd rhs  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_global_def)

lemma assign_local_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace> assign_local upd rhs  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_local_def)

lemma return_skip:
"\<lbrace>\<lambda>\<sigma>.  exec_stop \<sigma> \<and> P \<sigma> \<rbrace> return\<^sub>C upd rhs \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding hoare\<^sub>3_def return\<^sub>C_def unit_SE_def assign_local_def assign_def bind_SE'_def bind_SE_def
  by auto

lemma assign_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  assign tr  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_def)

lemma if_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  if\<^sub>C C then E else F fi \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def if_SE_def
  by (simp add: if_C_def)

lemma while_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  while\<^sub>C cond do body od  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def while_C_def 
  by auto

lemma if_opcall_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma>\<rbrace> (call\<^sub>C M A\<^sub>1) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def
  by simp

lemma if_funcall_skip:
"\<lbrace>\<lambda>\<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>(p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C fun E ; assign_local upd (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def assign_local_def assign_def
  by (simp add: bind_SE_def)

lemma if_funcall_skip':
"\<lbrace>\<lambda>\<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>(p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C fun E ; assign_global upd (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def assign_global_def assign_def
  by (simp add: bind_SE_def)




subsection\<open>Clean Assign Rules\<close>


lemma assign_global:
  assumes * : "\<sharp> upd"
  shows "\<lbrace>\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> P (upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<rbrace> 
         assign_global upd rhs 
         \<lbrace>\<lambda>r \<sigma>. \<not>exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_global_def  assign_def
  by(auto simp: assms)

lemma assign_local:
  assumes * : "\<sharp> (upd \<circ> map_hd)"
  shows "\<lbrace>\<lambda>\<sigma>.  \<not> exec_stop \<sigma> \<and> P ((upd \<circ> map_hd) (\<lambda>_. rhs \<sigma>) \<sigma>) \<rbrace>  
          assign_local upd rhs  
         \<lbrace>\<lambda>r \<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_local_def  assign_def
  using assms exec_stop_vs_control_independence by fastforce

lemma return_assign:
  assumes * : "\<sharp> (upd \<circ> map_hd)"
  shows "\<lbrace>\<lambda> \<sigma>. \<not> exec_stop \<sigma> \<and> P ((upd \<circ> map_hd) (\<lambda>_. rhs \<sigma>) (\<sigma> \<lparr> return_status := True \<rparr>))\<rbrace> 
          return\<^sub>C upd rhs
         \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<and> return_status \<sigma> \<rbrace>"
  unfolding return\<^sub>C_def hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_local_def assign_def 
            set_return_status_def bind_SE'_def bind_SE_def 
proof (auto)
  fix \<sigma> :: "'b control_state_scheme"
    assume a1: "P (upd (map_hd (\<lambda>_. rhs \<sigma>)) (\<sigma>\<lparr>return_status := True\<rparr>))"
    assume "\<not> exec_stop \<sigma>"
    show "P (upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>\<lparr>return_status := True\<rparr>)"
      using a1 assms exec_stop_vs_control_independence' by fastforce
  qed
  (* do we need independence of rhs ? Not really. 'Normal' programs would never
     be control-state dependent, and 'artificial' ones would still be correct ...*)


subsection\<open>Clean Construct Rules\<close>

lemma cond_clean : 
  "    \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<and> cond \<sigma>\<rbrace> M \<lbrace>Q\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<and> \<not> cond \<sigma>\<rbrace> M' \<lbrace>Q\<rbrace>  
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> if\<^sub>C cond then M else M' fi\<lbrace>Q\<rbrace>"
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
  by (simp add: if_C_def)


text\<open>There is a particular difficulty with a verification of (terminating) while rules
in a Hoare-logic for a language involving break. The first is, that break is not used
in the toplevel of a body of a loop (there might be breaks inside an inner loop, though).
This scheme is covered by the rule below, which is a generalisation of the classical 
while loop (as presented by @{thm while}.\<close>


lemma while_clean_no_break :
  assumes  * : "\<lbrace>\<lambda>\<sigma>. \<not> break_status \<sigma> \<and> cond \<sigma> \<and> P \<sigma>\<rbrace>  M \<lbrace>\<lambda>_. \<lambda>\<sigma>.  \<not> break_status \<sigma> \<and> P \<sigma> \<rbrace>"
  and measure: "\<forall>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma> \<and> P \<sigma> 
                    \<longrightarrow> M \<sigma> \<noteq> None \<and> f(snd(the(M \<sigma>))) < ((f \<sigma>)::nat) "
               (is "\<forall>\<sigma>. _ \<and> cond \<sigma> \<and> P \<sigma> \<longrightarrow> ?decrease \<sigma>")
  shows        "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> 
                while\<^sub>C cond do M od 
                \<lbrace>\<lambda>_ \<sigma>. (return_status \<sigma> \<or> \<not> cond \<sigma>) \<and> \<not> break_status \<sigma> \<and> P \<sigma>\<rbrace>"
                (is "\<lbrace>?pre\<rbrace> while\<^sub>C cond do M od \<lbrace>\<lambda>_ \<sigma>. ?post1 \<sigma> \<and> ?post2 \<sigma>\<rbrace>")  
  unfolding while_C_def hoare\<^sub>3_def hoare\<^sub>3'_def
  proof (simp add: hoare\<^sub>3_def[symmetric],rule sequence') 
    show "\<lbrace>?pre\<rbrace> 
          while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma>) do M od
          \<lbrace>\<lambda>_ \<sigma>. \<not> (\<not> exec_stop \<sigma> \<and> cond \<sigma>) \<and> \<not> break_status \<sigma> \<and> P \<sigma>\<rbrace>"
          (is "\<lbrace>?pre\<rbrace> while\<^sub>S\<^sub>E ?cond' do M od \<lbrace>\<lambda>_ \<sigma>. \<not> ( ?cond' \<sigma>) \<and> ?post2 \<sigma>\<rbrace>")
      proof (rule consequence_unit) 
         fix \<sigma> show " ?pre \<sigma> \<longrightarrow> ?post2 \<sigma>"  using exec_stop1 by blast
      next
         show "\<lbrace>?post2\<rbrace>while\<^sub>S\<^sub>E ?cond' do M od\<lbrace>\<lambda>x \<sigma>. \<not>(?cond' \<sigma>) \<and> ?post2 \<sigma>\<rbrace>"
         proof (rule_tac f = "f" in while, rule consequence_unit)
           fix \<sigma> show "?cond' \<sigma> \<and> ?post2 \<sigma> \<longrightarrow> \<not>break_status \<sigma> \<and> cond \<sigma> \<and> P \<sigma>" by simp
         next
           show "\<lbrace>\<lambda>\<sigma>. \<not> break_status \<sigma> \<and> cond \<sigma> \<and> P \<sigma>\<rbrace> M \<lbrace>\<lambda>x \<sigma>. ?post2 \<sigma>\<rbrace>" using "*" by blast
         next 
           fix \<sigma>  show "?post2 \<sigma> \<longrightarrow> ?post2 \<sigma>" by blast
         next 
           show "\<forall>\<sigma>.?cond' \<sigma> \<and> ?post2 \<sigma> \<longrightarrow> ?decrease \<sigma>" using measure by blast
         qed
      next
         fix \<sigma> show " \<not>?cond' \<sigma> \<and> ?post2 \<sigma> \<longrightarrow> \<not>?cond' \<sigma> \<and> ?post2 \<sigma>"  by blast
      qed
  next
    show "\<lbrace>\<lambda>\<sigma>. \<not> (\<not> exec_stop \<sigma> \<and> cond \<sigma>) \<and> ?post2 \<sigma>\<rbrace> unset_break_status
          \<lbrace>\<lambda>_ \<sigma>'. (return_status \<sigma>' \<or> \<not> cond \<sigma>') \<and> ?post2 \<sigma>'\<rbrace>"
         (is "\<lbrace>\<lambda>\<sigma>. \<not> (?cond'' \<sigma>) \<and> ?post2 \<sigma>\<rbrace> unset_break_status \<lbrace>\<lambda>_ \<sigma>'. ?post3 \<sigma>' \<and> ?post2 \<sigma>' \<rbrace>")
      proof (rule consequence_unit) 
        fix \<sigma>  
        show "\<not> ?cond'' \<sigma> \<and> ?post2 \<sigma> \<longrightarrow> (\<lambda>\<sigma>. P \<sigma> \<and> ?post3 \<sigma>) (\<sigma>\<lparr>break_status := False\<rparr>)"
              by (metis (full_types) exec_stop_def surjective update_convs(1))
      next
        show "\<lbrace>\<lambda>\<sigma>. (\<lambda>\<sigma>. P \<sigma> \<and> ?post3 \<sigma>) (\<sigma>\<lparr>break_status := False\<rparr>)\<rbrace>
              unset_break_status 
              \<lbrace>\<lambda>x \<sigma>. ?post3 \<sigma> \<and> \<not> break_status \<sigma> \<and> P \<sigma>\<rbrace>"    
             apply(subst (2) conj_commute,subst conj_assoc,subst (2) conj_commute)
             by(rule unset_break1)
      next 
         fix \<sigma> show  "?post3 \<sigma> \<and> ?post2 \<sigma> \<longrightarrow> ?post3 \<sigma> \<and> ?post2 \<sigma>"  by simp
      qed
qed 


text\<open>In the following we present a version allowing a break inside the body, which implies that the 
     invariant has been established at the break-point and the condition is irrelevant. 
     A return may occur, but the @{term "break_status"} is guaranteed to be true
     after leaving the loop.\<close>



lemma while_clean':
  assumes  M_inv   : "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma> \<and> P \<sigma>\<rbrace>  M \<lbrace>\<lambda>_. P\<rbrace>"
  and cond_idpc    : "\<forall>x \<sigma>.  (cond (\<sigma>\<lparr>break_status := x\<rparr>)) = cond \<sigma> "
  and inv_idpc     : "\<forall>x \<sigma>.  (P (\<sigma>\<lparr>break_status := x\<rparr>)) = P \<sigma> "
  and f_is_measure : "\<forall>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma> \<and> P \<sigma> \<longrightarrow> 
                       M \<sigma> \<noteq> None \<and> f(snd(the(M \<sigma>))) < ((f \<sigma>)::nat) "
shows    "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> 
          while\<^sub>C cond do M od 
          \<lbrace>\<lambda>_ \<sigma>.  \<not> break_status \<sigma> \<and> P \<sigma>\<rbrace>"
  unfolding while_C_def hoare\<^sub>3_def hoare\<^sub>3'_def
  proof (simp add: hoare\<^sub>3_def[symmetric], rule sequence')
    show "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> 
            while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma>) do M od
          \<lbrace>\<lambda>_ \<sigma>. P (\<sigma>\<lparr>break_status := False\<rparr>)\<rbrace>"
          apply(rule consequence_unit, rule impI, erule conjunct2)
          apply(rule_tac f = "f" in while)
          using M_inv f_is_measure inv_idpc by auto
  next
    show "\<lbrace>\<lambda>\<sigma>. P (\<sigma>\<lparr>break_status := False\<rparr>)\<rbrace> unset_break_status 
          \<lbrace>\<lambda>x \<sigma>. \<not> break_status \<sigma> \<and> P \<sigma>\<rbrace>"
          apply(subst conj_commute)
          by(rule  Hoare_Clean.unset_break1)
  qed


text\<open>Consequence and Sequence rules where inherited from the underlying Hoare-Monad theory.\<close>


end





