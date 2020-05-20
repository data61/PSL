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

theory Clean_Symbex
  imports Clean
begin


section\<open>Clean Symbolic Execution Rules \<close>


subsection\<open>Basic NOP - Symbolic Execution Rules.  \<close>

text\<open>  As they are equalities, they can also
be used as program optimization rules. \<close>

lemma non_exec_assign  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success)

lemma non_exec_assign'  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)

lemma exec_assign  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success)     

lemma exec_assign'  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)     

subsection\<open>Assign Execution Rules.  \<close>

lemma non_exec_assign_global  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
by(simp add: assign_global_def non_exec_assign assms)

lemma non_exec_assign_global'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
  by (metis (full_types) assms bind_SE'_def non_exec_assign_global)


lemma exec_assign_global  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_global_def assign_def assms exec_bind_SE_success)

lemma exec_assign_global'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_global_def assign_def assms exec_bind_SE_success bind_SE'_def)

lemma non_exec_assign_local  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by(simp add: assign_local_def non_exec_assign assms)

lemma non_exec_assign_local'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_local upd rhs;- M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by (metis assms bind_SE'_def non_exec_assign_local)

lemmas non_exec_assign_localD'= non_exec_assign[THEN iffD1]

lemma exec_assign_local  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_local_def assign_def assms exec_bind_SE_success)

lemma exec_assign_local'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( assign_local upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)" 
  unfolding assign_local_def assign_def 
  by (simp add: assms exec_bind_SE_success2)

lemmas exec_assignD = exec_assign[THEN iffD1]
thm exec_assignD

lemmas exec_assignD' = exec_assign'[THEN iffD1]
thm exec_assignD'

lemmas exec_assign_globalD =  exec_assign_global[THEN iffD1]

lemmas exec_assign_globalD' =  exec_assign_global'[THEN iffD1]

lemmas exec_assign_localD = exec_assign_local[THEN iffD1]
thm exec_assign_localD

lemmas exec_assign_localD' = exec_assign_local'[THEN iffD1]



subsection\<open>Basic Call Symbolic Execution Rules.  \<close>



lemma exec_call_0  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_0\<^sub>C_def exec_bind_SE_success)

lemma exec_call_0'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_0\<^sub>C M;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_0)



lemma exec_call_1  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> call_1\<^sub>C M A\<^sub>1; M' x)) = (\<sigma> \<Turnstile>  M' undefined)"
  by (simp add: assms call_1\<^sub>C_def call\<^sub>C_def exec_bind_SE_success)

lemma exec_call_1'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_1\<^sub>C M A\<^sub>1;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_1)

lemma exec_call  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> call\<^sub>C M A\<^sub>1; M' x)) = (\<sigma> \<Turnstile>  M' undefined)"
  by (simp add: assms call\<^sub>C_def call_1\<^sub>C_def exec_bind_SE_success)

lemma exec_call'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call\<^sub>C M A\<^sub>1;- M')) = (\<sigma> \<Turnstile>  M')"
  by (metis assms call_1\<^sub>C_def exec_call_1')

lemma exec_call_2  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_2\<^sub>C M A\<^sub>1 A\<^sub>2; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_2\<^sub>C_def exec_bind_SE_success)

lemma exec_call_2'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M')) = (\<sigma> \<Turnstile> M')"
  by (simp add: assms bind_SE'_def exec_call_2)

subsection\<open>Basic Call Symbolic Execution Rules.  \<close>

lemma non_exec_call_0  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_0\<^sub>C_def valid_SE_def)

lemma non_exec_call_0'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_0\<^sub>C M;- M') = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def non_exec_call_0)

lemma non_exec_call_1  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> (call_1\<^sub>C M A\<^sub>1); M' x)) = (\<sigma> \<Turnstile> (x \<leftarrow> M (A\<^sub>1 \<sigma>); M' x))"
  by (simp add: assms bind_SE'_def call\<^sub>C_def bind_SE_def call_1\<^sub>C_def valid_SE_def)

lemma non_exec_call_1'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_1\<^sub>C M A\<^sub>1;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_1)


lemma non_exec_call  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> (call\<^sub>C M A\<^sub>1); M' x)) = (\<sigma> \<Turnstile> (x \<leftarrow> M (A\<^sub>1 \<sigma>); M' x))"
  by (simp add: assms call\<^sub>C_def bind_SE'_def bind_SE_def call_1\<^sub>C_def valid_SE_def)

lemma non_exec_call'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call\<^sub>C M A\<^sub>1;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call)


lemma non_exec_call_2  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2); M')) = (\<sigma> \<Turnstile> M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_2\<^sub>C_def valid_SE_def)

lemma non_exec_call_2'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_2)


subsection\<open>Conditional.  \<close>

lemma exec_If\<^sub>C_If\<^sub>S\<^sub>E  : 
assumes "\<not> exec_stop \<sigma>"
shows  " ((if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi))\<sigma> = ((if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) \<sigma> "
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def
  by (simp add: assms bind_SE_def if_C_def)
    
    
lemma valid_exec_If\<^sub>C  : 
assumes "\<not> exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M)"
  by (meson assms exec_If\<^sub>C_If\<^sub>S\<^sub>E valid_bind'_cong)


      
lemma exec_If\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
    by (simp add: assms if_C_def)
    
lemma exec_While\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (while\<^sub>C P do B\<^sub>1 od);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding while_C_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
  apply simp using assms by blast    


    
    
lemma if\<^sub>C_cond_cong : "f \<sigma> = g \<sigma> \<Longrightarrow> 
                           (if\<^sub>C f then c else d fi) \<sigma> = 
                           (if\<^sub>C g then c else d fi) \<sigma>"
  unfolding if_C_def
   by simp 
   
 
subsection\<open>Break - Rules.  \<close>

lemma break_assign_skip [simp]: "break ;- assign f = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def bind_SE'_def   bind_SE_def
  by auto



lemma break_if_skip [simp]: "break ;- (if\<^sub>C b then c else d fi) = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def if_C_def bind_SE'_def   bind_SE_def
  by auto
    
                       
lemma break_while_skip [simp]: "break ;- (while\<^sub>C b do c od) = break"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def bind_SE'_def bind_SE_def break_def exec_stop_def
  by simp

    
lemma unset_break_idem [simp] : 
 "( unset_break_status ;- unset_break_status ;- M) = (unset_break_status ;- M)"
  apply(rule ext)  unfolding unset_break_status_def bind_SE'_def bind_SE_def by auto

lemma return_cancel1_idem [simp] : 
 "( return\<^sub>C X E ;- assign_global X E' ;- M) = ( return\<^sub>C X E ;- M)"
  apply(rule ext, rename_tac "\<sigma>")  
  unfolding unset_break_status_def bind_SE'_def bind_SE_def
            assign_def return\<^sub>C_def assign_global_def assign_local_def
  apply(case_tac "exec_stop \<sigma>")
  apply auto
  by (simp add: exec_stop_def set_return_status_def)
    
lemma return_cancel2_idem [simp] : 
 "( return\<^sub>C X E ;- assign_local X E' ;- M) = ( return\<^sub>C X E ;- M)"
    apply(rule ext, rename_tac "\<sigma>")  
  unfolding unset_break_status_def bind_SE'_def bind_SE_def
            assign_def return\<^sub>C_def assign_global_def assign_local_def
  apply(case_tac "exec_stop \<sigma>")
   apply auto
  by (simp add: exec_stop_def set_return_status_def)


subsection\<open>While.  \<close>     

lemma while\<^sub>C_skip [simp]: "(while\<^sub>C (\<lambda> x. False) do c od) = skip\<^sub>S\<^sub>E"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def
  apply auto
  unfolding exec_stop_def skip\<^sub>S\<^sub>E_def unset_break_status_def bind_SE'_def unit_SE_def bind_SE_def
  by simp
 

txt\<open> Various tactics for various coverage criteria \<close>

definition while_k :: "nat \<Rightarrow> (('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
where     "while_k _ \<equiv> while_C"


text\<open>Somewhat amazingly, this unfolding lemma crucial for symbolic execution still holds ... 
     Even in the presence of break or return...\<close> 
lemma exec_while\<^sub>C : 
"(\<sigma> \<Turnstile> ((while\<^sub>C b do c od) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- ((while\<^sub>C b do c od) ;- unset_break_status) else skip\<^sub>S\<^sub>E fi)  ;- M))"
proof (cases "exec_stop \<sigma>")
  case True
  then show ?thesis 
    by (simp add: True exec_If\<^sub>C' exec_While\<^sub>C')
next
  case False
  then show ?thesis
    proof (cases "\<not> b \<sigma>")
      case True
      then show ?thesis
        apply(subst valid_bind'_cong)
        using \<open>\<not> exec_stop \<sigma>\<close> apply simp_all
        apply (auto simp: skip\<^sub>S\<^sub>E_def unit_SE_def)
          apply(subst while_C_def, simp)
         apply(subst bind'_cong)
         apply(subst MonadSE.while_SE_unfold)
          apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. False"])
          apply simp_all
        apply(subst if\<^sub>C_cond_cong [of _ _ "\<lambda>_. False"], simp add: )
        apply(subst exec_If\<^sub>C_If\<^sub>S\<^sub>E,simp_all)
        by (simp add: exec_stop_def unset_break_status_def)
    next
      case False
      have * : "b \<sigma>"  using False by auto
      then show ?thesis
           unfolding while_k_def 
           apply(subst  while_C_def)
           apply(subst  if_C_def)
           apply(subst  valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
           apply(subst  (2) valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
            apply(subst MonadSE.while_SE_unfold)
            apply(subst valid_bind'_cong)
            apply(subst bind'_cong)
             apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. True"])
              apply(simp_all add:   \<open>\<not> exec_stop \<sigma>\<close> )
            apply(subst bind_assoc', subst bind_assoc')
            proof(cases "c \<sigma>")
              case None
              then show "(\<sigma> \<Turnstile> c;-((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c;-(while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                by (simp add: bind_SE'_def exec_bind_SE_failure)
            next
              case (Some a)
              then show "(\<sigma> \<Turnstile> c ;- ((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c ;- (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                apply(insert \<open>c \<sigma> = Some a\<close>, subst (asm) surjective_pairing[of a])
                apply(subst exec_bind_SE_success2, assumption)
                apply(subst exec_bind_SE_success2, assumption)
                proof(cases "exec_stop (snd a)")
                  case True
                  then show "(snd a \<Turnstile>((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                       by (metis (no_types, lifting) bind_assoc' exec_While\<^sub>C' exec_skip if_SE_D2' 
                                                  skip\<^sub>S\<^sub>E_def while_SE_unfold)
                next
                  case False
                  then show "(snd a \<Turnstile> ((while\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                          unfolding  while_C_def
                          by(subst (2) valid_bind'_cong,simp)(simp)
                qed       
            qed  
    qed
qed
(* ... although it is, oh my god, amazingly complex to prove. *)


lemma while_k_SE : "while_C = while_k k"
by (simp only: while_k_def)


corollary exec_while_k : 
"(\<sigma> \<Turnstile> ((while_k (Suc n) b c) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while_k n b c) ;- unset_break_status else skip\<^sub>S\<^sub>E fi)  ;- M))"
  by (metis exec_while\<^sub>C while_k_def)
    

txt\<open> Necessary prerequisite: turning ematch and dmatch into a proper Isar Method. \<close>
(* TODO : this code shoud go to TestGen Method setups *)
ML\<open>
local
fun method_setup b tac =
  Method.setup b
    (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o K (tac ctxt rules))))
in
val _ =
  Theory.setup (   method_setup @{binding ematch} ematch_tac "fast elimination matching"
                #> method_setup @{binding dmatch} dmatch_tac "fast destruction matching"
                #> method_setup @{binding match} match_tac "resolution based on fast matching")
end
\<close>

lemmas exec_while_kD = exec_while_k[THEN iffD1]

end