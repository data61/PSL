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
 * Basic Hoare Calculus for the State Exception Monad 
 *
 * Authors : Burkhart Wolff
 *)

theory Hoare_MonadSE
  imports Symbex_MonadSE
begin
  


section\<open>Hoare\<close>


definition hoare\<^sub>3 :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<alpha> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
where   "\<lbrace>P\<rbrace> M \<lbrace>Q\<rbrace> \<equiv> (\<forall>\<sigma>. P \<sigma> \<longrightarrow> (case M \<sigma> of None => False | Some(x, \<sigma>') => Q x \<sigma>'))" 

definition hoare\<^sub>3' :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)/\<dagger>)" 50)
where   "\<lbrace>P\<rbrace> M \<dagger> \<equiv> (\<forall>\<sigma>. P \<sigma> \<longrightarrow> (case M \<sigma> of None => True | _ => False))" 

subsection\<open>Basic rules\<close> 
  
lemma skip: " \<lbrace>P\<rbrace> skip\<^sub>S\<^sub>E \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by auto
    
lemma fail: "\<lbrace>P\<rbrace> fail\<^sub>S\<^sub>E \<dagger>"
  unfolding hoare\<^sub>3'_def fail_SE_def unit_SE_def by auto

lemma assert: "\<lbrace>P\<rbrace> assert\<^sub>S\<^sub>E P \<lbrace>\<lambda> _ _. True\<rbrace>"    
  unfolding hoare\<^sub>3_def assert_SE_def unit_SE_def
  by auto

lemma assert_conseq: "Collect P \<subseteq> Collect Q \<Longrightarrow> \<lbrace>P\<rbrace> assert\<^sub>S\<^sub>E Q \<lbrace>\<lambda> _ _. True\<rbrace>"    
  unfolding hoare\<^sub>3_def assert_SE_def unit_SE_def
  by auto

lemma assume_conseq: 
  assumes "\<exists> \<sigma>. Q \<sigma>"
  shows   "\<lbrace>P\<rbrace> assume\<^sub>S\<^sub>E Q \<lbrace>\<lambda> _ . Q\<rbrace>"    
  unfolding hoare\<^sub>3_def assume_SE_def unit_SE_def
  apply (auto simp : someI2)
  using assms by auto

    
text \<open>assignment missing in the calculus because this is viewed as a state specific  
       operation, definable for concrete instances of @{typ "'\<sigma>"}.\<close>  

subsection \<open>Generalized and special sequence rules\<close> 
text\<open>The decisive idea is to factor out the post-condition on the results of @{term M} :\<close>
lemma sequence : 
  "    \<lbrace>P\<rbrace> M \<lbrace>\<lambda>x \<sigma>. x\<in>A \<and> Q x \<sigma>\<rbrace>
   \<Longrightarrow> \<forall>x\<in>A. \<lbrace>Q x\<rbrace> M' x \<lbrace>R\<rbrace> 
   \<Longrightarrow> \<lbrace>P\<rbrace> x \<leftarrow> M; M' x \<lbrace>R\<rbrace>" 
  unfolding hoare\<^sub>3_def bind_SE_def 
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)

lemma sequence_irpt_l : "\<lbrace>P\<rbrace> M \<dagger>  \<Longrightarrow> \<lbrace>P\<rbrace> x \<leftarrow> M; M' x \<dagger>" 
  unfolding hoare\<^sub>3'_def bind_SE_def 
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)

lemma sequence_irpt_r : "\<lbrace>P\<rbrace> M \<lbrace>\<lambda>x \<sigma>. x\<in>A \<and> Q x \<sigma>\<rbrace> \<Longrightarrow> \<forall>x\<in>A. \<lbrace>Q x\<rbrace> M' x \<dagger>  \<Longrightarrow> \<lbrace>P\<rbrace> x \<leftarrow> M; M' x \<dagger>" 
  unfolding hoare\<^sub>3'_def hoare\<^sub>3_def bind_SE_def 
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)
        
lemma sequence' : "\<lbrace>P\<rbrace> M \<lbrace>\<lambda>_. Q \<rbrace> \<Longrightarrow> \<lbrace>Q\<rbrace> M' \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> M;- M' \<lbrace>R\<rbrace>"     
  unfolding hoare\<^sub>3_def hoare\<^sub>3_def bind_SE_def bind_SE'_def
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)

lemma sequence_irpt_l' : "\<lbrace>P\<rbrace> M \<dagger> \<Longrightarrow> \<lbrace>P\<rbrace> M;- M' \<dagger>" 
  unfolding hoare\<^sub>3'_def bind_SE_def bind_SE'_def
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)
    
lemma sequence_irpt_r' : "\<lbrace>P\<rbrace> M \<lbrace>\<lambda>_. Q \<rbrace> \<Longrightarrow> \<lbrace>Q\<rbrace> M' \<dagger> \<Longrightarrow> \<lbrace>P\<rbrace> M;- M' \<dagger>" 
  unfolding hoare\<^sub>3'_def hoare\<^sub>3_def bind_SE_def bind_SE'_def
  by(auto,erule_tac x="\<sigma>" in allE, auto split: Option.option.split_asm Option.option.split)

subsection\<open>Generalized and special consequence rules\<close>  
lemma consequence : 
  "    Collect P \<subseteq> Collect P'
   \<Longrightarrow> \<lbrace>P'\<rbrace> M \<lbrace>\<lambda>x \<sigma>. x\<in>A \<and> Q' x \<sigma>\<rbrace> 
   \<Longrightarrow> \<forall> x\<in>A. Collect(Q' x) \<subseteq> Collect (Q x)
   \<Longrightarrow> \<lbrace>P\<rbrace> M \<lbrace>\<lambda>x \<sigma>. x\<in>A \<and> Q x \<sigma>\<rbrace>"
  unfolding hoare\<^sub>3_def bind_SE_def 
  by(auto,erule_tac x="\<sigma>" in allE,auto split: Option.option.split_asm Option.option.split)

lemma consequence_unit : 
  assumes "(\<And> \<sigma>. P \<sigma> \<longrightarrow> P' \<sigma>)" 
   and  "\<lbrace>P'\<rbrace> M \<lbrace>\<lambda>x::unit. \<lambda> \<sigma>.  Q' \<sigma>\<rbrace>" 
   and  " (\<And> \<sigma>. Q'  \<sigma> \<longrightarrow> Q  \<sigma>)" 
   shows "\<lbrace>P\<rbrace> M \<lbrace>\<lambda>x \<sigma>. Q \<sigma>\<rbrace>"
proof -
  have * : "(\<lambda>x \<sigma>. Q  \<sigma>) = (\<lambda>x::unit. \<lambda> \<sigma>. x\<in>UNIV \<and> Q  \<sigma>) " by auto
  show ?thesis
    apply(subst *)
    apply(rule_tac  P' = "P'" and Q' = "%_. Q'" in consequence)
    apply (simp add: Collect_mono assms(1))
    using assms(2) apply auto[1]
    by (simp add: Collect_mono assms(3))
qed


lemma consequence_irpt : 
  "    Collect P \<subseteq> Collect P'
   \<Longrightarrow> \<lbrace>P'\<rbrace> M \<dagger>
   \<Longrightarrow> \<lbrace>P\<rbrace>  M \<dagger>"
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def  
  by(auto)

lemma consequence_mt_swap : 
  "(\<lbrace>\<lambda>_. False\<rbrace> M \<dagger>) = (\<lbrace>\<lambda>_. False\<rbrace> M \<lbrace>P\<rbrace>)" 
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def 
  by auto
    
subsection\<open>Condition rules\<close> 
  
lemma cond : 
  "    \<lbrace>\<lambda>\<sigma>. P \<sigma> \<and> cond \<sigma>\<rbrace> M \<lbrace>Q\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. P \<sigma> \<and> \<not> cond \<sigma>\<rbrace> M' \<lbrace>Q\<rbrace>  
   \<Longrightarrow> \<lbrace>P\<rbrace>if\<^sub>S\<^sub>E cond then M else M' fi\<lbrace>Q\<rbrace>"
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
  by auto
  
lemma cond_irpt : 
  "    \<lbrace>\<lambda>\<sigma>. P \<sigma> \<and> cond \<sigma>\<rbrace> M \<dagger>
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. P \<sigma> \<and> \<not> cond \<sigma>\<rbrace> M' \<dagger>  
   \<Longrightarrow> \<lbrace>P\<rbrace>if\<^sub>S\<^sub>E cond then M else M' fi \<dagger>"
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
  by auto

text\<open> Note that the other four combinations can be directly derived via
       the @{thm consequence_mt_swap} rule.\<close>
  
subsection\<open>While rules\<close> 
text\<open>The only non-trivial proof is, of course, the while loop rule. Note
that non-terminating loops were mapped to @{term None} following the principle
that our monadic state-transformers represent partial functions in the mathematical 
sense.\<close>
  
lemma while :
  assumes  * : "\<lbrace>\<lambda>\<sigma>. cond \<sigma> \<and> P \<sigma>\<rbrace>  M \<lbrace>\<lambda>_. P\<rbrace>"
  and measure: "\<forall>\<sigma>. cond \<sigma> \<and> P \<sigma> \<longrightarrow> M \<sigma> \<noteq> None \<and> f(snd(the(M \<sigma>))) < ((f \<sigma>)::nat) "
  shows        "\<lbrace>P\<rbrace>while\<^sub>S\<^sub>E cond do M od \<lbrace>\<lambda>_ \<sigma>. \<not>cond \<sigma> \<and> P \<sigma>\<rbrace>"

unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
proof auto
  have * : "\<forall>n. \<forall> \<sigma>. P \<sigma> \<and> f \<sigma> \<le> n \<longrightarrow>  
                     (case (while\<^sub>S\<^sub>E cond do M od) \<sigma> of 
                          None \<Rightarrow> False
                        | Some (x, \<sigma>') \<Rightarrow> \<not> cond \<sigma>' \<and> P \<sigma>')" (is "\<forall>n. ?P n")
     proof (rule allI, rename_tac n, induct_tac n)
       fix n show "?P 0"
         apply(auto)
         apply(subst while_SE_unfold)
         by (metis (no_types, lifting) gr_implies_not0 if_SE_def  measure option.case_eq_if 
                     option.sel option.simps(3) prod.sel(2) split_def unit_SE_def)
     next
       fix n  show " ?P n \<Longrightarrow> ?P (Suc n)"
        apply(auto,subst while_SE_unfold)
         apply(case_tac "\<not>cond \<sigma>")
        apply (simp add: if_SE_def unit_SE_def)
        apply(simp add: if_SE_def)
        apply(case_tac "M \<sigma> = None")
         using measure apply blast
        proof (auto simp: bind_SE'_def bind_SE_def)
          fix \<sigma> \<sigma>'
          assume 1 : "cond \<sigma>"
            and  2 : "M \<sigma> = Some ((), \<sigma>')"
            and  3 : " P \<sigma>"
            and  4 : " f \<sigma> \<le> Suc n"
            and  hyp : "?P n"
          have 5 : "P \<sigma>'" 
            by (metis (no_types, lifting) * 1 2 3 case_prodD hoare\<^sub>3_def option.simps(5))
          have 6 : "snd(the(M \<sigma>)) = \<sigma>'" 
            by (simp add: 2)
          have 7 : "cond \<sigma>' \<Longrightarrow> f \<sigma>' \<le> n" 
            using 1 3 4 6 leD measure by auto
          show   "case (while\<^sub>S\<^sub>E cond do M od) \<sigma>' of None \<Rightarrow> False
                                                  | Some (xa, \<sigma>') \<Rightarrow> \<not> cond \<sigma>' \<and> P \<sigma>'"
          using 1 3 4 5 6 hyp measure by auto
        qed
      qed
  show "\<And>\<sigma>. P \<sigma> \<Longrightarrow>
         case (while\<^sub>S\<^sub>E cond do M od) \<sigma> of None \<Rightarrow> False
         | Some (x, \<sigma>') \<Rightarrow> \<not> cond \<sigma>' \<and> P \<sigma>'"
  using "*" by blast
qed
  

lemma while_irpt :
  assumes  * : "\<lbrace>\<lambda>\<sigma>. cond \<sigma> \<and> P \<sigma>\<rbrace>  M \<lbrace>\<lambda>_. P\<rbrace> \<or> \<lbrace>\<lambda>\<sigma>. cond \<sigma> \<and> P \<sigma>\<rbrace>  M  \<dagger>"
  and measure: "\<forall>\<sigma>. cond \<sigma> \<and> P \<sigma> \<longrightarrow> M \<sigma> = None \<or> f(snd(the(M \<sigma>))) < ((f \<sigma>)::nat)"
  and enabled: "\<forall>\<sigma>. P \<sigma> \<longrightarrow> cond \<sigma>"
  shows        "\<lbrace>P\<rbrace>while\<^sub>S\<^sub>E cond do M od \<dagger>"
unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
proof auto
  have * : "\<forall>n. \<forall> \<sigma>. P \<sigma> \<and> f \<sigma> \<le> n \<longrightarrow>  
                     (case (while\<^sub>S\<^sub>E cond do M od) \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False)" 
            (is "\<forall>n. ?P n ")
    proof (rule allI, rename_tac n, induct_tac n)
      fix n 
         have 1 : "\<And>\<sigma>. P \<sigma> \<Longrightarrow> cond \<sigma>" 
          by (simp add: enabled * )
      show "?P 0 "
        apply(auto,frule 1)
        by (metis assms(2) bind_SE'_def bind_SE_def gr_implies_not0 if_SE_def option.case(1) 
                           option.case_eq_if  while_SE_unfold)
    next
      fix k n 
      assume hyp : "?P n"
         have 1 : "\<And>\<sigma>. P \<sigma> \<Longrightarrow> cond \<sigma>" 
          by (simp add: enabled * )
      show "?P (Suc n) "
        apply(auto, frule 1)
        apply(subst while_SE_unfold, auto simp: if_SE_def)
      proof(insert *,simp_all add: hoare\<^sub>3_def hoare\<^sub>3'_def, erule disjE)
        fix \<sigma>
        assume "P \<sigma>"
         and   "f \<sigma> \<le> Suc n"
         and   "cond \<sigma>"
         and   ** : "\<forall>\<sigma>. cond \<sigma> \<and> P \<sigma> \<longrightarrow> (case M \<sigma> of None \<Rightarrow> False | Some (x, \<sigma>') \<Rightarrow> P \<sigma>')"
         obtain "(case M \<sigma> of None \<Rightarrow> False | Some (x, \<sigma>') \<Rightarrow> P \<sigma>')" 
               by (simp add: "**" \<open>P \<sigma>\<close> \<open>cond \<sigma>\<close>)
        then 
        show "case (M ;- (while\<^sub>S\<^sub>E cond do M od)) \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False"
             apply(case_tac "M \<sigma>", auto, rename_tac \<sigma>', simp add: bind_SE'_def bind_SE_def)
             proof - 
               fix \<sigma>' 
               assume "P \<sigma>'"
                and "M \<sigma> = Some ((), \<sigma>')"
                have "cond \<sigma>'"  by (simp add: \<open>P \<sigma>'\<close> enabled)
                have "f \<sigma>' \<le> n" 
                  using \<open>M \<sigma> = Some ((), \<sigma>')\<close> \<open>P \<sigma>\<close> \<open>cond \<sigma>\<close> \<open>f \<sigma> \<le> Suc n\<close> measure by fastforce   
               show "case (while\<^sub>S\<^sub>E cond do M od) \<sigma>' of None \<Rightarrow> True | Some a \<Rightarrow> False"
                  using hyp  by (simp add: \<open>P \<sigma>'\<close> \<open>f \<sigma>' \<le> n\<close>)
              qed
      next
        fix \<sigma>
        assume "P \<sigma>"
         and   "f \<sigma> \<le> Suc n"
         and   "cond \<sigma>"  
         and * : "\<forall>\<sigma>. cond \<sigma> \<and> P \<sigma> \<longrightarrow> (case M \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False)"
        obtain ** : "(case M \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False)" 
          by (simp add: "*" \<open>P \<sigma>\<close> \<open>cond \<sigma>\<close>)
        have "M \<sigma> = None" 
          by (simp add: "**" option.disc_eq_case(1))
        show "case (M ;- (while\<^sub>S\<^sub>E cond do M od)) \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False"          
          by (simp add: \<open>M \<sigma> = None\<close> bind_SE'_def bind_SE_def)
      qed      
    qed
show "\<And>\<sigma>. P \<sigma> \<Longrightarrow> case (while\<^sub>S\<^sub>E cond do M od) \<sigma> of None \<Rightarrow> True | Some a \<Rightarrow> False" using * by blast
qed
  

subsection\<open>Experimental Alternative Definitions (Transformer-Style Rely-Guarantee)\<close>

definition  hoare\<^sub>1 :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<alpha> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> bool" ("\<turnstile>\<^sub>1 ({(1_)}/ (_)/ {(1_)})" 50)
where  "(\<turnstile>\<^sub>1{P} M {Q} ) = (\<forall>\<sigma>. \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E P ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (Q x)))"

(* Problem: Severe Deviation for the case of an unsatisfyabke precondition *)

definition  hoare\<^sub>2 :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<alpha> \<Rightarrow> '\<sigma> \<Rightarrow> bool) \<Rightarrow> bool" ("\<turnstile>\<^sub>2 ({(1_)}/ (_)/ {(1_)})" 50)
where  "(\<turnstile>\<^sub>2{P} M {Q} ) = (\<forall>\<sigma>. P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile>  (x \<leftarrow> M; assert\<^sub>S\<^sub>E (Q x))))"

  
end
  