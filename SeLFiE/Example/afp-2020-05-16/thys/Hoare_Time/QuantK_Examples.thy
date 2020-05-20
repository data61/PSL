subsection "Examples for quantitative Hoare logic"
theory QuantK_Examples
imports QuantK_VCG
begin





fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"

lemma example: "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }"
apply(rule Seq)
 prefer 2
 apply(rule conseq')
 apply(rule While[where I="\<lambda>s. enat (3 * nat (s ''x''))"])
  apply(rule Seq)
   prefer 2
      apply(rule Assign)
      apply(rule Assign')
     apply(simp)
     apply(safe) subgoal for s apply(cases "0 < s ''x''") apply(simp)
    apply (smt Suc_eq_plus1 Suc_nat_eq_nat_zadd1 distrib_left_numeral eSuc_numeral enat_numeral eq_iff iadd_Suc_right nat_mult_1_right one_add_one plus_1_eSuc(1) plus_enat_simps(1) semiring_norm(5)) 
    apply(simp) done   
    apply blast
  apply simp
apply(rule Assign')
apply simp
  apply(safe) subgoal for s apply(cases "s ''x'' = int n") apply(simp)
     apply (simp add: eSuc_enat plus_1_eSuc(2))
    apply simp
    done
  done

lemma example_sound:  "\<Turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }"
apply(rule hoareQ_sound) apply (rule example) done
  
schematic_goal "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. ?A s + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }"
apply(rule Seq)
 prefer 2
 apply(rule conseq')
       apply(rule While)
  apply(rule Seq)
   prefer 2
      apply(rule Assign)
      apply(rule Assign')
     apply(simp)
     apply(safe) apply(case_tac "0 < s ''x''") apply(simp) defer    
    apply(simp)    
    apply blast
  apply simp
apply(rule Assign')
apply simp
  apply(safe) apply(case_tac "s ''x'' = int n") apply(simp)
     apply (simp add: eSuc_enat plus_1_eSuc(2)) defer
    apply simp
  prefer 2 apply auto oops
     
    
    
    
    
subsubsection "Example for VCG"
  
  
  
lemma "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. 1} SKIP ;; SKIP {\<lambda>s. 0 }"
proof -
  have "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat 1} strip ({2} Ab (SKIP ;; SKIP)) {\<lambda>s. 0 }"
    apply(rule vc_sound')
     apply(auto simp: eSuc_enat zero_enat_def)
    by (simp add: mydivcode mydivcode1 mydivcode2)
  then show ?thesis by (simp add: one_enat_def)
qed
  
  
lemma hoareQ_Seq_assoc: "\<turnstile>\<^sub>2\<^sub>' {P} A;; B;; C {Q} = (\<turnstile>\<^sub>2\<^sub>' {P} A;; (B;; C) {Q})"
 by(auto simp: hoare2o_valid_def hoareQ_sound_complete Seq_t_assoc) 
  
  
lemma "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. 1} SKIP  ;; SKIP ;; SKIP {\<lambda>s. 0 }"
proof -
  have "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat 1} strip ({2} Ab (SKIP ;; {2} Ab (SKIP ;; SKIP))) {\<lambda>s. 0 }"
    apply(rule vc_sound')
     apply(auto simp: eSuc_enat zero_enat_def) 
    by (simp add: mydivcode mydivcode1 mydivcode2)
  then show ?thesis by (simp add: one_enat_def hoareQ_Seq_assoc)
qed
  
  
  
  
   
abbreviation "Wsum ==  
  {\<lambda>s. enat (3 * nat (s ''x''))} WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"
  
  
lemma "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }" 
proof -
  have "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} strip (''y'' ::= N 0;; Wsum) {\<lambda>s. 0 }"
    apply(rule vc_sound')
    subgoal
      apply simp
      apply(safe) subgoal for s apply(cases "0 < s ''x''")
         apply(simp)
    apply ( smt Suc_eq_plus1 Suc_nat_eq_nat_zadd1 distrib_left_numeral eSuc_numeral enat_numeral eq_iff iadd_Suc_right nat_mult_1_right one_add_one plus_1_eSuc(1) plus_enat_simps(1) semiring_norm(5)) 
        apply(simp) done   
      done
    subgoal
      apply simp          
      apply(safe) subgoal for s apply(cases "s ''x'' = int n") apply(simp)          
         apply (simp add: eSuc_enat plus_1_eSuc(2))          
        apply simp          
        done
      done
    done      
   then show ?thesis by simp
 qed
   
lemma assumes n0: "n>0" shows "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (n ) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }" 
proof - 
  from n0 obtain n' where n': "n=Suc n'"
    using not0_implies_Suc by blast 
  have "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (n ) + emb (s ''x'' = int n)} strip ({5} Ab (''y'' ::= N 0;; Wsum)) {\<lambda>s. 0 }"
    apply(rule vc_sound')
    subgoal
      apply simp
      apply(safe) subgoal for s apply(cases "0 < s ''x''")
         apply(simp)
    apply ( smt Suc_eq_plus1 Suc_nat_eq_nat_zadd1 distrib_left_numeral eSuc_numeral enat_numeral eq_iff iadd_Suc_right nat_mult_1_right one_add_one plus_1_eSuc(1) plus_enat_simps(1) semiring_norm(5)) 
        apply(simp) done   
      done
    subgoal
      apply simp          
      apply(safe) subgoal for s apply(cases "s ''x'' = int n") apply(simp)          
        subgoal apply (simp add: eSuc_enat plus_1_eSuc(2)) 
            apply(simp add: n') apply (simp add: mydiv_le_E) done 
        apply simp          
        done
      done
    done      
   then show ?thesis by simp
qed
   
lemma  "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (n+1) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }" 
proof -  
  have "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat (n+1) + emb (s ''x'' = int n)} strip ({3} Ab (''y'' ::= N 0;; Wsum)) {\<lambda>s. 0 }"
    apply(rule vc_sound')
    subgoal
      apply simp
      apply(safe) subgoal for s apply(cases "0 < s ''x''")
         apply(simp)
    apply ( smt Suc_eq_plus1 Suc_nat_eq_nat_zadd1 distrib_left_numeral eSuc_numeral enat_numeral eq_iff iadd_Suc_right nat_mult_1_right one_add_one plus_1_eSuc(1) plus_enat_simps(1) semiring_norm(5)) 
        apply(simp) done   
      done
    subgoal
      apply simp          
      apply(safe) subgoal for s apply(cases "s ''x'' = int n") apply(simp)          
        subgoal apply (simp add: eSuc_enat plus_1_eSuc(2)) 
            apply (simp add: mydiv_le_E) done 
        apply simp          
        done
      done
    done      
   then show ?thesis by simp
qed   
    
   
    
abbreviation "Wsum1 z ==  
  {\<lambda>s. enat (z * nat (s ''x''))} WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"
    
abbreviation "Wsum2 n vier ==  
  {\<lambda>s. enat (vier * (nat (s ''x'') +  n + 1))  } WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"
   
  
    


end