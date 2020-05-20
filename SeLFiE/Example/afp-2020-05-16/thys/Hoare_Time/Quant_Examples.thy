subsection "Examples"

theory Quant_Examples
imports Quant_VCG
begin

fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"

lemma example: "\<turnstile>\<^sub>2 {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }"
apply(rule Seq)
 prefer 2
 apply(rule conseq)
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

lemma example_sound:  "\<Turnstile>\<^sub>2 {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }"
apply(rule hoare2_sound) apply (rule example) done
   
subsubsection \<open>Examples for the use of the VCG\<close>
      
abbreviation "Wsum ==  
  {\<lambda>s. enat (3 * nat (s ''x''))} WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
      ''x'' ::= Plus (V ''x'') (N (- 1)))"  
  
lemma "\<turnstile>\<^sub>2 {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} ''y'' ::= N 0;; wsum {\<lambda>s. 0 }" 
proof -
  have "\<turnstile>\<^sub>2 {\<lambda>s. enat (2 + 3*n) + emb (s ''x'' = int n)} strip (''y'' ::= N 0;; Wsum) {\<lambda>s. 0 }"
    apply(rule vc_sound')
    subgoal
      apply simp
      apply(safe) subgoal for s apply(cases "0 < s ''x''")
         apply(simp)
         apply (smt Suc_eq_plus1 Suc_nat_eq_nat_zadd1 distrib_left_numeral eSuc_numeral enat_numeral eq_iff iadd_Suc_right nat_mult_1_right one_add_one plus_1_eSuc(1) plus_enat_simps(1) semiring_norm(5)) 
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

end