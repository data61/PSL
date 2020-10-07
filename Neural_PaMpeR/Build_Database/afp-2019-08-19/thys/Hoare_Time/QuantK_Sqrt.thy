theory QuantK_Sqrt 
imports QuantK_VCG "HOL-Library.Discrete"
begin 
     
subsection \<open>Example: discrete square root in the quantitative Hoare logic\<close>  
  
  
text \<open>As an example, consider the following program that computes the discrete square root:\<close>  
     
definition c :: com where "c= 
         ''l''::= N 0 ;;
         ''m'' ::= N 0 ;;
         ''r''::= Plus (N 1) (V ''x'');;
         (WHILE (Less (Plus (N 1) (V ''l'')) (V ''r'')) 
              DO (''m'' ::= (Div (Plus (V ''l'') (V ''r'')) (N 2)) ;; 
                 (IF Not (Less (Times (V ''m'') (V ''m'')) (V ''x'')) 
                    THEN ''l'' ::= V ''m''
                    ELSE ''r'' ::= V ''m'');;
                 ''m'' ::= N 0))" 
 
text \<open>In this theory we will show that its running time is in the order of magnitude of the
      logarithm of the variable ''x''\<close>  
     

text \<open>a little lemma we need later for bounding the running time:\<close>
  
lemma absch: "\<And>s k. 1 + s ''x'' = 2 ^ k \<Longrightarrow> 5 * k \<le> 96 + 100 * Discrete.log (nat (s ''x''))"  
proof -
  fix s :: state and  k :: nat 
  assume F: " 1 + s ''x'' = 2 ^ k " 
  then have i: "nat (1 + s ''x'') =  2 ^ k" and nn: "s ''x''\<ge> 0"  apply (auto simp: nat_power_eq)
    by (smt one_le_power)          
  have F: "1 + nat (s ''x'') = 2 ^k" unfolding i[symmetric] using nn by auto
  show "5 * k \<le> 96 + 100 * Discrete.log (nat (s ''x''))"
  proof (cases "s ''x'' \<ge> 1")
    case True
    have "5 * k = 5 * (Discrete.log (2^k))"     by auto
    also have "\<dots> = 5 * Discrete.log (1 + nat (s ''x''))" by(simp only: F[symmetric])
    also have "\<dots> \<le> 5 * Discrete.log (nat (s ''x'' + s ''x''))" using True
      apply auto apply(rule monoD[OF log_mono]) by auto
    also have "\<dots> = 5 *  Discrete.log (2 * nat (s ''x''))" by (auto simp: nat_mult_distrib) 
    also have "\<dots> = 5 + 5 * (Discrete.log (nat (s ''x'')))" using True by auto
    also have "\<dots> \<le> 96 + 100 * Discrete.log (nat (s ''x''))" by simp
    finally show ?thesis .
  next
    case False
    with nn have gt1: "s ''x'' = 0" by auto
    from F[unfolded gt1] have "2 ^ k = (1::int)" using log_Suc_zero by auto 
    then have "k=0"
      by (metis One_nat_def add.right_neutral gt1 i n_not_Suc_n nat_numeral nat_power_eq_Suc_0_iff numeral_2_eq_2 numeral_One) 
    then show ?thesis by(simp add: gt1)
  qed 
qed
    
  
text \<open>For simplicity we assume, that during the process all segments between ''l'' and ''r'' have
      as length a power of two. This simplifies the analysis.
      To obtain this we choose the prepotential P accordingly.

      Now lets show the correctness of our time complexity: the binary search is in O(log ''x'') \<close>
    
lemma 
  assumes   
    P: "P  = (\<lambda>s. \<up> (  (\<exists>k. 1 + s ''x''  = 2 ^ k)) + (Discrete.log (nat ( s ''x'')) + 1))" and
      Q[simp]: "Q = (\<lambda>_. 0)" 
  shows " \<turnstile>\<^sub>2\<^sub>' {P} c {Q}"
proof -
  \<comment> \<open>first we create an annotated command\<close>
  let ?lb = "''m'' ::= 
              (Div (Plus (V ''l'') (V ''r'')) (N 2)) ;; 
              (IF Not (Less (Times (V ''m'') (V ''m'')) (V ''x'')) 
                THEN ''l'' ::= V ''m''
                ELSE ''r'' ::= V ''m'');;
              (''m'' ::= N 0)::acom"
  \<comment> \<open>with an invariant potential\<close>
  define I   where "I \<equiv> (\<lambda>s::state. (( emb (  s ''l''\<ge>0   \<and> ( \<exists>k. s ''r'' - s ''l'' = 2 ^ k) ) + 5 * Discrete.log (nat (s ''r'') - nat (s ''l'')))::enat) )"
  let ?C = " ((''l''::= N 0) :: acom) ;; (''m'' ::= N 0) ;; ''r''::= Plus (N 1) (V ''x'');; ({I} WHILE (Less (Plus (N 1) (V ''l'')) (V ''r'')) DO ?lb)"
  
  \<comment> \<open>we show that the annotated command corresponds to the command we are interested in\<close>
  have s: "strip ?C = c" unfolding c_def by auto
    
  \<comment> \<open>now we show that the annotated command is correct; here we use the VCG for the QuantK logic\<close>
  have v: "\<turnstile>\<^sub>2\<^sub>' {P} strip ?C {Q}"
  proof (rule vc_sound'', safe) 
    
    \<comment> \<open>A) first lets show the verification conditions:\<close>
    show "vc ?C Q" apply auto 
      unfolding I_def
      subgoal for s
        apply(cases "(\<exists>k. s ''r''  - s ''l'' = 2 ^ k)") apply auto
        apply(cases "(1 + s ''l'' < s ''r'')") apply auto
        apply(cases "0 \<le> s ''l''") apply auto 
      proof (goal_cases)
        case (1 k)
        then have "k>0" using gr0I by force 
        then obtain k' where k': "k=k'+1" by (metis Suc_eq_plus1 Suc_pred)  
        from 1 k' have R: " s ''r'' - (s ''l'' + s ''r'') div 2 = 2 ^ k'" by auto
        have gN: "s ''l''\<le>s ''r''"  "s ''l''\<ge>0" "s ''r'' \<ge> 0" using 1 by auto
        have n: "nat ( s ''r'' - (s ''l'' + s ''r'') div 2 ) =  nat (s ''r'') - nat ((s ''l'' + s ''r'') div 2)"
          using gN  apply(simp add: nat_diff_distrib nat_div_distrib) done
            
        have R': "nat (s ''r'') -  nat ((s ''l'' + s ''r'') div 2) = 2 ^ k'"
          apply(simp only: n[symmetric] R nat_power_eq) by auto 
        have S': "nat (s ''r'') - nat (s ''l'') = 2 ^ k"
          using gN apply(simp only: nat_diff_distrib[symmetric] 1(2) nat_power_eq) by auto
        have N: "0 \<le> (s ''l'' + s ''r'') div 2" using gN by auto     
            
        from N  show ?case apply (simp ) apply (simp only : R R' S' k') by (auto simp: eSuc_enat plus_1_eSuc(2))    
      qed 
      subgoal for s 
        apply(cases "\<exists>k. s ''r''  - s ''l'' = 2 ^ k") apply auto
        apply (cases "(1 + s ''l'' < s ''r'')") apply auto
        apply(cases "0 \<le> s ''l''") apply auto 
      proof (goal_cases)
        case (1 k)
        from 1(2,3) have "k>0" using gr0I by force 
        then obtain k' where k': "k=k'+1" by (metis Suc_eq_plus1 Suc_pred)            
        from 1 k' have R: " (s ''l'' + s ''r'') div 2 - s ''l'' = 2 ^ k'" by auto 
        have gN: "s ''l''\<le>s ''r''"  "s ''l''\<ge>0" "s ''r'' \<ge> 0" using 1 by auto
        have n: "nat ((s ''l'' + s ''r'') div 2 - s ''l'') =  nat ( (s ''l'' + s ''r'') div 2) - nat (s ''l'')"
          using gN  apply(simp add: nat_diff_distrib nat_div_distrib) done
            
        have R': "nat ( (s ''l'' + s ''r'') div 2) - nat (s ''l'') = 2 ^ k'"
          apply(simp only: n[symmetric] R nat_power_eq) by auto 
        have S': "nat (s ''r'') - nat (s ''l'') = 2 ^ k"
          using gN apply(simp only: nat_diff_distrib[symmetric] 1(2) nat_power_eq) by auto 
            
        show ?case   apply (simp only : R R' S' k') by (auto simp: eSuc_enat plus_1_eSuc(2))        
      qed done        
  next
    \<comment> \<open>B) lets show that the precondition implies the weakest precondition, and that the
            time bound of C can be bounded by log ''x''\<close>
    fix s
    show "pre ?C Q s \<le> enat 100 * P s" unfolding  I_def apply(simp only: P)  apply auto apply(cases "(\<exists>k. 1 + s ''x''   = 2 ^ k)") 
       apply (auto simp: eSuc_enat plus_1_eSuc(2) nat_power_eq) 
        using absch by force
  qed auto
    
  from s v show ?thesis by simp
qed

end