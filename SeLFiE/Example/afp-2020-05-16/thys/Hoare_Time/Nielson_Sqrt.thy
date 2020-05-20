theory Nielson_Sqrt
imports Nielson_VCGi "HOL-Library.Discrete"
begin
     
subsection \<open>Example: discrete square root in Nielson's logic\<close>  
  
  
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
      To obtain this we choose the precondition P accordingly.

      Now lets show the correctness of our time complexity: the binary search is in O(log ''x'') \<close>
  
lemma 
  assumes P: "P  = (\<lambda>l s.  (\<exists>k. 1 + s ''x''  = 2 ^ k) )"
      and e : "e  = (\<lambda>s. Discrete.log (nat (s ''x'')) + 1)" and
      Q[simp]: "Q = (\<lambda>l s. True)" 
  shows " \<turnstile>\<^sub>1 {P} c { e \<Down> Q}"
proof -
  
  \<comment> \<open>first we create an annotated command\<close>
  let ?lb = "''m'' ::= 
              (Div (Plus (V ''l'') (V ''r'')) (N 2)) ;; 
              (IF Not (Less (Times (V ''m'') (V ''m'')) (V ''x'')) 
                THEN ''l'' ::= V ''m''
                ELSE ''r'' ::= V ''m'');;
              (''m'' ::= N 0)::acom"
  \<comment> \<open>with an Invariant\<close>
  define I :: assn2 where "I \<equiv> (\<lambda>l s. (\<exists>k. s ''r'' - s ''l'' = 2 ^ k ) \<and> s ''l'' \<ge> 0 )"
    
  \<comment> \<open>and an time bound annotation for the loop\<close>  
  define E :: tbd where "E \<equiv> %s. 1 + 5 * Discrete.log (nat(s ''r'' - s ''l''))"
  define S :: "state \<Rightarrow> state" where "S \<equiv> %s. s"
  define Es :: "vname \<Rightarrow> vname set" where "Es  = (%x. {x})"
    
  define R :: "(assn2*(vname set))*((state\<Rightarrow>state)*(tbd*((vname set*(vname \<Rightarrow> vname set)))))"
      where "R=((I,{''l'',''r''}),(S,(E,({''l'',''r''},Es))))"
    
  let ?C = "''l''::= N 0 ;; (''m'' ::= N 0) ;; ''r''::= Plus (N 1) (V ''x'');; ({R} WHILE (Less (Plus (N 1) (V ''l'')) (V ''r'')) DO ?lb)"
  
  \<comment> \<open>we show that the annotated command corresponds to the command we are interested in\<close>  
  have s: "strip ?C = c" unfolding c_def by auto
    
  \<comment> \<open>now we show that the annotated command is correct; here we use the improved VCG and the
      Nielson\<close>
  have v: "\<turnstile>\<^sub>1 {P} strip ?C {e  \<Down> Q}"
  proof (rule vc_sound'', safe)     
    
    \<comment> \<open>A) first lets show the verification conditions:\<close>
    show "vc ?C Q {} {}"  unfolding R_def apply (simp only: vc.simps) apply auto
      subgoal unfolding I_def by auto
      subgoal unfolding I_def by auto
      subgoal unfolding E_def by auto
    proof (goal_cases) 
      fix s::state and l
      assume  I: "I l s" and 2: "1 + s ''l'' < s ''r''"
      from I obtain k :: nat where 3: "s ''r'' - s ''l'' = 2 ^ k" and 4: "s ''l'' \<ge> 0" unfolding I_def by blast
      from 3 2 have "k>0" using gr0I by force 
      then obtain k' where k': "k=k'+1" by (metis Suc_eq_plus1 Suc_pred) 
          
      from 3 k' have R1: " s ''r'' - (s ''l'' + s ''r'') div 2 = 2 ^ k'" and
          R2: "(s ''l'' + s ''r'') div 2 - s ''l'' = 2 ^ k'" by auto         
      then have E1: "\<exists>k. s ''r'' - (s ''l'' + s ''r'') div 2 = 2 ^ k" and
          E2: "\<exists>k. (s ''l'' + s ''r'') div 2 - s ''l'' = 2 ^ k" by auto         
      then show "I l (s(''l'' := (s ''l'' + s ''r'') div 2, ''m'' := 0))" and 
          "I l (s(''r'' := (s ''l'' + s ''r'') div 2, ''m'' := 0))" using 2 4 unfolding I_def by auto 
          
      show "Suc (Suc (Suc (Suc (Suc (E (s(''l'' := (s ''l'' + s ''r'') div 2, ''m'' := 0))))))) \<le> E s"
        unfolding E_def apply simp unfolding R1 3 k' by (auto  simp: nat_power_eq nat_mult_distrib)
      show "Suc (Suc (Suc (Suc (Suc (E (s(''r'' := (s ''l'' + s ''r'') div 2, ''m'' := 0))))))) \<le> E s"
        unfolding E_def apply simp unfolding R2 3 k' by (auto  simp: nat_power_eq nat_mult_distrib)
    next
      fix l s 
      show "Suc 0 \<le> E s" unfolding E_def by auto
      show "Suc 0 \<le> E s" unfolding E_def by auto
    qed    
  next
    \<comment> \<open>B) lets show that the precondition implies the weakest precondition, and that the
            time bound of C can be bounded by log ''x''\<close>
    fix s
    show "(\<exists>k>0. \<forall>l s. P l s \<longrightarrow> pre ?C Q l s \<and> time ?C s \<le> k * e s)"
      apply(rule exI[where x=100])
      unfolding P R_def I_def E_def e by (auto simp: nat_power_eq absch) 
  qed
    \<comment> \<open>last side conditions are proven automatically\<close>
    (auto simp: Q support_inv R_def I_def)
    
  \<comment> \<open>now we conclude with the correctness of the Hoare triple involving the time bound\<close>
  from s v show ?thesis by simp
qed

  
  



end
