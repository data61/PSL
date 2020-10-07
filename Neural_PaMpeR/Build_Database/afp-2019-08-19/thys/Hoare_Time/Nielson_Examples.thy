theory Nielson_Examples
imports Nielson_VCG
begin


subsubsection \<open>example\<close>
  
  
lemma "\<turnstile>\<^sub>1 {%l s. True} SKIP;; SKIP { %s. 1 \<Down> %l s. True}"
proof -
 let ?T = "%l s. True"
 have "\<turnstile>\<^sub>1 {%l s. True} strip (Aconseq ?T ?T (%s. 1) (Aseq Askip Askip)) { %s. 1 \<Down> %l s. True}"
   apply(rule vc_sound'') by auto
 then show ?thesis by simp
qed  
  
  
   
lemma "finite (support P) \<Longrightarrow> \<turnstile>\<^sub>1 {P} strip Askip {time Askip \<Down> P}"
  apply(rule vc_sound')
      apply(simp)
     apply(simp)
    apply(simp)
   apply(simp)  done


lemma support_single2: "support (\<lambda>l s. P s) = {}"
  unfolding support_def by fastforce

lemma "\<turnstile>\<^sub>1 { %l s. True } strip (Aassign a (N 1)) {time (Aassign a (N 1)) \<Down> %l s. s a = 1}"
  apply(rule vc_sound')
      apply(simp_all add: support_single2)  done

lemma "\<turnstile>\<^sub>1 { %l s. True } strip ( (a ::= (N 1)) ;; Askip ) {time ( (a ::= (N 1)) ;; Askip ) \<Down> %l s. s a = 1}"
  apply(rule vc_sound')
      apply(simp_all add: support_single2) done

lemma "\<turnstile>\<^sub>1 { %l s. True } strip ( (a ::= (N 1)) ;; b ::= (V a) ) {time ( (a ::= (N 1)) ;; b ::= (V a) ) \<Down> %l s. s b = 1}"
  apply(rule vc_sound')
  by(simp_all add: support_single2)

lemma assumes     
  E: "E = (%s. 1 + 2 * (4 - nat (s a)))" and
  C: "C = ({(I,(S,(E)))} WHILE Less (V a) (N 3) DO a ::= Plus (V a) (N 1) )"
shows "\<And>s. 0 \<le> s a \<Longrightarrow> time C s \<le> 9"
  unfolding C E apply(simp) done

paragraph "Count up to 3"

lemma example_count_upto_3: assumes 
  I: "I = (%l s. s a \<ge> 0)" and
  E: "E = (%s. 1 + 2 * (4 - nat (s a)))" and
  S: "S = (%s. (if s a \<ge> 3 then s else s(a:=3) ))" and
  C: "C = ({(I,(S,(E)))} WHILE Less (V a) (N 3) DO a ::= Plus (V a) (N 1) )"
shows "\<turnstile>\<^sub>1 { %l s. 0 \<le> s a } strip C {time C \<Down> %l s. True }"
  unfolding C
  apply(rule vc_sound')
  subgoal
    apply(simp)
    apply(safe) 
    subgoal unfolding I by simp
    subgoal unfolding I E by simp
    subgoal unfolding S by auto
    subgoal unfolding I E by auto
    subgoal unfolding I S by auto 
    done
  subgoal
    by simp
  subgoal  
    unfolding I  by(simp add: support_inv) 
  subgoal unfolding I by simp
  done 


paragraph "Count up to b"

lemma example_count_upto_b: assumes 
  I: "I = (%l s. s a \<ge> 0 )" and
  E: "E = (%s. 1 + 2 * ((nat b+1) - nat (s a)))" and
  S: "S = (%s. (if s a \<ge> b then s else s(a:=b) ))" and
  C: "C = ({(I,(S,(E)))} WHILE Less (V a) (N b) DO a ::= Plus (V a) (N 1) )"
shows "\<turnstile>\<^sub>1 { %l s. 0 \<le> s a } strip C {time C \<Down> %l s. True }"
  unfolding C
  apply(rule vc_sound') by(auto simp: I E S support_inv)

paragraph " Example: multiplication by repeated addition"

lemma helper: "(A::int) * B + B = (A+1) * B" by(auto simp: distrib_right)
  
lemma mult: assumes  
  I: "I = (%l s. s ''a'' \<ge> 0 \<and> s ''a'' \<ge> s ''z'' \<and> s ''z'' \<ge> 0  \<and> s ''y'' =  s ''z'' * (s ''b'')  )" and
  E: "E = (%s. 1 + 3 * ((nat (s ''a'') + 1) - nat (s ''z'')))" and
  S: "S = (%s. (if s ''z'' \<ge> s ''a'' then s else s(''y'':=(s ''a'') * (s ''b''), ''z'':=s ''a''  ) ))" and
  C: "C = (''y'' ::= (N 0);; ''z'' ::= (N 0) ;; {(I,(S,(E)))}  WHILE Less (V ''z'') (V ''a'') DO (''y'' ::= Plus (V ''y'') (V ''b'') ;; ''z'' ::= Plus (V ''z'') (N 1)) )" and
  f: "f = (%s. 3 * (nat(s ''a'') + 2))"
shows "\<turnstile>\<^sub>1 { %l s. 0 \<le> s ''a''  } strip C { f \<Down> %l s. s ''y'' = s ''a'' * (s ''b'') }"
  unfolding C 
  apply(rule vc_sound'')
     apply(auto simp: I E S distrib_right support_inv f)
  subgoal for s by (auto simp add: helper)   
  done
      

(* try to use abstraction *)    
lemma mult_abstract: assumes  
  I: "I = (%l s. s ''a'' \<ge> 0 \<and> s ''a'' \<ge> s ''z'' \<and> s ''z'' \<ge> 0  \<and> s ''y'' =  s ''z'' * (s ''b'')  )" and
  E: "E = (%s. 1 + 2* ((nat (s ''a'') + 1) - nat (s ''z'')))" and
  S: "S = (%s. (if s ''z'' \<ge> s ''a'' then s else s(''y'':=(s ''a'') * (s ''b''), ''z'':=s ''a''  ) ))" and
  e: "e = (%s. 1)" and
  lb[simp]: "(lb::acom) = ({\<lambda>l s. I l s \<and> s ''z'' < s ''a''  /I/e} CONSEQ (''y'' ::= Plus (V ''y'') (V ''b'') ;; ''z'' ::= Plus (V ''z'') (N 1)) )" and
  l[simp]: "(l::acom) = {(I,(S,(E)))}  WHILE  (Less (V ''z'') (V ''a'')) DO lb" and
  e'[simp]: "e' = (%s. 1 + (nat (s ''a'')))" and
  wl[simp]: "(wl::acom) = {I/\<lambda>l s. I l s \<and> s ''z'' \<ge> s ''a''/e'} CONSEQ l" and
  C: "(C::acom) = (''y'' ::= (N 0);; ''z'' ::= (N 0) ;; wl )" and
  f: "f = (%s. nat(s ''a'') + 1)"
shows "\<turnstile>\<^sub>1 { %l s. 0 \<le> s ''a''  } strip (  {%l s. 0 \<le> s ''a''/ %l s. s ''y'' = s ''a'' * (s ''b'')/ f} CONSEQ C) { f \<Down> %l s. s ''y'' = s ''a'' * (s ''b'') }"
  unfolding C 
  apply(rule vc_sound'')
     apply(auto simp: I E S distrib_right support_inv f e)
  subgoal for s by (auto simp add: helper) 
    apply(rule exI[where x=100]) apply auto
    apply(rule exI[where x=100]) apply auto 
  done
     

paragraph \<open>Example: nested loops\<close>

lemma nested: assumes   
    I2: "I2 = (%l s. s ''a'' \<ge> 0 \<and> s ''b'' \<ge> 0  \<and> s ''a'' >  s ''z''  \<and> s ''z'' \<ge> 0 \<and>   s ''b'' \<ge> s ''g'' \<and> s ''g'' \<ge> 0  \<and> s ''y'' = (s ''z'')  * (s ''b'') + s ''g''  )" and
 
  I1: "I1 = (%l s. s ''a'' \<ge> 0 \<and> s ''b'' \<ge> 0 \<and> s ''a'' \<ge>  s ''z'' \<and> s ''z'' \<ge> 0  \<and> s ''y'' =  s ''z'' * (s ''b'')  )" and  
  
  E2: "E2 = (%s. 1 + 3 * ((nat (s ''b'') ) - nat (s ''g'')))" and
  S2: "S2 = (%s. (if s ''g'' \<ge> s ''b'' then s else s(''y'':=(s ''z'')  * (s ''b'') + s ''b'' , ''g'':=s ''b''  ) ))" and
     
  E1: "E1 = (%s. 1 + ( 4 + (3 * ((nat (s ''b'')  ))) ) * ((nat (s ''a'') ) - nat (s ''z'')))" and
  S1: "S1 = (%s. (if s ''z'' \<ge> s ''a'' then s else s(''y'':=(s ''a'') * (s ''b''), ''z'':=s ''a'', ''g'':=s ''b''  ) ))" and
  C: "C = (''y'' ::= (N 0);; 
  ''z'' ::= (N 0) ;;
  {(I1,(S1,(E1)))}  WHILE Less (V ''z'') (V ''a'') DO
  (
  ''g'' ::= (N 0) ;;                                                 
  (
  {(I2,(S2,(E2)))}  WHILE Less (V ''g'') (V ''b'') DO
  (''y'' ::= Plus (V ''y'') (N 1);;
  ''g'' ::= Plus (V ''g'') (N 1))
  
  ) ;;  
  ''z'' ::= Plus (V ''z'') (N 1))
  )" and
  f: "f = (%s. 3 + 4*nat(s ''a'')+ 3 * (nat(s ''a'') * nat(s ''b'')))"
shows "\<turnstile>\<^sub>1 { %l s. 0 \<le> s ''a'' \<and> s ''b'' \<ge> 0  } strip C { f \<Down> %l s. s ''y'' = s ''a'' * (s ''b'') }"
  unfolding C 
  apply(rule vc_sound'') 
proof( goal_cases)
  case 1
  show ?case   apply(simp)
  proof(safe, goal_cases) 
    case (1 l s) (* outer loop: invariant implies precondition of body *) 
    from 1 show ?case unfolding I1 unfolding I2   by(auto )   
  next
    case (2 l s) (* outer loop:  E1 is correct *)
    then show ?case unfolding I1 S2  apply(auto) unfolding E2 apply(simp) unfolding E2   apply(auto) 
      unfolding E1 apply(simp)
      
      apply(simp) 
    proof (goal_cases)
      case 1
      then have g: "s ''a'' > s ''z''" by linarith
      then have p: "(nat (s ''a'') - nat (s ''z'' + 1)) = (nat (s ''a'') - nat (s ''z'')) - 1" and z: "(nat (s ''a'') - nat (s ''z'')) \<ge> 1"
        using "1" apply linarith 
        using g 1 by linarith
      
      have "Suc (Suc (Suc (Suc ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'' + 1)) + 3 * nat (s ''b''))))) =
        4 + ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'' + 1)) + 3 * nat (s ''b''))
        " by auto
      also
      have "\<dots> = 4 + ( (4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'')) - (4 + 3 * nat (s ''b''))  + 3 * nat (s ''b''))"
        apply(simp only: p)
      proof -
        have "\<And>n na. (n::nat) * na - n = n * (na - 1)"
          by (simp add: diff_mult_distrib2)
        then show "4 + ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'') - 1) + 3 * nat (s ''b'')) = 4 + ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'')) - (4 + 3 * nat (s ''b'')) + 3 * nat (s ''b''))"
          by presburger
      qed
      also
      have "\<dots> = (4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z''))"
        using z
        by (smt \<open>4 + ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'' + 1)) + 3 * nat (s ''b'')) = 4 + ((4 + 3 * nat (s ''b'')) * (nat (s ''a'') - nat (s ''z'')) - (4 + 3 * nat (s ''b'')) + 3 * nat (s ''b''))\<close> add.left_commute diff_add distrib_left mult.right_neutral p)  
      
      finally show ?case by simp
    qed
    
  next
    case (3 l s)  (* outer loop: S is preserved *)
    { fix i :: int assume "0 \<le> i" then have "int (\<Sum>{0..<nat i}) + i = int (\<Sum>{0..nat i})"
        by (simp add: sum.last_plus)    } note bla=this
    from 3 show ?case unfolding I1 S1 S2  apply(auto simp add:  )
    proof (goal_cases)
      case 1
      then have a: "s ''a'' =  s ''z'' + 1" by linarith
      show ?case apply(simp only: a) using 1
        by (simp add: distrib_left mult.commute fun_upd_twist)     
    qed    
  next
    case (4 l s) (* outer loop: post condition is correct after exiting the loop *)
    then show ?case unfolding I1  by (auto)
  next
    case (5 l s) (* outer loop: time expression is correct after exiting the loop *)
    then show ?case unfolding I1 E1 by auto
  next
    case (6 l s) (* outer loop: S correct if loop guard not fullfilled *)
    then show ?case unfolding I1 S1 by(simp)
    
    
  next
    case (7 l s)  (* inner loop: invariant for >0 implies loop guard *) 
    then show ?case unfolding I2 apply(simp) done 
  next 
    case (8 l s) (* inner loop:  E1 is correct *)
    then show ?case unfolding I2    apply(auto) unfolding  E2  by(auto)  
  next
    case (9 l s)  (* inner loop: S is preserved *)
    { fix i :: int assume "0 \<le> i" then have "int (\<Sum>{0..<nat i}) + i = int (\<Sum>{0..nat i})"
        by (simp add: sum.last_plus)    } note bla=this
    from 9 show ?case unfolding I2   S2  apply(auto simp add:  ) done  
  next  
    case (10 l s) (* inner loop: post condition is correct after exiting the loop *)
    then show ?case unfolding I2 I1 by (auto simp add: distrib_left mult.commute)
  next
    case (11 l s) (* inner loop: time expression is correct after exiting the loop *)
    then show ?case unfolding I2 E2 by (simp)
  next
    case (12 l s) (* inner loop: S correct if loop guard not fullfilled *)
    then show ?case unfolding I2 S2 by(simp) 
  qed 
next
  case 2
  show ?case apply (rule exI[where x=1]) by (auto simp add: I1 C E1 f distrib_left mult.commute)    
qed (auto simp: I1 I2 support_single2)  

   
  
  
  
paragraph "with logical variables"

lemma fin_sup_single: "finite (support (\<lambda>l. P (l a)))"
  apply(rule finite_subset[OF support_single]) by simp

lemmas fin_support = fin_sup_single 
  
lemma finite_support_and: "finite (support A) \<Longrightarrow> finite (support B) \<Longrightarrow> finite (support (\<lambda>l s. A l s \<and> B l s))"
  apply(rule finite_subset[OF support_and]) by blast
   

end