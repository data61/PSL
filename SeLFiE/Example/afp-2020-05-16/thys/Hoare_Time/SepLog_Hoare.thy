section "Hoare Logic based on Separation Logic and Time Credits" 
theory SepLog_Hoare
  imports Big_StepT_Partial    "SepLogAdd/Sep_Algebra_Add"                                           
begin


subsection "Definition of Validity"


definition hoare3_valid :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>3 {(1_)}/ (_)/ { (1_)}" 50) where
"\<Turnstile>\<^sub>3 { P } c { Q }  \<longleftrightarrow>  
     (\<forall>ps n. P (ps,n)
     \<longrightarrow> (\<exists>ps' m. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps')
           \<and> n\<ge>m \<and> Q (ps', n-m))  )"
 
lemma alternative: "\<Turnstile>\<^sub>3 { P } c { Q }  \<longleftrightarrow>  
     (\<forall>ps n. P (ps,n)
     \<longrightarrow> (\<exists>ps' t n'. ((c,ps) \<Rightarrow>\<^sub>A t \<Down> ps')
             \<and> n=n'+t \<and> Q (ps', n'))  )" 
proof rule
  assume "\<Turnstile>\<^sub>3 {P} c { Q}"
  then have P: "(\<forall>ps n. P (ps,n) \<longrightarrow> (\<exists>ps' m. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps') \<and> n\<ge>m \<and> Q (ps', n-m))  )" unfolding hoare3_valid_def.
  show "\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' m e. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> n = e + m \<and> Q (ps', e))"
  proof (safe)
    fix ps n
    assume "P (ps, n)"
    with P obtain ps' m where Z: "((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps')" "n\<ge>m" "Q (ps', n-m)" by blast
    show "\<exists>ps' m e. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> n = e + m \<and> Q (ps', e)"
    apply(rule exI[where x=ps'])
    apply(rule exI[where x=m]) 
      apply(rule exI[where x="n-m"]) using Z by auto
  qed
next
  assume "\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' m e. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> n = e + m \<and> Q (ps', e))"
  then show "\<Turnstile>\<^sub>3 { P } c { Q } "  unfolding hoare3_valid_def
     by fastforce
qed
       

subsection "Hoare Rules"    
     
inductive
  hoareT3 :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>3 ({(1_)}/ (_)/ { (1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>3 {$1} SKIP { $0}"  |

Assign:  "\<turnstile>\<^sub>3 {lmaps_to_expr_x x a v ** $1} x::=a { (%(s,c). dom s = vars a - {x} \<and> c = 0) ** x \<hookrightarrow> v }"  |

If: "\<lbrakk> \<turnstile>\<^sub>3 { \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s } c\<^sub>1 { Q };
       \<turnstile>\<^sub>3 {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } c\<^sub>2 { Q } \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>3 { (\<lambda>(s,n). P (s,n) \<and> vars b \<subseteq> dom s) ** $1} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q}"   |

Frame:  "\<lbrakk>    \<turnstile>\<^sub>3 { P } C { Q  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3 { P ** F } C { Q ** F } "  |

Seq:  "\<lbrakk> \<turnstile>\<^sub>3 { P } C\<^sub>1 { Q } ;  \<turnstile>\<^sub>3 { Q } C\<^sub>2 { R  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3 { P } C\<^sub>1 ;; C\<^sub>2 { R } "  |

While:  "\<lbrakk> \<turnstile>\<^sub>3 { (\<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s) } C { P  ** $1 }  \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3 { (\<lambda>(s,n). P (s,n) \<and>  vars b \<subseteq> dom s) ** $1 } WHILE b DO C {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } "  |
  
conseq: "\<lbrakk> \<turnstile>\<^sub>3 {P}c{Q} ; \<And>s. P' s \<Longrightarrow> P s ; \<And>s. Q s \<Longrightarrow> Q' s \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>3 {P'}c{ Q'}"   |

normalize:  "\<lbrakk>    \<turnstile>\<^sub>3 { P ** $m } C { Q  ** $n }; n\<le>m \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3 { P ** $(m-n) } C { Q } "   |

constancy:  "\<lbrakk>    \<turnstile>\<^sub>3 { P } C { Q }; \<And>ps ps'. ps = ps' on UNIV - lvars C \<Longrightarrow> R ps = R ps'  \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3 { %(ps,n). P (ps,n) \<and> R ps } C { %(ps,n). Q (ps,n) \<and> R ps } " |

Assign''': "\<turnstile>\<^sub>3 {  $1 ** (x \<hookrightarrow> ds) } x ::= (N v) {  (x \<hookrightarrow> v) }" |

Assign'''': "\<lbrakk>  symeval P a v; \<turnstile>\<^sub>3 {P} x ::= (N v) {Q'}  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>3 {P} x ::= a {Q'}" |

Assign4:  "\<turnstile>\<^sub>3 { (\<lambda>(ps,t). x\<in>dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x\<mapsto>(paval a ps)),t) ) ** $1} x::=a { Q }" |

False: "\<turnstile>\<^sub>3 {  \<lambda>(ps,n). False } c {  Q }" |

pureI: "( P \<Longrightarrow>  \<turnstile>\<^sub>3 { Q} c { R}) \<Longrightarrow>  \<turnstile>\<^sub>3 {\<up>P ** Q} c { R}"
   

text \<open>Derived Rules\<close>

  
lemma Frame_R:  assumes "\<turnstile>\<^sub>3 { P } C { Q  }" "Frame P' P F"
             shows "\<turnstile>\<^sub>3 { P' } C { Q ** F } "  
  apply(rule conseq) apply(rule Frame) apply(rule assms(1))
      using assms(2) unfolding Frame_def by auto
  
lemma strengthen_post: assumes "\<turnstile>\<^sub>3 {P}c{Q}" "\<And>s. Q s \<Longrightarrow> Q' s"
  shows "\<turnstile>\<^sub>3 {P}c{ Q'}"
  apply(rule conseq)
    apply (rule assms(1))
    apply simp apply fact done
            
  
        
lemma weakenpre:  "\<lbrakk> \<turnstile>\<^sub>3 {P}c{Q} ; \<And>s. P' s \<Longrightarrow> P s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>3 {P'}c{ Q}"
  using conseq by auto
   
subsection \<open>Soundness Proof\<close>
   
    
       
lemma exec_preserves_disj: "(c,ps) \<Rightarrow>\<^sub>A t \<Down> ps' \<Longrightarrow> ps'' ## ps \<Longrightarrow> ps'' ## ps'" 
 apply(drule big_step_t3_post_dom_conv)  
  unfolding sep_disj_fun_def domain_conv by auto
    
lemma FrameRuleSound: assumes "\<Turnstile>\<^sub>3 { P  } C { Q  }"
  shows "\<Turnstile>\<^sub>3 { P ** F } C { Q ** F }"
proof -
  {
    fix ps n
    assume "(P \<and>* F) (ps, n)"
    then obtain pP nP pF nF where orth: "(pP, nP) ## (pF, nF)" and add: "(ps, n) = (pP, nP) + (pF, nF)"
              and P: "P (pP, nP)" and F: "F (pF, nF)" unfolding sep_conj_def by auto
    from assms[unfolded hoare3_valid_def] P
      obtain pP' m where ex: "(C, pP) \<Rightarrow>\<^sub>A m \<Down> pP'" and m: "m \<le> nP" and Q: "Q (pP', nP - m)" by blast
  
    have exF: "(C, ps) \<Rightarrow>\<^sub>A m \<Down> pP' + pF"  
       using Framer2 ex orth add by auto
    have QF: "(Q \<and>* F) (pP' + pF, n - m)"
      unfolding sep_conj_def
          apply(rule exI[where x="(pP',nP-m)"])
          apply(rule exI[where x="(pF,nF)"])
          using orth exec_preserves_disj[OF ex] add m F Q by (auto simp add: sep_add_ac) 
    have "(C, ps) \<Rightarrow>\<^sub>A m \<Down> pP'+pF \<and> m \<le> n \<and> (Q \<and>* F) (pP'+pF, n - m)"  
      using QF exF add m by auto 
    hence "\<exists>ps' m. (C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> n \<and> (Q \<and>* F) (ps', n - m)" by auto
  }
  thus ?thesis unfolding hoare3_valid_def by auto
qed

theorem hoare3_sound: assumes "\<turnstile>\<^sub>3 { P }c{ Q  }"
  shows "\<Turnstile>\<^sub>3 { P } c { Q }" using assms        
proof(induction  rule: hoareT3.induct) 
  case (False c Q)
  then show ?case by (auto simp: hoare3_valid_def)
next
  case Skip
  then show ?case by (auto simp: hoare3_valid_def dollar_def)   
next
  case (Assign4 x a Q)
  then show ?case
    apply (auto simp: dollar_def sep_conj_def hoare3_valid_def ) 
      subgoal for ps b y
        apply(rule exI[where x="ps(x \<mapsto> paval a ps)"])
          apply(rule exI[where x="Suc 0"]) by auto 
      done
next
  case (Assign x a v)   
  then show ?case unfolding hoare3_valid_def apply auto apply (auto simp: dollar_def ) apply (subst (asm) separate_othogonal)
      apply simp_all apply(intro exI conjI) 
      apply(rule big_step_t_part.Assign)
      apply (auto simp: pointsto_def)  unfolding  sep_conj_def
    subgoal for ps apply(rule exI[where x="((%y. if y=x then None else ps y) , 0)"])
      apply(rule exI[where x="((%y. if y = x then Some (paval a ps) else None),0)"])
        apply (auto simp: sep_disj_prod_def sep_disj_fun_def plus_fun_def)
      apply (smt domIff domain_conv)
      apply (metis domI insertE option.simps(3))
      using domIff by fastforce
    done  
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(3)[unfolded hoare3_valid_def]
    have T: "\<And>ps n. P (ps, n) \<Longrightarrow> vars b \<subseteq> dom ps \<Longrightarrow> pbval b ps
     \<Longrightarrow> (\<exists>ps' m. (c\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> n \<and> Q (ps', n-m))" by auto
  from If(4)[unfolded hoare3_valid_def]
    have F: "\<And>ps n. P (ps, n) \<Longrightarrow> vars b \<subseteq> dom ps \<Longrightarrow> \<not> pbval b ps
     \<Longrightarrow> (\<exists>ps' m. (c\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> n \<and> Q (ps', n-m))" by auto
  show ?case unfolding hoare3_valid_def apply auto apply (auto simp: dollar_def)   
  proof (goal_cases)
    case (1 ps n)   
    then obtain n' where P: "P (ps, n')" and dom: "vars b \<subseteq> dom ps" and Suc: "n = Suc n'" unfolding sep_conj_def
      by force
    show ?case 
    proof(cases "pbval b ps")
      case True
      with T[OF P dom] obtain ps' m where d: "(c\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps'" 
            and m1: "m \<le> n'" and Q: "Q (ps', n'-m)" by blast
      from big_step_t3_post_dom_conv[OF d] have klong: "dom ps' = dom ps" . 
      show ?thesis
        apply(rule exI[where x=ps']) apply(rule exI[where x="m+1"])   
          apply safe
            apply(rule big_step_t_part.IfTrue)
              apply (rule dom)
              apply fact
               apply (rule True)
           apply (rule d)
           apply simp 
        using m1 Suc apply simp
           using Q Suc by force          
    next
      case False
      with F[OF P dom] obtain ps' m where d: "(c\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps'" 
            and m1: "m \<le> n'" and Q: "Q (ps', n'-m)" by blast
      from big_step_t3_post_dom_conv[OF d] have "dom ps' = dom ps" . 
      show ?thesis
        apply(rule exI[where x=ps']) apply(rule exI[where x="m+1"])
          apply safe
            apply(rule big_step_t_part.IfFalse)
          apply fact
          apply fact
               apply (rule False)
           apply (rule d)
          apply simp
        using m1 Suc apply simp
           using Q Suc by force    
       qed   
     qed  
next     
  case (Frame P C Q F)
  then show ?case using FrameRuleSound by auto
next
  case (Seq P C\<^sub>1 Q C\<^sub>2 R) 
  show ?case unfolding hoare3_valid_def
  proof (safe, goal_cases)
    case (1 ps n)
    with Seq(3)[unfolded hoare3_valid_def] obtain ps' m where C1: "(C\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps'"
          and m: "m \<le> n" and Q: "Q (ps', n - m)" by blast
    with Seq(4)[unfolded hoare3_valid_def] obtain ps'' m' where C2: "(C\<^sub>2, ps') \<Rightarrow>\<^sub>A m' \<Down> ps''" 
          and m': "m' \<le> n - m" and R: "R (ps'', n - m - m')" by blast
    have a: "(C\<^sub>1;; C\<^sub>2, ps) \<Rightarrow>\<^sub>A m + m' \<Down> ps''" apply(rule big_step_t_part.Seq)
        apply fact+ by simp
    have b: "m + m' \<le> n" using m' m by auto
    have c: "R (ps'', n - (m + m'))" using R by simp
    show ?case apply(rule exI[where x=ps'']) apply(rule exI[where x="m+m'"])
      using a b c by auto
  qed
next
  case (While P b C)
  show ?case  unfolding hoare3_valid_def apply auto  apply (auto simp: dollar_def) 
  proof (goal_cases)
    case (1 ps n)  
    from 1 show ?case  
      proof(induct n arbitrary: ps rule: less_induct)
        case (less x ps3) 
          
      show ?case 
      proof(cases "pbval b ps3")
        case True
        \<comment> \<open>prepare premise to obtain ...\<close>
        from less(2) obtain x' where P: "P (ps3, x')" and dom: "vars b \<subseteq> dom ps3"  and Suc: "x = Suc x'" unfolding sep_conj_def dollar_def by auto 
        from P dom True have 
           g: "((\<lambda>(s, n). P (s, n) \<and> lmaps_to_axpr b True s)) (ps3, x')" 
            unfolding dollar_def by auto  
        \<comment> \<open>... the loop body from the outer IH\<close>
        from While(2)[unfolded hoare3_valid_def] g obtain ps3' x'' where C: "(C, ps3) \<Rightarrow>\<^sub>A x'' \<Down> ps3'" and x: "x'' \<le> x'" and P': "(P \<and>* $ 1) (ps3', x' - x'')" by blast
        then obtain x''' where P'': "P (ps3', x''')"  and Suc'': "x' - x'' = Suc x'''" unfolding sep_conj_def dollar_def by auto  
              
        from C big_step_t3_post_dom_conv have "dom ps3 = dom ps3'" by simp
        with dom have dom': "vars b \<subseteq> dom ps3'" by auto
              
        \<comment> \<open>prepare premises to ...\<close>
        from C big_step_t3_gt0 have gt0: "x'' > 0" by auto
        have "\<exists>ps' m. (WHILE b DO C, ps3') \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> (x - (1 + x'')) \<and> P (ps', (x - (1 + x'')) - m) \<and> vars b \<subseteq> dom ps' \<and> \<not> pbval b ps'"
          apply(rule less(1))
          using gt0 x Suc apply simp 
            using dom' Suc P' unfolding dollar_def sep_conj_def  
            by force 
        \<comment> \<open>... obtain the tail of the While loop from the inner IH\<close>
        then obtain ps3'' m where w: "((WHILE b DO C, ps3') \<Rightarrow>\<^sub>A m \<Down> ps3'')"
                    and m'': "m \<le> (x - (1 + x''))" and P'': "P (ps3'', (x - (1 + x'')) - m)"
                    and dom'': "vars b \<subseteq> dom ps3''" and b'': "\<not> pbval b ps3''" by auto
        
        \<comment> \<open>combine body and tail to one loop unrolling:\<close>
        \<comment> \<open>- the Bigstep Semantic\<close>
        have BigStep: "(WHILE b DO C, ps3) \<Rightarrow>\<^sub>A 1 + x'' + m \<Down> ps3''"
          apply(rule big_step_t_part.WhileTrue)
              apply (fact True) apply (fact dom) apply (fact C) apply (fact w) by simp            
        \<comment> \<open>- the TimeBound\<close> 
        have TimeBound: "1 + x'' + m \<le> x"
          using m'' Suc'' Suc by simp            
        \<comment> \<open>- the invariantPreservation\<close> 
        have invariantPreservation: "P (ps3'', x - (1 + x'' + m))" using P'' m'' by auto 
            
            
        \<comment> \<open>finally combine BigStep Semantic, TimeBound, invariantPreservation\<close>
        show ?thesis
          apply(rule exI[where x="ps3''"])
          apply(rule exI[where x="1 + x'' + m"]) 
            using BigStep TimeBound invariantPreservation dom'' b'' by blast                 
      next
        case False
        from less(2) obtain x' where P: "P (ps3, x')" and dom: "vars b \<subseteq> dom ps3" and Suc: "x = Suc x'" unfolding sep_conj_def
          by force
        show ?thesis 
        apply(rule exI[where x=ps3])
        apply(rule exI[where x="Suc 0"]) apply safe
            apply (rule big_step_t_part.WhileFalse)
        subgoal using dom by simp 
            apply fact
        using Suc apply simp
        using P Suc apply simp
          using dom apply auto
          using False apply auto done    
      qed         
    qed       
  qed
next       
  case (conseq P c Q P' Q')
  then show ?case unfolding hoare3_valid_def by metis
next
  case (normalize P m C Q n)
  then show ?case unfolding hoare3_valid_def
  apply(safe) proof (goal_cases)
    case (1 ps N)
    have Q2: "P (ps, N - (m - n))" apply(rule stardiff) by fact
    have mn: "m - n \<le> N" apply(rule stardiff(2)) by fact 
    have P: "(P \<and>* $ m) (ps, N - (m - n) + m)"  unfolding sep_conj_def dollar_def
      apply(rule exI[where x="(ps,N - (m - n))"]) apply(rule exI[where x="(0,m)"])
      apply(auto simp: sep_disj_prod_def sep_disj_nat_def) by fact
    have " N - (m - n) + m =  N +n" using normalize(2)
      using mn by auto 
        
    from P 1(3) obtain ps' m' where "(C, ps) \<Rightarrow>\<^sub>A m' \<Down> ps'" and m': "m' \<le> N - (m - n) + m" and Q: "(Q \<and>* $ n) (ps', N - (m - n) + m - m')" by blast 
    have Q2: "Q (ps', (N - (m - n) + m - m') - n)" apply(rule stardiff) by fact
    have nm2: "n \<le> (N - (m - n) + m - m')" apply(rule stardiff(2)) by fact
    show ?case
      apply(rule exI[where x="ps'"]) apply(rule exI[where x="m'"])
      apply(safe)
        apply fact 
        using Q2
        using \<open>N - (m - n) + m = N + n\<close> m' nm2 apply linarith
        using Q2 \<open>N - (m - n) + m = N + n\<close> by auto          
    qed
next
  case (constancy P C Q R)
  from constancy(3) show ?case unfolding hoare3_valid_def
 apply safe proof (goal_cases)
    case (1 ps n)
    then obtain ps' m where C: "(C, ps) \<Rightarrow>\<^sub>A m \<Down> ps'" and m: "m \<le> n" and Q: "Q (ps', n - m)" by blast
    from C big_step_t3_same have "ps = ps' on UNIV - lvars C" by auto
    with constancy(2) 1(3) have "R ps'" by auto
        
    show ?case apply(rule exI[where x=ps']) apply(rule exI[where x=m])
      apply(safe)
         apply fact+ done
  qed
next
  case (Assign''' x ds v)
  then show ?case 
    unfolding hoare3_valid_def apply auto 
    subgoal for ps n apply(rule exI[where x="ps(x\<mapsto>v)"])
      apply(rule exI[where x="Suc 0"])
      apply safe 
        apply(rule big_step_t_part.Assign)
        apply (auto) 
         subgoal apply(subst (asm) separate_othogonal_commuted') by(auto simp: dollar_def pointsto_def)
         subgoal apply(subst (asm) separate_othogonal_commuted') by(auto simp: dollar_def pointsto_def)
         subgoal apply(subst (asm) separate_othogonal_commuted') by(auto simp: dollar_def pointsto_def)
         done
       done
         
next
  case (Assign'''' P a v x Q')
  show ?case  
           
  unfolding hoare3_valid_def   apply auto 
    proof (goal_cases)
      case (1 ps n)
      with Assign''''(3)[unfolded hoare3_valid_def] obtain ps' m
        where "(x ::= N v, ps) \<Rightarrow>\<^sub>A m \<Down> ps'" "m \<le> n" "Q' (ps', n - m)" by metis
      from 1(1) Assign''''(1)[unfolded symeval_def] have "paval' a ps = Some v" by auto
      show ?case apply(rule exI[where x=ps']) apply(rule exI[where x=m])
        apply safe
          apply(rule avalDirekt3_correct)
          apply fact+ done  
    qed
next
  case (pureI P Q c R)
  then show ?case unfolding hoare3_valid_def by auto
qed 
  
subsection \<open>Completeness\<close>
    
    
definition wp3 :: "com \<Rightarrow> assn2 \<Rightarrow> assn2" ("wp\<^sub>3") where 
"wp\<^sub>3 c Q  =  (\<lambda>(s,n). \<exists>t m. n\<ge>m \<and> (c,s) \<Rightarrow>\<^sub>A m \<Down> t \<and> Q (t,n-m))" 
    
         
lemma wp3_SKIP[simp]: "wp\<^sub>3 SKIP Q = (Q ** $1)"
  apply (auto intro!: ext simp: wp3_def) 
    unfolding sep_conj_def dollar_def sep_disj_prod_def sep_disj_nat_def apply auto apply force
    subgoal for t n apply(rule exI[where x=t])  apply(rule exI[where x="Suc 0"])
      using big_step_t_part.Skip by auto
    done
 
lemma wp3_Assign[simp]: "wp\<^sub>3 (x ::= e) Q = ((\<lambda>(ps,t). vars e \<union> {x} \<subseteq> dom ps \<and> Q (ps(x \<mapsto> paval e ps),t)) ** $1)"
  apply (auto intro!: ext simp: wp3_def )  
  unfolding sep_conj_def apply (auto simp: sep_disj_prod_def sep_disj_nat_def dollar_def) apply force
    by fastforce
 
lemma wpt_Seq[simp]: "wp\<^sub>3 (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>3 c\<^sub>1 (wp\<^sub>3 c\<^sub>2 Q)"
  apply (auto simp: wp3_def fun_eq_iff ) 
  subgoal for a b t m1 s2 m2  
      apply(rule exI[where x="s2"])
      apply(rule exI[where x="m1"])
        apply simp
      apply(rule exI[where x="t"])
      apply(rule exI[where x="m2"])
      apply simp done
  subgoal for s m t' m1 t m2
      apply(rule exI[where x="t"])
      apply(rule exI[where x="m1+m2"])
    apply (auto simp: big_step_t_part.Seq) done
      done

lemma wp3_If[simp]:
 "wp\<^sub>3 (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = ((\<lambda>(ps,t). vars b \<subseteq> dom ps \<and> wp\<^sub>3 (if pbval b ps then c\<^sub>1 else c\<^sub>2) Q (ps,t)) ** $1)"
  apply (auto simp: wp3_def fun_eq_iff)
  unfolding sep_conj_def apply (auto simp: sep_disj_prod_def sep_disj_nat_def dollar_def)    
  subgoal for a ba t x apply(rule exI[where x="ba - 1"]) apply auto  
    apply(rule exI[where x=t]) apply(rule exI[where x=x]) apply auto done
  subgoal for a ba t x apply(rule exI[where x="ba - 1"]) apply auto 
    apply(rule exI[where x=t]) apply(rule exI[where x=x]) apply auto done
  subgoal for a ba t m
    apply(rule exI[where x=t]) apply(rule exI[where x="Suc m"]) apply auto
    apply(cases "pbval b a")
    subgoal apply simp apply(subst big_step_t_part.IfTrue) using big_step_t3_post_dom_conv by auto 
    subgoal apply simp apply(subst big_step_t_part.IfFalse) using big_step_t3_post_dom_conv by auto  
  done
  done 
         
lemma sFTrue: assumes "pbval b ps" "vars b \<subseteq> dom ps"
  shows "wp\<^sub>3 (WHILE b DO c) Q (ps, n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps, n)"
    (is "?wp = (?I \<and>* $ 1) _")
proof 
  assume "wp\<^sub>3 (WHILE b DO c) Q (ps, n)"
  from this[unfolded wp3_def] obtain ps'' tt where tn: "tt \<le> n" and w1: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A tt \<Down> ps''" and Q: "Q (ps'', n - tt) " by blast      
  with assms obtain t t' ps' where w2: "(WHILE b DO c, ps') \<Rightarrow>\<^sub>A t' \<Down> ps''" and c: "(c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and tt: "tt=1+t+t'" by auto
  
  from tn obtain k where n: "n=tt+k"
    using le_Suc_ex by blast  
      
  from assms show "(?I \<and>* $ 1) (ps,n)"
    unfolding sep_conj_def dollar_def  wp3_def  apply auto
    apply(rule exI[where x="t+t'+k"])
      apply safe subgoal using n tt by auto
      apply(rule exI[where x="ps'"])
    apply(rule exI[where x="t"])
    using c apply auto
      apply(rule exI[where x="ps''"])
    apply(rule exI[where x="t'"])
    using w2 Q n by auto
next
  assume "(?I \<and>* $ 1) (ps,n)"
  with assms have Q: "wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n-1)" and n: "n\<ge>1" unfolding dollar_def sep_conj_def by auto
  then obtain t ps' t' ps'' where t: "t \<le> n - 1"  
        and c: "(c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and  t': "t' \<le> (n-1) - t" and w: "(WHILE b DO c, ps') \<Rightarrow>\<^sub>A t' \<Down> ps''" 
        and Q: "Q (ps'', ((n-1) - t) - t')"
    unfolding wp3_def by auto
      
      
  show "?wp" unfolding wp3_def
    apply simp apply(rule exI[where x="ps''"]) apply(rule exI[where x="1+t+t'"])
    apply safe
    subgoal using t t' n by simp
    subgoal using c w assms by auto
    subgoal using Q t t' n by simp
    done      
qed
  
lemma sFFalse: assumes "~ pbval b ps" "vars b \<subseteq> dom ps"
  shows "wp\<^sub>3 (WHILE b DO c) Q (ps, n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps, n)"
    (is "?wp = (?I \<and>* $ 1) _")
proof 
  assume "wp\<^sub>3 (WHILE b DO c) Q (ps, n)"
  from this[unfolded wp3_def] obtain ps' t where tn: "t \<le> n" and w1: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and Q: "Q (ps', n - t) " by blast      
  from assms have w2: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A 1 \<Down> ps" by auto
  from w1 w2 big_step_t_determ2 have t1: "t=1" and pps: "ps=ps'" by auto
  from assms show "(?I \<and>* $ 1) (ps,n)"
    unfolding sep_conj_def dollar_def using t1 tn Q pps apply auto  apply(rule exI[where x="n-1"]) by auto
next
  assume "(?I \<and>* $ 1) (ps,n)"
  with assms have Q: "Q(ps,n-1)" "n\<ge>1" unfolding dollar_def sep_conj_def by auto
  from assms have w2: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A 1 \<Down> ps" by auto   
  show "?wp" unfolding wp3_def
    apply auto   apply(rule exI[where x=ps]) apply(rule exI[where x=1])
      using Q w2 by auto  
qed
    
lemma sF': "wp\<^sub>3 (WHILE b DO c) Q (ps,n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps,n)"   
  apply(cases "vars b \<subseteq> dom ps")
  subgoal apply(cases "pbval b ps") using sFTrue sFFalse by auto
  subgoal   by (auto simp add: dollar_def wp3_def sep_conj_def) 
      done
    
lemma sF: "wp\<^sub>3 (WHILE b DO c) Q s = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) s"   
 using sF'
  by (metis (mono_tags, lifting) prod.case_eq_if prod.collapse sep_conj_impl1) 
    
lemma assumes "\<And>Q. \<turnstile>\<^sub>3 {wp\<^sub>3 c Q} c {Q}"
  shows WhileWpisPre: "\<turnstile>\<^sub>3 {wp\<^sub>3 (WHILE b DO c) Q} WHILE b DO c { Q}"
proof - 
  define I where  "I \<equiv> (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q) (ps, n) else Q (ps, n)))"
   
  from assms[where Q="(wp\<^sub>3 (WHILE b DO c) Q)"] have 
    c: "\<turnstile>\<^sub>3 {wp\<^sub>3 c (wp\<^sub>3 (WHILE b DO c) Q)} c {(wp\<^sub>3 (WHILE b DO c) Q)}" .
  have c': "\<turnstile>\<^sub>3 { (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b True s) } c { I  ** $1 }"
    apply(rule conseq)             
      apply(rule c)              
    subgoal apply auto unfolding I_def by auto            
    subgoal  unfolding I_def   using sF by auto 
    done
     
  from hoareT3.While[where P="I"] c' have
    w: "\<turnstile>\<^sub>3 { (\<lambda>(s,n). I (s,n) \<and>  vars b \<subseteq> dom s) ** $1 } WHILE b DO c {  \<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b False s }" .
        
  show "\<turnstile>\<^sub>3 {wp\<^sub>3 (WHILE b DO c) Q} WHILE b DO c { Q}"       
      apply(rule conseq)      
      apply(rule w)           
    subgoal using sF I_def
      by (smt Pair_inject R case_prodE case_prodI2)      
    subgoal unfolding I_def by auto
    done
qed
 
  
lemma wp3_is_pre: "\<turnstile>\<^sub>3 {wp\<^sub>3 c Q} c { Q}"
proof (induction c arbitrary: Q)
  case SKIP
  then show ?case apply auto 
    using Frame[where F=Q and Q="$0" and P="$1", OF Skip]
      by (auto simp: sep.add_ac) 
next
  case (Assign x1 x2) 
  then show ?case using Assign4 by simp 
next               
  case (Seq c1 c2)
  then show ?case apply auto
    apply(subst hoareT3.Seq[rotated]) by auto
next
  case (If x1 c1 c2)
  then show ?case apply auto 
    apply(rule weakenpre[OF hoareT3.If, where P1="%(ps,n). wp\<^sub>3 (if pbval x1 ps then c1 else c2) Q (ps,n)"])
      apply auto
    subgoal apply(rule conseq[where P="wp\<^sub>3 c1 Q" and Q=Q]) by auto 
    subgoal apply(rule conseq[where P="wp\<^sub>3 c2 Q" and Q=Q]) by auto 
  proof -
    fix a b
    assume "((\<lambda>(ps, t). vars x1 \<subseteq> dom ps \<and> wp\<^sub>3 (if pbval x1 ps then c1 else c2) Q (ps, t)) \<and>* $ (Suc 0)) (a, b)"
    then show "((\<lambda>(ps, t). wp\<^sub>3 (if pbval x1 ps then c1 else c2) Q (ps, t) \<and> vars x1 \<subseteq> dom ps) \<and>* $ (Suc 0)) (a, b)"
       unfolding sep_conj_def apply auto apply(case_tac "pbval x1 aa") apply auto done (* strange! *)
  qed 
next
  case (While b c)
  with WhileWpisPre show ?case .
qed  
  
  
theorem hoare3_complete: "\<Turnstile>\<^sub>3 {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>3 {P}c{Q}"  
apply(rule conseq[OF wp3_is_pre, where Q'=Q and Q=Q, simplified]) 
  apply(auto simp: hoare3_valid_def wp3_def)
  by fast     
  
  
theorem hoare3_sound_complete: "\<Turnstile>\<^sub>3 {P}c{Q} \<longleftrightarrow> \<turnstile>\<^sub>3 {P}c{Q}"  
 using hoare3_complete hoare3_sound by metis
  
  
subsubsection "What about garbage collection?"
  
definition F where "F C Q = (%(ps,n). \<exists>ps1' ps2' m e1 e2. (C, ps) \<Rightarrow>\<^sub>A m \<Down> ps1' + ps2' \<and>  ps1' ## ps2' \<and> n = e1 + e2 + m \<and> Q (ps1',e1) )"  
  
lemma "wp\<^sub>3 C (Q**(%_.True)) = F C Q" 
  apply rule
  unfolding wp3_def sep_conj_def 
  unfolding F_def apply auto 
  subgoal for a b m aaa ba ab bb apply(rule exI[where x=aaa])
    apply(rule exI[where x=ab])  apply(rule exI[where x=m])
    apply auto apply(rule exI[where x=ba]) apply auto apply(rule exI[where x=bb])
    apply auto
  done    
  subgoal for a ps1' ps2' m e1 e2
    apply(rule exI[where x="ps1'+ps2'"])
    apply(rule exI[where x="m"]) by auto
  done

                
definition hoareT3_validGC :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>G {(1_)}/ (_)/ { (1_)}" 50) where
"\<Turnstile>\<^sub>G { P } c { Q }  \<longleftrightarrow> \<Turnstile>\<^sub>3 { P } c { Q ** (%_.True) }"                                                                                                  
  
end
