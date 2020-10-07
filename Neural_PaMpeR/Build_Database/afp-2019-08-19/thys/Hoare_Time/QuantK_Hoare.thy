section \<open>Quantitative Hoare Logic (big-O style)\<close>

theory QuantK_Hoare
imports Big_StepT Complex_Main "HOL-Library.Extended_Nat"
begin


abbreviation "eq a b == (And (Not (Less a b)) (Not (Less b a)))"
   
type_synonym lvname = string
type_synonym assn = "state \<Rightarrow> bool" (* time bound *)
type_synonym qassn = "state \<Rightarrow> enat" (* time bound *)

text \<open>The support of an assn2\<close>
 
abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

fun emb :: "bool \<Rightarrow> enat" ("\<up>") where
   "emb False = \<infinity>"
 | "emb True = 0"
  
subsection "Definition of Validity"
  
(* this definition refines the normal Hoare Triple Validity *)
definition hoare2o_valid :: "qassn \<Rightarrow> com \<Rightarrow> qassn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>2\<^sub>' {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>2\<^sub>' {P} c {Q}  \<longleftrightarrow>  (\<exists>k>0. (\<forall>s.  P s < \<infinity> \<longrightarrow> (\<exists>t p. ((c,s) \<Rightarrow> p \<Down> t) \<and> enat k * P s \<ge> p + enat k * Q t)))"


subsection "Hoare Rules"

inductive
  hoareQ :: "qassn \<Rightarrow> com \<Rightarrow> qassn \<Rightarrow> bool" ("\<turnstile>\<^sub>2\<^sub>' ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>2\<^sub>' {%s. eSuc (P s)} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>2\<^sub>' {\<lambda>s. eSuc (P (s[a/x]))} x::=a { P }"  |

If: "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {\<lambda>s. P s + \<up>( bval b s)} c\<^sub>1 { Q};
       \<turnstile>\<^sub>2\<^sub>' {\<lambda>s. P s + \<up>(\<not> bval b s)} c\<^sub>2 { Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {\<lambda>s. eSuc (P s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q }"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' { P\<^sub>1 } c\<^sub>1 { P\<^sub>2 }; \<turnstile>\<^sub>2\<^sub>' {P\<^sub>2} c\<^sub>2 { P\<^sub>3 }\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |
 
While:
  "\<lbrakk>   \<turnstile>\<^sub>2\<^sub>' { %s. I s + \<up>(bval b s) } c { %t. I t + 1 }   \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {\<lambda>s. I s + 1 } WHILE b DO c {\<lambda>s.  I s + \<up>(\<not> bval b s)  }" |

conseq:  "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {P}c{Q} ; \<And>s. P s \<le> enat k *  P' s ; \<And>s. enat k * Q' s \<le> Q s; k>0 \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>2\<^sub>' {P'}c{ Q'}" 
  
text \<open>Derived Rules\<close>

lemma const: "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {\<lambda>s. enat k * P s}c{\<lambda>s. enat k * Q s};  k>0 \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>2\<^sub>' {P}c{ Q}" 
  apply(rule conseq) by auto

inductive
  hoareQ' :: "qassn \<Rightarrow> com \<Rightarrow> qassn \<Rightarrow> bool" ("\<turnstile>\<^sub>Z ({(1_)}/ (_)/ {(1_)})" 50)
where

ZSkip:  "\<turnstile>\<^sub>Z {%s. eSuc (P s)} SKIP {P}"  |

ZAssign:  "\<turnstile>\<^sub>Z {\<lambda>s. eSuc (P (s[a/x]))} x::=a { P }"  |

ZIf: "\<lbrakk> \<turnstile>\<^sub>Z {\<lambda>s. P s + \<up>( bval b s)} c\<^sub>1 { Q};
       \<turnstile>\<^sub>Z {\<lambda>s. P s + \<up>(\<not> bval b s)} c\<^sub>2 { Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>Z {\<lambda>s. eSuc (P s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q }"  |

ZSeq: "\<lbrakk> \<turnstile>\<^sub>Z { P\<^sub>1 } c\<^sub>1 { P\<^sub>2 }; \<turnstile>\<^sub>Z {P\<^sub>2} c\<^sub>2 { P\<^sub>3 }\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>Z {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |
 
ZWhile:
  "\<lbrakk>   \<turnstile>\<^sub>Z { %s. I s + \<up>(bval b s) } c { %t. I t + 1 }   \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>Z {\<lambda>s. I s + 1 } WHILE b DO c {\<lambda>s.  I s + \<up>(\<not> bval b s)  }" |

Zconseq': "\<lbrakk> \<turnstile>\<^sub>Z {P}c{Q} ; \<And>s. P s \<le>  P' s ; \<And>s. Q' s \<le> Q s \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>Z {P'}c{ Q'}"   |
   
Zconst:  "\<lbrakk> \<turnstile>\<^sub>Z {\<lambda>s. enat k * P s}c{\<lambda>s. enat k * Q s};  k>0 \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>Z {P}c{ Q}"  
    

lemma Zconseq: "\<lbrakk> \<turnstile>\<^sub>Z {P}c{Q} ; \<And>s. P s \<le> enat k *  P' s ; \<And>s. enat k * Q' s \<le> Q s; k>0 \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>Z {P'}c{ Q'}"
  apply(rule Zconst[of k P' c Q'])
  apply(rule Zconseq'[where P=P and Q=Q]) by auto
    
    
lemma ZQ: " \<turnstile>\<^sub>Z { P } c { Q } \<Longrightarrow>  \<turnstile>\<^sub>2\<^sub>' { P } c { Q }"
  apply(induct rule: hoareQ'.induct) 
    apply (auto simp: hoareQ.Skip  hoareQ.Assign hoareQ.If hoareQ.Seq hoareQ.While) 
    subgoal using conseq[where k=1] using one_enat_def by auto  
    subgoal for k P c Q  using const by auto  
    done
lemma QZ: " \<turnstile>\<^sub>2\<^sub>' { P } c { Q } \<Longrightarrow>  \<turnstile>\<^sub>Z { P } c { Q }"
  apply(induct rule: hoareQ.induct) 
    apply (auto simp: ZSkip  ZAssign ZIf ZSeq ZWhile ) 
    using Zconseq by blast 
      
lemma QZ_iff:  "\<turnstile>\<^sub>2\<^sub>' { P } c { Q } \<longleftrightarrow>  \<turnstile>\<^sub>Z { P } c { Q }"   
using ZQ QZ by metis      

  
subsection "Soundness"

lemma enatSuc0[simp]: "enat (Suc 0) * x = x"
  using one_enat_def by auto 
 
    
theorem hoareQ_sound: "\<turnstile>\<^sub>2\<^sub>' {P}c{ Q}  \<Longrightarrow>  \<Turnstile>\<^sub>2\<^sub>' {P}c{ Q}"
apply(unfold hoare2o_valid_def)
proof(  induction  rule: hoareQ.induct)
  case (Skip P)
  show ?case apply(rule exI[where x=1]) apply(auto)
    subgoal for s apply(rule exI[where x=s]) apply(rule exI[where x="Suc 0"])  
      apply safe 
      apply fast    
      by (metis add.left_neutral add.right_neutral eSuc_enat iadd_Suc le_iff_add zero_enat_def)
    done
next
  case (Assign P a x)
  show ?case apply(rule exI[where x=1])   apply(auto)
    subgoal for s apply(rule exI[where x="s[a/x]"]) apply(rule exI[where x="Suc 0"]) 
      apply safe 
      apply fast
      by (metis add.left_neutral add.right_neutral  eSuc_enat iadd_Suc le_iff_add zero_enat_def)      
    done
next
  case (Seq P1 C1 P2 C2 P3)
  from Seq(3) obtain k1 where Seq3: "\<forall>s. P1 s < \<infinity> \<longrightarrow> (\<exists>t p. (C1, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k1 * P2 t \<le> enat k1 * P1 s)" and 10: "k1>0" by blast
  from Seq(4) obtain k2 where Seq4: "\<forall>s. P2 s < \<infinity> \<longrightarrow> (\<exists>t p. (C2, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k2 * P3 t \<le> enat k2 * P2 s)" and 20: "k2>0" by blast
  let ?k = "lcm k1 k2" (* or k1*k2 *)
  show ?case apply(rule exI[where x="?k"])
  proof (safe)
    from 10 20 show "lcm k1 k2>0" by (auto simp: lcm_pos_nat)
    fix s
    assume ninfP1: "P1 s < \<infinity>"
    with Seq3 obtain t1 p1 where 1: "(C1, s) \<Rightarrow> p1 \<Down> t1" and q1: "enat p1 + k1 * P2 t1 \<le> k1 * P1 s" by blast
    with ninfP1 have ninfP2: "P2 t1 < \<infinity>"
      using not_le 10 by fastforce 
    with Seq4 obtain t2 p2 where 2: "(C2, t1) \<Rightarrow> p2 \<Down> t2" and q2: "enat p2 + k2 * P3 t2 \<le> k2 * P2 t1" by blast
    with ninfP2 have ninfP3: "P3 t2 < \<infinity>"
      using not_le 20  by fastforce 
    then obtain u2 where u2: "P3 t2 = enat u2" by auto
    from ninfP2 obtain u1 where u1: "P2 t1 = enat u1" by auto
    from ninfP1 obtain u0 where u0: "P1 s = enat u0" by auto
    
    from Big_StepT.Seq[OF 1 2] have 12: "(C1;; C2, s) \<Rightarrow> p1 + p2 \<Down> t2" by simp
    
    have i: "(C1;; C2, s) \<Rightarrow> p1+p2 \<Down> t2" using 1 and 2 by auto
    
    from 10 20 have p: "k1 div gcd k1 k2 > 0" "k2 div gcd k1 k2 > 0" by (simp_all add: Divides.div_positive)
        
    have za: "?k = (k1 div gcd k1 k2) * k2" 
      apply(simp only: lcm_nat_def)
      by (simp add: dvd_div_mult)
        
    have za2: "?k = (k2 div gcd k1 k2) * k1" 
      apply(simp only: lcm_nat_def)
      by (metis dvd_div_mult gcd_dvd2 mult.commute)
        
    from q1[unfolded u1 u2 u0] have z: "p1 + k1 * u1 \<le> k1 * u0" by auto
    from q2[unfolded u1 u2 u0] have y: "  p2 + k2 *   u2 \<le> k2 *   u1" by auto
    have "p1+p2 + ?k * u2 \<le> p1 + (k1 div gcd k1 k2)*p2  + ?k * u2  " using p by simp
    also have "\<dots> \<le> (k2 div gcd k1 k2)*p1 + (k1 div gcd k1 k2)*p2  + ?k * u2  " using p by simp                                      
    also have "\<dots> = (k2 div gcd k1 k2)*p1 + (k1 div gcd k1 k2)*(p2 + k2* u2)"
      apply(simp only: za) by algebra  
    also have "\<dots> \<le> (k2 div gcd k1 k2)*p1 + (k1 div gcd k1 k2)*(k2 *   u1)" using y
      by (metis add_left_mono distrib_left le_iff_add)   
    also have "\<dots> = (k2 div gcd k1 k2)*p1 + ?k * u1" by(simp only: za)
    also have "\<dots> = (k2 div gcd k1 k2)*p1 + (k2 div gcd k1 k2) *(k1* u1)" by(simp only: za2)
    also have "\<dots> \<le> (k2 div gcd k1 k2)*(p1 + k1*u1)"
      by (simp add: distrib_left)
    also have "\<dots> \<le> (k2 div gcd k1 k2)*(k1 * u0)" using z  
      by fastforce
    also have "\<dots> \<le> ?k * u0" by(simp only: za2)
    finally   
    have "p1+p2 + ?k * u2 \<le> ?k * u0" .
    then have ii: "enat (p1+p2) + ?k * P3 t2 \<le> ?k * P1 s" 
      unfolding u0 u2  by auto
        
    from i ii show "\<exists>t p. (C1;; C2, s) \<Rightarrow> p \<Down> t \<and> enat p + ?k * P3 t \<le> ?k * P1 s " by blast 
  qed  
next
  case (If P b c1 Q c2)
  from If(3) obtain kT where If3: "\<forall>s. P s + \<up> (bval b s) < \<infinity> \<longrightarrow> (\<exists>t p. (c1, s) \<Rightarrow> p \<Down> t \<and> enat p + enat kT * Q t \<le> enat kT * (P s + \<up> (bval b s))) " and T: "kT > 0" by blast
  from If(4) obtain kF where If4: "\<forall>s. P s + \<up> (\<not> bval b s) < \<infinity> \<longrightarrow> (\<exists>t p. (c2, s) \<Rightarrow> p \<Down> t \<and> enat p + enat kF * Q t \<le> enat kF * (P s + \<up> (\<not> bval b s)))" and F: "kF > 0" by blast
  show ?case apply(rule exI[where x="kT*kF"])
  proof (safe)
    from T F show "0 < kT * kF" by auto
    fix s
    assume "eSuc (P s) < \<infinity>"
    then have i: "P s < \<infinity>"
      using enat_ord_simps(4) by fastforce  
    then obtain u0 where u0: "P s = enat u0" by auto
    show "\<exists>t p. (IF b THEN c1 ELSE c2, s) \<Rightarrow> p \<Down> t \<and> enat p + enat (kT * kF) * Q t \<le> enat (kT * kF) * eSuc (P s)"
    proof(cases "bval b s")
      case True
      with i have "P s + emb (bval b s) < \<infinity>" by simp
      with If3 obtain p t where 1: "(c1, s) \<Rightarrow> p \<Down> t" and q: "enat p + enat kT * Q t \<le> enat kT * (P s + emb (bval b s))"  by blast
      from Big_StepT.IfTrue[OF True 1] have 2: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p + 1 \<Down> t" by simp
           
      from q have "Q t < \<infinity>" using i T True
        using less_irrefl by fastforce
      then obtain u1 where u1: "Q t = enat u1" by auto 
      from q True have q': "p + kT * u1 \<le> kT * u0" unfolding u0 u1 by auto
      have "(p+1) +  (kT * kF) * u1 \<le> kF*(p+1) + (kT * kF) * u1" using F 
        by (simp add: mult_eq_if)
      also have "\<dots> \<le> kF*(p+1  + kT  * u1)"
        by (simp add: add_mult_distrib2)  
      also have "\<dots> \<le> kF*(1  + kT  * u0)"
        using q' by auto
      also have "\<dots> \<le> (kT * kF) * Suc u0" using T by simp
      finally 
      have " (p+1) +  (kT * kF) * u1 \<le>  (kT * kF) * Suc u0" .
      then have 1: "enat (p+1) + enat (kT * kF) * Q t \<le> enat (kT * kF) * eSuc (P s)"
        unfolding u1 u0 by (simp add: eSuc_enat) 
      from 1 2 show ?thesis by metis 
    next
      case False
      with i have "P s + emb (~bval b s) < \<infinity>" by simp
      with If4 obtain p t where 1: "(c2, s) \<Rightarrow> p \<Down> t" and q: "enat p + enat kF * Q t \<le> enat kF * (P s + emb (~bval b s))"  by blast
      from Big_StepT.IfFalse[OF False 1] have 2: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p + 1 \<Down> t" by simp
           
      from q have "Q t < \<infinity>" using i F False
        using less_irrefl by fastforce
      then obtain u1 where u1: "Q t = enat u1" by auto 
      from q False have q': "p + kF * u1 \<le> kF * u0" unfolding u0 u1 by auto
      have "(p+1) +  (kF * kT) * u1 \<le> kT*(p+1) + (kF * kT) * u1" using T 
        by (simp add: mult_eq_if)
      also have "\<dots> \<le> kT*(p+1  + kF  * u1)"
        by (simp add: add_mult_distrib2)  
      also have "\<dots> \<le> kT*(1  + kF  * u0)"
        using q' by auto
      also have "\<dots> \<le> (kF * kT) * Suc u0" using F by simp
      finally 
      have " (p+1) +  (kT * kF) * u1 \<le>  (kT * kF) * Suc u0"
        by (simp add: mult.commute) 
      then have 1: "enat (p+1) + enat (kT * kF) * Q t \<le> enat (kT * kF) * eSuc (P s)"
        unfolding u1 u0 by (simp add: eSuc_enat) 
      from 1 2 show ?thesis by metis 
    qed
  qed
next
  case (conseq P c Q k1 P' Q') 
  from conseq(5) obtain k where c4: "\<forall>s. P s < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * Q t \<le> enat k * P s)" and 0: "k>0" by blast
  show ?case apply(rule exI[where x="k*k1"])
  proof (safe)
    show "k*k1>0" using 0 conseq(4) by auto
    fix s
    assume "P' s < \<infinity>"
    with conseq(2,4)  have "P s < \<infinity>"
      using le_less_trans
      by (metis enat.distinct(2) enat_ord_simps(4) imult_is_infinity)  
    with c4 obtain p t where 1: "(c, s) \<Rightarrow> p \<Down> t" and 2: "enat p + enat k * Q t \<le> enat k * P s" by blast   
               
    have "enat p + enat (k*k1) * Q' t = enat p + enat (k) * ( (enat k1) * Q' t)"
      by (metis mult.assoc times_enat_simps(1))       
    also have "\<dots> \<le> enat p + enat (k) * Q t" using conseq(3)
      by (metis add_left_mono distrib_left le_iff_add)  
    also have "\<dots> \<le> enat k * P s" using 2 by auto
    also have "\<dots> \<le> enat (k*k1)  * P' s" using conseq(2)
      by (metis mult.assoc mult_left_mono not_less not_less_zero times_enat_simps(1))
    finally have 2: "enat p + enat (k*k1) * Q' t \<le> enat (k*k1) * P' s"
      by auto
    from 1 2 show "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + (k*k1) * Q' t \<le> (k*k1) * P' s" by auto
  qed
next
  case (While INV b c)  
  then obtain k where W2: "\<forall>s. INV s + \<up> (bval b s) < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * (INV t + 1) \<le> enat k * (INV s + \<up> (bval b s)))" and g0: "k>0"
    by blast
  show ?case apply(rule exI[where x=k])
  proof (safe)
    show "0<k" by fact
    fix s
    assume ninfINV: "INV s + 1 < \<infinity>" 
    then have f: "INV s < \<infinity>"
      using enat_ord_simps(4) by fastforce 
    then obtain n where i: "INV s = enat n" using not_infinity_eq
      by auto      
    
    have "INV s = enat n \<Longrightarrow> \<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * (INV t + emb (\<not> bval b t)) \<le> enat k * (INV s + 1)"
    proof (induct n arbitrary: s rule: less_induct)
      case (less n) 
      
      then show ?case 
      proof (cases "bval b s")
        case False
        show ?thesis
            apply(rule exI[where x="s"])
          apply(rule exI[where x="Suc 0"])
          apply safe
           apply (fact WhileFalse[OF False])
          using False 
          apply (simp add: one_enat_def) using g0
          by (metis One_nat_def Suc_ile_eq add.commute add_left_mono distrib_left enat_0_iff(2) mult.right_neutral not_gr_zero one_enat_def)    
      next
        case True
        with less(2) W2 have "(\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * (INV t + 1) \<le> enat k * INV s )"
          by force  
        then obtain t p where o: "(c, s) \<Rightarrow> p \<Down> t" and q: "enat p + enat k * (INV t + 1) \<le> enat k * INV s " by auto
        from o bigstep_progress have p: "p > 0" by blast
             
            
        from q  have pf: "enat k * (INV t + 1) \<le> enat k * INV s"
          using dual_order.trans by fastforce
        then have "INV t < \<infinity>" using less(2) 
          using g0 not_le by fastforce 
        then obtain invt where invt: "INV t = enat invt" by auto
        from pf g0 have g: "INV t  < INV s"
          unfolding less(2) invt
          by (metis (full_types) Suc_ile_eq add.commute eSuc_enat enat_ord_simps(1) nat_mult_le_cancel_disj plus_1_eSuc(1) times_enat_simps(1))
              
              
        then have ninfINVt: "INV t < \<infinity>" using less(2)
          using enat_ord_simps(4) by fastforce 
        then obtain n' where i: "INV t = enat n'" using not_infinity_eq
          by auto 
        with less(2) have ii: "n' < n"
          using g by auto
        from i ii less(1) obtain t2 p2 where o2: "(WHILE b DO c, t) \<Rightarrow> p2 \<Down> t2" and q2: "enat p2 + enat k * (INV t2 + emb (\<not> bval b t2)) \<le> enat k * ( INV t + 1)" by blast
        have ende: "~ bval b t2"
          apply(rule ccontr) apply(simp) using q2 g0 ninfINVt
          by (simp add: i one_enat_def) 
        from WhileTrue[OF True o o2] have "(WHILE b DO c, s) \<Rightarrow> 1 + p + p2 \<Down> t2" by simp
       
        from ende q2 have q2': "enat p2 + enat k * INV t2 \<le> enat k * (INV t + 1)" by simp
        
        show ?thesis 
          apply(rule exI[where x=t2])
          apply(rule exI[where x= "1 + p + p2"])
          apply(safe)
           apply(fact)
          using ende apply(simp)
        proof -
          have "enat (Suc (p + p2)) +  enat k * INV t2 = enat (Suc p) + enat p2 +  enat k * INV t2" by fastforce
          also have "\<dots> \<le> enat (Suc p) + enat k * (INV t + 1)" using q2'
            by (metis ab_semigroup_add_class.add_ac(1) add_left_mono) 
          also have "\<dots> \<le> 1 + enat k * (INV s)" using q
            by (metis (no_types, hide_lams) add.commute add_left_mono eSuc_enat iadd_Suc plus_1_eSuc(1))
          also have "\<dots> \<le> enat k + enat k * (INV s)" using g0
            by (simp add: Suc_leI one_enat_def) 
          also have "\<dots> \<le>  enat k * (INV s + 1)"
            by (simp add: add.commute distrib_left)
          finally show "enat (Suc (p + p2)) +  enat k * INV t2 \<le>  enat k * (INV s + 1)" .
          qed
        qed 
      qed
        
    from this[OF i] show "\<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * (INV t + emb (\<not> bval b t)) \<le> enat k * (INV s + 1)" .
        
  qed
qed 

  
lemma conseq':
  "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {P} c {Q} ;  \<forall>s. P s \<le> P' s; \<forall>s. Q' s \<le> Q s  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P'} c {Q'}"
  apply(rule conseq[where k=1]) by auto

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P s \<le> P' s;  \<turnstile>\<^sub>2\<^sub>' {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P'} c {Q}"
  apply(rule conseq[where k=1 and Q'=Q and Q=Q]) by auto

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {P} c {Q};  \<forall>s. Q s \<ge> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>2\<^sub>' {P} c {Q'}"
  apply(rule conseq[where k=1]) by auto 

lemma Assign': "\<forall>s. P s \<ge> eSuc ( Q(s[a/x])) \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P} x ::= a {Q}" 
by (simp add: strengthen_pre[OF _ Assign])

  
subsection "Completeness"
    
lemma bigstep_det: "(c1, s) \<Rightarrow> p1 \<Down> t1 \<Longrightarrow> (c1, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp

lemma bigstepT_the_cost: "(c, s) \<Rightarrow> P \<Down> T \<Longrightarrow> (THE n. \<exists>a. (c, s) \<Rightarrow> n \<Down> a) = P"
  using bigstep_det by blast 

lemma bigstepT_the_state: "(c, s) \<Rightarrow> P \<Down> T \<Longrightarrow> (THE a. \<exists>n. (c, s) \<Rightarrow> n \<Down> a) = T"
  using bigstep_det by blast 


lemma SKIPnot: "(\<not> (SKIP, s) \<Rightarrow> p \<Down> t) = (s\<noteq>t \<or> p\<noteq>Suc 0)" by blast

 
lemma SKIPp: "(THE p. \<exists>t. (SKIP, s) \<Rightarrow> p \<Down> t) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma SKIPt: "(THE t. \<exists>p. (SKIP, s) \<Rightarrow> p \<Down> t) = s"
  apply(rule the_equality)
  apply fast
  apply auto done 


lemma ASSp: "(THE p. Ex (big_step_t (x ::= e, s) p)) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSt: "(THE t. \<exists>p. (x ::= e, s) \<Rightarrow> p \<Down> t) = s(x := aval e s)"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSnot: "( \<not> (x ::= e, s) \<Rightarrow> p \<Down> t ) = (p\<noteq>Suc 0 \<or> t\<noteq>s(x := aval e s))"
  apply auto done

text\<open>
The completeness proof proceeds along the same lines as the one for partial
correctness. First we have to strengthen our notion of weakest precondition
to take termination into account:\<close>

definition wpQ :: "com \<Rightarrow> qassn \<Rightarrow> qassn" ("wp\<^sub>Q") where
"wp\<^sub>Q c Q  =  (\<lambda>s. (if (\<exists>t p. (c,s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>)  then enat (THE p. \<exists>t. (c,s) \<Rightarrow> p \<Down> t) + Q (THE t. \<exists>p. (c,s) \<Rightarrow> p \<Down> t) else \<infinity>))"
  
lemma wpQ_skip[simp]: "wp\<^sub>Q SKIP Q = (%s. eSuc (Q s))"
  apply(auto intro!: ext simp: wpQ_def)
   prefer 2
   apply(simp only: SKIPnot)
   apply(simp)  
  apply(simp only: SKIPp SKIPt)
  using one_enat_def plus_1_eSuc(1) by auto    

lemma wpQ_ass[simp]: "wp\<^sub>Q (x ::= e) Q = (\<lambda>s. eSuc (Q (s(x := aval e s))))"
by (auto intro!: ext simp: wpQ_def ASSp ASSt ASSnot eSuc_enat) 

lemma wpt_Seq[simp]: "wp\<^sub>Q (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>Q c\<^sub>1 (wp\<^sub>Q c\<^sub>2 Q)"
unfolding wpQ_def
proof (rule, case_tac "\<exists>t p. (c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>", goal_cases)
  case (1 s)
  then obtain u p where ter: "(c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> p \<Down> u" and Q: "Q u < \<infinity>" by blast
  then obtain t p1 p2 where i: "(c\<^sub>1 , s) \<Rightarrow> p1 \<Down> t" and ii: "(c\<^sub>2 , t) \<Rightarrow> p2 \<Down> u" and p: "p1 + p2 = p" by blast

  from bigstepT_the_state[OF i] have t: "(THE t. \<exists>p. (c\<^sub>1, s) \<Rightarrow> p \<Down> t) = t"  
    by blast
  from bigstepT_the_state[OF ii] have t2: "(THE u. \<exists>p. (c\<^sub>2, t) \<Rightarrow> p \<Down> u) = u"  
    by blast
  from bigstepT_the_cost[OF i] have firstcost: "(THE p. \<exists>t. (c\<^sub>1, s) \<Rightarrow> p \<Down> t) = p1"  
    by blast
  from bigstepT_the_cost[OF ii] have secondcost: "(THE p. \<exists>u. (c\<^sub>2, t) \<Rightarrow> p \<Down> u) = p2"  
    by blast
  
  have totalcost: "(THE p. Ex (big_step_t (c\<^sub>1;; c\<^sub>2, s) p)) = p1 + p2"
    using bigstepT_the_cost[OF ter] p by auto
  have totalstate: "(THE t. \<exists>p. (c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> p \<Down> t) = u"
    using bigstepT_the_state[OF ter] by auto
  
  have c2: "\<exists>ta p. (c\<^sub>2, t) \<Rightarrow> p \<Down> ta \<and> Q ta < \<infinity>"
    apply(rule exI[where x= u])
    apply(rule exI[where x= p2]) apply safe apply fact+ done
  
  
  have C: "\<exists>t p. (c\<^sub>1, s) \<Rightarrow> p \<Down> t \<and> (if \<exists>ta p. (c\<^sub>2, t) \<Rightarrow> p \<Down> ta \<and> Q ta < \<infinity> then enat (THE p. Ex (big_step_t (c\<^sub>2, t) p)) + Q (THE ta. \<exists>p. (c\<^sub>2, t) \<Rightarrow> p \<Down> ta) else \<infinity>) < \<infinity>"
    apply(rule exI[where x=t])
    apply(rule exI[where x=p1])
    apply safe
     apply fact
    apply(simp only: c2 if_True)
    using Q bigstepT_the_state ii by auto
   
  show ?case
    apply(simp only: 1 if_True t t2 c2 C totalcost totalstate firstcost secondcost) by fastforce
next
  case (2 s)
  show ?case apply(simp only: 2 if_False)
    apply auto using 2  
    by force 
qed
   

lemma wpQ_If[simp]:
 "wp\<^sub>Q (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. eSuc (wp\<^sub>Q (if bval b s then c\<^sub>1 else c\<^sub>2) Q s))"
  apply (auto simp: wpQ_def fun_eq_iff)
  subgoal for x t p i ta ia xa apply(simp only: IfTrue[THEN bigstepT_the_state])
    apply(simp only: IfTrue[THEN bigstepT_the_cost])
    apply(simp only: bigstepT_the_cost bigstepT_the_state)
    by (simp add: eSuc_enat)            
    apply(simp only: bigstepT_the_state bigstepT_the_cost) apply force
   apply(simp only: bigstepT_the_state bigstepT_the_cost)
proof(goal_cases)
  case (1 x t p i ta ia xa)
  note f= IfFalse[THEN bigstepT_the_state, of b x c\<^sub>2 xa ta "Suc xa" c\<^sub>1, simplified, OF 1(4) 1(5)]
  note f2= IfFalse[THEN bigstepT_the_cost, of b x c\<^sub>2 xa ta "Suc xa" c\<^sub>1, simplified, OF 1(4) 1(5)]
  note g= bigstep_det[OF 1(1) 1(5)]
  show ?case
    apply(simp only: f f2) using 1 g
    by (simp add: eSuc_enat)   
next
  case 2
  then 
  show ?case
    apply(simp only: bigstepT_the_state bigstepT_the_cost)  apply force done
qed
  
lemma hoareQ_inf: "\<turnstile>\<^sub>2\<^sub>' {%s. \<infinity>} c { Q}"
  apply (induction c arbitrary: Q)
  apply(auto intro: hoareQ.Skip hoareQ.Assign hoareQ.Seq hoareQ.conseq)
  subgoal apply(rule hoareQ.conseq) apply(rule hoareQ.If[where P="%s. \<infinity>"]) by(auto intro: hoareQ.If hoareQ.conseq)
  subgoal apply(rule hoareQ.conseq) apply(rule hoareQ.While[where I="%s. \<infinity>"]) apply(rule hoareQ.conseq) by auto 
  done

lemma assumes b: "bval b s"
  shows wpQ_WhileTrue: " wp\<^sub>Q c (wp\<^sub>Q (WHILE b DO c) Q) s  + 1 \<le> wp\<^sub>Q (WHILE b DO c) Q s"
proof (cases "\<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>")
  case True
  then obtain t p where w: "(WHILE b DO c, s) \<Rightarrow> p \<Down> t" and q: "Q t < \<infinity>" by blast
  from b w obtain p1 p2 t1 where c: "(c, s) \<Rightarrow> p1 \<Down> t1" and w': "(WHILE b DO c, t1) \<Rightarrow> p2 \<Down> t" and sum: "1 + p1 + p2 = p"
    by auto 
  have g: "\<exists>ta p. (WHILE b DO c, t1) \<Rightarrow> p \<Down> ta \<and> Q ta < \<infinity>"
    apply(rule exI[where x="t"])
    apply(rule exI[where x="p2"])
      apply safe apply fact+ done
    
  have h: "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> (if \<exists>ta p. (WHILE b DO c, t) \<Rightarrow> p \<Down> ta \<and> Q ta < \<infinity> then enat (THE p. Ex (big_step_t (WHILE b DO c, t) p)) + Q (THE ta. \<exists>p. (WHILE b DO c, t) \<Rightarrow> p \<Down> ta) else \<infinity>) < \<infinity>"
    apply(rule exI[where x="t1"])
    apply(rule exI[where x="p1"])
    apply safe apply fact
    apply(simp only: g if_True) using   bigstepT_the_state bigstepT_the_cost w' q by(auto)
  
  have "wp\<^sub>Q c (wp\<^sub>Q (WHILE b DO c) Q) s + 1 = enat p + Q t"
    unfolding wpQ_def apply(simp only: h if_True)
    apply(simp only: bigstepT_the_state[OF c] bigstepT_the_cost[OF c] g if_True bigstepT_the_state[OF w'] bigstepT_the_cost[OF w']) using sum
    by (metis One_nat_def ab_semigroup_add_class.add_ac(1) add.commute add.right_neutral eSuc_enat plus_1_eSuc(2) plus_enat_simps(1)) 
  also have "\<dots> = wp\<^sub>Q (WHILE b DO c) Q s"
    unfolding wpQ_def apply(simp only: True if_True)
    using bigstepT_the_state bigstepT_the_cost w apply(simp) done
  finally show ?thesis by simp
next
  case False
  have "wp\<^sub>Q (WHILE b DO c) Q s = \<infinity>"
    unfolding wpQ_def 
    apply(simp only: False if_False) done
  then show ?thesis by auto
qed

lemma assumes b: "~ bval b s"
  shows wpQ_WhileFalse: " Q s  + 1 \<le> wp\<^sub>Q (WHILE b DO c) Q s"
proof (cases "\<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>")
  case True
  with b obtain t p where w: "(WHILE b DO c, s) \<Rightarrow> p \<Down> t" and "Q t < \<infinity>" by blast
  with b have c: "s=t" "p=Suc 0" by auto
  have " wp\<^sub>Q (WHILE b DO c) Q s =  Q s  + 1"
    unfolding wpQ_def apply(simp only: True if_True)
    using w c bigstepT_the_cost bigstepT_the_state by(auto simp add: one_enat_def)  
  then show ?thesis by auto
next
  case False
  have "wp\<^sub>Q (WHILE b DO c) Q s = \<infinity>"
    unfolding wpQ_def 
    apply(simp only: False if_False) done
  then show ?thesis by auto
qed 
                            

lemma wpQ_is_pre: "\<turnstile>\<^sub>2\<^sub>' {wp\<^sub>Q c Q} c { Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case apply (auto intro: hoareQ.Skip) done
next
  case Assign show ?case apply (auto intro:hoareQ.Assign) done
next
  case Seq thus ?case by (auto intro:hoareQ.Seq)
next 
  case (If x1 c1 c2 Q) thus ?case
    apply (auto intro!: hoareQ.If )  
     apply(rule hoareQ.conseq) 
       apply(auto)
     apply(rule hoareQ.conseq) 
      apply(auto)
    done
next
  case (While b c)   
  show ?case
      apply(rule conseq[where k=1])   
      apply(rule hoareQ.While[where I="%s. (if bval b s then  wp\<^sub>Q c (wp\<^sub>Q (WHILE b DO c) Q) s else Q s)"])
      apply(rule conseq[where k=1])  
        apply(rule While[of "wp\<^sub>Q (WHILE b DO c) Q"])
       apply(case_tac "bval b s")  
        apply(simp) apply(simp)
      subgoal for s
        apply(cases "bval b s")
        using wpQ_WhileTrue apply simp
        using wpQ_WhileFalse apply simp done
        apply simp
      subgoal for s
        apply(cases "bval b s")
        using wpQ_WhileTrue apply simp
        using wpQ_WhileFalse apply simp done 
       apply(case_tac "bval b s")  
        apply(simp) apply(simp)
        apply simp done  
qed
  
  
lemma wpQ_is_pre': "\<turnstile>\<^sub>2\<^sub>' {wp\<^sub>Q c (%s. enat k * Q s )} c {(%s. enat k * Q s )}"  
  using wpQ_is_pre by blast 
    
lemma wpQ_is_weakestprePotential1: "\<Turnstile>\<^sub>2\<^sub>' {P}c{Q} \<Longrightarrow> (\<exists>k>0. \<forall>s. wp\<^sub>Q c (%s. enat k* Q s) s \<le> enat k * P s)" 
apply(auto simp: hoare2o_valid_def wpQ_def)
proof (goal_cases)
  case (1 k) 
  show ?case 
  proof (rule exI[where x=k], safe)
    show "0<k" by fact
  next
    fix s t p i
    assume "(c, s) \<Rightarrow> p \<Down> t" "enat k * Q t = enat i"
    
    show "enat (\<down>\<^sub>t (c, s)) + enat k * Q (\<down>\<^sub>s (c, s)) \<le> enat k * P s"
    proof (cases "P s < \<infinity>") 
      case True
      with 1 obtain t p' where i: "(c, s) \<Rightarrow> p' \<Down> t" and ii: "enat p' + enat k *  Q t \<le> enat k * P s"
        by auto    
      show ?thesis by(simp add: bigstepT_the_state[OF i] bigstepT_the_cost[OF i] ii)
    next
      case False
      then show ?thesis
        using 1 by auto 
    qed  
  next
    fix s
    assume "\<forall>t. (\<forall>p. \<not> (c, s) \<Rightarrow> p \<Down> t) \<or> enat k * Q t = \<infinity>"
    then show "enat k * P s = \<infinity>" using 1 by force
  qed
qed   

theorem hoareQ_complete: "\<Turnstile>\<^sub>2\<^sub>' {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P}c{ Q}" 
proof -
  assume "\<Turnstile>\<^sub>2\<^sub>' {P}c{Q}"
  with wpQ_is_weakestprePotential1 obtain k where "k>0" 
    and 1: "\<And>s. wp\<^sub>Q c (\<lambda>s. enat k * Q s) s \<le> enat k * P s" by blast
  show "\<turnstile>\<^sub>2\<^sub>' {P}c{Q}"
    apply(rule conseq[OF wpQ_is_pre'])
    apply(fact 1)
     apply simp by fact
qed
    
theorem hoareQ_complete': "\<Turnstile>\<^sub>2\<^sub>' {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {P}c{ Q}"  
  unfolding hoare2o_valid_def
proof -
  assume "\<exists>k>0. \<forall>s. P s < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * Q t \<le> enat k * P s)"
  then obtain k where f: "\<forall>s. P s < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * Q t \<le> enat k * P s)" and k: "k>0" by auto
  
  show "\<turnstile>\<^sub>2\<^sub>' {P}c{ Q}"
    apply(rule conseq[OF wpQ_is_pre', where Q'=Q, simplified, where k1=k and k=k and Q1=Q])
    unfolding  wpQ_def
    subgoal for s
      proof(cases "P s < \<infinity>") 
        case True
        with f obtain t p' where i: "(c, s) \<Rightarrow> p' \<Down> t" and ii: "enat p' + enat k * Q t \<le> enat k * P s"
          by auto    
        from ii k True have iii: "enat k * Q t < \<infinity>"
          using imult_is_infinity by fastforce 
        have kla: "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat k * Q t < \<infinity>"
          using iii i by auto
        show ?thesis unfolding bigstepT_the_state[OF i]
            unfolding bigstepT_the_cost[OF i] 
            apply(simp only: kla) using ii by simp
      next
        case False
        then show ?thesis using k by auto
      qed   
    subgoal by auto 
    using k by auto  
qed 

corollary hoareQ_sound_complete: " \<turnstile>\<^sub>2\<^sub>' {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>2\<^sub>' {P}c{ Q}"
  by (metis hoareQ_sound hoareQ_complete)
  
subsection "Example"
 
lemma fixes X::int assumes "0 < X" shows  
 Z: "eSuc (enat (nat (2 * X) * nat (2 * X))) \<le> enat (5 * (nat (X * X)))"
proof -
  from assms have nn: "0 \<le> X" by auto
  from assms have "0 < nat X" by auto 
  then have "0 < enat (nat X)" by (simp add: zero_enat_def)  
  then have A: "eSuc 0 \<le> enat (nat X)" using ileI1
    by blast
      
  have " (nat X) \<le>  (nat (X*X))"  using nn nat_mult_distrib  by auto
  then have D: "enat (nat X) \<le> enat (nat (X*X))"    by auto
      
  have C: "(enat (nat (2 * X) * nat (2 * X))) = 4* enat (nat (X * X))"   
    using nn nat_mult_distrib
    by (simp add: numeral_eq_enat)    
  have "eSuc (enat (nat (2 * X) * nat (2 * X)))
    = eSuc 0 +  (enat (nat (2 * X) * nat (2 * X)))"
    using one_eSuc plus_1_eSuc(1) by auto
  also have "\<dots> \<le> enat (nat X) +  (enat (nat (2 * X) * nat (2 * X)))"
    using A  add_right_mono by blast  
  also have "\<dots> \<le> enat (nat X) + 4* enat (nat (X * X))" using C by auto
  also have "\<dots> \<le> enat (nat (X * X)) + 4* enat (nat (X * X))" using D by auto
  also have "\<dots> = 5* enat (nat (X * X))"
    by (metis eSuc_numeral mult_eSuc semiring_norm(5)) 
  also have "\<dots> =  enat ( 5* nat (X * X))"
    by (simp add: numeral_eq_enat) 
  finally 
  show ?thesis .
qed
          
     
 
lemma weakenpre: "\<lbrakk> \<turnstile>\<^sub>2\<^sub>' {P}c{Q} ;   (\<forall>s. P s \<le>  P' s)  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>2\<^sub>' {P'}c{ Q}"  using conseq[where Q'=Q and k=1]  
  by auto  

lemma whileDecr: "\<turnstile>\<^sub>2\<^sub>' { %s. enat (nat (s ''x'')) + 1} WHILE (Less (N 0) (V ''x'')) DO (SKIP;; SKIP;; ''x'' ::= Plus (V ''x'') (N (-1))) { %s. enat 0}" 
  apply(rule conseq[where k=4])
     apply(rule While[where I="%s. enat 4 * (enat (nat (s ''x'')))"])
     prefer 2
  subgoal for s apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1)) by presburger
      apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (''x'' ::= Plus (V ''x'') (N (-1))) (\<lambda>t. enat 4 * enat (nat (t ''x'')) + 1)"])
      apply(simp)
     apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (SKIP) (\<lambda>s. eSuc (enat (4 * nat (s ''x'' - 1)) + 1))"])
      apply simp
  subgoal apply(rule weakenpre) apply(rule Skip) apply auto
    subgoal for s apply(cases "s ''x'' > 0") apply auto
      apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1) eSuc_enat) done
    done
  subgoal apply simp   apply(rule Skip) done
  subgoal apply simp apply(rule weakenpre) apply(rule Assign) by simp
     apply simp 
  subgoal for s apply(cases "s ''x'' > 0") by auto
  by simp
    
    
lemma whileDecrIf: "\<turnstile>\<^sub>2\<^sub>' { %s. enat (nat (s ''x'')) + 1} WHILE (Less (N 0) (V ''x'')) DO ( (IF Less (N 0) (V ''z'') THEN SKIP;; SKIP ELSE SKIP );; ''x'' ::= Plus (V ''x'') (N (-1))) { %s. enat 0}"
  apply(rule conseq[OF While, where k=6 and I1="%s. enat 6 * (enat (nat (s ''x'')))"])  
     prefer 2
  subgoal for s apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1)) by presburger
      apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (''x'' ::= Plus (V ''x'') (N (-1))) (\<lambda>t. enat 6 * enat (nat (t ''x'')) + 1)"])
     apply(simp)
      apply(rule weakenpre)
      apply(rule If[where P="wp\<^sub>Q (IF Less (N 0) (V ''z'') THEN SKIP;; SKIP ELSE SKIP ) (\<lambda>s. eSuc (enat (6 * nat (s ''x'' - 1)) + 1))"])
      subgoal  
        apply simp 
        apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (SKIP) (\<lambda>s. eSuc (enat (6 * nat (s ''x'' - 1)) + 1))"])
        subgoal apply(rule weakenpre)  apply(rule Skip) by auto  
        subgoal apply(rule weakenpre) apply(rule Skip) by auto
        done
      subgoal
        apply simp 
        subgoal apply(rule weakenpre)  apply(rule Skip) by auto  
        done
     subgoal
              apply auto
    subgoal for s apply(cases "s ''x'' > 0") apply auto
      apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1) eSuc_enat) done
    subgoal for s apply(cases "s ''x'' > 0") apply auto
      apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1) eSuc_enat) done
    done
  subgoal apply simp apply(rule weakenpre) apply(rule Assign) by simp
     apply simp 
  subgoal for s apply(cases "s ''x'' > 0") by auto
  by simp
   
    
lemma whileDecrIf2: "\<turnstile>\<^sub>2\<^sub>' { %s. enat (nat (s ''x'')) + 1} WHILE (Less (N 0) (V ''x'')) DO ( (IF Less (N 0) (V ''z'') THEN SKIP;; SKIP ELSE SKIP );; ''x'' ::= Plus (V ''x'') (N (-1))) { %s. enat 0}"
  apply(rule conseq[OF While, where k=6 and I1="%s. enat 6 * (enat (nat (s ''x'')))"])
      apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (''x'' ::= Plus (V ''x'') (N (-1))) (\<lambda>t. enat 6 * enat (nat (t ''x'')) + 1)"])
     apply(simp)
      apply(rule weakenpre)
      apply(rule If[where P="wp\<^sub>Q (IF Less (N 0) (V ''z'') THEN SKIP;; SKIP ELSE SKIP ) (\<lambda>s. eSuc (enat (6 * nat (s ''x'' - 1)) + 1))"])
      subgoal  
        apply simp 
        apply(rule Seq[where P\<^sub>2="wp\<^sub>Q (SKIP) (\<lambda>s. eSuc (enat (6 * nat (s ''x'' - 1)) + 1))"])
        subgoal apply(rule weakenpre)  apply(rule Skip) by auto  
        subgoal apply(rule weakenpre) apply(rule Skip) by auto
        done
      subgoal
        apply simp 
        subgoal apply(rule weakenpre)  apply(rule Skip) by auto  
        done
     prefer 2
    subgoal apply simp apply(rule weakenpre) apply(rule Assign) by simp        
     subgoal
              apply auto
    subgoal for s apply(cases "s ''x'' > 0") apply auto
      apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1) eSuc_enat) done
    subgoal for s apply(cases "s ''x'' > 0") apply auto
      apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1) eSuc_enat) done
    done 
  subgoal for s apply(simp only: one_enat_def plus_enat_simps times_enat_simps enat_ord_code(1)) by presburger
  subgoal for s apply(cases "s ''x'' > 0") by auto
  by simp
    

end