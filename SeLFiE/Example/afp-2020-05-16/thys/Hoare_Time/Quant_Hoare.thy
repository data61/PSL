section "Quantitative Hoare Logic (due to Carbonneaux)"
theory Quant_Hoare
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
  
subsection "Validity of quantitative Hoare Triple"
  
(* this definition refines the definition of validity of normal Hoare Triple for total correctness  *)

definition hoare2_valid :: "qassn \<Rightarrow> com \<Rightarrow> qassn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>2 {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>2 {P} c {Q}  \<longleftrightarrow>  (\<forall>s.  P s < \<infinity> \<longrightarrow> (\<exists>t p. ((c,s) \<Rightarrow> p \<Down> t) \<and> P s \<ge> p + Q t))"

subsection "Hoare logic for quantiative reasoning"

inductive
  hoare2 :: "qassn \<Rightarrow> com \<Rightarrow> qassn \<Rightarrow> bool" ("\<turnstile>\<^sub>2 ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>2 {%s. eSuc (P s)} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>2 {\<lambda>s. eSuc (P (s[a/x]))} x::=a { P }"  |

If: "\<lbrakk> \<turnstile>\<^sub>2 {\<lambda>s. P s + \<up>( bval b s)} c\<^sub>1 { Q};
       \<turnstile>\<^sub>2 {\<lambda>s. P s + \<up>(\<not> bval b s)} c\<^sub>2 { Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>2 {\<lambda>s. eSuc (P s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q }"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>2 { P\<^sub>1 } c\<^sub>1 { P\<^sub>2 }; \<turnstile>\<^sub>2 {P\<^sub>2} c\<^sub>2 { P\<^sub>3 }\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>2 {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |
 
While:
  "\<lbrakk>   \<turnstile>\<^sub>2 { %s. I s + \<up>(bval b s) } c { %t. I t + 1 }   \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>2 {\<lambda>s. I s + 1 } WHILE b DO c {\<lambda>s.  I s + \<up>(\<not> bval b s)  }" |

conseq: "\<lbrakk> \<turnstile>\<^sub>2 {P}c{Q} ; \<And>s. P s \<le> P' s ; \<And>s. Q' s \<le> Q s \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>2 {P'}c{ Q'}"  

text \<open>derived rules\<close>

lemma strengthen_pre: "\<lbrakk> \<forall>s. P s \<le> P' s;  \<turnstile>\<^sub>2 {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>2 {P'} c {Q}"
  using conseq by blast 

lemma weaken_post: "\<lbrakk> \<turnstile>\<^sub>2 {P} c {Q};  \<forall>s. Q s \<ge> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>2 {P} c {Q'}"
  using conseq by blast

lemma Assign': "\<forall>s. P s \<ge> eSuc ( Q(s[a/x])) \<Longrightarrow> \<turnstile>\<^sub>2 {P} x ::= a {Q}" 
  by (simp add: strengthen_pre[OF _ Assign])    

lemma progress: "(c, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p > 0"
  by (induct rule: big_step_t.induct, auto)
    

lemma FalseImplies: "\<turnstile>\<^sub>2 {%s. \<infinity>} c { Q}"
  apply (induction c arbitrary: Q)
  apply(auto intro: hoare2.Skip hoare2.Assign hoare2.Seq hoare2.conseq)
  subgoal apply(rule hoare2.conseq) apply(rule hoare2.If[where P="%s. \<infinity>"]) by(auto intro: hoare2.If hoare2.conseq)
  subgoal apply(rule hoare2.conseq) apply(rule hoare2.While[where I="%s. \<infinity>"]) apply(rule hoare2.conseq) by auto 
  done
    
subsection "Soundness"

  
  
    
text\<open>The soundness theorem:\<close>
   
lemma help1: assumes " enat a + X \<le> Y"
    "enat b + Z \<le> X"
  shows "enat (a + b) + Z \<le> Y" 
  using assms  by (metis ab_semigroup_add_class.add_ac(1) add_left_mono order_trans plus_enat_simps(1))
    
lemma help2': assumes "enat p + INV t  \<le> INV s"
    "0 < p" "INV s = enat n"
  shows "INV t < INV s"
  using assms iadd_le_enat_iff by auto 
    
lemma help2: assumes "enat p + INV t + 1 \<le> INV s"
     "INV s = enat n"
  shows "INV t < INV s"
  using assms le_less_trans not_less_iff_gr_or_eq by fastforce  
  
    
lemma Seq_sound: assumes "\<Turnstile>\<^sub>2 {P1} C1 {P2}"
    "\<Turnstile>\<^sub>2 {P2} C2 {P3}" 
    shows  "\<Turnstile>\<^sub>2 {P1} C1 ;; C2 {P3}"
unfolding hoare2_valid_def                             
proof (safe) 
  fix s
  assume ninfP1: "P1 s < \<infinity>"
  with assms(1)[unfolded hoare2_valid_def] obtain t1 p1
    where 1: "(C1, s) \<Rightarrow> p1 \<Down> t1" and q1: "enat p1 + P2 t1 \<le> P1 s" by blast
  with ninfP1 have ninfP2: "P2 t1 < \<infinity>"
    using not_le by fastforce 
  with assms(2)[unfolded hoare2_valid_def] obtain t2 p2
    where 2: "(C2, t1) \<Rightarrow> p2 \<Down> t2" and q2: "enat p2 + P3 t2 \<le> P2 t1" by blast
  with ninfP2 have ninfP3: "P3 t2 < \<infinity>"
    using not_le by fastforce 
  
  from Big_StepT.Seq[OF 1 2] have bigstep: "(C1;; C2, s) \<Rightarrow> p1 + p2 \<Down> t2" by simp
  from help1[OF q1 q2] have potential: "enat (p1 + p2) + P3 t2 \<le> P1 s" .
  
  show "\<exists>t p. (C1;; C2, s) \<Rightarrow> p \<Down> t \<and> enat p + P3 t \<le> P1 s " 
    apply(rule exI[where x="t2"])
    apply(rule exI[where x="p1 + p2"]) 
    using bigstep potential by simp  
qed    
    
    
theorem hoare2_sound: "\<turnstile>\<^sub>2 {P}c{ Q}  \<Longrightarrow>  \<Turnstile>\<^sub>2 {P}c{ Q}"  
proof(induction rule: hoare2.induct) 
  case (Skip P)
  show ?case unfolding hoare2_valid_def apply(safe)
    subgoal for s apply(rule exI[where x=s]) apply(rule exI[where x="Suc 0"])  
      by (auto simp: eSuc_enat_iff eSuc_enat) 
    done
next
  case (Assign P a x)
  show ?case unfolding hoare2_valid_def apply(safe)
    subgoal for s apply(rule exI[where x="s[a/x]"]) apply(rule exI[where x="Suc 0"])  
      by (auto simp: eSuc_enat_iff eSuc_enat) 
    done
next
  case (Seq P1 C1 P2 C2 P3)
  thus ?case using Seq_sound by auto
next
  case (If P b c1 Q c2)
  show ?case  unfolding hoare2_valid_def
  proof (safe)
    fix s
    assume "eSuc (P s) < \<infinity>"
    then have i: "P s < \<infinity>"
      using enat_ord_simps(4) by fastforce  
    show "\<exists>t p. (IF b THEN c1 ELSE c2, s) \<Rightarrow> p \<Down> t \<and> enat p + Q t \<le> eSuc (P s)"
    proof(cases "bval b s")
      case True
      with i have "P s + emb (bval b s) < \<infinity>" by simp
      with If(3)[unfolded hoare2_valid_def] obtain p t
        where 1: "(c1, s) \<Rightarrow> p \<Down> t" and q: "enat p + Q t \<le> P s + emb (bval b s)"  by blast
      from Big_StepT.IfTrue[OF True 1] have 2: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p + 1 \<Down> t" by simp
      show ?thesis apply(rule exI[where x=t]) apply(rule exI[where x="p+1"])
        apply(safe) apply(fact)
        using q True apply(simp) 
        by (metis eSuc_enat eSuc_ile_mono iadd_Suc) 
    next
      case False
      with i have "P s + emb (~ bval b s) < \<infinity>" by simp
      with If(4)[unfolded hoare2_valid_def] obtain p t
        where 1: "(c2, s) \<Rightarrow> p \<Down> t" and q: "enat p + Q t \<le> P s + emb (~ bval b s)"  by blast
      from Big_StepT.IfFalse[OF False 1] have 2: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p + 1 \<Down> t" by simp
      show ?thesis apply(rule exI[where x=t]) apply(rule exI[where x="p+1"])
        apply(safe) apply(fact)
        using q False apply(simp)
        by (metis eSuc_enat eSuc_ile_mono iadd_Suc)
    qed
  qed
next
  case (conseq P c Q P' Q') 
  show ?case unfolding hoare2_valid_def
  proof (safe)
    fix s
    assume "P' s < \<infinity>"
    with conseq(2) have "P s < \<infinity>"
      using le_less_trans by blast  
    with conseq(4)[unfolded hoare2_valid_def] obtain p t where "(c, s) \<Rightarrow> p \<Down> t" "enat p + Q t \<le> P s" by blast    
    with conseq(2,3) show "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + Q' t \<le> P' s"
      by (meson add_left_mono dual_order.trans) 
  qed
next
  case (While INV b c)  
    
  from While(2)[unfolded hoare2_valid_def]
  have WH2: "\<And>s. INV s + \<up> (bval b s) < \<infinity> \<Longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + INV t + 1 \<le> INV s + \<up> (bval b s))"
    by (simp add: add.commute add.left_commute)     
        
  show ?case unfolding hoare2_valid_def
  proof (safe)
    fix s
    assume ninfINV: "INV s + 1 < \<infinity>" 
    then have "INV s < \<infinity>"
      using enat_ord_simps(4) by fastforce 
    then obtain n where i: "INV s = enat n" using not_infinity_eq
      by auto      
    
    text \<open>In order to prove validity, we induct on the value of the Invariant, which is a finite number
          and decreases in every loop iteration. For each step we show that validity holds.\<close>
    have "INV s = enat n \<Longrightarrow> \<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> enat p + (INV t + emb (\<not> bval b t)) \<le> INV s + 1"
    proof (induct n arbitrary: s rule: less_induct)
      case (less n) 
      show ?case
      proof (cases "bval b s")
        case False
        show ?thesis
          using WhileFalse[OF False] one_enat_def by fastforce
      next
        case True
        \<comment> \<open>obtain the loop body from the outer IH\<close>
        with less(2) WH2 obtain t p
          where o: "(c, s) \<Rightarrow> p \<Down> t"
            and q: "enat p + INV t + 1 \<le> INV s " by force

        \<comment> \<open>prepare premises to ...\<close>
        from q have g: "INV t < INV s"
          using help2 less(2) by metis 
        then have ninfINVt: "INV t < \<infinity>" using less(2)
          using enat_ord_simps(4) by fastforce 
        then obtain n' where i: "INV t = enat n'" using not_infinity_eq
          by auto 
        with less(2) have ii: "n' < n"
          using g by auto
        \<comment> \<open>... obtain the tail of the While loop from the inner IH\<close>
        from i ii less(1) obtain t2 p2
          where o2: "(WHILE b DO c, t) \<Rightarrow> p2 \<Down> t2"
            and q2: "enat p2 + (INV t2 + emb (\<not> bval b t2)) \<le> INV t + 1" by blast
        have ende: "~ bval b t2"
          apply(rule ccontr) apply(simp) using q2 ninfINVt
          by (simp add: i one_enat_def) 
            
        \<comment> \<open>combine body and tail to one loop unrolling:\<close>
        \<comment> \<open>- the Bigstep Semantic\<close>
        from WhileTrue[OF True o o2] have BigStep: "(WHILE b DO c, s) \<Rightarrow> 1 + p + p2 \<Down> t2" by simp

        \<comment> \<open>- the potentialPreservation\<close>       
        from ende q2 have q2': "enat p2 + INV t2 \<le> INV t + 1" by simp
        
        have potentialPreservation: "enat (1 + p + p2) + (INV t2 + \<up> (\<not> bval b t2)) \<le> INV s + 1"     
        proof -
          have "enat (1 + p + p2) + (INV t2 + \<up> (\<not> bval b t2))
            = enat (Suc (p + p2)) + INV t2" using ende by simp
          also have "\<dots> = enat (Suc p) + enat p2 + INV t2" by fastforce
          also have "\<dots> \<le> enat (Suc p) + INV t + 1" using q2'
            by (metis ab_semigroup_add_class.add_ac(1) add_left_mono) 
          also have "\<dots> \<le> INV s + 1" using q
            by (metis (no_types, hide_lams) add.commute add_left_mono eSuc_enat iadd_Suc plus_1_eSuc(1))
          finally show "enat (1 + p + p2) + (INV t2 + \<up> (\<not> bval b t2)) \<le> INV s + 1" .
        qed
            
        \<comment> \<open>finally combine BigStep Semantic and TimeBound\<close>
        show ?thesis 
          apply(rule exI[where x=t2])
          apply(rule exI[where x= "1 + p + p2"])
          apply(safe)
           by(fact BigStep potentialPreservation)+ 
       qed 
     qed  
    from this[OF i] show "\<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> enat p + (INV t + emb (\<not> bval b t)) \<le> INV s + 1" .        
  qed
qed 



  
subsection "Completeness"
    
  
(* the WeakestPrePotential  *)  
definition wp2 :: "com \<Rightarrow> qassn \<Rightarrow> qassn" ("wp\<^sub>2") where
"wp\<^sub>2 c Q  =  (\<lambda>s. (if (\<exists>t p. (c,s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>)  then enat (THE p. \<exists>t. (c,s) \<Rightarrow> p \<Down> t) + Q (THE t. \<exists>p. (c,s) \<Rightarrow> p \<Down> t) else \<infinity>))"

lemma wp2_alt: "wp\<^sub>2 c Q = (\<lambda>s. (if \<down>(c,s) then enat (\<down>\<^sub>t (c, s)) + Q (\<down>\<^sub>s (c, s)) else \<infinity>))"
  apply(rule ext) by(auto simp: bigstepT_the_state wp2_def split: if_split)    
    

theorem wp2_is_weakestprePotential: "\<Turnstile>\<^sub>2 {P}c{Q} \<longleftrightarrow> (\<forall>s. wp\<^sub>2 c Q s \<le> P s)" 
  unfolding  wp2_def hoare2_valid_def
  apply(rule)
  subgoal 
    apply(safe) subgoal for s
      apply(cases "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>")
        apply(simp) apply auto oops
  
  
lemma wp2_Skip[simp]: "wp\<^sub>2 SKIP Q = (%s. eSuc (Q s))"
  apply(auto intro!: ext simp: wp2_def)
   prefer 2
   apply(simp only: SKIPnot)
   apply(simp)
  apply(simp only: SKIPp SKIPt)
  using one_enat_def plus_1_eSuc(1) by auto    

lemma wp2_Assign[simp]: "wp\<^sub>2 (x ::= e) Q = (\<lambda>s. eSuc (Q (s(x := aval e s))))"
by (auto intro!: ext simp: wp2_def ASSp ASSt ASSnot eSuc_enat) 

   
  
lemma wp2_Seq[simp]: "wp\<^sub>2 (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>2 c\<^sub>1 (wp\<^sub>2 c\<^sub>2 Q)"
unfolding wp2_def (* what rule is doing: it uses the extensionality (ext) of functions *)
proof (rule, case_tac "\<exists>t p. (c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>", goal_cases)
  case (1 s)
  then obtain u p where ter: "(c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> p \<Down> u" and Q: "Q u < \<infinity>" by blast
  then obtain t p1 p2 where i: "(c\<^sub>1 , s) \<Rightarrow> p1 \<Down> t" and ii: "(c\<^sub>2 , t) \<Rightarrow> p2 \<Down> u" and p: "p1 + p2 = p" by blast

  from bigstepT_the_state[OF i] have t: "\<down>\<^sub>s (c\<^sub>1, s) = t"  
    by blast
  from bigstepT_the_state[OF ii] have t2: "\<down>\<^sub>s (c\<^sub>2, t) = u"  
    by blast
  from bigstepT_the_cost[OF i] have firstcost: "\<down>\<^sub>t (c\<^sub>1, s) = p1"  
    by blast
  from bigstepT_the_cost[OF ii] have secondcost: "\<down>\<^sub>t (c\<^sub>2, t) = p2"  
    by blast
  
  have totalcost: "\<down>\<^sub>t(c\<^sub>1;; c\<^sub>2, s) = p1 + p2"
    using bigstepT_the_cost[OF ter] p by auto
  have totalstate: "\<down>\<^sub>s(c\<^sub>1;; c\<^sub>2, s) = u"
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
   

lemma wp2_If[simp]:
 "wp\<^sub>2 (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. eSuc (wp\<^sub>2 (if bval b s then c\<^sub>1 else c\<^sub>2) Q s))"
  apply (auto simp: wp2_def fun_eq_iff)
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
 

lemma assumes b: "bval b s"
  shows wp2WhileTrue: " wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s  + 1 \<le> wp\<^sub>2 (WHILE b DO c) Q s"
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
  
  have "wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s + 1 = enat p + Q t"
    unfolding wp2_def apply(simp only: h if_True)
    apply(simp only: bigstepT_the_state[OF c] bigstepT_the_cost[OF c] g if_True bigstepT_the_state[OF w'] bigstepT_the_cost[OF w']) using sum
    by (metis One_nat_def ab_semigroup_add_class.add_ac(1) add.commute add.right_neutral eSuc_enat plus_1_eSuc(2) plus_enat_simps(1)) 
  also have "\<dots> = wp\<^sub>2 (WHILE b DO c) Q s"
    unfolding wp2_def apply(simp only: True if_True)
    using bigstepT_the_state bigstepT_the_cost w apply(simp) done
  finally show ?thesis by simp
next
  case False
  have "wp\<^sub>2 (WHILE b DO c) Q s = \<infinity>"
    unfolding wp2_def 
    apply(simp only: False if_False) done
  then show ?thesis by auto
qed

lemma assumes b: "bval b s"
shows wp2WhileTrue': "wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s  + 1 = wp\<^sub>2 (WHILE b DO c) Q s"
proof (cases "\<exists>p t. (WHILE b DO c, s) \<Rightarrow> p \<Down> t")
  case True
  then obtain t p where w: "(WHILE b DO c, s) \<Rightarrow> p \<Down> t"  by blast
  from b w obtain p1 p2 t1 where c: "(c, s) \<Rightarrow> p1 \<Down> t1" and w': "(WHILE b DO c, t1) \<Rightarrow> p2 \<Down> t" and sum: "1 + p1 + p2 = p"
    by auto 
  then have z: "\<down> (c, s)" and z2: "\<down> (WHILE b DO c, t1)" by auto 
  
  have "wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s + 1 = enat p + Q t"
    unfolding wp2_alt apply(simp only: z if_True)
    apply(simp only: bigstepT_the_state[OF c] bigstepT_the_cost[OF c] z2 if_True bigstepT_the_state[OF w'] bigstepT_the_cost[OF w'])
      using sum
    by (metis One_nat_def ab_semigroup_add_class.add_ac(1) add.commute add.right_neutral eSuc_enat plus_1_eSuc(2) plus_enat_simps(1)) 
  also have "\<dots> = wp\<^sub>2 (WHILE b DO c) Q s"
    unfolding wp2_alt apply(simp only: True if_True)
    using bigstepT_the_state bigstepT_the_cost w apply(simp) done
  finally show ?thesis by simp
next
  case False
  have "\<not> (\<down> (WHILE b DO c, \<down>\<^sub>s(c,s)) \<and> \<down> (c, s))"
  proof (rule)
    assume P: "\<down> (WHILE b DO c, \<down>\<^sub>s (c, s)) \<and> \<down> (c, s)"
    then obtain t s' where A: "(c,s) \<Rightarrow> t \<Down> s'" by blast 
    with A P have "\<down> (WHILE b DO c, s')" using bigstepT_the_state by auto
    then obtain t' s'' where B: "(WHILE b DO c,s') \<Rightarrow> t' \<Down> s''" by auto
    have "(WHILE b DO c, s) \<Rightarrow> 1+t+t' \<Down> s''" apply(rule WhileTrue) using b A B by auto
    then have "\<down> (WHILE b DO c, s)" by auto
    thus "False" using False by auto
  qed
  then have "\<not>\<down> (WHILE b DO c, \<down>\<^sub>s(c,s)) \<or> \<not>\<down> (c, s)" by simp 
  
  then show ?thesis apply rule
    subgoal unfolding wp2_alt apply(simp only: if_False False) by auto
    subgoal unfolding wp2_alt apply(simp only: if_False False) by auto
  done
qed
  
  
lemma assumes b: "~ bval b s"
  shows wp2WhileFalse: " Q s  + 1 \<le> wp\<^sub>2 (WHILE b DO c) Q s"
proof (cases "\<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> Q t < \<infinity>")
  case True
  with b obtain t p where w: "(WHILE b DO c, s) \<Rightarrow> p \<Down> t" and "Q t < \<infinity>" by blast
  with b have c: "s=t" "p=Suc 0" by auto
  have " wp\<^sub>2 (WHILE b DO c) Q s =  Q s  + 1"
    unfolding wp2_def apply(simp only: True if_True)
    using w c bigstepT_the_cost bigstepT_the_state by(auto simp add: one_enat_def)  
  then show ?thesis by auto
next
  case False
  have "wp\<^sub>2 (WHILE b DO c) Q s = \<infinity>"
    unfolding wp2_def 
    apply(simp only: False if_False) done
  then show ?thesis by auto
qed 
    
lemma thet_WhileFalse: "~ bval b s \<Longrightarrow> \<down>\<^sub>t (WHILE b DO c, s) = 1" by auto 
lemma thes_WhileFalse: "~ bval b s \<Longrightarrow> \<down>\<^sub>s (WHILE b DO c, s) = s" by auto 
  
lemma assumes b: "~ bval b s"
  shows wp2WhileFalse': "Q s  + 1 = wp\<^sub>2 (WHILE b DO c) Q s"
proof - 
  from b have T: "\<down> (WHILE b DO c, s)" by auto      
  show ?thesis unfolding wp2_alt using b apply(simp only: T if_True)
      by(simp add: thet_WhileFalse thes_WhileFalse one_enat_def) 
qed 
  
  
(* note that \<le> is sufficient for the completness proof *)
lemma wp2While: "(if bval b s then wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s else Q s) + 1 = wp\<^sub>2 (WHILE b DO c) Q s"  
  apply(cases "bval b s")      
  using wp2WhileTrue' apply simp
  using wp2WhileFalse' apply simp   done 
    
 
  
lemma assumes "\<And>Q. \<turnstile>\<^sub>2 {wp\<^sub>2 c Q} c {Q}"
  shows  "\<turnstile>\<^sub>2 {wp\<^sub>2 (WHILE b DO c) Q} WHILE b DO c {Q}"
proof -
  let ?I = "%s. (if bval b s then wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s else Q s)"
  from assms[of "wp\<^sub>2 (WHILE b DO c) Q"]
  have A: " \<turnstile>\<^sub>2 {wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q)} c {wp\<^sub>2 (WHILE b DO c) Q}" .
  have B: "\<turnstile>\<^sub>2 {\<lambda>s. (?I s) + \<up> (bval b s)} c {\<lambda>t. (?I t) + 1}"
    apply(rule conseq)
      apply(rule A)
     apply simp
      using wp2While apply simp done
  from hoare2.While[where I="?I"]
  have C: "\<turnstile>\<^sub>2 {\<lambda>s. (?I s) + \<up> (bval b s)} c {\<lambda>t. (?I t) + 1} \<Longrightarrow>
          \<turnstile>\<^sub>2 {\<lambda>s. (?I s) + 1} WHILE b DO c {\<lambda>s. (?I s) + \<up> (\<not> bval b s)}" by simp
  from C[OF B] have D: "\<turnstile>\<^sub>2 {\<lambda>s. (?I s) + 1} WHILE b DO c {\<lambda>s. (?I s) + \<up> (\<not> bval b s)}" .                           
  show "\<turnstile>\<^sub>2 {wp\<^sub>2 (WHILE b DO c) Q} WHILE b DO c {Q}"
    apply(rule conseq)
      apply(rule D)
    using wp2While apply simp
      apply simp  done
qed
                            

lemma wp2_is_pre: "\<turnstile>\<^sub>2 {wp\<^sub>2 c Q} c { Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case by (auto intro: hoare2.Skip)
next
  case Assign show ?case by (auto intro:hoare2.Assign)
next
  case Seq thus ?case by (auto intro:hoare2.Seq)
next 
  case (If x1 c1 c2 Q) thus ?case
    apply (auto intro!: hoare2.If )  
     apply(rule hoare2.conseq) 
       apply(auto)
     apply(rule hoare2.conseq) 
      apply(auto)
    done
next
  case (While b c)   
  show ?case
    apply(rule conseq)       
      apply(rule hoare2.While[where I="%s. (if bval b s then wp\<^sub>2 c (wp\<^sub>2 (WHILE b DO c) Q) s else Q s)"])       
      apply(rule conseq)        
        apply(rule While[of "wp\<^sub>2 (WHILE b DO c) Q"])      
    using wp2While by auto       
qed
  
  
  
lemma wp2_is_weakestprePotential1: "\<Turnstile>\<^sub>2 {P}c{Q} \<Longrightarrow> (\<forall>s. wp\<^sub>2 c Q s \<le> P s)" 
apply(auto simp: hoare2_valid_def wp2_def)
proof (goal_cases)
  case (1 s t p i) 
  show ?case
  proof(cases "P s < \<infinity>")
    case True
    with 1(1) obtain t p' where i: "(c, s) \<Rightarrow> p' \<Down> t" and ii: "enat p' + Q t \<le> P s"
      by auto    
    show ?thesis apply(simp add: bigstepT_the_state[OF i] bigstepT_the_cost[OF i] ii) done
  qed simp  
qed force
  
lemma wp2_is_weakestprePotential2: "(\<forall>s. wp\<^sub>2 c Q s \<le> P s) \<Longrightarrow> \<Turnstile>\<^sub>2 {P}c{Q}" 
apply(auto simp: hoare2_valid_def wp2_def)
proof (goal_cases)
  case (1 s i)
  then have A: "(if \<exists>t. (\<exists>p. (c, s) \<Rightarrow> p \<Down> t) \<and> (\<exists>i. Q t = enat i) then enat (THE p. Ex (big_step_t (c, s) p)) + Q (THE t. \<exists>p. (c, s) \<Rightarrow> p \<Down> t) else \<infinity>) \<le> P s"
    by fast 
  show ?case
  proof (cases "\<exists>t. (\<exists>p. (c, s) \<Rightarrow> p \<Down> t) \<and> (\<exists>i. Q t = enat i)")
    case True
    then obtain t p where i: "(c, s) \<Rightarrow> p \<Down> t" by blast
    from True A have "enat p + Q t \<le> P s" by (simp add: bigstepT_the_cost[OF i] bigstepT_the_state[OF i])
    then have "(c, s) \<Rightarrow> p \<Down> t \<and> enat p + Q t \<le> enat i" using 1(2) i by simp
    then show ?thesis by auto
  next
    case False
    with A have "P s \<ge> \<infinity>" by auto 
    then show ?thesis using 1 by auto
  qed   
qed
          
theorem wp2_is_weakestprePotential: "(\<forall>s. wp\<^sub>2 c Q s \<le> P s) \<longleftrightarrow> \<Turnstile>\<^sub>2 {P}c{Q}" 
 using   wp2_is_weakestprePotential2  wp2_is_weakestprePotential1 by metis

   
   
theorem hoare2_complete: "\<Turnstile>\<^sub>2 {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>2 {P}c{ Q}"  
apply(rule conseq[OF wp2_is_pre, where Q'=Q and Q=Q, simplified]) 
using wp2_is_weakestprePotential1 by blast

 


corollary hoare2_sound_complete: " \<turnstile>\<^sub>2 {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>2 {P}c{ Q}"
by (metis hoare2_sound hoare2_complete)



end