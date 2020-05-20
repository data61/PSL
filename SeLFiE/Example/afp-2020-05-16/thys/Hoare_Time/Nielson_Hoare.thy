theory Nielson_Hoare
imports Big_StepT 
begin

section "Nielson Style Hoare Logic with logical variables"

abbreviation "eq a b == (And (Not (Less a b)) (Not (Less b a)))"
   
type_synonym lvname = string
type_synonym assn2 = "(lvname \<Rightarrow> nat) \<Rightarrow> state \<Rightarrow> bool"
type_synonym tbd = "state \<Rightarrow> nat" (* time bound *)

subsection \<open>The support of an assn2\<close>

definition support :: "assn2 \<Rightarrow> string set" where
"support P = {x. \<exists>l1 l2 s. (\<forall>y. y \<noteq> x \<longrightarrow> l1 y = l2 y) \<and> P l1 s \<noteq> P l2 s}"


lemma support_and: "support (\<lambda>l s. P l s \<and> Q l s) \<subseteq> support P \<union> support Q"
unfolding support_def by blast
  
lemma support_impl: "support (\<lambda>l s. P s \<longrightarrow> Q l s) \<subseteq> support Q"
unfolding support_def by blast
  
lemma support_exist: "support (\<lambda>l s. \<exists> z::nat. Q z l s) \<subseteq> (UN n. support (Q n))"
  unfolding support_def apply(auto)
  by blast+   

    
lemma support_all: "support (\<lambda>l s. \<forall>z. Q z l s) \<subseteq> (UN n. support (Q n))"
  unfolding support_def apply(auto)
  by blast+  
    
    
lemma support_single: "support (\<lambda>l s. P (l a) s) \<subseteq> {a}"
  unfolding support_def by fastforce
    
lemma support_inv: "\<And>P. support (\<lambda>l s. P s) = {}"
unfolding support_def by blast 

lemma assn2_lupd: "x \<notin> support Q \<Longrightarrow> Q (l(x:=n)) = Q l"
by(simp add: support_def fun_upd_other fun_eq_iff)
  (metis (no_types, lifting) fun_upd_def)

subsection "Validity"
  
abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

definition hoare1_valid :: "assn2 \<Rightarrow> com \<Rightarrow> tbd \<Rightarrow> assn2 \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>1 {(1_)}/ (_)/ { _ \<Down>(1_)}" 50) where
"\<Turnstile>\<^sub>1 {P} c {q \<Down> Q}  \<longleftrightarrow>  (\<exists>k>0. (\<forall>l s. P l s \<longrightarrow> (\<exists>t p. ((c,s) \<Rightarrow> p \<Down> t) \<and>  p \<le> k * (q s) \<and> Q l t)))"


subsection "Hoare rules"
  
inductive
  hoare1 :: "assn2 \<Rightarrow> com \<Rightarrow> tbd \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>1 ({(1_)}/ (_)/ { _ \<Down> (1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>1 {P} SKIP { (%s. Suc 0) \<Down> P}"  |

Assign:  "\<turnstile>\<^sub>1 {\<lambda>l s. P l (s[a/x])} x::=a {  (%s. Suc 0) \<Down> P}"  |

If: "\<lbrakk> \<turnstile>\<^sub>1 {\<lambda>l s. P l s \<and> bval b s} c\<^sub>1 { e1 \<Down> Q};
       \<turnstile>\<^sub>1 {\<lambda>l s. P l s \<and> \<not> bval b s} c\<^sub>2 { e1 \<Down> Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>1 {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { (\<lambda>s. e1 s + Suc 0 ) \<Down> Q}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>1 { (%l s. P\<^sub>1 l s \<and> l x = e2' s ) } c\<^sub>1 { e1 \<Down> (%l s. P\<^sub>2 l s \<and>  e2 s \<le> l x )};
         \<turnstile>\<^sub>1 {P\<^sub>2} c\<^sub>2 { e2 \<Down> P\<^sub>3}; x \<notin> support P\<^sub>1; x \<notin> support P\<^sub>2;
         \<And>l s. P\<^sub>1 l s \<Longrightarrow> e1 s + e2' s \<le> e s\<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>1 {P\<^sub>1} c\<^sub>1;;c\<^sub>2 { e \<Down> P\<^sub>3}"  |

While:
  "\<lbrakk> \<turnstile>\<^sub>1 {\<lambda>l s. P l s \<and> bval b s \<and> e' s = l y} c {  e'' \<Down> \<lambda>l s. P l s \<and> e s \<le> l y};
       \<forall>l s. bval b s \<and> P l s \<longrightarrow>  e s \<ge> 1  +  e' s + e'' s  ; 
     \<forall>l s. ~ bval b s \<and> P l s \<longrightarrow> 1 \<le> e s;
     y \<notin> support P  \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>1 {P} WHILE b DO c { e \<Down> \<lambda>l s. P l s \<and> \<not> bval b s}" |

conseq: "\<lbrakk> \<exists>k>0. \<forall>l s. P' l s \<longrightarrow> ( e s \<le> k * (e' s) \<and>(\<forall>t. \<exists>l'. P l' s \<and> ( Q l' t \<longrightarrow> Q' l t) ));
           \<turnstile>\<^sub>1 {P}c{ e \<Down> Q}   \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>1 {P'}c{e' \<Down> Q'}"  
  
  
text\<open>Derived Rules:\<close>

lemma conseq_old: "\<lbrakk>\<exists>k>0. \<forall>l s. P' l s \<longrightarrow> (P l s \<and> ( e' s \<le>  k * (e s))); \<turnstile>\<^sub>1 {P}c{ e' \<Down>  Q}; \<forall>l s. Q l s \<longrightarrow> Q' l s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>1 {P'}c{e \<Down> Q'}"
  using conseq apply(metis) done

lemma If2: "\<lbrakk> \<turnstile>\<^sub>1 {\<lambda>l s. P l s \<and> bval b s} c\<^sub>1 { e \<Down> Q}; \<turnstile>\<^sub>1 {\<lambda>l s. P l s \<and> \<not> bval b s} c\<^sub>2 { e \<Down> Q};
        \<And>l s. P l s \<Longrightarrow> e s + 1 = e' s \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>1 {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { e' \<Down> Q}"
apply(rule conseq[OF _ If, where P=P and P'=P]) by(auto)

lemma strengthen_pre:
  "\<lbrakk> \<forall>l s. P' l s \<longrightarrow> P l s ;  \<turnstile>\<^sub>1 {P} c { e \<Down> Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>1 {P'} c { e \<Down> Q}"
  apply(rule conseq_old[where e'=e and Q=Q and P=P])
    by(auto)

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>1 {P} c {e \<Down> Q};  \<forall>l s. Q l s \<longrightarrow> Q' l s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>1 {P} c {e \<Down> Q'}"
  apply(rule conseq_old[where   e'=e and Q=Q and P=P])
    by(auto)

lemma ub_cost:
  "\<lbrakk> (\<exists>k>0. \<forall>l s. P l s \<longrightarrow> e' s \<le> k * (e s));  \<turnstile>\<^sub>1 {P} c {e' \<Down> Q} \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>1 {P} c {e \<Down> Q}"
  apply(rule conseq_old[where e'=e' and Q=Q and P=P])
  by(auto) 

lemma Assign': "\<forall>l s. P l s \<longrightarrow> Q l (s[a/x]) \<Longrightarrow> (\<turnstile>\<^sub>1 {P} x ::= a { (%s. 1) \<Down> Q})"
using strengthen_pre[OF _ Assign] 
by (simp )

 
subsection "Soundness"
  
text\<open>The soundness theorem:\<close>

theorem hoare1_sound: "\<turnstile>\<^sub>1 {P}c{e \<Down> Q}  \<Longrightarrow>  \<Turnstile>\<^sub>1 {P}c{e \<Down> Q}"
apply(unfold hoare1_valid_def)
proof(  induction  rule: hoare1.induct)
  case (Skip P)
  show ?case  by fastforce
next
  case (Assign P a x)
  show ?case  by fastforce 
next
  case (Seq P1 x e2' c1 e1 P2 e2 c2 P3 e)
  from Seq(6) obtain k where k: "k>0" and  S6: "\<forall>l s. P1 l s \<and> l x = e2' s \<longrightarrow> (\<exists>t p. (c1, s) \<Rightarrow> p \<Down> t \<and> p \<le> k * e1 s \<and> P2 l t \<and> e2 t \<le> l x)" by auto
  from Seq(7) obtain k' where k': "k'>0" and  S7:  "\<forall>l s. P2 l s \<longrightarrow> (\<exists>t p. (c2, s) \<Rightarrow> p \<Down> t \<and> p \<le> k' * e2 s \<and> P3 l t)" by auto
  from k k' have "0 < max k k'" by auto
  show ?case 
  proof (rule exI[where x="max k k'"], safe)
    fix l s 
    have x_supp: "x \<notin> support P1" by fact
    have x_supp2: "x \<notin> support P2" by fact

    from S6 have S: "P1 (l(x := e2' s)) s \<and> (l(x := e2' s)) x = e2' s \<longrightarrow> (\<exists>t p. (c1, s) \<Rightarrow> p \<Down> t \<and>  p \<le> k * e1 s \<and> P2 (l(x := e2' s)) t \<and> e2 t \<le> (l(x := e2' s)) x) "
       by blast
     
    assume a: "P1 l s"

    with Seq(5) have 1: " e1 s + e2' s \<le>   e s" by simp 
    with a S assn2_lupd[OF x_supp] have "(\<exists>t p. (c1, s) \<Rightarrow> p \<Down> t \<and> p \<le> k * e1 s \<and> P2 (l(x := e2' s)) t \<and> e2 t \<le> (l(x := e2' s)) x)" by simp
    then obtain t p where c1: "(c1, s) \<Rightarrow> p \<Down> t" and cost1: " p \<le> k * e1 s" and P2': "P2 (l(x := e2' s)) t" and 31: "e2 t \<le> (l(x := e2' s)) x" by blast
    from P2' assn2_lupd[OF x_supp2] have P2: "P2 l t" by auto
    from 31 have 3: "e2 t \<le> e2' s" by simp 
    from S7 P2 have "(\<exists>t' p'. ((c2, t) \<Rightarrow> p' \<Down> t') \<and>   p' \<le> k' * e2 t \<and> P3 l t')" by blast
    then obtain t' p'  where c2: "(c2, t) \<Rightarrow> p' \<Down> t'" and cost2: " p' \<le> k' * (e2 t)" and P3: "P3 l t'" by blast

    from c1 c2 have weg: "(c1;; c2, s) \<Rightarrow> p + p' \<Down> t'"  
      apply (rule Big_StepT.Seq) by simp
    from cost1 cost2 3 have " (p+p') \<le> k * (e1 s) + k' * (e2' s)"
      by (meson add_mono mult_le_mono2 order_subst1)  
    also have "\<dots> \<le> (max k k') * (e1 s) + (max k k') * (e2' s)"
      by (simp add: add_mono) 
    also have "\<dots> \<le> (max k k') * (e1 s + e2' s)"
      by (simp add: add_mult_distrib2)      
    also have "\<dots> \<le> (max k k') * (e s)" using 1 by simp
  finally
    have cost: " (p + p') \<le> (max k k') * (e s)" .
      
    from weg cost P3
    have "(c1;; c2, s) \<Rightarrow> p+p' \<Down> t' \<and>   (p+p') \<le> (max k k') * (e s) \<and> P3 l t'" by blast
    then show "(\<exists>t p. (c1;; c2, s) \<Rightarrow> p \<Down> t \<and>  p \<le> (max k k') * (e s) \<and> P3 l t)" by metis
  qed fact
next
  case (If P b c1 e Q c2)
  from If(3) obtain k1 where k1: "k1>0" and If1: "\<forall>l s. P l s \<and> bval b s \<longrightarrow> (\<exists>t p. (c1, s) \<Rightarrow> p \<Down> t \<and> p \<le> k1 * e s \<and> Q l t)" by auto
  from If(4) obtain k2 where  k2: "k2>0" and If2: "\<forall>l s. P l s \<and> \<not> bval b s \<longrightarrow> (\<exists>t p. (c2, s) \<Rightarrow> p \<Down> t \<and> p \<le> k2 * e s \<and> Q l t)" by auto
  let ?k' = "max (k1+1) (k2+1)"
  have "?k'>0" by auto  
  show ?case
  proof (rule exI[where x="?k'"], safe)
    fix l s
    assume P1: "P l s"
    show "\<exists>t p. (IF b THEN c1 ELSE c2, s) \<Rightarrow> p \<Down> t \<and>  p \<le> ?k' * (e s + Suc 0) \<and> Q l t"
    proof (cases "bval b s")
      case True
      with If1 P1 obtain t p where "(c1, s) \<Rightarrow> p \<Down> t" "p \<le> k1 * (e s)" "Q l t" by blast
      with True have 1: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t" "(p + 1) \<le> (k1+1) * (e s  + Suc 0)"
          "Q l t"
        by auto  
      have "(k1+1) * (e s  + Suc 0) \<le> ?k' * (e s  + Suc 0)"
        by (simp add: nat_mult_max_left) 
      with 1 have 2: "p+1   \<le> ?k' * (e s  + Suc 0)"
        by linarith
      from 1 2 show "\<exists>t p. (IF b THEN c1 ELSE c2, s) \<Rightarrow> p \<Down> t \<and> p \<le> ?k' * (e s + Suc 0) \<and> Q l t" by metis
    next
      case False
      with If2 P1 obtain t p where "(c2, s) \<Rightarrow> p \<Down> t" "p \<le> k2 * (e s)" "Q l t" by blast
      with False have 1: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t" "(p + 1) \<le> (k2+1) * ( e s  + Suc 0)"
          "Q l t"
        by auto 
      have "(k2+1) * (e s  + Suc 0) \<le> ?k' * (e s  + Suc 0)"
        by (simp add: nat_mult_max_left)  
      with 1 have 2: "p+1   \<le> ?k' * (e s  + Suc 0)"
        by linarith
      from 1 2 show "\<exists>t p. (IF b THEN c1 ELSE c2, s) \<Rightarrow> p \<Down> t \<and>  p \<le> ?k' * (e s + Suc 0) \<and> Q l t" by metis
    qed
  qed fact
next
  case (conseq P' e e' P Q Q' c)
  from conseq(1) obtain k1 where k1: "k1>0" and c1: "\<forall>l s. P' l s \<longrightarrow> e s \<le> k1 * e' s \<and> (\<forall>t. \<exists>l'. P l' s \<and> (Q l' t \<longrightarrow> Q' l t))" by auto
  then have c1': "\<And>l s. P' l s \<Longrightarrow> e s \<le> k1 * e' s \<and> (\<forall>t. \<exists>l'. P l' s \<and> (Q l' t \<longrightarrow> Q' l t))"
    by auto
  from conseq(3) obtain k2 where k2: "k2>0" and c2: "\<forall>l s. P l s \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le> k2 * e s \<and> Q l t)" by auto
  then have c2': "\<And>l s.  P l s \<Longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le> k2 * e s \<and> Q l t)" by auto
  have "k2*k1 > 0" using k1 k2 by auto
  show ?case 
  proof (rule exI[where x="k2*k1"], safe)
    fix l s
    assume "P' l s"
    with c1' have A: "e s \<le> k1 * e' s" and "\<And>t. \<exists>l'. P l' s \<and> (Q l' t \<longrightarrow> Q' l t)" by auto
    then obtain fl where "\<And>t. P (fl t) s" and B: "\<And>t. Q (fl t) t \<longrightarrow> Q' l t" by metis
    with c2' obtain ft fp where i: "\<And>t. (c, s) \<Rightarrow> (fp t) \<Down> (ft t)" and ii: "\<And>t. (fp t) \<le> k2 * e s"
        and iii: "\<And>t. Q (fl t) (ft t)" 
      by meson
    from i obtain t p where tt: "\<And>x. ft x = t" "\<And>x. fp x = p" using big_step_t_determ2
      by meson
    with i have c: "(c, s) \<Rightarrow> p \<Down> t" by simp   
    from tt ii iii have p: "p \<le> k2 * e s" and Q: "\<And>x. Q (fl x) t" by auto
    have p: "p \<le> k2 * k1 * e' s" using p A
      by (metis le_trans mult.assoc mult_le_mono2)  
    from B Q have q: "Q' l t" by fast
    
    from c p q
    show "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le>  k2 *k1 * e' s \<and> Q' l t" 
      by blast
  qed fact  
next
  case (While INV b e' y c e'' e)  
  from While(5) obtain k where W6: "\<forall>l s. INV l s \<and> bval b s \<and> e' s = l y \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le> k * e'' s \<and> INV l t \<and> e t \<le> l y)" by auto 
  let ?k' = "k+1"
  {
    fix n l s
    have "\<lbrakk> e s = n; INV l s \<rbrakk> \<Longrightarrow> \<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> p \<le> ?k' * e s \<and> INV l t \<and> \<not> bval b t"
    proof(induction "n" arbitrary: l s rule: less_induct)
      case (less x)
        
      show ?case
      proof (cases "bval b s")
        case False
        with less(2,3) While(3) have  b: "1 \<le> e s" by auto

        show ?thesis
          apply(rule exI[where x=s])
          apply(rule exI[where x=1]) apply safe
          subgoal using  WhileFalse[OF False] by simp 
          subgoal using b by auto 
          subgoal using less by auto
          subgoal using False by auto
          done
            
      next 
      case True
      with less(2,3) While(2) have bT: "bval b s" and cost1: "  1 + e' s + e'' s \<le> e s" by auto 
      let ?l' = "l(y := e' s)"

      have y_supp: "y \<notin> support INV" by fact 
 
      from cost1 have Z: "e' s < x" using less(2) by auto
      from W6
      have "INV ?l' s \<and> bval b s \<and> e' s = ?l' y
            \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and>   p \<le> k * e'' s  \<and> INV ?l' t \<and> e t \<le> ?l' y)"
          by blast
      with less(3) bT
      have "(\<exists>t p. ((c, s) \<Rightarrow> p \<Down> t) \<and>   p \<le> k * e'' s  \<and> INV ?l' t \<and> e t \<le> e' s)"
            using   assn2_lupd[OF y_supp] 
        by(auto)  
      then obtain t p   where ceff: "(c, s) \<Rightarrow> p \<Down> t" and cost2: " p \<le>  k * e'' s" 
                    and INVz': "INV ?l' t" and cost3: "  e t \<le>   e' s"
        by blast 

      from INVz' have INVz: "INV l t" using assn2_lupd[OF y_supp] by auto 
      have "e t < x" using Z cost3 by auto
      with less(1)[OF _ _ INVz, of "e t"]  obtain t' p' 
        where weff: "(WHILE b DO c, t) \<Rightarrow> p' \<Down> t'" and cost4: " p' \<le> ?k' *  e t" and INV0: "INV l t'"
            and nb: "\<not> bval b t'"
          by fastforce      

      have "(WHILE b DO c, s) \<Rightarrow> 1 + p + p'  \<Down> t'"
        apply(rule WhileTrue)
          apply fact
          apply (fact ceff) 
          apply (fact weff) by simp
    moreover
      note INV0 nb
      moreover
      {
        have "(1 + p + p') \<le> 1 + k * e'' s + ?k' * e t" using cost2 cost4 by linarith
        also have "\<dots> \<le>  1 + k * e'' s + ?k' * e' s" using cost3
          using add_left_mono mult_le_mono2 by blast 
        also have "\<dots> \<le> ?k'*1 + ?k'* e'' s + ?k' * e' s " by force 
        also have "\<dots> = ?k' * (1+ e' s + e'' s)" by algebra
        also have "\<dots> \<le> ?k' * e s" using cost1
          using mult_le_mono2 by blast            
        finally have " (1 + p + p') \<le> ?k' * e s" .
      }
    ultimately  
      show ?thesis by metis
    qed 
    qed
  }  
  then have erg: "\<And>l s. INV l s \<Longrightarrow> \<exists>t p. (WHILE b DO c, s) \<Rightarrow> p \<Down> t \<and> p \<le> (k + 1) * e s \<and> INV l t \<and> \<not> bval b t" by auto
  show ?case apply(rule exI[where x="?k'"]) using erg by fastforce
qed 

subsection "Completeness"

definition wp1 :: "com \<Rightarrow> assn2 \<Rightarrow> assn2" ("wp\<^sub>1") where
"wp\<^sub>1 c Q  =  (\<lambda>l s. \<exists>t p. (c,s) \<Rightarrow> p \<Down> t \<and> Q l t)"
 

lemma support_wpt: "support (wp\<^sub>1 c Q) \<subseteq> support Q"
by(simp add: support_def wp1_def) blast

  
lemma wp1_terminates: "wp\<^sub>1 c Q l s \<Longrightarrow> \<down> (c, s)" unfolding wp1_def by auto

    
lemma wp1_SKIP[simp]: "wp\<^sub>1 SKIP Q = Q" by(auto intro!: ext simp: wp1_def)

lemma wp1_Assign[simp]: "wp\<^sub>1 (x ::= e) Q = (\<lambda>l s. Q l (s(x := aval e s)))" by(auto intro!: ext simp: wp1_def)

lemma wp1_Seq[simp]: "wp\<^sub>1 (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>1 c\<^sub>1 (wp\<^sub>1 c\<^sub>2 Q)" by (auto simp: wp1_def fun_eq_iff)

lemma wp1_If[simp]: "wp\<^sub>1 (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>l s. wp\<^sub>1 (if bval b s then c\<^sub>1 else c\<^sub>2) Q l s)" by (auto simp: wp1_def fun_eq_iff)

    
definition "prec c E == %s. E (THE t. (\<exists>p. (c,s) \<Rightarrow> p \<Down> t))"
  
lemma wp1_prec_Seq_correct: "wp\<^sub>1 (c1;;c2) Q l s \<Longrightarrow> \<down>\<^sub>t (c1, s) + prec c1 (\<lambda>s. \<down>\<^sub>t (c2, s)) s \<le> \<down>\<^sub>t (c1;; c2, s)"
proof -
  assume "wp\<^sub>1 (c1;;c2) Q l s"
  then have wp: "wp\<^sub>1 c1 (wp\<^sub>1 c2 Q) l s" by simp
  then obtain t p where c1_term: "(c1, s) \<Rightarrow> p \<Down> t" and "(\<exists>ta p. (c2, t) \<Rightarrow> p \<Down> ta \<and> Q l ta)" unfolding wp1_def by blast
  then obtain t' p' where c2_term: "(c2, t) \<Rightarrow> p' \<Down> t'" and  "Q l t'" by blast

  have p: "\<down>\<^sub>t (c1, s) = p" using c1_term bigstepT_the_cost by simp
  have "\<down>\<^sub>t (c2, t) = p'" using c2_term bigstepT_the_cost by simp

  have f: "(THE t. \<exists>p. (c1, s) \<Rightarrow> p \<Down> t) = t" using c1_term bigstepT_the_state by simp

  have " prec c1 (\<lambda>s. \<down>\<^sub>t (c2, s)) s = p'" unfolding prec_def f using c2_term bigstep_det by blast
  then have p': " prec c1 (\<lambda>s.  (THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a)) s
        =  p'" unfolding prec_def by blast

  from wp have "wp\<^sub>1 (c1;;c2) Q l s" by simp
  then obtain T P where c12_term: "(c1;;c2, s) \<Rightarrow> P \<Down> T" and "Q l T" unfolding wp1_def by blast

  have P: "(THE n. (\<exists>a. (c1;;c2, s) \<Rightarrow> n \<Down> a)) = P" using c12_term bigstepT_the_cost by simp

  from c12_term have Ppp': "P = p + p'"
    apply(elim Seq_tE)
    using c1_term bigstep_det c2_term by blast

  have " (THE n. \<exists>a. (c1, s) \<Rightarrow> n \<Down> a) + prec c1 (\<lambda>s.  (THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a)) s
        =  p +  p'" using p p' by auto
  also have "\<dots> =  P" using Ppp' by auto
  also have "\<dots> =  (THE n. (\<exists>a. (c1;;c2, s) \<Rightarrow> n \<Down> a))" using P by auto
  finally
  show "\<down>\<^sub>t (c1, s) + prec c1 (\<lambda>s. \<down>\<^sub>t (c2, s)) s \<le> \<down>\<^sub>t (c1;; c2, s)"
    by simp
qed 
  


abbreviation "new Q \<equiv> SOME x. x \<notin> support Q"

lemma bigstep_det: "(c1, s) \<Rightarrow> p1 \<Down> t1 \<Longrightarrow> (c1, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp

lemma bigstepT_the_cost: "(c, s) \<Rightarrow> P \<Down> T \<Longrightarrow> (THE n. \<exists>a. (c, s) \<Rightarrow> n \<Down> a) = P"
  using bigstep_det by blast 

lemma bigstepT_the_state: "(c, s) \<Rightarrow> P \<Down> T \<Longrightarrow> (THE a. \<exists>n. (c, s) \<Rightarrow> n \<Down> a) = T"
  using bigstep_det by blast 
   
lemma assumes b: "bval b s"
  shows wp1WhileTrue': "wp\<^sub>1 (WHILE b DO c) Q l s = wp\<^sub>1 c (wp\<^sub>1 (WHILE b DO c) Q) l s"
proof 
  assume "wp\<^sub>1 c (wp\<^sub>1 (WHILE b DO c) Q) l s"
  from this[unfolded wp1_def]
  obtain t s' t' s'' where "(c, s) \<Rightarrow> t \<Down> s'" "(WHILE b DO c, s') \<Rightarrow> t' \<Down> s''" and Q: "Q l s''" by blast
  with b have "(WHILE b DO c, s) \<Rightarrow> 1+t+t' \<Down> s''" by auto
  with Q show "wp\<^sub>1 (WHILE b DO c) Q l s" unfolding wp1_def by auto
next
  assume "wp\<^sub>1 (WHILE b DO c) Q l s"
  from this[unfolded wp1_def]
  obtain t s'' where "(WHILE b DO c, s) \<Rightarrow> t \<Down> s''" and Q: "Q l s''" by blast
  with b  obtain t1 t2 s' where "(c, s) \<Rightarrow> t1 \<Down> s'" "(WHILE b DO c, s') \<Rightarrow> t2 \<Down> s''" by auto
  with Q show "wp\<^sub>1 c (wp\<^sub>1 (WHILE b DO c) Q) l s " unfolding wp1_def by auto
qed
  
lemma assumes b: "~ bval b s"
  shows wp1WhileFalse': "wp\<^sub>1 (WHILE b DO c) Q l s =  Q l s"
proof 
  assume "wp\<^sub>1 (WHILE b DO c) Q l s"
  from this[unfolded wp1_def]
  obtain t s' where "(WHILE b DO c, s) \<Rightarrow> t \<Down> s'" and Q: "Q l s'" by blast
  with b  have "s=s'" by auto
  with Q show "Q l s" by auto
next
  assume "Q l s"
  with b show  "wp\<^sub>1 (WHILE b DO c) Q l s" unfolding wp1_def by auto
qed
  
lemma wp1While: "wp\<^sub>1 (WHILE b DO c) Q l s = (if bval b s then wp\<^sub>1 c (wp\<^sub>1 (WHILE b DO c) Q) l s else Q l s)"  
  apply(cases "bval b s")      
  using wp1WhileTrue' apply simp
  using wp1WhileFalse' apply simp   done 
  
lemma wp1_prec2: fixes e::tbd
    shows "(wp\<^sub>1 c1 Q l s \<and>
           l x = prec c1 e s) = wp\<^sub>1 c1 (\<lambda>l s. Q l s \<and> e s = l x) l s"
      by (metis (mono_tags, lifting) Big_StepT.bigstepT_the_state prec_def wp1_def)
      
      
lemma wp1_prec: fixes e::tbd
    shows "wp\<^sub>1 c1 Q l s \<Longrightarrow>
           l x = prec c1 e s \<Longrightarrow> wp\<^sub>1 c1 (\<lambda>l s. Q l s \<and> e s = l x) l s"
unfolding wp1_def prec_def apply(auto) 
proof -
  fix p t
  assume "l x = e (THE t. \<exists>p. (c1, s) \<Rightarrow> p \<Down> t)"
  assume 2: "Q l t"
  assume 1: "(c1, s) \<Rightarrow> p \<Down> t "
  show "\<exists>t. (\<exists>p. (c1, s) \<Rightarrow> p \<Down> t) \<and> Q l t \<and> e t = e (THE t. \<exists>p. (c1, s) \<Rightarrow> p \<Down> t) "
    apply(rule exI[where x=t])
    apply(safe)
      apply(rule exI[where x=p]) using 1 apply simp
      apply(fact)
      using 1 by(simp add: bigstepT_the_state)
qed 
  

lemma wp1_is_pre: "finite (support Q) \<Longrightarrow> \<turnstile>\<^sub>1 {wp\<^sub>1 c Q} c { \<lambda>s. \<down>\<^sub>t (c, s) \<Down> Q}"
proof (induction c arbitrary: Q)
  case SKIP
  have ff: "\<And>s n. (\<exists>a. (SKIP, s) \<Rightarrow> n \<Down> a) = (n=Suc 0)" by blast  
  show ?case apply (auto intro:hoare1.Skip simp add: ff) using ff done
next
  have gg: "\<And>x1 x2 s n. (\<exists>a. (x1 ::= x2, s) \<Rightarrow> n \<Down> a) = (n=Suc 0)" by blast
  case Assign show ?case apply (auto intro:hoare1.Assign simp add: gg) done
next
  case (Seq c1 c2)  
  \<comment> \<open>choose a fresh logical variable x\<close>
  let ?x = "new Q"
  have "\<exists>x. x \<notin> support Q" using Seq.prems infinite_UNIV_listI
    using ex_new_if_finite by blast
  hence  "?x \<notin> support Q" by (rule someI_ex) 
  then have x2: "?x \<notin> support (wp\<^sub>1 c2 Q)"  using support_wpt by (fast)
  then have x12: "?x \<notin> support (wp\<^sub>1 (c1;;c2) Q)" apply simp using support_wpt by fast

  \<comment> \<open>assemble a postcondition Q1 that ensures the weakest precondition of Q before c2
        and saves the running time of c2 into the logical variable x\<close>
  let ?Q1 = "(\<lambda>l s. (wp\<^sub>1 c2 Q) l s \<and>  \<down>\<^sub>t (c2, s) = l ?x)"
  have "finite (support ?Q1)" apply(rule rev_finite_subset[OF _ support_and])
     apply(rule finite_UnI)
      apply(rule rev_finite_subset[OF _ support_wpt]) apply(fact)
    apply(rule rev_finite_subset[OF _ support_single]) by simp
  \<comment> \<open>we can now specify this Q1 in the first Induction Hypothesis\<close>    
  then have pre: "\<And>u. \<turnstile>\<^sub>1 {wp\<^sub>1 c1 ?Q1 } c1 { \<lambda>s. \<down>\<^sub>t (c1, s) \<Down>  ?Q1  }"
    using Seq(1) by simp  

  \<comment> \<open>we can rewrite this into the form we need for the Seq rule\<close>
  have A: " \<turnstile>\<^sub>1 {\<lambda>l s. wp\<^sub>1 (c1;;c2) Q l s \<and> l ?x = (prec c1 (%s. \<down>\<^sub>t (c2, s))) s} c1 { \<lambda>s. \<down>\<^sub>t (c1, s) \<Down> \<lambda>l s. wp\<^sub>1 c2 Q l s \<and>  \<down>\<^sub>t (c2, s) \<le> l ?x}"
    apply(rule conseq_old[OF _ pre ])
    by(auto simp add: wp1_prec) 

  \<comment> \<open>we can now apply the Seq rule with the first IH (in the right shape A) and the second IH\<close>
  show "\<turnstile>\<^sub>1 {wp\<^sub>1 (c1;; c2) Q} c1;; c2 { \<lambda>s. \<down>\<^sub>t (c1;; c2, s) \<Down> Q}"
    apply(rule hoare1.Seq[OF A Seq(2)])  
       \<comment> \<open>finally some side conditions have to be proven\<close> 
       using Seq(3) x12 x2 wp1_prec_Seq_correct .
next
  case (If b c1 c2)
    
  show ?case apply(simp)
  apply(rule If2[where e="%s. if bval b s then \<down>\<^sub>t (c1, s) else \<down>\<^sub>t (c2, s)"]) 
    apply(simp_all  cong:rev_conj_cong)
    apply(rule conseq_old[where Q=Q and Q'=Q])
      prefer 2
      apply(rule If.IH(1)) apply(fact)
      apply(simp_all) apply(auto)[1]
    apply(rule conseq_old[where Q=Q and Q'=Q])
      prefer 2
      apply(rule If.IH(2)) apply(fact)
      apply(simp_all) apply(auto)[1]
      apply (blast intro: If_THE_True wp1_terminates If_THE_False) 
     done
 
next
  case (While b c)
 
      let ?y = "(new (wp\<^sub>1 (WHILE b DO c) Q))"
    have "finite (support (wp\<^sub>1 (WHILE b DO c) Q))"
      apply(rule finite_subset[OF support_wpt]) apply fact done
    then have "\<exists>x. x \<notin> support (wp\<^sub>1 (WHILE b DO c) Q)" using infinite_UNIV_listI
      using ex_new_if_finite by blast
    hence yQx: "?y \<notin> support (wp\<^sub>1 (WHILE b DO c) Q)" by (rule someI_ex)

  show ?case
  proof (rule conseq_old[OF _  hoare1.While], safe )
    show "\<exists>k>0. \<forall>l s. wp\<^sub>1 (WHILE b DO c) Q l s \<longrightarrow> wp\<^sub>1 (WHILE b DO c) Q l s \<and>  \<down>\<^sub>t (WHILE b DO c, s) \<le> k * \<down>\<^sub>t (WHILE b DO c, s)"
      apply auto done
  next
    fix l s
    assume "wp\<^sub>1 (WHILE b DO c) Q l s" "\<not> bval b s"
    then show "Q l s" by (simp add: wp1While)
  next
    fix l s
    assume "wp\<^sub>1 (WHILE b DO c) Q l s"
    from this[unfolded wp1_def] obtain t s' where t: "(WHILE b DO c, s) \<Rightarrow> t \<Down> s'" and "Q l s'" by blast
    then have r: "\<down>\<^sub>t (WHILE b DO c, s) = t" using Nielson_Hoare.bigstepT_the_cost by auto 
    assume "\<not> bval b s"
    with r t have   t2: "t=1" by auto 
    from r t2 show "1 \<le> \<down>\<^sub>t (WHILE b DO c, s)" by auto 
  next
    fix l s
    assume "wp\<^sub>1 (WHILE b DO c) Q l s"
    from this[unfolded wp1_def] obtain t s'' where t: "(WHILE b DO c, s) \<Rightarrow> t \<Down> s''" "Q l s''" by blast
    then have r: "\<down>\<^sub>t (WHILE b DO c, s) = t" using Nielson_Hoare.bigstepT_the_cost by auto 
    assume "bval b s" 
    with t obtain t1 t2 s' where 1: "(c,s) \<Rightarrow> t1 \<Down> s'" and 2: "(WHILE b DO c, s') \<Rightarrow> t2 \<Down> s''" and sum: "t=t1+t2+1" and "bval b s" by auto
    from 1 have A: "\<down>\<^sub>t (c,s) = t1" and s': "\<down>\<^sub>s (c,s) = s'" using Nielson_Hoare.bigstepT_the_cost bigstepT_the_state by auto
    from 2 s' have B: "\<down>\<^sub>t (WHILE b DO c, \<down>\<^sub>s(c,s)) = t2" using Nielson_Hoare.bigstepT_the_cost by auto

    show "1 + (%s. \<down>\<^sub>t (WHILE b DO c, \<down>\<^sub>s(c,s))) s  + (%s. \<down>\<^sub>t (c,s)) s \<le> \<down>\<^sub>t (WHILE b DO c, s)"
      apply(simp add: r A B sum) done
  next 
    
    
    show "\<turnstile>\<^sub>1 {\<lambda>l s. wp\<^sub>1 (WHILE b DO c) Q l s \<and> bval b s \<and> \<down>\<^sub>t (WHILE b DO c, \<down>\<^sub>s (c, s)) = l ?y} c
         { \<lambda>s. \<down>\<^sub>t (c, s) \<Down> \<lambda>l s. wp\<^sub>1 (WHILE b DO c) Q l s \<and> \<down>\<^sub>t (WHILE b DO c, s) \<le> l ?y}"
       apply(rule conseq_old[OF _ While(1), of _ "%l s. wp\<^sub>1 (WHILE b DO c) Q l s \<and> \<down>\<^sub>t (WHILE b DO c, s) = l ?y"])
        apply(rule exI[where x=1]) apply simp
      subgoal apply safe
        apply(subst (asm) wp1While) apply simp
      proof - fix l s
        assume 1: "wp\<^sub>1 c (wp\<^sub>1 (WHILE b DO c) Q) l s"
        assume 2: "\<down>\<^sub>t (WHILE b DO c, \<down>\<^sub>s (c, s)) = l ?y" 
        then have "l ?y = prec c (%s. \<down>\<^sub>t (WHILE b DO c, s)) s" unfolding prec_def by auto
        with 1 wp1_prec2[of c "(wp\<^sub>1 (WHILE b DO c) Q)" l s _ "(\<lambda>s. \<down>\<^sub>t (WHILE b DO c, s))"]
          show "wp\<^sub>1 c (\<lambda>l s. wp\<^sub>1 (WHILE b DO c) Q l s \<and>  \<down>\<^sub>t (WHILE b DO c, s) = l ?y) l s" by auto
        qed
        subgoal apply(rule finite_subset[OF support_and]) apply auto
           apply(rule finite_subset[OF support_wpt]) apply fact
             apply(rule finite_subset) apply(rule support_single)  by auto
        apply auto done 
    next
      assume "new (wp\<^sub>1 (WHILE b DO c) Q) \<in> support (wp\<^sub>1 (WHILE b DO c) Q)"
      with yQx show "False"  
        by blast
       
    qed
  qed

    
lemma valid_wp: "\<Turnstile>\<^sub>1 {P}c{p \<Down> Q} \<longleftrightarrow> (\<exists>k>0. (\<forall>l s. P l s \<longrightarrow> (wp\<^sub>1 c Q l s \<and> ((THE n. (\<exists> t. ((c,s) \<Rightarrow> n \<Down> t)))) \<le> k * p s)))"
  apply(rule)
   apply(auto simp: hoare1_valid_def wp1_def)    
  subgoal for k apply(rule exI[where x=k]) using bigstepT_the_cost by fast       
  subgoal for k apply(rule exI[where x=k]) using bigstepT_the_cost by fast
  done
    
    
theorem hoare1_complete: "finite (support Q) \<Longrightarrow> \<Turnstile>\<^sub>1 {P}c{p \<Down> Q} \<Longrightarrow> \<turnstile>\<^sub>1 {P}c{p \<Down> Q}"   
  apply(rule conseq_old[OF _ wp1_is_pre, where Q'=Q and Q=Q, simplified]) 
  by (auto simp: valid_wp)   
  
    
corollary hoare1_sound_complete: "finite (support Q) \<Longrightarrow> \<turnstile>\<^sub>1 {P}c{p \<Down> Q} \<longleftrightarrow> \<Turnstile>\<^sub>1 {P}c{p \<Down> Q}"
  by (metis hoare1_sound hoare1_complete)
    
end

