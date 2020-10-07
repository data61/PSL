theory SepLogK_VCG 
imports SepLogK_Hoare
begin
  
lemmas conseqS = conseq[where k=1, simplified]

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) | 
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile assn2 bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61) 
    
notation com.SKIP ("SKIP")
  
fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"  


fun pre :: "acom \<Rightarrow> assn2 \<Rightarrow> assn2" where
"pre SKIP Q = ($1 ** Q)" |
"pre (x ::= a) Q = ((\<lambda>(ps,t). x\<in>dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x\<mapsto>(paval a ps)),t) ) ** $1)" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (
   $1 **  (\<lambda>(ps,n). vars b \<subseteq> dom ps \<and> (if pbval b ps then pre C\<^sub>1 Q (ps,n)  else pre C\<^sub>2 Q (ps,n) )))" |
"pre ({I} WHILE b DO C) Q = (I ** $1)"  
  
  
fun vc :: "acom \<Rightarrow> assn2 \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1 ;; C\<^sub>2) Q = ((vc C\<^sub>1 (pre C\<^sub>2 Q)) \<and> (vc C\<^sub>2 Q) )" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |  
"vc ({I} WHILE b DO C) Q =  ( (\<forall>s. (I s \<longrightarrow> vars b \<subseteq> dom (fst s) ) \<and> ((\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b True s) s \<longrightarrow> pre C (I ** $ 1) s)
         \<and> ( (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b False s) s \<longrightarrow> Q s)) \<and> vc C (I  ** $ 1))" 

 
lemma dollar0_left: "($ 0 \<and>* Q) = Q"  
 apply rule unfolding dollar_def sep_conj_def  
  by force
  
lemma vc_sound: "vc C Q \<Longrightarrow>  \<turnstile>\<^sub>3\<^sub>' {pre C Q} strip C { Q }"
proof (induct C arbitrary: Q)
  case Askip
  then show ?case
    apply simp
    apply(rule conseqS[OF Frame[OF Skip]])
        by (auto simp: dollar0_left)  
next
  case (Aassign x1 x2)
  then show ?case 
    apply simp
    apply(rule conseqS)
      apply(rule Assign4)
      apply auto done
next
  case (Aseq C1 C2)
  then show ?case   apply (auto intro: Seq)  done
next
  case (Aif b C1 C2)
  then have Aif1: "\<turnstile>\<^sub>3\<^sub>' {pre C1 Q} strip C1 {Q}"
        and Aif2: "\<turnstile>\<^sub>3\<^sub>' {pre C2 Q} strip C2 {Q}"  by auto
  show ?case apply simp
    apply (rule conseqS) 
      apply(rule If[where P="%(ps,n).  (if pbval b ps then pre C1 Q (ps,n) else pre C2 Q (ps,n))" and Q="Q"])
    subgoal apply simp
      apply (rule conseqS) apply(fact Aif1) by auto 
    subgoal apply simp
      apply (rule conseqS) apply(fact Aif2) by auto 
     apply (auto simp: sep_conj_ac) 
    unfolding sep_conj_def by blast 
next
  case (Awhile I b C)
  then have
       dom : "\<And>s. (I s \<longrightarrow> vars b \<subseteq> dom (fst s) )"
      and i: "\<And>s.  (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b True s) s \<longrightarrow> pre C (I ** $ 1) s"
      and ii: "\<And>s.  (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b False s) s \<longrightarrow> Q s"
      and C: "\<turnstile>\<^sub>3\<^sub>' {pre C (I ** $ 1)} strip C {I ** $ 1}"
     by fastforce+
    
  show ?case
    apply simp 
    apply(rule conseqS)
       apply(rule While[where P=I])
       apply(rule conseqS)
        apply(rule C)
    subgoal using i by auto
    subgoal apply simp using dom unfolding sep_conj_def by force
    subgoal apply simp using dom unfolding sep_conj_def by force
    subgoal using ii apply auto done
    done
qed  
  
lemma vc2valid: "vc C Q \<Longrightarrow> \<forall>s. P s \<longrightarrow> pre C Q s \<Longrightarrow> \<Turnstile>\<^sub>3\<^sub>' {P} strip C { Q}"
  using hoareT_sound2_part weakenpre vc_sound by metis

lemma pre_mono: assumes "\<forall>s. P s \<longrightarrow> Q s" shows "\<And>s. pre C P s \<Longrightarrow> pre C Q s"   
using assms proof(induct C arbitrary: P Q)
  case Askip
  then show ?case  apply (auto simp: sep_conj_def dollar_def)
    by force
next
  case (Aassign x1 x2)
  then show ?case by (auto simp: sep_conj_def dollar_def)
next
  case (Aseq C1 C2)
  then show ?case by auto
next
  case (Aif b C1 C2)
  then show ?case apply (auto simp: sep_conj_def dollar_def) 
    subgoal for ps n
      apply(rule exI[where x=0]) 
      apply(rule exI[where x=1])
      apply(rule exI[where x=ps]) by auto
    done
next
  case (Awhile x1 x2 C)
  then show ?case by auto
qed
  
lemma vc_mono: assumes "\<forall>s. P s \<longrightarrow> Q s" shows "vc C P \<Longrightarrow> vc C Q"        
using assms proof(induct C arbitrary: P Q)
  case Askip
  then show ?case by auto
next
  case (Aassign x1 x2)
  then show ?case  by auto
next
  case (Aseq C1 C2 P Q)
  then have i: "vc C1 (pre C2 P)" and ii: "vc C2 P" by auto
  from  pre_mono[OF ] Aseq(4) have iii: "\<forall>s. pre C2 P s \<longrightarrow> pre C2 Q s" by blast
  show ?case  apply auto
      using Aseq(1)[OF i  iii] Aseq(2)[OF ii Aseq(4)] by auto
next
  case (Aif x1 C1 C2)
  then show ?case  by auto
next
  case (Awhile I b C P Q)
  then show ?case by auto
qed


lemma vc_sound': "vc C Q \<Longrightarrow> (\<And>s n. P' (s, n) \<Longrightarrow> pre C Q (s, k * n)) \<Longrightarrow> (\<And>s n. Q (s, n) \<Longrightarrow> Q' (s, n div k)) \<Longrightarrow> 0 < k \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' {P'} strip C { Q'}"
  using conseq vc_mono vc_sound by metis


  
  
        
lemma pre_Frame: "(\<forall>s. P s \<longrightarrow> pre C Q s) \<Longrightarrow> vc C Q
     \<Longrightarrow> (\<exists>C'. strip C = strip C' \<and>  vc C' (Q ** F) \<and> (\<forall>s. (P ** F) s \<longrightarrow> pre C' (Q ** F) s) )"  
proof (induct C arbitrary: P Q)
  case Askip
  show ?case 
  proof (rule exI[where x="Askip"], safe)
    fix a b
    assume "(P \<and>* F) (a, b)"
    then obtain ps1 ps2 n1 n2 where A: "ps1##ps2" "a=ps1+ps2" "b=n1+n2"
      and P: "P (ps1,n1)" and F: "F (ps2,n2)" unfolding sep_conj_def by auto
    from P Askip have p: "($ (Suc 0) \<and>* Q) (ps1, n1)" by auto
    
    from p A F
    have "(($ (Suc 0) \<and>* Q) \<and>* F) (a, b)"
      apply(subst (2) sep_conj_def) by auto
    then show "pre SKIP (Q \<and>* F) (a, b)" by (simp add: sep_conj_ac)
  qed simp
next
  case (Aassign x a)
  show ?case 
  proof (rule exI[where x="Aassign x a"], safe)
    fix ps n
    assume "(P \<and>* F) (ps,n)"
    then obtain ps1 ps2 n1 n2 where o: "ps1##ps2" "ps=ps1+ps2" "n=n1+n2"
      and P: "P (ps1,n1)" and F: "F (ps2,n2)" unfolding sep_conj_def by auto
    from P Aassign(1) have z: "((\<lambda>(ps, t). x \<in> dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x \<mapsto> paval a ps), t))
                                     \<and>* $ (Suc 0)) (ps1, n1)" 
        by auto    
    with o F show " pre (x ::= a) (Q \<and>* F) (ps,n)" apply auto
      unfolding sep_conj_def dollar_def apply (auto)
        subgoal by(simp add: plus_fun_def)  
        subgoal by(auto simp add: plus_fun_def)  
        subgoal
          by (smt add_update_distrib dom_fun_upd domain_conv insert_dom option.simps(3) paval_extend sep_disj_fun_def)
        done
  qed auto
next
  case (Aseq C1 C2) 
  from Aseq(3) have pre: "\<forall>s. P s \<longrightarrow> pre C1 (pre C2 Q) s" by auto
  from Aseq(4) have vc1: "vc C1 (pre C2 Q)" and vc2: "vc C2 Q" by auto
  from Aseq(1)[OF pre vc1] obtain C1' where S1: "strip C1 = strip C1'"
      and vc1': "vc C1' (pre C2 Q \<and>* F)"
      and I1: "(\<forall>s. (P \<and>* F) s \<longrightarrow> pre C1' (pre C2 Q \<and>* F) s)" by blast
  from Aseq(2)[of "pre C2 Q" Q, OF _ vc2] obtain C2' where S2: "strip C2 = strip C2'"
      and vc2': "vc C2' (Q \<and>* F)"
      and I2: "(\<forall>s. (pre C2 Q \<and>* F) s \<longrightarrow> pre C2' (Q \<and>* F) s) " by blast
   
  show ?case apply(rule exI[where x="Aseq C1' C2'"])    
    apply safe
    subgoal using S1 S2 by auto
    subgoal apply simp apply safe
      subgoal using vc_mono[OF I2 vc1'] .
      subgoal by (fact vc2')
    done
    subgoal using I1 I2 pre_mono
      by force 
    done
next
  case (Aif b C1 C2)
  from Aif(3) have i: "\<forall>s. P s \<longrightarrow>
          ($ (Suc 0) \<and>*
           (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then pre C1 Q (ps, n) else pre C2 Q (ps, n))))
           s" by simp  
  from Aif(4) have vc1: "vc C1 Q" and vc2: "vc C2 Q" by auto 
  from Aif(1)[where P="pre C1 Q" and Q="Q", OF _ vc1] obtain C1' where
    s1: "strip C1 = strip C1'" and v1: "vc C1' (Q \<and>* F)"
    and p1: "(\<forall>s. (pre C1 Q \<and>* F) s \<longrightarrow> pre C1' (Q \<and>* F) s)"
    by auto
  from Aif(2)[where P="pre C2 Q" and Q="Q", OF _ vc2] obtain C2' where
    s2: "strip C2 = strip C2'" and v2: "vc C2' (Q \<and>* F)" 
    and p2: "(\<forall>s. (pre C2 Q \<and>* F) s \<longrightarrow> pre C2' (Q \<and>* F) s)"
    by auto
    
  show ?case apply(rule exI[where x="Aif b C1' C2'"])
  proof safe
    fix ps n
    assume "(P \<and>* F) (ps, n)"
    then obtain ps1 ps2 n1 n2 where o: "ps1##ps2" "ps=ps1+ps2" "n=n1+n2"
      and P: "P (ps1,n1)" and F: "F (ps2,n2)" unfolding sep_conj_def by auto
    from P i have P': "($ (Suc 0) \<and>*
         (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then pre C1 Q (ps, n) else pre C2 Q (ps, n))))
         (ps1,n1)" by auto
    have PF: "(($ (Suc 0) \<and>*
         (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then pre C1 Q (ps, n) else pre C2 Q (ps, n)))) ** F)
         (ps,n)" apply(subst (2) sep_conj_def)
        apply(rule exI[where x="(ps1,n1)"])
        apply(rule exI[where x="(ps2,n2)"])
      using F P' o by auto 
    from this[simplified sep_conj_assoc] obtain ps1 ps2 n1 n2 where o: "ps1##ps2" "ps=ps1+ps2" "n=n1+n2"
      and P: "($ (Suc 0)) (ps1,n1)" and F: "((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then pre C1 Q (ps, n) else pre C2 Q (ps, n))) \<and>* F) (ps2,n2)"
      unfolding sep_conj_def apply auto by fast
    then have "((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then (pre C1 Q  \<and>* F) (ps, n) else (pre C2 Q  \<and>* F) (ps, n)))) (ps2,n2)"    
      unfolding sep_conj_def apply auto
      apply (metis contra_subsetD domD map_add_dom_app_simps(1) plus_fun_conv sep_add_commute)
      using pbval_extend apply auto[1]                                                     
      apply (metis contra_subsetD domD map_add_dom_app_simps(1) plus_fun_conv sep_add_commute) 
      using pbval_extend apply auto[1]    done
    then have "((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then (pre C1' (Q \<and>* F)) (ps, n) else (pre C2' (Q \<and>* F)) (ps, n)))) (ps2,n2)" 
      using p1 p2  by auto
    with o P 
    show "pre (IF b THEN C1' ELSE C2') (Q \<and>* F) (ps, n)"
      apply auto apply(subst sep_conj_def) by force
  qed (auto simp: s1 s2 v1 v2)
next
  case (Awhile I b C)
  from Awhile(2) have pre: "\<forall>s. P s \<longrightarrow>  (I ** $1) s"  by auto
  from Awhile(3) have 
    dom:  "\<forall>ps n. I (ps, n) \<longrightarrow> vars b \<subseteq> dom ps" 
  and  tB: "\<forall>s. I s \<and> vars b \<subseteq> dom (fst s) \<and> pbval b (fst s) \<longrightarrow> pre C (I \<and>* $ (Suc 0)) s"
  and  fB: "\<forall>ps n. I (ps, n) \<and> vars b \<subseteq> dom ps \<and> \<not> pbval b ps \<longrightarrow> Q (ps, n)"
  and vcB: "vc C (I \<and>* $(Suc 0))" by auto
  from Awhile(1)[OF tB vcB] obtain C' where st: "strip C = strip C'"
    and vc': "vc C' ((I \<and>* $ (Suc 0)) \<and>* F)"
    and pre': "(\<forall>s. ((\<lambda>a. I a \<and> vars b \<subseteq> dom (fst a) \<and> pbval b (fst a)) \<and>* F) s \<longrightarrow>
            pre C' ((I \<and>* $ (Suc 0)) \<and>* F) s)"
    by auto
  show ?case apply(rule exI[where x="Awhile (I**F) b C'"])
    apply safe
    subgoal using st by simp 
    subgoal apply simp apply safe
        subgoal using dom unfolding sep_conj_def apply auto
          by (metis domD sep_substate_disj_add subState subsetCE) 
        subgoal  using pre' apply(auto simp: sep_conj_ac) 
            apply(subst (asm)  sep_conj_def)
            apply(subst (asm)  sep_conj_def) apply auto
          by (metis dom pbval_extend sep_add_commute sep_disj_commuteI)
        subgoal using fB unfolding sep_conj_def apply auto
          using dom pbval_extend by fastforce
        subgoal using vc' apply(auto simp: sep_conj_ac) done
        done
      subgoal apply simp using pre unfolding sep_conj_def apply auto
        by (smt semiring_normalization_rules(23) sep_add_assoc sep_add_commute sep_add_disjD sep_add_disjI1)
      done
qed

  
  
        
        
        
lemma vc_complete: "\<turnstile>\<^sub>3\<^sub>a {P} c { Q } \<Longrightarrow> (\<exists>C. vc C Q \<and> (\<forall>s. P s \<longrightarrow> pre C Q s) \<and> strip C = c)"
proof(induct   rule: hoare3a.induct)
  case Skip
  then show ?case apply(rule exI[where x="Askip"]) by auto
next
  case (Assign4 x a Q)
  then show ?case apply(rule exI[where x="Aassign x a"]) by auto
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(2) obtain C1 where A1: "vc C1 Q" "strip C1 = c\<^sub>1" and 
    A2: "\<And>ps n. (P (ps, n) \<and> lmaps_to_axpr b True ps) \<longrightarrow> pre C1 Q (ps,n)"
    by blast
  from If(4) obtain C2 where B1: "vc C2 Q" "strip C2 = c\<^sub>2" and B2:
    "\<And>ps n. (P (ps, n) \<and> lmaps_to_axpr b False ps) \<longrightarrow> pre C2 Q (ps,n)"
    by blast
      
  show ?case apply(rule exI[where x="Aif b C1 C2"]) using A1 B1 apply auto
    subgoal for ps n
      unfolding sep_conj_def dollar_def apply auto
      apply(rule exI[where x="0"])
      apply(rule exI[where x="1"])
      apply(rule exI[where x="ps"])
      using A2 B2 by auto
  done
next
  case (Frame P C Q F) 
  then obtain C' where vc: "vc C' Q" and pre: "(\<forall>s. P s \<longrightarrow> pre C' Q s)"
      and strip: "strip C' = C" by auto 
  show ?case using pre_Frame[OF pre vc] strip by metis
next
  case (Seq P c\<^sub>1 Q c\<^sub>2 R)
  from Seq(2) obtain C1 where A1: "vc C1 Q" "strip C1 = c\<^sub>1" and 
    A2: "\<And>s. P s \<longrightarrow> pre C1 Q s"
    by blast
  from Seq(4) obtain C2 where B1: "vc C2 R" "strip C2 = c\<^sub>2" and 
    B2: "\<And>s. Q s \<longrightarrow> pre C2 R s"
    by blast
  show ?case apply(rule exI[where x="Aseq C1 C2"])
    using B1 A1 apply auto
    subgoal using vc_mono B2 by auto
    subgoal apply(rule pre_mono[where P=Q])  using  B2 apply auto
      using A2 by auto
    done
next
  case (While I b c)
  then obtain C where 1: "vc C ((\<lambda>(s, n). I (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1)"
          "strip C = c" and 2:
         "\<And>ps n. (I (ps, n) \<and> lmaps_to_axpr b True ps) \<longrightarrow>
              pre C ((\<lambda>(s, n). I (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps,n) " by blast
    
  show ?case apply(rule exI[where x="Awhile (\<lambda>(s, n). I (s, n) \<and> vars b \<subseteq> dom s) b C"])
    using 1 2 by auto 
next
  case (conseqS P c Q P' Q')
  then obtain C' where C': "vc C' Q" "(\<forall>s. P s \<longrightarrow> pre C' Q s)" "strip C' = c"
    by blast
  show ?case apply(rule exI[where x=C'])
      using C' conseqS(3,4) pre_mono vc_mono by force
qed 
           
   
  
  
theorem vc_completeness:
  assumes "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q}"
  shows "\<exists>C k. vc C (Q ** sep_true)
          \<and> (\<forall>ps n. P (ps, n) \<longrightarrow> pre C (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (ps, k * n))
          \<and> strip C = c"
proof - 
  let ?QG = "\<lambda>k (ps,n). (Q ** sep_true) (ps,n div k)"
  from assms obtain k where k[simp]: "k>0" and p: "\<And>ps n. P (ps, n) \<Longrightarrow> wp\<^sub>3\<^sub>' c (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (ps, k * n)" 
    using valid_wp by blast 
      
  from wpT_is_pre  have R: "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' c (?QG k)} c {?QG k}" by auto
  
  have z: "(\<forall>s. (\<lambda>(ps, n). (Q \<and>* (\<lambda>s. True)) (ps, n div k)) s) \<Longrightarrow> (\<forall>s. (\<lambda>(ps, n). (Q \<and>* (\<lambda>s. True)) (ps, n)) s)"
    by (metis (no_types) case_prod_conv k neq0_conv nonzero_mult_div_cancel_left old.prod.exhaust)
  
     
  have z: "\<And>ps n. ((Q \<and>* (\<lambda>s. True)) (ps, n div k) \<Longrightarrow> (Q \<and>* (\<lambda>s. True)) (ps, n))"   
  proof -
    fix ps n
    assume "(Q \<and>* (\<lambda>s. True)) (ps, n div k) "
    then guess ps1 n1 ps2 n2 unfolding sep_conj_def by auto
    note o = this
    from o(4) have nn1: "n\<ge>n1" using k
      by (metis (full_types) add_leE div_le_dividend) 
    show "(Q \<and>* (\<lambda>s. True)) (ps, n)" unfolding sep_conj_def
        apply(rule exI[where x="(ps1, n1)"])
      apply(rule exI[where x="(ps2, n - n1)"])
      using o nn1 by auto   
  qed
  then have z': "\<forall>s. ((Q \<and>* (\<lambda>s. True)) (fst s, (snd s) div k) \<longrightarrow> (Q \<and>* (\<lambda>s. True)) s)"
    by (metis prod.collapse)   
      
  from vc_complete[OF R]   guess C by auto
  note o = this
    
  have y: "\<And>ps n. P (ps, n) \<Longrightarrow>  pre C (\<lambda>(ps, n). (Q \<and>* (\<lambda>s. True)) (ps, n div k)) (ps, k * n)"
    using o p by metis 
    
  show ?thesis apply(rule exI[where x=C])  apply(rule exI[where x=k])
    apply safe
    subgoal apply(rule vc_mono[OF _ o(1)]) using z  by blast
    subgoal using y by blast
    subgoal using o by simp
    done
qed

end