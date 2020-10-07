subsection "Verification Condition Generator"
theory QuantK_VCG
imports QuantK_Hoare
begin

subsubsection "Ceiling integer division on extended natural numbers"

definition "mydiv (a::nat) (k::nat) = (if k dvd a then a div k else (a div k) + 1)"
   
lemma mydivcode: "k>0 \<Longrightarrow> D\<ge>k \<Longrightarrow> mydiv D k = Suc (mydiv (D-k) k)"  
  unfolding mydiv_def apply (auto simp add: le_div_geq)
  using dvd_minus_self by auto 
    
lemma mydivcode1: "mydiv 0 k = 0"  
  unfolding mydiv_def by auto 
    
lemma mydivcode2: "k>0 \<Longrightarrow> 0<D \<Longrightarrow> D<k \<Longrightarrow> mydiv D k = Suc 0"  
  unfolding mydiv_def by auto
    
lemma mydiv_mono: "a\<le>b \<Longrightarrow> mydiv a k \<le> mydiv b k" unfolding mydiv_def
  apply(cases "k dvd a")
  subgoal apply(cases "k dvd b")  apply auto apply (auto simp add: div_le_mono)
    using div_le_mono le_Suc_eq by blast  
  subgoal apply(cases "k dvd b")  apply auto apply (auto simp add: div_le_mono)
    by (metis Suc_leI add.right_neutral div_le_mono div_mult_mod_eq dvd_imp_mod_0 le_add1 le_antisym less_le) 
     done
      
lemma mydiv_cancel: "0 < k \<Longrightarrow> mydiv (k * i) k = i"    
  unfolding mydiv_def by auto 
    
lemma assumes k: "k>0" and B: "B \<le> k*A"
  shows mydiv_le_E: "mydiv B k \<le> A"
proof - 
  from mydiv_mono[OF B] and k mydiv_cancel show ?thesis 
    by metis
qed
lemma mydiv_mult_leq: "0 < k \<Longrightarrow> l\<le>k \<Longrightarrow> mydiv (l*A) k \<le> A"
  by(simp add: mydiv_le_E)
   
lemma mydiv_cancel3: "0 < k \<Longrightarrow> i \<le> k * mydiv i k"
  by (auto simp add: mydiv_def dividend_less_times_div le_eq_less_or_eq)  
                                                                                                    
definition "ediv a k = (if a=\<infinity> then \<infinity> else enat (mydiv (THE i. a=enat i) k))"  
  
lemma ediv_enat[simp]: "ediv (enat a) k = enat (mydiv a k)"
  unfolding ediv_def by auto
lemma ediv_mydiv[simp]: "ediv (enat a) k \<le> enat f \<longleftrightarrow> mydiv a k \<le> f"
  unfolding ediv_def by auto
  
lemma ediv_mono: "a\<le>b \<Longrightarrow> ediv a k \<le> ediv b k"
  unfolding ediv_def by (auto simp add: mydiv_mono) 

lemma ediv_cancel2: "k>0 \<Longrightarrow> ediv (enat k * x) k = x"
  unfolding ediv_def apply(cases "x=\<infinity>") using mydiv_cancel by auto
        
lemma ediv_cancel3: "k>0 \<Longrightarrow> A \<le> enat k * ediv A k"
  unfolding ediv_def apply(cases "A=\<infinity>") using mydiv_cancel3 by auto 

subsubsection "Definition of VCG"    
  
datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) | 
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile qassn bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61)
 |  Abst nat acom  ("({_}/ Ab _)"  [0, 61] 61)

notation com.SKIP ("SKIP")
  
fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)" |
"strip ({_} Ab C) = strip C"
    
fun pre :: "acom \<Rightarrow> qassn \<Rightarrow> qassn" where
"pre SKIP Q = (\<lambda>s. eSuc (Q s))" |
"pre (x ::= a) Q = (\<lambda>s. eSuc (Q (s[a/x])))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. eSuc (if bval b s then pre C\<^sub>1 Q s  else pre C\<^sub>2 Q s  ))" |
"pre ({P} WHILE b DO C) Q = (%s. P s + 1)" |
"pre ({k} Ab C) Q = (\<lambda>s. ediv (pre C (\<lambda>s. k*Q s) s) k)"
  
text \<open>In contrast to @{term pre}, @{term vc} produces a formula that is independent of the state:\<close>
  
fun vc :: "acom \<Rightarrow> qassn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1 ;; C\<^sub>2) Q = ((vc C\<^sub>1 (pre C\<^sub>2 Q)) \<and> (vc C\<^sub>2 Q) )" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |  
"vc ({I} WHILE b DO C) Q =  ( (\<forall>s.  (pre C (\<lambda>s. I s + 1) s \<le> I s + \<up>(bval b s)) \<and> ( Q s \<le> I s + \<up> (\<not> bval b s))) \<and> vc C (%s. I s + 1))" |
"vc ({k} Ab C) Q = (vc C (\<lambda>s. enat k* Q s) \<and> k>0 \<^cancel>\<open>\<and> (\<forall>s. pre C (\<lambda>s. enat k * Q s) s \<le> enat k * ediv (pre C (\<lambda>s. enat k * Q s) s) k)\<close>)"

subsubsection "Soundness of VCG"
  
lemma vc_sound: "vc C Q \<Longrightarrow>  \<turnstile>\<^sub>2\<^sub>' {pre C Q} strip C { Q }"
proof (induct C arbitrary: Q) 
  case (Aif b C1 C2)
  then have Aif1: "\<turnstile>\<^sub>2\<^sub>' {pre C1 Q} strip C1 {Q}" and Aif2: "\<turnstile>\<^sub>2\<^sub>' {pre C2 Q} strip C2 {Q}" by auto
    show ?case apply auto apply(rule hoareQ.conseq[where k=1])
      apply(rule hoareQ.If[where P="%s. if bval b s then pre C1 Q s else pre C2 Q s" and Q="Q"])
    subgoal
      apply(rule hoareQ.conseq[where k=1])
         apply (fact Aif1)
      subgoal for s apply(cases "bval b s") by auto
      apply auto done
    subgoal 
      apply(rule hoareQ.conseq[where k=1])
        apply (fact Aif2)
      subgoal for s apply(cases "bval b s") by auto
      apply auto done
     apply auto
    done
next
  case (Awhile I b C)
  then have i: "(\<And>Q. vc C Q \<Longrightarrow> \<turnstile>\<^sub>2\<^sub>' {pre C Q} strip C {Q})"
   and ii': " \<forall>s. pre C (\<lambda>s. I s + 1) s \<le> I s + \<up> (bval b s)" 
   and ii'': "\<And>s. Q s \<le>  I s + \<up> (\<not> bval b s)" 
     and iii: "vc C (\<lambda>s. I s + 1)"
    by auto

  from i iii have  A: "\<turnstile>\<^sub>2\<^sub>' {pre C (\<lambda>s. I s + 1)} strip C {(\<lambda>s. I s + 1)}" by auto 
     
  show ?case
    apply simp
    apply(rule conseq[where k=1])
       apply(rule While[where I=I])
       apply(rule weakenpre)
        apply(rule A)
      apply(rule ii') apply simp
    using ii'' apply auto done  
next
  case (Abst k C)
  then have vc: "vc C (\<lambda>s. k* Q s)" and k: "k>0" by auto
  from Abst(1) vc have C: "\<turnstile>\<^sub>2\<^sub>' {pre C (%s. k*Q s)} strip C {(%s. k*Q s)}" by auto
  show ?case apply(simp)
    apply(rule conseq)
       apply(rule C) using k apply auto
      using ediv_cancel3 by auto
qed (auto intro: hoareQ.Skip hoareQ.Assign hoareQ.Seq )


lemma vc_sound': "\<lbrakk>vc C Q ; (\<forall>s. pre C Q s \<le> P s) \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>2\<^sub>' {P} strip C { Q }"
  apply(rule hoareQ.conseq[where k=1])
    apply(rule vc_sound) by auto


lemma vc_sound'': "\<lbrakk>vc C Q' ; (\<forall>s.  pre C Q' s \<le> k * P s)  ; (\<And>s. enat k * Q s \<le> Q' s); k>0 \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>2\<^sub>' {P} strip C { Q }"
  apply(rule hoareQ.conseq )
    apply(rule vc_sound) by auto

  
subsubsection "Completeness" 
  
lemma pre_mono: assumes "\<And>s. P' s \<le> P s" 
  shows "\<And>s. pre C P' s \<le> pre C P s"
  using assms by (induct C arbitrary: P P', auto simp: ediv_mono mult_left_mono )    
      
lemma vc_mono: assumes "\<And>s. P' s \<le> P s" 
  shows "vc C P \<Longrightarrow> vc C P'"    
  using assms
proof (induct C arbitrary: P P') 
  case (Awhile I b C Q)
  thus ?case 
    apply (auto simp: pre_mono) 
    using order.trans by blast  
next
  case (Abst x1 C)
  then show ?case by (auto simp: mult_left_mono)  
qed (auto simp: pre_mono)
      
    
lemma "\<turnstile>\<^sub>2\<^sub>' { P } c { Q } \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. pre C Q s \<le> P s)"
  (is "_ \<Longrightarrow>   \<exists>C. ?G P c Q C")
proof (induction rule: hoareQ.induct)
  case (conseq P c Q k P' Q')
  then obtain C where strip: "strip C = c" and vc: "vc C Q" and pre: "\<And>s. pre C Q s \<le> P s"
    by blast
  
  { fix s
    have "pre C (\<lambda>s. enat k * Q' s) s \<le> pre C Q s" using pre_mono conseq(3) by simp 
    also 
    from pre conseq(2) have "\<dots>  \<le> enat k * P' s" using order.trans by blast
    finally have  "pre C (\<lambda>s. enat k * Q' s) s  \<le> enat k * P' s" by auto
        then have  "ediv (pre C (\<lambda>s. enat k * Q' s) s) k  \<le> ediv (enat k * P' s) k" using ediv_mono by auto
    moreover note  ediv_cancel2[OF conseq(4)]
    ultimately have "ediv (pre C (\<lambda>s. enat k * Q' s) s) k \<le> P' s"    
      by simp
  } note compensate=this
  
  show ?case
    apply(rule exI[where x="{k} Ab C"])
    apply(safe)
    subgoal using strip by simp
    subgoal apply simp apply safe
      subgoal using vc vc_mono conseq(3) by force
      subgoal by fact
      done
    subgoal apply simp using compensate by auto
        done
next
  case (Skip P)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by auto  qed
next
  case (Assign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" by auto  qed
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 Q"
        and pre1: "(\<And>s. pre C1 Q s \<le> (P s + \<up>(bval b s)))"
         by blast
  from If(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 Q"
        and pre2: "(\<And>s. pre C2 (\<lambda>s. Q s) s \<le> (P s + \<up>(\<not> bval b s)))"
    by blast

  show ?case
    apply(rule exI[where x="IF b THEN C1 ELSE C2"], safe)
    subgoal using strip1 strip2 by auto
    subgoal  using vc1 vc2 by auto 
    subgoal for s using pre1[of s] pre2[of s] by auto  
    done      
next
  case (Seq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)
  from Seq(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 P\<^sub>2"
      and pre1: "(\<forall>s. pre C1 P\<^sub>2 s \<le>   P\<^sub>1 s)"    by blast
  from Seq(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 P\<^sub>3"
      and pre2: "\<And>s. pre C2 P\<^sub>3 s \<le>   P\<^sub>2 s"   by blast
       
  {
    fix s
    have "pre C1 (pre C2 P\<^sub>3) s \<le> P\<^sub>1 s" 
      apply(rule order.trans[where b="pre C1 P\<^sub>2 s"])
       apply(rule pre_mono) using pre2 apply simp using pre1 by simp
  } note pre = this
  show ?case
    apply(rule exI[where x="C1 ;; C2"], safe)
    subgoal using strip1 strip2 by simp
    subgoal apply simp apply safe  using vc1 vc2 vc_mono pre2 by auto 
    subgoal    apply simp using  pre by auto  
      done 
next
  case (While I b c)
  from While(2) obtain C where strip: "strip C = c" and vc: "vc C (\<lambda>a. I a + 1)"
    and pre: "\<And>s. pre C (\<lambda>a. I a + 1) s \<le> I s + \<up> (bval b s)" by blast
  show ?case 
    apply(rule exI[where x="{I} WHILE b DO C"], safe)
    subgoal using strip by simp
    subgoal apply simp using pre vc by auto
    subgoal by simp
  done
qed
    
lemma "\<turnstile>\<^sub>Z { P } c { Q } \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. pre C Q s \<le> P s)"
  (is "_ \<Longrightarrow>   \<exists>C. ?G P c Q C")
proof (induction rule: hoareQ'.induct)
  case (ZSkip P)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by auto   
  qed
next
  case (ZAssign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" by simp qed
next
  case (ZIf P b c\<^sub>1 Q c\<^sub>2)
  from ZIf(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 Q" and pre1: "(\<And>s. pre C1 Q s \<le> P s + \<up> (bval b s))"  by blast
  from ZIf(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 Q" and pre2: "(\<And>s. pre C2 Q s \<le> P s + \<up> (\<not> bval b s))"  by blast
      
  show ?case apply(rule exI[where x="IF b THEN C1 ELSE C2"])
    apply(safe)
    subgoal using strip1 strip2 by auto
    subgoal using vc1 vc2 by auto
    subgoal for s apply auto 
        subgoal using pre1[of s] by auto 
        subgoal using pre2[of s] by auto 
        done
      done
next
  case (ZSeq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)
  from ZSeq(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 P\<^sub>2" and pre1: "(\<forall>s. pre C1 P\<^sub>2 s \<le> P\<^sub>1 s)"  by blast
  from ZSeq(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 P\<^sub>3" and pre2: "(\<forall>s. pre C2 P\<^sub>3 s \<le> P\<^sub>2 s)"  by blast
  {
    fix s
    have "pre C1 (pre C2 P\<^sub>3) s \<le> P\<^sub>1 s" 
      apply(rule order.trans[where b="pre C1 P\<^sub>2 s"])
       apply(rule pre_mono) using pre2 apply simp using pre1 by simp
  } note pre = this
  show ?case apply(rule exI[where x="C1 ;; C2"])
    apply safe
    subgoal using strip1 strip2 by simp
    subgoal using vc1 vc2 vc_mono pre2 by auto 
    subgoal using pre by auto 
    done      
next
  case (ZWhile I b c)
  from ZWhile(2) obtain C where strip: "strip C = c" and vc: "vc C (\<lambda>a. I a + 1)"
    and pre: "\<And>s. pre C (\<lambda>a. I a + 1) s \<le> I s + \<up> (bval b s)" by blast
  show ?case apply(rule exI[where x="{I} WHILE b DO C"])
    apply safe
    subgoal using strip by simp
    subgoal using pre vc by auto
    subgoal by simp
  done
next
  case (Zconseq' P c Q P' Q')
  then obtain C where "strip C = c" and vc: "vc C Q" and pre: "\<And>s. pre C Q s \<le> P s" by blast
   
  from pre_mono[OF Zconseq'(3)] have 1: "\<And>s. pre C Q' s \<le> pre C Q s" by auto
    
  show ?case
    apply(rule exI[where x=C])
    apply safe
      apply fact
    subgoal using vc Zconseq'(3) vc_mono by auto
    subgoal using pre Zconseq'(2) 1 using order.trans  by metis
    done
next
  case (Zconst k P c Q)
  then obtain C where strip: "strip C = c" and vc: "vc C (\<lambda>a. enat k * Q a)" 
    and k: "k>0" and pre: "\<And>s. pre C (\<lambda>a. enat k * Q a) s \<le> enat k * P s" by blast
  show ?case
    apply(rule exI[where x="{k} Ab C"]) apply safe
    subgoal using strip by auto
    subgoal using vc k by auto
    subgoal apply auto using ediv_mono[OF pre] ediv_cancel2[OF k] by metis
    done
qed
  
    
end