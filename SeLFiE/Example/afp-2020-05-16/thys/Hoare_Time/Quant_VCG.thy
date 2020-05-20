subsection "Verification Condition Generator"
theory Quant_VCG
imports Quant_Hoare
begin

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile qassn bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61)

notation com.SKIP ("SKIP")
  
fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"
  
fun pre :: "acom \<Rightarrow> qassn \<Rightarrow> qassn" where
"pre SKIP Q = (\<lambda>s. eSuc (Q s))" |
"pre (x ::= a) Q = (\<lambda>s. eSuc (Q (s[a/x])))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. eSuc (if bval b s then pre C\<^sub>1 Q s  else pre C\<^sub>2 Q s  ))" |
"pre ({I} WHILE b DO C) Q = (\<lambda>s. I s + 1)"
   
fun vc :: "acom \<Rightarrow> qassn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1 ;; C\<^sub>2) Q = ((vc C\<^sub>1 (pre C\<^sub>2 Q)) \<and> (vc C\<^sub>2 Q) )" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |  
"vc ({I} WHILE b DO C) Q =  ((\<forall>s. (pre C (\<lambda>s. I s + 1) s \<le> I s + \<up>(bval b s)) \<and> (Q s \<le> I s + \<up> (\<not> bval b s))) \<and> vc C (%s. I s + 1))"


subsubsection "Soundness of VCG"
  
lemma vc_sound: "vc C Q \<Longrightarrow>  \<turnstile>\<^sub>2 {pre C Q} strip C { Q }"
proof (induct C arbitrary: Q) 
  case (Aif b C1 C2)
  then have Aif1: "\<turnstile>\<^sub>2 {pre C1 Q} strip C1 {Q}" and Aif2: "\<turnstile>\<^sub>2 {pre C2 Q} strip C2 {Q}" by auto
    show ?case apply auto apply(rule hoare2.conseq)
      apply(rule hoare2.If[where P="%s. if bval b s then pre C1 Q s else pre C2 Q s" and Q="Q"])
    subgoal
      apply(rule hoare2.conseq)
        apply (fact Aif1)
      subgoal for s apply(cases "bval b s") by auto
      apply simp done
    subgoal 
      apply(rule hoare2.conseq)
        apply (fact Aif2)
      subgoal for s apply(cases "bval b s") by auto
      apply simp done
     apply auto
    done
next
  case (Awhile I b C)
  then have i: "(\<And>Q. vc C Q \<Longrightarrow> \<turnstile>\<^sub>2 {pre C Q} strip C {Q})"
   and ii: " \<forall>s. pre C (\<lambda>s. I s + 1) s \<le> I s + \<up> (bval b s) \<and> Q s \<le>  I s + \<up> (\<not> bval b s)" 
     and iii: "vc C (\<lambda>s. I s + 1)" by auto
     
  from i iii have  A: "\<turnstile>\<^sub>2 {pre C (\<lambda>s. I s + 1)} strip C {(\<lambda>s. I s + 1)}" by auto 
    
  have   "\<turnstile>\<^sub>2 {\<lambda>s. I s + 1} WHILE b DO strip C {Q}"
    apply(rule hoare2.conseq)
     apply(rule hoare2.While[where I=I])
      apply(rule hoare2.conseq)
        apply(rule A) using ii by auto
  then show ?case by auto      
qed (auto intro: hoare2.Skip hoare2.Assign hoare2.Seq )
  
  
lemma vc_sound': "\<lbrakk>vc C Q ; (\<forall>s. pre C Q s \<le> P s) \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>2 {P} strip C { Q }"
  apply(rule hoare2.conseq)
    apply(rule vc_sound) by auto

subsubsection "Completeness"
  
lemma pre_mono: assumes "\<And>s. P' s \<le> P s" 
  shows "\<And>s. pre C P' s \<le> pre C P s"
  using assms by (induct C arbitrary: P P', auto)    
    
    
lemma vc_mono: assumes "\<And>s. P' s \<le> P s" 
  shows "vc C P \<Longrightarrow> vc C P'"    
  using assms proof (induct C arbitrary: P P')  
  case (Awhile I b C)
  thus ?case 
    apply (auto simp: pre_mono) 
    using order.trans by blast   
qed (auto simp: pre_mono)
    
    
lemma "\<turnstile>\<^sub>2 { P } c { Q } \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. pre C Q s \<le> P s)"
  (is "_ \<Longrightarrow>   \<exists>C. ?G P c Q C")
proof (induction rule: hoare2.induct)
  case (Skip P)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by auto   
  qed
next
  case (Assign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" by simp qed
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 Q" 
    and pre1: "(\<And>s. pre C1 Q s \<le> P s + \<up> (bval b s))"  by blast
  from If(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 Q" 
    and pre2: "(\<And>s. pre C2 Q s \<le> P s + \<up> (\<not> bval b s))"  by blast
      
  show ?case
    apply(rule exI[where x="IF b THEN C1 ELSE C2"], safe)
    subgoal using strip1 strip2 by auto
    subgoal using vc1 vc2 by auto
    subgoal for s using pre1[of s] pre2[of s] by auto
    done
next
  case (Seq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)
  from Seq(3) obtain C1 where strip1: "strip C1 = c\<^sub>1" and vc1: "vc C1 P\<^sub>2"
    and pre1: "(\<forall>s. pre C1 P\<^sub>2 s \<le> P\<^sub>1 s)"  by blast
  from Seq(4) obtain C2 where strip2: "strip C2 = c\<^sub>2" and vc2: "vc C2 P\<^sub>3"
    and pre2: "(\<forall>s. pre C2 P\<^sub>3 s \<le> P\<^sub>2 s)"  by blast
  {
    fix s
    have "pre C1 (pre C2 P\<^sub>3) s \<le> P\<^sub>1 s" 
      apply(rule order.trans[where b="pre C1 P\<^sub>2 s"])
       apply(rule pre_mono) using pre2 apply simp using pre1 by simp
  } note pre = this
  show ?case
    apply(rule exI[where x="C1 ;; C2"], safe)
    subgoal using strip1 strip2 by simp
    subgoal using vc1 vc2 vc_mono pre2 by auto 
    subgoal using pre by auto 
    done      
next
  case (While I b c)
  from While(2) obtain C where strip: "strip C = c" and vc: "vc C (\<lambda>a. I a + 1)"
    and pre: "\<And>s. pre C (\<lambda>a. I a + 1) s \<le> I s + \<up> (bval b s)" by blast
  show ?case
    apply(rule exI[where x="{I} WHILE b DO C"], safe)
    subgoal using strip by simp
    subgoal using pre vc by auto
    subgoal by simp
  done
next
  case (conseq P c Q P' Q')
  then obtain C where "strip C = c" and vc: "vc C Q" and pre: "\<And>s. pre C Q s \<le> P s" by blast
   
  from pre_mono[OF conseq(3)] have 1: "\<And>s. pre C Q' s \<le> pre C Q s" by auto
    
  show ?case
    apply(rule exI[where x=C])
    apply safe
      apply fact
    subgoal using vc conseq(3) vc_mono by auto
    subgoal using pre conseq(2) 1 using order.trans  by metis
    done
qed
     
  
  
  
    
end