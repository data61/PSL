(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Inv3 imports DiskPaxos_Inv2  begin

subsection \<open>Invariant 3\<close>

text \<open>
  This invariant says that if two processes have read each other's block 
  from disk $d$ during their current phases, then at least one of them 
  has read the other's current block.
\<close>

definition HInv3_L :: "state \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
where
  "HInv3_L s p q d =  (phase s p \<in> {1,2}
                     \<and> phase s q \<in> {1,2}      
                     \<and> hasRead s p d q
                     \<and> hasRead s q d p)"

definition HInv3_R :: "state \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
where
  "HInv3_R s p q d =  (\<lparr>block= dblock s q, proc= q\<rparr> \<in> blocksRead s p d
                     \<or> \<lparr>block= dblock s p, proc= p\<rparr> \<in> blocksRead s q d)"

definition HInv3_inner :: "state \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
  where "HInv3_inner s p q d = (HInv3_L s p q d \<longrightarrow> HInv3_R s p q d)"

definition HInv3 :: "state \<Rightarrow> bool"
  where "HInv3 s = (\<forall>p q d. HInv3_inner s p q d)"

subsubsection\<open>Proofs of Invariant 3\<close>

theorem HInit_HInv3: "HInit s \<Longrightarrow> HInv3 s"
  by(simp add: HInit_def Init_def HInv3_def 
               HInv3_inner_def HInv3_L_def HInv3_R_def)

lemma InitPhase_HInv3_p: 
  "\<lbrakk> InitializePhase s s' p; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: InitializePhase_def HInv3_inner_def 
                    hasRead_def HInv3_L_def HInv3_R_def)

lemma InitPhase_HInv3_q: 
  "\<lbrakk> InitializePhase s s' q ; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: InitializePhase_def HInv3_inner_def 
                    hasRead_def HInv3_L_def HInv3_R_def)

lemma HInv3_L_sym: "HInv3_L s p q d \<Longrightarrow> HInv3_L s q p d"
  by(auto simp add: HInv3_L_def)

lemma HInv3_R_sym: "HInv3_R s p q d \<Longrightarrow> HInv3_R s q p d"
  by(auto simp add: HInv3_R_def)

lemma Phase1or2ReadThen_HInv3_pq: 
  assumes act:  "Phase1or2ReadThen s s' p d q"
  and  inv_L':  "HInv3_L s' p q d"
  and      pq:  "p\<noteq>q"
  and   inv2b:  "Inv2b s"
  shows   "HInv3_R s' p q d"
proof -
  from inv_L' act pq
  have "phase s q \<in> {1,2} \<and> hasRead s q d p"
    by(auto simp add: Phase1or2ReadThen_def HInv3_L_def 
            hasRead_def split: if_split_asm)
  with inv2b
  have "disk s d q = dblock s q"
    by(auto simp add: Inv2b_def Inv2b_inner_def 
             hasRead_def)
  with act
  show ?thesis
    by(auto simp add: Phase1or2ReadThen_def HInv3_def 
                       HInv3_inner_def HInv3_R_def)
qed

lemma Phase1or2ReadThen_HInv3_hasRead: 
  "\<lbrakk> \<not>hasRead s pp dd qq; 
     Phase1or2ReadThen s s' p d q; 
     pp\<noteq>p \<or> qq\<noteq>q \<or> dd\<noteq>d\<rbrakk> 
  \<Longrightarrow> \<not>hasRead s' pp dd qq"
  by(auto simp add: hasRead_def Phase1or2ReadThen_def)

theorem HPhase1or2ReadThen_HInv3:
  assumes act:  "HPhase1or2ReadThen s s' p d q"
  and     inv:  "HInv3 s"
  and      pq:  "p\<noteq>q"
  and   inv2b:  "Inv2b s"
  shows   "HInv3 s'"
proof(clarsimp simp add: HInv3_def HInv3_inner_def)
  fix pp qq dd
  assume h3l': "HInv3_L s' pp qq dd"
  show  "HInv3_R s' pp qq dd"
  proof(cases "HInv3_L s pp qq dd")
    case True
    with inv
    have "HInv3_R s pp qq dd"
      by(auto simp add: HInv3_def HInv3_inner_def)
    with act h3l'
    show ?thesis
      by(auto simp add: HInv3_R_def HInv3_L_def 
                          Phase1or2ReadThen_def)
  next
    case False
    assume nh3l: "\<not> HInv3_L s pp qq dd"
    show " HInv3_R s' pp qq dd"
    proof(cases "((pp=p \<and> qq=q) \<or> (pp=q \<and> qq=p)) \<and> dd=d")
      case True
      with act pq inv2b h3l' HInv3_L_sym[OF h3l']  
      show ?thesis
        by(auto dest: Phase1or2ReadThen_HInv3_pq HInv3_R_sym)
    next
      case False
      from nh3l h3l' act
      have "(\<not>hasRead s pp dd qq \<or> \<not>hasRead s qq dd pp) 
            \<and> hasRead s' pp dd qq \<and> hasRead s' qq dd pp"
        by(auto simp add: HInv3_L_def Phase1or2ReadThen_def)
      with act False
      show ?thesis
        by(auto dest: Phase1or2ReadThen_HInv3_hasRead)
    qed
  qed
qed

lemma StartBallot_HInv3_p:   
  "\<lbrakk> StartBallot s s' p; HInv3_L s' p q d \<rbrakk> 
          \<Longrightarrow> HInv3_R s' p q d"
by(auto simp add: StartBallot_def dest: InitPhase_HInv3_p)

lemma StartBallot_HInv3_q:   
  "\<lbrakk> StartBallot s s' q; HInv3_L s' p q d \<rbrakk>
           \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: StartBallot_def dest: InitPhase_HInv3_q)

lemma StartBallot_HInv3_nL:   
  "\<lbrakk> StartBallot s s' t; \<not>HInv3_L s p q d; t\<noteq>p; t\<noteq> q \<rbrakk> 
           \<Longrightarrow> \<not>HInv3_L s' p q d"
  by(auto simp add: StartBallot_def InitializePhase_def 
                      HInv3_L_def hasRead_def)

lemma StartBallot_HInv3_R:
  "\<lbrakk> StartBallot s s' t; HInv3_R s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
              \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: StartBallot_def InitializePhase_def 
                    HInv3_R_def hasRead_def)

lemma StartBallot_HInv3_t:
  "\<lbrakk> StartBallot s s' t; HInv3_inner s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                \<Longrightarrow> HInv3_inner s' p q d"
  by(auto simp add: HInv3_inner_def 
        dest: StartBallot_HInv3_nL StartBallot_HInv3_R)

lemma StartBallot_HInv3:
  assumes act: "StartBallot s s' t"
  and     inv: "HInv3_inner s p q d"
  shows        "HInv3_inner s' p q d"
proof(cases "t=p \<or> t=q")
  case True
  with act inv
  show ?thesis
    by(auto simp add: HInv3_inner_def 
         dest: StartBallot_HInv3_p StartBallot_HInv3_q)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: HInv3_inner_def dest: StartBallot_HInv3_t)
qed

theorem HStartBallot_HInv3:
  "\<lbrakk> HStartBallot s s' p; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: HInv3_def dest: StartBallot_HInv3)

theorem HPhase1or2ReadElse_HInv3:
  "\<lbrakk> HPhase1or2ReadElse s s' p d q; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: Phase1or2ReadElse_def HInv3_def 
              dest: StartBallot_HInv3)

theorem HPhase1or2Write_HInv3:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv3 s"
  shows "HInv3 s'"
proof(auto simp add: HInv3_def)
  fix pp qq dd
  show " HInv3_inner s' pp qq dd"
  proof(cases "HInv3_L s pp qq dd")
    case True
    with inv
    have "HInv3_R s pp qq dd"
      by(simp add: HInv3_def HInv3_inner_def)
    with act
    show ?thesis
      by(auto simp add: HInv3_inner_def HInv3_R_def 
                      Phase1or2Write_def)
  next
    case False
    with act
    have "\<not>HInv3_L s' pp qq dd"
      by(auto simp add: HInv3_L_def hasRead_def Phase1or2Write_def)
    thus ?thesis
      by(simp add: HInv3_inner_def)
  qed
qed

lemma EndPhase1_HInv3_p:   
  "\<lbrakk> EndPhase1 s s' p; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
by(auto simp add: EndPhase1_def dest: InitPhase_HInv3_p)

lemma EndPhase1_HInv3_q:   
  "\<lbrakk> EndPhase1 s s' q; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase1_def dest: InitPhase_HInv3_q)

lemma EndPhase1_HInv3_nL:   
  "\<lbrakk> EndPhase1 s s' t; \<not>HInv3_L s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                    \<Longrightarrow> \<not>HInv3_L s' p q d"
  by(auto simp add: EndPhase1_def InitializePhase_def 
                    HInv3_L_def hasRead_def)

lemma EndPhase1_HInv3_R:
  "\<lbrakk> EndPhase1 s s' t; HInv3_R s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                      \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase1_def InitializePhase_def
                    HInv3_R_def hasRead_def)

lemma EndPhase1_HInv3_t:
  "\<lbrakk> EndPhase1 s s' t; HInv3_inner s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                \<Longrightarrow> HInv3_inner s' p q d"
  by(auto simp add: HInv3_inner_def dest: EndPhase1_HInv3_nL 
                   EndPhase1_HInv3_R)

lemma EndPhase1_HInv3:
  assumes act: "EndPhase1 s s' t"
  and     inv: "HInv3_inner s p q d"
  shows        "HInv3_inner s' p q d"
proof(cases "t=p \<or> t=q")
  case True
  with act inv
  show ?thesis
    by(auto simp add: HInv3_inner_def 
                dest: EndPhase1_HInv3_p EndPhase1_HInv3_q)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: HInv3_inner_def dest: EndPhase1_HInv3_t)
qed

theorem HEndPhase1_HInv3:
  "\<lbrakk> HEndPhase1 s s' p; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: HInv3_def dest: EndPhase1_HInv3)

lemma EndPhase2_HInv3_p:   
  "\<lbrakk> EndPhase2 s s' p; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
by(auto simp add: EndPhase2_def dest: InitPhase_HInv3_p)

lemma EndPhase2_HInv3_q:   
  "\<lbrakk> EndPhase2 s s' q; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase2_def dest: InitPhase_HInv3_q)

lemma EndPhase2_HInv3_nL:   
  "\<lbrakk> EndPhase2 s s' t; \<not>HInv3_L s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                     \<Longrightarrow> \<not>HInv3_L s' p q d"
  by(auto simp add: EndPhase2_def InitializePhase_def
                    HInv3_L_def hasRead_def)

lemma EndPhase2_HInv3_R:
  "\<lbrakk> EndPhase2 s s' t; HInv3_R s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                     \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase2_def InitializePhase_def
                    HInv3_R_def hasRead_def)

lemma EndPhase2_HInv3_t:
  "\<lbrakk> EndPhase2 s s' t; HInv3_inner s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                    \<Longrightarrow> HInv3_inner s' p q d"
  by(auto simp add: HInv3_inner_def 
              dest: EndPhase2_HInv3_nL EndPhase2_HInv3_R)

lemma EndPhase2_HInv3:
  assumes act: "EndPhase2 s s' t"
  and     inv: "HInv3_inner s p q d"
  shows        "HInv3_inner s' p q d"
proof(cases "t=p \<or> t=q")
  case True
  with act inv
  show ?thesis
    by(auto simp add: HInv3_inner_def 
                dest: EndPhase2_HInv3_p EndPhase2_HInv3_q)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: HInv3_inner_def dest: EndPhase2_HInv3_t)
qed

theorem HEndPhase2_HInv3:
  "\<lbrakk> HEndPhase2 s s' p; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: HInv3_def dest: EndPhase2_HInv3)

lemma Fail_HInv3_p:   
  "\<lbrakk> Fail s s' p; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
by(auto simp add: Fail_def dest: InitPhase_HInv3_p)

lemma Fail_HInv3_q:   
  "\<lbrakk> Fail s s' q; HInv3_L s' p q d \<rbrakk> \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: Fail_def dest: InitPhase_HInv3_q)

lemma Fail_HInv3_nL:   
  "\<lbrakk> Fail s s' t; \<not>HInv3_L s p q d; t\<noteq>p; t\<noteq> q \<rbrakk> 
             \<Longrightarrow> \<not>HInv3_L s' p q d"
  by(auto simp add: Fail_def InitializePhase_def
                    HInv3_L_def hasRead_def)

lemma Fail_HInv3_R:
  "\<lbrakk> Fail s s' t; HInv3_R s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
             \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: Fail_def InitializePhase_def
                    HInv3_R_def hasRead_def)

lemma Fail_HInv3_t:
  "\<lbrakk> Fail s s' t; HInv3_inner s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
              \<Longrightarrow> HInv3_inner s' p q d"
  by(auto simp add: HInv3_inner_def 
              dest: Fail_HInv3_nL Fail_HInv3_R)

lemma Fail_HInv3:
  assumes act: "Fail s s' t"
  and     inv: "HInv3_inner s p q d"
  shows        "HInv3_inner s' p q d"
proof(cases "t=p \<or> t=q")
  case True
  with act inv
  show ?thesis
    by(auto simp add: HInv3_inner_def 
                dest: Fail_HInv3_p Fail_HInv3_q)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: HInv3_inner_def dest: Fail_HInv3_t)
qed

theorem HFail_HInv3:
  "\<lbrakk> HFail s s' p; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: HInv3_def dest: Fail_HInv3)

theorem HPhase0Read_HInv3:
  assumes act: "HPhase0Read s s' p d"
  and inv: "HInv3 s"
  shows "HInv3 s'"
proof(auto simp add: HInv3_def)
  fix pp qq dd
  show " HInv3_inner s' pp qq dd"
  proof(cases "HInv3_L s pp qq dd")
    case True
    with inv
    have "HInv3_R s pp qq dd"
      by(simp add: HInv3_def HInv3_inner_def)
    with act
    show ?thesis
      by(auto simp add: HInv3_inner_def HInv3_R_def Phase0Read_def)
  next
    case False
    with act
    have "\<not>HInv3_L s' pp qq dd"
      by(auto simp add: HInv3_L_def hasRead_def Phase0Read_def)
    thus ?thesis
      by(simp add: HInv3_inner_def)
  qed
qed

lemma EndPhase0_HInv3_p:   
  "\<lbrakk> EndPhase0 s s' p; HInv3_L s' p q d \<rbrakk> 
              \<Longrightarrow> HInv3_R s' p q d"
by(auto simp add: EndPhase0_def dest: InitPhase_HInv3_p)

lemma EndPhase0_HInv3_q:   
  "\<lbrakk> EndPhase0 s s' q; HInv3_L s' p q d \<rbrakk>
              \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase0_def dest: InitPhase_HInv3_q)

lemma EndPhase0_HInv3_nL:   
  "\<lbrakk> EndPhase0 s s' t; \<not>HInv3_L s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
               \<Longrightarrow> \<not>HInv3_L s' p q d"
  by(auto simp add: EndPhase0_def InitializePhase_def 
                    HInv3_L_def hasRead_def)

lemma EndPhase0_HInv3_R:
  "\<lbrakk> EndPhase0 s s' t; HInv3_R s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                \<Longrightarrow> HInv3_R s' p q d"
  by(auto simp add: EndPhase0_def InitializePhase_def 
                    HInv3_R_def hasRead_def)

lemma EndPhase0_HInv3_t:
  "\<lbrakk> EndPhase0 s s' t; HInv3_inner s p q d; t\<noteq>p; t\<noteq> q \<rbrakk>
                 \<Longrightarrow> HInv3_inner s' p q d"
  by(auto simp add: HInv3_inner_def 
              dest: EndPhase0_HInv3_nL EndPhase0_HInv3_R)

lemma EndPhase0_HInv3:
  assumes act: "EndPhase0 s s' t"
  and     inv: "HInv3_inner s p q d"
  shows        "HInv3_inner s' p q d"
proof(cases "t=p \<or> t=q")
  case True
  with act inv
  show ?thesis
    by(auto simp add: HInv3_inner_def 
                dest: EndPhase0_HInv3_p EndPhase0_HInv3_q)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: HInv3_inner_def dest: EndPhase0_HInv3_t)
qed

theorem HEndPhase0_HInv3:
  "\<lbrakk> HEndPhase0 s s' p; HInv3 s \<rbrakk> \<Longrightarrow> HInv3 s'"
  by(auto simp add: HInv3_def dest: EndPhase0_HInv3)

text\<open>$HInv1 \wedge HInv2 \wedge HInv3$ is an invariant of $HNext$.\<close>

lemma I2c:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s \<and> HInv2 s \<and> HInv3 s"
  shows "HInv3 s'" using assms
  by(auto simp add: HNext_def Next_def,
     auto intro: HStartBallot_HInv3,
     auto intro: HPhase0Read_HInv3,
     auto intro: HPhase1or2Write_HInv3,
     auto simp add: Phase1or2Read_def HInv2_def
          intro: HPhase1or2ReadThen_HInv3
                 HPhase1or2ReadElse_HInv3,
     auto simp add: EndPhase1or2_def
          intro: HEndPhase1_HInv3
                 HEndPhase2_HInv3,
     auto intro: HFail_HInv3,
     auto intro: HEndPhase0_HInv3)

end
